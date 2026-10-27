/* Theorem Sketchpad — runtime: values and operators, the compiler (AST → closures),
   claim analysis, and the library registry. */
'use strict';
(function (global) {
const MV = global.MV;
const { MVError, fmtNum, ppText, freeNames, subst, binderNames, splitStatements, parseStatement, locate } = MV;

let ACTIVE = { types: [], views: {}, libs: new Set() };
let DEFS = new WeakMap();
const REG = new Map();
let NAME_INDEX = new Map(), VIEW_INDEX = new Map();
let PENDING = new Set();   // names defined later in the notebook, so forward references are allowed

/* ================= Records and namespaces ================= */

/* A record: named fields, optionally made by a structure's constructor. */
function makeRecord(fields, struct = null, label = null) {
  return { __record: true, fields, struct, label };
}
const isRecord = v => !!(v && v.__record);

function getField(v, name) {
  if (v && v.__ns) {
    if (name in v.members) return v.members[name];
    throw new MVError(`The ${v.name} library has no ${name}. It has: ${Object.keys(v.members).slice(0, 12).join(', ')}${Object.keys(v.members).length > 12 ? ', …' : ''}.`);
  }
  if (isRecord(v)) {
    if (name in v.fields) return v.fields[name];
    // Extras a library attached (a quotient's projection, …).
    if (Object.prototype.hasOwnProperty.call(v, name) && !['fields', 'struct', 'label', '__record'].includes(name) && ['function', 'number', 'boolean'].includes(typeof v[name])) return v[name];
    throw new MVError(`${fmt(v)} has no field ${name}. Its fields are ${Object.keys(v.fields).join(', ')}.`);
  }
  // What a library object knows about itself: a sequence's limit, a series' sum, …
  if ((typeof v === 'function' || (v && typeof v === 'object')) && Object.prototype.hasOwnProperty.call(v, name)) {
    const x = v[name];
    if (['number', 'boolean', 'function'].includes(typeof x) || (Array.isArray(x) && x.every(t => typeof t === 'number'))) return x;
  }
  throw new MVError(`${describeValue(v)} has no field ${name}, so ".${name}" means nothing here.`);
}

/* ================= Formatting ================= */

// A number as a short decimal when it is one (0.25), as a fraction when it is a simple one that
// isn't (1/3, −5/12), else rounded.
function fmtNumber(v) {
  const s = fmtNum(v);
  if (!Number.isFinite(v) || Number.isInteger(v)) return s;
  const close = (a, b) => Math.abs(a - b) <= 4 * Number.EPSILON * Math.max(1, Math.abs(a));
  const plain = +s.replace('−', '-');
  if (close(plain, v) && !/e/i.test(s)) return s;
  let h0 = 1, h1 = 0, k0 = 0, k1 = 1, y = Math.abs(v);
  for (let i = 0; i < 20; i++) {
    const a = Math.floor(y);
    [h0, h1] = [a * h0 + h1, h0];
    [k0, k1] = [a * k0 + k1, k0];
    if (k0 > 100) break;
    if (h0 > 0 && close(h0 / k0, Math.abs(v))) return (v < 0 ? '−' : '') + h0 + '/' + k0;
    if (y - a < 1e-12) break;
    y = 1 / (y - a);
  }
  return s;
}

function fmt(v) {
  if (typeof v === 'number') return fmtNumber(v);
  if (v && v.__exact) return MV.EX.fmtExact(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (v === undefined || v === null) return 'nothing';
  for (const T of ACTIVE.types) {
    try { if (T.test(v) && T.ops.format) return T.ops.format(v); } catch (e) { /* ignore */ }
  }
  if (v.__claim) return v.label;
  if (v.__elt) return v.label;
  if (v.__record) return v.label || '{' + Object.entries(v.fields).map(([k, x]) => `${k} = ${fmt(x)}`).join(', ') + '}';
  if (v.__ns) return `the ${v.name} library`;
  if (Array.isArray(v)) return v.label || '(' + v.map(fmt).join(', ') + ')';
  if (typeof v === 'function') return v.label || v.name || 'a function';
  if (v.__domain) {
    // A set carved out of a finite set: list its elements.
    if (v.kind === 'set' && v.ambient && v.ambient.kind === 'finite' && v.ambient.values.length <= 64) {
      const els = elementsOf(v);
      return els.length ? '{' + els.map(fmt).join(', ') + '}' : '∅';
    }
    return v.describe();
  }
  return String(v);
}

function describeValue(v) {
  if (typeof v === 'number') return 'the number ' + fmtNum(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (typeof v === 'function') return v.isSequence ? `the sequence ${fmt(v)}` : 'a function';
  if (v && v.__domain) return 'the set ' + v.describe();
  if (v && v.__elt) return 'the group element ' + v.label;
  if (v && v.__record) return 'the record ' + fmt(v);
  if (v && v.__ns) return `the ${v.name} library`;
  if (Array.isArray(v)) return 'the point ' + fmt(v);
  if (v === undefined || v === null) return 'nothing';
  for (const T of ACTIVE.types) { try { if (T.test(v)) return `a ${T.name} value (${fmt(v)})`; } catch (e) { /* ignore */ } }
  return String(v);
}

/* ================= Operators ================= */

// Relative tolerance, with an absolute floor of tol/1000 (1e-12 by default) near zero.
const approxEq = (a, b, tol = MV.TOL) => a === b || (Number.isFinite(a) && Number.isFinite(b) && Math.abs(a - b) <= tol * Math.max(1e-3, Math.abs(a), Math.abs(b)));
const isFn = v => typeof v === 'function' && !v.domainCtor;
const isDom = v => !!(v && v.__domain);

function truth(v, node) {
  if (v === true || v === false) return v;
  throw new MVError(`Expected a true/false statement${node ? `, but ${ppText(node)} is ${describeValue(v)}` : `, got ${describeValue(v)}`}.`);
}

function findType(op, a, b) {
  for (const T of ACTIVE.types) {
    if (!T.ops[op]) continue;
    try { if (T.test(a) || (b !== undefined && T.test(b))) return T; } catch (e) { /* ignore */ }
  }
  return null;
}

function opError(op, a, b) {
  const sym = { '+': '+', '-': '−', '*': '·', '/': '/', '^': '^', mod: 'mod', neg: '−', abs: '|…|', '<': '<', union: '∪', inter: '∩', '\\': '∖' }[op] || op;
  let hint = '';
  outer: for (const lib of REG.values()) {
    if (!lib.def || ACTIVE.libs.has(lib.name)) continue;
    for (const T of lib.def.types || []) {
      try {
        if (T.test(a) || (b !== undefined && T.test(b))) { hint = ` The ${lib.name} library works with ${T.name} values: add "import ${lib.name}".`; break outer; }
      } catch (e) { /* ignore */ }
    }
  }
  const what = b === undefined ? describeValue(a) : `${describeValue(a)} and ${describeValue(b)}`;
  return new MVError(`Can't apply ${sym} to ${what}.${hint}`);
}

const isEx = v => !!(v && v.__exact);
function arith(op, a, b) {
  // Exact reals: exact with numbers and each other; as floats with anything else (points, sets…).
  if (isEx(a) || isEx(b)) {
    const numeric = v => v === undefined || typeof v === 'number' || isEx(v);
    if (numeric(a) && numeric(b) && ['+', '-', '*', '/', '^', 'mod', 'neg', 'abs'].includes(op)) return MV.EX.arith(op, a, b);
    if (isEx(a)) a = +a;
    if (isEx(b)) b = +b;
  }
  if (typeof a === 'number' && (b === undefined || typeof b === 'number')) {
    switch (op) {
      case '+': return a + b;
      case '-': return a - b;
      case '*': return a * b;
      case '/': return a / b;
      case '^': return Math.pow(a, b);
      case 'mod': return ((a % b) + b) % b;
      case 'neg': return -a;
      case 'abs': return Math.abs(a);
    }
  }
  // Spaces: ℝ^2, A × B, A ∪ B, A ∩ B, A ∖ B. A bare constructor such as R stands for its space.
  if (typeof a === 'function' && a.domainCtor) a = toDomain(a);
  if (typeof b === 'function' && b.domainCtor) b = toDomain(b);
  if (isDom(a) || isDom(b)) {
    if (op === '^' && isDom(a) && Number.isInteger(b) && b >= 1) return MV.product(new Array(b).fill(a));
    if (op === '*' && isDom(a) && isDom(b)) return MV.product([a, b]);
    if ((op === 'union' || op === 'inter' || op === '\\') && isDom(a) && isDom(b)) return MV.setOp(op, a, b);
  }
  // |S| is the number of elements of a finite set.
  if (op === 'abs' && isDom(a)) {
    const els = elementsOf(a);
    if (els) return els.length;
    throw new MVError(`|${a.describe()}| would be its number of elements, but it isn't a finite set we can list.`);
  }
  // Library types (complex numbers, matrices, …) come before the built-in rules.
  const T = findType(op, a, b);
  if (T) return T.ops[op](a, b);
  // Points and vectors: elementwise.
  if (Array.isArray(a) || Array.isArray(b)) {
    if (op === 'abs' && Array.isArray(a)) return Math.sqrt(a.reduce((s, x) => { const m = arith('abs', x); return s + m * m; }, 0));
    if (op === 'neg' && Array.isArray(a)) return a.map(x => arith('neg', x));
    if ((op === '+' || op === '-') && Array.isArray(a) && Array.isArray(b)) {
      if (a.length !== b.length) throw new MVError(`Can't ${op === '+' ? 'add' : 'subtract'} points with ${a.length} and ${b.length} coordinates.`);
      return a.map((x, i) => arith(op, x, b[i]));
    }
    if (op === '*' && typeof a === 'number' && Array.isArray(b)) return b.map(x => arith('*', a, x));
    if ((op === '*' || op === '/') && Array.isArray(a) && typeof b === 'number') return a.map(x => arith(op, x, b));
  }
  // Functions and sequences: pointwise, keeping known limits.
  if (isFn(a) || isFn(b)) {
    // Exact inputs reach the parts that can take them (as in callValue); the others get floats.
    const via = f => (f.__notebook || f.exactAware ? f : (...xs) => f(...xs.map(x => (isEx(x) ? +x : x))));
    const fa = isFn(a) ? via(a) : () => a, fb = b === undefined ? null : isFn(b) ? via(b) : () => b;
    const out = fb ? (...xs) => arith(op, fa(...xs), fb(...xs)) : (...xs) => arith(op, fa(...xs));
    out.exactAware = true;
    out.kindSensitive = !!((isFn(a) && a.kindSensitive) || (isFn(b) && b.kindSensitive));
    // A formula for the asymptotic analysis, when both parts have one (or are numbers).
    if (MV.ASYM) {
      const part = (v, name) => (isFn(v) ? (MV.ASYM.formulaOf(v) ? { type: 'call', f: { type: 'id', name }, args: [{ type: 'id', name: '__x' }] } : null) : typeof v === 'number' ? { type: 'num', v } : null);
      const A = part(a, '__f'), Bn = b === undefined ? true : part(b, '__g');
      if (A && Bn) {
        const body = b === undefined ? (op === 'neg' ? { type: 'un', op: 'neg', a: A } : op === 'abs' ? { type: 'abs', e: A } : null) : { type: 'bin', op, a: A, b: Bn };
        if (body) out.__lambda = { params: ['__x'], body, env: { __f: a, __g: b } };
      }
    }
    const la = isFn(a) ? a.limit : a, lb = isFn(b) ? b.limit : b;
    out.label = fb ? `(${fmt(a)} ${{ '+': '+', '-': '−', '*': '·', '/': '/', '^': '^', mod: 'mod' }[op] || op} ${fmt(b)})` : `${op === 'neg' ? '−' : '|'}${fmt(a)}${op === 'abs' ? '|' : ''}`;
    out.isSequence = (isFn(a) && a.isSequence) || (isFn(b) && b.isSequence);
    // Known limits combine; otherwise (for example a divergent term) lim falls back to the numerical test.
    if (la !== undefined && (b === undefined || lb !== undefined)) {
      try { out.limit = b === undefined ? arith(op, la) : arith(op, la, lb); out.convergent = true; } catch (e) { /* no limit */ }
    }
    return out;
  }
  throw opError(op, a, b);
}

// The elements of a set, when it has finitely many we can list: a finite set, or a set carved
// out of a finite one.
function elementsOf(D) {
  if (!isDom(D)) return null;
  if (D.kind === 'finite') return D.values;
  if (D.kind === 'set' && D.ambient) { const all = elementsOf(D.ambient); return all ? all.filter(v => D.contains(v)) : null; }
  if (D.kind === 'interval' && D.integer && !D.unbounded && D.size <= 1e4) return D.sample(Infinity);
  return null;
}

function equalValues(a, b) {
  if (typeof a === 'number' && typeof b === 'number') return approxEq(a, b);
  // A named group element equals its ordinary value: 1 in ℤ/2, (2, 3, 1) for the cycle (1 2 3).
  if (a && a.__elt && !(b && b.__elt)) return a.raw !== undefined && equalValues(a.raw, b);
  if (b && b.__elt && !(a && a.__elt)) return b.raw !== undefined && equalValues(a, b.raw);
  if ((isEx(a) || isEx(b)) && (typeof a === 'number' || isEx(a)) && (typeof b === 'number' || isEx(b))) {
    const e = MV.EX.equalExact(a, b);
    return e !== null ? e : approxEq(+a, +b);
  }
  if (a === b) return true;
  if (isRecord(a) && isRecord(b)) {
    const ka = Object.keys(a.fields), kb = Object.keys(b.fields);
    return ka.length === kb.length && ka.every(k => k in b.fields && equalValues(a.fields[k], b.fields[k]));
  }
  if (isDom(a) && isDom(b)) {
    if (a.sameSet) return a.sameSet(b);
    if (b.sameSet) return b.sameSet(a);
    const ea = elementsOf(a), eb = elementsOf(b);
    if (ea && eb) return ea.length === eb.length && ea.every(x => b.contains(x)) && eb.every(x => a.contains(x));
    return false;
  }
  const T = findType('=', a, b);
  if (T) return !!T.ops['='](a, b);
  if (Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((x, i) => equalValues(x, b[i]));
  return a === b;
}

/* Comparisons are tolerant: within MV.TOL (relative) counts as equal, so "<=" includes
   numbers that are just over and "<" excludes numbers that are just under. */
function compare(op, a, b) {
  if ((isEx(a) || isEx(b)) && (typeof a === 'number' || isEx(a)) && (typeof b === 'number' || isEx(b))) {
    const c = MV.EX.cmpExact(a, b);
    if (c !== null) {
      switch (op) {
        case '<': return c < 0; case '<=': return c <= 0; case '>': return c > 0; case '>=': return c >= 0;
        case '=': case '~=': return c === 0; case '!=': return c !== 0;
      }
    }
    if (op === '=' || op === '!=') { const e = MV.EX.equalExact(a, b); if (e !== null) return op === '=' ? e : !e; }
    a = +a; b = +b;
  }
  if (typeof a === 'number' && typeof b === 'number') {
    switch (op) {
      case '<': return a < b && !approxEq(a, b);
      case '<=': return a <= b || approxEq(a, b);
      case '>': return a > b && !approxEq(a, b);
      case '>=': return a >= b || approxEq(a, b);
      case '=': return approxEq(a, b);
      case '!=': return !approxEq(a, b);
      case '~=': return approxEq(a, b, 1e-6);
    }
  }
  // ≈ on points and matrices: coordinate by coordinate.
  if (op === '~=' && Array.isArray(a) && Array.isArray(b)) return a.length === b.length && a.every((x, i) => compare('~=', x, b[i]));
  if (op === '=' || op === '~=') return equalValues(a, b);
  if (op === '!=') return !equalValues(a, b);
  const T = findType('<', a, b);
  if (T) {
    const lt = T.ops['<'];
    if (op === '<') return lt(a, b);
    if (op === '>') return lt(b, a);
    if (op === '<=') return lt(a, b) || equalValues(a, b);
    if (op === '>=') return lt(b, a) || equalValues(a, b);
  }
  if (Array.isArray(a) || Array.isArray(b)) throw new MVError(`Points can't be ordered with ${op}. Compare their sizes instead, as in |x| < 1.`);
  throw opError('<', a, b);
}

function factorial(n) {
  if (typeof n !== 'number' || n < 0 || !Number.isInteger(n)) throw new MVError(`Factorial needs a whole number ≥ 0, got ${fmt(n)}.`);
  let r = 1;
  for (let k = 2; k <= n; k++) r *= k;
  return r;
}

// Words people write for the number spaces.
const ALIASES = { reals: 'R', real: 'R', Reals: 'R', RR: 'R', integers: 'Z', ints: 'Z', ZZ: 'Z', naturals: 'N', nat: 'N', NN: 'N', Nat: 'N',
  rationals: 'Q', infinity: 'inf', oo: 'inf', PI: 'pi', Pi: 'pi', ln10: 'ln(10)', arcsin: 'asin', arccos: 'acos', arctan: 'atan' };
// Edit distance, for "did you mean".
function distance(a, b) {
  const d = Array.from({ length: a.length + 1 }, (_, i) => [i, ...Array(b.length).fill(0)]);
  for (let j = 1; j <= b.length; j++) d[0][j] = j;
  for (let i = 1; i <= a.length; i++) for (let j = 1; j <= b.length; j++) d[i][j] = Math.min(d[i - 1][j] + 1, d[i][j - 1] + 1, d[i - 1][j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
  return d[a.length][b.length];
}
function unknownName(name, env = null, inClaim = false) {
  const lib = NAME_INDEX.get(name);
  if (lib && !ACTIVE.libs.has(lib)) return new MVError(`"${name}" comes from the ${lib} library. Add "import ${lib}" above this line.`);
  if (ALIASES[name] && (!env || env[ALIASES[name]] !== undefined || /\(/.test(ALIASES[name]))) return new MVError(`"${name}" isn't defined. Did you mean ${ALIASES[name]}?`);
  // A lone letter in a claim is usually a variable meant to range over something.
  if (inClaim && /^[\p{L}]'*$/u.test(name)) return new MVError(`"${name}" isn't defined. To claim this for every ${name}, say where it ranges: forall ${name} in R: …`);
  if (env && name.length > 2) {
    const known = new Set();
    for (const k in env) if (/^[\p{L}_][\p{L}\p{N}_']*$/u.test(k)) known.add(k);
    for (const k of NAME_INDEX.keys()) known.add(k);
    let best = null, bd = Infinity;
    for (const k of known) { const dd = distance(name.toLowerCase(), k.toLowerCase()); if (dd < bd) { bd = dd; best = k; } }
    if (best && bd <= Math.max(1, Math.floor(name.length / 4))) {
      const from = NAME_INDEX.get(best);
      return new MVError(`"${name}" isn't defined. Did you mean ${best}${from && !ACTIVE.libs.has(from) ? ` (from the ${from} library: add "import ${from}")` : ''}?`);
    }
  }
  return new MVError(`"${name}" isn't defined. Define it with let or def, or check the spelling.`);
}

function lookup(e, name) {
  const v = e[name];
  if (v === undefined) throw unknownName(name);
  return v;
}

function callValue(f, args, name) {
  if (typeof f !== 'function') throw new MVError(`${name} is ${describeValue(f)}, not a function, so it can't be called.`);
  if (f.arity !== undefined && args.length !== f.arity) {
    throw new MVError(`${f.label || name} takes ${f.arity} argument${f.arity === 1 ? '' : 's'} but got ${args.length}.`);
  }
  if (!f.__notebook && !f.exactAware && args.some(isEx)) args = args.map(a => (isEx(a) ? +a : a));
  try { return f(...args); }
  catch (err) {
    if (err instanceof MVError) throw err;
    throw new MVError(`${name}: ${err.message}`);
  }
}

function toDomain(v, what) {
  if (isDom(v)) return v;
  if (typeof v === 'function' && v.__structure) return v.__structure.space;
  if (typeof v === 'function' && v.domainCtor) return toDomain(v(), what);
  if (Array.isArray(v)) return MV.finite(v);
  throw new MVError(`${what || 'This'} is ${describeValue(v)}, which isn't a set. Use an interval like [0, 1], a space like R^2, a range like 1..10, or a set.`);
}

function bindTarget(e, b, v) {
  if (!b.pattern) { e[b.name] = v; return; }
  if (!Array.isArray(v) || v.length !== b.pattern.length) throw new MVError(`Can't split ${fmt(v)} into (${b.pattern.join(', ')}).`);
  b.pattern.forEach((x, i) => { e[x] = v[i]; });
}

const num = (v, node) => {
  if (typeof v === 'number') return v;
  if (v && v.__exact) return +v;   // interval ends are floats; exact sampling recovers fractions
  throw new MVError(`${ppText(node)} should be a number but is ${describeValue(v)}.`);
};

/* ================= Compiler ================= */

/* Samples per quantified variable, by nesting depth. Depth is counted while evaluating, so a
   quantifier inside a definition gets fewer samples when that definition is used inside another
   quantifier. */
const SAMPLES = [200, 64, 40, 20];
let DEPTH = 0;
// Inside an ∃, a ∀ samples down to the same tiny scale the ∃ searched (∃δ ∀ε needs ε as small as δ).
let IN_EXISTS = 0;
const perDepth = () => SAMPLES[Math.min(DEPTH, SAMPLES.length - 1)];
function atDepth(d, f) {
  const old = DEPTH;
  DEPTH = d;
  try { return f(); } finally { DEPTH = old; }
}

function compile(n, cx = { q: 0 }) {
  switch (n.type) {
    case 'num': case 'bool': case 'value': { const v = n.v; return () => v; }
    case 'id': { const name = n.name; return e => { const v = e[name]; if (v === undefined) throw unknownName(name, e); return v; }; }
    case 'bin': {
      const a = compile(n.a, cx), b = compile(n.b, cx), op = n.op;
      switch (op) {
        case 'and': return e => truth(a(e), n.a) && truth(b(e), n.b);
        case 'or': return e => truth(a(e), n.a) || truth(b(e), n.b);
        case '->': return e => !truth(a(e), n.a) || truth(b(e), n.b);
        case '<->': return e => truth(a(e), n.a) === truth(b(e), n.b);
        default: return e => arith(op, a(e), b(e));
      }
    }
    case 'cmp': {
      const fs = n.args.map(x => compile(x, cx)), ops = n.ops;
      return e => {
        let p = fs[0](e);
        for (let i = 0; i < ops.length; i++) {
          const c = fs[i + 1](e);
          if (!compare(ops[i], p, c)) return false;
          p = c;
        }
        return true;
      };
    }
    case 'un': {
      const a = compile(n.a, cx);
      switch (n.op) {
        case 'neg': return e => arith('neg', a(e));
        case 'not': return e => !truth(a(e), n.a);
        case 'sqrt': return e => callValue(lookup(e, 'sqrt'), [a(e)], 'sqrt');
        default: return e => factorial(a(e));
      }
    }
    case 'abs': { const a = compile(n.e, cx); return e => arith('abs', a(e)); }
    case 'call': {
      const f = compile(n.f, cx), as = n.args.map(x => compile(x, cx));
      const name = n.f.type === 'id' ? n.f.name : 'This expression';
      return e => callValue(f(e), as.map(g => g(e)), name);
    }
    case 'index': {
      const o = compile(n.obj, cx), as = n.args.map(x => compile(x, cx)), name = n.obj.name || 'This value';
      return e => {
        const v = o(e), args = as.map(g => g(e));
        if (typeof v === 'function') return callValue(v, args, name);
        if (Array.isArray(v)) {
          let r = v;
          for (const k of args) {
            if (isEx(k)) k = +k;
            if (!Array.isArray(r) || !Number.isInteger(k) || k < 1 || k > r.length) throw new MVError(`Index ${fmt(k)} is out of range. Coordinates are numbered from 1.`);
            r = r[k - 1];
          }
          return r;
        }
        throw new MVError(`${name} can't be indexed with [ ].`);
      };
    }
    case 'list': case 'tuple': { const fs = n.items.map(x => compile(x, cx)); return e => fs.map(f => f(e)); }
    case 'field': { const o = compile(n.obj, cx), name = n.name; return e => getField(o(e), name); }
    case 'record': {
      const fs = n.fields.map(f => ({ name: f.name, f: compile(f.expr, cx) }));
      return e => { const fields = {}; for (const f of fs) fields[f.name] = f.f(e); return makeRecord(fields); };
    }
    case 'finite': { const fs = n.items.map(x => compile(x, cx)); return e => MV.finite(fs.map(f => f(e))); }
    case 'if': {
      const c = compile(n.c, cx), a = compile(n.a, cx), b = compile(n.b, cx);
      return e => truth(c(e), n.c) ? a(e) : b(e);
    }
    case 'lambda': {
      const body = compile(n.body, cx), ps = n.params, label = ppText(n);
      return e => {
        const fn = (...args) => {
          const e2 = Object.create(e);
          for (let i = 0; i < ps.length; i++) e2[ps[i]] = args[i];
          return body(e2);
        };
        fn.label = label; fn.arity = ps.length; fn.__notebook = true;
        fn.__lambda = { params: ps, body: n.body, env: e };
        return fn;
      };
    }
    case 'where': {
      const binds = n.binds.map(b => ({ name: b.name, f: compile(b.expr, cx) })), body = compile(n.body, cx);
      return e => {
        const env = Object.create(e);
        for (const b of binds) env[b.name] = b.f(env);
        return body(env);
      };
    }
    case 'quant': return compileQuant(n, cx);
    case 'bigop': return compileBigop(n, cx);
    case 'lim': return compileLim(n, cx);
    case 'in': {
      const x = compile(n.elem, cx), D = compileDomain(n.dom, cx), neg = n.neg;
      return e => { const r = D(e).contains(x(e)); return neg ? !r : r; };
    }
    case 'subset': {
      const A = compileDomain(n.a, cx), B = compileDomain(n.b, cx);
      return e => {
        const a = A(e), b = B(e), per = perDepth();
        return atDepth(DEPTH + 1, () => {
          const xs = a.sample(per);
          if (!(finiteSize(a) <= xs.length)) MV.INEXACT = true;
          for (const x of xs) if (!b.contains(x)) return false;
          // Where B is a set we explored, also test the points just outside it that A might contain.
          if (b.outsidePoints) for (const q of b.outsidePoints()) if (a.contains(q) && !b.contains(q)) return false;
          return true;
        });
      };
    }
    case 'setb': return compileSetBuilder(n, cx);
    case 'interval': case 'bound': case 'range': return compileDomain(n, cx);
  }
  throw new MVError('This kind of expression isn\'t supported here.');
}

function compileDomain(n, cx = { q: 0 }) {
  if (n.type === 'interval') {
    const lo = compile(n.lo, cx), hi = compile(n.hi, cx);
    return e => MV.interval(num(lo(e), n.lo), num(hi(e), n.hi), { loOpen: n.loOpen, hiOpen: n.hiOpen });
  }
  if (n.type === 'range') {
    const lo = compile(n.lo, cx), hi = compile(n.hi, cx);
    // 1..0 is empty, so a sum over it is 0 and a product 1, as in the base case of an induction.
    return e => {
      const a = num(lo(e), n.lo), b = num(hi(e), n.hi);
      return a > b ? MV.finite([], { label: '∅' }) : MV.interval(a, b, { integer: true });
    };
  }
  if (n.type === 'bound') {
    const c = compile(n.c, cx), op = n.op, W = 10;
    return e => {
      const v = num(c(e), n.c);
      if (op === '>') return MV.interval(v, v + W, { loOpen: true });
      if (op === '>=') return MV.interval(v, v + W);
      if (op === '<') return MV.interval(v - W, v, { hiOpen: true });
      return MV.interval(v - W, v);
    };
  }
  const f = compile(n, cx), what = ppText(n);
  return e => toDomain(f(e), what);
}

function compileBinders(binders, cx) {
  return binders.map(b => ({ b, dom: compileDomain(b.dom, cx) }));
}

/* Witnesses that sampling would miss, for ∃y ∈ D: … with y real: simple values first (0, ±1, ±2,
   ±1/2, ±3), and the roots of each equation lhs = rhs in the body that involves y, found by
   bisection between sign changes of lhs − rhs. So ∃y ∈ ℝ: y³ = x finds ∛x. */
const NICE = [0, 1, -1, 2, -2, 0.5, -0.5, 3, -3];
function equationsFor(body, b, cx) {
  if (!b || b.pattern) return [];
  const out = [];
  const walk = n => {
    if (n.type === 'bin' && n.op === 'and') { walk(n.a); walk(n.b); return; }
    if (n.type !== 'cmp') return;
    n.ops.forEach((op, i) => {
      if (op !== '=') return;
      const diff = { type: 'bin', op: '-', a: n.args[i], b: n.args[i + 1] };
      if (MV.freeNames(diff).has(b.name)) out.push(compile(diff, cx));
    });
  };
  walk(body);
  return out;
}
const realLine = D => D.kind === 'interval' && D.scalar && !D.integer;
// Over all of ℝ (sampled in [−10, 10]) a witness may lie further out: y > x at x = 10.
const FAR = [11, -11, 100, -100, 1e4, -1e4, 1e8, -1e8];
function niceValues(D) { return realLine(D) ? [...NICE, ...(D.unbounded ? FAR : [])].filter(x => D.contains(x)) : []; }
function rootsFor(D, b, eqs, env) {
  if (!eqs.length || !realLine(D) || MV.EXACT_SAMPLING) return [];
  const N = 96, xs = [];
  for (let k = 0; k <= N; k++) xs.push(D.lo + (D.hi - D.lo) * k / N);
  const roots = [];
  for (const g of eqs) {
    const at = x => {
      const e2 = Object.create(env);
      bindTarget(e2, b, x);
      try { const v = +g(e2); return Number.isFinite(v) ? v : NaN; } catch (err) { return NaN; }
    };
    const gs = xs.map(at);
    // Touching roots (y² = 0) don't change sign: refine each local minimum of |g| by ternary search.
    for (let k = 1; k < xs.length - 1 && roots.length < 12; k++) {
      const a = Math.abs(gs[k]);
      if (!(a <= Math.abs(gs[k - 1]) && a <= Math.abs(gs[k + 1]))) continue;
      if (a === 0) { if (D.contains(xs[k])) roots.push(xs[k]); continue; }
      let lo = xs[k - 1], hi = xs[k + 1];
      for (let it = 0; it < 100; it++) {
        const m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3;
        if (Math.abs(at(m1)) < Math.abs(at(m2))) hi = m2; else lo = m1;
      }
      const r = (lo + hi) / 2;
      if (D.contains(r)) roots.push(r);
    }
    if (gs[0] === 0 && D.contains(xs[0])) roots.push(xs[0]);
    if (gs[N] === 0 && D.contains(xs[N])) roots.push(xs[N]);
    let pa = xs[0], ga = gs[0];
    for (let k = 1; k < xs.length && roots.length < 24; k++) {
      const pb = xs[k], gb = gs[k];
      if (ga * gb < 0) {
        let lo = pa, hi = pb, glo = ga;
        for (let it = 0; it < 80 && hi - lo > 1e-15 * Math.max(1, Math.abs(lo)); it++) {
          const m = (lo + hi) / 2, gm = at(m);
          if (Number.isNaN(gm)) break;
          if (gm === 0) { lo = hi = m; break; }
          if ((gm < 0) === (glo < 0)) { lo = m; glo = gm; } else hi = m;
        }
        const r = (lo + hi) / 2;
        if (D.contains(r)) roots.push(r);
      }
      pa = pb; ga = gb;
    }
  }
  return roots;
}

function compileQuant(n, cx) {
  const inner = { q: cx.q + 1 };
  const body = compile(n.body, inner);
  const bs = compileBinders(n.binders, inner);
  const all = n.q === 'forall';
  const eqs = all ? [] : equationsFor(n.body, bs[bs.length - 1].b, inner);
  return e => {
    const opts = all && !IN_EXISTS ? {} : { deep: true };
    // One or two variables: the depth's sample count (shared √k ways). Three or more: about
    // (depth count)² combinations in total, so ∀x, y, t: … stays affordable.
    const k = bs.length;
    const per = k <= 2 ? Math.max(6, Math.round(perDepth() / Math.sqrt(k))) : Math.max(5, Math.round(Math.pow(perDepth() * perDepth(), 1 / k)));
    const rec = (i, env) => {
      if (i === bs.length) return truth(body(env), n.body);
      const D = bs[i].dom(env);
      // With three or more variables, points of a set (x, y in S) matter more than a scalar
      // parameter (t in [0, 1]), so they get more of the samples, at about the same total cost.
      const share = k >= 3 ? (D.kind === 'interval' && D.scalar ? 0.6 : 1.3) : 1;
      let vals = D.sample(Math.max(4, Math.round(per * share)), opts);
      if (!(finiteSize(D) <= vals.length)) { MV.INEXACT = true; if (!all) MV.SEARCHED = true; }
      if (!all) vals = [...niceValues(D), ...vals];
      const tryAll = list => {
        for (const v of list) {
          const e2 = Object.create(env);
          bindTarget(e2, bs[i].b, v);
          const r = rec(i + 1, e2);
          if (all ? !r : r) return true;
        }
        return false;
      };
      if (tryAll(vals)) return !all;
      if (!all && i === bs.length - 1 && tryAll(rootsFor(D, bs[i].b, eqs, env))) return true;
      return all;
    };
    if (all) return atDepth(DEPTH + 1, () => rec(0, e));
    IN_EXISTS++;
    try { return atDepth(DEPTH + 1, () => rec(0, e)); } finally { IN_EXISTS--; }
  };
}

const finiteSize = D => D.kind === 'finite' ? D.values.length
  : (D.kind === 'interval' && D.integer && !D.unbounded) ? D.size
  : (D.kind === 'product' && D.discrete) ? D.size
  : D.kind === 'structure' ? D.structure.instances().length : Infinity;

function compileBigop(n, cx) {
  const inner = { q: cx.q + 1 };
  const body = compile(n.body, inner), bs = compileBinders(n.binders, inner), op = n.op;
  const exactOnly = op === 'sum' || op === 'prod';
  return e => {
    let acc = op === 'sum' ? 0 : op === 'prod' ? 1 : null, any = false;
    const rec = (i, env) => {
      if (i === bs.length) {
        const v = body(env);
        any = true;
        if (op === 'sum') acc = arith('+', acc, v);
        else if (op === 'prod') acc = arith('*', acc, v);
        else {
          if (typeof v !== 'number') throw new MVError(`${op} needs numbers, but ${ppText(n.body)} is ${describeValue(v)}.`);
          if (acc === null || ((op === 'max' || op === 'sup') ? v > acc : v < acc)) acc = v;
        }
        return;
      }
      const D = bs[i].dom(env), size = finiteSize(D);
      let vals;
      if (exactOnly) {
        if (size > 1e6) throw new MVError(`${op} needs a finite range with at most a million elements, such as 1..n, but the range is ${D.describe()}.`);
        vals = D.sample(Infinity);
      } else if (size <= 1e5) vals = D.sample(Infinity);
      else { vals = D.sample(perDepth() * 2, { deep: true }); MV.INEXACT = true; }
      for (const v of vals) { const e2 = Object.create(env); bindTarget(e2, bs[i].b, v); rec(i + 1, e2); }
    };
    atDepth(DEPTH + 1, () => rec(0, e));
    if (!any) return op === 'sum' ? 0 : op === 'prod' ? 1 : NaN;
    return acc;
  };
}

function compileLim(n, cx) {
  const to = compile(n.to, cx), body = compile(n.body, { q: cx.q + 1 });
  const direct = n.body.type === 'call' && n.body.args.length === 1 && n.body.args[0].type === 'id' &&
    n.body.args[0].name === n.v && !freeNames(n.body.f).has(n.v) ? compile(n.body.f, cx) : null;
  const label = ppText(n.body);
  return e => {
    const target = to(e);
    if (target === Infinity) {
      let s = direct ? direct(e) : null;
      if (typeof s !== 'function') {
        s = k => { const e2 = Object.create(e); e2[n.v] = k; return body(e2); };
        s.label = label;
        // A formula's limit exactly when the asymptotics can tell (1/n → 0, not −8·10⁻¹⁰).
        s.__lambda = { params: [n.v], body: n.body, env: e };
        const L = MV.ASYM && MV.ASYM.seqLimit(s);
        if (L && L.kind === 'finite') return Math.abs(L.v) < 1e-300 ? 0 : L.v;
        if (L && L.kind === 'inf') return L.sign > 0 ? Infinity : -Infinity;
      }
      return MV.limOf(s);
    }
    const f = x => { const e2 = Object.create(e); e2[n.v] = x; return body(e2); };
    return MV.limitAt(f, num(target, n.to));
  };
}

function compileSetBuilder(n, cx) {
  const inner = { q: cx.q + 1 };
  const bs = compileBinders(n.binders, inner), pred = compile(n.pred, inner), text = ppText(n);
  const vars = n.binders.flatMap(binderNames);
  // A binder's range may mention earlier binders ({x in [0, 1], y in [0, x] | …}).
  const earlier = [];
  const depends = n.binders.map(b => {
    const used = freeNames(b.dom.type === 'bound' ? b.dom.c : b.dom);
    const dep = earlier.some(x => used.has(x));
    earlier.push(...binderNames(b));
    return dep;
  });
  return e => {
    const env0 = Object.create(e), doms = [];
    bs.forEach((b, i) => {
      const D = b.dom(env0);
      doms.push(D);
      try { bindTarget(env0, b.b, representative(D)); } catch (err) { /* only used for sampling windows */ }
    });
    const ambient = doms.length === 1 ? doms[0] : MV.product(doms);
    const multi = bs.length > 1;
    const test = v => {
      if (multi && (!Array.isArray(v) || v.length !== bs.length)) return false;
      const env = Object.create(e);
      for (let i = 0; i < bs.length; i++) {
        const part = multi ? v[i] : v;
        const D = depends[i] ? bs[i].dom(env) : doms[i];
        if (!D.contains(part)) return false;
        bindTarget(env, bs[i].b, part);
      }
      return atDepth(DEPTH + 1, () => truth(pred(env), n.pred));
    };
    return MV.predSet({ ambient, test, text, vars });
  };
}

function representative(D) {
  const w = D.window && D.window();
  if (w && typeof w[0] === 'number') return D.integer ? Math.round((w[0] + w[1]) / 2) : (w[0] + w[1]) / 2;
  if (w && Array.isArray(w[0])) return w.map(([a, b]) => (a + b) / 2);
  return D.random();
}

/* ================= Analysing a claim ================= */

const hasQuant = n => !!n && typeof n === 'object' && (n.type === 'quant' || n.type === 'subset' ||
  Object.values(n).some(v => Array.isArray(v) ? v.some(hasQuant) : (v && typeof v === 'object' && v.type ? hasQuant(v) : false)));

function tryEval(node, scope) { try { return compile(node)(scope); } catch (e) { return undefined; } }

// Replace a call to one of your definitions by the definition's body (used inside claims).
function inlineCall(node, scope, boundNames) {
  if (node.type !== 'call') return null;
  let d = null;
  if (node.f.type === 'id') {
    if (boundNames.has(node.f.name)) return null;
    d = DEFS.get(scope[node.f.name]);
  } else if (node.f.type === 'field') {
    // top.T0(S), with "import topology as top": inline only if every name the body uses means the
    // same here as in the library (an aliased import doesn't bring the library's names along).
    let root = node.f;
    while (root.type === 'field') root = root.obj;
    if (root.type !== 'id' || boundNames.has(root.name)) return null;
    d = DEFS.get(tryEval(node.f, scope));
    if (d) {
      const params = new Set(d.params);
      for (const n of freeNames(d.body).keys()) if (!params.has(n) && scope[n] !== d.env[n]) return null;
    }
  }
  if (!d || node.args.length !== d.params.length) return null;
  // Keep calls folded when an argument is an object with facts about this definition.
  if (d.fromLibrary && node.args.some(a => { const v = asSetArg(tryEval(a, scope)); return v && v.facts && d.name in v.facts; })) return null;
  // … or when an analyzer can decide it from a formula given in the call.
  if (d.fromLibrary && MV.ANALYZERS[d.name] && node.args.some(a => a.type === 'lambda' || (a.type === 'id' && MV.ASYM && MV.ASYM.formulaOf(tryEval(a, scope))))) return null;
  return subst(d.body, new Map(d.params.map((p, i) => [p, node.args[i]])));
}

/* Facts: an object (a function, a set, …) may carry known answers for library definitions, as
   obj.facts = { continuous_at: (f, a) => …, integrable_on: true, … }, each a value or a function
   of the call's arguments returning true, false or undefined (unknown: check numerically). An
   entry may be { v, why } to say why. MV.NO_FACTS switches them off (for self-checks). */
// A set passed by its constructor (CantorSet, Q) stands for the set.
const asSetArg = v => (typeof v === 'function' && v.domainCtor ? (() => { try { return toDomain(v); } catch (e) { return v; } })() : v);

function factFor(name, args) {
  if (MV.NO_FACTS) return null;
  for (const a of args) {
    const F = a && (typeof a === 'object' || typeof a === 'function') ? a.facts : null;
    if (!F || !Object.prototype.hasOwnProperty.call(F, name)) continue;
    const entry = F[name];
    const f = entry && typeof entry === 'object' && 'v' in entry ? entry.v : entry;
    let v;
    try { v = typeof f === 'function' ? f(...args) : f; } catch (e) { v = undefined; }
    if (typeof v === 'boolean' || typeof v === 'number') {
      return { v, obj: a, why: (entry && typeof entry === 'object' && entry.why) || '', source: a.source || '' };
    }
  }
  // Analyzers decide from formulas (asymptotic analysis of n ↦ 1/(n ln n), of x ↦ x²·sin(1/x) near 0, …).
  for (const an of MV.ANALYZERS[name] || []) {
    let r = null;
    try { r = an(...args); } catch (e) { r = null; }
    if (r && typeof r.v === 'boolean') return { v: r.v, obj: args[0], why: r.why || '', source: r.source || 'exact asymptotic analysis of the formula' };
  }
  return null;
}

/* ---------- preparing a claim: unfold definitions, peel the leading ∀s, compile the body ---------- */

function prepareClaim(body, env) {
  let node = body, scope = env, bindings = [], unfolded = false;
  // A lemma by name: check its statement.
  if (node.type === 'id') {
    const v = scope[node.name];
    if (v && v.__claim) { node = v.body; scope = v.env; unfolded = true; }
  }
  for (let g = 0; g < 8 && node.type === 'call'; g++) {
    const fv = tryEval(node.f, scope);
    const d = fv && DEFS.get(fv);
    if (!d) break;
    const args = node.args.map(a => compile(a)(scope));
    if (args.length === d.params.length) d.check(args);
    if (d.fromLibrary && factFor(d.name, args)) break;
    if (args.length !== d.params.length) throw new MVError(`${fv.label} takes ${d.params.length} arguments but got ${args.length}.`);
    d.check(args);
    const e2 = Object.create(d.env);
    d.params.forEach((p, i) => { e2[p] = args[i]; });
    bindings = d.params.map((p, i) => [p, args[i]]);
    scope = e2; node = d.body; unfolded = true;
  }

  const U = [];
  for (let g = 0; g < 16; g++) {
    if (node.type === 'quant' && node.q === 'forall') { U.push(...node.binders); node = node.body; continue; }
    if (node.type === 'bin' && node.op === '->' && node.b.type === 'quant' && node.b.q === 'forall') {
      // P → ∀y: Q  is the same claim as  ∀y: P → Q  when y is not used in P.
      const usedInP = freeNames(node.a);
      if (node.b.binders.some(b => binderNames(b).some(x => usedInP.has(x)))) break;
      U.push(...node.b.binders); node = { ...node, b: node.b.body }; continue;
    }
    // Once a variable ranges over named objects (example sets, functions, sequences), keep the
    // definitions folded: the picture is then a gallery of those objects.
    if (U.some(b => { try { const D = compileDomain(b.dom)(scope); return (D.kind === 'finite' && !D.numeric) || D.kind === 'seq'; } catch (e) { return false; } })) break;
    const bound = new Set(U.flatMap(binderNames));
    const isImp = node.type === 'bin' && node.op === '->';
    const inl = inlineCall(isImp ? node.b : node, scope, bound);
    if (!inl) break;
    node = isImp ? { ...node, b: inl } : inl;
    unfolded = true;
  }
  const shown = U.length ? { type: 'quant', q: 'forall', binders: U, body: node } : node;

  let hyp = null, concl = node;
  if (node.type === 'bin' && node.op === '->') { hyp = node.a; concl = node.b; }
  let kind = 'bool';
  if (concl.type === 'cmp' && concl.args.length === 2) kind = 'cmp';
  else if (concl.type === 'quant' && concl.q === 'exists') kind = 'witness';

  const cx = { q: 1 };
  const P = { unfolded, shown, node, bindings, U, scope, kind, hyp, concl, hypF: hyp && compile(hyp, cx), W: null };
  if (kind === 'cmp') { P.Lf = compile(concl.args[0], cx); P.Rf = compile(concl.args[1], cx); P.op = concl.ops[0]; }
  else if (kind === 'witness') {
    const wb = concl.binders[0];
    const rest = concl.binders.length > 1 ? { ...concl, binders: concl.binders.slice(1) } : concl.body;
    P.W = { b: wb, name: wb.name || `(${wb.pattern.join(', ')})`, dom: compileDomain(wb.dom, cx), rest: compile(rest, { q: 2 }), restNode: rest,
      eqs: concl.binders.length === 1 ? equationsFor(rest, wb, { q: 2 }) : [] };
  } else P.boolF = compile(concl, cx);
  P.binders = compileBinders(U, cx);
  P.heavy = kind === 'witness' || hasQuant(concl) || (hyp && hasQuant(hyp));
  P.exact = needsExact(P.node, P.scope, P.U);
  return P;
}

/* Does a claim depend on the kind of a number (rational or not)? Then its real variables are
   sampled with exact rationals and irrationals. Looks through the definitions it uses, the sets
   its variables range over, and the objects in catalogs. */
function needsExact(node, scope, binders = [], depth = 0, seen = new Set()) {
  const flagged = v => !!v && (typeof v === 'object' || typeof v === 'function') && !!v.kindSensitive;
  const check = v => {
    if (flagged(v)) return true;
    if (isDom(v) && v.kind === 'finite' && v.values.some(flagged)) return true;
    const d = DEFS.get(v);
    if (d && depth < 5 && !seen.has(v)) { seen.add(v); return needsExact(d.body, d.env, [], depth + 1, seen); }
    return false;
  };
  let found = false;
  const visit = n => {
    if (found || !n || typeof n !== 'object') return;
    if (Array.isArray(n)) { n.forEach(visit); return; }
    if (n.type === 'id') { let v; try { v = scope[n.name]; } catch (e) { v = undefined; } if (check(v)) found = true; return; }
    if (n.type === 'field' || (n.type === 'call' && n.f && n.f.type === 'field')) { if (check(tryEval(n.type === 'field' ? n : n.f, scope))) { found = true; return; } }
    if (n.binders) for (const b of n.binders) if (b.dom && b.dom.type !== 'bound' && check(tryEval(b.dom, scope))) { found = true; return; }
    for (const [k, v] of Object.entries(n)) if (k !== 'pos' && v && typeof v === 'object') visit(v);
  };
  for (const b of binders) if (b.dom && b.dom.type !== 'bound' && check(tryEval(b.dom, scope))) return true;
  visit(node);
  return found;
}

const marginOf = (op, L, R) => op === '<' || op === '<=' ? R - L : op === '>' || op === '>=' ? L - R : op === '!=' ? Math.abs(L - R) : -Math.abs(L - R);

/* Classify one sample: an environment with the claim's variables bound. Sets r.s to ok / fail /
   vac (hypothesis false) / undef, plus both sides (r.L, r.R, margin r.m) or the witness (r.w).
   r.inexact is set when something inside was sampled or estimated rather than computed exactly. */
function evalSample(P, e, r, factor = 1) {
  MV.INEXACT = false;
  const exactBefore = MV.EXACT_SAMPLING;
  MV.EXACT_SAMPLING = !!P.exact;
  try { return evalSampleIn(P, e, r, factor); } finally { MV.EXACT_SAMPLING = exactBefore; }
}
function evalSampleIn(P, e, r, factor) {
  evalCore(P, e, r, factor);
  if (r.s === 'fail' && P.hypF && onRoundingSeam(P, e, factor)) r.s = 'vac';
  r.inexact = MV.INEXACT;
  return r;
}

/* Tolerant comparisons aren't transitive: −7·10⁻¹³ ≥ 0 holds within rounding, yet |x| = x fails
   there. A failure whose hypothesis is false under exact comparison, and which goes away with a
   slightly looser tolerance, is that seam, not a counterexample. (A float √2 still fails
   x² = 2 ⇒ x ≠ √2·1.1: loosening the tolerance doesn't rescue it.) */
function onRoundingSeam(P, e, factor) {
  let strictHyp;
  try { strictHyp = MV.exact(() => atDepth(1, () => truth(P.hypF(e), P.hyp))); } catch (err) { return false; }
  if (strictHyp) return false;
  const t = MV.TOL;
  MV.TOL = t * 4;
  try { const r2 = {}; evalCore(P, e, r2, factor); return r2.s !== 'fail'; } catch (err) { return false; } finally { MV.TOL = t; }
}

function evalCore(P, e, r, factor) {
  atDepth(1, () => {
    if (P.hypF && !truth(P.hypF(e), P.hyp)) { r.s = 'vac'; return; }
    if (P.kind === 'cmp') {
      const L = P.Lf(e), R = P.Rf(e);
      r.L = L; r.R = R;
      if (typeof L === 'number' && typeof R === 'number') {
        if (Number.isNaN(L) || Number.isNaN(R)) r.s = 'undef';
        else { r.s = compare(P.op, L, R) ? 'ok' : 'fail'; r.m = marginOf(P.op, L, R); }
      } else r.s = compare(P.op, L, R) ? 'ok' : 'fail';
    } else if (P.kind === 'witness') {
      const W = P.W, D = W.dom(e);
      let cands = D.sample(Math.round((P.binders.length === 0 ? 400 : 48) * Math.sqrt(factor)), { deep: true });
      if (!(finiteSize(D) <= cands.length)) { MV.INEXACT = true; MV.SEARCHED = true; }
      P.wInteger = !!D.integer;
      if (cands.every(c => typeof c === 'number')) cands = cands.slice().sort((a, b) => D.integer ? a - b : b - a);
      r.w = undefined;
      IN_EXISTS++;
      try { atDepth(2, () => {
        // The largest sampled witness first (the widest δ), then simple values, then roots.
        const tryAll = list => list.some(c => {
          const e2 = Object.create(e);
          bindTarget(e2, W.b, c);
          if (truth(W.rest(e2), W.restNode)) { r.w = c; return true; }
          return false;
        });
        tryAll(cands) || tryAll(niceValues(D)) || tryAll(rootsFor(D, W.b, W.eqs, e));
      }); } finally { IN_EXISTS--; }
      r.s = r.w !== undefined ? 'ok' : 'fail';
      r.wdom = D;
    } else {
      const v = P.boolF(e);
      r.s = v === true ? 'ok' : v === false ? 'fail' : 'undef';
    }
  });
}

/* Bind given values to the claim's variables, checking each lies in its range. */
function bindValues(P, vals) {
  let e = P.scope;
  for (let i = 0; i < Math.min(P.binders.length, vals.length); i++) {
    const D = P.binders[i].dom(e);
    if (!D.contains(vals[i])) return null;
    e = Object.create(e);
    bindTarget(e, P.binders[i].b, vals[i]);
  }
  return e;
}

/* ---------- the analysis, as a generator: it yields after each sample so callers can pace it ---------- */

/* opts.restrict: [[x0, x1]] or [[x0, x1], [y0, y1]] limits the first coordinates (zoomed views).
   opts.factor multiplies the number of samples. opts.stress swaps example catalogs for wilder ones.
   opts.search: false skips the targeted search after sampling. */
// The claim prepared and its samples, from a seed that depends only on the claim and the options:
// the page can rebuild exactly the samples a background worker used.
function claimSeed(body, opts) {
  const s = ppText(body) + '|' + (opts.factor || 1) + '|' + (opts.stress || 0) + '|' + JSON.stringify(opts.restrict || null);
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
  return h >>> 0;
}
function claimTuples(body, env, opts = {}) {
  MV.STRESS = opts.stress || 0;
  MV.STRESSABLE = false;
  MV.reseed(claimSeed(body, opts));
  const P = prepareClaim(body, env);
  if (opts.restrict) restrictBinders(P.binders, opts.restrict);
  MV.EXACT_SAMPLING = !!P.exact;
  let sampled;
  try { sampled = sampleTuples(P.binders, P.scope, P.heavy, opts.factor || 1); } finally { MV.EXACT_SAMPLING = false; }
  return { P, sampled };
}

/* opts.slice = { k, n }: evaluate only the samples numbered k, k + n, k + 2n, … and return those
   verdicts (a background worker's share of one claim). opts.given = { res, stopped, inexact }:
   verdicts already computed, by sample number; go on to the search and the exact proofs. Each
   sample is evaluated from its own seed, so the split and the whole give the same verdicts. */
function* analyzeSteps(body, env, opts = {}) {
  const stress = opts.stress || 0;
  const { P, sampled } = claimTuples(body, env, opts);
  const factor = opts.factor || 1;
  const { tuples, exhaustive, dom0, examplesOnly } = sampled;
  const seed = claimSeed(body, opts);
  let res = [];
  let stopped = false, inexact = !!examplesOnly;
  if (opts.given) {
    res = opts.given.res.filter(g => tuples[g.i]).map(g => ({ ...g, vals: tuples[g.i].vals, env: tuples[g.i].env }));
    stopped = !!opts.given.stopped;
    inexact = inexact || !!opts.given.inexact;
  } else {
    const sl = opts.slice;
    const t0 = Date.now(), budget = (opts.budget || 30000) * Math.sqrt(factor);
    MV.SEARCHED = false;
    for (let i = 0; i < tuples.length; i++) {
      if (sl && i % sl.n !== sl.k) continue;
      if (Date.now() - t0 > budget) { stopped = true; break; }
      MV.STRESS = stress;
      MV.reseed((seed + Math.imul(i + 1, 0x9E3779B1)) >>> 0);
      const r = evalSample(P, tuples[i].env, { vals: tuples[i].vals, env: tuples[i].env, s: 'ok' }, factor);
      r.i = i;
      inexact = inexact || r.inexact;
      res.push(r);
      if ((i & 3) === 3) yield { phase: 'sampling', done: i + 1, total: tuples.length };
    }
    // A strict inequality that "fails" only within rounding of a tie (L ≈ R) but holds in exact
    // floating point is not a counterexample: samples hugging an open boundary do that.
    if (strictCmp(P)) {
      let n = 0;
      for (const r of res) if (r.s === 'fail' && n++ < 400 && tieHolds(P, r, factor)) { r.s = 'ok'; r.tie = true; }
    }
    // A sample that failed because no witness (δ, N, …) was found among the usual candidates is
    // looked at again with candidates creeping much closer to the open end (down to 1e-14): δ for
    // √x near 0 must be about ε², below the usual search for small ε.
    if (MV.SEARCHED) {
      const t1 = Date.now();
      let n = 0;
      for (const r of res) {
        if (r.s !== 'fail' || n++ >= 24 || Date.now() - t1 > 400 * Math.sqrt(factor)) continue;
        MV.reseed((seed + Math.imul(r.i + 1, 0x9E3779B1)) >>> 0);
        if (deeperHolds(P, r, factor)) { r.s = 'ok'; r.deeper = true; } else r.deeperTried = true;
      }
    }
    if (sl) { MV.STRESS = 0; return { slice: true, res, stopped, inexact, total: tuples.length }; }
  }
  const info = {
    unfolded: P.unfolded, shown: P.shown, body: P.node, bindings: P.bindings, binders: P.U, scope: P.scope, k: P.U.length,
    kind: P.kind, hyp: P.hyp, concl: P.concl, op: P.op, W: P.W, wInteger: P.wInteger ?? null, res, dom0,
    exhaustive: exhaustive && !stopped, stopped, total: tuples.length, restricted: !!opts.restrict, factor, stress, prepared: P,
  };
  if (opts.search !== false && !stopped) {
    MV.STRESS = stress;
    yield* searchCounterexamples(info, P);
  }
  info.count = { ok: 0, fail: 0, vac: 0, undef: 0 };
  for (const r of res) info.count[r.s]++;
  info.stressable = !!MV.STRESSABLE;
  info.proved = info.exhaustive && !inexact && info.k > 0 && info.count.ok > 0 && !info.count.fail && !info.count.undef;
  // An equation whose two sides simplify to the same expression is proved by algebra.
  if (!info.proved && !info.count.fail && !info.count.undef && MV.symbolicClaim) {
    const alg = MV.symbolicClaim(P);
    if (alg && alg.identity) { info.algebra = alg; if (alg.proved) info.proved = true; }
  }
  // Inequalities (and |…|, min, max): proved exactly for every value the ranges and hypotheses allow.
  // Samples that "fail" only by a rounding tie (t²/(1 + t²) < 1 at t = 10⁸, where both sides round
  // to 1) don't stop the attempt; if the exact proof succeeds they were rounding, and say so.
  const ties = info.count.fail > 0 && P.kind === 'cmp' && info.res.every(r => r.s !== 'fail' ||
    (typeof r.L === 'number' && typeof r.R === 'number' && Math.abs(r.L - r.R) <= 1e-9 * Math.max(1, Math.abs(r.L), Math.abs(r.R))));
  if (!info.proved && (!info.count.fail || ties) && !info.count.undef && MV.inequalityClaim) {
    const iq = MV.inequalityClaim(P);
    if (iq && iq.proved) {
      if (ties) {
        const n = info.count.fail;
        for (const r of info.res) if (r.s === 'fail') { r.s = 'ok'; r.tie = true; }
        info.count.ok += n; info.count.fail = 0; info.simplest = null;
        iq.note += ` ${n === 1 ? 'One sample seemed' : `${n} samples seemed`} to fail, but only by rounding: there both sides are equal in floating point.`;
      }
      info.algebra = iq; info.proved = true;
    }
  }
  MV.STRESS = 0;
  return info;
}

const strictCmp = P => P.kind === 'cmp' && (P.op === '<' || P.op === '>');
function tieHolds(P, r, factor) {
  if (!strictCmp(P)) return false;
  try {
    return MV.exact(() => {
      const e = bindValues(P, r.vals) || r.env;
      return evalSample(P, e, { vals: r.vals, env: e, s: 'ok' }, factor).s === 'ok';
    });
  } catch (err) { return false; }
}

// With exact comparisons: below the tolerance (1e-9) a tolerant x < 0.5 can't see a jump at 0.5,
// and a jump must stay a jump however small δ gets.
function deeperHolds(P, r, factor) {
  const before = MV.DEEPER;
  MV.DEEPER = true;
  try {
    return MV.exact(() => {
      const e = bindValues(P, r.vals) || r.env;
      return evalSample(P, e, { vals: r.vals, env: e, s: 'ok' }, factor).s === 'ok';
    });
  } catch (err) { return false; } finally { MV.DEEPER = before; }
}

function analyzeClaim(body, env, opts = {}) {
  const g = analyzeSteps(body, env, opts);
  for (;;) { const r = g.next(); if (r.done) return r.value; }
}

/* Run a generator in slices of about 25 ms, so the page stays responsive. ctl.cancelled stops it;
   ctl.onProgress(step) is told how far it got. */
// Give the page a moment (input, drawing) between slices of work. A message, not setTimeout:
// timers are slowed to once a second in background tabs, so a long check would crawl there.
MV.yieldNow = () => new Promise(res => {
  if (typeof MessageChannel !== 'function') { setTimeout(res, 0); return; }
  const ch = new MessageChannel();
  ch.port1.onmessage = () => { ch.port1.close(); res(); };
  ch.port2.postMessage(0);
});
async function runSliced(gen, ctl = {}) {
  let t = Date.now();
  for (;;) {
    const r = gen.next();
    if (r.done) return r.value;
    if (Date.now() - t > 25) {
      if (ctl.onProgress) ctl.onProgress(r.value);
      await MV.yieldNow();
      if (ctl.cancelled) { MV.STRESS = 0; throw new MVError('Stopped.'); }
      t = Date.now();
    }
  }
}
const analyzeClaimAsync = (body, env, opts, ctl) => runSliced(analyzeSteps(body, env, opts), ctl);

/* ---------- after sampling: simplest counterexample, or a targeted search for one ---------- */

const isNumArr = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');

// Simple numbers near x, simplest first: integers, then halves, thirds, quarters, …, twelfths.
function simpleNear(x, radius) {
  const out = [];
  for (const q of [1, 2, 3, 4, 5, 6, 8, 10, 12]) {
    const lo = Math.ceil((x - radius) * q), hi = Math.floor((x + radius) * q);
    const ps = [];
    for (let p = lo; p <= hi && ps.length < 60; p++) if (q === 1 || gcd(Math.abs(p), q) === 1) ps.push(p);
    ps.sort((a, b) => Math.abs(a / q - x) - Math.abs(b / q - x));
    for (const p of ps) out.push(p / q);
  }
  return out;
}
const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };

/* tieStart: a point where a strict inequality is only a rounding tie; simplifying it may reach a
   real counterexample (x = 0 for x² > 0). Then returns whether it found one. */
function* searchCounterexamples(info, P, tieStart = null) {
  const fails = tieStart ? [tieStart] : info.res.filter(r => r.s === 'fail');
  if (fails.length) {
    // Simplify: replace each value by the simplest nearby one that still fails.
    let best = fails.slice().sort((a, b) => (a.m ?? 0) - (b.m ?? 0))[0];
    const start = best;
    let vals = best.vals.slice(), tries = 0;
    const attempt = cand => {
      tries++;
      // Candidates must lie in their ranges exactly, not just within rounding of them.
      const e = MV.exact(() => bindValues(P, cand));
      if (!e) return null;
      const r = evalSample(P, e, { vals: cand, env: e, s: 'ok' }, info.factor);
      return r.s === 'fail' && !tieHolds(P, r, info.factor) ? r : null;
    };
    for (let i = 0; i < vals.length && tries < 600; i++) {
      const v = vals[i];
      if (isEx(v)) {
        for (const c of MV.EX.simpleExactNear(+v, Math.max(2, 2 * Math.abs(+v)), MV.EX.kindOf(v))) {
          if (tries >= 600) break;
          if (MV.EX.equalExact(c, v) === true && MV.EX.kindOf(c) === MV.EX.kindOf(v)) break;
          const cand = vals.slice(); cand[i] = c;
          const prevExact = MV.EXACT_SAMPLING;
          MV.EXACT_SAMPLING = !!P.exact;
          let r;
          try { r = attempt(cand); } finally { MV.EXACT_SAMPLING = prevExact; }
          if (r) { vals = cand; best = r; break; }
          if ((tries & 15) === 0) yield { phase: 'simplifying' };
        }
      } else if (typeof v === 'number') {
        const D = (() => { try { return P.binders[i].dom(bindValues(P, vals.slice(0, i).concat(vals.slice(i))) || P.scope); } catch (e) { return null; } })();
        const span = D && D.window ? (w => typeof w[0] === 'number' ? w[1] - w[0] : 1)(D.window()) : 1;
        for (const c of simpleNear(v, Math.max(1, span / 2))) {
          if (tries >= 600) break;
          if (c === v) break;
          const cand = vals.slice(); cand[i] = c;
          const r = attempt(cand);
          if (r) { vals = cand; best = r; break; }
          if ((tries & 15) === 0) yield { phase: 'simplifying' };
        }
      } else if (isNumArr(v)) {
        for (let j = 0; j < v.length && tries < 600; j++) {
          for (const c of simpleNear(v[j], 1)) {
            if (tries >= 600 || c === v[j]) break;
            const pt = vals[i].slice(); pt[j] = c;
            const cand = vals.slice(); cand[i] = pt;
            const r = attempt(cand);
            if (r) { vals = cand; best = r; break; }
            if ((tries & 15) === 0) yield { phase: 'simplifying' };
          }
        }
      } else {
        // Named objects: an earlier (simpler) example from the same catalog that also fails.
        let D = null;
        try { D = P.binders[i].dom(P.scope); } catch (e) { D = null; }
        let pool = null;
        try { pool = D && D.kind === 'finite' ? D.values : D && D.kind === 'structure' ? D.sample() : D && D.simpleFirst ? D.sample(80) : null; } catch (e) { pool = null; }
        if (pool) {
          // With an earlier object, the later variables may need new values too (x = 3 means
          // nothing in a space on {1, 2}), so try a few of their values as well.
          const later = (cand, j) => {
            if (j >= vals.length) return attempt(cand);
            const direct = attempt(cand);
            if (direct) return direct;
            let Dj = null;
            try { Dj = P.binders[j].dom(bindValues(P, cand.slice(0, j)) || P.scope); } catch (e) { return null; }
            let xs = [];
            try { xs = Dj.sample(12); } catch (e) { return null; }
            for (const x of xs) {
              if (tries >= 600) return null;
              const c2 = cand.slice(); c2[j] = x;
              const r = later(c2, j + 1);
              if (r) { cand.splice(0, cand.length, ...c2); return r; }
            }
            return null;
          };
          for (const c of pool) {
            if (c === v || tries >= 600) break;
            const cand = vals.slice(); cand[i] = c;
            const r = later(cand, i + 1);
            if (r) { vals = r.vals.slice(); best = r; break; }
            yield { phase: 'simplifying' };
          }
        }
      }
    }
    // Exact values that only work together (x = √2, y = −√2 for "x + y is irrational") can't be
    // simplified one at a time: try pairs of simple values.
    const complicated = vals.map((v, i) => (isEx(v) && MV.EX.fmtExact(v).length > 7 ? i : -1)).filter(i => i >= 0);
    if (complicated.length >= 2) {
      const [i, j] = complicated;
      const ci = MV.EX.simpleExactNear(+vals[i], Math.max(2, 2 * Math.abs(+vals[i])), MV.EX.kindOf(vals[i])).slice(0, 14);
      const cj = MV.EX.simpleExactNear(+vals[j], Math.max(2, 2 * Math.abs(+vals[j])), MV.EX.kindOf(vals[j])).slice(0, 14);
      const prevExact = MV.EXACT_SAMPLING;
      MV.EXACT_SAMPLING = !!P.exact;
      try {
        pairs: for (const a of ci) for (const b of cj) {
          const cand = vals.slice(); cand[i] = a; cand[j] = b;
          const r = attempt(cand);
          if (r) { vals = cand; best = r; break pairs; }
          if ((tries & 15) === 0) yield { phase: 'simplifying' };
        }
      } finally { MV.EXACT_SAMPLING = prevExact; }
    }
    if (tieStart) {
      if (best === start) return false;
      best.found = 'search';
      info.res.push(best);
      info.simplest = best;
      return true;
    }
    info.simplest = best;
    return;
  }
  // No counterexample among the samples: search where the claim comes closest to failing.
  if (P.kind !== 'cmp' || !info.res.length) return;
  const shape = info.res[0].vals.map(v => typeof v === 'number' ? 1 : isNumArr(v) ? v.length : 0);
  if (shape.some(s => s === 0)) return;
  const dims = shape.reduce((a, b) => a + b, 0);
  if (!dims) return;   // nothing to move: a claim without variables was checked once, completely
  const toVals = x => { const out = []; let k = 0; for (const s of shape) { out.push(s === 1 ? x[k] : x.slice(k, k + s)); k += s; } return out; };
  const flatVals = vals => vals.flatMap(v => typeof v === 'number' ? [v] : v);
  const intMask = P.binders.map((b, i) => { try { return !!P.binders[i].dom(P.scope).integer; } catch (e) { return false; } });
  if (intMask.some(Boolean) && intMask.every(Boolean)) return;   // whole-number ranges were sampled densely already
  let evals = 0, found = null, bestR = null, tie = null;
  const f = x => {
    evals++;
    const vals = toVals(x);
    const e = MV.exact(() => bindValues(P, vals));
    if (!e) return Infinity;
    const r = evalSample(P, e, { vals, env: e, s: 'ok' }, info.factor);
    if (r.s === 'fail' && !found) { if (!tieHolds(P, r, info.factor)) found = r; else if (!tie) tie = r; }
    if (r.s !== 'ok' && r.s !== 'fail') return Infinity;
    if (!bestR || r.m < bestR.m) bestR = r;
    return r.m;
  };
  const starts = info.res.filter(r => typeof r.m === 'number').sort((a, b) => a.m - b.m).slice(0, 6);
  const t0 = Date.now();
  for (const s of starts) {
    const x0 = flatVals(s.vals);
    const scale = x0.map(v => Math.max(1e-3, Math.abs(v) * 0.05, 0.05));
    yield* nelderMead(f, x0, scale, 250, () => found || Date.now() - t0 > 2500);
    if (found || Date.now() - t0 > 2500) break;
  }
  info.searched = { evals, found: !!found, best: bestR };
  if (found) { found.found = 'search'; info.res.push(found); info.simplest = found; }
  else if (tie && (yield* searchCounterexamples(info, P, tie))) info.searched.found = true;
}

/* Nelder–Mead minimisation (a generator, so it can be paced). */
function* nelderMead(f, x0, scale, maxIter, stop) {
  const n = x0.length;
  let simplex = [x0.slice()];
  for (let i = 0; i < n; i++) { const x = x0.slice(); x[i] += scale[i]; simplex.push(x); }
  let fx = simplex.map(f);
  for (let it = 0; it < maxIter; it++) {
    if (stop()) return;
    const order = fx.map((v, i) => i).sort((a, b) => fx[a] - fx[b]);
    simplex = order.map(i => simplex[i]); fx = order.map(i => fx[i]);
    const c = Array(n).fill(0);
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) c[j] += simplex[i][j] / n;
    const at = t => c.map((v, j) => v + t * (simplex[n][j] - v));
    const xr = at(-1), fr = f(xr);
    if (fr < fx[0]) {
      const xe = at(-2), fe = f(xe);
      if (fe < fr) { simplex[n] = xe; fx[n] = fe; } else { simplex[n] = xr; fx[n] = fr; }
    } else if (fr < fx[n - 1]) { simplex[n] = xr; fx[n] = fr; }
    else {
      const xc = at(0.5), fc = f(xc);
      if (fc < fx[n]) { simplex[n] = xc; fx[n] = fc; }
      else for (let i = 1; i <= n; i++) { simplex[i] = simplex[i].map((v, j) => simplex[0][j] + 0.5 * (v - simplex[0][j])); fx[i] = f(simplex[i]); }
    }
    if ((it & 7) === 7) yield { phase: 'searching' };
  }
}

// Limit the first coordinates to a zoomed window: [[x0, x1]] for one number, [[x0, x1], [y0, y1]] for a point or two numbers.
function restrictBinders(binders, box) {
  const wrap = (b, range) => { const dom = b.dom; b.dom = e => MV.restrictSpace(dom(e), range); };
  if (binders.length === 1) wrap(binders[0], box);
  else if (binders.length >= 2) { wrap(binders[0], [box[0]]); if (box[1]) wrap(binders[1], [box[1]]); }
}

function sampleTuples(binders, scope, heavy, factor = 1) {
  const k = binders.length;
  if (k === 0) return { tuples: [{ vals: [], env: scope }], exhaustive: true, dom0: null };
  let exhaustive = true, examplesOnly = false;
  // A result over a structure's examples (forall M in MetricSpace) covers those examples, not
  // every metric space, so it can't be called proved.
  const done = r => Object.assign(r, { examplesOnly });
  const take = (D, n, opts) => {
    if (D.kind === 'structure') examplesOnly = true;
    const vals = D.sample(n, opts);
    if (!(finiteSize(D) <= n && vals.length >= finiteSize(D))) exhaustive = false;
    return vals;
  };
  const nested = (count, opts) => {
    const out = [];
    const rec = (i, e, vals) => {
      if (i === k) { out.push({ vals: vals.slice(), env: e }); return; }
      const D = binders[i].dom(e);
      for (const v of take(D, count(D), opts)) {
        const e2 = Object.create(e);
        bindTarget(e2, binders[i].b, v);
        vals.push(v);
        rec(i + 1, e2, vals);
        vals.pop();
      }
    };
    rec(0, scope, []);
    return out;
  };
  const dom0 = binders[0].dom(scope);
  const f = factor, sf = Math.sqrt(factor);
  if (k === 1) {
    const dim = dom0.dim;
    const n = Math.round(f * (dim === 1 ? (heavy ? 120 : 400)
      : dim === 2 ? (dom0.kind === 'product' ? (heavy ? 900 : 6400) : (heavy ? 300 : 900))
      : typeof dim === 'number' ? (heavy ? 300 : 2000)
      : (heavy ? 60 : 160)));
    // A list of models (all magmas on 3 elements, …) is checked in full when it isn't huge.
    const all = dom0.kind === 'finite' && dom0.values.length <= 5000 * f ? dom0.values.length : 0;
    return done({ tuples: nested(() => Math.max(n, all), { grid: dom0.kind === 'product' }), exhaustive, dom0 });
  }
  if (k === 2) {
    const per = D => Math.round(sf * (D.dim === 1 ? (heavy ? 30 : 80) : (heavy ? 16 : 64)));
    return done({ tuples: nested(per, { grid: true }), exhaustive, dom0 });
  }
  // Three or more variables: every case if the ranges are small and finite, otherwise random samples.
  try {
    const e = Object.create(scope);
    let total = 1;
    for (const b of binders) { const D = b.dom(e); total *= finiteSize(D); bindTarget(e, b.b, D.random()); }
    if (total <= 4000 * f) return done({ tuples: nested(() => 4000 * f, {}), exhaustive, dom0 });
  } catch (err) { /* dependent or infinite ranges */ }
  const T = Math.round(f * (heavy ? 400 : 2500)), out = [];
  for (let t = 0; t < T; t++) {
    let e = scope;
    const vals = [];
    try {
      for (const b of binders) {
        const v = b.dom(e).random();
        e = Object.create(e);
        bindTarget(e, b.b, v);
        vals.push(v);
      }
    } catch (err) { if (err instanceof MVError) continue; throw err; }   // an empty range: nothing to check here
    out.push({ vals, env: e });
  }
  return done({ tuples: out, exhaustive: false, dom0 });
}

/* ================= Explaining a result: an evaluation tree ================= */

/* Evaluates a formula at an environment and records why it came out the way it did:
   which part of a conjunction failed, the counterexample of a ∀, the witness of an ∃,
   and what a definition unfolds to. */
function trace(node, env, budget = 6) {
  const evalAt = (n, e) => { try { return { v: compile(n)(e) }; } catch (err) { return { err: err.message }; } };
  const out = { node, ...evalAt(node, env), kids: [], note: null, label: null };
  if (budget <= 0 || out.err) return out;
  const sub = (n, e, label) => { const t = trace(n, e, budget - 1); t.label = label || null; out.kids.push(t); return t; };
  switch (node.type) {
    case 'bin':
      if (node.op === 'and' || node.op === 'or' || node.op === '<->') {
        const a = sub(node.a, env);
        const decided = (node.op === 'and' && a.v === false) || (node.op === 'or' && a.v === true);
        if (!decided) sub(node.b, env);
      } else if (node.op === '->') {
        const a = sub(node.a, env, 'if');
        if (a.v === true) sub(node.b, env, 'then'); else out.note = 'The hypothesis is false, so the implication holds.';
      }
      break;
    case 'un': if (node.op === 'not') sub(node.a, env); break;
    case 'cmp': node.args.forEach(a => { if (a.type !== 'num') sub(a, env); }); break;
    case 'where': {
      const e2 = Object.create(env);
      for (const b of node.binds) e2[b.name] = compile(b.expr)(e2);
      sub(node.body, e2);
      break;
    }
    case 'quant': {
      const all = node.q === 'forall';
      const found = findBinding(node, env, !all);
      atDepth(DEPTH + 1, () => {
        if (found.hit) sub(node.body, found.hit.env, `${all ? 'fails at' : 'witness:'} ${found.hit.text}`);
        else {
          out.note = all ? `Holds at all ${found.count} values tried.` : `None of the ${found.count} values tried works.`;
          if (!all && found.first) sub(node.body, found.first.env, `for example at ${found.first.text}`);
        }
      });
      break;
    }
    case 'subset': {
      try {
        const A = compileDomain(node.a)(env), B = compileDomain(node.b)(env);
        const bad = A.sample(perDepth()).find(x => !B.contains(x));
        const precise = v => Array.isArray(v) ? '(' + v.map(precise).join(', ') + ')' : typeof v === 'number' ? MV.fmtNum(+v.toPrecision(12)) : fmt(v);
        const off = bad !== undefined && A.kind === 'ball' ? ` It lies ${fmt(+MV.pdist(bad, A.center).toPrecision(3))} from the center.` : '';
        out.note = bad !== undefined ? `${precise(bad)} is in the first set but not in the second.${off}` : 'Every sampled point of the first set is in the second.';
      } catch (err) { /* keep the value only */ }
      break;
    }
    case 'call': {
      const f = tryEval(node.f, env);
      const d = f && DEFS.get(f);
      const known = d && d.fromLibrary && factFor(d.name, node.args.map(a => asSetArg(tryEval(a, env))));
      if (known) {
        out.note = `Known: ${known.why || `a fact about ${fmt(known.obj)}`}${known.source ? ` (${known.source})` : ''}.`;
        break;
      }
      if (d && node.args.length === d.params.length) {
        const e2 = Object.create(d.env);
        d.params.forEach((p, i) => { e2[p] = compile(node.args[i])(env); });
        sub(d.body, e2, `by the definition of ${f.label}, with ${d.params.map(p => `${p} = ${fmt(e2[p])}`).join(', ')}`);
      }
      break;
    }
  }
  return out;
}

function findBinding(node, env, target) {
  const bs = compileBinders(node.binders, { q: 0 });
  const per = Math.max(6, Math.round(perDepth() / Math.sqrt(bs.length)));
  const opts = node.q === 'forall' ? {} : { deep: true };
  const body = compile(node.body);
  const eqs = node.q === 'exists' ? equationsFor(node.body, bs[bs.length - 1].b, { q: 0 }) : [];
  let count = 0, first = null, hit = null;
  const rec = (i, e, parts) => {
    if (hit || count > 20000) return;
    if (i === bs.length) {
      count++;
      const text = parts.join(', ');
      if (!first) first = { env: e, text };
      let v;
      try { v = atDepth(DEPTH + 1, () => body(e)); } catch (err) { v = undefined; }
      if (v === target) hit = { env: e, text };
      return;
    }
    const D = bs[i].dom(e);
    const vals = node.q === 'exists' ? [...niceValues(D), ...D.sample(per, opts)] : D.sample(per, opts);
    for (const v of vals) {
      const e2 = Object.create(e);
      bindTarget(e2, bs[i].b, v);
      const nm = bs[i].b.pattern ? `(${bs[i].b.pattern.join(', ')})` : bs[i].b.name;
      rec(i + 1, e2, [...parts, `${nm} = ${fmt(v)}`]);
      if (hit) return;
    }
    if (node.q === 'exists' && i === bs.length - 1) for (const v of rootsFor(D, bs[i].b, eqs, e)) {
      const e2 = Object.create(e);
      bindTarget(e2, bs[i].b, v);
      rec(i + 1, e2, [...parts, `${bs[i].b.name} = ${fmt(v)}`]);
      if (hit) return;
    }
  };
  rec(0, env, []);
  return { hit, first, count };
}

/* ================= Libraries ================= */

function normalizeDef(def) {
  if (!def || typeof def !== 'object') throw new Error('define() expects an object.');
  if (typeof def.name !== 'string' || !/^[A-Za-z_]\w*$/.test(def.name)) throw new Error('define() needs a name made of letters, digits and _.');
  const docs = Object.assign({}, def.docs || {});
  const functions = {};
  for (const [k, f] of Object.entries(def.functions || {})) {
    if (f && typeof f === 'object' && typeof f.fn === 'function') { functions[k] = f.fn; if (f.doc) docs[k] = f.doc; }
    else if (typeof f === 'function') functions[k] = f;
    else throw new Error(`functions.${k} must be a function, or { doc, fn }.`);
  }
  const domains = {};
  for (const [k, v] of Object.entries(def.domains || def.spaces || {})) {
    if (v && typeof v === 'object' && !v.__domain && (typeof v.fn === 'function' || v.space)) { domains[k] = v.fn || v.space; if (v.doc) docs[k] = v.doc; }
    else domains[k] = v;
  }
  for (const [k, v] of Object.entries(def.views || {})) {
    if (!v || typeof v.render !== 'function') throw new Error(`views.${k} needs a render(ctx, ...args) function.`);
    if (v.doc) docs[k] = v.doc;
  }
  for (const T of def.types || []) if (!T || typeof T.test !== 'function' || typeof T.ops !== 'object') throw new Error('Each type needs a name, a test(value) function and an ops object.');
  return { ...def, functions, domains, docs };
}

let EVAL_OK = true;
try { EVAL_OK = new Function('return 1')() === 1; } catch (e) { EVAL_OK = false; }

function registerJS(source, meta = {}) {
  let captured = null;
  const api = Object.assign({}, MathViz, { define(def) { captured = def; } });
  try {
    if (typeof source === 'function') source(api);
    else {
      if (!EVAL_OK) throw new Error('This page isn\'t allowed to run pasted JavaScript. Notation libraries still work, and JavaScript libraries work when you open index.html locally.');
      const body = source.replace(/^\s*MathVizLibrary\s*\(\s*function\s*\w*\s*\(\s*MathViz\s*\)\s*\{([\s\S]*)\}\s*\)\s*;?\s*$/, '$1');
      new Function('MathViz', body)(api);
    }
    if (!captured) throw new Error('The library never called MathViz.define({ … }).');
    for (const x of MV.REPRESENT) if (!x.lib) x.lib = captured.name;
    captured = normalizeDef(captured);
    if (captured.notation) captured.section = parseNotation(captured.notation, false);
  } catch (e) {
    return { ...meta, kind: 'js', name: (captured && captured.name) || meta.name || 'untitled', error: e.message };
  }
  const sec = captured.section;
  return { ...meta, kind: 'js', name: captured.name, def: captured, description: captured.description || '',
    docs: { ...captured.docs, ...(sec ? sec.docs : {}) }, section: sec || null, names: sec ? sec.names : [], lemmas: sec ? sec.lemmas : [], structures: sec ? sec.structures || [] : [] };
}

/* Documentation of a statement: the comment lines right above it. A line "examples: x in S, …"
   is not shown; it gives the default examples for explain. */
function docOf(stmt) {
  const lines = (stmt && stmt.docLines) || [];
  const doc = lines.filter(l => !/^\s*examples\s*:/.test(l)).join(' ').trim();
  const ex = lines.map(l => /^\s*examples\s*:\s*(.*)$/.exec(l)).find(Boolean);
  return { doc, examples: ex ? ex[1] : null };
}

/* Parse the statements of a notation section: a notation library, or the `notation` field of a
   JavaScript library. Sections may contain import, let, def and named lemmas. */
function parseNotation(source, requireHeader) {
  const sec = { statements: [], names: [], docs: {}, lemmas: [], description: '', name: null };
  const comments = [];
  for (const line of source.split('\n')) {
    if (/^\s*library\b/.test(line) && !comments.length) continue;
    const m = /^\s*#\s?(.*)$/.exec(line);
    if (m) comments.push(m[1]); else break;
  }
  sec.description = comments.join(' ').trim();
  sec.statements = splitStatements(source).map(s => {
    try { return { stmt: s, ast: parseStatement(s) }; }
    catch (err) { err.message = `Line ${locate(s, err.pos).line}: ${err.message}`; throw err; }
  });
  let body = sec.statements;
  if (requireHeader) {
    const head = body[0];
    if (!head || head.ast.type !== 'library') throw new Error('A notation library starts with a line like "library mylib".');
    sec.name = head.ast.name;
    body = body.slice(1);
  }
  sec.body = body;
  const agree = [];
  for (const { ast, stmt } of body) {
    const { doc } = docOf(stmt);
    const own = doc && doc !== sec.description ? doc : '';
    if (ast.type === 'def' || ast.type === 'let') {
      sec.names.push(ast.name);
      if (own) sec.docs[ast.name] = own;
    } else if (ast.type === 'check') {
      if (!ast.name) throw new Error(`Line ${stmt.line}: a lemma in a library needs a name, as in "lemma my_lemma: …".`);
      sec.lemmas.push({ name: ast.name, kind: ast.kind, ast });
      if (own) sec.docs[ast.name] = own;
    } else if (ast.type === 'structure') {
      (sec.structures = sec.structures || []).push(ast.name);
      if (own) sec.docs[ast.name] = own;
    } else if (ast.type === 'concept') {
      for (const n of conceptNames(ast)) sec.names.push(n);
      (sec.forms = sec.forms || []).push(...conceptNames(ast).slice(1));
      (sec.concepts = sec.concepts || []).push(ast.name);
      if (own) sec.docs[ast.name] = own;
      ast.forms.forEach((f, i) => { sec.docs[`${ast.name}_${f.name}`] = `${own ? own.replace(/\.?$/, '') + ': ' : ''}the ${ordinal(i)} form, "${f.name}", of ${ast.name}.`; });
      // With examples, the library also states that the forms agree on them, so the tests check it.
      const ex = docOf(stmt).examples;
      if (ex && ast.params) agree.push(agreementLemma(ast, ex, stmt));
    } else if (ast.type !== 'import') throw new Error(`Line ${stmt.line}: a library can contain import, let, def, structure, concept and named lemmas.`);
  }
  for (const a of agree) { sec.body.push(a); sec.lemmas.push({ name: a.ast.name, kind: 'lemma', ast: a.ast, tame: true }); sec.docs[a.ast.name] = a.doc; }
  return sec;
}

const ordinal = i => ['first', 'second', 'third', 'fourth', 'fifth', 'sixth'][i] || `${i + 1}th`;

// Does a formula give true or false (rather than a number or an object)?
function propositional(node) {
  if (!node) return false;
  if (node.type === 'quant' || node.type === 'bool') return true;
  if (node.type === 'un') return node.op === 'not';
  if (node.type === 'bin') return ['and', 'or', '->', '<->', '<', '<=', '>', '>=', '=', '!=', '~=', 'in', 'notin', 'subset'].includes(node.op);
  if (node.type === 'cmp' || node.type === 'in' || node.type === 'subset') return true;
  if (node.type === 'where') return propositional(node.body);
  return false;
}

/* lemma name_forms_agree: forall examples: form₁(p) <-> form₂(p) and …, written as a statement so
   it reads like the other lemmas of the library. */
function agreementLemma(ast, examples, stmt) {
  const call = f => `${ast.name}_${f.name}(${ast.params.join(', ')})`;
  const op = ast.forms.some(f => propositional(f.body)) ? '<->' : '=';
  const [first, ...rest] = ast.forms;
  const body = rest.map(f => `(${call(first)} ${op} ${call(f)})`).join(' and ');
  const name = `${ast.name}_forms_agree`;
  const own = { text: `lemma ${name}: forall ${examples}: ${body}`, line: stmt.line, lines: [stmt.line], docLines: [] };
  let node;
  try { node = parseStatement(own); }
  catch (err) { throw new Error(`Line ${stmt.line}: the "examples:" line of ${ast.name} doesn't parse: ${err.message}`); }
  return { ast: node, stmt: own, doc: `The ${ast.forms.length} forms of ${ast.name} (${ast.forms.map(f => f.name).join(', ')}) agree on its examples.` };
}

function registerNotation(source, meta = {}) {
  source = source.replace(/^\s*MathVizNotation\s*\(\s*`([\s\S]*)`\s*\)\s*;?\s*$/, '$1');
  const entry = { ...meta, kind: 'notation', source, names: [], docs: {}, lemmas: [], description: '' };
  try {
    const sec = parseNotation(source, true);
    Object.assign(entry, { name: sec.name, names: sec.names, docs: sec.docs, lemmas: sec.lemmas, structures: sec.structures || [], description: sec.description, section: sec });
  } catch (e) {
    entry.error = e.message;
    if (!entry.name) entry.name = (/^\s*library\s+(\w+)/m.exec(source) || [])[1] || 'untitled';
  }
  return entry;
}

function rebuildIndex() {
  NAME_INDEX = new Map(); VIEW_INDEX = new Map();
  const add = (k, lib) => { if (!NAME_INDEX.has(k)) NAME_INDEX.set(k, lib); };
  for (const lib of REG.values()) {
    if (lib.error) continue;
    if (lib.def) {
      const d = lib.def;
      for (const k of [...Object.keys(d.functions), ...Object.keys(d.constants || {}), ...Object.keys(d.domains)]) add(k, lib.name);
      for (const k of Object.keys(d.views || {})) if (!VIEW_INDEX.has(k)) VIEW_INDEX.set(k, lib.name);
    }
    for (const k of lib.names || []) add(k, lib.name);
    for (const l of lib.lemmas || []) add(l.name, lib.name);
    for (const st of lib.structures || []) add(st, lib.name);
  }
}

const LIBS = Symbol('libraries');

/* Load a library into env. Its exports become names in env, and the library itself becomes a
   namespace value, so topology.open works too. With alias, only the namespace is bound. */
function activate(name, env, alias = null) {
  if (alias) {
    const inner = Object.create(env);
    activate(name, inner);
    env[alias] = namespaceOf(name, inner);
    return;
  }
  const lib = REG.get(name);
  if (!lib) throw new MVError(`There's no library called "${name}". Available: ${[...REG.keys()].join(', ')}.`);
  if (!Object.prototype.hasOwnProperty.call(env, LIBS)) env[LIBS] = new Set(env[LIBS] || []);
  if (env[LIBS].has(name)) return;
  if (lib.error) throw new MVError(`The ${name} library has an error: ${lib.error}`);
  env[LIBS].add(name);
  ACTIVE.libs.add(name);
  if (lib.def) {
    const d = lib.def;
    Object.assign(env, d.constants || {});
    for (const [k, f] of Object.entries(d.functions)) env[k] = f;
    for (const [k, v] of Object.entries(d.domains)) {
      if (typeof v === 'function') v.domainCtor = true;
      env[k] = v;
    }
    for (const T of d.types || []) if (!ACTIVE.types.includes(T)) ACTIVE.types.push(T);
    for (const [k, v] of Object.entries(d.views || {})) ACTIVE.views[k] = { ...v, lib: name };
    // Required libraries come after this library's own exports, and before its notation section.
    for (const r of d.requires || []) activate(r, env);
    if (lib.section) runSection(lib.section, env, name);
  } else runSection(lib.section, env, name);
  if (env[name] === undefined) env[name] = namespaceOf(name, env);
}

function namespaceOf(name, env) {
  const lib = REG.get(name), members = {};
  const names = [...(lib.def ? [...Object.keys(lib.def.functions), ...Object.keys(lib.def.constants || {}), ...Object.keys(lib.def.domains)] : []), ...(lib.names || []), ...(lib.lemmas || []).map(l => l.name), ...(lib.structures || [])];
  for (const n of names) if (env[n] !== undefined) members[n] = env[n];
  return { __ns: true, name, members };
}

function runSection(sec, env, libName) {
  const own = new Set([...sec.names, ...sec.lemmas.map(l => l.name), ...(sec.structures || [])]);
  for (const { ast, stmt } of sec.body) {
    try {
      if (ast.type === 'check') {
        checkNames(ast.body, env, [], own);
        env[ast.name] = makeClaim(ast.name, ast.body, env, ast.kind, docOf(stmt).doc, libName);
      } else execDefinition(ast, env, stmt, own);
    } catch (err) { throw new MVError(`In library ${libName}, line ${locate(stmt, err.pos).line}: ${err.message}`); }
  }
}

/* A named theorem or lemma, as a value: "check name" checks it again and "explain name" shows it. */
function makeClaim(name, body, env, kind = 'theorem', doc = '', lib = null) {
  return { __claim: true, name, body, env, kind, doc, lib, label: `${kind} ${name}` };
}

/* Names used in a definition or claim must exist now, or be defined later in the notebook. */
function checkNames(node, env, bound = [], extra = null, inClaim = false) {
  for (const [name, pos] of freeNames(node, new Set(bound))) {
    if (env[name] !== undefined || PENDING.has(name) || (extra && extra.has(name))) continue;
    const err = unknownName(name, env, inClaim);
    err.pos = pos;
    throw err;
  }
}

// A key for remembering calls: numbers, booleans, points, and objects by identity.
const OBJ_IDS = new WeakMap();
let NEXT_ID = 1;
function memoKey(v) {
  if (typeof v === 'number') return 'n' + v;
  if (typeof v === 'boolean') return 'b' + v;
  if (Array.isArray(v) && v.every(x => typeof x === 'number')) return 'a' + v.join(',');
  if (v && (typeof v === 'object' || typeof v === 'function')) {
    if (!OBJ_IDS.has(v)) OBJ_IDS.set(v, NEXT_ID++);
    return 'o' + OBJ_IDS.get(v);
  }
  return null;
}

/* import / let / def: statements that only change the environment. */
function execDefinition(ast, env, stmt, extra) {
  if (ast.type === 'import') { if (ast.alias) activate(ast.names[0], env, ast.alias); else for (const n of ast.names) activate(n, env); return true; }
  if (ast.type === 'structure') { defineStructure(ast, env, stmt, extra); return true; }
  if (ast.type === 'concept') { defineConcept(ast, env, stmt, extra); return true; }
  if (ast.type === 'library') return true;
  const { doc, examples } = docOf(stmt);
  if (ast.type === 'let' || (ast.type === 'def' && !ast.params)) {
    const expr = ast.type === 'let' ? ast.expr : ast.body;
    checkNames(expr, env, [], extra);
    const v = compile(expr)(env);
    if (v && v.__domain && !v.label) v.label = ast.name;
    if (typeof v === 'function' && !v.domainCtor) { v.label = ast.name; if (doc) v.doc = doc; }
    env[ast.name] = v;
    return true;
  }
  if (ast.type === 'def') {
    const params = ast.params;
    checkNames(ast.body, env, [...params, ast.name], extra);
    (ast.types || []).forEach(t => t && checkNames(t, env, [], extra));
    const body = compile(ast.body);
    const types = (ast.types || []).map(t => t ? compileDomain(t) : null);
    const check = args => {
      for (let i = 0; i < params.length; i++) {
        if (!types[i]) continue;
        const D = types[i](env);
        // A set given by its constructor (CantorSet, Q) becomes the set itself.
        if (D === MV.SetType && typeof args[i] === 'function' && (args[i].domainCtor || args[i].__structure)) args[i] = toDomain(args[i]);
        if (!D.contains(args[i])) throw new MVError(`${ast.name} expects ${params[i]} ∈ ${D.describe()}, but got ${describeValue(args[i])}.`);
      }
    };
    // Calls are remembered: the language has no side effects, so a definition applied to the same
    // numbers, points or objects (sets, functions) always gives the same answer.
    const memo = new Map();
    const fromLibrary = !!extra;
    const fn = (...args) => {
      // A famous object may know the answer (Thomae's function is continuous exactly at the irrationals).
      check(args);
      if (fromLibrary) { const k = factFor(ast.name, args); if (k) return k.v; }
      const keys = args.map(memoKey);
      const key = keys.every(k => k !== null) ? keys.join('|') : null;
      // A remembered result keeps its "estimated" flag, so a cached estimate isn't later called exact.
      if (key !== null && memo.has(key)) { const hit = memo.get(key); if (hit.inexact) MV.INEXACT = true; return hit.v; }
      check(args);
      const e = Object.create(env);
      for (let i = 0; i < params.length; i++) e[params[i]] = args[i];
      const before = MV.INEXACT;
      MV.INEXACT = false;
      let v, inexact;
      try { v = body(e); } finally { inexact = MV.INEXACT; MV.INEXACT = before || inexact; }
      if (key !== null && memo.size < 20000) memo.set(key, { v, inexact });
      return v;
    };
    fn.label = ast.name; fn.arity = params.length; fn.__notebook = true;
    if (doc) fn.doc = doc;
    let exampleBinders = null;
    if (examples) {
      try {
        const p = new MV.Parser(MV.tokenize(examples));
        exampleBinders = p.binders();
        if (p.peek().t !== 'eof') throw new MVError('Unexpected text after the examples.');
      } catch (err) { throw new MVError(`The "examples:" line of ${ast.name} doesn't parse: ${err.message}`); }
    }
    DEFS.set(fn, { name: ast.name, params, types: ast.types || [], body: ast.body, env, check, doc, examples: exampleBinders, fromLibrary });
    env[ast.name] = fn;
    return true;
  }
  return false;
}

/* concept name(params) where form: formula …
   One notion with several equivalent definitions. Each form is a definition of its own,
   name_form, and name is the first form; all of them know the concept (CONCEPTS), so explain
   and interpret can set the forms side by side. */
const CONCEPTS = new Map();
const conceptNames = ast => [ast.name, ...ast.forms.map(f => `${ast.name}_${f.name}`)];
function defineConcept(ast, env, stmt, extra) {
  const all = new Set([...(extra || []), ...conceptNames(ast)]);
  const C = { name: ast.name, params: ast.params || [], types: ast.types || [], forms: [], doc: docOf(stmt).doc, env };
  const define = (name, body) => {
    const node = ast.params ? { type: 'def', name, params: ast.params, types: ast.types, body } : { type: 'def', name, params: null, body };
    execDefinition(node, env, stmt, extra ? all : undefined);
    return env[name];
  };
  for (const f of ast.forms) C.forms.push({ name: f.name, label: `${ast.name}_${f.name}`, body: f.body, fn: define(`${ast.name}_${f.name}`, f.body) });
  C.fn = define(ast.name, ast.forms[0].body);
  const d = DEFS.get(C.fn);
  C.examples = d ? d.examples : null;
  for (const v of [C.fn, ...C.forms.map(f => f.fn)]) {
    const e = DEFS.get(v);
    if (e) e.concept = C;
    if (v && (typeof v === 'object' || typeof v === 'function')) CONCEPTS.set(v, C);
  }
  CONCEPTS.set(ast.name, C);
}
// The concept a value or name belongs to, if any.
const conceptOf = v => (v !== null && v !== undefined && CONCEPTS.get(v)) || null;

/* structure Name(fields) extends Parent where axiom: formula …
   Defines Name as a constructor, Name(…) making a record, and as a type: a record belongs to
   Name when it has the fields and every axiom (including the parent's) holds for it. */
const STRUCTS = new Map();
function defineStructure(ast, env, stmt, extra) {
  const parent = ast.parent ? env[ast.parent] && env[ast.parent].__structure : null;
  if (ast.parent && !parent) throw new MVError(`There's no structure called ${ast.parent} to extend.`);
  if (parent) for (const p of parent.params) if (!ast.params.includes(p)) throw new MVError(`${ast.name} extends ${ast.parent}, so it needs the field ${p} too.`);
  for (const ax of ast.axioms) checkNames(ax.body, env, [...ast.params], extra);
  const own = ast.axioms.map(ax => ({ name: ax.name, body: ax.body, from: ast.name, f: compile(ax.body) }));
  const S = {
    name: ast.name, params: ast.params, types: ast.types || [], parent,
    axioms: [...(parent ? parent.axioms : []), ...own], env, doc: docOf(stmt).doc, examples: null,
  };
  const exSrc = docOf(stmt).examples;
  if (exSrc) {
    try { S.examples = new MV.Parser(MV.tokenize('[' + exSrc + ']')).expr(); }
    catch (err) { throw new MVError(`The "examples:" line of ${ast.name} doesn't parse: ${err.message}`); }
  }
  const holds = new WeakMap();
  S.envFor = r => { const e = Object.create(env); for (const p of S.params) e[p] = r.fields[p]; return e; };
  S.check = r => {
    if (!isRecord(r) || !S.params.every(p => p in r.fields)) return false;
    // An infinite example (the Sorgenfrey line) can't have its axioms sampled; it says what it is.
    if (Array.isArray(r.known) && r.known.includes(S.name)) return true;
    if (holds.has(r)) return holds.get(r);
    const e = S.envFor(r);
    const ok = S.axioms.every(ax => atDepth(DEPTH + 1, () => truth(ax.f(e), ax.body)));
    holds.set(r, ok);
    return ok;
  };
  S.space = MV.space({
    kind: 'structure', label: S.name, structure: S,
    contains: r => S.check(r),
    // Quantifying over a structure means: over its examples that satisfy the axioms.
    sample: () => {
      const xs = S.instances();
      if (!xs.length) throw new MVError(`${S.name} has no examples to try. Add a comment line "examples: ${S.name}(…), …" above it, or quantify over a list, as in forall g in {…}.`);
      MV.INEXACT = true;
      return xs;
    },
    random: () => { const xs = S.instances(); if (!xs.length) throw new MVError(`${S.name} has no examples to try.`); return xs[Math.floor(Math.random() * xs.length)]; },
    describe: () => S.name,
  });
  let examples = null;
  S.allExamples = () => examples || (examples = S.examples ? compile(S.examples)(env) : []);
  S.instances = () => S.allExamples().filter(r => S.check(r));
  const types = S.types.map(t => t ? compileDomain(t) : null);
  const ctor = (...args) => {
    if (args.length !== S.params.length) throw new MVError(`${S.name} takes ${S.params.length} fields (${S.params.join(', ')}) but got ${args.length}.`);
    const fields = {};
    S.params.forEach((p, i) => {
      if (types[i] && !types[i](env).contains(args[i])) throw new MVError(`The field ${p} of ${S.name} must be in ${types[i](env).describe()}, but got ${describeValue(args[i])}.`);
      fields[p] = args[i];
    });
    return makeRecord(fields, S, `${S.name}(${args.map(fmt).join(', ')})`);
  };
  ctor.label = S.name;
  ctor.arity = S.params.length;
  ctor.__structure = S;
  if (S.doc) ctor.doc = S.doc;
  STRUCTS.set(S.name, S);
  env[ast.name] = ctor;
}

function freshEnv(pending = []) {
  ACTIVE = { types: [], views: {}, libs: new Set() };
  PENDING = new Set(pending);
  MV.RNG = MV.rng32(7);
  MV.TOL = 1e-9;
  DEPTH = 0;
  const env = Object.create(null);
  CONCEPTS.clear();
  activate('core', env);
  return env;
}

/* ================= Public API for libraries ================= */

MV.SHARED = {};
MV.ANALYZERS = {};
MV.SELF_CHECKS = [];
MV.NO_FACTS = false;
const FORMULA_CODE = new WeakMap();   // compiled formulas of functions made by fromFormula
const MathViz = {
  // spaces
  interval: (lo, hi, o) => MV.interval(lo, hi, o),
  finite: (values, o) => MV.finite(values, o),
  product: factors => MV.product(factors),
  ball: (c, r, closed) => MV.ball(c, r, closed),
  seq: X => MV.seqSpace(X),
  set: (ambient, test, label) => { const A = toDomain(ambient); return MV.predSet({ ambient: A, test: v => A.contains(v) && test(v) === true, label }); },
  space: spec => spec.window && !spec.random && !spec.sample ? MV.boxSet(spec) : MV.space({ kind: 'custom', ...spec, label: spec.label || spec.name }),
  complement: S => MV.complement(S),
  // sequences
  sequence: (fn, label, meta) => MV.makeSeq(fn, label, meta || {}),
  record: (fields, label) => makeRecord(fields, null, label || null),
  lim: s => MV.limOf(s),
  convergent: s => MV.convergent(s),
  limitAt: (f, a) => MV.limitAt(f, a),
  // values
  isSet: v => isDom(v),
  isDomain: v => isDom(v),
  toDomain: v => toDomain(v),
  // The elements of a finite set or a product of finite sets, or null when it isn't finite.
  elements: v => { try { return elementsOf(toDomain(v)) || null; } catch (e) { return null; } },
  format: v => fmt(v),
  error: msg => new MVError(msg),
  exact: fn => MV.exact(fn),
  ops: {
    add: (a, b) => arith('+', a, b), sub: (a, b) => arith('-', a, b),
    mul: (a, b) => arith('*', a, b), div: (a, b) => arith('/', a, b),
    pow: (a, b) => arith('^', a, b), neg: a => arith('neg', a), abs: a => arith('abs', a),
    eq: (a, b) => compare('=', a, b), lt: (a, b) => compare('<', a, b), le: (a, b) => compare('<=', a, b),
    union: (a, b) => arith('union', a, b), inter: (a, b) => arith('inter', a, b), minus: (a, b) => arith('\\', a, b),
  },
  types: { Set: MV.SetType, Fun: MV.FunType },
  // Example catalogs ask for the stress level (0 normal, 1 wild) and mark that they were used.
  stress: () => MV.STRESS,
  markStressable: () => { MV.STRESSABLE = true; },
  // A library function that estimates (rather than computes exactly) says so, so results aren't labelled "proved".
  markInexact: () => { MV.INEXACT = true; },
  // Values one library makes for others (the zoo's famous functions for the catalogs, …).
  shared: MV.SHARED,
  // selfCheck(name, env => [{ name, ok, detail }]): a consistency check the test suite runs.
  selfCheck: (name, run) => { MV.SELF_CHECKS.push({ name, run }); },
  // analyzer(defName, (...args) => ({ v, why }) | null): decides a library definition from formulas.
  analyzer: (name, fn) => { (MV.ANALYZERS[name] = MV.ANALYZERS[name] || []).push(fn); },
  asym: () => MV.ASYM,
  // The formula of a function ({ params, body, env } for a notebook lambda or one-line definition),
  // and a function made from one: it evaluates the formula, and exact algebra sees through it.
  formula: f => (MV.ASYM && MV.ASYM.formulaOf(f)) || null,
  fromFormula: ({ params, body, env }, label) => {
    let run = FORMULA_CODE.get(body);
    if (!run) FORMULA_CODE.set(body, run = compile(body, {}));
    const fn = (...args) => {
      const e = Object.create(env);
      for (let i = 0; i < params.length; i++) e[params[i]] = args[i];
      return run(e);
    };
    fn.label = label || ppText({ type: 'lambda', params, body }); fn.arity = params.length; fn.__notebook = true;
    fn.__lambda = { params, body, env };
    DEFS.set(fn, { name: fn.label, params, types: [], body, env, fromLibrary: false });
    return fn;
  },
  // Run fn at a stress level (0 the usual examples, 1 the wild ones).
  withStress: (level, fn) => { const b = MV.STRESS; MV.STRESS = level; try { return fn(); } finally { MV.STRESS = b; } },
  facts: { lookup: (name, args) => factFor(name, args), disable: on => { MV.NO_FACTS = !!on; } },
  // Run fn with real intervals sampled by exact rationals and irrationals (or not).
  withExactSampling: (on, fn) => { const b = MV.EXACT_SAMPLING; MV.EXACT_SAMPLING = !!on; try { return fn(); } finally { MV.EXACT_SAMPLING = b; } },
  // Exact reals (src/exact.js): kinds of numbers, exact rationals and irrationals.
  numbers: {
    isRational: v => MV.EX.isRational(v), denominator: v => MV.EX.denominator(v), kindOf: v => MV.EX.kindOf(v),
    isExact: v => MV.EX.isExact(v), rational: (p, q) => MV.EX.Q(p, q), irrational: (approx, label, facts) => MV.EX.T(approx, label, facts),
    inCantor: v => MV.EX.inCantor(v), cantorPoint: (seed, lo, w) => MV.EX.cantorPoint(seed, lo, w),
    sample: (lo, hi, n, o = {}) => MV.EX.sampleExact(lo, hi, !!o.loOpen, !!o.hiOpen, n),
  },
  // A small picture for galleries: draw(fig, value, host), where fig(options) makes a figure.
  thumbnail: (test, draw) => { MV.THUMBS.push({ test, draw }); },
  // A way of looking at a value, shown by interpret: { name, label, doc, test(v), render(ctx, v) }.
  represent: r => {
    if (!r || !r.name || typeof r.test !== 'function' || typeof r.render !== 'function') throw new Error('MathViz.represent needs { name, test(v), render(ctx, v) }.');
    const i = MV.REPRESENT.findIndex(x => x.name === r.name);
    if (i >= 0) MV.REPRESENT.splice(i, 1, r); else MV.REPRESENT.push(r);
  },
};
MV.THUMBS = [];
MV.REPRESENT = [];

const BUILTIN = [];
global.MathVizLibrary = fn => BUILTIN.push({ kind: 'js', fn });
global.MathVizNotation = src => BUILTIN.push({ kind: 'notation', source: src });

Object.assign(MV, {
  factFor, needsExact, defineConcept, conceptOf, CONCEPTS, propositional, definedNames: ast => ast.type === 'concept' ? conceptNames(ast) : [ast.name], makeRecord, isRecord, getField, elementsOf, defineStructure, fmt, describeValue, arith, compare, equalValues, truth, callValue, toDomain, compile, compileDomain, bindTarget,
  analyzeClaim, analyzeSteps, analyzeClaimAsync, claimTuples, runSliced, prepareClaim, evalSample, bindValues, nelderMead, trace, makeClaim, docOf, execDefinition, checkNames, atDepth, freshEnv, activate, registerJS, registerNotation, rebuildIndex,
  REG, BUILTIN, MathViz, SAMPLES,
});
// Live views of module state (Object.assign would copy their current values instead).
Object.defineProperties(MV, {
  ACTIVE: { get: () => ACTIVE }, VIEW_INDEX: { get: () => VIEW_INDEX }, NAME_INDEX: { get: () => NAME_INDEX },
  EVAL_OK: { get: () => EVAL_OK }, DEFS: { get: () => DEFS },
});

})(typeof window !== 'undefined' ? window : globalThis);
