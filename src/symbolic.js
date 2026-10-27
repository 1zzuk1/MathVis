/* Theorem Sketchpad — exact algebra. Expressions become fractions of polynomials with rational
   coefficients (exact, in BigInt) in the variables, and anything else (sin x, √x, |x|, …) becomes
   an opaque symbol keyed by its simplified arguments. Your own definitions are expanded. Sums
   over k in lo..hi of polynomials in k get closed forms (Faulhaber); other sums are symbols, split
   as Σ_{lo}^{n+1} = Σ_{lo}^{n} + (last term), which is what an induction step needs.

   |a|, min(a, b) and max(a, b) are symbols that remember their arguments ("pieces"): products of
   absolute values merge (|x − 1|·|x + 1| = |x² − 1|), even powers lose their bars (|x|² = x²), and
   src/inequal.js splits them into cases (|a| = a where a ≥ 0, −a elsewhere) when that is needed.

   An equation is an identity when the two sides simplify to the same fraction. It is reported as
   proved only when that holds for every value of the variables: no denominator that could vanish,
   and every sum's range non-negative in length (hi ≥ lo − 1) for all values of its variables. */
'use strict';
(function (global) {
const MV = global.MV;

class NotAlgebra extends Error {}
const no = why => { throw new NotAlgebra(why); };

/* ---------- exact rationals ---------- */
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
const Q = (n, d = 1n) => {
  if (d === 0n) no('division by zero');
  if (d < 0n) { n = -n; d = -d; }
  const g = gcd(n, d) || 1n;
  return { n: n / g, d: d / g };
};
const ONE = Q(1n), ZERO = Q(0n);
const qadd = (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d);
const qmul = (a, b) => Q(a.n * b.n, a.d * b.d);
const qinv = a => Q(a.d, a.n);
const qzero = a => a.n === 0n;
function qFromNumber(x) {
  if (!Number.isFinite(x)) return null;
  if (Number.isInteger(x)) return Math.abs(x) < 2 ** 53 ? Q(BigInt(x)) : null;
  const s = String(x);
  if (/e/i.test(s)) return null;
  const [i, f] = s.split('.');
  return Q(BigInt(i + f), 10n ** BigInt(f.length));
}

/* ---------- polynomials: Map(monomial key → { vars: [[name, exp]] sorted, c }) ---------- */
const LIMIT = 4000;
const monoKey = vars => vars.map(([v, e]) => e === 1 ? v : v + '^' + e).join('*');
const pconst = q => qzero(q) ? new Map() : new Map([['', { vars: [], c: q }]]);
const pvar = name => new Map([[name, { vars: [[name, 1]], c: ONE }]]);
function acc(out, vars, c) {
  const k = monoKey(vars), s = out.get(k);
  if (s) { const c2 = qadd(s.c, c); if (qzero(c2)) out.delete(k); else out.set(k, { vars, c: c2 }); }
  else if (!qzero(c)) out.set(k, { vars, c });
  if (out.size > LIMIT) no('too large');
}
function padd(a, b) { const out = new Map(a); for (const t of b.values()) acc(out, t.vars, t.c); return out; }
const pscale = (a, q) => { const out = new Map(); if (!qzero(q)) for (const [k, t] of a) out.set(k, { vars: t.vars, c: qmul(t.c, q) }); return out; };
function mulVars(x, y) {
  const m = new Map(x);
  for (const [v, e] of y) m.set(v, (m.get(v) || 0) + e);
  return [...m].sort((p, q) => (p[0] < q[0] ? -1 : p[0] > q[0] ? 1 : 0));
}
function pmul(a, b) {
  const out = new Map();
  for (const t of a.values()) for (const u of b.values()) acc(out, mulVars(t.vars, u.vars), qmul(t.c, u.c));
  return out;
}
const pIsConst = a => a.size === 0 || (a.size === 1 && a.has(''));
const pConstVal = a => a.size === 0 ? ZERO : a.get('').c;
const pequal = (a, b) => a.size === b.size && [...a].every(([k, t]) => b.has(k) && qzero(qadd(t.c, { n: -b.get(k).c.n, d: b.get(k).c.d })));
const pvars = a => new Set([...a.values()].flatMap(t => t.vars.map(v => v[0])));

/* ---------- fractions of polynomials ---------- */
const R = (n, d = pconst(ONE)) => {
  // Keep constant denominators folded into the numerator.
  if (pIsConst(d)) { const c = pConstVal(d); if (qzero(c)) no('division by zero'); return { n: pscale(n, qinv(c)), d: pconst(ONE) }; }
  return { n, d };
};
const rconst = q => R(pconst(q));
const rvar = name => R(pvar(name));
const radd = (a, b) => pequal(a.d, b.d) ? R(padd(a.n, b.n), a.d) : R(padd(pmul(a.n, b.d), pmul(b.n, a.d)), pmul(a.d, b.d));
const rneg = a => R(pscale(a.n, Q(-1n)), a.d);
const rsub = (a, b) => radd(a, rneg(b));
const rmul = (a, b) => R(pmul(a.n, b.n), pmul(a.d, b.d));
const rdiv = (a, b) => { if (b.n.size === 0) no('division by zero'); return R(pmul(a.n, b.d), pmul(a.d, b.n)); };
function rpow(a, k) {
  if (k < 0) return rpow(rdiv(rconst(ONE), a), -k);
  let out = rconst(ONE), base = a;
  while (k) { if (k & 1) out = rmul(out, base); k >>= 1; if (k) base = rmul(base, base); }
  return out;
}
const rIsZero = a => a.n.size === 0;
const rIsConst = a => pIsConst(a.n) && pIsConst(a.d);
const rConstVal = a => qmul(pConstVal(a.n), qinv(pConstVal(a.d)));
const rvarsOf = a => new Set([...pvars(a.n), ...pvars(a.d)]);
// Replace the variable v by the fraction s.
function rsubst(a, v, s) {
  const sp = p => {
    let out = rconst(ZERO);
    for (const t of p.values()) {
      let term = rconst(t.c);
      for (const [x, e] of t.vars) term = rmul(term, x === v ? rpow(s, e) : rpow(rvar(x), e));
      out = radd(out, term);
    }
    return out;
  };
  return rdiv(sp(a.n), sp(a.d));
}

/* ---------- display ---------- */
const SUP = { '0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴', '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹' };
const sup = e => String(e).split('').map(c => SUP[c]).join('');
// Graded order, as written by hand: x² + 2xy + y², higher powers of earlier variables first.
function termOrder(a, b) {
  const deg = t => t.vars.reduce((s, v) => s + v[1], 0);
  if (deg(a) !== deg(b)) return deg(b) - deg(a);
  const names = [...new Set([...a.vars, ...b.vars].map(v => v[0]))].sort();
  for (const x of names) {
    const ea = (a.vars.find(v => v[0] === x) || [x, 0])[1], eb = (b.vars.find(v => v[0] === x) || [x, 0])[1];
    if (ea !== eb) return eb - ea;
  }
  return 0;
}
const lcm = (a, b) => a / gcd(a, b) * b;
function pstr(p, names) {
  if (p.size === 0) return '0';
  // A common denominator comes out front: (n² + n)/2 rather than 1/2·n² + 1/2·n.
  const D = [...p.values()].reduce((m, t) => lcm(m, t.c.d), 1n);
  if (D > 1n && p.size > 1) return `(${pstr(pscale(p, Q(D)), names)})/${D}`;
  const terms = [...p.values()].sort(termOrder);
  return terms.map((t, i) => {
    const neg = t.c.n < 0n, c = { n: neg ? -t.c.n : t.c.n, d: t.c.d };
    const vs = t.vars.map(([v, e]) => { const nm = names.get(v) || v; return (/[\s+\-−*/·^]/.test(nm.replace(/\([^()]*\)/g, '')) ? `(${nm})` : nm) + (e > 1 ? sup(e) : ''); }).join('');
    const coef = c.d === 1n ? (c.n === 1n && vs ? '' : String(c.n)) : `${c.n}/${c.d}${vs ? '·' : ''}`;
    return (i ? (neg ? ' − ' : ' + ') : neg ? '−' : '') + coef + vs;
  }).join('');
}
const rstr = (a, names) => pIsConst(a.d) ? pstr(a.n, names) : `(${pstr(a.n, names)}) / (${pstr(a.d, names)})`;

/* ---------- Faulhaber: F_p(n) = 1^p + 2^p + … + n^p as a polynomial in n ---------- */
const BERN = [];
function bernoulli(m) {
  // B_m with B_1 = +1/2, so that the formula below sums 1..n.
  for (let j = BERN.length; j <= m; j++) {
    if (j === 0) { BERN.push(ONE); continue; }
    let s = ZERO;
    for (let k = 0; k < j; k++) s = qadd(s, qmul(Q(binom(j + 1, k)), BERN[k]));
    BERN.push(qmul(Q(-1n), qmul(s, Q(1n, BigInt(j + 1)))));
  }
  return m === 1 ? Q(1n, 2n) : BERN[m];
}
const binom = (n, k) => { let r = 1n; for (let i = 0; i < k; i++) r = r * BigInt(n - i) / BigInt(i + 1); return r; };
// Σ_{k=1}^{n} k^p, with n a fraction (a polynomial expression).
function faulhaber(p, n) {
  let out = rconst(ZERO);
  for (let j = 0; j <= p; j++) out = radd(out, rmul(rconst(qmul(Q(binom(p + 1, j)), bernoulli(j))), rpow(n, p + 1 - j)));
  return rmul(out, rconst(Q(1n, BigInt(p + 1))));
}

/* ---------- from formulas ---------- */
// cx: { env, bound: Set, subst: Map(name → fraction), names: Map(var → display), conds: [], denoms: [], depth, sums }
function sym(n, cx) {
  switch (n.type) {
    case 'num': { const q = qFromNumber(n.v); return q ? rconst(q) : no('number'); }
    case 'id': return ident(n.name, cx);
    case 'bin': {
      if (n.op === '+') return radd(sym(n.a, cx), sym(n.b, cx));
      if (n.op === '-') return rsub(sym(n.a, cx), sym(n.b, cx));
      if (n.op === '*') return rmul(sym(n.a, cx), sym(n.b, cx));
      if (n.op === '/') {
        const d = sym(n.b, cx);
        if (!rIsConst(d)) cx.denoms.push(d);
        return rdiv(sym(n.a, cx), d);
      }
      if (n.op === '^') {
        const e = sym(n.b, cx);
        if (rIsConst(e)) {
          const q = rConstVal(e);
          if (q.d === 1n && q.n >= -64n && q.n <= 64n) {
            const b = sym(n.a, cx);
            if (q.n < 0n && !rIsConst(b)) cx.denoms.push(b);
            return rpow(b, Number(q.n));
          }
        }
        // a^(e + c) = a^e · a^c for a whole number c, so 2^(n + 2) and 2·2^(n + 1) agree.
        if (pIsConst(e.d)) {
          const c = e.n.get('') ? e.n.get('').c : ZERO;
          const b = sym(n.a, cx);
          if (rIsConst(b) && !qzero(rConstVal(b)) && c.d === 1n && c.n >= -64n && c.n <= 64n) {
            const rest = rsub(e, rconst(c)), bs = rstr(b, new Map()), es = rstr(rest, new Map());
            const key = `⟨^(${bs}, ${es})⟩`;
            cx.names.set(key, `${bs}^(${rstr(rest, cx.names)})`);
            if (cx.facts && rConstVal(b).n > 0n) cx.facts.set(key, { kind: 'positive' });
            return rmul(rvar(key), rpow(b, Number(c.n)));
          }
        }
        return atom(n, cx);
      }
      if (n.op === 'mod') return atom(n, cx);
      return no('not arithmetic');
    }
    case 'un':
      if (n.op === 'neg') return rneg(sym(n.a, cx));
      if (n.op === 'sqrt' || n.op === 'fact') return atom(n, cx);
      return no('not arithmetic');
    case 'abs': return absOf(sym(n.e, cx), cx);
    case 'call': return call(n, cx);
    case 'bigop': return n.op === 'sum' ? sum(n, cx) : atom(n, cx);
    case 'index': case 'field': case 'lim': case 'if': return atom(n, cx);
    case 'where': {
      const inner = { ...cx, subst: new Map(cx.subst) };
      for (const b of n.binds) inner.subst.set(b.name, sym(b.expr, inner));
      return sym(n.body, inner);
    }
    default: return no('not arithmetic');
  }
}

const CONSTS = { pi: 'π', 'π': 'π', e: 'e' };
function ident(name, cx) {
  if (cx.subst.has(name)) return cx.subst.get(name);
  if (cx.bound.has(name)) return rvar(name);
  const v = cx.env ? cx.env[name] : undefined;
  if (typeof v === 'number' && CONSTS[name] && !cx.bound.has(name)) { cx.names.set('#' + CONSTS[name], CONSTS[name]); return rvar('#' + CONSTS[name]); }
  if (typeof v === 'number' && Number.isInteger(v) && Math.abs(v) < 2 ** 53) return rconst(Q(BigInt(v)));
  // A free name: a symbol, so an identity in it holds for every value it could have.
  return rvar(name);
}

// An opaque symbol for a subexpression, keyed by its arguments in simplified form, so sin(x + y)
// and sin(y + x) are the same symbol.
function atom(n, cx) {
  const key = '⟨' + keyOf(n, cx) + '⟩';
  cx.names.set(key, MV.ppText(n));
  // What is known about some symbols, for inequalities: sin and cos lie in [−1, 1], exp is
  // positive, √u is ≥ 0 with (√u)² = u.
  if (cx.facts && !cx.facts.has(key)) {
    const fname = n.type === 'call' && n.f.type === 'id' && n.args.length === 1 ? n.f.name : null;
    if (fname === 'sin' || fname === 'cos') cx.facts.set(key, { kind: 'bounded' });
    else if (fname === 'exp') cx.facts.set(key, { kind: 'positive' });
    else if (n.type === 'un' && n.op === 'sqrt') { try { cx.facts.set(key, { kind: 'sqrt', arg: sym(n.a, cx) }); } catch (e) { if (!(e instanceof NotAlgebra)) throw e; } }
  }
  return rvar(key);
}
function keyOf(n, cx) {
  const k = x => { try { return rstr(sym(x, cx), new Map()); } catch (e) { if (!(e instanceof NotAlgebra)) throw e; return MV.ppText(x); } };
  switch (n.type) {
    case 'call': return (n.f.type === 'id' ? n.f.name : MV.ppText(n.f)) + '(' + n.args.map(k).join(', ') + ')';
    case 'abs': return '|' + k(n.e) + '|';
    case 'un': return n.op + '(' + k(n.a) + ')';
    case 'bin': return n.op + '(' + k(n.a) + ', ' + k(n.b) + ')';
    default: return MV.ppText(n);
  }
}

function call(n, cx) {
  if (n.f.type === 'lambda' && n.f.params.length === n.args.length) {
    const inner = { ...cx, subst: new Map(cx.subst) };
    n.f.params.forEach((p, i) => inner.subst.set(p, sym(n.args[i], cx)));
    return sym(n.f.body, inner);
  }
  // A function made by an expression that doesn't involve the claim's variables (partial(f, 1),
  // a lambda returned by a definition): evaluated once, then its formula is expanded.
  if (n.f.type === 'call' && cx.env && cx.depth < 12 && ![...MV.freeNames(n.f).keys()].some(k => cx.bound.has(k) || cx.subst.has(k))) {
    let fv = null;
    try { fv = MV.compile(n.f)(cx.env); } catch (e) { fv = null; }
    const F = typeof fv === 'function' && (MV.DEFS.get(fv) || fv.__lambda);
    if (F && F.params.length === n.args.length && !(MV.DEFS.get(fv) || {}).fromLibrary) {
      try {
        const inner = { ...cx, env: F.env, bound: new Set(), subst: new Map(), depth: cx.depth + 1 };
        F.params.forEach((p, i) => inner.subst.set(p, sym(n.args[i], cx)));
        return sym(F.body, inner);
      } catch (e) { if (!(e instanceof NotAlgebra)) throw e; }
    }
  }
  if (n.f.type === 'id' && !cx.subst.has(n.f.name) && !cx.bound.has(n.f.name) && cx.env) {
    const fv = cx.env[n.f.name];
    const d = fv && MV.DEFS.get(fv);
    if (d && d.params.length === n.args.length && cx.depth < 12) {
      // Expand a definition: its parameters become the (simplified) arguments.
      try {
        const inner = { ...cx, env: d.env, bound: new Set(), subst: new Map(), depth: cx.depth + 1 };
        d.params.forEach((p, i) => inner.subst.set(p, sym(n.args[i], cx)));
        return sym(d.body, inner);
      } catch (e) { if (!(e instanceof NotAlgebra)) throw e; }
    }
    if (n.f.name === 'sqrt' && n.args.length === 1) return atom({ type: 'un', op: 'sqrt', a: n.args[0] }, cx);
    if ((n.f.name === 'min' || n.f.name === 'max') && n.args.length >= 2 && !MV.DEFS.get(cx.env[n.f.name])) {
      return n.args.map(a => sym(a, cx)).reduce((a, b) => minMax(n.f.name, a, b, cx));
    }
    if (n.f.name === 'abs' && n.args.length === 1 && !MV.DEFS.get(cx.env.abs)) return absOf(sym(n.args[0], cx), cx);
  }
  return atom(n, cx);
}

/* ---------- pieces: |a|, min, max ---------- */
const qabs = q => (q.n < 0n ? { n: -q.n, d: q.d } : q);
// p = c·m with m's leading coefficient 1 (in the order the terms are written).
function monic(p) {
  if (pIsConst(p)) return [pConstVal(p), pconst(ONE)];
  const lead = [...p.values()].sort(termOrder)[0].c;
  return [lead, pscale(p, qinv(lead))];
}
// |c·p/q| = |c|·|p|/|q| with p and q made monic, so |2 − 2x| and 2|x − 1| are the same.
function absOf(r, cx) {
  if (rIsConst(r)) return rconst(qabs(rConstVal(r)));
  const [cn, pn] = monic(r.n), [cd, pd] = monic(r.d);
  let out = rmul(rconst(qabs(qmul(cn, qinv(cd)))), absAtom(pn, cx));
  if (!pIsConst(pd)) out = rdiv(out, absAtom(pd, cx));
  return out;
}
function absAtom(p, cx) {
  // Only even powers with positive coefficients (x² + 1, x²y⁴): never negative, no bars needed.
  if ([...p.values()].every(t => t.c.n > 0n && t.vars.every(([, e]) => e % 2 === 0))) return R(p);
  const key = `⟨|${pstr(p, new Map())}|⟩`;
  cx.names.set(key, `|${pstr(p, cx.names)}|`);
  cx.pieces.set(key, { kind: 'abs', arg: R(p) });
  return rvar(key);
}
function minMax(kind, a, b, cx) {
  if (rIsConst(a) && rIsConst(b)) {
    const d = rConstVal(rsub(a, b));
    return (kind === 'min') === (d.n <= 0n) ? a : b;
  }
  const sa = rstr(a, new Map()), sb = rstr(b, new Map());
  if (sa === sb) return a;
  const [x, y] = sa < sb ? [a, b] : [b, a];
  const key = `⟨${kind}(${sa < sb ? sa : sb}, ${sa < sb ? sb : sa})⟩`;
  cx.names.set(key, `${kind}(${rstr(x, cx.names)}, ${rstr(y, cx.names)})`);
  cx.pieces.set(key, { kind, args: [x, y] });
  return rvar(key);
}
// In each term, even powers of |a| become powers of a, and the absolute values left are merged
// into one: |a|·|b| = |ab|.
function mergeAbs(r, cx) {
  const pieces = cx.pieces;
  if (![...rvarsOf(r)].some(v => pieces.has(v) && pieces.get(v).kind === 'abs')) return r;
  const merge = p => {
    let out = rconst(ZERO);
    for (const t of p.values()) {
      let term = rconst(t.c);
      const odd = [];
      for (const [v, e] of t.vars) {
        const pc = pieces.get(v);
        if (pc && pc.kind === 'abs') {
          if (e >= 2) term = rmul(term, rpow(pc.arg, 2 * Math.floor(e / 2)));
          if (e % 2) odd.push(v);
        } else term = rmul(term, rpow(rvar(v), e));
      }
      if (odd.length === 1) term = rmul(term, rvar(odd[0]));
      else if (odd.length > 1) term = rmul(term, absOf(odd.map(v => pieces.get(v).arg).reduce(rmul), cx));
      out = radd(out, term);
    }
    return out;
  };
  return rdiv(merge(r.n), merge(r.d));
}

// Σ_{k=lo}^{hi} body. Each sum's index gets its own name.
let SUM_ID = 0;
function sum(n, cx) {
  if (n.binders.length !== 1 || n.binders[0].pattern || n.binders[0].dom.type !== 'range') return atom(n, cx);
  const b = n.binders[0], kv = '§' + (++SUM_ID);
  const lo = sym(b.dom.lo, cx), hi = sym(b.dom.hi, cx);
  if (rIsConst(lo) && rConstVal(lo).d === 1n) cx.mins.set(kv, rConstVal(lo).n);
  if (!pIsConst(lo.d) || !pIsConst(hi.d)) return atom(n, cx);
  const withK = v => { const inner = { ...cx, subst: new Map(cx.subst) }; inner.subst.set(b.name, v); return sym(n.body, inner); };
  // Small constant ranges: add the terms up.
  if (rIsConst(lo) && rIsConst(hi)) {
    const a = rConstVal(lo), z = rConstVal(hi);
    if (a.d === 1n && z.d === 1n && z.n - a.n <= 200n) {
      let s = rconst(ZERO);
      for (let k = a.n; k <= z.n; k++) s = radd(s, withK(rconst(Q(k))));
      return s;
    }
  }
  cx.conds.push(radd(rsub(hi, lo), rconst(ONE)));   // the range has hi − lo + 1 ≥ 0 terms
  // A polynomial in k: Faulhaber's formula for each power of k.
  const body = withK(rvar(kv));
  const kIn = v => v === kv || v.includes(kv);
  if (pIsConst(body.d) && ![...pvars(body.n)].some(v => v !== kv && kIn(v))) {
    let s = rconst(ZERO);
    const lo1 = rsub(lo, rconst(ONE));
    for (const t of body.n.values()) {
      const e = (t.vars.find(v => v[0] === kv) || [kv, 0])[1];
      const rest = t.vars.filter(v => v[0] !== kv);
      const coef = R(new Map([[monoKey(rest), { vars: rest, c: t.c }]]));
      const F = e === 0 ? rsub(hi, lo1) : rsub(faulhaber(e, hi), faulhaber(e, lo1));
      s = radd(s, rmul(coef, F));
    }
    return s;
  }
  // Otherwise a symbol, with the last terms split off when the upper end is (something) + c.
  const c0 = hi.n.get('') ? hi.n.get('').c : ZERO;
  if (c0.d === 1n && c0.n > 0n && c0.n <= 4n && !pIsConst(hi.n)) {
    const base = rsub(hi, rconst(c0));
    let s = sumAtom(n, b, lo, base, cx);
    for (let j = 1n; j <= c0.n; j++) s = radd(s, withK(radd(base, rconst(Q(j)))));
    return s;
  }
  return sumAtom(n, b, lo, hi, cx);
}
function sumAtom(n, b, lo, hi, cx) {
  // The key's own simplification records nothing about conditions: its index is a placeholder.
  const inner = { ...cx, subst: new Map(cx.subst), denoms: [], conds: [] };
  inner.subst.set(b.name, rvar('§'));
  let bodyKey;
  try { bodyKey = rstr(sym(n.body, inner), new Map()); } catch (e) { if (!(e instanceof NotAlgebra)) throw e; bodyKey = MV.ppText(n.body); }
  const key = `⟨Σ ${bodyKey} | ${rstr(lo, new Map())} .. ${rstr(hi, new Map())}⟩`;
  cx.names.set(key, `Σ_{${b.name}=${rstr(lo, cx.names)}}^{${rstr(hi, cx.names)}} ${MV.ppText(n.body)}`);
  return rvar(key);
}

/* ---------- conditions: is this always ≥ 0? ---------- */
// The smallest value of a whole-number variable, from its range: ℕ, a..b, or n ≥ c.
function minOf(name, doms) {
  const d = doms.get(name);
  if (!d) return null;
  if (d.type === 'id' && d.name === 'N') return 0n;
  if (d.type === 'range' && d.lo.type === 'num' && Number.isInteger(d.lo.v)) return BigInt(d.lo.v);
  return null;
}
// p is a constant ≥ 0, or a·v + c with a > 0 and v a whole-number variable with a·min(v) + c ≥ 0.
function alwaysNonneg(r, doms) {
  if (!pIsConst(r.d)) return false;
  const p = r.n;
  if (pIsConst(p)) return pConstVal(p).n >= 0n;
  const terms = [...p.values()].filter(t => t.vars.length);
  if (terms.length !== 1 || terms[0].vars.length !== 1 || terms[0].vars[0][1] !== 1) return false;
  const a = terms[0].c, v = terms[0].vars[0][0], m = minOf(v, doms);
  if (m === null || a.n <= 0n) return false;
  const c = p.get('') ? p.get('').c : ZERO;
  return qadd(qmul(a, Q(m)), c).n >= 0n;
}

/* ---------- identities ---------- */
const isEquation = n => n && n.type === 'cmp' && n.ops.every(o => o === '=');
function context(env, binders, subst) {
  const doms = new Map(), bound = new Set();
  for (const b of binders) { if (b.pattern) b.pattern.forEach(x => bound.add(x)); else { bound.add(b.name); doms.set(b.name, b.dom); } }
  const mins = new Map();
  for (const name of doms.keys()) { const m = minOf(name, doms); if (m !== null) mins.set(name, m); }
  return { env, bound, subst: subst || new Map(), names: new Map(), conds: [], denoms: [], depth: 0, doms, mins, pieces: new Map(), facts: new Map(), constraints: null };
}
// rewrites: [{ v, s }] replacing the variable (or symbol) v by s; relations: fractions known to be 0.
// sin² + cos² = 1: every cos(X)² next to a sin(X) of the same argument becomes 1 − sin(X)².
function reduceTrig(p) {
  const vs = [...pvars(p)];
  for (const c of vs) {
    const m = /^⟨cos\((.*)\)⟩$/.exec(c);
    if (!m || !vs.includes(`⟨sin(${m[1]})⟩`)) continue;
    const s = `⟨sin(${m[1]})⟩`;
    for (let changed = true; changed;) {
      changed = false;
      const out = new Map();
      for (const t of p.values()) {
        const e = (t.vars.find(v => v[0] === c) || [c, 0])[1];
        if (e < 2) { acc(out, t.vars, t.c); continue; }
        changed = true;
        const rest = t.vars.map(([v, x]) => [v, v === c ? x - 2 : x]).filter(v => v[1] > 0);
        acc(out, rest, t.c);
        acc(out, mulVars(rest, [[s, 2]]), qmul(t.c, Q(-1n)));
      }
      p = out;
    }
  }
  return p;
}
const trig = r => R(reduceTrig(r.n), reduceTrig(r.d));

function equalities(node, cx, rewrites = [], relations = []) {
  const diffs = [];
  for (let i = 0; i + 1 < node.args.length; i++) {
    let d = rsub(sym(node.args[i], cx), sym(node.args[i + 1], cx));
    for (const { v, s } of rewrites) if (rvarsOf(d).has(v)) d = rsubst(d, v, s);
    diffs.push(mergeAbs(trig(d), cx));
  }
  const via = [];
  const ok = diffs.every(d => {
    if (rIsZero(d)) return true;
    // With |a|, min or max left: zero in every case they split into (src/inequal.js).
    if ([...rvarsOf(d)].some(v => cx.pieces.has(v)) && MV.casesZero && MV.casesZero(d, cx)) { via.push('cases'); return true; }
    // A constant multiple of a known relation (an assumption lhs − rhs = 0).
    for (const r of relations) {
      if (r.n.size && pIsConst(d.d) && pIsConst(r.d)) {
        const [k, t] = [...r.n][0], u = d.n.get(k);
        if (u) { const q = qmul(u.c, qinv(t.c)); if (rIsZero(rsub(R(d.n), R(pscale(r.n, q))))) { via.push(r.label); return true; } }
      }
    }
    return false;
  });
  return { ok, diffs, via };
}
// A denominator that can't vanish: every coefficient positive, each variable raised to an even
// power or a whole number ≥ 0, and some term surely positive (1 + x², (n + 1)(n + 2) for n ∈ ℕ,
// k(k + 1) for k ≥ 1).
function alwaysPositive(r, mins) {
  // Every term ≥ 0, and one of them > 0: a positive constant, or a product of variables ≥ 1.
  const pos = p => [...p.values()].every(t => t.c.n > 0n && t.vars.every(([v, e]) => e % 2 === 0 || (mins.has(v) && mins.get(v) >= 0n)))
    && [...p.values()].some(t => t.vars.every(([v]) => mins.has(v) && mins.get(v) >= 1n));
  const neg = p => pos(pscale(p, Q(-1n)));
  return (pos(r.n) || neg(r.n)) && (pos(r.d) || neg(r.d));
}
function verdict(res, cx, doms) {
  const conds = cx.conds.every(c => alwaysNonneg(c, doms));
  const risky = cx.denoms.filter(d => !alwaysPositive(d, cx.mins));
  return { identity: res.ok, proved: res.ok && !risky.length && conds, denoms: risky.map(d => rstr(d, cx.names)), condsOk: conds, via: res.via, sides: [] };
}
// Show both sides simplified (the first pair), for the explanation.
function shownSides(node, cx) {
  try { return [rstr(sym(node.args[0], cx), cx.names), rstr(sym(node.args[node.args.length - 1], cx), cx.names)]; } catch (e) { return null; }
}

// A claim ∀ (binders): L = R (the prepared claim P of the analyzer).
function symbolicClaim(P) {
  const concl = P.concl;
  if (!isEquation(concl)) return null;
  try {
    const cx = context(P.scope, P.U || []);
    const res = equalities(concl, cx);
    if (!res.ok) return { identity: false };
    const v = verdict(res, cx, cx.doms);
    v.sides = shownSides(concl, context(P.scope, P.U || []));
    return v;
  } catch (e) { if (e instanceof NotAlgebra || e instanceof RangeError) return null; throw e; }
}

// A proof step F in a context (ctx from the proof checker: variables, assumptions, chosen values).
function symbolicStep(ctx, F, env) {
  if (!isEquation(F)) return null;
  try {
    const binders = ctx.filter(e => e.kind === 'var').map(e => e.binder);
    const cx = context(env, binders);
    // Chosen values are substituted, in order.
    for (const e of ctx) if (e.kind === 'def') cx.subst.set(e.name, sym(e.expr, cx));
    // Assumptions lhs = rhs: rewrite a lone variable or symbol, or keep the relation.
    const rewrites = [], relations = [];
    for (const e of ctx) {
      if (e.kind !== 'hyp' || !isEquation(e.expr) || e.expr.args.length !== 2) continue;
      let a, b;
      try { a = sym(e.expr.args[0], cx); b = sym(e.expr.args[1], cx); } catch (err) { if (err instanceof NotAlgebra) continue; throw err; }
      const lone = r => pIsConst(r.d) && r.n.size === 1 && [...r.n.values()][0].vars.length === 1 && [...r.n.values()][0].vars[0][1] === 1 && qzero(qadd([...r.n.values()][0].c, Q(-1n))) ? [...r.n.values()][0].vars[0][0] : null;
      const la = lone(a), lb = lone(b);
      if (la && !rvarsOf(b).has(la)) rewrites.push({ v: la, s: b });
      else if (lb && !rvarsOf(a).has(lb)) rewrites.push({ v: lb, s: a });
      const rel = rsub(a, b);
      rel.label = MV.ppText(e.expr);
      relations.push(rel);
    }
    const res = equalities(F, cx, rewrites, relations);
    if (!res.ok) return { identity: false };
    const v = verdict(res, cx, cx.doms);
    v.usedAssumptions = rewrites.length > 0 || res.via.length > 0;
    return v;
  } catch (e) { if (e instanceof NotAlgebra || e instanceof RangeError) return null; throw e; }
}

// For the tests and the console: the simplified form of an expression.
function simplify(node, env, bound = []) {
  try { const cx = context(env, bound.map(name => ({ name, dom: { type: 'id', name: 'R' } }))); return rstr(sym(node, cx), cx.names); }
  catch (e) { if (e instanceof NotAlgebra) return null; throw e; }
}

// The pieces src/inequal.js builds on.
MV.SYMK = {
  NotAlgebra, Q, ONE, ZERO, qadd, qmul, qinv, qzero, qabs, qFromNumber,
  pconst, pvar, padd, pscale, pmul, pIsConst, pConstVal, pequal, pvars, monoKey, mulVars, acc, termOrder,
  R, rconst, rvar, radd, rneg, rsub, rmul, rdiv, rpow, rIsZero, rIsConst, rConstVal, rvarsOf, rsubst,
  pstr, rstr, sym, context, minOf, alwaysPositive, mergeAbs, trig, isEquation,
};

Object.assign(MV, { symbolicClaim, symbolicStep, simplify });
})(typeof window !== 'undefined' ? window : globalThis);
