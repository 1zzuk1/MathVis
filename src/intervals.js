/* Theorem Sketchpad — interval arithmetic: proofs of inequalities on boxes.

   Every quantity is replaced by an interval guaranteed to contain all its values on a box of
   inputs. If "left − right ≥ 0" holds for the whole interval, the inequality is proved on that
   box; if it fails for the whole interval, every point of the box is a counterexample; otherwise
   the box is split in two. The result is a proof map: proved, failing and undecided boxes.
   Results are rounded outward by a few ulps, which covers ordinary floating-point error. */
'use strict';
(function (global) {
const MV = global.MV;

const EPS = 4 * Number.EPSILON;
const dn = x => x === 0 ? -Number.MIN_VALUE * 4 : x - Math.abs(x) * EPS - Number.MIN_VALUE;
const up = x => x === 0 ? Number.MIN_VALUE * 4 : x + Math.abs(x) * EPS + Number.MIN_VALUE;
const I = (lo, hi = lo) => ({ lo, hi });
const out = (lo, hi) => (Number.isNaN(lo) || Number.isNaN(hi)) ? null : { lo: dn(lo), hi: up(hi) };
const ALL = { lo: -Infinity, hi: Infinity };

const ops = {
  add: (a, b) => out(a.lo + b.lo, a.hi + b.hi),
  sub: (a, b) => out(a.lo - b.hi, a.hi - b.lo),
  mul: (a, b) => { const p = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi].map(v => Number.isNaN(v) ? 0 : v); return out(Math.min(...p), Math.max(...p)); },
  div: (a, b) => (b.lo <= 0 && b.hi >= 0) ? ALL : ops.mul(a, out(1 / b.hi, 1 / b.lo)),
  neg: a => I(-a.hi, -a.lo),
  abs: a => a.lo >= 0 ? a : a.hi <= 0 ? I(-a.hi, -a.lo) : I(0, Math.max(-a.lo, a.hi)),
  powInt(a, n) {
    if (n === 0) return I(1);
    if (n < 0) return ops.div(I(1), ops.powInt(a, -n));
    if (n % 2 === 1) return out(Math.pow(a.lo, n), Math.pow(a.hi, n));
    const b = ops.abs(a);
    return out(Math.pow(b.lo, n), Math.pow(b.hi, n));
  },
  sqrt: a => a.hi < 0 ? null : out(Math.sqrt(Math.max(0, a.lo)), Math.sqrt(a.hi)),
  cbrt: a => out(Math.cbrt(a.lo), Math.cbrt(a.hi)),
  exp: a => out(Math.exp(a.lo), Math.exp(a.hi)),
  ln: a => a.hi <= 0 ? null : out(a.lo <= 0 ? -Infinity : Math.log(a.lo), Math.log(a.hi)),
  atan: a => out(Math.atan(a.lo), Math.atan(a.hi)),
  // sin and cos: the end values, plus ±1 wherever a peak lies inside.
  sin: a => trig(Math.sin, a, Math.PI / 2),
  cos: a => trig(Math.cos, a, 0),
  min: (a, b) => I(Math.min(a.lo, b.lo), Math.min(a.hi, b.hi)),
  max: (a, b) => I(Math.max(a.lo, b.lo), Math.max(a.hi, b.hi)),
};
function trig(f, a, peak) {
  if (a.hi - a.lo >= 2 * Math.PI) return I(-1, 1);
  let lo = Math.min(f(a.lo), f(a.hi)), hi = Math.max(f(a.lo), f(a.hi));
  // peaks of f at peak + 2kπ (value 1) and troughs at peak + π + 2kπ (value −1)
  const has = base => { const k = Math.ceil((a.lo - base) / (2 * Math.PI)); return base + 2 * k * Math.PI <= a.hi; };
  if (has(peak)) hi = 1;
  if (has(peak + Math.PI)) lo = -1;
  return out(Math.max(-1, lo), Math.min(1, hi));
}

const CORE_FNS = { sin: 'sin', cos: 'cos', exp: 'exp', ln: 'ln', sqrt: 'sqrt', cbrt: 'cbrt', abs: 'abs', atan: 'atan', min: 'min', max: 'max' };

/* Compile an expression to a function from a box (one interval per coordinate) to an interval,
   or return null when it uses something interval arithmetic doesn't cover here. coords maps a
   variable name to a coordinate index, or to a list of indices for a point. */
function compileI(node, coords, env, depth = 0) {
  if (depth > 6) return null;
  const core = MV.REG.get('core');
  const coreFns = core && core.def ? core.def.functions : {};
  const c = n => compileI(n, coords, env, depth);
  switch (node.type) {
    case 'num': { const v = node.v; return () => I(v); }
    case 'id': {
      if (node.name in coords) { const k = coords[node.name]; return Array.isArray(k) ? null : box => box[k]; }
      const v = env[node.name];
      return typeof v === 'number' && Number.isFinite(v) ? () => I(v) : null;
    }
    case 'bin': {
      if (node.op === '^') {
        const a = c(node.a);
        if (!a) return null;
        if (node.b.type === 'num' && Number.isInteger(node.b.v)) { const n = node.b.v; return box => { const x = a(box); return x && ops.powInt(x, n); }; }
        if (node.b.type === 'num' && node.b.v === 0.5) return box => { const x = a(box); return x && ops.sqrt(x); };
        return null;
      }
      const a = c(node.a), b = c(node.b), f = { '+': ops.add, '-': ops.sub, '*': ops.mul, '/': ops.div }[node.op];
      if (!a || !b || !f) return null;
      return box => { const x = a(box), y = b(box); return x && y && f(x, y); };
    }
    case 'un': {
      if (node.op !== 'neg' && node.op !== 'sqrt') return null;
      const a = c(node.a);
      if (!a) return null;
      const f = node.op === 'neg' ? ops.neg : ops.sqrt;
      return box => { const x = a(box); return x && f(x); };
    }
    case 'abs': {
      // |x| of a point variable is its length.
      if (node.e.type === 'id' && Array.isArray(coords[node.e.name])) {
        const ks = coords[node.e.name];
        return box => ops.sqrt(ks.map(k => ops.powInt(box[k], 2)).reduce(ops.add));
      }
      const a = c(node.e);
      return a && (box => { const x = a(box); return x && ops.abs(x); });
    }
    case 'index': {
      if (node.obj.type === 'id' && Array.isArray(coords[node.obj.name]) && node.args.length === 1 && node.args[0].type === 'num') {
        const k = coords[node.obj.name][node.args[0].v - 1];
        return k === undefined ? null : box => box[k];
      }
      return null;
    }
    case 'call': {
      if (node.f.type !== 'id') return null;
      const name = node.f.name, fv = env[name];
      const d = fv && MV.DEFS.get(fv);
      if (d && d.params.length === node.args.length) return c(MV.subst(d.body, new Map(d.params.map((p, i) => [p, node.args[i]]))));
      if (CORE_FNS[name] && fv === coreFns[name]) {
        const args = node.args.map(c);
        if (args.some(x => !x)) return null;
        const f = ops[CORE_FNS[name]];
        if (args.length === 1) return box => { const x = args[0](box); return x && f(x); };
        if (args.length === 2 && (name === 'min' || name === 'max')) return box => { const x = args[0](box), y = args[1](box); return x && y && f(x, y); };
      }
      return null;
    }
    default: return null;
  }
}

/* Three-valued comparisons: true, false, or null (can't tell on this box). */
function cmpI(op, a, b) {
  if (!a || !b) return null;
  switch (op) {
    case '<': return a.hi < b.lo ? true : a.lo >= b.hi ? false : null;
    case '<=': return a.hi <= b.lo ? true : a.lo > b.hi ? false : null;
    case '>': return a.lo > b.hi ? true : a.hi <= b.lo ? false : null;
    case '>=': return a.lo >= b.hi ? true : a.hi < b.lo ? false : null;
    default: return null;
  }
}
function compileCond(node, coords, env) {
  if (node.type === 'cmp') {
    const fs = node.args.map(a => compileI(a, coords, env));
    if (fs.some(f => !f)) return null;
    return box => {
      const vs = fs.map(f => f(box));
      let all = true;
      for (let i = 0; i < node.ops.length; i++) {
        const r = cmpI(node.ops[i], vs[i], vs[i + 1]);
        if (r === false) return false;
        if (r === null) all = null;
      }
      return all;
    };
  }
  if (node.type === 'bin' && (node.op === 'and' || node.op === 'or')) {
    const a = compileCond(node.a, coords, env), b = compileCond(node.b, coords, env);
    if (!a || !b) return null;
    return node.op === 'and'
      ? box => { const x = a(box), y = b(box); return x === false || y === false ? false : x && y ? true : null; }
      : box => { const x = a(box), y = b(box); return x === true || y === true ? true : x === false && y === false ? false : null; };
  }
  return null;
}

/* Try to prove a claim by interval arithmetic. Applies to claims whose variables range over
   bounded real intervals or boxes, whose conclusion is an inequality, and whose hypothesis (if
   any) is made of inequalities. Yields progress; returns a proof map, or null if it can't apply. */
function* proveByIntervals(body, env, opts = {}) {
  const P = MV.prepareClaim(body, env);
  if (P.kind !== 'cmp' || !['<', '<=', '>', '>='].includes(P.op) || !P.U.length) return null;
  const coords = {}, box0 = [], names = [];
  for (const b of P.U) {
    let D;
    try { D = MV.compileDomain(b.dom)(P.scope); } catch (e) { return null; }   // ranges that depend on other variables
    const add = (name, f) => {
      if (f.kind !== 'interval' || f.integer || f.unbounded) return false;
      coords[name] = box0.length; box0.push(I(f.lo, f.hi)); names.push(name);
      return true;
    };
    if (b.pattern) {
      if (D.kind !== 'product' || D.factors.length !== b.pattern.length) return null;
      if (!b.pattern.every((n, i) => add(n, D.factors[i]))) return null;
    } else if (D.kind === 'interval') { if (!add(b.name, D)) return null; }
    else if (D.kind === 'product' && D.factors.every(f => f.kind === 'interval')) {
      const ks = [];
      for (let i = 0; i < D.factors.length; i++) {
        const f = D.factors[i];
        if (f.integer || f.unbounded) return null;
        ks.push(box0.length); box0.push(I(f.lo, f.hi)); names.push(`${b.name}${'₀₁₂₃₄₅₆₇₈₉'[i + 1]}`);
      }
      coords[b.name] = ks;
    } else return null;
  }
  if (box0.length > 4) return null;
  const [A, B] = P.concl.args;
  const L = compileI(A, coords, P.scope), R = compileI(B, coords, P.scope);
  if (!L || !R) return null;
  const hyp = P.hyp ? compileCond(P.hyp, coords, P.scope) : null;
  if (P.hyp && !hyp) return null;
  const maxBoxes = opts.maxBoxes || 4000, minWidth = opts.minWidth || 1e-9;
  const boxes = [], queue = [box0];
  let evaluated = 0;
  const t0 = Date.now();
  while (queue.length) {
    const bx = queue.shift();   // breadth first: every region gets refined evenly
    evaluated++;
    const h = hyp ? hyp(bx) : true;
    let s;
    if (h === false) s = 'vac';
    else {
      const verdict = cmpI(P.op, L(bx), R(bx));
      if (verdict === true && h !== false) s = h === true ? 'ok' : 'ok';
      else if (verdict === false && h === true) s = 'fail';
      else s = null;
      // A box whose conclusion holds is proved whatever the hypothesis does there.
      if (verdict === true) s = 'ok';
    }
    const widest = bx.reduce((best, iv, i) => (iv.hi - iv.lo > bx[best].hi - bx[best].lo ? i : best), 0);
    const w = bx[widest].hi - bx[widest].lo;
    if (s === null && (boxes.length + queue.length >= maxBoxes || w <= minWidth * Math.max(1, Math.abs(bx[widest].lo)) || Date.now() - t0 > (opts.ms || 1500))) s = 'open';
    if (s !== null) { boxes.push({ box: bx, s }); }
    else {
      const m = (bx[widest].lo + bx[widest].hi) / 2;
      const a = bx.slice(), b2 = bx.slice();
      a[widest] = I(bx[widest].lo, m); b2[widest] = I(m, bx[widest].hi);
      queue.push(a, b2);
    }
    if ((evaluated & 63) === 0) yield { phase: 'proving', done: boxes.length, total: maxBoxes };
  }
  const volume = bx => bx.reduce((v, iv) => v * Math.max(iv.hi - iv.lo, 0), 1);
  const total = volume(box0) || 1;
  const share = { ok: 0, fail: 0, vac: 0, open: 0 };
  for (const b of boxes) share[b.s] += volume(b.box) / total;
  return {
    names, box0, boxes, share,
    proved: share.open < 1e-12 && share.fail === 0,
    disproved: share.fail > 0,
    coords: box0.length,
  };
}

Object.assign(MV, { Interval: { I, ops, compileI }, proveByIntervals });
})(typeof window !== 'undefined' ? window : globalThis);
