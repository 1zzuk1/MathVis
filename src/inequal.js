/* Theorem Sketchpad — exact inequalities. A claim L ≤ R (or <, ≥, >) is proved for every value of
   its variables allowed by their ranges and the hypotheses, or left to the samples. Steps:

   1. Pieces. |a|, min(a, b), max(a, b) are split into cases: |a| = a where a ≥ 0 and −a where
      a ≤ 0; min(a, b) = a where a ≤ b, and so on. Each case is proved separately.
   2. Constraints. The ranges (x in [0, 1], n in N, ε > 0) and the hypotheses (|x − 1| < δ) become
      polynomial constraints p ≥ 0, p > 0 or p = 0; a goal with a denominator needs the
      denominator's sign proved first.
   3. Deciding p ≥ 0 (or p > 0) under the constraints, by the first method that works:
      - signs: every term of p is ≥ 0 given the signs the ranges give its variables;
      - linear arithmetic: when p and the constraints are linear, Fourier–Motzkin elimination
        decides exactly whether p < 0 is possible;
      - one variable: Sturm sequences count the real roots of p and the constraints exactly, so
        the sign of p is known everywhere the constraints allow;
      - quadratic forms: a polynomial of degree 2 is ≥ 0 everywhere exactly when its matrix is
        positive semidefinite (checked by exact elimination);
      - and substitutions that bring p to one of those: y = x + h with h ≥ 0 from a constraint
        y ≥ x, factoring out a variable ≥ 0, x² = u when x appears only to even powers.
   Every method is exact (rational arithmetic in BigInt), so "proved" means proved; when none
   applies the samples decide, as before. */
'use strict';
(function (global) {
const MV = global.MV;
let K = null;   // the algebra kit from src/symbolic.js, taken on first use
const kit = () => K || (K = MV.SYMK);

class GiveUp extends Error {}
const isNA = e => e instanceof GiveUp || e instanceof RangeError || (K && e instanceof K.NotAlgebra);

/* ---------- small helpers on rationals and polynomials ---------- */
const qneg = q => ({ n: -q.n, d: q.d });
const qsub = (a, b) => kit().qadd(a, qneg(b));
const qsign = q => (q.n > 0n ? 1 : q.n < 0n ? -1 : 0);
const qcmp = (a, b) => qsign(qsub(a, b));
const qdiv = (a, b) => kit().qmul(a, kit().qinv(b));
const pdeg = p => Math.max(0, ...[...p.values()].map(t => t.vars.reduce((s, v) => s + v[1], 0)));
const pneg = p => kit().pscale(p, kit().Q(-1n));
const psub = (a, b) => kit().padd(a, pneg(b));
const pIsZero = p => p.size === 0;
// Replace variable v by the polynomial s (a fraction with constant denominator is fine).
const psubst = (p, v, s) => { const r = kit().rsubst(kit().R(p), v, kit().R(s)); if (!kit().pIsConst(r.d)) throw new GiveUp(); return r.n; };

/* ---------- constraints: { p, rel } meaning p ≥ 0, p > 0 or p = 0 ---------- */
// A fraction compared with 0: N/D ≥ 0 is N·D ≥ 0 where D ≠ 0 (and N/D = 0 is N = 0).
function rfConstraint(r, rel) {
  const k = kit();
  if (k.pIsConst(r.d)) return { r, rel };
  return { r: rel === '=' ? k.R(r.n) : k.R(k.pmul(r.n, r.d)), rel };
}
function cmpConstraints(a, op, b) {
  const k = kit();
  switch (op) {
    case '<': return [rfConstraint(k.rsub(b, a), '>')];
    case '<=': return [rfConstraint(k.rsub(b, a), '>=')];
    case '>': return [rfConstraint(k.rsub(a, b), '>')];
    case '>=': return [rfConstraint(k.rsub(a, b), '>=')];
    case '=': return [rfConstraint(k.rsub(a, b), '=')];
    default: return [];
  }
}
// The constraints a range puts on a variable (or any expression x): [a, b], (a, b], x > c, ℕ, a..b.
function domConstraints(x, dom, cx) {
  const k = kit(), out = [];
  const s = n => k.sym(n, cx);
  try {
    if (dom.type === 'interval') {
      out.push(...cmpConstraints(x, dom.loOpen ? '>' : '>=', s(dom.lo)));
      out.push(...cmpConstraints(x, dom.hiOpen ? '<' : '<=', s(dom.hi)));
    } else if (dom.type === 'bound') out.push(...cmpConstraints(x, dom.op, s(dom.c)));
    else if (dom.type === 'range') { out.push(...cmpConstraints(x, '>=', s(dom.lo))); out.push(...cmpConstraints(x, '<=', s(dom.hi))); }
    else if (dom.type === 'id' && dom.name === 'N') out.push(...cmpConstraints(x, '>=', k.rconst(k.ZERO)));
  } catch (e) { if (!isNA(e)) throw e; }
  return out;
}
// Hypotheses: comparisons (chains too), memberships, joined by "and".
function hypConstraints(node, cx) {
  const k = kit(), out = [];
  const walk = n => {
    if (!n) return;
    if (n.type === 'bin' && n.op === 'and') { walk(n.a); walk(n.b); return; }
    try {
      if (n.type === 'cmp') {
        const vals = n.args.map(a => k.sym(a, cx));
        n.ops.forEach((op, i) => out.push(...cmpConstraints(vals[i], op, vals[i + 1])));
      } else if (n.type === 'in' && !n.neg) out.push(...domConstraints(k.sym(n.elem, cx), n.dom, cx));
    } catch (e) { if (!isNA(e)) throw e; }
  };
  walk(node);
  return out;
}

/* ---------- pieces: split |a|, min, max into cases ---------- */
const MAX_CASES = 256;
// Calls fn(goals, constraints) for every case; goals and constraints are fractions here.
function eachCase(goals, cons, cx, fn) {
  const k = kit();
  let count = 0;
  const rec = (gs, cs) => {
    const vars = new Set([...gs.flatMap(g => [...k.rvarsOf(g.r)]), ...cs.flatMap(c => [...k.rvarsOf(c.r)])]);
    const v = [...vars].find(x => cx.pieces.has(x));
    if (!v) { if (++count > MAX_CASES) throw new GiveUp(); return fn(gs, cs); }
    const pc = cx.pieces.get(v);
    const sub = (r, s) => (k.rvarsOf(r).has(v) ? k.rsubst(r, v, s) : r);
    const branch = (s, extra) => rec(gs.map(g => ({ ...g, r: sub(g.r, s) })), [...cs.map(c => ({ ...c, r: sub(c.r, s) })), ...extra]);
    if (pc.kind === 'abs') {
      return branch(pc.arg, [rfConstraint(pc.arg, '>=')]) && branch(k.rneg(pc.arg), [rfConstraint(k.rneg(pc.arg), '>=')]);
    }
    const [a, b] = pc.args, aSmall = rfConstraint(k.rsub(b, a), '>='), bSmall = rfConstraint(k.rsub(a, b), '>=');
    if (pc.kind === 'min') return branch(a, [aSmall]) && branch(b, [bSmall]);
    return branch(a, [bSmall]) && branch(b, [aSmall]);
  };
  return rec(goals, cons);
}

/* ---------- facts about symbols ---------- */
let FACTS = new Map();   // the facts of the claim being proved (set by proveAll)
function factConstraints(vars) {
  const k = kit(), out = [];
  for (const v of vars) {
    const f = FACTS.get(v);
    if (!f) continue;
    const x = k.pvar(v);
    if (f.kind === 'bounded') out.push({ p: k.padd(x, k.pconst(k.ONE)), rel: '>=' }, { p: psub(k.pconst(k.ONE), x), rel: '>=' });
    else if (f.kind === 'positive') out.push({ p: x, rel: '>' });
    else if (f.kind === 'sqrt') {
      out.push({ p: x, rel: '>=' });
      if (k.pIsConst(f.arg.d)) out.push({ p: psub(k.pmul(x, x), f.arg.n), rel: '=' });
    }
  }
  return out;
}

/* ---------- deciding p ≥ 0 / p > 0 under polynomial constraints ---------- */
let budget = 0, method = null;
const toPoly = cs => {
  const k = kit();
  return cs.map(c => (k.pIsConst(c.r.d) ? { p: c.r.n, rel: c.rel } : null)).filter(Boolean);
};

// Bounds a variable gets from constraints a·x + c ≥ 0 (or > 0, = 0) in that variable alone.
function boundsOf(cons) {
  const B = new Map();
  for (const c of cons) {
    const L = linear(c.p);
    if (!L || L.a.size !== 1) continue;
    const [[x, a]] = [...L.a];
    const val = qdiv(qneg(L.c), a), b = B.get(x) || {};
    const lower = () => { if (!b.lo || qcmp(val, b.lo) > 0 || (qcmp(val, b.lo) === 0 && c.rel === '>')) { b.lo = val; b.loStrict = c.rel === '>'; } };
    const upper = () => { if (!b.hi || qcmp(val, b.hi) < 0 || (qcmp(val, b.hi) === 0 && c.rel === '>')) { b.hi = val; b.hiStrict = c.rel === '>'; } };
    if (c.rel === '=') { lower(); upper(); }
    else if (a.n > 0n) lower(); else upper();
    B.set(x, b);
  }
  return B;
}
// The sign a variable must have: +1 (≥ 0, strict if > 0), −1, or unknown.
function signOf(b) {
  if (!b) return null;
  if (b.lo && (qsign(b.lo) > 0 || (qsign(b.lo) === 0))) return { s: 1, strict: qsign(b.lo) > 0 || b.loStrict };
  if (b.hi && qsign(b.hi) <= 0) return { s: -1, strict: qsign(b.hi) < 0 || b.hiStrict };
  return null;
}
// 1. Every term ≥ 0 from the signs of its variables (and one > 0 for a strict goal).
function termwise(p, rel, bounds) {
  let somePos = false;
  for (const t of p.values()) {
    let s = qsign(t.c), strict = true;
    for (const [v, e] of t.vars) {
      if (e % 2 === 0) { const sg = signOf(bounds.get(v)); if (!(sg && sg.strict)) strict = false; continue; }
      const sg = signOf(bounds.get(v));
      if (!sg) return false;
      s *= sg.s;
      if (!sg.strict) strict = false;
    }
    if (s < 0) return false;
    if (s > 0 && strict) somePos = true;
  }
  return rel === '>=' || somePos;
}

// 2. Linear arithmetic: Fourier–Motzkin elimination; exact for linear constraints.
function linear(p) {
  const k = kit(), a = new Map();
  let c = k.ZERO;
  for (const t of p.values()) {
    if (!t.vars.length) c = t.c;
    else if (t.vars.length === 1 && t.vars[0][1] === 1) a.set(t.vars[0][0], t.c);
    else return null;
  }
  return { a, c };
}
function fmInfeasible(rows) {
  const k = kit();
  const vars = [...new Set(rows.flatMap(r => [...r.a.keys()]))];
  for (const v of vars) {
    const pos = [], neg = [], rest = [];
    for (const r of rows) { const q = r.a.get(v); if (!q || k.qzero(q)) rest.push(r); else if (q.n > 0n) pos.push(r); else neg.push(r); }
    const next = rest;
    for (const P of pos) for (const N of neg) {
      const kp = P.a.get(v), kn = qneg(N.a.get(v));
      const a = new Map();
      for (const [x, q] of P.a) if (x !== v) a.set(x, k.qmul(q, kn));
      for (const [x, q] of N.a) if (x !== v) { const s = k.qadd(a.get(x) || k.ZERO, k.qmul(q, kp)); if (k.qzero(s)) a.delete(x); else a.set(x, s); }
      next.push({ a, c: k.qadd(k.qmul(P.c, kn), k.qmul(N.c, kp)), strict: P.strict || N.strict });
      if (next.length > 4000) throw new GiveUp();
    }
    rows = next;
  }
  return rows.some(r => (r.strict ? r.c.n <= 0n : r.c.n < 0n));
}
function fm(p, rel, cons) {
  const rows = [];
  const add = (q, strict) => { const L = linear(q); if (!L) throw new GiveUp(); rows.push({ ...L, strict }); };
  for (const c of cons) { if (c.rel === '=') { add(c.p, false); add(pneg(c.p), false); } else add(c.p, c.rel === '>'); }
  add(pneg(p), rel === '>=');   // the goal fails: −p > 0 (or −p ≥ 0 for a strict goal)
  return fmInfeasible(rows);
}

// 3. One variable: dense polynomials (coefficients low → high) and Sturm sequences.
const dTrim = a => { while (a.length && kit().qzero(a[a.length - 1])) a.pop(); return a; };
function dense(p, v) {
  const k = kit(), a = [];
  for (const t of p.values()) {
    if (t.vars.length > 1 || (t.vars.length === 1 && t.vars[0][0] !== v)) return null;
    const e = t.vars.length ? t.vars[0][1] : 0;
    if (e > 40) throw new GiveUp();
    a[e] = t.c;
  }
  for (let i = 0; i < a.length; i++) if (!a[i]) a[i] = k.ZERO;
  return dTrim(a);
}
const dEval = (a, x) => { const k = kit(); let s = k.ZERO; for (let i = a.length - 1; i >= 0; i--) s = k.qadd(k.qmul(s, x), a[i]); return s; };
const dDeriv = a => dTrim(a.slice(1).map((c, i) => kit().qmul(c, kit().Q(BigInt(i + 1)))));
function dDivmod(a, b) {
  const k = kit();
  let r = a.slice();
  const q = [];
  const lb = b[b.length - 1];
  while (r.length >= b.length && r.length) {
    const f = qdiv(r[r.length - 1], lb), s = r.length - b.length;
    q[s] = f;
    for (let i = 0; i < b.length; i++) r[s + i] = qsub(r[s + i], k.qmul(f, b[i]));
    r.pop();
    dTrim(r);
  }
  for (let i = 0; i < q.length; i++) if (!q[i]) q[i] = k.ZERO;
  return { q: dTrim(q), r: dTrim(r) };
}
const dMonic = a => (a.length ? a.map(c => qdiv(c, a[a.length - 1])) : a);
function dGcd(a, b) { while (b.length) [a, b] = [b, dDivmod(a, b).r]; return dMonic(a); }
const dMul = (a, b) => { const k = kit(), out = Array(a.length + b.length - 1).fill(k.ZERO); a.forEach((x, i) => b.forEach((y, j) => { out[i + j] = k.qadd(out[i + j], k.qmul(x, y)); })); return dTrim(out); };
function sturm(a) {
  const seq = [a, dDeriv(a)];
  while (seq[seq.length - 1].length) { const r = dDivmod(seq[seq.length - 2], seq[seq.length - 1]).r; if (!r.length) break; seq.push(r.map(qneg)); }
  return seq.filter(s => s.length);
}
function variations(seq, x) {
  let n = 0, prev = 0;
  for (const s of seq) { const g = qsign(dEval(s, x)); if (g && prev && g !== prev) n++; if (g) prev = g; }
  return n;
}
// Distinct real roots of a in (lo, hi], neither end a root.
const countRoots = (seq, lo, hi) => variations(seq, lo) - variations(seq, hi);
// |roots| < B (Cauchy).
function cauchy(a) {
  const k = kit();
  let m = k.ZERO;
  for (let i = 0; i < a.length - 1; i++) { const q = kit().qabs(qdiv(a[i], a[a.length - 1])); if (qcmp(q, m) > 0) m = q; }
  return k.qadd(m, k.ONE);
}
// Isolate the roots of a square-free a: intervals (lo, hi] with one root each, or exact roots.
function isolate(a, seq, B) {
  const k = kit(), out = [], half = x => k.qmul(x, k.Q(1n, 2n));
  const stack = [[qneg(B), B]];
  let guard = 0;
  while (stack.length) {
    if (++guard > 4000) throw new GiveUp();
    const [lo, hi] = stack.pop();
    const n = countRoots(seq, lo, hi);
    if (n === 0) continue;
    if (n === 1) { out.push({ lo, hi }); continue; }
    const m = half(k.qadd(lo, hi));
    if (k.qzero(dEval(a, m))) {
      let d = half(qsub(hi, lo));
      for (let i = 0; i < 200; i++) {
        d = half(d);
        const l = qsub(m, d), h = k.qadd(m, d);
        if (!k.qzero(dEval(a, l)) && !k.qzero(dEval(a, h)) && countRoots(seq, l, h) === 1) { out.push({ exact: m, lo: l, hi: h }); stack.push([lo, l], [h, hi]); break; }
      }
      continue;
    }
    stack.push([lo, m], [m, hi]);
  }
  return out;
}
// Decide p rel 0 for one variable v, under constraints in v alone: exact.
function univariate(p, rel, cons, v) {
  const k = kit();
  const dp = dense(p, v);
  if (!dp) return false;
  const dcs = [];
  for (const c of cons) { const d = dense(c.p, v); if (d) dcs.push({ d, rel: c.rel }); }
  const polys = [dp, ...dcs.map(c => c.d)].filter(d => d.length > 1);
  const okRel = (s, rel) => (rel === '>=' ? s >= 0 : rel === '>' ? s > 0 : s === 0);
  const constSign = d => qsign(d.length ? d[0] : k.ZERO);
  if (!polys.length) {
    const feasible = dcs.every(c => okRel(constSign(c.d), c.rel));
    return !feasible || okRel(constSign(dp), rel);
  }
  let P = polys.reduce(dMul);
  P = dDivmod(P, dGcd(P, dDeriv(P))).q;   // square-free: the same roots, each once
  const seq = sturm(P), B = cauchy(P);
  const roots = isolate(P, seq, B);
  const seqs = new Map();
  const signAt = (d, pt) => {
    if (d.length <= 1) return constSign(d);
    if (pt.exact) return qsign(dEval(d, pt.exact));
    if (pt.at) return qsign(dEval(d, pt.at));
    if (!seqs.has(d)) seqs.set(d, sturm(d));
    return countRoots(seqs.get(d), pt.lo, pt.hi) > 0 ? 0 : qsign(dEval(d, pt.hi));
  };
  const check = pt => {
    const feasible = dcs.every(c => okRel(signAt(c.d, pt), c.rel));
    return !feasible || okRel(signAt(dp, pt), rel);
  };
  // Between the roots every polynomial keeps its sign: test one point in each gap, and the roots.
  const tests = [{ at: qneg(k.qadd(B, k.ONE)) }, { at: k.qadd(B, k.ONE) }];
  for (const r of roots) { tests.push({ at: r.lo }, { at: r.hi }); tests.push(r.exact ? { exact: r.exact } : { lo: r.lo, hi: r.hi }); }
  return tests.every(check);
}

// 4. Degree 2: p = zᵀMz with z = (1, x₁, …), and p ≥ 0 for all x exactly when M is positive
// semidefinite (> 0 when M is positive definite).
function quadForm(p, rel) {
  const k = kit();
  if (pdeg(p) > 2) return false;
  const vars = [...k.pvars(p)].sort();
  const n = vars.length + 1, M = Array.from({ length: n }, () => Array(n).fill(k.ZERO));
  const idx = v => vars.indexOf(v) + 1;
  for (const t of p.values()) {
    if (!t.vars.length) M[0][0] = t.c;
    else if (t.vars.length === 1 && t.vars[0][1] === 1) { const i = idx(t.vars[0][0]); M[0][i] = M[i][0] = k.qmul(t.c, k.Q(1n, 2n)); }
    else if (t.vars.length === 1) { const i = idx(t.vars[0][0]); M[i][i] = t.c; }
    else { const i = idx(t.vars[0][0]), j = idx(t.vars[1][0]); M[i][j] = M[j][i] = k.qmul(t.c, k.Q(1n, 2n)); }
  }
  for (let c = 0; c < n; c++) {
    const d = M[c][c];
    if (d.n < 0n) return false;
    if (d.n === 0n) {
      if (rel === '>') return false;
      for (let j = c + 1; j < n; j++) if (!k.qzero(M[c][j])) return false;
      continue;
    }
    for (let i = c + 1; i < n; i++) for (let j = c + 1; j < n; j++) M[i][j] = qsub(M[i][j], qdiv(k.qmul(M[i][c], M[c][j]), d));
  }
  return true;
}

// 5. Handelman: on a region cut out by linear constraints gᵢ ≥ 0, p ≥ 0 when p is a combination
// of products of the gᵢ with coefficients ≥ 0; the coefficients solve a linear program, done
// here exactly by the simplex method. (p > 0 when some product of strict constraints, or the
// constant 1, gets a positive coefficient.)
function simplexFeasible(A, b, strictCols) {
  // Rows A·c = b, c ≥ 0. Phase 1 with an artificial variable per row, then (for a strict goal)
  // phase 2 maximizing the strict columns. Exact rationals, Bland's rule.
  const k = kit(), m = A.length, n = A[0].length;
  const T = A.map((row, i) => { const neg = qsign(b[i]) < 0; const r = row.map(x => (neg ? qneg(x) : x)); return [...r, ...Array.from({ length: m }, (_, j) => (j === i ? k.ONE : k.ZERO)), neg ? qneg(b[i]) : b[i]]; });
  const basis = Array.from({ length: m }, (_, i) => n + i);
  const W = n + m;   // index of the right-hand side
  const pivot = (r, c) => {
    const pv = T[r][c];
    T[r] = T[r].map(x => qdiv(x, pv));
    for (let i = 0; i < m; i++) if (i !== r && !k.qzero(T[i][c])) { const f = T[i][c]; T[i] = T[i].map((x, j) => qsub(x, k.qmul(f, T[r][j]))); }
    basis[r] = c;
  };
  // Reduced costs of the objective (maximize Σ obj·x) over the current basis.
  const run = (obj, allowed) => {
    for (let it = 0; it < 500; it++) {
      if (--budget < 0) throw new GiveUp();
      let enter = -1;
      for (let j = 0; j < W && enter < 0; j++) {
        if (!allowed(j) || basis.includes(j)) continue;
        let rc = obj[j] || k.ZERO;
        for (let i = 0; i < m; i++) if (obj[basis[i]]) rc = qsub(rc, k.qmul(obj[basis[i]], T[i][j]));
        if (qsign(rc) > 0) enter = j;
      }
      if (enter < 0) return 'optimal';
      let leave = -1, best = null;
      for (let i = 0; i < m; i++) {
        // An artificial variable still in the basis (at 0) must stay 0: it leaves first.
        if (basis[i] >= n && !k.qzero(T[i][enter]) && k.qzero(T[i][W])) { leave = i; best = k.ZERO; break; }
        if (qsign(T[i][enter]) > 0) { const ratio = qdiv(T[i][W], T[i][enter]); if (!best || qcmp(ratio, best) < 0 || (qcmp(ratio, best) === 0 && basis[i] < basis[leave])) { best = ratio; leave = i; } }
      }
      if (leave < 0) return 'unbounded';
      pivot(leave, enter);
    }
    throw new GiveUp();
  };
  const phase1 = {};
  for (let j = n; j < n + m; j++) phase1[j] = qneg(k.ONE);
  run(phase1, () => true);
  for (let i = 0; i < m; i++) if (basis[i] >= n && qsign(T[i][W]) !== 0) return false;   // infeasible
  if (!strictCols) return true;
  const value = j => { const i = basis.indexOf(j); return i < 0 ? k.ZERO : T[i][W]; };
  if (strictCols.some(j => qsign(value(j)) > 0)) return true;
  const obj = {};
  for (const j of strictCols) obj[j] = k.ONE;
  const res = run(obj, j => j < n);
  return res === 'unbounded' || strictCols.some(j => qsign(value(j)) > 0);
}
function handelman(p, rel, lin) {
  const k = kit();
  const D = pdeg(p);
  if (D < 2 || D > 4 || lin.length > 8) return false;
  for (const deg of [D, D + 1]) {
    // Every product of at most deg constraints (with repetition), the empty one being 1.
    const prods = [{ poly: k.pconst(k.ONE), strict: true }];
    const grow = (start, depth, poly, strict) => {
      if (depth === deg) return;
      for (let i = start; i < lin.length; i++) {
        const q = k.pmul(poly, lin[i].p), s = strict && lin[i].rel === '>';
        prods.push({ poly: q, strict: s });
        if (prods.length > 260) throw new GiveUp();
        grow(i, depth + 1, q, s);
      }
    };
    grow(0, 0, k.pconst(k.ONE), true);
    const monos = new Map();
    for (const x of [p, ...prods.map(q => q.poly)]) for (const [key] of x) if (!monos.has(key)) monos.set(key, monos.size);
    const A = [...monos.keys()].map(key => prods.map(q => (q.poly.get(key) ? q.poly.get(key).c : k.ZERO)));
    const b = [...monos.keys()].map(key => (p.get(key) ? p.get(key).c : k.ZERO));
    const strictCols = rel === '>' ? prods.map((q, j) => (q.strict ? j : -1)).filter(j => j >= 0) : null;
    if (simplexFeasible(A, b, strictCols)) return true;
  }
  return false;
}

// The methods without substitutions.
function basic(p, rel, cons) {
  const k = kit();
  if (--budget < 0) throw new GiveUp();
  if (k.pIsConst(p) && (rel === '>=' ? qsign(k.pConstVal(p)) >= 0 : qsign(k.pConstVal(p)) > 0)) { method = method || 'arithmetic'; return true; }
  const bounds = boundsOf(cons);
  if (termwise(p, rel, bounds)) { method = 'signs'; return true; }
  if (linear(p) && cons.every(c => linear(c.p))) { if (fm(p, rel, cons)) { method = 'linear'; return true; } return false; }
  const pv = [...k.pvars(p)];
  const cand = pv.length === 1 ? pv : pv.length === 0 ? [...new Set(cons.flatMap(c => [...k.pvars(c.p)]))].filter(v => cons.some(c => dense(c.p, v))) : [];
  for (const v of cand) if (univariate(p, rel, cons, v)) { method = 'one variable'; return true; }
  if (quadForm(p, rel)) { method = 'squares'; return true; }
  const lin = cons.filter(c => c.rel !== '=' && linear(c.p) && !k.pIsConst(c.p));
  if (lin.length && handelman(p, rel, lin)) { method = 'products'; return true; }
  // One square root, to the first power: p = A + B·√u with B constant. As √u ≥ 0 and (√u)² = u,
  // A − c√u ≥ 0 (c > 0) exactly when A ≥ 0 and A² − c²u ≥ 0; A + c√u ≥ 0 when A ≥ 0.
  for (const v of pv) {
    const f = FACTS.get(v);
    if (!f || f.kind !== 'sqrt' || !k.pIsConst(f.arg.d)) continue;
    const deg = Math.max(...[...p.values()].map(t => (t.vars.find(x => x[0] === v) || [v, 0])[1]));
    if (deg !== 1) continue;
    const A = new Map(), Bp = new Map();
    for (const [key, t] of p) { if (t.vars.some(x => x[0] === v)) { const vars = t.vars.filter(x => x[0] !== v); Bp.set(k.monoKey(vars), { vars, c: t.c }); } else A.set(key, t); }
    if (!k.pIsConst(Bp)) continue;
    const B = k.pConstVal(Bp), others = cons.filter(c => !k.pvars(c.p).has(v));
    // A + c√u ≥ 0 also when c²u − A² ≥ 0, since then c√u ≥ |A| ≥ −A (so x ≤ √(x² + y²)).
    const ok = B.n > 0n ? (decide(A, rel, others) || decide(psub(k.pscale(f.arg.n, k.qmul(B, B)), k.pmul(A, A)), rel, others))
      : (decide(A, rel, others) && decide(psub(k.pmul(A, A), k.pscale(f.arg.n, k.qmul(B, B))), rel, others));
    if (ok) { method = 'square roots'; return true; }
  }
  // A factor v^m with v ≥ 0 doesn't change the sign of a ≥ goal.
  for (const v of pv) {
    const sg = signOf(bounds.get(v));
    if (!sg || sg.s < 0 || (rel === '>' && !sg.strict)) continue;
    const m = Math.min(...[...p.values()].map(t => (t.vars.find(x => x[0] === v) || [v, 0])[1]));
    if (m > 0) {
      const q = new Map();
      for (const t of p.values()) { const vars = t.vars.map(([x, e]) => [x, x === v ? e - m : e]).filter(x => x[1] > 0); q.set(k.monoKey(vars), { vars, c: t.c }); }
      if (basic(q, rel, cons)) return true;
    }
  }
  // A variable that appears only to even powers: x² = u ≥ 0.
  for (const v of pv) {
    if (![...p.values()].every(t => (t.vars.find(x => x[0] === v) || [v, 0])[1] % 2 === 0)) continue;
    const u = v + '²', q = new Map();
    for (const t of p.values()) { const vars = t.vars.map(([x, e]) => (x === v ? [u, e / 2] : [x, e])).sort((a, b) => (a[0] < b[0] ? -1 : 1)); q.set(k.monoKey(vars), { vars, c: t.c }); }
    if (basic(q, rel, [...cons.filter(c => !k.pvars(c.p).has(v)), { p: k.pvar(u), rel: '>=' }])) return true;
  }
  return false;
}

// With substitutions from the linear constraints: y = (h − rest)/a where a·y + rest = h ≥ 0, so
// y ≥ x becomes y = x + h; two levels deep.
function decide(p, rel, cons, depth = 0) {
  const k = kit();
  if (basic(p, rel, cons)) return true;
  if (depth >= 2) return false;
  let tries = 0;
  for (const c of cons) {
    const L = linear(c.p);
    if (!L || !L.a.size) continue;
    for (const [y, a] of L.a) {
      if (++tries > 10) return false;
      const h = `ℎ${depth}${tries}`;
      // y = (h − (rest))/a, with h = the constraint's left side (or 0 for an equation).
      const rest = psub(c.p, k.pscale(k.pvar(y), a));
      const yv = k.pscale(psub(c.rel === '=' ? new Map() : k.pvar(h), rest), k.qinv(a));
      try {
        const p2 = psubst(p, y, yv);
        const cs2 = cons.filter(d => d !== c).map(d => ({ p: k.pvars(d.p).has(y) ? psubst(d.p, y, yv) : d.p, rel: d.rel }));
        if (c.rel !== '=') cs2.push({ p: k.pvar(h), rel: c.rel });
        if (decide(p2, rel, cs2, depth + 1)) return true;
      } catch (e) { if (!isNA(e)) throw e; }
    }
  }
  return false;
}

// A goal g rel 0 (a fraction) in one case: its denominator's sign first.
function provePolyGoal(g, rel, cons) {
  const k = kit();
  if (k.pIsConst(g.d)) return decide(g.n, rel, cons);
  if (decide(g.d, '>', cons)) return decide(g.n, rel, cons);
  if (decide(pneg(g.d), '>', cons)) return decide(pneg(g.n), rel, cons);
  return false;
}
const METHOD = {
  arithmetic: 'arithmetic', signs: 'the signs of its terms', linear: 'linear arithmetic (Fourier–Motzkin elimination)',
  'one variable': 'exact root counting in one variable (Sturm sequences)', squares: 'a sum of squares (its quadratic form is positive semidefinite)',
  'square roots': 'squaring away a square root',
};
// Prove every goal ({ r, rel }) under the constraints, case by case.
function proveAll(goals, cons, cx) {
  budget = 800; method = null;
  FACTS = cx.facts || new Map();
  const used = new Set();
  let split = false;
  try {
    const ok = eachCase(goals, cons, cx, (gs, cs) => {
      if (gs.length !== goals.length || cs.length !== cons.length) split = true;
      const pc = toPoly(cs);
      pc.push(...factConstraints(new Set([...gs.flatMap(g => [...kit().rvarsOf(g.r)]), ...pc.flatMap(c => [...kit().pvars(c.p)])])));
      return gs.every(g => {
        method = null;
        // d = 0 on this case: zero outright, or both d ≥ 0 and d ≤ 0 there (min(a, b) − a = 0 where a ≤ b,
        // or where the case only allows a = b).
        const r = g.rel === '=' ? (kit().rIsZero(g.r) || (provePolyGoal(g.r, '>=', pc) && provePolyGoal(kit().rneg(g.r), '>=', pc))) : provePolyGoal(g.r, g.rel, pc);
        if (r && method) used.add(method);
        return r;
      });
    });
    return ok ? { proved: true, methods: [...used], split } : { proved: false };
  } catch (e) { if (isNA(e)) return { proved: false }; throw e; }
}

/* ---------- claims and proof steps ---------- */
// Every denominator in the goal is nonzero wherever the claim speaks (1 + t² is; x is not), or
// the goal would be undefined somewhere and nothing is proved.
function denominatorsSafe(denoms, cons, cx) {
  const k = kit();
  return denoms.every(d => proveAll([{ r: d, rel: '>' }], cons, cx).proved || proveAll([{ r: k.rneg(d), rel: '>' }], cons, cx).proved);
}
const INEQ = new Set(['<', '<=', '>', '>=']);
// The comparisons a conclusion makes: a chain, or several joined by "and".
function comparisons(node, cx) {
  const k = kit(), out = [];
  const walk = n => {
    if (n.type === 'bin' && n.op === 'and') { walk(n.a); walk(n.b); return; }
    if (n.type !== 'cmp') throw new GiveUp();
    const vals = n.args.map(a => k.sym(a, cx));
    n.ops.forEach((op, i) => {
      if (op === '!=' || op === '~=') throw new GiveUp();
      // a < b as b − a > 0, a = b as a − b = 0
      const [rel, r] = op === '<' ? ['>', k.rsub(vals[i + 1], vals[i])] : op === '<=' ? ['>=', k.rsub(vals[i + 1], vals[i])]
        : op === '>' ? ['>', k.rsub(vals[i], vals[i + 1])] : op === '>=' ? ['>=', k.rsub(vals[i], vals[i + 1])] : ['=', k.rsub(vals[i], vals[i + 1])];
      out.push({ r: rel === '=' ? k.mergeAbs(k.trig(r), cx) : k.mergeAbs(r, cx), rel });
    });
  };
  walk(node);
  return out;
}
const hasIneq = n => n && ((n.type === 'cmp' && n.ops.some(o => INEQ.has(o))) || (n.type === 'bin' && n.op === 'and' && (hasIneq(n.a) || hasIneq(n.b))));
function explain(res) {
  const how = res.methods.map(m => METHOD[m] || m).join(', ');
  return `Proved exactly${res.split ? ', splitting |…|, min and max into cases,' : ''}${how ? ' by ' + how : ''}: it holds for every value allowed, not just the samples.`;
}

// A claim (the analyzer's prepared P): ∀ (binders): hypothesis ⇒ comparisons.
function inequalityClaim(P) {
  if (!hasIneq(P.concl) && !(P.concl && P.concl.type === 'cmp')) return null;
  try {
    const k = kit(), cx = k.context(P.scope, P.U || []);
    const goals = comparisons(P.concl, cx), denoms = cx.denoms.slice();
    if (!goals.some(g => g.rel !== '=') && !goals.some(g => [...k.rvarsOf(g.r)].some(v => cx.pieces.has(v)))) return null;
    const cons = [];
    for (const b of P.U || []) if (!b.pattern) cons.push(...domConstraints(k.rvar(b.name), b.dom, cx));
    if (P.hyp) cons.push(...hypConstraints(P.hyp, cx));
    if (cx.conds.length) return null;   // sums with symbolic ranges: the identity check handles those
    if (!denominatorsSafe(denoms, cons, cx)) return null;
    const res = proveAll(goals, cons, cx);
    return res.proved ? { proved: true, identity: true, kind: 'inequality', methods: res.methods, note: explain(res) } : null;
  } catch (e) { if (isNA(e)) return null; throw e; }
}

// A proof step: the variables so far (with their ranges), the values chosen, the assumptions.
function inequalityStep(ctx, F, env) {
  if (!hasIneq(F)) return null;
  try {
    const k = kit();
    const binders = ctx.filter(e => e.kind === 'var').map(e => e.binder);
    const cx = k.context(env, binders);
    for (const e of ctx) if (e.kind === 'def') cx.subst.set(e.name, k.sym(e.expr, cx));
    const cons = [];
    for (const b of binders) if (!b.pattern && cx.subst.get(b.name) === undefined) cons.push(...domConstraints(k.rvar(b.name), b.dom, cx));
    for (const e of ctx) if (e.kind === 'hyp' && !e.contra) cons.push(...hypConstraints(e.expr, cx));
    const before = cx.denoms.length, goals = comparisons(F, cx);
    if (!denominatorsSafe(cx.denoms.slice(before), cons, cx)) return null;
    const res = proveAll(goals, cons, cx);
    return res.proved ? { proved: true, methods: res.methods, note: 'Exact: ' + explain(res).replace(/^Proved exactly/, 'proved') } : null;
  } catch (e) { if (isNA(e)) return null; throw e; }
}

// An identity left with |a|, min or max in it: zero in every case they split into (cases that
// can't happen under the ranges are skipped).
function casesZero(d, cx) {
  const k = kit(), cons = [];
  for (const [name, dom] of cx.doms) cons.push(...domConstraints(k.rvar(name), dom, cx));
  return proveAll([{ r: d, rel: '=' }], cons, cx).proved;
}

Object.assign(MV, { inequalityClaim, inequalityStep, casesZero });
})(typeof window !== 'undefined' ? window : globalThis);
