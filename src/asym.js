/* Theorem Sketchpad — exact eventual and local behaviour, from formulas instead of samples.

   A sequence a(n) written as a formula (n => (-1)^n/sqrt(n) + 1/n) is expanded as n → ∞ into a
   sum of terms  c · e^(f·n·ln n) · e^(r·n) · n^p · (ln n)^q · (oscillating factor),  ordered by
   growth (the key [f, r, p, q]). From the expansion: limits, whether the series Σ a(n) converges
   (by comparison, Bertrand, Leibniz and Dirichlet, each term separately), and whether a(n) ≤ b(n)
   eventually. A function near a point a is handled by the same machinery with x = a ± 1/t,
   t → ∞: continuity, differentiability and continuity of the derivative at a (xᵃ·sin(1/xᵇ) and
   friends) are decided exactly.

   Soundness first: every expansion records a bound such that all omitted terms are of order at
   most the bound, terms at or below it are dropped as unreliable, and anything the rules don't
   cover gives null ("don't know"), so the caller falls back to sampling. */
'use strict';
(function (global) {
const MV = global.MV;

/* ---------- keys: [f, r, p, q, s] for e^(f·t·ln t)·e^(r·t)·t^p·(ln t)^q·(ln ln t)^s ---------- */
const K0 = [0, 0, 0, 0, 0];
const kadd = (a, b) => a.map((x, i) => x + b[i]);
const kscale = (a, s) => a.map(x => x * s);
const kcmp = (a, b) => { for (let i = 0; i < a.length; i++) { const d = a[i] - b[i]; if (Math.abs(d) > 1e-9) return d > 0 ? 1 : -1; } return 0; };
const kmax = (a, b) => (a === null ? b : b === null ? a : kcmp(a, b) >= 0 ? a : b);

/* ---------- oscillating factors ----------
   alt:  (−1)^n;  trig: sin/cos of a linear argument (mean zero, bounded partial sums);
   osc:  any other bounded oscillation (no limit, nothing known about its sums). */
const oscKey = o => (!o ? '' : o.kind === 'alt' ? 'alt' : `${o.kind}:${o.id}`);
function oscMul(a, b) {
  if (!a) return { o: b };
  if (!b) return { o: a };
  if (a.kind === 'alt' && b.kind === 'alt') return { o: null };
  if (a.kind === 'alt' && b.kind === 'trig') return { o: { kind: 'trig', id: '(−1)ⁿ·' + b.id } };
  if (b.kind === 'alt' && a.kind === 'trig') return { o: { kind: 'trig', id: '(−1)ⁿ·' + a.id } };
  return { o: { kind: 'osc', id: [oscKey(a), oscKey(b)].sort().join('·') } };
}

/* ---------- expansions: { terms: [{ c, k, osc }], bound: key | null } ---------- */
const ZERO = { terms: [], bound: null };
const isZero = E => !E.terms.length && E.bound === null;
const lead = E => E.terms[0];
const MAXTERMS = 12;

function norm(terms, bound) {
  const out = [];
  terms = terms.filter(t => Number.isFinite(t.c)).sort((a, b) => kcmp(b.k, a.k));
  for (const t of terms) {
    const same = out.find(u => kcmp(u.k, t.k) === 0 && oscKey(u.osc) === oscKey(t.osc));
    if (same) same.c += t.c; else out.push({ c: t.c, k: t.k.slice(), osc: t.osc });
  }
  const big = Math.max(0, ...out.map(t => Math.abs(t.c)));
  let kept = out.filter(t => Math.abs(t.c) > 1e-12 * big && t.c !== 0);
  // Like terms that nearly cancel (to rounding) are lower-order information we don't have.
  for (const t of out) if (t.c !== 0 && Math.abs(t.c) <= 1e-12 * big) bound = kmax(bound, t.k);
  if (bound) kept = kept.filter(t => kcmp(t.k, bound) > 0);
  if (kept.length > MAXTERMS) { bound = kmax(bound, kept[MAXTERMS].k); kept = kept.slice(0, MAXTERMS).filter(t => kcmp(t.k, bound) > 0); }
  return { terms: kept, bound };
}
const C = c => (c === 0 ? ZERO : { terms: [{ c, k: K0.slice(), osc: null }], bound: null });
const mono = (c, k, osc = null) => ({ terms: [{ c, k, osc }], bound: null });
const add = (A, B) => (!A || !B ? null : norm([...A.terms, ...B.terms], kmax(A.bound, B.bound)));
const neg = A => (!A ? null : { terms: A.terms.map(t => ({ ...t, c: -t.c })), bound: A.bound });
const sub = (A, B) => add(A, neg(B));
function mul(A, B) {
  if (!A || !B) return null;
  if (isZero(A) || isZero(B)) return ZERO;
  const terms = [];
  for (const a of A.terms) for (const b of B.terms) {
    const m = oscMul(a.osc, b.osc);
    terms.push({ c: a.c * b.c, k: kadd(a.k, b.k), osc: m.o });
  }
  let bound = null;
  const la = A.terms.length ? A.terms[0].k : A.bound, lb = B.terms.length ? B.terms[0].k : B.bound;
  if (A.bound && lb) bound = kmax(bound, kadd(A.bound, lb));
  if (B.bound && la) bound = kmax(bound, kadd(B.bound, la));
  return norm(terms, bound);
}
const scale = (A, s) => (!A ? null : mul(A, C(s)));

// Σ coef[j]·W^j for j ≤ m, W → 0; the bound covers the omitted powers.
function series(W, coefs) {
  if (!W) return null;
  if (W.terms.length && kcmp(W.terms[0].k, K0) >= 0) return null;   // W must tend to 0
  if (!W.terms.length && W.bound && kcmp(W.bound, K0) >= 0) return null;
  let out = C(coefs[0]), P = C(1);
  for (let j = 1; j < coefs.length; j++) {
    P = mul(P, W);
    if (!P) return null;
    if (coefs[j]) out = add(out, scale(P, coefs[j]));
  }
  const top = W.terms.length ? W.terms[0].k : W.bound;
  if (top && (W.terms.length || W.bound)) {
    const omitted = kscale(top, coefs.length);
    out = norm(out.terms, kmax(out.bound, omitted));
  }
  return out;
}
// A = M(1 + W) with M the leading term.
function split(A) {
  if (!A || !A.terms.length) return null;
  const M = A.terms[0];
  const rest = { terms: A.terms.slice(1), bound: A.bound };
  if (M.osc && M.osc.kind !== 'alt') return null;
  const W = mul(rest, mono(1 / M.c, kscale(M.k, -1), M.osc));
  return W && { M, W };
}
function inv(A) {
  const s = split(A);
  if (!s) return null;
  const S = series(s.W, [1, -1, 1, -1, 1]);
  return S && mul(mono(1 / s.M.c, kscale(s.M.k, -1), s.M.osc), S);
}
const div = (A, B) => mul(A, inv(B));
function pow(A, k) {
  if (!A) return null;
  if (Number.isInteger(k) && k >= 0 && k <= 8) { let r = C(1); for (let i = 0; i < k; i++) r = mul(r, A); return r; }
  if (Number.isInteger(k) && k < 0 && k >= -8) return inv(pow(A, -k));
  const s = split(A);
  if (!s) return null;
  const { M, W } = s;
  if (M.osc) return null;                    // (−1)ⁿ to a fractional power
  if (M.c < 0) return null;
  const binom = [1];
  for (let j = 1; j < 5; j++) binom.push(binom[j - 1] * (k - j + 1) / j);
  const S = series(W, binom);
  return S && mul(mono(Math.pow(M.c, k), kscale(M.k, k)), S);
}
// Split into growing, constant and vanishing parts.
function parts(A) {
  const P = [], Z = [], N = [];
  for (const t of A.terms) (kcmp(t.k, K0) > 0 ? P : kcmp(t.k, K0) === 0 ? Z : N).push(t);
  return { P, Z, N: { terms: N, bound: A.bound } };
}
function expE(A) {
  if (!A) return null;
  if (A.bound && kcmp(A.bound, K0) >= 0) return null;
  const { P, Z, N } = parts(A);
  if (Z.some(t => t.osc) || P.some(t => t.osc)) return null;
  let key = K0.slice();
  for (const t of P) {
    // e^(c·t·ln t), e^(c·t), e^(c·ln t) = t^c; other growth (e^√t) is beyond these terms.
    if (kcmp(t.k, [0, 0, 1, 1, 0]) === 0) key[0] += t.c;
    else if (kcmp(t.k, [0, 0, 1, 0, 0]) === 0) key[1] += t.c;
    else if (kcmp(t.k, [0, 0, 0, 1, 0]) === 0) key[2] += t.c;
    else if (kcmp(t.k, [0, 0, 0, 0, 1]) === 0) key[3] += t.c;
    else return null;
  }
  const c0 = Z.reduce((s, t) => s + t.c, 0);
  const S = series(N, [1, 1, 1 / 2, 1 / 6, 1 / 24]);
  return S && mul(mono(Math.exp(c0), key), S);
}
function lnE(A) {
  const s = split(A);
  if (!s) return null;
  const { M, W } = s;
  if (M.osc || M.c <= 0) return null;
  const [f, r, p, q, s5] = M.k;
  if (Math.abs(s5) > 1e-12) return null;      // ln ln ln t is beyond these terms
  let out = C(Math.log(M.c));
  if (f) out = add(out, mono(f, [0, 0, 1, 1, 0]));
  if (r) out = add(out, mono(r, [0, 0, 1, 0, 0]));
  if (p) out = add(out, mono(p, [0, 0, 0, 1, 0]));
  if (q) out = add(out, mono(q, [0, 0, 0, 0, 1]));
  const S = series(W, [0, 1, -1 / 2, 1 / 3, -1 / 4]);
  return S && add(out, S);
}
// sin and cos. A linear argument c·t + d gives sin(ct + d): mean zero when t runs over the whole
// numbers (unless c is a multiple of π, where it is constant or (−1)ⁿ).
function trigE(A, which, ctx) {
  if (!A) return null;
  if (A.bound && kcmp(A.bound, K0) >= 0) return null;
  const { P, Z, N } = parts(A);
  if (Z.some(t => t.osc)) return null;
  const d = Z.reduce((s, t) => s + t.c, 0);
  const cosN = series(N, [1, 0, -1 / 2, 0, 1 / 24]), sinN = series(N, [0, 1, 0, -1 / 6, 0]);
  if (!cosN || !sinN) return null;
  if (!P.length) {
    const [s0, c0] = [Math.sin(d), Math.cos(d)];
    return which === 'sin' ? add(scale(cosN, s0), scale(sinN, c0)) : sub(scale(cosN, c0), scale(sinN, s0));
  }
  if (P.some(t => t.osc)) return null;
  if (P.length === 1 && kcmp(P[0].k, [0, 0, 1, 0, 0]) === 0) {
    const w = P[0].c;
    // On the whole numbers, w ≡ 0 or π (mod 2π) makes sin(wn + d) constant or alternating.
    if (ctx.integer) {
      const m = ((w % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI);
      if (Math.abs(m) < 1e-9 || Math.abs(m - 2 * Math.PI) < 1e-9) return trigE(add(C(d), N), which, ctx);
      if (Math.abs(m - Math.PI) < 1e-9) return mul(mono(1, K0.slice(), { kind: 'alt' }), trigE(add(C(d), N), which, ctx));
    }
    const wt = Math.abs(w - 1) < 1e-12 ? 't' : `${+w.toPrecision(6)}t`;
    const id = (f, phase) => `${f}(${wt}${phase ? ' + ' + +phase.toPrecision(6) : ''})`;
    const S = mono(1, K0.slice(), { kind: 'trig', id: id('sin', d) }), Co = mono(1, K0.slice(), { kind: 'trig', id: id('cos', d) });
    // sin(θ + N) = sin θ cos N + cos θ sin N;  cos(θ + N) = cos θ cos N − sin θ sin N
    return which === 'sin' ? add(mul(S, cosN), mul(Co, sinN)) : sub(mul(Co, cosN), mul(S, sinN));
  }
  // Any other growing argument (sin(n²), sin(√n), sin(ln n)): a bounded oscillation, nothing more.
  return mono(1, K0.slice(), { kind: 'osc', id: `${which}(…)` });
}
function absE(A) {
  if (!A) return null;
  if (!A.terms.length) return A.bound ? null : ZERO;
  const M = A.terms[0];
  if (!M.osc) return M.c > 0 ? A : neg(A);
  if (A.terms.every(t => t.osc && t.osc.kind === 'alt')) {
    const B = { terms: A.terms.map(t => ({ ...t, osc: null })), bound: A.bound };
    return absE(B);
  }
  // |oscillation|: bounded by the leading magnitude, no finer structure.
  return { terms: [{ c: Math.abs(M.c), k: M.k, osc: { kind: 'osc', id: 'abs' } }], bound: A.bound };
}
function atanE(A) {
  if (!A || !A.terms.length) return A && !A.bound ? ZERO : null;
  const M = A.terms[0];
  if (M.osc) return null;
  if (kcmp(M.k, K0) > 0) return add(C(Math.sign(M.c) * Math.PI / 2), neg(series(inv(A), [0, 1, 0, -1 / 3, 0])));
  if (kcmp(M.k, K0) < 0) return series(A, [0, 1, 0, -1 / 3, 0]);
  return null;
}
// x! = Γ(x + 1) for x → ∞, by Stirling: exp(x ln x − x + ½ ln x + ½ ln 2π + 1/(12x)).
function factE(A) {
  if (!A || !A.terms.length || A.terms[0].osc || kcmp(A.terms[0].k, K0) <= 0 || A.terms[0].c <= 0) return null;
  const L = lnE(A);
  if (!L) return null;
  return expE(add(add(add(sub(mul(A, L), A), scale(L, 0.5)), C(0.5 * Math.log(2 * Math.PI))), scale(inv(A), 1 / 12)));
}

/* ---------- formulas to expansions ---------- */
// ctx: { vars: Map(name → expansion), env, integer }
function ex(node, ctx, depth = 0) {
  if (!node || depth > 40) return null;
  switch (node.type) {
    case 'num': return C(node.v);
    case 'value': return typeof node.v === 'number' ? C(node.v) : null;
    case 'id': {
      if (ctx.vars.has(node.name)) return ctx.vars.get(node.name);
      let v;
      try { v = ctx.env[node.name]; } catch (e) { return null; }
      if (typeof v === 'number') return C(v);
      if (v && v.__exact) return C(+v);
      return null;
    }
    case 'bin': {
      const a = ex(node.a, ctx, depth + 1);
      if (node.op === '^') {
        // A constant exponent, a constant base, or e^(b·ln a) in general.
        const b = ex(node.b, ctx, depth + 1);
        if (!a || !b) return null;
        const bc = constOf(b), ac = constOf(a);
        if (bc !== null) return pow(a, bc);
        if (ac !== null) {
          if (ac > 0) return expE(scale(b, Math.log(ac)));
          if (ac === -1 || ac < 0) {
            // (−1)ⁿ and (−c)ⁿ for an integer variable exponent n + k
            if (!ctx.integer) return null;
            const lin = linearInt(b);
            if (lin === null) return null;
            const sign = lin.k % 2 === 0 ? 1 : -1;
            const base = ac === -1 ? C(1) : expE(scale(b, Math.log(-ac)));
            return base && mul(mono(sign, K0.slice(), { kind: 'alt' }), base);
          }
          return null;
        }
        return expE(mul(b, lnE(a)));
      }
      const b = ex(node.b, ctx, depth + 1);
      if (!a || !b) return null;
      switch (node.op) {
        case '+': return add(a, b);
        case '-': return sub(a, b);
        case '*': return mul(a, b);
        case '/': return div(a, b);
      }
      return null;
    }
    case 'un':
      if (node.op === 'neg') return neg(ex(node.a, ctx, depth + 1));
      if (node.op === 'fact') return factE(ex(node.a, ctx, depth + 1));
      return null;
    case 'abs': return absE(ex(node.e, ctx, depth + 1));
    case 'if': {
      const branch = decideCond(node.c, ctx, depth);
      if (branch === null) return null;
      return ex(branch ? node.a : node.b, ctx, depth + 1);
    }
    case 'call': {
      if (node.f.type !== 'id') return null;
      const name = node.f.name;
      if (!ctx.vars.has(name)) {
        const args = node.args.map(a => ex(a, ctx, depth + 1));
        if (args.some(a => !a)) return null;
        const [u] = args;
        switch (name) {
          case 'sin': case 'cos': if (args.length === 1) return trigE(u, name, ctx); break;
          case 'tan': if (args.length === 1) return div(trigE(u, 'sin', ctx), trigE(u, 'cos', ctx)); break;
          case 'exp': if (args.length === 1) return expE(u); break;
          case 'ln': if (args.length === 1) return lnE(u); break;
          case 'log': if (args.length === 1) return scale(lnE(u), 1 / Math.LN10); if (args.length === 2) { const b = constOf(args[1]); return b > 0 && b !== 1 ? scale(lnE(u), 1 / Math.log(b)) : null; } break;
          case 'sqrt': if (args.length === 1) return pow(u, 0.5); break;
          case 'abs': if (args.length === 1) return absE(u); break;
          case 'atan': if (args.length === 1) return atanE(u); break;
          case 'floor': case 'ceil': {
            // ⌊u⌋ = u − frac(u): a bounded oscillation, for growing u.
            if (args.length === 1 && u.terms.length && !u.terms[0].osc && kcmp(u.terms[0].k, K0) > 0) return add(u, mono(1, K0.slice(), { kind: 'osc', id: 'frac' }));
            return null;
          }
        }
      }
      // A function the notebook defined: its formula, with the arguments substituted.
      let f;
      try { f = ctx.vars.has(name) ? null : ctx.env[name]; } catch (e) { f = null; }
      const src = formulaOf(f);
      if (!src || src.params.length !== node.args.length) return null;
      const vars = new Map(ctx.vars);
      for (let i = 0; i < src.params.length; i++) {
        const a = ex(node.args[i], ctx, depth + 1);
        if (!a) return null;
        vars.set(src.params[i], a);
      }
      return ex(src.body, { ...ctx, vars, env: src.env }, depth + 1);
    }
  }
  return null;
}
// The constant value of an exact constant expansion, or null.
const constOf = E => (E && E.bound === null && E.terms.length <= 1 && (!E.terms.length || (kcmp(E.terms[0].k, K0) === 0 && !E.terms[0].osc)) ? (E.terms.length ? E.terms[0].c : 0) : null);
// For an exponent: exactly n + k with k a whole number?
function linearInt(E) {
  if (!E || E.bound !== null) return null;
  let one = false, k = 0;
  for (const t of E.terms) {
    if (t.osc) return null;
    if (kcmp(t.k, [0, 0, 1, 0, 0]) === 0 && Math.abs(t.c - 1) < 1e-12) one = true;
    else if (kcmp(t.k, K0) === 0 && Number.isInteger(t.c)) k = t.c;
    else return null;
  }
  return one ? { k } : null;
}
// The branch an "if" takes eventually: compares both sides' expansions.
function decideCond(c, ctx, depth) {
  if (c.type === 'cmp' && c.args.length === 2) {
    const D = sub(ex(c.args[0], ctx, depth + 1), ex(c.args[1], ctx, depth + 1));
    if (!D) return null;
    const sgn = !D.terms.length ? (D.bound ? null : 0) : D.terms[0].osc ? null : Math.sign(D.terms[0].c);
    if (sgn === null) return null;
    switch (c.ops[0]) {
      case '=': return sgn === 0;
      case '!=': return sgn !== 0;
      case '<': return sgn < 0; case '<=': return sgn <= 0;
      case '>': return sgn > 0; case '>=': return sgn >= 0;
    }
  }
  if (c.type === 'bin' && (c.op === 'and' || c.op === 'or')) {
    const a = decideCond(c.a, ctx, depth), b = decideCond(c.b, ctx, depth);
    if (a === null || b === null) return null;
    return c.op === 'and' ? a && b : a || b;
  }
  if (c.type === 'un' && c.op === 'not') { const a = decideCond(c.a, ctx, depth); return a === null ? null : !a; }
  return null;
}

// The formula of a function: a notebook lambda, a one-line definition, or an expr string.
function formulaOf(f) {
  if (typeof f !== 'function') return null;
  if (f.__lambda) return f.__lambda;
  const d = MV.DEFS && MV.DEFS.get(f);
  if (d && !d.fromLibrary) return { params: d.params, body: d.body, env: d.env };
  if (typeof f.expr === 'string') {
    if (!f.__exprAst) { try { f.__exprAst = new MV.Parser(MV.tokenize(f.expr)).expr(); } catch (e) { f.__exprAst = null; } }
    return f.__exprAst && { params: [f.exprVar || 'n'], body: f.__exprAst, env: MV.EXPR_ENV || {} };
  }
  return null;
}

/* ---------- verdicts ---------- */
const order = t => kcmp(t.k, K0);
// The limit as t → ∞: { kind: 'finite', v } | { kind: 'inf', sign } | { kind: 'none' } | null.
function limitOf(E) {
  if (!E) return null;
  if (!E.terms.length) return E.bound && kcmp(E.bound, K0) >= 0 ? null : { kind: 'finite', v: 0 };
  const M = E.terms[0];
  if (order(M) < 0) return { kind: 'finite', v: 0 };
  if (order(M) > 0) return M.osc ? { kind: 'none', why: 'oscillates with growing size' } : { kind: 'inf', sign: Math.sign(M.c) };
  // Order 0: a constant plus perhaps oscillations of size 1.
  const zero = E.terms.filter(t => order(t) === 0);
  if (zero.some(t => t.osc)) return { kind: 'none', why: 'keeps oscillating' };
  if (E.bound && kcmp(E.bound, K0) >= 0) return null;
  return { kind: 'finite', v: zero.reduce((s, t) => s + t.c, 0) };
}
// Does Σ (the terms) converge? { converges, absolutely, why } or null.
function seriesOf(E) {
  if (!E) return null;
  const L = limitOf(E);
  if (!L) return null;
  if (!(L.kind === 'finite' && Math.abs(L.v) < 1e-300)) return { converges: false, absolutely: false, why: 'the terms don\'t tend to 0' };
  const verdictOf = k => {
    const [f, r, p, q, s] = k;
    if (Math.abs(f) > 1e-9) return { ok: f < 0, how: f < 0 ? 'a factorial in the denominator (ratio test)' : 'factorial growth' };
    if (Math.abs(r) > 1e-9) return { ok: r < 0, how: r < 0 ? `geometric decay like ${+Math.exp(r).toPrecision(4)}ⁿ (root test)` : 'exponential growth' };
    if (Math.abs(p + 1) > 1e-9) return { ok: p < -1, how: `comparison with Σ 1/n^${+(-p).toPrecision(6)} (a p-series with p ${p < -1 ? '>' : '≤'} 1)` };
    if (Math.abs(q + 1) > 1e-9) return { ok: q < -1, how: q === 0 ? 'comparison with the harmonic series' : `comparison with Σ 1/(n (ln n)^${+(-q).toPrecision(6)}) (Bertrand: converges exactly when the power of ln n exceeds 1)` };
    if (Math.abs(s) < 1e-9) return { ok: false, how: 'comparison with Σ 1/(n ln n), which diverges (Bertrand: the power of ln n must exceed 1)' };
    return { ok: s < -1, how: `comparison with Σ 1/(n ln n (ln ln n)^${+(-s).toPrecision(6)}) (Bertrand again: converges exactly when the power of ln ln n exceeds 1)` };
  };
  // Omitted terms must be summable for the verdict to stand.
  if (E.bound && !verdictOf(E.bound).ok) return null;
  const plain = E.terms.filter(t => !t.osc), oscs = E.terms.filter(t => t.osc);
  const parts = [];
  if (plain.length) {
    const v = verdictOf(plain[0].k);
    parts.push({ conv: v.ok, abs: v.ok, why: `the non-oscillating part behaves like ${describeTerm(plain[0])}: ${v.how}` });
  }
  for (const t of oscs) {
    const v = verdictOf(t.k);
    if (v.ok) { parts.push({ conv: true, abs: true, why: `${describeTerm(t)} converges absolutely (${v.how})` }); continue; }
    if (t.osc.kind === 'osc') return null;
    if (order(t) < 0) parts.push({ conv: true, abs: false, why: `${describeTerm(t)} converges by the ${t.osc.kind === 'alt' ? 'alternating series (Leibniz)' : 'Dirichlet'} test, but not absolutely` });
    else return null;
  }
  const bad = parts.filter(x => !x.conv);
  if (bad.length > 1) return null;          // two divergent parts might cancel
  if (bad.length === 1) return { converges: false, absolutely: false, why: bad[0].why };
  return { converges: true, absolutely: parts.every(x => x.abs), why: parts.map(x => x.why).join('; ') };
}
// The sign of E eventually: 1, −1, 0 (identically zero), or null (oscillates, or unknown).
function signOf(E) {
  if (!E) return null;
  if (!E.terms.length) return E.bound ? null : 0;
  return E.terms[0].osc ? null : Math.sign(E.terms[0].c);
}

/* ---------- readable terms ---------- */
const sup = s => String(s).replace(/[-0-9.]/g, ch => ({ '-': '⁻', '.': '·' })[ch] || '⁰¹²³⁴⁵⁶⁷⁸⁹'[+ch]);
function describeTerm(t, v = 'n') {
  const [f, r, p, q, s5] = t.k;
  const parts = [];
  const num = x => +x.toPrecision(4);
  // e^(f·n·ln n) = n^(f·n)
  if (f) parts.push(f === 1 ? `${v}^${v}` : `${v}^(${num(f)}${v})`.replace('-', '−'));
  if (r) parts.push(`${num(Math.exp(r))}^${v}`);
  if (p) parts.push(p === 1 ? v : `${v}${sup(num(p))}`);
  if (q) parts.push(q === 1 ? `ln ${v}` : `(ln ${v})${sup(num(q))}`);
  if (s5) parts.push(s5 === 1 ? `ln ln ${v}` : `(ln ln ${v})${sup(num(s5))}`);
  const c = num(t.c);
  let s = parts.length ? (c === 1 ? '' : c === -1 ? '−' : String(c).replace('-', '−') + '·') + parts.join('·') : String(c).replace('-', '−');
  if (t.osc) s += t.osc.kind === 'alt' ? `·(−1)^${v}` : t.osc.kind === 'trig' ? `·${t.osc.id.replace(/t/g, v)}` : '·(an oscillation)';
  return s;
}

/* ---------- entry points ---------- */
// As n → ∞, for a sequence given by a formula.
function seq(fn) {
  const src = formulaOf(fn);
  if (!src || src.params.length !== 1) return null;
  const vars = new Map([[src.params[0], mono(1, [0, 0, 1, 0, 0])]]);
  try { return ex(src.body, { vars, env: src.env, integer: true }); } catch (e) { return null; }
}
// Near the point a, from the right (side 1) or left (−1): f(a + side/t) as t → ∞.
function germ(fn, a, side, body = null) {
  const src = formulaOf(fn);
  if (!src || src.params.length !== 1) return null;
  const x = add(C(+a), mono(side, [0, 0, -1, 0, 0]));
  const vars = new Map([[src.params[0], x]]);
  try { return ex(body || src.body, { vars, env: src.env, integer: false }); } catch (e) { return null; }
}
const fmtL = L => (L.kind === 'finite' ? MV.fmt(+L.v.toPrecision(12)) : L.kind === 'inf' ? (L.sign > 0 ? '∞' : '−∞') : 'no limit');

// Symbolic derivative of a formula in x (for continuity of the derivative).
const NUM = v => ({ type: 'num', v });
const B = (op, a, b) => ({ type: 'bin', op, a, b });
const CALL = (name, ...args) => ({ type: 'call', f: { type: 'id', name }, args });
function free(node, x) { return MV.freeNames(node).has(x); }
function d(node, x) {
  if (!node) return null;
  if (!free(node, x)) return NUM(0);
  switch (node.type) {
    case 'id': return node.name === x ? NUM(1) : NUM(0);
    case 'bin': {
      const { a, b } = node, da = d(a, x), db = d(b, x);
      if (!da || !db) return null;
      switch (node.op) {
        case '+': case '-': return B(node.op, da, db);
        case '*': return B('+', B('*', da, b), B('*', a, db));
        case '/': return B('/', B('-', B('*', da, b), B('*', a, db)), B('^', b, NUM(2)));
        case '^':
          if (!free(b, x)) return B('*', B('*', b, B('^', a, B('-', b, NUM(1)))), da);
          if (!free(a, x)) return B('*', B('*', CALL('ln', a), node), db);
          return B('*', node, B('+', B('*', db, CALL('ln', a)), B('/', B('*', b, da), a)));
      }
      return null;
    }
    case 'un': return node.op === 'neg' ? { type: 'un', op: 'neg', a: d(node.a, x) } : null;
    case 'abs': { const du = d(node.e, x); return du && B('*', B('/', node.e, node), du); }
    case 'if': { const da = d(node.a, x), db = d(node.b, x); return da && db ? { type: 'if', c: node.c, a: da, b: db } : null; }
    case 'call': {
      if (node.f.type !== 'id' || node.args.length !== 1) return null;
      const u = node.args[0], du = d(u, x);
      if (!du) return null;
      const chain = g => B('*', g, du);
      switch (node.f.name) {
        case 'sin': return chain(CALL('cos', u));
        case 'cos': return chain({ type: 'un', op: 'neg', a: CALL('sin', u) });
        case 'exp': return chain(node);
        case 'ln': return B('/', du, u);
        case 'log': return B('/', du, B('*', u, NUM(Math.LN10)));
        case 'sqrt': return B('/', du, B('*', NUM(2), node));
        case 'tan': return B('/', du, B('^', CALL('cos', u), NUM(2)));
        case 'atan': return B('/', du, B('+', NUM(1), B('^', u, NUM(2))));
        case 'abs': return chain(B('/', u, CALL('abs', u)));
      }
      return null;
    }
  }
  return null;
}

/* Local questions about f at a: each returns { v: true/false, why } or null (don't know). */
function sides(fn, a, body) {
  const r = germ(fn, a, 1, body), l = germ(fn, a, -1, body);
  return r && l ? { r, l } : null;
}
function continuousAt(fn, a) {
  let fa;
  try { fa = +fn(a); } catch (e) { return null; }
  if (!Number.isFinite(fa)) return null;
  const S = sides(fn, a);
  if (!S) return null;
  const Lr = limitOf(S.r), Ll = limitOf(S.l);
  if (!Lr || !Ll) return null;
  const close = L => L.kind === 'finite' && Math.abs(L.v - fa) <= 1e-9 * Math.max(1, Math.abs(fa));
  const ok = close(Lr) && close(Ll);
  return { v: ok, why: ok ? `f(x) → ${fmtL(Lr)} = f(${MV.fmt(a)}) from both sides` : `from the right f(x) → ${fmtL(Lr)}, from the left → ${fmtL(Ll)}, while f(${MV.fmt(a)}) = ${MV.fmt(+fa.toPrecision(12))}` };
}
function derivativeAt(fn, a) {
  let fa;
  try { fa = +fn(a); } catch (e) { return null; }
  if (!Number.isFinite(fa)) return null;
  const S = sides(fn, a);
  if (!S) return null;
  // (f(a + h) − f(a))/h with h = ±1/t.
  const q = side => mul(sub(side === 1 ? S.r : S.l, C(fa)), mono(side, [0, 0, 1, 0, 0]));
  const Lr = limitOf(q(1)), Ll = limitOf(q(-1));
  if (!Lr || !Ll) return null;
  const ok = Lr.kind === 'finite' && Ll.kind === 'finite' && Math.abs(Lr.v - Ll.v) <= 1e-9 * Math.max(1, Math.abs(Lr.v));
  return { v: ok, L: ok ? Lr.v : null, why: ok ? `the difference quotient tends to ${fmtL(Lr)} from both sides` : `the difference quotient tends to ${fmtL(Lr)} from the right and ${fmtL(Ll)} from the left` };
}
function c1At(fn, a) {
  const D = derivativeAt(fn, a);
  if (!D) return null;
  if (!D.v) return { v: false, why: `it is not differentiable there: ${D.why}` };
  const src = formulaOf(fn);
  const dbody = src && d(src.body, src.params[0]);
  if (!dbody) return null;
  const S = sides(fn, a, dbody);
  if (!S) return null;
  const Lr = limitOf(S.r), Ll = limitOf(S.l);
  if (!Lr || !Ll) return null;
  const close = L => L.kind === 'finite' && Math.abs(L.v - D.L) <= 1e-9 * Math.max(1, Math.abs(D.L));
  const ok = close(Lr) && close(Ll);
  return { v: ok, why: ok ? `f′(${MV.fmt(a)}) = ${fmtL({ kind: 'finite', v: D.L })} and f′(x) tends to it` : `f′(${MV.fmt(a)}) = ${fmtL({ kind: 'finite', v: D.L })}, but near it f′(x) → ${fmtL(Lr)} (right) and ${fmtL(Ll)} (left)` };
}

MV.ASYM = {
  seq, germ, limitOf, seriesOf, signOf, describeTerm, formulaOf, continuousAt, derivativeAt, c1At, sub, d, fmtL,
  // Σ fn(n): { converges, absolutely, why } or null.
  series: fn => seriesOf(seq(fn)),
  seqLimit: fn => limitOf(seq(fn)),
  // a(n) ≤ b(n) for all large n? true / false / null.
  eventuallyLe: (a, b) => { const s = signOf(sub(seq(b), seq(a))); return s === null ? null : s >= 0; },
  growth: fn => { const E = seq(fn); return E && E.terms.length ? describeTerm(E.terms[0]) : E && !E.bound ? '0' : null; },
};
})(typeof window !== 'undefined' ? window : globalThis);
