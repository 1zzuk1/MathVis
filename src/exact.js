/* Theorem Sketchpad — exact reals that know what kind of number they are.

   Floats are all rationals in disguise, so a float can't say whether the number it stands for is
   rational. That decides the Dirichlet and Thomae functions, membership in ℚ and in the Cantor
   set, and many classic counterexamples. An ExactReal is one of
     Q:  a rational p/q, exactly (BigInt numerator and denominator);
     S:  a + b·√r with a, b rational and r a square-free whole number > 1 (irrational when b ≠ 0);
     T:  a known irrational given by an approximation and a label (π/4, a Cantor-set point with
         known ternary digits, …), optionally with facts about it (inCantor: true).
   Arithmetic stays exact where the kind of the result is known (ℚ with ℚ, ℚ(√r) with itself, an
   irrational T plus or times a nonzero rational), and otherwise falls back to a plain float, whose
   kind is unknown. valueOf() gives the float, so code that only does numerics never notices.

   Claims that depend on the kind of a number (they use ℚ, is_rational, the Dirichlet function, …)
   are sampled with exact values: half rationals, half irrationals. All others use plain floats. */
'use strict';
(function (global) {
const MV = global.MV;

/* ---------- rationals ---------- */
const babs = a => (a < 0n ? -a : a);
const bgcd = (a, b) => { a = babs(a); b = babs(b); while (b) [a, b] = [b, a % b]; return a; };
const qn = (n, d = 1n) => {
  if (d === 0n) return null;
  if (d < 0n) { n = -n; d = -d; }
  const g = bgcd(n, d) || 1n;
  return { n: n / g, d: d / g };
};
const qadd = (x, y) => qn(x.n * y.d + y.n * x.d, x.d * y.d);
const qsub = (x, y) => qn(x.n * y.d - y.n * x.d, x.d * y.d);
const qmul = (x, y) => qn(x.n * y.n, x.d * y.d);
const qdiv = (x, y) => (y.n === 0n ? null : qn(x.n * y.d, x.d * y.n));
const qcmp = (x, y) => { const t = x.n * y.d - y.n * x.d; return t < 0n ? -1 : t > 0n ? 1 : 0; };
const qnum = x => Number(x.n) / Number(x.d);
const qzero = x => x.n === 0n;
const BIG = 2n ** 256n;
const tooBig = x => babs(x.n) > BIG || x.d > BIG;

/* A plain number as a rational, when it plainly is one: a whole number, or a short decimal such as a
   literal 0.25 or 1e-3. Results of floating-point computations (√2 ≈ 1.4142135623730951) are not. */
function numToQ(x) {
  if (typeof x !== 'number' || !Number.isFinite(x)) return null;
  if (Number.isInteger(x)) return Math.abs(x) <= Number.MAX_SAFE_INTEGER ? qn(BigInt(x)) : null;
  const s = String(x);
  const m = /^(-?)(\d+)(?:\.(\d+))?(?:e([+-]\d+))?$/.exec(s);
  if (!m) return null;
  const digits = (m[2] + (m[3] || '')).replace(/^0+/, '');
  if (digits.length > 12) return null;
  const exp = (m[4] ? +m[4] : 0) - (m[3] || '').length;
  let n = BigInt(m[2] + (m[3] || ''));
  if (m[1]) n = -n;
  return exp >= 0 ? qn(n * 10n ** BigInt(exp)) : qn(n, 10n ** BigInt(-exp));
}

/* ---------- the value type ---------- */
const proto = {
  __exact: true,
  valueOf() { return this.approx; },
  toString() { return fmtExact(this); },
};
const mk = (o, approx) => Object.assign(Object.create(proto), o, { approx });
const Q = q => (q === null ? NaN : tooBig(q) ? qnum(q) : mk({ kind: 'Q', q }, qnum(q)));
// a + b√r; b = 0 gives a rational.
const S = (a, b, r) => {
  if (a === null || b === null) return NaN;
  if (qzero(b)) return Q(a);
  if (tooBig(a) || tooBig(b)) return qnum(a) + qnum(b) * Math.sqrt(r);
  return mk({ kind: 'S', a, b, r }, qnum(a) + qnum(b) * Math.sqrt(r));
};
const T = (approx, label, facts = {}) => mk({ kind: 'T', label, facts }, approx);
const isExact = v => !!(v && v.__exact);

// The kind of a value: 'rational', 'irrational', or null when unknown.
function kindOf(v) {
  if (isExact(v)) return v.kind === 'Q' ? 'rational' : 'irrational';
  if (typeof v === 'number') return numToQ(v) ? 'rational' : null;
  return null;
}
// An exact value from a plain number, when the number is plainly rational.
const lift = v => (isExact(v) ? v : typeof v === 'number' ? (numToQ(v) ? Q(numToQ(v)) : null) : null);
const asS = v => (v.kind === 'Q' ? { a: v.q, b: qn(0n), r: 0 } : v);

function squareFree(n) {
  // n = k² · r with r square-free; returns [k, r] (n a positive whole number below 10⁹).
  let k = 1, r = n;
  for (let p = 2; p * p <= r; p++) while (r % (p * p) === 0) { r /= p * p; k *= p; }
  return [k, r];
}

/* ---------- arithmetic ---------- */
function arith(op, a, b) {
  const A = lift(a), B = b === undefined ? undefined : lift(b);
  const plain = () => {
    const x = +a, y = b === undefined ? undefined : +b;
    switch (op) {
      case '+': return x + y; case '-': return x - y; case '*': return x * y; case '/': return x / y;
      case '^': return Math.pow(x, y); case 'mod': return ((x % y) + y) % y;
      case 'neg': return -x; case 'abs': return Math.abs(x);
    }
    return NaN;
  };
  if (!A || (b !== undefined && !B)) return plain();
  if (op === 'neg') return A.kind === 'Q' ? Q(qn(-A.q.n, A.q.d)) : A.kind === 'S' ? S(qn(-A.a.n, A.a.d), qn(-A.b.n, A.b.d), A.r) : T(-A.approx, `−${A.label}`);
  if (op === 'abs') return +A < 0 ? arith('neg', A) : A;
  if (A.kind === 'Q' && B.kind === 'Q') {
    switch (op) {
      case '+': return Q(qadd(A.q, B.q));
      case '-': return Q(qsub(A.q, B.q));
      case '*': return Q(qmul(A.q, B.q));
      case '/': return qzero(B.q) ? NaN : Q(qdiv(A.q, B.q));
      case 'mod': {
        if (qzero(B.q)) return NaN;
        const t = qdiv(A.q, B.q), fl = t.n >= 0n ? t.n / t.d : -((-t.n + t.d - 1n) / t.d);
        return Q(qsub(A.q, qmul(B.q, qn(fl))));
      }
      case '^': {
        if (B.q.d === 1n && babs(B.q.n) <= 64n) {
          const k = Number(B.q.n);
          let r = qn(1n);
          for (let i = 0; i < Math.abs(k); i++) r = qmul(r, A.q);
          return k < 0 ? (qzero(r) ? NaN : Q(qdiv(qn(1n), r))) : Q(r);
        }
        if (B.q.n === 1n && B.q.d === 2n) return sqrt(A);
        return plain();
      }
    }
    return plain();
  }
  // ℚ(√r): numbers with the same r (or rationals) combine exactly.
  if (A.kind !== 'T' && B.kind !== 'T') {
    const x = asS(A), y = asS(B), r = x.r || y.r;
    if (x.r && y.r && x.r !== y.r) return plain();
    switch (op) {
      case '+': return S(qadd(x.a, y.a), qadd(x.b, y.b), r);
      case '-': return S(qsub(x.a, y.a), qsub(x.b, y.b), r);
      case '*': return S(qadd(qmul(x.a, y.a), qmul(qmul(x.b, y.b), qn(BigInt(r)))), qadd(qmul(x.a, y.b), qmul(x.b, y.a)), r);
      case '/': {
        // (a + b√r)/(c + d√r) = (a + b√r)(c − d√r)/(c² − d²r)
        const den = qsub(qmul(y.a, y.a), qmul(qmul(y.b, y.b), qn(BigInt(r))));
        if (qzero(den)) return NaN;
        const num = { a: qsub(qmul(x.a, y.a), qmul(qmul(x.b, y.b), qn(BigInt(r)))), b: qsub(qmul(x.b, y.a), qmul(x.a, y.b)) };
        return S(qdiv(num.a, den), qdiv(num.b, den), r);
      }
      case '^': {
        if (B.kind === 'Q' && B.q.d === 1n && babs(B.q.n) <= 32n) {
          const k = Number(B.q.n);
          let p = Q(qn(1n));
          for (let i = 0; i < Math.abs(k); i++) p = arith('*', p, A);
          return k < 0 ? arith('/', Q(qn(1n)), p) : p;
        }
        return plain();
      }
    }
    return plain();
  }
  // A known irrational with a nonzero rational stays irrational under + − · and /.
  const t = A.kind === 'T' ? A : B, o = A.kind === 'T' ? B : A;
  if (o.kind === 'Q') {
    const v = plain(), ol = fmtExact(o);
    if (op === '+') return T(v, `${t.label} + ${ol}`);
    if (op === '-') return T(v, A === t ? `${t.label} − ${ol}` : `${ol} − ${t.label}`);
    if ((op === '*' || op === '/') && !qzero(o.q)) return T(v, op === '*' ? `${ol}·${t.label}` : A === t ? `${t.label}/${ol}` : `${ol}/${t.label}`);
    if (op === '*' && qzero(o.q)) return Q(qn(0n));
  }
  return plain();
}

// √x: exact for rationals (a rational, or b√r).
function sqrt(x) {
  const X = lift(x);
  if (!X || X.kind !== 'Q') return Math.sqrt(+x);
  const { n, d } = X.q;
  if (n < 0n) return NaN;
  if (n === 0n) return X;
  // √(n/d) = √(n·d)/d
  const m = n * d;
  if (m > 10n ** 15n) return Math.sqrt(+X);
  const [k, r] = squareFree(Number(m));
  return r === 1 ? Q(qn(BigInt(k), d)) : S(qn(0n), qn(BigInt(k), d), r);
}

/* ---------- comparison ---------- */
// The sign of a + b√r, exactly.
function signS(a, b, r) {
  const sa = qcmp(a, qn(0n)), sb = qcmp(b, qn(0n));
  if (sb === 0) return sa;
  if (sa === 0 || sa === sb) return sa || sb;
  // a and b√r have opposite signs: compare a² with b²r.
  const c = qcmp(qmul(a, a), qmul(qmul(b, b), qn(BigInt(r))));
  return c === 0 ? 0 : c > 0 ? sa : sb;
}
// −1, 0, 1 when the order is known exactly; null otherwise.
function cmpExact(a, b) {
  const A = lift(a), B = lift(b);
  if (!A || !B) return null;
  if (A.kind === 'Q' && B.kind === 'Q') return qcmp(A.q, B.q);
  if (A.kind !== 'T' && B.kind !== 'T') {
    const x = asS(A), y = asS(B);
    if (x.r && y.r && x.r !== y.r) return null;
    return signS(qsub(x.a, y.a), qsub(x.b, y.b), x.r || y.r);
  }
  // A known irrational never equals a rational; its order comes from the approximation.
  if ((A.kind === 'T') !== (B.kind === 'T') && (A.kind === 'Q' || B.kind === 'Q')) return +A < +B ? -1 : 1;
  return null;
}
// Equality: exact when the kinds are known. null means "decide numerically".
function equalExact(a, b) {
  const c = cmpExact(a, b);
  if (c !== null) return c === 0;
  const ka = kindOf(a), kb = kindOf(b);
  if (ka && kb && ka !== kb) return false;
  return null;
}

/* ---------- formatting ---------- */
const qstr = q => (q.n < 0n ? '−' : '') + babs(q.n).toString() + (q.d === 1n ? '' : '/' + q.d.toString());
function fmtExact(v) {
  if (v.kind === 'Q') return qstr(v.q);
  if (v.kind === 'T') return v.label;
  // a + b√r, written as √2/2, 1 + √2, −3√5/2, 1/2 − √3
  const { a, b, r } = v;
  const absb = qn(babs(b.n), b.d);
  const rad = (absb.n === 1n ? '' : absb.n.toString()) + `√${r}` + (absb.d === 1n ? '' : '/' + absb.d.toString());
  if (qzero(a)) return (b.n < 0n ? '−' : '') + rad;
  return `${qstr(a)} ${b.n < 0n ? '−' : '+'} ${rad}`;
}

/* ---------- facts about numbers ---------- */
const isRational = v => {
  const k = kindOf(v);
  if (k) return k === 'rational';
  // A float of unknown origin: rational if it is a simple fraction, which is a guess, so say so.
  MV.INEXACT = true;
  return smallDen(+v) > 0;
};
// The denominator of a rational in lowest terms (Thomae's function); 0 for an irrational.
const denominator = v => {
  const X = lift(v);
  if (X) return X.kind === 'Q' ? Number(X.q.d) : 0;
  MV.INEXACT = true;
  return smallDen(+v);
};
// q when x is p/q with q ≤ 1000 to rounding; else 0 (a guess about a float of unknown origin).
function smallDen(x) {
  if (!Number.isFinite(x)) return 0;
  let h0 = 1, h1 = 0, k0 = 0, k1 = 1, y = Math.abs(x);
  for (let i = 0; i < 20; i++) {
    const t = Math.floor(y);
    [h0, h1] = [t * h0 + h1, h0];
    [k0, k1] = [t * k0 + k1, k0];
    if (k0 > 1000) return 0;
    if (Math.abs(Math.abs(x) - h0 / k0) <= 1e-12 * Math.max(1, Math.abs(x))) return k0;
    if (y - t < 1e-14) break;
    y = 1 / (y - t);
  }
  return 0;
}

/* Membership in the Cantor set: exact for rationals (their ternary expansion is eventually
   periodic) and for points that carry the fact; otherwise from 40 ternary digits (marked inexact). */
function inCantor(v) {
  if (isExact(v) && v.kind === 'T' && v.facts && typeof v.facts.inCantor === 'boolean') return v.facts.inCantor;
  const X = lift(v);
  if (X && X.kind === 'Q') {
    let x = X.q;
    if (qcmp(x, qn(0n)) < 0 || qcmp(x, qn(1n)) > 0) return false;
    const seen = new Set();
    const third = qn(1n, 3n), twoThirds = qn(2n, 3n);
    for (let i = 0; i < 10000; i++) {
      const key = x.n + '/' + x.d;
      if (seen.has(key)) return true;
      seen.add(key);
      if (qcmp(x, third) > 0 && qcmp(x, twoThirds) < 0) return false;
      x = qcmp(x, third) <= 0 ? qmul(x, qn(3n)) : qsub(qmul(x, qn(3n)), qn(2n));
    }
    MV.INEXACT = true;
    return true;
  }
  MV.INEXACT = true;
  let y = +v;
  if (!(y >= 0 && y <= 1)) return false;
  for (let k = 0; k < 40; k++) {
    if (y > 1 / 3 && y < 2 / 3) return false;
    y = y <= 1 / 3 ? 3 * y : 3 * y - 2;
  }
  return true;
}
// A point of the Cantor set with ternary digits 0 and 2 chosen by the bits of a seed: irrational
// unless the digits repeat, which these (from an aperiodic rule) don't.
function cantorPoint(seed, lo = 0, w = 1) {
  let x = 0, p = 1, label = '0.';
  for (let k = 1; k <= 45; k++) {
    // Thue–Morse-like aperiodic digits, varied by the seed.
    const bit = (popcount(k + seed * 7) + (k % (seed + 2) === 0 ? 1 : 0)) % 2;
    p /= 3;
    x += 2 * bit * p;
    if (k <= 6) label += bit ? '2' : '0';
  }
  return T(lo + w * x, `${label}…₃ (in the Cantor set)`, { inCantor: true });
}
const popcount = n => { let c = 0; while (n) { c += n & 1; n >>= 1; } return c; };

/* ---------- sampling an interval with exact numbers ---------- */
// The rational nearest x from inside [lo, hi] with a small denominator.
function innerQ(x, up) {
  const q = numToQ(x);
  if (q) return q;
  const s = 1e9;
  return qn(BigInt(up ? Math.ceil(x * s) : Math.floor(x * s)), BigInt(s));
}
const PI_FRACS = [[1, 4], [1, 3], [1, 6], [3, 4], [1, 8]];
function sampleExact(lo, hi, loOpen, hiOpen, n, deep = false) {
  // Like the float sampler: points creep to 10⁻³ of the width toward the ends, or to 10⁻⁸ when "deep" (inside an ∃).
  const depths = deep ? [2n, 3n, 5n, 8n] : [2n, 3n];
  const a = innerQ(lo, true), b = innerQ(hi, false);
  if (qcmp(a, b) > 0) return [];
  const w = qsub(b, a), out = [];
  const inside = x => { const c1 = cmpExact(x, Q(a)), c2 = cmpExact(x, Q(b)); return (loOpen ? c1 > 0 : c1 >= 0) && (hiOpen ? c2 < 0 : c2 <= 0); };
  const push = x => { if (inside(x)) out.push(x); };
  const m = Math.max(2, Math.floor(n / 2));
  // Rationals: an even grid, the ends, and points creeping toward the ends.
  for (let k = 0; k < m; k++) push(Q(qadd(a, qmul(w, qn(BigInt(k), BigInt(m - 1))))));
  for (const e of depths) {
    const t = qdiv(w, qn(10n ** e));
    push(Q(qadd(a, t))); push(Q(qsub(b, t)));
  }
  for (let z = Math.ceil(lo); z <= Math.floor(hi) && z - Math.ceil(lo) < 6; z++) push(Q(qn(BigInt(z))));
  // Irrationals: one between each pair of grid points, a + (w/m)(k − 1 + √2), and a few π multiples.
  const step = qdiv(w, qn(BigInt(m)));
  for (let k = 0; k < m; k++) push(S(qadd(a, qmul(step, qn(BigInt(k - 1)))), step, 2));
  // Irrationals creeping toward the ends: a + t(√2 − 1) and b − t(√2 − 1), with t = w/10ᵉ.
  for (const e of depths) {
    const t = qdiv(w, qn(10n ** e));
    push(S(qsub(a, t), t, 2));
    push(S(qadd(b, t), qn(-t.n, t.d), 2));
  }
  for (const [p, q] of PI_FRACS) {
    const x = +Q(a) + +Q(w) * (Math.PI * p / q) / 4;
    push(T(x, `${qstr(a) === '0' ? '' : qstr(a) + ' + '}${qstr(w) === '1' ? '' : qstr(w) + '·'}${p === 1 ? '' : p}π/${4 * q}`));
  }
  // The famous irrationals themselves (√2, √2/2, π, e, …), where counterexamples like to sit.
  for (const v of simpleExactNear((lo + hi) / 2, (hi - lo) / 2 + 1e-12, 'irrational')) { if (kindOf(v) !== 'irrational') break; push(v); }
  // Remove duplicates (same value and kind).
  const seen = new Set();
  return out.filter(x => { const k = fmtExact(x); if (seen.has(k)) return false; seen.add(k); return true; });
}

/* Simple numbers near x, for the simplest counterexample. Rationals: whole numbers, then halves,
   thirds, …, nearest first. Irrationals: in order of simplicity (√2, √2/2, √2 − 1, …). The kind of
   the counterexample in hand comes first: a failure at an irrational is usually about irrationality. */
function simpleExactNear(x, radius, kind = 'rational') {
  const rats = [];
  for (const q of [1, 2, 3, 4, 5, 6, 8, 10, 12]) {
    const lo = Math.ceil((x - radius) * q), hi = Math.floor((x + radius) * q);
    const ps = [];
    for (let p = lo; p <= hi && ps.length < 40; p++) if (q === 1 || Number(bgcd(BigInt(p), BigInt(q))) === 1) ps.push(p);
    ps.sort((u, v) => Math.abs(u / q - x) - Math.abs(v / q - x));
    for (const p of ps) rats.push(Q(qn(BigInt(p), BigInt(q))));
  }
  const s = (a, b, bd, r) => S(qn(BigInt(a)), qn(BigInt(b), BigInt(bd)), r);
  const irrs = [s(0, 1, 1, 2), s(0, 1, 2, 2), s(-1, 1, 1, 2), s(0, -1, 1, 2), s(0, -1, 2, 2), s(0, 1, 1, 3), s(0, 1, 2, 3), s(1, 1, 1, 2),
    s(0, 1, 4, 2), s(0, 1, 1, 5), T(Math.PI, 'π'), T(Math.PI / 4, 'π/4'), T(Math.PI / 2, 'π/2'), T(Math.E, 'e'), s(0, 2, 1, 2), s(0, 1, 3, 2)]
    .filter(v => Math.abs(+v - x) <= radius);
  return kind === 'irrational' ? [...irrs, ...rats] : [...rats, ...irrs];
}

// Every fraction p/q in [lo, hi] with q ≤ maxQ (in lowest terms), at most cap of them: the rationals
// that show the shape of functions like Thomae's.
function farey(lo, hi, maxQ = 40, cap = 1500) {
  const out = [];
  for (let q = 1; q <= maxQ && out.length < cap; q++) {
    for (let p = Math.ceil(lo * q); p <= Math.floor(hi * q) && out.length < cap; p++) {
      if (Number(bgcd(BigInt(p), BigInt(q))) === 1) out.push(Q(qn(BigInt(p), BigInt(q))));
    }
  }
  return out;
}

Object.assign(MV, {
  EX: { farey, isExact, kindOf, lift, numToQ, Q: (p, q = 1) => Q(qn(BigInt(p), BigInt(q))), S, T, qn, arith, sqrt, cmpExact, equalExact, fmtExact, isRational, denominator, inCantor, cantorPoint, smallDen, sampleExact, simpleExactNear },
});
MV.EXACT_SAMPLING = false;
// Run fn with real intervals sampled by exact rationals and irrationals (or not).
MV.withExactSampling = (on, fn) => { const b = MV.EXACT_SAMPLING; MV.EXACT_SAMPLING = !!on; try { return fn(); } finally { MV.EXACT_SAMPLING = b; } };
})(typeof window !== 'undefined' ? window : globalThis);
