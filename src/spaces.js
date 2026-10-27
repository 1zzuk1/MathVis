/* Theorem Sketchpad — spaces: everything a variable can range over, and how each is sampled.

   Every space has  contains(v), sample(n, opts), random(), describe()  and optionally
   window() (a sampling box), boundary() (points on its edge, each marked inside or not),
   universe() (what complements are taken in), dim (coordinates per element) and scalar
   (elements are plain numbers).

   Open and closed sets differ only on their boundary, so sets locate their boundary by
   bisection with exact comparisons, then decide membership of each boundary point with the
   usual tolerant comparisons: "|p| <= 1" contains points that are within 1e-9 of the circle,
   "|p| < 1" does not. */
'use strict';
(function (global) {
const MV = global.MV;
const { MVError, fmtNum } = MV;

/* ---------- random numbers and tolerance ---------- */

function rng32(seed) {
  return function () {
    seed |= 0; seed = seed + 0x6D2B79F5 | 0;
    let t = Math.imul(seed ^ seed >>> 15, 1 | seed);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
MV.rng32 = rng32;
MV.RNG = rng32(7);
// A fresh generator from a seed: each claim samples from its own, so the same claim gets the same
// samples wherever and in whatever order it is checked (a background worker, or the page again).
MV.reseed = seed => { MV.RNG = rng32(seed >>> 0 || 7); };
const rand = () => MV.RNG();

MV.TOL = 1e-9;
MV.INEXACT = false;   // set when a result relied on sampling or numerical estimates
MV.STRESS = 0;       // 1 while checking with wilder example catalogs
function exact(fn) {
  const t = MV.TOL;
  MV.TOL = 0;
  try { return fn(); } finally { MV.TOL = t; }
}

/* ---------- numeric points: numbers or flat arrays of numbers ---------- */

const isNumArr = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');
const isPoint = v => typeof v === 'number' || isNumArr(v);
const pdim = v => typeof v === 'number' ? 1 : v.length;
const plerp = (a, b, t) => typeof a === 'number' ? a + (b - a) * t : a.map((x, i) => x + (b[i] - x) * t);
function pdist(a, b) {
  if (typeof a === 'number') return Math.abs(a - b);
  let s = 0;
  for (let i = 0; i < a.length; i++) s += (a[i] - b[i]) ** 2;
  return Math.sqrt(s);
}
const pnorm = a => typeof a === 'number' ? Math.abs(a) : Math.hypot(...a);
// Interpolation that also works for sequences and library types, through the language's own arithmetic.
function glerp(a, b, t) {
  if (isPoint(a) && isPoint(b) && typeof a === typeof b && pdim(a) === pdim(b)) return plerp(a, b, t);
  return MV.arith('+', a, MV.arith('*', t, MV.arith('-', b, a)));
}
function stride(arr, m) {
  if (arr.length <= m) return arr.slice();
  const out = [];
  for (let k = 0; k < m; k++) out.push(arr[Math.floor(k * arr.length / m)]);
  return out;
}
function shuffled(arr) {
  const a = arr.slice();
  for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(rand() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}
const SUP = n => String(n).split('').map(c => '⁰¹²³⁴⁵⁶⁷⁸⁹'[+c]).join('');
function bbox(points, scalar) {
  if (!points.length) return null;
  const d = scalar ? 1 : points[0].length;
  const box = Array.from({ length: d }, () => [Infinity, -Infinity]);
  for (const p of points) for (let i = 0; i < d; i++) {
    const x = scalar ? p : p[i];
    if (x < box[i][0]) box[i][0] = x;
    if (x > box[i][1]) box[i][1] = x;
  }
  return box;
}

/* ---------- the generic constructor ---------- */

function space(spec) {
  const d = Object.assign({ __domain: true, dim: 1 }, spec);
  if (typeof d.contains !== 'function') throw new MVError('A space needs a contains(value) function.');
  if (!d.random && !d.sample) throw new MVError('A space needs random() or sample(n) so it can be sampled.');
  if (!d.random) d.random = () => {
    const s = d.sample(64);
    if (!s.length) throw new MVError(`${d.describe()} is empty, so nothing can be picked from it.`);
    return s[Math.floor(rand() * s.length)];
  };
  if (!d.sample) d.sample = n => Array.from({ length: Math.min(n, 4000) }, () => d.random());
  if (!d.describe) d.describe = () => d.label || d.kind || 'a space';
  if (!d.boundary) d.boundary = () => [];
  if (!d.universe) d.universe = () => d;
  return d;
}

/* ---------- intervals, ℝ, ℤ, ℕ ---------- */

function interval(lo, hi, o = {}) {
  lo = +lo; hi = +hi;
  if (Number.isNaN(lo) || Number.isNaN(hi)) throw new MVError('An interval end is undefined.');
  if (lo > hi) throw new MVError(`The interval from ${fmtNum(lo)} to ${fmtNum(hi)} is empty: its lower end is larger.`);
  if (!Number.isFinite(lo) || !Number.isFinite(hi)) throw new MVError('Intervals need finite ends so they can be sampled, as in R[-100, 100].');
  const d = space({
    kind: 'interval', lo, hi, loOpen: !!o.loOpen, hiOpen: !!o.hiOpen, integer: !!o.integer,
    unbounded: o.unbounded || null, label: o.label, dim: 1, scalar: true, discrete: !!o.integer,
    contains(x) {
      // Exact reals (src/exact.js) are compared exactly with the ends.
      if (x && x.__exact) {
        if (d.integer) return Number.isInteger(+x) && MV.EX.kindOf(x) === 'rational' && +x >= d.a && +x <= d.b;
        if (d.unbounded === 'both') return Number.isFinite(+x);
        return MV.compare(d.loOpen ? '>' : '>=', x, lo) && MV.compare(d.hiOpen ? '<' : '<=', x, hi);
      }
      if (typeof x !== 'number' || !Number.isFinite(x)) return false;
      if (d.integer && !Number.isInteger(x)) return false;
      if (d.unbounded === 'both') return true;
      if (d.unbounded === 'above') return x >= lo;
      if (d.integer) return x >= d.a && x <= d.b;
      // Tolerant, like every other comparison, so [0, 1] and {x | 0 <= x <= 1} agree near their ends.
      return MV.compare(d.loOpen ? '>' : '>=', x, lo) && MV.compare(d.hiOpen ? '<' : '<=', x, hi);
    },
    random() {
      if (d.integer) return d.a + Math.floor(rand() * d.size);
      let x;
      do { x = lo + (hi - lo) * rand(); } while ((d.loOpen && x === lo) || (d.hiOpen && x === hi));
      return x;
    },
    sample: (n, opts) => sampleInterval(d, n, opts),
    bounds: () => d.integer ? [d.a, d.b] : [lo, hi],
    window: () => d.integer ? [d.a, d.b] : [lo, hi],
    boundary: () => (d.integer || d.unbounded) ? [] : [
      { p: lo, inside: !d.loOpen, inner: (lo + hi) / 2 },
      { p: hi, inside: !d.hiOpen, inner: (lo + hi) / 2 },
    ],
    universe: () => d.integer ? Zuniverse() : Runiverse(),
    describe: () => d.label || (d.integer ? `${fmtNum(d.a)}..${fmtNum(d.b)}`
      : `${d.loOpen ? '(' : '['}${fmtNum(lo)}, ${fmtNum(hi)}${d.hiOpen ? ')' : ']'}`),
  });
  if (d.integer) {
    d.a = Math.ceil(lo); if (d.loOpen && d.a === lo) d.a++;
    d.b = Math.floor(hi); if (d.hiOpen && d.b === hi) d.b--;
    d.size = d.unbounded ? Infinity : Math.max(0, d.b - d.a + 1);
    d.windowSize = Math.max(0, d.b - d.a + 1);
  }
  return d;
}
let R_U = null, Z_U = null;
const Runiverse = () => R_U || (R_U = interval(-10, 10, { unbounded: 'both', label: 'ℝ' }));
const Zuniverse = () => Z_U || (Z_U = interval(-50, 50, { integer: true, unbounded: 'both', label: 'ℤ' }));

/* opts.grid: evenly spaced points only. opts.deep: extra points creeping toward open ends,
   down to 1e-8 of the width (used when searching for a witness such as δ), or to 1e-14 while
   MV.DEEPER is set (a failing sample looked at again). */
function sampleInterval(d, n, opts = {}) {
  if (d.integer) {
    const size = d.windowSize;
    if (size <= 0) return [];
    if (size <= n) { const out = []; for (let k = d.a; k <= d.b; k++) out.push(k); return out; }
    const out = new Set();
    if (opts.grid) for (let k = 0; k < n; k++) out.add(Math.round(d.a + (d.b - d.a) * k / (n - 1)));
    else {
      // The first quarter consecutively, the rest spaced more and more widely (cubic), so
      // "eventually" claims and searches for the smallest N see the start of the range in detail.
      const q = Math.floor(n / 4), m = n - q;
      for (let k = 0; k < q; k++) out.add(d.a + k);
      if (size > 1e5) {
        // Huge ranges (like 1..10^12): logarithmic spacing, so every scale is represented.
        const span = d.b - d.a;
        for (let k = 0; k < m; k++) out.add(Math.round(d.a + Math.exp(Math.log(q) + (Math.log(span) - Math.log(q)) * k / (m - 1))));
      } else for (let k = 0; k < m; k++) out.add(Math.round(d.a + (d.b - d.a) * Math.pow(k / (m - 1), 3)));
    }
    return [...out].sort((x, y) => x - y);
  }
  const { lo, hi } = d;
  if (lo === hi) return (d.loOpen || d.hiOpen) ? [] : [lo];
  // Claims about rationality get exact rationals and irrationals instead of floats.
  if (MV.EXACT_SAMPLING && !opts.grid) {
    const xs = MV.EX.sampleExact(lo, hi, d.loOpen, d.hiOpen, Math.max(8, n), !!opts.deep);
    if (xs.length) return xs;
  }
  const w = hi - lo, out = [];
  if (opts.grid) {
    const m = Math.max(2, n + (d.loOpen ? 1 : 0) + (d.hiOpen ? 1 : 0));
    for (let k = 0; k < m; k++) {
      if ((k === 0 && d.loOpen) || (k === m - 1 && d.hiOpen)) continue;
      out.push(lo + w * k / (m - 1));
    }
    return out;
  }
  const g = opts.deep ? (MV.DEEPER ? 13 : 7) : 2;
  const m = Math.max(3, n - (d.loOpen ? g : 0) - (d.hiOpen ? g : 0) - 2);
  for (let k = 0; k < m; k++) out.push(lo + w * k / (m - 1));
  if (d.loOpen) out.shift();
  if (d.hiOpen) out.pop();
  for (let k = 1; k <= g; k++) {
    if (d.loOpen) out.push(lo + w * Math.pow(10, -(k + 1)));
    if (d.hiOpen) out.push(hi - w * Math.pow(10, -(k + 1)));
  }
  // Functions also blow up beside closed ends and beside 0 (1/x on [0, 1] with 1/0 set to 0), so
  // deep samples approach those too.
  if (opts.deep) {
    for (const e of [3, 5, 7]) {
      const t = w * Math.pow(10, -e);
      if (!d.loOpen) out.push(lo + t);
      if (!d.hiOpen) out.push(hi - t);
      if (lo < 0 && hi > 0) out.push(t, -t);
    }
  }
  for (let k = 0; k < 2; k++) out.push(lo + w * (0.05 + 0.9 * rand()));
  // Landmarks: 0 and the integers inside (when there are only a few), where textbook examples
  // put their jumps and singularities.
  const landmarks = [];
  for (let z = Math.ceil(lo); z <= Math.floor(hi) && landmarks.length <= 6; z++) landmarks.push(z);
  if (landmarks.length <= 6) { for (const z of landmarks) if (d.contains(z)) out.push(z); }
  else if (lo < 0 && hi > 0 && d.contains(0)) out.push(0);
  return [...new Set(out)].sort((a, b) => a - b);
}

/* ---------- finite sets ---------- */

function finite(values, o = {}) {
  const vals = [...values];
  const numeric = vals.every(v => typeof v === 'number');
  const d = space({
    kind: 'finite', values: vals, numeric, scalar: numeric, discrete: true, integer: numeric && vals.every(Number.isInteger),
    label: o.label, size: vals.length,
    contains: x => vals.some(v => MV.equalValues(v, x)),
    sample: n => {
      if (vals.length <= n) return vals.slice();
      const out = [];
      for (let k = 0; k < n; k++) out.push(vals[Math.round(k * (vals.length - 1) / (n - 1))]);
      return [...new Set(out)];
    },
    random: () => {
      if (!vals.length) throw new MVError('Can\'t pick an element of an empty set.');
      return vals[Math.floor(rand() * vals.length)];
    },
    bounds: () => numeric && vals.length ? [Math.min(...vals), Math.max(...vals)] : null,
    window: () => numeric && vals.length ? [Math.min(...vals), Math.max(...vals)] : null,
    describe: () => o.label || (!vals.length ? '∅' : `{${vals.slice(0, 6).map(MV.fmt).join(', ')}${vals.length > 6 ? ', …' : ''}}`),
    // A finite set of numbers or points lives in ℝ or ℝⁿ, so its complement is taken there.
    universe: () => numeric ? Runiverse()
      : vals.length && vals.every(v => isNumArr(v) && v.length === vals[0].length) ? product(new Array(vals[0].length).fill(Runiverse()))
      : d,
  });
  return d;
}

/* The part of a space inside a box: [[x0, x1]] for spaces of numbers, [[x0, x1], [y0, y1]] for the plane. */
function restrictSpace(D, box) {
  if (D.scalar) {
    const [a, b] = box[0];
    if (D.kind === 'interval') {
      if (D.integer) {
        const lo = Math.max(Math.ceil(a), D.unbounded ? -Infinity : D.a), hi = Math.min(Math.floor(b), D.unbounded === 'both' ? Infinity : D.b);
        return interval(lo, Math.max(lo, hi), { integer: true });
      }
      if (D.unbounded) return interval(Math.max(a, D.unbounded === 'above' ? D.lo : a), b);
      const lo = Math.max(a, D.lo), hi = Math.min(b, D.hi);
      if (lo > hi) return finite([]);
      return interval(lo, hi, { loOpen: lo === D.lo && D.loOpen, hiOpen: hi === D.hi && D.hiOpen });
    }
    const A = interval(a, b);
    return predSet({ ambient: A, test: v => A.contains(v) && D.contains(v), label: D.describe() });
  }
  if (D.dim === 2 && box.length === 2) {
    if (D.kind === 'product' && D.factors.every(f => f.scalar)) return product(D.factors.map((f, i) => restrictSpace(f, [box[i]])));
    const A = product([interval(...box[0]), interval(...box[1])]);
    return predSet({ ambient: A, test: v => A.contains(v) && D.contains(v), label: D.describe() });
  }
  return D;
}

/* ---------- products: ℝ², [0, 1]³, A × B ---------- */

function product(factors, o = {}) {
  const fs = factors.map(f => MV.toDomain(f));
  const n = fs.length;
  const scalar = fs.every(f => f.scalar);
  const same = fs.every(f => f.describe() === fs[0].describe());
  // (−1..1)² rather than −1..1², which reads as −1..(1²).
  const wrap = t => /\.\.|[\s×∪∩∖|]/.test(t) && !/^[[({].*[\])}]$/.test(t) ? `(${t})` : t;
  const label = o.label || (same ? `${wrap(fs[0].describe())}${SUP(n)}` : fs.map(f => f.describe()).join(' × '));
  let bcache = null, ucache = null;
  const d = space({
    kind: 'product', factors: fs, label, numeric: scalar, discrete: fs.every(f => f.discrete),
    dim: scalar ? n : fs.reduce((s, f) => s + (typeof f.dim === 'number' ? f.dim : 1), 0),
    size: fs.reduce((s, f) => s * (f.discrete ? (f.size ?? Infinity) : Infinity), 1),
    contains: v => Array.isArray(v) && v.length === n && fs.every((f, i) => f.contains(v[i])),
    random: () => fs.map(f => f.random()),
    sample(m, opts = {}) {
      if (d.discrete && d.size <= m) return cartesian(fs.map(f => f.sample(Infinity)));
      if (opts.grid && n === 2) {
        const per = Math.max(2, Math.round(Math.sqrt(m)));
        return cartesian([fs[0].sample(per, { grid: true }), fs[1].sample(per, { grid: true })]);
      }
      const out = stride(d.boundary().filter(b => b.inside).map(b => b.p), Math.floor(m / 5));
      while (out.length < m) out.push(d.random());
      return out;
    },
    boundary() {
      if (bcache) return bcache;
      bcache = [];
      fs.forEach((f, i) => {
        for (const r of f.boundary()) for (let k = 0; k < 8; k++) {
          const p = fs.map(g => g.random());
          const inner = p.slice();
          p[i] = r.p; inner[i] = r.inner;
          bcache.push({ p, inside: r.inside, inner });
        }
      });
      return bcache;
    },
    window: () => scalar ? fs.map(f => f.window()) : null,
    universe() {
      if (ucache) return ucache;
      const us = fs.map(f => f.universe());
      return (ucache = us.every((u, i) => u === fs[i]) ? d : product(us));
    },
  });
  return d;
}
function cartesian(lists) {
  let out = [[]];
  for (const L of lists) { const next = []; for (const p of out) for (const v of L) next.push([...p, v]); out = next; }
  return out;
}

/* ---------- sets defined by a predicate ---------- */

function predSet({ ambient, test, label, text, vars }) {
  const S = space({
    kind: 'set', ambient, vars, label, text,
    dim: ambient.dim, scalar: !!ambient.scalar, numeric: !!(ambient.numeric || ambient.scalar), discrete: !!ambient.discrete,
    contains: v => test(v) === true,
    sample: (n, opts) => sampleSet(S, n, opts),
    random() {
      const pool = explore(S).pool;
      if (!pool.length) throw new MVError(`Couldn't find any point of ${S.describe()} by sampling. It may be empty or too thin to hit.`);
      return pool[Math.floor(rand() * pool.length)];
    },
    boundary: () => explore(S).boundary,
    outsidePoints: () => explore(S).outside || [],
    window: () => explore(S).window,
    universe: () => ambient.universe ? ambient.universe() : ambient,
    describe: () => S.label || text || 'a set',
  });
  return S;
}

function explore(S) {
  if (S._ex) return S._ex;
  const amb = S.ambient;
  const win = (amb.scalar || amb.numeric) && amb.window ? amb.window() : null;
  if (!win || amb.discrete) {
    const pool = amb.sample(3000).filter(v => S.contains(v));
    return (S._ex = { pool, inside: pool, near: [], boundary: [], window: win, outside: [] });
  }
  const scalar = !!amb.scalar;
  const box0 = scalar ? [win] : win;
  const randomIn = box => { const p = box.map(([a, b]) => a + (b - a) * rand()); return scalar ? p[0] : p; };
  const ins = [], outs = [];
  const classify = p => { (S.contains(p) ? ins : outs).push(p); };
  for (const p of amb.sample(Math.min(400, 80 * box0.length))) classify(p);
  for (let k = 0; k < 1200; k++) classify(randomIn(box0));
  // Shrinking boxes around the window's center, so small sets near the origin are always hit.
  for (const f of [1 / 4, 1 / 16, 1 / 64]) {
    const sub = box0.map(([a, b]) => { const c = (a + b) / 2, h = (b - a) * f / 2; return [c - h, c + h]; });
    for (let k = 0; k < 300; k++) classify(randomIn(sub));
  }
  // Look more closely wherever the rarer kind of point lives (a small set, or a small hole).
  for (let round = 0; round < 3; round++) {
    if (ins.length >= 80 && outs.length >= 80) break;
    const minority = ins.length <= outs.length ? ins : outs;
    if (!minority.length) break;
    const bb = bbox(minority, scalar).map(([a, b], i) => {
      const w = Math.max(b - a, (box0[i][1] - box0[i][0]) * 1e-3);
      return [a - w * 0.5, b + w * 0.5];
    });
    for (let k = 0; k < 800; k++) classify(randomIn(bb));
  }
  const toWin = box => scalar ? box[0] : box;
  if (!ins.length) return (S._ex = { pool: [], inside: [], near: [], boundary: [], window: toWin(box0), empty: true, outside: stride(outs, 200) });

  // Boundary: from inside points, walk along rays (the axis directions and random ones) until the
  // ray leaves the set, then bisect with exact comparisons. Rays in every direction find every edge.
  const boundary = [];
  const dim = box0.length;
  const span0 = Math.max(...box0.map(([a, b]) => b - a));
  const firstBox = bbox(ins, scalar);
  const step0 = Math.max(1e-9, Math.max(...firstBox.map(([a, b]) => b - a)) * 0.02, span0 * 1e-6);
  const dirs = [];
  for (let i = 0; i < dim; i++) for (const s of [-1, 1]) { const u = new Array(dim).fill(0); u[i] = s; dirs.push(u); }
  const randDir = () => {
    const g = Array.from({ length: dim }, () => rand() * 2 - 1);
    const L = Math.hypot(...g) || 1;
    return g.map(x => x / L);
  };
  const along = (a, u, t) => scalar ? a + u[0] * t : a.map((x, i) => x + u[i] * t);
  // Rays start from inside points and walk out, and from outside points and walk in, so a small set
  // or a small hole is found from both sides.
  const outBox = outs.length ? bbox(outs, scalar) : firstBox;
  const outStep = Math.max(1e-9, Math.max(...outBox.map(([a, b]) => b - a)) * 0.02, span0 * 1e-6);
  const rays = [
    ...stride(shuffled(ins), 80).map((a, idx) => ({ from: a, inside: true, idx })),
    ...stride(shuffled(outs), 60).map((a, idx) => ({ from: a, inside: false, idx })),
  ];
  rays.forEach(({ from, inside, idx }) => {
    const u = idx < dirs.length * 3 ? dirs[idx % dirs.length] : randDir();
    let t = inside ? step0 : outStep, other = null;
    for (let k = 0; k < 40 && t <= span0 * 4; k++, t *= 1.6) {
      const c = along(from, u, t);
      if (S.contains(c) !== inside) { other = c; break; }
    }
    if (!other) return;
    const a = inside ? from : other;
    {
      let lo = a, hi = inside ? other : from;
      exact(() => {
        for (let it = 0; it < 64; it++) {
          const mid = plerp(lo, hi, 0.5);
          if (S.contains(mid)) lo = mid; else hi = mid;
          if (pdist(lo, hi) <= 4e-16 * (1 + pnorm(hi))) break;
        }
      });
      const inHi = S.contains(hi), inLo = S.contains(lo);
      boundary.push({ p: inHi ? hi : inLo ? lo : hi, inside: inHi || inLo, inner: a });
    }
  });
  const bb = bbox([...ins, ...boundary.map(b => b.p)], scalar);
  const scale = Math.max(1e-9, ...bb.map(([a, b]) => b - a));
  // Inside points at distances 1e-2, 1e-3 and 1e-4 (relative to the set's size) from the boundary.
  const near = [];
  for (const b of boundary) {
    const L = pdist(b.p, b.inner);
    if (!(L > 0)) continue;
    for (const f of [1e-2, 1e-3, 1e-4]) {
      const q = plerp(b.p, b.inner, Math.min(0.5, f * scale / L));
      if (S.contains(q)) near.push(q);
    }
  }
  const window = toWin(bb.map(([a, b]) => { const pad = Math.max((b - a) * 0.08, 1e-6); return [a - pad, b + pad]; }));
  // Very near points, just beyond the comparison tolerance: offered only to a ∀ inside an ∃
  // (as in "∃ε ∀x ∈ S"), which must see points as close to the edge as ε is small.
  const deepNear = [];
  for (const b of boundary) {
    const L = pdist(b.p, b.inner);
    if (!(L > 0)) continue;
    for (const dist of [1e-6 * scale, 5e-9 * Math.max(1, pnorm(b.p))]) {
      const q = plerp(b.p, b.inner, Math.min(0.5, dist / L));
      if (S.contains(q)) deepNear.push(q);
    }
  }
  const pool = [...ins, ...near, ...boundary.filter(b => b.inside).map(b => b.p)];
  // Points just outside the set (and some farther out): used by A ⊆ S to find where A leaves S.
  const outside = [...boundary.filter(b => !b.inside).map(b => b.p)];
  for (const b of boundary) {
    const L = pdist(b.p, b.inner);
    if (!(L > 0)) continue;
    for (const f of [1e-2, 1e-3, 1e-4]) {
      const q = plerp(b.p, b.inner, -Math.min(0.5, f * scale / L));
      if (!S.contains(q)) outside.push(q);
    }
  }
  outside.push(...stride(shuffled(outs), 200));
  return (S._ex = { pool, inside: ins, near, deepNear, boundary, window, outside });
}

function sampleSet(S, n, opts = {}) {
  const ex = explore(S);
  if (!ex.boundary.length && !ex.near.length) return stride(ex.pool, n);
  const bIn = ex.boundary.filter(b => b.inside).map(b => b.p);
  const near = opts.deep && ex.deepNear ? [...stride(ex.deepNear, Math.round(n * 0.15)), ...stride(ex.near, Math.round(n * 0.1))] : stride(ex.near, Math.round(n * 0.25));
  const out = [...stride(bIn, Math.round(n * 0.25)), ...near];
  out.push(...stride(ex.inside, Math.max(0, n - out.length)));
  return out;
}

/* ---------- balls ---------- */

function ball(c, r, closed = false) {
  if (!isPoint(c)) throw new MVError(`A ball's center must be a number or a point such as (0, 0), not ${MV.fmt(c)}.`);
  if (typeof r !== 'number') throw new MVError(`A ball's radius must be a number, not ${MV.fmt(r)}.`);
  const dim = pdim(c), scalar = typeof c === 'number';
  const at = (dir, rad) => scalar ? c + dir * rad : c.map((x, i) => x + dir[i] * rad);
  const randDir = () => {
    if (scalar) return rand() < 0.5 ? -1 : 1;
    const g = c.map(() => { let u = 0; while (u === 0) u = rand(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * rand()); });
    const L = Math.hypot(...g) || 1;
    return g.map(x => x / L);
  };
  const fixedDirs = () => {
    if (scalar) return [-1, 1];
    const dirs = [];
    for (let i = 0; i < dim; i++) for (const s of [-1, 1]) { const v = new Array(dim).fill(0); v[i] = s; dirs.push(v); }
    if (dim === 2) for (const [a, b] of [[1, 1], [1, -1], [-1, 1], [-1, -1]]) dirs.push([a / Math.SQRT2, b / Math.SQRT2]);
    return dirs;
  };
  const d = space({
    kind: 'ball', center: c, radius: r, closed, dim, scalar, numeric: !scalar,
    label: `${closed ? 'B̄' : 'B'}(${MV.fmt(c)}, ${fmtNum(r)})`,
    contains: v => isPoint(v) && pdim(v) === dim && (typeof v === 'number') === scalar && MV.compare(closed ? '<=' : '<', pdist(v, c), r),
    random: () => r > 0 ? at(randDir(), r * Math.pow(rand(), 1 / dim)) : c,
    sample(n) {
      if (!(r > 0)) return closed ? [c] : [];
      const edge = closed ? r : r * (1 - 1e-6);
      const out = [c, ...fixedDirs().map(u => at(u, edge))];
      while (out.length < n) out.push(out.length % 2 ? at(randDir(), edge) : d.random());
      return out.slice(0, Math.max(n, 1));
    },
    boundary: () => (r > 0 ? [...fixedDirs(), ...Array.from({ length: 16 }, randDir)] : []).map(u => ({ p: at(u, r), inside: closed, inner: c })),
    window: () => scalar ? [c - r, c + r] : c.map(x => [x - r, x + r]),
    universe: () => scalar ? Runiverse() : product(new Array(dim).fill(Runiverse())),
  });
  return d;
}

/* ---------- sequences: Seq(X) is the space of sequences 1, 2, 3, … → X ---------- */

const RATES = [
  { f: k => 1 / k, t: '1/n' }, { f: k => 1 / (k * k), t: '1/n²' },
  { f: k => Math.pow(2, -k), t: '2⁻ⁿ' }, { f: k => 1 / Math.sqrt(k), t: '1/√n' },
];
const CHECK_TERMS = [...Array.from({ length: 40 }, (_, i) => i + 1), 100, 1000, 10000];

function seqSpace(X) {
  X = MV.toDomain(X);
  const cache = {};
  const all = () => { MV.STRESSABLE = true; const s = MV.STRESS || 0; return cache[s] || (cache[s] = makeSequences(X, s)); };
  const S = space({
    kind: 'seq', of: X, dim: 'seq', label: `Seq(${X.describe()})`,
    contains(s) {
      if (typeof s !== 'function' || s.domainCtor) return false;
      for (let k = 1; k <= 30; k++) { let v; try { v = s(k); } catch (e) { return false; } if (!X.contains(v)) return false; }
      return true;
    },
    sample: n => all().slice(0, n),
    random: () => { const a = all(); return a[Math.floor(rand() * a.length)]; },
  });
  return S;
}

function makeSeq(fn, label, meta) {
  fn.label = label;
  fn.isSequence = true;
  return Object.assign(fn, meta);
}

/* A spread of sequences in X, most informative first: sequences that run into X's boundary
   (where closedness is decided), sequences converging inside X, constants, and divergent ones.
   Each knows its own formula and limit, so lim(s) and convergent(s) are exact for them. */
function makeSequences(X, stress = 0) {
  const fmt = v => typeof v === 'function' ? `(${MV.fmt(v)})` : MV.fmt(v);
  const pts = shuffled(X.sample(24));
  const bnd = stride(shuffled(X.boundary()), 10);
  const groups = [[], [], [], [], []];
  bnd.forEach((b, i) => {
    for (const g of [RATES[i % 4], RATES[(i + 1) % 4]]) {
      groups[0].push(makeSeq(k => glerp(b.p, b.inner, g.f(k)), `runs to ${fmt(b.p)} like ${g.t}`, { limit: b.p, convergent: true }));
    }
  });
  pts.forEach((L, i) => {
    const a = pts[(i + 7) % pts.length], g = RATES[i % 4];
    if (pts.length > 1) groups[1].push(makeSeq(k => glerp(L, a, g.f(k)), `tends to ${fmt(L)} like ${g.t}`, { limit: L, convergent: true }));
    if (isPoint(L) && i % 3 === 0 && pts.length > 1) {
      groups[1].push(makeSeq(k => glerp(L, a, (k % 2 ? -1 : 1) / k), `tends to ${fmt(L)}, alternating`, { limit: L, convergent: true }));
    }
  });
  pts.slice(0, 4).forEach(p => groups[2].push(makeSeq(() => p, `constant ${fmt(p)}`, { limit: p, convergent: true })));
  for (let i = 0; i + 1 < pts.length && i < 8; i += 2) {
    const p = pts[i], q = pts[i + 1];
    if (MV.equalValues(p, q)) continue;
    groups[3].push(makeSeq(k => (k % 2 ? p : q), `alternates between ${fmt(p)} and ${fmt(q)}`, { convergent: false, bounded: true }));
  }
  if (pts.length >= 3) {
    const cyc = pts.slice(0, 5);
    groups[3].push(makeSeq(k => cyc[(k * 7 + (k >> 2)) % cyc.length], `jumps around ${cyc.length} points`, { convergent: false, bounded: true }));
  }
  if (X.scalar) {
    const c = pts[0] ?? 0;
    groups[4].push(makeSeq(k => c + Math.sin(k), `${fmt(c)} + sin(n)`, { convergent: false, bounded: true }));
    groups[4].push(makeSeq(k => c + k, `${fmt(c)} + n`, { convergent: false, bounded: false }));
    groups[4].push(makeSeq(k => c + (k % 2 ? 1 : -1), `${fmt(c)} ± 1, alternating`, { convergent: false, bounded: true }));
  }
  if (stress) {
    // Wilder ways to converge and to fail to converge.
    pts.slice(0, 6).forEach((L, i) => {
      const a = pts[(i + 3) % pts.length];
      if (!a || MV.equalValues(a, L)) return;
      groups[1].unshift(makeSeq(k => glerp(L, a, 1 / Math.log(k + 1)), `tends to ${fmt(L)} like 1/log n (very slowly)`, { limit: L, convergent: true, hard: 'it converges so slowly (like 1/log n) that its terms are still far from the limit at any n a finite check looks at' }));
      groups[1].unshift(makeSeq(k => glerp(L, a, Math.sin(k) / k), `tends to ${fmt(L)}, oscillating`, { limit: L, convergent: true }));
    });
    for (let i = 0; i + 1 < pts.length && i < 6; i += 2) {
      const p = pts[i], q = pts[i + 1];
      if (MV.equalValues(p, q)) continue;
      groups[3].unshift(makeSeq(k => ((k & (k - 1)) === 0 ? q : p), `${fmt(p)}, except ${fmt(q)} at powers of 2`, { convergent: false, bounded: true, hard: 'it differs from a constant only at powers of 2, which sampled indices usually miss' }));
      groups[3].unshift(makeSeq(k => glerp(p, q, (1 + Math.sin(Math.log(k))) / 2), `drifts between ${fmt(p)} and ${fmt(q)} like sin(log n)`, { convergent: false, bounded: true, hard: 'it drifts so slowly (like sin(log n)) that over any short stretch of indices it looks convergent' }));
    }
  }
  const ok = s => CHECK_TERMS.every(k => { try { return X.contains(s(k)); } catch (e) { return false; } });
  const kept = groups.map(g => g.filter(ok));
  // Interleave the groups so a short sample still covers every kind.
  const out = [];
  for (let i = 0; out.length < 400 && kept.some(g => i < g.length); i++) for (const g of kept) if (i < g.length) out.push(g[i]);
  return out;
}

/* ---------- limits ---------- */

function limOf(s) {
  if (typeof s !== 'function') throw new MVError(`lim expects a sequence, not ${MV.fmt(s)}.`);
  if (s.limit !== undefined) return s.limit;
  if (s.convergent === false) return NaN;
  // A sequence given by a formula: its limit from the asymptotic expansion, when that decides it.
  const L = MV.ASYM && MV.ASYM.seqLimit(s);
  if (L) return L.kind === 'finite' ? L.v : L.kind === 'inf' ? L.sign * Infinity : NaN;
  MV.INEXACT = true;   // a numerical estimate
  return numericLimit(s);
}
function numericLimit(s) {
  // Mixed residues (even, odd, 0/1/2 mod 3) and consecutive terms at the end, so periodic
  // sequences such as (−1)ⁿ are not mistaken for constant ones.
  const ns = [1000, 10007, 100002, 1000003];
  let vals, tail;
  try { vals = ns.map(n => s(n)); tail = [1000004, 1000005].map(n => s(n)); } catch (e) { return NaN; }
  if (typeof vals[0] === 'function') {
    const f = m => numericLimit(k => s(k)(m));
    f.label = `pointwise limit of ${MV.fmt(s)}`;
    return makeSeq(f, f.label, {});
  }
  if (Array.isArray(vals[0])) return vals[0].map((_, i) => numericLimit(k => s(k)[i]));
  if (![...vals, ...tail].every(v => typeof v === 'number' && Number.isFinite(v))) return NaN;
  const [, b, c, d] = vals, d1 = Math.abs(c - b), d2 = Math.abs(d - c);
  const tol = 1e-4 * Math.max(1, Math.abs(d));
  if (d2 > tol || d2 > d1 + 1e-12 || tail.some(t => Math.abs(t - d) > tol)) return NaN;
  // Richardson step for the common 1/n rate.
  const q = d1 > 0 ? d2 / d1 : 0;
  return (q > 0.05 && q < 0.15) ? d + (d - c) * q / (1 - q) : d;
}
function convergent(s) {
  if (typeof s !== 'function') throw new MVError(`convergent expects a sequence, not ${MV.fmt(s)}.`);
  if (s.convergent !== undefined) return s.convergent;
  const A = MV.ASYM && MV.ASYM.seqLimit(s);
  if (A) return A.kind === 'finite';
  MV.INEXACT = true;
  const L = limOf(s);
  const bad = v => typeof v === 'number' ? Number.isNaN(v) : Array.isArray(v) ? v.some(bad) : false;
  return !bad(L);
}
function limitAt(f, a) {
  MV.INEXACT = true;
  // Both one-sided values at shrinking steps must settle down, and agree.
  const hs = [1e-3, 1e-4, 1e-5, 1e-6, 1e-7];
  const side = s => hs.map(h => f(a + s * h));
  const L = side(-1), R = side(1);
  if (![...L, ...R].every(v => typeof v === 'number' && Number.isFinite(v))) return NaN;
  const settled = v => {
    const d1 = Math.abs(v[4] - v[3]), d0 = Math.abs(v[3] - v[2]);
    return d1 <= 1e-4 * Math.max(1, Math.abs(v[4])) && d1 <= d0 + 1e-9 * Math.max(1, Math.abs(v[4]));
  };
  if (!settled(L) || !settled(R)) return NaN;
  const tol = 1e-4 * Math.max(1, Math.abs(L[4]), Math.abs(R[4]));
  return Math.abs(L[4] - R[4]) <= tol ? (L[4] + R[4]) / 2 : NaN;
}

/* ---------- set algebra ---------- */

function complement(S) {
  S = MV.toDomain(S);
  if (S.complementOf) return S.complementOf;   // (Sᶜ)ᶜ = S exactly, even for sets sampling can't see, like a point
  const U = S.universe();
  const C = predSet({ ambient: U, test: v => U.contains(v) && !S.contains(v), label: `${S.describe()}ᶜ` });
  C.complementOf = S;
  return C;
}
function setOp(op, A, B) {
  A = MV.toDomain(A); B = MV.toDomain(B);
  // Finite sets combine exactly, into finite sets.
  const ea = MV.elementsOf(A), eb = MV.elementsOf(B);
  if (ea && (eb || op !== 'union')) {
    const vals = op === 'union' ? [...ea, ...eb.filter(x => !ea.some(y => MV.equalValues(x, y)))]
      : op === 'inter' ? ea.filter(x => B.contains(x)) : ea.filter(x => !B.contains(x));
    return finite(vals);
  }
  const sym = { union: '∪', inter: '∩', '\\': '∖' }[op];
  const test = op === 'union' ? v => A.contains(v) || B.contains(v)
    : op === 'inter' ? v => A.contains(v) && B.contains(v)
    : v => A.contains(v) && !B.contains(v);
  return predSet({ ambient: A.universe(), test, label: `${A.describe()} ${sym} ${B.describe()}` });
}

/* A box-shaped universe for MathViz.space({ window, contains }). */
function boxSet(spec) {
  const w = spec.window;
  const scalar = typeof w[0] === 'number';
  const ambient = scalar ? interval(w[0], w[1], { unbounded: 'both', label: 'ℝ' })
    : product(w.map(([a, b]) => interval(a, b, { unbounded: 'both', label: 'ℝ' })));
  return predSet({ ambient, test: v => ambient.contains(v) && spec.contains(v) === true, label: spec.label || spec.name });
}

const SetType = space({ kind: 'type', label: 'Set', contains: v => !!(v && v.__domain), random: () => Runiverse() });
const FunType = space({ kind: 'type', label: 'Fun', contains: v => typeof v === 'function' && !v.domainCtor, random: () => (x => x) });

Object.assign(MV, {
  exact, space, interval, finite, product, predSet, restrictSpace, ball, seqSpace, makeSeq, limOf, convergent, limitAt,
  complement, setOp, boxSet, Runiverse, Zuniverse, SetType, FunType, explore,
  isPoint, pdist, glerp, stride,
});

})(typeof window !== 'undefined' ? window : globalThis);
