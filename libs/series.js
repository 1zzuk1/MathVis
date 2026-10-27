MathVizLibrary(function series(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const isFn = f => typeof f === 'function';
  const seq = (fn, label, meta) => MathViz.sequence(fn, label, meta);

  /* ---------- partial sums, fast: running (Kahan) sums with a checkpoint every 1000 terms ---------- */
  const MAXN = 2e6;
  const sums = new WeakMap();
  function partialSum(a, N) {
    need(isFn(a), 'partial_sum(a, N) adds up the terms a(1), …, a(N) of a sequence a.');
    need(Number.isInteger(N) && N >= 0, 'partial_sum(a, N) needs a whole number N ≥ 0.');
    need(N <= MAXN, `partial_sum works up to N = ${MAXN.toExponential(0)}.`);
    let st = sums.get(a);
    if (!st) { st = { cp: [0], n: 0, s: 0, c: 0 }; sums.set(a, st); }
    // Extend the checkpoints up to N.
    while (st.n + 1000 <= N) {
      for (let k = st.n + 1; k <= st.n + 1000; k++) {
        const y = a(k) - st.c, t = st.s + y;
        st.c = (t - st.s) - y; st.s = t;
      }
      st.n += 1000;
      st.cp.push(st.s);
    }
    const base = Math.floor(N / 1000);
    let s = st.cp[Math.min(base, st.cp.length - 1)], c = 0;
    for (let k = Math.min(base, st.cp.length - 1) * 1000 + 1; k <= N; k++) {
      const y = a(k) - c, t = s + y;
      c = (t - s) - y; s = t;
    }
    return s;
  }

  /* ---------- does Σ a(n) converge? Known series say so; others are judged from partial sums ---------- */
  function judge(a) {
    if (typeof a.summable === 'boolean') return { summable: a.summable, sum: a.sum, known: true };
    const asym = MathViz.asym && MathViz.asym();
    const v = asym && asym.series(a);
    if (v) return { summable: v.converges, absolutely: v.absolutely, known: true, why: v.why, lazySum: v.converges };
    MathViz.markInexact();
    const Ns = [100, 1000, 10000, 100000, 1000000];
    const S = Ns.map(N => partialSum(a, N));
    if (!S.every(Number.isFinite)) return { summable: false };
    const d = S.slice(1).map((s, i) => s - S[i]);
    const ad = d.map(Math.abs);
    const scale = Math.max(1, Math.abs(S[S.length - 1]));
    if (ad[ad.length - 1] <= 1e-9 * scale) return { summable: true, sum: S[S.length - 1] };
    const r = ad.slice(1).map((x, i) => x / (ad[i] || 1e-300));
    const last = r[r.length - 1], prev = r[r.length - 2];
    // Geometric-looking decay of the differences (and not creeping up towards 1) means convergence.
    if (last < 0.85 && last <= prev + 0.03) {
      const tail = d[d.length - 1] * last / (1 - last);
      return { summable: true, sum: S[S.length - 1] + tail };
    }
    return { summable: false };
  }
  // The sum of a series known to converge, estimated from partial sums.
  function numericSum(a) {
    MathViz.markInexact();
    const S = [100000, 1000000].map(N => partialSum(a, N));
    const d = S[1] - S[0];
    return Math.abs(d) < 1e-9 * Math.max(1, Math.abs(S[1])) ? S[1] : S[1] + d / 9;
  }
  const summable = a => { need(isFn(a), 'summable(a) asks whether the series a(1) + a(2) + … converges.'); return judge(a).summable; };
  const seriesSum = a => {
    need(isFn(a), 'series_sum(a) is a(1) + a(2) + a(3) + ….');
    const j = judge(a);
    if (!j.known) MathViz.markInexact();
    // A series the analysis knows converges: its value comes from partial sums (an estimate).
    if (j.summable && j.lazySum) return numericSum(a);
    return j.summable ? j.sum : NaN;
  };
  const absCache = new WeakMap();
  const absSummable = a => {
    need(isFn(a), 'abs_summable(a) asks whether |a(1)| + |a(2)| + … converges.');
    if (typeof a.absolutely === 'boolean') return a.absolutely;
    { const asym = MathViz.asym && MathViz.asym(), v = asym && asym.series(a); if (v) return v.absolutely; }
    if (!absCache.has(a)) absCache.set(a, judge(n => Math.abs(a(n))).summable);
    MathViz.markInexact();
    return absCache.get(a);
  };
  // lim |a(n+1)/a(n)| and lim |a(n)|^(1/n) (for the ratio and root tests): values at two n,
  // extrapolated assuming an error like c/n. A limit near 1 is snapped to 1, where the tests say nothing.
  const extrapolate = (v, n1, n2, snap) => {
    const v1 = v(n1), v2 = v(n2);
    if (!Number.isFinite(v1) || !Number.isFinite(v2)) return NaN;
    let L = (n2 * v2 - n1 * v1) / (n2 - n1);
    if (Math.abs(L - 1) < snap) L = 1;
    return Math.max(0, L);
  };
  const ratioLimit = a => {
    MathViz.markInexact();
    const at = n => Math.abs(a(n + 1) / a(n));
    return Number.isFinite(at(1000)) ? extrapolate(at, 100, 1000, 2e-3) : extrapolate(at, 10, 100, 2e-3);
  };
  const rootLimit = a => {
    MathViz.markInexact();
    return extrapolate(n => Math.pow(Math.abs(a(n)), 1 / n), 100, 400, 1e-2);
  };

  /* ---------- example series (their terms; each knows whether it converges, and to what) ---------- */
  const caches = {};
  const zeta15 = 2.612375348685488, zeta101 = 100.57794333, dzeta2 = 0.9375482543158437;
  const fact = n => { let f = 1; for (let k = 2; k <= n; k++) f *= k; return f; };
  const Series = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (caches[key]) return caches[key];
    const list = [
      seq(n => 1 / (n * n), '1/n²', { expr: '1/n^2',  summable: true, sum: Math.PI * Math.PI / 6, absolutely: true }),
      seq(n => Math.pow(2, -n), '1/2ⁿ', { expr: '1/2^n',  summable: true, sum: 1, absolutely: true }),
      seq(n => (n % 2 ? 1 : -1) / n, '(−1)ⁿ⁺¹/n', { expr: '(-1)^(n+1)/n',  summable: true, sum: Math.LN2, absolutely: false }),
      seq(n => 1 / n, '1/n (harmonic)', { expr: '1/n',  summable: false, absolutely: false }),
      seq(n => 1 / Math.sqrt(n), '1/√n', { expr: '1/sqrt(n)',  summable: false, absolutely: false }),
      seq(n => (n <= 170 ? 1 / fact(n) : 0), '1/n!', { expr: '1/n!',  summable: true, sum: Math.E - 1, absolutely: true }),
      seq(n => n / Math.pow(2, n), 'n/2ⁿ', { expr: 'n/2^n',  summable: true, sum: 2, absolutely: true }),
      seq(n => (n % 2 ? -1 : 1), '(−1)ⁿ', { expr: '(-1)^n',  summable: false, absolutely: false }),
      seq(n => Math.sin(n) / (n * n), 'sin(n)/n²', { expr: 'sin(n)/n^2',  summable: true, sum: 1.0139591323607684, absolutely: true }),
      seq(n => 1 / ((n + 1) * Math.log(n + 1)), '1/((n+1) ln(n+1))', { expr: '1/((n+1)*ln(n+1))',  summable: false, absolutely: false }),
      seq(n => Math.pow(n, -1.5), '1/n^1.5', { expr: 'n^(-1.5)',  summable: true, sum: zeta15, absolutely: true }),
      seq(n => (n % 2 ? 1 : -1) / Math.sqrt(n), '(−1)ⁿ⁺¹/√n', { expr: '(-1)^(n+1)/sqrt(n)',  summable: true, sum: 0.6048986434216305, absolutely: false }),
      seq(n => Math.log(n) / (n * n), 'ln(n)/n²', { expr: 'ln(n)/n^2',  summable: true, sum: dzeta2, absolutely: true }),
      seq(n => 1 / (n * (n + 1)), '1/(n(n+1))', { expr: '1/(n*(n+1))',  summable: true, sum: 1, absolutely: true }),
      seq(n => Math.cos(n) / n, 'cos(n)/n', { expr: 'cos(n)/n',  summable: true, sum: -Math.log(2 * Math.sin(0.5)), absolutely: false }),
    ];
    if (key) list.push(
      seq(n => Math.pow(n, -1.01), '1/n^1.01 (converges, very slowly)', { expr: 'n^(-1.01)',  summable: true, sum: zeta101, absolutely: true }),
      seq(n => 1 / ((n + 2) * Math.log(n + 2) * Math.log(Math.log(n + 2))), '1/(n ln n ln ln n) (diverges, very slowly)', { expr: '1/((n+2)*ln(n+2)*ln(ln(n+2)))', summable: false, absolutely: false }),
      seq(n => Math.sin(n) / n, 'sin(n)/n', { expr: 'sin(n)/n',  summable: true, sum: (Math.PI - 1) / 2, absolutely: false }),
      seq(n => { const r = Math.round(Math.sqrt(n)); return r * r === n ? 1 / n : 1 / (n * n * n); }, '1/n at squares, 1/n³ elsewhere', { summable: true, absolutely: true }),
      seq(n => (n % 2 ? -1 : 1) / Math.pow(n, 0.6), '(−1)ⁿ/n^0.6', { expr: '(-1)^n/n^0.6',  summable: true, absolutely: false }),
    );
    return (caches[key] = MathViz.finite(list, { label: 'example series' }));
  };

  /* ---------- sequences of functions ---------- */
  // F(n) is the same function object each time, so sup distances can be remembered.
  const fseq = (F, label, meta = {}) => {
    const made = new Map();
    const G = n => {
      need(Number.isInteger(n) && n >= 1, `${label} is a sequence of functions: F(n) for n = 1, 2, 3, …`);
      if (made.has(n)) return made.get(n);
      const f = x => F(n, x);
      f.label = label.replace(/\bn\b/g, String(n));
      if (made.size < 20000) made.set(n, f);
      return f;
    };
    G.label = label;
    G.isFunctionSequence = true;
    if (meta.limit) { meta.limit.label = meta.limitLabel || 'lim'; }
    return Object.assign(G, meta);
  };
  const fcache = {};
  const FunctionSequences = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (fcache[key]) return fcache[key];
    const lim = (f, label) => { f.label = label; return f; };
    const list = [
      fseq((n, x) => Math.pow(x, n), 'xⁿ', { limit: lim(x => (x === 1 ? 1 : Math.abs(x) < 1 ? 0 : x > 1 ? Infinity : NaN), '0 for x < 1, 1 at x = 1'), uniform: false }),
      fseq((n, x) => x / n, 'x/n', { limit: lim(() => 0, '0'), uniform: true }),
      fseq((n, x) => Math.sin(n * x) / n, 'sin(nx)/n', { limit: lim(() => 0, '0'), uniform: true }),
      fseq((n, x) => n * x * Math.exp(-n * x), 'nx·e^(−nx)', { limit: lim(() => 0, '0'), uniform: false }),
      fseq((n, x) => Math.pow(x, n) * (1 - x), 'xⁿ(1 − x)', { limit: lim(() => 0, '0'), uniform: true }),
      fseq((n, x) => Math.pow(1 + x / n, n), '(1 + x/n)ⁿ', { limit: lim(x => Math.exp(x), 'eˣ'), uniform: true }),
      fseq((n, x) => Math.sqrt(x * x + 1 / n), '√(x² + 1/n)', { limit: lim(x => Math.abs(x), '|x|'), uniform: true }),
      fseq((n, x) => Math.atan(n * (x - 0.5)) * 2 / Math.PI, 'arctan(n(x − ½))·2/π', { limit: lim(x => Math.sign(x - 0.5), 'sign(x − ½)'), uniform: false }),
      fseq((n, x) => (x > 0 && x < 1 / n ? n : 0), 'n on (0, 1/n), else 0', { limit: lim(() => 0, '0'), uniform: false }),
    ];
    if (key) list.push(
      fseq((n, x) => Math.sin(n * n * x) / n, 'sin(n²x)/n (derivatives blow up)', { limit: lim(() => 0, '0'), uniform: true }),
      fseq((n, x) => n * n * x * Math.pow(1 - x, n), 'n²x(1 − x)ⁿ', { limit: lim(() => 0, '0'), uniform: false }),
    );
    return (fcache[key] = MathViz.finite(list, { label: 'example sequences of functions' }));
  };
  // The pointwise limit x ↦ lim F(n)(x): known for the examples, estimated otherwise.
  const limitFn = F => {
    need(isFn(F), 'limit_fn(F) needs a sequence of functions F, with F(n) a function for each n.');
    if (F.limit) return F.limit;
    const g = x => {
      MathViz.markInexact();
      const vs = [1e4, 1e5, 1e6].map(n => F(n)(x));
      return Math.abs(vs[2] - vs[1]) <= 1e-4 * Math.max(1, Math.abs(vs[2])) ? vs[2] : NaN;
    };
    g.label = `lim ${fmt(F)}`;
    return g;
  };
  // sup over [a, b] of |f − g|, from a fine grid refined around the largest gap.
  const supMemo = new WeakMap();
  const supDist = (f, g, a, b) => {
    MathViz.markInexact();
    const key = a + ',' + b;
    let m = supMemo.get(f);
    if (!m) { m = new Map(); supMemo.set(f, m); }
    let mg = m.get(g);
    if (!mg) { mg = new Map(); m.set(g, mg); }
    if (!mg.has(key)) mg.set(key, supDistRaw(f, g, a, b));
    return mg.get(key);
  };
  const supDistRaw = (f, g, a, b) => {
    let best = 0, bx = a;
    const n = 2000;
    const probe = x => { const v = Math.abs(f(x) - g(x)); if (Number.isFinite(v) && v > best) { best = v; bx = x; } };
    for (let i = 0; i <= n; i++) probe(a + (b - a) * i / n);
    // The gap often hides right beside an end (xⁿ near 1, a spike near 0): probe at 10⁻ᵏ from each end.
    for (let k = 1; k <= 15; k++) { probe(a + (b - a) * Math.pow(10, -k)); probe(b - (b - a) * Math.pow(10, -k)); }
    // Refine in a window as wide as the grid spacing, or as the distance to the nearer end if smaller.
    const toEnd = Math.min(bx - a, b - bx);
    const h = toEnd > 0 ? Math.min((b - a) / n, toEnd) : (b - a) / n;
    let lo = Math.max(a, bx - h), hi = Math.min(b, bx + h);
    for (let k = 0; k < 60; k++) {
      const m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3;
      const v1 = Math.abs(f(m1) - g(m1)), v2 = Math.abs(f(m2) - g(m2));
      if (v1 > best) best = v1;
      if (v2 > best) best = v2;
      if (v1 < v2) lo = m1; else hi = m2;
    }
    return best;
  };

  /* ---------- power series (Section 4.3) ---------- */
  // The radius of convergence 1 / limsup |cₖ|^(1/k) (Cauchy–Hadamard), from the coefficients
  // c(0), c(1), …: the largest of |cₖ|^(1/k) over a late stretch of k, with logarithms so that
  // cₖ = kᵏ or 1/k! don't overflow. 0 when the coefficients grow too fast, inf when they vanish.
  function radius(c) {
    if (typeof c !== 'function') throw MathViz.error('radius_of_convergence(c) needs the coefficients as a function k ↦ c(k), k = 0, 1, 2, ….');
    MathViz.markInexact();
    // The largest log|cₖ|/k over windows [K, 2K), K = 25, 50, …, until the coefficients overflow or
    // underflow (2ᵏ at k > 1023, 1/k! at k > 170): beyond that floating point says nothing.
    const roots = [];
    let seenNonzero = false;
    for (let K = 25; K <= 1600; K *= 2) {
      let best = -Infinity, broke = false;
      for (let k = K; k < 2 * K; k++) {
        let v;
        try { v = +c(k); } catch (e) { broke = true; break; }
        if (!Number.isFinite(v)) { broke = true; break; }
        if (v === 0) continue;
        if (Math.abs(v) < 1e-300) { broke = true; break; }
        seenNonzero = true;
        best = Math.max(best, Math.log(Math.abs(v)) / k);
      }
      if (broke) break;
      roots.push(best);
    }
    if (!seenNonzero && roots.length) return Infinity;   // a polynomial, or zeros from some point on
    const fin = roots.filter(r => r > -Infinity);
    if (fin.length < 2) {
      // Overflow or underflow from the start: kᵏ grows, 1/kᵏ shrinks, faster than any geometric rate.
      let v; try { v = +c(30); } catch (e) { v = NaN; }
      return !Number.isFinite(v) || Math.abs(v) > 1 ? 0 : Infinity;
    }
    const last = fin[fin.length - 1], d = last - fin[fin.length - 2];
    if (d > 0.3) return 0;           // the k-th roots keep growing (like kᵏ): radius 0
    if (d < -0.3) return Infinity;   // they keep shrinking (like 1/k!): radius ∞
    let R = Math.exp(-last);
    // The ratios |cₖ/cₖ₊₁| converge much faster when polynomial factors are involved (k²/3ᵏ): use
    // them when they are defined and steady over the last window.
    const K = 25 * 2 ** (roots.length - 1), ratios = [];
    for (let k = K; k < 2 * K - 1; k++) { let u, v; try { u = +c(k); v = +c(k + 1); } catch (e) { break; } if (u && v && Number.isFinite(u / v)) ratios.push(Math.abs(u / v)); }
    if (ratios.length > K / 2) {
      ratios.sort((x, y) => x - y);
      const lo = ratios[Math.floor(ratios.length * 0.1)], hi = ratios[Math.floor(ratios.length * 0.9)];
      if (hi / lo < 1.05) R = ratios[ratios.length - 1];
    }
    // Snap to a simple value when it is one (polynomial factors make the estimate converge slowly).
    for (const v of [0.25, 1 / 3, 0.5, 2 / 3, 1, 1.5, 2, 3, 4, 5, 10]) if (Math.abs(R - v) < 0.04 * v) return v;
    return R;
  }
  // The partial sum Σₖ₌₀ⁿ c(k)(x − x₀)ᵏ, as a function of x.
  function powerSum(c, x0, n) {
    if (typeof c !== 'function' || !Number.isInteger(n) || n < 0) throw MathViz.error('power_sum(c, x0, n) needs coefficients k ↦ c(k), a centre x0 and a degree n ≥ 0.');
    const cs = Array.from({ length: n + 1 }, (_, k) => +c(k));
    const f = x => { const t = +x - x0; let v = 0; for (let k = n; k >= 0; k--) v = v * t + cs[k]; return v; };
    f.label = `Σ_{k ≤ ${n}} c(k)(x − ${fmt(x0)})^k`;
    f.arity = 1;
    return f;
  }

  MathViz.define({
    name: 'series',
    requires: ['sequences', 'functions', 'analysis'],
    description: 'Infinite series (partial sums, sums, convergence tests, example series that know their sums) and sequences of functions (pointwise and uniform convergence, sup distances, example sequences).',
    functions: {
      partial_sum: { doc: 'partial_sum(a, N) = a(1) + a(2) + … + a(N), fast even for N in the millions.', fn: partialSum },
      series_sum: { doc: 'series_sum(a) = a(1) + a(2) + …: exact for the example series, estimated from partial sums otherwise; undefined if it diverges.', fn: seriesSum },
      summable: { doc: 'summable(a): whether a(1) + a(2) + … converges. The example series know the answer; for others it is judged from partial sums up to 10⁶, which slow series can fool.', fn: summable },
      abs_summable: { doc: 'abs_summable(a): whether |a(1)| + |a(2)| + … converges.', fn: absSummable },
      ratio_limit: { doc: 'ratio_limit(a) = lim |a(n+1)/a(n)|, estimated (undefined if it doesn\'t settle). The ratio test: < 1 converges, > 1 diverges.', fn: ratioLimit },
      root_limit: { doc: 'root_limit(a) = lim |a(n)|^(1/n), estimated. The root test: < 1 converges, > 1 diverges.', fn: rootLimit },
      limit_fn: { doc: 'limit_fn(F): the pointwise limit x ↦ lim F(n)(x) of a sequence of functions.', fn: limitFn },
      sup_norm: { doc: 'sup_norm(f, a, b) = ‖f‖∞ = sup |f(x)| for x in [a, b] (Definition 4.7), found on a fine grid.', fn: (f, a, b) => supDist(f, x => 0, a, b) },
      radius_of_convergence: { doc: 'radius_of_convergence(c): the radius of convergence of Σ c(k)(x − x₀)ᵏ, 1 / limsup |c(k)|^(1/k), estimated from late coefficients (0 for kᵏ, inf for 1/k!).', fn: radius },
      power_sum: { doc: 'power_sum(c, x0, n): the partial sum Σₖ₌₀ⁿ c(k)(x − x0)ᵏ, as a function of x.', fn: powerSum },
      sup_dist: { doc: 'sup_dist(f, g, a, b): the largest |f(x) − g(x)| for x in [a, b], found on a fine grid.', fn: supDist },
    },
    spaces: {
      Series: { doc: 'Series: example series, given by their terms a(n): 1/n², 1/2ⁿ, (−1)ⁿ⁺¹/n, the harmonic series, 1/√n, 1/n!, cos(n)/n, … Each knows whether it converges and its sum. "Try wilder examples" adds series too slow for any finite check.', fn: Series },
      FunctionSequences: { doc: 'FunctionSequences: example sequences of functions F (F(n) is a function) on [0, 1]: xⁿ, sin(nx)/n, nx·e^(−nx), (1 + x/n)ⁿ, a moving spike, … each with its pointwise limit.', fn: FunctionSequences },
    },
    views: {
      power_series: {
        doc: 'power_series(c, x0) draws partial sums of Σ c(k)(x − x0)ᵏ up to degree n (drag n) with the interval of convergence (x0 − r, x0 + r): inside, the partial sums settle (uniformly on each smaller closed interval, Theorem 4.10); outside, they fly apart.',
        render(ctx, c, x0 = 0) {
          const n = Math.round(ctx.param('n', { min: 0, max: 60, step: 1, value: 8 }));
          const r = radius(c), shown = Number.isFinite(r) && r > 0 ? r : 2;
          const X = [x0 - 1.6 * shown, x0 + 1.6 * shown];
          const limit = Number.isFinite(r) && r > 0 ? powerSum(c, x0, 400) : r === Infinity ? powerSum(c, x0, 200) : null;
          const vals = [];
          const fig = ctx.figure({ x: X, xlabel: 'x' });
          if (Number.isFinite(r) && r > 0) fig.vband(x0 - r, x0 + r, { color: 'c2', alpha: 0.08 });
          const ys = [];
          for (const k of [Math.max(0, n - 6), Math.max(0, n - 3), n]) {
            const f = powerSum(c, x0, k);
            const pts = Array.from({ length: 601 }, (_, i) => { const x = X[0] + (X[1] - X[0]) * i / 600; return [x, f(x)]; });
            vals.push([k, pts]);
            pts.forEach(p => { if (Math.abs(p[0] - x0) <= shown) ys.push(p[1]); });
          }
          if (limit) Array.from({ length: 200 }, (_, i) => { const x = x0 - 0.98 * shown + 1.96 * shown * i / 199; ys.push(limit(x)); });
          const fin = ys.filter(Number.isFinite), lo = Math.min(...fin), hi = Math.max(...fin), pad = 0.4 * ((hi - lo) || 1);
          const clip = pts => pts.map(([x, y]) => [x, y < lo - 3 * pad || y > hi + 3 * pad ? NaN : y]);
          vals.forEach(([k, pts], i) => fig.curve(clip(pts), { color: ['c4', 'c3', 'c1'][i], width: i === 2 ? 2 : 1.2 }));
          if (limit && Number.isFinite(r)) fig.curve(x => (Math.abs(x - x0) < 0.98 * r ? limit(x) : NaN), { color: 'ink', width: 1, dash: [4, 3], n: 500 });
          fig.points([[x0, +c(0)]], { color: 'ink', r: 3, track: false });
          ctx.legend([{ label: `degree ${n}`, color: 'c1' }, { label: `degree ${Math.max(0, n - 3)}`, color: 'c3' }, { label: `degree ${Math.max(0, n - 6)}`, color: 'c4' }, ...(Number.isFinite(r) && r > 0 ? [{ label: 'interval of convergence', color: 'c2' }] : [])]);
          ctx.note(r === Infinity ? 'The radius of convergence is ∞: the partial sums settle everywhere, uniformly on every bounded interval.'
            : r === 0 ? 'The radius of convergence is 0: the series converges only at x₀ (the coefficients grow like kᵏ, as in the appendix to chapter 4).'
              : `The radius of convergence is ${fmt(+r.toPrecision(4))}: inside (x₀ − r, x₀ + r) the partial sums settle, outside they grow without bound.`);
        },
      },
      partial_sums: {
        doc: 'partial_sums(a) plots the partial sums S(N) = a(1) + … + a(N) against N (with a log scale on N), and the sum if it converges.',
        render(ctx, a, upTo = 100000) {
          need(isFn(a), 'partial_sums(a) needs the terms a(n) of a series.');
          const pts = [];
          for (let e = 0; e <= Math.log10(upTo) + 1e-9; e += 0.02) {
            const N = Math.round(Math.pow(10, e));
            if (pts.length && pts[pts.length - 1][2] === N) continue;
            pts.push([e, partialSum(a, N), N]);
          }
          const fig = ctx.figure({ xlabel: 'log₁₀ N', ylabel: 'S(N)' });
          const j = judge(a);
          if (j.summable && j.lazySum) j.sum = numericSum(a);
          if (j.summable && Number.isFinite(j.sum)) fig.hband(j.sum, j.sum, { color: 'pos', alpha: 0.6 });
          fig.curve(pts.map(p => [p[0], p[1]]), { color: 'c1', width: 2 });
          fig.points(pts.filter(p => p[2] <= 30).map(p => [p[0], p[1]]), { color: 'c1', r: 2.5 });
          if (j.summable && Number.isFinite(j.sum)) fig.curve([[0, j.sum], [Math.log10(upTo), j.sum]], { color: 'pos', width: 1.5, dash: [6, 4] });
          ctx.note(j.summable ? `The partial sums settle at ${fmt(+j.sum.toPrecision(8))}${j.known && !j.lazySum ? '' : ' (estimated)'}.`
            : `The partial sums don't settle: S(${upTo.toLocaleString('en-US')}) = ${fmt(+partialSum(a, upTo).toPrecision(6))}${j.known ? '' : ' (judged from partial sums)'}.`);
        },
      },
      uniform: {
        doc: 'uniform(F, g, a, b) draws F(n) and its limit g on [a, b] with the band g ± ε. Uniform convergence means F(n) eventually stays in the band everywhere; drag n and ε.',
        render(ctx, F, g, a = 0, b = 1) {
          need(isFn(F), 'uniform(F, g, a, b) needs a sequence of functions F.');
          if (g === undefined) g = limitFn(F);
          const n = ctx.param('n', { min: 1, max: 200, step: 1, value: 5 });
          const eps = ctx.param('ε', { min: 0.01, max: 1, step: 0.01, value: 0.2 });
          const fig = ctx.figure({ x: [a, b], xlabel: 'x' });
          const xs = Array.from({ length: 801 }, (_, i) => a + (b - a) * i / 800);
          const up = xs.map(x => [x, g(x) + eps]), down = xs.map(x => [x, g(x) - eps]);
          const okUp = up.filter(p => Number.isFinite(p[1])), okDown = down.filter(p => Number.isFinite(p[1]));
          if (okUp.length > 2) fig.poly([...okUp, ...okDown.slice().reverse()], { color: 'pos', alpha: 0.12 });
          fig.curve(x => g(x), { color: 'pos', width: 1.5, dash: [6, 4], n: 800 });
          const f = F(n);
          fig.curve(x => f(x), { color: 'c1', width: 2.2, n: 1200 });
          const out = xs.filter(x => Number.isFinite(g(x)) && !(Math.abs(f(x) - g(x)) < eps)).map(x => [x, f(x)]);
          fig.points(out, { color: 'neg', r: 1.8 });
          const d = supDist(f, g, a, b);
          ctx.legend([{ label: `F(${n}) = ${fmt(f)}`, color: 'c1' }, { label: `limit ${fmt(g)} ± ε`, color: 'pos' }, { label: 'outside the band', color: 'neg' }]);
          ctx.note(`sup |F(${n}) − g| on [${fmt(a)}, ${fmt(b)}] = ${fmt(+d.toPrecision(4))}. ${d < eps ? 'Inside the band everywhere.' : 'Not yet inside the band everywhere.'} Uniform convergence means this sup tends to 0 as n grows.`);
        },
      },
    },
    notation: `
# fₙ → f uniformly on [a, b]: the sup-distance ‖fₙ − f‖∞ tends to 0 (Definitions 4.5 and 4.7).
# examples: F in FunctionSequences
def uniformly_to(F, f, a, b) := lim n -> inf: sup_dist(F(n), f, a, b) = 0

# The power series of eˣ, sin and 1/(1 − x) have radii ∞, ∞ and 1; Σ kᵏ xᵏ has radius 0 (appendix to chapter 4).
lemma radii: radius_of_convergence(k => 1/k!) = inf and radius_of_convergence(k => if k mod 2 = 1 then (-1)^((k - 1)/2)/k! else 0) = inf and radius_of_convergence(k => 1) = 1 and radius_of_convergence(k => k^k) = 0

# Inside the radius the partial sums converge uniformly (Theorem 4.10): eˣ on [−2, 2].
lemma power_series_uniform: forall n in {20, 30, 40}: sup_dist(power_sum(k => 1/k!, 0, n), exp, -2, 2) < 1e-9

# A power series may be differentiated term by term inside its radius (Corollary 4.11).
lemma power_series_derivative: forall x in [-0.9, 0.9]: deriv(power_sum(k => 1, 0, 400))(x) ~= power_sum(k => k + 1, 0, 400)(x)

# The Weierstrass M-test (4.8): Σ sin(kx)/k² converges uniformly, so its partial sums are uniformly Cauchy.
lemma m_test: forall n in {50, 100, 200}: sup_dist(x => sum k in 1..n: sin(k*x)/k^2, x => sum k in 1..2*n: sin(k*x)/k^2, 0, 6) <= sum k in n + 1..2*n: 1/k^2

# A uniform limit of differentiable functions need not be differentiable (after Theorem 4.8): each |x|^(1+1/n)
# is differentiable at 0, they converge uniformly to |x|, and |x| is not.
lemma powers_of_abs_differentiable: forall n in 1..20: differentiable_at(x => |x|^(1 + 1/n), 0)
lemma powers_of_abs_uniform: forall n in 1..50: sup_dist(x => |x|^(1 + 1/n), abs, -1, 1) <= 1/n
conjecture uniform_limit_differentiable: forall f in {x => |x|^(1 + 1/2), x => |x|}: differentiable_at(f, 0)

# Swapping limit and integral needs more than pointwise convergence: n times a tent of height 1 and base 2/n
# tends to 0 at every point, but its integral is 1 (Question 4.5).
conjecture pointwise_integral_swap: forall n in {1, 10, 100, 1000}: integral(x => n * max(0, 1 - |n*x - 1|), 0, 2, 20000) < 0.5

# The series Σ a(n) converges (the Cauchy criterion): the sum of the terms from N to 10N gets small.
# Checked with N up to 10⁵, so a slowly converging series (1/n^1.5 for tiny ε) can look divergent
# here; summable(a) knows the answer for the example series. Compare them with explain.
# examples: a in Series
def series_converges(a) := forall ε in (0, 1]: exists N in 1..100000: forall M in N..10*N: |partial_sum(a, M) - partial_sum(a, N)| < ε

# Σ a(n) converges absolutely: Σ |a(n)| converges.
# examples: a in Series
def absolutely_converges(a) := abs_summable(a)

# The terms of a convergent series tend to 0.
lemma term_test: forall a in Series: summable(a) -> converges_to(a, 0)

# Is the converse true? The harmonic series says no.
conjecture terms_to_zero_imply_summable: forall a in Series: converges_to(a, 0) -> summable(a)

# Absolute convergence implies convergence.
lemma absolute_implies_convergent: forall a in Series: abs_summable(a) -> summable(a)

# Does convergence imply absolute convergence? No: (−1)ⁿ⁺¹/n.
conjecture convergent_is_absolute: forall a in Series: summable(a) -> abs_summable(a)

# The comparison test, with its hypothesis 0 ≤ a ≤ b checked only for n ≤ 2000. Is that enough?
# Holds on the usual examples; try wilder ones: 1/(n ln n) stays below 1/n^1.01 far beyond any
# n you could check, yet one series diverges and the other converges.
conjecture comparison_test_finite: forall a, b in Series: (forall n in 1..2000: 0 <= a(n) and a(n) <= b(n)) and summable(b) -> summable(a)

# The ratio test: a ratio limit below 1 means convergence.
lemma ratio_test: forall a in Series: ratio_limit(a) < 1 -> summable(a)

# F converges to g pointwise on [a, b]: at each x, F(n)(x) → g(x) (N may depend on x).
# examples: F in FunctionSequences, a in {0}, b in {1}
def pointwise_converges(F, a, b) := forall x in [a, b], ε in (0, 1]: exists N in 1..10^7: forall n in N..10*N: |F(n)(x) - limit_fn(F)(x)| < ε

# F converges uniformly on [a, b]: one N works for every x at once.
# examples: F in FunctionSequences, a in {0}, b in {1}
def uniformly_converges(F, a, b) := forall ε in (0, 1]: exists N in 1..10^7: forall n in N..10*N: sup_dist(F(n), limit_fn(F), a, b) < ε

# A uniform limit of continuous functions is continuous.
lemma uniform_limit_continuous: forall F in FunctionSequences: uniformly_converges(F, 0, 1) -> continuous_at(limit_fn(F), 1)

# Is a pointwise limit of continuous functions continuous? xⁿ says no.
conjecture pointwise_limit_continuous: forall F in FunctionSequences: continuous_at(limit_fn(F), 1) and continuous_at(limit_fn(F), 0.5)
`,
  });
});
