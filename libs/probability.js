MathVizLibrary(function probability(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const num = v => typeof v === 'number' ? v : Array.isArray(v) ? v.map(num) : v != null && typeof v.valueOf() === 'number' ? +v : v;
  const r4 = x => fmt(+(+x).toPrecision(4));
  const truthy = v => v === true;

  /* ---------- special functions ---------- */
  // ln Γ(x) (Lanczos, about 15 digits).
  const LG = [676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
  function lgamma(x) {
    if (x < 0.5) return Math.log(Math.PI / Math.abs(Math.sin(Math.PI * x))) - lgamma(1 - x);
    x -= 1;
    let a = 0.99999999999980993;
    const t = x + 7.5;
    for (let i = 0; i < 8; i++) a += LG[i] / (x + i + 1);
    return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
  }
  const lchoose = (n, k) => lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1);
  // erf to about 1e-15: the series near 0, a continued fraction for erfc further out.
  function erf(x) {
    if (x < 0) return -erf(-x);
    if (x < 3) {
      let s = 0, term = x, n = 0;
      while (Math.abs(term) > 1e-17 * Math.abs(s) || n < 3) { s += term / (2 * n + 1); n++; term *= -x * x / n; if (n > 200) break; }
      return 2 / Math.sqrt(Math.PI) * s;
    }
    return 1 - erfc(x);
  }
  function erfc(x) {
    if (x < 3) return 1 - erf(x);
    // Lentz's method for erfc(x) = e^(−x²)/√π · 1/(x + 1/2/(x + 1/(x + 3/2/(x + …)))).
    let f = x, C = x, D = 0;
    for (let n = 1; n < 300; n++) {
      const a = n / 2;
      D = x + a * D; D = D === 0 ? 1e-300 : 1 / D;
      C = x + a / C; if (C === 0) C = 1e-300;
      const delta = C * D; f *= delta;
      if (Math.abs(delta - 1) < 1e-16) break;
    }
    return Math.exp(-x * x) / Math.sqrt(Math.PI) / f;
  }
  const Phi = z => 0.5 * erfc(-z / Math.SQRT2);

  /* ---------- seeded random numbers, so results repeat ---------- */
  function rng(seed = 1) {
    let a = (num(seed) * 2654435761) >>> 0 || 1;
    return () => { a |= 0; a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
  }
  const gauss = R => { let u = 0; while (!u) u = R(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * R()); };

  /* ---------- distributions ---------- */
  // { kind: 'distribution', label, discrete, support: [lo, hi] (whole numbers for discrete),
  //   pmf/pdf, cdf, mean, variance, draw(R), quantile(p) }
  const dist = o => Object.assign(Object.create(null), { kind: 'distribution', __dist: true }, o, { toString() { return o.label; } });
  const discreteCdf = (d, x) => { if (x < d.support[0]) return 0; let s = 0; const top = Math.min(Math.floor(x), d.support[1]); for (let k = d.support[0]; k <= top; k++) s += d.pmf(k); return Math.min(1, s); };
  const isWhole = k => Number.isInteger(k);

  function Bernoulli(p) {
    p = num(p); need(p >= 0 && p <= 1, 'Bernoulli(p) needs 0 ≤ p ≤ 1.');
    return dist({ label: `Bernoulli(${fmt(p)})`, discrete: true, support: [0, 1], pmf: k => k === 1 ? p : k === 0 ? 1 - p : 0, mean: p, variance: p * (1 - p), draw: R => (R() < p ? 1 : 0), cdfOf: null });
  }
  function Binomial(n, p) {
    n = num(n); p = num(p);
    need(isWhole(n) && n >= 0 && p >= 0 && p <= 1, 'Binomial(n, p) needs a whole number n ≥ 0 and 0 ≤ p ≤ 1.');
    const pmf = k => {
      if (!isWhole(k) || k < 0 || k > n) return 0;
      if (p === 0) return k === 0 ? 1 : 0;
      if (p === 1) return k === n ? 1 : 0;
      return Math.exp(lchoose(n, k) + k * Math.log(p) + (n - k) * Math.log(1 - p));
    };
    return dist({ label: `Binomial(${fmt(n)}, ${fmt(p)})`, discrete: true, support: [0, n], pmf, mean: n * p, variance: n * p * (1 - p), draw: R => { let s = 0; for (let i = 0; i < n; i++) if (R() < p) s++; return s; } });
  }
  function Geometric(p) {
    p = num(p); need(p > 0 && p <= 1, 'Geometric(p) needs 0 < p ≤ 1: the number of trials up to and including the first success.');
    return dist({ label: `Geometric(${fmt(p)})`, discrete: true, support: [1, Infinity], pmf: k => isWhole(k) && k >= 1 ? p * Math.pow(1 - p, k - 1) : 0, cdf: x => x < 1 ? 0 : 1 - Math.pow(1 - p, Math.floor(x)), mean: 1 / p, variance: (1 - p) / (p * p), draw: R => { let k = 1; while (R() >= p) k++; return k; } });
  }
  function Poisson(l) {
    l = num(l); need(l > 0, 'Poisson(λ) needs λ > 0.');
    return dist({ label: `Poisson(${fmt(l)})`, discrete: true, support: [0, Infinity], pmf: k => isWhole(k) && k >= 0 ? Math.exp(-l + k * Math.log(l) - lgamma(k + 1)) : 0, mean: l, variance: l, draw: R => { let k = 0, t = Math.exp(-l), s = t; const u = R(); while (u > s && k < 10000) { k++; t *= l / k; s += t; } return k; } });
  }
  function Die(sides = 6) {
    sides = num(sides); need(isWhole(sides) && sides >= 1, 'Die(n) needs a whole number of sides.');
    return dist({ label: sides === 6 ? 'a fair die' : `a fair ${fmt(sides)}-sided die`, discrete: true, support: [1, sides], pmf: k => isWhole(k) && k >= 1 && k <= sides ? 1 / sides : 0, mean: (sides + 1) / 2, variance: (sides * sides - 1) / 12, draw: R => 1 + Math.floor(R() * sides) });
  }
  function Uniform(a, b) {
    a = num(a); b = num(b); need(a < b, 'Uniform(a, b) needs a < b.');
    return dist({ label: `Uniform(${fmt(a)}, ${fmt(b)})`, discrete: false, support: [a, b], pdf: x => x >= a && x <= b ? 1 / (b - a) : 0, cdf: x => x <= a ? 0 : x >= b ? 1 : (x - a) / (b - a), mean: (a + b) / 2, variance: (b - a) ** 2 / 12, draw: R => a + (b - a) * R(), quantile: q => a + (b - a) * q });
  }
  function Normal(m = 0, s = 1) {
    m = num(m); s = num(s); need(s > 0, 'Normal(μ, σ) needs σ > 0.');
    return dist({ label: m === 0 && s === 1 ? 'Normal(0, 1)' : `Normal(${fmt(m)}, ${fmt(s)})`, discrete: false, support: [-Infinity, Infinity], pdf: x => Math.exp(-0.5 * ((x - m) / s) ** 2) / (s * Math.sqrt(2 * Math.PI)), cdf: x => Phi((x - m) / s), mean: m, variance: s * s, draw: R => m + s * gauss(R) });
  }
  function Exponential(l) {
    l = num(l); need(l > 0, 'Exponential(λ) needs λ > 0.');
    return dist({ label: `Exponential(${fmt(l)})`, discrete: false, support: [0, Infinity], pdf: x => x >= 0 ? l * Math.exp(-l * x) : 0, cdf: x => x <= 0 ? 0 : 1 - Math.exp(-l * x), mean: 1 / l, variance: 1 / (l * l), draw: R => -Math.log(1 - R()) / l, quantile: q => -Math.log(1 - q) / l });
  }

  const D = v => { need(v && v.__dist, `Expected a distribution, such as Binomial(10, 0.5), Normal(0, 1) or Die(6), but got ${fmt(v)}.`); return v; };
  const cdf = (d, x) => { d = D(d); x = num(x); return d.cdf ? d.cdf(x) : discreteCdf(d, x); };
  // The range that holds all but about 10⁻¹² of the probability, for sums and integrals.
  function span(d) {
    let [lo, hi] = d.support;
    if (lo === -Infinity) { lo = d.mean - 40 * Math.sqrt(d.variance); }
    if (hi === Infinity) hi = d.mean + 40 * Math.sqrt(d.variance) + (d.discrete ? 60 : 0);
    return [lo, hi];
  }
  // E[f(X)]: a sum over the support, or an integral (Gauss–Legendre on many panels).
  const GL = [[-0.9061798459386640, 0.2369268850561891], [-0.5384693101056831, 0.4786286704993665], [0, 0.5688888888888889], [0.5384693101056831, 0.4786286704993665], [0.9061798459386640, 0.2369268850561891]];
  function expectNum(d, f) {
    const [lo, hi] = span(d);
    if (d.discrete) {
      let s = 0;
      for (let k = Math.ceil(lo); k <= hi; k++) { const p = d.pmf(k); if (p > 0) s += p * f(k); }
      return s;
    }
    const n = 4000, w = (hi - lo) / n;
    let s = 0;
    for (let i = 0; i < n; i++) { const c = lo + w * (i + 0.5); for (const [x, wt] of GL) { const t = c + x * w / 2; s += wt * d.pdf(t) * f(t); } }
    return s * w / 2;
  }
  const call = (f, x) => num(f(x));
  const expect = (d, f) => { d = D(d); MathViz.markInexact(); return expectNum(d, x => call(f, x)); };
  // P(X ∈ A): A an interval (exact, from the cdf), or a condition x ↦ true/false.
  function prob(d, A) {
    d = D(d);
    // [a, b] written as a list of two numbers means the closed interval.
    if (Array.isArray(A) && A.length === 2 && num(A).every(Number.isFinite)) A = MathViz.interval(num(A[0]), num(A[1]));
    if (MathViz.isSet(A)) {
      const S = MathViz.toDomain(A);
      if (S.kind === 'interval' && !S.integer && !d.discrete) return Math.max(0, cdf(d, S.hi) - cdf(d, S.lo));
      return expect(d, x => (S.contains(x) ? 1 : 0));
    }
    need(typeof A === 'function', 'prob(D, A): A is a set or a condition x => …, as in prob(Die(6), k => k >= 5).');
    MathViz.markInexact();
    if (d.discrete) return expectNum(d, x => (truthy(A(x)) ? 1 : 0));
    return probIntervals(d, x => truthy(A(x)));
  }
  // A continuous distribution: where the condition holds, found on a grid with each switch point
  // pinned down by bisection, then measured exactly with the cdf. (A stretch where it holds that
  // is narrower than the grid can be missed.)
  function probIntervals(d, test) {
    const [lo, hi] = span(d), N = 600, xs = Array.from({ length: N + 1 }, (_, i) => lo + (hi - lo) * i / N);
    const on = xs.map(test);
    const edge = (a, b) => { const ta = test(a); for (let i = 0; i < 50; i++) { const m = (a + b) / 2; if (test(m) === ta) a = m; else b = m; } return (a + b) / 2; };
    let total = 0, start = on[0] ? -Infinity : null;
    for (let i = 1; i <= N; i++) {
      if (on[i] === on[i - 1]) continue;
      const x = edge(xs[i - 1], xs[i]);
      if (on[i]) start = x; else { total += cdf(d, x) - (start === -Infinity ? 0 : cdf(d, start)); start = null; }
    }
    if (start !== null) total += 1 - (start === -Infinity ? 0 : cdf(d, start));
    return Math.min(1, Math.max(0, total));
  }
  const mean = d => D(d).mean, variance = d => D(d).variance, sd = d => Math.sqrt(D(d).variance);
  const pmf = (d, k) => { d = D(d); need(d.discrete, `${d.label} is continuous: use pdf.`); return d.pmf(num(k)); };
  const pdf = (d, x) => { d = D(d); need(!d.discrete, `${d.label} is discrete: use pmf.`); return d.pdf(num(x)); };
  function quantile(d, q) {
    d = D(d); q = num(q); need(q > 0 && q < 1, 'quantile(D, q) needs 0 < q < 1.');
    if (d.quantile) return d.quantile(q);
    let [lo, hi] = span(d);
    if (d.discrete) { for (let k = Math.ceil(lo); k <= hi; k++) if (cdf(d, k) >= q) return k; return hi; }
    for (let i = 0; i < 200; i++) { const m = (lo + hi) / 2; if (cdf(d, m) < q) lo = m; else hi = m; }
    return (lo + hi) / 2;
  }
  const sample = (d, n, seed = 1) => { d = D(d); n = num(n); need(isWhole(n) && n >= 1 && n <= 1e6, 'sample(D, n) takes a whole number n of draws, up to a million.'); const R = rng(seed); return Array.from({ length: n }, () => d.draw(R)); };
  const sampleMean = (d, n, seed = 1) => { const xs = sample(d, n, seed); return xs.reduce((s, x) => s + x, 0) / xs.length; };

  /* ---------- finite probability spaces, exactly ---------- */
  const tuples = (k, vals) => { let out = [[]]; for (let i = 0; i < k; i++) out = out.flatMap(t => vals.map(v => [...t, v])); return out; };
  const dice = (n = 1, sides = 6) => {
    n = num(n); sides = num(sides);
    need(isWhole(n) && n >= 1 && Math.pow(sides, n) <= 200000, 'dice(n, sides): every outcome of n dice (at most 200000 outcomes).');
    const vals = Array.from({ length: sides }, (_, i) => i + 1);
    return MathViz.finite(n === 1 ? vals : tuples(n, vals), { label: n === 1 ? `the faces of a ${sides}-sided die` : `the ${fmt(Math.pow(sides, n))} rolls of ${fmt(n)} dice` });
  };
  const coins = n => {
    n = num(n); need(isWhole(n) && n >= 1 && n <= 16, 'coins(n): every sequence of n tosses, 1 for heads and 0 for tails (n ≤ 16).');
    return MathViz.finite(n === 1 ? [0, 1] : tuples(n, [0, 1]), { label: `the ${fmt(2 ** n)} sequences of ${fmt(n)} tosses` });
  };
  // P(A) when every outcome of S is equally likely: an exact fraction.
  function chance(S, A, B = null) {
    const els = MathViz.elements(S);
    need(els && els.length, 'chance(S, A) needs a finite set of equally likely outcomes, such as dice(2) or coins(3).');
    const test = (f, x) => truthy(f(x));
    let n = 0, k = 0;
    for (const x of els) { if (B && !test(B, x)) continue; n++; if (test(A, x)) k++; }
    need(n > 0, 'The condition never happens, so the conditional probability is undefined.');
    return MathViz.numbers.rational(k, n);
  }
  const chanceGiven = (S, A, B) => chance(S, A, B);
  // The chance that among n people two share a birthday (365 equally likely days).
  const birthday = n => { n = num(n); let q = 1; for (let k = 0; k < n; k++) q *= (365 - k) / 365; return 1 - q; };

  /* ---------- catalog ---------- */
  let cat = {};
  const Distributions = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (cat[key]) return cat[key];
    const list = [Bernoulli(0.3), Binomial(10, 0.5), Binomial(20, 0.1), Geometric(0.25), Poisson(3), Die(6), Uniform(0, 1), Normal(0, 1), Normal(2, 0.5), Exponential(1)];
    if (key) list.push(Poisson(0.2), Binomial(60, 0.95), Exponential(0.1), Geometric(0.9));
    return (cat[key] = MathViz.finite(list, { label: 'example distributions' }));
  };

  /* ---------- views ---------- */
  const shape = (ctx, d, fig) => {
    const [lo, hi] = d.discrete ? [d.support[0], Math.min(d.support[1], Math.ceil(d.mean + 6 * Math.sqrt(d.variance) + 3))] : [d.support[0] === -Infinity ? d.mean - 4.5 * Math.sqrt(d.variance) : d.support[0], d.support[1] === Infinity ? d.mean + 4.5 * Math.sqrt(d.variance) : d.support[1]];
    if (d.discrete) for (let k = Math.max(lo, Math.floor(d.mean - 6 * Math.sqrt(d.variance) - 3)); k <= hi; k++) fig.rect(k - 0.38, 0, k + 0.38, d.pmf(k), { color: 'c1', alpha: 0.75 });
    else fig.curve(Array.from({ length: 401 }, (_, i) => { const x = lo + (hi - lo) * i / 400; return [x, d.pdf(x)]; }), { color: 'c1', width: 2 });
    return [lo, hi];
  };
  const views = {
    distribution: {
      doc: 'distribution(D) draws the probabilities of D (bars for a discrete distribution, the density for a continuous one) with the mean and one standard deviation either side, and its cumulative distribution function.',
      render(ctx, d) {
        d = D(d);
        const fig = ctx.figure({ xlabel: 'x' });
        const [lo, hi] = shape(ctx, d, fig);
        const m = d.mean, s = Math.sqrt(d.variance);
        fig.vband(m - s, m + s, { color: 'c4', alpha: 0.12 });
        fig.seg(m, 0, m, d.discrete ? Math.max(...Array.from({ length: 30 }, (_, i) => d.pmf(Math.round(m) - 15 + i))) : d.pdf(m) * 1.05, { color: 'c4', width: 2 });
        const g = ctx.figure({ x: [lo - (d.discrete ? 1 : 0), hi + (d.discrete ? 1 : 0)], y: [0, 1.05], height: 140, xlabel: 'x' });
        g.curve(Array.from({ length: 601 }, (_, i) => { const x = lo - 1 + (hi - lo + 2) * i / 600; return [x, cdf(d, x)]; }), { color: 'c2', width: 2 });
        ctx.legend([{ label: d.discrete ? 'P(X = k)' : 'density', color: 'c1' }, { label: 'mean ± one standard deviation', color: 'c4' }, { label: 'P(X ≤ x)', color: 'c2' }]);
        ctx.note(`${d.label}: mean ${r4(m)}, standard deviation ${r4(s)}, median ${r4(quantile(d, 0.5))}.`);
      },
    },
    lln: {
      doc: 'lln(D, n) draws several running averages of n draws from D: each settles at the mean (the law of large numbers), with the band of ±2σ/√k around it narrowing as 1/√k.',
      render(ctx, d, n = 1000) {
        d = D(d);
        n = ctx.param('draws', { min: 10, max: 20000, step: 10, value: num(n) });
        const paths = ctx.param('paths', { min: 1, max: 12, step: 1, value: 6 });
        const m = d.mean, s = Math.sqrt(d.variance);
        const fig = ctx.figure({ x: [1, n], xlabel: 'number of draws k' });
        const ks = Array.from({ length: 300 }, (_, i) => Math.max(1, Math.round(Math.exp(Math.log(n) * i / 299))));
        fig.curve(ks.map(k => [k, m + 2 * s / Math.sqrt(k)]), { color: 'c4', width: 1, dash: [4, 3] });
        fig.curve(ks.map(k => [k, m - 2 * s / Math.sqrt(k)]), { color: 'c4', width: 1, dash: [4, 3] });
        const colors = ['c1', 'c2', 'c3', 'c5', 'c6'];
        for (let p = 0; p < paths; p++) {
          const R = rng(1000 + p), pts = [];
          let sum = 0, j = 0;
          for (let k = 1; k <= n; k++) { sum += d.draw(R); if (k === ks[j]) { pts.push([k, sum / k]); while (ks[j] === k) j++; } }
          fig.curve(pts, { color: colors[p % colors.length], width: 1.4, alpha: 0.85 });
        }
        fig.seg(1, m, n, m, { color: 'ink', width: 1.5 });
        ctx.legend([{ label: 'running averages', color: 'c1' }, { label: `mean ${r4(m)}`, color: 'ink' }, { label: 'mean ± 2σ/√k', color: 'c4' }]);
      },
    },
    clt: {
      doc: 'clt(D, n) draws the histogram of many sums of n draws from D, standardized, against the normal density: the central limit theorem. Slide n from 1 up and watch any shape turn into the bell curve.',
      render(ctx, d, n = 1) {
        d = D(d);
        n = ctx.param('n', { min: 1, max: 100, step: 1, value: num(n) });
        const trials = 20000, R = rng(7), m = d.mean, s = Math.sqrt(d.variance);
        const bins = 60, lo = -4, hi = 4, w = (hi - lo) / bins, counts = new Array(bins).fill(0);
        for (let t = 0; t < trials; t++) {
          let sum = 0;
          for (let i = 0; i < n; i++) sum += d.draw(R);
          const z = (sum - n * m) / (s * Math.sqrt(n)), b = Math.floor((z - lo) / w);
          if (b >= 0 && b < bins) counts[b]++;
        }
        const fig = ctx.figure({ x: [lo, hi], xlabel: 'standardized sum' });
        counts.forEach((c, i) => fig.rect(lo + i * w, 0, lo + (i + 1) * w, c / (trials * w), { color: 'c1', alpha: 0.6 }));
        fig.curve(Array.from({ length: 201 }, (_, i) => { const z = lo + (hi - lo) * i / 200; return [z, Math.exp(-z * z / 2) / Math.sqrt(2 * Math.PI)]; }), { color: 'c2', width: 2.2 });
        ctx.legend([{ label: `sums of ${n} draws from ${d.label}, standardized (${trials} trials)`, color: 'c1' }, { label: 'Normal(0, 1)', color: 'c2' }]);
        ctx.note(d.discrete && n < 30 ? 'A discrete distribution gives spiky histograms for small n; the spikes merge as n grows.' : 'Every distribution with a finite variance gives the same limit.');
      },
    },
    monty_hall: {
      doc: 'monty_hall(trials) plays the Monty Hall game: a car behind one of three doors, you pick one, the host opens another with a goat. Staying wins about 1/3 of the time, switching about 2/3.',
      render(ctx, trials = 3000) {
        trials = ctx.param('games', { min: 10, max: 20000, step: 10, value: num(trials) });
        const R = rng(3);
        let stay = 0, sw = 0;
        const ps = [], pw = [];
        for (let t = 1; t <= trials; t++) {
          const car = Math.floor(R() * 3), pick = Math.floor(R() * 3);
          if (pick === car) stay++; else sw++;
          if (t % Math.max(1, Math.floor(trials / 300)) === 0) { ps.push([t, stay / t]); pw.push([t, sw / t]); }
        }
        const fig = ctx.figure({ x: [1, trials], y: [0, 1], xlabel: 'games played' });
        fig.seg(1, 1 / 3, trials, 1 / 3, { color: 'c1', width: 1, dash: [4, 3] });
        fig.seg(1, 2 / 3, trials, 2 / 3, { color: 'c2', width: 1, dash: [4, 3] });
        fig.curve(ps, { color: 'c1', width: 2 });
        fig.curve(pw, { color: 'c2', width: 2 });
        ctx.legend([{ label: `stay: won ${r4(stay / trials)}`, color: 'c1' }, { label: `switch: won ${r4(sw / trials)}`, color: 'c2' }]);
        ctx.note('Switching wins exactly when your first pick was wrong, which happens 2 times in 3.');
      },
    },
    random_walk: {
      doc: 'random_walk(steps, paths) draws simple random walks (±1 each step) with the curves ±√n and ±2√n: a typical walk strays about √n from 0 after n steps.',
      render(ctx, steps = 1000, paths = 8) {
        steps = ctx.param('steps', { min: 10, max: 20000, step: 10, value: num(steps) });
        paths = num(paths);
        const fig = ctx.figure({ x: [0, steps], xlabel: 'step' });
        for (const k of [1, -1, 2, -2]) fig.curve(Array.from({ length: 200 }, (_, i) => { const t = steps * i / 199; return [t, k * Math.sqrt(t)]; }), { color: 'c4', width: 1, dash: Math.abs(k) === 2 ? [2, 3] : [5, 3] });
        const colors = ['c1', 'c2', 'c3', 'c5', 'c6'];
        for (let p = 0; p < paths; p++) {
          const R = rng(50 + p), pts = [[0, 0]];
          let x = 0;
          const every = Math.max(1, Math.floor(steps / 600));
          for (let t = 1; t <= steps; t++) { x += R() < 0.5 ? -1 : 1; if (t % every === 0) pts.push([t, x]); }
          fig.curve(pts, { color: colors[p % colors.length], width: 1.2, alpha: 0.85 });
        }
        ctx.legend([{ label: 'walks', color: 'c1' }, { label: '±√n and ±2√n', color: 'c4' }]);
      },
    },
  };

  MathViz.thumbnail(v => v && v.__dist, (fig, d) => {
    const f = fig({});
    shape(null, d, f);
  });

  MathViz.define({
    name: 'probability',
    description: 'Probability: distributions (Bernoulli, Binomial, Geometric, Poisson, Die, Uniform, Normal, Exponential) with pmf, pdf, cdf, mean, variance, quantiles, expectations and probabilities of events; seeded sampling; finite spaces of equally likely outcomes (dice, coins) with exact chances and conditional chances; the birthday problem; views of distributions, the law of large numbers, the central limit theorem, Monty Hall and random walks.',
    functions: {
      Bernoulli: { doc: 'Bernoulli(p): 1 with probability p, else 0.', fn: Bernoulli },
      Binomial: { doc: 'Binomial(n, p): the number of successes in n independent trials, each a success with probability p.', fn: Binomial },
      Geometric: { doc: 'Geometric(p): the number of trials up to and including the first success.', fn: Geometric },
      Poisson: { doc: 'Poisson(λ): the number of events when they happen at rate λ, independently.', fn: Poisson },
      Die: { doc: 'Die(n): a fair n-sided die (6 by default).', fn: Die },
      Uniform: { doc: 'Uniform(a, b): a point of [a, b], equally likely anywhere.', fn: Uniform },
      Normal: { doc: 'Normal(μ, σ): the bell curve with mean μ and standard deviation σ.', fn: Normal },
      Exponential: { doc: 'Exponential(λ): a waiting time at rate λ; memoryless.', fn: Exponential },
      pmf: { doc: 'pmf(D, k) = P(X = k) for a discrete distribution.', fn: pmf },
      pdf: { doc: 'pdf(D, x): the density of a continuous distribution at x.', fn: pdf },
      cdf: { doc: 'cdf(D, x) = P(X ≤ x).', fn: cdf },
      prob: { doc: 'prob(D, A) = P(X ∈ A), for a set A or a condition x => …, as in prob(Normal(0, 1), [-1, 1]) or prob(Die(6), k => k >= 5).', fn: prob },
      expect: { doc: 'expect(D, f) = E[f(X)], as in expect(Die(6), k => k^2).', fn: expect },
      mean: { doc: 'mean(D) = E[X].', fn: mean },
      variance: { doc: 'variance(D) = E[(X − E X)²].', fn: variance },
      sd: { doc: 'sd(D): the standard deviation, √variance.', fn: sd },
      quantile: { doc: 'quantile(D, q): the smallest x with P(X ≤ x) ≥ q; quantile(D, 0.5) is the median.', fn: quantile },
      sample: { doc: 'sample(D, n, seed): n independent draws from D, the same ones for the same seed.', fn: sample },
      sample_mean: { doc: 'sample_mean(D, n, seed): the average of n draws.', fn: sampleMean },
      dice: { doc: 'dice(n, sides): every roll of n dice, as tuples, each equally likely.', fn: dice },
      coins: { doc: 'coins(n): every sequence of n coin tosses (1 heads, 0 tails), each equally likely.', fn: coins },
      chance: { doc: 'chance(S, A): the probability of A when every outcome of the finite set S is equally likely, as an exact fraction; chance(S, A, B) is P(A given B).', fn: chance },
      chance_given: { doc: 'chance_given(S, A, B) = P(A | B) = P(A and B)/P(B), exactly.', fn: chanceGiven },
      birthday: { doc: 'birthday(n): the chance that two of n people share a birthday.', fn: birthday },
      normal_cdf: { doc: 'normal_cdf(z) = Φ(z), the standard normal distribution function.', fn: z => Phi(num(z)) },
      erf: { doc: 'erf(x), the error function.', fn: x => erf(num(x)) },
    },
    spaces: {
      Distributions: { doc: 'Distributions: example distributions, discrete and continuous, for claims about all of them.', fn: Distributions },
    },
    views,
    notation: `
# The probabilities of a distribution add up to 1.
lemma total_probability: forall D in Distributions: |prob(D, x => true) - 1| < 1e-6

# Chebyshev: the chance of landing t standard deviations from the mean is at most 1/t².
lemma chebyshev: forall D in Distributions, t in [1, 4]: prob(D, x => |x - mean(D)| >= t * sd(D)) <= 1/t^2 + 1e-6

# Is the mean always the median? Skewed distributions say no.
conjecture mean_is_median: forall D in Distributions: |cdf(D, mean(D)) - 1/2| < 1e-6

# The mean of Binomial(n, p) is np: summing k·P(X = k) agrees with the formula.
lemma binomial_mean: forall n in 1..30, p in [0, 1]: |expect(Binomial(n, p), k => k) - n*p| < 1e-8

# Two dice: a sum of 7 is the likeliest, at 1/6.
lemma seven_likeliest: forall s in 2..12: chance(dice(2), r => r[1] + r[2] = s) <= chance(dice(2), r => r[1] + r[2] = 7)

# The birthday problem: 23 people are enough for better than even odds.
lemma birthday_23: birthday(23) > 1/2 and birthday(22) < 1/2

# Pairwise independent events need not be independent: two tosses, A = first heads,
# B = second heads, C = both the same.
conjecture pairwise_gives_independent: forall S in {coins(2)}: chance(S, w => w[1] = 1 and w[2] = 1 and w[1] = w[2]) = chance(S, w => w[1] = 1) * chance(S, w => w[2] = 1) * chance(S, w => w[1] = w[2])
`,
  });
});
