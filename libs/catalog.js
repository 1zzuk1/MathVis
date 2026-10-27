MathVizLibrary(function catalog(MathViz) {
  const { lt, le, abs } = MathViz.ops;
  const R = MathViz.interval(-10, 10, { unbounded: 'both', label: 'ℝ' });
  const R2 = MathViz.product([R, R]);
  const set1 = (label, test) => MathViz.set(R, test, label);
  const set2 = (label, test) => MathViz.set(R2, test, label);
  const named = (fn, label) => { fn.label = label; return fn; };
  const seq = (f, label, limit) => MathViz.sequence(f, label, limit === undefined ? { convergent: false } : { limit, convergent: true });
  // Built once per level (normal / wild), so the same objects come back every time:
  // results of definitions are remembered per object.
  const cached = make => { const v = {}; return () => { MathViz.markStressable(); const s = MathViz.stress(); return v[s] || (v[s] = make(s)); }; };
  // A small seeded generator, so the "random" examples are the same on every run.
  const rng = seed => () => { seed = (seed * 16807) % 2147483647; return (seed - 1) / 2147483646; };
  const angle = ([x, y]) => Math.atan2(y, x);

  const subsetsR = cached(s => MathViz.finite([
    MathViz.interval(0, 1, { loOpen: true, hiOpen: true }),
    MathViz.interval(0, 1),
    MathViz.interval(0, 1, { hiOpen: true }),
    set1('[0, ∞)', x => le(0, x)),
    set1('(0, 1) ∪ (2, 3)', x => (lt(0, x) && lt(x, 1)) || (lt(2, x) && lt(x, 3))),
    MathViz.finite([0], { label: '{0}' }),
    MathViz.finite([0, 1, 2], { label: '{0, 1, 2}' }),
    set1('ℝ', () => true),
    set1('∅', () => false),
    ...(s ? [
      set1('Cantor set, 3rd stage', x => { if (!(le(0, x) && le(x, 1))) return false; let y = x; for (let k = 0; k < 3; k++) { if (le(y, 1 / 3)) y = 3 * y; else if (le(2 / 3, y)) y = 3 * y - 2; else return false; } return true; }),
      set1('(0, √2] ∪ [π, 4)', x => (lt(0, x) && le(x, Math.SQRT2)) || (le(Math.PI, x) && lt(x, 4))),
      MathViz.finite(Array.from({ length: 20 }, (_, k) => 1 / (k + 1)), { label: '{1, 1/2, …, 1/20}' }),
      set1('(−∞, 0) ∪ (0, ∞)', x => x !== 0 && !le(Math.abs(x), 0)),
      set1('ten small intervals', x => { const k = Math.floor(x * 5); return k >= 0 && k < 10 && lt(k / 5 + 0.02, x) && lt(x, k / 5 + 0.1); }),
      // The famous sets from the zoo (ℚ, the irrationals, the Cantor sets), which know their facts.
      ...((MathViz.shared.zoo && MathViz.shared.zoo.sets) || []),
    ] : []),
  ], { label: s ? 'example subsets of ℝ, wild' : 'example subsets of ℝ' }));

  const subsetsR2 = cached(s => {
    const base = [
      set2('open disk', p => lt(abs(p), 1)),
      set2('closed disk', p => le(abs(p), 1)),
      set2('half-open square', ([x, y]) => le(0, x) && lt(x, 1) && le(0, y) && lt(y, 1)),
      set2('open half-plane y > 0', ([, y]) => lt(0, y)),
      set2('closed half-plane y ≥ 0', ([, y]) => le(0, y)),
      set2('open annulus', p => lt(1, abs(p)) && lt(abs(p), 2)),
      set2('punctured disk', p => lt(0, abs(p)) && lt(abs(p), 1)),
      set2('closed triangle', ([x, y]) => le(0, x) && le(0, y) && le(x + y, 1)),
      set2('two disks', p => lt(abs([p[0] + 1.2, p[1]]), 1) || lt(abs([p[0] - 1.2, p[1]]), 1)),
      MathViz.finite([[0, 0]], { label: '{(0, 0)}' }),
      set2('ℝ²', () => true),
      set2('∅', () => false),
    ];
    if (!s) return MathViz.finite(base, { label: 'example subsets of ℝ²' });
    const r = rng(7);
    const polygon = (n, wobble) => {
      const pts = Array.from({ length: n }, (_, k) => { const t = 2 * Math.PI * k / n, rad = 1 - wobble * r(); return [rad * Math.cos(t), rad * Math.sin(t)]; });
      // Closed: inside by the even-odd rule, or on an edge.
      const segDist = (q, a, b) => {
        const dx = b[0] - a[0], dy = b[1] - a[1], t = Math.max(0, Math.min(1, ((q[0] - a[0]) * dx + (q[1] - a[1]) * dy) / (dx * dx + dy * dy)));
        return Math.hypot(q[0] - a[0] - t * dx, q[1] - a[1] - t * dy);
      };
      return p => {
        let inside = false;
        for (let i = 0, j = n - 1; i < n; j = i++) {
          if (le(segDist(p, pts[j], pts[i]), 0)) return true;
          const [xi, yi] = pts[i], [xj, yj] = pts[j];
          if ((yi > p[1]) !== (yj > p[1]) && p[0] < (xj - xi) * (p[1] - yi) / (yj - yi) + xi) inside = !inside;
        }
        return inside;
      };
    };
    return MathViz.finite([...base,
      set2('disk with half its boundary', p => lt(abs(p), 1) || (le(abs(p), 1) && le(0, p[1]))),
      set2('flower r < 1 + 0.35·sin(7θ)', p => lt(abs(p), 1 + 0.35 * Math.sin(7 * angle(p)))),
      set2('closed annulus 1 ≤ |p| ≤ 1.2', p => le(1, abs(p)) && le(abs(p), 1.2)),
      set2('comb', ([x, y]) => (le(0, x) && le(x, 1) && le(0, y) && le(y, 0.08)) || (le(0, y) && le(y, 1) && [0, 0.2, 0.4, 0.6, 0.8, 1].some(c => le(Math.abs(x - c), 0.03)))),
      set2('cusp y² ≤ x³, x ≤ 1', ([x, y]) => le(y * y, x * x * x) && le(x, 1)),
      set2('closed checkerboard', ([x, y]) => { for (let i = Math.floor(2 * x) - 1; i <= Math.floor(2 * x) + 1; i++) for (let j = Math.floor(2 * y) - 1; j <= Math.floor(2 * y) + 1; j++) if (i >= -2 && i < 2 && j >= -2 && j < 2 && (i + j) % 2 === 0 && le(i / 2, x) && le(x, (i + 1) / 2) && le(j / 2, y) && le(y, (j + 1) / 2)) return true; return false; }),
      set2('random polygon', polygon(9, 0.6)),
      set2('random star', polygon(14, 0.75)),
      set2('small disk |p − (0.5, 0.5)| < 0.2', p => lt(abs([p[0] - 0.5, p[1] - 0.5]), 0.2)),
    ], { label: 'example subsets of ℝ², wild' });
  });

  const functionsR = cached(s => {
    const base = [
      named(x => x, 'x ↦ x'),
      named(x => x * x, 'x ↦ x²'),
      named(x => Math.abs(x), 'x ↦ |x|'),
      named(x => (x < 0 ? 0 : 1), 'step'),
      named(x => Math.sin(x), 'sin'),
      named(x => Math.exp(x), 'exp'),
      named(x => 1 / x, 'x ↦ 1/x'),
      named(x => Math.sqrt(Math.abs(x)), 'x ↦ √|x|'),
      named(x => (x === 0 ? 0 : x * Math.sin(1 / x)), 'x ↦ x·sin(1/x)'),
      named(x => Math.floor(x), 'floor'),
      named(x => { let t = 0; for (let k = 0; k < 12; k++) t += Math.pow(0.5, k) * Math.cos(Math.pow(3, k) * Math.PI * x); return t; }, 'Weierstrass (12 terms)'),
    ];
    if (!s) return MathViz.finite(base, { label: 'example functions ℝ → ℝ' });
    const r = rng(11);
    const coeffs = n => Array.from({ length: n }, () => Math.round((r() * 4 - 2) * 10) / 10);
    const poly = cs => { const f = x => cs.reduce((a, c) => a * x + c, 0); return named(f, `random polynomial (${cs.join(', ')})`); };
    const trig = () => { const a = coeffs(4), b = coeffs(4); return named(x => a.reduce((t, c, k) => t + c * Math.sin((k + 1) * x) + b[k] * Math.cos((k + 1) * x), 0), 'random trigonometric sum'); };
    const takagi = x => { let t = 0; for (let k = 0; k < 30; k++) { const y = Math.pow(2, k) * x; t += Math.abs(y - Math.round(y)) / Math.pow(2, k); } return t; };
    const cantor = x => {
      if (x <= 0) return 0;
      if (x >= 1) return 1;
      let v = 0, w = 0.5;
      for (let k = 0; k < 40; k++) {
        x *= 3;
        const d = Math.floor(x);
        if (d === 1) return v + w;
        if (d === 2) v += w;
        x -= d; w /= 2;
      }
      return v;
    };
    return MathViz.finite([...base,
      poly(coeffs(4)), poly(coeffs(6)), trig(),
      named(takagi, 'Takagi (blancmange)'),
      named(cantor, 'Cantor function'),
      named(x => (x === 0 ? 0 : Math.sin(1 / x)), 'x ↦ sin(1/x)'),
      named(x => (x === 0 ? 0 : x * x * Math.sin(1 / (x * x))), 'x ↦ x²·sin(1/x²)'),
      named(x => Math.cbrt(x), 'x ↦ ∛x'),
      named(x => (x === 0 ? 0 : Math.exp(-1 / (x * x))), 'x ↦ e^(−1/x²)'),
      named(x => x - Math.floor(x), 'sawtooth x − ⌊x⌋'),
      named(x => (Number.isInteger(x) ? 1 : 0), 'spikes at the integers'),
      named(x => (x < 0 ? -1 : x > 0 ? 1 : 0) * Math.sqrt(Math.abs(x)), 'x ↦ sign(x)·√|x|'),
      // The zoo's famous functions that aren't above (Dirichlet, Thomae, x on ℚ, Weierstrass, …).
      ...((MathViz.shared.zoo && MathViz.shared.zoo.functions) || []).filter(f => !/^(Cantor function|sin\(1\/x\)|e\^|x²·sin)/.test(f.label)),
    ], { label: 'example functions ℝ → ℝ, wild' });
  });

  const harmonic = (() => {
    const cache = [0];
    return n => {
      for (let k = cache.length; k <= n && k <= 1e6; k++) cache[k] = cache[k - 1] + 1 / k;
      return n < cache.length ? cache[n] : Math.log(n) + 0.5772156649015329 + 1 / (2 * n);
    };
  })();
  const altHarmonic = (() => {
    const cache = [0];
    return n => {
      for (let k = cache.length; k <= n && k <= 1e6; k++) cache[k] = cache[k - 1] + (k % 2 ? 1 : -1) / k;
      return n < cache.length ? cache[n] : Math.LN2 + (n % 2 ? 1 : -1) / (2 * n);
    };
  })();
  const sequencesR = cached(s => MathViz.finite([
    seq(n => 1 / n, '1/n', 0),
    seq(n => (n % 2 ? -1 : 1), '(−1)ⁿ'),
    seq(n => (n % 2 ? -1 : 1) / n, '(−1)ⁿ/n', 0),
    seq(n => n, 'n'),
    seq(n => Math.sin(n), 'sin(n)'),
    seq(n => Math.sin(n) / n, 'sin(n)/n', 0),
    seq(n => Math.pow(1 + 1 / n, n), '(1 + 1/n)ⁿ', Math.E),
    seq(harmonic, 'Hₙ = 1 + 1/2 + … + 1/n'),
    seq(n => Math.pow(2, -n), '2⁻ⁿ', 0),
    seq(n => Math.pow(n, 1 / n), 'n^(1/n)', 1),
    seq(() => 1, '1', 1),
    ...(s ? [
      seq(n => 1 / Math.sqrt(n), '1/√n (slow)', 0),
      seq(n => Math.log(n) / n, 'log(n)/n', 0),
      seq(n => Math.sin(Math.log(n)), 'sin(log n) (diverges very slowly)'),
      seq(n => ((n & (n - 1)) === 0 ? 1 : 0), '1 at powers of 2, else 0'),
      seq(altHarmonic, '1 − 1/2 + 1/3 − … (alternating harmonic)', Math.LN2),
      seq(n => Math.sqrt(n + 1) - Math.sqrt(n), '√(n+1) − √n', 0),
      seq(n => (n % 2 ? -1 : 1) + 1 / n, '(−1)ⁿ + 1/n'),
      seq(n => n * Math.sin(1 / n), 'n·sin(1/n)', 1),
      seq(n => Math.pow(-1, n) * n / (n + 1), '(−1)ⁿ·n/(n + 1)'),
    ] : []),
  ], { label: s ? 'example sequences, wild' : 'example sequences' }));

  MathViz.define({
    name: 'catalog',
    description: 'Named example objects to quantify over and to illustrate definitions with: subsets of ℝ and ℝ², real functions and sequences. "Try wilder examples" adds pathological ones. Loaded automatically.',
    spaces: {
      Subsets: { doc: 'Subsets(R) or Subsets(R^2): open, closed and half-open intervals or disks, half-planes, an annulus, a punctured disk, points, the whole space and ∅. Wild: Cantor stages, combs, cusps, flowers, random polygons, a disk with half its boundary.', fn: (X = R2) => MathViz.toDomain(X).dim === 2 ? subsetsR2() : subsetsR() },
      Functions: { doc: 'Functions(R): x, x², |x|, a step, sin, exp, 1/x, √|x|, x·sin(1/x), floor and a Weierstrass sum. Wild: Takagi, the Cantor function, sin(1/x), x²·sin(1/x²), e^(−1/x²), random polynomials and more.', fn: () => functionsR() },
      Sequences: { doc: 'Sequences(R): 1/n, (−1)ⁿ, (−1)ⁿ/n, n, sin(n), sin(n)/n, (1 + 1/n)ⁿ, the harmonic sums, 2⁻ⁿ, n^(1/n) and 1. Wild: sin(log n), spikes at powers of 2, 1/log n and more.', fn: () => sequencesR() },
    },
  });
});
