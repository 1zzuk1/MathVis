MathVizLibrary(function core(MathViz) {
  const fn = (doc, f) => ({ doc, fn: f });
  const Rn = MathViz.interval(-10, 10, { unbounded: 'both', label: 'ℝ' });
  const N = MathViz.numbers;
  const exactAware = (f, kindSensitive = true) => Object.assign(f, { exactAware: true, kindSensitive });
  // ℚ and ℝ ∖ ℚ: membership needs to know the kind of a number, so sampled values are exact.
  const ratsAndIrrs = () => N.sample(-10, 10, 120);
  const Qspace = MathViz.space({
    kind: 'rationals', label: 'ℚ', kindSensitive: true, dim: 1, scalar: true, numeric: true,
    contains: v => (typeof v === 'number' || N.isExact(v)) && N.isRational(v),
    sample: n => ratsAndIrrs().filter(v => N.kindOf(v) === 'rational').slice(0, Math.max(4, n)),
    random: () => N.rational(Math.round(Math.random() * 200 - 100), 1 + Math.floor(Math.random() * 12)),
    window: () => [-10, 10],
    describe: () => 'ℚ',
  });
  MathViz.shared.Q = Qspace;
  const Ispace = MathViz.space({
    kind: 'irrationals', label: 'ℝ ∖ ℚ', kindSensitive: true, dim: 1, scalar: true, numeric: true,
    contains: v => (typeof v === 'number' || N.isExact(v)) && !N.isRational(v),
    sample: n => ratsAndIrrs().filter(v => N.kindOf(v) === 'irrational').slice(0, Math.max(4, n)),
    random: () => ratsAndIrrs().filter(v => N.kindOf(v) === 'irrational')[0],
    window: () => [-10, 10],
    describe: () => 'ℝ ∖ ℚ',
  });
  MathViz.shared.Irrationals = Ispace;

  MathViz.define({
    name: 'core',
    description: 'Numbers, points, sets and sequences: elementary functions, the spaces ℝ, ℤ, ℕ, ℝⁿ, intervals, balls and Seq(X), limits, and the region view. Every notebook loads it automatically.',
    requires: ['geometry'],
    constants: { pi: Math.PI, 'π': Math.PI, tau: 2 * Math.PI, e: Math.E, inf: Infinity },
    functions: {
      sin: Math.sin, cos: Math.cos, tan: Math.tan,
      asin: Math.asin, acos: Math.acos, atan: Math.atan, atan2: Math.atan2,
      sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
      exp: Math.exp, ln: Math.log, log2: Math.log2,
      log: fn('log(x) is base 10; log(x, b) is base b.', (x, base) => base === undefined ? Math.log10(x) : Math.log(x) / Math.log(base)),
      // A number within 10⁻¹² below 0 counts as 0 (as comparisons do), so √(x + h) is defined when
      // x + h ∈ [0, 1] holds only up to that tolerance.
      sqrt: fn('sqrt(x) = √x. Exact for exact rationals: √(1/2) is √2/2, an irrational.', exactAware(x => MathViz.ops.pow(typeof x === 'number' && x < 0 && x >= -1e-12 ? 0 : x, MathViz.numbers.rational(1, 2)), false)),
      cbrt: Math.cbrt,
      is_rational: fn('is_rational(x): whether x is rational. Exact for the exact numbers that claims about rationality are sampled with; for other numbers, a guess (a fraction with denominator up to 1000).', exactAware(x => N.isRational(x))),
      denominator: fn('denominator(x): q when x = p/q in lowest terms, 0 when x is irrational.', exactAware(x => N.denominator(x))),
      floor: Math.floor, ceil: Math.ceil, round: Math.round, sign: Math.sign,
      min: Math.min, max: Math.max, hypot: Math.hypot,
      abs: fn('abs(x) = |x|: absolute value of a number, length of a point.', x => MathViz.ops.abs(x)),
      defined: fn('defined(x): false when x is undefined (as for a divergent limit), true otherwise.', x => !(typeof x === 'number' ? Number.isNaN(x) : Array.isArray(x) ? x.some(v => typeof v === 'number' && Number.isNaN(v)) : x === undefined)),
      len: fn('len(v): the number of entries of a list or point, or of elements of a finite set.', v => {
        if (Array.isArray(v)) return v.length;
        if (MathViz.isSet(v)) return MathViz.ops.abs(v);
        throw MathViz.error('len expects a list, a point or a finite set.');
      }),
      dist: fn('dist(x, y) = |x − y|.', (x, y) => MathViz.ops.abs(MathViz.ops.sub(x, y))),
      lim: fn('lim(s): the limit of a sequence, or undefined if it diverges. Sequences drawn from Seq(X) know their limit exactly; others are estimated numerically.', s => MathViz.lim(s)),
      convergent: fn('convergent(s): whether a sequence converges.', s => MathViz.convergent(s)),
      complement: fn('complement(S): everything in S\'s space (ℝ, ℝⁿ, …) that is not in S.', S => MathViz.complement(S)),
      union: fn('union(A, B) = A ∪ B.', (A, B) => MathViz.ops.union(MathViz.toDomain(A), MathViz.toDomain(B))),
      intersect: fn('intersect(A, B) = A ∩ B.', (A, B) => MathViz.ops.inter(MathViz.toDomain(A), MathViz.toDomain(B))),
    },
    domains: {
      R: fn('ℝ, the real numbers (sampled on [−10, 10]). R[a, b] is the interval [a, b].', (a, b) => a === undefined ? Rn : MathViz.interval(a, b)),
      Z: fn('ℤ, the integers (sampled on −50..50). Z[a, b] is a..b.', (a, b) => a === undefined ? MathViz.interval(-50, 50, { integer: true, unbounded: 'both', label: 'ℤ' }) : MathViz.interval(a, b, { integer: true })),
      N: fn('ℕ = {0, 1, 2, …} (sampled on 0..100). N[a, b] is a..b.', (a, b) => a === undefined ? MathViz.interval(0, 100, { integer: true, unbounded: 'above', label: 'ℕ' }) : MathViz.interval(a, b, { integer: true })),
      Q: fn('ℚ, the rational numbers (sampled as exact fractions on [−10, 10]).', () => Qspace),
      Irrationals: fn('ℝ ∖ ℚ, the irrational numbers (sampled as exact irrationals such as √2/3 + 1 and π/4).', () => Ispace),
      Icc: fn('Icc(a, b) = [a, b].', (a, b) => MathViz.interval(a, b)),
      Ico: fn('Ico(a, b) = [a, b).', (a, b) => MathViz.interval(a, b, { hiOpen: true })),
      Ioc: fn('Ioc(a, b) = (a, b].', (a, b) => MathViz.interval(a, b, { loOpen: true })),
      Ioo: fn('Ioo(a, b) = (a, b).', (a, b) => MathViz.interval(a, b, { loOpen: true, hiOpen: true })),
      Ball: fn('Ball(c, r): the open ball of radius r around c, in ℝ or ℝⁿ.', (c, r) => MathViz.ball(c, r, false)),
      ClosedBall: fn('ClosedBall(c, r): the closed ball of radius r around c.', (c, r) => MathViz.ball(c, r, true)),
      Seq: fn('Seq(X): sequences s(1), s(2), … in X. Quantifying over Seq(X) tries sequences that run into X\'s boundary, converge inside X, stay constant or diverge.', X => MathViz.seq(X)),
      Set: MathViz.types.Set,
      Fun: MathViz.types.Fun,
    },
    views: {
      heatmap: {
        doc: 'heatmap(f, r) colors the square [−r, r]² by f(x, y) (or f(p) for a function of a point), with contour lines. Zoom in to see detail.',
        render(ctx, f, r = 2) {
          const call = f.length === 1 || f.arity === 1 ? (x, y) => f([x, y]) : (x, y) => f(x, y);
          const fig = ctx.figure({ x: [-r, r], y: [-r, r], square: true });
          const mix = (a, b, t) => a.map((v, i) => Math.round(v + (b[i] - v) * t));
          fig.raster({
            x: [-r, r], y: [-r, r], nx: 260, ny: 260,
            value: (x, y) => { const v = call(x, y); return typeof v === 'number' ? v : NaN; },
            color: (v, theme, stats, k) => {
              if (!Number.isFinite(v)) return null;
              const m = Math.max(Math.abs(stats.min), Math.abs(stats.max)) || 1;
              const t = Math.max(-1, Math.min(1, v / m));
              const base = theme.rgb('panel');
              const rgb = t < 0 ? mix(base, theme.rgb('c1'), -t) : mix(base, theme.rgb('c2'), t);
              return stats.edge[k] ? [...mix(rgb, theme.rgb('ink'), 0.5), 255] : [...rgb, 255];
            },
            // Contour lines: pixels whose level (value ÷ step, rounded down) differs from a neighbour's.
            stats: (vals, nx, ny) => {
              let min = Infinity, max = -Infinity;
              for (const v of vals) if (Number.isFinite(v)) { if (v < min) min = v; if (v > max) max = v; }
              const span = max - min || 1, raw = span / 12, p = Math.pow(10, Math.floor(Math.log10(raw))), m = raw / p;
              const step = (m < 1.5 ? 1 : m < 3 ? 2 : m < 7 ? 5 : 10) * p;
              const level = v => Number.isFinite(v) ? Math.floor(v / step) : NaN;
              const edge = new Uint8Array(vals.length);
              for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
                const k = j * nx + i, l = level(vals[k]);
                if ((i + 1 < nx && level(vals[k + 1]) !== l) || (j + 1 < ny && level(vals[k + nx]) !== l)) edge[k] = 1;
              }
              return { min, max, step, edge };
            },
          });
          ctx.legend([{ label: 'negative', color: 'c1' }, { label: 'positive', color: 'c2' }, { label: 'contour lines', color: 'ink' }]);
        },
      },
      field: {
        doc: 'field(F, r) draws the vector field F(x, y) (or F(p)) on the square [−r, r]² as arrows.',
        render(ctx, F, r = 2) {
          const call = F.length === 1 || F.arity === 1 ? (x, y) => F([x, y]) : (x, y) => F(x, y);
          const fig = ctx.figure({ x: [-r, r], y: [-r, r], square: true });
          const n = 17, vecs = [];
          for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
            const x = -r + 2 * r * (i + 0.5) / n, y = -r + 2 * r * (j + 0.5) / n, v = call(x, y);
            if (Array.isArray(v) && v.length === 2 && v.every(Number.isFinite)) vecs.push([x, y, v]);
          }
          const big = Math.max(...vecs.map(([, , v]) => Math.hypot(...v)), 1e-12), L = 2 * r / n * 0.9;
          for (const [x, y, v] of vecs) {
            const s = Math.hypot(...v) / big;
            fig.arrow(x, y, x + v[0] / big * L, y + v[1] / big * L, { color: 'c1', width: 1.2, alpha: 0.35 + 0.65 * s });
          }
          ctx.note('Arrow length and darkness show the size of the vector, relative to the largest one shown.');
        },
      },
      region: {
        doc: 'region(S, T, …) shades sets of the line or the plane.',
        render(ctx, ...sets) {
          if (!sets.length) throw MathViz.error('region needs at least one set, as in region(disk).');
          sets = sets.map(s => MathViz.toDomain(s));
          const dims = sets[0].dim;
          if (sets.some(s => s.dim !== dims)) throw MathViz.error('All sets in one region view need the same number of coordinates.');
          const colors = sets.map((_, i) => 'c' + (i % 6 + 1));
          const name = (s, i) => s.label || 'set ' + (i + 1);
          if (dims === 2) {
            const ws = sets.map(s => s.window());
            const x = [Math.min(...ws.map(w => w[0][0])), Math.max(...ws.map(w => w[0][1]))];
            const y = [Math.min(...ws.map(w => w[1][0])), Math.max(...ws.map(w => w[1][1]))];
            const n = 240;
            const vars = sets[0].vars && sets[0].vars.length === 2 ? sets[0].vars : ['x₁', 'x₂'];
            const fig = ctx.figure({ x, y, square: true, xlabel: vars[0], ylabel: vars[1] });
            const hits = fig.raster({
              x, y, nx: n, ny: n, smooth: false,
              value: (px, py) => sets.map(s => s.contains([px, py])),
              color: (inside, theme) => {
                const on = [];
                inside.forEach((h, i) => { if (h) on.push(theme.rgb(colors[i])); });
                if (!on.length) return null;
                const avg = [0, 1, 2].map(c => on.reduce((t, rgb) => t + rgb[c], 0) / on.length);
                return [...avg, on.length > 1 ? 200 : 150];
              },
            });
            const cell = (x[1] - x[0]) * (y[1] - y[0]) / (n * n);
            ctx.legend(sets.map((s, i) => ({
              label: `${name(s, i)}: area ≈ ${MathViz.format(+(hits.filter(h => h[i]).length * cell).toPrecision(3))}`,
              color: colors[i],
            })));
          } else if (dims === 1) {
            const ws = sets.map(s => s.window());
            const x = [Math.min(...ws.map(w => w[0])), Math.max(...ws.map(w => w[1]))];
            const fig = ctx.figure({ x, y: [0, sets.length], height: 48 + 30 * sets.length, yAxis: false });
            sets.forEach((s, i) => fig.raster({
              x, y: [i + 0.2, i + 0.8], nx: 800, ny: 1, smooth: false,
              value: px => s.contains(px),
              color: (v, theme) => v ? [...theme.rgb(colors[i]), 210] : null,
            }));
            ctx.legend(sets.map((s, i) => ({ label: name(s, i), color: colors[i] })));
          } else {
            throw MathViz.error('region draws sets of the line or the plane.');
          }
        },
      },
    },
  });
});
