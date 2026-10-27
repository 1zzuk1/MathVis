MathVizLibrary(function metric(MathViz) {
  const { le } = MathViz.ops;
  const named = (fn, label) => { fn.label = label; return fn; };
  const pts = (x, y) => {
    if (!Array.isArray(x) || !Array.isArray(y) || x.length !== y.length) throw MathViz.error('A metric here compares two points of the same space.');
  };
  const pnorm = (x, p) => {
    const v = typeof x === 'number' ? [x] : x;
    if (!Array.isArray(v)) throw MathViz.error('pnorm expects a point.');
    if (p === Infinity) return Math.max(...v.map(Math.abs));
    return Math.pow(v.reduce((s, c) => s + Math.pow(Math.abs(c), p), 0), 1 / p);
  };
  const once = make => { let v = null; return () => v || (v = make()); };
  const diff = (x, y) => x.map((c, i) => c - y[i]);

  const D = {
    euclid: named((x, y) => (pts(x, y), pnorm(diff(x, y), 2)), 'Euclidean'),
    taxicab: named((x, y) => (pts(x, y), pnorm(diff(x, y), 1)), 'taxicab'),
    max: named((x, y) => (pts(x, y), pnorm(diff(x, y), Infinity)), 'maximum'),
    discrete: named((x, y) => (pts(x, y), x.every((c, i) => c === y[i]) ? 0 : 1), 'discrete'),
    sqrt: named((x, y) => (pts(x, y), Math.sqrt(pnorm(diff(x, y), 2))), '√Euclidean'),
    squared: named((x, y) => (pts(x, y), pnorm(diff(x, y), 2) ** 2), 'squared Euclidean'),
    first: named((x, y) => (pts(x, y), Math.abs(x[0] - y[0])), 'first coordinate only'),
    // Uphill costs twice as much as downhill: everything but symmetry.
    lopsided: named((x, y) => (pts(x, y), x.reduce((s, c, i) => s + 2 * Math.max(c - y[i], 0) + Math.max(y[i] - c, 0), 0)), 'lopsided'),
  };
  const metrics = once(() => MathViz.finite([
    named((x, y) => (pts(x, y), pnorm(diff(x, y), 2)), 'Euclidean'),
    named((x, y) => (pts(x, y), pnorm(diff(x, y), 1)), 'taxicab'),
    named((x, y) => (pts(x, y), pnorm(diff(x, y), Infinity)), 'maximum'),
    named((x, y) => (pts(x, y), x.every((c, i) => c === y[i]) ? 0 : 1), 'discrete'),
    named((x, y) => (pts(x, y), Math.sqrt(pnorm(diff(x, y), 2))), '√Euclidean'),
    named((x, y) => (pts(x, y), pnorm(diff(x, y), 2) ** 2), 'squared Euclidean'),
    named((x, y) => (pts(x, y), Math.abs(x[0] - y[0])), 'first coordinate only'),
  ], { label: 'example metrics on ℝ²' }));

  const norms = once(() => MathViz.finite([
    named(x => pnorm(x, 2), 'Euclidean norm'),
    named(x => pnorm(x, 1), '1-norm'),
    named(x => pnorm(x, Infinity), 'maximum norm'),
    named(x => pnorm(x, 3), '3-norm'),
    named(x => 2 * Math.abs(x[0]) + Math.abs(x[1]), '2|x₁| + |x₂|'),
    named(x => Math.abs(x[0]), '|x₁| (a seminorm)'),
    named(x => pnorm(x, 2) ** 2, 'squared length'),
    named(x => pnorm(x, 0.5), '½-“norm”'),
  ], { label: 'example norms on ℝ²' }));

  const unitBall = p => MathViz.space({ label: `unit ball of the ${p === Infinity ? '∞' : MathViz.format(p)}-norm`, window: [[-1.15, 1.15], [-1.15, 1.15]], contains: v => le(pnorm(v, p), 1) });

  const short = x => MathViz.format(+(+x).toPrecision(4));
  const pt = p => '(' + p.map(short).join(', ') + ')';
  // The unit sphere of the 1-norm in the plane, as m points going round.
  const diamond = (m, r = 1) => Array.from({ length: m }, (_, k) => {
    const t = 4 * k / m, side = Math.floor(t), u = t - side;
    const c = [[1 - u, u], [-u, 1 - u], [-(1 - u), -u], [u, -(1 - u)]][side];
    return [c[0] * r, c[1] * r];
  });
  const ballPoly = (p, r, c, m = 240) => Array.from({ length: m }, (_, k) => {
    const a = 2 * Math.PI * k / m, v = [Math.cos(a), Math.sin(a)], L = pnorm(v, p);
    return [c[0] + r * v[0] / L, c[1] + r * v[1] / L];
  });

  /* ---------- contractions and Banach's fixed point theorem (Theorem 10.6) ---------- */
  const dist = (x, y) => (typeof x === 'number' ? Math.abs(x - y) : Math.hypot(...x.map((c, i) => c - y[i])));
  const call = (T, x) => { const v = T(x); return Array.isArray(v) ? v.map(Number) : +v; };
  // sup |T(x) − T(y)| / |x − y| over pairs of points of K: far pairs, and close pairs in every
  // direction (independent samples are rarely close, and the sup is usually approached there).
  function lipschitz(T, K) {
    if (typeof T !== 'function') throw MathViz.error('lipschitz_constant(T, K) needs a map T and a set K.');
    const D = MathViz.toDomain(K);
    MathViz.markInexact();
    const pts = D.sample(160).map(x => (Array.isArray(x) ? x.map(Number) : +x)).filter(x => D.contains(x));
    const w = D.window(), size = Array.isArray(w[0]) ? Math.max(...w.map(([a, b]) => b - a)) : w[1] - w[0];
    const n = Array.isArray(pts[0]) ? pts[0].length : 1;
    const dirs = n === 1 ? [1, -1] : Array.from({ length: 8 }, (_, k) => [Math.cos(k * Math.PI / 4), Math.sin(k * Math.PI / 4)]);
    let best = 0;
    const tryPair = (x, y) => { const d = dist(x, y); if (!(d > 0)) return; let r; try { r = dist(call(T, x), call(T, y)) / d; } catch (e) { return; } if (Number.isFinite(r) && r > best) best = r; };
    for (const x of pts) for (const u of dirs) for (const h of [1e-3, 1e-6]) {
      const y = typeof x === 'number' ? x + u * h * size : x.map((c, i) => c + u[i] * h * size);
      if (D.contains(y)) tryPair(x, y);
    }
    for (let i = 0; i < pts.length; i++) for (let j = i + 1; j < pts.length; j += 7) tryPair(pts[i], pts[j]);
    return best;
  }
  const iterateMap = (T, x0, m) => { let x = Array.isArray(x0) ? x0.map(Number) : +x0; for (let k = 0; k < m; k++) x = call(T, x); return x; };

  MathViz.define({
    name: 'metric',
    requires: ['sequences'],
    description: 'Norms and metrics on ℝⁿ: p-norms, unit balls, balls for any metric, example metrics and norms, convergence, Cauchy sequences and completeness in a metric, equivalence of norms, and the definitions of metric and norm.',
    constants: {
      d_euclid: D.euclid, d_taxicab: D.taxicab, d_max: D.max, d_discrete: D.discrete,
      d_sqrt: D.sqrt, d_squared: D.squared, d_first: D.first, d_lopsided: D.lopsided,
    },
    functions: {
      lipschitz_constant: { doc: 'lipschitz_constant(T, K): an estimate of the smallest L with |T(x) − T(y)| ≤ L·|x − y| for x, y in K, from close pairs in every direction and from far pairs. T is a contraction on K when it is below 1 (Theorem 10.6).', fn: lipschitz },
      fixed_point_iteration: { doc: 'fixed_point_iteration(T, x0, m): x_m, where x_0 = x0 and x_(k+1) = T(x_k): the sequence of the proof of Banach\'s fixed point theorem.', fn: (T, x0, m) => { if (!Number.isInteger(m) || m < 0) throw MathViz.error('fixed_point_iteration(T, x0, m): m is the number of steps, a whole number ≥ 0.'); return iterateMap(T, x0, m); } },
      pnorm: { doc: 'pnorm(x, p): the p-norm (|x₁|ᵖ + … + |xₙ|ᵖ)^(1/p); pnorm(x, inf) is the largest |xᵢ|.', fn: pnorm },
      maxnorm: { doc: 'maxnorm(x): the largest |xᵢ|.', fn: x => pnorm(x, Infinity) },
      taxicab: { doc: 'taxicab(x): |x₁| + … + |xₙ|.', fn: x => pnorm(x, 1) },
    },
    spaces: {
      UnitBall: { doc: 'UnitBall(p): the closed unit ball of the p-norm in ℝ².', fn: unitBall },
      MetricBall: { doc: 'MetricBall(d, c, r): the points x of the plane with d(x, c) < r.', fn: (d, c, r) => MathViz.space({
        label: `ball of radius ${MathViz.format(r)} around ${MathViz.format(c)} for ${MathViz.format(d)}`,
        window: [[c[0] - 2 * r, c[0] + 2 * r], [c[1] - 2 * r, c[1] + 2 * r]],
        contains: x => MathViz.ops.lt(d(x, c), r),
      }) },
      Metrics: { doc: 'Metrics(R^2): Euclidean, taxicab, maximum, discrete, √Euclidean, squared Euclidean and first-coordinate distances.', fn: () => metrics() },
      Norms: { doc: 'Norms(R^2): p-norms for p = 1, 2, 3, ∞, a weighted norm, a seminorm, the squared length and the ½-“norm”.', fn: () => norms() },
    },
    views: {
      banach: {
        doc: 'banach(T, x0, K) iterates x ↦ T(x) from x0 (Theorem 10.6) and plots the distance to the fixed point on a log scale against the a-priori bound κᵐ/(1 − κ)·|x₀ − T(x₀)|, with κ the Lipschitz constant of T on K. For a map of the line it also draws the iteration as a staircase between the graph of T and the diagonal; for a map of the plane, the path of the iterates.',
        render(ctx, T, x0, K) {
          if (typeof T !== 'function') throw MathViz.error('banach(T, x0, K) needs a map, a starting point and the set it contracts.');
          const M = Math.round(ctx.param('steps', { min: 5, max: 80, step: 1, value: 30 }));
          const xs = [Array.isArray(x0) ? x0.map(Number) : +x0];
          for (let m = 0; m < 200; m++) xs.push(call(T, xs[xs.length - 1]));
          const star = xs[xs.length - 1], scalar = typeof star === 'number';
          const kappa = K !== undefined ? lipschitz(T, K) : NaN;
          const d0 = dist(xs[0], xs[1]);
          if (scalar) {
            const all = xs.slice(0, M + 1), lo = Math.min(...all, star) - 0.2, hi = Math.max(...all, star) + 0.2;
            const fig = ctx.figure({ x: [lo, hi], y: [lo, hi], square: true });
            fig.curve(x => call(T, x), { color: 'c1', width: 2 });
            fig.curve(x => x, { color: 'faint', width: 1 });
            const stair = [[xs[0], xs[0]]];
            for (let m = 0; m < M; m++) { stair.push([xs[m], xs[m + 1]]); stair.push([xs[m + 1], xs[m + 1]]); }
            fig.curve(stair, { color: 'c2', width: 1.3 });
            fig.points([[star, star]], { color: 'ink', r: 5 });
            ctx.legend([{ label: 'T', color: 'c1' }, { label: 'y = x', color: 'faint' }, { label: 'x ↦ T(x), step by step', color: 'c2' }]);
          } else {
            const all = xs.slice(0, M + 1);
            const xsr = all.map(q => q[0]), ysr = all.map(q => q[1]), pad = 0.1 * Math.max(Math.max(...xsr) - Math.min(...xsr), Math.max(...ysr) - Math.min(...ysr), 0.2);
            const fig = ctx.figure({ x: [Math.min(...xsr) - pad, Math.max(...xsr) + pad], y: [Math.min(...ysr) - pad, Math.max(...ysr) + pad], square: true });
            fig.curve(all, { color: 'c2', width: 1.3 });
            fig.points(all, { color: 'c2', r: 3 });
            fig.points([star], { color: 'ink', r: 5 });
            ctx.legend([{ label: 'x₀, x₁, x₂, …', color: 'c2' }, { label: 'the fixed point', color: 'ink' }]);
          }
          // The error against the bound, on a log scale.
          const err = xs.slice(0, M + 1).map((x, m) => [m, Math.log10(Math.max(dist(x, star), 1e-17))]);
          const fig2 = ctx.figure({ x: [0, M], xlabel: 'm', ylabel: 'log₁₀ |xₘ − x*|', height: 220 });
          fig2.points(err, { color: 'c2', r: 3 });
          if (kappa < 1 && d0 > 0) fig2.curve(Array.from({ length: M + 1 }, (_, m) => [m, Math.log10(Math.max(kappa ** m / (1 - kappa) * d0, 1e-17))]), { color: 'c3', width: 1.5, dash: [5, 3] });
          ctx.legend([{ label: 'distance to the fixed point', color: 'c2' }, ...(kappa < 1 ? [{ label: 'bound κᵐ/(1 − κ)·|x₀ − T(x₀)|', color: 'c3' }] : [])]);
          const sp = v => (scalar ? short(v) : pt(v));
          if (K === undefined) ctx.note(`Fixed point ≈ ${sp(star)}. Give the set T contracts (banach(T, x0, K)) to compare with the bound of Theorem 10.6.`);
          else if (kappa < 1) ctx.status('ok', `κ ≈ ${short(kappa)} < 1 on ${MathViz.format(K)}: a contraction. The iterates converge to the fixed point ${sp(star)}, at least as fast as κᵐ.`);
          else ctx.status('info', `κ ≈ ${short(kappa)} ≥ 1 on ${MathViz.format(K)}: T is not a contraction there, so Theorem 10.6 promises nothing${dist(call(T, star), star) < 1e-9 ? ` (here the iterates still settle at ${sp(star)})` : ''}.`);
        },
      },
      norm_convergence: {
        doc: 'norm_convergence(s, a) shows a sequence of the plane converging to a (worked out from s when left out) with the ε-balls around a for the 1-, 2- and ∞-norms (diamond, disk, square), and from which index N(ε) the terms stay inside each. Drag ε: the three N(ε) differ, but each is finite exactly when the others are (Theorem 6.3).',
        render(ctx, s, lim) {
          if (typeof s !== 'function') throw MathViz.error('norm_convergence(s, a) needs a sequence of points and its limit, such as norm_convergence(k => (cos(k)/k, sin(k)/k), (0, 0)).');
          const eps = ctx.param('ε', { min: 0.005, max: 1, step: 0.005, value: 0.2 });
          const K = 20000, terms = [];
          for (let k = 1; k <= K; k++) terms.push(s(k).map(Number));
          if (!terms.every(t => t.length === 2 && t.every(Number.isFinite))) throw MathViz.error('norm_convergence draws sequences of points of the plane.');
          let a = lim !== undefined ? lim : MathViz.lim(s);
          if (!Array.isArray(a) || !a.every(Number.isFinite)) a = terms[K - 1];
          a = a.map(Number);
          const norms = [[1, 'c1', '1-norm (diamond)'], [2, 'c2', '2-norm (disk)'], [Infinity, 'c3', '∞-norm (square)']];
          const Ns = norms.map(([p]) => { let last = 0; terms.forEach((t, i) => { if (pnorm([t[0] - a[0], t[1] - a[1]], p) >= eps) last = i + 1; }); return last + 1; });
          const shown = terms.slice(0, Math.max(60, Math.min(400, Math.max(...Ns.filter(n => n <= K)) + 20)));
          const xs = shown.map(t => t[0]).concat(a[0] - eps * 1.1, a[0] + eps * 1.1), ys = shown.map(t => t[1]).concat(a[1] - eps * 1.1, a[1] + eps * 1.1);
          const fig = ctx.figure({ x: [Math.min(...xs), Math.max(...xs)], y: [Math.min(...ys), Math.max(...ys)], square: true });
          norms.forEach(([p, color]) => fig.poly(ballPoly(p, eps, a), { color, alpha: 0.08, stroke: color }));
          fig.curve(shown, { color: 'faint', width: 1 });
          fig.points(shown, { color: 'muted', r: 2 });
          norms.forEach(([p, color], j) => { if (Ns[j] <= shown.length) fig.points([shown[Ns[j] - 1]], { color, r: 5 }); });
          fig.points([a], { color: 'ink', r: 4 });
          ctx.legend(norms.map(([, color, label], j) => ({ label: `${label}: N = ${Ns[j] > K ? '> ' + K : Ns[j]}`, color })));
          ctx.note(`Limit ${pt(a)}. For ε = ${short(eps)} the terms stay within ε from N₁ = ${Ns[0] > K ? '> ' + K : Ns[0]} on in the 1-norm, N₂ = ${Ns[1] > K ? '> ' + K : Ns[1]} in the 2-norm and N∞ = ${Ns[2] > K ? '> ' + K : Ns[2]} in the ∞-norm. Since ‖x‖∞ ≤ ‖x‖₂ ≤ ‖x‖₁ ≤ 2‖x‖∞ in the plane, the ∞-norm's N for ε/2 works for the 1-norm and ε (Question 6.1).`);
        },
      },
      equivalent_norms: {
        doc: 'equivalent_norms(N) draws the unit ball of a norm N of the plane between two diamonds (balls of the 1-norm): γ‖x‖₁ ≤ N(x) ≤ Γ‖x‖₁ with γ and Γ the smallest and largest value of N on the 1-sphere, which is compact, so both are attained (the proof of Theorem 7.16). For something that is not a norm, γ can be 0.',
        render(ctx, N) {
          if (typeof N !== 'function') throw MathViz.error('equivalent_norms(N) needs a function of a point, such as x => sqrt(x[1]^2 + 3*x[2]^2).');
          const val = x => { try { return +N(x); } catch (e) { return NaN; } };
          const sph = diamond(1440), vals = sph.map(val);
          let gi = 0, Gi = 0;
          vals.forEach((v, i) => { if (v < vals[gi]) gi = i; if (v > vals[Gi]) Gi = i; });
          const g = vals[gi], G = vals[Gi];
          // Homogeneous? N(t x) = |t| N(x) on a few points.
          const homog = [0.5, 2, -3].every(t => sph.filter((_, i) => i % 97 === 0).every(x => Math.abs(val(x.map(c => t * c)) - Math.abs(t) * val(x)) <= 1e-9 * Math.max(1, Math.abs(t * val(x)))));
          const R = Math.min(5, 1.25 / Math.max(g, 0.2));
          const fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true });
          fig.region(MathViz.space({ label: 'unit ball of N', window: [[-R, R], [-R, R]], contains: x => val(x) <= 1 }), { color: 'c1', alpha: 0.35 });
          if (G > 0) fig.poly(diamond(4, 1 / G), { color: 'c2', alpha: 0.05, stroke: 'c2' });
          if (g > 1e-9) fig.poly(diamond(4, 1 / g), { color: 'c3', alpha: 0.03, stroke: 'c3' });
          fig.points([sph[gi]], { color: 'c3', r: 5 });
          fig.points([sph[Gi]], { color: 'c2', r: 5 });
          fig.poly(diamond(4, 1), { color: 'faint', alpha: 0, stroke: 'faint' });
          ctx.legend([{ label: 'N(x) ≤ 1', color: 'c1' }, { label: `‖x‖₁ ≤ 1/Γ: inside`, color: 'c2' }, { label: `‖x‖₁ ≤ 1/γ: outside`, color: 'c3' }]);
          if (!(g > 1e-9)) ctx.status('fail', `N vanishes at ${pt(sph[gi])} on the 1-sphere, so N(x) ≥ γ‖x‖₁ fails for every γ > 0: N is not a norm (it is 0 at a point other than 0).`);
          else if (!homog) ctx.status('fail', `N(tx) ≠ |t|·N(x): N is not a norm, and the bounds γ = ${short(g)}, Γ = ${short(G)} hold only on the 1-sphere itself.`);
          else ctx.status('ok', `${short(g)}·‖x‖₁ ≤ N(x) ≤ ${short(G)}·‖x‖₁ for every x: N is equivalent to the 1-norm.`);
          ctx.note(`γ = min N on the 1-sphere = ${short(g)} at ${pt(sph[gi])}; Γ = max = ${short(G)} at ${pt(sph[Gi])}. The 1-sphere is closed and bounded, hence compact, and N is continuous, so the minimum γ is attained, at a point x* ≠ 0; that is why γ > 0 for a norm.`);
        },
      },
      unitballs: {
        doc: 'unitballs() overlays the unit balls of the p-norms; drag p to morph between them.',
        render(ctx) {
          const p = ctx.param('p', { min: 0.3, max: 8, step: 0.05, value: 2 });
          const fig = ctx.figure({ x: [-1.3, 1.3], y: [-1.3, 1.3], square: true });
          [[1, 'c2'], [Infinity, 'c3']].forEach(([q, color]) => fig.region(unitBall(q), { color, alpha: 0.14 }));
          fig.region(unitBall(p), { color: 'c1', alpha: 0.4 });
          ctx.legend([{ label: `p = ${MathViz.format(p)}`, color: 'c1' }, { label: 'p = 1', color: 'c2' }, { label: 'p = ∞', color: 'c3' }]);
          ctx.note(p < 1 ? 'For p < 1 the ball is not convex, so the p-“norm” breaks the triangle inequality.' : 'For p ≥ 1 every unit ball is convex; it grows from the diamond (p = 1) to the square (p = ∞).');
        },
      },
    },
    notation: `
# d is a metric on X: distances are at least 0, zero exactly between equal points, symmetric, and satisfy the triangle inequality.
# examples: d in Metrics(R^2), X in {(-1..1)^2}
def is_metric(d: Fun, X: Set) := forall x, y, z in X: d(x, y) >= 0 and (d(x, y) = 0 <-> x = y) and d(x, y) = d(y, x) and d(x, z) <= d(x, y) + d(y, z)

# N is a norm on X: positive away from 0, scales with |c|, and satisfies the triangle inequality.
# examples: N in Norms(R^2), X in {(-2..2)^2}
def is_norm(N: Fun, X: Set) := forall x, y in X, c in [-2, 2]: N(x) >= 0 and (N(x) = 0 <-> x = (0, 0)) and N(c*x) = |c|*N(x) and N(x + y) <= N(x) + N(y)

# A metric space: a distance d on X that is zero exactly on the diagonal, symmetric, and obeys the
# triangle inequality. (Nonnegativity follows from the others: try to find an example that breaks
# only that one.)
# examples: MetricSpace((-1..1)^2, d_euclid), MetricSpace((-1..1)^2, d_taxicab), MetricSpace((-1..1)^2, d_discrete), MetricSpace((-1..1)^2, d_sqrt), MetricSpace((-1..1)^2, d_squared), MetricSpace((-1..1)^2, d_first), MetricSpace((-1..1)^2, d_lopsided)
structure MetricSpace(X: Set, d: Fun) where
  nonnegative: forall x, y in X: d(x, y) >= 0
  identity: forall x, y in X: d(x, y) = 0 <-> x = y
  symmetric: forall x, y in X: d(x, y) = d(y, x)
  triangle: forall x, y, z in X: d(x, z) <= d(x, y) + d(y, z)

# s converges to a in the metric d: for every ε the terms are eventually within distance ε of a (Definition 6.1).
# examples: d in {d_euclid, d_taxicab, d_discrete}, s in {k => (1/k, 1), k => (1, 1)}, a in {(0, 1), (1, 1)}
def converges_in(d: Fun, s, a) := forall ε in (0, 1]: exists N in 1..10^12: forall k in N..10*N: d(s(k), a) < ε

# s is a Cauchy sequence for the metric d (Definition 6.5).
# examples: d in {d_euclid, d_discrete}, s in {k => (1/k, 1), k => (1, 1), k => ((-1)^k, 0)}
def cauchy_in(d: Fun, s) := forall ε in (0, 1]: exists N in 1..10^12: forall k, m in N..10*N: d(s(k), s(m)) < ε

# X is complete (with the usual distance): every Cauchy sequence in X converges to a point of X (Definition 6.6).
# examples: X in {Icc(0, 1), Ioc(0, 1), {p in R^2 | |p| <= 1}, {p in R^2 | |p| < 1}}
def complete(X: Set) := forall s in Seq(X): cauchy(s) -> convergent(s) and lim(s) in X

# The discrete metric is different: only sequences that end up constant converge.
conjecture discrete_same_limits: forall s in Seq(R^2): convergent(s) -> converges_in(d_discrete, s, lim(s))

# The norms of ℝ² compared: ‖x‖∞ ≤ ‖x‖₂ ≤ ‖x‖₁ ≤ 2‖x‖∞ (all three proved exactly).
lemma pnorm_chain: forall x, y in R: max(|x|, |y|) <= sqrt(x^2 + y^2) and sqrt(x^2 + y^2) <= |x| + |y| and |x| + |y| <= 2*max(|x|, |y|)

# A closed interval is complete: every Cauchy sequence in it converges to a point of it.
lemma closed_interval_complete: complete(Icc(0, 1))

# A set missing a limit point is not complete: 1/n is Cauchy in (0, 1] but its limit 0 is missing.
conjecture half_open_complete: complete(Ioc(0, 1))

# Young's inequality (Lemma 5.8): ab ≤ aᵖ/p + b^q/q when 1/p + 1/q = 1.
lemma young: forall a, b in [0, 3], p in [1.1, 4]: a*b <= a^p/p + b^(p/(p - 1))*(p - 1)/p

# Hölder's inequality (5.9): |⟨x, y⟩| ≤ ‖x‖ₚ‖y‖_q when 1/p + 1/q = 1; Cauchy–Schwarz is p = q = 2.
lemma holder: forall x, y in [-1, 1]^3, p in [1.1, 4]: |x[1]*y[1] + x[2]*y[2] + x[3]*y[3]| <= pnorm(x, p) * pnorm(y, p/(p - 1))

# Minkowski's inequality (5.12): the triangle inequality for every p-norm, p ≥ 1 …
lemma minkowski: forall x, y in [-1, 1]^3, p in [1, 4]: pnorm(x + y, p) <= pnorm(x, p) + pnorm(y, p)

# … and only for p ≥ 1: below, the unit ball isn't convex.
conjecture minkowski_small_p: forall x, y in [-1, 1]^3, p in [0.3, 0.9]: pnorm(x + y, p) <= pnorm(x, p) + pnorm(y, p)

# The p-norms of ℝⁿ compared (5.14): ‖x‖∞ ≤ ‖x‖_q ≤ ‖x‖ₚ ≤ n^(1/p)·‖x‖∞ for 1 ≤ p ≤ q, here n = 3.
lemma pnorm_bounds: forall x in [-1, 1]^3, p in [1, 4], q in [4, 8]: pnorm(x, inf) <= pnorm(x, q) and pnorm(x, q) <= pnorm(x, p) and pnorm(x, p) <= 3^(1/p) * pnorm(x, inf)

# T is a contraction on K: it shrinks distances by a factor κ < 1 (10.2), estimated from close and far pairs.
# examples: T in {x => cos(x), x => x/2 + 1/4, x => x^2}, K in {Icc(0, 1)}
def contraction(T: Fun, K: Set) := lipschitz_constant(T, K) < 1

# Banach's fixed point theorem (10.6): a contraction of a closed set into itself has a fixed point, and
# the iterates from any start reach it.
lemma banach_fixed_point: forall T in {x => cos(x), x => x/2 + 1/4, x => (1 + x^2)/3}, x0 in [0, 1]: contraction(T, Icc(0, 1)) -> |T(fixed_point_iteration(T, x0, 100)) - fixed_point_iteration(T, x0, 100)| < 1e-9

# The fixed point is unique: two starts end at the same point.
lemma banach_unique: forall T in {x => cos(x), x => x/2 + 1/4}, x0, y0 in [0, 1]: |fixed_point_iteration(T, x0, 100) - fixed_point_iteration(T, y0, 100)| < 1e-9

# Not every map of [0, 1] into itself is a contraction: x² stretches distances near 1.
conjecture all_contractions: forall T in {x => cos(x), x => x/2 + 1/4, x => x^2}: contraction(T, Icc(0, 1))

# In a metric space, |d(x, z) − d(y, z)| ≤ d(x, y) (the reverse triangle inequality).
lemma reverse_triangle: forall M in MetricSpace: forall x, y, z in M.X: |M.d(x, z) - M.d(y, z)| <= M.d(x, y)
`,
  });
});
