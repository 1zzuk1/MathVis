MathVizLibrary(function fourier(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const sh = x => fmt(+(+x).toPrecision(4));
  const PI = Math.PI;

  // ∫ over [−π, π] by composite 8-point Gauss–Legendre on 96 panels (jumps at panel ends are exact).
  const GX = [-0.9602898564975363, -0.7966664774136267, -0.525532409916329, -0.1834346424956498, 0.1834346424956498, 0.525532409916329, 0.7966664774136267, 0.9602898564975363];
  const GW = [0.1012285362903763, 0.2223810344533745, 0.3137066458778873, 0.362683783378362, 0.362683783378362, 0.3137066458778873, 0.2223810344533745, 0.1012285362903763];
  const integ = g => {
    const P = 96, h = 2 * PI / P;
    let s = 0;
    for (let k = 0; k < P; k++) { const m = -PI + (k + 0.5) * h; for (let i = 0; i < 8; i++) s += GW[i] * g(m + GX[i] * h / 2); }
    return s * h / 2;
  };
  const num = f => x => { const y = +f(x); return Number.isFinite(y) ? y : 0; };
  const cache = new WeakMap();
  // a₀, a₁, b₁, …: f ~ a₀/2 + Σ aₖ cos kx + bₖ sin kx on [−π, π].
  const coeffs = (f, N) => {
    need(typeof f === 'function', 'Expected a function of x on [−π, π].');
    need(Number.isInteger(N) && N >= 0 && N <= 400, 'The number of terms N is a whole number up to 400.');
    MathViz.markInexact();
    let c = cache.get(f);
    if (!c) cache.set(f, c = { a: [], b: [] });
    const g = num(f);
    for (let k = c.a.length; k <= N; k++) { c.a[k] = integ(x => g(x) * Math.cos(k * x)) / PI; c.b[k] = k ? integ(x => g(x) * Math.sin(k * x)) / PI : 0; }
    return { a: c.a.slice(0, N + 1), b: c.b.slice(0, N + 1) };
  };
  const partial = (f, N) => {
    const { a, b } = coeffs(f, N);
    const S = x => { let s = a[0] / 2; for (let k = 1; k <= N; k++) s += a[k] * Math.cos(k * x) + b[k] * Math.sin(k * x); return s; };
    S.label = `S${N}(${f.label || 'f'})`;
    return S;
  };
  const meanSquare = f => { MathViz.markInexact(); const g = num(f); return integ(x => g(x) ** 2) / PI; };
  const energy = (f, N) => { const { a, b } = coeffs(f, N); return a[0] ** 2 / 2 + a.slice(1).reduce((s, x, i) => s + x * x + b[i + 1] ** 2, 0); };
  const l2error = (f, N) => { const S = partial(f, N), g = num(f); return Math.sqrt(integ(x => (g(x) - S(x)) ** 2) / PI); };

  // Periodic examples on [−π, π].
  const wrap = x => { const y = ((x + PI) % (2 * PI) + 2 * PI) % (2 * PI) - PI; return y; };
  const named = (f, label) => Object.assign(f, { label, arity: 1 });
  const square = named(x => (wrap(x) === 0 || Math.abs(wrap(x)) === PI ? 0 : Math.sign(wrap(x))), 'square wave');
  const saw = named(x => (Math.abs(wrap(x)) === PI ? 0 : wrap(x)), 'sawtooth x on (−π, π)');
  const tri = named(x => Math.abs(wrap(x)), 'triangle wave |x|');
  let CAT = null;
  const catalog = () => CAT || (CAT = MathViz.finite([square, saw, tri, named(x => wrap(x) ** 2, 'x² on [−π, π]'), named(Math.cos, 'cos x'), named(x => Math.sin(3 * x), 'sin 3x'), named(x => Math.exp(Math.cos(x)), 'e^(cos x)'), named(x => (Math.abs(wrap(x)) < PI / 2 ? 1 : 0), 'a pulse')], { label: 'periodic examples' }));

  function seriesView(ctx, f, N0 = 5) {
    const N = Math.round(ctx.param('N', { min: 0, max: 60, step: 1, value: N0 }));
    const S = partial(f, N), g = num(f), { a, b } = coeffs(f, N);
    const row = ctx.row();
    const fig = row.figure({ x: [-PI - 0.3, PI + 0.3], xlabel: 'x' });
    fig.curve(g, { color: 'c1', width: 2, n: 1200 });
    fig.curve(S, { color: 'c2', width: 2, n: 1200 });
    // Overshoot near a jump: the largest |S_N − f| where f is continuous, as Gibbs saw.
    const amp = row.figure({ x: [-0.5, N + 0.5], xlabel: 'k', ylabel: '√(aₖ² + bₖ²)', height: 220 });
    for (let k = 0; k <= N; k++) amp.seg(k, 0, k, k ? Math.hypot(a[k], b[k]) : Math.abs(a[0]) / 2, { color: 'c2', width: 3 });
    row.legend([{ label: 'f', color: 'c1' }, { label: `S${N}: the partial sum with ${N} harmonic${N === 1 ? '' : 's'}`, color: 'c2' }]);
    const err = l2error(f, N);
    let jump = false;
    for (let k = 0; k < 400; k++) { const x = -PI + (k + 0.5) * 2 * PI / 400; if (Math.abs(g(x + 1e-6) - g(x - 1e-6)) > 1e-3) jump = true; }
    ctx.note(`Mean-square error ‖f − S_N‖ = ${sh(err)}.${jump ? ' f jumps, so near the jump S_N overshoots by about 9% of the jump however large N is (the Gibbs phenomenon), even though the mean-square error tends to 0.' : ' The coefficients of a smooth periodic function decay fast, and so does the error.'}`);
  }
  function parsevalView(ctx, f) {
    const N = 40, { a, b } = coeffs(f, N), total = meanSquare(f);
    const cum = [];
    let s = a[0] ** 2 / 2;
    cum.push([0, s]);
    for (let k = 1; k <= N; k++) { s += a[k] ** 2 + b[k] ** 2; cum.push([k, s]); }
    const fig = ctx.figure({ x: [0, N], xlabel: 'N', ylabel: 'a₀²/2 + Σ (aₖ² + bₖ²)' });
    fig.curve([[0, total], [N, total]], { color: 'ink', dash: [5, 3] });
    fig.curve(cum, { color: 'c2', width: 2 }); fig.points(cum, { color: 'c2', r: 2.5 });
    ctx.legend([{ label: 'partial sums of the squared coefficients', color: 'c2' }, { label: `(1/π)∫ f² = ${sh(total)}`, color: 'ink' }]);
    ctx.note(`Bessel: the sums never exceed (1/π)∫f². Parseval: they tend to it. After ${N} terms: ${sh(s)} of ${sh(total)}.`);
  }

  const realFn = v => {
    if (typeof v !== 'function' || v.domainCtor || v.__structure || (v.arity || v.length) > 1) return false;
    try { return [0.37, 1.3, -0.8].every(x => { const y = v(x); return typeof y === 'number' || (y && y.__exact); }); } catch (e) { return false; }
  };
  MathViz.represent({
    name: 'fourier_series', label: 'A sum of waves: its Fourier series on [−π, π]', test: realFn,
    doc: 'f ~ a₀/2 + Σ (aₖ cos kx + bₖ sin kx) on [−π, π] (repeated with period 2π): the function as a combination of pure frequencies. Drag N.',
    render: (ctx, f) => seriesView(ctx, f, 5),
  });

  MathViz.define({
    name: 'fourier',
    requires: ['analysis'],
    description: 'Fourier series on [−π, π]: coefficients, partial sums, mean-square errors, Bessel\'s inequality and Parseval\'s identity, the Gibbs phenomenon at jumps, periodic examples (square, sawtooth and triangle waves), even functions said two ways, and views of the partial sums and of the energy in the coefficients.',
    functions: {
      fourier_a: { doc: 'fourier_a(f, k): aₖ = (1/π)∫ f(x) cos kx dx over [−π, π].', fn: (f, k) => coeffs(f, k).a[k] },
      fourier_b: { doc: 'fourier_b(f, k): bₖ = (1/π)∫ f(x) sin kx dx over [−π, π].', fn: (f, k) => coeffs(f, k).b[k] },
      fourier_partial: { doc: 'fourier_partial(f, N): the partial sum S_N f(x) = a₀/2 + Σₖ₌₁ᴺ (aₖ cos kx + bₖ sin kx), as a function.', fn: partial },
      fourier_energy: { doc: 'fourier_energy(f, N): a₀²/2 + Σₖ₌₁ᴺ (aₖ² + bₖ²), which increases to (1/π)∫ f² (Parseval).', fn: energy },
      mean_square: { doc: 'mean_square(f): (1/π)∫ f² over [−π, π].', fn: meanSquare },
      fourier_error: { doc: 'fourier_error(f, N): the mean-square distance ‖f − S_N f‖ = √((1/π)∫ (f − S_N f)²).', fn: l2error },
      square_wave: { doc: 'square_wave(x): −1 on (−π, 0), 1 on (0, π), 0 at the jumps, repeated with period 2π.', fn: square },
      sawtooth: { doc: 'sawtooth(x): x on (−π, π), repeated with period 2π.', fn: saw },
      triangle_wave: { doc: 'triangle_wave(x): |x| on [−π, π], repeated with period 2π.', fn: tri },
    },
    spaces: {
      Periodic: { doc: 'Periodic: example functions on [−π, π]: square, sawtooth and triangle waves, x², cos x, sin 3x, e^(cos x) and a pulse.', fn: catalog },
    },
    views: {
      fourier_series: { doc: 'fourier_series(f, N) draws f with its Fourier partial sum S_N (drag N) and the amplitudes √(aₖ² + bₖ²) of its harmonics. At a jump the overshoot stays near 9% (Gibbs).', render: seriesView },
      parseval: { doc: 'parseval(f) draws a₀²/2 + Σ (aₖ² + bₖ²) as more terms are added, rising to (1/π)∫ f² (Bessel\'s inequality and Parseval\'s identity).', render: parsevalView },
    },
    notation: `
# f is even on [−π, π], two ways: by its values, f(−x) = f(x); by its Fourier series, which has only cosines (every bₖ is 0).
# examples: f in Periodic
concept even_function(f) where
  values: forall x in [-pi, pi]: |f(-x) - f(x)| < 1e-9
  cosines_only: forall k in 1..8: |fourier_b(f, k)| < 1e-6

# f is odd on [−π, π], two ways: f(−x) = −f(x), or only sines (every aₖ is 0).
# examples: f in Periodic
concept odd_function(f) where
  values: forall x in (-pi, pi): |f(-x) + f(x)| < 1e-9
  sines_only: forall k in 0..8: |fourier_a(f, k)| < 1e-6

# Bessel's inequality: the energy in the first N coefficients never exceeds that of f.
lemma bessel: forall f in Periodic, N in 1..12: fourier_energy(f, N) <= mean_square(f) + 1e-9

# The partial sums get closer in mean square as N grows.
lemma error_decreases: forall f in Periodic, N in 1..10: fourier_error(f, N + 1) <= fourier_error(f, N) + 1e-9

# Riemann–Lebesgue: the coefficients tend to 0.
lemma riemann_lebesgue: forall f in Periodic: |fourier_a(f, 40)| + |fourier_b(f, 40)| < 0.06

# Uniform convergence fails at a jump: the partial sums of the square wave overshoot by about 9% of the jump 2.
lemma gibbs: forall N in {10, 20, 40}: max x in [0, 0.5]: fourier_partial(square_wave, N)(x) > 1.15
`,
  });
});
