MathVizLibrary(function numerics(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const sh = x => fmt(+(+x).toPrecision(6));
  const num = f => x => { const y = +f(x); return Number.isFinite(y) ? y : NaN; };
  const dnum = (f, x) => { const h = 1e-6 * Math.max(1, Math.abs(x)); return (f(x + h) - f(x - h)) / (2 * h); };

  /* ---------- root finding ---------- */
  // Newton's method: xₖ₊₁ = xₖ − f(xₖ)/f′(xₖ); the list of iterates (it stops at a zero derivative).
  const newtonSteps = (f, x0, n = 8) => {
    need(typeof f === 'function' && Number.isFinite(+x0), 'newton_steps(f, x₀, n): Newton\'s method for f from x₀.');
    MathViz.markInexact();
    const g = num(f), xs = [+x0];
    for (let k = 0; k < n; k++) {
      const x = xs[xs.length - 1], d = dnum(g, x);
      if (!Number.isFinite(d) || d === 0) break;
      const y = x - g(x) / d;
      if (!Number.isFinite(y)) break;
      xs.push(y);
      if (Math.abs(y - x) < 1e-15 * Math.max(1, Math.abs(y))) break;
    }
    return xs;
  };
  const bisectSteps = (f, a, b, n = 20) => {
    const g = num(f);
    need(g(a) * g(b) <= 0, `bisection needs a sign change: f(${sh(a)}) and f(${sh(b)}) have the same sign.`);
    MathViz.markInexact();
    const out = [[a, b]];
    for (let k = 0; k < n; k++) {
      const m = (a + b) / 2;
      if (g(a) * g(m) <= 0) b = m; else a = m;
      out.push([a, b]);
    }
    return out;
  };
  const secantSteps = (f, x0, x1, n = 10) => {
    MathViz.markInexact();
    const g = num(f), xs = [+x0, +x1];
    for (let k = 0; k < n; k++) {
      const [a, b] = xs.slice(-2), d = g(b) - g(a);
      if (!d) break;
      xs.push(b - g(b) * (b - a) / d);
      if (Math.abs(xs[xs.length - 1] - b) < 1e-15) break;
    }
    return xs;
  };

  /* ---------- interpolation ---------- */
  const equispaced = (n, a = -1, b = 1) => Array.from({ length: n + 1 }, (_, i) => a + (b - a) * i / n);
  const chebyshev = (n, a = -1, b = 1) => Array.from({ length: n + 1 }, (_, i) => (a + b) / 2 + (b - a) / 2 * Math.cos((2 * i + 1) * Math.PI / (2 * n + 2))).reverse();
  // The interpolating polynomial through (xᵢ, yᵢ), in barycentric form (stable).
  const interpolate = (xs, ys) => {
    need(xs.length === ys.length && xs.length >= 1 && new Set(xs).size === xs.length, 'Interpolation needs distinct nodes, one value for each.');
    const w = xs.map((x, i) => 1 / xs.reduce((p, y, j) => (j === i ? p : p * (x - y)), 1));
    const P = t => {
      let nu = 0, de = 0;
      for (let i = 0; i < xs.length; i++) { if (t === xs[i]) return ys[i]; const c = w[i] / (t - xs[i]); nu += c * ys[i]; de += c; }
      return nu / de;
    };
    P.label = `the polynomial of degree ≤ ${xs.length - 1} through ${xs.length} points`;
    P.arity = 1;
    return P;
  };
  const interpFn = (f, nodes) => { const xs = Array.isArray(nodes) ? nodes.map(Number) : MathViz.toDomain(nodes).values.map(Number); return interpolate(xs, xs.map(num(f))); };
  const maxError = (f, g, a = -1, b = 1) => { MathViz.markInexact(); const F = num(f), G = num(g); let m = 0; for (let k = 0; k <= 2000; k++) { const x = a + (b - a) * k / 2000, e = Math.abs(F(x) - G(x)); if (e > m) m = e; } return m; };
  const runge = Object.assign(x => 1 / (1 + 25 * x * x), { label: '1/(1 + 25x²)', arity: 1 });

  /* ---------- views ---------- */
  function newtonView(ctx, f, x0 = 1) {
    const n = Math.round(ctx.param('steps', { min: 1, max: 10, step: 1, value: 4 }));
    const g = num(f), xs = newtonSteps(f, x0, n);
    const lo = Math.min(...xs.filter(Number.isFinite), x0) - 1, hi = Math.max(...xs.filter(Number.isFinite), x0) + 1;
    const fig = ctx.figure({ x: [Math.max(lo, x0 - 6), Math.min(hi, x0 + 6)], xlabel: 'x' });
    fig.curve([[-1e6, 0], [1e6, 0]], { color: 'faint', track: false });
    fig.curve(g, { color: 'c1', width: 2 });
    for (let k = 0; k + 1 < xs.length; k++) {
      const x = xs[k], y = g(x);
      fig.seg(x, 0, x, y, { color: 'faint', dash: [3, 3] });
      fig.seg(x, y, xs[k + 1], 0, { color: 'c2', width: 1.6 });
      fig.points([[x, y]], { color: 'c2', r: 3 });
    }
    fig.points([[xs[xs.length - 1], 0]], { color: 'ink', r: 4 });
    ctx.table(['k', 'xₖ', 'f(xₖ)', '|xₖ − xₖ₋₁|'], xs.map((x, k) => [String(k), sh(x), fmt(+g(x).toPrecision(3)), k ? fmt(+Math.abs(x - xs[k - 1]).toPrecision(2)) : '']));
    ctx.note('Each step follows the tangent line down to the x-axis. Near a simple root the number of correct digits roughly doubles every step (quadratic convergence); from a bad start it can wander, cycle or fly off.');
  }
  function bisectionView(ctx, f, a, b) {
    const n = Math.round(ctx.param('steps', { min: 0, max: 20, step: 1, value: 5 }));
    const g = num(f), I = bisectSteps(f, a, b, n);
    const pad = (b - a) * 0.15, fig = ctx.figure({ x: [a - pad, b + pad], xlabel: 'x' });
    fig.curve(g, { color: 'c1', width: 2 });
    I.forEach(([l, r], k) => { const y = -0.06 * (k + 1) * Math.max(1e-9, Math.abs(g(a)) + Math.abs(g(b))) / 2; fig.seg(l, y, r, y, { color: k === I.length - 1 ? 'c2' : 'faint', width: k === I.length - 1 ? 3 : 2 }); });
    const [l, r] = I[I.length - 1];
    ctx.note(`After ${n} halvings the root lies in [${sh(l)}, ${sh(r)}], of length ${fmt(+(r - l).toPrecision(3))} = (b − a)/2^${n}: one binary digit per step, slow but sure (the intermediate value theorem keeps a root inside).`);
  }
  function interpolationView(ctx, f = runge, a = -1, b = 1) {
    const n = Math.round(ctx.param('n', { min: 1, max: 30, step: 1, value: 10 }));
    const g = num(f), E = equispaced(n, a, b), C = chebyshev(n, a, b), PE = interpFn(f, E), PC = interpFn(f, C);
    const ys = []; for (let k = 0; k <= 200; k++) ys.push(g(a + (b - a) * k / 200));
    const lo = Math.min(...ys), hi = Math.max(...ys), pad = (hi - lo) * 0.6 + 0.1;
    const clip = P => x => { const y = P(x); return y < lo - pad || y > hi + pad ? NaN : y; };
    const fig = ctx.figure({ x: [a, b], y: [lo - pad, hi + pad], xlabel: 'x' });
    fig.curve(g, { color: 'ink', width: 2, track: false });
    fig.curve(clip(PE), { color: 'c3', width: 1.6, track: false }); fig.points(E.map(x => [x, g(x)]), { color: 'c3', r: 3, track: false });
    fig.curve(clip(PC), { color: 'c2', width: 1.6, track: false }); fig.points(C.map(x => [x, g(x)]), { color: 'c2', r: 3, hollow: true, track: false });
    ctx.legend([{ label: 'f', color: 'ink' }, { label: `equispaced nodes: max error ${fmt(+maxError(f, PE, a, b).toPrecision(3))}`, color: 'c3' }, { label: `Chebyshev nodes: max error ${fmt(+maxError(f, PC, a, b).toPrecision(3))}`, color: 'c2' }]);
    ctx.note('With equally spaced nodes the interpolating polynomials of 1/(1 + 25x²) swing wildly near the ends as n grows (Runge\'s phenomenon); nodes bunched towards the ends like cos((2i + 1)π/(2n + 2)) make the error shrink.');
  }

  MathViz.define({
    name: 'numerics',
    description: 'Numerical methods: Newton\'s method, bisection and the secant method with every iterate, polynomial interpolation through equispaced or Chebyshev nodes, maximum errors, Runge\'s function; views of Newton\'s tangents, the shrinking bisection intervals and Runge\'s phenomenon, and lemmas on how fast they converge.',
    functions: {
      newton_steps: { doc: 'newton_steps(f, x₀, n): x₀, x₁, …, xₙ with xₖ₊₁ = xₖ − f(xₖ)/f′(xₖ) (derivative estimated).', fn: newtonSteps },
      newton_root: { doc: 'newton_root(f, x₀): the root Newton\'s method reaches from x₀ after up to 50 steps.', fn: (f, x0) => { const xs = newtonSteps(f, x0, 50); return xs[xs.length - 1]; } },
      bisection_steps: { doc: 'bisection_steps(f, a, b, n): the intervals [a, b], then the half containing a sign change, n times.', fn: bisectSteps },
      bisection_root: { doc: 'bisection_root(f, a, b): the midpoint after 60 halvings of [a, b] (f(a) and f(b) of opposite signs).', fn: (f, a, b) => { const I = bisectSteps(f, a, b, 60); const [l, r] = I[I.length - 1]; return (l + r) / 2; } },
      secant_steps: { doc: 'secant_steps(f, x₀, x₁, n): the secant method, the tangent replaced by the line through the last two points.', fn: secantSteps },
      equispaced_nodes: { doc: 'equispaced_nodes(n, a, b): the n + 1 points a, a + h, …, b.', fn: equispaced },
      chebyshev_nodes: { doc: 'chebyshev_nodes(n, a, b): the n + 1 Chebyshev points, bunched towards the ends of [a, b].', fn: chebyshev },
      interpolate: { doc: 'interpolate(xs, ys): the polynomial of degree ≤ n through the points (xᵢ, yᵢ), as a function (barycentric formula).', fn: (xs, ys) => interpolate(xs.map(Number), ys.map(Number)) },
      interpolate_fn: { doc: 'interpolate_fn(f, nodes): the polynomial through (x, f(x)) for the given nodes.', fn: interpFn },
      max_error: { doc: 'max_error(f, g, a, b): max |f − g| on [a, b], from 2001 points.', fn: maxError },
      runge: { doc: 'runge(x) = 1/(1 + 25x²): smooth, yet badly interpolated at equispaced nodes (Runge, 1901).', fn: runge },
    },
    views: {
      newton: { doc: 'newton(f, x₀) draws Newton\'s method: from each xₖ the tangent line down to the axis gives xₖ₊₁ (drag the number of steps), with a table of the iterates.', render: newtonView },
      bisection: { doc: 'bisection(f, a, b) draws the nested intervals of the bisection method, each half the length of the one before.', render: bisectionView },
      interpolation: { doc: 'interpolation(f, a, b) compares the interpolating polynomials through equispaced and Chebyshev nodes (drag n); for runge it shows Runge\'s phenomenon.', render: interpolationView },
    },
    notation: `
# Newton's method finds √2 from 1 in five steps.
lemma newton_sqrt2: |newton_steps(x => x^2 - 2, 1, 5)[6] - sqrt(2)| < 1e-12

# Quadratic convergence: each error is at most a constant times the square of the one before.
lemma newton_quadratic: forall k in 1..3: |newton_steps(x => x^2 - 2, 1, 5)[k + 1] - sqrt(2)| <= |newton_steps(x => x^2 - 2, 1, 5)[k] - sqrt(2)|^2

# Bisection halves the interval every step.
lemma bisection_halves: forall n in 1..20: bisection_steps(x => x^3 - 2, 0, 2, n)[n + 1][2] - bisection_steps(x => x^3 - 2, 0, 2, n)[n + 1][1] = 2 / 2^n

# The interpolating polynomial passes through its points.
lemma interpolation_exact_at_nodes: forall n in 1..8, k in 1..n: |interpolate_fn(exp, equispaced_nodes(n, -1, 1))(equispaced_nodes(n, -1, 1)[k]) - exp(equispaced_nodes(n, -1, 1)[k])| < 1e-12

# Runge's phenomenon: for 1/(1 + 25x²) the error at equispaced nodes grows with n, while Chebyshev nodes make it shrink.
lemma runge_phenomenon: max_error(runge, interpolate_fn(runge, equispaced_nodes(16, -1, 1))) > max_error(runge, interpolate_fn(runge, equispaced_nodes(8, -1, 1))) and max_error(runge, interpolate_fn(runge, chebyshev_nodes(16, -1, 1))) < max_error(runge, interpolate_fn(runge, chebyshev_nodes(8, -1, 1)))
`,
  });
});
