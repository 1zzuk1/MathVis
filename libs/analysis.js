MathVizLibrary(function analysis(MathViz) {
  const simpson = (f, a, b, n = 2000) => {
    if (n % 2) n++;
    const h = (b - a) / n;
    let s = f(a) + f(b);
    for (let k = 1; k < n; k++) s += (k % 2 ? 4 : 2) * f(a + k * h);
    return s * h / 3;
  };
  // Adaptive 8-point Gauss–Legendre: splits where a piece and its two halves disagree.
  const GX = [-0.9602898564975363, -0.7966664774136267, -0.5255324099163290, -0.1834346424956498, 0.1834346424956498, 0.5255324099163290, 0.7966664774136267, 0.9602898564975363];
  const GW = [0.1012285362903763, 0.2223810344533745, 0.3137066458778873, 0.3626837833783620, 0.3626837833783620, 0.3137066458778873, 0.2223810344533745, 0.1012285362903763];
  const gl = (f, a, b) => { const m = (a + b) / 2, h = (b - a) / 2; let t = 0; for (let i = 0; i < 8; i++) t += GW[i] * f(m + h * GX[i]); return t * h; };
  function adaptive(f, a, b, tol = 1e-11) {
    if (a === b) return 0;
    if (a > b) return -adaptive(f, b, a, tol);
    let budget = 3000;
    const rec = (lo, hi, whole, t, d) => { const m = (lo + hi) / 2, L = gl(f, lo, m), R = gl(f, m, hi); if (--budget < 0 || d > 40 || Math.abs(L + R - whole) <= t * Math.max(1, Math.abs(L + R))) return L + R; return rec(lo, m, L, t / 1.6, d + 1) + rec(m, hi, R, t / 1.6, d + 1); };
    return rec(a, b, gl(f, a, b), tol, 0);
  }
  const fmt = MathViz.format;
  // n-th derivative by central differences, with a step suited to the order.
  const nthDeriv = (f, a, n) => {
    if (n === 0) return f(a);
    const h = Math.pow(1e-16, 1 / (n + 2)) * Math.max(1, Math.abs(a)) * 4;
    let s = 0, binom = 1;
    for (let k = 0; k <= n; k++) {
      s += (k % 2 ? -1 : 1) * binom * f(a + (n / 2 - k) * h);
      binom = binom * (n - k) / (k + 1);
    }
    return s / Math.pow(h, n);
  };
  const polyLabel = cs => {
    const deg = cs.length - 1;
    const terms = cs.map((c, i) => [c, deg - i]).filter(([c]) => c !== 0).map(([c, p]) => {
      const mag = Math.abs(c) === 1 && p > 0 ? '' : fmt(+Math.abs(c).toPrecision(4));
      return { neg: c < 0, s: mag + (p === 0 ? '' : p === 1 ? 'x' : `x^${p}`) };
    });
    if (!terms.length) return '0';
    return terms.map((t, i) => (i ? (t.neg ? ' − ' : ' + ') : (t.neg ? '−' : '')) + t.s).join('');
  };
  const poly = cs => {
    if (!Array.isArray(cs) || !cs.every(c => typeof c === 'number')) throw MathViz.error('poly expects a list of coefficients, highest power first, as in poly([1, 0, -1]) for x² − 1.');
    const f = x => cs.reduce((acc, c) => acc * x + c, 0);
    f.label = polyLabel(cs);
    f.coeffs = cs;
    return f;
  };
  const taylor = (f, a, n) => {
    // Coefficients of Σ f⁽ᵏ⁾(a)/k! (x − a)ᵏ, expanded so the label shows the polynomial around a.
    const ds = Array.from({ length: n + 1 }, (_, k) => nthDeriv(f, a, k));
    const g = x => { let s = 0, fact = 1, pw = 1; for (let k = 0; k <= n; k++) { if (k) { fact *= k; pw *= x - a; } s += ds[k] / fact * pw; } return s; };
    g.label = `Taylor polynomial of degree ${n} of ${fmt(f)} at ${fmt(a)}`;
    return g;
  };
  // f⁽ᵏ⁾(a)/k!, highest power first (for polyLabel), rounded where they are nearly whole.
  const taylorCoeffs = (f, a, n) => {
    const cs = [];
    let fact = 1;
    for (let k = 0; k <= n; k++) { if (k) fact *= k; const c = nthDeriv(f, a, k) / fact, r = Math.round(c * 1e4) / 1e4; cs.unshift(Math.abs(c - r) < 1e-6 ? r : c); }
    return cs;
  };

  /* ---------- ways of looking at a function ℝ → ℝ (interpret) ---------- */
  const sh = x => fmt(+(+x).toPrecision(4));
  const realFn = v => {
    if (typeof v !== 'function' || v.domainCtor || v.__structure || (v.arity || v.length) > 1) return false;
    let n = 0;
    for (const x of [0.37, 1.3, -0.8]) { try { const y = v(x); if (typeof y === 'number' || (y && y.__exact)) n++; else return false; } catch (e) { /* undefined there */ } }
    return n >= 2;
  };
  const num = f => x => { try { const y = +f(x); return Number.isFinite(y) ? y : NaN; } catch (e) { return NaN; } };
  MathViz.represent({
    name: 'function_graph', label: 'Its graph: a curve in the plane', test: realFn,
    doc: 'The set {(x, f(x))}: each vertical line meets it at most once. Zeros are where it crosses the x-axis.',
    render(ctx, f) {
      const g = num(f), xs = Array.from({ length: 801 }, (_, k) => -4 + k / 100);
      const fig = ctx.figure({ x: [-4, 4], xlabel: 'x' });
      fig.curve(g, { color: 'c1', width: 2 });
      const zeros = [];
      for (let k = 1; k < xs.length; k++) { const a = g(xs[k - 1]), b = g(xs[k]); if (Number.isFinite(a) && Number.isFinite(b) && (a === 0 || a * b < 0) && Math.abs(a - b) < 10) zeros.push(a === 0 ? xs[k - 1] : xs[k - 1] - a * (xs[k] - xs[k - 1]) / (b - a)); }
      fig.points(zeros.map(z => [z, 0]), { color: 'c3', r: 3.5, track: false });
      ctx.note(zeros.length ? `Zeros on [−4, 4] near ${zeros.slice(0, 8).map(sh).join(', ')}${zeros.length > 8 ? ', …' : ''}.` : 'No sign change on [−4, 4].');
    },
  });
  MathViz.represent({
    name: 'function_derivative', label: 'Its derivative: the slope at each point', test: realFn,
    doc: 'f′(x) is the slope of the tangent line at x: the best linear approximation f(x₀) + f′(x₀)(x − x₀). Drag x₀.',
    render(ctx, f) {
      const g = num(f), d = x => (g(x + 1e-5) - g(x - 1e-5)) / 2e-5;
      const x0 = ctx.param('x₀', { min: -3.5, max: 3.5, step: 0.01, value: 0.7 }), y0 = g(x0), m = d(x0);
      const fig = ctx.figure({ x: [-4, 4], xlabel: 'x' });
      fig.curve(g, { color: 'c1', width: 2 });
      fig.curve(d, { color: 'c2', width: 1.5, dash: [5, 3] });
      if (Number.isFinite(y0) && Number.isFinite(m)) { fig.curve([[x0 - 1.5, y0 - 1.5 * m], [x0 + 1.5, y0 + 1.5 * m]], { color: 'ink', width: 1.5, track: false }); fig.points([[x0, y0]], { color: 'ink', r: 4 }); }
      ctx.legend([{ label: 'f', color: 'c1' }, { label: 'f′ (numerical)', color: 'c2' }, { label: `tangent at x₀, slope ${sh(m)}`, color: 'ink' }]);
    },
  });
  MathViz.represent({
    name: 'function_taylor', label: 'Its Taylor polynomials: a power series near a point', test: realFn,
    doc: 'Near a, f(x) ≈ Σ f⁽ᵏ⁾(a)/k! (x − a)ᵏ. Raising the degree n improves the fit near a; how far it reaches depends on f (the radius of convergence).',
    render(ctx, f) {
      const a = ctx.param('a', { min: -2, max: 2, step: 0.05, value: 0 }), n = Math.round(ctx.param('n', { min: 0, max: 6, step: 1, value: 3 }));
      const g = num(f), fig = ctx.figure({ x: [-4, 4], xlabel: 'x' });
      fig.curve(g, { color: 'c1', width: 2 });
      const ys = [];
      for (let k = 0; k <= 160; k++) { const y = g(-4 + k / 20); if (Number.isFinite(y)) ys.push(y); }
      const lo = Math.min(...ys), hi = Math.max(...ys), pad = (hi - lo) * 0.3 + 0.5;
      const clip = h => x => { const y = h(x); return y < lo - pad || y > hi + pad ? NaN : y; };
      for (let k = 0; k < n; k++) fig.curve(clip(taylor(f, a, k)), { color: 'c2', width: 1, alpha: 0.12 + 0.3 * k / Math.max(1, n), track: false });
      fig.curve(clip(taylor(f, a, n)), { color: 'c2', width: 2.2, track: false });
      fig.points([[a, g(a)]], { color: 'ink', r: 4, track: false });
      ctx.legend([{ label: 'f', color: 'c1' }, { label: `Taylor polynomial of degree ${n} at ${sh(a)}`, color: 'c2' }]);
      ctx.note(`T(x) = ${polyLabel(taylorCoeffs(f, a, n)).replace(/x/g, a === 0 ? 'x' : `(x − ${sh(a)})`)}`);
    },
  });
  MathViz.represent({
    name: 'function_area', label: 'The derivative of its area function', test: realFn,
    doc: 'F(x) = ∫₀ˣ f(t) dt is the signed area under f from 0 to x, and F′ = f where f is continuous (the fundamental theorem of calculus).',
    render(ctx, f) {
      const g = num(f), x = ctx.param('x', { min: -3.5, max: 3.5, step: 0.01, value: 1.5 });
      const F = t => adaptive(g, 0, t);
      const row = ctx.row();
      const f1 = row.figure({ x: [-4, 4], xlabel: 't' });
      const pts = [[0, 0]];
      for (let k = 0; k <= 200; k++) { const t = x * k / 200, y = g(t); if (Number.isFinite(y)) pts.push([t, y]); }
      pts.push([x, 0]);
      f1.poly(pts, { color: 'c2', alpha: 0.3 });
      f1.curve(g, { color: 'c1', width: 2 });
      const f2 = row.figure({ x: [-4, 4], xlabel: 'x' });
      f2.curve(t => { const v = F(t); return Number.isFinite(v) ? v : NaN; }, { color: 'c2', width: 2, n: 200 });
      f2.points([[x, F(x)]], { color: 'ink', r: 4 });
      row.legend([{ label: 'f', color: 'c1' }, { label: `F(x) = ∫₀ˣ f = ${sh(F(x))}`, color: 'c2' }]);
    },
  });

  MathViz.define({
    name: 'analysis',
    description: 'Numerical derivatives, integrals, limits and sums, plus the epsdelta and riemann views.',
    functions: {
      // deriv(f) returns a new function, so deriv(f)(x) and plot deriv(f)(x) for x in R both work.
      deriv(f, h = 1e-5) {
        const g = x => (f(x + h) - f(x - h)) / (2 * h);
        g.label = `deriv(${fmt(f)})`;
        return g;
      },
      diff: (f, x, h = 1e-5) => (f(x + h) - f(x - h)) / (2 * h),
      // ∫ₐᵇ f: adaptive Gauss–Legendre; with n given, Simpson's rule with n pieces.
      integral: (f, a, b, n) => (n === undefined ? adaptive(x => +f(x), +a, +b) : simpson(f, a, b, n)),
      // Two-sided numerical limit; undefined when the sides disagree.
      limit(f, a) {
        const left = f(a - 1e-7), right = f(a + 1e-7);
        const tol = 1e-4 * Math.max(1, Math.abs(left), Math.abs(right));
        return Number.isFinite(left) && Math.abs(left - right) <= tol ? (left + right) / 2 : NaN;
      },
      sum(f, a, b) {
        let s = 0;
        for (let k = a; k <= b; k++) s = MathViz.ops.add(s, f(k));
        return s;
      },
      prod(f, a, b) {
        let p = 1;
        for (let k = a; k <= b; k++) p = MathViz.ops.mul(p, f(k));
        return p;
      },
      poly: { doc: 'poly([a, b, c]): the polynomial ax² + bx + c (coefficients highest power first).', fn: poly },
      taylor: { doc: 'taylor(f, a, n): the Taylor polynomial of degree n of f at a, from numerical derivatives (reliable up to n ≈ 6).', fn: taylor },
      nderiv: { doc: 'nderiv(f, a, n): the n-th derivative of f at a, numerically.', fn: nthDeriv },
    },
    views: {
      taylor: {
        doc: 'taylor(f, a, n) draws f with its Taylor polynomials at a; drag n to raise the degree.',
        render(ctx, f, a = 0, n = 3, span = 3) {
          n = ctx.param('degree', { min: 0, max: 8, step: 1, value: n });
          const fig = ctx.figure({ x: [a - span, a + span], xlabel: 'x' });
          const fa = f(a);
          for (let k = 0; k < n; k++) fig.curve(taylor(f, a, k), { color: 'c1', width: 1, alpha: 0.15 + 0.35 * k / Math.max(1, n), track: false });
          fig.curve(f, { color: 'ink', width: 2 });
          fig.curve(taylor(f, a, n), { color: 'c2', width: 2, track: false });
          fig.points([[a, fa]], { color: 'accent', r: 4 });
          ctx.legend([{ label: fmt(f), color: 'ink' }, { label: `degree ${n}`, color: 'c2' }, { label: 'lower degrees', color: 'c1' }]);
        },
      },
      tangent: {
        doc: 'tangent(f, a) draws f with its tangent line at a; drag a along the graph.',
        render(ctx, f, a = 0, lo = -3, hi = 3) {
          a = ctx.param('a', { min: lo, max: hi, step: (hi - lo) / 200, value: a });
          const h = 1e-5, slope = (f(a + h) - f(a - h)) / (2 * h), fa = f(a);
          const fig = ctx.figure({ x: [lo, hi], xlabel: 'x' });
          fig.curve(f, { color: 'ink', width: 2 });
          if (Number.isFinite(slope)) fig.curve(x => fa + slope * (x - a), { color: 'c2', width: 1.6, track: false });
          fig.points([[a, fa]], { color: 'accent', r: 4.5 });
          ctx.note(Number.isFinite(slope) ? `Slope at ${fmt(+a.toPrecision(4))}: ${fmt(+slope.toPrecision(5))}.` : 'The derivative is undefined here.');
        },
      },
      funcseq: {
        doc: 'funcseq(F, a, b) draws the functions F(1), F(2), … on [a, b], for a sequence of functions F; drag n to see more.',
        render(ctx, F, a = -1, b = 1) {
          const n = ctx.param('n', { min: 1, max: 40, step: 1, value: 6 });
          const fig = ctx.figure({ x: [a, b], xlabel: 'x' });
          for (let k = 1; k <= n; k++) fig.curve(F(k), { color: 'c1', width: k === n ? 2.2 : 1, alpha: k === n ? 1 : 0.15 + 0.6 * k / n });
          let sup = 0;
          for (let i = 0; i <= 400; i++) {
            const x = a + (b - a) * i / 400, v = Math.abs(F(n)(x) - F(n + 1)(x));
            if (Number.isFinite(v)) sup = Math.max(sup, v);
          }
          ctx.note(`Darkest: F(${n}). Largest gap between F(${n}) and F(${n + 1}) on the interval: ${fmt(+sup.toPrecision(3))}. If such gaps shrink uniformly, the sequence converges uniformly.`);
        },
      },
      epsdelta: {
        doc: 'epsdelta(f, a, ε) draws the band |f(x) − f(a)| < ε and the widest window |x − a| ≤ δ whose graph stays inside it.',
        render(ctx, f, a, eps = 0.3, span = 1) {
          eps = ctx.param('ε', { min: 0.01, max: 1, step: 0.01, value: eps });
          const L = f(a);
          if (!Number.isFinite(L)) throw MathViz.error('f(a) is undefined, so there is no band to draw.');
          const fits = d => {
            for (let k = 0; k <= 400; k++) {
              const x = a - d + 2 * d * k / 400;
              if (!(Math.abs(f(x) - L) < eps)) return false;
            }
            return true;
          };
          let delta = 0;
          for (let k = 0; k <= 80; k++) {
            const d = span * Math.pow(0.85, k);
            if (fits(d)) { delta = d; break; }
          }
          if (delta && delta < span) {
            let lo = delta, hi = Math.min(span, delta / 0.85);
            for (let k = 0; k < 30; k++) { const mid = (lo + hi) / 2; if (fits(mid)) lo = mid; else hi = mid; }
            delta = lo;
          }
          const fig = ctx.figure({ x: [a - span, a + span], xlabel: 'x', ylabel: 'f(x)' });
          fig.hband(L - eps, L + eps, { color: 'pos', alpha: 0.14 });
          if (delta) fig.vband(a - delta, a + delta, { color: 'accent', alpha: 0.13 });
          fig.curve(f, { color: 'ink', width: 1.6, n: 1400 });
          const outside = [];
          for (let k = 0; k <= 700; k++) {
            const x = a - span + 2 * span * k / 700, y = f(x);
            if (Number.isFinite(y) && !(Math.abs(y - L) < eps)) outside.push([x, y]);
          }
          fig.points(outside, { color: 'neg', r: 1.7 });
          fig.points([[a, L]], { color: 'accent', r: 4.5 });
          ctx.legend([
            { label: `ε-band: |f(x) − f(a)| < ${fmt(eps)}`, color: 'pos' },
            { label: delta ? `δ-window: |x − a| ≤ ${fmt(+delta.toPrecision(4))}` : 'no δ-window found', color: 'accent' },
            { label: 'graph outside the band', color: 'neg' },
          ]);
          ctx.status(delta ? 'ok' : 'fail', delta ? `δ ≈ ${fmt(+delta.toPrecision(3))} works` : 'No δ works for this ε');
        },
      },
      riemann: {
        doc: 'riemann(f, a, b, n) draws n midpoint rectangles under f on [a, b] and compares their total with the integral.',
        render(ctx, f, a, b, n = 8) {
          n = ctx.param('n', { min: 1, max: 120, step: 1, value: n });
          const w = (b - a) / n;
          const fig = ctx.figure({ x: [a, b], xlabel: 'x' });
          let s = 0;
          for (let i = 0; i < n; i++) {
            const y = f(a + (i + 0.5) * w);
            s += y * w;
            fig.rect(a + i * w, 0, a + (i + 1) * w, y, { color: 'accent', alpha: 0.18, stroke: 'accent' });
          }
          fig.curve(f, { color: 'ink', width: 1.8 });
          const I = simpson(f, a, b);
          ctx.note(`Midpoint sum with ${n} rectangles: ${fmt(s)}. Integral: ${fmt(I)}. Difference: ${fmt(s - I)}.`);
        },
      },
    },
  });
});
