MathVizLibrary(function dynamics(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const named = (f, label, meta = {}) => Object.assign(f, { label }, meta);
  const num = v => typeof v === 'number' ? v : Array.isArray(v) ? v.map(num) : v != null && typeof v.valueOf() === 'number' ? +v : v;
  const isVec = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');
  const arity = f => f.arity || f.length;
  const r4 = x => fmt(+(+x).toPrecision(4));
  const pt = p => Array.isArray(p) ? '(' + p.map(r4).join(', ') + ')' : r4(p);
  // A small set reads as its elements; a big one by what it is.
  const setLabel = (xs, what) => !xs.length ? `∅ (no ${what})` : xs.length <= 8 ? `{${xs.map(pt).join(', ')}}` : what;

  /* ---------- differential equations: y' = f(t, y), or y' = f(y) ---------- */

  // The right-hand side as a map on arrays: f(t, y) or, for an autonomous equation, f(y).
  function rhs(f, scalar) {
    need(typeof f === 'function', "The equation is a function: f(t, y) for y' = f(t, y), or f(y).");
    const auto = arity(f) === 1;
    return (t, Y) => {
      const y = scalar ? Y[0] : Y;
      const v = num(auto ? f(y) : f(t, y));
      const out = typeof v === 'number' ? [v] : v;
      need(Array.isArray(out) && out.length === Y.length, `f gives ${fmt(v)}, but y has ${Y.length} component${Y.length === 1 ? '' : 's'}.`);
      return out;
    };
  }

  // Dormand–Prince 5(4) with step control: the knots (t, y, y') of the solution from t0 towards
  // t1, which the dense output interpolates between (cubic Hermite). Stops if y blows up.
  const A = [[], [1 / 5], [3 / 40, 9 / 40], [44 / 45, -56 / 15, 32 / 9], [19372 / 6561, -25360 / 2187, 64448 / 6561, -212 / 729],
    [9017 / 3168, -355 / 33, 46732 / 5247, 49 / 176, -5103 / 18656], [35 / 384, 0, 500 / 1113, 125 / 192, -2187 / 6784, 11 / 84]];
  const C = [0, 1 / 5, 3 / 10, 4 / 5, 8 / 9, 1, 1];
  const E = [71 / 57600, 0, -71 / 16695, 71 / 1920, -17253 / 339200, 22 / 525, -1 / 40];
  function integrate(F, t0, Y0, t1, knots = null, maxSteps = 40000) {
    const dir = Math.sign(t1 - t0) || 1;
    const ks = knots || [{ t: t0, y: Y0, d: F(t0, Y0) }];
    let { t, y, d } = ks[ks.length - 1];
    let h = dir * Math.min(Math.abs(t1 - t) || 1, 0.05 * Math.max(1, Math.abs(t1 - t0)));
    for (let steps = 0; dir * (t1 - t) > 1e-14 * Math.max(1, Math.abs(t)) && steps < maxSteps; steps++) {
      if (dir * (t + h - t1) > 0) h = t1 - t;
      const K = [d];
      for (let s = 1; s < 7; s++) {
        const ys = y.map((v, i) => v + h * A[s].reduce((acc, a, j) => acc + a * K[j][i], 0));
        K.push(F(t + C[s] * h, ys));
      }
      const yn = y.map((v, i) => v + h * A[6].reduce((acc, a, j) => acc + a * K[j][i], 0));
      let err = 0;
      for (let i = 0; i < y.length; i++) {
        const e = h * E.reduce((acc, c, j) => acc + c * K[j][i], 0);
        err = Math.max(err, Math.abs(e) / (1e-10 + 1e-9 * Math.max(Math.abs(y[i]), Math.abs(yn[i]))));
      }
      if (!yn.every(Number.isFinite) || Number.isNaN(err)) {
        if (Math.abs(h) < 1e-12) break;
        h /= 4;
        continue;
      }
      if (err <= 1) {
        t += h; y = yn; d = K[6];
        ks.push({ t, y, d });
        if (y.some(v => Math.abs(v) > 1e12)) { ks.blewUp = t; break; }
      }
      h *= Math.min(5, Math.max(0.2, 0.9 * Math.pow(err || 1e-10, -0.2)));
      if (Math.abs(h) < 1e-13 * Math.max(1, Math.abs(t))) { ks.stuck = t; break; }
    }
    return ks;
  }
  const hermite = (a, b, t) => {
    const h = b.t - a.t, s = (t - a.t) / h, s2 = s * s, s3 = s2 * s;
    return a.y.map((ya, i) => (2 * s3 - 3 * s2 + 1) * ya + (s3 - 2 * s2 + s) * h * a.d[i] + (-2 * s3 + 3 * s2) * b.y[i] + (s3 - s2) * h * b.d[i]);
  };

  // The solution through (t0, y0) as a function of t, integrated on demand in both directions.
  function solution(f, t0, y0) {
    t0 = num(t0); y0 = num(y0);
    const scalar = typeof y0 === 'number';
    need(scalar || isVec(y0), 'The initial value is a number or a point, as in solution(f, 0, (1, 0)).');
    const F = rhs(f, scalar), Y0 = scalar ? [y0] : y0;
    const sides = { 1: [{ t: t0, y: Y0, d: F(t0, Y0) }], [-1]: null };
    sides[-1] = [sides[1][0]];
    const at = t => {
      t = num(t);
      need(typeof t === 'number', 'A solution is evaluated at a time t.');
      MathViz.markInexact();
      const dir = t >= t0 ? 1 : -1, ks = sides[dir];
      if (ks.blewUp !== undefined && dir * (t - ks.blewUp) > 0) return NaN;
      const last = ks[ks.length - 1];
      if (dir * (t - last.t) > 0) integrate(F, t0, Y0, t0 + dir * Math.max(dir * (t - t0) * 1.5, 1), ks);
      const end = ks[ks.length - 1];
      if (dir * (t - end.t) > 1e-12) return NaN;   // blew up or stalled before t
      // Binary search for the knot interval.
      let lo = 0, hi = ks.length - 1;
      while (hi - lo > 1) { const m = (lo + hi) >> 1; if (dir * (ks[m].t - t) <= 0) lo = m; else hi = m; }
      const Y = hi === lo ? ks[lo].y : hermite(ks[lo], ks[hi], t);
      return scalar ? Y[0] : Y;
    };
    return named(at, `the solution of y' = ${fmt(f)} with y(${fmt(t0)}) = ${fmt(y0)}`, { arity: 1 });
  }
  const odeSolve = (f, t0, y0, t1) => solution(f, t0, y0)(t1);

  // Euler's method with n steps, for comparing with the exact solution.
  function euler(f, t0, y0, t1, n) {
    t0 = num(t0); y0 = num(y0); t1 = num(t1); n = num(n);
    need(Number.isInteger(n) && n > 0, 'euler(f, t0, y0, t1, n) takes a whole number of steps n.');
    const scalar = typeof y0 === 'number', F = rhs(f, scalar);
    let y = scalar ? [y0] : y0.slice(), t = t0;
    const h = (t1 - t0) / n;
    for (let k = 0; k < n; k++) { const d = F(t, y); y = y.map((v, i) => v + h * d[i]); t += h; }
    MathViz.markInexact();
    return scalar ? y[0] : y;
  }

  /* ---------- planar systems: equilibria and their stability ---------- */

  // A vector field of the plane: F(p) with p = (x, y), or F(x, y).
  const field = F => {
    need(typeof F === 'function', 'A vector field is a function of a point: F(p) or F(x, y), giving (dx/dt, dy/dt).');
    return arity(F) === 2 ? p => num(F(p[0], p[1])) : p => num(F(p));
  };
  const jac = (G, p) => {
    const h = 1e-6;
    return [0, 1].map(i => [0, 1].map(j => { const a = p.slice(), b = p.slice(); a[j] += h; b[j] -= h; return (G(a)[i] - G(b)[i]) / (2 * h); }));
  };
  function equilibria(F, r = 3) {
    r = num(r);
    const G = field(F), found = [];
    const n = 15;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      let p = [-r + 2 * r * (i + 0.5) / n, -r + 2 * r * (j + 0.5) / n];
      for (let it = 0; it < 40; it++) {
        const v = G(p);
        if (!isVec(v) || v.length !== 2) break;
        const J = jac(G, p), D = J[0][0] * J[1][1] - J[0][1] * J[1][0];
        if (!Number.isFinite(D) || Math.abs(D) < 1e-14) break;
        const dx = (J[1][1] * v[0] - J[0][1] * v[1]) / D, dy = (-J[1][0] * v[0] + J[0][0] * v[1]) / D;
        p = [p[0] - dx, p[1] - dy];
        if (Math.hypot(dx, dy) < 1e-13) break;
      }
      const v = G(p);
      if (isVec(v) && Math.hypot(...v) < 1e-9 && Math.abs(p[0]) <= r && Math.abs(p[1]) <= r && !found.some(q => Math.hypot(q[0] - p[0], q[1] - p[1]) < 1e-6)) {
        // A degenerate equilibrium (x² = 0) is approached slowly by Newton: snap what is left.
        found.push(p.map(x => Math.abs(x) < 1e-9 * Math.max(1, r) ? 0 : +x.toPrecision(12)));
      }
    }
    MathViz.markInexact();
    found.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    return MathViz.finite(found, { label: setLabel(found, `equilibria of ${fmt(F)} in [−${fmt(r)}, ${fmt(r)}]²`) });
  }
  // The type of an equilibrium from the linearization: trace T and determinant D of the Jacobian.
  function classify(F, p) {
    p = num(p);
    need(isVec(p) && p.length === 2, 'classify(F, p) takes a point p of the plane.');
    const J = jac(field(F), p), T = J[0][0] + J[1][1], D = J[0][0] * J[1][1] - J[0][1] * J[1][0], disc = T * T - 4 * D, tol = 1e-7;
    if (Math.abs(D) < tol) return 'degenerate (det 0)';
    if (D < 0) return 'saddle';
    if (disc >= -tol) return Math.abs(T) < tol ? 'degenerate (repeated 0)' : T < 0 ? 'stable node' : 'unstable node';
    return Math.abs(T) < tol ? 'center (linearization)' : T < 0 ? 'stable spiral' : 'unstable spiral';
  }
  // Is p attracting? Followed numerically: every nearby start (8 directions, distance 10⁻³) ends
  // within 10⁻⁴ of p by time 60. A center or a saddle doesn't pass.
  function stable(F, p) {
    p = num(p);
    need(isVec(p) && p.length === 2, 'stable(F, p) takes a point p of the plane.');
    const G = field(F), Fa = (t, Y) => G(Y);
    MathViz.markInexact();
    for (let k = 0; k < 8; k++) {
      const a = 2 * Math.PI * k / 8 + 0.1, start = [p[0] + 1e-3 * Math.cos(a), p[1] + 1e-3 * Math.sin(a)];
      const ks = integrate(Fa, 0, start, 60, null, 20000);
      const end = ks[ks.length - 1];
      if (end.t < 60 - 1e-9 || Math.hypot(end.y[0] - p[0], end.y[1] - p[1]) > 1e-4) return false;
    }
    return true;
  }

  /* ---------- maps: x ↦ g(x), iterated ---------- */

  const mapOf = g => { need(typeof g === 'function', 'A map is a function x ↦ g(x).'); return x => num(g(x)); };
  function iterate(g, x, n) {
    n = num(n); x = num(x);
    need(Number.isInteger(n) && n >= 0, 'iterate(g, x, n) applies g n times; n is a whole number.');
    const G = mapOf(g);
    for (let k = 0; k < n; k++) x = G(x);
    return x;
  }
  function orbit(g, x, n) {
    n = num(n); x = num(x);
    need(Number.isInteger(n) && n >= 0 && n <= 100000, 'orbit(g, x, n) lists x, g(x), …, gⁿ(x); n is a whole number up to 100000.');
    const G = mapOf(g), out = [x];
    for (let k = 0; k < n; k++) out.push(x = G(x));
    return out;
  }
  function fixedPoints(g, a, b) {
    a = num(a); b = num(b);
    const G = mapOf(g), h = x => G(x) - x, N = 2000, out = [];
    let pa = a, ha = h(a);
    if (Math.abs(ha) < 1e-12) out.push(a);
    for (let k = 1; k <= N; k++) {
      const pb = a + (b - a) * k / N, hb = h(pb);
      if (Math.abs(hb) < 1e-12) out.push(pb);
      else if (Number.isFinite(ha) && Number.isFinite(hb) && ha * hb < 0 && Math.abs(ha) > 1e-12) {
        let lo = pa, hi = pb, hl = ha;
        for (let it = 0; it < 100; it++) { const m = (lo + hi) / 2, hm = h(m); if ((hm < 0) === (hl < 0)) { lo = m; hl = hm; } else hi = m; }
        const r = (lo + hi) / 2;
        if (Math.abs(G(r) - r) < 1e-8) out.push(+r.toPrecision(13));
      }
      pa = pb; ha = hb;
    }
    MathViz.markInexact();
    const fps = [...new Set(out)];
    return MathViz.finite(fps, { label: setLabel(fps, `fixed points of ${fmt(g)} in [${fmt(a)}, ${fmt(b)}]`) });
  }
  // The period the orbit settles into after 2000 steps (1 for a fixed point), or 0 when it doesn't
  // repeat within 128 steps (chaos, or very slow convergence).
  function period(g, x) {
    const G = mapOf(g);
    x = num(x);
    for (let k = 0; k < 2000; k++) x = G(x);
    const seen = [x];
    for (let k = 1; k <= 128; k++) {
      x = G(x);
      if (Math.abs(x - seen[0]) < 1e-7 * Math.max(1, Math.abs(x))) {
        // Check it again a cycle later, so a slow approach isn't mistaken for a cycle.
        let y = x;
        for (let j = 0; j < k; j++) y = G(y);
        if (Math.abs(y - x) < 1e-7 * Math.max(1, Math.abs(x))) return k;
      }
      seen.push(x);
    }
    MathViz.markInexact();
    return 0;
  }
  // The Lyapunov exponent of the orbit of x: the average of ln|g′| along it. Negative: nearby
  // orbits come together; positive: they separate (chaos).
  function lyapunov(g, x, n = 4000) {
    const G = mapOf(g);
    x = num(x); n = num(n);
    for (let k = 0; k < 500; k++) x = G(x);
    let s = 0;
    for (let k = 0; k < n; k++) {
      const h = 1e-7 * Math.max(1, Math.abs(x)), d = (G(x + h) - G(x - h)) / (2 * h);
      s += Math.log(Math.max(Math.abs(d), 1e-300));
      x = G(x);
    }
    MathViz.markInexact();
    return s / n;
  }
  const logistic = r => { r = num(r); return named(x => r * x * (1 - x), `x ↦ ${fmt(r)}·x(1 − x)`, { arity: 1, logisticR: r }); };

  /* ---------- example catalogs ---------- */

  let sysCat = {}, mapCat = {};
  const Systems = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (sysCat[key]) return sysCat[key];
    const sys = (F, label) => named(p => F(p[0], p[1]), label, { arity: 1 });
    const list = [
      sys((x, y) => [y, -x], 'harmonic oscillator (y, −x)'),
      sys((x, y) => [y, -x - 0.5 * y], 'damped oscillator (y, −x − y/2)'),
      sys((x, y) => [x, -y], 'saddle (x, −y)'),
      sys((x, y) => [x, -2 * y], 'saddle (x, −2y)'),
      sys((x, y) => [-x, -2 * y], 'stable node (−x, −2y)'),
      sys((x, y) => [2 * x, y], 'unstable node (2x, y)'),
      sys((x, y) => [-x + y, -x - y], 'stable spiral (−x + y, −x − y)'),
      sys((x, y) => [x * (1 - y), y * (x - 1)], 'Lotka–Volterra (x(1 − y), y(x − 1))'),
      sys((x, y) => [y, (1 - x * x) * y - x], 'van der Pol (y, (1 − x²)y − x)'),
      sys((x, y) => [y, -Math.sin(x)], 'pendulum (y, −sin x)'),
    ];
    if (key) list.push(
      sys((x, y) => [y, -x * x * x], 'nonlinear center (y, −x³)'),
      sys((x, y) => [x * x, -y], 'saddle-node (x², −y)'),
      sys((x, y) => [y - x * (x * x + y * y), -x - y * (x * x + y * y)], 'slow spiral, a center to first order (y − x r², −x − y r²)'),
    );
    return (sysCat[key] = MathViz.finite(list, { label: 'example planar systems' }));
  };
  const Maps = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (mapCat[key]) return mapCat[key];
    const list = [logistic(2.5), logistic(3.2), logistic(3.5), logistic(3.83), logistic(4),
      named(x => num(x) < 0.5 ? 2 * x : 2 - 2 * x, 'tent map'),
      named(x => num(x) / 2 + 0.25, 'x ↦ x/2 + 1/4'),
      named(x => Math.cos(num(x)), 'cos')];
    if (key) list.push(named(x => (4 * num(x)) % 1, 'x ↦ 4x mod 1'), named(x => num(x) * num(x), 'x ↦ x²'));
    return (mapCat[key] = MathViz.finite(list, { label: 'example maps of [0, 1]' }));
  };

  /* ---------- views ---------- */

  // Streamlines of a planar field: from each seed forward and back, a fixed length of curve.
  function streamline(G, p, len, dir) {
    const F = (t, Y) => { const v = G(Y), m = Math.hypot(v[0], v[1]); return m > 1e-12 ? [dir * v[0] / m, dir * v[1] / m] : [0, 0]; };
    return integrate(F, 0, p, len, null, 600).map(k => k.y);
  }
  const typeColor = s => /saddle/.test(s) ? 'c4' : /unstable/.test(s) ? 'neg' : /stable/.test(s) ? 'pos' : 'c3';

  const views = {
    phase_portrait: {
      doc: 'phase_portrait(F, r) draws the flow of the planar system p′ = F(p) on [−r, r]²: streamlines, direction arrows, and the equilibria colored by type (stable, unstable, saddle, center). Click anywhere to follow the solution through that point.',
      render(ctx, F, r = 3) {
        r = num(r);
        const G = field(F);
        const picks = ctx.memo('picks', () => []);
        const fig = ctx.figure({ x: [-r, r], y: [-r, r], square: true, pick: (x, y) => { picks.push([x, y]); ctx.redraw(); } });
        const n = 11, L = r * 0.55;
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
          const p = [-r + 2 * r * (i + 0.5) / n, -r + 2 * r * (j + 0.5) / n];
          for (const dir of [1, -1]) {
            const line = streamline(G, p, L, dir).filter(q => Math.abs(q[0]) <= r * 1.05 && Math.abs(q[1]) <= r * 1.05);
            if (line.length > 1) fig.curve(line, { color: 'c1', width: 1, alpha: 0.45 });
          }
          const v = G(p), m = Math.hypot(v[0], v[1]);
          if (m > 1e-12) { const s = r / n * 0.6; fig.arrow(p[0], p[1], p[0] + v[0] / m * s, p[1] + v[1] / m * s, { color: 'c1', width: 1.2, alpha: 0.8 }); }
        }
        for (const p of picks) {
          const F2 = (t, Y) => G(Y);
          for (const T of [25, -25]) {
            const ks = integrate(F2, 0, p, T, null, 8000);
            fig.curve(ks.map(k => k.y).filter(q => Math.abs(q[0]) <= 3 * r && Math.abs(q[1]) <= 3 * r), { color: 'c2', width: 2.2, alpha: T > 0 ? 1 : 0.45 });
          }
          fig.points([p], { color: 'c2', r: 4 });
        }
        const eq = equilibria(F, r).values;
        const kinds = eq.map(p => classify(F, p));
        eq.forEach((p, i) => fig.points([p], { color: typeColor(kinds[i]), r: 6 }));
        ctx.legend([{ label: 'flow', color: 'c1' }, ...(picks.length ? [{ label: 'your solutions (faint: backward in time)', color: 'c2' }] : []),
          { label: 'stable', color: 'pos' }, { label: 'unstable', color: 'neg' }, { label: 'saddle', color: 'c4' }, { label: 'center / other', color: 'c3' }]);
        ctx.note(eq.length ? `Equilibria: ${eq.map((p, i) => `${pt(p)} ${kinds[i]}`).join('; ')}. Click to follow a solution.` : 'No equilibria in this window. Click to follow a solution.');
      },
    },
    slope_field: {
      doc: "slope_field(f, t0, t1, y0, y1) draws the direction field of y′ = f(t, y) on [t0, t1] × [y0, y1] with a few solutions. Click to add the solution through a point.",
      render(ctx, f, t0 = -3, t1 = 3, y0 = -3, y1 = 3) {
        [t0, t1, y0, y1] = [t0, t1, y0, y1].map(num);
        const F = rhs(f, true);
        const picks = ctx.memo('picks', () => []);
        const fig = ctx.figure({ x: [t0, t1], y: [y0, y1], xlabel: 't', ylabel: 'y', pick: (t, y) => { picks.push([t, y]); ctx.redraw(); } });
        const nx = 21, ny = 15, sx = (t1 - t0) / nx, sy = (y1 - y0) / ny;
        for (let i = 0; i < nx; i++) for (let j = 0; j < ny; j++) {
          const t = t0 + sx * (i + 0.5), y = y0 + sy * (j + 0.5);
          let s;
          try { s = F(t, [y])[0]; } catch (e) { continue; }
          if (!Number.isFinite(s)) continue;
          // A short segment of slope s, the same length on screen whatever the scales.
          const ux = sx * 0.38, uy = s * ux, k = Math.min(1, (sy * 0.38) / Math.max(1e-12, Math.abs(uy)));
          fig.seg(t - ux * k, y - uy * k, t + ux * k, y + uy * k, { color: 'c1', width: 1.2, alpha: 0.7 });
        }
        const starts = [...[-0.6, -0.2, 0.2, 0.6].map(c => [t0 + 0.02 * (t1 - t0), (y0 + y1) / 2 + c * (y1 - y0)]), ...picks];
        starts.forEach((p, i) => {
          const sol = solution(f, p[0], p[1]);
          const ts = Array.from({ length: 301 }, (_, k) => t0 + (t1 - t0) * k / 300);
          const pts = ts.map(t => [t, sol(t)]).filter(q => Number.isFinite(q[1]) && q[1] > y0 - (y1 - y0) && q[1] < y1 + (y1 - y0));
          fig.curve(pts, { color: i < 4 ? 'c3' : 'c2', width: i < 4 ? 1.5 : 2.2 });
          if (i >= 4) fig.points([p], { color: 'c2', r: 4 });
        });
        ctx.legend([{ label: 'slopes', color: 'c1' }, { label: 'solutions', color: 'c3' }, ...(picks.length ? [{ label: 'through your points', color: 'c2' }] : [])]);
      },
    },
    cobweb: {
      doc: 'cobweb(g, x0, n, a, b) draws the graph of the map g on [a, b] with the diagonal, and the cobweb of the orbit of x0: up to the graph, across to the diagonal, n times. Drag x0 and n.',
      render(ctx, g, x0 = 0.2, n = 30, a = 0, b = 1) {
        [x0, n, a, b] = [x0, n, a, b].map(num);
        const G = mapOf(g);
        x0 = ctx.param('x₀', { min: a, max: b, step: (b - a) / 500, value: x0 });
        n = ctx.param('steps', { min: 1, max: 200, step: 1, value: n });
        const fig = ctx.figure({ x: [a, b], y: [a, b], square: true });
        fig.curve(Array.from({ length: 401 }, (_, k) => { const x = a + (b - a) * k / 400; return [x, G(x)]; }), { color: 'c1', width: 2 });
        fig.seg(a, a, b, b, { color: 'ink', width: 1, alpha: 0.4 });
        let x = x0;
        const path = [[x, a]];
        for (let k = 0; k < n; k++) {
          const y = G(x);
          if (!Number.isFinite(y)) break;
          path.push([x, y], [y, y]);
          x = y;
        }
        fig.curve(path, { color: 'c2', width: 1.3, alpha: 0.85 });
        fig.points([[x0, a]], { color: 'c2', r: 4 });
        const p = period(g, x0), fps = fixedPoints(g, a, b).values;
        fig.points(fps.map(f => [f, f]), { color: 'neg', r: 4 });
        ctx.legend([{ label: 'g', color: 'c1' }, { label: 'y = x', color: 'ink' }, { label: 'orbit', color: 'c2' }, { label: 'fixed points', color: 'neg' }]);
        ctx.note(`After ${n} steps x = ${r4(x)}. ${p === 1 ? 'The orbit settles on a fixed point.' : p > 1 ? `The orbit settles into a cycle of period ${p}.` : 'The orbit doesn\'t settle into a short cycle: chaotic, or converging slowly.'} Lyapunov exponent ${r4(lyapunov(g, x0))}.`);
      },
    },
    bifurcation: {
      doc: 'bifurcation(family, r0, r1) draws where the orbits of the maps family(r) settle, for r from r0 to r1: one branch for a fixed point, two after the first period doubling, a cloud where the dynamics is chaotic. family is r ↦ map, as logistic, or a function g(r, x).',
      render(ctx, fam, r0 = 2.5, r1 = 4, a = 0, b = 1) {
        [r0, r1, a, b] = [r0, r1, a, b].map(num);
        need(typeof fam === 'function', 'bifurcation(family, r0, r1): family is r ↦ map, such as logistic.');
        const mapAt = arity(fam) === 2 ? r => x => num(fam(r, x)) : r => mapOf(fam(r));
        const fig = ctx.figure({ x: [r0, r1], y: [a, b], xlabel: 'r', ylabel: 'x' });
        const pts = [];
        const N = 500;
        for (let i = 0; i <= N; i++) {
          const r = r0 + (r1 - r0) * i / N, G = mapAt(r);
          let x = a + (b - a) * 0.3141;
          for (let k = 0; k < 600; k++) x = G(x);
          for (let k = 0; k < 120; k++) { x = G(x); if (Number.isFinite(x) && x >= a - 0.1 * (b - a) && x <= b + 0.1 * (b - a)) pts.push([r, x]); }
        }
        fig.points(pts, { color: 'c1', r: 0.7, alpha: 0.5 });
        ctx.note('For each r: 600 steps to settle, then the next 120 points of the orbit. Zoom in on a window inside the chaos: the picture repeats in miniature.');
      },
    },
    time_series: {
      doc: "time_series(f, t0, y0, t1) plots each component of the solution of y′ = f(t, y) with y(t0) = y0 against t, up to t1.",
      render(ctx, f, t0, y0, t1) {
        const sol = solution(f, t0, y0);
        [t0, t1] = [t0, t1].map(num);
        const ts = Array.from({ length: 601 }, (_, k) => t0 + (t1 - t0) * k / 600);
        const ys = ts.map(t => sol(t));
        const dim = typeof ys[0] === 'number' ? 1 : ys[0].length;
        const fig = ctx.figure({ x: [t0, t1], xlabel: 't' });
        const colors = ['c1', 'c2', 'c3', 'c4', 'c5', 'c6'];
        for (let i = 0; i < dim; i++) fig.curve(ts.map((t, k) => [t, dim === 1 ? ys[k] : ys[k] && ys[k][i]]).filter(q => Number.isFinite(q[1])), { color: colors[i % 6], width: 2 });
        ctx.legend(Array.from({ length: dim }, (_, i) => ({ label: dim === 1 ? 'y(t)' : `y${'₁₂₃₄₅₆'[i]}(t)`, color: colors[i % 6] })));
        const bad = ys.findIndex(y => !(typeof y === 'number' ? Number.isFinite(y) : y.every(Number.isFinite)));
        if (bad >= 0) ctx.note(`The solution stops at t ≈ ${r4(ts[bad])}: it blows up (or the equation is undefined) there.`);
      },
    },
  };

  MathViz.define({
    name: 'dynamics',
    requires: ['multivar'],
    description: 'Differential equations and dynamical systems: solutions of y′ = f(t, y) (adaptive Runge–Kutta), Euler\'s method, equilibria of planar systems and their type and stability, iterated maps with orbits, fixed points, periods and Lyapunov exponents, the logistic family; views of phase portraits, slope fields, cobwebs, bifurcation diagrams and time series.',
    functions: {
      solution: { doc: "solution(f, t0, y0): the solution of y′ = f(t, y) (or y′ = f(y)) with y(t0) = y0, as a function of t. y0 is a number or a point; the solution is computed by an adaptive Runge–Kutta method, accurate to about 10⁻⁹.", fn: solution },
      ode_solve: { doc: "ode_solve(f, t0, y0, t1): the value at t1 of the solution of y′ = f(t, y) with y(t0) = y0.", fn: odeSolve },
      euler: { doc: "euler(f, t0, y0, t1, n): Euler's method with n equal steps from t0 to t1. Its error shrinks like 1/n.", fn: euler },
      equilibria: { doc: 'equilibria(F, r): the points of [−r, r]² where the planar field F vanishes, found by Newton\'s method from a grid of starts.', fn: equilibria },
      classify: { doc: 'classify(F, p): the type of the equilibrium p from the linearization: saddle, stable or unstable node, stable or unstable spiral, center, or degenerate.', fn: classify },
      stable: { doc: 'stable(F, p): whether p attracts the solutions that start near it (followed numerically from 8 nearby starts up to time 60).', fn: stable },
      iterate: { doc: 'iterate(g, x, n) = gⁿ(x): g applied n times to x.', fn: iterate },
      orbit: { doc: 'orbit(g, x, n): the list x, g(x), …, gⁿ(x).', fn: orbit },
      fixed_points: { doc: 'fixed_points(g, a, b): the points of [a, b] with g(x) = x.', fn: fixedPoints },
      period: { doc: 'period(g, x): the period of the cycle the orbit of x settles into (1 for a fixed point), or 0 if it doesn\'t settle into one of period up to 128.', fn: period },
      lyapunov: { doc: 'lyapunov(g, x): the Lyapunov exponent of the orbit of x, the average of ln|g′| along it: negative when nearby orbits converge, positive in chaos.', fn: lyapunov },
      logistic: { doc: 'logistic(r): the logistic map x ↦ r·x(1 − x).', fn: logistic },
    },
    spaces: {
      Systems: { doc: 'Systems: example planar vector fields: harmonic and damped oscillators, saddles, nodes, a spiral, Lotka–Volterra, van der Pol, the pendulum.', fn: Systems },
      Maps: { doc: 'Maps: example maps of [0, 1]: logistic maps from orderly to chaotic, the tent map, a contraction, cos.', fn: Maps },
    },
    views,
    notation: `
# The fixed point of cos attracts every orbit: the Dottie number 0.739085…
lemma dottie: forall x in [-10, 10]: |iterate(cos, x, 300) - 0.7390851332151607| < 1e-9

# For 1 < r < 3 the logistic map's orbits converge to its fixed point 1 − 1/r.
lemma logistic_settles: forall r in [1.2, 2.9], x in [0.05, 0.95]: |iterate(logistic(r), x, 5000) - (1 - 1/r)| < 1e-6

# Past r = 3 they don't: the fixed point loses stability and a cycle of period 2 takes over.
conjecture logistic_always_settles: forall r in [1.2, 4], x in [0.05, 0.95]: |iterate(logistic(r), x, 5000) - (1 - 1/r)| < 1e-6

# The solution of the harmonic oscillator x′ = y, y′ = −x through (1, 0).
def harmonic_orbit := solution(p => (p[2], -p[1]), 0, (1, 0))

# It keeps its energy: the solution stays on the unit circle.
lemma harmonic_circles: forall t in [0, 30]: ||harmonic_orbit(t)| - 1| < 1e-6

# Euler's method converges, with error about e/(2n) for y′ = y on [0, 1].
lemma euler_first_order: forall n in 10..2000: |euler((t, y) => y, 0, 1, 1, n) - e| < 2/n

# A negative trace isn't enough for stability: a saddle can have one.
conjecture negative_trace_stable: forall F in Systems: forall p in equilibria(F, 3): trace(jacobian(F, p)) < 0 -> stable(F, p)

# Negative trace and positive determinant (by a margin, past rounding): both eigenvalues have
# negative real part, and the equilibrium attracts.
lemma trace_det_stable: forall F in Systems: forall p in equilibria(F, 3): trace(jacobian(F, p)) < -1e-6 and det(jacobian(F, p)) > 1e-6 -> stable(F, p)
`,
  });
});
