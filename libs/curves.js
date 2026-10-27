MathVizLibrary(function curves(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const named = (f, label, meta = {}) => Object.assign(f, { label }, meta);
  const num = v => typeof v === 'number' ? v : Array.isArray(v) ? v.map(num) : v != null && typeof v.valueOf() === 'number' ? +v : v;
  const r4 = x => fmt(+(+x).toPrecision(4));
  const TAU = 2 * Math.PI;

  /* ---------- vectors in ℝ³ (plane curves get z = 0) ---------- */
  const v3 = p => p.length === 3 ? p : [p[0], p[1], 0];
  const sub = (a, b) => a.map((x, i) => x - b[i]);
  const add = (a, b) => a.map((x, i) => x + b[i]);
  const scale = (a, k) => a.map(x => x * k);
  const dot = (a, b) => a.reduce((s, x, i) => s + x * b[i], 0);
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const norm = a => Math.hypot(...a);
  const unit = a => { const n = norm(a); return n > 0 ? scale(a, 1 / n) : a.map(() => NaN); };

  /* ---------- curves t ↦ c(t) in ℝ² or ℝ³: derivatives by high-order differences ---------- */
  const curveFn = c => {
    need(typeof c === 'function', 'A curve is a function t ↦ c(t), a point of the plane or of space.');
    return t => {
      const p = num(c(t));
      need(Array.isArray(p) && (p.length === 2 || p.length === 3) && p.every(x => typeof x === 'number'), `A curve gives points of ℝ² or ℝ³, but c(${r4(t)}) is ${fmt(p)}.`);
      return p;
    };
  };
  const at = (C, t, k) => v3(C(t + k));
  function derivs(c, t) {
    t = num(t);
    need(typeof t === 'number', 'The parameter t is a number.');
    const C = curveFn(c), s = Math.max(1, Math.abs(t));
    MathViz.markInexact();
    const f = k => at(C, t, k);
    const h1 = 1e-3 * s, h3 = 5e-3 * s;
    const p = f(0), pa = f(h1), pb = f(-h1), pc = f(2 * h1), pd = f(-2 * h1);
    const d1 = p.map((_, i) => (-pc[i] + 8 * pa[i] - 8 * pb[i] + pd[i]) / (12 * h1));
    const d2 = p.map((_, i) => (-pc[i] + 16 * pa[i] - 30 * p[i] + 16 * pb[i] - pd[i]) / (12 * h1 * h1));
    const q = [3, 2, 1, -1, -2, -3].map(k => f(k * h3));
    const d3 = p.map((_, i) => (-q[0][i] + 8 * q[1][i] - 13 * q[2][i] + 13 * q[3][i] - 8 * q[4][i] + q[5][i]) / (8 * h3 ** 3));
    return { p, d1, d2, d3, planar: C(t).length === 2 };
  }
  const speed = (c, t) => norm(derivs(c, t).d1);
  const curvature = (c, t) => { const { d1, d2 } = derivs(c, t); return norm(cross(d1, d2)) / norm(d1) ** 3; };
  const signedCurvature = (c, t) => {
    const { d1, d2, planar } = derivs(c, t);
    need(planar, 'signed_curvature is for plane curves; in space use curvature (which is ≥ 0) and torsion.');
    return (d1[0] * d2[1] - d1[1] * d2[0]) / norm(d1) ** 3;
  };
  const torsion = (c, t) => {
    const { d1, d2, d3, planar } = derivs(c, t);
    if (planar) return 0;
    const x = cross(d1, d2), m = dot(x, x);
    // Where the curvature vanishes the torsion isn't defined.
    return m < 1e-14 * norm(d1) ** 6 ? NaN : dot(x, d3) / m;
  };
  const back = (p, planar) => planar ? p.slice(0, 2) : p;
  const tangent = (c, t) => { const { d1, planar } = derivs(c, t); return back(unit(d1), planar); };
  const normalVec = (c, t) => {
    const { d1, d2, planar } = derivs(c, t), T = unit(d1);
    return back(unit(sub(d2, scale(T, dot(d2, T)))), planar);
  };
  const binormal = (c, t) => {
    const { d1, d2 } = derivs(c, t);
    return unit(cross(d1, d2));
  };
  // Adaptive Simpson on a function of one variable.
  function integrate1(f, a, b, tol = 1e-10) {
    const simpson = (a, b, fa, fm, fb) => (b - a) / 6 * (fa + 4 * fm + fb);
    const rec = (a, b, fa, fm, fb, whole, tol, depth) => {
      const m = (a + b) / 2, lm = (a + m) / 2, rm = (m + b) / 2, flm = f(lm), frm = f(rm);
      const left = simpson(a, m, fa, flm, fm), right = simpson(m, b, fm, frm, fb);
      if (depth > 18 || Math.abs(left + right - whole) <= 15 * tol) return left + right + (left + right - whole) / 15;
      return rec(a, m, fa, flm, fm, left, tol / 2, depth + 1) + rec(m, b, fm, frm, fb, right, tol / 2, depth + 1);
    };
    // A few panels first, so a periodic integrand isn't mistaken for a constant.
    const n = 16;
    let s = 0;
    for (let k = 0; k < n; k++) {
      const x0 = a + (b - a) * k / n, x1 = a + (b - a) * (k + 1) / n, fa = f(x0), fm = f((x0 + x1) / 2), fb = f(x1);
      s += rec(x0, x1, fa, fm, fb, simpson(x0, x1, fa, fm, fb), tol / n, 0);
    }
    return s;
  }
  const arcLength = (c, a, b) => { [a, b] = [a, b].map(num); MathViz.markInexact(); return integrate1(t => speed(c, t), a, b); };
  // ∫ κ ds: how much the tangent turns in total (2π for a convex closed plane curve).
  const totalTurning = (c, a, b) => { [a, b] = [a, b].map(num); MathViz.markInexact(); return integrate1(t => curvature(c, t) * speed(c, t), a, b, 1e-8); };

  /* ---------- surfaces (u, v) ↦ s(u, v) in ℝ³ ---------- */
  const surfFn = s => {
    need(typeof s === 'function', 'A surface is a function (u, v) ↦ a point of ℝ³.');
    return (u, v) => {
      const p = num(s(u, v));
      need(Array.isArray(p) && p.length === 3 && p.every(x => typeof x === 'number'), `A surface gives points of ℝ³, but s(${r4(u)}, ${r4(v)}) is ${fmt(p)}.`);
      return p;
    };
  };
  function forms(s, u, v) {
    [u, v] = [u, v].map(num);
    const S = surfFn(s), hu = 1e-3 * Math.max(1, Math.abs(u)), hv = 1e-3 * Math.max(1, Math.abs(v));
    MathViz.markInexact();
    // The 17 points of the stencils, each evaluated once.
    const memo = new Map();
    const P = (a, b) => { const k = a + ',' + b; if (!memo.has(k)) memo.set(k, S(u + a * hu, v + b * hv)); return memo.get(k); };
    const p = P(0, 0);
    const d1 = (A, B, h) => { const a1 = A(1), a2 = A(2), b1 = B(1), b2 = B(2); return p.map((_, i) => (-a2[i] + 8 * a1[i] - 8 * b1[i] + b2[i]) / (12 * h)); };
    const d2 = (A, B, h) => { const a1 = A(1), a2 = A(2), b1 = B(1), b2 = B(2); return p.map((_, i) => (-a2[i] + 16 * a1[i] - 30 * p[i] + 16 * b1[i] - b2[i]) / (12 * h * h)); };
    const U = k => P(k, 0), Um = k => P(-k, 0), V = k => P(0, k), Vm = k => P(0, -k);
    const su = d1(U, Um, hu), sv = d1(V, Vm, hv), suu = d2(U, Um, hu), svv = d2(V, Vm, hv);
    // The mixed derivative by Richardson extrapolation of the four-point formula.
    const mix = k => { const a = P(k, k), b = P(k, -k), c = P(-k, k), d = P(-k, -k); return p.map((_, i) => (a[i] - b[i] - c[i] + d[i]) / (4 * k * k * hu * hv)); };
    const m1 = mix(1), m2 = mix(2), suv = m1.map((x, i) => (4 * x - m2[i]) / 3);
    const n = unit(cross(su, sv));
    const E = dot(su, su), F = dot(su, sv), G = dot(sv, sv), L = dot(suu, n), M = dot(suv, n), N = dot(svv, n);
    return { p, su, sv, n, E, F, G, L, M, N, W: E * G - F * F };
  }
  const gaussCurvature = (s, u, v) => { const f = forms(s, u, v); return (f.L * f.N - f.M * f.M) / f.W; };
  const meanCurvature = (s, u, v) => { const f = forms(s, u, v); return (f.E * f.N - 2 * f.F * f.M + f.G * f.L) / (2 * f.W); };
  const surfaceNormal = (s, u, v) => forms(s, u, v).n;
  const firstForm = (s, u, v) => { const f = forms(s, u, v); return [[f.E, f.F], [f.F, f.G]]; };
  const secondForm = (s, u, v) => { const f = forms(s, u, v); return [[f.L, f.M], [f.M, f.N]]; };
  // ∫∫ g(u, v) dA by 4-point Gauss–Legendre on an n × n grid of cells.
  const GL = [[-0.8611363115940526, 0.3478548451374538], [-0.3399810435848563, 0.6521451548625461], [0.3399810435848563, 0.6521451548625461], [0.8611363115940526, 0.3478548451374538]];
  function integrate2(g, u0, u1, v0, v1, n = 20) {
    let s = 0;
    const du = (u1 - u0) / n, dv = (v1 - v0) / n;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      const uc = u0 + du * (i + 0.5), vc = v0 + dv * (j + 0.5);
      for (const [a, wa] of GL) for (const [b, wb] of GL) s += wa * wb * g(uc + a * du / 2, vc + b * dv / 2);
    }
    return s * du * dv / 4;
  }
  const domainOf = (s, args) => {
    const [u0, u1, v0, v1] = args.map(num);
    if ([u0, u1, v0, v1].every(x => typeof x === 'number')) return [u0, u1, v0, v1];
    need(s.domain, 'Give the parameter ranges: (s, u0, u1, v0, v1).');
    return [...s.domain.u, ...s.domain.v];
  };
  const surfaceArea = (s, ...r) => { const [u0, u1, v0, v1] = domainOf(s, r); MathViz.markInexact(); return integrate2((u, v) => Math.sqrt(Math.max(0, forms(s, u, v).W)), u0, u1, v0, v1); };
  // ∫∫ K dA: 4π for a sphere, 0 for a torus (Gauss–Bonnet: 2π times the Euler characteristic).
  const totalCurvature = (s, ...r) => {
    const [u0, u1, v0, v1] = domainOf(s, r);
    MathViz.markInexact();
    return integrate2((u, v) => { const f = forms(s, u, v); return (f.L * f.N - f.M * f.M) / Math.sqrt(f.W); }, u0, u1, v0, v1, 12);
  };

  /* ---------- example catalogs ---------- */
  const { cos, sin, exp, cosh } = Math;
  const curve = (f, label, range, meta = {}) => named(t => f(num(t)), label, { arity: 1, range, ...meta });
  let curveCat = {}, closedCat = null, surfCat = {};
  const closedList = () => closedCat || (closedCat = [
    curve(t => [2 * cos(t), 2 * sin(t)], 'circle of radius 2', [0, TAU], { closed: true }),
    curve(t => [3 * cos(t), sin(t)], 'ellipse (3 cos t, sin t)', [0, TAU], { closed: true }),
    curve(t => [cos(t), sin(t) * cos(t)], 'figure eight (cos t, sin t cos t)', [0, TAU], { closed: true }),
    curve(t => [sin(t) + 2 * sin(2 * t), cos(t) - 2 * cos(2 * t), -sin(3 * t)], 'trefoil knot', [0, TAU], { closed: true, knotted: true }),
    curve(t => [cos(t), sin(t), 0.3 * sin(2 * t)], 'saddle loop (cos t, sin t, 0.3 sin 2t)', [0, TAU], { closed: true }),
  ]);
  const Curves = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (curveCat[key]) return curveCat[key];
    const list = [...closedList(),
      curve(t => [t, t * t], 'parabola (t, t²)', [-2, 2]),
      curve(t => [cos(t), sin(t), t / 2], 'helix (cos t, sin t, t/2)', [0, 4 * Math.PI]),
      curve(t => [t, t * t, t * t * t], 'twisted cubic (t, t², t³)', [-1.5, 1.5]),
      curve(t => [t - sin(t), 1 - cos(t)], 'cycloid (t − sin t, 1 − cos t)', [0.2, TAU - 0.2]),
      curve(t => [exp(t / 5) * cos(t), exp(t / 5) * sin(t)], 'logarithmic spiral', [0, 4 * Math.PI]),
      curve(t => [1 + t, 2 - t], 'line (1 + t, 2 − t)', [-2, 2]),
    ];
    if (key) list.push(
      curve(t => [cos(t) ** 3, sin(t) ** 3], 'astroid (cos³ t, sin³ t), with cusps', [0, TAU]),
      curve(t => [2 * cos(t * t * t), 2 * sin(t * t * t)], 'circle of radius 2 at speed 6t²', [0.3, 1.8]),
      curve(t => [cos(t), sin(t), (t * t) / 4], 'helix whose pitch grows (cos t, sin t, t²/4)', [0, 4 * Math.PI]),
    );
    return (curveCat[key] = MathViz.finite(list, { label: 'example curves' }));
  };
  const ClosedCurves = () => MathViz.finite(closedList(), { label: 'example closed curves, t ∈ [0, 2π]' });
  const surface = (f, label, u, v) => named((a, b) => f(num(a), num(b)), label, { arity: 2, domain: { u, v } });
  const Surfaces = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (surfCat[key]) return surfCat[key];
    const list = [
      surface((u, v) => [cos(u) * cos(v), sin(u) * cos(v), sin(v)], 'unit sphere', [0, TAU], [-Math.PI / 2, Math.PI / 2]),
      surface((u, v) => [2 * cos(u) * cos(v), 2 * sin(u) * cos(v), 2 * sin(v)], 'sphere of radius 2', [0, TAU], [-Math.PI / 2, Math.PI / 2]),
      surface((u, v) => [cos(u), sin(u), v], 'cylinder', [0, TAU], [-1, 1]),
      surface((u, v) => [v * cos(u), v * sin(u), v], 'cone (without its apex)', [0, TAU], [0.2, 1.5]),
      surface((u, v) => [(2 + cos(v)) * cos(u), (2 + cos(v)) * sin(u), sin(v)], 'torus', [0, TAU], [0, TAU]),
      surface((u, v) => [u, v, u * v], 'saddle z = xy', [-1.2, 1.2], [-1.2, 1.2]),
      surface((u, v) => [u, v, u * u + v * v], 'paraboloid z = x² + y²', [-1.2, 1.2], [-1.2, 1.2]),
      surface((u, v) => [u, v, u + 2 * v], 'plane z = x + 2y', [-1, 1], [-1, 1]),
      surface((u, v) => [cosh(v) * cos(u), cosh(v) * sin(u), v], 'catenoid', [0, TAU], [-1.2, 1.2]),
      surface((u, v) => [v * cos(u), v * sin(u), u], 'helicoid', [0, TAU], [-1.5, 1.5]),
    ];
    if (key) list.push(
      surface((u, v) => [u - u ** 3 / 3 + u * v * v, v - v ** 3 / 3 + v * u * u, u * u - v * v], "Enneper's surface", [-1.5, 1.5], [-1.5, 1.5]),
      surface((u, v) => [(1 + v / 2 * cos(u / 2)) * cos(u), (1 + v / 2 * cos(u / 2)) * sin(u), v / 2 * sin(u / 2)], 'Möbius strip', [0, TAU], [-1, 1]),
      surface((u, v) => [cos(u) / cosh(v), sin(u) / cosh(v), v - Math.tanh(v)], 'pseudosphere (K = −1)', [0, TAU], [0.2, 2.5]),
    );
    return (surfCat[key] = MathViz.finite(list, { label: 'example surfaces' }));
  };

  /* ---------- views ---------- */
  const rangeOf = (c, a, b) => {
    [a, b] = [a, b].map(num);
    if (typeof a === 'number' && typeof b === 'number') return [a, b];
    return c.range || [0, TAU];
  };
  const views = {
    frenet: {
      doc: 'frenet(c, a, b) draws the curve c on [a, b] with its moving frame at a point you slide along it: the unit tangent T, the principal normal N, the binormal B (in space), and the osculating circle, of radius 1/κ.',
      render(ctx, c, a, b) {
        [a, b] = rangeOf(c, a, b);
        const t = ctx.param('t', { min: a, max: b, step: (b - a) / 400, value: a + (b - a) * 0.3 });
        const C = curveFn(c), planar = C(a).length === 2;
        const ts = Array.from({ length: 401 }, (_, k) => a + (b - a) * k / 400);
        const pts = ts.map(s => C(s));
        const k = curvature(c, t), T = v3(tangent(c, t)), N = v3(normalVec(c, t)), p = v3(C(t));
        const ext = Math.max(...pts.flat().map(Math.abs), 1), L = ext * 0.25;
        const circ = Number.isFinite(k) && k > 1e-9 && 1 / k < 20 * ext
          ? Array.from({ length: 121 }, (_, i) => { const th = TAU * i / 120, ctr = add(p, scale(N, 1 / k)); return add(ctr, add(scale(T, cos(th) / k), scale(N, -sin(th) / k))); }) : null;
        if (planar) {
          // The window fits the curve (a large osculating circle runs off it).
          const xs = pts.map(q => q[0]), ys = pts.map(q => q[1]);
          const pad = 0.25 * Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys), 1e-6);
          const fig = ctx.figure({ square: true, x: [Math.min(...xs) - pad, Math.max(...xs) + pad], y: [Math.min(...ys) - pad, Math.max(...ys) + pad] });
          fig.curve(pts, { color: 'c1', width: 2 });
          if (circ) fig.curve(circ.map(q => [q[0], q[1]]), { color: 'c4', width: 1.2, dash: [5, 4] });
          fig.arrow(p[0], p[1], p[0] + L * T[0], p[1] + L * T[1], { color: 'c2', width: 2 });
          fig.arrow(p[0], p[1], p[0] + L * N[0], p[1] + L * N[1], { color: 'c3', width: 2 });
          fig.points([[p[0], p[1]]], { color: 'ink', r: 4 });
          ctx.legend([{ label: 'c', color: 'c1' }, { label: 'T', color: 'c2' }, { label: 'N', color: 'c3' }, { label: 'osculating circle', color: 'c4' }]);
          ctx.note(`At t = ${r4(t)}: speed ${r4(speed(c, t))}, signed curvature ${r4(signedCurvature(c, t))}${k > 1e-9 ? `, radius of curvature ${r4(1 / k)}` : ' (straight here)'}.`);
        } else {
          const B = binormal(c, t);
          const fig = ctx.figure3d({ labels: ['x', 'y', 'z'] });
          fig.curve(pts, { color: 'c1', width: 2 });
          if (circ) fig.curve(circ, { color: 'c4', width: 1.2, track: false });
          fig.arrow(p, add(p, scale(T, L)), { color: 'c2', width: 2.2, track: false });
          fig.arrow(p, add(p, scale(N, L)), { color: 'c3', width: 2.2, track: false });
          fig.arrow(p, add(p, scale(B, L)), { color: 'c6', width: 2.2, track: false });
          fig.points([p], { color: 'ink', r: 4, track: false });
          ctx.legend([{ label: 'c', color: 'c1' }, { label: 'T', color: 'c2' }, { label: 'N', color: 'c3' }, { label: 'B', color: 'c6' }, { label: 'osculating circle', color: 'c4' }]);
          ctx.note(`At t = ${r4(t)}: speed ${r4(speed(c, t))}, curvature κ = ${r4(k)}, torsion τ = ${r4(torsion(c, t))}. T and N span the osculating plane; τ measures how fast it turns about T.`);
        }
      },
    },
    curvature_comb: {
      doc: 'curvature_comb(c, a, b) draws a plane curve with a comb of normals whose lengths are proportional to the curvature (the engineer\'s check that a curve bends smoothly), and the curvature against t.',
      render(ctx, c, a, b) {
        [a, b] = rangeOf(c, a, b);
        const C = curveFn(c);
        const ts = Array.from({ length: 401 }, (_, k) => a + (b - a) * k / 400);
        const pts = ts.map(s => v3(C(s)));
        const ks = ts.map(s => { try { return curvature(c, s); } catch (e) { return NaN; } });
        const kmax = Math.max(1e-9, ...ks.filter(Number.isFinite).map(Math.abs).sort((x, y) => x - y).slice(0, Math.floor(ks.length * 0.97)));
        const ext = Math.max(...pts.flat().map(Math.abs), 1);
        const fig = ctx.figure({ square: true });
        const tips = [];
        for (let i = 0; i <= 400; i += 4) {
          const s = ts[i], k = ks[i];
          if (!Number.isFinite(k)) continue;
          const N = v3(normalVec(c, s)), len = -Math.min(k, 3 * kmax) / kmax * ext * 0.35, q = add(pts[i], scale(N, len));
          fig.seg(pts[i][0], pts[i][1], q[0], q[1], { color: 'c4', width: 1, alpha: 0.7 });
          tips.push([q[0], q[1]]);
        }
        fig.curve(tips, { color: 'c4', width: 1, alpha: 0.5 });
        fig.curve(pts.map(q => [q[0], q[1]]), { color: 'c1', width: 2.2 });
        const g = ctx.figure({ x: [a, b], xlabel: 't', height: 150 });
        g.curve(ts.map((s, i) => [s, ks[i]]).filter(q => Number.isFinite(q[1]) && q[1] <= 5 * kmax), { color: 'c4', width: 2 });
        ctx.legend([{ label: 'curve', color: 'c1' }, { label: 'curvature comb (and κ against t)', color: 'c4' }]);
        ctx.note(`Curvature from ${r4(Math.min(...ks.filter(Number.isFinite)))} to ${r4(Math.max(...ks.filter(Number.isFinite)))}; total turning ∫κ ds = ${r4(totalTurning(c, a, b))}${Math.abs(totalTurning(c, a, b) - TAU) < 1e-4 ? ' = 2π' : ''}.`);
      },
    },
    surface_curvature: {
      doc: 'surface_curvature(s, u0, u1, v0, v1) draws the surface twice, colored by its Gaussian curvature K (orange positive: curved like a sphere; blue negative: like a saddle; gray flat) and by its mean curvature H, with ∫∫K dA (Gauss–Bonnet).',
      render(ctx, s, ...r) {
        const [u0, u1, v0, v1] = domainOf(s, r);
        const S = surfFn(s);
        for (const [name, fn] of [['Gaussian curvature K', gaussCurvature], ['mean curvature H', meanCurvature]]) {
          ctx.note(name, 'view-caption');
          const fig = ctx.figure3d({ labels: ['x', 'y', 'z'] });
          fig.surface((u, v) => S(u, v), { u: [u0, u1], v: [v0, v1], n: 34, value: (u, v) => fn(s, u, v), wire: false });
        }
        const sample = [];
        for (let i = 1; i < 8; i++) for (let j = 1; j < 8; j++) sample.push(gaussCurvature(s, u0 + (u1 - u0) * i / 8, v0 + (v1 - v0) * j / 8));
        const tot = totalCurvature(s, u0, u1, v0, v1);
        ctx.legend([{ label: 'positive', color: 'c2' }, { label: 'zero', color: 'vac' }, { label: 'negative', color: 'c1' }]);
        ctx.note(`K ranges over about [${r4(Math.min(...sample))}, ${r4(Math.max(...sample))}]; ∫∫ K dA ${Math.abs(tot) < 1e-6 ? '≈ 0' : Math.abs(tot / Math.PI - Math.round(tot / Math.PI)) < 1e-4 ? `≈ ${Math.round(tot / Math.PI)}π` : `= ${r4(tot)}`}. Area ${r4(surfaceArea(s, u0, u1, v0, v1))}.`);
      },
    },
  };

  MathViz.define({
    name: 'curves',
    description: 'Curves and surfaces: speed, curvature, torsion, the Frenet frame, arc length and total turning of curves in the plane and in space; normals, the first and second fundamental forms, Gaussian and mean curvature, area and total curvature of parametrized surfaces; catalogs of classic curves and surfaces; views of the moving frame, curvature combs and surfaces colored by curvature.',
    functions: {
      speed: { doc: 'speed(c, t) = |c′(t)|.', fn: speed },
      curvature: { doc: 'curvature(c, t) = |c′ × c″| / |c′|³, how sharply the curve bends: 1/r on a circle of radius r, the same for any parametrization.', fn: curvature },
      signed_curvature: { doc: 'signed_curvature(c, t): the curvature of a plane curve with a sign, positive when it turns left.', fn: signedCurvature },
      torsion: { doc: 'torsion(c, t) = (c′ × c″)·c‴ / |c′ × c″|²: how fast the curve leaves its osculating plane (0 for plane curves; undefined where the curvature is 0).', fn: torsion },
      tangent: { doc: 'tangent(c, t): the unit tangent T.', fn: tangent },
      principal_normal: { doc: 'principal_normal(c, t): the principal unit normal N, pointing to the inside of the bend.', fn: normalVec },
      binormal: { doc: 'binormal(c, t) = T × N, for curves in space.', fn: binormal },
      arc_length: { doc: 'arc_length(c, a, b) = ∫ₐᵇ |c′(t)| dt.', fn: arcLength },
      total_turning: { doc: 'total_turning(c, a, b) = ∫ κ ds, the total angle the tangent turns through: at least 2π on a closed curve (Fenchel), more than 4π on a knot (Fáry–Milnor).', fn: totalTurning },
      gauss_curvature: { doc: 'gauss_curvature(s, u, v) = (LN − M²)/(EG − F²): positive where the surface is curved like a sphere, negative like a saddle, 0 like a plane or cylinder. It depends only on lengths measured in the surface (Gauss\'s Theorema Egregium).', fn: gaussCurvature },
      mean_curvature: { doc: 'mean_curvature(s, u, v) = (EN − 2FM + GL)/(2(EG − F²)), the average of the principal curvatures; 0 on minimal surfaces such as soap films.', fn: meanCurvature },
      surface_normal: { doc: 'surface_normal(s, u, v): the unit normal s_u × s_v / |s_u × s_v|.', fn: surfaceNormal },
      first_form: { doc: 'first_form(s, u, v): the matrix [[E, F], [F, G]] of the first fundamental form, which measures lengths on the surface.', fn: firstForm },
      second_form: { doc: 'second_form(s, u, v): the matrix [[L, M], [M, N]] of the second fundamental form, which measures how the surface bends in space.', fn: secondForm },
      surface_area: { doc: 'surface_area(s, u0, u1, v0, v1) = ∫∫ √(EG − F²) du dv (the ranges can be left out for the catalog\'s surfaces).', fn: surfaceArea },
      total_curvature: { doc: 'total_curvature(s, u0, u1, v0, v1) = ∫∫ K dA: 4π on a sphere, 0 on a torus (Gauss–Bonnet).', fn: totalCurvature },
    },
    spaces: {
      Curves: { doc: 'Curves: example curves t ↦ c(t): circle, ellipse, figure eight, trefoil knot, parabola, helix, twisted cubic, cycloid, logarithmic spiral, a line.', fn: Curves },
      ClosedCurves: { doc: 'ClosedCurves: the closed example curves, each traced once for t in [0, 2π].', fn: ClosedCurves },
      Surfaces: { doc: 'Surfaces: example surfaces (u, v) ↦ s(u, v): spheres, cylinder, cone, torus, saddle, paraboloid, plane, catenoid, helicoid.', fn: Surfaces },
    },
    views,
    notation: `
# The curvature of a circle of radius 2 is 1/2 everywhere.
lemma circle_curvature: forall t in [0, 6]: |curvature(t => (2cos(t), 2sin(t)), t) - 1/2| < 1e-6

# Curvature doesn't depend on the parametrization: the same circle traced at speed 6t².
lemma curvature_reparametrized: forall t in [0.4, 1.8]: |curvature(t => (2cos(t^3), 2sin(t^3)), t) - 1/2| < 1e-5

# A helix (cos t, sin t, bt) has constant curvature 1/(1 + b²) and torsion b/(1 + b²).
lemma helix_frame: forall t in [0, 10]: |curvature(t => (cos(t), sin(t), t/2), t) - 0.8| < 1e-6 and |torsion(t => (cos(t), sin(t), t/2), t) - 0.4| < 1e-4

# Does constant curvature make a curve plane? In the plane it makes a circle; in space the helix says no.
conjecture constant_curvature_plane: forall c in Curves: (forall s, t in [0.5, 2.5]: |curvature(c, s) - curvature(c, t)| < 1e-6) -> torsion(c, 1) = 0

# Fenchel: a closed curve turns through at least 2π.
lemma fenchel: forall c in ClosedCurves: total_turning(c, 0, 2*pi) >= 2*pi - 1e-6

# Is it exactly 2π? Only for convex plane curves: the trefoil turns through more than 4π (Fáry–Milnor).
conjecture turning_exactly_2pi: forall c in ClosedCurves: |total_turning(c, 0, 2*pi) - 2*pi| < 1e-4

# A sphere of radius 2 has Gaussian curvature 1/4 and mean curvature ±1/2 everywhere.
lemma sphere_curvatures: forall u in [0, 6], v in [-1.3, 1.3]: |gauss_curvature((u, v) => (2*cos(u)*cos(v), 2*sin(u)*cos(v), 2*sin(v)), u, v) - 1/4| < 1e-5

# Catenoids and helicoids are minimal surfaces: mean curvature 0.
lemma minimal_surfaces: forall u in [0, 6], v in [-1, 1]: |mean_curvature((u, v) => (cosh(v)*cos(u), cosh(v)*sin(u), v), u, v)| < 1e-5 and |mean_curvature((u, v) => (v*cos(u), v*sin(u), u), u, v)| < 1e-5

# Is a surface with K = 0 flat in the other sense too (H = 0)? The cylinder and the cone bend one way only.
conjecture zero_K_zero_H: forall S in Surfaces, u, v in [0.3, 1.2]: |gauss_curvature(S, u, v)| < 1e-6 -> |mean_curvature(S, u, v)| < 1e-6

# Gauss–Bonnet: the total curvature of a closed surface is 2π times its Euler characteristic.
lemma gauss_bonnet: |total_curvature((u, v) => (cos(u)*cos(v), sin(u)*cos(v), sin(v)), 0, 2*pi, -pi/2, pi/2) - 4*pi| < 1e-4 and |total_curvature((u, v) => ((2 + cos(v))*cos(u), (2 + cos(v))*sin(u), sin(v)), 0, 2*pi, 0, 2*pi)| < 1e-4
`,
  });
});
