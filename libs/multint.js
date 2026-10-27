MathVizLibrary(function multint(MathViz) {
  /* Integration in ℝⁿ and vector analysis, following the book definitions:
     rectangles and their volume, step functions and the upper and lower integrals, Fubini,
     integrals over sets between graphs, parameter integrals, the transformation formula; charts,
     tangent and normal spaces, the Gramian determinant, surface, line and flux integrals, div,
     curl and the Laplacian, and the theorems of Green, Stokes and Gauss as checks. */
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const isVec = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');
  const short = x => fmt(+(+x).toPrecision(5));
  const MVL = () => MathViz.shared.multivar || {};

  /* ---------- integration: adaptive Gauss–Legendre ---------- */
  const GX = [-0.9602898564975363, -0.7966664774136267, -0.5255324099163290, -0.1834346424956498, 0.1834346424956498, 0.5255324099163290, 0.7966664774136267, 0.9602898564975363];
  const GW = [0.1012285362903763, 0.2223810344533745, 0.3137066458778873, 0.3626837833783620, 0.3626837833783620, 0.3137066458778873, 0.2223810344533745, 0.1012285362903763];
  const gl = (f, a, b) => { const m = (a + b) / 2, h = (b - a) / 2; let s = 0; for (let i = 0; i < 8; i++) s += GW[i] * f(m + h * GX[i]); return s * h; };
  // ∫_a^b f, splitting where the 8-point rule and its two halves disagree.
  function adapt(f, a, b, tol = 1e-10) {
    if (a === b) return 0;
    let budget = 4000;
    const rec = (lo, hi, whole, t, depth) => {
      const m = (lo + hi) / 2, L = gl(f, lo, m), R = gl(f, m, hi);
      if (--budget < 0 || depth > 40 || Math.abs(L + R - whole) <= t * Math.max(1, Math.abs(L + R))) return L + R;
      return rec(lo, m, L, t / 1.6, depth + 1) + rec(m, hi, R, t / 1.6, depth + 1);
    };
    return rec(a, b, gl(f, a, b), tol, 0);
  }
  // Calling a function of a point: f(x, y) when it takes the coordinates separately, else f(p).
  const at = (f, p) => {
    if (typeof f === 'number') return f;
    need(typeof f === 'function', 'Expected a function.');
    const k = f.arity || f.length;
    return Array.isArray(p) && p.length > 1 && k === p.length ? f(...p) : f(p);
  };
  const num = v => { const x = +v; return x; };

  /* ---------- rectangles (Definition 11.1) ---------- */
  function Cuboid(...edges) {
    if (edges.length === 1 && Array.isArray(edges[0]) && edges[0].every(Array.isArray)) edges = edges[0];
    need(edges.length >= 1 && edges.every(e => isVec(e) && e.length === 2 && e[0] < e[1]), 'Cuboid([a₁, b₁], [a₂, b₂], …) needs intervals with aᵢ < bᵢ, as in Cuboid([0, 1], [0, 2]).');
    const n = edges.length;
    const label = edges.map(([a, b]) => `[${fmt(a)}, ${fmt(b)}]`).join(' × ');
    const S = MathViz.space({
      label, window: n === 1 ? edges[0].slice() : edges.map(e => e.slice()),
      contains: p => (n === 1 ? typeof p === 'number' || (isVec(p) && p.length === 1) : isVec(p) && p.length === n) &&
        (n === 1 ? [p].flat() : p).every((x, i) => MathViz.ops.le(edges[i][0], x) && MathViz.ops.le(x, edges[i][1])),
    });
    S.edges = edges;
    return S;
  }
  const edgesOf = Q => {
    if (Q && Q.edges) return Q.edges;
    if (isVec(Q) && Q.length === 2) return [Q];
    const D = MathViz.toDomain(Q), w = D.window && D.window();
    need(w, 'Expected a rectangle, such as Cuboid([0, 1], [0, 2]) or an interval [a, b].');
    return Array.isArray(w[0]) ? w : [w];
  };
  const vol = Q => edgesOf(Q).reduce((v, [a, b]) => v * (b - a), 1);

  // ∫_Q f over a rectangle: nested adaptive rules in one or two dimensions, a composite rule in three.
  function integrate(f, Q) {
    const E = edgesOf(Q), n = E.length;
    MathViz.markInexact();
    if (n === 1) return adapt(x => num(at(f, x)), E[0][0], E[0][1]);
    if (n === 2) return adapt(x => adapt(y => num(at(f, [x, y])), E[1][0], E[1][1], 1e-11), E[0][0], E[0][1], 1e-8);
    need(n === 3, 'integrate works in up to three dimensions.');
    const P = 4, nodes = E.map(([a, b]) => { const out = []; for (let k = 0; k < P; k++) { const lo = a + (b - a) * k / P, hi = a + (b - a) * (k + 1) / P, m = (lo + hi) / 2, h = (hi - lo) / 2; for (let i = 0; i < 8; i++) out.push([m + h * GX[i], h * GW[i]]); } return out; });
    let s = 0;
    for (const [x, wx] of nodes[0]) for (const [y, wy] of nodes[1]) for (const [z, wz] of nodes[2]) s += wx * wy * wz * num(at(f, [x, y, z]));
    return s;
  }
  // ∫_a^b ∫_lo(x)^hi(x) f(x, y) dy dx: a set between two graphs (Remark 11.14).
  function integralBetween(f, a, b, lo, hi) {
    need(typeof lo === 'function' && typeof hi === 'function', 'integral_between(f, a, b, lo, hi): lo and hi are functions of x.');
    MathViz.markInexact();
    return adapt(x => { const l = num(lo(x)), h = num(hi(x)); return h > l ? adapt(y => num(at(f, [x, y])), l, h, 1e-11) : 0; }, a, b, 1e-8);
  }
  // ∫_S f over a set of the line or the plane, by cells of a grid (an estimate: cells on the
  // boundary count by their centres).
  function integralOver(f, S, n = 400) {
    const D = MathViz.toDomain(S), w = D.window();
    MathViz.markInexact();
    if (!Array.isArray(w[0])) { const h = (w[1] - w[0]) / n; let s = 0; for (let i = 0; i < n; i++) { const x = w[0] + (i + 0.5) * h; if (D.contains(x)) s += num(at(f, x)) * h; } return s; }
    need(w.length === 2, 'integral_over works for sets of the line or the plane.');
    const hx = (w[0][1] - w[0][0]) / n, hy = (w[1][1] - w[1][0]) / n;
    let s = 0;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
      const p = [w[0][0] + (i + 0.5) * hx, w[1][0] + (j + 0.5) * hy];
      if (D.contains(p)) s += num(at(f, p)) * hx * hy;
    }
    return s;
  }

  /* ---------- step functions below and above f (Definitions 11.2, 11.3, 11.6) ---------- */
  // The n-per-side grid of Q; on each cell the step functions take the smallest and largest value of
  // f found there (corners, edges and inside), so φ ≤ f ≤ ψ as far as the samples show.
  function stepBounds(f, Q, n) {
    const E = edgesOf(Q), d = E.length;
    need(d <= 2, 'Step functions are drawn on intervals and rectangles of the plane.');
    need(Number.isInteger(n) && n >= 1 && n <= 400, 'The grid has n = 1 … 400 cells per side.');
    MathViz.markInexact();
    const k = 5, cells = [];
    const h = E.map(([a, b]) => (b - a) / n);
    const idx = d === 1 ? Array.from({ length: n }, (_, i) => [i]) : Array.from({ length: n * n }, (_, t) => [Math.floor(t / n), t % n]);
    for (const ix of idx) {
      const lo = ix.map((i, j) => E[j][0] + i * h[j]);
      let mn = Infinity, mx = -Infinity;
      const pts = d === 1 ? Array.from({ length: k }, (_, a) => [lo[0] + h[0] * a / (k - 1)]) : Array.from({ length: k * k }, (_, t) => [lo[0] + h[0] * Math.floor(t / k) / (k - 1), lo[1] + h[1] * (t % k) / (k - 1)]);
      for (const p of pts) { const v = num(at(f, d === 1 ? p[0] : p)); if (v < mn) mn = v; if (v > mx) mx = v; }
      cells.push({ lo, h, mn, mx });
    }
    const cellVol = h.reduce((a, b) => a * b, 1);
    return { cells, lower: cells.reduce((s, c) => s + c.mn * cellVol, 0), upper: cells.reduce((s, c) => s + c.mx * cellVol, 0), d, E };
  }
  /* ---------- charts, tangent spaces, the Gramian determinant (Definitions 12.1, 12.5, 12.8) ---------- */
  const isCurveParam = y => typeof y === 'number';
  const callP = (g, y) => (Array.isArray(y) ? ((g.arity || g.length) > 1 && y.length === (g.arity || g.length) ? g(...y) : g(y)) : g(y));
  // ∂Φ/∂yᵢ at y: exact for formulas (through multivar), else by central differences.
  function dcol(Phi, y, i) {
    const P = MVL().partial;
    if (P) {
      const g = P(Phi, i);
      if (g.__symbolic) { const v = callP(g, y); if (isVec(v) || typeof v === 'number') return [v].flat(); }
    }
    MathViz.markInexact();
    const yy = isCurveParam(y) ? [y] : y.slice(), h = 1e-6 * Math.max(1, Math.abs(yy[i - 1]));
    const up = yy.slice(), dn = yy.slice(); up[i - 1] += h; dn[i - 1] -= h;
    const A = [callP(Phi, isCurveParam(y) ? up[0] : up)].flat().map(Number), B = [callP(Phi, isCurveParam(y) ? dn[0] : dn)].flat().map(Number);
    return A.map((x, k) => (x - B[k]) / (2 * h));
  }
  const dimOfParam = y => (isCurveParam(y) ? 1 : y.length);
  const tangentVectors = (Phi, y) => Array.from({ length: dimOfParam(y) }, (_, i) => dcol(Phi, y, i + 1));
  const dot = (a, b) => a.reduce((s, x, i) => s + x * b[i], 0);
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const det = M => (M.length === 1 ? M[0][0] : M.length === 2 ? M[0][0] * M[1][1] - M[0][1] * M[1][0]
    : M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]));
  const gram = (Phi, y) => { const T = tangentVectors(Phi, y); return det(T.map(a => T.map(b => dot(a, b)))); };
  // A unit normal: for a curve of the plane the tangent turned clockwise (outward for a curve that
  // goes round anticlockwise); for a surface in space ∂₁Φ × ∂₂Φ normalised (Definition 12.14).
  function normalVector(Phi, y) {
    const T = tangentVectors(Phi, y);
    let v;
    if (T.length === 1 && T[0].length === 2) v = [T[0][1], -T[0][0]];
    else if (T.length === 2 && T[0].length === 3) v = cross(T[0], T[1]);
    else throw MathViz.error('normal_vector is for curves in the plane and surfaces in space.');
    const L = Math.hypot(...v);
    return v.map(x => x / L);
  }
  // Rank of DΦ(y): how many tangent vectors are independent (Definition 12.1(ii)).
  function chartRank(Phi, y) {
    const T = tangentVectors(Phi, y), s = Math.max(1, ...T.flat().map(Math.abs));
    if (T.length === 1) return Math.hypot(...T[0]) > 1e-9 * s ? 1 : 0;
    const g = gram(Phi, y);
    if (g > 1e-12 * s ** 4) return T.length;
    return T.some(v => Math.hypot(...v) > 1e-9 * s) ? 1 : 0;
  }
  // Injective on W (Definition 12.1(i)): no two parameters far apart give the same point. Images of
  // many parameters are compared; nearly equal ones are pushed together by a local search.
  function injectiveOn(Phi, W) {
    const E = edgesOf(W), d = E.length;
    MathViz.markInexact();
    const N = d === 1 ? 1500 : 45, ys = [];
    if (d === 1) for (let i = 0; i < N; i++) ys.push(E[0][0] + (E[0][1] - E[0][0]) * (i + 0.5) / N);
    else for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) ys.push([E[0][0] + (E[0][1] - E[0][0]) * (i + 0.5) / N, E[1][0] + (E[1][1] - E[1][0]) * (j + 0.5) / N]);
    const img = ys.map(y => [callP(Phi, y)].flat().map(Number));
    const scale = Math.max(1e-9, ...img.flat().map(Math.abs));
    const pd = (a, b) => (d === 1 ? Math.abs(a - b) : Math.hypot(a[0] - b[0], a[1] - b[1]));
    const span = Math.max(...E.map(([a, b]) => b - a));
    const order = img.map((p, i) => i).sort((a, b) => img[a][0] - img[b][0]);
    const gap = Math.max(3 * span / N, 0.02 * span);   // parameters substantially apart
    for (let s = 0; s < order.length; s++) for (let t = s + 1; t < order.length && img[order[t]][0] - img[order[s]][0] < 0.02 * scale; t++) {
      const i = order[s], j = order[t];
      if (pd(ys[i], ys[j]) < gap) continue;
      if (Math.hypot(...img[i].map((x, k) => x - img[j][k])) > 0.02 * scale) continue;
      // Push the two parameters towards each other's image.
      let a = d === 1 ? [ys[i]] : ys[i].slice(), b = d === 1 ? [ys[j]] : ys[j].slice();
      const val = (u, v) => Math.hypot(...[callP(Phi, d === 1 ? u[0] : u)].flat().map((x, k) => x - [callP(Phi, d === 1 ? v[0] : v)].flat()[k]));
      let cur = val(a, b), h = span / N;
      for (let it = 0; it < 400 && h > 1e-13 * span; it++) {
        let moved = false;
        for (const which of [0, 1]) for (let k = 0; k < d; k++) for (const sg of [1, -1]) {
          const u = (which ? b : a).slice(); u[k] += sg * h;
          if (u[k] < E[k][0] || u[k] > E[k][1]) continue;
          const v = which ? val(a, u) : val(u, b);
          if (v < cur) { cur = v; if (which) b = u; else a = u; moved = true; }
        }
        if (!moved) h /= 2;
      }
      if (cur < 1e-9 * scale && Math.hypot(...a.map((x, k) => x - b[k])) > gap / 3) return false;
    }
    return true;
  }

  /* ---------- integrals on submanifolds (Definitions 12.8, 12.12, 12.14) ---------- */
  const paramEdges = W => (isVec(W) && W.length === 2 && !W.edges ? [W] : edgesOf(W));
  const integrateParams = (g, W) => {
    const E = paramEdges(W);
    MathViz.markInexact();
    if (E.length === 1) return adapt(t => g(t), E[0][0], E[0][1], 1e-9);
    // The inner integrals much more accurate than the outer test, or their noise forces endless splitting.
    return adapt(s => adapt(t => g([s, t]), E[1][0], E[1][1], 1e-10), E[0][0], E[0][1], 1e-7);
  };
  // ∫_M f dS = ∫_W f(Φ(y)) √g_Φ(y) dy.
  const surfaceIntegral = (f, Phi, W) => integrateParams(y => num(at(f, [callP(Phi, y)].flat().map(Number))) * Math.sqrt(Math.max(0, gram(Phi, y))), W);
  // ∫_γ F · ds = ∫_a^b ⟨F(γ(t)), γ′(t)⟩ dt.
  const lineIntegral = (F, gamma, a, b) => integrateParams(t => dot([at(F, [callP(gamma, t)].flat().map(Number))].flat().map(Number), dcol(gamma, t, 1)), [a, b]);
  // The flux of F through Φ(W): ∫_W ⟨F(Φ(y)), ∂₁Φ × ∂₂Φ⟩ dy; for a curve of the plane, the flux
  // through it, ∫ ⟨F, (γ₂′, −γ₁′)⟩ dt (out of the region a curve going round anticlockwise encloses).
  function flux(F, Phi, W) {
    const E = paramEdges(W);
    if (E.length === 1) return integrateParams(t => { const T = dcol(Phi, t, 1), v = [at(F, [callP(Phi, t)].flat().map(Number))].flat().map(Number); return v[0] * T[1] - v[1] * T[0]; }, W);
    return integrateParams(y => dot([at(F, [callP(Phi, y)].flat().map(Number))].flat().map(Number), cross(dcol(Phi, y, 1), dcol(Phi, y, 2))), W);
  }

  /* ---------- div, curl, Laplacian ---------- */
  const jac = (F, p) => { const J = MVL().jacobian; need(J, 'div and curl need the multivar library.'); return J(F, p); };
  const divF = (F, p) => { need(isVec(p), 'div(F, p) needs a point.'); const J = jac(F, p); return J.reduce((s, r, i) => s + r[i], 0); };
  function curlF(F, p) {
    need(isVec(p) && (p.length === 2 || p.length === 3), 'curl(F, p) needs a point of the plane or of space.');
    const J = jac(F, p);   // J[i][j] = ∂Fᵢ/∂xⱼ
    if (p.length === 2) return J[1][0] - J[0][1];
    return [J[2][1] - J[1][2], J[0][2] - J[2][0], J[1][0] - J[0][1]];
  }
  const laplacian = (f, p) => { const H = MVL().hessian; need(H && isVec(p), 'laplacian(f, p) needs a point.'); const M = H(f, p); return M.reduce((s, r, i) => s + r[i], 0); };

  /* ---------- plane regions bounded by a closed curve (for Green and Gauss) ---------- */
  function regionOf(gamma, a, b, m = 600) {
    const poly = Array.from({ length: m }, (_, k) => [callP(gamma, a + (b - a) * k / m)].flat().map(Number));
    const inside = (x, y) => { let c = false; for (let i = 0, j = m - 1; i < m; j = i++) { const [xi, yi] = poly[i], [xj, yj] = poly[j]; if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c; } return c; };
    const xs = poly.map(p => p[0]), ys = poly.map(p => p[1]);
    return { poly, inside, box: [[Math.min(...xs), Math.max(...xs)], [Math.min(...ys), Math.max(...ys)]] };
  }

  MathViz.define({
    name: 'multint',
    requires: ['multivar', 'linalg', 'analysis'],
    description: 'Integration in ℝⁿ and vector analysis: rectangles, step functions and the upper and lower integrals, Fubini, integrals between graphs, the transformation formula; charts, tangent and normal spaces, the Gramian determinant, surface, line and flux integrals, div, curl and the Laplacian, with the theorems of Green, Stokes and Gauss as checks, and views of each.',
    functions: {
      Cuboid: { doc: 'Cuboid([a₁, b₁], [a₂, b₂], …): the rectangle (cuboid) [a₁, b₁] × [a₂, b₂] × … (Definition 11.1), as a set to integrate over, quantify over or draw.', fn: Cuboid },
      vol: { doc: 'vol(Q): the volume (b₁ − a₁)·(b₂ − a₂)·… of a rectangle (Definition 11.1(ii)).', fn: vol },
      integrate: { doc: 'integrate(f, Q): ∫_Q f over a rectangle (or an interval [a, b]), by adaptive Gauss–Legendre rules; f may take the coordinates, f(x, y), or a point, f(p).', fn: integrate },
      integral_between: { doc: 'integral_between(f, a, b, lo, hi): ∫ₐᵇ ∫ from lo(x) to hi(x) of f(x, y) dy dx, the integral over the set between two graphs (Remark 11.14).', fn: integralBetween },
      integral_over: { doc: 'integral_over(f, S, n): ∫_S f over a set of the line or the plane, from an n × n grid of cells (an estimate).', fn: integralOver },
      lower_step_integral: { doc: 'lower_step_integral(f, Q, n): ∫ φ for the step function φ ≤ f taking on each of the n × n cells of Q the least value of f found there (Definitions 11.3 and 11.6).', fn: (f, Q, n) => stepBounds(f, Q, n).lower },
      upper_step_integral: { doc: 'upper_step_integral(f, Q, n): ∫ ψ for the step function ψ ≥ f taking on each cell the largest value of f found there.', fn: (f, Q, n) => stepBounds(f, Q, n).upper },
      integrable_rect: { doc: 'integrable_rect(f, Q): whether f looks Riemann integrable on Q: the gap between the upper and lower step integrals keeps shrinking as the grid gets finer (Theorem 11.8). An estimate.', fn: (f, Q) => { const E = edgesOf(Q), sizes = E.length === 1 ? [8, 32, 128, 400] : [4, 16, 64]; const gaps = sizes.map(n => { const b = stepBounds(f, Q, n); return b.upper - b.lower; }); return gaps.every(Number.isFinite) && (gaps[gaps.length - 1] <= 1e-12 * Math.max(1, vol(Q)) || gaps[gaps.length - 1] < gaps[0] / 3); } },
      tangent_vectors: { doc: 'tangent_vectors(Φ, y): the vectors ∂Φ/∂y₁(y), …, ∂Φ/∂y_d(y), which span the tangent space T_pM at p = Φ(y) (Definition 12.5). Exact when Φ is a formula.', fn: tangentVectors },
      normal_vector: { doc: 'normal_vector(Φ, y): a unit normal at Φ(y): for a curve of the plane its tangent turned clockwise, for a surface in space ∂₁Φ × ∂₂Φ normalised (Definition 12.14).', fn: normalVector },
      gram: { doc: 'gram(Φ, y): the Gramian determinant g_Φ(y) = det(DΦ(y)ᵀ DΦ(y)), the squared area (or length) factor of the chart (Definition 12.8).', fn: gram },
      chart_rank: { doc: 'chart_rank(Φ, y): the rank of DΦ(y); a chart needs it to be d, the number of parameters (Definition 12.1(ii)).', fn: chartRank },
      injective_on: { doc: 'injective_on(Φ, W): whether Φ takes different points of the rectangle W to different points (Definition 12.1(i)), judged from many parameters and a search near every pair of nearly equal images. An estimate.', fn: injectiveOn },
      surface_integral: { doc: 'surface_integral(f, Φ, W): ∫_M f dS = ∫_W f(Φ(y)) √g_Φ(y) dy for the chart Φ on W, an interval [a, b] for a curve or a rectangle for a surface (Definition 12.8).', fn: surfaceIntegral },
      line_integral: { doc: 'line_integral(F, γ, a, b): ∫_γ F · ds = ∫ₐᵇ ⟨F(γ(t)), γ′(t)⟩ dt (Definition 12.12).', fn: lineIntegral },
      flux: { doc: 'flux(F, Φ, W): ∫ F · dS = ∫_W ⟨F(Φ(y)), ∂₁Φ × ∂₂Φ⟩ dy through a surface in space (Definition 12.14); for a curve γ of the plane on W = [a, b], the flux ∫ ⟨F, (γ₂′, −γ₁′)⟩ dt across it.', fn: flux },
      div: { doc: 'div(F, p): ∂F₁/∂x₁ + … + ∂Fₙ/∂xₙ at p (exact for formulas).', fn: divF },
      curl: { doc: 'curl(F, p): ∇ × F at p, a vector for fields in space; in the plane the number ∂F₂/∂x₁ − ∂F₁/∂x₂ (Theorems 12.17 and 12.18).', fn: curlF },
      laplacian: { doc: 'laplacian(f, p): Δf = ∂²f/∂x₁² + … + ∂²f/∂xₙ² at p, which is div(∇f) (Remark 12.21).', fn: laplacian },
    },
    views: {
      step_integral: {
        doc: 'step_integral(f, Q) draws f over an interval or a rectangle with the step functions φ ≤ f ≤ ψ on an n × n grid: on each cell the least and the largest value of f (Definitions 11.2–11.6). Drag n: ∫ψ − ∫φ shrinks to 0 for a continuous f (Theorems 11.8 and 11.9).',
        render(ctx, f, Q) {
          const E = edgesOf(Q), d = E.length;
          const n = Math.round(ctx.param('n', { min: 1, max: d === 1 ? 64 : 24, step: 1, value: d === 1 ? 6 : 4 }));
          const B = stepBounds(f, Q, n);
          if (d === 1) {
            const fig = ctx.figure({ x: [E[0][0] - 0.05 * (E[0][1] - E[0][0]), E[0][1] + 0.05 * (E[0][1] - E[0][0])] });
            for (const c of B.cells) {
              fig.rect(c.lo[0], 0, c.lo[0] + c.h[0], c.mx, { color: 'c2', alpha: 0.18 });
              fig.rect(c.lo[0], 0, c.lo[0] + c.h[0], c.mn, { color: 'c3', alpha: 0.35 });
            }
            fig.curve(x => num(at(f, x)), { color: 'c1', width: 2, n: 600 });
          } else {
            const fig = ctx.figure3d({ labels: ['x₁', 'x₂', 'f'], equal: false });
            fig.surface((u, v) => [u, v, num(at(f, [u, v]))], { u: E[0], v: E[1], n: 26 });
            for (const c of B.cells) {
              const [x0, y0] = c.lo, x1 = x0 + c.h[0], y1 = y0 + c.h[1];
              fig.poly([[x0, y0, c.mx], [x1, y0, c.mx], [x1, y1, c.mx], [x0, y1, c.mx]], { color: 'c2', alpha: 0.22, stroke: 'c2' });
              fig.poly([[x0, y0, c.mn], [x1, y0, c.mn], [x1, y1, c.mn], [x0, y1, c.mn]], { color: 'c3', alpha: 0.35, stroke: 'c3' });
            }
          }
          ctx.legend([{ label: 'f', color: 'c1' }, { label: 'ψ ≥ f (upper step function)', color: 'c2' }, { label: 'φ ≤ f (lower step function)', color: 'c3' }]);
          ctx.note(`With ${n}${d === 2 ? ' × ' + n : ''} cells: ∫φ = ${short(B.lower)} ≤ ∫f ≤ ∫ψ = ${short(B.upper)}; the gap is ${short(B.upper - B.lower)}. For a continuous f it shrinks like 1/n, so the upper and lower integrals agree: f is Riemann integrable.`);
        },
      },
      fubini: {
        doc: 'fubini(f, Q) slices the volume under f over a rectangle at x₁ = t (drag t). The slice has area A(t) = ∫ f(t, x₂) dx₂, drawn below; the area under A is ∫∫ f (Theorem 11.11).',
        render(ctx, f, Q) {
          const E = edgesOf(Q);
          need(E.length === 2, 'fubini draws a rectangle of the plane.');
          const t = ctx.param('t', { min: E[0][0], max: E[0][1], step: (E[0][1] - E[0][0]) / 200, value: (E[0][0] + E[0][1]) / 2 });
          const fig = ctx.figure3d({ labels: ['x₁', 'x₂', 'f'], equal: false });
          fig.surface((u, v) => [u, v, num(at(f, [u, v]))], { u: E[0], v: E[1], n: 24, alpha: 0.6 });
          const slice = Array.from({ length: 61 }, (_, k) => { const y = E[1][0] + (E[1][1] - E[1][0]) * k / 60; return [t, y, num(at(f, [t, y]))]; });
          fig.poly([[t, E[1][0], 0], ...slice, [t, E[1][1], 0]], { color: 'c2', alpha: 0.55, stroke: 'c2' });
          const A = x => adapt(y => num(at(f, [x, y])), E[1][0], E[1][1], 1e-8);
          const fig2 = ctx.figure({ x: E[0], xlabel: 'x₁', ylabel: 'A(x₁)', height: 220 });
          const pts = Array.from({ length: 121 }, (_, k) => { const x = E[0][0] + (E[0][1] - E[0][0]) * k / 120; return [x, A(x)]; });
          fig2.poly([[E[0][0], 0], ...pts.filter(p => p[0] <= t), [t, 0]], { color: 'c2', alpha: 0.25 });
          fig2.curve(pts, { color: 'c2', width: 2 });
          fig2.points([[t, A(t)]], { color: 'c2', r: 4 });
          const total = adapt(A, E[0][0], E[0][1], 1e-8), other = adapt(y => adapt(x => num(at(f, [x, y])), E[0][0], E[0][1], 1e-8), E[1][0], E[1][1], 1e-8);
          ctx.legend([{ label: `the slice at x₁ = ${short(t)}, of area A(x₁)`, color: 'c2' }]);
          ctx.note(`A(${short(t)}) = ${short(A(t))}. ∫ A(x₁) dx₁ = ${short(total)}; integrating in the other order, ∫ (∫ f dx₁) dx₂ = ${short(other)}. For a continuous f the two agree (Fubini).`);
        },
      },
      change_of_variables: {
        doc: 'change_of_variables(Φ, Q) maps a grid on the rectangle Q of parameters by Φ: ℝ² → ℝ². Each image cell is colored by |det DΦ| there, the factor by which Φ stretches areas, so ∫_Φ(Q) f = ∫_Q f(Φ)·|det DΦ| (Theorem 11.21). Polar coordinates: Φ = (r, φ) => (r·cos(φ), r·sin(φ)).',
        render(ctx, Phi, Q) {
          const E = edgesOf(Q);
          need(E.length === 2, 'change_of_variables maps a rectangle of the plane.');
          const n = Math.round(ctx.param('cells', { min: 2, max: 24, step: 1, value: 10 }));
          const jd = y => { const T = tangentVectors(Phi, y); return T[0][0] * T[1][1] - T[1][0] * T[0][1]; };
          const P = y => [callP(Phi, y)].flat().map(Number);
          const cells = [];
          for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
            const u0 = E[0][0] + (E[0][1] - E[0][0]) * i / n, u1 = E[0][0] + (E[0][1] - E[0][0]) * (i + 1) / n;
            const v0 = E[1][0] + (E[1][1] - E[1][0]) * j / n, v1 = E[1][0] + (E[1][1] - E[1][0]) * (j + 1) / n;
            const edge = (a, b, k = 6) => Array.from({ length: k }, (_, s) => [a[0] + (b[0] - a[0]) * s / k, a[1] + (b[1] - a[1]) * s / k]);
            const loop = [...edge([u0, v0], [u1, v0]), ...edge([u1, v0], [u1, v1]), ...edge([u1, v1], [u0, v1]), ...edge([u0, v1], [u0, v0])];
            cells.push({ loop, img: loop.map(P), J: Math.abs(jd([(u0 + u1) / 2, (v0 + v1) / 2])) });
          }
          const Jmax = Math.max(...cells.map(c => c.J), 1e-12);
          const all = cells.flatMap(c => c.img), xs = all.map(p => p[0]), ys = all.map(p => p[1]);
          const pad = 0.08 * Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys), 1e-9);
          const fig1 = ctx.figure({ x: E[0], y: E[1], height: 220, xlabel: 'y₁', ylabel: 'y₂' });
          for (const c of cells) fig1.poly(c.loop, { color: 'c1', alpha: 0.08 + 0.5 * c.J / Jmax, stroke: 'c1' });
          const fig2 = ctx.figure({ x: [Math.min(...xs) - pad, Math.max(...xs) + pad], y: [Math.min(...ys) - pad, Math.max(...ys) + pad], square: true });
          for (const c of cells) fig2.poly(c.img, { color: 'c2', alpha: 0.08 + 0.5 * c.J / Jmax, stroke: 'c2' });
          const shoelace = pts => Math.abs(pts.reduce((s, p, k) => { const q = pts[(k + 1) % pts.length]; return s + p[0] * q[1] - q[0] * p[1]; }, 0)) / 2;
          const sumImg = cells.reduce((s, c) => s + shoelace(c.img), 0);
          const integral = adapt(u => adapt(v => Math.abs(jd([u, v])), E[1][0], E[1][1], 1e-8), E[0][0], E[0][1], 1e-8);
          ctx.legend([{ label: 'cells of Q (darker: larger |det DΦ|)', color: 'c1' }, { label: 'their images under Φ', color: 'c2' }]);
          ctx.note(`The image cells add up to area ${short(sumImg)}; ∫_Q |det DΦ| = ${short(integral)}. Each small cell's area is multiplied by about |det DΦ| there — the factor in the transformation formula.`);
        },
      },
      chart: {
        doc: 'chart(Φ, W) draws the image of a chart Φ on W — a curve in the plane or in space (W an interval [a, b]) or a surface in space (W a rectangle) — and at the point p = Φ(y) (drag y) the tangent space p + T_pM and the normal space p + N_pM (Definitions 12.1 and 12.5). It warns where the rank of DΦ drops.',
        render(ctx, Phi, W) {
          const E = paramEdges(W), d = E.length;
          const ys = E.map(([a, b], i) => ctx.param(d === 1 ? 'y' : `y${i + 1}`, { min: a, max: b, step: (b - a) / 200, value: a + (b - a) * 0.37 }));
          const y = d === 1 ? ys[0] : ys;
          const P = q => [callP(Phi, q)].flat().map(Number), p = P(y), n = p.length, T = tangentVectors(Phi, y);
          const rank = chartRank(Phi, y), g = gram(Phi, y);
          if (d === 1 && n === 2) {
            const curve = Array.from({ length: 400 }, (_, k) => P(E[0][0] + (E[0][1] - E[0][0]) * k / 399));
            const xs = curve.map(q => q[0]), yy = curve.map(q => q[1]);
            const L = 0.35 * Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...yy) - Math.min(...yy), 1e-9);
            const fig = ctx.figure({ x: [Math.min(...xs) - L / 2, Math.max(...xs) + L / 2], y: [Math.min(...yy) - L / 2, Math.max(...yy) + L / 2], square: true });
            fig.curve(curve, { color: 'c1', width: 2 });
            const t = T[0], tl = Math.hypot(...t) || 1, u = t.map(x => x / tl), nv = [u[1], -u[0]];
            fig.seg(p[0] - L * u[0], p[1] - L * u[1], p[0] + L * u[0], p[1] + L * u[1], { color: 'c2', width: 1.5 });
            fig.seg(p[0] - L * nv[0], p[1] - L * nv[1], p[0] + L * nv[0], p[1] + L * nv[1], { color: 'c3', width: 1.5, dash: [5, 3] });
            fig.arrow(p[0], p[1], p[0] + t[0] * L / tl, p[1] + t[1] * L / tl, { color: 'c2', width: 2.5 });
            fig.points([p], { color: 'ink', r: 4 });
          } else {
            const fig = ctx.figure3d({ equal: true });
            if (d === 1) {
              fig.curve(Array.from({ length: 400 }, (_, k) => P(E[0][0] + (E[0][1] - E[0][0]) * k / 399)), { color: 'c1', width: 2 });
              const t = T[0], tl = Math.hypot(...t) || 1;
              fig.seg(p.map((x, i) => x - t[i] / tl), p.map((x, i) => x + t[i] / tl), { color: 'c2', width: 2 });
            } else {
              fig.surface((a, b) => P([a, b]), { u: E[0], v: E[1], n: 28, alpha: 0.4 });   // see-through, so p's tangent plane shows wherever p is
              const [t1, t2] = T, s1 = Math.hypot(...t1) || 1, s2 = Math.hypot(...t2) || 1, r = 0.5;
              const c = (a, b) => p.map((x, i) => x + r * (a * t1[i] / s1 + b * t2[i] / s2));
              fig.poly([c(-1, -1), c(1, -1), c(1, 1), c(-1, 1)], { color: 'c2', alpha: 0.35, stroke: 'c2' });
              if (rank === 2) { const nv = cross(t1, t2), nl = Math.hypot(...nv); fig.arrow(p, p.map((x, i) => x + 0.8 * nv[i] / nl), { color: 'c3', width: 2.5 }); }
            }
            fig.points([p], { color: 'ink', r: 5 });
          }
          ctx.legend([{ label: 'M = Φ(W)', color: 'c1' }, { label: 'p + T_pM', color: 'c2' }, { label: 'p + N_pM', color: 'c3' }]);
          const fy = d === 1 ? short(y) : '(' + y.map(short).join(', ') + ')';
          if (rank < d) ctx.status('fail', `At y = ${fy} the rank of DΦ is ${rank} < ${d}: Φ is not a chart there (Definition 12.1(ii)), and the tangent space isn't defined.`);
          ctx.note(`p = Φ(${fy}) = (${p.map(short).join(', ')}). T_pM is spanned by ${T.map(v => '(' + v.map(short).join(', ') + ')').join(' and ')}; rank DΦ = ${rank}. √g_Φ(y) = ${short(Math.sqrt(Math.max(0, g)))}: near y, Φ stretches ${d === 1 ? 'lengths' : 'areas'} by this factor (Definition 12.8).`);
        },
      },
      work: {
        doc: 'work(F, γ, a, b) draws a vector field of the plane and a curve γ on [a, b]. Along the curve, F is green where it pushes along γ′ and red where it pushes against; below, the integrand ⟨F(γ(t)), γ′(t)⟩ and its running integral, which ends at ∫_γ F · ds (Definition 12.12).',
        render(ctx, F, gamma, a, b) {
          const P = t => [callP(gamma, t)].flat().map(Number), Fv = p => [at(F, p)].flat().map(Number);
          const curve = Array.from({ length: 300 }, (_, k) => P(a + (b - a) * k / 299));
          const xs = curve.map(q => q[0]), ys = curve.map(q => q[1]);
          const pad = 0.25 * Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys), 1);
          const X = [Math.min(...xs) - pad, Math.max(...xs) + pad], Y = [Math.min(...ys) - pad, Math.max(...ys) + pad];
          const fig = ctx.figure({ x: X, y: Y, square: true });
          const m = 15, vecs = [];
          for (let i = 0; i < m; i++) for (let j = 0; j < m; j++) { const p = [X[0] + (X[1] - X[0]) * (i + 0.5) / m, Y[0] + (Y[1] - Y[0]) * (j + 0.5) / m], v = Fv(p); if (v.every(Number.isFinite)) vecs.push([p, v]); }
          const big = Math.max(1e-12, ...vecs.map(([, v]) => Math.hypot(...v))), L = (X[1] - X[0]) / m * 0.85;
          for (const [p, v] of vecs) fig.arrow(p[0], p[1], p[0] + v[0] / big * L, p[1] + v[1] / big * L, { color: 'faint', width: 1 });
          fig.curve(curve, { color: 'ink', width: 2 });
          const integrand = t => dot(Fv(P(t)), dcol(gamma, t, 1));
          for (let k = 0; k <= 24; k++) {
            const t = a + (b - a) * k / 24, p = P(t), v = Fv(p), s = integrand(t);
            fig.arrow(p[0], p[1], p[0] + v[0] / big * L, p[1] + v[1] / big * L, { color: s >= 0 ? 'pos' : 'neg', width: 2 });
          }
          fig.arrow(...P(b - (b - a) * 0.02), ...P(b), { color: 'ink', width: 2 });
          const ts = Array.from({ length: 201 }, (_, k) => a + (b - a) * k / 200);
          let run = 0;
          const runs = ts.map((t, k) => { if (k) run += gl(integrand, ts[k - 1], t); return [t, run]; });
          const fig2 = ctx.figure({ x: [a, b], xlabel: 't', height: 200 });
          fig2.curve(t => integrand(t), { color: 'c1', width: 1.5, n: 300 });
          fig2.curve(runs, { color: 'c2', width: 2 });
          ctx.legend([{ label: 'F along γ, pushing with it', color: 'pos' }, { label: 'against it', color: 'neg' }, { label: '⟨F(γ(t)), γ′(t)⟩', color: 'c1' }, { label: 'running integral', color: 'c2' }]);
          ctx.note(`∫_γ F · ds = ${short(run)}. Run along γ backwards and the integral changes sign (Remark 12.13); for F = ∇f it is f(γ(b)) − f(γ(a)) whatever the path (Theorem 12.16).`);
        },
      },
      green: {
        doc: 'green(F, γ, a, b) colors the region enclosed by a closed curve γ (going round anticlockwise for t from a to b) by the curl ∂F₂/∂x₁ − ∂F₁/∂x₂ of a field F of the plane, and compares: ∫∫ curl F = ∮ F · ds (Green, Theorem 12.17), and ∫∫ div F = the flux out through γ (Gauss in the plane, Question 12.8).',
        render(ctx, F, gamma, a, b) {
          const R = regionOf(gamma, a, b);
          const [[x0, x1], [y0, y1]] = R.box, pad = 0.15 * Math.max(x1 - x0, y1 - y0);
          const X = [x0 - pad, x1 + pad], Y = [y0 - pad, y1 + pad];
          const fig = ctx.figure({ x: X, y: Y, square: true });
          const cu = p => curlF(F, p), dv = p => divF(F, p);
          const mix = (A, B, t) => A.map((v, i) => Math.round(v + (B[i] - v) * t));
          fig.raster({ x: X, y: Y, nx: 110, ny: 110, value: (x, y) => (R.inside(x, y) ? cu([x, y]) : NaN),
            stats: vals => { const fin = vals.filter(Number.isFinite); return { m: Math.max(1e-12, ...fin.map(Math.abs)) }; },
            color: (v, T, st) => (Number.isFinite(v) ? [...mix(T.rgb('panel'), T.rgb(v < 0 ? 'c1' : 'c2'), 0.15 + 0.6 * Math.abs(v) / st.m), 255] : null) });
          fig.curve([...R.poly, R.poly[0]], { color: 'ink', width: 2 });
          const P = t => [callP(gamma, t)].flat().map(Number), Fv = p => [at(F, p)].flat().map(Number);
          const big = Math.max(1e-12, ...Array.from({ length: 24 }, (_, k) => Math.hypot(...Fv(P(a + (b - a) * k / 24))))), L = 0.12 * Math.max(x1 - x0, y1 - y0);
          for (let k = 0; k < 24; k++) { const p = P(a + (b - a) * k / 24), v = Fv(p); fig.arrow(p[0], p[1], p[0] + v[0] / big * L, p[1] + v[1] / big * L, { color: 'c4', width: 1.5 }); }
          // The area, ∫∫ curl F and ∫∫ div F in one pass over the grid.
          let area = 0, cint = 0, dint = 0;
          { const m = 180, [[gx0, gx1], [gy0, gy1]] = R.box, hx = (gx1 - gx0) / m, hy = (gy1 - gy0) / m;
            for (let i = 0; i < m; i++) for (let j = 0; j < m; j++) { const q = [gx0 + (i + 0.5) * hx, gy0 + (j + 0.5) * hy]; if (!R.inside(q[0], q[1])) continue; const J = jac(F, q); area += hx * hy; cint += (J[1][0] - J[0][1]) * hx * hy; dint += (J[0][0] + J[1][1]) * hx * hy; } }
          const circ = lineIntegral(F, gamma, a, b), fl = flux(F, gamma, [a, b]);
          ctx.legend([{ label: 'curl F < 0', color: 'c1' }, { label: 'curl F > 0', color: 'c2' }, { label: 'F on the boundary', color: 'c4' }]);
          ctx.table(['', 'over the region', 'along the boundary'], [
            ['Green: curl F  vs  ∮ F · ds', short(cint), short(circ)],
            ['Gauss: div F  vs  flux out', short(dint), short(fl)],
          ], `The region has area ≈ ${short(area)}; its integrals come from a grid (an estimate).`);
        },
      },
    },
    notation: `
# A rectangle's volume is the product of its side lengths (Definition 11.1).
# examples: Q in {Cuboid([0, 1], [0, 2]), Cuboid([-1, 1], [-1, 1], [0, 3])}
def volume_of(Q) := vol(Q)

# The step integrals bracket the integral: ∫φ ≤ ∫f ≤ ∫ψ (Definition 11.6).
lemma step_integrals_bracket: forall f in {(x, y) => x^2 + y^2, (x, y) => sin(x)*y, (x, y) => exp(-x*y)}, n in {1, 3, 8}: lower_step_integral(f, Cuboid([-1, 1], [0, 1]), n) <= integrate(f, Cuboid([-1, 1], [0, 1])) and integrate(f, Cuboid([-1, 1], [0, 1])) <= upper_step_integral(f, Cuboid([-1, 1], [0, 1]), n)

# Continuous functions are Riemann integrable on rectangles (Theorem 11.9).
lemma continuous_integrable_rect: forall f in {(x, y) => x^2 + y^2, (x, y) => sin(3*x)*cos(y), (x, y) => |x - y|}: integrable_rect(f, Cuboid([0, 1], [0, 1]))

# An unbounded function is not: near x = 0 every step function above 1/x must be huge.
conjecture all_integrable_rect: forall f in {(x, y) => x^2 + y^2, (x, y) => if x = 0 then 0 else 1/x}: integrable_rect(f, Cuboid([0, 1], [0, 1]))

# Fubini (Theorem 11.11): for continuous f the two iterated integrals agree, with the integral over the rectangle.
lemma fubini_continuous: forall f in {(x, y) => x^2 + y^2, (x, y) => x*exp(x*y), (x, y) => sin(x + 2*y)}: integrate(x => integrate(y => f(x, y), [0, 2]), [0, 1]) ~= integrate(y => integrate(x => f(x, y), [0, 1]), [0, 2])

# Without continuity the iterated integrals can differ: (x² − y²)/(x² + y²)² on [0, 1]² gives π/4 one way and −π/4 the other.
conjecture fubini_always: forall f in {(x, y) => x*y, (x, y) => if x = 0 and y = 0 then 0 else (x^2 - y^2)/(x^2 + y^2)^2}: integrate(x => integrate(y => f(x, y), [0, 1]), [0, 1]) ~= integrate(y => integrate(x => f(x, y), [0, 1]), [0, 1])

# The transformation formula (Theorem 11.21) for polar coordinates: ∫ over the unit disk = ∫∫ f(r cos φ, r sin φ)·r dr dφ.
lemma polar_coordinates: forall f in {p => 1, p => p[1]^2, p => exp(-(p[1]^2 + p[2]^2)), p => p[1] + 2*p[2]^2}: integral_between((x, y) => f((x, y)), -1, 1, x => -sqrt(1 - x^2), x => sqrt(1 - x^2)) ~= integrate((r, φ) => f((r*cos(φ), r*sin(φ))) * r, Cuboid([0, 1], [0, 2*pi]))

# Differentiating under the integral (Theorem 11.18).
lemma differentiate_under_integral: forall y in [0.5, 2]: deriv(t => integrate(x => cos(x*t), [0, 2]))(y) ~= integrate(x => -x*sin(x*y), [0, 2])

# The length of the unit circle and the area of the unit sphere, from the Gramian determinant (Example 12.9).
lemma circle_length: surface_integral(p => 1, t => (cos(t), sin(t)), [0, 2*pi]) ~= 2*pi
lemma sphere_area: surface_integral(p => 1, (u, v) => (sin(u)*cos(v), sin(u)*sin(v), cos(u)), Cuboid([0, pi], [0, 2*pi])) ~= 4*pi

# A line integral of a gradient depends only on the end points (Theorem 12.16).
lemma gradient_theorem: forall f in {p => p[1]^2*p[2], p => sin(p[1]) + p[2], p => exp(p[1]*p[2])}, γ in {t => (t, t^2), t => (cos(3*t), t*sin(t))}: line_integral(p => grad(f, p), γ, 0, 1) ~= f(γ(1)) - f(γ(0))

# Running along a curve backwards changes the sign of the line integral (Remark 12.13).
lemma reverse_orientation: forall F in {p => (-p[2], p[1]), p => (p[1]*p[2], p[1]^2)}: line_integral(F, t => (t, t^3), 0, 1) ~= -line_integral(F, t => (1 - t, (1 - t)^3), 0, 1)

# Green's theorem (12.17) on the unit disk: ∫∫ curl F = ∮ F · ds.
lemma green_disk: forall F in {p => (-p[2], p[1]), p => (p[1]*p[2], p[1]^2 + p[2]), p => (sin(p[2]), p[1]^3)}: integrate((r, φ) => curl(F, (r*cos(φ), r*sin(φ))) * r, Cuboid([0, 1], [0, 2*pi])) ~= line_integral(F, t => (cos(t), sin(t)), 0, 2*pi)

# Gauss's theorem (12.19) on the unit ball: ∫∫∫ div F = the flux out through the sphere.
lemma gauss_ball: forall F in {p => p, p => (p[1]^3, p[2], p[1]*p[3]), p => (p[2]*p[3], p[1]^2, p[3]^2)}: integrate((r, u, v) => div(F, (r*sin(u)*cos(v), r*sin(u)*sin(v), r*cos(u))) * r^2 * sin(u), Cuboid([0, 1], [0, pi], [0, 2*pi])) ~= flux(F, (u, v) => (sin(u)*cos(v), sin(u)*sin(v), cos(u)), Cuboid([0, pi], [0, 2*pi]))
`,
  });
});
