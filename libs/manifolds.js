MathVizLibrary(function manifolds(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const isVec = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');
  const short = x => fmt(+(+x).toPrecision(4));
  const pt = p => '(' + p.map(short).join(', ') + ')';

  /* ---------- small linear algebra ---------- */
  const dot = (a, b) => a.reduce((s, x, i) => s + x * b[i], 0);
  const norm = a => Math.sqrt(dot(a, a));
  const sub = (a, b) => a.map((x, i) => x - b[i]);
  const addv = (a, b) => a.map((x, i) => x + b[i]);
  const scale = (a, t) => a.map(x => x * t);
  // Solve A x = b by elimination with partial pivoting; null when A is (numerically) singular.
  function solve(A, b) {
    const n = A.length, M = A.map((r, i) => [...r, b[i]]);
    const big = Math.max(1e-300, ...A.flat().map(Math.abs));
    for (let c = 0; c < n; c++) {
      let piv = c;
      for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[piv][c])) piv = r;
      if (Math.abs(M[piv][c]) < 1e-12 * big) return null;
      [M[c], M[piv]] = [M[piv], M[c]];
      for (let r = 0; r < n; r++) if (r !== c) {
        const f = M[r][c] / M[c][c];
        for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
      }
    }
    return M.map((r, i) => r[n] / r[i]);
  }
  const det = A => {
    const n = A.length, M = A.map(r => r.slice());
    let d = 1;
    for (let c = 0; c < n; c++) {
      let piv = c;
      for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[piv][c])) piv = r;
      if (M[piv][c] === 0) return 0;
      if (piv !== c) { [M[c], M[piv]] = [M[piv], M[c]]; d = -d; }
      d *= M[c][c];
      for (let r = c + 1; r < n; r++) { const f = M[r][c] / M[c][c]; for (let k = c; k < n; k++) M[r][k] -= f * M[c][k]; }
    }
    return d;
  };
  // An orthonormal basis of the span of vs (Gram–Schmidt, dropping dependent vectors).
  const orth = vs => {
    const out = [];
    for (const v of vs) {
      let w = v.slice();
      for (const e of out) w = sub(w, scale(e, dot(w, e)));
      const l = norm(w);
      if (l > 1e-9 * Math.max(1, norm(v))) out.push(scale(w, 1 / l));
    }
    return out;
  };
  // An orthonormal basis of the orthogonal complement of span(vs) in ℝⁿ.
  const complement = (vs, n) => {
    const B = orth(vs), k = B.length;
    const all = orth([...B, ...Array.from({ length: n }, (_, i) => Array.from({ length: n }, (__, j) => (i === j ? 1 : 0)))]);
    return all.slice(k);
  };
  const subsets = (n, m) => {
    const out = [];
    const go = (s, from) => { if (s.length === m) { out.push(s); return; } for (let i = from; i < n; i++) go([...s, i], i + 1); };
    go([], 0);
    return out;
  };

  /* ---------- calling the user's functions ---------- */
  const atF = () => MathViz.shared.multivar.at;
  // A map of k numbers: f(t) for one, f(x, y) or f(p) for more; its value as a list of numbers.
  const callVec = (f, u) => {
    let v;
    if (u.length === 1 && (f.arity || f.length) <= 1) v = f(u[0]);
    else v = atF()(f, u);
    return Array.isArray(v) ? v.map(Number) : [Number(v)];
  };
  // The Jacobian of G: ℝᵈ → ℝᵐ at z, by central differences (m × d).
  const jac = (G, z) => {
    const cols = z.map((_, i) => {
      const h = 1e-6 * Math.max(1, Math.abs(z[i]));
      const a = z.slice(), b = z.slice();
      a[i] += h; b[i] -= h;
      return sub(G(a), G(b)).map(x => x / (2 * h));
    });
    return cols[0].map((_, r) => cols.map(c => c[r]));
  };
  // Solve G(z) = target (d equations, d unknowns) by damped Newton from z0; null if it fails.
  function newton(G, z0, target, iters = 50) {
    let z = z0.slice(), r = sub(G(z), target);
    for (let it = 0; it < iters; it++) {
      if (!r.every(Number.isFinite)) return null;
      const e = norm(r);
      if (e < 1e-13 * (1 + norm(target))) return z;
      const dz = solve(jac(G, z), r);
      if (!dz) return e < 1e-9 ? z : null;
      let t = 1, moved = false;
      for (let s = 0; s < 30; s++, t /= 2) {
        const zn = z.map((x, i) => x - t * dz[i]), rn = sub(G(zn), target);
        if (rn.every(Number.isFinite) && norm(rn) < e) { z = zn; r = rn; moved = true; break; }
      }
      if (!moved) break;
    }
    return norm(r) < 1e-9 * (1 + norm(target)) ? z : null;
  }
  // Least squares: the u minimising |G(u) − target| (more equations than unknowns), by Gauss–Newton.
  function closest(G, u0, target, iters = 60) {
    let u = u0.slice(), r = sub(G(u), target);
    for (let it = 0; it < iters; it++) {
      const J = jac(G, u), JT = J[0].map((_, c) => J.map(row => row[c]));
      const A = JT.map(a => JT.map(b => dot(a, b))), g = JT.map(a => dot(a, r));
      const du = solve(A, g);
      if (!du) break;
      let t = 1, moved = false;
      for (let s = 0; s < 30; s++, t /= 2) {
        const un = u.map((x, i) => x - t * du[i]), rn = sub(G(un), target);
        if (rn.every(Number.isFinite) && norm(rn) < norm(r) - 1e-16) { u = un; r = rn; moved = true; break; }
      }
      if (!moved || norm(du) < 1e-14) break;
    }
    return u;
  }
  const pick = (p, idx) => idx.map(i => p[i]);
  const compose = (n, free, dep, xf, y) => { const q = new Array(n); free.forEach((i, j) => { q[i] = xf[j]; }); dep.forEach((i, j) => { q[i] = y[j]; }); return q; };
  const names = n => (n <= 3 ? ['x', 'y', 'z'].slice(0, n) : Array.from({ length: n }, (_, i) => `x${i + 1}`));

  /* ---------- submanifolds ---------- */
  // edges of a parameter domain: an interval [a, b], a rectangle, or a list of [a, b].
  const edgesOf = W => {
    if (W && W.edges) return W.edges;
    if (isVec(W) && W.length === 2) return [W];
    if (Array.isArray(W) && W.every(e => isVec(e) && e.length === 2)) return W;
    const D = MathViz.toDomain(W), w = D.window && D.window();
    need(w, 'The parameters range over an interval [a, b] or a rectangle, such as Cuboid([0, 1], [0, 2]).');
    return Array.isArray(w[0]) ? w : [w];
  };

  function make(M) {
    const S = MathViz.space({
      kind: 'manifold', label: M.label, numeric: true,
      contains: p => isVec(p) && p.length === M.n && distance(M, p) <= 1e-7 * Math.max(1, norm(p)),
      sample: m => { MathViz.markInexact(); const P = points(M); return P.length <= m ? P.slice() : P.filter((_, i) => i % Math.ceil(P.length / m) === 0); },
      random: () => { const P = points(M); return P[Math.floor(Math.random() * P.length)]; },
      window: () => M.box,
      describe: () => M.label,
    });
    S.manifold = M;
    M.space = S;
    return S;
  }

  function zeroSet(F, n, box) {
    need(typeof F === 'function', 'zero_set(F): the points where F = 0, for F of (x, y), (x, y, z), … or of a point.');
    n = n || (F.arity || F.length);
    need(Number.isInteger(n) && n >= 2 && n <= 4, 'zero_set(F, n): say how many variables F has (2, 3 or 4), as in zero_set(p => p[1]^2 + p[2]^2 - 1, 2).');
    const r = typeof box === 'number' ? box : 2;
    const v0 = callVec(F, Array.from({ length: n }, (_, i) => 0.3 + 0.1 * i));
    const m = v0.length;
    need(m < n, `F gives ${m} numbers but has ${n} variables: a zero set needs fewer equations than variables.`);
    return make({ kind: 'equations', n, k: n - m, F, label: `{${F.label || 'F'} = 0}`, box: Array.from({ length: n }, () => [-r, r]) });
  }

  function parametrized(phi, W) {
    need(typeof phi === 'function', 'parametrized(φ, W): the image of φ on the parameter domain W.');
    const E = edgesOf(W), k = E.length;
    const mid = E.map(([a, b]) => (a + b) / 2);
    const n = callVec(phi, mid).length;
    need(n > k && n <= 4, `φ takes ${k} parameter${k === 1 ? '' : 's'} and gives points of ℝ^${n}: a parametrized submanifold needs fewer parameters than coordinates.`);
    const M = { kind: 'parametrization', n, k, phi, E, label: `${phi.label || 'φ'}(${E.map(([a, b]) => `[${fmt(a)}, ${fmt(b)}]`).join(' × ')})` };
    const P = gridPoints(M, 400);
    M.box = Array.from({ length: n }, (_, i) => { const xs = P.map(p => p[i]); const lo = Math.min(...xs), hi = Math.max(...xs), pad = 0.15 * Math.max(hi - lo, 0.5); return [lo - pad, hi + pad]; });
    return make(M);
  }

  function graphManifold(g, W) {
    need(typeof g === 'function', 'graph_manifold(g, W): the graph {(x, g(x))} of g over W.');
    const E = W ? edgesOf(W) : [[-1.5, 1.5]];
    let k = E.length;
    if (!W && (g.arity || g.length) > 1) k = g.arity || g.length;
    const EE = W ? E : Array.from({ length: k }, () => [-1.5, 1.5]);
    const m = callVec(g, EE.map(([a, b]) => (a + b) / 2)).length;
    const n = k + m;
    need(n <= 4, 'graph_manifold works for graphs in ℝ², ℝ³ and ℝ⁴.');
    const M = { kind: 'graph', n, k, g, E: EE, label: `graph(${g.label || 'g'})` };
    const P = gridPoints(M, 400);
    M.box = Array.from({ length: n }, (_, i) => { const xs = P.map(p => p[i]).filter(Number.isFinite); const lo = Math.min(...xs), hi = Math.max(...xs), pad = 0.15 * Math.max(hi - lo, 0.5); return [lo - pad, hi + pad]; });
    return make(M);
  }

  // Points of M spread over a grid of its parameters (parametrizations and graphs).
  function gridPoints(M, count) {
    const k = M.k, per = k === 1 ? count : Math.max(4, Math.round(Math.sqrt(count)));
    const out = [];
    const go = (j, u) => {
      if (j === k) {
        try { const p = M.kind === 'graph' ? [...u, ...callVec(M.g, u)] : callVec(M.phi, u); if (p.every(Number.isFinite)) out.push(p); } catch (e) { /* outside the domain */ }
        return;
      }
      const [a, b] = M.E[j];
      for (let i = 0; i < per; i++) go(j + 1, [...u, a + (b - a) * (i + 0.5) / per]);
    };
    go(0, []);
    return out;
  }

  // Points of M: a grid of parameters, or for a zero set random points pulled onto it.
  function points(M) {
    if (M.pts) return M.pts;
    if (M.kind !== 'equations') return (M.pts = gridPoints(M, M.k === 1 ? 400 : 900));
    let seed = 12345;
    const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
    const pts = [];
    const want = M.k === 1 ? 300 : 900;
    for (let t = 0; t < want * 4 && pts.length < want; t++) {
      const q = project(M, M.box.map(([a, b]) => a + (b - a) * rnd()));
      if (q && q.every((x, i) => x >= M.box[i][0] && x <= M.box[i][1])) pts.push(q);
    }
    // A curve of the plane: in order around its centre, so a slider moves along it.
    if (M.n === 2 && pts.length) {
      const c = [0, 1].map(i => pts.reduce((s, p) => s + p[i], 0) / pts.length);
      pts.sort((a, b) => Math.atan2(a[1] - c[1], a[0] - c[0]) - Math.atan2(b[1] - c[1], b[0] - c[0]));
    }
    return (M.pts = pts);
  }

  // The point of M nearest q, for q near M (null when the search fails).
  function project(M, q) {
    if (M.kind === 'equations') {
      let x = q.slice();
      for (let it = 0; it < 60; it++) {
        const F = callVec(M.F, x);
        if (!F.every(Number.isFinite)) return null;
        if (norm(F) < 1e-13) return x;
        const J = jac(p => callVec(M.F, p), x);
        const A = J.map(a => J.map(b => dot(a, b)));
        const y = solve(A, F);
        if (!y) return null;
        const step = J[0].map((_, c) => J.reduce((s, row, i) => s + row[c] * y[i], 0));
        x = sub(x, step);
        if (norm(step) > 1e3) return null;
      }
      return norm(callVec(M.F, x)) < 1e-9 ? x : null;
    }
    if (M.kind === 'graph') return [...pick(q, range(M.k)), ...callVec(M.g, pick(q, range(M.k)))];
    const u = paramOf(M, q);
    return u ? callVec(M.phi, u) : null;
  }
  const range = k => Array.from({ length: k }, (_, i) => i);
  // The parameters u with φ(u) nearest q: the nearest grid point, then Gauss–Newton.
  function paramOf(M, q) {
    const per = M.k === 1 ? 200 : 30;
    let best = null, bd = Infinity;
    const go = (j, u) => {
      if (j === M.k) { try { const d = norm(sub(callVec(M.phi, u), q)); if (d < bd) { bd = d; best = u; } } catch (e) { /* skip */ } return; }
      const [a, b] = M.E[j];
      for (let i = 0; i <= per; i++) go(j + 1, [...u, a + (b - a) * i / per]);
    };
    go(0, []);
    if (!best) return null;
    return closest(u => callVec(M.phi, u), best, q);
  }
  function distance(M, q) {
    MathViz.markInexact();
    if (M.kind === 'equations') { const p = project(M, q); return p ? norm(sub(p, q)) : Infinity; }
    const p = project(M, q);
    return p ? norm(sub(p, q)) : Infinity;
  }

  /* Every local description of M near a point p of it: a parametrization u ↦ param(u) with
     param(0) = p, local equations eq(q) = 0, a graph over k of the coordinates, and a straightening
     Φ with Φ(p) = 0 and Φ(M) ⊂ ℝᵏ × {0}; with the tangent and normal spaces. Each is built from the
     description M was given by, as in the proof that the descriptions are equivalent. */
  function local(M, p0) {
    const n = M.n, k = M.k, m = n - k;
    const L = { n, k, how: {} };
    if (M.kind === 'equations') {
      const p = project(M, p0);
      need(p, 'No point of the zero set near ' + pt(p0) + '.');
      const Fv = q => callVec(M.F, q);
      const J = jac(Fv, p);
      // The m columns with the largest minor: the implicit function theorem solves for those.
      let dep = null, bd = 0;
      for (const S of subsets(n, m)) { const d = Math.abs(det(J.map(r => pick(r, S)))); if (d > bd) { bd = d; dep = S; } }
      L.rank = orth(J).length;
      need(dep && L.rank === m, `DF(${pt(p)}) has rank ${L.rank} < ${m}: 0 isn't a regular value here, and the zero set may not be a submanifold near this point.`);
      const free = range(n).filter(i => !dep.includes(i)), pf = pick(p, free), pd = pick(p, dep);
      const solveDep = (xf, target) => newton(y => Fv(compose(n, free, dep, xf, y)), pd, target);
      const zero = new Array(m).fill(0);
      Object.assign(L, {
        p, free, dep, N: orth(J), T: complement(J, n),
        g: xf => solveDep(xf, zero),
        eq: Fv,
        param: u => { const xf = addv(pf, u), y = solveDep(xf, zero); return y ? compose(n, free, dep, xf, y) : null; },
        straight: q => [...sub(pick(q, free), pf), ...Fv(q)],
        straightInv: z => { const xf = addv(pf, z.slice(0, k)), y = solveDep(xf, z.slice(k)); return y ? compose(n, free, dep, xf, y) : null; },
      });
      const nm = names(n);
      L.how = {
        eq: `M is given by ${m === 1 ? 'the equation' : 'the equations'} F = 0, and DF(p) has rank ${m}.`,
        graph: `∂F/∂(${pick(nm, dep).join(', ')}) is invertible at p, so the implicit function theorem solves F = 0 for ${pick(nm, dep).join(', ')} as a function g of ${pick(nm, free).join(', ')} near p.`,
        param: `The graph gives the parametrization u ↦ (${pick(nm, free).join(', ')} = p + u, g(p + u)).`,
        straight: `Φ(q) = (${pick(nm, free).map(x => x + ' − p').join(', ')}, F(q)): DΦ(p) is invertible, and Φ sends M to the plane where the last ${m} coordinates are 0.`,
      };
      return L;
    }
    if (M.kind === 'graph') {
      const xf0 = pick(p0, range(k)), gv = x => callVec(M.g, x), p = [...xf0, ...gv(xf0)];
      const free = range(k), dep = range(m).map(i => k + i);
      const D = jac(u => [...addv(xf0, u), ...gv(addv(xf0, u))], new Array(k).fill(0));
      const cols = D[0].map((_, c) => D.map(r => r[c]));
      Object.assign(L, {
        p, free, dep, rank: k, T: orth(cols), N: complement(cols, n),
        g: gv,
        eq: q => sub(pick(q, dep), gv(pick(q, free))),
        param: u => { const x = addv(xf0, u); return [...x, ...gv(x)]; },
        straight: q => [...sub(pick(q, free), xf0), ...sub(pick(q, dep), gv(pick(q, free)))],
        straightInv: z => { const x = addv(xf0, z.slice(0, k)); return [...x, ...addv(gv(x), z.slice(k))]; },
      });
      const nm = names(n);
      L.how = {
        graph: `M is the graph of g: ${pick(nm, dep).join(', ')} = g(${pick(nm, free).join(', ')}).`,
        param: `u ↦ (p + u, g(p + u)) parametrizes it.`,
        eq: `It is the zero set of ${pick(nm, dep).join(', ')} − g(${pick(nm, free).join(', ')}), whose derivative has rank ${m}.`,
        straight: `Φ(x, y) = (x − p, y − g(x)) shears the graph flat.`,
      };
      return L;
    }
    // A parametrization φ: start from the parameters u₀ of the point.
    const u0 = paramOf(M, p0);
    need(u0, 'No point of the parametrized set near ' + pt(p0) + '.');
    const phiv = u => callVec(M.phi, u), p = phiv(u0);
    const D = jac(phiv, u0), cols = D[0].map((_, c) => D.map(r => r[c]));
    L.rank = orth(cols).length;
    need(L.rank === k, `Dφ(${pt(u0)}) has rank ${L.rank} < ${k}: φ isn't an immersion here, and its image may not be a submanifold near ${pt(p)}.`);
    const T = orth(cols), N = complement(cols, n);
    // Ψ(u, w) = φ(u₀ + u) + Σ wⱼ Nⱼ is a local diffeomorphism (inverse function theorem): Φ = Ψ⁻¹.
    const Psi = z => { let q = phiv(addv(u0, z.slice(0, k))); N.forEach((v, j) => { q = addv(q, scale(v, z[k + j])); }); return q; };
    let free = null, bd = 0;
    for (const S of subsets(n, k)) { const d = Math.abs(det(pick(D, S))); if (d > bd) { bd = d; free = S; } }
    const dep = range(n).filter(i => !free.includes(i));
    const zeroN = new Array(n).fill(0);
    Object.assign(L, {
      p, u0, free, dep, T, N,
      g: xf => { const u = newton(v => pick(phiv(addv(u0, v)), free), new Array(k).fill(0), xf); return u ? pick(phiv(addv(u0, u)), dep) : null; },
      param: u => phiv(addv(u0, u)),
      straightInv: Psi,
      straight: q => newton(Psi, zeroN, q),
      eq: q => { const z = newton(Psi, zeroN, q); return z ? z.slice(k) : new Array(m).fill(NaN); },
    });
    const nm = names(n);
    L.how = {
      param: `M is the image of φ, and Dφ(u₀) has rank ${k}.`,
      straight: `Ψ(u, w) = φ(u₀ + u) + w·N (N spanning the normal space at p) has DΨ invertible, so by the inverse function theorem Φ = Ψ⁻¹ is a change of coordinates near p, and Φ(M) lies in the plane w = 0.`,
      eq: `The last ${m} coordinates w of Φ = Ψ⁻¹ are local equations: near p, M = {w(q) = 0}.`,
      graph: `∂(φ_${pick(nm, free).join(', φ_')})/∂u is invertible at u₀, so ${pick(nm, free).join(', ')} can be taken as parameters: M is the graph of ${pick(nm, dep).join(', ')} over them.`,
    };
    return L;
  }

  // The four ways of saying "q lies on M", each from its own local description near q.
  const tolFor = q => 1e-6 * Math.max(1, norm(q));
  const near = (M, q) => { const p = project(M, q); need(p, `${pt(q)} is too far from M for a local description.`); return local(M, p); };
  const onParam = (M, q) => { MathViz.markInexact(); const L = near(M, q); const u = closest(L.param, new Array(L.k).fill(0), q); return norm(sub(L.param(u), q)) <= tolFor(q); };
  const onEquations = (M, q) => { MathViz.markInexact(); const L = near(M, q); const e = L.eq(q); return e.every(Number.isFinite) && norm(e) <= tolFor(q); };
  const onGraph = (M, q) => { MathViz.markInexact(); const L = near(M, q); const y = L.g(pick(q, L.free)); return !!y && norm(sub(pick(q, L.dep), y)) <= tolFor(q); };
  const onStraight = (M, q) => { MathViz.markInexact(); const L = near(M, q); const z = L.straight(q); return !!z && norm(z.slice(L.k)) <= tolFor(q); };

  const asM = v => { need(v && v.manifold, 'Expected a submanifold: zero_set(F), parametrized(φ, W) or graph_manifold(g).'); return v.manifold; };
  const onPoint = (M, q) => { need(isVec(q) && q.length === M.n, `Expected a point of ℝ^${M.n}.`); return q; };

  // Points near M: on it, and pushed off it along a normal.
  function Around(Ms, eps = 0.1) {
    const M = asM(Ms);
    const P = points(M);
    const list = [];
    const every = Math.max(1, Math.floor(P.length / 6));
    for (let i = 0; i < P.length && list.length < 12; i += every) {
      list.push(P[i]);
      try { const L = local(M, P[i]); list.push(addv(P[i], scale(L.N[0], eps * (list.length % 4 === 1 ? 1 : -0.5)))); } catch (e) { /* singular */ }
    }
    return MathViz.finite(list, { label: `points near ${M.label}` });
  }

  /* ---------- Lagrange multipliers ---------- */
  // Critical points of f on M: where ∇f(p) is normal to M, found by minimising |proj_T ∇f|² from many starts.
  function constrainedCritical(f, Ms) {
    const M = asM(Ms);
    MathViz.markInexact();
    const mv = MathViz.shared.multivar;
    const P = points(M), out = [];
    const fv = q => Number(atF()(f, q));
    const starts = P.filter((_, i) => i % Math.max(1, Math.floor(P.length / 40)) === 0);
    for (const s of starts) {
      let L;
      try { L = local(M, s); } catch (e) { continue; }
      // minimise or maximise f along the local parametrization: zero of the gradient of f∘param.
      const h = u => { const q = L.param(u); return q ? jac(v => [fv(L.param(v))], u)[0] : new Array(L.k).fill(NaN); };
      const u = newton(h, new Array(L.k).fill(0), new Array(L.k).fill(0), 30);
      if (!u || norm(u) > 0.8) continue;
      const q = L.param(u);
      if (!q || !q.every(Number.isFinite)) continue;
      if (out.some(o => norm(sub(o.p, q)) < 1e-4)) continue;
      const Lq = local(M, q);
      const gr = mv.grad(f, q);
      // λ: ∇f = Σ λⱼ nⱼ in the normal basis (for a zero set, ∇f = Σ λⱼ ∇Fⱼ).
      const lambda = M.kind === 'equations' ? (() => { const J = jac(v => callVec(M.F, v), q); const A = J.map(a => J.map(b => dot(a, b))); return solve(A, J.map(r => dot(r, gr))) || []; })() : Lq.N.map(v => dot(v, gr));
      // max, min or saddle along M: the second derivative of f∘param at 0.
      const H = jac(v => jac(w => [fv(Lq.param(w))], v)[0], new Array(Lq.k).fill(0));
      const ev = Lq.k === 1 ? [H[0][0]] : (() => { const a = H[0][0], b = (H[0][1] + H[1][0]) / 2, c = H[1][1], tr = a + c, dd = Math.sqrt(Math.max(0, (a - c) ** 2 / 4 + b * b)); return [tr / 2 - dd, tr / 2 + dd]; })();
      const kind = ev.every(x => x > 1e-6) ? 'local min' : ev.every(x => x < -1e-6) ? 'local max' : ev.some(x => x > 1e-6) && ev.some(x => x < -1e-6) ? 'saddle' : 'undecided';
      out.push({ p: q, value: fv(q), lambda, kind });
    }
    out.sort((a, b) => a.value - b.value);
    return out;
  }

  /* ---------- drawing ---------- */
  const COLORS = { M: 'c1', local: 'c2', normal: 'c3', faint: 'ink' };
  // The base point: sliders along M (s in [0, 1] for each parameter, or along the points of a zero set).
  function basePoint(ctx, M) {
    if (M.kind === 'equations') {
      const P = points(M);
      need(P.length, `No points of ${M.label} in the box ${M.box.map(([a, b]) => `[${fmt(a)}, ${fmt(b)}]`).join(' × ')}.`);
      const s = ctx.param('point', { min: 0, max: 1, step: 0.002, value: 0.13 });
      return P[Math.min(P.length - 1, Math.round(s * (P.length - 1)))];
    }
    const u = M.E.map(([a, b], i) => { const s = ctx.param(M.k === 1 ? 'point' : `point ${i + 1}`, { min: 0, max: 1, step: 0.002, value: i ? 0.4 : 0.13 }); return a + (b - a) * (0.02 + 0.96 * s); });
    return M.kind === 'graph' ? [...u, ...callVec(M.g, u)] : callVec(M.phi, u);
  }
  const span = M => Math.max(...M.box.map(([a, b]) => b - a));
  const curve2 = M => (M.kind === 'equations' ? null : gridPoints(M, 600));

  // The whole of M, faintly: a curve of the plane, or a cloud in space.
  function drawM(fig, M, three, st = {}) {
    if (!three) {
      if (M.kind === 'equations') fig.curve(M.contour || (M.contour = contour(q => callVec(M.F, q)[0], M.box[0], M.box[1], 240)), { color: st.color || COLORS.M, width: st.width || 1.5, alpha: st.alpha ?? 0.45 });
      else fig.curve(curve2(M), { color: st.color || COLORS.M, width: st.width || 1.5, alpha: st.alpha ?? 0.45 });
    } else {
      const P = points(M);
      if (M.k === 1 && M.kind !== 'equations') fig.curve(P, { color: st.color || COLORS.M, width: 1.5, alpha: st.alpha ?? 0.5 });
      else fig.points(P, { color: st.color || COLORS.M, r: 1.4, alpha: st.alpha ?? 0.35 });
    }
  }
  // The curve f = 0 in a box of the plane by marching squares: segments, separated by nulls.
  function contour(f, [x0, x1], [y0, y1], n) {
    const v = [];
    for (let j = 0; j <= n; j++) {
      const row = [];
      for (let i = 0; i <= n; i++) { let z; try { z = f([x0 + (x1 - x0) * i / n, y0 + (y1 - y0) * j / n]); } catch (e) { z = NaN; } row.push(z); }
      v.push(row);
    }
    const X = i => x0 + (x1 - x0) * i / n, Y = j => y0 + (y1 - y0) * j / n;
    const out = [];
    for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) {
      const c = [[i, j], [i + 1, j], [i + 1, j + 1], [i, j + 1]], z = c.map(([a, b]) => v[b][a]);
      if (!z.every(Number.isFinite)) continue;
      const cross = [];
      for (let e = 0; e < 4; e++) {
        const a = e, b = (e + 1) % 4;
        if ((z[a] < 0) !== (z[b] < 0)) {
          const t = z[a] / (z[a] - z[b]);
          cross.push([X(c[a][0] + t * (c[b][0] - c[a][0])), Y(c[a][1] + t * (c[b][1] - c[a][1]))]);
        }
      }
      if (cross.length >= 2) out.push(cross[0], cross[1], null);
      if (cross.length === 4) out.push(cross[2], cross[3], null);
    }
    return out;
  }
  const figFor = (ctx, M, three) => (three ? ctx.figure3d({ equal: true, labels: names(M.n) }) : ctx.figure({ x: M.box[0], y: M.box[1], square: true, xlabel: 'x', ylabel: 'y' }));
  const span1 = (f, a, b, n = 80) => Array.from({ length: n + 1 }, (_, i) => f(a + (b - a) * i / n));
  const guard = (ctx, M) => { if (M.n > 3) { ctx.note(`M lies in ℝ^${M.n}; the pictures need ℝ² or ℝ³.`); return false; } return true; };
  const tryLocal = (ctx, M, p) => { try { return local(M, p); } catch (e) { ctx.status('fail', e.message); ctx.note(e.message, 'caveat'); return null; } };

  function renderParam(ctx, Ms) {
    const M = asM(Ms);
    if (!guard(ctx, M)) return;
    const p0 = basePoint(ctx, M), L = tryLocal(ctx, M, p0);
    if (!L) return;
    const three = M.n === 3, d = 0.35 * span(M) / 2, nm = names(M.n);
    if (L.k === 1) {
      const us = span1(u => u, -d, d, 120), img = us.map(u => L.param([u]));
      const row = ctx.row();
      const f1 = row.figure({ x: [-d, d], xlabel: 'u' });
      nm.forEach((x, i) => f1.curve(us.map((u, j) => (img[j] ? [u, img[j][i]] : null)), { color: ['c1', 'c2', 'c3'][i], width: 2 }));
      f1.points([[0, L.p[0]]], { color: 'ink', r: 3 });
      const f2 = figFor(row, M, three);
      drawM(f2, M, three, { alpha: 0.3 });
      const ticks = span1(u => L.param([u]), -d, d, 12).filter(Boolean);
      if (three) {
        f2.curve(img.filter(Boolean), { color: COLORS.local, width: 3 });
        f2.points(ticks, { color: COLORS.local, r: 3 });
        f2.arrow(L.p, addv(L.p, scale(L.T[0], d)), { color: 'ink', width: 2 });
        f2.points([L.p], { color: 'ink', r: 5 });
      } else {
        f2.curve(img.filter(Boolean), { color: COLORS.local, width: 3 });
        f2.points(ticks, { color: COLORS.local, r: 3 });
        f2.arrow(L.p[0], L.p[1], L.p[0] + d * L.T[0][0], L.p[1] + d * L.T[0][1], { color: 'ink', width: 2 });
        f2.points([L.p], { color: 'ink', r: 4 });
      }
      row.legend(nm.map((x, i) => ({ label: `${x}(u)`, color: ['c1', 'c2', 'c3'][i] })).concat([{ label: 'u ↦ point of M, for |u| ≤ ' + short(d), color: COLORS.local }, { label: 'tangent vector', color: 'ink' }]));
    } else {
      const fig = ctx.figure3d({ equal: true, labels: nm });
      drawM(fig, M, true, { alpha: 0.25 });
      fig.surface((a, b) => L.param([a, b]), { u: [-d, d], v: [-d, d], n: 18, alpha: 0.75 });
      L.T.forEach(t => fig.arrow(L.p, addv(L.p, scale(t, d)), { color: 'ink', width: 2 }));
      fig.points([L.p], { color: 'ink', r: 5 });
      ctx.legend([{ label: 'the patch u ↦ point of M, |uᵢ| ≤ ' + short(d), color: 'c1' }, { label: 'tangent vectors (span T_pM)', color: 'ink' }]);
    }
    ctx.note(`p = ${pt(L.p)}. ${L.how.param} The tangent space T_pM is the image of the derivative of the parametrization at 0.`);
  }

  function renderEquations(ctx, Ms) {
    const M = asM(Ms);
    if (!guard(ctx, M)) return;
    const p0 = basePoint(ctx, M), L = tryLocal(ctx, M, p0);
    if (!L) return;
    const three = M.n === 3, d = 0.4 * span(M) / 2;
    if (!three) {
      const box = [[L.p[0] - d, L.p[0] + d], [L.p[1] - d, L.p[1] + d]];
      const fig = ctx.figure({ x: box[0], y: box[1], square: true, xlabel: 'x', ylabel: 'y' });
      fig.raster({ x: box[0], y: box[1], nx: 120, ny: 120, smooth: false, value: (x, y) => { const e = L.eq([x, y]); return e && Number.isFinite(e[0]) ? Math.sign(e[0]) : NaN; }, color: (v, th) => (v > 0 ? th.rgba('c2', 0.18) : v < 0 ? th.rgba('c3', 0.18) : null) });
      drawM(fig, M, false, { alpha: 0.9, width: 2.5 });
      const gr = L.N[0];
      fig.arrow(L.p[0], L.p[1], L.p[0] + 0.5 * d * gr[0], L.p[1] + 0.5 * d * gr[1], { color: 'ink', width: 2 });
      fig.points([L.p], { color: 'ink', r: 4 });
      ctx.legend([{ label: 'G > 0', color: 'c2' }, { label: 'G < 0', color: 'c3' }, { label: 'M = {G = 0}', color: 'c1' }, { label: 'normal (∇G direction)', color: 'ink' }]);
    } else {
      const fig = ctx.figure3d({ equal: true, labels: names(3) });
      // M and two neighbouring level sets of the local equations, as layers.
      const h = 0.25 * d;
      const layer = (c, color, alpha) => {
        if (L.k === 2) fig.surface((a, b) => { const z = [a, b, c]; return L.straightInv(z); }, { u: [-d, d], v: [-d, d], n: 14, alpha, color });
        else for (const [a, b] of [[c, 0], [0, c]]) fig.curve(span1(t => L.straightInv([t, a, b]), -d, d, 60).filter(Boolean), { color, width: 2, alpha });
      };
      drawM(fig, M, true, { alpha: 0.2 });
      layer(h, 'c2', 0.35); layer(0, 'c1', 0.85); layer(-h, 'c3', 0.35);
      L.N.forEach(v => fig.arrow(L.p, addv(L.p, scale(v, 0.6 * d)), { color: 'ink', width: 2 }));
      fig.points([L.p], { color: 'ink', r: 5 });
      ctx.legend([{ label: 'M: G = 0', color: 'c1' }, { label: `G = ${short(h)}`, color: 'c2' }, { label: `G = −${short(h)}`, color: 'c3' }, { label: 'normal space N_pM', color: 'ink' }]);
    }
    ctx.note(`p = ${pt(L.p)}. ${L.how.eq} The tangent space is the kernel of the derivative of the equations, and the normal space is spanned by their gradients.`);
  }

  function renderGraph(ctx, Ms, at0) {
    const M = asM(Ms);
    if (!guard(ctx, M)) return;
    const p0 = at0 || basePoint(ctx, M), L = tryLocal(ctx, M, p0);
    if (!L) return;
    const three = M.n === 3, d = 0.3 * span(M) / 2, nm = names(M.n);
    const fname = pick(nm, L.free).join(', '), dname = pick(nm, L.dep).join(', ');
    if (L.k === 1) {
      const xf0 = L.p[L.free[0]];
      const xs = span1(x => x, xf0 - d, xf0 + d, 120), ys = xs.map(x => L.g([x]));
      const row = ctx.row();
      const f1 = figFor(row, M, three);
      drawM(f1, M, three, { alpha: 0.3 });
      const pts = xs.map((x, i) => (ys[i] ? compose(M.n, L.free, L.dep, [x], ys[i]) : null));
      if (three) { f1.curve(pts.filter(Boolean), { color: COLORS.local, width: 3 }); f1.points([L.p], { color: 'ink', r: 5 }); }
      else {
        f1.curve(pts, { color: COLORS.local, width: 3 });
        // The axis the graph sits over, and a few vertical (or horizontal) lines meeting M once.
        const ax = L.free[0];
        for (let i = 0; i <= 6; i++) {
          const q = pts[Math.round(i * 20)];
          if (!q) continue;
          if (ax === 0) f1.seg(q[0], M.box[1][0], q[0], q[1], { color: 'faint', dash: [3, 3] });
          else f1.seg(M.box[0][0], q[1], q[0], q[1], { color: 'faint', dash: [3, 3] });
        }
        f1.points([L.p], { color: 'ink', r: 4 });
      }
      const f2 = row.figure({ x: [xf0 - d, xf0 + d], xlabel: fname, ylabel: dname });
      if (L.dep.length === 1) f2.curve(xs.map((x, i) => (ys[i] ? [x, ys[i][0]] : null)), { color: COLORS.local, width: 2.5 });
      else L.dep.forEach((_, j) => f2.curve(xs.map((x, i) => (ys[i] ? [x, ys[i][j]] : null)), { color: ['c2', 'c3'][j], width: 2.5 }));
      f2.points([[xf0, L.p[L.dep[0]]]], { color: 'ink', r: 4 });
      row.legend([{ label: `${dname} = g(${fname}) near p`, color: COLORS.local }]);
    } else {
      const fig = ctx.figure3d({ equal: true, labels: nm });
      drawM(fig, M, true, { alpha: 0.2 });
      const c = pick(L.p, L.free);
      fig.surface((a, b) => { const y = L.g([c[0] + a, c[1] + b]); return y ? compose(3, L.free, L.dep, [c[0] + a, c[1] + b], y) : null; }, { u: [-d, d], v: [-d, d], n: 18, alpha: 0.8 });
      fig.points([L.p], { color: 'ink', r: 5 });
      ctx.legend([{ label: `${dname} = g(${fname}) near p`, color: 'c1' }]);
    }
    ctx.note(`p = ${pt(L.p)}. ${L.how.graph} Over the ${fname}-${L.k === 1 ? 'axis' : 'plane'}, each nearby ${L.k === 1 ? 'line' : 'line'} parallel to the ${dname}-axis meets M near p exactly once.`);
  }

  function renderStraight(ctx, Ms) {
    const M = asM(Ms);
    if (!guard(ctx, M)) return;
    const p0 = basePoint(ctx, M), L = tryLocal(ctx, M, p0);
    if (!L) return;
    const three = M.n === 3, d = 0.3 * span(M) / 2;
    if (!three) {
      const row = ctx.row();
      const left = row.figure({ x: [L.p[0] - 1.6 * d, L.p[0] + 1.6 * d], y: [L.p[1] - 1.6 * d, L.p[1] + 1.6 * d], square: true, xlabel: 'x', ylabel: 'y' });
      const right = row.figure({ x: [-1.2 * d, 1.2 * d], y: [-1.2 * d, 1.2 * d], square: true, xlabel: 'z₁', ylabel: 'z₂' });
      drawM(left, M, false, { alpha: 0.25 });
      const K = 8;
      for (let i = -K; i <= K; i++) {
        const c = d * i / K, onM = i === 0;
        const st = { color: onM ? COLORS.M : 'c2', width: onM ? 3 : 1, alpha: onM ? 1 : 0.45 };
        // z₂ = c (parallel to M) and z₁ = c (across it), pulled back by Φ⁻¹.
        left.curve(span1(t => L.straightInv([t, c]), -d, d, 60), st);
        left.curve(span1(t => L.straightInv([c, t]), -d, d, 60), { color: 'c3', width: 1, alpha: 0.45 });
        right.seg(-d, c, d, c, st);
        right.seg(c, -d, c, d, { color: 'c3', width: 1, alpha: 0.45 });
      }
      left.points([L.p], { color: 'ink', r: 4 });
      right.points([[0, 0]], { color: 'ink', r: 4 });
      row.legend([{ label: 'M, and Φ(M) = the z₁-axis', color: COLORS.M }, { label: 'z₂ = const', color: 'c2' }, { label: 'z₁ = const', color: 'c3' }]);
    } else {
      const fig = ctx.figure3d({ equal: true, labels: names(3) });
      drawM(fig, M, true, { alpha: 0.15 });
      const h = 0.35 * d;
      if (L.k === 2) for (const c of [-h, 0, h]) fig.surface((a, b) => L.straightInv([a, b, c]), { u: [-d, d], v: [-d, d], n: 12, alpha: c === 0 ? 0.85 : 0.3 });
      else for (const a of [-h, 0, h]) for (const b of [-h, 0, h]) fig.curve(span1(t => L.straightInv([t, a, b]), -d, d, 50).filter(Boolean), { color: a === 0 && b === 0 ? 'c1' : 'c3', width: a === 0 && b === 0 ? 3 : 1, alpha: a === 0 && b === 0 ? 1 : 0.5 });
      fig.points([L.p], { color: 'ink', r: 5 });
      ctx.legend([{ label: 'Φ⁻¹ of the coordinate planes: M is the one with the normal coordinates 0', color: 'c1' }]);
    }
    ctx.note(`p = ${pt(L.p)}. ${L.how.straight}${three ? ' The layers are Φ⁻¹ of parallel coordinate planes; M is the middle one.' : ' The curved grid is Φ⁻¹ of the straight one: Φ straightens M without tearing the neighbourhood.'}`);
  }

  MathViz.represent({ name: 'parametrization', label: 'A parametrization: the image of a map', doc: 'Near each point, M is the image of an injective map u ↦ φ(u) whose derivative has full rank (an immersion). Drag the point along M.', test: v => !!(v && v.manifold), render: renderParam });
  MathViz.represent({ name: 'local_equations', label: 'Solutions of local equations', doc: 'Near each point, M is the set where some functions G₁, …, G_{n−k} vanish, with linearly independent gradients (0 a regular value).', test: v => !!(v && v.manifold), render: renderEquations });
  MathViz.represent({ name: 'local_graph', label: 'Locally the graph of a function', doc: 'Near each point, M is the graph of a smooth function of k of the coordinates (by the implicit function theorem).', test: v => !!(v && v.manifold), render: renderGraph });
  MathViz.represent({ name: 'straightening', label: 'A local straightening', doc: 'Near each point there is a change of coordinates Φ (a diffeomorphism) taking M to a flat piece ℝᵏ × {0}.', test: v => !!(v && v.manifold), render: renderStraight });

  /* ---------- views ---------- */
  function lagrangeView(ctx, f, Ms) {
    const M = asM(Ms);
    const crit = constrainedCritical(f, Ms), fv = q => Number(atF()(f, q));
    if (M.n === 2) {
      const [xr, yr] = M.box;
      const fig = ctx.figure({ x: xr, y: yr, square: true, xlabel: 'x', ylabel: 'y' });
      const vals = fig.raster({ x: xr, y: yr, nx: 200, ny: 200, smooth: true, value: (x, y) => fv([x, y]), color: () => null });
      const fin = vals.filter(Number.isFinite), lo = Math.min(...fin), hi = Math.max(...fin), st = (hi - lo) / 16 || 1;
      fig.raster({ x: xr, y: yr, nx: 200, ny: 200, smooth: false, value: (x, y) => Math.floor(fv([x, y]) / st), color: (v, th) => (Number.isFinite(v) ? th.rgba(v % 2 ? 'c2' : 'c3', 0.1) : null) });
      drawM(fig, M, false, { alpha: 0.95, width: 2.5 });
      const mv = MathViz.shared.multivar, L = 0.12 * span(M);
      for (const c of crit) {
        const g = mv.grad(f, c.p), gl = norm(g) || 1;
        fig.arrow(c.p[0], c.p[1], c.p[0] + L * g[0] / gl, c.p[1] + L * g[1] / gl, { color: 'ink', width: 2 });
        fig.points([c.p], { color: c.kind === 'local max' ? 'c2' : c.kind === 'local min' ? 'c3' : 'ink', r: 5 });
      }
      ctx.legend([{ label: 'bands of f (level curves at their edges)', color: 'c2' }, { label: 'M', color: 'c1' }, { label: '∇f at the critical points: normal to M', color: 'ink' }]);
    } else if (M.n === 3) {
      const fig = ctx.figure3d({ equal: true, labels: names(3) });
      drawM(fig, M, true, { alpha: 0.3 });
      for (const c of crit) fig.points([c.p], { color: c.kind === 'local max' ? 'c2' : c.kind === 'local min' ? 'c3' : 'ink', r: 6 });
    }
    if (!crit.length) { ctx.status('info', 'No critical points of f on M found'); return; }
    ctx.table(['point p', 'f(p)', 'λ', 'along M'], crit.map(c => [pt(c.p), short(c.value), c.lambda.map(short).join(', '), c.kind]));
    const mx = crit.reduce((a, b) => (b.value > a.value ? b : a)), mn = crit[0];
    ctx.note(`At each point, ∇f(p) = λ·∇F(p) (the Lagrange multiplier rule): the gradient of f is normal to M, so f has no first-order change along M. Largest value found: ${short(mx.value)} at ${pt(mx.p)}; smallest: ${short(mn.value)} at ${pt(mn.p)}.`);
  }

  function implicitView(ctx, F, p) {
    need(typeof F === 'function' && isVec(p), 'implicit_function(F, p): F of (x, y) (or (x, y, z)) and a point p with F(p) = c.');
    const c = callVec(F, p)[0];
    const G = Object.assign((...a) => callVec(F, a.length === 1 && Array.isArray(a[0]) ? a[0] : a)[0] - c, { arity: p.length, label: F.label });
    const Ms = zeroSet(G, p.length);
    const J = jac(q => callVec(F, q), p)[0];
    if (Math.abs(J[J.length - 1]) < 1e-9) ctx.status('fail', `∂F/∂${names(p.length)[p.length - 1]}(p) = 0: the theorem doesn't apply in the last variable here.`);
    renderGraph(ctx, Ms, p);
    if (p.length === 2) ctx.note(`Slope of the graph at p: g′ = −F_x/F_y = ${short(-J[0] / J[1])}.`);
  }

  function inverseView(ctx, f, p) {
    need(typeof f === 'function' && isVec(p) && p.length === 2, 'inverse_function(f, p): f of (x, y) giving points of the plane, and a point p.');
    const fv = q => callVec(f, q);
    const r = ctx.param('r', { min: 0.02, max: 1.5, step: 0.01, value: 0.4 });
    const q0 = fv(p), D = jac(fv, p), dt = det(D);
    const row = ctx.row();
    const left = row.figure({ x: [p[0] - 1.2 * r, p[0] + 1.2 * r], y: [p[1] - 1.2 * r, p[1] + 1.2 * r], square: true, xlabel: 'x', ylabel: 'y' });
    const right = row.figure({ square: true, xlabel: 'f₁', ylabel: 'f₂' });
    const K = 8;
    for (let i = -K; i <= K; i++) {
      const c = r * i / K;
      const h = span1(t => [p[0] + t, p[1] + c], -r, r, 50), v = span1(t => [p[0] + c, p[1] + t], -r, r, 50);
      left.curve(h, { color: 'c1', width: 1 }); left.curve(v, { color: 'c2', width: 1 });
      right.curve(h.map(fv), { color: 'c1', width: 1 }); right.curve(v.map(fv), { color: 'c2', width: 1 });
      const lin = q => addv(q0, [dot(D[0], sub(q, p)), dot(D[1], sub(q, p))]);
      if (i % 4 === 0) { right.curve(h.map(lin), { color: 'ink', width: 1, dash: [4, 3], alpha: 0.6 }); right.curve(v.map(lin), { color: 'ink', width: 1, dash: [4, 3], alpha: 0.6 }); }
    }
    left.points([p], { color: 'ink', r: 4 }); right.points([q0], { color: 'ink', r: 4 });
    row.legend([{ label: 'grid near p', color: 'c1' }, { label: 'its image under f', color: 'c2' }, { label: 'image under the linearization', color: 'ink' }]);
    if (Math.abs(dt) < 1e-9) ctx.status('fail', 'det Df(p) = 0: the inverse function theorem says nothing here, and f may fold the neighbourhood over.');
    else ctx.status('ok', `det Df(p) = ${short(dt)} ≠ 0: f is invertible near p`);
    ctx.note(`Df(p) = [[${D[0].map(short).join(', ')}], [${D[1].map(short).join(', ')}]]. When det Df(p) ≠ 0, f maps a neighbourhood of p one-to-one onto a neighbourhood of f(p), with a differentiable inverse whose derivative is Df(p)⁻¹. Shrink r: the image grid looks more and more like the image of the linearization.`);
  }

  MathViz.define({
    name: 'manifolds',
    requires: ['multivar', 'linalg'],
    description: 'Submanifolds of ℝⁿ given by a parametrization, by equations, or as a graph, and every other description computed from the given one: local parametrizations, local equations, local graphs (the implicit function theorem) and local straightenings (the inverse function theorem); tangent and normal spaces, points near a submanifold, Lagrange multipliers, and views of the implicit and inverse function theorems. interpret M shows all four descriptions.',
    functions: {
      zero_set: { doc: 'zero_set(F): the submanifold {F = 0} for F of (x, y), (x, y, z), … giving one number or several (one per equation); zero_set(F, n) when F takes a point of ℝⁿ. It is a set: p in M, forall p in M: …', fn: (F, n, r) => zeroSet(F, n, r) },
      parametrized: { doc: 'parametrized(φ, W): the image of φ on W, an interval [a, b] for a curve or a rectangle Cuboid([a, b], [c, d]) for a surface. A set, like zero_set.', fn: parametrized },
      graph_manifold: { doc: 'graph_manifold(g): the graph {(x, g(x))} of g (of one or two variables) over [−1.5, 1.5]ᵏ; graph_manifold(g, W) over W.', fn: graphManifold },
      dim: { doc: 'dim(M): the dimension k of the submanifold M.', fn: Ms => asM(Ms).k },
      codim: { doc: 'codim(M): n − k, the number of local equations needed.', fn: Ms => asM(Ms).n - asM(Ms).k },
      tangent_space: { doc: 'tangent_space(M, p): an orthonormal basis of T_pM, as a list of k vectors.', fn: (Ms, p) => { MathViz.markInexact(); return local(asM(Ms), onPoint(asM(Ms), p)).T; } },
      normal_space: { doc: 'normal_space(M, p): an orthonormal basis of the normal space N_pM, as a list of n − k vectors.', fn: (Ms, p) => { MathViz.markInexact(); return local(asM(Ms), onPoint(asM(Ms), p)).N; } },
      nearest_point: { doc: 'nearest_point(M, q): the point of M nearest q (for q near M).', fn: (Ms, q) => { MathViz.markInexact(); return project(asM(Ms), onPoint(asM(Ms), q)); } },
      distance_to: { doc: 'distance_to(M, q): the distance from q to M (for q near M).', fn: (Ms, q) => distance(asM(Ms), onPoint(asM(Ms), q)) },
      on_by_parametrization: { doc: 'on_by_parametrization(M, q): q is a value of a local parametrization of M near q.', fn: (Ms, q) => onParam(asM(Ms), onPoint(asM(Ms), q)) },
      on_by_equations: { doc: 'on_by_equations(M, q): q solves the local equations of M near q.', fn: (Ms, q) => onEquations(asM(Ms), onPoint(asM(Ms), q)) },
      on_by_graph: { doc: 'on_by_graph(M, q): q lies on the local graph of M near q.', fn: (Ms, q) => onGraph(asM(Ms), onPoint(asM(Ms), q)) },
      on_by_straightening: { doc: 'on_by_straightening(M, q): a local straightening Φ of M sends q into ℝᵏ × {0}.', fn: (Ms, q) => onStraight(asM(Ms), onPoint(asM(Ms), q)) },
      constrained_critical: { doc: 'constrained_critical(f, M): the critical points of f on M (where ∇f is normal to M), as records with the point, f there, the multipliers λ and whether it is a local max, min or saddle along M.', fn: (f, Ms) => constrainedCritical(f, Ms).map(c => MathViz.record({ p: c.p, value: c.value, lambda: c.lambda, kind: c.kind })) },
      constrained_max: { doc: 'constrained_max(f, M): the largest value of f at its critical points on M (the maximum of f on M when M is compact).', fn: (f, Ms) => Math.max(...constrainedCritical(f, Ms).map(c => c.value)) },
      constrained_min: { doc: 'constrained_min(f, M): the smallest value of f at its critical points on M.', fn: (f, Ms) => Math.min(...constrainedCritical(f, Ms).map(c => c.value)) },
    },
    spaces: {
      Manifolds: { doc: 'Manifolds: example submanifolds, each given in one of the three ways: the unit circle (an equation), a parabola (a graph), an ellipse (a parametrization), the unit sphere, a saddle surface, a helix and a torus.', fn: () => catalog() },
      Around: { doc: 'Around(M, ε): some points of M and some pushed off it along a normal by about ε, to try statements about points near M.', fn: Around },
    },
    views: {
      lagrange: { doc: 'lagrange(f, M) draws f by its level bands with the submanifold M and marks the critical points of f on M, where ∇f is normal to M (Lagrange multipliers), with a table of the points, the values of f, the multipliers and whether f has a max or min along M there.', render: lagrangeView },
      implicit_function: { doc: 'implicit_function(F, p) draws the level set F = F(p) near p as the graph of a function of the other variables (the implicit function theorem), with the function itself beside it.', render: implicitView },
      inverse_function: { doc: 'inverse_function(f, p) draws a grid around p and its image under f: f maps it one-to-one when det Df(p) ≠ 0 (the inverse function theorem), and the image looks like that of the linearization as the grid shrinks (drag r).', render: inverseView },
      manifold: { doc: 'manifold(M) shows the four descriptions of M one after another: a parametrization, local equations, a local graph and a straightening, each computed near the point you drag, the four equivalent descriptions of a submanifold.', render(ctx, Ms) { renderParam(ctx, Ms); renderEquations(ctx, Ms); renderGraph(ctx, Ms); renderStraight(ctx, Ms); } },
    },
    notation: `
# A point lies on a submanifold, said four ways: each uses one local description of M near the point (a set is a submanifold when, near each of its points, any one of these exists, and then all of them do).
# examples: M in Manifolds, q in Around(M)
concept on_manifold(M, q) where
  parametrization: on_by_parametrization(M, q)
  equations: on_by_equations(M, q)
  graph: on_by_graph(M, q)
  straightening: on_by_straightening(M, q)

# The tangent space is orthogonal to the normal space.
lemma tangent_perp_normal: forall M in Manifolds: forall p in M: forall t in tangent_space(M, p): forall v in normal_space(M, p): |dot(t, v)| < 1e-6

# The dimensions add up: dim T_pM + dim N_pM = n.
lemma tangent_normal_dimensions: forall M in Manifolds: forall p in M: len(tangent_space(M, p)) + len(normal_space(M, p)) = len(p)
`,
  });

  let CAT = null;
  function catalog() {
    if (CAT) return CAT;
    const fn = (f, label, arity) => Object.assign(f, { label, arity });
    const list = [
      zeroSet(fn((x, y) => x * x + y * y - 1, 'x² + y² − 1', 2), 2),
      graphManifold(fn(x => x * x, 'x ↦ x²', 1)),
      parametrized(fn(t => [2 * Math.cos(t), Math.sin(t)], 't ↦ (2 cos t, sin t)', 1), [0, 2 * Math.PI]),
      zeroSet(fn((x, y, z) => x * x + y * y + z * z - 1, 'x² + y² + z² − 1', 3), 3),
      graphManifold(fn((x, y) => x * x - y * y, '(x, y) ↦ x² − y²', 2), [[-1, 1], [-1, 1]]),
      parametrized(fn(t => [Math.cos(t), Math.sin(t), t / 4], 't ↦ (cos t, sin t, t/4)', 1), [0, 4 * Math.PI]),
      parametrized(fn((u, v) => [(1 + 0.4 * Math.cos(v)) * Math.cos(u), (1 + 0.4 * Math.cos(v)) * Math.sin(u), 0.4 * Math.sin(v)], 'torus', 2), [[0, 2 * Math.PI], [0, 2 * Math.PI]]),
    ];
    const labels = ['the unit circle {x² + y² = 1}', 'the parabola, graph of x²', 'the ellipse t ↦ (2 cos t, sin t)', 'the unit sphere {x² + y² + z² = 1}', 'the saddle, graph of x² − y²', 'the helix t ↦ (cos t, sin t, t/4)', 'the torus'];
    list.forEach((S, i) => { S.label = labels[i]; S.manifold.label = labels[i]; });
    return (CAT = MathViz.finite(list, { label: 'example submanifolds' }));
  }
});
