MathVizLibrary(function multivar(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const isVec = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');
  const named = (f, label, meta = {}) => Object.assign(f, { label }, meta);
  // Functions of several variables take a point: f(p), or f(x, y) when written with two parameters.
  const at = (f, p) => {
    need(typeof f === 'function', 'Expected a function of a point.');
    return (f.arity || f.length) > 1 && p.length === (f.arity || f.length) ? f(...p) : f(p);
  };
  const add = (p, i, h) => { const q = p.slice(); q[i] += h; return q; };
  const step = (p, i) => 1e-5 * Math.max(1, Math.abs(p[i]));
  const pdiff = (f, p, i) => {
    need(isVec(p), 'Derivatives are taken at a point, such as (0.5, 1).');
    need(Number.isInteger(i) && i >= 1 && i <= p.length, `The variable index goes from 1 to ${p.length}.`);
    MathViz.markInexact();
    const h = step(p, i - 1);
    return (at(f, add(p, i - 1, h)) - at(f, add(p, i - 1, -h))) / (2 * h);
  };
  // The exact ∂f/∂xᵢ at p when f is a formula (see partial below), else null.
  const exactAt = (f, p, i) => { const g = partial(f, i); return g.__symbolic ? at(Object.assign((...a) => g(...a), { arity: f.arity || f.length }), p) : null; };
  const grad = (f, p) => {
    need(isVec(p), 'grad(f, p) needs a point p.');
    const ex = p.map((_, i) => exactAt(f, p, i + 1));
    if (ex.every(v => typeof v === 'number')) return ex;
    return p.map((_, i) => pdiff(f, p, i + 1));
  };
  const jacobian = (F, p) => {
    need(isVec(p), 'jacobian(F, p) needs a point p.');
    const ex = p.map((_, i) => exactAt(F, p, i + 1));
    if (ex.every(c => typeof c === 'number' || isVec(c))) return Array.isArray(ex[0]) ? ex[0].map((_, r) => ex.map(c => c[r])) : [ex];
    MathViz.markInexact();
    const cols = p.map((_, i) => {
      const h = step(p, i), a = at(F, add(p, i, h)), b = at(F, add(p, i, -h));
      return Array.isArray(a) ? a.map((x, k) => (x - b[k]) / (2 * h)) : [(a - b) / (2 * h)];
    });
    return cols[0].map((_, r) => cols.map(c => c[r]));
  };
  // ∂/∂x_j (∂f/∂x_i): the inner derivative with a much smaller step than the outer one, so the
  // order matters as it should (for xy(x² − y²)/(x² + y²) at 0 the two orders differ).
  const mixed = (f, p, i, j) => {
    need(isVec(p) && Number.isInteger(i) && Number.isInteger(j), 'mixed_partial(f, p, i, j) needs a point and two variable indices.');
    const g = partial(f, i);
    if (g.__symbolic) { const v = exactAt(Object.assign(g, { arity: f.arity || f.length }), p, j); if (typeof v === 'number') return v; }
    MathViz.markInexact();
    const H = 1e-3 * Math.max(1, Math.abs(p[j - 1]));
    const inner = q => { const h = 1e-7 * Math.max(1, Math.abs(q[i - 1])) * 1e-1; return (at(f, add(q, i - 1, h)) - at(f, add(q, i - 1, -h))) / (2 * h); };
    return (inner(add(p, j - 1, H)) - inner(add(p, j - 1, -H))) / (2 * H);
  };
  // Diagonal entries by the second difference (more accurate); off-diagonal ones keep their order.
  const second = (f, p, i) => {
    MathViz.markInexact();
    const h = 1e-4 * Math.max(1, Math.abs(p[i]));
    return (at(f, add(p, i, h)) - 2 * at(f, p) + at(f, add(p, i, -h))) / (h * h);
  };
  const hessian = (f, p) => {
    need(isVec(p), 'hessian(f, p) needs a point p.');
    const ex = p.map((_, i) => p.map((__, j) => { const g = partial(f, i + 1); return g.__symbolic ? exactAt(Object.assign(g, { arity: f.arity || f.length }), p, j + 1) : null; }));
    if (ex.every(r => r.every(v => typeof v === 'number'))) return ex;
    return p.map((_, i) => p.map((__, j) => (i === j ? second(f, p, i) : mixed(f, p, i + 1, j + 1))));
  };
  const directional = (f, p, v) => {
    need(isVec(p) && isVec(v) && v.length === p.length, 'directional(f, p, v) needs a point and a direction of the same length.');
    MathViz.markInexact();
    const h = 1e-6, L = Math.hypot(...v), u = v.map(x => x / L);
    return (at(f, p.map((x, k) => x + h * u[k])) - at(f, p.map((x, k) => x - h * u[k]))) / (2 * h);
  };
  // The derivative of F at p along v, not normalised: d/dt F(p + tv) at t = 0. F may be vector-valued.
  const ddir = (F, p, v) => {
    need(isVec(p) && isVec(v) && v.length === p.length, 'ddir(F, p, v) needs a point and a direction of the same length.');
    // From the exact partial derivatives when F is a formula: Σ vₖ ∂F/∂xₖ(p).
    const ex = p.map((_, k) => exactAt(F, p, k + 1));
    if (ex.every(c => typeof c === 'number')) return ex.reduce((s, c, k) => s + c * v[k], 0);
    if (ex.every(isVec)) return ex[0].map((_, r) => ex.reduce((s, c, k) => s + c[r] * v[k], 0));
    MathViz.markInexact();
    const h = 1e-6 / Math.max(1, Math.hypot(...v));
    const a = at(F, p.map((x, k) => x + h * v[k])), b = at(F, p.map((x, k) => x - h * v[k]));
    return Array.isArray(a) ? a.map((x, k) => (x - b[k]) / (2 * h)) : (a - b) / (2 * h);
  };

  /* ---------- exact partial derivatives ---------- */
  // For a function given by a formula, ∂f/∂xᵢ is a formula too: differentiated symbolically, so
  // exact algebra can prove identities about it. Anything else is differentiated numerically.
  const NUM = v => ({ type: 'num', v });
  const isNum = n => n && n.type === 'num';
  function fold(n) {
    if (!n || typeof n !== 'object') return n;
    if (n.type === 'bin' && ['+', '-', '*', '/', '^'].includes(n.op)) {
      const a = fold(n.a), b = fold(n.b), A = isNum(a) ? a.v : null, B = isNum(b) ? b.v : null;
      if (A !== null && B !== null && n.op !== '/' && n.op !== '^') return NUM(n.op === '+' ? A + B : n.op === '-' ? A - B : A * B);
      switch (n.op) {
        case '+': if (A === 0) return b; if (B === 0) return a; break;
        case '-': if (B === 0) return a; if (A === 0) return { type: 'un', op: 'neg', a: b }; break;
        case '*': if (A === 0 || B === 0) return NUM(0); if (A === 1) return b; if (B === 1) return a; break;
        case '/': if (A === 0) return NUM(0); if (B === 1) return a; break;
        case '^': if (B === 1) return a; if (B === 0) return NUM(1); break;
      }
      return { ...n, a, b };
    }
    if (n.type === 'un' && n.op === 'neg') { const a = fold(n.a); return isNum(a) ? NUM(-a.v) : { ...n, a }; }
    if (n.type === 'call') return { ...n, args: n.args.map(fold) };
    if (n.type === 'if') return { ...n, a: fold(n.a), b: fold(n.b) };
    if (n.type === 'abs') return { ...n, e: fold(n.e) };
    if (n.type === 'tuple' || n.type === 'list') return { ...n, items: n.items.map(fold) };
    return n;
  }
  // Rewrite a formula: f(node) returns a replacement or null (keep going).
  const mapNode = (n, f) => {
    if (Array.isArray(n)) return n.map(x => mapNode(x, f));
    if (!n || typeof n !== 'object' || n.type === 'value') return n;
    const r = f(n);
    if (r) return r;
    const o = {};
    for (const k of Object.keys(n)) o[k] = n[k] && typeof n[k] === 'object' ? mapNode(n[k], f) : n[k];
    return o;
  };
  // p[k] ↔ a name of its own, so a formula of a point is differentiated coordinate by coordinate.
  const coordName = (p, k) => `__${p}_${k}`;
  const toIds = (body, p) => mapNode(body, n => {
    if (n.type === 'index' && n.obj.type === 'id' && n.obj.name === p && n.args.length === 1 && isNum(n.args[0]) && Number.isInteger(n.args[0].v)) return { type: 'id', name: coordName(p, n.args[0].v) };
    if (n.type === 'un' && n.op === 'sqrt') return { type: 'call', f: { type: 'id', name: 'sqrt' }, args: [n.a] };
    return null;
  });
  const fromIds = (body, p) => mapNode(body, n => {
    const m = n.type === 'id' && new RegExp(`^__${p}_(\\d+)$`).exec(n.name);
    return m ? { type: 'index', obj: { type: 'id', name: p }, args: [NUM(+m[1])] } : null;
  });
  const usesWhole = (node, p) => { let hit = false; mapNode(node, n => { if (n.type === 'id' && n.name === p) hit = true; return null; }); return hit; };
  const SUB = '₀₁₂₃₄₅₆₇₈₉';
  const PARTIALS = new WeakMap(), DERIVS = new WeakMap();
  function partial(f, i) {
    need(typeof f === 'function', 'partial(f, i) differentiates a function f along its i-th variable.');
    need(Number.isInteger(i) && i >= 1, 'partial(f, i): i is the number of the variable, from 1.');
    let memo = PARTIALS.get(f);
    if (!memo) PARTIALS.set(f, memo = new Map());
    if (memo.has(i)) return memo.get(i);
    const label = `∂${String(i).split('').map(c => SUB[c]).join('')}(${fmt(f)})`;
    let out = null;
    const F = MathViz.formula(f), A = MathViz.asym();
    // The derivative depends only on the formula, so it is kept with the formula: a lambda written
    // inside a claim is a new function at every sample, but its formula is the same.
    const derive = () => {
      if (!F || !A || !A.d) return null;
      let hit = false;
      mapNode(F.body, n => { if (n.type === 'if') hit = true; return null; });
      if (hit) return null;   // the branches' formulas say nothing about the derivative where they meet
      const dd = (node, x) => {
        if (node.type === 'tuple' || node.type === 'list') { const items = node.items.map(it => A.d(it, x)); return items.every(Boolean) ? { ...node, items } : null; }
        return A.d(node, x);
      };
      const ps = F.params;
      let body = null;
      if (ps.length > 1) {
        need(i <= ps.length, `${fmt(f)} has ${ps.length} variables.`);
        body = dd(toIds(F.body, '\u0000'), ps[i - 1]);
      } else if (ps.length === 1) {
        const t = toIds(F.body, ps[0]);
        let coords = false;
        mapNode(t, n => { if (n.type === 'id' && n.name.startsWith(coordName(ps[0], ''))) coords = true; return null; });
        if (!usesWhole(t, ps[0])) { body = dd(t, coordName(ps[0], i)); if (body) body = fromIds(body, ps[0]); }
        else if (i === 1 && !coords) body = dd(t, ps[0]);   // a function of one number
      }
      return body ? fold(body) : null;
    };
    if (F) {
      let byI = DERIVS.get(F.body);
      if (!byI) DERIVS.set(F.body, byI = new Map());
      if (!byI.has(i)) { let b = null; try { b = derive(); } catch (e) { if (e && e.message && /has \d+ variables/.test(e.message)) throw e; b = null; } byI.set(i, b); }
      const body = byI.get(i);
      if (body) { out = MathViz.fromFormula({ params: F.params, body, env: F.env }, label); out.__symbolic = true; }
    }
    if (!out) {
      out = (...args) => {
        if (args.length === 1 && typeof args[0] === 'number') {
          MathViz.markInexact();
          const x = args[0], h = 1e-5 * Math.max(1, Math.abs(x));
          return (f(x + h) - f(x - h)) / (2 * h);
        }
        return pdiff(f, args.length > 1 ? args : args[0], i);
      };
      out.label = label;
      out.arity = f.arity || f.length;
    }
    memo.set(i, out);
    return out;
  }

  // Do the partial derivatives exist at p? The difference quotient must settle from both sides.
  const partialsExist = (f, p) => p.every((_, i) => Number.isFinite(MathViz.limitAt(t => (t === 0 ? NaN : (at(f, add(p, i, t)) - at(f, p)) / t), 0)));

  /* ---------- Taylor polynomials, critical points, the Hessian test (chapter 9) ---------- */
  // Eigenvalues of a symmetric matrix by Jacobi rotations, largest first.
  function symEigs(S) {
    const n = S.length, a = S.map(r => r.slice());
    for (let sweep = 0; sweep < 60; sweep++) {
      let off = 0;
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) off += a[i][j] ** 2;
      if (off < 1e-30) break;
      for (let q = 0; q < n; q++) for (let r = q + 1; r < n; r++) {
        if (Math.abs(a[q][r]) < 1e-300) continue;
        const th = (a[r][r] - a[q][q]) / (2 * a[q][r]);
        const t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), sn = t * c;
        for (let k = 0; k < n; k++) { const x = a[k][q], y = a[k][r]; a[k][q] = c * x - sn * y; a[k][r] = sn * x + c * y; }
        for (let k = 0; k < n; k++) { const x = a[q][k], y = a[r][k]; a[q][k] = c * x - sn * y; a[r][k] = sn * x + c * y; }
      }
    }
    return a.map((r, i) => r[i]).sort((x, y) => y - x);
  }
  // Solve M x = b (Gaussian elimination with pivoting); null if M is singular.
  function solveLin(M, b) {
    const n = M.length, A = M.map((r, i) => [...r, b[i]]);
    for (let c = 0; c < n; c++) {
      let piv = c;
      for (let r = c + 1; r < n; r++) if (Math.abs(A[r][c]) > Math.abs(A[piv][c])) piv = r;
      if (Math.abs(A[piv][c]) < 1e-14) return null;
      [A[c], A[piv]] = [A[piv], A[c]];
      for (let r = 0; r < n; r++) if (r !== c) { const f = A[r][c] / A[c][c]; for (let k = c; k <= n; k++) A[r][k] -= f * A[c][k]; }
    }
    return A.map((r, i) => r[n] / r[i]);
  }
  const symHess = (f, q) => { const H = hessian(f, q); return H.map((r, i) => r.map((x, j) => (x + H[j][i]) / 2)); };

  // The Taylor polynomial of degree k ≤ 2 of f at p: f(p) + ∇f(p)·(x − p) + ½(x − p)ᵀH(p)(x − p)
  // (Definition 9.3 with Remark 9.4), with exact derivatives when f is a formula.
  function taylorPoly(f, p, k = 2) {
    need(typeof f === 'function' && isVec(p), 'taylor_poly(f, p, k) needs a function of a point, a point and a degree 0, 1 or 2.');
    need([0, 1, 2].includes(k), 'taylor_poly works up to degree 2 (k = 0, 1 or 2).');
    const f0 = +at(f, p), g = k >= 1 ? grad(f, p) : null, H = k >= 2 ? symHess(f, p) : null;
    const T = (...args) => {
      const x = args.length > 1 ? args : args[0];
      need(isVec(x) && x.length === p.length, `taylor_poly(f, p, k) is a function of a point with ${p.length} coordinates.`);
      const z = x.map((v, i) => v - p[i]);
      let v = f0;
      if (g) v += g.reduce((t, gi, i) => t + gi * z[i], 0);
      if (H) v += 0.5 * H.reduce((t, row, i) => t + z[i] * row.reduce((u, h, j) => u + h * z[j], 0), 0);
      return v;
    };
    T.label = `T${k}(${fmt(f)}, (${p.map(x => fmt(x)).join(', ')}))`;
    T.arity = 1;
    return T;
  }

  // Points of [−r, r]ⁿ where ∇f = 0 (Definition 9.11): Newton's method x ← x − H(x)⁻¹∇f(x) from a
  // grid of starting points; points found twice are kept once.
  function criticalPoints(f, r = 2, n = 2) {
    need(typeof f === 'function', 'critical_points(f, r, n) needs a function of a point.');
    MathViz.markInexact();
    const found = [], m = n === 1 ? 25 : n === 2 ? 9 : 4;
    const starts = [];
    const rec = (i, x) => { if (i === n) { starts.push(x); return; } for (let k = 0; k < m; k++) rec(i + 1, [...x, -r + 2 * r * (k + 0.5) / m]); };
    rec(0, []);
    for (let x of starts) {
      for (let it = 0; it < 60; it++) {
        const g = grad(f, x);
        if (!g.every(Number.isFinite)) break;
        if (Math.hypot(...g) < 1e-11) break;
        const d = solveLin(symHess(f, x), g);
        if (!d || !d.every(Number.isFinite)) break;
        x = x.map((v, i) => v - d[i]);
        if (x.some(v => Math.abs(v) > 2 * r)) break;
      }
      const g = grad(f, x);
      if (!g.every(Number.isFinite) || Math.hypot(...g) > 1e-7 || x.some(v => Math.abs(v) > r * (1 + 1e-9))) continue;
      const clean = x.map(v => { const q = Math.round(v * 1e9) / 1e9; return Math.abs(q - v) < 1e-9 ? (Object.is(q, -0) ? 0 : q) : v; });
      if (!found.some(y => Math.hypot(...y.map((v, i) => v - clean[i])) < 1e-6)) found.push(clean);
    }
    found.sort((a, b) => a[0] - b[0] || (a[1] || 0) - (b[1] || 0));
    return MathViz.finite(found);
  }
  // What the Hessian says at a point (Theorem 9.15).
  function hessianTest(f, p) {
    need(isVec(p), 'The Hessian test needs a point.');
    const g = grad(f, p), e = symEigs(symHess(f, p)), tol = 1e-7 * Math.max(1, ...e.map(Math.abs));
    if (Math.hypot(...g) > 1e-6) return { kind: 'not a critical point', e, g };
    if (e.every(x => x > tol)) return { kind: 'local minimum', e, g };
    if (e.every(x => x < -tol)) return { kind: 'local maximum', e, g };
    if (e.some(x => x > tol) && e.some(x => x < -tol)) return { kind: 'saddle point', e, g };
    return { kind: 'undecided (a zero eigenvalue: the Hessian test can\'t tell)', e, g };
  }

  /* ---------- level sets ---------- */
  // Points with f(p) = c in the box [−r, r]ⁿ: found by bisection along random segments, plus the
  // points of the set where |grad f| is smallest (where a level set can fail to be smooth).
  function LevelSet(f, c, r = 2, n = 2) {
    need(typeof f === 'function' && typeof c === 'number', 'LevelSet(f, c, r, n): the points of [−r, r]ⁿ where f = c.');
    let seed = 99;
    const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
    const g = p => at(f, p) - c;
    let pts = null;
    const find = () => {
      if (pts) return pts;
      pts = [];
      for (let t = 0; t < 4000 && pts.length < 600; t++) {
        const a = Array.from({ length: n }, () => (rnd() * 2 - 1) * r), b = Array.from({ length: n }, () => (rnd() * 2 - 1) * r);
        let ga = g(a), gb = g(b);
        if (!Number.isFinite(ga) || !Number.isFinite(gb) || ga * gb > 0) continue;
        let lo = a, hi = b;
        for (let k = 0; k < 60; k++) {
          const m = lo.map((x, i) => (x + hi[i]) / 2), gm = g(m);
          if (!Number.isFinite(gm)) break;
          if (gm * ga <= 0) { hi = m; gb = gm; } else { lo = m; ga = gm; }
        }
        pts.push(Math.abs(ga) < Math.abs(gb) ? lo : hi);
      }
      // Where on the set is the gradient smallest? Minimise (f − c)² + |grad f|² from a few starts.
      const obj = p => { const v = g(p), gr = p.map((_, i) => { const h = 1e-6; return (g(add(p, i, h)) - g(add(p, i, -h))) / (2 * h); }); return v * v + gr.reduce((s, x) => s + x * x, 0); };
      const crit = [];
      for (let s = 0; s < 8 && s < pts.length; s++) {
        let p = pts[Math.floor(s * pts.length / 8)].slice(), best = obj(p), scale = r / 4;
        for (let it = 0; it < 400 && scale > 1e-10; it++) {
          let moved = false;
          for (let i = 0; i < n; i++) for (const sg of [1, -1]) {
            const q = add(p, i, sg * scale), v = obj(q);
            if (v < best) { best = v; p = q; moved = true; }
          }
          if (!moved) scale /= 2;
        }
        if (Math.abs(g(p)) < 1e-8) crit.push(p);
      }
      pts = [...crit, ...pts];
      return pts;
    };
    return MathViz.space({
      kind: 'levelset', label: `{f = ${fmt(c)}}`, dim: n, numeric: true,
      contains: p => isVec(p) && p.length === n && Math.abs(g(p)) <= 1e-7 * Math.max(1, Math.abs(c)),
      sample: m => { MathViz.markInexact(); const P = find(); return P.length <= m ? P.slice() : P.slice(0, m); },
      random: () => { const P = find(); return P[Math.floor(rnd() * P.length)]; },
      window: () => Array.from({ length: n }, () => [-r, r]),
      describe: () => `the level set ${fmt(f)} = ${fmt(c)}`,
    });
  }

  /* ---------- example functions of two variables ---------- */
  let cat = {};
  const r2 = p => p[0] * p[0] + p[1] * p[1];
  const Functions2 = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (cat[key]) return cat[key];
    const list = [
      named(p => r2(p), 'x² + y²'),
      named(p => p[0] * p[1], 'xy'),
      named(p => p[0] * p[0] - p[1] * p[1], 'x² − y²'),
      named(p => (r2(p) === 0 ? 0 : p[0] * p[1] / r2(p)), 'xy/(x² + y²), 0 at 0'),
      named(p => (r2(p) === 0 ? 0 : p[0] * p[0] * p[1] / (p[0] ** 4 + p[1] * p[1])), 'x²y/(x⁴ + y²), 0 at 0'),
      named(p => (r2(p) === 0 ? 0 : p[0] * p[1] * (p[0] * p[0] - p[1] * p[1]) / r2(p)), 'xy(x² − y²)/(x² + y²), 0 at 0'),
      named(p => Math.abs(p[0]) + Math.abs(p[1]), '|x| + |y|'),
      named(p => Math.sqrt(Math.abs(p[0] * p[1])), '√|xy|'),
      named(p => Math.sin(p[0]) * Math.cos(p[1]), 'sin x · cos y'),
      named(p => p[0] ** 3 - 3 * p[0] * p[1] * p[1], 'x³ − 3xy² (monkey saddle)'),
      named(p => Math.exp(-r2(p)), 'e^(−x² − y²)'),
    ];
    if (key) list.push(
      named(p => (r2(p) === 0 ? 0 : r2(p) * Math.sin(1 / Math.sqrt(r2(p)))), '(x² + y²)·sin(1/√(x² + y²))'),
      named(p => (p[1] === p[0] * p[0] && p[0] !== 0 ? 1 : 0), '1 on the parabola y = x² (minus 0)'),
      named(p => Math.cbrt(p[0] ** 3 + p[1] ** 3), '∛(x³ + y³)'),
    );
    return (cat[key] = MathViz.finite(list, { label: 'example functions of (x, y)' }));
  };

  // For other libraries (multint): derivatives that are exact for formulas.
  MathViz.shared.multivar = { partial, grad, jacobian, hessian, at };

  /* ---------- ways of looking at a function of (x, y) (interpret) ---------- */
  const plane = v => {
    if (typeof v !== 'function' || v.domainCtor || v.__structure) return false;
    const ar = v.arity || v.length;
    if (ar > 2) return false;
    try { const y = at(v, [0.3, 0.7]); return typeof y === 'number' && (ar === 2 || (() => { try { return typeof v(0.5) !== 'number' || Number.isNaN(v(0.5)); } catch (e) { return true; } })()); } catch (e) { return false; }
  };
  const val = f => (x, y) => { try { const z = +at(f, [x, y]); return Number.isFinite(z) ? z : NaN; } catch (e) { return NaN; } };
  MathViz.represent({
    name: 'surface', label: 'Its graph: a surface over the plane', test: plane,
    doc: 'The set {(x, y, f(x, y))} in space. Drag to turn it.',
    render(ctx, f) {
      const g = val(f), fig = ctx.figure3d({ labels: ['x', 'y', 'f'], equal: false });
      fig.surface((x, y) => g(x, y), { u: [-2, 2], v: [-2, 2], n: 40 });
    },
  });
  MathViz.represent({
    name: 'level_curves', label: 'Its level curves: a contour map', test: plane,
    doc: 'The curves f = c for evenly spaced c, as on a map: close together where f changes fast.',
    render(ctx, f) {
      const g = val(f), fig = ctx.figure({ x: [-2, 2], y: [-2, 2], square: true });
      const vs = [];
      for (let i = 0; i <= 30; i++) for (let j = 0; j <= 30; j++) { const z = g(-2 + i * 4 / 30, -2 + j * 4 / 30); if (Number.isFinite(z)) vs.push(z); }
      vs.sort((a, b) => a - b);
      const lo = vs[Math.floor(vs.length * 0.02)] ?? 0, hi = vs[Math.floor(vs.length * 0.98)] ?? 1, st = (hi - lo) / 14 || 1;
      fig.raster({ x: [-2, 2], y: [-2, 2], nx: 220, ny: 220, smooth: false, value: (x, y) => Math.floor((g(x, y) - lo) / st), color: (v, th) => (Number.isFinite(v) ? th.rgba(v % 2 ? 'c1' : 'c2', 0.12 + 0.012 * Math.max(0, Math.min(14, v))) : null) });
      ctx.note(`Bands of height ${fmt(+st.toPrecision(3))} from ${fmt(+lo.toPrecision(3))} to ${fmt(+hi.toPrecision(3))}: each edge between bands is a level curve.`);
    },
  });
  MathViz.represent({
    name: 'gradient_field', label: 'Its gradient: a vector field', test: plane,
    doc: '∇f(x, y) points uphill, as steep as f rises, and crosses the level curves at right angles.',
    render(ctx, f) {
      const g = val(f), fig = ctx.figure({ x: [-2, 2], y: [-2, 2], square: true });
      const arrows = [];
      for (let i = 0; i <= 12; i++) for (let j = 0; j <= 12; j++) {
        const x = -1.9 + i * 3.8 / 12, y = -1.9 + j * 3.8 / 12, h = 1e-5;
        const v = [(g(x + h, y) - g(x - h, y)) / (2 * h), (g(x, y + h) - g(x, y - h)) / (2 * h)];
        if (v.every(Number.isFinite)) arrows.push([x, y, v]);
      }
      const m = Math.max(1e-12, ...arrows.map(([, , v]) => Math.hypot(...v)));
      for (const [x, y, v] of arrows) fig.arrow(x, y, x + 0.28 * v[0] / m, y + 0.28 * v[1] / m, { color: 'c2', width: 1.3 });
      ctx.note(`Arrows scaled so the longest is 0.28; |∇f| is at most about ${fmt(+m.toPrecision(3))} here.`);
    },
  });

  MathViz.define({
    name: 'multivar',
    requires: ['linalg', 'functions'],
    description: 'Several variables: partial and directional derivatives, gradients, Jacobians, Hessians and mixed partials, differentiability in ℝⁿ, level sets and regular values, example functions of (x, y) including the classic counterexamples, and views of gradients, linearizations and level surfaces.',
    functions: {
      pdiff: { doc: 'pdiff(f, p, i): the partial derivative of f along the i-th variable at the point p.', fn: pdiff },
      grad: { doc: 'grad(f, p): the gradient of f at p, the vector of its partial derivatives (exact when f is a formula).', fn: grad },
      jacobian: { doc: 'jacobian(F, p): the Jacobian matrix of F: ℝⁿ → ℝᵐ at p, its total derivative (rows: components of F; exact when F is a formula).', fn: jacobian },
      hessian: { doc: 'hessian(f, p): the matrix of second partial derivatives (row i, column j: first along i, then along j).', fn: hessian },
      mixed_partial: { doc: 'mixed_partial(f, p, i, j) = ∂/∂x_j (∂f/∂x_i) at p: first along i, then along j, with the inner derivative taken much more finely, so the order matters.', fn: mixed },
      directional: { doc: 'directional(f, p, v): the derivative of f at p in the direction of v.', fn: directional },
      taylor_poly: { doc: 'taylor_poly(f, p, k): the Taylor polynomial of degree k (0, 1 or 2) of f at the point p, as a function: f(p) + ∇f(p)·(x − p) + ½(x − p)ᵀH(p)(x − p) for k = 2 (Definition 9.3). Exact derivatives when f is a formula.', fn: taylorPoly },
      critical_points: { doc: 'critical_points(f, r, n): the points of [−r, r]ⁿ (r = 2, n = 2 if left out) where the gradient of f vanishes, found by Newton\'s method, as a finite set to quantify over.', fn: criticalPoints },
      hessian_test: { doc: 'hessian_test(f, p): what the Hessian test (Theorem 9.15) says at p: local minimum, local maximum, saddle point, undecided, or not a critical point.', fn: (f, p) => hessianTest(f, p).kind },
      min_by_hessian: { doc: 'min_by_hessian(f, p): p is a critical point and the Hessian there is positive definite, so p is a strict local minimum (Theorem 9.15).', fn: (f, p) => hessianTest(f, p).kind === 'local minimum' },
      max_by_hessian: { doc: 'max_by_hessian(f, p): p is a critical point with negative definite Hessian: a strict local maximum.', fn: (f, p) => hessianTest(f, p).kind === 'local maximum' },
      saddle_by_hessian: { doc: 'saddle_by_hessian(f, p): p is a critical point whose Hessian has eigenvalues of both signs: a saddle point.', fn: (f, p) => hessianTest(f, p).kind === 'saddle point' },
      partial: { doc: 'partial(f, i): the function ∂f/∂xᵢ. For a formula ((x, y) => …, or p => … in p[1], p[2], …) it is the exact derivative, so exact algebra can prove identities about it; otherwise it is computed numerically.', fn: partial },
      ddir: { doc: 'ddir(F, p, v): the directional derivative d/dt F(p + tv) at t = 0, for any v (not normalised) and F with values in ℝ or ℝᵐ. By Theorem 8.11 it is jacobian(F, p) · v.', fn: ddir },
      partials_exist: { doc: 'partials_exist(f, p): whether every partial derivative of f exists at p (its difference quotient settles from both sides).', fn: partialsExist },
    },
    spaces: {
      LevelSet: { doc: 'LevelSet(f, c, r, n): the points of [−r, r]ⁿ where f = c (n = 2 or 3), found numerically, including where the gradient is smallest.', fn: LevelSet },
      Functions2: { doc: 'Functions2: example functions of a point (x, y): smooth ones, saddles, and the classic counterexamples xy/(x² + y²), x²y/(x⁴ + y²), xy(x² − y²)/(x² + y²), √|xy|.', fn: Functions2 },
    },
    views: {
      extrema: {
        doc: 'extrema(f, r) colors f on [−r, r]² with its level curves and marks its critical points by what the Hessian says: local minima, local maxima, saddle points, and undecided ones (a zero eigenvalue), with a table of the eigenvalues (Theorem 9.15).',
        render(ctx, f, r = 2) {
          const P = criticalPoints(f, r, 2), pts = MathViz.elements(P) || [];
          const fig = ctx.figure({ x: [-r, r], y: [-r, r], square: true });
          const mix = (A, B, t) => A.map((v, i) => Math.round(v + (B[i] - v) * t));
          fig.raster({ x: [-r, r], y: [-r, r], nx: 220, ny: 220, value: (x, y) => { const v = at(f, [x, y]); return typeof v === 'number' ? v : NaN; },
            stats: vals => { let lo = Infinity, hi = -Infinity; for (const v of vals) if (Number.isFinite(v)) { lo = Math.min(lo, v); hi = Math.max(hi, v); } const st = (hi - lo || 1) / 16, edge = new Uint8Array(vals.length); for (let j = 0; j < 220; j++) for (let i = 0; i < 220; i++) { const k = j * 220 + i, l = Math.floor(vals[k] / st); if ((i < 219 && Math.floor(vals[k + 1] / st) !== l) || (j < 219 && Math.floor(vals[k + 220] / st) !== l)) edge[k] = 1; } return { lo, hi, edge }; },
            color: (v, T, st, k) => { if (!Number.isFinite(v)) return null; const b = mix(T.rgb('panel'), T.rgb('c1'), 0.08 + 0.45 * (v - st.lo) / ((st.hi - st.lo) || 1)); return st.edge[k] ? [...mix(b, T.rgb('ink'), 0.3), 255] : [...b, 255]; } });
          const COL = { 'local minimum': 'pos', 'local maximum': 'neg', 'saddle point': 'c3' };
          const rows = pts.map(q => {
            const t = hessianTest(f, q);
            fig.points([q], { color: COL[t.kind] || 'undef', r: 6 });
            return ['(' + q.map(x => fmt(+x.toPrecision(5))).join(', ') + ')', fmt(+(+at(f, q)).toPrecision(6)), t.e.map(x => fmt(+x.toPrecision(4))).join(', '), t.kind];
          });
          ctx.legend([{ label: 'local minimum', color: 'pos' }, { label: 'local maximum', color: 'neg' }, { label: 'saddle point', color: 'c3' }, { label: 'undecided', color: 'undef' }]);
          if (rows.length) ctx.table(['critical point', 'f', 'Hessian eigenvalues', 'Hessian test'], rows);
          ctx.note(rows.length ? `${rows.length} critical point${rows.length > 1 ? 's' : ''} in the square. Positive eigenvalues only: a strict local minimum; negative only: a strict local maximum; both signs: a saddle point; a zero eigenvalue: the test can't tell (x⁴ + y⁴ and x⁴ − y⁴ both have a zero Hessian at 0).` : 'No point of the square has ∇f = 0.');
        },
      },
      taylor_surface: {
        doc: 'taylor_surface(f, p) draws the graph of f near p with its Taylor polynomial of degree k (drag k from 0 to 2) and the radius. The note compares the largest error on the circle of that radius with radiusᵏ⁺¹: the ratio stays bounded as the radius shrinks (f − P = O(‖x − p‖ᵏ⁺¹), Remark 9.6).',
        render(ctx, f, p) {
          need(isVec(p) && p.length === 2, 'taylor_surface(f, p) needs a function of the plane and a point.');
          const k = Math.round(ctx.param('degree k', { min: 0, max: 2, step: 1, value: 2 }));
          const rad = ctx.param('radius', { min: 0.02, max: 2, step: 0.02, value: 1 });
          const T = taylorPoly(f, p, k);
          const fig = ctx.figure3d({ labels: ['x₁', 'x₂', 'f'], equal: false });
          fig.surface((u, v) => [u, v, at(f, [u, v])], { u: [p[0] - rad, p[0] + rad], v: [p[1] - rad, p[1] + rad], n: 26 });
          fig.surface((u, v) => [u, v, T([u, v])], { u: [p[0] - rad, p[0] + rad], v: [p[1] - rad, p[1] + rad], n: 14, color: 'c4', alpha: 0.45 });
          let worst = 0;
          for (let j = 0; j < 240; j++) { const a = 2 * Math.PI * j / 240, q = [p[0] + rad * Math.cos(a), p[1] + rad * Math.sin(a)]; worst = Math.max(worst, Math.abs(at(f, q) - T(q))); }
          ctx.legend([{ label: 'graph of f', color: 'c1' }, { label: `Taylor polynomial of degree ${k}`, color: 'c4' }]);
          ctx.note(`On the circle of radius ${fmt(rad)} the largest error is ${fmt(+worst.toPrecision(3))}, which is ${fmt(+(worst / rad ** (k + 1)).toPrecision(3))} × radius^${k + 1}. Shrink the radius: that factor stays bounded, because f − P = O(‖x − p‖^${k + 1}).`);
        },
      },
      approach: {
        doc: 'approach(f, p) runs into the point p of the plane along straight lines from four directions and along the parabolas y = x² and x = y², and plots f along each path against the distance to p. f is continuous at p only if every path (every sequence, Definition 6.9) gives f(p); x²y/(x⁴ + y²) agrees on every line and disagrees on the parabola.',
        render(ctx, f, p = [0, 0]) {
          need(typeof f === 'function' && isVec(p) && p.length === 2, 'approach(f, p) needs a function of the plane and a point, such as approach(p => p[1]*p[2]/(p[1]^2 + p[2]^2), (0, 0)).');
          const r = ctx.param('radius', { min: 0.01, max: 2, step: 0.01, value: 1 });
          const val = q => { try { return +at(f, q); } catch (e) { return NaN; } };
          const paths = [0, 1, 2, 3].map(k => {
            const a = Math.PI * k / 4;
            return { label: `line at ${k * 45}°`, go: t => [p[0] + t * Math.cos(a), p[1] + t * Math.sin(a)] };
          }).concat(
            { label: 'parabola y = x²', go: t => { const x = t / Math.sqrt(1 + t * t); return [p[0] + x, p[1] + x * x]; }, curved: true },
            { label: 'parabola x = y²', go: t => { const y = t / Math.sqrt(1 + t * t); return [p[0] + y * y, p[1] + y]; }, curved: true },
          );
          const colors = ['c1', 'c2', 'c3', 'c4', 'neg', 'c6'];
          const fp = val(p);
          // Left: the paths on the plane, over f's values.
          const fig = ctx.figure({ x: [p[0] - r, p[0] + r], y: [p[1] - r, p[1] + r], square: true });
          const mix = (A, B, t) => A.map((v, i) => Math.round(v + (B[i] - v) * t));
          fig.raster({ x: [p[0] - r, p[0] + r], y: [p[1] - r, p[1] + r], nx: 160, ny: 160, value: (x, y) => val([x, y]),
            stats: vals => { const fin = vals.filter(Number.isFinite); return { lo: Math.min(...fin), hi: Math.max(...fin) }; },
            color: (v, T, st) => (Number.isFinite(v) ? [...mix(T.rgb('panel'), T.rgb('muted'), 0.08 + 0.5 * (v - st.lo) / ((st.hi - st.lo) || 1)), 255] : null) });
          paths.forEach((P, i) => fig.curve(Array.from({ length: 80 }, (_, j) => P.go(r * (1 - j / 80))), { color: colors[i], width: P.curved ? 2.5 : 1.5, dash: P.curved ? [5, 3] : undefined }));
          fig.points([p], { color: 'ink', r: 4 });
          // Right: f along each path, against the distance travelled to p.
          const fig2 = ctx.figure({ x: [0, r], xlabel: 'distance t to p', ylabel: 'f along the path', height: 260 });
          const limits = paths.map((P, i) => {
            fig2.curve(Array.from({ length: 300 }, (_, j) => { const t = r * (j + 1) / 300; return [t, val(P.go(t))]; }), { color: colors[i], width: P.curved ? 2.5 : 1.5, dash: P.curved ? [5, 3] : undefined });
            return val(P.go(1e-9));
          });
          if (Number.isFinite(fp)) fig2.seg(0, fp, r, fp, { color: 'ink', width: 1, dash: [2, 3] });
          ctx.legend(paths.map((P, i) => ({ label: P.label, color: colors[i] })).concat([{ label: 'f(p)', color: 'ink' }]));
          const fin = limits.filter(Number.isFinite), spread = fin.length ? Math.max(...fin) - Math.min(...fin) : NaN;
          const lim = paths.map((P, i) => `${P.label}: ${Number.isFinite(limits[i]) ? fmt(+limits[i].toPrecision(4)) : 'none'}`);
          if (fin.length === paths.length && spread < 1e-4 && Math.abs(fin[0] - fp) < 1e-4) ctx.status('info', `Every path tried gives f(p) = ${fmt(+fp.toPrecision(4))}. That is evidence of continuity, not proof: continuity needs every sequence, not just these.`);
          else ctx.status('fail', `The paths give different values near p, or values other than f(p) = ${Number.isFinite(fp) ? fmt(+fp.toPrecision(4)) : 'undefined'}: f is not continuous at p.`);
          ctx.note('Near p: ' + lim.join('; ') + '.');
        },
      },
      descent: {
        doc: 'descent(f, x0, α) runs gradient descent x ↦ x − α·∇f(x) from x0 over the level curves of f (Example 8.15). Drag the step size α: small steps creep, good ones converge fast, too large ones overshoot, oscillate or blow up (Question 8.5).',
        render(ctx, f, x0, a0 = 0.25) {
          need(typeof f === 'function' && isVec(x0) && x0.length === 2, 'descent(f, x0, α) needs a function of the plane and a starting point, such as descent(p => (p[1] - 1)^2 + (p[2] - 2)^2, (0, 0), 1/4).');
          const alpha = ctx.param('α', { min: 0.01, max: 1.2, step: 0.01, value: a0 });
          const K = Math.round(ctx.param('steps', { min: 1, max: 60, step: 1, value: 12 }));
          const pts = [x0.slice()];
          for (let k = 0; k < K; k++) {
            const x = pts[pts.length - 1], g = grad(f, x);
            const y = [x[0] - alpha * g[0], x[1] - alpha * g[1]];
            if (!y.every(Number.isFinite) || Math.hypot(...y) > 1e6) break;
            pts.push(y);
          }
          const vals = pts.map(x => +at(f, x));
          const fmin = Math.min(...vals.filter(Number.isFinite));
          const xs = pts.map(q => q[0]), ys = pts.map(q => q[1]);
          let cx = (Math.min(...xs) + Math.max(...xs)) / 2, cy = (Math.min(...ys) + Math.max(...ys)) / 2;
          let R = 0.6 * Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys), 1);
          R = Math.min(R, 50);
          const fig = ctx.figure({ x: [cx - R, cx + R], y: [cy - R, cy + R], square: true });
          const mix = (A, B, t) => A.map((v, i) => Math.round(v + (B[i] - v) * t));
          fig.raster({ x: [cx - R, cx + R], y: [cy - R, cy + R], nx: 200, ny: 200, value: (x, y) => { const v = at(f, [x, y]); return typeof v === 'number' ? Math.log(1 + Math.max(0, v - fmin)) : NaN; },
            stats: vals2 => { let lo = Infinity, hi = -Infinity; for (const v of vals2) if (Number.isFinite(v)) { lo = Math.min(lo, v); hi = Math.max(hi, v); } const st = (hi - lo || 1) / 12; const edge = new Uint8Array(vals2.length); for (let j = 0; j < 200; j++) for (let i = 0; i < 200; i++) { const k = j * 200 + i, l = Math.floor(vals2[k] / st); if ((i < 199 && Math.floor(vals2[k + 1] / st) !== l) || (j < 199 && Math.floor(vals2[k + 200] / st) !== l)) edge[k] = 1; } return { lo, hi, edge }; },
            color: (v, T, st, k) => { if (!Number.isFinite(v)) return null; const b = mix(T.rgb('panel'), T.rgb('c1'), 0.05 + 0.35 * (v - st.lo) / ((st.hi - st.lo) || 1)); return st.edge[k] ? [...mix(b, T.rgb('ink'), 0.35), 255] : [...b, 255]; } });
          fig.curve(pts, { color: 'c2', width: 2 });
          fig.points(pts, { color: 'c2', r: 3 });
          fig.points([pts[0]], { color: 'ink', r: 5 });
          ctx.legend([{ label: 'level curves of f', color: 'ink' }, { label: 'x⁽ᵏ⁺¹⁾ = x⁽ᵏ⁾ − α∇f(x⁽ᵏ⁾)', color: 'c2' }]);
          const last = vals[vals.length - 1], blew = pts.length <= K;
          const trend = blew ? 'the iterates run off to infinity' : last < vals[0] * 1e-6 + 1e-12 ? 'f(x⁽ᵏ⁾) drops towards its minimum' : last > vals[0] ? 'f grows: the steps overshoot more each time' : Math.abs(last - vals[0]) < 1e-9 * Math.max(1, Math.abs(vals[0])) ? 'f does not change: the steps jump back and forth' : 'f decreases';
          ctx.table(['k', 'x⁽ᵏ⁾', 'f(x⁽ᵏ⁾)'], pts.slice(0, 8).map((q, k) => [String(k), '(' + q.map(x => fmt(+x.toPrecision(5))).join(', ') + ')', fmt(+vals[k].toPrecision(6))]));
          ctx.note(`With α = ${fmt(alpha)}: ${trend}${blew ? '' : `; after ${pts.length - 1} steps f = ${fmt(+last.toPrecision(5))}`}.`);
        },
      },
      gradient: {
        doc: 'gradient(f, r) draws the level curves of f on [−r, r]² with gradient arrows, which cross the level curves at right angles.',
        render(ctx, f, r = 2) {
          const fig = ctx.figure({ x: [-r, r], y: [-r, r], square: true });
          const mix = (a, b, t) => a.map((v, i) => Math.round(v + (b[i] - v) * t));
          fig.raster({
            x: [-r, r], y: [-r, r], nx: 220, ny: 220,
            value: (x, y) => { const v = at(f, [x, y]); return typeof v === 'number' ? v : NaN; },
            color: (v, T, st, k) => {
              if (!Number.isFinite(v)) return null;
              const t = (v - st.min) / ((st.max - st.min) || 1);
              const base = mix(T.rgb('panel'), T.rgb('c1'), 0.15 + 0.5 * t);
              return st.edge[k] ? [...mix(base, T.rgb('ink'), 0.45), 255] : [...base, 255];
            },
            stats: (vals, nx, ny) => {
              let min = Infinity, max = -Infinity;
              for (const v of vals) if (Number.isFinite(v)) { if (v < min) min = v; if (v > max) max = v; }
              const stepv = ((max - min) || 1) / 14, level = v => Number.isFinite(v) ? Math.floor(v / stepv) : NaN;
              const edge = new Uint8Array(vals.length);
              for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
                const k = j * nx + i, l = level(vals[k]);
                if ((i + 1 < nx && level(vals[k + 1]) !== l) || (j + 1 < ny && level(vals[k + nx]) !== l)) edge[k] = 1;
              }
              return { min, max, edge };
            },
          });
          const n = 13, arrows = [];
          for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
            const p = [-r + 2 * r * (i + 0.5) / n, -r + 2 * r * (j + 0.5) / n];
            const g = grad(f, p);
            if (g.every(Number.isFinite)) arrows.push([p, g]);
          }
          const big = Math.max(1e-12, ...arrows.map(([, g]) => Math.hypot(...g))), L = 2 * r / n * 0.85;
          for (const [p, g] of arrows) fig.arrow(p[0], p[1], p[0] + g[0] / big * L, p[1] + g[1] / big * L, { color: 'c2', width: 1.3, alpha: 0.4 + 0.6 * Math.hypot(...g) / big });
          ctx.legend([{ label: 'level curves', color: 'ink' }, { label: 'gradient (uphill, ⟂ to level curves)', color: 'c2' }]);
        },
      },
      linearize: {
        doc: 'linearize(F, p) shows how F: ℝ² → ℝ² (or f: ℝ² → ℝ) bends a small grid around p, next to its linear approximation F(p) + J(p)(x − p). Shrink the radius: a differentiable map looks more and more linear.',
        render(ctx, F, p) {
          need(isVec(p) && p.length === 2, 'linearize(F, p) needs a point p of the plane.');
          const rad = ctx.param('radius', { min: 0.01, max: 2, step: 0.01, value: 0.8 });
          const v0 = at(F, p);
          if (typeof v0 === 'number') {
            // A real function: its graph near p against the tangent plane.
            const g = grad(F, p);
            const fig = ctx.figure3d({ labels: ['x', 'y', 'z'], equal: false });
            fig.surface((u, v) => [u, v, at(F, [u, v])], { u: [p[0] - rad, p[0] + rad], v: [p[1] - rad, p[1] + rad], n: 26 });
            fig.surface((u, v) => [u, v, v0 + g[0] * (u - p[0]) + g[1] * (v - p[1])], { u: [p[0] - rad, p[0] + rad], v: [p[1] - rad, p[1] + rad], n: 6, color: 'c4', alpha: 0.4 });
            let worst = 0;
            for (let k = 0; k < 200; k++) {
              const a = 2 * Math.PI * k / 200, q = [p[0] + rad * Math.cos(a), p[1] + rad * Math.sin(a)];
              worst = Math.max(worst, Math.abs(at(F, q) - v0 - g[0] * (q[0] - p[0]) - g[1] * (q[1] - p[1])));
            }
            ctx.legend([{ label: 'graph of f', color: 'c1' }, { label: 'tangent plane', color: 'c4' }]);
            ctx.note(`On the circle of radius ${fmt(rad)} around p, the graph is up to ${fmt(+worst.toPrecision(3))} away from the tangent plane, which is ${fmt(+(worst / rad).toPrecision(3))} × the radius. For a differentiable f this ratio tends to 0 as the radius shrinks.`);
            return;
          }
          const J = jacobian(F, p);
          const lin = q => [v0[0] + J[0][0] * (q[0] - p[0]) + J[0][1] * (q[1] - p[1]), v0[1] + J[1][0] * (q[0] - p[0]) + J[1][1] * (q[1] - p[1])];
          const lines = [];
          for (let k = -4; k <= 4; k++) {
            const t = k / 4 * rad;
            lines.push(Array.from({ length: 41 }, (_, i) => [p[0] + t, p[1] - rad + 2 * rad * i / 40]));
            lines.push(Array.from({ length: 41 }, (_, i) => [p[0] - rad + 2 * rad * i / 40, p[1] + t]));
          }
          const imgs = lines.map(l => l.map(q => at(F, q))), lins = lines.map(l => l.map(lin));
          const all = [...imgs, ...lins].flat().filter(q => q.every(Number.isFinite));
          const xs = all.map(q => q[0]), ys = all.map(q => q[1]);
          const pad = 0.08 * Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)) || 1;
          const fig = ctx.figure({ x: [Math.min(...xs) - pad, Math.max(...xs) + pad], y: [Math.min(...ys) - pad, Math.max(...ys) + pad], square: true });
          lins.forEach(l => fig.curve(l, { color: 'c4', width: 1, alpha: 0.6, dash: [4, 3] }));
          imgs.forEach(l => fig.curve(l, { color: 'c1', width: 1.5 }));
          fig.points([v0], { color: 'neg', r: 4 });
          ctx.legend([{ label: 'image of the grid under F', color: 'c1' }, { label: 'under the linear approximation', color: 'c4' }]);
          ctx.note(`J(p) = [[${J[0].map(x => fmt(+x.toPrecision(4))).join(', ')}], [${J[1].map(x => fmt(+x.toPrecision(4))).join(', ')}]], det ${fmt(+(J[0][0] * J[1][1] - J[0][1] * J[1][0]).toPrecision(4))}. Shrink the radius and the two grids agree more and more.`);
        },
      },
      level_surface: {
        doc: 'level_surface(f, c, r) draws the level set f = c of a function of (x, y, z) in the box [−r, r]³ as a cloud of points, and marks where the gradient vanishes (where the set may fail to be a smooth surface).',
        render(ctx, f, c = 0, r = 2) {
          const S = LevelSet(f, c, r, 3);
          const pts = S.sample(600);
          const fig = ctx.figure3d({ box: [[-r, r], [-r, r], [-r, r]] });
          const sing = [];
          const shown = pts.map(p => {
            const g = grad(f, p), m = Math.hypot(...g), q = p.slice();
            q.color = m < 1e-3 ? 'neg' : 'c1';
            if (m < 1e-3 && !sing.some(s => Math.hypot(...s.map((x, i) => x - p[i])) < 1e-3)) sing.push(p);
            return q;
          });
          fig.points(shown.filter(p => p.color !== 'neg'), { r: 2, alpha: 0.7 });
          fig.points(shown.filter(p => p.color === 'neg'), { r: 5, alpha: 1 });
          ctx.legend([{ label: `f = ${fmt(c)}`, color: 'c1' }, ...(sing.length ? [{ label: 'gradient ≈ 0', color: 'neg' }] : [])]);
          ctx.note(sing.length ? `The gradient vanishes at ${sing.slice(0, 3).map(p => '(' + p.map(x => fmt(+x.toFixed(4))).join(', ') + ')').join(', ')}: ${fmt(c)} is not a regular value, and the level set can have a singular point there.`
            : `The gradient doesn't vanish on the points found: ${fmt(c)} looks like a regular value, so the level set is a smooth surface.`);
        },
      },
    },
    notation: `
# f is continuous at the point p of ℝⁿ: for every ε some ball around p is mapped within ε of f(p).
# examples: f in Functions2, p in {(0, 0), (0.5, 0.5)}
def continuous_at_point(f, p) := forall ε in (0, 1]: exists δ in (0, 1]: forall x in Ball(p, δ): |f(x) - f(p)| < ε

# f is differentiable at p: near p it is its tangent plane, up to an error small compared with |x − p|.
# examples: f in Functions2, p in {(0, 0), (0.5, 0.5)}
def differentiable_at_point(f, p) := forall ε in (0, 1]: exists δ in (0, 1]: forall x in Ball(p, δ): |f(x) - f(p) - dot(grad(f, p), x - p)| <= ε * |x - p|

# c is a regular value of f on [−r, r]ⁿ: the gradient doesn't vanish anywhere on the level set f = c.
def regular_value(f, c, r, n) := forall p in LevelSet(f, c, r, n): |grad(f, p)| > 1e-6

# f has a local minimum at p: no point of some ball around p gives a smaller value (Definition 9.8).
# examples: f in {p => p[1]^2 + p[2]^2, p => p[1]^2 - p[2]^2, p => p[1]^4 + p[2]^4}, p in {(0, 0)}
def local_min(f, p) := exists ε in (0, 1]: forall y in Ball(p, ε): f(p) <= f(y)

# f has a local maximum at p.
# examples: f in {p => -(p[1]^2 + p[2]^2), p => p[1]^2 - p[2]^2}, p in {(0, 0)}
def local_max(f, p) := exists ε in (0, 1]: forall y in Ball(p, ε): f(y) <= f(p)

# The Hessian test is right: a positive definite Hessian at a critical point gives a local minimum (Theorem 9.15).
lemma hessian_test_min: forall f in {p => p[1]^2 + 3*p[2]^2 - p[1]*p[2] + p[1], p => (p[1]^2 - 1)^2 + p[2]^2, p => sin(p[1])*cos(p[2])}: forall q in critical_points(f, 2): min_by_hessian(f, q) -> local_min(f, q)

# But it isn't complete: x⁴ + y⁴ has a local minimum at 0 where the Hessian is 0.
conjecture local_min_needs_hessian: forall f in {p => p[1]^2 + p[2]^2, p => p[1]^4 + p[2]^4}: local_min(f, (0, 0)) -> min_by_hessian(f, (0, 0))

# At a local minimum the gradient vanishes (Theorem 9.10).
lemma extremum_is_critical: forall f in {p => (p[1] - 1)^2 + (p[2] + 2)^2, p => p[1]^2 + p[1]*p[2] + p[2]^2 - 3*p[2]}: forall q in critical_points(f, 3): local_min(f, q) -> |grad(f, q)| < 1e-6

# The Taylor polynomial of degree 2 is within C·‖x − p‖³ of f near p (Remark 9.6).
lemma taylor_remainder: forall x in Ball((0.3, 0.2), 0.3): |exp(x[1])*sin(x[2]) - taylor_poly(q => exp(q[1])*sin(q[2]), (0.3, 0.2), 2)(x)| <= 2 * |x - (0.3, 0.2)|^3

# Differentiable implies continuous, in several variables too.
lemma differentiable_continuous: forall f in Functions2, p in {(0, 0), (0.5, 0.5)}: differentiable_at_point(f, p) -> (forall x in Ball(p, 0.001): |f(x) - f(p)| < 0.01)

# Do partial derivatives at a point make f differentiable there? xy/(x² + y²) says no.
conjecture partials_give_differentiable: forall f in Functions2: partials_exist(f, (0, 0)) -> differentiable_at_point(f, (0, 0))

# Do the mixed partials always agree (Clairaut)? Not without continuity: xy(x² − y²)/(x² + y²) at 0.
conjecture mixed_partials_agree: forall f in Functions2, p in {(0, 0), (0.3, 0.7)}: |mixed_partial(f, p, 1, 2) - mixed_partial(f, p, 2, 1)| < 0.001

# For smooth functions away from trouble, the mixed partials agree.
lemma clairaut_smooth: forall f in Functions2, p in {(0.3, 0.7), (-0.5, 0.4)}: |mixed_partial(f, p, 1, 2) - mixed_partial(f, p, 2, 1)| < 0.001

# The gradient is perpendicular to the level set: moving along it, f doesn't change to first order.
lemma gradient_normal_to_level_curve: forall p in LevelSet(p => p[1]^2 + p[2]^2, 1, 2, 2): |dot(grad(p => p[1]^2 + p[2]^2, p), (-p[2], p[1]))| < 1e-6
`,
  });
});
