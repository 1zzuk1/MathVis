MathVizLibrary(function linalg(MathViz) {
  const isVec = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');
  const isMat = v => Array.isArray(v) && v.length > 0 && v.every(isVec) && v.every(r => r.length === v[0].length);
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const sameLen = (a, b) => need(a.length === b.length, `Vectors of lengths ${a.length} and ${b.length} can't be combined.`);
  const vadd = (a, b) => { sameLen(a, b); return a.map((x, i) => x + b[i]); };
  const vsub = (a, b) => { sameLen(a, b); return a.map((x, i) => x - b[i]); };
  const vscale = (c, a) => a.map(x => c * x);
  const dot = (a, b) => {
    need(isVec(a) && isVec(b), 'dot expects two vectors, as in dot((1, 2), (3, 4)).');
    sameLen(a, b);
    return a.reduce((s, x, i) => s + x * b[i], 0);
  };
  const norm = v => Math.sqrt(dot(v, v));
  const size = A => `${A.length}×${A[0].length}`;
  const matmul = (A, B) => {
    need(A[0].length === B.length, `Can't multiply a ${size(A)} matrix by a ${size(B)} matrix.`);
    return A.map(r => B[0].map((_, j) => r.reduce((s, x, k) => s + x * B[k][j], 0)));
  };
  const matvec = (A, v) => {
    need(A[0].length === v.length, `Can't multiply a ${size(A)} matrix by a vector of length ${v.length}.`);
    return A.map(r => r.reduce((s, x, k) => s + x * v[k], 0));
  };
  const asMat = (A, what) => { need(isMat(A), `${what} expects a matrix, written as a list of rows like [[1, 2], [3, 4]].`); return A; };
  const square = (A, what) => need(isMat(A) && A.length === A[0].length, `${what} expects a square matrix.`);
  const identity = n => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => +(i === j)));
  const zeros = (m, n = m) => Array.from({ length: m }, () => new Array(n).fill(0));
  const transpose = A => asMat(A, 'transpose')[0].map((_, j) => A.map(r => r[j]));

  /* ---------- operator norms ---------- */
  const vpnorm = (v, p) => (p === Infinity ? Math.max(...v.map(Math.abs)) : Math.pow(v.reduce((t, x) => t + Math.abs(x) ** p, 0), 1 / p));
  // The eigenvalues of a symmetric matrix, by Jacobi rotations (accurate even when they differ
  // wildly in size, where the characteristic polynomial loses the small ones).
  function symEigs(S) {
    const n = S.length, a = S.map(r => r.slice());
    for (let sweep = 0; sweep < 60; sweep++) {
      let off = 0;
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) off += a[i][j] ** 2;
      if (off < 1e-30) break;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
        if (Math.abs(a[p][q]) < 1e-300) continue;
        const th = (a[q][q] - a[p][p]) / (2 * a[p][q]);
        const t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), sn = t * c;
        for (let k = 0; k < n; k++) { const x = a[k][p], y = a[k][q]; a[k][p] = c * x - sn * y; a[k][q] = sn * x + c * y; }
        for (let k = 0; k < n; k++) { const x = a[p][k], y = a[q][k]; a[p][k] = c * x - sn * y; a[q][k] = sn * x + c * y; }
      }
    }
    return a.map((r, i) => r[i]).sort((x, y) => y - x);
  }
  const symMaxEig = S => symEigs(S)[0];
  // ‖A‖ = sup{‖Ax‖ : ‖x‖ ≤ 1} for the p-norm on both sides (Definition 6.22): exact formulas for
  // p = 1 (largest column sum), ∞ (largest row sum) and 2 (√ of the largest eigenvalue of AᵀA);
  // other p by searching the unit sphere of the plane.
  function opnorm(A, p = 2) {
    asMat(A, 'opnorm');
    need(p === Infinity || (typeof p === 'number' && p >= 1), 'opnorm(A, p) takes p ≥ 1 or inf.');
    if (p === 1) return Math.max(...A[0].map((_, j) => A.reduce((t, r) => t + Math.abs(r[j]), 0)));
    if (p === Infinity) return Math.max(...A.map(r => r.reduce((t, x) => t + Math.abs(x), 0)));
    if (p === 2) return Math.sqrt(Math.max(0, symMaxEig(matmul(transpose(A), A))));
    need(A[0].length === 2, 'opnorm(A, p) for p other than 1, 2 and inf needs a matrix with 2 columns.');
    MathViz.markInexact();
    let best = 0;
    for (let k = 0; k < 3600; k++) { const a = Math.PI * k / 3600, v = [Math.cos(a), Math.sin(a)], L = vpnorm(v, p); best = Math.max(best, vpnorm(matvec(A, v.map(x => x / L)), p)); }
    return best;
  }

  /* ---------- exact rationals (BigInt), used whenever the entries are fractions ---------- */
  const babs = a => a < 0n ? -a : a;
  const bgcd = (a, b) => { a = babs(a); b = babs(b); while (b) [a, b] = [b, a % b]; return a; };
  const Q = (n, d = 1n) => {
    if (d < 0n) { n = -n; d = -d; }
    const g = bgcd(n, d) || 1n;
    return { n: n / g, d: d / g };
  };
  // A number as a fraction p/q with q ≤ 10⁶, when it is one (to rounding); else null.
  const toQ = x => {
    if (!Number.isFinite(x)) return null;
    if (Number.isInteger(x)) return Math.abs(x) < 2 ** 53 ? Q(BigInt(x)) : null;
    let h0 = 1, h1 = 0, k0 = 0, k1 = 1, y = x;
    for (let i = 0; i < 40; i++) {
      const a = Math.floor(y);
      [h0, h1] = [a * h0 + h1, h0];
      [k0, k1] = [a * k0 + k1, k0];
      if (k0 > 1e6) return null;
      // Within a few units in the last place: a fraction computed in floating point, not a lucky approximation.
      if (Math.abs(x - h0 / k0) <= 8 * Number.EPSILON * Math.max(1, Math.abs(x))) return Q(BigInt(h0), BigInt(k0));
      const f = y - a;
      if (f < 1e-15) break;
      y = 1 / f;
    }
    return null;
  };
  const QF = {
    exact: true,
    zero: Q(0n), one: Q(1n),
    add: (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d),
    sub: (a, b) => Q(a.n * b.d - b.n * a.d, a.d * b.d),
    mul: (a, b) => Q(a.n * b.n, a.d * b.d),
    div: (a, b) => Q(a.n * b.d, a.d * b.n),
    neg: a => Q(-a.n, a.d),
    isZero: a => a.n === 0n,
    isOne: a => a.n === a.d,
    num: a => Number(a.n) / Number(a.d),
    str: a => (a.n < 0n ? '−' : '') + babs(a.n).toString() + (a.d === 1n ? '' : '/' + a.d.toString()),
  };
  const FF = tol => ({
    exact: false,
    zero: 0, one: 1,
    add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b, div: (a, b) => a / b, neg: a => -a,
    isZero: a => Math.abs(a) <= tol, isOne: a => Math.abs(a - 1) <= tol,
    num: a => a,
    str: a => frac(a),
  });
  // Pick exact arithmetic when every entry is a fraction.
  // In floating point, rows can first be scaled by powers of 2 (exactly, no rounding) to similar
  // sizes, so pivoting isn't fooled by one huge row; rowScale is the product of those factors.
  const field = (A, tol = 1e-10, equilibrate = false) => {
    const qs = A.map(r => r.map(toQ));
    if (qs.every(r => r.every(Boolean))) return { F: { ...QF, isZeroIn: QF.isZero }, M: qs, rowScale: 1 };
    const s = A.map(r => { const mx = Math.max(...r.map(Math.abs)); return equilibrate && mx > 0 && Number.isFinite(mx) ? Math.pow(2, Math.round(Math.log2(mx))) : 1; });
    const M = A.map((r, i) => r.map(x => x / s[i]));
    const scale = Math.max(1, ...M.flat().map(Math.abs));
    const F = FF(tol * scale);
    // Entries are judged against their own column, so diag(10⁻⁸, 1, 10⁸) still has rank 3.
    const colScale = M[0].map((_, j) => Math.max(...M.map(r => Math.abs(r[j]))) || 1);
    F.isZeroIn = (x, c) => Math.abs(x) <= tol * Math.min(scale, colScale[c] ?? scale);
    return { F, M, rowScale: s.reduce((a, b) => a * b, 1) };
  };
  // A number shown as a fraction when it is a simple one: 0.333… as 1/3.
  const frac = x => {
    if (typeof x !== 'number') return MathViz.format(x);
    const q = Number.isInteger(x) ? null : toQ(x);
    if (q && q.d <= 1000n) return QF.str(q);
    return MathViz.format(Math.abs(x) < 1e-12 ? 0 : +x.toPrecision(6));
  };

  /* ---------- row reduction, recording each step ---------- */
  function rrefCore(A, opts = {}) {
    // Steps are shown as the user wrote the rows, so only unshown reductions are equilibrated.
    const { F, M, rowScale } = field(A, opts.tol, !opts.steps);
    const m = M.length, n = M[0].length, cols = opts.cols ?? n;
    const steps = [], pivots = [];
    const snap = () => M.map(r => r.map(x => F.str(x)));
    const R = i => `R${i + 1}`;
    let det = F.one, r = 0;
    for (let c = 0; c < cols && r < m; c++) {
      // Pivot: exactly, the first nonzero entry; in floating point, the largest (for stability).
      let p = -1;
      for (let i = r; i < m; i++) {
        if (F.isZeroIn(M[i][c], c)) continue;
        if (p < 0 || (!F.exact && Math.abs(M[i][c]) > Math.abs(M[p][c]))) p = i;
        if (F.exact) break;
      }
      if (p < 0) { det = F.zero; continue; }
      if (p !== r) {
        [M[p], M[r]] = [M[r], M[p]];
        det = F.neg(det);
        if (opts.steps) steps.push({ text: `${R(r)} ↔ ${R(p)}`, M: snap() });
      }
      const piv = M[r][c];
      det = F.mul(det, piv);
      if (!F.isOne(piv)) {
        M[r] = M[r].map(x => F.div(x, piv));
        if (opts.steps) steps.push({ text: `${R(r)} ← ${R(r)} / ${F.str(piv)}`, M: snap() });
      }
      const ops = [];
      for (let i = 0; i < m; i++) {
        if (i === r || F.isZeroIn(M[i][c], c)) continue;
        const f = M[i][c];
        M[i] = M[i].map((x, k) => F.sub(x, F.mul(f, M[r][k])));
        const fs = F.str(f);
        ops.push(fs.startsWith('−') ? `${R(i)} ← ${R(i)} + ${fs === '−1' ? '' : fs.slice(1) + '·'}${R(r)}` : `${R(i)} ← ${R(i)} − ${fs === '1' ? '' : fs + '·'}${R(r)}`);
      }
      if (opts.steps && ops.length) steps.push({ text: ops.join(',  '), M: snap() });
      pivots.push(c);
      r++;
    }
    if (pivots.length < Math.min(m, cols) || m !== cols) det = pivots.length === m && m === cols ? det : F.zero;
    // Clean tiny floating-point leftovers.
    const out = M.map(row => row.map(x => { const v = F.num(x); return Math.abs(v) < 1e-12 ? 0 : v; }));
    return { R: out, pivots, steps, det: F.num(det) * rowScale, exact: F.exact, F, M };
  }

  const rref = A => rrefCore(asMat(A, 'rref')).R;
  const rank = A => rrefCore(asMat(A, 'rank')).pivots.length;
  const det = A => {
    square(A, 'det');
    const { F, M, rowScale } = field(A, 1e-10, true);
    const n = M.length;
    let d = F.one;
    for (let c = 0; c < n; c++) {
      let p = -1;
      for (let i = c; i < n; i++) if (!F.isZeroIn(M[i][c], c) && (p < 0 || (!F.exact && Math.abs(M[i][c]) > Math.abs(M[p][c])))) { p = i; if (F.exact) break; }
      if (p < 0) return 0;
      if (p !== c) { [M[p], M[c]] = [M[c], M[p]]; d = F.neg(d); }
      d = F.mul(d, M[c][c]);
      for (let i = c + 1; i < n; i++) {
        if (F.isZeroIn(M[i][c], c)) continue;
        const f = F.div(M[i][c], M[c][c]);
        for (let k = c; k < n; k++) M[i][k] = F.sub(M[i][k], F.mul(f, M[c][k]));
      }
    }
    return F.num(d) * rowScale;
  };
  const inv = A => {
    square(A, 'inv');
    const n = A.length;
    const { R, pivots } = rrefCore(A.map((r, i) => [...r, ...identity(n)[i]]), { cols: n });
    need(pivots.length === n, 'This matrix is singular (its determinant is 0), so it has no inverse.');
    return R.map(r => r.slice(n));
  };

  // A basis of the null space {x : Ax = 0}, from the reduced form.
  const kernelBasis = (A, tol) => {
    const { R, pivots } = rrefCore(A, { tol });
    const n = A[0].length, free = [...Array(n).keys()].filter(c => !pivots.includes(c));
    return free.map(f => {
      const v = new Array(n).fill(0);
      v[f] = 1;
      pivots.forEach((pc, row) => { v[pc] = -R[row][f]; });
      return v.map(x => Math.abs(x) < 1e-12 ? 0 : x);
    });
  };

  /* ---------- subspaces (and affine subspaces) as sets ---------- */
  function gramSchmidt(vs, tol = 1e-10) {
    const out = [];
    for (const v of vs) {
      let w = v.slice();
      for (const q of out) w = vsub(w, vscale(dot(w, q), q));
      // Twice, for accuracy.
      for (const q of out) w = vsub(w, vscale(dot(w, q), q));
      const l = Math.sqrt(dot(w, w));
      if (l > tol * Math.max(1, Math.sqrt(dot(v, v)))) out.push(vscale(1 / l, w));
    }
    return out;
  }
  const fmtVec = v => '(' + v.map(frac).join(', ') + ')';
  function subspace(basis, n, o = {}) {
    const offset = o.offset || new Array(n).fill(0);
    const ortho = gramSchmidt(basis);
    const k = ortho.length;
    // Keep the given basis vectors (nicer to read), minus any that depend on the others.
    const indep = [];
    for (const b of basis) if (gramSchmidt([...indep, b]).length > indep.length) indep.push(b);
    const affine = offset.some(x => x !== 0);
    const label = o.label || (k === 0 ? (affine ? `{${fmtVec(offset)}}` : `{0}`)
      : (affine ? `${fmtVec(offset)} + ` : '') + `span{${indep.map(fmtVec).join(', ')}}`);
    let seed = 7;
    const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
    const combo = cs => cs.reduce((acc, c, i) => vadd(acc, vscale(c, indep[i])), offset.slice());
    const S = MathViz.space({
      kind: 'subspace', label, basis: indep, ortho, offset, n, k, dim: n, numeric: true, affine,
      contains: v => {
        if (!isVec(v) || v.length !== n) return false;
        let w = vsub(v, offset);
        const scale = Math.max(1, Math.sqrt(dot(w, w)), Math.sqrt(dot(offset, offset)));
        for (const q of ortho) w = vsub(w, vscale(dot(w, q), q));
        return Math.sqrt(dot(w, w)) <= 1e-8 * scale;
      },
      sample: m => {
        const out = [offset.slice()];
        indep.forEach(b => { out.push(vadd(offset, b), vsub(offset, b)); });
        if (k >= 2) out.push(combo(indep.map(() => 1)), combo(indep.map((_, i) => (i % 2 ? -1 : 2))));
        while (out.length < Math.max(m, 1) && k > 0) out.push(combo(indep.map(() => Math.round((rnd() * 6 - 3) * 4) / 4)));
        return out.slice(0, Math.max(1, Math.min(m, out.length)));
      },
      random: () => combo(indep.map(() => rnd() * 4 - 2)),
      window: () => {
        const pts = S.sample(40);
        return [...Array(n).keys()].map(i => { const xs = pts.map(p => p[i]); const lo = Math.min(...xs, -1), hi = Math.max(...xs, 1); return [lo, hi]; });
      },
      describe: () => label,
      // Two subspaces are equal when each contains the other's basis (and offset).
      sameSet: T => !!(T && T.kind === 'subspace' && T.n === n && T.k === k && T.contains(offset) && S.contains(T.offset) &&
        T.basis.every(b => S.contains(vadd(T.offset, b))) && indep.every(b => T.contains(vadd(offset, b)))),
    });
    return S;
  }
  const asSub = (S, what) => { need(S && S.kind === 'subspace', `${what} expects a subspace, such as Span((1, 0, 1)), kernel(A) or image(A).`); return S; };
  const Span = (...vs) => {
    if (vs.length === 1 && Array.isArray(vs[0]) && vs[0].every(isVec)) vs = vs[0];
    need(vs.length && vs.every(isVec) && vs.every(v => v.length === vs[0].length), 'Span takes vectors of the same length, as in Span((1, 0, 1), (0, 1, 1)).');
    return subspace(vs, vs[0].length);
  };
  const kernel = A => { asMat(A, 'kernel'); return subspace(kernelBasis(A), A[0].length); };
  const image = A => {
    asMat(A, 'image');
    const { pivots } = rrefCore(A);
    return subspace(pivots.map(c => A.map(r => r[c])), A.length);
  };
  const rowspace = A => {
    const { R, pivots } = rrefCore(asMat(A, 'rowspace'));
    return subspace(R.slice(0, pivots.length), A[0].length);
  };
  const solveAll = (A, b) => {
    asMat(A, 'solve');
    if (typeof b === 'number' && A.length === 1) b = [b];
    need(isVec(b) && b.length === A.length, `solve(A, b) needs b to have ${A.length} entries, one per row of A.`);
    const { R, pivots } = rrefCore(A.map((r, i) => [...r, b[i]]), { cols: A[0].length });
    const n = A[0].length;
    // Inconsistent: a row 0 = c with c ≠ 0.
    if (R.some((r, i) => i >= pivots.length && Math.abs(r[n]) > 1e-9 * Math.max(1, ...b.map(Math.abs)))) return null;
    const x = new Array(n).fill(0);
    pivots.forEach((pc, row) => { x[pc] = R[row][n]; });
    return { x, kernel: kernelBasis(A) };
  };

  /* ---------- characteristic polynomial and eigenvalues ---------- */
  // Coefficients [1, c₁, …, cₙ] of det(λI − A) = λⁿ + c₁λⁿ⁻¹ + … + cₙ (Faddeev–LeVerrier), exactly when possible.
  function charpolyQ(A) {
    const { F, M } = field(A);
    const n = M.length;
    const I = identity(n).map(r => r.map(x => x ? F.one : F.zero));
    const mul = (X, Y) => X.map(r => Y[0].map((_, j) => r.reduce((s, x, k) => F.add(s, F.mul(x, Y[k][j])), F.zero)));
    const coeffs = [F.one];
    let Mk = I.map(r => r.map(() => F.zero));
    for (let k = 1; k <= n; k++) {
      Mk = mul(M, Mk).map((r, i) => r.map((x, j) => F.add(x, i === j ? coeffs[k - 1] : F.zero)));
      const AM = mul(M, Mk);
      let tr = F.zero;
      for (let i = 0; i < n; i++) tr = F.add(tr, AM[i][i]);
      coeffs.push(F.div(F.neg(tr), F.exact ? Q(BigInt(k)) : k));
    }
    return { F, coeffs };
  }
  const charpoly = A => { square(A, 'charpoly'); const { F, coeffs } = charpolyQ(A); return coeffs.map(F.num); };
  // Roots of a polynomial with real coefficients (highest power first), as [re, im] pairs.
  function polyRoots(c) {
    while (c.length > 1 && Math.abs(c[0]) < 1e-300) c = c.slice(1);
    const n = c.length - 1;
    if (n < 1) return [];
    const a = c.map(x => x / c[0]);
    const cmul = (p, q) => [p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0]];
    const cdiv = (p, q) => { const d = q[0] * q[0] + q[1] * q[1] || 1e-300; return [(p[0] * q[0] + p[1] * q[1]) / d, (p[1] * q[0] - p[0] * q[1]) / d]; };
    const evalAt = z => { let v = [1, 0]; for (let i = 1; i <= n; i++) v = [v[0] * z[0] - v[1] * z[1] + a[i], v[0] * z[1] + v[1] * z[0]]; return v; };
    const R = 1 + Math.max(...a.slice(1).map(Math.abs));
    let zs = Array.from({ length: n }, (_, k) => { const t = 2 * Math.PI * k / n + 0.4; return [R * 0.9 * Math.cos(t), R * 0.9 * Math.sin(t)]; });
    for (let it = 0; it < 800; it++) {
      let moved = 0;
      zs = zs.map((z, i) => {
        let den = [1, 0];
        zs.forEach((w, j) => { if (j !== i) den = cmul(den, [z[0] - w[0], z[1] - w[1]]); });
        const d = cdiv(evalAt(z), den);
        moved = Math.max(moved, Math.hypot(d[0], d[1]));
        return [z[0] - d[0], z[1] - d[1]];
      });
      if (moved < 1e-15 * R) break;
    }
    return zs;
  }
  // Rational roots of a polynomial with rational coefficients (rational root theorem), with multiplicity.
  function rationalRoots(coeffs) {
    // Clear denominators.
    let L = 1n;
    for (const q of coeffs) L = L / bgcd(L, q.d) * q.d;
    let p = coeffs.map(q => q.n * (L / q.d));
    const roots = [];
    const divisors = x => {
      x = babs(x);
      if (x > 10n ** 7n) return null;
      const out = [];
      for (let d = 1n; d * d <= x; d++) if (x % d === 0n) { out.push(d); if (d * d !== x) out.push(x / d); }
      return out;
    };
    const evalQ = (poly, r) => poly.reduce((s, c) => QF.add(QF.mul(s, r), Q(c)), QF.zero);
    const deflate = (poly, r) => {
      const out = [];
      let acc = QF.zero;
      for (let i = 0; i < poly.length - 1; i++) { acc = QF.add(QF.mul(acc, r), Q(poly[i])); out.push(acc); }
      let D = 1n;
      for (const q of out) D = D / bgcd(D, q.d) * q.d;
      return out.map(q => q.n * (D / q.d));
    };
    for (let guard = 0; guard < 64 && p.length > 1; guard++) {
      while (p.length > 1 && p[p.length - 1] === 0n) { roots.push(QF.zero); p = p.slice(0, -1); }
      if (p.length <= 1) break;
      const ps = divisors(p[p.length - 1]), qs = divisors(p[0]);
      if (!ps || !qs) break;
      let found = null;
      outer: for (const a of ps) for (const b of qs) for (const s of [1n, -1n]) {
        const r = Q(s * a, b);
        if (QF.isZero(evalQ(p, r))) { found = r; break outer; }
      }
      if (!found) break;
      roots.push(found);
      p = deflate(p, found);
    }
    return { roots, rest: p.map(Number) };
  }
  // All eigenvalues as [re, im] pairs, exact rational ones first.
  function eigenPairs(A) {
    square(A, 'eigenvalues');
    const { F, coeffs } = charpolyQ(A);
    let exact = [], rest = coeffs.map(F.num);
    if (F.exact) { const rr = rationalRoots(coeffs); exact = rr.roots.map(QF.num); rest = rr.rest; }
    const others = polyRoots(rest).map(([re, im]) => {
      // Snap to the real line, and polish real roots with Newton steps on the full polynomial.
      if (Math.abs(im) < 1e-7 * Math.max(1, Math.abs(re))) {
        let x = re;
        const P = coeffs.map(F.num);
        for (let i = 0; i < 6; i++) {
          let v = 0, d = 0;
          for (const c of P) { d = d * x + v; v = v * x + c; }
          if (!d) break;
          const nx = x - v / d;
          if (!Number.isFinite(nx) || Math.abs(nx - x) > 1e-6 * Math.max(1, Math.abs(x))) break;
          x = nx;
        }
        return [x, 0];
      }
      return [re, im];
    });
    return [...exact.map(x => [x, 0]), ...others];
  }
  const eigenvalues = A => eigenPairs(A).filter(p => p[1] === 0).map(p => p[0]).sort((a, b) => b - a);
  const eigenspace = (A, lambda) => {
    square(A, 'eigenspace');
    need(typeof lambda === 'number', 'eigenspace(A, λ) needs a number λ.');
    const n = A.length, B = A.map((r, i) => r.map((x, j) => x - (i === j ? lambda : 0)));
    // An eigenvalue known only to rounding makes A − λI only nearly singular, so decide rank loosely.
    return subspace(kernelBasis(B, toQ(lambda) ? 1e-10 : 1e-7), n);
  };
  const diagonalizable = A => {
    square(A, 'diagonalizable');
    const pairs = eigenPairs(A);
    if (pairs.some(p => p[1] !== 0)) return false;
    const distinct = [];
    for (const [x] of pairs) if (!distinct.some(y => Math.abs(x - y) <= 1e-7 * Math.max(1, Math.abs(x)))) distinct.push(x);
    return distinct.reduce((s, l) => s + eigenspace(A, l).k, 0) === A.length;
  };
  const polyeval = (p, X) => {
    need(isVec(p), 'polyeval(p, x) takes coefficients (highest power first), as in polyeval((1, 0, -2), x) = x² − 2.');
    if (typeof X === 'number') return p.reduce((s, c) => s * X + c, 0);
    square(X, 'polyeval');
    const n = X.length;
    return p.reduce((S, c) => matmul(S, X).map((r, i) => r.map((x, j) => x + (i === j ? c : 0))), zeros(n));
  };

  /* ---------- example matrices ---------- */
  const named = (A, label) => { A.label = label; return A; };
  const c30 = Math.cos(Math.PI / 6), s30 = Math.sin(Math.PI / 6);
  const cat2 = () => [
    named(identity(2), 'identity'),
    named([[0, 0], [0, 0]], 'zero'),
    named([[2, 0], [0, 3]], 'diagonal'),
    named([[0, -1], [1, 0]], 'rotation by 90°'),
    named([[c30, -s30], [s30, c30]], 'rotation by 30°'),
    named([[1, 0], [0, -1]], 'reflection'),
    named([[1, 1], [0, 1]], 'shear'),
    named([[1, 0], [0, 0]], 'projection'),
    named([[0, 1], [0, 0]], 'nilpotent'),
    named([[1, 2], [2, 4]], 'singular'),
    named([[2, 1], [1, 2]], 'symmetric'),
    named([[1, 2], [3, 4]], '[[1, 2], [3, 4]]'),
  ];
  const cat3 = () => [
    named(identity(3), 'identity'),
    named(zeros(3), 'zero'),
    named([[1, 0, 0], [0, 2, 0], [0, 0, 3]], 'diagonal'),
    named([[0, -1, 0], [1, 0, 0], [0, 0, 1]], 'rotation about z'),
    named([[0, 1, 0], [0, 0, 1], [1, 0, 0]], 'cyclic permutation'),
    named([[1, 1, 0], [0, 1, 1], [0, 0, 1]], 'Jordan block'),
    named([[0, 1, 0], [0, 0, 1], [0, 0, 0]], 'nilpotent'),
    named([[1, 2, 3], [4, 5, 6], [7, 8, 9]], 'rank 2'),
    named([[1, 1, 1], [1, 1, 1], [1, 1, 1]], 'rank 1'),
    named([[2, -1, 0], [-1, 2, -1], [0, -1, 2]], 'symmetric'),
    named([[1, 0, 0], [0, 1, 0], [0, 0, 0]], 'projection onto a plane'),
  ];
  const wild2 = () => [
    named([[1, 1], [1, 1 + 1e-9]], 'nearly singular'),
    named([[1e6, 1], [1, 1e-6]], 'badly scaled'),
    named([[0, 1], [-1, -1e-8]], 'almost a rotation'),
    named([[1, 1e8], [0, 1]], 'huge shear'),
  ];
  const wild3 = () => [
    named([[1, 1 / 2, 1 / 3], [1 / 2, 1 / 3, 1 / 4], [1 / 3, 1 / 4, 1 / 5]], 'Hilbert matrix'),
    named([[1, 1, 0], [0, 1, 1e-9], [0, 0, 1]], 'nearly defective'),
    named([[1e-8, 0, 0], [0, 1, 0], [0, 0, 1e8]], 'wildly scaled'),
  ];
  const caches = {};
  const Matrices = n => {
    need(n === 2 || n === 3, 'Matrices(n) has example matrices for n = 2 and n = 3.');
    MathViz.markStressable();
    const key = n + ':' + MathViz.stress();
    return caches[key] || (caches[key] = MathViz.finite([...(n === 2 ? cat2() : cat3()), ...(MathViz.stress() ? (n === 2 ? wild2() : wild3()) : [])], { label: `example ${n}×${n} matrices` }));
  };
  // All m×n matrices, sampled: simple ones first, then random integer and real matrices.
  const matSpaces = {};
  const Mat = (m, n = m) => {
    need(Number.isInteger(m) && Number.isInteger(n) && m >= 1 && n >= 1 && m <= 8 && n <= 8, 'Mat(m, n) takes sizes from 1 to 8, as in Mat(3) or Mat(2, 3).');
    MathViz.markStressable();
    const key = `${m}×${n}:${MathViz.stress()}`;
    if (matSpaces[key]) return matSpaces[key];
    let seed = 12345 + 97 * m + n;
    const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
    const simple = [];
    if (m === n && m <= 3) simple.push(...(m === 2 ? cat2() : m === 3 ? cat3() : [named(identity(1), 'identity')]));
    else {
      simple.push(named(zeros(m, n), 'zero'));
      simple.push(named(Array.from({ length: m }, (_, i) => Array.from({ length: n }, (_, j) => +(i === j))), 'ones on the diagonal'));
      simple.push(named(Array.from({ length: m }, (_, i) => Array.from({ length: n }, (_, j) => i + j + 1)), 'rank ≤ 2'));
    }
    if (MathViz.stress() && m === n && m <= 3) simple.push(...(m === 2 ? wild2() : wild3()));
    const pool = [...simple];
    for (let t = 0; t < 300; t++) {
      const intEntries = t % 3 !== 2;
      pool.push(Array.from({ length: m }, () => Array.from({ length: n }, () => intEntries ? Math.round(rnd() * 6 - 3) : Math.round((rnd() * 4 - 2) * 100) / 100)));
    }
    return (matSpaces[key] = MathViz.space({
      kind: 'matrices', label: m === n ? `Mat(${m})` : `Mat(${m}, ${n})`, simpleFirst: true,
      contains: A => isMat(A) && A.length === m && A[0].length === n,
      sample: k => pool.slice(0, Math.max(1, k)),
      random: () => pool[Math.floor(rnd() * pool.length)],
      describe: () => m === n ? `the ${m}×${m} matrices` : `the ${m}×${n} matrices`,
    }));
  };

  /* ---------- drawing helpers for views ---------- */
  const matHTML = (rows, o = {}) => {
    const esc = s => String(s).replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' })[c]);
    const piv = new Set((o.pivots || []).map(([i, j]) => i + ',' + j));
    return `<table class="mat${o.aug ? ' aug' : ''}" style="--aug:${o.aug || 0}">` + rows.map((r, i) => '<tr>' + r.map((x, j) =>
      `<td class="${piv.has(i + ',' + j) ? 'piv' : ''}${o.aug && j === r.length - o.aug ? ' bar' : ''}">${esc(x)}</td>`).join('') + '</tr>').join('') + '</table>';
  };

  MathViz.thumbnail(v => isMat(v) && v.length === 2 && v[0].length === 2, (fig, M) => {
    const ap = (x, y) => [M[0][0] * x + M[0][1] * y, M[1][0] * x + M[1][1] * y];
    const pts = [ap(0, 0), ap(1, 0), ap(1, 1), ap(0, 1)];
    const R = Math.max(1.3, ...pts.flat().map(Math.abs).filter(Number.isFinite).map(x => Math.min(x, 1e3) * 1.15));
    const f = fig({ x: [-R, R], y: [-R, R], square: true, height: 110 });
    f.poly([[0, 0], [1, 0], [1, 1], [0, 1]], { color: 'faint', alpha: 0.25 });
    f.poly(pts, { color: 'c2', alpha: 0.35, stroke: 'c2' });
    f.arrow(0, 0, ...ap(1, 0), { color: 'c4', width: 2 });
    f.arrow(0, 0, ...ap(0, 1), { color: 'c5', width: 2 });
  });
  MathViz.thumbnail(v => isMat(v) && (v.length !== 2 || v[0].length !== 2) && v.length <= 4 && v[0].length <= 4, (fig, M, host) => {
    host.innerHTML = matHTML(M.map(r => r.map(frac)));
    host.classList.add('thumb-mat');
  });

  /* ---------- ways of looking at a matrix or a vector (interpret) ---------- */
  const sq2 = M => isMat(M) && M.length === 2 && M[0].length === 2;
  const sh = x => MathViz.format(+(+x).toPrecision(4));
  MathViz.represent({
    name: 'matrix_as_map', label: 'A linear map: what it does to the plane', test: sq2,
    doc: 'x ↦ Ax sends the unit square to the parallelogram spanned by the columns, and the unit circle to an ellipse. |det A| is the area of the parallelogram; a negative det flips the orientation.',
    render(ctx, M) {
      const ap = ([x, y]) => [M[0][0] * x + M[0][1] * y, M[1][0] * x + M[1][1] * y];
      const circle = Array.from({ length: 121 }, (_, k) => [Math.cos(k * Math.PI / 60), Math.sin(k * Math.PI / 60)]);
      const img = circle.map(ap), R = Math.max(1.3, ...[...img, ap([1, 1])].flat().map(Math.abs).filter(Number.isFinite)) * 1.15;
      const fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true });
      for (let i = -3; i <= 3; i++) {
        fig.curve([ap([i / 2, -1.5]), ap([i / 2, 1.5])], { color: 'faint', width: 1, alpha: 0.6 });
        fig.curve([ap([-1.5, i / 2]), ap([1.5, i / 2])], { color: 'faint', width: 1, alpha: 0.6 });
      }
      fig.curve(circle, { color: 'ink', width: 1, alpha: 0.35, dash: [4, 3] });
      fig.curve(img, { color: 'c1', width: 2 });
      fig.poly([[0, 0], ap([1, 0]), ap([1, 1]), ap([0, 1])], { color: 'c2', alpha: 0.3, stroke: 'c2' });
      fig.arrow(0, 0, ...ap([1, 0]), { color: 'c4', width: 2.5 });
      fig.arrow(0, 0, ...ap([0, 1]), { color: 'c5', width: 2.5 });
      ctx.legend([{ label: 'A e₁ (first column)', color: 'c4' }, { label: 'A e₂ (second column)', color: 'c5' }, { label: 'image of the unit square', color: 'c2' }, { label: 'image of the unit circle', color: 'c1' }]);
      const d = det(M);
      ctx.note(`det A = ${sh(d)}: ${d === 0 ? 'the plane is squashed onto a line (or a point), so A is not invertible' : `areas are multiplied by ${sh(Math.abs(d))}${d < 0 ? ', and the orientation is reversed' : ''}`}. The lines show where the grid lines go: they stay straight, parallel and evenly spaced.`);
    },
  });
  MathViz.represent({
    name: 'matrix_eigen', label: 'Eigenvectors: the directions it only stretches', test: sq2,
    doc: 'An eigenvector v keeps its direction: Av = λv. In a basis of eigenvectors (when there is one) A is diagonal.',
    render(ctx, M) {
      const [[a, b], [c, d]] = M, tr = a + d, dt = a * d - b * c, disc = tr * tr / 4 - dt;
      const fig = ctx.figure({ x: [-2.2, 2.2], y: [-2.2, 2.2], square: true });
      const ap = ([x, y]) => [a * x + b * y, c * x + d * y];
      for (let k = 0; k < 24; k++) { const t = k * Math.PI / 12, v = [Math.cos(t), Math.sin(t)], w = ap(v), s = Math.max(1, Math.hypot(...w)); fig.arrow(v[0], v[1], v[0] + 0.5 * w[0] / s, v[1] + 0.5 * w[1] / s, { color: 'faint', width: 1 }); }
      if (disc < -1e-12) {
        const re = tr / 2, im = Math.sqrt(-disc);
        ctx.note(`No real eigenvectors: the eigenvalues are ${sh(re)} ± ${sh(im)}i. A turns every direction (by about ${sh(Math.atan2(im, re) * 180 / Math.PI)}° in suitable coordinates) and scales by ${sh(Math.sqrt(dt))}.`);
        return;
      }
      const ls = disc < 1e-12 ? [tr / 2] : [tr / 2 + Math.sqrt(disc), tr / 2 - Math.sqrt(disc)];
      const rows = [];
      ls.forEach((l, i) => {
        // A kernel vector of A − λI.
        let v = Math.abs(b) > 1e-12 || Math.abs(a - l) > 1e-12 ? [b, l - a] : [l - d, c];
        if (Math.hypot(...v) < 1e-12) v = i ? [0, 1] : [1, 0];
        const s = Math.hypot(...v); v = v.map(x => x / s);
        fig.curve([[-3 * v[0], -3 * v[1]], [3 * v[0], 3 * v[1]]], { color: i ? 'c3' : 'c2', width: 1.5, dash: [5, 3] });
        fig.arrow(0, 0, v[0], v[1], { color: i ? 'c3' : 'c2', width: 2.5 });
        fig.arrow(0, 0, l * v[0], l * v[1], { color: i ? 'c3' : 'c2', width: 1.2, alpha: 0.6 });
        rows.push([`λ${i + 1} = ${sh(l)}`, `(${v.map(sh).join(', ')})`, `A v = ${sh(l)}·v`]);
      });
      ctx.table(['eigenvalue', 'eigenvector v', ''], rows);
      ctx.note(disc < 1e-12 && Math.abs(b) + Math.abs(c) > 1e-12 ? 'A repeated eigenvalue with one eigenvector: A is not diagonalizable (a shear).' : 'The grey arrows show where A pushes the points of the unit circle; along the dashed lines it only stretches.');
    },
  });
  MathViz.represent({
    name: 'quadratic_form', label: 'A quadratic form: q(x) = xᵀAx', test: M => sq2(M) && Math.abs(M[0][1] - M[1][0]) < 1e-12,
    doc: 'A symmetric matrix is also a function q(x) = xᵀAx. Its level curves are ellipses (definite), hyperbolas (indefinite) or lines (semidefinite), with axes along the eigenvectors.',
    render(ctx, M) {
      const q = (x, y) => M[0][0] * x * x + 2 * M[0][1] * x * y + M[1][1] * y * y;
      const fig = ctx.figure({ x: [-2, 2], y: [-2, 2], square: true });
      const vals = [];
      for (let i = 0; i <= 20; i++) for (let j = 0; j <= 20; j++) vals.push(Math.abs(q(-2 + i / 5, -2 + j / 5)));
      const st = Math.max(...vals) / 10 || 1;
      fig.raster({ x: [-2, 2], y: [-2, 2], nx: 180, ny: 180, smooth: false, value: (x, y) => Math.floor(q(x, y) / st), color: (v, th) => th.rgba(v >= 0 ? 'c2' : 'c3', 0.08 + 0.05 * (Math.abs(v) % 2)) });
      const ev = [(M[0][0] + M[1][1]) / 2 + Math.hypot((M[0][0] - M[1][1]) / 2, M[0][1]), (M[0][0] + M[1][1]) / 2 - Math.hypot((M[0][0] - M[1][1]) / 2, M[0][1])];
      const kind = ev.every(l => l > 1e-12) ? 'positive definite: q > 0 away from 0, the level curves are ellipses' : ev.every(l => l < -1e-12) ? 'negative definite: q < 0 away from 0' : ev.some(l => l > 1e-12) && ev.some(l => l < -1e-12) ? 'indefinite: q takes both signs, the level curves are hyperbolas' : 'semidefinite: q vanishes along a line';
      ctx.legend([{ label: 'q > 0 (bands of equal width in q)', color: 'c2' }, { label: 'q < 0', color: 'c3' }]);
      ctx.note(`q(x, y) = ${sh(M[0][0])}x² + ${sh(2 * M[0][1])}xy + ${sh(M[1][1])}y². Eigenvalues ${ev.map(sh).join(' and ')}: ${kind}.`);
    },
  });
  MathViz.represent({
    name: 'matrix_rref', label: 'Row reduction: rank, pivots and kernel', test: M => isMat(M) && M.length <= 6 && M[0].length <= 6,
    doc: 'Row operations don\'t change the solutions of Ax = 0. The reduced row echelon form shows the rank (the number of pivots) and a basis of the kernel (one vector per free column).',
    render(ctx, M) {
      const core = rrefCore(asMat(M, 'interpret')), K = kernelBasis(M);
      ctx.html(`<div class="mat-pair">${matHTML(M.map(r => r.map(frac)))}<span class="mat-arrow">→</span>${matHTML(core.R.map(r => r.map(frac)), { pivots: core.pivots.map((c, i) => [i, c]) })}</div>`);
      ctx.note(`rank ${core.pivots.length}, pivots in column${core.pivots.length === 1 ? '' : 's'} ${core.pivots.map(c => c + 1).join(', ') || 'none'}; ${K.length ? `kernel spanned by ${K.map(v => '(' + v.map(frac).join(', ') + ')').join(', ')}` : 'the kernel is {0}'}.${M.length === M[0].length ? ` det = ${frac(core.det)}.` : ''}`);
    },
  });
  MathViz.represent({
    name: 'vector', label: 'A vector: an arrow, its length and direction', test: v => isVec(v) && (v.length === 2 || v.length === 3),
    doc: 'A point of ℝ² or ℝ³ is also an arrow from 0: its length is |v| and its direction is v/|v| (angles in polar or spherical coordinates).',
    render(ctx, v) {
      const r = Math.hypot(...v);
      if (v.length === 2) {
        const R = Math.max(1, r) * 1.3, fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true });
        fig.arrow(0, 0, v[0], v[1], { color: 'c1', width: 2.5 });
        fig.seg(v[0], 0, v[0], v[1], { color: 'faint', dash: [3, 3] }); fig.seg(0, v[1], v[0], v[1], { color: 'faint', dash: [3, 3] });
        fig.curve(Array.from({ length: 41 }, (_, k) => { const t = Math.atan2(v[1], v[0]) * k / 40; return [0.25 * R * Math.cos(t), 0.25 * R * Math.sin(t)]; }), { color: 'c2', width: 1.5 });
        ctx.note(`|v| = ${sh(r)}, angle θ = ${sh(Math.atan2(v[1], v[0]))} rad = ${sh(Math.atan2(v[1], v[0]) * 180 / Math.PI)}°: v = ${sh(r)}·(cos θ, sin θ).`);
      } else {
        const fig = ctx.figure3d({ equal: true });
        fig.arrow([0, 0, 0], v, { color: 'c1', width: 2.5 });
        fig.seg([0, 0, 0], [v[0], v[1], 0], { color: 'faint' }); fig.seg([v[0], v[1], 0], v, { color: 'faint' });
        ctx.note(`|v| = ${sh(r)}; spherical coordinates: θ = ${sh(Math.atan2(v[1], v[0]))} (around the z-axis), φ = ${sh(Math.acos(r ? v[2] / r : 1))} (from the z-axis).`);
      }
    },
  });

  MathViz.define({
    name: 'linalg',
    description: 'Matrices as lists of rows: products, powers, det, inv, rref with every step (exact fractions), rank, kernel, image and spans as sets you can quantify over, eigenvalues of any size, characteristic polynomials, Gram–Schmidt, example matrices, and views of 2×2 and 3×3 matrices acting on the plane and on space.',
    types: [
      {
        name: 'matrix',
        test: isMat,
        ops: {
          '+': (a, b) => { need(isMat(a) && isMat(b) && a.length === b.length && a[0].length === b[0].length, 'Matrices add to matrices of the same size.'); return a.map((r, i) => vadd(r, b[i])); },
          '-': (a, b) => { need(isMat(a) && isMat(b) && a.length === b.length && a[0].length === b[0].length, 'Matrices subtract from matrices of the same size.'); return a.map((r, i) => vsub(r, b[i])); },
          '*': (a, b) => {
            if (isMat(a) && isMat(b)) return matmul(a, b);
            if (isMat(a) && isVec(b)) return matvec(a, b);
            if (typeof a === 'number') return b.map(r => r.map(x => a * x));
            if (typeof b === 'number') return a.map(r => r.map(x => x * b));
            throw MathViz.error('A matrix can be multiplied by a number, a vector or another matrix.');
          },
          '/': (a, b) => { need(typeof b === 'number', 'A matrix can be divided by a number.'); return a.map(r => r.map(x => x / b)); },
          '^': (a, k) => {
            need(Number.isInteger(k) && a.length === a[0].length, 'Matrix powers need a square matrix and a whole-number exponent.');
            let r = identity(a.length);
            const base = k < 0 ? inv(a) : a;
            for (let i = 0; i < Math.abs(k); i++) r = matmul(r, base);
            return r;
          },
          neg: a => a.map(r => r.map(x => -x)),
          '=': (a, b) => isMat(a) && isMat(b) && a.length === b.length && a[0].length === b[0].length &&
            a.every((r, i) => r.every((x, j) => Math.abs(x - b[i][j]) <= 1e-9 * Math.max(1, Math.abs(x), Math.abs(b[i][j])))),
          format: a => (a.label && !a.label.startsWith('[') ? a.label + ' ' : '') + '[' + a.map(r => '[' + r.map(frac).join(', ') + ']').join(', ') + ']',
        },
      },
    ],
    functions: {
      dot, norm, det, inv, identity, transpose, rref, rank, charpoly, eigenvalues, eigenspace, diagonalizable, polyeval,
      zeros: { doc: 'zeros(m, n): the m×n zero matrix; zeros(n) is n×n.', fn: zeros },
      sym_eigenvalues: { doc: 'sym_eigenvalues(A): the eigenvalues of a symmetric matrix, largest first, by Jacobi rotations (accurate even for wildly scaled matrices).', fn: A => { square(A, 'sym_eigenvalues'); need(A.every((r, i) => r.every((x, j) => Math.abs(x - A[j][i]) <= 1e-9 * Math.max(1, Math.abs(x)))), 'sym_eigenvalues expects a symmetric matrix.'); return symEigs(A); } },
      leading_minors: { doc: 'leading_minors(A): the determinants of the top-left 1×1, 2×2, …, n×n blocks of a square matrix A. A symmetric A is positive definite exactly when all are > 0 (Sylvester).', fn: A => { square(A, 'leading_minors'); return A.map((_, k) => det(A.slice(0, k + 1).map(r => r.slice(0, k + 1)))); } },
      opnorm: { doc: 'opnorm(A, p): the operator norm sup{‖Ax‖ₚ : ‖x‖ₚ ≤ 1}, the most A stretches a vector (Definition 6.22); p = 2 if left out. Exact formulas for p = 1, 2 and inf.', fn: opnorm },
      fnorm: { doc: 'fnorm(A): the Frobenius norm √(Σ aᵢⱼ²), the length of A as a vector of entries.', fn: A => Math.sqrt(asMat(A, 'fnorm').flat().reduce((s, x) => s + x * x, 0)) },
      trace: A => { square(A, 'trace'); return A.reduce((s, r, i) => s + r[i], 0); },
      nullity: { doc: 'nullity(A): the dimension of the kernel of A.', fn: A => kernelBasis(asMat(A, 'nullity')).length },
      nrows: { doc: 'nrows(A): the number of rows.', fn: A => asMat(A, 'nrows').length },
      ncols: { doc: 'ncols(A): the number of columns.', fn: A => asMat(A, 'ncols')[0].length },
      col: { doc: 'col(A, j): the j-th column of A (from 1).', fn: (A, j) => { asMat(A, 'col'); need(Number.isInteger(j) && j >= 1 && j <= A[0].length, `A has columns 1 to ${A[0].length}.`); return A.map(r => r[j - 1]); } },
      row: { doc: 'row(A, i): the i-th row of A (from 1).', fn: (A, i) => { asMat(A, 'row'); need(Number.isInteger(i) && i >= 1 && i <= A.length, `A has rows 1 to ${A.length}.`); return A[i - 1].slice(); } },
      columns: { doc: 'columns(v₁, …, vₖ): the matrix with these vectors as its columns.', fn: (...vs) => { if (vs.length === 1 && vs[0].every && vs[0].every(isVec)) vs = vs[0]; need(vs.every(isVec) && vs.every(v => v.length === vs[0].length), 'columns takes vectors of the same length.'); return vs[0].map((_, i) => vs.map(v => v[i])); } },
      diag: { doc: 'diag(d₁, …, dₙ): the diagonal matrix with these entries.', fn: (...ds) => { if (ds.length === 1 && isVec(ds[0])) ds = ds[0]; return ds.map((d, i) => ds.map((_, j) => i === j ? d : 0)); } },
      rotation: { doc: 'rotation(θ): the 2×2 matrix of the rotation by θ.', fn: t => [[Math.cos(t), -Math.sin(t)], [Math.sin(t), Math.cos(t)]] },
      outer: { doc: 'outer(u, v): the matrix u vᵀ.', fn: (u, v) => { need(isVec(u) && isVec(v), 'outer expects two vectors.'); return u.map(a => v.map(b => a * b)); } },
      cross: (a, b) => {
        need(isVec(a) && isVec(b) && a.length === 3 && b.length === 3, 'cross expects two vectors of length 3.');
        return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
      },
      solve: { doc: 'solve(A, b): a solution x of Ax = b, or undefined if there is none. See solutions(A, b) for all of them.', fn: (A, b) => { const s = solveAll(A, b); return s ? s.x : A[0].map(() => NaN); } },
      solutions: { doc: 'solutions(A, b): the set of all solutions of Ax = b: a particular solution plus the kernel, or the empty set.', fn: (A, b) => { const s = solveAll(A, b); return s ? subspace(s.kernel, A[0].length, { offset: s.x }) : MathViz.finite([], { label: '∅ (no solutions)' }); } },
      kernel: { doc: 'kernel(A): the null space {x | Ax = 0}, as a set you can quantify over or draw.', fn: kernel },
      image: { doc: 'image(A): the column space of A, as a set.', fn: image },
      rowspace: { doc: 'rowspace(A): the span of the rows of A.', fn: rowspace },
      dimension: { doc: 'dimension(S): the dimension of a subspace.', fn: S => asSub(S, 'dimension').k },
      basis: { doc: 'basis(S): a basis of a subspace, as a list of vectors.', fn: S => asSub(S, 'basis').basis.map(v => v.slice()) },
      proj: { doc: 'proj(v, S): the orthogonal projection of v onto a subspace S (or onto the line through a vector S).', fn: (v, S) => {
        need(isVec(v), 'proj(v, S) projects a vector v.');
        if (isVec(S)) S = subspace([S], S.length);
        asSub(S, 'proj');
        const w = vsub(v, S.offset);
        return S.ortho.reduce((acc, q) => vadd(acc, vscale(dot(w, q), q)), S.offset.slice());
      } },
      orth_complement: { doc: 'orth_complement(S): the vectors orthogonal to every vector of the subspace S.', fn: S => { asSub(S, 'orth_complement'); return S.k ? kernel(S.basis) : subspace(identity(S.n), S.n); } },
      gram_schmidt: { doc: 'gram_schmidt(v₁, …, vₖ): an orthonormal list with the same span, by Gram–Schmidt.', fn: (...vs) => { if (vs.length === 1 && vs[0].every && vs[0].every(isVec)) vs = vs[0]; need(vs.every(isVec), 'gram_schmidt takes vectors.'); return gramSchmidt(vs); } },
      independent: { doc: 'independent(v₁, …, vₖ): whether the vectors are linearly independent.', fn: (...vs) => { if (vs.length === 1 && vs[0].every && vs[0].every(isVec)) vs = vs[0]; need(vs.every(isVec), 'independent takes vectors.'); return rank(vs) === vs.length; } },
    },
    constants: {},
    spaces: {
      Span: { doc: 'Span(v₁, …, vₖ): all linear combinations of the vectors, as a set.', fn: Span },
      Matrices: { doc: 'Matrices(n): example n×n matrices (n = 2 or 3): identity, rotations, shears, projections, nilpotent, singular, symmetric, Jordan blocks… Wilder ones (nearly singular, badly scaled) with "Try wilder examples".', fn: Matrices },
      Mat: { doc: 'Mat(m, n): all m×n matrices (Mat(n) for square), sampled: simple named ones first, then random integer and real ones.', fn: Mat },
    },
    views: {
      operator_norm: {
        doc: 'operator_norm(A, p) maps the unit ball of the p-norm (p = 2 if left out) by a 2×2 matrix A and draws the smallest p-ball around the image: its radius is ‖A‖, reached at the vector marked (Definition 6.22). Every x then has ‖Ax‖ ≤ ‖A‖·‖x‖.',
        render(ctx, A, p = 2) {
          need(isMat(A) && A.length === 2 && A[0].length === 2, 'operator_norm draws a 2×2 matrix, such as [[2, 1], [0, 1]].');
          const ball = (r, m = 720) => Array.from({ length: m }, (_, k) => { const a = 2 * Math.PI * k / m, v = [Math.cos(a), Math.sin(a)], L = vpnorm(v, p); return [r * v[0] / L, r * v[1] / L]; });
          const unit = ball(1), img = unit.map(v => matvec(A, v));
          let bi = 0;
          img.forEach((w, i) => { if (vpnorm(w, p) > vpnorm(img[bi], p)) bi = i; });
          const N = opnorm(A, p), R = 1.15 * Math.max(1, N);
          const fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true });
          fig.poly(ball(N), { color: 'c3', alpha: 0.06, stroke: 'c3' });
          fig.poly(unit, { color: 'c1', alpha: 0.18, stroke: 'c1' });
          fig.poly(img, { color: 'c2', alpha: 0.25, stroke: 'c2' });
          fig.arrow(0, 0, ...unit[bi], { color: 'c1', width: 2.5 });
          fig.arrow(0, 0, ...img[bi], { color: 'c2', width: 2.5 });
          const pn = p === Infinity ? '∞' : MathViz.format(p);
          ctx.legend([{ label: `unit ball of the ${pn}-norm`, color: 'c1' }, { label: 'its image under A', color: 'c2' }, { label: `the ${pn}-ball of radius ‖A‖`, color: 'c3' }]);
          const amax = Math.max(...A.flat().map(Math.abs));
          ctx.note(`‖A‖ = ${frac(+N.toPrecision(6))} for the ${pn}-norm, reached at x = (${unit[bi].map(x => frac(+x.toPrecision(4))).join(', ')}).${p === 2 ? ` Example 6.21 bounds it by √(nm)·max|aᵢₖ| = 2·${frac(amax)} = ${frac(2 * amax)}.` : ''}`);
        },
      },
      rref_steps: {
        doc: 'rref_steps(A) row-reduces A one operation at a time, in exact fractions, and reads off the rank, the pivots and a basis of the kernel. rref_steps(A, b) reduces the augmented matrix [A | b] and solves Ax = b.',
        render(ctx, A, b) {
          asMat(A, 'rref_steps');
          const aug = b !== undefined;
          if (aug) need(isVec(b) && b.length === A.length, `b needs ${A.length} entries, one per row of A.`);
          const M = aug ? A.map((r, i) => [...r, b[i]]) : A;
          const res = rrefCore(M, { steps: true, cols: A[0].length });
          const start = M.map(r => r.map(frac));
          let html = '<div class="rref-steps"><div class="rref-step"><div class="rref-op">start</div>' + matHTML(start, { aug: aug ? 1 : 0 }) + '</div>';
          for (const s of res.steps) html += `<div class="rref-arrow">→</div><div class="rref-step"><div class="rref-op">${s.text}</div>${matHTML(s.M, { aug: aug ? 1 : 0, pivots: [] })}</div>`;
          html += '</div>';
          ctx.html(html);
          const final = res.R.map(r => r.map(frac));
          ctx.html('<div class="rref-final"><span>Reduced row echelon form, pivots marked:</span>' + matHTML(final, { aug: aug ? 1 : 0, pivots: res.pivots.map((c, i) => [i, c]) }) + '</div>');
          const n = A[0].length;
          const kb = kernelBasis(A);
          ctx.note(`Rank ${res.pivots.length} (pivots in column${res.pivots.length === 1 ? '' : 's'} ${res.pivots.map(c => c + 1).join(', ') || 'none'}), so the kernel has dimension ${n - res.pivots.length}${kb.length ? ': it is spanned by ' + kb.map(fmtVec).join(', ') : ''}.${res.exact ? ' All arithmetic was exact.' : ' Some entries are not simple fractions, so this used floating point.'}`);
          if (aug) {
            const s = solveAll(A, b);
            ctx.note(!s ? 'A row reads 0 = (nonzero), so Ax = b has no solution.'
              : kb.length ? `Solutions: x = ${fmtVec(s.x)} + ${kb.map((v, i) => `t${'₁₂₃₄₅₆₇₈₉'[i] || i + 1}·${fmtVec(v)}`).join(' + ')}.`
              : `The unique solution is x = ${fmtVec(s.x)}.`);
          }
        },
      },
      transform: {
        doc: 'transform(M) shows how a 2×2 matrix moves the grid, the unit square and the unit circle, or how a 3×3 matrix moves the unit cube. Drag t to blend from the identity to M.',
        render(ctx, M) {
          need(isMat(M) && M.length === M[0].length && (M.length === 2 || M.length === 3), 'transform expects a 2×2 or 3×3 matrix, such as [[2, 1], [1, 3]].');
          const t = ctx.param('t', { min: 0, max: 1, step: 0.01, value: 1 });
          const n = M.length;
          const A = M.map((r, i) => r.map((x, j) => (i === j ? 1 : 0) * (1 - t) + x * t));
          const d = det(A);
          if (n === 3) {
            const ap = p => matvec(A, p);
            const fig = ctx.figure3d({ equal: true });
            const cube = [[0, 0, 0], [1, 0, 0], [1, 1, 0], [0, 1, 0], [0, 0, 1], [1, 0, 1], [1, 1, 1], [0, 1, 1]];
            const faces = [[0, 1, 2, 3], [4, 5, 6, 7], [0, 1, 5, 4], [2, 3, 7, 6], [1, 2, 6, 5], [0, 3, 7, 4]];
            for (const f of faces) fig.poly(f.map(i => cube[i]), { color: 'faint', alpha: 0.12, stroke: 'faint' });
            for (const f of faces) fig.poly(f.map(i => ap(cube[i])), { color: 'c2', alpha: 0.3, stroke: 'c2' });
            ['c4', 'c5', 'c6'].forEach((c, i) => fig.arrow([0, 0, 0], ap(identity(3)[i]), { color: c, width: 2.5 }));
            ctx.legend([{ label: 'image of e₁', color: 'c4' }, { label: 'image of e₂', color: 'c5' }, { label: 'image of e₃', color: 'c6' }, { label: 'image of the unit cube', color: 'c2' }]);
            ctx.note(`det = ${frac(d)}: volumes are scaled by ${frac(Math.abs(d))}${d < 0 ? ' and orientation flips' : ''}${Math.abs(d) < 1e-12 ? ' (the cube is flattened)' : ''}.`);
            return;
          }
          const ap = (x, y) => [A[0][0] * x + A[0][1] * y, A[1][0] * x + A[1][1] * y];
          const R = 1.1 * Math.max(2, ...[[2, 2], [2, -2], [-2, 2], [-2, -2]].flatMap(([x, y]) =>
            [Math.abs(M[0][0] * x + M[0][1] * y), Math.abs(M[1][0] * x + M[1][1] * y)]));
          const fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true });
          for (let k = -2; k <= 2; k++) {
            fig.seg(k, -2, k, 2, { color: 'faint', width: 1, alpha: 0.6 });
            fig.seg(-2, k, 2, k, { color: 'faint', width: 1, alpha: 0.6 });
          }
          for (let k = -2; k <= 2; k++) {
            fig.seg(...ap(k, -2), ...ap(k, 2), { color: 'c1', width: 1.2, alpha: 0.5 });
            fig.seg(...ap(-2, k), ...ap(2, k), { color: 'c1', width: 1.2, alpha: 0.5 });
          }
          fig.poly([ap(0, 0), ap(1, 0), ap(1, 1), ap(0, 1)], { color: 'c2', alpha: 0.25, stroke: 'c2' });
          fig.curve(Array.from({ length: 241 }, (_, k) => ap(Math.cos(k / 240 * 2 * Math.PI), Math.sin(k / 240 * 2 * Math.PI))), { color: 'c3', width: 2 });
          fig.arrow(0, 0, ...ap(1, 0), { color: 'c4', width: 2.5 });
          fig.arrow(0, 0, ...ap(0, 1), { color: 'c5', width: 2.5 });
          ctx.legend([
            { label: 'image of e₁', color: 'c4' }, { label: 'image of e₂', color: 'c5' },
            { label: 'unit square', color: 'c2' }, { label: 'unit circle', color: 'c3' },
          ]);
          ctx.note(`det = ${frac(d)}: areas are scaled by ${frac(Math.abs(d))}${d < 0 ? ' and orientation flips' : ''}.`);
        },
      },
      eigen: {
        doc: 'eigen(M) for a 2×2 matrix: a vector v going round the unit circle and its image Mv. Where they line up, v is an eigenvector. Drag θ to move v.',
        render(ctx, M) {
          need(isMat(M) && M.length === 2 && M[0].length === 2, 'eigen expects a 2×2 matrix.');
          const th = ctx.param('θ', { min: 0, max: 6.283, step: 0.01, value: 0.6 });
          const ap = (x, y) => [M[0][0] * x + M[0][1] * y, M[1][0] * x + M[1][1] * y];
          const ell = Array.from({ length: 241 }, (_, k) => ap(Math.cos(k / 240 * 2 * Math.PI), Math.sin(k / 240 * 2 * Math.PI)));
          const R = 1.15 * Math.max(1.2, ...ell.flat().map(Math.abs));
          const fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true });
          fig.curve(Array.from({ length: 241 }, (_, k) => [Math.cos(k / 240 * 2 * Math.PI), Math.sin(k / 240 * 2 * Math.PI)]), { color: 'faint', width: 1.2 });
          fig.curve(ell, { color: 'c3', width: 1.6, alpha: 0.7 });
          const ls = eigenvalues(M);
          const lines = [];
          for (const l of [...new Set(ls.map(x => +x.toPrecision(12)))]) {
            const E = eigenspace(M, l);
            for (const b of E.basis) {
              const u = vscale(1 / norm(b), b);
              fig.seg(-R * u[0], -R * u[1], R * u[0], R * u[1], { color: 'c2', width: 1.2, dash: [6, 4] });
              lines.push(`λ = ${frac(l)} along ${fmtVec(b)}`);
            }
          }
          const v = [Math.cos(th), Math.sin(th)], w = ap(...v);
          fig.arrow(0, 0, ...v, { color: 'c4', width: 2.5 });
          fig.arrow(0, 0, ...w, { color: 'c5', width: 2.5 });
          const cr = v[0] * w[1] - v[1] * w[0];
          ctx.legend([{ label: 'v', color: 'c4' }, { label: 'Mv', color: 'c5' }, { label: 'image of the unit circle', color: 'c3' }, { label: 'eigenvector lines', color: 'c2' }]);
          ctx.note(lines.length ? `Eigenvalues and eigenvectors: ${lines.join('; ')}. ${Math.abs(cr) < 0.02 * Math.max(1, norm(w)) ? 'Right now v and Mv line up: v is (nearly) an eigenvector.' : ''}`
            : 'No real eigenvalues: Mv never lines up with v, as for a rotation.');
        },
      },
      subspace: {
        doc: 'subspace(S, …) draws subspaces (or solution sets) of ℝ² or ℝ³: lines and planes with their basis vectors, as in subspace(kernel(A), image(A)).',
        render(ctx, ...Ss) {
          need(Ss.length && Ss.every(S => S && S.kind === 'subspace'), 'subspace(S, …) draws subspaces, such as Span((1, 2)), kernel(A) or solutions(A, b).');
          const n = Ss[0].n;
          need(Ss.every(S => S.n === n) && (n === 2 || n === 3), 'subspace draws subspaces of ℝ² or ℝ³, all in the same space.');
          const L = 2.5;
          const leg = [];
          if (n === 2) {
            const fig = ctx.figure({ x: [-L, L], y: [-L, L], square: true });
            Ss.forEach((S, i) => {
              const c = 'c' + (i % 6 + 1), o = S.offset;
              if (S.k === 0) fig.points([o], { color: c, r: 5 });
              else if (S.k === 1) { const u = S.ortho[0]; fig.seg(o[0] - 10 * u[0], o[1] - 10 * u[1], o[0] + 10 * u[0], o[1] + 10 * u[1], { color: c, width: 2.5, alpha: 0.8 }); }
              else fig.rect(-L, -L, L, L, { color: c, alpha: 0.15 });
              S.basis.forEach(b => { const k = Math.min(1, 0.9 * L / Math.max(...b.map(Math.abs))); fig.arrow(o[0], o[1], o[0] + k * b[0], o[1] + k * b[1], { color: c, width: 2 }); });
              leg.push({ label: `${S.describe()} (dimension ${S.k})`, color: c });
            });
          } else {
            const fig = ctx.figure3d({ box: [[-L, L], [-L, L], [-L, L]] });
            // Clip a convex polygon to the box [−L, L]³ (one face at a time).
            const clip = poly => {
              for (let ax = 0; ax < 3; ax++) for (const s of [1, -1]) {
                const inside = p => s * p[ax] <= L + 1e-12;
                const out = [];
                poly.forEach((p, i) => {
                  const q = poly[(i + 1) % poly.length];
                  if (inside(p)) out.push(p);
                  if (inside(p) !== inside(q)) { const t = (s * L - p[ax]) / (q[ax] - p[ax]); out.push(p.map((x, k) => x + t * (q[k] - x))); }
                });
                poly = out;
                if (!poly.length) return poly;
              }
              return poly;
            };
            // Arrows for basis vectors, shortened to fit in the box (the direction is what matters).
            const fit = b => vscale(Math.min(1, 0.9 * L / Math.max(...b.map(Math.abs))), b);
            Ss.forEach((S, i) => {
              const c = 'c' + (i % 6 + 1), o = S.offset;
              if (S.k === 0) fig.points([o], { color: c, r: 5 });
              else if (S.k === 1) {
                // The part of the line o + t·u inside the box.
                const u = S.ortho[0];
                let t0 = -Infinity, t1 = Infinity;
                for (let ax = 0; ax < 3; ax++) {
                  if (Math.abs(u[ax]) < 1e-12) { if (Math.abs(o[ax]) > L) t1 = -Infinity; continue; }
                  const a = (-L - o[ax]) / u[ax], b = (L - o[ax]) / u[ax];
                  t0 = Math.max(t0, Math.min(a, b)); t1 = Math.min(t1, Math.max(a, b));
                }
                if (t1 > t0) fig.seg(vadd(o, vscale(t0, u)), vadd(o, vscale(t1, u)), { color: c, width: 2.5 });
              } else if (S.k === 2) {
                const [u, v] = S.ortho, s = 4 * L;
                const patch = clip([[-s, -s], [s, -s], [s, s], [-s, s]].map(([a, b]) => vadd(o, vadd(vscale(a, u), vscale(b, v)))));
                if (patch.length >= 3) fig.poly(patch, { color: c, alpha: 0.3, stroke: c });
              } else fig.points(S.sample(400), { color: c, r: 1.5, alpha: 0.3, track: false });
              S.basis.forEach(b => fig.arrow(o, vadd(o, fit(b)), { color: c, width: 2.5, track: false }));
              leg.push({ label: `${S.describe()} (dimension ${S.k})`, color: c });
            });
          }
          ctx.legend(leg);
        },
      },
    },
    notation: `
# A is symmetric: it equals its transpose.
# examples: A in Matrices(3)
def symmetric(A) := transpose(A) = A

# A is positive definite: symmetric with xᵀAx > 0 for every x ≠ 0, which is the same as every
# eigenvalue being positive (Definition 9.13).
# examples: A in Matrices(2)
def positive_definite(A) := symmetric(A) and forall λ in sym_eigenvalues(A): λ > 0

# A is negative definite: −A is positive definite.
# examples: A in Matrices(2)
def negative_definite(A) := positive_definite(-1 * A)

# A is indefinite: symmetric with a positive and a negative eigenvalue (xᵀAx takes both signs).
# examples: A in Matrices(2)
def indefinite(A) := symmetric(A) and (exists λ in sym_eigenvalues(A): λ > 0) and (exists λ in sym_eigenvalues(A): λ < 0)

# Sylvester's criterion: a symmetric matrix is positive definite exactly when its leading minors are positive.
lemma sylvester: forall A in Mat(3): positive_definite(A + transpose(A)) <-> (forall m in leading_minors(A + transpose(A)): m > 0)

# For a positive definite A the quadratic form is positive away from 0.
lemma quadratic_form_positive: forall A in Mat(2), x in [-1, 1]^2: positive_definite(A + transpose(A)) and |x| > 0.1 -> dot(x, (A + transpose(A)) * x) > 0

# Q is orthogonal: its columns are orthonormal, so QᵀQ = I.
# examples: A in Matrices(2)
def orthogonal_matrix(A) := transpose(A) * A = identity(nrows(A))

# A is invertible, four ways: its determinant is not zero; it has full rank; its kernel is {0}; its columns are linearly independent.
# examples: A in Matrices(3)
concept invertible(A) where
  determinant: det(A) != 0
  rank: rank(A) = nrows(A)
  kernel: nullity(A) = 0
  columns: independent(columns(A))

# A symmetric 2×2 matrix is positive definite, three ways: all eigenvalues are positive; all leading minors are positive (Sylvester's criterion); xᵀAx > 0 for every x ≠ 0 (tried on a grid of integer vectors).
# examples: A in {[[2, 1], [1, 2]], [[1, 2], [2, 1]], [[1, 0], [0, 0]], [[3, 0], [0, 1]], [[-1, 0], [0, -2]], [[2, -1], [-1, 2]], [[1, 1], [1, 1]], [[5, 4], [4, 5]]}
concept posdef(A) where
  eigenvalues: forall l in sym_eigenvalues(A): l > 0
  sylvester: forall m in leading_minors(A): m > 0
  quadratic_form: forall x in -3..3, y in -3..3: (x, y) = (0, 0) or dot((x, y), A * (x, y)) > 0

# A is nilpotent: some power of it is zero (for n×n, the n-th power is enough).
# examples: A in Matrices(3)
def nilpotent(A) := A^nrows(A) = zeros(nrows(A))

# λ is an eigenvalue of A: A − λI has a nonzero kernel.
def is_eigenvalue(λ, A) := dimension(eigenspace(A, λ)) > 0

# The determinant is multiplicative.
lemma det_product: forall A, B in Mat(3): det(A * B) = det(A) * det(B)

# Is the determinant additive? No.
conjecture det_sum: forall A, B in Mat(2): det(A + B) = det(A) + det(B)

# Do matrices commute? Not in general.
conjecture matrices_commute: forall A, B in Mat(2): A * B = B * A

# Rank–nullity: rank plus nullity is the number of columns.
lemma rank_nullity: forall A in Mat(3, 4): rank(A) + nullity(A) = 4

# The trace is cyclic: tr(AB) = tr(BA).
lemma trace_cyclic: forall A, B in Mat(3): trace(A * B) = trace(B * A)

# Cayley–Hamilton: every square matrix satisfies its characteristic polynomial. (Compared with the
# size of A³, since that is the scale of the rounding errors.)
lemma cayley_hamilton: forall A in Mat(3): fnorm(polyeval(charpoly(A), A)) <= 1e-9 * (1 + fnorm(A))^3

# The kernel really is sent to zero.
lemma kernel_to_zero: forall A in Matrices(3): forall v in kernel(A): A * v = (0, 0, 0)

# A real symmetric matrix has only real eigenvalues (all 3 of them, with multiplicity).
lemma symmetric_real_eigenvalues: forall A in Mat(3): len(eigenvalues(A + transpose(A))) = 3

# Every matrix is diagonalizable? Jordan blocks, nilpotent matrices and rotations say no.
conjecture all_diagonalizable: forall A in Matrices(3): diagonalizable(A)

# The rank of a product is at most the rank of each factor.
lemma rank_product: forall A, B in Mat(3): rank(A * B) <= min(rank(A), rank(B))
`,
  });
});
