MathVizLibrary(function geometry(MathViz) {
  const { lt, le, abs } = MathViz.ops;
  const point = (p, what) => {
    if (!Array.isArray(p) || p.length !== 2 || !p.every(Number.isFinite)) throw MathViz.error(`${what} must be a point of the plane such as (0, 0), not ${MathViz.format(p)}.`);
    return p;
  };
  const num = (x, what) => { if (typeof x !== 'number') throw MathViz.error(`${what} must be a number.`); return x; };
  const shape = (label, window, contains) => MathViz.space({ label, window, contains });
  const box = (c, r) => [[c[0] - r, c[0] + r], [c[1] - r, c[1] + r]];
  const fmt = MathViz.format;
  const cross = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
  const segDist = (p, a, b) => {
    const dx = b[0] - a[0], dy = b[1] - a[1], L2 = dx * dx + dy * dy;
    const t = L2 ? Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / L2)) : 0;
    return Math.hypot(p[0] - a[0] - t * dx, p[1] - a[1] - t * dy);
  };
  // Closed polygon: inside by the even-odd rule, or on an edge (within the usual tolerance).
  const inPolygon = (pts, p) => {
    if (!Array.isArray(p) || p.length !== 2) return false;
    let inside = false;
    for (let i = 0, j = pts.length - 1; i < pts.length; j = i++) {
      if (le(segDist(p, pts[j], pts[i]), 0)) return true;
      const [xi, yi] = pts[i], [xj, yj] = pts[j];
      if ((yi > p[1]) !== (yj > p[1]) && p[0] < (xj - xi) * (p[1] - yi) / (yj - yi) + xi) inside = !inside;
    }
    return inside;
  };
  const bboxOf = pts => {
    const xs = pts.map(p => p[0]), ys = pts.map(p => p[1]);
    const pad = 0.15 * Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys), 1e-6);
    return [[Math.min(...xs) - pad, Math.max(...xs) + pad], [Math.min(...ys) - pad, Math.max(...ys) + pad]];
  };
  const windowOf = S => { const w = MathViz.toDomain(S).window(); if (!w || typeof w[0] === 'number') throw MathViz.error('This needs a set of the plane.'); return w; };

  MathViz.define({
    name: 'geometry',
    description: 'Shapes of the plane as sets (disks, rectangles, triangles, polygons, half-planes, annuli, ellipses), area and diameter estimates, and convexity. Loaded automatically.',
    requires: ['catalog'],
    spaces: {
      Disk: { doc: 'Disk(c, r): the closed disk |p − c| ≤ r.', fn: (c, r) => { point(c, 'The center'); num(r, 'The radius'); return shape(`disk |p − ${fmt(c)}| ≤ ${fmt(r)}`, box(c, 1.2 * r), p => le(abs([p[0] - c[0], p[1] - c[1]]), r)); } },
      OpenDisk: { doc: 'OpenDisk(c, r): the open disk |p − c| < r.', fn: (c, r) => { point(c, 'The center'); num(r, 'The radius'); return shape(`disk |p − ${fmt(c)}| < ${fmt(r)}`, box(c, 1.2 * r), p => lt(abs([p[0] - c[0], p[1] - c[1]]), r)); } },
      Rect: { doc: 'Rect(x0, y0, x1, y1): the closed rectangle [x0, x1] × [y0, y1].', fn: (x0, y0, x1, y1) => shape(`[${fmt(x0)}, ${fmt(x1)}] × [${fmt(y0)}, ${fmt(y1)}]`, bboxOf([[x0, y0], [x1, y1]]), ([x, y]) => le(x0, x) && le(x, x1) && le(y0, y) && le(y, y1)) },
      OpenRect: { doc: 'OpenRect(x0, y0, x1, y1): the open rectangle (x0, x1) × (y0, y1).', fn: (x0, y0, x1, y1) => shape(`(${fmt(x0)}, ${fmt(x1)}) × (${fmt(y0)}, ${fmt(y1)})`, bboxOf([[x0, y0], [x1, y1]]), ([x, y]) => lt(x0, x) && lt(x, x1) && lt(y0, y) && lt(y, y1)) },
      Square: { doc: 'Square(c, s): the closed square with center c and side s.', fn: (c, s) => { point(c, 'The center'); const h = s / 2; return shape(`square of side ${fmt(s)} at ${fmt(c)}`, box(c, 0.6 * s), ([x, y]) => le(Math.abs(x - c[0]), h) && le(Math.abs(y - c[1]), h)); } },
      Triangle: { doc: 'Triangle(a, b, c): the closed triangle with corners a, b, c.', fn: (a, b, c) => {
        [a, b, c].forEach((p, i) => point(p, `Corner ${i + 1}`));
        const s = Math.sign(cross(a, b, c)) || 1;
        return shape(`triangle ${fmt(a)}, ${fmt(b)}, ${fmt(c)}`, bboxOf([a, b, c]), p => Array.isArray(p) && [[a, b], [b, c], [c, a]].every(([u, v]) => le(0, s * cross(u, v, p))));
      } },
      Polygon: { doc: 'Polygon(points): the closed polygon with these corners, as in Polygon([(0, 0), (2, 0), (1, 1)]).', fn: pts => {
        if (!Array.isArray(pts) || pts.length < 3) throw MathViz.error('A polygon needs a list of at least three corners.');
        pts.forEach((p, i) => point(p, `Corner ${i + 1}`));
        return shape(`polygon with ${pts.length} corners`, bboxOf(pts), p => inPolygon(pts, p));
      } },
      HalfPlane: { doc: 'HalfPlane(n, c): the closed half-plane n·p ≤ c.', fn: (n, c) => { point(n, 'The normal'); return shape(`half-plane ${fmt(n)}·p ≤ ${fmt(c)}`, [[-4, 4], [-4, 4]], p => le(n[0] * p[0] + n[1] * p[1], c)); } },
      OpenHalfPlane: { doc: 'OpenHalfPlane(n, c): the open half-plane n·p < c.', fn: (n, c) => { point(n, 'The normal'); return shape(`half-plane ${fmt(n)}·p < ${fmt(c)}`, [[-4, 4], [-4, 4]], p => lt(n[0] * p[0] + n[1] * p[1], c)); } },
      Annulus: { doc: 'Annulus(c, r, R): the open ring r < |p − c| < R.', fn: (c, r, R) => { point(c, 'The center'); return shape(`annulus ${fmt(r)} < |p − ${fmt(c)}| < ${fmt(R)}`, box(c, 1.2 * R), p => { const d = abs([p[0] - c[0], p[1] - c[1]]); return lt(r, d) && lt(d, R); }); } },
      Ellipse: { doc: 'Ellipse(c, a, b): the closed ellipse with center c and half-axes a (horizontal) and b (vertical).', fn: (c, a, b) => { point(c, 'The center'); return shape(`ellipse at ${fmt(c)} with half-axes ${fmt(a)}, ${fmt(b)}`, [[c[0] - 1.2 * a, c[0] + 1.2 * a], [c[1] - 1.2 * b, c[1] + 1.2 * b]], ([x, y]) => le(((x - c[0]) / a) ** 2 + ((y - c[1]) / b) ** 2, 1)); } },
      Point: { doc: 'Point(p): the set {p}.', fn: p => MathViz.finite([point(p, 'The point')], { label: `{${fmt(p)}}` }) },
    },
    functions: {
      area: { doc: 'area(S): the area of a set of the plane, counted on a 400 × 400 grid over its window.', fn: S => {
        S = MathViz.toDomain(S);
        const [[x0, x1], [y0, y1]] = windowOf(S), n = 400;
        let hits = 0;
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (S.contains([x0 + (i + 0.5) * (x1 - x0) / n, y0 + (j + 0.5) * (y1 - y0) / n])) hits++;
        return hits * (x1 - x0) * (y1 - y0) / (n * n);
      } },
      centroid: { doc: 'centroid(S): the center of mass of a set of the plane, from the same grid.', fn: S => {
        S = MathViz.toDomain(S);
        const [[x0, x1], [y0, y1]] = windowOf(S), n = 300;
        let sx = 0, sy = 0, c = 0;
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
          const p = [x0 + (i + 0.5) * (x1 - x0) / n, y0 + (j + 0.5) * (y1 - y0) / n];
          if (S.contains(p)) { sx += p[0]; sy += p[1]; c++; }
        }
        return c ? [sx / c, sy / c] : [NaN, NaN];
      } },
      diameter: { doc: 'diameter(S): the largest distance between two sampled points of S, boundary included.', fn: S => {
        const pts = MathViz.toDomain(S).sample(300);
        let best = 0;
        for (let i = 0; i < pts.length; i++) for (let j = i + 1; j < pts.length; j++) best = Math.max(best, abs(MathViz.ops.sub(pts[i], pts[j])));
        return best;
      } },
      dist_to: { doc: 'dist_to(p, S): the distance from p to the nearest sampled point of S.', fn: (p, S) => {
        const pts = MathViz.toDomain(S).sample(600);
        return pts.reduce((m, q) => Math.min(m, abs(MathViz.ops.sub(p, q))), Infinity);
      } },
    },
    notation: `
# S is convex: the segment between any two of its points stays in S.
# examples: S in Subsets(R^2)
def convex_set(S: Set) := forall x, y in S, t in [0, 1]: (1 - t)*x + t*y in S

# S is star-shaped around c: the segment from c to any point of S stays in S.
# examples: S in Subsets(R^2), c in {(0, 0)}
def star_shaped(S: Set, c) := forall x in S, t in [0, 1]: (1 - t)*c + t*x in S

# The intersection of two convex sets is convex.
lemma convex_intersection: forall A, B in Subsets(R^2): convex_set(A) and convex_set(B) -> convex_set(A ∩ B)

# The union of two convex sets need not be convex.
conjecture convex_union: forall A, B in Subsets(R^2): convex_set(A) and convex_set(B) -> convex_set(A ∪ B)
`,
  });
});
