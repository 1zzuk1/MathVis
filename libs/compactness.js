MathVizLibrary(function compactness(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const isVec = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');
  const short = x => fmt(+(+x).toPrecision(4));
  const pt = p => (typeof p === 'number' ? short(p) : '(' + p.map(short).join(', ') + ')');
  const precise = p => (typeof p === 'number' ? fmt(+p.toPrecision(10)) : '(' + p.map(x => fmt(+x.toPrecision(10))).join(', ') + ')');
  const dom = S => {
    let D = null;
    try { D = MathViz.toDomain(S); } catch (e) { D = null; }
    need(D && D.contains && D.window, 'Expected a set of the line or of ℝⁿ, such as Icc(0, 1) or {p in R^2 | |p| <= 1}.');
    return D;
  };
  // A set of the line has a window [a, b]; a set of the plane [[a, b], [c, d]].
  const dimOf = S => { const w = S.window(); return Array.isArray(w[0]) ? w.length : 1; };
  const sizeOf = S => { const w = S.window(); return Array.isArray(w[0]) ? Math.max(...w.map(([a, b]) => b - a)) : w[1] - w[0]; };
  const value = (f, x) => {
    try {
      const k = f.arity || f.length;
      const v = Array.isArray(x) && x.length > 1 && k === x.length ? f(...x) : f(x);
      return +v;
    } catch (e) { return NaN; }
  };
  const step = (p, u, s) => (typeof p === 'number' ? p + u * s : p.map((x, i) => x + u[i] * s));
  const dist = (p, q) => (typeof p === 'number' ? Math.abs(p - q) : Math.hypot(...p.map((x, i) => x - q[i])));
  const DIRS = { 1: [1, -1], 2: Array.from({ length: 16 }, (_, k) => [Math.cos(k * Math.PI / 8), Math.sin(k * Math.PI / 8)]) };
  const dirs = n => DIRS[n] || Array.from({ length: 2 * n }, (_, k) => Array.from({ length: n }, (__, i) => (i === k >> 1 ? (k & 1 ? -1 : 1) : 0)));
  const asPoint = x => (Array.isArray(x) ? x.map(Number) : +x);

  /* ---------- does f attain its supremum on S? ---------- */
  // Climb from the best samples, staying in S. A climb either stops at a point of S where f is
  // largest nearby, or gets stuck at the edge of S with f still rising outward. There the boundary
  // point b is found by bisection (with exact comparisons, as sets find their boundary): if b is in
  // S and f(b) is at least what the climb reached, the maximum is attained at b; otherwise the
  // supremum is only approached.
  function extremum(f, S, sign) {
    S = dom(S);
    MathViz.markInexact();
    const n = dimOf(S), size = sizeOf(S) || 1, D = dirs(n);
    const g = x => sign * value(f, x);
    const pool = S.sample(400).map(asPoint).concat(S.boundary().filter(b => b.inside).map(b => asPoint(b.p)))
      .filter(x => S.contains(x) && Number.isFinite(g(x)));
    need(pool.length, `No point of ${fmt(S)} gives f a value.`);
    pool.sort((a, b) => g(b) - g(a));
    const starts = [pool[0], ...pool.filter((_, i) => i && i % Math.max(1, Math.floor(pool.length / 6)) === 0).slice(0, 5)];
    let best = null;
    for (const s0 of starts) {
      let p = s0, v = g(p), h = size / 8, far = false;
      for (let it = 0; it < 4000 && h > 1e-13 * size; it++) {
        let moved = false;
        for (const u of D) {
          const q = step(p, u, h);
          if (!S.contains(q)) continue;
          const w = g(q);
          if (w > v) { p = q; v = w; moved = true; }
        }
        h = moved ? Math.min(2 * h, 1e6 * size) : h / 2;
        if (dist(p, s0) > 1e3 * size) { far = true; break; }
      }
      let r = { p, v, attained: true, far };
      if (far) r = { p, v: Infinity, attained: false, far };
      else {
        // Stuck at the edge of S? Then the boundary point b next to p is where f was heading.
        for (const u of D) {
          const q = step(p, u, 1e-7 * size);
          if (S.contains(q)) continue;
          let lo = p, hi = q;
          for (let k = 0; k < 80; k++) {
            const m = typeof lo === 'number' ? (lo + hi) / 2 : lo.map((x, i) => (x + hi[i]) / 2);
            if (MathViz.exact(() => S.contains(m))) lo = m; else hi = m;
          }
          const b = hi, back = typeof p === 'number' ? Math.sign(p - b) || -u : p.map((x, i) => x - b[i]);
          const bl = typeof back === 'number' ? 1 : Math.hypot(...back) || 1;
          const inward = d => step(b, typeof back === 'number' ? back : back.map(x => x / bl), d * size);
          // Is f rising towards b? Compare f a little further inside.
          const gIn = g(inward(1e-4));
          if (!(gIn < v)) continue;
          const gb = g(b), tol = 1e-7 * Math.max(1, Math.abs(v));
          if (S.contains(b) && gb >= v - tol) r = { p: b, v: gb, attained: true };
          else {
            // Not attained: the supremum is the limit towards b, perhaps infinite.
            const near = [1e-3, 1e-6, 1e-9, 1e-12].map(d => g(inward(d)));
            const unbounded = near[3] > 1e6 * Math.max(1, Math.abs(near[0])) && near[3] > near[2] && near[2] > near[1];
            r = { p: b, v: unbounded ? Infinity : Math.max(v, near[3]), attained: false, edge: true, unbounded, jump: !unbounded && S.contains(b) };
          }
          break;
        }
      }
      if (!best || r.v > best.v + 1e-9 * Math.max(1, Math.abs(best.v)) || (Math.abs(r.v - best.v) <= 1e-9 * Math.max(1, Math.abs(best.v)) && !r.attained && best.attained)) best = r;
    }
    return { ...best, value: sign * best.v, S };
  }
  const describeExt = (e, word) => e.far || e.unbounded ? `f is unbounded ${word === 'maximum' ? 'above' : 'below'} on ${fmt(e.S)}${e.unbounded ? ` (towards ${pt(e.p)})` : ''}: there is no ${word}`
    : e.attained ? `the ${word} ${short(e.value)} is attained at ${pt(e.p)}`
      : e.jump ? `the ${word === 'maximum' ? 'supremum' : 'infimum'} ${short(e.value)} is approached towards ${pt(e.p)}, where f jumps away from it: not attained`
        : `the ${word === 'maximum' ? 'supremum' : 'infimum'} ${short(e.value)} is approached towards ${pt(e.p)}, which is not in the set: not attained`;

  /* ---------- covers ---------- */
  // U is a function k ↦ set (k = 1, 2, …) or a finite list of sets.
  const coverSets = U => {
    if (typeof U === 'function') return { get: k => dom(U(k)), finite: null };
    const els = MathViz.elements(U) || (Array.isArray(U) ? U : null);
    need(els && els.every(MathViz.isSet), 'A cover is a function k ↦ (the k-th set), such as k => Ioo(-1, 1 - 1/k), or a list of sets.');
    return { get: k => dom(els[k - 1]), finite: els.length };
  };
  // For each sample point of S: the first k ≤ limit with x in U(k), or 0.
  function firstCover(S, C, pts, limit) {
    const memo = new Map();
    const get = k => { if (!memo.has(k)) memo.set(k, C.get(k)); return memo.get(k); };
    const max = C.finite ? Math.min(C.finite, limit) : limit;
    return pts.map(x => { for (let k = 1; k <= max; k++) if (get(k).contains(x)) return k; return 0; });
  }

  /* ---------- δ for each point (Heine–Cantor) ---------- */
  // The largest δ ≤ width with |f(y) − f(x)| < ε/2 for every sampled y of S within δ of x.
  function localDelta(f, S, x, eps, width) {
    const fx = value(f, x);
    if (!Number.isFinite(fx)) return 0;
    const ok = d => {
      for (let i = 1; i <= 24; i++) for (const s of [1, -1]) {
        const y = x + s * d * i / 24;
        if (!S.contains(y)) continue;
        const fy = value(f, y);
        if (!(Math.abs(fy - fx) < eps / 2)) return false;
      }
      return true;
    };
    if (ok(width)) return width;
    let lo = 0, hi = width;
    for (let k = 0; k < 40; k++) { const m = (lo + hi) / 2; if (ok(m)) lo = m; else hi = m; }
    return lo;
  }

  MathViz.analyzer('bounded', S => {
    let D;
    try { D = dom(S); } catch (e) { return null; }
    const n = dimOf(D);
    if (n > 3) return null;
    const c = D.sample(8).map(asPoint).find(x => D.contains(x));
    if (c === undefined) return null;
    for (const R of [1e3, 1e6, 1e9]) for (const u of dirs(n)) {
      const q = step(c, u, R);
      if (D.contains(q)) return { v: false, why: `it contains ${pt(q)}, at distance ${fmt(R)} from ${pt(c)}` };
    }
    return null;
  });

  MathViz.define({
    name: 'compactness',
    requires: ['topology'],
    description: 'Compact sets: open covers and finite subcovers, Heine–Borel, convergent subsequences found by halving (Bolzano–Weierstrass), maxima and minima attained or only approached, and the δ of uniform continuity from a finite subcover (Heine–Cantor).',
    functions: {
      attains_max: { doc: 'attains_max(f, S): whether f has a largest value on the set S (of ℝ or ℝⁿ). Decided by climbing from the best samples: a climb stuck at the edge of S looks at the boundary point there, which may or may not belong to S.', fn: (f, S) => extremum(f, S, 1).attained },
      attains_min: { doc: 'attains_min(f, S): whether f has a smallest value on S.', fn: (f, S) => extremum(f, S, -1).attained },
      sup_on: { doc: 'sup_on(f, S): the supremum of f on S, attained or not (∞ if f is unbounded there).', fn: (f, S) => extremum(f, S, 1).value },
      inf_on: { doc: 'inf_on(f, S): the infimum of f on S.', fn: (f, S) => extremum(f, S, -1).value },
      argmax_on: { doc: 'argmax_on(f, S): where f is largest on S, or the boundary point its supremum is approached at.', fn: (f, S) => extremum(f, S, 1).p },
    },
    views: {
      cover: {
        doc: 'cover(S, U) draws a set S of the line or the plane with the first n sets of a cover U (a function k ↦ set, or a list of sets). Drag n: the samples of S no set covers yet are red. Shows the smallest n that covers every sample, or that none up to 5000 does.',
        render(ctx, S, U) {
          S = dom(S);
          const C = coverSets(U), n = dimOf(S);
          need(n <= 2, 'cover draws sets of the line or the plane.');
          const maxN = C.finite || 60;
          const N = Math.round(ctx.param('n', { min: 1, max: maxN, step: 1, value: Math.min(C.finite || 6, maxN) }));
          // The samples, the boundary points in S, and points creeping towards each boundary point
          // left out of S (where a cover of a non-compact set needs ever later sets).
          const creep = S.boundary().filter(b => !b.inside && b.inner !== undefined).slice(0, 12).flatMap(b => [1e-2, 1e-4, 1e-6, 1e-9].map(t => {
            const P = asPoint(b.p), I = asPoint(b.inner);
            return typeof P === 'number' ? P + (I - P) * t : P.map((x, i) => x + (I[i] - x) * t);
          })).filter(x => S.contains(x));
          const pts = S.sample(n === 1 ? 300 : 500).map(asPoint).concat(S.boundary().filter(b => b.inside).map(b => asPoint(b.p)), creep);
          const first = firstCover(S, C, pts, 5000);
          const need_ = first.includes(0) ? null : Math.max(...first);
          const uncovered = pts.filter((_, i) => !first[i] || first[i] > N);
          const colors = ['c1', 'c2', 'c3', 'c4', 'c5', 'c6'];
          if (n === 1) {
            const [a, b] = S.window(), pad = 0.35 * (b - a || 1);
            const fig = ctx.figure({ x: [a - pad, b + pad], y: [-1.2, N + 0.6], height: 120 + 14 * Math.min(N, 30), yAxis: false });
            fig.raster({ x: [a - pad, b + pad], y: [-0.25, 0.25], nx: 900, ny: 1, smooth: false, fixed: true, value: x => S.contains(x), color: (v, T) => (v ? [...T.rgb('ink'), 200] : null) });
            for (const bd of S.boundary()) fig.points([[+bd.p, 0]], { color: 'ink', r: 5, hollow: !bd.inside });
            for (let k = 1; k <= N; k++) {
              const Uk = C.get(k), w = Uk.window && Uk.window();
              const y = k <= 30 ? k * 0.9 : 30 * 0.9;
              if (w && !Array.isArray(w[0])) {
                const lo = Math.max(+w[0], a - pad), hi = Math.min(+w[1], b + pad);
                fig.seg(lo, y, hi, y, { color: colors[(k - 1) % 6], width: 3 });
                for (const bd of Uk.boundary()) if (+bd.p >= a - pad && +bd.p <= b + pad) fig.points([[+bd.p, y]], { color: colors[(k - 1) % 6], r: 3.5, hollow: !bd.inside });
              }
            }
            fig.points(uncovered.map(x => [x, 0]), { color: 'neg', r: 3 });
          } else {
            const ws = [S.window()];
            for (let k = 1; k <= Math.min(N, 40); k++) { const w = C.get(k).window && C.get(k).window(); if (w && Array.isArray(w[0])) ws.push(w); }
            const box = S.window(), pad = 0.25 * sizeOf(S);
            const fig = ctx.figure({ x: [box[0][0] - pad, box[0][1] + pad], y: [box[1][0] - pad, box[1][1] + pad], square: true });
            fig.region(S, { color: 'faint', alpha: 0.5 });
            for (let k = 1; k <= Math.min(N, 40); k++) fig.region(C.get(k), { color: colors[(k - 1) % 6], alpha: 0.16 });
            fig.points(pts.filter((_, i) => first[i] && first[i] <= N), { color: 'ink', r: 1.5 });
            fig.points(uncovered, { color: 'neg', r: 3 });
          }
          ctx.legend([{ label: 'the set (hollow end: left out)', color: 'ink' }, { label: `the sets U₁ … U${N}`, color: 'c1' }, { label: 'samples not yet covered', color: 'neg' }]);
          if (uncovered.length) ctx.status('info', `${uncovered.length} of the ${pts.length} samples are outside U₁ ∪ … ∪ U${N}.`);
          else ctx.status('ok', `U₁ ∪ … ∪ U${N} covers every sample.`);
          if (need_) ctx.note(`The first ${need_} set${need_ > 1 ? 's' : ''} already cover every sample: a finite subcover${C.finite ? '' : ', as compactness promises when the set is closed and bounded'}.`);
          else if (first.includes(0)) {
            const worst = pts.filter((_, i) => !first[i]);
            ctx.note(`${worst.length} sample${worst.length > 1 ? 's are' : ' is'} in none of the first ${C.finite || 5000} sets, for example ${precise(worst[0])}. ${C.finite ? 'These sets are not a cover.' : 'Either the sets are not a cover, or points ever closer to the edge need ever later sets: then no finitely many of them suffice, and the set is not compact.'}`);
          }
        },
      },
      bolzano: {
        doc: 'bolzano(s) finds a convergent subsequence of a bounded sequence (of numbers or points of the plane) by halving: keep the half (or quarter) holding the most of the remaining terms, take the next term in it, repeat. The boxes shrink, so the subsequence is Cauchy.',
        render(ctx, s) {
          need(typeof s === 'function', 'bolzano(s) needs a sequence, such as k => (cos(k), sin(2k)).');
          const N = Math.round(ctx.param('terms', { min: 50, max: 4000, step: 50, value: 800 }));
          const terms = [];
          for (let k = 1; k <= N; k++) { const v = s(k); terms.push(Array.isArray(v) ? v.map(Number) : [+v]); }
          need(terms.every(t => t.every(Number.isFinite)), 'Some terms are undefined.');
          const n = terms[0].length;
          need(n <= 2, 'bolzano draws sequences of numbers or of points in the plane.');
          let box = Array.from({ length: n }, (_, i) => [Math.min(...terms.map(t => t[i])), Math.max(...terms.map(t => t[i]))]);
          const L = Math.max(...box.map(([a, b]) => b - a)) || 1;
          box = box.map(([a, b]) => { const m = (a + b) / 2; return [m - L / 2, m + L / 2]; });
          const boxes = [box], picks = [];
          let idx = terms.map((_, k) => k), last = -1;
          for (let level = 0; level < 16; level++) {
            const halves = [];
            const mids = box.map(([a, b]) => (a + b) / 2);
            for (let c = 0; c < 2 ** n; c++) halves.push(box.map(([a, b], i) => ((c >> i) & 1 ? [mids[i], b] : [a, mids[i]])));
            const inBox = (t, bx) => bx.every(([a, b], i) => t[i] >= a && t[i] <= b);
            let bestH = null, bestI = null;
            for (const h of halves) {
              const I = idx.filter(k => k > last && inBox(terms[k], h));
              if (!bestI || I.length > bestI.length) { bestH = h; bestI = I; }
            }
            if (!bestI || bestI.length < 2) break;
            box = bestH; idx = bestI; last = idx[0];
            boxes.push(box); picks.push(last);
          }
          const sub = picks.map(k => terms[k]);
          if (n === 1) {
            const fig = ctx.figure({ x: [0, N + 1], xlabel: 'k', ylabel: 's(k)' });
            // Each halving interval as its two ends; the last one shaded.
            boxes.forEach((b, j) => { if (j) for (const y of b[0]) fig.seg(0, y, N + 1, y, { color: 'c2', width: 1, alpha: Math.max(0.25, 0.9 - j / 16) }); });
            const lb = boxes[boxes.length - 1][0];
            fig.hband(lb[0], lb[1], { color: 'c2', alpha: 0.18 });
            fig.points(terms.map((t, k) => [k + 1, t[0]]), { color: 'faint', r: 1.5 });
            fig.curve(picks.map(k => [k + 1, terms[k][0]]), { color: 'c1', width: 1.5 });
            fig.points(picks.map(k => [k + 1, terms[k][0]]), { color: 'c1', r: 3.5 });
          } else {
            const pad = 0.04 * L;
            const fig = ctx.figure({ x: [boxes[0][0][0] - pad, boxes[0][0][1] + pad], y: [boxes[0][1][0] - pad, boxes[0][1][1] + pad], square: true });
            fig.points(terms, { color: 'faint', r: 1.5 });
            boxes.forEach((b, j) => {
              const st = { color: 'c2', width: 1.2, alpha: Math.max(0.3, 1 - j / 14) }, [[x0, x1], [y0, y1]] = b;
              fig.seg(x0, y0, x1, y0, st); fig.seg(x1, y0, x1, y1, st); fig.seg(x1, y1, x0, y1, st); fig.seg(x0, y1, x0, y0, st);
            });
            fig.curve(sub, { color: 'c1', width: 1.3, alpha: 0.7 });
            fig.points(sub, { color: 'c1', r: 3.5 });
          }
          ctx.legend([{ label: `the first ${N} terms`, color: 'faint' }, { label: 'the halving boxes', color: 'c2' }, { label: 'the subsequence', color: 'c1' }]);
          const lastBox = boxes[boxes.length - 1], side = Math.max(...lastBox.map(([a, b]) => b - a));
          ctx.note(`Subsequence k = ${picks.slice(0, 10).map(k => k + 1).join(', ')}${picks.length > 10 ? ', …' : ''}: after j halvings its terms stay in a box of side 2⁻ʲ·${short(L)}, so it is a Cauchy sequence, and it converges because ℝ${n === 1 ? '' : 'ⁿ'} is complete. The ${picks.length} boxes here shrink to side ${short(side)}, around ${pt(lastBox.map(([a, b]) => (a + b) / 2).length === 1 ? (lastBox[0][0] + lastBox[0][1]) / 2 : lastBox.map(([a, b]) => (a + b) / 2))}. More terms let the halving go deeper.`);
        },
      },
      uniform_delta: {
        doc: 'uniform_delta(f, S, ε) for an interval S: for each point a the largest δₐ with |f(x) − f(a)| < ε/2 when |x − a| < δₐ, the balls B(a, δₐ/2), a finite subcover chosen from them, and δ = the smallest δₐ/2 in it: the δ of uniform continuity (the proof of Theorem 7.15). On a set that isn\'t compact, δₐ can shrink to 0.',
        render(ctx, f, S, eps0 = 0.2) {
          S = dom(S);
          need(dimOf(S) === 1, 'uniform_delta works on intervals of the line.');
          const eps = ctx.param('ε', { min: 0.02, max: 1, step: 0.01, value: eps0 });
          const [a, b] = S.window().map(Number), W = b - a;
          const xs = Array.from({ length: 241 }, (_, i) => a + W * i / 240).filter(x => S.contains(x));
          const near = S.boundary().filter(bd => !bd.inside).map(bd => +bd.p);
          for (const e of near) for (let j = 2; j <= 9; j++) { const x = e + (e === a ? 1 : -1) * W * 10 ** -j; if (S.contains(x)) xs.push(x); }
          xs.sort((x, y) => x - y);
          const deltas = xs.map(x => localDelta(f, S, x, eps, W));
          // A finite subcover by balls B(a, δₐ/2), chosen from the closed end of S inwards (towards an
          // open end the balls shrink, and the cover never finishes).
          const balls = [];
          const fromLeft = S.contains(a) || !S.contains(b);
          let reach = fromLeft ? a : b, done = false;
          for (let guard = 0; guard < 400 && !done; guard++) {
            let best = null;
            xs.forEach((x, i) => {
              const r = deltas[i] / 2;
              if (!(r > 0)) return;
              if (fromLeft ? x - r <= reach + 1e-12 && (!best || x + r > best.x + best.r) : x + r >= reach - 1e-12 && (!best || x - r < best.x - best.r)) best = { x, r, d: deltas[i] };
            });
            if (!best || (fromLeft ? best.x + best.r <= reach + 1e-12 : best.x - best.r >= reach - 1e-12)) break;
            balls.push(best);
            reach = fromLeft ? best.x + best.r : best.x - best.r;
            done = fromLeft ? reach >= b - 1e-12 : reach <= a + 1e-12;
          }
          const coveredAll = done && S.contains(a) && S.contains(b);
          const ys = xs.map(x => value(f, x)).filter(Number.isFinite);
          const yl = [Math.min(...ys), Math.max(...ys)], yr = yl[1] - yl[0] || 1;
          const fig = ctx.figure({ x: [a - 0.05 * W, b + 0.05 * W], y: [yl[0] - 0.45 * yr, yl[1] + 0.1 * yr], xlabel: 'x' });
          fig.curve(x => (S.contains(x) ? value(f, x) : NaN), { color: 'c1', width: 2, n: 800 });
          const base = yl[0] - 0.12 * yr, scale = 0.3 * yr / Math.max(...deltas, 1e-12);
          fig.curve(xs.map((x, i) => [x, base - deltas[i] * scale]), { color: 'c3', width: 1.5 });
          balls.forEach((B, i) => {
            const y = base + 0.03 * yr * (i % 3);
            fig.seg(Math.max(a, B.x - B.r), y, Math.min(b, B.x + B.r), y, { color: 'c2', width: 3, alpha: 0.8 });
            fig.points([[B.x, y]], { color: 'c2', r: 2.5 });
          });
          ctx.legend([{ label: 'f', color: 'c1' }, { label: 'δₐ for each a (drawn downward)', color: 'c3' }, { label: 'the finite subcover B(aᵢ, δᵢ/2)', color: 'c2' }]);
          if (coveredAll && balls.length) {
            const d = Math.min(...balls.map(B => B.d / 2));
            ctx.status('ok', `${balls.length} balls cover ${fmt(S)}; δ = min δᵢ/2 = ${short(d)} works for ε = ${short(eps)} at every point at once.`);
          } else if (S.contains(a) && S.contains(b)) {
            ctx.status('info', `More than ${balls.length} balls would be needed for ε = ${short(eps)}; a larger ε shows the finite subcover.`);
          } else {
            const tiny = Math.min(...deltas.filter(d => d > 0));
            ctx.status('fail', `δₐ shrinks towards ${pt(near[0] !== undefined ? near[0] : a)} (down to ${short(tiny)} on the points tried): the balls B(a, δₐ/2) have no finite subcover, and no single δ > 0 works for ε = ${short(eps)}.`);
          }
        },
      },
      extremes: {
        doc: 'extremes(f, S) colors f over a set S of the plane (or draws its graph over an interval) and marks its maximum and minimum: a filled dot where one is attained, a hollow dot where it is only approached at a boundary point outside S. On a compact S both are attained (Theorem 7.13).',
        render(ctx, f, S) {
          S = dom(S);
          const n = dimOf(S), mx = extremum(f, S, 1), mn = extremum(f, S, -1);
          const mark = (fig, e, color) => {
            if (e.far) return;
            const p = n === 1 ? [e.p, value(f, e.p)] : e.p;
            fig.points([n === 1 && !e.attained ? [e.p, e.value] : p], { color, r: 6, hollow: !e.attained });
          };
          if (n === 1) {
            const [a, b] = S.window().map(Number), pad = 0.08 * (b - a || 1);
            const fig = ctx.figure({ x: [a - pad, b + pad], xlabel: 'x' });
            fig.curve(x => (S.contains(x) ? value(f, x) : NaN), { color: 'c1', width: 2, n: 1000 });
            mark(fig, mx, 'pos'); mark(fig, mn, 'neg');
          } else if (n === 2) {
            const w = S.window(), pad = 0.08 * sizeOf(S);
            const x = [w[0][0] - pad, w[0][1] + pad], y = [w[1][0] - pad, w[1][1] + pad];
            const fig = ctx.figure({ x, y, square: true });
            const lo = mn.far ? -1 : mn.value, hi = mx.far ? 1 : mx.value;
            const mix = (A, B, t) => A.map((v, i) => Math.round(v + (B[i] - v) * t));
            fig.raster({ x, y, nx: 220, ny: 220, value: (px, py) => (S.contains([px, py]) ? value(f, [px, py]) : NaN),
              color: (v, T) => (Number.isFinite(v) ? [...mix(T.rgb('panel'), T.rgb('c1'), Math.max(0, Math.min(1, (v - lo) / ((hi - lo) || 1))) * 0.85 + 0.1), 255] : null) });
            mark(fig, mx, 'pos'); mark(fig, mn, 'neg');
          } else throw MathViz.error('extremes draws sets of the line or the plane.');
          ctx.legend([{ label: 'maximum (hollow: not attained)', color: 'pos' }, { label: 'minimum (hollow: not attained)', color: 'neg' }]);
          ctx.note(`On ${fmt(S)}: ${describeExt(mx, 'maximum')}; ${describeExt(mn, 'minimum')}.`);
          ctx.status(mx.attained && mn.attained ? 'ok' : 'info', mx.attained && mn.attained ? 'Both extremes are attained.' : 'Not every extreme is attained.');
        },
      },
    },
    notation: `
# S is compact. In ℝⁿ, by the Heine–Borel theorem, that means closed and bounded.
# examples: S in Subsets(R^2)
def compact(S: Set) := closed(S) and bounded(S)

# The sets U(1), …, U(n) cover S.
# examples: S in {Icc(0, 1), Ico(0, 1)}, U in {k => Ioo(-1, 1 - 1/k)}, n in {10, 1000}
def covered(S: Set, U: Fun, n) := forall x in S: exists k in 1..n: x in U(k)

# Finitely many of the sets U(1), U(2), … cover S (looking among the first 10⁵).
def finite_subcover(S: Set, U: Fun) := exists n in 1..10^5: covered(S, U, n)

# f is uniformly continuous on a set S of the line: one δ serves every point. (Pairs are written
# x and x + h, which samples close pairs well.)
# examples: f in {x => x^2, x => 1/x, x => sin(1/x), x => sqrt(x)}, S in {Icc(0, 1), Ioc(0, 1)}
def uniformly_continuous_set(f: Fun, S: Set) := forall ε in (0, 1]: exists δ in (0, 1]: forall x in S, h in [-δ, δ]: x + h in S -> |f(x + h) - f(x)| < ε

# A continuous function on a compact set attains its maximum and minimum (Theorem 7.13).
lemma extreme_values: forall f in {p => p[1] + p[2], p => p[1]*p[2], p => sin(3*p[1]) + p[2]^2}, S in {{p in R^2 | |p| <= 1}, {p in R^2 | |p[1]| <= 1 and |p[2]| <= 1}}: attains_max(f, S) and attains_min(f, S)

# Without compactness the maximum can escape: on the open disk the supremum sits on the circle.
conjecture extreme_values_open: forall f in {p => p[1] + p[2], p => p[1]*p[2], p => 1 - |p|}, S in {{p in R^2 | |p| < 1}, {p in R^2 | |p| <= 1}}: attains_max(f, S)

# Continuous functions on compact intervals are uniformly continuous (Heine–Cantor, Theorem 7.15).
lemma heine_cantor: forall f in {x => x^2, x => cos(3*x), x => |x - 1/2|}: uniformly_continuous_set(f, Icc(0, 1))

# On (0, 1], which is not compact, uniform continuity can fail.
conjecture heine_cantor_open: forall f in {x => x^2, x => 1/x, x => sin(1/x)}: uniformly_continuous_set(f, Ioc(0, 1))
`,
  });
});
