MathVizLibrary(function integration(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const isFn = f => typeof f === 'function';
  const named = (f, label, meta = {}) => Object.assign(f, { label }, meta);

  /* ---------- Darboux sums ---------- */
  // The largest and smallest value of f on [a, b]: from the function's own knowledge when it has it
  // (supOn/infOn), else from samples refined around the extremes.
  function extremes(f, a, b, fine = false) {
    if (f.supOn && f.infOn) return [f.infOn(a, b), f.supOn(a, b)];
    MathViz.markInexact();
    let lo = Infinity, hi = -Infinity, xlo = a, xhi = a;
    // Fine partitions have tiny pieces: a few samples each are enough.
    const n = fine ? 3 : 8;
    for (let i = 0; i <= n; i++) {
      const x = a + (b - a) * i / n;
      const y = f(x);
      if (!Number.isFinite(y)) {
        // A pole or a gap: probe beside it, so 1/x on (0, 1] shows up as unbounded.
        const yl = f(x - (b - a) * 1e-9), yr = f(x + (b - a) * 1e-9);
        for (const v of [yl, yr]) if (Number.isFinite(v)) { if (v < lo) lo = v; if (v > hi) hi = v; }
        if (!Number.isFinite(yl) && !Number.isFinite(yr) && i > 0 && i < n) return [-Infinity, Infinity];
        continue;
      }
      if (y < lo) { lo = y; xlo = x; }
      if (y > hi) { hi = y; xhi = x; }
    }
    // A few golden-section steps around each extreme.
    const refine = (x0, sign) => {
      let l = Math.max(a, x0 - (b - a) / n), r = Math.min(b, x0 + (b - a) / n), best = sign * f(x0);
      for (let k = 0; k < 12; k++) {
        const m1 = l + (r - l) * 0.382, m2 = l + (r - l) * 0.618, v1 = sign * f(m1), v2 = sign * f(m2);
        if (Number.isFinite(v1) && v1 > best) best = v1;
        if (Number.isFinite(v2) && v2 > best) best = v2;
        if (v1 > v2) r = m2; else l = m1;
      }
      return sign * best;
    };
    if (fine) return [lo, hi];
    return [Math.min(lo, refine(xlo, -1)), Math.max(hi, refine(xhi, 1))];
  }
  const memo = new WeakMap();
  function darboux(f, a, b, n) {
    need(isFn(f), 'Darboux sums need a function f.');
    need(typeof a === 'number' && typeof b === 'number' && a < b, 'Darboux sums need an interval [a, b] with a < b.');
    need(Number.isInteger(n) && n >= 1 && n <= 1 << 16, 'The number of pieces n must be a whole number from 1 to 65536.');
    const key = `${a},${b},${n}`;
    let m = memo.get(f);
    if (!m) { m = new Map(); memo.set(f, m); }
    if (m.has(key)) { if (!(f.supOn && f.infOn)) MathViz.markInexact(); return m.get(key); }
    const w = (b - a) / n;
    let U = 0, L = 0;
    for (let i = 0; i < n; i++) {
      const [lo, hi] = extremes(f, a + i * w, a + (i + 1) * w, n > 2048);
      U += hi * w; L += lo * w;
    }
    const r = { U, L };
    m.set(key, r);
    return r;
  }
  const upper = (f, a, b, n) => darboux(f, a, b, n).U;
  const lower = (f, a, b, n) => darboux(f, a, b, n).L;

  /* ---------- step functions (Definitions 1.1 and 1.3) ---------- */
  const isPartition = xs => Array.isArray(xs) && xs.length >= 2 && xs.every((x, i) => i === 0 || +x > +xs[i - 1]);
  function checkStep(xs, cs) {
    need(isPartition(xs), 'A partition is a list a = x₀ < x₁ < … < xₙ = b, as in [0, 0.5, 1].');
    need(Array.isArray(cs) && cs.length === xs.length - 1, `A step function on a partition with ${xs.length - 1} pieces needs ${xs.length - 1} values c₀, c₁, ….`);
  }
  // The function equal to cₖ on (xₖ, xₖ₊₁); at a partition point it takes the value of the piece to its right.
  function stepFunction(xs, cs) {
    checkStep(xs, cs);
    const f = x => { const v = +x; for (let k = xs.length - 2; k >= 0; k--) if (v >= +xs[k]) return cs[k]; return cs[0]; };
    f.label = 'step function on ' + MathViz.format(xs);
    f.arity = 1;
    return f;
  }
  // ∫ = Σ (xₖ₊₁ − xₖ)·cₖ, with the notebook's own arithmetic, so fractions stay exact.
  function stepIntegral(xs, cs) {
    checkStep(xs, cs);
    const { add, sub, mul } = MathViz.ops;
    let s = 0;
    let size = 0;
    for (let k = 0; k < cs.length; k++) { const t = mul(sub(xs[k + 1], xs[k]), cs[k]); s = add(s, t); size += Math.abs(+t); }
    return typeof s === 'number' && Math.abs(s) <= 1e-14 * size ? 0 : s;
  }
  // The same step function on the partition with one more point t (Remark 1.2).
  function refinePartition(xs, cs, t) {
    checkStep(xs, cs);
    const k = xs.findIndex((x, i) => i < xs.length - 1 && +t > +x && +t < +xs[i + 1]);
    if (k < 0) return MathViz.record({ xs: xs.slice(), cs: cs.slice() });
    return MathViz.record({ xs: [...xs.slice(0, k + 1), t, ...xs.slice(k + 1)], cs: [...cs.slice(0, k + 1), cs[k], ...cs.slice(k + 1)] });
  }
  // A Riemann sum Σ (xₖ₊₁ − xₖ)·f(ξₖ) for a partition and points ξₖ ∈ [xₖ, xₖ₊₁] (Section 1.3).
  function taggedSum(f, xs, ts) {
    need(isFn(f) && isPartition(xs) && Array.isArray(ts) && ts.length === xs.length - 1, 'tagged_sum(f, partition, points) needs one point ξₖ in each piece.');
    need(ts.every((t, k) => +t >= +xs[k] && +t <= +xs[k + 1]), 'Each point ξₖ must lie in its piece [xₖ, xₖ₊₁].');
    let s = 0;
    for (let k = 0; k < ts.length; k++) s += (xs[k + 1] - xs[k]) * f(ts[k]);
    return s;
  }
  // The composite trapezoidal rule with n pieces (Theorem 2.14 on each piece).
  function trapezoid(f, a, b, n = 1) {
    need(isFn(f) && Number.isInteger(n) && n >= 1, 'trapezoid(f, a, b, n) needs a function and a whole number of pieces.');
    const h = (b - a) / n;
    let s = (f(a) + f(b)) / 2;
    for (let k = 1; k < n; k++) s += f(a + k * h);
    return s * h;
  }

  /* ---------- improper integrals (Definition 3.7) ---------- */
  const GX = [-0.9602898564975363, -0.7966664774136267, -0.5255324099163290, -0.1834346424956498, 0.1834346424956498, 0.5255324099163290, 0.7966664774136267, 0.9602898564975363];
  const GW = [0.1012285362903763, 0.2223810344533745, 0.3137066458778873, 0.3626837833783620, 0.3626837833783620, 0.3137066458778873, 0.2223810344533745, 0.1012285362903763];
  const gl = (f, a, b) => { const m = (a + b) / 2, h = (b - a) / 2; let t = 0; for (let i = 0; i < 8; i++) t += GW[i] * f(m + h * GX[i]); return t * h; };
  function adapt(f, a, b, tol = 1e-11) {
    let budget = 3000;
    const rec = (lo, hi, whole, t, d) => { const m = (lo + hi) / 2, L = gl(f, lo, m), R = gl(f, m, hi); if (--budget < 0 || d > 40 || Math.abs(L + R - whole) <= t * Math.max(1, Math.abs(L + R))) return L + R; return rec(lo, m, L, t / 1.6, d + 1) + rec(m, hi, R, t / 1.6, d + 1); };
    return rec(a, b, gl(f, a, b), tol, 0);
  }
  // The pieces ∫ over [c, c+1], [c+1, c+3], … (doubling) towards an infinite end, or halving towards
  // a singular end. The integral exists when the pieces shrink geometrically: then the rest of the
  // tail is the last piece times r/(1 − r). Doubling stops where a piece suddenly jumps (the rule
  // can't follow the oscillations of sin(x)/x over [2⁴⁰, 2⁴¹]).
  function towards(f, c, end, dir) {
    const pieces = [];
    const g = x => { const v = +f(x); return Number.isFinite(v) ? v : 0; };
    let prev = c, sum = 0;
    for (let k = 1; k <= 64; k++) {
      const next = end === Infinity ? c + dir * (2 ** k - 1) : end + (c - end) * 2 ** -k;
      const piece = dir > 0 ? adapt(g, prev, next) : adapt(g, next, prev);
      if (k > 12 && Math.abs(piece) > 8 * Math.max(...pieces.slice(-4).map(Math.abs)) + 1e-300) break;
      pieces.push(piece); sum += piece; prev = next;
    }
    const K = pieces.length, scale = Math.max(1, Math.abs(sum));
    const fail = { value: NaN, pieces, converges: false };
    if (K < 12) return fail;
    const last = pieces.slice(-12).map(Math.abs);
    if (Math.max(...last.slice(-8)) <= 1e-13 * scale) return { value: sum, pieces, converges: true };
    const group = i => last.slice(i, i + 4).reduce((x, y) => x + y, 0);
    const A = group(0), B = group(4), C = group(8);
    if (!(A > 0 && B > 0)) return C <= 1e-13 * scale ? { value: sum, pieces, converges: true } : fail;
    const r1 = Math.pow(B / A, 1 / 4), r2 = Math.pow(C / B, 1 / 4);
    const geometric = (r1 < 0.9 && r2 < 0.9) || (r1 < 0.97 && r2 < 0.97 && Math.abs(r1 - r2) < 0.02);
    if (!geometric) return fail;
    return { value: sum + pieces[K - 1] * r2 / (1 - r2), pieces, converges: true };
  }
  function improper(f, a, b) {
    need(isFn(f), 'improper_integral(f, a, b) needs a function; a may be -inf, b may be inf.');
    a = +a; b = +b;
    need(a < b, 'improper_integral(f, a, b) needs a < b.');
    MathViz.markInexact();
    const finite = x => Number.isFinite(x);
    const bad = x => { try { const v = +f(x); return !Number.isFinite(v); } catch (e) { return true; } };
    // Split at a middle point; each half goes towards one end, which may be infinite or singular.
    const c = finite(a) && finite(b) ? (a + b) / 2 : finite(a) ? a + 1 : finite(b) ? b - 1 : 0;
    const left = !finite(a) ? towards(f, c, Infinity, -1) : bad(a) || Math.abs(+f(a + (c - a) * 1e-12)) > 1e6 * Math.max(1, Math.abs(+f(c))) ? towards(f, c, a, -1) : { value: adapt(x => +f(x), a, c), converges: true, pieces: [] };
    const right = !finite(b) ? towards(f, c, Infinity, 1) : bad(b) || Math.abs(+f(b - (b - c) * 1e-12)) > 1e6 * Math.max(1, Math.abs(+f(c))) ? towards(f, c, b, 1) : { value: adapt(x => +f(x), c, b), converges: true, pieces: [] };
    return left.converges && right.converges ? left.value + right.value : NaN;
  }

  /* ---------- functions to integrate ---------- */
  // The Dirichlet and Thomae functions come from the zoo, which knows facts about them.
  const { dirichlet, thomae } = MathViz.shared.zoo;
  let cat = {};
  const Integrands = () => {
    MathViz.markStressable();
    const key = MathViz.stress();
    if (cat[key]) return cat[key];
    const list = [
      named(x => x * x, 'x²'),
      named(x => Math.sin(Math.PI * x), 'sin(πx)'),
      named(x => (x < 0.5 ? 0 : 1), 'step at ½'),
      named(x => Math.floor(4 * x), 'floor(4x)'),
      named(x => (x === 0 ? 0 : Math.sin(1 / x)), 'sin(1/x), 0 at 0'),
      named(x => (x > 0 ? 1 / x : 0), '1/x, 0 at 0 (unbounded)'),
      named(x => (x > 0 ? 1 / Math.sqrt(x) : 0), '1/√x, 0 at 0 (unbounded)'),
      dirichlet,
      thomae,
    ];
    if (key) list.push(
      named(x => { let s = 0; for (let k = 0; k < 20; k++) s += Math.abs(Math.pow(2, k) * x - Math.round(Math.pow(2, k) * x)) / Math.pow(2, k); return s; }, 'Takagi function'),
      named(x => (x === 0 ? 0 : x * x * Math.sin(1 / (x * x))), 'x²·sin(1/x²)'),
      named(x => { let s = 0; for (let k = 1; k <= 30; k++) if (x >= 1 / k) s += Math.pow(2, -k); return s; }, 'jumps at 1/k'),
    );
    return (cat[key] = MathViz.finite(list, { label: 'example functions on [0, 1]' }));
  };

  MathViz.define({
    name: 'integration',
    requires: ['functions', 'analysis', 'series'],
    description: 'Riemann integration through Darboux sums: upper and lower sums, the integrability criterion as a definition, functions that are and aren\'t integrable (Dirichlet, Thomae, unbounded ones), and a view of the sums closing in.',
    functions: {
      step_function: { doc: 'step_function(xs, cs): the step function with partition xs = [x₀, …, xₙ] that equals cₖ on each open piece (xₖ, xₖ₊₁) (Definition 1.1).', fn: stepFunction },
      step_integral: { doc: 'step_integral(xs, cs) = Σ (xₖ₊₁ − xₖ)·cₖ, the integral of the step function (Definition 1.3); exact for fractions.', fn: stepIntegral },
      refine_partition: { doc: 'refine_partition(xs, cs, t): the same step function described on the partition with the extra point t, as a record with fields xs and cs (Remark 1.2).', fn: refinePartition },
      tagged_sum: { doc: 'tagged_sum(f, xs, ξs): the Riemann sum Σ (xₖ₊₁ − xₖ)·f(ξₖ) for a partition xs and points ξₖ in its pieces (Section 1.3).', fn: taggedSum },
      trapezoid: { doc: 'trapezoid(f, a, b, n): the trapezoidal rule with n equal pieces; with n = 1 it is (b − a)(f(a) + f(b))/2 (Theorem 2.14).', fn: trapezoid },
      improper_integral: { doc: 'improper_integral(f, a, b): the integral as a limit (Definition 3.7) when a = -inf, b = inf or f blows up at an end; undefined if the limit doesn\'t exist. Judged from pieces that double towards the end: they must shrink geometrically.', fn: improper },
      improper_converges: { doc: 'improper_converges(f, a, b): whether the improper integral of f from a to b exists (Definition 3.7).', fn: (f, a, b) => Number.isFinite(improper(f, a, b)) },
      upper_sum: { doc: 'upper_sum(f, a, b, n): the upper Darboux sum of f on [a, b] with n equal pieces (the sup on each piece times its width).', fn: upper },
      lower_sum: { doc: 'lower_sum(f, a, b, n): the lower Darboux sum (the inf on each piece times its width).', fn: lower },
      riemann_sum: { doc: 'riemann_sum(f, a, b, n, t): the Riemann sum with n equal pieces, each evaluated at the point a fraction t (0 to 1) of the way along it; t = ½ is the midpoint rule.', fn: (f, a, b, n, t = 0.5) => {
        need(isFn(f) && Number.isInteger(n) && n >= 1, 'riemann_sum(f, a, b, n, t) needs a function and a whole number of pieces.');
        const w = (b - a) / n;
        let s = 0;
        for (let i = 0; i < n; i++) s += f(a + (i + t) * w) * w;
        return s;
      } },
    },
    constants: { dirichlet, thomae },
    spaces: {
      Integrands: { doc: 'Integrands: example functions on [0, 1]: continuous ones, steps, sin(1/x), unbounded ones, the Dirichlet function (not integrable) and the Thomae function (integrable, discontinuous at every rational).', fn: Integrands },
    },
    views: {
      antiderivative: {
        doc: 'antiderivative(f, a) draws f with the signed area from a to x shaded (drag x), and below it F(x) = ∫ₐˣ f, whose slope at x is f(x): F is an antiderivative (Theorem 2.3), and ∫ₐᵇ f = F(b) − F(a) (Theorem 2.8).',
        render(ctx, f, a = 0, b = a + 2) {
          need(isFn(f), 'antiderivative(f, a, b) needs a function.');
          const x = ctx.param('x', { min: a, max: b, step: (b - a) / 400, value: a + 0.6 * (b - a) });
          const F = t => (t === a ? 0 : t > a ? adapt(u => +f(u), a, t) : -adapt(u => +f(u), t, a));
          const xs = Array.from({ length: 301 }, (_, k) => a + (b - a) * k / 300);
          const fig = ctx.figure({ x: [a, b], xlabel: 't', ylabel: 'f(t)', height: 220 });
          const upto = xs.filter(t => t <= x).concat([x]);
          const pos = upto.map(t => [t, Math.max(0, +f(t))]), neg = upto.map(t => [t, Math.min(0, +f(t))]);
          fig.poly([[a, 0], ...pos, [x, 0]], { color: 'pos', alpha: 0.3 });
          fig.poly([[a, 0], ...neg, [x, 0]], { color: 'neg', alpha: 0.3 });
          fig.curve(t => +f(t), { color: 'c1', width: 2, n: 600 });
          const Fx = F(x), fx = +f(x), span = (b - a) * 0.15;
          const fig2 = ctx.figure({ x: [a, b], xlabel: 'x', ylabel: 'F(x)', height: 220 });
          fig2.curve(xs.map(t => [t, F(t)]), { color: 'c2', width: 2 });
          fig2.seg(x - span, Fx - fx * span, x + span, Fx + fx * span, { color: 'c3', width: 1.5, dash: [5, 3] });
          fig2.points([[x, Fx]], { color: 'c2', r: 4 });
          ctx.legend([{ label: 'f', color: 'c1' }, { label: 'area counted positive', color: 'pos' }, { label: 'counted negative', color: 'neg' }, { label: 'F(x) = ∫ₐˣ f', color: 'c2' }, { label: 'slope f(x)', color: 'c3' }]);
          ctx.note(`F(${fmt(+x.toPrecision(4))}) = ${fmt(+Fx.toPrecision(6))}, the signed area so far; the tangent to F there has slope f(${fmt(+x.toPrecision(4))}) = ${fmt(+fx.toPrecision(6))}.`);
        },
      },
      improper: {
        doc: 'improper(f, a, b) shows an improper integral as a limit (Definition 3.7): the area under f up to a cut-off R (drag R towards the infinite or singular end), and the integral up to R against R. It settles exactly when the improper integral exists.',
        render(ctx, f, a = 1, b = Infinity) {
          need(isFn(f), 'improper(f, a, b) needs a function.');
          a = +a; b = +b;
          const toInf = !Number.isFinite(b), lo = Number.isFinite(a) ? a : -10;
          const t = ctx.param(toInf ? 'log₂ of the cut-off R' : 'how close to the end (log₂ of 1/distance)', { min: 0, max: 30, step: 0.5, value: 6 });
          const R = toInf ? lo + 2 ** t : b - (b - lo) * 2 ** -t;
          const g = x => +f(x);
          const view = toInf ? [lo, lo + Math.min(2 ** t, 2 ** 12)] : [lo, b];
          const fig = ctx.figure({ x: view, xlabel: 'x', height: 220 });
          const xs = Array.from({ length: 401 }, (_, k) => view[0] + (Math.min(R, view[1]) - view[0]) * k / 400);
          fig.poly([[view[0], 0], ...xs.map(x => [x, g(x)]).filter(p => Number.isFinite(p[1])), [Math.min(R, view[1]), 0]], { color: 'c1', alpha: 0.25 });
          fig.curve(x => g(x), { color: 'c1', width: 2, n: 800 });
          // The integral up to cut-offs 2⁰ … 2³⁰ (or as close to the end).
          const cuts = Array.from({ length: 61 }, (_, k) => k / 2);
          let acc = 0, prev = lo;
          const vals = cuts.map(k => { const r = toInf ? lo + 2 ** k : b - (b - lo) * 2 ** -k; acc += adapt(x => { const v = g(x); return Number.isFinite(v) ? v : 0; }, prev, r); prev = r; return [k, acc]; });
          const lim = improper(f, a, b);
          const fig2 = ctx.figure({ x: [0, 30], xlabel: toInf ? 'log₂ R' : 'log₂ (1/distance to the end)', ylabel: '∫ up to R', height: 200 });
          fig2.curve(vals, { color: 'c2', width: 2 });
          if (Number.isFinite(lim)) fig2.seg(0, lim, 30, lim, { color: 'ink', width: 1, dash: [3, 3] });
          fig2.points([[t, vals[Math.round(t * 2)][1]]], { color: 'c2', r: 4 });
          ctx.legend([{ label: 'area up to R', color: 'c1' }, { label: 'the integral up to R', color: 'c2' }, ...(Number.isFinite(lim) ? [{ label: 'the limit', color: 'ink' }] : [])]);
          if (Number.isFinite(lim)) ctx.status('ok', `The improper integral exists: ${fmt(+lim.toPrecision(8))}.`);
          else ctx.status('fail', 'The integral up to R doesn\'t settle: the improper integral does not exist.');
        },
      },
      darboux: {
        doc: 'darboux(f, a, b) draws the upper and lower Darboux sums of f on [a, b]. Drag n: f is integrable exactly when the gap between them can be made as small as you like.',
        render(ctx, f, a = 0, b = 1) {
          need(isFn(f), 'darboux(f, a, b) needs a function.');
          const n = ctx.param('n', { min: 1, max: 128, step: 1, value: 8 });
          const fig = ctx.figure({ x: [a, b], xlabel: 'x' });
          const w = (b - a) / n;
          let U = 0, L = 0, finite = true;
          for (let i = 0; i < n; i++) {
            const x0 = a + i * w, x1 = x0 + w;
            const [lo, hi] = extremes(f, x0, x1);
            if (!Number.isFinite(lo) || !Number.isFinite(hi)) { finite = false; continue; }
            U += hi * w; L += lo * w;
            fig.rect(x0, Math.min(0, lo), x1, hi, { color: 'c2', alpha: 0.12, stroke: 'c2', strokeWidth: 0.8 });
            fig.rect(x0, Math.min(0, lo), x1, lo, { color: 'c1', alpha: 0.28 });
            fig.rect(x0, lo, x1, hi, { color: 'neg', alpha: 0.1 });
          }
          if (f.supOn) {
            fig.points(Array.from({ length: 2001 }, (_, i) => { const x = a + (b - a) * i / 2000; return [x, f(x)]; }).filter(p => Number.isFinite(p[1])), { color: 'ink', r: 1.1, alpha: 0.6 });
          } else fig.curve(f, { color: 'ink', width: 1.6, n: 1500 });
          ctx.legend([{ label: 'upper sum', color: 'c2' }, { label: 'lower sum', color: 'c1' }, { label: 'the gap', color: 'neg' }]);
          ctx.note(finite ? `With ${n} pieces: upper sum ${fmt(+U.toPrecision(6))}, lower sum ${fmt(+L.toPrecision(6))}, gap ${fmt(+(U - L).toPrecision(4))}.${f.supOn ? ' (Exact: every piece contains rationals and irrationals.)' : ''}`
            : `f is unbounded on some pieces, so their upper (or lower) sums are infinite: a Riemann integral needs a bounded function.`);
        },
      },
    },
    notation: `
# f is Riemann integrable on [a, b] (Darboux's criterion): the upper and lower sums can be made as
# close as you like. A finite check: ε down to 0.01, with up to 2¹⁶ equal pieces. (Thomae's function
# and sin(1/x) close their gap slowly; the Dirichlet function never does.)
# examples: f in Integrands, a in {0}, b in {1}
def integrable_on(f: Fun, a: R, b: R) := forall ε in [0.01, 1]: exists k in 0..16: upper_sum(f, a, b, 2^k) - lower_sum(f, a, b, 2^k) < ε

# Continuous functions are integrable.
lemma continuous_integrable: forall f in Integrands: continuous_on(f, 0, 1) -> integrable_on(f, 0, 1)

# Bounded functions are integrable? The Dirichlet function says no.
conjecture bounded_integrable: forall f in Integrands: bounded_on(f, 0, 1) -> integrable_on(f, 0, 1)

# Integrable functions are bounded.
lemma integrable_bounded: forall f in Integrands: integrable_on(f, 0, 1) -> bounded_on(f, 0, 1)

# The integral of a step function doesn't depend on the partition: one more point changes nothing (Definition 1.3).
lemma step_integral_well_defined: forall t in (0, 1): step_integral(refine_partition([0, 1/3, 1], [3, 1], t).xs, refine_partition([0, 1/3, 1], [3, 1], t).cs) = step_integral([0, 1/3, 1], [3, 1])

# Riemann sums with any points ξₖ in the pieces approach the integral as the pieces shrink (Section 1.3).
lemma riemann_sums_converge: forall f in {x => x^2, sin, x => exp(-x)}, t in [0, 1]: |riemann_sum(f, 0, 1, 2000, t) - integral(f, 0, 1)| < 1e-3

# The mean value theorem for integrals (1.12): a continuous f takes its average value somewhere.
lemma mean_value_integral: forall f in {x => x^2, x => sin(3*x), x => exp(x) - 2}: exists ξ in [0, 1]: f(ξ) = integral(f, 0, 1)

# The trapezoidal rule (2.14): the error is −(b − a)³/12 · f″(ξ) for some ξ.
lemma trapezoid_error: forall f in {x => x^3, sin, x => exp(2*x)}: exists ξ in [0, 1]: integral(f, 0, 1) = trapezoid(f, 0, 1, 1) - nderiv(f, ξ, 2)/12

# Integration by parts (2.12): ∫ f g′ = [f g] − ∫ f′ g, here with f = ln and g = x (Example 2.13).
lemma by_parts_log: forall b in [1.5, 4]: integral(x => ln(x), 1, b) ~= b*ln(b) - b + 1

# The triangle inequality for integrals (3.6(ii)).
lemma integral_triangle: forall f in {sin, x => x^2 - 0.5, x => cos(5*x), x => x - 1/2}: |integral(f, 0, 2)| <= integral(x => |f(x)|, 0, 2)

# The integral of a product is not the product of the integrals (Remark 1.5).
conjecture integral_product: forall f in {x => 1, x => x}: integral(x => f(x)*f(x), 0, 1) ~= integral(f, 0, 1) * integral(f, 0, 1)

# ∫₁^∞ 1/xˢ exists exactly when s > 1, and ∫₀¹ 1/xˢ exactly when s < 1 (Example 3.8).
lemma power_integrals: forall s in {0.5, 0.8, 1, 1.5, 2, 3}: (improper_converges(x => 1/x^s, 1, inf) <-> s > 1) and (improper_converges(x => 1/x^s, 0, 1) <-> s < 1)

# The integral test (3.9): for decreasing f ≥ 0, Σ f(k) converges exactly when ∫₁^∞ f does.
lemma integral_test: forall s in {0.5, 1, 1.5, 2}: summable(n => 1/n^s) <-> improper_converges(x => 1/x^s, 1, inf)

# The fundamental theorem of calculus, for continuous f: d/dx ∫₀ˣ f = f(x).
lemma ftc: forall f in {sin, exp, x => x^2, abs, x => sqrt(x + 1)}, x in [0.1, 0.9]: |diff(t => integral(f, 0, t), x) - f(x)| < 1e-4
`,
  });
});
