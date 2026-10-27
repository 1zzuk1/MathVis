MathVizLibrary(function complex(MathViz) {
  class Complex {
    constructor(re, im) { this.re = re; this.im = im; }
  }
  const C = (re, im = 0) => new Complex(re, im);
  const isC = v => v instanceof Complex;
  const lift = v => {
    if (isC(v)) return v;
    if (typeof v === 'number') return C(v, 0);
    throw MathViz.error(`Expected a number, got ${MathViz.format(v)}.`);
  };
  const add = (a, b) => { a = lift(a); b = lift(b); return C(a.re + b.re, a.im + b.im); };
  const sub = (a, b) => { a = lift(a); b = lift(b); return C(a.re - b.re, a.im - b.im); };
  const mul = (a, b) => { a = lift(a); b = lift(b); return C(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re); };
  const div = (a, b) => {
    a = lift(a); b = lift(b);
    const d = b.re * b.re + b.im * b.im;
    return C((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d);
  };
  const cexp = z => { z = lift(z); const r = Math.exp(z.re); return C(r * Math.cos(z.im), r * Math.sin(z.im)); };
  const cln = z => { z = lift(z); return C(Math.log(Math.hypot(z.re, z.im)), Math.atan2(z.im, z.re)); };
  const pow = (a, b) => {
    if (typeof b === 'number' && Number.isInteger(b) && Math.abs(b) <= 64) {
      let r = C(1, 0), base = lift(a), k = Math.abs(b);
      while (k) { if (k & 1) r = mul(r, base); base = mul(base, base); k >>= 1; }
      return b < 0 ? div(1, r) : r;
    }
    const la = lift(a);
    if (la.re === 0 && la.im === 0) return C(0, 0);
    return cexp(mul(b, cln(la)));
  };
  const fmt = MathViz.format;
  const show = z => {
    const re = Math.abs(z.re) < 1e-14 ? 0 : z.re, im = Math.abs(z.im) < 1e-14 ? 0 : z.im;
    if (im === 0) return fmt(re);
    const imPart = (Math.abs(im) === 1 ? '' : fmt(Math.abs(im))) + 'i';
    if (re === 0) return (im < 0 ? '−' : '') + imPart;
    return `${fmt(re)} ${im < 0 ? '−' : '+'} ${imPart}`;
  };

  // Hue from the argument, brightness from log|z| with bands at every doubling.
  const hsl = (h, s, l) => {
    const k = n => (n + h * 12) % 12, a = s * Math.min(l, 1 - l);
    const f = n => l - a * Math.max(-1, Math.min(k(n) - 3, 9 - k(n), 1));
    return [f(0) * 255, f(8) * 255, f(4) * 255, 255];
  };
  const shade = z => {
    if (!z) return null;
    const m = Math.hypot(z.re, z.im);
    if (Number.isNaN(m)) return null;
    if (!Number.isFinite(m)) return [255, 255, 255, 255];
    if (m === 0) return [0, 0, 0, 255];
    const h = (Math.atan2(z.im, z.re) / (2 * Math.PI) + 1) % 1;
    const l2 = Math.log2(m), band = l2 - Math.floor(l2);
    const l = Math.min(0.94, Math.max(0.06, 0.5 + 0.4 * Math.atan(l2 / 3) / (Math.PI / 2) + 0.07 * (band - 0.5)));
    return hsl(h, 0.78, l);
  };

  /* ---------- ways of looking at a complex number (interpret) ---------- */
  const sh = x => MathViz.format(+(+x).toPrecision(4));
  MathViz.represent({
    name: 'complex_forms', label: 'Cartesian, polar and exponential form', test: isC,
    doc: 'z = a + bi = r(cos θ + i sin θ) = r·e^{iθ}: a point of the plane, given by its coordinates or by its distance r = |z| from 0 and its angle θ = arg z.',
    render(ctx, z) {
      const r = Math.hypot(z.re, z.im), t = Math.atan2(z.im, z.re), R = Math.max(1, r) * 1.3;
      const fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true, xlabel: 'Re', ylabel: 'Im' });
      fig.curve(Array.from({ length: 121 }, (_, k) => [r * Math.cos(k * Math.PI / 60), r * Math.sin(k * Math.PI / 60)]), { color: 'faint', dash: [4, 3] });
      fig.arrow(0, 0, z.re, z.im, { color: 'c1', width: 2.5 });
      fig.seg(z.re, 0, z.re, z.im, { color: 'c4', dash: [3, 3] }); fig.seg(0, 0, z.re, 0, { color: 'c4', width: 2 });
      fig.curve(Array.from({ length: 41 }, (_, k) => [0.3 * R * Math.cos(t * k / 40), 0.3 * R * Math.sin(t * k / 40)]), { color: 'c2', width: 2 });
      fig.points([[z.re, z.im]], { color: 'ink', r: 4 });
      ctx.legend([{ label: `a = Re z = ${sh(z.re)}, b = Im z = ${sh(z.im)}`, color: 'c4' }, { label: `θ = arg z = ${sh(t)}`, color: 'c2' }, { label: `r = |z| = ${sh(r)}`, color: 'c1' }]);
      ctx.table(['form', ''], [['cartesian', `${sh(z.re)} ${z.im < 0 ? '−' : '+'} ${sh(Math.abs(z.im))}i`], ['polar', `${sh(r)}·(cos ${sh(t)} + i sin ${sh(t)})`], ['exponential', `${sh(r)}·e^(${sh(t)}i)`], ['conjugate', `${sh(z.re)} ${z.im < 0 ? '+' : '−'} ${sh(Math.abs(z.im))}i`]]);
    },
  });
  MathViz.represent({
    name: 'complex_as_map', label: 'Multiplication by z: a rotation and a scaling', test: isC,
    doc: 'w ↦ z·w turns the plane by arg z and stretches it by |z|. As a real 2×2 matrix it is [[a, −b], [b, a]].',
    render(ctx, z) {
      const ap = ([x, y]) => [z.re * x - z.im * y, z.im * x + z.re * y], r = Math.hypot(z.re, z.im), R = Math.max(1.5, 1.5 * r) * 1.1;
      const fig = ctx.figure({ x: [-R, R], y: [-R, R], square: true, xlabel: 'Re', ylabel: 'Im' });
      for (let i = -3; i <= 3; i++) {
        fig.curve([[i / 2, -1.5], [i / 2, 1.5]], { color: 'faint', alpha: 0.5 }); fig.curve([[-1.5, i / 2], [1.5, i / 2]], { color: 'faint', alpha: 0.5 });
        fig.curve([ap([i / 2, -1.5]), ap([i / 2, 1.5])], { color: 'c1', alpha: 0.6 }); fig.curve([ap([-1.5, i / 2]), ap([1.5, i / 2])], { color: 'c1', alpha: 0.6 });
      }
      fig.arrow(0, 0, 1, 0, { color: 'faint', width: 2 }); fig.arrow(0, 0, ...ap([1, 0]), { color: 'c2', width: 2.5 });
      fig.arrow(0, 0, 0, 1, { color: 'faint', width: 2 }); fig.arrow(0, 0, ...ap([0, 1]), { color: 'c3', width: 2.5 });
      ctx.legend([{ label: 'the grid', color: 'faint' }, { label: 'z times the grid', color: 'c1' }, { label: 'z·1 = z', color: 'c2' }, { label: 'z·i', color: 'c3' }]);
      ctx.note(`As a matrix: [[${sh(z.re)}, ${sh(-z.im)}], [${sh(z.im)}, ${sh(z.re)}]], with determinant |z|² = ${sh(r * r)}.`);
    },
  });

  MathViz.define({
    name: 'complex',
    description: 'Complex numbers: the constant i, arithmetic, exp, ln, sqrt, sin and cos on complex input, and a domain-coloring view.',
    constants: { i: C(0, 1) },
    types: [{
      name: 'complex',
      test: isC,
      ops: {
        '+': add, '-': sub, '*': mul, '/': div, '^': pow,
        neg: z => C(-z.re, -z.im),
        abs: z => Math.hypot(z.re, z.im),
        '=': (a, b) => { a = lift(a); b = lift(b); return Math.hypot(a.re - b.re, a.im - b.im) <= 1e-9 * Math.max(1, Math.hypot(a.re, a.im)); },
        '<': () => { throw MathViz.error("Complex numbers can't be ordered. Compare absolute values instead, as in |z| < 1."); },
        format: show,
      },
    }],
    functions: {
      re: z => lift(z).re,
      im: z => lift(z).im,
      conj: z => { z = lift(z); return C(z.re, -z.im); },
      arg: z => { z = lift(z); return Math.atan2(z.im, z.re); },
      cis: t => C(Math.cos(t), Math.sin(t)),
      // These replace the core versions and still accept plain numbers.
      exp: z => isC(z) ? cexp(z) : Math.exp(z),
      ln: z => isC(z) || z < 0 ? cln(z) : Math.log(z),
      sqrt: z => isC(z) || z < 0 ? pow(z, 0.5) : Math.sqrt(z),
      sin: z => isC(z) ? C(Math.sin(z.re) * Math.cosh(z.im), Math.cos(z.re) * Math.sinh(z.im)) : Math.sin(z),
      cos: z => isC(z) ? C(Math.cos(z.re) * Math.cosh(z.im), -Math.sin(z.re) * Math.sinh(z.im)) : Math.cos(z),
    },
    views: {
      domaincolor: {
        doc: 'domaincolor(f, r) colors each z in the square [−r, r]² by f(z): hue is the argument, brightness bands mark each doubling of |f(z)|.',
        render(ctx, f, r = 2) {
          r = ctx.param('r', { min: 0.5, max: 6, step: 0.1, value: r });
          const fig = ctx.figure({ x: [-r, r], y: [-r, r], square: true, xlabel: 'Re z', ylabel: 'Im z' });
          fig.raster({
            x: [-r, r], y: [-r, r], nx: 280, ny: 280,
            value: (x, y) => {
              const w = f(C(x, y));
              return isC(w) ? w : typeof w === 'number' ? C(w, 0) : null;
            },
            color: shade,
          });
          ctx.note('A zero shows every hue around a dark point and a pole every hue around a bright one. The number of times the hues cycle around a point is its order.');
        },
      },
    },
  });
});
