MathVizLibrary(function zoo(MathViz) {
  /* The zoo: famous objects that counterexamples are made of, from the classic collections
     (Gelbaum & Olmsted, Counterexamples in Analysis; Steen & Seebach, Counterexamples in Topology).
     Each object knows facts about itself for the library definitions (continuous_at, integrable_on,
     open, closed, …): exact answers, with the reason, where sampling can only guess. A self-check
     recomputes the facts that sampling can decide, with the facts switched off, and must agree. */
  const N = MathViz.numbers;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const fmt = MathViz.format;
  const isRat = x => N.isRational(x);
  const inC = x => N.inCantor(x);
  const meets0 = (a, b) => +a <= 0 && 0 <= +b;
  const nondeg = (a, b) => +a < +b;
  const fn = (f, label, o = {}) => Object.assign(f, { label }, o);
  const GO = 'Gelbaum & Olmsted, Counterexamples in Analysis';
  const ST = 'Steen & Seebach, Counterexamples in Topology';

  /* ---------- functions ---------- */
  const dirichlet = fn(x => (isRat(x) ? 1 : 0), 'Dirichlet function (1 on ℚ, 0 elsewhere)', {
    exactAware: true, kindSensitive: true, source: GO,
    supOn: () => 1, infOn: () => 0,
    facts: {
      continuous_at: { v: false, why: 'every interval holds rationals (value 1) and irrationals (value 0)' },
      continuous_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'it is continuous nowhere' },
      uniformly_continuous_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'it is continuous nowhere' },
      differentiable_at: { v: false, why: 'it is continuous nowhere' },
      bounded_on: { v: true, why: 'its only values are 0 and 1' },
      increasing_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'between any two points it jumps up and down' },
      integrable_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'every upper sum is b − a and every lower sum is 0' },
    },
  });
  const thomae = fn(x => { const q = N.denominator(x); return q ? (N.isExact(x) ? N.rational(1, q) : 1 / q) : 0; }, 'Thomae function (1/q at p/q, 0 at irrationals)', {
    exactAware: true, kindSensitive: true, source: GO,
    supOn: (a, b) => { for (let q = 1; q <= 4096; q++) if (Math.floor(b * q) >= Math.ceil(a * q)) return 1 / q; return 0; },
    infOn: () => 0,
    facts: {
      continuous_at: { v: (f, a) => !isRat(a), why: 'near an irrational, the fractions have large denominators, so values near it are near 0; at p/q the value 1/q is not approached' },
      continuous_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'every interval contains rationals, where it is discontinuous' },
      uniformly_continuous_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'it is discontinuous at every rational' },
      differentiable_at: { v: false, why: 'it is discontinuous at the rationals, and at an irrational the difference quotients against nearby fractions don\'t tend to 0' },
      bounded_on: { v: true, why: 'its values lie in [0, 1]' },
      integrable_on: { v: true, why: 'only finitely many fractions have denominator below any bound, so the upper sums tend to 0' },
    },
  });
  const xQ = fn(x => (isRat(x) ? x : N.isExact(x) ? N.rational(0) : 0), 'x on ℚ, 0 elsewhere', {
    exactAware: true, kindSensitive: true, source: GO,
    facts: {
      continuous_at: { v: (f, a) => +a === 0, why: 'it is squeezed between −|x| and |x| at 0, and jumps between x and 0 everywhere else' },
      continuous_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'it is continuous only at 0' },
      uniformly_continuous_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'it is continuous only at 0' },
      differentiable_at: { v: false, why: 'at 0 the difference quotient is 1 at rationals and 0 at irrationals' },
      bounded_on: { v: true, why: 'it is at most |x|' },
      integrable_on: { v: (f, a, b) => (nondeg(a, b) && (+a > 0 || +b < 0 || +b - +a > 0) ? false : undefined), why: 'it is discontinuous on a set of positive length' },
    },
  });
  const x2Q = fn(x => (isRat(x) ? MathViz.ops.mul(x, x) : N.isExact(x) ? N.rational(0) : 0), 'x² on ℚ, 0 elsewhere', {
    exactAware: true, kindSensitive: true, source: GO,
    facts: {
      continuous_at: { v: (f, a) => +a === 0, why: 'it is squeezed between 0 and x² at 0, and jumps everywhere else' },
      differentiable_at: { v: (f, a) => +a === 0, why: 'at 0 the difference quotient is squeezed by |h|, so the derivative is 0; elsewhere it is not even continuous' },
      continuous_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'it is continuous only at 0' },
      bounded_on: { v: true, why: 'it is at most x²' },
    },
  });
  // Weierstrass: Σ (1/2)ⁿ cos(13ⁿπx), with ab = 6.5 > 1 + 3π/2 (Weierstrass's condition).
  const weierstrass = fn(x => { let s = 0; for (let n = 0; n <= 14; n++) s += Math.pow(0.5, n) * Math.cos(Math.pow(13, n) * Math.PI * x); return s; },
    'Weierstrass function Σ 2⁻ⁿcos(13ⁿπx)', {
      source: 'Weierstrass (1872); ' + GO,
      facts: {
        continuous_at: { v: true, why: 'a uniformly convergent series of continuous functions' },
        continuous_on: { v: true, why: 'a uniformly convergent series of continuous functions' },
        uniformly_continuous_on: { v: true, why: 'continuous on a closed bounded interval' },
        differentiable_at: { v: false, why: 'Weierstrass\'s theorem: with ab > 1 + 3π/2 it is differentiable nowhere' },
        bounded_on: { v: true, why: '|W(x)| ≤ Σ 2⁻ⁿ = 2' },
        integrable_on: { v: true, why: 'it is continuous' },
        increasing_on: { v: (f, a, b) => (nondeg(a, b) ? false : undefined), why: 'it is monotone on no interval' },
      },
    });
  const cantorF = fn(x => {
    const v = +x;
    if (v <= 0) return 0;
    if (v >= 1) return 1;
    let y = v, s = 0, p = 0.5;
    for (let k = 0; k < 50; k++) {
      y *= 3;
      const d = Math.floor(y);
      if (d === 1) return s + p;
      s += (d / 2) * p;
      y -= d;
      p /= 2;
    }
    return s;
  }, 'Cantor function (devil\'s staircase)', {
    source: GO,
    facts: {
      continuous_at: { v: true, why: 'it is continuous (and monotone) on ℝ' },
      continuous_on: { v: true, why: 'it is continuous' },
      uniformly_continuous_on: { v: true, why: 'continuous on a closed bounded interval' },
      increasing_on: { v: true, why: 'it never decreases' },
      bounded_on: { v: true, why: 'its values lie in [0, 1]' },
      integrable_on: { v: true, why: 'it is monotone' },
      differentiable_at: { v: (f, a) => !inC(a), why: 'off the Cantor set it is locally constant (derivative 0); at a point of the Cantor set it rises by 2⁻ⁿ over an interval of length 3⁻ⁿ around it, for every n, so the difference quotients are unbounded' },
    },
  });
  const xsin = fn(x => (+x === 0 ? 0 : +x * Math.sin(1 / +x)), 'x·sin(1/x), 0 at 0', {
    source: GO,
    facts: {
      continuous_at: { v: true, why: 'squeezed between −|x| and |x| at 0' },
      differentiable_at: { v: (f, a) => +a !== 0, why: 'at 0 the difference quotient is sin(1/h), which oscillates' },
      bounded_on: { v: true, why: '|x·sin(1/x)| ≤ |x|' },
      integrable_on: { v: true, why: 'it is continuous' },
      uniformly_continuous_on: { v: true, why: 'continuous on a closed bounded interval' },
      continuous_on: { v: true, why: 'it is continuous everywhere' },
    },
  });
  const x2sin = fn(x => (+x === 0 ? 0 : +x * +x * Math.sin(1 / +x)), 'x²·sin(1/x), 0 at 0', {
    source: GO,
    facts: {
      continuous_at: { v: true, why: 'squeezed by x²' },
      differentiable_at: { v: true, why: 'at 0 the difference quotient h·sin(1/h) tends to 0; elsewhere by the rules (but the derivative 2x·sin(1/x) − cos(1/x) is not continuous at 0)' },
      bounded_on: { v: true, why: 'it is at most x²' },
      integrable_on: { v: true, why: 'it is continuous' },
      continuous_on: { v: true, why: 'it is continuous everywhere' },
    },
  });
  const sin1x = fn(x => (+x === 0 ? 0 : Math.sin(1 / +x)), 'sin(1/x), 0 at 0', {
    source: GO,
    facts: {
      continuous_at: { v: (f, a) => +a !== 0, why: 'near 0 it takes every value in [−1, 1] infinitely often' },
      differentiable_at: { v: (f, a) => +a !== 0, why: 'it is not continuous at 0' },
      continuous_on: { v: (f, a, b) => !meets0(a, b), why: 'it is discontinuous only at 0' },
      uniformly_continuous_on: { v: (f, a, b) => !meets0(a, b), why: 'continuous on [a, b] exactly when 0 is not in it' },
      bounded_on: { v: true, why: '|sin| ≤ 1' },
      integrable_on: { v: true, why: 'bounded, with a single discontinuity' },
    },
  });
  const flat = fn(x => (+x === 0 ? 0 : Math.exp(-1 / (+x * +x))), 'e^(−1/x²), 0 at 0', {
    source: GO,
    facts: {
      continuous_at: { v: true, why: 'e^(−1/x²) → 0 as x → 0' },
      differentiable_at: { v: true, why: 'every derivative exists and is 0 at 0, yet its Taylor series at 0 (all zeros) misses the function' },
      bounded_on: { v: true, why: 'its values lie in [0, 1)' },
      integrable_on: { v: true, why: 'it is continuous' },
      continuous_on: { v: true, why: 'it is continuous everywhere' },
    },
  });
  const recip = fn(x => (+x === 0 ? 0 : 1 / +x), '1/x, 0 at 0', {
    source: 'standard',
    facts: {
      continuous_at: { v: (f, a) => +a !== 0, why: 'it is unbounded near 0' },
      differentiable_at: { v: (f, a) => +a !== 0, why: 'it is not continuous at 0' },
      continuous_on: { v: (f, a, b) => !meets0(a, b), why: 'it is discontinuous at 0' },
      bounded_on: { v: (f, a, b) => !meets0(a, b), why: 'it is unbounded near 0, and bounded on intervals away from 0' },
      integrable_on: { v: (f, a, b) => (nondeg(a, b) ? !meets0(a, b) : undefined), why: 'a Riemann integrable function must be bounded' },
    },
  });
  const indC = fn(x => (inC(x) ? 1 : 0), 'indicator of the Cantor set', {
    exactAware: true, kindSensitive: true, source: GO,
    facts: {
      continuous_at: { v: (f, a) => !inC(a), why: 'off the closed Cantor set it is 0 nearby; at a point of the Cantor set, gaps (value 0) come arbitrarily close' },
      differentiable_at: { v: (f, a) => !inC(a), why: 'it is locally constant off the Cantor set and discontinuous on it' },
      bounded_on: { v: true, why: 'its only values are 0 and 1' },
      integrable_on: { v: true, why: 'it is discontinuous only on the Cantor set, which has length 0, though uncountably many points' },
      continuous_on: { v: (f, a, b) => (+a <= 1 && +b >= 0 ? false : true), why: 'it is discontinuous exactly on the Cantor set' },
    },
  });
  const famousFunctions = [dirichlet, thomae, xQ, x2Q, weierstrass, cantorF, xsin, x2sin, sin1x, flat, recip, indC];
  const Famous = MathViz.finite(famousFunctions, { label: 'famous functions' });

  /* ---------- sets of numbers ---------- */
  const setFacts = (o, facts) => Object.assign(o, { facts, source: o.source || 'standard' });
  const window01 = () => [0, 1];
  const cantorPts = (() => {
    const rats = [[0, 1], [1, 1], [1, 3], [2, 3], [1, 9], [2, 9], [7, 9], [8, 9], [1, 4], [3, 4], [1, 10], [1, 27], [26, 27]].map(([p, q]) => N.rational(p, q));
    const irr = Array.from({ length: 24 }, (_, i) => N.cantorPoint(i + 1));
    return [...rats, ...irr];
  })();
  const Cantor = setFacts(MathViz.space({
    kind: 'cantor', label: 'Cantor set', kindSensitive: true, dim: 1, scalar: true, numeric: true,
    contains: x => (typeof x === 'number' || N.isExact(x)) && inC(x),
    sample: n => cantorPts.slice(0, Math.max(4, n)),
    random: () => cantorPts[Math.floor(Math.random() * cantorPts.length)],
    window: window01, describe: () => 'the Cantor set',
  }), {
    open: { v: false, why: 'it contains no interval' }, closed: { v: true, why: 'an intersection of closed sets' },
    seq_closed: { v: true, why: 'it is closed' }, bounded: { v: true, why: 'it lies in [0, 1]' },
    interior_point: { v: false, why: 'it contains no interval' },
    boundary_point: { v: (x, S) => inC(x), why: 'its points are all boundary points, as it has no interior' },
    limit_point: { v: (x, S) => inC(x), why: 'it is perfect: closed with no isolated points' },
  });
  Object.assign(Cantor, { measure: 0, countable: false, dense: false, nowhereDense: true, perfect: true });
  // The Smith–Volterra–Cantor set: remove middle intervals of length 4⁻ⁿ; what's left has length 1/2.
  const svcContains = x => {
    let v = +x;
    if (!(v >= 0 && v <= 1)) return false;
    MathViz.markInexact();
    let l = 0, r = 1;
    for (let n = 1; n <= 40; n++) {
      const mid = (l + r) / 2, half = Math.pow(4, -n) / 2;
      if (Math.abs(v - mid) < half) return false;
      if (v < mid) r = mid - half; else l = mid + half;
    }
    return true;
  };
  const svcPts = (() => {
    let iv = [[0, 1]];
    for (let n = 1; n <= 5; n++) iv = iv.flatMap(([l, r]) => { const m = (l + r) / 2, h = Math.pow(4, -n) / 2; return [[l, m - h], [m + h, r]]; });
    return iv.flatMap(([l, r]) => [l, r, (l + r) / 2]);
  })();
  const FatCantor = setFacts(MathViz.space({
    kind: 'fatcantor', label: 'fat Cantor set', dim: 1, scalar: true, numeric: true,
    contains: svcContains, sample: n => svcPts.slice(0, Math.max(4, n)), random: () => svcPts[Math.floor(Math.random() * svcPts.length)],
    window: window01, describe: () => 'the fat (Smith–Volterra–Cantor) set',
  }), {
    open: { v: false, why: 'it contains no interval' }, closed: { v: true, why: 'an intersection of closed sets' },
    seq_closed: { v: true, why: 'it is closed' }, bounded: { v: true, why: 'it lies in [0, 1]' },
    interior_point: { v: false, why: 'it contains no interval' },
  });
  Object.assign(FatCantor, { measure: 0.5, countable: false, dense: false, nowhereDense: true, perfect: true, source: GO });
  const recipSeq = Array.from({ length: 60 }, (_, i) => N.rational(1, i + 1));
  const Harmonic0 = setFacts(MathViz.finite([N.rational(0), ...recipSeq], { label: '{1/n} ∪ {0}' }), {
    open: { v: false, why: 'it is countable, so it contains no interval' }, closed: { v: true, why: 'its only limit point, 0, belongs to it' },
    seq_closed: { v: true, why: 'it is closed' }, bounded: true,
    limit_point: { v: (x, S) => +x === 0, why: 'only 0 is approached by the points 1/n' },
    interior_point: { v: false, why: 'it is countable' },
  });
  Object.assign(Harmonic0, { measure: 0, countable: true, dense: false, nowhereDense: true });
  const Harmonic = setFacts(MathViz.finite(recipSeq, { label: '{1/n : n ≥ 1}' }), {
    open: { v: false, why: 'it is countable' }, closed: { v: false, why: '0 is a limit point that is missing' },
    seq_closed: { v: false, why: '1/n → 0, which is not in the set' }, bounded: true,
    limit_point: { v: (x, S) => +x === 0, why: 'only 0 is approached by the points 1/n' },
    interior_point: { v: false, why: 'it is countable' },
  });
  Object.assign(Harmonic, { measure: 0, countable: true, dense: false, nowhereDense: true });

  // ℚ and ℝ ∖ ℚ come from core; give them their facts here.
  const Rat = MathViz.shared.Q, Irr = MathViz.shared.Irrationals;
  if (Rat) {
    setFacts(Rat, {
      open: { v: false, why: 'every interval contains irrationals' }, closed: { v: false, why: 'every irrational is a limit of rationals' },
      seq_closed: { v: false, why: 'rationals converge to √2' }, bounded: false,
      interior_point: { v: false, why: 'every interval contains irrationals' },
      boundary_point: { v: true, why: 'ℚ and its complement are both dense' }, limit_point: { v: true, why: 'ℚ is dense' },
    });
    Object.assign(Rat, { measure: 0, countable: true, dense: true, nowhereDense: false });
  }
  if (Irr) {
    setFacts(Irr, {
      open: { v: false, why: 'every interval contains rationals' }, closed: { v: false, why: 'every rational is a limit of irrationals' },
      seq_closed: { v: false, why: '√2/n → 0, which is rational' }, bounded: false,
      interior_point: { v: false, why: 'every interval contains rationals' },
      boundary_point: { v: true, why: 'both ℚ and its complement are dense' }, limit_point: { v: true, why: 'the irrationals are dense' },
    });
    Object.assign(Irr, { measure: Infinity, countable: false, dense: true, nowhereDense: false });
  }
  const famousSets = [Rat, Irr, Cantor, FatCantor, Harmonic0, Harmonic].filter(Boolean);
  const FamousSets = MathViz.finite(famousSets, { label: 'famous subsets of ℝ' });

  // Properties of sets of numbers: known for the famous ones, intervals and finite sets.
  const prop = (name, ofInterval, ofFinite) => S => {
    S = MathViz.toDomain(S);
    if (S[name] !== undefined) return S[name];
    if (S.kind === 'interval' && !S.integer) return ofInterval(S);
    if (S.kind === 'finite' || (S.kind === 'interval' && S.integer && !S.unbounded)) return ofFinite(S);
    throw MathViz.error(`${name === 'nowhereDense' ? 'nowhere_dense' : name} isn't known for ${S.describe()}. It is known for intervals, finite sets and the famous sets (FamousSets).`);
  };
  const len = S => (S.unbounded ? Infinity : S.hi - S.lo);
  const measure = prop('measure', len, () => 0);
  const countable = prop('countable', S => len(S) === 0, () => true);
  const dense = prop('dense', S => !!S.unbounded && S.unbounded === 'both', () => false);
  const nowhereDense = prop('nowhereDense', S => len(S) === 0, () => true);

  /* ---------- counterexamples built from pieces ----------
     Many counterexamples combine famous objects: 1_ℚ + (1 − 1_ℚ) = 1 is continuous though neither
     part is. Pieces: the objects themselves and 1 − f (or, for sets, the complements). */
  const ops = MathViz.ops;
  const one = Object.assign(() => 1, { label: '1' });
  /* Facts carry over to combinations by the usual rules, so only the genuinely open cases (two
     discontinuous parts, say) are left to sampling. */
  const FN_PROPS = ['continuous_at', 'continuous_on', 'uniformly_continuous_on', 'differentiable_at', 'integrable_on', 'bounded_on'];
  const look = (name, f, rest) => { const k = MathViz.facts.lookup(name, [f, ...rest]); return k ? k.v : undefined; };
  // −f and 1 − f: exactly as good as f.
  const sameAs = (h, f) => {
    h.facts = {};
    for (const name of FN_PROPS) h.facts[name] = { v: (_, ...rest) => look(name, f, rest), why: `the same holds for ${fmt(f)}` };
    h.kindSensitive = h.kindSensitive || f.kindSensitive;
    return h;
  };
  // f + g: good + good is good; good + bad is bad (the bad part is the sum minus the good one).
  // f · g: good · good is good; nothing else is decided.
  const pairFacts = (h, f, g, sum) => {
    h.facts = {};
    for (const name of FN_PROPS) {
      h.facts[name] = {
        v: (_, ...rest) => {
          const a = look(name, f, rest), b = look(name, g, rest);
          if (a === true && b === true) return true;
          if (sum && a !== undefined && b !== undefined && a !== b) return false;
          return undefined;
        },
        why: sum ? 'a sum of two parts with this property has it, and a sum of one with it and one without does not' : 'a product of two parts with this property has it',
      };
    }
    return h;
  };
  const pieces = C => {
    const vals = MathViz.toDomain(C).values.slice(0, 12);
    need(vals.every(v => typeof v === 'function' || MathViz.isSet(v)), 'Sums, Products and Combinations build from functions or sets.');
    return vals.flatMap(v => (typeof v === 'function' ? [v, sameAs(ops.sub(one, v), v)] : [v, MathViz.complement(v)]));
  };
  const label = (f, s) => Object.assign(f, { label: s });
  const pairsOf = (C, combine, sym) => {
    const P = pieces(C), out = [];
    for (let i = 0; i < P.length; i++) for (let j = i + 1; j < P.length; j++) {
      const h = combine(P[i], P[j]);
      if (typeof h === 'function') { h.left = P[i]; h.right = P[j]; label(h, `${fmt(P[i])} ${sym} ${fmt(P[j])}`); pairFacts(h, P[i], P[j], sym === '+'); }
      else Object.assign(h, { left: P[i], right: P[j], label: `${fmt(P[i])} ${sym} ${fmt(P[j])}` });
      out.push(h);
    }
    return out;
  };
  const built = new WeakMap();
  const remember = (C, key, make) => {
    const D = MathViz.toDomain(C);
    let m = built.get(D);
    if (!m) { m = {}; built.set(D, m); }
    return m[key] || (m[key] = make());
  };
  const isFnCat = C => MathViz.toDomain(C).values.every(v => typeof v === 'function');
  const Sums = C => remember(C, 'sums', () => MathViz.finite(pairsOf(C, (f, g) => (isFnCat(C) ? ops.add(f, g) : ops.union(f, g)), isFnCat(C) ? '+' : '∪'), { label: `sums of ${MathViz.toDomain(C).describe()}` }));
  const Products = C => remember(C, 'products', () => MathViz.finite(pairsOf(C, (f, g) => (isFnCat(C) ? ops.mul(f, g) : ops.inter(f, g)), isFnCat(C) ? '·' : '∩'), { label: `products of ${MathViz.toDomain(C).describe()}` }));
  const Combinations = C => remember(C, 'all', () => {
    const P = pieces(C);
    const unary = MathViz.toDomain(C).values.slice(0, 12).flatMap(f => (typeof f === 'function' ? [sameAs(label(ops.neg(f), `−${fmt(f)}`), f), label(ops.abs(f), `|${fmt(f)}|`)] : []));
    return MathViz.finite([...P, ...unary, ...Sums(C).values, ...Products(C).values], { label: `combinations of ${MathViz.toDomain(C).describe()}` });
  });

  MathViz.shared.zoo = { dirichlet, thomae, functions: famousFunctions, sets: famousSets };

  MathViz.define({
    name: 'zoo',
    requires: ['functions', 'topology', 'integration'],
    description: 'Famous counterexamples from the classic collections: the Dirichlet, Thomae, Weierstrass and Cantor functions, x·sin(1/x) and its relatives, the Cantor and fat Cantor sets, ℚ and the irrationals. Each knows exact facts about itself (continuity, differentiability, integrability, openness, measure, countability) with the reason, so claims about them are decided, not guessed.',
    constants: { xQ, x2Q, weierstrass, cantor_function: cantorF, indicator_cantor: indC },
    functions: {
      measure: { doc: 'measure(S): the length (Lebesgue measure) of a set of numbers: known for intervals, finite sets and the famous sets.', fn: measure },
      countable: { doc: 'countable(S): whether S is countable (known for intervals, finite sets and the famous sets).', fn: countable },
      dense: { doc: 'dense(S): whether S is dense in ℝ.', fn: dense },
      nowhere_dense: { doc: 'nowhere_dense(S): whether the closure of S contains no interval.', fn: nowhereDense },
      facts_of: { doc: 'facts_of(x): what the zoo knows about x, with reasons.', fn: x => {
        const F = x && x.facts;
        if (!F) return 'no recorded facts';
        return Object.entries(F).map(([k, e]) => `${k}: ${e && typeof e === 'object' && 'why' in e ? e.why : typeof e === 'function' ? 'depends on the arguments' : e}`).join('; ');
      } },
    },
    spaces: {
      Famous: { doc: 'Famous: the famous functions: Dirichlet, Thomae, x on ℚ, x² on ℚ, Weierstrass, Cantor, x·sin(1/x), x²·sin(1/x), sin(1/x), e^(−1/x²), 1/x, and the indicator of the Cantor set.', fn: () => Famous },
      FamousSets: { doc: 'FamousSets: ℚ, the irrationals, the Cantor set, the fat Cantor set, {1/n} ∪ {0} and {1/n}.', fn: () => FamousSets },
      CantorSet: { doc: 'CantorSet: the middle-thirds Cantor set (membership exact for fractions).', fn: () => Cantor },
      Sums: { doc: 'Sums(C): f + g for any two of the objects of C and their complements 1 − f (for sets, A ∪ B with complements). Each knows its parts as .left and .right.', fn: Sums },
      Products: { doc: 'Products(C): f · g (for sets, A ∩ B), as Sums.', fn: Products },
      Combinations: { doc: 'Combinations(C): the objects of C, their negatives, absolute values and complements, and all sums and products of two: counterexamples are often built this way.', fn: Combinations },
      FatCantor: { doc: 'FatCantor: the Smith–Volterra–Cantor set: nowhere dense, yet of length 1/2.', fn: () => FatCantor },
    },
    notation: `
# A set of numbers is compact when it is closed and bounded (Heine–Borel).
# examples: S in FamousSets
def compact_set(S: Set) := closed(S) and bounded(S)

# Is a set of length 0 countable? The Cantor set says no.
conjecture measure_zero_is_countable: forall S in FamousSets: measure(S) = 0 -> countable(S)

# A countable set has length 0.
lemma countable_has_measure_zero: forall S in FamousSets: countable(S) -> measure(S) = 0

# Does a nowhere dense set have length 0? The fat Cantor set says no.
conjecture nowhere_dense_has_measure_zero: forall S in FamousSets: nowhere_dense(S) -> measure(S) = 0

# Is a function continuous everywhere differentiable somewhere? Weierstrass says no.
conjecture continuous_is_somewhere_differentiable: forall f in Famous: (forall a in [0, 1]: continuous_at(f, a)) -> (exists a in [0, 1]: differentiable_at(f, a))

# Does continuity at a point give continuity near it? x on ℚ is continuous only at 0.
conjecture continuous_at_a_point_is_continuous_nearby: forall f in Famous: continuous_at(f, 0) -> continuous_at(f, 1/2)

# Does differentiability at a point give continuity near it? x² on ℚ is differentiable only at 0.
conjecture differentiable_at_a_point_is_continuous_nearby: forall f in Famous: differentiable_at(f, 0) -> continuous_at(f, 1/2)

# Is a function with uncountably many discontinuities never integrable? The indicator of the Cantor set is.
conjecture integrable_has_few_discontinuities: forall f in Famous: integrable_on(f, 0, 1) -> (forall a in CantorSet: continuous_at(f, a))

# If f + g is continuous, is f or g? The Dirichlet function and 1 minus it say no: their sum is 1.
conjecture continuous_sum_has_a_continuous_part: forall h in Sums(Famous): continuous_at(h, 1/2) -> continuous_at(h.left, 1/2) or continuous_at(h.right, 1/2)

# If f·g is integrable, is f or g? The Dirichlet function times 1 minus it is 0.
conjecture integrable_product_has_an_integrable_part: forall h in Products({dirichlet}): integrable_on(h, 0, 1) -> integrable_on(h.left, 0, 1) or integrable_on(h.right, 0, 1)

# Differentiable implies continuous, for the famous functions too.
lemma differentiable_continuous_famous: forall f in Famous, a in {0, 1/2, 1/3}: differentiable_at(f, a) -> continuous_at(f, a)

# A Riemann integrable function is bounded.
lemma integrable_bounded_famous: forall f in Famous: integrable_on(f, -1, 1) -> bounded_on(f, -1, 1)
`,
  });

  /* The facts that sampling can decide are recomputed with the facts switched off; they must agree.
     (Facts about rationality at a point, or about every point of a set, are beyond sampling: those
     are exactly why the zoo has facts.) */
  MathViz.selfCheck('zoo facts against sampling', env => {
    const cases = [
      ['continuous_at', dirichlet, [N.rational(1, 2)]],
      ['bounded_on', dirichlet, [0, 1]],
      ['continuous_at', thomae, [N.rational(1, 2)]],
      ['continuous_at', xQ, [N.rational(0)]],
      ['continuous_at', xQ, [N.rational(1, 2)]],
      ['bounded_on', weierstrass, [0, 1]],
      ['continuous_at', cantorF, [0.5]],
      ['increasing_on', cantorF, [0, 1]],
      ['continuous_at', xsin, [0]],
      ['differentiable_at', xsin, [0]],
      ['differentiable_at', x2sin, [0]],
      ['continuous_at', sin1x, [0]],
      ['continuous_at', sin1x, [0.5]],
      ['differentiable_at', flat, [0]],
      ['bounded_on', recip, [0, 1]],
      ['bounded_on', recip, [1, 2]],
      ['continuous_at', recip, [0]],
      ['integrable_on', dirichlet, [0, 1]],
      ['integrable_on', recip, [0, 1]],
      ['integrable_on', sin1x, [0, 1]],
    ];
    const out = [];
    for (const [name, f, rest] of cases) {
      const def = env[name];
      const args = [f, ...rest];
      const fact = MathViz.facts.lookup(name, args);
      const label = `${name}(${fmt(f)}, ${rest.map(fmt).join(', ')})`;
      if (!def || !fact) { out.push({ name: label, ok: false, detail: def ? 'no fact recorded' : `${name} is not defined` }); continue; }
      MathViz.facts.disable(true);
      let v;
      try { v = MathViz.withExactSampling(!!f.kindSensitive, () => def(...args)); } catch (e) { v = 'error: ' + e.message; } finally { MathViz.facts.disable(false); }
      out.push({ name: label, ok: v === fact.v, detail: `fact says ${fact.v}, sampling says ${v}` });
    }
    return out;
  });
});
