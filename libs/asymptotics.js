MathVizLibrary(function asymptotics(MathViz) {
  /* Exact eventual and local behaviour, from formulas (src/asym.js): limits and series of sequences
     written as n => …, continuity and differentiability of functions written as x => … at a point,
     and families with a parameter (xᵃ·sin(1/x), Σ 1/nᵖ) whose properties switch at a threshold.
     Formulas the analysis can't decide fall back to sampling, as before. */
  const A = MathViz.asym();
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const isFn = f => typeof f === 'function';
  const hasFormula = f => !!A.formulaOf(f);
  const closeTo = (x, y) => Math.abs(x - y) <= 1e-9 * Math.max(1, Math.abs(x), Math.abs(y));

  /* ---------- analyzers for the library definitions ---------- */
  MathViz.analyzer('continuous_at', (f, a) => (hasFormula(f) && typeof +a === 'number' ? A.continuousAt(f, a) : null));
  MathViz.analyzer('differentiable_at', (f, a) => (hasFormula(f) ? A.derivativeAt(f, a) : null));
  MathViz.analyzer('continuously_differentiable_at', (f, a) => (hasFormula(f) ? A.c1At(f, a) : null));
  MathViz.analyzer('converges_to', (s, L) => {
    if (!hasFormula(s) || typeof +L !== 'number') return null;
    const lim = A.seqLimit(s);
    if (!lim) return null;
    const ok = lim.kind === 'finite' && closeTo(lim.v, +L);
    return { v: ok, why: `the terms tend to ${A.fmtL(lim)}` };
  });
  MathViz.analyzer('cauchy', s => {
    const lim = hasFormula(s) && A.seqLimit(s);
    return lim ? { v: lim.kind === 'finite', why: `the terms tend to ${A.fmtL(lim)}, and a sequence is Cauchy exactly when it converges` } : null;
  });
  MathViz.analyzer('bounded_seq', s => {
    const E = hasFormula(s) && A.seq(s);
    if (!E) return null;
    const lim = A.limitOf(E);
    if (!lim) return null;
    if (lim.kind === 'inf' || (lim.kind === 'none' && E.terms.length && E.terms[0].k.some(x => x > 0))) return { v: false, why: 'the terms grow without bound' };
    // Eventually bounded; the first terms must be finite too.
    for (let n = 1; n <= 200; n++) { let v; try { v = +s(n); } catch (e) { return null; } if (!Number.isFinite(v)) return { v: false, why: `s(${n}) is undefined` }; }
    return { v: true, why: lim.kind === 'finite' ? `the terms converge (to ${A.fmtL(lim)})` : 'the terms stay bounded while they oscillate' };
  });
  // Sequences sampled from Seq(X) are built to converge (to a known limit) or not, and to stay
  // bounded or not: the definitions are answered from that, so even the very slow ones are right.
  const known = s => typeof s === 'function' && s.isSequence && typeof s.convergent === 'boolean';
  MathViz.analyzer('converges_to', (s, L) => {
    if (!known(s)) return null;
    if (!s.convergent) return { v: false, why: `${fmt(s)} doesn't converge (by construction)` };
    if (s.limit === undefined) return null;
    const ok = MathViz.ops.eq(s.limit, L);
    return { v: ok, why: `${fmt(s)} tends to ${fmt(s.limit)} (by construction)` };
  });
  MathViz.analyzer('cauchy', s => (known(s) ? { v: s.convergent, why: `${fmt(s)} ${s.convergent ? 'converges' : "doesn't converge"} (by construction), and in ℝⁿ a sequence is Cauchy exactly when it converges` } : null));
  MathViz.analyzer('bounded_seq', s => {
    if (!known(s)) return null;
    const b = s.convergent ? true : s.bounded;
    return typeof b === 'boolean' ? { v: b, why: `${fmt(s)} ${s.convergent ? 'converges, so it is bounded' : b ? 'stays in a bounded region (by construction)' : 'grows without bound (by construction)'}` } : null;
  });
  MathViz.analyzer('series_converges', a => {
    const v = hasFormula(a) && A.series(a);
    return v ? { v: v.converges, why: v.why } : null;
  });

  /* ---------- functions ---------- */
  const eventuallyLe = (a, b) => {
    need(isFn(a) && isFn(b), 'eventually_le(a, b) compares two sequences, as in eventually_le(n => 1/n^2, n => 1/n).');
    const v = A.eventuallyLe(a, b);
    if (v !== null) return v;
    // No formula to decide it: look far out, and say it's an estimate.
    MathViz.markInexact();
    for (const N of [1e4, 1e5, 1e6]) for (let k = 0; k < 50; k++) if (!(+a(N + k) <= +b(N + k) + 1e-12 * Math.abs(+b(N + k)))) return false;
    return true;
  };
  const growth = a => { need(isFn(a), 'growth(a) describes how a sequence behaves as n → ∞.'); const g = A.growth(a); return g === null ? 'unknown (no formula the analysis can read)' : `like ${g}`; };
  const seriesTest = a => {
    need(isFn(a), 'series_test(a) says whether Σ a(n) converges, and why.');
    const v = A.series(a);
    if (!v) return 'undecided: the formula is beyond the analysis (summable(a) estimates it from partial sums)';
    return `${v.converges ? (v.absolutely ? 'converges absolutely' : 'converges, but not absolutely') : 'diverges'}: ${v.why}`;
  };
  // The parameter values in [lo, hi] where P switches between true and false, located by bisection
  // and snapped to simple fractions.
  const snap = x => {
    for (const q of [1, 2, 3, 4, 5, 6, 8, 10, 12]) { const p = Math.round(x * q); if (Math.abs(x - p / q) < 1e-7) return p / q; }
    return x;
  };
  function findThresholds(P, lo, hi, n = 240) {
    need(isFn(P), 'threshold(P, lo, hi) needs a property P of a parameter, as in a => differentiable_at(x => abs(x)^a * sin(1/x), 0).');
    need(typeof lo === 'number' && typeof hi === 'number' && lo < hi, 'threshold(P, lo, hi) needs a range lo < hi.');
    const val = x => { try { const v = P(x); return v === true ? true : v === false ? false : null; } catch (e) { return null; } };
    const out = [];
    let px = lo, pv = val(lo);
    for (let i = 1; i <= n; i++) {
      const x = lo + (hi - lo) * i / n, v = val(x);
      if (v !== null && pv !== null && v !== pv) {
        let a = px, b = x;
        for (let k = 0; k < 60; k++) { const m = (a + b) / 2, vm = val(m); if (vm === pv) a = m; else b = m; }
        const t = snap((a + b) / 2);
        out.push({ x: t, below: pv, at: val(t), above: v });
      }
      if (v !== null) { px = x; pv = v; }
    }
    return out;
  }
  const describeFamily = (ths, lo, hi, P, name = 'the parameter') => {
    if (!ths.length) { let v; try { v = P((lo + hi) / 2); } catch (e) { v = null; } return `${v ? 'true' : 'false'} for every ${name} in [${fmt(lo)}, ${fmt(hi)}]`; }
    const pieces = [];
    let from = lo, incl = true;
    ths.forEach((t, i) => {
      const atBelow = t.at === t.below;
      // A piece of length 0 is a single value.
      if (from === t.x) pieces.push(`${t.below ? 'true' : 'false'} only at ${name} = ${fmt(t.x)}`);
      else pieces.push(`${t.below ? 'true' : 'false'} for ${fmt(from)} ${incl ? '≤' : '<'} ${name} ${atBelow ? '≤' : '<'} ${fmt(t.x)}`);
      from = t.x; incl = !atBelow;
      if (i === ths.length - 1) pieces.push(`${t.above ? 'true' : 'false'} for ${fmt(t.x)} ${incl ? '≤' : '<'} ${name} ≤ ${fmt(hi)}`);
    });
    return pieces.join('; ');
  };

  MathViz.define({
    name: 'asymptotics',
    requires: ['sequences', 'series', 'functions', 'analysis'],
    description: 'Exact eventual and local behaviour from formulas: limits and series of sequences written as n => … (comparison, Bertrand, Leibniz and Dirichlet tests), continuity and differentiability of functions written as x => … at a point (xᵃ·sin(1/xᵇ) and friends), eventual comparisons, and families whose properties switch at a threshold.',
    functions: {
      eventually_le: { doc: 'eventually_le(a, b): whether a(n) ≤ b(n) for all large n. Exact for sequences given by formulas.', fn: eventuallyLe },
      growth: { doc: 'growth(a): how a(n) behaves as n → ∞, as in "like n⁻¹·(ln n)⁻¹".', fn: growth },
      series_test: { doc: 'series_test(a): whether Σ a(n) converges, absolutely or not, and which test decides it.', fn: seriesTest },
      thresholds: { doc: 'thresholds(P, lo, hi): the parameter values in [lo, hi] where the property P switches between true and false.', fn: (P, lo, hi) => findThresholds(P, lo, hi).map(t => t.x) },
      threshold: { doc: 'threshold(P, lo, hi): the first value in [lo, hi] where P switches, as in threshold(a => differentiable_at(x => abs(x)^a * sin(1/x), 0), 0, 3) = 1.', fn: (P, lo, hi) => { const t = findThresholds(P, lo, hi); return t.length ? t[0].x : NaN; } },
      describe_family: { doc: 'describe_family(P, lo, hi): where P is true and false on [lo, hi], with the thresholds and whether each belongs to the true side.', fn: (P, lo, hi) => describeFamily(findThresholds(P, lo, hi), lo, hi, P) },
    },
    views: {
      family: {
        doc: 'family(P, lo, hi) colors the parameter range [lo, hi] by where the property P holds, and marks the thresholds, as in family(a => differentiable_at(x => abs(x)^a * sin(1/x), 0), 0, 3).',
        render(ctx, P, lo = 0, hi = 3) {
          const ths = findThresholds(P, lo, hi);
          const fig = ctx.figure({ x: [lo, hi], y: [0, 1], height: 90, yAxis: false, xlabel: 'parameter' });
          const cuts = [lo, ...ths.map(t => t.x), hi];
          for (let i = 0; i + 1 < cuts.length; i++) {
            let v; try { v = P((cuts[i] + cuts[i + 1]) / 2); } catch (e) { v = null; }
            fig.vband(cuts[i], cuts[i + 1], { color: v === true ? 'pos' : v === false ? 'neg' : 'undef', alpha: 0.25 });
          }
          for (const t of ths) {
            fig.seg(t.x, 0, t.x, 1, { color: 'ink', width: 1.5 });
            fig.points([[t.x, 0.5]], { color: t.at ? 'pos' : 'neg', r: 5 });
            fig.text(t.x, 0.82, MathViz.format(t.x), { align: 'center', dx: 0 });
          }
          ctx.legend([{ label: 'holds', color: 'pos' }, { label: 'fails', color: 'neg' }, { label: 'the dot: the value at the threshold itself', color: 'ink' }]);
          ctx.note(describeFamily(ths, lo, hi, P) + '.');
        },
      },
      family2: {
        doc: 'family2(P, [a0, a1], [b0, b1]) colors the plane of two parameters by where P(a, b) holds, as in family2((a, b) => continuously_differentiable_at(x => abs(x)^a * sin(1/abs(x)^b), 0), [0, 4], [0.25, 3]).',
        render(ctx, P, ar = [0, 3], br = [0, 3]) {
          need(Array.isArray(ar) && Array.isArray(br) && ar.length === 2 && br.length === 2, 'family2(P, [a0, a1], [b0, b1]) needs two ranges.');
          const fig = ctx.figure({ x: ar, y: br, xlabel: 'a', ylabel: 'b' });
          let t = 0, f = 0, u = 0;
          fig.raster({
            x: ar, y: br, nx: 90, ny: 90, fixed: true, smooth: false,
            value: (a, b) => { let v; try { v = P(a, b); } catch (e) { v = null; } if (v === true) t++; else if (v === false) f++; else u++; return v === true ? 1 : v === false ? 0 : -1; },
            color: (v, T) => (v === 1 ? T.rgba('pos', 0.45) : v === 0 ? T.rgba('neg', 0.3) : T.rgba('undef', 0.25)),
          });
          ctx.legend([{ label: 'holds', color: 'pos' }, { label: 'fails', color: 'neg' }, ...(u ? [{ label: 'undecided', color: 'undef' }] : [])]);
          ctx.note(`Each cell is P(a, b) at its center: true in ${t}, false in ${f}${u ? `, undecided in ${u}` : ''} of ${t + f + u}. The boundary is where the property switches.`);
        },
      },
    },
    notation: `
# f has a continuous derivative at a: it is differentiable at a, and f′(x) → f′(a).
# (Exact for functions given by formulas; numerical otherwise.)
# examples: f in Functions(R), a in {0}
def continuously_differentiable_at(f: Fun, a: R) := differentiable_at(f, a) and continuous_at(deriv(f), a)

# |x|ᵃ·sin(1/x) is continuous at 0 exactly when a > 0 …
lemma xa_sin_continuous: forall a in [0, 3]: continuous_at(x => if x = 0 then 0 else abs(x)^a * sin(1/x), 0) <-> a > 0

# … differentiable at 0 exactly when a > 1 …
lemma xa_sin_differentiable: forall a in [0, 3]: differentiable_at(x => if x = 0 then 0 else abs(x)^a * sin(1/x), 0) <-> a > 1

# … and has a continuous derivative at 0 exactly when a > 2.
lemma xa_sin_c1: forall a in [0, 4]: continuously_differentiable_at(x => if x = 0 then 0 else abs(x)^a * sin(1/x), 0) <-> a > 2

# Σ 1/nᵖ converges exactly when p > 1.
lemma p_series: forall p in [0.25, 3]: summable(n => 1/n^p) <-> p > 1

# Σ 1/(n (ln(n+1))^q) converges exactly when q > 1 (Bertrand).
lemma bertrand: forall q in [0, 3]: summable(n => 1/(n * ln(n + 1)^q)) <-> q > 1

# Σ (−1)ⁿ/nᵖ converges for every p > 0, absolutely exactly when p > 1.
lemma alternating_p_series: forall p in [0.25, 2]: summable(n => (-1)^n / n^p) and (abs_summable(n => (-1)^n / n^p) <-> p > 1)

# The alternating series test needs decreasing terms: adding c/n breaks it for every c ≠ 0.
conjecture alternating_with_a_nudge: forall c in [0, 1]: summable(n => (-1)^n / sqrt(n) + c / n)

# The comparison test, with its true hypothesis: 0 ≤ a(n) ≤ b(n) for all large n.
lemma comparison_test: forall a, b in Series: eventually_le(n => 0, a) and eventually_le(a, b) and summable(b) -> summable(a)
`,
  });

  /* The analysis must agree with what each example series knows about itself. */
  MathViz.selfCheck('asymptotics against the series catalog', env => {
    const out = [];
    for (const stress of [0, 1]) {
      const cat = MathViz.withStress(stress, () => env.Series());
      for (const a of MathViz.toDomain(cat).values) {
        if (!a.expr) continue;
        const v = A.series(a);
        if (!v) { out.push({ name: `Σ ${a.label}`, ok: true, detail: 'undecided' }); continue; }
        const ok = v.converges === a.summable && (typeof a.absolutely !== 'boolean' || v.absolutely === a.absolutely);
        out.push({ name: `Σ ${a.label}`, ok, detail: `known: ${a.summable ? 'converges' : 'diverges'}${typeof a.absolutely === 'boolean' ? (a.absolutely ? ' absolutely' : ', not absolutely') : ''}; analysis: ${v.converges ? 'converges' : 'diverges'}${v.absolutely ? ' absolutely' : ''} (${v.why})` });
      }
    }
    return out;
  });
});
