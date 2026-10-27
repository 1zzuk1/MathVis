MathVizLibrary(function logic(MathViz) {
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };

  /* ---------- Boolean functions: (p, q) => p -> q, tried on every row of the truth table ---------- */
  const arity = f => f.arity || f.length;
  const rows = k => Array.from({ length: 2 ** k }, (_, m) => Array.from({ length: k }, (_, i) => !((m >> (k - 1 - i)) & 1)));
  const asBool = (f, what = 'a formula of true/false variables, such as (p, q) => p -> q') => {
    need(typeof f === 'function' && arity(f) >= 1 && arity(f) <= 6, `Expected ${what}.`);
    return f;
  };
  const table = f => { asBool(f); return rows(arity(f)).map(r => { const v = f(...r); need(typeof v === 'boolean', `The formula should give true or false, but gives ${MathViz.format(v)} at ${r.join(', ')}.`); return [r, v]; }); };
  const isBoolFn = v => {
    if (typeof v !== 'function' || v.domainCtor || v.__structure) return false;
    const k = arity(v);
    if (k < 1 || k > 4) return false;
    try { return rows(k).every(r => typeof v(...r) === 'boolean'); } catch (e) { return false; }
  };
  // The variable names of a formula, from its source when it has one.
  const varNames = f => { const F = MathViz.formula(f); return F && F.params && F.params.length === arity(f) ? F.params : ['p', 'q', 'r', 's', 't', 'u'].slice(0, arity(f)); };
  const lit = (n, v) => (v ? n : `¬${n}`);
  const dnf = f => { const N = varNames(f), T = table(f).filter(([, v]) => v); return T.length ? T.map(([r]) => (r.length > 1 ? '(' : '') + r.map((v, i) => lit(N[i], v)).join(' ∧ ') + (r.length > 1 ? ')' : '')).join(' ∨ ') : '⊥ (false)'; };
  const cnf = f => { const N = varNames(f), F = table(f).filter(([, v]) => !v); return F.length ? F.map(([r]) => (r.length > 1 ? '(' : '') + r.map((v, i) => lit(N[i], !v)).join(' ∨ ') + (r.length > 1 ? ')' : '')).join(' ∧ ') : '⊤ (true)'; };
  const sameArity = (f, g) => need(arity(asBool(f)) === arity(asBool(g)), 'Both formulas need the same number of variables.');

  const B = MathViz.finite([false, true], { label: '{false, true}' });
  // Every subset of a finite set (up to 10 elements).
  const powerSet = S => {
    const D = MathViz.toDomain(S);
    need(D.kind === 'finite' && D.values.length <= 10, 'PowerSet(S) needs a finite set with at most 10 elements, such as {1, 2, 3}.');
    const xs = D.values, out = [];
    for (let m = 0; m < 2 ** xs.length; m++) out.push(MathViz.finite(xs.filter((_, i) => m & (1 << i))));
    return MathViz.finite(out, { label: `the subsets of ${D.describe()}` });
  };

  /* ---------- drawing ---------- */
  const CIRCLES = { 1: [[0, 0, 1]], 2: [[-0.55, 0, 1], [0.55, 0, 1]], 3: [[-0.55, 0.35, 1], [0.55, 0.35, 1], [0, -0.55, 1]] };
  function venn(ctx, f) {
    const k = arity(asBool(f));
    need(k <= 3, 'A Venn diagram is drawn for formulas of 1, 2 or 3 variables.');
    const C = CIRCLES[k], N = varNames(f);
    const fig = ctx.figure({ x: [-2, 2], y: [-1.8, 1.7], square: true, xAxis: false, yAxis: false, height: 300 });
    fig.rect(-1.9, -1.7, 1.9, 1.6, { color: 'faint', alpha: 0.05, stroke: 'faint' });
    fig.raster({ x: [-1.9, 1.9], y: [-1.7, 1.6], nx: 260, ny: 230, smooth: false, value: (x, y) => f(...C.map(([cx, cy, r]) => (x - cx) ** 2 + (y - cy) ** 2 <= r * r)), color: (v, th) => (v ? th.rgba('c1', 0.35) : null) });
    C.forEach(([cx, cy, r], i) => { fig.curve(Array.from({ length: 121 }, (_, t) => [cx + r * Math.cos(t * Math.PI / 60), cy + r * Math.sin(t * Math.PI / 60)]), { color: 'ink', width: 1.5 }); fig.text(cx + (cx || (i === 2 ? 0 : 0)) * 0.9, cy + (i === 2 ? -1.15 : 1.12), N[i], { color: 'ink', align: 'center', font: 'italic 16px "STIX Two Text", Georgia, serif' }); });
    ctx.note(`Shaded: where the formula is true. Each circle is where its variable is true; the outside of all ${k === 1 ? 'of it' : 'of them'} is where ${k === 1 ? 'it is' : 'all are'} false.`);
  }
  MathViz.represent({
    name: 'truth_table', label: 'Its truth table', test: isBoolFn,
    doc: 'The value on every row: a formula of k variables is a function {true, false}ᵏ → {true, false}, and two formulas are equivalent exactly when their tables agree.',
    render(ctx, f) {
      const N = varNames(f), T = table(f), t = T.filter(([, v]) => v).length;
      ctx.table([...N, 'value'], T.map(([r, v]) => [...r.map(x => (x ? 'T' : 'F')), v ? 'T' : 'F']));
      ctx.note(t === T.length ? 'True on every row: a tautology.' : t === 0 ? 'False on every row: a contradiction.' : `True on ${t} of ${T.length} rows: satisfiable, not a tautology.`);
    },
  });
  MathViz.represent({
    name: 'normal_forms', label: 'Its normal forms', test: isBoolFn,
    doc: 'Every formula equals an "or" of "and"s (disjunctive normal form: one term per true row) and an "and" of "or"s (conjunctive normal form: one clause per false row).',
    render(ctx, f) { ctx.table(['', ''], [['DNF', dnf(f)], ['CNF', cnf(f)]]); },
  });
  MathViz.represent({
    name: 'venn', label: 'A Venn diagram: the set where it is true', test: v => isBoolFn(v) && arity(v) <= 3,
    doc: 'Reading each variable as "x lies in the set P", a formula describes a region: and is intersection, or is union, not is the complement.',
    render: venn,
  });

  MathViz.define({
    name: 'logic',
    description: 'Propositional logic: formulas as functions of true/false variables, truth tables, tautologies, satisfiability, equivalence and entailment decided over every row, disjunctive and conjunctive normal forms, Venn diagrams, power sets; implication, equivalence and inclusion of sets each said several ways, and the laws of logic checked in every case.',
    functions: {
      truth_table: { doc: 'truth_table(f): the rows (values of the variables, then the value of f), for f such as (p, q) => p -> q.', fn: f => table(f).map(([r, v]) => [...r, v]) },
      tautology: { doc: 'tautology(f): f is true on every row.', fn: f => table(f).every(([, v]) => v) },
      satisfiable: { doc: 'satisfiable(f): f is true on some row.', fn: f => table(f).some(([, v]) => v) },
      contradiction: { doc: 'contradiction(f): f is false on every row.', fn: f => table(f).every(([, v]) => !v) },
      equivalent: { doc: 'equivalent(f, g): f and g agree on every row.', fn: (f, g) => { sameArity(f, g); const T = table(g); return table(f).every(([, v], i) => v === T[i][1]); } },
      entails: { doc: 'entails(f, g): g is true on every row where f is (f ⊨ g).', fn: (f, g) => { sameArity(f, g); const T = table(g); return table(f).every(([, v], i) => !v || T[i][1]); } },
      models: { doc: 'models(f): the rows where f is true, each a list of values of the variables.', fn: f => table(f).filter(([, v]) => v).map(([r]) => r) },
      count_models: { doc: 'count_models(f): on how many rows f is true.', fn: f => table(f).filter(([, v]) => v).length },
      dnf: { doc: 'dnf(f): the disjunctive normal form, one term per true row, as text.', fn: dnf },
      cnf: { doc: 'cnf(f): the conjunctive normal form, one clause per false row, as text.', fn: cnf },
      xor: { doc: 'xor(p, q): exactly one of p, q is true.', fn: (p, q) => p !== q },
      nand: { doc: 'nand(p, q): not both (the Sheffer stroke; every formula can be written with nand alone).', fn: (p, q) => !(p && q) },
      nor: { doc: 'nor(p, q): neither.', fn: (p, q) => !(p || q) },
    },
    spaces: {
      Bool: { doc: 'Bool: {false, true}, for statements about every truth value, as in forall p, q in Bool: …', space: B },
      PowerSet: { doc: 'PowerSet(S): every subset of a finite set S (up to 10 elements).', fn: powerSet },
    },
    views: {
      venn: { doc: 'venn(f) draws a Venn diagram of a formula of 1 to 3 variables: each circle is where its variable holds, shaded where f is true.', render: venn },
    },
    notation: `
# p implies q, four ways: the arrow; not p or q; the contrapositive, not q implies not p; and "never p true with q false".
# examples: p in Bool, q in Bool
concept implication(p: Bool, q: Bool) where
  arrow: p -> q
  disjunction: not p or q
  contrapositive: not q -> not p
  no_counterexample: not (p and not q)

# p and q are equivalent, four ways: the biconditional; implications both ways; both true or both false; not exclusive-or.
# examples: p in Bool, q in Bool
concept equivalence(p: Bool, q: Bool) where
  biconditional: p <-> q
  both_ways: (p -> q) and (q -> p)
  same_value: (p and q) or (not p and not q)
  not_xor: not xor(p, q)

# A is a subset of B, four ways: every element of A lies in B; A ∩ B = A; A ∪ B = B; A minus B is empty.
# examples: A in PowerSet({1, 2, 3}), B in PowerSet({1, 2, 3})
concept included(A, B) where
  elements: forall x in A: x in B
  meet: A inter B = A
  join: A union B = B
  difference: A \\ B = {}

# De Morgan's laws.
lemma de_morgan_and: forall p, q in Bool: not (p and q) <-> (not p or not q)
lemma de_morgan_or: forall p, q in Bool: not (p or q) <-> (not p and not q)

# Distributivity, both ways.
lemma distributive: forall p, q, r in Bool: (p and (q or r)) <-> ((p and q) or (p and r))

# The converse of an implication is a different statement.
conjecture converse: forall p, q in Bool: (p -> q) -> (q -> p)

# Modus ponens is a tautology.
lemma modus_ponens: tautology((p, q) => (p and (p -> q)) -> q)

# The law of the excluded middle.
lemma excluded_middle: tautology(p => p or not p)
`,
  });
});
