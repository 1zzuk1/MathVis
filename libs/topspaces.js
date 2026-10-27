MathVizLibrary(function topspaces(MathViz) {
  /* Infinite topological spaces, given by what is known about them (as in Steen & Seebach,
     Counterexamples in Topology, and the π-Base database): ℝ, ℚ, the Cantor set, the Sorgenfrey
     line, cofinite and cocountable topologies, particular- and excluded-point topologies, the
     topologist's sine curve, the line with two origins, … Their open sets can't be sampled, so each
     carries facts for the properties below; finite spaces compute the same properties directly. */
  const ST = 'Steen & Seebach, Counterexamples in Topology';
  const PROPS = ['T0', 'T1', 'hausdorff_space', 'connected_space', 'path_connected_space', 'compact_space', 'separable_space', 'metrizable_space', 'first_countable', 'second_countable'];
  const WORDS = { T0: 'T₀', T1: 'T₁', hausdorff_space: 'Hausdorff', connected_space: 'connected', path_connected_space: 'path-connected', compact_space: 'compact', separable_space: 'separable', metrizable_space: 'metrizable', first_countable: 'first countable', second_countable: 'second countable' };
  const opaque = name => MathViz.space({
    kind: 'opaque', label: `the open sets of ${name}`,
    contains: () => { throw MathViz.error(`The open sets of ${name} can't be tested one by one here; what is known about the space comes from its facts (facts_of shows them).`); },
    sample: () => { throw MathViz.error(`The open sets of ${name} can't be listed; ask about its properties (T1, compact_space, …), which are known facts.`); },
    random: () => { throw MathViz.error(`The open sets of ${name} can't be listed.`); },
    describe: () => `the open sets of ${name}`,
  });
  // flags: T0 T1 T2 connected path compact separable metrizable 1st 2nd, why: notes for the surprising ones
  function space(label, X, flags, why = {}, source = ST) {
    const r = MathViz.record({ X, T: opaque(label) }, label);
    r.known = ['TopologicalSpace'];
    r.source = source;
    r.facts = {};
    PROPS.forEach((p, i) => { r.facts[p] = { v: flags[i] === '1', why: why[p] || `${label} is ${flags[i] === '1' ? '' : 'not '}${WORDS[p]}` }; });
    return r;
  }
  const R = MathViz.interval(-10, 10, { unbounded: 'both', label: 'ℝ' });
  const spaces = [
    space('ℝ', R, '1111101111', { compact_space: 'ℝ is unbounded, so the cover by (−n, n) has no finite subcover' }, 'standard'),
    space('[0, 1]', MathViz.interval(0, 1), '1111111111', { compact_space: 'Heine–Borel: closed and bounded' }, 'standard'),
    space('ℚ (as a subspace of ℝ)', R, '1110001111', { connected_space: 'ℚ splits into the rationals below and above √2' }, 'standard'),
    space('the Cantor set', MathViz.interval(0, 1), '1110011111', { connected_space: 'it is totally disconnected', compact_space: 'closed and bounded in ℝ' }),
    space('ℝ with the discrete topology', R, '1110000110', { separable_space: 'every set is closed, so a dense set must be all of ℝ, which is uncountable', second_countable: 'every point must be a basis element' }),
    space('ℝ with the indiscrete topology', R, '0001111011', { T0: 'the only open sets are ∅ and ℝ, so no open set tells two points apart', metrizable_space: 'a metric would separate points' }),
    space('the Sorgenfrey line', R, '1110001010',
      { connected_space: 'the half-open intervals [a, b) are open and closed', separable_space: 'ℚ is dense', second_countable: 'a basis needs a set [x, …) for every x', metrizable_space: 'it is separable but not second countable, which a metric space can\'t be' }),
    space('the topologist\'s sine curve (closed)', MathViz.product([MathViz.interval(0, 1), MathViz.interval(-1, 1)]), '1111011111',
      { path_connected_space: 'no path reaches the segment {0} × [−1, 1] from the curve: sin(1/x) oscillates too fast', connected_space: 'the closure of a connected set (the curve) is connected' }),
    space('the line with two origins', R, '1101101011',
      { hausdorff_space: 'the two origins have no disjoint neighbourhoods', metrizable_space: 'it is not Hausdorff' }),
    space('ℕ with the cofinite topology', MathViz.interval(0, 100, { integer: true, unbounded: 'above', label: 'ℕ' }), '1101011011',
      { hausdorff_space: 'any two nonempty open sets meet: their complements are finite', path_connected_space: 'a path would split [0, 1] into countably many disjoint closed sets, which Sierpiński\'s theorem forbids', compact_space: 'any open set misses only finitely many points' }),
    space('ℝ with the cofinite topology', R, '1101111000',
      { hausdorff_space: 'any two nonempty open sets meet: their complements are finite', first_countable: 'countably many open sets around a point would miss only countably many points' }),
    space('ℝ with the cocountable topology', R, '1101000000',
      { hausdorff_space: 'any two nonempty open sets meet: their complements are countable', compact_space: 'any countably infinite set is closed and discrete', separable_space: 'countable sets are closed', path_connected_space: 'compact sets are finite, so a path is constant' }),
    space('ℝ with the particular point topology (open sets contain 0)', R, '1001101010',
      { T1: 'every open set around x ≠ 0 contains 0', compact_space: 'the open sets {0, x} cover ℝ with no finite subcover', separable_space: '{0} is dense' }),
    space('ℝ with the excluded point topology (open sets miss 0, or are ℝ)', R, '1001110010',
      { T1: 'the only open set containing 0 is ℝ', compact_space: 'the only open set containing 0 is ℝ itself', separable_space: 'the closure of a set A is A ∪ {0}' }),
    space('the Hilbert cube [0, 1]^ℕ', MathViz.interval(0, 1), '1111111111', { compact_space: 'Tychonoff\'s theorem' }),
  ];

  // For a finite space these properties are decided directly; an infinite one must know them.
  const finiteOnly = S => {
    const X = S && S.fields && S.fields.X;
    if (X && X.kind === 'finite') return true;
    throw MathViz.error(`${MathViz.format(S)} is infinite: this property is computed only for finite spaces, and for an infinite space it must be a known fact.`);
  };

  MathViz.define({
    name: 'topspaces',
    requires: ['topology', 'models'],
    description: 'Infinite topological spaces given by what is known about them (Steen & Seebach; π-Base): ℝ, ℚ, the Cantor set, the Sorgenfrey line, cofinite, cocountable, particular- and excluded-point topologies, the topologist\'s sine curve, the line with two origins, the Hilbert cube, with ten properties each. Finite spaces compute the same properties, so they can be mixed.',
    functions: {
      finite_space: { doc: 'finite_space(S): true for a finite topological space; an error for an infinite one (whose properties must be known facts).', fn: finiteOnly },
    },
    spaces: {
      InfiniteSpaces: { doc: 'InfiniteSpaces: ℝ, [0, 1], ℚ, the Cantor set, discrete and indiscrete ℝ, the cofinite topology on ℕ and on ℝ, the cocountable topology, the Sorgenfrey line, the particular- and excluded-point topologies, the topologist\'s sine curve, the line with two origins and the Hilbert cube.', fn: () => MathViz.finite(spaces, { label: 'famous infinite spaces' }) },
      Spaces: { doc: 'Spaces: every topology on up to 3 points, then the famous infinite spaces. Claims over them find the smallest counterexample, finite or not.', fn: () => MathViz.finite([...(MathViz.shared.allTopologies ? MathViz.toDomain(MathViz.shared.allTopologies(3)).values : []), ...spaces], { label: 'finite and famous spaces' }) },
    },
    notation: `
# Path-connected: any two points are joined by a path. (For a finite space this is the same as connected.)
def path_connected_space(S: TopologicalSpace) := finite_space(S) and connected_space(S)

# Compact: every open cover has a finite subcover. (Every finite space is.)
def compact_space(S: TopologicalSpace) := finite_space(S)

# Separable: some countable set is dense. (Every finite space is.)
def separable_space(S: TopologicalSpace) := finite_space(S)

# First and second countable: countable neighbourhood bases, a countable basis. (Every finite space is both.)
def first_countable(S: TopologicalSpace) := finite_space(S)
def second_countable(S: TopologicalSpace) := finite_space(S)

# Metrizable: the topology comes from a metric. (A finite space is metrizable exactly when it is discrete, that is T₁.)
def metrizable_space(S: TopologicalSpace) := finite_space(S) and T1(S)

# The separation axioms get stronger: Hausdorff gives T₁ gives T₀.
lemma separation_chain: forall S in Spaces: (hausdorff_space(S) -> T1(S)) and (T1(S) -> T0(S))

# Does T₁ give Hausdorff? The cofinite topology on ℕ says no.
conjecture T1_gives_hausdorff: forall S in Spaces: T1(S) -> hausdorff_space(S)

# Does connected give path-connected? The topologist's sine curve says no.
conjecture connected_gives_path_connected: forall S in Spaces: connected_space(S) -> path_connected_space(S)

# Path-connected gives connected.
lemma path_connected_gives_connected: forall S in Spaces: path_connected_space(S) -> connected_space(S)

# Does separable give second countable? The Sorgenfrey line says no.
conjecture separable_gives_second_countable: forall S in Spaces: separable_space(S) -> second_countable(S)

# Second countable gives separable and first countable.
lemma second_countable_gives_both: forall S in Spaces: second_countable(S) -> separable_space(S) and first_countable(S)

# A metrizable space is Hausdorff and first countable; and it is separable exactly when it is second countable.
lemma metrizable_properties: forall S in Spaces: metrizable_space(S) -> hausdorff_space(S) and first_countable(S) and (separable_space(S) <-> second_countable(S))

# Does metrizable give separable? ℝ with the discrete topology says no.
conjecture metrizable_gives_separable: forall S in Spaces: metrizable_space(S) -> separable_space(S)

# Is a compact space Hausdorff? Not at all: the smallest example has two points.
conjecture compact_gives_hausdorff: forall S in Spaces: compact_space(S) -> hausdorff_space(S)
`,
  });
});
