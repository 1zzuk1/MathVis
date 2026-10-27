MathVizNotation(`library sequences
# Convergence of sequences, written in notebook notation. A sequence is a function on 1, 2, 3, …
# Search ranges are finite: N is looked for in 1..10^12 (spread over every scale) and terms are checked for n from N to 10N.

# s converges to L: for every ε the terms are eventually within ε of L.
# examples: s in Sequences(R), L in {0, 1}
def converges_to(s, L) := forall ε in (0, 1]: exists N in 1..10^12: forall n in N..10*N: |s(n) - L| < ε

# s is a Cauchy sequence: for every ε the terms are eventually within ε of each other.
# examples: s in Sequences(R)
def cauchy(s) := forall ε in (0, 1]: exists N in 1..10^12: forall m, n in N..10*N: |s(m) - s(n)| < ε

# s is bounded: all its terms fit inside one ball around the origin.
# examples: s in Sequences(R)
def bounded_seq(s) := exists M in (0, 1000]: forall n in 1..10000: |s(n)| <= M

# s never decreases.
# examples: s in Sequences(R)
def increasing_seq(s) := forall n in 1..1000: s(n) <= s(n + 1)

# s never increases.
# examples: s in Sequences(R)
def decreasing_seq(s) := forall n in 1..1000: s(n + 1) <= s(n)

# A convergent sequence is Cauchy.
lemma convergent_is_cauchy: forall s in Sequences(R): convergent(s) -> cauchy(s)

# A convergent sequence is bounded.
lemma convergent_is_bounded: forall s in Sequences(R): convergent(s) -> bounded_seq(s)

# A bounded sequence need not converge.
conjecture bounded_converges: forall s in Sequences(R): bounded_seq(s) -> convergent(s)
`);
