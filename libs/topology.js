MathVizNotation(`library topology
# Open and closed sets, interior, boundary and limit points, for sets of numbers or of points in ℝⁿ.
# Written in notebook notation: every definition here is checked by sampling, like any other.

# x is an interior point of S: some ball around x lies inside S.
# examples: x in {(0, 0), (1, 0), (0.5, 0.5)}, S in Subsets(R^2)
def interior_point(x, S) := exists ε in (0, 1]: Ball(x, ε) ⊆ S

# S is open: each of its points is an interior point.
# examples: S in Subsets(R^2)
def open(S: Set) := forall x in S: interior_point(x, S)

# S is closed: its complement is open.
# examples: S in Subsets(R^2)
def closed(S: Set) := open(complement(S))

# S is sequentially closed: every convergent sequence in S has its limit in S.
# examples: S in Subsets(R^2)
def seq_closed(S: Set) := forall s in Seq(S): convergent(s) -> lim(s) in S

# x is a boundary point of S: every ball around x meets both S and its complement.
# examples: x in {(0, 0), (1, 0), (0.5, 0.5)}, S in Subsets(R^2)
def boundary_point(x, S) := forall ε in (0, 1]: (exists y in Ball(x, ε): y in S) and (exists y in Ball(x, ε): y notin S)

# x is a limit point of S: every ball around x holds a point of S other than x.
# examples: x in {(0, 0), (1, 0), (0.5, 0.5)}, S in Subsets(R^2)
def limit_point(x, S) := forall ε in (0, 1]: exists y in Ball(x, ε): y in S and y != x

# S is bounded: it fits inside some ball around the origin.
# examples: S in Subsets(R^2)
def bounded(S: Set) := exists M in (0, 1000]: forall x in S: |x| <= M

# The union of two open sets is open.
lemma union_of_open: forall A, B in Subsets(R^2): open(A) and open(B) -> open(A ∪ B)

# The intersection of two closed sets is closed.
lemma intersection_of_closed: forall A, B in Subsets(R^2): closed(A) and closed(B) -> closed(A ∩ B)

# A set is closed exactly when it is sequentially closed.
lemma closed_iff_seq_closed: forall A in Subsets(R^2): closed(A) <-> seq_closed(A)

# A set is open exactly when its complement is closed.
lemma open_iff_complement_closed: forall A in Subsets(R^2): open(A) <-> closed(complement(A))

# Most sets are neither open nor closed.
conjecture open_or_closed: forall A in Subsets(R^2): open(A) or closed(A)

# ---- Topological spaces on finite sets ----

# A topology on a finite set X: T lists the open sets. It must contain ∅ and X and be closed
# under unions and intersections (for finite sets, pairwise is enough).
# examples: TopologicalSpace({1, 2}, {{}, {1}, {1, 2}}), TopologicalSpace({1, 2}, {{}, {1}, {2}, {1, 2}}), TopologicalSpace({1, 2, 3}, {{}, {1}, {1, 2}, {1, 2, 3}}), TopologicalSpace({1, 2, 3}, {{}, {1, 2, 3}}), TopologicalSpace({1, 2, 3}, {{}, {1}, {2, 3}, {1, 2, 3}}), TopologicalSpace({1, 2, 3}, {{}, {1}, {2}, {1, 2}, {1, 2, 3}}), TopologicalSpace({1, 2}, {{}, {3}, {1, 2}, {1, 2, 3}}), TopologicalSpace({1, 2, 3}, {{1}, {1, 2, 3}}), TopologicalSpace({1, 2, 3}, {{}, {1}}), TopologicalSpace({1, 2, 3}, {{}, {1}, {2}, {1, 2, 3}}), TopologicalSpace({1, 2, 3}, {{}, {1, 2}, {2, 3}, {1, 2, 3}})
structure TopologicalSpace(X: Set, T: Set) where
  subsets: forall U in T: U ⊆ X
  has_empty: {} in T
  has_whole: X in T
  unions: forall U, V in T: U ∪ V in T
  intersections: forall U, V in T: U ∩ V in T

# A is closed in the space S: its complement in S.X is open.
def closed_in(S: TopologicalSpace, A: Set) := S.X ∖ A in S.T

# The interior of A in S: the points with an open neighborhood inside A.
def interior_in(S: TopologicalSpace, A: Set) := {x in S.X | exists U in S.T: x in U and U ⊆ A}

# The closure of A in S: the points whose every open neighborhood meets A.
def closure_in(S: TopologicalSpace, A: Set) := {x in S.X | forall U in S.T: x in U -> (exists y in U: y in A)}

# f is continuous from S to R: preimages of open sets are open.
def continuous_between(f: Fun, S: TopologicalSpace, R: TopologicalSpace) := forall V in R.T: {x in S.X | f(x) in V} in S.T

# S is T₀ (Kolmogorov): any two points are told apart by some open set.
def T0(S: TopologicalSpace) := forall x, y in S.X: x != y -> exists U in S.T: (x in U and y notin U) or (y in U and x notin U)

# S is T₁: for any two points, each has an open set avoiding the other.
def T1(S: TopologicalSpace) := forall x, y in S.X: x != y -> exists U in S.T: x in U and y notin U

# S is Hausdorff: any two points have disjoint open neighborhoods.
def hausdorff_space(S: TopologicalSpace) := forall x, y in S.X: x != y -> exists U, V in S.T: x in U and y in V and U ∩ V = {}

# S is connected: the only sets both open and closed are ∅ and S.X.
def connected_space(S: TopologicalSpace) := forall U in S.T: closed_in(S, U) -> U = {} or U = S.X

# Hausdorff implies T₁, which implies T₀.
lemma hausdorff_T1_T0: forall S in TopologicalSpace: (hausdorff_space(S) -> T1(S)) and (T1(S) -> T0(S))

# Is every T₀ space T₁? The Sierpiński space says no.
conjecture T0_is_T1: forall S in TopologicalSpace: T0(S) -> T1(S)

# A finite T₁ space is discrete: every point is open.
lemma finite_T1_discrete: forall S in TopologicalSpace: T1(S) -> forall x in S.X: {x} in S.T

# The interior lies inside the set, which lies inside its closure.
lemma interior_closure: forall S in TopologicalSpace: forall A in S.T ∪ {{1}, {2}, {1, 3}}: interior_in(S, A) ⊆ A and A ∩ S.X ⊆ closure_in(S, A)

# The closure of a set is closed.
lemma closure_is_closed: forall S in TopologicalSpace: forall A in {{1}, {2}, {1, 3}, {2, 3}}: closed_in(S, closure_in(S, A))
`);
