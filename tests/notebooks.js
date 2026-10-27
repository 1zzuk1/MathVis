/* More notebooks, for the tests: they exercise every library and every view (tests/run.js runs
   them, tests/views.html draws their views). They aren't shown in the app; to show one, move it
   into EXAMPLES in app/main.js or into app/courses.js. */
'use strict';
(function () {
const NOTEBOOKS = [
  { name: "Start here", src: `# Welcome to Theorem Sketchpad. Each line is a statement; Run (Ctrl+Enter) checks them all and
# the results appear on the right. Edit anything and run again: this copy is yours.

# 1. Arithmetic, exact where it can be.
1/3 + 1/12
sqrt(8) / sqrt(2)

# 2. A claim is checked on many examples. This one holds, and algebra proves it for every x, y.
check forall x, y in R: (x + y)^2 = x^2 + 2x*y + y^2

# 3. This one is false: you get the simplest counterexample, and a picture of where it fails.
#    Click a counterexample on the right to see why it fails, step by step.
check forall x in R: x^2 >= x

# 4. Definitions read like mathematics, and claims can use them.
def increasing(f) := forall x, y in [-3, 3]: x < y -> f(x) < f(y)
check increasing(x => x^3)
check increasing(x => x^2)

# 5. Pictures: plot, or "show" one of the views the libraries provide.
plot sin(x), x - x^3/6 for x in [-4, 4]

# 6. Proofs: write the steps and each one is checked. Here every step is exact algebra, so the
#    induction is a complete proof.
theorem gauss: forall n in N: sum k in 1..n: k = n*(n + 1)/2
proof:
  induction on n
  base:
    so sum k in 1..0: k = 0*(0 + 1)/2
  step:
    let n
    assume sum k in 1..n: k = n*(n + 1)/2
    so sum k in 1..n + 1: k = (n + 1)*(n + 2)/2

# Where next: the Notebook menu above has courses (analysis, algebra, groups, topology, dynamics,
# geometry, proofs, …); the Libraries tab has ready-made definitions to import; the Language tab
# is the reference. The ∀ ∃ ∈ ≤ buttons insert symbols, or type forall, exists, in, <=.
` },
  { name: "Open and closed sets", src: `# Open and closed sets, checked straight from their definitions.
# The definitions live in the topology library (Libraries tab), written in this same notation.
import topology

def open_disk := {p in R^2 | |p| < 1}
def closed_disk := {p in R^2 | |p| <= 1}
def square := {(x, y) in R^2 | 0 <= x < 1 and 0 <= y < 1}    # half-open: neither open nor closed

show region(open_disk, square)

# Open: every point has a ball around it inside the set. Zoom in on the boundary.
check open(open_disk)
check open(closed_disk)

# Closed, once through complements and once through sequences.
check closed(closed_disk)
check seq_closed(open_disk)
check seq_closed(closed_disk)

check open(square)
check seq_closed(square)

# The same definitions work on the line.
check open(Ioo(0, 1))
check seq_closed(Ico(0, 1))
` },
  { name: "Explaining definitions", src: `# explain shows a definition, reads it in plain words, and tries it on examples.
# Every definition and lemma in the libraries can be explained (Libraries tab → Explain),
# and so can yours. Click any example or cell to see why it comes out that way.
import topology, functions

explain open
explain continuous_at

# Your own definitions: give parameters types, and explain picks examples for them.
# f is even: f(−x) = f(x).
def even(f: Fun) := forall x in [-3, 3]: f(-x) = f(x)
explain even

# Or choose the examples yourself with "for".
explain interior_point for x in {(0, 0), (1, 0), (2, 0)}, S in {Disk((0, 0), 1), OpenDisk((0, 0), 1)}

# Lemmas from the libraries are checked by name; conjectures show their counterexamples.
check union_of_open
check closed_iff_seq_closed
check open_or_closed
` },
  { name: "Sequences", src: `# A sequence is a function on 1, 2, 3, …  Seq(X) is the space of sequences in X,
# and Seq(Seq(R)) the space of sequences of sequences.
import sequences

def s(n) := (1 + 1/n)^n
plot s(n) for n in 1..60
lim n -> inf: s(n)

check converges_to(s, e)
check converges_to(n => (-1)^n, 0)

# Named examples: 1/n, (−1)ⁿ, the harmonic sums, …
explain cauchy
check bounded_converges

# Claims about every sequence: the sampler tries convergent, constant and divergent ones.
theorem limit_of_sum: forall a, b in Seq(R): convergent(a) and convergent(b) -> lim(a + b) = lim(a) + lim(b)

# Sequences in the plane. Zoom in to follow the spiral.
def spiral(n) := (cos(n), sin(n)) / n
plot spiral(n) for n in 1..80
check converges_to(spiral, (0, 0))

# Sequences of sequences: the first claim is false, the second repairs it.
conjecture limits_converge: forall A in Seq(Seq(R)): convergent(A) -> convergent(lim(A))
theorem limits_converge_2: forall A in Seq(Seq(R)): convergent(A) and (forall k in 1..50: convergent(A(k))) -> convergent(lim(A))
` },
  { name: "Calculus", src: `# Views for functions of one and two variables. Drag the sliders, and zoom into any picture.
import analysis, functions

show taylor(sin, 0, 5)
show tangent(x => x^3 - x, 0.5)
show funcseq(n => (x => x^n), 0, 1)
show heatmap((x, y) => sin(x) * cos(y), 3)
show field((x, y) => (-y, x - y/3))

integral(x => exp(-x^2), -5, 5)
taylor(exp, 0, 4)(1)

explain differentiable_at
check differentiable_implies_continuous
check continuous_implies_differentiable
` },
  { name: "Algebra and metrics", src: `import algebra, metric

show cayley(add_mod(6), Zmod(6))
show cayley(compose, Sym(3))

explain is_group
check groups_commute
order(3, mul_mod(7), 1)

show unitballs()
explain is_metric
explain is_norm
check UnitBall(1) ⊆ UnitBall(2)
check convex_set(UnitBall(0.5))
` },
  { name: "Geometry", src: `# Shapes are sets, so everything that works for sets works for them.
def T := Triangle((0, 0), (2, 0), (1, 1.5))
def P := Polygon([(0, 0), (2, 0), (2, 1), (1, 0.4), (0, 1)])
show region(T, Disk((1, 0.5), 0.6), P)

area(T)
area(Disk((0, 0), 1))
centroid(T)
diameter(P)

check convex_set(T)
check convex_set(P)
check T ∩ Disk((1, 0.5), 0.6) ⊆ T

explain convex_set
check convex_union
` },
  { name: "Inequalities", src: `# Each claim is sampled numerically. The picture depends on how many
# variables the leading ∀ binds: one gives curves, two a grid, three or more a scatter.
import means

theorem am_gm: ∀ a, b ∈ [0, 5]: am(a, b) ≥ gm(a, b)

theorem bernoulli: ∀ x ∈ [-1, 3], n ∈ 1..6: (1 + x)^n ≥ 1 + n*x

theorem am_gm_3: ∀ a, b, c ∈ [0, 4]: (a + b + c)/3 ≥ cbrt(a*b*c)

theorem mean_chain: ∀ a, b ∈ [0.1, 5]: hm(a, b) ≤ gm(a, b) ≤ am(a, b) ≤ qm(a, b)

theorem cauchy_schwarz: ∀ x, y ∈ [-2, 2]²: |x[1]*y[1] + x[2]*y[2]| ≤ |x| * |y|

# Zoom into the failing stretch, then press "Sample this view".
conjecture square_beats_x: ∀ x ∈ [-2, 3]: x^2 ≥ x
` },
  { name: "Definitions and ε–δ", src: `# Write a definition once, then check it on concrete inputs.
# Checking a call to your own definition unfolds it and draws its quantifiers.

# f never decreases on [a, b].
def increasing(f, a, b) := forall x, y in [a, b]: x < y -> f(x) <= f(y)

check increasing(exp, -2, 2)
check increasing(cos, 0, 4)

# f is continuous at a.
def continuous_at(f, a) :=
  forall ε in (0, 1]: exists δ in (0, 1]:
    forall x in [a - δ, a + δ]: |f(x) - f(a)| < ε

def wiggle(x) := if x = 0 then 0 else x^2 * sin(1/x)
def step(x) := if x < 0 then 0 else 1

check continuous_at(wiggle, 0)
check continuous_at(step, 0)

import analysis
show epsdelta(wiggle, 0, 0.3)
` },
  { name: "Sets and regions", src: `# A set written in set-builder notation can be drawn, tested for membership and combined.
def disk := {p in R^2 | |p| <= 1}
def wave := {(x, y) in [-2, 2]^2 | |y - sin(3x)| < 0.3}
show region(disk, wave)

def cardioid := {(x, y) in R^2 | (x^2 + y^2 - x)^2 <= x^2 + y^2}
show region(cardioid)

theorem diamond: forall x, y in [-1.5, 1.5]: (x, y) in disk -> |x| + |y| <= 1.5
check (0.6, 0.6) in disk
check disk ⊆ Ball((0, 0), 1.01)
check disk ∩ wave ⊆ wave
check disk ⊆ wave
` },
  { name: "Number theory", src: `import numtheory

theorem fermat_little: forall p in Primes[3, 400], a in 2..40:
  gcd(a, p) = 1 -> powmod(a, p - 1, p) = 1

conjecture euler_prime_formula: forall n in 0..60: isprime(n^2 + n + 41)

plot phi(n) for n in 1..150

sum d in 1..100: phi(d)

show ulam(81)
` },
  { name: "Complex plane", src: `import complex

show domaincolor(z => (z^3 - 1) / (z^2 + 1), 2)

check |exp(i * pi) + 1| < 1e-10

theorem on_unit_circle: forall t in [0, 2 pi]: |exp(i * t)| = 1

theorem triangle_inequality: forall a, b, c, d in [-2, 2]:
  |(a + b*i) + (c + d*i)| <= |a + b*i| + |c + d*i|
` },
  { name: "Linear algebra", src: `import linalg

let M = [[2, 1], [1, 3]]
show transform(M)

det(M)
eigenvalues(M)
check det(M * M) = det(M)^2

# Points of ℝⁿ are built in: |x| is the length, x + y and 2x work coordinatewise.
theorem triangle: forall x, y in [-3, 3]^2: |x + y| <= |x| + |y|

conjecture dot_bounded_by_square: forall x, y in [-3, 3]^2: dot(x, y) <= dot(x, x)
` },
  { name: "Real analysis I: sequences and series", src: `# Real analysis I: sequences, limits and series.
# Every claim is checked on many examples; when one fails you get the simplest counterexample.
# Click any result to see why it holds or fails. Try "Is every condition needed?" on the lemmas.
import sequences, series

# 1. The definition of a limit, read in plain words and tried on example sequences.
explain converges_to

# 2. Convergent sequences are bounded. Bounded sequences need not converge.
check convergent_is_bounded
check bounded_converges

# 3. A proof sketch: each step is checked numerically, and the goal is tracked.
theorem one_over_n: converges_to(n => 1/n, 0)
proof:
  let ε
  choose N = ceil(1/ε) + 1
  let n
  have n > 1/ε
  so |1/n - 0| < ε

# 4. Series. The partial sums of the alternating harmonic series settle at ln 2.
show partial_sums(n => (-1)^(n+1) / n)
check term_test
check terms_to_zero_imply_summable
check convergent_is_absolute
check ratio_test

# 5. Which example series converge absolutely? (Try wilder examples: some are too slow for any finite check.)
explain absolutely_converges
` },
  { name: "Real analysis II: continuity and integration", src: `# Real analysis II: continuity, derivatives, the Riemann integral and uniform convergence.
import functions, analysis, integration, series

# 1. Continuity at a point, and what each part of the definition is for.
explain continuous_at
show epsdelta(x => if x = 0 then 0 else x * sin(1/x), 0, 0.2)

# 2. Differentiable implies continuous; not conversely.
check differentiable_implies_continuous
check continuous_implies_differentiable

# 3. The Riemann integral: midpoint rectangles first, then Darboux sums. Drag n: Thomae's function
#    closes the gap, slowly.
show riemann(x => x^2, 0, 1, 8)
show darboux(thomae, 0, 1)
explain integrable_on
check bounded_integrable
check ftc

# 4. Uniform convergence: one N for every x at once. Compare the two definitions:
explain uniformly_converges
show uniform(n => (x => x^n))
check pointwise_limit_continuous
check uniform_limit_continuous
` },
  { name: "Linear algebra", src: `# Linear algebra: row reduction, subspaces, determinants and eigenvalues.
import linalg

# 1. Row reduction, one step at a time, in exact fractions.
let A = [[1, 2, 3], [4, 5, 6], [7, 8, 10]]
show rref_steps(A, (1, 2, 3))
inv(A)

# 2. A singular matrix: its kernel and image are subspaces you can quantify over and draw.
let B = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
kernel(B)
image(B)
show subspace(kernel(B), image(B))
check forall v in kernel(B): B * v = (0, 0, 0)
check rank_nullity

# 3. Determinants: volume scaling, multiplicative but not additive.
show transform([[1, 1, 0], [0, 1, 0], [0, 0, 2]])
check det_product
check det_sum
check matrices_commute

# 4. Eigenvalues and eigenvectors. Drag θ until v and Mv line up.
show eigen([[2, 1], [1, 2]])
check cayley_hamilton
check all_diagonalizable
check symmetric_real_eigenvalues
` },
  { name: "Abstract algebra", src: `# Abstract algebra: structures are defined by axioms, and examples are checked against them.
import algebra

# 1. A group, its axioms (inherited from Magma, Semigroup and Monoid), and examples that break each one.
explain Group
check Group(Zmod(5), loop5, 0) in Group
show cayley(compose, Sym(3))

# 2. Theorems about all the small groups in the catalog.
check lagrange_order
check inverse_unique
check groups_are_abelian
check exponent_two_abelian

# 3. Rings and fields: ℤ/5 is a field, ℤ/6 isn't.
explain Field

# 4. A structure of your own: partial orders on 1..12.
structure Poset(X: Set, le: Fun) where
  reflexive: forall x in X: le(x, x)
  antisymmetric: forall x, y in X: le(x, y) and le(y, x) -> x = y
  transitive: forall x, y, z in X: le(x, y) and le(y, z) -> le(x, z)
check Poset(1..12, (a, b) => b mod a = 0) in Poset
check Poset(1..12, (a, b) => |a - b| <= 1) in Poset
` },
  { name: "Topology", src: `# Topology: open and closed sets in the plane, finite topological spaces, metric spaces.
import topology, metric

# 1. Open and closed, straight from the definitions.
check open({p in R^2 | |p| < 1})
check closed({p in R^2 | |p| <= 1})
check open_or_closed
check closed_iff_seq_closed

# 2. Topological spaces on finite sets: the axioms, and an example breaking each one.
explain TopologicalSpace
check T0_is_T1
check finite_T1_discrete

let sier = TopologicalSpace({1, 2}, {∅, {1}, {1, 2}})
closure_in(sier, {2})
interior_in(sier, {2})

# 3. Metric spaces. Nonnegativity follows from the other axioms: no example separates it.
explain MetricSpace
check reverse_triangle
` },
  { name: "Several variables and geometry", src: `# Several variables: surfaces, gradients, differentiability, level sets. Drag the 3D pictures to turn them.
import multivar

# 1. Graphs and parametric surfaces.
plot x^2 - y^2 for x in [-1, 1], y in [-1, 1]
plot ((2 + cos(v)) * cos(u), (2 + cos(v)) * sin(u), sin(v)) for u in [0, 2π], v in [0, 2π]
plot (cos(t), sin(t), t/6) for t in [0, 4π]

# 2. Gradients are perpendicular to level curves.
show gradient(p => p[1]^3 - 3*p[1]*p[2]^2)
check gradient_normal_to_level_curve

# 3. Partial derivatives don't make a function differentiable; mixed partials needn't agree.
check partials_give_differentiable
check mixed_partials_agree

# 4. Linearization: shrink the radius and the map looks linear.
show linearize(p => (p[1]^2 - p[2]^2, 2*p[1]*p[2]), (1, 0.5))

# 5. Regular values: the sphere is smooth; the cone has a singular point.
show level_surface(p => p[1]^2 + p[2]^2 + p[3]^2, 1)
show level_surface(p => p[1]^2 + p[2]^2 - p[3]^2, 0)
check regular_value(p => p[1]^2 + p[2]^2 + p[3]^2, 1, 2, 3)
` },
  { name: "One object, many faces", src: `# One object, many faces. Much of mathematics is knowing that one thing can be described in several
# ways, and picking the way that makes the problem easy. Two tools here: "concept" states a notion
# with all its equivalent definitions and compares them on examples; "interpret" shows every way the
# libraries know of looking at a value.
import manifolds, linalg, complex, numtheory, analysis, multivar, algebra, functions, graphs, logic

# A concept of your own: one name, several forms. Each form is also a definition of its own
# (square_root_of_squares, …), and the concept itself means the first. The card compares them.
# examples: x in [-3, 3]
concept abs_value(x: R) where
  cases: if x >= 0 then x else -x
  root_of_square: sqrt(x^2)
  largest: max(x, -x)

# Forms that are NOT equivalent show where they part: a "convergent" definition missing a condition.
# examples: n in 1..12
concept even_number(n: Z) where
  remainder: n mod 2 = 0
  last_digit: (n mod 10) in {0, 2, 4, 6, 8}
  half_is_whole: floor(n/2) = n/2
  wrong: n mod 4 = 0

# Library concepts: a prime said four ways (Wilson's theorem among them), coprime pairs (Bézout).
explain prime
interpret coprime(12, 35)

# A matrix: a linear map, its eigenvectors, a quadratic form, a row reduction.
interpret [[2, 1], [1, 2]]
# Invertible, four ways, on example matrices, and positive definite, three ways.
explain invertible
explain posdef

# A number: as a product of primes and in other bases; an irrational as a continued fraction.
interpret 2024
interpret (1 + sqrt(5))/2
# A complex number: cartesian, polar, exponential, and as a rotation-scaling of the plane.
interpret 1 + i

# A function: its graph, its slopes, its Taylor polynomials, and the derivative of its area function.
interpret x => x*exp(-x^2)
# Convex on [−1, 1], three ways: chords, increasing slopes, midpoints.
explain convex_on
# A function of two variables: a surface, a contour map, a gradient field.
interpret (x, y) => x*y*exp(-(x^2 + y^2)/2)

# A permutation, as a list of images, in cycles, two-line notation and as a matrix.
interpret (3, 1, 2, 5, 4)
# A point of the plane is also an arrow, with a length and an angle; (2, 3, 1) is also a permutation.
interpret (3, 4)
interpret (2, 3, 1)

# A submanifold: a chart, local equations, a local graph, a straightening.
interpret parametrized((u, v) => ((1 + 0.4*cos(v))*cos(u), (1 + 0.4*cos(v))*sin(u), 0.4*sin(v)), [[0, 2*pi], [0, 2*pi]])
interpret graph_manifold(x => x^3 - x)
show manifold(zero_set((x, y) => x^4 + y^2 - 1))

# A graph: a drawing, a matrix, lists, a spectrum. Trees, bipartite, connected and Eulerian graphs,
# each said several ways and compared on all 64 graphs with 4 vertices.
interpret petersen_graph()
explain tree
explain bipartite

# A formula of logic: a truth table, normal forms, a region of a Venn diagram.
interpret (p, q, r) => (p -> q) and (q -> r)
explain implication
explain included
` },
  { name: "Graphs, logic, Fourier series, numerics", src: `# Graphs, logic, Fourier series and numerical methods: four smaller libraries, each with its views,
# its lemmas and its concepts.
import graphs, logic, fourier, numerics, linalg

# --- Graphs. Statements about SmallGraphs(4) are checked on all 64 graphs with 4 vertices.
let G = Graph(6, ((1, 2), (2, 3), (3, 1), (3, 4), (4, 5), (5, 6), (6, 4)))
show coloring(G)
show bfs_layers(cube_graph(3), 1)
# Euler's theorem: an Euler circuit exactly when the edges are connected and every degree is even.
show euler(complete_graph(5))
show euler(complete_graph(4))
check handshake
check forall G in SmallGraphs(4): connected(G) or connected(complement_graph(G))
# A tree on n vertices has n − 1 edges: checked on every graph with 4 vertices.
check forall G in SmallGraphs(4): tree(G) -> nedges(G) = 3
explain connected_graph
explain eulerian
# The Petersen graph is not Hamiltonian, though every degree is 3 and it is very symmetric.
hamiltonian(petersen_graph())
chromatic_number(petersen_graph())

# --- Logic. Over Bool every case is tried, so these are proved, not sampled.
check de_morgan_and
check forall p, q, r in Bool: (p -> q) and (q -> r) -> (p -> r)
equivalent((p, q) => p -> q, (p, q) => not q -> not p)
equivalent((p, q) => p -> q, (p, q) => q -> p)
show venn((a, b, c) => (a or b) and not c)
explain equivalence

# --- Fourier series on [−π, π]: the square wave as a sum of sines, with Gibbs's overshoot at the jumps.
show fourier_series(square_wave, 9)
show parseval(triangle_wave)
check bessel
explain even_function
explain odd_function

# --- Numerical methods.
show newton(x => x^3 - 2*x - 5, 3)
show bisection(x => cos(x) - x, 0, 1)
show interpolation(runge, -1, 1)
check newton_quadratic
check runge_phenomenon
newton_root(x => x^3 - 2*x - 5, 3)
bisection_root(x => cos(x) - x, 0, 1)
` },
  { name: "The counterexample zoo", src: `# The counterexample zoo: the famous functions and sets most counterexamples are made of.
# They know exact facts about themselves (with the reason; click a result to see it), and numbers
# know whether they are rational, so the Dirichlet and Thomae functions are evaluated exactly.
import zoo

# 1. The famous functions, and what they are famous for.
explain Famous
facts_of(thomae)
check continuous_is_somewhere_differentiable
check continuous_at_a_point_is_continuous_nearby
check differentiable_at_a_point_is_continuous_nearby

# 2. Thomae's function is continuous exactly at the irrationals, and integrable all the same.
check forall a in [0, 1]: continuous_at(thomae, a) <-> not is_rational(a)
show darboux(thomae, 0, 1)
check integrable_has_few_discontinuities

# 3. Famous sets: length, countability and density come apart.
check measure_zero_is_countable
check nowhere_dense_has_measure_zero
check closed(CantorSet) and not open(CantorSet)
check not open(Q) and not closed(Q)

# 4. Numbers that know whether they are rational: the simplest counterexamples are exact.
check forall x in [0, 1]: is_rational(x)
check forall x in Irrationals: x^2 != 2
check forall x in Irrationals, y in Irrationals: not is_rational(x + y)
` },
  { name: "Asymptotics and thresholds", src: `# Exact answers from formulas: limits, series and local behaviour, decided by expanding the formula
# (n → ∞, or x → a), not by sampling. And families whose properties switch at a threshold.
import asymptotics

# 1. Series: each part of a term gets its own test, with the reason.
series_test(n => (-1)^n/sqrt(n))
series_test(n => (-1)^n/sqrt(n) + 1/n)
series_test(n => 1/(n*ln(n+1)))
series_test(n => n!/n^n)
check alternating_with_a_nudge

# 2. The comparison test needs a ≤ b only eventually, and eventually is decided exactly:
eventually_le(n => ln(n)^10, n => sqrt(n))
check comparison_test

# 3. Thresholds: Σ 1/nᵖ converges exactly when p > 1 …
show family(p => summable(n => 1/n^p), 0, 3)

# … |x|ᵃ·sin(1/x) is continuous at 0 for a > 0, differentiable for a > 1, with a continuous derivative for a > 2 …
show family(a => differentiable_at(x => if x = 0 then 0 else abs(x)^a * sin(1/x), 0), 0, 3)
show family(a => continuously_differentiable_at(x => if x = 0 then 0 else abs(x)^a * sin(1/x), 0), 0, 4)

# … and |x|ᵃ·sin(1/|x|ᵇ) has a continuous derivative at 0 exactly when a > b + 1.
show family2((a, b) => continuously_differentiable_at(x => if x = 0 then 0 else abs(x)^a * sin(1/abs(x)^b), 0), [0, 5], [0.25, 3])

# 4. Which value of c makes sin(x)/x continuous at 0?
describe_family(c => continuous_at(x => if x = 0 then c else sin(x)/x, 0), -2, 2)
` },
  { name: "Group structure and diagrams", src: `# Groups as structure: subgroups, cosets, quotients, homomorphisms, and diagrams that are checked.
# Hover the pictures; click a subgroup in a lattice to see its cosets.
import groups

# 1. Subgroup lattices: normal subgroups are filled. Q₈ has only normal subgroups, yet isn't abelian.
show subgroup_lattice(D4)
show subgroup_lattice(Q8)
check all_normal_gives_abelian

# 2. Cayley graphs: each coset of ⟨first generator⟩ on its own circle.
show cayley_graph(Q8)
show cayley_graph(Dihedral(5))

# 3. Cosets and quotients: for a normal subgroup the blocks are one color each, the table of G/H.
let V = generated(S4, {(2, 1, 4, 3), (3, 4, 1, 2)})
show coset_table(V, S4)
iso_name(quotient(S4, V))
show coset_table(generated(S3, {(2, 1, 3)}), S3)

# 4. Homomorphisms and the first isomorphism theorem.
let K = generated(S3, {(2, 3, 1)})
let sign = x => if x in K.G then 0 else 1
show homomorphism(sign, S3, Cyclic(2))
check first_isomorphism_theorem

# 5. A diagram, checked at every element: the sign map factors through S₃/K.
let Q = quotient(S3, K)
let q = Q.projection
let sbar = c => if c = Q.e then 0 else 1
diagram sign_factors:
  sign: S3 -> Cyclic(2)
  q: S3 -> Q
  sbar: Q -> Cyclic(2)
  sbar ∘ q = sign

# 6. An exact sequence 1 → A₃ → S₃ → ℤ/2 → 1.
let into = x => K.e
let incl = x => x
let out = x => 0
diagram short_exact:
  into: Cyclic(1) -> K
  incl: K -> S3
  sign: S3 -> Cyclic(2)
  out: Cyclic(2) -> Cyclic(1)
  exact at K
  exact at S3
  exact at Cyclic(2)

# 7. Theorems over every group of order ≤ 12, and the converse of Lagrange failing at A₄.
check lagrange_subgroups
check lagrange_converse
check normal_is_transitive
show class_equation(A4)
` },
  { name: "Dynamical systems", src: `# Dynamical systems: differential equations, phase portraits, and iterated maps.
# Click inside a phase portrait or a slope field to follow the solution through that point.
import dynamics

# 1. Slope fields: y′ = y − t. Every solution bends away from the line y = t + 1, except that line.
show slope_field((t, y) => y - t, -3, 3, -3, 4)

# 2. Solutions as functions: y′ = y with y(0) = 1 is e^t, and Euler's method approaches it slowly.
let growth = solution((t, y) => y, 0, 1)
growth(1)
euler((t, y) => y, 0, 1, 1, 100)
check euler_first_order

# 3. Planar systems: equilibria colored by type. Lotka–Volterra: predators and prey circle a center.
show phase_portrait(p => (p[1]*(1 - p[2]), p[2]*(p[1] - 1)), 3)
equilibria(p => (p[1]*(1 - p[2]), p[2]*(p[1] - 1)), 3)

# The van der Pol oscillator: an unstable spiral inside a limit cycle that attracts everything.
show phase_portrait(p => (p[2], (1 - p[1]^2)*p[2] - p[1]), 3)
show time_series(p => (p[2], (1 - p[1]^2)*p[2] - p[1]), 0, (0.1, 0), 30)

# 4. Stability from the linearization: a negative trace is not enough (a saddle can have one),
#    negative trace and positive determinant is.
check negative_trace_stable
check trace_det_stable

# 5. Maps: the logistic map x ↦ r x(1 − x). A fixed point for r < 3, then period doubling, then chaos.
show cobweb(logistic(2.8), 0.1, 40)
show cobweb(logistic(3.83), 0.1, 80)
show bifurcation(logistic, 2.5, 4)
check logistic_settles
check logistic_always_settles
period(logistic(3.5), 0.3)
lyapunov(logistic(4), 0.3)

# Every orbit of cos ends at the same point, the Dottie number.
check dottie
` },
  { name: "Curves and surfaces", src: `# Curves and surfaces: curvature, torsion, the moving frame, and how surfaces bend.
import curves

# 1. Plane curves: the moving frame and the osculating circle, whose radius is 1/κ. Slide t.
show frenet(t => (3*cos(t), sin(t)), 0, 2*pi)
show curvature_comb(t => (3*cos(t), sin(t)), 0, 2*pi)
check circle_curvature
check curvature_reparametrized

# 2. Space curves: T, N and the binormal B. The helix has constant curvature and constant torsion.
show frenet(t => (cos(t), sin(t), t/2), 0, 4*pi)
check helix_frame
check constant_curvature_plane

# 3. Turning: a closed curve turns through at least 2π (Fenchel); a knot through more than 4π.
show frenet(t => (sin(t) + 2*sin(2t), cos(t) - 2*cos(2t), -sin(3t)), 0, 2*pi)
check fenchel
check turning_exactly_2pi

# 4. Surfaces colored by curvature: a torus is positively curved outside, negatively inside,
#    and its total curvature is 0. A sphere's is 4π (Gauss–Bonnet).
show surface_curvature((u, v) => ((2 + cos(v))*cos(u), (2 + cos(v))*sin(u), sin(v)), 0, 2*pi, 0, 2*pi)
show surface_curvature((u, v) => (u, v, u*v), -1.2, 1.2, -1.2, 1.2)
check sphere_curvatures
check gauss_bonnet

# 5. Minimal surfaces have mean curvature 0, and K = 0 doesn't make a surface a plane.
show surface_curvature((u, v) => (cosh(v)*cos(u), cosh(v)*sin(u), v), 0, 2*pi, -1.2, 1.2)
check minimal_surfaces
check zero_K_zero_H
` },
  { name: "Probability", src: `# Probability: exact chances on finite spaces, distributions, and the two great limit theorems.
import probability

# 1. Equally likely outcomes, counted exactly. Two dice: a 7 is the likeliest sum.
chance(dice(2), r => r[1] + r[2] = 7)
chance(dice(2), r => r[1] + r[2] = 12)
check seven_likeliest

# Conditional probability: given that the sum is at least 10, how likely is a 6 on the first die?
chance(dice(2), r => r[1] = 6, r => r[1] + r[2] >= 10)

# Independence is subtle: three events can be independent in pairs but not together.
check pairwise_gives_independent

# 2. The birthday problem, and the Monty Hall game played thousands of times.
check birthday_23
show monty_hall(3000)

# 3. Distributions: probabilities, mean and spread, and the cumulative distribution function.
show distribution(Binomial(20, 0.3))
show distribution(Exponential(1))
prob(Normal(0, 1), [-1, 1])
check total_probability
check chebyshev
check mean_is_median

# 4. The law of large numbers: running averages settle at the mean, within about 2σ/√n.
show lln(Die(6), 2000)
sample_mean(Die(6), 100000)

# 5. The central limit theorem: sums of n draws, standardized, approach the bell curve whatever
#    the distribution. Slide n from 1 upward.
show clt(Exponential(1), 1)
show clt(Die(6), 2)

# 6. Random walks stray about √n from where they started.
show random_walk(2000, 8)
` },
  { name: "Smallest counterexamples", src: `# Every small model, checked exhaustively: when a claim fails, the first counterexample is a smallest
# one; when it holds, it holds for every model of that size. Infinite spaces come with known facts.
import models, topspaces, zoo

# 1. Relations: is "symmetric and transitive" enough for reflexive? (x R y and y R x give x R x …)
check symmetric_transitive_is_reflexive
check not_transitive_only
# The counterexample drawn: symmetric and transitive, yet 2 is not related to itself.
show relation_graph({X = {1, 2}, rel = (a, b) => a = 1 and b = 1})

# 2. Groups and monoids: the smallest non-abelian group, the smallest non-cyclic abelian group,
#    the smallest non-commutative monoid.
explain AllGroups
check small_groups_are_abelian
check abelian_groups_are_cyclic
check prime_order_cyclic
check monoids_are_commutative

# 3. Orders and maps. The divisors of 12, ordered by divisibility.
show hasse({X = {1, 2, 3, 4, 6, 12}, le = (a, b) => b mod a = 0})
check finite_poset_has_greatest
check pigeonhole
check injective_is_surjective

# 4. Topology: finite spaces computed, infinite ones by their known facts.
# The smallest T0 space that is not T1: {1} is open but {2} is not.
show open_sets({X = {1, 2}, T = {{}, {1}, {1, 2}}})
check T0_gives_T1
check T1_gives_hausdorff
check connected_gives_path_connected
check metrizable_gives_separable
check compact_gives_hausdorff

# 5. Built from pieces: neither part of 1_ℚ + (1 − 1_ℚ) = 1 is continuous.
check continuous_sum_has_a_continuous_part
` },
  { name: "Proof sketches", src: `# Proof sketches: write the steps of a proof; each is checked numerically in its context.
# let takes an arbitrary element, assume takes a hypothesis, choose answers an "exists",
# have states an intermediate fact, so concludes. A wrong step gets a counterexample.
# Equations and inequalities are checked exactly where algebra can settle them: every step of the
# first proof is "exact", so it is a complete proof. Further down: cases, induction,
# contradiction, and citing a lemma.

theorem square_continuous: forall ε > 0: exists δ > 0: forall x in R: |x - 1| < δ -> |x^2 - 1| < ε
proof:
  let ε
  choose δ = min(1, ε / 3)
  let x
  assume |x - 1| < δ
  have |x + 1| < 3 by the triangle inequality
  have |x^2 - 1| = |x - 1| * |x + 1|
  so |x^2 - 1| < ε

# The same theorem with a careless choice of δ: the last step fails, with a counterexample.
theorem square_continuous_again: forall ε > 0: exists δ > 0: forall x in R: |x - 1| < δ -> |x^2 - 1| < ε
proof:
  let ε
  choose δ = ε
  let x
  assume |x - 1| < δ
  so |x^2 - 1| < ε

theorem am_gm: forall a, b in [0, 10]: sqrt(a*b) <= (a + b)/2
proof:
  let a, b
  have (sqrt(a) - sqrt(b))^2 >= 0
  have a + b - 2*sqrt(a*b) >= 0
  so sqrt(a*b) <= (a + b)/2

# Is every condition of AM–GM needed? Drop or change one at a time:
vary am_gm

theorem archimedes: forall x in [0, 100]: exists n in 1..1000: n > x
proof:
  let x
  choose n = floor(x) + 1
  so n > x

# Cases: indented blocks. The cases are checked to cover everything, and each must reach the goal.
# Change "x >= 0" to "x > 0" and the split misses x = 0.
theorem abs_triangle: forall x, y in R: |x + y| <= |x| + |y|
proof:
  let x, y
  case x + y >= 0:
    have |x + y| = x + y
    so |x + y| <= |x| + |y|
  otherwise:
    have |x + y| = -x - y
    so |x + y| <= |x| + |y|

# Induction: "induction on n" splits the goal into a base case and a step. The step's goal is
# shown under it; "let n" and "assume" take it apart as usual.
theorem odd_sum: forall n in N: sum k in 1..n: (2k - 1) = n^2
proof:
  induction on n
  base:
    so sum k in 1..0: (2k - 1) = 0^2
  step:
    let n
    assume sum k in 1..n: (2k - 1) = n^2
    have sum k in 1..n + 1: (2k - 1) = (sum k in 1..n: (2k - 1)) + 2n + 1
    so sum k in 1..n + 1: (2k - 1) = (n + 1)^2

# Equations are checked by exact algebra where they can be: this induction is proved outright,
# every step "exact", the step using the induction hypothesis to rewrite the shorter sum.
theorem telescoping: forall n in N: sum k in 1..n: 1/(k*(k + 1)) = n/(n + 1)
proof:
  induction on n
  base:
    so sum k in 1..0: 1/(k*(k + 1)) = 0/(0 + 1)
  step:
    let n
    assume sum k in 1..n: 1/(k*(k + 1)) = n/(n + 1)
    so sum k in 1..n + 1: 1/(k*(k + 1)) = (n + 1)/(n + 2)

# Contradiction: suppose the goal fails and reach "so false". When the theorem is true the
# supposition never holds on the samples, so the steps after it hold vacuously.
theorem no_rational_sqrt2: forall q in 1..40: forall p in 0..80: p^2 != 2q^2
proof:
  let q, p
  contradiction
  have p^2 = 2q^2
  have p mod 2 = 0
  so false

# Citing a lemma: "by sq_mono" matches the step to the lemma's conclusion (a = x, b = 3) and
# checks what the lemma needs: both in [0, 100] and x ≤ 3. On [−5, 3] it wouldn't apply.
lemma sq_mono: forall a, b in [0, 100]: a <= b -> a^2 <= b^2
theorem sq_bound: forall x in [0, 3]: x^2 <= 9
proof:
  let x
  so x^2 <= 3^2 by sq_mono
` },
];
if (typeof window !== 'undefined') window.TEST_NOTEBOOKS = NOTEBOOKS;
if (typeof module !== 'undefined') module.exports = NOTEBOOKS;
})();
