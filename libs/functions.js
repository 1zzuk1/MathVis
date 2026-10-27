MathVizNotation(`library functions
# Properties of real functions: continuity, uniform continuity, differentiability, monotonicity, boundedness, convexity.
# Written in notebook notation; explain any of them to see which example functions have the property.

# f is continuous at a.
# examples: f in Functions(R), a in {-1, 0, 1}
def continuous_at(f: Fun, a: R) := forall ε in (0, 1]: exists δ in (0, 1]: forall x in [a - δ, a + δ]: |f(x) - f(a)| < ε

# f is continuous at every point of [a, b].
# examples: f in Functions(R), a in {-1}, b in {1}
def continuous_on(f: Fun, a: R, b: R) := forall c in [a, b]: continuous_at(f, c)

# f is uniformly continuous on [a, b]: one δ works for every point. (Pairs of points are written x and x + h with |h| ≤ δ, which samples close pairs well.)
# examples: f in Functions(R), a in {-1}, b in {1}
def uniformly_continuous_on(f: Fun, a: R, b: R) := forall ε in (0, 1]: exists δ in (0, 1]: forall x in [a, b], h in [-δ, δ]: x + h in [a, b] -> |f(x + h) - f(x)| < ε

# f is differentiable at a: its difference quotients converge (checked numerically).
# examples: f in Functions(R), a in {-1, 0, 1}
def differentiable_at(f: Fun, a: R) := defined(lim h -> 0: (f(a + h) - f(a)) / h)

# f never decreases on [a, b].
# examples: f in Functions(R), a in {-1}, b in {1}
def increasing_on(f: Fun, a: R, b: R) := forall x, y in [a, b]: x <= y -> f(x) <= f(y)

# f is bounded on [a, b].
# examples: f in Functions(R), a in {-1}, b in {1}
def bounded_on(f: Fun, a: R, b: R) := exists M in (0, 1000]: forall x in [a, b]: |f(x)| <= M

# f is convex on [a, b], three ways: every chord lies above the graph; the slopes of chords increase from left to right; the graph lies below the chord at every midpoint (enough for continuous f).
# examples: f in Functions(R), a in {-1}, b in {1}
concept convex_on(f: Fun, a: R, b: R) where
  chords: forall x, y in [a, b], t in [0, 1]: f((1 - t)*x + t*y) <= (1 - t)*f(x) + t*f(y)
  slopes: forall x, y, z in [a, b]: x < y and y < z -> (f(y) - f(x))/(y - x) <= (f(z) - f(y))/(z - y)
  midpoints: forall x, y in [a, b]: f((x + y)/2) <= (f(x) + f(y))/2

# f is Lipschitz on [a, b] with constant L.
# examples: f in Functions(R), a in {-1}, b in {1}, L in {1, 10}
def lipschitz_on(f: Fun, a: R, b: R, L: R) := forall x, y in [a, b]: |f(x) - f(y)| <= L*|x - y|

# A function that is differentiable at a point is continuous there.
lemma differentiable_implies_continuous: forall f in Functions(R), a in {-1, 0, 1}: differentiable_at(f, a) -> continuous_at(f, a)

# The converse fails: |x| is continuous but not differentiable at 0.
conjecture continuous_implies_differentiable: forall f in Functions(R), a in {-1, 0, 1}: continuous_at(f, a) -> differentiable_at(f, a)
`);
