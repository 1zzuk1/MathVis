/* Theorem Sketchpad UI — examples, running notebooks, saved notebooks, previews and start-up. */
'use strict';
(function () {
const APP = window.APP;
const { h, store, makeCard, makeCtx, runView, runClaim, runExplain } = APP;
const { MVError, esc, fmt, describeValue, splitStatements, parseStatement, pp, ppText, compile, compileDomain,
  execDefinition, checkNames, freshEnv, callValue, minmax, FIGS, renderAllFigures, resetTheme } = MV;
const $ = s => document.querySelector(s);

const LS_DRAFT = 'theorem-sketchpad.notebook.v2', LS_NOTEBOOKS = 'theorem-sketchpad.notebooks', LS_CURRENT = 'theorem-sketchpad.current', LS_AUTO = 'theorem-sketchpad.autorun';

/* ================= Examples ================= */

const EXAMPLES = [
  { name: "Analysis II · 1–3 The Riemann integral", src: `# Analysis II, chapters 1–3: the Riemann integral. Numbers such as (1.12) follow the chapters'
# definitions and theorems.
import integration, analysis, functions, series, multint

# 1.1–1.4 Step functions and their integral Σ (xₖ₊₁ − xₖ)·cₖ. More partition points change nothing.
let xs = [0, 1/3, 1]
let cs = [3, 1]
step_integral(xs, cs)
check step_integral_well_defined
check forall λ in [-2, 2]: step_integral(xs, λ*cs) = λ*step_integral(xs, cs)

# 1.6–1.10 Upper and lower integrals from step functions above and below f; continuous functions
#     are integrable. Drag n: the gap closes. Thomae's function closes it too, Dirichlet's never.
show step_integral(x => x^2 + sin(4*x), [0, 2])
show darboux(thomae, 0, 1)
check continuous_integrable
check bounded_integrable

# 1.11 Riemann sums: any points ξₖ in the pieces. Example 1.11: left sums of x on [0, y] are y²/2 − δy/2.
check forall n in 1..50, y in [0.5, 3]: riemann_sum(x => x, 0, y, n, 0) ~= y^2/2 - (y/n)*y/2
check riemann_sums_converge
show riemann(x => x^2, 0, 1, 8)

# 1.12 The mean value theorem for integrals: f takes its average value somewhere.
check mean_value_integral

# 2.3–2.8 The fundamental theorem of calculus. F(x) = ∫ₐˣ f has slope f(x) everywhere.
show antiderivative(x => cos(2*x) + 0.3, 0, 4)
check ftc
# 2.10–2.13 Substitution and integration by parts (Example 2.13: ∫₁ᵇ ln x dx = b ln b − b + 1).
check forall b in [0, 2]: integral(x => 2*x*cos(x^2), 0, b) ~= sin(b^2)
check by_parts_log
# 2.14 The trapezoidal rule and its error term.
check trapezoid_error

# 3.6 |∫ f| ≤ ∫ |f|, but ∫ fg is not (∫ f)(∫ g).
check integral_triangle
check integral_product

# 3.7–3.8 Improper integrals as limits. ∫₁^∞ 1/xˢ exists exactly for s > 1, ∫₀¹ 1/xˢ for s < 1;
#     ∫₋₁¹ 1/√(1 − x²) = π (Example 3.8(v)). Drag R towards the end.
show improper(x => 1/x^2, 1, inf)
show improper(x => 1/x, 1, inf)
check power_integrals
check improper_integral(x => 1/sqrt(1 - x^2), -1, 1) ~= pi
# 3.9 The integral test: Σ f(k) and ∫₁^∞ f converge together for decreasing f ≥ 0.
check integral_test
` },
  { name: "Analysis II · 4 Sequences of functions", src: `# Analysis II, chapter 4: sequences of functions and power series. Numbers such as (4.8) follow the
# chapter's definitions and theorems. A sequence of functions F gives the function F(n) for each n.
import series, analysis, functions

# 4.1–4.5 Pointwise and uniform convergence. xⁿ on [0, 1] converges pointwise to a jump, not uniformly:
#     the sup-distance to the limit stays 1. Drag n.
show uniform(n => (x => x^n))
explain uniformly_converges
check forall n in 1..100: sup_norm(x => x^n - (if x = 1 then 1 else 0), 0, 1) > 0.9
# 4.6 A uniform limit of continuous functions is continuous; a pointwise one need not be.
check uniform_limit_continuous
check pointwise_limit_continuous

# 4.7–4.8 The sup norm, and the Weierstrass M-test: Σ sin(kx)/k² converges uniformly.
check m_test
show funcseq(n => (x => sum k in 1..n: sin(k*x)/k^2), 0, 6)

# After 4.8: each |x|^(1+1/n) is differentiable, they converge uniformly to |x|, which isn't.
check powers_of_abs_differentiable
check powers_of_abs_uniform
check uniform_limit_differentiable

# 4.10–4.12 Power series converge uniformly inside their radius, and may be differentiated term by
#     term. Drag n: inside (−r, r) the partial sums settle, outside they fly apart.
show power_series(k => 1, 0)
show power_series(k => if k mod 2 = 1 then (-1)^((k - 1)/2)/k! else 0, 0)
check radii
check power_series_uniform
check power_series_derivative
#     Example 4.12: the cosine series.
check forall x in [-3, 3]: power_sum(k => if k mod 2 = 0 then (-1)^(k/2)/k! else 0, 0, 40)(x) ~= cos(x)

# 4.13 Uniform convergence lets the integral pass to the limit; pointwise convergence alone doesn't:
#     n tents of base 2/n and height n tend to 0 pointwise but always have area 1 (Question 4.5).
check pointwise_integral_swap
show funcseq(n => (x => n * max(0, 1 - |n*x - 1|)), 0, 2)

# 4.5 (appendix) A power series that converges only at 0: Σ kᵏ xᵏ.
radius_of_convergence(k => k^k)
` },
  { name: "Analysis II · 5 ℝⁿ, norms, open and closed sets", src: `# Analysis II, chapter 5: functions in ℝⁿ, metrics, norms, open and closed sets. Numbers such as
# (5.12) follow the chapter's definitions and theorems.
import metric, topology, multivar, series

# 5.1–5.2 Functions of several variables: a graph over the plane, and a map of the plane to itself.
plot x^2 - y^2 for x in [-1, 1], y in [-1, 1]
show field(p => (-p[2], p[1]))

# 5.3–5.4 Metrics and norms by their axioms; each example that fails one shows which.
explain MetricSpace
explain is_norm
check reverse_triangle

# 5.6–5.12 p-norms. Young's inequality, then Hölder's and Minkowski's; Minkowski fails below p = 1.
show unitballs()
check young
check holder
check minkowski
check minkowski_small_p
# 5.14 All p-norms are comparable: ‖x‖∞ ≤ ‖x‖_q ≤ ‖x‖ₚ ≤ n^(1/p)‖x‖∞ for p ≤ q.
check pnorm_bounds

# 5.15 Functions are vectors too: the sup norm on C([0, 1]) obeys the triangle inequality.
check forall f, g in {sin, cos, x => x^2, x => 1 - x}: sup_dist(x => f(x) + g(x), x => 0, 0, 1) <= sup_dist(f, x => 0, 0, 1) + sup_dist(g, x => 0, 0, 1)

# 5.16–5.20 Balls and open sets: every point of an open set has a ball around it inside the set.
explain open
check open({p in R^2 | |p| < 1})
check open({p in R^2 | |p| <= 1})
# 5.17 (Hausdorff) Two different points have disjoint balls around them.
check forall x, y in [-1, 1]^2: x != y -> exists r in (0, 1]: forall z in Ball(x, r): |z - y| >= r

# 5.21–5.23 Boundary points: a set is open exactly when it contains none of them.
explain boundary_point
check boundary_point((1, 0), {p in R^2 | |p| < 1})
check boundary_point((0.5, 0), {p in R^2 | |p| < 1})

# 5.24–5.25 Finite unions and intersections of open sets are open; an infinite intersection need not be:
#     ⋂ (−1/n, 1/n) = {0}.
check union_of_open
check forall n in 1..100: open(Ioo(-1/n, 1/n))
#     No ball around 0 fits in all of them: every (−ε, ε) pokes out of some (−1/n, 1/n).
check forall ε in (0, 1]: exists n in 1..10^12: 1/n < ε

# 5.26–5.30 Closed sets: complements of open ones, and they keep their limits.
check intersection_of_closed
check closed_iff_seq_closed
check open_or_closed
` },
  { name: "Analysis II · 6 Limits and continuity in metric spaces", src: `# Analysis II, chapter 6: limits and continuity in metric spaces. Numbers such as (6.4) follow
# the chapter's definitions and theorems. Click any result to see why it holds or fails.
import metric, topology, multivar, linalg

# 6.1 Convergence in a metric space: d(xₖ, a) → 0. Read the definition, tried on examples.
explain converges_in

# 6.3 In ℝⁿ the choice of p-norm doesn't matter. The ε-balls are a diamond, a disk and a square:
#     drag ε and compare the three N(ε). Each is finite exactly when the others are.
show norm_convergence(k => (cos(k)/k, 1 + sin(k)/k), (0, 1))
check pnorm_chain
check forall s in Seq(R^2): convergent(s) -> converges_in(d_taxicab, s, lim(s)) and converges_in(d_max, s, lim(s))
#     A metric that doesn't come from a norm can change everything (Question 6.2):
check discrete_same_limits

# 6.4 A set is closed exactly when the limits of its convergent sequences stay in it.
check closed_iff_seq_closed
check seq_closed({p in R^2 | |p| <= 1})
check seq_closed({p in R^2 | |p| < 1})

# 6.5–6.6 Cauchy sequences and completeness: [0, 1] is complete, (0, 1] is not (1/k has no limit
#     there), and neither is the open disk.
check complete(Icc(0, 1))
check complete(Ioc(0, 1))
check complete({p in R^2 | |p| < 1})

# 6.9 and 6.16 Continuity: along every sequence, or with ε and δ. xy/(x² + y²) has a limit along
#     each line through 0, but a different one on each line.
show approach(p => if p = (0, 0) then 0 else p[1]*p[2]/(p[1]^2 + p[2]^2), (0, 0))
check continuous_at_point(p => if p = (0, 0) then 0 else p[1]*p[2]/(p[1]^2 + p[2]^2), (0, 0))
#     x²y/(x⁴ + y²) gives 0 on every line, and still isn't continuous: follow the parabolas.
show approach(p => if p = (0, 0) then 0 else p[1]^2*p[2]/(p[1]^4 + p[2]^2), (0, 0))
# 6.15 Polynomials are continuous.
check continuous_at_point(p => p[1]^3*p[2] - 2*p[1]*p[2] + 5, (1, -1))
# 6.17 The distance to a fixed point changes no faster than the distance itself, in every metric.
check forall d in Metrics(R^2): forall x, y in (-1..1)^2: |d(x, (0, 0)) - d(y, (0, 0))| <= d(x, y)

# 6.20–6.22 A linear map is continuous exactly when it is bounded. ‖A‖ is the most A stretches the
#     unit ball: the image of the disk (or of the diamond, for the 1-norm) fits in the ball of radius ‖A‖.
show operator_norm([[1, 2], [0, 1]])
show operator_norm([[1, 2], [0, 1]], 1)
check forall A in Matrices(2), x in [-2, 2]^2: |A * x| <= opnorm(A) * |x|
# 6.21(i) ‖A‖ ≤ √(nm)·max|aᵢₖ|, here 2·max|aᵢₖ|.
check forall A in Matrices(2): opnorm(A) <= 2 * max(max(|A[1][1]|, |A[1][2]|), max(|A[2][1]|, |A[2][2]|))
# 6.21(iii) Differentiation is not bounded in the sup-norm: on [0, 1], xⁿ has norm 1 and its
#     derivative n·xⁿ⁻¹ has norm n, so no constant C works.
check exists C in [1, 100]: forall n in 1..200: (sup x in [0, 1]: |n*x^(n - 1)|) <= C * (sup x in [0, 1]: |x^n|)
# Question 6.5: without linearity, continuity gives no bound |f(x)| ≤ C|x|.
check exists C in (0, 1000]: forall x in R: |cos(x)| <= C * |x|

# 6.23–6.24 Preimages: {f < c} is open and {f ≤ c} is closed when f is continuous.
check open({p in R^2 | p[1]^2 - p[2] < 1})
check closed({p in R^2 | p[1]^2 - p[2] <= 1})
#     A jump breaks it: here {f < 1/2} is the closed half-plane x₁ ≤ 0.
check open({p in R^2 | (if p[1] > 0 then 1 else 0) < 1/2})
` },
  { name: "Analysis II · 7 Compactness", src: `# Analysis II, chapter 7: compactness. Numbers such as (7.6) follow the chapter's definitions and
# theorems. Drag the sliders in the pictures.
import compactness, topology, metric, functions

# 7.1–7.2 Compact: every open cover has a finite subcover. The intervals (−1, 1 − 1/k) cover [0, 1),
#     but no finitely many of them do: drag n and the points near 1 stay red.
show cover(Ico(0, 1), k => Ioo(-1, 1 - 1/k))
check finite_subcover(Ico(0, 1), k => Ioo(-1, 1 - 1/k))
#     [0, 1] needs one more set, around 1, and then the first few suffice.
show cover(Icc(0, 1), k => if k = 1 then Ioo(0.9, 1.1) else Ioo(-1, 1 - 1/k))
check finite_subcover(Icc(0, 1), k => if k = 1 then Ioo(0.9, 1.1) else Ioo(-1, 1 - 1/k))
#     The same in the plane: disks of radius 1 − 1/k cover the open disk, never finitely many.
show cover({p in R^2 | |p| < 1}, k => Ball((0, 0), 1 - 1/k))

# 7.6 and 7.8 (Heine–Borel) In ℝⁿ, compact means closed and bounded.
check compact({p in R^2 | |p| <= 1})
check compact({p in R^2 | |p| < 1})
check compact({p in R^2 | p[1] >= 0})
check compact({p in R^2 | |p[1]| + |p[2]| <= 2 and |p| >= 1})

# 7.10–7.11 (Bolzano–Weierstrass) A bounded sequence has a convergent subsequence. Halve the box,
#     keep the half with the most terms still to come, take the next term in it, and repeat.
#     This sequence winds round and round towards the unit circle and never converges; a subsequence does.
show bolzano(k => ((1 + 1/k)*cos(k), (1 + 1/k)*sin(k)))
show bolzano(k => sin(k))

# 7.13 A continuous function on a compact set attains its maximum and minimum. On the open disk the
#     supremum of x₁ + x₂ sits on the circle, outside the set: the hollow dot.
show extremes(p => p[1] + p[2]^2 - p[1]*p[2], {p in R^2 | |p| <= 1})
show extremes(p => p[1] + p[2], {p in R^2 | |p| < 1})
check extreme_values
check extreme_values_open
check attains_max(x => 1/x, Ioc(0, 1))

# 7.15 (Heine–Cantor) Continuous on a compact set means uniformly continuous. Each point a has its δₐ;
#     the balls B(a, δₐ/2) cover the set, finitely many suffice, and the smallest of their δ's
#     serves every point. On (0, 1], δₐ for sin(1/x) shrinks to 0 and no finite subcover exists.
show uniform_delta(x => sqrt(x), Icc(0, 1), 0.2)
show uniform_delta(x => sin(1/x), Ioc(0, 1), 0.4)
check heine_cantor
check heine_cantor_open

# 7.16 All norms on ℝⁿ are equivalent. The proof takes γ, the least value of the norm on the
#     1-sphere: the sphere is compact, so γ is attained, at a point ≠ 0, and γ > 0.
show equivalent_norms(x => sqrt(x[1]^2 + 3*x[2]^2))
show equivalent_norms(x => max(|x[1]|, 2*|x[2] - x[1]|))
#     |x₁| alone is no norm: it vanishes at (0, 1), so γ = 0.
show equivalent_norms(x => |x[1]|)
` },
  { name: "Analysis II · 8 Derivatives in ℝⁿ", src: `# Analysis II, chapter 8: derivatives in ℝⁿ. Numbers such as (8.7) follow the chapter's definitions
# and theorems. partial(f, i) differentiates a formula exactly, so identities about derivatives are
# proved, not just sampled.
import multivar, linalg

# 8.1 f is differentiable at x when f(x + z) = f(x) + Az + φ(z) with φ(z)/‖z‖ → 0. Shrink the
#     radius: the error is an ever smaller multiple of it, and the grid's image looks linear.
show linearize(p => p[1]^2 + 2*p[2]^2, (1, 1))
show linearize(p => (p[1]^2 - p[2]^2, 2*p[1]*p[2]), (1, 0.5))
# 8.2 Differentiable implies continuous.
check differentiable_continuous
# 8.3 The derivative of x ↦ Ax is A, at every point.
check forall p in [-2, 2]^2: jacobian(x => [[1, 2], [3, 4]] * x, p) = [[1, 2], [3, 4]]

# 8.4–8.5 Partial derivatives. A box with sides x₁, x₂, x₃ has this surface area and volume:
def area(x1, x2, x3) := 2*(x1*x2 + x1*x3 + x2*x3)
def volume(x1, x2, x3) := x1*x2*x3
check forall x1, x2, x3 in R: partial(area, 1)(x1, x2, x3) = 2*x2 + 2*x3
check forall x1, x2, x3 in R: partial(volume, 2)(x1, x2, x3) = x1*x3

# 8.7 Totally differentiable ⇒ partially differentiable, but not conversely: xy/(x² + y²) has both
#     partial derivatives at 0 and isn't even continuous there.
check partials_give_differentiable
#     Continuous partial derivatives are enough (8.7(ii)):
check differentiable_at_point(p => p[1]^2*p[2] + sin(p[2]), (0.5, 1))

# 8.10–8.12 The directional derivative is Df(x)·v. At the unit cube, stretching length and width
#     (v = (1, 1, 0)) grows the surface area at rate 8 and the volume at rate 2.
def box(p) := (2*(p[1]*p[2] + p[1]*p[3] + p[2]*p[3]), p[1]*p[2]*p[3])
jacobian(box, (1, 1, 1))
ddir(box, (1, 1, 1), (1, 1, 0))
check forall p in [-2, 2]^3, v in [-1, 1]^3: ddir(box, p, v) = jacobian(box, p) * v
# Question 8.4: doubling v doubles the directional derivative, and −v flips its sign.
check forall p in [-2, 2]^3, v in [-1, 1]^3: ddir(box, p, 2*v) = 2*ddir(box, p, v) and ddir(box, p, -v) = -ddir(box, p, v)

# 8.13–8.14 The gradient points where f climbs fastest: no unit vector beats it. The arrows cross
#     the level curves at right angles.
def g(p) := p[1]^2*p[2] - p[2]^3/3
show gradient(g)
check forall p in [-1, 1]^2, t in [0, 2*pi]: ddir(g, p, (cos(t), sin(t))) <= |grad(g, p)|

# 8.15 Gradient descent on (x₁ − 1)² + (x₂ − 2)² from 0 with α = 1/4: f is divided by 4 at every step.
def f(p) := (p[1] - 1)^2 + (p[2] - 2)^2
def x(k) := if k = 0 then (0, 0) else x(k - 1) - 1/4 * grad(f, x(k - 1))
check forall k in 0..30: f(x(k)) = 5 / 4^k
# Question 8.5: drag α. At 1/2 one step lands on the minimum, at 1 the steps bounce back and forth,
#     and beyond 1 they run away.
show descent(f, (0, 0), 1/4)

# 8.16 The gradient of ‖y‖² is 2y.
check forall y in [-2, 2]^3: grad(y => y[1]^2 + y[2]^2 + y[3]^2, y) = 2*y
# 8.5 The chain rule: D(H ∘ G)(x) = DH(G(x))·DG(x).
def G(p) := (p[1]*p[2], p[1] + p[2]^2)
def H(q) := (sin(q[1]), q[1]*q[2])
check forall p in [-1, 1]^2: jacobian(p => H(G(p)), p) ~= jacobian(H, G(p)) * jacobian(G, p)

# 8.19–8.20 (Schwarz) With continuous partial derivatives the order of differentiation doesn't
#     matter. Example 8.20, proved exactly:
def c(x1, x2) := cos(x1*x2)
check forall x1, x2 in R: partial(partial(partial(c, 1), 1), 2)(x1, x2) = partial(partial(partial(c, 2), 1), 1)(x1, x2)
check forall x1, x2 in R: partial(partial(partial(c, 2), 1), 1)(x1, x2) = sin(x1*x2)*x1*x2^2 - 2*cos(x1*x2)*x2
# 8.21 So the Hessian is symmetric …
check forall p in [-1, 1]^2: hessian(p => cos(p[1]*p[2]), p) = transpose(hessian(p => cos(p[1]*p[2]), p))
#     … unless the second derivatives aren't continuous: xy(x² − y²)/(x² + y²) at 0.
check mixed_partials_agree
` },
  { name: "Analysis II · 9–10 Taylor, extrema, fixed points", src: `# Analysis II, chapters 9–10: Taylor's theorem, extrema, and Banach's fixed point theorem.
# Numbers such as (9.15) follow the chapters' definitions and theorems.
import multivar, linalg, metric

# 9.3–9.6 Taylor polynomials in ℝⁿ. Drag the degree k and shrink the radius: the error divided
#     by radiusᵏ⁺¹ stays bounded.
show taylor_surface(p => exp(p[1])*sin(p[2]), (0.3, 0.2))
check taylor_remainder
#     The degree-2 polynomial is f(x₀) + ∇f(x₀)·z + ½ zᵀH z (Remark 9.4); for a quadratic it is f itself.
check forall x in [-2, 2]^2: taylor_poly(p => p[1]^2 - 3*p[1]*p[2] + 2*p[2], (1, 1), 2)(x) ~= x[1]^2 - 3*x[1]*x[2] + 2*x[2]

# 9.5 (with k = 0) The mean value theorem along a segment: some point between x and x + z has the
#     average slope.
def h(p) := sin(p[1]) + p[1]*p[2]^2
check forall x in [-1, 1]^2, z in [-1, 1]^2: exists θ in [0, 1]: h(x + z) - h(x) = dot(grad(h, x + θ*z), z)

# 9.13–9.14 Definite matrices: the eigenvalues, and Sylvester's leading minors, agree.
positive_definite([[3, 1], [1, 2]])
leading_minors([[3, 1], [1, 2]])
sym_eigenvalues([[-3, 1], [1, 2]])
check sylvester
#     The three characterizations side by side: eigenvalues, leading minors, and xᵀAx > 0. Click a cell
#     to see that form checked; [[1, 1], [1, 1]] is only semidefinite, so all three say no.
explain posdef
interpret [[3, 1], [1, 2]]

# 9.10–9.16 Extrema. At a local minimum the gradient vanishes; at a critical point a positive
#     definite Hessian gives a strict local minimum, a negative definite one a maximum.
#     Example 9.16: f(x) = xᵀAx + bᵀx + c with A = [[3, 1], [1, 2]], b = (1, 1), c = 5.
def f(x1, x2) := 3*x1^2 + 2*x1*x2 + 2*x2^2 + x1 + x2 + 5
critical_points(f)
hessian_test(f, (-1/10, -1/5))
check f(-1/10, -1/5) = 97/20
check grad(f, (-1/10, -1/5)) = (0, 0)
#     With A = [[−3, 1], [1, 2]] the only critical point is a saddle.
def g(x1, x2) := -3*x1^2 + 2*x1*x2 + 2*x2^2 + x1 + x2 + 5
hessian_test(g, (1/14, -2/7))
show extrema(p => p[1]^3 - 3*p[1] + p[2]^2 - p[2]^4/4, 2)
check hessian_test_min
#     The test can't decide everything: x⁴ + y⁴ has a minimum at 0 with Hessian 0.
check local_min_needs_hessian

# 10.6 (Banach's fixed point theorem) A contraction of a closed set into itself has exactly one
#     fixed point, and the iterates reach it at least as fast as κᵐ. cos on [0, 1] has κ = sin 1.
lipschitz_constant(x => cos(x), Icc(0, 1))
show banach(x => cos(x), 0, Icc(0, 1))
show banach(p => (cos(p[2])/2, sin(p[1])/2 + 0.3), (1, 1), {p in R^2 | |p| <= 2})
check banach_fixed_point
check banach_unique
#     x² maps [0, 1] into itself but isn't a contraction there.
check all_contractions
` },
  { name: "Analysis II · 11 Integrals in ℝⁿ", src: `# Analysis II, chapter 11: the Riemann integral in ℝⁿ. Numbers such as (11.8) follow the chapter's
# definitions and theorems. integrate(f, Q) integrates over a cuboid Q; f may take (x, y) or a point.
import multint, multivar, analysis

# 11.1 Rectangles (cuboids) and their volume.
let Q = Cuboid([-1, 1], [-1, 1])
vol(Q)
vol(Cuboid([0, 3], [0, 2], [0, 2]))

# 11.2–11.9 Step functions below and above f, and the upper and lower integrals. Drag n: for a
#     continuous f the gap ∫ψ − ∫φ shrinks to 0, so f is Riemann integrable.
show step_integral((x, y) => x^2 + y^2, Q)
show step_integral(x => sin(3*x) + x, [0, 2])
check forall n in 1..12: lower_step_integral((x, y) => x^2 + y^2, Q, n) <= 8/3 and 8/3 <= upper_step_integral((x, y) => x^2 + y^2, Q, n)
check continuous_integrable_rect
#     Boundedness is needed: near x = 0 no step function stays above 1/x.
check all_integrable_rect

# 11.11–11.13 Fubini: integrate slice by slice. Example 11.13(i): ∫ over [−1, 1]² of x₁² + x₂² is 8/3.
show fubini((x, y) => x^2 + y^2, Q)
check integrate((x, y) => x^2 + y^2, Q) ~= 8/3
check fubini_continuous
#     Without continuity the order can matter: here the two orders give π/4 and −π/4.
check fubini_always

# 11.14 Sets between two graphs. The hemisphere of Example 11.13(ii) has volume 2π/3.
check integral_between((x, y) => sqrt(1 - x^2 - y^2), -1, 1, x => -sqrt(1 - x^2), x => sqrt(1 - x^2)) ~= 2*pi/3
#     The same over the disk as a set (a grid estimate):
integral_over(p => sqrt(1 - p[1]^2 - p[2]^2), {p in R^2 | |p| <= 1})

# 11.15–11.20 Integrals over part of the arguments: differentiate under the integral. Example 11.20
#     finds ∫₀ᵇ x² cos x dx this way: −2 sin b + 2b cos b + b² sin b.
check differentiate_under_integral
check forall b in [0, 3]: integrate(x => x^2*cos(x), [0, b]) ~= -2*sin(b) + 2*b*cos(b) + b^2*sin(b)

# 11.21–11.22 The transformation formula: ∫_Φ(A) f = ∫_A f(Φ)·|det DΦ|. Polar coordinates stretch
#     areas by r; Example 11.22: ∫ over the unit disk of ‖x‖ is 2π/3.
def polar(r, φ) := (r*cos(φ), r*sin(φ))
check forall r in [0, 2], φ in [0, 2*pi]: det(jacobian(polar, (r, φ))) = r
show change_of_variables(polar, Cuboid([0, 1], [0, 2*pi]))
check integrate((r, φ) => r * r, Cuboid([0, 1], [0, 2*pi])) ~= 2*pi/3
check polar_coordinates
` },
  { name: "Analysis II · 12 Vector analysis", src: `# Analysis II, chapter 12: vector analysis. Numbers such as (12.8) follow the chapter's definitions
# and theorems. A chart is a function of one parameter (a curve) or two (a surface).
import multint, multivar, linalg, manifolds

# 12.1–12.3 Charts: injective, with DΦ of full rank. The circle needs more than one chart: on
#     [0, 2π] the angle chart meets itself.
def circle(t) := (cos(t), sin(t))
check forall t in [0, 2*pi]: chart_rank(circle, t) = 1
injective_on(circle, [0, 1.9*pi])
injective_on(circle, [0, 2*pi])
#     A cusp: t ↦ (t², t³) has DΦ = 0 at t = 0, so it is no chart there.
check forall t in [-1, 1]: chart_rank(t => (t^2, t^3), t) = 1

# 12.4–12.7 Tangent and normal spaces. Drag y along the curve or over the surface.
show chart(circle, [0, 2*pi])
show chart((u, v) => (sin(u)*cos(v), sin(u)*sin(v), cos(u)), Cuboid([0.2, 3], [0, 6]))
show chart(t => (t^2, t^3), [-1, 1])
#     For M = {F = 0} the normal space is spanned by ∇F (Remark 12.7(iv)): on the circle ∇F is p itself.
check forall t in [0, 2*pi]: dot(tangent_vectors(circle, t)[1], grad(p => p[1]^2 + p[2]^2 - 1, circle(t))) ~= 0

# Four descriptions of a submanifold. Near each of its points M is the image of a chart, the set of
#     solutions of local equations, the graph of a function of some of the coordinates, and flat after
#     a change of coordinates. interpret builds all four from the one M is given by; drag the point.
#     An ellipsoid given by an equation:
interpret zero_set((x, y, z) => x^2/4 + y^2 + z^2 - 1)
#     A curve of the plane given by a chart: the implicit function theorem turns it into equations and a graph.
interpret parametrized(t => (cos(t) + 0.3*cos(2*t), sin(t) - 0.3*sin(2*t)), [0, 2*pi])
#     The descriptions agree: at points on M each says yes, at points pushed off M each says no.
explain on_manifold
#     The implicit function theorem: near (0.6, 0.8) the circle is the graph y = √(1 − x²); at (1, 0) it has to be x = g(y).
show implicit_function((x, y) => x^2 + y^2, (0.6, 0.8))
#     The inverse function theorem: polar coordinates are invertible near any point with r ≠ 0.
show inverse_function((r, t) => (r*cos(t), r*sin(t)), (1, 0.5))
#     Extrema on a submanifold: where ∇f is normal to M (Lagrange multipliers). f = x + 2y on the circle.
show lagrange(p => p[1] + 2*p[2], zero_set((x, y) => x^2 + y^2 - 1))
check constrained_max(p => p[1] + 2*p[2], zero_set((x, y) => x^2 + y^2 - 1)) ~= sqrt(5)

# 12.8–12.11 Integrals over submanifolds: ∫_M f dS = ∫_W f(Φ(y)) √g_Φ(y) dy. Lengths and areas.
check circle_length
check sphere_area
#     The Gramian of a graph (u, v, h(u, v)) is 1 + |∇h|² (Example 12.11(iii)).
check forall u, v in [-1, 1]: gram((u, v) => (u, v, u^2 - v*u), (u, v)) ~= 1 + (2*u - v)^2 + u^2
#     The value doesn't depend on the chart (Remark 12.10): the upper half circle as a graph.
check surface_integral(p => p[2], t => (t, sqrt(1 - t^2)), [-1, 1]) ~= surface_integral(p => p[2], circle, [0, pi])

# 12.12–12.13 Line integrals. The work along a curve, and its sign flip when the curve is reversed.
show work(p => (-p[2], p[1]), t => (cos(t), 2*sin(t)), 0, 2*pi)
check reverse_orientation
# 12.16 For a gradient field only the end points matter.
check gradient_theorem

# 12.17 Green: ∫∫ curl F = ∮ F · ds; in the plane Gauss is the same idea with div and the outward flux.
show green(p => (p[1]*p[2], p[1]^2 + p[2]), t => (1.5*cos(t), sin(t) + 0.3*sin(2*t)), 0, 2*pi)
check green_disk
# 12.18–12.19 Stokes and Gauss in space: the flux out of the unit sphere equals ∫∫∫ div F over the ball.
check gauss_ball
#     The flux of p ↦ p out of the unit sphere is 4π: div p = 3, times the ball's volume 4π/3.
check flux(p => p, (u, v) => (sin(u)*cos(v), sin(u)*sin(v), cos(u)), Cuboid([0, pi], [0, 2*pi])) ~= 4*pi
# 12.21(iii) ∫ Δf = the flux of ∇f: for f = x² + y² + z², Δf = 6 and the flux through the sphere is 8π.
check forall p in [-1, 1]^3: laplacian(q => q[1]^2 + q[2]^2 + q[3]^2, p) = 6
` },
];

/* ================= Editors ================= */

const KEYWORD_DOCS = {
  forall: 'forall x in S: P — P holds for every x in S.', exists: 'exists x in S: P — P holds for some x in S.',
  theorem: 'theorem name: claim — check a claim and draw it.', lemma: 'lemma name: claim — like theorem.', conjecture: 'conjecture name: claim — like theorem.',
  check: 'check claim — check a claim and draw it.',
  concept: 'concept name(x) where form: … form: … — one notion, several equivalent definitions, compared on examples.',
  interpret: 'interpret name(x) — every form of a concept at x; interpret value — every way of looking at a value.',
  explain: 'explain name — show a definition, lemma, function or set, and try it on examples.',
  def: 'def f(x: R) := … — define a function, set or value.', import: 'import name — load a library.', plot: 'plot f(x) for x in [a, b].',
  show: 'show view(…) — open a view from a library.', where: 'e where a = …, b = … — local definitions.', lim: 'lim n -> inf: s(n) — a limit.',
  sum: 'sum k in 1..n: … — a finite sum.', sup: 'sup x in S: f(x) — the supremum over samples.', inf: 'inf x in S: f(x) — the infimum over samples.',
};

let completionCache = null;
function completions() {
  if (completionCache) return completionCache;
  const out = Object.entries(KEYWORD_DOCS).map(([name, doc]) => ({ name, kind: 'keyword', doc }));
  const env = APP.env;
  if (env) {
    for (const name in env) {
      const v = env[name];
      const kind = MV.DEFS.get(v) ? 'definition' : v && v.__claim ? v.kind : v && v.__domain ? 'set' : typeof v === 'function' ? (v.domainCtor ? 'space' : 'function') : 'value';
      out.push({ name, kind, doc: APP.docFor(name, env) });
    }
  }
  for (const lib of MV.REG.values()) {
    if (lib.error || (env && [...MV.ACTIVE.libs].includes(lib.name))) continue;
    for (const [name] of Object.entries(lib.docs || {})) out.push({ name, kind: `in ${lib.name}`, doc: `${lib.docs[name]} (adds import ${lib.name})`, lib: lib.name });
  }
  return (completionCache = out);
}

// Library names about a topic, for the editor: "?compact" or a word like "derivative".
function topicCompletions(query) {
  const active = new Set(MV.ACTIVE.libs);
  return MV.findTopic(query, { limit: 14 }).map(e => {
    const needs = !active.has(e.lib) && !['core', 'catalog', 'geometry'].includes(e.lib);
    return { name: e.name, kind: `${e.kind} · ${e.lib}`, view: e.kind === 'view', lib: needs ? e.lib : null,
      doc: (e.doc || `A ${e.kind} of the ${e.lib} library.`) + (needs ? ` (adds import ${e.lib})` : '') };
  });
}
// Accepting a name from a library that isn't imported adds it to the notebook's first import line,
// or puts an import line above the first statement.
function addImport(lib) {
  const ta = editor.ta, src = ta.value;
  const m = /^import[ \t]+([\w \t,]+)$/m.exec(src);
  if (m && !/\bas\b/.test(m[1])) {
    if (m[1].split(',').map(x => x.trim()).includes(lib)) return;
    ta.setRangeText(`, ${lib}`, m.index + m[0].length, m.index + m[0].length, 'preserve');
  } else {
    // After the comment lines at the top.
    const lines = src.split('\n');
    let k = 0, at = 0;
    while (k < lines.length && /^\s*(#.*)?$/.test(lines[k]) && lines[k].trim()) { at += lines[k].length + 1; k++; }
    ta.setRangeText(`import ${lib}\n`, at, at, 'preserve');
  }
  APP.toast && APP.toast(`Added import ${lib}`);
}

let draftTimer = 0, autoTimer = 0;
const editor = APP.makeEditor($('#notebookEditor'), {
  onRun: () => run(),
  complete: completions,
  findTopic: topicCompletions,
  onImport: addImport,
  onInput: () => {
    clearTimeout(draftTimer);
    draftTimer = setTimeout(saveCurrent, 400);
    if ($('#autorun').checked) { clearTimeout(autoTimer); autoTimer = setTimeout(run, 900); }
  },
});
APP.editor = editor;
APP.libEditor = APP.makeEditor($('#libEditor'), { lang: 'js' });
const src = editor.ta;

document.querySelectorAll('[data-ins]').forEach(b => b.addEventListener('click', () => {
  src.focus();
  src.setRangeText(b.dataset.ins, src.selectionStart, src.selectionEnd, 'end');
  src.dispatchEvent(new Event('input'));
}));

APP.gotoLine = function (line, endLine = line) {
  showTab('notebook');
  const lines = src.value.split('\n');
  let a = 0;
  for (let i = 0; i < line - 1; i++) a += lines[i].length + 1;
  let b = a;
  for (let i = line - 1; i < endLine; i++) b += (lines[i] || '').length + 1;
  src.focus();
  src.setSelectionRange(a, Math.max(a, b - 1));
  const lh = parseFloat(getComputedStyle(src).lineHeight) || 21;
  src.scrollTop = Math.max(0, (line - 4) * lh);
  editor.sync();
  if (window.matchMedia('(max-width: 900px)').matches) src.scrollIntoView({ block: 'center' });
};

/* ================= Running statements ================= */

APP.OUT = $('#cards');
const OUT = APP.OUT;

function runPlot(ast, env, card) {
  card.formula(ast.exprs.map(e => pp(e)).join(', ') + ' <span class="fkw">for</span> ' + MV.ppBinders(ast.binders, true));
  ast.exprs.forEach(e => checkNames(e, env, ast.binders.flatMap(MV.binderNames)));
  const xb = ast.binders[0], yb = ast.binders[1];
  if (xb.pattern) throw new MVError('plot needs a single variable, as in "plot f(x) for x in [0, 1]".');
  if (yb && !yb.pattern && ast.exprs.some(e => MV.freeNames(e).has(yb.name))) return plotSurface(ast, env, card, xb, yb);
  const D = compileDomain(xb.dom)(env);
  const yr = yb ? compileDomain(yb.dom)(env).bounds() : null;
  const fs = ast.exprs.map(x => compile(x, { q: 1 }));
  if (D.kind === 'interval' && !D.integer && ast.exprs.some(e => MV.needsExact(e, env))) return plotByKind(ast, env, card, xb, D, fs);
  const discrete = !!(D.integer || (D.kind === 'finite' && D.numeric));
  let xs;
  if (D.kind === 'interval' && !D.integer) {
    const [a, b] = D.bounds();
    xs = Array.from({ length: 1001 }, (_, k) => a + (b - a) * k / 1000);
  } else xs = D.sample(4000, { grid: true }).filter(x => typeof x === 'number').sort((a, b) => a - b);
  if (!xs.length) throw new MVError(`The range ${D.describe()} is empty.`);
  const ctx = makeCtx(card);
  const valueAt = (f, i, x) => {
    const e = Object.create(env);
    e[xb.name] = x;
    let y = f(e);
    if (typeof y === 'function') y = callValue(y, [x], ppText(ast.exprs[i]));
    if (typeof y === 'boolean') y = y ? 1 : 0;
    if (y && y.__exact) y = +y;
    return y;
  };
  const series = fs.map((f, i) => xs.map(x => {
    const y = valueAt(f, i, x);
    if (typeof y !== 'number' && !(APP.isNumArr(y) && (y.length === 2 || y.length === 3))) throw new MVError(`plot needs numbers or points (of the plane or of space), but ${ppText(ast.exprs[i])} is ${describeValue(y)} at ${xb.name} = ${fmt(x)}.`);
    return [x, y];
  }));
  const parametric = series.every(s => s.every(([, y]) => APP.isNumArr(y)));
  if (series.every(s => s.every(([, y]) => APP.isNumArr(y) && y.length === 3))) {
    // Space curves.
    const fig = ctx.figure3d({});
    series.forEach((s, i) => {
      const pts = s.map(([, p]) => p), color = 'c' + (i % 6 + 1);
      if (discrete) fig.points(pts, { color, r: 2.4 }); else fig.curve(pts, { color, width: 2.2 });
    });
    ctx.legend(ast.exprs.map((e, i) => ({ label: `${ppText(e)} for ${xb.name} ∈ ${D.describe()}`, color: 'c' + (i % 6 + 1) })));
    for (const f of card.figs) f.render();
    return;
  }
  if (parametric) {
    const all = series.flatMap(s => s.map(([, p]) => p)).filter(p => p.every(Number.isFinite));
    const [a, b] = minmax(all.map(p => p[0])), [c, d] = minmax(all.map(p => p[1]));
    const pad = Math.max(b - a, d - c) * 0.08 || 1;
    const fig = ctx.figure({ x: [a - pad, b + pad], y: [c - pad, d + pad], square: true });
    series.forEach((s, i) => {
      const pts = s.map(([, p]) => p), color = 'c' + (i % 6 + 1);
      fig.curve(pts, { color, width: discrete ? 1 : 2, alpha: discrete ? 0.4 : 1 });
      if (discrete) fig.points(pts, { color, r: 2.4 });
    });
    ctx.legend(ast.exprs.map((e, i) => ({ label: `${ppText(e)} for ${xb.name} ∈ ${D.describe()}`, color: 'c' + (i % 6 + 1) })));
  } else {
    if (series.some(s => s.some(([, y]) => typeof y !== 'number'))) throw new MVError('plot can\'t mix numbers and points in one picture.');
    const [x0, x1] = minmax(xs);
    const fig = ctx.figure({ x: discrete ? [x0 - 0.5, x1 + 0.5] : [x0, x1], y: yr || undefined, xlabel: MV.idOut(xb.name, false), ylabel: yb ? MV.idOut(yb.name, false) : undefined });
    series.forEach((pts, i) => {
      const color = 'c' + (i % 6 + 1);
      if (discrete) fig.points(pts, { color, r: xs.length > 200 ? 1.8 : 2.8 });
      // Curves of real functions are re-evaluated when you zoom.
      else fig.curve(x => { try { const y = valueAt(fs[i], i, x); return typeof y === 'number' ? y : NaN; } catch (e) { return NaN; } }, { color, n: 1000 });
    });
    ctx.legend(ast.exprs.map((e, i) => ({ label: ppText(e), color: 'c' + (i % 6 + 1) })));
  }
  for (const f of card.figs) f.render();
}

/* A function that depends on whether x is rational (Dirichlet, Thomae, …) is plotted at exact
   rationals and exact irrationals, as two families of dots, since a float can't tell them apart. */
function plotByKind(ast, env, card, xb, D, fs) {
  const [a, b] = D.bounds();
  const xs = [...MV.EX.farey(a, b, 50, 1200), ...MV.withExactSampling(true, () => MV.EX.sampleExact(a, b, D.loOpen, D.hiOpen, 1600))];
  const ctx = makeCtx(card);
  const legend = [], series = [];
  fs.forEach((f, i) => {
    const rat = [], irr = [];
    for (const x of xs) {
      const e = Object.create(env);
      e[xb.name] = x;
      let y;
      try { y = MV.withExactSampling(true, () => f(e)); if (typeof y === 'function') y = callValue(y, [x], ppText(ast.exprs[i])); } catch (err) { continue; }
      if (typeof y === 'boolean') y = y ? 1 : 0;
      const v = +y;
      if (!Number.isFinite(v)) continue;
      (MV.EX.kindOf(x) === 'rational' ? rat : irr).push([+x, v]);
    }
    const c1 = 'c' + ((2 * i) % 6 + 1), c2 = 'c' + ((2 * i + 1) % 6 + 1);
    series.push([irr, c2, 1.8, 0.7], [rat, c1, 2.2, 1]);
    legend.push({ label: `${ppText(ast.exprs[i])} at rationals`, color: c1 }, { label: 'at irrationals', color: c2 });
  });
  // The whole range of values: the isolated high points are the point of such pictures.
  const ys = series.flatMap(([pts]) => pts.map(p => p[1]));
  const [y0, y1] = ys.length ? minmax(ys) : [0, 1], pad = (y1 - y0) * 0.06 || 0.5;
  const fig = ctx.figure({ x: [a, b], y: [y0 - pad, y1 + pad], xlabel: MV.idOut(xb.name, false) });
  for (const [pts, color, r, alpha] of series) fig.points(pts, { color, r, alpha });
  ctx.legend(legend);
  ctx.note('This depends on whether the input is rational, so it is drawn at exact fractions and exact irrationals (such as k + √2 and π multiples) instead of a curve.');
  for (const f of card.figs) f.render();
}

/* plot f(x, y) for x in I, y in J: the surface z = f(x, y). An expression giving points (x, y, z)
   is a parametric surface. */
function plotSurface(ast, env, card, xb, yb) {
  const DX = compileDomain(xb.dom)(env), DY = compileDomain(yb.dom)(env);
  const bx = DX.bounds && DX.bounds(), by = DY.bounds && DY.bounds();
  if (!bx || !by || !bx.every(Number.isFinite) || !by.every(Number.isFinite)) throw new MVError('A surface plot needs bounded ranges for both variables, as in plot x^2 - y^2 for x in [-1, 1], y in [-1, 1].');
  const fs = ast.exprs.map(x => compile(x, { q: 2 }));
  const ctx = makeCtx(card);
  const at = (f, i) => (u, v) => {
    const e = Object.create(env);
    e[xb.name] = u; e[yb.name] = v;
    let z = f(e);
    if (typeof z === 'function') z = callValue(z, [u, v], ppText(ast.exprs[i]));
    if (typeof z === 'boolean') z = z ? 1 : 0;
    return z;
  };
  const probe = at(fs[0], 0)((bx[0] + bx[1]) / 2 + 1e-3, (by[0] + by[1]) / 2 + 1e-3);
  const param = APP.isNumArr(probe) && probe.length === 3;
  if (!param && typeof probe !== 'number') throw new MVError(`A surface plot needs a number (a height) or a point (x, y, z), but ${ppText(ast.exprs[0])} is ${describeValue(probe)}.`);
  const fig = ctx.figure3d({ labels: param ? ['x', 'y', 'z'] : [MV.idOut(xb.name, false), MV.idOut(yb.name, false), 'z'], equal: param });
  const n = ast.exprs.length > 1 ? 28 : 40;
  fs.forEach((f, i) => fig.surface(at(f, i), { u: bx, v: by, n, color: ast.exprs.length > 1 ? 'c' + (i % 6 + 1) : undefined, alpha: ast.exprs.length > 1 ? 0.75 : 0.92 }));
  ctx.legend(ast.exprs.map((e, i) => ({ label: param ? ppText(e) : 'z = ' + ppText(e), color: ast.exprs.length > 1 ? 'c' + (i % 6 + 1) : 'c1' })));
  for (const f of card.figs) f.render();
}

APP.runPlot = runPlot;

function runShow(ast, env, card) {
  card.formula(pp({ type: 'call', f: { type: 'id', name: ast.name }, args: ast.args }));
  const view = MV.ACTIVE.views[ast.name];
  if (!view) {
    const lib = MV.VIEW_INDEX.get(ast.name);
    throw new MVError(lib ? `The ${ast.name} view comes from the ${lib} library. Add "import ${lib}" above this line.`
      : `There's no view called ${ast.name}. Views you can use now: ${Object.keys(MV.ACTIVE.views).join(', ')}.`);
  }
  ast.args.forEach(a => checkNames(a, env));
  if (view.doc) card.doc(view.doc);
  runView(card, view, ast.args.map(a => compile(a)(env)));
}

function runEval(ast, env, card) {
  checkNames(ast.expr, env);
  const v = compile(ast.expr)(env);
  card.formula(`${pp(ast.expr)} <span class="eq">=</span> <span class="val">${esc(fmt(v))}</span>`);
  if (typeof v === 'boolean') card.setStatus(v ? 'ok' : 'fail', v ? 'true' : 'false');
}

async function runStatement(ast, env, card, stmt) {
  if (ast.type === 'check') {
    card.formula(pp(ast.body));
    await runClaim(ast.body, env, card);
    if (ast.name && env[ast.name] === undefined) env[ast.name] = MV.makeClaim(ast.name, ast.body, env, ast.kind, MV.docOf(stmt).doc);
    if (ast.name) APP.lastClaim = env[ast.name];
  } else if (ast.type === 'proof') await APP.runProof(ast, env, card, stmt);
  else if (ast.type === 'diagram') APP.runDiagram(ast, env, card);
  else if (ast.type === 'explain') await runExplain(ast, env, card);
  else if (ast.type === 'interpret') await APP.runInterpret(ast, env, card);
  else if (ast.type === 'vary') await APP.runVary(ast, env, card);
  else if (ast.type === 'plot') runPlot(ast, env, card);
  else if (ast.type === 'show') runShow(ast, env, card);
  else runEval(ast, env, card);
}

const label = ast => ast.type === 'check' ? ast.kind : ast.type === 'eval' ? 'value' : ast.type;

let runId = 0;
const tick = () => MV.yieldNow();

async function run() {
  for (const c of APP.activeCtls) c.cancelled = true;   // a new run stops the previous one
  const id = ++runId;
  running = true;
  const runBtn = $('#run');
  runBtn.classList.add('busy');
  runBtn.querySelector('.label').textContent = 'Stop';
  await tick();
  OUT.replaceChildren();
  for (const f of [...FIGS]) if (!f.wrap.isConnected || OUT.contains(f.wrap)) FIGS.delete(f);
  editor.errors = new Set();
  completionCache = null;
  const stmts = splitStatements(src.value);
  APP.lastClaim = null;
  const parsed = stmts.map(s => { try { return { s, ast: parseStatement(s) }; } catch (err) { return { s, err }; } });
  const names = parsed.filter(p => p.ast && (['def', 'let', 'structure', 'concept'].includes(p.ast.type) || (p.ast.type === 'check' && p.ast.name))).flatMap(p => MV.definedNames(p.ast));
  const env = freshEnv(names);
  APP.env = env;
  APP.trackDefs(env, names);
  const pending = [];
  const t0 = performance.now();
  for (const { s: stmt, ast, err: parseErr } of parsed) {
    if (id !== runId) return;
    if (parseErr) {
      const card = makeCard(stmt, 'statement', null);
      card.error(parseErr instanceof MVError ? parseErr : new MVError(parseErr.message));
      continue;
    }
    if (['import', 'library', 'let', 'def', 'structure', 'concept'].includes(ast.type)) {
      APP.noteDef(env, stmt);
      try { execDefinition(ast, env, stmt); }
      catch (err) {
        const card = makeCard(stmt, ast.type, ast.name || null);
        card.formula(esc(stmt.text.trim().split('\n')[0]));
        card.error(err instanceof MVError ? err : new MVError(err.message));
        continue;
      }
      // A concept shows its forms side by side on its examples.
      if (ast.type === 'concept') {
        const card = makeCard(stmt, 'concept', ast.name);
        try { await APP.runConcept(MV.CONCEPTS.get(ast.name), env, card); }
        catch (err) { card.error(err instanceof MVError ? err : new MVError(err.message || String(err))); }
        if (id !== runId) return;
        await tick();
      }
      continue;
    }
    const card = makeCard(stmt, label(ast), ast.name && ast.type !== 'show' && ast.type !== 'explain' ? ast.name : ast.type === 'explain' ? ast.name : null);
    // With workers, a check runs in the background while the next statements start; a named one
    // is defined right away, so later statements can use it.
    if (ast.type === 'check' && APP.parallel()) {
      if (ast.name) {
        if (env[ast.name] === undefined) env[ast.name] = MV.makeClaim(ast.name, ast.body, env, ast.kind, MV.docOf(stmt).doc);
        APP.lastClaim = env[ast.name];
        APP.noteDef(env, stmt);
      }
      pending.push(runStatement(ast, env, card, stmt).catch(err => card.error(err instanceof MVError ? err : new MVError(err.message || String(err)))));
      continue;
    }
    try { await runStatement(ast, env, card, stmt); }
    catch (err) { card.error(err instanceof MVError ? err : new MVError(err.message || String(err))); }
    if (ast.type === 'check' && ast.name) APP.noteDef(env, stmt);
    if (id !== runId) return;
    await tick();
  }
  await Promise.all(pending);
  if (id !== runId) return;
  if (!stmts.length) OUT.append(h('p', 'empty', 'Write a statement on the left, such as theorem t: forall x in [0, 1]: x^2 <= x, then run it.'));
  summarize(performance.now() - t0);
  completionCache = null;
  editor.refresh();
  running = false;
  runBtn.classList.remove('busy');
  runBtn.querySelector('.label').textContent = 'Run';
}
APP.run = run;
APP.EXAMPLES = EXAMPLES;
let running = false;
function stopAll() {
  runId++;
  for (const c of APP.activeCtls) c.cancelled = true;
  running = false;
  const runBtn = $('#run');
  runBtn.classList.remove('busy');
  runBtn.querySelector('.label').textContent = 'Run';
}

function summarize(ms) {
  const cards = [...OUT.querySelectorAll('.card')];
  const n = { ok: 0, fail: 0, error: 0 };
  for (const c of cards) {
    const chip = c.querySelector('.chip:not([hidden])');
    if (!chip) continue;
    for (const k of Object.keys(n)) if (chip.classList.contains(k)) n[k]++;
  }
  const el = $('#summary');
  el.replaceChildren();
  el.append(h('span', 'sum-total', `${cards.length} result${cards.length === 1 ? '' : 's'}`));
  // Each chip steps through the results of its kind, unfolding the one it reaches.
  const jumper = (k, text) => {
    const b = h('button', 'chip ' + k, text);
    b.type = 'button';
    b.title = 'Go to the next one';
    let at = -1;
    b.addEventListener('click', () => {
      const list = [...OUT.querySelectorAll('.card')].filter(c => { const ch = c.querySelector('.chip:not([hidden])'); return ch && ch.classList.contains(k); });
      if (!list.length) return;
      at = (at + 1) % list.length;
      const c = list[at];
      if (c.card && c.classList.contains('folded')) c.card.setFolded(false);
      c.scrollIntoView({ block: 'start', behavior: 'smooth' });
      c.classList.remove('flash'); void c.offsetWidth; c.classList.add('flash');
    });
    el.append(b);
  };
  if (n.ok) jumper('ok', `${n.ok} hold`);
  if (n.fail) jumper('fail', `${n.fail} fail`);
  if (n.error) jumper('error', `${n.error} error${n.error === 1 ? '' : 's'}`);
  el.append(h('span', 'sum-time', `${(ms / 1000).toFixed(1)} s`));
  if (APP.pool) {
    const n = APP.pool.state === 'ready' ? APP.pool.workers.length : 0;
    const t = h('span', 'sum-threads', n ? `${n} threads` : '1 thread');
    t.title = n ? 'Claims are checked in background threads, side by side' : 'This browser checks claims on the page itself (no background threads here)';
    el.append(t);
  }
  if (cards.length > 1) {
    const allFolded = cards.every(c => c.classList.contains('folded'));
    const fb = h('button', 'btn small sum-fold', allFolded ? 'Unfold all' : 'Fold all');
    fb.type = 'button';
    fb.addEventListener('click', () => {
      const fold = fb.textContent === 'Fold all';
      for (const c of OUT.querySelectorAll('.card')) if (c.card) c.card.setFolded(fold);
      fb.textContent = fold ? 'Unfold all' : 'Fold all';
    });
    el.append(fb);
  }
}

$('#run').addEventListener('click', () => { if (running) stopAll(); else { run(); if (APP.toResults) APP.toResults(); } });

/* ================= Previews (from the Libraries tab and "Uses" chips) ================= */

APP.preview = async function (text, libName) {
  const host = $('#preview');
  const env = Object.create(APP.env || freshEnv());
  try { if (libName) MV.activate(libName, env); } catch (e) { /* reported below */ }
  const m = /^\s*(?:explain|check)\s+(\w+)/.exec(text);
  if (m && env[m[1]] === undefined) {
    const lib = MV.NAME_INDEX.get(m[1]);
    if (lib) { try { MV.activate(lib, env); } catch (e) { /* reported below */ } }
  }
  const stmt = { text, line: 0, endLine: 0, lines: [0], docLines: [] };
  let ast;
  try { ast = parseStatement(stmt); } catch (err) { return; }
  const card = makeCard(stmt, `preview · ${label(ast)}`, ast.name || null, host);
  card.el.classList.add('preview-card');
  const close = h('button', 'close-btn', '×');
  close.type = 'button';
  close.title = 'Close this preview';
  close.addEventListener('click', () => { card.clearBody(); card.el.remove(); });
  card.head.append(close);
  host.prepend(card.el);
  $('.right').scrollTop = 0;
  card.el.scrollIntoView({ block: 'start' });
  const status = h('p', 'note', 'Working…');
  card.body.append(status);
  await tick();
  status.remove();
  try { await runStatement(ast, env, card, stmt); }
  catch (err) { card.error(err instanceof MVError ? err : new MVError(err.message || String(err))); }
};

APP.importIntoNotebook = function (name) {
  if (!new RegExp(`^\\s*import\\b.*\\b${name}\\b`, 'm').test(src.value)) editor.set(`import ${name}\n` + src.value);
  saveCurrent();
  showTab('notebook');
  run();
};

/* ================= Notebooks: examples, your saved notebooks, and an unsaved draft ================= */

let NOTEBOOKS = [];
try { NOTEBOOKS = JSON.parse(store.get(LS_NOTEBOOKS, '[]')) || []; } catch (e) { NOTEBOOKS = []; }
// Notebooks are kept in this browser's storage (in the desktop app, the app's own).
const saveNotebooks = () => {
  store.set(LS_NOTEBOOKS, JSON.stringify(NOTEBOOKS));
};
APP.notebooks = () => NOTEBOOKS;
let current = store.get(LS_CURRENT, 'ex:0');
const exSel = $('#examples');

function fillSelect() {
  exSel.replaceChildren();
  const draft = h('option', null, 'Unsaved notebook');
  draft.value = 'draft';
  exSel.append(draft);
  const g1 = document.createElement('optgroup');
  g1.label = 'Examples';
  EXAMPLES.forEach((ex, i) => { const o = h('option', null, ex.name); o.value = 'ex:' + i; g1.append(o); });
  exSel.append(g1);
  const gc = document.createElement('optgroup');
  gc.label = 'Courses';
  (APP.COURSES || []).forEach((c, i) => { const o = h('option', null, c.name); o.value = 'co:' + i; gc.append(o); });
  if (gc.children.length) exSel.append(gc);
  if (NOTEBOOKS.length) {
    const g2 = document.createElement('optgroup');
    g2.label = 'Your notebooks';
    NOTEBOOKS.forEach(nb => { const o = h('option', null, nb.name); o.value = 'nb:' + nb.id; g2.append(o); });
    exSel.append(g2);
  }
  exSel.value = current;
  if (exSel.value !== current) { current = 'draft'; exSel.value = 'draft'; }
  $('#nbDelete').hidden = !current.startsWith('nb:');
  $('#nbDelete').textContent = 'Delete';
  $('#nbDelete').classList.remove('confirm');
}

function sourceOf(key) {
  if (key.startsWith('ex:')) return (EXAMPLES[+key.slice(3)] || EXAMPLES[0]).src;
  if (key.startsWith('co:')) return ((APP.COURSES || [])[+key.slice(3)] || EXAMPLES[0]).src;
  if (key.startsWith('nb:')) { const nb = NOTEBOOKS.find(n => 'nb:' + n.id === key); return nb ? nb.src : ''; }
  return store.get(LS_DRAFT, '');
}

function saveCurrent() {
  const text = src.value;
  if (current.startsWith('nb:')) {
    const nb = NOTEBOOKS.find(n => 'nb:' + n.id === current);
    if (nb) { nb.src = text; nb.updated = Date.now(); saveNotebooks(); return; }
  }
  if ((current.startsWith('ex:') || current.startsWith('co:')) && text === sourceOf(current)) return;
  // Editing an example turns it into the unsaved draft.
  store.set(LS_DRAFT, text);
  if (current !== 'draft') { current = 'draft'; store.set(LS_CURRENT, current); fillSelect(); }
}

exSel.addEventListener('change', () => {
  current = exSel.value;
  store.set(LS_CURRENT, current);
  editor.set(sourceOf(current));
  fillSelect();
  run();
});

// A notebook from outside (a shared link, a file) opens as the unsaved draft.
APP.loadSource = text => {
  current = 'draft';
  store.set(LS_CURRENT, current);
  store.set(LS_DRAFT, text);
  editor.set(text);
  fillSelect();
  run();
};
APP.notebookName = () => current.startsWith('ex:') ? EXAMPLES[+current.slice(3)].name
  : current.startsWith('co:') ? APP.COURSES[+current.slice(3)].name
  : current.startsWith('nb:') ? (NOTEBOOKS.find(n => 'nb:' + n.id === current) || {}).name || 'Notebook'
  : 'Notebook';

$('#nbSaveAs').addEventListener('click', () => {
  const form = $('#saveForm');
  form.hidden = !form.hidden;
  if (!form.hidden) {
    const base = current.startsWith('ex:') ? EXAMPLES[+current.slice(3)].name : current.startsWith('co:') ? APP.COURSES[+current.slice(3)].name : 'My notebook';
    $('#nbName').value = base;
    $('#nbName').select();
    $('#nbName').focus();
  }
});
$('#saveForm').addEventListener('submit', ev => {
  ev.preventDefault();
  const name = $('#nbName').value.trim() || 'Untitled notebook';
  const id = Date.now().toString(36);
  NOTEBOOKS.push({ id, name, src: src.value, updated: Date.now() });
  saveNotebooks();
  current = 'nb:' + id;
  store.set(LS_CURRENT, current);
  $('#saveForm').hidden = true;
  fillSelect();
});
$('#nbCancel').addEventListener('click', () => { $('#saveForm').hidden = true; });
$('#nbDelete').addEventListener('click', ev => {
  const btn = ev.currentTarget;
  if (!btn.classList.contains('confirm')) { btn.classList.add('confirm'); btn.textContent = 'Delete permanently?'; return; }
  const gone = current.slice(3);
  NOTEBOOKS = NOTEBOOKS.filter(n => n.id !== gone);
  saveNotebooks({ deleted: gone });
  current = 'draft';
  store.set(LS_DRAFT, src.value);
  store.set(LS_CURRENT, current);
  fillSelect();
});

/* ================= Welcome ================= */

const LS_WELCOMED = 'theorem-sketchpad.welcomed';
const welcome = $('#welcome');
const showWelcome = on => { welcome.hidden = !on; if (!on) store.set(LS_WELCOMED, '1'); };
if (store.get(LS_WELCOMED, '0') !== '1') showWelcome(true);
const narrow = window.matchMedia('(max-width: 900px)');
const placeWelcome = () => {
  if (narrow.matches) $('#tab-notebook').prepend(welcome);
  else $('.results-head').after(welcome);
};
placeWelcome();
narrow.addEventListener('change', placeWelcome);
APP.toResults = () => { if (narrow.matches) $('.right').scrollIntoView({ behavior: 'smooth', block: 'start' }); };
$('#welcomeClose').addEventListener('click', () => showWelcome(false));
$('#helpBtn').addEventListener('click', () => { showTab('notebook'); showWelcome(welcome.hidden); });
$('#welcomeRun').addEventListener('click', () => {
  showWelcome(false);
  if (current !== 'ex:0') { exSel.value = 'ex:0'; exSel.dispatchEvent(new Event('change')); } else run();
  APP.toResults();
});
$('#welcomeCourses').addEventListener('click', () => { showWelcome(false); exSel.focus(); try { exSel.showPicker(); } catch (e) { /* not supported: focused instead */ } });
$('#welcomeLang').addEventListener('click', () => { showWelcome(false); showTab('syntax'); });

$('#autorun').checked = store.get(LS_AUTO, '0') === '1';
$('#autorun').addEventListener('change', () => store.set(LS_AUTO, $('#autorun').checked ? '1' : '0'));
if (!MV.mathSupported()) $('#typeset').closest('label').hidden = true;
$('#typeset').checked = APP.typeset;
$('#typeset').addEventListener('change', () => { APP.setTypeset($('#typeset').checked); run(); });

/* ================= Tabs ================= */

function showTab(name) {
  document.querySelectorAll('.tab').forEach(t => {
    const on = t.dataset.tab === name;
    t.setAttribute('aria-selected', on);
    t.tabIndex = on ? 0 : -1;
  });
  document.querySelectorAll('.tabpanel').forEach(p => { p.hidden = p.id !== 'tab-' + name; });
  if (name === 'libraries') APP.libEditor.refresh();
}
APP.showTab = showTab;
document.querySelectorAll('.tab').forEach(t => t.addEventListener('click', () => showTab(t.dataset.tab)));

/* ================= Theme, resize, start ================= */

let resizeRaf = 0, lastWidth = 0;
new ResizeObserver(() => {
  const w = OUT.clientWidth;
  if (w === lastWidth) return;
  lastWidth = w;
  cancelAnimationFrame(resizeRaf);
  resizeRaf = requestAnimationFrame(renderAllFigures);
}).observe(OUT);
const rethemed = () => { resetTheme(); renderAllFigures(); };
window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', rethemed);
new MutationObserver(rethemed).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { editor.refresh(); renderAllFigures(); });
document.addEventListener('pointerdown', ev => {
  if (MV.Figure.active && !MV.Figure.active.wrap.contains(ev.target)) { MV.Figure.active.wrap.classList.remove('active'); MV.Figure.active = null; }
});

APP.rebuildRegistry();
APP.renderLibList();
APP.wireLibraries();
fillSelect();
editor.set(sourceOf(current) || EXAMPLES[0].src);
run();
})();
