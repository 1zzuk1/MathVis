# Theorem Sketchpad

**Write mathematics the way it looks on the blackboard, and see whether it's true.**

Theorem Sketchpad is a notebook for definitions, theorems and proofs. You write them in a notation
close to ordinary mathematics; every claim is then checked and drawn:

- **proved exactly** when algebra settles it: identities, sums, many inequalities, derivatives of
  formulas, the steps of an induction or an ε–δ proof;
- otherwise **tested on many well-chosen examples**: boundary points of sets, sequences that run
  into an edge, functions from a catalog of classic counterexamples;
- and when it is false, you get the **simplest counterexample**, drawn, with a step-by-step
  explanation of why it fails.

And one object can be seen in all its forms at once: `interpret` shows a submanifold as the image
of a chart, as the solutions of local equations, as locally a graph and as flattened by a change of
coordinates, each built from whichever description it was given by; a matrix as a linear map, by
its eigenvectors and as a quadratic form; a number as a product of primes or a continued fraction.
`concept` states a notion with all its equivalent definitions and sets them side by side on
examples, so you see that they agree, or exactly where a careless one parts from the others.

It runs entirely on your computer, offline, with nothing to install but the app itself.

```
import topology

def closed_disk := {p in R^2 | |p| <= 1}

check open(closed_disk)        # fails: every boundary point, drawn in red
check seq_closed(closed_disk)  # holds: every sampled sequence's limit stays in the disk
```

`open` and `seq_closed` aren't built in: they are book definitions in the topology library, written
in the same notation, and `explain open` reads one out in plain words and tries it on example sets.

---

## Contents

- [Starting it](#starting-it)
- [A first notebook](#a-first-notebook)
- [The example notebooks: Analysis II, chapters 1–12](#the-example-notebooks-analysis-ii-chapters-112)
- [The language in five minutes](#the-language-in-five-minutes)
- [How claims are checked](#how-claims-are-checked)
- [Working in the app](#working-in-the-app)
- [Libraries](#libraries)
- [Writing your own libraries](#writing-your-own-libraries)
- [Development](#development)
- [Limits](#limits)

---

## Starting it

**The desktop app.** Double-click the start script for your system, in this folder:

| System | File |
|---|---|
| Windows | `Start Theorem Sketchpad (Windows).bat` |
| macOS | `Start Theorem Sketchpad (macOS).command` (the first time: right-click it, then **Open**) |
| Linux | `Start Theorem Sketchpad (Linux).sh` (allow it to run as a program if asked) |

It needs [Node.js](https://nodejs.org) (the LTS version; installing it once is enough). The first
start downloads Electron, about 100 MB, into `desktop/node_modules`; after that it starts in a few
seconds and works offline. Without Node.js the script opens the app in your browser instead.

If a script won't start on macOS or Linux after the folder was zipped on Windows (the permission
to run is lost), open a terminal in this folder and run it with `bash`, as in
`bash "Start Theorem Sketchpad (macOS).command"`.

**Installers.** `Build installers (…)` builds a real installer for the system you are on, into
`desktop/release/`: a Setup `.exe` and a portable `.exe` on Windows, `.dmg` disk images on macOS,
an `.AppImage` and a `.deb` on Linux. Those can be given to people without Node.js. They aren't
signed with a paid certificate, so the system asks once: on Windows "Windows protected your PC" →
**More info → Run anyway**; on macOS "can't be verified" → **Done**, then **System Settings →
Privacy & Security → Open Anyway**.

**Without installing anything**: double-click `index.html` to use the app in your browser
(claims are then checked on the page rather than in background threads). `npm run release` also
makes a one-file version with "Open as app" launchers, `dist/Theorem-Sketchpad.zip`.

Notebooks you save stay with the app (or browser) on that computer. **Share → Download the
notebook** and **Open a notebook file** move them between computers; **Share → Download a report**
saves the results as one HTML page anyone can read.

## A first notebook

Open the app, write a few lines on the left, and press **Run** (or **Ctrl+Enter**):

```
# Every statement is one line (indent to continue it).
check forall x, y in R: (x + y)^2 = x^2 + 2*x*y + y^2     # proved by algebra
check forall x in [0, 1]: x^2 <= x                          # proved exactly (an inequality)
check forall x in R: x^2 >= x                               # fails: simplest counterexample x = 1/2

def f(x) := x * sin(1/x)
plot f(x) for x in [-0.5, 0.5]

import functions
check continuous_at(x => if x = 0 then 0 else x*sin(1/x), 0)   # holds, decided from the formula
explain uniformly_continuous_on                                 # the definition, read and tried out
```

Each result appears on the right as a card: the claim typeset as mathematics, a verdict (**Proved**,
**Holds on all samples**, **Fails**), a picture, and buttons for more. Click any counterexample,
table cell or gallery tile to see **why**: the claim evaluated step by step.

Not sure of the notation? Press **Words…** and type the statement in English ("for every real
number x, x squared is at least 0"); the panel shows the notation it means.

## The example notebooks: Analysis II, chapters 1–12

The **Notebook** menu has a complete Analysis II course, chapter by chapter. Each notebook follows
the chapter's definitions and theorems (the numbers in the comments, such as `(7.13)`, are theirs),
formalised as close to the book as the notation allows, with pictures you can drag:

| Notebook | What you see |
|---|---|
| **1–3 The Riemann integral** | Step functions and their integral; upper and lower integrals closing in; Riemann sums; the mean value theorem; the fundamental theorem (F's slope is f); substitution, integration by parts, the trapezoidal rule; improper integrals as limits; the integral test |
| **4 Sequences of functions** | Pointwise vs uniform convergence; the M-test; uniform limits of differentiable functions that aren't; power series converging inside their radius and flying apart outside; a series with radius 0 |
| **5 ℝⁿ, norms, open and closed sets** | Metrics and norms by their axioms; Young, Hölder and Minkowski (and Minkowski failing for p < 1); comparing p-norms; open sets, boundary points, closed sets |
| **6 Limits and continuity** | Convergence in a metric; ε-balls of three norms around a limit; completeness; continuity along every path (x²y/(x⁴ + y²) agrees on every line and still isn't continuous); operator norms |
| **7 Compactness** | Open covers with and without finite subcovers; Heine–Borel; a convergent subsequence found by halving (Bolzano–Weierstrass); maxima attained or only approached; the δ of Heine–Cantor from a finite subcover; all norms are equivalent |
| **8 Derivatives in ℝⁿ** | The total derivative as a linear approximation; partial and directional derivatives, proved exactly; the gradient as steepest ascent; gradient descent with a step-size slider; the chain rule; Schwarz's theorem |
| **9–10 Taylor, extrema, fixed points** | Taylor polynomials with their error; definite matrices (eigenvalues, Sylvester's minors and xᵀAx compared); critical points classified by the Hessian; Banach's fixed point theorem with its error bound |
| **11 Integrals in ℝⁿ** | Step functions under and over a surface; Fubini slice by slice (and an example where the two orders disagree); integrals between graphs; differentiating under the integral; polar coordinates |
| **12 Vector analysis** | Charts, tangent and normal spaces; the four descriptions of a submanifold (chart, local equations, local graph, straightening) side by side; the implicit and inverse function theorems; Lagrange multipliers; lengths and areas from the Gramian; line integrals and the work along a curve; Green, Stokes and Gauss checked numerically |

Edit anything and run again: the notebook becomes your own unsaved copy (**Save as…** keeps it).

## The language in five minutes

A notebook is a list of statements. The full reference is [LANGUAGE.md](LANGUAGE.md); the app's
**Language** tab has a summary.

| Statement | Meaning |
|---|---|
| `def f(x) := x^2 + 1` | A definition: a function, a set (`def D := {p in R^2 \| \|p\| < 1}`) or a value. Parameters may be typed: `def f(x: R^2)`. A comment line right above it is its documentation. |
| `let a = 3` | A value, computed once. |
| `check claim` | Check a claim. `theorem`, `lemma`, `conjecture` and `claim` work the same, and with a name (`theorem t: …`) the claim can be used again. |
| `explain name` | Show a definition, lemma or function: its formula, a reading in plain words, what it uses, and a gallery of examples marked by whether they satisfy it. |
| `plot f(x) for x in [a, b]` | Curves, surfaces (`for x in …, y in …`), parametric curves and surfaces in 2D and 3D. |
| `show view(…)` | A picture from a library, usually with sliders (`show epsdelta(f, a, ε)`, `show cover(S, U)`). |
| `import topology` | Load a library (several: `import topology, metric`). |
| `proof:` | A proof sketch under a theorem; each step (`let`, `assume`, `choose`, `have`, `so`, `case`, `induction`) is checked in its context. |
| `structure Group(G, op, e) where …` | A structure defined by axioms; its examples are checked against each one. |
| `concept prime(n: Z) where …` | One notion with several equivalent definitions (`two_divisors: …`, `wilson: …`), one per line; each is also a definition (`prime_wilson`), and the card compares them on the examples. |
| `interpret value` | Every way of looking at a value (`interpret zero_set((x, y) => x^2 + y^2 - 1)`, `interpret [[2, 1], [1, 2]]`), or every form of a concept at given arguments (`interpret coprime(12, 35)`). |

Inside claims: `forall x in S: P`, `exists x in S: P`, `and`, `or`, `not`, `->`, `<->`, chained
comparisons (`0 < x <= 1`), `∈`, `⊆`, `sum k in 1..n: …`, `lim n -> inf: …`, `sup`, `inf`, `|x|`,
points `(1, 2)`, sets `{x in R | x^2 < 2}`, functions `x => x^2`, `(x, y) => x*y`. Unicode and ASCII
are interchangeable: `∀` or `forall`, `ℝ` or `R`, `≤` or `<=`, `↦` or `=>`.

Spaces a variable can range over: `R`, `Z`, `N`, intervals `[a, b]` and `(a, b]`, ranges `1..n`,
products `R^2` and `[0, 1]^3`, sets in set-builder notation, balls, `Seq(X)` (sequences in X) and
the libraries' catalogs of examples (`Functions(R)`, `Subsets(R^2)`, `Matrices(2)`, `AllGroups(8)`…).

## How claims are checked

1. **Sampling, chosen to find trouble.** Variables are sampled where counterexamples live: interval
   ends and points creeping towards open ends, the integers and 0, the boundary of a set (found by
   bisection, so `|p| <= 1` and `|p| < 1` really differ), sequences that run into each boundary
   point, and catalogs of famous functions, sets, groups and matrices.
2. **Exact proofs where possible.** Equations are simplified as fractions of polynomials with
   rational coefficients (with closed forms of sums and exact derivatives of formulas);
   inequalities go through exact methods (case splits for |…|, min and max; linear arithmetic,
   Sturm sequences, quadratic forms, Handelman products). A claim over finitely many cases is
   checked case by case. Such results say **Proved**, and name the method.
3. **Counterexamples, simplified.** A failing claim is re-checked at simpler inputs (integers,
   halves, thirds, earlier catalog objects) and the simplest failure is shown. With no failure, a
   targeted search pushes towards one.
4. **Honesty about the hard cases.** Some claims have a shape sampling answers wrongly ("a maximum
   is attained", pairs of points closer than δ, a bound over an unbounded set); they get a warning
   instead of a plain "holds". A failure that may only be the limit of a finite check (a sequence
   converging like 1/log n, a δ smaller than floating point can hold) is flagged too.
5. **Exact answers from formulas.** Limits, series, continuity and differentiability of functions
   written as formulas are decided by asymptotic expansion, not sampling.

**Is every condition needed?** on a claim drops or weakens each hypothesis in turn and checks the
variations: the ones that fail show why the condition is there.

## Working in the app

- **Autocomplete** suggests keywords, your definitions and every library name with its
  documentation (**Ctrl+Space**, then **Tab** or **Enter**). It also finds names by topic: typing
  `derivative` offers `grad`, `jacobian` and `partial`; typing `?fixed point` searches only by
  topic. Accepting a name from a library that isn't imported adds the import.
- **Words…** turns English sentences into notation, and marks a sentence it only partly
  understood instead of guessing.
- **Pictures** zoom (scroll or pinch) and pan (drag); double-click resets. 3D pictures turn when
  dragged. Sliders above a picture redraw it live.
- **Results** fold (▾), and the counts above them (**hold**, **fail**, **error**) step through the
  results of that kind. **Typeset** switches formulas between mathematics and plain text.
- **Libraries tab**: every library with its definitions, lemmas and views, searchable; **Explain**
  and **Check** preview them without touching your notebook. **New…** writes a library of your own.
- **Background threads**: claims are checked side by side on the spare cores of your computer, so
  the page stays responsive; **Stop** interrupts a long run.
- **Share**: download the notebook, open a notebook file, or download a report of the results.

## Libraries

`core`, `catalog` and `geometry` are always loaded; `import` the others.

| Library | Contents |
|---|---|
| `core` | Elementary functions, ℝ, ℤ, ℕ, ℝⁿ, intervals, balls, `Seq(X)`, limits, set algebra; views `region`, `heatmap`, `field` |
| `catalog` | `Subsets(R)`, `Subsets(R^2)`, `Functions(R)`, `Sequences(R)`: named examples to quantify over and explain with |
| `geometry` | Shapes as sets (`Disk`, `Rect`, `Triangle`, `Polygon`, `Annulus`, …), `area`, `centroid`, `convex_set` |
| `topology` | `open`, `closed`, `seq_closed`, interior, boundary and limit points, `bounded`; finite topological spaces |
| `sequences` | `converges_to`, `cauchy`, `bounded_seq`, monotonicity |
| `functions` | Continuity, uniform continuity, differentiability, monotonicity, convexity, Lipschitz |
| `analysis` | Derivatives, integrals, limits, sums, Taylor polynomials; views `epsdelta`, `riemann`, `taylor`, `tangent`, `funcseq` |
| `integration` | Step functions, Darboux and Riemann sums, the trapezoidal rule, improper integrals, the Dirichlet and Thomae functions; views `darboux`, `antiderivative`, `improper` |
| `series` | Series and their tests; sequences of functions, pointwise and uniform convergence; power series and their radius; views `partial_sums`, `uniform`, `power_series` |
| `metric` | Metrics and norms, p-norms, completeness, Hölder and Minkowski, contractions and Banach's fixed point theorem; views `unitballs`, `norm_convergence`, `equivalent_norms`, `banach` |
| `compactness` | Covers and finite subcovers, Heine–Borel, attained extremes, uniform continuity on sets; views `cover`, `bolzano`, `extremes`, `uniform_delta` |
| `multivar` | Partial, directional and total derivatives (exact for formulas), gradients, Jacobians, Hessians, Taylor polynomials, critical points and the Hessian test; views `gradient`, `linearize`, `approach`, `descent`, `extrema`, `taylor_surface`, `level_surface` |
| `multint` | Integration in ℝⁿ (cuboids, step functions, Fubini, the transformation formula) and vector analysis (charts, the Gramian, surface, line and flux integrals, div, curl); views `step_integral`, `fubini`, `change_of_variables`, `chart`, `work`, `green` |
| `linalg` | Matrices with exact row reduction, rank, kernels and images as sets, eigenvalues, definiteness, operator norms; views `rref_steps`, `transform`, `eigen`, `subspace`, `operator_norm` |
| `asymptotics` | Exact limits, series tests and local behaviour of formulas; thresholds of parameter families |
| `algebra`, `groups`, `models` | Algebraic structures by their axioms; subgroups, cosets, quotients, homomorphisms; every small group, topology, order and relation, for smallest counterexamples |
| `topspaces`, `zoo` | Infinite topological spaces by their properties; famous counterexamples (Weierstrass, Cantor, Thomae…) with exact facts |
| `dynamics`, `curves`, `probability` | Differential equations and maps; curvature of curves and surfaces; distributions, exact chances, the limit theorems |
| `manifolds` | Submanifolds given by equations, a chart or a graph, with every other local description computed (implicit and inverse function theorems); tangent and normal spaces; Lagrange multipliers; views `manifold`, `lagrange`, `implicit_function`, `inverse_function` |
| `graphs` | Finite graphs, every graph on up to 4 vertices for exhaustive checks, colourings, Euler circuits, adjacency and Laplacian spectra; trees, bipartite, connected and Eulerian graphs each defined several ways; views `coloring`, `bfs_layers`, `euler` |
| `logic` | Truth tables, tautologies, equivalence and entailment over every row, normal forms, power sets; implication, equivalence and inclusion said several ways; view `venn` |
| `fourier` | Fourier coefficients and partial sums on [−π, π], Bessel and Parseval, the Gibbs overshoot; even and odd functions by values and by coefficients; views `fourier_series`, `parseval` |
| `numerics` | Newton, bisection and secant iterations, interpolation at equispaced and Chebyshev nodes, Runge's phenomenon; views `newton`, `bisection`, `interpolation` |
| `complex`, `numtheory`, `means` | Complex numbers and domain coloring; number theory, primes and coprime pairs said several ways; classical means |

Each library's full list of names, with documentation, is in the app's **Libraries** tab.

## Writing your own libraries

**Notation libraries** are definitions and lemmas in the notebook language. A comment directly
above a definition is its documentation; a comment line `# examples: …` says what `explain`
should try it on.

```
library convexity
# Shape conditions on real functions.

# f is convex on [a, b].
# examples: f in Functions(R), a in {-1}, b in {1}
def convex(f: Fun, a: R, b: R) := forall x, y in [a, b], t in [0, 1]:
  f(t*x + (1 - t)*y) <= t*f(x) + (1 - t)*f(y)

# The sum of two convex functions is convex.
lemma convex_sum: forall f, g in Functions(R): convex(f, -1, 1) and convex(g, -1, 1) -> convex(x => f(x) + g(x), -1, 1)
```

Add one in the app (**Libraries → New…**, or **Load from file**), or as a file in `libs/`
(wrapped as ``MathVizNotation(`library convexity …`);``, see `libs/topology.js`) listed in
`index.html`.

**JavaScript libraries** add what the notation can't: new kinds of values, spaces, and views
with sliders. They call `MathViz.define({ name, functions, spaces, views, notation, … })`; see
`libs/metric.js` or `libs/compactness.js` for complete examples. The main pieces:

| Field of `MathViz.define` | Meaning |
|---|---|
| `name`, `description` | What `import` uses, and one sentence for the Libraries tab |
| `requires` | Libraries to import first, such as `['linalg']` |
| `functions`, `constants` | Functions (or `{ doc, fn }`) and values available by name |
| `spaces` | Spaces to quantify over; `MathViz.space({ label, window, contains })` is enough for a region of ℝⁿ |
| `types` | New kinds of values with their operators (`+`, `*`, `abs`, `=`, `format`, …) |
| `views` | `{ doc, render(ctx, ...args) }`, used as `show name(args)`; `ctx.figure()`, `ctx.figure3d()`, `ctx.param()` (a slider), `ctx.note()`, `ctx.table()` |
| `notation` | Definitions, concepts and lemmas in notebook notation, run after the exports; a concept with an `# examples:` line adds a lemma that its forms agree |

`MathViz.represent({ name, label, doc, test(v), render(ctx, v) })` adds a way of looking at values to
`interpret`: every representation whose `test` accepts the value is drawn in its own section, with
sliders shared between them. `ctx.row()` puts figures side by side.

A function that estimates rather than computes calls `MathViz.markInexact()`, so results using it
are never labelled proved.

## Development

Everything is plain JavaScript in the browser, with no build step needed to run it.

```bash
npm run serve        # serves the folder at http://localhost:5178 (background threads need a server)
npm test             # the test suite, about two minutes
npm run build        # dist/theorem-sketchpad.html: the whole app in one file
npm run release      # also dist/Theorem-Sketchpad.zip, with the "Open as app" launchers
```

Opening `index.html` directly works too (claims are then checked on the page instead of in
background threads).

**Tests.** `npm test` runs every example notebook and the test notebooks in `tests/notebooks.js`
(which exercise every library), the expectation files in `tests/cases` (a comment like
`#! fails simplest √2/2` above a statement says what it must give), every library lemma and
conjecture with the usual and the wild examples, the topic search, the warnings, and the
typesetting of every formula. With `npm run serve` running,
http://localhost:5178/tests/views.html draws every view and checks that each library view is
shown somewhere.

**The desktop app** is in `desktop/`: Electron loads the single-file build in its own window,
and electron-builder packs the installers. In `desktop/`: `npm install` once, then `npm start`
(opens the app), `npm run smoke` (starts it hidden, runs the first example, reports) and
`npm run dist` (installers for the system you are on, in `desktop/release/`).

| Path | What it is |
|---|---|
| `index.html`, `style.css` | The page |
| `src/` | The engine: parser (`syntax.js`), spaces and sampling (`spaces.js`), evaluation and claim analysis (`runtime.js`), exact algebra (`symbolic.js`), exact inequalities (`inequal.js`), asymptotics (`asym.js`), exact reals (`exact.js`), proofs, diagrams, interval arithmetic, variations, plain English (`words.js`), topic search (`topics.js`), warnings (`cautions.js`), figures and MathML |
| `libs/` | The libraries |
| `app/` | The interface: editor, result cards, pictures of claims, proofs, the Libraries tab, sharing, background threads, the Words panel, the example notebooks (`main.js`) and courses (`courses.js`) |
| `tests/` | `run.js` (the suite), `harness.js` (the engine in Node), `cases/`, `notebooks.js`, `views.html`, `words.txt` |
| `desktop/` | The Electron app and its installer settings |
| `Start …`, `Build installers …` | Set up and start the desktop app from the source, or build its installers |
| `CHANGELOG.md` | What changed in each version |
| `launch/` | "Open as app" launchers for the light version |
| `build.js`, `serve.js` | The single-file build and a small local server |
| `LANGUAGE.md` | The language reference |

## Limits

- **Sampling is evidence, not proof.** Only results labelled **Proved** are certain. Samples are
  chosen to find counterexamples, but a claim that fails only on unusual inputs can pass; the
  warnings cover the shapes known to fool sampling, not every way.
- **Finite checks of infinite statements.** Definitions with "for every ε > 0" over infinite
  ranges are checked on finite versions; very slow phenomena (Σ 1/n^1.01) are out of reach of any
  finite check, though the example catalogs know the true answers for theirs.
- **Numbers are floating point**, with comparisons tolerant to 10⁻⁹ (exact rationals and simple
  irrationals where rationality matters). Structure finer than that can't be seen.
- **Estimates are marked**: integrals over sets, improper integrals that converge very slowly,
  critical points and Lipschitz constants are numerical, and say so.
- **Proof sketches** check each step numerically or exactly; they find wrong steps, they don't
  certify a whole argument the way a proof assistant does.
- Sets of zero area (a circle `|p| = 1`) can't be sampled at random; describe them by a
  parametrization instead.
