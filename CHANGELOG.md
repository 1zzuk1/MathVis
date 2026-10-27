# Changelog

Versions follow [semantic versioning](https://semver.org): the desktop apps take their version
from the release tag (`v1.0.0`).

## 1.0.0

The first release.

**The language and its checks**
- A notation close to the blackboard: definitions with typed parameters, `forall` / `exists`,
  sets, sequences, points of ℝⁿ, big operators and limits; plain English through the Words panel.
- Claims proved exactly where algebra settles them (identities, sums, inequalities, derivatives
  of formulas, the steps of inductions and ε–δ proofs), otherwise tested on well-chosen samples,
  with the simplest counterexample when they fail.
- Warnings for claims of a shape sampling can't decide, and for failures that may not be real.
- `explain`, `vary`, structures defined by axioms, proof sketches, commutative diagrams.
- `concept`: one notion with several equivalent definitions, compared on examples.
- `interpret`: every way of looking at a value (a submanifold as a chart, local equations, a local
  graph and a straightening; a matrix as a map, by eigenvectors, as a quadratic form; numbers,
  functions, graphs, formulas of logic…).

**Libraries**
- Analysis: sequences, functions, integration, series, metric spaces, compactness, several
  variables, integration in ℝⁿ and vector analysis, asymptotics, Fourier series, submanifolds.
- Algebra and discrete mathematics: linear algebra, number theory, algebraic structures, groups,
  every small model, graphs, logic.
- Also: topology, geometry, curves and surfaces, dynamics, probability, numerical methods, a zoo of
  famous counterexamples.

**The app**
- Notebooks with typeset formulas, sliders, 2D and 3D figures, background threads, topic search
  for library functions, sharing as files and reports.
- Example notebooks: Analysis II, chapters 1–12.
- A desktop app for Windows, macOS and Linux, and a single-file version for any browser.
