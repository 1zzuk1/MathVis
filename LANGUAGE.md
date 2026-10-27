# The Theorem Sketchpad language

A notebook is a sequence of statements. Definitions build an environment; claims are checked by
sampling their variables and drawn. This document is the reference for the notation and for what
each construct means when it is evaluated.

## 1. Lexical structure

- **Statements** end at the end of a line. A line continues the previous statement when it is
  indented, when brackets are still open, or when the previous line ends in an operator,
  `:`, `:=`, `,`, `->`, `and`, `or` or `where`.
- **Comments** start with `#` (at the start of a line, or after a space) and run to the end of
  the line. Comment lines directly above a `def` or `let` are its documentation.
- **Names** are letters (any alphabet, so `ε`, `δ`, `π` work), digits, `_` and `'`, not starting
  with a digit: `x`, `x1`, `f'`, `open_disk`.
- **Numbers**: `3`, `0.25`, `1e-9`. A number directly followed by a name or `(` multiplies:
  `2x`, `2 pi`, `3(x + 1)`.
- **Unicode and ASCII are interchangeable**:

| Unicode | ASCII | | Unicode | ASCII |
|---|---|---|---|---|
| `∀` `∃` | `forall` `exists` | | `ℝ` `ℤ` `ℕ` | `R` `Z` `N` |
| `∈` `∉` | `in` `notin` | | `²` `³` `ⁿ` | `^2` `^3` `^n` |
| `∧` `∨` `¬` | `and` `or` `not` | | `⊆` | `subset` |
| `⇒` `→` `⇔` | `->` `<->` (`implies`, `iff`) | | `∪` `∩` `∖` | `union` `inter` `\` |
| `≤` `≥` `≠` `≈` | `<=` `>=` `!=` `~=` | | `∑` `∏` | `sum` `prod` |
| `·` `×` `−` | `*` `*` `-` | | `↦` | `=>` |
| `∞` | `inf` | | `‖x‖` | `\|x\|` |

Reserved words: `forall exists in notin and or not if then else mod let def theorem lemma claim
conjecture check plot show explain vary for import library true false where structure extends as
concept interpret`.
Inside a proof, a step starts with `let`, `assume`, `choose`, `have` or `so` (also `take`, `fix`,
`suppose`, `pick`, `set`, `claim`, `note`, `hence`, `thus`, `therefore`, `show`, `conclude`). `∅` is `{}`. The words `sum prod sup inf max
min lim subset union inter` are special only where they introduce their construct; elsewhere they
are ordinary names (so `max(a, b)` is a function call and `inf` is ∞).

## 2. Grammar

```ebnf
statement  = "import" name { "," name } | "import" name "as" name
           | "library" name
           | "let" name ("=" | ":=") expr
           | "def" name [ "(" param { "," param } ")" ] (":=" | "=") expr
           | ("theorem" | "lemma" | "claim" | "conjecture" | "check") [ name ":" ] expr
           | "plot" expr { "," expr } "for" binders
           | "show" name "(" [ expr { "," expr } ] ")"
           | "explain" name [ "for" binders ]
           | "vary" name
           | "structure" name "(" field { "," field } ")" [ "extends" name ]
               [ "where" axiom { axiom } ]
           | "concept" name [ "(" param { "," param } ")" ] "where" form form { form }
           | "interpret" expr
           | "proof" [ "of" name ] ":" step { step }    (* steps on indented lines *)
           | "diagram" [ name ] ":" dline { dline }     (* on indented lines *)
           | expr ;
dline      = name ":" add "->" add                  (* an arrow; also → *)
           | path "=" path                          (* g ∘ f = h: apply f first; also "g o f" *)
           | "exact" "at" add
           | "commutes" ;
path       = name { ("∘" | "o") name } ;
field      = name [ ":" space ] ;
axiom      = name ":" expr ;
form       = name ":" expr ;                         (* at least two, usually one per line *)
step       = "let" name { "," name } [ "in" space | cmpop add ]
           | "assume" expr
           | "choose" name ( "=" expr | "in" space ("such that" | "with" | ":") expr )
           | ("have" | "so") expr [ "by" text ]       (* text starting with a lemma's name cites it *)
           | "case" expr ":" block { "case" expr ":" block } [ "otherwise" ":" block ]
           | "induction" [ "on" ] name [ "base" ":" block ] [ "step" ":" block ]
           | "contradiction" ;                         (* also "by contradiction", "suppose not" *)
block      = step { step } ;                           (* on lines indented below the header *)
param      = name [ ":" space ] ;

expr       = iff [ "where" name "=" iff { "," name "=" iff } ] ;
iff        = imp { "<->" imp } ;
imp        = or [ "->" imp ] ;                      (* right associative *)
or         = and { "or" and } ;
and        = not { "and" not } ;
not        = "not" not | rel ;
rel        = add [ ".." add ]
             ( { cmpop add }                         (* chains: 0 < x <= 1 *)
             | ("in" | "notin") space
             | "subset" add ) ;
add        = mul { ("+" | "-" | "\" | "union") mul } ;
mul        = unary { ("*" | "/" | "mod" | "inter") unary } ;
unary      = "-" unary | "√" unary | quantifier | pow ;
pow        = postfix [ "^" unary ] ;                (* right associative, binds tighter than unary minus *)
postfix    = primary { "(" args ")" | "[" args "]" | "!" | "." name } ;   (* record fields, library members *)
primary    = number | name | "true" | "false"
           | "(" expr { "," expr } ")"               (* grouping or a point (x, y) *)
           | "[" expr { "," expr } "]"               (* a list *)
           | "[" expr "," expr ")" | "(" expr "," expr "]"   (* half-open intervals *)
           | "|" add "|"
           | "{" binders "|" expr "}"                (* set builder *)
           | "{" expr { "," expr } "}"               (* finite set *)
           | "{" name "=" expr { "," name "=" expr } "}"   (* record *)
           | "if" expr "then" expr "else" expr
           | name "=>" expr | "(" name { "," name } ")" "=>" expr
           | bigop binders ":" add
           | "lim" name "->" add ":" add ;
quantifier = ("forall" | "exists") binders ":" expr ;
bigop      = "sum" | "prod" | "sup" | "inf" | "max" | "min" ;
binders    = binder { "," binder } ;
binder     = target { "," target } ( "in" space | (">" | ">=" | "<" | "<=") add ) ;
target     = name | "(" name { "," name } ")" ;     (* (x, y) splits a point *)
space      = "[" expr "," expr ("]" | ")") { ("^" | "*") unary }
           | "(" expr "," expr ("]" | ")") { ("^" | "*") unary }
           | add [ ".." add ] ;
```

Quantifier bodies extend as far to the right as possible: `forall x in S: P and Q` quantifies
both `P` and `Q`. The bodies of `sum`, `sup`, `lim` and the other big operators are additive
expressions, so `sum k in 1..n: k^2 = n^3/3` compares the sum with `n^3/3`.

## 3. Values

| Kind | Examples | Notes |
|---|---|---|
| Number | `3`, `pi`, `1e-9` | IEEE doubles |
| Boolean | `true`, `x < 1` | Logical operators require booleans |
| Point | `(1, 2)`, `[1, 2, 3]` | Add and subtract coordinatewise, scale by numbers; `\|p\|` is the length; `p[1]` is the first coordinate |
| Function | `x => x^2`, `def f(x) := …` | Arithmetic on functions is pointwise: `f + g`, `2f` |
| Sequence | `n => 1/n`, sampled from `Seq(X)` | A function on 1, 2, 3, … Sequences from `Seq(X)` know their limit |
| Space | `R^2`, `[0, 1)`, `{p in R^2 \| \|p\| < 1}` | Anything a variable can range over (section 4) |
| Exact real | `1/3`, `sqrt(1/2)` = `√2/2`, π/4 | Knows whether it is rational (below) |
| Record | `{G = Zmod(5), op = add_mod(5), e = 0}`, `Group(Zmod(6), add_mod(6), 0)` | Named fields, read with `r.G`; equal when every field is |
| Matrix | `[[1, 2], [3, 4]]` (with `linalg`) | Products, powers, `det`, `inv`; printed with exact fractions |
| Library values | `i` (complex), subspaces | Library types define their own operators |

Numbers print as short decimals when they are (`0.25`), as fractions when they are simple ones
with denominators up to 100 (`5/12`), and rounded otherwise. Finite sets compare as sets
(`{1, 2} = {2, 1}`), combine exactly (`{1, 2} ∪ {2, 3}`), and `|S|` is the number of elements.

`=` on points, lists and library values compares them elementwise, within the tolerance below.

### Tolerance

Comparisons treat numbers within `10⁻⁹` of each other (relative, with an absolute floor of
`10⁻¹²` near zero) as equal. So `<=` includes numbers just over its bound, and `<` excludes
numbers just under it. `~=` uses `10⁻⁶`. This is what makes `|p| <= 1` contain the points that
numerically sit on the unit circle while `|p| < 1` excludes them, which is the difference between
a closed and an open disk. On points and matrices `~=` compares coordinate by coordinate. `sqrt` of a
number within 10⁻¹² below 0 is 0, so `√(x + h)` is defined wherever `x + h ∈ [0, 1]` holds up to
that tolerance.

## 4. Spaces

A space supports membership (`x in S`) and sampling (so it can be quantified over).

| Space | Meaning | Sampled as |
|---|---|---|
| `R`, `Z`, `N` | ℝ, ℤ, ℕ = {0, 1, 2, …}; membership is unbounded | [−10, 10], −50..50, 0..100 |
| `R[a, b]`, `Z[a, b]`, `N[a, b]` | Bounded versions | — |
| `[a, b]`, `(a, b]`, `[a, b)`, `(a, b)` | Intervals (in binder position; elsewhere `(a, b)` is a point, so write `Ioo(a, b)`) | Even grid, plus points creeping toward open ends |
| `Icc Ico Ioc Ioo (a, b)` | Intervals as values | — |
| `a..b` | Whole numbers from a to b | All of them when few; else the start in detail, then wider spacing |
| `A^n`, `A * B` | Products; elements are points | Grids or random points |
| `{x in A \| P}`, `{(x, y) in A \| P}`, `{x in A, y in B \| P}` | Sets | Inside, near the boundary, and on it (below) |
| `A ∪ B`, `A ∩ B`, `A \ B`, `complement(A)` | Set algebra; complements are taken in the surrounding space (ℝ, ℝⁿ, …) | As sets |
| `Ball(c, r)`, `ClosedBall(c, r)` | Balls in ℝ or ℝⁿ | Center, points just inside the sphere in the axis directions, random points |
| `Seq(X)` | Sequences in X; `Seq(Seq(R))` is sequences of sequences | A curated family (below) |
| `{1, 2, 3}`, lists | Finite sets | All elements |
| `Set`, `Fun` | Any space, any function (for typed parameters) | — |

### How sets are sampled

Sets are explored once, when they are first sampled:

1. Random points of the surrounding window are classified as inside or outside; the window is
   refined around whichever kind is rarer, so small sets and small holes are found.
2. From inside points, rays in the axis directions and in random directions are followed until
   they leave the set, and the crossing is located by bisection with **exact** comparisons.
3. Each crossing is then tested with the usual **tolerant** comparisons. It counts as a boundary
   point *in* the set (closed side) or *not in* it (open side).
4. Inside points at distances 10⁻², 10⁻³ and 10⁻⁴ (relative to the set's size) from each
   boundary point are added.

A sample of a set mixes interior points, near-boundary points, and boundary points that belong to
the set. Sets of zero area (a circle `|p| = 1`) and sets too small to hit at random can't be
sampled this way.

### How `Seq(X)` is sampled

`Seq(X)` offers, interleaved: sequences that run into each boundary point of X at rates 1/n,
1/n², 2⁻ⁿ and 1/√n (including boundary points not in X); sequences converging to interior points,
some alternating; constants; and divergent ones (alternating between two points, jumping between
several, and for numbers `c + sin(n)` and `c + n`). Only sequences whose terms (n = 1…40, 100,
1000, 10000) lie in X are kept. Each carries its formula as a label and its limit, so `lim(s)` and
`convergent(s)` are exact for them; arithmetic on sequences keeps limits when both are known.

## 5. Evaluation

### Definitions

- `let x = e` evaluates `e` once. `def f := e` (no parameters) does the same; a set defined this
  way takes the name as its label.
- `def f(x, y) := e` defines a function. Bodies are checked when the definition is made: every
  name must be a parameter, a bound variable, something already defined, or something defined
  **later** in the notebook (so definitions may refer to each other and to themselves).
- `def f(x: R^2, s: Seq(R))` checks each argument's membership on every call.
- Calls whose arguments are all numbers are remembered, which makes recursive sequences cheap.
- `e where a = …, b = …` evaluates the bindings in order, each seeing the previous ones.
- Calls are remembered (the language has no side effects): a definition applied to the same
  numbers, points, or objects (the same set, the same function) is evaluated once.
- Comment lines directly above a definition are its documentation. A comment line
  `# examples: x in S, f in Functions(R)` gives the examples `explain` tries it on.
- A named claim (`theorem name: …`) becomes a value: a later `check name` checks it again and
  `explain name` shows it.

### Quantifiers

`forall x in S: P` and `exists x in S: P` are evaluated by sampling `S`. The number of samples
per variable depends on nesting depth, counted while evaluating (so a quantifier inside a
definition gets fewer samples when that definition is used inside another quantifier): 200, 64,
40, then 20. Two variables bound together share the count √2 ways; three or more get about
(count)² combinations in total. Real intervals always include 0 and the integers inside them (when
there are at most six), where textbook examples put their jumps. `exists` over an interval also tries values down to 10⁻⁸ of its width near open ends,
so `exists δ in (0, 1]` finds small δ. When no sample works, `exists y` over a real range tries
the simple values 0, ±1/2, ±1, ±2, ±3, then solves each equation `lhs = rhs` in its body that
involves y: bisection between sign changes of lhs − rhs on a grid of the range, and a search at
each place where |lhs − rhs| is smallest (for double roots like y² = 0). So
`forall x in [0, 1]: exists y in R: y^3 = x` holds. Claims that depend on whether numbers are
rational skip the solving, since a root found this way is a float. `forall` stops at the first
counterexample, `exists` at the first witness. Variable ranges may use earlier variables: `forall x in [a - δ, a + δ]`.

`A ⊆ B` is `forall x in A: x in B`, sampled the same way.

### Big operators and limits

- `sum` and `prod` need finite ranges (at most a million elements) and are exact.
- `max` and `min` are exact over finite ranges; `sup` and `inf` over infinite ones are taken over
  samples (including boundary points).
- `lim n -> inf: e` is the limit of a sequence. If `e` is `s(n)` for a sequence `s` that knows its
  limit, that limit is used; otherwise terms near n = 10³…10⁶ (with mixed parity, plus
  consecutive terms) are compared, with one Richardson step for 1/n convergence. A divergent
  sequence gives `undefined`.
- `lim x -> a: e` compares values at `a ± 10⁻⁴…10⁻⁷`.

## 6. Claims

`theorem`, `lemma`, `claim`, `conjecture` and `check` are interchangeable; the word is a label.
A claim is analysed in these steps:

1. **Unfolding.** If the claim is a call to a `def`, its arguments are evaluated and its body is
   used instead, repeatedly. After that, a definition called in the conclusion is inlined by
   substitution (with bound variables renamed when they would clash).
2. **Peeling.** Leading `forall`s become the claim's variables. `P -> forall y: Q` becomes
   `forall y: P -> Q` when `y` is not used in `P`.
3. **Classifying the body.** `P -> Q` marks samples where `P` is false as vacuous. A two-sided
   comparison records both sides; an `exists` becomes a witness search (largest real witness or
   smallest whole-number witness); anything else is true/false.
4. **Sampling.** Each claim draws its samples (and every sample its own random numbers) from a seed
   made from the claim's text and options, so a claim gives the same result wherever and in
   whatever order it is checked. One number: 400 samples (120 if the body has nested
   quantifiers). Two numbers or a
   point of a box: a grid of up to 6400. A point of a set: about 900 (300). A sequence: the
   `Seq` family. Three or more numbers: every case if there are at most 4000, otherwise 2500
   random samples (400).
5. **Drawing.** See the table in the Language tab of the app.

A result is reported as holding on all samples, failing on some (with counterexamples, worst
first when there is a margin), or never tested when every sample is vacuous. Results are evidence
from sampling, not proofs, except in three cases: every case of a finite range was checked
exactly, interval arithmetic covered an inequality (the proof map), or exact algebra settled an
equation.

### Exact algebra

An equation `L = R` (or a chain `A = B = C`) whose samples all hold is also simplified exactly:
both sides become fractions of polynomials with rational coefficients in the claim's variables.
Anything else becomes an opaque symbol keyed by its simplified arguments, so `sin(x + y)` and
`sin(y + x)` agree. The simplifier knows:

- your definitions, expanded with their arguments, and functions made by an expression that doesn't
  involve the claim's variables, such as `partial(f, 1)` (multivar), whose result is the exact
  derivative of f's formula: `partial(partial(g, 1), 2)(x, y) = partial(partial(g, 2), 1)(x, y)` is proved;
- `a^(e + c) = a^e · a^c` for whole numbers c, so `2^(n + 2) = 4·2^n`;
- `sin(x)² + cos(x)² = 1`;
- sums `sum k in lo..hi: p(k)` of polynomials in k, in closed form (Faulhaber's formulas), and
  other sums with the last terms split off, `Σ_{lo}^{n+1} = Σ_{lo}^{n} + (term at n + 1)`.

If both sides agree the claim is **proved by algebra**, provided it holds for every value: each
denominator can't vanish (1 + x², n + 1 for n in ℕ, k(k + 1) for k ≥ 1 are accepted; x is not), and
each sum's range is never shorter than empty (for `1..n`, n ∈ ℕ or n in a range starting at 0 or
more). Otherwise the card says which condition is missing and the samples decide.

### Exact inequalities

An inequality (`<`, `<=`, `>`, `>=`, also chains and several joined by `and`) whose samples
hold is also tried exactly, for every value the variables' ranges and the claim's hypothesis
allow:

- `|a|`, `min(a, b)` and `max(a, b)` are split into cases (`|a| = a` where `a ≥ 0`, `−a` where
  `a ≤ 0`, and so on). Before that, products of absolute values merge (`|x − 1|·|x + 1| = |x² − 1|`)
  and even powers lose their bars, so identities like `|xy| = |x||y|` are exact too.
- The ranges (`x in [0, 1]`, `n in N`, `ε > 0`) and hypotheses become polynomial constraints.
  `sin` and `cos` lie in [−1, 1], `exp` and `2^n` are positive, `sqrt(u)` is ≥ 0 with square u.
- In each case the difference of the two sides is shown ≥ 0 (or > 0) by the first method that
  applies: the signs of its terms; linear arithmetic (Fourier–Motzkin elimination, complete for
  linear claims); exact root counting in one variable (Sturm sequences, complete for one
  variable); a positive semidefinite quadratic form (complete for degree 2 without constraints);
  products of the linear constraints (Handelman's theorem, solved as a linear program with exact
  rational simplex); squaring away one square root. Substitutions bring more claims to these:
  `y = x + h` with `h ≥ 0` from a hypothesis `x ≤ y`, factoring out a variable ≥ 0, `x² = u`
  when x appears only to even powers.
- Denominators must be provably nonzero (`1 + t²` is, `x` is not).

Every method is exact rational arithmetic, so **proved** means proved; the card names the method.
If no method applies, the samples decide. A sample that fails only by a floating-point tie (both
sides equal after rounding) doesn't block an exact proof, and the card says it was rounding.

In a proof sketch, `have` and `so` equations are tried the same way, with the values chosen so
far substituted and the assumptions `A = B` used as rewrites (a lone variable or symbol on one
side is replaced by the other) or as relations (a step that is a multiple of an assumption).
Inequality steps are tried with the prover above, using the variables' ranges, the values chosen
and every assumption so far; `choose δ = …` checks that δ is allowed the same way. A `by` with a
reason that isn't a lemma's name doesn't stop the algebra. Such a step is marked **exact**; a proof whose every step is exact or structural is reported as
proved. An induction whose base and step are exact is a complete proof.

### Claims sampling can't decide

Some claims have a shape that sampling answers wrongly, and always the same way: they hold on every
sample while being false. When a claim that holds on its samples has one of these shapes (in its
statement or in a definition it uses), the card says so instead of a plain "holds", and explains:

- **An attained extremum**, `∃p ∈ S: ∀q ∈ S: f(q) ≤ f(p)`. p and q come from the same samples, so the
  best sample always passes, even on an open set where the maximum isn't attained. `attains_max`
  and `attains_min` (compactness) decide it by following the climb to the edge of S.
- **Close pairs**, `∀x, y ∈ S: |x − y| < δ → …` with δ chosen by an enclosing `∃`. Independent samples
  are rarely that close, so nearly every sample passes vacuously. Writing y as x + h with
  h ∈ [−δ, δ] samples close pairs.
- **A bound over an unbounded set**, `∃M: ∀x ∈ S: |x| ≤ M` where S reaches far beyond the window it
  is sampled in.

Equations (an identity element, `∃e: ∀x: e·x = x`), finite sets and ranges, and bounds under a
hypothesis that keeps x near a point (`|x − a| < δ → …`) are decided fine and get no caution.

A failure can be the search's limit rather than the claim's:

- **A deeper search.** A sample that failed because no witness was found (no δ in (0, 1], …) is
  checked again with candidates creeping much closer to the open end of the range, down to 10⁻¹⁴
  of its width instead of 10⁻⁸, and with exact comparisons, so tolerance can't blur a jump away.
  Samples that pass then count as holding. This is what makes √x on [0, 1] uniformly continuous:
  its δ must be about ε².
- **Failures that may not be real** are flagged instead of reported as plain failures: every
  failing sample is an example built to fool finite checks (a sequence converging like 1/log n, one
  that differs from a constant only at powers of 2), or the claim fails only at tiny ε, holds for
  every larger ε, and the deeper search rescued some samples (the δ needed shrinks faster than
  floating point can follow, as for x^(1/5)).
- **Known facts of examples.** Sequences sampled from `Seq(X)` are built to converge (to a known
  limit) or not and to stay bounded or not, so `converges_to`, `cauchy` and `bounded_seq` are
  answered from that, even for the very slow ones.

## 7. Hunting counterexamples

After sampling, a failing claim is **simplified**: each value is replaced by the simplest nearby
one that still fails (integers first, then halves, thirds, … twelfths; points coordinate by
coordinate; objects from a catalog by earlier, simpler ones, re-choosing the later variables when
needed). A failure of a strict inequality that holds in exact floating point (a rounding tie,
typically right at an open boundary) is not a counterexample. With no failures, a comparison
claim gets a **targeted search**: Nelder–Mead minimisation of the margin, from the tightest samples.

**Is every condition needed?** produces variations of the claim, at most 16: each hypothesis or
conjunct dropped, `<` and `≤` swapped, `∀`/`∃` reordered, open range ends closed and closed ones
opened, and ranges widened. Each is checked with half the usual samples. A numeric constant gets
a bisection for its **sharp** value, shown in closed form (a simple fraction, a square root of
one, π or e multiples) when one matches.

`vary name` on a definition produces the same kinds of variations of its body (and of the
definitions it calls, one level deep) and lists the examples whose answer changes.

A claim is **proved** when every case was checked and nothing in it was estimated (no sampled
range, no numerical limit, no library estimate). For a comparison in at most three real variables
over a box, **interval arithmetic** (with outward rounding) splits the box breadth-first; the proof
map shows the share proved, disproved, vacuous and open.

## 8. Structures, records and namespaces

`structure Name(f₁: T₁, f₂, …) extends Parent where ax₁: P₁ ax₂: P₂ …` defines `Name` twice over:
as a constructor, `Name(a, b, …)` making a record with those fields (each checked against its
type), and as a space, whose elements are the records that have the fields and satisfy every
axiom, the parent's included. Axioms refer to the fields by name.

- `check r in Name` checks each axiom separately and shows which fail, with counterexamples.
- `explain Name` checks each example from the structure's `# examples:` line against each axiom,
  and names, for each axiom, an example satisfying all the others: proof that it doesn't follow
  from them. When no example separates an axiom, it says so.
- `forall g in Name: …` quantifies over the examples that satisfy the axioms. Such results are
  never labelled proved.

`r.f` reads a field of a record, a member of a library (`import topology as top`, then `top.open`;
plain `import` binds the library name too), or a fact a library value carries (`a.sum`).

### Diagrams

A `diagram` names maps between finite sets or groups (records with fields `G`, `op`, `e`) and says
what should hold. It is checked at every element, and drawn with failing arrows in red:

```
diagram sign_factors:
  sign: S3 -> Cyclic(2)
  q: S3 -> Q
  sbar: Q -> Cyclic(2)
  sbar ∘ q = sign
```

- Each arrow `f: A -> B` is checked to land in B. Between two groups it is also tested for being a
  homomorphism. This is reported but doesn't make the diagram fail, since a diagram of plain maps
  is fine.
- `g ∘ f = h` compares the two paths at every element of their common source. The paths must
  start and end at the same objects.
- `exact at B` needs one arrow into B and one out of it, and checks that the image of the first is
  the kernel of the second.
- `commutes`, or a diagram with no equations, compares every two paths of up to 4 arrows with the
  same ends.

A failure names the element: `wrong(q(e)) = 0 but f(e) = 1`. Objects are written as expressions
(`Cyclic(2)`, `K`, `quotient(G, K)`), and the same text means the same object. A map may return
an element's ordinary value instead of the element: `1` for the generator of `Cyclic(2)`, or
`(2, 3, 1)` for a permutation.

## 9. Proof sketches

`proof of name:` (or `proof:` right after a theorem) is followed by steps. The checker keeps a
context (variables with ranges, assumptions, chosen values) and the remaining goal:

| Step | Context | Goal |
|---|---|---|
| `let x`, `let x in D`, `let ε > 0` | `x` ranges over D (from the goal's `∀` when no range is given) | peels `∀x` |
| `assume P` | adds P | peels `P ⇒`; a different P is checked to follow from the goal's hypothesis |
| `choose x = e` | x is e | answers `∃x ∈ D`: checks that e is in D |
| `choose x in D such that P` | x ranges over D with P | checks that such an x exists |
| `have P` | checks P, then adds it | unchanged |
| `so P` | checks P | closes the goal if P is it, or numerically implies it |

Blocks hold steps on lines indented below a header, and each runs in its own copy of the context:

| Step | What is checked | Goal |
|---|---|---|
| `case P:` … `case Q:` … | that P ∨ Q holds in the context (no check with `otherwise:`, which takes what the others leave) | each case starts from the current goal, with its condition assumed; the goal is reached when every case reaches it |
| `induction on n` | the goal must be `∀n ∈ ℕ` or `∀n ∈ a..b` | splits into `base:` P(a) and `step:` ∀n: P(n) ⇒ P(n + 1); a missing block is checked directly |
| `contradiction` | the goal itself, to say whether the steps below will be tested | assumes the goal fails; the goal becomes `false`, reached by `so false` |
| `have P by lemma` | P is matched to the lemma's conclusion (or a conjunct of it), then the lemma's hypothesis and ranges are checked with the matched values, and P too | unchanged |

Under `contradiction`, a step whose assumptions never hold on the samples is reported as holding
vacuously: that is what should happen when the theorem is true. In an induction step the
hypothesis P(n) is usually rare for a false formula, so a wrong formula fails at a small n.

Each check is a claim `∀ (variables): (assumptions) ⇒ P` with the chosen values substituted, and
an assumption `|x − c| < r` narrows x's range so samples aren't wasted. Goals that are calls to
definitions are unfolded when a step needs a `∀`, `⇒` or `∃`. Click a step to see its check.

### Formulas, decided exactly

A lambda remembers its formula. For a sequence `n => …` or a function `x => …` built from numbers,
the variable, + − · / ^, sqrt, exp, ln, log, sin, cos, tan, atan, abs, floor, ceil, !, `if` (whose
condition is decided eventually) and other one-line definitions, the asymptotics library expands it
as n → ∞ (or, for f near a, f(a ± 1/t) as t → ∞) and answers `lim`, `convergent`, `summable`,
`converges_to`, `cauchy`, `bounded_seq`, `series_converges`, `continuous_at`, `differentiable_at` and
`continuously_differentiable_at` exactly. When the expansion can't decide, sampling decides as before.

### Exact reals and facts

An exact real is a fraction p/q, a number a + b√r (a, b fractions, r square-free), or a known
irrational (π/4, a Cantor-set point with known digits). Arithmetic keeps exactness where the kind of
the result is known: fractions with fractions, ℚ(√r) with itself, a known irrational with a nonzero
fraction; otherwise the result is a float. Number literals count as fractions where they meet exact
numbers, and `sqrt` of a fraction is exact. `is_rational` and `denominator` are exact for exact
reals and a guess for floats (marked as an estimate).

A claim is **kind-sensitive** when it (or a definition it uses, or a catalog it ranges over) involves
ℚ, `Irrationals`, `is_rational`, `denominator` or an object marked as depending on rationality
(Dirichlet, Thomae, the Cantor set). Its real intervals are then sampled with exact fractions and
exact irrationals, including √2, √2/2 and multiples of π; the simplest counterexample tries simple
fractions and simple irrationals, and pairs of them.

A call to a library definition whose arguments carry a **fact** about it (see Facts in README.md) is answered by
the fact instead of being evaluated, and is not unfolded inside claims; the why view cites the fact.

## 10. explain

`explain name` shows what a name means:

- **A definition**: its statement with parameter types, its documentation, a plain-English
  reading of the formula (nested by quantifier), the names it uses (each can be explained in
  turn), and a gallery: the definition applied to examples, each marked as satisfying it or not.
  Examples come from `for` (as in `explain open for S in {Disk((0, 0), 1)}`), then from the
  definition's `# examples:` line, then from parameter types: `Set` uses `Subsets(R^2)`, `Fun` uses
  `Functions(R)`, `Seq(…)` uses `Sequences(R)`, a finite set uses its elements, and numbers use
  −1, 0, 1 (or −1 and 1 for a pair of bounds).
- **A lemma or theorem**: its statement, reading and check.
- **A function, set or space**: its documentation and a picture where possible.

Every gallery tile, table cell and counterexample can be clicked to show **why**: the claim
evaluated step by step, with the parts of each connective, the counterexample of a failing
`forall`, the witness of an `exists`, and each definition unfolded with its arguments.

### concept: one notion, several definitions

```
# A number is even, three ways.
# examples: n in -4..10
concept even(n: Z) where
  remainder: n mod 2 = 0
  half: exists k in -20..20: n = 2*k
  parity: (-1)^n = 1
```

`concept name(p₁, …) where form: formula …` states one notion together with its equivalent
definitions. Each form becomes a definition of its own, `name_form` (`even_half(9)` is false), and
`name` itself is the first form, so the concept is used like any other definition. Without
parameters, the forms are values: `concept golden where root: (1 + sqrt(5))/2  fraction: …`.

The concept's card (and `explain name`) evaluates every form on the examples — from `for`, the
`# examples:` line, or the parameter types, as for `explain` — up to 64 of them, and shows a table
with a column per form and whether they agree. Disagreements come first; a cell opens that form's
own check on that example. Agreement on examples is evidence of equivalence, not a proof; forms
that really differ (a condition missing in one of them) show exactly where.

In a library, a concept with an `# examples:` line also adds the lemma `name_forms_agree`, so the
test suite checks the forms agree on those examples (at the usual stress level: the wild examples
are sampled differently by different forms).

### interpret: every way of looking at something

- `interpret name(args)`, for a concept: every form at those arguments, side by side, each checked
  and drawn on its own (`interpret on_manifold(M, p)`, `interpret coprime(12, 35)`).
- `interpret value`: every representation the libraries know for it, one section each — a matrix
  as a linear map, by its eigenvectors, as a quadratic form and by row reduction; a whole number as
  a product of primes and in other bases; a real number as a continued fraction; a complex number in
  polar form and as a rotation; a function by its graph, slopes, Taylor polynomials, area function
  and Fourier series; a submanifold by a parametrization, local equations, a local graph and a
  straightening; a graph by a drawing, matrices and its spectrum; a formula of logic by its truth
  table, normal forms and Venn diagram. Sliders are shared: one "point" slider moves the point in
  every picture. Below them, "As an instance of" lists the one-parameter concepts in scope that
  apply to the value and whether it is one.

Libraries add representations with `MathViz.represent` (see `README.md`).

## 11. Errors

Errors name the line and point at the column. Unknown names suggest the library that defines
them; operators applied to values they don't support suggest the library that does; argument
counts and typed parameters are checked at each call.

## 12. Words

**Words…** in the notebook toolbar turns English sentences (one per line) into notation. It knows:

- statements: `prove that …`, `define f(x) to be …`, `let a be 3`, `plot … for x from a to b`,
  `what is …`;
- quantifiers: `for every / for all / for each / for any …`, `there is / there exists … such that`
  (or `with`), also at the end of a sentence (`… for every natural number n`), with kinds of
  numbers (`real`, `natural`, `integer`, `positive real`, `positive integer`) and ranges (`in [0, 1]`,
  `between a and b`, `from a to b`, `> 0`); a one-letter variable never introduced is taken for all
  values (integers if the sentence speaks of even, odd or prime, reals otherwise), and the panel
  says so;
- logic: `if … then`, `implies`, `if and only if`, `whenever`, `and`, `or`, `not`;
- comparisons: `is (greater|less) than`, `is at least / at most`, `exceeds`, `equals`, `is between a and
  b`, `divides`, `is divisible by`;
- properties: `even`, `odd`, `prime`, `positive`, `negative`, `nonnegative`, `an integer`, `rational`,
  `a perfect square`; for functions `continuous`, `differentiable`, `bounded`, `increasing`, `convex`
  (`on [a, b]`, `at a`); for sequences `convergent`, `bounded`, `Cauchy`, `increasing`; for sets `open`,
  `closed`, `bounded`, `compact`; for groups `abelian`, `cyclic`, `of order n`;
- claims about kinds of objects: `every / no / some (adjectives) function | sequence | set | group |
  prime (qualifiers) is …`, checked over the example catalogs (with the library imported);
- arithmetic: `plus`, `minus`, `times`, `divided by`, `over`, `squared`, `cubed`, `to the power of`,
  `factorial`, `the square root of`, `the absolute value of`, `sine / cosine / log / exp of`,
  `the sum / product / difference / quotient of a and b`, `the square of`, `twice`, `half of`,
  `the maximum / minimum of`, `the sum of … for k from 1 to n`, `the sum from k = 1 to n of …`,
  `the sum of the first n odd numbers`, `the limit of … as n goes to infinity`, number words, Greek
  letter names, and notation written directly (`x^2 + 1`, `[0, 1]`, `f(x)`).

Each translation is parsed before it is offered. A sentence with words left over, or one that
ended early, is marked **?** for review and inserted commented out; the original sentence is kept
as a comment above the notation.

## 13. Libraries

A notation library is `library name` followed by `import`, `let`, `def`, `structure`, `concept` and named lemmas
(`lemma name: …`, also `theorem`, `claim`, `conjecture`). A JavaScript library calls
`MathViz.define` and may carry a `notation` string with definitions and lemmas of its own, run
after its exports and its `requires`. See `README.md` for the API.

The libraries `core`, `catalog` (example objects) and `geometry` (shapes) are always loaded.
