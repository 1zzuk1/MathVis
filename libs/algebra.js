MathVizLibrary(function algebra(MathViz) {
  const named = (fn, label) => { fn.label = label; return fn; };
  const whole = (n, what) => { if (!Number.isInteger(n) || n < 1) throw MathViz.error(`${what} must be a whole number ≥ 1.`); return n; };
  const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a; };
  const mod = (a, n) => ((a % n) + n) % n;
  // Cycle notation for a permutation given as a list of images: (2, 3, 1) is (1 2 3).
  const cycles = p => {
    const seen = new Set(), out = [];
    for (let i = 1; i <= p.length; i++) {
      if (seen.has(i)) continue;
      const cyc = [];
      for (let j = i; !seen.has(j); j = p[j - 1]) { seen.add(j); cyc.push(j); }
      if (cyc.length > 1) out.push('(' + cyc.join(' ') + ')');
    }
    return out.join('') || 'e';
  };
  const isPerm = v => Array.isArray(v) && v.length > 1 && v.every(Number.isInteger) && new Set(v).size === v.length && v.every(x => x >= 1 && x <= v.length);
  const SUB = n => String(n).split('').map(c => '₀₁₂₃₄₅₆₇₈₉'[+c]).join('');

  const Zmod = n => MathViz.finite(Array.from({ length: whole(n, 'n') }, (_, k) => k), { label: `ℤ/${n}` });
  const Units = n => MathViz.finite(Array.from({ length: whole(n, 'n') }, (_, k) => k).filter(k => gcd(k, n) === 1), { label: `(ℤ/${n})ˣ` });
  const perms = n => {
    if (n > 5) throw MathViz.error('Sym(n) is limited to n ≤ 5 (120 permutations).');
    const out = [];
    const rec = (cur, rest) => { if (!rest.length) { out.push(cur); return; } rest.forEach((x, i) => rec([...cur, x], [...rest.slice(0, i), ...rest.slice(i + 1)])); };
    rec([], Array.from({ length: n }, (_, k) => k + 1));
    return out;
  };
  const Sym = n => MathViz.finite(perms(whole(n, 'n')), { label: `S${SUB(n)}` });
  const compose = named((p, q) => {
    if (!Array.isArray(p) || !Array.isArray(q) || p.length !== q.length) throw MathViz.error('compose expects two permutations of the same size, as in compose((2, 1, 3), (1, 3, 2)).');
    return q.map(i => p[i - 1]);
  }, '∘');
  const add = n => named((a, b) => mod(a + b, n), `+ mod ${n}`);
  const mul = n => named((a, b) => mod(a * b, n), `· mod ${n}`);
  const sub = n => named((a, b) => mod(a - b, n), `− mod ${n}`);
  // An operation on {0, …, n − 1} given by its table: T[a][b] is a·b.
  const tableOp = T => {
    if (!Array.isArray(T) || !T.every(r => Array.isArray(r) && r.length === T.length)) throw MathViz.error('table_op needs a square table, as in table_op([[0, 1], [1, 0]]).');
    return named((a, b) => {
      if (!(Number.isInteger(a) && Number.isInteger(b) && a >= 0 && b >= 0 && a < T.length && b < T.length)) return NaN;
      return T[a][b];
    }, `table(${T.length}×${T.length})`);
  };
  const pair = (op, G, label) => { const a = [op, G]; a.label = label; return a; };
  let magmas = null;
  const Magmas = () => magmas || (magmas = MathViz.finite([
    pair(add(6), Zmod(6), '(ℤ/6, +)'),
    pair(mul(6), Zmod(6), '(ℤ/6, ·)'),
    pair(mul(7), MathViz.finite([1, 2, 3, 4, 5, 6], { label: 'ℤ/7 ∖ {0}' }), '(ℤ/7 ∖ {0}, ·)'),
    pair(mul(8), Units(8), '((ℤ/8)ˣ, ·)'),
    pair(compose, Sym(3), '(S₃, ∘)'),
    pair(sub(5), Zmod(5), '(ℤ/5, −)'),
    pair(named((a, b) => Math.max(a, b), 'max'), Zmod(4), '(ℤ/4, max)'),
    pair(named((a, b) => Math.min(a, b) - 1, 'min − 1'), Zmod(4), '({0, …, 3}, min − 1)'),
  ], { label: 'example magmas' }));

  /* ---------- ways of looking at a permutation (interpret) ---------- */
  const permOk = v => isPerm(v) && v.length <= 9;
  const sign = p => { let s = 1; const seen = new Set(); for (let i = 1; i <= p.length; i++) { if (seen.has(i)) continue; let len = 0; for (let j = i; !seen.has(j); j = p[j - 1]) { seen.add(j); len++; } if (len % 2 === 0) s = -s; } return s; };
  MathViz.represent({
    name: 'permutation_forms', label: 'A permutation: cycles, two-line notation and a matrix', test: permOk,
    doc: 'The list (2, 3, 1) of images is the bijection 1 ↦ 2, 2 ↦ 3, 3 ↦ 1: in cycle notation (1 2 3), and as the matrix with a 1 in row p(j) of column j, which permutes the coordinates.',
    render(ctx, p) {
      const n = p.length;
      ctx.table(['form', ''], [['images', '(' + p.join(', ') + ')'], ['cycles', cycles(p)], ['sign', `${sign(p) > 0 ? '+1 (even)' : '−1 (odd)'}`]]);
      ctx.table(['i', ...p.map((_, i) => String(i + 1))], [['p(i)', ...p.map(String)]], 'two-line notation');
      ctx.table(['', ...p.map((_, j) => String(j + 1))], p.map((_, i) => [String(i + 1), ...p.map(pj => (pj === i + 1 ? '1' : '·'))]), 'permutation matrix: column j has its 1 in row p(j)');
      // Arrows from i to p(i) between two rows of points.
      const fig = ctx.figure({ x: [0.3, n + 0.7], y: [-0.4, 1.4], height: 150, xAxis: false, yAxis: false, static: true });
      for (let i = 1; i <= n; i++) {
        fig.arrow(i, 1, p[i - 1], 0.08, { color: p[i - 1] === i ? 'faint' : 'c1', width: 1.6 });
        fig.text(i, 1.2, String(i), { align: 'center', color: 'ink' }); fig.text(i, -0.2, String(i), { align: 'center', color: 'ink' });
      }
    },
  });

  MathViz.define({
    name: 'algebra',
    description: 'Finite algebraic structures: ℤ/n with its operations, unit groups, symmetric groups, example magmas to test axioms on, the group axioms, and Cayley tables.',
    functions: {
      add_mod: { doc: 'add_mod(n): addition modulo n, as a function of two arguments.', fn: add },
      mul_mod: { doc: 'mul_mod(n): multiplication modulo n.', fn: mul },
      sub_mod: { doc: 'sub_mod(n): subtraction modulo n.', fn: sub },
      table_op: { doc: 'table_op(T): the operation on {0, …, n − 1} with a·b = T[a][b], for operations given by a Cayley table.', fn: tableOp },
      cycles: { doc: 'cycles(p): a permutation in cycle notation, as in cycles((2, 3, 1)) = (1 2 3).', fn: cycles },
      compose: { doc: 'compose(p, q): the permutation p ∘ q (apply q first). Permutations are written as lists of images, as in (2, 3, 1).', fn: compose },
      order: { doc: 'order(x, op, e): the smallest k ≥ 1 with x·x·…·x (k times) = e, or undefined after 1000 steps.', fn: (x, op, e) => {
        let y = x;
        for (let k = 1; k <= 1000; k++) { if (MathViz.ops.eq(y, e)) return k; y = op(y, x); }
        return NaN;
      } },
    },
    constants: {
      comp: compose,
      max_op: named((a, b) => Math.max(a, b), 'max'),
      // The smallest loop that is not a group: identity 0, every element its own inverse, not associative.
      loop5: named(tableOp([[0, 1, 2, 3, 4], [1, 0, 3, 4, 2], [2, 4, 0, 1, 3], [3, 2, 4, 0, 1], [4, 3, 1, 2, 0]]), 'loop₅'),
    },
    spaces: {
      Zmod: { doc: 'Zmod(n): ℤ/n = {0, 1, …, n − 1}.', fn: Zmod },
      Units: { doc: 'Units(n): the residues mod n that are coprime to n.', fn: Units },
      Sym: { doc: 'Sym(n): the permutations of 1..n (n ≤ 5).', fn: Sym },
      Magmas: { doc: 'Magmas: pairs (op, G) such as (ℤ/6, +), (ℤ/6, ·), (S₃, ∘) and (ℤ/5, −), for testing axioms. Use as "forall (op, G) in Magmas: …".', fn: Magmas },
    },
    views: {
      cayley: {
        doc: 'cayley(op, G) draws the operation table of op on a finite set G, one color per element.',
        render(ctx, op, G) {
          G = MathViz.toDomain(G);
          if (G.kind !== 'finite' || G.values.length > 30) throw MathViz.error('cayley needs a finite set with at most 30 elements.');
          const els = G.values, n = els.length;
          const index = v => els.findIndex(u => MathViz.ops.eq(u, v));
          const name = v => isPerm(v) ? cycles(v) : MathViz.format(v);
          const hue = i => `hsl(${Math.round(360 * i / n)}, 55%, 60%)`;
          const fig = ctx.figure({ x: [-1, n], y: [-n, 1], square: true, xAxis: false, yAxis: false });
          let closed = true;
          const cells = [];
          for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
            const k = index(op(els[i], els[j]));
            if (k < 0) closed = false;
            cells.push({ x: j + 0.5, y: -i - 0.5, w: 0.96, h: 0.96, c: k < 0 ? 'neg' : hue(k), a: 0.85 });
          }
          fig.cells(cells);
          if (n <= 12 && els.every(v => name(v).length <= 7)) {
            const font = `${n <= 6 ? 13 : 10}px "JetBrains Mono", monospace`;
            for (let i = 0; i < n; i++) {
              fig.text(i + 0.5, 0.5, name(els[i]), { color: 'muted', align: 'center', font });
              fig.text(-0.5, -i - 0.5, name(els[i]), { color: 'muted', align: 'center', font });
              for (let j = 0; j < n; j++) fig.text(j + 0.5, -i - 0.5, name(op(els[i], els[j])), { color: 'ink', align: 'center', font });
            }
          }
          ctx.note(`Row x, column y shows ${MathViz.format(op)}(x, y). ${closed ? 'Every entry lies in the set, so it is closed under the operation.' : 'Red entries fall outside the set.'} A group's table has every element exactly once in each row and column.`);
        },
      },
    },
    notation: `
# op keeps G closed: combining two elements of G gives an element of G.
# examples: (op, G) in Magmas
def closed_under(op: Fun, G: Set) := forall x, y in G: op(x, y) in G

# op is associative on G.
# examples: (op, G) in Magmas
def associative(op: Fun, G: Set) := forall x, y, z in G: op(op(x, y), z) = op(x, op(y, z))

# op is commutative on G.
# examples: (op, G) in Magmas
def commutative(op: Fun, G: Set) := forall x, y in G: op(x, y) = op(y, x)

# e is an identity element for op on G.
def identity_element(e, op: Fun, G: Set) := forall x in G: op(e, x) = x and op(x, e) = x

# op has an identity element on G.
# examples: (op, G) in Magmas
def has_identity(op: Fun, G: Set) := exists e in G: identity_element(e, op, G)

# op has an identity element, and every element has an inverse.
# examples: (op, G) in Magmas
def has_inverses(op: Fun, G: Set) := exists e in G: identity_element(e, op, G) and (forall x in G: exists y in G: op(x, y) = e and op(y, x) = e)

# (G, op) is a group: closed, associative, with identity and inverses.
# examples: (op, G) in Magmas
def is_group(op: Fun, G: Set) := closed_under(op, G) and associative(op, G) and has_inverses(op, G)

# A magma: a set G with an operation op that keeps G closed.
# examples: Magma(Zmod(6), add_mod(6)), Magma(Zmod(5), sub_mod(5)), Magma(Zmod(4), max_op), Magma(Zmod(4), (a, b) => a + b)
structure Magma(G: Set, op: Fun) where
  closed: forall x, y in G: op(x, y) in G

# A semigroup: a magma whose operation is associative.
# examples: Semigroup(Zmod(6), mul_mod(6)), Semigroup(Zmod(5), sub_mod(5)), Semigroup(Zmod(4), max_op), Semigroup({-1, 0, 1}, (a, b) => a + b)
structure Semigroup(G: Set, op: Fun) extends Magma where
  associative: forall x, y, z in G: op(op(x, y), z) = op(x, op(y, z))

# A monoid: a semigroup with an identity element e.
# examples: Monoid(Zmod(6), mul_mod(6), 1), Monoid(Zmod(4), max_op, 0), Monoid(Zmod(6), add_mod(6), 1), Monoid(Zmod(5), loop5, 0)
structure Monoid(G: Set, op: Fun, e) extends Semigroup where
  identity: e in G and (forall x in G: op(e, x) = x and op(x, e) = x)

# A group: a monoid in which every element has an inverse.
# examples: Group(Zmod(6), add_mod(6), 0), Group(Units(8), mul_mod(8), 1), Group(Sym(3), compose, (1, 2, 3)), Group({-1, 0, 1}, (a, b) => a + b, 0), Group(Zmod(5), loop5, 0), Group(Zmod(6), add_mod(6), 1), Group(Zmod(6), mul_mod(6), 1)
structure Group(G: Set, op: Fun, e) extends Monoid where
  inverses: forall x in G: exists y in G: op(x, y) = e and op(y, x) = e

# An abelian group: a group whose operation is commutative.
# examples: AbelianGroup(Zmod(6), add_mod(6), 0), AbelianGroup(Units(8), mul_mod(8), 1), AbelianGroup(Sym(3), compose, (1, 2, 3)), AbelianGroup(Zmod(6), mul_mod(6), 1)
structure AbelianGroup(G: Set, op: Fun, e) extends Group where
  commutative: forall x, y in G: op(x, y) = op(y, x)

# A ring with 1: an abelian group under add, a monoid under mul, and mul distributes over add.
# examples: Ring(Zmod(6), add_mod(6), mul_mod(6), 0, 1), Ring(Zmod(5), add_mod(5), mul_mod(5), 0, 1), Ring(Zmod(6), add_mod(6), max_op, 0, 0), Ring(Zmod(6), mul_mod(6), add_mod(6), 1, 0)
structure Ring(R: Set, add: Fun, mul: Fun, zero, one) where
  additive_group: AbelianGroup(R, add, zero) in AbelianGroup
  multiplicative_monoid: Monoid(R, mul, one) in Monoid
  distributive: forall x, y, z in R: mul(x, add(y, z)) = add(mul(x, y), mul(x, z)) and mul(add(x, y), z) = add(mul(x, z), mul(y, z))

# A field: a commutative ring, with 0 ≠ 1, in which every nonzero element has an inverse.
# examples: Field(Zmod(5), add_mod(5), mul_mod(5), 0, 1), Field(Zmod(7), add_mod(7), mul_mod(7), 0, 1), Field(Zmod(6), add_mod(6), mul_mod(6), 0, 1), Field(Zmod(4), add_mod(4), mul_mod(4), 0, 1), Field(Zmod(1), add_mod(1), mul_mod(1), 0, 0)
structure Field(R: Set, add: Fun, mul: Fun, zero, one) extends Ring where
  commutative: forall x, y in R: mul(x, y) = mul(y, x)
  nontrivial: zero != one
  inverses: forall x in R: x != zero -> exists y in R: mul(x, y) = one

# Some small groups, to quantify over: forall g in SmallGroups: …
let SmallGroups = {Group(Zmod(1), add_mod(1), 0), Group(Zmod(2), add_mod(2), 0), Group(Zmod(4), add_mod(4), 0), Group(Units(8), mul_mod(8), 1), Group(Zmod(6), add_mod(6), 0), Group(Sym(3), compose, (1, 2, 3)), Group(Units(7), mul_mod(7), 1), Group(Sym(4), compose, (1, 2, 3, 4))}

# The order of an element divides the order of the group (Lagrange).
lemma lagrange_order: forall g in SmallGroups: forall x in g.G: |g.G| mod order(x, g.op, g.e) = 0

# Inverses in a group are unique.
lemma inverse_unique: forall g in SmallGroups: forall x, y, z in g.G: g.op(x, y) = g.e and g.op(x, z) = g.e -> y = z

# Is every group abelian?
conjecture groups_are_abelian: forall g in SmallGroups: g in AbelianGroup

# If x·x = e for every x, the group is abelian.
lemma exponent_two_abelian: forall g in SmallGroups: (forall x in g.G: g.op(x, x) = g.e) -> g in AbelianGroup

# A magma has at most one identity element.
lemma identity_is_unique: forall (op, G) in Magmas: forall e, f in G: identity_element(e, op, G) and identity_element(f, op, G) -> e = f

# Not every group is commutative.
conjecture groups_commute: forall (op, G) in Magmas: is_group(op, G) -> commutative(op, G)
`,
  });
});
