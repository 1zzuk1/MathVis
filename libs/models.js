MathVizLibrary(function models(MathViz) {
  /* Every small model: all groups up to order 8, all topologies on up to 4 points, all partial
     orders on up to 4 points, all relations on up to 3 points, all binary operations on up to 3
     elements (each up to isomorphism), and all maps between small sets. The lists are complete
     and ordered by size, so a claim checked over them is checked for every model of that size, and
     the first counterexample is a smallest one. */
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };
  const fin = (vals, label) => MathViz.finite(vals, label ? { label } : {});
  const range = n => Array.from({ length: n }, (_, i) => i);
  const SUB = n => String(n).split('').map(c => '₀₁₂₃₄₅₆₇₈₉'[+c]).join('');
  function perms(n) {
    const out = [];
    const rec = (cur, rest) => { if (!rest.length) { out.push(cur); return; } rest.forEach((x, i) => rec([...cur, x], [...rest.slice(0, i), ...rest.slice(i + 1)])); };
    rec([], range(n));
    return out;
  }
  // Keep one representative of each isomorphism class: enc(obj, perm) must describe obj relabelled by perm.
  function upToIso(objs, n, enc) {
    const P = perms(n), seen = new Set(), out = [];
    for (const o of objs) {
      let best = null;
      for (const p of P) { const e = enc(o, p); if (best === null || e < best) best = e; }
      if (!seen.has(best)) { seen.add(best); out.push(o); }
    }
    return out;
  }
  const memo = {};
  const cached = (key, make) => memo[key] || (memo[key] = make());

  /* ---------- groups of order ≤ 12 (all 24, up to isomorphism) ----------
     Elements are named objects (i, −k, (1 2 3), r²s): one object per element, so equality is
     identity and counterexamples print readably. */
  // An operation on {0, …, n − 1} from its table (binary operations on small sets).
  const tableOp = (T, label) => Object.assign((a, b) => (Number.isInteger(a) && Number.isInteger(b) && a >= 0 && b >= 0 && a < T.length && b < T.length ? T[a][b] : NaN), { label });
  const SUP = n => String(n).split('').map(c => '⁰¹²³⁴⁵⁶⁷⁸⁹'[+c]).join('');
  const power = (x, k) => (k === 0 ? '' : k === 1 ? x : x + SUP(k));
  // A group from its elements (identity first), multiplication and names.
  // raw(x): the element as an ordinary value, so (1 2 3) can be written (2, 3, 1).
  function groupFrom(elems, mul, eq, label, name, raw = null) {
    const idx = x => elems.findIndex(y => eq(x, y));
    const T = elems.map(a => elems.map(b => idx(mul(a, b))));
    const E = elems.map((x, i) => Object.freeze({ __elt: true, i, label: name(x, i), raw: raw ? raw(x) : undefined }));
    const op = Object.assign((a, b) => (a && b && a.__elt && b.__elt && E[a.i] === a && E[b.i] === b ? E[T[a.i][b.i]] : NaN), { label: `·` });
    const r = MathViz.record({ G: fin(E, `{${E.map(x => x.label).join(', ')}}`), op, e: E[0] }, label);
    r.table = T;
    return r;
  }
  const eqNum = (a, b) => a === b, eqArr = (a, b) => a.every((x, i) => x === b[i]);
  const cyclic = n => groupFrom(range(n), (a, b) => (a + b) % n, eqNum, `ℤ/${n}`, x => String(x), x => x);
  const product = (ns, label) => {
    const elems = ns.reduce((acc, n) => acc.flatMap(t => range(n).map(x => [...t, x])), [[]]);
    return groupFrom(elems, (a, b) => a.map((x, i) => (x + b[i]) % ns[i]), eqArr, label, x => `(${x.join(', ')})`, x => x.slice());
  };
  const compose = (p, q) => q.map(i => p[i]);
  const cyc = p => {
    const seen = new Set(), out = [];
    for (let i = 0; i < p.length; i++) {
      if (seen.has(i)) continue;
      const c = [];
      for (let j = i; !seen.has(j); j = p[j]) { seen.add(j); c.push(j + 1); }
      if (c.length > 1) out.push('(' + c.join(' ') + ')');
    }
    return out.join('') || 'e';
  };
  const parity = p => { let s = 0; for (let i = 0; i < p.length; i++) for (let j = i + 1; j < p.length; j++) if (p[i] > p[j]) s++; return s % 2; };
  const sym = n => groupFrom(perms(n), compose, eqArr, `S${'₀₁₂₃₄₅₆₇₈₉'[n]}`, cyc, p => p.map(i => i + 1));
  const alt4 = () => groupFrom(perms(4).filter(p => !parity(p)), compose, eqArr, 'A₄ (even permutations of 4)', cyc, p => p.map(i => i + 1));
  // Dₙ: rᵏsʲ with (k1, j1)(k2, j2) = (k1 + (−1)^j1·k2, j1 + j2).
  const dihedral = (n, label) => groupFrom(range(2).flatMap(j => range(n).map(k => [k, j])),
    (a, b) => [(((a[0] + (a[1] ? -b[0] : b[0])) % n) + n) % n, (a[1] + b[1]) % 2], eqArr, label, ([k, j]) => (k === 0 && j === 0 ? 'e' : power('r', k) + (j ? 's' : '')));
  // Q₈ = {±1, ±i, ±j, ±k} as quaternions.
  const qmul = (a, b) => [a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3], a[0] * b[1] + a[1] * b[0] + a[2] * b[3] - a[3] * b[2],
    a[0] * b[2] - a[1] * b[3] + a[2] * b[0] + a[3] * b[1], a[0] * b[3] + a[1] * b[2] - a[2] * b[1] + a[3] * b[0]];
  const QN = ['1', '−1', 'i', '−i', 'j', '−j', 'k', '−k'];
  const q8 = () => groupFrom([[1, 0, 0, 0], [-1, 0, 0, 0], [0, 1, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, -1, 0], [0, 0, 0, 1], [0, 0, 0, -1]], qmul, eqArr, 'Q₈ (quaternions)', (x, i) => QN[i]);
  // The dicyclic group of order 12: aᵏxʲ with a⁶ = 1, x² = a³, x·a = a⁻¹·x.
  const dic3 = () => groupFrom(range(2).flatMap(j => range(6).map(k => [k, j])), (u, v) => {
    const [i, j] = u, [k, l] = v;
    if (!j) return [(i + k) % 6, l];
    // x·aᵏ = a⁻ᵏ·x
    const e = ((i - k) % 6 + 6) % 6;
    return l ? [(e + 3) % 6, 0] : [e, 1];
  }, eqArr, 'Dic₃ (dicyclic, order 12)', ([k, j]) => (k === 0 && j === 0 ? 'e' : power('a', k) + (j ? 'x' : '')));
  const groups = () => cached('groups', () => [
    cyclic(1), cyclic(2), cyclic(3), cyclic(4), product([2, 2], 'ℤ/2 × ℤ/2 (Klein)'), cyclic(5), cyclic(6), sym(3), cyclic(7),
    cyclic(8), product([4, 2], 'ℤ/4 × ℤ/2'), product([2, 2, 2], 'ℤ/2 × ℤ/2 × ℤ/2'), dihedral(4, 'D₄ (symmetries of a square)'), q8(),
    cyclic(9), product([3, 3], 'ℤ/3 × ℤ/3'), cyclic(10), dihedral(5, 'D₅ (symmetries of a pentagon)'), cyclic(11),
    cyclic(12), product([6, 2], 'ℤ/6 × ℤ/2'), alt4(), dihedral(6, 'D₆ (symmetries of a hexagon)'), dic3(),
  ]);
  const AllGroups = (n = 8) => {
    need(Number.isInteger(n) && n >= 1 && n <= 12, 'AllGroups(n) lists every group of order at most n, for n up to 12.');
    return cached('G' + n, () => fin(groups().filter(g => g.fields.G.values.length <= n), `all groups of order ≤ ${n}`));
  };
  MathViz.shared.groupMakers = { sym, cyclic, dihedral, q8, alt4 };

  /* ---------- topologies on ≤ 4 points (up to homeomorphism) ---------- */
  const setOf = (mask, n) => fin(range(n).filter(i => mask >> i & 1).map(i => i + 1));
  const permMask = (m, p) => { let r = 0; for (let i = 0; i < p.length; i++) if (m >> i & 1) r |= 1 << p[i]; return r; };
  function topologies(n) {
    const full = (1 << n) - 1, mids = range(full + 1).filter(m => m !== 0 && m !== full), out = [];
    for (let pick = 0; pick < 1 << mids.length; pick++) {
      const T = [0, full, ...mids.filter((_, i) => pick >> i & 1)];
      const has = new Set(T);
      let ok = true;
      for (const a of T) { for (const b of T) if (!has.has(a | b) || !has.has(a & b)) { ok = false; break; } if (!ok) break; }
      if (ok) out.push(T.sort((a, b) => a - b));
    }
    return upToIso(out, n, (T, p) => T.map(m => permMask(m, p)).sort((a, b) => a - b).join(','))
      .sort((a, b) => a.length - b.length);
  }
  const fmtSet = (m, n) => { const xs = range(n).filter(i => m >> i & 1).map(i => i + 1); return xs.length ? `{${xs.join(', ')}}` : '∅'; };
  const AllTopologies = (n = 4) => {
    need(Number.isInteger(n) && n >= 1 && n <= 4, 'AllTopologies(n) lists every topology on 1 to n points (n up to 4), up to homeomorphism.');
    return cached('T' + n, () => fin(range(n).flatMap(k => topologies(k + 1).map(T => MathViz.record({
      X: setOf((1 << (k + 1)) - 1, k + 1), T: fin(T.map(m => setOf(m, k + 1))),
    }, `({${range(k + 1).map(i => i + 1).join(', ')}}, {${T.map(m => fmtSet(m, k + 1)).join(', ')}})`))), `all topologies on ≤ ${n} points`));
  };

  /* ---------- partial orders on ≤ 4 points, relations on ≤ 3 points ---------- */
  const relEnc = (R, p) => { const n = R.length, S = range(n).map(() => new Array(n).fill(0)); for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) if (R[a][b]) S[p[a]][p[b]] = 1; return S.map(r => r.join('')).join('/'); };
  function allRelations(n) {
    const out = [];
    for (let m = 0; m < 1 << (n * n); m++) out.push(range(n).map(a => range(n).map(b => (m >> (a * n + b)) & 1)));
    return out;
  }
  const isPoset = R => {
    const n = R.length;
    for (let a = 0; a < n; a++) { if (!R[a][a]) return false; for (let b = 0; b < n; b++) { if (a !== b && R[a][b] && R[b][a]) return false; for (let c = 0; c < n; c++) if (R[a][b] && R[b][c] && !R[a][c]) return false; } }
    return true;
  };
  const relFn = (R, name) => Object.assign((a, b) => (Number.isInteger(a) && Number.isInteger(b) && a >= 1 && b >= 1 && a <= R.length && b <= R.length ? !!R[a - 1][b - 1] : false), { label: name });
  const pairs = R => { const out = []; R.forEach((r, a) => r.forEach((v, b) => { if (v) out.push([a + 1, b + 1]); })); return out; };
  const covers = R => pairs(R).filter(([a, b]) => a !== b && !R.some((_, c) => c + 1 !== a && c + 1 !== b && R[a - 1][c] && R[c][b - 1]));
  const AllPosets = (n = 4) => {
    need(Number.isInteger(n) && n >= 1 && n <= 4, 'AllPosets(n) lists every partial order on 1 to n points (n up to 4), up to isomorphism.');
    return cached('P' + n, () => fin(range(n).flatMap(k => upToIso(allRelations(k + 1).filter(isPoset), k + 1, relEnc).map(R => {
      const cs = covers(R);
      const label = `poset on ${k + 1} point${k ? 's' : ''}: ${cs.length ? cs.map(([a, b]) => `${a} < ${b}`).join(', ') : 'no comparisons'}`;
      return MathViz.record({ X: fin(range(k + 1).map(i => i + 1)), le: relFn(R, '≤') }, label);
    })), `all partial orders on ≤ ${n} points`));
  };
  const AllRelations = (n = 3) => {
    need(Number.isInteger(n) && n >= 1 && n <= 3, 'AllRelations(n) lists every relation on 1 to n points (n up to 3), up to isomorphism.');
    return cached('R' + n, () => fin(range(n).flatMap(k => upToIso(allRelations(k + 1), k + 1, relEnc)
      .sort((a, b) => pairs(a).length - pairs(b).length)
      .map(R => MathViz.record({ X: fin(range(k + 1).map(i => i + 1)), rel: relFn(R, 'R') },
        `${pairs(R).length ? '{' + pairs(R).map(([a, b]) => `(${a}, ${b})`).join(', ') + '}' : '∅'} on {${range(k + 1).map(i => i + 1).join(', ')}}`))), `all relations on ≤ ${n} points`));
  };

  /* ---------- binary operations on ≤ 3 elements (up to isomorphism) ---------- */
  function magmas(n) {
    const out = [];
    const total = Math.pow(n, n * n);
    for (let m = 0; m < total; m++) {
      const T = range(n).map(() => new Array(n)), digits = [];
      let v = m;
      for (let i = 0; i < n * n; i++) { digits.push(v % n); v = Math.floor(v / n); }
      for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) T[a][b] = digits[a * n + b];
      out.push(T);
    }
    // Relabelling by p: T'[p(a)][p(b)] = p(T[a][b]).
    return upToIso(out, n, (T, p) => { const S = range(n).map(() => new Array(n)); for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) S[p[a]][p[b]] = p[T[a][b]]; return S.map(r => r.join('')).join('/'); });
  }
  const AllMagmas = (n = 3) => {
    need(Number.isInteger(n) && n >= 1 && n <= 3, 'AllMagmas(n) lists every binary operation on 1 to n elements (n up to 3), up to isomorphism.');
    return cached('M' + n, () => fin(range(n).flatMap(k => magmas(k + 1).map(T => {
      const label = `[${T.map(r => r.join(' ')).join(' | ')}]`;
      return MathViz.record({ G: fin(range(k + 1)), op: tableOp(T, label) }, `operation ${label} on {${range(k + 1).join(', ')}}`);
    })), `all binary operations on ≤ ${n} elements`));
  };

  /* ---------- all maps {1, …, n} → {1, …, m} ---------- */
  const AllMaps = (n, m) => {
    need(Number.isInteger(n) && Number.isInteger(m) && n >= 1 && m >= 1 && Math.pow(m, n) <= 4096, 'AllMaps(n, m) lists every map {1, …, n} → {1, …, m} (at most 4096 of them).');
    return cached(`F${n},${m}`, () => {
      const out = [];
      for (let k = 0; k < Math.pow(m, n); k++) {
        const vals = [];
        let v = k;
        for (let i = 0; i < n; i++) { vals.push(v % m + 1); v = Math.floor(v / m); }
        const f = Object.assign(x => (Number.isInteger(x) && x >= 1 && x <= n ? vals[x - 1] : NaN), { label: '[' + vals.map((y, i) => `${i + 1}↦${y}`).join(', ') + ']', arity: 1 });
        out.push(f);
      }
      return fin(out, `all maps {1, …, ${n}} → {1, …, ${m}}`);
    });
  };

  MathViz.shared.allTopologies = AllTopologies;
  MathViz.shared.allGroups = AllGroups;

  MathViz.define({
    name: 'models',
    requires: ['algebra', 'topology'],
    description: 'Every small model, up to isomorphism: all groups of order ≤ 12, topologies on ≤ 4 points, partial orders on ≤ 4 points, relations on ≤ 3 points, binary operations on ≤ 3 elements, and all maps between small sets. Claims over them are checked for every model of that size, and the first counterexample is a smallest one.',
    constants: {
      S3: groups()[7], Q8: groups()[13], D4: groups()[12], A4: groups()[21], Klein: groups()[4],
      S4: cached('S4', () => sym(4)),
    },
    functions: {
      Cyclic: { doc: 'Cyclic(n): the cyclic group ℤ/n (written additively, elements 0, …, n − 1), as a group record.', fn: n => { need(Number.isInteger(n) && n >= 1 && n <= 60, 'Cyclic(n) needs 1 ≤ n ≤ 60.'); return n <= 12 ? groups().find(g => g.label === `ℤ/${n}`) : cached('C' + n, () => cyclic(n)); } },
      Dihedral: { doc: 'Dihedral(n): the symmetries of a regular n-gon (order 2n), elements rᵏ and rᵏs.', fn: n => { need(Number.isInteger(n) && n >= 2 && n <= 30, 'Dihedral(n) needs 2 ≤ n ≤ 30.'); return n === 4 ? groups()[12] : cached('D' + n, () => dihedral(n, `D${SUB(n)} (symmetries of a ${n}-gon)`)); } },
    },
    spaces: {
      AllGroups: { doc: 'AllGroups(n): every group of order ≤ n (n ≤ 12), one per isomorphism class: the cyclic groups, the Klein group, S₃, D₄, Q₈, ℤ/3 × ℤ/3, D₅, A₄, D₆, Dic₃ and the other products. Each is a record {G, op, e} whose elements have names (i, −k, (1 2 3), r²s).', fn: AllGroups },
      AllTopologies: { doc: 'AllTopologies(n): every topology on 1 to n points (n ≤ 4), up to homeomorphism: 1 + 3 + 9 + 33 of them. Each is a record {X, T}, so T0(S), connected_space(S), … apply.', fn: AllTopologies },
      AllPosets: { doc: 'AllPosets(n): every partial order on 1 to n points (n ≤ 4), up to isomorphism. Each is a record {X, le}.', fn: AllPosets },
      AllRelations: { doc: 'AllRelations(n): every binary relation on 1 to n points (n ≤ 3), up to isomorphism, fewest pairs first. Each is a record {X, rel}.', fn: AllRelations },
      AllMagmas: { doc: 'AllMagmas(n): every binary operation on 1 to n elements (n ≤ 3), up to isomorphism (3341 of them for n = 3). Each is a record {G, op}.', fn: AllMagmas },
      AllMaps: { doc: 'AllMaps(n, m): every map {1, …, n} → {1, …, m}.', fn: AllMaps },
    },
    views: {
      hasse: {
        doc: 'hasse(P) draws the Hasse diagram of a finite partial order P = {X, le}: each element above the ones it covers. Hover an element to see everything above and below it.',
        render(ctx, P) {
          need(P && P.fields && P.fields.X && typeof P.fields.le === 'function', 'hasse(P) needs a partial order, a record {X, le} such as one from AllPosets(4).');
          const X = MathViz.toDomain(P.fields.X).values, le = (a, b) => P.fields.le(a, b) === true;
          need(X.length <= 40, 'hasse draws partial orders with at most 40 elements.');
          const D = ctx.diagram({ layout: 'layered', hint: 'Hover an element to see what lies above and below it.' });
          X.forEach((x, i) => D.node(i, {
            label: MathViz.format(x),
            related: X.map((_, j) => j).filter(j => j !== i && (le(X[i], X[j]) || le(X[j], X[i]))),
            tip: `${MathViz.format(x)}: ${X.filter((y, j) => j !== i && le(x, y)).length} elements above, ${X.filter((y, j) => j !== i && le(y, x)).length} below`,
          }));
          // Covering pairs: a < b with nothing strictly between.
          X.forEach((a, i) => X.forEach((b, j) => {
            if (i === j || !le(a, b)) return;
            if (!X.some((c, k) => k !== i && k !== j && le(a, c) && le(c, b))) D.edge(i, j, { arrow: false });
          }));
          const min = X.filter((x, i) => !X.some((y, j) => j !== i && le(y, x))), max = X.filter((x, i) => !X.some((y, j) => j !== i && le(x, y)));
          ctx.note(`Minimal: ${min.map(MathViz.format).join(', ')}${min.length === 1 ? ' (the least element)' : ''}. Maximal: ${max.map(MathViz.format).join(', ')}${max.length === 1 ? ' (the greatest element)' : ''}.`);
        },
      },
      relation_graph: {
        doc: 'relation_graph(R) draws a relation R = {X, rel} on a finite set as arrows x → y when x R y, and says which of reflexive, symmetric, transitive and antisymmetric hold.',
        render(ctx, R) {
          need(R && R.fields && R.fields.X && typeof R.fields.rel === 'function', 'relation_graph(R) needs a relation, a record {X, rel} such as one from AllRelations(3).');
          const X = MathViz.toDomain(R.fields.X).values, r = (a, b) => R.fields.rel(a, b) === true, f = MathViz.format;
          const D = ctx.diagram({ layout: 'circle', height: 260 });
          X.forEach((x, i) => D.node(i, { label: f(x) }));
          X.forEach((a, i) => X.forEach((b, j) => { if (r(a, b)) D.edge(i, j, { color: i === j ? 'c2' : 'c1', width: 1.6 }); }));
          const findPair = test => { for (const a of X) for (const b of X) if (test(a, b)) return [a, b]; return null; };
          const refl = X.find(x => !r(x, x)), sym = findPair((a, b) => r(a, b) && !r(b, a)), anti = findPair((a, b) => a !== b && r(a, b) && r(b, a));
          let trans = null;
          for (const a of X) for (const b of X) for (const c of X) if (!trans && r(a, b) && r(b, c) && !r(a, c)) trans = [a, b, c];
          ctx.note([
            refl === undefined ? 'reflexive ✓' : `not reflexive (${f(refl)} is not related to itself)`,
            !sym ? 'symmetric ✓' : `not symmetric (${f(sym[0])} R ${f(sym[1])} but not back)`,
            !trans ? 'transitive ✓' : `not transitive (${f(trans[0])} R ${f(trans[1])} R ${f(trans[2])}, but not ${f(trans[0])} R ${f(trans[2])})`,
            !anti ? 'antisymmetric ✓' : `not antisymmetric (${f(anti[0])} and ${f(anti[1])} are related both ways)`,
          ].join(' · '));
          if (refl === undefined && !sym && !trans) {
            const classes = [];
            for (const x of X) if (!classes.some(c => c.includes(x))) classes.push(X.filter(y => r(x, y)));
            ctx.note(`An equivalence relation: its classes are ${classes.map(c => `{${c.map(f).join(', ')}}`).join(', ')}.`);
          }
        },
      },
      open_sets: {
        doc: 'open_sets(S) draws the open sets of a finite topological space S = {X, T}, ordered by inclusion.',
        render(ctx, S) {
          need(S && S.fields && S.fields.T, 'open_sets(S) needs a topological space, a record {X, T} such as one from AllTopologies(4).');
          const T = MathViz.toDomain(S.fields.T).values.map(U => MathViz.toDomain(U).values);
          const sub = (a, b) => a.every(x => b.some(y => MathViz.ops.eq(x, y)));
          const D = ctx.diagram({ layout: 'layered' });
          T.forEach((U, i) => D.node(i, { label: U.length ? `{${U.map(MathViz.format).join(', ')}}` : '∅', level: U.length }));
          T.forEach((a, i) => T.forEach((b, j) => {
            if (i === j || a.length >= b.length || !sub(a, b)) return;
            if (!T.some((c, k) => k !== i && k !== j && c.length > a.length && c.length < b.length && sub(a, c) && sub(c, b))) D.edge(i, j, { arrow: false });
          }));
          ctx.note(`${T.length} open sets, closed under unions and intersections: each is drawn above the open sets it contains.`);
        },
      },
    },
    notation: `
# A partial order: reflexive, antisymmetric and transitive.
structure PartialOrder(X: Set, le: Fun) where
  reflexive: forall x in X: le(x, x)
  antisymmetric: forall x, y in X: le(x, y) and le(y, x) -> x = y
  transitive: forall x, y, z in X: le(x, y) and le(y, z) -> le(x, z)

# The poset P has a greatest element.
# examples: P in AllPosets(3)
def has_greatest(P) := exists g in P.X: forall x in P.X: P.le(x, g)

# Any two elements of P are comparable.
# examples: P in AllPosets(3)
def total_order(P) := forall x, y in P.X: P.le(x, y) or P.le(y, x)

# Properties of a relation R on R.X.
# examples: R in AllRelations(2)
def reflexive_rel(R) := forall x in R.X: R.rel(x, x)
# examples: R in AllRelations(2)
def symmetric_rel(R) := forall x, y in R.X: R.rel(x, y) -> R.rel(y, x)
# examples: R in AllRelations(2)
def transitive_rel(R) := forall x, y, z in R.X: R.rel(x, y) and R.rel(y, z) -> R.rel(x, z)
# examples: R in AllRelations(2)
def antisymmetric_rel(R) := forall x, y in R.X: R.rel(x, y) and R.rel(y, x) -> x = y
# examples: R in AllRelations(2)
def equivalence_rel(R) := reflexive_rel(R) and symmetric_rel(R) and transitive_rel(R)

# f is injective on A; f maps A onto B.
def injective(f: Fun, A: Set) := forall x, y in A: f(x) = f(y) -> x = y
def surjective(f: Fun, A: Set, B: Set) := forall y in B: exists x in A: f(x) = y

# The group g is cyclic: some element's powers give everything.
# examples: g in AllGroups(8)
def cyclic_group(g) := exists x in g.G: order(x, g.op, g.e) = |g.G|

# Does symmetric and transitive give reflexive? ("x R y and y R x, so x R x.") The empty relation on one point says no.
conjecture symmetric_transitive_is_reflexive: forall R in AllRelations(3): symmetric_rel(R) and transitive_rel(R) -> reflexive_rel(R)

# Reflexivity, symmetry and transitivity are independent: each can fail while the other two hold.
lemma not_transitive_only: exists R in AllRelations(3): reflexive_rel(R) and symmetric_rel(R) and not transitive_rel(R)
lemma not_symmetric_only: exists R in AllRelations(3): reflexive_rel(R) and transitive_rel(R) and not symmetric_rel(R)
lemma not_reflexive_only: exists R in AllRelations(3): symmetric_rel(R) and transitive_rel(R) and not reflexive_rel(R)

# Does every finite partial order have a greatest element? Two incomparable points say no.
conjecture finite_poset_has_greatest: forall P in AllPosets(4): has_greatest(P)

# A finite partial order in which any two elements have an upper bound has a greatest element.
lemma directed_finite_has_greatest: forall P in AllPosets(4): (forall x, y in P.X: exists z in P.X: P.le(x, z) and P.le(y, z)) -> has_greatest(P)

# Is every group of order ≤ 8 abelian? S₃ (order 6) is the smallest that isn't.
conjecture small_groups_are_abelian: forall g in AllGroups(8): g in AbelianGroup

# Is every abelian group cyclic? The Klein group (order 4) is the smallest that isn't.
conjecture abelian_groups_are_cyclic: forall g in AllGroups(8): g in AbelianGroup -> cyclic_group(g)

# A group of prime order is cyclic.
lemma prime_order_cyclic: forall g in AllGroups(8): |g.G| in {2, 3, 5, 7} -> cyclic_group(g)

# If x·x = e for every x, the group is abelian.
lemma exponent_two_abelian_all: forall g in AllGroups(8): (forall x in g.G: g.op(x, x) = g.e) -> g in AbelianGroup

# Is every monoid commutative? The smallest that isn't has 3 elements.
conjecture monoids_are_commutative: forall m in AllMagmas(3): associative(m.op, m.G) and has_identity(m.op, m.G) -> commutative(m.op, m.G)

# T₀ doesn't give T₁: the Sierpiński space (2 points) is the smallest example.
conjecture T0_gives_T1: forall S in AllTopologies(4): T0(S) -> T1(S)

# A finite T₁ space is discrete.
lemma finite_T1_is_discrete: forall S in AllTopologies(4): T1(S) -> forall x in S.X: {x} in S.T

# On a finite set, a map to itself is injective exactly when it is surjective (the pigeonhole principle).
lemma pigeonhole: forall f in AllMaps(3, 3): injective(f, 1..3) <-> surjective(f, 1..3, 1..3)

# Between different sets, injective doesn't give surjective.
conjecture injective_is_surjective: forall f in AllMaps(2, 3): injective(f, 1..2) -> surjective(f, 1..2, 1..3)
`,
  });

  MathViz.selfCheck('small model counts', () => {
    const counts = [[() => AllGroups(8), 14], [() => AllGroups(12), 24], [() => AllTopologies(4), 1 + 3 + 9 + 33], [() => AllPosets(4), 1 + 2 + 5 + 16], [() => AllRelations(3), 2 + 10 + 104], [() => AllMagmas(3), 1 + 10 + 3330], [() => AllMaps(3, 3), 27]];
    return counts.map(([make, want]) => { const n = make().values.length; return { name: make().describe(), ok: n === want, detail: `${n} listed, ${want} known` }; });
  });
});
