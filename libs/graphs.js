MathVizLibrary(function graphs(MathViz) {
  const fmt = MathViz.format;
  const need = (ok, msg) => { if (!ok) throw MathViz.error(msg); };

  /* ---------- graphs: vertices 1 … n and a set of edges {u, v} ---------- */
  class Graph {
    constructor(n, edges, label) {
      this.n = n;
      const key = new Set(), E = [];
      for (const [a, b] of edges) {
        need(Number.isInteger(a) && Number.isInteger(b) && a >= 1 && b >= 1 && a <= n && b <= n, `Edges join vertices 1 … ${n}; got (${a}, ${b}).`);
        need(a !== b, `A simple graph has no loops; got (${a}, ${a}).`);
        const e = a < b ? [a, b] : [b, a], k = e.join(',');
        if (!key.has(k)) { key.add(k); E.push(e); }
      }
      E.sort((x, y) => x[0] - y[0] || x[1] - y[1]);
      this.E = E;
      this.adj = Array.from({ length: n + 1 }, () => new Set());
      for (const [a, b] of E) { this.adj[a].add(b); this.adj[b].add(a); }
      this.label = label || null;
    }
  }
  const isG = v => v instanceof Graph;
  const asG = (v, what = 'a graph') => { need(isG(v), `Expected ${what}, such as Graph(4, ((1, 2), (2, 3))) or cycle_graph(5).`); return v; };
  const V = G => Array.from({ length: G.n }, (_, i) => i + 1);
  // Short names for small graphs: Graph(4; 12 23 34) lists the edges by their ends.
const show = G => G.label || (G.n <= 9 ? `Graph(${G.n}; ${G.E.map(e => e.join('')).join(' ') || 'no edges'})` : `Graph(${G.n}, {${G.E.map(e => `{${e.join(', ')}}`).join(', ')}})`);
  const make = (n, edges, label) => new Graph(n, edges, label);

  const complete = n => { const E = []; for (let a = 1; a <= n; a++) for (let b = a + 1; b <= n; b++) E.push([a, b]); return make(n, E, `K${sub(n)}`); };
  const cycle = n => { need(n >= 3, 'A cycle needs at least 3 vertices.'); return make(n, V({ n }).map(i => [i, (i % n) + 1]), `C${sub(n)}`); };
  const path = n => make(n, V({ n }).slice(0, -1).map(i => [i, i + 1]), `P${sub(n)}`);
  const star = n => make(n + 1, V({ n }).map(i => [1, i + 1]), `star with ${n} leaves`);
  const bip = (m, n) => { const E = []; for (let a = 1; a <= m; a++) for (let b = 1; b <= n; b++) E.push([a, m + b]); return make(m + n, E, `K${sub(m)},${sub(n)}`); };
  const wheel = n => { const G = cycle(n); return make(n + 1, [...G.E, ...V(G).map(i => [i, n + 1])], `wheel W${sub(n)}`); };
  const petersen = () => make(10, [[1, 2], [2, 3], [3, 4], [4, 5], [5, 1], [1, 6], [2, 7], [3, 8], [4, 9], [5, 10], [6, 8], [8, 10], [10, 7], [7, 9], [9, 6]], 'the Petersen graph');
  const cube = d => {
    need(Number.isInteger(d) && d >= 1 && d <= 5, 'cube_graph(d) for d = 1 … 5.');
    const n = 2 ** d, E = [];
    for (let a = 0; a < n; a++) for (let k = 0; k < d; k++) { const b = a ^ (1 << k); if (a < b) E.push([a + 1, b + 1]); }
    return make(n, E, `the ${d}-cube Q${sub(d)}`);
  };
  function sub(n) { return String(n).split('').map(c => '₀₁₂₃₄₅₆₇₈₉'[+c] || c).join(''); }

  /* ---------- properties ---------- */
  const degree = (G, v) => { asG(G); return G.adj[v] ? G.adj[v].size : 0; };
  // Breadth-first distances from s (Infinity where unreachable).
  const bfs = (G, s) => {
    const d = new Array(G.n + 1).fill(Infinity);
    d[s] = 0;
    const q = [s];
    while (q.length) { const u = q.shift(); for (const w of G.adj[u]) if (d[w] === Infinity) { d[w] = d[u] + 1; q.push(w); } }
    return d;
  };
  const components = G => {
    const seen = new Set(), out = [];
    for (const v of V(G)) {
      if (seen.has(v)) continue;
      const d = bfs(G, v), comp = V(G).filter(u => d[u] < Infinity);
      comp.forEach(u => seen.add(u));
      out.push(comp);
    }
    return out;
  };
  const connected = G => asG(G).n <= 1 || components(G).length === 1;
  // A cycle exists when some component has as many edges as vertices or more.
  const hasCycle = G => { asG(G); return G.E.length > G.n - components(G).length; };
  // A proper 2-colouring by breadth-first search, or null.
  const twoColour = G => {
    const c = new Array(G.n + 1).fill(-1);
    for (const s of V(G)) {
      if (c[s] >= 0) continue;
      c[s] = 0;
      const q = [s];
      while (q.length) { const u = q.shift(); for (const w of G.adj[u]) { if (c[w] < 0) { c[w] = 1 - c[u]; q.push(w); } else if (c[w] === c[u]) return null; } }
    }
    return c;
  };
  // An odd cycle, found directly: an edge inside one BFS layer closes one.
  const oddCycle = G => {
    asG(G);
    for (const s of V(G)) { const d = bfs(G, s); for (const [a, b] of G.E) if (d[a] < Infinity && d[a] === d[b]) return true; }
    return false;
  };
  // A proper colouring with k colours by backtracking (vertices by decreasing degree), or null.
  const colouring = (G, k) => {
    const order = V(G).sort((a, b) => G.adj[b].size - G.adj[a].size), c = new Array(G.n + 1).fill(0);
    let steps = 0;
    const go = i => {
      if (i === order.length) return true;
      if (++steps > 2e5) throw MathViz.error('That colouring search is too long; try a smaller graph.');
      const v = order[i];
      for (let col = 1; col <= k; col++) {
        let ok = true;
        for (const w of G.adj[v]) if (c[w] === col) { ok = false; break; }
        if (!ok) continue;
        c[v] = col;
        if (go(i + 1)) return true;
        c[v] = 0;
      }
      return false;
    };
    return go(0) ? c : null;
  };
  const chromatic = G => { asG(G); if (!G.n) return 0; for (let k = 1; k <= G.n; k++) if (colouring(G, k)) return k; return G.n; };
  // Simple paths from u to v, counted by depth-first search (up to a cap).
  const numPaths = (G, u, v) => {
    asG(G);
    if (u === v) return 1;
    let count = 0;
    const seen = new Set([u]);
    const go = x => { for (const w of G.adj[x]) { if (w === v) { count++; continue; } if (!seen.has(w)) { seen.add(w); go(w); seen.delete(w); } if (count > 1e5) return; } };
    go(u);
    return count;
  };
  const removeEdge = (G, e) => { asG(G); const k = [Math.min(...e), Math.max(...e)].join(','); return make(G.n, G.E.filter(x => x.join(',') !== k)); };
  const addEdge = (G, e) => make(asG(G).n, [...G.E, e]);
  const complementG = G => { asG(G); const E = []; for (let a = 1; a <= G.n; a++) for (let b = a + 1; b <= G.n; b++) if (!G.adj[a].has(b)) E.push([a, b]); return make(G.n, E, G.label ? `complement of ${G.label}` : null); };
  const adjacency = G => { asG(G); return V(G).map(a => V(G).map(b => (G.adj[a].has(b) ? 1 : 0))); };
  const laplacian = G => { asG(G); return V(G).map(a => V(G).map(b => (a === b ? G.adj[a].size : G.adj[a].has(b) ? -1 : 0))); };
  // Eigenvalues of a symmetric matrix by Jacobi rotations, sorted.
  const symEig = A => {
    const n = A.length, M = A.map(r => r.slice());
    for (let sweep = 0; sweep < 100; sweep++) {
      let off = 0;
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) off += M[i][j] ** 2;
      if (off < 1e-22) break;
      for (let p = 0; p < n; p++) for (let q = p + 1; q < n; q++) {
        if (Math.abs(M[p][q]) < 1e-15) continue;
        const th = (M[q][q] - M[p][p]) / (2 * M[p][q]), t = Math.sign(th || 1) / (Math.abs(th) + Math.sqrt(th * th + 1)), c = 1 / Math.sqrt(t * t + 1), s = t * c;
        for (let k = 0; k < n; k++) { const a = M[k][p], b = M[k][q]; M[k][p] = c * a - s * b; M[k][q] = s * a + c * b; }
        for (let k = 0; k < n; k++) { const a = M[p][k], b = M[q][k]; M[p][k] = c * a - s * b; M[q][k] = s * a + c * b; }
      }
    }
    return M.map((r, i) => (Math.abs(r[i]) < 1e-10 ? 0 : r[i])).sort((a, b) => a - b);
  };
  const algConn = G => { asG(G); need(G.n >= 2, 'The algebraic connectivity needs at least 2 vertices.'); MathViz.markInexact(); return symEig(laplacian(G))[1]; };
  // An Euler circuit (every edge once, back to the start) by Hierholzer's algorithm, or null.
  const eulerCircuit = G => {
    asG(G);
    if (!G.E.length) return [];
    if (V(G).some(v => G.adj[v].size % 2)) return null;
    const used = new Set(), adj = V({ n: G.n + 1 }).map(() => []);
    G.E.forEach(([a, b], i) => { adj[a].push([b, i]); adj[b].push([a, i]); });
    const stack = [G.E[0][0]], out = [];
    while (stack.length) {
      const v = stack[stack.length - 1];
      while (adj[v].length && used.has(adj[v][adj[v].length - 1][1])) adj[v].pop();
      if (!adj[v].length) out.push(stack.pop());
      else { const [w, i] = adj[v].pop(); used.add(i); stack.push(w); }
    }
    return used.size === G.E.length ? out : null;
  };
  const edgesConnected = G => { const live = V(G).filter(v => G.adj[v].size); if (!live.length) return true; const d = bfs(G, live[0]); return live.every(v => d[v] < Infinity); };
  const hamiltonian = G => {
    asG(G);
    need(G.n <= 11, 'hamiltonian(G) searches every ordering; it is limited to 11 vertices.');
    if (G.n < 3) return false;
    const seen = new Set([1]);
    const go = (v, k) => {
      if (k === G.n) return G.adj[v].has(1);
      for (const w of G.adj[v]) if (!seen.has(w)) { seen.add(w); if (go(w, k + 1)) return true; seen.delete(w); }
      return false;
    };
    return go(1, 1);
  };

  /* ---------- examples ---------- */
  let CAT = null;
  const catalog = () => CAT || (CAT = MathViz.finite([path(4), cycle(5), complete(4), star(4), bip(2, 3), cube(3), petersen(), wheel(5), make(6, [[1, 2], [2, 3], [3, 1], [4, 5], [5, 6]], 'two components'), make(5, [[1, 2], [2, 3], [2, 4], [4, 5]], 'a tree')], { label: 'example graphs' }));
  // Every graph on n labelled vertices (n ≤ 4: 64 of them on 4 vertices), for checks that try them all.
  const small = new Map();
  const allGraphs = n => {
    need(Number.isInteger(n) && n >= 1 && n <= 4, 'SmallGraphs(n) has every graph on n = 1 … 4 vertices.');
    if (small.has(n)) return small.get(n);
    const pairs = [];
    for (let a = 1; a <= n; a++) for (let b = a + 1; b <= n; b++) pairs.push([a, b]);
    const list = [];
    for (let m = 0; m < 2 ** pairs.length; m++) list.push(make(n, pairs.filter((_, i) => m & (1 << i))));
    const S = MathViz.finite(list, { label: `all ${list.length} graphs on ${n} vertices` });
    small.set(n, S);
    return S;
  };

  /* ---------- drawing ---------- */
  // Positions: a circle, relaxed by a few hundred steps of a spring model (deterministic).
  const layouts = new WeakMap();
  const layout = G => {
    if (layouts.has(G)) return layouts.get(G);
    const n = G.n;
    let P = V(G).map(i => [Math.cos(2 * Math.PI * (i - 1) / n + 0.3), Math.sin(2 * Math.PI * (i - 1) / n + 0.3)]);
    if (G.label === 'the Petersen graph') P = V(G).map(i => { const r = i <= 5 ? 1 : 0.5, k = (i - 1) % 5; return [r * Math.cos(Math.PI / 2 + 2 * Math.PI * k / 5), r * Math.sin(Math.PI / 2 + 2 * Math.PI * k / 5)]; });
    else if (!/^C|^K|^wheel|^star/.test(G.label || '') && n > 3) {
      const k = 1 / Math.sqrt(n);
      for (let it = 0; it < 300; it++) {
        const F = P.map(() => [0, 0]), t = 0.1 * (1 - it / 300);
        for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) if (a !== b) {
          const dx = P[a][0] - P[b][0], dy = P[a][1] - P[b][1], d = Math.max(1e-3, Math.hypot(dx, dy));
          const f = k * k / d - (G.adj[a + 1].has(b + 1) ? d * d / k : 0);
          F[a][0] += f * dx / d; F[a][1] += f * dy / d;
        }
        P = P.map((p, a) => { const l = Math.hypot(...F[a]) || 1; return [p[0] + F[a][0] / l * Math.min(t, l), p[1] + F[a][1] / l * Math.min(t, l)]; });
      }
      const xs = P.map(p => p[0]), ys = P.map(p => p[1]), cx = (Math.max(...xs) + Math.min(...xs)) / 2, cy = (Math.max(...ys) + Math.min(...ys)) / 2;
      const s = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)) / 2 || 1;
      P = P.map(([x, y]) => [(x - cx) / s, (y - cy) / s]);
    }
    layouts.set(G, P);
    return P;
  };
  const PALETTE = ['c1', 'c2', 'c3', 'c4', 'c5', 'ink'];
  function drawGraph(ctx, G, o = {}) {
    const P = layout(G);
    const fig = ctx.figure({ x: [-1.35, 1.35], y: [-1.25, 1.25], square: true, xAxis: false, yAxis: false, height: o.height || 280 });
    for (const [a, b] of G.E) {
      const hl = o.edges && o.edges.has([a, b].join(','));
      fig.seg(P[a - 1][0], P[a - 1][1], P[b - 1][0], P[b - 1][1], { color: hl ? 'c2' : 'faint', width: hl ? 3 : 1.6 });
    }
    V(G).forEach(v => {
      const col = o.colours ? PALETTE[(o.colours[v] - 1) % PALETTE.length] : 'c1';
      fig.points([P[v - 1]], { color: col, r: 7 });
      fig.text(P[v - 1][0], P[v - 1][1], String(v), { color: 'ink', align: 'left', dx: 9, dy: -9 });
    });
    return fig;
  }

  MathViz.thumbnail(isG, (fig, G) => {
    const P = layout(G), f = fig({ x: [-1.3, 1.3], y: [-1.3, 1.3], square: true, height: 110 });
    for (const [a, b] of G.E) f.seg(P[a - 1][0], P[a - 1][1], P[b - 1][0], P[b - 1][1], { color: 'faint', width: 1.4 });
    f.points(P, { color: 'c1', r: 3.5 });
  });
  MathViz.represent({
    name: 'graph_drawing', label: 'A drawing: points and lines', test: isG,
    doc: 'The vertices as points and the edges as lines between them. The same graph can be drawn in many ways; what matters is only which pairs are joined.',
    render(ctx, G) {
      drawGraph(ctx, G);
      const degs = V(G).map(v => G.adj[v].size);
      ctx.note(`${G.n} vertices, ${G.E.length} edges; degrees ${degs.join(', ')} (they add up to 2·${G.E.length} = ${2 * G.E.length}). ${connected(G) ? 'Connected' : `${components(G).length} components`}${hasCycle(G) ? '' : ', no cycles'}.`);
    },
  });
  MathViz.represent({
    name: 'graph_matrix', label: 'Its adjacency matrix', test: G => isG(G) && G.n <= 16,
    doc: 'A[u][v] = 1 when u and v are joined: a symmetric 0–1 matrix with zero diagonal. The (u, v) entry of Aᵏ counts the walks of length k from u to v.',
    render(ctx, G) {
      const A = adjacency(G);
      ctx.table(['', ...V(G).map(String)], A.map((r, i) => [String(i + 1), ...r.map(x => (x ? '1' : '·'))]));
      const A2 = A.map(r => A[0].map((_, j) => r.reduce((s, x, k) => s + x * A[k][j], 0)));
      ctx.note(`The diagonal of A² is the degree sequence (${A2.map((r, i) => r[i]).join(', ')}): a walk of length 2 from v back to v goes out along one edge and back.`);
    },
  });
  MathViz.represent({
    name: 'graph_lists', label: 'Adjacency lists', test: isG,
    doc: 'For each vertex, its neighbours: how a computer usually stores a graph.',
    render(ctx, G) { ctx.table(['vertex', 'neighbours', 'degree'], V(G).map(v => [String(v), [...G.adj[v]].sort((a, b) => a - b).join(', ') || '—', String(G.adj[v].size)])); },
  });
  MathViz.represent({
    name: 'graph_spectrum', label: 'Its spectrum: the eigenvalues of A and of the Laplacian', test: G => isG(G) && G.n <= 30,
    doc: 'The eigenvalues of the adjacency matrix A and of the Laplacian L = D − A. 0 is an eigenvalue of L once for each component; A\'s spectrum is symmetric about 0 exactly when the graph is bipartite.',
    render(ctx, G) {
      const ea = symEig(adjacency(G)), el = symEig(laplacian(G)), sh = x => fmt(+x.toFixed(4));
      const fig = ctx.figure({ height: 120, y: [-0.5, 1.5], yAxis: false, xlabel: 'eigenvalue' });
      fig.points(ea.map(x => [x, 1]), { color: 'c1', r: 5 }); fig.points(el.map(x => [x, 0]), { color: 'c2', r: 5 });
      fig.text(Math.min(...ea, ...el), 1.3, 'A', { color: 'c1' }); fig.text(Math.min(...ea, ...el), 0.3, 'L = D − A', { color: 'c2' });
      const zeros = el.filter(x => Math.abs(x) < 1e-8).length, sym = ea.every(x => ea.some(y => Math.abs(x + y) < 1e-6));
      ctx.table(['', 'eigenvalues'], [['A', ea.map(sh).join(', ')], ['L', el.map(sh).join(', ')]]);
      ctx.note(`0 is an eigenvalue of L ${zeros} time${zeros === 1 ? '' : 's'}: ${zeros} component${zeros === 1 ? '' : 's'}. A's spectrum ${sym ? 'is' : 'is not'} symmetric about 0: the graph ${sym ? 'is' : 'is not'} bipartite.${G.n >= 2 ? ` The second smallest eigenvalue of L (the algebraic connectivity) is ${sh(el[1])}.` : ''}`);
    },
  });

  MathViz.define({
    name: 'graphs',
    requires: ['linalg'],
    description: 'Finite simple graphs: building them (Graph(n, edges), complete, cycle, path, star, bipartite, wheel, cube and Petersen graphs), every graph on up to 4 vertices to check statements exhaustively, degrees, components, cycles, distances, colourings and the chromatic number, Euler circuits and Hamiltonian cycles, adjacency and Laplacian matrices and their eigenvalues; trees, bipartite, connected and Eulerian graphs each defined several ways, and views of colourings, breadth-first search and Euler circuits.',
    types: [{ name: 'graph', test: isG, ops: { '=': (a, b) => isG(a) && isG(b) && a.n === b.n && a.E.length === b.E.length && a.E.every((e, i) => e[0] === b.E[i][0] && e[1] === b.E[i][1]), format: show } }],
    functions: {
      Graph: { doc: 'Graph(n, edges): the graph on the vertices 1 … n with the given edges, as in Graph(4, ((1, 2), (2, 3), (3, 4))).', fn: (n, edges = []) => { need(Number.isInteger(n) && n >= 0 && n <= 200, 'Graph(n, edges) needs a number of vertices n = 0 … 200.'); const list = Array.isArray(edges) ? edges : edges && edges.__domain && edges.values ? edges.values : null; need(list, 'The edges are a list of pairs, as in ((1, 2), (2, 3)).'); return make(n, list); } },
      complete_graph: { doc: 'complete_graph(n): Kₙ, every pair of the n vertices joined.', fn: complete },
      cycle_graph: { doc: 'cycle_graph(n): Cₙ, the vertices in a ring.', fn: cycle },
      path_graph: { doc: 'path_graph(n): Pₙ, the vertices in a row.', fn: path },
      star_graph: { doc: 'star_graph(n): a centre joined to n leaves.', fn: star },
      complete_bipartite: { doc: 'complete_bipartite(m, n): K_{m,n}, every one of m vertices joined to every one of n others.', fn: bip },
      wheel_graph: { doc: 'wheel_graph(n): a cycle of n vertices and a hub joined to all of them.', fn: wheel },
      cube_graph: { doc: 'cube_graph(d): the d-dimensional cube: vertices are 0–1 strings of length d, joined when they differ in one place.', fn: cube },
      petersen_graph: { doc: 'petersen_graph(): the Petersen graph, the counterexample to many conjectures: 10 vertices, every degree 3, no cycle shorter than 5.', fn: petersen },
      vertices: { doc: 'vertices(G): the list 1, …, n.', fn: G => V(asG(G)) },
      edges: { doc: 'edges(G): the list of edges, each a pair (u, v) with u < v.', fn: G => asG(G).E.map(e => e.slice()) },
      nvertices: { doc: 'nvertices(G): the number of vertices.', fn: G => asG(G).n },
      nedges: { doc: 'nedges(G): the number of edges.', fn: G => asG(G).E.length },
      degree: { doc: 'degree(G, v): the number of edges at v.', fn: degree },
      neighbours: { doc: 'neighbours(G, v): the vertices joined to v.', fn: (G, v) => [...asG(G).adj[v]].sort((a, b) => a - b) },
      adjacent: { doc: 'adjacent(G, u, v): whether u and v are joined by an edge.', fn: (G, u, v) => asG(G).adj[u].has(v) },
      connected: { doc: 'connected(G): whether every vertex can be reached from every other one (by breadth-first search).', fn: connected },
      components: { doc: 'components(G): the connected components, each a list of vertices.', fn: G => components(asG(G)) },
      has_cycle: { doc: 'has_cycle(G): whether G contains a cycle (some component has at least as many edges as vertices).', fn: hasCycle },
      graph_distance: { doc: 'graph_distance(G, u, v): the least number of edges on a path from u to v (inf when there is none).', fn: (G, u, v) => bfs(asG(G), u)[v] },
      num_paths: { doc: 'num_paths(G, u, v): the number of simple paths from u to v (1 when u = v).', fn: numPaths },
      colorable: { doc: 'colorable(G, k): whether the vertices can be coloured with k colours so that joined vertices differ.', fn: (G, k) => !!colouring(asG(G), k) },
      chromatic_number: { doc: 'chromatic_number(G): the least number of colours for a proper colouring (by backtracking; fine up to about 15 vertices).', fn: chromatic },
      has_odd_cycle: { doc: 'has_odd_cycle(G): whether G has a cycle of odd length (an edge inside one layer of a breadth-first search closes one).', fn: oddCycle },
      euler_circuit: { doc: 'euler_circuit(G): a closed walk using every edge exactly once, as a list of vertices (Hierholzer\'s algorithm), or undefined when there is none.', fn: G => { const c = eulerCircuit(asG(G)); return c && edgesConnected(G) ? c : undefined; } },
      has_euler_circuit: { doc: 'has_euler_circuit(G): whether a closed walk uses every edge exactly once (searched for, not read off the degrees).', fn: G => { const c = eulerCircuit(asG(G)); return !!c && edgesConnected(G); } },
      edges_connected: { doc: 'edges_connected(G): whether all the edges lie in one component (isolated vertices are ignored).', fn: G => edgesConnected(asG(G)) },
      hamiltonian: { doc: 'hamiltonian(G): whether a cycle passes through every vertex exactly once (searched; up to 11 vertices).', fn: hamiltonian },
      adjacency: { doc: 'adjacency(G): the adjacency matrix, A[u][v] = 1 when u and v are joined.', fn: adjacency },
      laplacian_matrix: { doc: 'laplacian_matrix(G): L = D − A, the degrees on the diagonal and −1 for each edge.', fn: laplacian },
      algebraic_connectivity: { doc: 'algebraic_connectivity(G): the second smallest eigenvalue of the Laplacian; positive exactly when G is connected (Fiedler).', fn: algConn },
      remove_edge: { doc: 'remove_edge(G, e): G without the edge e = (u, v).', fn: removeEdge },
      add_edge: { doc: 'add_edge(G, e): G with the edge e = (u, v) added.', fn: addEdge },
      complement_graph: { doc: 'complement_graph(G): the graph joining exactly the pairs G doesn\'t.', fn: complementG },
      max_degree: { doc: 'max_degree(G): the largest degree Δ(G).', fn: G => Math.max(0, ...V(asG(G)).map(v => G.adj[v].size)) },
      degree_sequence: { doc: 'degree_sequence(G): the degrees, largest first.', fn: G => V(asG(G)).map(v => G.adj[v].size).sort((a, b) => b - a) },
    },
    spaces: {
      Graphs: { doc: 'Graphs: example graphs: a path, a 5-cycle, K₄, a star, K₂,₃, the cube, the Petersen graph, a wheel, a graph in two pieces and a tree.', fn: catalog },
      SmallGraphs: { doc: 'SmallGraphs(n): every graph on the vertices 1 … n (n ≤ 4; 64 graphs on 4 vertices), so a statement about them is checked in every case.', fn: allGraphs },
    },
    views: {
      coloring: {
        doc: 'coloring(G) colours the vertices with as few colours as possible so that joined vertices differ, and says why fewer colours can\'t work when that is easy to see (an odd cycle, a clique).',
        render(ctx, G) {
          asG(G);
          const k = chromatic(G), c = colouring(G, k);
          drawGraph(ctx, G, { colours: c });
          ctx.status('info', `χ(G) = ${k}`);
          ctx.note(k <= 2 ? (k === 2 ? 'Two colours: the graph is bipartite, so it has no odd cycle.' : 'One colour: no edges.') : `${k} colours, and no proper colouring with ${k - 1} exists (every way was tried).${oddCycle(G) && k === 3 ? ' Two can\'t work because of an odd cycle.' : ''}`);
        },
      },
      bfs_layers: {
        doc: 'bfs_layers(G, s) draws G with the vertices coloured by their distance from s, and the edges of a breadth-first search tree: each vertex is reached by a shortest path.',
        render(ctx, G, s = 1) {
          asG(G);
          const d = bfs(G, s), tree = new Set();
          for (const v of V(G)) if (v !== s && d[v] < Infinity) { const p = [...G.adj[v]].find(w => d[w] === d[v] - 1); tree.add([Math.min(p, v), Math.max(p, v)].join(',')); }
          drawGraph(ctx, G, { colours: V({ n: G.n + 1 }).map(v => (d[v - 1] === Infinity ? 6 : d[v - 1] + 1)).slice(0), edges: tree });
          ctx.table(['distance', 'vertices'], [...new Set(V(G).map(v => d[v]))].sort((a, b) => a - b).map(k => [k === Infinity ? 'unreachable' : String(k), V(G).filter(v => d[v] === k).join(', ')]));
        },
      },
      euler: {
        doc: 'euler(G) draws an Euler circuit when there is one, numbering the edges in the order it uses them; otherwise it marks the vertices of odd degree that rule one out (Euler\'s theorem).',
        render(ctx, G) {
          asG(G);
          const c = eulerCircuit(G);
          if (!c || !edgesConnected(G)) {
            const odd = V(G).filter(v => G.adj[v].size % 2);
            drawGraph(ctx, G, { colours: V({ n: G.n + 1 }).map(v => (odd.includes(v) ? 2 : 1)) });
            ctx.status('fail', odd.length ? `No Euler circuit: ${odd.length} vertices of odd degree` : 'No Euler circuit: the edges are in several pieces');
            ctx.note(odd.length ? `A closed walk enters and leaves each vertex equally often, so every degree must be even; ${odd.join(', ')} ${odd.length === 1 ? 'has' : 'have'} odd degree.` : 'Every degree is even, but no single walk can reach all the edges.');
            return;
          }
          const P = layout(G), fig = drawGraph(ctx, G);
          for (let i = 0; i + 1 < c.length; i++) { const a = P[c[i] - 1], b = P[c[i + 1] - 1]; fig.text((a[0] + b[0]) / 2, (a[1] + b[1]) / 2, String(i + 1), { color: 'c2', align: 'center' }); }
          ctx.status('ok', 'An Euler circuit');
          ctx.note(`${c.join(' → ')}: every edge once. It exists because the edges are connected and every degree is even (Euler, 1736).`);
        },
      },
    },
    notation: `
# G is a tree, five ways: connected without cycles; connected with n − 1 edges; without cycles and with n − 1 edges; exactly one path between any two vertices; connected, but removing any edge disconnects it.
# examples: G in SmallGraphs(4)
concept tree(G) where
  connected_acyclic: connected(G) and not has_cycle(G)
  connected_edges: connected(G) and nedges(G) = nvertices(G) - 1
  acyclic_edges: not has_cycle(G) and nedges(G) = nvertices(G) - 1
  unique_paths: forall u, v in vertices(G): num_paths(G, u, v) = 1
  minimally_connected: connected(G) and forall e in edges(G): not connected(remove_edge(G, e))

# G is bipartite, three ways: two colours are enough; it has no odd cycle; the eigenvalues of its adjacency matrix are symmetric about 0.
# examples: G in SmallGraphs(4)
concept bipartite(G) where
  two_colours: colorable(G, 2)
  no_odd_cycle: not has_odd_cycle(G)
  spectrum: forall l in sym_eigenvalues(adjacency(G)): exists m in sym_eigenvalues(adjacency(G)): |l + m| < 1e-6

# G is connected, four ways: a search from one vertex reaches all; any two vertices are at finite distance; the Laplacian's second eigenvalue is positive; (I + A)ⁿ⁻¹ has no zero entry.
# examples: G in SmallGraphs(4)
concept connected_graph(G) where
  search: connected(G)
  distances: forall u, v in vertices(G): graph_distance(G, u, v) < inf
  laplacian: algebraic_connectivity(G) > 1e-9
  walks: forall row in (identity(nvertices(G)) + adjacency(G))^(nvertices(G) - 1): forall x in row: x > 0

# G has an Euler circuit, two ways: Euler's theorem (the edges are connected and every degree is even), or a circuit found by search.
# examples: G in SmallGraphs(4)
concept eulerian(G) where
  degrees: edges_connected(G) and forall v in vertices(G): degree(G, v) mod 2 = 0
  circuit: has_euler_circuit(G)

# The degrees add up to twice the number of edges (each edge has two ends).
lemma handshake: forall G in Graphs: sum v in vertices(G): degree(G, v) = 2*nedges(G)

# A graph or its complement is connected.
lemma complement_connected: forall G in SmallGraphs(4): connected(G) or connected(complement_graph(G))

# Trees are bipartite.
lemma trees_bipartite: forall G in SmallGraphs(4): tree(G) -> bipartite(G)

# A graph with maximal degree d can be coloured with d + 1 colours (greedily).
lemma greedy_colouring: forall G in Graphs: chromatic_number(G) <= max_degree(G) + 1

# Every graph with n ≥ 3 vertices whose degrees are all ≥ n/2 has a Hamiltonian cycle (Dirac).
lemma dirac: forall G in SmallGraphs(4): (forall v in vertices(G): degree(G, v) >= 2) -> hamiltonian(G)

# Every graph is 4-colourable? Not without planarity: K₅ needs 5 colours.
conjecture four_colours: forall n in 1..6: chromatic_number(complete_graph(n)) <= 4
`,
  });
});
