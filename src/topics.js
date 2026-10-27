/* Theorem Sketchpad — finding library names by topic.

   MV.findTopic('uniform continuity') lists the functions, definitions, sets, views, lemmas and
   structures of every library (imported or not) whose name or documentation is about that topic,
   best first. Words match by their stems (continuity ~ continuous), and a small table of related
   words widens a topic (derivative → gradient, jacobian, partial…). The editor's autocomplete
   uses it, so typing "derivative" offers grad and jacobian. */
'use strict';
(function (global) {
const MV = global.MV;

// Words that belong to the same topic. A query word in a group also finds the others (weaker).
const GROUPS = [
  ['derivative', 'differentiable', 'differentiate', 'differentiation', 'gradient', 'grad', 'jacobian', 'hessian', 'partial', 'tangent', 'slope', 'linearize', 'directional'],
  ['continuous', 'continuity', 'epsilon', 'delta', 'lipschitz', 'uniformly', 'uniform'],
  ['limit', 'converge', 'convergent', 'convergence', 'tends', 'cauchy', 'sequence', 'subsequence'],
  ['integral', 'integrate', 'integrable', 'riemann', 'darboux', 'area', 'antiderivative'],
  ['series', 'sum', 'summable', 'partial sums', 'ratio', 'root'],
  ['compact', 'compactness', 'cover', 'subcover', 'heine', 'borel', 'bolzano', 'weierstrass', 'attains', 'maximum', 'minimum', 'extreme'],
  ['norm', 'metric', 'distance', 'ball', 'complete', 'banach'],
  ['open', 'closed', 'topology', 'topological', 'boundary', 'interior', 'closure', 'hausdorff', 'connected'],
  ['matrix', 'matrices', 'linear', 'eigenvalue', 'eigenvector', 'determinant', 'det', 'rank', 'kernel', 'image', 'span', 'basis', 'subspace'],
  ['group', 'subgroup', 'homomorphism', 'coset', 'quotient', 'normal', 'isomorphic', 'order', 'cyclic', 'symmetric'],
  ['ring', 'field', 'monoid', 'semigroup', 'magma'],
  ['probability', 'random', 'distribution', 'expectation', 'expected', 'variance', 'mean', 'chance', 'dice', 'coin'],
  ['curve', 'curvature', 'torsion', 'arc', 'frenet', 'surface', 'gauss'],
  ['differential equation', 'ode', 'dynamics', 'dynamical', 'phase', 'orbit', 'fixed point', 'iterate', 'equilibrium', 'stable', 'contraction'],
  ['prime', 'divisor', 'divides', 'gcd', 'modular', 'mod', 'congruence', 'totient'],
  ['complex', 'imaginary', 'conjugate', 'argument'],
  ['asymptotic', 'growth', 'threshold', 'eventually'],
  ['level set', 'level', 'regular value', 'contour'],
];
const SUFFIXES = ['ations', 'ation', 'ities', 'ity', 'ness', 'ible', 'able', 'ous', 'ive', 'ing', 'ies', 'ly', 'es', 'ed', 'y', 's'];
function stem(w) {
  w = w.toLowerCase();
  for (const s of SUFFIXES) if (w.endsWith(s) && w.length - s.length >= 4) return w.slice(0, -s.length);
  return w;
}
const tokens = text => (String(text || '').toLowerCase().match(/[\p{L}][\p{L}\p{N}]*/gu) || []);

let INDEX = null, INDEX_KEY = '';
function buildIndex() {
  const key = [...MV.REG.values()].map(l => l.name + ':' + Object.keys(l.docs || {}).length).join(',');
  if (INDEX && key === INDEX_KEY) return INDEX;
  const out = [];
  for (const lib of MV.REG.values()) {
    if (lib.error) continue;
    const docs = lib.docs || {}, d = lib.def || {}, seen = new Set();
    // The forms of a concept (prime_wilson, …) are found through the concept itself.
    for (const f of [...((lib.section && lib.section.forms) || []), ...((d.section && d.section.forms) || [])]) seen.add(f);
    const add = (name, kind, doc) => {
      if (seen.has(name) || name.startsWith('_')) return;
      seen.add(name);
      const text = doc || '';
      out.push({ name, lib: lib.name, kind, doc: text, nameParts: name.toLowerCase().split(/[_\d]+/).filter(Boolean),
        words: new Set(tokens(text).map(stem)), libWords: new Set(tokens(`${lib.name} ${lib.description || ''}`).map(stem)) });
    };
    for (const k of Object.keys(d.views || {})) add(k, 'view', d.views[k].doc);
    for (const k of Object.keys(d.functions || {})) add(k, 'function', docs[k]);
    for (const k of Object.keys(d.domains || {})) add(k, 'space', docs[k]);
    for (const k of Object.keys(d.constants || {})) add(k, 'constant', docs[k]);
    for (const l of lib.lemmas || []) add(l.name, l.kind || 'lemma', docs[l.name]);
    for (const st of lib.structures || []) add(st, 'structure', docs[st]);
    for (const k of lib.names || []) add(k, 'definition', docs[k]);
  }
  INDEX_KEY = key;
  return (INDEX = out);
}

// The words a query word stands for: itself (stemmed), then the rest of its topic group.
function expand(w) {
  const s = stem(w), related = new Set();
  for (const g of GROUPS) if (g.some(x => x.split(' ').some(p => stem(p) === s || (s.length >= 5 && stem(p).startsWith(s))))) {
    for (const x of g) if (!x.includes(' ') && stem(x) !== s) related.add(stem(x));   // phrases match, but their words don't widen
  }
  return { s, related: [...related] };
}

function scoreWord(e, w) {
  const { s, related } = expand(w);
  const name = e.name.toLowerCase();
  let best = 0;
  if (name === w) best = 10;
  else if (name.startsWith(w) && /^[_\d]?$/.test(name.charAt(w.length))) best = 7;
  else if (e.nameParts.some(p => stem(p) === s || (p.length >= 5 && s.startsWith(p)))) best = 6;
  else if (s.length >= 3 && name.includes(s)) best = 4;
  // A name that matches and whose documentation uses the very word ranks higher (opnorm before normal).
  if (best >= 4 && best < 7 && e.words.has(s)) best += 1;
  if (best < 3 && s.length >= 3 && [...e.words].some(x => x === s || (s.length >= 4 && x.startsWith(s)))) best = 3;
  if (best < 2.5 && related.some(r => e.nameParts.some(p => stem(p) === r))) best = 2.5;
  if (best < 1.5 && related.some(r => e.words.has(r))) best = 1.5;
  if (best < 0.5 && e.libWords.has(s)) best = 0.5;
  return best;
}

// Words that say little about the topic: they add to a match but aren't required.
const SOFT = new Set(['set', 'sets', 'function', 'functions', 'map', 'maps', 'the', 'of', 'a', 'an', 'in', 'on', 'is', 'for', 'and', 'to', 'with', 'by', 'number', 'numbers', 'point', 'points', 'theorem', 'lemma', 'definition', 'how', 'what', 'find']);

// Library entries about a topic: every word of the query (but the soft ones) must match something.
function findTopic(query, opts = {}) {
  let words = tokens(query).filter(w => w.length >= 2);
  if (words.every(w => SOFT.has(w))) words = words.filter(w => w.length >= 3);
  if (!words.length) return [];
  const out = [];
  for (const e of buildIndex()) {
    let total = 0, ok = true;
    for (const w of words) {
      const sc = scoreWord(e, w);
      if (!sc && !SOFT.has(w)) { ok = false; break; }
      total += SOFT.has(w) ? sc / 4 : sc;
    }
    if (!ok) continue;
    // Views and definitions explain a topic better than helpers; lemmas come after.
    total += e.kind === 'view' ? 0.4 : e.kind === 'definition' ? 0.3 : e.kind === 'lemma' || e.kind === 'conjecture' ? -1.5 : 0;
    out.push({ ...e, score: total });
  }
  out.sort((a, b) => b.score - a.score || a.name.length - b.name.length || a.name.localeCompare(b.name));
  return opts.limit ? out.slice(0, opts.limit) : out;
}

MV.findTopic = findTopic;
MV.topicStem = stem;
})(typeof window !== 'undefined' ? window : globalThis);
