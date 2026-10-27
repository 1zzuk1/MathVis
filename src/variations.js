/* Theorem Sketchpad — variations: is every condition of a claim or definition needed?

   A variation changes one thing: drops a hypothesis, flips < and ≤, swaps the order of a ∀ and
   the ∃ after it, closes or opens the end of a range, or widens a range. Checking the variations
   shows which conditions the statement depends on, with the simplest counterexample for each.
   Sharpness finds the critical value of a constant in a comparison. */
'use strict';
(function (global) {
const MV = global.MV;
const { ppText, freeNames, binderNames } = MV;

/* ---------- small AST helpers ---------- */

// A copy of root with the node `target` (compared by identity) replaced.
function replaceNode(root, target, replacement) {
  if (root === target) return replacement;
  if (!root || typeof root !== 'object' || root.type === 'value') return root;
  if (Array.isArray(root)) { let changed = false; const out = root.map(x => { const y = replaceNode(x, target, replacement); if (y !== x) changed = true; return y; }); return changed ? out : root; }
  let out = null;
  for (const [k, v] of Object.entries(root)) {
    if (!v || typeof v !== 'object') continue;
    const y = replaceNode(v, target, replacement);
    if (y !== v) { out = out || { ...root }; out[k] = y; }
  }
  return out || root;
}

function walk(node, fn, parent = null) {
  if (!node || typeof node !== 'object' || node.type === 'value') return;
  if (Array.isArray(node)) { node.forEach(x => walk(x, fn, parent)); return; }
  if (node.type) fn(node, parent);
  for (const [k, v] of Object.entries(node)) if (k !== 'type' && v && typeof v === 'object') walk(v, fn, node);
}

const conjuncts = n => n.type === 'bin' && n.op === 'and' ? [...conjuncts(n.a), ...conjuncts(n.b)] : [n];
const andAll = parts => parts.reduce((a, b) => ({ type: 'bin', op: 'and', a, b }));
const FLIP = { '<': '<=', '<=': '<', '>': '>=', '>=': '>' };
const num = n => n.type === 'num' ? n.v : (n.type === 'un' && n.op === 'neg' && n.a.type === 'num') ? -n.a.v : null;
const lit = v => v < 0 ? { type: 'un', op: 'neg', a: { type: 'num', v: -v } } : { type: 'num', v };
const fmtLit = v => MV.fmtNum(+v.toPrecision(6));

/* All variations of a formula. `top` holds the leading ∀ binders of a claim (whose ranges may be
   widened); `node` is the rest. Returns [{ kind, label, node }] with node a full formula. */
function variationsOf(top, node) {
  const out = [];
  const rebuild = (binders, body) => binders.length ? { type: 'quant', q: 'forall', binders, body } : body;
  const add = (kind, label, binders, body) => out.push({ kind, label, node: rebuild(binders, body) });

  // 1. Hypotheses: drop each part, or all of them.
  if (node.type === 'bin' && node.op === '->') {
    const parts = conjuncts(node.a);
    if (parts.length > 1) parts.forEach((h, i) => add('hypothesis', `without “${ppText(h)}”`, top, { ...node, a: andAll(parts.filter((_, j) => j !== i)) }));
    add('hypothesis', parts.length > 1 ? 'without any hypothesis' : `without the hypothesis “${ppText(node.a)}”`, top, node.b);
  }
  // Conjunctions in a definition's body: drop each part.
  if (!top.length && node.type === 'bin' && node.op === 'and') {
    const parts = conjuncts(node);
    parts.forEach((h, i) => add('condition', `without “${ppText(h)}”`, top, andAll(parts.filter((_, j) => j !== i))));
  }

  // 2. Quantifier order: ∀a … ∃b becomes ∃b … ∀a (and the reverse), when neither range mentions the other.
  walk(node, n => {
    if (n.type !== 'quant' || n.body.type !== 'quant' || n.body.q === n.q) return;
    const inner = n.body;
    const outerNames = n.binders.flatMap(binderNames), innerNames = inner.binders.flatMap(binderNames);
    const mentions = (bs, names) => bs.some(b => { const used = freeNames(b.dom.type === 'bound' ? b.dom.c : b.dom); return names.some(x => used.has(x)); });
    if (mentions(inner.binders, outerNames) || mentions(n.binders, innerNames)) return;
    const swapped = { ...inner, body: { ...n, body: inner.body } };
    const sym = q => q === 'forall' ? '∀' : '∃';
    add('order', `${sym(inner.q)}${innerNames.join(', ')} before ${sym(n.q)}${outerNames.join(', ')}`, top, replaceNode(node, n, swapped));
  });

  // 3. Strict and non-strict comparisons.
  walk(node, n => {
    if (n.type !== 'cmp') return;
    n.ops.forEach((op, i) => {
      if (!FLIP[op]) return;
      const ops = n.ops.slice(); ops[i] = FLIP[op];
      const changed = { ...n, ops };
      add('comparison', `“${ppText(changed)}” instead of “${ppText(n)}”`, top, replaceNode(node, n, changed));
    });
  });

  // 4. Ranges of quantified variables: close or open an end; widen the leading ranges.
  const rangeVariants = (b, replaceIn) => {
    const d = b.dom;
    if (d.type !== 'interval') return;
    const name = b.pattern ? `(${b.pattern.join(', ')})` : b.name;
    const ppD = x => (x.loOpen ? '(' : '[') + ppText(x.lo) + ', ' + ppText(x.hi) + (x.hiOpen ? ')' : ']');
    for (const end of ['lo', 'hi']) {
      const key = end === 'lo' ? 'loOpen' : 'hiOpen';
      const nd = { ...d, [key]: !d[key] };
      replaceIn(nd, `${name} ∈ ${ppD(nd)} instead of ${ppD(d)}`);
    }
  };
  walk(node, n => {
    if (n.type !== 'quant') return;
    n.binders.forEach((b, i) => rangeVariants(b, (nd, label) => {
      const binders = n.binders.map((x, j) => j === i || x.dom === b.dom ? { ...x, dom: nd } : x);
      add('range', label, top, replaceNode(node, n, { ...n, binders }));
    }));
  });
  top.forEach((b, i) => {
    // Opening an end only weakens a claim; closing one strengthens it, which is worth checking.
    rangeVariants(b, (nd, label) => { if ((nd.loOpen && !b.dom.loOpen) || (nd.hiOpen && !b.dom.hiOpen)) return; add('range', label, top.map((x, j) => j === i || x.dom === b.dom ? { ...x, dom: nd } : x), node); });
    const d = b.dom;
    const lo = d.type === 'interval' || d.type === 'range' ? num(d.lo) : null, hi = d.type === 'interval' || d.type === 'range' ? num(d.hi) : null;
    if (lo !== null && hi !== null && hi > lo) {
      const w = d.type === 'range' ? Math.max(1, Math.round((hi - lo) / 2)) : (hi - lo) / 2;
      const nd = { ...d, lo: lit(lo - w), hi: lit(hi + w) };
      const name = b.pattern ? `(${b.pattern.join(', ')})` : b.name;
      if (!top.slice(0, i).some(x => x.dom === b.dom)) {
        add('range', `${name} in a wider range, ${d.type === 'range' ? `${fmtLit(lo - w)}..${fmtLit(hi + w)}` : `[${fmtLit(lo - w)}, ${fmtLit(hi + w)}]`}`, top.map(x => x.dom === b.dom ? { ...x, dom: nd } : x), node);
      }
    }
  });
  // Keep the list readable: no duplicates, at most 16.
  const seen = new Set();
  return out.filter(v => { const k = v.label; if (seen.has(k)) return false; seen.add(k); return true; }).slice(0, 16);
}

/* Variations of a claim (after unfolding a top-level definition call and peeling its ∀s). */
function claimVariations(body, env) {
  const P = MV.prepareClaim(body, env);
  return { scope: P.scope, variants: variationsOf(P.U, P.node), original: P.shown };
}

/* Check each variation of a claim. Yields progress; returns [{ ...variant, info }]. */
function* checkClaimVariations(body, env, opts = {}) {
  const { scope, variants } = claimVariations(body, env);
  const out = [];
  for (let i = 0; i < variants.length; i++) {
    const v = variants[i];
    let info = null, error = null;
    try { info = yield* MV.analyzeSteps(v.node, scope, { factor: opts.factor || 0.5, stress: opts.stress || 0, budget: 4000 }); }
    catch (e) { if (e instanceof MV.MVError) error = e.message; else throw e; }
    out.push({ ...v, info, error });
    yield { phase: 'variations', done: i + 1, total: variants.length };
  }
  return out;
}

/* Variations of a definition: each becomes a temporary definition with the same parameters. */
// Replace calls to definitions by their bodies, one level deep.
function inlineOnce(node, env) {
  let out = node;
  walk(node, n => {
    if (n.type !== 'call' || n.f.type !== 'id') return;
    const d = MV.DEFS.get(env[n.f.name]);
    if (!d || d.params.length !== n.args.length) return;
    out = replaceNode(out, n, MV.subst(d.body, new Map(d.params.map((p, i) => [p, n.args[i]]))));
  });
  return out;
}

function definitionVariations(fn) {
  const d = MV.DEFS.get(fn);
  if (!d) return [];
  const own = variationsOf([], d.body);
  const inner = variationsOf([], inlineOnce(d.body, d.env)).filter(v => !own.some(o => o.label === v.label));
  return [...own, ...inner].slice(0, 16).map(v => {
    const body = MV.compile(v.node);
    const vf = (...args) => {
      const e = Object.create(d.env);
      d.params.forEach((p, i) => { e[p] = args[i]; });
      return body(e);
    };
    vf.label = `${fn.label} (${v.label})`;
    vf.arity = d.params.length;
    return { ...v, fn: vf };
  });
}

/* ---------- sharpness: the critical value of a constant ---------- */

// Recognise a number as a simple closed form: p/q, p√k/q, pπ/q, e, ln 2.
function closedForm(x, tol = 2e-4) {
  if (!Number.isFinite(x)) return null;
  const near = (val, t = tol) => Math.abs(x - val) <= t * Math.max(1, Math.abs(x));
  for (let q = 1; q <= 12; q++) { const p = Math.round(x * q); if (near(p / q, 1e-9)) return (q === 1 ? `${p}` : `${p}/${q}`).replace(/^-/, '−'); }
  const squareFree = k => { for (let d = 2; d * d <= k; d++) if (k % (d * d) === 0) return false; return true; };
  const cands = [[Math.E, 'e', 2], [Math.LN2, 'ln 2', 3], [1 / Math.E, '1/e', 3], [(1 + Math.sqrt(5)) / 2, 'φ = (1 + √5)/2', 4]];
  for (let k = 2; k <= 30; k++) {
    if (!squareFree(k)) continue;
    for (let q = 1; q <= 6; q++) for (let p = 1; p <= 12; p++) if (gcd(p, q) === 1) cands.push([p * Math.sqrt(k) / q, `${p === 1 ? '' : p}√${k}${q === 1 ? '' : '/' + q}`, p + q + k / 4]);
  }
  for (let q = 1; q <= 12; q++) for (let p = 1; p <= 24; p++) if (gcd(p, q) === 1) cands.push([p * Math.PI / q, `${p === 1 ? '' : p}π${q === 1 ? '' : '/' + q}`, p + q + 1]);
  // The simplest form that matches, not the closest.
  let best = null;
  for (const [val, s, cost] of cands) for (const sign of [1, -1]) {
    if (near(sign * val) && (!best || cost < best.cost)) best = { cost, s: (sign < 0 ? '−' : '') + s };
  }
  return best ? best.s : null;
}
const gcd = (a, b) => { while (b) [a, b] = [b, a % b]; return a; };

/* For a claim "∀…: L ≤ c" (or ≥, <, >, with the constant on either side), find the critical c:
   the largest (or smallest) value of the other side over the samples, refined by a search. */
function* sharpness(body, env, opts = {}) {
  const P = MV.prepareClaim(body, env);
  if (P.kind !== 'cmp' || !P.U.length) return null;
  const [A, B] = P.concl.args;
  let side, constant, op = P.op;
  if (num(B) !== null) { side = 0; constant = num(B); }
  else if (num(A) !== null) { side = 1; constant = num(A); op = { '<': '>', '<=': '>=', '>': '<', '>=': '<=' }[op] || op; }
  else return null;
  if (!['<', '<=', '>', '>='].includes(op)) return null;
  const upper = op === '<' || op === '<='; // the other side must stay below the constant
  const info = yield* MV.analyzeSteps(body, env, { search: false, factor: opts.factor || 1 });
  const val = r => side === 0 ? r.L : r.R;
  const usable = info.res.filter(r => (r.s === 'ok' || r.s === 'fail') && typeof val(r) === 'number' && Number.isFinite(val(r)));
  if (!usable.length) return null;
  let best = usable.reduce((a, r) => (upper ? val(r) > val(a) : val(r) < val(a)) ? r : a);
  // Refine by pushing the other side as far as it goes.
  const shape = best.vals.map(v => typeof v === 'number' ? 1 : (Array.isArray(v) && v.every(x => typeof x === 'number')) ? v.length : 0);
  if (shape.every(s => s > 0)) {
    const toVals = x => { const out = []; let k = 0; for (const s of shape) { out.push(s === 1 ? x[k] : x.slice(k, k + s)); k += s; } return out; };
    const f = x => {
      const vals = toVals(x);
      const e = MV.bindValues(P, vals);
      if (!e) return Infinity;
      const r = MV.evalSample(P, e, { vals, env: e, s: 'ok' });
      if ((r.s !== 'ok' && r.s !== 'fail') || typeof val(r) !== 'number' || !Number.isFinite(val(r))) return Infinity;
      if (upper ? val(r) > val(best) : val(r) < val(best)) best = r;
      return upper ? -val(r) : val(r);
    };
    const starts = usable.slice().sort((a, b) => upper ? val(b) - val(a) : val(a) - val(b)).slice(0, 5);
    const t0 = Date.now();
    for (const s of starts) {
      const x0 = s.vals.flatMap(v => typeof v === 'number' ? [v] : v);
      yield* MV.nelderMead(f, x0, x0.map(v => Math.max(1e-3, Math.abs(v) * 0.05, 0.05)), 300, () => Date.now() - t0 > 2000);
    }
  }
  const critical = val(best);
  return {
    constant, critical, upper, side, at: best, form: closedForm(critical), op,
    holds: upper ? critical <= constant : critical >= constant,
  };
}

Object.assign(MV, { inlineOnce, replaceNode, variationsOf, claimVariations, checkClaimVariations, definitionVariations, sharpness, closedForm });
})(typeof window !== 'undefined' ? window : globalThis);
