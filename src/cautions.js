/* Theorem Sketchpad — claims sampling can't decide.

   Some claims have a shape that sampling answers wrongly, and always in the same direction: they
   "hold" on every sample while being false. claimCautions(P) looks at a prepared claim (its
   statement and the definitions it uses) for three such shapes and explains each one it finds:

   - extremum:  ∃p ∈ S: ∀q ∈ S: f(q) ≤ f(p). Both variables are drawn from the same samples, so
                the best sample always passes, whether or not f has a largest value on S.
   - pairs:     ∀x, y ∈ S: |x − y| < δ → …, with δ chosen by an enclosing ∃. x and y are drawn
                independently, so pairs that close are rare and nearly every sample is vacuous.
   - window:    ∃M: ∀x ∈ S: |x| ≤ M, with S unbounded. S is sampled in a window, so a bound that
                fits the samples can still fail further out.

   The app shows these on a claim that holds on its samples, instead of a plain "holds". */
'use strict';
(function (global) {
const MV = global.MV;
const { ppText, freeNames, binderNames, subst } = MV;

const names = node => new Set(freeNames(node).keys());
const text = node => ppText(node);

// Is the domain sampled (rather than listed in full)? Unknown counts as sampled.
function domainInfo(dom, scope, bound) {
  const info = { sampled: true, D: null };
  if ([...names(dom)].some(n => bound.has(n))) return info;
  try {
    const D = MV.toDomain(MV.compileDomain(dom)(scope));
    info.D = D;
    const els = MV.elementsOf(D);
    if (els && els.length <= 4000) info.sampled = false;
  } catch (e) { /* not evaluable here: assume sampled */ }
  return info;
}

// A point of D far from its samples, if D reaches that far (D unbounded), else null.
function farPoint(D) {
  if (!D || !D.contains || !D.sample) return null;
  let c;
  try { c = D.sample(4).find(x => D.contains(x)); } catch (e) { return null; }
  if (c === undefined) return null;
  const n = Array.isArray(c) ? c.length : 1;
  for (const R of [1e6, 1e9]) for (let i = 0; i < n; i++) for (const s of [1, -1]) {
    const q = Array.isArray(c) ? c.map((x, j) => +x + (j === i ? s * R : 0)) : +c + s * R;
    try { if (D.contains(q)) return q; } catch (e) { /* skip */ }
  }
  return null;
}

// The comparisons in a formula (through and, or, not, implications).
function comparisons(node, out = []) {
  if (!node || typeof node !== 'object') return out;
  if (node.type === 'cmp') out.push(node);
  else if (node.type === 'bin' && ['and', 'or', '->', '<->'].includes(node.op)) { comparisons(node.a, out); comparisons(node.b, out); }
  else if (node.type === 'un' && node.op === 'not') comparisons(node.a, out);
  return out;
}

function claimCautions(P) {
  const out = [], seen = new Set();
  const add = (kind, key, msg) => { if (!seen.has(kind + key)) { seen.add(kind + key); out.push({ kind, text: msg }); } };
  // Quantified variables in force: name → { q: 'forall' | 'exists', dom, info, quant }.
  function walk(node, scope, vars, depth, stack) {
    if (!node || typeof node !== 'object' || depth > 6 || out.length >= 3) return;
    if (Array.isArray(node)) { node.forEach(n => walk(n, scope, vars, depth, stack)); return; }
    if (node.type === 'quant') {
      const bound = new Set(vars.keys());
      const mine = new Map(vars);
      const here = [];
      for (const b of node.binders) {
        const info = b.dom && b.dom.type !== 'bound' ? domainInfo(b.dom, scope, bound) : { sampled: true, D: null };
        let shown = text(b.dom);
        if (b.dom.type === 'id' && info.D) { try { const d = MV.fmt(scope[b.dom.name]); if (d && d !== shown) shown = `${shown} = ${d}`; } catch (e) { /* keep the name */ } }
        for (const n of binderNames(b)) { const v = { q: node.q, dom: b.dom, info, name: n, shown }; mine.set(n, v); here.push(v); }
      }
      if (node.q === 'forall') checkForall(node, here, mine);
      walk(node.body, scope, mine, depth, stack);
      return;
    }
    if (node.type === 'call' && node.f.type === 'id' && !vars.has(node.f.name)) {
      const fv = scope[node.f.name], d = fv && MV.DEFS.get(fv);
      if (d && d.params.length === node.args.length && !stack.includes(d.name) && !(d.fromLibrary && MV.ANALYZERS && MV.ANALYZERS[d.name])) {
        const closed = node.args.every(a => ![...names(a)].some(n => vars.has(n)));
        if (closed) {
          // Arguments known: run through the definition with its parameters bound to their values.
          let e2 = null;
          try { e2 = Object.create(d.env); d.params.forEach((p, i) => { e2[p] = MV.compile(node.args[i])(scope); }); } catch (e) { e2 = null; }
          if (e2) walk(d.body, e2, new Map(), depth + 1, [...stack, d.name]);
        } else {
          const map = new Map(d.params.map((p, i) => [p, node.args[i]]));
          walk(subst(d.body, map), scope, vars, depth + 1, [...stack, d.name]);
        }
      }
      walk(node.args, scope, vars, depth, stack);
      return;
    }
    for (const k of Object.keys(node)) if (k !== 'pos' && node[k] && typeof node[k] === 'object') walk(node[k], scope, vars, depth, stack);
  }

  function checkForall(node, here, vars) {
    // extremum: ∀q ∈ S under ∃p ∈ S (the same S), with a comparison involving both.
    for (const qv of here) {
      if (!qv.info.sampled) continue;
      for (const pv of vars.values()) {
        if (pv.q !== 'exists' || pv === qv || !pv.dom || !qv.dom || text(pv.dom) !== text(qv.dom)) continue;
        // An ordering of the two (an equation, as for an identity element, is decided fine).
        const both = comparisons(node.body).some(c => c.ops.some(o => ['<', '<=', '>', '>='].includes(o)) && (ns => ns.has(pv.name) && ns.has(qv.name))(names(c)));
        if (!both) continue;
        add('extremum', pv.name + qv.name, `${pv.name} and ${qv.name} both range over ${qv.shown}, and ${qv.name}'s samples are among ${pv.name}'s, so the best sample always passes. Sampling can't tell whether a largest (or smallest) value is attained there: on an open set the best sample sits just inside the edge. attains_max(f, S) and attains_min(f, S) (import compactness) decide it by following the climb to the edge of S.`);
      }
    }
    // pairs: ∀x, y ∈ S: (comparison of x with y) < (something chosen by an ∃) → …
    const sampled = [...vars.values()].filter(v => v.q === 'forall' && v.info.sampled);
    if (node.body.type === 'bin' && node.body.op === '->') {
      for (const c of comparisons(node.body.a)) {
        if (!c.ops.every(o => o === '<' || o === '<=')) continue;
        for (let i = 0; i + 1 < c.args.length; i++) {
          const L = names(c.args[i]), R = names(c.args[i + 1]);
          const pair = sampled.filter(v => L.has(v.name) && !R.has(v.name));
          const small = [...R].some(n => vars.has(n) && vars.get(n).q === 'exists');
          if (pair.length >= 2 && small && pair.some(v => here.includes(v))) {
            const [x, y] = pair, r = text(c.args[i + 1]);
            add('pairs', x.name + y.name, `${x.name} and ${y.name} are sampled independently, so pairs with ${text(c.args[i])} < ${r} are rare and nearly every sample passes vacuously, whatever ${r} is. To sample close pairs, write ${y.name} as ${x.name} + h with h in [-${r}, ${r}] (in ℝⁿ: h in Ball(0, ${r})), as uniformly_continuous_on does.`);
          }
        }
      }
    }
    // window: ∀x ∈ S: … ≤ M with M chosen by an ∃, and S unbounded. Only in the conclusion: a
    // hypothesis such as |x − a| < δ keeps x near a, where the samples are.
    const concl = node.body.type === 'bin' && node.body.op === '->' ? node.body.b : node.body;
    for (const xv of here) {
      if (!xv.info.sampled || !xv.info.D) continue;
      const uses = comparisons(concl).some(c => c.ops.some(o => ['<', '<=', '>', '>='].includes(o)) && c.args.some((a, i) => {
        const A = names(a);
        return A.has(xv.name) && c.args.some((b, j) => j !== i && [...names(b)].some(n => vars.has(n) && vars.get(n).q === 'exists' && !names(b).has(xv.name)));
      }));
      if (!uses) continue;
      const far = farPoint(xv.info.D);
      if (far === null) continue;
      add('window', xv.name, `${xv.shown} is unbounded (it contains ${MV.fmt(far)}), but it is sampled only in a window, so a bound that fits every sample can still fail further out. bounded(S) (topology, with compactness loaded) also looks far out along rays.`);
    }
  }

  try {
    walk(P.shown, P.scope, new Map(), 0, []);
  } catch (e) { /* a caution is a hint; never let it break a check */ }
  return out;
}

/* ---------- failures that may not be real ----------
   A claim that fails can still be true when every failing sample is one a finite check misjudges:
   - hard: an example built to fool finite checks (a sequence converging like 1/log n, one that
     differs from a constant only at powers of 2, …), which says so in its .hard;
   - tiny: it fails only for very small values of a variable ranging over (0, c] (an ε), holds for
     every larger one, and looking again with a much deeper search for δ rescued some samples: the δ
     needed shrinks so fast that below some ε floating point can't hold it (δ ≈ ε² for √x). */
function failCautions(info) {
  const out = [];
  const fails = (info.res || []).filter(r => r.s === 'fail');
  if (!fails.length) return out;
  const P = info.prepared || {};
  // hard examples
  const hardOf = r => (r.vals || []).find(v => v && (typeof v === 'object' || typeof v === 'function') && typeof v.hard === 'string');
  if (fails.every(hardOf)) {
    const seen = new Set();
    for (const r of fails) {
      const v = hardOf(r), label = MV.fmt(v);
      if (seen.has(v.hard) || seen.size >= 2) continue;
      seen.add(v.hard);
      out.push({ kind: 'hard', text: `Every failing example is one a finite check misjudges: ${label}, where ${v.hard}. So this failure may not be real.` });
    }
    return out;
  }
  // tiny ε
  const U = P.U || info.binders || [];
  const rescued = (info.res || []).filter(r => r.deeper).length;
  if (!rescued) return out;
  U.forEach((b, i) => {
    if (out.length || !b.name) return;
    const d = b.dom;
    const fromZero = d && ((d.type === 'interval' && d.loOpen && d.lo.type === 'num' && d.lo.v === 0) || (d.type === 'bound' && d.op === '>' && d.c.type === 'num' && d.c.v === 0));
    if (!fromZero) return;
    const fe = fails.map(r => +r.vals[i]).filter(Number.isFinite);
    if (fe.length !== fails.length) return;
    const top = Math.max(...fe);
    const larger = (info.res || []).some(r => r.s === 'ok' && +r.vals[i] > 10 * top);
    if (!larger) return;
    out.push({ kind: 'tiny', text: `It fails only for ${b.name} ≤ ${MV.fmt(+top.toPrecision(3))} and holds for every larger ${b.name} tried. A much deeper search rescued ${rescued} failing sample${rescued > 1 ? 's' : ''}, so what has to be found for each ${b.name} (a δ, an N, …) shrinks very fast as ${b.name} → 0, like ε² for √x. Below about 10⁻¹⁴ no search in floating point can find it, so these failures may be a limit of the arithmetic, not of the claim.` });
  });
  return out;
}
MV.failCautions = info => {
  try { return failCautions(info); } catch (e) { return []; }
};

// Looking at the claim evaluates some sets and arguments; that mustn't change how the claim's own
// result is labelled (inexact, stressable).
MV.claimCautions = P => {
  if (P.cautions) return P.cautions;
  const inexact = MV.INEXACT, stressable = MV.STRESSABLE;
  try { return (P.cautions = claimCautions(P)); } finally { MV.INEXACT = inexact; MV.STRESSABLE = stressable; }
};
})(typeof window !== 'undefined' ? window : globalThis);
