/* Concepts and interpretations, without the page.
   - formsAt(C, args): every form of a concept at one list of arguments, and whether they agree.
   - exampleArgs(C, binders, env): argument lists to try, from binders such as those of an
     "examples:" line (or the parameters' types).
   - conceptsFor(v, env): the one-parameter concepts in scope whose type contains v, and whether v
     is an instance of each.
   - representationsOf(v): the ways of looking at a value that libraries registered with
     MathViz.represent (a matrix as a linear map, a complex number in polar form, …). */
'use strict';
(function () {
const MV = globalThis.MV;

function evalForm(fn, args, valued) {
  const before = MV.INEXACT;
  MV.INEXACT = false;
  try {
    const v = valued ? fn : fn(...args);
    return { v, inexact: MV.INEXACT };
  } catch (err) { return { error: err.message || String(err) }; }
  finally { MV.INEXACT = before; }
}

function sameValue(a, b) {
  if (typeof a === 'boolean' || typeof b === 'boolean') return a === b;
  try { return MV.equalValues(a, b); } catch (e) { return false; }
}

// One row: each form's value at args. agree is true, false, or null when a form failed to evaluate.
function formsAt(C, args) {
  const results = C.forms.map(f => ({ form: f, ...evalForm(f.fn, args, !C.params.length) }));
  const good = results.filter(r => !('error' in r));
  let agree = good.every(r => sameValue(r.v, good[0].v));
  if (agree && good.length < results.length) agree = null;
  return { args, results, agree };
}

// Argument lists from binders, depth first, at most max of them.
function exampleArgs(C, binders, env, max = 12) {
  const out = [];
  const per = Math.max(2, Math.ceil(Math.pow(max, 1 / Math.max(1, binders.length))));
  const go = (i, e) => {
    if (out.length >= max) return;
    if (i === binders.length) { out.push(C.params.map(p => e[p])); return; }
    const b = binders[i];
    const D = MV.compileDomain(b.dom)(e);
    let vals;
    if (D.kind === 'finite') vals = D.values.slice(0, binders.length === 1 ? max : per + 1);
    else vals = D.sample(per * 3).filter((x, k, a) => a.findIndex(y => sameValue(x, y)) === k).slice(0, per);
    for (const v of vals) {
      const e2 = Object.create(e);
      if (b.pattern) b.pattern.forEach((n, k) => { e2[n] = v[k]; }); else e2[b.name] = v;
      go(i + 1, e2);
      if (out.length >= max) return;
    }
  };
  go(0, Object.create(env));
  return out;
}

// Binders for a concept: given ones, its "examples:" line, or the parameters' types.
function conceptBinders(C, given, env) {
  const binders = [...(given || [])];
  const covered = new Set(binders.flatMap(MV.binderNames));
  for (const b of C.examples || []) if (!MV.binderNames(b).some(n => covered.has(n))) { binders.push(b); MV.binderNames(b).forEach(n => covered.add(n)); }
  const missing = [];
  C.params.forEach((p, i) => {
    if (covered.has(p)) return;
    if (C.types[i]) binders.push({ name: p, pattern: null, dom: C.types[i] });
    else missing.push(p);
  });
  return { binders, missing };
}

function conceptRows(C, given, env, max = 12) {
  if (!C.params.length) return { rows: [formsAt(C, [])], missing: [] };
  const { binders, missing } = conceptBinders(C, given, env);
  if (missing.length) return { rows: [], missing };
  return { rows: exampleArgs(C, binders, env, max).map(args => formsAt(C, args)), missing: [] };
}

// The distinct concepts in scope (env names them as they were defined).
function conceptsInScope(env) {
  const seen = new Set(), out = [];
  for (const C of MV.CONCEPTS.values()) {
    if (seen.has(C) || typeof C.name !== 'string' || env[C.name] !== C.fn) continue;
    seen.add(C);
    out.push(C);
  }
  return out;
}

// Is v an instance of the one-parameter concepts that apply to it: those whose parameter's type
// contains v, and untyped ones that answer true or false for it without an error.
function conceptsFor(v, env) {
  const out = [];
  for (const C of conceptsInScope(env)) {
    if (C.params.length !== 1) continue;
    if (C.types[0]) {
      let ok = false;
      try { ok = MV.compileDomain(C.types[0])(C.env).contains(v); } catch (e) { ok = false; }
      if (ok) out.push({ concept: C, ...evalForm(C.fn, [v]) });
    } else {
      const r = evalForm(C.fn, [v]);
      if (!('error' in r) && typeof r.v === 'boolean') out.push({ concept: C, ...r });
    }
  }
  return out;
}

function representationsOf(v) {
  return MV.REPRESENT.filter(r => { try { return !!r.test(v); } catch (e) { return false; } });
}

Object.assign(MV, { formsAt, exampleArgs, conceptBinders, conceptRows, conceptsInScope, conceptsFor, representationsOf, sameValue });
})();
