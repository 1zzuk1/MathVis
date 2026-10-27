/* Theorem Sketchpad UI — concepts and interpretations.
   - A concept (concept name(p) where form: … form: …) gets a card setting its forms side by side
     on its examples; a cell opens that form's own check.
   - interpret name(args): every form of a concept at those arguments, each checked and drawn.
   - interpret value: every way the libraries know of looking at it (MathViz.represent), and the
     one-parameter concepts it is an instance of. */
'use strict';
(function () {
const APP = window.APP;
const { h, makeCtx } = APP;
const { MVError, esc, fmt, pp, ppText, compile, checkNames } = MV;

// Numbers stay numbers, so algebra can still settle the form; other values are carried as they are.
const valueNode = (v, label) => (typeof v === 'number' && Number.isInteger(v) && v >= 0 ? { type: 'num', v } : { type: 'value', v, label: label || fmt(v) });
const short = s => (s.length > 40 ? s.slice(0, 38) + '…' : s);
const shown = v => short(fmt(v));
const mark = r => ('error' in r ? '!' : typeof r.v === 'boolean' ? (r.v ? '✓' : '✗') : shown(r.v));

function conceptSignature(C) {
  const params = C.params.map((p, i) => esc(ppText({ type: 'id', name: p })) + (C.types[i] ? ': ' + MV.ppDom(C.types[i], true) : '')).join(', ');
  return `<span class="fkw">concept</span> <span class="up">${esc(C.name)}</span>${C.params.length ? `(${params})` : ''}`;
}

function formList(card, C) {
  const list = h('ul', 'axiom-list concept-forms');
  for (const f of C.forms) {
    const li = h('li');
    li.innerHTML = `<strong>${esc(f.name)}</strong>: ${pp(f.body)}`;
    list.append(li);
  }
  card.body.append(list);
}

// A form's body with the concept's parameters replaced by the given values.
function formAt(C, form, args, labels) {
  const map = new Map(C.params.map((p, i) => [p, valueNode(args[i], labels && labels[i])]));
  return map.size ? MV.subst(form.body, map) : form.body;
}

// The full check of one form at one argument list, as a card in a panel (or in host).
async function showForm(card, C, form, args, labels, host) {
  let box = host;
  if (!box) {
    box = h('div', 'panel form-detail');
    const old = card.el.querySelector('.form-detail');
    if (old) old.remove();
    const head = h('div', 'trace-head');
    head.append(h('strong', null, `${form.name} at ${C.params.map((p, i) => `${p} = ${labels ? labels[i] : shown(args[i])}`).join(', ') || C.name}`));
    const close = h('button', 'link-btn', 'Close');
    close.type = 'button';
    close.addEventListener('click', () => box.remove());
    head.append(close);
    box.append(head);
    card.el.append(box);
  }
  const sub = APP.makeCard(null, 'form', `${C.name}_${form.name}`, box);
  const body = formAt(C, form, args, labels);
  sub.formula(pp(body));
  try {
    if (MV.propositional(form.body) && C.params.length) await APP.runClaim(body, C.env, sub);
    else {
      const v = C.params.length ? form.fn(...args) : form.fn;
      sub.formula(`${pp(body)} <span class="eq">=</span> <span class="val">${esc(fmt(v))}</span>`);
      if (typeof v === 'boolean') sub.setStatus(v ? 'ok' : 'fail', v ? 'true' : 'false');
      else showRepresentations(sub, v, { limit: 1 });
    }
  } catch (err) { sub.error(err instanceof MVError ? err : new MVError(err.message || String(err))); }
  if (!host) box.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
}

// How far apart numeric forms are, when they don't agree exactly.
function spread(results) {
  const xs = results.filter(r => !('error' in r)).map(r => +r.v);
  if (xs.length < 2 || xs.some(x => !Number.isFinite(x))) return null;
  const lo = Math.min(...xs), hi = Math.max(...xs), m = Math.max(Math.abs(lo), Math.abs(hi), 1e-300);
  return (hi - lo) / m;
}

// A dozen rows to show: every disagreement first, then rows of each outcome of the first form in
// turn (so true and false cases both appear), in their original order.
function pickRows(all, max) {
  if (all.length <= max) return all;
  const keep = new Set(all.filter(r => r.agree !== true).slice(0, max));
  const key = r => ('error' in r.results[0] ? '!' : fmt(r.results[0].v));
  const groups = new Map();
  for (const r of all) if (!keep.has(r)) { const k = key(r); if (!groups.has(k)) groups.set(k, []); groups.get(k).push(r); }
  const lists = [...groups.values()];
  for (let i = 0; keep.size < max && lists.some(l => i < l.length); i++) for (const l of lists) if (i < l.length && keep.size < max) keep.add(l[Math.floor(i * l.length / Math.min(l.length, max))] || l[i]);
  return all.filter(r => keep.has(r));
}

/* The forms side by side on examples. given: binders from "explain name for …". */
async function runConcept(C, env, card, given = null) {
  card.formula(conceptSignature(C));
  if (C.doc) card.doc(C.doc);
  formList(card, C);
  const { binders, missing } = C.params.length ? MV.conceptBinders(C, given, env) : { binders: [], missing: [] };
  if (missing.length) {
    makeCtx(card).note(`To compare the forms on examples, give ${missing.join(' and ')} a type (as in ${missing[0]}: R), add a comment line "examples: ${missing[0]} in {…}" above the concept, or write "explain ${C.name} for ${missing[0]} in …".`);
    card.setStatus('info', `${C.forms.length} forms`);
    return;
  }
  // Up to 64 examples (as many as fit in a few seconds), of which a varied dozen are shown.
  const argLists = C.params.length ? MV.exampleArgs(C, binders, env, 64) : [[]];
  const ctl = card.progress('Comparing the forms');
  const all = [], t0 = performance.now();
  try {
    for (let i = 0; i < argLists.length; i++) {
      if (ctl.cancelled || (i >= 12 && performance.now() - t0 > 3000)) break;
      all.push(MV.formsAt(C, argLists[i]));
      ctl.onProgress({ phase: 'examples', done: i + 1, total: argLists.length });
      await MV.yieldNow();
    }
  } finally { ctl.done(); }
  const rows = pickRows(all, 12);
  const bad = all.filter(r => r.agree === false), unsure = all.filter(r => r.agree === null);
  const close = !C.params.length && bad.length ? spread(rows[0].results) : null;
  if (close !== null && close < 1e-3) card.setStatus('ok', `The forms agree to ${Math.max(1, Math.floor(-Math.log10(close)))} digits`);
  else if (bad.length) card.setStatus('fail', `The forms disagree on ${bad.length} of ${all.length} example${all.length === 1 ? '' : 's'}`);
  else if (unsure.length) card.setStatus('info', `The forms agree where they can be evaluated (${all.length - unsure.length} of ${all.length})`);
  else card.setStatus('ok', C.params.length ? `All ${C.forms.length} forms agree on ${all.length} example${all.length === 1 ? '' : 's'}` : `All ${C.forms.length} forms agree`);

  const wrap = h('div', 'table-wrap'), t = h('table', 'var-table matrix axioms concept-table');
  const head = h('tr');
  if (C.params.length) head.append(h('th', null, C.params.map(p => ppText({ type: 'id', name: p })).join(', ')));
  for (const f of C.forms) head.append(h('th', null, f.name));
  head.append(h('th', null, 'agree?'));
  t.append(head);
  for (const row of rows) {
    const tr = h('tr', row.agree === false ? 'disagree' : null);
    if (C.params.length) tr.append(h('td', null, row.args.map(shown).join(', ')));
    for (const r of row.results) {
      const cls = 'error' in r ? 'error-msg' : r.v === true ? 'gained' : r.v === false ? 'lost' : '';
      const td = h('td', 'clickable ' + cls, mark(r));
      td.title = ('error' in r ? r.error : `${r.form.name}: ${fmt(r.v)}${r.inexact ? ' (estimated)' : ''}`) + ' · click for the full check';
      td.addEventListener('click', () => showForm(card, C, r.form, row.args));
      tr.append(td);
    }
    tr.append(h('td', row.agree === false ? 'lost' : row.agree ? 'gained' : 'muted', row.agree === false ? 'no' : row.agree ? 'yes' : '?'));
    t.append(tr);
  }
  wrap.append(t);
  card.body.append(wrap);
  const ctx = makeCtx(card);
  if (all.length > rows.length) ctx.note(`Showing ${rows.length} of the ${all.length} examples tried: every disagreement, and cases of each outcome.`);
  if (close !== null && close >= 1e-3) ctx.note(`The values differ by ${fmt(+close.toPrecision(2))} relative to their size.`);
  else if (close !== null) ctx.note('The forms are computed approximately (a limit cut off, a series summed to a finite term), so they agree only up to the precision of each.');
  if (bad.length && C.params.length) {
    const r = bad[0], split = r.results.filter(x => !('error' in x) && !MV.sameValue(x.v, r.results[0].v)).map(x => x.form.name);
    ctx.note(`At ${C.params.map((p, i) => `${p} = ${shown(r.args[i])}`).join(', ')}, ${split.join(' and ')} ${split.length === 1 ? 'says' : 'say'} otherwise than ${r.results[0].form.name}. Click a cell to see the check of that form.`, 'caveat');
  } else if (C.params.length) ctx.note('Click a cell to see how that form is checked on that example. Agreement on examples is evidence that the forms are equivalent, not a proof.');
  if (unsure.length) ctx.note(`On ${unsure.length} example${unsure.length === 1 ? '' : 's'} a form couldn't be evaluated (marked !); hover over it for the reason.`);
}

/* ---------------- interpret ---------------- */

// Each registered representation of v, in its own section. They share their sliders: one "point"
// slider moves the point in every picture at once.
function showRepresentations(card, v, opts = {}) {
  let reps = MV.representationsOf(v);
  if (opts.limit) reps = reps.slice(0, opts.limit);
  const state = {}, draws = [];
  const all = () => draws.forEach(d => d());
  for (const rep of reps) {
    const sec = h('section', 'interp');
    const title = h('h4', 'interp-title', rep.label || rep.name);
    if (rep.lib) title.append(h('span', 'muted', ` · ${rep.lib}`));
    sec.append(title);
    if (rep.doc) sec.append(h('p', 'note interp-doc', rep.doc));
    const host = h('div', 'interp-body');
    sec.append(host);
    card.body.append(sec);
    const draw = () => {
      card.figs = card.figs.filter(f => !host.contains(f.wrap));
      host.replaceChildren();
      const before = card.figs.length;
      try {
        rep.render(makeCtx(card, state, all, host), v);
        for (const f of card.figs.slice(before)) f.render();
      } catch (err) { host.append(h('p', 'error-msg', `This view failed: ${err.message}`)); }
    };
    draws.push(draw);
  }
  all();
  return reps.length;
}

async function runInterpret(ast, env, card) {
  checkNames(ast.expr, env);
  const e = ast.expr;
  // A concept at some arguments: every form, each checked on its own.
  const head = e.type === 'call' && e.f.type === 'id' ? env[e.f.name] : e.type === 'id' ? env[e.name] : undefined;
  const C = MV.conceptOf(head) || (e.type === 'id' ? MV.CONCEPTS.get(e.name) : null);
  if (C && (e.type === 'call' || !C.params.length)) {
    const args = e.type === 'call' ? e.args.map(a => compile(a)(env)) : [];
    if (args.length !== C.params.length) throw new MVError(`${C.name} takes ${C.params.length} argument${C.params.length === 1 ? '' : 's'} (${C.params.join(', ')}) but got ${args.length}.`);
    const labels = e.type === 'call' ? e.args.map(a => ppText(a)) : [];
    card.formula(`<span class="fkw">interpret</span> ${pp(e)}`);
    if (C.doc) card.doc(C.doc);
    const row = MV.formsAt(C, args);
    card.setStatus(row.agree === false ? 'fail' : row.agree ? 'ok' : 'info',
      row.agree === false ? `The ${C.forms.length} forms of ${C.name} disagree here` : row.agree ? `All ${C.forms.length} forms of ${C.name} agree: ${mark(row.results[0])}` : `Some forms of ${C.name} can't be evaluated here`);
    makeCtx(card).table(['Form', 'Definition', 'Value'], row.results.map(r => [r.form.name, ppText(formAt(C, r.form, args, labels)), 'error' in r ? r.error : fmt(r.v)]));
    for (const r of row.results) {
      const box = h('div', 'interp-form');
      card.body.append(box);
      await showForm(card, C, r.form, args, labels, box);
    }
    return;
  }
  const v = compile(e)(env);
  card.formula(`<span class="fkw">interpret</span> ${pp(e)} <span class="eq">=</span> <span class="val">${esc(short(fmt(v)))}</span>`);
  const fn = e.type === 'id' && typeof v === 'function' ? v : null;
  if (fn && fn.doc) card.doc(fn.doc);
  const n = showRepresentations(card, v);
  const memberships = MV.conceptsFor(v, env);
  if (memberships.length) {
    const sec = h('section', 'interp');
    sec.append(h('h4', 'interp-title', 'As an instance of'));
    card.body.append(sec);
    makeCtx(card, {}, null, sec).table(['Concept', 'Holds?'], memberships.map(m => [m.concept.name, 'error' in m ? m.error : typeof m.v === 'boolean' ? (m.v ? '✓ yes' : '✗ no') : fmt(m.v)]),
      null, i => { const m = memberships[i]; showForm(card, m.concept, m.concept.forms[0], [v], [ppText(e)]); });
  }
  if (!n && !memberships.length) {
    card.setStatus('info', 'No other views');
    makeCtx(card).note(`No library describes ${MV.describeValue(v)} in other ways yet. Libraries add ways of looking at values with MathViz.represent, and concepts with several forms with "concept".`);
  } else card.setStatus('info', `${n} view${n === 1 ? '' : 's'}${memberships.length ? `, ${memberships.length} concept${memberships.length === 1 ? '' : 's'}` : ''}`);
}

Object.assign(APP, { runConcept, runInterpret, showRepresentations });
})();
