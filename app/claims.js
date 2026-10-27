/* Theorem Sketchpad UI — checking claims and drawing them, and explaining definitions. */
'use strict';
(function () {
const APP = window.APP;
const { h, makeCtx, thumb, showTrace, reading, isNumArr } = APP;
const { MVError, esc, fmt, pp, ppText, compile, compileDomain, analyzeClaim, checkNames, minmax, stride } = MV;

const STATUS_COLOR = { ok: 'pos', fail: 'neg', vac: 'vac', undef: 'undef' };
const uniqSorted = arr => [...new Set(arr)].sort((a, b) => a - b);
function medianGap(u) {
  if (u.length < 2) return 1;
  const d = [];
  for (let i = 1; i < u.length; i++) d.push(u[i] - u[i - 1]);
  d.sort((a, b) => a - b);
  return d[Math.floor(d.length / 2)];
}
const count = n => n.toLocaleString('en-US');
const short = v => typeof v === 'number' ? fmt(+v.toPrecision(4)) : isNumArr(v) ? fmt(v.map(x => +x.toPrecision(4))) : fmt(v);
const flat = v => typeof v === 'number' ? [v] : v && v.__exact ? [+v] : isNumArr(v) ? v : null;
const nameOf = n => ppText({ type: 'id', name: n });
const isObject = v => (v && typeof v === 'object' && !isNumArr(v)) || (typeof v === 'function' && !v.domainCtor);

function statusBands(fig, sorted, discrete, include) {
  const xs = sorted.map(r => r.c[0]), n = sorted.length;
  const half = discrete ? 0.5 : 0;
  for (let i = 0; i < n;) {
    const s = sorted[i].s;
    let j = i;
    while (j + 1 < n && sorted[j + 1].s === s) j++;
    if (include[s]) {
      const x0 = i === 0 ? xs[0] - half : (xs[i - 1] + xs[i]) / 2;
      const x1 = j === n - 1 ? xs[n - 1] + half : (xs[j] + xs[j + 1]) / 2;
      fig.vband(x0, x1, include[s]);
    }
    i = j + 1;
  }
}

/* ---------------- running a claim ---------------- */

// A number or point shown in its simplest exact form when it has one (1/2, √2), else rounded.
const nice = v => typeof v === 'number' ? (MV.closedForm(v, 1e-12) || short(v)) : isNumArr(v) ? '(' + v.map(nice).join(', ') + ')' : fmt(v);

/* Check a claim and draw it. opts.examples (a definition's name) words the result as examples.
   Resolves to the analysis once it is drawn. */
async function runClaim(body, env, card, opts = {}) {
  checkNames(body, env, [], null, true);
  if (body.type === 'in') {
    let S = null;
    try { S = structureOf(compile(body.dom)(env)); } catch (e) { /* not a plain value */ }
    if (S) return runStructureCheck(body, env, card, S);
  }
  if (body.type === 'call' && body.f.type === 'id') {
    const f = env[body.f.name];
    if (f && f.doc) card.doc(f.doc);
  }
  if (body.type === 'id' && env[body.name] && env[body.name].__claim) {
    const c = env[body.name];
    card.formula(`<span class="fkw">${c.kind}</span> <span class="up">${esc(c.name)}</span>: ${pp(c.body)}`);
    if (c.doc) card.doc(c.doc);
  }
  let state = { factor: 1, restrict: null, stress: 0 };
  let last = null;
  const defs = APP.defsSnapshot(env);
  const draw = async () => {
    card.clearBody();
    card.clearActions();
    const ctl = card.progress(opts.examples ? 'Trying the examples' : 'Checking');
    let info;
    try { info = await APP.analyze(body, env, { factor: state.factor, restrict: state.restrict, stress: state.stress }, ctl, defs); }
    finally { ctl.done(); }
    last = info;
    if (info.unfolded && !opts.examples) card.unfolded(pp(info.shown), info.bindings);
    renderClaim(card, info, {
      ...opts,
      resample: box => { state = { ...state, restrict: box }; draw().catch(err => card.error(err)); },
    });
    const again = patch => () => { state = { ...state, ...patch }; draw().catch(err => card.error(err)); };
    if (state.restrict) card.action('Back to the full range', again({ restrict: null }));
    if (!info.exhaustive && info.k > 0 && state.factor < 64) card.action(`More samples (×${state.factor * 4})`, again({ factor: state.factor * 4 }), 'Check again with four times as many samples');
    if (info.stressable) {
      card.action(state.stress ? 'Back to the usual examples' : 'Try wilder examples', again({ stress: state.stress ? 0 : 1 }),
        'Add pathological examples: Takagi and Cantor functions, sin(1/x), combs, cusps, random polygons, slowly diverging sequences, …');
    }
    if (state.stress) card.el.classList.add('wild'); else card.el.classList.remove('wild');
    if (!opts.examples && info.k > 0) {
      card.action('Is every condition needed?', () => showVariations(card, body, env, state), 'Drop hypotheses, flip < and ≤, swap quantifiers and change ranges, and check each version');
    }
    if (!opts.examples && info.kind === 'cmp' && !info.count.fail && info.count.ok && !state.restrict) await proofSection(card, body, env, info);
    if (opts.after) opts.after(info, card);
  };
  await draw();
  return last;
}

/* ---------------- interval-arithmetic proofs ---------------- */

async function proofSection(card, body, env, info, maxBoxes = 4000) {
  let map;
  try { map = await MV.runSliced(MV.proveByIntervals(body, env, { maxBoxes, ms: maxBoxes > 4000 ? 8000 : 1500 }), {}); }
  catch (e) { return; }
  if (!map) return;
  let box = card.el.querySelector('.proof');
  if (box) box.remove();
  box = h('div', 'proof');
  card.body.append(box);
  const pct = k => (100 * map.share[k]).toFixed(map.share[k] > 0.999 || map.share[k] < 0.001 ? 0 : 1) + '%';
  if (map.proved) {
    card.setStatus('ok', 'Proved by interval arithmetic');
    box.append(h('p', 'note', `Interval arithmetic bounds both sides on every one of ${map.boxes.length.toLocaleString('en-US')} boxes covering the range, so the inequality holds everywhere, not only at samples${map.share.vac > 0 ? ' (boxes where the hypothesis is false need nothing)' : ''}.`));
  } else if (map.disproved) {
    box.append(h('p', 'note', `Interval arithmetic found boxes where the inequality fails everywhere (${pct('fail')} of the range).`));
  } else {
    box.append(h('p', 'note', `Interval arithmetic proved the inequality on ${pct('ok')} of the range${map.share.vac ? ` (and ${pct('vac')} needs nothing, the hypothesis being false)` : ''}; ${pct('open')} is undecided, typically where the two sides touch.`));
  }
  const show = h('button', 'link-btn', 'Show the proof map');
  show.type = 'button';
  show.addEventListener('click', () => { show.remove(); drawProofMap(card, box, map); });
  box.append(show);
  if (!map.proved && !map.disproved && maxBoxes < 64000) {
    const more = h('button', 'link-btn', 'Refine the proof');
    more.type = 'button';
    more.style.marginLeft = '14px';
    more.addEventListener('click', () => { more.textContent = 'Refining…'; proofSection(card, body, env, info, maxBoxes * 4); });
    box.append(more);
  }
}

function drawProofMap(card, host, map) {
  const ctx = APP.makeCtx(card, {}, null, host);
  const color = { ok: 'pos', fail: 'neg', vac: 'vac', open: 'undef' };
  const alpha = { ok: 0.45, fail: 0.85, vac: 0.25, open: 0.55 };
  if (map.coords === 1) {
    const [a] = map.box0;
    const fig = ctx.figure({ x: [a.lo, a.hi], y: [0, 1], height: 80, yAxis: false, xlabel: map.names[0] });
    for (const b of map.boxes) fig.vband(b.box[0].lo, b.box[0].hi, { color: color[b.s], alpha: alpha[b.s] });
    fig.render();
  } else if (map.coords === 2) {
    const [a, b] = map.box0;
    const fig = ctx.figure({ x: [a.lo, a.hi], y: [b.lo, b.hi], xlabel: map.names[0], ylabel: map.names[1], square: (a.hi - a.lo) / (b.hi - b.lo) < 3 && (b.hi - b.lo) / (a.hi - a.lo) < 3 });
    fig.cells(map.boxes.map(x => ({ x: (x.box[0].lo + x.box[0].hi) / 2, w: x.box[0].hi - x.box[0].lo, y: (x.box[1].lo + x.box[1].hi) / 2, h: x.box[1].hi - x.box[1].lo, c: color[x.s], a: alpha[x.s] })));
    for (const x of map.boxes) if (x.box[0].hi - x.box[0].lo > (a.hi - a.lo) / 60) fig.rect(x.box[0].lo, x.box[1].lo, x.box[0].hi, x.box[1].hi, { color: 'panel', alpha: 0, stroke: 'line', strokeWidth: 0.5 });
    fig.render();
  } else {
    ctx.note(`The proof covers ${map.coords} coordinates, too many to draw; ${map.boxes.length} boxes were used.`);
    return;
  }
  ctx.legend([{ label: 'proved', color: 'pos' }, { label: 'fails', color: 'neg' }, { label: 'hypothesis false', color: 'vac' }, { label: 'undecided', color: 'undef' }]);
}

/* ---------------- variations of a claim ---------------- */

function panel(card, cls, title) {
  let box = card.el.querySelector('.' + cls);
  if (box) box.remove();
  box = h('div', 'panel ' + cls);
  const head = h('div', 'trace-head');
  head.append(h('strong', null, title));
  const close = h('button', 'link-btn', 'Close');
  close.type = 'button';
  close.addEventListener('click', () => box.remove());
  head.append(close);
  box.append(head);
  card.el.append(box);
  return box;
}

async function showVariations(card, body, env, state = {}) {
  const box = panel(card, 'variations', 'Is every condition needed?');
  box.append(h('p', 'note', 'Each row changes one thing in the claim and checks the result. A version that fails shows the condition is needed; a version that still holds is a stronger statement (on these samples).'));
  const ctl = card.progress('Checking variations');
  box.append(card.body.lastElementChild);   // keep the progress line inside the panel
  box.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  let results, sharp;
  try {
    results = await MV.runSliced(MV.checkClaimVariations(body, env, { stress: state.stress }), ctl);
    sharp = await MV.runSliced(MV.sharpness(body, env), ctl);
  } catch (err) {
    ctl.done();
    box.append(h('p', err.message === 'Stopped.' ? 'note' : 'error-msg', err.message === 'Stopped.' ? 'Stopped.' : err.message));
    return;
  }
  ctl.done();
  if (sharp) {
    const p = h('p', 'sharp');
    const lim = `${nice(sharp.critical)}${sharp.form && sharp.form !== nice(sharp.critical) ? ` (≈ ${sharp.form})` : ''}`;
    const where = sharp.at.vals.length ? `, reached near ${sharp.at.vals.map(nice).join(', ')}` : '';
    p.innerHTML = `<strong>How sharp is the constant?</strong> The other side goes ${sharp.upper ? 'up to' : 'down to'} <span class="val">${esc(lim)}</span>${esc(where)}. ` +
      (sharp.holds ? `Your constant ${esc(nice(sharp.constant))} ${Math.abs(sharp.critical - sharp.constant) < 1e-9 * Math.max(1, Math.abs(sharp.constant)) ? 'is exactly the best possible' : `could be replaced by ${esc(lim)}`}.` : `Your constant ${esc(nice(sharp.constant))} is past it, so the claim fails.`);
    box.append(p);
  }
  if (!results.length) { box.append(h('p', 'note', 'This claim has no hypotheses, comparisons, quantifier pairs or ranges to vary.')); return; }
  const wrap = h('div', 'table-wrap');
  const t = h('table', 'var-table');
  const head = h('tr');
  ['What changes', 'Result', 'Simplest counterexample'].forEach(x => head.append(h('th', null, x)));
  t.append(head);
  const needed = [], notNeeded = [];
  for (const v of results) {
    const tr = h('tr');
    const what = h('td');
    what.append(h('span', 'badge', v.kind), document.createTextNode(' ' + v.label));
    tr.append(what);
    const info = v.info;
    let verdict, cls, ex = '';
    if (v.error) { verdict = 'error'; cls = 'undef'; ex = v.error; }
    else if (info.count.fail) {
      verdict = 'fails'; cls = 'fail';
      const r = info.simplest || info.res.find(x => x.s === 'fail');
      const names = info.binders.map(b => b.pattern ? `(${b.pattern.join(', ')})` : b.name);
      ex = r.vals.length ? names.map((n, i) => `${MV.idOut(n, false)} = ${nice(r.vals[i])}`).join(', ') : '—';
      needed.push(v.label);
      const td = h('td');
      const b = h('button', 'link-btn', ex);
      b.type = 'button';
      b.title = 'Show why';
      b.addEventListener('click', () => APP.showTrace(card, `Why “${v.label}” fails at ${ex}`, info.body, r.env, 1, !!(info.prepared && info.prepared.exact)));
      td.append(b);
      tr.append(h('td', `verdict ${cls}`, verdict), td);
      t.append(tr);
      continue;
    } else if (info.count.ok) { verdict = info.proved ? 'proved' : 'holds'; cls = 'ok'; notNeeded.push(v.label); }
    else { verdict = 'never tested'; cls = 'vac'; }
    tr.append(h('td', `verdict ${cls}`, verdict), h('td', 'muted', ex));
    t.append(tr);
  }
  wrap.append(t);
  box.append(wrap);
  if (needed.length || notNeeded.length) {
    box.append(h('p', 'note', `${needed.length} of ${results.length} changes break the claim${needed.length ? '' : ' — every condition could be relaxed, at least on these samples'}.`));
  }
}

/* ---------------- variations of a definition ---------------- */

async function showDefinitionVariations(card, name, fn, claim, env, base, state = {}) {
  const box = panel(card, 'variations', `What if the definition of ${name} were different?`);
  box.append(h('p', 'note', 'Each row changes one thing in the definition and lists the examples whose answer changes. That shows what each part of the definition is for.'));
  const variants = MV.definitionVariations(fn);
  if (!variants.length) { box.append(h('p', 'note', 'Nothing in this definition can be varied automatically.')); return; }
  const key = r => r.vals.map(v => (v && v.label) || fmt(v)).join(' | ');
  const before = new Map(base.res.map(r => [key(r), r.s]));
  const ctl = card.progress('Checking variations');
  box.append(card.body.lastElementChild);
  box.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  const wrap = h('div', 'table-wrap');
  const t = h('table', 'var-table');
  const head = h('tr');
  ['What changes', 'Now true for', 'Now false for'].forEach(x => head.append(h('th', null, x)));
  t.append(head);
  wrap.append(t);
  box.append(wrap);
  try {
    for (let i = 0; i < variants.length; i++) {
      const v = variants[i];
      const vclaim = MV.replaceNode(claim, claim.body.f, { type: 'value', v: v.fn, label: name });
      let info;
      try { info = await MV.runSliced(MV.analyzeSteps(vclaim, env, { search: false, stress: state.stress, budget: 6000 }), ctl); }
      catch (err) { if (err.message === 'Stopped.') throw err; const tr = h('tr'); tr.append(h('td', null, v.label), h('td', 'error-msg', err.message), h('td')); t.append(tr); continue; }
      ctl.onProgress({ phase: 'variations', done: i + 1, total: variants.length });
      const gained = [], lost = [];
      for (const r of info.res) {
        const was = before.get(key(r));
        if (was === undefined) continue;
        if (r.s === 'ok' && was !== 'ok') gained.push(key(r));
        if (r.s !== 'ok' && was === 'ok') lost.push(key(r));
      }
      const tr = h('tr');
      const what = h('td');
      what.append(h('span', 'badge', v.kind), document.createTextNode(' ' + v.label));
      const cell = (list, cls) => { const td = h('td', list.length ? cls : 'muted', list.length ? list.slice(0, 6).join('; ') + (list.length > 6 ? ` and ${list.length - 6} more` : '') : 'no change'); return td; };
      tr.append(what, cell(gained, 'gained'), cell(lost, 'lost'));
      t.append(tr);
    }
  } catch (err) {
    box.append(h('p', 'note', err.message === 'Stopped.' ? 'Stopped.' : err.message));
  } finally { ctl.done(); }
}

function renderClaim(card, info, opts = {}) {
  const { k, kind, res, count: c, binders } = info;
  const ctx = makeCtx(card);
  const unit = info.exhaustive ? 'cases' : 'samples';
  const tested = c.ok + c.fail;
  const varNames = binders.map(b => b.pattern ? `(${b.pattern.map(nameOf).join(', ')})` : nameOf(b.name));
  const L = kind === 'cmp' ? ppText(info.concl.args[0]) : '', R = kind === 'cmp' ? ppText(info.concl.args[1]) : '';
  const wName = info.W ? (info.W.b.pattern ? `(${info.W.b.pattern.map(nameOf).join(', ')})` : nameOf(info.W.name)) : '';
  const wWord = info.wInteger ? 'smallest' : 'largest';
  const ex = opts.examples;
  const legendTail = [];
  if (c.fail) legendTail.push({ label: ex ? 'does not satisfy it' : kind === 'witness' ? `no ${wName} found` : 'fails', color: 'neg' });
  if (c.vac) legendTail.push({ label: 'hypothesis false', color: 'vac' });
  if (c.undef) legendTail.push({ label: 'undefined', color: 'undef' });
  const why = r => {
    const at = r.vals.length ? ' at ' + varNames.map((n, i) => `${n} = ${short(r.vals[i])}`).join(', ') : '';
    const verdict = r.s === 'ok' ? (ex ? 'satisfies' : 'holds') : r.s === 'fail' ? (ex ? 'does not satisfy' : 'fails') : r.s === 'vac' ? 'holds vacuously' : 'is undefined';
    APP.showTrace(card, ex ? `Why it ${verdict} ${ex}${at}` : `Why it ${verdict}${at}`, info.body, r.env, 1, !!(info.prepared && info.prepared.exact));
  };

  // A claim of a shape sampling answers wrongly (src/cautions.js) doesn't get a plain "holds".
  const cautions = !ex && c.ok && !c.fail && !info.proved && info.prepared && MV.claimCautions ? MV.claimCautions(info.prepared) : [];
  // A failure that may only be the limit of a finite check (src/cautions.js).
  const failCautions = !ex && c.fail && MV.failCautions ? MV.failCautions(info) : [];
  if (ex) card.setStatus('info', `${count(c.ok)} of ${count(c.ok + c.fail + c.undef)} examples satisfy ${ex}`);
  else if (c.fail && failCautions.length) card.setStatus('info', `Fails on ${count(c.fail)} of ${count(tested)} ${unit}, but maybe only where a finite check gives up`);
  else if (cautions.length) card.setStatus('info', `${k === 0 ? 'Holds' : `Holds on the ${count(tested)} ${unit}`}, but sampling can't decide a claim of this shape`);
  else if (c.fail) card.setStatus('fail', k === 0 ? 'Fails' : `Fails on ${count(c.fail)} of ${count(tested)} ${unit}`);
  else if (c.ok) card.setStatus('ok', info.proved && info.algebra ? (info.algebra.kind === 'inequality' ? 'Proved exactly' : 'Proved by algebra') : k === 0 ? 'Holds' : info.proved ? `Proved: all ${count(tested)} cases checked exactly` : info.exhaustive ? `Holds in all ${count(tested)} cases` : `Holds on all ${count(tested)} samples`);
  else if (c.vac) card.setStatus('info', 'Never tested: the hypothesis is false on every sample');
  else card.setStatus('undef', 'Undefined on every sample');

  for (const r of res) {
    const parts = r.vals.map(flat);
    r.c = parts.every(Boolean) ? parts.flat() : null;
  }
  const coordNames = [];
  binders.forEach((b, i) => {
    const v = res.length ? res[0].vals[i] : null;
    if (b.pattern) coordNames.push(...b.pattern.map(nameOf));
    else if (isNumArr(v)) v.forEach((_, j) => coordNames.push(`${nameOf(b.name)}${'₀₁₂₃₄₅₆₇₈₉'[j + 1] || '[' + (j + 1) + ']'}`));
    else coordNames.push(nameOf(b.name));
  });
  const C = res.length && res.every(r => r.c) ? res[0].c.length : 0;
  const objects = i => res.length > 0 && res.some(r => isObject(r.vals[i]));
  const distinct = i => new Set(res.map(r => r.vals[i])).size;
  // Variables that take a single value (a in {−1}) are not dimensions of the picture.
  const varying = binders.map((_, i) => i).filter(i => distinct(i) > 1);
  const fixedNote = () => {
    const fixed = binders.map((_, i) => i).filter(i => !varying.includes(i) && res.length);
    if (fixed.length) ctx.note(`With ${fixed.map(i => `${varNames[i]} = ${short(res[0].vals[i])}`).join(', ')}.`);
  };
  let shownTable = false;

  if (k === 0) {
    const r = res[0];
    if (kind === 'cmp') ctx.note(`Left side: ${fmt(r.L)}. Right side: ${fmt(r.R)}.`);
    if (kind === 'witness') {
      ctx.note(r.w !== undefined ? `Witness: ${wName} = ${short(r.w)} (the ${wWord} that works among the candidates tried).`
        : `No ${wName} in ${r.wdom.describe()} works among the candidates tried.`);
    }
    if (r.s === 'fail') why(r);
    else {
      const b = card.action('Why?', () => why(r), 'Show how the claim evaluates');
      b.classList.add('why');
    }
  } else if (info.exhaustive && varying.length <= 1 && binders.some((_, i) => objects(i))) {
    fixedNote();
    renderGallery(card, info, opts, why, varying.length ? varying[0] : binders.findIndex((_, i) => objects(i)));
    shownTable = true;
  } else if (info.exhaustive && varying.length === 2 && varying.some(objects) && varying.every(i => distinct(i) <= 24)) {
    fixedNote();
    renderMatrix(card, info, varNames, opts, why, varying[0], varying[1]);
    shownTable = true;
  } else if (res.length && res[0].vals.some(v => typeof v === 'function' && v.isSequence)) {
    renderSequences(ctx, info, res[0].vals.findIndex(v => typeof v === 'function' && v.isSequence), legendTail);
  } else if (C === 1) {
    renderLine(ctx, info, coordNames, L, R, wName, wWord, legendTail, opts);
  } else if (C === 2) {
    renderPlane(ctx, info, coordNames, wName, wWord, legendTail, opts);
  } else if (C === 3) {
    render3D(ctx, info, coordNames, legendTail);
    if (kind === 'cmp' && res.every(r => r.L === undefined || (typeof r.L === 'number' && typeof r.R === 'number'))) renderScatter(ctx, info, L, R);
  } else if (C >= 3 && kind === 'cmp' && res.every(r => r.L === undefined || (typeof r.L === 'number' && typeof r.R === 'number'))) {
    renderScatter(ctx, info, L, R);
  }

  if (!ex) {
    if (kind === 'cmp' && ['<', '<=', '>', '>='].includes(info.op) && c.ok && !c.fail && k > 0) {
      const tight = res.filter(r => r.s === 'ok' && typeof r.m === 'number').sort((a, b) => a.m - b.m)[0];
      if (tight) ctx.note(`Closest to failing: ${varNames.map((n, i) => `${n} = ${short(tight.vals[i])}`).join(', ')}, where the left side is ${short(tight.L)} and the right side is ${short(tight.R)}.`);
    }
    if (c.vac) ctx.note(`${c.vac === 1 ? `1 ${unit.slice(0, -1)}` : `${count(c.vac)} ${unit}`} where ${ppText(info.hyp)} is false ${c.vac === 1 ? "holds" : "hold"} vacuously and ${c.vac === 1 ? "is" : "are"} shown separately.`);
    if (c.undef) ctx.note(c.undef === 1 ? `1 ${unit.slice(0, -1)} was undefined, for example a division by zero or the square root of a negative number.` : `${count(c.undef)} ${unit} were undefined, for example a division by zero or the square root of a negative number.`);
  }
  if (info.simplest && !ex && k > 0) {
    const r = info.simplest;
    const p = h('p', 'simplest');
    p.append(h('strong', null, r.found === 'search' ? 'Counterexample found by a targeted search: ' : 'Simplest counterexample: '));
    const b = h('button', 'link-btn', varNames.map((n, i) => `${n} = ${nice(r.vals[i])}`).join(', '));
    b.type = 'button';
    b.title = 'Show why';
    b.addEventListener('click', () => why(r));
    p.append(b);
    if (kind === 'cmp' && typeof r.L === 'number') p.append(document.createTextNode(` (left side ${nice(r.L)}, right side ${nice(r.R)})`));
    card.body.append(p);
  }
  if (info.searched && !info.searched.found && info.searched.best && !ex) {
    const b = info.searched.best;
    ctx.note(`A targeted search (${count(info.searched.evals)} evaluations, pushing toward failure) found no counterexample either. ` +
      (info.op === '=' ? '' : b.m < 1e-6 * Math.max(1, Math.abs(b.L)) ? `It is tight: equality at ${varNames.map((n, i) => `${n} = ${nice(b.vals[i])}`).join(', ')}.` : `The closest it came: a margin of ${short(b.m)} at ${varNames.map((n, i) => `${n} = ${short(b.vals[i])}`).join(', ')}.`));
  }
  if (info.stress) ctx.note('Checked with the wilder example catalogs.', 'caveat');
  if (info.restricted) ctx.note('Sampled only inside the zoomed view.', 'caveat');
  if (info.stopped) ctx.note(`Stopped after ${count(res.length)} of ${count(info.total)} samples to keep the page responsive.`);

  const fails = res.filter(r => r.s === 'fail');
  if (fails.length > 1 && k > 0 && !shownTable) {
    if (fails.every(r => typeof r.m === 'number')) fails.sort((a, b) => a.m - b.m);
    const shown = fails.slice(0, 6);
    const rows = shown.map(r => [
      ...r.vals.map(short),
      ...(kind === 'cmp' ? [short(r.L), short(r.R)] : kind === 'witness' ? [`none in ${r.wdom.describe()}`] : []),
    ]);
    const headers = [...varNames, ...(kind === 'cmp' ? ['left side', 'right side'] : kind === 'witness' ? [wName] : [])];
    const sortedNote = fails.every(r => typeof r.m === 'number') ? ', worst first' : '';
    ctx.table(headers, rows, `Counterexamples: ${rows.length} of ${count(fails.length)}${sortedNote} · click one to see why`, i => why(shown[i]));
  }
  // Exact algebra: both sides simplified, and why it is (or isn't quite) a proof.
  if (!ex && info.algebra && info.algebra.identity) {
    const a = info.algebra, sides = a.sides ? `Both sides simplify to ${a.sides[0]}.` : 'Both sides simplify to the same expression.';
    ctx.note(a.note ? a.note : a.proved ? `Proved by algebra: ${sides} This holds for every value, not just the samples.`
      : !a.condsOk ? `${sides} That is an identity wherever every sum has a range of length ≥ 0 (its upper end at least its lower end − 1), which the ranges given don't guarantee, so the samples decide.`
      : `${sides} That is an identity wherever ${a.denoms.map(d => d + ' ≠ 0').join(' and ')}, so the samples decide the rest.`, a.proved ? 'algebra' : 'caveat');
  }
  for (const w of cautions) ctx.note(`Sampling can't decide this. ${w.text}`, 'caveat caution');
  for (const w of failCautions) ctx.note(w.text, 'caveat caution');
  if (!ex && c.ok && !c.fail && !info.proved && !cautions.length) ctx.note(info.exhaustive ? 'Every case was checked, but some parts were sampled or estimated, so this is strong evidence rather than a proof.' : 'This is evidence from sampling, not a proof.', 'caveat');
  for (const f of card.figs) f.render();
}

/* One object variable over a finite catalog: a tile per object, colored by result. */
function renderGallery(card, info, opts, why, vi = 0) {
  const grid = h('div', 'gallery');
  // A long list of models (all 3341 operations on 3 elements): failures first, then a spread of the rest.
  const MAX = 150;
  let shown = info.res;
  if (shown.length > MAX) {
    const fails = shown.filter(r => r.s === 'fail').slice(0, MAX / 2);
    const rest = shown.filter(r => r.s !== 'fail');
    const step = rest.length / (MAX - fails.length);
    shown = [...fails, ...Array.from({ length: Math.min(rest.length, MAX - fails.length) }, (_, i) => rest[Math.floor(i * step)])];
  }
  for (const r of shown) {
    const tile = h('button', `tile ${r.s}`);
    tile.type = 'button';
    tile.title = 'Show why';
    const th = h('div', 'thumb');
    tile.append(th);
    if (!thumb(card, th, r.vals[vi])) th.remove();
    const word = r.s === 'ok' ? (opts.examples ? '✓ satisfies' : '✓ holds') : r.s === 'fail' ? (opts.examples ? '✗ does not' : '✗ fails') : r.s === 'vac' ? '– hypothesis false' : '? undefined';
    // A named object with a picture needs only its name.
    const v = r.vals[vi], named = v && v.label && th.isConnected;
    tile.append(h('span', 'tile-label', named ? v.label : fmt(v)), h('span', 'tile-status', word));
    tile.addEventListener('click', () => why(r));
    grid.append(tile);
  }
  card.body.append(grid);
  card.body.append(h('p', 'note', (shown.length < info.res.length ? `Showing ${shown.length} of ${info.res.length}: the failures first, then a spread of the rest. ` : '') + 'Click an example to see how it evaluates.'));
}

/* Two variables over small catalogs: a table with one row per value of the first and one column per value of the second. */
function renderMatrix(card, info, allNames, opts, why, vi = 0, vj = 1) {
  const names = [allNames[vi], allNames[vj]];
  const rowsV = [...new Set(info.res.map(r => r.vals[vi]))], colsV = [...new Set(info.res.map(r => r.vals[vj]))];
  const at = new Map(info.res.map(r => [rowsV.indexOf(r.vals[vi]) + ',' + colsV.indexOf(r.vals[vj]), r]));
  const wrap = h('div', 'table-wrap');
  const t = h('table', 'matrix');
  const head = h('tr');
  head.append(h('th', 'corner', `${names[0]} ↓   ${names[1]} →`));
  colsV.forEach(v => head.append(h('th', null, short(v))));
  t.append(head);
  rowsV.forEach((rv, i) => {
    const tr = h('tr');
    tr.append(h('th', null, short(rv)));
    colsV.forEach((cv, j) => {
      const r = at.get(i + ',' + j);
      const td = h('td', r ? `cell ${r.s}` : 'cell', r ? (r.s === 'ok' ? '✓' : r.s === 'fail' ? '✗' : r.s === 'vac' ? '–' : '?') : '');
      if (r) {
        td.tabIndex = 0;
        td.title = `${names[0]} = ${short(rv)}, ${names[1]} = ${short(cv)}: show why`;
        td.addEventListener('click', () => why(r));
        td.addEventListener('keydown', ev => { if (ev.key === 'Enter') why(r); });
      }
      tr.append(td);
    });
    t.append(tr);
  });
  wrap.append(t);
  card.body.append(wrap);
  const ctx = makeCtx(card);
  const legend = [{ label: opts.examples ? 'satisfies it' : 'holds', color: 'pos' }, { label: opts.examples ? 'does not' : 'fails', color: 'neg' }];
  if (info.count.vac) legend.push({ label: 'hypothesis false', color: 'vac' });
  ctx.legend(legend);
  card.body.append(h('p', 'note', 'Click a cell to see how it evaluates.'));
}

/* One coordinate: both sides (or the witness) against the variable, failing stretches shaded. */
function renderLine(ctx, info, names, L, R, wName, wWord, legendTail, opts) {
  const { res, kind } = info;
  const sorted = res.slice().sort((a, b) => a.c[0] - b.c[0]);
  const xs = sorted.map(r => r.c[0]);
  const discrete = !!(info.dom0 && info.dom0.integer) || (xs.every(Number.isInteger) && xs.length < 400 && info.exhaustive);
  const [x0, x1] = minmax(xs);
  const xr = discrete ? [x0 - 0.5, x1 + 0.5] : [x0, x1];
  const cmpNumeric = kind === 'cmp' && sorted.some(r => typeof r.L === 'number') && sorted.every(r => (r.L === undefined || typeof r.L === 'number') && (r.R === undefined || typeof r.R === 'number'));
  const wNumeric = kind === 'witness' && sorted.every(r => r.w === undefined || typeof r.w === 'number') && sorted.some(r => r.w !== undefined);
  const resample = info.k === 1 && opts.resample ? v => opts.resample([v[0]]) : null;
  const legend = [];
  if (cmpNumeric || wNumeric) {
    const fig = ctx.figure({ x: xr, xlabel: names[0], ylabel: wNumeric ? wName : undefined, onResample: resample });
    statusBands(fig, sorted, discrete, { fail: { color: 'neg', alpha: 0.16 }, vac: { color: 'vac', alpha: 0.18 }, undef: { color: 'undef', alpha: 0.16 } });
    const draw = (pts, color) => discrete ? fig.points(pts, { color, r: xs.length > 120 ? 2 : 3 }) : fig.curve(pts, { color });
    if (cmpNumeric) {
      // Sides that agree everywhere would hide each other: the left drawn wide and pale, the right dashed on top.
      const both = sorted.filter(r => typeof r.L === 'number' && typeof r.R === 'number');
      const same = both.length > 1 && both.every(r => Math.abs(r.L - r.R) <= 1e-9 * Math.max(1, Math.abs(r.L), Math.abs(r.R)));
      const Lpts = sorted.map(r => typeof r.L === 'number' ? [r.c[0], r.L] : null), Rpts = sorted.map(r => typeof r.R === 'number' ? [r.c[0], r.R] : null);
      if (same && !discrete) {
        fig.curve(Lpts, { color: 'c1', width: 6, alpha: 0.35 });
        fig.curve(Rpts, { color: 'c2', width: 2, dash: [6, 4] });
      } else { draw(Lpts, 'c1'); draw(Rpts, 'c2'); }
      legend.push({ label: `left side: ${L}`, color: 'c1' }, { label: `right side: ${R}`, color: 'c2' });
      if (same) legend.push({ label: 'the two sides coincide at every sample, so the lines lie on top of each other', color: 'muted' });
    } else {
      draw(sorted.map(r => r.w !== undefined ? [r.c[0], r.w] : null), 'accent');
      legend.push({ label: `${wWord} ${wName} found`, color: 'accent' });
    }
  } else {
    const fig = ctx.figure({ x: xr, y: [0, 1], height: 86, yAxis: false, xlabel: names[0], onResample: resample });
    statusBands(fig, sorted, discrete, { ok: { color: 'pos', alpha: 0.4 }, fail: { color: 'neg', alpha: 0.75 }, vac: { color: 'vac', alpha: 0.35 }, undef: { color: 'undef', alpha: 0.5 } });
    if (info.count.ok) legend.push({ label: 'holds', color: 'pos' });
  }
  ctx.legend([...legend, ...legendTail]);
}

/* Two coordinates: cells for grid samples, otherwise points over the set they come from. */
function renderPlane(ctx, info, names, wName, wWord, legendTail, opts) {
  const { res, kind } = info;
  const xu = uniqSorted(res.map(r => r.c[0])), yu = uniqSorted(res.map(r => r.c[1]));
  const isGrid = xu.length * yu.length <= res.length * 1.05 && xu.length > 2 && yu.length > 2;
  const margins = res.filter(r => r.s === 'ok' && typeof r.m === 'number').map(r => r.m).sort((a, b) => a - b);
  const p90 = margins.length ? margins[Math.floor(margins.length * 0.9)] : 0;
  const alpha = r => r.s === 'ok' ? (p90 > 0 && typeof r.m === 'number' ? 0.16 + 0.74 * Math.min(1, Math.max(0, r.m) / p90) : 0.6)
    : r.s === 'fail' ? 0.85 : r.s === 'vac' ? 0.28 : 0.6;
  const resample = (info.k === 1 || info.k === 2) && opts.resample ? v => opts.resample(v) : null;
  const legend = [];
  if (isGrid) {
    const spans = u => {
      const g = medianGap(u), m = new Map();
      u.forEach((v, i) => m.set(v, [i ? (u[i - 1] + v) / 2 : v - g / 2, i < u.length - 1 ? (v + u[i + 1]) / 2 : v + g / 2]));
      return m;
    };
    const xs = spans(xu), ys = spans(yu);
    const fig = ctx.figure({ x: [xs.get(xu[0])[0], xs.get(xu[xu.length - 1])[1]], y: [ys.get(yu[0])[0], ys.get(yu[yu.length - 1])[1]], xlabel: names[0], ylabel: names[1], onResample: resample });
    fig.cells(res.map(r => {
      const [a, b] = xs.get(r.c[0]), [cc, d] = ys.get(r.c[1]);
      return { x: (a + b) / 2, w: b - a, y: (cc + d) / 2, h: d - cc, c: STATUS_COLOR[r.s], a: alpha(r) };
    }));
    legend.push({ label: p90 > 0 ? 'holds (darker means more slack)' : 'holds', color: 'pos' });
  } else {
    const D = info.dom0;
    const fromSet = D && (D.kind === 'set' || D.kind === 'ball') && D.dim === 2;
    let win = fromSet && D.window ? D.window() : null;
    if (!win || !Array.isArray(win[0]) || win.some(([a, b]) => !(b > a) || b - a > 30)) {
      const [a, b] = minmax(res.map(r => r.c[0])), [cc, d] = minmax(res.map(r => r.c[1]));
      const pad = Math.max(b - a, d - cc) * 0.08 || 1;
      win = [[a - pad, b + pad], [cc - pad, d + pad]];
    }
    const fig = ctx.figure({ x: win[0], y: win[1], square: true, xlabel: names[0], ylabel: names[1], onResample: resample });
    if (fromSet) { fig.region(D, { color: 'c1', alpha: 0.13 }); legend.push({ label: D.describe(), color: 'c1' }); }
    // For "∃ε" claims, draw the ball of the witness radius around a spread of points.
    const balls = kind === 'witness' && !info.wInteger && res.some(r => typeof r.w === 'number');
    if (balls) {
      const okPts = res.filter(r => r.s === 'ok' && typeof r.w === 'number');
      const span = win[0][1] - win[0][0];
      for (const r of stride(okPts, 40)) if (r.w < span) fig.circle(r.c[0], r.c[1], r.w, { color: 'pos', width: 1, alpha: 0.5 });
      legend.push({ label: `${wName}-balls: the ${wWord} ${wName} found at a point`, color: 'pos', ring: true });
    }
    for (const s of ['vac', 'undef', 'ok', 'fail']) {
      const pts = res.filter(r => r.s === s).map(r => r.c);
      if (pts.length) fig.points(pts, { color: STATUS_COLOR[s], r: s === 'fail' ? 3.2 : 2.1, alpha: s === 'ok' ? 0.8 : s === 'vac' ? 0.5 : 1 });
    }
    legend.push({ label: 'holds', color: 'pos' });
  }
  ctx.legend([...legend, ...legendTail]);
}

/* Three coordinates: every sample as a dot in space, colored by its result. */
function render3D(ctx, info, names, legendTail) {
  const pts = info.res.filter(r => r.c && r.c.every(Number.isFinite)).map(r => { const p = r.c.slice(); p.color = STATUS_COLOR[r.s]; return p; });
  if (!pts.length) return;
  // Failures last, so they are drawn bigger on top of the rest.
  const fig = ctx.figure3d({ labels: names, equal: true });
  fig.points(pts.filter(p => p.color !== 'neg'), { r: 2, alpha: 0.55 });
  fig.points(pts.filter(p => p.color === 'neg'), { r: 3.4, alpha: 1 });
  ctx.legend([{ label: 'holds', color: 'pos' }, ...(legendTail || [])]);
}

function renderScatter(ctx, info, L, R) {
  const { res } = info;
  const pts = res.filter(r => typeof r.L === 'number' && Number.isFinite(r.L) && Number.isFinite(r.R));
  if (!pts.length) return;
  const [lo, hi] = minmax(pts.flatMap(r => [r.L, r.R]));
  const pad = (hi - lo) * 0.04 || 1, a = lo - pad, b = hi + pad;
  const fig = ctx.figure({ x: [a, b], y: [a, b], square: true, xlabel: 'left', ylabel: 'right' });
  const op = info.op;
  if (op === '<' || op === '<=') fig.poly([[a, a], [b, b], [a, b]], { color: 'pos', alpha: 0.08 });
  else if (op === '>' || op === '>=') fig.poly([[a, a], [b, a], [b, b]], { color: 'pos', alpha: 0.08 });
  fig.seg(a, a, b, b, { color: 'muted', width: 1, dash: [5, 4] });
  fig.points(pts.filter(r => r.s === 'ok').map(r => [r.L, r.R]), { color: 'pos', r: 1.8, alpha: 0.55 });
  fig.points(pts.filter(r => r.s === 'fail').map(r => [r.L, r.R]), { color: 'neg', r: 3 });
  ctx.legend([{ label: 'the claim holds in the shaded half', color: 'pos' }, ...(info.count.fail ? [{ label: 'counterexamples', color: 'neg' }] : [])]);
  ctx.note(`Each dot is one random sample. Horizontal: the left side, ${L}. Vertical: the right side, ${R}.`);
}

/* Claims about sampled sequences: a gallery of them, colored by result. */
function renderSequences(ctx, info, idx, legendTail) {
  const { res } = info;
  const pick = [...res.filter(r => r.s === 'ok').slice(0, 10), ...res.filter(r => r.s === 'vac').slice(0, 3), ...res.filter(r => r.s === 'fail').slice(0, 6)];
  if (!pick.length) return;
  const style = r => ({ color: STATUS_COLOR[r.s], width: r.s === 'fail' ? 2 : 1.2, alpha: r.s === 'fail' ? 1 : r.s === 'ok' ? 0.45 : 0.5 });
  const t1 = (() => { try { return pick[0].vals[idx](1); } catch (e) { return null; } })();
  const legend = [];
  if (typeof t1 === 'number') {
    const N = 40;
    const fig = ctx.figure({ x: [0.5, N + 4], xlabel: 'n' });
    for (const r of pick) {
      const s = r.vals[idx], st = style(r);
      const pts = [];
      for (let n = 1; n <= N; n++) { let v; try { v = s(n); } catch (e) { v = NaN; } pts.push(typeof v === 'number' && Number.isFinite(v) ? [n, v] : null); }
      fig.curve(pts, { ...st, width: st.width * 0.8 });
      fig.points(pts.filter(Boolean), { color: st.color, r: r.s === 'fail' ? 2.2 : 1.4, alpha: st.alpha });
      if (typeof s.limit === 'number') {
        fig.seg(N, s.limit, N + 2.6, s.limit, { color: st.color, width: 1, dash: [3, 3], alpha: st.alpha });
        fig.points([[N + 2.6, s.limit]], { color: st.color, r: r.s === 'fail' ? 4 : 3, alpha: st.alpha });
      }
    }
    legend.push({ label: 'satisfies the claim', color: 'pos' });
    ctx.legend([...legend, ...legendTail]);
    ctx.note(`Each line is one sampled sequence, n = 1 to ${N}. The dots at the right edge mark their limits.`);
  } else if (isNumArr(t1) && t1.length === 2) {
    const D = info.dom0, X = D && D.of;
    const planar = X && X.dim === 2 && X.window;
    let win = planar ? X.window() : null;
    const paths = pick.map(r => {
      const s = r.vals[idx], pts = [];
      for (let n = 1; n <= 60; n++) { try { const v = s(n); if (isNumArr(v)) pts.push(v); } catch (e) { /* skip */ } }
      return { r, s, pts };
    });
    if (!win || !Array.isArray(win[0]) || win.some(([a, b]) => b - a > 30)) {
      const all = paths.flatMap(p => p.pts);
      const [a, b] = minmax(all.map(p => p[0])), [cc, d] = minmax(all.map(p => p[1]));
      const pad = Math.max(b - a, d - cc) * 0.08 || 1;
      win = [[a - pad, b + pad], [cc - pad, d + pad]];
    }
    const fig = ctx.figure({ x: win[0], y: win[1], square: true });
    if (planar && (X.kind === 'set' || X.kind === 'ball')) { fig.region(X, { color: 'c1', alpha: 0.13 }); legend.push({ label: X.describe(), color: 'c1' }); }
    const ring = (win[0][1] - win[0][0]) * 0.018;
    for (const { r, s, pts } of paths) {
      const st = style(r);
      fig.curve(pts, { ...st, width: st.width * 0.7 });
      fig.points(pts, { color: st.color, r: r.s === 'fail' ? 2 : 1.3, alpha: st.alpha });
      if (isNumArr(s.limit)) fig.circle(s.limit[0], s.limit[1], ring, { color: st.color, width: r.s === 'fail' ? 2.2 : 1.2, alpha: st.alpha });
    }
    legend.push({ label: 'satisfies the claim', color: 'pos' }, { label: 'limit of a sequence', color: 'muted', ring: true });
    ctx.legend([...legend, ...legendTail]);
    ctx.note('Each path is one sampled sequence, n = 1 to 60; rings mark limits. Counterexamples are drawn bold. Zoom in to follow a path to its limit.');
  } else if (typeof t1 === 'function') {
    const r = res.find(x => x.s === 'fail') || pick[pick.length - 1];
    const A = r.vals[idx];
    const ks = [1, 2, 3, 5, 8, 13, 21, 34], N = 30;
    const fig = ctx.figure({ x: [0.5, N + 0.5], xlabel: 'n' });
    ks.forEach((kk, j) => {
      const pts = [];
      for (let n = 1; n <= N; n++) { let v; try { v = A(kk)(n); } catch (e) { v = NaN; } pts.push(typeof v === 'number' && Number.isFinite(v) ? [n, v] : null); }
      fig.curve(pts, { color: STATUS_COLOR[r.s], width: 1.3, alpha: 0.2 + 0.8 * j / (ks.length - 1) });
    });
    if (typeof A.limit === 'function') {
      const pts = [];
      for (let n = 1; n <= N; n++) { try { pts.push([n, A.limit(n)]); } catch (e) { pts.push(null); } }
      fig.curve(pts, { color: 'ink', width: 1.6, dash: [5, 4] });
    }
    ctx.legend([{ label: `A(k) for k = ${ks.join(', ')}, lighter to darker`, color: STATUS_COLOR[r.s] }, { label: 'lim A', color: 'ink' }]);
    ctx.note(`One sampled sequence of sequences${r.s === 'fail' ? ' (a counterexample)' : ''}: ${fmt(A)}. Each curve is one A(k), drawn for n = 1 to ${N}.`);
  }
}

/* ---------------- explain ---------------- */

/* Documentation of a name: a definition's own comment, or a library's documentation. */
function docFor(name, env) {
  const v = env && env[name];
  if (v && v.doc) return v.doc;
  for (const lib of MV.REG.values()) if (lib.docs && lib.docs[name]) return lib.docs[name];
  return '';
}

const R2 = () => MV.product([MV.Runiverse(), MV.Runiverse()]);

/* Default examples for a parameter, from its type. */
function defaultExamples(typeNode, env, numericSlot, numericCount) {
  if (!typeNode) return null;
  let D;
  try { D = compileDomain(typeNode)(env); } catch (e) { return null; }
  const call = (name, ...args) => { const f = env[name]; return f ? MV.toDomain(f(...args)) : null; };
  if (D === MV.SetType) return call('Subsets', R2());
  if (D === MV.FunType) return call('Functions');
  if (D.kind === 'structure') { const xs = D.structure.instances(); return xs.length ? MV.finite(xs, { label: `example ${D.structure.name}s` }) : null; }
  if (D.kind === 'seq') { const cat = call('Sequences'); return cat ? MV.finite(cat.values.filter(s => D.contains(s)), { label: 'example sequences' }) : null; }
  if (D.kind === 'finite') return D.values.length <= 30 ? D : MV.finite(stride(D.values, 12));
  if (D.scalar) {
    const pool = numericCount === 1 ? [-1, 0, 1] : [[-1], [1], [1], [2]][Math.min(numericSlot, 3)];
    const vals = pool.filter(x => D.contains(x));
    return MV.finite(vals.length ? vals : D.sample(5));
  }
  if (D.dim === 2) {
    const vals = [[0, 0], [1, 0], [0.5, 0.5]].filter(p => D.contains(p));
    return MV.finite(vals.length ? vals : D.sample(5));
  }
  return MV.finite(D.sample(8));
}

function signature(name, d) {
  return `${MV.idOut(name, true, true)}(${d.params.map((p, i) => MV.idOut(p, true) + (d.types[i] ? ': ' + MV.ppDom(d.types[i], true) : '')).join(', ')})`;
}

function usesOf(node, env, exclude) {
  const out = [];
  for (const name of MV.freeNames(node).keys()) {
    if (exclude.has(name)) continue;
    const v = env[name];
    if ((typeof v === 'function' && (MV.DEFS.get(v) || docFor(name, env))) || (v && v.__claim) || (v && v.__domain && docFor(name, env))) out.push(name);
  }
  return out;
}

function addExtra(card, node, env, exclude) {
  const det = h('details', 'explain-read');
  det.open = true;
  det.append(h('summary', null, 'Read it'));
  const div = h('div');
  div.innerHTML = reading(node);
  det.append(div);
  card.extra.append(det);
  const uses = usesOf(node, env, exclude);
  if (uses.length) {
    const p = h('p', 'uses');
    p.append(h('span', 'uses-label', 'Uses'));
    for (const name of uses) {
      const b = h('button', 'chip-btn', name);
      b.type = 'button';
      b.title = docFor(name, env) || `Explain ${name}`;
      b.addEventListener('click', () => APP.preview(`explain ${name}`));
      p.append(b);
    }
    card.extra.append(p);
  }
}

async function runExplain(ast, env, card, opts = {}) {
  checkNames({ type: 'id', name: ast.name, pos: ast.pos }, env);
  let v = env[ast.name];
  const C = MV.CONCEPTS.get(ast.name);
  if (C && C.fn === v) return APP.runConcept(C, env, card, ast.binders);
  // A set named by its constructor (Famous, Subsets, CantorSet): explain the set it makes.
  if (typeof v === 'function' && v.domainCtor) { try { v = MV.toDomain(v); } catch (e) { /* needs arguments */ } }
  const d = MV.DEFS.get(v);
  if (d) return explainDefinition(ast, env, card, v, d, opts);
  if (structureOf(v)) return explainStructure(ast, env, card, structureOf(v));
  if (v && v.__claim) {
    card.formula(`<span class="fkw">${v.kind}</span> <span class="up">${esc(v.name)}</span>: ${pp(v.body)}`);
    addExtra(card, v.body, v.env, new Set());
    return runClaim({ type: 'id', name: ast.name }, env, card);
  }
  const doc = docFor(ast.name, env);
  card.formula(`<span class="up">${esc(ast.name)}</span>${v && v.__domain && v.describe() !== ast.name ? ` = ${esc(v.describe())}` : ''}`);
  if (doc) card.doc(doc);
  const ctx = makeCtx(card);
  if (v && v.__domain) {
    if (v.kind === 'finite' && v.values.some(x => isObject(x))) {
      const grid = h('div', 'gallery');
      for (const x of v.values) {
        const tile = h('div', 'tile plain');
        const th = h('div', 'thumb');
        tile.append(th, h('span', 'tile-label', fmt(x)));
        if (!thumb(card, th, x)) th.remove();
        grid.append(tile);
      }
      card.body.append(grid);
    } else if (v.dim === 3) {
      // Uniform points of the window that lie in the set, so the cloud shows its shape evenly.
      let ps = [];
      const w = v.window && v.window();
      if (w && w.length === 3) {
        for (let t = 0; t < 40000 && ps.length < 3000; t++) {
          const p = w.map(([a, b]) => a + (b - a) * Math.random());
          try { if (v.contains(p)) ps.push(p); } catch (e) { /* skip */ }
        }
      }
      if (ps.length < 200) ps = v.sample(2500).filter(p => isNumArr(p) && p.length === 3);
      const fig = ctx.figure3d({});
      fig.points(ps, { color: 'c1', r: 1.8, alpha: 0.6 });
      ctx.note(`${ps.length} points of the set, sampled. Drag to turn it.`);
    } else if (v.dim === 2 || (v.dim === 1 && v.scalar)) {
      ctx.figure(v.dim === 2 ? { square: true } : { y: [0, 1], height: 70, yAxis: false }).region(v, { color: 'c1', alpha: 0.5 });
    } else ctx.note(`Some elements: ${v.sample(6).map(fmt).join(', ')}.`);
  } else if (typeof v === 'function' && !v.domainCtor) {
    let numeric = false;
    try { numeric = typeof v(0.5) === 'number'; } catch (e) { /* not a function of one number */ }
    if (numeric) ctx.figure({ x: [-4, 4], xlabel: 'x' }).curve(x => v(x), { color: 'c1' });
    else if (!doc) ctx.note('A function.');
  } else if (typeof v === 'function') {
    if (!doc) ctx.note('Builds a set from its arguments.');
  } else ctx.note(`Its value is ${fmt(v)}.`);
  for (const f of card.figs) f.render();
}

// Does the claim's body give numbers or points? Tried at a few sample values of its variables
// (a plot needs plain variables, so a split point (x, y) keeps the true/false treatment).
function givesNumbers(claim, env) {
  if (claim.binders.some(b => b.pattern) || claim.binders.length > 2) return false;
  const f = compile(claim.body, { q: 1 });
  try {
    const doms = claim.binders.map(b => compileDomain(b.dom)(env));
    if (!doms.every(D => D.scalar)) return false;
    const draws = [0, 1, 2].map(k => doms.map(D => { const s = D.sample(5); return s[k % s.length]; }));
    let numbers = 0;
    for (const vals of draws) {
      const e = Object.create(env);
      claim.binders.forEach((b, i) => { e[b.name] = vals[i]; });
      let v;
      try { v = f(e); } catch (err) { continue; }
      if (typeof v === 'boolean') return false;
      if (typeof v === 'number' || (v && v.__exact) || (APP.isNumArr(v) && v.length <= 3)) numbers++;
    }
    return numbers > 0;
  } catch (err) { return false; }
}

async function explainDefinition(ast, env, card, fn, d, opts = {}) {
  card.formula(`${signature(ast.name, d)} := ${pp(d.body)}`);
  if (d.doc) card.doc(d.doc);
  addExtra(card, d.body, d.env, new Set([...d.params, ast.name]));
  if (!d.params.length) return;
  const given = ast.binders || [];
  const covered = new Set(given.flatMap(MV.binderNames));
  const fromExamples = (d.examples || []).filter(b => !MV.binderNames(b).some(n => covered.has(n)));
  fromExamples.forEach(b => MV.binderNames(b).forEach(n => covered.add(n)));
  const numericParams = d.params.filter((p, i) => !covered.has(p) && d.types[i] && (() => { try { return compileDomain(d.types[i])(env).scalar; } catch (e) { return false; } })());
  const defaults = [], missing = [];
  d.params.forEach((p, i) => {
    if (covered.has(p)) return;
    const ex = defaultExamples(d.types[i], env, numericParams.indexOf(p), numericParams.length);
    if (ex && (ex.kind !== 'finite' || ex.values.length)) defaults.push({ name: p, pattern: null, dom: { type: 'value', v: ex, label: ex.describe() } });
    else missing.push(p);
  });
  if (missing.length) {
    makeCtx(card).note(`To try ${ast.name} on examples, give ${missing.join(' and ')} a type in the definition (as in ${missing[0]}: R), or write "explain ${ast.name} for ${missing[0]} in …".`);
    return;
  }
  const claim = {
    type: 'quant', q: 'forall', binders: [...given, ...fromExamples, ...defaults],
    body: { type: 'call', f: { type: 'value', v: fn, label: ast.name }, args: d.params.map(p => ({ type: 'id', name: p })) },
  };
  // A definition giving numbers (or points) rather than true/false is drawn, not tested.
  if (givesNumbers(claim, env)) {
    const shown = card.el.querySelector('.formula').innerHTML;
    try { APP.runPlot({ exprs: [claim.body], binders: claim.binders }, env, card); } finally { card.formula(shown); }
    return;
  }
  await runClaim(claim, env, card, {
    examples: ast.name,
    after: (info, c) => {
      const go = () => showDefinitionVariations(c, ast.name, fn, claim, env, info, { stress: info.stress });
      c.action('Vary the definition', go, 'Change one part of the definition at a time and see which examples change');
      if (opts.vary) go();
    },
  });
}

/* ---------------- structures ---------------- */

const structureOf = v => (typeof v === 'function' && v.__structure) || null;

function structureSignature(S) {
  const fields = S.params.map((p, i) => esc(nameOf(p)) + (S.types[i] ? ': ' + MV.ppDom(S.types[i], true) : '')).join(', ');
  return `<span class="fkw">structure</span> <span class="up">${esc(S.name)}</span>(${fields})${S.parent ? ` <span class="fkw">extends</span> ${esc(S.parent.name)}` : ''}`;
}

// Check each axiom of S for the record rec. Resolves to [{ax, info | error}].
async function checkAxioms(S, rec, ctl, opts = {}) {
  const env = S.envFor(rec), out = [];
  for (const ax of S.axioms) {
    try { out.push({ ax, info: await MV.runSliced(MV.analyzeSteps(ax.body, env, { search: opts.search !== false, budget: opts.budget || 8000 }), ctl) }); }
    catch (err) { if (err.message === 'Stopped.') throw err; out.push({ ax, error: err.message }); }
  }
  return out;
}
const axiomOk = r => !!(r.info && !r.info.count.fail && !r.info.count.undef && (r.info.count.ok || r.info.count.vac));

function counterText(info) {
  const r = info.simplest || info.res.find(x => x.s === 'fail');
  if (!r || !info.binders.length) return info.count.fail ? 'false' : '';
  const names = info.binders.map(b => b.pattern ? `(${b.pattern.map(nameOf).join(', ')})` : nameOf(b.name));
  return names.map((n, i) => `${n} = ${nice(r.vals[i])}`).join(', ');
}

// The full check of one axiom for one record, drawn as a card inside a panel of card.
function showAxiom(card, S, rec, r) {
  const box = panel(card, 'axiom-detail', `${r.ax.name} for ${fmt(rec)}`);
  const sub = APP.makeCard(null, 'axiom', r.ax.name, box);
  sub.formula(pp(r.ax.body));
  if (r.error) sub.error(new MVError(r.error));
  else renderClaim(sub, r.info, {});
  box.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
}

// check x in S, for a structure S: one row per axiom.
async function runStructureCheck(body, env, card, S) {
  const rec = compile(body.elem)(env);
  card.formula(pp(body));
  if (S.doc) card.doc(S.doc);
  const no = text => { card.setStatus(body.neg ? 'ok' : 'fail', `Not a ${S.name}`); makeCtx(card).note(text); };
  if (!MV.isRecord(rec)) return no(`${MV.describeValue(rec)} is not a record, so it has no fields ${S.params.join(', ')}.`);
  const missing = S.params.filter(p => !(p in rec.fields));
  if (missing.length) return no(`It has no field ${missing.join(', ')}.`);
  const ctl = card.progress('Checking the axioms');
  let results;
  try { results = await checkAxioms(S, rec, ctl); } finally { ctl.done(); }
  const bad = results.filter(r => !axiomOk(r));
  const truth = body.neg ? !!bad.length : !bad.length;
  card.setStatus(truth ? 'ok' : 'fail', bad.length ? `Not a ${S.name}: fails ${bad.map(r => r.ax.name).join(', ')}` : `A ${S.name}: all ${results.length} axioms hold`);
  const wrap = h('div', 'table-wrap'), t = h('table', 'var-table axioms');
  const head = h('tr');
  ['Axiom', '', 'Result', 'Counterexample'].forEach(x => head.append(h('th', null, x)));
  t.append(head);
  for (const r of results) {
    const tr = h('tr', 'clickable');
    const name = h('td');
    name.append(h('strong', null, r.ax.name));
    if (r.ax.from !== S.name) name.append(h('span', 'muted', ` (${r.ax.from})`));
    const f = h('td', 'axiom-formula');
    f.innerHTML = pp(r.ax.body);
    const ok = axiomOk(r);
    const res = h('td', ok ? 'gained' : 'lost', r.error ? 'error' : ok ? (r.info.exhaustive && !r.info.binders.length ? '✓ holds' : r.info.exhaustive ? '✓ holds (all cases)' : '✓ holds') : '✗ fails');
    const cex = h('td', null, r.error ? r.error : ok ? '' : counterText(r.info));
    tr.append(name, f, res, cex);
    tr.title = 'Show the full check';
    tr.addEventListener('click', () => showAxiom(card, S, rec, r));
    t.append(tr);
  }
  wrap.append(t);
  card.body.append(wrap);
  makeCtx(card).note('Click an axiom to see its full check.');
}

// explain S: the fields and axioms, and how the examples fare against each axiom.
async function explainStructure(ast, env, card, S) {
  card.formula(structureSignature(S));
  if (S.doc) card.doc(S.doc);
  const list = h('ul', 'axiom-list');
  for (const ax of S.axioms) {
    const li = h('li');
    li.innerHTML = `<strong>${esc(ax.name)}</strong>${ax.from !== S.name ? ` <span class="muted">(from ${esc(ax.from)})</span>` : ''}: ${pp(ax.body)}`;
    list.append(li);
  }
  card.body.append(list);
  let examples = null;
  if (ast.binders && ast.binders.length) examples = ast.binders.flatMap(b => compileDomain(b.dom)(env).sample(64));
  else if (S.examples) examples = compile(S.examples)(S.env);
  if (!examples || !examples.length) {
    makeCtx(card).note(`To see examples, add a comment line "examples: ${S.name}(…), …" above the structure, or write explain ${S.name} for g in {…}.`);
    return;
  }
  const ctl = card.progress('Checking the examples');
  const rows = [];
  try {
    for (let i = 0; i < examples.length; i++) {
      const rec = examples[i];
      rows.push({ rec, results: MV.isRecord(rec) ? await checkAxioms(S, rec, ctl, { search: false, budget: 4000 }) : null });
      ctl.onProgress({ phase: 'examples', done: i + 1, total: examples.length });
    }
  } finally { ctl.done(); }
  const n = rows.filter(r => r.results && r.results.every(axiomOk)).length;
  card.setStatus('info', `${n} of ${rows.length} examples are ${S.name}s`);
  const wrap = h('div', 'table-wrap'), t = h('table', 'var-table matrix axioms');
  const head = h('tr');
  head.append(h('th', null, 'Example'));
  for (const ax of S.axioms) head.append(h('th', null, ax.name));
  head.append(h('th', null, S.name + '?'));
  t.append(head);
  for (const row of rows) {
    const tr = h('tr');
    tr.append(h('td', null, fmt(row.rec)));
    if (!row.results) { tr.append(h('td', 'error-msg', 'not a record')); t.append(tr); continue; }
    for (const r of row.results) {
      const ok = axiomOk(r);
      const td = h('td', 'clickable ' + (ok ? 'gained' : 'lost'), r.error ? '!' : ok ? '✓' : '✗');
      td.title = (r.error || (ok ? 'Holds' : 'Fails at ' + counterText(r.info))) + ' · click for the full check';
      td.addEventListener('click', () => showAxiom(card, S, row.rec, r));
      tr.append(td);
    }
    const all = row.results.every(axiomOk);
    tr.append(h('td', all ? 'gained' : 'lost', all ? 'yes' : 'no'));
    t.append(tr);
  }
  wrap.append(t);
  card.body.append(wrap);
  // An example satisfying every axiom but one shows that axiom doesn't follow from the rest.
  const separates = j => rows.find(row => row.results && !axiomOk(row.results[j]) && row.results.every((r, i) => i === j || axiomOk(r)));
  const indep = [], open = [];
  S.axioms.forEach((ax, j) => { const w = separates(j); if (w) indep.push(`${ax.name} (${fmt(w.rec)} has all the others)`); else open.push(ax.name); });
  if (indep.length) makeCtx(card).note(`Not implied by the other axioms: ${indep.join('; ')}.`);
  if (open.length && indep.length) makeCtx(card).note(`No example here satisfies everything except ${open.join(', or except ')}. Add one to show that axiom is needed, or it may follow from the others.`, 'caveat');
}

/* vary name: a definition's examples and how they change when the definition changes; or a
   claim's check and its variations. */
async function runVary(ast, env, card) {
  checkNames({ type: 'id', name: ast.name, pos: ast.pos }, env);
  const v = env[ast.name];
  if (MV.DEFS.get(v)) return runExplain({ ...ast, type: 'explain', binders: null }, env, card, { vary: true });
  if (v && v.__claim) {
    const body = { type: 'id', name: ast.name };
    await runClaim(body, env, card, { after: (info, c) => showVariations(c, body, env, { stress: info.stress }) });
    return;
  }
  throw new MVError(`vary works on definitions and named theorems or lemmas; ${ast.name} is ${MV.describeValue(v)}.`);
}

Object.assign(APP, { runClaim, renderClaim, runExplain, runVary, docFor, nice });
})();
