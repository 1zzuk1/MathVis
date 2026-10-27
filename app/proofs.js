/* Theorem Sketchpad UI — proof sketches: runs the checker in src/proofs.js in slices, then
   draws one row per step, with blocks (cases, the base and step of an induction) indented under
   the step that opens them. Click a step to see its check. */
'use strict';
(function () {
const APP = window.APP;
const { h, makeCtx } = APP;
const { esc, pp, ppText } = MV;

async function runProof(ast, env, card) {
  const target = MV.proofTarget(ast, env, APP.lastClaim);
  card.formula(target ? `<span class="fkw">proof of</span> <span class="up">${esc(target.name)}</span>: ${pp(target.body)}` : '<span class="fkw">proof</span> (no goal: each step is checked on its own)');
  if (target && target.doc) card.doc(target.doc);

  const ctl = card.progress('Checking the steps');
  let result;
  try {
    const g = MV.checkProofSteps(ast, env, target);
    let r = g.next(), done = 0;
    while (!r.done) {
      ctl.onProgress({ phase: 'steps', done: done++, total: done + 1 });
      const info = await APP.analyze(r.value, env, { budget: 6000 }, ctl);
      r = g.next(info);
    }
    result = r.value;
  } finally { ctl.done(); }
  const { rows, closed } = result;

  const bad = rows.findIndex(r => r.status === 'fail' || r.status === 'error');
  if (bad >= 0) card.setStatus('fail', `Step ${stepNumber(rows, bad)} ${rows[bad].status === 'error' ? 'has an error' : 'fails'}`);
  else if (target && closed && exactProof(rows)) card.setStatus('ok', 'Proved: every step is exact');
  else if (target && closed) card.setStatus('ok', 'Every step holds on the samples, and the goal is reached');
  else if (target) card.setStatus('info', 'The steps hold, but the goal isn\'t reached yet');
  else card.setStatus('ok', 'Every step holds on the samples');

  const list = h('ol', 'proof-steps');
  rows.forEach((r, i) => {
    const li = h('li', 'proof-step ' + (r.status || '') + (isHeader(r) ? ' ps-block' : ''));
    li.style.setProperty('--depth', r.depth);
    const head = h('div', 'ps-head');
    head.append(h('span', 'ps-num', isHeader(r) ? '' : stepNumber(rows, i) + '.'), h('span', 'fkw', r.step.word), document.createTextNode(' '));
    const body = h('span', 'ps-body');
    body.innerHTML = stepText(r.step);
    const res = h('span', 'ps-res ' + (r.status || ''), r.status === 'error' ? 'error' : resultText(r));
    head.append(body, res);
    li.append(head);
    if (r.error) li.append(h('div', 'error-msg', r.error));
    for (const n of r.notes) li.append(h('div', 'ps-note', n));
    if (r.info && r.status === 'fail') {
      const cx = counterText(r.info);
      if (cx) li.append(h('div', 'ps-note ps-cex', 'Counterexample: ' + cx));
    }
    // The goal after each step that changes it, inside each block, and at the end if still open.
    const changes = !['have', 'so'].includes(r.step.kind) || i === rows.length - 1;
    if (target && r.goalAfter && changes && r.step.kind !== 'cases') {
      const g = h('div', 'ps-goal');
      g.innerHTML = `<span class="muted">goal:</span> ${pp(r.goalAfter)}`;
      li.append(g);
    }
    if (r.claim) {
      li.classList.add('clickable');
      li.title = 'Show this step\'s check';
      li.addEventListener('click', ev => { if (ev.target.closest('.panel')) return; showStep(card, r, stepNumber(rows, i)); });
    }
    list.append(li);
  });
  card.body.append(list);
  makeCtx(card).note(target && closed && bad < 0 && exactProof(rows)
    ? 'Every step is exact: the equations were checked by algebra (both sides simplify to the same expression), not on samples.'
    : 'Each step is checked in its context: by algebra when it is an identity ("exact"), otherwise numerically on the variables taken so far, the assumptions and the values chosen. Click a step to see its check.' + (bad >= 0 ? '' : ' Holding on samples is evidence, not a proof.'));
}

const isHeader = r => ['case', 'base', 'step'].includes(r.step.kind);
// Every step exact: taken apart (let, assume, …) or proved by algebra, none merely sampled.
const exactProof = rows => rows.some(r => r.status === 'proved') && rows.every(r => isHeader(r) || r.status === 'struct' || r.status === 'proved');
// Steps are numbered in order, block headers not.
const stepNumber = (rows, i) => rows.slice(0, i + 1).filter(r => !isHeader(r)).length;

function stepText(s) {
  switch (s.kind) {
    case 'let': return s.binders.map(b => esc(MV.idOut(b.name, false)) + (b.dom ? ' ∈ ' + MV.ppDom(b.dom, true) : '')).join(', ');
    case 'choose': return s.expr ? `${esc(MV.idOut(s.name, false))} = ${pp(s.expr)}` : `${esc(MV.idOut(s.name, false))} ∈ ${MV.ppDom(s.dom, true)} such that ${pp(s.cond)}`;
    case 'contradiction': return '<span class="muted">suppose the goal fails</span>';
    case 'induction': return `on ${esc(MV.idOut(s.name, false))}`;
    case 'cases': return `<span class="muted">${s.cases.length} cases</span>`;
    case 'case': return s.expr ? pp(s.expr) : '';
    case 'base': case 'step': return '';
    default: return pp(s.expr) + (s.by ? ` <span class="muted">by ${esc(s.by)}</span>` : '');
  }
}

function resultText(r) {
  if (r.status === 'open') return '… open';
  if (r.status === 'struct') return '';
  if (r.status === 'vacuous') return '✓ vacuous';
  if (r.status === 'proved') return '✓ exact';
  const c = r.info && r.info.count;
  if (!c) return r.status === 'ok' ? '✓' : '';
  if (r.status === 'fail') return `✗ fails on ${c.fail} of ${c.ok + c.fail}`;
  if (r.status === 'vac') return '– never tested';
  if (r.status === 'undef') return '? undefined';
  return r.info.k === 0 ? '✓ holds' : `✓ ${c.ok + c.vac} samples`;
}

function counterText(info) {
  const r = info.simplest || info.res.find(x => x.s === 'fail');
  if (!r || !info.binders.length) return '';
  const names = info.binders.map(b => b.pattern ? `(${b.pattern.join(', ')})` : ppText({ type: 'id', name: b.name }));
  return names.map((n, i) => `${n} = ${APP.nice(r.vals[i])}`).join(', ');
}

function showStep(card, r, n) {
  let box = card.el.querySelector('.panel.step-detail');
  if (box) box.remove();
  box = h('div', 'panel step-detail');
  const head = h('div', 'trace-head');
  head.append(h('strong', null, `Step ${n}: what was checked`));
  const close = h('button', 'link-btn', 'Close');
  close.type = 'button';
  close.addEventListener('click', () => box.remove());
  head.append(close);
  box.append(head);
  card.el.append(box);
  const sub = APP.makeCard(null, 'step', `${n}`, box);
  sub.formula(pp(r.claim));
  APP.renderClaim(sub, r.info, {});
  box.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
}

APP.runProof = runProof;
})();
