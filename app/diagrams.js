/* Theorem Sketchpad UI — diagram statements: the objects and arrows drawn left to right, every
   check listed, and the arrows of failing checks in red. */
'use strict';
(function () {
const APP = window.APP;
const { h, makeCtx } = APP;
const { esc } = MV;

function runDiagram(ast, env, card) {
  const res = MV.checkDiagram(ast, env);
  card.formula(`<span class="fkw">diagram</span>${ast.name ? ` <span class="up">${esc(ast.name)}</span>` : ''}: ${res.arrows.map(a => `${esc(a.name)}: ${esc(a.src.label)} → ${esc(a.dst.label)}`).join(', ')}`);
  const bad = new Set(res.checks.filter(c => !c.ok).flatMap(c => c.arrows || []));
  for (const a of res.arrows) if (!a.lands.ok) bad.add(a.name);
  const ctx = makeCtx(card);
  const D = ctx.diagram({ layout: 'flow', hint: 'Hover an object to see its elements.' });
  for (const o of res.objects) D.node(o.key, { label: o.label, tip: `${o.label} = {${o.els.slice(0, 16).map(MV.fmt).join(', ')}${o.els.length > 16 ? ', …' : ''}} (${o.els.length} elements)` });
  for (const a of res.arrows) D.edge(a.src.key, a.dst.key, { label: a.name, color: bad.has(a.name) ? 'neg' : res.ok ? 'pos' : 'ink', width: 1.6 });
  // The checks, one per row.
  const rows = [
    ...res.arrows.map(a => [`${a.name}: ${a.src.label} → ${a.dst.label}`, a.lands.ok ? (a.hom ? (a.hom.ok ? '✓ a homomorphism' : '✓ a map (not a homomorphism)') : '✓ a map') : '✗', a.lands.ok ? (a.hom && !a.hom.ok ? a.hom.detail : '') : a.lands.detail]),
    ...res.checks.map(c => [c.text, c.ok ? '✓' : '✗', c.detail]),
  ];
  const wrap = h('div', 'table-wrap'), t = h('table', 'var-table');
  const head = h('tr');
  ['Check', 'Result', ''].forEach(x => head.append(h('th', null, x)));
  t.append(head);
  for (const [a, b, c] of rows) {
    const tr = h('tr');
    tr.append(h('td', 'axiom-formula', a), h('td', b.startsWith('✓') ? 'gained' : 'lost', b), h('td', null, c));
    t.append(tr);
  }
  wrap.append(t);
  card.body.append(wrap);
  const failed = res.checks.filter(c => !c.ok).length + res.arrows.filter(a => !a.lands.ok).length;
  card.setStatus(res.ok ? 'ok' : 'fail', res.ok ? (res.checks.length ? `Holds: ${res.checks.length} check${res.checks.length > 1 ? 's' : ''}, at every element` : 'Every arrow is a map') : `${failed} check${failed > 1 ? 's' : ''} fail${failed > 1 ? '' : 's'}`);
  for (const f of card.figs) f.render();
}

APP.runDiagram = runDiagram;
})();
