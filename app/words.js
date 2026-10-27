/* Theorem Sketchpad UI — "Words": write a statement in plain English and get the notation, shown
   typeset, with what was assumed and what wasn't understood; insert it into the notebook (and run
   it). The translation itself is src/words.js. */
'use strict';
(function () {
const APP = window.APP;
const { h } = APP;
const $ = s => document.querySelector(s);

const EXAMPLES = [
  'For every real number x, x squared is at least 0.',
  'Every continuous function on [0, 1] is bounded.',
  'The sum of k for k from 1 to n equals n(n + 1)/2 for every natural number n.',
  'If n is even then n squared is even.',
  'Every bounded sequence is convergent.',
  'For all positive real numbers a and b, the square root of a times b is at most the sum of a and b divided by 2.',
];

let last = null;
function render() {
  const input = $('#wordsInput').value;
  const out = $('#wordsOut');
  out.replaceChildren();
  last = null;
  $('#wordsInsert').disabled = $('#wordsRun').disabled = true;
  if (!input.trim()) return;
  let r;
  try { r = MV.wordsToNotation(input, APP.env || null); } catch (e) { out.append(h('p', 'note caveat', 'Something went wrong translating this: ' + e.message)); return; }
  last = r;
  for (const imp of r.imports) out.append(h('div', 'words-line import', imp));
  for (const l of r.lines) {
    const row = h('div', 'words-line ' + (!l.ok ? 'bad' : l.sure ? 'ok' : 'unsure'));
    const head = h('div', 'words-head');
    head.append(h('span', 'words-mark', !l.ok ? '✗' : l.sure ? '✓' : '?'), h('code', 'words-code', l.output));
    row.append(head);
    // The notation, typeset, so it can be read back as mathematics.
    if (l.ok) {
      try {
        const ast = MV.parseStatement(MV.splitStatements(l.output)[0]);
        const node = ast.body || ast.expr || null;
        if (node) { const f = h('div', 'words-math formula'); f.innerHTML = (ast.type === 'check' ? '<span class="fkw">check</span> ' : '') + MV.pp(node); row.append(f); }
      } catch (e) { /* shown as code only */ }
    }
    const notes = [...(l.error ? [l.error] : []), ...l.notes];
    if (l.unknown.length) notes.push(`Not understood: ${l.unknown.join(', ')}.`);
    if (l.ok && !l.sure) notes.unshift('Part of this wasn\'t understood: check the notation before using it, or rephrase.');
    for (const n of notes) row.append(h('div', 'words-note', n));
    out.append(row);
  }
  $('#wordsInsert').disabled = $('#wordsRun').disabled = !r.lines.length;
}

// Add the notation after the line the cursor is on (imports at the top, unless already there).
function insert(run) {
  if (!last) return;
  const ta = APP.editor.ta, src = ta.value;
  const imports = last.imports.filter(i => !new RegExp(`^\\s*${i.replace(/\s+/g, '\\s+')}\\b`, 'm').test(src));
  // Each sentence stays above its notation as a comment; one that wasn't fully understood goes in
  // commented out, to fix by hand, so nothing half-understood runs.
  const body = last.lines.map(l => (l.ok && l.sure
    ? `# ${l.input}\n${l.output}`
    : `# Not fully understood, check before using: ${l.input}\n# ${l.output.replace(/\n/g, '\n# ')}`)).join('\n');
  let text = src;
  const pos = ta.selectionEnd || 0;
  const lineEnd = src.indexOf('\n', pos);
  const at = src.trim() ? (lineEnd < 0 ? src.length : lineEnd) : 0;
  text = text.slice(0, at) + (at > 0 ? '\n' : '') + body + (at < src.length ? '' : '\n') + text.slice(at);
  if (imports.length) text = imports.join('\n') + '\n' + text;
  APP.editor.set(text);
  ta.dispatchEvent(new Event('input'));
  ta.focus();
  if (run) { APP.run(); if (APP.toResults) APP.toResults(); }
}

function wire() {
  const panel = $('#wordsPanel');
  $('#wordsBtn').addEventListener('click', () => {
    panel.hidden = !panel.hidden;
    $('#wordsBtn').setAttribute('aria-expanded', String(!panel.hidden));
    if (!panel.hidden) $('#wordsInput').focus();
  });
  let timer = null;
  $('#wordsInput').addEventListener('input', () => { clearTimeout(timer); timer = setTimeout(render, 150); });
  $('#wordsInput').addEventListener('keydown', ev => {
    if (ev.key === 'Enter' && (ev.ctrlKey || ev.metaKey)) { ev.preventDefault(); render(); insert(true); }
  });
  $('#wordsInsert').addEventListener('click', () => insert(false));
  $('#wordsRun').addEventListener('click', () => insert(true));
  $('#wordsClose').addEventListener('click', () => { panel.hidden = true; $('#wordsBtn').setAttribute('aria-expanded', 'false'); });
  const ex = $('#wordsExamples');
  for (const s of EXAMPLES) {
    const b = h('button', 'words-example', s);
    b.type = 'button';
    b.addEventListener('click', () => { $('#wordsInput').value = s; render(); });
    ex.append(b);
  }
}
wire();
})();
