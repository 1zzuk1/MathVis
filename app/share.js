/* Theorem Sketchpad UI — sharing a notebook: a link that carries the notebook in its address,
   the notebook as a file, opening such a file, and a report: the results as one static HTML page
   with the pictures as images, readable anywhere without the app. */
'use strict';
(function () {
const APP = window.APP;
const { h } = APP;
const $ = s => document.querySelector(s);
const src = () => APP.editor.ta.value;

let framed = true;
try { framed = window.self !== window.top; } catch (e) { /* cross-origin parent */ }

const slug = s => s.replace(/[^\p{L}\p{N}]+/gu, '-').replace(/^-|-$/g, '').toLowerCase() || 'notebook';

function toast(text, kind = 'ok') {
  let t = $('#toast');
  if (!t) { t = h('div', 'toast'); t.id = 'toast'; t.setAttribute('role', 'status'); document.body.append(t); }
  t.textContent = text;
  t.className = 'toast ' + kind;
  t.hidden = false;
  clearTimeout(toast.timer);
  toast.timer = setTimeout(() => { t.hidden = true; }, 3200);
}

async function offerFile(name, ext, data, mime) {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([data], { type: mime }));
  a.download = `${name}.${ext}`;
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 2000);
}

/* ---------- links: #nb=<the source, deflated, base64url> ---------- */

const unb64url = s => Uint8Array.from(atob(s.replace(/-/g, '+').replace(/_/g, '/')), c => c.charCodeAt(0));
async function pipe(bytes, stream) {
  const out = await new Response(new Blob([bytes]).stream().pipeThrough(stream)).arrayBuffer();
  return new Uint8Array(out);
}
async function encode(text) {
  const raw = new TextEncoder().encode(text);
  if (typeof CompressionStream !== 'function') return 'src=' + encodeURIComponent(text);
  const z = await pipe(raw, new CompressionStream('deflate-raw'));
  let s = '';
  for (let i = 0; i < z.length; i += 0x8000) s += String.fromCharCode(...z.subarray(i, i + 0x8000));
  return 'nb=' + btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}
async function decode(hash) {
  const m = /^#?(nb|src)=(.*)$/s.exec(hash);
  if (!m) return null;
  if (m[1] === 'src') return decodeURIComponent(m[2]);
  return new TextDecoder().decode(await pipe(unb64url(m[2]), new DecompressionStream('deflate-raw')));
}

async function copyLink() {
  const url = location.origin + location.pathname + '#' + await encode(src());
  try { await navigator.clipboard.writeText(url); toast(url.length > 8000 ? 'Link copied. It is long; some apps may cut it.' : 'Link copied: opening it shows this notebook.'); }
  catch (e) { prompt('Copy this link:', url); }
}

/* ---------- the report ---------- */

function pageCSS() {
  let css = '';
  for (const sheet of document.styleSheets) {
    try { for (const r of sheet.cssRules) css += r.cssText + '\n'; } catch (e) { /* the web-font sheet: linked instead */ }
  }
  return css;
}

function reportHTML() {
  // Thumbnails not yet scrolled into view are drawn now, so the report has every picture.
  for (const f of MV.FIGS) if (f.o && f.o.static && !f.seen && f.wrap.isConnected) { f.seen = true; f.draw(); }
  const cards = $('#cards').cloneNode(true);
  // Pictures become images; controls and hover hints go.
  const live = [...$('#cards').querySelectorAll('canvas')];
  [...cards.querySelectorAll('canvas')].forEach((c, i) => {
    const orig = live[i];
    let url = '';
    try { url = orig.toDataURL('image/png'); } catch (e) { /* leave it out */ }
    const img = document.createElement('img');
    img.src = url;
    img.alt = 'Figure';
    img.style.width = (orig.clientWidth || orig.width) + 'px';
    img.style.maxWidth = '100%';
    img.style.height = 'auto';
    c.replaceWith(img);
  });
  cards.querySelectorAll('button, input, select, textarea, .card-actions, .diagram-tip, .hint').forEach(e => e.remove());
  cards.querySelectorAll('[hidden]').forEach(e => e.remove());
  const name = APP.notebookName();
  const esc = MV.esc;
  const fonts = [...document.querySelectorAll('link[rel="stylesheet"][href^="https://fonts.googleapis.com"]')].map(l => l.outerHTML).join('');
  const theme = document.documentElement.getAttribute('data-theme');
  return `<!doctype html>
<html lang="en"${theme ? ` data-theme="${theme}"` : ''}><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>${esc(name)} — Theorem Sketchpad</title>${fonts}
<style>${pageCSS()}
body.report { background: var(--bg); color: var(--ink); font-family: var(--f-ui); margin: 0; }
.report-main { max-width: 880px; margin: 0 auto; padding: 28px 16px 48px; }
.report-main > h1 { font: 600 26px/1.2 var(--f-math); margin: 0 0 4px; }
.report-meta { color: var(--muted); font-size: 13px; margin: 0 0 20px; }
.report-main .card { margin-bottom: 16px; }
.report-src { margin-top: 28px; }
.report-src pre { font: 13px/1.5 var(--f-mono); background: var(--sunk); border: 1px solid var(--line); border-radius: 8px; padding: 12px; overflow-x: auto; }
</style></head>
<body class="report"><main class="report-main">
<h1>${esc(name)}</h1>
<p class="report-meta">Results from Theorem Sketchpad, ${esc(new Date().toLocaleString())}. Sampled checks are evidence, not proofs, unless marked proved.</p>
${cards.innerHTML}
<details class="report-src"><summary>The notebook</summary><pre>${esc(src())}</pre></details>
</main></body></html>`;
}

/* ---------- the menu ---------- */

function setup() {
  const btn = $('#nbShare'), menu = $('#shareMenu');
  if (!btn) return;
  const close = () => { menu.hidden = true; btn.setAttribute('aria-expanded', 'false'); };
  btn.addEventListener('click', () => {
    menu.hidden = !menu.hidden;
    btn.setAttribute('aria-expanded', String(!menu.hidden));
    if (!menu.hidden) menu.querySelector('button:not([hidden])').focus();
  });
  document.addEventListener('click', ev => { if (!menu.hidden && !menu.contains(ev.target) && ev.target !== btn) close(); });
  menu.addEventListener('keydown', ev => { if (ev.key === 'Escape') { close(); btn.focus(); } });
  // A link only means something when the page is opened directly, not inside a viewer's frame.
  $('#shareLink').hidden = framed || location.protocol === 'file:';
  $('#shareLink').addEventListener('click', () => { close(); copyLink(); });
  $('#shareFile').addEventListener('click', () => { close(); offerFile(slug(APP.notebookName()), 'mv', src(), 'text/plain'); });
  $('#shareReport').addEventListener('click', () => {
    close();
    if (!$('#cards').querySelector('.card')) { toast('Run the notebook first: the report holds its results.', 'info'); return; }
    offerFile(slug(APP.notebookName()) + '-report', 'html', reportHTML(), 'text/html');
  });
  $('#openFile').addEventListener('change', async ev => {
    const f = ev.target.files[0];
    ev.target.value = '';
    close();
    if (!f) return;
    APP.loadSource(await f.text());
    toast(`Opened ${f.name} as an unsaved notebook.`);
  });
}

async function openFromLink() {
  if (!/^#(nb|src)=/.test(location.hash)) return;
  try {
    const text = await decode(location.hash);
    if (text != null) { APP.loadSource(text); toast('Opened the notebook from the link. It is an unsaved copy.'); }
  } catch (e) { toast('This link holds a notebook that could not be read; it may have been cut short.', 'error'); }
  // Drop the notebook from the address so a reload keeps later edits.
  try { history.replaceState(null, '', location.pathname + location.search); } catch (e) { /* not allowed here */ }
}

setup();
openFromLink();
APP.share = { encode, decode, reportHTML };
APP.toast = toast;
})();
