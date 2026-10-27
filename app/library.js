/* Theorem Sketchpad UI — the library registry and the Libraries tab. */
'use strict';
(function () {
const APP = window.APP;
const { h } = APP;
const { registerJS, registerNotation, rebuildIndex, REG, BUILTIN } = MV;
const $ = s => document.querySelector(s);

const LS_LIBS = 'theorem-sketchpad.libraries';
let USER_LIBS = [];
try { USER_LIBS = JSON.parse(APP.store.get(LS_LIBS, '[]')) || []; } catch (e) { USER_LIBS = []; }
const saveUserLibs = () => APP.store.set(LS_LIBS, JSON.stringify(USER_LIBS));

function fnBody(fn) {
  const s = fn.toString();
  const lines = s.slice(s.indexOf('{') + 1, s.lastIndexOf('}')).split('\n');
  while (lines.length && !lines[0].trim()) lines.shift();
  while (lines.length && !lines[lines.length - 1].trim()) lines.pop();
  const indent = Math.min(...lines.filter(l => l.trim()).map(l => l.match(/^ */)[0].length));
  return lines.map(l => l.slice(indent)).join('\n') + '\n';
}

function rebuildRegistry() {
  REG.clear();
  for (const b of BUILTIN) {
    const entry = b.kind === 'js'
      ? registerJS(b.fn, { builtin: true, source: fnBody(b.fn) })
      : registerNotation(b.source.trim() + '\n', { builtin: true });
    entry.key = entry.name;
    REG.set(entry.key, entry);
  }
  for (const u of USER_LIBS) {
    const entry = u.kind === 'js'
      ? registerJS(u.source, { builtin: false, id: u.id, source: u.source })
      : registerNotation(u.source, { builtin: false, id: u.id });
    entry.key = entry.name;
    if (REG.has(entry.key)) {
      entry.error = `Another library is already called "${entry.name}". Rename this one to use it.`;
      entry.key = `${entry.name} · ${u.id}`;
    }
    REG.set(entry.key, entry);
  }
  rebuildIndex();
  if (APP.pool && APP.pool.reset) APP.pool.reset();
}
APP.userLibs = () => USER_LIBS.map(u => ({ kind: u.kind, source: u.source, id: u.id }));

const JS_TEMPLATE = name => `// A JavaScript library. Every field except name is optional.
// Use it in a notebook with: import ${name}
MathViz.define({
  name: '${name}',
  description: 'Golden-ratio helpers, an annulus, and a spiral view.',

  constants: {
    golden: (1 + Math.sqrt(5)) / 2,
  },

  // Plain functions, or { doc, fn } to show documentation in the Libraries tab and in autocomplete.
  functions: {
    fibratio: {
      doc: 'fibratio(n): the ratio F(n)/F(n − 1) of consecutive Fibonacci numbers.',
      fn(n) {
        let a = 1, b = 1;
        for (let k = 2; k < n; k++) [a, b] = [b, a + b];
        return b / a;
      },
    },
  },

  // Spaces variables can range over. contains() plus a sampling window is enough:
  // sampling, boundary search, Seq(…), complements and drawing then work automatically.
  spaces: {
    Annulus2: {
      doc: 'Annulus2(r, R): points of the plane with r < |p| < R.',
      fn: (r, R) => MathViz.space({
        label: \`annulus \${r} < |p| < \${R}\`,
        window: [[-R, R], [-R, R]],
        contains: p => MathViz.ops.lt(r, MathViz.ops.abs(p)) && MathViz.ops.lt(MathViz.ops.abs(p), R),
      }),
    },
  },

  views: {
    spiral: {
      doc: 'spiral(turns) draws a golden spiral.',
      render(ctx, turns = 3) {
        turns = ctx.param('turns', { min: 1, max: 8, step: 0.5, value: turns });
        const g = (1 + Math.sqrt(5)) / 2, pts = [];
        for (let k = 0; k <= 800; k++) {
          const t = k / 800 * turns * 2 * Math.PI, r = Math.pow(g, t / (Math.PI / 2)) / 10;
          pts.push([r * Math.cos(t), r * Math.sin(t)]);
        }
        const R = Math.max(...pts.map(p => Math.hypot(p[0], p[1]))) * 1.05;
        ctx.figure({ x: [-R, R], y: [-R, R], square: true }).curve(pts, { color: 'accent' });
        ctx.note(\`\${turns} turns; the radius grows by a factor of \${MathViz.format(+g.toFixed(4))} every quarter turn.\`);
      },
    },
  },

  // Definitions and lemmas in notebook notation, run after the exports above.
  notation: \`
# The annulus is open.
lemma annulus_open: open(Annulus2(1, 2))
\`,
  requires: ['topology'],
});
`;
const NOTATION_TEMPLATE = name => `library ${name}
# Definitions in notebook notation. Use them after: import ${name}
# A library may contain import, let, def and named lemmas. The comment right above a
# definition documents it; an "examples:" line says what explain should try it on.

# f is bounded by M on [a, b].
# examples: f in Functions(R), a in {-1}, b in {1}, M in {1, 2}
def bounded_by(f: Fun, a: R, b: R, M: R) := forall x in [a, b]: |f(x)| <= M

# f is even: f(−x) = f(x).
# examples: f in Functions(R)
def even(f: Fun) := forall x in [-3, 3]: f(-x) = f(x)

# S is dense in [a, b]: every small interval of [a, b] meets S.
def dense_in(S: Set, a: R, b: R) := forall x in [a, b], ε in (0, 1]: exists y in Ball(x, ε): y in S

# A sum of two even functions is even.
lemma even_sum: forall f, g in Functions(R): even(f) and even(g) -> even(x => f(x) + g(x))
`;

let openId = null;  // REG key of the library shown in the detail view

// Search across every library's exports: names first, then documentation.
function searchLibs(q) {
  const words = q.toLowerCase().split(/\s+/).filter(Boolean);
  // Matches by topic (src/topics.js): "derivative" also finds grad and jacobian.
  const topic = new Map(MV.findTopic ? MV.findTopic(q).map(e => [e.lib + '|' + e.name, e.score]) : []);
  const hits = [];
  for (const lib of REG.values()) {
    if (lib.error) continue;
    for (const g of exportsOf(lib)) for (const [n, doc] of g.items) {
      const name = n.toLowerCase(), text = (doc || '').toLowerCase();
      let score = 0;
      for (const w of words) {
        const s = name === w ? 100 : name.startsWith(w) ? 60 : name.includes(w) ? 40 : text.includes(w) ? 10 : 0;
        if (!s) { score = 0; break; }
        score += s;
      }
      if (!score && topic.has(lib.name + '|' + n)) score = 3 * topic.get(lib.name + '|' + n);
      if (score) hits.push({ lib, kind: g.title, action: g.action, name: n, doc, score });
    }
  }
  return hits.sort((a, b) => b.score - a.score || a.name.localeCompare(b.name)).slice(0, 60);
}
function renderSearch(q) {
  const list = $('#libList');
  list.replaceChildren();
  const hits = searchLibs(q);
  if (!hits.length) { list.append(h('li', 'lib-none', `Nothing matches "${q}". Try a shorter word, or a word from the documentation.`)); return; }
  for (const x of hits) {
    const li = h('li', 'lib-hit');
    const top = h('div', 'lib-top');
    top.append(h('code', 'lib-name', x.name), h('span', 'badge', x.kind.replace(/s$/, '').toLowerCase()));
    const open = h('button', 'link-btn', x.lib.name);
    open.type = 'button';
    open.title = 'Open this library';
    open.addEventListener('click', () => openLib(x.lib.key));
    top.append(open);
    if (x.action) {
      const b = h('button', 'mini-btn', x.action === 'check' ? 'Check' : 'Explain');
      b.type = 'button';
      b.addEventListener('click', () => APP.preview(`${x.action} ${x.name}`, x.lib.name));
      top.append(b);
    }
    li.append(top, h('span', 'lib-desc', x.doc || ''));
    list.append(li);
  }
}

function renderLibList() {
  const q = ($('#libSearch') || {}).value || '';
  if (q.trim()) { renderSearch(q.trim()); return; }
  const list = $('#libList');
  list.replaceChildren();
  for (const lib of REG.values()) {
    const li = h('li');
    const btn = h('button', 'lib-item');
    btn.type = 'button';
    const top = h('span', 'lib-top');
    top.append(h('span', 'lib-name', lib.name));
    top.append(h('span', 'badge', lib.kind === 'js' ? 'JavaScript' : 'notation'));
    top.append(h('span', 'badge' + (lib.builtin ? '' : ' mine'), lib.builtin ? 'built-in' : 'yours'));
    if (['core', 'catalog', 'geometry'].includes(lib.name)) top.append(h('span', 'badge', 'always loaded'));
    if (lib.error) top.append(h('span', 'badge err', 'error'));
    btn.append(top, h('span', 'lib-desc', lib.error || lib.description || ''));
    btn.addEventListener('click', () => openLib(lib.key));
    li.append(btn);
    list.append(li);
  }
}

function exportsOf(lib) {
  const docs = lib.docs || {};
  const groups = [];
  const add = (title, names, action) => { if (names.length) groups.push({ title, action, items: names.map(n => [n, docs[n] || '']) }); };
  if (lib.def) {
    const d = lib.def;
    add('Functions', Object.keys(d.functions), 'explain');
    add('Constants', Object.keys(d.constants || {}), null);
    add('Spaces', Object.keys(d.domains), 'explain');
    add('Value types', (d.types || []).map(t => t.name), null);
    add('Views', Object.keys(d.views || {}), null);
  }
  add('Definitions', lib.names || [], 'explain');
  add('Lemmas', (lib.lemmas || []).map(l => l.name), 'check');
  return groups;
}

function openLib(key) {
  const lib = REG.get(key);
  if (!lib) return;
  openId = key;
  $('#libListWrap').hidden = true;
  $('#libDetail').hidden = false;
  $('#libTitle').textContent = lib.name;
  $('#libBadges').replaceChildren(h('span', 'badge', lib.kind === 'js' ? 'JavaScript' : 'notation'), h('span', 'badge' + (lib.builtin ? '' : ' mine'), lib.builtin ? 'built-in' : 'yours'));
  $('#libDesc').textContent = lib.description || '';
  const use = $('#libUse');
  use.replaceChildren();
  if (['core', 'catalog', 'geometry'].includes(lib.name)) use.textContent = 'Loaded automatically in every notebook.';
  else use.append('Use it with ', h('code', null, `import ${lib.name}`), '. Explain and Check open a preview above your results.');
  $('#libTry').hidden = ['core', 'catalog', 'geometry'].includes(lib.name) || !!lib.error;
  const ex = $('#libExports');
  ex.replaceChildren();
  for (const g of exportsOf(lib)) {
    const box = h('div', 'exp-group');
    box.append(h('h4', null, g.title));
    const dl = h('dl', 'exp-docs');
    for (const [n, doc] of g.items) {
      const dt = h('dt');
      dt.append(h('code', null, n));
      if (g.action && !lib.error) {
        const b = h('button', 'mini-btn', g.action === 'check' ? 'Check' : 'Explain');
        b.type = 'button';
        b.addEventListener('click', () => APP.preview(`${g.action} ${n}`, lib.name));
        dt.append(b);
      }
      dl.append(dt, h('dd', null, doc));
    }
    box.append(dl);
    ex.append(box);
  }
  APP.libEditor.lang = lib.kind === 'js' ? 'js' : 'notation';
  APP.libEditor.ta.readOnly = !!lib.builtin;
  APP.libEditor.set(lib.source || '');
  $('#libSave').hidden = $('#libDelete').hidden = !!lib.builtin;
  $('#libCopy').hidden = !lib.builtin;
  $('#libDelete').textContent = 'Delete';
  $('#libDelete').classList.remove('confirm');
  setLibMsg(lib.error ? 'error' : '', lib.error || '');
}

function setLibMsg(kind, text) {
  const m = $('#libMsg');
  m.className = 'lib-msg ' + kind;
  m.textContent = text;
}

function closeLib() {
  openId = null;
  $('#libDetail').hidden = true;
  $('#libListWrap').hidden = false;
  renderLibList();
}

function uniqueName(base) {
  let name = base, k = 2;
  const taken = new Set([...REG.values()].map(l => l.name));
  while (taken.has(name)) name = base + k++;
  return name;
}

function addUserLib(kind, source) {
  const id = Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
  USER_LIBS.push({ id, kind, source });
  saveUserLibs();
  rebuildRegistry();
  openLib([...REG.values()].find(e => e.id === id).key);
}

function wire() {
  $('#newJs').addEventListener('click', () => addUserLib('js', JS_TEMPLATE(uniqueName('mylib'))));
  $('#newNotation').addEventListener('click', () => addUserLib('notation', NOTATION_TEMPLATE(uniqueName('mydefs'))));
  $('#libBack').addEventListener('click', closeLib);
  let searchTimer = null;
  $('#libSearch').addEventListener('input', () => { clearTimeout(searchTimer); searchTimer = setTimeout(renderLibList, 120); });
  $('#libFile').addEventListener('change', async ev => {
    const file = ev.target.files[0];
    ev.target.value = '';
    if (!file) return;
    const text = await file.text();
    const kind = /^\s*(MathVizNotation\s*\(\s*`\s*)?library\s+\w+/.test(text) ? 'notation' : 'js';
    addUserLib(kind, text);
    setLibMsg('ok', `Loaded ${file.name}. It is saved in this browser.`);
  });
  $('#libCopy').addEventListener('click', () => {
    const lib = REG.get(openId);
    if (!lib) return;
    const name = uniqueName(lib.name + '_copy');
    const source = lib.kind === 'js'
      ? lib.source.replace(new RegExp(`name:\\s*'${lib.name}'`), `name: '${name}'`)
      : lib.source.replace(/^(\s*library\s+)\w+/m, `$1${name}`);
    addUserLib(lib.kind, source);
    setLibMsg('ok', `Copied as ${name}. Edit it, then save.`);
  });
  $('#libCopySource').addEventListener('click', async () => {
    try { await navigator.clipboard.writeText(APP.libEditor.ta.value); setLibMsg('ok', 'Source copied.'); }
    catch (e) { APP.libEditor.ta.focus(); APP.libEditor.ta.select(); setLibMsg('', 'Press Ctrl+C to copy the selected source.'); }
  });
  $('#libTry').addEventListener('click', () => {
    const lib = REG.get(openId);
    if (lib) APP.importIntoNotebook(lib.name);
  });
  $('#libSave').addEventListener('click', () => {
    const lib = REG.get(openId);
    if (!lib || lib.builtin) return;
    const u = USER_LIBS.find(x => x.id === lib.id);
    u.source = APP.libEditor.ta.value;
    saveUserLibs();
    rebuildRegistry();
    const entry = [...REG.values()].find(e => e.id === u.id);
    openLib(entry.key);
    if (!entry.error) {
      setLibMsg('ok', `Saved. Notebooks can now use import ${entry.name}.`);
      APP.run();
    }
  });
  $('#libDelete').addEventListener('click', ev => {
    const btn = ev.currentTarget;
    if (!btn.classList.contains('confirm')) {
      btn.classList.add('confirm');
      btn.textContent = 'Delete permanently';
      setLibMsg('', 'Press again to delete this library from this browser.');
      return;
    }
    const lib = REG.get(openId);
    USER_LIBS = USER_LIBS.filter(x => x.id !== lib.id);
    saveUserLibs();
    rebuildRegistry();
    closeLib();
  });
}

Object.assign(APP, { rebuildRegistry, renderLibList, wireLibraries: wire });
})();
