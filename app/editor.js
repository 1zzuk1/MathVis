/* Theorem Sketchpad UI — editors: syntax highlighting, line numbers and autocomplete. */
'use strict';
(function () {
const APP = window.APP = window.APP || {};
const { esc } = MV;

function h(tag, cls, text) {
  const el = document.createElement(tag);
  if (cls) el.className = cls;
  if (text != null) el.textContent = text;
  return el;
}
APP.h = h;
APP.store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v == null ? d : v; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem(k, v); } catch (e) { /* storage unavailable */ } },
};

const NOTATION_RE = /(#.*)|\b(forall|exists|in|notin|and|or|not|if|then|else|mod|implies|iff|let|def|theorem|lemma|claim|conjecture|check|plot|show|explain|vary|structure|concept|interpret|extends|as|proof|diagram|commutes|exact|case|otherwise|induction|contradiction|assume|suppose|choose|have|hence|so|thus|therefore|such|that|for|import|library|true|false|where|lim|sum|prod|sup|inf|max|min|subset|union|inter)\b|(?<![A-Za-z_\d.])(\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)|(:=|=>|<->|->|<=|>=|!=|\.\.|[∀∃∈∉≤≥≠≈→⇒↔⇔∧∨¬√↦|⊆⊂∪∩∖∑∏²³ⁿ])/g;
const JS_RE = /(\/\/.*|\/\*[\s\S]*?\*\/)|('(?:\\.|[^'\\\n])*'|"(?:\\.|[^"\\\n])*"|`(?:\\.|[^`\\])*`)|\b(const|let|var|function|return|if|else|for|while|of|in|new|throw|class|this|true|false|null|undefined|typeof|instanceof)\b|(?<![A-Za-z_\d.])(\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)/g;

function highlight(text, lang) {
  const re = lang === 'js' ? JS_RE : NOTATION_RE;
  re.lastIndex = 0;
  let out = '', last = 0, m;
  while ((m = re.exec(text))) {
    out += esc(text.slice(last, m.index));
    const cls = lang === 'js'
      ? (m[1] ? 'hc' : m[2] ? 'hs' : m[3] ? 'hk' : 'hn')
      : (m[1] ? 'hc' : m[2] ? 'hk' : m[3] ? 'hn' : 'ho');
    out += `<span class="${cls}">${esc(m[0])}</span>`;
    last = re.lastIndex;
  }
  return out + esc(text.slice(last)) + '\n';
}

let measureCtx = null;
function charWidth(ta) {
  if (!measureCtx) measureCtx = document.createElement('canvas').getContext('2d');
  const cs = getComputedStyle(ta);
  measureCtx.font = `${cs.fontWeight} ${cs.fontSize} ${cs.fontFamily}`;
  return measureCtx.measureText('MMMMMMMMMM').width / 10;
}

/* Rank completions: exact-case prefix matches first, then any-case prefix, then substring. */
function rank(all, word) {
  const lw = word.toLowerCase(), seen = new Set(), out = [];
  const tiers = [c => c.name.startsWith(word), c => c.name.toLowerCase().startsWith(lw), c => c.name.toLowerCase().includes(lw)];
  for (const t of tiers) for (const c of all) {
    if (seen.has(c.name) || c.name === word || !t(c)) continue;
    seen.add(c.name);
    out.push(c);
  }
  return out;
}

/* A textarea with a highlighted copy behind it, a line-number gutter and, if opts.complete is
   given, an autocomplete list of names with their documentation. With opts.findTopic, names whose
   documentation is about the typed word follow the names that match it, and "?topic words" lists
   only those. Accepting a name from a library that isn't imported calls opts.onImport(lib). */
function makeEditor(root, opts = {}) {
  const { onInput, onRun, complete, findTopic, onImport } = opts;
  const ta = root.querySelector('textarea'), hl = root.querySelector('.hl'), gut = root.querySelector('.gut');
  const ed = {
    ta, lang: opts.lang || 'notation', errors: new Set(),
    refresh() {
      hl.innerHTML = highlight(ta.value, ed.lang);
      const n = ta.value.split('\n').length;
      let g = '';
      for (let i = 1; i <= n; i++) g += ed.errors.has(i) ? `<span class="err">${i}</span>\n` : i + '\n';
      gut.innerHTML = g;
      ed.sync();
    },
    sync() {
      hl.scrollTop = ta.scrollTop;
      hl.scrollLeft = ta.scrollLeft;
      gut.style.transform = `translateY(${-ta.scrollTop}px)`;
    },
    set(v) { ta.value = v; ta.scrollTop = 0; ed.refresh(); },
  };

  // ---- autocomplete ----
  const pop = h('div', 'complete');
  pop.hidden = true;
  pop.setAttribute('role', 'listbox');
  root.querySelector('.code').append(pop);
  let items = [], sel = 0, wordStart = 0;
  const close = () => { pop.hidden = true; items = []; };
  const draw = () => {
    pop.replaceChildren();
    items.forEach((c, i) => {
      const row = h('div', 'ci' + (i === sel ? ' sel' : '') + (c.topic ? ' topic' : ''));
      row.setAttribute('role', 'option');
      row.append(h('span', 'cn', c.name), h('span', 'ck', c.kind || ''));
      if (i === sel) requestAnimationFrame(() => row.scrollIntoView({ block: 'nearest' }));
      row.addEventListener('mousedown', ev => { ev.preventDefault(); accept(i); });
      pop.append(row);
    });
    const doc = items[sel] && items[sel].doc;
    if (doc) pop.append(h('div', 'cdoc', doc));
  };
  const accept = i => {
    const c = items[i];
    if (!c) return;
    // A view on an otherwise empty line is written as "show view(".
    const lineStart = ta.value.lastIndexOf('\n', wordStart - 1) + 1;
    const alone = !ta.value.slice(lineStart, wordStart).trim();
    ta.setRangeText(c.insert || (c.view && alone ? `show ${c.name}(` : c.name), wordStart, ta.selectionStart, 'end');
    close();
    if (c.lib && onImport) onImport(c.lib);
    ta.dispatchEvent(new Event('input'));
    close();
  };
  const update = () => {
    if (!complete) return;
    const pos = ta.selectionStart;
    if (pos !== ta.selectionEnd) return close();
    const before = ta.value.slice(0, pos);
    const line = before.slice(before.lastIndexOf('\n') + 1);
    if (line.includes('#')) return close();
    // "?topic words": library names about the topic.
    const q = findTopic && /\?([\p{L}][\p{L}\p{N}_ ]*)$/u.exec(line);
    let word;
    if (q) {
      word = q[0];
      wordStart = pos - word.length;
      items = findTopic(q[1]).slice(0, 14).map(c => ({ ...c, topic: true }));
    } else {
      const m = /[\p{L}_][\p{L}\p{N}_']*$/u.exec(line);
      if (!m || m[0].length < 2) return close();
      word = m[0];
      wordStart = pos - word.length;
      items = rank(complete(), word).slice(0, 8);
      // Then names whose documentation is about the word (derivative → grad, jacobian…).
      if (findTopic && word.length >= 3) {
        const have = new Set(items.map(c => c.name));
        for (const c of findTopic(word)) if (items.length < 12 && !have.has(c.name) && c.name !== word) { items.push({ ...c, topic: true }); have.add(c.name); }
      }
    }
    if (!items.length) return close();
    sel = 0;
    draw();
    pop.hidden = false;
    const cs = getComputedStyle(ta), lh = parseFloat(cs.lineHeight) || 21;
    const row = before.split('\n').length - 1, col = line.length - word.length;
    const left = parseFloat(cs.paddingLeft) + col * charWidth(ta) - ta.scrollLeft;
    const top = parseFloat(cs.paddingTop) + (row + 1) * lh - ta.scrollTop + 2;
    const maxLeft = Math.max(0, root.querySelector('.code').clientWidth - pop.offsetWidth - 8);
    pop.style.left = Math.max(4, Math.min(left, maxLeft)) + 'px';
    pop.style.top = top + 'px';
  };

  ta.addEventListener('input', () => { ed.refresh(); update(); if (onInput) onInput(); });
  ta.addEventListener('scroll', () => { ed.sync(); if (!pop.hidden) update(); });
  ta.addEventListener('blur', () => setTimeout(close, 100));
  ta.addEventListener('click', close);
  ta.addEventListener('keydown', ev => {
    if (!pop.hidden && items.length) {
      if (ev.key === 'ArrowDown' || ev.key === 'ArrowUp') {
        ev.preventDefault();
        sel = (sel + (ev.key === 'ArrowDown' ? 1 : items.length - 1)) % items.length;
        draw();
        return;
      }
      if (ev.key === 'Enter' || ev.key === 'Tab') { ev.preventDefault(); accept(sel); return; }
      if (ev.key === 'Escape') { ev.preventDefault(); close(); return; }
    }
    if ((ev.ctrlKey || ev.metaKey) && ev.key === 'Enter' && onRun) { ev.preventDefault(); onRun(); return; }
    if ((ev.ctrlKey || ev.metaKey) && ev.key === ' ') { ev.preventDefault(); update(); return; }
    if (ev.key === 'Tab' && !ev.shiftKey) {
      ev.preventDefault();
      ta.setRangeText('  ', ta.selectionStart, ta.selectionEnd, 'end');
      ta.dispatchEvent(new Event('input'));
    }
  });
  return ed;
}

APP.highlight = highlight;
APP.makeEditor = makeEditor;
})();
