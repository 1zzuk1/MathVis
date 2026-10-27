/* Theorem Sketchpad UI — result cards, the context views draw with, thumbnails of objects,
   evaluation trees ("why?") and plain-English readings of formulas. */
'use strict';
(function () {
const APP = window.APP;
const { h } = APP;
const { MVError, esc, fmt, locate, pp, ppText, ppBinders, Figure, FIGS } = MV;

let CARD_ID = 0;
APP.FOLDED = new Set();
APP.activeCtls = new Set();   // running analyses, so Run can stop them all

/* A result card. stmt gives the line link; container defaults to the results column. */
function makeCard(stmt, kind, name, container) {
  const id = ++CARD_ID;
  const el = h('article', 'card');
  const head = h('header', 'card-head');
  // Fold to the headline and formula; remembered by statement text across runs.
  const foldKey = stmt && stmt.text ? stmt.text.trim() : null;
  const fold = h('button', 'fold-btn');
  fold.type = 'button';
  fold.title = 'Fold or unfold this result';
  head.append(fold, h('span', 'kind', kind));
  if (name) head.append(h('span', 'name', name));
  const chip = h('span', 'chip');
  chip.hidden = true;
  head.append(chip);
  if (stmt && stmt.line) {
    const lineBtn = h('button', 'line-link', stmt.line === stmt.endLine ? `line ${stmt.line}` : `lines ${stmt.line}–${stmt.endLine}`);
    lineBtn.type = 'button';
    lineBtn.title = 'Show this statement in the editor';
    lineBtn.addEventListener('click', () => APP.gotoLine(stmt.line, stmt.endLine));
    head.append(lineBtn);
  }
  const formula = h('div', 'formula'), docEl = h('p', 'doc'), extra = h('div', 'card-extra'), unfold = h('div', 'unfold'), params = h('div', 'params'), body = h('div', 'card-body'), actions = h('div', 'card-actions');
  formula.hidden = unfold.hidden = docEl.hidden = params.hidden = actions.hidden = true;
  el.append(head, formula, docEl, extra, unfold, params, body, actions);
  (container || APP.OUT).append(el);
  const card = {
    id, el, head, body, extra, paramsEl: params, figs: [], status: null, kind, stmt,
    setStatus(k, text) { chip.hidden = false; chip.className = 'chip ' + k; chip.textContent = text; card.status = k; },
    formula(html) { formula.innerHTML = html; formula.hidden = false; },
    unfolded(html, bindings) {
      unfold.innerHTML = `<span class="tag">unfolds to</span><span class="f">${html}</span>` +
        (bindings && bindings.length ? `<span class="with">with ${bindings.map(([p, v]) => `${pp({ type: 'id', name: p })} = ${esc(fmt(v))}`).join(', ')}</span>` : '');
      unfold.hidden = false;
    },
    doc(text) { docEl.textContent = text; docEl.hidden = false; },
    action(label, fn, title) {
      const b = h('button', 'btn small', label);
      b.type = 'button';
      if (title) b.title = title;
      b.addEventListener('click', fn);
      actions.append(b);
      actions.hidden = false;
      return b;
    },
    clearActions() { actions.replaceChildren(); actions.hidden = true; },
    setFolded(on) {
      el.classList.toggle('folded', on);
      fold.setAttribute('aria-expanded', String(!on));
      if (foldKey && !container) { if (on) APP.FOLDED.add(foldKey); else APP.FOLDED.delete(foldKey); }
      // Figures drawn while folded had no width: draw them again.
      if (!on) for (const fg of card.figs) { try { fg.render(); } catch (e) { /* redrawn on the next run */ } }
    },
    /* A progress line with a Stop button; returns the controller analyses report to. */
    progress(what = 'Checking') {
      const box = h('div', 'progress');
      const bar = h('div', 'bar'), fill = h('i');
      bar.append(fill);
      const text = h('span', 'progress-text', what + '…');
      const stop = h('button', 'btn small', 'Stop');
      stop.type = 'button';
      box.append(bar, text, stop);
      body.append(box);
      const ctl = {
        cancelled: false,
        onProgress(step) {
          if (!step) return;
          if (step.total) { fill.style.width = (100 * step.done / step.total).toFixed(1) + '%'; }
          const words = { sampling: 'Checking', searching: 'Searching for a counterexample', simplifying: 'Simplifying the counterexample', variations: 'Checking variations' };
          text.textContent = (words[step.phase] || what) + (step.total ? ` ${step.done.toLocaleString('en-US')} of ${step.total.toLocaleString('en-US')}` : '') + '…';
        },
        done() { box.remove(); APP.activeCtls.delete(ctl); },
      };
      stop.addEventListener('click', () => { ctl.cancelled = true; text.textContent = 'Stopping…'; });
      APP.activeCtls.add(ctl);
      return ctl;
    },
    clearBody() {
      for (const f of card.figs) FIGS.delete(f);
      card.figs = [];
      body.replaceChildren();
    },
    error(err) {
      if (err && err.message === 'Stopped.') { card.setStatus('info', 'Stopped'); body.append(h('p', 'note', 'Stopped before it finished.')); return; }
      const loc = locate(stmt && stmt.text ? stmt : null, err.pos);
      card.setStatus('error', 'Error');
      const p = h('p', 'error-msg');
      if (loc && loc.line) p.append(h('strong', null, `Line ${loc.line}: `));
      p.append(document.createTextNode(err.message));
      body.append(p);
      if (loc && loc.col != null) body.append(h('pre', 'err-src', `${loc.text}\n${' '.repeat(loc.col)}^`));
      if (loc && loc.line && APP.editor) APP.editor.errors.add(loc.line);
    },
  };
  el.card = card;
  fold.addEventListener('click', () => card.setFolded(!el.classList.contains('folded')));
  card.setFolded(!!(foldKey && !container && APP.FOLDED.has(foldKey)));
  return card;
}

const SWATCH_TOKENS = /^(c[1-6]|pos|neg|vac|undef|accent|ink|muted|faint)$/;
function swatch(color, ring) {
  const sw = h('i', 'sw' + (ring ? ' ring' : ''));
  const col = SWATCH_TOKENS.test(color) ? `var(--${color})` : color;
  if (ring) sw.style.borderColor = col; else sw.style.background = col;
  return sw;
}

function makeCtx(card, state = {}, redraw = null, host = null) {
  const into = host || card.body;
  return {
    figure(o = {}) { const f = new Figure(into, o); card.figs.push(f); return f; },
    figure3d(o = {}) { const f = new MV.Figure3D(into, o); card.figs.push(f); return f; },
    diagram(o = {}) { const f = new MV.Diagram(into, o); card.figs.push(f); return f; },
    param(name, spec = {}) {
      if (!(name in state)) {
        state[name] = spec.value ?? spec.min ?? 0;
        const id = `p${card.id}-${String(name).replace(/[^\w]/g, '_')}-${Object.keys(state).length}`;
        const lab = h('label', 'param');
        lab.htmlFor = id;
        lab.append(h('span', 'pname', name));
        const input = document.createElement('input');
        Object.assign(input, { type: 'range', id, min: spec.min ?? 0, max: spec.max ?? 1, step: spec.step ?? 0.01, value: state[name] });
        const out = h('output', null, fmt(state[name]));
        let pending = false;
        input.addEventListener('input', () => {
          state[name] = +input.value;
          out.textContent = fmt(state[name]);
          if (redraw && !pending) { pending = true; requestAnimationFrame(() => { pending = false; redraw(); }); }
        });
        lab.append(input, out);
        card.paramsEl.append(lab);
        card.paramsEl.hidden = false;
      }
      return state[name];
    },
    // Something a view keeps while its sliders redraw it, such as the points clicked so far.
    memo(name, init) { const k = '\u0000' + name; if (!(k in state)) state[k] = init(); return state[k]; },
    // Draw the view again with the same state (after a click adds something).
    redraw() { if (redraw) redraw(); },
    legend(items) {
      const el = h('div', 'legend');
      for (const it of items) {
        const s = h('span', 'leg');
        s.append(swatch(it.color, it.ring), document.createTextNode(it.label));
        el.append(s);
      }
      into.append(el);
    },
    note(text, cls) { into.append(h('p', 'note' + (cls ? ' ' + cls : ''), String(text))); },
    // Figures side by side (stacked on a narrow screen): row().figure(…), row().figure(…).
    row() { const d = h('div', 'fig-row'); into.append(d); return makeCtx(card, state, redraw, d); },
    // Library views can add their own markup (libraries are code the user chose to load).
    html(markup) { const d = h('div', 'view-html'); d.innerHTML = markup; into.append(d); return d; },
    status(kind, text) { card.setStatus(kind, String(text)); },
    table(headers, rows, caption, onRow) {
      const wrap = h('div', 'table-wrap');
      const t = h('table');
      if (caption) t.append(h('caption', null, caption));
      const tr = h('tr');
      headers.forEach(x => tr.append(h('th', null, x)));
      const thead = h('thead');
      thead.append(tr);
      const tbody = h('tbody');
      rows.forEach((row, i) => {
        const r = h('tr');
        row.forEach(x => r.append(h('td', null, x)));
        if (onRow) {
          r.className = 'clickable';
          r.tabIndex = 0;
          r.title = 'Show why';
          r.addEventListener('click', () => onRow(i));
          r.addEventListener('keydown', ev => { if (ev.key === 'Enter') onRow(i); });
        }
        tbody.append(r);
      });
      t.append(thead, tbody);
      wrap.append(t);
      into.append(wrap);
      return wrap;
    },
    format: fmt,
  };
}

function runView(card, view, args) {
  const state = {};
  const draw = () => {
    card.clearBody();
    try {
      view.render(makeCtx(card, state, draw), ...args);
      for (const f of card.figs) f.render();
    } catch (err) {
      card.error(err instanceof MVError ? err : new MVError(`The ${view.lib} library failed: ${err.message}`));
    }
  };
  draw();
}

/* ---------------- thumbnails of objects, for galleries ---------------- */

const isNumArr = v => Array.isArray(v) && v.length > 0 && v.every(x => typeof x === 'number');

function thumb(card, host, v) {
  const fig = o => { const f = new Figure(host, { static: true, xAxis: false, yAxis: false, ...o }); card.figs.push(f); return f; };
  try {
    for (const t of MV.THUMBS) {
      let ok = false;
      try { ok = t.test(v); } catch (e) { ok = false; }
      if (ok) { t.draw(fig, v, host); return true; }
    }
    if (v && v.__domain) {
      if (v.kind === 'finite' && v.values.length && v.values.every(isNumArr) && v.values[0].length === 2) {
        const xs = v.values.map(p => p[0]), ys = v.values.map(p => p[1]);
        const pad = Math.max(1, Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)) * 0.6;
        const cx = (Math.max(...xs) + Math.min(...xs)) / 2, cy = (Math.max(...ys) + Math.min(...ys)) / 2;
        fig({ x: [cx - pad, cx + pad], y: [cy - pad, cy + pad], square: true, height: 120 }).points(v.values, { color: 'c1', r: 4 });
        return true;
      }
      if (v.dim === 2 && v.window) {
        let w = v.window();
        if (!w || !Array.isArray(w[0])) w = [[-2, 2], [-2, 2]];
        // A set that fills its whole window (like ℝ²) is drawn in a fixed box.
        const big = w.some(([a, b]) => b - a > 12);
        if (big) w = [[-2.5, 2.5], [-2.5, 2.5]];
        fig({ x: w[0], y: w[1], square: true, height: 120 }).region(v, { color: 'c1', alpha: 0.55, n: 120 });
        return true;
      }
      if (v.dim === 1 && v.scalar) {
        const w = v.window && v.window();
        const x = w && typeof w[0] === 'number' && w[1] - w[0] < 12 ? [w[0] - (w[1] - w[0]) * 0.15 - 0.2, w[1] + (w[1] - w[0]) * 0.15 + 0.2] : [-1, 4];
        if (v.kind === 'finite') fig({ x, y: [0, 1], height: 56 }).points(v.values.map(p => [p, 0.5]), { color: 'c1', r: 4 });
        else fig({ x, y: [0, 1], height: 56 }).region(v, { color: 'c1', alpha: 0.75, n: 300 });
        return true;
      }
    }
    if (typeof v === 'function' && v.kindSensitive) {
      // Depends on rationality: dots at exact rationals and at exact irrationals.
      const xs = [...MV.EX.farey(-1.5, 1.5, 16, 300), ...MV.EX.sampleExact(-1.5, 1.5, false, false, 240)];
      const rat = [], irr = [];
      for (const x of xs) { let y; try { y = +v(x); } catch (e) { continue; } if (Number.isFinite(y)) (MV.EX.kindOf(x) === 'rational' ? rat : irr).push([+x, y]); }
      const f = fig({ x: [-1.6, 1.6], height: 110 });
      f.points(irr, { color: 'c2', r: 1.4, alpha: 0.7 });
      f.points(rat, { color: 'c1', r: 1.8 });
      return true;
    }
    if (typeof v === 'function' && !v.domainCtor) {
      const t1 = v(1);
      if (v.isSequence && typeof t1 === 'number') {
        const pts = [];
        for (let n = 1; n <= 30; n++) { const y = v(n); if (Number.isFinite(y)) pts.push([n, y]); }
        fig({ x: [0, 31], height: 110 }).points(pts, { color: 'c1', r: 2 });
        return true;
      }
      if (typeof t1 === 'number' || typeof v(0.5) === 'number') {
        fig({ x: [-3, 3], height: 110 }).curve(x => v(x), { color: 'c1', width: 1.8, n: 400 });
        return true;
      }
    }
  } catch (e) { /* no picture */ }
  return false;
}

/* ---------------- evaluation trees ---------------- */

function valueBadge(t) {
  if (t.err) return h('span', 'tv undef', '!');
  if (t.v === true) return h('span', 'tv ok', '✓');
  if (t.v === false) return h('span', 'tv fail', '✗');
  return h('span', 'tv num', '= ' + fmt(typeof t.v === 'number' ? +t.v.toPrecision(6) : t.v));
}

function renderTree(t) {
  const li = h('li');
  const line = h('div', 'tline');
  line.append(valueBadge(t));
  if (t.label) line.append(h('span', 'tlabel', t.label));
  const f = h('span', 'tf');
  f.innerHTML = pp(t.node);
  line.append(f);
  li.append(line);
  if (t.err) li.append(h('div', 'tnote', t.err));
  if (t.note) li.append(h('div', 'tnote', t.note));
  if (t.kids.length) {
    const ul = h('ul');
    t.kids.forEach(k => ul.append(renderTree(k)));
    li.append(ul);
  }
  return li;
}

/* Show the evaluation tree of node at env in a panel inside card (replacing an earlier one). */
function showTrace(card, title, node, env, depth = 1, exact = false) {
  let panel = card.el.querySelector('.trace');
  if (panel) panel.remove();
  panel = h('div', 'trace');
  const head = h('div', 'trace-head');
  head.append(h('strong', null, title));
  const close = h('button', 'link-btn', 'Close');
  close.type = 'button';
  close.addEventListener('click', () => panel.remove());
  head.append(close);
  panel.append(head);
  try {
    // A claim about rationality is evaluated with exact numbers, as it was checked.
    const before = MV.EXACT_SAMPLING;
    MV.EXACT_SAMPLING = exact;
    let t;
    try { t = MV.atDepth(depth, () => MV.trace(node, env)); } finally { MV.EXACT_SAMPLING = before; }
    const ul = h('ul', 'tree');
    ul.append(renderTree(t));
    panel.append(ul);
  } catch (err) {
    panel.append(h('p', 'error-msg', err.message));
  }
  card.body.append(panel);
  panel.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
}

/* ---------------- plain-English readings ---------------- */

function reading(node) {
  const line = (html, kids) => `<div class="rd"><div class="rd-line">${html}</div>${kids ? `<div class="rd-kids">${kids}</div>` : ''}</div>`;
  const word = w => `<span class="rd-word">${w}</span>`;
  const formula = n => `<span class="rd-f">${pp(n)}</span>`;
  const chain = (n, op) => n.type === 'bin' && n.op === op ? [...chain(n.a, op), ...chain(n.b, op)] : [n];
  const read = n => {
    switch (n.type) {
      case 'quant':
        return n.q === 'forall'
          ? line(`${word('for every')} <span class="rd-f">${ppBinders(n.binders, true)}</span>`, read(n.body))
          : line(`${word('there is')} <span class="rd-f">${ppBinders(n.binders, true)}</span> ${word('such that')}`, read(n.body));
      case 'bin':
        if (n.op === '->') return line(word('if'), read(n.a)) + line(word('then'), read(n.b));
        if (n.op === '<->') return read(n.a) + line(word('exactly when'), read(n.b));
        if (n.op === 'and' || n.op === 'or') return chain(n, n.op).map(read).join(line(word(n.op === 'and' ? 'and' : 'or')));
        return line(formula(n));
      case 'un':
        if (n.op === 'not') return line(word('it is not true that'), read(n.a));
        return line(formula(n));
      case 'where':
        return read(n.body) + line(`${word('where')} ${n.binds.map(b => `${pp({ type: 'id', name: b.name })} = ${pp(b.expr)}`).join(', ')}`);
      case 'subset':
        return line(`${formula(n.a)} ${word('lies inside')} ${formula(n.b)}`);
      default:
        return line(formula(n));
    }
  };
  return `<div class="reading">${read(node)}</div>`;
}

Object.assign(APP, { makeCard, makeCtx, runView, thumb, showTrace, reading, swatch, isNumArr });
})();
