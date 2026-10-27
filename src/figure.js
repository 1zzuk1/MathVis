/* Theorem Sketchpad — figures: a small canvas plotter that redraws itself for the theme and width. */
'use strict';
(function (global) {
const MV = global.MV;
const { fmtNum } = MV;
const minmax = arr => {
  let lo = Infinity, hi = -Infinity;
  for (const v of arr) { if (v < lo) lo = v; if (v > hi) hi = v; }
  return [lo, hi];
};


let THEME = null, THEME_STAMP = 0;
const RGB_CACHE = new Map();
function hexToRgb(c) {
  if (RGB_CACHE.has(c)) return RGB_CACHE.get(c);
  let m = /^#?([0-9a-f]{6})$/i.exec((c || '').trim()), out = [128, 128, 128];
  if (m) out = [0, 2, 4].map(i => parseInt(m[1].slice(i, i + 2), 16));
  else if ((m = /^#?([0-9a-f]{3})$/i.exec((c || '').trim()))) out = [0, 1, 2].map(i => parseInt(m[1][i] + m[1][i], 16));
  RGB_CACHE.set(c, out);
  return out;
}
function theme() {
  if (THEME) return THEME;
  const cs = typeof getComputedStyle === 'function' ? getComputedStyle(document.documentElement) : null;
  const g = n => cs ? cs.getPropertyValue('--' + n).trim() : '#808080';
  const T = { stamp: ++THEME_STAMP, c: [1, 2, 3, 4, 5, 6].map(i => g('c' + i)) };
  for (const k of ['ink', 'muted', 'faint', 'line', 'panel', 'bg', 'accent', 'pos', 'neg', 'vac', 'undef']) T[k] = g(k);
  T.css = name => T[name] || (/^c\d$/.test(name) ? T.c[(+name[1] - 1) % 6] : name);
  T.rgb = name => hexToRgb(T.css(name));
  T.rgba = (name, a) => [...T.rgb(name), Math.round(a * 255)];
  return (THEME = T);
}
function resetTheme() { THEME = null; }

const FIGS = new Set();
const HINT = 'drag to pan · scroll to zoom · double-click to reset';

function niceStep(span, count) {
  const raw = span / Math.max(1, count), p = Math.pow(10, Math.floor(Math.log10(raw))), m = raw / p;
  return (m < 1.5 ? 1 : m < 3 ? 2 : m < 7 ? 5 : 10) * p;
}
function tickLabel(v, step) {
  if (Math.abs(v) < step * 1e-9) return '0';
  const a = Math.abs(v);
  if (a >= 1e6 || a < 1e-4) return fmtNum(v);
  const dec = Math.max(0, Math.min(6, -Math.floor(Math.log10(step) + 1e-9)));
  return v.toFixed(dec).replace(/^-/, '−');
}
function robustRange(arr) {
  if (arr.length < 50) return minmax(arr);
  const s = Float64Array.from(arr).sort();
  const q = Math.floor(s.length * 0.01);
  const lo = s[q], hi = s[s.length - 1 - q], span = Math.max(hi - lo, 1e-12);
  return [(lo - s[0]) > 3 * span ? lo : s[0], (s[s.length - 1] - hi) > 3 * span ? hi : s[s.length - 1]];
}

class Figure {
  constructor(host, o = {}) {
    this.o = o; this.cmds = []; this.xs = []; this.ys = [];
    this.wrap = document.createElement('div');
    this.wrap.className = 'fig';
    this.canvas = document.createElement('canvas');
    this.read = document.createElement('div');
    this.read.className = 'readout';
    this.wrap.append(this.canvas, this.read);
    host.appendChild(this.wrap);
    this.view = null;        // the zoomed ranges [xr, yr], or null for the original view
    this.canvas.addEventListener('pointermove', ev => this.hover(ev));
    this.canvas.addEventListener('pointerleave', () => { this.read.textContent = ''; });
    if (!o.static) this.interactive();
    FIGS.add(this);
  }

  /* Zoom and pan: drag to pan, scroll (after clicking the figure, or with Ctrl) or pinch to zoom,
     double-click to reset. Curves and shaded regions are re-evaluated for the new view. */
  interactive() {
    const w = this.wrap, cv = this.canvas;
    w.classList.add('zoomable');
    const bar = document.createElement('div');
    bar.className = 'fig-tools';
    const btn = (label, title, fn) => {
      const b = document.createElement('button');
      b.type = 'button'; b.textContent = label; b.title = title;
      b.addEventListener('click', ev => { ev.stopPropagation(); fn(); });
      bar.append(b);
      return b;
    };
    btn('+', 'Zoom in', () => this.zoomBy(0.6));
    btn('−', 'Zoom out', () => this.zoomBy(1 / 0.6));
    this.resetBtn = btn('Reset', 'Back to the original view (or double-click)', () => this.setView(null));
    this.sampleBtn = btn('Sample this view', 'Check the claim again, sampling only inside this view', () => this.o.onResample && this.o.onResample(this.view));
    btn('Copy', 'Copy the picture as an image', () => this.copyImage());
    this.hint = document.createElement('span');
    this.hint.className = 'fig-hint';
    this.hint.textContent = HINT;
    bar.append(this.hint);
    w.append(bar);
    this.syncTools();
    const pointers = new Map();
    let drag = null, pinch = null;
    cv.addEventListener('pointerdown', ev => {
      if (!this.tf) return;
      pointers.set(ev.pointerId, [ev.clientX, ev.clientY]);
      cv.setPointerCapture(ev.pointerId);
      Figure.activate(this);
      if (pointers.size === 1) drag = { x: ev.clientX, y: ev.clientY, view: this.current(), moved: false };
      else if (pointers.size === 2) {
        const [a, b] = [...pointers.values()];
        pinch = { d: Math.hypot(a[0] - b[0], a[1] - b[1]) || 1, view: this.current(), mid: [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2] };
        drag = null;
      }
    });
    cv.addEventListener('pointermove', ev => {
      if (!pointers.has(ev.pointerId)) return;
      pointers.set(ev.pointerId, [ev.clientX, ev.clientY]);
      const { pw, ph } = this.tf;
      if (pinch && pointers.size === 2) {
        const [a, b] = [...pointers.values()];
        const d = Math.hypot(a[0] - b[0], a[1] - b[1]) || 1;
        this.zoomAround(pinch.mid[0], pinch.mid[1], pinch.d / d, pinch.view, true);
      } else if (drag) {
        const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y;
        if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true;
        if (!drag.moved) return;
        const [xr, yr] = drag.view;
        const sx = (xr[1] - xr[0]) / pw, sy = (yr[1] - yr[0]) / ph;
        const fixY = this.o.yAxis === false;
        this.setView([[xr[0] - dx * sx, xr[1] - dx * sx], fixY ? yr : [yr[0] + dy * sy, yr[1] + dy * sy]], true);
      }
    });
    const end = ev => {
      pointers.delete(ev.pointerId);
      if (pointers.size < 2) pinch = null;
      if (!pointers.size) { const moved = drag && drag.moved; drag = null; if (moved || this.interacting) this.settle(); }
    };
    cv.addEventListener('pointerup', ev => {
      const click = drag && !drag.moved && pointers.size === 1;
      end(ev);
      if (click && this.o.pick) { const w = this.toWorld(ev); if (w) this.o.pick(w[0], w[1]); }
    });
    cv.addEventListener('pointercancel', end);
    cv.addEventListener('wheel', ev => {
      if (!this.tf || !(Figure.active === this || ev.ctrlKey || ev.metaKey)) return;
      ev.preventDefault();
      this.zoomAround(ev.clientX, ev.clientY, Math.pow(1.0018, ev.deltaY * (ev.deltaMode ? 30 : 1)), this.current(), true);
      clearTimeout(this.wheelTimer);
      this.wheelTimer = setTimeout(() => this.settle(), 180);
    }, { passive: false });
    cv.addEventListener('dblclick', () => this.setView(null));
  }
  static activate(fig) {
    if (Figure.active && Figure.active !== fig) Figure.active.wrap.classList.remove('active');
    Figure.active = fig;
    fig.wrap.classList.add('active');
  }
  current() { return this.view || this.base || [this.o.x || [-1, 1], this.o.y || [-1, 1]]; }
  syncTools() {
    if (!this.resetBtn) return;
    this.resetBtn.hidden = !this.view;
    this.sampleBtn.hidden = !(this.view && this.o.onResample);
  }
  setView(v, interacting = false) {
    this.view = v;
    this.interacting = interacting;
    this.syncTools();
    if (!interacting) { this.render(); return; }
    if (!this.raf) this.raf = requestAnimationFrame(() => { this.raf = 0; this.render(); });
  }
  settle() { this.interacting = false; this.render(); }
  zoomBy(f) {
    if (!this.tf) return;
    const { m, pw, ph } = this.tf;
    const r = this.canvas.getBoundingClientRect();
    this.zoomAround(r.left + m.l + pw / 2, r.top + m.t + ph / 2, f, this.current(), false);
  }
  zoomAround(cx, cy, f, from, interacting) {
    if (!this.tf) return;
    const r = this.canvas.getBoundingClientRect();
    const { m, pw, ph } = this.tf;
    const [xr, yr] = from;
    const px = Math.max(0, Math.min(1, (cx - r.left - m.l) / pw)), py = Math.max(0, Math.min(1, (cy - r.top - m.t) / ph));
    const dx = xr[0] + px * (xr[1] - xr[0]), dy = yr[1] - py * (yr[1] - yr[0]);
    const span = (xr[1] - xr[0]) * f;
    if (span < 1e-12 * Math.max(1, Math.abs(dx)) || span > 1e9) return;
    const nx = [dx - (dx - xr[0]) * f, dx + (xr[1] - dx) * f];
    const ny = this.o.yAxis === false ? yr : [dy - (dy - yr[0]) * f, dy + (yr[1] - dy) * f];
    this.setView([nx, ny], interacting);
  }
  async copyImage() {
    try {
      const blob = await new Promise(res => this.canvas.toBlob(res, 'image/png'));
      await navigator.clipboard.write([new ClipboardItem({ 'image/png': blob })]);
      this.flash('Copied');
    } catch (e) { this.flash('This page isn’t allowed to copy images'); }
  }
  flash(text) {
    this.hint.textContent = text;
    clearTimeout(this.flashTimer);
    this.flashTimer = setTimeout(() => { this.hint.textContent = HINT; }, 1600);
  }
  track(pts) {
    for (const p of pts) if (p) {
      if (Number.isFinite(p[0])) this.xs.push(p[0]);
      if (Number.isFinite(p[1])) this.ys.push(p[1]);
    }
  }
  xRange() { return this.o.x || (this.xs.length ? minmax(this.xs) : [-1, 1]); }
  curve(src, st = {}) {
    let pts;
    if (typeof src === 'function') {
      const [a, b] = this.xRange(), n = st.n || 800;
      pts = [];
      for (let k = 0; k <= n; k++) {
        const x = a + (b - a) * k / n;
        let y;
        try { y = src(x); } catch (e) { y = NaN; }
        pts.push(typeof y === 'number' && Number.isFinite(y) ? [x, y] : null);
      }
    } else pts = src.map(p => p && Number.isFinite(p[0]) && Number.isFinite(p[1]) ? p : null);
    this.cmds.push({ k: 'curve', pts, st, fn: typeof src === 'function' ? src : null });
    if (st.track !== false) this.track(pts);
    return this;
  }
  points(pts, st = {}) {
    pts = pts.filter(p => p && Number.isFinite(p[0]) && Number.isFinite(p[1]));
    this.cmds.push({ k: 'points', pts, st });
    if (st.track !== false) this.track(pts);
    return this;
  }
  seg(x0, y0, x1, y1, st = {}) { this.cmds.push({ k: 'seg', a: [x0, y0], b: [x1, y1], st }); this.track([[x0, y0], [x1, y1]]); return this; }
  arrow(x0, y0, x1, y1, st = {}) { this.cmds.push({ k: 'arrow', a: [x0, y0], b: [x1, y1], st }); this.track([[x0, y0], [x1, y1]]); return this; }
  poly(pts, st = {}) { this.cmds.push({ k: 'poly', pts, st }); this.track(pts); return this; }
  rect(x0, y0, x1, y1, st = {}) { this.cmds.push({ k: 'rect', r: [x0, y0, x1, y1], st }); this.track([[x0, y0], [x1, y1]]); return this; }
  cells(list, st = {}) { this.cmds.push({ k: 'cells', list, st }); return this; }
  circle(cx, cy, r, st = {}) { this.cmds.push({ k: 'circle', c: [cx, cy], r, st }); this.track([[cx - r, cy - r], [cx + r, cy + r]]); return this; }
  // Shade a set of the plane (or of the line) over the figure's x and y ranges.
  region(set, st = {}) {
    const S = MV.toDomain(set);
    const two = S.dim === 2;
    const x = this.o.x || (two ? S.window()[0] : S.window());
    const y = this.o.y || (two ? S.window()[1] : [0, 1]);
    const n = st.n || (two ? 220 : 600);
    const rgba = st.color || 'c1', a = st.alpha ?? 0.22;
    this.raster({
      x, y, nx: n, ny: two ? n : 1, smooth: false,
      value: two ? (px, py) => S.contains([px, py]) : px => S.contains(px),
      color: (v, theme) => v ? theme.rgba(rgba, a) : null,
    });
    return this;
  }
  hband(y0, y1, st = {}) { this.cmds.push({ k: 'hband', y0, y1, st }); this.ys.push(y0, y1); return this; }
  vband(x0, x1, st = {}) { this.cmds.push({ k: 'vband', x0, x1, st }); return this; }
  text(x, y, s, st = {}) { this.cmds.push({ k: 'text', x, y, s: String(s), st }); return this; }
  raster(o) {
    const nx = o.nx || 200, ny = o.ny || 200, [x0, x1] = o.x, [y0, y1] = o.y;
    const vals = new Array(nx * ny);
    for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
      vals[j * nx + i] = o.value(x0 + (i + 0.5) * (x1 - x0) / nx, y1 - (j + 0.5) * (y1 - y0) / ny);
    }
    this.cmds.push({ k: 'raster', o, nx, ny, vals, ext: [o.x, o.y], stats: o.stats ? o.stats(vals, nx, ny) : null });
    return vals;
  }

  ranges(pw, ph) {
    if (this.view) return [this.view[0].slice(), this.view[1].slice()];
    let xr = this.o.x ? this.o.x.slice() : (this.xs.length ? minmax(this.xs) : [-1, 1]);
    let yr;
    if (this.o.y) yr = this.o.y.slice();
    else {
      yr = this.ys.length ? robustRange(this.ys) : [-1, 1];
      if (yr[1] - yr[0] < 1e-12) yr = [yr[0] - 1, yr[1] + 1];
      const pad = (yr[1] - yr[0]) * 0.07;
      yr = [yr[0] - pad, yr[1] + pad];
    }
    if (xr[1] - xr[0] < 1e-12) xr = [xr[0] - 1, xr[1] + 1];
    if (this.o.square) {
      const sx = (xr[1] - xr[0]) / pw, sy = (yr[1] - yr[0]) / ph;
      if (sx > sy) { const c = (yr[0] + yr[1]) / 2, h = sx * ph / 2; yr = [c - h, c + h]; }
      else { const c = (xr[0] + xr[1]) / 2, h = sy * pw / 2; xr = [c - h, c + h]; }
    }
    return [xr, yr];
  }

  /* Small static pictures (gallery thumbnails) are drawn only once they scroll into view, a few
     at a time between moments for the page: a gallery of 150 pathological functions would
     otherwise hold the page for seconds. */
  render() {
    if (!this.wrap.isConnected) return;
    if (this.o.static && typeof IntersectionObserver === 'function' && !this.seen) { Figure.watch(this); return; }
    this.draw();
  }
  static watch(fig) {
    if (!Figure.io) {
      Figure.io = new IntersectionObserver(entries => {
        for (const e of entries) {
          if (!e.isIntersecting) continue;
          Figure.io.unobserve(e.target);
          const f = e.target.__fig;
          if (f) { f.seen = true; Figure.queue.add(f); }
        }
        Figure.drain();
      }, { rootMargin: '300px' });
    }
    fig.wrap.__fig = fig;
    Figure.io.observe(fig.wrap);
  }
  static async drain() {
    if (Figure.draining) return;
    Figure.draining = true;
    try {
      while (Figure.queue.size) {
        const t = performance.now();
        for (const f of Figure.queue) {
          Figure.queue.delete(f);
          f.draw();
          if (performance.now() - t > 12) break;
        }
        if (Figure.queue.size && MV.yieldNow) await MV.yieldNow();
      }
    } finally { Figure.draining = false; }
  }
  draw() {
    if (!this.wrap.isConnected) return;
    const T = theme();
    const W = Math.max(this.o.static ? 80 : 200, Math.floor(this.wrap.clientWidth || 600));
    const showX = this.o.xAxis !== false, showY = this.o.yAxis !== false;
    const m = { l: showY ? 50 : 10, r: 12, t: 10, b: showX ? 26 : 10 };
    const pw = W - m.l - m.r;
    let ph;
    if (this.o.height) ph = this.o.height - m.t - m.b;
    else if (this.o.square) ph = Math.min(pw, 420);
    else ph = Math.round(Math.min(340, Math.max(190, pw * 0.55)));
    const H = ph + m.t + m.b;
    const dpr = global.devicePixelRatio || 1;
    const cv = this.canvas;
    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
    cv.style.width = W + 'px'; cv.style.height = H + 'px';
    const g = cv.getContext('2d');
    g.setTransform(dpr, 0, 0, dpr, 0, 0);
    g.clearRect(0, 0, W, H);
    const [xr, yr] = this.ranges(pw, ph);
    if (!this.view) this.base = [xr.slice(), yr.slice()];
    const X = x => m.l + (x - xr[0]) / (xr[1] - xr[0]) * pw;
    const Y = y => m.t + ph - (y - yr[0]) / (yr[1] - yr[0]) * ph;
    const clampY = v => Math.max(-1e5, Math.min(1e5, v));
    this.tf = { m, pw, ph, xr, yr };

    // grid and ticks
    g.font = '10.5px "JetBrains Mono", ui-monospace, monospace';
    g.lineWidth = 1;
    const xs = niceStep(xr[1] - xr[0], Math.max(2, pw / 84)), ys = niceStep(yr[1] - yr[0], Math.max(2, ph / 52));
    g.strokeStyle = T.line; g.fillStyle = T.muted;
    if (showX) {
      g.textAlign = 'center'; g.textBaseline = 'top';
      for (let v = Math.ceil(xr[0] / xs) * xs; v <= xr[1] + xs * 1e-9; v += xs) {
        const px = Math.round(X(v)) + 0.5;
        g.beginPath(); g.moveTo(px, m.t); g.lineTo(px, m.t + ph); g.stroke();
        g.fillText(tickLabel(v, xs), px, m.t + ph + 6);
      }
    }
    if (showY) {
      g.textAlign = 'right'; g.textBaseline = 'middle';
      for (let v = Math.ceil(yr[0] / ys) * ys; v <= yr[1] + ys * 1e-9; v += ys) {
        const py = Math.round(Y(v)) + 0.5;
        g.beginPath(); g.moveTo(m.l, py); g.lineTo(m.l + pw, py); g.stroke();
        g.fillText(tickLabel(v, ys), m.l - 7, py);
      }
    }
    g.strokeStyle = T.faint;
    if (showY && xr[0] < 0 && xr[1] > 0) { const px = Math.round(X(0)) + 0.5; g.beginPath(); g.moveTo(px, m.t); g.lineTo(px, m.t + ph); g.stroke(); }
    if (showX && yr[0] < 0 && yr[1] > 0) { const py = Math.round(Y(0)) + 0.5; g.beginPath(); g.moveTo(m.l, py); g.lineTo(m.l + pw, py); g.stroke(); }

    g.save();
    g.beginPath(); g.rect(m.l, m.t, pw, ph); g.clip();
    for (const c of this.cmds) {
      const st = c.st || {};
      g.globalAlpha = st.alpha ?? 1;
      const col = T.css(st.color || 'accent');
      g.strokeStyle = col; g.fillStyle = col;
      g.lineWidth = st.width || 2;
      g.setLineDash(st.dash || []);
      switch (c.k) {
        case 'curve': {
          // A curve given by a function is sampled again for a zoomed view.
          if (c.fn && this.view) {
            const key = xr.join();
            if (c.key !== key) {
              const n = c.st.n || 800, pts = [];
              for (let k = 0; k <= n; k++) {
                const x = xr[0] + (xr[1] - xr[0]) * k / n;
                let y;
                try { y = c.fn(x); } catch (e) { y = NaN; }
                pts.push(typeof y === 'number' && Number.isFinite(y) ? [x, y] : null);
              }
              c.zpts = pts; c.key = key;
            }
          }
          g.lineJoin = 'round'; g.lineCap = 'round';
          g.beginPath();
          let pen = false, py = 0;
          const jump = (yr[1] - yr[0]) * 3;
          for (const p of (c.fn && this.view ? c.zpts : c.pts)) {
            if (!p) { pen = false; continue; }
            if (pen && Math.abs(p[1] - py) > jump) pen = false;
            const sx = X(p[0]), sy = clampY(Y(p[1]));
            if (pen) g.lineTo(sx, sy); else g.moveTo(sx, sy);
            pen = true; py = p[1];
          }
          g.stroke();
          break;
        }
        case 'points': {
          const r = st.r || 2.5;
          // hollow: an open dot (a point left out, as at the open end of an interval).
          for (const p of c.pts) {
            g.beginPath(); g.arc(X(p[0]), clampY(Y(p[1])), r, 0, 6.2832);
            if (st.hollow) { const fs = g.fillStyle; g.fillStyle = T.css('panel'); g.fill(); g.fillStyle = fs; g.lineWidth = st.width || 1.6; g.stroke(); } else g.fill();
          }
          break;
        }
        case 'seg': case 'arrow': {
          const [x0, y0] = [X(c.a[0]), Y(c.a[1])], [x1, y1] = [X(c.b[0]), Y(c.b[1])];
          g.beginPath(); g.moveTo(x0, y0); g.lineTo(x1, y1); g.stroke();
          if (c.k === 'arrow') {
            const ang = Math.atan2(y1 - y0, x1 - x0), L = 9;
            g.setLineDash([]);
            g.beginPath(); g.moveTo(x1, y1);
            g.lineTo(x1 - L * Math.cos(ang - 0.4), y1 - L * Math.sin(ang - 0.4));
            g.lineTo(x1 - L * Math.cos(ang + 0.4), y1 - L * Math.sin(ang + 0.4));
            g.closePath(); g.fill();
          }
          break;
        }
        case 'poly': {
          g.beginPath();
          c.pts.forEach((p, i) => i ? g.lineTo(X(p[0]), Y(p[1])) : g.moveTo(X(p[0]), Y(p[1])));
          g.closePath(); g.fill();
          if (st.stroke) { g.globalAlpha = 1; g.strokeStyle = T.css(st.stroke); g.lineWidth = st.strokeWidth || 1.5; g.stroke(); }
          break;
        }
        case 'rect': {
          const [x0, y0, x1, y1] = c.r;
          const a = X(Math.min(x0, x1)), b = Y(Math.max(y0, y1)), w = Math.abs(X(x1) - X(x0)), h = Math.abs(Y(y1) - Y(y0));
          g.fillRect(a, b, w, h);
          if (st.stroke) { g.globalAlpha = 1; g.strokeStyle = T.css(st.stroke); g.lineWidth = st.strokeWidth || 1; g.strokeRect(a + 0.5, b + 0.5, w, h); }
          break;
        }
        case 'circle': {
          const rx = Math.abs(X(c.c[0] + c.r) - X(c.c[0])), ry = Math.abs(Y(c.c[1] + c.r) - Y(c.c[1]));
          g.beginPath();
          g.ellipse(X(c.c[0]), Y(c.c[1]), Math.max(rx, 0.5), Math.max(ry, 0.5), 0, 0, 6.2832);
          if (st.fill) { g.fillStyle = T.css(st.fill); g.globalAlpha = st.fillAlpha ?? 0.1; g.fill(); g.globalAlpha = st.alpha ?? 1; }
          g.lineWidth = st.width || 1.2;
          g.stroke();
          break;
        }
        case 'cells':
          for (const q of c.list) {
            g.globalAlpha = q.a ?? 1;
            g.fillStyle = T.css(q.c);
            // Snap edges to whole pixels so neighbouring translucent cells neither overlap nor leave gaps.
            const x0 = Math.round(X(q.x - q.w / 2)), x1 = Math.round(X(q.x + q.w / 2));
            const y0 = Math.round(Y(q.y + q.h / 2)), y1 = Math.round(Y(q.y - q.h / 2));
            g.fillRect(x0, y0, Math.max(1, x1 - x0), Math.max(1, y1 - y0));
          }
          break;
        case 'hband': g.fillRect(m.l, Y(Math.max(c.y0, c.y1)), pw, Math.abs(Y(c.y1) - Y(c.y0))); break;
        case 'vband': g.fillRect(X(Math.min(c.x0, c.x1)), m.t, Math.max(1, Math.abs(X(c.x1) - X(c.x0))), ph); break;
        case 'text':
          g.font = st.font || '13px "STIX Two Text", Georgia, serif';
          g.textAlign = st.align || 'left'; g.textBaseline = st.baseline || 'middle';
          g.fillText(c.s, X(c.x) + (st.dx || 0), Y(c.y) + (st.dy || 0));
          break;
        case 'raster': {
          // Rasters with a value function are computed again for a zoomed view, once interaction pauses.
          if (c.o.value && !c.o.fixed) {
            const want = this.view ? [[Math.max(xr[0], c.o.clip ? c.o.x[0] : -Infinity), Math.min(xr[1], c.o.clip ? c.o.x[1] : Infinity)], c.o.ny === 1 ? c.o.y : [Math.max(yr[0], c.o.clip ? c.o.y[0] : -Infinity), Math.min(yr[1], c.o.clip ? c.o.y[1] : Infinity)]] : [c.o.x, c.o.y];
            const key = want.flat().join();
            if (c.extKey !== key && !this.interacting && want[0][1] > want[0][0] && want[1][1] > want[1][0]) {
              const [[x0, x1], [y0, y1]] = want;
              for (let j = 0; j < c.ny; j++) for (let i = 0; i < c.nx; i++) {
                c.vals[j * c.nx + i] = c.o.value(x0 + (i + 0.5) * (x1 - x0) / c.nx, y1 - (j + 0.5) * (y1 - y0) / c.ny);
              }
              c.ext = want; c.extKey = key; c.img = null;
              if (c.o.stats) c.stats = c.o.stats(c.vals, c.nx, c.ny);
            }
          }
          if (!c.img || c.stamp !== T.stamp) {
            const off = document.createElement('canvas');
            off.width = c.nx; off.height = c.ny;
            const cg = off.getContext('2d'), id = cg.createImageData(c.nx, c.ny);
            for (let k = 0; k < c.vals.length; k++) {
              const v = c.o.color(c.vals[k], T, c.stats, k);
              if (v) { id.data[k * 4] = v[0]; id.data[k * 4 + 1] = v[1]; id.data[k * 4 + 2] = v[2]; id.data[k * 4 + 3] = v[3] ?? 255; }
            }
            cg.putImageData(id, 0, 0);
            c.img = off; c.stamp = T.stamp;
          }
          g.imageSmoothingEnabled = c.o.smooth !== false;
          const [[x0, x1], [y0, y1]] = c.ext;
          g.drawImage(c.img, X(x0), Y(y1), X(x1) - X(x0), Y(y0) - Y(y1));
          break;
        }
      }
    }
    g.restore();
    g.globalAlpha = 1; g.setLineDash([]);
    g.strokeStyle = T.line; g.lineWidth = 1;
    g.strokeRect(m.l + 0.5, m.t + 0.5, pw - 1, ph - 1);

    // axis names
    g.font = 'italic 13px "STIX Two Text", Georgia, serif';
    g.fillStyle = T.muted;
    if (this.o.xlabel && showX) { g.textAlign = 'right'; g.textBaseline = 'bottom'; g.fillText(this.o.xlabel, m.l + pw - 6, m.t + ph - 4); }
    if (this.o.ylabel && showY) { g.textAlign = 'left'; g.textBaseline = 'top'; g.fillText(this.o.ylabel, m.l + 6, m.t + 4); }
  }

  // The point of the plot under the pointer, or null outside the plotting area.
  toWorld(ev) {
    if (!this.tf) return null;
    const r = this.canvas.getBoundingClientRect();
    const px = ev.clientX - r.left, py = ev.clientY - r.top;
    const { m, pw, ph, xr, yr } = this.tf;
    if (px < m.l || px > m.l + pw || py < m.t || py > m.t + ph) return null;
    return [xr[0] + (px - m.l) / pw * (xr[1] - xr[0]), yr[1] - (py - m.t) / ph * (yr[1] - yr[0])];
  }
  hover(ev) {
    const w = this.toWorld(ev);
    if (!w) { this.read.textContent = ''; return; }
    const [x, y] = w;
    const s = v => fmtNum(+v.toPrecision(4));
    this.read.textContent = `${this.o.xlabel || 'x'} = ${s(x)}` + (this.o.yAxis === false ? '' : `   ${this.o.ylabel || 'y'} = ${s(y)}`);
  }
}

function renderAllFigures() {
  for (const f of FIGS) { if (f.wrap.isConnected) f.render(); else FIGS.delete(f); }
}


Figure.queue = new Set();
MV.Figure = Figure;
MV.FIGS = FIGS;
MV.renderAllFigures = renderAllFigures;
MV.theme = theme;
MV.resetTheme = resetTheme;
MV.minmax = minmax;

})(typeof window !== 'undefined' ? window : globalThis);
