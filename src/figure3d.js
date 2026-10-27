/* Theorem Sketchpad — 3D figures: points, curves, arrows, polygons and surfaces in a box you can
   turn (drag) and zoom (scroll or the buttons). Drawn on a canvas with depth sorting, so it needs
   no WebGL and looks the same in the light and dark themes. */
'use strict';
(function (global) {
const MV = global.MV;
const { fmtNum } = MV;

const HINT3 = 'drag to turn · scroll to zoom · double-click to reset';
const VIEW0 = { yaw: -0.65, pitch: 0.42, zoom: 1 };

function niceStep(span, count) {
  const raw = span / Math.max(1, count), p = Math.pow(10, Math.floor(Math.log10(raw))), m = raw / p;
  return (m < 1.5 ? 1 : m < 3 ? 2 : m < 7 ? 5 : 10) * p;
}
const tick = (v, step) => Math.abs(v) < step * 1e-9 ? '0' : fmtNum(+v.toPrecision(3));

// Height colors: a perceptual ramp from the theme's first color to its third.
function ramp(T, t) {
  const a = T.rgb('c1'), b = T.rgb('c3'), c = T.rgb('c2');
  t = Math.max(0, Math.min(1, t));
  const [p, q, s] = t < 0.5 ? [a, c, t * 2] : [c, b, (t - 0.5) * 2];
  return p.map((x, i) => Math.round(x + (q[i] - x) * s));
}

class Figure3D {
  constructor(host, o = {}) {
    this.o = o; this.cmds = []; this.pts = [];
    this.view = { ...VIEW0, ...(o.view || {}) };
    this.wrap = document.createElement('div');
    this.wrap.className = 'fig fig3d zoomable';
    this.canvas = document.createElement('canvas');
    this.read = document.createElement('div');
    this.read.className = 'readout';
    this.wrap.append(this.canvas, this.read);
    host.appendChild(this.wrap);
    this.tools();
    MV.FIGS.add(this);
  }

  tools() {
    const bar = document.createElement('div');
    bar.className = 'fig-tools';
    const btn = (label, title, fn) => {
      const b = document.createElement('button');
      b.type = 'button'; b.textContent = label; b.title = title;
      b.addEventListener('click', ev => { ev.stopPropagation(); fn(); });
      bar.append(b);
      return b;
    };
    btn('+', 'Zoom in', () => this.set({ zoom: this.view.zoom * 1.25 }));
    btn('−', 'Zoom out', () => this.set({ zoom: this.view.zoom / 1.25 }));
    btn('Top', 'Look straight down the z-axis', () => this.set({ yaw: 0, pitch: Math.PI / 2 - 0.001 }));
    btn('Front', 'Look along the y-axis', () => this.set({ yaw: 0, pitch: 0 }));
    btn('Reset', 'Back to the original view (or double-click)', () => this.set({ ...VIEW0, ...(this.o.view || {}) }));
    this.spinBtn = btn('Spin', 'Turn the figure slowly', () => this.toggleSpin());
    btn('Copy', 'Copy the picture as an image', () => this.copyImage());
    this.hint = document.createElement('span');
    this.hint.className = 'fig-hint';
    this.hint.textContent = HINT3;
    bar.append(this.hint);
    this.wrap.append(bar);

    const cv = this.canvas;
    let drag = null;
    cv.addEventListener('pointerdown', ev => {
      cv.setPointerCapture(ev.pointerId);
      MV.Figure.activate(this);
      drag = { x: ev.clientX, y: ev.clientY, v: { ...this.view } };
      this.stopSpin();
    });
    cv.addEventListener('pointermove', ev => {
      if (!drag) { this.hover(ev); return; }
      const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y;
      const pitch = Math.max(-Math.PI / 2 + 0.001, Math.min(Math.PI / 2 - 0.001, drag.v.pitch + dy * 0.008));
      this.set({ yaw: drag.v.yaw + dx * 0.008, pitch }, true);
    });
    const end = () => { if (drag) { drag = null; this.interacting = false; this.render(); } };
    cv.addEventListener('pointerup', end);
    cv.addEventListener('pointercancel', end);
    cv.addEventListener('pointerleave', () => { this.read.textContent = ''; });
    cv.addEventListener('wheel', ev => {
      if (!(MV.Figure.active === this || ev.ctrlKey || ev.metaKey)) return;
      ev.preventDefault();
      this.set({ zoom: Math.max(0.2, Math.min(20, this.view.zoom * Math.pow(0.9985, ev.deltaY * (ev.deltaMode ? 30 : 1)))) }, true);
      clearTimeout(this.wheelTimer);
      this.wheelTimer = setTimeout(() => { this.interacting = false; this.render(); }, 160);
    }, { passive: false });
    cv.addEventListener('dblclick', () => this.set({ ...VIEW0, ...(this.o.view || {}) }));
  }
  set(v, interacting = false) {
    Object.assign(this.view, v);
    this.interacting = interacting;
    if (!interacting) { this.render(); return; }
    if (!this.raf) this.raf = requestAnimationFrame(() => { this.raf = 0; this.render(); });
  }
  toggleSpin() { if (this.spin) this.stopSpin(); else this.startSpin(); }
  startSpin() {
    this.spinBtn.textContent = 'Stop';
    let last = performance.now();
    const step = now => {
      if (!this.spin || !this.wrap.isConnected) { this.spin = 0; return; }
      this.view.yaw += (now - last) * 0.0006; last = now;
      this.interacting = true;
      this.render();
      this.spin = requestAnimationFrame(step);
    };
    this.spin = requestAnimationFrame(step);
  }
  stopSpin() {
    if (!this.spin) return;
    cancelAnimationFrame(this.spin); this.spin = 0;
    this.spinBtn.textContent = 'Spin';
    this.interacting = false;
    this.render();
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
    this.flashTimer = setTimeout(() => { this.hint.textContent = HINT3; }, 1600);
  }

  /* ---- drawing commands (coordinates are [x, y, z]) ---- */
  track(ps) { for (const p of ps) if (p && p.every(Number.isFinite)) this.pts.push(p); }
  points(ps, st = {}) { ps = ps.filter(p => p && p.length === 3 && p.every(Number.isFinite)); this.cmds.push({ k: 'points', ps, st }); if (st.track !== false) this.track(ps); return this; }
  curve(ps, st = {}) { this.cmds.push({ k: 'curve', ps, st }); if (st.track !== false) this.track(ps); return this; }
  seg(a, b, st = {}) { this.cmds.push({ k: 'seg', a, b, st }); if (st.track !== false) this.track([a, b]); return this; }
  arrow(a, b, st = {}) { this.cmds.push({ k: 'arrow', a, b, st }); if (st.track !== false) this.track([a, b]); return this; }
  poly(ps, st = {}) { this.cmds.push({ k: 'poly', ps, st }); if (st.track !== false) this.track(ps); return this; }
  text(p, s, st = {}) { this.cmds.push({ k: 'text', p, s: String(s), st }); return this; }
  /* A surface: f(u, v) gives a point [x, y, z], or a height z over (u, v). Faces are colored by
     height unless st.color is given; undefined points leave holes. */
  surface(f, st = {}) {
    const [u0, u1] = st.u || [-1, 1], [v0, v1] = st.v || [-1, 1], n = st.n || 36, m = st.m || n;
    const grid = [], vals = st.value ? [] : null;
    for (let i = 0; i <= n; i++) {
      const row = [], vrow = [];
      for (let j = 0; j <= m; j++) {
        const u = u0 + (u1 - u0) * i / n, v = v0 + (v1 - v0) * j / m;
        let p;
        try { p = f(u, v); } catch (e) { p = null; }
        if (typeof p === 'number') p = [u, v, p];
        row.push(Array.isArray(p) && p.length === 3 && p.every(Number.isFinite) ? p : null);
        if (vals) { let x; try { x = st.value(u, v); } catch (e) { x = NaN; } vrow.push(Number.isFinite(x) ? x : NaN); }
      }
      grid.push(row);
      if (vals) vals.push(vrow);
    }
    this.cmds.push({ k: 'surface', grid, vals, st });
    if (st.track !== false) this.track(grid.flat().filter(Boolean));
    return this;
  }

  box() {
    if (this.o.box) return this.o.box;
    const b = [0, 1, 2].map(i => {
      let lo = Infinity, hi = -Infinity;
      for (const p of this.pts) { if (p[i] < lo) lo = p[i]; if (p[i] > hi) hi = p[i]; }
      if (!(hi > lo)) { lo = (Number.isFinite(lo) ? lo : 0) - 1; hi = lo + 2; }
      // Huge outliers (a pole of a surface) shouldn't flatten everything else.
      if (i === 2 && this.pts.length > 200) {
        const zs = this.pts.map(p => p[2]).sort((a, c) => a - c), q = Math.floor(zs.length * 0.02);
        const a = zs[q], c = zs[zs.length - 1 - q];
        if (c > a && (hi - lo) > 6 * (c - a)) { lo = a - (c - a) * 0.3; hi = c + (c - a) * 0.3; }
      }
      return [lo, hi];
    });
    if (this.o.equal !== false) {
      const span = Math.max(...b.map(r => r[1] - r[0]));
      // Keep equal scales unless one axis would be squashed to almost nothing.
      if (b.every(r => (r[1] - r[0]) > span / 8)) return b.map(r => { const c = (r[0] + r[1]) / 2; return [c - span / 2, c + span / 2]; });
    }
    return b;
  }

  render() {
    if (!this.wrap.isConnected) return;
    const T = MV.theme();
    const W = Math.max(200, Math.floor(this.wrap.clientWidth || 600));
    const H = this.o.height || Math.round(Math.min(460, Math.max(260, W * 0.72)));
    const dpr = global.devicePixelRatio || 1;
    const cv = this.canvas;
    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
    cv.style.width = W + 'px'; cv.style.height = H + 'px';
    const g = cv.getContext('2d');
    g.setTransform(dpr, 0, 0, dpr, 0, 0);
    g.clearRect(0, 0, W, H);

    const B = this.box();
    const norm = p => p.map((x, i) => 2 * (x - B[i][0]) / (B[i][1] - B[i][0]) - 1);
    const { yaw, pitch, zoom } = this.view;
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const scale = Math.min(W, H) * 0.3 * zoom, cx0 = W / 2, cy0 = H / 2 + H * 0.02;
    // Camera: turn about z by yaw, then tilt by pitch. Screen x right, screen y up, depth toward the viewer.
    const cam = q => {
      const x1 = q[0] * cy - q[1] * sy, y1 = q[0] * sy + q[1] * cy, z1 = q[2];
      return [x1, y1 * sp + z1 * cp, -y1 * cp + z1 * sp];
    };
    const persp = 5;
    const proj = p => {
      const [x, y, d] = cam(norm(p));
      const f = persp / (persp - d);
      return [cx0 + x * scale * f, cy0 - y * scale * f, d];
    };
    this.tf = { proj, B };

    const items = [];   // {d, draw}
    // The box: the three back faces' edges and grid lines, behind everything.
    const corners = [];
    for (const a of [0, 1]) for (const b of [0, 1]) for (const c of [0, 1]) corners.push([B[0][a], B[1][b], B[2][c]]);
    const back = i => {
      // For axis i, the face (lo or hi) farther from the viewer.
      const lo = B.map(r => (r[0] + r[1]) / 2); lo[i] = B[i][0];
      const hi = lo.slice(); hi[i] = B[i][1];
      return proj(lo)[2] < proj(hi)[2] ? 0 : 1;
    };
    g.lineWidth = 1;
    g.font = '10px "JetBrains Mono", ui-monospace, monospace';
    for (let i = 0; i < 3; i++) {
      const side = back(i), val = B[i][side];
      const [j, k] = [0, 1, 2].filter(x => x !== i);
      const at = (u, v) => { const p = [0, 0, 0]; p[i] = val; p[j] = u; p[k] = v; return proj(p); };
      g.strokeStyle = T.line; g.globalAlpha = 0.9;
      for (const [ax, other] of [[j, k], [k, j]]) {
        const step = niceStep(B[ax][1] - B[ax][0], 4);
        for (let t = Math.ceil(B[ax][0] / step) * step; t <= B[ax][1] + 1e-9 * step; t += step) {
          const a = ax === j ? at(t, B[other][0]) : at(B[other][0], t), b = ax === j ? at(t, B[other][1]) : at(B[other][1], t);
          g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke();
        }
      }
    }
    g.globalAlpha = 1;
    // Axis ticks along the front-bottom edges.
    const names = this.o.labels || ['x', 'y', 'z'];
    for (let i = 0; i < 3; i++) {
      const others = [0, 1, 2].filter(x => x !== i);
      // Pick the edge parallel to axis i that is lowest on screen (for x, y) or leftmost (for z).
      let best = null;
      for (const a of [0, 1]) for (const b of [0, 1]) {
        const p = [0, 0, 0]; p[others[0]] = B[others[0]][a]; p[others[1]] = B[others[1]][b];
        const q0 = p.slice(), q1 = p.slice(); q0[i] = B[i][0]; q1[i] = B[i][1];
        const s0 = proj(q0), s1 = proj(q1), key = i === 2 ? -(s0[0] + s1[0]) : (s0[1] + s1[1]);
        if (!best || key > best.key) best = { key, p, s0, s1 };
      }
      const step = niceStep(B[i][1] - B[i][0], 4);
      g.fillStyle = T.muted;
      g.textAlign = 'center'; g.textBaseline = 'middle';
      const mid = [(best.s0[0] + best.s1[0]) / 2, (best.s0[1] + best.s1[1]) / 2];
      const out = [mid[0] - cx0, mid[1] - cy0], ol = Math.hypot(...out) || 1;
      for (let t = Math.ceil(B[i][0] / step) * step; t <= B[i][1] + 1e-9 * step; t += step) {
        const p = best.p.slice(); p[i] = t;
        const s = proj(p);
        g.fillText(tick(t, step), s[0] + out[0] / ol * 14, s[1] + out[1] / ol * 14);
      }
      g.font = 'italic 13px "STIX Two Text", Georgia, serif';
      g.fillText(names[i], mid[0] + out[0] / ol * 32, mid[1] + out[1] / ol * 32);
      g.font = '10px "JetBrains Mono", ui-monospace, monospace';
    }

    const light = [-0.4, 0.5, 0.75], ll = Math.hypot(...light);
    const shade = (a, b, c) => {
      const u = [b[0] - a[0], b[1] - a[1], b[2] - a[2]], v = [c[0] - a[0], c[1] - a[1], c[2] - a[2]];
      const n = [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]];
      const nl = Math.hypot(...n) || 1;
      return 0.55 + 0.45 * Math.abs((n[0] * light[0] + n[1] * light[1] + n[2] * light[2]) / (nl * ll));
    };
    const rgbStr = (c, a = 1) => `rgba(${c[0]},${c[1]},${c[2]},${a})`;
    const coarse = this.interacting;

    for (const c of this.cmds) {
      const st = c.st || {};
      const color = st.color || 'accent';
      switch (c.k) {
        case 'points': {
          const r = st.r || 2.6, ps = coarse && c.ps.length > 4000 ? c.ps.filter((_, i) => i % 3 === 0) : c.ps;
          for (const p of ps) {
            const s = proj(p);
            items.push({ d: s[2], draw: () => { g.globalAlpha = st.alpha ?? 0.9; g.fillStyle = T.css(p.color || color); g.beginPath(); g.arc(s[0], s[1], r, 0, 6.2832); g.fill(); } });
          }
          break;
        }
        case 'curve': {
          let prev = null;
          for (const p of c.ps) {
            const s = p && p.every(Number.isFinite) ? proj(p) : null;
            if (s && prev) {
              const a = prev;
              items.push({ d: (a[2] + s[2]) / 2, draw: () => { g.globalAlpha = st.alpha ?? 1; g.strokeStyle = T.css(color); g.lineWidth = st.width || 2; g.lineCap = 'round'; g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(s[0], s[1]); g.stroke(); } });
            }
            prev = s;
          }
          break;
        }
        case 'seg': case 'arrow': {
          // Long segments go in pieces, each sorted by its own depth, so they pass through planes properly.
          // An arrow's last piece carries the head.
          const N = 24, at = t => c.a.map((x, i) => x + (c.b[i] - x) * t);
          for (let s = 0; s < (c.k === 'arrow' ? N - 1 : N); s++) {
            const pa = proj(at(s / N)), pb = proj(at((s + 1) / N));
            items.push({ d: (pa[2] + pb[2]) / 2, draw: () => {
              g.globalAlpha = st.alpha ?? 1; g.strokeStyle = T.css(color); g.lineWidth = st.width || 2; g.lineCap = 'round';
              g.beginPath(); g.moveTo(pa[0], pa[1]); g.lineTo(pb[0], pb[1]); g.stroke();
            } });
          }
          if (c.k === 'seg') break;
          const a = proj(at((N - 1) / N)), b = proj(c.b);
          items.push({ d: Math.max(a[2], b[2]) + 0.01, draw: () => {
            g.globalAlpha = st.alpha ?? 1; g.strokeStyle = g.fillStyle = T.css(color); g.lineWidth = st.width || 2;
            g.setLineDash(st.dash || []);
            g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke();
            g.setLineDash([]);
            if (c.k === 'arrow') {
              const ang = Math.atan2(b[1] - a[1], b[0] - a[0]), L = 10;
              g.beginPath(); g.moveTo(b[0], b[1]);
              g.lineTo(b[0] - L * Math.cos(ang - 0.4), b[1] - L * Math.sin(ang - 0.4));
              g.lineTo(b[0] - L * Math.cos(ang + 0.4), b[1] - L * Math.sin(ang + 0.4));
              g.closePath(); g.fill();
            }
          } });
          break;
        }
        case 'poly': {
          const s = c.ps.map(proj), d = s.reduce((t, p) => t + p[2], 0) / s.length;
          const k = c.ps.length >= 3 ? shade(...c.ps.slice(0, 3).map(norm)) : 1;
          const base = T.rgb(color);
          items.push({ d, draw: () => {
            g.globalAlpha = 1;
            g.fillStyle = rgbStr(base.map(x => Math.round(x * k)), st.alpha ?? 0.35);
            g.beginPath(); s.forEach((p, i) => i ? g.lineTo(p[0], p[1]) : g.moveTo(p[0], p[1])); g.closePath(); g.fill();
            if (st.stroke) { g.strokeStyle = T.css(st.stroke); g.lineWidth = st.strokeWidth || 1.2; g.stroke(); }
          } });
          break;
        }
        case 'surface': {
          const G = c.grid, n = G.length - 1, m = G[0].length - 1;
          // Colored by value: the largest |value| (or st.vmax) is full color, 0 is neutral.
          // Each sign is scaled by its own extreme, so small positive values still show next to
          // large negative ones; values tiny next to both read as zero.
          const V = c.vals, fin = V ? V.flat().filter(Number.isFinite) : [];
          const vpos = st.vmax || Math.max(0, ...fin), vneg = st.vmax || Math.max(0, ...fin.map(x => -x)), vbig = Math.max(vpos, vneg, 1e-12);
          const neutral = T.rgb('vac'), negC = T.rgb('c1'), posC = T.rgb('c2');
          const byValue = x => {
            const m = x < 0 ? vneg : vpos;
            const t = Math.abs(x) < 1e-6 * vbig || !(m > 0) ? 0 : Math.min(1, 0.25 + 0.75 * Math.abs(x) / m), to = x < 0 ? negC : posC;
            return neutral.map((a, i) => a + (to[i] - a) * t);
          };
          const zs = G.flat().filter(Boolean).map(p => p[2]);
          let z0 = Math.max(Math.min(...zs), B[2][0]), z1 = Math.min(Math.max(...zs), B[2][1]);
          if (!(z1 > z0)) z1 = z0 + 1;
          const S = G.map(row => row.map(p => p && p[2] >= B[2][0] - 1e-9 * (B[2][1] - B[2][0]) && p[2] <= B[2][1] + 1e-9 * (B[2][1] - B[2][0]) ? proj(p) : null));
          const stepI = coarse && n > 24 ? 2 : 1;
          for (let i = 0; i < n; i += stepI) for (let j = 0; j < m; j += stepI) {
            const i1 = Math.min(n, i + stepI), j1 = Math.min(m, j + stepI);
            const q = [S[i][j], S[i1][j], S[i1][j1], S[i][j1]];
            if (q.some(x => !x)) continue;
            const P = [G[i][j], G[i1][j], G[i1][j1], G[i][j1]];
            const d = (q[0][2] + q[1][2] + q[2][2] + q[3][2]) / 4;
            const k = shade(norm(P[0]), norm(P[1]), norm(P[2]));
            const zc = (P[0][2] + P[1][2] + P[2][2] + P[3][2]) / 4;
            const vc = V ? (V[i][j] + V[i1][j] + V[i1][j1] + V[i][j1]) / 4 : NaN;
            const base = V && Number.isFinite(vc) ? byValue(vc) : st.color ? T.rgb(st.color) : ramp(T, (zc - z0) / (z1 - z0));
            const fill = rgbStr(base.map(x => Math.round(x * k)), st.alpha ?? 0.92);
            const edge = st.wire === false ? null : rgbStr(base.map(x => Math.round(x * k * 0.7)), 0.5);
            items.push({ d, draw: () => {
              g.globalAlpha = 1;
              g.fillStyle = fill;
              g.beginPath(); g.moveTo(q[0][0], q[0][1]); g.lineTo(q[1][0], q[1][1]); g.lineTo(q[2][0], q[2][1]); g.lineTo(q[3][0], q[3][1]); g.closePath();
              g.fill();
              if (edge) { g.strokeStyle = edge; g.lineWidth = 0.6; g.stroke(); } else { g.strokeStyle = fill; g.lineWidth = 0.6; g.stroke(); }
            } });
          }
          break;
        }
        case 'text': {
          const s = proj(c.p);
          items.push({ d: s[2] + 0.02, draw: () => {
            g.globalAlpha = 1; g.fillStyle = T.css(st.color || 'ink');
            g.font = st.font || '13px "STIX Two Text", Georgia, serif';
            g.textAlign = st.align || 'left'; g.textBaseline = 'middle';
            g.fillText(c.s, s[0] + (st.dx ?? 6), s[1] + (st.dy ?? -6));
          } });
          break;
        }
      }
    }
    items.sort((a, b) => a.d - b.d);
    for (const it of items) it.draw();
    g.globalAlpha = 1;
    // The front edges of the box, over everything, faintly.
    g.strokeStyle = T.faint; g.lineWidth = 1; g.globalAlpha = 0.5;
    const edges = [];
    for (let a = 0; a < 8; a++) for (let b = a + 1; b < 8; b++) if ([0, 1, 2].filter(i => corners[a][i] !== corners[b][i]).length === 1) edges.push([a, b]);
    const P = corners.map(proj);
    const maxD = Math.max(...P.map(p => p[2]));
    for (const [a, b] of edges) {
      const front = P[a][2] >= maxD - 1e-9 || P[b][2] >= maxD - 1e-9;
      g.setLineDash(front ? [3, 4] : []);
      g.beginPath(); g.moveTo(P[a][0], P[a][1]); g.lineTo(P[b][0], P[b][1]); g.stroke();
    }
    g.setLineDash([]); g.globalAlpha = 1;
  }

  hover(ev) {
    if (!this.tf || !this.o.readout) return;
    this.read.textContent = this.o.readout(ev) || '';
  }
}

MV.Figure3D = Figure3D;
})(typeof window !== 'undefined' ? window : globalThis);
