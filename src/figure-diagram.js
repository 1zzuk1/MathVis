/* Theorem Sketchpad — diagrams: nodes and labelled arrows, laid out automatically.
   Layouts: 'layered' (bottom to top by level: Hasse diagrams, lattices), 'flow' (left to right:
   commutative diagrams), 'grid' (given col and row), 'circle', 'force' (springs: Cayley graphs),
   'columns' (given col, rows in order: maps between two sets). Hovering a node highlights it, its
   edges and its related nodes and shows its tip; clicking calls its onClick. */
'use strict';
(function (global) {
const MV = global.MV;

class Diagram {
  constructor(host, o = {}) {
    this.o = o;
    this.nodes = [];
    this.edges = [];
    this.byId = new Map();
    this.wrap = document.createElement('div');
    this.wrap.className = 'fig diagram';
    this.canvas = document.createElement('canvas');
    // The hover text goes under the picture, not over it.
    this.read = document.createElement('div');
    this.read.className = 'diagram-tip';
    this.wrap.append(this.canvas, this.read);
    host.appendChild(this.wrap);
    this.hoverId = null;
    this.canvas.addEventListener('pointermove', ev => this.hover(ev));
    this.canvas.addEventListener('pointerleave', () => { this.hoverId = null; this.read.textContent = this.o.hint || ''; this.render(); });
    this.canvas.addEventListener('click', ev => { const n = this.hit(ev); if (n && n.onClick) n.onClick(n); });
    this.read.textContent = o.hint || '';
    MV.FIGS.add(this);
  }
  node(id, o = {}) {
    const n = { id, label: String(o.label ?? id), ...o };
    if (this.byId.has(id)) Object.assign(this.byId.get(id), n);
    else { this.nodes.push(n); this.byId.set(id, n); }
    return this;
  }
  edge(from, to, o = {}) { this.edges.push({ from, to, ...o }); return this; }

  /* ---------- layout: positions in [0, 1]² (y up), scaled at render time ---------- */
  layout() {
    const N = this.nodes, kind = this.o.layout || 'layered';
    if (!N.length) return;
    if (kind === 'grid') {
      const cols = Math.max(...N.map(n => n.col ?? 0)), rows = Math.max(...N.map(n => n.row ?? 0));
      for (const n of N) { n.x = cols ? (n.col ?? 0) / cols : 0.5; n.y = rows ? 1 - (n.row ?? 0) / rows : 0.5; }
      return;
    }
    if (kind === 'circle') {
      N.forEach((n, i) => { const t = Math.PI / 2 - 2 * Math.PI * i / N.length; n.x = 0.5 + 0.5 * Math.cos(t); n.y = 0.5 + 0.5 * Math.sin(t); });
      return;
    }
    if (kind === 'force') return this.forceLayout();
    if (kind === 'fixed') return;   // positions given as x, y in [0, 1]
    if (kind === 'columns') {
      const cols = [...new Set(N.map(n => n.col ?? 0))].sort((a, b) => a - b);
      for (const c of cols) {
        const ns = N.filter(n => (n.col ?? 0) === c);
        ns.forEach((n, i) => { n.x = cols.length > 1 ? cols.indexOf(c) / (cols.length - 1) : 0.5; n.y = ns.length > 1 ? 1 - i / (ns.length - 1) : 0.5; });
      }
      return;
    }
    // layered / flow: levels from the nodes, or the longest path from a source.
    const out = new Map(N.map(n => [n.id, []])), inn = new Map(N.map(n => [n.id, []]));
    for (const e of this.edges) if (e.from !== e.to && out.has(e.from) && out.has(e.to)) { out.get(e.from).push(e.to); inn.get(e.to).push(e.from); }
    const level = new Map();
    if (N.every(n => n.level !== undefined)) for (const n of N) level.set(n.id, n.level);
    else {
      const visit = (id, seen = new Set()) => {
        if (level.has(id)) return level.get(id);
        if (seen.has(id)) return 0;
        seen.add(id);
        const l = Math.max(-1, ...inn.get(id).map(p => visit(p, seen))) + 1;
        level.set(id, l);
        return l;
      };
      for (const n of N) visit(n.id);
    }
    const levels = [...new Set(level.values())].sort((a, b) => a - b);
    const rows = levels.map(l => N.filter(n => level.get(n.id) === l));
    // Barycenter sweeps to reduce crossings.
    const pos = new Map();
    const place = () => rows.forEach(r => r.forEach((n, i) => pos.set(n.id, (i + 0.5) / r.length)));
    place();
    for (let it = 0; it < 6; it++) {
      const order = it % 2 ? rows.slice().reverse() : rows;
      for (const r of order) {
        const bary = n => {
          const nb = [...out.get(n.id), ...inn.get(n.id)].filter(id => pos.has(id));
          return nb.length ? nb.reduce((s, id) => s + pos.get(id), 0) / nb.length : pos.get(n.id);
        };
        r.sort((a, b) => bary(a) - bary(b));
        r.forEach((n, i) => pos.set(n.id, (i + 0.5) / r.length));
      }
    }
    const L = Math.max(1, levels.length - 1);
    rows.forEach((r, li) => r.forEach(n => {
      const across = r.length === 1 ? 0.5 : pos.get(n.id);
      if (kind === 'flow') { n.x = li / L; n.y = 1 - across; }
      else { n.x = across; n.y = levels.length === 1 ? 0.5 : li / L; }
    }));
  }
  forceLayout() {
    const N = this.nodes, n = N.length;
    let seed = 7;
    const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
    N.forEach((v, i) => { const t = 2 * Math.PI * i / n; v.x = 0.5 + 0.4 * Math.cos(t) + 0.01 * rnd(); v.y = 0.5 + 0.4 * Math.sin(t) + 0.01 * rnd(); });
    const k = 0.9 / Math.sqrt(n), idx = new Map(N.map((v, i) => [v.id, i]));
    const E = this.edges.filter(e => e.from !== e.to && idx.has(e.from) && idx.has(e.to)).map(e => [idx.get(e.from), idx.get(e.to)]);
    for (let it = 0, temp = 0.1; it < 500; it++, temp *= 0.992) {
      const d = N.map(() => [0, 0]);
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
        const dx = N[i].x - N[j].x, dy = N[i].y - N[j].y, dist = Math.max(1e-4, Math.hypot(dx, dy)), f = k * k / dist;
        d[i][0] += dx / dist * f; d[i][1] += dy / dist * f; d[j][0] -= dx / dist * f; d[j][1] -= dy / dist * f;
      }
      for (const [a, b] of E) {
        const dx = N[a].x - N[b].x, dy = N[a].y - N[b].y, dist = Math.max(1e-4, Math.hypot(dx, dy)), f = dist * dist / k;
        d[a][0] -= dx / dist * f; d[a][1] -= dy / dist * f; d[b][0] += dx / dist * f; d[b][1] += dy / dist * f;
      }
      N.forEach((v, i) => { const l = Math.hypot(...d[i]) || 1; v.x += d[i][0] / l * Math.min(l, temp); v.y += d[i][1] / l * Math.min(l, temp); });
    }
    const xs = N.map(v => v.x), ys = N.map(v => v.y), [x0, x1] = [Math.min(...xs), Math.max(...xs)], [y0, y1] = [Math.min(...ys), Math.max(...ys)];
    N.forEach(v => { v.x = x1 > x0 ? (v.x - x0) / (x1 - x0) : 0.5; v.y = y1 > y0 ? (v.y - y0) / (y1 - y0) : 0.5; });
  }

  /* ---------- drawing ---------- */
  render() {
    if (!this.wrap.isConnected || !this.nodes.length) return;
    if (!this.laid) { this.layout(); this.laid = true; }
    const T = MV.theme();
    const avail = Math.max(240, Math.floor(this.wrap.clientWidth || 600));
    let W = avail;
    const kind = this.o.layout || 'layered';
    const nLevels = new Set(this.nodes.map(n => Math.round(n.y * 1000))).size;
    const H = this.o.height || Math.round(kind === 'flow' || kind === 'grid' ? Math.min(420, 120 + 70 * nLevels) : kind === 'layered' ? Math.min(560, 70 + 78 * nLevels) : Math.min(460, Math.max(260, W * 0.6)));
    const cv = this.canvas, g = cv.getContext('2d');
    // Node boxes, sized by their labels. A crowded row first gets a smaller font, then a wider
    // picture that scrolls sideways (centred), rather than overlapping boxes.
    const rows = new Map();
    for (const n of this.nodes) { const k = Math.round(n.y * 1000); if (!rows.has(k)) rows.set(k, []); rows.get(k).push(n); }
    let font, padX, boxH, mx, need;
    for (const size of [14, 12, 10.5]) {
      font = this.o.font || `${size}px "STIX Two Text", Georgia, serif`;
      g.font = font;
      padX = size > 12 ? 9 : 6; boxH = this.o.small || size < 14 ? 20 : 26;
      for (const n of this.nodes) { n.w = n.dot ? 12 : Math.max(boxH, g.measureText(n.label).width + 2 * padX); n.h = n.dot ? 12 : boxH; }
      mx = Math.max(...this.nodes.map(n => n.w)) / 2 + 14;
      need = 0;
      if (kind === 'layered') for (const r of rows.values()) need = Math.max(need, r.length * (Math.max(...r.map(n => n.w)) + 12));
      if (need + 2 * mx <= avail || this.o.font) break;
    }
    if (need + 2 * mx > W) W = Math.ceil(need + 2 * mx);
    const my = boxH / 2 + 16;
    const dpr = global.devicePixelRatio || 1;
    cv.width = Math.round(W * dpr); cv.height = Math.round(H * dpr);
    cv.style.width = W + 'px'; cv.style.height = H + 'px';
    g.setTransform(dpr, 0, 0, dpr, 0, 0);
    g.clearRect(0, 0, W, H);
    g.font = font;
    const scrolls = W > avail;
    this.wrap.style.overflowX = scrolls ? 'auto' : '';
    if (scrolls && !this.centred) { this.centred = true; requestAnimationFrame(() => { this.wrap.scrollLeft = (W - avail) / 2; }); }
    const X = n => mx + n.x * (W - 2 * mx), Y = n => H - my - n.y * (H - 2 * my);
    for (const n of this.nodes) { n.px = X(n); n.py = Y(n); }
    this.geom = { W, H };
    // Highlighting: the hovered node, its edges, and its related nodes.
    const hov = this.hoverId !== null ? this.byId.get(this.hoverId) : null;
    const related = new Set(hov ? [hov.id, ...(hov.related || [])] : []);
    if (hov) for (const e of this.edges) { if (e.from === hov.id) related.add(e.to); if (e.to === hov.id) related.add(e.from); }
    const dim = id => hov && !related.has(id);

    // Edges (parallel ones curve apart; loops above the node).
    const pairCount = new Map();
    for (const e of this.edges) { const k = [e.from, e.to].sort().join('→'); pairCount.set(k, (pairCount.get(k) || 0) + 1); }
    const pairSeen = new Map();
    for (const e of this.edges) {
      const a = this.byId.get(e.from), b = this.byId.get(e.to);
      if (!a || !b) continue;
      const touches = hov && (e.from === hov.id || e.to === hov.id);
      g.globalAlpha = hov ? (touches ? 1 : 0.15) : (e.alpha ?? 0.85);
      g.strokeStyle = g.fillStyle = T.css(e.color || 'muted');
      g.lineWidth = (e.width || 1.4) * (touches ? 1.5 : 1);
      g.setLineDash(e.dashed ? [5, 4] : []);
      if (a === b) {
        g.beginPath(); g.arc(a.px, a.py - a.h / 2 - 8, 8, 0, 2 * Math.PI); g.stroke();
        continue;
      }
      const key = [e.from, e.to].sort().join('→'), k = pairSeen.get(key) || 0;
      pairSeen.set(key, k + 1);
      const count = pairCount.get(key);
      const bend = count > 1 ? (k - (count - 1) / 2) * 26 * (e.from < e.to ? 1 : -1) : (e.bend || 0);
      const [sx, sy] = this.border(a, b.px, b.py), [tx, ty] = this.border(b, a.px, a.py);
      const mxp = (sx + tx) / 2, myp = (sy + ty) / 2, len = Math.hypot(tx - sx, ty - sy) || 1;
      const cx = mxp - (ty - sy) / len * bend, cy = myp + (tx - sx) / len * bend;
      g.beginPath(); g.moveTo(sx, sy);
      if (bend) g.quadraticCurveTo(cx, cy, tx, ty); else g.lineTo(tx, ty);
      g.stroke();
      g.setLineDash([]);
      if (e.arrow !== false) {
        const ang = bend ? Math.atan2(ty - cy, tx - cx) : Math.atan2(ty - sy, tx - sx), L = 9;
        g.beginPath(); g.moveTo(tx, ty);
        g.lineTo(tx - L * Math.cos(ang - 0.38), ty - L * Math.sin(ang - 0.38));
        g.lineTo(tx - L * Math.cos(ang + 0.38), ty - L * Math.sin(ang + 0.38));
        g.closePath(); g.fill();
      }
      if (e.label && !(this.edges.length > 30 && e.minor)) {
        const lx = bend ? (mxp + cx) / 2 : mxp, ly = bend ? (myp + cy) / 2 : myp;
        g.font = e.font || 'italic 13px "STIX Two Text", Georgia, serif';
        const tw = g.measureText(e.label).width;
        // Labels sit beside the edge, on its left.
        const nx = -(ty - sy) / len, ny = (tx - sx) / len, off = 10;
        const px = lx + nx * off, py = ly + ny * off;
        g.globalAlpha = Math.max(g.globalAlpha, 0.5);
        g.fillStyle = T.panel || T.bg;
        g.fillRect(px - tw / 2 - 2, py - 8, tw + 4, 16);
        g.fillStyle = T.css(e.labelColor || e.color || 'muted');
        g.textAlign = 'center'; g.textBaseline = 'middle';
        g.fillText(e.label, px, py);
        g.font = font;
      }
    }
    g.globalAlpha = 1;
    g.setLineDash([]);
    // Nodes.
    for (const n of this.nodes) {
      g.globalAlpha = dim(n.id) ? 0.3 : 1;
      const fill = T.css(n.fill || 'panel'), stroke = T.css(n.color || 'ink');
      if (n.dot) {
        g.beginPath(); g.arc(n.px, n.py, 6, 0, 2 * Math.PI);
        g.fillStyle = T.css(n.color || 'c1'); g.fill();
        if (n.label) { g.fillStyle = T.css('ink'); g.font = '12px "STIX Two Text", Georgia, serif'; g.textAlign = 'center'; g.textBaseline = 'bottom'; g.fillText(n.label, n.px, n.py - 8); g.font = font; }
        continue;
      }
      const x = n.px - n.w / 2, y = n.py - n.h / 2, r = Math.min(8, n.h / 2);
      g.beginPath();
      g.moveTo(x + r, y); g.arcTo(x + n.w, y, x + n.w, y + n.h, r); g.arcTo(x + n.w, y + n.h, x, y + n.h, r);
      g.arcTo(x, y + n.h, x, y, r); g.arcTo(x, y, x + n.w, y, r); g.closePath();
      g.fillStyle = fill;
      g.globalAlpha = (dim(n.id) ? 0.3 : 1) * (n.fillAlpha ?? 1);
      g.fill();
      g.globalAlpha = dim(n.id) ? 0.3 : 1;
      g.strokeStyle = stroke;
      g.lineWidth = n.id === this.hoverId ? 2.4 : n.ring ? 2 : 1.2;
      if (n.dashed) g.setLineDash([4, 3]);
      g.stroke();
      g.setLineDash([]);
      g.fillStyle = T.css(n.textColor || 'ink');
      g.textAlign = 'center'; g.textBaseline = 'middle';
      g.fillText(n.label, n.px, n.py + 1);
    }
    g.globalAlpha = 1;
  }
  // Where the segment from n's center toward (tx, ty) leaves n's box.
  border(n, tx, ty) {
    const dx = tx - n.px, dy = ty - n.py;
    if (n.dot) { const l = Math.hypot(dx, dy) || 1; return [n.px + dx / l * 7, n.py + dy / l * 7]; }
    const hw = n.w / 2 + 3, hh = n.h / 2 + 3;
    const s = Math.min(hw / Math.abs(dx || 1e-9), hh / Math.abs(dy || 1e-9));
    return [n.px + dx * s, n.py + dy * s];
  }
  hit(ev) {
    const r = this.canvas.getBoundingClientRect(), x = ev.clientX - r.left, y = ev.clientY - r.top;
    return this.nodes.find(n => n.px !== undefined && Math.abs(x - n.px) <= n.w / 2 + 3 && Math.abs(y - n.py) <= n.h / 2 + 3) || null;
  }
  hover(ev) {
    const n = this.hit(ev);
    const id = n ? n.id : null;
    this.canvas.style.cursor = n && n.onClick ? 'pointer' : 'default';
    if (id === this.hoverId) return;
    this.hoverId = id;
    this.read.textContent = n ? (n.tip || n.label) : (this.o.hint || '');
    this.render();
  }
}

MV.Diagram = Diagram;
})(typeof window !== 'undefined' ? window : globalThis);
