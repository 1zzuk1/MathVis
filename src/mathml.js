/* Theorem Sketchpad — typesetting formulas as MathML, which browsers lay out natively: stacked
   fractions, root signs, ∑ with its limits above and below, piecewise braces for if-then-else.
   ppMath(node) gives HTML holding one or more <math> elements: a long formula is cut at its
   top-level quantifiers and connectives so the line can wrap there (MathML itself never wraps).
   It mirrors pp in syntax.js, with the same precedences, so both put brackets in the same places. */
'use strict';
(function (global) {
const MV = global.MV;
const { esc, fmtNum } = MV;

const GREEK = { alpha: 'α', beta: 'β', gamma: 'γ', delta: 'δ', eps: 'ε', epsilon: 'ε', theta: 'θ', lambda: 'λ', mu: 'μ', pi: 'π', sigma: 'σ', tau: 'τ', phi: 'φ', omega: 'ω' };
const BB = { R: 'ℝ', Z: 'ℤ', N: 'ℕ', Q: 'ℚ', C: 'ℂ' };
const CMP = { '<': '<', '<=': '≤', '>': '>', '>=': '≥', '=': '=', '!=': '≠', '~=': '≈' };
const PREC = { quant: 0, lambda: 0, if: 0, where: 0, '<->': 1, '->': 2, or: 3, and: 4, not: 5, cmp: 6, in: 6, subset: 6, range: 6, '+': 7, '-': 7, '\\': 7, union: 7, bigop: 7, '*': 8, '/': 8, mod: 8, inter: 8, neg: 9, sqrt: 10, '^': 11, post: 12, atom: 13 };
const BINOP = { '+': '+', '-': '−', '*': '⋅', mod: 'mod', and: '∧', or: '∨', '->': '⇒', '<->': '⇔', union: '∪', inter: '∩', '\\': '∖' };

const mo = (s, attrs = '') => `<mo${attrs}>${esc(s)}</mo>`;
const mi = (s, attrs = '') => `<mi${attrs}>${esc(s)}</mi>`;
const mn = s => `<mn>${esc(s)}</mn>`;
const mtext = s => `<mtext>${esc(s)}</mtext>`;
const row = (...xs) => `<mrow>${xs.join('')}</mrow>`;
const fence = c => mo(c, ' lspace="0" rspace="0"');
const paren = (x, l = '(', r = ')') => row(fence(l), x, fence(r));
const comma = mo(',', ' separator="true"');
const list = (xs, l, r) => paren(xs.join(comma), l, r);
const word = s => mo(s, ' form="infix" lspace="0.35em" rspace="0.35em"');

function num(v) {
  const s = fmtNum(v);
  if (s.startsWith('−')) return row(mo('−'), num(-v));
  const m = /^(.+)e(-?\d+)$/.exec(s);
  if (m) return row(mn(m[1]), mo('×'), `<msup>${mn('10')}${mn(m[2].replace('-', '−'))}</msup>`);
  return mn(s);
}

// x1 is x with subscript 1, f'' keeps its primes, Greek names become letters, R ℝ as a space.
// Names bound by an enclosing quantifier, set builder, sum or ↦: a relation called R stays R.
const BOUND = new Map();
function withBound(names, fn) {
  for (const x of names) BOUND.set(x, (BOUND.get(x) || 0) + 1);
  try { return fn(); } finally { for (const x of names) { const k = BOUND.get(x) - 1; if (k) BOUND.set(x, k); else BOUND.delete(x); } }
}
const namesOf = bs => bs.flatMap(MV.binderNames);

function ident(name, { space = false } = {}) {
  if (space && BB[name] && name.length === 1 && !BOUND.has(name)) return mi(BB[name]);
  if (name === 'inf') return mi('∞');
  const base = GREEK[name] || name;
  const m = /^([^\d']+?)(\d+)('*)$/.exec(base) || /^([^']+?)()('+)$/.exec(base);
  const letters = m ? m[1] : base;
  // Multi-letter names come out upright and one-letter names italic, as in sin(x) and f(x).
  const core = mi(letters);
  let out = m && m[2] ? `<msub>${core}${mn(m[2])}</msub>` : core;
  if (m && m[3]) out = row(out, mo('′'.repeat(m[3].length), ' lspace="0" rspace="0"'));
  return out;
}

const isSpaceName = a => (a.type === 'id' && 'RZN'.includes(a.name) && a.name.length === 1) || (a.type === 'bin' && a.op === '^' && a.a.type === 'id' && 'RZN'.includes(a.a.name) && a.a.name.length === 1);

function target(b) { return b.pattern ? list(b.pattern.map(x => ident(x)), '(', ')') : ident(b.name); }

function binders(bs) {
  const groups = [];
  for (const b of bs) {
    const g = groups[groups.length - 1];
    if (g && g.dom === b.dom) g.items.push(b); else groups.push({ dom: b.dom, items: [b] });
  }
  return groups.map(g => row(g.items.map(target).join(comma),
    g.dom.type === 'bound' ? row(mo(CMP[g.dom.op]), conv(g.dom.c, PREC.cmp + 1)) : row(mo('∈'), dom(g.dom)))).join(comma);
}

function dom(d) {
  if (d.type === 'interval') return row(fence(d.loOpen ? '(' : '['), conv(d.lo, 0), comma, conv(d.hi, 0), fence(d.hiOpen ? ')' : ']'));
  if (d.type === 'bound') return row(mo(CMP[d.op]), conv(d.c, 0));
  if (d.type === 'id') return ident(d.name, { space: true });
  if (d.type === 'bin' && d.op === '^' && d.a.type === 'id') return `<msup>${ident(d.a.name, { space: true })}${conv(d.b, 0)}</msup>`;
  if (d.type === 'range') return range(d);
  return conv(d, PREC.cmp + 1);
}

const range = n => row(fence('{'), conv(n.lo, 0), comma, mo('…'), comma, conv(n.hi, 0), fence('}'));

// The branches of if c then a else if c2 then b else d, for one brace.
function branches(n) {
  const rows = [];
  while (n.type === 'if') { rows.push([n.a, n.c]); n = n.b; }
  rows.push([n, null]);
  return rows;
}

function conv(n, p = 0) {
  let s, my = PREC.atom;
  switch (n.type) {
    case 'num': s = num(n.v); if (n.v < 0) my = PREC.neg; break;
    case 'bool': s = mtext(n.v ? 'true' : 'false'); break;
    case 'value': s = mi(n.label, ' mathvariant="normal"'); break;
    case 'id': s = ident(n.name); break;
    case 'bin': {
      my = PREC[n.op];
      if (n.op === '^') { s = `<msup>${conv(n.a, PREC.post)}${conv(n.b, 0)}</msup>`; break; }
      if (n.op === '/') { s = `<mfrac>${conv(n.a, 0)}${conv(n.b, 0)}</mfrac>`; break; }
      let o = n.op === 'mod' ? word('mod') : mo(BINOP[n.op]);
      if (n.op === '*' && (n.implicit || (n.a.type === 'num' && ['id', 'call', 'abs'].includes(n.b.type)))) o = mo('⁢');
      const right = n.op === '->';
      s = row(conv(n.a, right ? my + 1 : my), o, conv(n.b, right ? my : my + 1));
      break;
    }
    case 'cmp':
      my = PREC.cmp;
      s = row(...n.args.map((a, i) => (i ? mo(CMP[n.ops[i - 1]]) : '') + conv(a, PREC.cmp + 1)));
      break;
    case 'in': my = PREC.in; s = row(conv(n.elem, PREC.in + 1), mo(n.neg ? '∉' : '∈'), dom(n.dom)); break;
    case 'subset': my = PREC.subset; s = row(conv(n.a, PREC.subset + 1), mo('⊆'), conv(n.b, PREC.subset + 1)); break;
    case 'range': s = range(n); break;
    case 'un':
      if (n.op === 'neg') { my = PREC.neg; s = row(mo('−'), conv(n.a, PREC.neg)); }
      else if (n.op === 'not') { my = PREC.not; s = row(mo('¬'), conv(n.a, PREC.not)); }
      else if (n.op === 'sqrt') { s = `<msqrt>${conv(n.a, 0)}</msqrt>`; }
      else { my = PREC.post; s = row(conv(n.a, PREC.post), mo('!', ' lspace="0"')); }
      break;
    case 'abs': s = row(mo('|', ' stretchy="true"'), conv(n.e, 0), mo('|', ' stretchy="true"')); break;
    case 'call': {
      my = PREC.post;
      if (n.f.type === 'id' && n.f.name === 'sqrt' && n.args.length === 1) { s = `<msqrt>${conv(n.args[0], 0)}</msqrt>`; my = PREC.atom; break; }
      const f = n.f.type === 'id' ? ident(n.f.name) : conv(n.f, PREC.post);
      s = row(f, mo('⁡'), list(n.args.map(a => isSpaceName(a) ? dom(a) : conv(a, 0)), '(', ')'));
      break;
    }
    case 'index':
      my = PREC.post;
      s = `<msub>${n.obj.type === 'id' ? ident(n.obj.name, { space: true }) : conv(n.obj, PREC.post)}${row(n.args.map(a => conv(a, 0)).join(comma))}</msub>`;
      break;
    case 'list': s = list(n.items.map(a => conv(a, 0)), '[', ']'); break;
    case 'tuple': s = list(n.items.map(a => conv(a, 0)), '(', ')'); break;
    case 'finite': s = n.items.length ? list(n.items.map(a => conv(a, 0)), '{', '}') : mi('∅'); break;
    case 'field': my = PREC.post; s = row(conv(n.obj, PREC.post), mo('.', ' lspace="0" rspace="0"'), mi(n.name)); break;
    case 'record': s = list(n.fields.map(f => row(mi(f.name), mo('='), conv(f.expr, 0))), '{', '}'); break;
    case 'if': {
      const rows = branches(n).map(([v, c]) => `<mtr><mtd columnalign="left">${conv(v, 0)}</mtd><mtd columnalign="left">${c ? row(mtext('if '), conv(c, 0)) : mtext('otherwise')}</mtd></mtr>`);
      s = row(mo('{', ' stretchy="true"'), `<mtable columnspacing="1em">${rows.join('')}</mtable>`);
      break;
    }
    case 'lambda':
      my = PREC.lambda;
      s = row(n.params.length === 1 ? ident(n.params[0]) : list(n.params.map(x => ident(x)), '(', ')'), mo('↦'), withBound(n.params, () => conv(n.body, 0)));
      break;
    case 'quant': my = PREC.quant; s = row(quantHead(n), withBound(namesOf(n.binders), () => conv(n.body, 0))); break;
    case 'bigop': my = PREC.bigop; s = row(bigHead(n), withBound(namesOf(n.binders), () => conv(n.body, PREC.bigop + 1))); break;
    case 'lim': my = PREC.bigop; s = row(`<munder>${mo('lim', ' movablelimits="true"')}${row(ident(n.v), mo('→'), conv(n.to, PREC.post))}</munder>`, withBound([n.v], () => conv(n.body, PREC.bigop + 1))); break;
    case 'where': my = PREC.where; s = row(conv(n.body, 1), whereTail(n)); break;
    case 'setb': s = row(fence('{'), binders(n.binders), mo('∣'), withBound(namesOf(n.binders), () => conv(n.pred, 0)), fence('}')); break;
    case 'interval': case 'bound': s = dom(n); break;
    default: s = mi('?');
  }
  return my < p ? paren(s) : s;
}

const quantHead = n => row(mo(n.q === 'forall' ? '∀' : '∃', ' rspace="0.1em"'), binders(n.binders), mo(':', ' lspace="0.1em" rspace="0.4em"'));
const whereTail = n => row(word('where'), n.binds.map(b => row(ident(b.name), mo('='), conv(b.expr, 1))).join(comma));

// ∑ and ∏ over one range get their limits above and below; other big operators have the binder
// underneath.
function bigHead(n) {
  const sym = { sum: '∑', prod: '∏' }[n.op];
  const b = n.binders[0];
  if (sym && n.binders.length === 1 && !b.pattern && b.dom.type === 'range')
    return `<munderover>${mo(sym, ' largeop="true" movablelimits="true"')}${row(ident(b.name), mo('='), conv(b.dom.lo, 0))}${conv(b.dom.hi, 0)}</munderover>`;
  return `<munder>${mo(sym || n.op, ' largeop="true" movablelimits="true"')}${binders(n.binders)}</munder>`;
}

/* One <math> per piece: quantifier heads, connectives and their operands, so a long formula
   wraps between them. Pieces are only cut where the whole would need no brackets. */
function pieces(n, p, out) {
  const my = n.type === 'quant' ? PREC.quant : n.type === 'where' ? PREC.where : n.type === 'bin' && ['->', '<->', 'and', 'or'].includes(n.op) ? PREC[n.op] : -1;
  if (my < 0 || my < p) { out.push(conv(n, p)); return; }
  if (n.type === 'quant') { out.push(quantHead(n)); withBound(namesOf(n.binders), () => pieces(n.body, 0, out)); return; }
  if (n.type === 'where') { pieces(n.body, 1, out); out.push(whereTail(n)); return; }
  const right = n.op === '->';
  pieces(n.a, right ? my + 1 : my, out);
  out.push(mo(BINOP[n.op]));
  pieces(n.b, right ? my : my + 1, out);
}

function ppMath(n, { display = false } = {}) {
  const out = [];
  pieces(n, 0, out);
  const open = `<math${display ? ' displaystyle="true"' : ''}>`;
  // Each piece in a box that scrolls sideways when one piece is wider than the space it has.
  return out.map(x => '<span class="mx">' + open + x + '</math></span>').join(' ');
}

// MathML Core shipped in Chrome 109 and has long been in Firefox and Safari.
const mathSupported = () => typeof window !== 'undefined' && typeof window.MathMLElement === 'function';

const inMath = x => '<span class="mx"><math>' + x + '</math></span>';
const ppMathBinders = bs => inMath(binders(bs));
const ppMathDom = d => inMath(dom(d));

Object.assign(MV, { ppMath, ppMathBinders, ppMathDom, mathSupported });
})(typeof window !== 'undefined' ? window : globalThis);
