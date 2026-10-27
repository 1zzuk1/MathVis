/* Theorem Sketchpad — syntax: tokenizer, parser, statement splitter, pretty printer and name checker.
   Everything here is pure (no evaluation, no DOM). */
'use strict';
(function (global) {
const MV = global.MV = global.MV || {};

class MVError extends Error {
  constructor(msg, pos) { super(msg); this.pos = pos; }
}

const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));

function fmtNum(x) {
  if (Number.isNaN(x)) return 'undefined';
  if (!Number.isFinite(x)) return x > 0 ? '∞' : '−∞';
  let s;
  if (Number.isInteger(x) && Math.abs(x) < 1e15) s = String(x);
  else {
    const a = Math.abs(x);
    s = (a !== 0 && (a < 1e-4 || a >= 1e7))
      ? x.toExponential(3).replace(/\.?0+e/, 'e').replace('e+', 'e')
      : String(+x.toPrecision(6));
  }
  return s.replace(/^-/, '−');
}

/* ================= Tokens ================= */

const KW = new Set('forall exists in notin and or not if then else mod let def theorem lemma claim conjecture check plot show for import library true false where explain vary structure extends as concept interpret'.split(' '));
// Words that follow a bracket without multiplying it: (a, b) such that …, f(x) by lemma, g o f.
const NOT_FACTORS = new Set(['implies', 'iff', 'subset', 'union', 'inter', 'such', 'that', 'with', 'by', 'o', 'on', 'at', 'to', 'is', 'from']);
// Words with a special meaning only in some positions; elsewhere they are ordinary names.
const BIGOPS = new Set(['sum', 'prod', 'sup', 'inf', 'max', 'min']);
const UNI = {
  '∀': 'forall', '∃': 'exists', '∈': 'in', '∉': 'notin', '≤': '<=', '≥': '>=', '≠': '!=', '≈': '~=',
  '→': '->', '⇒': '->', '⟹': '->', '↔': '<->', '⇔': '<->', '∧': 'and', '∨': 'or', '¬': 'not',
  '·': '*', '⋅': '*', '×': '*', '−': '-', '↦': '=>', '‖': '|', '∖': '\\',
  'ℝ': 'R', 'ℤ': 'Z', 'ℕ': 'N', 'ℚ': 'Q', '∞': 'inf', '∑': 'sum', '∏': 'prod', '⊆': 'subset', '⊂': 'subset', '∪': 'union', '∩': 'inter',
};
const SUPERSCRIPT = { '²': '2', '³': '3', '⁴': '4', 'ⁿ': 'n' };
const OPS = ['<->', '<=>', '**', ':=', '=>', '->', '<=', '>=', '!=', '==', '~=', '..', '.',
  '+', '-', '*', '/', '^', '(', ')', '[', ']', '{', '}', ',', ':', '|', '<', '>', '=', '!', '√', '\\'];
const ID_START = /[\p{L}_]/u, ID_CHAR = /[\p{L}\p{N}_']/u;
const CMP = new Set(['<', '<=', '>', '>=', '=', '!=', '~=']);
const NUM_RE = /^(\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|\.\d+(?:[eE][+-]?\d+)?)/;

function tokenize(src) {
  const toks = [];
  const push = (t, v, pos, extra) => toks.push(Object.assign({ t, v, pos }, extra));
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c)) { i++; continue; }
    const pos = i;
    if (SUPERSCRIPT[c]) {
      push('op', '^', pos);
      const v = SUPERSCRIPT[c];
      if (/\d/.test(v)) push('num', +v, pos); else push('id', v, pos);
      i++; continue;
    }
    if (c === '∅') { push('op', '{', pos); push('op', '}', pos); i++; continue; }
    if (UNI[c] !== undefined) {
      const v = UNI[c];
      push(KW.has(v) ? 'kw' : /^[A-Za-z]/.test(v) ? 'id' : 'op', v, pos);
      i++; continue;
    }
    const num = NUM_RE.exec(src.slice(i));
    if (num) {
      push('num', parseFloat(num[1]), pos);
      i += num[1].length;
      // Implicit multiplication: 2x, 3(x + 1), 2π, and "2 pi" with a space.
      let j = i;
      while (src[j] === ' ' || src[j] === '\t') j++;
      const nx = src[j];
      if (nx && (nx === '(' || nx === '√') && j === i) push('op', '*', i, { implicit: true });
      else if (nx && ID_START.test(nx) && UNI[nx] === undefined) {
        let k = j + 1;
        while (k < src.length && ID_CHAR.test(src[k])) k++;
        const w = src.slice(j, k);
        if (!KW.has(w) && !['implies', 'iff', 'subset', 'union', 'inter'].includes(w)) push('op', '*', i, { implicit: true });
      }
      continue;
    }
    if (ID_START.test(c)) {
      let j = i + 1;
      while (j < src.length && ID_CHAR.test(src[j])) j++;
      const w = src.slice(i, j);
      if (w === 'implies') push('op', '->', pos);
      else if (w === 'iff') push('op', '<->', pos);
      else push(KW.has(w) ? 'kw' : 'id', w, pos);
      i = j; continue;
    }
    let op = OPS.find(o => src.startsWith(o, i));
    if (op) {
      i += op.length;
      if (op === '<=>') op = '<->';
      if (op === '**') op = '^';
      if (op === '==') op = '=';
      push('op', op, pos);
      // Implicit multiplication after a bracket: cos(u)cos(v), (x + 1)y, p[1]p[2]. Not before "(",
      // which applies a function: f(x)(y).
      if (op === ')' || op === ']') {
        let j = i;
        while (src[j] === ' ' || src[j] === '\t') j++;
        if (j < src.length && ID_START.test(src[j]) && UNI[src[j]] === undefined) {
          let k = j + 1;
          while (k < src.length && ID_CHAR.test(src[k])) k++;
          if (!KW.has(src.slice(j, k)) && !NOT_FACTORS.has(src.slice(j, k))) push('op', '*', i, { implicit: true });
        }
      }
      continue;
    }
    throw new MVError(`Unexpected character "${c}".`, pos);
  }
  push('eof', '', src.length);
  return toks;
}

const desc = t => t.t === 'eof' ? 'the end of the statement' : `"${t.t === 'num' ? fmtNum(t.v) : t.v}"`;

/* ================= Parser ================= */

const bin = (op, a, b, extra) => Object.assign({ type: 'bin', op, a, b }, extra);

class Parser {
  constructor(toks) { this.t = toks; this.i = 0; }
  peek(k = 0) { return this.t[Math.min(this.i + k, this.t.length - 1)]; }
  next() { return this.t[this.i++]; }
  is(v, k = 0) { const t = this.peek(k); return (t.t === 'op' || t.t === 'kw') && t.v === v; }
  isWord(v, k = 0) { const t = this.peek(k); return t.t === 'id' && t.v === v; }
  accept(v) { return this.is(v) ? this.next() : null; }
  expect(v, what) {
    if (this.is(v)) return this.next();
    const t = this.peek();
    throw new MVError(`Expected "${v}"${what ? ' ' + what : ''} but found ${desc(t)}.`, t.pos);
  }
  ident(what = 'a name') {
    const t = this.peek();
    if (t.t === 'id') { this.i++; return t.v; }
    throw new MVError(`Expected ${what} but found ${desc(t)}.`, t.pos);
  }
  args(close) {
    const a = [];
    if (!this.is(close)) do a.push(this.expr()); while (this.accept(','));
    this.expect(close);
    return a;
  }

  /* ---------- statements ---------- */
  statement() {
    const t = this.peek();
    let node = null;
    if (t.t === 'kw') switch (t.v) {
      case 'import': {
        this.next();
        const names = [this.ident('a library name')];
        while (this.accept(',')) names.push(this.ident('a library name'));
        node = { type: 'import', names };
        if (this.accept('as')) {
          if (names.length > 1) throw new MVError('"as" renames one library at a time: import topology as top.', this.peek().pos);
          node.alias = this.ident('a short name for the library');
        }
        break;
      }
      case 'library': this.next(); node = { type: 'library', name: this.ident('a library name') }; break;
      case 'let': {
        this.next();
        const name = this.ident();
        if (!this.accept('=') && !this.accept(':=')) this.expect('=');
        node = { type: 'let', name, expr: this.expr() };
        break;
      }
      case 'def': {
        this.next();
        const name = this.ident('the name being defined');
        let params = null, types = null;
        if (this.accept('(')) {
          params = []; types = [];
          if (!this.is(')')) do {
            params.push(this.ident('a parameter name'));
            types.push(this.accept(':') ? this.domain() : null);
          } while (this.accept(','));
          this.expect(')');
        }
        if (!this.accept(':=') && !this.accept('=')) this.expect(':=', 'after the name being defined');
        node = { type: 'def', name, params, types, body: this.expr(), pos: t.pos };
        break;
      }
      case 'theorem': case 'lemma': case 'claim': case 'conjecture': case 'check': {
        this.next();
        let name = null;
        if (this.peek().t === 'id' && this.is(':', 1)) { name = this.next().v; this.next(); }
        else this.accept(':');
        node = { type: 'check', kind: t.v, name, body: this.expr() };
        break;
      }
      case 'plot': {
        this.next();
        const exprs = [this.expr()];
        while (this.accept(',')) exprs.push(this.expr());
        this.expect('for', 'followed by a variable and its range, as in "for x in [-5, 5]"');
        node = { type: 'plot', exprs, binders: this.binders() };
        break;
      }
      case 'structure': {
        this.next();
        const name = this.ident('the structure\'s name');
        const params = [], types = [];
        this.expect('(', 'and the fields, as in structure Group(G, op, e)');
        if (!this.is(')')) do {
          params.push(this.ident('a field name'));
          types.push(this.accept(':') ? this.domain() : null);
        } while (this.accept(','));
        this.expect(')');
        const parent = this.accept('extends') ? this.ident('the structure it extends') : null;
        const axioms = [];
        if (this.accept('where')) {
          // Axioms: "name: formula", one after another (each usually on its own indented line).
          while (this.peek().t === 'id' && this.is(':', 1)) {
            const an = this.next().v;
            this.next();
            axioms.push({ name: an, body: this.expr() });
          }
          if (!axioms.length) throw new MVError('After "where", list the axioms as "name: formula".', this.peek().pos);
        }
        node = { type: 'structure', name, params, types, parent, axioms, pos: t.pos };
        break;
      }
      case 'concept': {
        // concept name(params) where form: expr …  — one notion, several equivalent definitions.
        this.next();
        const name = this.ident('the concept\'s name');
        let params = null, types = null;
        if (this.accept('(')) {
          params = []; types = [];
          if (!this.is(')')) do {
            params.push(this.ident('a parameter name'));
            types.push(this.accept(':') ? this.domain() : null);
          } while (this.accept(','));
          this.expect(')');
        }
        this.expect('where', 'and its forms, as in concept open_set(U) where balls: … complement: …');
        const forms = [];
        while (this.peek().t === 'id' && this.is(':', 1)) {
          const fn = this.next().v;
          this.next();
          if (forms.some(f => f.name === fn)) throw new MVError(`${name} already has a form called ${fn}.`, this.peek().pos);
          forms.push({ name: fn, body: this.expr() });
        }
        if (forms.length < 2) throw new MVError('After "where", give at least two forms, each as "name: formula".', this.peek().pos);
        node = { type: 'concept', name, params, types, forms, pos: t.pos };
        break;
      }
      case 'interpret': {
        this.next();
        node = { type: 'interpret', expr: this.expr(), pos: t.pos };
        break;
      }
      case 'vary': {
        this.next();
        node = { type: 'vary', name: this.ident('the name of a definition or lemma'), pos: t.pos };
        break;
      }
      case 'explain': {
        this.next();
        const name = this.ident('the name of a definition, lemma, function or set');
        node = { type: 'explain', name, binders: this.accept('for') ? this.binders() : null, pos: t.pos };
        break;
      }
      case 'show': {
        this.next();
        const name = this.ident('a view name');
        this.expect('(');
        node = { type: 'show', name, args: this.args(')') };
        break;
      }
    }
    if (!node) node = { type: 'eval', expr: this.expr() };
    const end = this.peek();
    if (end.t !== 'eof') throw trailing(this.t, this.i, end);
    return node;
  }

  /* ---------- expressions, lowest precedence first ---------- */
  expr() {
    const body = this.iff();
    if (!this.accept('where')) return body;
    const binds = [];
    do {
      const name = this.ident('a name to define after "where"');
      if (!this.accept('=') && !this.accept(':=')) this.expect('=');
      binds.push({ name, expr: this.iff() });
    } while (this.accept(','));
    return { type: 'where', body, binds };
  }
  iff() { let a = this.imp(); while (this.accept('<->')) a = bin('<->', a, this.imp()); return a; }
  imp() { const a = this.or(); return this.accept('->') ? bin('->', a, this.imp()) : a; }
  or() { let a = this.and(); while (this.accept('or')) a = bin('or', a, this.and()); return a; }
  and() { let a = this.not(); while (this.accept('and')) a = bin('and', a, this.not()); return a; }
  not() { return this.accept('not') ? { type: 'un', op: 'not', a: this.not() } : this.rel(); }
  rel() {
    let first = this.add();
    if (this.accept('..')) first = { type: 'range', lo: first, hi: this.add() };
    if (this.is('in') || this.is('notin')) {
      const neg = this.next().v === 'notin';
      return { type: 'in', neg, elem: first, dom: this.domain() };
    }
    if (this.isWord('subset')) { this.next(); return { type: 'subset', a: first, b: this.add() }; }
    const args = [first], ops = [];
    while (this.peek().t === 'op' && CMP.has(this.peek().v)) { ops.push(this.next().v); args.push(this.add()); }
    return ops.length ? { type: 'cmp', ops, args } : first;
  }
  add() {
    let a = this.mul();
    for (;;) {
      if (this.accept('+')) a = bin('+', a, this.mul());
      else if (this.accept('-')) a = bin('-', a, this.mul());
      else if (this.accept('\\')) a = bin('\\', a, this.mul());
      else if (this.isWord('union')) { this.next(); a = bin('union', a, this.mul()); }
      else return a;
    }
  }
  mul() {
    let a = this.unary();
    for (;;) {
      const t = this.peek();
      if (this.accept('*')) a = bin('*', a, this.unary(), { implicit: t.implicit });
      else if (this.accept('/')) a = bin('/', a, this.unary());
      else if (this.accept('mod')) a = bin('mod', a, this.unary());
      else if (this.isWord('inter')) { this.next(); a = bin('inter', a, this.unary()); }
      else return a;
    }
  }
  unary() {
    if (this.accept('-')) return { type: 'un', op: 'neg', a: this.unary() };
    if (this.accept('+')) return this.unary();
    if (this.accept('√')) return { type: 'un', op: 'sqrt', a: this.unary() };
    if (this.is('forall') || this.is('exists')) return this.quant();
    return this.pow();
  }
  quant() {
    const q = this.next().v;
    const binders = this.binders();
    this.expect(':', 'after the quantified variables');
    return { type: 'quant', q, binders, body: this.expr() };
  }

  /* A binder list: "a, b in D, (x, y) in R^2, ε > 0". */
  binders() {
    const out = [];
    do {
      const items = [this.binderTarget()];
      while (this.is(',') && (this.peek(1).t === 'id' || this.is('(', 1))) { this.next(); items.push(this.binderTarget()); }
      let dom;
      if (this.accept('in')) dom = this.domain();
      else if (this.peek().t === 'op' && ['>', '>=', '<', '<='].includes(this.peek().v)) {
        const op = this.next().v;
        dom = { type: 'bound', op, c: this.add() };
      } else {
        const t = this.peek();
        const shown = items.map(x => x.pattern ? `(${x.pattern.join(', ')})` : x.name).join(', ');
        throw new MVError(`Expected "in" and a range after ${shown}, as in "${shown} in [0, 1]".`, t.pos);
      }
      for (const it of items) out.push({ ...it, dom });
    } while (this.accept(','));
    return out;
  }
  binderTarget() {
    const t = this.peek();
    if (this.accept('(')) {
      const pattern = [this.ident('a variable name')];
      while (this.accept(',')) pattern.push(this.ident('a variable name'));
      this.expect(')');
      return { name: null, pattern, pos: t.pos };
    }
    return { name: this.ident('a variable name'), pattern: null, pos: t.pos };
  }
  // Does a binder list start at offset k? Used to tell "max x in S: …" from "max(a, b)".
  binderAhead(k) {
    const t = this.peek(k);
    if (t.t === 'id') {
      const n = this.peek(k + 1);
      return (n.t === 'kw' && n.v === 'in') || (n.t === 'op' && [',', '>', '>=', '<', '<='].includes(n.v));
    }
    if (this.is('(', k)) {
      let j = k + 1;
      while (this.peek(j).t === 'id' && this.is(',', j + 1)) j += 2;
      return this.peek(j).t === 'id' && this.is(')', j + 1) && this.is('in', j + 2) && j > k + 1;
    }
    return false;
  }
  domain() {
    if (this.is('[') || this.is('(')) {
      const save = this.i;
      const open = this.next().v;
      try {
        const lo = this.expr();
        if (this.accept(',')) {
          const hi = this.expr();
          if (this.is(']') || this.is(')')) {
            const close = this.next().v;
            let d = { type: 'interval', lo, hi, loOpen: open === '(', hiOpen: close === ')' };
            // Products of intervals: [0, 1]^2, [0, 1] * [2, 3].
            for (;;) {
              if (this.accept('^')) d = bin('^', d, this.unary());
              else if (this.accept('*')) d = bin('*', d, this.is('[') || this.is('(') ? this.domain() : this.unary());
              else return d;
            }
          }
        }
      } catch (e) { /* not an interval; reparse below */ }
      this.i = save;
    }
    const a = this.add();
    return this.accept('..') ? { type: 'range', lo: a, hi: this.add() } : a;
  }
  pow() {
    const base = this.postfix();
    return this.accept('^') ? bin('^', base, this.unary()) : base;
  }
  postfix() {
    let e = this.primary();
    for (;;) {
      const t = this.peek();
      if (this.accept('(')) e = { type: 'call', f: e, args: this.args(')'), pos: t.pos };
      else if (this.accept('[')) e = { type: 'index', obj: e, args: this.args(']'), pos: t.pos };
      else if (this.accept('!')) e = { type: 'un', op: 'fact', a: e };
      else if (this.accept('.')) e = { type: 'field', obj: e, name: this.ident('a field name after "."'), pos: t.pos };
      else return e;
    }
  }
  primary() {
    const t = this.peek();
    if (t.t === 'num') { this.next(); return { type: 'num', v: t.v }; }
    if (t.t === 'kw' && (t.v === 'true' || t.v === 'false')) { this.next(); return { type: 'bool', v: t.v === 'true' }; }
    if (t.t === 'id') {
      if (BIGOPS.has(t.v) && this.binderAhead(1)) {
        this.next();
        const binders = this.binders();
        this.expect(':', `after the variables of ${t.v}`);
        return { type: 'bigop', op: t.v, binders, body: this.add(), pos: t.pos };
      }
      if (t.v === 'lim' && this.peek(1).t === 'id' && this.is('->', 2)) {
        this.next();
        const v = this.ident();
        this.next();
        const to = this.add();
        this.expect(':', 'after the limit, as in "lim n -> inf: 1/n"');
        return { type: 'lim', v, to, body: this.add(), pos: t.pos };
      }
      this.next();
      if (this.accept('=>')) return { type: 'lambda', params: [t.v], body: this.expr() };
      return { type: 'id', name: t.v, pos: t.pos };
    }
    if (this.is('(') || this.is('[')) {
      const open = this.next().v;
      const items = [];
      if (!this.is(')') && !this.is(']')) do items.push(this.expr()); while (this.accept(','));
      const close = this.peek();
      if (!this.is(')') && !this.is(']')) throw new MVError(`Expected "${open === '(' ? ')' : ']'}" but found ${desc(close)}.`, close.pos);
      this.next();
      // Half-open interval literals: [a, b) and (a, b].
      if (open !== (close.v === ')' ? '(' : '[')) {
        if (items.length !== 2) throw new MVError('Mismatched brackets. A half-open interval has two ends, as in [0, 1).', close.pos);
        return { type: 'interval', lo: items[0], hi: items[1], loOpen: open === '(', hiOpen: close.v === ')' };
      }
      if (open === '[') return { type: 'list', items };
      if (this.accept('=>')) {
        if (!items.every(x => x.type === 'id')) throw new MVError('Function parameters must be plain names, as in (a, b) => a + b.', t.pos);
        return { type: 'lambda', params: items.map(x => x.name), body: this.expr() };
      }
      if (!items.length) throw new MVError('Empty parentheses.', t.pos);
      return items.length === 1 ? items[0] : { type: 'tuple', items };
    }
    if (this.accept('|')) {
      const e = this.add();
      this.expect('|', 'to close the absolute value');
      return { type: 'abs', e };
    }
    if (this.accept('{')) {
      if (this.peek().t === 'id' && this.is('=', 1)) {
        const fields = [];
        do {
          const name = this.ident('a field name');
          this.expect('=');
          fields.push({ name, expr: this.expr() });
        } while (this.accept(','));
        this.expect('}');
        return { type: 'record', fields };
      }
      const save = this.i;
      let binders = null;
      try { binders = this.binders(); if (!this.is('|')) binders = null; } catch (e) { binders = null; }
      if (binders) {
        this.next();
        const pred = this.expr();
        this.expect('}');
        return { type: 'setb', binders, pred };
      }
      this.i = save;
      return { type: 'finite', items: this.args('}') };
    }
    if (this.accept('if')) {
      const c = this.expr();
      this.expect('then');
      const a = this.expr();
      this.expect('else');
      return { type: 'if', c, a, b: this.expr() };
    }
    throw new MVError(`Unexpected ${desc(t)}.`, t.pos);
  }
}

/* ================= Statements ================= */

/* Split source into statements. A line continues the previous statement when it is indented,
   when brackets are still open, or when the previous line ends in an operator. Comment lines
   directly above a statement become its documentation. */
const CONT_END = /(:=|=>|->|<->|[,:=+\-*/^(\[{\\]|\band|\bor|\bimplies|\bwhere|[∀∃∧∨⇒→⇔∈≤≥⊆∪∩])\s*$/;
function splitStatements(src) {
  const lines = src.split('\n');
  const out = [];
  let cur = null, doc = [];
  lines.forEach((raw, ln) => {
    const comment = /^\s*#\s?(.*)$/.exec(raw);
    if (comment) { if (!cur || !(cur.depth > 0)) doc.push(comment[1]); return; }
    const code = raw.replace(/\s#.*$|\/\/.*$/, '');
    if (!code.trim()) { doc = []; return; }
    if (cur && (/^\s/.test(code) || cur.depth > 0 || CONT_END.test(cur.text))) {
      cur.text += '\n' + code;
      cur.lines.push(ln + 1);
      cur.endLine = ln + 1;
    } else {
      cur = { text: code, line: ln + 1, endLine: ln + 1, lines: [ln + 1], depth: 0, doc: doc.join(' ').trim(), docLines: doc.slice() };
      out.push(cur);
    }
    doc = [];
    for (const ch of code) {
      if ('([{'.includes(ch)) cur.depth++;
      else if (')]}'.includes(ch)) cur.depth--;
    }
  });
  return out;
}

function parseStatement(stmt) {
  if (/^\s*proof\b/.test(stmt.text)) return parseProof(stmt);
  if (/^\s*diagram\b/.test(stmt.text)) return parseDiagram(stmt);
  return new Parser(tokenize(stmt.text)).statement();
}

/* A diagram of maps between finite sets or groups, checked exhaustively:
     diagram first_iso:
       f: G -> H                 an arrow: the map f from G to H
       q: G -> Q
       fbar: Q -> H
       fbar ∘ q = f              a face that must commute (apply q, then fbar)
       exact at B                image of the arrow into B = kernel of the arrow out of B
       commutes                  every two paths with the same ends must agree
   Steps start at the diagram's indentation; deeper-indented lines continue one. */
function parseDiagram(stmt) {
  const text = stmt.text;
  const head = /^(\s*)diagram\b[ \t]*([\p{L}_][\p{L}\p{N}_']*)?[ \t]*:[ \t]*/u.exec(text);
  if (!head) throw new MVError('Write "diagram name:" and then, on indented lines, arrows "f: A -> B" and equations "g ∘ f = h".', 0);
  const node = { type: 'diagram', name: head[2] || null, arrows: [], equations: [], exact: [], all: false, pos: head[1].length };
  let pos = head[0].length;
  const rest = text.slice(pos);
  if (rest.split('\n')[0].trim()) throw new MVError('Put each arrow and equation of the diagram on its own indented line below "diagram:".', pos);
  const groups = [];
  let indent = null;
  for (const line of rest.split('\n')) {
    const at = pos;
    pos += line.length + 1;
    if (!line.trim()) continue;
    const ind = /^\s*/.exec(line)[0].length;
    if (indent === null) indent = ind;
    if (ind > indent && groups.length) groups[groups.length - 1].text += ' ' + line.trim();
    else groups.push({ text: line.trim(), pos: at + ind });
  }
  if (!groups.length) throw new MVError('This diagram is empty. Add arrows such as "f: A -> B".', pos);
  const NAME = /^[\p{L}_][\p{L}\p{N}_']*$/u;
  const expr = (s, p) => {
    const toks = tokenize(s);
    for (const t of toks) t.pos += p;
    const P = new Parser(toks), e = P.expr();
    if (P.peek().t !== 'eof') throw new MVError(`Unexpected "${P.peek().v}" here.`, P.peek().pos);
    return e;
  };
  for (const g of groups) {
    const s = g.text;
    let m;
    if (/^commutes$/i.test(s)) { node.all = true; continue; }
    if ((m = /^exact\s+at\s+(.+)$/u.exec(s))) { node.exact.push({ text: m[1].trim(), node: expr(m[1].trim(), g.pos), pos: g.pos }); continue; }
    if ((m = /^([\p{L}_][\p{L}\p{N}_']*)\s*:\s*(.+?)\s*(?:->|→)\s*(.+)$/u.exec(s))) {
      const [, name, a, b] = m;
      node.arrows.push({ name, srcText: a, dstText: b, src: expr(a, g.pos), dst: expr(b, g.pos), pos: g.pos });
      continue;
    }
    if ((m = /^(.+?)\s*=\s*(.+)$/u.exec(s))) {
      const path = t => t.split(/\s*(?:∘|\bo\b)\s*/u).map(x => x.trim());
      const left = path(m[1]), right = path(m[2]);
      for (const n of [...left, ...right]) if (!NAME.test(n)) throw new MVError(`In "${s}", "${n}" should be the name of an arrow; compose arrows with ∘ (or o), as in g ∘ f = h.`, g.pos);
      node.equations.push({ text: s, left, right, pos: g.pos });
      continue;
    }
    throw new MVError(`A diagram line is an arrow "f: A -> B", an equation "g ∘ f = h", "exact at B" or "commutes"; "${s}" is none of these.`, g.pos);
  }
  return node;
}

/* A proof sketch:
     proof of name:
       let ε                       take an arbitrary ε (its range comes from the goal, or: let ε > 0)
       choose δ = min(1, ε/3)      pick a witness for "exists δ"
       let x
       assume |x − 1| < δ          take the hypothesis of an implication
       have |x + 1| < 3            an intermediate fact, checked numerically
       choose N in 1..10^6 such that 1/N < ε    obtain something that exists
       so |x² − 1| < ε             the conclusion
   Blocks hold steps on deeper-indented lines:
       case x >= 0:  …  case x < 0:  …   (or otherwise:)   a split into cases
       induction on n   then   base: …   step: …           induction over the integers
       contradiction                                       suppose the goal fails; aim for "so false"
   "have P by lemma_name" cites a lemma; the checker matches P to its conclusion.
   Steps start at the block's indentation; deeper-indented lines continue a step. */
const STEP_WORDS = { let: 'let', take: 'let', fix: 'let', assume: 'assume', suppose: 'assume', choose: 'choose', pick: 'choose', set: 'choose',
  have: 'have', claim: 'have', note: 'have', so: 'so', hence: 'so', thus: 'so', therefore: 'so', show: 'so', conclude: 'so' };
function parseProof(stmt) {
  const text = stmt.text;
  const head = /^(\s*)proof\b[ \t]*(?:of[ \t]+([\p{L}_][\p{L}\p{N}_']*)[ \t]*)?:[ \t]*/u.exec(text);
  if (!head) throw new MVError('Write "proof of name:" (or just "proof:" right after a theorem), then the steps on indented lines.', 0);
  const node = { type: 'proof', name: head[2] || null, steps: [], pos: head[1].length };
  // Split into steps, remembering where each starts in the statement text.
  const lines = [];
  let off = head[0].length;
  const rest = text.slice(off);
  if (rest.split('\n')[0].trim()) throw new MVError('Put each step of the proof on its own indented line below "proof:".', off);
  let pos = off;
  for (const line of rest.split('\n')) { lines.push({ line, pos }); pos += line.length + 1; }
  const body = lines.filter(l => l.line.trim());
  if (!body.length) throw new MVError('This proof has no steps yet. Add indented lines such as "let ε", "assume …", "have …", "so …".', off);
  node.steps = parseSteps(body);
  return node;
}

// A block's header line: "case P:", "otherwise:", "base:" or "step:", with its steps indented below.
const BLOCK_HEAD = /^(\s*)(case\b[\s\S]*?|otherwise|else|base(?:\s+case)?|(?:inductive\s+)?step)\s*:\s*$/;
const INDUCTION = /^\s*(?:by\s+)?induction\s+(?:on\s+)?([\p{L}_][\p{L}\p{N}_']*)\s*:?\s*$/u;
const CONTRADICTION = /^\s*(?:by\s+contradiction|contradiction|suppose\s+not|assume\s+not)\s*:?\s*$/;

function parseSteps(lines) {
  const indent = Math.min(...lines.map(l => /^\s*/.exec(l.line)[0].length));
  const groups = [];
  for (const l of lines) {
    const ind = /^\s*/.exec(l.line)[0].length;
    if (ind > indent && groups.length) groups[groups.length - 1].children.push(l);
    else groups.push({ head: l, children: [] });
  }
  const steps = [];
  for (const g of groups) {
    const hm = BLOCK_HEAD.exec(g.head.line);
    if (hm) {
      const pos = g.head.pos + hm[1].length;
      const word = hm[2].split(/\s+/)[0];
      if (!g.children.length) throw new MVError(`Put the steps of this ${word} on indented lines below it.`, pos);
      const inner = parseSteps(g.children);
      const prev = steps[steps.length - 1];
      if (word === 'case' || word === 'otherwise' || word === 'else') {
        let cond = null;
        if (word === 'case') {
          const ctext = hm[2].replace(/^case/, '');
          const toks = tokenize(ctext);
          for (const t of toks) t.pos += pos + 4;
          const p = new Parser(toks);
          if (p.peek().t === 'eof') throw new MVError('Write the condition of this case, as in "case x >= 0:".', pos);
          cond = p.expr();
          if (p.peek().t !== 'eof') throw new MVError(`Unexpected "${p.peek().v}" in this case.`, p.peek().pos);
        }
        const c = { cond, steps: inner, pos, word };
        if (prev && prev.kind === 'cases' && prev.open) prev.cases.push(c);
        else if (cond) steps.push({ kind: 'cases', word: 'cases', pos, cases: [c], open: true });
        else throw new MVError('"otherwise:" comes after one or more "case …:" blocks.', pos);
        // After an otherwise, the next case starts a new split.
        if (!cond) steps[steps.length - 1].open = false;
      } else {
        const which = /base/.test(word) ? 'base' : 'step';
        if (!prev || prev.kind !== 'induction') throw new MVError(`"${which}:" belongs right after an "induction on n" step.`, pos);
        if (prev[which]) throw new MVError(`This induction already has a ${which} block.`, pos);
        prev[which] = inner;
        prev[which + 'Pos'] = pos;
      }
      continue;
    }
    const text = [g.head, ...g.children].map(l => l.line).join('\n');
    const im = INDUCTION.exec(text);
    if (im) { steps.push({ kind: 'induction', word: 'induction', pos: g.head.pos + /^\s*/.exec(text)[0].length, name: im[1], text: text.trim(), base: null, step: null }); continue; }
    if (CONTRADICTION.test(text)) { steps.push({ kind: 'contradiction', word: 'contradiction', pos: g.head.pos + /^\s*/.exec(text)[0].length, text: text.trim() }); continue; }
    steps.push(parseStep({ text, pos: g.head.pos }));
  }
  for (const st of steps) delete st.open;
  return steps;
}

function parseStep(g) {
  // "… by <reason>": a lemma's name is checked against the step; any other reason is for the reader.
  let by = null;
  const bm = /^(\s*(?:have|claim|note|so|hence|thus|therefore|show|conclude)\b[\s\S]*?)\s+by\s+([\s\S]+)$/.exec(g.text);
  if (bm) { by = bm[2].replace(/\s+/g, ' ').trim(); g.text = bm[1]; }
  // "choose N in D such that P": a colon, so "1000 such" isn't read as 1000·such. (Same length, so positions hold.)
  if (/^\s*(?:choose|pick)\b/.test(g.text)) g.text = g.text.replace(/(\s)such(\s+)that(\s)/, (m, a, b, c) => a + ':' + ' '.repeat(7 + b.length) + c).replace(/(\s)with(\s)/, '$1:   $2');
  const toks = tokenize(g.text);
  for (const t of toks) t.pos += g.pos;
  const p = new Parser(toks);
  const first = p.peek();
  const kind = STEP_WORDS[first.v];
  if (!kind || !(first.t === 'id' || first.t === 'kw')) {
    throw new MVError(`Each step starts with let, assume, choose, have or so, or is a block (case …:, induction on n, contradiction) (got "${first.v ?? g.text.trim()}").`, first.pos);
  }
  p.next();
  const step = { kind, word: first.v, pos: first.pos, text: g.text.trim() };
  if (kind === 'let') {
    // let x, y   |   let x in D   |   let ε > 0   |   let x, y in D, n in N
    const names = [];
    step.binders = [];
    const flush = dom => { for (const n of names) step.binders.push({ name: n.name, pattern: null, pos: n.pos, dom }); names.length = 0; };
    do {
      const t = p.peek();
      names.push({ name: p.ident('a variable name'), pos: t.pos });
      if (p.accept('in')) flush(p.domain());
      else if (p.peek().t === 'op' && ['>', '>=', '<', '<='].includes(p.peek().v)) { const op = p.next().v; flush({ type: 'bound', op, c: p.add() }); }
    } while (p.accept(','));
    flush(null);
  } else if (kind === 'choose') {
    const t = p.peek();
    step.name = p.ident('the name of what you choose');
    step.namePos = t.pos;
    if (p.accept('=') || p.accept(':=')) step.expr = p.expr();
    else if (p.accept('in')) {
      step.dom = p.domain();
      // "such that P" or "with P"
      if (p.isWord('such') && p.isWord('that', 1)) { p.next(); p.next(); }
      else if (p.isWord('with') || p.is('where')) p.next();
      else if (!p.accept(':')) throw new MVError('Write "choose x = value" or "choose x in D such that P".', p.peek().pos);
      step.cond = p.expr();
    } else throw new MVError('Write "choose x = value" or "choose x in D such that P".', p.peek().pos);
  } else {
    step.expr = p.expr();
    if (by) step.by = by;
  }
  if (p.peek().t !== 'eof') throw new MVError(`Unexpected "${p.peek().v}" in this step.`, p.peek().pos);
  return step;
}

// Something left over after a complete statement: name the likely slip.
function trailing(toks, i, end) {
  const prev = toks[i - 1];
  if (end.v === '=>') return new MVError('"=>" makes a function, as in x => x^2. For "at least" write >=, and for "implies" write ->.', end.pos);
  if (prev && prev.t === 'id' && (end.t === 'num' || end.t === 'id'))
    return new MVError(`Put the argument in brackets: ${prev.v}(${end.v}).` + (end.t === 'id' ? ` Two names side by side aren't multiplied; write ${prev.v}*${end.v} for a product.` : ''), end.pos);
  if (end.v === ')' || end.v === ']' || end.v === '}') return new MVError(`There's an extra "${end.v}" here, or an opening bracket is missing before it.`, end.pos);
  return new MVError(`Unexpected ${desc(end)}. Each statement goes on its own line; indent a line to continue the previous one.`, end.pos);
}

function locate(stmt, pos) {
  if (!stmt) return null;
  if (pos == null) return { line: stmt.line, col: null, text: stmt.text.split('\n')[0] };
  const before = stmt.text.slice(0, pos).split('\n');
  const k = before.length - 1;
  return { line: stmt.lines[k] || stmt.line, col: before[k].length, text: stmt.text.split('\n')[k] };
}

/* ================= Free names (for checking definitions when they are written) ================= */

function binderNames(b) { return b.pattern ? b.pattern : [b.name]; }

function freeNames(node, bound = new Set(), out = new Map()) {
  const walk = (n, sc) => {
    if (!n || typeof n !== 'object') return;
    switch (n.type) {
      case 'id': if (!sc.has(n.name) && !out.has(n.name)) out.set(n.name, n.pos); return;
      case 'value': return;
      case 'lambda': { const s = new Set(sc); n.params.forEach(p => s.add(p)); walk(n.body, s); return; }
      case 'quant': case 'bigop': case 'setb': {
        const s = new Set(sc);
        for (const b of n.binders) { walkDom(b.dom, s); binderNames(b).forEach(x => s.add(x)); }
        walk(n.body || n.pred, s);
        return;
      }
      case 'lim': { walk(n.to, sc); const s = new Set(sc); s.add(n.v); walk(n.body, s); return; }
      case 'where': {
        const s = new Set(sc);
        for (const b of n.binds) { walk(b.expr, s); s.add(b.name); }
        walk(n.body, s);
        return;
      }
      default:
        for (const [k, v] of Object.entries(n)) {
          if (k === 'type' || k === 'pos') continue;
          if (Array.isArray(v)) v.forEach(x => x && typeof x === 'object' && walk(x, sc));
          else if (v && typeof v === 'object' && v.type) walk(v, sc);
        }
    }
  };
  const walkDom = (d, sc) => { if (d.type === 'bound') walk(d.c, sc); else walk(d, sc); };
  walk(node, bound);
  return out;
}

/* ================= Substitution (used to unfold definitions inside claims) ================= */

function subst(node, map) {
  const freeIn = new Set();
  for (const v of map.values()) for (const k of freeNames(v).keys()) freeIn.add(k);
  let fresh = 0;
  const rename = (name, sc) => {
    if (!freeIn.has(name)) return name;
    let nn;
    do nn = name + "'".repeat(++fresh); while (freeIn.has(nn));
    sc.set(name, { type: 'id', name: nn });
    return nn;
  };
  const go = (n, m) => {
    if (!n || typeof n !== 'object') return n;
    if (Array.isArray(n)) return n.map(x => go(x, m));
    if (n.type === 'id') return m.has(n.name) ? m.get(n.name) : n;
    if (n.type === 'value') return n;
    const shadow = (names, mm) => { names.forEach(x => mm.delete(x)); return mm; };
    switch (n.type) {
      case 'lambda': {
        const mm = shadow(n.params, new Map(m));
        const params = n.params.map(p => rename(p, mm));
        return { ...n, params, body: go(n.body, mm) };
      }
      case 'quant': case 'bigop': case 'setb': {
        const mm = new Map(m);
        const binders = n.binders.map(b => {
          const dom = b.dom.type === 'bound' ? { ...b.dom, c: go(b.dom.c, mm) } : go(b.dom, mm);
          shadow(binderNames(b), mm);
          return b.pattern ? { ...b, dom, pattern: b.pattern.map(x => rename(x, mm)) } : { ...b, dom, name: rename(b.name, mm) };
        });
        return n.type === 'setb' ? { ...n, binders, pred: go(n.pred, mm) } : { ...n, binders, body: go(n.body, mm) };
      }
      case 'lim': {
        const mm = shadow([n.v], new Map(m));
        const v = rename(n.v, mm);
        return { ...n, v, to: go(n.to, m), body: go(n.body, mm) };
      }
      case 'where': {
        const mm = new Map(m);
        const binds = n.binds.map(b => { const expr = go(b.expr, mm); mm.delete(b.name); return { name: rename(b.name, mm), expr }; });
        return { ...n, binds, body: go(n.body, mm) };
      }
    }
    const out = {};
    for (const [k, v] of Object.entries(n)) out[k] = (v && typeof v === 'object') ? go(v, m) : v;
    return out;
  };
  return go(node, map);
}

/* ================= Pretty printer ================= */

const GREEK = { alpha: 'α', beta: 'β', gamma: 'γ', delta: 'δ', eps: 'ε', epsilon: 'ε', theta: 'θ', lambda: 'λ', mu: 'μ', pi: 'π', sigma: 'σ', tau: 'τ', phi: 'φ', omega: 'ω' };
const BB = { R: 'ℝ', Z: 'ℤ', N: 'ℕ', inf: '∞' };
const CMP_OUT = { '<': '<', '<=': '≤', '>': '>', '>=': '≥', '=': '=', '!=': '≠', '~=': '≈' };
const PREC = { quant: 0, lambda: 0, if: 0, where: 0, '<->': 1, '->': 2, or: 3, and: 4, not: 5, cmp: 6, in: 6, subset: 6, range: 6, '+': 7, '-': 7, '\\': 7, union: 7, bigop: 7, '*': 8, '/': 8, mod: 8, inter: 8, neg: 9, sqrt: 10, '^': 11, post: 12, atom: 13 };
const BIG_OUT = { sum: '∑', prod: '∏', sup: 'sup', inf: 'inf', max: 'max', min: 'min' };

function idOut(name, H, asFunc, asSpace) {
  const base = GREEK[name] || (asSpace || name === 'inf' ? BB[name] : null) || name;
  if (!H) return base;
  const m = /^([^\d']+?)(\d+)('*)$/.exec(base);
  const html = m ? esc(m[1]) + '<sub>' + m[2] + '</sub>' + m[3] : esc(base);
  const single = [...(m ? m[1] : base.replace(/'+$/, ''))].length === 1;
  return (!asFunc && single && !(asSpace && BB[name])) ? `<i>${html}</i>` : `<span class="up">${html}</span>`;
}

function pp(n, H = true, p = 0) {
  const r = (x, q) => pp(x, H, q);
  const kw = w => H ? `<span class="fkw">${w}</span>` : w;
  const sub = s => H ? `<sub>${s}</sub>` : ` ${s}: `;
  let s, my = PREC.atom;
  switch (n.type) {
    case 'num': s = fmtNum(n.v); break;
    case 'bool': s = n.v ? 'true' : 'false'; break;
    case 'value': s = H ? `<span class="up">${esc(n.label)}</span>` : n.label; break;
    case 'id': s = idOut(n.name, H); break;
    case 'bin': {
      my = PREC[n.op];
      if (n.op === '^') { s = r(n.a, PREC.post) + (H ? `<sup>${r(n.b, 0)}</sup>` : '^' + r(n.b, PREC.post)); break; }
      const O = { '+': ' + ', '-': ' − ', '*': '·', '/': '/', mod: ' mod ', and: ' ∧ ', or: ' ∨ ', '->': ' ⇒ ', '<->': ' ⇔ ', union: ' ∪ ', inter: ' ∩ ', '\\': ' ∖ ' };
      let o = O[n.op];
      if (n.op === '*' && (n.implicit || (n.a.type === 'num' && ['id', 'call', 'abs'].includes(n.b.type)))) o = '';
      const right = n.op === '->';
      s = r(n.a, right ? my + 1 : my) + o + r(n.b, right ? my : my + 1);
      break;
    }
    case 'cmp':
      my = PREC.cmp;
      s = n.args.map((a, i) => (i ? ' ' + CMP_OUT[n.ops[i - 1]] + ' ' : '') + r(a, PREC.cmp + 1)).join('');
      break;
    case 'in': my = PREC.in; s = r(n.elem, PREC.in + 1) + (n.neg ? ' ∉ ' : ' ∈ ') + ppDom(n.dom, H); break;
    case 'subset': my = PREC.subset; s = r(n.a, PREC.subset + 1) + ' ⊆ ' + r(n.b, PREC.subset + 1); break;
    case 'range': my = PREC.range; s = r(n.lo, PREC.range + 1) + '..' + r(n.hi, PREC.range + 1); break;
    case 'un':
      if (n.op === 'neg') { my = PREC.neg; s = '−' + r(n.a, PREC.neg); }
      else if (n.op === 'not') { my = PREC.not; s = '¬' + r(n.a, PREC.not); }
      else if (n.op === 'sqrt') { my = PREC.sqrt; s = '√' + r(n.a, PREC.post); }
      else { my = PREC.post; s = r(n.a, PREC.post) + '!'; }
      break;
    case 'abs': s = '|' + r(n.e, 0) + '|'; break;
    case 'call':
      my = PREC.post;
      // Arguments that name a number space (R, R^2) are shown as ℝ, ℝ².
      s = (n.f.type === 'id' ? idOut(n.f.name, H, true) : r(n.f, PREC.post)) + '(' + n.args.map(a => isSpaceName(a) ? ppDom(a, H) : r(a, 0)).join(', ') + ')';
      break;
    case 'index':
      my = PREC.post;
      s = (n.obj.type === 'id' ? idOut(n.obj.name, H, true, true) : r(n.obj, PREC.post)) + '[' + n.args.map(a => r(a, 0)).join(', ') + ']';
      break;
    case 'list': s = '[' + n.items.map(a => r(a, 0)).join(', ') + ']'; break;
    case 'tuple': s = '(' + n.items.map(a => r(a, 0)).join(', ') + ')'; break;
    case 'finite': s = n.items.length ? '{' + n.items.map(a => r(a, 0)).join(', ') + '}' : '∅'; break;
    case 'field': my = PREC.post; s = r(n.obj, PREC.post) + '.' + idOut(n.name, H, true); break;
    case 'record': s = '{' + n.fields.map(f => idOut(f.name, H, true) + ' = ' + r(f.expr, 0)).join(', ') + '}'; break;
    case 'if': my = PREC.if; s = `${kw('if')} ${r(n.c, 0)} ${kw('then')} ${r(n.a, 0)} ${kw('else')} ${r(n.b, 0)}`; break;
    case 'lambda':
      my = PREC.lambda;
      s = (n.params.length === 1 ? idOut(n.params[0], H) : '(' + n.params.map(x => idOut(x, H)).join(', ') + ')') + ' ↦ ' + r(n.body, 0);
      break;
    case 'quant': my = PREC.quant; s = (n.q === 'forall' ? '∀' : '∃') + ppBinders(n.binders, H) + ': ' + r(n.body, 0); break;
    case 'bigop': my = PREC.bigop; s = (H ? `<span class="up">${BIG_OUT[n.op]}</span>` : n.op) + sub(ppBinders(n.binders, H)) + (H ? ' ' : '') + r(n.body, PREC.bigop + 1); break;
    case 'lim': my = PREC.bigop; s = (H ? '<span class="up">lim</span>' : 'lim') + sub(idOut(n.v, H) + ' → ' + r(n.to, PREC.post)) + (H ? ' ' : '') + r(n.body, PREC.bigop + 1); break;
    case 'where': my = PREC.where; s = r(n.body, 1) + ` ${kw('where')} ` + n.binds.map(b => idOut(b.name, H) + ' = ' + r(b.expr, 1)).join(', '); break;
    case 'setb': s = '{' + ppBinders(n.binders, H) + ' | ' + r(n.pred, 0) + '}'; break;
    case 'interval': case 'bound': s = ppDom(n, H); break;
    default: s = '?';
  }
  return my < p ? '(' + s + ')' : s;
}

const isSpaceName = a => (a.type === 'id' && 'RZN'.includes(a.name) && a.name.length === 1) || (a.type === 'bin' && a.op === '^' && a.a.type === 'id' && 'RZN'.includes(a.a.name) && a.a.name.length === 1);

function ppTarget(b, H) { return b.pattern ? '(' + b.pattern.map(x => idOut(x, H)).join(', ') + ')' : idOut(b.name, H); }

function ppBinders(bs, H) {
  const groups = [];
  for (const b of bs) {
    const g = groups[groups.length - 1];
    if (g && g.dom === b.dom) g.items.push(b);
    else groups.push({ dom: b.dom, items: [b] });
  }
  return groups.map(g => g.items.map(b => ppTarget(b, H)).join(', ') +
    (g.dom.type === 'bound' ? ` ${CMP_OUT[g.dom.op]} ${pp(g.dom.c, H, PREC.cmp + 1)}` : ' ∈ ' + ppDom(g.dom, H))).join(', ');
}

function ppDom(d, H) {
  if (d.type === 'interval') return (d.loOpen ? '(' : '[') + pp(d.lo, H) + ', ' + pp(d.hi, H) + (d.hiOpen ? ')' : ']');
  if (d.type === 'bound') return `${CMP_OUT[d.op]} ${pp(d.c, H)}`;
  if (d.type === 'id') return idOut(d.name, H, false, true);
  if (d.type === 'bin' && d.op === '^' && d.a.type === 'id') return idOut(d.a.name, H, false, true) + (H ? `<sup>${pp(d.b, H)}</sup>` : '^' + pp(d.b, H, PREC.post));
  if (d.type === 'call' && d.f.type === 'id' && d.args.length === 1 && d.args[0].type === 'id' && BB[d.args[0].name]) return idOut(d.f.name, H, true) + '(' + idOut(d.args[0].name, H, false, true) + ')';
  return pp(d, H, d.type === 'range' ? 0 : PREC.cmp + 1);
}

const ppText = n => pp(n, false);

Object.assign(MV, {
  MVError, esc, fmtNum, tokenize, Parser, splitStatements, parseStatement, locate, freeNames, subst, binderNames,
  pp, ppText, ppBinders, ppTarget, ppDom, idOut, KW, BIGOPS,
});

})(typeof window !== 'undefined' ? window : globalThis);
