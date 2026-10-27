/* Theorem Sketchpad — plain words to notation. A small grammar for the way simple mathematical
   statements are said in English:

     for every real number x, x squared is at least 0        → check forall x in R: x^2 >= 0
     there is a natural number n such that n squared exceeds 50 → check exists n in N: n^2 > 50
     every continuous function on [0, 1] is bounded          → import functions
                                                                check forall f in Functions(R): continuous_on(f, 0, 1) -> bounded_on(f, 0, 1)
     the sum of k for k from 1 to n equals n(n + 1)/2 for every natural number n
                                                             → check forall n in N: sum k in 1..n: k = n*(n + 1)/2
     if n is even then n squared is even                     → check forall n in Z: n mod 2 = 0 -> n^2 mod 2 = 0

   Words are matched as phrases (longest first), then parsed: statements, quantifiers, if/then,
   and/or/not, comparisons, properties (even, prime, continuous, bounded, …), arithmetic in words.
   Notation written directly (x^2 + 1, [0, 1], f(x)) passes through. Whatever isn't understood is
   reported, and the result is checked by the real parser before it is offered. */
'use strict';
(function (global) {
const MV = global.MV;

/* ---------- phrases ---------- */
const K = (k, extra = {}) => ({ k, ...extra });
const PHRASES = [];
const add = (k, list, extra) => list.split('|').forEach(p => PHRASES.push([p.split(' '), K(k, extra)]));
add('CHECK', 'prove that|show that|check that|verify that|is it true that|prove|show|check|verify|claim that|claim');
add('FORALL', 'for all|for every|for each|for any|given any|whatever');
add('EXISTS', 'there is|there are|there exists|there exist|we can find|one can find|for some|there is some');
add('ST', 'such that|so that|for which|with the property that|with');
add('EVERY', 'every|each|all|any');
add('NO', 'no');
add('SOME', 'some');
add('IFF', 'if and only if|iff|exactly when|precisely when|is equivalent to');
add('IF', 'if');
add('WHENEVER', 'whenever');
add('THEN', 'then');
add('IMPLIES', 'implies that|implies|means that');
add('AND', 'and');
add('OR', 'or');
add('NOT', 'it is not true that|it is not the case that|not');
add('CMP', 'is greater than or equal to|is bigger than or equal to|is at least|is no less than|is not less than|greater than or equal to|at least', { op: '>=' });
add('CMP', 'is less than or equal to|is smaller than or equal to|is at most|is no more than|is no greater than|is not greater than|does not exceed|less than or equal to|at most', { op: '<=' });
add('CMP', 'is greater than|is bigger than|is larger than|is more than|exceeds|greater than|bigger than|larger than|more than|is above', { op: '>' });
add('CMP', 'is less than|is smaller than|is below|less than|smaller than|fewer than', { op: '<' });
add('CMP', 'is not equal to|is different from|does not equal|differs from|is unequal to', { op: '!=' });
add('CMP', 'is equal to|equals|is the same as|equal to|is always equal to', { op: '=' });
add('IS', 'is|are|is always|are always');
add('HAS', 'has|have');
add('BETWEEN', 'between');
add('FROM', 'from');
add('TO', 'to|up to|until');
add('IN', 'in|belongs to|lies in|is in|is an element of|is a member of|in the set');
add('OF', 'of');
add('ON', 'on');
add('AT', 'at');
add('FOR', 'for');
add('AS', 'as|when');
add('TENDS', 'goes to|tends to|approaches|grows to|converges to');
add('ART', 'the|an');
add('THAT', 'that|which|who');
add('OP', 'plus|added to', { op: '+' });
add('OP', 'minus|less', { op: '-' });
add('OP', 'times|multiplied by', { op: '*' });
add('OP', 'divided by|over', { op: '/' });
add('OP', 'to the power of|to the power|raised to the power of|raised to', { op: '^' });
add('POST', 'squared', { s: '^2' });
add('POST', 'cubed', { s: '^3' });
add('POST', 'factorial', { s: '!' });
add('UN', 'the square root of|square root of|the root of|root of|sqrt of', { f: 'sqrt' });
add('UN', 'the cube root of|cube root of', { f: 'cbrt' });
add('ABS', 'the absolute value of|absolute value of|the modulus of|the size of');
add('UN', 'sine squared of|sin squared of|sine squared|sin squared', { f: 'sin', pow: 2 });
add('UN', 'cosine squared of|cos squared of|cosine squared|cos squared', { f: 'cos', pow: 2 });
add('UN', 'the sine of|sine of|sin of', { f: 'sin' });
add('UN', 'the cosine of|cosine of|cos of', { f: 'cos' });
add('UN', 'the tangent of|tangent of|tan of', { f: 'tan' });
add('UN', 'the exponential of|exponential of|exp of|e to the power of|e to the', { f: 'exp' });
add('UN', 'the natural logarithm of|the natural log of|natural log of|the logarithm of|the log of|log of|ln of', { f: 'ln' });
add('UN', 'the floor of|floor of', { f: 'floor' });
add('UN', 'the ceiling of|ceiling of', { f: 'ceil' });
add('BIN', 'the sum of|sum of', { op: '+', sum: true });
add('BIN', 'the product of|product of', { op: '*' });
add('BIN', 'the difference of|the difference between|difference of', { op: '-' });
add('BIN', 'the quotient of|the ratio of|quotient of|ratio of', { op: '/' });
add('FN2', 'the maximum of|the max of|the larger of|the greater of|maximum of', { f: 'max' });
add('FN2', 'the minimum of|the min of|the smaller of|the lesser of|minimum of', { f: 'min' });
add('SQ', 'the square of|square of', { s: '^2' });
add('SQ', 'the cube of|cube of', { s: '^3' });
add('TWICE', 'twice|double|two times');
add('HALF', 'half of|half');
add('RECIP', 'the reciprocal of|reciprocal of|one over');
add('LIM', 'the limit of|limit of');
add('SUMFROM', 'the sum from|sum from|sum over');
add('INF', 'infinity|plus infinity');
add('DIVBY', 'divisible by|a multiple of|multiple of');
add('DIVIDES', 'divides');
// Kinds of numbers, for "for every real number x".
add('TYPE', 'positive real numbers|positive real number|positive reals|positive real|positive numbers|positive number', { ty: 'posR' });
add('TYPE', 'nonnegative real numbers|nonnegative real number|non-negative real numbers|non-negative real number|nonnegative numbers|nonnegative number', { ty: 'nonnegR' });
add('TYPE', 'positive integers|positive integer|positive whole numbers|positive whole number', { ty: 'posZ' });
add('TYPE', 'natural numbers|natural number|naturals|natural', { ty: 'N' });
add('TYPE', 'integers|integer|whole numbers|whole number', { ty: 'Z' });
add('TYPE', 'real numbers|real number|reals|real|numbers|number', { ty: 'R' });
add('TYPE', 'points in the plane|point in the plane|points of the plane|point of the plane|points|point', { ty: 'R2' });
// Named sets.
add('SET', 'the real numbers|the reals|the real line', { s: 'R' });
add('SET', 'the natural numbers|the naturals', { s: 'N' });
add('SET', 'the integers|the whole numbers', { s: 'Z' });
add('SET', 'the rational numbers|the rationals', { s: 'Q' });
add('SET', 'the plane', { s: 'R^2' });
add('SET', 'the unit interval', { s: '[0, 1]' });
add('INTERVAL', 'the closed interval|the interval|closed interval|interval', { open: false });
add('INTERVAL', 'the open interval|open interval', { open: true });
// Objects, for "every continuous function …".
add('NOUN', 'functions|function', { n: 'fn' });
add('NOUN', 'sequences|sequence', { n: 'seq' });
add('NOUN', 'subsets of the plane|subset of the plane|sets in the plane|set in the plane', { n: 'set2' });
add('NOUN', 'subsets of the line|subset of the line|sets|set|subsets|subset', { n: 'set' });
add('NOUN', 'groups|group', { n: 'group' });
add('NOUN', 'prime numbers|prime number|primes', { n: 'prime' });
// Properties.
add('ADJ', 'uniformly continuous', { a: 'ucont' });
add('ADJ', 'continuous', { a: 'cont' });
add('ADJ', 'differentiable', { a: 'diff' });
add('ADJ', 'bounded', { a: 'bounded' });
add('ADJ', 'strictly increasing|increasing|monotone increasing|monotonically increasing', { a: 'inc' });
add('ADJ', 'strictly decreasing|decreasing|monotone decreasing|monotonically decreasing', { a: 'dec' });
add('ADJ', 'convex', { a: 'convex' });
add('ADJ', 'convergent|converges|converging', { a: 'conv' });
add('ADJ', 'cauchy|a cauchy sequence', { a: 'cauchy' });
add('ADJ', 'open', { a: 'open' });
add('ADJ', 'closed', { a: 'closed' });
add('ADJ', 'compact', { a: 'compact' });
add('ADJ', 'abelian|commutative', { a: 'abelian' });
add('ADJ', 'cyclic', { a: 'cyclic' });
add('ADJ', 'even|an even number', { a: 'even' });
add('ADJ', 'odd|an odd number', { a: 'odd' });
add('ADJ', 'prime|a prime|a prime number', { a: 'prime' });
add('ADJ', 'positive', { a: 'pos' });
add('ADJ', 'negative', { a: 'neg' });
add('ADJ', 'nonnegative|non-negative', { a: 'nonneg' });
add('ADJ', 'nonzero|non-zero', { a: 'nonzero' });
add('ADJ', 'an integer|a whole number', { a: 'integer' });
add('ADJ', 'rational|a rational number', { a: 'rational' });
add('ADJ', 'irrational|an irrational number', { a: 'irrational' });
add('ADJ', 'a perfect square|a square', { a: 'square' });
add('ORDER', 'of order');
add('FIRST', 'the first|first');
PHRASES.sort((a, b) => b[0].length - a[0].length);

const NUMWORDS = { zero: 0, one: 1, two: 2, three: 3, four: 4, five: 5, six: 6, seven: 7, eight: 8, nine: 9, ten: 10, eleven: 11, twelve: 12,
  thirteen: 13, fourteen: 14, fifteen: 15, sixteen: 16, seventeen: 17, eighteen: 18, nineteen: 19, twenty: 20, thirty: 30, forty: 40,
  fifty: 50, sixty: 60, seventy: 70, eighty: 80, ninety: 90, hundred: 100, thousand: 1000, million: 1000000 };
const FRACWORDS = { 'one half': '1/2', 'a half': '1/2', 'one third': '1/3', 'a third': '1/3', 'one quarter': '1/4', 'a quarter': '1/4', 'one fourth': '1/4' };
const GREEK = { epsilon: 'ε', eps: 'ε', delta: 'δ', alpha: 'α', beta: 'β', gamma: 'γ', theta: 'θ', lambda: 'λ', mu: 'μ', sigma: 'σ', phi: 'φ', omega: 'ω' };
// Words that start a phrase after the article "a" (so "a real number" isn't the variable a).
const AFTER_ARTICLE = new Set(['real', 'natural', 'positive', 'nonnegative', 'non-negative', 'whole', 'integer', 'number', 'function', 'sequence',
  'set', 'subset', 'group', 'prime', 'point', 'continuous', 'bounded', 'convergent', 'differentiable', 'convex', 'half', 'third', 'quarter',
  'multiple', 'perfect', 'square', 'rational', 'irrational', 'cauchy', 'uniformly', 'strictly', 'monotone', 'monotonically', 'increasing',
  'decreasing', 'open', 'closed', 'compact', 'cyclic', 'abelian', 'even', 'odd', 'whole', 'finite', 'nonzero']);

/* ---------- tokens ---------- */
function tokenize(text) {
  const raw = [];
  const re = /(\d+(?:\.\d+)?)|([A-Za-zα-ωΑ-Ω][A-Za-zα-ωΑ-Ω'_-]*\d*)|(<=|>=|!=|->|<->|=>|[≤≥≠∈→⇒]|[+\-*/^()[\]{},:;|=<>!])/g;
  let m;
  while ((m = re.exec(text))) {
    if (m[1]) raw.push({ t: 'num', v: m[1] });
    else if (m[2]) raw.push({ t: 'w', v: m[2] });
    else raw.push({ t: 'sym', v: { '≤': '<=', '≥': '>=', '≠': '!=', '∈': 'in', '→': '->', '⇒': '->' }[m[3]] || m[3] });
  }
  // Number words and fractions; then phrases, longest first.
  const out = [];
  for (let i = 0; i < raw.length;) {
    const w = j => (raw[i + j] && raw[i + j].t === 'w' ? raw[i + j].v.toLowerCase() : null);
    if (w(0) && w(1) && FRACWORDS[w(0) + ' ' + w(1)]) { out.push({ t: 'num', v: FRACWORDS[w(0) + ' ' + w(1)] }); i += 2; continue; }
    if (w(0) && NUMWORDS[w(0)] !== undefined && !(w(0) === 'one' && w(1) === 'over')) {
      let n = NUMWORDS[w(0)], j = 1;
      while (w(j) && NUMWORDS[w(j)] !== undefined) { const x = NUMWORDS[w(j)]; n = x >= 100 ? n * x : n + x; j++; }
      out.push({ t: 'num', v: String(n) }); i += j; continue;
    }
    if (raw[i].t === 'w') {
      let hit = null;
      for (const [ws, tok] of PHRASES) {
        if (ws.every((x, j) => w(j) === x)) { hit = [ws.length, tok]; break; }
      }
      // The article "a": a real number, a function … but the variable a otherwise.
      if (w(0) === 'a' && raw[i].v === 'a' && (!hit || hit[0] === 1)) {
        if (w(1) && AFTER_ARTICLE.has(w(1))) { i++; continue; }
        out.push({ t: 'var', v: 'a' }); i++; continue;
      }
      if (hit) { out.push({ ...hit[1], t: 'kw', text: raw.slice(i, i + hit[0]).map(x => x.v).join(' ') }); i += hit[0]; continue; }
      const lw = raw[i].v.toLowerCase();
      if (GREEK[lw]) { out.push({ t: 'var', v: GREEK[lw] }); i++; continue; }
      if (lw === 'pi') { out.push({ t: 'var', v: 'pi' }); i++; continue; }
      // Single letters (and x1, a_n, f') are variables; longer words are names or unknown words.
      if (/^[A-Za-zα-ω]('|\d|_\w+)*$/.test(raw[i].v)) out.push({ t: 'var', v: raw[i].v.replace(/_/g, '') });
      else out.push({ t: 'w', v: raw[i].v });
      i++; continue;
    }
    out.push(raw[i]); i++;
  }
  return out;
}

/* ---------- parsing ---------- */
const FN_LETTERS = new Set(['f', 'g', 'h', 'F', 'G', 'H']);
class Parser {
  constructor(toks, known) { this.pending = []; this.t = toks; this.i = 0; this.notes = []; this.unknown = []; this.imports = new Set(); this.kinds = new Map(); this.known = known; this.bound = new Set(); this.used = new Map(); }
  peek(k = 0) { return this.t[this.i + k] || { t: 'end' }; }
  next() { return this.t[this.i++] || { t: 'end' }; }
  is(k, j = 0) { const x = this.peek(j); return x.t === 'kw' && x.k === k; }
  sym(v, j = 0) { const x = this.peek(j); return x.t === 'sym' && x.v === v; }
  eat(k) { if (this.is(k)) return this.next(); return null; }
  eatSym(v) { if (this.sym(v)) return this.next(); return null; }
  skipArt() { while (this.is('ART')) this.next(); }
  atEnd() { return this.peek().t === 'end'; }
  // Words nobody understood are skipped, and reported.
  skipUnknown() { while (this.peek().t === 'w') this.unknown.push(this.next().v); }

  /* propositions */
  prop() {
    const left = this.implication();
    if (this.eat('IFF')) return `(${left}) <-> (${this.prop()})`;
    return left;
  }
  implication() {
    if (this.eat('IF')) {
      const a = this.disj();
      this.eatSym(',');
      this.eat('THEN');
      return `${wrapP(a)} -> ${wrapP(this.prop())}`;
    }
    let a = this.disj();
    if (this.eat('IMPLIES')) return `${wrapP(a)} -> ${wrapP(this.prop())}`;
    if (this.eat('WHENEVER') || this.eat('IF')) { const b = this.disj(); return `${wrapP(b)} -> ${wrapP(a)}`; }
    return a;
  }
  disj() { let s = this.conj(); while (this.eat('OR')) s = `${s} or ${this.conj()}`; return s; }
  conj() {
    let s = this.neg();
    while (this.is('AND') && !this.quantStart(1)) { this.next(); s = `${s} and ${this.neg()}`; }
    return s;
  }
  quantStart(j = 0) { return this.is('FORALL', j) || this.is('EXISTS', j); }
  neg() {
    if (this.eat('NOT')) return `not ${wrapP(this.neg())}`;
    this.skipArt();
    if (this.is('FORALL') || this.is('EXISTS')) return this.quantified();
    if (this.is('EVERY') || this.is('NO') || this.is('SOME')) { const r = this.nounClaim(); if (r) return r; }
    // "The function x squared is continuous at 0": a function given by a formula.
    if (this.is('NOUN') && this.peek().n === 'fn' && !this.is('IS', 1)) {
      this.next();
      const saveUsed = new Map(this.used);
      const e = this.sum();
      const x = [...this.used.keys()].find(k => !saveUsed.has(k)) || 'x';
      this.used = saveUsed;
      const v = `(${x} => ${e})`;
      this.kinds.set(v, 'fn');
      let iv = null;
      this.eat('IS');
      const pred = this.predicate(v, 'fn', () => iv, () => null, i => { iv = i; });
      if (/⟨I⟩/.test(pred) && !iv) this.notes.push('No interval given; using [0, 1].');
      return pred.replace(/⟨I⟩/g, iv ? ivArgs(iv) : '0, 1');
    }
    const before = this.pending.length;
    let c = this.clause();
    const ps = this.pending.splice(before);
    for (const pb of ps.reverse()) c = `forall ${pb.vars.join(', ')} in ${pb.dom}: ${pb.cond ? `${pb.cond} -> ${wrapP(c)}` : c}`;
    // "… for every x": a quantifier at the end applies to the whole clause.
    while (this.quantStart()) {
      const q = this.next(), b = this.binder();
      c = q.k === 'FORALL' ? `forall ${b.text}: ${b.cond ? `${b.cond} -> ` : ''}${wrapP(c)}` : `exists ${b.text}: ${b.cond ? `${b.cond} and ` : ''}${wrapP(c)}`;
    }
    return c;
  }
  quantified() {
    const q = this.next();
    const b = this.binder();
    this.eatSym(',') || this.eatSym(':') || this.eat('ST') || (q.k === 'EXISTS' && this.eat('THAT'));
    this.eat('ST');
    const body = this.prop();
    if (q.k === 'FORALL') return `forall ${b.text}: ${b.cond ? `${b.cond} -> ${wrapP(body)}` : body}`;
    return `exists ${b.text}: ${b.cond ? `${b.cond} and ${wrapP(body)}` : body}`;
  }
  // "real numbers x and y in [0, 1]", "positive integer n", "x > 0", "x between 0 and 1"
  binder() {
    this.skipArt();
    let type = null;
    if (this.is('TYPE')) type = this.next().ty;
    const vars = [];
    const one = () => { const x = this.peek(); if (x.t === 'var') { this.next(); vars.push(x.v); return true; } return false; };
    if (!one()) { this.notes.push('Expected a variable name after the quantifier; using x.'); vars.push('x'); }
    const listGoesOn = j => { const x = this.peek(j); return x.t === 'end' || (x.t === 'sym' && (x.v === ',' || x.v === ':')) || (x.t === 'kw' && ['AND', 'IN', 'BETWEEN', 'FROM', 'ST'].includes(x.k)); };
    while ((this.sym(',', 0) || this.is('AND')) && this.peek(1).t === 'var' && !vars.includes(this.peek(1).v) && listGoesOn(2)) { this.next(); one(); }
    for (const v of vars) this.bound.add(v);
    // An explicit range.
    let dom = null, cond = null;
    if (this.eat('IN')) dom = this.set();
    else if (this.eat('BETWEEN')) { const a = this.sum(); this.eat('AND'); dom = `[${a}, ${this.sum()}]`; }
    else if (this.eat('FROM')) { const a = this.sum(); this.eat('TO'); dom = `[${a}, ${this.sum()}]`; }
    else if (this.is('CMP') && this.peek().op !== '=' && this.peek().op !== '!=') {
      const op = this.next().op, c = this.sum();
      if (type === 'N' || type === 'Z' || type === 'posZ') { dom = typeDom(type); cond = vars.map(v => `${v} ${op} ${c}`).join(' and '); }
      else return { text: `${vars.join(', ')} ${op} ${c}`, cond: null, vars };
    } else if (this.peek().t === 'sym' && ['<', '>', '<=', '>='].includes(this.peek().v)) {
      const op = this.next().v, c = this.sum();
      if (type === 'N' || type === 'Z' || type === 'posZ') { dom = typeDom(type); cond = vars.map(v => `${v} ${op} ${c}`).join(' and '); }
      else return { text: `${vars.join(', ')} ${op} ${c}`, cond: null, vars };
    }
    if (!dom) {
      if (type === 'posR') return { text: `${vars.join(', ')} > 0`, vars };
      if (type === 'nonnegR') return { text: `${vars.join(', ')} >= 0`, vars };
      dom = typeDom(type || guessType(vars));
      if (!type && guessType(vars) === 'R') this.notes.push(`${vars.join(', ')} taken to range over ℝ.`);
    }
    if (type === 'posZ') cond = [cond, ...vars.map(v => `${v} >= 1`)].filter(Boolean).join(' and ');
    for (const v of vars) { this.bound.add(v); this.kinds.set(v, type === 'R2' ? 'point' : 'num'); }
    return { text: `${vars.join(', ')} in ${dom}`, cond, vars };
  }
  cmpAfter(j) { const x = this.peek(j); return (x.t === 'kw' && (x.k === 'CMP' || x.k === 'IS')) || (x.t === 'sym' && ['=', '<', '>', '<=', '>=', '!='].includes(x.v)); }
  set() {
    this.skipArt();
    if (this.is('SET')) return this.next().s;
    if (this.is('INTERVAL')) {
      const open = this.next().open;
      if (this.eat('FROM')) { const a = this.sum(); this.eat('TO'); const b = this.sum(); return open ? `(${a}, ${b})` : `[${a}, ${b}]`; }
    }
    if (this.is('TYPE')) return typeDom(this.next().ty);
    // Notation as written: [a, b], (a, b], R, N, a..b, a named set.
    if (this.sym('[') || this.sym('(')) {
      const o = this.next().v, a = this.sum();
      this.eatSym(',');
      const b = this.sum();
      const c = this.sym(']') || this.sym(')') ? this.next().v : ']';
      return `${o}${a}, ${b}${c}`;
    }
    const s = this.sum();
    if (this.eatSym('.') && this.eatSym('.')) return `${s}..${this.sum()}`;
    return s;
  }

  /* "every continuous function on [0, 1] is bounded", "no prime greater than 2 is even" */
  nounClaim() {
    const save = this.i, q = this.next().k;
    const adjs = [];
    while (this.is('ADJ')) { adjs.push(this.next().a); this.eat('AND'); }
    let noun = null;
    if (this.is('NOUN')) noun = this.next().n;
    else if (adjs.length && adjs[adjs.length - 1] === 'prime') { adjs.pop(); noun = 'prime'; }
    else if (this.is('TYPE')) { const t = this.next().ty; noun = { N: 'nat', Z: 'int', R: 'real', posZ: 'posint', posR: 'posreal', nonnegR: 'nonnegreal', R2: 'point' }[t]; }
    if (!noun) { this.i = save; return null; }
    const v = { fn: 'f', seq: 's', set: 'S', set2: 'S', group: 'g', prime: 'p', nat: 'n', int: 'n', posint: 'n', real: 'x', posreal: 'x', nonnegreal: 'x', point: 'p' }[noun];
    const kind = { fn: 'fn', seq: 'seq', set: 'set', set2: 'set', group: 'group' }[noun] || 'num';
    this.kinds.set(v, kind);
    this.bound.add(v);
    const conds = [];
    let interval = null, point = null;
    // Qualifiers: on [a, b], of order n, greater than c, in S, that are P.
    for (let guard = 0; guard < 6; guard++) {
      if (this.eat('ON')) { interval = this.set(); continue; }
      if (this.eat('AT')) { point = this.sum(); continue; }
      if (this.eat('ORDER')) { conds.push(`|${v}.G| = ${this.sum()}`); continue; }
      if (this.is('CMP') && !this.is('IS')) { const op = this.next().op; conds.push(`${v} ${op} ${this.sum()}`); continue; }
      if (this.is('THAT') && (this.is('IS', 1) || this.is('HAS', 1))) { this.next(); this.next(); conds.push(this.predicate(v, kind, () => interval, () => point)); continue; }
      break;
    }
    const domain = this.catalog(noun);
    const pre = [...adjs.map(a => this.adj(a, v, kind, interval, point)), ...conds];
    if (noun === 'prime') pre.unshift(`isprime(${v})`), this.imports.add('numtheory');
    if (noun === 'posint') pre.unshift(`${v} >= 1`);
    this.eat('IS') || this.eat('HAS');
    // The interval may come after the verb: "every continuous function is bounded on [0, 1]".
    const pred = this.predicate(v, kind, () => interval, () => point, iv => { interval = iv; });
    if (!interval && (kind === 'fn') && /_on\(/.test(pred + pre.join())) this.notes.push('No interval given for the functions; using [0, 1].');
    const fix = s => s.replace(/⟨I⟩/g, interval ? ivArgs(interval) : '0, 1');
    const P = pre.map(fix), Q = fix(pred);
    const binder = noun === 'posreal' ? `${v} > 0` : noun === 'nonnegreal' ? `${v} >= 0` : `${v} in ${domain}`;
    if (q === 'EVERY') return `forall ${binder}: ${P.length ? `${P.join(' and ')} -> ${wrapP(Q)}` : Q}`;
    if (q === 'NO') return `forall ${binder}: ${P.length ? `${P.join(' and ')} -> not ${wrapP(Q)}` : `not ${wrapP(Q)}`}`;
    return `exists ${binder}: ${[...P, wrapP(Q)].join(' and ')}`;
  }
  catalog(noun) {
    switch (noun) {
      case 'fn': return 'Functions(R)';
      case 'seq': return 'Sequences(R)';
      case 'set': return 'Subsets(R)';
      case 'set2': return 'Subsets(R^2)';
      case 'group': this.imports.add('models'); return 'AllGroups(12)';
      case 'prime': return '2..1000';
      case 'nat': case 'posint': return 'N';
      case 'int': return 'Z';
      case 'point': return 'R^2';
      default: return 'R';
    }
  }
  // What follows "is": properties (and/or), not, comparisons, between, divisible by, in.
  predicate(v, kind, getI, getP, setI) {
    const neg = !!this.eat('NOT');
    let s;
    if (this.is('ADJ')) {
      const parts = [];
      let joiner = ' and ';
      do {
        const a = this.next().a;
        // "continuous on [0, 1]", "differentiable at 0"
        if (this.eat('ON') && setI) setI(this.set());
        let pt = null;
        if (this.eat('AT')) pt = this.sum();
        parts.push(this.adj(a, v, kind, getI(), pt || getP()));
        if (this.is('OR')) joiner = ' or ';
      } while ((this.eat('AND') || this.eat('OR')) && (this.is('ADJ') || (this.eat('NOT') && this.is('ADJ'))));
      if (this.eat('ON') && setI) setI(this.set());
      s = parts.length > 1 ? `(${parts.join(joiner)})` : parts[0];
    } else if (this.eat('BETWEEN')) { const a = this.sum(); this.eat('AND'); s = `${a} <= ${v} <= ${this.sum()}`; }
    else if (this.eat('DIVBY')) s = `${v} mod ${wrap(this.sum(), 2)} = 0`;
    else if (this.eat('IN')) s = `${v} in ${this.set()}`;
    else if (this.is('CMP')) { const op = this.next().op; s = `${v} ${op} ${this.sum()}`; }
    else { this.skipUnknown(); s = `${v} = ${this.sum()}`; }
    return neg ? `not ${wrapP(s)}` : s;
  }
  // A property of v; ⟨I⟩ stands for the interval's ends until they are known.
  adj(a, v, kind, interval, point) {
    const I = interval ? ivArgs(interval) : '⟨I⟩';
    const need = lib => this.imports.add(lib);
    if (kind === 'fn') {
      if (point && (a === 'cont' || a === 'diff')) { need('functions'); return `${a === 'cont' ? 'continuous_at' : 'differentiable_at'}(${v}, ${point})`; }
      const m = { cont: 'continuous_on', ucont: 'uniformly_continuous_on', bounded: 'bounded_on', inc: 'increasing_on', convex: 'convex_on' }[a];
      if (m) { need('functions'); return `${m}(${v}, ${I})`; }
      if (a === 'diff') { need('functions'); return `(forall t in ${interval || '[0, 1]'}: differentiable_at(${v}, t))`; }
      if (a === 'dec') { need('functions'); return `increasing_on(x => -${v}(x), ${I})`; }
    }
    if (kind === 'seq') {
      const m = { conv: 'convergent', bounded: 'bounded_seq', cauchy: 'cauchy', inc: 'increasing_seq', dec: 'decreasing_seq' }[a];
      if (m) { if (m !== 'convergent') need('sequences'); return `${m}(${v})`; }
    }
    if (kind === 'set') {
      const m = { open: 'open', closed: 'closed', bounded: 'bounded' }[a];
      if (m) { need('topology'); return `${m}(${v})`; }
      if (a === 'compact') { need('topology'); return `(closed(${v}) and bounded(${v}))`; }
      if (a === 'convex') return `convex_set(${v})`;
    }
    if (kind === 'group') {
      if (a === 'abelian') return `(forall a, b in ${v}.G: ${v}.op(a, b) = ${v}.op(b, a))`;
      if (a === 'cyclic') { need('models'); return `cyclic_group(${v})`; }
    }
    switch (a) {
      case 'even': this.use(v, 'Z'); return `${wrap(v, 2)} mod 2 = 0`;
      case 'odd': this.use(v, 'Z'); return `${wrap(v, 2)} mod 2 = 1`;
      case 'prime': this.use(v, 'N'); need('numtheory'); return `isprime(${v})`;
      case 'pos': return `${v} > 0`;
      case 'neg': return `${v} < 0`;
      case 'nonneg': return `${v} >= 0`;
      case 'nonzero': return `${v} != 0`;
      case 'integer': return `${v} in Z`;
      case 'rational': return `is_rational(${v})`;
      case 'irrational': return `not is_rational(${v})`;
      case 'square': this.use(v, 'N'); return `floor(sqrt(${v}))^2 = ${v}`;
      default:
        this.notes.push(`"${a}" isn't a property I know for this kind of object.`);
        return 'true';
    }
  }

  /* clauses: comparisons and "x is …" */
  clause() {
    const left = this.sum();
    const parts = [left];
    let anyOp = false;
    for (;;) {
      if (this.is('CMP')) { parts.push(this.next().op, this.sum()); anyOp = true; continue; }
      if (this.peek().t === 'sym' && ['=', '<', '>', '<=', '>=', '!='].includes(this.peek().v)) { parts.push(this.next().v, this.sum()); anyOp = true; continue; }
      if (this.is('DIVIDES')) { this.next(); const b = this.sum(); this.markZ(left); return `${wrap(b, 2)} mod ${wrap(left, 2)} = 0`; }
      if (this.is('IS') || this.is('HAS')) {
        this.next();
        if (this.is('CMP')) { parts.push(this.next().op, this.sum()); anyOp = true; continue; }
        const kind = this.kinds.get(left) || (FN_LETTERS.has(left) ? 'fn' : /^[A-Z]$/.test(left) && left !== 'N' ? 'set' : 'num');
        return this.predicate(left, kind, () => null, () => null);
      }
      if (this.is('IN') && !anyOp) { this.next(); return `${left} in ${this.set()}`; }
      if (this.is('TENDS') && !anyOp) { this.next(); const L = this.is('INF') ? (this.next(), 'inf') : this.sum(); return `converges_to(${left}, ${L})`; }
      break;
    }
    return parts.join(' ');
  }
  markZ(v) { this.use(v, 'Z'); }
  use(v, dom) { if (/^[A-Za-zα-ω]'*\d*$/u.test(v) && !this.known.has(v)) this.used.set(v, dom || this.used.get(v) || null); }

  /* arithmetic in words: strings with a precedence (1 sum, 2 product, 3 sign, 4 power, 5 atom) */
  sum() { return this.sumE().s; }
  sumE() {
    let a = this.prodE();
    for (;;) {
      const op = this.binop(['+', '-']);
      if (!op) return a;
      const b = this.prodE();
      a = { s: `${a.s} ${op} ${wrap(b, op === '-' ? 2 : 1)}`, p: 1 };
    }
  }
  binop(ops) {
    if (this.is('OP') && ops.includes(this.peek().op)) return this.next().op;
    if (this.peek().t === 'sym' && ops.includes(this.peek().v)) return this.next().v;
    return null;
  }
  prodE(fnStops = false) {
    let a = this.powE();
    const FN = ['ABS', 'UN', 'BIN', 'SQ', 'FN2', 'LIM', 'TWICE', 'HALF', 'RECIP', 'SUMFROM'];
    for (;;) {
      if (fnStops && ((this.is('OP') && ['*', '/'].includes(this.peek().op)) || this.sym('*') || this.sym('/')) && this.peek(1).t === 'kw' && FN.includes(this.peek(1).k)) return a;
      const op = this.binop(['*', '/']);
      if (!op) {
        // A number next to a variable or bracket multiplies: 2x, 3(x + 1).
        if (this.sym('(') && a.p >= 4) { const b = this.powE(); a = { s: `${wrap(a, 2)}*${wrap(b, 3)}`, p: 2 }; continue; }
        if (a.p >= 4 && /^[\d.]+$/.test(a.s) && (this.peek().t === 'var' || this.sym('('))) { const b = this.powE(); a = { s: `${a.s}${b.p >= 5 ? '' : '*'}${b.p >= 5 ? b.s : wrap(b, 3)}`, p: 2 }; continue; }
        return a;
      }
      const b = this.powE();
      a = { s: `${wrap(a, 2)}${op === '*' ? '*' : '/'}${wrap(b, 3)}`, p: 2 };
    }
  }
  // One term: a power, with a number or bracket in front multiplying it (3y, 2(x + 1)).
  termE() {
    let a = this.powE();
    while ((/^[\d.]+$/.test(a.s) && this.peek().t === 'var') || this.sym('(')) { const b = this.powE(); a = { s: `${wrap(a, 2)}*${wrap(b, 3)}`, p: 2 }; }
    return a;
  }
  powE() {
    let a = this.unaryE();
    for (;;) {
      if (this.is('POST')) { a = { s: `${wrap(a, 5)}${this.next().s}`, p: 4 }; continue; }
      const op = this.binop(['^']);
      if (op) { const b = this.unaryE(); a = { s: `${wrap(a, 5)}^${wrap(b, 5)}`, p: 4 }; continue; }
      if (this.sym('!')) { this.next(); a = { s: `${wrap(a, 5)}!`, p: 4 }; continue; }
      return a;
    }
  }
  unaryE() {
    this.skipArt();
    if (this.binop(['-'])) { const a = this.unaryE(); return { s: `-${wrap(a, 3)}`, p: 3 }; }
    if (this.is('UN')) {
      const tok = this.next();
      this.skipArt();
      const a = tok.f === 'sqrt' || tok.f === 'cbrt' ? this.prodE(true) : this.powE();
      return tok.pow ? { s: `${tok.f}(${a.s})^${tok.pow}`, p: 4 } : { s: `${tok.f}(${a.s})`, p: 5 };
    }
    if (this.eat('ABS')) { const a = this.prodE(true); return { s: `|${a.s}|`, p: 5 }; }
    if (this.is('SQ')) { const s = this.next().s; const a = this.unaryE(); return { s: `${wrap(a, 5)}${s}`, p: 4 }; }
    if (this.eat('TWICE')) { const a = this.powE(); return { s: `2${a.p >= 5 && /^[A-Za-zα-ω]/.test(a.s) ? '' : '*'}${wrap(a, 3)}`, p: 2 }; }
    if (this.eat('HALF')) { this.eat('OF'); const a = this.powE(); return { s: `${wrap(a, 2)}/2`, p: 2 }; }
    if (this.eat('RECIP')) { const a = this.powE(); return { s: `1/${wrap(a, 3)}`, p: 2 }; }
    if (this.is('BIN')) {
      const tok = this.next();
      if (this.peek().t === 'num' && this.peek().v === '2' && (this.is('ADJ', 1) || this.is('TYPE', 1))) {
        const save = this.i;
        this.next();
        const vs = this.nounValue(2);
        if (vs) return { s: `(${vs[0]} ${tok.op} ${vs[1]})`, p: 5 };
        this.i = save;
      }
      if (tok.sum && this.eat('FIRST')) {
        const n = this.peek().t === 'var' || this.peek().t === 'num' ? this.next().v : 'n';
        const adjs = [];
        while (this.is('ADJ')) adjs.push(this.next().a);
        this.eat('TYPE') || this.eat('NOUN');
        const term = adjs.includes('odd') ? '(2k - 1)' : adjs.includes('even') ? '2k' : adjs.includes('square') ? 'k^2' : 'k';
        if (/^[A-Za-z]$/.test(n)) this.use(n, 'N');
        this.bound.add('k');
        return { s: `(sum k in 1..${n}: ${term})`, p: 5 };
      }
      const a = this.sumE();
      // "the sum of k for k from 1 to n"
      if (tok.sum && this.is('FOR') && this.peek(1).t === 'var') {
        this.next();
        const k = this.next().v;
        this.bound.add(k);
        let range;
        if (this.eat('FROM')) { const lo = this.sum(); this.eat('TO'); range = `${lo}..${this.sum()}`; }
        else if (this.eatSym('=')) { const lo = this.sum(); this.eat('TO'); range = `${lo}..${this.sum()}`; }
        else if (this.eat('IN')) range = this.set();
        else range = '1..n';
        return { s: `(sum ${k} in ${range}: ${a.s})`, p: 5 };
      }
      this.eat('AND');
      const b = this.termE();
      return { s: `(${wrap(a, tok.op === '+' ? 1 : tok.op === '*' ? 2 : 2)} ${tok.op} ${wrap(b, tok.op === '-' || tok.op === '/' ? 3 : 2)})`, p: 5 };
    }
    if (this.is('FN2')) { const f = this.next().f; const a = this.sum(); this.eat('AND'); this.eatSym(','); return { s: `${f}(${a}, ${this.sum()})`, p: 5 }; }
    // "the sum from k = 1 to n of k^2"
    if (this.eat('SUMFROM')) {
      const k = this.peek().t === 'var' ? this.next().v : 'k';
      this.bound.add(k);
      this.eatSym('=') || this.eat('FROM');
      const lo = this.sum(); this.eat('TO'); const hi = this.sum();
      this.eat('OF');
      const body = this.sumE();
      return { s: `(sum ${k} in ${lo}..${hi}: ${body.s})`, p: 5 };
    }
    // "the limit of 1/n as n goes to infinity"
    if (this.eat('LIM')) {
      const body = this.sumE();
      this.eat('AS');
      const n = this.peek().t === 'var' ? this.next().v : 'n';
      this.bound.add(n);
      this.eat('TENDS');
      const to = this.is('INF') ? (this.next(), 'inf') : this.sum();
      return { s: `(lim ${n} -> ${to}: ${body.s})`, p: 5 };
    }
    return this.primary();
  }
  // "any real number", "every odd number", "two odd integers": fresh variables, quantified over
  // the whole clause, with the adjectives as a hypothesis.
  nounValue(count) {
    const save = this.i;
    const adjs = [];
    while (this.is('ADJ')) adjs.push(this.next().a);
    if (!this.is('TYPE')) { this.i = save; return null; }
    const ty = this.next().ty;
    const intish = ty === 'N' || ty === 'Z' || ty === 'posZ' || adjs.some(a => ['even', 'odd', 'prime', 'square'].includes(a));
    const pool = intish ? ['m', 'n', 'k', 'j'] : ['x', 'y', 'z', 'w'];
    const vars = [];
    for (const v of pool) if (vars.length < count && !this.bound.has(v) && !this.used.has(v)) vars.push(v);
    vars.forEach(v => { this.bound.add(v); this.kinds.set(v, 'num'); });
    const dom = intish && ty !== 'N' && ty !== 'posZ' ? 'Z' : typeDom(ty === 'posR' || ty === 'nonnegR' ? 'R' : ty);
    const conds = [];
    for (const v of vars) {
      for (const a of adjs) conds.push(this.adj(a, v, 'num', null, null));
      if (ty === 'posR' || ty === 'posZ') conds.push(`${v} > 0`);
      if (ty === 'nonnegR') conds.push(`${v} >= 0`);
    }
    this.pending.push({ vars, dom, cond: conds.join(' and ') });
    return vars;
  }
  primary() {
    const x = this.peek();
    if (this.is('EVERY') || (this.is('SOME') && false)) {
      const save = this.i;
      this.next();
      const vs = this.nounValue(1);
      if (vs) return { s: vs[0], p: 5 };
      this.i = save;
    }
    if (x.t === 'num') { this.next(); return { s: x.v, p: /\//.test(x.v) ? 2 : 5 }; }
    if (this.is('INF')) { this.next(); return { s: 'inf', p: 5 }; }
    if (this.is('SET')) { return { s: this.next().s, p: 5 }; }
    if (x.t === 'var' || (x.t === 'w' && (this.known.has(x.v) || this.known.has(x.v.toLowerCase())))) {
      this.next();
      const name = x.t === 'w' && !this.known.has(x.v) ? x.v.toLowerCase() : x.v;
      if (!this.bound.has(name) && x.t === 'var') this.use(name);
      // f(x) is a call; n(n + 1) multiplies, unless n is a function.
      if (this.sym('(')) {
        const isFn = FN_LETTERS.has(name) || x.t === 'w' || this.kinds.get(name) === 'fn';
        this.next();
        const args = [this.sum()];
        while (this.eatSym(',')) args.push(this.sum());
        this.eatSym(')');
        if (isFn) return { s: `${name}(${args.join(', ')})`, p: 5 };
        return { s: `${name}*(${args.join(', ')})`, p: 2 };
      }
      if (this.is('OF') && FN_LETTERS.has(name)) { this.next(); const a = this.powE(); return { s: `${name}(${a.s})`, p: 5 }; }
      return { s: name, p: 5 };
    }
    if (this.eatSym('(')) {
      const a = this.sum();
      if (this.eatSym(',')) { const b = this.sum(); this.eatSym(')'); return { s: `(${a}, ${b})`, p: 5 }; }
      this.eatSym(')');
      return { s: `(${a})`, p: 5 };
    }
    if (this.eatSym('|')) { const a = this.sum(); this.eatSym('|'); return { s: `|${a}|`, p: 5 }; }
    if (this.sym('[')) return { s: this.set(), p: 5 };
    if (x.t === 'w') { this.unknown.push(this.next().v); return this.atEnd() ? { s: '0', p: 5 } : this.primary(); }
    if (x.t === 'end') { this.notes.push('The sentence ended where a value was expected.'); return { s: '0', p: 5 }; }
    this.next();
    this.notes.push(`Skipped "${x.text || x.v}".`);
    return this.primary();
  }
}
const wrap = (e, p) => (typeof e === 'string' ? (/^[\w.αβγδεθλμσφωπ]+$/u.test(e) || /^[\w.]+\(.*\)$/u.test(e) || (/^\(/.test(e) && closes(e) === e.length - 1) ? e : `(${e})`) : e.p < p ? `(${e.s})` : e.s);
// A proposition needs brackets next to -> unless it's a single comparison or call.
const wrapP = s => {
  // Already one bracketed whole: leave it.
  if (/^\(/.test(s) && closes(s) === s.length - 1) return s;
  let t = s;
  while (/\([^()]*\)/.test(t)) t = t.replace(/\([^()]*\)/g, '');
  return /^(forall|exists|not) /.test(s) || / (and|or|->|<->) /.test(t) ? `(${s})` : s;
};
// Where the bracket opening s closes.
const closes = s => { let d = 0; for (let i = 0; i < s.length; i++) { if (s[i] === '(') d++; else if (s[i] === ')' && --d === 0) return i; } return -1; };
const ivArgs = iv => { const m = /^[[(]\s*(.+?)\s*,\s*(.+?)\s*[\])]$/.exec(iv); return m ? `${m[1]}, ${m[2]}` : '0, 1'; };
const typeDom = t => ({ N: 'N', Z: 'Z', posZ: 'N', R: 'R', R2: 'R^2', posR: 'R', nonnegR: 'R' }[t] || 'R');
const guessType = vars => (vars.every(v => /^[ijklmn]$/.test(v)) ? 'N' : 'R');

/* ---------- statements ---------- */
function translateLine(line, known) {
  let text = line.trim().replace(/[.?!]+$/, '').replace(/\s+/g, ' ');
  if (!text) return null;
  // Already notation? Leave it.
  if (/^(check|theorem|lemma|claim|conjecture|def|let|plot|show|explain|import|proof|structure|vary)\b/.test(text) && /[:=(]/.test(text)) return { output: text, notes: ['Already in notation.'], unknown: [], imports: [] };
  // define f(x) to be …, let f(x) = …
  let m = /^(?:define|let)\s+([A-Za-z]\w*)\s*\(([^)]*)\)\s*(?:to be|be|=|:=|equal to|equals?|as)\s+(.+)$/i.exec(text);
  if (m) {
    const p = new Parser(tokenize(m[3]), known);
    m[2].split(',').map(s => s.trim()).filter(Boolean).forEach(v => p.bound.add(v));
    const body = p.prop();
    return finish(p, `def ${m[1]}(${m[2].split(',').map(s => s.trim()).join(', ')}) := ${body}`);
  }
  m = /^(?:let|set|put)\s+([A-Za-z]\w*)\s*(?:be|=|:=|equal to|equals?|be equal to)\s+(.+)$/i.exec(text);
  if (m) { const p = new Parser(tokenize(m[2]), known); return finish(p, `let ${m[1]} = ${p.sum()}`); }
  // plot … for x from a to b
  m = /^(?:plot|graph|draw|sketch)\s+(?:the graph of\s+)?(.+?)\s+(?:for|with|as)\s+([A-Za-z])\s+(?:goes\s+|going\s+|runs\s+|runs\s+)?(?:from|between|in)\s+(.+)$/i.exec(text)
    || /^(?:plot|graph|draw|sketch)\s+(?:the graph of\s+)?(.+?)\s+(?:from|between|on)\s+()(.+)$/i.exec(text);
  if (m) {
    const p = new Parser(tokenize(m[1]), known);
    const e = p.sum();
    const x = m[2] || ([...p.used.keys()][0] || 'x');
    const q = new Parser(tokenize(/^\s*[[(]/.test(m[3]) ? m[3] : m[3].replace(/\s+(?:to|and)\s+/, ', ').replace(/^/, '[') + ']'), known);
    return finish(p, `plot ${e} for ${x} in ${q.set()}`, q);
  }
  // what is …, compute …
  m = /^(?:what is|what's|compute|calculate|evaluate|find|work out|simplify)\s+(.+)$/i.exec(text);
  if (m) { const p = new Parser(tokenize(m[1]), known); const e = p.sum(); return finish(p, e, null, true); }
  // A claim (with or without "prove that").
  const toks = tokenize(text);
  const p = new Parser(toks, known);
  p.eat('CHECK');
  const body = p.prop();
  return finish(p, body, null, false, true);
}

function finish(p, out, q = null, isExpr = false, isClaim = false) {
  if (!p.atEnd()) {
    const rest = p.t.slice(p.i).map(x => x.text || x.v).join(' ');
    p.notes.push(`Didn't use the end of the sentence: "${rest}".`);
  }
  const notes = [...p.notes, ...(q ? q.notes : [])];
  const unknown = [...p.unknown, ...(q ? q.unknown : [])];
  if (isClaim) {
    // Free one-letter variables become "for all", over the integers if parity or primes were
    // mentioned, otherwise over ℝ.
    const free = [...p.used.keys()].filter(v => !p.bound.has(v) && !['e', 'pi'].includes(v) && !p.known.has(v));
    if (free.length) {
      const byDom = new Map();
      for (const v of free) { const d = p.used.get(v) || (/^[ijklmn]$/.test(v) ? 'N' : 'R'); if (!byDom.has(d)) byDom.set(d, []); byDom.get(d).push(v); }
      const binders = [...byDom].map(([d, vs]) => `${vs.join(', ')} in ${d}`).join(', ');
      out = `forall ${binders}: ${out}`;
      notes.push(`${free.join(', ')} ${free.length > 1 ? 'were' : 'was'} not introduced, so the claim is made for every ${free.join(', ')} (in ${[...byDom.keys()].map(d => ({ R: 'ℝ', N: 'ℕ', Z: 'ℤ' }[d] || d)).join(', ')}).`);
    }
    out = `check ${out}`;
  }
  const imports = [...p.imports];
  const doubtful = unknown.length > 0 || notes.some(n => /^(Skipped|Didn't use|The sentence ended|Expected a variable|"[^"]+" isn't a property)/.test(n));
  return { output: out, notes, unknown: [...new Set(unknown)], imports, sure: !doubtful };
}

// Translate text (one statement per line). env: the names defined so far, so they are
// recognized (functions, sets) rather than reported as unknown words.
function wordsToNotation(text, env = null) {
  const known = new Set();
  const names = env || MV.freshEnv();
  for (const k in names) if (/^[A-Za-z_]\w*$/.test(k)) known.add(k);
  const lines = [];
  const imports = new Set();
  for (const line of String(text).split(/\n+/)) {
    const r = translateLine(line, known);
    if (!r) continue;
    r.imports.forEach(i => imports.add(i));
    // Checked by the real parser before it is offered.
    try { MV.parseStatement(MV.splitStatements(r.output)[0]); r.ok = true; }
    catch (e) { r.ok = false; r.error = e.message; }
    lines.push({ input: line.trim(), ...r });
  }
  const importLines = [...imports].filter(lib => !(env && env[lib])).map(lib => `import ${lib}`);
  return { lines, imports: importLines, text: [...importLines, ...lines.map(l => l.output)].join('\n'), ok: lines.length > 0 && lines.every(l => l.ok) };
}

Object.assign(MV, { wordsToNotation, wordsTokenize: tokenize });
})(typeof window !== 'undefined' ? window : globalThis);
