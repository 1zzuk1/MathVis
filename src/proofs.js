/* Theorem Sketchpad — checking proof sketches. Each step is checked numerically in its context
   (the variables taken so far, the assumptions, the values chosen), and the goal is tracked:
   let peels a ∀, assume peels a hypothesis, choose answers an ∃, a split into cases checks that
   the cases cover everything and that each reaches the goal, induction turns ∀n into a base case
   and a step, contradiction assumes the goal fails and aims for false, and "by lemma" matches a
   step to a lemma's conclusion and checks the lemma's hypothesis. This is not a proof checker; it
   finds the step that goes wrong, with a counterexample.

   checkProofSteps is a generator: it yields each claim to check and receives the analysis back,
   so the app can run it in slices and the tests can run it straight through. */
'use strict';
(function (global) {
const MV = global.MV;
const { MVError, ppText } = MV;

const bin = (op, a, b) => ({ type: 'bin', op, a, b });
const not = a => ({ type: 'un', op: 'not', a });
const FALSE = { type: 'bool', v: false };
const norm = n => ppText(n).replace(/\s+/g, '');
const sameFormula = (a, b) => norm(a) === norm(b);
const id = name => ({ type: 'id', name });

// (n ↦ 1/n)(k) becomes 1/k, so unfolded goals read naturally.
function beta(n) {
  if (!n || typeof n !== 'object') return n;
  if (Array.isArray(n)) return n.map(beta);
  if (n.type === 'call' && n.f.type === 'lambda' && n.f.params.length === n.args.length) {
    return beta(MV.subst(n.f.body, new Map(n.f.params.map((p, i) => [p, n.args[i]]))));
  }
  const out = {};
  for (const [k, v] of Object.entries(n)) out[k] = v && typeof v === 'object' ? beta(v) : v;
  return out;
}

// Unfold a goal that is a call to a definition (or the name of a lemma) one level.
function unfold(goal, env) {
  if (goal.type === 'call' && goal.f.type === 'id') {
    const d = MV.DEFS.get(env[goal.f.name]);
    if (d && d.params.length === goal.args.length) return beta(MV.subst(d.body, new Map(d.params.map((p, i) => [p, goal.args[i]]))));
  }
  if (goal.type === 'id' && env[goal.name] && env[goal.name].__claim) return env[goal.name].body;
  return null;
}
// The goal in the shape a step needs (a ∀, an ⇒ or an ∃), unfolding definitions until it is.
function shaped(goal, env, test) {
  for (let g = goal, k = 0; g && k < 4; g = unfold(g, env), k++) if (test(g)) return g;
  return null;
}
const restOf = (g, binders) => binders.length ? { ...g, binders } : g.body;
const renameIn = (node, from, to) => from === to ? node : MV.subst(node, new Map([[from, id(to)]]));
const membership = (elem, dom) => dom.type === 'bound'
  ? { type: 'cmp', ops: [dom.op], args: [elem, dom.c] }
  : { type: 'in', neg: false, elem, dom };

/* The claim that checks formula F in a context: ∀ (variables) : (assumptions) ⇒ F, with chosen
   values substituted. Assumptions like |x − c| < r narrow x's range so samples aren't wasted. */
function contextClaim(ctx, F) {
  const defs = new Map(), binders = [], hyps = [];
  const sub = n => MV.subst(n, defs);
  const subDom = d => d.type === 'bound' ? { ...d, c: sub(d.c) } : sub(d);
  for (const e of ctx) {
    if (e.kind === 'var') binders.push({ ...e.binder, dom: subDom(e.binder.dom) });
    else if (e.kind === 'hyp') hyps.push(sub(e.expr));
    else if (e.kind === 'def') defs.set(e.name, sub(e.expr));
  }
  const names = binders.map(b => b.name);
  const extra = [];
  for (const hy of hyps) {
    if (hy.type !== 'cmp' || hy.args.length !== 2 || !['<', '<='].includes(hy.ops[0])) continue;
    const [l, r] = hy.args;
    if (l.type !== 'abs' || l.e.type !== 'bin' || l.e.op !== '-' || l.e.a.type !== 'id') continue;
    const i = names.indexOf(l.e.a.name);
    if (i < 0) continue;
    const later = new Set(names.slice(i));
    if ([...MV.freeNames(l.e.b).keys(), ...MV.freeNames(r).keys()].some(n => later.has(n))) continue;
    const b = binders[i];
    // Keep the original range as an assumption.
    if (!(b.dom.type === 'id' && b.dom.name === 'R')) extra.push(membership(id(b.name), b.dom));
    const open = hy.ops[0] === '<';
    binders[i] = { ...b, dom: { type: 'interval', lo: bin('-', l.e.b, r), hi: bin('+', l.e.b, r), loOpen: open, hiOpen: open } };
  }
  const all = [...extra, ...hyps];
  let body = F;
  if (all.length) body = bin('->', all.reduce((a, c) => bin('and', a, c)), F);
  return binders.length ? { type: 'quant', q: 'forall', binders, body: sub(body) } : sub(body);
}

/* ---------- citing a lemma: match the step to its conclusion ---------- */

const SKIP = new Set(['pos', 'implicit', 'endPos']);
function unify(p, t, vars, sub) {
  if (p && p.type === 'id' && vars.has(p.name)) {
    if (sub.has(p.name)) return norm(sub.get(p.name)) === norm(t);
    sub.set(p.name, t);
    return true;
  }
  if (Array.isArray(p)) return Array.isArray(t) && p.length === t.length && p.every((x, i) => unify(x, t[i], vars, sub));
  if (!p || typeof p !== 'object') return p === t;
  if (!t || typeof t !== 'object' || p.type !== t.type) return false;
  for (const k of new Set([...Object.keys(p), ...Object.keys(t)])) if (!SKIP.has(k) && !unify(p[k], t[k], vars, sub)) return false;
  return true;
}
const conjuncts = n => n.type === 'bin' && n.op === 'and' ? [...conjuncts(n.a), ...conjuncts(n.b)] : [n];

// lemma: ∀ vars: hyp ⇒ concl. Finds values of the variables that make concl (or one of its
// conjuncts) read as P. Returns what the lemma then needs: each value in its range, and hyp.
function lemmaInstance(lem, P) {
  let body = lem.body;
  const vars = [];
  while (body.type === 'quant' && body.q === 'forall') { vars.push(...body.binders); body = body.body; }
  if (vars.some(b => b.pattern)) return null;
  const names = new Set(vars.map(b => b.name));
  const hasHyp = body.type === 'bin' && body.op === '->';
  const concl = hasHyp ? body.b : body, hyp = hasHyp ? body.a : null;
  for (const c of [concl, ...(conjuncts(concl).length > 1 ? conjuncts(concl) : [])]) {
    const sub = new Map();
    if (!unify(c, P, names, sub)) continue;
    const bound = vars.filter(b => sub.has(b.name)), free = vars.filter(b => !sub.has(b.name));
    const subDom = d => d.type === 'bound' ? { ...d, c: MV.subst(d.c, sub) } : MV.subst(d, sub);
    const needs = bound.map(b => membership(sub.get(b.name), subDom(b.dom)));
    if (hyp) {
      const h = MV.subst(hyp, sub);
      // Variables the conclusion doesn't mention: the hypothesis must hold for some value of them.
      needs.push(free.length ? { type: 'quant', q: 'exists', binders: free.map(b => ({ ...b, dom: subDom(b.dom) })), body: h } : h);
    }
    return { sub, bound, needs };
  }
  return null;
}

/* ---------- induction ---------- */

// The goal ∀n ∈ D: P(n) over whole numbers from lo on: the base P(lo) and the step
// ∀n ∈ D': P(n) ⇒ P(n + 1), where D' leaves out the last value of a range lo..hi.
function inductionGoals(g, name) {
  const gb = g.binders[0];
  if (gb.pattern || gb.name !== name) {
    const vars = g.binders.map(b => b.pattern ? '(' + b.pattern.join(', ') + ')' : b.name).join(', ');
    throw new MVError(`Induction works on the goal's first variable, here ${vars.split(', ')[0]}${g.binders.some(b => b.name === name) ? `: take the variables before ${name} with "let" first` : `; the goal has no variable ${name}`}.`);
  }
  const d = gb.dom;
  let lo, stepDom;
  if (d.type === 'id' && d.name === 'N') { lo = { type: 'num', v: 0 }; stepDom = d; }
  else if (d.type === 'range') { lo = d.lo; stepDom = { ...d, hi: bin('-', d.hi, { type: 'num', v: 1 }) }; }
  else throw new MVError(`Induction needs ${name} to range over whole numbers from a first one: write the goal with ${name} in N or ${name} in 1..m (it has ${name} ∈ ${MV.ppDom(d, false)}).`);
  const P = restOf(g, g.binders.slice(1));
  const at = v => MV.subst(P, new Map([[name, v]]));
  return {
    lo, P,
    base: at(lo),
    step: { type: 'quant', q: 'forall', binders: [{ name, pattern: null, dom: stepDom }], body: bin('->', P, at(bin('+', id(name), { type: 'num', v: 1 }))) },
  };
}

/* ---------- the checker ---------- */

const statusOf = (info, contra) => {
  const c = info.count;
  if (c.fail) return 'fail';
  if (!c.ok && c.vac) return contra ? 'vacuous' : 'vac';
  if (c.undef && !c.ok) return 'undef';
  return 'ok';
};

// target: the claim being proved (or null). Yields claims; returns { rows, closed, goal }.
function* checkProofSteps(ast, env, target) {
  const rows = [];
  const check = function* (ctx, F) {
    const claim = contextClaim(ctx, F);
    return { claim, info: yield claim };
  };
  const inContra = ctx => ctx.some(e => e.contra);

  function* block(steps, ctx, goal, depth) {
    let closed = false;
    for (const s of steps) {
      const row = { step: s, notes: [], depth };
      rows.push(row);
      if (closed) row.notes.push('The goal was already reached.');
      try {
        if (s.kind === 'let') {
          for (const b of s.binders) {
            const g = goal && shaped(goal, env, x => x.type === 'quant' && x.q === 'forall');
            let dom = b.dom;
            if (g) {
              const gb = g.binders[0];
              if (gb.pattern) throw new MVError(`The goal takes a point (${gb.pattern.join(', ')}); take it with one name for now.`);
              if (!dom) dom = gb.dom;
              else if (norm(dom) !== norm(gb.dom)) row.notes.push(`The goal has ${gb.name} ∈ ${MV.ppDom(gb.dom, false)}; the steps are checked for ${b.name} ∈ ${MV.ppDom(dom, false)}.`);
              const rest = g.binders.slice(1).map(x => ({ ...x, dom: x.dom.type === 'bound' ? { ...x.dom, c: renameIn(x.dom.c, gb.name, b.name) } : renameIn(x.dom, gb.name, b.name) }));
              goal = renameIn(restOf(g, rest), gb.name, b.name);
            } else if (goal) row.notes.push(`The goal isn't a "for all" here, so ${b.name} is just a new variable.`);
            if (!dom) throw new MVError(`Give ${b.name} a range, as in "let ${b.name} in [0, 1]" or "let ${b.name} > 0".`);
            ctx.push({ kind: 'var', binder: { name: b.name, pattern: null, dom, pos: b.pos } });
          }
          row.status = 'struct';
        } else if (s.kind === 'assume') {
          const g = goal && shaped(goal, env, x => x.type === 'bin' && x.op === '->');
          if (g) {
            if (!sameFormula(s.expr, g.a)) {
              // Assuming something else is fine if the goal's hypothesis implies it.
              Object.assign(row, yield* check(ctx, bin('->', g.a, s.expr)));
              row.notes.push(row.info.count.fail ? `This isn't the goal's hypothesis ${ppText(g.a)}, and doesn't follow from it.` : `The goal's hypothesis is ${ppText(g.a)}; it implies this (on the samples).`);
              ctx.push({ kind: 'hyp', expr: g.a });
            }
            goal = g.b;
          } else row.notes.push(goal ? 'The goal has no hypothesis here, so this narrows the cases being checked.' : 'Narrows the cases checked from here on.');
          ctx.push({ kind: 'hyp', expr: s.expr });
          row.status = row.info ? (row.info.count.fail ? 'fail' : 'ok') : 'struct';
        } else if (s.kind === 'choose' && s.expr) {
          const g = goal && shaped(goal, env, x => x.type === 'quant' && x.q === 'exists');
          if (g) {
            const gb = g.binders[0];
            const inDom = membership(s.expr, gb.dom);
            const iq = MV.inequalityStep(ctx, inDom, env);
            if (iq && iq.proved) { row.claim = contextClaim(ctx, inDom); row.exact = iq; }
            else Object.assign(row, yield* check(ctx, inDom));
            row.notes.push(`Is it allowed? Checks ${ppText(inDom)}.`);
            goal = renameIn(restOf(g, g.binders.slice(1)), gb.name, s.name);
          } else if (goal) row.notes.push('The goal isn\'t an "exists" here, so this just names a value.');
          ctx.push({ kind: 'def', name: s.name, expr: s.expr });
          row.status = row.exact ? 'proved' : row.info ? (row.info.count.fail || row.info.count.undef ? 'fail' : 'ok') : 'struct';
          if (row.exact) row.notes.push(row.exact.note);
        } else if (s.kind === 'choose') {
          // choose x in D such that P: something with P exists (checked); from now on x is any such value.
          const ex = { type: 'quant', q: 'exists', binders: [{ name: s.name, pattern: null, dom: s.dom, pos: s.namePos }], body: s.cond };
          Object.assign(row, yield* check(ctx, ex));
          row.notes.push(`Checks that such a ${s.name} exists; afterwards ${s.name} is any of them.`);
          ctx.push({ kind: 'var', binder: { name: s.name, pattern: null, dom: s.dom, pos: s.namePos } });
          ctx.push({ kind: 'hyp', expr: s.cond });
          row.status = row.info.count.fail ? 'fail' : 'ok';
        } else if (s.kind === 'contradiction') {
          if (!goal) throw new MVError('There is no goal here to prove by contradiction.');
          // Where the goal holds, the supposition is false and every later step holds vacuously.
          Object.assign(row, yield* check(ctx, goal));
          row.notes.push(`Suppose ${ppText(goal)} fails; the goal is now a contradiction: "so false".`);
          row.notes.push(row.info.count.fail
            ? 'The goal itself fails on some samples, so the steps below are tested there.'
            : 'The goal holds on every sample, so the supposition never does: the steps below hold vacuously, as they should when the theorem is true.');
          ctx.push({ kind: 'hyp', expr: not(goal), contra: true });
          goal = FALSE;
          row.status = 'struct';
        } else if (s.kind === 'cases') {
          // Do the cases cover everything? (otherwise: covers what the others don't.)
          const conds = s.cases.filter(c => c.cond).map(c => c.cond);
          const hasOtherwise = s.cases.some(c => !c.cond);
          if (!hasOtherwise) {
            Object.assign(row, yield* check(ctx, conds.reduce((a, c) => bin('or', a, c))));
            row.status = statusOf(row.info, inContra(ctx)) === 'fail' ? 'fail' : 'ok';
            row.notes.push(row.status === 'fail' ? 'These cases don\'t cover everything: the counterexample is in none of them.' : 'The cases cover everything (on the samples).');
          } else { row.status = 'struct'; row.notes.push('"otherwise" covers whatever the other cases leave.'); }
          let every = true;
          const before = [];
          for (const c of s.cases) {
            const cond = c.cond || (before.length ? not(before.reduce((a, x) => bin('or', a, x))) : { type: 'bool', v: true });
            if (c.cond) before.push(c.cond);
            const head = { step: { kind: 'case', word: c.cond ? 'case' : 'otherwise', expr: c.cond, pos: c.pos }, notes: [], depth: depth + 1, goalAfter: goal };
            rows.push(head);
            const sub = yield* block(c.steps, [...ctx, { kind: 'hyp', expr: cond }], goal, depth + 2);
            head.status = !goal ? 'struct' : sub.closed ? 'ok' : 'open';
            if (goal) head.notes.push(sub.closed ? 'This case reaches the goal.' : 'This case doesn\'t reach the goal yet.');
            every = every && sub.closed;
          }
          if (goal && every && row.status !== 'fail') { closed = true; goal = null; row.notes.push('Every case reaches the goal.'); }
        } else if (s.kind === 'induction') {
          const g = goal && shaped(goal, env, x => x.type === 'quant' && x.q === 'forall');
          if (!g) throw new MVError(goal ? `Induction proves a "for all n"; the goal here is ${ppText(goal)}.` : 'Induction needs a goal "for all n …" to prove.');
          const I = inductionGoals(g, s.name);
          row.notes.push(`Base: ${ppText(I.base)}.`, `Step: ${ppText(I.step)}.`);
          row.status = 'struct';
          let both = true;
          for (const which of ['base', 'step']) {
            const sg = I[which];
            const head = { step: { kind: which, word: which, pos: s[which + 'Pos'] }, notes: [], depth: depth + 1, goalAfter: sg };
            rows.push(head);
            if (s[which]) {
              const sub = yield* block(s[which], [...ctx], sg, depth + 2);
              head.status = sub.closed ? 'ok' : 'open';
              head.notes.push(sub.closed ? `The ${which} is shown.` : `The ${which} isn't reached yet.`);
              both = both && sub.closed;
            } else {
              Object.assign(head, yield* check(ctx, sg));
              head.status = statusOf(head.info, inContra(ctx));
              head.notes.push(`No ${which}: block, so it is checked directly on the samples.`);
              both = both && head.status === 'ok';
            }
          }
          if (both) { closed = true; goal = null; }
        } else {
          // have / so: exact algebra when the step is an identity (given the assumptions), otherwise
          // check the formula in this context, or the hypotheses of a cited lemma.
          const lemmaName = s.by && (/^([\p{L}_][\p{L}\p{N}_']*)/u.exec(s.by) || [])[1];
          const lem = lemmaName && env[lemmaName] && env[lemmaName].__claim ? env[lemmaName] : null;
          let alg = !lem ? MV.symbolicStep(ctx, s.expr, env) : null;
          // Inequalities, |…|, min and max, from the ranges and the assumptions so far.
          if (!lem && !(alg && alg.proved)) { const iq = MV.inequalityStep(ctx, s.expr, env); if (iq && iq.proved) alg = iq; }
          const inst = lem && lemmaInstance(lem, s.expr);
          if (alg && alg.proved) {
            row.status = 'proved';
            row.notes.push(alg.note || (alg.usedAssumptions ? 'Exact: it follows by algebra from the assumptions above.' : 'Exact: both sides simplify to the same expression.'));
            if (s.by) row.notes.push(`The reason given: ${s.by}.`);
          } else if (inst) {
            const with_ = inst.bound.map(b => `${b.name} = ${ppText(inst.sub.get(b.name))}`).join(', ');
            if (inst.needs.length) {
              Object.assign(row, yield* check(ctx, inst.needs.reduce((a, c) => bin('and', a, c))));
              row.status = statusOf(row.info, inContra(ctx));
              row.notes.push(row.status === 'fail'
                ? `${lem.name}${with_ ? ` with ${with_}` : ''} doesn't apply: it needs ${inst.needs.map(ppText).join(' and ')}, which fails here.`
                : `By ${lem.name}${with_ ? ` with ${with_}` : ''}: it needs ${inst.needs.map(ppText).join(' and ')}, which holds here (on the samples).`);
            } else { row.status = 'ok'; row.notes.push(`By ${lem.name}${with_ ? ` with ${with_}` : ''}, which needs nothing more.`); }
            if (row.status !== 'fail') {
              // The lemma could be false; check the step too.
              const direct = yield* check(ctx, s.expr);
              if (direct.info.count.fail) { Object.assign(row, direct); row.status = 'fail'; row.notes.push(`Yet this fails here: is ${lem.name} true?`); }
              else if (!row.info) Object.assign(row, direct);
            }
          } else {
            Object.assign(row, yield* check(ctx, s.expr));
            row.status = statusOf(row.info, inContra(ctx));
            if (lem) row.notes.push(`Couldn't read this as ${lem.name}'s conclusion ${ppText(lemmaConclusion(lem))}; checked directly.`);
            else if (s.by) row.notes.push(`By ${s.by} (not checked).`);
          }
          if (s.kind === 'so' && goal && !closed) {
            const gs = [goal, unfold(goal, env)].filter(Boolean);
            if (row.status === 'fail') row.notes.push(gs.some(x => sameFormula(s.expr, x)) ? 'This is the goal, but it fails here.' : `The goal is still ${ppText(goal)}.`);
            else if (gs.some(x => sameFormula(s.expr, x))) { closed = true; row.notes.push(goal === FALSE ? 'A contradiction: the supposition was impossible.' : 'This is the goal.'); goal = null; }
            else {
              const imp = yield* check(ctx, bin('->', s.expr, goal));
              const vacuousOk = inContra(ctx) && !imp.info.count.fail;
              if (!imp.info.count.fail && (imp.info.count.ok || vacuousOk)) { closed = true; row.notes.push(`This gives the goal ${ppText(goal)} (checked on the samples).`); goal = null; }
              else row.notes.push(`The goal is still ${ppText(goal)}, and this doesn't give it${imp.info.count.fail ? '' : ' (no samples to tell)'}.`);
            }
          }
          ctx.push({ kind: 'hyp', expr: s.expr });
        }
      } catch (err) {
        if (err.message === 'Stopped.') throw err;
        row.status = 'error';
        row.error = err.message;
      }
      row.goalAfter = goal;
    }
    return { closed, goal };
  }

  const res = yield* block(ast.steps, [], target ? target.body : null, 0);
  return { rows, closed: res.closed, goal: res.goal };
}

function lemmaConclusion(lem) {
  let b = lem.body;
  while (b.type === 'quant' && b.q === 'forall') b = b.body;
  return b.type === 'bin' && b.op === '->' ? b.b : b;
}

// The claim a proof is about: the named lemma, or the theorem just before it.
function proofTarget(ast, env, lastClaim) {
  if (!ast.name) return lastClaim || null;
  const t = env[ast.name];
  if (!t || !t.__claim) throw new MVError(ast.name in env || t !== undefined ? `${ast.name} is not a theorem or lemma, so there's nothing to prove.` : `There's no theorem called ${ast.name}. Write it above the proof, as in theorem ${ast.name}: …`, ast.pos);
  return t;
}

// Straight through, for the tests.
function checkProof(ast, env, lastClaim, opts = { budget: 6000 }) {
  const target = proofTarget(ast, env, lastClaim);
  const g = checkProofSteps(ast, env, target);
  let r = g.next();
  while (!r.done) r = g.next(MV.analyzeClaim(r.value, env, opts));
  return { target, ...r.value };
}

Object.assign(MV, { checkProofSteps, checkProof, proofTarget, contextClaim, lemmaInstance, inductionGoals });
})(typeof window !== 'undefined' ? window : globalThis);
