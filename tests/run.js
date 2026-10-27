// The test suite: node tests/run.js [--quick] [filter]
//   1. every example, course and test notebook (tests/notebooks.js) runs without errors;
//   2. the expectation files in tests/cases: a comment "#! holds", "#! fails", "#! proved",
//      "#! never-tested", "#! homs" (diagrams), "#! open" and "#! fails at <step>" (proofs), "#! error", "#! value <text>" or "#! simplest <text>" above a statement
//      says what it must give (several may be combined, as "#! fails simplest 1/2");
//   3. every library lemma holds and every conjecture fails, at the usual stress level and with
//      the wild examples (a conjecture may hold on the usual examples if it fails on the wild ones);
//   4. every self-check a library registers (MathViz.selfCheck) passes.
'use strict';
const fs = require('fs'), path = require('path');
const { load, runNotebook, notebooks } = require('./harness');
const MV = load();

const args = process.argv.slice(2);
const quick = args.includes('--quick');
const filter = args.find(a => !a.startsWith('--')) || '';
let passed = 0, failed = 0;
const failures = [];
const t0 = Date.now();
const ok = (name, cond, detail = '') => {
  if (cond) passed++;
  else { failed++; failures.push(`${name}${detail ? '\n      ' + detail : ''}`); }
};
const section = title => { if (!quick) console.log('\n' + title); };
const matches = name => !filter || name.includes(filter);

/* 1. Notebooks */
section('Notebooks');
for (const nb of notebooks()) {
  const name = `${nb.group}: ${nb.name}`;
  if (!matches(name)) continue;
  const t = Date.now();
  const { records } = runNotebook(nb.src);
  const errs = records.filter(r => r.error);
  ok(name, !errs.length, errs.map(r => `line ${r.line}: ${r.error.split('\n')[0]}`).join('\n      '));
  if (!quick) console.log(`  ${errs.length ? 'FAIL' : 'ok  '} ${name} (${Date.now() - t} ms)`);
}

/* 2. Expectations */
section('Expectations');
const verdict = info => {
  const c = info.count;
  return { holds: !c.fail && !c.undef && c.ok > 0, fails: c.fail > 0, proved: !!info.proved, never: !c.ok && !c.fail && c.vac > 0 };
};
const casesDir = path.join(__dirname, 'cases');
for (const file of fs.readdirSync(casesDir).filter(f => f.endsWith('.mv')).sort()) {
  const src = fs.readFileSync(path.join(casesDir, file), 'utf8');
  const t = Date.now();
  const { records } = runNotebook(src);
  let n = 0, bad = 0;
  for (const r of records) {
    const ex = r.docLines.map(l => /^!\s*(.*)$/.exec(l)).filter(Boolean).map(m => m[1].trim()).join(' ');
    const name = `${file}:${r.line} ${r.text.trim().slice(0, 70)}`;
    if (!matches(name) && !matches(file)) continue;
    if (!ex) {
      if (r.error) { ok(name, false, 'unexpected error: ' + r.error.split('\n')[0]); bad++; }
      continue;
    }
    n++;
    const before = failed;
    if (/\berror\b/.test(ex)) ok(name, !!r.error, 'expected an error');
    else if (r.error) ok(name, false, 'unexpected error: ' + r.error.split('\n')[0]);
    else {
      // An expectation about a verdict needs something that produced one.
      if (/\b(holds|fails|proved|never-tested|open)\b/.test(ex) && !r.info && !r.diagram && !r.proof) ok(name, false, `nothing was checked here (a ${r.type || 'statement'})`);
      if (r.diagram) {
        const bad = r.diagram.checks.filter(c => !c.ok).map(c => c.text + ': ' + c.detail).concat(r.diagram.arrows.filter(a => !a.lands.ok).map(a => a.lands.detail));
        if (/\bholds\b/.test(ex)) ok(name, r.diagram.ok, 'expected the diagram to hold: ' + bad.join('; '));
        if (/\bfails\b/.test(ex)) ok(name, !r.diagram.ok, 'expected the diagram to fail');
        if (/\bhoms\b/.test(ex)) {
          const nh = r.diagram.arrows.filter(a => a.hom && !a.hom.ok);
          ok(name, !nh.length, 'expected homomorphisms: ' + nh.map(a => a.hom.detail).join('; '));
        }
      }
      if (r.proof) {
        // A proof holds when no step fails and the goal is reached; "open" when the steps hold
        // but the goal isn't reached; "fails at 3" names the first failing step.
        const steps = r.proof.rows.filter(x => !['case', 'base', 'step'].includes(x.step.kind));
        const badAt = steps.findIndex(x => x.status === 'fail' || x.status === 'error');
        const desc = steps.map((x, i) => `${i + 1}:${x.step.kind}=${x.status}${x.error ? '(' + x.error + ')' : ''}`).join(' ') + (r.proof.closed ? ' closed' : ' open');
        if (/\bholds\b/.test(ex)) ok(name, badAt < 0 && r.proof.closed, 'expected the proof to hold: ' + desc);
        if (/\bopen\b/.test(ex)) ok(name, badAt < 0 && !r.proof.closed, 'expected the steps to hold with the goal open: ' + desc);
        if (/(?<![-\w])proved\b/.test(ex)) ok(name, r.proof.closed && r.proof.rows.every(x => ['case', 'base', 'step'].includes(x.step.kind) || ['struct', 'proved'].includes(x.status)), 'expected every step exact: ' + desc);
        const fm = /\bfails(?:\s+at\s+(\d+))?/.exec(ex);
        if (fm) ok(name, badAt >= 0 && (!fm[1] || badAt + 1 === +fm[1]), `expected a failing step${fm[1] ? ' at ' + fm[1] : ''}: ` + desc);
      }
      if (r.info) {
        const v = verdict(r.info), c = JSON.stringify(r.info.count);
        if (/\bholds\b/.test(ex)) ok(name, v.holds, `expected to hold, got ${c}`);
        if (/\bfails\b/.test(ex)) ok(name, v.fails, `expected to fail, got ${c}`);
        if (/(?<![-\w])proved\b/.test(ex)) ok(name, v.proved, `expected "proved", got ${c}${v.proved ? '' : ' (not proved)'}`);
        if (/\bnot-proved\b/.test(ex)) ok(name, !v.proved, 'expected not to be labelled proved');
        if (/\bnever-tested\b/.test(ex)) ok(name, v.never, `expected every sample vacuous, got ${c}`);
        // Claims of a shape sampling answers wrongly: "caution extremum", or "no-caution".
        const kinds = MV.claimCautions(r.info.prepared).map(x => x.kind);
        const cm = /(?<![-\w])caution\s+(\w+)/.exec(ex);
        if (cm) ok(name, kinds.includes(cm[1]), `expected a caution of kind ${cm[1]}, got ${kinds.join(', ') || 'none'}`);
        if (/\bno-caution\b/.test(ex)) ok(name, !kinds.length, `expected no caution, got ${kinds.join(', ')}`);
        // Failures that may not be real: "fail-caution tiny", or "no-fail-caution".
        const fk = MV.failCautions(r.info).map(x => x.kind);
        const fm2 = /\bfail-caution\s+(\w+)/.exec(ex);
        if (fm2) ok(name, fk.includes(fm2[1]), `expected a failure caution of kind ${fm2[1]}, got ${fk.join(', ') || 'none'}`);
        if (/\bno-fail-caution\b/.test(ex)) ok(name, !fk.length, `expected no failure caution, got ${fk.join(', ')}`);
        const sm = /\bsimplest\s+(.+?)(?=\s+(?:holds|fails|proved|not-proved)\b|$)/.exec(ex);
        if (sm) {
          const got = r.info.simplest ? r.info.simplest.vals.map(MV.fmt).join(', ') : '(none)';
          ok(name, got === sm[1].trim(), `expected simplest counterexample ${sm[1].trim()}, got ${got}`);
        }
      }
      // Concepts and interpret: "agree" (every form agrees on every example), "disagree",
      // "represents name …" (interpret shows these views), "instance name …" (and is one of these).
      const forms = r.concept ? r.concept.rows : r.interpret && r.interpret.forms ? [r.interpret.forms] : null;
      const formDesc = () => forms ? forms.map(x => `${x.args.map(MV.fmt).join(',')}: ${x.results.map(y => y.error || MV.fmt(y.v)).join(' ')}`).join('; ') : '(no forms)';
      if (/\bagree\b/.test(ex)) ok(name, !!forms && forms.length > 0 && forms.every(x => x.agree === true), 'expected the forms to agree: ' + formDesc());
      if (/\bdisagree\b/.test(ex)) ok(name, !!forms && forms.some(x => x.agree === false), 'expected the forms to disagree: ' + formDesc());
      const rm = /\brepresents\s+([\w\s]+?)(?=\s+(?:instance|value)\b|$)/.exec(ex);
      if (rm) { const got = r.interpret && r.interpret.representations || []; ok(name, rm[1].trim().split(/\s+/).every(n => got.includes(n)), `expected views ${rm[1].trim()}, got ${got.join(', ') || 'none'}`); }
      const im = /\binstance\s+([\w\s]+?)(?=\s+(?:represents|value)\b|$)/.exec(ex);
      if (im) { const got = (r.interpret && r.interpret.concepts || []).filter(c => c.v === true).map(c => c.name); ok(name, im[1].trim().split(/\s+/).every(n => got.includes(n)), `expected an instance of ${im[1].trim()}, got ${got.join(', ') || 'none'}`); }
      const vm = /\bvalue\s+(.+)$/.exec(ex);
      if (vm) ok(name, 'value' in r && MV.fmt(r.value) === vm[1].trim(), `expected value ${vm[1].trim()}, got ${'value' in r ? MV.fmt(r.value) : '(no value)'}`);
    }
    if (failed > before) bad++;
  }
  if (!quick) console.log(`  ${bad ? 'FAIL' : 'ok  '} ${file}: ${n} expectations (${Date.now() - t} ms)`);
}

/* Failures only on examples a finite check misjudges (wild sequences) are flagged. */
section('Hard examples');
{
  const name = 'failure on a 1/log n sequence is flagged';
  if (matches(name) || matches('Hard examples')) {
    const { records } = runNotebook('import metric\ncheck forall s in Seq(R^2): convergent(s) -> converges_in(d_taxicab, s, lim(s))', { stress: 1 });
    const r = records.find(x => x.info);
    ok(name, r && r.info.count.fail > 0 && MV.failCautions(r.info).some(c => c.kind === 'hard'), r ? JSON.stringify(r.info.count) : 'no result');
  }
}

/* Finding library names by topic (src/topics.js): each query must find these among its first results. */
section('Topic search');
for (const [q, want, within] of [
  ['derivative', ['partial', 'grad', 'deriv'], 14], ['open set', ['open'], 3], ['compact', ['compact', 'cover'], 10],
  ['uniform continuity', ['uniformly_continuous_on'], 4], ['fixed point', ['fixed_points', 'fixed_point_iteration'], 6],
  ['eigenvalue', ['eigenvalues'], 3], ['norm', ['norm', 'opnorm'], 10], ['hessian', ['hessian', 'hessian_test'], 6],
]) {
  const name = `topic "${q}"`;
  if (!matches(name) && !matches('Topic search')) continue;
  const got = MV.findTopic(q, { limit: within }).map(e => e.name);
  ok(name, want.every(w => got.includes(w)), `expected ${want.join(', ')} among ${got.join(', ')}`);
}

/* 3. Library lemmas and conjectures */
section('Library lemmas');
const env = MV.freshEnv();
for (const name of MV.REG.keys()) MV.activate(name, env);
for (const name of MV.REG.keys()) {
  const lib = MV.REG.get(name);
  for (const lem of lib.lemmas || []) {
    const id = `${name}.${lem.name}`;
    if (!matches(id)) continue;
    const kind = env[lem.name].kind;
    const t = Date.now();
    // That the forms of a concept agree is checked on the usual examples: on the wild ones the
    // forms are sampled differently, and a sampled definition can miss what another one catches.
    const runs = (lem.tame ? [0] : [0, 1]).map(stress => {
      try { return MV.analyzeClaim({ type: 'id', name: lem.name }, env, { stress }); }
      catch (e) { return { error: e.message }; }
    });
    const err = runs.find(r => r.error);
    if (err) { ok(id, false, err.error); continue; }
    if (kind === 'conjecture') ok(id, runs.some(r => r.count.fail > 0), `conjecture never fails: ${runs.map(r => JSON.stringify(r.count)).join(' / ')}`);
    else runs.forEach((r, s) => ok(`${id} (stress ${s})`, !r.count.fail && !r.count.undef, `lemma fails: ${JSON.stringify(r.count)}${r.simplest ? ' at ' + r.simplest.vals.map(MV.fmt).join(', ') : ''}`));
    // A lemma's "holds" must not rest on a shape sampling can't decide.
    if (kind !== 'conjecture' && runs[0].prepared) {
      const kinds = MV.claimCautions(runs[0].prepared).map(x => x.kind);
      ok(`${id} has no caution`, !kinds.length, kinds.join(', '));
    }
    const ms = Date.now() - t;
    ok(`${id} runs in under 10 s`, ms < 10000, `${ms} ms`);
    if (!quick && ms > 3000) console.log(`  slow: ${id} ${ms} ms`);
  }
}
if (!quick) console.log(`  ${[...MV.REG.values()].reduce((s, l) => s + (l.lemmas || []).length, 0)} lemmas and conjectures checked`);

/* Libraries must not export the same name twice, or loading both silently hides one (the complex
   library's extensions of the elementary functions are deliberate). */
section('Name clashes');
{
  const allowed = new Set(['sin', 'cos', 'exp', 'ln', 'sqrt']);
  const owners = new Map();
  for (const [name, lib] of MV.REG) {
    const d = lib.def || {};
    const names = [...Object.keys(d.functions || {}), ...Object.keys(d.constants || {}), ...Object.keys(d.domains || {}), ...Object.keys(d.spaces || {}),
      ...(lib.names || []), ...(lib.lemmas || []).map(l => l.name), ...(lib.structures || [])];
    for (const n of new Set(names)) { if (!owners.has(n)) owners.set(n, []); owners.get(n).push(name); }
  }
  for (const [n, libs] of owners) if (libs.length > 1 && !allowed.has(n)) ok(`name ${n}`, false, `exported by ${libs.join(' and ')}`);
  passed++;
  if (!quick) console.log(`  ${owners.size} names checked`);
}

/* Plain words → notation: tests/words.txt lists sentences and the notation each must give, or
   REVIEW where the translator must say it didn't fully understand. */
section('Words');
{
  const lines = fs.readFileSync(path.join(__dirname, 'words.txt'), 'utf8').split('\n');
  let n = 0;
  for (let i = 0; i < lines.length; i++) {
    const s = lines[i];
    if (!s.trim() || s.startsWith('#') || s.trim().startsWith('=>')) continue;
    const want = (lines[i + 1] || '').trim().replace(/^=>\s*/, '');
    if (!matches('words') && !matches(s)) continue;
    const r = MV.wordsToNotation(s), l = r.lines[0] || {};
    const got = l.ok && l.sure ? r.text.split('\n').join(' ; ') : 'REVIEW';
    ok(`words: ${s.slice(0, 60)}`, got === want, `expected ${want}\n      got      ${got}${l.notes && l.notes.length ? '\n      notes: ' + l.notes.join(' | ') : ''}`);
    n++;
  }
  if (!quick) console.log(`  ${n} sentences translated`);
}

/* A claim split into slices (as the page's background workers do) and merged gives the same
   verdicts, simplest counterexample and proof as the whole claim checked at once. */
section('Split checks');
{
  const { env } = runNotebook('import functions, models, sequences, zoo');
  const claims = [
    'forall x, y in [-2, 2]: exp(x + y) >= 1 + x + y + 1/1000*sin(x*y)',
    'forall f in Functions(R): continuous_at(f, 0) -> differentiable_at(f, 0)',
    'forall x, y in R: (x + y)^2 = x^2 + 2x*y + y^2',
    'forall g in AllGroups(8): forall a, b in g.G: g.op(a, b) = g.op(b, a)',
    'forall s in Seq(R): bounded_seq(s) -> convergent(s)',
  ];
  const run = gen => { let r = gen.next(); while (!r.done) r = gen.next(); return r.value; };
  const sig = info => JSON.stringify({ c: info.count, p: info.proved, s: info.simplest ? info.simplest.vals.map(MV.fmt) : null });
  let n = 0;
  for (const text of claims) {
    if (!matches('split') && !matches(text)) continue;
    const body = MV.parseStatement(MV.splitStatements('check ' + text)[0]).body;
    const whole = run(MV.analyzeSteps(body, env, {}));
    const parts = [0, 1, 2].map(k => run(MV.analyzeSteps(body, env, { slice: { k, n: 3 }, search: false })));
    const given = { res: parts.flatMap(p => p.res).sort((a, b) => a.i - b.i).map(r => ({ i: r.i, s: r.s, L: r.L, R: r.R, m: r.m, tie: r.tie })), stopped: parts.some(p => p.stopped), inexact: parts.some(p => p.inexact) };
    const merged = run(MV.analyzeSteps(body, env, { given }));
    ok(`split: ${text.slice(0, 60)}`, sig(whole) === sig(merged), `whole ${sig(whole)} vs split ${sig(merged)}`);
    n++;
  }
  if (!quick) console.log(`  ${n} claims split and merged`);
}

/* Every formula in the notebooks and expectation files typesets as well-formed MathML, with no
   node left unhandled. */
section('Typesetting');
{
  const wellFormed = s => {
    const stack = [];
    for (const m of s.matchAll(/<(\/?)([a-z]+)[^>]*?(\/?)>/g)) {
      if (m[3]) continue;
      if (!m[1]) stack.push(m[2]);
      else if (stack.pop() !== m[2]) return false;
    }
    return !stack.length;
  };
  const sources = [...notebooks().map(nb => [`${nb.group}: ${nb.name}`, nb.src]),
    ...fs.readdirSync(casesDir).filter(f => f.endsWith('.mv')).map(f => [f, fs.readFileSync(path.join(casesDir, f), 'utf8')])];
  let count = 0;
  for (const [name, src] of sources) {
    if (!matches(name) && !matches('typeset')) continue;
    for (const s of MV.splitStatements(src)) {
      let ast;
      try { ast = MV.parseStatement(s); } catch (e) { continue; }
      for (const node of [ast.body, ast.expr, ...(ast.exprs || [])].filter(x => x && typeof x === 'object' && x.type)) {
        count++;
        let out;
        try { out = MV.ppMath(node); } catch (e) { ok(`typeset ${name}: ${MV.ppText(node).slice(0, 60)}`, false, e.message); continue; }
        ok(`typeset ${name}: ${MV.ppText(node).slice(0, 60)}`, wellFormed(out) && !out.includes('<mi>?</mi>'), out.slice(0, 300));
      }
    }
  }
  if (!quick) console.log(`  ${count} formulas typeset`);
}

/* 4. Library self-checks */
section('Self-checks');
for (const check of MV.SELF_CHECKS || []) {
  if (!matches(check.name)) continue;
  let res;
  try { res = check.run(env); } catch (e) { res = [{ name: check.name, ok: false, detail: e.message }]; }
  for (const r of res) ok(`${check.name}: ${r.name}`, r.ok, r.detail || '');
  if (!quick) console.log(`  ${res.every(r => r.ok) ? 'ok  ' : 'FAIL'} ${check.name}: ${res.length} checks`);
}

console.log(`\n${passed} passed, ${failed} failed (${((Date.now() - t0) / 1000).toFixed(1)} s)`);
if (failures.length) { console.log('\nFailures:'); for (const f of failures) console.log('  ✗ ' + f); }
process.exit(failed ? 1 : 0);
