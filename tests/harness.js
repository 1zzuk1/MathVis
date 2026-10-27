// Loads the engine and all libraries in Node, without the page: require('./harness').
'use strict';
const fs = require('fs'), path = require('path');
const root = path.join(__dirname, '..');

function load() {
  if (globalThis.MV && globalThis.MV.__loaded) return globalThis.MV;
  globalThis.window = undefined;
  const files = ['src/syntax.js', 'src/spaces.js', 'src/runtime.js'];
  for (const f of fs.readdirSync(path.join(root, 'src'))) {
    // Figures need a page; everything else runs in Node.
    if (!files.includes('src/' + f) && !f.startsWith('figure')) files.push('src/' + f);
  }
  const libs = fs.readFileSync(path.join(root, 'index.html'), 'utf8').match(/libs\/[\w]+\.js/g);
  for (const f of [...files, ...libs]) (0, eval)(fs.readFileSync(path.join(root, f), 'utf8'));
  const MV = globalThis.MV;
  for (const b of MV.BUILTIN) {
    const e = b.kind === 'js' ? MV.registerJS(b.fn, { builtin: true }) : MV.registerNotation(b.source, { builtin: true });
    if (e.error) throw new Error(`Library ${e.name} failed to load: ${e.error}`);
    MV.REG.set(e.name, e);
  }
  MV.rebuildIndex();
  MV.__loaded = true;
  return MV;
}

/* Run a notebook. Returns one record per statement:
   { line, text, type, kind?, info?, value?, error?, docLines }. Proof statements are parsed only
   (checking them needs the page). */
function runNotebook(src, opts = {}) {
  const MV = load();
  const stmts = MV.splitStatements(src);
  const parsed = stmts.map(s => { try { return { s, ast: MV.parseStatement(s) }; } catch (e) { return { s, err: e }; } });
  const pending = parsed.filter(p => p.ast && (['def', 'let', 'structure', 'concept'].includes(p.ast.type) || (p.ast.type === 'check' && p.ast.name))).flatMap(p => MV.definedNames(p.ast));
  const env = MV.freshEnv(pending);
  const out = [];
  let lastClaim = null;   // the theorem a following "proof:" proves
  for (const { s, ast, err } of parsed) {
    const rec = { line: s.line, text: s.text.split('\n')[0], docLines: s.docLines || [] };
    out.push(rec);
    if (err) { rec.error = err.message; continue; }
    rec.type = ast.type;
    rec.ast = ast;
    const t0 = Date.now();
    try {
      if (['import', 'library', 'let', 'def', 'structure', 'concept'].includes(ast.type)) {
        MV.execDefinition(ast, env, s);
        if (ast.type === 'concept') rec.concept = MV.conceptRows(MV.CONCEPTS.get(ast.name), null, env);
      } else if (ast.type === 'interpret') rec.interpret = interpretRecord(MV, ast, env);
      else if (ast.type === 'check') {
        rec.info = MV.analyzeClaim(ast.body, env, { stress: opts.stress || 0 });
        if (ast.name && env[ast.name] === undefined) env[ast.name] = MV.makeClaim(ast.name, ast.body, env, ast.kind, '');
        if (ast.name) lastClaim = env[ast.name];
      } else if (ast.type === 'eval') rec.value = MV.compile(ast.expr)(env);
      else if (ast.type === 'diagram') rec.diagram = MV.checkDiagram(ast, env);
      else if (ast.type === 'proof') rec.proof = MV.checkProof(ast, env, lastClaim);
      // explain, vary, plot and show need the page; parsing them is the test here.
    } catch (e) {
      rec.error = e.message + (e instanceof MV.MVError ? '' : '\n' + e.stack);
    }
    rec.ms = Date.now() - t0;
  }
  return { env, records: out };
}

// What "interpret" shows, without drawing it: the forms of a concept at the arguments, or the
// names of the representations and concepts that apply to a value.
function interpretRecord(MV, ast, env) {
  MV.checkNames(ast.expr, env);
  const e = ast.expr;
  const head = e.type === 'call' && e.f.type === 'id' ? env[e.f.name] : undefined;
  const C = MV.conceptOf(head) || (e.type === 'id' ? MV.CONCEPTS.get(e.name) : null);
  if (C && (e.type === 'call' || !C.params.length)) return { forms: MV.formsAt(C, e.type === 'call' ? e.args.map(a => MV.compile(a)(env)) : []) };
  const v = MV.compile(e)(env);
  return { value: v, representations: MV.representationsOf(v).map(r => r.name), concepts: MV.conceptsFor(v, env).map(m => ({ name: m.concept.name, v: m.v, error: m.error })) };
}

// The example and course notebooks, read from the app's source, and the test notebooks.
function notebooks() {
  const grab = (file, name) => {
    const src = fs.readFileSync(path.join(root, file), 'utf8');
    const a = src.indexOf(name), b = src.indexOf('\n];', a) + 3;
    return (0, eval)('(' + src.slice(src.indexOf('[', a), b - 1) + ')');
  };
  return [
    ...grab('app/main.js', 'const EXAMPLES = [').map(n => ({ ...n, group: 'example' })),
    ...grab('app/courses.js', 'APP.COURSES = [').map(n => ({ ...n, group: 'course' })),
    ...grab('tests/notebooks.js', 'const NOTEBOOKS = [').map(n => ({ ...n, group: 'test' })),
  ];
}

module.exports = { load, runNotebook, notebooks, root };
