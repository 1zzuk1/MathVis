/* Theorem Sketchpad UI — checking claims in background threads. A pool of workers (one per spare
   core, at most four) each loads the engine (src/ and libs/, no page code), rebuilds the
   notebook's definitions, runs the sampling and the search, and sends back plain data: the
   samples' values and verdicts, the counts, the simplest counterexample, any exact proof. The
   page rebuilds the rest cheaply (the environments behind "why?" only when one is clicked) and
   draws as before. Claims of a notebook run side by side, and the page stays responsive.

   Anything that can't cross over (a claim built around a function value, samples that are exact
   reals or sets), or a browser that won't start workers, is checked on the page as before. */
'use strict';
(function () {
const APP = window.APP;

/* ---------- the worker's program (stringified into the worker) ---------- */
function workerMain() {
  const MV = self.MV;
  const register = () => {
    MV.REG.clear();
    for (const b of MV.BUILTIN) {
      const e = b.kind === 'js' ? MV.registerJS(b.fn, { builtin: true }) : MV.registerNotation(b.source, { builtin: true });
      e.key = e.name;
      MV.REG.set(e.key, e);
    }
  };
  register();
  MV.rebuildIndex();
  const cancelled = new Set();
  // Environments for the notebook up to a point, keyed by the definitions' text; a longer list
  // continues from a cached shorter one.
  const envs = new Map();
  const BAD = {};
  function buildEnv(defs, names) {
    const key = i => names.join(',') + '\u0001' + defs.slice(0, i).map(d => d.text).join('\u0000');
    let start = 0, env = null;
    for (let i = defs.length; i >= 0; i--) { const e = envs.get(key(i)); if (e) { env = e; start = i; break; } }
    if (!env) env = MV.freshEnv(names);
    for (let i = start; i < defs.length; i++) {
      env = Object.create(env);
      const stmt = defs[i];
      try {
        const ast = MV.parseStatement(stmt);
        if (ast.type === 'check' && ast.name) env[ast.name] = MV.makeClaim(ast.name, ast.body, env, ast.kind, MV.docOf(stmt).doc);
        else MV.execDefinition(ast, env, stmt);
      } catch (e) { /* the page reports errors in definitions */ }
      envs.set(key(i + 1), env);
    }
    if (envs.size > 200) envs.clear();
    return env;
  }
  // Plain values only: numbers, booleans, strings and arrays of them.
  const ser = v => {
    if (v === null || v === undefined || typeof v === 'number' || typeof v === 'boolean' || typeof v === 'string') return v;
    if (Array.isArray(v)) { const a = v.map(ser); return a.includes(BAD) ? BAD : a; }
    return BAD;
  };
  const serR = (r, i = -1) => {
    if (!r) return null;
    // A sample from the claim's own list goes by its number (its values may be groups, sets, …);
    // one the search made up must be plain values.
    if (i >= 0) {
      const out = { i, s: r.s, L: ser(r.L), R: ser(r.R), m: typeof r.m === 'number' ? r.m : undefined, tie: r.tie, deeper: r.deeper, deeperTried: r.deeperTried, w: ser(r.w), inexact: r.inexact };
      if (out.L === BAD || out.R === BAD || out.w === BAD) throw BAD;
      return out;
    }
    const out = { vals: ser(r.vals), s: r.s, L: ser(r.L), R: ser(r.R), m: typeof r.m === 'number' ? r.m : undefined, tie: r.tie, deeper: r.deeper, deeperTried: r.deeperTried, w: ser(r.w), found: r.found, inexact: r.inexact };
    if (out.vals === BAD || out.L === BAD || out.R === BAD || out.w === BAD) throw BAD;
    return out;
  };
  function summarizeSlice(part) {
    try { return { slice: true, res: part.res.map(r => serR(r, r.i)), stopped: part.stopped, inexact: part.inexact, total: part.total }; }
    catch (e) { if (e === BAD) return null; throw e; }
  }
  function summarize(info) {
    try {
      const res = info.res.map((r, i) => serR(r, r.found ? -1 : (r.i ?? i)));
      const plain = JSON.parse(JSON.stringify({ count: info.count, proved: info.proved, algebra: info.algebra || null }));
      return {
        ...plain, res,
        exhaustive: info.exhaustive, stopped: info.stopped, total: info.total, stressable: info.stressable, restricted: info.restricted,
        factor: info.factor, stress: info.stress, wInteger: info.wInteger,
        simplestIndex: info.simplest ? info.res.indexOf(info.simplest) : -1, simplest: info.simplest && info.res.indexOf(info.simplest) < 0 ? serR(info.simplest) : null,
        nTuples: info.total,
        searched: info.searched ? { evals: info.searched.evals, found: info.searched.found, best: serR(info.searched.best) } : null,
      };
    } catch (e) { if (e === BAD) return null; throw e; }
  }
  self.onmessage = async ev => {
    const m = ev.data;
    if (m.type === 'libs') {
      register();
      for (const u of m.libs) {
        try {
          const e = u.kind === 'js' ? MV.registerJS(u.source, { builtin: false, id: u.id, source: u.source }) : MV.registerNotation(u.source, { builtin: false, id: u.id });
          e.key = MV.REG.has(e.name) ? `${e.name} · ${u.id}` : e.name;
          MV.REG.set(e.key, e);
        } catch (err) { /* the page reports library errors */ }
      }
      MV.rebuildIndex();
      envs.clear();
      return;
    }
    if (m.type === 'cancel') { cancelled.add(m.id); return; }
    if (m.type !== 'claim') return;
    try {
      const env = buildEnv(m.defs, m.names);
      const gen = MV.analyzeSteps(m.body, env, m.opts);
      let t = Date.now(), r;
      for (;;) {
        r = gen.next();
        if (r.done) break;
        if (Date.now() - t > 60) {
          self.postMessage({ type: 'progress', id: m.id, p: r.value });
          // Let a "stop" message in. A message channel, not setTimeout: timers are slowed to a
          // second in background tabs, messages aren't.
          await new Promise(res => { const ch = new MessageChannel(); ch.port1.onmessage = () => { ch.port1.close(); res(); }; ch.port2.postMessage(0); });
          if (cancelled.has(m.id)) { cancelled.delete(m.id); self.postMessage({ type: 'cancelled', id: m.id }); return; }
          t = Date.now();
        }
      }
      const summary = r.value && r.value.slice ? summarizeSlice(r.value) : summarize(r.value);
      self.postMessage(summary ? { type: 'result', id: m.id, summary } : { type: 'fallback', id: m.id });
    } catch (e) {
      self.postMessage({ type: 'error', id: m.id, message: e && e.message || String(e), pos: e && e.pos, mv: !!(e && e instanceof MV.MVError) });
    }
  };
  self.postMessage({ type: 'ready' });
}

/* ---------- the pool, on the page ---------- */
const pool = {
  workers: [], queue: [], jobs: new Map(), nextId: 1, state: 'off',   // off → starting → ready | broken
  size: Math.max(1, Math.min(4, (navigator.hardwareConcurrency || 2) - 1)),
  url: null,
};
APP.pool = pool;
pool.supported = () => typeof Worker === 'function' && typeof Blob === 'function' && pool.state !== 'broken';

// The engine's code, from the page's own script tags (src/…, libs/…; the build keeps the names).
async function engineSource() {
  const tags = [...document.querySelectorAll('script')].map(s => ({ s, name: s.getAttribute('data-src') || s.getAttribute('src') || '' }))
    .filter(x => /^(src|libs)\//.test(x.name) && !/^src\/figure/.test(x.name));
  const parts = [];
  for (const { s, name } of tags) {
    if (s.getAttribute('src')) { const r = await fetch(name); if (!r.ok) throw new Error('fetch ' + name); parts.push(await r.text()); }
    else parts.push(s.textContent);
  }
  return parts.join('\n;\n');
}
async function start() {
  if (pool.state !== 'off') return;
  pool.state = 'starting';
  try {
    const code = await engineSource();
    const blob = new Blob([`self.window = undefined;\n${code}\n;(${workerMain.toString()})();`], { type: 'text/javascript' });
    pool.url = URL.createObjectURL(blob);
    let ready = 0;
    const libs = APP.userLibs ? APP.userLibs() : [];
    await new Promise((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error('workers did not start')), 15000);
      for (let i = 0; i < pool.size; i++) {
        const w = new Worker(pool.url);
        w.busy = null;
        w.onmessage = ev => {
          const m = ev.data;
          if (m.type === 'ready') { if (libs.length) w.postMessage({ type: 'libs', libs }); if (++ready === pool.size) { clearTimeout(timer); resolve(); } return; }
          onMessage(w, m);
        };
        w.onerror = ev => { ev.preventDefault && ev.preventDefault(); if (pool.state === 'starting') { clearTimeout(timer); reject(new Error(ev.message || 'worker error')); } else crash(w); };
        pool.workers.push(w);
      }
    });
    pool.state = 'ready';
    pump();
  } catch (e) {
    // No workers here (a strict page policy, an old browser): everything runs on the page.
    pool.state = 'broken';
    for (const w of pool.workers) w.terminate();
    pool.workers = [];
    for (const job of pool.queue.splice(0)) job.resolve(null);
  }
}
function onMessage(w, m) {
  const job = pool.jobs.get(m.id);
  if (!job) return;
  if (m.type === 'progress') { if (job.ctl && job.ctl.onProgress) job.ctl.onProgress(m.p); return; }
  pool.jobs.delete(m.id);
  w.busy = null;
  if (m.type === 'result') job.resolve(m.summary);
  else if (m.type === 'fallback') job.resolve(null);
  else if (m.type === 'cancelled') job.reject(new MV.MVError('Stopped.'));
  else if (m.type === 'error') { const e = m.mv ? new MV.MVError(m.message, m.pos) : new Error(m.message); job.reject(e); }
  pump();
}
function crash(w) {
  // A worker died mid-job: its job runs on the page, and a fresh worker takes its place.
  if (w.busy) { const job = w.busy; pool.jobs.delete(job.id); job.resolve(null); }
  w.terminate();
  const i = pool.workers.indexOf(w);
  if (i >= 0) pool.workers.splice(i, 1);
}
function pump() {
  if (pool.state !== 'ready') return;
  for (const w of pool.workers) {
    if (w.busy) continue;
    // Jobs of a stopped run are dropped on the way, however many there are.
    let job;
    while ((job = pool.queue.shift()) && job.ctl && job.ctl.cancelled) job.reject(new MV.MVError('Stopped.'));
    if (!job) break;
    w.busy = job;
    pool.jobs.set(job.id, job);
    job.worker = w;
    w.postMessage({ type: 'claim', id: job.id, body: job.body, opts: job.opts, defs: job.defs, names: job.names });
  }
  if (!pool.workers.length && pool.queue.length) for (const job of pool.queue.splice(0)) job.resolve(null);
}
// Libraries changed: the workers learn the new set.
pool.reset = () => {
  const libs = APP.userLibs ? APP.userLibs() : [];
  for (const w of pool.workers) w.postMessage({ type: 'libs', libs });
};

/* ---------- what the page keeps of a notebook run, for the workers ---------- */
// For each notebook environment: the names defined anywhere in it, and the definitions so far.
const DEFS = new WeakMap();
APP.trackDefs = (env, names) => DEFS.set(env, { names, stmts: [] });
APP.noteDef = (env, stmt) => { const d = DEFS.get(env); if (d) d.stmts.push({ text: stmt.text, line: stmt.line, endLine: stmt.endLine, lines: stmt.lines, docLines: stmt.docLines }); };
APP.defsSnapshot = env => { const d = DEFS.get(env); return d ? { names: d.names, stmts: d.stmts.slice() } : null; };

// A formula is plain data (no function values inside), so it can travel to a worker.
function plain(n, depth = 0) {
  if (depth > 200) return false;
  if (n === null || typeof n !== 'object') return typeof n !== 'function';
  if (Array.isArray(n)) return n.every(x => plain(x, depth + 1));
  if (Object.getPrototypeOf(n) !== Object.prototype) return false;
  if (n.type === 'value') return false;
  return Object.values(n).every(x => plain(x, depth + 1));
}

/* ---------- the page side of a check ---------- */
// Back from plain data: the claim prepared again on the page (cheap), each sample's environment
// rebuilt only when asked for.
function rehydrate(sum, body, env, opts) {
  // The same samples the worker had: same seed, same preparation.
  let P, tuples = [];
  try { ({ P, sampled: { tuples } } = MV.claimTuples(body, env, opts || {})); } finally { MV.STRESS = 0; }
  if (sum.res.some(x => x.i >= 0 && !tuples[x.i])) return null;
  const bindAll = vals => {
    const e = MV.bindValues(P, vals);
    if (e) return e;
    let x = P.scope;
    P.binders.forEach((b, i) => { x = Object.create(x); MV.bindTarget(x, b.b, vals[i]); });
    return x;
  };
  const mk = x => {
    const r = { ...x };
    let e = null;
    Object.defineProperty(r, 'env', { get() { return e || (e = bindAll(r.vals)); }, configurable: true });
    if (P.W) Object.defineProperty(r, 'wdom', { get() { try { return P.W.dom(r.env); } catch (err) { return null; } }, configurable: true });
    return r;
  };
  const res = sum.res.map(x => (x.i >= 0 ? Object.assign(mk({ ...x, vals: tuples[x.i].vals }), {}) : mk(x)));
  // Samples from the list already have their environments.
  sum.res.forEach((x, j) => { if (x.i >= 0) Object.defineProperty(res[j], 'env', { value: tuples[x.i].env, configurable: true }); });
  let dom0 = null;
  try { if (P.binders.length) dom0 = P.binders[0].dom(P.scope); } catch (e) { /* depends on another variable */ }
  return {
    unfolded: P.unfolded, shown: P.shown, body: P.node, bindings: P.bindings, binders: P.U, scope: P.scope, k: P.U.length,
    kind: P.kind, hyp: P.hyp, concl: P.concl, op: P.op, W: P.W, prepared: P, dom0,
    count: sum.count, proved: sum.proved, algebra: sum.algebra || undefined, res,
    exhaustive: sum.exhaustive, stopped: sum.stopped, total: sum.total, stressable: sum.stressable, restricted: sum.restricted,
    factor: sum.factor, stress: sum.stress, wInteger: sum.wInteger,
    simplest: sum.simplestIndex >= 0 ? res[sum.simplestIndex] : sum.simplest ? mk(sum.simplest) : null,
    searched: sum.searched ? { ...sum.searched, best: sum.searched.best ? mk(sum.searched.best) : null } : undefined,
    worker: true,
  };
}

// Check a claim: in a worker when it can go there, otherwise on the page as before.
APP.analyze = async (body, env, opts, ctl, defs = null) => {
  const local = () => MV.analyzeClaimAsync(body, env, opts, ctl);
  defs = defs || APP.defsSnapshot(env);
  if (!pool.supported() || !defs || !plain(body)) return local();
  if (pool.state === 'off') start();
  const run = o => new Promise((resolve, reject) => {
    const job = { id: pool.nextId++, body, opts: JSON.parse(JSON.stringify(o || {})), defs: defs.stmts, names: defs.names, ctl, resolve, reject };
    if (ctl) {
      // Stop: every job of this check (one per slice, then the merge) is stopped: a queued one is
      // dropped, a running one is told to stop at its next pause.
      if (!ctl.poolJobs) {
        let stopped = ctl.cancelled;
        const jobs = [];
        Object.defineProperty(ctl, 'poolJobs', { value: jobs });
        Object.defineProperty(ctl, 'cancelled', {
          configurable: true,
          get: () => stopped,
          set: v => {
            stopped = v;
            if (!v) return;
            for (const j of jobs) {
              const i = pool.queue.indexOf(j);
              if (i >= 0) { pool.queue.splice(i, 1); j.reject(new MV.MVError('Stopped.')); }
              else if (j.worker && pool.jobs.has(j.id)) j.worker.postMessage({ type: 'cancel', id: j.id });
            }
          },
        });
      }
      ctl.poolJobs.push(job);
    }
    pool.queue.push(job);
    pump();
  });
  // How many samples? Many: split them over the workers (every n-th sample to each), merge the
  // verdicts, and let one worker run the search and the exact proofs on the merged list.
  let total = 0;
  try { total = MV.claimTuples(body, env, opts || {}).sampled.tuples.length; } catch (e) { total = 0; } finally { MV.STRESS = 0; }
  const n = Math.min(pool.size, Math.floor(total / 48));
  let summary;
  if (n >= 2 && !(opts && opts.given)) {
    const parts = await Promise.all(Array.from({ length: n }, (_, k) => run({ ...opts, slice: { k, n }, search: false })));
    if (parts.some(p => !p)) return local();
    const given = { res: parts.flatMap(p => p.res).sort((a, b) => a.i - b.i), stopped: parts.some(p => p.stopped), inexact: parts.some(p => p.inexact) };
    summary = await run({ ...opts, given });
  } else summary = await run(opts);
  if (!summary) return local();
  return rehydrate(summary, body, env, opts) || local();
};
APP.parallel = () => pool.supported();
})();
