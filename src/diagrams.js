/* Theorem Sketchpad — checking diagrams of maps between finite sets and groups, exhaustively:
   each arrow lands in its target (and, between groups, whether it is a homomorphism), each
   equation g ∘ f = h holds at every element, and each "exact at B" has image = kernel. A failure
   names the element where it fails. */
'use strict';
(function (global) {
const MV = global.MV;
const { MVError } = MV;

const isGroup = v => v && v.__record && v.fields && 'G' in v.fields && 'op' in v.fields && 'e' in v.fields;
function elementsOf(v, what) {
  const D = isGroup(v) ? MV.toDomain(v.fields.G) : (() => { try { return MV.toDomain(v, what); } catch (e) { return null; } })();
  if (!D) throw new MVError(`${what} is ${MV.describeValue(v)}: the objects of a diagram are finite sets or groups.`);
  const els = MV.elementsOf(D);
  if (!els) throw new MVError(`${what} is ${D.describe()}, which isn't a finite set; diagrams are checked element by element.`);
  if (els.length > 2000) throw new MVError(`${what} has ${els.length} elements; diagrams are checked for at most 2000.`);
  return { els, D };
}
const member = (obj, y) => obj.els.some(x => MV.equalValues(x, y));
// The object's own element equal to y (a map may return 1 for the element 1 of ℤ/2), or y itself.
const canonical = (obj, y) => { const i = obj.els.findIndex(x => MV.equalValues(x, y)); return i < 0 ? y : obj.els[i]; };
const show = v => MV.fmt(v);
const count = n => n === 1 ? '1 element' : `${n} elements`;

function checkDiagram(ast, env) {
  const norm = t => t.replace(/\s+/g, '');
  const objects = new Map();
  const object = (node, text) => {
    const k = norm(MV.ppText(node));
    if (!objects.has(k)) {
      MV.checkNames(node, env);
      const value = MV.compile(node)(env);
      objects.set(k, { key: k, label: MV.ppText(node), value, isGroup: isGroup(value), ...elementsOf(value, text) });
    }
    return objects.get(k);
  };
  const arrows = [];
  for (const a of ast.arrows) {
    if (arrows.some(b => b.name === a.name)) throw new MVError(`Two arrows are called ${a.name}; give each its own name.`, a.pos);
    MV.checkNames({ type: 'id', name: a.name, pos: a.pos }, env);
    const fn = env[a.name];
    if (typeof fn !== 'function') throw new MVError(`${a.name} is ${MV.describeValue(fn)}, not a map.`, a.pos);
    const src = object(a.src, a.srcText), dst = object(a.dst, a.dstText);
    const apply = x => canonical(dst, MV.callValue(fn, [x], a.name));
    // Does it land in its target?
    let lands = { ok: true };
    for (const x of src.els) {
      let y;
      try { y = apply(x); } catch (e) { lands = { ok: false, detail: `${a.name}(${show(x)}) is undefined: ${e.message}` }; break; }
      if (!member(dst, y)) { lands = { ok: false, detail: `${a.name}(${show(x)}) = ${show(y)} is not in ${dst.label}` }; break; }
    }
    // Between groups: is it a homomorphism?
    let hom = null;
    if (lands.ok && src.isGroup && dst.isGroup) {
      hom = { ok: true };
      const op1 = src.value.fields.op, op2 = dst.value.fields.op;
      outer: for (const x of src.els) for (const y of src.els) {
        const l = apply(op1(x, y)), r = op2(apply(x), apply(y));
        if (!MV.equalValues(l, r)) { hom = { ok: false, detail: `${a.name}(${show(x)}·${show(y)}) = ${show(l)} but ${a.name}(${show(x)})·${a.name}(${show(y)}) = ${show(r)}` }; break outer; }
      }
    }
    arrows.push({ name: a.name, src, dst, apply, lands, hom });
  }
  const byName = n => {
    const a = arrows.find(b => b.name === n);
    if (!a) throw new MVError(`${n} is not one of the diagram's arrows (${arrows.map(b => b.name).join(', ')}).`);
    return a;
  };
  // A path written g ∘ f: apply f first. Checks that consecutive arrows meet.
  const pathOf = names => {
    const seq = names.map(byName).reverse();
    for (let i = 1; i < seq.length; i++) if (seq[i].src.key !== seq[i - 1].dst.key) throw new MVError(`${names.join(' ∘ ')} doesn't compose: ${seq[i - 1].name} ends at ${seq[i - 1].dst.label} but ${seq[i].name} starts at ${seq[i].src.label}.`);
    return { seq, src: seq[0].src, dst: seq[seq.length - 1].dst, text: names.join(' ∘ ') };
  };
  const run = (p, x) => p.seq.reduce((v, a) => a.apply(v), x);
  const written = (p, x) => p.seq.reduce((s, a) => `${a.name}(${s})`, show(x));
  const compare = (L, R, text) => {
    if (L.src.key !== R.src.key || L.dst.key !== R.dst.key) throw new MVError(`${text}: the two sides go ${L.src.label} → ${L.dst.label} and ${R.src.label} → ${R.dst.label}; they must start and end at the same objects.`);
    for (const x of L.src.els) {
      let l, r;
      try { l = run(L, x); r = run(R, x); } catch (e) { return { text, ok: false, detail: `at ${show(x)}: ${e.message}`, arrows: [...L.seq, ...R.seq].map(a => a.name) }; }
      if (!MV.equalValues(l, r)) return { text, ok: false, at: x, detail: `at ${show(x)}: ${written(L, x)} = ${show(l)} but ${written(R, x)} = ${show(r)}`, arrows: [...L.seq, ...R.seq].map(a => a.name) };
    }
    return { text, ok: true, detail: `${L.src.els.length === 1 ? `holds at the one element of ${L.src.label}` : `holds at all ${L.src.els.length} elements of ${L.src.label}`}`, arrows: [...L.seq, ...R.seq].map(a => a.name) };
  };
  const checks = [];
  for (const eq of ast.equations) checks.push(compare(pathOf(eq.left), pathOf(eq.right), eq.text));
  // "commutes", or no equations at all: every two paths with the same ends (up to 4 arrows).
  if (ast.all || (!ast.equations.length && !ast.exact.length)) {
    const paths = [];
    const extend = (p) => {
      paths.push(p);
      if (p.length >= 4) return;
      const end = p[p.length - 1].dst.key;
      for (const a of arrows) if (a.src.key === end && !p.includes(a)) extend([...p, a]);
    };
    for (const a of arrows) extend([a]);
    const groups = new Map();
    for (const p of paths) { const k = p[0].src.key + '→' + p[p.length - 1].dst.key; if (!groups.has(k)) groups.set(k, []); groups.get(k).push(p); }
    for (const ps of groups.values()) {
      for (let i = 1; i < ps.length; i++) {
        const L = pathOf(ps[0].map(a => a.name).reverse()), R = pathOf(ps[i].map(a => a.name).reverse());
        if (L.src.key === R.src.key) checks.push(compare(L, R, `${L.text} = ${R.text}`));
      }
    }
  }
  // Exactness at B: image of the arrow into B equals the kernel of the arrow out of B.
  for (const ex of ast.exact) {
    const B = object(ex.node, ex.text);
    const into = arrows.filter(a => a.dst.key === B.key), out = arrows.filter(a => a.src.key === B.key);
    if (into.length !== 1 || out.length !== 1) throw new MVError(`exact at ${ex.text} needs exactly one arrow into ${B.label} and one out of it (there are ${into.length} and ${out.length}).`, ex.pos);
    const [a] = into, [b] = out;
    if (!b.dst.isGroup) throw new MVError(`exact at ${ex.text}: the kernel of ${b.name} needs an identity, so ${b.dst.label} must be a group.`, ex.pos);
    const e = b.dst.value.fields.e;
    const image = a.src.els.map(a.apply);
    const inImage = y => image.some(z => MV.equalValues(z, y));
    const inKernel = y => MV.equalValues(b.apply(y), e);
    const bad1 = B.els.find(y => inImage(y) && !inKernel(y)), bad2 = B.els.find(y => !inImage(y) && inKernel(y));
    checks.push({
      text: `exact at ${B.label}`, ok: bad1 === undefined && bad2 === undefined, arrows: [a.name, b.name],
      detail: bad1 !== undefined ? `${show(bad1)} is in the image of ${a.name} but ${b.name}(${show(bad1)}) = ${show(b.apply(bad1))} ≠ ${show(e)}`
        : bad2 !== undefined ? `${show(bad2)} is in the kernel of ${b.name} but not in the image of ${a.name}`
        : `the image of ${a.name} is the kernel of ${b.name} (${count(image.filter((y, i) => image.findIndex(z => MV.equalValues(z, y)) === i).length)})`,
    });
  }
  const ok = arrows.every(a => a.lands.ok) && checks.every(c => c.ok);
  return { ok, objects: [...objects.values()], arrows, checks };
}

MV.checkDiagram = checkDiagram;
})(typeof window !== 'undefined' ? window : globalThis);
