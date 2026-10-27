// Bundles index.html and everything it loads into one self-contained file.
//   node build.js              -> dist/theorem-sketchpad.html
//   node build.js --release    -> also dist/Theorem-Sketchpad.zip (the app as "Theorem Sketchpad.html",
//                                 the "Open as app" launchers, How to use.txt) and dist/site/index.html
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');

const root = __dirname;
const release = process.argv.includes('--release');
let html = fs.readFileSync(path.join(root, 'index.html'), 'utf8');

html = html.replace(/<link rel="stylesheet" href="(?!https?:)([^"]+)">/g, (_, file) =>
  `<style>\n${fs.readFileSync(path.join(root, file), 'utf8')}</style>`);
html = html.replace(/<script src="([^"]+)"><\/script>/g, (_, file) => {
  const code = fs.readFileSync(path.join(root, file), 'utf8').replace(/<\/script/gi, '<\\/script');
  // The file name stays on the tag, so app/workers.js can build its workers from the same code.
  return `<script data-src="${file}">\n${code}</script>`;
});

const dist = path.join(root, 'dist');
const out = path.join(dist, 'theorem-sketchpad.html');
fs.mkdirSync(dist, { recursive: true });
fs.writeFileSync(out, html);
console.log(`Wrote ${path.relative(root, out)} (${(html.length / 1024).toFixed(0)} KB)`);

if (release) {
  // The online copy (GitHub Pages serves dist/site).
  fs.mkdirSync(path.join(dist, 'site'), { recursive: true });
  fs.writeFileSync(path.join(dist, 'site', 'index.html'), html);
  fs.writeFileSync(path.join(dist, 'Theorem Sketchpad.html'), html);
  // The download: one folder, ready to double-click.
  const launch = path.join(root, 'launch');
  const entries = [{ name: 'Theorem Sketchpad/Theorem Sketchpad.html', data: Buffer.from(html) }];
  for (const f of fs.readdirSync(launch)) {
    let data = fs.readFileSync(path.join(launch, f));
    // Windows scripts and notes with Windows line endings; shell scripts executable.
    if (/\.(vbs|txt)$/.test(f)) data = Buffer.from(data.toString('utf8').replace(/\r?\n/g, '\r\n'));
    entries.push({ name: `Theorem Sketchpad/${f}`, data, exec: /\.(command|sh)$/.test(f) });
  }
  const zip = makeZip(entries);
  fs.writeFileSync(path.join(dist, 'Theorem-Sketchpad.zip'), zip);
  console.log(`Wrote dist/Theorem-Sketchpad.zip (${(zip.length / 1024).toFixed(0)} KB, ${entries.length} files) and dist/site/index.html`);
}

/* A small zip writer (deflate), so a release needs nothing beyond Node. */
function crc32(buf) {
  let c, crc = 0xFFFFFFFF;
  for (let n = 0; n < buf.length; n++) {
    c = (crc ^ buf[n]) & 0xFF;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1;
    crc = (crc >>> 8) ^ c;
  }
  return (crc ^ 0xFFFFFFFF) >>> 0;
}
function makeZip(files) {
  const locals = [], centrals = [];
  let offset = 0;
  const time = 0, date = ((2026 - 1980) << 9) | (1 << 5) | 1;
  for (const f of files) {
    const name = Buffer.from(f.name, 'utf8');
    const deflated = zlib.deflateRawSync(f.data, { level: 9 });
    const crc = crc32(f.data);
    const local = Buffer.alloc(30);
    local.writeUInt32LE(0x04034b50, 0); local.writeUInt16LE(20, 4); local.writeUInt16LE(0x0800, 6); local.writeUInt16LE(8, 8);
    local.writeUInt16LE(time, 10); local.writeUInt16LE(date, 12); local.writeUInt32LE(crc, 14);
    local.writeUInt32LE(deflated.length, 18); local.writeUInt32LE(f.data.length, 22); local.writeUInt16LE(name.length, 26); local.writeUInt16LE(0, 28);
    locals.push(local, name, deflated);
    const central = Buffer.alloc(46);
    central.writeUInt32LE(0x02014b50, 0); central.writeUInt16LE((3 << 8) | 20, 4); central.writeUInt16LE(20, 6); central.writeUInt16LE(0x0800, 8);
    central.writeUInt16LE(8, 10); central.writeUInt16LE(time, 12); central.writeUInt16LE(date, 14); central.writeUInt32LE(crc, 16);
    central.writeUInt32LE(deflated.length, 20); central.writeUInt32LE(f.data.length, 24); central.writeUInt16LE(name.length, 28);
    // Unix permissions in the upper half: rwxr-xr-x for scripts, rw-r--r-- otherwise.
    central.writeUInt32LE(((f.exec ? 0o100755 : 0o100644) << 16) >>> 0, 38);
    central.writeUInt32LE(offset, 42);
    centrals.push(central, name);
    offset += local.length + name.length + deflated.length;
  }
  const cd = Buffer.concat(centrals);
  const end = Buffer.alloc(22);
  end.writeUInt32LE(0x06054b50, 0); end.writeUInt16LE(files.length, 8); end.writeUInt16LE(files.length, 10);
  end.writeUInt32LE(cd.length, 12); end.writeUInt32LE(offset, 16);
  return Buffer.concat([...locals, cd, end]);
}
