// Starts the desktop app hidden (TS_SMOKE=1): it runs the first example notebook, prints the
// result and quits. Exits non-zero if the app failed to load or a statement errored.
'use strict';
const { spawnSync } = require('child_process');
const path = require('path');
const electron = require('electron');   // the path to the Electron binary

// GitHub's Linux machines don't allow Chromium's sandbox; the check runs without it there.
const args = [path.join(__dirname, '..')];
if (process.platform === 'linux' && process.env.CI) args.push('--no-sandbox');
const r = spawnSync(electron, args, { env: { ...process.env, TS_SMOKE: '1' }, encoding: 'utf8', timeout: 120000 });
const out = (r.stdout || '') + (r.stderr || '');
const line = out.split('\n').find(l => l.startsWith('SMOKE'));
console.log(line || out.slice(-2000));
process.exit(line && line.startsWith('SMOKE {') && r.status === 0 ? 0 : 1);
