// Builds the single-file app from the project (../build.js) and puts it where the desktop app
// loads it: app/index.html.
'use strict';
const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const desktop = path.join(__dirname, '..');
const root = path.join(desktop, '..');
execFileSync(process.execPath, [path.join(root, 'build.js')], { stdio: 'inherit' });
fs.mkdirSync(path.join(desktop, 'app'), { recursive: true });
fs.copyFileSync(path.join(root, 'dist', 'theorem-sketchpad.html'), path.join(desktop, 'app', 'index.html'));
console.log('Copied the app to desktop/app/index.html');
