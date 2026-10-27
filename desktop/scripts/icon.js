// Draws the app icon (build/icon.png, 1024×1024) with Electron's own Chromium. Run it once, when
// the design changes: npx electron scripts/icon.js
'use strict';
const { app, BrowserWindow } = require('electron');
const fs = require('fs');
const path = require('path');

const SVG = `<svg xmlns="http://www.w3.org/2000/svg" width="1024" height="1024" viewBox="0 0 1024 1024">
  <defs>
    <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0" stop-color="#1F7A5C"/><stop offset="1" stop-color="#0E4A38"/>
    </linearGradient>
  </defs>
  <rect x="64" y="64" width="896" height="896" rx="200" fill="url(#bg)"/>
  <path d="M180 800 Q 360 640 512 740 T 834 690" fill="none" stroke="#F2C14E" stroke-width="34" stroke-linecap="round" opacity="0.9"/>
  <text x="512" y="590" text-anchor="middle" font-family="Georgia, 'Times New Roman', serif" font-size="340" fill="#F4F7F5">&#8704;&#8707;</text>
  <circle cx="834" cy="690" r="34" fill="#F2C14E"/>
</svg>`;

app.whenReady().then(async () => {
  const win = new BrowserWindow({ width: 1024, height: 1024, show: false, frame: false, transparent: true, useContentSize: true });
  await win.loadURL('data:text/html,' + encodeURIComponent(
    `<html><head><meta charset="utf-8"></head><body style="margin:0;background:transparent">${SVG}</body></html>`));
  await new Promise(r => setTimeout(r, 300));
  const img = await win.webContents.capturePage({ x: 0, y: 0, width: 1024, height: 1024 });
  const out = path.join(__dirname, '..', 'build', 'icon.png');
  fs.mkdirSync(path.dirname(out), { recursive: true });
  fs.writeFileSync(out, img.resize({ width: 1024, height: 1024 }).toPNG());
  console.log('Wrote ' + out);
  app.quit();
});
