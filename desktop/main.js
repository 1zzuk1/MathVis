// Theorem Sketchpad as a desktop app: the same single-file app (app/index.html, made from the
// project by scripts/prepare.js) in its own Chromium window, the same on Windows, macOS and Linux.
// The page gets no Node access; links to web pages open in the system browser; downloads (a
// notebook, a report) ask where to save, as Chromium does.
'use strict';
const { app, BrowserWindow, Menu, shell, session, nativeTheme } = require('electron');
const path = require('path');

const PAGE = path.join(__dirname, 'app', 'index.html');
const SMOKE = process.env.TS_SMOKE === '1';   // a hidden run that checks the app works, then quits

// One window for the app: opening it again brings the existing one forward.
if (!SMOKE && !app.requestSingleInstanceLock()) app.quit();
let win = null;
app.on('second-instance', () => { if (win) { if (win.isMinimized()) win.restore(); win.focus(); } });

function createWindow() {
  win = new BrowserWindow({
    width: 1400, height: 900, minWidth: 720, minHeight: 480,
    title: 'Theorem Sketchpad',
    backgroundColor: nativeTheme.shouldUseDarkColors ? '#0F1412' : '#EBEFED',
    show: false,
    icon: path.join(__dirname, 'build', 'icon.png'),
    webPreferences: { contextIsolation: true, nodeIntegration: false, sandbox: true, spellcheck: true },
  });
  if (!SMOKE) win.once('ready-to-show', () => win.show());
  // The app never navigates away from itself; web links open in the system browser.
  win.webContents.setWindowOpenHandler(({ url }) => {
    if (/^https?:\/\//.test(url)) shell.openExternal(url);
    return { action: 'deny' };
  });
  win.webContents.on('will-navigate', (event, url) => {
    if (url.split('#')[0] === win.webContents.getURL().split('#')[0]) return;
    event.preventDefault();
    if (/^https?:\/\//.test(url)) shell.openExternal(url);
  });
  win.loadFile(PAGE);
  win.on('closed', () => { win = null; });
  if (SMOKE) smokeTest();
}

function menu() {
  const mac = process.platform === 'darwin';
  const template = [
    ...(mac ? [{ role: 'appMenu' }] : []),
    { label: 'File', submenu: [mac ? { role: 'close' } : { role: 'quit' }] },
    { role: 'editMenu' },   // copy and paste shortcuts (on macOS they need this menu)
    {
      label: 'View',
      submenu: [
        { role: 'reload' }, { type: 'separator' },
        { role: 'resetZoom' }, { role: 'zoomIn' }, { role: 'zoomOut' }, { type: 'separator' },
        { role: 'togglefullscreen' }, { type: 'separator' }, { role: 'toggleDevTools' },
      ],
    },
    { role: 'windowMenu' },
    {
      role: 'help',
      submenu: [{ label: 'Project page', click: () => shell.openExternal(require('./package.json').homepage || 'https://github.com') }],
    },
  ];
  Menu.setApplicationMenu(Menu.buildFromTemplate(template));
}

app.whenReady().then(() => {
  // The app asks for nothing: no camera, microphone, location or notifications.
  session.defaultSession.setPermissionRequestHandler((wc, permission, callback) => callback(false));
  menu();
  createWindow();
  app.on('activate', () => { if (!BrowserWindow.getAllWindows().length) createWindow(); });
});
app.on('window-all-closed', () => { if (process.platform !== 'darwin' || SMOKE) app.quit(); });

// TS_SMOKE=1: load the app hidden, run the first example notebook (which also stops the page's own
// first run halfway), print what came out, quit. Fails if a result is an error or the run hangs.
function smokeTest() {
  const fail = msg => { console.log('SMOKE FAIL ' + msg); app.exit(1); };
  const timer = setTimeout(() => fail('timeout'), 100000);
  win.webContents.on('did-fail-load', (e, code, desc) => fail('load ' + desc));
  win.webContents.on('console-message', e => { if (e.level === 'error') console.log('PAGE error: ' + e.message); });
  win.webContents.on('did-finish-load', async () => {
    try {
      const res = await win.webContents.executeJavaScript(`(async () => {
        const wait = () => new Promise(r => setTimeout(r, 100));
        for (let i = 0; i < 100 && !(window.APP && APP.run); i++) await wait();
        APP.loadSource(APP.EXAMPLES[0].src);
        await wait();
        const done = () => !document.querySelector('#run').classList.contains('busy') && document.querySelector('#summary').textContent;
        for (let i = 0; i < 800 && !done(); i++) await wait();
        const chips = [...APP.OUT.querySelectorAll('.card')].map(c => c.querySelector('.chip:not([hidden])')).filter(Boolean);
        return {
          finished: !!done(),
          summary: document.querySelector('#summary').innerText.replace(/\\s+/g, ' ').trim(),
          results: chips.length,
          errors: chips.filter(c => c.classList.contains('error')).length,
          words: MV.wordsToNotation('every convergent sequence is bounded').text,
        };
      })()`);
      clearTimeout(timer);
      console.log('SMOKE ' + JSON.stringify(res));
      app.exit(res.finished && res.results && !res.errors ? 0 : 1);
    } catch (e) { fail(e.message); }
  });
}
