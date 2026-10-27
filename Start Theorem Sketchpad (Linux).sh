#!/bin/bash
# Starts Theorem Sketchpad as a desktop app. The first time it downloads Electron (about 100 MB).
cd "$(dirname "$0")/desktop" || exit 1
OPEN=xdg-open
if ! command -v node >/dev/null 2>&1; then
  echo "Node.js is needed to run the desktop app: install the LTS version from https://nodejs.org"
  echo "and start this file again. Meanwhile the app opens in your browser instead."
  $OPEN ../index.html >/dev/null 2>&1
  $OPEN https://nodejs.org >/dev/null 2>&1
  read -r -p "Press Enter to close." _
  exit 1
fi
if [ ! -x node_modules/.bin/electron ]; then
  echo "First start: installing Electron, about 100 MB. This happens only once."
  npm install || { read -r -p "The installation failed. Press Enter to close." _; exit 1; }
fi
npm run prepare-app || { read -r -p "Press Enter to close." _; exit 1; }
# Without a setuid chrome-sandbox (an npm install never has one) Electron needs --no-sandbox.
ARGS=""
SB=node_modules/electron/dist/chrome-sandbox
if [ "$(stat -c %U:%a "$SB" 2>/dev/null)" != "root:4755" ]; then ARGS="--no-sandbox"; fi
nohup ./node_modules/.bin/electron . $ARGS >/dev/null 2>&1 &
exit 0
