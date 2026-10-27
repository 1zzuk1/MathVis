#!/bin/bash
# Starts Theorem Sketchpad as a desktop app. The first time it downloads Electron (about 100 MB).
cd "$(dirname "$0")/desktop" || exit 1
OPEN=open
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
nohup ./node_modules/.bin/electron . >/dev/null 2>&1 &
# Close this Terminal window once the app is up.
sleep 2; osascript -e 'tell application "Terminal" to close (every window whose name contains "Start Theorem Sketchpad")' >/dev/null 2>&1 &
exit 0
