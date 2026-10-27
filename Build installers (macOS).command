#!/bin/bash
# Builds the macOS disk images (.dmg, Intel and Apple Silicon) into desktop/release.
cd "$(dirname "$0")/desktop" || exit 1
if ! command -v node >/dev/null 2>&1; then
  echo "Node.js is needed: install the LTS version from https://nodejs.org and start this file again."
  read -r -p "Press Enter to close." _
  exit 1
fi
if [ ! -d node_modules/electron-builder ]; then
  echo "Installing Electron and electron-builder, once."
  npm install || { read -r -p "Press Enter to close." _; exit 1; }
fi
npm run dist || { read -r -p "The build failed. Press Enter to close." _; exit 1; }
echo
echo "Done: the installers are in desktop/release."
open release >/dev/null 2>&1
read -r -p "Press Enter to close." _
