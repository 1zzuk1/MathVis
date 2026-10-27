#!/bin/bash
# Theorem Sketchpad: opens the app in its own window (Chrome, Edge, Brave or Chromium in app mode),
# or in the default browser. Double-click this file (the first time: right-click it, then Open).
cd "$(dirname "$0")" || exit 1
target=""
for f in "Theorem Sketchpad.html" "../dist/theorem-sketchpad.html" "../index.html"; do
  if [ -f "$f" ]; then target="$(cd "$(dirname "$f")" && pwd)/$(basename "$f")"; break; fi
done
if [ -z "$target" ]; then echo "Theorem Sketchpad.html wasn't found next to this file."; exit 1; fi
# Percent-encoded (spaces, non-Latin folder names) so the browser gets the address intact.
url="file://$(printf '%s' "$target" | perl -pe 's{([^A-Za-z0-9/._~:-])}{sprintf("%%%02X", ord($1))}ge' 2>/dev/null || printf '%s' "$target")"
for app in "Google Chrome" "Microsoft Edge" "Brave Browser" "Chromium"; do
  if [ -d "/Applications/$app.app" ]; then open -na "$app" --args --app="$url"; exit 0; fi
done
open "$target"
