#!/bin/sh
# Theorem Sketchpad: opens the app in its own window (Chrome, Chromium, Edge or Brave in app mode),
# or in the default browser. Run it from your file manager ("Run" / "Execute").
cd "$(dirname "$0")" || exit 1
target=""
for f in "Theorem Sketchpad.html" "../dist/theorem-sketchpad.html" "../index.html"; do
  if [ -f "$f" ]; then target="$(cd "$(dirname "$f")" && pwd)/$(basename "$f")"; break; fi
done
if [ -z "$target" ]; then echo "Theorem Sketchpad.html wasn't found next to this file."; exit 1; fi
# Percent-encoded (spaces, non-Latin folder names) so the browser gets the address intact.
url="file://$(printf '%s' "$target" | perl -pe 's{([^A-Za-z0-9/._~:-])}{sprintf("%%%02X", ord($1))}ge' 2>/dev/null || printf '%s' "$target")"
for b in google-chrome google-chrome-stable chromium chromium-browser microsoft-edge brave-browser; do
  if command -v "$b" >/dev/null 2>&1; then "$b" --app="$url" >/dev/null 2>&1 & exit 0; fi
done
xdg-open "$target" >/dev/null 2>&1 &
