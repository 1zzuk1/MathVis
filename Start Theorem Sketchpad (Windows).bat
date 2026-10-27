@echo off
rem Starts Theorem Sketchpad as a desktop app. The first time it downloads Electron (about 100 MB).
title Theorem Sketchpad
cd /d "%~dp0desktop"
where node >nul 2>nul
if errorlevel 1 (
  echo Node.js is needed to run the desktop app: install the LTS version from https://nodejs.org
  echo and start this file again. Meanwhile the app opens in your browser instead.
  start "" "%~dp0index.html"
  start "" https://nodejs.org
  pause
  exit /b 1
)
if not exist "node_modules\electron\dist\electron.exe" (
  echo First start: installing Electron, about 100 MB. This happens only once.
  call npm install
  if errorlevel 1 (
    echo The installation failed; see the messages above.
    pause
    exit /b 1
  )
)
call npm run prepare-app
if errorlevel 1 (
  pause
  exit /b 1
)
start "" "node_modules\electron\dist\electron.exe" .
