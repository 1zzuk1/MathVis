@echo off
rem Builds the Windows installer (Setup .exe) and a portable .exe into desktop\release.
title Theorem Sketchpad: building the installers
cd /d "%~dp0desktop"
where node >nul 2>nul
if errorlevel 1 (
  echo Node.js is needed: install the LTS version from https://nodejs.org and start this file again.
  start "" https://nodejs.org
  pause
  exit /b 1
)
if not exist "node_modules\electron-builder" (
  echo Installing Electron and electron-builder, once.
  call npm install
  if errorlevel 1 ( pause & exit /b 1 )
)
call npm run dist
if errorlevel 1 (
  echo The build failed; see the messages above.
  pause
  exit /b 1
)
echo.
echo Done: the installers are in desktop\release.
start "" "%~dp0desktop\release"
pause
