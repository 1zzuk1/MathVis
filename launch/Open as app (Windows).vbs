' Theorem Sketchpad: opens the app in its own window (Microsoft Edge or Google Chrome in app mode),
' or in the default browser when neither is installed. Double-click this file.
Option Explicit
Dim fso, sh, here, candidates, c, target, url, browsers, b
Set fso = CreateObject("Scripting.FileSystemObject")
Set sh = CreateObject("WScript.Shell")
here = fso.GetParentFolderName(WScript.ScriptFullName)

' The app: next to this file (the release folder), or the built file / the sources in the project.
candidates = Array(here & "\Theorem Sketchpad.html", here & "\..\dist\theorem-sketchpad.html", here & "\..\index.html")
target = ""
For Each c In candidates
  If fso.FileExists(c) Then
    target = fso.GetAbsolutePathName(c)
    Exit For
  End If
Next
If target = "" Then
  MsgBox "Theorem Sketchpad.html wasn't found next to this file.", 48, "Theorem Sketchpad"
  WScript.Quit
End If
url = FileUrl(target)

browsers = Array( _
  sh.ExpandEnvironmentStrings("%ProgramFiles(x86)%") & "\Microsoft\Edge\Application\msedge.exe", _
  sh.ExpandEnvironmentStrings("%ProgramFiles%") & "\Microsoft\Edge\Application\msedge.exe", _
  sh.ExpandEnvironmentStrings("%ProgramFiles%") & "\Google\Chrome\Application\chrome.exe", _
  sh.ExpandEnvironmentStrings("%ProgramFiles(x86)%") & "\Google\Chrome\Application\chrome.exe", _
  sh.ExpandEnvironmentStrings("%LocalAppData%") & "\Google\Chrome\Application\chrome.exe")
For Each b In browsers
  If fso.FileExists(b) Then
    sh.Run """" & b & """ --app=""" & url & """", 1, False
    WScript.Quit
  End If
Next
' No Edge or Chrome: the default browser, through the Windows shell (safe with any folder name).
CreateObject("Shell.Application").ShellExecute target

' A file:/// address with every character outside plain ASCII percent-encoded as UTF-8, so a
' folder named in Cyrillic (or with spaces) reaches the browser intact.
Function FileUrl(p)
  Dim s, i, c, code, out
  s = Replace(p, "\", "/")
  out = ""
  For i = 1 To Len(s)
    c = Mid(s, i, 1)
    code = AscW(c)
    If code < 0 Then code = code + 65536
    If (code >= 48 And code <= 57) Or (code >= 65 And code <= 90) Or (code >= 97 And code <= 122) Or InStr("/:-._~", c) > 0 Then
      out = out & c
    ElseIf code < 128 Then
      out = out & "%" & Right("0" & Hex(code), 2)
    ElseIf code < 2048 Then
      out = out & "%" & Hex(192 + (code \ 64)) & "%" & Hex(128 + (code And 63))
    Else
      out = out & "%" & Hex(224 + (code \ 4096)) & "%" & Hex(128 + ((code \ 64) And 63)) & "%" & Hex(128 + (code And 63))
    End If
  Next
  FileUrl = "file:///" & out
End Function
