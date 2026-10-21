@echo off
rem Turns circuit_builder.py into a stand-alone CircuitBuilder.exe (no Python needed to run it).
rem You only need to do this once, on a PC that has Python installed.
rem
rem PyInstaller's scratch files go in your TEMP folder, not next to this script, because
rem OneDrive / Dropbox lock those files while syncing and the build then fails with
rem "PermissionError: [WinError 5] Access is denied".  Only the finished .exe is copied here.
setlocal
cd /d "%~dp0"
set "HERE=%~dp0"
set "HERE=%HERE:~0,-1%"
set "WORK=%TEMP%\CircuitBuilder_build"

set "PY="
where py >nul 2>nul && set "PY=py -3"
if not defined PY (
    where python >nul 2>nul && set "PY=python"
)
if not defined PY (
    echo Python 3 was not found. Install it from https://www.python.org/downloads/windows/
    echo and tick "Add python.exe to PATH" in the installer.
    pause
    exit /b 1
)

echo.
echo === Installing PyInstaller (one-time) ===
%PY% -m pip install --upgrade pyinstaller
if errorlevel 1 (
    echo Could not install PyInstaller. Check your internet connection and try again.
    pause
    exit /b 1
)

echo.
echo === Building CircuitBuilder.exe (working folder: %WORK%) ===
if exist "%WORK%" rmdir /s /q "%WORK%"
%PY% -m PyInstaller --noconfirm --clean --onefile --windowed ^
    --name "CircuitBuilder" --icon "%HERE%\CircuitBuilder.ico" ^
    --workpath "%WORK%\build" --specpath "%WORK%" --distpath "%WORK%\dist" ^
    "%HERE%\circuit_builder.py"
if errorlevel 1 (
    echo Build failed - see the messages above.
    pause
    exit /b 1
)

if not exist "%HERE%\dist" mkdir "%HERE%\dist"
copy /y "%WORK%\dist\CircuitBuilder.exe" "%HERE%\dist\CircuitBuilder.exe" >nul
if errorlevel 1 (
    echo.
    echo The app was built, but it could not be copied into the dist folder.
    echo Close CircuitBuilder.exe if it is running and try again, or take it from here:
    echo   %WORK%\dist\CircuitBuilder.exe
    explorer "%WORK%\dist"
    pause
    exit /b 1
)
rmdir /s /q "%WORK%" 2>nul

echo.
echo Done!  Your app is here:  %HERE%\dist\CircuitBuilder.exe
echo You can copy that single file anywhere (Desktop, USB stick, classmates' PCs).
echo.
explorer "%HERE%\dist"
pause
