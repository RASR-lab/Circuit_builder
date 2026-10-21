@echo off
rem Turns circuit_builder.py into a stand-alone CircuitBuilder.exe (no Python needed to run it).
rem You only need to do this once, on a PC that has Python installed.
cd /d "%~dp0"

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
echo === Building CircuitBuilder.exe ===
%PY% -m PyInstaller --noconfirm --clean --onefile --windowed ^
    --name "CircuitBuilder" --icon "CircuitBuilder.ico" "circuit_builder.py"
if errorlevel 1 (
    echo Build failed - see the messages above.
    pause
    exit /b 1
)

echo.
echo Done!  Your app is here:  %~dp0dist\CircuitBuilder.exe
echo You can copy that single file anywhere (Desktop, USB stick, classmates' PCs).
echo.
explorer "%~dp0dist"
pause
