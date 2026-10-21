@echo off
rem Starts Circuit Builder with the Python installed on this PC.
cd /d "%~dp0"

where pyw >nul 2>nul
if %errorlevel%==0 (
    start "" pyw -3 "%~dp0circuit_builder.py" %*
    exit /b
)
where pythonw >nul 2>nul
if %errorlevel%==0 (
    start "" pythonw "%~dp0circuit_builder.py" %*
    exit /b
)
where python >nul 2>nul
if %errorlevel%==0 (
    python "%~dp0circuit_builder.py" %*
    exit /b
)

echo.
echo  Python 3 was not found on this computer.
echo.
echo  1. Download it from https://www.python.org/downloads/windows/
echo  2. In the installer, tick "Add python.exe to PATH".
echo  3. Double-click this file again.
echo.
pause
