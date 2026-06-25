@echo off
cd /d "%~dp0"

set LOG_FILE=rekordbox_startup.log

REM Function replacement - timestamped logging
call :log "Starting Rekordbox MCP Server..."

call :log "Checking rekordbox database key..."

REM Test if database connection works
uv run python -c "import pyrekordbox; db = pyrekordbox.Rekordbox6Database(); content = list(db.get_content()); print(f'Database key working! Found {len(content)} tracks.')" >> "%LOG_FILE%" 2>&1

if errorlevel 1 (
    call :log "Database key not found or not working."
    call :log "Attempting to download key..."

    uv run python -m pyrekordbox download-key >> "%LOG_FILE%" 2>&1

    if errorlevel 1 (
        call :log "Failed to download key."
        call :log "Please run: uv run python -m pyrekordbox download-key"
        call :log "Or check the setup guide for manual key extraction."
        exit /b 1
    )

    call :log "Key downloaded successfully!"

    uv run python -c "import pyrekordbox; db = pyrekordbox.Rekordbox6Database(); content = list(db.get_content()); print(f'Database connection verified! Found {len(content)} tracks.')" >> "%LOG_FILE%" 2>&1

    if errorlevel 1 (
        call :log "Database still not accessible after key download."
        call :log "Please check that rekordbox is not running and try again."
        exit /b 1
    )

    call :log "Database setup complete!"
)

call :log "Starting rekordbox MCP server..."
call :log "This will connect to the database on startup."
call :log "If connection fails, the server will exit automatically."

uv run rekordbox-mcp --log-level DEBUG %*

goto :eof

:log
echo [%date% %time%] - %~1 >> "%LOG_FILE%"
goto :eof