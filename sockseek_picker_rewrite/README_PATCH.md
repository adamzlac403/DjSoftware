# Stateful search + fewer Rekordbox popups patch

Replace your current project files with these files.

Changes:
- Editing Artist / Title / Album / Raw now rebuilds the generated Soulseek query list after a short debounce.
- Rekordbox duplicate checks are informational and do not interrupt preview/download.
- Added **Set default playlist** button.
- Once a default playlist is set, accepted existing RB tracks and newly downloaded/kept files are added to that playlist automatically for the rest of the session.
- Removed success/confirm popups from Rekordbox playlist actions; results are written to the log instead.
- If no default playlist is set, downloads still continue normally and the log tells you no playlist add was attempted.

Run command example:

```bat
python main.py --spotify-csv "..\OILS (1).csv" --download-dir "C:\Users\adam\Music\Soulseek Downloads" --sockseek "..\sockseek.exe" --config "..\sockseek.conf" --rekordbox-root "C:\Users\adam\DjSoftware\rekordbox-mcp"
```
