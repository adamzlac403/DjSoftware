from __future__ import annotations

import argparse
from pathlib import Path
from gui import App
from loaders import load_csv, load_spotify_url, load_text, spotify_state_name
from sockseek_client import SockseekClient


def main() -> int:
    parser = argparse.ArgumentParser(description='Manual Sockseek DJ version picker')
    src = parser.add_mutually_exclusive_group(required=True)
    src.add_argument('--input', help='Text file of tracks, one per line')
    src.add_argument('--spotify-csv', help='Spotify/Exportify CSV file')
    src.add_argument('--spotify-url', help='Spotify playlist URL; requires spotipy + Spotify API env vars')
    parser.add_argument('--download-dir', required=True, help='Folder where Sockseek should save downloads')
    parser.add_argument('--sockseek', default='sockseek', help='Sockseek executable path/name')
    parser.add_argument('--config', default=None, help='Optional Sockseek config path')
    parser.add_argument('--state', default=None, help='Optional JSON state file')
    parser.add_argument('--rekordbox-root', default=None, help='Optional path to sibling rekordbox-mcp project for duplicate checks')
    parser.add_argument('--no-rekordbox-check', action='store_true', help='Disable Rekordbox duplicate check before downloading')
    args = parser.parse_args()

    download_dir = Path(args.download_dir).expanduser().resolve()
    download_dir.mkdir(parents=True, exist_ok=True)

    if args.input:
        input_path = Path(args.input).expanduser().resolve()
        state_path = Path(args.state).expanduser().resolve() if args.state else input_path.with_suffix('.sockseek_state.json')
        tracks = load_text(input_path, state_path)
    elif args.spotify_csv:
        input_path = Path(args.spotify_csv).expanduser().resolve()
        state_path = Path(args.state).expanduser().resolve() if args.state else input_path.with_suffix('.sockseek_state.json')
        tracks = load_csv(input_path, state_path)
    else:
        state_path = Path(args.state).expanduser().resolve() if args.state else Path.cwd() / spotify_state_name(args.spotify_url)
        tracks = load_spotify_url(args.spotify_url, state_path)

    if not tracks:
        print('No tracks loaded.')
        return 1
    rekordbox_root = None if args.no_rekordbox_check else args.rekordbox_root
    if not args.no_rekordbox_check and rekordbox_root is None:
        # From C:\Users\adam\DjSoftware\sockseek_picker_rewrite this resolves to the sibling project.
        candidate = Path.cwd().parent / 'rekordbox-mcp'
        rekordbox_root = str(candidate) if candidate.exists() else None
    App(tracks, SockseekClient(args.sockseek, download_dir, args.config), state_path, rekordbox_root=rekordbox_root).mainloop()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
