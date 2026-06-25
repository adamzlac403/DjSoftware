from __future__ import annotations

import csv
import json
import os
import re
from pathlib import Path
from models import Track
from parser import make_track, normalise


def load_state(path: Path) -> list[Track] | None:
    if not path.exists(): return None
    try:
        data = json.loads(path.read_text(encoding='utf-8'))
        # State files from older versions will not have newer fields such as explicit.
        allowed = set(Track.__dataclass_fields__.keys())
        tracks = [Track(**{k: v for k, v in x.items() if k in allowed}) for x in data]
        return tracks or None
    except Exception:
        return None


def save_state(path: Path, tracks: list[Track]) -> None:
    path.write_text(json.dumps([t.to_dict() for t in tracks], indent=2, ensure_ascii=False), encoding='utf-8')


def load_text(path: Path, state_path: Path) -> list[Track]:
    if tracks := load_state(state_path): return tracks
    seen, out = set(), []
    for raw in path.read_text(encoding='utf-8', errors='replace').splitlines():
        raw = raw.strip()
        if not raw or raw.lower().startswith('skip to '): continue
        track = make_track(raw)
        if not track.title: continue
        key = (normalise(track.artist), normalise(track.title))
        if key in seen: continue
        seen.add(key); out.append(track)
    return out


def parse_bool(value: str) -> bool | None:
    text = str(value or '').strip().lower()
    if text in {'true', 'yes', 'y', '1', 'explicit'}:
        return True
    if text in {'false', 'no', 'n', '0', 'clean', 'not explicit'}:
        return False
    return None


def load_csv(path: Path, state_path: Path) -> list[Track]:
    if tracks := load_state(state_path): return tracks
    def get(row: dict[str, str], names: list[str]) -> str:
        lower = {k.strip().lower(): (v or '').strip() for k, v in row.items()}
        return next((lower[n.lower()] for n in names if n.lower() in lower and lower[n.lower()]), '')
    seen, out = set(), []
    with path.open('r', encoding='utf-8-sig', errors='replace', newline='') as f:
        for row in csv.DictReader(f):
            title = get(row, ['Track Name','Name','Title','Track','Song'])
            artist = get(row, ['Artist Name(s)','Artists','Artist','Artist Name','Artist(s)'])
            album = get(row, ['Album Name','Album'])
            url = get(row, ['Track URL','Spotify URL','URL','Track URI','Spotify URI','URI'])
            explicit = parse_bool(get(row, ['Explicit','Is Explicit','explicit','is_explicit']))
            if not title: continue
            key = (normalise(artist), normalise(title))
            if key in seen: continue
            track = make_track(f'{artist} - {title}' if artist else title, artist, title, album, url)
            track.explicit = explicit
            seen.add(key); out.append(track)
    return out


def load_spotify_url(playlist_url: str, state_path: Path) -> list[Track]:
    if tracks := load_state(state_path): return tracks
    try:
        import spotipy
        from spotipy.oauth2 import SpotifyOAuth
        from spotipy.exceptions import SpotifyException
    except Exception as exc:
        raise SystemExit('Spotify mode needs spotipy. Install with: pip install spotipy\n' + f'Original error: {exc}')
    client_id = os.environ.get('SPOTIPY_CLIENT_ID') or os.environ.get('SPOTIFY_CLIENT_ID')
    client_secret = os.environ.get('SPOTIPY_CLIENT_SECRET') or os.environ.get('SPOTIFY_CLIENT_SECRET')
    redirect_uri = os.environ.get('SPOTIPY_REDIRECT_URI') or os.environ.get('SPOTIFY_REDIRECT_URI') or 'http://127.0.0.1:8888/callback'
    if not client_id or not client_secret:
        raise SystemExit('Spotify mode needs SPOTIPY_CLIENT_ID and SPOTIPY_CLIENT_SECRET. Or export playlist to CSV and use --spotify-csv.')
    token_cache = state_path.with_suffix('.spotify_token_cache')
    sp = spotipy.Spotify(auth_manager=SpotifyOAuth(client_id=client_id, client_secret=client_secret, redirect_uri=redirect_uri, scope='playlist-read-private playlist-read-collaborative', cache_path=str(token_cache), open_browser=True))
    try:
        results = sp.playlist_items(playlist_url, fields='items(track(name,explicit,external_urls,uri,album(name),artists(name))),next', additional_types=['track'], limit=100)
    except SpotifyException as exc:
        raise SystemExit(f'Spotify permission error. Check redirect URI {redirect_uri}, sign into the right account, or use CSV.\nOriginal error: {exc}')
    seen, out = set(), []
    while results:
        for item in results.get('items', []):
            tr = (item or {}).get('track') or {}
            title = tr.get('name') or ''
            artists = ', '.join(a.get('name', '') for a in tr.get('artists', []) if a.get('name'))
            album = ((tr.get('album') or {}).get('name') or '')
            url = (tr.get('external_urls') or {}).get('spotify') or tr.get('uri') or ''
            if not title: continue
            key = (normalise(artists), normalise(title))
            if key in seen: continue
            track = make_track(f'{artists} - {title}', artists, title, album, url)
            track.explicit = tr.get('explicit') if isinstance(tr.get('explicit'), bool) else None
            seen.add(key); out.append(track)
        results = sp.next(results) if results.get('next') else None
    save_state(state_path, out)
    return out


def spotify_state_name(url: str) -> str:
    return 'spotify_' + re.sub(r'[^a-zA-Z0-9_.-]+', '_', url.strip())[:80] + '.sockseek_state.json'
