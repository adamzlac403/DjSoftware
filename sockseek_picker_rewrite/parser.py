from __future__ import annotations

import re
import uuid
from pathlib import Path
from models import Track

NOISE_PATTERNS = [
    r'^\s*-\s*', r'^\s*\d{1,3}\s*[\.\-_)]+\s*', r'^\s*\d{2,3}\s*bpm\s*-\s*',
    r'\b\d{1,3}\s*bpm\b', r'\b\d{1,2}[ab]\b', r'\benergy\s*\d+\b',
    r'\bwww\.[^\s]+\b', r'https?://\S+', r'\\',
]

VERSION_REMOVE_PATTERNS = [
    r'\bintro\s*[-/]?\s*dirty\b', r'\bdirty\s*[-/]?\s*intro\b',
    r'\bintro\s*[-/]?\s*clean\b', r'\bclean\s*[-/]?\s*intro\b', r'\bno\s*intro\b',
    r'\bintro\s*outro\b', r'\bintro\s*edit\b', r'\bdj\s*intro\b', r'\bck\s*intro\b',
    r'\bdjcity\s*intro\b', r'\btmu\s*(urban|uk urban|throwback)?\s*intro\b',
    r'\bmmp\s*intro\s*(edit)?\b', r'\bhh\s*(dirty|clean)?\s*intro\b', r'\bhype\s*intro\b',
    r'\b8\s*bar\s*intro\b', r'\bacap(ella)?\s*intro\b', r'\bintro\b', r'\bdirty\b',
    r'\bclean\b', r'\bexplicit\b', r'\bmain\b', r'\bradio\s*edit\b', r'\boriginal\s*mix\b',
    r'\bextended\s*(mix|version)?\b', r'\bclub\s*mix\b', r'\bquick\s*hit\b',
]


def clean_spaces(text: str) -> str:
    return re.sub(r'\s+', ' ', str(text)).strip(' -_\t\r\n')


def strip_noise(text: str) -> str:
    out = str(text).strip()
    for pat in NOISE_PATTERNS:
        out = re.sub(pat, ' ', out, flags=re.I)
    return clean_spaces(out)


def normalise(text: str) -> str:
    text = str(text).lower().replace('&', ' and ')
    return clean_spaces(re.sub(r'[^a-z0-9]+', ' ', text))


def clean_artist(artist: str) -> str:
    artist = strip_noise(artist).replace(';', ', ')
    artist = re.sub(r'\b(featuring|feat\.?|ft\.?)\b', 'ft', artist, flags=re.I)
    artist = re.sub(r'\s+and\s+', ' & ', artist, flags=re.I)
    return clean_spaces(artist)


def clean_title(title: str) -> str:
    title = strip_noise(title)

    def bracket_repl(match: re.Match[str]) -> str:
        inner = match.group(1)
        low = inner.lower()
        if any(re.search(p, low, flags=re.I) for p in VERSION_REMOVE_PATTERNS):
            return ' '
        if re.search(r'\b(feat|ft|featuring)\b', low):
            return ' '
        return f' {inner} '

    title = re.sub(r'\(([^)]*)\)', bracket_repl, title)
    title = re.sub(r'\[([^]]*)\]', bracket_repl, title)
    for pat in VERSION_REMOVE_PATTERNS:
        title = re.sub(pat, ' ', title, flags=re.I)
    title = re.sub(r'\s+(feat\.?|ft\.?)\s+.*$', '', title, flags=re.I)
    return clean_spaces(title)


def split_artist_title(raw: str) -> tuple[str, str]:
    text = strip_noise(Path(raw).stem)
    parts = [clean_spaces(p) for p in re.split(r'\s+-\s+', text) if clean_spaces(p)]
    if len(parts) >= 2:
        artist, title = parts[0], ' - '.join(parts[1:])
    else:
        artist, title = '', text
    artist = clean_artist(artist)
    title = clean_title(title)
    if artist and title.lower().startswith(artist.lower() + ' - '):
        title = clean_spaces(title[len(artist) + 3:])
    return artist, title


def make_track(raw: str, artist: str = '', title: str = '', album: str = '', spotify_url: str = '', explicit: bool | None = None) -> Track:
    if not title:
        parsed_artist, parsed_title = split_artist_title(raw)
        artist = artist or parsed_artist
        title = parsed_title
    return Track(id=str(uuid.uuid4()), raw=raw, artist=clean_artist(artist), title=clean_title(title), album=album, spotify_url=spotify_url, explicit=explicit)


def make_queries(track: Track) -> list[tuple[str, str]]:
    """Build a broad-to-specific DJ search ladder.

    The first query deliberately searches for just "intro" rather than
    "intro clean". Many DJ-pool shares are named "Intro", "Intro Edit", or
    "DJ Intro" and only say "clean" elsewhere in the path. Clean/dirty choice
    is therefore handled by scoring/filtering instead of over-constraining the
    Soulseek query.
    """
    artist = clean_spaces(track.artist)
    title = clean_spaces(track.title)
    exact = clean_spaces(f'{artist} {title}') if artist else title
    broad = artist
    title_only = title

    ladder = [
        ('Intro / Exact', f'{exact} intro'),
        ('Intro / Title Only', f'{title_only} intro'),
        ('Intro / Broad', f'{broad} intro'),
        ('Clean / Exact', f'{exact} clean'),
        ('Clean / Broad', f'{broad} clean'),
        ('Normal / Exact', exact),
        ('Normal / Broad', broad),
    ]
    out: list[tuple[str, str]] = []
    seen: set[str] = set()
    for tier, query in ladder:
        query = clean_spaces(query)
        if query and query.casefold() not in seen:
            seen.add(query.casefold())
            out.append((tier, query))
    return out
