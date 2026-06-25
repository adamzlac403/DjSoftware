from __future__ import annotations

from dataclasses import dataclass, field, asdict
from typing import Any

AUDIO_EXTENSIONS = {'.mp3', '.flac', '.wav', '.aiff', '.aif', '.aac', '.ogg', '.opus', '.alac'}


@dataclass
class Track:
    id: str
    raw: str
    artist: str
    title: str
    album: str = ''
    spotify_url: str = ''
    explicit: bool | None = None
    status: str = 'pending'
    query_index: int = 0
    last_query: str = ''
    selected_result: dict[str, Any] | None = None
    attempts: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class SearchResult:
    query: str
    tier: str
    score: float
    raw: Any
    filename: str = ''
    username: str = ''
    size: str = ''
    bitrate: str = ''
    length: str = ''
    upload_speed: str = ''
    has_free_slot: str = ''
    slsk_link: str | None = None

    @property
    def identity_key(self) -> str:
        import re
        key = (self.filename or str(self.raw)).lower().replace('\\', '/')
        key = key.split('/')[-1]
        key = re.sub(r'[^a-z0-9]+', ' ', key).strip()
        return key

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)
