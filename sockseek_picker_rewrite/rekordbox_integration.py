from __future__ import annotations

import asyncio
import inspect
import re
import sys
import threading
from dataclasses import dataclass, field
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any


@dataclass
class RekordboxTrackRef:
    id: str
    artist: str = ""
    title: str = ""
    album: str = ""
    file_path: str = ""
    playlists: list[tuple[str, str]] = field(default_factory=list)

    @property
    def label(self) -> str:
        bits = [f"{self.artist} - {self.title}".strip(" -")]
        if self.album:
            bits.append(self.album)
        if self.file_path:
            bits.append(self.file_path)
        return " | ".join(x for x in bits if x)


class RekordboxIntegration:
    """Small synchronous bridge used by the Sockseek picker GUI.

    This avoids importing the big extension GUI. It only connects to
    rekordbox_mcp.database.RekordboxDatabase and provides a deliberately loose
    duplicate assistant:

    - loads/indexes Rekordbox tracks
    - shows Strong/Possible/Weak artist/title matches
    - lets you accept an existing RB track and add it to a playlist
    - lets you ignore the suggestion and download anyway
    - best-effort attempts to add newly downloaded files to a playlist if your
      local rekordbox-mcp wrapper exposes an import/add-track method
    """

    # Loose on purpose: this is a warning assistant, not a blocker.
    MIN_MATCH_SCORE = 0.62

    def __init__(self, rekordbox_root: str | Path | None = None):
        self.root = Path(rekordbox_root).expanduser() if rekordbox_root else None
        self.error = ""
        self.loaded = False
        self.db = None
        self._loop = asyncio.new_event_loop()
        self._thread = threading.Thread(target=self._run_loop, daemon=True)
        self._thread.start()
        self._tracks: list[RekordboxTrackRef] = []
        self._playlists: list[Any] = []
        self._playlist_by_name: dict[str, Any] = {}
        self._lock = threading.Lock()

        self._prepare_import_paths()
        try:
            self._run(self._connect_and_index())
        except Exception as exc:
            self.error = f"Could not load Rekordbox library: {exc}"
            self.loaded = False

    def _run_loop(self) -> None:
        asyncio.set_event_loop(self._loop)
        self._loop.run_forever()

    def _run(self, coro):
        fut = asyncio.run_coroutine_threadsafe(coro, self._loop)
        return fut.result()

    def _prepare_import_paths(self) -> None:
        candidates: list[Path] = []
        if self.root:
            candidates.append(self.root)
            candidates.append(self.root / "rekordbox-mcp")
            candidates.append(self.root.parent / "rekordbox-mcp")
        candidates.append(Path.cwd().parent / "rekordbox-mcp")
        candidates.append(Path("C:/Users/adam/DjSoftware/rekordbox-mcp"))

        for p in candidates:
            try:
                if p.exists() and str(p) not in sys.path:
                    sys.path.insert(0, str(p))
            except Exception:
                pass

    async def _connect_and_index(self) -> None:
        from rekordbox_mcp.database import RekordboxDatabase

        self.db = RekordboxDatabase()
        await self.db.connect()

        # Prove the connection if available. Not all local wrapper versions expose this.
        try:
            await self.db.get_track_count()
        except Exception:
            pass

        await self._reload_index()
        self.loaded = True
        self.error = ""

    async def _maybe_await(self, value):
        if inspect.isawaitable(value):
            return await value
        return value

    async def _reload_index(self) -> None:
        if self.db is None:
            raise RuntimeError("Database not connected")

        playlists = await self._maybe_await(self.db.get_playlists())
        self._playlists = list(playlists or [])
        self._playlist_by_name = {
            (getattr(p, "name", "") or "").strip().casefold(): p
            for p in self._playlists
            if getattr(p, "name", "")
        }

        by_id: dict[str, RekordboxTrackRef] = {}

        # First: playlist entries. This gives playlist membership too.
        for playlist in self._playlists:
            if bool(getattr(playlist, "is_folder", False)):
                continue
            try:
                songs = await self._maybe_await(self.db.get_playlist_tracks(playlist.id))
            except Exception:
                continue
            for s in songs or []:
                self._add_track_ref(by_id, s, playlist)

        # Second: try full collection if wrapper exposes helpers. This catches
        # tracks not currently in any playlist.
        for s in await self._load_all_collection_tracks_best_effort():
            self._add_track_ref(by_id, s, None)

        self._tracks = list(by_id.values())

    async def _load_all_collection_tracks_best_effort(self) -> list[Any]:
        if self.db is None:
            return []
        candidates = [
            "get_tracks",
            "get_all_tracks",
            "get_library_tracks",
            "get_collection_tracks",
        ]
        for name in candidates:
            method = getattr(self.db, name, None)
            if method is None:
                continue
            try:
                result = await self._maybe_await(method())
                if result:
                    return list(result)
            except Exception:
                pass

        # Last resort for your current wrapper style: private helpers used by the extension GUI.
        try:
            if hasattr(self.db, "_get_active_content") and hasattr(self.db, "_content_to_track"):
                rows = await self._maybe_await(self.db._get_active_content())
                return [self.db._content_to_track(c) for c in rows]
        except Exception:
            pass
        return []

    def _add_track_ref(self, by_id: dict[str, RekordboxTrackRef], song: Any, playlist: Any | None) -> None:
        tid = str(getattr(song, "id", "") or getattr(song, "track_id", "") or "")
        if not tid:
            return
        ref = by_id.get(tid)
        if ref is None:
            ref = RekordboxTrackRef(
                id=tid,
                artist=str(getattr(song, "artist", "") or ""),
                title=str(getattr(song, "title", "") or ""),
                album=str(getattr(song, "album", "") or ""),
                file_path=str(getattr(song, "file_path", "") or getattr(song, "path", "") or ""),
                playlists=[],
            )
            by_id[tid] = ref
        if playlist is not None:
            pname = str(getattr(playlist, "name", "") or "")
            pid = str(getattr(playlist, "id", "") or "")
            if pname and (pid, pname) not in ref.playlists:
                ref.playlists.append((pid, pname))

    def playlist_names(self) -> list[str]:
        if not self.loaded:
            return []
        return sorted({str(getattr(p, "name", "") or "") for p in self._playlists if getattr(p, "name", "")})

    def find_similar(self, artist: str, title: str, limit: int = 12) -> list[tuple[float, RekordboxTrackRef, str]]:
        if not self.loaded:
            return []
        want_artist = self._norm_artist(artist)
        want_title = self._norm_title(title)
        if not want_title:
            return []

        out: list[tuple[float, RekordboxTrackRef, str]] = []
        for ref in self._tracks:
            got_title = self._norm_title(ref.title)
            got_artist = self._norm_artist(ref.artist)
            if not got_title:
                continue

            title_ratio = SequenceMatcher(None, want_title, got_title).ratio()
            title_tokens = self._token_overlap(want_title, got_title)
            artist_ratio = SequenceMatcher(None, want_artist, got_artist).ratio() if want_artist and got_artist else 0.0
            artist_tokens = self._token_overlap(want_artist, got_artist) if want_artist and got_artist else 0.0
            artist_score = max(artist_ratio, artist_tokens)
            title_score = max(title_ratio, title_tokens)

            # Loose matching: title dominates because artist tags in DJ libraries are messy.
            score = (title_score * 0.78) + (artist_score * 0.22)

            # Still reduce obvious same-title/different-artist collisions, but don't hide them fully.
            if want_artist and got_artist and artist_score < 0.35:
                score -= 0.14

            # Missing artist tags are common. Exact title should still be visible.
            if title_score >= 0.97 and (not got_artist or not want_artist):
                score = max(score, 0.76)

            if score >= self.MIN_MATCH_SCORE:
                strength = "Strong" if score >= 0.90 else "Possible" if score >= 0.76 else "Weak"
                reason = f"{strength}: title={title_score:.2f}, artist={artist_score:.2f}"
                out.append((score, ref, reason))

        out.sort(key=lambda x: x[0], reverse=True)
        return out[:limit]

    def add_track_to_playlist(self, track_id: str, playlist_name: str, create_missing: bool = True) -> tuple[bool, str]:
        if not self.loaded or self.db is None:
            return False, self.error or "Rekordbox database is not loaded"
        playlist_name = (playlist_name or "").strip()
        if not playlist_name:
            return False, "No playlist name supplied"
        try:
            return self._run(self._add_track_to_playlist_async(str(track_id), playlist_name, create_missing))
        except Exception as exc:
            self.error = str(exc)
            return False, str(exc)

    async def _get_or_create_playlist(self, playlist_name: str, create_missing: bool):
        if self.db is None:
            raise RuntimeError("Database not connected")
        key = playlist_name.casefold()
        playlist = self._playlist_by_name.get(key)
        if playlist is None:
            if not create_missing:
                raise RuntimeError(f"Playlist not found: {playlist_name}")
            if not hasattr(self.db, "create_playlist"):
                raise RuntimeError("This RekordboxDatabase wrapper does not expose create_playlist(). Create it manually, then retry.")
            new_id = await self._maybe_await(self.db.create_playlist(playlist_name, parent_id=None, is_folder=False))
            await self._reload_index()
            playlist = self._playlist_by_name.get(key)
            if playlist is None:
                class _Temp:
                    id = new_id
                    name = playlist_name
                playlist = _Temp()
        return playlist

    async def _add_track_to_playlist_async(self, track_id: str, playlist_name: str, create_missing: bool) -> tuple[bool, str]:
        if self.db is None:
            return False, "Database not connected"
        playlist = await self._get_or_create_playlist(playlist_name, create_missing)
        await self._maybe_await(self.db.add_track_to_playlist(playlist.id, track_id))
        await self._reload_index()
        return True, f"Added existing Rekordbox track {track_id} to playlist: {playlist_name}"

    def add_file_to_playlist(self, file_path: str, playlist_name: str, create_missing: bool = True) -> tuple[bool, str]:
        if not self.loaded or self.db is None:
            return False, self.error or "Rekordbox database is not loaded"
        try:
            return self._run(self._add_file_to_playlist_async(str(file_path), playlist_name, create_missing))
        except Exception as exc:
            self.error = str(exc)
            return False, str(exc)

    async def _add_file_to_playlist_async(self, file_path: str, playlist_name: str, create_missing: bool) -> tuple[bool, str]:
        if self.db is None:
            return False, "Database not connected"
        path = str(Path(file_path))
        playlist = await self._get_or_create_playlist(playlist_name, create_missing)

        # If it already exists in our index by path, just add that track id.
        path_key = str(Path(path)).replace("\\", "/").casefold()
        for ref in self._tracks:
            if ref.file_path and str(Path(ref.file_path)).replace("\\", "/").casefold() == path_key:
                await self._maybe_await(self.db.add_track_to_playlist(playlist.id, ref.id))
                await self._reload_index()
                return True, f"Added already-imported Rekordbox track to playlist: {playlist_name}"

        # Try common wrapper method names for importing/adding a file to RB.
        import_method_names = [
            "import_track",
            "add_track",
            "add_file",
            "add_file_to_collection",
            "create_track_from_file",
            "import_file",
        ]
        last_error = None
        new_track = None
        called = None
        for name in import_method_names:
            method = getattr(self.db, name, None)
            if method is None:
                continue
            try:
                called = name
                new_track = await self._maybe_await(method(path))
                break
            except TypeError as exc:
                last_error = exc
                try:
                    new_track = await self._maybe_await(method(file_path=path))
                    called = name
                    break
                except Exception as exc2:
                    last_error = exc2
            except Exception as exc:
                last_error = exc

        if new_track is None:
            return False, (
                "The downloaded file was moved successfully, but I could not automatically import it into Rekordbox. "
                "Your local rekordbox-mcp wrapper does not appear to expose import_track/add_track/add_file. "
                "Import the file in Rekordbox manually, then use the RB assistant to add it to playlists."
                + (f" Last import error: {last_error}" if last_error else "")
            )

        # Extract track id from whatever shape the wrapper returns.
        track_id = None
        if isinstance(new_track, (str, int)):
            track_id = str(new_track)
        elif isinstance(new_track, dict):
            for k in ("id", "track_id", "content_id"):
                if new_track.get(k):
                    track_id = str(new_track[k]); break
        else:
            for k in ("id", "track_id", "content_id"):
                v = getattr(new_track, k, None)
                if v:
                    track_id = str(v); break
        if not track_id:
            await self._reload_index()
            # Try finding by path after import.
            for ref in self._tracks:
                if ref.file_path and str(Path(ref.file_path)).replace("\\", "/").casefold() == path_key:
                    track_id = ref.id
                    break
        if not track_id:
            return False, f"Called db.{called}({path!r}), but could not determine the new Rekordbox track id."

        await self._maybe_await(self.db.add_track_to_playlist(playlist.id, track_id))
        await self._reload_index()
        return True, f"Imported downloaded file and added it to playlist: {playlist_name}"

    @staticmethod
    def _tokens(text: str) -> set[str]:
        return {t for t in text.split() if t}

    @classmethod
    def _token_overlap(cls, a: str, b: str) -> float:
        aa, bb = cls._tokens(a), cls._tokens(b)
        if not aa or not bb:
            return 0.0
        return len(aa & bb) / len(aa | bb)

    @staticmethod
    def _norm_artist(text: str) -> str:
        text = str(text or "").casefold().replace("&", " and ")
        text = re.sub(r"\b(feat|ft|featuring)\b.*", " ", text)
        text = re.sub(r"\b(x|vs|and)\b", " ", text)
        text = re.sub(r"[^a-z0-9]+", " ", text)
        return re.sub(r"\s+", " ", text).strip()

    @staticmethod
    def _norm_title(text: str) -> str:
        text = str(text or "").casefold()
        text = re.sub(r"\([^)]*\)", " ", text)
        text = re.sub(r"\[[^\]]*\]", " ", text)
        removable = [
            r"\bclean\b", r"\bdirty\b", r"\bexplicit\b", r"\bradio edit\b",
            r"\bintro\b", r"\bdj intro\b", r"\bck intro\b", r"\bquick hit\b",
            r"\bextended( mix)?\b", r"\boriginal mix\b", r"\bremix\b", r"\bedit\b",
            r"\bfeat\b.*", r"\bft\b.*", r"\bfeaturing\b.*",
        ]
        for pat in removable:
            text = re.sub(pat, " ", text)
        text = re.sub(r"[^a-z0-9]+", " ", text)
        return re.sub(r"\s+", " ", text).strip()
