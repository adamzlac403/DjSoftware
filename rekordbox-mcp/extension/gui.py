from collections import defaultdict, deque
from pathlib import Path
from difflib import SequenceMatcher
import json
import os
import platform
import re
import subprocess
import time
import urllib.error
import urllib.parse
import urllib.request
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog

try:
    import pygame
    PYGAME_AVAILABLE = True
except Exception:
    pygame = None
    PYGAME_AVAILABLE = False

from rekordbox_mcp.database import RekordboxDatabase


class Gui:
    """
    Rekordbox storage duplicate resolver.

    This version is deliberately stricter than the older fuzzy-title scanner.

    Main idea:
    - Same file in multiple playlists is fine and is ignored.
    - Separate physical files are only grouped when artist + title evidence is strong.
    - Same-title-only collisions such as:
          Justin Timberlake - My Love
          Route 94 - My Love
          Not3s x Mabel - My Love
      should no longer be grouped together.
    - False positives can be marked as NOT duplicates and persist across boots.
    """

    # Pair must be strong enough to become an edge in the duplicate graph.
    TITLE_STRONG = 0.92
    TITLE_EXACTISH = 0.98
    ARTIST_STRONG = 0.80
    ARTIST_MEDIUM = 0.72
    TOKEN_OVERLAP_STRONG = 0.70
    SIZE_TOLERANCE = 0.01  # 1%

    FORMAT_PRIORITY = {
        "flac": 0,
        "aif": 1,
        "aiff": 1,
        "wav": 2,
        "mp3": 3,
    }

    PLAYABLE_EXTENSIONS = {"mp3", "flac", "aif", "aiff", "wav"}
    IGNORE_FILE_NAME = "rekordbox_duplicate_ignores.json"
    MUSICBRAINZ_CACHE_FILE_NAME = "musicbrainz_genre_suggestions_cache.json"
    SORTING_DONE_CACHE_FILE_NAME = "rekordbox_sorted_processed_tracks.json"

    # MusicBrainz asks API users to identify themselves and not exceed 1 request/sec.
    MUSICBRAINZ_USER_AGENT = "rekordbox-sorted-assistant/1.0 (personal-library-tool)"
    MUSICBRAINZ_MIN_REQUEST_INTERVAL = 1.1

    # Public API by default. You can point this at a local mirror later by setting:
    #   set MUSICBRAINZ_BASE_URL=http://localhost:5000/ws/2
    MUSICBRAINZ_BASE_URL = os.environ.get(
        "MUSICBRAINZ_BASE_URL",
        "https://musicbrainz.org/ws/2",
    ).rstrip("/")

    # Convert broad public tags into useful DJ/library buckets.
    # You can freely edit this dictionary to match your own SORTED playlist names.
    MUSICBRAINZ_TAG_TO_PLAYLIST = {
        "house": "House",
        "tech house": "Tech House",
        "deep house": "Deep House",
        "progressive house": "Progressive House",
        "electro house": "Electro House",
        "dance": "Dance",
        "dance-pop": "Pop",
        "pop": "Pop",
        "r&b": "R&B",
        "rnb": "R&B",
        "contemporary r&b": "R&B",
        "hip hop": "Hip Hop",
        "hip-hop": "Hip Hop",
        "rap": "Hip Hop",
        "uk garage": "UK Garage",
        "garage": "Garage",
        "2-step": "UK Garage",
        "drum and bass": "Drum & Bass",
        "drum & bass": "Drum & Bass",
        "dnb": "Drum & Bass",
        "jungle": "Jungle",
        "afrobeats": "Afrobeats",
        "afrobeat": "Afrobeats",
        "amapiano": "Amapiano",
        "dancehall": "Dancehall",
        "reggaeton": "Reggaeton",
        "latin": "Latin",
        "disco": "Disco",
        "funk": "Funk",
        "soul": "Soul",
        "trance": "Trance",
        "techno": "Techno",
        "minimal techno": "Techno",
        "electronic": "Electronic",
        "electronica": "Electronic",
        "edm": "EDM",
        "dubstep": "Dubstep",
        "grime": "Grime",
        "indie": "Indie",
        "indie pop": "Indie",
        "rock": "Rock",
        "alternative rock": "Rock",
        "country": "Country",
        "jazz": "Jazz",
        "blues": "Blues",
        "reggae": "Reggae",
    }

    def __init__(self, db: RekordboxDatabase):
        self.db = db
        self.duplicate_groups = []
        self.current_index = 0
        self.queued_fixes = []
        self.ignored_pairs = set()
        self.ignore_file = self.get_ignore_file_path()
        self.load_ignored_pairs()

        self.musicbrainz_cache_file = self.get_musicbrainz_cache_file_path()
        self.musicbrainz_cache = {}
        self.musicbrainz_last_request_time = 0.0
        self.current_musicbrainz_debug = []
        self.load_musicbrainz_cache()

        self.sorting_done_file = self.get_sorting_done_file_path()
        self.sorting_done_cache = {}
        self.load_sorting_done_cache()
        self.hide_already_sorted_tracks = True

        # Embedded audio preview state. Uses pygame.mixer so playback stays inside
        # this Python/Tkinter process instead of opening Windows Media Player etc.
        self.audio_mixer_ready = False
        self.audio_current_path = None
        self.audio_is_paused = False

    async def startGui(self):
        await self.load_duplicate_groups()

        if self.duplicate_groups:
            self.open_window()

            if self.queued_fixes:
                await self.apply_queued_fixes()
        else:
            print("No storage duplicate groups found; moving straight to library cleanup.")

        # Phase 2: after duplicate review/deletes, offer to clean tracks whose
        # underlying files are missing / empty / no longer resolvable.
        await self.load_broken_library_items()

        if self.has_broken_library_items():
            self.open_library_cleanup_window()

            if getattr(self, "cleanup_apply_requested", False):
                await self.apply_library_cleanup()
        else:
            print("No broken library items found.")

        # Phase 3: after duplicates + broken-library cleanup, open the manual
        # sorting assistant. This creates a SORTED folder if needed, lets you
        # assign each track to one or more playlists/folders under SORTED, and
        # writes the selected playlist names back into the track Genre field.
        await self.prepare_sorting_stage()
        if getattr(self, "sorting_tracks", []):
            self.open_sorting_window()
            if getattr(self, "sorting_apply_requested", False):
                await self.apply_sorting_actions()

    # ------------------------------------------------------------------
    # Persistent false-positive ignore list
    # ------------------------------------------------------------------

    def get_ignore_file_path(self):
        try:
            return Path(__file__).resolve().parent / self.IGNORE_FILE_NAME
        except Exception:
            return Path.cwd() / self.IGNORE_FILE_NAME

    def path_key(self, path):
        return str(Path(path)).replace("\\", "/").casefold()

    def ignore_pair_key(self, path_a, path_b):
        a = self.path_key(path_a)
        b = self.path_key(path_b)
        return tuple(sorted((a, b)))

    def load_ignored_pairs(self):
        self.ignored_pairs = set()

        if not self.ignore_file.exists():
            return

        try:
            data = json.loads(self.ignore_file.read_text(encoding="utf-8"))
            pairs = data.get("ignored_pairs", [])

            for pair in pairs:
                if isinstance(pair, list) and len(pair) == 2:
                    self.ignored_pairs.add(tuple(sorted((pair[0], pair[1]))))

            print(f"Loaded ignored false-positive pairs: {len(self.ignored_pairs)}")
            print(f"Ignore file: {self.ignore_file}")

        except Exception as exc:
            print(f"Could not load ignore file {self.ignore_file}: {exc}")
            self.ignored_pairs = set()

    def save_ignored_pairs(self):
        data = {
            "note": (
                "Pairs of file paths marked as NOT duplicates by the Rekordbox "
                "storage duplicate resolver. Delete this file or use Clear saved ignores "
                "inside the GUI to allow them to appear again."
            ),
            "ignored_pairs": [list(pair) for pair in sorted(self.ignored_pairs)],
        }

        self.ignore_file.write_text(
            json.dumps(data, indent=2, ensure_ascii=False),
            encoding="utf-8"
        )

    def clear_saved_ignores(self):
        confirmed = messagebox.askyesno(
            "Clear saved ignores?",
            "This will clear every pair you previously marked as NOT duplicates.\n\n"
            "Those false-positive groups may appear again next time you scan.\n\n"
            "Continue?"
        )

        if not confirmed:
            return

        self.ignored_pairs.clear()
        self.save_ignored_pairs()
        messagebox.showinfo("Saved ignores cleared", "Saved not-duplicate pairs have been cleared.")

    def paths_are_ignored_together(self, path_a, path_b):
        return self.ignore_pair_key(path_a, path_b) in self.ignored_pairs

    def add_not_duplicate_pairs_for_paths(self, paths):
        paths = sorted(set(paths))
        added = 0

        for i in range(len(paths)):
            for j in range(i + 1, len(paths)):
                key = self.ignore_pair_key(paths[i], paths[j])
                if key not in self.ignored_pairs:
                    self.ignored_pairs.add(key)
                    added += 1

        if added:
            self.save_ignored_pairs()

        return added

    def mark_current_group_not_duplicates(self):
        if not self.duplicate_groups:
            return

        group = self.duplicate_groups[self.current_index]
        added = self.add_not_duplicate_pairs_for_paths(group["paths"])

        print(f"Marked current group as NOT duplicates: {added} new ignored pairs")
        self.remove_current_group_from_scan()

    def mark_unticked_paths_not_duplicates(self):
        if not self.duplicate_groups:
            return

        chosen_path = self.path_var.get()
        unticked_paths = [
            data["path"]
            for data in self.path_vars.values()
            if data["path"] != chosen_path and not data["var"].get()
        ]

        if not unticked_paths:
            messagebox.showinfo(
                "Nothing to save",
                "There are no unticked duplicate paths to mark as NOT duplicates."
            )
            return

        added = 0
        for path in unticked_paths:
            key = self.ignore_pair_key(chosen_path, path)
            if key not in self.ignored_pairs:
                self.ignored_pairs.add(key)
                added += 1

        self.save_ignored_pairs()
        messagebox.showinfo(
            "Saved false positives",
            f"Saved {added} not-duplicate pair(s). They will be ignored in future boots."
        )

        self.filter_current_group_after_ignores()

    def filter_current_group_after_ignores(self):
        if not self.duplicate_groups:
            return

        group = self.duplicate_groups[self.current_index]
        paths = group["paths"]

        remaining_paths = []
        for path in paths:
            has_candidate_pair = any(
                other != path and not self.paths_are_ignored_together(path, other)
                for other in paths
            )
            if has_candidate_pair:
                remaining_paths.append(path)

        if len(set(remaining_paths)) <= 1:
            self.remove_current_group_from_scan()
            return

        allowed_paths = set(remaining_paths)
        group["paths"] = self.sort_paths_by_format_priority(allowed_paths)
        group["default_path"] = group["paths"][0]
        group["entries"] = [entry for entry in group["entries"] if entry["path"] in allowed_paths]
        group["entries_by_path"] = self.rebuild_entries_by_path(group["entries"])
        group["mixed_formats"] = self.has_mixed_formats(group["paths"])
        self.render_group()

    def remove_current_group_from_scan(self):
        if not self.duplicate_groups:
            return

        del self.duplicate_groups[self.current_index]

        if self.current_index >= len(self.duplicate_groups):
            self.current_index = max(0, len(self.duplicate_groups) - 1)

        if self.duplicate_groups:
            self.render_group()
        else:
            self.title_label.config(text="No duplicate groups left")
            for widget in self.path_buttons_frame.winfo_children():
                widget.destroy()
            for widget in self.path_checks_frame.winfo_children():
                widget.destroy()
            self.summary_text.delete("1.0", tk.END)

    # ------------------------------------------------------------------
    # Duplicate scan
    # ------------------------------------------------------------------

    async def load_duplicate_groups(self):
        start_time = time.time()

        print("\n=== STRICT STORAGE DUPLICATE SCAN STARTED ===")
        print(f"Using ignore file: {self.ignore_file}")

        playlists = await self.db.get_playlists()
        print(f"Loaded playlists: {len(playlists)}")

        all_entries = []
        playlist_count = 0

        for playlist in playlists:
            playlist_count += 1
            print(f"[1/4] Reading playlist {playlist_count}/{len(playlists)}: {playlist.name}")

            songs = await self.db.get_playlist_tracks(playlist.id)

            for song in songs:
                if not song.file_path:
                    continue

                title = song.title or ""
                artist = song.artist or ""

                if self.is_extended_mix(title):
                    continue

                normalised_title = self.normalise_title(title)
                if not normalised_title:
                    continue

                path = song.file_path
                all_entries.append({
                    "song": song,
                    "playlist": playlist,
                    "playlist_id": playlist.id,
                    "playlist_name": playlist.name,
                    "path": path,
                    "artist": artist,
                    "title": title,
                    "normalised_artist": self.normalise_artist(artist),
                    "normalised_title": normalised_title,
                    "title_tokens": self.token_set(normalised_title),
                    "version": self.version_flag(title),
                    "file_size": self.file_size_bytes(path),
                    "ext": self.get_extension(path),
                })
        
        with open("track_titles.txt", "w", encoding="utf-8") as f:
            for playlist in playlists:
                songs = await self.db.get_playlist_tracks(playlist.id)

                for song in songs:
                    f.write(f"{song.artist} - {song.title}\n")
        
        print("[1/4] Finished reading playlists")
        print(f"Total candidate playlist entries: {len(all_entries)}")

        # Storage mode: collapse repeated playlist entries pointing at the same physical path.
        entries_by_path = defaultdict(list)
        for entry in all_entries:
            entries_by_path[entry["path"]].append(entry)

        physical_entries = []
        for path, entries in entries_by_path.items():
            rep = self.pick_representative_entry(entries)
            rep = dict(rep)
            rep["all_entries_for_path"] = entries
            physical_entries.append(rep)

        print(f"Unique physical files considered: {len(physical_entries)}")

        buckets = defaultdict(list)
        for entry in physical_entries:
            # Still bucket by title prefix for performance, but final grouping uses strict pair evidence.
            title_key = entry["normalised_title"]
            prefix = title_key[:3] if len(title_key) >= 3 else title_key
            bucket_key = (entry["version"], prefix)
            buckets[bucket_key].append(entry)

        print(f"[2/4] Built buckets: {len(buckets)}")

        total_buckets = len(buckets)
        processed_buckets = 0
        skipped_pairs = 0
        accepted_pairs = 0

        for bucket_name, entries in buckets.items():
            processed_buckets += 1
            if len(entries) <= 1:
                continue

            print(
                f"\n[3/4] Pair checking bucket "
                f"{processed_buckets}/{total_buckets}: {bucket_name!r} "
                f"({len(entries)} physical files)"
            )

            bucket_start = time.time()
            components, bucket_accepted, bucket_skipped = self.make_duplicate_components(entries)
            accepted_pairs += bucket_accepted
            skipped_pairs += bucket_skipped
            bucket_elapsed = time.time() - bucket_start

            print(
                f"[3/4] Bucket {bucket_name!r} produced "
                f"{len(components)} duplicate component(s) in {bucket_elapsed:.2f}s | "
                f"accepted pairs={bucket_accepted}, ignored pairs={bucket_skipped}"
            )

            for component_entries, edge_reasons in components:
                unique_paths = sorted({e["path"] for e in component_entries})

                # Same physical file across many playlists is not a storage duplicate.
                if len(unique_paths) <= 1:
                    continue

                # Rebuild full playlist entries for every path in the component.
                full_entries = []
                for e in component_entries:
                    full_entries.extend(e.get("all_entries_for_path", [e]))

                sorted_paths = self.sort_paths_by_format_priority(unique_paths)
                unique_titles = sorted({e["title"] for e in component_entries})
                unique_artists = sorted({e["artist"] for e in component_entries if e["artist"]})

                entries_by_component_path = defaultdict(list)
                for entry in full_entries:
                    entries_by_component_path[entry["path"]].append(entry)

                self.duplicate_groups.append({
                    "artist": " / ".join(unique_artists) if unique_artists else "Unknown Artist",
                    "title": " / ".join(unique_titles),
                    "entries": full_entries,
                    "entries_by_path": dict(entries_by_component_path),
                    "paths": sorted_paths,
                    "default_path": sorted_paths[0],
                    "mixed_formats": self.has_mixed_formats(unique_paths),
                    "edge_reasons": edge_reasons,
                })

        print("\n[4/4] Sorting duplicate groups")

        self.duplicate_groups.sort(
            key=lambda g: (
                not g["mixed_formats"],
                self.path_priority(g["default_path"]),
                g["title"].lower()
            )
        )

        elapsed = time.time() - start_time

        print("\n=== STRICT STORAGE DUPLICATE SCAN FINISHED ===")
        print(f"Possible storage duplicate groups: {len(self.duplicate_groups)}")
        print(f"Accepted duplicate pairs: {accepted_pairs}")
        print(f"Ignored saved false-positive pairs encountered: {skipped_pairs}")
        print(f"Total scan time: {elapsed:.2f}s")

    def pick_representative_entry(self, entries):
        # Prefer entries with the richest tags for display/comparison.
        return sorted(
            entries,
            key=lambda e: (
                -len(e.get("artist", "")),
                -len(e.get("title", "")),
                str(e.get("playlist_name", "")).lower(),
            )
        )[0]

    def make_duplicate_components(self, entries):
        """
        Build a graph where an edge means "these two physical files are strong duplicate candidates".
        Connected components with 2+ paths become GUI groups.
        """
        n = len(entries)
        adjacency = defaultdict(set)
        edge_reasons_by_pair = {}
        accepted = 0
        skipped_ignored = 0
        comparisons = 0
        last_print = time.time()

        for i in range(n):
            a = entries[i]
            for j in range(i + 1, n):
                b = entries[j]
                comparisons += 1

                if self.paths_are_ignored_together(a["path"], b["path"]):
                    skipped_ignored += 1
                    continue

                reason = self.duplicate_pair_reason(a, b)
                if reason:
                    adjacency[i].add(j)
                    adjacency[j].add(i)
                    edge_reasons_by_pair[(a["path"], b["path"])] = reason
                    accepted += 1

            now = time.time()
            if (i + 1) % 100 == 0 or now - last_print > 5:
                print(
                    f"    Checked {i + 1}/{n} physical files | "
                    f"comparisons={comparisons} | accepted={accepted}"
                )
                last_print = now

        seen = set()
        components = []

        for i in range(n):
            if i in seen or i not in adjacency:
                continue

            q = deque([i])
            seen.add(i)
            component_indexes = []

            while q:
                cur = q.popleft()
                component_indexes.append(cur)
                for nxt in adjacency[cur]:
                    if nxt not in seen:
                        seen.add(nxt)
                        q.append(nxt)

            if len(component_indexes) <= 1:
                continue

            component_entries = [entries[k] for k in component_indexes]
            component_paths = {e["path"] for e in component_entries}
            component_reasons = []

            for (path_a, path_b), reason in edge_reasons_by_pair.items():
                if path_a in component_paths and path_b in component_paths:
                    component_reasons.append(reason)

            components.append((component_entries, component_reasons))

        return components, accepted, skipped_ignored

    def duplicate_pair_reason(self, a, b):
        """
        Return a human-readable reason if two physical files are duplicate candidates.
        Return None if they should not be grouped.

        Important rule: same title alone is not enough.
        """
        if a["path"] == b["path"]:
            return None

        title_ratio = self.similarity(a["normalised_title"], b["normalised_title"])
        token_overlap = self.token_overlap(a["title_tokens"], b["title_tokens"])
        artist_ratio = self.artist_similarity(a["normalised_artist"], b["normalised_artist"])
        size_close = self.sizes_close(a.get("file_size", 0), b.get("file_size", 0))
        same_ext = a.get("ext") == b.get("ext")

        title_ok = title_ratio >= self.TITLE_STRONG and token_overlap >= self.TOKEN_OVERLAP_STRONG
        exact_title = title_ratio >= self.TITLE_EXACTISH and token_overlap >= 0.95
        artist_ok = artist_ratio >= self.ARTIST_STRONG
        artist_medium = artist_ratio >= self.ARTIST_MEDIUM

        # Best case: artist and title strongly agree.
        if title_ok and artist_ok:
            return (
                f"HIGH: title {title_ratio:.2f}, artist {artist_ratio:.2f}, "
                f"token overlap {token_overlap:.2f}"
            )

        # Good storage duplicate signal: same/similar artist+title and file sizes are very close.
        # Useful for mp3/wav/flac copies with tiny naming differences.
        if title_ok and artist_medium and size_close:
            return (
                f"HIGH: title {title_ratio:.2f}, artist {artist_ratio:.2f}, "
                f"file sizes within {self.SIZE_TOLERANCE * 100:.1f}%"
            )

        # Missing artist tags are common. Allow them only when title is basically exact AND size is close.
        if exact_title and size_close and (not a["normalised_artist"] or not b["normalised_artist"]):
            return (
                f"MEDIUM: exact title, missing artist tag, file sizes within "
                f"{self.SIZE_TOLERANCE * 100:.1f}%"
            )

        # Exact title + same extension + very close size + at least some artist agreement.
        if exact_title and same_ext and size_close and artist_ratio >= 0.60:
            return (
                f"MEDIUM: exact title, same format, close size, partial artist {artist_ratio:.2f}"
            )

        return None

    # ------------------------------------------------------------------
    # Normalisation and matching helpers
    # ------------------------------------------------------------------

    def sort_paths_by_format_priority(self, paths):
        return sorted(
            paths,
            key=lambda path: (
                self.path_priority(path),
                -self.file_size_bytes(path),
                path.lower()
            )
        )

    def path_priority(self, path):
        ext = self.get_extension(path)
        return self.FORMAT_PRIORITY.get(ext, 99)

    def similarity(self, a, b):
        if not a or not b:
            return 1.0 if a == b else 0.0
        return SequenceMatcher(None, a, b).ratio()

    def token_set(self, text):
        return {token for token in text.split() if token}

    def token_overlap(self, tokens_a, tokens_b):
        if not tokens_a or not tokens_b:
            return 1.0 if tokens_a == tokens_b else 0.0
        return len(tokens_a & tokens_b) / len(tokens_a | tokens_b)

    def artist_similarity(self, artist_a, artist_b):
        if not artist_a or not artist_b:
            return 0.0

        if artist_a == artist_b:
            return 1.0

        tokens_a = self.token_set(artist_a)
        tokens_b = self.token_set(artist_b)

        # JT / Justin Timberlake aliases etc are handled before here, but token overlap
        # helps with "calvin harris" vs "calvin harris dua lipa" style tags.
        ratio = SequenceMatcher(None, artist_a, artist_b).ratio()
        overlap = self.token_overlap(tokens_a, tokens_b)
        return max(ratio, overlap)

    def sizes_close(self, size_a, size_b):
        if not size_a or not size_b:
            return False
        larger = max(size_a, size_b)
        smaller = min(size_a, size_b)
        return (larger - smaller) / larger <= self.SIZE_TOLERANCE

    def normalise_artist(self, artist):
        artist = artist.lower()

        aliases = {
            "justin timberlake": "jt",
            "j timberlake": "jt",
            "timbaland": "timbaland",
        }

        artist = artist.replace("&", ",")
        artist = artist.replace(" x ", ",")
        artist = artist.replace(" vs ", ",")
        artist = artist.replace(" and ", ",")

        artist = re.sub(r"\bfeat\.?\b.*", "", artist)
        artist = re.sub(r"\bft\.?\b.*", "", artist)
        artist = re.sub(r"\bfeaturing\b.*", "", artist)

        artist = artist.split(",")[0]
        artist = re.sub(r"[^a-z0-9 ]", " ", artist)
        artist = re.sub(r"\s+", " ", artist).strip()

        return aliases.get(artist, artist)

    def is_extended_mix(self, title):
        title = title.lower()
        return bool(re.search(r"\b(extended|extended mix|club mix|12 inch|12\" mix)\b", title))

    def version_flag(self, title):
        title = title.lower()

        if re.search(r"\bclean\b", title):
            return "clean"

        if re.search(r"\b(dirty|explicit)\b", title):
            return "dirty"

        if re.search(r"\b(intro|ck intro|dj intro|quick hit|short edit)\b", title):
            return "intro"

        return "normal"

    def normalise_title(self, title):
        title = title.lower()

        title = re.sub(r"\([^)]*\b(ft|feat|featuring)\.?\b[^)]*\)", " ", title)
        title = re.sub(r"\[[^\]]*\b(ft|feat|featuring)\.?\b[^\]]*\]", " ", title)
        title = re.sub(r"\([^)]*\bintro\b[^)]*\)", " ", title)
        title = re.sub(r"\[[^\]]*\bintro\b[^\]]*\]", " ", title)

        removable = [
            r"\bck intro\b",
            r"\bdj intro\b",
            r"\bdirty intro\b",
            r"\bclean intro\b",
            r"\bintro dirty\b",
            r"\bintro clean\b",
            r"\bintro\b",
            r"\bdj\s+\w+\b",
            r"\bradio edit\b",
            r"\boriginal mix\b",
            r"\bremaster(ed)?\b",
            r"\bfeat\.?\b.*",
            r"\bft\.?\b.*",
            r"\bfeaturing\b.*",
            r"\bedit\b",
            r"\bremix\b",
            r"\bremastered\b",
        ]

        title = re.sub(r"[\[\]\(\)_\-]", " ", title)

        for pattern in removable:
            title = re.sub(pattern, " ", title)

        title = re.sub(r"[^a-z0-9 ]", " ", title)
        title = re.sub(r"\s+", " ", title).strip()

        return title

    def get_extension(self, path):
        return Path(path).suffix.lower().replace(".", "")

    def has_mixed_formats(self, paths):
        return len({self.get_extension(path) for path in paths}) > 1

    # ------------------------------------------------------------------
    # GUI
    # ------------------------------------------------------------------

    def open_window(self):
        self.root = tk.Tk()
        self.root.title("Rekordbox Strict Storage Duplicate Resolver")
        self.root.geometry("1350x900")

        self.path_var = tk.StringVar()
        self.path_vars = {}

        self.title_label = ttk.Label(self.root, text="", font=("Arial", 16, "bold"))
        self.title_label.pack(pady=10)

        help_label = ttk.Label(
            self.root,
            text=(
                "Strict storage mode: same-title-only artist collisions are blocked. "
                "Choose one physical file to keep, tick other physical files to delete. "
                "Unticked files are left alone and can be saved as NOT duplicates."
            )
        )
        help_label.pack(pady=(0, 5))

        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill="both", expand=True, padx=10, pady=5)

        keep_frame = ttk.LabelFrame(main_frame, text="1) Choose the physical file to KEEP")
        keep_frame.pack(side="left", fill="both", expand=True, padx=5)

        remove_frame = ttk.LabelFrame(main_frame, text="2) Tick physical files to REMOVE from playlists and DELETE from disk")
        remove_frame.pack(side="right", fill="both", expand=True, padx=5)

        self.path_buttons_frame = ttk.Frame(keep_frame)
        self.path_buttons_frame.pack(fill="both", expand=True, padx=10, pady=10)

        self.path_canvas = tk.Canvas(remove_frame, height=250)
        self.path_scrollbar = ttk.Scrollbar(remove_frame, orient="vertical", command=self.path_canvas.yview)
        self.path_checks_frame = ttk.Frame(self.path_canvas)

        self.path_checks_frame.bind(
            "<Configure>",
            lambda event: self.path_canvas.configure(scrollregion=self.path_canvas.bbox("all"))
        )

        self.path_canvas_window = self.path_canvas.create_window(
            (0, 0),
            window=self.path_checks_frame,
            anchor="nw"
        )
        self.path_canvas.configure(yscrollcommand=self.path_scrollbar.set)

        self.path_canvas.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=5)
        self.path_scrollbar.pack(side="right", fill="y", padx=(0, 10), pady=5)
        self.path_canvas.bind(
            "<Configure>",
            lambda event: self.path_canvas.itemconfigure(self.path_canvas_window, width=event.width)
        )

        self.summary_text = tk.Text(self.root, height=17)
        self.summary_text.pack(fill="x", padx=10, pady=10)

        bottom_frame = ttk.Frame(self.root)
        bottom_frame.pack(fill="x", padx=10, pady=10)

        ttk.Button(bottom_frame, text="Previous", command=self.previous_group).pack(side="left")

        ttk.Button(
            bottom_frame,
            text="Next / Skip",
            command=self.next_group_without_queue
        ).pack(side="left", padx=5)

        ttk.Button(
            bottom_frame,
            text="Queue delete ticked files + Next",
            command=self.queue_fix_and_next
        ).pack(side="left", padx=5)

        ttk.Button(
            bottom_frame,
            text="Save unticked as NOT duplicates",
            command=self.mark_unticked_paths_not_duplicates
        ).pack(side="left", padx=5)

        ttk.Button(
            bottom_frame,
            text="Mark whole group NOT duplicates",
            command=self.mark_current_group_not_duplicates
        ).pack(side="left", padx=5)

        ttk.Button(
            bottom_frame,
            text="Clear saved ignores",
            command=self.clear_saved_ignores
        ).pack(side="left", padx=5)

        ttk.Button(
            bottom_frame,
            text="Finish and apply queued deletes",
            command=self.finish
        ).pack(side="right", padx=5)

        self.render_group()
        self.root.mainloop()

    def render_group(self):
        for widget in self.path_buttons_frame.winfo_children():
            widget.destroy()

        for widget in self.path_checks_frame.winfo_children():
            widget.destroy()

        self.path_vars.clear()
        self.summary_text.delete("1.0", tk.END)

        if not self.duplicate_groups:
            self.title_label.config(text="No strict storage duplicate groups found")
            return

        group = self.duplicate_groups[self.current_index]
        group["entries_by_path"] = self.rebuild_entries_by_path(group["entries"])
        format_label = "MIXED FORMATS" if group["mixed_formats"] else "same format"

        self.title_label.config(
            text=f"{self.current_index + 1}/{len(self.duplicate_groups)}: "
                 f"{group['artist']} - {group['title']} [{format_label}]"
        )

        self.path_var.set(group["default_path"])

        for path in group["paths"]:
            ext = self.get_extension(path).upper()
            priority_marker = "  ★ default" if path == group["default_path"] else ""
            file_info = self.file_size_label(path)
            playlist_count = len({e["playlist_id"] for e in group["entries_by_path"].get(path, [])})

            row = ttk.Frame(self.path_buttons_frame)
            row.pack(fill="x", anchor="w", pady=3)

            ttk.Radiobutton(
                row,
                text=f"[{ext}] {file_info} | in {playlist_count} playlist(s) | {path}{priority_marker}",
                variable=self.path_var,
                value=path,
                command=self.on_keep_path_changed
            ).pack(side="left", anchor="w", fill="x", expand=True)

            ttk.Button(
                row,
                text="Play",
                command=lambda p=path: self.play_audio_file(p)
            ).pack(side="right", padx=5)

        self.render_path_checkboxes()
        self.render_summary()

    def rebuild_entries_by_path(self, entries):
        result = defaultdict(list)
        for entry in entries:
            result[entry["path"]].append(entry)
        return dict(result)

    def render_path_checkboxes(self):
        for widget in self.path_checks_frame.winfo_children():
            widget.destroy()

        self.path_vars.clear()

        group = self.duplicate_groups[self.current_index]
        chosen_path = self.path_var.get()

        for index, path in enumerate(group["paths"]):
            is_chosen = path == chosen_path
            var = tk.BooleanVar(value=False)

            self.path_vars[index] = {
                "var": var,
                "path": path,
            }

            ext = self.get_extension(path).upper()
            file_info = self.file_size_label(path)
            entries = group["entries_by_path"].get(path, [])
            playlists = sorted({entry["playlist_name"] for entry in entries})
            playlist_label = ", ".join(playlists[:6])
            if len(playlists) > 6:
                playlist_label += f", +{len(playlists) - 6} more"

            row = ttk.Frame(self.path_checks_frame)
            row.pack(fill="x", anchor="w", pady=2)

            check = ttk.Checkbutton(
                row,
                text=f"[{ext}] {file_info} | {path} | playlists: {playlist_label}",
                variable=var,
                command=self.render_summary
            )
            check.pack(side="left", anchor="w", fill="x", expand=True)

            ttk.Button(
                row,
                text="Play",
                command=lambda p=path: self.play_audio_file(p)
            ).pack(side="right", padx=5)

            if is_chosen:
                check.state(["disabled"])

    def on_keep_path_changed(self):
        self.render_path_checkboxes()
        self.render_summary()

    def render_summary(self):
        self.summary_text.delete("1.0", tk.END)

        if not self.duplicate_groups:
            return

        group = self.duplicate_groups[self.current_index]
        chosen_path = self.path_var.get()

        selected_duplicate_paths = [
            data["path"]
            for data in self.path_vars.values()
            if data["var"].get() and data["path"] != chosen_path
        ]

        selected_duplicate_set = set(selected_duplicate_paths)
        bytes_to_delete = sum(self.file_size_bytes(path) for path in selected_duplicate_set)

        self.summary_text.insert(tk.END, f"Chosen keep file:\n{chosen_path}\n\n")
        self.summary_text.insert(
            tk.END,
            "Tick means DELETE THIS PHYSICAL FILE after removing its playlist references.\n"
            "Unticked means leave it alone. Use the not-duplicate buttons to persistently hide false positives.\n"
            "The scanner now requires title + artist evidence; same title alone is blocked.\n\n"
        )

        reasons = group.get("edge_reasons", [])[:6]
        if reasons:
            self.summary_text.insert(tk.END, "Why this group appeared:\n")
            for reason in reasons:
                self.summary_text.insert(tk.END, f"  - {reason}\n")
            if len(group.get("edge_reasons", [])) > 6:
                self.summary_text.insert(tk.END, f"  - +{len(group['edge_reasons']) - 6} more pair reason(s)\n")
            self.summary_text.insert(tk.END, "\n")

        for path in group["paths"]:
            entries = group["entries_by_path"].get(path, [])
            playlists = sorted({entry["playlist_name"] for entry in entries})

            if path == chosen_path:
                marker = "KEEP FILE"
            elif path in selected_duplicate_set:
                marker = "DELETE FILE + REMOVE FROM ALL LISTED PLAYLISTS"
            else:
                marker = "LEAVE ALONE"

            self.summary_text.insert(
                tk.END,
                f"[{marker}] {self.file_size_label(path)} | {path}\n"
                f"    Playlist refs found here: {', '.join(playlists)}\n"
            )

        self.summary_text.insert(
            tk.END,
            f"\nPhysical files ticked for deletion: {len(selected_duplicate_set)}\n"
            f"Estimated storage saved: {self.human_size(bytes_to_delete)}\n"
            f"Saved not-duplicate pairs loaded: {len(self.ignored_pairs)}\n"
        )

    def queue_current_fix(self):
        group = self.duplicate_groups[self.current_index]
        chosen_path = self.path_var.get()

        canonical_entries = [
            e for e in group["entries"]
            if e["path"] == chosen_path
        ]

        if not canonical_entries:
            print("Error: Could not find selected canonical track.")
            return False

        canonical_song = canonical_entries[0]["song"]

        selected_duplicate_paths = [
            data["path"]
            for data in self.path_vars.values()
            if data["var"].get() and data["path"] != chosen_path
        ]

        if not selected_duplicate_paths:
            messagebox.showinfo(
                "Nothing queued",
                "No duplicate physical files are ticked for deletion."
            )
            return False

        selected_duplicate_set = set(selected_duplicate_paths)
        selected_duplicate_entries = [
            entry for entry in group["entries"]
            if entry["path"] in selected_duplicate_set
        ]

        affected_playlist_ids = {entry["playlist_id"] for entry in selected_duplicate_entries}
        playlists_needing_canonical = set()

        for playlist_id in affected_playlist_ids:
            already_has_chosen = any(
                entry["playlist_id"] == playlist_id and entry["path"] == chosen_path
                for entry in group["entries"]
            )
            if not already_has_chosen:
                playlists_needing_canonical.add(playlist_id)

        self.queued_fixes = [
            fix for fix in self.queued_fixes
            if fix["group"] is not group
        ]

        self.queued_fixes.append({
            "group": group,
            "chosen_path": chosen_path,
            "canonical_song": canonical_song,
            "selected_duplicate_paths": selected_duplicate_set,
            "selected_duplicate_entries": selected_duplicate_entries,
            "playlists_needing_canonical": playlists_needing_canonical,
        })

        bytes_to_delete = sum(self.file_size_bytes(path) for path in selected_duplicate_set)

        print(f"Queued storage fix for: {group['artist']} - {group['title']}")
        print(f"  Keeping: {chosen_path}")
        print(f"  Physical files to delete: {len(selected_duplicate_set)}")
        print(f"  Estimated storage saved: {self.human_size(bytes_to_delete)}")
        return True

    def queue_fix_and_next(self):
        queued = self.queue_current_fix()
        if queued:
            self.next_group_without_queue()

    def next_group_without_queue(self):
        if self.current_index < len(self.duplicate_groups) - 1:
            self.current_index += 1
            self.render_group()

    def previous_group(self):
        if self.current_index > 0:
            self.current_index -= 1
            self.render_group()

    # ------------------------------------------------------------------
    # Apply fixes
    # ------------------------------------------------------------------

    async def apply_queued_fixes(self):
        for fix in self.queued_fixes:
            group = fix["group"]
            chosen_path = fix["chosen_path"]
            canonical_song = fix["canonical_song"]
            selected_duplicate_paths = fix["selected_duplicate_paths"]
            selected_duplicate_entries = fix["selected_duplicate_entries"]
            playlists_needing_canonical = fix["playlists_needing_canonical"]

            print(f"\nApplying storage fix for: {group['artist']} - {group['title']}")
            print(f"Keeping: {chosen_path}")
            print(f"Physical duplicate files to delete: {len(selected_duplicate_paths)}")

            playlists_by_id = {
                entry["playlist_id"]: entry["playlist"]
                for entry in group["entries"]
            }

            for playlist_id in playlists_needing_canonical:
                playlist = playlists_by_id[playlist_id]
                print(f"Adding chosen version to playlist before removing duplicate: {playlist.name}")
                await self.db.add_track_to_playlist(playlist.id, canonical_song.id)

            for entry in selected_duplicate_entries:
                playlist = entry["playlist"]
                song = entry["song"]

                print(f"Removing duplicate playlist ref from {playlist.name}: {entry['path']}")

                await self.db.remove_track_from_playlist_by_content(
                    playlist.id,
                    song.id
                )

            for old_path in selected_duplicate_paths:
                self.delete_file(old_path)

    def delete_file(self, old_path):
        src = Path(old_path)

        if not src.exists():
            print(f"File already missing, cannot delete: {old_path}")
            return

        print(f"PERMANENTLY deleting duplicate physical file: {src}")
        src.unlink()


    # ------------------------------------------------------------------
    # Phase 2: Library cleanup for missing / unresolved files
    # ------------------------------------------------------------------

    async def load_broken_library_items(self):
        """
        Loads broken library information using rekordbox-mcp cleanup helpers.

        Expected db method, if available:
            await db.find_broken_tracks()

        The current rekordbox-mcp README lists these cleanup operations:
        - find_broken_tracks
        - cleanup_orphaned_playlist_entries
        - remove_broken_tracks

        This wrapper is deliberately tolerant because return shapes can differ
        between local versions of the MCP/database wrapper.
        """
        self.broken_library_raw = None
        self.broken_library_sections = {
            "missing_files": [],
            "empty_paths": [],
            "apple_music_streams": [],
            "orphaned_playlist_refs": [],
            "other": [],
        }
        self.cleanup_track_vars = {}
        self.cleanup_orphan_refs_var = None
        self.cleanup_apply_requested = False

        print("\n=== LIBRARY CLEANUP SCAN STARTED ===")

        if not hasattr(self.db, "find_broken_tracks"):
            print("db.find_broken_tracks() is not available in this local RekordboxDatabase wrapper.")
            print("Update rekordbox-mcp or wire the wrapper method name inside load_broken_library_items().")
            return

        try:
            result = self.db.find_broken_tracks()
            if hasattr(result, "__await__"):
                result = await result

            self.broken_library_raw = result
            self.broken_library_sections = self.normalise_broken_tracks_result(result)

            total = sum(len(items) for items in self.broken_library_sections.values())
            print(f"Broken library items found: {total}")
            for name, items in self.broken_library_sections.items():
                print(f"  {name}: {len(items)}")

        except Exception as exc:
            print(f"Could not run find_broken_tracks(): {exc}")
            self.broken_library_raw = None

    def normalise_broken_tracks_result(self, result):
        sections = {
            "missing_files": [],
            "empty_paths": [],
            "apple_music_streams": [],
            "orphaned_playlist_refs": [],
            "other": [],
        }

        if result is None:
            return sections

        if isinstance(result, dict):
            key_aliases = {
                "missing_files": ["missing_files", "missing", "missing_tracks", "file_missing"],
                "empty_paths": ["empty_paths", "empty_path_tracks", "empty_file_paths"],
                "apple_music_streams": ["apple_music_streams", "apple_music", "streaming_tracks"],
                "orphaned_playlist_refs": ["orphaned_playlist_refs", "orphaned_playlist_entries", "orphaned_refs"],
            }

            used_keys = set()
            for section, aliases in key_aliases.items():
                for key in aliases:
                    if key in result and isinstance(result[key], list):
                        sections[section].extend(result[key])
                        used_keys.add(key)

            # If the tool returns a flat track list under a generic key.
            for key in ["tracks", "broken_tracks", "items", "results"]:
                if key in result and isinstance(result[key], list):
                    for item in result[key]:
                        sections[self.classify_broken_item(item)].append(item)
                    used_keys.add(key)

            # Preserve unexpected lists rather than hiding them.
            for key, value in result.items():
                if key not in used_keys and isinstance(value, list):
                    for item in value:
                        wrapped = item
                        if isinstance(item, dict):
                            wrapped = dict(item)
                            wrapped.setdefault("source_section", key)
                        sections["other"].append(wrapped)

            return sections

        if isinstance(result, list):
            for item in result:
                sections[self.classify_broken_item(item)].append(item)

        return sections

    def classify_broken_item(self, item):
        text = self.item_text(item).casefold()

        if "orphan" in text or "playlist" in text and "ref" in text:
            return "orphaned_playlist_refs"
        if "apple" in text or "stream" in text:
            return "apple_music_streams"
        if "empty" in text or "blank" in text:
            return "empty_paths"
        if "missing" in text or "not found" in text or "does not exist" in text:
            return "missing_files"

        path = self.extract_item_path(item)
        if path == "":
            return "empty_paths"
        if path and not Path(path).exists():
            return "missing_files"

        return "other"

    def item_text(self, item):
        if isinstance(item, dict):
            return " | ".join(f"{k}: {v}" for k, v in item.items())
        return str(item)

    def extract_item_track_id(self, item):
        if isinstance(item, dict):
            for key in ["track_id", "id", "content_id", "song_id", "TrackID", "ID"]:
                value = item.get(key)
                if value not in [None, ""]:
                    return value
        else:
            for key in ["track_id", "id", "content_id", "song_id"]:
                value = getattr(item, key, None)
                if value not in [None, ""]:
                    return value
        return None

    def extract_item_path(self, item):
        if isinstance(item, dict):
            for key in ["file_path", "path", "location", "filepath", "FilePath", "Location"]:
                if key in item:
                    value = item.get(key)
                    return "" if value is None else str(value)
        else:
            for key in ["file_path", "path", "location", "filepath"]:
                if hasattr(item, key):
                    value = getattr(item, key)
                    return "" if value is None else str(value)
        return None

    def has_broken_library_items(self):
        return any(len(items) > 0 for items in getattr(self, "broken_library_sections", {}).values())

    def open_library_cleanup_window(self):
        self.cleanup_root = tk.Tk()
        self.cleanup_root.title("Rekordbox Library Cleanup")
        self.cleanup_root.geometry("1250x850")

        title = ttk.Label(
            self.cleanup_root,
            text="Library Cleanup: missing files, empty paths, Apple Music streams, orphaned playlist refs",
            font=("Arial", 15, "bold")
        )
        title.pack(pady=10)

        help_label = ttk.Label(
            self.cleanup_root,
            text=(
                "Default selection removes missing-file and empty-path tracks. "
                "Apple Music streams are shown but left unticked. Orphaned playlist refs can be cleaned separately."
            )
        )
        help_label.pack(pady=(0, 5))

        top_frame = ttk.Frame(self.cleanup_root)
        top_frame.pack(fill="both", expand=True, padx=10, pady=5)

        canvas = tk.Canvas(top_frame)
        scrollbar = ttk.Scrollbar(top_frame, orient="vertical", command=canvas.yview)
        self.cleanup_checks_frame = ttk.Frame(canvas)

        self.cleanup_checks_frame.bind(
            "<Configure>",
            lambda event: canvas.configure(scrollregion=canvas.bbox("all"))
        )

        canvas_window = canvas.create_window((0, 0), window=self.cleanup_checks_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        canvas.bind("<Configure>", lambda event: canvas.itemconfigure(canvas_window, width=event.width))

        self.cleanup_track_vars = {}
        self.render_cleanup_items()

        self.cleanup_summary_text = tk.Text(self.cleanup_root, height=10)
        self.cleanup_summary_text.pack(fill="x", padx=10, pady=10)

        bottom = ttk.Frame(self.cleanup_root)
        bottom.pack(fill="x", padx=10, pady=10)

        ttk.Button(bottom, text="Select missing + empty", command=self.cleanup_select_missing_empty).pack(side="left", padx=5)
        ttk.Button(bottom, text="Select all non-orphan tracks", command=self.cleanup_select_all_tracks).pack(side="left", padx=5)
        ttk.Button(bottom, text="Select none", command=self.cleanup_select_none).pack(side="left", padx=5)
        ttk.Button(bottom, text="Refresh summary", command=self.render_cleanup_summary).pack(side="left", padx=5)

        ttk.Button(bottom, text="Skip cleanup", command=self.cleanup_skip).pack(side="right", padx=5)
        ttk.Button(bottom, text="Apply selected cleanup", command=self.cleanup_apply_and_close).pack(side="right", padx=5)

        self.render_cleanup_summary()
        self.cleanup_root.mainloop()

    def render_cleanup_items(self):
        section_labels = {
            "missing_files": "Missing local files — selected by default",
            "empty_paths": "Empty file paths — selected by default",
            "apple_music_streams": "Apple Music / streaming refs — not selected by default",
            "orphaned_playlist_refs": "Orphaned playlist references — cleaned by separate operation",
            "other": "Other suspicious items — not selected by default",
        }

        counter = 0
        for section, label in section_labels.items():
            items = self.broken_library_sections.get(section, [])
            if not items:
                continue

            frame = ttk.LabelFrame(self.cleanup_checks_frame, text=f"{label} ({len(items)})")
            frame.pack(fill="x", expand=True, padx=5, pady=6)

            if section == "orphaned_playlist_refs":
                self.cleanup_orphan_refs_var = tk.BooleanVar(value=True)
                ttk.Checkbutton(
                    frame,
                    text=(
                        "Run cleanup_orphaned_playlist_entries() to remove stale playlist entries "
                        "that point at already-deleted/nonexistent tracks"
                    ),
                    variable=self.cleanup_orphan_refs_var,
                    command=self.render_cleanup_summary
                ).pack(anchor="w", padx=8, pady=4)

                sample_text = tk.Text(frame, height=min(6, max(2, len(items))), wrap="none")
                sample_text.pack(fill="x", padx=8, pady=4)
                for item in items[:50]:
                    sample_text.insert(tk.END, f"{self.item_text(item)}\n")
                sample_text.configure(state="disabled")
                continue

            default_selected = section in {"missing_files", "empty_paths"}
            for item in items:
                track_id = self.extract_item_track_id(item)
                path = self.extract_item_path(item)
                var = tk.BooleanVar(value=default_selected and track_id is not None)

                self.cleanup_track_vars[counter] = {
                    "var": var,
                    "item": item,
                    "section": section,
                    "track_id": track_id,
                }

                row = ttk.Frame(frame)
                row.pack(fill="x", anchor="w", padx=4, pady=2)

                label_text = self.cleanup_item_label(item, section, track_id, path)
                chk = ttk.Checkbutton(row, text=label_text, variable=var, command=self.render_cleanup_summary)
                chk.pack(side="left", fill="x", expand=True, anchor="w")

                if track_id is None:
                    chk.state(["disabled"])

                counter += 1

    def cleanup_item_label(self, item, section, track_id, path):
        if isinstance(item, dict):
            artist = item.get("artist") or item.get("Artist") or ""
            title = item.get("title") or item.get("Title") or ""
            reason = item.get("reason") or item.get("status") or section
            bits = []
            if track_id is not None:
                bits.append(f"ID {track_id}")
            if artist or title:
                bits.append(f"{artist} - {title}".strip(" -"))
            if path is not None:
                bits.append(f"path={path!r}")
            bits.append(f"reason={reason}")
            return " | ".join(bits)

        return f"ID {track_id} | {self.item_text(item)}" if track_id is not None else self.item_text(item)

    def selected_cleanup_track_ids(self):
        ids = []
        for data in self.cleanup_track_vars.values():
            if data["var"].get() and data["track_id"] is not None:
                ids.append(data["track_id"])
        return ids

    def render_cleanup_summary(self):
        if not hasattr(self, "cleanup_summary_text"):
            return

        self.cleanup_summary_text.delete("1.0", tk.END)
        ids = self.selected_cleanup_track_ids()
        orphan = bool(self.cleanup_orphan_refs_var and self.cleanup_orphan_refs_var.get())

        counts_by_section = defaultdict(int)
        for data in self.cleanup_track_vars.values():
            if data["var"].get():
                counts_by_section[data["section"]] += 1

        self.cleanup_summary_text.insert(tk.END, "Selected cleanup actions:\n\n")
        self.cleanup_summary_text.insert(tk.END, f"Tracks to soft-delete/remove from playlists: {len(ids)}\n")
        for section, count in sorted(counts_by_section.items()):
            self.cleanup_summary_text.insert(tk.END, f"  {section}: {count}\n")
        self.cleanup_summary_text.insert(tk.END, f"Run orphaned playlist cleanup: {orphan}\n\n")
        self.cleanup_summary_text.insert(
            tk.END,
            "remove_broken_tracks should soft-delete selected track IDs and remove them from playlists. "
            "cleanup_orphaned_playlist_entries removes stale playlist rows that reference deleted tracks.\n"
        )

    def cleanup_select_missing_empty(self):
        for data in self.cleanup_track_vars.values():
            data["var"].set(data["section"] in {"missing_files", "empty_paths"} and data["track_id"] is not None)
        self.render_cleanup_summary()

    def cleanup_select_all_tracks(self):
        for data in self.cleanup_track_vars.values():
            data["var"].set(data["track_id"] is not None)
        self.render_cleanup_summary()

    def cleanup_select_none(self):
        for data in self.cleanup_track_vars.values():
            data["var"].set(False)
        if self.cleanup_orphan_refs_var:
            self.cleanup_orphan_refs_var.set(False)
        self.render_cleanup_summary()

    def cleanup_skip(self):
        self.cleanup_apply_requested = False
        self.cleanup_root.destroy()

    def cleanup_apply_and_close(self):
        ids = self.selected_cleanup_track_ids()
        orphan = bool(self.cleanup_orphan_refs_var and self.cleanup_orphan_refs_var.get())

        if not ids and not orphan:
            messagebox.showinfo("Nothing selected", "No cleanup actions are selected.")
            return

        confirmed = messagebox.askyesno(
            "Apply library cleanup?",
            "This will mutate your Rekordbox database.\n\n"
            f"Tracks selected for broken-track removal: {len(ids)}\n"
            f"Run orphaned playlist cleanup: {orphan}\n\n"
            "This should NOT delete audio files from disk. It removes/soft-deletes "
            "broken Rekordbox library records and playlist references.\n\n"
            "Close Rekordbox and make a backup first.\n\n"
            "Continue?"
        )

        if confirmed:
            # Copy values out of Tk variables before destroying the Tk window.
            # Otherwise the apply phase can read stale/invalid widget state.
            self.cleanup_ids_to_apply = list(ids)
            self.cleanup_orphan_to_apply = bool(orphan)
            self.cleanup_apply_requested = True
            self.cleanup_root.destroy()

    async def apply_library_cleanup(self):
        ids = list(getattr(self, "cleanup_ids_to_apply", self.selected_cleanup_track_ids()))
        orphan = bool(getattr(self, "cleanup_orphan_to_apply", False))

        print("\n=== APPLYING LIBRARY CLEANUP ===")
        print(f"Track IDs selected for broken-track removal: {len(ids)}")
        print(f"Cleanup orphaned playlist refs: {orphan}")

        orphan_result = None
        tracks_result = None

        if orphan:
            orphan_result = await self.call_first_available_async(
                [
                    "cleanup_orphaned_playlist_entries",  # README/server tool name
                    "remove_orphaned_playlist_entries",   # actual method name in your pasted database.py
                ]
            )
            print(f"Orphan playlist cleanup result: {orphan_result}")

        if ids:
            tracks_result = await self.call_first_available_async(
                [
                    "remove_broken_tracks",   # README/server tool name
                    "remove_tracks_by_ids",   # actual method name in your pasted database.py
                ],
                ids,
                named_arg_fallback={"track_ids": ids},
            )
            print(f"Broken-track removal result: {tracks_result}")

        # Force the wrapper cache to refresh if the local wrapper exposes the helper.
        self.save_sorting_done_cache()

        if hasattr(self.db, "_invalidate_content_cache"):
            try:
                self.db._invalidate_content_cache()
            except Exception:
                pass

        # Immediately rescan so the console tells you whether the database actually changed.
        before_counts = {}
        try:
            before_counts = {
                key: len(value)
                for key, value in getattr(self, "broken_library_sections", {}).items()
            }
        except Exception:
            pass

        await self.load_broken_library_items()

        after_counts = {
            key: len(value)
            for key, value in getattr(self, "broken_library_sections", {}).items()
        }

        print("Cleanup scan counts before apply:", before_counts)
        print("Cleanup scan counts after apply:", after_counts)
        print("=== LIBRARY CLEANUP FINISHED ===")

        messagebox.showinfo(
            "Cleanup finished",
            "Library cleanup finished.\n\n"
            f"Track IDs requested: {len(ids)}\n"
            f"Orphan cleanup requested: {orphan}\n\n"
            "The library was rescanned after applying. Check the terminal output for before/after counts."
        )

    async def call_first_available_async(self, method_names, *args, named_arg_fallback=None):
        """
        Call the first cleanup method that exists on the connected RekordboxDatabase.

        This matters because the README/tool names and the actual Python wrapper
        methods can differ. For your pasted database.py, the real names are:
        - remove_orphaned_playlist_entries()
        - remove_tracks_by_ids(track_ids)
        """
        last_error = None

        for name in method_names:
            method = getattr(self.db, name, None)
            if method is None:
                print(f"db.{name}() is not available; trying next name if any.")
                continue

            try:
                print(f"Calling db.{name}()")
                result = method(*args)
                if hasattr(result, "__await__"):
                    result = await result
                return {"called": name, "result": result}
            except TypeError as exc:
                last_error = exc
                if named_arg_fallback is not None:
                    try:
                        print(f"Retrying db.{name}() with named args {list(named_arg_fallback.keys())}")
                        result = method(**named_arg_fallback)
                        if hasattr(result, "__await__"):
                            result = await result
                        return {"called": name, "result": result}
                    except Exception as retry_exc:
                        last_error = retry_exc
                print(f"db.{name}() failed: {last_error}")
            except Exception as exc:
                last_error = exc
                print(f"db.{name}() failed: {exc}")

        return {
            "called": None,
            "error": str(last_error) if last_error else "No compatible cleanup method found on db wrapper",
            "tried": method_names,
        }


    # ------------------------------------------------------------------
    # Phase 3: Manual SORTED playlist assignment + genre tagging
    # ------------------------------------------------------------------

    async def prepare_sorting_stage(self):
        """
        Prepare the post-cleanup sorting assistant.

        Behaviour:
        - Ensures a top-level Rekordbox folder named SORTED exists.
        - Loads the full active track collection.
        - Loads existing playlists/folders under SORTED.
        - The GUI then lets you assign every track to one or more playlists.
        """
        print("\n=== SORTING STAGE PREP STARTED ===")
        self.sorted_root_name = "SORTED"
        self.sorted_root_id = None
        self.sorting_tracks = []
        self.sorting_track_index = 0
        self.sorting_actions = {}
        self.sorting_apply_requested = False
        self.sorted_nodes = []
        self.sorted_nodes_by_path = {}
        self.current_musicbrainz_suggestions = []
        self.current_musicbrainz_result = None
        self.musicbrainz_suggestion_vars = {}
        self.sorted_track_ids = set()
        self.sorting_skipped_already_sorted_count = 0

        await self.ensure_sorted_root_folder()
        await self.load_sorted_playlist_tree()
        await self.load_sorted_track_id_set()
        await self.load_sorting_tracks()

        print(f"SORTED root id: {self.sorted_root_id}")
        print(f"Tracks available for sorting: {len(self.sorting_tracks)}")
        print(f"Tracks hidden because already sorted: {self.sorting_skipped_already_sorted_count}")
        print(f"Existing SORTED playlists/folders loaded: {len(self.sorted_nodes)}")
        print("=== SORTING STAGE PREP FINISHED ===")

    async def ensure_sorted_root_folder(self):
        playlists = await self.db.get_playlists()
        for playlist in playlists:
            if (playlist.name or "").strip().casefold() == "sorted" and getattr(playlist, "is_folder", False):
                self.sorted_root_id = playlist.id
                return playlist.id

        print("SORTED folder does not exist; creating it.")
        self.sorted_root_id = await self.db.create_playlist("SORTED", parent_id=None, is_folder=True)
        return self.sorted_root_id

    async def load_sorting_tracks(self):
        """Load active collection tracks and, by default, hide tracks already sorted."""
        def _inner():
            if hasattr(self.db, "_get_active_content") and hasattr(self.db, "_content_to_track"):
                return [self.db._content_to_track(c) for c in self.db._get_active_content()]

            # Fallback: pyrekordbox direct content conversion if wrapper helpers exist differently.
            if hasattr(self.db, "db") and self.db.db is not None:
                rows = list(self.db.db.get_content())
                tracks = []
                for c in rows:
                    if getattr(c, "rb_local_deleted", 0) != 0:
                        continue
                    if hasattr(self.db, "_content_to_track"):
                        tracks.append(self.db._content_to_track(c))
                return tracks

            return []

        result = await self.run_db_thread(_inner)
        all_tracks = sorted(
            [t for t in result if getattr(t, "file_path", "")],
            key=lambda t: ((getattr(t, "artist", "") or "").lower(), (getattr(t, "title", "") or "").lower())
        )

        if not getattr(self, "hide_already_sorted_tracks", True):
            self.sorting_tracks = all_tracks
            self.sorting_skipped_already_sorted_count = 0
            return

        visible = []
        skipped = 0
        for track in all_tracks:
            if self.track_is_already_sorted(track):
                skipped += 1
            else:
                visible.append(track)

        self.sorting_tracks = visible
        self.sorting_skipped_already_sorted_count = skipped

    async def load_sorted_track_id_set(self):
        """Collect track IDs that already appear in any playlist under SORTED."""
        ids = set()
        for node in getattr(self, "sorted_nodes", []):
            if node.get("is_folder"):
                continue
            playlist_id = node.get("id")
            if not playlist_id:
                continue
            try:
                tracks = await self.db.get_playlist_tracks(str(playlist_id))
                for track in tracks:
                    ids.add(str(getattr(track, "id", "")))
            except Exception as exc:
                print(f"Could not read SORTED playlist {node.get('path')}: {exc}")
        self.sorted_track_ids = ids
        print(f"Tracks already present in SORTED playlists: {len(self.sorted_track_ids)}")

    def track_is_already_sorted(self, track):
        """A track is processed if it is in SORTED, in the done cache, or tagged with a SORTED genre."""
        track_id = str(getattr(track, "id", ""))
        if track_id and track_id in getattr(self, "sorted_track_ids", set()):
            return True

        if track_id and track_id in getattr(self, "sorting_done_cache", {}):
            return True

        genre = getattr(track, "genre", "") or ""
        if genre and self.genre_contains_sorted_playlist_name(genre):
            return True

        return False

    def genre_contains_sorted_playlist_name(self, genre_text):
        """Return True when a genre field contains one of your SORTED playlist names."""
        if not genre_text:
            return False
        genre_tokens = {
            self.normalise_playlist_name_for_match(part)
            for part in re.split(r"[;,|/]", str(genre_text))
            if part.strip()
        }
        if not genre_tokens:
            return False

        sorted_names = set()
        for node in getattr(self, "sorted_nodes", []):
            if node.get("is_folder"):
                continue
            name = node.get("name") or ((node.get("path") or [""])[-1])
            if name:
                sorted_names.add(self.normalise_playlist_name_for_match(name))

        return any(token in sorted_names for token in genre_tokens)

    async def load_sorted_playlist_tree(self):
        playlists = await self.db.get_playlists()
        by_id = {str(p.id): p for p in playlists}
        children = defaultdict(list)
        for p in playlists:
            parent = str(p.parent_id) if p.parent_id else None
            children[parent].append(p)

        self.sorted_nodes = []
        self.sorted_nodes_by_path = {}
        self.current_musicbrainz_suggestions = []
        self.current_musicbrainz_result = None
        self.musicbrainz_suggestion_vars = {}

        def walk(parent_id, path_parts, depth):
            for p in sorted(children.get(str(parent_id), []), key=lambda x: ((not getattr(x, "is_folder", False)), (x.name or "").lower())):
                node_path = tuple(path_parts + [p.name])
                node = {
                    "id": str(p.id),
                    "name": p.name,
                    "path": node_path,
                    "depth": depth,
                    "is_folder": bool(getattr(p, "is_folder", False)),
                    "is_existing": True,
                    "parent_path": tuple(path_parts),
                }
                self.sorted_nodes.append(node)
                self.sorted_nodes_by_path[node_path] = node
                if node["is_folder"]:
                    walk(p.id, list(node_path), depth + 1)

        if self.sorted_root_id:
            walk(self.sorted_root_id, [], 0)


    def open_sorting_window(self):
        self.sort_root = tk.Tk()
        self.sort_root.title("Rekordbox SORTED Playlist Assistant")
        self.sort_root.geometry("1550x920")

        self.sort_playlist_vars = {}
        self.sort_search_var = tk.StringVar()

        # For a 3,000 track library, public MusicBrainz + permanent local cache is
        # more practical than a full local MusicBrainz mirror. This makes each track
        # look itself up when displayed, but repeated lookups come from cache.
        self.auto_musicbrainz_lookup_var = tk.BooleanVar(value=True)

        # Auto-preview the selected/current track inside this Tk window.
        # Turn this off if you want to browse silently.
        self.auto_play_on_track_load_var = tk.BooleanVar(value=True)

        title = ttk.Label(
            self.sort_root,
            text="SORTED assistant: approve MusicBrainz suggestions, tick your real DJ playlists, then write those playlist names as Genre",
            font=("Arial", 15, "bold")
        )
        title.pack(pady=8)

        help_label = ttk.Label(
            self.sort_root,
            text=(
                "MusicBrainz is only used as a helper. Your SORTED playlist names are the source of truth. "
                "Tick playlists you actually want; Genre becomes the selected playlist names, e.g. House; Tech House."
            ),
            wraplength=1450
        )
        help_label.pack(pady=(0, 5))

        main = ttk.Frame(self.sort_root)
        main.pack(fill="both", expand=True, padx=10, pady=5)

        track_col = ttk.LabelFrame(main, text="1) Track")
        track_col.pack(side="left", fill="both", expand=True, padx=5)

        mb_col = ttk.LabelFrame(main, text="2) MusicBrainz suggestions — approve, do not trust blindly")
        mb_col.pack(side="left", fill="both", expand=True, padx=5)

        playlist_col = ttk.LabelFrame(main, text="3) Your SORTED playlists — source of truth")
        playlist_col.pack(side="right", fill="both", expand=True, padx=5)

        self.sort_track_label = ttk.Label(track_col, text="", font=("Arial", 13, "bold"), wraplength=480)
        self.sort_track_label.pack(anchor="w", padx=10, pady=8)

        # Editable metadata assistant. The original Rekordbox tags are still shown,
        # but these fields are what MusicBrainz lookup uses. Saved changes can also
        # be written back to Rekordbox during Apply.
        self.sort_meta_vars = {
            "artist": tk.StringVar(),
            "title": tk.StringVar(),
            "album": tk.StringVar(),
            "year": tk.StringVar(),
            "comments": tk.StringVar(),
        }

        meta_box = ttk.LabelFrame(track_col, text="Track attributes / MusicBrainz search metadata")
        meta_box.pack(fill="x", padx=10, pady=5)

        row = ttk.Frame(meta_box)
        row.pack(fill="x", padx=6, pady=2)
        ttk.Label(row, text="Artist", width=10).pack(side="left")
        ttk.Entry(row, textvariable=self.sort_meta_vars["artist"]).pack(side="left", fill="x", expand=True)

        row = ttk.Frame(meta_box)
        row.pack(fill="x", padx=6, pady=2)
        ttk.Label(row, text="Title", width=10).pack(side="left")
        ttk.Entry(row, textvariable=self.sort_meta_vars["title"]).pack(side="left", fill="x", expand=True)

        row = ttk.Frame(meta_box)
        row.pack(fill="x", padx=6, pady=2)
        ttk.Label(row, text="Album", width=10).pack(side="left")
        ttk.Entry(row, textvariable=self.sort_meta_vars["album"]).pack(side="left", fill="x", expand=True)

        row = ttk.Frame(meta_box)
        row.pack(fill="x", padx=6, pady=2)
        ttk.Label(row, text="Year", width=10).pack(side="left")
        ttk.Entry(row, textvariable=self.sort_meta_vars["year"]).pack(side="left", fill="x", expand=True)

        row = ttk.Frame(meta_box)
        row.pack(fill="x", padx=6, pady=2)
        ttk.Label(row, text="Comments", width=10).pack(side="left")
        ttk.Entry(row, textvariable=self.sort_meta_vars["comments"]).pack(side="left", fill="x", expand=True)

        meta_buttons = ttk.Frame(meta_box)
        meta_buttons.pack(fill="x", padx=6, pady=4)
        ttk.Button(meta_buttons, text="Guess artist/title from filename", command=self.sort_guess_metadata_from_filename).pack(side="left", padx=3)
        ttk.Button(meta_buttons, text="Use current Rekordbox tags", command=self.sort_reset_metadata_fields).pack(side="left", padx=3)
        ttk.Button(meta_buttons, text="Apply fields to lookup", command=self.sort_apply_metadata_fields).pack(side="left", padx=3)
        ttk.Button(meta_buttons, text="Normalise Intro/Clean/Dirty", command=self.sort_normalise_current_title_version).pack(side="left", padx=3)

        token_box = ttk.LabelFrame(track_col, text="Filename/title tokens — select words then send to Artist or Title")
        token_box.pack(fill="both", expand=False, padx=10, pady=5)
        self.sort_token_listbox = tk.Listbox(token_box, height=6, selectmode="extended", exportselection=False)
        self.sort_token_listbox.pack(fill="x", padx=6, pady=4)
        token_buttons = ttk.Frame(token_box)
        token_buttons.pack(fill="x", padx=6, pady=(0,4))
        ttk.Button(token_buttons, text="Replace Artist", command=lambda: self.sort_tokens_to_field("artist", replace=True)).pack(side="left", padx=2)
        ttk.Button(token_buttons, text="Append Artist", command=lambda: self.sort_tokens_to_field("artist", replace=False)).pack(side="left", padx=2)
        ttk.Button(token_buttons, text="Replace Title", command=lambda: self.sort_tokens_to_field("title", replace=True)).pack(side="left", padx=2)
        ttk.Button(token_buttons, text="Append Title", command=lambda: self.sort_tokens_to_field("title", replace=False)).pack(side="left", padx=2)
        ttk.Button(token_buttons, text="Clear Artist/Title", command=self.sort_clear_artist_title_fields).pack(side="left", padx=2)

        self.sort_track_meta = tk.Text(track_col, height=10, wrap="word")
        self.sort_track_meta.pack(fill="x", padx=10, pady=5)

        audio_box = ttk.LabelFrame(track_col, text="Embedded audio preview")
        audio_box.pack(fill="x", padx=10, pady=5)

        audio_buttons = ttk.Frame(audio_box)
        audio_buttons.pack(fill="x", padx=6, pady=4)

        ttk.Button(audio_buttons, text="Play current", command=self.sort_play_current_track).pack(side="left", padx=4)
        ttk.Button(audio_buttons, text="Pause / Resume", command=self.pause_resume_embedded_audio).pack(side="left", padx=4)
        ttk.Button(audio_buttons, text="Stop", command=self.stop_embedded_audio).pack(side="left", padx=4)
        ttk.Button(audio_buttons, text="Open file location", command=self.sort_open_current_file_location).pack(side="left", padx=4)

        ttk.Checkbutton(
            audio_box,
            text="Auto-play when track changes",
            variable=self.auto_play_on_track_load_var,
        ).pack(anchor="w", padx=8, pady=(0, 2))

        self.audio_status_label = ttk.Label(
            audio_box,
            text="Audio preview idle. Requires: pip install pygame",
            wraplength=520,
        )
        self.audio_status_label.pack(fill="x", padx=8, pady=(0, 5))

        nav = ttk.Frame(track_col)
        nav.pack(fill="x", padx=10, pady=10)
        ttk.Button(nav, text="Previous", command=self.sort_previous_track).pack(side="left", padx=5)
        ttk.Button(nav, text="Save choices + Next", command=self.sort_save_and_next).pack(side="left", padx=5)
        ttk.Button(nav, text="Skip", command=self.sort_skip_track).pack(side="left", padx=5)

        mb_buttons = ttk.Frame(mb_col)
        mb_buttons.pack(fill="x", padx=6, pady=4)
        ttk.Checkbutton(
            mb_buttons,
            text="Auto-suggest on track load",
            variable=self.auto_musicbrainz_lookup_var,
        ).pack(side="left", padx=3)
        ttk.Button(mb_buttons, text="Suggest genres", command=self.sort_fetch_musicbrainz_suggestions).pack(side="left", padx=3)
        ttk.Button(mb_buttons, text="Force fresh lookup", command=lambda: self.sort_fetch_musicbrainz_suggestions(force_refresh=True)).pack(side="left", padx=3)
        ttk.Button(mb_buttons, text="Tick selected playlist suggestions", command=self.sort_apply_selected_musicbrainz_suggestions).pack(side="left", padx=3)
        ttk.Button(mb_buttons, text="Clear", command=self.sort_clear_musicbrainz_suggestions).pack(side="left", padx=3)

        self.musicbrainz_status_label = ttk.Label(
            mb_col,
            text="Auto-suggest is on. Cached results show instantly; uncached tracks use MusicBrainz at about 1 request/sec.",
            wraplength=500
        )
        self.musicbrainz_status_label.pack(anchor="w", padx=6, pady=(0, 4))

        self.musicbrainz_suggestions_frame = ttk.Frame(mb_col)
        self.musicbrainz_suggestions_frame.pack(fill="both", expand=True, padx=6, pady=4)

        debug_frame = ttk.LabelFrame(mb_col, text="MusicBrainz lookup debug")
        debug_frame.pack(fill="both", expand=False, padx=6, pady=(4, 6))
        self.musicbrainz_debug_text = tk.Text(debug_frame, height=9, wrap="word")
        self.musicbrainz_debug_text.pack(fill="both", expand=True, padx=4, pady=4)
        self.musicbrainz_debug_text.insert(tk.END, "Debug appears after Suggest genres: exact query, recordings found, raw tags, mapped playlist names.\n")
        self.musicbrainz_debug_text.configure(state="disabled")

        search_frame = ttk.Frame(playlist_col)
        search_frame.pack(fill="x", padx=8, pady=5)
        ttk.Label(search_frame, text="Filter:").pack(side="left")
        ent = ttk.Entry(search_frame, textvariable=self.sort_search_var)
        ent.pack(side="left", fill="x", expand=True, padx=5)
        ttk.Button(search_frame, text="Apply", command=self.render_sort_playlist_tree).pack(side="left", padx=3)
        ttk.Button(search_frame, text="Clear", command=self.clear_sort_filter).pack(side="left", padx=3)

        create_frame = ttk.Frame(playlist_col)
        create_frame.pack(fill="x", padx=8, pady=5)
        ttk.Button(create_frame, text="Create folder under SORTED", command=self.sort_create_folder).pack(side="left", padx=3)
        ttk.Button(create_frame, text="Create playlist under selected folder", command=self.sort_create_playlist).pack(side="left", padx=3)

        self.sort_parent_choice = tk.StringVar(value="SORTED")
        self.sort_parent_combo = ttk.Combobox(create_frame, textvariable=self.sort_parent_choice, state="readonly", width=35)
        self.sort_parent_combo.pack(side="left", padx=6)
        self.refresh_sort_parent_combo()

        tree_outer = ttk.Frame(playlist_col)
        tree_outer.pack(fill="both", expand=True, padx=8, pady=5)
        self.sort_canvas = tk.Canvas(tree_outer)
        self.sort_scrollbar = ttk.Scrollbar(tree_outer, orient="vertical", command=self.sort_canvas.yview)
        self.sort_checks_frame = ttk.Frame(self.sort_canvas)
        self.sort_checks_frame.bind(
            "<Configure>",
            lambda event: self.sort_canvas.configure(scrollregion=self.sort_canvas.bbox("all"))
        )
        self.sort_canvas_window = self.sort_canvas.create_window((0, 0), window=self.sort_checks_frame, anchor="nw")
        self.sort_canvas.configure(yscrollcommand=self.sort_scrollbar.set)
        self.sort_canvas.pack(side="left", fill="both", expand=True)
        self.sort_scrollbar.pack(side="right", fill="y")
        self.sort_canvas.bind("<Configure>", lambda event: self.sort_canvas.itemconfigure(self.sort_canvas_window, width=event.width))

        self.sort_summary_text = tk.Text(self.sort_root, height=8)
        self.sort_summary_text.pack(fill="x", padx=10, pady=8)

        bottom = ttk.Frame(self.sort_root)
        bottom.pack(fill="x", padx=10, pady=8)
        ttk.Button(bottom, text="Export SORTED to Serato crates", command=self.sort_export_sorted_to_serato_prompt).pack(side="left", padx=5)
        ttk.Button(bottom, text="Finish and apply sorting changes", command=self.sort_finish_and_close).pack(side="right", padx=5)
        ttk.Button(bottom, text="Exit without applying sorting", command=self.sort_cancel).pack(side="right", padx=5)

        self.render_sort_track()
        self.sort_clear_musicbrainz_suggestions(silent=True)
        self.render_sort_playlist_tree()
        self.render_sort_summary()
        self.sort_root.mainloop()
    def current_sort_track(self):
        if not self.sorting_tracks:
            return None
        self.sorting_track_index = max(0, min(self.sorting_track_index, len(self.sorting_tracks) - 1))
        return self.sorting_tracks[self.sorting_track_index]

    def sort_track_id(self, track):
        return str(getattr(track, "id", ""))


    def clean_track_token(self, token):
        token = str(token or "")
        token = re.sub(r"^[\(\[]+|[\)\]]+$", "", token)
        token = re.sub(r"^[\d._#-]+", "", token)
        token = token.replace("_", " ").strip(" -._()[]{}")
        return token.strip()

    def metadata_noise_words(self):
        return {
            "mp3", "flac", "wav", "aif", "aiff", "m4a",
            "dirty", "clean", "explicit", "intro", "outro", "radio", "edit",
            "version", "mix", "remix", "extended", "ck", "dj", "original",
            "quick", "hit", "short", "full", "download", "playlist", "wav",
        }

    def sort_candidate_text_for_tokens(self, track=None):
        track = track or self.current_sort_track()
        if not track:
            return ""
        parts = []
        title = getattr(track, "title", "") or ""
        path = getattr(track, "file_path", "") or ""
        if title:
            parts.append(title)
        if path:
            parts.append(Path(path).stem)
        return " | ".join(parts)

    def sort_extract_metadata_tokens(self, track=None):
        text = self.sort_candidate_text_for_tokens(track)
        text = re.sub(r"[|]+", " - ", text)
        # Split but preserve normal words; remove obvious technical junk.
        raw = re.split(r"[\/\-_ââ:;,.]+|\s+", text)
        noise = self.metadata_noise_words()
        result = []
        seen = set()
        for tok in raw:
            cleaned = self.clean_track_token(tok)
            if not cleaned:
                continue
            low = cleaned.casefold()
            if low in noise:
                continue
            # Hide pure track numbers / durations like 122, 4, 13 where possible.
            if low.isdigit():
                continue
            if len(low) == 1 and low not in {"t", "i"}:
                continue
            if low not in seen:
                seen.add(low)
                result.append(cleaned)
        return result

    def sort_get_selected_tokens(self):
        if not hasattr(self, "sort_token_listbox"):
            return []
        return [self.sort_token_listbox.get(i) for i in self.sort_token_listbox.curselection()]

    def sort_tokens_to_field(self, field, replace=True):
        tokens = self.sort_get_selected_tokens()
        if not tokens:
            return
        text = " ".join(tokens).strip()
        var = self.sort_meta_vars.get(field)
        if var is None:
            return
        if replace or not var.get().strip():
            var.set(self.title_case_metadata(text))
        else:
            var.set((var.get().strip() + " " + self.title_case_metadata(text)).strip())
        self.sort_apply_metadata_fields(refresh_lookup=False)

    def sort_clear_artist_title_fields(self):
        self.sort_meta_vars["artist"].set("")
        self.sort_meta_vars["title"].set("")
        self.sort_apply_metadata_fields(refresh_lookup=False)

    def title_case_metadata(self, value):
        value = re.sub(r"\s+", " ", str(value or "")).strip()
        if not value:
            return ""
        # Keep common all-caps acronyms readable.
        small = {"ft", "feat", "and", "the", "of", "a", "an", "in", "on"}
        words = []
        for w in value.split():
            lw = w.casefold()
            if lw in {"r&b", "uk", "usa", "dj"}:
                words.append(w.upper())
            elif lw in small:
                words.append(lw)
            else:
                words.append(w[:1].upper() + w[1:])
        if words:
            words[0] = words[0][:1].upper() + words[0][1:]
        return " ".join(words)

    def detect_dj_version_flags(self, *texts):
        """
        Detect DJ-library version words from Rekordbox title / filename text.

        These flags are intended for the displayed/written Rekordbox title only.
        MusicBrainz lookup strips them back out so searches use the clean title.
        Examples:
            "Intro Dirty" -> ["Intro", "Dirty"]
            "Clean Intro" -> ["Intro", "Clean"]
            "Chris Hailes Intro" -> ["Intro"]
        """
        joined = " ".join(str(t or "") for t in texts).casefold()
        compact = re.sub(r"[_\-./\\()\[\]{}]+", " ", joined)
        compact = re.sub(r"\s+", " ", compact)

        flags = []
        if re.search(r"\b(intro|ck intro|dj intro|quick hit|short edit)\b", compact):
            flags.append("Intro")

        # Treat explicit as Dirty for DJ file naming.
        if re.search(r"\b(dirty|explicit)\b", compact):
            flags.append("Dirty")
        elif re.search(r"\bclean\b", compact):
            flags.append("Clean")

        return flags

    def strip_dj_version_words(self, value):
        """
        Remove DJ/version/extension noise from a title string for lookup.

        This is deliberately aggressive because it is ONLY used for clean
        MusicBrainz lookup text, not for the final Rekordbox display title.

        Examples:
            "Thong Song (4.13 Version) (Dirty) (Flac)" -> "Thong Song"
            "Thong Song (Dirty) (Chris Hailes Intro) (Wav)" -> "Thong Song"
        """
        value = str(value or "")

        # Remove full bracketed chunks that are obviously not part of the song title.
        # This catches broken cases like "(4.13 Version)", "(Dirty)",
        # "(Chris Hailes Intro)", "(Wav)", etc.
        noisy_bracket_words = (
            r"intro|dirty|clean|explicit|version|flac|wav|mp3|aif|aiff|m4a|"
            r"ck intro|dj intro|quick hit|short edit|radio edit|remix|edit"
        )
        value = re.sub(
            rf"\([^)]*(?:{noisy_bracket_words}|\d+(?:\.\d+)?\s*version)[^)]*\)",
            " ",
            value,
            flags=re.I,
        )
        value = re.sub(
            rf"\[[^\]]*(?:{noisy_bracket_words}|\d+(?:\.\d+)?\s*version)[^\]]*\]",
            " ",
            value,
            flags=re.I,
        )

        # Remove loose noise words outside brackets.
        value = re.sub(r"\b(ck intro|dj intro|quick hit|short edit|radio edit)\b", " ", value, flags=re.I)
        value = re.sub(r"\b(intro|dirty|clean|explicit|version|flac|wav|mp3|aif|aiff|m4a)\b", " ", value, flags=re.I)

        # Remove version numbers / catalogue-ish leading numbers.
        value = re.sub(r"\b\d+(?:\.\d+)?\s*version\b", " ", value, flags=re.I)
        value = re.sub(r"\b\d+\s*\.\s*\d+\b", " ", value)
        value = re.sub(r"\b\d{1,2}\s+\d{1,2}\b", " ", value)

        # If earlier removals left unmatched brackets, get rid of bracket chars.
        value = re.sub(r"[()\[\]{}]", " ", value)
        value = re.sub(r"\s+", " ", value).strip(" -")
        return value

    def remove_existing_dj_version_suffix(self, title):
        title = str(title or "")
        title = re.sub(
            r"\s*[\[(]\s*(intro\s*[-/]\s*)?(dirty|clean|explicit)?\s*[-/]?\s*(intro)?\s*[\])]\s*$",
            "",
            title,
            flags=re.I,
        )
        title = re.sub(r"\s+", " ", title).strip(" -")
        return title

    def apply_dj_version_suffix(self, base_title, flags):
        base_title = self.remove_existing_dj_version_suffix(base_title)
        base_title = re.sub(r"\s+", " ", str(base_title or "")).strip(" -")
        if not base_title:
            return ""
        clean_flags = []
        for flag in flags:
            if flag and flag not in clean_flags:
                clean_flags.append(flag)
        if not clean_flags:
            return self.title_case_metadata(base_title)
        return f"{self.title_case_metadata(base_title)} ({' - '.join(clean_flags)})"

    def musicbrainz_lookup_title_from_display_title(self, title):
        """Use the clean title for API lookup, even if UI title includes (Intro - Dirty)."""
        title = self.remove_existing_dj_version_suffix(title)
        title = self.strip_dj_version_words(title)
        return self.title_case_metadata(title)

    def remove_leading_track_number(self, text):
        """Remove DJ/library numbering such as '04.', '04 -', '(04)' from the front."""
        text = str(text or "")
        text = re.sub(r"^\s*\(?\s*\d{1,4}\s*\)?\s*[-.)_ ]+", "", text)
        return re.sub(r"\s+", " ", text).strip(" -")

    def find_artist_title_separator(self, text):
        """Find the first artist/title dash outside brackets.

        Example:
            04. Iggy Azalea Ft Charlie Xcx - Fancy (Intro - Dirty)
        should split on the dash before Fancy, not the dash inside Intro - Dirty.
        """
        text = str(text or "")
        depth = 0
        for index, char in enumerate(text):
            if char in "([{" :
                depth += 1
                continue
            if char in ")]}":
                depth = max(0, depth - 1)
                continue
            if depth != 0:
                continue
            if char not in "-–—":
                continue

            before = text[:index].strip()
            after = text[index + 1:].strip()
            if not before or not after:
                continue

            # Avoid treating version text as an artist/title split.
            before_tail = before.split()[-1].casefold() if before.split() else ""
            after_head = after.split()[0].strip("()[]{} ").casefold() if after.split() else ""
            version_words = {
                "intro", "clean", "dirty", "explicit", "radio", "edit",
                "remix", "mix", "extended", "instrumental", "acapella",
            }
            if before_tail in version_words or after_head in version_words:
                continue

            return index
        return None

    def sort_guess_artist_title_from_text(self, text):
        original = str(text or "")
        flags = self.detect_dj_version_flags(original)

        stem = Path(original).stem
        stem = stem.replace("_", " ")
        stem = re.sub(r"\b(mp3|flac|wav|aif|aiff|m4a)\b", " ", stem, flags=re.I)
        stem = self.remove_leading_track_number(stem)
        stem = re.sub(r"\s+", " ", stem).strip(" -")

        # Prefer the first real dash outside brackets as Artist - Title.
        # Dashes inside version suffixes such as (Intro - Dirty) are ignored.
        separator = self.find_artist_title_separator(stem)
        if separator is not None:
            artist = stem[:separator].strip(" -")
            title = stem[separator + 1:].strip(" -")
        else:
            # Fallback: use first token as artist and the rest as title.
            tokens = [self.clean_track_token(t) for t in stem.split()]
            tokens = [
                t for t in tokens
                if t and t.casefold() not in self.metadata_noise_words() and not t.isdigit()
            ]
            if len(tokens) >= 3:
                artist = tokens[0]
                title = " ".join(tokens[1:])
            else:
                artist = ""
                title = " ".join(tokens)

        clean_title = self.strip_dj_version_words(title)
        clean_title = re.sub(r"\s+", " ", clean_title).strip(" -")
        title = self.apply_dj_version_suffix(clean_title, flags)
        artist = re.sub(r"\s+", " ", artist).strip(" -")
        return self.title_case_metadata(artist), title

    def sort_normalise_current_title_version(self):
        """Normalise current title field to e.g. Thong Song (Intro - Dirty)."""
        track = self.current_sort_track()
        if not track:
            return
        fields = self.sort_get_metadata_fields()
        existing_title = fields.get("title") or getattr(track, "title", "") or ""
        file_path = getattr(track, "file_path", "") or ""
        context = " ".join([
            existing_title,
            getattr(track, "title", "") or "",
            file_path,
            Path(file_path).parent.name if file_path else "",
            Path(file_path).stem if file_path else "",
            fields.get("comments", ""),
        ])
        flags = self.detect_dj_version_flags(context)
        clean_title = self.musicbrainz_lookup_title_from_display_title(existing_title)
        if clean_title:
            self.sort_meta_vars["title"].set(self.apply_dj_version_suffix(clean_title, flags))
        self.sort_apply_metadata_fields(refresh_lookup=False)

    def sort_guess_metadata_from_filename(self):
        track = self.current_sort_track()
        if not track:
            return

        file_path = getattr(track, "file_path", "") or ""
        file_stem = Path(file_path).stem
        parent_name = Path(file_path).parent.name if file_path else ""
        raw_title = getattr(track, "title", "") or ""
        raw_artist = getattr(track, "artist", "") or ""

        # Use both path and Rekordbox title as evidence. The filename/folder often
        # contains useful DJ-version info like "Chris Hailes Intro", while the
        # Rekordbox title may contain Dirty/Clean/Flac/Version noise.
        flags = self.detect_dj_version_flags(file_path, parent_name, file_stem, raw_title)

        # Prefer filename when it has an artist-title split, because it usually
        # reflects the real local DJ file name. Fall back to Rekordbox title.
        file_artist, file_title = self.sort_guess_artist_title_from_text(file_stem)
        rb_artist, rb_title = self.sort_guess_artist_title_from_text(raw_title)

        artist = file_artist or raw_artist or rb_artist

        # Choose the cleanest base title, then reapply normalised DJ suffix.
        file_clean = self.musicbrainz_lookup_title_from_display_title(file_title)
        rb_clean = self.musicbrainz_lookup_title_from_display_title(rb_title or raw_title)

        if file_clean and (len(file_clean) <= len(rb_clean or file_clean) + 8):
            clean_title = file_clean
        else:
            clean_title = rb_clean or file_clean

        title = self.apply_dj_version_suffix(clean_title, flags)

        if artist:
            self.sort_meta_vars["artist"].set(artist)
        if title:
            self.sort_meta_vars["title"].set(title)
        self.sort_apply_metadata_fields(refresh_lookup=False)

    def sort_reset_metadata_fields(self):
        track = self.current_sort_track()
        if not track:
            return
        self.sort_meta_vars["artist"].set(getattr(track, "artist", "") or "")
        self.sort_meta_vars["title"].set(getattr(track, "title", "") or "")
        self.sort_meta_vars["album"].set(getattr(track, "album", "") or "")
        self.sort_meta_vars["year"].set(str(getattr(track, "year", "") or ""))
        self.sort_meta_vars["comments"].set(getattr(track, "comments", "") or "")
        self.sort_apply_metadata_fields(refresh_lookup=False)

    def sort_get_metadata_fields(self):
        if not hasattr(self, "sort_meta_vars"):
            track = self.current_sort_track()
            return {
                "artist": getattr(track, "artist", "") or "",
                "title": getattr(track, "title", "") or "",
                "album": getattr(track, "album", "") or "",
                "year": str(getattr(track, "year", "") or ""),
                "comments": getattr(track, "comments", "") or "",
            }
        return {key: var.get().strip() for key, var in self.sort_meta_vars.items()}

    def sort_get_lookup_artist_title(self, track=None):
        track = track or self.current_sort_track()
        fields = self.sort_get_metadata_fields()
        artist = fields.get("artist") or getattr(track, "artist", "") or ""
        display_title = fields.get("title") or getattr(track, "title", "") or ""

        # Important: keep titles like "Thong Song (Intro - Dirty)" in Rekordbox,
        # but search MusicBrainz with just "Thong Song".
        lookup_title = self.musicbrainz_lookup_title_from_display_title(display_title)
        return artist, lookup_title

    def sort_apply_metadata_fields(self, refresh_lookup=False):
        # Store the editable metadata on the current action immediately so moving
        # back/forward does not lose it. The actual database write happens only
        # when the final apply button is pressed.
        track = self.current_sort_track()
        if not track:
            return
        track_id = self.sort_track_id(track)
        action = self.sorting_actions.setdefault(track_id, {
            "track": track,
            "track_id": track_id,
            "playlist_paths": [],
            "genre_text": "",
        })
        fields = self.sort_get_metadata_fields()
        action["metadata_override"] = fields
        if refresh_lookup:
            self.sort_fetch_musicbrainz_suggestions(force_refresh=True)
        self.render_sort_summary()



    def render_sort_track(self):
        track = self.current_sort_track()
        if not track:
            self.sort_track_label.config(text="No tracks to sort")
            return

        self.sort_track_label.config(
            text=f"{self.sorting_track_index + 1}/{len(self.sorting_tracks)}: {track.artist or 'Unknown Artist'} - {track.title or 'Untitled'}"
        )

        saved = self.sorting_actions.get(self.sort_track_id(track), {})
        metadata_override = saved.get("metadata_override") or {}

        # Fill editable metadata fields. If we have never edited this track before,
        # start with the current Rekordbox values, and if artist is empty try a
        # filename guess so MusicBrainz has a better first query.
        if hasattr(self, "sort_meta_vars"):
            artist = metadata_override.get("artist", getattr(track, "artist", "") or "")
            title = metadata_override.get("title", getattr(track, "title", "") or "")
            album = metadata_override.get("album", getattr(track, "album", "") or "")
            year = metadata_override.get("year", str(getattr(track, "year", "") or ""))
            comments = metadata_override.get("comments", getattr(track, "comments", "") or "")

            if not artist and title:
                guess_artist, guess_title = self.sort_guess_artist_title_from_text(title)
                if guess_artist:
                    artist = guess_artist
                if guess_title:
                    title = guess_title

            if not artist and getattr(track, "file_path", ""):
                guess_artist, guess_title = self.sort_guess_artist_title_from_text(Path(track.file_path).stem)
                if guess_artist:
                    artist = guess_artist
                if guess_title and (not title or title == getattr(track, "title", "")):
                    title = guess_title

            self.sort_meta_vars["artist"].set(artist)
            self.sort_meta_vars["title"].set(title)
            self.sort_meta_vars["album"].set(album)
            self.sort_meta_vars["year"].set(str(year or ""))
            self.sort_meta_vars["comments"].set(comments)

        if hasattr(self, "sort_token_listbox"):
            self.sort_token_listbox.delete(0, tk.END)
            for token in self.sort_extract_metadata_tokens(track):
                self.sort_token_listbox.insert(tk.END, token)

        self.sort_track_meta.configure(state="normal")
        self.sort_track_meta.delete("1.0", tk.END)
        self.sort_track_meta.insert(tk.END, "Original Rekordbox metadata:\n")
        self.sort_track_meta.insert(tk.END, f"  Artist: {track.artist}\n")
        self.sort_track_meta.insert(tk.END, f"  Title: {track.title}\n")
        self.sort_track_meta.insert(tk.END, f"  Album: {getattr(track, 'album', '')}\n")
        self.sort_track_meta.insert(tk.END, f"  Year: {getattr(track, 'year', '') or ''}\n")
        self.sort_track_meta.insert(tk.END, f"  Current Rekordbox genre: {track.genre}\n")
        self.sort_track_meta.insert(tk.END, f"  BPM: {track.bpm}\n")
        self.sort_track_meta.insert(tk.END, f"  Key: {track.key}\n")
        self.sort_track_meta.insert(tk.END, f"  Rating: {getattr(track, 'rating', '')}\n")
        self.sort_track_meta.insert(tk.END, f"  Play count: {getattr(track, 'play_count', '')}\n")
        self.sort_track_meta.insert(tk.END, f"  Bitrate: {getattr(track, 'bitrate', '')}\n")
        self.sort_track_meta.insert(tk.END, f"  Sample rate: {getattr(track, 'sample_rate', '')}\n")
        self.sort_track_meta.insert(tk.END, f"  Path: {track.file_path}\n")
        self.sort_track_meta.insert(tk.END, f"  Size: {self.file_size_label(track.file_path)}\n")

        fields = self.sort_get_metadata_fields() if hasattr(self, "sort_meta_vars") else {}
        if fields:
            self.sort_track_meta.insert(tk.END, "\nEditable fields currently used for MusicBrainz lookup:\n")
            self.sort_track_meta.insert(tk.END, f"  Artist: {fields.get('artist', '')}\n")
            self.sort_track_meta.insert(tk.END, f"  Title: {fields.get('title', '')}\n")
            self.sort_track_meta.insert(tk.END, f"  Album: {fields.get('album', '')}\n")
            self.sort_track_meta.insert(tk.END, f"  Year: {fields.get('year', '')}\n")
            self.sort_track_meta.insert(tk.END, f"  Comments: {fields.get('comments', '')}\n")

        if saved:
            self.sort_track_meta.insert(tk.END, "\nSaved for final apply:\n")
            self.sort_track_meta.insert(tk.END, f"  Playlists: {', '.join('/'.join(p) for p in saved.get('playlist_paths', []))}\n")
            self.sort_track_meta.insert(tk.END, f"  Genre to write: {saved.get('genre_text', '')}\n")
            if saved.get("metadata_override"):
                self.sort_track_meta.insert(tk.END, f"  Metadata override: {saved.get('metadata_override')}\n")
        else:
            self.sort_track_meta.insert(tk.END, "\nNo saved sorting choice yet.\n")
        self.sort_track_meta.configure(state="disabled")

        self.sort_clear_musicbrainz_suggestions(silent=True)
        self.render_sort_playlist_tree()
        self.sort_schedule_auto_play_current_track()
        self.sort_schedule_auto_musicbrainz_suggestions()

    def sort_schedule_auto_musicbrainz_suggestions(self):
        """Automatically fetch MusicBrainz suggestions when a track is displayed.

        This is deliberately soft:
        - cached results return instantly
        - uncached results obey the MusicBrainz rate limit
        - failures only show a message/debug text and never block manual sorting
        - suggestions are never applied unless you explicitly tick/apply them
        """
        if not hasattr(self, "sort_root"):
            return
        if not hasattr(self, "auto_musicbrainz_lookup_var"):
            return
        if not self.auto_musicbrainz_lookup_var.get():
            return

        track = self.current_sort_track()
        if not track:
            return

        expected_track_id = self.sort_track_id(track)

        def run_if_still_current():
            current = self.current_sort_track()
            if not current or self.sort_track_id(current) != expected_track_id:
                return
            self.sort_fetch_musicbrainz_suggestions(force_refresh=False, automatic=True)

        self.musicbrainz_status_label.config(text="Auto-suggest queued. Checking local cache / MusicBrainz shortly...")
        self.sort_root.after(250, run_if_still_current)

    def render_sort_playlist_tree(self):
        if not hasattr(self, "sort_checks_frame"):
            return

        for widget in self.sort_checks_frame.winfo_children():
            widget.destroy()

        self.sort_playlist_vars.clear()
        track = self.current_sort_track()
        selected_paths = set()
        if track:
            selected_paths = {tuple(p) for p in self.sorting_actions.get(self.sort_track_id(track), {}).get("playlist_paths", [])}

        filter_text = self.sort_search_var.get().strip().casefold() if hasattr(self, "sort_search_var") else ""

        for node in self.sorted_nodes:
            node_path = tuple(node["path"])
            display = "/".join(node_path)
            if filter_text and filter_text not in display.casefold():
                continue

            row = ttk.Frame(self.sort_checks_frame)
            row.pack(fill="x", anchor="w", pady=1)
            indent = "    " * int(node.get("depth", 0))

            if node["is_folder"]:
                ttk.Label(row, text=f"{indent}📁 {node['name']}").pack(side="left", anchor="w")
            else:
                var = tk.BooleanVar(value=node_path in selected_paths)
                self.sort_playlist_vars[node_path] = {"var": var, "node": node}
                ttk.Checkbutton(
                    row,
                    text=f"{indent}🎵 {node['name']}    ({display})",
                    variable=var,
                    command=self.render_sort_summary,
                ).pack(side="left", anchor="w", fill="x", expand=True)

    def refresh_sort_parent_combo(self):
        if not hasattr(self, "sort_parent_combo"):
            return
        folders = ["SORTED"]
        for node in self.sorted_nodes:
            if node.get("is_folder"):
                folders.append("SORTED/" + "/".join(node["path"]))
        self.sort_parent_combo["values"] = folders
        if self.sort_parent_choice.get() not in folders:
            self.sort_parent_choice.set("SORTED")

    def parent_choice_to_path(self):
        value = self.sort_parent_choice.get()
        if value == "SORTED":
            return tuple()
        if value.startswith("SORTED/"):
            return tuple(part for part in value[len("SORTED/"):].split("/") if part)
        return tuple()

    def sort_create_folder(self):
        name = simpledialog.askstring("Create folder", "Folder name under selected parent:", parent=self.sort_root)
        if not name:
            return
        name = name.strip()
        if not name:
            return
        parent_path = self.parent_choice_to_path()
        new_path = tuple(list(parent_path) + [name])
        if new_path in self.sorted_nodes_by_path:
            messagebox.showinfo("Already exists", "That folder/playlist path already exists.")
            return
        node = {
            "id": None,
            "name": name,
            "path": new_path,
            "depth": len(new_path) - 1,
            "is_folder": True,
            "is_existing": False,
            "parent_path": parent_path,
        }
        self.sorted_nodes.append(node)
        self.sorted_nodes_by_path[new_path] = node
        self.sorted_nodes.sort(key=lambda n: (n["path"], not n["is_folder"]))
        self.refresh_sort_parent_combo()
        self.render_sort_playlist_tree()

    def sort_create_playlist(self):
        name = simpledialog.askstring("Create playlist", "Playlist name under selected folder:", parent=self.sort_root)
        if not name:
            return
        name = name.strip()
        if not name:
            return
        parent_path = self.parent_choice_to_path()
        new_path = tuple(list(parent_path) + [name])
        if new_path in self.sorted_nodes_by_path:
            messagebox.showinfo("Already exists", "That folder/playlist path already exists.")
            return
        node = {
            "id": None,
            "name": name,
            "path": new_path,
            "depth": len(new_path) - 1,
            "is_folder": False,
            "is_existing": False,
            "parent_path": parent_path,
        }
        self.sorted_nodes.append(node)
        self.sorted_nodes_by_path[new_path] = node
        self.sorted_nodes.sort(key=lambda n: (n["path"], not n["is_folder"]))
        self.render_sort_playlist_tree()

    def clear_sort_filter(self):
        self.sort_search_var.set("")
        self.render_sort_playlist_tree()

    def sort_selected_playlist_paths(self):
        selected = []
        for path, data in self.sort_playlist_vars.items():
            if data["var"].get():
                selected.append(tuple(path))
        return sorted(selected)

    def sort_save_current_choices(self):
        track = self.current_sort_track()
        if not track:
            return
        playlist_paths = self.sort_selected_playlist_paths()
        genre_names = sorted({path[-1] for path in playlist_paths if path})
        genre_text = "; ".join(genre_names)
        existing = self.sorting_actions.get(self.sort_track_id(track), {})
        metadata_override = self.sort_get_metadata_fields() if hasattr(self, "sort_meta_vars") else existing.get("metadata_override", {})
        if getattr(self, "current_musicbrainz_result", None):
            mb_year = self.current_musicbrainz_result.get("year")
            if mb_year and not str(metadata_override.get("year", "")).strip():
                metadata_override["year"] = str(mb_year)
            mb_album = self.current_musicbrainz_result.get("album")
            if mb_album and not str(metadata_override.get("album", "")).strip():
                metadata_override["album"] = str(mb_album)
                if hasattr(self, "sort_meta_vars") and "album" in self.sort_meta_vars:
                    self.sort_meta_vars["album"].set(str(mb_album))
        self.sorting_actions[self.sort_track_id(track)] = {
            "track": track,
            "track_id": self.sort_track_id(track),
            "playlist_paths": playlist_paths,
            "genre_text": genre_text,
            "metadata_override": metadata_override,
        }
        print(
            f"Saved sorting choice for {self.sort_track_id(track)}: "
            f"playlist_paths={playlist_paths}, genre_text={genre_text!r}"
        )
        self.render_sort_summary()

    def sort_save_and_next(self):
        self.sort_save_current_choices()
        if self.sorting_track_index < len(self.sorting_tracks) - 1:
            self.sorting_track_index += 1
            self.render_sort_track()

    def sort_skip_track(self):
        if self.sorting_track_index < len(self.sorting_tracks) - 1:
            self.sorting_track_index += 1
            self.render_sort_track()

    def sort_previous_track(self):
        self.sort_save_current_choices()
        if self.sorting_track_index > 0:
            self.sorting_track_index -= 1
            self.render_sort_track()

    def render_sort_summary(self):
        if not hasattr(self, "sort_summary_text"):
            return
        track = self.current_sort_track()
        selected = self.sort_selected_playlist_paths() if track else []
        genre_names = sorted({p[-1] for p in selected if p})
        genre_text = "; ".join(genre_names)
        new_nodes = [n for n in self.sorted_nodes if not n.get("is_existing")]

        self.sort_summary_text.delete("1.0", tk.END)
        self.sort_summary_text.insert(tk.END, f"Currently ticked for this track: {len(selected)} playlist(s)\n")
        if selected:
            self.sort_summary_text.insert(tk.END, "  " + ", ".join("/".join(p) for p in selected) + "\n")
        self.sort_summary_text.insert(tk.END, f"Genre that would be written for this track: {genre_text or '(unchanged/blank if saved)'}\n")
        self.sort_summary_text.insert(tk.END, f"Tracks with saved sorting choices: {len(self.sorting_actions)}\n")
        self.sort_summary_text.insert(tk.END, f"Tracks hidden this run because already sorted: {getattr(self, 'sorting_skipped_already_sorted_count', 0)}\n")
        self.sort_summary_text.insert(tk.END, f"Processed-track cache entries: {len(getattr(self, 'sorting_done_cache', {}))}\n")
        self.sort_summary_text.insert(tk.END, f"New folders/playlists waiting to be created: {len(new_nodes)}\n")

    def sort_play_current_track(self):
        track = self.current_sort_track()
        if track:
            self.embedded_play_audio_file(track.file_path, auto=False)

    def sort_schedule_auto_play_current_track(self):
        """Auto-play the currently displayed sorting track inside the Tk window."""
        if not hasattr(self, "sort_root"):
            return
        if not hasattr(self, "auto_play_on_track_load_var"):
            return
        if not self.auto_play_on_track_load_var.get():
            return

        track = self.current_sort_track()
        if not track:
            return

        expected_track_id = self.sort_track_id(track)

        def run_if_still_current():
            current = self.current_sort_track()
            if not current or self.sort_track_id(current) != expected_track_id:
                return
            self.embedded_play_audio_file(current.file_path, auto=True)

        self.sort_root.after(120, run_if_still_current)

    def set_audio_status(self, text):
        if hasattr(self, "audio_status_label"):
            self.audio_status_label.config(text=text)
        else:
            print(text)

    def ensure_embedded_audio_player(self):
        """Initialise pygame.mixer once.

        Install with:
            pip install pygame

        This keeps playback in the Python process rather than launching an
        external default media player. It supports common preview formats through
        SDL_mixer; if a particular FLAC/AIF build fails, convert preview support
        or install a pygame build with that codec enabled.
        """
        if not PYGAME_AVAILABLE or pygame is None:
            raise RuntimeError(
                "pygame is not installed. Run this in your venv/terminal: pip install pygame"
            )

        if not self.audio_mixer_ready:
            pygame.mixer.init()
            self.audio_mixer_ready = True

    def embedded_play_audio_file(self, path, auto=False):
        src = Path(path or "")
        ext = self.get_extension(str(src))

        if ext not in self.PLAYABLE_EXTENSIONS:
            message = f"Unsupported preview type: .{ext}"
            self.set_audio_status(message)
            if not auto:
                messagebox.showwarning("Unsupported file type", message)
            return

        if not src.exists():
            message = f"File not found: {src}"
            self.set_audio_status(message)
            if not auto:
                messagebox.showerror("File not found", f"Could not find this file on disk:\n\n{src}")
            return

        try:
            self.ensure_embedded_audio_player()

            # Stop whatever was previously playing before loading the new track.
            pygame.mixer.music.stop()
            pygame.mixer.music.unload()

            pygame.mixer.music.load(str(src))
            pygame.mixer.music.play()

            self.audio_current_path = str(src)
            self.audio_is_paused = False
            self.set_audio_status(f"Playing: {src.name}")

        except Exception as exc:
            message = f"Could not play inside Tk preview: {src}\n{exc}"
            self.set_audio_status(message)
            if not auto:
                messagebox.showerror(
                    "Could not play embedded audio",
                    message + "\n\nTry: pip install pygame\nIf this is FLAC/AIF and pygame cannot decode it, test with MP3/WAV first."
                )

    def pause_resume_embedded_audio(self):
        try:
            self.ensure_embedded_audio_player()
            if self.audio_is_paused:
                pygame.mixer.music.unpause()
                self.audio_is_paused = False
                name = Path(self.audio_current_path).name if self.audio_current_path else "audio"
                self.set_audio_status(f"Playing: {name}")
            else:
                pygame.mixer.music.pause()
                self.audio_is_paused = True
                name = Path(self.audio_current_path).name if self.audio_current_path else "audio"
                self.set_audio_status(f"Paused: {name}")
        except Exception as exc:
            self.set_audio_status(f"Could not pause/resume audio: {exc}")

    def stop_embedded_audio(self):
        try:
            if PYGAME_AVAILABLE and pygame is not None and self.audio_mixer_ready:
                pygame.mixer.music.stop()
                try:
                    pygame.mixer.music.unload()
                except Exception:
                    pass
            self.audio_current_path = None
            self.audio_is_paused = False
            self.set_audio_status("Audio preview stopped.")
        except Exception as exc:
            self.set_audio_status(f"Could not stop audio: {exc}")

    def sort_open_current_file_location(self):
        track = self.current_sort_track()
        if not track or not track.file_path:
            return
        src = Path(track.file_path)
        try:
            system = platform.system().lower()
            if system == "windows":
                subprocess.Popen(["explorer", "/select,", str(src)])
            elif system == "darwin":
                subprocess.Popen(["open", "-R", str(src)])
            else:
                subprocess.Popen(["xdg-open", str(src.parent)])
        except Exception as exc:
            messagebox.showerror("Could not open location", str(exc))


    # ------------------------------------------------------------------
    # Serato crate export
    # ------------------------------------------------------------------

    def default_serato_subcrates_dir(self):
        """
        Best guess for Serato's Subcrates folder.

        serato-tools exposes Crate.DIR_PATH, but this fallback keeps the GUI usable
        even before the package is installed.
        """
        try:
            from serato_tools.crate import Crate
            return Path(Crate.DIR_PATH)
        except Exception:
            return Path.home() / "Music" / "_Serato_" / "Subcrates"

    def sort_export_sorted_to_serato_prompt(self):
        """
        Button handler: export all database-backed SORTED playlists as Serato .crate files.
        This can be run at any time after the SORTED tree has loaded.
        """
        try:
            from tkinter import filedialog
        except Exception as exc:
            messagebox.showerror("Tk file dialog unavailable", str(exc))
            return

        # Keep any current GUI-created playlist choices in memory before export.
        try:
            self.sort_save_current_choices()
        except Exception:
            pass

        default_dir = self.default_serato_subcrates_dir()
        try:
            default_dir.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass

        output_dir = filedialog.askdirectory(
            title="Choose Serato _Serato_/Subcrates folder",
            initialdir=str(default_dir if default_dir.exists() else Path.home()),
        )
        if not output_dir:
            return

        confirmed = messagebox.askyesno(
            "Export SORTED to Serato crates?",
            "This will create/update .crate files from every playlist under SORTED.\n\n"
            f"Output folder:\n{output_dir}\n\n"
            "It will not copy audio files. The crates will point to the existing file paths.\n"
            "Close Serato before exporting so it can reload the crate files cleanly.\n\n"
            "Continue?"
        )
        if not confirmed:
            return

        try:
            result = self.export_sorted_playlists_to_serato_crates(Path(output_dir))
        except Exception as exc:
            messagebox.showerror("Serato crate export failed", str(exc))
            raise

        messagebox.showinfo(
            "Serato crate export finished",
            "Export finished.\n\n"
            f"Crates written: {result['crates_written']}\n"
            f"Tracks written: {result['tracks_written']}\n"
            f"Skipped playlists: {result['skipped_playlists']}\n\n"
            "Open Serato and check the Crates panel."
        )

    def safe_serato_crate_filename(self, sorted_path):
        """
        Serato crate file names are plain files, so flatten nested Rekordbox paths:
            SORTED / DANCE / GARAGE -> SORTED - DANCE - GARAGE.crate
        """
        parts = ["SORTED"] + [str(part or "").strip() for part in sorted_path if str(part or "").strip()]
        name = " - ".join(parts)
        name = re.sub(r'[<>:"/\\|?*\x00-\x1f]+', " - ", name)
        name = re.sub(r"\s+", " ", name).strip(" .-_")
        if not name:
            name = "SORTED"
        return name[:180] + ".crate"

    def get_playlist_tracks_for_serato_export(self, playlist_id):
        """
        Synchronous export helper.

        The sorting GUI is running inside Tk's normal mainloop, so this avoids trying
        to await from a button callback. It uses the same pyrekordbox database handle
        behind your RekordboxDatabase wrapper.
        """
        if not getattr(self.db, "db", None):
            raise RuntimeError("Rekordbox database is not connected.")

        playlist_songs = list(self.db.db.get_playlist_songs(PlaylistID=int(playlist_id)))
        active_songs = [
            s for s in playlist_songs
            if getattr(s, "rb_local_deleted", 0) == 0
        ]

        if hasattr(self.db, "_get_active_content"):
            active_content = self.db._get_active_content()
        else:
            active_content = [
                c for c in list(self.db.db.get_content())
                if getattr(c, "rb_local_deleted", 0) == 0
            ]

        content_lookup = {str(c.ID): c for c in active_content}
        tracks = []
        for song_playlist in sorted(active_songs, key=lambda x: getattr(x, "TrackNo", 0)):
            content_id = str(song_playlist.ContentID)
            content = content_lookup.get(content_id)
            if content is None:
                continue

            if hasattr(self.db, "_content_to_track"):
                track = self.db._content_to_track(content)
                tracks.append(track)
            else:
                path = getattr(content, "FolderPath", "") or ""
                tracks.append(type("ExportTrack", (), {"file_path": path})())

        return tracks

    def export_sorted_playlists_to_serato_crates(self, output_dir):
        """
        Convert every non-folder playlist under SORTED into a Serato .crate file.

        Uses:
        - rekordbox-mcp / pyrekordbox wrapper to read SORTED playlists and track paths.
        - serato-tools Crate to write the .crate files.
        """
        try:
            from serato_tools.crate import Crate
        except ImportError as exc:
            raise RuntimeError(
                "serato-tools is not installed. Install it with:\n\n"
                "    pip install serato-tools\n\n"
                "Then run the export again."
            ) from exc

        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        playlist_nodes = [
            node for node in getattr(self, "sorted_nodes", [])
            if not node.get("is_folder") and node.get("id") and node.get("path")
        ]

        crates_written = 0
        tracks_written = 0
        skipped_playlists = 0

        print("\n=== EXPORTING SORTED PLAYLISTS TO SERATO CRATES ===")
        print(f"Output folder: {output_dir}")
        print(f"SORTED playlists found: {len(playlist_nodes)}")

        for node in sorted(playlist_nodes, key=lambda n: tuple(n.get("path") or ())):
            sorted_path = tuple(node.get("path") or ())
            crate_name = self.safe_serato_crate_filename(sorted_path)
            crate_path = output_dir / crate_name

            tracks = self.get_playlist_tracks_for_serato_export(node["id"])
            file_paths = []
            missing_paths = 0
            for track in tracks:
                path = str(getattr(track, "file_path", "") or "").strip()
                if not path:
                    missing_paths += 1
                    continue
                file_paths.append(path)

            if not file_paths:
                skipped_playlists += 1
                print(f"Skipping empty/no-path playlist SORTED/{'/'.join(sorted_path)}")
                continue

            # Crate(path) creates a blank crate if the file does not exist.
            # Reset entries to DEFAULT_ENTRIES so the export mirrors current SORTED membership
            # instead of accumulating stale tracks from old exports.
            crate = Crate(str(crate_path))
            crate.entries = list(Crate.DEFAULT_ENTRIES)
            for path in file_paths:
                crate.add_track(path)
            crate.remove_duplicates()
            crate.save(str(crate_path))

            crates_written += 1
            tracks_written += len(file_paths)
            print(
                f"Wrote {crate_path.name}: {len(file_paths)} track(s) "
                f"from SORTED/{'/'.join(sorted_path)}"
            )
            if missing_paths:
                print(f"  Warning: {missing_paths} track(s) had no file path and were skipped.")

        print(f"Crates written: {crates_written}")
        print(f"Tracks written: {tracks_written}")
        print(f"Skipped playlists: {skipped_playlists}")
        print("=== SERATO CRATE EXPORT FINISHED ===")

        return {
            "crates_written": crates_written,
            "tracks_written": tracks_written,
            "skipped_playlists": skipped_playlists,
            "output_dir": str(output_dir),
        }

    def sort_finish_and_close(self):
        self.sort_save_current_choices()
        total_playlist_adds = sum(len(a.get("playlist_paths", [])) for a in self.sorting_actions.values())
        confirmed = messagebox.askyesno(
            "Apply sorting changes?",
            "This will mutate your Rekordbox database.\n\n"
            f"Tracks with saved choices: {len(self.sorting_actions)}\n"
            f"Playlist additions requested: {total_playlist_adds}\n"
            f"Tracks hidden this run because already sorted: {getattr(self, 'sorting_skipped_already_sorted_count', 0)}\n\n"
            "Each track's Genre field will be set to the selected playlist names joined with '; '.\n"
            "New folders/playlists created in the GUI will be created under SORTED.\n\n"
            "Close Rekordbox and make a backup first. Continue?"
        )
        if confirmed:
            self.sorting_apply_requested = True
            self.sort_root.destroy()

    def sort_cancel(self):
        self.sorting_apply_requested = False
        self.sort_root.destroy()


    # ------------------------------------------------------------------
    # Persistent sorting done cache
    # ------------------------------------------------------------------

    def get_sorting_done_file_path(self):
        try:
            return Path(__file__).resolve().parent / self.SORTING_DONE_CACHE_FILE_NAME
        except Exception:
            return Path.cwd() / self.SORTING_DONE_CACHE_FILE_NAME

    def load_sorting_done_cache(self):
        self.sorting_done_cache = {}
        if not getattr(self, "sorting_done_file", None) or not self.sorting_done_file.exists():
            return
        try:
            data = json.loads(self.sorting_done_file.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                self.sorting_done_cache = data.get("processed_tracks", {}) or {}
            print(f"Loaded processed sorting cache: {len(self.sorting_done_cache)} track(s)")
            print(f"Sorting done cache: {self.sorting_done_file}")
        except Exception as exc:
            print(f"Could not load sorting done cache {self.sorting_done_file}: {exc}")
            self.sorting_done_cache = {}

    def save_sorting_done_cache(self):
        data = {
            "note": (
                "Tracks processed by the SORTED assistant. If you want all tracks to appear again, "
                "delete this file or clear it manually. Tracks may also be hidden if they are already "
                "inside a SORTED playlist or their genre field contains a SORTED playlist name."
            ),
            "processed_tracks": self.sorting_done_cache,
        }
        self.sorting_done_file.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")

    def mark_sorting_action_processed(self, action):
        track_id = str(action.get("track_id", ""))
        if not track_id:
            return
        # Only mark as done when an actual sorting choice was made. Metadata-only edits
        # do not hide the track from future sorting passes.
        if not action.get("playlist_paths") and not action.get("genre_text"):
            return
        self.sorting_done_cache[track_id] = {
            "processed_at": time.strftime("%Y-%m-%d %H:%M:%S"),
            "playlist_paths": [list(p) for p in action.get("playlist_paths", [])],
            "genre_text": action.get("genre_text", ""),
        }

    # ------------------------------------------------------------------
    # MusicBrainz genre suggestion helpers for Phase 3
    # ------------------------------------------------------------------

    def get_musicbrainz_cache_file_path(self):
        try:
            return Path(__file__).resolve().parent / self.MUSICBRAINZ_CACHE_FILE_NAME
        except Exception:
            return Path.cwd() / self.MUSICBRAINZ_CACHE_FILE_NAME

    def load_musicbrainz_cache(self):
        self.musicbrainz_cache = {}
        if not self.musicbrainz_cache_file.exists():
            return

        try:
            data = json.loads(self.musicbrainz_cache_file.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                self.musicbrainz_cache = data
            print(f"Loaded MusicBrainz suggestion cache: {len(self.musicbrainz_cache)} entries")
            print(f"MusicBrainz cache file: {self.musicbrainz_cache_file}")
        except Exception as exc:
            print(f"Could not load MusicBrainz cache {self.musicbrainz_cache_file}: {exc}")
            self.musicbrainz_cache = {}

    def save_musicbrainz_cache(self):
        try:
            self.musicbrainz_cache_file.write_text(
                json.dumps(self.musicbrainz_cache, indent=2, ensure_ascii=False),
                encoding="utf-8"
            )
        except Exception as exc:
            print(f"Could not save MusicBrainz cache {self.musicbrainz_cache_file}: {exc}")

    def musicbrainz_track_cache_key(self, track):
        # Cache by the editable artist/title fields, not only the raw Rekordbox
        # metadata. This means fixing "122 sisqo - thong song..." to
        # Artist=Sisqo, Title=Thong Song gets its own useful cache entry.
        try:
            artist_raw, title_raw = self.sort_get_lookup_artist_title(track)
        except Exception:
            artist_raw = getattr(track, "artist", "") or ""
            title_raw = getattr(track, "title", "") or ""
        artist = self.normalise_musicbrainz_query_text(artist_raw)
        title = self.normalise_musicbrainz_query_text(title_raw)
        return f"{artist}::{title}"

    def normalise_musicbrainz_query_text(self, value):
        value = value.casefold().strip()
        value = re.sub(r"\([^)]*\b(ft|feat|featuring)\.?\b[^)]*\)", " ", value)
        value = re.sub(r"\[[^\]]*\b(ft|feat|featuring)\.?\b[^\]]*\]", " ", value)
        value = re.sub(r"\bfeat\.?\b.*", " ", value)
        value = re.sub(r"\bft\.?\b.*", " ", value)
        value = re.sub(r"\bfeaturing\b.*", " ", value)
        value = re.sub(r"[^a-z0-9 &,'/-]+", " ", value)
        value = re.sub(r"\s+", " ", value).strip()
        return value

    def musicbrainz_urlopen_json(self, url):
        elapsed = time.time() - float(getattr(self, "musicbrainz_last_request_time", 0.0))
        if elapsed < self.MUSICBRAINZ_MIN_REQUEST_INTERVAL:
            time.sleep(self.MUSICBRAINZ_MIN_REQUEST_INTERVAL - elapsed)

        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": self.MUSICBRAINZ_USER_AGENT,
                "Accept": "application/json",
            }
        )

        self.musicbrainz_last_request_time = time.time()
        with urllib.request.urlopen(request, timeout=15) as response:
            raw = response.read().decode("utf-8", errors="replace")
            return json.loads(raw)

    def musicbrainz_search_recordings(self, artist, title, limit=5, mode="artist_title"):
        query_parts = []
        if artist and mode != "title_only":
            query_parts.append(f'artist:"{artist}"')
        if title:
            query_parts.append(f'recording:"{title}"')
        query = " AND ".join(query_parts) if query_parts else title or artist

        params = urllib.parse.urlencode({
            "query": query,
            "fmt": "json",
            "limit": str(limit),
        })
        url = f"{self.MUSICBRAINZ_BASE_URL}/recording/?{params}"

        if not hasattr(self, "current_musicbrainz_debug"):
            self.current_musicbrainz_debug = []
        self.current_musicbrainz_debug.append(f"SEARCH [{mode}]: {query}")
        self.current_musicbrainz_debug.append(f"URL: {url}")

        data = self.musicbrainz_urlopen_json(url)
        recordings = data.get("recordings", []) if isinstance(data, dict) else []
        self.current_musicbrainz_debug.append(f"Recordings returned: {len(recordings)}")

        for rec in recordings[:limit]:
            artist_credit = rec.get("artist-credit", []) or []
            artists = []
            for credit in artist_credit:
                if isinstance(credit, dict):
                    artist_obj = credit.get("artist") or {}
                    name = artist_obj.get("name") or credit.get("name")
                    if name:
                        artists.append(str(name))
            artist_text = ", ".join(artists) if artists else "unknown artist"
            self.current_musicbrainz_debug.append(
                f"  - score={rec.get('score')} | {artist_text} - {rec.get('title')} | id={rec.get('id')}"
            )

        return recordings

    def musicbrainz_lookup_recording_tags(self, mbid):
        params = urllib.parse.urlencode({
            "inc": "genres+tags+releases",
            "fmt": "json",
        })
        url = f"{self.MUSICBRAINZ_BASE_URL}/recording/{urllib.parse.quote(str(mbid))}?{params}"
        return self.musicbrainz_urlopen_json(url)

    def musicbrainz_extract_year(self, recording_details, default_year=None):
        """Return the most obvious MusicBrainz year, falling back to the existing Rekordbox year.

        MusicBrainz can expose dates at recording level and release level. For DJ
        library sorting, the earliest valid release year is usually the safest
        default. If MusicBrainz has no clear date, keep the track's current year.
        """
        years = []

        if isinstance(recording_details, dict):
            for key in ["first-release-date", "date"]:
                raw = recording_details.get(key)
                if raw and re.match(r"^\d{4}", str(raw)):
                    years.append(int(str(raw)[:4]))

            for release in recording_details.get("releases", []) or []:
                if not isinstance(release, dict):
                    continue
                raw = release.get("date")
                if raw and re.match(r"^\d{4}", str(raw)):
                    years.append(int(str(raw)[:4]))

        if years:
            return min(years)

        if default_year not in [None, ""]:
            try:
                return int(str(default_year)[:4])
            except (TypeError, ValueError):
                return None
        return None

    def musicbrainz_extract_album(self, recording_details, default_album=None):
        """Return the most obvious MusicBrainz album/release title.

        Prefer release titles with dates because those are usually real releases.
        If MusicBrainz has no release title, keep the existing Rekordbox album.
        """
        candidates = []
        if isinstance(recording_details, dict):
            for release in recording_details.get("releases", []) or []:
                if not isinstance(release, dict):
                    continue
                title = str(release.get("title") or "").strip()
                if not title:
                    continue
                date = release.get("date") or "9999"
                year = int(str(date)[:4]) if re.match(r"^\d{4}", str(date)) else 9999
                candidates.append((year, title))

        if candidates:
            # Earliest dated release first; then shortest title to avoid noisy deluxe labels.
            candidates.sort(key=lambda item: (item[0], len(item[1]), item[1].casefold()))
            return candidates[0][1]

        if default_album not in [None, ""]:
            return str(default_album).strip() or None
        return None

    def fetch_musicbrainz_genre_suggestions_for_track(self, track, force_refresh=False):
        """
        Search MusicBrainz by artist/title, then lookup tags/genres for likely recordings.

        This deliberately exposes debug data to the GUI so you can see why it said
        "no useful suggestions": no recordings, no tags, or tags that did not map to
        your SORTED playlist names.
        """
        cache_key = self.musicbrainz_track_cache_key(track)
        self.current_musicbrainz_debug = []

        if cache_key in self.musicbrainz_cache and not force_refresh:
            cached = dict(self.musicbrainz_cache[cache_key])
            cached["from_cache"] = True
            debug = list(cached.get("debug", []))
            debug.insert(0, f"Loaded result from local MusicBrainz cache: {cache_key!r}")
            cached["debug"] = debug
            self.current_musicbrainz_debug = cached.get("debug", [])
            return cached

        lookup_artist, lookup_title = self.sort_get_lookup_artist_title(track)
        artist = self.normalise_musicbrainz_query_text(lookup_artist)
        title = self.normalise_musicbrainz_query_text(lookup_title)

        result = {
            "status": "not_found",
            "artist": artist,
            "title": title,
            "query_artist": artist,
            "query_title": title,
            "suggestions": [],
            "raw_tags": [],
            "unmapped_tags": [],
            "source_recordings": [],
            "year": None,
            "from_cache": False,
            "debug": [],
        }

        display_fields = self.sort_get_metadata_fields()
        self.current_musicbrainz_debug.append(f"MusicBrainz base URL: {self.MUSICBRAINZ_BASE_URL}")
        self.current_musicbrainz_debug.append(f"Cache key: {cache_key!r}")
        self.current_musicbrainz_debug.append(f"Display title field: {display_fields.get('title', '')!r}")
        self.current_musicbrainz_debug.append(f"MusicBrainz lookup metadata: artist={artist!r}, title={title!r}")

        if not title:
            result["status"] = "error"
            result["error"] = "Track has no title to search MusicBrainz with."
            result["debug"] = list(self.current_musicbrainz_debug)
            self.musicbrainz_cache[cache_key] = result
            self.save_musicbrainz_cache()
            return result

        try:
            # First try precise artist+title. If that returns no tags/suggestions,
            # retry title-only because many DJ files have artist/remixer metadata wrong.
            search_batches = []
            recordings = self.musicbrainz_search_recordings(artist=artist, title=title, limit=5, mode="artist_title")
            search_batches.append(("artist_title", recordings))
            if not recordings and artist:
                recordings = self.musicbrainz_search_recordings(artist="", title=title, limit=5, mode="title_only")
                search_batches.append(("title_only", recordings))

            tag_scores = defaultdict(float)
            raw_tags = []
            sources = []
            looked_up = 0
            default_year = getattr(track, "year", None)
            default_album = getattr(track, "album", None)
            candidate_years = []
            candidate_albums = []

            for mode, recordings in search_batches:
                for rec in recordings[:5]:
                    mbid = rec.get("id")
                    if not mbid:
                        continue

                    rec_title = rec.get("title", "")
                    rec_score = float(rec.get("score", 0) or 0)
                    artist_credit = rec.get("artist-credit", []) or []
                    rec_artists = []
                    for credit in artist_credit:
                        if isinstance(credit, dict):
                            artist_obj = credit.get("artist") or {}
                            name = artist_obj.get("name") or credit.get("name")
                            if name:
                                rec_artists.append(str(name))

                    sources.append({
                        "id": mbid,
                        "title": rec_title,
                        "artist": ", ".join(rec_artists),
                        "score": rec_score,
                        "search_mode": mode,
                    })

                    self.current_musicbrainz_debug.append(
                        f"LOOKUP [{mode}]: score={rec_score} | {', '.join(rec_artists) or 'unknown artist'} - {rec_title} | {mbid}"
                    )

                    details = self.musicbrainz_lookup_recording_tags(mbid)
                    looked_up += 1

                    mb_year = self.musicbrainz_extract_year(details, default_year=default_year)
                    if mb_year:
                        candidate_years.append(mb_year)
                        self.current_musicbrainz_debug.append(f"  year candidate: {mb_year}")

                    mb_album = self.musicbrainz_extract_album(details, default_album=default_album)
                    if mb_album:
                        candidate_albums.append(mb_album)
                        self.current_musicbrainz_debug.append(f"  album candidate: {mb_album}")

                    local_tag_count = 0
                    for key, weight in [("genres", 3.0), ("tags", 1.0)]:
                        values = details.get(key, []) if isinstance(details, dict) else []
                        self.current_musicbrainz_debug.append(f"  {key}: {len(values)} value(s)")
                        for tag in values:
                            name = str(tag.get("name", "")).strip()
                            if not name:
                                continue
                            count = float(tag.get("count", 1) or 1)
                            raw_tags.append(name)
                            tag_scores[name.casefold()] += weight * max(count, 1.0)
                            local_tag_count += 1

                    if local_tag_count == 0:
                        self.current_musicbrainz_debug.append("  No genres/tags on this MusicBrainz recording.")

                    # Do not hammer too many lookups; one good batch is enough for the UI.
                    if looked_up >= 5:
                        break
                if looked_up >= 5:
                    break

            suggestions = self.map_musicbrainz_tags_to_playlist_suggestions(tag_scores)
            mapped_source_tags = set()
            for suggestion in suggestions:
                for source_tag in suggestion.get("source_tags", []):
                    mapped_source_tags.add(str(source_tag).casefold())

            raw_unique = sorted(set(raw_tags), key=lambda s: s.casefold())
            unmapped = [tag for tag in raw_unique if tag.casefold() not in mapped_source_tags]

            self.current_musicbrainz_debug.append(f"Raw unique tags returned: {len(raw_unique)}")
            self.current_musicbrainz_debug.append("Raw tags: " + (", ".join(raw_unique[:50]) if raw_unique else "none"))
            self.current_musicbrainz_debug.append(f"Mapped SORTED playlist suggestions: {len(suggestions)}")
            if suggestions:
                for sug in suggestions:
                    self.current_musicbrainz_debug.append(
                        f"  -> {sug.get('name')} ({sug.get('confidence')}%) path=SORTED/{'/'.join(sug.get('playlist_path') or [])} exists={sug.get('playlist_exists')}"
                    )
            elif raw_unique:
                self.current_musicbrainz_debug.append(
                    "MusicBrainz returned tags, but none mapped strongly to useful playlist suggestions. "
                    "Edit MUSICBRAINZ_TAG_TO_PLAYLIST if you want these tags to map."
                )

            best_year = min(candidate_years) if candidate_years else self.musicbrainz_extract_year({}, default_year=default_year)
            best_album = None
            if candidate_albums:
                # Most common album title wins; ties prefer shorter names.
                album_counts = defaultdict(int)
                for album in candidate_albums:
                    album_counts[album] += 1
                best_album = sorted(album_counts, key=lambda a: (-album_counts[a], len(a), a.casefold()))[0]
            else:
                best_album = self.musicbrainz_extract_album({}, default_album=default_album)

            result.update({
                "status": "ok" if suggestions or raw_unique or best_year or best_album else "not_found",
                "suggestions": suggestions,
                "raw_tags": raw_unique,
                "unmapped_tags": unmapped[:50],
                "source_recordings": sources,
                "year": best_year,
                "album": best_album,
            })

        except urllib.error.HTTPError as exc:
            result["status"] = "error"
            result["error"] = f"HTTP {exc.code}: {exc.reason}"
            self.current_musicbrainz_debug.append(f"HTTP error: {exc.code} {exc.reason}")
        except urllib.error.URLError as exc:
            result["status"] = "error"
            result["error"] = f"Network error: {exc.reason}"
            self.current_musicbrainz_debug.append(f"Network error: {exc.reason}")
        except Exception as exc:
            result["status"] = "error"
            result["error"] = str(exc)
            self.current_musicbrainz_debug.append(f"Unexpected error: {exc}")

        result["debug"] = list(self.current_musicbrainz_debug)
        self.musicbrainz_cache[cache_key] = result
        self.save_musicbrainz_cache()
        return result



    def normalise_playlist_name_for_match(self, name):
        name = (name or "").casefold().strip()
        name = name.replace("&", "and")
        name = re.sub(r"[^a-z0-9]+", " ", name)
        name = re.sub(r"\s+", " ", name).strip()
        aliases = {
            "dnb": "drum and bass",
            "drum bass": "drum and bass",
            "drum n bass": "drum and bass",
            "rnb": "r and b",
            "rb": "r and b",
            "hiphop": "hip hop",
            "ukg": "uk garage",
        }
        return aliases.get(name, name)

    def sorted_playlist_name_lookup(self):
        lookup = defaultdict(list)
        for node in getattr(self, "sorted_nodes", []):
            if node.get("is_folder"):
                continue
            path = tuple(node.get("path") or [])
            if not path:
                continue
            key = self.normalise_playlist_name_for_match(path[-1])
            lookup[key].append(path)
        return lookup

    def find_best_sorted_playlist_path(self, suggested_name, playlist_lookup=None):
        if playlist_lookup is None:
            playlist_lookup = self.sorted_playlist_name_lookup()

        key = self.normalise_playlist_name_for_match(suggested_name)
        if key in playlist_lookup:
            # Prefer the most specific existing playlist.
            # Example: if SORTED/RNB/R&B exists, use that instead of creating SORTED/R&B.
            return sorted(playlist_lookup[key], key=lambda p: (-len(p), p))[0]

        # Useful aliases for common folder/playlist naming differences.
        # This makes suggestions like R&B match existing structures like SORTED/RNB/R&B.
        alias_keys = {
            "r and b": ["rnb", "rb", "r b"],
            "drum and bass": ["dnb", "drum bass", "drum n bass"],
            "uk garage": ["ukg"],
            "hip hop": ["hiphop", "hip hop"],
        }.get(key, [])
        for alias in alias_keys:
            alias_norm = self.normalise_playlist_name_for_match(alias)
            if alias_norm in playlist_lookup:
                return sorted(playlist_lookup[alias_norm], key=lambda p: (-len(p), p))[0]

        # Light fuzzy fallback for existing playlist names, but avoid wild matches.
        best_path = None
        best_ratio = 0.0
        for existing_key, paths in playlist_lookup.items():
            ratio = SequenceMatcher(None, key, existing_key).ratio()
            if ratio > best_ratio:
                best_ratio = ratio
                best_path = sorted(paths, key=lambda p: (-len(p), p))[0]

        return best_path if best_ratio >= 0.88 else None

    def refresh_musicbrainz_suggestions_against_current_sorted_tree(self, suggestions):
        """
        Cached MusicBrainz suggestions can become stale after you create new SORTED
        folders/playlists. Before rendering or applying suggestions, re-check every
        suggestion against the current SORTED tree and prefer existing playlists.

        This prevents cases like:
            suggestion R&B -> creates SORTED/R&B
        when you already have:
            SORTED/RNB/R&B
        """
        playlist_lookup = self.sorted_playlist_name_lookup()
        refreshed = []

        for suggestion in suggestions or []:
            suggestion = dict(suggestion)
            name = suggestion.get("name", "")
            if not name:
                refreshed.append(suggestion)
                continue

            matched_path = self.find_best_sorted_playlist_path(name, playlist_lookup)
            if matched_path:
                suggestion["playlist_path"] = list(matched_path)
                suggestion["playlist_exists"] = True
            else:
                suggestion["playlist_path"] = suggestion.get("playlist_path") or [name]
                # Make absolutely sure stale cache does not incorrectly claim existence.
                suggestion["playlist_exists"] = tuple(suggestion["playlist_path"]) in self.sorted_nodes_by_path

            refreshed.append(suggestion)

        return refreshed

    def map_musicbrainz_tags_to_playlist_suggestions(self, tag_scores):
        """
        Convert MusicBrainz genre/tag scores into DJ-useful SORTED playlist suggestions.

        Important: this does not decide the genre. It only proposes playlists to tick.
        Existing SORTED playlist names are preferred; unknown useful tags are shown as
        possible new playlists.
        """
        canonical_scores = defaultdict(float)
        source_tags = defaultdict(list)

        for raw_tag, score in tag_scores.items():
            tag = raw_tag.casefold().strip().replace("_", " ")
            tag = re.sub(r"\s+", " ", tag)
            if not tag:
                continue

            canonical = self.MUSICBRAINZ_TAG_TO_PLAYLIST.get(tag)
            if not canonical:
                if 2 <= len(tag) <= 30 and not any(bad in tag for bad in ["seen live", "favorite", "spotify", "albums i own"]):
                    canonical = " ".join(part.capitalize() for part in tag.split())
                else:
                    continue

            canonical_scores[canonical] += score
            source_tags[canonical].append(raw_tag)

        if not canonical_scores:
            return []

        max_score = max(canonical_scores.values()) or 1.0
        playlist_lookup = self.sorted_playlist_name_lookup()
        suggestions = []

        for name, score in sorted(canonical_scores.items(), key=lambda x: (-x[1], x[0].casefold()))[:12]:
            matched_path = self.find_best_sorted_playlist_path(name, playlist_lookup)
            confidence = int(round(100 * score / max_score))
            suggestions.append({
                "name": name,
                "score": round(score, 2),
                "confidence": confidence,
                "playlist_path": list(matched_path) if matched_path else [name],
                "playlist_exists": bool(matched_path),
                "source_tags": sorted(set(source_tags.get(name, [])), key=lambda s: s.casefold())[:6],
            })

        return suggestions
    def sort_fetch_musicbrainz_suggestions(self, force_refresh=False, automatic=False):
        track = self.current_sort_track()
        if not track:
            return

        # Check whether this will be a cache hit before showing a scary "querying" message.
        cache_key = self.musicbrainz_track_cache_key(track)
        if cache_key in self.musicbrainz_cache and not force_refresh:
            self.musicbrainz_status_label.config(text="Loading MusicBrainz suggestions from local cache...")
        elif automatic:
            self.musicbrainz_status_label.config(text="Auto-querying MusicBrainz... uncached tracks are rate-limited to about 1 request/sec.")
        else:
            self.musicbrainz_status_label.config(text="Querying MusicBrainz... this may take a few seconds.")
        self.sort_root.update_idletasks()

        result = self.fetch_musicbrainz_genre_suggestions_for_track(track, force_refresh=force_refresh)
        result["automatic"] = bool(automatic)
        self.current_musicbrainz_result = result
        self.current_musicbrainz_suggestions = result.get("suggestions", [])
        mb_year = result.get("year")
        if mb_year and hasattr(self, "sort_meta_vars") and not self.sort_meta_vars.get("year").get().strip():
            self.sort_meta_vars["year"].set(str(mb_year))
            self.sort_apply_metadata_fields(refresh_lookup=False)
        self.render_musicbrainz_suggestions(result)


    def render_musicbrainz_suggestions(self, result=None):
        if not hasattr(self, "musicbrainz_suggestions_frame"):
            return

        for widget in self.musicbrainz_suggestions_frame.winfo_children():
            widget.destroy()

        self.musicbrainz_suggestion_vars = {}

        if result is None:
            result = {"status": "idle", "suggestions": [], "debug": []}

        self.render_musicbrainz_debug(result)

        status = result.get("status", "unknown")
        if status == "ok":
            cache_note = "local cache" if result.get("from_cache") else "MusicBrainz"
            auto_note = "Auto-suggest loaded" if result.get("automatic") else "Suggestions loaded"
            self.musicbrainz_status_label.config(
                text=(
                    f"{auto_note} from {cache_note}. Confidence is relative, not certainty. "
                    f"Year suggestion: {result.get('year') or 'none'}. "
                    "Tick suggestions you agree with, then press 'Tick selected playlist suggestions'."
                )
            )
        elif status == "not_found":
            raw = result.get("raw_tags", [])
            if raw:
                self.musicbrainz_status_label.config(text=f"MusicBrainz returned tags, but no clean playlist suggestions: {', '.join(raw[:12])}")
            else:
                self.musicbrainz_status_label.config(text="No useful MusicBrainz genre/tag suggestions found for this track.")
        elif status == "error":
            self.musicbrainz_status_label.config(text=f"MusicBrainz error: {result.get('error', 'unknown error')}")
        else:
            self.musicbrainz_status_label.config(text="Suggestions cleared.")

        suggestions = self.refresh_musicbrainz_suggestions_against_current_sorted_tree(result.get("suggestions", []) or [])
        for suggestion in suggestions:
            name = suggestion.get("name", "")
            if not name:
                continue
            path = tuple(suggestion.get("playlist_path") or [name])
            exists = bool(suggestion.get("playlist_exists"))
            confidence = suggestion.get("confidence", 0)
            var = tk.BooleanVar(value=confidence >= 60)
            self.musicbrainz_suggestion_vars[name] = {
                "var": var,
                "suggestion": suggestion,
                "playlist_path": path,
            }

            target = "SORTED/" + "/".join(path)
            status_text = "existing playlist" if exists else "new pending playlist"
            source_tags = suggestion.get("source_tags", [])
            tag_text = f" | tags: {', '.join(source_tags)}" if source_tags else ""

            ttk.Checkbutton(
                self.musicbrainz_suggestions_frame,
                text=f"{confidence:3d}%  {name} → {target} ({status_text}){tag_text}",
                variable=var,
            ).pack(anchor="w", pady=2)

        raw_tags = result.get("raw_tags", []) or []
        if raw_tags:
            raw_label = ttk.Label(
                self.musicbrainz_suggestions_frame,
                text="Raw MusicBrainz tags: " + ", ".join(raw_tags[:18]),
                wraplength=500
            )
            raw_label.pack(anchor="w", pady=(8, 2))

    def render_musicbrainz_debug(self, result):
        if not hasattr(self, "musicbrainz_debug_text"):
            return

        lines = []
        if result:
            lines.extend(result.get("debug", []) or [])

            sources = result.get("source_recordings", []) or []
            if sources:
                lines.append("")
                lines.append("Source recordings considered:")
                for src in sources[:8]:
                    lines.append(
                        f"  score={src.get('score')} | mode={src.get('search_mode')} | "
                        f"{src.get('artist') or 'unknown artist'} - {src.get('title')} | {src.get('id')}"
                    )

            unmapped = result.get("unmapped_tags", []) or []
            if unmapped:
                lines.append("")
                lines.append("Tags returned but not used as playlist suggestions:")
                lines.append("  " + ", ".join(unmapped[:40]))

        if not lines:
            lines = ["No MusicBrainz lookup has been run for this track yet."]

        self.musicbrainz_debug_text.configure(state="normal")
        self.musicbrainz_debug_text.delete("1.0", tk.END)
        self.musicbrainz_debug_text.insert(tk.END, "\n".join(lines))
        self.musicbrainz_debug_text.configure(state="disabled")

    def sort_clear_musicbrainz_suggestions(self, silent=False):
        self.current_musicbrainz_suggestions = []
        self.current_musicbrainz_result = None
        self.musicbrainz_suggestion_vars = {}
        if hasattr(self, "musicbrainz_suggestions_frame"):
            for widget in self.musicbrainz_suggestions_frame.winfo_children():
                widget.destroy()
        if hasattr(self, "musicbrainz_debug_text"):
            self.musicbrainz_debug_text.configure(state="normal")
            self.musicbrainz_debug_text.delete("1.0", tk.END)
            self.musicbrainz_debug_text.insert(tk.END, "Suggestions cleared. Run Suggest genres to see exact lookup debug.\n")
            self.musicbrainz_debug_text.configure(state="disabled")
        if not silent and hasattr(self, "musicbrainz_status_label"):
            self.musicbrainz_status_label.config(text="Suggestions cleared.")


    def sort_apply_selected_musicbrainz_suggestions(self):
        selected = [
            data for data in self.musicbrainz_suggestion_vars.values()
            if data["var"].get()
        ]

        if not selected:
            messagebox.showinfo("No suggestions selected", "Tick at least one suggestion first.")
            return

        created_paths = []
        selected_paths = []

        for data in selected:
            suggestion = data.get("suggestion", {})
            refreshed = self.refresh_musicbrainz_suggestions_against_current_sorted_tree([suggestion])
            if refreshed:
                path = tuple(refreshed[0].get("playlist_path") or data.get("playlist_path") or [])
            else:
                path = tuple(data.get("playlist_path") or [])
            if not path:
                continue

            node = self.sorted_nodes_by_path.get(path)
            if node is None:
                # Create as a pending playlist under SORTED. If you want hierarchy,
                # manually create the folders/playlists on the right and rerun suggestions.
                node = {
                    "id": None,
                    "name": path[-1],
                    "path": path,
                    "depth": len(path) - 1,
                    "is_folder": False,
                    "is_existing": False,
                    "parent_path": tuple(path[:-1]),
                }
                self.sorted_nodes.append(node)
                self.sorted_nodes_by_path[path] = node
                created_paths.append(path)

            if not node.get("is_folder"):
                selected_paths.append(path)

        self.sorted_nodes.sort(key=lambda n: (n["path"], not n["is_folder"]))
        self.render_sort_playlist_tree()

        # Tick the matching playlists for the current track. Existing manual ticks remain ticked.
        selected_path_set = set(selected_paths)
        for path, data in self.sort_playlist_vars.items():
            if tuple(path) in selected_path_set:
                data["var"].set(True)

        self.sort_save_current_choices()
        self.render_sort_summary()

        if created_paths:
            messagebox.showinfo(
                "Suggestions applied",
                "Created pending SORTED playlist(s):\n" + "\n".join("SORTED/" + "/".join(p) for p in created_paths)
            )
    async def apply_sorting_actions(self):
        print("\n=== APPLYING SORTING CHANGES ===")
        await self.ensure_sorted_root_folder()

        # Ensure every folder/playlist path exists and fill node ids.
        await self.ensure_sorted_nodes_exist()

        added = 0
        failed_adds = []
        genre_updates = 0
        failed_genres = []

        playlist_lookup = self.sorted_playlist_name_lookup()

        for action in self.sorting_actions.values():
            track = action["track"]
            track_id = action["track_id"]
            playlist_paths = list(action.get("playlist_paths") or [])

            # Safety fallback: if the GUI/checkbox state somehow saved the genre text
            # but lost playlist_paths, recover the intended playlists by matching each
            # genre token against existing SORTED playlists. This prevents the exact
            # failure mode where Genre is updated but playlist additions stay at 0.
            if not playlist_paths and action.get("genre_text"):
                recovered_paths = []
                for name in re.split(r"[;|]", action.get("genre_text", "")):
                    name = name.strip()
                    if not name:
                        continue
                    matched = self.find_best_sorted_playlist_path(name, playlist_lookup=playlist_lookup)
                    if matched:
                        recovered_paths.append(tuple(matched))

                playlist_paths = sorted(set(recovered_paths))
                if playlist_paths:
                    action["playlist_paths"] = playlist_paths
                    print(
                        f"Recovered playlist paths for {track_id} from genre text "
                        f"{action.get('genre_text')!r}: "
                        f"{['SORTED/' + '/'.join(p) for p in playlist_paths]}"
                    )

            for playlist_path in playlist_paths:
                playlist_path = tuple(playlist_path)
                node = self.resolve_sorted_playlist_node(playlist_path)
                if not node:
                    print(f"Skipping missing playlist path for {track_id}: SORTED/{'/'.join(playlist_path)}")
                    print(f"  Known SORTED playlist paths: {self.sorted_playlist_path_debug_sample()}")
                    continue
                if node.get("is_folder"):
                    print(f"Skipping folder path for {track_id}: SORTED/{'/'.join(playlist_path)}")
                    continue
                if not node.get("id"):
                    print(f"Skipping playlist without database id for {track_id}: SORTED/{'/'.join(playlist_path)}")
                    continue
                try:
                    await self.db.add_track_to_playlist(str(node["id"]), str(track_id))
                    added += 1
                    actual_path = tuple(node.get("path") or playlist_path)
                    print(f"Added {track_id} to SORTED/{'/'.join(actual_path)}")
                except Exception as exc:
                    failed_adds.append({"track_id": track_id, "playlist": playlist_path, "error": str(exc)})
                    print(f"Failed to add {track_id} to SORTED/{'/'.join(playlist_path)}: {exc}")

            metadata_override = action.get("metadata_override") or {}
            if metadata_override:
                try:
                    await self.set_track_basic_metadata(track_id, metadata_override)
                    print(f"Updated metadata for {track_id}: {metadata_override}")
                except Exception as exc:
                    print(f"Failed to update metadata for {track_id}: {exc}")

            genre_text = action.get("genre_text", "")
            if genre_text:
                try:
                    await self.set_track_genre(track_id, genre_text)
                    genre_updates += 1
                    print(f"Set genre for {track_id}: {genre_text}")
                except Exception as exc:
                    failed_genres.append({"track_id": track_id, "genre": genre_text, "error": str(exc)})
                    print(f"Failed to set genre for {track_id}: {exc}")

            self.mark_sorting_action_processed(action)

        if hasattr(self.db, "_invalidate_content_cache"):
            try:
                self.db._invalidate_content_cache()
            except Exception:
                pass

        print(f"Playlist additions completed: {added}")
        print(f"Playlist addition failures: {len(failed_adds)}")
        print(f"Genre updates completed: {genre_updates}")
        print(f"Genre update failures: {len(failed_genres)}")
        print("=== SORTING CHANGES FINISHED ===")

        messagebox.showinfo(
            "Sorting finished",
            "Sorting changes finished.\n\n"
            f"Playlist additions completed: {added}\n"
            f"Playlist addition failures: {len(failed_adds)}\n"
            f"Genre updates completed: {genre_updates}\n"
            f"Genre update failures: {len(failed_genres)}\n\n"
            "Check the terminal for details."
        )

        try:
            export_now = messagebox.askyesno(
                "Export to Serato?",
                "Sorting changes are done. Export the SORTED playlists to Serato crates now?"
            )
            if export_now:
                self.sort_export_sorted_to_serato_prompt()
        except Exception:
            pass

    def sorted_playlist_path_debug_sample(self, limit=20):
        paths = []
        for node in getattr(self, "sorted_nodes", []):
            if node.get("is_folder"):
                continue
            path = tuple(node.get("path") or [])
            if path:
                paths.append("SORTED/" + "/".join(path))
        paths = sorted(set(paths))
        shown = paths[:limit]
        if len(paths) > limit:
            shown.append(f"+{len(paths) - limit} more")
        return shown

    def resolve_sorted_playlist_node(self, requested_path):
        """Return a concrete existing playlist node for a requested SORTED path.

        Hard defensive resolver for the apply phase.

        The previous version could print both of these at the same time:
            Skipping missing playlist path: SORTED/DANCE/GARAGE
            Known SORTED playlist paths: ['SORTED/DANCE/GARAGE']

        That means the node existed in ``self.sorted_nodes`` but the dictionary
        key lookup in ``self.sorted_nodes_by_path`` did not match the key shape
        used by the action. This resolver therefore does NOT trust only the dict.
        It compares normalised full path strings against both the dict and the
        node list, then aliases the requested tuple back into the dict once found.
        """
        requested_path = tuple(str(part).strip() for part in (requested_path or []) if str(part).strip())
        if not requested_path:
            return None

        def path_key(path):
            return "/".join(
                self.normalise_playlist_name_for_match(part)
                for part in tuple(path or [])
            )

        requested_key = path_key(requested_path)

        # 1) Exact tuple lookup.
        node = getattr(self, "sorted_nodes_by_path", {}).get(requested_path)
        if node and not node.get("is_folder") and node.get("id"):
            return node

        # 2) Scan dictionary values/keys by normalised full path.
        for key, candidate in list(getattr(self, "sorted_nodes_by_path", {}).items()):
            candidate_path = tuple(candidate.get("path") or key or [])
            if path_key(candidate_path) == requested_key and not candidate.get("is_folder") and candidate.get("id"):
                self.sorted_nodes_by_path[requested_path] = candidate
                return candidate

        # 3) Scan visible loaded nodes by normalised full path.
        for candidate in getattr(self, "sorted_nodes", []):
            candidate_path = tuple(candidate.get("path") or [])
            if path_key(candidate_path) == requested_key and not candidate.get("is_folder") and candidate.get("id"):
                self.sorted_nodes_by_path[requested_path] = candidate
                return candidate

        # 4) Fall back to final-name match, but only if it is unambiguous.
        target_name = self.normalise_playlist_name_for_match(requested_path[-1])
        name_matches = []
        for candidate in getattr(self, "sorted_nodes", []):
            if candidate.get("is_folder") or not candidate.get("id"):
                continue
            candidate_path = tuple(candidate.get("path") or [])
            candidate_name = candidate.get("name") or (candidate_path[-1] if candidate_path else "")
            if self.normalise_playlist_name_for_match(candidate_name) == target_name:
                name_matches.append(candidate)

        if len(name_matches) == 1:
            self.sorted_nodes_by_path[requested_path] = name_matches[0]
            return name_matches[0]

        if len(name_matches) > 1:
            # Prefer one with the same parent path if available.
            requested_parent_key = path_key(requested_path[:-1])
            parent_matches = [
                candidate for candidate in name_matches
                if path_key(tuple(candidate.get("path") or [])[:-1]) == requested_parent_key
            ]
            if len(parent_matches) == 1:
                self.sorted_nodes_by_path[requested_path] = parent_matches[0]
                return parent_matches[0]

        return None

    def find_existing_sorted_playlist_node(self, name, want_folder=False):
        """Find a REAL existing node under SORTED by final display name.

        Important:
        pending GUI-created nodes also live in ``self.sorted_nodes`` before Apply.
        They have ``id=None``. The old version accidentally returned those pending
        nodes as if they already existed, which produced misleading logs like:

            Using existing playlist SORTED/test/test for requested SORTED/test/test
            Skipping missing playlist path for ... SORTED/test/test

        This version only returns nodes that already have a concrete database id.
        """
        target = self.normalise_playlist_name_for_match(name)
        candidates = []
        for node in getattr(self, "sorted_nodes", []):
            # Only real database-backed rows count as "existing".
            if not node.get("id"):
                continue
            if not node.get("is_existing", False):
                continue
            if bool(node.get("is_folder")) != bool(want_folder):
                continue

            node_name = node.get("name") or (node.get("path") or [""])[-1]
            if self.normalise_playlist_name_for_match(node_name) == target:
                candidates.append(node)

        if not candidates:
            return None

        # Prefer the deepest match so SORTED/RNB/R&B wins over SORTED/R&B if both exist.
        return sorted(
            candidates,
            key=lambda n: (len(n.get("path", ())), n.get("path", ())),
            reverse=True,
        )[0]

    def normalise_playlist_name_for_match(self, name):
        text = str(name or "").casefold()
        text = text.replace("&", "and")
        text = re.sub(r"[^a-z0-9]+", "", text)
        aliases = {
            "rnb": "randb",
            "rn b": "randb",
            "randb": "randb",
            "hiphop": "hiphop",
            "hiphoprap": "hiphop",
            "dnb": "drumandbass",
            "drumnbass": "drumandbass",
        }
        return aliases.get(text, text)

    async def ensure_sorted_nodes_exist(self):
        """Create any new folders/playlists from the GUI, parents first.

        Important bug fix:
        the old version refreshed ``self.sorted_nodes`` before creating pending
        GUI-created nodes. That wiped out every node with ``id=None``, so the
        apply phase updated Genre text but never created playlists or added
        tracks. This version snapshots pending nodes, reloads the real Rekordbox
        tree, then re-attaches and creates the missing pending paths.
        """
        # Preserve pending folders/playlists that only exist in the GUI so far.
        pending_nodes = []
        for node in getattr(self, "sorted_nodes", []):
            if not node.get("id") or not node.get("is_existing", False):
                pending_nodes.append(dict(node))

        # Refresh existing tree from Rekordbox without losing the snapshot above.
        await self.load_sorted_playlist_tree()

        # Re-attach pending nodes that still do not exist after refresh.
        for node in pending_nodes:
            path = tuple(node.get("path") or [])
            if not path:
                continue
            existing = self.find_existing_sorted_playlist_node(path[-1], want_folder=bool(node.get("is_folder")))
            if existing:
                # Prefer any existing playlist/folder with the same final name,
                # but also alias the originally requested GUI path to that row.
                self.sorted_nodes_by_path[tuple(existing["path"])] = existing
                self.sorted_nodes_by_path[path] = existing
                continue
            if path not in self.sorted_nodes_by_path:
                node["id"] = None
                node["is_existing"] = False
                node["parent_path"] = tuple(path[:-1])
                node["depth"] = len(path) - 1
                self.sorted_nodes.append(node)
                self.sorted_nodes_by_path[path] = node

        # Create missing nodes in path-depth order, creating parent folders first.
        for node in sorted(list(self.sorted_nodes), key=lambda n: (len(n["path"]), n["path"], not n.get("is_folder", False))):
            if node.get("id"):
                continue

            path = tuple(node.get("path") or [])
            if not path:
                continue

            # One final duplicate check by final name before creating a new row.
            existing = self.find_existing_sorted_playlist_node(path[-1], want_folder=bool(node.get("is_folder")))
            if existing:
                node.update(existing)
                self.sorted_nodes_by_path[tuple(existing["path"])] = existing
                self.sorted_nodes_by_path[path] = existing
                print(f"Using existing {'folder' if existing['is_folder'] else 'playlist'} SORTED/{'/'.join(existing['path'])} for requested SORTED/{'/'.join(path)}")
                continue

            parent_path = tuple(node.get("parent_path", tuple(path[:-1])))
            parent_id = self.sorted_root_id
            if parent_path:
                parent_node = self.sorted_nodes_by_path.get(parent_path)
                if parent_node is None or not parent_node.get("id"):
                    parent_id = await self.ensure_sorted_path(parent_path, is_folder=True)
                else:
                    parent_id = parent_node["id"]

            new_id = await self.db.create_playlist(
                node["name"],
                parent_id=str(parent_id) if parent_id else None,
                is_folder=bool(node["is_folder"]),
            )
            node["id"] = str(new_id)
            node["is_existing"] = True
            self.sorted_nodes_by_path[path] = node
            print(f"Created {'folder' if node['is_folder'] else 'playlist'} SORTED/{'/'.join(path)}: {new_id}")

        # Do not blindly reload here: some rekordbox/pyrekordbox builds report
        # folder attributes oddly immediately after creation, which can make the
        # freshly-existing child playlist disappear from the walked tree. The
        # in-memory index above now has the concrete database ids needed for the
        # add loop.

    async def ensure_sorted_path(self, path_tuple, is_folder=True):
        """Ensure a folder path exists under SORTED; returns final folder id."""
        await self.load_sorted_playlist_tree()
        parent_id = self.sorted_root_id
        built = []
        for part in path_tuple:
            built.append(part)
            cur_path = tuple(built)
            node = self.sorted_nodes_by_path.get(cur_path)
            if node and node.get("id"):
                parent_id = node["id"]
                continue
            parent_path = tuple(built[:-1])
            new_id = await self.db.create_playlist(part, parent_id=str(parent_id) if parent_id else None, is_folder=True)
            node = {
                "id": str(new_id),
                "name": part,
                "path": cur_path,
                "depth": len(cur_path) - 1,
                "is_folder": True,
                "is_existing": True,
                "parent_path": parent_path,
            }
            self.sorted_nodes.append(node)
            self.sorted_nodes_by_path[cur_path] = node
            parent_id = str(new_id)
        return parent_id

    async def set_track_basic_metadata(self, track_id, metadata):
        """
        Best-effort write-back for corrected artist/title/album/year/comments.

        This is deliberately conservative: blank fields are ignored, and genre is
        still controlled by selected SORTED playlists via set_track_genre().
        """
        metadata = dict(metadata or {})

        # Prefer a wrapper method if you later add one.
        if hasattr(self.db, "update_track_metadata"):
            result = self.db.update_track_metadata(str(track_id), metadata)
            if hasattr(result, "__await__"):
                return await result
            return result

        def _inner():
            if not hasattr(self.db, "db") or self.db.db is None:
                raise RuntimeError("Raw pyrekordbox db object is unavailable; cannot update metadata directly.")

            if hasattr(self.db, "_create_backup"):
                self.db._create_backup()

            content = self.db.db.get_content(ID=int(track_id))
            if not content:
                raise RuntimeError(f"Track ID not found: {track_id}")

            artist = (metadata.get("artist") or "").strip()
            title = (metadata.get("title") or "").strip()
            album = (metadata.get("album") or "").strip()
            comments = (metadata.get("comments") or "").strip()
            year_raw = metadata.get("year")

            if title:
                content.Title = title

            if comments:
                # Rekordbox/pyrekordbox uses Commnt in this wrapper.
                content.Commnt = comments

            if year_raw not in [None, ""]:
                try:
                    content.ReleaseYear = int(str(year_raw)[:4])
                except (TypeError, ValueError):
                    pass

            if artist:
                artist_row = None
                if hasattr(self.db, "_resolve_or_create"):
                    artist_row = self.db._resolve_or_create("get_artist", "add_artist", artist)
                else:
                    try:
                        existing = self.db.db.get_artist(Name=artist)
                        artist_row = existing.first() if hasattr(existing, "first") else next(iter(existing), None)
                    except Exception:
                        artist_row = None
                    if artist_row is None and hasattr(self.db.db, "add_artist"):
                        artist_row = self.db.db.add_artist(artist)
                if artist_row is not None and hasattr(artist_row, "ID"):
                    content.ArtistID = artist_row.ID

            if album:
                album_row = None
                try:
                    existing = self.db.db.get_album(Name=album)
                    album_row = existing.first() if hasattr(existing, "first") else next(iter(existing), None)
                except Exception:
                    album_row = None
                if album_row is None and hasattr(self.db.db, "add_album"):
                    try:
                        album_row = self.db.db.add_album(album)
                    except TypeError:
                        album_row = self.db.db.add_album(album, artist=None)
                if album_row is not None and hasattr(album_row, "ID"):
                    content.AlbumID = album_row.ID

            self.db.db.commit()
            if hasattr(self.db, "_invalidate_content_cache"):
                self.db._invalidate_content_cache()
            return True

        return await self.run_db_thread(_inner)


    async def set_track_genre(self, track_id, genre_name):
        """
        Set the rekordbox Genre field for a track.

        Rekordbox stores a single Genre relation. To support multiple playlist tags,
        this writes one semicolon-separated genre string such as:
            House; Tech House; Warm Up
        Smart playlists can then match with a contains rule.
        """
        if hasattr(self.db, "update_track_genre"):
            result = self.db.update_track_genre(str(track_id), str(genre_name))
            if hasattr(result, "__await__"):
                return await result
            return result

        def _inner():
            if not hasattr(self.db, "db") or self.db.db is None:
                raise RuntimeError("Raw pyrekordbox db object is unavailable; cannot set GenreID directly.")

            if hasattr(self.db, "_create_backup"):
                self.db._create_backup()

            content = self.db.db.get_content(ID=int(track_id))
            if not content:
                raise RuntimeError(f"Track ID not found: {track_id}")

            genre_row = None
            if hasattr(self.db, "_resolve_or_create"):
                genre_row = self.db._resolve_or_create("get_genre", "add_genre", genre_name)
            else:
                try:
                    existing = self.db.db.get_genre(Name=genre_name)
                    genre_row = existing.first() if hasattr(existing, "first") else next(iter(existing), None)
                except Exception:
                    genre_row = None
                if genre_row is None:
                    genre_row = self.db.db.add_genre(genre_name)

            if genre_row is None:
                raise RuntimeError(f"Could not resolve/create genre: {genre_name}")

            content.GenreID = genre_row.ID
            self.db.db.commit()
            if hasattr(self.db, "_invalidate_content_cache"):
                self.db._invalidate_content_cache()
            return True

        return await self.run_db_thread(_inner)

    async def run_db_thread(self, func):
        import asyncio
        return await asyncio.to_thread(func)

    # ------------------------------------------------------------------
    # Utilities
    # ------------------------------------------------------------------

    def play_audio_file(self, path):
        """Play audio inside the Python/Tkinter process instead of opening an external app."""
        self.embedded_play_audio_file(path, auto=False)

    def file_size_bytes(self, path):
        try:
            return Path(path).stat().st_size
        except Exception:
            return 0

    def file_size_label(self, path):
        size = self.file_size_bytes(path)
        if size <= 0:
            return "size unknown"
        return self.human_size(size)

    def human_size(self, size_bytes):
        size = float(size_bytes)
        units = ["B", "KB", "MB", "GB", "TB"]

        for unit in units:
            if size < 1024 or unit == units[-1]:
                if unit == "B":
                    return f"{int(size)} {unit}"
                return f"{size:.1f} {unit}"
            size /= 1024

        return f"{size_bytes} B"

    def finish(self):
        if not self.queued_fixes:
            self.root.destroy()
            return

        files_to_delete = set()
        bytes_to_delete = 0

        for fix in self.queued_fixes:
            for path in fix["selected_duplicate_paths"]:
                if path not in files_to_delete:
                    files_to_delete.add(path)
                    bytes_to_delete += self.file_size_bytes(path)

        confirmed = messagebox.askyesno(
            "Apply destructive storage changes?",
            "This will mutate Rekordbox playlists and PERMANENTLY DELETE "
            "the ticked duplicate physical files from disk.\n\n"
            f"Physical files queued for deletion: {len(files_to_delete)}\n"
            f"Estimated storage saved: {self.human_size(bytes_to_delete)}\n\n"
            "Repeated appearances of the same file across playlists are not treated "
            "as storage duplicates. Only separate physical files you ticked will be deleted.\n\n"
            "This strict version blocks same-title-only matches unless there is also "
            "strong artist/size evidence.\n\n"
            "Saved NOT duplicate choices persist in:\n"
            f"{self.ignore_file}\n\n"
            "Close Rekordbox and make a backup first.\n\n"
            "Continue?"
        )

        if confirmed:
            self.root.destroy()
