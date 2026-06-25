from __future__ import annotations

import csv
import os
import queue
import shutil
import subprocess
import sys
import threading
import time
from datetime import datetime
import tkinter as tk
from pathlib import Path
from tkinter import messagebox, ttk
from typing import Any

from loaders import save_state
from models import SearchResult, Track
from parser import make_queries
from scoring import score_result
from rekordbox_integration import RekordboxIntegration, RekordboxTrackRef
from sockseek_client import (
    SockseekClient,
    build_slsk_link,
    fields,
    flatten,
    is_audio,
    is_private_or_locked,
    extract_slsk,
)


class App(tk.Tk):
    def __init__(self, tracks: list[Track], client: SockseekClient, state_path: Path, rekordbox_root: str | Path | None = None):
        super().__init__()
        self.title('Sockseek DJ Version Picker')
        self.geometry('1550x900')
        self.minsize(1100, 720)

        self.tracks = tracks
        self.client = client
        self.state_path = state_path
        self.index = 0
        self.results_by_track: dict[str, list[SearchResult]] = {}
        self.worker_queue: queue.Queue = queue.Queue()
        self.busy = False
        self.search_counter = 0
        self.active_search_id: str | None = None
        self.debug_log_path = Path.cwd() / 'log.txt'
        self.training_log_path = Path.cwd() / 'selection_training_log.csv'
        self.preview_dir = Path.cwd() / '_sockseek_preview_limbo'
        self.preview_dir.mkdir(parents=True, exist_ok=True)
        self.preview_files_by_key: dict[str, list[Path]] = {}
        self.last_preview_result_key: str | None = None
        self.unavailable_users_path = Path.cwd() / 'unavailable_users.txt'
        self.unavailable_users: set[str] = self.load_unavailable_users()
        self.rekordbox = RekordboxIntegration(rekordbox_root) if rekordbox_root else None
        self.not_downloaded_report_path = Path.cwd() / 'not_downloaded_tracks.csv'
        self.explicit_popup_seen: set[str] = set()

        self.rb_ignored_tracks = set()
        self.rb_checking_track_ids = set()
        self.rb_matches_by_track = {}
        self.rb_selected_match_by_track = {}
        self.rb_playlist_cache = None
        self.rb_default_playlist_name = ''
        self._rendering_current = False
        self._metadata_refresh_after_id = None
        
        self.create_widgets()
        self.bind_shortcuts()
        self.render_current()
        self.after(100, self.poll_worker)

    def current(self) -> Track:
        return self.tracks[self.index]

    def create_widgets(self) -> None:
        self.columnconfigure(0, weight=1)
        self.rowconfigure(4, weight=1)

        header = ttk.Frame(self)
        header.grid(row=0, column=0, sticky='ew', padx=12, pady=(10, 4))
        header.columnconfigure(0, weight=1)
        self.track_label = ttk.Label(header, font=('Arial', 16, 'bold'), wraplength=1150)
        self.track_label.grid(row=0, column=0, sticky='w')
        self.status_label = ttk.Label(header, font=('Arial', 10))
        self.status_label.grid(row=0, column=1, sticky='e')
        self.explicit_label = ttk.Label(header, font=('Arial', 11, 'bold'))
        self.explicit_label.grid(row=1, column=0, columnspan=2, sticky='w', pady=(3, 0))

        meta = ttk.LabelFrame(self, text='Current track')
        meta.grid(row=1, column=0, sticky='ew', padx=12, pady=4)
        meta.columnconfigure(1, weight=1)
        meta.columnconfigure(3, weight=1)

        self.raw_var = tk.StringVar()
        self.artist_var = tk.StringVar()
        self.title_var = tk.StringVar()
        self.album_var = tk.StringVar()
        self.query_var = tk.StringVar()
        for _var in (self.raw_var, self.artist_var, self.title_var, self.album_var):
            _var.trace_add('write', self.on_track_metadata_edit)

        rows = [
            ('Artist', self.artist_var, 'Title', self.title_var),
            ('Album', self.album_var, 'Manual query', self.query_var),
            ('Raw', self.raw_var, '', None),
        ]
        for r, (l1, v1, l2, v2) in enumerate(rows):
            ttk.Label(meta, text=l1, width=12).grid(row=r, column=0, sticky='w', padx=(8, 4), pady=3)
            ttk.Entry(meta, textvariable=v1).grid(row=r, column=1, sticky='ew', padx=(0, 10), pady=3)
            if v2 is not None:
                ttk.Label(meta, text=l2, width=12).grid(row=r, column=2, sticky='w', padx=(8, 4), pady=3)
                ttk.Entry(meta, textvariable=v2).grid(row=r, column=3, sticky='ew', padx=(0, 8), pady=3)

        rb_frame = ttk.LabelFrame(self, text='Rekordbox loose duplicate assistant')
        rb_frame.grid(row=2, column=0, sticky='ew', padx=12, pady=4)
        rb_frame.columnconfigure(0, weight=1)

        self.rb_status_var = tk.StringVar(value='Rekordbox: disabled. Pass --rekordbox-root to enable loose duplicate suggestions.')
        ttk.Label(rb_frame, textvariable=self.rb_status_var, font=('Arial', 10, 'bold')).grid(row=0, column=0, sticky='ew', padx=8, pady=(5, 2))

        rb_cols = ('score', 'track', 'playlists', 'path')
        self.rb_tree = ttk.Treeview(rb_frame, columns=rb_cols, show='headings', height=3, selectmode='browse')
        for col, text, width in (
            ('score', 'Match', 105),
            ('track', 'Possible existing Rekordbox track', 360),
            ('playlists', 'Already in playlists', 330),
            ('path', 'File path', 610),
        ):
            self.rb_tree.heading(col, text=text)
            self.rb_tree.column(col, width=width, minwidth=50, anchor='w')
        self.rb_tree.grid(row=1, column=0, sticky='ew', padx=(8, 4), pady=(2, 6))
        self.rb_tree.bind('<Double-Button-1>', lambda _e: self.play_selected_rekordbox_match())

        rb_buttons = ttk.Frame(rb_frame)
        rb_buttons.grid(row=1, column=1, sticky='ns', padx=(4, 8), pady=(2, 6))
        ttk.Button(rb_buttons, text='▶ Play selected RB', command=self.play_selected_rekordbox_match).pack(fill='x', pady=2)
        ttk.Button(rb_buttons, text='Use selected RB track', command=self.use_selected_rekordbox_match).pack(fill='x', pady=2)
        ttk.Button(rb_buttons, text='Ignore / download anyway', command=self.ignore_rekordbox_matches_for_track).pack(fill='x', pady=2)
        ttk.Button(rb_buttons, text='Search RB Again', command=self.manual_rekordbox_search).pack(fill='x', pady=2)
        ttk.Button(rb_buttons, text='Set default playlist', command=self.set_default_rekordbox_playlist).pack(fill='x', pady=2)
        ttk.Button(rb_buttons, text='Auto rescan RB', command=self.start_rekordbox_check_current).pack(fill='x', pady=2)

        actions = ttk.Frame(self)
        actions.grid(row=3, column=0, sticky='ew', padx=12, pady=6)
        primary = [
            ('◀ Previous', self.previous_track),
            ('Next ▶', self.next_track),
            ('Search selected query', self.search_selected_query),
            ('Search manual query', self.search_manual),
            ('▶ Play / preview selected', self.play_selected),
            ('⬇ Download selected', self.download_selected),
            ('✓ Keep preview', self.keep_preview_selected),
            ('✓ Mark downloaded', lambda: self.set_status('downloaded')),
            ('Skip', lambda: self.set_status('skipped')),
            ('Jump unfinished', self.jump_failed_pending),
        ]
        for text, cmd in primary:
            ttk.Button(actions, text=text, command=cmd).pack(side='left', padx=3)
        ttk.Button(actions, text='Save state', command=self.save_state).pack(side='right', padx=3)
        ttk.Button(actions, text='Export not downloaded', command=self.export_not_downloaded_report).pack(side='right', padx=3)

        paned = ttk.PanedWindow(self, orient='horizontal')
        paned.grid(row=4, column=0, sticky='nsew', padx=12, pady=4)

        left = ttk.LabelFrame(paned, text='1. Choose the search you want to try')
        left.columnconfigure(0, weight=1)
        left.rowconfigure(0, weight=1)
        paned.add(left, weight=1)

        self.query_list = tk.Listbox(left, height=16, exportselection=False)
        self.query_list.grid(row=0, column=0, sticky='nsew', padx=6, pady=6)
        qscroll = ttk.Scrollbar(left, orient='vertical', command=self.query_list.yview)
        qscroll.grid(row=0, column=1, sticky='ns', pady=6)
        self.query_list.configure(yscrollcommand=qscroll.set)
        self.query_list.bind('<Double-Button-1>', lambda _e: self.search_selected_query())

        qbuttons = ttk.Frame(left)
        qbuttons.grid(row=1, column=0, columnspan=2, sticky='ew', padx=6, pady=(0, 6))
        ttk.Button(qbuttons, text='Use in manual box', command=self.use_selected_query).pack(side='left', fill='x', expand=True, padx=2)
        ttk.Button(qbuttons, text='Previous query', command=self.previous_query).pack(side='left', fill='x', expand=True, padx=2)
        ttk.Button(qbuttons, text='Next query', command=self.next_query).pack(side='left', fill='x', expand=True, padx=2)

        right = ttk.LabelFrame(paned, text='2. Pick the best matching file')
        right.columnconfigure(0, weight=1)
        right.rowconfigure(0, weight=1)
        paned.add(right, weight=4)

        columns = ('play', 'score', 'tier', 'file', 'length', 'bitrate', 'size', 'user', 'slot', 'speed')
        self.result_tree = ttk.Treeview(right, columns=columns, show='headings', selectmode='browse')
        headings = {
            'play': ('Play', 70),
            'score': ('Score', 64),
            'tier': ('Tier', 110),
            'file': ('Filename', 570),
            'length': ('Length', 75),
            'bitrate': ('Bitrate', 75),
            'size': ('Size', 80),
            'user': ('User', 150),
            'slot': ('Free slot', 75),
            'speed': ('Speed', 90),
        }
        for col, (text, width) in headings.items():
            self.result_tree.heading(col, text=text)
            self.result_tree.column(col, width=width, minwidth=45, anchor='w')
        self.result_tree.grid(row=0, column=0, sticky='nsew', padx=(6, 0), pady=6)
        rscroll = ttk.Scrollbar(right, orient='vertical', command=self.result_tree.yview)
        rscroll.grid(row=0, column=1, sticky='ns', padx=(0, 6), pady=6)
        self.result_tree.configure(yscrollcommand=rscroll.set)
        self.result_tree.bind('<Double-Button-1>', lambda _e: self.download_selected())
        self.result_tree.bind('<ButtonRelease-1>', self.on_result_click)
        self.result_tree.bind('<<TreeviewSelect>>', lambda _e: self.render_selected_details())

        detail = ttk.LabelFrame(self, text='Selected result details')
        detail.grid(row=5, column=0, sticky='ew', padx=12, pady=4)
        detail.columnconfigure(0, weight=1)
        self.details_var = tk.StringVar(value='Select a candidate to see the full path here. Double-click a result to download it.')
        ttk.Label(detail, textvariable=self.details_var, wraplength=1450).grid(row=0, column=0, sticky='ew', padx=8, pady=5)

        bottom = ttk.LabelFrame(self, text='Log')
        bottom.grid(row=6, column=0, sticky='ew', padx=12, pady=(4, 10))
        bottom.columnconfigure(0, weight=1)
        self.log = tk.Text(bottom, height=9, wrap='word')
        self.log.grid(row=0, column=0, sticky='ew', padx=(6, 0), pady=6)
        lscroll = ttk.Scrollbar(bottom, orient='vertical', command=self.log.yview)
        lscroll.grid(row=0, column=1, sticky='ns', padx=(0, 6), pady=6)
        self.log.configure(yscrollcommand=lscroll.set)

    def bind_shortcuts(self) -> None:
        self.bind('<Control-s>', lambda _e: self.save_state())
        self.bind('<Control-f>', lambda _e: self.search_manual())
        self.bind('<Return>', lambda _e: self.search_selected_query())
        self.bind('<Control-d>', lambda _e: self.download_selected())
        self.bind('<Right>', lambda _e: self.next_track())
        self.bind('<Left>', lambda _e: self.previous_track())

    def load_unavailable_users(self) -> set[str]:
        if not self.unavailable_users_path.exists():
            return set()
        try:
            return {line.strip() for line in self.unavailable_users_path.read_text(encoding='utf-8').splitlines() if line.strip() and not line.startswith('#')}
        except Exception:
            return set()

    def save_unavailable_users(self) -> None:
        try:
            self.unavailable_users_path.write_text('\n'.join(sorted(self.unavailable_users)) + ('\n' if self.unavailable_users else ''), encoding='utf-8')
        except Exception as exc:
            self.write_debug(f'Could not save unavailable users: {exc}')

    def mark_user_unavailable(self, username: str, reason: str = '') -> None:
        username = (username or '').strip()
        if not username:
            return
        if username not in self.unavailable_users:
            self.log_line(f'Marking user unavailable for this/session future searches: {username}' + (f' ({reason})' if reason else ''))
        self.unavailable_users.add(username)
        self.save_unavailable_users()
        removed = 0
        for track_id, results in list(self.results_by_track.items()):
            keep = [r for r in results if (r.username or '').strip() != username]
            removed += len(results) - len(keep)
            self.results_by_track[track_id] = keep
        if removed:
            self.log_line(f'Removed {removed} visible candidate(s) from unavailable user {username}.')
            self.render_results()

    def select_first_result_if_any(self) -> None:
        rows = self.result_tree.get_children()
        if rows:
            self.result_tree.selection_set(rows[0])
            self.result_tree.focus(rows[0])
            self.render_selected_details()

    def log_line(self, text: str) -> None:
        line = f'{time.strftime("%H:%M:%S")}  {text}'
        self.log.insert(tk.END, line + '\n')
        self.log.see(tk.END)
        self.write_debug(line)

    def write_debug(self, text: str) -> None:
        try:
            with self.debug_log_path.open('a', encoding='utf-8') as f:
                f.write(str(text) + '\n')
        except Exception:
            pass

    def update_track_from_fields(self) -> None:
        t = self.current()
        t.raw = self.raw_var.get().strip()
        t.artist = self.artist_var.get().strip()
        t.title = self.title_var.get().strip()
        t.album = self.album_var.get().strip()
        t.last_query = self.query_var.get().strip()

    def render_current(self) -> None:
        t = self.current()
        self.track_label.config(text=f'{self.index + 1}/{len(self.tracks)}  {t.artist} - {t.title}' + (f'  |  {t.album}' if t.album else ''))
        self._rendering_current = True
        try:
            self.raw_var.set(t.raw)
            self.artist_var.set(t.artist)
            self.title_var.set(t.title)
            self.album_var.set(t.album)
        finally:
            self._rendering_current = False

        self.render_query_choices(reset_manual=False)

        self.render_results()
        self.render_explicit_status(t)
        self.render_rekordbox_matches(t)
        self.render_status()
        self.details_var.set('Select a candidate to see the full path here. Double-click a result to download it.')
        self.log_line(f'Loaded: {t.raw}')
        self.start_rekordbox_check_current()

    def render_query_choices(self, reset_manual: bool = False) -> None:
        """Rebuild the generated Soulseek query ladder from current track fields.

        This is intentionally separate from render_current() so editing Artist/Title
        in the GUI immediately updates the constructed searches without changing
        track position or clearing current Soulseek results.
        """
        t = self.current()
        queries = make_queries(t)
        if t.query_index >= len(queries):
            t.query_index = 0
        if reset_manual:
            t.last_query = ''
        if reset_manual or not t.last_query:
            self.query_var.set(queries[t.query_index][1] if queries else t.title)

        self.query_list.delete(0, tk.END)
        for i, (tier, q) in enumerate(queries):
            prefix = '▶ ' if i == t.query_index else '  '
            self.query_list.insert(tk.END, f'{prefix}{i + 1}. {tier}: {q}')
        if queries:
            self.query_list.selection_clear(0, tk.END)
            self.query_list.selection_set(t.query_index)
            self.query_list.see(t.query_index)

    def on_track_metadata_edit(self, *_args) -> None:
        if self._rendering_current:
            return
        if self._metadata_refresh_after_id is not None:
            try:
                self.after_cancel(self._metadata_refresh_after_id)
            except Exception:
                pass
        self._metadata_refresh_after_id = self.after(350, self.apply_track_metadata_edits)

    def apply_track_metadata_edits(self) -> None:
        self._metadata_refresh_after_id = None
        t = self.current()
        old_identity = (t.artist, t.title, t.album, t.raw)
        self.update_track_from_fields()
        new_identity = (t.artist, t.title, t.album, t.raw)
        if old_identity == new_identity:
            return
        t.query_index = 0
        t.last_query = ''
        self.render_query_choices(reset_manual=True)
        self.track_label.config(text=f'{self.index + 1}/{len(self.tracks)}  {t.artist} - {t.title}' + (f'  |  {t.album}' if t.album else ''))

        # Any old RB suggestions were based on the previous metadata. Clear them
        # and start a fresh lightweight duplicate check after the edit settles.
        self.rb_matches_by_track.pop(t.id, None)
        self.rb_ignored_tracks.discard(t.id)
        self.render_rekordbox_matches(t)
        self.start_rekordbox_check_current()

    def render_explicit_status(self, track: Track) -> None:
        if track.explicit is True:
            self.explicit_label.config(text='Explicit: true')
        elif track.explicit is False:
            self.explicit_label.config(text='Explicit: false')
        else:
            self.explicit_label.config(text='Explicit: unknown')

    def maybe_show_explicit_popup(self, track: Track) -> None:
        return

    def render_results(self) -> None:
        selected = self.result_tree.selection()
        selected_iid = selected[0] if selected else None
        for row in self.result_tree.get_children():
            self.result_tree.delete(row)
        for i, r in enumerate(self.results_by_track.get(self.current().id, [])):
            self.result_tree.insert('', 'end', iid=str(i), values=(
                '▶ Play',
                round(r.score, 1),
                r.tier,
                self._clean_filename(r.filename),
                self.format_length(r.length),
                r.bitrate or '',
                r.size or '',
                r.username or '',
                r.has_free_slot if r.has_free_slot is not None else '',
                r.upload_speed or '',
            ))
        if selected_iid and selected_iid in self.result_tree.get_children():
            self.result_tree.selection_set(selected_iid)

    def _clean_filename(self, filename: str | None) -> str:
        if not filename:
            return ''
        return filename.replace('\\', '/').split('/')[-1]

    def format_length(self, value: str | int | None) -> str:
        try:
            seconds = int(str(value).strip())
            if seconds < 0:
                return ''
            return f'{seconds // 60}:{seconds % 60:02d}'
        except Exception:
            return str(value or '')

    def render_selected_details(self) -> None:
        result = self.selected_result()
        if not result:
            return
        filename = result.filename or ''
        self.details_var.set(f'{filename}    |    user={result.username}    |    query="{result.query}"')

    def render_status(self) -> None:
        t = self.current()
        states = ['pending', 'searched', 'downloaded', 'failed', 'skipped']
        counts = {s: sum(1 for x in self.tracks if x.status == s) for s in states}
        rb = 'RB check off' if self.rekordbox is None else ('RB loaded' if self.rekordbox.loaded else 'RB ready')
        if self.rb_default_playlist_name:
            rb += f' → {self.rb_default_playlist_name}'
        self.status_label.config(
            text=f'Current: {t.status}   |   '
                 f'Pending {counts["pending"]}  Searched {counts["searched"]}  '
                 f'Downloaded {counts["downloaded"]}  Failed {counts["failed"]}  Skipped {counts["skipped"]}  Hidden users {len(self.unavailable_users)}  |  {rb}'
        )

    def export_not_downloaded_report(self, silent: bool = False) -> None:
        """Write a simple CSV of anything still requiring manual follow-up."""
        try:
            with self.not_downloaded_report_path.open('w', encoding='utf-8', newline='') as f:
                writer = csv.writer(f)
                writer.writerow(['index', 'status', 'artist', 'title', 'album', 'last_query', 'spotify_url', 'selected_filename', 'selected_user'])
                for i, t in enumerate(self.tracks, start=1):
                    if t.status == 'downloaded':
                        continue
                    selected = t.selected_result or {}
                    writer.writerow([
                        i, t.status, t.artist, t.title, t.album, t.last_query, t.spotify_url,
                        selected.get('filename', '') if isinstance(selected, dict) else '',
                        selected.get('username', '') if isinstance(selected, dict) else '',
                    ])
            if not silent:
                self.log_line(f'Exported not-downloaded/manual follow-up list to {self.not_downloaded_report_path}')
        except Exception as exc:
            if not silent:
                messagebox.showerror('Export failed', str(exc))
            self.write_debug(f'Could not export not-downloaded report: {exc}')

    def confirm_rekordbox_duplicate_guard(self) -> bool:
        """Return True when a Soulseek download/preview should continue.

        The Rekordbox assistant is now informational only. If possible matches
        exist, they stay visible in the RB panel, but downloads/previews are not
        interrupted by a popup. Use "Use selected RB track" manually when you
        want to reuse an existing library copy.
        """
        if self.rekordbox is None:
            return True
        t = self.current()
        if t.id in self.rb_ignored_tracks:
            return True
        if t.id not in self.rb_matches_by_track:
            self.log_line('Checking Rekordbox for existing/similar tracks before downloading...')
            matches = self.rekordbox.find_similar(t.artist, t.title, limit=12)
            self.rb_matches_by_track[t.id] = matches
            self.render_rekordbox_matches(t)
        return True

    def choose_rekordbox_match(self, matches: list[tuple[float, RekordboxTrackRef, str]]) -> RekordboxTrackRef | None:
        win = tk.Toplevel(self)
        win.title('Choose existing Rekordbox track')
        win.geometry('900x430')
        win.transient(self)
        win.grab_set()
        ttk.Label(win, text='Select the existing Rekordbox track to use:', font=('Arial', 12, 'bold')).pack(anchor='w', padx=10, pady=(10, 4))
        frame = ttk.Frame(win)
        frame.pack(fill='both', expand=True, padx=10, pady=6)
        listbox = tk.Listbox(frame, height=12, exportselection=False)
        listbox.pack(side='left', fill='both', expand=True)
        scroll = ttk.Scrollbar(frame, orient='vertical', command=listbox.yview)
        scroll.pack(side='right', fill='y')
        listbox.configure(yscrollcommand=scroll.set)
        refs = [ref for _score, ref, _reason in matches]
        for score, ref, reason in matches:
            playlists = ', '.join(name for _pid, name in ref.playlists[:3])
            listbox.insert(tk.END, f'{score:.2f} | {ref.artist} - {ref.title} | {Path(ref.file_path).name} | {playlists} | {reason}')
        if refs:
            listbox.selection_set(0)
        chosen: dict[str, RekordboxTrackRef | None] = {'value': None}
        def ok() -> None:
            sel = listbox.curselection()
            if sel:
                chosen['value'] = refs[sel[0]]
            win.destroy()
        def cancel() -> None:
            win.destroy()
        btns = ttk.Frame(win)
        btns.pack(fill='x', padx=10, pady=8)
        ttk.Button(btns, text='Use selected existing track', command=ok).pack(side='right', padx=4)
        ttk.Button(btns, text='Cancel', command=cancel).pack(side='right', padx=4)
        win.wait_window()
        return chosen['value']

    def set_default_rekordbox_playlist(self) -> None:
        playlist_name = self.choose_rekordbox_playlist(
            title='Set default Rekordbox playlist',
            item_label='New downloads and accepted existing RB tracks will be added here automatically for the rest of this session.',
            action_text='Set default playlist',
            force_default=True,
        )
        if playlist_name:
            self.rb_default_playlist_name = playlist_name
            self.log_line(f'Rekordbox default playlist for this session: {playlist_name}')
            self.render_status()

    def choose_rekordbox_playlist(self, title: str, item_label: str, action_text: str, force_default: bool = False) -> str | None:
        """Return a playlist name, optionally saving it as the session default."""
        if self.rekordbox is None:
            return None
        names = self.rekordbox.playlist_names()
        win = tk.Toplevel(self)
        win.title(title)
        win.geometry('720x260')
        win.transient(self)
        win.grab_set()

        ttk.Label(win, text='Choose an existing playlist or type a new playlist name:').pack(anchor='w', padx=10, pady=(12, 4))
        value = tk.StringVar(value=self.rb_default_playlist_name)
        combo = ttk.Combobox(win, textvariable=value, values=names)
        combo.pack(fill='x', padx=10, pady=5)
        combo.focus()

        use_default_var = tk.BooleanVar(value=force_default or bool(self.rb_default_playlist_name))
        ttk.Checkbutton(
            win,
            text='Use this as the default playlist for the rest of this session',
            variable=use_default_var,
        ).pack(anchor='w', padx=10, pady=(2, 6))

        ttk.Label(win, text=item_label, wraplength=680).pack(anchor='w', padx=10, pady=5)
        result = {'ok': False}

        def ok() -> None:
            result['ok'] = True
            win.destroy()

        def cancel() -> None:
            win.destroy()

        buttons = ttk.Frame(win)
        buttons.pack(fill='x', padx=10, pady=8)
        ttk.Button(buttons, text=action_text, command=ok).pack(side='right', padx=4)
        ttk.Button(buttons, text='Cancel', command=cancel).pack(side='right', padx=4)
        win.wait_window()

        playlist_name = value.get().strip()
        if not result['ok'] or not playlist_name:
            return None
        if use_default_var.get():
            self.rb_default_playlist_name = playlist_name
            self.log_line(f'Rekordbox session default playlist set to: {playlist_name}')
        return playlist_name

    def offer_add_existing_to_playlist(self, ref: RekordboxTrackRef) -> None:
        if self.rekordbox is None:
            return
        playlist_name = self.rb_default_playlist_name or self.choose_rekordbox_playlist(
            title='Add existing track to Rekordbox playlist',
            item_label='Existing track: ' + ref.label,
            action_text='Add existing track to playlist',
            force_default=True,
        )
        if not playlist_name:
            self.log_line('Accepted existing Rekordbox track without adding it to a playlist because no playlist was selected.')
            return
        ok, msg = self.rekordbox.add_track_to_playlist(ref.id, playlist_name, create_missing=True)
        if ok:
            self.log_line(msg)
        else:
            self.log_line('Could not update Rekordbox: ' + msg)

    def manual_rekordbox_search(self) -> None:
        """Run a loose manual Rekordbox query when Spotify titles are messy."""
        if self.rekordbox is None:
            self.render_rekordbox_matches(self.current())
            return
        track = self.current()

        win = tk.Toplevel(self)
        win.title('Search Rekordbox Again')
        win.geometry('560x150')
        win.transient(self)
        win.grab_set()

        query_var = tk.StringVar(value=f'{track.artist} {track.title}'.strip())
        ttk.Label(win, text='Search Rekordbox for:').pack(anchor='w', padx=10, pady=(12, 4))
        entry = ttk.Entry(win, textvariable=query_var)
        entry.pack(fill='x', padx=10, pady=4)
        entry.focus()
        entry.select_range(0, tk.END)

        def run() -> None:
            query = query_var.get().strip()
            if not query:
                return
            self.rb_ignored_tracks.discard(track.id)
            self.rb_status_var.set('Rekordbox: manual search running...')
            try:
                matches = self.rekordbox.find_similar('', query, limit=25)
                self.rb_matches_by_track[track.id] = matches
                self.log_line(f'Manual Rekordbox search for "{query}" returned {len(matches)} match(es).')
            except Exception as exc:
                self.rb_matches_by_track[track.id] = []
                self.log_line(f'Manual Rekordbox search failed: {exc}')
            self.render_rekordbox_matches(track)
            win.destroy()

        entry.bind('<Return>', lambda _e: run())
        buttons = ttk.Frame(win)
        buttons.pack(fill='x', padx=10, pady=10)
        ttk.Button(buttons, text='Search RB', command=run).pack(side='right', padx=4)
        ttk.Button(buttons, text='Cancel', command=win.destroy).pack(side='right', padx=4)
        win.wait_window()

    def rb_match_label(self, score: float) -> str:
        if score >= 0.90:
            return f'Strong {score:.2f}'
        if score >= 0.76:
            return f'Possible {score:.2f}'
        return f'Weak {score:.2f}'

    def render_rekordbox_matches(self, track: Track | None = None) -> None:
        """Render existing Rekordbox copies for the current track.

        This is informational and manual: the app never silently skips a download.
        If a likely existing copy is found, you choose either:
        - Use selected RB track, optionally adding it to a playlist; or
        - Ignore / download anyway.
        """
        track = track or self.current()
        for row in self.rb_tree.get_children():
            self.rb_tree.delete(row)
        if self.rekordbox is None:
            self.rb_status_var.set('Rekordbox: disabled. Use --rekordbox-root "..\\rekordbox-mcp" to enable loose duplicate suggestions.')
            return
        if track.id in self.rb_ignored_tracks:
            self.rb_status_var.set('Rekordbox: matches ignored for this track. Downloads/previews will continue normally.')
            return
        if track.id in self.rb_checking_track_ids:
            self.rb_status_var.set('Rekordbox: checking library for existing copies...')
            return
        matches = self.rb_matches_by_track.get(track.id)
        if matches is None:
            self.rb_status_var.set('Rekordbox: not checked yet.')
            return
        if not matches:
            msg = 'Rekordbox: no possible existing copy found.'
            if self.rekordbox.error:
                msg += f' ({self.rekordbox.error})'
            self.rb_status_var.set(msg)
            return
        self.rb_status_var.set(f'Rekordbox: {len(matches)} possible existing copy/copies found. Use one, or ignore and download anyway.')
        for i, (score, ref, reason) in enumerate(matches, start=1):
            playlists = ', '.join(name for _pid, name in ref.playlists[:6])
            if len(ref.playlists) > 6:
                playlists += f', +{len(ref.playlists) - 6} more'
            self.rb_tree.insert('', 'end', iid=str(i - 1), values=(
                f'{self.rb_match_label(score)}',
                f'{ref.artist} - {ref.title}' + (f' | {ref.album}' if ref.album else ''),
                playlists,
                ref.file_path,
            ))
        rows = self.rb_tree.get_children()
        if rows:
            self.rb_tree.selection_set(rows[0])
            self.rb_tree.focus(rows[0])

    def start_rekordbox_check_current(self) -> None:
        if self.rekordbox is None:
            self.render_rekordbox_matches(self.current())
            return
        t = Track(**self.current().to_dict())
        if t.id in self.rb_checking_track_ids:
            return
        if t.id in self.rb_matches_by_track and t.id not in self.rb_ignored_tracks:
            self.render_rekordbox_matches(self.current())
            return
        self.rb_checking_track_ids.add(t.id)
        self.render_rekordbox_matches(t)
        threading.Thread(target=self.worker_rekordbox_check, args=(t,), daemon=True).start()

    def worker_rekordbox_check(self, track: Track) -> None:
        matches: list[tuple[float, RekordboxTrackRef, str]] = []
        error = ''
        try:
            if self.rekordbox is not None:
                matches = self.rekordbox.find_similar(track.artist, track.title, limit=12)
                error = self.rekordbox.error or ''
        except Exception as exc:
            error = str(exc)
        self.worker_queue.put(('rb_done', track.id, matches, error))

    def selected_rekordbox_match(self) -> RekordboxTrackRef | None:
        matches = self.rb_matches_by_track.get(self.current().id) or []
        sel = self.rb_tree.selection()
        if sel:
            try:
                idx = int(sel[0])
                if 0 <= idx < len(matches):
                    return matches[idx][1]
            except Exception:
                pass
        return matches[0][1] if matches else None

    def play_selected_rekordbox_match(self) -> None:
        ref = self.selected_rekordbox_match()
        if ref is None:
            self.log_line('No existing Rekordbox track selected to play.')
            return
        path = Path(ref.file_path or '')
        if not ref.file_path:
            self.log_line(f'Selected Rekordbox track has no file path: {ref.label}')
            return
        if not path.exists():
            self.log_line(f'Rekordbox file not found on disk: {path}')
            return
        self.log_line(f'Playing existing Rekordbox match: {ref.label}')
        self._open_audio_file(path)

    def use_selected_rekordbox_match(self) -> None:
        ref = self.selected_rekordbox_match()
        if ref is None:
            self.log_line('No existing Rekordbox track selected.')
            return
        # No extra confirmation popup here: selecting the row and pressing the
        # button is the confirmation. You still get the playlist chooser below.
        self.offer_add_existing_to_playlist(ref)
        t = self.current()
        t.status = 'downloaded'
        t.selected_result = {
            'source': 'rekordbox_existing',
            'filename': ref.file_path,
            'username': 'rekordbox',
            'track_id': ref.id,
        }
        self.save_state(silent=True)
        self.render_status()
        self.export_not_downloaded_report(silent=True)
        self.log_line(f'Accepted existing Rekordbox track instead of downloading: {ref.label}')

    def ignore_rekordbox_matches_for_track(self) -> None:
        self.rb_ignored_tracks.add(self.current().id)
        self.render_rekordbox_matches(self.current())
        self.log_line('Ignored Rekordbox existing-track suggestions for this track; download/preview will proceed normally.')


    def offer_add_downloaded_files_to_rekordbox_playlist(self, files: list[Path]) -> None:
        """Best-effort playlist add for newly downloaded files.

        No confirmation popup is shown when a session default playlist is set.
        This keeps the download workflow fast: set the playlist once, then every
        kept/downloaded file is attempted automatically. If no default is set,
        the file remains in the final download folder and the log explains what
        to do.
        """
        if self.rekordbox is None or not files:
            return
        playlist_name = self.rb_default_playlist_name
        if not playlist_name:
            self.log_line('Downloaded file not added to Rekordbox playlist because no session default playlist is set. Use "Set default playlist" first.')
            return
        ok, msg = self.rekordbox.add_file_to_playlist(str(files[0]), playlist_name, create_missing=True)
        if ok:
            self.log_line(msg)
        else:
            self.log_line('Could not add new downloaded file to Rekordbox automatically: ' + msg)

    def selected_result(self) -> SearchResult | None:
        sel = self.result_tree.selection()
        results = self.results_by_track.get(self.current().id, [])
        if not sel:
            return None
        i = int(sel[0])
        if i >= len(results):
            return None
        return results[i]

    def previous_track(self) -> None:
        self.update_track_from_fields()
        self.index = max(0, self.index - 1)
        self.render_current()

    def next_track(self) -> None:
        self.update_track_from_fields()
        self.index = min(len(self.tracks) - 1, self.index + 1)
        self.render_current()

    def next_query(self) -> None:
        self.update_track_from_fields()
        t = self.current()
        qs = make_queries(t)
        if not qs:
            return
        t.query_index = min(t.query_index + 1, max(0, len(qs) - 1))
        t.last_query = ''
        self.render_current()
        self.search_current()

    def previous_query(self) -> None:
        self.update_track_from_fields()
        t = self.current()
        t.query_index = max(0, t.query_index - 1)
        t.last_query = ''
        self.render_current()

    def selected_query(self) -> tuple[str, str] | None:
        self.update_track_from_fields()
        sel = self.query_list.curselection()
        selected_index = sel[0] if sel else self.current().query_index
        queries = make_queries(self.current())
        if selected_index >= len(queries):
            selected_index = 0
        self.current().query_index = selected_index
        self.render_query_choices(reset_manual=False)
        if not queries:
            return None
        return queries[selected_index]

    def use_selected_query(self) -> None:
        self.update_track_from_fields()
        self.render_query_choices(reset_manual=False)
        sq = self.selected_query()
        if not sq:
            return
        _, q = sq
        self.current().query_index = self.query_list.curselection()[0]
        self.query_var.set(q)

    def search_selected_query(self) -> None:
        sq = self.selected_query()
        if not sq:
            messagebox.showinfo('Pick query', 'Select a generated query first.')
            return
        self.current().query_index = self.query_list.curselection()[0]
        self.start_search(*sq)

    def search_current(self) -> None:
        self.update_track_from_fields()
        qs = make_queries(self.current())
        if not qs:
            return
        if self.current().query_index >= len(qs):
            self.current().query_index = 0
        self.start_search(*qs[self.current().query_index])

    def search_manual(self) -> None:
        self.update_track_from_fields()
        q = self.query_var.get().strip()
        if q:
            self.start_search('Manual', q)

    def start_search(self, tier: str, query: str) -> None:
        if self.busy:
            return
        self.update_track_from_fields()
        self.busy = True
        self.search_counter += 1
        track = Track(**self.current().to_dict())
        search_id = f'{track.id}:{self.search_counter}'
        self.active_search_id = search_id
        self.results_by_track[track.id] = []
        self.render_results()
        self.details_var.set('Searching... results will appear as Sockseek prints them.')
        self.log_line('')
        self.log_line('=' * 120)
        self.log_line(f'Searching: [{tier}] {query}')
        self.log_line(f'FULL DEBUG LOG: {self.debug_log_path}')
        threading.Thread(target=self.worker_search, args=(search_id, track, tier, query), daemon=True).start()

    def parse_upload_speed_mb(self, value: str) -> float:
        text = str(value or '').strip().lower().replace(' ', '')
        if not text:
            return 0.0
        import re
        m = re.search(r'(\d+(?:\.\d+)?)(kb|mb|gb)?/s', text)
        if not m:
            m = re.search(r'(\d+(?:\.\d+)?)(kb|mb|gb)?', text)
        if not m:
            return 0.0
        n = float(m.group(1))
        unit = m.group(2) or 'mb'
        if unit == 'kb':
            return n / 1024.0
        if unit == 'gb':
            return n * 1024.0
        return n

    def upload_speed_score_boost(self, value: str) -> float:
        mb = self.parse_upload_speed_mb(value)
        if mb <= 0:
            return 0.0
        # Small capped nudge only; relevance must still dominate.
        if mb >= 5:
            return 12.0
        if mb >= 2:
            return 8.0
        if mb >= 1:
            return 5.0
        if mb >= 0.5:
            return 3.0
        return 1.0

    def make_result(self, track: Track, tier: str, query: str, item: Any) -> SearchResult | None:
        f = fields(item)
        filename = f['filename']
        username = (f.get('username') or '').strip()
        if username and username in self.unavailable_users:
            self.write_debug(f'REJECT unavailable-user | tier={tier} | query={query} | user={username} | filename={filename}')
            return None
        if filename and not is_audio(filename):
            self.write_debug(f'REJECT non-audio | tier={tier} | query={query} | filename={filename} | raw={str(item)}')
            return None
        private, _reason = is_private_or_locked(item)
        if private:
            self.write_debug(f'REJECT private/locked | tier={tier} | query={query} | filename={filename} | raw={str(item)}')
            return None
        text = flatten(item)
        score = score_result(track, text, tier)
        if str(f.get('has_free_slot', '')).lower() == 'false':
            score -= 4
        speed_boost = self.upload_speed_score_boost(f.get('upload_speed', ''))
        score += speed_boost
        self.write_debug(f'SCORE {score:.1f} speed_boost={speed_boost:.1f} | tier={tier} | query={query} | user={f["username"]} | file={filename or text[:160]} | raw={str(item)}')
        return SearchResult(
            query=query,
            tier=tier,
            score=score,
            raw=item,
            filename=filename or text[:160],
            username=f['username'],
            size=f['size'],
            bitrate=f['bitrate'],
            length=f['length'],
            upload_speed=f['upload_speed'],
            has_free_slot=f['has_free_slot'],
            slsk_link=extract_slsk(item),
        )

    def worker_search(self, search_id: str, track: Track, tier: str, query: str) -> None:
        shown = skipped = 0
        try:
            self.worker_queue.put(('log', f'RUNNING search_id={search_id} track_id={track.id}: [{tier}] {query}'))
            for kind, payload in self.client.search_stream(query, timeout=45):
                if kind == 'log':
                    self.worker_queue.put(('log', payload))
                    continue
                result = self.make_result(track, tier, query, payload)
                if result is None:
                    skipped += 1
                    continue
                shown += 1
                self.worker_queue.put(('search_result', search_id, track.id, result))
        except subprocess.TimeoutExpired:
            self.worker_queue.put(('log', f'TIMEOUT: {tier}: {query}'))
        except FileNotFoundError:
            self.worker_queue.put(('log', 'ERROR: sockseek command not found. Put sockseek in PATH or set --sockseek.'))
        except Exception as exc:
            self.worker_queue.put(('log', f'ERROR searching {query}: {exc}'))
        self.worker_queue.put(('search_done', search_id, track.id, shown, skipped))

    def add_live_result(self, track_id: str, result: SearchResult) -> None:
        results = self.results_by_track.setdefault(track_id, [])
        if any(r.identity_key == result.identity_key for r in results):
            return
        results.append(result)
        results.sort(key=lambda r: r.score, reverse=True)
        # While tuning scoring, keep a wider visible list so good-but-under-scored
        # results are not hidden below the first page.
        del results[100:]
        if track_id == self.current().id:
            self.render_results()
            self.details_var.set(f'{len(results)} candidate(s) so far. Results update live while the search is running.')

    def poll_worker(self) -> None:
        try:
            while True:
                msg = self.worker_queue.get_nowait()
                if msg[0] == 'log':
                    self.log_line(msg[1])
                    continue
                if msg[0] == 'search_result':
                    _, search_id, track_id, result = msg
                    if search_id == self.active_search_id:
                        self.add_live_result(track_id, result)
                    continue
                if msg[0] == 'search_done':
                    _, search_id, track_id, shown, skipped = msg
                    stale = search_id != self.active_search_id
                    if stale:
                        self.log_line(f'Ignored stale search completion: {search_id}')
                        continue
                    self.busy = False
                    results = self.results_by_track.get(track_id, [])
                    t = next((x for x in self.tracks if x.id == track_id), None)
                    if t:
                        t.status = 'searched' if results else 'failed'
                    self.render_results()
                    self.render_status()
                    self.save_state(silent=True)
                    self.details_var.set(f'{len(results)} candidate(s). Pick one, then click Download selected or double-click it.')
                    self.log_line(f'Displayed {len(results)} candidate(s). Raw shown={shown}; filtered/deduped={skipped}.')
                    continue
                if msg[0] == 'rb_done':
                    _, track_id, matches, error = msg
                    self.rb_checking_track_ids.discard(track_id)
                    self.rb_matches_by_track[track_id] = matches
                    if error:
                        self.log_line('Rekordbox check: ' + error)
                    if track_id == self.current().id:
                        self.render_rekordbox_matches(self.current())
                    continue
                if msg[0] == 'preview_done':
                    _, ok, result_key, username, new_files, logs = msg
                    self.busy = False
                    for line in logs:
                        self.log_line(line)
                    if ok and new_files:
                        self.preview_files_by_key[result_key] = list(new_files)
                        self.details_var.set(f'Preview downloaded to limbo and opened. If it sounds right, click ✓ Keep preview to move it to the final folder.')
                        self._open_audio_file(Path(new_files[0]))
                    else:
                        self.mark_user_unavailable(username, 'preview failed / no quick progress')
                        self.details_var.set('Preview failed quickly, so that user was hidden. Select another candidate and press ▶ Play.')
                        self.select_first_result_if_any()
                    continue
                if msg[0] == 'download_done':
                    _, ok, username, new_files, logs = msg
                    self.busy = False
                    for line in logs:
                        self.log_line(line)
                    if not ok:
                        self.mark_user_unavailable(username, 'final download failed')
                    self.current().status = 'downloaded' if ok else 'failed'
                    self.render_status()
                    self.save_state(silent=True)
                    if ok and new_files:
                        self.offer_add_downloaded_files_to_rekordbox_playlist([Path(p) for p in new_files])
        except queue.Empty:
            pass
        self.after(100, self.poll_worker)


    def on_result_click(self, event: tk.Event) -> None:
        region = self.result_tree.identify('region', event.x, event.y)
        if region != 'cell':
            return
        column = self.result_tree.identify_column(event.x)
        row = self.result_tree.identify_row(event.y)
        if column == '#1' and row:
            self.result_tree.selection_set(row)
            self.play_selected()

    def _open_audio_file(self, path: Path) -> None:
        try:
            if os.name == 'nt':
                os.startfile(str(path))  # type: ignore[attr-defined]
            elif sys.platform == 'darwin':
                subprocess.Popen(['open', str(path)])
            else:
                subprocess.Popen(['xdg-open', str(path)])
        except Exception as exc:
            self.log_line(f'Could not auto-open preview file: {exc}')

    def play_selected(self) -> None:
        if self.busy:
            return
        result = self.selected_result()
        if not result:
            messagebox.showinfo('Pick result', 'Select a candidate first.')
            return
        if not self.confirm_rekordbox_duplicate_guard():
            return
        target = build_slsk_link(result)
        if not target:
            messagebox.showerror('Cannot preview exact result', 'This result did not contain enough metadata to build a slsk:// link.')
            return
        self.current().selected_result = result.to_dict()
        self.busy = True
        self.last_preview_result_key = result.identity_key
        self.log_selection(result, action='preview')
        self.log_line(f'Preview downloading to limbo folder: {self.preview_dir}')
        self.log_line(f'Preview target: {target}')
        threading.Thread(target=self.worker_preview_download, args=(target, result.identity_key, result.username), daemon=True).start()

    def worker_preview_download(self, target: str, result_key: str, username: str) -> None:
        logs: list[str] = []
        ok = False
        new_files: list[Path] = []
        try:
            code, stdout, stderr, new_files = self.client.download(
                target,
                timeout=300,
                progress=lambda line: self.worker_queue.put(('log', line)),
                download_dir=self.preview_dir,
                fail_fast=True,
                first_progress_timeout=12,
                stall_timeout=18,
            )
            logs.append(f'Preview Sockseek exit code: {code}')
            if stdout.strip():
                logs.append('preview stdout: ' + stdout.strip()[-4000:])
            if stderr.strip():
                logs.append('preview stderr: ' + stderr.strip()[-4000:])
            ok = code == 0 and bool(new_files)
            if new_files:
                logs.append('Preview downloaded into limbo:')
                logs.extend(f'  {p}' for p in new_files[:12])
            elif code == 0:
                logs.append('Sockseek returned success, but no new preview audio file was detected.')
        except Exception as exc:
            logs.append(f'Preview download error: {exc}')
        self.worker_queue.put(('preview_done', ok, result_key, username, new_files, logs))

    def keep_preview_selected(self) -> None:
        result = self.selected_result()
        key = result.identity_key if result else self.last_preview_result_key
        if not key or key not in self.preview_files_by_key:
            messagebox.showinfo('No preview found', 'Preview/play a result first, then keep it if it sounds right.')
            return
        files = [p for p in self.preview_files_by_key.get(key, []) if p.exists()]
        if not files:
            messagebox.showinfo('No preview file', 'The preview file was not found in the limbo folder.')
            return
        if not self.confirm_rekordbox_duplicate_guard():
            return
        if not messagebox.askyesno('Move preview to final folder?', f'Move {len(files)} preview file(s) from limbo to:\n\n{self.client.download_dir}'):
            return
        moved: list[Path] = []
        for src in files:
            dst = self.unique_destination(self.client.download_dir / src.name)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.move(str(src), str(dst))
            moved.append(dst)
        self.preview_files_by_key.pop(key, None)
        self.current().status = 'downloaded'
        if result:
            self.log_selection(result, action='keep_preview')
        self.render_status()
        self.save_state(silent=True)
        self.log_line('Kept preview and moved to final download folder:')
        for p in moved:
            self.log_line(f'  {p}')
        self.offer_add_downloaded_files_to_rekordbox_playlist(moved)

    def unique_destination(self, path: Path) -> Path:
        if not path.exists():
            return path
        stem, suffix = path.stem, path.suffix
        for i in range(1, 1000):
            candidate = path.with_name(f'{stem} ({i}){suffix}')
            if not candidate.exists():
                return candidate
        return path.with_name(f'{stem} ({int(time.time())}){suffix}')

    def log_selection(self, result: SearchResult, action: str) -> None:
        exists = self.training_log_path.exists()
        try:
            with self.training_log_path.open('a', encoding='utf-8', newline='') as f:
                writer = csv.writer(f)
                if not exists:
                    writer.writerow(['timestamp', 'action', 'track_artist', 'track_title', 'track_album', 'query', 'tier', 'score', 'filename', 'username', 'length', 'bitrate', 'size', 'speed'])
                t = self.current()
                writer.writerow([datetime.now().isoformat(timespec='seconds'), action, t.artist, t.title, t.album, result.query, result.tier, result.score, result.filename, result.username, result.length, result.bitrate, result.size, result.upload_speed])
        except Exception as exc:
            self.write_debug(f'Could not write training log: {exc}')

    def download_selected(self) -> None:
        if self.busy:
            return
        result = self.selected_result()
        if not result:
            messagebox.showinfo('Pick result', 'Select a candidate first.')
            return
        if not self.confirm_rekordbox_duplicate_guard():
            return
        target = build_slsk_link(result)
        self.current().selected_result = result.to_dict()
        self.log_selection(result, action='download_final')
        if not target:
            messagebox.showerror('Cannot download exact result', 'This result did not contain a slsk link or enough User/File metadata. Try another candidate or use a json-all result if your Sockseek build buffers text output.')
            return
        name = self._clean_filename(result.filename or target)
        if not messagebox.askyesno('Download selected?', f'Download this exact candidate?\n\n{name[:700]}'):
            return
        self.busy = True
        self.log_line(f'Downloading selected file: {target}')
        threading.Thread(target=self.worker_download, args=(target, result.username), daemon=True).start()

    def worker_download(self, target: str, username: str) -> None:
        logs, ok = [], False
        new_files: list[Path] = []
        try:
            code, stdout, stderr, new_files = self.client.download(target, progress=lambda line: self.worker_queue.put(('log', line)), fail_fast=True, first_progress_timeout=15, stall_timeout=25)
            logs.append(f'Sockseek exit code: {code}')
            if stdout.strip():
                logs.append('stdout: ' + stdout.strip()[-1200:])
            if stderr.strip():
                logs.append('stderr: ' + stderr.strip()[-1200:])
            ok = code == 0
            if new_files:
                logs.append('Downloaded new audio file(s):')
                logs.extend(f'  {p}' for p in new_files[:8])
            elif ok:
                logs.append('Sockseek returned success, but no new audio file was detected by timestamp.')
        except Exception as exc:
            logs.append(f'Download error: {exc}')
        self.worker_queue.put(('download_done', ok, username, new_files, logs))

    def set_status(self, status: str) -> None:
        self.current().status = status
        self.save_state(silent=True)
        if status != 'downloaded':
            self.export_not_downloaded_report(silent=True)
        self.render_status()

    def jump_failed_pending(self) -> None:
        self.update_track_from_fields()
        order = list(range(self.index + 1, len(self.tracks))) + list(range(0, self.index + 1))
        for i in order:
            if self.tracks[i].status in {'failed', 'pending', 'searched'}:
                self.index = i
                self.render_current()
                return
        messagebox.showinfo('Done', 'No failed, pending, or searched tracks left.')

    def save_state(self, silent: bool = False) -> None:
        self.update_track_from_fields()
        save_state(self.state_path, self.tracks)
        self.export_not_downloaded_report(silent=True)
        if not silent:
            self.log_line(f'Saved state to {self.state_path}')
