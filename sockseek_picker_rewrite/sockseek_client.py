from __future__ import annotations

import json
import re
import subprocess
import time
import signal
from pathlib import Path
from typing import Any, Callable, Iterator
from models import AUDIO_EXTENSIONS, SearchResult

AUDIO_EXT_PATTERN = re.compile(r'\.(?:mp3|flac|wav|aac|ogg|opus|aif|aiff|wma)\b', re.I)
RESULT_FULL_RE = re.compile(
    r'^\[(?P<meta>[^\]]+)\]\s*'
    r'(?:\((?P<speed>[^)]*?/s)\)\s*)?'
    r'(?P<path>.*?)'
    r'(?:\s*\(nec:.*)?$',
    re.I,
)

DEBUG_SNIPPET_CHARS = 3000
PRIVATE_OR_LOCKED_KEYS = {'isprivate','private','islocked','locked','isfilelocked','requiresprivileges','requiresprivilege','isrestricted','isunavailable','unavailable','inaccessible','haspermission'}
PRIVATE_OR_LOCKED_WORDS = {'private','locked','unavailable','inaccessible','no permission','privileges required','permission denied','user list only'}

DOWNLOAD_FAILURE_WORDS = (
    'failed', 'failure', 'timed out', 'timeout', 'stale', 'unavailable',
    'offline', 'disconnected', 'cannot connect', 'could not connect',
    'connection failed', 'connection refused', 'denied', 'permission',
    'locked', 'private', 'cancelled', 'canceled', 'aborted', 'not found',
    'no such file', 'no route', 'reset by peer', 'user is not online',
)


def looks_like_download_failure(stdout: str, stderr: str) -> bool:
    text = f'{stdout}\n{stderr}'.lower()
    return any(word in text for word in DOWNLOAD_FAILURE_WORDS)


def flatten(obj: Any) -> str:
    if obj is None: return ''
    if isinstance(obj, (str, int, float, bool)): return str(obj)
    if isinstance(obj, list): return ' '.join(flatten(x) for x in obj)
    if isinstance(obj, dict): return ' '.join(flatten(v) for v in obj.values())
    return str(obj)


def find_key(obj: Any, names: set[str]) -> Any:
    if isinstance(obj, dict):
        for k, v in obj.items():
            if str(k).lower() in names: return v
        for v in obj.values():
            got = find_key(v, names)
            if got not in (None, ''): return got
    if isinstance(obj, list):
        for x in obj:
            got = find_key(x, names)
            if got not in (None, ''): return got
    return None


def _clean_result_path(text: str) -> str:
    text = str(text).strip()
    # Strip Sockseek condition suffixes such as "(nec:Satisfied, prf:StrictTitle fails)".
    text = re.sub(r'\s*\(nec:.*$', '', text, flags=re.I).strip()
    return text


def _parse_result_full_line(line: str) -> dict[str, str]:
    raw = str(line).strip()
    m = RESULT_FULL_RE.match(raw)
    meta = m.group('meta') if m else ''
    path = _clean_result_path(m.group('path') if m else raw)
    speed = (m.group('speed') or '') if m else ''

    # Metadata normally looks like: "207s/320kbps / 7.9MB". Keep this best-effort;
    # the ranking only needs filename/path and the GUI can still show the rest when present.
    length = bitrate = size = ''
    lm = re.search(r'(?P<len>\d+)s', meta, flags=re.I)
    bm = re.search(r'(?P<br>\d+)\s*kbps', meta, flags=re.I)
    sm = re.search(r'(?P<size>\d+(?:\.\d+)?\s*(?:kb|mb|gb))', meta, flags=re.I)
    if lm: length = lm.group('len')
    if bm: bitrate = bm.group('br')
    if sm: size = sm.group('size')

    username = ''
    filename = path
    if '\\' in path:
        username, filename = [part.strip() for part in path.split('\\', 1)]
    elif '/' in path:
        username, filename = [part.strip() for part in path.split('/', 1)]

    return {
        'username': username,
        'filename': filename,
        'length': length,
        'size': size,
        'bitrate': bitrate,
        'upload_speed': speed,
        'has_free_slot': '',
    }


def fields(item: Any) -> dict[str, str]:
    if not isinstance(item, dict):
        return _parse_result_full_line(str(item))
    def g(*names: str) -> str:
        return str(find_key(item, {n.lower() for n in names}) or '')
    return {
        'username': g('Username','user','owner'),
        'filename': _clean_result_path(g('Filename','filename','path','name','title')),
        'length': g('Length','duration','time'),
        'size': g('Size','filesize'),
        'bitrate': g('Bitrate','br'),
        'upload_speed': g('UploadSpeed','speed'),
        'has_free_slot': g('HasFreeUploadSlot'),
    }


def is_audio(filename: str) -> bool:
    # Path.suffix fails for streamed text lines because Sockseek appends condition text
    # after the filename. Accept audio extensions anywhere as a real filename boundary.
    return AUDIO_EXT_PATTERN.search(str(filename)) is not None


def is_private_or_locked(obj: Any) -> tuple[bool, str]:
    if isinstance(obj, dict):
        for k, v in obj.items():
            key = str(k).lower()
            if key in PRIVATE_OR_LOCKED_KEYS:
                if key == 'haspermission' and v is False: return True, 'permission=false'
                if isinstance(v, bool) and v is True: return True, f'{k}=true'
                if isinstance(v, str) and v.strip().lower() in {'true','yes','locked','private'}: return True, f'{k}={v}'
            found, reason = is_private_or_locked(v)
            if found: return found, reason
    elif isinstance(obj, list):
        for x in obj:
            found, reason = is_private_or_locked(x)
            if found: return found, reason
    elif isinstance(obj, str):
        # Plain streamed result lines are filenames/paths. A folder called "private"
        # should not remove an otherwise visible search result from the GUI.
        return False, ''
    return False, ''


def extract_slsk(obj: Any) -> str | None:
    if isinstance(obj, str):
        m = re.search(r'slsk://\S+', obj)
        return m.group(0) if m else None
    if isinstance(obj, list):
        return next((x for item in obj if (x := extract_slsk(item))), None)
    if isinstance(obj, dict):
        for v in obj.values():
            if isinstance(v, str) and v.startswith('slsk://'): return v
            got = extract_slsk(v)
            if got: return got
    return None


def build_slsk_link(result: SearchResult) -> str | None:
    if result.slsk_link: return result.slsk_link
    if not result.username or not result.filename: return None
    return f'slsk://{result.username}/{result.filename.replace(chr(92), "/")}'


class SockseekClient:
    def __init__(self, sockseek_cmd: str, download_dir: Path, config: str | None = None):
        self.sockseek_cmd = sockseek_cmd
        self.download_dir = Path(download_dir)
        self.config = config

    def base_args(self) -> list[str]:
        return self.base_args_for(self.download_dir)

    def base_args_for(self, download_dir: Path | str | None = None) -> list[str]:
        args = [self.sockseek_cmd]
        if self.config:
            args += ['--config', self.config]
        out_dir = Path(download_dir) if download_dir is not None else self.download_dir
        return args + ['--path', str(out_dir), '--no-progress']

    @staticmethod
    def fmt(args: list[str]) -> str:
        return subprocess.list2cmdline([str(a) for a in args])

    @staticmethod
    def snippet(text: str, limit: int = DEBUG_SNIPPET_CHARS) -> str:
        text = (text or '').strip()
        return text if len(text) <= limit else text[:limit] + '\n... [truncated]'

    def _json_all(self, query: str, timeout: int) -> tuple[list[Any], list[str]]:
        logs: list[str] = []
        args = self.base_args() + [query, '--print', 'json-all']
        logs.append('COMMAND json-all: ' + self.fmt(args))
        proc = subprocess.run(args, capture_output=True, text=True, timeout=timeout, encoding='utf-8', errors='replace')
        stdout, stderr = proc.stdout or '', proc.stderr or ''
        logs.append(f'json-all exit={proc.returncode} stdout_chars={len(stdout)} stderr_chars={len(stderr)}')
        if stderr.strip(): logs.append('json-all STDERR:\n' + self.snippet(stderr))
        if stdout.strip(): logs.append('json-all STDOUT head:\n' + self.snippet(stdout))
        try:
            parsed = json.loads(stdout) if stdout.strip() else []
            if parsed:
                return (parsed if isinstance(parsed, list) else [parsed]), logs + [f'json-all parsed_items={len(parsed) if isinstance(parsed, list) else 1}']
        except Exception as exc:
            logs.append(f'json parse failed: {exc}')
        return [], logs

    def search_raw(self, query: str, timeout: int = 60) -> tuple[list[Any], list[str]]:
        """Compatibility method: returns all results after the process exits."""
        items, logs = self._json_all(query, timeout)
        if items:
            return items, logs
        args = self.base_args() + [query, '--print', 'results-full']
        logs.append('COMMAND results-full: ' + self.fmt(args))
        proc = subprocess.run(args, capture_output=True, text=True, timeout=timeout, encoding='utf-8', errors='replace')
        stdout, stderr = proc.stdout or '', proc.stderr or ''
        logs.append(f'results-full exit={proc.returncode} stdout_chars={len(stdout)} stderr_chars={len(stderr)}')
        if stderr.strip(): logs.append('results-full STDERR:\n' + self.snippet(stderr))
        if stdout.strip(): logs.append('results-full STDOUT head:\n' + self.snippet(stdout))
        lines = [line.strip() for line in stdout.splitlines() if line.strip()]
        return lines, logs + [f'results-full parsed_lines={len(lines)}']

    def search_stream(self, query: str, timeout: int = 60) -> Iterator[tuple[str, Any | str]]:
        """Yield ('item', result) and ('log', text) while Sockseek is running.

        `--print results-full` is attempted first because it can be consumed line
        by line when the CLI flushes output. Some Sockseek versions buffer the
        whole print output; in that case the GUI still updates as soon as each
        printed line is received. If no text results are emitted, we fall back to
        `json-all` at the end for reliable structured metadata.
        """
        args = self.base_args() + [query, '--print', 'results-full']
        yield 'log', 'COMMAND results-full streaming: ' + self.fmt(args)
        proc = subprocess.Popen(
            args,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding='utf-8',
            errors='replace',
            bufsize=1,
        )
        start = time.time()
        emitted = 0
        stdout_tail: list[str] = []
        assert proc.stdout is not None
        while True:
            line = proc.stdout.readline()
            if line:
                clean = line.strip()
                if clean:
                    emitted += 1
                    stdout_tail.append(clean)
                    stdout_tail = stdout_tail[-20:]
                    yield 'item', clean
            elif proc.poll() is not None:
                break
            else:
                if time.time() - start > timeout:
                    proc.kill()
                    yield 'log', 'TIMEOUT: results-full streaming timed out.'
                    break
                time.sleep(0.05)
        stderr = proc.stderr.read() if proc.stderr else ''
        code = proc.wait()
        yield 'log', f'results-full streaming exit={code} emitted_lines={emitted}'
        if stderr.strip():
            yield 'log', 'results-full STDERR:\n' + self.snippet(stderr)
        if stdout_tail:
            yield 'log', 'results-full tail:\n' + self.snippet('\n'.join(stdout_tail))
        if emitted:
            return

        # Fallback: structured output is not real-time, but gives exact metadata.
        try:
            items, logs = self._json_all(query, timeout)
            for log in logs:
                yield 'log', log
            for item in items:
                yield 'item', item
        except subprocess.TimeoutExpired:
            yield 'log', 'TIMEOUT: json-all fallback timed out.'

    def download(
        self,
        target: str,
        timeout: int = 900,
        progress: Callable[[str], None] | None = None,
        download_dir: Path | str | None = None,
        *,
        fail_fast: bool = False,
        first_progress_timeout: int = 12,
        stall_timeout: int = 18,
    ) -> tuple[int, str, str, list[Path]]:
        """Download a target and return (exit_code, stdout, stderr, new_audio_files).

        When fail_fast=True this behaves like a preview probe: if Sockseek does
        not create/change any file in the target folder quickly, the process is
        killed. This avoids offline/stale users blocking the GUI for ages.
        """
        actual_dir = Path(download_dir) if download_dir is not None else self.download_dir
        actual_dir.mkdir(parents=True, exist_ok=True)
        before = time.time() - 2
        args = self.base_args_for(actual_dir) + [target]
        if progress:
            progress('COMMAND download: ' + self.fmt(args))
            if fail_fast:
                progress(f'fail-fast enabled: first_progress_timeout={first_progress_timeout}s stall_timeout={stall_timeout}s')
        proc = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace')
        start = time.time()
        last_activity = start
        seen_sizes: dict[str, int] = self._file_size_snapshot(actual_dir)
        killed_reason = ''

        while proc.poll() is None:
            time.sleep(0.5)
            now = time.time()
            current_sizes = self._file_size_snapshot(actual_dir)
            if current_sizes != seen_sizes:
                last_activity = now
                seen_sizes = current_sizes

            if fail_fast:
                if not current_sizes and now - start > first_progress_timeout:
                    killed_reason = f'No file/progress appeared after {first_progress_timeout}s; treating candidate as unavailable/stale.'
                    proc.kill()
                    break
                if current_sizes and now - last_activity > stall_timeout:
                    killed_reason = f'No download progress for {stall_timeout}s; treating candidate as stalled/unavailable.'
                    proc.kill()
                    break

            if now - start > timeout:
                killed_reason = f'Timed out after {timeout}s.'
                proc.kill()
                break

        stdout, stderr = proc.communicate()
        code = proc.returncode if proc.returncode is not None else 124
        if killed_reason:
            code = 124
            stderr = (stderr or '') + '\n' + killed_reason
        if looks_like_download_failure(stdout or '', stderr or '') and code == 0:
            code = 2
        return code, stdout or '', stderr or '', self.new_audio_files(before, actual_dir)

    def _file_size_snapshot(self, root: Path) -> dict[str, int]:
        """Return size of files created/modified since this process began.

        Includes .incomplete files, because Sockseek may not create the final
        .mp3/.flac name until the transfer finishes.
        """
        out: dict[str, int] = {}
        if not root.exists():
            return out
        for p in root.rglob('*'):
            try:
                if p.is_file():
                    st = p.stat()
                    out[str(p)] = int(st.st_size)
            except OSError:
                pass
        return out

    def new_audio_files(self, after_ts: float, root: Path | str | None = None) -> list[Path]:
        search_root = Path(root) if root is not None else self.download_dir
        if not search_root.exists(): return []
        out = []
        for p in search_root.rglob('*'):
            try:
                if p.is_file() and p.suffix.lower() in AUDIO_EXTENSIONS and p.stat().st_mtime >= after_ts:
                    out.append(p)
            except OSError:
                pass
        return sorted(out, key=lambda p: p.stat().st_mtime, reverse=True)
