from __future__ import annotations

import re
from models import AUDIO_EXTENSIONS, SearchResult, Track
from parser import normalise

BAD_CLEAN_WORDS = {'dirty', 'explicit', 'raw', 'uncensored', 'nasty', 'xxx', 'uncut'}
GOOD_CLEAN_WORDS = {'clean', 'radio'}
GOOD_INTRO_PHRASES = (
    'intro', 'dj intro', 'intro edit', 'intro clean', 'clean intro', '8 bar',
    '8bar', 'hype intro', 'ck intro', 'djcity intro', 'tmu intro', 'mmp intro',
    'hh intro', 'clap intro', 'acap intro', 'urban intro', 'throwback intro',
)
BAD_INTRO_PHRASES = ('no intro', 'non intro')
MASHUP_WORDS = {' vs ', ' x ', ' mashup ', ' wordplay '}
SOFT_REMIX_WORDS = {' bootleg ', ' rework '}  # edit/intro edit can be good, so don't punish 'edit' itself


def judgement(score: float) -> str:
    if score >= 115:
        return 'Excellent'
    if score >= 85:
        return 'Good'
    if score >= 45:
        return 'Maybe'
    return 'Weak'


def _has_phrase(hay: str, phrase: str) -> bool:
    return re.search(r'\b' + re.escape(phrase).replace(r'\ ', r'\s+') + r'\b', hay) is not None


def _tokens(text: str) -> list[str]:
    return [t for t in normalise(text).split() if len(t) > 1]


def _coverage(needles: list[str], hay_words: set[str]) -> float:
    useful = [t for t in needles if len(t) > 2]
    if not useful:
        return 0.0
    return sum(1 for t in useful if t in hay_words) / len(useful)


def score_result(track: Track, result_text: str, tier: str) -> float:
    """Lenient ranking, not harsh filtering.

    The GUI should show a useful list even when the result is a remix, bootleg, or
    has extra DJ-pool words. The only job here is to put the most likely exact
    clean/intro version near the top.
    """
    hay = normalise(result_text)
    hay_spaced = f' {hay} '
    artist = normalise(track.artist)
    title = normalise(track.title)
    hay_words = set(hay.split())
    artist_tokens = _tokens(track.artist)
    title_tokens = _tokens(track.title)

    score = 0.0

    # Track identity. Exact phrase is best, but token coverage is enough to show it.
    if title and title in hay:
        score += 70
    title_cov = _coverage(title_tokens, hay_words)
    score += title_cov * 55

    if artist and artist in hay:
        score += 45
    artist_cov = _coverage(artist_tokens, hay_words)
    score += artist_cov * 35

    # Prefer paths that look like the two main entities belong together.
    # Check both orders because some CSVs / filenames have artist-title swapped.
    if artist and title:
        if re.search(re.escape(artist) + r'\s+' + re.escape(title), hay):
            score += 35
        if re.search(re.escape(title) + r'\s+' + re.escape(artist), hay):
            score += 35
    if title_cov >= 0.99 and artist_cov >= 0.99:
        score += 55

    # Mashups/wordplays can still be useful, but they should not beat a real
    # Artist - Title result just because they contain intro/clean words.
    if any(w in hay_spaced for w in MASHUP_WORDS):
        score -= 45
    if ' x ' in hay_spaced or ' vs ' in hay_spaced:
        score -= 35
    if any(w in hay_spaced for w in SOFT_REMIX_WORDS):
        score -= 10

    has_intro = any(_has_phrase(hay, p) for p in GOOD_INTRO_PHRASES)
    has_no_intro = any(_has_phrase(hay, p) for p in BAD_INTRO_PHRASES)
    has_clean = bool(GOOD_CLEAN_WORDS & hay_words)
    has_dirty = bool(BAD_CLEAN_WORDS & hay_words)
    base_tier = tier.split(' / ', 1)[0]

    if base_tier in {'Intro', 'Intro Clean'}:
        if has_intro:
            score += 55
        if has_clean:
            score += 45
        if has_intro and has_clean:
            score += 30
        if has_no_intro:
            score -= 80
        if has_dirty:
            score -= 75
    elif base_tier == 'Clean':
        if has_clean:
            score += 55
        if has_intro:
            score += 18
        if has_dirty:
            score -= 80
        if has_no_intro:
            score -= 20
    else:
        if has_clean:
            score += 12
        if has_intro:
            score += 12
        if has_dirty:
            score -= 25

    lower = result_text.lower()
    if any(ext in lower for ext in AUDIO_EXTENSIONS):
        score += 10
    if any(x in hay for x in ('incomplete', 'preview', 'youtube', 'video rip', 'synoindex')):
        score -= 35

    # Don't hard-filter weak results, but push obvious broad-search noise down
    # hard. This stops things like "Crazy Frog - Intro.mp3" beating an actual
    # "Crazy Frog - Axel F" result just because it says intro.
    if title_tokens and title_cov == 0:
        score -= 150
    elif title_tokens and title_cov < 0.5:
        score -= 65

    if artist_tokens and artist_cov == 0:
        score -= 125
    elif artist_tokens and artist_cov < 0.5:
        score -= 55
    return score


def display_result(result: SearchResult) -> str:
    name = (result.filename or str(result.raw)).replace('\\', '/').split('/')[-1]
    extras = []
    if result.length:
        try:
            sec = int(float(result.length)); extras.append(f'{sec//60}:{sec%60:02d}')
        except Exception: extras.append(str(result.length))
    if result.bitrate:
        extras.append(f'{str(result.bitrate).split(".")[0]}kbps')
    if result.size:
        try:
            n = float(str(result.size).replace('MB','').replace('mb','').strip())
            extras.append(f'{n:.1f}MB')
        except Exception: extras.append(str(result.size))
    if result.username: extras.append(f'user={result.username}')
    if str(result.has_free_slot).lower() == 'false': extras.append('queued')
    return f'[{result.tier}] {judgement(result.score)} score={result.score:.0f}  {name}' + ((' | ' + ' | '.join(extras)) if extras else '')
