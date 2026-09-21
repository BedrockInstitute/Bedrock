#!/usr/bin/env python3
"""Convert reader-facing Japanese prose from desu/masu to de-aru style.

The converter is deliberately repository-specific and conservative.  It visits
only ``<!--ja--> ... <!--/-->`` regions in ``src/**/*.lagda.md`` and masks
Markdown constructs that are not reader prose before looking at sentence
endings.  In particular, fenced code, inline code, HTML tags and comments,
Markdown link destinations, and attribute/term-anchor blocks are never edited.

The default mode is a dry run.  Pass ``--write`` to apply conversions, or
``--check`` to report every remaining polite sentence ending without proposing
changes.  A dry run or write exits nonzero if a conjugation is not covered by a
reviewed rule; it never guesses silently.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import os
from pathlib import Path
import re
import sys
import tempfile
from typing import Iterable


JA_OPEN = "<!--ja-->"
GROUP_CLOSE = "<!--/-->"
FENCE_RE = re.compile(r"^\s*(`{3,}|~{3,})")
TOKEN_RE = re.compile("\ue000([0-9]+)\ue001")
TOKEN_PATTERN = r"\ue000[0-9]+\ue001"

# Markdown punctuation that may intervene between a Japanese sentence ending
# and its punctuation.  TOKEN_PATTERN accounts for a protected link target or
# HTML/attribute fragment in the same position.
TRAILER_PATTERN = rf"(?:(?:{TOKEN_PATTERN})|[*_~\]}}」』】》〉])*"
CONNECTOR_PATTERN = (
    rf"(?:が|けれど(?:も)?|けど|ので|のに|から|し|と|なら|ため|ものの|、|：|；|か|ね|よ|"
    rf"[ \t]+[（(]|[)）]|{TOKEN_PATTERN})"
)
BOUNDARY_PATTERN = (
    rf"(?P<trailer>{TRAILER_PATTERN})"
    rf"(?:(?P<punct>[。！？])|(?P<zero>(?={CONNECTOR_PATTERN}|$)))"
)

POLITE_FORMS = (
    "ではありませんでした",
    "じゃありませんでした",
    "ありませんでした",
    "ませんでした",
    "ではありません",
    "じゃありません",
    "ありません",
    "ください",
    "ましょう",
    "でしょう",
    "でした",
    "ました",
    "ません",
    "ます",
    "です",
)
POLITE_RE = re.compile(
    rf"(?P<form>{'|'.join(map(re.escape, POLITE_FORMS))}){BOUNDARY_PATTERN}"
)
POLITE_ANY_RE = re.compile(rf"(?P<form>{'|'.join(map(re.escape, POLITE_FORMS))})")

# Regression guard for forms previously produced by over-general conjugation.
# A hit is never silently written: it is reported as unresolved even when no
# polite ending remains.  Keep this list exact so legitimate suru compounds
# such as 代表する and 指示する are not rejected.
INVALID_GENERATED_RE = re.compile(
    r"名指する|産み出する|読み戻する|運び戻する|向け直する|"
    r"送り返する|選び出する|切り出する|思い出しよう|"
    r"効いてく(?=[。！？、]|$)|比較でくる|符号化でくる|切り詰められたる|"
    r"降ろする|剥がする|やり直しない|証明し直しない"
)


def iter_polite(text: str) -> Iterable[re.Match[str]]:
    """Yield polite forms, excluding corpus-attested cross-word coincidences."""
    for match in POLITE_ANY_RE.finditer(text):
        # These are particle で followed by the adverbs すでに / すぐ / すべて,
        # or the verb すむ, not the copula です.
        if match.group("form") == "です" and text.startswith(
            ("でに", "ぐ", "べて", "む"), match.end()
        ):
            continue
        yield match

SPECIAL_REPLACEMENTS = {
    # This awkward but corpus-attested sequence means that the preceding noun
    # is not the case.  Replacing only its final です would yield ではなくである.
    "ではなくです": "ではない",
    "ではありませんでした": "ではなかった",
    "じゃありませんでした": "ではなかった",
    "ありませんでした": "なかった",
    "ではありません": "ではない",
    "じゃありません": "ではない",
    "ありません": "ない",
    "ください": "ほしい",
    "でしょう": "であろう",
    "でした": "であった",
    "です": "である",
}

# Corpus-attested i-adjectives immediately followed by です.  Their plain form
# drops the copula; treating them like nouns would create the ungrammatical
# 正しいである.  Unknown -いです forms are not guessed: they remain visible to
# POLITE_ANY_RE and make the run fail as unresolved.
I_ADJECTIVES = {
    "短い",
    "正しい",
    "等しい",
    "分かりやすい",
}
I_ENDING_NOUNS = {
    "問い",
    "違い",
    "振る舞い",
}

# Corpus-reviewed verbs whose polite stem is exceptional under the general
# godan rules.  Entries map a suffix of the polite stem to the plain form.  The
# suffix match is intentional: it also handles compounds such as 取り過ぎます.
ICHIDAN_PRESENT = {
    "でき": "できる",
    "用い": "用いる",
    "試み": "試みる",
    "過ぎ": "過ぎる",
    "すぎ": "すぎる",
    "生き": "生きる",
    "起き": "起きる",
    "尽き": "尽きる",
    "落ち": "落ちる",
    "満ち": "満ちる",
    "足り": "足りる",
    "借り": "借りる",
    "降り": "降りる",
    "懲り": "懲りる",
    "信じ": "信じる",
    "応じ": "応じる",
    "命じ": "命じる",
    "通じ": "通じる",
    "強い": "強いる",
    # The negative phrase てはいません / ではいません inflects いる after
    # the topic particle は.  Keeping は in the reviewed suffix avoids treating
    # an arbitrary unknown -います verb as ichidan.
    "はい": "はいる",
}

# Native -す verbs occurring at sentence ends in the current corpus.  Without
# this list, 表します and 証明します would be indistinguishable by their final
# kana even though their plain forms are 表す and 証明する respectively.
GODAN_SU = {
    "表す",
    "示す",
    "満たす",
    "移す",
    "写す",
    "戻す",
    "下ろす",
    "出す",
    "返す",
    "渡す",
    "指す",
    "尽くす",
    "起こす",
    "施す",
    "落とす",
    "直す",
    "減らす",
    "ずらす",
    "崩す",
    "延ばす",
    "伸ばす",
    "動かす",
    "許す",
    "残す",
    "課す",
    "外す",
    "飛ばす",
    "果たす",
    "通す",
    "倒す",
    "繰り返す",
    "取り外す",
    "取り戻す",
    "押し出す",
    "生み出す",
    "取り出す",
    # Corpus-reviewed compounds.  These must be listed as complete verbs:
    # guessing from the final 「し」 confuses native -す verbs with suru verbs.
    "産み出す",
    "作り出す",
    "選び出す",
    "切り出す",
    "見つけ出す",
    "導き出す",
    "写し出す",
    "送り出す",
    "呼び出す",
    "引き出す",
    "思い出す",
    "読み戻す",
    "書き戻す",
    "運び戻す",
    "結び戻す",
    "引き戻す",
    "送り戻す",
    "差し戻す",
    "つなぎ戻す",
    "送り返す",
    "向け直す",
    "組み立て直す",
    "読み直す",
    "書き直す",
    "言い直す",
    "作り直す",
    "指し直す",
    "手渡す",
    "引き渡す",
    "受け渡す",
    "名指す",
    "指し示す",
    "書き下ろす",
    "降ろす",
    "剥がす",
    "やり直す",
    "証明し直す",
    "なす",
}

# These short native verbs have no corpus-relevant suru noun ending in the
# same kanji, so a suffix match is safe even after an unspaced adverb.  Roots
# such as 表す/示す/出す are intentionally absent: 代表する, 指示する,
# and 提出する show why their preceding boundary must be inspected.
UNAMBIGUOUS_GODAN_SU = {
    "戻す", "下ろす", "返す", "指す", "尽くす", "起こす", "落とす",
    "直す", "減らす", "ずらす", "崩す", "延ばす", "伸ばす", "動かす", "許す",
    "残す", "外す", "飛ばす", "果たす", "降ろす", "剥がす", "なす",
}

# Native -う verbs found in this tree.  A bare polite stem ending in い is
# otherwise ambiguous with いる (notably the progressive ています), so unknown
# -います forms are reported rather than guessed.
GODAN_U = {
    "使う",
    "扱う",
    "従う",
    "行う",
    "言う",
    "向かう",
    "伴う",
    "覆う",
    "担う",
    "違う",
    "失う",
    "払う",
    "出会う",
    "揃う",
    "整う",
    "沿う",
    "合う",
    "間違う",
    "拾う",
    "狙う",
    "賄う",
    "補う",
    "囲う",
    "追う",
    "問う",
    "しまう",
    "構う",
    "かまう",
    "そろう",
    "いう",
    "負う",
    "振る舞う",
}

I_TO_U = {
    "き": "く",
    "ぎ": "ぐ",
    "ち": "つ",
    "に": "ぬ",
    "び": "ぶ",
    "み": "む",
    "り": "る",
}
I_TO_A = {
    "き": "か",
    "ぎ": "が",
    "ち": "た",
    "に": "な",
    "び": "ば",
    "み": "ま",
    "り": "ら",
}
I_TO_PAST = {
    "き": "いた",
    "ぎ": "いだ",
    "ち": "った",
    "に": "んだ",
    "び": "んだ",
    "み": "んだ",
    "り": "った",
}
I_TO_VOLITIONAL = {
    "き": "こう",
    "ぎ": "ごう",
    "ち": "とう",
    "に": "のう",
    "び": "ぼう",
    "み": "もう",
    "り": "ろう",
}
ICHIDAN_STEM_ENDINGS = set("えけげせぜてでねへべぺめれじ")
JAPANESE_CHAR_RE = re.compile(r"[ぁ-んァ-ン一-龠々〆ヶ]$")
VERB_BOUNDARIES = set(" \t\n、。！？：；（(「『【をがにはへとでてものやかも")


@dataclass(frozen=True)
class Finding:
    path: Path
    line: int
    form: str
    excerpt: str
    reason: str = ""

    def render(self, root: Path) -> str:
        try:
            shown = self.path.relative_to(root)
        except ValueError:
            shown = self.path
        detail = f" [{self.reason}]" if self.reason else ""
        return f"{shown}:{self.line}: {self.form}: {self.excerpt}{detail}"


@dataclass
class FileResult:
    path: Path
    original: str
    converted: str
    replacements: Counter[str]
    unresolved: list[Finding]
    polite: list[Finding]
    protected_ignored: int


def _protected_ranges(text: str) -> list[tuple[int, int]]:
    """Return non-overlapping inline Markdown ranges that must not be edited."""
    ranges: list[tuple[int, int]] = []
    i = 0
    length = len(text)
    while i < length:
        if text[i] == "`":
            run = 1
            while i + run < length and text[i + run] == "`":
                run += 1
            marker = "`" * run
            end = text.find(marker, i + run)
            if end >= 0:
                ranges.append((i, end + run))
                i = end + run
                continue
        if text[i] == "<":
            end = text.find(">", i + 1)
            if end >= 0:
                ranges.append((i, end + 1))
                i = end + 1
                continue
        if text[i] == "{" and (i == 0 or text[i - 1] != "\\"):
            end = text.find("}", i + 1)
            if end >= 0:
                ranges.append((i, end + 1))
                i = end + 1
                continue
        if text[i] == "(" and i > 0 and text[i - 1] == "]":
            depth = 1
            j = i + 1
            angle = False
            while j < length and depth:
                char = text[j]
                if char == "<" and depth == 1:
                    angle = True
                elif char == ">" and angle:
                    angle = False
                elif not angle and char == "(":
                    depth += 1
                elif not angle and char == ")":
                    depth -= 1
                j += 1
            if depth == 0:
                ranges.append((i, j))
                i = j
                continue
        i += 1
    return ranges


def _mask_inline(text: str) -> tuple[str, list[str], int]:
    spans = _protected_ranges(text)
    if not spans:
        return text, [], 0
    pieces: list[str] = []
    protected: list[str] = []
    cursor = 0
    ignored = 0
    for start, end in spans:
        if start < cursor:
            continue
        pieces.append(text[cursor:start])
        value = text[start:end]
        ignored += sum(1 for _ in iter_polite(value))
        protected.append(value)
        pieces.append(f"\ue000{len(protected) - 1}\ue001")
        cursor = end
    pieces.append(text[cursor:])
    return "".join(pieces), protected, ignored


def _unmask_inline(text: str, protected: list[str]) -> str:
    def restore(match: re.Match[str]) -> str:
        return protected[int(match.group(1))]

    return TOKEN_RE.sub(restore, text)


def _replace_suffix(text: str, old: str, new: str) -> str:
    assert text.endswith(old)
    return text[: -len(old)] + new


def _has_word_suffix(text: str, suffix: str) -> bool:
    if not text.endswith(suffix):
        return False
    start = len(text) - len(suffix)
    return start == 0 or text[start - 1] in VERB_BOUNDARIES


def _matching_plain(prefix: str, entries: Iterable[str]) -> str | None:
    for plain in sorted(entries, key=len, reverse=True):
        polite_stem = plain[:-1] + "し"
        if not prefix.endswith(polite_stem):
            continue
        start = len(prefix) - len(polite_stem)
        # Complete compounds (four or more Japanese characters) have already
        # been reviewed and may follow prose without whitespace.  For short
        # base verbs, accept a normal boundary or a preceding kana adverb, but
        # not an arbitrary kanji: the latter would turn 代表します into 代表す.
        reviewed_compound = len(plain) >= 4 or plain in UNAMBIGUOUS_GODAN_SU
        kana_context = start > 0 and re.fullmatch(r"[ぁ-んァ-ンー]", prefix[start - 1])
        if reviewed_compound or _has_word_suffix(prefix, polite_stem) or kana_context:
            return _replace_suffix(prefix, polite_stem, plain)
    return None


def _auxiliary_plain(prefix: str, form: str) -> str | None:
    """Convert reviewed -te iru / -te kuru auxiliary chains.

    These are checked before the final polite-stem kana.  In particular,
    効いてきます contains 来る, not the godan verb 効く, and must become
    効いてくる rather than 効いてく.
    """
    tables = {
        "ます": (("てき", "てくる"), ("んでき", "んでくる"), ("いでき", "いでくる"), ("てい", "ている"), ("でい", "でいる")),
        "ません": (("てき", "てこない"), ("んでき", "んでこない"), ("いでき", "いでこない"), ("てい", "ていない"), ("でい", "でいない")),
        "ました": (("てき", "てきた"), ("んでき", "んできた"), ("いでき", "いできた"), ("てい", "ていた"), ("でい", "でいた")),
        "ましょう": (("てき", "てこよう"), ("んでき", "んでこよう"), ("いでき", "いでこよう"), ("てい", "ていよう"), ("でい", "でいよう")),
        "ませんでした": (("てき", "てこなかった"), ("んでき", "んでこなかった"), ("いでき", "いでこなかった"), ("てい", "ていなかった"), ("でい", "でいなかった")),
    }
    for old, new in tables.get(form, ()):
        if prefix.endswith(old):
            return _replace_suffix(prefix, old, new)
    return None


def _matching_ichidan(prefix: str) -> tuple[str, str] | None:
    for polite_stem, plain in sorted(
        ICHIDAN_PRESENT.items(), key=lambda item: len(item[0]), reverse=True
    ):
        if prefix.endswith(polite_stem):
            return polite_stem, plain
    return None


def _matching_godan_u(prefix: str) -> str | None:
    for plain in sorted(GODAN_U, key=len, reverse=True):
        polite_stem = plain[:-1] + "い"
        if prefix.endswith(polite_stem):
            return _replace_suffix(prefix, polite_stem, plain)
    return None


def plain_present(prefix: str) -> tuple[str | None, str]:
    """Turn a prefix ending in a polite verb stem into the plain present."""
    if prefix.endswith(("てい", "でい")):
        return prefix + "る", ""
    ichidan = _matching_ichidan(prefix)
    if ichidan:
        stem, plain = ichidan
        return _replace_suffix(prefix, stem, plain), ""
    godan_su = _matching_plain(prefix, GODAN_SU)
    if godan_su is not None:
        return godan_su, ""
    godan_u = _matching_godan_u(prefix)
    if godan_u is not None:
        return godan_u, ""
    if not prefix:
        return None, "missing verb stem"
    last = prefix[-1]
    if last == "い":
        return None, "ambiguous -います conjugation"
    if last == "し":
        return prefix[:-1] + "する", ""
    if last in I_TO_U:
        return prefix[:-1] + I_TO_U[last], ""
    if last in ICHIDAN_STEM_ENDINGS:
        return prefix + "る", ""
    if JAPANESE_CHAR_RE.search(prefix):
        return prefix + "る", ""
    return None, "unrecognized verb stem"


def plain_negative(prefix: str) -> tuple[str | None, str]:
    """Turn a prefix ending in a polite verb stem into the plain negative."""
    if prefix.endswith(("てい", "でい")):
        return prefix + "ない", ""
    ichidan = _matching_ichidan(prefix)
    if ichidan:
        stem, _plain = ichidan
        return _replace_suffix(prefix, stem, stem + "ない"), ""
    for plain in sorted(GODAN_SU, key=len, reverse=True):
        polite_stem = plain[:-1] + "し"
        if _has_word_suffix(prefix, polite_stem):
            return _replace_suffix(prefix, polite_stem, plain[:-1] + "さない"), ""
    for plain in sorted(GODAN_U, key=len, reverse=True):
        polite_stem = plain[:-1] + "い"
        if prefix.endswith(polite_stem):
            return _replace_suffix(prefix, polite_stem, plain[:-1] + "わない"), ""
    if not prefix:
        return None, "missing verb stem"
    last = prefix[-1]
    if last == "い":
        return None, "ambiguous -いません conjugation"
    if last == "し":
        return prefix + "ない", ""
    if last in I_TO_A:
        return prefix[:-1] + I_TO_A[last] + "ない", ""
    if last in ICHIDAN_STEM_ENDINGS:
        return prefix + "ない", ""
    if JAPANESE_CHAR_RE.search(prefix):
        return prefix + "ない", ""
    return None, "unrecognized verb stem"


def plain_past(prefix: str) -> tuple[str | None, str]:
    """Turn a prefix ending in a polite verb stem into the plain past."""
    if prefix.endswith(("てい", "でい")):
        return prefix + "た", ""
    ichidan = _matching_ichidan(prefix)
    if ichidan:
        stem, _plain = ichidan
        return _replace_suffix(prefix, stem, stem + "た"), ""
    if not prefix:
        return None, "missing verb stem"
    last = prefix[-1]
    if last == "い":
        for plain in sorted(GODAN_U, key=len, reverse=True):
            polite_stem = plain[:-1] + "い"
            if prefix.endswith(polite_stem):
                return _replace_suffix(prefix, polite_stem, plain[:-1] + "った"), ""
        return None, "ambiguous -いました conjugation"
    if last == "し":
        return prefix + "た", ""
    if last in I_TO_PAST:
        return prefix[:-1] + I_TO_PAST[last], ""
    if last in ICHIDAN_STEM_ENDINGS:
        return prefix + "た", ""
    if JAPANESE_CHAR_RE.search(prefix):
        return prefix + "た", ""
    return None, "unrecognized verb stem"


def plain_volitional(prefix: str) -> tuple[str | None, str]:
    """Turn a prefix ending in a polite verb stem into the plain volitional."""
    if prefix.endswith(("てい", "でい")):
        return prefix + "よう", ""
    ichidan = _matching_ichidan(prefix)
    if ichidan:
        stem, _plain = ichidan
        return _replace_suffix(prefix, stem, stem + "よう"), ""
    for plain in sorted(GODAN_SU, key=len, reverse=True):
        polite_stem = plain[:-1] + "し"
        if _has_word_suffix(prefix, polite_stem):
            return _replace_suffix(prefix, polite_stem, plain[:-1] + "そう"), ""
    for plain in sorted(GODAN_U, key=len, reverse=True):
        polite_stem = plain[:-1] + "い"
        if prefix.endswith(polite_stem):
            return _replace_suffix(prefix, polite_stem, plain[:-1] + "おう"), ""
    if not prefix:
        return None, "missing verb stem"
    last = prefix[-1]
    if last == "い":
        return None, "ambiguous -いましょう conjugation"
    if last == "し":
        return prefix[:-1] + "しよう", ""
    if last in I_TO_VOLITIONAL:
        return prefix[:-1] + I_TO_VOLITIONAL[last], ""
    if last in ICHIDAN_STEM_ENDINGS:
        return prefix + "よう", ""
    if JAPANESE_CHAR_RE.search(prefix):
        return prefix + "よう", ""
    return None, "unrecognized verb stem"


def _excerpt(text: str, start: int, end: int, radius: int = 36) -> str:
    left = max(0, start - radius)
    right = min(len(text), end + radius)
    clean = TOKEN_RE.sub("…", text[left:right]).strip()
    return ("…" if left else "") + clean + ("…" if right < len(text) else "")


def _convert_masked(
    text: str, path: Path, line_no: int
) -> tuple[str, Counter[str], list[Finding]]:
    replacements: Counter[str] = Counter()
    unresolved: list[Finding] = []

    def ending(match: re.Match[str]) -> str:
        return match.group("trailer") + (match.group("punct") or "")

    def adjective(match: re.Match[str]) -> str:
        replacements["です"] += 1
        return match.group("adjective") + ending(match)

    adjectives = "|".join(map(re.escape, sorted(I_ADJECTIVES, key=len, reverse=True)))
    text = re.sub(
        rf"(?P<adjective>{adjectives})(?P<form>です){BOUNDARY_PATTERN}",
        adjective,
        text,
    )
    text = re.sub(
        rf"(?P<adjective>[ぁ-んァ-ン一-龠々〆ヶ]+(?:くなかった|くない|かった))"
        rf"(?P<form>です){BOUNDARY_PATTERN}",
        adjective,
        text,
    )

    def special(match: re.Match[str]) -> str:
        form = match.group("form")
        if form == "です" and text[: match.start()].endswith("い"):
            prefix = text[: match.start()]
            if not any(prefix.endswith(noun) for noun in I_ENDING_NOUNS):
                unresolved.append(
                    Finding(
                        path,
                        line_no,
                        "いです",
                        _excerpt(text, match.start() - 1, match.end()),
                        "unknown -いです form; classify as adjective or noun",
                    )
                )
                return match.group(0)
        replacements[form] += 1
        return SPECIAL_REPLACEMENTS[form] + ending(match)

    pre_verb_specials = (
        "ではありませんでした",
        "じゃありませんでした",
        "ありませんでした",
        "ではありません",
        "じゃありません",
        "ありません",
    )
    text = re.sub(
        rf"(?P<form>{'|'.join(map(re.escape, pre_verb_specials))}){BOUNDARY_PATTERN}",
        special,
        text,
    )

    special_forms = "|".join(map(re.escape, SPECIAL_REPLACEMENTS))

    # These forms require the preceding polite stem.  Capturing a single final
    # Japanese character keeps particles and Markdown outside the conjugator;
    # the converter still receives the complete prefix for reviewed suffixes.
    verb_re = re.compile(
        rf"(?P<stem>[ぁ-んァ-ン一-龠々〆ヶ])"
        rf"(?P<form>ませんでした|ますです|ましょう|ました|ません|ます)"
        rf"{BOUNDARY_PATTERN}"
    )

    def verb(match: re.Match[str]) -> str:
        form = match.group("form")
        prefix = text[: match.start()] + match.group("stem")
        auxiliary_form = "ます" if form == "ますです" else form
        converted = _auxiliary_plain(prefix, auxiliary_form)
        reason = ""
        # A corpus typo such as 切り詰められたります is not a conjugation
        # the converter may repair by guessing.  Report it for human review.
        if converted is None and prefix.endswith("切り詰められたり"):
            reason = "suspicious -たります form; requires human review"
        elif converted is not None:
            pass
        elif form in {"ます", "ますです"}:
            converted, reason = plain_present(prefix)
        elif form == "ましょう":
            converted, reason = plain_volitional(prefix)
        elif form == "ません":
            converted, reason = plain_negative(prefix)
        elif form == "ました":
            converted, reason = plain_past(prefix)
        elif form == "ませんでした":
            negative, reason = plain_negative(prefix)
            converted = None if negative is None else negative[:-2] + "なかった"
        if converted is None:
            unresolved.append(
                Finding(
                    path,
                    line_no,
                    match.group("stem") + form,
                    _excerpt(text, match.start(), match.end()),
                    reason,
                )
            )
            return match.group(0)
        # re.sub needs only the replacement for the matched stem and suffix,
        # not the unchanged prefix used to classify the conjugation.
        unchanged_prefix = text[: match.start()]
        if not converted.startswith(unchanged_prefix):
            unresolved.append(
                Finding(
                    path,
                    line_no,
                    match.group("stem") + form,
                    _excerpt(text, match.start(), match.end()),
                    "conversion crossed a protected or Markdown boundary",
                )
            )
            return match.group(0)
        if form == "ますです":
            replacements["ます"] += 1
            replacements["です"] += 1
        else:
            replacements[form] += 1
        replacement = converted[len(unchanged_prefix) :]
        return replacement + ending(match)

    text = verb_re.sub(verb, text)
    text = re.sub(
        rf"(?P<form>{special_forms}){BOUNDARY_PATTERN}", special, text
    )

    # Anything still matching is either an unsupported conjugation or a form
    # deliberately left untouched above.  Report it exactly once.
    for match in iter_polite(text):
        if not any(
            item.line == line_no and item.form.endswith(match.group("form"))
            for item in unresolved
        ):
            unresolved.append(
                Finding(
                    path,
                    line_no,
                    match.group("form"),
                    _excerpt(text, match.start(), match.end()),
                    "unconverted polite ending",
                )
            )
    for match in INVALID_GENERATED_RE.finditer(text):
        unresolved.append(
            Finding(
                path,
                line_no,
                match.group(0),
                _excerpt(text, match.start(), match.end()),
                "invalid form produced by conjugation; add a reviewed rule",
            )
        )
    return text, replacements, unresolved


def _find_polite(text: str, path: Path, line_no: int) -> list[Finding]:
    return [
        Finding(path, line_no, match.group("form"), _excerpt(text, match.start(), match.end()))
        for match in iter_polite(text)
    ]


def process_file(path: Path, convert: bool) -> FileResult:
    original = path.read_bytes().decode("utf-8")
    lines = original.splitlines(keepends=True)
    output: list[str] = []
    replacements: Counter[str] = Counter()
    unresolved: list[Finding] = []
    polite: list[Finding] = []
    protected_ignored = 0
    in_ja = False
    fence_marker: str | None = None

    for line_no, line in enumerate(lines, 1):
        fence = FENCE_RE.match(line)
        if fence:
            marker = fence.group(1)[0]
            if fence_marker is None:
                fence_marker = marker
            elif fence_marker == marker:
                fence_marker = None
            if in_ja:
                protected_ignored += sum(1 for _ in iter_polite(line))
            output.append(line)
            continue
        if fence_marker is not None:
            if in_ja:
                protected_ignored += sum(1 for _ in iter_polite(line))
            output.append(line)
            continue

        # Markers normally occupy their own line, but splitting also preserves
        # the correct scope if a compact group places text beside a marker.
        pieces = re.split(f"({re.escape(JA_OPEN)}|{re.escape(GROUP_CLOSE)})", line)
        converted_pieces: list[str] = []
        for piece in pieces:
            if piece == JA_OPEN:
                in_ja = True
                converted_pieces.append(piece)
                continue
            if piece == GROUP_CLOSE:
                in_ja = False
                converted_pieces.append(piece)
                continue
            if not in_ja or not piece:
                converted_pieces.append(piece)
                continue
            masked, protected, ignored = _mask_inline(piece)
            protected_ignored += ignored
            polite.extend(_find_polite(masked, path, line_no))
            if convert:
                changed, counts, issues = _convert_masked(masked, path, line_no)
                replacements.update(counts)
                unresolved.extend(issues)
                converted_pieces.append(_unmask_inline(changed, protected))
            else:
                converted_pieces.append(piece)
        output.append("".join(converted_pieces))

    return FileResult(
        path,
        original,
        "".join(output),
        replacements,
        unresolved,
        polite,
        protected_ignored,
    )


def _atomic_write(path: Path, text: str) -> None:
    data = text.encode("utf-8")
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="apply safe conversions")
    mode.add_argument(
        "--check",
        action="store_true",
        help="report polite endings in the current files without converting",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="repository root (default: inferred from this script)",
    )
    parser.add_argument(
        "--max-report",
        type=int,
        default=0,
        help="limit printed findings; 0 prints every finding",
    )
    return parser.parse_args(argv)


def _print_findings(label: str, findings: list[Finding], root: Path, limit: int) -> None:
    if not findings:
        return
    print(f"{label}: {len(findings)}", file=sys.stderr)
    selected = findings if limit <= 0 else findings[:limit]
    for finding in selected:
        print(finding.render(root), file=sys.stderr)
    if len(selected) < len(findings):
        print(f"... {len(findings) - len(selected)} more", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    root = args.root.resolve()
    paths = sorted((root / "src").glob("**/*.lagda.md"))
    if not paths:
        print(f"no src/**/*.lagda.md files below {root}", file=sys.stderr)
        return 2

    results = [process_file(path, convert=not args.check) for path in paths]
    protected = sum(result.protected_ignored for result in results)

    if args.check:
        findings = [item for result in results for item in result.polite]
        counts = Counter(item.form for item in findings)
        print(f"mode: check")
        print(f"files scanned: {len(results)}")
        print(f"polite endings: {len(findings)}")
        print(f"forms: {dict(sorted(counts.items()))}")
        print(
            "protected matches ignored: "
            f"{protected} (fenced code, inline code, HTML, link targets, attributes)"
        )
        _print_findings("remaining polite endings", findings, root, args.max_report)
        return 1 if findings else 0

    changed = [result for result in results if result.converted != result.original]
    replacements = Counter()
    unresolved: list[Finding] = []
    for result in results:
        replacements.update(result.replacements)
        unresolved.extend(result.unresolved)

    mode = "write" if args.write else "dry-run"
    print(f"mode: {mode}")
    print(f"files scanned: {len(results)}")
    print(f"files changed: {len(changed)}")
    print(f"replacements: {sum(replacements.values())}")
    print(f"forms: {dict(sorted(replacements.items()))}")
    print(f"unresolved: {len(unresolved)}")
    print(
        "protected matches ignored: "
        f"{protected} (fenced code, inline code, HTML, link targets, attributes)"
    )
    _print_findings("unresolved forms", unresolved, root, args.max_report)

    if unresolved:
        print("no files written because unresolved forms remain", file=sys.stderr)
        return 2
    if args.write:
        for result in changed:
            _atomic_write(result.path, result.converted)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
