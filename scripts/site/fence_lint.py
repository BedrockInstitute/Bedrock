"""Code/prose boundary rules independent of filenames and discovery."""
import re
from reading_routes import strip_metadata
# An Agda identifier head. Agda admits primes, hyphens, dots and subscripts.
IDENT = r"[^\s():=|`*#>\-][^\s():=]*"

# THREE SHAPES, and the second one is why the first draft of this file was
# blind to the defect it was written for. A signature `f : T` matched, but a
# clause head with arguments, `AndAgree γ = mk ...`, did not, so every run
# broke at its second line and the checker stayed silent on a synthetic
# reproduction of the real defect. Test a checker against the thing it exists
# to catch, or it proves nothing.
SIG = re.compile(rf"^\s*{IDENT}\s*:\s")                    # f : T
CLAUSE = re.compile(rf"^\s*{IDENT}(\s+[^\s=]+)*\s*=\s")    # f x y = e
KEYWORD = re.compile(r"^\s*(where|module|open|private|data|record|"
                     r"postulate|mutual|abstract|opaque|instance|variable)\b")


def looks_like_agda(line: str) -> bool:
    return bool(SIG.match(line) or CLAUSE.match(line) or KEYWORD.match(line))

# Lines that are prose by construction, whatever else they look like.
PROSE_HEAD = ("-", "*", "|", ">", "#", "<!--", "`")

# MARKDOWN MARKERS THAT NEVER OCCUR IN AGDA CODE, and they are the whole
# reason this checker can be quiet. This repository's prose names Agda
# identifiers as `foo`{.Agda}, so a backtick is a certain sign of prose. The
# first draft checked only the FIRST character of a line and fired on wrapped
# paragraphs in a literate master and the former catalog master.
PROSE_ANYWHERE = ("`", "**", "{.Agda}", "<!--")

DEFAULT_RUN = 3

# RULE 2. A line comment or a block comment inside a ```agda fence.
# `{-# ... #-}` is a pragma, not a comment, and stays.
LINE_COMMENT = re.compile(r"^\s*--(\s|$|-)")
BLOCK_OPEN = re.compile(r"^\s*\{-(?!#)")
BLOCK_CLOSE = re.compile(r"-\}")
LANGUAGE_MARKER = re.compile(r"<!--(?:en|zh|ja|/)-->")

REMEDY = """    HOW TO FIX ONE. Do not delete the sentence: split the fence where the
    comment is, and write it as prose between the two halves.

        ```agda            ```agda
        f : A → B          f : A → B
        -- why it is so    ```
        f x = ...
        ```                Why it is so.

                           ```agda
                           f x = ...
                           ```

    A fence may be split ANYWHERE, including inside a `where` block: Agda
    blanks the prose and keeps every line and column, so the layout survives
    and the definition is still one definition. This was measured, not assumed.
    An `{-# OPTIONS ... #-}` pragma is not a comment and is exempt."""


def fenced_comments(text: str) -> list[tuple[int, str]]:
    """Every comment line inside a ```agda fence."""
    fenced = False
    in_block = False
    hits: list[tuple[int, str]] = []
    for i, line in enumerate(text.split("\n"), 1):
        if line.startswith("```agda"):
            fenced = True
            continue
        if line.startswith("```"):
            fenced = False
            in_block = False
            continue
        if not fenced:
            continue
        if in_block:
            hits.append((i, line))
            if BLOCK_CLOSE.search(line):
                in_block = False
            continue
        if BLOCK_OPEN.match(line):
            hits.append((i, line))
            if not BLOCK_CLOSE.search(line):
                in_block = True
            continue
        if LINE_COMMENT.match(line):
            hits.append((i, line))
    return hits


def tight_language_boundaries(text: str) -> list[int]:
    """Closing fences immediately followed by a language marker."""
    lines = text.splitlines()
    return [
        i + 2
        for i, (line, following) in enumerate(zip(lines, lines[1:]))
        if line == "```" and LANGUAGE_MARKER.fullmatch(following)
    ]



def suspects(text: str, run: int) -> list[tuple[int, str]]:
    fenced = False
    streak: list[tuple[int, str]] = []
    hits: list[tuple[int, str]] = []
    # Route metadata contains declaration-shaped JSON lines. Blank only the
    # recognized marker, preserving every newline so reported source locations
    # remain exact. Other HTML comments still pass through the ordinary scan.
    text = strip_metadata(text)
    for i, line in enumerate(text.split("\n"), 1):
        if line.startswith("```agda"):
            fenced = True
            streak = []
            continue
        if line.startswith("```"):
            fenced = False
            streak = []
            continue
        if fenced:
            continue
        stripped = line.lstrip()
        if not stripped:
            # A blank line ends a run: real Agda blocks are contiguous.
            if len(streak) >= run:
                hits.extend(streak)
            streak = []
            continue
        # An INDENTED line continues a run that has already started: a `where`
        # block's body is Agda but rarely matches a declaration shape on its
        # own. It never STARTS a run, so an indented prose line is inert.
        continues = bool(streak) and line[:1] in (" ", "\t")
        prose = (stripped.startswith(PROSE_HEAD)
                 or any(mark in line for mark in PROSE_ANYWHERE))
        if prose or not (looks_like_agda(line) or continues):
            if len(streak) >= run:
                hits.extend(streak)
            streak = []
            continue
        streak.append((i, line))
    if len(streak) >= run:
        hits.extend(streak)
    return hits
