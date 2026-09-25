#!/usr/bin/env python3
"""Prose linter for Bedrock: enforces CJK punctuation conventions and bans em dashes.

Rules (apply to Markdown prose, `*.md` / `*.lagda.md`; the verbatim LICENSE is excluded):

  1. Sentence punctuation , ; : ! ?  -> full-width ，；：！？ in Chinese context   [auto-fix]
  2. Chinese double quotes "..." / “...”  -> 「...」                               [auto-fix]
  3. Parentheses in Chinese context must be half-width ( ), with English-style outer
     spacing: a space before '(' and after ')'   (e.g. 经典原理 (LEM、AC) 是…)        [auto-fix]
     No space before/after a full-width symbol; no space between two Chinese
     characters (markdown-adjacent spaces are exempt). A soft line-wrap that falls
     between two CJK characters renders as a space, so such paragraphs are reflowed
     (the wrapped lines are joined); breaks at Latin word boundaries are kept.        [auto-fix]
  4. No em dash — (U+2014), ― (U+2015), or 中文 破折号 ——                          [report only]
  5. No single quotes as quotation marks in Chinese context, no quote nesting       [report only]
  6. Inside an ```agda code block: no Chinese or full-width symbols (the CJK prose
     rules do not apply there); Agda's own Unicode (≡ ℕ λ …) is fine                 [report only]
  7. No CJK in SHARED prose of a src/ master, meaning prose outside every
     <!--en|zh|ja--> block, because that text reaches the English book verbatim
     (C-8). This one reads all masters and not the FILE list, so it runs only
     when the caller names no file.                                              [report only]
  8. A centered single-line code display must use one complete
     `<div class="single-line-code"><code>...</code></div>` line.                 [report only]
 9. Standalone theorem-style labels use a bold label followed by a space, never a
     period. Fact, lemma, theorem and corollary labels must immediately name an Agda declaration:
     `**Fact** (`name`{.Agda}) Text` (likewise in Chinese and Japanese).         [report only]
 10. Every definition, construction, fact, lemma, theorem, corollary or proof
     encloses Agda code; semantic definition endings require no prose end mark.
     Folded helpers obey the same rule. Parallel names use one Construction
     header and a bullet per name, never several empty parallel labels.       [report only]
 11. Foldable
     submodules use a single-line Agda declaration as their summary and close
     after the submodule's last code block.                                      [report only]
 12. Japanese prose uses plain style (である体), not polite です・ます forms.      [report only]
 13. An unboxed Agda link names one declaration only. Applications, type
     annotations and equations use one complete inline-code span.             [report only]
 14. In every chapter, standalone symbolic variables in prose use inline Agda
     markup. Exact pre-existing lines are tracked as a shrinking legacy list. [report only]
 15. Inline LaTeX outside figures requires an explicit human approval tied to
     its exact context. Explicit temporary chapter allowances end when the
     catalog marks human_reviewed true. Standalone display math is allowed.  [report only]

"Chinese context" = the punctuation is adjacent to (or, for quotes/parens, wraps) a
CJK ideograph or CJK punctuation, looking past whitespace, markdown emphasis markers,
inline code, links and URLs. English apostrophes (V's, field's) and English quotes
("formal purity") are not in Chinese context and are left untouched.

Code spans, fenced code blocks, markdown link/image destinations and URLs are protected.

Usage:
  lint-prose.py [--check | --fix] [--staged] [FILE ...]
  default mode is --check; with no FILE and no --staged, scans git-tracked *.md/*.lagda.md.
  The archive (archive/) is never scanned: it is outside every gate
  (archived D20; the live home of that rule is DD13).
Exit status is non-zero if any violation remains (in --fix, only the report-only ones).
"""

import json
import os
import subprocess
import sys
from pathlib import Path

# CUTOVER STEP 7 gave this per-file linter its first whole-tree check, so it needs
# a root. It had none: every other check here reads the files named on the command
# line. ROOT is derived from this file's own location and never from the cwd.
ROOT = Path(__file__).resolve().parent.parent.parent
SRC = ROOT / "src"

from outcrop.site import SiteConfig
_SITE_CONFIG = SiteConfig.load(ROOT / 'site/project.json', root=ROOT)
_BARE_VARIABLE_LEGACY_PATH = _SITE_CONFIG.path(_SITE_CONFIG.values['variable_legacy'])

from outcrop.core.prose_lint import EXCLUDE_BASENAMES, ProsePolicy
from outcrop.core.prose_lint import analyze as analyze_prose, theorem_label_violations as label_violations
from outcrop.core.prose_lint import new_bare_variable_violations as bare_variable_policy_violations
from outcrop.core.i18n_markers import shared_cjk_errors
from outcrop.site.math_review import load_math_review
_MATH_APPROVALS, _MATH_TEMPORARY = load_math_review(_SITE_CONFIG)
def load_bare_variable_legacy():
    """Exact old prose lines, never chapter-level exclusions."""
    with _BARE_VARIABLE_LEGACY_PATH.open(encoding="utf-8") as source:
        entries = json.load(source)
    if entries.get("version") != 1:
        raise ValueError("unknown inline Agda legacy inventory version")
    return {chapter: set(lines) for chapter, lines in entries["lines"].items()}


_BARE_VARIABLE_LEGACY = load_bare_variable_legacy()

def new_bare_variable_violations(text, chapter, legacy=None):
    return bare_variable_policy_violations(text, chapter,
        _BARE_VARIABLE_LEGACY if legacy is None else legacy)



def theorem_label_violations(text, path=None):
    numbered = range(5) if path and Path(path).resolve() == SRC / 'Origin.lagda.md' else ()
    return label_violations(text, numbered_theorems=numbered)

def analyze(text, path=None):
    chapter = None
    if path is not None:
        try:
            chapter = Path(path).resolve().relative_to(SRC).as_posix()
        except ValueError:
            pass
    policy = ProsePolicy(chapter=chapter or '', numbered_theorems=tuple(range(5)) if chapter == 'Origin.lagda.md' else (),
                         require_submodules=chapter is not None, variables=chapter is not None,
                         inline_code=path is None or chapter is not None,
                         inline_math_review=chapter is not None and _SITE_CONFIG.policies.get('inline_math_review', True),
                         math_approvals=_MATH_APPROVALS,
                         math_temporary=_MATH_TEMPORARY,
                         variable_legacy=_BARE_VARIABLE_LEGACY)
    return analyze_prose(text, policy=policy)

# ---- driver ------------------------------------------------------------------

def line_of(text, index):
    return text.count("\n", 0, index) + 1


def report(path, text, violations):
    for v in sorted(violations, key=lambda x: x.index):
        ln = line_of(text, v.index)
        print(f"{path}:{ln}: {v.message}")


def git_lines(args):
    try:
        out = subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    return [l for l in out.splitlines() if l]


def target_files(explicit, staged):
    if explicit:
        files = explicit
    elif staged:
        files = git_lines(["diff", "--cached", "--name-only", "--diff-filter=ACM"])
    else:
        files = sorted(set(git_lines(["ls-files", "--cached", "--others", "--exclude-standard", "*.md", "*.lagda.md"])))
    return [f for f in files
            if (f.endswith(".md") or f.endswith(".lagda.md"))
            and os.path.basename(f).lower() not in EXCLUDE_BASENAMES
            and not f.startswith(".claude/")    # Claude skill/config, not prose docs
            and not f.startswith("archive/")    # outside every gate (archived D20, live DD13)
            # Compiler HTML is an input fixture, not an authored Markdown master.
            # Its corresponding examples/renderer/chapters sources are linted.
            and not f.startswith("outcrop/")  # independent project, linted by its own configured gate
            # A brief and a report are FROZEN RECORDS. A brief says what an agent was told
            # on a date; a report says what it found. Neither is live guidance, and neither
            # is ever rewritten, so a style gate over them can only force an edit to a
            # record, which corrupts the record it was meant to protect. The same reasoning
            # used to exempt the per-episode journal; that file is archived.
            # Measured when the tree
            # moved here on 2026-08-13: 1,109 violations in 74 archived reports and 24 in 10
            # briefs, none of them a defect in anything the project still runs on.
            and not f.startswith("agents/")]


def main(argv):
    mode = "check"
    staged = False
    docs_only = False
    paths = []
    for a in argv:
        if a == "--check":
            mode = "check"
        elif a == "--fix":
            mode = "fix"
        elif a == "--staged":
            staged = True
        elif a == "--docs-only":
            docs_only = True
        elif a.startswith("-"):
            sys.stderr.write(f"unknown option: {a}\n")
            return 2
        else:
            paths.append(a)

    files = target_files(paths, staged)
    if docs_only:
        files = [path for path in files if not Path(path).resolve().is_relative_to(SRC)]
    total_fixable = 0
    total_manual = 0
    fixed_files = []

    for path in files:
        try:
            with open(path, encoding="utf-8") as fh:
                text = fh.read()
        except (OSError, UnicodeDecodeError):
            continue
        fixed, fixable, manual = analyze(text, path)

        if mode == "fix":
            cur = text
            for _ in range(6):  # converge: char fixes + reflow may interact
                nxt = analyze(cur, path)[0]
                if nxt == cur:
                    break
                cur = nxt
            if cur != text:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(cur)
                fixed_files.append(path)
            # report manual violations against the fixed text
            manual = analyze(cur, path)[2]
            if manual:
                report(path, cur, manual)
                total_manual += len(manual)
        else:  # check
            if fixable:
                report(path, text, fixable)
                total_fixable += len(fixable)
            if manual:
                report(path, text, manual)
                total_manual += len(manual)

    if mode == "fix":
        for p in fixed_files:
            print(f"fixed: {p}", file=sys.stderr)
        if total_manual:
            print(f"\n{total_manual} issue(s) need manual rewriting (em dash / single quote / nesting).", file=sys.stderr)
            return 1
        return 0
    else:
        rc = 0
        if total_fixable or total_manual:
            hint = "run: python3 scripts/gate/lint-prose.py --fix <files>  (auto-fixes punctuation/quotes; em dash & nesting are manual)"
            print(f"\n{total_fixable + total_manual} violation(s). {hint}", file=sys.stderr)
            rc = 1
        # C-8, the shared-CJK check. It reads every master under src/ and not the
        # file list, so a caller that NAMES files gets the lint alone. `make check`
        # and the pre-commit hook both name none, which is why this fires at both.
        if not paths and not docs_only:
            cjk = check_shared_cjk()
            for msg in cjk:
                print(msg, file=sys.stderr)
            if cjk:
                print(f"\n{len(cjk)} shared-CJK violation(s).", file=sys.stderr)
                rc = 1
        return rc


# ---------------------------------------------------------------------------
# WIRED 2026-08-18. The move above landed both functions BELOW the `__main__`
# guard, so in script mode neither `def` ever ran, and no module in the tree
# imports this file. C-8's shared-CJK check was therefore retired in silence
# from the cutover until now, while the cutover commit fc676cb reported it moved
# and verified. `main()` calls `check_shared_cjk()` on the check path, which is
# both enforcement points the design names for it: the pre-commit hook, which
# passes `--staged`, and conjunct 6, which passes `--check`.
# It reads 99 masters in 0.031 s (measured 2026-08-18), so a hook can pay it.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# MOVED HERE BY THE POD CUTOVER, step 7, 2026-08-18. It lived in
# scripts/gate/check-tree.py, which the cutover splits: the closure half became
# scripts/pod/check-closure.py and this half had no home. **Moving it is what
# keeps the check alive**: archiving check-tree.py without this move would have
# retired a live check in silence, which is the failure clause W4 exists for.
# ---------------------------------------------------------------------------
def _masters_for_cjk() -> list[Path]:
    """The working tree, not the index: a new untracked master must not escape the audit."""
    return sorted(p for p in SRC.rglob("*.lagda.md"))

def check_shared_cjk() -> list[str]:
    """Prose outside every language marker is shared and reaches the English book verbatim."""
    bad = []
    for p in _masters_for_cjk():
        for n, message in shared_cjk_errors(p.read_text(encoding='utf-8')):
            bad.append(f'{p.relative_to(ROOT)}:{n}: CJK_SHARED: {message}; wrap it in a language block')
    return bad


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
