# scripts

Repository tooling. English-only: this is developer documentation. User-facing docs
(`docs/<lang>/`) are trilingual; developer docs are English. Developer docs include `dev/`,
the root `AGENTS.md` and `CONTRIBUTING.md`, the per-directory `README.md` files such as this
one, and anything else written for contributors. See [AGENTS.md](../AGENTS.md) for the full
rulebook and the user/developer doc split. The marker grammar these tools share is specified in
[dev/STYLE-i18n.md](../dev/STYLE-i18n.md).

## The multilingual literate-Agda pipeline

A master `.lagda.md` per module holds the Agda code once plus prose for every language,
wrapped in `<!--en--> / <!--zh--> / <!--ja--> / <!--/-->` markers. From the masters:

```
src/**/*.lagda.md ──agda──────────────► typecheck (the proof gate)
        │
        ├─ weave-i18n.py ─► _build/woven/<lang>/…  (mono-lingual .lagda.md, on demand)
        │
        └─ render-site.py ─► _build/site/<lang>/…  (the hyperlinked multilingual site)
                 ▲   uses: agda --html  +  extract-types.py  +  vendored 1lab assets
        └─ gen-depmap.py ─► _build/site/<lang>/depmap.html  (the dependency map)
```

Everything generated lives under `_build/` (git-ignored); nothing generated is committed.

## `i18n_markers.py`

The single canonical implementation of the marker grammar (parse / weave / validate),
imported by `weave-i18n.py` and `render-site.py` so the grammar can never drift. Not a CLI.

## `weave-i18n.py`

Weaves masters into per-language mono-lingual `.lagda.md` (kept on demand for
`agda --html` compatibility, never committed), and validates marker integrity.

```sh
python3 scripts/weave-i18n.py --check                 # validate markers (exit 1 on error)
python3 scripts/weave-i18n.py --lang zh FILE          # weave one master -> stdout
python3 scripts/weave-i18n.py --gen --out _build/woven  # weave all -> _build/woven/<lang>/
```

`--gen` also drops a per-language `bedrock.agda-lib` so each woven tree type-checks and
`agda --html`-es on its own (consume it outside the source project to avoid include-path
clashes with the root `bedrock.agda-lib`).

## `extract-types.py`

Extracts per-module identifier types for type-on-hover and typed search, on stock Agda
2.8.0, by driving Agda's batch interaction protocol (`agda --interaction-json`,
`Cmd_show_module_contents_toplevel`). No Haskell, no Agda-as-a-library.

```sh
python3 scripts/extract-types.py --out _build/types.json
```

## `render-site.py`

Builds the hyperlinked multilingual static site from the masters: runs `agda --html`,
weaves prose per language, splices the (language-neutral) highlighted code, resolves inline
`` `name`{.Agda} `` references, renders math (KaTeX) and Markdown, rewrites links, emits the
per-module `types/<Module>.json` (for hover) and per-language `search.json`, and wraps each
page in the vendored 1lab-styled template.

```sh
python3 scripts/render-site.py --out _build/site [--langs en,zh] [--base-url /Bedrock]
```

See the root `Makefile` (`make site`, `make serve`) for the orchestrated build.

## `lint-prose.py`

Enforces the project's CJK writing conventions on Markdown (`*.md`, `*.lagda.md`; the
verbatim `LICENSE` is excluded):

- Chinese sentence punctuation `, ; : ! ?` must be full-width `，；：！？` (auto-fixable).
- Chinese double quotes use the corner brackets `「」`, not `"…"` / `“…”` (auto-fixable).
- Parentheses in Chinese text stay half-width `()` with English-style outer spacing; no
  space between CJK characters; no space adjacent to a full-width symbol; CJK paragraphs are
  reflowed so a soft wrap never falls between two CJK characters. All auto-fixable.
- The i18n marker lines (`<!--en|zh|ja|/-->`) are treated as hard block boundaries, so
  reflow never merges prose across a language switch.
- Inline `` `code` ``, fenced blocks, links, URLs, and math (`$...$`, `$$...$$`) are
  protected from the CJK rules.
- Em dash (`—`, `―`, `——`) is banned; en dash `–` and hyphen `-` are allowed.
- Single quotes as Chinese quotation marks, and any quote nesting, are banned.
- Inside an `agda` fenced block, Chinese and full-width symbols are banned (translate to
  English); Agda's own Unicode (`≡ ℕ λ`) is fine.

```sh
python3 scripts/lint-prose.py --check          # scan tracked files; exit 1 on any violation
python3 scripts/lint-prose.py --fix <files>    # auto-fix punctuation/quotes (dashes/nesting are manual)
python3 scripts/lint-prose.py --check --staged # only staged files (used by the hook)
```

## `check-glossary.py`

Enforces the translation glossary so term renderings cannot drift between passes. Its data source
is [dev/glossary.toml](../dev/glossary.toml), read via `tomllib` (so Python 3.11+; use the `.venv`
from `make venv`); the human-readable explanation is [dev/GLOSSARY.md](../dev/GLOSSARY.md). For each
term's `avoid` entries it scans the CJK docs (`docs/zh/`, `docs/ja/`, and the `<!--zh-->` / `<!--ja-->`
prose of masters) and reports any off-glossary rendering, pointing at the canonical one. A
`zh:`/`ja:` tag scopes an avoided term to one language; an untagged one applies to both.
Code spans, fenced blocks, links and URLs are protected (shared with `lint-prose.py`).
Report-only, like the em-dash rule: there is no `--fix`. Suppress a genuine exception with
`<!-- glossary-ignore -->` (or `<!-- glossary-ignore: charter -->`) on the line.

```sh
python3 scripts/check-glossary.py --check          # scan tracked files; exit 1 on any violation
python3 scripts/check-glossary.py --check --staged # only staged files (used by the hook)
```

## `ledger.py`

Computes the size ledger. Its data source is [dev/ledger.toml](../dev/ledger.toml), read via
`tomllib`; the reasoning lives in that file's own header comment. It measures
**standing** from the tree (non-blank lines inside ` ```agda ` fences, over git-tracked
`*.lagda.md` under `src/`, minus the declared retirement set), then sums the remaining rows
into an endpoint.

**Three declarations are SUSPENDED today** and the tool reports rather than enforces each:
`retire_suspended` (the retirement set was ruled for the retired route, so standing is the
whole tree), `trophy_split_suspended` (its roots name modules that left `src/`), and
`remaining_stale` (the `[[remaining]]` rows price the retired route, so `--brief` REFUSES the
endpoint and says why). Each names its re-arm task in `dev/ledger.toml`. **DD7 revoked the
two-caliber rule**, so when the rows are rebuilt the endpoint is ONE best-effort band naming
its basis; the matrix keeps both calibers as a DD5 diagnostic.

**Standing appears in no file and never will.** The script exists because a standing figure
written in prose was fixed as a projection and then re-quoted unchecked for nine dispatches
while the tree moved under it; the cure is that the number is computed and never stored. The
`--check` mode is what `make check` runs: it fails on a retirement entry naming a file no longer
in the tree, a remaining row missing a band or its provenance, an inverted band, or a calibrated
band below its naive one.

```sh
python3 scripts/ledger.py           # the full ledger
python3 scripts/ledger.py --brief   # one line: standing, endpoint, overage
python3 scripts/ledger.py --check   # validate the declaration; exit 1 on a defect
```

**`--check` enforces DD5's a-priori ceiling.** When `lines_state` says the line benchmark BINDS,
the declaration must carry `lines_apriori`, `[LJ-1.1]`'s projection recorded before any phase-1
build, and the binding figure must be the SMALLER of it and the measurement. The gate is silent
while the state reads unbound, so it costs nothing through phase 1 and fires the day the number
starts to matter. It exists because the benchmark is measured from a wing this project builds
itself: a wing larger than it needed to be raises the bar by exactly that much, and no
dishonesty is required for that to happen.

**`--reuse` is DD4's REPORT and never a gate.** It prints what the AC and GCH endpoints' import
closures share, in masters and lines, with each side's total and the shared share of the union.
It exits 0 whatever it finds and is NOT in `make check`, because DD4 has no threshold by ruling:
a shared-line count used as a pass-or-fail is gamed by moving code into a shared module neither
proof needs. `[LJ-0.3]` separated the gate from the measurement and the owner adopted the split.
The roots are declared in `dev/ledger.toml`'s `[reuse]` block; with no GCH endpoint in the tree
the tool says so instead of computing a number.

```sh
python3 scripts/ledger.py --reuse
```

## `deletion-test.py`

The deletion test is a STRUCTURAL judgment, runnable on demand: the AC
endpoint must typecheck, exit 0, in a tree with every gch-side master
removed. `[T147]` ran it once by hand and this tool makes it repeatable.

**It is suspended twice over today, and it says so instead of passing.** The
cap it compared against (D36's, raised to 20,000 on 2026-08-09) is retired by
DD5, and `trophy_split_suspended` empties the partition, so there is no
gch side to delete: a run would typecheck the whole tree and print a PASS.
`--run` therefore REFUSES, and `--shadow` prints `SPLIT VACUOUS`. Re-arm is
`[LJ-2.1]`. A vacuous pass is worse than a refusal, because a pass gets
quoted.

The shadow mode is the daily proxy. It reuses `scripts/ledger.py`'s trophy
split by import, so the two can never drift apart silently. It reports the
count, the cap, the headroom, and the file list on request. The count is
file-granular. The board discloses the granularity error `[T155]` measured
at 2,069-2,248 lines. The `--run` mode is the real test. It creates a git
worktree and removes every gch-side master. It generates a root module that
imports every remaining AC-side master. It typechecks the root under
`GHCRTS=-M8g`. It refuses without `--yes`. It refuses when another Agda
process is live.

The tool is a MEASUREMENT, not a gate. It is deliberately NOT part of
`make check`: `--run` costs minutes, and the judgment runs at the landing,
not at every commit.

```sh
python3 scripts/deletion-test.py                # shadow: count, cap, headroom
python3 scripts/deletion-test.py --files        # shadow, with the AC-side file set
python3 scripts/deletion-test.py --run --yes    # the real test (guarded)
```

## `check-probes.py`

The never-commit gate, plus the probe lifecycle. Two standing rules from `AGENTS.md`'s Never
list: probe files are never committed (`dev/LESSONS.md` D-1), and generated files (anything
under `_build/`, the woven mono-lingual copies) are never committed.

`.gitignore` already covers both, which is exactly why this exists: **an ignore rule is a
default, not a gate.** `git add -f` walks past it and a pattern that stops matching a new
naming shape fails silently. On 2026-08-04 one `git add -A src/` committed 13 probe files,
3,274 lines. `--staged` runs in the pre-commit hook and stops the commit; `--check` runs in
`make check` over every tracked file and catches anything that got in historically or past a
bypass.

`--stale` carries the half an ignore rule cannot express: a probe is **thrown away** once its
verdict is recorded, and untracked probes otherwise pile up in `src/` where they are mistaken
for committed ones. A probe is deletable only when its verdict survives (some report under
`_build/` names it) AND nobody is writing it (untouched for longer than the freshness window,
default 6 hours). Anything else is listed as PROTECTED with the reason.

```sh
python3 scripts/check-probes.py --check           # every tracked file (make check)
python3 scripts/check-probes.py --staged          # staged files only (pre-commit hook)
python3 scripts/check-probes.py --stale           # what is safe to delete, and why
python3 scripts/check-probes.py --stale --delete  # delete it
```

## `check-tree.py`

Whole-tree invariants that the per-file linters structurally cannot see, because they read one
file at a time.

The one that matters most is **closure** (`dev/PLAN.md` section 7 rule 3): every master under
`src/` must appear in `src/Everything.lagda.md`'s import list. `make check` typechecks exactly
one file, which is what makes it a trusted single invocation, and the price is that **a master
nobody imports is never typechecked while the gate still goes green**. PLAN specified this
audit from the beginning and nothing had implemented it; on its first run it found a real
in-progress chapter sitting outside the gate. The others: **archive** (no live master imports a
module that lives only in `archive/`, D20), **shared-cjk** (no CJK in marker-free prose, which
would reach the English book verbatim, C-8), **spdx** (licensing has one source of truth, D4),
**retiring**, WARN only and SILENT today (it flagged a surviving master importing a chapter
the retired route's D18 was retiring; `retire_suspended` empties that set, so the check returns
nothing until the new route rules its own retirements), and **module-body**, WARN only (C-11's
silently empty parameterized module).

Its docstring also records what was deliberately NOT made a check and why, since three
proposals were rejected on false-positive grounds: a rule already enforced by Agda itself, a
rule whose only hit is in code booked for retirement, and a rule whose predicate cannot tell a
goal's status from a sub-item's.

It also carries the **gate-debt** counter. A full `agda src/Everything.lagda.md` costs not its
twelve background minutes but the **quiet tree** it needs for all of them: no agent may write a
master while it runs, so every full gate costs one dispatch window. Full gates are therefore
batched (`dev/PLAN.md` D28), and this reports whether one is due.

```sh
python3 scripts/check-tree.py --check            # every invariant (make check and the hook)
python3 scripts/check-tree.py --check closure    # just one
python3 scripts/check-tree.py --gate-debt        # commits and added lines since the last gate
python3 scripts/check-tree.py --gate-passed      # record HEAD after a green full gate
```

## `check-dev-docs.py`

The maintenance mechanism for the dev/ documents, built by `[L3.32-T110]`
after a day in which every decay instance below was found by accident and
none by a gate. The cadence, the thresholds with their arguments, and what is
deliberately not automated are recorded in
this script's own docstring, which is its operative home.

The gate half (`make check`'s `devdocs` target) is six cheap pure-Python
checks: a word cap on AGENTS.md (2,200), a word cap on every dev/PLAN.md
table cell (1,600), a requirement that a LESSONS entry marked "imported
from/into" be routed in dev/rules.toml, a check that PLAN section 0's "as of"
date is no older than the newest date in its own body, a form check on
dev/memos/ `**STATUS:` headers, and a check that every `scripts/*.py` named
in AGENTS.md exists.

The sweep half is informational and exits 0: it lists LESSONS entries that
are unrouted AND cited nowhere (the "landed and nobody noticed" class), and
section 11 cells over the 600-word episode-scale line (episode content
belongs in dev/JOURNAL.md).

```sh
python3 scripts/check-dev-docs.py            # run every gate subcheck
python3 scripts/check-dev-docs.py --check NAME  # run one
python3 scripts/check-dev-docs.py --sweep    # on-demand informational sweep
```

## `check-agents-guard.py`

The AGENTS.md guard (ruling D34, owner-approved 2026-08-07). AGENTS.md loads
into every agent session, so a wrong sentence there governs all work
silently; the one-process incident (see the script's docstring) is why this
exists. A commit that edits AGENTS.md must carry the owner's dated approval
trailer, `AGENTS-diff-approved: YYYY-MM-DD`, written only after the owner
ruled on the presented diff.

Two modes: with no arguments (the `agentsguard` target in `make check`) it
audits history, judging only commits whose own tree contains the guard;
with `--msg-file` (the `commit-msg` hook) it refuses a trailerless commit
that stages the file.

```sh
python3 scripts/check-agents-guard.py                 # history audit
python3 scripts/check-agents-guard.py --msg-file MSG  # commit-msg hook mode
```

## `lint-agda.py`

Enforces the code-side rules of [dev/STYLE-agda.md](../dev/STYLE-agda.md) on the ```agda
fences of the masters (report-only; prose is `lint-prose.py`'s business):

- `[options]` the file's first pragma is exactly `{-# OPTIONS --cubical --safe --guardedness #-}`.
- `[bare-open]` every `open import` carries a `using`/`renaming` list (`hiding` alone does
  not qualify). Exempt: `Everything`, and the designated hub modules (`Base.Prelude`,
  `Base.Truth`), which are curated re-export preludes designed to be opened wholesale.
- `[unused-import]` **import necessity**: every name bound by a `using`/`renaming` clause
  (of an import or a plain `open`), and the handle of every qualified `import M [as A]`,
  is actually used outside the binding clauses. Sufficiency is exactly what `agda`
  typechecking enforces, so together imports are always necessary and sufficient.
  Exempt: `Everything`, `... public` re-exports, and names ending in `-syntax` (used
  through their notation). Usage detection is lexical (mixfix names match by their name
  parts); a name imported from two modules and used once leaves both unflagged.
- `[forbidden]` no `postulate`, no `TERMINATING`-family pragma, no interaction holes
  (`{! !}` or a bare `?`): no debt form is sanctioned. The Frontier record (dev/PLAN.md
  §5) was the one exception and is gone, deleted with its last field.

Suppress a genuine exception (e.g. an instance-only import) with a `-- lint-agda: keep`
comment on the import line or the line above it.

```sh
python3 scripts/lint-agda.py --check           # scan tracked src masters; exit 1 on any violation
python3 scripts/lint-agda.py <files>           # specific masters (used by the hook)
```

## The archive

Archived modules live in `archive/` at the repository root, outside `src/`, so
every gate is structurally blind to them (D20, `dev/PLAN.md` section 3).
`lint-agda.py` and `weave-i18n.py` scan `src/` only, and `lint-prose.py` and
`check-glossary.py` drop `archive/` paths from their file lists, so neither
`make check` nor the pre-commit hook inspects the archive; `reuse lint` still
covers it through the `archive/**` carve-out in `REUSE.toml`. The rules are
stated in full in `archive/README.md`; the registry is `dev/ARCHIVE.md`.

## Pre-commit hook

`git-hooks/pre-commit` runs fast source checks on staged Markdown (the prose linter, marker
integrity, the glossary check, and the Agda code linter) and blocks the commit on any
violation. Version-controlled; activate it once per clone (or run `make hooks`):

```sh
git config --local core.hooksPath scripts/git-hooks
```

## `gen-depmap.py`

Generates the per-language dependency-map page (`depmap.html`, linked from the
site sidebar), fully derived: nodes and edges from the masters' `import` lines,
reading order and per-module descriptions from the `Everything` reading catalog,
lanes from the namespace tree, columns from longest-path dependency depth. The
page shell is `depmap-template.html` (self-contained inline CSS/JS; follows the
site's stored theme). Runs as part of `make site`.

```sh
python3 scripts/gen-depmap.py --src src --out _build/site --langs en,zh
```

## `check-ratio.py`

DD24's bar: cold build seconds over in-fence lines, for the internalization GCH wing, matched
against the delivered AC wing's measured **0.007614 s/line** (133.19 s over 17,492 lines). It
is the ONLY threshold on that wing: no line cap and no seconds cap, because the wing exists to
MEASURE what a GCH wing costs and a cap would make the measurement report the cap.

**A ratio is the right single bar** because a total can be met by writing less of a worse
thing and a ratio cannot. `dev/LESSONS.md` P-m measured a twentyfold spread between content
classes and P-t a twentyeightfold spread inside one file; no line count sees either.

**It measures COLD by default** (`--warm` is opt-in and labels itself NOT COMPARABLE), because
the baseline is cold and a warm run against it is not looser but wrong. **It is NOT in
`make check`**: it runs Agda, which the commit gate forbids, and it fails closed beside a live
`agda`. It is an on-demand measurement, like `deletion-test.py`. It refuses to invent a
baseline (P-l), and it EXCLUDES an unmeasurable module from the aggregate rather than
counting it as zero.

Staged: it reports from the first GCH module onward and exits 0 while `ratio.gch_wing` is
empty, which is the state until `[LJ-1.3]`.

```sh
make ratio                                  # the declared wing, cold
python3 scripts/check-ratio.py --module src/L/Foo.lagda.md   # one master
```

## Retired: `dashboard.py`, `check-dashboard.py`, `test_dashboard.py`

The generated dashboard was ABOLISHED by the owner on 2026-08-09. The three
scripts are frozen in `archive/tooling/`, and
[archive/tooling/README.md](../archive/tooling/README.md) records what they
did right and the one thing they got wrong. Standing figures now come from
`python3 scripts/ledger.py --brief`, which was always their source.
