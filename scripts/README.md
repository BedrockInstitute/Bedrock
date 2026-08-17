# scripts

Repository tooling. English-only: this is developer documentation. User-facing docs
(`docs/<lang>/`) are trilingual; developer docs are English. Developer docs include `dev/`,
the root `AGENTS.md` and `CONTRIBUTING.md`, the per-directory `README.md` files such as this
one, and anything else written for contributors. See [AGENTS.md](../AGENTS.md) for the full
rulebook and the user/developer doc split. The marker grammar these tools share is specified in
[dev/STYLE-i18n.md](../dev/STYLE-i18n.md).

## The layout (LJ-1.295, owner's option C, 2026-08-15)

Every script lives in a group directory named by WHEN it runs and WHO runs it, because the
same topic can span a gate and a build step (`weave-i18n.py --check` is in `make check`;
`weave-i18n.py --gen` builds the site):

| directory | holds | members |
|---|---|---|
| `scripts/` (flat) | the modules scripts IMPORT BY NAME across groups | `agents_tree.py`, `repo_root.py` |
| `scripts/gate/` | runs inside `make check` or a git hook; a red one stops a commit | `check-agents-guard.py`, `check-archive-cited.py`, `check-baseline-home.py`, `check-build-manifest.py`, `check-dd18-survey.py`, `check-dd25-review-named.py`, `check-dd4-stated.py`, `check-dev-docs.py`, `check-fences.py`, `check-glossary.py`, `check-live-record-claims.py`, `check-live-territory.py`, `check-premises-stated.py`, `check-probes.py`, `check-rule-ids.py`, `check-task-index.py`, `check-tree.py`, `lint-agda.py`, `lint-prose.py` |
| `scripts/dispatch/` | everything about running and auditing a dispatch | `check-dispatch-policy.py`, `check-sources-read.py`, `dd25-record.py`, `dispatch_policy.py`, `recall-hook.py`, `rules.py` |
| `scripts/measure/` | costs seconds to minutes, runs Agda, or reports a number; never a gate | `check-ratio.py`, `check-timing.py`, `check-unbound-hyp.py`, `deletion-test.py`, `dispatch-usage.py`, `ledger.py`, `obligations.py` |
| `scripts/site/` | the publishing pipeline and the deploy | `extract-types.py`, `gen-depmap.py`, `i18n_markers.py`, `link-check.py`, `render-site.py`, `weave-i18n.py`, `depmap-template.html` |
| `scripts/ops/` | machine safety | `agda-watchdog.sh` |

Unchanged in place: this `README.md`, `scripts/tests/`, `scripts/git-hooks/`.

### THE ONE PLACEMENT RULE for an imported module

**A module that another script imports lives in the shallowest directory that contains
every importer.** No judgement call is needed:

| module | importers | lands in |
|---|---|---|
| `repo_root.py` | scripts in `gate/`, `dispatch/` and `measure/` | `scripts/` (flat) |
| `agents_tree.py` | `check-dev-docs.py`, `check-rule-ids.py`, `check-task-index.py`, `check-premises-stated.py`, `check-dd4-stated.py` (all `gate/`), `check-dispatch-policy.py`, `check-sources-read.py` (`dispatch/`) | `scripts/` (flat) |
| `i18n_markers.py` | `weave-i18n.py`, `gen-depmap.py`, `render-site.py` (all `site/`) | `site/` |
| `ledger.py` | `check-ratio.py`, `deletion-test.py` (both `measure/`) | `measure/` |
| `dispatch_policy.py` | `check-dispatch-policy.py` (`dispatch/`) | `dispatch/` |
| `lint-prose.py` | `check-glossary.py` (`gate/`, loaded by path) | `gate/` |
| `check-rule-ids.py` | `check-dev-docs.py` (`gate/`, loaded by path) | `gate/` |
| `check-timing.py` | `check-ratio.py` (`measure/`, loaded by path) | `measure/` |
| `obligations.py` | `check-timing.py` (`measure/`, loaded by path) | `measure/` |

`repo_root.py` and `agents_tree.py` are flat BY THIS RULE, not by exception: no shallower
directory contains all their importers than `scripts/` itself. A consumer outside this
repository is not an importer for placement; the one such consumer
(`.claude/skills/codex-dispatch/dispatch.py`) was re-pointed by its owner when
`dispatch_policy.py` moved.

### The breakage this move accepted

Briefs and reports written before LJ-1.295 cite the flat layout: they name
`scripts/foo.py` where this tree holds `scripts/<group>/foo.py`. The BASENAME of nothing
changed. The owner ruled on 2026-08-15 to accept those dangling reader pointers (option C):
no shim runs the old path and no resolver maps it, so a reader who meets `scripts/foo.py`
in an older brief or report should look for `foo.py` under the subdirectories in the table
above. Frozen records under `agents/`, `dev/JOURNAL.md` and `dev/memos/` are never
rewritten, so their flat citations are correct as history.

### What enforces the layout (C-48)

The GROUP a new script belongs to is a review decision with no mechanical check; this
README's table is its home, and a script that lands outside its group is caught only by
reading. Two parts ARE mechanical, in `scripts/tests/test_scripts_layout.py`: the set of
directories under `scripts/` is pinned (no `misc/` bucket can appear silently, C-43), the
flat `.py` set is pinned to the two cross-group modules (a new flat script must either
have importers across groups or join one), and every script outside `tests/` and
`git-hooks/` must appear in this README by its full `scripts/<group>/<name>` path.

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

## gate/

### `lint-prose.py`

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
python3 scripts/gate/lint-prose.py --check          # scan tracked files; exit 1 on any violation
python3 scripts/gate/lint-prose.py --fix <files>    # auto-fix punctuation/quotes (dashes/nesting are manual)
python3 scripts/gate/lint-prose.py --check --staged # only staged files (used by the hook)
```

### `check-glossary.py`

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
python3 scripts/gate/check-glossary.py --check          # scan tracked files; exit 1 on any violation
python3 scripts/gate/check-glossary.py --check --staged # only staged files (used by the hook)
```

### `check-probes.py`

The never-commit gate. **One rule with one exemption**: a probe must not enter the repository
under `src/`, and `agents/tasks/` is where it belongs instead. Generated files (anything
under `_build/`, the woven mono-lingual copies, any `.agdai`) are never committed at all.
`dev/LESSONS.md` **D-1** is the canonical rule and this checker only enforces it.

`.gitignore` covers `src/`, which is exactly why this exists: **an ignore rule is a default,
not a gate.** `git add -f` walks past it and a pattern that stops matching a new naming shape
fails silently. On 2026-08-04 one `git add -A src/` committed 13 probe files, 3,274 lines.
`--staged` runs in the pre-commit hook and stops the commit; `--check` runs in `make check`
over every tracked file and catches anything that got in historically or past a bypass.

**`--staged` reads `--diff-filter=ACMR`, and the `R` is load-bearing.** MEASURED 2026-08-13 at
`[LJ-1.141]`: 257 staged probe renames, and `ACM` reported zero of them. A probe is tracked
now, so it can be `git mv`-ed straight into `src/`, and the old filter would have passed it.

**THE LIFECYCLE IS RETIRED**, by the owner's ruling of 2026-08-13. A probe pairs one-to-one
with its report, lives in `agents/tasks/<TASK>/`, is tracked, and is never deleted, so there
is nothing to sweep and no verdict to compute. `--gate`, `--stale`, `--sweep`, `--index`, the
live-task trigger and the 24 hour deletion floor are gone; the frozen code is
`archive/scripts/check-probes-lifecycle.py` with its suite. Every retired flag now exits 2.

```sh
python3 scripts/gate/check-probes.py --check   # every tracked file (make check, make probes)
python3 scripts/gate/check-probes.py --staged  # staged files only (pre-commit hook)
```

### `check-tree.py`

Whole-tree invariants that the per-file linters structurally cannot see, because they read one
file at a time.

The one that matters most is **closure** (`dev/PLAN.md` section 7 rule 3): every master under
`src/` must appear in `src/Everything.lagda.md`'s import list. `make check` typechecks exactly
one file, which is what makes it a trusted single invocation, and the price is that **a master
nobody imports is never typechecked while the gate still goes green**. PLAN specified this
audit from the beginning and nothing had implemented it; on its first run it found a real
in-progress chapter sitting outside the gate. The others: **archive** (no live master imports a
module that lives only in `archive/`, archived D20, live home DD13), **shared-cjk** (no CJK in
marker-free prose, which would reach the English book verbatim, C-8), **spdx** (licensing has
one source of truth, archived D4, live home DD22),
**retiring**, WARN only and SILENT today (it flagged a surviving master importing a chapter
the retired route's archived D18 was retiring; `retire_suspended` empties that set, so the check returns
nothing until the new route rules its own retirements), and **module-body**, WARN only (C-11's
silently empty parameterized module).

Its docstring also records what was deliberately NOT made a check and why, since three
proposals were rejected on false-positive grounds: a rule already enforced by Agda itself, a
rule whose only hit is in code booked for retirement, and a rule whose predicate cannot tell a
goal's status from a sub-item's.

It also carries the **gate-debt** counter. A full `agda src/Everything.lagda.md` costs not its
twelve background minutes but the **quiet tree** it needs for all of them: no agent may write a
master while it runs, so every full gate costs one dispatch window. Full gates are therefore
batched (`archive/dev/DECISIONS-archived.md`, archived D28), and this reports whether one is due.

```sh
python3 scripts/gate/check-tree.py --check            # every invariant (make check and the hook)
python3 scripts/gate/check-tree.py --check closure    # just one
python3 scripts/gate/check-tree.py --gate-debt        # commits and added lines since the last gate
python3 scripts/gate/check-tree.py --gate-passed      # record HEAD after a green full gate
```

### `check-dev-docs.py`

The maintenance mechanism for the dev/ documents, built by `[L3.32-T110]`
after a day in which every decay instance below was found by accident and
none by a gate. The cadence, the thresholds with their arguments, and what
is deliberately not automated are recorded in
this script's own docstring, which is its operative home.

The gate half (`make check`'s `devdocs` target) is six cheap pure-Python
checks: a word cap on AGENTS.md (2,200), a word cap on every dev/PLAN.md
table cell (1,600), a requirement that a LESSONS entry marked "imported
from/into" be routed in dev/rules.toml, a check that PLAN section 0's "as of"
date is no older than the newest date in its own body, a form check on
dev/memos/ `**STATUS:` headers, and a check that every `scripts/*.py` named
in AGENTS.md exists (subdirectory paths count; the regex accepts them).

The sweep half is informational and exits 0: it lists LESSONS entries that
are unrouted AND cited nowhere (the "landed and nobody noticed" class), and
section 11 cells over the 600-word episode-scale line (episode content
belongs in dev/JOURNAL.md).

```sh
python3 scripts/gate/check-dev-docs.py            # run every gate subcheck
python3 scripts/gate/check-dev-docs.py --check NAME  # run one
python3 scripts/gate/check-dev-docs.py --sweep    # on-demand informational sweep
```

### `check-agents-guard.py`

The AGENTS.md guard (ruling D34, owner-approved 2026-08-07). AGENTS.md loads
into every agent session, so a wrong sentence there governs all work
silently; the one-process incident (see the script's docstring) is why this
exists. A commit that edits AGENTS.md must carry the owner's dated approval
trailer, `AGENTS-diff-approved: YYYY-MM-DD`, written only after the owner
ruled on the presented diff.

Two modes: with no arguments (the `agentsguard` target in `make check`) it
audits history, judging only commits whose own tree contains the guard at
any home it has ever had (the flat home before LJ-1.295, `scripts/gate/`
after); with `--msg-file` (the `commit-msg` hook) it refuses a trailerless
commit that stages the file.

```sh
python3 scripts/gate/check-agents-guard.py                 # history audit
python3 scripts/gate/check-agents-guard.py --msg-file MSG  # commit-msg hook mode
```

### `lint-agda.py`

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
python3 scripts/gate/lint-agda.py --check           # scan tracked src masters; exit 1 on any violation
python3 scripts/gate/lint-agda.py <files>           # specific masters (used by the hook)
```

### `check-rule-ids.py`

Runs in `make check`. Every `[LJ-x.y]`, `DD<n>` and LESSONS id cited anywhere
under `dev/` must resolve to a real entry, and a struck decision still
resolves against the archive. It exists because a document written ABOUT rule
hygiene shipped a fake id.

**THE SERIES CHECK, added 2026-08-13 by `[LJ-1.140]`.** Resolving is not enough
while two series share the numbers. The `D` series was archived on 2026-08-09
and the live series is `DD`, so a bare code resolves against the archive and
points the reader at the `DD` row of the same number, which is a different
rule. Archived D7 is naming hygiene; DD7 is REVOKED, so two lines of
`dev/STYLE-agda.md` told every agent that a live naming rule was dead. The
check has two parts. **A bare `D<n>` in a live document is a defect when a
`DD<n>` row exists**: the home goes beside the code, as `archived D7` or
`struck D8`, and the marker may sit at the end of the previous line, so a
reflow costs nothing. **A `D<n>` sent to `dev/PLAN.md` section 3 is a defect
whatever else the line says**, because that section holds the `DD` table and no
`D` row. The scope is wider than the citation check: `dev/LESSONS.md`, which
binds new code, and every `.py` under `scripts/`, which agents read before
they edit a checker. `scripts/tests/` is excluded because its fixtures reproduce document
text verbatim. Pinned by `scripts/tests/test_rule_series.py`, 63 checks.

**WHAT THE SERIES CHECK CANNOT DO, and the limit is real.** It reads the word
beside the code, never the sentence, so **it cannot tell which series an author
MEANT.** A citation labelled `archived D5` that argues DD5's content passes
green. It removes the SILENT retarget, where nothing beside the code warns
the reader at all, and claims nothing beyond that. Three exemptions let real text
through and each is deliberate. `dev/JOURNAL.md`, `dev/memos/` and `agents/`
are dated records, so a July entry citing an August-struck code is correct as
history and nobody rewrites it. **A file may declare its whole series ONCE**,
in a fixed `**D-SERIES NOTE.**` sentence that a reader sees, which is what
keeps `dev/ARCHIVE.md`'s 70 dated retirement rows from saying one thing seventy
times; **nothing checks that the declaration is true of every row below it.**
The locator rule **skips a line that names a `DD` code**, because the repaired
sentences read "archived D11; DD11 in section 3 is a DIFFERENT rule", so a line
that cites one code correctly and misdirects a second one passes.

### `check-task-index.py`

Runs in `make check`. Every cited task code has exactly one row in PLAN
section 11, and no row exceeds 200 characters. The cap stops a verdict
paragraph sneaking back into a row. **Widened 2026-08-10** to see lettered
codes: `LJ-\d+\.\d+` matched none of `LJ-0.4a` to `LJ-0.4q`, so fifteen rows
were invisible and twelve of them were over the cap, one at 438 characters.

### `check-archive-cited.py`

**A brief's ARCHIVE section must cite an ARCHIVE, not only the new route's own
tasks.** `AGENTS.md` requires the section and its enforcement is REVIEW ONLY.

**`[LJ-1.157]` measured what that costs, and the shape is not carelessness.**
164 of 164 briefs carried the heading. **The content decayed while the form
survived**: after `[LJ-1.94]` only process tasks cited a retired-route file, and
the section's meaning drifted to "the new route's own prior tasks". That is
`dev/LESSONS.md` C-41 one level down, a rule still reading true after its world
changed.

**The bill, measured:** `[LJ-1.107]` rebuilt 82 delivered lines of
Cantor-Schroeder-Bernstein; three tasks priced `levelIn` without an 845-line
comparable that the route's OWN recon had marked ADAPTABLE; and the archived
`CSB` was surfaced twice in the route's own record and lost both times.

**What it checks:** a live brief has an ARCHIVE section, and that section cites
a path under `archive/` or `agents/tasks/archive/`.

**What it cannot do**, and this is why it is `make archivecited` and NOT part
of `make check`:

- It cannot tell whether the cited archive BEARS on the task. A brief citing an
  irrelevant archive file passes.
- It cannot tell a process task, which may legitimately have nothing archived,
  from a mathematical one that does.
- It reads the brief and never the return.

**So it REPORTS and never gates**, for the reason `check-build-manifest.py`
does not gate either: **a red gate here buys a pasted citation rather than a
survey.** Its whole claim is that the drift is VISIBLE, which is the thing that
was missing.

### `check-dd4-stated.py`, `check-dd25-review-named.py`, `check-premises-stated.py`, `check-build-manifest.py`, `check-fences.py`, `check-live-territory.py`, `check-dd18-survey.py`, `check-baseline-home.py`, `check-live-record-claims.py`

The remaining gates. Each one's operative documentation is its own docstring,
which carries the ruling, the epoch and the measured defect it exists to stop:
`check-dd4-stated.py` (every brief states DD4), `check-dd25-review-named.py`
(a negative return's index row names its review's code),
`check-premises-stated.py` (a brief with a trigger token declares its
premises), `check-build-manifest.py` (`_build/` entries are declared in
`dev/build-manifest.toml`), `check-fences.py` (Agda outside a fence is
invisible to Agda and to the ledger, so a green tree proves nothing about it),
and `check-live-territory.py` (the commit gate against a live agent's write
territory; `--staged` in the hook, `--check` the tracked-tree audit).

**Three landed on 2026-08-16 and each carries an epoch**, so read the epoch
before reading a frozen count as compliance: `check-dd18-survey.py` (DD18's
return side, where an ARCHIVE USED section must quote one line per archived
file at the line it cites), `check-baseline-home.py` (DD24's figures live in
`dev/ledger.toml` and a live claim names the field), and
`check-live-record-claims.py` (a brief that names a goal answers the
open-work list).

**They were absent from this index until 2026-08-16, and
`scripts/tests/test_scripts_layout.py` was RED from the moment they landed.**
Nothing reported it, because `make test` is not part of `make check`.

## dispatch/

### `rules.py`

**The first command AGENTS.md gives an agent**, and until 2026-08-10 it was
absent from this index. It prints the MANDATORY laws for a task kind out of
`dev/LESSONS.md`, routed by `dev/rules.toml`, so a brief cites the routing
rather than the corpus. `--grep <term>` resolves the long tail by trigger
word.

It exists because memory drifted: sixteen laws entered the corpus over two
days and were cited in 10 briefs out of 112. **Never pick rules from memory.**
The kind is DERIVED from the brief's write scope, never self-declared, because
an author who picks the kind picks the bundle.

```sh
python3 scripts/dispatch/rules.py --for build     # build, probe, recon, rewrite, review
python3 scripts/dispatch/rules.py --grep seal     # the long tail, by trigger word
```

### `dispatch_policy.py` and `check-dispatch-policy.py`

`dispatch_policy.py` is **the one home of DD17's dispatch policy**: a hardcoded
`VERSION_IN_FORCE` switch, the two versions of the head table, the date the
current version was set, its reason and its revert condition. Edit that one
line to change the policy. **Inspect it with `python3
scripts/dispatch/dispatch_policy.py`**, which prints the version in force with its whole
table, so nobody reads code to answer "which head runs this task".

`check-dispatch-policy.py` runs in `make check` and holds no policy of its own:
it imports the switch and derives every expectation from it. It enforces five
things. The switch names a version the module defines. No governed document
under `dev/`, plus `AGENTS.md` and this file, restates the head table. Every
brief carries a legal `tier:` token. A brief written after the policy epoch
names the version it was chosen under. An adversarial review carries the
critic's head and not the author's.

**WHAT NEITHER TOOL CAN DO, and the list is the point.** **The switch cannot
force the orchestrator's choice.** An in-harness Opus dispatch never passes
through `.claude/skills/codex-dispatch/dispatch.py`, so no value here can start
it, stop it or redirect it. A brief that says `tier: pi` and was run on Opus 5
passes green. What the switch DOES drive is the dispatcher's default harness,
what the checker accepts, and what the inspection command prints, which makes a
wrong head **detectable by an audit** and nothing more. The checker also cannot
date a brief reliably, because `_build/` is never committed and mtime is all
there is; and it cannot tell an adversarial review from a brief that discusses
one, because it reads the GOAL section and the tier line for one word.

**The epoch exists so the gate can be green on its first run.** The
version-naming and adversarial checks bind only briefs written on or after
2026-08-13 11:00, which is `check-agents-guard.py`'s self-anchoring pattern. A
pre-epoch defect is printed as a note by `--notes` and never fails the gate.
Measured at the landing: 406 briefs read, 4 notes, 0 failures.

### `check-sources-read.py`

**An audit aid, not a gate; exit 0 always.** DD18 makes a brief name what in
`archive/` and `dev/literature/` may bear on the task, and `dispatch.py`
refuses a brief that omits either section. The RETURN half is review-only, and
that gap cost a day on 2026-08-10: `[LJ-1.6]` filed a filled ARCHIVE USED
section while the cure it needed sat unread in the archive file its own brief
named.

This diffs the sources a brief NAMED against the paths the agent actually
OPENED in a tool call, using the session log the dispatcher already keeps. It
separates three things a naive grep conflates: the brief's text, the report's
text, and a real read.

**It proves a path was opened, never that the right part was read.** It would
have passed `[LJ-1.6]`. A miss is a signal for the adversarial reviewer:
`dev/ORCHESTRATION.md` routes one today, and `dev/POD.md` section 6.6 does at the
cutover.

```sh
python3 scripts/dispatch/check-sources-read.py LJ-1.6      # one or more task codes
python3 scripts/dispatch/check-sources-read.py --all
```

### `recall-hook.py`

**The only enforcement point in this repository that fires while the brief is
still being written.** Every other one fires at the commit or is the
orchestrator's own intention. `dev/LESSONS.md` **C-59** names the disease: an
enforcement point exists, and nothing carries its verdict to a decision.
`[LJ-1.376]` measured the dominant detour class as the orchestrator's own live
record unread, and `[LJ-1.377]`'s report says its gate cannot reach the moment
that would have prevented it.

It is a Claude Code hook, which is the one UNCONDITIONAL trigger in this
toolchain. It adds no store, no index, no daemon, no port and no dependency: it
re-runs `check-live-record-claims.py`, `check-premises-stated.py` and
`check-dispatch-policy.py`, which are already in `make check`, and prints what
they say.

**It never blocks and never fails a turn; it always exits 0.** It fires on a
brief write and on a task-shaped subagent dispatch, and is silent otherwise,
because `[LJ-1.377]` measured two wider designs at 274 firings out of 274
briefs and killed both: a gate that fires on everything trains pasting.

**The wiring is owner-private and the script is tracked.** That split answers
the defect `dev/memos/L3.32-context-layering.md` section 5 named against the
last routing proposal, whose enforcement point sat in `.claude/`. Delete
`.claude/settings.json` to turn the mechanism off.

**The session card is an INDEX and never a summary**, and that distinction is
what the owner's 2026-08-09 abolition of the dashboard bought. It states no
claim of its own: a blocked row gets its code, its line and its character
count, and the reader opens it. MEASURED at the design: the three blocked rows
are 1,155, 806 and 527 characters, and a 150-character cut keeps 13, 19 and 28
percent of them, dropping the qualifier at the end of a clause first, which is
the failure `dev/JOURNAL.md`:938-959 records. An open-work headline IS printed,
whole, because the author wrote it as a headline; where it wraps across source
lines it is REASSEMBLED, which is unwrapping and not cutting. Ruled by the
owner on 2026-08-16. It costs about 1,990 characters and 1.0 s per session, and
it does not fire for a subagent.

```sh
python3 scripts/dispatch/recall-hook.py --print-settings   # the .claude/settings.json to place
python3 scripts/dispatch/recall-hook.py --log             # what it has fired on so far
```

The log is one JSON line per firing, beside the dispatch registry rather than
under `_build/`, which `make clean` empties. It exists so that this tool's own
value becomes a measurement: count how many firings were followed by an edit to
the same brief before its dispatch.

### `dd25-record.py`

Writes a DD25 negative's row into `dev/PLAN.md` section 11 in the structured
form the gate reads, so a negative return lands as data rather than prose. Its
usage block is its operative documentation.

## measure/

### `ledger.py`

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
python3 scripts/measure/ledger.py           # the full ledger
python3 scripts/measure/ledger.py --brief   # one line: standing, endpoint, overage
python3 scripts/measure/ledger.py --check   # validate the declaration; exit 1 on a defect
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
python3 scripts/measure/ledger.py --reuse
```

### `check-ratio.py`

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
python3 scripts/measure/check-ratio.py --module src/L/Foo.lagda.md   # one master
```

### `check-timing.py`

The repository's ONLY module timer, and it stays that way; a second
implementation drifts (C-26). It moves a module's own interface aside, times
the check, and puts it back. **The caliber is a parameter:** the default is a
bare `-M8g`, which is what the ledger's `[[hot]]` rows were measured at, and a
caller comparing against a different baseline passes its own. Suspended as a
gate by DD5; it reports.

### `deletion-test.py`

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

The shadow mode is the daily proxy. It reuses `ledger.py`'s trophy
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
python3 scripts/measure/deletion-test.py                # shadow: count, cap, headroom
python3 scripts/measure/deletion-test.py --files        # shadow, with the AC-side file set
python3 scripts/measure/deletion-test.py --run --yes    # the real test (guarded)
```

### `obligations.py`

Not a gate. It counts a module's proof obligations, which is the denominator
of the per-obligation rates `dev/ARCHIVE.md` records, so every consumer calls
this one counter (a second implementation drifts, C-26).

```sh
python3 scripts/measure/obligations.py --by-tree
python3 scripts/measure/obligations.py src/L/Rud/Bridge.lagda.md
```

### `dispatch-usage.py`

**Tokens per dispatch, joined from the agent's own session file.** The cost
model of 2026-08-16 priced a dispatch at about 1,757 words of orchestrator
prose and about 35 delivered Agda lines, and then named the one input a cost
decision needs and could not supply: the registry record carries no usage
field, and `dev/vendors.toml` holds price BANDS that nothing joins to a task
code. This supplies the missing half.

**It does not touch `dispatch.py`**, and that is a decision rather than
caution. The data already exists in each agent's session file; `dispatch.py` is
untracked and no gate reads it; and above all a field written at launch could
only price dispatches from today forward, while this reads the history.
MEASURED at the landing: **278 of 467 registry records priced, 59.5 percent**,
237 joined by the record's `session` field and 41 by the pi session path the
herdr log announces in its opening event.

**THE TWO STORES HAVE OPPOSITE SEMANTICS AND BOTH WERE MEASURED, not read off a
document.** codex writes a CUMULATIVE `total_token_usage`, measured strictly
monotonic over 791 events rising to 391,252,172, so the LAST event is the run;
summing them returns 347 times the truth. pi writes PER-TURN `usage`, measured
not monotonic, so they are SUMMED; taking the last returns 121 times low.
**The two also disagree about caching**: codex's `cached` is a SUBSET of
`input`, pi's `cacheRead` is DISJOINT from it, and reading them alike made the
aggregate `input - cached` come out negative at minus 245,596,874. That is how
it was caught.

**READ THE FRESH PAIR, NOT THE PROCESSED FIGURE.** Measured over the priced
set: 9,656,291 tokens processed per dispatch at the median, of which **98.8
percent are cache reads**. The pair a cost question needs is fresh input
120,686 and output 96,085 per dispatch, both medians.

**No cost figure.** `dev/vendors.toml` names price bands and carries no
per-token rate, so money is not derivable here and none is invented (DD8).

```sh
python3 scripts/measure/dispatch-usage.py --summary
python3 scripts/measure/dispatch-usage.py --task LJ-1.377
python3 scripts/measure/dispatch-usage.py --json
```

### `check-unbound-hyp.py`

**ADVISORY, and deliberately NOT in `make check`.** It finds telescope
hypotheses that are refutable by regularity: the shape that cost phase LJ-1
about a thousand delivered lines across seven statement-level defects. A
flag is a QUESTION, never a verdict, so it must not fail a build; the cure
is a refutation probe, and `agents/tasks/LJ-1-97/ProbeLJ197A.agda` is that probe's shape at
one line of real content per fact.

Three rules. Rule 1: the conclusion asserts `⟨ A ∈ B ⟩` and a set-typed
variable free in `A` appears in no premise. Rule 2: a membership premise's
object is built only from variables this telescope binds, none of which
reaches the conclusion, so the premise is satisfiable at a set the author
never intended. Rule 3: a set-typed telescope with no premise at all.

**Measured recall, 2026-08-13.** On `src/L/Condensation/TwelveAgree.lagda.md`
before its repair it flags **all eleven** hypotheses that `[LJ-1.95]` and
`[LJ-1.97]` machine-refuted, plus `valK` and `valK-un`, which `[LJ-1.97]`
found to be the same shape and could not refute at the abstract frame. It
does NOT flag the sound conditionals in the same file: `carrierK`,
`arityK`, `pairK`, `innerK` and the `tagEq`/`numK` families.

Two precision rules earn that. Only SET-typed binders count, because
regularity refutes a membership claim about a set and not about an index at
`ℕ`; that alone removed the `innerK` false positive. And
`lookup (suc^n zero) (v0 ∷ … ∷ γ)` is resolved to `vn` before free variables
are read, because otherwise a repaired hypothesis reads as unconstrained:
`succK` after its tie carries the premise `ar ∈ K` and concludes about a
lookup that names six other variables it never uses.

Run it on a frame before you fund a build against it. See `dev/LESSONS.md`
C-38.

## site/

### `i18n_markers.py`

The single canonical implementation of the marker grammar (parse / weave / validate),
imported by `weave-i18n.py`, `gen-depmap.py` and `render-site.py` so the grammar can never
drift. Not a CLI.

### `weave-i18n.py`

Weaves masters into per-language mono-lingual `.lagda.md` (kept on demand for
`agda --html` compatibility, never committed), and validates marker integrity.

```sh
python3 scripts/site/weave-i18n.py --check                 # validate markers (exit 1 on error)
python3 scripts/site/weave-i18n.py --lang zh FILE          # weave one master -> stdout
python3 scripts/site/weave-i18n.py --gen --out _build/woven  # weave all -> _build/woven/<lang>/
```

`--gen` also drops a per-language `bedrock.agda-lib` so each woven tree type-checks and
`agda --html`-es on its own (consume it outside the source project to avoid include-path
clashes with the root `bedrock.agda-lib`).

### `extract-types.py`

Extracts per-module identifier types for type-on-hover and typed search, on stock Agda
2.8.0, by driving Agda's batch interaction protocol (`agda --interaction-json`,
`Cmd_show_module_contents_toplevel`). No Haskell, no Agda-as-a-library.

```sh
python3 scripts/site/extract-types.py --out _build/types.json
```

### `render-site.py`

Builds the hyperlinked multilingual static site from the masters: runs `agda --html`,
weaves prose per language, splices the (language-neutral) highlighted code, resolves inline
`` `name`{.Agda} `` references, renders math (KaTeX) and Markdown, rewrites links, emits the
per-module `types/<Module>.json` (for hover) and per-language `search.json`, and wraps each
page in the vendored 1lab-styled template.

```sh
python3 scripts/site/render-site.py --out _build/site [--langs en,zh] [--base-url /Bedrock]
```

See the root `Makefile` (`make site`, `make serve`) for the orchestrated build.

### `gen-depmap.py`

Generates the per-language dependency-map page (`depmap.html`, linked from the
site sidebar), fully derived: nodes and edges from the masters' `import` lines,
reading order and per-module descriptions from the `Everything` reading catalog,
lanes from the namespace tree, columns from longest-path dependency depth. The
page shell is `depmap-template.html` (self-contained inline CSS/JS; follows the
site's stored theme), read from this script's own directory. Runs as part of
`make site`.

```sh
python3 scripts/site/gen-depmap.py --src src --out _build/site --langs en,zh
```

### `link-check.py`

Checks the built site's internal links. It is the ONLY script the deploy runs
(`.github/workflows/cloudflare.yml` and `pages.yml`, both on merge to `main`),
which is why its path is edited in both workflows in any move, in the same
commit.

```sh
python3 scripts/site/link-check.py _build/site
```

## ops/

### `agda-watchdog.sh`

Kills runaway `agda` before it OOMs the machine (born 2026-08-02 after four
unguarded parallel writers crashed the 64 GB box; the primary guard is the
`GHCRTS` heap cap, this is the backstop). It finds the repository root by
walking up to `.git`, never by counting directories, so its log always lands
in the true `_build/tools/` whatever directory it runs from.

## The flat modules

### `repo_root.py`

**Not a checker. The one way a script finds the repository root.** Written by
`[LJ-1.291]` after `[LJ-1.290]` measured the failure the old depth anchors buy: 24 scripts
computed the root as `Path(__file__).resolve().parent.parent`, so a gate copied or moved
one level deeper guarded the wrong tree and still said `clean` (55 tracked files read as
2,369, both exit 0). `find_root(__file__)` walks up from the caller to the nearest `.git`
and REFUSES loudly when no marker is above, so a relocated or exported script can never
silently guard a guessed tree. Its docstring carries the two stamped anchor shapes: the
two-line anchor for a flat script, and the group-directory walk (up to `repo_root.py`
itself) for a script inside `gate/`, `dispatch/`, `measure/` or `site/`.

### `agents_tree.py`

**Not a checker. The one place that knows the shape of `agents/tasks/`.** NINE
scripts read the tree through it, MEASURED 2026-08-17 by import: in `dispatch/`,
`check-dispatch-policy.py` and `check-sources-read.py`; in `gate/`,
`check-dd18-survey.py`, `check-dd4-stated.py`, `check-dev-docs.py`,
`check-live-record-claims.py`, `check-premises-stated.py`, `check-rule-ids.py`
and `check-task-index.py`. This paragraph said FIVE until that count was taken.

Until 2026-08-13 a brief was a file in `agents/briefs/` and a report was a file
in `agents/reports/`, so the DIRECTORY carried the distinction and each importer
wrote the path by hand. `[LJ-1.142]` merged the trees into one directory per
task, which deleted that signal. This module carries the replacement.

**It offers two brief predicates and the choice matters.** `briefs()` reads the
content and is exact: MEASURED 415 of 415 briefs found, 0 reports misread.
`candidate_briefs()` reads the name and is wider: 415 found, 27 archived reports
misread. **A checker that hunts a MISSING `tier:` line must take the second**,
because the first finds a brief partly by that line and would never see the
defect. The docstring states this with its measurements.

`scripts/tests/test_agents_tree.py` pins the layout, the census floors and the
Agda-safe directory name, which nothing else enforces.

## tests/

`scripts/tests/` holds the suites `make test` runs, one per checker or module,
each loading its target by path from this tree. Two suites police the layout
itself: `test_archive_layout.py` derives the legal top-level `archive/`
directories from the repository root, and `test_scripts_layout.py` pins the
group directories, the flat module set and this README's coverage of every
script (see [What enforces the layout](#what-enforces-the-layout-c48)).

### `tests/test_archive_layout.py`

**Not a checker, and nothing else notices what it notices.** The owner ruled on
2026-08-13 that `archive/` MIRRORS the repository root: something archived from
`dev/measurements/` goes to `archive/dev/measurements/`, and something archived
from `scripts/` goes to `archive/scripts/`. This suite derives the legal set of
top-level archive directories from the root itself, so it needs no hand-written
list, and it refuses any other name unless the name is a declared exception with
a reason. It also pins the archival-event directories under `archive/src/` to the
`<date>-<slug>` shape, which is what makes a directory name say WHICH archival it
was rather than merely what the files are.

**The archive is outside every gate by construction**, which is what makes it
free to keep and also what makes a layout defect invisible there. Three
directories drifted in eight days before anyone measured it. `[LJ-1.143]` moved
them and wrote this suite so the next one fails a test instead of accumulating.

## The archive

Archived modules live in `archive/` at the repository root, outside `src/`, so
every gate is structurally blind to them (archived D20, in
`archive/dev/DECISIONS-archived.md`; the live home is DD13 in `dev/PLAN.md` section 3).
`lint-agda.py` and `weave-i18n.py` scan `src/` only, and `lint-prose.py` and
`check-glossary.py` drop `archive/` paths from their file lists, so neither
`make check` nor the pre-commit hook inspects the archive; `reuse lint` still
covers it through the `archive/**` carve-out in `REUSE.toml`. The rules are
stated in full in `archive/README.md`; the registry is `dev/ARCHIVE.md`.

## Pre-commit hook

`git-hooks/pre-commit` runs fast source checks on staged Markdown (the prose linter, marker
integrity, the glossary check, and the Agda code linter) and blocks the commit on any
violation. `git-hooks/commit-msg` runs the AGENTS.md guard on the message. Both are
version-controlled; activate them once per clone (or run `make hooks`):

```sh
git config --local core.hooksPath scripts/git-hooks
```

## Retired: `dashboard.py`, `check-dashboard.py`, `test_dashboard.py`

The generated dashboard was ABOLISHED by the owner on 2026-08-09. The three
scripts are frozen in `archive/scripts/`, and
[archive/scripts/README.md](../archive/scripts/README.md) records what they
did right and the one thing they got wrong. Standing figures now come from
`python3 scripts/measure/ledger.py --brief`, which was always their source.
