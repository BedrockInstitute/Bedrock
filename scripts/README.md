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
| `scripts/gate/` | runs inside `make check` or a git hook; a red one stops a commit | `check-fences.py`, `check-glossary.py`, `check-probes.py`, `check-rule-ids.py`, `lint-agda.py`, `lint-prose.py` |
| `scripts/measure/` | costs seconds to minutes, runs Agda, or reports a number; never a gate | `check-ratio.py`, `check-timing.py`, `check-unbound-hyp.py`, `deletion-test.py`, `dispatch-usage.py`, `ledger.py`, `obligations.py` |
| `scripts/site/` | the publishing pipeline and the deploy | `extract-types.py`, `gen-depmap.py`, `i18n_markers.py`, `link-check.py`, `render-site.py`, `weave-i18n.py`, `depmap-template.html` |
| `scripts/ops/` | machine safety | `agda-watchdog.sh`, `bark-push.sh` |
| `scripts/pod/` | the POD program of goal LJ-4: it runs the route and it is not a gate | `accept.py`, `check-closure.py`, `check-spec-surface.py`, `check-survey-quotes.py`, `digest.py`, `facts.py`, `heads.py`, `launcher.py`, `pi_stream.py`, `pod.py`, `preflight.py`, `replay.py`, `retrieve.py`, `rules.py`, `table.py`, `witness.py` |

Unchanged in place: this `README.md`, `scripts/tests/`, `scripts/git-hooks/`.

### THE ONE PLACEMENT RULE for an imported module

**A module that another script imports lives in the shallowest directory that contains
every importer.** No judgement call is needed:

| module | importers | lands in |
|---|---|---|
| `repo_root.py` | scripts in `gate/`, `dispatch/` and `measure/` | `scripts/` (flat) |
| `agents_tree.py` | `check-rule-ids.py` (`gate/`), `check-sources-read.py` (`dispatch/`), seven files in `pod/` | `scripts/` (flat) |
| `i18n_markers.py` | `weave-i18n.py`, `gen-depmap.py`, `render-site.py` (all `site/`) | `site/` |
| `ledger.py` | `check-ratio.py`, `deletion-test.py` (both `measure/`) | `measure/` |
| `lint-prose.py` | `check-glossary.py` (`gate/`, loaded by path) | `gate/` |
| `check-timing.py` | `check-ratio.py` (`measure/`, loaded by path) | `measure/` |
| `obligations.py` | `check-timing.py` (`measure/`, loaded by path) | `measure/` |

`repo_root.py` and `agents_tree.py` are flat BY THIS RULE, not by exception: no shallower
directory contains all their importers than `scripts/` itself. A consumer outside this
repository is not an importer for placement. The one such consumer was the retired
`codex-dispatch` skill, and the POD cutover of 2026-08-18 replaced it with
`scripts/pod/launcher.py`, which is inside the tree.

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
directories under `scripts/` is pinned (no `misc/` bucket can appear silently, C-43), and
the flat `.py` set is pinned to the two cross-group modules (a new flat script must either
have importers across groups or join one).

**THE COVERAGE CHECK RUNS IN ONE DIRECTION ONLY, and this sentence is the record of
the gap.** `test_readme_table_matches_every_group_directory` compares the LAYOUT TABLE
above with the tree, file by file, in both directions. **No test reads the per-script
`###` sections below.** So a script that leaves the tree keeps its section, with its
command block, until a reader notices: the POD cutover of 2026-08-18 archived seventeen
scripts and left all seventeen sections live here. The missing half is a reverse check,
that every `scripts/<group>/<name>.py` path this file names exists in the tree. It is not
built, and until it is, deleting a script means deleting its section by hand.

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

### `check-fences.py`

Catches Agda that sits OUTSIDE a code fence in a `.lagda.md` master. It runs in
`make check` and in the pre-commit hook.

**One measured failure built it.** On 2026-08-11 `[LJ-1.41]` reported two
condensation row agreements CLOSED and machine-checked. `[LJ-1.42]` then found
that both sat outside the ` ```agda ` fence, as prose, and that they carried
four real defects. **Every gate passed.** Agda typechecks only fenced code, and
`scripts/measure/ledger.py` counts only fenced lines, so the master was green and
the size figure was right. Unfenced text is invisible BY CONSTRUCTION to every
tool this repository has.

It looks for a RUN of consecutive declaration-shaped lines outside a fence. One
`Note:` in a paragraph is prose; three or more such lines together is a lost
fence. **It cannot tell a lost fence from a deliberate code SAMPLE in prose**, so
a hit is a defect or a style violation, and either way it wants a human.

```sh
python3 scripts/gate/check-fences.py           # report
python3 scripts/gate/check-fences.py --check   # gate mode (make check, the hook)
python3 scripts/gate/check-fences.py --run 5   # raise the run threshold
```

### Archived gates

**The POD cutover of 2026-08-18 archived thirteen gates out of this directory.**
`check-agents-guard.py`, `check-archive-cited.py`, `check-baseline-home.py`,
`check-build-manifest.py`, `check-dd18-survey.py`, `check-dd25-review-named.py`,
`check-dd4-stated.py`, `check-dev-docs.py`, `check-live-record-claims.py`,
`check-live-territory.py`, `check-premises-stated.py`, `check-task-index.py` and
`check-tree.py` are frozen under `archive/scripts/gate/`, at the same basename.
Each one's own docstring is still its operative documentation.

**Read the disposition before you read the file.** `dev/memos/LJ-4-pod-program-design.md`
section 7.1 gives every one of them a row: RETIRE, because a ruling it served is
SUPERSEDED, or REWRITE, because its function moved into `scripts/pod/`. Three
functions moved rather than died: `check-tree.py`'s closure half is
`scripts/pod/check-closure.py`, `check-dd18-survey.py` is
`scripts/pod/check-survey-quotes.py`, and `check-agents-guard.py`'s approval
mechanism is `scripts/pod/check-spec-surface.py`. `dev/ARCHIVE.md` is the
registry.

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
python3 scripts/pod/rules.py --for build     # build, probe, recon, rewrite, review
python3 scripts/pod/rules.py --grep seal     # the long tail, by trigger word
```

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
have passed `[LJ-1.6]`. A miss is a signal for the adversarial reviewer, which the
program routes through the `mathematician_adversarial` and `coder_adversarial` slots
of `dev/pod/heads.toml`. The archived operating manual is
`archive/dev/ORCHESTRATION.md` section 1.1.

**ITS CORPUS IS AN UNTRACKED ORPHAN AND THE RETARGET IS NOT DONE.**
`check-sources-read.py:61` reads `.claude/skills/codex-dispatch/.state/logs`, which the
retired skill wrote: 1,017 files and 931MB, newest 2026-08-16, git-ignored, so a fresh
clone has none of it. The POD writes its own logs under `.pod-state/`.
`dev/memos/LJ-4-pod-program-design.md` section 7.1 row 23 says KEEP AND RETARGET, and the
retarget is section 7.4. Until it lands this tool reads history only, and nothing calls
it: no `make` target, no hook and no POD rule.

```sh
python3 archive/scripts/dispatch/check-sources-read.py LJ-1.6      # one or more task codes
python3 archive/scripts/dispatch/check-sources-read.py --all
```

### Archived dispatch scripts

**The POD cutover of 2026-08-18 archived four scripts out of this directory**:
`dispatch_policy.py` and `check-dispatch-policy.py`, which held DD17's head
table, `recall-hook.py`, and `dd25-record.py`. All four are frozen under
`archive/scripts/dispatch/`, with their suites.

**What replaced each one.** `dev/pod/heads.toml` is now the ONE home of the head
per slot, read by `scripts/pod/heads.py`, so no switch and no checker of a
`tier:` line survives. `dd25-record.py`'s record moved into the transition log's
`role` field. `recall-hook.py` was retired by physics: a Claude Code hook fires
only for an in-harness subagent, and the program dispatches through a harness.
`dev/memos/LJ-4-pod-program-design.md` section 7.1 rows 20, 21, 24 and 25 carry the
rulings.

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
python3 scripts/measure/obligations.py src/L/GCH.lagda.md
```

### `dispatch-usage.py`

**Tokens per dispatch, joined from the agent's own session file.** The cost
model of 2026-08-16 priced a dispatch at about 1,757 words of orchestrator
prose and about 35 delivered Agda lines, and then named the one input a cost
decision needs and could not supply: the registry record carries no usage
field, and `dev/vendors.toml` held price BANDS that nothing joined to a task
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

**No cost figure.** The vendor data named price bands and carried no per-token
rate, so money is not derivable here and none is invented (DD8). The POD cutover of
2026-08-18 archived that file to `archive/dev/vendors.toml` and moved the live model
data to `dev/pod/heads.toml`, which carries no rate either.

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

### `bark-push.sh`

Pushes one encrypted message to the owner's phone. The POD loop has two stops, and
`notify_owner()` calls this at both of them. It reads the body from `BARK_BODY`, and it
reads `BARK_KEY_URL` and `BARK_AES_KEY` from the environment. Both are deployment
secrets, so this copy holds neither and REFUSES to run when either is unset. The push is
AES-256-GCM with a fresh random 12-byte IV, and a failed encryption pushes nothing.

```sh
BARK_TITLE="POD 已停止" BARK_GROUP="Bedrock POD" BARK_BODY="<what happened>" \
  scripts/ops/bark-push.sh </dev/null
```

## pod/

The POD program of goal L9. `dev/memos/LJ-4-pod-program-design.md` is its design, and each
file below names the section it implements. **The program is in force since the cutover of
2026-08-18.** `make check` runs three of these files, as the `closure`, `specsurface` and
`instructions` targets; the `commit-msg` hook runs `check-spec-surface.py --msg-file`; and
`make survey` runs `check-survey-quotes.py`. `scripts/pod/pod.py` is the loop itself and no
`make` target calls it: the repository owner starts it with `pod.py run`.

**Eight of the sixteen files below have no section of their own**: `accept.py`, `heads.py`,
`launcher.py`, `pi_stream.py`, `pod.py`, `preflight.py`, `replay.py` and `table.py`. Each
one's docstring names the design section it implements, and
`dev/memos/LJ-4-pod-program-design.md` is the operative document for all of them.

### `facts.py`

The six-fact recorder, section 4.3.1. It holds `run_agda()`, which is the ONE place the
POD starts Agda, the error class map of fact 2, the changed-file snapshot of fact 4 and
the verification target rule of section 4.3.2. It measures, and it never routes.

### `witness.py`

The fact 3 witness meter, amendments A1 and A4. It reads one obligation as
`<probe path>::<dotted name>`, derives a witness module from the probe, runs it, and
reports one of four values: PASS, MISSING, PROBE RED or NO FILE. Only PASS is resolved.
Run it directly to meter an obligation:

```sh
python3 scripts/pod/witness.py "agents/tasks/LJ-1-383/Probe383.agda::Wire.residue2-false-at-record"
```

### `instructions.py`

**The generator of the SHARED half of every `dev/pod/instructions/<slot>.md`, from
`AGENTS.md`.** Amendment A8 makes `AGENTS.md` the ONE hand-written source of that half, and
this program copies its three sections (What Bedrock is, The milestone, Boundary) into all
five slot files, above a marker comment. Below the marker each slot's own clauses are
hand-written and this program never touches them.

**A rule restated in a second file is a rule that drifts**, and the file's docstring carries
the measurement: on 2026-08-04 a bulk refresh wrote a superseded concurrency rule into the
rulebook two days after the owner had widened it, three rewrites polished the sentence, and
the wrong rule steered dispatch for three days. Five slot files each carrying its own copy
is that failure five times over.

`--check` is the gate, and it is the `instructions` target of `make check`. `--write` is
what a person runs after editing `AGENTS.md`. **It is not the same gate as
`check-spec-surface.py`**: that one refuses an unapproved edit to `AGENTS.md`, and this one
refuses an approved edit that never reached the five files agents read.

```sh
python3 scripts/pod/instructions.py --check   # exit 1 when any slot file is stale
python3 scripts/pod/instructions.py --write   # regenerate every shared half
```

### `check-closure.py`

The closure check of section 7.2, and acceptance conjunct 3. It is the split half of
`archive/scripts/gate/check-tree.py` that the POD needs: closure, the archive boundary,
the unwired new master and the empty parameterized module. `make check` calls THIS file
as the `closure` target; the cutover of 2026-08-18 repointed it and archived the old
gate.

### `check-spec-surface.py`

The spec surface gate of section 7.3, and it serves rules R9 and R16. The surface is
`src/Landmarks.lagda.md` plus one file per `open import` in its fences, which VERIFIES
as 8 files and 499 in-fence lines. A bare `import M` is excluded, because those two
imports hold the proofs and a signature change there fails to typecheck. The gate hashes
every declaration signature into `dev/pod/spec-surface.toml` and refuses a silent move:
a worker can change `isZFCModel`, `𝒮ʟ` or `LEM` and leave the whole tree green while the
trophy asserts something different. R16 rides the same snapshot with one sha256 per rule
home. Four modes: `--check` at acceptance conjunct 5, `--msg-file` at the `commit-msg`
hook, no argument for the history audit, and `--write` to regenerate the snapshot.

### `check-survey-quotes.py`

The survey verification of section 7.4 Part 2, and acceptance conjunct 6. It is lifted
from `archive/scripts/gate/check-dd18-survey.py` and it keeps both gated halves of that
file: a
return must name every path the program injected, and a quoted phrase of twelve
characters or more must sit at each cited `path:line`. The brief-side print goes,
because the program performs the search now. The gate judges ONE task. `--all` sweeps
the tree and it is a survey tool, never a gate: the records written before the amendment
of 2026-08-16 fail it by construction.

### `retrieve.py`

The retrieval seam of section 7.4 Parts 1a and 1b. `retrieve(query, scope, k)` ranks a
scope with BM25 over whole files, and a later implementation replaces this one function
and nothing else. THE SCOPE IS THE MEASURED PART: the same ranker moved the gold file of
one detour episode from rank 444 over the full corpus to rank 1 over the archive scope,
and the record is `dev/measurements/pod-retrieval-scoping-2026-08-17.txt`. The module
also holds the miss signal, which writes one JSON line per dispatch and reports the
discriminative overlap of every missed file. It reports, and it never triggers.

### `digest.py`

The owner's digest of section 8, in Chinese. **The program writes it and no model writes
it or edits it.** `FIELD_SOURCES` binds every field to the file and the line that
produces it, and `scripts/tests/test_pod_digest.py` resolves all of them, so a field
whose source moves fails the suite rather than printing a stale number. It prints the
two AD7 numbers and twelve more, and every one of them reports and none of them
triggers: the rollback criterion is the owner's. NO SENTENCE IN IT RANKS ANYTHING,
because ranking is a judgement AD1 forbids the program. Rule (e) runs it beside the
maintainer batch, and it also serves the batch the three log-derived lists of section
6.7, so the batch and the digest count one thing one way.

```sh
python3 scripts/pod/digest.py --hours 12
```

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
scripts read the tree through it before the POD cutover of 2026-08-18, and seven of
those nine are now archived. **MEASURED 2026-08-18 by import, nine scripts read it
again**: `check-rule-ids.py` in `gate/`, `check-sources-read.py` in `dispatch/`, and
`accept.py`, `check-survey-quotes.py`, `digest.py`, `facts.py`, `pod.py`,
`preflight.py` and `witness.py` in `pod/`. This paragraph said FIVE until the first
count was taken: re-measure it rather than quoting it.

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

`git-hooks/pre-commit` runs eight fast checks and blocks the commit on any violation. In
the order the hook runs them: `lint-prose.py --staged`, `weave-i18n.py --check`,
`lint-agda.py --staged`, `check-glossary.py`, `check-probes.py --staged`,
`check-fences.py`, `check-closure.py` and `check-rule-ids.py`. The first six belong to the
LINT class of the design's section 5.4; the last two are cheap enough for the hook and are
not LINT class.

**The hook is one check short of what cutover step 11 specifies.** That step names
`check-survey-quotes.py` in the hook too, as the seventh LINT member, and the hook does
not run it. Nothing else runs it at commit time either: `make survey` is a manual target.

`git-hooks/commit-msg` runs R16's spec-surface guard, `check-spec-surface.py --msg-file`.
It refuses a commit that stages a guarded rule home, or the snapshot, without a
`Spec-surface-approved: YYYY-MM-DD (name)` trailer in the message. The guarded homes are
`AGENTS.md`, `dev/memos/LJ-4-pod-program-design.md`, `dev/pod/heads.toml` and every file
under `dev/pod/instructions/`.

Both hooks are version-controlled; activate them once per clone (or run `make hooks`):

```sh
git config --local core.hooksPath scripts/git-hooks
```

## Retired: `dashboard.py`, `check-dashboard.py`, `test_dashboard.py`

The generated dashboard was ABOLISHED by the owner on 2026-08-09. The three
scripts are frozen in `archive/scripts/`, and
[archive/scripts/README.md](../archive/scripts/README.md) records what they
did right and the one thing they got wrong. Standing figures now come from
`python3 scripts/measure/ledger.py --brief`, which was always their source.
