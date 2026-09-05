# LJ-1.295: MOVE `scripts/` into subdirectories. The owner ruled option C.

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch_policy.py` before writing this line and took the head it
gave.** **QUEUED, not run**: `[LJ-1.291]` holds `scripts/` and is repairing the
depth anchors. The queue waits for that territory and fires when it clears.

## THE RULING

**The owner ruled OPTION C on 2026-08-15: accept the breakage, do the move.**

**So: NO shims (option B), NO `where.py` resolver (option D).** The 3,215
citations under `agents/` break as reader pointers and that is the accepted
price. **Do not build a mitigation the owner declined.**

## THE LAYOUT, from `[LJ-1.290]`

| target | members |
|---|---|
| `scripts/` flat | `agents_tree.py`, `dispatch_policy.py` |
| `scripts/gate/` (16) | the `make check` and git-hook checkers |
| `scripts/dispatch/` (4) | `check-dispatch-policy`, `check-sources-read`, `dd25-record`, `rules` |
| `scripts/measure/` (6) | `check-ratio`, `check-timing`, `check-unbound-hyp`, `deletion-test`, `ledger`, `obligations` |
| `scripts/site/` (5+1) | `extract-types`, `gen-depmap`, `i18n_markers`, `link-check`, `render-site`, `weave-i18n`, `depmap-template.html` |
| `scripts/ops/` (1) | `agda-watchdog.sh` |

Unchanged: `scripts/README.md`, `scripts/tests/`, `scripts/git-hooks/`.
**The full mapping and the per-file reasoning are in
`agents/tasks/LJ-1-290/lj-1.290-report.md` section 2. Read it; do not re-derive
it.**

## THE TWO FLAT MODULES, AND THEY ARE FLAT FOR DIFFERENT REASONS

**This is the half `[LJ-1.290]` got half right, and the brief says so because
the report's own rule does not cover both.**

**`agents_tree.py` STAYS FLAT because it is genuinely cross-group.** Seven
importers, five landing in `gate/` and two in `dispatch/`, and they take only
`briefs()` and `documents()`. **That is one question answered once, not two
things in one module, so DO NOT SPLIT IT.** Its own docstring records why it
exists: five checkers each wrote their own predicate and drifted, and two of
them were still drifting this morning.

**`dispatch_policy.py` IS NOT CROSS-GROUP, and the report's rule does not
explain it.** I measured: it has exactly ONE tracked importer,
`check-dispatch-policy.py`, which lands in `dispatch/`. By the report's own
placement rule it belongs in `dispatch/`.

**It is flat for a different reason: an OUT-OF-REPO consumer.**
`.claude/skills/codex-dispatch/dispatch.py` does `sys.path.insert` on the
scripts directory at `:112-113` and `import dispatch_policy` at `:124`, and that
file is untracked and outside every scope.

**So write TWO placement rules in `scripts/README.md`, not one:**

1. **A module imported across groups lives in the shallowest directory
   containing every importer.**
2. **A module with a consumer OUTSIDE this repository stays where that consumer
   expects it, and the exception is NAMED with the consumer at `file:line`.**

**Rule 2 is what actually keeps `dispatch_policy.py` flat. Say so.** A rule that
looks like it explains a case it does not is worse than an admitted exception.

## THE THREE THINGS THAT MUST NOT BREAK

**1. THE DEPLOY.** `.github/workflows/cloudflare.yml:43` and `pages.yml:51`
BOTH run `python3 scripts/link-check.py _build/site`. **Edit BOTH in the same
change.** Editing one deploys one site and leaves the other stale, and that
failure appears only after a merge to `main`.

**2. `make check`.** 26 invocations in `Makefile`, plus the git hooks. **Every
checker must report the SAME counts after the move as before.** Capture the
output of each BEFORE you move anything, and diff.

**3. THE SILENT FALSE-GREENS `[LJ-1.290]` FOUND.** A naive move made
`check-probes.py` and `check-live-territory.py` report `clean` over 55 files
instead of 2,425, exit 0; flipped `check-agents-guard.py` to `0 guarded
commit(s)`; and made `check-rule-ids.py` scan almost nothing. **`[LJ-1.291]` is
repairing the root anchors right now, so VERIFY the repair landed before you
move**, and re-run those four specifically. **If any reports a smaller count
after the move, STOP.**

## `scripts/README.md` IS THE ONLY DECLARED TAXONOMY

642 lines. **REWRITE it to the new layout, in place. Do not add a second
document beside it**: DD19 forbids a rule being canonical twice.

## `AGENTS.md` IS DD19-GATED AND IS NOT YOURS

**It names 15 scripts, 8 of them WITH paths** (`scripts/check-probes.py`,
`scripts/ledger.py`, `scripts/rules.py`, `scripts/lint-prose.py`,
`scripts/dispatch_policy.py`, `scripts/check-agents-guard.py`,
`scripts/check-rule-ids.py`, `scripts/check-task-index.py`). **A move makes
those eight wrong, and `check-dev-docs.py`'s `agents-enforcers` subcheck fails
inside `make check` when a named script does not exist.**

**DO NOT EDIT `AGENTS.md`.** It needs the owner's ruling and a dated
`AGENTS-diff-approved:` trailer (DD19). **Report the exact eight lines I must
change, and say whether making them BARE NAMES instead of paths would keep the
subcheck green**, because that would decouple `AGENTS.md` from the layout
permanently and no future move would touch it.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **EVERYTHING MOVES AND EVERY CHECKER MATCHES ITS BASELINE.** Report the
  baselines, the four re-run gates, and the two workflow edits. STOP.
- **A CHECKER REPORTS A SMALLER COUNT.** **STOP.** That is the defect this whole
  chain exists to avoid.
- **`[LJ-1.291]`'s REPAIR IS NOT IN THE TREE.** Then the anchors still count
  directories and the move is unsafe. **Say so and stop.**
- **A FILE HAS NO GROUP.** `[LJ-1.290]` named 8 as ambiguous and mapped every
  one. **The migration must REFUSE to run with an unmapped file** and there is
  no `misc/` bucket (C-43).

## CONSTRAINTS

- **DO NOT RUN AGDA.** Siblings hold both slots.
- **Do not run `make check`**; I run it. Run the individual checkers.
- Your write territory: `scripts/`, `Makefile`, `.github/workflows/`, `dev/`
  documents that name a script path, and `agents/tasks/LJ-1-295/`.
  **NOT `AGENTS.md`. NOT `CLAUDE.md`. NOT `dev/PLAN.md`. NOT `src/`. NOT
  `.claude/`. NOT `agents/` beyond your own directory.**
- **Use `git mv`**, so history follows the file.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- **Create `agents/tasks/LJ-1-295/lj-1.295-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/lint-prose.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**C-43. An escape hatch is the shape a wrong choice hides in.** A `misc/`
bucket is that shape. So is a placement rule that pretends to explain
`dispatch_policy.py`.

**C-48. A policy that only a document states is not enforced.** **If the new
layout needs a rule like「a new script goes in the right subdirectory」, name
its enforcement point or say it has none.**

**C-44.** Every number in this brief is `[LJ-1.290]`'s or mine and you must
re-derive each one.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. This task writes no mathematics. **Say in one
line whether a reader could place a new script without asking, and whether the
taxonomy survives the script count doubling.**

## ARCHIVE (DD18)

**`agents/tasks/LJ-1-290/lj-1.290-report.md`, read WHOLE.** It is the plan; this
brief only rules on it. **`archive/dev/TASKS-archived.md`**, taking SHAPE and
never a claim: the retired route reorganised directories and what it cost is on
the record. Return an **ARCHIVE USED** section naming ONE line read per archived
file.

## LITERATURE (DD18)

No mathematical literature bears on directory layout. Say so in one line and
return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-290/lj-1.290-report.md` FIRST, whole.

## SCOPE (write)

As listed under CONSTRAINTS.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for rewrite` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS IS AN
EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **DD13.** Price a retirement from the rewrite side.
- **C-40.** Verify the CONSUMERS of a changed file, never the file alone.
- **C-42.** A refutation measures the site it names and never how far it
  extends. **`[LJ-1.290]` named four gates that go silently green; the sweep for
  a fifth is yours.**
- **D-10.** Price the truth of a recorded residue before pricing its proof.
  **`[LJ-1.290]`'s baselines are a record and they are one day old.**
- **P-l.** A judgement at one site is a hypothesis at another. **The migration
  was tested on a COPY; the tree is not the copy.**
- **D-26.** A well-founded key on a tower needs generation data, or syntax.
  **It does not bear here and I say so rather than pretend it does.**
- **C-43, C-44, C-48. DD19.**

## RETURN

**Lead with every checker's baseline against its post-move output, and the four
gates `[LJ-1.290]` named, specifically.** Then both workflow edits. Then the two
placement rules as you wrote them into `scripts/README.md`. Then the exact eight
`AGENTS.md` lines I must change, and whether bare names keep the subcheck green.
Then any file that resisted its group. **Mark every negative MEASURED or
INFERRED.**
