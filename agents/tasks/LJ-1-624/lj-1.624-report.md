# LJ-1.624 report: landing `CardAboveL` into `src/L/CardinalAbove.lagda.md`

## HEAD

head_slot: coder
machine: exclusive
agda_tier: heavy
verdict: GO. `CardAboveL` is in the tree at `src/L/CardinalAbove.lagda.md::CardAboveL`,
green in one fresh Agda process at the pane's heavy-tier caliber, with the one
aggregator line in `src/Everything.lagda.md`. The recipe of `[LJ-1.622]` is followed
to the letter: the floor is measured first, the probe of `[LJ-1.526]` is not
imported, and `make check` is not re-run in the landing run.

## THE OBLIGATION

    CardAboveL :
        (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ θ ∈ SL.S ]
           (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

at `src/L/CardinalAbove.lagda.md:580-585` (declaration `:580`, term `:585`). The
statement and the term are byte-identical to the block of `[LJ-1.528]`,
`agents/tasks/LJ-1-528/Probe528.agda:638-643`: the diff of the two six-line blocks
is empty (re-run this dispatch, 2026-08-25). The telescope is `{ℓ : Level}
(lem : LEM (ℓ-suc ℓ))` and nothing else (`src/L/CardinalAbove.lagda.md:18`), the
probe's own telescope. The statement is not weakened by one hypothesis.

Nothing is postulated, no hole, no choice. The only import lines of the master
carry no probe of this campaign: the grep for `LJ-1-526`, `LJ-1-528`, `Probe526`
and `Probe528` over the master's import lines is empty; the four hits it returns
are comments, and they are provenance. The first fence line is
`{-# OPTIONS --cubical --safe --guardedness #-}` (`src/L/CardinalAbove.lagda.md:4`).

## CALIBER AND STATE

- **Caliber: `-A64m -I0 -M4g`**, read from the pane's `GHCRTS` at dispatch start.
  It is the HEAVY tier (`dev/pod/heads.toml`, `[tiers.heavy]`), cap 4,294,967,296
  bytes. It is never set by this task.
- Every Agda run is ONE fresh process, timed with `/usr/bin/time -l`, and each log
  is written to `agents/tasks/LJ-1-624/runs/` before the next run starts. The
  harness is `runs/run.sh`; its own comment says the caliber comes from the pane
  and is never set there.
- The brief's estimates (a 766 MB / 3 s floor, an 843 MB / 3.91 s term) are
  measured at the WIDE tier `-M2g` by `[LJ-1.622]`. My numbers are at `-M4g`. The
  slot rule says a number under another caliber is not a comparable, so my numbers
  are the price and the wide-tier numbers are the reference, labeled as such.

**THIS DISPATCH IS THE THIRD OF THE SAME TASK, AND THE WORKTREE CARRIES THE
TWO BEFORE IT.**

- `.pod-state/state.json` (main tree, read 2026-08-25): the task `LJ-1.624`
  carries `proc_start "Tue 25 Aug 01:25:35 2026"` for this dispatch, `obl_before
  0`, and `park_reason "row:task-lj-1-624-heap-wall-park"`, the reason persisted
  from the wide-tier park.
- Attempt 1 (2026-08-24 17:29-17:47, WIDE tier) wrote the master and the
  aggregator line, measured the chapter green at the 2 g cap (933,462,016 bytes,
  4.16 s, exit 0, `runs/typecheck-chapter.out`), then ran the whole tree at the
  2 g cap and walled (1,880,276,992 bytes, 19.18 s, exit 251,
  `runs/typecheck-everything.out`). The program's acceptance re-ran the whole
  tree at 2 g, walled again (14.36 s, exit 251, conjunct 1 FAILED), and parked
  the task by `heap-wall-park` (`runs/accept-1.out`).
- Attempt 2 (2026-08-24 23:37 to 00:44, HEAVY tier) re-measured the recipe here:
  the floor, the chapter, the bare import, all green (the logs below), and
  returned a report that still carried TODOs in its survey sections. The
  program's acceptance ran the whole tree at `-M4g`, green in 15.69 s (conjunct 1
  held), and failed conjunct 6 on the survey duty (`runs/accept-2.out`). This
  dispatch completes that report. It changed no line of the landed code.
- At my dispatch point the obligation was therefore ALREADY discharged in this
  worktree, and the dispatch-point meter measured it: 0 unresolved. Two pieces
  of evidence: `obl_before 0` in `.pod-state/state.json`, and the witness file
  the meter wrote into this worktree at dispatch time,
  `.pod-state/witness/Witness-LJ-1-624-8bc86b19.agda` (mtime 2026-08-25 01:25,
  its interface `_build/2.8.0/agda/.pod-state/witness/Witness-LJ-1-624-8bc86b19.agdai`).
- **THE EXIT DELTA IS 0, AND THE TASK ROW `go` CANNOT MATCH THIS DISPATCH.** The
  exit delta is the unresolved count at exit minus `obl_before`
  (`scripts/pod/witness.py:535-537`). Both ends are 0, so the delta is 0 whatever
  this task does. The task row `go` in the brief requires
  `obligations_delta_max = -1`. A green record with the in-scope review file
  present routes to the row `stop-stated` (exit 0, delta at least 0,
  `review-of-*.md` in the changed files, no `review-of-LJ-*-*.md`), and that row
  escalates to `mathematician_adversarial`. That is the designed path for a
  return that carries a review file: the critic reads this report and
  `agents/tasks/LJ-1-624/review-of-CardAboveL-landing.md`.

## THE FLOOR, THEN THE TERM

**THE FLOOR, FIRST, BEFORE ANY LANDING (W3 AND D-10).** The W3 term is this
worktree's warm floor: the eleven `src` interfaces warm, one trivial term. It is
measured with `agents/tasks/LJ-1-624/Probe624.agda`, whose import block is
byte-identical to `agents/tasks/LJ-1-619/Probe619.agda:17-31` (diff is empty
apart from the module name line), the floor file `[LJ-1.622]` ran. One fresh
process, the pane's `-M4g`, 2026-08-25 00:25:

| run | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|
| floor, eleven src imports, one trivial term | 635,355,136 | 14.8 | 3.05 | 0 | `runs/floor624.out` |

Against `[LJ-1.622]`'s floor of 765,902,848 bytes (35.7 percent of the 2 g cap)
in 3.06 s (`agents/tasks/LJ-1-622/runs/floor.out`), wide tier: the seconds agree
to 0.01, and the bytes sit at the LOW end of the run-to-run spread that task
itself recorded, "the run-to-run spread of the floor alone is 635 to 766 MB
(20 percent)", the low end being its own pre-`run.sh` manual floor at
635,387,904 bytes. Mine is 32 KB from that manual run.

The recipe's test: "about 766 MB and 3 s means proceed; far higher means bisect
the `_build` state". 635 MB is not far higher; it is inside the floor's own
documented spread. **Verdict: the warm floor fits, the elaboration fits, proceed.
No bisect of the build state is needed, and none was done.**

**THE TERM.** `agda src/L/CardinalAbove.lagda.md`, one fresh process, the whole
chapter, a genuine re-elaboration (the log carries its `Checking L.CardinalAbove`
line; the module's own interface was invalidated before the run and regenerated
identically after it, so the eleven dependency interfaces stayed warm):

| run | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|
| `Checking L.CardinalAbove`, the whole master, fresh elaboration | 933,412,864 | 21.7 | 4.55 | 0 | `runs/typecheck-chapter624-fresh.out` |

Two data points from attempt 2, kept as interface loads and not re-elaborations
(neither log carries a `Checking` line; attempt 2 verified that Agda 2.8.0
judges up-to-date by content digest, so an unchanged master is never re-run):

| run | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|
| chapter as pure interface load | 765,214,720 | 17.8 | 2.71 | 0 | `runs/typecheck-chapter624.out` |
| chapter as pure interface load, second run | 765,247,488 | 17.8 | 3.11 | 0 | `runs/typecheck-chapter624-cold.out` |

Compared, with the tier labeled: the fresh elaboration at `-M4g` is
933,412,864 bytes in 4.55 s; attempt 1's fresh elaboration of the same bytes at
`-M2g` is 933,462,016 in 4.16 s (`runs/typecheck-chapter.out`), 50 KB apart, so
the number is reproducible across tiers; the interface load at `-M4g` is
765,214,720 in 2.71 s, and `[LJ-1.622]`'s second-pass top rung, the same shape
at `-M2g`, is 764,903,424 in 2.75 s (`agents/tasks/LJ-1-622/runs/probe622b.out`).
The brief's reference, `[LJ-1.622]`'s first-pass peak 843,366,400 in 3.91 s, is a
partially elaborated ladder (its part 3 over the warm parts below it) and a
different module boundary from the whole master as one module; it is a
reference and not a comparable. Nothing in the master comes close to the cap:
the worst rung of my landing is 21.7 percent of it.

**THE ONE AGGREGATOR LINE, AT ITS NARROWEST SHAPE.** `runs/ImportCheck624.agda`
is a module whose body is one bare `import L.CardinalAbove`. One fresh process:

| run | peak RSS | percent of cap | seconds | exit | log |
|---|---|---|---|---|---|
| bare import of `L.CardinalAbove` | 728,121,344 | 17.0 | 2.65 | 0 | `runs/import-check624.out` |

**THE WHOLE TREE, AT THE HEAVY CAP.** I did not re-run it in this landing run.
The recipe's second item forbids re-running `make check` in the landing, and the
program's acceptance already ran the whole tree at this same tier and caliber:
`run src/Everything.lagda.md rc 0 seconds 15.69`, `runs/accept-2.out:11`, under
`GHCRTS -A64m -I0 -M4g` (`runs/accept-2.out:6`). That is the whole-tree green
this campaign had not carried: the same tree walled at the 2 g cap in attempt 1
(19.18 s, exit 251), and at the 4 g cap it is green. A re-run by me would repeat
the same code for no new measurement.

## WHAT IS NOW IN SRC

- `src/L/CardinalAbove.lagda.md`, NEW, 586 lines, a leaf master: nothing imports
  it, so it adds no import edge to any existing chapter. sha256
  `b29013d670c542dab6a6a576317125189a9d089ec8522f56ca44b7982dae1ced`
  (re-verified this dispatch). The declaration is at `:580`, the term
  `CardAboveL = noInjOrd→CardAboveLᵀ noInjOrd` at `:585`.
- `src/Everything.lagda.md`, one line added at `:397`: `import L.CardinalAbove`,
  after `import L.StageBound` (`:396`) and before `import L.Choice.Transversal`
  (`:398`). The git diff is that one added line. Nothing reordered.

**PROVENANCE.** Both files were written by attempt 1 of this same task, in this
worktree, and are uncommitted. Attempt 1's chapter run was green at the wide cap
(`runs/typecheck-chapter.out`), and attempt 1's report
(`runs/attempt-1-report.md`) verified the statement byte-identity against the
probe. This dispatch changed no line of either file. It re-verified the
statement against `agents/tasks/LJ-1-528/Probe528.agda:638-643` (diff empty),
re-verified that the master's import lines carry no probe import, re-verified
the sha256, and re-measured the chapter green at the heavy cap (the table
above).

**IF NOTHING LANDED, I WOULD SAY THAT PLAINLY. SOMETHING LANDED: one term, the
first of this campaign, plus the one aggregator line.**

## THE GATES, RUN INDIVIDUALLY DURING THE WORK

Every component of `make check` (`Makefile:40-41`) except the whole-tree
`typecheck` target, run individually, all with `.venv/bin/python` (Python
3.11.16), 2026-08-25, each log under `runs/`:

| component | command | result | log |
|---|---|---|---|
| venv-check | `test -x .venv/bin/python` | 0, venv present | `runs/gate-venv-check.log` |
| lint-agda | `scripts/gate/lint-agda.py --check` | 0 | `runs/gate-lint-agda.log` |
| lint-prose | `scripts/gate/lint-prose.py --check` | 0 | `runs/gate-lint-prose.log` |
| glossary | `scripts/gate/check-glossary.py --check` | 0 | `runs/gate-glossary.log` |
| fences | `scripts/gate/check-fences.py --check` | 0, clean, 103 masters | `runs/gate-fences.log` |
| probes | `scripts/gate/check-probes.py --check` | 0, clean, 7,949 tracked files | `runs/gate-probes.log` |
| markers | `scripts/site/weave-i18n.py --check` | 0 | `runs/gate-markers.log` |
| ledger | `scripts/measure/ledger.py --check` | 0, thresholds SUSPENDED, reported not enforced | `runs/gate-ledger.log` |
| closure | `scripts/pod/check-closure.py --check closure` | 0, clean, 103 masters | `runs/gate-closure.log` |
| ruleids | `scripts/gate/check-rule-ids.py` | 0, clean, 56 files | `runs/gate-ruleids.log` |
| specsurface | `scripts/pod/check-spec-surface.py --check` | 0, clean, 8 surface files, 499 in-fence lines | `runs/gate-specsurface.log` |
| reuse | `.venv/bin/reuse lint` | 0, missing 0, bad 0 | `runs/gate-reuse.log` |
| typecheck (the whole tree) | not run by me, see below | program acceptance: rc 0, 15.69 s | `runs/accept-2.out:11` |

The survey duty of acceptance conjunct 6, `scripts/pod/check-survey-quotes.py
LJ-1-624`, was RED at the end of attempt 2 (this report then carried TODOs in
the survey sections) and is re-run green at the foot of this section, after the
sections are filled: 0, `runs/gate-survey-quotes.log`.

## make check

NOT RUN IN THIS LANDING RUN, per the recipe's second item. The measured reason:
`AGENTS.md:74` makes `make check` the gate before a commit, and the program
commits (rule R8, `AGENTS.md:78`), so the suite runs at the program's own cap
(`Makefile:20` exports `-A64m -I0 -M16g` for the `typecheck` target), not this
pane's. The components of it were run individually while the work was live, as
the table above shows. The whole-tree `typecheck` step is the one component I
did not run, and the program's acceptance ran it at the pane's heavy cap
instead: green, 15.69 s, `runs/accept-2.out:11`.

## W2, THE GENERIC CARRIER

The brief names no fixed carrier and this task instantiates nothing. The chapter
states `CardAboveL` once, at a generic `{ℓ}` and one `lem`, and no second proof
in the tree carries a copy it could share. Nothing to share, nothing fixed: the
rule is not exercised, and this is the same answer `[LJ-1.622]` gave.

## W3, THE WIDEST UNMEASURED TERM

It is this worktree's warm floor, and it is measured FIRST, above, before any
landing: 635,355,136 bytes in 3.05 s, exit 0, `runs/floor624.out`. The brief
guessed about 766 MB and 3 s; the measured number is 635 MB and 3.05 s, and the
brief's own reference task recorded the 635 MB end of the spread in its own
manual run, so the guess and the measurement are the same number inside its own
variance. The floor decided the D-10 question: about, not far higher, proceed,
no bisect.

The wide unmeasured term the brief named turned out to be a whole-tier question
in attempt 1 (the 2 g wall, 19.18 s, exit 251, `runs/typecheck-everything.out`)
and this dispatch line measures it at the heavy cap: the whole tree is green at
`-M4g` in 15.69 s, `runs/accept-2.out:11`.

## WHAT THE LANDING COST, AND WHAT IT DID NOT RESIST

**The cost.** One term, 586 lines of a new master, one aggregator line. The
frame (the eleven warm interfaces) costs 635 MB and 3 s; the whole chapter costs
933 MB and 4.55 s at the heavy cap, 21.7 percent of it; the bare import line
costs 728 MB and 2.65 s; the whole tree costs 15.69 s of the program's
acceptance at the same cap and no RSS record. The shape resisted nothing:
every rung of `[LJ-1.622]`'s ladder was already 39.3 percent or less of the 2 g
cap, and the master as one module is 21.7 percent of the 4 g cap.

**What resisted.** Only the tier did. Attempt 1 ran the whole tree under the
wide 2 g cap and the tree, not the term, exhausted the heap in 19.18 s, exit
251, `runs/typecheck-everything.out`; the program's acceptance re-hit the same
wall (`runs/accept-1.out`), and the task parked. That wall is a property of the
whole tree at 2 g and has nothing to do with the one landed term, which peaks at
43.5 percent of that same cap in attempt 1's own run (`runs/typecheck-chapter.out`).
The heavy cap carries the whole tree green, `runs/accept-2.out:11`. After the
tier correction, nothing in the recipe failed: the floor was within its spread,
the term was within its cap, and the import line resolved.

## TWO ITEMS FOR THE NEXT BRIEF, BOTH MEASURED, BOTH OUT OF THIS SCOPE

1. **The duplication `[LJ-1.555]` named is still open.** The same `CardAboveL`
   exists twice, at `agents/tasks/LJ-1-528/Probe528.agda:638-643` and at
   `src/L/CardinalAbove.lagda.md:580-585`, and nothing makes the two agree in
   the future. The cure is one line, outside this scope: replace the probe's
   sections 0 to 9 with `open import L.CardinalAbove {ℓ} lem using ( CardAboveL
   )`, which also re-proves the `[LJ-1.526]` chain against the LANDED term
   (`agents/tasks/LJ-1-555/lj-1.555-report.md`, WHAT MOVED AND WHAT DID NOT).
2. **`cardAboveAnyOrd` is still free and still stronger.**
   `agents/tasks/LJ-1-528/Probe528.agda:669-678` proves an ordinal L-cardinal
   above EVERY ordinal, cardinal or not, finite or not, at ten lines over what
   is now landed. Left out because this brief gave one obligation, not because
   it is expensive.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` was read. The landed chapter's comment
  prices its own construction against the predecessor's Hartogs build, and this
  file carries that price. `archive/dev/LJ-dispatch-index.md:170` read:
  "1058 lines, 27 s, no choice." That is the row of `[LJ-1.94]`, the ambient
  Hartogs the master's section 6 comment names, and the landed chapter builds
  the same fact in 586 lines without the order types.
- `dev/ARCHIVE.md` was surveyed by grep over `CardinalAbove`, `LJ-1.528`,
  `LJ-1.526` and `LJ-1.62`: no hit. This dispatch retires no module, so nothing
  in it bears on this landing, and it is declined as a premise.
- `archive/dev/JOURNAL.md` declined: not read. The campaign history it holds is
  not a premise of the landing or of its measurement.
- `archive/dev/JOURNAL-archived.md` declined: not read. Same reason.
- `archive/dev/DECISIONS-archived.md` declined: not read. Same reason.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md` declined: not read. The
  truncation behavior this chapter uses is settled in the tree
  (`L.BoundedSubset`, `L.StageCardinal`) and is re-measured nowhere by the
  landing.
- `dev/literature/devlin-II5.md` declined: not read. The Devlin II.5 content
  lives in `L.StageCardinal` and `L.BoundedSubset`, which this landing loads but
  does not price.
- `dev/literature/digest.md` declined: not read. This is a landing and a
  measurement; no mathematical statement is settled here, and no digest entry
  changes anything.
- `dev/literature/terms-2026-08.md` declined: not read. No term-definition
  question is open in this dispatch; the landed term is the probe's, byte for
  byte.
- `dev/literature/formalizations-landscape.md` declined: not read. No
  positioning question is open in this dispatch.
