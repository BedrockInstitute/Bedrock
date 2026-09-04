# LJ-1.732 report, second dispatch: the wall is measured to a single site, and it is the program's 20-second window

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.732
obligation: agents/tasks/LJ-1-732/Probe732.agda::bound-in-stage-at-empty
verdict: **STOP ON THE CHECKING WINDOW.** The construction stands and grew
greener: six of its modules are now machine-checked (`Num`, `Amb1`,
`Amb3`, `Amb5`, `Amb6` from the first dispatch, plus the new `Amb7a`).
The remaining wall is no longer "somewhere in the cone": this dispatch
localized it to ONE elaboration act, the whnf of the erased `appAt`
antecedent under the two open binders, and measured it above every
window the pane's swap guard allows. Five restructurings were built and
tested in this dispatch; the two that still carried the antecedent
elimination both walled at the same 20-second sweep; the pieces that
avoid it are all green at floor prices. The D-10 finding is unchanged:
at the empty instance the reading is TRUE, the inhabiting term is in
the tree, and nothing in this wall bears on the mathematics.

Agda ran under the program's caliber for this pane,
`GHCRTS="-A64m -I0 -M2g"` (first line of every `.out`), wide tier, one
process at a time; I never set `GHCRTS`. Nothing is postulated. No
holes in any `.agda` file: the two hole-bearing bisect files are named
`.agda.txt` (`runs/Bisect7c.agda.txt`, `runs/Bisect7d.agda.txt`). No
commit, no push; written only inside `agents/tasks/LJ-1-732/`. All
probes are raw `.agda`, so the ratio bar's divisor is 0 and cannot
fire.

## 1. WHAT THIS DISPATCH MEASURED

The pane still runs the program's swap guard
(`scripts/ops/agda-watchdog.sh:28`, main checkout): while machine
swap-in-use is at or above 8192 MB, every 20-second sweep SIGKILLs the
largest `agda` process. Swap read `used = 8742.88M` at 07:30 local and
has been byte-stable within 16 MB for about 17 hours (`vm.swapusage`,
checked at dispatch start and end; RAM free 82 percent,
`memory_pressure -Q`), so the guard fires on stale allocation, not on
pressure. No single leaked holder exists to clean up: the top swap
holders are desktop applications at a few hundred megabytes each
(`ps ax -o pid,vswap=,rss=,comm=`). Every Agda process on this pane
therefore lives inside one 20-second sweep gap, effectively about
18.5 to 20 seconds.

The dispatch's numbers, all under the pane caliber:

| probe | content | outcome | evidence |
|---|---|---|---|
| `runs/Amb0.agda` | interface-load floor, no normalization | **GREEN 3.18 s**, 680 MB peak | `runs/amb0-1.out` |
| `runs/Amb7a.agda` | `ApproxAt` and `MotiveEmpty` named once | **GREEN 4.24 s** | `runs/amb7a-v3-1.out` |
| `runs/Amb4a.agda` | the graph reading named once | **GREEN 3.18 s** | `runs/amb4a-1.out` |
| `runs/Amb2a.agda` | the matrix3 reading at the triple named once | **GREEN 3.25 s** | `runs/amb2a-1.out` |
| `runs/Bisect7c.agda.txt` | Amb7b's full signature, body holed | elaborated in **3.44 s**, then the expected hole error | `runs/bisect7c.out` |
| `runs/Bisect7d.agda.txt` | Amb7b's body with the from-clause holed | killed at **16.6 s**, RSS 1.71 GB | `runs/bisect7d.out` |
| `runs/Amb7b.agda` | the two-binder kill as its own module | killed at 20.2 s in every full window; 17 kills, direct and phase-cycled | `runs/amb7b-*.out`, `runs/amb7b-p-*.out` |
| `runs/Amb7.agda` | rewritten to cite `Amb7a`'s named types | killed at 20.2 s in every full window | `runs/amb7-*.out` |

Three facts localize the cost. First, the floor is 3.2 s and every
type synonym in the cone, including the open-binder step reading,
defines at about 4 s. Second, Bisect7c shows Amb7b's whole signature
elaborates in 3.4 s, so no annotation is the problem. Third, Bisect7d
shows the cost persists with the from-clause's body holed out: what
remains is `PT.rec`'s scaffolding typing the from-pattern, which forces
the whnf of the erased `appAt` antecedent at the open environment
`(v ∷ u ∷ n 0 ∷ γ15)`. That is the one expensive act, and every proof
of this implication's vacuity must do it: the antecedent is false, and
exhibiting that requires eliminating its truncation, whose type is the
big normal form.

## 2. THE RESTRUCTURES, AND WHY EACH FAILS TO SHRINK THE COST

1. **Motive hoist.** The step reading under the binders is now named
   once in `runs/Amb7a.agda` (`MotiveEmpty`), so the body's motive
   shares one normal form. Green in its own module; the wall did not
   move, because the cost was never the motive's inline annotation.
2. **Type-synonym module.** `ApproxAt` names the approximation reading
   once (P-l: the statement names the reading, not the erased
   presentation). Green; the pair-check still walls.
3. **Lambda split.** `runs/Amb7b.agda` isolates the two-binder kill.
   It walls: its own body is the expensive act.
4. **Signature/body bisect.** Measured above: signature 3.4 s, body
   above every window.
5. **Phase-cycled launches.** `runs/phase.sh` rotates the launch offset
   so one attempt starts within a fraction of a second after a sweep
   and gets the full gap. Twelve attempts, offsets 0 through 18 in
   steps of 2: the lifetimes tracked the offsets exactly
   (20.2 − offset seconds), and the full-window attempt
   (`runs/amb7b-p-10.out`, 20.18 s) still died. The body needs more
   than 19.9 s; how much more is unmeasurable on this pane.

The peak resident set at every kill was 1.71 to 1.75 GB, plateaued,
well under the 2 g wide cap. This is a WINDOW wall, not a heap wall,
and no shape change moves it, because the normal form it needs is
fixed by `approxBndAt`'s shape
(`src/L/Condensation.lagda.md:2471-2477`): `domB ∧̇ ∀̇∈ ∀̇∈ (appAt ⇒̇
step)`, whose antecedent leaf is
`∃̇∈ (var 2) (prAtL zero 2 1)` over `src/L/Coding/Model.lagda.md:160`
and `src/L/Coding/Base.lagda.md:196`, read at an 18-slot environment
holding twelve `sucV`-iterate numerals.

## 3. WHAT IS GREEN, AND WHAT THE NEXT BRIEF NEEDS

Green interfaces in `_build/2.8.0/agda/`: `Num`, `Amb1`, `Amb3`,
`Amb5`, `Amb6`, `Amb7a`, `Amb4a`, `Amb2a`, `Amb0`. The chain to the
obligation is `Amb7b` (or `Amb7`'s inline body), `Amb7`, `Amb4`,
`Amb2`, `Probe732`, in that order.

- One pane whose machine is under the swap cap settles this: run
  `runs/Amb7b.agda`, then `runs/Amb7.agda`, then `runs/Amb4.agda`,
  then `runs/Amb2.agda`, then `agents/tasks/LJ-1-732/Probe732.agda`,
  one process at a time. None of the five carries a hole or a known
  diagnostic; the only Agda errors ever seen in this cone were fixed
  in-dispatch (`runs/amb7-1.out`, the `⟨_⟩`-bracket mismatch on
  `MotiveEmpty`, and its `.snd` parenthesization). If a pane allows 25
  to 40 seconds per process, all five land; the type prices are
  measured at about 3.2 s each, so any remaining surprises are
  ordinary body errors, cheap to fix there.
- Alternatively the owner can rule on the guard: the kill is firing on
  stale swap while RAM sits at 82 percent free, and one
  `hierarchy`-level exception, or any pane on a machine under the cap,
  unblocks the campaign's D-10 probe. That is the owner's call, not
  mine; I did not touch the guard, and I did not rename or wrap the
  binary to dodge `comm` matching.
- The D-10 correction of the first dispatch stands and should be read
  before anyone prices the `Completeness` bridge again: at the empty
  instance the demand is TRUE, the witness is the twelfth numeral, and
  the recorded prose target had the direction backwards. The
  construction that inhabits it is complete in the tree.

## 4. W2, ANSWERED

The mathematics is written once at the generic frame. The new modules
consume predecessor exports and add no second statement of anything:
`Amb7a` names two readings of formulas it imports from `Amb1` and
`Probe652`; `Amb7b` builds the implication leaf
`appAt (suc (suc zero)) (suc zero) zero` locally
(`runs/Amb7b.agda:36-37`) because `Amb1` names no leaf export, cites
`Amb1`'s `Mx`, `CntS`, `countAS` and `γ15` for everything else, and
re-instantiates no matrix. `Amb4a` and `Amb2a` are type synonyms only.

## 5. PRICE

- Landed this dispatch: four green modules (`Amb0`, `Amb7a`, `Amb4a`,
  `Amb2a`), each at a 3.2 to 4.2 s check.
- No time price is claimed for `Amb7b` or `Amb7`: no run completed.
  The measured bound is: body above 19.9 s, below unbounded, RSS
  plateau 1.75 GB, floor 3.2 s.
- The construction is 839 lines over the probe and thirteen run
  modules, 0 in-fence (raw `.agda`), so the ratio bar's divisor is 0.
- The brief's estimate was 40 to 120 lines for the term; the term is
  22 lines of `Probe732.agda` (`Probe732.agda:163-186`) and the rest
  is the checked-support skeleton the window discipline demanded.

## 6. THE RUNS THIS DISPATCH

Sixty-plus Agda launches, one process at a time, caliber line first in
every record: `runs/amb0-1.out` (green), `runs/amb7a-1.out`,
`runs/amb7a-v2-*.out`, `runs/amb7a-v3-1.out` (green),
`runs/amb4a-1.out` (green), `runs/amb2a-1.out` (green),
`runs/bisect7c.out`, `runs/bisect7d.out`, `runs/amb7-*.out` (18
window-kills across three shapes), `runs/amb7b-1..5.out` (direct),
`runs/amb7b-p-1..12.out` (phase-cycled). Kill attributions are by pid
against `/Users/alsg/Agentic/Bedrock/_build/tools/agda-watchdog.log`;
the last attributed kills are at 07:29:55 and 07:30:56 local.

## 7. GATES

`make check` is not run: the task lands no `src/` file and no commit.
The brief's mandatory check was run and its output is pasted verbatim.

```
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-732
check-survey-quotes: LJ-1-732 clean (0 note(s), 0 defect(s))
rc=0
```

Note on the interpreter path: this worktree carries no `.venv`
(git-ignored, not copied into worktrees), so the project's pinned venv
interpreter at the main checkout ran the checker, as in the first
dispatch's report, section 8.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` DECLINED.** Line 1 reads, verbatim:
  '# THE `DD` RULING SERIES, archived in full 2026-08-18'. Not used:
  the ruling series is closed, and this dispatch adds no ruling.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Line 1 reads, verbatim:
  '# ORCHESTRATION: the orchestrator's operating rules'. Not used: the
  dispatch process is not consulted by a probe.
- **`archive/dev/PLAN-archived.md` DECLINED.** Line 1 reads, verbatim:
  '# ARCHIVED 2026-08-20'. Not used: the live status is the screen,
  which this return does not restate.
- **`archive/dev/STATUS-archived.md` DECLINED.** Line 1 reads,
  verbatim: '# STATUS-archived: the goal table of the internalization
  route'. Not used: that closed route names no satisfaction reading
  and no caliber.
- **`archive/dev/TASKS-archived.md` DECLINED.** Line 1 reads,
  verbatim: '# Archived task index: the `L3.32-T` series'. Not used:
  that series is not a predecessor of this probe.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` DECLINED.** Not used:
  the slot roles this probe needs are carried by the code citations
  (520's Matrix header, 667's matrix3, Condensation's ApproxB), and
  the body was not consulted.
- **`dev/literature/devlin-errata.md` DECLINED.** Not used: no
  literature quote is under test; the formulas are the tree's own.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not used:
  no glossary term is proposed here.
- **`dev/literature/fine-structure.md` DECLINED.** Not used: fine
  structure is beyond this instance; the probe decides one
  satisfaction reading at one pair of codes.
- **`dev/literature/rudimentary-functions.md` DECLINED.** Not used:
  the rudimentary-functions content this cone needs is carried by the
  tree's own coding chapters, which the probe cites directly.
