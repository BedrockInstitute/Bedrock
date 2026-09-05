# LJ-1.746: BoundInStage at empty, after the generic vacuity

## HEAD

head_slot: coder
machine: shared
task: LJ-1.746
agda_tier: wide
pane caliber: GHCRTS=`-A64m -I0 -M2g`, set by the program; never touched here
verdict: **NO-GO stated.** The obligation does not land: the chain walls at
`runs/Amb4.agda.txt`, the erased-graph conjunction slot of `GraphAt`, and
three restructures still wall. The NO-GO statement is
`review-of-bound-in-stage-at-empty.md` in this directory. The named leaf
cure itself is GREEN: `runs/Amb7.agda` typechecks rc 0. The probe is named
`.agda.txt` because it cannot typecheck (Boundary rule); nothing in
`src/`; nothing committed.

## THE DELIVERABLE

- `agents/tasks/LJ-1-746/runs/Amb7.agda` — the brief's named rewrite,
  **rc 0** (`runs/amb7-746-1.out`, peak RSS 657 MB, fresh re-check
  rc 0 at the end of the dispatch). `StepKilledGen`
  (`runs/Amb7.agda:55`) is the critic's type
  (`agents/tasks/LJ-1-732/review-of-LJ-1-732-1.md:163-166`) named once,
  in the spelling LJ-1.745 measured green
  (`agents/tasks/LJ-1-745/Probe745.agda:64-76`): gamma as `Vec S 15`,
  the prose negation as its carrier `⟨ env ⊨ₚ App ⟩ → Empty.⊥`.
  `approx-part` (`runs/Amb7.agda:69-70`) is the domain row from the green
  732 `Amb5` plus the one-line instance call
  `Empty.rec (gen u v γ15 u∈ v∈ ant)`. No `PT.rec` sits at the instance;
  no numeral-bound motive is typed. W2 answered: the mathematics is
  written once at the generic hypothesis and instantiated.
- `agents/tasks/LJ-1-746/runs/EraseIrr.agda` — **rc 0** in 0.84 s
  (`runs/eraseirr-4.out`), a new lemma born of the wall:
  `erase-cong` (`runs/EraseIrr.agda:56`) proves
  `erase φ p ≡ erase φ q` by induction on φ, O(|φ|) cong steps. It is the
  machine form of the claim Amb2's 732 comment made at prose level; the
  tree had only `BoundedSubset.erase-Δ₀`
  (`src/L/BoundedSubset.lagda.md:825-837`), which transports Delta-0
  through ONE proof, never both. Green, and so far unused: the assembly it
  was built for walls for a second reason (below).
- `agents/tasks/LJ-1-746/Probe746.agda.txt` — the drafted probe, named
  `.agda.txt` because it cannot typecheck. It carries the full intended
  shape: the 673 At telescope as the module telescope
  (`Probe673.agda:57-61` order), `StepKilledGen` as the leading explicit
  binder of the obligation, the alias export at the file's top level, the
  bridge and pins consumed from the 732 frame, and the two scope fixes the
  committed 732 file needs (it never machine-checked: `Lset-cumul` /
  `ord∈Lset-suc` need `L.Ordinal.Stages`, `sucV` needs `InfinitySet`,
  neither is in the committed `Probe732.agda` import list). The obligation
  binder order is: At telescope, then `gen`, then
  `(ca cp : Code) → fst (val cp) ≡ ∅ → fst (val ca) ≡ Lset ∅ →
  BoundInStage ca cp`.
- `runs/Amb4.agda.txt`, `runs/Amb2.agda.txt` — the restructured chain
  modules in their best measured shapes; neither typechecks (the wall).
- `runs/B*.agda.txt`, `runs/*.out` — the bisection record, every number
  cited below.
- `review-of-bound-in-stage-at-empty.md` — the NO-GO statement.

Not inhabited, as the brief demands: `Completeness`,
`completeness-from-pack`. The 732 frame's `codes-exist` block was dropped
(no row of the obligation reads it; coder trim law, owner ruling
2026-08-23).

## MEASUREMENTS

All runs one Agda process at a time, pane caliber untouched, cold cone
warmed bottom-up per the LJ-1.745 cure (the cold cone here was fully
cold: no LJ-1-520/652/667/673 or 732-runs interfaces existed in this
worktree's `_build`).

| run | file | rc | what it prices |
|---|---|---|---|
| floor746.out | floor (full cone) attempt 1 | killed by my own 300 s window | cold cone: interfaces for P520/P652/P667/P673/Num/Amb1/Amb3/Amb5/Amb6/Amb7a/Amb2a/Amb4a all landed before the kill |
| amb7-746-1.out | `runs/Amb7.agda` | **0** | the named rewrite: peak RSS 657 MB |
| eraseirr-4.out | `runs/EraseIrr.agda` | **0** | the lemma, 0.84 s |
| amb4-746-3.out | `Amb4` direct term | **251, HEAP WALL** | **342.78 s**, `Heap exhausted` at the 2 g cap, peak RSS 2.4 GB |
| amb4-746-4.out | `Amb4` with erase-cong bridges | timeout >240 s | restructure 1: still walls |
| b1.out | `Amb4` type floor (term holed) | 42 expected | **6.05 s** — the type is cheap |
| b4.out | `Amb4` slots, both rows holed | 42 expected | **3.33 s** — the Sigma/and-structure is cheap |
| b7-3.out | bare `refl` between the two count-proof spellings | timeout >120 s | the proof spellings do not convert cheaply |
| b8.out / b10.out | isolated bridge (implicit / explicit implicits) | 42 `[UnsolvedMetaVariables]` | **48.94 s** / **48.99 s** — the unifier blocks on `_a + (countFo A.approxBndAt + _b) = 0` over the erased-graph tree |
| b5.out / b6.out | assembly, one bridge holed | timeout >180 s | restructure 2: still walls |
| b12.out | assembly with BOTH slots GIVEN at the split spellings | timeout >150 s | restructure 3: the slot comparison itself does not complete; no row-term trick avoids it |

W3 ANSWER: **NO.** The remaining chain does not land once `approx-part`
spends the generic lemma. The wall module is `Amb4`; the wall site is the
conversion of the erased-graph conjunction slots
(`CntS.erase Mx.G.graphBndAt countGB`, whose `graphBndAt` is
`src/L/Condensation.lagda.md:2493`) against any spelling of the rows.
By the same mechanism `Amb2`'s `matrix15` slot
(`CntS.erase Mx.matrix countMx` split three ways) is a larger instance of
the identical shape and was never reachable.

## WHY THE WALL IS NOT THE 732 WALL

The 732 wall was the `PT.rec` typed against the concrete instance; the
critic's cure removed it and the removal is green (`runs/Amb7.agda`). The
wall that remains is one level up and of a different kind: `erase`
threads its count proof through every clause
(`src/FOL/Count.lagda.md:598-610`), so the slots of the erased graph
carry plus-zero splits of `countGB` while the green row modules name
`countA` / `countS`, and every conversion between the two spellings
sends the unifier into count-normalization over the unfolded
`ApproxB`/`StepB` trees, where it blocks on plus-split equations and
grinds past the caliber. The heap cap is where it becomes visible
(342.78 s, 2.4 GB); B12 shows the comparison does not complete even with
the rows given.

## WHAT THE NEXT BRIEF NEEDS

- A shape in which no consumer spells a count-split term and no
  conversion descends into the erased-graph tree. Two candidates are
  priced in the review file: (1) `Amb1` names the split-spelled row
  types once, checked there, so slots and rows share one spelling;
  (2) head-depth decomposition of the graph reading into a written
  mirror Sigma type with a single head-level `refl` equality, keeping
  the conjunct formulas suspended. Both need one dispatch each; both
  reuse `runs/EraseIrr.agda`.
- `runs/Amb7.agda` and `runs/EraseIrr.agda` are green and importable:
  the next chain starts from them, not from the 732 runs.
- The heavy caliber would widen the cap but does not cure the unifier
  blocking; it needs the owner's tier ruling and is the last resort.
- The kill census: no watchdog kill of this task's processes. All
  timeouts were this agent's own bash windows; the one SIGKILL-class
  event was the heap exhaustion (`runs/amb4-746-3.out`), not a watchdog
  kill. Both watchdog logs' last kill remains 09:40:03, before this
  task's first run; `vm.swapusage` read 660 MB used throughout.

## WHAT THE SHAPE RESISTED

- The committed `Probe732.agda` frame never machine-checked: besides the
  known Amb2 chain wall, its import list is missing `L.Ordinal.Stages`
  (`Lset-cumul`, `ord∈Lset-suc`) and `InfinitySet` (`sucV`), both of
  which its own body names. My draft fixes both; a later GO should not
  clone the 732 imports blindly.
- The preamble of an Agda file cannot reference the module telescope's
  `{ℓ}` (measured: `[NotInScope]` at the `FOL.Count {ℓ = ...}`
  instantiation; same trap LJ-1.745 recorded). Instances of
  parameterized library modules are spelled in the body
  (`runs/EraseIrr.agda:36-40`).
- The bounded quantifiers `∃̇∈` / `∀̇∈` are plain two-argument names
  (`src/FOL/Syntax.lagda.md:100`), not mixfix with a trailing
  underscore; `cong₂ ∃̇∈` is the spelling that parses
  (`[NoParseForLHS]` measured, `runs/eraseirr-3.out`).

## RECORD FACTS

- Nothing in `src/` was written; nothing was committed or pushed.
- The floor discipline was applied: the floor files are in `runs/`
  (`Floor746.agda.txt`, `B1`/`B4`), the floor numbers are 6.05 s (type)
  and 3.33 s (structure); `Probe746`'s own floor was never reached
  because the chain walls at `Amb4` before it, so no frame-only number
  for the probe exists and none is claimed.
- Two sibling panes ran Agda during part of this dispatch
  (LJ-1.740-SPLIT, LJ-1.742-SPLIT); no process of mine overlapped with
  them beyond normal scheduling, and no watchdog kill fired during the
  task.
- The ratio bar does not fire on this task: the write scope holds no
  `src/` master and no fenced agda lines; the divisor is 0.

## THE ORDERED CHECKER OUTPUT

```
check-survey-quotes: LJ-1-746 clean (0 note(s), 0 defect(s))
```
(Run as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-746`;
this worktree has no `.venv`, so the main checkout's pinned interpreter
was used, the LJ-1.745 precedent.)

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** Line 35 carries DD25, the rule
  this NO-GO return is written under: "A NEGATIVE RETURN IS ADVERSARIALLY
  REVIEWED AT MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN READ
  TOGETHER" — hence `review-of-bound-in-stage-at-empty.md` beside this
  report. Line 30 carries DD18, the row that makes these two sections a
  duty rather than a hope: "THE ARCHIVE AND LITERATURE SURVEYS are
  sections of the brief and of the return, not a hope."
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read past its header:
  orchestrator dispatch mechanics do not bear on an Agda elaboration
  wall.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read: it announces
  itself as the construction registry as it stood on archival day; the
  live status is the screen the program injected.
- **`archive/dev/STATUS-archived.md` DECLINED.** Not read: a retired
  goal table of the superseded route; this task's goal comes from its
  brief.
- **`archive/dev/TASKS-archived.md` DECLINED.** Not read: no earlier
  dispatch's findings are cited here; every number above was measured
  this task at its own site.

## LITERATURE USED

- **`dev/literature/devlin-errata.md` DECLINED.** Not read beyond its
  header: the wall is an elaborator measurement, not a mathematics
  formula under test; no literature claim is quoted or corrected here.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read: no
  glossary term is proposed, questioned or used by this return.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read: nothing here
  cites a published source.
- **`dev/literature/primary-sources.md` DECLINED.** Not read: the probe
  is not a provability probe (DD28's trigger); its question was whether
  a chain elaborates at a caliber, settled by measurement.
- **`dev/literature/fine-structure.md` DECLINED.** Not read: fine
  structure plays no part in the count-proof splitting the wall lives
  in.

