# LJ-1.268 report: the landing order for Route A-prime

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. Recon only. No
Agda ran. No master, brief or report was edited. No commit, no push. Written
incrementally (C-22).

Every negative is marked MEASURED (read at the cited line) or INFERRED (my
judgement). ASD-STE100 applies to this report.

## 0. LEAD: THE ORDER

**An order exists. Every block has a home. Five new masters. Nothing extends
an existing master, so no over-the-bar master gains a line.**

The seven-block order, at block granularity: **A2 and A1 first, in parallel.
Then A3 and A4 and A5, after A2. Then A7, after A4. Then A6, after A2 and
a re-site.** A5's rows split; the detail is below.

The order is a partial order, not one sequence. Three waves, each with
parallel work. Nothing forces one sequence.

```
Wave 0 (land now, in parallel, every import delivered):
  A2  -> src/L/Coding/Injection.lagda.md   (new)
  A1  -> src/L/Cardinal.lagda.md           (new)
  A5 row 5 (pairω) -> src/L/InjChain.lagda.md (new)

Wave 1 (after A2, in parallel with each other):
  A3  -> src/L/Cardinal.lagda.md
  A4  -> src/L/Cardinal.lagda.md
  A5 row 1 (composition) -> src/L/InjChain.lagda.md

Wave 2 (after A4):
  A7  -> src/L/GCH.lagda.md                (new)

Wave 3 (after A2, after a re-site):
  A5 row 3 (inclusion) -> src/L/InjChain.lagda.md
  A6  -> src/L/Absorption.lagda.md         (new)
```

A5 is one block whose rows split across three waves. Row 5 is independent.
Row 1 needs A2. Row 3 needs a re-sited probe before it lands. Section 1
names each row.

**Why five new masters and no extension.** Every block's object is absent
from `src/` today. MEASURED by my own grep: `injAt`, `LeastCardInj`,
`GCHStatement`, `IsCardinalL` each return zero hits over `src/` (excluding
the catalog). The blocks CONSUME existing masters and do not EXTEND them.
MEASURED by reading each probe's import block. The consequence for the bar:
the wing's 60.0 s gap is measured over the existing 11,926 lines. New
masters do not change that denominator. The new masters' rates are measured
fresh at landing, and no over-the-bar Condensation master grows.

**The one correction the brief needs, before anything lands.** Two probes
are stale today, not one. The brief names only A5's row 3. A6's probe is
also stale. Both fail on the same import. Section 2 gives the evidence.

## 1. ONE SECTION PER BLOCK

### A2 (186 lines)

- **Home master.** NEW `src/L/Coding/Injection.lagda.md`.
- **Why.** A2 is the coding-layer injection vocabulary: `injAt` and its two
  adequacy directions, `ranAt` mirroring `domAt`, the range set built by
  `hasReplacementL`, and the readback (`Extract`, `Small`). The atoms
  (`appAt`, `svAt`, `domAt`, `prAtL`) live in `L.Coding.Model`. The range
  set needs `hasReplacementL` from `L.Axioms.Full`. MEASURED that `L.Coding.Model`
  does not import `L.Axioms.Full` (`src/L/Coding/Model.lagda.md:52` imports
  only `L.Axioms.Numerals`). So A2 sits above Full. The formula parts alone
  (`injAt`, `ranAt`) could extend Model, but the range set and readback cannot.
  One new master keeps the 186-line block whole.
- **Undelivered imports.** NONE. MEASURED. Every import of
  `ProbeLJ1229A.agda` is a delivered master: `FOL.ZFStructure`, `FOL.Syntax`,
  `FOL.Absoluteness`, `FOL.ZFModel`, `V.Hierarchy`, `V.Coding`,
  `L.Constructible`, `L.Coding.Model`, `L.Axioms.Full`, `V.Presentation`.
- **`Everything.lagda.md` line.** `import L.Coding.Injection`
- **Bar side.** NEW master, no rate today. It grows no existing master.
- **The re-run (C-45).** A2 is a device parameterized by a graph `(F D)` and
  hypotheses `sv`, `dm`, `ij`, `ran`. It is not a closed theorem. Its supply
  is discharged when A5 or A6 instantiate it at a real graph. The first
  re-run is A3 or A4 importing `injAt` from the landed A2 master, with their
  local copy deleted.

### A1 (54 lines)

- **Home master.** NEW `src/L/Cardinal.lagda.md` (shared with A3 and A4).
- **Why.** A1 restates the ambient `LeastCardInj` over the L-carrier. It is
  the least-cardinal theorem in its ambient-injection form. A3 is the same
  object in its internal-code form, A4 in its cardinal form. One master
  holds the three faces. This grouping is INFERRED (a placement decision).
- **Undelivered imports.** NONE. MEASURED. Every import is delivered:
  `L.Ordinal.SquareLaw`, `L.Ordinal`, `L.Constructible`, `L.Ordinal.Stages`,
  `V.Hierarchy`, `V.Model`, `V.Presentation`, `FOL.ZFStructure`,
  `L.WellOrder.Base`.
- **`Everything.lagda.md` line.** `import L.Cardinal`
- **Bar side.** NEW master, no rate today.
- **The re-run.** None against an A-block; A1 imports no other block. Its
  own C-38 guard (`Atω`) already instantiates the lift at a real ordinal.

### A3 (26 lines)

- **Home master.** NEW `src/L/Cardinal.lagda.md`.
- **Why.** The canonical selection: `leastOf (orderAt β oβ)` over the bare
  graph atoms, with β from `stageBound`. It is the selection step of the
  least-cardinal family.
- **Undelivered imports.** A2's `injAt` (copied as S1 in the probe,
  `ProbeLJ1232A3.agda`). MEASURED. Everything else is delivered
  (`L.Choice.Stage`, `L.Choice.Step`, `L.WellOrder.Base`, `L.Coding.Model`).
- **`Everything.lagda.md` line.** `import L.Cardinal`
- **Bar side.** NEW master, no rate today.
- **The re-run.** `ProbeLJ1232A3.agda` minus its local `injAt`, importing
  `injAt` from `L.Coding.Injection`.

### A4 (43 lines)

- **Home master.** NEW `src/L/Cardinal.lagda.md`.
- **Why.** `InjCode`, `IsCardinalL`, `InternalLeastCard`. The internal
  cardinal and the internal least-of. The same family as A1 and A3.
- **Undelivered imports.** A2's `injAt` (copied as S1 in
  `ProbeLJ1236A4.agda`). MEASURED. The nonempty witness (A2's `lid`) is an
  OPEN HYPOTHESIS, stated as a parameter, so it does not block the landing;
  A5 supplies it later.
- **`Everything.lagda.md` line.** `import L.Cardinal`
- **Bar side.** NEW master, no rate today.
- **The re-run.** `ProbeLJ1236A4.agda` minus its local `injAt`, importing
  from `L.Coding.Injection`.
- **Correction to the brief.** The brief's abort criterion calls A4 "a
  MINIMAL CORE". That gap DISSOLVED. MEASURED: `[LJ-1.253]` section 1 closed
  it. The object-language `IsCardinal` formula is not owed because the
  trophy is metatheoretic, and `IsCardinalL` is already in the probe. A4's
  43 lines stand complete (about 32 in a master, after dropping the 11-line
  probe-only `Atω` guard).

### A5 (348 lines)

- **Home master.** NEW `src/L/InjChain.lagda.md`.
- **Why.** The five internalized injections the square-law chain consumes:
  composition (row 1), CSB (row 2, dissolved), inclusion (row 3), column
  square (row 4, dissolved), `pairω` (row 5), plus the shared `StageBound`.
  One master holds the rows so that one carve body serves several rows.
  `[LJ-1.176]` section 5.2 measured that sharing saves about 78 lines if two
  rows share it. The saving is optional and unmeasured today (INFERRED).
- **Undelivered imports.** Rows 1 and 3 need A2's `injAt`, `Extract`,
  `Small`. MEASURED. Row 5 needs none (delivered `L.Ordinal.SquareLaw`
  only). `StageBound` needs none.
- **`Everything.lagda.md` line.** `import L.InjChain`
- **Bar side.** NEW master, no rate today.
- **Row split.** Row 5 (60) is green and independent; it lands in wave 0.
  Row 1 (160) is green (`ProbeLJ1264A.agda` re-derived it) and needs A2; it
  lands in wave 1. Row 3 (112) is NOT landable; see section 2.
- **The re-run.** `ProbeLJ1264A.agda` minus its inlined `injAt`/`Extract`/
  `Small`/`Concrete`, importing from `L.Coding.Injection`.

### A6 (399 lines)

- **Home master.** NEW `src/L/Absorption.lagda.md`.
- **Why.** The successor absorption (`ShiftAbs`/`Shiftω`) built into L. One
  object, one master.
- **Undelivered imports.** A2's `injAt`, `injAt-in`, `module Small`.
  MEASURED: `ProbeLJ1217A.agda:239` imports them.
- **`Everything.lagda.md` line.** `import L.Absorption`
- **Bar side.** NEW master, no rate today.
- **NOT landable today.** See section 2.
- **The re-run.** `ProbeLJ1217A.agda` minus its `ProbeLJ1134A` import,
  importing `injAt` and `Small` from `L.Coding.Injection`.

### A7 (33 lines)

- **Home master.** NEW `src/L/GCH.lagda.md`.
- **Why.** The trophy statement. It will also hold the proof later. One
  master is the root chapter of the GCH proof, as `L.Model` is the root
  chapter of `L ⊨ ZFC`.
- **Undelivered imports.** A2's `injAt` (S0 in the probe) and A4's `InjCode`
  and `IsCardinalL` (S1, S2). MEASURED. A7 does NOT import A5 or A6:
  `SqShape` and `AbsorbsShape` are written as hypotheses, not imported.
  So A7 lands after A4 and before A5 or A6.
- **`Everything.lagda.md` line.** `import L.GCH`
- **Bar side.** NEW master, no rate today.
- **The re-run.** `ProbeLJ1236A7.agda` minus its local `injAt`/`InjCode`/
  `IsCardinalL`, importing from `L.Coding.Injection` and `L.Cardinal`.

## 2. THE BLOCKS THAT CANNOT LAND YET

Two sub-blocks are not landable. The brief names one. My check found the
second. Both fail on the same stale import.

**A5 row 3 (inclusion, 112 lines).** MEASURED. Its only probe,
`agents/tasks/LJ-1-176/ProbeLJ1176A.agda`, imports `open import ProbeLJ1134A`
at `:73`. That module no longer resolves: `ProbeLJ1134A.agda` now lives only
at `agents/tasks/LJ-1-134/ProbeLJ1134A.agda` (MEASURED by `find`), and
`[LJ-1.264]` section 3 measured the exact failure, `[FileNotFound] Failed to
find source of module ProbeLJ1134A`. What it needs: a re-sited probe that
inlines `injAt`/`Extract`/`Small` or imports them from the landed A2 master.

**A6 (399 lines).** MEASURED, and this is new against the brief. Its only
probe, `agents/tasks/LJ-1-217/ProbeLJ1217A.agda`, imports
`open import ProbeLJ1134A` at `:239`. Same failure, same cause. The brief's
goal says "Every block exists as a GREEN PROBE"; that is FALSE for A6 today.
What it needs: the same re-site.

**A4 is landable.** The brief's abort criterion calls it a minimal core.
That is superseded. MEASURED: `[LJ-1.253]` section 1 dissolved the gap.
A4 needs only A2's `injAt` before it lands.

**No block has no home.** Every block, landable or not, has a named master.

## 3. DD4 PER BLOCK, WITH THE AXIS NAMED

**The axis is Def against J** (`dev/literature/devlin-II5.md:375`, `:387-389`):
the per-tower content is exactly two objects, the level-hood certificate and
the definable well-order. `[LJ-1.262]` section 7 fixed that this axis is
different from the port's L-against-ambient axis. A block marked tower-neutral
on the Def-vs-J axis re-instantiates for the J tower; a block marked per-tower
does not pretend to.

| block | tower class | axis named | where it lands on that basis |
|---|---|---|---|
| A1 | PER-TOWER | Def vs J (level-hood certificate, object 1) | `L.Cardinal`, L-specific, no pretence of neutrality |
| A2 | TOWER-NEUTRAL | Def vs J (coding layer, neither object) | `L.Coding.Injection`, shared, J re-instantiates |
| A3 | PER-TOWER | Def vs J (definable well-order, object 2) | `L.Cardinal`, L-specific |
| A4 | PER-TOWER | Def vs J (well-order applied to cardinality) | `L.Cardinal`, L-specific |
| A5 | MIXED, OPEN | Def vs J | `L.InjChain`, generic bodies + L instantiation modules |
| A6 | 85 pc neutral, 15 pc per-tower | Def vs J | `L.Absorption`, Part 5 is the per-tower instantiation |
| A7 | TOWER-NEUTRAL | Def vs J (the statement) | `L.GCH`, shared by both towers for free |

The A5 row is OPEN as a block, MEASURED from `[LJ-1.247]` section 6. Its
parts carry partial verdicts: `pairω` (60) and composition (160) are
tower-neutral in shape modulo two parameterized names; the inclusion is 81
percent generic; `StageBound` is the shared bound device. A5's per-tower
share is the L instantiation sites alone.

A7's tower-neutrality is measured: `GCHStatement : isZFModel → Type` takes
the model as a parameter and names `S`, `∈ˢ`, `IsCardinalL`, `↪`; no `isL`,
no `Lset`, no `orderAt` (`ProbeLJ1236A7.agda:147`, `:103-106`).

## 4. THE ABORT CRITERION, ANSWERED

The criterion was fixed before the run (D-1). The first branch fires.

- **AN ORDER EXISTS AND EVERY BLOCK HAS A HOME.** Given. STOP.
- **A BLOCK HAS NO HOME.** None. Every block has a named master.
- **THE ORDER IS FORCED TO ONE SEQUENCE.** NO. It is a partial order of
  three waves with parallel work. Nothing forces one sequence.
- **A BLOCK CANNOT LAND AT ALL YET.** Two sub-blocks: A5 row 3 and A6,
  both with stale probes. Section 2 names them and what each needs.

## 5. ARCHIVE USED (DD18)

One line read per archived file.

- **`agents/tasks/LJ-1-253/lj-1.253-report.md`, read WHOLE.** TAKEN: A4's
  gap dissolves at section 1; the seven blocks sum to 1,089.
- **`agents/tasks/LJ-1-248/lj-1.248-report.md`, read WHOLE.** TAKEN: the
  tower table at section 4, which is the DD4 basis of section 3 here.
- **`agents/tasks/LJ-1-218/lj-1.218-report.md`, read WHOLE.** TAKEN: the
  per-master seconds table at section 1; the four Condensation masters are
  over the bar, the other eight are under it together.
- **`agents/tasks/LJ-1-236/lj-1.236-report.md`, read WHOLE.** TAKEN: A4 =
  43 and A7 = 47 at section 2 and section 4; the A5/A6 audit at section 1.
- **`agents/tasks/LJ-1-232/lj-1.232-report.md`, read WHOLE.** TAKEN: A1 =
  54 and A3 = 26, and A1's three delivered L-lemmas at section 3.
- **`agents/tasks/LJ-1-229/lj-1.229-report.md`, read WHOLE.** TAKEN: A2 =
  186 and the description-plus-adequacy split at section 3.
- **`agents/tasks/LJ-1-217/lj-1.217-report.md`, read WHOLE.** TAKEN: A6 =
  446 and the 296 charge at section 3; the direct shape at section 2.
- **`agents/tasks/LJ-1-234/lj-1.234-report.md`, read WHOLE.** TAKEN: `pairω`
  at 60 lines and tower-neutral, section 2 and section 4.
- **`agents/tasks/LJ-1-264/lj-1.264-report.md`, read WHOLE.** TAKEN: row 1
  re-derived at 160, section 3; the stale-import finding at section 3.
- **`agents/tasks/LJ-1-263/lj-1.263-report.md`, read WHOLE.** TAKEN: the
  re-run discipline at section 3, which is the template for section 1's
  re-runs.
- **`agents/tasks/LJ-1-262/lj-1.262-report.md`, read WHOLE.** TAKEN: the two
  axes at section 7, which fix the DD4 axis of section 3 here.
- **`agents/tasks/LJ-1-247/lj-1.247-report.md`, read WHOLE.** TAKEN: A5 =
  348 with the row table at section 5, and A5's OPEN tower status at section 6.
- **`agents/tasks/LJ-1-176/lj-1.176-report.md`, read WHOLE.** TAKEN: row 3
  (the inclusion) at 112 lines, section 5; the shared-carve note at section 5.2.
- **`src/Everything.lagda.md`, read.** TAKEN the wiring shape: an
  `import L.X` line inside the catalog fence. Not edited.
- **`archive/dev/TASKS-archived.md:10`.** TAKEN: "The 264 rows below record
  every dispatch made on the retired route". SHAPE ONLY.
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:536-537`.**
  TAKEN, SHAPE ONLY: the retired route held the internal predicates
  (`eqFo`, `cardFo`, `succCardFo`) in one master. **WHAT WOULD NOT TRANSFER:**
  the retired `cardFo` is the BIJECTION form; A-prime's `IsCardinalL` is the
  INJECTION form, so the archive's body does not transfer, only the
  one-master shape.
- **`archive/src/2026-08-09-rud-route/Everything.lagda.md:431-468`.**
  TAKEN, SHAPE ONLY: `import L.CardinalPredicates`, `import L.PairAtoms`,
  `import L.Cardinal`, `import L.CardinalCount` are separate wiring lines.
  The retired route's file layout is a SHAPE, not a claim, and its module
  names do not transfer to the seven-block split.

## 6. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md:365-395`, read directly.** TAKEN: the
  twelve-row step table (A, B, C1 to C6, D, E, F, G) and the verdict at
  `:387-389`.

**Does the literature suggest a file layout for II.5's twelve rows?** NO.
It states a mathematical step table with one grouping hint: per-tower versus
either-tower. MEASURED as the absence of any file or module boundary in the
source. The file layout is purely an engineering choice, and this report
makes it on the dependency graph and the bar, not on the literature.

## 7. THE NEGATIVES, CLASSIFIED

- **MEASURED. The four objects are absent from `src/`.** My own grep:
  `injAt`, `LeastCardInj`, `GCHStatement`, `IsCardinalL` each zero hits.
- **MEASURED. A2 imports only delivered masters.** Read from the probe.
- **MEASURED. A1 imports only delivered masters.** Read from the probe.
- **MEASURED. `L.Coding.Model` does not import `L.Axioms.Full`.**
  `src/L/Coding/Model.lagda.md:52`.
- **MEASURED. A6's probe is stale.** `ProbeLJ1217A.agda:239` imports
  `ProbeLJ1134A`; the file no longer resolves.
- **MEASURED. A5 row 3's probe is stale.** `ProbeLJ1176A.agda:73`, same
  import.
- **MEASURED. `ProbeLJ1134A.agda` lives only under `agents/tasks/LJ-1-134/`.** By `find`.
- **MEASURED. A4's gap dissolved.** `[LJ-1.253]` section 1.
- **MEASURED. A7 does not import A5 or A6.** `SqShape` and `AbsorbsShape`
  are hypothesis types in the probe.
- **MEASURED. A5's tower status is OPEN.** `[LJ-1.247]` section 6.
- **INFERRED. All seven blocks land in new masters.** A placement decision,
  not a measurement.
- **INFERRED. A1, A3, A4 share one master.** A placement decision.
- **INFERRED. A5 and A6 stay separate masters, with a shareable carve noted.**
  A placement decision; the share is unmeasured.

## 8. WORKING TREE, AS MY REPORT DESCRIBES IT

One file written: `agents/tasks/LJ-1-268/lj-1.268-report.md`, this file. No
master edited. No brief or report edited. No probe written. No Agda process
ran. No commit, no push, no `git checkout .`, stash, reset or clean. The
siblings' directories `agents/tasks/LJ-1-266/` and `agents/tasks/LJ-1-267/`
were not touched.

`scripts/lint-prose.py --check` runs on this report and exits 0.
