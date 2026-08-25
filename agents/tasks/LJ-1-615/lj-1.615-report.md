# LJ-1.615 report: `value-is-L`, the second factor at today's carrier

## HEAD
head_slot: coder
machine: shared
verdict: STOP, AND IT IS THE STOP THE BRIEF FUNDED IN ADVANCE. The
recovered `ValueIsL` NEEDS `TransferL`: the factorization recovered by
`[LJ-1.611]` does not split into a paid factor and an unpaid one, and
row 3 is back in the unpaid direction. The stop is stated at
`agents/tasks/LJ-1-615/review-of-value-is-L.md`. The obligation name
`value-is-L` is ABSENT from the delivered probe on purpose, and the
meter reads it MISSING (`missing exit=42 ... [NotInScope]`,
`1 UNRESOLVED of 1`, `probe_red=False`, witness run 1.50 s). The probe
itself is GREEN and carries no hole (`runs/p-5-forced.out`, exit 0,
8.79 s, peak 581,648,384 bytes, final forced recheck of the delivered
file, its own `Checking` line).

Written as a skeleton before any Agda beyond W3 and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-615/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, ONE Agda process at a time. I did
not set `GHCRTS`. Nothing is postulated, the probe carries `--safe`,
the delivered file is green and carries no hole, and nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no ` ```agda `
fence, counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET ANYWHERE IN THIS TASK.** The highest peak of any
run is 581,648,384 bytes against the 2,147,483,648-byte cap
(`runs/p-5-forced.out`), and the longest run is 8.87 s against the caps
I set: 120 s for every W3 run (the brief's two-minute cap), 300 s for
every floor and probe run. macOS has no `timeout`; the cap is a `perl
alarm` wrapper and every `.out` carries `CAP=`. No run was killed and
no run printed a heap message.

## D-10, THE RECOVERY BEFORE ANY AGDA, AND IT TURNED TWICE

**THE FIRST RECOVERY WAS MINE AND IT WAS WRONG, AND THE REPORT ITSELF
SAYS WHY.** From `[LJ-1.611]`'s delivered evidence alone, the factor
reads as the INNER determination: the report gives the arrow
`ambientOnly-from : TransferL → ValueIsL → AmbientOnly`
(`agents/tasks/LJ-1-611/lj-1.611-report.md:197-199`), the review
describes `TransferL` as "the ambient-to-inner transfer of the graph
formula at `L`" and `ValueIsL` as "the value's constructibility"
(`agents/tasks/LJ-1-611/review-of-graph-ambient.md:90-92`), and an
arrow type underdetermines the split. That reading STATES, INHABITS,
and recomposes at today's carrier (all runs kept: `runs/w3-1.out`,
`runs/w3-2.out`, `runs/p-1.out`, `runs/p-2-forced.out`, all green). It
cannot be the factor: the report says "**Neither factor was delivered
there**" (`review-of-graph-ambient.md:92-93`), while the inner
`Lset-only` WAS delivered there ("the delivered inner `Lset-only`",
`agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:36-37`). A lemma
that was free cannot be the factor that was missing.

**THE C-42 SWEEP RECOVERED THE STATEMENT, FROM RECORDS AND NOT FROM
GIT.** No git history was read. The sweep (below) surfaced the retired
route's own task records, which quote the type literally and agree
five times over:

    ValueIsL = (v b : S) → IsOrd b
             → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
             → ⟨ isL v ⟩

at `agents/tasks/archive/L3-32-T51/l3.32-t51-report.md:55`,
`agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:20` ("The ambient
satisfaction's value is constructible. W1p's second factor"),
`agents/tasks/archive/L3-32-T130/l3.32-t130-report.md:69` ("ambient
satisfaction implies `isL v`"),
`agents/tasks/archive/L3-31-IVPROBE/l3.31-ivprobe-report.md:222` ("the
value named by an ambient satisfaction is constructible"), and the
blocker measurement at
`agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:38-39`. With `S`
the ambient carrier: **the second factor is the AMBIENT one, the
ambient satisfaction of the graph implies the VALUE is constructible.**
`[LJ-1.611]`'s words "the value's constructibility" were literal.

**THE TRUTH CHECK PASSES, AND THE STOP IS A SUPPLY STOP.** At the
adequate matrix the ambient determination is true classically (Devlin
5.2 (a), `dev/literature/devlin-II5.md:95-97`: `∀v∀γ [v = L_γ ↔ ∃z
Φ(z, v, γ)]` with `Φ` Σ₀), so `isL v` under the ambient reading of an
adequate graph is not refuted by a Tarskian obstruction. What is missing
is SUPPLY at the delivered matrix, and `[LJ-1.611]` had already
measured that `TransferL`'s truth there is open
(`agents/tasks/LJ-1-611/lj-1.611-report.md:321-322`). I claim the
target is NOT SUPPLIED, not that it is false.

## W3, THE WIDEST UNMEASURED TERM

**GO, AND THE TYPE IS CHEAP, IN BOTH SHAPES.** The delivered slice is
`agents/tasks/LJ-1-615/runs/W3.agda` (69 lines, 18 code lines), the
RECOVERED type, written before the delivered probe and typechecked
ALONE: `runs/w3-3.out` is **exit 0 at 1.83 s, peak 384,532,480 bytes**,
under the 120-second cap. The first shape (the inner determination,
later overturned) had also stated green: `runs/w3-1.out` exit 0 at
1.97 s and `runs/w3-2.out` exit 0 at 2.10 s, peak 375,848,960 bytes.
The brief estimated about 12 lines; the recovered type is 4 and the
slice that holds it is 18 code lines. The measurement moves the weight
where it belongs, exactly as `[LJ-1.611]` measured for face G-: the
STATEMENT costs under two seconds, and the weight is in the TERM,
because the term must consume an AMBIENT reading.

## THE STATEMENT AT TODAY'S CARRIER

`agents/tasks/LJ-1-615/Probe615.agda:131-134`, the W3 type letter for
letter (`runs/W3.agda:66-69`):

    ValueIsL = (v b : SV.S) → IsOrd b
             → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
             → ⟨ isL v ⟩

**WHAT CHANGED FROM THE RETIRED FORM: THE FORMULA, AND NOTHING ELSE.**
The retired type is quoted above with `S` the ambient carrier; today's
`SV.S` is the ambient carrier `𝒮ᵥ.S`, and the identification is forced,
not chosen: the satisfaction's environment sits at the STRUCTURE's
carrier (`src/FOL/Semantics.lagda.md:91`), so `⊨ᵛ` takes ambient
environments and `⊨ᵐ` takes class-carrier environments
(`src/FOL/Absoluteness.lagda.md:74-78`), exactly the discipline the
archived `TransferL` already shows with its `fst`-projected premise
(`agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:19`). `IsOrd`
and `isL` stand at the ambient carrier both then and now
(`src/L/Constructible.lagda.md:376-377`). What moved is the formula
UNDER the statement: the retired chapter's `LsetGraphAt` is gone with
its route (cut by D32, `dev/ARCHIVE.md:285`), and today's rebuilt graph
at the same slots is `src/L/Coding/Sequence.lagda.md:291-292` (opened
at `:349`; the arity-2 instance carries the name `LsetGraph`,
`:353-354`). Same slots, same role, different construction underneath.

## DOES IT NEED TransferL

**YES.** The hypothesis is the ambient reading at an arbitrary ambient
environment, whose every existential ranges over every ambient set
(`src/FOL/Semantics.lagda.md:96`; the graph's own outer binder is
unbounded, `src/L/Coding/Sequence.lagda.md:292`), and every delivered
road from there to the inner fact `isL v` is closed: the transfer
machine covers Δ₀/Σ₁/Π₁ only (`src/FOL/Absoluteness.lagda.md:80-121`),
the graph is none of the three (its approximation conjunct carries
unbounded universal quantifiers in the definition itself,
`src/L/Coding/Sequence.lagda.md:287-292`), the bounded restatement's
leaf adequacy is conditional on the certificate frame's site facts
(`src/L/Condensation.lagda.md:7216-7306`), and the determination lemma
is inner-only (`src/L/Hierarchy.lagda.md:333-335`). The site of the
need is the composition rebuilt green at
`agents/tasks/LJ-1-615/Probe615.agda:191-198`: the second factor's
whole job there is to carry the ambient VALUE into the class carrier so
the transfer can hand the inner environment to the free inner
determination, and the retired route measured the same thing at its own
site ("`ValueIsL` has the same single blocker",
`agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:38-39`). **Row 3's
second factor runs in the unpaid direction, and the factorization does
not split the way its author thought.**

## WHAT THE PROBE LANDS, ALL GREEN

| what | at `Probe615.agda` |
|---|---|
| the recovered `ValueIsL`, STATED, not inhabited | `:131-134` |
| `inner-determined`, the free lemma the first recovery mistook for the factor | `:147-150` |
| `ord-isL`, the composition's ordinal input, delivered today in two lines | `:162-163` |
| `TransferL`, the archived first factor's type, hypothesis only | `:181-184` |
| `AmbientOnly`, the archived conclusion type | `:186-189` |
| `ambientOnly-from`, the retired reduction rebuilt at today's carrier | `:191-198` |

The last item is the recovery CHECK under the correct reading: with
both factors as hypotheses the retired arrow typechecks at today's
carrier, the second factor's proof obligation inside it is exactly the
carrier bridge, and the free inner determination sits inside it as the
retired route used it ("proved through `Lset-only` and `ord-isL`",
`agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:21`). A wrong
recovery would not compose; mine of the first shape composed only
because I had chosen the split to make it compose, which is why that
green run was not evidence, and why the sweep's literal quotes decide.

## THE FLOOR, MEASURED BEFORE THE PROOF, AND IT EARNED ITS KEEP

Per the owner's ruling of 2026-08-23, `runs/FLOOR.agda` is the probe's
import list and frame with the obligation at ONE designed hole, run
before the proof. `runs/floor-1.out` priced the frame at **2.19 s,
peak 405,553,152 bytes, exit 42** and CAUGHT A REAL SHAPE ERROR before
any proof was attempted: the satisfaction's environment sits at the
structure's carrier, so my ambient-side types had been stated at the
wrong carrier (`[UnequalTerms]`, class carrier vs `V ℓ`). `runs/floor-2.out`
is the corrected shape at **2.35 s, peak 410,550,272 bytes**, exit 42
at the hole and nothing else. The delivered probe's own frame was then
priced by its green runs (8.79 s to 8.87 s): the heavy import is
`L.Hierarchy` for `Lset-only` plus `L.Ordinal.Stages` for
`ord∈Lset-suc`, and both were needed by rows that use them.

## PRICE

**EVERY NUMBER IS MINE, MEASURED UNDER `GHCRTS=[-A64m -I0 -M2g]`, ONE
AGDA PROCESS PER RUN.** Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^\s*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the delivered probe, whole | 198 | 47 | `Probe615.agda` |
| header and imports | 128 | 22 | `:1-128` |
| S1 the recovered type, stated | 15 | 4 | `:129-134` |
| S2 the free lemma | 18 | 4 | `:136-150` |
| S3 ord-isL | 15 | 2 | `:152-163` |
| S4 the factorization rebuilt | 34 | 10 | `:165-198` |
| W3 slice, delivered | 69 | 18 | `runs/W3.agda` |
| FLOOR slice | 169 | 31 | `runs/FLOOR.agda` |

| measurement | wall | peak RSS | basis |
|---|---:|---:|---|
| W3 recovered type, alone, exit 0 | 1.83 s | 384,532,480 | `runs/w3-3.out` |
| W3 first shape, alone, exit 0 | 1.97 s | not taken | `runs/w3-1.out` |
| W3 first shape, RSS capture, exit 0 | 2.10 s | 375,848,960 | `runs/w3-2.out` |
| floor, first shape, exit 42 (env-carrier catch) | 2.19 s | 405,553,152 | `runs/floor-1.out` |
| floor, corrected, exit 42 at the hole only | 2.35 s | 410,550,272 | `runs/floor-2.out` |
| probe first shape, first green | 2.83 s | 377,913,344 | `runs/p-1.out` |
| probe first shape, forced recheck | 2.31 s | 405,454,848 | `runs/p-2-forced.out` |
| delivered probe, green | 8.87 s | 580,616,192 | `runs/p-3.out` |
| delivered probe, forced recheck | 8.78 s | 580,648,960 | `runs/p-4-forced.out` |
| delivered probe, FINAL forced recheck | 8.79 s | 581,648,384 | `runs/p-5-forced.out` |
| witness meter, first shape, PASS (mid-task, wrong recovery) | 2.67 s | not taken | meter output, not kept |
| witness meter, delivered, MISSING as designed | 1.50 s | not taken | `1 UNRESOLVED of 1`, `probe_red=False` |

**THE ESTIMATE WAS ABOUT 170 LINES IN THE PROBE, ABOUT 45 FOR THE
OBLIGATION.** The delivered file is 198 lines and 47 code lines; the
obligation is ABSENT, and the six terms that price it are 20 code
lines. The estimate's stated uncertainty ("the statement is recovered
from a report quoting a retired file, and nobody has stated it at
today's carrier") is exactly where the task spent its turns: the
recovery took two shapes, and the first one was mine and wrong.

**NOTHING IN `runs/` IS UNEXPLAINED.** `w3-1`/`w3-2` (the first,
overturned recovery's type, green before and after RSS capture),
`w3-3` (the recovered type, green), `floor-1` (the floor run that
caught the env-carrier error), `floor-2` (the corrected floor, hole
only), `p-1`/`p-2-forced` (the first shape's probe, green and forced,
overturned by the sweep), `p-3`/`p-4-forced` (the delivered probe,
green and forced), `p-5-forced` (the delivered file after a comment-only
citation fix, green, its own `Checking` line). Every `.out` carries
`GHCRTS=`, `CAP=`, a start stamp, an end stamp and `EXIT=`.

## C-42, THE SWEEP

The shape swept for is "the second factor of the recovered
factorization". The command is `grep -rn "ValueIsL\|TransferL\|
ambientOnly-from\|AmbientOnly" agents/ src/ archive/` over records and
Agda. The `ValueIsL` sites:

| site | statement | at `file:line` |
|---|---|---|
| 1 | the recovery, description only | `agents/tasks/LJ-1-611/review-of-graph-ambient.md:90-92` |
| 2 | the recovery, report | `agents/tasks/LJ-1-611/lj-1.611-report.md:197-199` |
| 3 | the original factorization probe's statement | `agents/tasks/archive/L3-31-IVPROBE/l3.31-ivprobe-report.md:217-222` |
| 4 | the statements table | `agents/tasks/archive/L3-32-T51/l3.32-t51-report.md:53-55` |
| 5 | the blocker measurement | `agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:33-42` |
| 6 | the inventory with the retired proof line | `agents/tasks/archive/L3-32-T130/l3.32-t130-report.md:67-70` |
| 7 | the cut inventory | `agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:18-21` |
| 8 | today's restatement, stated not inhabited | `agents/tasks/LJ-1-615/Probe615.agda:131-134` |

**EIGHT SITES IN THE RECORDS, NOTHING IN `src/`, AND ONE IN GIT
HISTORY.** The ninth site is `3f5001e` itself, recoverable only by
`git show` (`dev/ARCHIVE.md:285`) and NOT read, per the brief. The
sweep is what overturned my first recovery, which is C-42 working as
ruled: the refutation of a wrong reading came from counting the sites
that carry the shape, before any cure was priced.

## W2, THE GENERIC CARRIER

**The mathematics is written once, at the tree's own carriers, and
nothing needed a second instantiation.** The probe is generic in `ℓ`;
the statement sits at the ambient carrier `SV.S` and the class carrier
`AbsL.SM`, both the tree's own, and the composition moves between them
by pairing, not by restating. No deadline forced a fixed form; there is
no conflict to report.

## W4

Not applicable. No module was retired, nothing under `src/` changed,
and `dev/ARCHIVE.md` takes no row from this task. The row this task
READ is `dev/ARCHIVE.md:285`, already present.

## WHAT THE SHAPE RESISTED

- **What it cost.** 47 code lines for a green probe that states the
  recovered factor, lands the free lemma, the ordinal input and the
  rebuilt factorization, and prices the stop; 8.79 s and 581,648,384
  bytes at the final forced recheck, and no heap event at any point.
- **What the shape resisted.** Not the type: both shapes stated green
  under two seconds. The resistance was the RECOVERY: the report's
  evidence underdetermines the factorization's split, my first reading
  was wrong, and the sweep's five literal quotes were needed to decide
  it. The floor run also caught a real env-carrier error in my own
  Section 3 before any proof existed, which is the 2026-08-23 ruling
  earning its keep at this site.
- **What I had to weaken.** Nothing. The stop is stated at full
  strength: the recovered factor needs the ambient-to-inner move.
- **What I could not close.** `value-is-L` itself: every road from the
  ambient hypothesis to `isL v` passes through the ambient-to-inner
  move, and that is the finding, not a failure to finish.

## WHAT THE NEXT BRIEF NEEDS

1. **THE FACTORIZATION DOES NOT SPLIT PAID FROM UNPAID.** Both factors
   of `ambientOnly-from` need the ambient-to-inner move. The honest
   residue on row 3 is ONE obligation, the ambient determination of the
   graph, which is `[LJ-1.611]`'s `Honest-G-` from the class-carrier
   side (`agents/tasks/LJ-1-611/Probe611.agda:175-177`). A dispatch on
   the second factor as the cheap half should not be written again.
2. **THE REBUILT REDUCTION IS NOW IN THE TREE, AT TODAY'S CARRIER.**
   `Probe615.agda:191-198` is the retired `ambientOnly-from` with both
   factors as hypotheses, green. Any future supplier of either factor
   composes with it directly; the shape it expects is the archived
   shape (`T144:18-20`), and `ord-isL` is delivered at
   `Probe615.agda:162-163`.
3. **THE PREMISE TABLE HAS ONE UNVERIFIABLE ROW.** Premise 10 names
   `archive/dev/LJ-dispatch-index.md:212` as the basis for
   `[LJ-1.607]`'s "recorded cure with no surviving code"; that line is
   the `LJ-1.136` row and says nothing of the sort, and `LJ-1.607`
   appears nowhere in that index. The instruction the premise carries
   (do not dig in git history) was followed regardless, because the
   brief states it directly. The mathematician should re-source that
   premise or drop it.
4. **IF THE OWNER WANTS THE AMBIENT DETERMINATION FUNDED, THE ROADS
   ARE STILL `[LJ-1.611]`'s THREE.** Transfer (this task's finding adds:
   it must also carry the VALUE into the class carrier or pair with a
   `ValueIsL` supplier), the bounded certificate road
   (`src/L/Condensation.lagda.md:7216-7306`), or the direct ambient
   leaf. Which road is not my call.

## SCOPE

I wrote only inside `agents/tasks/LJ-1-615/`:
`Probe615.agda`, `runs/W3.agda`, `runs/FLOOR.agda`, `runs/*.out`,
`lj-1.615-report.md`, `review-of-value-is-L.md`. Gates run:
`check-probes.py --check` clean (7831 tracked files), `lint-agda.py
--check` exit 0, `check-fences.py --check` clean (102 masters). The
witness meter returns `missing exit=42`, `1 UNRESOLVED of 1`,
`probe_red=False` (1.50 s), by design. I did not run `make check`: I
commit nothing. No commit, no push. `git status` shows only
`agents/tasks/LJ-1-615/` untracked; nothing in `src/` moved.

## ARCHIVE USED

- `dev/ARCHIVE.md`: **READ, one row.** `:285` is the `L.Condensation`
  partial-retirement row; its note reads "The Crossing section stated
  the ambient-reading form of `Lset-only` at the class carrier. It
  factored that form into `TransferL` and `ValueIsL`. It proved the
  factorization in `ambientOnly-from`." TOOK the locator only: the
  retired section is in git history at `3f5001e`, which this task did
  NOT read, per the brief.
- `archive/dev/LJ-dispatch-index.md`: **READ, one line, and it
  REFUTED a premise.** `:212` reads `| LJ-1.136 | Gate the remaining
  A-prime blocks | GO, BOTH PROBES | pick-canonical elaborates, so
  LJ-1.114's wall falls. A5's risk is seconds, not lines: 2.594 s per
  line |`. Premise 10 names this line as `[LJ-1.607]`'s basis; the
  line is `LJ-1.136`'s row, and `LJ-1.607` appears nowhere in the
  index. Reported in `## WHAT THE NEXT BRIEF NEEDS`, item 3.
- `archive/dev/JOURNAL-archived.md`: **declined, not read beyond its
  first line.** `:1` reads `# Archived journal: the retired route`. A
  history; the recovery's evidence is the archived TASK REPORTS the
  sweep surfaced, which quote the statements themselves.
- `archive/dev/JOURNAL.md`: **declined, not read beyond its first
  line.** `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- `archive/dev/DECISIONS-archived.md`: **READ, one row.** `:52` is the
  D32 row; it reads `| D32 | Arm B is severed by deletion; the
  internalization rebuild is deferred to the GCH resume, comprehensively
  documented | **RULED 2026-08-07 by the owner**, on the full gate
  chain: `[T129]` (the re-home IS the cone), `[T130]` (no rud-side
  escape)`. TOOK the ruling date and the deferral only; the cut's
  content is `dev/ARCHIVE.md:285`, its named home.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ, the (a) half.** `:95-97`
  reads

      > By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that
      > (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

  TOOK it as the D-10 truth check, as `[LJ-1.611]` did before me: the
  ambient determination is true at the adequate matrix, so the stop is
  a supply stop and not a truth stop.
- `dev/literature/digest.md`: **not used.** `:1` reads `# Digest: the
  orthodox form of the rud route, pinned from the collected
  literature`; the recovery came from the archived task records, which
  quote the retired statements directly, and the digest adds nothing
  they lack.
- `dev/literature/truncation-and-selection.md`: **not used.** `:1`
  reads `# Truncation and selection: how the two literatures pick a
  witness`; this task truncates nothing and selects no least witness.
- `dev/literature/level-formula-slot-roles.md`: **not used.** `:1`
  reads `# The level-hood formula: arity, what it binds, what stays
  free`; the factor's slots are fixed by the archived quotes and by
  today's `LsetGraph` (`src/L/Coding/Sequence.lagda.md:353-354`), so
  no slot arithmetic was owed.
- `dev/literature/geology.md`: **not used.** `:1` reads `# Geology
  dossier: set-theoretic geology sources and the five questions`;
  geology has no bearing on the ambient decode at the class carrier.
