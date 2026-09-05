# LJ-1.743 report: `Lset-trans-set`, the name the meter reads

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.743
obligation: agents/tasks/LJ-1-743/Probe743.agda::Lset-trans-set
verdict: **GO.** The 725-SPLIT-inhabited term converts in a fresh file
at its own top-level name. `Lset-trans-set` is stated and INHABITED in
`Probe743.agda`, exported at the file's top level; the verdict run
p-2-verdict is EXIT=0 on the delivered bytes. The delivered term block
is byte-identical to `agents/tasks/LJ-1-725-SPLIT/Probe725Split.agda:71-79`
(diff measured, not asserted). No postulate stands anywhere, the probe
carries `--safe` and no hole, nothing lands in `src/`, and `stage-read`
appears in no code line of the file. The obligation the live meter
reads now has supply.

## 0. THE PREDECESSOR QUESTION

The predecessor is `[LJ-1.725-SPLIT]`. Its report verdict is GO on the
inhabited term and STOP, STATED on the separate type `stage-read`
(agents/tasks/LJ-1-725-SPLIT/lj-1.725-SPLIT-report.md:12). The coder
clause that stops on a NO-GO predecessor does not fire: nothing this
brief buys was the subject of a NO-GO. The type is taken from the
probe bytes that typechecked, not from the report's prose:
Probe725Split.agda:71 is the first line of the inhabited block, and
the block runs to line 79. The four brief premises each verified at
dispatch:

1. 725-SPLIT inhabited `Lset-trans-set` and its meter closed on the
   TYPE `stage-read` (lj-1.725-SPLIT-report.md:12).
2. The term is the block at Probe725Split.agda:71, over `Lset-out`,
   `𝒟ₒ∋⊆` and `Lset-mono`.
3. `[LJ-1.734]` is the export precedent: the name sits at the fresh
   file's top level, and a nested or sibling name is not the meter
   name (lj-1.734-report.md:10).
4. `stage-read` is NOT stated or inhabited here
   (lj-1.725-SPLIT-report.md:9).

## 1. WHAT WAS BUILT

One file, `agents/tasks/LJ-1-743/Probe743.agda`: the 725-SPLIT term,
transcribed, and nothing else.

- `Lset-trans-set`, stated and inhabited at the file's top level,
  signature and body byte-identical to Probe725Split.agda:71-79. The
  content is one `PT.rec` over the landed `Lset-out`, closed by the
  landed operator refinement `𝒟ₒ∋⊆` and monotonicity `Lset-mono`.
- The import cone is TRIMMED against 725-SPLIT's frame. That file
  carried `Base.Truth`, `Base.Classical` (a `LEM` parameter),
  `FOL.Syntax`, `FOL.Manipulation.Relativize`, `Cubical.Data.FinData`,
  `L.Ordinal`, `L.Ordinal.Stages`, `L.Axioms.Basic` and
  `L.Coding.Sequence`. All of them served `stage-read`'s type and the
  `ord-in-Lset` section; none is used by this term. The fresh file
  imports only `Base.Prelude`, `V` from
  `Cubical.HITs.CumulativeHierarchy.Base`, `module hPropStructure`
  over `𝒮ᵥ`, `PT` qualified, and the five `L.Constructible` names.
- No iterate is transcribed. The two-step iterate the spine consumes
  is two applications of this name (725-SPLIT's `Lset-trans-set²`,
  Probe725Split.agda:84-88), so restating it here would duplicate
  content the predecessor already carries. The brief ordered ONE term.
- `stage-read` appears in comments only (lines 17, 18, 28). No
  postulate stands in for it and no weaker form is inhabited under
  any name.
- `review-of-Lset-trans-set.md` is deliberately UNWRITTEN. The
  verdict is GO, no stop is stated, and the 734 precedent writes no
  review file on a GO (agents/tasks/LJ-1-734/ contains none). The
  brief's scope made the file available for a stop that did not
  happen.

## 2. THE FLOOR AND THE RUNS

The floor was priced before the proof, per the heavy-object rule, on
the SAME file with a hole standing in for the body. The floor run is
also the trim check: its only complaint is the interaction meta at
Probe743.agda:59, so the trimmed import cone elaborates clean and
every trimmed import was genuinely unused. The verdict run followed on
the delivered bytes. No failing run was ever repeated unchanged: the
two runs have different shapes (hole, then body). No heap wall was
met at any point and the 1800 s cap was never in play.

| run | wall | peak | note |
|---|---|---|---|
| f-1-floor | 0.84 s | 268,681,216 B | EXIT=42, hole in the body; only defect is the unsolved interaction meta at line 59. Prices the trimmed frame. |
| p-2-verdict | **0.83 s** | **268,173,312 B** | **EXIT=0, green, delivered bytes** |

Both runs carry `GHCRTS=[-A64m -I0 -M2g]` in their .out headers. The
peak is 12.5 percent of the 2,147,483,648-byte wide cap. The verdict
run was warm relative to f-1 (16 s later, interfaces cached), and each
number reported is the number its run measured. Against 725-SPLIT's
same-site verdict run (1.77 s, 374,603,776 B, its p-8), the trimmed
frame is about half the wall and 106,430,464 B less peak at the same
caliber; the two runs are days apart, so the comparison indicates the
trim, it does not price it.

## 3. W3 ANSWER

The brief's W3: whether the transcribed alias still converts in a
fresh file, estimated 20 to 90 lines. Answer: **YES, and the estimate
was generous.** The file is 65 total lines, 59 non-blank, raw `.agda`
(in-fence count 0, the ratio bar cannot fire). The term block needed
zero edits: the diff against Probe725Split.agda:71-79 is empty, and
the only edit the fresh file demanded was the module line. The
conversion cost less than the estimate because the cost was all in
the FRAME, and the trim removed the frame the term never used.

## 4. W2 ANSWER

The term is generic as delivered: `γ`, `a` and `x` are universally
quantified, no carrier is fixed, and no sibling proof is duplicated.
The transcription duplicated no content across files: the iterate is
cited at its predecessor site instead of restated, and one statement
of the term exists per file. Nothing landed in `src/`, so no
shared-master question arises. No deadline forced a fixed form.

## 5. WHAT THE NEXT BRIEF NEEDS

1. The meter's name has supply. Later briefs may cite
   `agents/tasks/LJ-1-743/Probe743.agda::Lset-trans-set` (verdict run
   p-2-verdict, EXIT=0) the way they cite a landed `src/` name, with
   the caveat that it is a task artifact and not a `src/` master.
2. The `stage-read` spine re-brief may name THIS file for the forward
   half's extraction sites, which 725-SPLIT measured to discharge by
   this term iterated (lj-1.725-SPLIT-report.md section 6). The spine
   still waits on the stage bound for the coding constructions
   (lj-1.725-SPLIT-report.md section 6, item 1), which stays unfunded
   and was not priced here.
3. The trimmed floor is measured: a probe whose rows live over
   `L.Constructible` alone costs 0.84 s and 269 MB for its frame at
   wide caliber. A probe carrying more of 725-SPLIT's frame than its
   own rows use repeats the `[LJ-1.559]`/`[LJ-1.566]` pattern, and
   this floor is the number to subtract.
4. Do not re-fund the term itself. It is green at two sites now; when
   the W4 collection after LJ-1 retires the duplication (owner,
   2026-08-20, dev/pod/direction.md), both sites are the count.
5. No review file accompanies this GO, by the 734 precedent. A
   critic looking for `review-of-Lset-trans-set.md` should read this
   report instead; the file exists only if a stop is ever stated.

## 6. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 0.83 s (`runs/p-2-verdict.out`) |
| peak, verdict run | 268,173,312 B, 12.5 percent of cap |
| floor run (hole) | 0.84 s, 268,681,216 B (`runs/f-1-floor.out`), EXIT=42, interaction meta only |
| runs this dispatch | f-1-floor, p-2-verdict |
| heap wall | none met |
| probe lines | 65 total, 59 non-blank, raw `.agda` (in-fence count 0, the ratio bar cannot fire) |
| brief estimate | 20 to 90 lines (W3); actual 65, inside it |
| caliber | `-A64m -I0 -M2g`, never set here |
| `src/` edits | none |

## ARCHIVE USED

- `archive/dev/DD-archived.md:1` `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Declined: not used. The clauses this dispatch answers to live in the slot file and the brief; the closed DD series is history.
- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch transcribes a predecessor's green bytes and runs them; no archived dispatching rule bears on that.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not used. The live screen is `dev/pod/screen.toml` and the live direction is `dev/pod/direction.md`; this task follows those.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not used. The route this task sits on is the live queue's, not the archived table's.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the \`L3.32-T\` series`. Declined: not used. The `L3.32-T` series predates the POD and shares no obligation with LJ-1.743.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used. A raw `.agda` probe and its records carry no translation surface.
- `dev/literature/level-formula-slot-roles.md:1` `# The level-hood formula: arity, what it binds, what stays free`. Declined: not used. The slot census belongs to the graph tasks; this transcription states no formula.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not used. No source is cited beyond the predecessor probe and its report.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not used. This dispatch cites no Devlin page and transcribes no classical construction.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not used. The fetch map is the literature team's record; this dispatch fetches nothing.
