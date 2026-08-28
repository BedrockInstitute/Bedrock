# LJ-1.738 report: `defat-fill-in-bound-lim`, the bounded DefAt fill under closedω

(This skeleton was written before the first Agda run and filled as the
runs landed; see C-22, `dev/LESSONS.md:2307`.)

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.738
obligation: agents/tasks/LJ-1-738/Probe738.agda::defat-fill-in-bound-lim
verdict: **NO-GO, STATED.** The obligation's type is stated, not
inhabited, and the clause of `dev/pod/instructions/coder.md` (a module
hypothesis taken from a predecessor is the type that predecessor
delivered) is what forbids the inhabitant: the module hypothesis
`Sat-in-carrier-lim` carries a NO-GO report naming the statement FALSE
at the full ruled scope (agents/tasks/LJ-1-736/lj-1.736-report.md:13,
:15), so the brief's type rests on a false premise and the only
possible inhabitant is vacuous -- and this brief's own premise 1 says
a vacuous inhabitant is not a GO. review-of-defat-fill-in-bound-lim.md
is the NO-GO's home. The file is green, EXIT=0 (`runs/p-2.out`, 1.50 s,
380,813,312 B peak), under `--cubical --safe --guardedness`, no
postulate, no hole. Nothing lands in `src/`. `stage-read` and
`envSet-in-carrier-stage` appear nowhere in the file; the landed
unbounded `fill` is not imported (`DefBody` is) and is named in
comments only.

## 0. THE PREDECESSOR QUESTION

The brief rests the obligation on three module hypotheses and says to
restate each as the type its predecessor delivered. Their state in
the tree, measured this dispatch:

| hypothesis | predecessor's delivery | verdict there |
|---|---|---|
| `keyS-in-carrier-lim` | agents/tasks/LJ-1-729/Probe729.agda:202 (the signature, INHABITED at :208) | GO (agents/tasks/LJ-1-729/lj-1.729-report.md:10, :53) |
| `envSet-in-carrier-lim` | agents/tasks/LJ-1-735/Probe735.agda:65 (the signature, INHABITED at :71) | GO (agents/tasks/LJ-1-735/lj-1.735-report.md:13) |
| `Sat-in-carrier-lim` | agents/tasks/LJ-1-736/Probe736.agda:147 (the type, STATED, NOT INHABITED) | NO-GO, STATED; the type is priced FALSE at the full ruled scope (agents/tasks/LJ-1-736/lj-1.736-report.md:13, :15; agents/tasks/LJ-1-736/review-of-Sat-in-carrier-lim.md:3) |

The clause says: if the report is NO-GO, or names the statement FALSE,
stop and say so with `file:line`, and do not inhabit the brief's type.
The third hypothesis is in that case. So this task is a stop, stated
in review-of-defat-fill-in-bound-lim.md.

No predecessor verdict is contradicted. The brief's premise 2 and the
two GOs stand; the brief was written before 735 and 736 returned (its
premise "the envSet and Sat lim bounds are hypotheses, not reports"
was true at brief build), and the clause is what handles the gap.

## 1. WHAT WAS BUILT

`agents/tasks/LJ-1-738/Probe738.agda` (198 lines, 180 non-blank, raw
`.agda`; in-fence count 0, so the ratio bar cannot fire):

1. The three hypothesis types, RESTATED, not imported
   (`Probe738.agda:136, :148, :163`): hypothesis 1 verbatim from the
   probe that typechecked and INHABITED it (Probe729.agda:202-208),
   hypothesis 2 verbatim from Probe735.agda:65-71, hypothesis 3
   verbatim from Probe736.agda:147-153, where it is STATED, NOT
   INHABITED. Each restatement's comment carries its predecessor's
   verdict with `file:line`.
2. The obligation's TYPE, stated with no inhabitant
   (`Probe738.agda:185`), the brief's glyphs verbatim up to the three
   resolutions recorded in the file's header: the V-level membership
   renamed `∈ˢᵥ` (the 725-SPLIT disambiguation), the Powerset-local
   `toS`/`DA` resolved at top level (`toS A ψ`, `DefOf.defSet
   (fst A) ψ`), and the landed `DefBody` imported from
   `src/L/Coding/Powerset.lagda.md` -- the obligation is about the
   landed formula, so restating it would drift (the 733 resolution).
3. The consumption-site record (`Probe738.agda`, header block "THE
   CONSUMPTION SITE"): the landed unbounded `fill` concludes at
   `Sat A (toS ψ) ∷ keyS A ψ ∷ z ∷ γ ⊨ DefBody w`
   (src/L/Coding/Powerset.lagda.md:500, conclusion at :502), and
   `toS ψ : Formula S 1`, so the site consumes the Sat bound AT THE
   WIDE ALPHABET -- exactly the scope 736 prices FALSE. The review
   works out what this means for the corrected-target list.

NOT built, and why: any measurement section. The 733 probe could
re-run an existing machine-checked refutation at its own site; this
task's falsity mechanism is the 736 diagonal, which the 736 review
prices at far more than a probe and leaves unlanded. Re-measuring it
here would re-fund that diagonal, and the clause needs only the
predecessor's verdict, which exists. No corrected type for the Sat
scope is stated either: the corrected targets are UNRULED, and stating
one would be inventing a specification (the 733 discipline).

## 2. THE FLOOR AND THE RUNS

The probe carries no proofs, so the elaboration frame IS the whole
cost and the floor run is the verdict run; there was nothing to trim.
p-1 is the first green on the delivered bytes; p-2 is the confirm re-
run after the review landed, same bytes. ONE Agda process per run,
GHCRTS `-A64m -I0 -M2g`, the wide caliber, set on the pane by the
program and never touched here. Peak RSS is instrumented
(`/usr/bin/time -l`). No heap wall was met: the largest peak,
402,358,272 B (p-1), is 18.7 percent of the 2,147,483,648-byte wide
cap. No run timed out and there were no failing runs, so nothing was
repeated.

| run | wall | peak RSS (B) | note |
|---|---|---|---|
| p-1 | 1.54 s | 402,358,272 | first green, EXIT=0, delivered bytes |
| p-2 (verdict) | **1.50 s** | **380,813,312** | **EXIT=0, confirm, same bytes** |

## 3. WHAT THE NEXT BRIEF NEEDS

1. **Rule the corrected Sat scope first.** Two of the three bounds the
   assembly needs are real (729, 735); the third is priced FALSE by
   its own predecessor report, and the review sharpens 736's
   corrected-target list AT THIS SITE: correction 1 (carrier-bounded
   alphabet) does not directly feed the consumption, because the fill
   carries `Sat A (toS A ψ)` with `toS A ψ : Formula S 1`; correction
   2 (bounded constants) fits the site's shape -- every constant of
   `toS A ψ` is an `asConst A m` (src/L/Coding/Bridge.lagda.md:623
   already reads `Sat B (mapFo asConst ψ)`), and `asConst A m` is
   `intoL (ιA m)` (src/L/Coding/Bridge.lagda.md:124-125) -- but
   whether that side condition closes cheaply from the 729 helpers is
   UNMEASURED and the scope is UNRULED. Price after the ruling, not
   before.
2. **Do not re-fund**: the 736 kernel (Probe736.agda:88-135), the 729
   climb, `keyS-in-carrier-lim`, `envSet-in-carrier-lim` and its
   landed route, `relativize-correct`, the unbounded `fill`, the 730
   rank chain. The restated types in Probe738.agda are the assembly's
   shell and can be copied forward.
3. **A vacuous inhabitant is not a GO** (the 733 report's item 5,
   which transfers as a warning, not as a measurement): while
   `Sat-in-carrier-lim` stands delivered FALSE, any future return that
   inhabits THIS obligation's type should be read as vacuity through
   the false hypothesis, not as a membrane crossing.
4. **W3 answer.** The brief's W3 asked whether the three `closedω`
   bounds plus `relativize-correct` close bounded `fill`, estimated 40
   to 100 lines. Answer: **NO at the offered hypothesis set.** The
   clause fired before the assembly was attempted, so the estimate is
   neither met nor missed -- the assembly was never priced because one
   of its three premises is false by its predecessor's report. The W2
   clause had nothing to bind: no new mathematics was written, the
   restated types are the predecessors' own, and nothing is duplicated
   or shared with a sibling.
5. **C-42 note.** This NO-GO measures ONE site: the assembly at the
   offered hypothesis set. The bound family now stands at keys GO
   (729), environment sets GO (735), `Sat` NO-GO at `Formula S n`
   (736), assembly blocked at the toS consumption (here). No sweep of
   further sites is owed by this verdict: the defect is the 736
   alphabet defect, already on record there.

## 4. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.50 s (`runs/p-2.out`) |
| peak, verdict run | 380,813,312 B, 17.7 percent of cap |
| first green | 1.54 s, 402,358,272 B (`runs/p-1.out`) |
| floor | the file itself: no proofs, frame is the whole cost |
| runs this dispatch | p-1, p-2 |
| heap wall | none |
| in-file / in-fence lines | 198 total, 180 non-blank / 0 (raw `.agda`) |
| brief estimate (W3) | 40 to 100 lines |
| caliber | `-A64m -I0 -M2g`, never set here |

The W3 estimate named the ASSEMBLY; the clause fired before the
attempt, so the estimate is not met or missed. The delivered probe is
198 lines of types and records.

## ARCHIVE USED

All five injected archive candidates are DECLINED, not used. The stop
rests on two predecessor probes, three predecessor reports and one
predecessor review, plus landed masters, all cited at `file:line` in
sections 0 to 2 and in the review.

- archive/dev/ORCHESTRATION.md: declined, not read; the pod loop's
  history does not touch a clause-driven stop built from
  machine-checked predecessors.
- archive/dev/DD-archived.md: declined, not read; the clauses this
  dispatch answers to live in the live slot file and the brief.
- archive/dev/PLAN-archived.md: declined, not read; retired plans name
  no bounded-fill obligation.
- archive/dev/STATUS-archived.md: declined, not read; standing status
  lives in `dev/pod/screen.toml`, and this task's record is in its own
  runs directory.
- archive/dev/TASKS-archived.md: declined, not read; the predecessor
  files this task needed (LJ-1.729, LJ-1.733, LJ-1.735, LJ-1.736) are
  live files named by the brief and cited at `file:line` in section 0.

## LITERATURE USED

All five injected literature candidates are DECLINED, not used. The
verdict quotes no book: every step is an in-tree fact cited at
`file:line` in sections 1 to 3 and in the review.

- dev/literature/glossary-review-2026-08.md: declined, not used; a
  raw `.agda` probe and its records carry no translation surface.
- dev/literature/devlin-errata.md: declined, not used; the errata
  collects rud-route error classes, and this stop is in-tree clause
  application, not a do-not-repeat checklist item.
- dev/literature/level-formula-slot-roles.md: declined, not used; the
  level formula plays no part in this membrane.
- dev/literature/primary-sources.md: declined, not used; no primary
  source was consulted for this dispatch.
- dev/literature/BIBLIOGRAPHY.md: declined, not used; no source beyond
  the tree was consulted for this dispatch.
