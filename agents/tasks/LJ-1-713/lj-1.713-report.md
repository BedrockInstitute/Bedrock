# LJ-1.713 report: the chain measured to its true edge

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.713
obligation: agents/tasks/LJ-1-713/Probe713.agda::below-closed
verdict: **NO-GO on `below-closed` as briefed; the assembled prefix is
green at one frame.** `review-of-below-closed.md` states the stop with
`file:line`. In short: the brief's fourth supply, `[LJ-1.679]`'s
`CompletenessFrom`, is a named TYPE (`Probe679.agda:94-95`), not a
term; its inhabitation is `[LJ-1.700]`'s own obligation, which closed
NO-GO and was upheld (`review-of-LJ-1-700-1.md:167`, `:174-175`); and
this run measured the same fact from the composition side
(`runs/floor-1.out:30-33`, `[CannotApply]` on `A.CompletenessFrom`).
What the probe DELIVERS is green and is the chain assembled to its
true edge: `runs/p-1.out` EXIT 0, 35.17 s warm, peak 1,130,430,464 B,
recheck `runs/p-2.out` EXIT 0 at 2.70 s, 705,069,056 B. The
obligation name `below-closed` is not defined, so the witness meter
must read UNRESOLVED.

Written as a skeleton before any Agda run and filled after each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-713/`. Agda ran under the caliber the program set
on this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda
process at a time. I did not set `GHCRTS`. Nothing is postulated, the
delivered probe carries `--safe` and no hole, and nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP WALL WAS MET IN THIS TASK.** Highest peak of any run here
is 1,660,157,952 B against the 2,147,483,648-byte wide cap
(`runs/floor-1.out`), 77 percent of it. `[LJ-1.700]`'s wall is that
task's record; this probe's definitions carry explicit codomains
throughout, which is the cure its critic named untested, applied and
measured at THIS frame, not transferred.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1
work. It does not start that collection and it does not start phase
3. No Boundary clause is in conflict.

**EVERY NUMBER BELOW IS MEASURED IN THIS WORKTREE.** `floor-1` is the
one cold-cone row (it elaborated the whole import cone: `Probe652`,
`Probe679`, `Probe690` with its runs chain, `Probe697` with
`LJ-1-697.runs.W3`, `Probe706` with `Probe693` and `Probe698`,
`Probe709` with `LJ-1-703` and its runs modules, plus `src/`). Rows
`p-1` and `p-2` ran on the interfaces it left. This report does not
bound a cold-cache number for `src/` outside this worktree.

## 1. THE PREDECESSOR QUESTION, ANSWERED BEFORE ANY AGDA

The standing coder clause: take the type from the probe that
typechecked, and the verdict from the report. One predecessor on this
chain returned NO-GO, and it is the one premise 4 leans on.

| piece | type | site | verdict |
|---|---|---|---|
| `below-from-place` | placement + identification to `Below` | `Probe706.agda:78` | GO. Imported, not rebuilt. |
| `Bound-in-tower` | the placement row | `Probe706.agda:65-67` | TYPE, green. Not inhabited. Taken as hypothesis 1. `[LJ-1.711]` is dispatched on it. |
| `Identified` | the carve equals the table | `Probe706.agda:59-61` | TYPE, green. Not inhabited. Taken as hypothesis 2. `[LJ-1.712]` re-aims the row at the re-bounded carve. |
| `from-below` | `Below`-all to `HierInStage` | `Probe697.agda:81` | GO. Imported, not rebuilt. |
| `HierInStage` | `hierL δ` in `Lset lam` | `Probe679.agda:84-88` | TYPE, green. The assembly's waypoint. |
| `CompletenessFrom` | `SameHyp → HierInStage → Completeness` | `Probe679.agda:94-95` | **TYPE, green; NOT inhabited** (`Probe679.agda:97`: "named supplier, not the obligation"). Inhabiting it is `[LJ-1.700]`'s obligation (`LJ-1.700.md:12`), closed NO-GO and upheld (`review-of-LJ-1-700-1.md:167`, `:174-175`). This is the stop. |
| `same-as-graph-both` | the union telescope to `SameAsGraph w b γ` | `Probe709.agda:67` | GO. Imported, not rebuilt. |
| `SameHyp` | all `w b γ` unconditionally | `Probe679.agda:48-49` | TYPE, green. PRODUCED here from 709's delivery by `same-hyp-of`, green. |

`[LJ-1.700]`'s report is an unfinished skeleton, but its outcome is
not: the critic separated outcome from record and upheld the outcome
(`review-of-LJ-1-700-1.md:167-175`). A NO-GO predecessor blocks
inhabiting its type, and premise 4 of this brief is that type.

## 2. D-10, BEFORE ANY AGDA

**PREMISE 4 FAILED THE TRUTH CHECK.** The brief says the assembly
above `Below` is green, on a basis that names a type. The floor run
tested it before any proof was attempted: `A.CompletenessFrom` has
type `Type (ℓ-suc ℓ)`, not a function type, and the application
`A.CompletenessFrom s h` is refused (`runs/floor-1.out:30-33`). The
corrected target beside the original, as D-10 asks: `below-closed-via`
(`Probe713.agda:120-130`), the same composition with the fourth arrow
taken as the explicit hypothesis it is. The corrected bill list for
the chain to `Completeness` has three rows, not two: `Bound-in-tower`
(`[LJ-1.711]`), the identification at the re-bounded carve
(`[LJ-1.712]`), and `CompletenessFrom`'s inhabitation (`[LJ-1.700]`,
open, cure named and untested, `review-of-LJ-1-700-1.md:182-183`).

**THE STATEMENT IS NOT FALSE.** Nothing here measures that `SameHyp`
and `HierInStage` cannot reach `Completeness`. C-42 applies to the
`[CannotApply]`: it is an elaboration fact about a missing term. The
mathematical question stays open exactly where `[LJ-1.700]` left it,
and its critic called the obstruction argument "coherent and
unrefuted" (`review-of-LJ-1-700-1.md:174`).

## 3. THE FLOOR, MEASURED BEFORE ANY PROOF

Coder clause, owner 2026-08-23: price the frame before the term. The
floor version of the probe carried the full frame, the full
`SameHyp` half of the body, and one hole at the `from-below` half:
**the frame costs 276.87 s cold-cone and 1,660,157,952 B, 77 percent
of the wide cap, and it does not wall** (`runs/floor-1.out`, exit 42,
the one error the `[CannotApply]` at the `CompletenessFrom`
application). The same run therefore priced the frame AND measured
the stop's evidence in one pass. No import can be trimmed: each of
the four arrows lives at its own committed address, and the cone is
the union of their needs. `[LJ-1.697]`'s frame alone was 144.56 s
(`lj-1.697-report.md:126`); adding the 690/703/709 cone for the
`SameHyp` half roughly doubles it.

## 4. THE DELIVERED PROBE

All green, `runs/p-1.out` exit 0, 35.17 s warm, 1,130,430,464 B peak;
recheck `runs/p-2.out` exit 0 at 2.70 s, 705,069,056 B; final row
`runs/p-3.out` exit 0 at 36.54 s, 1,130,444,648 B, taken after the
last comment edit so the delivered bytes are the checked bytes:

1. **`same-hyp-of`** (`Probe713.agda:89-96`). `[LJ-1.709]`'s
   delivered telescope, hoisted over the family `{n} w b γ`, produces
   `[LJ-1.679]`'s unconditional `SameHyp`. `pow` is global in 709's
   delivery, so it hoists out front; `IsOrd` at the b-slot and the
   two bridges hoist as families. The floor run checked this term
   against `CompletenessFrom`'s first input and accepted it, so the
   709-to-679 handover is measured, not argued.
2. **`below-of`** (`Probe713.agda:102-107`). The two rows through
   `below-from-place`. The target is `[LJ-1.697]`'s `Below` spelling
   on purpose: this forces 693's `step` and W3's `step` to one
   convertibility.
3. **`hier-of`** (`Probe713.agda:110-115`). `from-below` applied to
   `below-of`. The rows reach `HierInStage` at the shared frame.
4. **`below-closed-via`** (`Probe713.agda:120-130`). The whole chain:
   `cf (same-hyp-of pow ordb up down) (hier-of bound ident)`, with
   `(cf : A.CompletenessFrom)` explicit.

The obligation name `below-closed` is absent on purpose. No postulate
stands in for it, and I did not deliver a weakened term under the
briefed name: a `below-closed` with a third visible argument would
misreport the chain as having two bills.

## 5. W2 ANSWER

Nothing is proved twice. All four arrows are consumed at their
delivered addresses (`Probe706.agda:78`, `Probe697.agda:81`,
`Probe709.agda:67`, and `CompletenessFrom` as a type at
`Probe679.agda:94`). The new lines are the composition itself: two
family-hoist wrappers and one application. The mathematics is written
once at the generic frame (`At713` over `[LJ-1.679]`'s telescope,
`Probe700`'s `module Spend` as precedent) and instantiated by
nothing. No deadline forced a fixed form; the weakening found here is
reported, not hidden (W2's report-the-conflict duty is section 2 and
the review).

## 6. W3, THE WIDEST UNMEASURED TERM, ANSWERED

The brief asked whether the four arrows compose at one frame, or
whether two of them want different carriers. Measured answer, in two
halves:

1. **THE `SameHyp` HALF: ONE FRAME.** `[LJ-1.709]`'s delivery, fed
   through the hoisting, is accepted against `[LJ-1.679]`'s
   unconditional `SameHyp` (`Probe713.agda:89-96`, green in
   `runs/floor-1.out` before any body existed and again in
   `runs/p-1.out`). The 709 carrier and the 679 carrier agree; no
   coercion, no transport.
2. **THE `Below` HALF: ONE FRAME.** `P706.Below` (693's `step`) and
   `P697.At.Below` (W3's `step`) are convertible at this frame;
   `below-of` typechecks with `B.Below` as its target
   (`Probe713.agda:102-107`, green in `runs/p-1.out`). The reason is
   visible in the sources, `S = V ℓ` by record literal
   (`src/V/Hierarchy.lagda.md:78-84`) and both iterators are the same
   `sucV` clauses; the measurement confirms it rather than assuming
   it.

So the four arrows' carriers agree. What does not compose is the
chain through the fourth arrow, because the fourth arrow is not a
term. NO-GO would have earned the frame mismatch as a term; there is
no mismatch between the arrows to earn. The mismatch is between the
brief's supply list and the tree.

## 7. W4, AND P-l

**W4: not applicable.** No module was retired, nothing under `src/`
changed, and `dev/ARCHIVE.md` takes no row from this task. The ideal
form written fresh today is the form delivered: the hoisting, the two
row-arrows, and the composition at the honest fourth argument.

**P-l: obeyed.** Every type in the file names `Lset` stages, which
are opaque, and `step 3` through `[LJ-1.697]`'s own `Below`. No
successor presentation is named in an obligation type, and no
conversion between presentations is asked anywhere. The two `step`
spellings meet inside `below-of`'s TARGET check, which is a
measurement site, not a type drag.

## 8. WHAT THE SHAPE RESISTED

- **What it cost.** 140 lines, 60 code. Floor 276.87 s cold-cone,
  77 percent of the cap. First green 35.17 s warm. Recheck 2.70 s.
  No heap wall.
- **What the shape resisted.** One thing: `A.CompletenessFrom` does
  not apply. The fix is the honest one, `below-closed-via`, and the
  stop it implies is stated in the review. Everything else, including
  the dotted-path spellings `P709.Pin.FPin.Bridge {n} w b γ` for the
  hoisted bridge families, elaborated on the first correct attempt.
- **What I had to weaken.** Nothing in any delivered type. The
  obligation type as briefed is uninhabited in this tree, and I left
  the name uninhabited rather than re-label a third hypothesis as one
  of the two.
- **What I could not close.** The same thing `[LJ-1.700]` could not:
  the ambient `matrix₃` reading at a stage member, which
  `BoundInStage` spends (`Probe700.agda:78-79`).

## 9. WHAT THE NEXT BRIEF NEEDS

1. **CORRECT THE SUPPLY COUNT.** The chain to `Completeness` carries
   three open bills, not two. The third is `CompletenessFrom`'s
   inhabitation: `[LJ-1.700]`'s obligation, open, its wall localized
   and its cure named (`review-of-LJ-1-700-1.md:121-125`, `:151-153`,
   `:182-183`).
2. **DO NOT RE-DISPATCH** `below-from-place`, `from-below`,
   `same-as-graph-both`, the `SameHyp` hoisting, or the row types.
   `same-hyp-of` is now the tree's producer of `[LJ-1.679]`'s
   unconditional `SameHyp` from 709's delivery, and `hier-of` is the
   producer of `HierInStage` from the two rows. Fund their consumers,
   not them.
3. **IF `[LJ-1.700]` IS RE-DISPATCHED**, start from its critic's
   handoff: the wall sits in `toL`, `same-at-codes` and
   `hier-at-code`, the floor already paid for the telescope, and the
   explicit codomain on `hier-at-code` is the first untested move.
   This probe's green rows with explicit codomains everywhere are a
   same-frame measurement that the narrow shapes are cheap.
4. **THE ASSEMBLY IS DONE.** When `[LJ-1.700]`'s term lands, the
   chain closes with `below-closed-via`: no new assembly work is
   left, at this frame or any successor of it.

## 10. PRICE

Non-blank non-comment lines counted by
`awk 'NF' file | grep -cv '^[[:space:]]*--'`.

| what | lines | code lines | at `file:line` |
|---|---:|---:|---|
| the probe, whole | 140 | 60 | `Probe713.agda` |
| `same-hyp-of` | 9 | 9 | `Probe713.agda:89-97` |
| `below-of` | 6 | 6 | `Probe713.agda:102-107` |
| `hier-of` | 6 | 6 | `Probe713.agda:110-115` |
| `below-closed-via` | 11 | 11 | `Probe713.agda:120-130` |

The brief estimated 40 to 110 lines for W3. The delivered file is 60
code lines, and the composition is 5 of them. The estimate's worth
went into the measurement the brief actually needed: the fourth
supply is not supply.

## GATES

- **D-10** (`dev/LESSONS.md:1375`). Applied in section 2: the
  recorded target (premise 4) was priced for truth before any proof
  and failed the check; the corrected target is recorded beside it.
- **C-22** (`dev/LESSONS.md:2307`). The report was a skeleton before
  the first run and was filled after each row landed.
- **P-l** (`dev/LESSONS.md:2367`). Section 7. Obeyed.
- **D-26** (`dev/LESSONS.md:1735`). Did not bind: no well-founded key
  was built.
- **C-42** (`dev/LESSONS.md:3762`). Section 2, second paragraph. No
  refutation of the two-inputs-reach-`Completeness` question landed,
  and none is claimed.

## Return

`below-closed` is not inhabited, and the stop is not mine to soften:
the brief's fourth supply is a type, its inhabitation is
`[LJ-1.700]`'s open NO-GO, and the floor run measured the refusal at
this frame (`runs/floor-1.out:30-33`). What the probe delivers is
green and useful: `[LJ-1.709]`'s delivery hoisted into
`[LJ-1.679]`'s `SameHyp`, the two rows through `below-from-place` and
`from-below` into `HierInStage`, and the whole chain assembled as
`below-closed-via` with the fourth arrow as the explicit hypothesis
it is, at one frame, EXIT 0. W3 is answered: the arrows agree on
carriers; the tree lacks a term, not a frame. The critic reads
`review-of-below-closed.md`. Nothing is staged, nothing is pushed,
and the working tree carries only `agents/tasks/LJ-1-713/` as changed
output.

---

(Appended by the `lint-back-to-author` review dispatch, LJ-1.713#2,
2026-08-28, whose return is `agents/tasks/LJ-1-713/review-of-LJ-1-713-1.md`.
The acceptance run of this return held conjuncts 1 to 5 and failed conjunct 6,
the survey duty. The two sections below answer it for the paths the work brief
injected. Nothing above this note is altered. The review UPHELD the NO-GO.)

## ARCHIVE USED

- **`archive/dev/DD-archived.md:35`, read.** The DD25 row states the
  reviewer's questions: "is the refusal correct on its own numbers; is the
  measurement sound; did the BRIEF cause the outcome; and is there a cure the
  return missed". The review of this return answers them; the stop stands.
- **`archive/dev/ORCHESTRATION.md:74`, read.** The heading says the duty in
  one line: "1.1 A negative return is adversarially reviewed (PLAN DD25)".
- **`archive/dev/PLAN-archived.md`, declined.** Not read: its first line is
  "# ARCHIVED 2026-08-20" and planning history bears nothing on a supply
  count.
- **`archive/dev/STATUS-archived.md`, declined.** Not read beyond its first
  line: "# STATUS-archived: the goal table of the internalization route". The
  internalization goal table is not this composition's supply list.
- **`archive/dev/TASKS-archived.md`, declined.** Not read beyond its first
  line: "# Archived task index: the `L3.32-T` series". That series predates
  the LJ-1 campaign and names none of this chain's pieces.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`, declined.** Not used: the
  slot-role table is semantics evidence for the 700 question, and this stop
  is about term existence, settled at `Probe679.agda:94-95` and the 700
  record.
- **`dev/literature/BIBLIOGRAPHY.md`, declined.** Not read: its first line is
  "# Bibliography for the rud route", and this return adds no citation.
- **`dev/literature/devlin-errata.md`, declined.** Not read: its first line
  is "# Devlin errata: documented error classes (do-not-repeat checklist)",
  and this return quotes no scanned page.
- **`dev/literature/primary-sources.md`, declined.** Not read: its first line
  is "# Primary sources, second round: Jensen manuscript, Devlin, Jech", and
  no source question arose.
- **`dev/literature/glossary-review-2026-08.md`, declined.** Not read: its
  first line is "# Glossary review: the 119 pre-protocol entries", and this
  return proposes no glossary entry.
