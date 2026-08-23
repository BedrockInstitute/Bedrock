# [LJ-1.588] Does `gch-from-five` need row 4 unrestricted?

**GO. THE ANSWER IS NO.** The bill never spends row 4 at a δ where
`[LJ-1.585]`'s two side conditions fail, so the restricted row is enough and
**no new hypothesis goes on the bill**.

**THE OBLIGATION IS INHABITED.** `gch-from-restricted-row4`
(`agents/tasks/LJ-1-588/Probe588.agda:424-435`) is `gch-from-five`
(`agents/tasks/LJ-1-564/Probe564.agda:456-463`) with row 4 replaced by
`[LJ-1.585]`'s restricted row and with no other change. The witness meter
resolves it: 0 UNRESOLVED of 1, 12.78 s.

**THE PROBE IS GREEN, EXIT 0, THREE RUNS** (`runs/final-1.out` to
`runs/final-3.out`). It carries NO hole and NO postulate under `--safe`, so
every row in it is a measurement. **Nothing landed in `src/`.** Row 4 is never
built, the formula is never written, and `Row4RestrictedGeneric` is a
hypothesis from the first line to the last.

**ONE THING MOVES, AND IT IS NOT A WIDENING.** The tower parameter α₀ is
QUANTIFIED, exactly as `L.StageCardinal` quantifies it
(`src/L/StageCardinal.lagda.md:15-19`). Section 4 of the probe prices the other
reading, and the price is a row that bounds every infinite L-cardinal.
**Read the GO with that sentence beside it.**

**I DID NOT WIDEN `stage-card-upper` AND I WROTE NO FORMULA**, as the brief
forbids. `[LJ-1.585]`'s principle is kept: the hypothesis is stated exactly
where the function has a value, and at no other δ.


## W3, WRITTEN FIRST AND TYPECHECKED ALONE

`agents/tasks/LJ-1-588/runs/W3.agda`, TYPE ONLY, three runs, exit 0:
`runs/w3-1.out` (first check on this pane, 32.96 s, 1,848,033,280 bytes peak
RSS), `runs/w3-2.out` (3.03 s) and `runs/w3-3.out` (4.03 s, after two comment
corrections to `file:line` citations). The brief estimated about 12 lines and under 90 seconds. The
slice is 117 lines and 32.96 s. **The overrun is the dependency chain and not
the statement**: naming the spend site needs `[LJ-1.564]` in scope, and
`[LJ-1.564]` pulls `[LJ-1.550]`, `[LJ-1.558]`, `[LJ-1.528]`, `[LJ-1.543]`,
`[LJ-1.540]` and `[LJ-1.544]` behind it.

**W3's FINDING, AND IT DECIDED THE TASK.** The spend lives in
`power-into-succ-from-landing` (`Probe564.agda:203-226`), whose own head
carries NEITHER `IsOrd (fst κ)` NOR `κ ∉ ω`. **But `gch-from-five` does not
reach it through that head.** It reaches it through `power-into-succ-at`
(`Probe564.agda:351-360`), whose type is `PowerIntoSuccAt`
(`Probe564.agda:327-330`), and that type binds BOTH. So the fourth hypothesis
of `GCHStatement` IS in scope at the spend, and the brief's guess about it is
correct.


## WHERE ROW 4 IS SPENT

**ONE SITE. `agents/tasks/LJ-1-564/Probe564.agda:210`, `b9 δ Lδ ordδ refl`.**

`b9` occurs TWELVE times in that file, one to a line: `:209`, `:210`, `:234`,
`:235`, `:358`, `:359`, `:376`, `:378`, `:416`, `:417`, `:462`, `:463`. It is
APPLIED at exactly one of them. The other eleven are binders (`:209`, `:234`,
`:358`, `:376`, `:416`, `:462`) or pass-throughs (`:235`, `:359`, `:378`,
`:417`, `:463`).

**THE CHAIN FROM `gch-from-five` TO THE SPEND, AT `file:line`.**

| Step | Where | What it does with row 4 |
|---|---|---|
| `gch-from-five` | `Probe564.agda:462-463` | binds `b9`, hands it to the next |
| `gch-from-here-sharp` | `Probe564.agda:416-417` | hands it on |
| `gch-from-here` | `Probe564.agda:376-378` | hands it to `power-into-succ-at` |
| `power-into-succ-at` | `Probe564.agda:358-359` | hands it on. **Its head binds `ordκ` and `κ∉ω`** |
| `power-into-succ-from-landing` | `Probe564.agda:209-210` | **APPLIES it** |

`power-into-succ` (`Probe564.agda:229-235`) is the OTHER caller of the applying
function and it is NOT on this chain. **That distinction is the whole task**:
`power-into-succ`'s head carries no `κ∉ω`, so at that entry the first side
condition would not be derivable. `gch-from-five` does not use that entry.

**THE δ IT IS SPENT AT.** The δ is bound by `SuccCardL δ κ`
(`src/L/GCH.lagda.md:46-53`), produced by `[LJ-1.528]`'s `b4-paid`
(`Probe564.agda:439-440`) inside `gch-route-with-premised-hard`
(`Probe564.agda:335-341`). **It is the successor cardinal of κ in L**, and its
third conjunct `⟨ fst κ ∈ fst δ ⟩` (`src/L/GCH.lagda.md:50`) is the only thing
that ties it to κ.

**AND THE `Lδ` OF THE SPEND IS `LsetS` ON THE NOSE**, with no transport.
`Lδ-is-LsetS` (`Probe588.agda:161-163`) is `refl`: `stage-is-L δ oδ` is
`isL-Lset (fst δ) oδ` (`Probe564.agda:155-156`) and `LsetS β oβ` is
`Lset β , isL-Lset β oβ` (`src/L/Axioms/Basic.lagda.md:160-161`).

### Condition one, `δ ∉ ω`: HOLDS, AND IT IS THE SITE'S OWN TERM

**THE BRIEF ASKED WHETHER `src/L/GCH.lagda.md:64` PROPAGATES TO THAT δ. IT
DOES, AND THE PROOF ALREADY STANDS IN THE TREE AT THIS VERY SITE.**
`P550.UseSite.δ∉ω` (`agents/tasks/LJ-1-550/Probe550.agda:250-251`) is two
lines: ω is transitive (`src/L/Ordinal.lagda.md:263-264`) and `SuccCardL`'s
third conjunct puts κ in δ, so a finite δ would make κ finite.

`delta-not-omega` (`Probe588.agda:180-183`) is those two lines lifted off
`UseSite`'s telescope, so the bill's other four inputs are not needed to state
them. **AND IT IS NOT MY TERM.** `delta-not-omega-is-the-sites-own`
(`Probe588.agda:189-197`) is `refl`: the lifted term IS the one the use site
already computes.

**SO ONE OF THE TWO SIDE CONDITIONS IS FREE, AND I SAY IT PLAINLY AS THE BRIEF
ORDERED.**

### Condition two, `δ ∈ sucV α₀`: THERE IS NO α₀ AT THE SITE TO CHECK IT AGAINST

**THE BRIEF ASKED WHERE α₀ COMES FROM AT THE SPEND SITE. IT COMES FROM
NOWHERE.** `gch-from-five` has no α₀, and `Probe564.agda` never imports
`L.StageCardinal` at all. **So the site does not pick the tower. The hypothesis
does.**

That is not a licence to widen. `L.StageCardinal` takes α₀, `oα₀` and `sq` as
MODULE PARAMETERS (`src/L/StageCardinal.lagda.md:15-19`), so
`stage-card-upper` EXISTS at every α₀, and a hypothesis about it may be stated
at every α₀ without being stated more widely than the function.
`Row4RestrictedGeneric` (`Probe588.agda:219-223`) is `[LJ-1.585]`'s
`Row4Restricted` with those three binders in front, and `generic-is-585s`
(`Probe588.agda:232-237`) is the `refl` that says the written form IS
`Row4Restricted` (`agents/tasks/LJ-1-585/Probe585.agda:163-166`) at every tower.

**UNDER THAT READING THE SECOND CONDITION IS FREE AT α₀ := δ.**
`self∈sucV` (`src/V/Model.lagda.md:236-237`) discharges `δ ∈ sucV δ` in one
line, and the square law that the tower demands is `P550.SqAt` at δ
(`Probe550.agda:309-310`), **which is ROW 2 OF THE BILL and not a new
hypothesis** (`Probe564.agda:458`).

**WHAT THAT COLLAPSES TO.** `generic→row4-infinite` (`Probe588.agda:267-270`)
is the finding in one row: **quantifying the tower turns `[LJ-1.585]`'s TWO
side conditions into ONE, and the survivor is `δ ∉ ω`.** `restricted-at-spend`
(`Probe588.agda:291-294`) then pays the spend from that row and
`delta-not-omega`, with nothing else.


## WHAT THIS DOES TO THE BILL

**THE RESTRICTED ROW SUFFICES. THE BILL IS STILL FIVE ROWS AND NO ROW GREW.**

`gch-from-restricted-row4` (`Probe588.agda:424-435`):

| Row | Type | Changed? |
|---|---|---|
| 1 | `P550.AmbientCardAtSucc` | no |
| 2 | `P550.SqAt` | no. **It is spent twice now**: once by `UseSite` and once at α₀ := δ |
| 3 | `P550.CoHyps` | no |
| 4 | `Row4RestrictedGeneric` | **YES. This is the swap** |
| 5 | `P558.SuccIntoPower` | no |

**AND THE SWAP CAN ONLY WEAKEN.** `full→generic` (`Probe588.agda:308-309`) is
`[LJ-1.585]`'s `full→restricted` (`Probe585.agda:188-189`) IMPORTED with the
tower quantified, so row 4 in full gives the restricted row.
`gch-from-five-through-the-restricted-row` (`Probe588.agda:441-448`) closes
`gch-from-five`'s OWN type through this file's route, and
`five-row-bill-unchanged` (`Probe588.agda:453-459`) is `[LJ-1.564]`'s term at
the same type. **A mismatch of one implicit anywhere in the chain would be
exit 42.**

**SO `[LJ-1.584]`'s FORMULA PAYS ROW 4 AFTER ALL, subject to one condition the
brief did not state**: the formula must hold AT EVERY TOWER, not at one.

### THE HONEST BOUNDARY. What I did NOT inhabit

1. **NOTHING HERE PAYS ROW 4.** `Row4RestrictedGeneric` is a hypothesis in
   every row of the file. No formula and no injection is built.
2. **`[LJ-1.585]`'s REFUTATION STANDS UNTOUCHED AND I NEVER ATTACKED IT.**
   `side-conditions-are-false` (`Probe585.agda:219-226`) says the restricted
   row cannot be widened to row 4, because δ := 0 is in ω. **This file agrees
   and never tries.** The only δ it spends at is a successor cardinal above an
   infinite κ, and `delta-not-omega` proves that δ is not in ω. **The two
   statements are about different δ.** `full→row4-infinite`
   (`Probe588.agda:279-280`) is the one direction that holds, and the other
   direction is never asked for.
3. **I did not price row 4's truth at a finite δ.** `[LJ-1.533]` left it open,
   `[LJ-1.585]` left it open, and this file leaves it open. It now matters
   LESS, not more: the GCH bill does not need it.
4. **I did not measure whether `[LJ-1.584]`'s formula is provable at every
   tower.** That is the one thing the GO now depends on, and section 4 below
   is the price if it is not.

### THE FIXED-TOWER READING, PRICED

**IF THE FORMULA CAN ONLY BE HAD AT ONE α₀, THIS GO DOES NOT APPLY, and the
probe says what the difference costs rather than leaving it as an opinion.**

`BoundAtSucc α₀` (`Probe588.agda:327-328`) is the extra hypothesis:
every successor cardinal of every infinite L-cardinal lies in `sucV α₀`.
`fixed-tower-with-the-bound` (`Probe588.agda:333-343`) shows the fixed form
pays the spend WITH it, so **the bound is the whole difference between the two
readings and nothing else is hiding in the generic route.**

**AND THE BOUND IS NOT A SMALL ROW.** `bound-bounds-every-cardinal`
(`Probe588.agda:357-366`) proves, from `[LJ-1.528]`'s PAID `SuccCardExists`
(`Probe564.agda:439-440`) and nothing else, that the bound puts **EVERY
infinite L-cardinal inside `sucV α₀`**. `GCHStatement` quantifies over every
infinite L-cardinal (`src/L/GCH.lagda.md:60-64`), and no row of
`gch-from-five` says anything about a single tower that bounds L's cardinals.
**That row is on nobody's bill.**


## W2, ANSWERED

The brief did not state W2. I answer it because the slot file requires the
answer in the return.

**W2 IS KEPT AND IT IS THE FILE'S SHAPE.** The mathematics is written once at a
generic carrier and instantiated. `Row4Infinite` (`Probe588.agda:261-265`) and
`injL-recarry` (`Probe588.agda:247-252`) are stated at an arbitrary L-element,
with no mention of the bounded-subset site and no mention of κ. Section 3
instantiates them at the spend site, and section 5 threads the result through
`[LJ-1.564]`'s own route. **Two functions are re-derived and no more**:
`power-into-succ-from-spend` (`Probe588.agda:387-407`) and
`power-into-succ-at-restricted` (`Probe588.agda:410-421`), because
`power-into-succ-at` takes row 4 as an ARGUMENT and a substitute cannot be
plugged into it. Everything above and below those two in the chain is
`[LJ-1.564]`'s own term, applied.


## WHAT THE STATEMENT COST, AND WHAT RESISTED

- **THE BRIEF'S ESTIMATE WAS 140 LINES WITH ABOUT 30 FOR THE OBLIGATION. THE
  FILE IS 474 LINES AND THE OBLIGATION IS 12** (`Probe588.agda:424-435`). The
  obligation is smaller than the estimate and the file is 3.4 times bigger.
  Both numbers have one cause: the answer is a chain of eight small rows, not
  one big row, and each row is a separate measurement the next brief can check.
- **ONE THING RESISTED, AND IT IS WORTH THE NEXT BRIEF'S ATTENTION.**
  **`InjL` IS NOT INJECTIVE FOR UNIFICATION.** `InjL a b` is
  `∥ Σ[ F ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`) and `InjCode`
  unfolds to a conjunction of satisfaction facts
  (`src/L/Cardinal.lagda.md:223-228`). When a transport helper leaves its two
  endpoints implicit, Agda unfolds `InjCode` and the endpoints end up under
  `FOL.Semantics.At.⟦_⟧`, where they cannot be solved. Two red runs measured
  it: `runs/stage-2.out` (exit 42, `[UnsolvedConstraints]`, the blocked
  constraints name `FOL.Semantics.At.⟦ ... ⟧` explicitly) and
  `runs/stage-2c.out` (exit 42, `[UnsolvedMetaVariables]` at the call site).
  **THE CURE IS TO WRITE BOTH ENDPOINTS OF EVERY `InjL` TRANSPORT.**
  `injL-recarry` (`Probe588.agda:247-252`) takes all four as EXPLICIT
  arguments for that reason.
- **THAT CURE COST ONE RE-TYPING, AND I NAME IT AS A DEBT.** Writing the
  endpoints needs a name for `[LJ-1.568]`'s `ordS` (`Probe568.agda:103-104`),
  and `[LJ-1.568]` takes the tower parameters, so at a QUANTIFIED α₀ there is
  no name for it. `isL-ord` and `ordS` (`Probe588.agda:104-108`) are re-typed
  for the reason `[LJ-1.561]` gives for re-typing the same three lines
  (`Probe561.agda:106-108`). **`generic-is-585s` (`Probe588.agda:232-237`) is
  the `refl` that keeps the re-typing honest**: if the copy were a different
  object the row would be exit 42.
- **ONE MORE RED RUN AND IT WAS THE SAME CAUSE.** `runs/stage-2b.out`, exit 42:
  making the equalities explicit was not enough while the endpoints stayed
  implicit.
- **NOTHING ELSE RESISTED.** No universe rose and no `refl` was expensive.
  `refl` occurs at seven lines (`Probe588.agda:163`, `:197`, `:237`, `:269`,
  `:294`, `:301`, `:338`). Three of them ASSERT an identity (`:163`, `:197`,
  `:237`) and each is at the level of type formers or hProp components. The
  other four fill a carrier equation that already holds by unfolding.
- **I WEAKENED NOTHING IN THE OBLIGATION.** The four rows other than row 4 are
  the predecessors' own types, imported. What I weakened is row 4 itself, and
  that is what the brief asked for.

### THE PRICE, MEASURED

| Run | File | Exit | Wall | Peak RSS |
|---|---|---|---|---|
| `runs/w3-1.out` | W3, first check on this pane | 0 | 32.96 s | 1,848,033,280 B |
| `runs/w3-2.out` | W3 | 0 | 3.03 s | 795,312,128 B |
| `runs/w3-3.out` | W3, after the citation fixes | 0 | 4.03 s | 861,700,096 B |
| `runs/stage-1.out` | probe, sections 0-1, first check | 0 | 139.01 s | 3,031,793,664 B |
| `runs/stage-2.out` | probe, RED | 42 | 19.16 s | 2,043,969,536 B |
| `runs/stage-2b.out` | probe, RED | 42 | 10.50 s | 2,067,890,176 B |
| `runs/stage-2c.out` | probe, RED | 42 | 10.62 s | 2,060,533,760 B |
| `runs/stage-2d.out` | probe, sections 0-3 | 0 | 14.18 s | 2,868,101,120 B |
| `runs/stage-3.out` | probe, whole file | 0 | 14.70 s | 2,889,170,944 B |
| `runs/final-1.out` | probe, whole file | 0 | 14.06 s | 2,889,170,944 B |
| `runs/final-2.out` | probe, whole file | 0 | 14.60 s | 2,889,187,328 B |
| `runs/final-3.out` | probe, whole file | 0 | 15.24 s | 2,889,187,328 B |

**EVERY FINAL RUN IS A REAL RECHECK.** `touch` does not force Agda to recheck,
because Agda keys the interface on content: three runs after a `touch` all read
3.36 s to 3.53 s and were interface loads, not checks. The three finals above
each ran with `_build/2.8.0/agda/agents/tasks/LJ-1-588/Probe588.agdai` REMOVED
first. **The 139.01 s of `stage-1` is the dependency chain's first check on
this pane and is not comparable with the finals.**

**NO HEAP WALL.** Peak RSS never passed 3.04 GB against the pane's `-M8g`.
**CALIBER: the program set `GHCRTS="-A64m -I0 -M8g"` on this pane. I did not
set it. One Agda process at a time throughout.**

**THE RATIO BAR DID NOT FIRE AND COULD NOT.** The write scope is a raw `.agda`
probe and three Markdown files. A raw probe carries no ` ```agda ` fence, so
the in-fence line count of this task's write scope is 0 and the bar has no
divisor. Nothing landed in `src/`.


## GATES RUN

`make check`'s `typecheck` target is `src/Everything.lagda.md` (`Makefile:50`,
`:26`) and this task changed no file under `src/`, so that target is
unaffected. The cheap gates were run and every one is clean:

- `scripts/gate/check-probes.py --check`: clean, 7263 tracked files, no probe
  outside `agents/tasks/`
- `scripts/gate/lint-agda.py --check`: clean, no output
- `scripts/gate/lint-prose.py --check`: clean, no output
- `scripts/gate/check-fences.py --check`: clean, 102 masters
- `scripts/gate/check-glossary.py --check`: clean, no output
- `scripts/gate/check-rule-ids.py`: clean, 56 files
- `scripts/measure/ledger.py --check`: declaration clean, standing 33,523
  lines over 100 masters
- `scripts/pod/check-closure.py --check closure`: clean, 102 masters
- `scripts/pod/check-spec-surface.py --check`: clean, 8 surface files
- `scripts/site/weave-i18n.py --check`: clean, no output
- `reuse lint`: compliant, 7075 / 7075 files

**I did not commit and I did not push.** `git status --porcelain` reads
`?? agents/tasks/LJ-1-588/` and nothing else. Three of the write scope's four
paths carry new files: `Probe588.agda`, `lj-1.588-report.md` and `runs/`.
**`review-of-gch-from-restricted-row4.md` was NOT written**, because the
obligation is inhabited and there is no stop to state.


## WHAT I COULD NOT CLOSE

1. **Whether `[LJ-1.584]`'s formula holds at EVERY tower.** The whole GO rests
   on it. If the formula can only be had at one α₀, `bound-bounds-every-cardinal`
   (`Probe588.agda:357-366`) is the price, and it is a row that bounds every
   infinite L-cardinal of L.
2. **Whether `BoundAtSucc α₀` is FALSE.** I did not refute it. I measured what
   it implies and stopped there. A refutation would need an L-cardinal above
   α₀, and nothing on this bill produces one at a named α₀.
3. **Row 4 at a finite δ.** Still open, and now off the GCH route.
4. **The other caller.** `power-into-succ` (`Probe564.agda:229-235`) reaches
   the same applying function WITHOUT `κ∉ω`. It is not on `gch-from-five`'s
   chain and I did not measure whether anything else needs it. **If a later
   task wires `PowerIntoSucc` (the unpremised form, `Probe564.agda:84-87`)
   into a route, condition one is NOT free there and this GO does not carry
   over.**


## C-42, THE SWEEP

`[LJ-1.585]` refuted my predecessor's reading at ONE site. C-42 says the next
action is the sweep and the COUNT before the cure. **The count is ONE.** There
is one application of row 4 in the campaign's bill
(`agents/tasks/LJ-1-564/Probe564.agda:210`), reached by one chain, and the
shape does not recur: `grep -c b9` over `Probe564.agda` returns 12 lines and
eleven of them are binders or pass-throughs. **A cure funded against that site
is funded against the whole bill.**


## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** Line 81 reads
  `| LJ-1.21 | Build: the carrier-level descent for the level size | DELIVERED, and it cost | StageCardinal 174 to 484 lines, 0.90 to 42.03 s. Init dropped, so every infinite alpha. LJ-1.25 cured it |`.
  "Init dropped, so every infinite alpha" is the record that
  `stage-card-upper`'s `δ ∉ ω` is the FUNCTION's own restriction from the day
  it was built, and not a condition `[LJ-1.585]` added. That is why section 1
  of the probe treats the condition as the site's obligation and not as a
  defect.
- `archive/dev/JOURNAL.md`: **READ AND USED.** Line 940 reads
  `**And the shape question was never asked.** Both consumers are Σ-types that`.
  The paragraph at `:938-944` records that `src/L/StageCardinal.lagda.md:15-19`
  demands an injective `⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` and nothing more. That is why
  `P550.SqLaw α₀` (`Probe550.agda:82-87`) can fill the tower's `sq` slot with
  no coercion, which the module application at `Probe588.agda:95-96` then
  confirms by typechecking.
- `archive/dev/JOURNAL-archived.md`: **NOT USED.** Searched for
  `stage-card`, `StageCounted` and `StageCardinal`: no hit. Declined.
- `dev/ARCHIVE.md`: **NOT USED.** Searched for the same three terms: no hit.
  No module was retired by this task, so W4 has nothing to record here.
  Declined.
- `archive/dev/DECISIONS-archived.md`: **NOT USED.** 61 lines, no hit on the
  same three terms, and this task turns on no `D<n>` decision. Declined.


## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED.** Line 281 reads
  `(ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact`. The
  source states the stage-size equation FOR INFINITE α, which is the same
  restriction `stage-card-upper` carries as `δ ∉ ω`. So the restricted row is
  the textbook's own statement and the unrestricted row is stronger than the
  literature asks for. `:164-166` reads
  `The application of 5.5 in 5.6 is at the cardinal κ⁺ with α = κ: every`,
  which is the same assignment the spend site uses, at the SUCCESSOR cardinal.
- `dev/literature/truncation-and-selection.md`: **NOT USED.** Searched for
  `stage-card`, `successor cardinal`, `sucV`, `κ⁺` and `infinite`: no hit.
  Declined.
- `dev/literature/digest.md`: **NOT READ.** This task settles a scope question
  about one Agda term and needs no survey. Declined.
- `dev/literature/geology.md`: **NOT READ.** Set-theoretic geology bears on
  no row of this bill. Declined.
- `dev/literature/glossary-review-2026-08.md`: **NOT READ.** No glossary term
  was added or renamed by this task. Declined.
