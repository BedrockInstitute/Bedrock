# review-of-LJ-1-584-1: the NO-GO of LJ-1.584#1 is UPHELD

## HEAD
verdict: upheld
head_slot: mathematician_adversarial
machine: shared
return under review: `agents/tasks/LJ-1-584/lj-1.584-report.md` (LJ-1.584#1, slot `coder`)
stop statement under review: `agents/tasks/LJ-1-584/review-of-stage-bound-definable.md`
invariant: the critic is not the author. This head did not write the return,
the stop statement, or the probe.

## WHAT THIS REVIEW DECIDES

The predecessor stated a NO-GO on `stage-bound-definable`. It left the probe
green without that name, proved that every value of `stage-card-upper` is a
value of the module parameter `sq`, and named three reopeners. I attack that
return on the three questions of this brief. Result: the verdict line and the
body agree, the obligation is unbound in the machine record, and the block at
`sq` resolves today. Two citation slips in the stop statement, and one
incomplete producer sentence, do not inhabit the obligation. The NO-GO is
UPHELD.

## INPUTS

- `agents/tasks/LJ-1-584/lj-1.584-report.md`, read in full.
- `agents/tasks/LJ-1-584/LJ-1.584.md`, read in full.
- `agents/tasks/LJ-1-584/review-of-stage-bound-definable.md`, read in full.
- `agents/tasks/LJ-1-584/Probe584.agda`, 291 lines, read in full.
- `agents/tasks/LJ-1-584/runs/accept-1.out`, and the run artefacts the
  return names.
- The transitions record this brief names does not resolve in this worktree.
  `dev/pod/transitions/2026-08.jsonl` ends at line 157, seq 158, task
  `LJ-1.399`, ts `2026-08-19T13:31:57Z`. No line carries `"task": "LJ-1.584"`,
  so `model`, `effort` and `heads_sha256` of LJ-1.584#1 were not readable.
  The six facts of the run under attack are taken from
  `agents/tasks/LJ-1-584/runs/accept-1.out`. No load-bearing claim of the
  return cites the transitions file.

## QUESTION 1. DOES THE VERDICT LINE MATCH ITS OWN BODY

The line (`agents/tasks/LJ-1-584/lj-1.584-report.md:8` and `:30`):
`verdict: NO-GO`, and `NO-GO on stage-bound-definable`. The stop statement
opens with the same words (`review-of-stage-bound-definable.md:1`).

The body is that same verdict at a finer grain. The obligation name
`agents/tasks/LJ-1-584/Probe584.agda::stage-bound-definable` has no term.
A search of the probe for that name as a binder returns none. What stands in
its place is a type `Obligation` (`Probe584.agda:95-99`) and a reduction
`vl→obligation` (`:108-119`) that carries `((x : V ℓ) → ⟨ isL x ⟩)` to the
left of the arrow. The return refuses to offer that reduction as the
obligation (`lj-1.584-report.md:40-43`,
`review-of-stage-bound-definable.md:27-31`).

The probe being green does not contradict the line. The return states the
green as deliberate (`lj-1.584-report.md:35-36`): every reduction is then a
measurement. The accept arm of this checkout agrees with that machine state
and not with a discharge:

- `exit_code: 42`
- `obligations_delta: 0`
- `obligations_open: 1`
- `heap_wall: false`
- `error_class: unsolved_meta`
- `unbound_vacuous: true`

(`agents/tasks/LJ-1-584/runs/accept-1.out:10-23` and the JSON object at
`:25`). The probe run on that arm is `rc 0` in 3.33 s. The `unsolved_meta`
and the exit 42 come from `runs/Floor.agda` (`rc 42` in 3.28 s), which keeps
the D-10 hole (`runs/Floor.agda:44`). That hole is not an inhabit of the
named obligation.

This is not the defect class the project measured on 2026-08-16. A line that
said GO while the body left the obligation open, or a line that said NO-GO
while the body inhabited it, would be that class. Here the line and the body
assert the same verdict: the name is missing, the probe is green, the
statement is not refuted, and `L.StageCardinal` cannot build it.

One count mismatch sits inside the pair and does not move the line. The stop
statement says three green runs (`review-of-stage-bound-definable.md:7-8`).
The report says four (`lj-1.584-report.md:32-34`). `runs/final-4.out` exists
and prints `3.36 real` with `EXIT=0`. The extra run is a later warm check of
the same green file. It is not a fifth inhabit.

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A `file:line` THAT RESOLVES TODAY

I opened every citation the return and the stop statement spend on the
verdict. The block resolves. Two operational citations in the stop statement
do not resolve at the file they name. They are recorded below. They do not
carry the NO-GO.

### Claims that resolve

The obligation's type. `Obligation` at `Probe584.agda:95-99` is
`[LJ-1.568]`'s `Def` (`agents/tasks/LJ-1-568/Probe568.agda:189-190`) at
`a := LsetS α oα`, `b := ordS α oα`,
`g := fst (SC.Upper.stage-card-upper α oα α∈suc α∉ω)`. `stage-card-upper` is
`src/L/StageCardinal.lagda.md:564-566`. `Def` is imported, not restated
(`Probe584.agda:73`).

Not false. `vl→obligation` is `Probe584.agda:108-119`. It is
`[LJ-1.561]`'s `ambient-graph-isL` (`agents/tasks/LJ-1-561/Probe561.agda:171-176`)
followed by `[LJ-1.568]`'s `graph→def` (`Probe568.agda:368-374`).
`refuting-obligation-refutes-V=L` is `Probe584.agda:126-132`. Nothing on that
path is truncated.

The block theorem. `value-is-a-sq-value` is `Probe584.agda:200-213`. Its
proof is one projection of `leastOf`
(`src/L/WellOrder/Base.lagda.md:158-160`). `IsLeast P a` is
`⟨ P a ⟩ × _` at `:131`, so `fst (snd (leastOf ...))` is the predicate at
the least index. The predicate is `class-pred`
(`src/L/StageCardinal.lagda.md:319-324`), whose only occurrence of the value
is `B.pair m (cnt m φ) ≡ y`. `pair-is-sq` is
`agents/tasks/LJ-1-584/runs/W3a.agda:41-46` and is `refl`. `B` is
`Bound α oα infα (sq α α∈suc infα)` (`src/L/StageCardinal.lagda.md:283`).
`sq` is the module parameter at `:17-19`. The accept arm typechecked this
row (`accept-1.out:16`, `Probe584.agda rc 0`).

The pairing is `sq` applied. `Bound.pair` is
`src/L/StageCardinal.lagda.md:68-69`: `pair x y = fst pairing (x , y)`.
`limit-step` is `:396-403`. `step` is `:561-562`. `LimitStep.h` is
`:350-351`. Two of the three ingredients are internal: `D` is `defSet`
(`:400-401`), and `leastOf` is the ordinal order (`:258-259` in the
return's reading; the call site is `:351`).

Equivalence to a graph in L. `[LJ-1.568]`'s `def∥↔conclusion` is
`Probe568.agda:387-393`. `def-restricted` is `:252-253`. `weakest` is
`:377-381`. `obligation→graph` is `Probe584.agda:230-239`.

`[LJ-1.533]`'s wall. `agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`
reads "NONE. No term in `src/` and no term in any probe I read turns an
arbitrary ambient function into an `InjCode`." The stop statement cites
that pair as the wall at this site
(`review-of-stage-bound-definable.md:58-60`). The citation resolves. The
identification is the parameterized module, where `sq` is an arbitrary
injective pairing, not a named code.

No canonical `sq` at the consumer of `L.StageCardinal`.
`src/L/SquareLawClosed.lagda.md:325-328` is `sq-trunc-closed`, with result
`∥ sq δ ∥₁`. `src/L/StageBound.lagda.md:42` reads "Not inhabited" of
`SqCollect`. `bounded-from-trunc` is `:122-123`, a `PT.rec` into
`⟨ x ∈ˢ Lset κ ⟩`. `InjL` is `src/L/GCH.lagda.md:38`.

The reopener is weaker. `Reopener` is `Probe584.agda:250-251`. It takes
neither `α∈suc` nor `α∉ω`. `[LJ-1.580]`'s reopener sentence is
`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:117-124`. The
brief pinned `Def` at one named `g` (`LJ-1.584.md:11-16`). Those are
different types, and the two signatures in the probe show it.

The floor. `runs/floor-cold-1.out:17-18` is 14.66 s and 1,620,688,896 B,
exit 42 at the hole (`:14-16`). `runs/floor-warm-1.out:7-8` is 2.67 s and
814,432,256 B. `[LJ-1.559]`'s 1.39 s warm and 4.12 s cold sit at
`agents/tasks/LJ-1-559/lj-1.559-report.md:58-59`, and the "not the frame"
sentence is `:84`.

W3, type only. `runs/W3a.agda:36-37` re-ascribes `step`. `runs/w3a-1.out:4`
and `:22` are 1.22 s and `EXIT=0`. Peak RSS at `:5` is 313,917,440 B.

W3b does not terminate. `runs/w3b-1.out:1-4` is a 180 s bound that did not
reach an `EXIT=` line. `runs/w3-1.out:4-5` is 313.25 s real, killed,
`EXIT=143` at `:23`. The operator notes at `:25-26` record 98.8% CPU and
RSS pinned at 1,154,848 KB, with no allocation growth between the 03:58 and
04:56 samples.

C-42 parameter lines. I re-opened each cited site. `sq` is
`src/L/StageCardinal.lagda.md:17-19`, `src/L/BoundedSubset.lagda.md:1388-1390`,
`src/L/StageBound.lagda.md:67`. `absorbs` is
`src/L/BoundedSubset.lagda.md:1392`, `src/L/StageBound.lagda.md:69` and `:97`.
`ih` is `src/L/StageCardinal.lagda.md:281`. That is seven parameter lines
and three objects, as the table states
(`review-of-stage-bound-definable.md:106-110`). `branch` supplies `ih` at
`:534-536`. `absorbs` as `[LJ-1.580]`'s block is
`review-of-beta-into-alpha-coded.md:49-61`.

Premise 10. `agents/tasks/LJ-1-572/` does not exist in this tree. The
`no-go-stated` row is `dev/pod/table.toml:19147-19159` (the stop statement's
`:19146-19160` window includes the preceding `[[row]]` and the following
blank). The return relies on none of that premise
(`lj-1.584-report.md:205-209`).

Literature the return spends. `dev/literature/truncation-and-selection.md:146-148`
is the `hProp`-valued constraint on `leastOf`. `:83-84` is the cardinal
inequality as truncated existence. `:158-160` is Kraus, Escardó, Coquand
and Altenkirch Theorem 16. `archive/dev/JOURNAL.md:940` names the injective
pairing demand. `:1366-1367` names the endomap on `sq δ`.
`dev/literature/devlin-II5.md:156` is the size equation as a cardinal
equation.

Link arity. `LinkAt` is `agents/tasks/LJ-1-554/Probe554.agda:80-86`,
`Formula S 3`.

### Two citation slips that do not carry the verdict

The stop statement hangs the 98.8% CPU and 1,154,848 KB figures on
`runs/w3b-1.out` (`review-of-stage-bound-definable.md:153-156`). That file
has four lines and no such number. The figures live at
`runs/w3-1.out:25-26`. The report splits the two artefacts correctly
(`lj-1.584-report.md:109-113`). The conversion-loop warning survives at
the right file. It is not the block.

The stop statement says three green runs of the finished probe
(`review-of-stage-bound-definable.md:7-8`). The report and the accept
arm's changed-files list include `final-4.out`. The extra run is warm and
green. It does not inhabit `stage-bound-definable`.

### One producer sentence that is incomplete, and is not a cure

The stop statement says `sq` has a producer, truncated, and cites only
`src/L/SquareLawClosed.lagda.md:325-328`
(`review-of-stage-bound-definable.md:119-121`). At `Init` ordinals the
tree already has untruncated data: `via-col-square` is
`src/L/Ordinal/SquareLaw.lagda.md:960-961`, and `Initial.square` is
`:953-954`. That sentence of the return is therefore false at `Init`.

The miss does not inhabit `Obligation`. `via-col-square` is still an
ambient Agda function, `p ↦ fiber α (col∈α p) .fst` (`:945`). It carries
no `Formula`. Plugging it into `L.StageCardinal` at `Init` leaves
`value-is-a-sq-value` in force, with `sq` now a named construction and
still undescribed in the object language. That is reopen route 2 of the
return (`review-of-stage-bound-definable.md:132-139`), not a term this
probe hid.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

The obligation. One name is missing, `stage-bound-definable`. The probe
enumerates every term it did build. I checked each name against the file.

- `Obligation` (`Probe584.agda:95`)
- `vl→obligation` (`:108`)
- `refuting-obligation-refutes-V=L` (`:126`)
- `step` (`:143`)
- `pair-is-sq` (`:148`)
- `value-is-a-sq-value` (`:200`)
- `obligation→graph` (`:230`)
- `Reopener` (`:250`)
- `obligation∥→graph` (`:259`)

None of these is a hidden inhabit. `vl→obligation` and the two graph
lemmas carry extra hypotheses the obligation does not have. `Reopener` is
a different type.

The C-42 sweep of the named shape is complete at the seven lines above.
I grepped `_↪_` under `src/L/` for further module parameters of a bare
injection handed to a chapter with no `Formula`. The extra hits are
function arguments and local constructions (`comp-inj`, `mem-incl`,
`shift-at`, `κ-inj` as a lemma hypothesis in `L.SquareLawClosed`), not
a fourth chapter-level parameter of that shape. `Bound.pairing` at
`src/L/StageCardinal.lagda.md:65-67` is the same `sq` object applied
internally. It is not a fourth object.

The incomplete producer sentence under QUESTION 2 is the one enumeration
gap. It is the `Init` untruncated square, and it is not a cure.

No cure the return could have delivered was missed. Four candidates, and
why each is not a missed inhabit:

1. Write a `Formula S 3` for this `g` inside the parameterized module.
   `value-is-a-sq-value` plus `pair-is-sq` say every value is a value of
   an arbitrary ambient pairing. `Formula S 3` takes L-sets as constants
   (`Probe554.agda:80-86`, and the brief at `LJ-1.584.md:82-84`). An
   ambient Agda function is not an L-set. That is the construction gap
   the return measured. `[LJ-1.533]`'s wall is the same demand at a
   generic injection (`lj-1.533-report.md:42-43`).
2. Inhabit `Reopener` instead, `InjL (Lset α) α`. The return names that
   as reopen route 1 (`review-of-stage-bound-definable.md:127-130`). The
   work brief forbade row 1 and row 4 (`LJ-1.584.md:90-91`) and gave one
   obligation (`:40`). A target that quantifies over all codes cannot
   demand `stage-card-upper`. Delivering `Reopener` as
   `stage-bound-definable` would have been the 2026-08-16 line/body
   defect.
3. Instantiate `sq` with `via-col-square` at `Init` and describe that
   pairing. The return names a definable pairing as route 2 and prices it
   against nothing measured (`review-of-stage-bound-definable.md:132-139`).
   Kuratowski pairing in `src/V/Coding.lagda.md` does not land in `α`.
   `FOL.Count`'s square-scheme pairing is on `ℕ`, not on `α`. No
   `Formula` for an injective `⟪α⟫ × ⟪α⟫ → ⟪α⟫` sits in `src/` today.
   A measured cure does not transfer by analogy.
4. Lift `∥ sq δ ∥₁` by a weakly constant endomap. The return names that
   as route 3 and points at the archive that already named the probe
   (`archive/dev/JOURNAL.md:1366-1367`, Theorem 16 at
   `dev/literature/truncation-and-selection.md:158-160`). Amendment A21
   asks whether the return named the term and the probe. It named both.
   It did not write that probe, and the brief did not ask it to.

The brief did cause the outcome, and that is not a defect in the return.
The work brief's obligation is `Def` at one named `g`
(`LJ-1.584.md:11-16`). `[LJ-1.580]`'s reopener is an injection of
`Lset β` into `α`, truncated, with no named function
(`review-of-beta-into-alpha-coded.md:117-124`, and `:126-129` already
said that residue is not `[LJ-1.533]`'s wall). The predecessor measured
the gap instead of silently delivering the weaker type. W3 ordered `step`
re-ascribed alone first (`LJ-1.584.md:109-115`). The predecessor named
the term, wrote `runs/W3a.agda`, and typechecked it alone
(`runs/w3a-1.out`). A21 asks whether a mathematician's return named the
term and the probe. This return is a coder's, and it did both.

Treat the green probe as a GO: the accept arm still has
`obligations_open: 1` and `obligations_delta: 0`. The brief's GO branch
requires `obligations_delta_max = -1` (`LJ-1.584.md:128-136`). A green
file without the named term is the NO-GO the brief priced
(`LJ-1.584.md:122-123`).

## ARCHIVE USED

- `archive/dev/JOURNAL.md`. **READ.** `archive/dev/JOURNAL.md:940` reads
  "`src/L/StageCardinal.lagda.md:15-19` both demand an injective". The
  same entry at `:1367` reads "the next probe is named for it." Both
  lines resolve today. They corroborate reopen route 3 and the pairing
  shape. They do not inhabit `Obligation`.
- `archive/dev/ORCHESTRATION.md`. **DECLINED.** It is the archived
  process document. This review attacks a mathematical NO-GO and takes
  no rule from it. `archive/dev/ORCHESTRATION.md:1` was opened to
  confirm the file identity and was not used.
- `archive/dev/DD-archived.md`. **READ.** `archive/dev/DD-archived.md:35`
  reads "did the BRIEF cause the outcome". That is DD25's third lens
  question. It is how QUESTION 3 above reads the brief's named `g`
  against `[LJ-1.580]`'s reopener. The four questions are the lens. The
  three questions of this file are section 6.6's list.
- `archive/dev/PLAN-archived.md`. **DECLINED.** It is the archived
  construction registry. Live status is `dev/pod/screen.toml`. This
  review does not spend a PLAN row. `archive/dev/PLAN-archived.md:1`
  was opened to confirm the file identity and was not used.
- `dev/ARCHIVE.md`. **DECLINED.** No module was retired by the
  predecessor, and none is retired by this review. `dev/ARCHIVE.md:1`
  was opened to confirm the file identity and was not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **READ.** `dev/literature/devlin-II5.md:156`
  reads "|L_α| = |α| and |L_γ| = |γ|, so |γ| = |M| = |α| < κ, hence γ < κ and".
  The source states the stage bound as a cardinal equation, not as a
  named injection. That is the same asymmetry the return measures between
  `Obligation` and `Reopener`.
- `dev/literature/BIBLIOGRAPHY.md`. **DECLINED.** A source list for the
  rud route. This review does not fetch a primary text and adds no
  citation. Not used.
- `dev/literature/digest.md`. **DECLINED.** It pins the orthodox rud
  route. The obligation sits on the definable-power stage bound. Not
  used.
- `dev/literature/geology.md`. **DECLINED.** Set-theoretic geology:
  mantles, grounds, Usuba. No bearing on whether `stage-card-upper`
  has a `Formula`. Not used.
- `dev/literature/devlin-errata.md`. **DECLINED.** Documented error
  classes in Devlin. No erratum in that file is about the existence of
  an object-language formula for this pairing. Not used.
