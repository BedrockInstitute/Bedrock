# lj-1.558-report: a route to GCHStatement that never lands inside Lset δ

## HEAD
head_slot: coder
task: LJ-1.558
obligation: agents/tasks/LJ-1-558/Probe558.agda::gch-route-without-stage
verdict: GO

## VERDICT

**GO. The stage landing is NOT forced by the target. One bridge put it
there.**

`scripts/pod/witness.py --brief` reports
`pass exit=0 1.52s agents/tasks/LJ-1-558/Probe558.agda::gch-route-without-stage`
and `witness: 0 UNRESOLVED of 1, 1.52 s, probe_red=False`
(`agents/tasks/LJ-1-558/runs/witness-2.out`, on the file as delivered).
The whole probe is green (`agents/tasks/LJ-1-558/runs/final-3.out`,
exit 0). Nothing is postulated,
there is no hole, and nothing lands in `src/`.

**READ THE GO WITH ITS SECOND HALF, WHICH IS IN
`## WHAT THE ROUTE RE-PRICES`.** A GO here does not say the ambient fact
is gone from the campaign. It says the ambient fact is not a demand of
`GCHStatement`, so it travels with whoever produces `PowerIntoSucc`, and
that producer is now a separately priced question and not a step of a
fixed bridge.

## WHERE THE STAGE LANDING CAME FROM

**THE STEP IS `Devlin55.BoundedSubsetAt.Co.theorem : ⟨ x ∈ˢ Lset κ ⟩`,
`src/L/BoundedSubset.lagda.md:1621`.** `[LJ-1.523]` restated it as the
codomain of `Tele.At` (`agents/tasks/LJ-1-523/Probe523.agda:139`).
`[LJ-1.550]` applied it at the assignment that serves the statement,
theorem-κ := `fst δ` and theorem-α := `fst κ`, and the result is
`UseSite.member-in-stage`
(`agents/tasks/LJ-1-550/Probe550.agda:257-261`), whose conclusion is
`⟨ fst y ∈ˢ Lset (fst δ) ⟩`.

**THE BRIDGE PUT IT THERE, NOT THE TARGET, AND THE REASON IS ONE LINE OF
`[LJ-1.550]`.** `agents/tasks/LJ-1-550/Probe550.agda:361-362` is

```
hard : InjL (𝒫 κ) δ
hard = r6 (𝒫 κ) Lδ δ (r5 (𝒫 κ) Lδ into) (b9 δ Lδ U.ordδ refl)
```

That is a composite `𝒫 κ` into `Lδ` into `δ` through a MIDDLE OBJECT,
and the middle object is `Lδ = Lset (fst δ) , r4 δ U.ordδ`
(`agents/tasks/LJ-1-550/Probe550.agda:358-359`). `into`
(`:354-356`) is the inclusion into that middle object, and `into` is the
ONLY consumer of `member-in-stage` in the whole of
`bridge-with-residues` (`:341-362`).

**`GCHStatement` NAMES NO MIDDLE OBJECT.** It names one arrow,
`InjL (𝒫 κ) δ` (`src/L/GCH.lagda.md:67`), beside `SuccCardL δ κ`
(`:66`) and `InjL δ (𝒫 κ)` (`:68`). The chapter says so at
`src/L/GCH.lagda.md:58`: "no ambient function type crosses the ⊨
boundary". So the middle object is a PARAMETER of the
route and the stage at δ is one value of that parameter.

**THIS IS MECHANICAL AND NOT A READING.** Section 5 of the probe builds
`stage-is-one-middle` (`agents/tasks/LJ-1-558/Probe558.agda:229-253`)
and then `bridge-is-this-route-at-the-stage` (`:255-261`), which is
`gch-route-via-any-middle` at that one instantiation.
`bridge-is-this-route-at-the-stage` and `[LJ-1.550]`'s
`bridge-with-residues` reach the same conclusion, and the difference
between their input lists is exactly `StageLanding`.

## THE HYPOTHESES OF THE ROUTE

`gch-route-without-stage`
(`agents/tasks/LJ-1-558/Probe558.agda:118-128`) has THREE hypotheses
and one module argument.

| # | Name | Type at | Ambient? |
|---|---|---|---|
| 0 | `zf : ModelL.isZFModel` | `Probe558.agda:119` | No. It is `GCHStatement`'s own argument (`src/L/GCH.lagda.md:59`), and B1 is paid: `L⊨ZFC : ... → isZFCModel (𝒮ʟ {ℓ})` (`src/Landmarks.lagda.md:76`) whose field `zf : isZFModel` (`src/FOL/ZFModel.lagda.md:421`) is this argument |
| 1 | `SuccCardExists` | `Probe558.agda:84-88` | No |
| 2 | `PowerIntoSucc` | `Probe558.agda:93-96` | No |
| 3 | `SuccIntoPower` | `Probe558.agda:99-102` | No |

**THE LIST IS EMPTY OF AMBIENT FACTS.** Not one of the three names an
ambient cardinality fact.

Hypothesis 1 is `[LJ-1.523]`'s B4 (`Probe523.agda:191-195`), copied
without a change. Every conjunct of `SuccCardL` is a type
`GCHStatement` already names: `IsOrd` (`src/L/GCH.lagda.md:48` and
`:62`), `IsCardinalL` (`:49` and `:63`), the V-membership (`:50`) and
the model's own `_⊆ˢ_` (`:51-52`, `src/FOL/ZFModel.lagda.md:141-142`). Hypotheses 2
and 3 are `GCHStatement`'s own second and third conjuncts
(`src/L/GCH.lagda.md:67-68`). Hypothesis 3 is `[LJ-1.523]`'s B10
(`Probe523.agda:266-268`), copied without a change. Hypothesis 2 is the
brief's own permission, in the brief's words: "You may take
`InjL (𝒫 κ) δ` and `InjL δ (𝒫 κ)` themselves as hypotheses".

**THE MECHANICAL CHECK, BECAUSE A TABLE IS A READING.** Two things must
hold: no ambient cardinality fact, and no conclusion inside
`Lset (fst δ)`. Both are settled by SCOPE and not by inspection.

1. `agents/tasks/LJ-1-558/Probe558.agda` never imports
   `L.BoundedSubset`. `IsCardinal` (`src/L/BoundedSubset.lagda.md:1046-1047`)
   and `_↪_` are therefore out of scope in the WHOLE probe, sections 4
   and 5 included.
2. `agents/tasks/LJ-1-558/runs/NoStage558.agda.txt` is sections 2 and 3
   copied letter for letter into a module whose `L.Constructible` import
   brings neither `Lset` nor `isL` nor `isL-trans`. It typechecks, exit 0
   (`agents/tasks/LJ-1-558/runs/nostage-1.out`). So no type written in
   the route names the stage at δ.
3. The control is not green by accident. Adding `IsCardinal` to that
   module gives `[NotInScope]`, exit 42
   (`agents/tasks/LJ-1-558/runs/nostage-neg-1.out`), and adding `Lset`
   gives `[NotInScope]`, exit 42
   (`agents/tasks/LJ-1-558/runs/nostage-neg-2.out`).

## W3, THE STAGE LANDING ALONE

The brief named the widest unmeasured term as the stage landing itself,
and ordered it written first and typechecked alone. That is
`StageLanding` (`agents/tasks/LJ-1-558/Probe558.agda:59-64`), TYPE ONLY.
The slice is kept at `agents/tasks/LJ-1-558/runs/w3-slice.agda.txt` and
its run is `agents/tasks/LJ-1-558/runs/w3-1.out`, exit 0, 1.52 s.

**WHAT ISOLATING IT MEASURED.** `StageLanding` drops the three slots
`[LJ-1.550]` found unfillable, because W3 asks what the step SAYS and
not what it costs. Once dropped, the step reads as one inclusion,
`𝒫 κ` into `Lset (fst δ)`. An inclusion is a candidate middle object and
nothing more. That is what made section 4 the right shape to write.

## THE C-42 SWEEP

`[LJ-1.550]` refuted ONE site. C-42 says the next action is the sweep
and the count, before any cure is priced.

**THE AMBIENT `IsCardinal` IS DEMANDED AT THREE TELESCOPE SITES IN
`src/`, AND ALL THREE CARRY THE SAME SHAPE.** The grep is
`IsCardinal ` minus `IsCardinalL` over `src/`: 5 hits, of which 2 are
the declaration (`src/L/BoundedSubset.lagda.md:1046-1047`).

| Site | Conclusion | Same theorem? |
|---|---|---|
| `src/L/BoundedSubset.lagda.md:1386` | `theorem : ⟨ x ∈ˢ Lset κ ⟩` (`:1621`) | `Devlin55.BoundedSubsetAt` |
| `src/L/StageBound.lagda.md:65` | `theorem : ⟨ x ∈ˢ Lset κ ⟩` (`:87`) | Yes, `module BSA = Devlin55.BoundedSubsetAt` at `:76` |
| `src/L/StageBound.lagda.md:94` | `go : SqFam α → ⟨ x ∈ˢ Lset κ ⟩` (`:111`) | Yes, it applies `Instantiation` |

**COUNT: 3 telescope sites, 1 independent theorem.** Every ambient
cardinality demand in `src/` is a stage-landing site, and every
stage-landing site is `Devlin55.BoundedSubsetAt`. So the shape
`[LJ-1.550]` refuted does not extend past the one theorem, and section 1
of this probe isolates exactly that shape.

## WHAT THE ROUTE RE-PRICES

The brief said a route re-prices the whole join and ordered its
hypotheses stated in full. They are stated above. Here is what moves.

**THE AMBIENT ROW LEAVES THE BRIDGE AND JOINS THE PRODUCER OF
`PowerIntoSucc`.** `[LJ-1.550]`'s R1, `AmbientCardAtSucc`
(`agents/tasks/LJ-1-550/Probe550.agda:301-302`), is spent at exactly one
place in `bridge-with-residues`: `:355`, inside `into`. `into` is what
section 1 of this probe replaces. So R1 sits behind `StageLanding` and
nowhere else on the route.

**`site-forced` STILL APPLIES, VERBATIM, TO ANYONE WHO CHOOSES THE STAGE
AS THE MIDDLE OBJECT.** `agents/tasks/LJ-1-550/Probe550.agda:385-389` is
not weakened by this task and I did not attack it. Its conditional is
intact: land the conclusion inside `Lset (fst δ)` and the ambient
hypothesis cannot be moved off the successor.

**AND THE CLASSICAL PROOF CHOOSES THE STAGE.** Devlin 5.6 is
`dev/literature/devlin-II5.md:159-160`: "5.6 Theorem. V = L implies
GCH." and "Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite cardinals κ."
`L_{κ⁺}` is the middle object, and 1.1(vii) is the cardinality step at
it. **I report this against my own GO, because it is the honest price:
the textbook route is the stage route, so a stage-free producer of
`PowerIntoSucc` is not a known thing that we merely have not written.**

**WHAT THE GO BUYS IS THEREFORE PRECISE AND IT IS NOT NOTHING.** Before
this task, the stage landing was a step of `[LJ-1.523]`'s bridge and the
only route the tree had, so `AmbientCardAtSucc` looked like a cost of
`L ⊨ GCH`. After it, the stage is a value of a parameter
(`Probe558.agda:163-168`), the bridge is that parameter at one value
(`:255-261`), and `AmbientCardAtSucc` is a cost of THAT VALUE. The
owner does not have to be told that `L ⊨ GCH` as stated needs an ambient
cardinality fact, because the statement does not.

**NO HIDDEN HYPOTHESIS.** Hypothesis 2 carries the whole hard leg and I
say so plainly. The task the brief set was whether an ambient
cardinality fact stands BETWEEN the two injections and `GCHStatement`.
It does not. Nothing here prices the two injections, and the brief
forbade that work ("DO NOT BUILD B9, B10 OR THE ASSIGNMENT").

## WHAT THE TREE HAS TOWARD `PowerIntoSucc` TODAY

Measured, because the next brief will want it. `InjL` is
`∥ Σ[ F ∈ S ] InjCode F a b ∥₁` (`src/L/GCH.lagda.md:37-38`), so a
producer of `InjL` is a producer of `InjCode`. There are TWO in `src/`:
`src/L/Absorption.lagda.md:614` and `src/L/CodedShift.lagda.md:40`.
**Both deliver the single shape `InjCode F (sucʟ γ) γ`.** Neither gives
`InjL (𝒫 κ) m` for any m at all. So `PowerIntoSucc` has no producer in
the tree today at ANY middle object, stage or not, and
`gch-route-via-any-middle` (`Probe558.agda:187-192`) is the type that
says what a producer would have to deliver.

`InjLTrans` (`Probe558.agda:158-159`) is `[LJ-1.550]`'s R6 and is still
open: `src/L/CantorBernstein.lagda.md` is the only consumer of `InjL` in
`src/` and it delivers `mutual-inj→bijection` (`:51-55`), not
transitivity.

## MEASUREMENTS

Caliber `GHCRTS=-A64m -I0 -M8g`, set by the program, never by me. One
Agda process at a time. No heap wall.

| Run | What | Exit | Wall | Peak RSS |
|---|---|---|---|---|
| `runs/w3-1.out` | W3, `StageLanding` alone | 0 | 1.52 s | 385 MB |
| `runs/obl-1.out` | sections 1 to 3, the obligation | 0 | 1.55 s | 399 MB |
| `runs/final-1.out` | the whole probe, sections 1 to 5 | 0 | 1.80 s | 392 MB |
| `runs/final-2.out` | the same, four citation lines corrected in a comment | 0 | 1.73 s | 392 MB |
| `runs/final-3.out` | **the file as delivered** | 0 | 1.74 s | 392 MB |
| `runs/nostage-1.out` | the route with `Lset` out of scope | 0 | 1.48 s | 408 MB |
| `runs/nostage-neg-1.out` | `IsCardinal` named there, must fail | 42 | n/a | n/a |
| `runs/nostage-neg-2.out` | `Lset` named there, must fail | 42 | n/a | n/a |
| `runs/witness-1.out` | the declared obligation | 0 | 1.54 s | n/a |
| `runs/witness-2.out` | the same, on the file as delivered | 0 | 1.52 s | n/a |

**THE OBLIGATION WAS GREEN ON THE FIRST CHECK.** `runs/obl-1.out` is
the first run of sections 1 to 3 and it is exit 0. No repair round. The
three `final-*` runs differ only in COMMENT text: `final-2` corrects four
citation line numbers in the section 2 comment and `final-3` closes a
backtick in the section 2 comment. No Agda term changed after
`final-1`.

Gates run: `check-probes.py` clean, `lint-agda.py` clean,
`check-spec-surface.py` clean, `check-fences.py` clean. `git status`
shows one untracked path, `agents/tasks/LJ-1-558/`, and nothing else.
Nothing is committed and nothing is pushed.

**THE RATIO BAR CANNOT FIRE ON THIS TASK.** The write scope holds no
`.lagda.md` master, so the in-fence line count is 0 and there is no
divisor. This is the rule as the brief states it, not a claim about the
bar's threshold.

## ESTIMATE AGAINST MEASURED

| Item | Estimate | Measured | Ratio |
|---|---|---|---|
| Probe, total lines | about 140 | 261 | 1.86 |
| The obligation | about 35 | 11 (`Probe558.agda:118-128`) | 0.31 |
| W3 slice | about 12 lines, under 60 s | 20 lines of section, 1.52 s | lines 1.67, time 0.03 |

**THE OBLIGATION CAME IN AT ONE THIRD OF THE ESTIMATE AND THE PROBE AT
NEARLY TWICE IT.** The estimate's basis was `[LJ-1.550]`, which rebuilt
one implication of the bridge. This task did not rebuild an
implication: the obligation is 11 lines because the target's conclusion
is a triple and the three hypotheses deliver its three components
directly. The overrun is sections 4 and 5, which the brief did not
order and which are not the obligation. They are 131 lines
(`Probe558.agda:131-261`) and they exist because the brief asked WHERE
the stage landing came from, and a typechecked instantiation answers
that better than my prose does.

## W2 AND W4

**W2.** The brief states no generic-carrier question and the route
raises none. `gch-route-via-any-middle` (`Probe558.agda:187-192`) is
already the generic form of section 3's route: the middle object is a
variable, and `stage-is-one-middle` (`:229-253`) is the instantiation.
That is W2's shape applied inside one probe, and it cost nothing extra
to write it that way.

**W4.** No module is retired by this task. Nothing moves to `archive/`
and nothing is deleted. `agents/tasks/LJ-1-558/runs/NoStage558.agda.txt`
is kept as a `.txt` so no sweep typechecks it, which is the shape
`[LJ-1.550]` used for `runs/Neg550.agda.txt`.

## WHAT THE NEXT BRIEF SHOULD KNOW

1. **The stop `[LJ-1.550]` recorded is narrower than it now reads.** It
   refutes the bridge, not the target. Do not report to the owner that
   `L ⊨ GCH` as stated needs an ambient cardinality fact. It does not:
   `gch-route-without-stage` is green with no ambient hypothesis.
2. **The whole question is now `PowerIntoSucc`**
   (`Probe558.agda:93-96`), and it has no producer in the tree at any
   middle object. Section "WHAT THE TREE HAS TOWARD `PowerIntoSucc`
   TODAY" gives the two `InjCode` producers and their single shape.
3. **A producer that goes through the stage pays R1 again.** That is
   `site-forced` and it is untouched. So the next mathematical question
   is whether a middle object other than `Lset (fst δ)` can carry
   `𝒫 κ` into `δ`, and Devlin 5.6 says the textbook does not offer one.
4. **`InjLTrans` is on the bill for the middle-object route and is
   open.** Any composite route needs it. A direct producer of
   `InjL (𝒫 κ) δ` does not.
5. **Two rows of `[LJ-1.550]`'s bill leave when the stage leaves.**
   `StageIsL` (R4) and `InclusionCoded` (R5) are consumed only by
   `stage-is-one-middle` (`Probe558.agda:233-253`). They are not on
   `gch-route-without-stage`'s bill and they are not on
   `gch-route-via-any-middle`'s bill either. So the stage instantiation
   costs R1, R2, R3, R4 and R5, and the parameterised route costs none
   of them.
6. **I did not prove B5 and I did not refute it.** The brief forbade
   both and I did not touch it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:165`. **READ.** The line reads
  `| LJ-1.90 | Instantiate BoundedSubsetAt for the first time | REACHES cardκ | Every other hypothesis takes a value, including AllCodes A in Lset lam. Nothing in the tree proves any set is a cardinal |`.
  It dates the ambient gap to the first instantiation of
  `BoundedSubsetAt` and ties it to that module, which is the C-42
  sweep's answer written down long before the sweep. And
  `archive/dev/LJ-dispatch-index.md:409` reads
  `| LJ-1.359 | Land the CSB corollary at the trophy's own InjL | LANDED GREEN, 34 LINES, exit 0 | The reader's step is now the tree's. It measured TWO of my citations FALSE, one of them stale |`,
  which is why I checked every `InjL` producer by grep and not by recall.
- `archive/dev/JOURNAL-archived.md`. **NOT READ.** Declined. Grep for
  `GCHStatement`, `SuccCardL`, `middle object` and `Lset (fst δ)`
  returns 0 hits, and the live evidence for this task is two probes and
  two chapters, all cited by `file:line`.
- `archive/dev/JOURNAL.md`. **NOT READ.** Declined, same grep, 0 hits.
- `dev/ARCHIVE.md`. **NOT READ.** Declined, same grep, 0 hits. This task
  retires no module, so it has no row to write there.
- `archive/dev/ORCHESTRATION.md`. **NOT USED.** Declined. It is the
  archived flow document and carries nothing about `GCHStatement` (same
  grep, 0 hits).

## LITERATURE USED

- `dev/literature/devlin-II5.md:159`. **READ, AND IT CHANGED THE
  REPORT.** The line reads `> 5.6 Theorem. V = L implies GCH.`, and
  `dev/literature/devlin-II5.md:160` reads
  `> Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all infinite cardinals κ. So by 1.1(vii),`.
  This is the finding I report against my own GO: the classical route's
  middle object IS the stage, so a stage-free producer of
  `PowerIntoSucc` is not something the sources hand over.
- `dev/literature/truncation-and-selection.md:83`. **READ.** The line
  reads
  `**So a proof that only needs cardinal arithmetic never needs an injection as`.
  This is why `MiddleAtSucc` (`Probe558.agda:163-168`) is a TRUNCATED Σ
  over the middle object and why `hard-from-middle` (`:175-184`) may use
  `PT.rec` into `InjL`: the target is truncated all the way down, so the
  middle object never has to be produced as data.
- `dev/literature/digest.md`. **NOT READ.** Declined. Grep for
  `GCHStatement`, `SuccCardL`, `middle object` and `Lset (fst δ)`
  returns 0 hits, and its GCH content is scope rulings about other
  formalizations, which price nothing here.
- `dev/literature/geology.md`. **NOT READ.** Declined, same grep, 0 hits.
  It is set-theoretic geology and no step of this task touches it.
- `dev/literature/terms-2026-08.md`. **NOT READ.** Declined, same grep,
  0 hits. This task adds no term and clause W5 is not in play.
