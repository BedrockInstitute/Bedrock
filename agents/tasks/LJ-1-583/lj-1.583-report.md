# [LJ-1.583] Report: the sealed projections `[LJ-1.576]` could not answer

## HEAD
task: LJ-1.583
slot: coder
machine: shared
obligation: agents/tasks/LJ-1-583/Probe583.agda::sealed-gaps-closed
verdict: **GO, WITH ONE GAP THAT DOES NOT CLOSE. THE GAP COUNT IS THREE.
TWO CLOSE FROM `src/` MODULES THAT `[LJ-1.576]` DID NOT FIND. THE THIRD
IS NOT WHERE `[LJ-1.576]` PUT IT, AND IT DOES NOT WANT THE AMBIENT
`Inj` BACK.**

This report was written as a skeleton before any Agda and filled as each
answer landed (C-22, `dev/LESSONS.md:2297`). No commit, no push. I wrote only
inside `agents/tasks/LJ-1-583/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated and no hole is left, so every reduction in the
probe is a measurement and not a claim. The probe is a raw `.agda` file, carries
no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it.

**This worktree carries no `.venv`.** I ran every Python command as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter.

## D-10, THE GAP LIST, READ BEFORE ANY AGDA

The brief orders D-10 first, and it names W3 as the gap count itself: read
`agents/tasks/LJ-1-576/Probe576.agda:327-382`, say which of the five sealed
projections are terms and which are named gaps, and report the count before any
spend. **I did that read first and here is its result.**

**ALL FIVE ARE TERMS. NONE OF THE FIVE IS A HOLE.**

| projection | `Probe576.agda` | state |
|---|---|---|
| 1 `κ₁` | `:333-334` | term, unconditional |
| 2 `κ₂` | `:339-341` | term, unconditional |
| 3 `κ₃` | `:344-345` | term, unconditional |
| 4 `κ₄` | `:353-354` | term, **UNDER A HYPOTHESIS** |
| 5 `κ₅` | `:360-378` | term, **AT A WEAKER TYPE** |

**SO THE GAPS ARE NOT HOLES IN THE FIVE. THEY ARE THREE NAMED TYPES BETWEEN THE
FIVE AND THE SEAL, AND THE COUNT IS THREE.**

| gap | what it gates | the binder or the antecedent | the type |
|---|---|---|---|
| A | ALL FIVE | `Probe576.agda:327`, the `ne` binder | `Probe576.agda:421-422` |
| B | projection 4 | `Probe576.agda:353`, `κ₄`'s antecedent | `Probe576.agda:239-240` |
| C | projection 5's three call sites | `Probe576.agda:360` | `Probe576.agda:394-395` |

`CodeUnique` (`Probe576.agda:90-91`) and `AmbientCoded` (`:282-283`) are NOT in
this list. The first is not expected to hold and gates nothing. The second gates
`[LJ-1.576]`'s section 4 EQUALITY of the two selections and not any of the five.
Both are imported by name into the probe (`Probe583.agda:47-49`), so this task
names them and does not silently drop them.

**I REPORTED THE COUNT BEFORE I SPENT.** The read is one file and it took under
ten minutes, which is what the brief estimated.

## THE FIVE, ONE ROW EACH

| projection | `src/L/SquareLawClosed.lagda.md` | after `[LJ-1.576]` | after THIS task | evidence |
|---|---|---|---|---|
| 1 `κL` | `:74` | term, gated by `ne` | **CLOSED. Unconditional** | `Probe583.agda:133-134`, `:145-146` |
| 2 `κoL` | `:77` | term, gated by `ne` | **CLOSED. Unconditional** | `Probe583.agda:133-134` |
| 3 `κ∈sucL` | `:80` | term, gated by `ne` | **CLOSED. Unconditional** | `Probe583.agda:133-134` |
| 4 `κ-injL` | `:84` | term, gated by `ne` AND by `BoundedCode` | **NOT CLOSED. `ne` goes, `BoundedCode` stays** | `Probe583.agda:259-266` |
| 5 `κ-min-atL` | `:89` | term, gated by `ne`, weaker than `src/`'s | **CLOSED as a term. Its DOWNSTREAM bill is paid for two of three sites** | `Probe583.agda:148-152`, `:169-180`, `:182-187` |

**GAP A CLOSES, SO ONE TERM MOVES FOUR ROWS.** `nonemptyᶜ`
(`Probe583.agda:133-134`) discharges the `ne` binder at EVERY α, so projections
1, 2, 3 and 5 lose their hypothesis. `module FiveAt` (`Probe583.agda:139-152`)
is that discharge applied, and it re-uses `[LJ-1.576]`'s own terms rather than
reproving them.

**PROJECTION 4 KEEPS ONE HYPOTHESIS AND THAT IS GAP B.** It is the only row of
the five that this task leaves open, and section 4 of the probe measures why.

## GAP A. IT CLOSES, AND `[LJ-1.576]` MEASURED THE WRONG `Carve`

`[LJ-1.576]`'s report reads: "`Carve` is hardwired to the shift formula
`shiftFo` (`src/L/Absorption.lagda.md:386`, and its carve reads
`sep bnd (shiftFo D γ ω z)` at `:413`), so it does not serve."

**THAT SENTENCE IS TRUE OF `L.Absorption.Carve` AND OF NO OTHER MODULE. THE TREE
HAS THREE MODULES CALLED `Carve`.** Measured, not assumed:

| module | at | its separation formula |
|---|---|---|
| `L.Absorption.Carve` | `src/L/Absorption.lagda.md:386` | `shiftFo` (`:413`) |
| `L.InjChain.Carve` | `src/L/InjChain.lagda.md:468` | **`inclFo`** (`:480`) |
| `L.Coding.Key.Carve` | `src/L/Coding/Key.lagda.md:258` | not this row's subject |

and `inclFo D = ∃̇∈ (con D) (prAtL (suc zero) zero zero)`
(`src/L/InjChain.lagda.md:446`) **IS the identity graph's formula.** The master's
own comment says so at `src/L/InjChain.lagda.md:439-442`, whose first line reads
"-- it: an inclusion IS the identity on its domain, so the codomain enters",
and which continues "the four conjuncts and not the formula.  That is why the
inclusion costs what the identity graph costs."

The L instantiation is `InclGraph D C sub` (`src/L/InjChain.lagda.md:575-598`),
which supplies the stage bound and `hasSeparationL` and nothing else. **At
`D = C = a` the subset witness is the identity function**, and the four conjuncts
come out at `γI = G ∷ D ∷ []` (`:516`) with `ran` into `C`
(`:544`). That tuple IS `InjCode G a a`. The term is three lines:

    idCoded : IdCoded
    idCoded a = ∣ IG.G , (IG.sv , IG.dm , IG.ij , IG.ran) ∣₁
      where module IG = InclGraph a a (λ _ z∈a → z∈a)

at `agents/tasks/LJ-1-583/Probe583.agda:123-126`, green.

**AND THE ARCHIVE RECORDED THIS FOUR HUNDRED TASKS AGO.**
`archive/dev/LJ-dispatch-index.md:230` reads
"| LJ-1.154 | Carve the identity graph by separation, not by replacement | GO: 1.73 s AGAINST 254.22 s | The device BUILDS, not only composes. Devlin's base theory has no replacement at all |".
`[LJ-1.576]` wrote "The coded form needs an L-ELEMENT that codes the identity on
α. That is a set to be carved, not a lambda." **The set was already carved.**

## GAP C. IT CLOSES, AND `comp-inj` WAS THE WRONG GREP

`[LJ-1.576]` measured: "the tree has no such term. `grep -rn "comp-inj :" src/`
returns THREE definitions, at `src/L/StageCardinal.lagda.md:500`,
`src/L/BoundedSubset.lagda.md:1365` and `src/L/SquareLawClosed.lagda.md:55`, and
every one of the three is at the AMBIENT `_↪_`."

**THE GREP IS RIGHT AND THE CONCLUSION IS TOO NARROW. The coded composite is not
called `comp-inj`.** It is `L.InjChain.Comp` (`src/L/InjChain.lagda.md:314-422`),
ROW 1 of that master, whose header at `:188` reads
"-- ROW 1.  The composition of two injection graphs, by separation."
It takes the four conjuncts of each factor as
module parameters (`:315-324`) and returns the four conjuncts of the composite at
`γK = K ∷ D ∷ []` (`:377-422`), with `ranK` into `C` (`:420`). **That tuple IS
`InjCode K a c`.** The term is six lines, at `Probe583.agda:169-180`, green.

`archive/dev/LJ-dispatch-index.md:446` records the landing:
"| LJ-1.279 | LAND A5 rows 5 and 1 as src/L/InjChain.lagda.md | LANDED GREEN, 343 LINES, 0.85x THE BAR | Six premises VERIFIED. A2's P-k boundary HELD: row 1 needs four names, all four exported |".

**AND TWO OF THE THREE `κ-min-atL` CALL SITES ARE NOW CLOSED OBJECTS AND NOT TWO
CITATIONS.** `src/L/SquareLawClosed.lagda.md:141` and `:156` both compose with
the shift, and `[LJ-1.576]` had already applied `shift-coded`
(`Probe576.agda:409-413`). Composing the two gives the site's whole second
factor:

    coded-shift-comp : ... → InjL α (sucʟ γ) → InjL α γ      Probe583.agda:182-187

**THE THIRD SITE, `src/L/SquareLawClosed.lagda.md:109`, IS NOT CLOSED**, and
`[LJ-1.576]` said why: its second factor is built from the SQUARE
(`src/L/SquareLawClosed.lagda.md:111-112`). `codedComp` is generic in the middle
set, so that site needs ONE coded factor and no new composition law. I wrote the
exact remaining ask as a type and did NOT inhabit it:

    SquareCoded : (κ β : S) → ⟪ fst κ ⟫ ↪ ⟪ fst β ⟫ → InjL κ β   Probe583.agda:195-196

## GAP B. IT DOES NOT CLOSE, AND THE GAP IS NOT WHERE `[LJ-1.576]` PUT IT

**THE MEASUREMENT.** `CodeBounded` (`Probe576.agda:239-240`) reads
`(a b : S) → InjL a b → CodeSelect.BoundedCode a b`, and `CodeSelect a b` opens
`SiteBound a` (`Probe576.agda:203`). **SO THE STAGE β IS A FUNCTION OF `a`
ALONE:**

- `SiteBound.β = stageBound (fst a) (snd a) .fst` (`src/L/Cardinal.lagda.md:165-166`);
- `stageBound a p = bound2 ω (stage a p) ω-ord (stage-ord a p)`
  (`src/L/Choice/Stage.lagda.md:366-368`);
- `bound2 σ₁ σ₂ o₁ o₂ : Σ[ β ∈ S ] (IsOrd β × ⟨ σ₁ ∈ˢ β ⟩ × ⟨ σ₂ ∈ˢ β ⟩)`
  (`src/L/Ordinal.lagda.md:185-186`), which says β is ABOVE its two arguments
  and says nothing else about it.

**A CODE OF AN INJECTION `a ↪ b` IS A SET OF PAIRS DRAWN FROM `a` AND `b`, SO
ITS STAGE READS `b`.** `src/` measures exactly that where it builds such a bound:
`PairBound D C` indexes on `Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫`
(`src/L/InjChain.lagda.md:279`) and hands that index type to `StageBound`
(`:293`). **The bound the code needs is a function of `a` AND `b`. The bound
`CodeSelect` offers is a function of `a` alone. Nothing in the tree makes them
one ordinal.**

**IT DOES NOT WANT THE AMBIENT `Inj` BACK, AND THE BRIEF ASKED ME TO SAY WHICH.**
The brief reads "IF A GAP NEEDS THE AMBIENT `Inj` BACK, SAY SO AND STOP." **NO
GAP DOES.** Projection 4 wants a STAGE BOUND ON THE CODE. No predicate in the
probe reintroduces `⟪ fst α ⟫ ↪ ⟪ fst γ ⟫`, and `κ₅` still refutes only a CODED
injection.

**WHAT IS PROVED INSTEAD, AND IT NARROWS THE GAP.** The selection never needed
`SiteBound`. `module CodeSelectAt (β : V ℓ) (oβ : IsOrd β) (a b : S)`
(`Probe583.agda:235-256`) is `[LJ-1.576]`'s section 3 with β as a PARAMETER, and
it delivers the same three terms, green:

    CodeSelectAt.chosen     : BoundedCodeAt → Σ[ F ∈ Mem (Lset β) ] IsLeast ...
    CodeSelectAt.bare-code  : BoundedCodeAt → Σ[ F ∈ S ] InjCode F a b
    CodeSelectAt.bare-inj   : BoundedCodeAt → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

So the gap moves from "a code at the β that `SiteBound a` names" to "a β,
computed from `a` and `b`, holding a code". That narrowed form is written and
**NOT inhabited**:

    StageOfCode : (a b : S) → InjL a b
                → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ] CodeSelectAt.BoundedCodeAt β oβ a b
                                                          Probe583.agda:259-262

**AND HERE IS WHY THAT TYPE IS THE WHOLE OF THE GAP, MEASURED AND NOT ARGUED.
ITS TRUNCATION IS INHABITED, WITH NOTHING ASSUMED:**

    stage-of-code-truncated : (a b : S) → InjL a b
      → ∥ Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ] CodeSelectAt.BoundedCodeAt β oβ a b ∥₁
                                                          Probe583.agda:269-280

green, built from `stage`, `stage-ord` and `stage-mem`
(`src/L/Stage.lagda.md:185-188`) and nothing else. **Every code always has a
stage. The Σ is not a proposition, so the stage cannot leave the truncation, and
`leastOf` needs it OUTSIDE. So the gap is the truncation boundary and it is not
existence.** The literature states the constraint that makes this decisive:
`dev/literature/truncation-and-selection.md:148` reads
"index is a proposition. **A data payload does not come out.**"

**AND CHOICE WOULD NOT PAY IT EITHER, WHICH MATTERS BECAUSE THE BRIEF FORBIDS
REACHING FOR ONE.** `dev/literature/truncation-and-selection.md:229-230` reads
"So AC delivers `∥ f ∥₁` for a selection function `f`, never `f`. **If the goal
that consumes `f` is not a proposition, AC does not help.**" I reached for no
choice principle, added no axiom and postulated nothing.

## WHAT ROW 2 NOW COSTS

`[LJ-1.576]` stated the bill as four items. **MEASURED AT TODAY'S TREE, TWO OF
THE FOUR ARE GONE AND THE REMAINING TWO ARE DIFFERENT SIZES.**

| item | `[LJ-1.576]`'s state | state after this task | evidence |
|---|---|---|---|
| 1 `IdCoded` | open, "a set to be carved" | **PAID** | `Probe583.agda:123-126` |
| 2 `CodeBounded` | open, "a reflection step" | **OPEN, AND RESTATED as `StageOfCode`** | `Probe583.agda:259-262` |
| 3 `CodedComp` | open, "the tree has no such term" | **PAID** | `Probe583.agda:169-180` |
| 4 the coded factor at `:109` | open, "the square" | **OPEN, as `SquareCoded`** | `Probe583.agda:195-196` |

**SO ROW 2 NOW COSTS TWO THINGS AND NEITHER IS A PRINCIPLE.**

1. **`StageOfCode`.** A β computed from `a` and `b`, with a code of `a ↪ b`
   inside `Lset β`, as DATA. This is projection 4 and nothing else.
2. **`SquareCoded`.** A coded factor at `src/L/SquareLawClosed.lagda.md:109`.
   This is projection 5's third call site and nothing else.

**AND ONE THING THE NEXT BRIEF MUST NOT ASSUME, WHICH `[LJ-1.576]` ALSO WARNED
ABOUT AND WHICH THIS TASK DID NOT TOUCH.** The restatement selects a possibly
LARGER κ. `AmbientCoded` (`Probe576.agda:282-283`) stays uninhabited here, so
`same-γ` (`Probe576.agda:298-313`) stays a debt. **`nonemptyᶜ` does not pay it.**

**DO NOT READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.** Five types are
named in `Probe583.agda` and none is inhabited: `CodeBounded`, `StageOfCode`,
`SquareCoded`, `AmbientCoded`, `CodeUnique` (`Probe583.agda:313-336`).
`SqCollectAt` is not stated in the file at all, and the brief forbids it.

## THE C-42 SWEEP

C-42 is in this task's law bundle: after a site-level finding the next action is
the sweep, with the COUNT reported before any cure is priced
(`dev/LESSONS.md:3752`).

**THE SHAPE IS NOT `Carve` AND IT IS NOT `comp-inj`. IT IS A REPORT THAT
CONCLUDED "THE TREE HAS NO SUCH TERM" FROM A GREP ON ONE NAME.** That is the
false shape this task found, and it is a shape a report can carry anywhere.

**THE SWEEP, OVER `[LJ-1.576]`'s OWN REPORT.** It named five uninhabited types.
Of those, **TWO are absence claims backed by a grep on one name**, and **BOTH ARE
NOW REFUTED**:

| claim | its grep | refuted by |
|---|---|---|
| `IdCoded`: "a set to be carved, not a lambda" | `Carve` at `src/L/Absorption.lagda.md:386` | `src/L/InjChain.lagda.md:575` |
| `CodedComp`: "the tree has no such term" | `grep -rn "comp-inj :" src/` | `src/L/InjChain.lagda.md:314` |

**THE COUNT IS TWO OF TWO.** The other three (`CodeUnique`, `AmbientCoded`,
`CodeBounded`) are not grep-backed absence claims: the first is a stated
expectation, and the last two are structural, so the sweep does not touch them.

**AND THE WIDER MEASUREMENT THAT MAKES THE SHAPE FALSE.** `grep` over every
top-level `module` header in `src/` returns **THREE modules named `Carve`**
(`src/L/Absorption.lagda.md:386`, `src/L/InjChain.lagda.md:468`,
`src/L/Coding/Key.lagda.md:258`). **So "the module named X is hardwired to Y" is
never a tree-wide claim in this repository.** The same sweep also counts the
builders of the four `InjCode` conjuncts: THREE carve them
(`src/L/Absorption.lagda.md:453-499`, `src/L/InjChain.lagda.md:518-547`,
`src/L/InjChain.lagda.md:380-422`), and `src/L/Cardinal.lagda.md:203-210`
selects them.

**I PRICE NO CURE FOR THE SHAPE ITSELF, AND THE RULE SAYS WHY.** `AGENTS.md:45`
reads "**A measured cure does not transfer by analogy.** Re-measure it at its own
site." **The count is the deliverable.**

## W2 (from DD4)

The brief carries no generic-carrier instruction. W2 says to write the
mathematics once at a generic carrier and instantiate it, and to answer it in the
return. **THIS TASK OBEYS W2 AND IT IS THE REASON GAPS A AND C COST THREE LINES
AND SIX.** Neither gap was written here at all: both are `src/` modules already
stated at a generic carrier, applied at this row's types.
`InclGraph D C sub` is generic in the two sets and the subset witness
(`src/L/InjChain.lagda.md:575-576`) and this task instantiates it at `D = C = a`
with the identity. `Comp D E C F H` is generic in three sets and two codes
(`src/L/InjChain.lagda.md:314`) and this task instantiates it at `a b c`.
`CodeSelectAt` (`Probe583.agda:235`) is the one thing this task GENERALIZED: it
takes β as a parameter where `[LJ-1.576]` took it from `SiteBound a`, so the
selection is now stated once for every stage. **No conflict with W2 arose and
there is nothing to report as a stop.**

## W3, THE WIDEST UNMEASURED TERM

The brief names it "the gap count itself" and calls it "the one W3 in the queue
whose value is a list rather than a type". **THE LIST IS THE `## D-10` SECTION
ABOVE AND IT WAS READ FIRST.**

**A LIST IS NOT A TERM, SO I WROTE W3's SECOND HALF AS ONE.**
`agents/tasks/LJ-1-583/runs/W3.agda` is the two module applications the list
points at, applied and not described: if either had failed to apply, the gap
list would have been wrong and everything after it wasted. **IT WENT GREEN ON
THE FIRST RUN**: exit 0, 1.64 s, 394 MB (`agents/tasks/LJ-1-583/runs/w3-1.out`).
No red taught anything here, which is itself the measurement: the two `src/`
modules fit the row's types with no adaptation at all.

**THE BRIEF ESTIMATED "one read, under 10 minutes". Measured: the read was under
ten minutes, and the 57-line confirmation file cost 1.64 s.**

## THE ESTIMATE AGAINST THE MEASUREMENT

The brief estimated "about 170 lines in the probe, of which the obligation is
about 45", and told me to report what I found before I spent. **Measured: 336
lines in `Probe583.agda`, of which 102 are code and 234 are comment or blank.
The obligation itself is 14 lines (`:296-310`).** The two closed gaps are 3 lines
and 6 lines of code. **THE FILE IS LONG BECAUSE THE GAP LIST AND THE GAP B
MEASUREMENT ARE WRITTEN INTO IT**, which is where a probe's value is once its
type has been checked.

## THE RUNS

| run | what | result |
|---|---|---|
| `runs/w3-1.out` | W3's second half ALONE, first attempt | exit 0, 1.64 s, 394 MB |
| `runs/p-1.out` | the whole probe, cold, first attempt | exit 0, 9.05 s, 1.05 GB |
| `runs/p-warm.out` | the whole probe, warm | exit 0, 1.57 s, 415 MB |
| `runs/witness-1.out` | the program's obligation meter | **0 UNRESOLVED of 1**, 1.62 s, `probe_red=False` |
| `runs/p-final.out` | the whole probe, FINAL file | exit 0, 1.85 s, 415 MB |
| `runs/witness-2.out` | the same meter against the FINAL probe | **0 UNRESOLVED of 1**, 1.88 s |

**NO RED IN THIS TASK, AND I REPORT THAT AS A FACT AND NOT AS A CLAIM OF SKILL.**
Both files went green on their first run. The reason is in the finding: gaps A
and C are `src/` modules applied, not new mathematics, so there was nothing for
the elaborator to reject.

**NO HEAP EVENT, AND I CHECKED RATHER THAN ASSUMED.** The largest resident set
was 1.05 GB against the 8 GB cap, on `p-1` (`runs/p-1.out`). **ONE Agda process
at a time throughout.** I did not set `GHCRTS`; every log records the caliber the
pane gave, `-A64m -I0 -M8g` (`runs/p-1.out:1`).

**THE COLD PRICE IS 9.05 s AND THE WARM PRICE IS 1.57 s.** The 7.5 s difference
is `L.Absorption`, `L.CodedShift` and `[LJ-1.576]`'s own probe, which this file
imports and which `runs/p-1.out:3-6` names.

## GATES

Clean on this tree, run with the pinned interpreter
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`:

- `scripts/gate/check-probes.py`: "check-probes: clean (7158 tracked files, no
  probe outside agents/tasks/ and no generated file)", exit 0
- `scripts/gate/lint-agda.py`: no output, exit 0, clean
- `scripts/gate/check-fences.py`: "check-fences: clean (102 masters, run
  threshold 3)", exit 0

I did not run `make check`: it is the gate before a commit, and I commit nothing.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED, AND IT IS THE FILE THAT
  ALREADY HELD GAP A'S ANSWER.** `archive/dev/LJ-dispatch-index.md:230` reads
  "| LJ-1.154 | Carve the identity graph by separation, not by replacement | GO: 1.73 s AGAINST 254.22 s | The device BUILDS, not only composes. Devlin's base theory has no replacement at all |".
  That row is `L.InjChain`'s inclusion carve, and it is exactly what closes gap A
  at today's tree. `:446` reads
  "| LJ-1.279 | LAND A5 rows 5 and 1 as src/L/InjChain.lagda.md | LANDED GREEN, 343 LINES, 0.85x THE BAR | Six premises VERIFIED. A2's P-k boundary HELD: row 1 needs four names, all four exported |",
  which is the landing of the master that closes gap C. `:371` reads
  "| LJ-1.314 | DD25 review of InjData's NECESSITY | SPLIT. THE RESIDUE IS NOT A NEW PRINCIPLE | Select the CODE, not the function: InjCode is a proposition, so leastOf untruncates it. Green probe |",
  the row the brief's premise 10 names, and this task does not re-open it:
  `[LJ-1.576]` already re-measured it green. **AND THE FILE RECORDS A RIVAL DOOR
  AT THE SAME WALL, WHICH A MATHEMATICIAN PRICING `StageOfCode` MUST KNOW.**
  `:373` reads
  "| LJ-1.316 | Literature for the InjData ruling | A DOOR NOBODY TRIED: rec-to-Set, not PT.rec | LJ-1.305 measured the WRONG eliminator. The criterion is a weakly constant endomap, Kraus Theorem 16 |"
  and `:376` reads
  "| LJ-1.319 | Fable RULING on InjData | NO PRINCIPLE, NO FORK, OPEN THE DOOR | sq-set is GREEN, so rec-to-Set applies and the necessity claim measured the wrong eliminator |".
  **I DID NOT TAKE THAT DOOR AND I SAY WHY**: `rec→Set` needs a weakly constant
  map, and two different codes read back as two different injections, so
  `readL` is not weakly constant. The brief names the coded route and I stayed on
  it.
- `archive/dev/JOURNAL-archived.md`. **SEARCHED, NOT USED FOR A MATHEMATICAL
  FACT.** Zero hits for `InclGraph`, `inclFo`, `InjChain`, `CodedComp`,
  `IdCoded` and `LeastCardInjL`. Its one on-topic hit is
  `archive/dev/JOURNAL-archived.md:1732`, which reads
  "plan rather than the target. The untruncated equivalence remains unavailable (T31's wall) and the".
  That is `[T31]`'s wall at an equivalence, not this row's wall at a stage bound.
  Declined.
- `archive/dev/JOURNAL.md`. **SEARCHED, NOT USED.** Zero hits for the six terms
  above. `archive/dev/JOURNAL.md:1` reads "# ARCHIVED 2026-08-20". Its nearest
  hits are its own audit of the truncation literature at `:1353` and `:1362`,
  which are line-citation corrections to
  `dev/literature/truncation-and-selection.md` and bind no mathematics of this
  row. Declined.
- `archive/dev/ORCHESTRATION.md`. **SEARCHED, NOT USED.** Zero hits for every
  term above and zero for `untrunc`, `truncat`, `inject` and `separation`.
  `archive/dev/ORCHESTRATION.md:1` reads
  "# ORCHESTRATION: the orchestrator's operating rules". It carries no
  mathematics. Declined.
- `archive/dev/DD-archived.md`. **READ, NOT USED FOR A MATHEMATICAL FACT, AND
  CHECKED AGAINST THIS TASK'S ORDER OF WORK.** Its one on-topic row is `DD28` at
  `archive/dev/DD-archived.md:38`, which begins
  "| DD28 | **A PROVABILITY PROBE SURVEYS THE LITERATURE FIRST, and the survey and the probe are ONE task.** | **Ruled 2026-08-16 by the owner.** Their instruction was that every probe about provability does the literature survey first".
  The series is SET ASIDE in this form (`dev/memos/LJ-4-pod-program-design.md`
  section 7.1), so it binds nothing here, and this task is not a provability
  probe. **I record it because gap B IS a provability question and the next brief
  about it may be one.** Declined as a rule.
- `dev/ARCHIVE.md`. **SEARCHED, NOT USED.** Zero hits for `InclGraph`, `inclFo`,
  `InjChain`, `CodedComp`, `IdCoded`, `Carve` and `LeastCardInjL`. This task
  retires no module and writes no `dev/ARCHIVE.md` row. Declined.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ AND USED, AND IT IS THE
  FILE THAT MAKES GAP B's MEASUREMENT DECISIVE.** Three citations, each verified
  at its line rather than copied: `:148` reads
  "index is a proposition. **A data payload does not come out.**"; `:229` reads
  "So AC delivers `∥ f ∥₁` for a selection function `f`, never `f`. **If the goal";
  `:158` reads
  "- **Theorem 16: \"A type X has a constant endomap if and only if it has split".
  The first is why `StageOfCode`'s Σ cannot leave the truncation. The second is
  why no choice principle would pay it, which the brief forbids reaching for
  anyway. The third is the criterion the archive's rival door needs, and it is
  why I did not take that door: `readL` is not weakly constant.
- `dev/literature/devlin-II5.md`. **SEARCHED, NOT USED, AND THE DECLINE IS
  DELIBERATE.** `dev/literature/devlin-II5.md:1` reads
  "# Devlin II.5: the Condensation Lemma and the GCH in L". Gap B is a stage
  bound on a set of pairs, and the condensation lemma is the classical instrument
  for stage bounds, so this file is the nearest neighbour this task has.
  **I DID NOT USE IT AND I SAY WHY: the brief gives this task ONE obligation and
  forbids `SqCollectAt`, so pricing a condensation route is a mathematical
  judgement and it is not mine (AD3).** Zero hits for `InjCode`, `untrunc` and
  `composition`. Declined.
- `dev/literature/digest.md`. **SEARCHED, NOT USED.** `dev/literature/digest.md:1`
  reads
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  Its `composition` hits (`:30`, `:34`, `:125`, `:173`) are the rudimentary
  function list closed under composition, which is a different notion of
  composition from `L.InjChain.Comp`'s. Row 2 is not on the rud route. Declined.
- `dev/literature/geology.md`. **SEARCHED, NOT USED.** Zero hits for `InjCode`,
  `identity graph`, `stage`, `untrunc` and `composition`.
  `dev/literature/geology.md:1` reads
  "# Geology dossier: set-theoretic geology sources and the five questions".
  Set-theoretic geology is not this row's subject. Declined.
- `dev/literature/terms-2026-08.md`. **SEARCHED, NOT USED.** Zero hits for the
  same five terms. `dev/literature/terms-2026-08.md:1` reads
  "# The terminology dossier: fourteen renderings for the owner's ruling".
  This task adds no term and I added no `dev/glossary.toml` entry. Declined.

## WHAT THE NEXT BRIEF NEEDS

**ROW 2's REMAINDER IS TWO OBLIGATIONS AND NEITHER IS A PRINCIPLE.**
`StageOfCode` (`Probe583.agda:259-262`) and `SquareCoded`
(`Probe583.agda:195-196`). Everything else `[LJ-1.576]` listed is paid.

**I RECOMMEND `StageOfCode` IS THE NEXT OBLIGATION AND `SquareCoded` WAITS**,
because `StageOfCode` alone decides whether projection 4 comes out bare, and
projection 4 is the whole gain of the row. `SquareCoded` only pays one of three
call sites of a projection that already has a term. **I did not price
`StageOfCode`. That is a mathematical judgement and it is not mine (AD3).**

**AND ONE WARNING ABOUT HOW TO SPECIFY IT.** `StageOfCode` as written asks for β
as DATA. `stage-of-code-truncated` (`Probe583.agda:269-280`) proves the truncated
form is free, so a brief that asks for the truncated form asks for nothing. **The
next brief must state which side of the truncation it wants, and it wants the
data side.**

**AND ONE THING THIS TASK MEASURED ABOUT REPORTS, WHICH IS NOT MATHEMATICS.**
Two of `[LJ-1.576]`'s three gaps were already built in `src/`, and both were
missed because a name was grepped instead of a shape. **A brief that asks a coder
to build a term should name the SHAPE, so the coder greps for the shape and finds
what the tree has.**

## FILES

| path | state |
|---|---|
| `agents/tasks/LJ-1-583/Probe583.agda` | NEW, 336 lines, green, no postulate, no hole |
| `agents/tasks/LJ-1-583/runs/W3.agda` | NEW, 57 lines, green, W3's second half alone |
| `agents/tasks/LJ-1-583/runs/run.sh` | NEW, the one-process harness, copied from `[LJ-1.576]` |
| `agents/tasks/LJ-1-583/runs/*.out` | NEW, 6 logs, every run of this task |
| `agents/tasks/LJ-1-583/review-of-sealed-gaps.md` | NEW, the NO-GO on gap B |
| `agents/tasks/LJ-1-583/lj-1.583-report.md` | NEW, this file |

Nothing under `src/` is touched. The working tree holds one untracked directory,
`agents/tasks/LJ-1-583/`, and nothing else.
