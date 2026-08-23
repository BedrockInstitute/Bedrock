# [LJ-1.576] Report: `LeastCardInjL` over the CODE

## HEAD
task: LJ-1.576
slot: coder
machine: shared
obligation: agents/tasks/LJ-1-576/Probe576.agda::least-card-inj-coded
verdict: **GO, WITH A CORRECTION. THE RESTATEMENT TYPECHECKS. IT DOES NOT
UNTRUNCATE BY ITSELF, AND THE SECOND `leastOf` DOES.**

This report was written as a skeleton before any Agda and filled as each answer
landed (C-22, `dev/LESSONS.md:2297`). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-576/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. Nothing is postulated and no hole is left, so every reduction in the
probe is a measurement and not a claim. The probe is a raw `.agda` file, carries
no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it.

**This worktree carries no `.venv`.** I ran every Python command as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter.

## VERDICT

**GO. `least-card-inj-coded` IS INHABITED AND IT IS GREEN.** The program's own
meter agrees and I ran it rather than predicting it: `0 UNRESOLVED of 1`,
`probe_red=False` (`agents/tasks/LJ-1-576/runs/witness-1.out:2`), and again
against the final file (`agents/tasks/LJ-1-576/runs/witness-3.out:2`). The probe
is green: exit 0, 5.19 s cold and 1.69 s warm
(`agents/tasks/LJ-1-576/runs/final-3.out`, `runs/final-5.out`).

**BUT THE BRIEF'S SENTENCE HAS TWO CLAUSES AND THEY LAND IN DIFFERENT PLACES.**
The brief asks for the restatement "so that `leastOf` untruncates the code and
`readL` reads it". **MEASURED: THAT IS TWO APPLICATIONS OF `leastOf`, NOT ONE.**
The restatement is the first. It untruncates NOTHING. The untruncation is a
SECOND `leastOf`, run over the CODE at a bounded stage, and W3 is what licenses
it. Section 3 of the probe is that correction, written into the file so that no
reader can take section 2 for more than it is
(`agents/tasks/LJ-1-576/Probe576.agda:168-199`).

**THE ROW IS NOT PAID AND I DID NOT ATTEMPT IT.** The brief forbids building
`SqCollectAt` and I built nothing of it.

## IS InjCode A PROPOSITION HERE

**YES. IT IS INHABITED AT TODAY'S TREE, AND HERE IS THE TERM:**

    isPropInjCode : (F a b : S) → isProp (InjCode F a b)

at `agents/tasks/LJ-1-576/Probe576.agda:77-84`, green. `[LJ-1.314]`'s archived
verdict therefore SURVIVES re-measurement. I did not assume it: the brief orders
D-10 first and `AGENTS.md:45` reads "**A measured cure does not transfer by
analogy.** Re-measure it at its own site."

**THE PROOF IS FOUR PROJECTIONS AND NOTHING ELSE.** `InjCode` has four conjuncts
(`src/L/Cardinal.lagda.md:224-228`). Three are `⟨ _ ⟩` of an hProp of the truth
algebra, so `snd` of that hProp is the proof. The fourth is a Π whose codomain
is `⟨ fst y ∈ fst b ⟩`, so `isPropΠ` three times over `snd (fst y ∈ fst b)`.
Nothing is assumed and `lem` is not spent.

**AND HERE IS THE DISTINCTION THAT DECIDES THE ROUTE, WHICH THE ARCHIVE'S ONE
LINE DOES NOT CARRY.** `isProp (InjCode F a b)` is NOT `isProp (Σ[ F ∈ S ] InjCode F a b)`.
`InjL a b` is the truncation of the Σ (`src/L/GCH.lagda.md:38`), so untruncating
`InjL` by unique choice alone would need the CODE to be unique, and two different
L-sets can code two different injections of `a` into `b`. I wrote that type down
and did NOT inhabit it:

    CodeUnique : Type (ℓ-suc ℓ)                         Probe576.agda:90-91

**WHAT `isPropInjCode` ACTUALLY BUYS IS THE PREDICATE OF A SECOND SELECTION.**
`leastOf` needs an hProp-VALUED predicate (`src/L/WellOrder/Base.lagda.md:158-160`).
`GoodF F = InjCode (up F) a b , isPropInjCode (up F) a b` is hProp-valued AND is
not a truncation, so `leastOf` hands the code back as DATA
(`Probe576.agda:201-222`). That is the archive's cure, as a term, at today's
tree.

## WHERE THE UNTRUNCATION IS, AND WHY SECTION 2 IS NOT IT

**`leastOf w lem P` RETURNS A BARE `a` AND A BARE `⟨ P a ⟩`.** When `P a` is
itself a truncation, the thing returned is still a truncation. The restated
predicate IS a truncation, because `InjL` already is one:

    InjPᶜ γ = InjL α γ , squash₁                        Probe576.agda:123-124
    κ-injᶜ : (ne : Nonemptyᶜ) → InjL α (κᶜ ne)          Probe576.agda:151-152

So the restated module's witness has the same grade of object as `src/`'s. The
literature says this in one line and I read it rather than deducing it:
`dev/literature/truncation-and-selection.md:146-148` reads "**The constraint the
route carries: `P` must be `hProp`-valued.** So `leastOf`" and continues
"delivers the least INDEX untruncated, and any payload it delivers with the
index is a proposition. **A data payload does not come out.**"

**THE SECOND `leastOf` IS WHERE THE DATA COMES OUT, AND THESE ARE THE TERMS:**

    CodeSelect.chosen    : BoundedCode → Σ[ F ] IsLeast (orderAt β oβ) GoodF F
    CodeSelect.bare-code : BoundedCode → Σ[ F ∈ S ] InjCode F a b
    CodeSelect.bare-inj  : BoundedCode → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

at `Probe576.agda:212-222`, green. `bare-inj` is `readL` applied to `bare-code`
(`src/L/CantorBernstein.lagda.md:33-35`). **NO CHOICE PRINCIPLE IS SPENT AND NO
AXIOM IS ADDED.** Only `lem`, which this chapter already takes.

**AT THE ROW'S OWN TYPES THAT IS `[LJ-1.573]`'s MISSING `BareLeastInj`:**

    bare-inj-at-coded-least :
      ... → CodeSelect.BoundedCode α (Coded.κᶜ α oα ne)
          → ⟪ fst α ⟫ ↪ ⟪ fst (Coded.κᶜ α oα ne) ⟫      Probe576.agda:229-233

`[LJ-1.573]`'s `BareLeastInj` is `(a : SL.S) (oa : IsOrd (fst a)) → ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫`
(`agents/tasks/LJ-1-573/Probe573.agda:183-185`).

**THE PRICE OF THE SECOND SELECTION IS THE BOUND, AND I NAME IT RATHER THAN HIDE
IT.** `leastOf` needs a well-order, and the only well-order on codes the tree has
is `orderAt β oβ` over `Mem (Lset β)` (`src/L/Choice/Step.lagda.md:730`). So the
code must be known to live in `Lset β`. `SiteBound a` produces a β above `a`'s
own stage and above ω (`src/L/Choice/Stage.lagda.md:366-368); it does not bound a
set of pairs drawn from `a × b`. The gap is written down and NOT inhabited:

    CodeBounded : (a b : S) → InjL a b → CodeSelect.BoundedCode a b   :239-240

**`src/` ITSELF ASSUMES THE SAME THING AT THE SAME PLACE**, so this is not a
defect of my construction: `InternalLeastCard.Selected` takes bounded
non-emptiness as a module hypothesis (`src/L/Cardinal.lagda.md:242-243`).

## DOES THE RESTATEMENT SELECT THE SAME γ

**IT DOES NOT, IN GENERAL, AND THE DIRECTION IS ONE-WAY. `[LJ-1.573]`'s WARNING
IS CORRECT.** The two selections run in ONE well-order, because section 2 takes
`w`, `up`, `self` and `self-eq` from `LeastCardInjL` itself rather than rebuilding
them (`Probe576.agda:112-113`). So what follows is a comparison and not an
analogy.

**ONE DIRECTION IS FREE.** `readL` under `PT.map` sends the coded predicate into
the ambient one, so the coded subset is inside the ambient subset:

    coded→ambient : (a b : S) → InjL a b → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁   :254-255
    coded⊆ambient : ... ⟨ Coded.InjPᶜ' α oα b ⟩ → ⟨ LeastCardInjL.InjP' α oα b ⟩  :259-262

Hence the ambient least is never strictly above the coded least, with NO
hypothesis:

    ambient-not-above : ... SWO._<∙_ w (Coded.γᶜ α oα ne) (LeastCardInjL.γ-card α oα)
                          → Empty.⊥                                     :268-276

**THE OTHER DIRECTION IS NOT FREE, AND THIS IS THE ANSWER THE BRIEF ASKED FOR.**
It needs every ambient injection between L-elements to carry a code. That is an
ABSOLUTENESS statement about L. I wrote it and did NOT inhabit it:

    AmbientCoded : (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁ → InjL a b    :282-283

Under that hypothesis, and only under it, the two selections agree, by
trichotomy of the shared well-order:

    coded-not-above : AmbientCoded → ...                                :285-296
    same-γ          : AmbientCoded → ... γ-card ≡ Coded.γᶜ α oα ne       :298-313

**SO THE HONEST STATEMENT IS: κᶜ ≥ κ ALWAYS, AND κᶜ = κ EXACTLY WHEN THE AMBIENT
INJECTIONS OF L-ELEMENTS ARE ALL CODED.** A restatement that selects a larger
object has changed the theorem, so a mathematician who takes this route must
either prove `AmbientCoded` or re-state every downstream consumer at κᶜ.

## WHAT ROW 2 NOW COSTS

**THE DOWNSTREAM BILL IS EXACTLY FIVE ITEMS AND NOT MORE, BECAUSE NOTHING
OUTSIDE ONE FILE READS THE MODULE.** Measured: `grep -rn "LeastCardInjL" src/ | wc -l`
returns 8. They are `src/L/Cardinal.lagda.md:61` (the module header),
`src/L/SquareLawClosed.lagda.md:37` (the import), `:65` (a comment) and `:74`,
`:77`, `:80`, `:84`, `:89` (the five sealed projections).

Each of the five is answered in `Probe576.agda:327-382` with a term or a named
gap:

| projection | `src/L/SquareLawClosed.lagda.md` | after the restatement | evidence |
|---|---|---|---|
| 1 `κL` | `:74` | DELIVERED, it is `Coded.κᶜ ne` | `Probe576.agda:333-334` |
| 2 `κoL` | `:77` | DELIVERED, `src/`'s own proof line for line | `:339-342` |
| 3 `κ∈sucL` | `:80` | DELIVERED | `:344-345` |
| 4 `κ-injL` | `:84` | **BARE, not truncated. THE GAIN** | `:353-354` |
| 5 `κ-min-atL` | `:89` | DELIVERED but WEAKER. **THE LOSS** | `:360-382` |

**PROJECTION 4 IS THE WHOLE POINT.** `[LJ-1.573]` measured that this one
truncation buys the entire truncation of `sq-trunc-closed`, and that four of the
five uses of `κ-injL` conclude a proposition so `PT.rec` pays them free
(`agents/tasks/LJ-1-573/lj-1.573-report.md`, the C-42 table). Under the
restatement it comes out bare, given the bound of section 3 and nothing else.

**PROJECTION 5 IS THE NEW BILL, AND IT IS ONE ITEM AND NOT THREE.** `κ-min-atL`
has THREE call sites, measured with
`grep -n "κ-min-atL" src/L/SquareLawClosed.lagda.md`: five lines, of which `:86`
and `:89` are the projection itself, so the sites are `:109`, `:141` and `:156`.
**ALL THREE HAVE THE SAME SHAPE.** Each feeds the minimality clause an AMBIENT
composite of the least-injection with a second injection, under `PT.map`:

| site | what it feeds | line |
|---|---|---|
| `:109` | `PT.map (λ iaκ → comp-inj iaκ κ↪β) κ-inj` | `:115` |
| `:141` | `PT.map (λ f → comp-inj f (... Shiftω.shift↪)) (κ-injL a oa)` | `:142-143` |
| `:156` | `PT.map (λ f → comp-inj f (... (shift-at γ oγ ω∈γ))) (κ-injL a oa)` | `:157-158` |

So the row acquires ONE new obligation, coded composition, and I wrote its type:

    CodedComp : (a b c : S) → InjL a b → InjL b c → InjL a c            :394-395

Measured: the tree has no such term. `grep -rn "comp-inj :" src/` returns THREE
definitions, at `src/L/StageCardinal.lagda.md:500`,
`src/L/BoundedSubset.lagda.md:1365` and `src/L/SquareLawClosed.lagda.md:55`, and
every one of the three is at the AMBIENT `_↪_`.

**AND TWO OF THE THREE SECOND FACTORS ARE ALREADY CODED IN `src/`.** `:141` and
`:156` both use the shift. `Shiftω` is `ShiftAbs ω ω-ord (∈-irrefl ω) #∈ω`
(`src/L/SquareLawClosed.lagda.md:117`) and `shift-at` is the same module at γ
(`:119-120`). `shift-coded` is built on `ShiftGraph`
(`src/L/Absorption.lagda.md:539-543`), which takes the SAME four hypotheses as
`ShiftAbs` (`src/L/Absorption.lagda.md:74-76`). So the coded second factor is
available at exactly the γ each call site already has. **I did not assert this: I
applied the term.**

    coded-shift-exists : ... → InjL (sucʟ γ) γ
    coded-shift-exists = shift-coded                                    :409-413

The remaining site, `:109`, is inside `clause4-at-kappa` and its second factor is
built from the SQUARE itself (`src/L/SquareLawClosed.lagda.md:111-112`). That one
wants the square coded and it is a different object. **I priced no cure for it.**

**AND THE NON-EMPTINESS IS THE THIRD ITEM, AND IT IS NOT FREE.**
`src/L/Cardinal.lagda.md:109-114` pays the ambient one with `idInj`, the ambient
identity, in two lines. The coded form needs an L-ELEMENT that codes the identity
on α. That is a set to be carved, not a lambda. `Carve` is hardwired to the shift
formula `shiftFo` (`src/L/Absorption.lagda.md:386`, and its carve reads `sep bnd (shiftFo D γ ω z)` at `:413`), so it does not serve. I
wrote the reduction and did NOT inhabit the antecedent:

    IdCoded            : (a : S) → InjL a a                             :421-422
    id-coded→nonempty  : IdCoded → (α : S) (oα : IsOrd (fst α))
                       → Coded.Nonemptyᶜ α oα                           :424-431

**THE BILL, STATED PLAINLY.** Row 2 through this route now costs four named
things and no principle:

1. `IdCoded`, or any coded injection out of α into a member of `sucV (fst α)`.
2. `CodeBounded`, the reflection of a code into one stage.
3. `CodedComp`, coded composition, for `κ-min-atL`'s three sites.
4. A coded second factor at `:109`, which is the square.

**AGAINST `[LJ-1.573]`'s PRICE THAT IS A DIFFERENT KIND OF DEBT.** Its price was
`SetChoice (ℓ-suc ℓ)`, which proves the excluded middle by Diaconescu
(`src/Base/Choice.lagda.md:16`) and would put a choice hypothesis on the front of
a trophy whose point is that choice is PROVED inside L. **The four items above
are constructions in `src/`, not principles.** Whether they are cheaper is not
measured here and I do not claim it. **What is measured is that they are of a
different kind.**

**DO NOT READ A DISCHARGE INTO ANYTHING I DID NOT INHABIT.** Five types are
written in the probe and none is inhabited: `CodeUnique`, `CodeBounded`,
`AmbientCoded`, `CodedComp`, `IdCoded`. `SqCollectAt` is not stated in the file
at all.

## W2 (from DD4)

The brief carries no generic-carrier instruction. W2 says to write the
mathematics once at a generic carrier and instantiate it. **THIS TASK OBEYS IT BY
NOT COPYING.** `Coded` opens `LeastCardInjL α oα` and REUSES `up`, `w`, `self`
and `self-eq` rather than rebuilding them (`Probe576.agda:112-113`), and
`CodeSelect` is stated once at a bound `(a b : S)` and instantiated at the row's
κᶜ (`:201`, `:233`). `κ₅` is `src/`'s own `κ-min-at` proof transported, not a
second proof (`:360-382`). **No conflict with W2 arose and there is nothing to
report as a stop.**

## W3, THE WIDEST UNMEASURED TERM

The brief names it "whether `InjCode` is an hProp at today's tree" and gives the
stub `-- isProp (InjCode F a b), at this frame, INHABITED or refuted`. **IT WAS
WRITTEN FIRST AND TYPECHECKED ALONE**, at `agents/tasks/LJ-1-576/runs/W3.agda`,
before any other Agda of this task.

**IT WENT RED ON THE FIRST RUN AND THE RED WAS TRIVIAL.** `isProp×` is not in
`Base.Prelude`'s re-export: `error: [NotInScope]`, exit 42, 1.81 s
(`agents/tasks/LJ-1-576/runs/w3-1.out:4-6`). I added
`open import Cubical.Foundations.HLevels using ( isProp× )` and it went green:
exit 0, 1.63 s, 384 MB (`runs/w3-2.out`).

**THE BRIEF ESTIMATED "about 12 lines, under 90 seconds". Measured: 60 lines and
1.63 s.** The line estimate was low because the import block and the written
reasoning are most of the file. The time estimate was generous. I report the
numbers I measured and not the numbers the brief guessed.

**IT DID DECIDE THE TASK, AND IT DECIDED IT TWICE.** Green, so `[LJ-1.314]`'s
cure is live at today's tree and the route is open. And writing it forced the
`isProp (InjCode ...)` against `isProp (Σ[ F ] InjCode ...)` distinction, which is
what put the untruncation at the SECOND `leastOf` rather than the first. That
distinction is the finding of this task. W3 also carries `CodeUnique` as a
TYPE ONLY, with no inhabitant (`runs/W3.agda:59-60`).

## THE C-42 SWEEP

C-42 is in this task's law bundle: after a site-level finding the next action is
the sweep, with the COUNT reported before any cure is priced
(`dev/LESSONS.md:3752`).

**THE SHAPE TO SWEEP IS NOT `LeastCardInjL`. IT IS `leastOf` APPLIED TO A
PREDICATE THAT IS A TRUNCATION OF A NON-PROPOSITION**, because that is the shape
whose selected witness cannot be used as data.

    grep -rn "leastOf" src/ | wc -l   ->  56

**MEASURED.** Of those 56, the rest are imports, comments, prose in
`src/Everything.lagda.md` and the definition itself in
`src/L/WellOrder/Base.lagda.md`. Removing those leaves 27 lines, of which two are
prose in `src/L/Choice/Finite.lagda.md` at `:1147` and `:1154`. **SO THE CALL
SITES ARE 25, OVER 14 PREDICATE DEFINITIONS.** Each predicate, classified by
reading its definition:

| predicate | defined at | a truncation | witness usable as data |
|---|---|---|---|
| `class-pred` | `src/L/StageCardinal.lagda.md:319-320` | **YES** | no |
| `P` (numeral) | `src/L/StageCardinal.lagda.md:443-445` | **YES** | no |
| `InjP'` | `src/L/Cardinal.lagda.md:82-83`, through `:67` | **YES** | **no. THIS ROW** |
| `Good` (Canonical) | `src/L/Cardinal.lagda.md:187-190` | no | yes |
| `Good` (Internal) | `src/L/Cardinal.lagda.md:240` | **YES** | no |
| `NP` | `src/L/Absorption.lagda.md:79` | no | yes |
| `cls` | `src/L/BoundedSubset.lagda.md:468-469` | **YES** | no |
| `_⊨₀_` at a formula | `src/L/Hull.lagda.md:81` | no | yes |
| `SatAt-h` | `src/L/Hull.lagda.md:380-383` | no | yes |
| `Cell` | `src/L/Choice/Transversal.lagda.md:200-201` | no | yes |
| `P` (pair) | `src/L/Ordinal/SquareLaw.lagda.md:535-537` | no | yes |
| `Pb` | `src/L/Ordinal/SquareLaw.lagda.md:790-791` | no | yes |
| `leastName` | `src/L/Choice/Name.lagda.md:812-814` | generic in `P` | its caller decides |
| `∈ˢ finiteStage` | `src/L/Choice/Finite.lagda.md:1002` | no | yes |

**THE COUNT IS FIVE.** Five predicate definitions carry the shape, and this row
is one of them. **ALL FIVE HAND THE TRUNCATED WITNESS ON TO A CONSUMER**, and I
checked each rather than assuming: `src/L/StageCardinal.lagda.md:358` and `:360`
(`pm = subst ... (fst (snd lx))`, `py = fst (snd ly)`),
`src/L/StageCardinal.lagda.md:456`
(`least-wit x x∈ = leastOf natOrder lem (P x) (nonempty x x∈) .snd .fst`),
`src/L/BoundedSubset.lagda.md:484`, `src/L/Cardinal.lagda.md:257-258`
(`δ-inj = fst (snd least)`) and this row's `src/L/Cardinal.lagda.md:133-134`
(`κ-inj = fst (snd least)`).

**BUT HANDING IT ON IS NOT THE SAME AS PAYING FOR IT, AND THIS IS WHERE THE
SWEEP STOPS.** A truncated witness is free wherever the consuming goal is a
proposition, because `PT.rec` absorbs it. `src/L/StageCardinal.lagda.md:354-361`
consumes it inside `h-inj`, whose goal is a path in an h-set, so that site pays
nothing. **WHETHER EACH OF THE OTHER FOUR PAYS IS NOT MEASURED IN THIS TASK.**
For this row it IS measured, and by a predecessor: `[LJ-1.573]` counted five uses
of `κ-injL`, of which four conclude a proposition and exactly one, `by-descent`
at `src/L/SquareLawClosed.lagda.md:318`, does not.

**I PRICE NO CURE FOR THE OTHER FOUR AND THE RULE SAYS WHY.** `AGENTS.md:45`
reads "**A measured cure does not transfer by analogy.** Re-measure it at its own
site." Each of the four has its own carrier, its own well-order and its own
payload. **The count is the deliverable. The cure is not.**

## THE ESTIMATE AGAINST THE MEASUREMENT

The brief estimated "about 180 lines in the probe, of which the obligation is
about 45". **Measured: 461 lines in `Probe576.agda`, of which 179 are code and
282 are comment or blank. The obligation itself is 4 lines** (`:162-165`), and
the module it names is 48 lines (`:110-157`). The file is long because the
reasoning is written into it, which is where a probe's value is once its type has
been checked.

## THE RUNS

| run | what | result |
|---|---|---|
| `runs/w3-1.out` | W3 ALONE, first attempt | **exit 42**, 1.81 s. `isProp×` not in scope |
| `runs/w3-2.out` | W3 ALONE, import added | exit 0, 1.63 s, 384 MB |
| `runs/s2-1.out` | sections 1 and 2, the obligation | exit 0, 1.75 s, 390 MB |
| `runs/s3-1.out` | section 3, the second `leastOf` | exit 0, 1.64 s, 392 MB |
| `runs/s4-1.out` | section 4, the comparison | exit 0, 1.60 s, 395 MB |
| `runs/s5-imports.out` | the four imports section 5 needs | exit 0, 6.16 s, 638 MB |
| `runs/s5-1.out` | section 5 added | **exit 42**, 5.22 s. `[UnsolvedMetaVariables]` |
| `runs/s5-2.out` | `Σ≡Prop` given its endpoints | exit 0, 4.37 s, 1.10 GB |
| `runs/final-1.out` | section 6 added | exit 0, 4.82 s, 1.32 GB |
| `runs/final-2.out` | after citation fixes | exit 0, 5.15 s, 1.10 GB |
| `runs/final-3.out` | own `_build` interfaces DELETED first | exit 0, 5.19 s, 1.10 GB |
| `runs/final-4.out` | warm | exit 0, 1.75 s, 407 MB |
| `runs/final-5.out` | warm, FINAL | exit 0, 1.69 s, 407 MB |
| `runs/witness-1.out` | the program's obligation meter | **0 UNRESOLVED of 1**, `probe_red=False` |
| `runs/witness-2.out` | the same meter, after the citation fixes | **0 UNRESOLVED of 1**, 1.83 s |
| `runs/witness-3.out` | the same meter against the FINAL probe | **0 UNRESOLVED of 1**, 1.66 s |

**THE ONE RED THAT TAUGHT SOMETHING IS `s5-1`.** `Σ≡Prop` cannot invert `fst`, so
it cannot infer its two endpoints from the path alone. Ascribing
`up-b≡δ : up b ≡ δ` fixes it. The measurement is written beside the term
(`Probe576.agda:369-373`), and it is the same idiom `src/L/CodedShift.lagda.md:48-49`
already uses.

**NO HEAP EVENT, AND I CHECKED RATHER THAN ASSUMED.** The largest resident set
was 1.32 GB against the 8 GB cap, on `final-1` (`runs/final-1.out`). **ONE Agda
process at a time throughout.** I did not set `GHCRTS`; every log records the
caliber the pane gave, `-A64m -I0 -M8g` (`runs/final-4.out:1`).

**THE COLD PRICE IS 5.19 s AND THE WARM PRICE IS 1.69 s.** The 3.4 s difference
is the four imports section 5 added, measured separately at `runs/s5-imports.out`:
sections 1 to 4 alone ran at 1.60 s.

## GATES

Clean on this tree, run with the pinned interpreter:

- `scripts/gate/check-probes.py`: "check-probes: clean (6855 tracked files, no
  probe outside agents/tasks/ and no generated file)"
- `scripts/gate/lint-agda.py`: no output, exit 0, clean
- `scripts/gate/check-fences.py`: "check-fences: clean (102 masters, run
  threshold 3)"

I did not run `make check`: it is the gate before a commit, and I commit nothing.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`. **READ AND USED, AND IT IS THE FILE THIS
  TASK RE-MEASURED.** `archive/dev/LJ-dispatch-index.md:371` reads
  "| LJ-1.314 | DD25 review of InjData's NECESSITY | SPLIT. THE RESIDUE IS NOT A NEW PRINCIPLE | Select the CODE, not the function: InjCode is a proposition, so leastOf untruncates it. Green probe |".
  **THE FIRST HALF OF THAT ROW IS CONFIRMED AT TODAY'S TREE AND THE SECOND HALF
  IS TOO NARROW.** `InjCode` IS a proposition (`Probe576.agda:77-84`), but
  `leastOf` untruncates the CODE'S EXISTENCE only when the code is bounded and
  the selection runs over the code, not when the selection runs over the target.
  `:362` reads
  "| LJ-1.305 | Untruncate the descent: deliver SqShape | NEEDS-A-PRINCIPLE: InjData, then GREEN | 322 lines, 4 s. Route 1 CLOSED by countermodel: sq omega is NOT an hProp. sq-initial is unconditional |",
  which is the same wall under the name `InjData`.
  **AND TWO LATER ROWS OF THE SAME FILE QUALIFY :371, WHICH THE BRIEF DOES NOT
  MENTION.** `:373` reads
  "| LJ-1.316 | Literature for the InjData ruling | A DOOR NOBODY TRIED: rec-to-Set, not PT.rec | LJ-1.305 measured the WRONG eliminator. The criterion is a weakly constant endomap, Kraus Theorem 16 |"
  and `:376` reads
  "| LJ-1.319 | Fable RULING on InjData | NO PRINCIPLE, NO FORK, OPEN THE DOOR | sq-set is GREEN, so rec-to-Set applies and the necessity claim measured the wrong eliminator |".
  So the archive records a SECOND door at this wall, `rec→Set`, which this task
  did not take because the brief names the coded one. I report it because a
  mathematician pricing the four items above should know a rival exists.
  `:380` reads
  "| LJ-1.325 | Re-price PLAN 0.0 against the restated trophy | MORE BY 600, AND 800 UNDER THE SURVEY | InjCode's four conjuncts are already PROVED in three modules and thrown away at the last step |",
  which is evidence for the coded route and not against it.
- `archive/dev/JOURNAL.md`. **SEARCHED, NOT USED.** Zero hits for `InjCode`,
  `LeastCardInjL`, `InjData` and `untrunc`. Declined.
- `archive/dev/JOURNAL-archived.md`. **SEARCHED, NOT USED FOR A MATHEMATICAL
  FACT.** Its one on-topic hit is `archive/dev/JOURNAL-archived.md:1732`, which
  reads
  "plan rather than the target. The untruncated equivalence remains unavailable (T31's wall) and the".
  That is `[T31]`'s wall at an equivalence, not this row's wall at an injection,
  and nothing in it binds this task. Declined.
- `dev/ARCHIVE.md`. **SEARCHED, NOT USED.** Its one hit is
  `dev/ARCHIVE.md:267`, the retirement row for `L.Rud.CodeSet`, whose cell reads
  in part "decode untruncated". That is the rud route's code family, not
  `InjCode`, and this task retires no module. Declined.
- `archive/dev/ORCHESTRATION.md`. **NOT USED.** Zero hits for every term above.
  It is the archived orchestrator operating rules
  (`archive/dev/ORCHESTRATION.md:1` reads
  "# ORCHESTRATION: the orchestrator's operating rules") and carries no
  mathematics. Declined.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ AND USED, AND IT IS THE
  FILE THAT NAMES THIS TASK'S CORRECTION.** Three citations, each verified at its
  line rather than copied:
  `:146` reads
  "**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`";
  `:148` reads
  "index is a proposition. **A data payload does not come out.**";
  `:297` reads
  "4. **Does `A` decompose as an index over a well-order plus a".
  The first two are exactly why section 2 untruncates nothing. The third is the
  checklist step the second `leastOf` of section 3 satisfies, with `InjCode` as
  the proposition-valued payload and `orderAt β oβ` as the well-order.
- `dev/literature/devlin-II5.md`. **SEARCHED, NOT USED.** Zero hits for
  `InjCode`, `leastOf`, `LeastCardInj` and `untrunc`. It is the Condensation
  Lemma and the GCH in Devlin II.5 (`dev/literature/devlin-II5.md:1` reads
  "# Devlin II.5: the Condensation Lemma and the GCH in L"). This task changed no
  mathematical target. Declined.
- `dev/literature/digest.md`. **SEARCHED, NOT USED.** Zero hits for the same four
  terms. `dev/literature/digest.md:1` reads
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  Row 2 is not on the rud route. Declined.
- `dev/literature/geology.md`. **SEARCHED, NOT USED.** Zero hits for the same
  four terms. `dev/literature/geology.md:1` reads
  "# Geology dossier: set-theoretic geology sources and the five questions".
  Set-theoretic geology is not this row's subject. Declined.
- `dev/literature/terms-2026-08.md`. **SEARCHED, NOT USED.** Zero hits for the
  same four terms. `dev/literature/terms-2026-08.md:1` reads
  "# The terminology dossier: fourteen renderings for the owner's ruling".
  This task adds no term and I added no `dev/glossary.toml` entry. Declined.

## WHAT THE NEXT BRIEF NEEDS

**THE ROUTE IS OPEN AND IT IS NOT ONE TASK.** The four items of "WHAT ROW 2 NOW
COSTS" are four different constructions in `src/`, and only the first of them,
`IdCoded`, is needed before the restatement is non-vacuous. **I recommend that
`IdCoded` is the next obligation and that nothing else is queued against this
route until it lands**, because if the identity code is expensive then the whole
route is, and the archive's `rec→Set` door (`archive/dev/LJ-dispatch-index.md:373`,
`:376`) becomes the cheaper question. **I did not price `IdCoded`. That is a
mathematical judgement and it is not mine (AD3).**

**AND ONE THING THE NEXT BRIEF MUST NOT ASSUME.** The restatement selects a
possibly LARGER κ. Any downstream statement about κ must be re-read at κᶜ, or
`AmbientCoded` must be proved. `same-γ` (`Probe576.agda:298-313`) is the exact
statement of that debt.

## FILES

| path | state |
|---|---|
| `agents/tasks/LJ-1-576/Probe576.agda` | NEW, 461 lines, green, no postulate, no hole |
| `agents/tasks/LJ-1-576/runs/W3.agda` | NEW, 60 lines, green, W3 alone |
| `agents/tasks/LJ-1-576/runs/run.sh` | NEW, the one-process harness, copied from `[LJ-1.573]` |
| `agents/tasks/LJ-1-576/runs/*.out` | NEW, 15 logs, every run of this task |
| `agents/tasks/LJ-1-576/lj-1.576-report.md` | NEW, this file |

**NO `review-of-*.md` IS WRITTEN.** This is a GO and the branch table's `go` row
does not carry one. Nothing under `src/` is touched. The working tree holds one
untracked directory, `agents/tasks/LJ-1-576/`, and nothing else
(`git status --porcelain` returns `?? agents/tasks/LJ-1-576/`).
