# LJ-1.600 report: `keyS` at this carrier

Status: COMPLETE. GO. No commit, no push. ASD-STE100.

## THE VERDICT

**GO.** The obligation `agents/tasks/LJ-1-600/Probe600.agda::key-at-stage`
IS in the probe, at `agents/tasks/LJ-1-600/Probe600.agda:129-130`, with its
type written out at the concrete carrier:

    key-at-stage : (δ : V ℓ) (oδ : IsOrd δ) {n : ℕ} → Formula ⟪ Lset δ ⟫ n → S
    key-at-stage δ oδ = keyS (LsetS δ oδ)

This is `keyS` of the LIVE chapter `src/L/Coding/CodeSet.lagda.md`
(`:300-301`) instantiated at `A := LsetS δ oδ`
(`src/L/Axioms/Basic.lagda.md:160-161`), which is ingredient (v) of the
`class-pred` formula at this carrier: the coded copy of the meta syntax the
existential ranges over. Nothing landed in `src/`. Nothing was postulated.
The probe carries no hole. `review-of-key-at-stage.md` is NOT written,
because there is no stop to state.

The probe is GREEN, EXIT 0, SIX RUNS
(`agents/tasks/LJ-1-600/runs/final-1.out` to `final-6.out`), 1.14 to 1.27 s
each, peak memory 331 to 352 MB, caliber `-A64m -I0 -M2g` set by the program
on this pane. The machine was not quiet (load 8.84 at the first run, 3.03 at
the last). One Agda process at a time, throughout.

## WHAT IS IN THE TREE

All under `agents/tasks/LJ-1-600/`:

| File | What it is |
|---|---|
| `runs/W3.agda` | The widest unmeasured term, TYPE ONLY: `key-at-stage` and the carrier equation `stage-carrier`. Written FIRST, typechecked ALONE. |
| `runs/w3-1.out` to `w3-3.out` | W3, GREEN, 1.17, 1.17, 1.19 s, cap 120 s never approached. |
| `runs/w3-neg-1.out` | Negative control: one planted type error, exit 42 at that row and nowhere else, 1.17 s. The checker is live. |
| `runs/Floor.agda` | The obligation and the stage row STATED WITH HOLES, in the full import frame of the final probe. |
| `runs/floor-1.out` | Floor, exit 42 at the two holes and nowhere else, 1.17 s, cap 300 s never approached. |
| `Probe600.agda` | The delivery: section 0 the stage, section 1 the obligation, section 2 the collection rows. |
| `runs/final-1.out` to `final-6.out` | The delivery, GREEN six times. |

Rows of the probe, with their prices included in the six green runs:

- 0.1 `allcodes-stage` (`Probe600.agda:106-112`): the stage that holds
  `AllCodes` at this carrier, named and proved. See the section below.
- 1.1 `key-at-stage` (`Probe600.agda:129-130`): THE OBLIGATION.
- 1.2 `key-at-stage-is-w3` (`Probe600.agda:135-136`): `refl`; the
  obligation and the alone-typechecked W3 row are one term.
- 1.3 `stage-carrier` (`Probe600.agda:145-146`): `refl`, imported from W3;
  the alphabet is the stage's members with no bridge.
- 2.1 `key-at-stage-1` (`Probe600.agda:171-172`): the arity-1 instance the
  site plugs into (`Formula ⟪ Lset δ ⟫ 1`,
  `src/L/StageCardinal.lagda.md:286`, `:321`).
- 2.2 `key-collected` (`Probe600.agda:180-188`): every meta formula at this
  carrier has a key, and `AllCodes` at this carrier holds it
  (`key∈AllCodes` applied, `src/L/Coding/CodeSet.lagda.md:443-447`).
- 2.3 `coded-member` (`Probe600.agda:192-203`): every member of `AllCodes`
  at this carrier is the key of a meta formula at this carrier
  (`AllCodes-out` applied, `src/L/Coding/CodeSet.lagda.md:449-455`). The
  truncation's payload is written out, the law the chapter itself recorded.

NOT ATTEMPTED, per AD12: (i) `D` and its `inv`, (ii) the leastness, (iii)
the pairing `sq`, (iv) the branch `ih` and its `Recursion` instance, and the
`class-pred` formula chapter itself. No row imports `L.StageCardinal`, so no
row can put `step`, `branch` or `stage-card-upper` into a conversion
problem, the drain `[LJ-1.584]` measured
(`agents/tasks/LJ-1-584/runs/w3b-1.out`).

## THE STAGE, NAMED

**The stage that holds `AllCodes` at this carrier is
`stage (AllCodes (LsetS δ oδ) .fst) (AllCodes (LsetS δ oδ) .snd)`, the
EARLIEST such stage**, delivered by the earliest-stage function of
`src/L/Stage.lagda.md`: `stage` at `:180`, `stage-ord` at `:185-186`,
`stage-mem` at `:188-189`. Probe row 0.1
(`agents/tasks/LJ-1-600/Probe600.agda:106-112`) states and proves it, green.

How I chose it: `AllCodes (LsetS δ oδ)` is an `S`, a constructible set
whose second component IS the `isL` certificate the function asks for, so
the choice needs no extra data and no induction. This is `[LJ-1.86]`'s own
half 1, measured TRUE at the older tree
(`agents/tasks/archive/LJ-1-86/lj-1.86-report.md:18-19`); this task
re-measures it AT THIS CARRIER and it is green. `stage` is sealed, so the
well-founded descent behind it never enters a conversion problem here.

Why the proof could not, per `[LJ-1.86]`: what no proof can choose is a
stage ADMISSIBLE for a `lam` FIXED UPSTREAM, because `lam` is a module
parameter of the condensation frames
(`agents/tasks/archive/LJ-1-86/lj-1.86-report.md:84-118`; the knife-edge at
`:130-134`). That wall does not bind this route, for two reasons measured
here. First, no consumer of ingredient (v) on the `class-pred` route fixes a
`lam`: the coded copy enters an object-language formula as the CONSTANT
`AllCodes A`, and a constant needs only an `S`, which it has. Second, where
a stage does enter `AllCodes`'s own construction, it is already chosen and
sealed: `smallDom` returns `LsetS β oβ` for the bounding ordinal of the
family's earliest stages (`src/L/Recursion.lagda.md:133-143`), separation
cuts `AllCodes` out of that stage with `isCodeAny`
(`src/L/Coding/CodeSet.lagda.md:304-310`), and `AllCodes` is opaque
(`:439-441`), so it stays an atom in every later type.

## THE TWO CURES, READ, AND WHETHER THE METHOD INSTANTIATES

**`L.Coding.CodeSet` BUILDS the copy** (`src/L/Coding/CodeSet.lagda.md`):
at a generic carrier `A : S` it gives every meta formula over `⟪ fst A ⟫`
a key that is an L-set, `keyS φ = key ι ιL φ , keyL ι ιL φ` (`:300-301`),
and it collects the keys of ALL arities into ONE L-set by cutting
`smallDom`'s stage-bound superset with the single predicate `isCodeAny A`
(`:304-310`), with both directions exported (`key∈AllCodes` `:443-447`,
`AllCodes-out` `:449-455`). The method instantiates here BY SUBSTITUTION:
the whole machine sits in `module _ (A : S)`, and rows 1.1, 2.2 and 2.3 of
the probe ARE that substitution at `A := LsetS δ oδ`, green. `[LJ-1.594]`
had measured only the generic forms
(`agents/tasks/LJ-1-594/Probe594.agda:392-401`); the instantiation is what
this task adds.

**`L.Coding.Powerset` CONSUMES the copy, and builds none of its own**
(`src/L/Coding/Powerset.lagda.md`): its object-language predicate for "c is
a code at the carrier in slot w" is `isCodeAt c w = keyArityAtL c 1 ∧̇
hasWitnessAt w c` (`:297-298`), with the two directions `codeAt-in` and
`codeAt-out` at a VARIABLE carrier `A` (`:300-318`), and its two halves
speak of `keyS A ψ` without naming `A` as a constant, which is what lets
the description live under the binder that binds the carrier. The method
instantiates here the same way, by substitution at the same `A`; I did not
build that row, because it is (i)'s territory (the `DefBody` description,
`:438`) and this brief forbids reaching past (v).

## WHAT (i) AND (ii) NOW NEED

My (v) neither blocks them nor does their work: (i) is `DefOf.defSet`
supplied by the site itself through `limit-step`'s parameters
(`src/L/StageCardinal.lagda.md:396-403`) and (ii) is `leastOf` over the
ordinal order (`src/L/StageCardinal.lagda.md:349-351`), and `[LJ-1.594]`
measured both internal at the real site (`D-at-the-site` and
`h-is-leastOf`, `agents/tasks/LJ-1-594/Probe594.agda:227-234`, `:305-317`).
What they now need is not machinery but RENDERING: an object-language
`Formula S 2` whose two directions say "the D-image of the coded formula is
the value" and "the value is the ordinal-least such", written at a carrier
that occupies a slot and is named nowhere, on the pattern `Powerset`
already used for exactly that shape (`isCodeAt`,
`src/L/Coding/Powerset.lagda.md:297-298`). A brief on them should carry
the file and the statement, the arity and slot order the internalization
chapter itself states (`graph : Formula S 2` with `defines` and `only`,
`src/L/Recursion.lagda.md:272-279`), and the explicit fact that (iii) and
(iv) stay out, because a formula that quantifies over the coded copy
through `AllCodes` (my rows 2.2 and 2.3 are its range, both directions)
needs neither.

## WHAT THE STATEMENT COST, AND WHAT RESISTED

**The statement cost 1.17 s of floor and 1.14 to 1.27 s of delivery, and
nothing resisted.** The floor run (holes where the bodies go, full import
frame, `runs/floor-1.out`) and the delivered runs cost the same, so the
whole price IS the frame; the obligation's own body is one application.
The shape did not resist because the tree has cured it twice, at
`CodeSet` and at `Powerset`, both at a generic carrier: this task's whole
content is the substitution `A := LsetS δ oδ` and the measurement that it
elaborates. I weakened nothing: every row of the probe is the chapter's
own statement at this carrier, with no weaker respelling, and the one
bridge anywhere is `fst (Lset δ , p)` reducing to `Lset δ`, a single
definitional projection. Nothing inside (v) stayed open; what remains open
is everything the brief ordered me not to touch, (i) through (iv) and the
`class-pred` formula that ties them.

The brief estimated about 190 probe lines with about 50 for the obligation.
The probe is 197 lines of file, of which 48 are code; the obligation is 2
code lines, its support rows are 14 more, and the stage row is 7. Estimates
of shape held (one small file, one frame, no chapter); estimates of size
were high, and nothing was funded against them.

## W2, ANSWERED

The mathematics is already written ONCE at a generic carrier and this task
only instantiates it: `keyS`, `AllCodes`, `key∈AllCodes` and `AllCodes-out`
all live in `module _ (A : S)` of the live chapter
(`src/L/Coding/CodeSet.lagda.md:286` onward), `Powerset` consumes them at a
variable carrier, and the probe adds ZERO generic code. Both trophies will
share this piece exactly as they share the chapter. No deadline pressure
occurred.

## PREMISE DEFECTS, TWO, BOTH REPORTED AND NEITHER LOAD-BEARING

1. **Premise 9 cites a file that is not in this tree.**
   `agents/tasks/LJ-1-572/review-of-b9-g-definable.md:116` does not exist:
   `agents/tasks/LJ-1-572/` is absent, a defect known since `[LJ-1.584]`
   (`agents/tasks/LJ-1-584/review-of-stage-bound-definable.md:165-166`,
   "`[LJ-1.572]` left not even its brief on disk"). The premise's claim,
   that the chain to `sq` is measured by `refl`, is independently measured
   in green probes that DO exist (`pair-is-sq`,
   `agents/tasks/LJ-1-594/Probe594.agda:238-243`, re-proved at
   `agents/tasks/LJ-1-597/Probe597.agda` section 1.1). This task relies on
   none of it: the probe does not import `L.StageCardinal`.
2. **Premise 11 names a rule that does not exist.** There is no R-42 in
   `dev/LESSONS.md`; the rules end at R-41, and `dev/LESSONS.md:4404` is
   C-53's Related line, not a rule. The respelling rule the premise means
   is R-41, "state an index in the spelling its proof produces"
   (`dev/LESSONS.md:4762`). I worked under R-41's substance: ONE spelling,
   `⟪ Lset δ ⟫`, the site's own (`src/L/StageCardinal.lagda.md:278`,
   `:286`), in every row of the probe; R-41's own census prices a depth-one
   bridge at zero, and the runs agree.

## D-10, THE TARGET'S TRUTH, PRICED BEFORE THE PROOF

The target is a total function delivered by a green chapter at a generic
carrier; no Tarskian or cardinality obstruction can reach a substitution
instance of it. The recorded residue this brief ordered re-priced, the
stage, split exactly as `[LJ-1.86]` left it and is answered in the stage
section above: the stage EXISTS and is nameable at this carrier (green,
row 0.1); what remains impossible is choosing a stage fixed upstream, and
no consumer of (v) on this route fixes one.

## THE GATES

`lint-agda`, `check-probes`, `lint-prose`, `check-rule-ids` and
`check-fences` were run individually and are clean. No file under `src/`
was touched, so the whole-tree typecheck state is unchanged. `make check`
is the program's gate at commit time; this task never commits.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` READ at `:160`: "| LJ-1.86 | Is there
  a stage containing AllCodes A | EXISTS; proof cannot choose it |
  AllCodes-stage is green. But lam is a module parameter at every frame, so
  the obligation moves to the frame |". This is premise 4's basis and the
  D-10 residue; the probe's stage row and this report's stage section
  answer it at this carrier.
- `archive/dev/JOURNAL-archived.md` READ at `:3935`: "  **slot**; `Codes`
  and `AllCodes` are re-derived on top; exactly one code". The owner's
  `[L3.19]` fork ruling that made the code-set layer carrier-generic, which
  is why the method instantiates by substitution today.
- `archive/dev/JOURNAL.md` not used: grep for `keyS` and `AllCodes`
  returns 0 hits; the AllCodes history I needed is in the archived journal
  above.
- `archive/dev/ORCHESTRATION.md` declined: orchestration history, no row of
  this task rests on it.
- `archive/dev/DECISIONS-archived.md` declined: the archived decision log;
  the rules that bind this task are in `dev/LESSONS.md` and the rulings,
  and grep for `keyS` and `AllCodes` returns 0 hits.

## LITERATURE USED

- `dev/literature/devlin-II5.md` READ at `:253`: "are exactly the
  analogues of this substrate on the project's coding; the". The coded copy
  this task instantiates is the project's analogue of Devlin's bounded
  satisfaction substrate, and the corpus adds that the argument "does not
  require them to have any particular shape" (`:254`), which is consistent
  with the finding here: the instantiation constrains nothing downstream.
- `dev/literature/truncation-and-selection.md` READ at `:83`: "**So a
  proof that only needs cardinal arithmetic never needs an injection as".
  Binds `[LJ-1.592]`'s truncated route 1, not this task; recorded because
  the two routes share the endpoint and the next brief on (i) and (ii)
  may meet it.
- `dev/literature/digest.md` declined: it pins the rudimentary-functions
  architecture; nothing in a coding instantiation at a carrier rests on it.
- `dev/literature/terms-2026-08.md` declined: a terminology dossier for
  glossary rulings, with no mathematics of the coded copy.
- `dev/literature/geology.md` declined: set-theoretic geology sources, no
  bearing on this task.
