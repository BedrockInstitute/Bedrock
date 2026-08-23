# [LJ-1.594] report: what a definable pairing would cost L.StageCardinal

## HEAD
head_slot: coder
machine: shared
task: LJ-1.594
obligation: agents/tasks/LJ-1-594/Probe594.agda::pairing-suffices
verdict: NO-GO

The report was written as a skeleton before any proof Agda and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-594/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. **NO HEAP EVENT**: the largest maximum resident set size of any run of
mine is 1,613,332,480 bytes, about 1.50 GiB, against the 8 GB cap
(`agents/tasks/LJ-1-594/runs/p594-s0-1.out`). No run of mine gave exit 251 and no
run printed a heap message. Nothing is postulated, the probe carries `--safe`,
and there is no hole. Nothing lands in `src/`. The probe is a raw `.agda` file,
so it carries no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar
cannot fire on it.

## VERDICT

**NO-GO on `pairing-suffices`**, and
`agents/tasks/LJ-1-594/review-of-pairing-suffices.md` states it.

**THE PROBE IS GREEN, EXIT 0, FIVE RUNS** (`runs/final-1.out` to
`runs/final-5.out`). **THREE OF THE FIVE UNAMBIGUOUSLY POSTDATE THE LAST EDIT TO
`Probe594.agda`**, which was at 06:07:33Z: `final-3` (06:09:27Z), `final-4`
(06:15:37Z) and `final-5` (06:15:52Z). `final-1` predates it and `final-2`
started in the same second, so neither is offered as evidence about the file as
it stands. **The edit in question changed one citation inside a comment and no
Agda.** Green and not holed is deliberate: every reduction in the file is then a
measurement and not a claim.

**THE ANSWER IN FOUR LINES.**

1. **THE BRIEF'S CENTRAL PREMISE IS FALSE AS MEASURED.** The brief says two of
   `class-pred`'s three ingredients are already internal, so "the module is one
   substitution away from carrying a formula". **`class-pred` HAS FIVE
   INGREDIENTS.** `class-pred-is` (`Probe594.agda:283-300`) writes
   `src/L/StageCardinal.lagda.md:319-324` out by `refl`. The two the predecessor
   did not count are `ih m`, the injection at the stage BELOW
   (`cnt-is-the-IH`, `Probe594.agda:252-263`), and the META syntax
   `Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1` that the existential ranges over.
2. **AND THE HYPOTHESIS IS NOT TOO STRONG. IT IS TOO WEAK.** The brief asks what
   to say if the pairing hypothesis is as strong as the conclusion. **IT IS NOT.**
   `DefPairing` (`Probe594.agda:199-210`) describes one binary function on the
   members of one ordinal; the conclusion is an injection of a whole stage. It is
   strictly weaker AND still not sufficient, which is a different failure from
   the one the brief priced for.
3. **THE PRICE IS A CHAPTER, NOT A SUBSTITUTION, AND EVERY PIECE OF IT IS
   ALREADY IN THE TREE.** (iv) costs a formula and not a new induction
   principle: `src/L/Recursion.lagda.md:259-261`, re-ascribed at
   `Probe594.agda:362-370`, with `hierL` (`src/L/Hierarchy.lagda.md:621-622`) as
   its domain. (v) is already coded: `src/L/Coding/CodeSet.lagda.md:300-301` and
   `:440-443`, re-ascribed at `Probe594.agda:392-401`. **What is missing is the
   one `Formula` that ties (i) to (v) together, with its `defines` and its
   `only`.**
4. **AND THE SECOND HALF OF ROUTE 2 IS FREE.** `def-h→target`
   (`Probe594.agda:124-129`) is `[LJ-1.568]`'s `restrict→B9` at its own theorem
   `def-restricted`, so it spends no hypothesis: whoever writes the formula gets
   `InjL (Lset α) α` for nothing. The block is entirely in producing the formula.

**I DID NOT BUILD THE PAIRING. I DID NOT BUILD ROUTE 1'S TERM AND I DID NOT WAIT
ON `[LJ-1.592]`. I DID NOT EDIT `src/L/StageCardinal.lagda.md`. I DID NOT
POSTULATE. I CLAIM NO SECOND LEDGER ROW.**

## D-10: `sq` AT ITS SITE

**THE BRIEF ORDERS THIS FIRST AND IT IS THE FIRST THING I DID.**

`sq` is `L.StageCardinal`'s third module parameter, declared at
`src/L/StageCardinal.lagda.md:17-20`:

```
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
```

It carries one function on the pairs of members of δ and one injectivity proof of
it. **NO `Formula`, no L-set, no satisfaction, no ordinal grade.**

**IT IS USED ONCE IN THAT FILE**: `src/L/StageCardinal.lagda.md:283`,
`module B = Bound α oα infα (sq α α∈suc infα)`, inside `module LimitStep` (`:277`).

**THE COUNT IS `grep -nw "sq" src/L/StageCardinal.lagda.md`, WHICH RETURNS
EXACTLY THOSE TWO LINES, AND `grep -cw` WHICH RETURNS 2. NO COMMAND CONTAINING
`head` WAS USED TO REACH IT.** The other five matches of the substring in that
file are `squash₁` (`:51`, `:323`, `:327`, `:445`) and the word "square" in a
comment (`:59`).

**AND THE TARGET IS NOT FALSE.** `V = L` gives it outright: `vl→target`
(`Probe594.agda:135-140`). So a refutation of the target is a refutation of
`V = L` (`refuting-target-refutes-V=L`, `Probe594.agda:146-152`). This report
does not claim the target is false; it measures that a definable pairing does not
buy it.

## THE PAIRING, STATED

**IN FULL** (`agents/tasks/LJ-1-594/Probe594.agda:199-210`):

```agda
DefPairing : (α : V ℓ) (oα : IsOrd α) → ⟨ α ∈ˢ sucV α₀ ⟩
           → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → Type (ℓ-suc ℓ)
DefPairing α oα α∈suc α∉ω =
  Σ[ Pf ∈ Formula S 3 ]
    ( ((x y : ⟪ α ⟫) → ⟨ (asL (pr2 x y) ∷ asL x ∷ asL y ∷ []) ⊨ Pf ⟩)
    × ((x y : ⟪ α ⟫) (z : S) → ⟨ (z ∷ asL x ∷ asL y ∷ []) ⊨ Pf ⟩
         → z ≡ asL (pr2 x y)) )
  where
  asL : ⟪ α ⟫ → S
  asL = P561.up (P568.ordS α oα)
  pr2 : ⟪ α ⟫ → ⟪ α ⟫ → ⟪ α ⟫
  pr2 x y = fst (sq α α∈suc α∉ω) (x , y)
```

**ONE SENTENCE ON WHAT IT ASSUMES.** It assumes only that SOME formula of the
object language, with L-sets as constants and at NO Levy grade, describes the
pairing the module already has, in both directions, on the members of one
ordinal α: it does not ask for a new pairing, it does not ask the pairing to be
canonical, and it assumes nothing at any other stage.

It is the shape `[LJ-1.554]`'s `LinkAt` (`agents/tasks/LJ-1-554/Probe554.agda:80-87`)
takes for a unary assignment, written at arity two. The grade is `Def`'s
(`agents/tasks/LJ-1-568/Probe568.agda:189`), which is arbitrary because the
separation it would be spent through takes an arbitrary formula
(`src/L/Axioms/Full.lagda.md:144`).

**IT IS STATED UNTRUNCATED, WHICH IS THE STRONGEST OF THE THREE READINGS**, and
the file does not need the difference: it is not sufficient in any grade.

## WHAT SUBSTITUTING IT WOULD COST src/

**A COUNT I MEASURED, by `grep -rn "L.StageCardinal" src/` and `grep -rnw "sq" src/`.**

| site | line | what it is |
|---|---|---|
| `src/L/StageCardinal.lagda.md` | `:17-20` | the parameter, declared |
| `src/L/StageCardinal.lagda.md` | `:283` | the only use in that chapter |
| `src/L/BoundedSubset.lagda.md` | `:1388-1390` | the same parameter, re-declared on `BoundedSubsetAt` |
| `src/L/BoundedSubset.lagda.md` | `:1397` | the ONLY application of `L.StageCardinal` in `src/` |
| `src/L/BoundedSubset.lagda.md` | `:1410` | the second use of `sq`, at `SC.Bound` |
| `src/L/StageBound.lagda.md` | `:36-40` | `SqFam`, the type abbreviated, and its own comment at `:33-34` says it is copied from `src/L/BoundedSubset.lagda.md:1388-1390` |
| `src/L/StageBound.lagda.md` | `:67` | the parameter, re-declared on `Instantiation` |
| `src/L/StageBound.lagda.md` | `:75` | passed on to `BoundedSubsetAt` |

**THREE CHAPTERS, THREE DECLARATION SITES, TWO USE SITES, ONE MODULE
APPLICATION.** `src/Everything.lagda.md:389` and `src/L/BoundedSubset.lagda.md:882`
are bare `import L.StageCardinal` lines and apply nothing.

**ONE SENTENCE ON WHETHER THE SUBSTITUTION IS LOCAL. THE EDIT IS LOCAL AND THE
EFFECT IS NOT**: changing the parameter's type touches eight lines in three
chapters and nothing else, but the property the brief wanted from it, that the
chapter then carries a formula, does not follow, because the pairing is one of
five ingredients of `class-pred` and two of the other four are not internal
either.

## THE C-42 SWEEP

C-42 orders the count before the cure, and it orders it over the shape the
refutation names, not the site.

**THE SHAPE: a selection predicate that quantifies over `Formula` at an AMBIENT
carrier**, written `Formula ⟪ ... ⟫`. That is ingredient (v), and it is the one
of the two uncounted ingredients that a grep can see.

`grep -rn "Formula ⟪" src/`: **80 LINES IN 16 FILES.** By file:
`src/L/Coding/Powerset.lagda.md` 15, `src/L/Coding/CodeSet.lagda.md` 12,
`src/L/StageCardinal.lagda.md` 11, `src/L/Definability.lagda.md` 7,
`src/L/Coding/Uniform.lagda.md` 7, `src/L/Choice/Name.lagda.md` 5,
`src/L/Coding/Key.lagda.md` 4, `src/L/Axioms/Separation.lagda.md` 4,
`src/L/Axioms/Basic.lagda.md` 4, `src/L/Choice/Internal.lagda.md` 3,
`src/L/Constructible.lagda.md` 2, `src/L/Coding/Bridge.lagda.md` 2, and one each
in `src/L/Ordinal/Stages.lagda.md`, `src/L/Coding/EnvSupply.lagda.md`,
`src/L/Choice/Faithful.lagda.md`, `src/L/Choice/Adequate.lagda.md`.

**THE COUNT IS NOT "16 BLOCKED SITES", AND REPORTING IT THAT WAY WOULD BE THE
ERROR C-42 EXISTS TO STOP.** Two of the sixteen, `Coding/CodeSet` and
`Coding/Powerset`, are the CURE and not an instance: they are where the coded
copy is built. The sweep's finding is that the shape is common and that the tree
already answered it twice, which is why this NO-GO prices route 2 instead of
closing it.

## THE FLOOR AND THE RUNS

| run | file | exit | real | max RSS |
|---|---|---|---|---|
| `runs/w3-1.out` | W3, first attempt | 42 | 1.02 s | 310,263,808 B |
| `runs/w3-2.out` | W3, GREEN | 0 | 1.06 s | 310,722,560 B |
| `runs/p594-s0-1.out` | probe, sections 0 to 2 | 42 | 36.78 s | 1,613,332,480 B |
| `runs/p594-s3-1.out` | probe, all sections | 0 | 105.80 s | 1,462,960,128 B |
| `runs/final-1.out` | probe, GREEN, cold, pre-edit | 0 | 107.03 s | 1,487,011,840 B |
| `runs/final-2.out` | probe, GREEN, cold, same second as the edit | 0 | 107.19 s | 1,487,011,840 B |
| `runs/final-3.out` | probe, GREEN, warm, post-edit | 0 | 3.48 s | 711,426,048 B |
| `runs/final-4.out` | probe, GREEN, warm, post-edit | 0 | 3.42 s | 711,409,664 B |
| `runs/final-5.out` | probe, GREEN, warm, post-edit | 0 | 3.28 s | 711,426,048 B |

**THE COLD PRICE OF THE PROBE IS 107 SECONDS AND THE WARM PRICE IS 3.3
SECONDS**, both under the caliber the program set. The three post-edit runs are
warm because the interface files were already built by the two cold ones; a warm
run still elaborates this file's own 439 lines and would still refuse a bad
`refl`.

`runs/w3-1.out` is exit 42 for one reason and it is recorded rather than hidden:
`SqParam`'s universe was written `Type ℓ` and the ambient membership proposition
lives at `Type (ℓ-suc ℓ)`, so the transcription was corrected before any other
Agda. `runs/p594-s0-1.out` is exit 42 for a scaffolding placeholder in an
unfinished section 3, not for any claim in the file.

**THE RUNS DIRECTORY HOLDS EXACTLY**: `run.sh` (the harness, copied from
`[LJ-1.584]` and repointed), `W3.agda`, and the nine `.out` files named above.
No bounded run was needed, because no run of mine approached a time or a heap
bound.

**W3 WAS WRITTEN FIRST AND TYPECHECKED ALONE**, as the brief ordered:
`agents/tasks/LJ-1-594/runs/W3.agda`, GREEN in 1.06 s against the estimate of
"about 10 lines, under 60 seconds". It is 54 lines and it is IMPORTED by the
probe, not restated.

## AGAINST THE ESTIMATE

**ESTIMATE: about 160 probe lines, of which the obligation is about 40.
ACTUAL: 439 lines in `Probe594.agda` and 54 in `runs/W3.agda`, and the
obligation is 0, because the obligation is not inhabited.** The overrun is not
the obligation. It is section 3: five `refl` rows that each carry the full
seven-argument telescope of `LimitStep`, which is what it costs to state a fact
about a module's internals from outside it. The brief's comparable, `[LJ-1.526]`,
made a reduction; this task made a count, and a count of five ingredients costs
five rows.

## WHAT THE NEXT BRIEF NEEDS

`agents/tasks/LJ-1-594/review-of-pairing-suffices.md` carries this in full. The
three things that do not fit in a verdict line:

1. **ORDER (v) FIRST, NOT (iii).** The existential's range has to exist before
   the rest of `class-pred`'s clause can be written. That is `keyS` and
   `AllCodes` at `A := LsetS δ oδ` (`src/L/Coding/CodeSet.lagda.md:300-301`,
   `:440-443`). The pairing is the SMALLEST of the five and goes in last.
2. **`AllCodes` AT A CARRIER IS NOT NEW GROUND AND ITS KNOWN FAILURE IS NOT THE
   CODE SET.** `archive/dev/LJ-dispatch-index.md:160` records `[LJ-1.86]`:
   the stage containing `AllCodes A` exists, and the proof cannot choose it,
   because the stage is a module parameter at every frame. A brief ordering (v)
   must say which stage.
3. **DO NOT PUT `step`, `branch` OR `stage-card-upper` INTO A CONVERSION
   PROBLEM.** `[LJ-1.584]` measured one that does not terminate
   (`agents/tasks/LJ-1-584/runs/w3b-1.out`). Every row of my section 3 that
   touches the recursion is TYPE ONLY (`Probe594.agda:327-332`, `:337-341`), and
   the `refl` rows take `ih` as an abstract argument.

## ARCHIVE USED

- **`archive/dev/JOURNAL.md` READ AND USED.** `archive/dev/JOURNAL.md:1366`:
  "pricing. **That endomap on `sq δ` is now the widest unmeasured term, and".
  This is `[LJ-1.584]`'s route 3, the weakly constant endomap on `sq δ`. It is
  NOT this task's route and I did not take it, but it is why the report says the
  pairing hypothesis is untruncated by choice: an endomap would make
  `stage-card-upper` canonical, and nothing in my finding depends on whether it
  is, because ingredients (iv) and (v) are untouched by that question.
- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:160`: "| LJ-1.86 | Is there a stage
  containing AllCodes A | EXISTS; proof cannot choose it | AllCodes-stage is
  green. But lam is a module parameter at every frame, so the obligation moves to
  the frame |". It is the warning in `## WHAT THE NEXT BRIEF NEEDS` item 2, and
  it changed what I recommend ordering first.
- **`dev/ARCHIVE.md` READ AND USED.** `dev/ARCHIVE.md:267` begins
  "| `L.Rud.CodeSet` | `src/L/Rud/CodeSet.lagda.md` | The formula codes over a
  carrier as one sealed family: membership definitional, decode untruncated,
  every code unconditionally a closure member." That is a RETIRED chapter and it
  is NOT the one I re-ascribe. I re-ascribe the live
  `src/L/Coding/CodeSet.lagda.md`. The two names differ by one component and the
  review says so, so a next brief does not revive the wrong one.
- **`archive/dev/JOURNAL-archived.md` NOT USED, DECLINED.** Its own first
  lines say it is the journal of the retired route, archived 2026-08-09 when the
  two-tower route was ruled. My finding is about chapters of the live route.
- **`archive/dev/ORCHESTRATION.md` NOT USED, DECLINED.** It is the archived
  process document; it carries no mathematics about `L.StageCardinal`.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ AND USED, AND IT CONFIRMS THE
  FINDING.** `dev/literature/devlin-II5.md:335`: "7. The level-recursion
  machinery 2.2-2.8, the Def-side engine:", and
  `dev/literature/devlin-II5.md:360`: "The single engine II.5 leans on most is
  item 7: the uniformly-Δ₁ level". **Devlin's own engine for the level-size
  theorem is the level-recursion formula `E(f, α)` together with the bound set
  `K(u)`, "the finite sequences over formulas, variables and members of u".
  Those are ingredients (iv) and (v). The pairing is not the engine in the source
  either**, which is independent evidence that this NO-GO is about the
  mathematics and not about this tree's presentation of it.
- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `dev/literature/truncation-and-selection.md:147`: "delivers the least INDEX
  untruncated, and any payload it delivers with the". This is the law behind
  ingredient (ii): the least-element selection gives back an index and a
  propositional payload, which is exactly what `h` takes from `leastOf`
  (`Probe594.agda:305-317`). And `:83`: "**So a proof that only needs cardinal
  arithmetic never needs an injection as", which is why the target is
  `InjL`, a truncation, and why the second half of route 2 costs nothing.
- **`dev/literature/digest.md` READ, DID NOT BEAR.** `dev/literature/digest.md:193`
  is "### What the sources say about the relation", and the section is the
  Gandy-Jensen against Devlin-Basic split over R8. Nothing in it touches
  `class-pred`'s ingredients, so no row of my probe rests on it.
- **`dev/literature/geology.md` NOT USED, DECLINED.** Its first line is a
  geology dossier for `[L3.32-T12]`, set-theoretic geology sources. It is not
  about the level-size theorem.
- **`dev/literature/terms-2026-08.md` NOT USED, DECLINED.** It is the
  terminology dossier of fourteen renderings for an owner's ruling. This task
  wrote no prose for the owner and coined no term.
