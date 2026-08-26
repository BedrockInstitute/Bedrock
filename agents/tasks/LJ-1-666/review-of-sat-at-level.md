# review-of-sat-at-level: a STATED NO-GO, with the chapter's slot commitment

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.666
obligation: agents/tasks/LJ-1-666/Probe666.agda::sat-at-level
verdict: **NO-GO.** `sat-at-level : SatAtLevel φ₀` is not inhabited for any
arity-2, parameter-free `φ₀` built from the chapter's bounded matrix. The
witness meter reads `1 UNRESOLVED of 1, 0.98 s, probe_red=False`
(`runs/meter-obligation.out`). The probe is green and carries no hole.

**THIS IS NOT A REFUTATION OF THE LEVEL-HOOD'S SATISFACTION.** The bounded
matrix IS true: the witnesses exist, and the formula holds. What is
measured is that the TREE cannot close the stage-satisfaction term: the
only delivered bridge between the bounded and unbounded graphs
(`LeafAgree`/`extAtB→extAt`) requires the `KFacts` record at fourteen
environment slots, and the arity-2 formula provides two. A direct proof
of the bounded graph's stage satisfaction (without the bridge) is not
delivered in the tree. It would be a new module.

## 1. THE OBLIGATION

The brief asks for one term:

    sat-at-level : SatAtLevel φ₀

where `φ₀` is an arity-2, parameter-free formula chosen by the coder, and
`SatAtLevel` is `[LJ-1.662]`'s type at
`agents/tasks/LJ-1-662/Probe662.agda:284-286`:

    SatAtLevel φ =
      (γ : Hd.ASt.SL) (oγ : IsOrd (fst γ))
      → ⟨ ((Lset (fst γ), level-in-stage γ oγ) ∷ γ ∷ []) T.⊨c (embed φ) ⟩

The probe `Probe666.agda` does NOT state the obligation name. A qualified
reference to an absent name is the witness meter's `[NotInScope]`, and that
reading is the NO-GO the branch table prices. The probe instead states,
green, every fact the verdict rests on.

## 2. THE THREE WALLS

### Wall 1: The KFacts slot count

The `KFacts` record (`src/L/Condensation.lagda.md:6079-6140`) carries
twelve numeral columns (`tagEq0` through `tagEq11`), twelve numeral-in-K
columns (`numK0` through `numK11`), one inner-K column, and one pair-K
column. The sole value in the tree, `KValue.facts`
(`src/L/Condensation.lagda.md:7411`), sits at `Kenv : S ^ 14`
(`src/L/Condensation.lagda.md:7389`): the carrier, the bound, and the
twelve arity tags.

The chapter's `LevelHood0` matrix (`src/L/BoundedSubset.lagda.md:849`) is
at arity 4: `u ∷ v ∷ γ ∷ K`. The module's N-parameters are `Fin 5`
(`src/L/BoundedSubset.lagda.md:841`): they address at most five distinct
slots. The M-parameters are `Fin 7`
(`src/L/BoundedSubset.lagda.md:842`): at most seven.

The `KFacts` needs twelve distinct numeral columns
(`src/L/Condensation.lagda.md:7397-7408`). Five does not reach twelve.
Seven does not reach twelve. **No choice of `LevelHood0`'s twenty-eight
parameters can supply the `KFacts`.**

### Wall 2: The bounded-unbounded gap

`graphBndAt` (`src/L/Condensation.lagda.md:2492`) is the bounded graph
formula. It occurs at six lines in `src/` total:
`src/L/Condensation.lagda.md:2492, :2493, :2495, :2496` and
`src/L/BoundedSubset.lagda.md:111, :115`. None of those lines provides a
satisfaction lemma for the bounded graph at the stage.

The delivered adequacy is `Lset-only` (`src/L/Hierarchy.lagda.md:334-335`)
and `Lset-defines` (`src/L/Hierarchy.lagda.md:646`), for the UNBOUNDED
`LsetGraphAt` at the CLASS CARRIER.

The only bridge in the tree is `LeafAgree`
(`src/L/Condensation.lagda.md:7224`), which requires a `KFacts` record at
fourteen environment slots. The `extAtB→extAt` function
(`src/L/Condensation.lagda.md:2510-2517`) is the lift that uses it: it
takes a `KFacts`-indexed leaf agreement and transfers the bounded
two-way frame to the machine's unbounded two-way frame.

**Any route that uses the delivered bridge (`LeafAgree`/`extAtB→extAt`)
from the bounded matrix's stage satisfaction to the unbounded graph's
class-carrier satisfaction requires the `KFacts` at fourteen slots. The
arity-2 formula has two free slots. The gap is ten. A direct proof of
the bounded graph's stage satisfaction, bypassing the bridge, is not
delivered in the tree: no satisfaction lemma for `approxBndAt` or
`stepBndAt` exists at `src/`. The six `graphBndAt` lines are the
formula definition and its Δ₀ certificate, not a satisfaction proof.**

### Wall 3: The third option does not create slots

The 662 report names a third option: "A formula that SAYS its own columns
are the numerals" (`agents/tasks/LJ-1-662/lj-1.662-report.md`, section 7).
This would fold the twelve tag equations into the formula body.

The tag equations are of the form:

    fst (lookup i env) ≡ fst (numeralL k)

for twelve values of `i : Fin 14` and `k : ℕ`. The `lookup i env` is
defined only for `i < n` where `n` is the environment arity. At arity 2,
lookups 0 and 1 are defined; lookups 2 through 13 are not. **The twelve
tag equations cannot be read from a two-slot environment.**

Folding the equations into the formula body does not create the missing
slots. The equations assert facts ABOUT the environment; they do not
extend it. An arity-2 formula has two free variables, full stop.

## 3. THE STATEMENT ABOUT THE CHAPTER

The 662 count was: "twelve numeral columns cannot come from five committed
slots." That was a fact about `LevelHood0`'s parameterization. This review
sharpens it: **the commitment is not in the parameterization; it is in the
bounded graph machinery itself.** The `graphBndAt` formula, as used in
`LevelHood`, requires the `KFacts` for its satisfaction bridge. The
`KFacts` requires fourteen environment slots. This is true of ANY
instantiation of the bounded graph, at ANY arity. The `LevelHood {n}`
module for `n ≥ 14` has room for the columns, but its matrix is at arity
`4 + n ≥ 18`, and closing the surplus by `∃̇` to return to arity 2 loses the
tag equations that the `KFacts` asserts.

**The chapter's bounded graph and the chapter's arity-2 satisfaction
obligation are in tension. The tension is structural, not parametric.**

## 4. SITE COUNT

The refutation measures one site: the `SatAtLevel` obligation at the
bounded matrix. The sweep asked how many sites carry the same false shape.
Search: `graphBndAt` over `src/` — six lines, all in the two files named
above. `KFacts` over `src/` — the record definition at
`src/L/Condensation.lagda.md:6079` and the sole value at
`src/L/Condensation.lagda.md:7411`. `LeafAgree` over `src/` — the module
at `src/L/Condensation.lagda.md:7224`. No other site carries the same
commitment. Count: **1**.

## 5. RUNS

One Agda process per run, wide caliber. Files under `runs/`.

| Run | What | Result |
|---|---|---|
| probe-1 | probe, first attempt | red: `_-_` not in scope (`runs/probe-1.out`) |
| probe-2 | probe, final | **green**, exit 0 (`runs/probe-2.out`) |
| meter-obligation | witness meter, one obligation | `1 UNRESOLVED of 1, 0.98 s, probe_red=False` (`runs/meter-obligation.out`) |

## 6. WHAT THE NEXT BRIEF NEEDS

1. **A satisfaction lemma for the bounded graph at the stage, that does
   NOT go through `KFacts`.** No such lemma exists in `src/`. The six
   `graphBndAt` lines are the formula and its Δ₀ certificate. A new
   module would need to construct the witnesses (the codes, the shapes,
   the clauses) in the stage and prove the bounded formulas hold,
   without the `LeafAgree` bridge. This is the chapter's own named
   residue ("the level-hood instantiation at the hull",
   `src/L/BoundedSubset.lagda.md:901-902`).
2. **OR: a `KFacts` value at arity 2.** This would require redefining the
   `KFacts` record to carry its twelve numeral columns as parameters
   rather than as environment lookups. This changes the record's shape and
   every consumer of it.
3. **OR: the unbounded graph at the stage.** A `φ₀` that is the UNBOUNDED
   `LsetGraphAt` (Σ₁, arity 2) rather than the bounded matrix. The chapter
   delivers `Lset-defines` for the unbounded graph at the CLASS CARRIER.
   The stage satisfaction would require the graph's witnesses to be in the
   stage, which is a different proof (the graph is a set of pairs, not a
   stage element by definition). This route is also not delivered in the
   tree.
4. **OR: a different formula.** A `φ₀` that is NOT the level-hood at all,
   but whose satisfaction IS provable at the stage, and whose
   `HoodSoundP` is also meaningful. The constraint is that the formula
   must pin the value to `Lset γ` in a way that the soundness half can
   read.
