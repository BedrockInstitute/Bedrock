# review of `stage-card-upper-coded`: the formula reaches the site and not the value

**VERDICT: NO-GO.** `stage-card-upper-coded` is not written in
`agents/tasks/LJ-1-535/Probe535.agda`. This file is the obstruction.

**THE BRIEF'S OBLIGATION HAS TWO HALVES AND THEY DO NOT LAND TOGETHER.**

1. "a Formula-carrying restatement of `stage-card-upper`'s injection":
   **BUILT AND GREEN**, `Probe535.agda:228-232`, at the type
   `StageCardUpperCodedᵀ` (`:122-133`).
2. "from which an `InjCode` is reachable": **NOT REACHABLE**, and the reason is
   a type argument, not a failed search.

Because half 2 fails, the term does not carry the obligation's name. The
restatement is named `stage-card-upper-with-formula` instead.

## THE ANSWER TO W3, IN ONE SENTENCE

**The formula is in scope where the injection is formed, and it is not in the
injection's value.** `count-bound` consumes it through
`code : Formula (⊥* {ℓ}) k → ℕ`, and the value is then assembled by two ambient
maps that carry no `Formula`.

## THE MEASUREMENT

`count-bound` (`src/L/StageCardinal.lagda.md:124-129`) is the whole counting:

    count-bound g (k , (ψ , (n , cs))) =
      pair (numeral k) (pair (pair (numeral (code ψ)) (numeral n))
                             (tuple-g g k cs))

Three ingredients reach the ordinal, and the `Formula` is in one of them.

| ingredient | its type | carries a `Formula`? |
|---|---|---|
| `code ψ` | `Formula (⊥* {ℓ}) k → ℕ` (`src/FOL/Count.lagda.md:81`, `Probe535.agda:257-258`) | the domain is the parameter-FREE shape, and what leaves is `ℕ` |
| `tuple-g g k cs` | `g : Σ[ f ∈ (K → ⟪ β ⟫) ] injective` (`:100-102`, `Probe535.agda:263-264`) | NO |
| `pair` | the module parameter `sq`, same bare Σ shape (`src/L/StageCardinal.lagda.md:17-19`, `Probe535.agda:276-280`) | NO |

**AND THE BARE Σ IS `[LJ-1.533]`'s OBJECT.** `_↪_` is
`Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)`
(`src/L/Cardinal.lagda.md:47-48`), which is `TupleInputᵀ` (`Probe535.agda:263-264`)
with the carriers renamed. `[LJ-1.533]` proved by types that nothing turns such a
thing into an `InjCode`
(`agents/tasks/LJ-1-533/review-of-StageCountedCoded.md`).

**AT THE RECURSIVE SITE THE FIRST ONE IS THE INDUCTION HYPOTHESIS.**
`LimitStep`'s `ih` (`src/L/StageCardinal.lagda.md:281`) is the branch family, and
`cnt m` is `formula-bound` applied to `ih m` (`:288-289`). `branch-is-ambient`
(`Probe535.agda:269-271`) typechecks `ih` AT `TupleInputᵀ`, so the identification
is the elaborator's and not mine.

**SO THE WALL IS NOT AT THE CHAPTER'S EDGE. IT IS INSIDE THE TERM.** Two of the
three ingredients that compute `f x` are the object `[LJ-1.533]` refuted, and the
formula the brief hoped for does not change either one's type.

## WHAT THE FORMULA DOES BUY, SO NOBODY RE-BUYS IT

**IT COMES OUT UNTRUNCATED.** `class-pred` (`src/L/StageCardinal.lagda.md:319-323`)
binds the formula under `∥_∥₁`, and that truncation is NOT a wall: at a fixed
value the witness is a proposition, because `pair-inj` (`:71-75`) and `cnt-inj`
(`:291-292`) determine `m` and `φ` from the packed value. `isPropWit`
(`Probe535.agda:196-214`) is that argument and `witness` (`:221-222`) spends
`SC.extract` (`src/L/StageCardinal.lagda.md:419-420`) once.

What the restatement delivers for every member `x` of `Lset α`:

- `m : ⟪ α ⟫`, a member of `α`;
- `φ : Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1`;
- `defSet (Lset (⟪ α ⟫↪ m)) φ ≡ ⟪ Lset α ⟫↪ x`;
- `pack m φ ≡ f x`, with `pack m` injective (`Probe535.agda:187-190`).

**AND IT IS STILL THE WRONG FORMULA FOR THE JOB.** `hasSeparationL` takes
`Formula S 1` (`src/L/Axioms/Full.lagda.md:144`) and `hasReplacementL` takes
`Formula S 2` (`:277`), both over the L-CARRIER, and both are used to define ONE
set. What the chapter has is a formula over `⟪ Lset δ ⟫`, the members of a lower
stage, and it names ONE MEMBER of the domain, not the injection. A formula per
member of the domain is not a formula for the graph, and no term in the tree
turns the first into the second.

## THE PRICE, AND THE TREE'S OWN TEMPLATE FOR IT

A coded B9 must be written from its own object-language formula, in the shape
`L.Absorption` already uses:

    shiftFo     : S → S → S → S → Formula S 1                   (src/L/Absorption.lagda.md:224)
    absorbs     : ... → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫            (:635-638)
    shift-coded : ... → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁    (:611-614)

**ONE `ShiftGraph` MODULE, TWO EXPORTS, ONE FORMULA.** The ambient injection and
the `InjCode` are read off the same graph. That is what "build coded at the
chapter's own site" means, and `L.StageCardinal` has no term of the first line's
shape at all.

**THIS IS A STOP AND NOT A REFUSAL TO TRY.** The restatement is built, green and
tracked. What it shows is that the missing input is an object-language formula
for the counting graph, and that writing one is not a restatement of anything
delivered: it is new mathematics at `L.StageCardinal`'s site, and the
mathematician must price it.
