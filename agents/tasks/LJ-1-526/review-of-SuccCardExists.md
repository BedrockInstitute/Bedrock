# review-of-SuccCardExists: the obligation is NOT inhabited, and it is NOT false

## THE STOP

**`SuccCardExists` (`agents/tasks/LJ-1-526/Probe526.agda:169-174`) IS NOT
INHABITED IN THIS TASK.** The type forms, with no hole and no free name, at the
brief's own binding. I do not inhabit it and I do not postulate it.

**THIS IS A STOP AND NOT A REFUTATION.** Nothing here says the statement is
false. Section `## AMBIENT AGAINST INTERNAL` of
`agents/tasks/LJ-1-526/lj-1.526-report.md` measures that the obstruction the
brief feared does NOT reach the internal predicate.

## WHY THE STOP, IN ONE LINE

**THE OBLIGATION NEEDS EXACTLY ONE THING THE TREE DOES NOT HAVE: AN ORDINAL
L-CARDINAL STRICTLY ABOVE κ.**

    CardAboveL : Type (ℓ-suc ℓ)
    CardAboveL =
        (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
      → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ θ ∈ SL.S ]
           (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

`Probe526.agda:178-183`. **STATED NOWHERE IN THE TREE.** It is the Hartogs fact.
`grep -rn "Hartogs" src` returns nothing, and the brief ordered that a Hartogs
construction must not be assumed to exist.

## WHAT IS DELIVERED IN ITS PLACE

**THE REDUCTION IS GREEN, WITH NO HOLES** (`Probe526.agda:285-292`):

    reduction : CardAboveL → SuccCardExists

Exit 0, three forced rechecks, `runs/s4-sealed-1.out` to `-3.out`, median
14.03 s. **So `CardAboveL` is not merely necessary in my judgement: it is
sufficient, and that is checked by the elaborator and not by this prose.**

**THE LEASTNESS CLAUSE IS NOT WEAKENED.** The brief forbade weakening
`SuccCardL` (`src/L/GCH.lagda.md:50-53`) and it is not weakened. Its fourth
conjunct is PRODUCED by `leastOf` (`src/L/WellOrder/Base.lagda.md:158-160`) over
the ordinal well-order, at `Probe526.agda:255-283`, and it holds at every
ordinal L-cardinal above κ, inside the selection domain and outside it.

## THE TWO ARCHIVE FINDINGS THAT DID NOT SURVIVE

**1. `[LJ-1.91]`'s OBSTRUCTION DOES NOT TRANSFER.**
`archive/dev/LJ-dispatch-index.md:167` records that the AMBIENT `IsCardinal` is
out of reach at the internal ω₁. `ambient→internal` (`Probe526.agda:106-108`) is
green and shows `IsCardinalL` is the WEAKER predicate. Out of reach transfers
upward, never downward.

**2. `[LJ-1.90-A]`'s "IsCardinal is never inhabited" IS NO LONGER TRUE OF THE
TREE.** `archive/dev/LJ-dispatch-index.md:166` counted terms in `src/` and found
none. `ω-card : IsCardinal ω` (`Probe526.agda:135-138`) is four lines from
`finite-excl-ω` (`src/L/InjChain.lagda.md:152-156`). Through the implication
above, `ω-cardL : IsCardinalL ωʟ` follows (`Probe526.agda:141-142`), and
`gchHypAtω` (`Probe526.agda:146-148`) fills the whole κ slot of `GCHStatement`
(`src/L/GCH.lagda.md:60-63`).

**SO THE TROPHY STATEMENT HAS AT LEAST ONE INSTANCE TO PROVE, AND THE CAMPAIGN
IS NOT IN THE `[LJ-1.507]` CASE.**

## WHAT THE CRITIC SHOULD ATTACK FIRST

1. **`Good`'s propositionality** (`Probe526.agda:221-223`). If `IsCardinalL`
   were not an hProp, `leastOf` would not accept it and the leastness clause
   would cost real work. It is an hProp because it is a Π ending in `⊥`
   (`Probe526.agda:214-216`).
2. **The out-of-domain branch of `leastness`** (`Probe526.agda:263-265`). A
   candidate c above the witness θ never enters the selection. I claim
   `ord-tri` closes it without the domain. Check the two branches `δ ∈ c` and
   `δ = c` carry no hidden appeal to the bound.
3. **Whether `CardAboveL` is the WEAKEST sufficient input.** I did not prove
   minimality. A weaker input may exist.
4. **The price of `CardAboveL` is NOT stated here, deliberately.**
   `archive/dev/LJ-dispatch-index.md:167` prices an AMBIENT Hartogs at 490 to
   890 lines. That number does not carry to the internal form and I did not
   carry it. `AGENTS.md:45`.
