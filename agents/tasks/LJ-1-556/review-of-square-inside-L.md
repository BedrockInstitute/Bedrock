# NO-GO on `square-inside-L`

## THE STOP, IN ONE SENTENCE

**The square law is not a per-ordinal theorem in this tree, ambiently or
internally.** It is one ∈-induction over all ordinals
(`src/L/SquareLawClosed.lagda.md:325`), and the hypothesis its inductive step
spends at each ordinal is strictly stronger than `IsCardinalL κ`. So the
brief's type is under-hypothesized: no route the tree has can discharge it,
and the two steps that fail are independent of each other.

I did not inhabit the brief's type. No term named `square-inside-L` exists in
any file of this task. Nothing is postulated and no hole is left.

## D-10, AND IT IS ANSWERED BEFORE ANY AGDA

The brief orders: read `L.Ordinal.SquareLaw`, say at `file:line` what its
injection is built from, then say whether each step of it is available inside
L, and name the first step that is not.

### What the ambient injection is built from

`Initial.pair` (`src/L/Ordinal/SquareLaw.lagda.md:945`) is

    pair p = fiber α {x = colA p} (col∈α p) .fst

and it decomposes into six pieces, in this order.

| # | Piece | `file:line` |
|---|---|---|
| 1 | `Pair α oα = ⟪ α ⟫ × ⟪ α ⟫`, the index type | `src/L/Ordinal/SquareLaw.lagda.md:212-213` |
| 2 | `ordSWO`, the membership order on the members of `α` | `src/L/Ordinal/SquareLaw.lagda.md:176` |
| 3 | `maxOrd` and `_≺_`, the max-then-lexicographic order on pairs | `src/L/Ordinal/SquareLaw.lagda.md:200`, `:215` |
| 4 | `wf≺` / `godSWO`, well-foundedness of `_≺_` via `prodSWO` on the three-fold lexicographic product | `src/L/Ordinal/SquareLaw.lagda.md:302`, `:308` |
| 5 | `col`, the collapse, by well-founded recursion with step `colStep p rec = ⋃ (sett Pair (λ r → colPick p rec r (≺-dec r p)))` | `src/L/Ordinal/SquareLaw.lagda.md:378`, `:384` |
| 6 | `col∈α`, the exclusion chase, which spends `noinj²` and `finite-excl` | `src/L/Ordinal/SquareLaw.lagda.md:862`, `:931` |

`col-inj` (`src/L/Ordinal/SquareLaw.lagda.md:427`) is what makes `pair`
injective, and it is a corollary of 5 and of `col-mono` (`:406`); it adds no
new ingredient.

### Which steps internalize

**1 INTERNALIZES, AND IT IS MEASURED.** W3 built `κ × κ` as an L-set with both
projections, and the second projection is untruncated. `Probe556.agda`,
section 1, `Square.sqL`, `Square.sqL-in`, `Square.sqL-out`. Exit 0.

**2, 3 AND 4 INTERNALIZE AS FORMULAS, AND ONE OF THEM IS MEASURED.** The
recursion template the tree already has, `L.Coding.Sequence.RecShape`
(`src/L/Coding/Sequence.lagda.md:281`), takes its step as a `Formula` and
never as a set, so the order data does not have to become an L-set at all: it
has to become a condition on the two components of a pair. Section 2 of
`Probe556.agda` measures that at the membership order (`Square.ltFo`,
`Square.ltL`, `Square.ltL-in`, `Square.ltL-out`), and builds the set too,
because once the formula exists the carve is one more `hasSeparationL`. I
measured one condition and I did not measure the max-then-lexicographic one:
AGENTS.md:45 forbids the transfer by analogy, so what I claim for 3 and 4 is
that the DEVICE is the same, not that their adequacy is proved.

**5 IS THE FIRST STEP THE TREE CANNOT TAKE INSIDE L.** `col`
(`src/L/Ordinal/SquareLaw.lagda.md:384`) is `W.induction` over the ambient
type `Pair`, producing an ambient `S`-valued function. The tree's only route
from such a function to an internal table is `L.Recursion`, and that chapter
states its own condition exactly: "A recursive definition is internalizable
when its graph is expressible, and nothing about the recursion's shape, its
depth, its order of descent, or the complexity of its clauses appears in the
condition" (`src/L/Recursion.lagda.md:259-262`). The form to fill is
`Definition` (`src/L/Recursion.lagda.md:272`): `dom`, `fn`, `graph`,
`defines`, `only`. `dom` is delivered by W3 and `fn` is `col` itself.
**`graph`, `defines` and `only` do not exist in the tree for `col`, and
nothing weaker will do.**

**6 IS A SECOND WALL, INDEPENDENT OF 5, AND NO AMOUNT OF CODING REMOVES IT.**
This is the one that kills the brief's TYPE rather than its price. See below.

## WHY THE BRIEF'S TYPE CANNOT BE DISCHARGED, EVEN WITH 5 PAID

`col∈α` (`src/L/Ordinal/SquareLaw.lagda.md:931`) closes through `exclude`
(`:862`), and `exclude` spends `noinj²`, the fourth conjunct of `Init`
(`src/L/Ordinal/SquareLaw.lagda.md:692`, fourth conjunct at `:696-698`):

    ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
     → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
     → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)

**`Init` is a HYPOTHESIS in `SquareLaw`, and the tree discharges it in exactly
one place**: `clause4-at-kappa` (`src/L/SquareLawClosed.lagda.md:96`). That
derivation takes TWO inputs and both matter here.

1. `κ-min-atL` (`src/L/SquareLawClosed.lagda.md:86`), the AMBIENT leastness
   of the ambient least cardinal, from `LeastCardInjL.κ-min-at`. It refutes an
   AMBIENT injection `⟪ fst a ⟫ ↪ ⟪ fst δ ⟫`, with no code anywhere in it.
2. `ih` (`src/L/SquareLawClosed.lagda.md:99-100`), **the square law at every
   smaller infinite ordinal**:

       ih : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
          → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁

   `clause4-at-kappa` spends it at `src/L/SquareLawClosed.lagda.md:106`, to
   turn `f : κ ↪ β × β` into `κ ↪ β` and then contradict 1. `ih` is the
   induction hypothesis of `sq-trunc-closed`
   (`src/L/SquareLawClosed.lagda.md:325`), an `∈-induction` with four cases.

**`IsCardinalL κ` supplies NEITHER of them.** Its statement
(`src/L/Cardinal.lagda.md:230-233`) is

    IsCardinalL κ =
      (δ : S) → ⟨ fst δ ∈ fst κ ⟩
              → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)

and `InjCode F κ δ` (`src/L/Cardinal.lagda.md:223`) is an injection of `κ`
into `δ`. Two gaps, and they are independent.

- **CODED versus AMBIENT.** `IsCardinalL` refutes only injections that carry
  a code. The chase's injection is built ambiently, from the ambient
  hypothesis `colA p ≡ α`, by `comp₀` (`src/L/Ordinal/SquareLaw.lagda.md:835`)
  through `AbstractH₀.h₀` (`:828`). `[LJ-1.533]` measured that nothing codes
  an arbitrary ambient injection
  (`agents/tasks/LJ-1-533/lj-1.533-report.md:30`). This gap CLOSES if step 5
  is paid, because then the chase is internal from the start and its
  injection carries a code by construction. It does not close otherwise.
- **`δ` versus `β × β`.** `IsCardinalL κ` refutes an injection of `κ` into a
  smaller set. `noinj²` must refute an injection of `κ` into a smaller set's
  SQUARE. **The bridge between the two is the square law at that smaller
  set.** This gap does NOT close by paying step 5, and it does not close by
  coding anything. It closes only by having the theorem below `κ`.

So the brief's type asks for the conclusion of an induction while binding none
of the induction hypothesis. The obligation is TRUE, and it is not provable
from what it binds.

## THE CORRECTED TARGET (D-10 ORDERS IT RECORDED BESIDE THE ORIGINAL)

`Probe556.agda` writes both types out and inhabits neither.

    BriefTarget =                              -- section 3, the original
      (κ : S) → IsOrd (fst κ) → IsCardinalL κ → InternalSquare κ

    SquareStep =                               -- section 4, corrected
        (κ : S) → IsOrd (fst κ)
      → IsCardinalL κ
      → ( (β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩ → InternalSquare β )
      → InternalSquare κ

    InternalSquare κ = ∥ Σ[ F ∈ S ] InjCode F (Square.sqL κ) κ ∥₁

`SquareStep` is the internal image of `init-at-kappa`
(`src/L/SquareLawClosed.lagda.md:166`) composed with `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`), and it is the thing a next brief can
fund. The closed form is then one internal ∈-induction over `SquareStep`, the
internal image of `sq-trunc-closed` (`src/L/SquareLawClosed.lagda.md:325`).

**AND `SquareStep` IS STILL NOT A TASK.** Even with its induction hypothesis
in hand, discharging it needs step 5, which is `Definition`'s three unwritten
fields for `col`. `[LJ-1.552]` already said this in its own words:
"Step 2 is a chapter and not a task"
(`agents/tasks/LJ-1-552/review-of-succ-assignment.md:190`). **This review
agrees with it and adds the two things it could not name**: which step of the
ambient proof is the one that does not internalize, and that the obligation's
type is short one hypothesis.

## WHAT WOULD REOPEN THIS

Three things, in this order, and none is a task on its own.

1. **The step formula for `col`, with its adequacy.** Instantiate
   `L.Coding.Sequence.RecShape` (`src/L/Coding/Sequence.lagda.md:281`) at
   `dom = Square.sqL κ` with a `Step` that says
   `z = ⋃ { sucV (f r) : r ≺ c }`. The order `≺` enters as a FORMULA, not as
   a set, so section 2's device is what carries it. **`L.Choice.Table` names
   the same debt for its own instance** and calls it three things and not one
   (`src/L/Choice/Table.lagda.md:874-877`).
2. **`col∈κ` internally, from `SquareStep`'s induction hypothesis.** The
   ambient chase is `exclude` (`src/L/Ordinal/SquareLaw.lagda.md:862`) and
   its three branches are `finite-excl`, `β≠ω` and `noinj²`. With 1 paid, the
   injection the chase builds is internal and carries a code, so
   `IsCardinalL κ` becomes spendable, and the induction hypothesis is what
   converts `β × β` to `β`.
3. **The closed form**, one internal ∈-induction, the image of
   `sq-trunc-closed`.

## WHAT WAS NOT DONE

No postulate, no hole, no module parameter that asserts the square law. `src/`
is untouched. I did not build `Codes δ κ` and I did not touch the assignment
([LJ-1.557] takes the other step). I did not try to code the ambient
injection: the brief forbids it and `[LJ-1.533]` already measured it. No term
named `square-inside-L` exists in any file of this task. I did not commit and
did not push.
