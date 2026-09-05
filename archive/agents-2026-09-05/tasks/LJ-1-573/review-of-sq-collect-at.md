# Review of `sq-collect-at`: NO-GO, and it is a ruling for the owner

task: LJ-1.573
slot: coder
obligation: `agents/tasks/LJ-1-573/Probe573.agda::sq-collect-at`
verdict: **NO-GO. NOT INHABITED, AND NOT INHABITABLE ON THIS TREE WITHOUT A
PRINCIPLE THE OWNER MUST RULE ON.**

My slot file says writing this file is how a coder states a NO-GO, and that it
does not close the task, because the critic reads it. A stop is a deliverable
(`AGENTS.md:43`).

## THE STOP, IN ONE PARAGRAPH

`SqCollect α` is the axiom of choice over a set-indexed family. It is not a
statement about squares. Written out, its antecedent is `(x : Ix) → ∥ B x ∥₁`
and its consequent is `∥ (x : Ix) → B x ∥₁`, which is `SetChoice`'s implication
letter for letter (`src/Base/Choice.lagda.md:55-56`). The index is an h-set and
the fibre `sq δ` is not a proposition, so no free untruncation applies. The
brief forbids me to reach for an ambient choice principle, and says that if the
only route needs one I must say so and stop. **The route I could close needs
one. I stop.**

## WHY IT IS NOT A GUESS

I did not assert this. I built the reduction and the machine checked it:

    sq-collect-at-from-choice : SetChoice (ℓ-suc ℓ) → SqCollectAt

at `agents/tasks/LJ-1-573/Probe573.agda:135-141`. The whole probe is green,
exit 0, 3.51 s (`agents/tasks/LJ-1-573/runs/final-2.out`). The obligation itself
is absent and the program's own meter says so: `1 UNRESOLVED of 1`, with
`probe_red=False` (`agents/tasks/LJ-1-573/runs/witness-1.out:4-5`).

The level `ℓ-suc ℓ` is measured, not chosen. W3's first run refused `Type ℓ`
(`agents/tasks/LJ-1-573/runs/w3-1.out:4-5`): the squares live at `Type ℓ`, but
the two side conditions are read through `TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))`
and lift the index. So the principle is `SetChoice (ℓ-suc ℓ)`, which is the
owner's own phrase in the charge of `[LJ-1.376]`
(`agents/tasks/LJ-1-376/LJ-1.376.md:10`).

## WHY THE OWNER AND NOT THE MATHEMATICIAN ALONE

The brief says it: this development proves `L ⊨ AC`, and an ambient choice
assumption would be a different claim. Three measured facts make that concrete.

1. **`SetChoice` proves the excluded middle**, by Diaconescu
   (`src/Base/Choice.lagda.md:16-18`). It is strictly stronger than the `lem`
   this chapter already takes, so it is a new and larger classical debt and not
   a rearrangement of the one on the books.
2. **Today it is spent in exactly one place, and that place is the ZFC trophy
   and not the L trophies**: `V⊨ZFC : SetChoice (ℓ-suc ℓ) → isZFCModel`
   (`src/V/Model.lagda.md:528` and `src/Landmarks.lagda.md:54`). Spending
   it on `L ⊨ GCH` would put a choice hypothesis on the front of a trophy whose
   point is that choice is PROVED inside `L`.
3. **`L` already has choice as a THEOREM**, with no ambient principle spent:
   `hasChoiceL` (`src/L/Choice/Transversal.lagda.md:382-383`). So the tree does
   not lack choice. It lacks it at the AMBIENT carrier, which is where this row
   is stated.

## WHAT I DELIVERED INSTEAD OF THE TERM

**The row is not what it looked like, and this is the part the next brief
needs.** `src/`'s own recursion has four cases and only ONE truncates
(`src/L/SquareLawClosed.lagda.md:280-323`). Cases 2 and 3 hand back a BARE
square and throw it away into `∣ _ ∣₁` only because the motive is truncated. The
entire truncation is bought by one term, `κ-injL`.

So I rebuilt that recursion bare, from one untruncated injection, and it is
green:

    Bare.bare-sq-closed : BareLeastInj → SqFam α

at `agents/tasks/LJ-1-573/Probe573.agda:259-261`. It delivers LEVEL 3, the bare
family, which is `[LJ-1.550]`'s `SqAt` and therefore the ORIGINAL row 2. Two
identity functions are the machine's word that the type is that row and not a
look-alike (`Probe573.agda:283`, `:286`).

**THIS IS A RE-LOCALIZATION AND NOT A PAYMENT, AND I WRITE IT DOWN SO NOBODY
READS A GO INTO IT.** `BareLeastInjAt` is not inhabited in my file either.
Untruncating `κ-injL` uniformly over every ordinal is itself a selection.

## THE ONE QUESTION THIS ROW ACTUALLY REDUCES TO

The archive already walked into this wall and already named the way out.
`archive/dev/LJ-dispatch-index.md:362` records `[LJ-1.305]`, the same wall under
the name `InjData`. `archive/dev/LJ-dispatch-index.md:371` records `[LJ-1.314]`
and its verdict: **"Select the CODE, not the function: InjCode is a
proposition, so leastOf untruncates it."**

That cure is one definition away from this row, and the bridge is already a term
in `src/`. `readL` turns a CODE into a BARE ambient injection with no truncation
(`src/L/CantorBernstein.lagda.md:33-35`); I checked it at this row's own types
as `inj-from-code` (`Probe573.agda:354-356`). What blocks it is that
`LeastCardInjL.Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫` is the AMBIENT function type
(`src/L/Cardinal.lagda.md:63-64`). An arbitrary ambient injection carries no
code, so `leastOf` has nothing to be least among, and `κL`'s least is a
different predicate from `InjL`'s.

**THE QUESTION FOR THE MATHEMATICIAN, IN ONE SENTENCE: can `LeastCardInjL` be
restated over the CODED injection `InjL` (`src/L/GCH.lagda.md:37-38`) instead of
the ambient one, so that `leastOf` untruncates the code and `readL` reads it
back?** If it can, this row costs no principle at all. That is a change to
`src/` and a different row, so I named it and did not do it.

## WHAT I DID NOT DO

- I did not postulate and I did not add an axiom. The tree stays `--safe` and
  postulate-free.
- I did not define a term named `sq-collect-at`, at this type or any other. A
  term of that name with a hypothesis in front of it would make the program's
  meter report a GO that is not there.
- I attempted no other row. AD12 gives this brief one obligation.
- Nothing was written under `src/`. Nothing was committed. Nothing was pushed.
