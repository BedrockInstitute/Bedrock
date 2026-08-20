# LJ-1.396 review of `kappa-is-limit`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch `no-go-stated`
asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-396/Probe396.agda:106-110` states `kappa-is-limit` exactly
as the brief writes it:

```agda
kappa-is-limit :
    (a : S) (oa : IsOrd (fst a))
  → (γ : V ℓ) → ⟨ γ ∈ fst (LeastCardInjL.κ a oa) ⟩
  → ⟨ sucV γ ∈ fst (LeastCardInjL.κ a oa) ⟩
```

No hypothesis says `fst a` is infinite. No hypothesis says `γ` contains `ω`.

## THE VERDICT

NO-GO, and it is a refutation, not a failed search. The statement is FALSE, and
the refutation is green in Agda.

`kappa-is-limit-refuted` (`Probe396.agda:152-161`) builds a term of the
negation of the stated type. It instantiates at `a := sucV ∅`, the ordinal 1,
proves `fst κ = sucV ∅`, feeds the member `γ := ∅`, obtains
`⟨ sucV ∅ ∈ sucV ∅ ⟩`, and `∈-irrefl` kills it. So in `--safe` cubical no term
of the stated type exists.

## WHY THE STATEMENT IS FALSE

`LeastCardInjL.κ a oa` is the least member of `sucV (fst a)` that admits an
ambient injection of `⟪ fst a ⟫` (`src/L/Cardinal.lagda.md:104-106`). That is
the cardinality `|fst a|`. For `fst a = sucV ∅` it is `sucV ∅`, a finite
ordinal.

The proof of `fst κ = sucV ∅` in the file has three steps:

1. `fst κ ∈ sucV (sucV ∅)`, from `κ∈sα` (`Probe396.agda:145-146`).
2. `fst κ ≠ ∅`. `κ-inj` gives `∥ ⟪ sucV ∅ ⟫ ↪ ⟪ fst κ ⟫ ∥₁`
   (`Probe396.agda:139-143`). `⟪ sucV ∅ ⟫` is inhabited (`∅ ∈ sucV ∅`) and
   `⟪ ∅ ⟫` is empty, so no injection of the former into the latter exists
   (`noInjEmpty`, `:133-137`).
3. A member of `sucV (sucV ∅)` is `∅` or `sucV ∅`. With step 2, it is
   `sucV ∅` (`:145-150`).

Then `∅ ∈ sucV ∅ = fst κ` (`:160-161`), and the stated conclusion forces
`sucV ∅ ∈ sucV ∅` (`:158`), which `∈-irrefl` (`src/V/Hierarchy.lagda.md:155-156`)
refutes.

The brief's reasoning for TERM 2 reads `⟨ ω ∈ γ ⟩` from nowhere. That
membership is exactly what fails at this site. `suc-absorb` itself demands
`⟨ ω ∈ γ ⟩` (`Probe392.agda:121`), so the "same move at a successor" cannot
fire at a finite member.

## THE TWO CORRECTED TARGETS

Local, BUILT, green: `kappa-is-limit-ω∈γ` (`Probe396.agda:172-184`). Add
`⟨ ω ∈ γ ⟩`. Then `suc∈or≡` (`src/L/Ordinal/Stages.lagda.md:137`) closes:
the first case is the goal, the second dies on `suc-absorb` plus TERM 1.
This is `[LJ-1.392]`'s `amb-limit-ω∈γ` at the selected `κ`.

Global, NOT built: add `⟨ ω ∈ fst a ⟩` and prove full successor-closure of
`fst κ`. That still wants `⟨ ω ∈ fst κ ⟩` (that `|fst a|` is infinite) and
then `⟨ sucV ω ∈ fst κ ⟩`. The second would follow from the first plus the
local repair. The first is not priced here.

## THE SWEEP, BECAUSE A REFUTATION MEASURES ONE SITE (C-42)

This refutation measures ONE site: `a := sucV ∅`. COUNT of the named shape
(successor-closure of `LeastCardInjL.κ` with no infiniteness hypothesis) in
live `src/`: 0. COUNT of that shape as a stated obligation: 1, this task.

Two already-refuted cousins, not this shape:

- `amb-limit` (`agents/tasks/LJ-1-392/Probe392.agda:211-215`)
- `amb-init` (`agents/tasks/LJ-1-393/Probe393.agda:182-185`)

The general claim, that `fst κ = |fst a|` is finite whenever `fst a` is
finite, is reasoning and not a measurement. It is stated in the report as
such and no number is funded against it.
