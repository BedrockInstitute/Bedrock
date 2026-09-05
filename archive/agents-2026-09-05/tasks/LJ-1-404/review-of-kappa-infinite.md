# LJ-1.404 review of `kappa-infinite`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch `no-go-stated`
asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-404/Probe404.agda:141-145` states `kappa-infinite` with the
membership spelling of `κ-min-at` (`src/L/Cardinal.lagda.md:140-142`), which is
`∈ˢ`:

```agda
kappa-infinite :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ ω ∈ˢ fst a ⟩
  → ⟨ ω ∈ˢ fst (LeastCardInjL.κ a oa) ⟩
```

The brief's displayed type uses the bare `∈`. The two convert, and the site
uses `∈ˢ`.

## THE VERDICT

NO-GO, and it is a refutation, not a failed search. The statement is FALSE, and
the refutation is green in Agda.

`kappa-infinite-refuted` (`Probe404.agda:182-188`) builds a term of the
negation of the stated type. It instantiates at `a := sucV ω`, proves
`fst κ ≡ ω` (`κ≡ω`, `:175-180`), and the stated conclusion becomes
`⟨ ω ∈ ω ⟩`, which `∈-irrefl` kills (`src/V/Hierarchy.lagda.md:155-156`).

So in `--safe` cubical no term of the stated type exists.

## WHY THE STATEMENT IS FALSE

`LeastCardInjL.κ a oa` is the least member of `sucV (fst a)` that admits an
ambient injection of `⟪ fst a ⟫` (`src/L/Cardinal.lagda.md:104-123`). That is
the cardinality `|fst a|`. For `fst a = sucV ω` it is `ω`, which does not
contain `ω`.

The brief's reasoning kills only the finite case `κ ∈ ω`, by `finite-excl`.
Trichotomy of `κ` against `ω` (`src/L/Ordinal/Linear.lagda.md:136`) has three
summands. The equality `κ ≡ ω` remains, and at this site it holds.

The proof of `fst κ ≡ ω` in the file has three steps:

1. `fst κ ∈ sucV (sucV ω)`, from `κ∈sα` (`Probe404.agda:176`).
2. `fst κ` is not a numeral. `kappa-not-finite` (`:124-133`) plus `ω ∈ sucV ω`
   (`self∈sucV ω`) refute `κ ∈ ω`.
3. `fst κ ≢ sucV ω`. If it were, then `ω ∈ κ`, and `κ-min-at` at `δ := ω`
   with `Shiftω.shift↪ : ⟪ sucV ω ⟫ ↪ ⟪ ω ⟫` (`src/L/Absorption.lagda.md:189-190`,
   instantiated at `ω`) contradicts minimality (`:168-173`).

A member of `sucV (sucV ω)` is a member of `sucV ω` or `sucV ω` itself. A
member of `sucV ω` is a member of `ω` or `ω`. Steps 2 and 3 leave `κ ≡ ω`.

## THE CORRECTED TARGET

BUILT, green: `kappa-not-finite` (`Probe404.agda:124-133`). From `ω ∈ a` it
follows that `κ ∉ ω`. Together with `infinite-or-omega`
(`Probe404.agda:52-59`) that is `(κ ≡ ω) ⊎ ⟨ ω ∈ κ ⟩`. That is the honest
infiniteness of the selected cardinal.

`kappa-is-limit⁺` (`Probe404.agda:202-243`) is GREEN as the brief states it.
The case `κ ≡ ω` is successor-closure of `ω` by `ω-limit`
(`src/L/InjChain.lagda.md:109`). The case `ω ∈ κ` closes `γ ≡ ω` by
`suc∈or≡` (`src/L/Ordinal/Stages.lagda.md:137`) plus `Shiftω.shift↪` plus
`κ-min-at`. The brief named `⟨ sucV ω ∈ fst κ ⟩` as a possible extra
hypothesis. That membership is a conclusion in this case, not a hypothesis.

## THE SWEEP, BECAUSE A REFUTATION MEASURES ONE SITE (C-42)

This refutation measures ONE site: `a := sucV ω`. COUNT of the named shape
(`ω ∈` the selected `κ`, from `ω ∈ a`) in live `src/`: 0. COUNT of that shape
as a stated obligation: 1, this task.

Cousins, not this shape:

- `kappa-is-limit` (`agents/tasks/LJ-1-396/Probe396.agda:106-110`),
  successor-closure of `κ` with no infiniteness hypothesis, refuted at
  `a := sucV ∅`.
- `amb-init` (`agents/tasks/LJ-1-393/Probe393.agda:182-185`), `Init` from
  `AmbCard` without `⟨ sucV ω ∈ α ⟩`.

The general claim, that `|fst a| = ω` whenever `ω ∈ a` and `⟪ fst a ⟫` injects
into `⟪ ω ⟫`, is reasoning and not a measurement. It is stated in the report
as such and no number is funded against it.
