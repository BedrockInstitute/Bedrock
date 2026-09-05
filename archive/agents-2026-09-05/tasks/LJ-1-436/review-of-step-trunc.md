# Review of `step-trunc`

slot: `coder`. This file states the NO-GO that the brief's branch
`no-go-stated` asks for. Evidence is `file:line` throughout.

## THE STATEMENT, AS THE BRIEF NAMES IT

    step-trunc : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P! δ) → P! α

with

    P! : S → Type (ℓ-suc ℓ)
    P! α = IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
         → ∥ Σ[ f ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ]
               ((u v : ⟪ Lset α ⟫) → f u ≡ f v → u ≡ v) ∥₁

Exact types used: `agents/tasks/LJ-1-436/Probe436.agda:64-67` for `P!`
and `:248-250` for `step-trunc`. Generic in `α`. I did not inhabit
`step-trunc`. I did not weaken `P!`.

The one module hypothesis the brief names is the truncated square law
at the type `[LJ-1.407]` delivered
(`agents/tasks/LJ-1-407/Probe407.agda:262-265`). Predecessor report:
**GO**, no residue (`agents/tasks/LJ-1-407/lj-1.407-report.md:18`). I
did not import that probe. I did not add pairing as data. W3 does not
spend that hypothesis, and W3 did not close, so the hypothesis is not
in this probe's telescope.

## VERDICT

**NO-GO.** The direct route is blocked at the branch family. The
truncation cannot pass through the Pi that `limit-step` demands as
data.

## D-10. THE TYPES

Type of `branch`, `src/L/StageCardinal.lagda.md:534-536`:

    branch : (α : S) (oα : IsOrd α) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩)
             (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P δ)
           → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫

Type `limit-step` demands of its last argument,
`src/L/StageCardinal.lagda.md:396-398`:

    ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)

The two types meet. The family is a Pi of injections. An injection is
a Sigma of a function (`src/L/StageCardinal.lagda.md:221-222`). It is
not an hProp.

`P! δ` after the three ordinal hypotheses is a truncated injection.
`PT.rec` may open it only if the goal is an hProp.

## W3. THE BRANCH FAMILY

`branch-trunc` is the chapter's `branch` with `P` replaced by `P!`
(`Probe436.agda:204-208`). The finite case closed
(`Probe436.agda:220`, matching `src/L/StageCardinal.lagda.md:548`).
It does not read the induction hypothesis.

The first case that reads the hypothesis is the ω-case
(`src/L/StageCardinal.lagda.md:550`). With `P!` that reading has type
`∥ ⟪ Lset ω ⟫ ↪ ⟪ ω ⟫ ∥₁`. `comp-inj` wants `⟪ Lset ω ⟫ ↪ ⟪ ω ⟫`.

`open-ih` (`Probe436.agda:194-202`) is that untruncation. Its body is
`PT.rec` into `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫`. The elaborator asks for

    isProp (⟪ Lset δ ⟫ ↪ ⟪ δ ⟫)

at `Probe436.agda:202.10-14`. That is the only error of the W3-alone
runs: `[UnsolvedInteractionMetas]`, exit 42.

## THE TYPE THIS TASK DELIVERS TO `[LJ-2.5]`

    PiTruncSwap :
      (α : S) (Y : ⟪ α ⟫ → Type ℓ)
      → ((m : ⟪ α ⟫) → ∥ Y m ∥₁)
      → ∥ ((m : ⟪ α ⟫) → Y m) ∥₁

Named at `Probe436.agda:239-243`. Not postulated. Not inhabited. This
is HoTT Book 3.8.1 at the members of an ordinal
(`dev/literature/truncation-and-selection.md:226`).

This swap does not inhabit `branch-trunc`. `branch-trunc` wants the
untruncated Pi. The swap would serve `step-trunc` if `limit-step` ran
under `PT.rec`, because `P! α` is an hProp.

The repair that does not need the swap is a limit step that consumes
the family truncated POINTWISE. That is owed at `[LJ-1.435]`. This
worktree has no `agents/tasks/LJ-1-435/` and no report to cite.

## THE FIRST TERM THAT NEEDS DATA

`src/L/StageCardinal.lagda.md:550`, the first argument of `comp-inj`
in the ω-case of `branch.go`. The type it needs:

    ⟪ Lset ω ⟫ ↪ ⟪ ω ⟫

which is `P ω` after the three ordinal hypotheses, not `P! ω`.

## WHAT WAS NOT DONE

I did not inhabit `step-trunc`. The brief orders that only if W3
closes. W3 did not close. I did not edit `src/`. I did not weaken
`P!`. I did not add pairing as data, an injection as data, a choice
principle, or a postulate.
