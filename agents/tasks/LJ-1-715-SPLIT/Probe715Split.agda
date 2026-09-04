{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.715-SPLIT] PROBE.  bound2-in-limit, mirrored from src/L/Ordinal.lagda.md.
--
--   THE OBLIGATION  <a limit that contains sigma1 and sigma2 contains
--                   fst (bound2 sigma1 sigma2 o1 o2)>.  LANDED IN src/
--                   as L.Ordinal.bound2-in-limit; this file mirrors the
--                   statement verbatim and discharges it through the src
--                   lemma, which is its only proof: bound2's where-bound
--                   family is unnameable outside the clause that defines
--                   it (worktree runs mini-scope.out, NotInScope even
--                   from a sibling in the same module, at
--                   .pod-state/worktrees/LJ-1-715/agents/tasks/LJ-1-715/runs/;
--                   710's runs/t-paths2.out, NotInScope from a probe).
--
--   LAYER           The statement uses the chapter's structure membership
--                   (the membership of the structure 𝒮ᵥ, opened from
--                   ZFStructure); the brief's bracketed small-layer
--                   membership (the library's) glues to it pointwise by
--                   ∈∈ₛ, recorded in V.Model's union-spec round-up.  The
--                   710 probe needed the small layer because it proved
--                   content in a probe frame; the landed lemma only
--                   channels the limit's own clauses, so the chapter's
--                   native layer carries it.
--
-- ONE Agda process per run, GHCRTS heavy caliber (-A64m -I0 -M4g), set
-- on the pane by the program and untouched here.  Nothing is postulated;
-- no hole survives.

open import Base.Prelude
open import Base.Truth

module LJ-1-715-SPLIT.Probe715Split {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_,_⁆; pairing-ax; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV )
open import V.Model {ℓ} using ( ∈sucV-inl )
open import L.Constructible {ℓ}
  using ( IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( IsLimit; bound2 )
open import L.Ordinal {ℓ} using () renaming ( bound2-in-limit to bound2-in-limit-src )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open ZFStructure 𝒮ᵥ

-- THE OBLIGATION, verbatim the brief's bracketed statement over
-- L.Ordinal's IsLimit (IsOrd α is its first conjunct).  The union set
-- is parenthesized because the union symbol is infixr 9 while the
-- structure membership is infix 20: bare, the parser hands the whole
-- membership to the union as its argument (worktree runs
-- diag-bare-union.out, runs/diag-paren.out, same worktree path as
-- above).

bound2-in-limit :
    (α : S) (Lim : IsLimit α)
    (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
    (h₁ : ⟨ σ₁ ∈ˢ α ⟩) (h₂ : ⟨ σ₂ ∈ˢ α ⟩)
  → ⟨ (fst (bound2 σ₁ σ₂ o₁ o₂)) ∈ˢ α ⟩
bound2-in-limit = bound2-in-limit-src

-- THE ROUTE, MEASURED AT THE 710 SITE.  710's review enumerated five
-- routes past the naming wall and concluded no sixth exists for a right
-- side without a name (agents/tasks/LJ-1-710/review-of-bound2-in-limit.md,
-- the five-way enumeration).  The landed proof uses one: leave the family
-- argument of the union clause a HOLE.  The result-type constraint solves
-- the hole by whole-term assignment to bound2's internal union (no
-- pattern restriction bites a meta with no arguments), and the branch
-- obligations, blocked on the hole meanwhile, retry afterward and close
-- by iota at the concrete boolean indices.  Nothing is ever named or
-- written on the right side.  Below, the same route at the small layer
-- (the library membership) over this file's own clauses: the shape 710
-- measured dead at a WRITTEN family closes at a hole.  Transcribed from
-- the worktree probe, where it was measured, so this mirror carries the
-- mechanism it discharges and no second copy of the src proof.

bound2-in-limit-small :
    (α : S) (ordα : IsOrd α)
    (succCl : (x : S) → ⟨ x ∈ₛ α ⟩ → ⟨ sucV x ∈ₛ α ⟩)
    (unionCl : (X : Type ℓ) (f : X → S)
              → ((i : X) → ⟨ f i ∈ₛ α ⟩) → ⟨ (⋃ (sett X f)) ∈ₛ α ⟩)
    (σ₁ σ₂ : S) (o₁ : IsOrd σ₁) (o₂ : IsOrd σ₂)
    (h₁ : ⟨ σ₁ ∈ₛ α ⟩) (h₂ : ⟨ σ₂ ∈ₛ α ⟩)
  → ⟨ (fst (bound2 σ₁ σ₂ o₁ o₂)) ∈ₛ α ⟩
bound2-in-limit-small α _ succCl unionCl σ₁ σ₂ _ _ h₁ h₂ =
  unionCl (Lift {ℓ-zero} {ℓ} Bool) _
    λ { (lift true)  → succCl σ₁ h₁
      ; (lift false) → succCl σ₂ h₂ }
