{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.397] W3 PROBE.  `code-lands`, the one implication from the
-- `S` form of the code quantifier to the `Mem` form, stated alone and
-- run FIRST.  It reduces to ONE step, the PLACEMENT obligation
-- `⟨ fst F ∈ Lset (SiteBound.β a) ⟩` from `InjCode F a c`, named below
-- as `Placement`.  That obligation is the residue [LJ-1.386] marked
-- unbuilt ("bookkeeping about stages",
-- agents/tasks/LJ-1-386/lj-1.386-report.md, section 2): nothing
-- delivered places a code `F` for `a ↪ c` inside `Lset (SiteBound.β a)`.
-- So `code-lands` is delivered CONDITIONAL on `Placement`, and the
-- repaired hypothesis of `coded-arrow` carries the `Mem` form instead.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-397.CodeLands {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset→isL )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem
  using ( InjCode; module SiteBound )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- The residue: a code `F` for `a ↪ c` lands in the site bound of `a`.
-- This is the single step the `S`-to-`Mem` implication owes, and no
-- delivered lemma pays it.
Placement : Type (ℓ-suc ℓ)
Placement = (a c F : S) → InjCode F a c → ⟨ fst F ∈ Lset (SiteBound.β a) ⟩

-- The full implication, reducing to `Placement`.  Given the placement,
-- the rest is the proof-irrelevance of the `isL` certificate, a
-- transport of the code along `Σ≡Prop`.
code-lands : Placement → (a c : S) → ∥ Σ[ F ∈ S ] InjCode F a c ∥₁
           → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
                   InjCode (SiteBound.up a F) a c ∥₁
code-lands place a c h = PT.map (into place) h
  where
  open SiteBound a renaming ( up to upβ )

  into : Placement → Σ[ F ∈ S ] InjCode F a c
       → Σ[ F ∈ Mem (Lset (SiteBound.β a)) ] InjCode (SiteBound.up a F) a c
  into place (F , code) = (fst F , p) , transported
    where
    p : ⟨ fst F ∈ Lset (SiteBound.β a) ⟩
    p = place a c F code
    upβF≡F : upβ (fst F , p) ≡ F
    upβF≡F = Σ≡Prop (λ v → snd (isL v)) refl
    transported : InjCode (upβ (fst F , p)) a c
    transported = subst (λ G → InjCode G a c) (sym upβF≡F) code
