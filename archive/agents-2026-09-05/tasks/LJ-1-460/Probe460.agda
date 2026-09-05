{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.460] W3 FIRST, then the obligation.  A code for the shift
-- injection, from the graph ShiftGraph already carved.
--
--   W3 FIRST  `range-clause`.  From G-out (via pair-out, which is
--             G-out at the coded pair).  Obligation omitted.
--             Typechecked ALONE.
--
--   TERM      `shift-coded`.  Written after W3 is green.  The four
--             conjuncts are ShiftGraph exports.  Domain transported
--             along D ≡ sucʟ γ.
--
-- ONE Agda process per run, GHCRTS the wide caliber the program set
-- on the pane, untouched here.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-460.Probe460 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Axioms.Numerals {ℓ} using ( sucʟ; sucʟ-fst )
open import L.Absorption {ℓ} lem using ( module ShiftGraph )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import Cubical.Data.Sigma using ( Σ≡Prop )

open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_ )
open import Cubical.Data.Nat using ( ℕ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  The range clause from G-out, via pair-out.  InjCode omitted.
-- pair-out is PT.map over G-out at the coded pair
-- (src/L/Absorption.lagda.md:431).  The conclusion is an hProp, so
-- PT.rec spends the truncation.
-- =====================================================================

module W3 (γ : S) (oγ : IsOrd (fst γ))
          (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
          (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩) where

  module SG = ShiftGraph γ oγ γ∉ω numerals

  range-clause :
      (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst SG.G ⟩ → ⟨ fst y ∈ fst γ ⟩
  range-clause x y h = PT.rec (snd (fst y ∈ fst γ)) go (SG.pair-out x y h)
    where
    go : _
    go r = subst (λ w → ⟨ w ∈ fst γ ⟩) (sym (r .snd .snd .snd))
      (member (fst SG.C) (SG.sh (fiber (fst SG.D) (r .snd .fst) .fst)))

-- =====================================================================
-- THE OBLIGATION.  Four conjuncts are ShiftGraph exports
-- (src/L/Absorption.lagda.md:452-498, opened publicly at :604-605).
-- Domain D is sucV (fst γ) with a transported isL; sucʟ γ agrees on
-- fst by sucʟ-fst.  InjCode sees the assignment, so the tuple moves
-- by Σ≡Prop.  No extra hypothesis.  No postulate.
-- =====================================================================

shift-coded :
    (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁
shift-coded γ oγ γ∉ω numerals = ∣ SG.G , code ∣₁
  where
  module SG = ShiftGraph γ oγ γ∉ω numerals

  codeD : InjCode SG.G SG.D γ
  codeD = SG.sv , SG.dm , SG.ij , SG.ran

  D≡suc : SG.D ≡ sucʟ γ
  D≡suc = Σ≡Prop (λ x → snd (isL x)) (sym (sucʟ-fst γ))

  code : InjCode SG.G (sucʟ γ) γ
  code = subst (λ a → InjCode SG.G a γ) D≡suc codeD
