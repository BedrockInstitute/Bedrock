{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.488] W3 first: apply SupplyEnv.someEnv with both gates.
-- Layout from Probe485.agda:70-76 (457 pad, carrier in slot 0),
-- not imported. n = 9. Slot indices from lj-1.485-report.md
-- Candidate 1 (LowerAgree.lagda.md:52-58). Brief type
-- ⟨ ω ∈ˢ fst gam ⟩ does not form. Predecessor type
-- ⟨ ω ∈ sucV gam ⟩ from EnvSupply.lagda.md:111.
-- W3 is W3.applied: someEnv with the satisfaction half omitted.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-488.Probe488 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Condensation {ℓ} lem using ( module KValue; envHypB2; module EnvSet )
open import L.Coding.EnvSupply {ℓ} lem using ( module SupplyEnv )
open import L.Coding.EnvSet {ℓ} lem using ( module Generic )
open import Cubical.Data.Nat using ( _+_ ; ℕ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; ω; #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- D-10.  someEnv inputs vs this telescope.
--   SupplyEnv (EnvSupply.lagda.md:107-111) takes the KValue
--   telescope plus ω∈γ.  someEnv (:417-424) takes arNum and three
--   memberships at Lset lam.  someEnvDef (LowerAgree.lagda.md:52-58)
--   takes the three memberships at lookup (suc^6 K) γ.  This pad
--   puts LsetS gam in slot 0 and LsetS lam at suc^6 iK'.  Both
--   gates are hypotheses.  No fourth unsourced input.
-- =====================================================================

-- =====================================================================
-- W3.  Apply someEnv with both gates.  Satisfaction half omitted.
--   applied : Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc^6 iK') Kenv') ⟩)
--   Brief type ⟨ ω ∈ˢ fst gam ⟩ does not form.  Gate type
--   ⟨ ω ∈ sucV gam ⟩ from EnvSupply.lagda.md:111.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- Carrier in slot 0, as [LJ-1.485] measured (Probe485.agda:70-72).
  -- Five remaining pad slots stay dummy. Layout from [LJ-1.457].
  Kenv' : Vec S (11 + 9)
  Kenv' = LsetS gam ordγ ∷ numeralL 0 ∷ numeralL 0
        ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ Kenv

  iK' : Fin (5 + 9)
  iK' = iK

  applied :
      (ya yc b a ar c : S)
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    → ⟨ ω ∈ sucV gam ⟩
    → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩
    → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩
    → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩
    → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩)
  applied ya yc b a ar c arNum ω∈γ yaK ycK arK =
    let module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ
        (E , (EK , _)) = SE.someEnv ya yc b a ar c arNum yaK ycK arK
    in  E , EK

  -- Obligation. someEnvDef {9} with both gates, Candidate 1 indices.
  -- Body: someEnv for (E, EK), then EnvSet.back Generic.Holds at the
  -- 27-slot env. That is the same generic transfer someEnv uses at 4
  -- slots (EnvSupply.lagda.md:440-444), instantiated at this layout.
  someEnv-doubly-gated :
      (ya yc b a ar c : S)
    → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    → ⟨ ω ∈ sucV gam ⟩
    → ⟨ fst ya ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩
    → ⟨ fst yc ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩
    → ⟨ fst ar ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩
    → Σ S (λ E → ⟨ fst E ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) Kenv') ⟩
        × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv') ⊨
              envHypB2 {11 + 9} zero (suc (suc (suc (suc (suc (suc iK')))))) ⟩)
  someEnv-doubly-gated ya yc b a ar c arNum ω∈γ yaK ycK arK =
    let module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈γ
        (E , (EK , _)) = SE.someEnv ya yc b a ar c arNum yaK ycK arK
        module G = Generic SE.B₀ ar
        γ27 = E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Kenv'
        iAr = suc (suc (suc (suc (suc zero))))
        iB  = suc (suc (suc (suc (suc (suc (suc zero))))))
        iK27 = suc (suc (suc (suc (suc (suc (suc
                 (suc (suc (suc (suc (suc (suc iK'))))))))))))
        arityK27 : (N v : S)
                 → ⟨ fst v ∈ fst N ⟩
                 → ⟨ fst N ∈ fst (lookup iK27 γ27) ⟩
                 → ⟨ fst v ∈ fst (lookup iK27 γ27) ⟩
        arityK27 N v hv hNK = SE.transK v N hv hNK
        envInK27 z hz = SE.envInK-gen γ27 iAr iB refl arNum arK z hz
        module ES = EnvSet {7 + (11 + 9)} zero iAr iB iK27 γ27
                      arityK27 EK arK envInK27
        module H = G.Holds {7 + (11 + 9)} γ27 zero iAr iB refl refl refl
    in  E , (EK , ES.back H.holds)

-- =====================================================================
-- THE OBLIGATION, at the probe top level so the witness name
-- `someEnv-doubly-gated` resolves.  W3.applied is the same application
-- with the satisfaction half omitted.
-- =====================================================================

someEnv-doubly-gated = W3.someEnv-doubly-gated
