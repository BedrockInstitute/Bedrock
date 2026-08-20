{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.411] PROBE.  A code as DATA, and no placement anywhere.
-- Lives in agents/tasks/LJ-1-411/ and lands nothing in src/.
--
-- W3 first: code-has-stage, the truncated CODE to a truncated ORDINAL
-- statement.  State it alone, run it, report its code lines before
-- writing step 4 (code-as-data).
--
-- Two carriers: L.Stage opens S from 𝒮ᵥ (renamed Sᵥ here);
-- L.Cardinal opens S from 𝒮ʟ (kept as S).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-411.Probe411 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset; Lset→isL )
open import L.Stage {ℓ} lem using ( leastOrd; stage; stage-ord; stage-mem )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
open import L.Cardinal {ℓ} lem using ( InjCode )

open import Cubical.Data.Sigma using ( Σ≡Prop )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ ) renaming ( S to Sᵥ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- Step 1.  CodeAt, a property of a BARE ordinal.  No IsOrd, no crossing.
-- Generic in a and b.  W2.
-- =====================================================================

CodeAt : (a b : S) → Sᵥ → Ω
CodeAt a b σ =
  (∥ Σ[ F ∈ S ] (⟨ fst F ∈ˢ Lset σ ⟩ × InjCode F a b) ∥₁) , squash₁

-- =====================================================================
-- W3.  Step 2 alone.  Truncated code to truncated ordinal statement.
-- σ := stage (fst F) (snd F), stage-ord, stage-mem.  No numeral, no
-- site, no named stage.  isPropInjCode is not used here.
-- =====================================================================

code-has-stage :
    (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁
  → ∥ Σ[ σ ∈ Sᵥ ] (IsOrd σ × ⟨ CodeAt a b σ ⟩) ∥₁
code-has-stage a b =
  PT.rec squash₁
    (λ { (F , inj) →
      ∣ stage (fst F) (snd F)
      , ( stage-ord (fst F) (snd F)
        , ∣ F , (stage-mem (fst F) (snd F) , inj) ∣₁ )
      ∣₁ })

-- =====================================================================
-- Steps 3 and 4.  leastOrd CodeAt, then leastOf (orderAt σ₀ oσ₀).
-- isPropInjCode is [LJ-1.401]'s term, taken as a module hypothesis.
-- Probe401 is not imported and is not rebuilt.
-- upAt is SiteBound.up written generic in the ordinal
-- (src/L/Cardinal.lagda.md:171-172).
-- =====================================================================

module _
  (isPropInjCode : (F a b : S) → isProp (InjCode F a b))
  where

  upAt : (σ : Sᵥ) → IsOrd σ → Mem (Lset σ) → S
  upAt σ oσ (x , mem) = x , Lset→isL σ oσ x mem

  up-from : (σ : Sᵥ) (oσ : IsOrd σ) (F : S)
          → (mem : ⟨ fst F ∈ˢ Lset σ ⟩)
          → F ≡ upAt σ oσ (fst F , mem)
  up-from σ oσ F mem = Σ≡Prop (λ x → snd (isL x)) refl

  code-as-data :
      (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁ → Σ[ F ∈ S ] InjCode F a b
  code-as-data a b h = upAt σ₀ oσ₀ F-mem , inj
    where
    got = leastOrd (CodeAt a b) (code-has-stage a b h)
    σ₀ = got .fst
    oσ₀ = got .snd .fst
    payload = got .snd .snd .fst

    Good : Mem (Lset σ₀) → hProp (ℓ-suc ℓ)
    Good m = InjCode (upAt σ₀ oσ₀ m) a b
           , isPropInjCode (upAt σ₀ oσ₀ m) a b

    nonempty : ∥ Σ[ m ∈ Mem (Lset σ₀) ] ⟨ Good m ⟩ ∥₁
    nonempty = PT.rec squash₁
      (λ { (F , (mem , injF)) →
        ∣ (fst F , mem)
        , subst (λ G → InjCode G a b) (up-from σ₀ oσ₀ F mem) injF
        ∣₁ })
      payload

    picked = leastOf (orderAt σ₀ oσ₀) lem Good nonempty
    F-mem = fst picked
    inj = fst (snd picked)
