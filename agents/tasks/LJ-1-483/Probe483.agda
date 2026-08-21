{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.483] W3 first: can codesK be applied at the [LJ-1.473] frame?
-- Frame from Probe473.agda:61-67, not imported. n = 9, carrier in slot 0.
-- codesK is a module hypothesis at Condensation.lagda.md:2782-2786.
-- W3 is no-code and arNum-from-codesK. The obligation is not
-- inhabited: c∈ and shEq have no source at someEnvDef.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-483.Probe483 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Condensation {ℓ} lem using ( module KValue )
open import V.Coding {ℓ} using ( pr )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ∅-empty )
open InfinitySet {ℓ} using ( sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- D-10.  codesK vs SupplyEnv.someEnv, side by side.
--   codesK (Condensation.lagda.md:2782-2786) takes c∈ in C and a
--   shape equation, then yields arK, aK, and
--   ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁ as its third component.
--   SupplyEnv.someEnv (EnvSupply.lagda.md:417-424) takes that
--   truncation as arNum.  The third component IS arNum's type.
--   codesK wants a code c in C and the shape equation before it
--   yields anything.  At this frame C is slot 2 of the pad, a dummy
--   numeralL 0.  someEnvDef (LowerAgree.lagda.md:52-58) takes
--   neither input.
-- =====================================================================

-- =====================================================================
-- W3.  codesK at the [LJ-1.473] frame, obligation omitted.
--   AbstractFrame's C is suc (suc zero) of γ' (TwelveAgree.lagda.md:494,
--   LowerAgree.lagda.md:255).  At the pad that slot is dummy
--   numeralL 0.  no-code: the domain of codesK is empty.  The
--   projection arNum-from-codesK typechecks when c∈ and shEq are
--   given, and those two have no source at someEnvDef.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- Carrier in slot 0, as [LJ-1.473] measured (Probe473.agda:61-64).
  -- Five remaining pad slots stay dummy.
  Kenv' : Vec S (11 + 9)
  Kenv' = LsetS gam ordγ ∷ numeralL 0 ∷ numeralL 0
        ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ Kenv

  iK' : Fin (5 + 9)
  iK' = iK

  -- AbstractFrame C = suc (suc zero). LowerAgree.lagda.md:255.
  C : Fin (11 + 9)
  C = suc (suc zero)

  -- Row K = suc^6 of TFacts.K. LowerAgree.lagda.md:255.
  Krow : Fin (11 + 9)
  Krow = suc (suc (suc (suc (suc (suc iK')))))

  C-slot : lookup C Kenv' ≡ numeralL 0
  C-slot = refl

  -- Domain of codesK at this frame is empty: C is # 0.
  no-code : (c : S) → ⟨ fst c ∈ fst (lookup C Kenv') ⟩ → Empty.⊥
  no-code c c∈ =
    ∅-empty (fst c)
      (∈∈ₛ {a = fst c} {b = ∅} .fst
        (subst (λ w → ⟨ fst c ∈ w ⟩)
               (cong fst C-slot ∙ numeralL-fst zero)
               c∈))

  -- codesK as a module hypothesis at Condensation.lagda.md:2782-2786,
  -- instantiated at this frame's C and Krow.
  module FromCodes
    (codesK : (c ar a : S)
            → ⟨ fst c ∈ fst (lookup C Kenv') ⟩
            → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
            → ⟨ fst ar ∈ fst (lookup Krow Kenv') ⟩
              × ⟨ fst a ∈ fst (lookup Krow Kenv') ⟩
              × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
    where

    arNum-from-codesK :
        (c ar a : S)
      → ⟨ fst c ∈ fst (lookup C Kenv') ⟩
      → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
      → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    arNum-from-codesK c ar a c∈ shEq = codesK c ar a c∈ shEq .snd .snd
