{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.457] W3 first, then the obligation tfacts-prefix.
-- n = 9: X : Fin 14 over γ' : S ^ 20, read at suc^6 X.
-- KValue's fourteen slots sit at positions 6 to 19. The first six
-- are filler. W3 is W3.one-tag. The obligation is tfacts-prefix.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-457.Probe457 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.TwelveAgree {ℓ} lem using ()
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS

-- =====================================================================
-- D-10.  n = 9 reconciles the two conventions.
--   TFacts: Fin (5 + n) over S ^ (11 + n), lookup at suc^6
--           (TwelveAgree.lagda.md:129-133).
--   KValue: Fin 14 over S ^ 14, lookup at a bare index
--           (Condensation.lagda.md:7387-7409).
--   n = 9: Fin 14 over S ^ 20. Pad six fillers. 6 + 14 = 20.
--   n = 3: Fin 8 over S ^ 14. That is the 14 != 8 of [LJ-1.450].
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  -- Six dummy fillers. tagEq and numK skip them via suc^6.
  Kenv' : Vec S (11 + 9)
  Kenv' = numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
        ∷ Kenv

  i0' : Fin (5 + 9)
  i0' = i0

  -- W3. One tagEq field at the re-laid-out environment.
  -- Inhabited from KValue.facts (Condensation.lagda.md:7413).
  one-tag : fst (lookup (suc (suc (suc (suc (suc (suc i0')))))) Kenv')
          ≡ fst (numeralL 0)
  one-tag = KFacts.tagEq0 facts

-- =====================================================================
-- THE OBLIGATION.  24 TFacts fields (tagEq0-11, numK0-11), copied from
-- TwelveAgree.lagda.md:133-156, as a Sigma at n = 9.  Indices are
-- KValue's Fin 14 names (Condensation.lagda.md:7395-7409), now at
-- Fin (5 + 9).  Kenv' pads six fillers in front of Kenv.
-- Do not inhabit TFacts.  The other 31 fields stay untouched.
-- =====================================================================

iK' : Fin (5 + 9)
iK' = suc zero
i0' : Fin (5 + 9)
i0' = suc (suc zero)
i1' : Fin (5 + 9)
i1' = suc (suc (suc zero))
i2' : Fin (5 + 9)
i2' = suc (suc (suc (suc zero)))
i3' : Fin (5 + 9)
i3' = suc (suc (suc (suc (suc zero))))
i4' : Fin (5 + 9)
i4' = suc (suc (suc (suc (suc (suc zero)))))
i5' : Fin (5 + 9)
i5' = suc (suc (suc (suc (suc (suc (suc zero))))))
i6' : Fin (5 + 9)
i6' = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
i7' : Fin (5 + 9)
i7' = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
i8' : Fin (5 + 9)
i8' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
i9' : Fin (5 + 9)
i9' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
i10' : Fin (5 + 9)
i10' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
i11' : Fin (5 + 9)
i11' = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))

Kenv' :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → Vec S (11 + 9)
Kenv' = W3.Kenv'

TFactsPrefix : Vec S (11 + 9) → Type (ℓ-suc ℓ)
TFactsPrefix γ' =
    (fst (lookup (suc (suc (suc (suc (suc (suc i0')))))) γ') ≡ fst (numeralL 0))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i1')))))) γ') ≡ fst (numeralL 1))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i2')))))) γ') ≡ fst (numeralL 2))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i3')))))) γ') ≡ fst (numeralL 3))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i4')))))) γ') ≡ fst (numeralL 4))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i5')))))) γ') ≡ fst (numeralL 5))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i6')))))) γ') ≡ fst (numeralL 6))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i7')))))) γ') ≡ fst (numeralL 7))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i8')))))) γ') ≡ fst (numeralL 8))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i9')))))) γ') ≡ fst (numeralL 9))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i10')))))) γ') ≡ fst (numeralL 10))
  × (fst (lookup (suc (suc (suc (suc (suc (suc i11')))))) γ') ≡ fst (numeralL 11))
  × ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩
  × ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc iK')))))) γ') ⟩

tfacts-prefix :
    (lam : V ℓ) (ordλ : IsOrd lam)
    (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ lam ⟩)
    (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  → TFactsPrefix (Kenv' lam ordλ succλ ∅∈λ gam ordγ γ∈λ)
tfacts-prefix lam ordλ succλ ∅∈λ gam ordγ γ∈λ =
  let open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  in  KFacts.tagEq0 facts
    , KFacts.tagEq1 facts
    , KFacts.tagEq2 facts
    , KFacts.tagEq3 facts
    , KFacts.tagEq4 facts
    , KFacts.tagEq5 facts
    , KFacts.tagEq6 facts
    , KFacts.tagEq7 facts
    , KFacts.tagEq8 facts
    , KFacts.tagEq9 facts
    , KFacts.tagEq10 facts
    , KFacts.tagEq11 facts
    , KFacts.numK0 facts
    , KFacts.numK1 facts
    , KFacts.numK2 facts
    , KFacts.numK3 facts
    , KFacts.numK4 facts
    , KFacts.numK5 facts
    , KFacts.numK6 facts
    , KFacts.numK7 facts
    , KFacts.numK8 facts
    , KFacts.numK9 facts
    , KFacts.numK10 facts
    , KFacts.numK11 facts

