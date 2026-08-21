{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.495] Six KFactsCons, then the 26 shared TFacts fields.
-- W3 first was `twice` (two conses). Six conses is the same move
-- four steps further. Shared TFacts fields carry six sucs
-- (TwelveAgree.lagda.md:133-161). KValue's KFacts is Fin 14 over
-- S ^ 14 (Condensation.lagda.md:7389-7395). After six conses the
-- environment is S ^ 20, which is TFacts at n = 9.
--
-- Predecessor [LJ-1.491] is GO. Telescope is KValue plus
-- ⟨ ω ∈ gam ⟩ (Probe491.agda:54-59). Do not import a probe.
-- Do not build a TFacts value. Do not fill someEnv.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide
-- caliber, set on the pane by the program and untouched here.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-495.Probe495 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ} using ( prʟ )
open import L.Condensation {ℓ} lem
  using ( module KValue; module KFactsNS; KFactsCons )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( sucV; ω )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts

-- =====================================================================
-- W2.  The 26 shared fields, once, at TFacts's own indices.
--   Instantiated below at n = 9 against KValue's Fin 14.
-- =====================================================================

record Shared26 {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 K : Fin (5 + n))
  (γ' : Vec S (11 + n)) : Type (ℓ-suc ℓ) where
  field
    tagEq0 : fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ') ≡ fst (numeralL 0)
    tagEq1 : fst (lookup (suc (suc (suc (suc (suc (suc N1)))))) γ') ≡ fst (numeralL 1)
    tagEq2 : fst (lookup (suc (suc (suc (suc (suc (suc N2)))))) γ') ≡ fst (numeralL 2)
    tagEq3 : fst (lookup (suc (suc (suc (suc (suc (suc N3)))))) γ') ≡ fst (numeralL 3)
    tagEq4 : fst (lookup (suc (suc (suc (suc (suc (suc N4)))))) γ') ≡ fst (numeralL 4)
    tagEq5 : fst (lookup (suc (suc (suc (suc (suc (suc N5)))))) γ') ≡ fst (numeralL 5)
    tagEq6 : fst (lookup (suc (suc (suc (suc (suc (suc N6)))))) γ') ≡ fst (numeralL 6)
    tagEq7 : fst (lookup (suc (suc (suc (suc (suc (suc N7)))))) γ') ≡ fst (numeralL 7)
    tagEq8 : fst (lookup (suc (suc (suc (suc (suc (suc N8)))))) γ') ≡ fst (numeralL 8)
    tagEq9 : fst (lookup (suc (suc (suc (suc (suc (suc N9)))))) γ') ≡ fst (numeralL 9)
    tagEq10 : fst (lookup (suc (suc (suc (suc (suc (suc N10)))))) γ') ≡ fst (numeralL 10)
    tagEq11 : fst (lookup (suc (suc (suc (suc (suc (suc N11)))))) γ') ≡ fst (numeralL 11)
    numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    innerK : (k : ℕ) (p : S) → ⟨ fst p ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              → ⟨ fst (prʟ (numeralL k) p) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
    pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
              → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

-- =====================================================================
-- W3.  Two applications of KFactsCons.  Then six, then the 26.
-- =====================================================================

module Frame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈γ : ⟨ ω ∈ gam ⟩) where

  open KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ

  twice : (c1 c2 : S)
        → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
        → KFacts (suc (suc iA)) (suc (suc iK))
            (suc (suc i0)) (suc (suc i1)) (suc (suc i2)) (suc (suc i3))
            (suc (suc i4)) (suc (suc i5)) (suc (suc i6)) (suc (suc i7))
            (suc (suc i8)) (suc (suc i9)) (suc (suc i10)) (suc (suc i11))
            (c2 ∷ c1 ∷ Kenv)
  twice c1 c2 f =
    KFactsCons (suc iA) (suc iK)
      (suc i0) (suc i1) (suc i2) (suc i3)
      (suc i4) (suc i5) (suc i6) (suc i7)
      (suc i8) (suc i9) (suc i10) (suc i11)
      (c1 ∷ Kenv) c2
      (KFactsCons iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
         Kenv c1 f)

  six : (c1 c2 c3 c4 c5 c6 : S)
      → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
      → KFacts
          (suc (suc (suc (suc (suc (suc iA))))))
          (suc (suc (suc (suc (suc (suc iK))))))
          (suc (suc (suc (suc (suc (suc i0))))))
          (suc (suc (suc (suc (suc (suc i1))))))
          (suc (suc (suc (suc (suc (suc i2))))))
          (suc (suc (suc (suc (suc (suc i3))))))
          (suc (suc (suc (suc (suc (suc i4))))))
          (suc (suc (suc (suc (suc (suc i5))))))
          (suc (suc (suc (suc (suc (suc i6))))))
          (suc (suc (suc (suc (suc (suc i7))))))
          (suc (suc (suc (suc (suc (suc i8))))))
          (suc (suc (suc (suc (suc (suc i9))))))
          (suc (suc (suc (suc (suc (suc i10))))))
          (suc (suc (suc (suc (suc (suc i11))))))
          (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
  six c1 c2 c3 c4 c5 c6 f =
    KFactsCons
      (suc (suc (suc (suc (suc iA))))) (suc (suc (suc (suc (suc iK)))))
      (suc (suc (suc (suc (suc i0))))) (suc (suc (suc (suc (suc i1)))))
      (suc (suc (suc (suc (suc i2))))) (suc (suc (suc (suc (suc i3)))))
      (suc (suc (suc (suc (suc i4))))) (suc (suc (suc (suc (suc i5)))))
      (suc (suc (suc (suc (suc i6))))) (suc (suc (suc (suc (suc i7)))))
      (suc (suc (suc (suc (suc i8))))) (suc (suc (suc (suc (suc i9)))))
      (suc (suc (suc (suc (suc i10))))) (suc (suc (suc (suc (suc i11)))))
      (c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) c6
      (KFactsCons
        (suc (suc (suc (suc iA)))) (suc (suc (suc (suc iK))))
        (suc (suc (suc (suc i0)))) (suc (suc (suc (suc i1))))
        (suc (suc (suc (suc i2)))) (suc (suc (suc (suc i3))))
        (suc (suc (suc (suc i4)))) (suc (suc (suc (suc i5))))
        (suc (suc (suc (suc i6)))) (suc (suc (suc (suc i7))))
        (suc (suc (suc (suc i8)))) (suc (suc (suc (suc i9))))
        (suc (suc (suc (suc i10)))) (suc (suc (suc (suc i11))))
        (c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv) c5
        (KFactsCons
          (suc (suc (suc iA))) (suc (suc (suc iK)))
          (suc (suc (suc i0))) (suc (suc (suc i1)))
          (suc (suc (suc i2))) (suc (suc (suc i3)))
          (suc (suc (suc i4))) (suc (suc (suc i5)))
          (suc (suc (suc i6))) (suc (suc (suc i7)))
          (suc (suc (suc i8))) (suc (suc (suc i9)))
          (suc (suc (suc i10))) (suc (suc (suc i11)))
          (c3 ∷ c2 ∷ c1 ∷ Kenv) c4
          (KFactsCons
            (suc (suc iA)) (suc (suc iK))
            (suc (suc i0)) (suc (suc i1))
            (suc (suc i2)) (suc (suc i3))
            (suc (suc i4)) (suc (suc i5))
            (suc (suc i6)) (suc (suc i7))
            (suc (suc i8)) (suc (suc i9))
            (suc (suc i10)) (suc (suc i11))
            (c2 ∷ c1 ∷ Kenv) c3
            (twice c1 c2 f))))

  tfacts-shared-from-kfacts :
      (c1 c2 c3 c4 c5 c6 : S)
    → KFacts iA iK i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 Kenv
    → Shared26 {n = 9} i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 iK
         (c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv)
  tfacts-shared-from-kfacts c1 c2 c3 c4 c5 c6 f =
    let f6 = six c1 c2 c3 c4 c5 c6 f
    in record
      { tagEq0 = f6 .tagEq0
      ; tagEq1 = f6 .tagEq1
      ; tagEq2 = f6 .tagEq2
      ; tagEq3 = f6 .tagEq3
      ; tagEq4 = f6 .tagEq4
      ; tagEq5 = f6 .tagEq5
      ; tagEq6 = f6 .tagEq6
      ; tagEq7 = f6 .tagEq7
      ; tagEq8 = f6 .tagEq8
      ; tagEq9 = f6 .tagEq9
      ; tagEq10 = f6 .tagEq10
      ; tagEq11 = f6 .tagEq11
      ; numK0 = f6 .numK0
      ; numK1 = f6 .numK1
      ; numK2 = f6 .numK2
      ; numK3 = f6 .numK3
      ; numK4 = f6 .numK4
      ; numK5 = f6 .numK5
      ; numK6 = f6 .numK6
      ; numK7 = f6 .numK7
      ; numK8 = f6 .numK8
      ; numK9 = f6 .numK9
      ; numK10 = f6 .numK10
      ; numK11 = f6 .numK11
      ; innerK = f6 .innerK
      ; pairK = f6 .pairK }

twice = Frame.twice
tfacts-shared-from-kfacts = Frame.tfacts-shared-from-kfacts
