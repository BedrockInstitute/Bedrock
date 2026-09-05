# The witness slot as syntax

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

-- The bounded matrix of the level formula, at the 𝒮ʟ carrier: the
-- twelve tag slots bounded by the witness, then erased onto ⊥*.  Read
-- by `L.GCH.Level`, `L.GCH.Sound` and `L.GCH.Complete`; it stands on
-- `L.Condensation`'s `GraphB` and leaves with it.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Frame {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-∀∈; δ-∃∈; δ-∈; δ-⊥ )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Coding.Model {ℓ} using ( sucAtL )
open import L.Condensation {ℓ} lem using
  ( module GraphB; DefBodyB; Δ₀-DefBodyB; Δ₀-sucAtL )
open import L.GCH.Hull {ℓ} lem using ( module Cnt; erase-Δ₀ )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( _,_ )

-- The 𝒮ʟ carrier, for the syntax of the witness slot.
module CS = hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- THE WITNESS SLOT, AS SYNTAX.  [LJ-1.520] Probe520.agda:53-128
-- (`Matrix`), then [LJ-1.667] runs/W3.agda:25-97 (`W3`): the bounded
-- matrix with the twelve tag slots bounded by the witness, erased
-- onto ⊥*.  Written at the 𝒮ʟ carrier `CS.S`.
-- =====================================================================

module Matrix {m : ℕ} (w b K : Fin m)
              (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where
  private
    sh5 : Fin m → Fin (5 + m)
    sh5 i = suc (suc (suc (suc (suc i))))

    sh7 : Fin m → Fin (7 + m)
    sh7 i = suc (suc (suc (suc (suc (suc (suc i))))))

  ψs : Formula CS.S (suc (suc (suc (5 + m))))
  ψs = DefBodyB {m} (suc zero) (sh5 K)
         (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
         (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
         (sh5 N0) (sh5 N1)

  ψa : Formula CS.S (suc (suc (suc (7 + m))))
  ψa = DefBodyB {2 + m} (suc zero) (sh7 K)
         (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
         (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
         (sh7 N0) (sh7 N1)

  module G = GraphB {m} ψs ψa w b K using (graphBndAt; Δ₀-graphBndAt; module A; module S)

  Δ₀-ψs : Δ₀ ψs
  Δ₀-ψs = Δ₀-DefBodyB {m} (suc zero) (sh5 K)
            (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
            (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
            (sh5 N0) (sh5 N1)

  Δ₀-ψa : Δ₀ ψa
  Δ₀-ψa = Δ₀-DefBodyB {2 + m} (suc zero) (sh7 K)
            (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
            (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
            (sh7 N0) (sh7 N1)

  -- K IS TRANSITIVE.
  transK : Formula CS.S m
  transK = ∀̇∈ (var K) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc K))))

  Δ₀-transK : Δ₀ transK
  Δ₀-transK = δ-∀∈ (δ-∀∈ δ-∈)

  -- THE TWELVE TAG SLOTS HOLD THE TWELVE NUMERALS, in the object
  -- language: N0 is empty, each next slot is the successor.
  pins : Formula CS.S m
  pins = ∀̇∈ (var N0) ⊥̇
       ∧̇ ( sucAtL N0 N1 ∧̇ ( sucAtL N1 N2 ∧̇ ( sucAtL N2 N3
       ∧̇ ( sucAtL N3 N4 ∧̇ ( sucAtL N4 N5 ∧̇ ( sucAtL N5 N6
       ∧̇ ( sucAtL N6 N7 ∧̇ ( sucAtL N7 N8 ∧̇ ( sucAtL N8 N9
       ∧̇ ( sucAtL N9 N10 ∧̇ sucAtL N10 N11 ))))))))))

  Δ₀-pins : Δ₀ pins
  Δ₀-pins =
    δ-∧ (δ-∀∈ δ-⊥)
      (δ-∧ (Δ₀-sucAtL N0 N1) (δ-∧ (Δ₀-sucAtL N1 N2) (δ-∧ (Δ₀-sucAtL N2 N3)
      (δ-∧ (Δ₀-sucAtL N3 N4) (δ-∧ (Δ₀-sucAtL N4 N5) (δ-∧ (Δ₀-sucAtL N5 N6)
      (δ-∧ (Δ₀-sucAtL N6 N7) (δ-∧ (Δ₀-sucAtL N7 N8) (δ-∧ (Δ₀-sucAtL N8 N9)
      (δ-∧ (Δ₀-sucAtL N9 N10) (Δ₀-sucAtL N10 N11)))))))))))

  -- THE WHOLE MATRIX, AND IT IS Δ₀.
  matrix : Formula CS.S m
  matrix = transK ∧̇ ( pins ∧̇ G.graphBndAt )

  Δ₀-matrix : Δ₀ matrix
  Δ₀-matrix = δ-∧ Δ₀-transK (δ-∧ Δ₀-pins (G.Δ₀-graphBndAt Δ₀-ψs Δ₀-ψa))

module W3 where

  -- Innermost environment, fifteen slots: n0..n11, a, p, z.  After
  -- twelve bounded existentials over z: a, p, z, which is
  -- Witnessed's (value ∷ parameter ∷ witness).
  private
    n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 ww bb kk : Fin 15
    n0  = zero
    n1  = suc zero
    n2  = suc (suc zero)
    n3  = suc (suc (suc zero))
    n4  = suc (suc (suc (suc zero)))
    n5  = suc (suc (suc (suc (suc zero))))
    n6  = suc (suc (suc (suc (suc (suc zero)))))
    n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
    n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    ww  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    bb  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
    kk  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))

  module Mx = Matrix {15} ww bb kk n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 using (matrix; Δ₀-matrix)

  lastFin : {n : ℕ} → Fin (suc n)
  lastFin {zero} = zero
  lastFin {suc n} = suc (lastFin {n})

  -- Result arity is `suc n`, so the bound term's last slot is `lastFin {n}`.
  wrap : {n : ℕ} → Formula CS.S (suc (suc n)) → Formula CS.S (suc n)
  wrap {n} φ = ∃̇∈ (var (lastFin {n})) φ

  δ-wrap : {n : ℕ} {φ : Formula CS.S (suc (suc n))} → Δ₀ φ → Δ₀ (wrap {n} φ)
  δ-wrap d = δ-∃∈ d

  -- Twelve bounded existentials, outermost env a ∷ p ∷ z.
  inner = Mx.matrix
  s14 = wrap {13} inner
  s13 = wrap {12} s14
  s12 = wrap {11} s13
  s11 = wrap {10} s12
  s10 = wrap {9}  s11
  s9  = wrap {8}  s10
  s8  = wrap {7}  s9
  s7  = wrap {6}  s8
  s6  = wrap {5}  s7
  s5  = wrap {4}  s6
  s4  = wrap {3}  s5
  three : Formula CS.S 3
  three = wrap {2} s4

  Δ₀-three : Δ₀ three
  Δ₀-three =
    δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap
      (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap Mx.Δ₀-matrix)))))))))))

  count-three : countFo three ≡ 0
  count-three = refl

  -- Erase onto the parameter-free alphabet Witnessed uses.
  erased : Formula (⊥* {ℓ-suc ℓ}) 3
  erased = Cnt.erase three count-three

  Δ₀-erased : Δ₀ erased
  Δ₀-erased = erase-Δ₀ three count-three Δ₀-three

  syntax₃ : Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 3 ] Δ₀ φ
  syntax₃ = erased , Δ₀-erased
```
