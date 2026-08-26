{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.667] W3.  Can the witness slot be written as a 3-slot Delta-0
-- parameter-free formula at all, by instantiating [LJ-1.520]'s Matrix
-- and bounding the twelve tag slots by the witness?  This file is
-- .agda.txt until it is green.  It lands nothing in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-667.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula; var; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∃∈ )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import FOL.ZFStructure using ( module hPropStructure )
open import LJ-1-520.Probe520 {ℓ} lem using ( module Matrix )
import L.BoundedSubset as Bnd

open hPropStructure 𝒮ʟ
module B = Bnd {ℓ} lem

-- Innermost environment, fifteen slots:
--   n0..n11, a, p, z
-- after twelve bounded existentials over z:
--   a, p, z
-- which is Witnessed's (value ∷ parameter ∷ witness).

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

module Mx = Matrix {15} ww bb kk n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11

lastFin : {n : ℕ} → Fin (suc n)
lastFin {zero} = zero
lastFin {suc n} = suc (lastFin {n})

-- Result arity is `suc n`, so the bound term's last slot is `lastFin {n}`.
wrap : {n : ℕ} → Formula S (suc (suc n)) → Formula S (suc n)
wrap {n} φ = ∃̇∈ (var (lastFin {n})) φ

δ-wrap : {n : ℕ} {φ : Formula S (suc (suc n))} → Δ₀ φ → Δ₀ (wrap {n} φ)
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
three : Formula S 3
three = wrap {2} s4

Δ₀-three : Δ₀ three
Δ₀-three =
  δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap
    (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap Mx.Δ₀-matrix)))))))))))

count-three : countFo three ≡ 0
count-three = refl

-- Erase onto the parameter-free alphabet Witnessed uses
-- (Probe652.agda:87-91).  count-three says erase never sees a constant.
erased : Formula (⊥* {ℓ-suc ℓ}) 3
erased = B.Cnt.erase three count-three

Δ₀-erased : Δ₀ erased
Δ₀-erased = B.erase-Δ₀ three count-three Δ₀-three

-- SYNTAX HALF OF Witnessed.  The missing conjunct is soundness:
-- (a p z : Sᵥ) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ erased ⟩ → a ≡ Lset p
syntax₃ : Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 3 ] Δ₀ φ
syntax₃ = erased , Δ₀-erased
