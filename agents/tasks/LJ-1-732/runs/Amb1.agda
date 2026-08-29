{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-732.runs.Amb1 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
open import L.Condensation {ℓ} lem using ( domB )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Vec using ( lookup; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-667.Probe667 {ℓ} lem as P667
import LJ-1-520.Probe520 {ℓ} lem as P520
open import LJ-1-732.runs.Num {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
module CS = hPropStructure 𝒮ʟ
module CntS = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

ww bb kk : Fin 15
ww = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))
bb = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero)))))))))))))
kk = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))))))
n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : Fin 15
n0 = zero
n1 = suc (zero)
n2 = suc (suc (zero))
n3 = suc (suc (suc (zero)))
n4 = suc (suc (suc (suc (zero))))
n5 = suc (suc (suc (suc (suc (zero)))))
n6 = suc (suc (suc (suc (suc (suc (zero))))))
n7 = suc (suc (suc (suc (suc (suc (suc (zero)))))))
n8 = suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))
n9 = suc (suc (suc (suc (suc (suc (suc (suc (suc (zero)))))))))
n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero))))))))))
n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (zero)))))))))))
module Mx = P520.Matrix {15} ww bb kk n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11

countMx : countFo Mx.matrix ≡ 0
countMx = refl
countGB : countFo Mx.G.graphBndAt ≡ 0
countGB = refl
countA : countFo Mx.G.A.approxBndAt ≡ 0
countA = refl
countAS : countFo Mx.G.A.S.stepBndAt ≡ 0
countAS = refl
countS : countFo Mx.G.S.stepBndAt ≡ 0
countS = refl
countTrans : countFo Mx.transK ≡ 0
countTrans = refl
countPins : countFo Mx.pins ≡ 0
countPins = refl
countDomB : countFo (domB zero (suc bb) (suc kk)) ≡ 0
countDomB = refl

erased-matrix : Formula (⊥* {ℓ-suc ℓ}) 15
erased-matrix = CntS.erase Mx.matrix countMx

γ15 : S ^ 15
γ15 = n 0 ∷ n 1 ∷ n 2 ∷ n 3 ∷ n 4 ∷ n 5 ∷ n 6 ∷ n 7 ∷ n 8 ∷ n 9
    ∷ n 10 ∷ n 11 ∷ Lset ∅ ∷ ∅ ∷ n 12 ∷ []
