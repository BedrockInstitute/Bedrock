{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K9.BooleanAtomic
import K10.CohenDomain
import K10.CohenBooleanInjCheck

module K10.CohenBooleanInjMaps
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula ; Term ; var ; con ; _∈̇_ ; _∧̇_ ; ∃̇_ ; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( prAtˢ ; instFo ; Fits ; ⊨-inst )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B )
module CD = K10.CohenDomain 𝒮 families accessible images pow κ w lem paths
open CD.G.AtomicGraph CD.atomicGraph using ( memAtˢ ; memAtˢ-reading )
module Chk = K10.CohenBooleanInjCheck 𝒮 families accessible images pow κ w lem

pairDom : S → S
pairDom ω₁ = Chk.product ω₁ w

-- Named layers of hitCoreB. Environments:
--   hitCoreB : (y ∷ ξ ∷ p ∷ σ ∷ B ∷ [])
--   hitInner : (n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ B ∷ [])
--   hitAtom  : (b ∷ τ ∷ pair ∷ n ∷ r ∷ y ∷ ξ ∷ p ∷ σ ∷ B ∷ [])
--     0b 1τ 2pair 3n 4r 5y 6ξ 7p 8σ 9B

checkPair : Fin 2 → Term S 10
checkPair zero = var (suc zero)
checkPair (suc zero) = var (suc (suc zero))

hitAtom : S → Formula S 10
hitAtom ω₁ =
  prAtˢ (suc (suc zero))
        (suc (suc (suc (suc (suc (suc zero))))))
        (suc (suc (suc zero)))
  ∧̇ instFo checkPair (Chk.checks (pairDom ω₁))
  ∧̇ memAtˢ zero (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  ∧̇ (var (suc (suc (suc (suc zero)))) ∈̇ var zero)

hitMem : S → Formula S 7
hitMem ω₁ = ∃̇ (∃̇ (∃̇ (hitAtom ω₁)))

hitInner : S → Formula S 7
hitInner ω₁ =
  ∃̇∈ (con Chk.order)
    (prAtˢ zero (suc (suc zero)) (suc (suc (suc (suc (suc zero))))))
  ∧̇ hitMem ω₁

hitCoreB : S → Formula S 5
hitCoreB ω₁ =
  ∃̇∈ (con Chk.carrier)
    (∃̇∈ (con w)
      ( prAtˢ (suc (suc zero)) (suc zero) zero
      ∧̇ hitInner ω₁ ))

hitSlots : S → S → Fin 5 → Term S 2
hitSlots p σ zero = var zero
hitSlots p σ (suc zero) = var (suc zero)
hitSlots p σ (suc (suc zero)) = con p
hitSlots p σ (suc (suc (suc zero))) = con σ
hitSlots p σ (suc (suc (suc (suc zero)))) = con BAT.B

hitFo : S → S → S → Formula S 2
hitFo σ p ω₁ = instFo (hitSlots p σ) (hitCoreB ω₁)

hit-fits : (p σ y ξ : S)
  → Fits (hitSlots p σ) (y ∷ ξ ∷ []) (y ∷ ξ ∷ p ∷ σ ∷ BAT.B ∷ [])
hit-fits p σ y ξ zero = refl
hit-fits p σ y ξ (suc zero) = refl
hit-fits p σ y ξ (suc (suc zero)) = refl
hit-fits p σ y ξ (suc (suc (suc zero))) = refl
hit-fits p σ y ξ (suc (suc (suc (suc zero)))) = refl

hit-reading : (σ p ω₁ y ξ : S)
  → ((y ∷ ξ ∷ []) ⊨ hitFo σ p ω₁)
    ≡ ((y ∷ ξ ∷ p ∷ σ ∷ BAT.B ∷ []) ⊨ hitCoreB ω₁)
hit-reading σ p ω₁ y ξ =
  ⊨-inst (hitSlots p σ) (hitCoreB ω₁) (y ∷ ξ ∷ [])
    (y ∷ ξ ∷ p ∷ σ ∷ BAT.B ∷ [])
    (hit-fits p σ y ξ)

mem-at : (b τ σ : S)
  → ((b ∷ τ ∷ σ ∷ BAT.B ∷ [])
      ⊨ memAtˢ zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))))
    ≡ CD.G.AtomicGraph.memΔ CD.atomicGraph BAT.B b τ σ
mem-at b τ σ =
  memAtˢ-reading zero (suc zero) (suc (suc zero)) (suc (suc (suc zero)))
    (b ∷ τ ∷ σ ∷ BAT.B ∷ [])

-- Fiber of a frozen value n: those ξ ∈ ω₁ for which some y = ⟨r,n⟩
-- satisfies hitFo.

fiberAt : S → S → S → Formula S 2
fiberAt σ p ω₁ =
  ∃̇ ( instFo (λ { zero → var zero ; (suc zero) → var (suc zero) })
        (hitFo σ p ω₁)
    ∧̇ ∃̇∈ (con Chk.carrier)
         (prAtˢ (suc zero) zero (suc (suc (suc zero)))))

fiberFo : S → S → S → S → Formula S 1
fiberFo σ p ω₁ n =
  instFo (λ { zero → var zero ; (suc zero) → con n }) (fiberAt σ p ω₁)

fiber : S → S → S → S → S
fiber σ p ω₁ n = Chk.separator ω₁ (fiberFo σ p ω₁ n)

fiber-in : (σ p ω₁ n ξ : S) → ⟨ ξ ∈ˢ ω₁ ⟩
  → ⟨ (ξ ∷ []) ⊨ fiberFo σ p ω₁ n ⟩
  → ⟨ ξ ∈ˢ fiber σ p ω₁ n ⟩
fiber-in σ p ω₁ n ξ hξ h =
  subst ⟨_⟩ (sym (Chk.separator-spec ω₁ (fiberFo σ p ω₁ n) ξ)) (hξ , h)

fiber-out : (σ p ω₁ n ξ : S)
  → ⟨ ξ ∈ˢ fiber σ p ω₁ n ⟩
  → ⟨ ξ ∈ˢ ω₁ ⟩ × ⟨ (ξ ∷ []) ⊨ fiberFo σ p ω₁ n ⟩
fiber-out σ p ω₁ n ξ h =
  subst ⟨_⟩ (Chk.separator-spec ω₁ (fiberFo σ p ω₁ n) ξ) h
