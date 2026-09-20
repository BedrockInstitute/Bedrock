{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenValSeam
import K10.CohenBooleanRename
import K10.CohenBooleanPowerSrc
import K10.CohenBooleanSubset

module K10.CohenBooleanPowerUnfold
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

open import FOL.Syntax using ( var ; ∀̇_ ; _∈̇_ ; _⇒̇_ ; _∧̇_ )
open import FOL.Manipulation.Renaming using ( renameFo )

open TruthAlgebra (hPropAlgebra ℓ)

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; ⊤ᴮ ; ⊓-lb₂ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( _⇒ᴮ_ ; ≤ᴮ-antisym ; ⊤-greatest ; ⇒ᴮ-curry ; ⊓-⊤ )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths
module RN = K10.CohenBooleanRename 𝒮 families accessible images pow κ w lem paths
module PS = K10.CohenBooleanPowerSrc 𝒮
module Sub = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem

open VS using ( Src ; Nameᴮ ; Envᴮ ; val )
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem )

emptyEnv : Envᴮ 0
emptyEnv = []

omegaNm : Nameᴮ
omegaNm = Sub.omegaNm

at2 : Nameᴮ → Envᴮ 2
at2 pω = pω ∷ omegaNm ∷ emptyEnv

inner : Src 3
inner = (var zero ∈̇ var (suc zero)) PS.↔̇ (renameFo PS.CB.pow-emb PS.subsetSrc)

inner-shape : PS.powerSrc ≡ ∀̇ inner
inner-shape = refl

pow-emb-env : (pω τ : Nameᴮ)
  → RN.renameEnv PS.CB.pow-emb (τ ∷ at2 pω) ≡ (τ ∷ omegaNm ∷ emptyEnv)
pow-emb-env pω τ = refl

subset-at : (pω τ : Nameᴮ)
  → val (renameFo PS.CB.pow-emb PS.subsetSrc) (τ ∷ at2 pω)
    ≡ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv)
subset-at pω τ =
  RN.val-rename PS.CB.pow-emb PS.subsetSrc (τ ∷ at2 pω)
  ∙ cong (val PS.subsetSrc) (pow-emb-env pω τ)

mem-at : (pω τ : Nameᴮ)
  → val (var zero ∈̇ var (suc zero)) (τ ∷ at2 pω)
    ≡ mem (fst τ) (fst pω)
mem-at pω τ = VS.law-∈ zero (suc zero) (τ ∷ at2 pω)

inner-val : (pω τ : Nameᴮ)
  → val inner (τ ∷ at2 pω)
    ≡ ((mem (fst τ) (fst pω)
         ⇒ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv))
       ⊓ᴮ (val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv)
         ⇒ᴮ mem (fst τ) (fst pω)))
inner-val pω τ =
  VS.law-∧ (var zero ∈̇ var (suc zero) ⇒̇ renameFo PS.CB.pow-emb PS.subsetSrc)
    (renameFo PS.CB.pow-emb PS.subsetSrc ⇒̇ var zero ∈̇ var (suc zero))
    (τ ∷ at2 pω)
  ∙ cong₂ _⊓ᴮ_
      (VS.law-⇒ (var zero ∈̇ var (suc zero))
        (renameFo PS.CB.pow-emb PS.subsetSrc) (τ ∷ at2 pω)
        ∙ cong₂ _⇒ᴮ_ (mem-at pω τ) (subset-at pω τ))
      (VS.law-⇒ (renameFo PS.CB.pow-emb PS.subsetSrc)
        (var zero ∈̇ var (suc zero)) (τ ∷ at2 pω)
        ∙ cong₂ _⇒ᴮ_ (subset-at pω τ) (mem-at pω τ))

⇒ᴮ-from-≤ : (a b : Pt BAT.B) → ⟨ a ≤ᴮ b ⟩ → (a ⇒ᴮ b) ≡ ⊤ᴮ
⇒ᴮ-from-≤ a b h = ≤ᴮ-antisym (⊤-greatest (a ⇒ᴮ b))
  (⇒ᴮ-curry ⊤ᴮ a b (⊆ˢ-trans (⊓-lb₂ ⊤ᴮ a) h))

inner-top-from : (pω τ : Nameᴮ)
  → ⟨ mem (fst τ) (fst pω)
      ≤ᴮ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv) ⟩
  → ⟨ val PS.subsetSrc (τ ∷ omegaNm ∷ emptyEnv)
      ≤ᴮ mem (fst τ) (fst pω) ⟩
  → val inner (τ ∷ at2 pω) ≡ ⊤ᴮ
inner-top-from pω τ le ge =
  inner-val pω τ
  ∙ cong₂ _⊓ᴮ_ (⇒ᴮ-from-≤ _ _ le) (⇒ᴮ-from-≤ _ _ ge)
  ∙ ⊓-⊤ ⊤ᴮ

module FromAll
  (pω : Nameᴮ)
  (inner-top : (τ : Nameᴮ) → val inner (τ ∷ at2 pω) ≡ ⊤ᴮ)
  where

  opaque
    power-top : val PS.powerSrc (at2 pω) ≡ ⊤ᴮ
    power-top = ≤ᴮ-antisym
      (⊤-greatest (val PS.powerSrc (at2 pω)))
      (subst (λ φ → ⟨ ⊤ᴮ ≤ᴮ val φ (at2 pω) ⟩) (sym inner-shape)
        (VS.law-∀-glb inner (at2 pω) ⊤ᴮ λ τ →
          subst (λ z → ⟨ ⊤ᴮ ≤ᴮ z ⟩) (sym (inner-top τ))
            (⊤-greatest ⊤ᴮ)))
