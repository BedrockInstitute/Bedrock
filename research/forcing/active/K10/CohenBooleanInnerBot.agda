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
import K10.CohenBooleanNotCH
import K10.CohenBooleanRename

module K10.CohenBooleanInnerBot
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.Syntax using ( _∧̇_ ; _∨̇_ ; _⇒̇_ ; ∃̇_ )
open import FOL.Manipulation.ConstantOccurrences using ( module ZeroOccurrences )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge

module CH = K10.CohenBooleanNotCH 𝒮 families accessible images pow find
  κ w lem hw paths
module RN = K10.CohenBooleanRename 𝒮 families accessible images pow κ w lem paths
module CB = CardinalBridge 𝒮
module ZO = ZeroOccurrences (ZFStructure.S 𝒮)

open CH using ( ⊤B ; ⊥B )
open CH.VS using ( Src ; Nameᴮ ; Envᴮ ; val )
open K4.Algebra 𝒮 using ( ≤ᴮ-refl ; _≤ᴮ_ )
open K4.Implication 𝒮 CH.NG.extensional CH.NG.≈ˢ-paths CH.BAT.B
  CH.BAT.IC.codedLattice CH.BAT.IC.codedComplement
  using ( ≤⊥→≡⊥ )

injSrc : Src 2
injSrc = ZO.erase CB.Injectableφ refl

injBody : Src 3
injBody = ZO.erase CB.IsInjectionφ refl

inj-shape : injSrc ≡ ∃̇ injBody
inj-shape = refl

inj-bot-from : (a b : Nameᴮ)
  → ((σ : Nameᴮ) → val injBody (σ ∷ a ∷ b ∷ CH.emptyEnv) ≡ ⊥B)
  → val injSrc (a ∷ b ∷ CH.emptyEnv) ≡ ⊥B
inj-bot-from a b hyp =
  ≤⊥→≡⊥ (val injSrc (a ∷ b ∷ CH.emptyEnv))
    (subst (λ φ → ⟨ val φ (a ∷ b ∷ CH.emptyEnv) ≤ᴮ ⊥B ⟩) (sym inj-shape)
      (CH.VS.law-∃-lub injBody (a ∷ b ∷ CH.emptyEnv) ⊥B λ σ →
        subst (λ z → ⟨ z ≤ᴮ ⊥B ⟩) (sym (hyp σ))
          (≤ᴮ-refl ⊥B)))

wx-env : (x pω : Nameᴮ)
  → RN.renameEnv CH.CH.inj-wx (x ∷ CH.at2 pω) ≡ (CH.omegaNm ∷ x ∷ CH.emptyEnv)
wx-env x pω = refl

xw-env : (x pω : Nameᴮ)
  → RN.renameEnv CH.CH.inj-xw (x ∷ CH.at2 pω) ≡ (x ∷ CH.omegaNm ∷ CH.emptyEnv)
xw-env x pω = refl

xp-env : (x pω : Nameᴮ)
  → RN.renameEnv CH.CH.inj-xp (x ∷ CH.at2 pω) ≡ (x ∷ pω ∷ CH.emptyEnv)
xp-env x pω = refl

px-env : (x pω : Nameᴮ)
  → RN.renameEnv CH.CH.inj-px (x ∷ CH.at2 pω) ≡ (pω ∷ x ∷ CH.emptyEnv)
px-env x pω = refl

wx-val : (x pω : Nameᴮ)
  → val (renameFo CH.CH.inj-wx injSrc) (x ∷ CH.at2 pω)
    ≡ val injSrc (CH.omegaNm ∷ x ∷ CH.emptyEnv)
wx-val x pω =
  RN.val-rename CH.CH.inj-wx injSrc (x ∷ CH.at2 pω)
  ∙ cong (val injSrc) (wx-env x pω)

xw-val : (x pω : Nameᴮ)
  → val (renameFo CH.CH.inj-xw injSrc) (x ∷ CH.at2 pω)
    ≡ val injSrc (x ∷ CH.omegaNm ∷ CH.emptyEnv)
xw-val x pω =
  RN.val-rename CH.CH.inj-xw injSrc (x ∷ CH.at2 pω)
  ∙ cong (val injSrc) (xw-env x pω)

xp-val : (x pω : Nameᴮ)
  → val (renameFo CH.CH.inj-xp injSrc) (x ∷ CH.at2 pω)
    ≡ val injSrc (x ∷ pω ∷ CH.emptyEnv)
xp-val x pω =
  RN.val-rename CH.CH.inj-xp injSrc (x ∷ CH.at2 pω)
  ∙ cong (val injSrc) (xp-env x pω)

px-val : (x pω : Nameᴮ)
  → val (renameFo CH.CH.inj-px injSrc) (x ∷ CH.at2 pω)
    ≡ val injSrc (pω ∷ x ∷ CH.emptyEnv)
px-val x pω =
  RN.val-rename CH.CH.inj-px injSrc (x ∷ CH.at2 pω)
  ∙ cong (val injSrc) (px-env x pω)

ante-src : Src 3
ante-src = renameFo CH.CH.inj-wx injSrc ∧̇ renameFo CH.CH.inj-xp injSrc

cons-src : Src 3
cons-src = renameFo CH.CH.inj-xw injSrc ∨̇ renameFo CH.CH.inj-px injSrc

between-erase : CH.CH-between ≡ (ante-src ⇒̇ cons-src)
between-erase = refl

module FromInjectables
  (pω x : Nameᴮ)
  (wx-top : val injSrc (CH.omegaNm ∷ x ∷ CH.emptyEnv) ≡ ⊤B)
  (xp-top : val injSrc (x ∷ pω ∷ CH.emptyEnv) ≡ ⊤B)
  (xw-bot : val injSrc (x ∷ CH.omegaNm ∷ CH.emptyEnv) ≡ ⊥B)
  (px-bot : val injSrc (pω ∷ x ∷ CH.emptyEnv) ≡ ⊥B)
  where

  open K4.Algebra.Lattice CH.BAT.IC.codedLattice using ( _⊓ᴮ_ ; _⊔ᴮ_ )
  open K4.Implication 𝒮 CH.NG.extensional CH.NG.≈ˢ-paths CH.BAT.B
    CH.BAT.IC.codedLattice CH.BAT.IC.codedComplement
    using ( ⊓-⊤ ; ⊔-⊥ˡ ; ⇒ᴮ-⊤ˡ ; _⇒ᴮ_ )

  ante-top : val ante-src (x ∷ CH.at2 pω) ≡ ⊤B
  ante-top =
    CH.VS.law-∧ (renameFo CH.CH.inj-wx injSrc)
      (renameFo CH.CH.inj-xp injSrc) (x ∷ CH.at2 pω)
    ∙ cong₂ _⊓ᴮ_ (wx-val x pω ∙ wx-top) (xp-val x pω ∙ xp-top)
    ∙ ⊓-⊤ ⊤B

  cons-bot : val cons-src (x ∷ CH.at2 pω) ≡ ⊥B
  cons-bot =
    CH.VS.law-∨ (renameFo CH.CH.inj-xw injSrc)
      (renameFo CH.CH.inj-px injSrc) (x ∷ CH.at2 pω)
    ∙ cong₂ _⊔ᴮ_ (xw-val x pω ∙ xw-bot) (px-val x pω ∙ px-bot)
    ∙ ⊔-⊥ˡ ⊥B

  between-bot : val CH.CH-between (x ∷ CH.at2 pω) ≡ ⊥B
  between-bot =
    cong (λ φ → val φ (x ∷ CH.at2 pω)) between-erase
    ∙ CH.VS.law-⇒ ante-src cons-src (x ∷ CH.at2 pω)
    ∙ cong₂ _⇒ᴮ_ ante-top cons-bot
    ∙ ⇒ᴮ-⊤ˡ ⊥B

  opaque
    inner-bot : val CH.CH-cons (CH.at2 pω) ≡ ⊥B
    inner-bot = CH.cons-bot-from pω x between-bot
