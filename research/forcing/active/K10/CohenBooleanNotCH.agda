{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import CHSentence
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.BooleanReals
import K9.NameGround
import K10.BooleanGraph
import K10.CohenValSeam
import K10.CohenBooleanSubset
import K10.NegatedSentences

module K10.CohenBooleanNotCH
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

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula ; _⇒̇_ ; ⊥̇ ; ¬̇_ ; ∀̇_ ; _∧̇_ ; _∨̇_ )
open import FOL.Manipulation.ConstantOccurrences using ( countFo ; module ZeroOccurrences )
open import FOL.Manipulation.ParameterAbstraction using ( absFo )
open import FOL.Manipulation.Renaming using ( renameFo )
import CardinalBridge
import K9.BooleanNameGround
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; ⊆ˢ-trans ; _≤ᴮ_ )
open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( _⇒ᴮ_ ; ≤ᴮ-antisym ; ⊔-⊥ˡ ; ⇒ᴮ-curry ; ≤⊥→≡⊥
        ; ⊥-least ; ⊤-greatest ; ⊓-lb₂ ; ⊥ᴮ ; ⊤ᴮ ; ¬ᴮ_ ; ¬-⊔
        ; ⇒ᴮ-⊤ˡ ; ⊓-⊤ )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths
module BR = K9.BooleanReals 𝒮 families accessible images pow κ w lem
module BGr = K10.BooleanGraph 𝒮 families accessible images pow κ w lem
module CH = CHSentence 𝒮
module Neg = K10.NegatedSentences 𝒮
module CB = CardinalBridge 𝒮
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
module ZO = ZeroOccurrences S

module Distinct = BR.DenseDistinct find hw
module GraphDistinct = BGr.Distinct find hw
module Pow = K10.CohenBooleanSubset 𝒮 families accessible images pow κ w lem

⇒ᴮ-⊥ˡ : (v : Pt BAT.B) → (⊥ᴮ ⇒ᴮ v) ≡ ⊤ᴮ
⇒ᴮ-⊥ˡ v = ≤ᴮ-antisym (⊤-greatest (⊥ᴮ ⇒ᴮ v))
  (⇒ᴮ-curry ⊤ᴮ ⊥ᴮ v (⊆ˢ-trans (⊓-lb₂ ⊤ᴮ ⊥ᴮ) (⊥-least v)))

¬-⊥ : (¬ᴮ ⊥ᴮ) ≡ ⊤ᴮ
¬-⊥ = sym (⊔-⊥ˡ (¬ᴮ ⊥ᴮ)) ∙ ¬-⊔ ⊥ᴮ

CHcount : countFo CH.CHsent ≡ 0
CHcount = refl

¬CHcount : countFo CH.¬CHsent ≡ 0
¬CHcount = refl

GCHωcount : countFo CH.GCHωsent ≡ 0
GCHωcount = refl

¬GCHωcount : countFo Neg.¬GCHωsent ≡ 0
¬GCHωcount = refl

¬CHsrc : VS.Src 0
¬CHsrc = ZO.erase CH.¬CHsent ¬CHcount

¬GCHωsrc : VS.Src 0
¬GCHωsrc = ZO.erase Neg.¬GCHωsent ¬GCHωcount

CHsrc : VS.Src 0
CHsrc = ZO.erase CH.CHsent CHcount

GCHωsrc : VS.Src 0
GCHωsrc = ZO.erase CH.GCHωsent GCHωcount

emptyEnv : VS.Envᴮ 0
emptyEnv = []

not-CH-reals-top : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
  → (⟨ α ≈ˢ β ⟩ → ⟨ ⊥ ⟩)
  → (¬ᴮ (BAT.Atomic._≈ᴮ_ (BR.realB α) (BR.realB β))) ≡ ⊤ᴮ
not-CH-reals-top = Distinct.distinct-top

indexed-real-check : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
  → BAT.Atomic._≈ᴮ_ (BR.realB α) (BR.realB β)
    ≡ BAT.Atomic._≈ᴮ_ (BGr.BG.translated-check α) (BGr.BG.translated-check β)
indexed-real-check = GraphDistinct.indexed-equality

not-CH-compiled : Pt BAT.B
not-CH-compiled = VS.val ¬CHsrc emptyEnv

not-GCHω-compiled : Pt BAT.B
not-GCHω-compiled = VS.val ¬GCHωsrc emptyEnv

CH-implies-bot : VS.val (CHsrc ⇒̇ ⊥̇) emptyEnv
  ≡ (VS.val CHsrc emptyEnv ⇒ᴮ VS.val {0} ⊥̇ emptyEnv)
CH-implies-bot = VS.law-⇒ CHsrc ⊥̇ emptyEnv

GCHω-implies-bot : VS.val (GCHωsrc ⇒̇ ⊥̇) emptyEnv
  ≡ (VS.val GCHωsrc emptyEnv ⇒ᴮ VS.val {0} ⊥̇ emptyEnv)
GCHω-implies-bot = VS.law-⇒ GCHωsrc ⊥̇ emptyEnv

¬CH-is-impl : ¬CHsrc ≡ (CHsrc ⇒̇ ⊥̇)
¬CH-is-impl = refl

¬GCHω-is-impl : ¬GCHωsrc ≡ (GCHωsrc ⇒̇ ⊥̇)
¬GCHω-is-impl = refl

val-⊥ : VS.val {0} ⊥̇ emptyEnv ≡ ⊥ᴮ
val-⊥ = VS.law-⊥ emptyEnv

not-CH-from-bot : VS.val CHsrc emptyEnv ≡ ⊥ᴮ
  → VS.val ¬CHsrc emptyEnv ≡ ⊤ᴮ
not-CH-from-bot ch-bot =
  cong (λ φ → VS.val φ emptyEnv) ¬CH-is-impl
  ∙ CH-implies-bot
  ∙ cong₂ _⇒ᴮ_ ch-bot val-⊥
  ∙ ⇒ᴮ-⊥ˡ ⊥ᴮ

not-GCHω-from-bot : VS.val GCHωsrc emptyEnv ≡ ⊥ᴮ
  → VS.val ¬GCHωsrc emptyEnv ≡ ⊤ᴮ
not-GCHω-from-bot gch-bot =
  cong (λ φ → VS.val φ emptyEnv) ¬GCHω-is-impl
  ∙ GCHω-implies-bot
  ∙ cong₂ _⇒ᴮ_ gch-bot val-⊥
  ∙ ⇒ᴮ-⊥ˡ ⊥ᴮ

CH-inner1-ground : Formula S 1
CH-inner1-ground =
  ∀̇ (((renameFo CH.om-w CB.IsOmegaφ) ∧̇ CB.IsPowerSetφ)
    ⇒̇ (∀̇ (((renameFo CH.inj-wx CB.Injectableφ)
           ∧̇ (renameFo CH.inj-xp CB.Injectableφ))
         ⇒̇ ((renameFo CH.inj-xw CB.Injectableφ)
          ∨̇ (renameFo CH.inj-px CB.Injectableφ)))))

CH-inner1 : VS.Src 1
CH-inner1 = ZO.erase CH-inner1-ground refl

CHsrc-∀ : CHsrc ≡ ∀̇ CH-inner1
CHsrc-∀ = refl

checkNmᴮ : S → VS.Nameᴮ
checkNmᴮ a = BNG.Checked.check a , BNG.Checked.check-name a

CH-bot-from-instance : (φ : VS.Src 1) (σ : VS.Nameᴮ)
  → VS.val (∀̇ φ) emptyEnv ≡ VS.val CHsrc emptyEnv
  → VS.val φ (σ ∷ emptyEnv) ≡ ⊥ᴮ
  → VS.val CHsrc emptyEnv ≡ ⊥ᴮ
CH-bot-from-instance φ σ outer inst-bot =
  ≤⊥→≡⊥ (VS.val CHsrc emptyEnv)
    (subst (λ z → ⟨ VS.val CHsrc emptyEnv ≤ᴮ z ⟩) inst-bot
      (subst (λ u → ⟨ u ≤ᴮ VS.val φ (σ ∷ emptyEnv) ⟩) outer
        (VS.law-∀-lb φ emptyEnv σ)))

CH-bot-at-omega : VS.val CH-inner1 (checkNmᴮ w ∷ emptyEnv) ≡ ⊥ᴮ
  → VS.val CHsrc emptyEnv ≡ ⊥ᴮ
CH-bot-at-omega =
  CH-bot-from-instance CH-inner1 (checkNmᴮ w)
    (cong (λ φ → VS.val φ emptyEnv) (sym CHsrc-∀))

omegaNm : VS.Nameᴮ
omegaNm = Pow.omegaNm

powerNm : VS.Nameᴮ
powerNm = Pow.powerNm

CH-matrix-ground : Formula S 2
CH-matrix-ground =
  ((renameFo CH.om-w CB.IsOmegaφ) ∧̇ CB.IsPowerSetφ)
  ⇒̇ (∀̇ (((renameFo CH.inj-wx CB.Injectableφ)
         ∧̇ (renameFo CH.inj-xp CB.Injectableφ))
       ⇒̇ ((renameFo CH.inj-xw CB.Injectableφ)
        ∨̇ (renameFo CH.inj-px CB.Injectableφ))))

CH-matrix : VS.Src 2
CH-matrix = ZO.erase CH-matrix-ground refl

CH-inner1-∀ : CH-inner1 ≡ ∀̇ CH-matrix
CH-inner1-∀ = refl

CH-bot-at-power : (pω : VS.Nameᴮ)
  → VS.val CH-matrix (pω ∷ omegaNm ∷ emptyEnv) ≡ ⊥ᴮ
  → VS.val CHsrc emptyEnv ≡ ⊥ᴮ
CH-bot-at-power pω mat-bot =
  CH-bot-from-instance CH-inner1 omegaNm
    (cong (λ φ → VS.val φ emptyEnv) (sym CHsrc-∀))
    (≤⊥→≡⊥ (VS.val CH-inner1 (omegaNm ∷ emptyEnv))
      (subst (λ z → ⟨ VS.val CH-inner1 (omegaNm ∷ emptyEnv) ≤ᴮ z ⟩) mat-bot
        (subst (λ u → ⟨ u ≤ᴮ VS.val CH-matrix (pω ∷ omegaNm ∷ emptyEnv) ⟩)
          (cong (λ φ → VS.val φ (omegaNm ∷ emptyEnv)) (sym CH-inner1-∀))
          (VS.law-∀-lb CH-matrix (omegaNm ∷ emptyEnv) pω))))

CH-omega-ground : Formula S 2
CH-omega-ground = renameFo CH.om-w CB.IsOmegaφ

CH-power-ground : Formula S 2
CH-power-ground = CB.IsPowerSetφ

CH-ante-ground : Formula S 2
CH-ante-ground = CH-omega-ground ∧̇ CH-power-ground

CH-between-ground : Formula S 3
CH-between-ground =
  ((renameFo CH.inj-wx CB.Injectableφ)
   ∧̇ (renameFo CH.inj-xp CB.Injectableφ))
  ⇒̇ ((renameFo CH.inj-xw CB.Injectableφ)
   ∨̇ (renameFo CH.inj-px CB.Injectableφ))

CH-cons-ground : Formula S 2
CH-cons-ground = ∀̇ CH-between-ground

CH-matrix-split : CH-matrix-ground ≡ (CH-ante-ground ⇒̇ CH-cons-ground)
CH-matrix-split = refl

CH-omega-part : VS.Src 2
CH-omega-part = ZO.erase CH-omega-ground refl

CH-power-part : VS.Src 2
CH-power-part = ZO.erase CH-power-ground refl

CH-ante : VS.Src 2
CH-ante = ZO.erase CH-ante-ground refl

CH-between : VS.Src 3
CH-between = ZO.erase CH-between-ground refl

CH-cons : VS.Src 2
CH-cons = ZO.erase CH-cons-ground refl

at2 : VS.Nameᴮ → VS.Envᴮ 2
at2 pω = pω ∷ omegaNm ∷ emptyEnv

ante-top-from : (pω : VS.Nameᴮ)
  → VS.val CH-omega-part (at2 pω) ≡ ⊤ᴮ
  → VS.val CH-power-part (at2 pω) ≡ ⊤ᴮ
  → VS.val CH-ante (at2 pω) ≡ ⊤ᴮ
ante-top-from pω ot pt =
  cong (λ φ → VS.val φ (at2 pω)) ante-shape
  ∙ VS.law-∧ CH-omega-part CH-power-part (at2 pω)
  ∙ cong₂ _⊓ᴮ_ ot pt
  ∙ ⊓-⊤ ⊤ᴮ
  where
  ante-shape : CH-ante ≡ (CH-omega-part ∧̇ CH-power-part)
  ante-shape = refl

cons-bot-from : (pω x : VS.Nameᴮ)
  → VS.val CH-between (x ∷ at2 pω) ≡ ⊥ᴮ
  → VS.val CH-cons (at2 pω) ≡ ⊥ᴮ
cons-bot-from pω x inst-bot =
  ≤⊥→≡⊥ (VS.val CH-cons (at2 pω))
    (subst (λ z → ⟨ VS.val CH-cons (at2 pω) ≤ᴮ z ⟩) inst-bot
      (subst (λ u → ⟨ u ≤ᴮ VS.val CH-between (x ∷ at2 pω) ⟩)
        (cong (λ φ → VS.val φ (at2 pω)) cons-shape)
        (VS.law-∀-lb CH-between (at2 pω) x)))
  where
  cons-shape : CH-cons ≡ ∀̇ CH-between
  cons-shape = refl

matrix-bot-from : (pω : VS.Nameᴮ)
  → VS.val CH-ante (at2 pω) ≡ ⊤ᴮ
  → VS.val CH-cons (at2 pω) ≡ ⊥ᴮ
  → VS.val CH-matrix (at2 pω) ≡ ⊥ᴮ
matrix-bot-from pω ante-top cons-bot =
  cong (λ φ → VS.val φ (at2 pω)) matrix-shape
  ∙ VS.law-⇒ CH-ante CH-cons (at2 pω)
  ∙ cong₂ _⇒ᴮ_ ante-top cons-bot
  ∙ ⇒ᴮ-⊤ˡ ⊥ᴮ
  where
  matrix-shape : CH-matrix ≡ (CH-ante ⇒̇ CH-cons)
  matrix-shape = refl

not-CH-from-parts : (pω : VS.Nameᴮ)
  → VS.val CH-omega-part (at2 pω) ≡ ⊤ᴮ
  → VS.val CH-power-part (at2 pω) ≡ ⊤ᴮ
  → VS.val CH-cons (at2 pω) ≡ ⊥ᴮ
  → VS.val ¬CHsrc emptyEnv ≡ ⊤ᴮ
not-CH-from-parts pω ot pt cb =
  not-CH-from-bot
    (CH-bot-at-power pω
      (matrix-bot-from pω (ante-top-from pω ot pt) cb))

⊤B : Pt BAT.B
⊤B = ⊤ᴮ

⊥B : Pt BAT.B
⊥B = ⊥ᴮ


