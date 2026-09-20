{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.BooleanReals
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty
import K9.BooleanNameGround
import K9.RealNames
import K9.BooleanSeparation
import K4.Algebra
import K4.Implication
import K5.Frame
import K8.Cohen
import K8.MapOperations
import K8.GroundSets
import K8.DistinctDense
import CardinalBridge
import CodedVocabulary

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∥_∥₁; ∣_∣₁ )
open CodedVocabulary 𝒮 using ( refinesΔ )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B; weight; weight-upper; weight-least; entry-agrees; translated-check; translated-check-distinct
        ; module NG; module IC; module BK; module Atomic; module Laws; module Translation; module BSupport; module Base )
module RN = K9.RealNames 𝒮 families accessible images pow κ w
  using ( realCode; real-spec; real-name; real-entry )
open BG.NG using ( extensional; ≈ˢ-paths; hasPair; hasUnion; hasSeparation )
module C = K8.Cohen 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ w
  using ( carrier; order; coordinate; coordinate-in; coordinates; two; bit₀; bit₁; bit₀-in; bit₁-in; bits-distinct )
module MO = K8.MapOperations.Operations 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ C.coordinates C.two
  using ( compatible→agrees )
module GS = K8.GroundSets.Ground 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation κ
  using ( ordered-unique; pairOf-out )
open K4.Algebra 𝒮 using ( Pt; Pt≡; isSetPt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans )
open K4.Algebra.Lattice BG.IC.codedLattice
open K4.Algebra.Complement BG.IC.codedComplement using ( ¬ᴮ_ )
open K4.Implication 𝒮 extensional ≈ˢ-paths BG.B BG.IC.codedLattice BG.IC.codedComplement
  using ( _⇒ᴮ_; ⇒ᴮ-curry; ⇒ᴮ-uncurry; ⊓-comm; ⊓⊥→≤¬; ≤¬→⊓⊥ )
module FP = K5.Frame.Poset 𝒮 C.carrier C.order
module FF = FP.Forcing extensional ≈ˢ-paths BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
  (BG.Base.codedBase lem) using ( _⊩ᴮ_; ⊩ᴮ-intro )
open FP using ( Cond )
open K5.Frame.Poset.ForcingBase (BG.Base.codedBase lem) using ( i; i-compat← )
open FF using ( _⊩ᴮ_; ⊩ᴮ-intro )
open BG.Atomic using () renaming ( _≈ᴮ_ to eq; _∈ᴮ_ to mem )

≈→≡ : {a b : S} → ⟨ a ≈ˢ b ⟩ → a ≡ b
≈→≡ {a} {b} = subst ⟨_⟩ (≈ˢ-paths a b)

realB : S → S
realB α = BG.Translation.trᴮ (RN.realCode α)

realB-name : (α : S) → ⟨ BG.BK.IsName (realB α) ⟩
realB-name α = BG.Translation.trᴮ-name (RN.realCode α) (RN.real-name α)

realB-entry : (α n : S) → ⟨ n ∈ˢ w ⟩ → (p : Cond)
  → ⟨ refinesΔ (fst p) (C.coordinate α n) C.bit₁ ⟩
  → ⟨ BG.BK.entry (BG.translated-check n) (fst (i p)) ∈ˢ realB α ⟩
realB-entry α n hn p bit = subst ⟨_⟩ (sym (BG.Translation.trᴮ-entries (RN.realCode α) _))
  ∣ BG.NG.Check.chk n , ∣ fst p , ∣ snd p ,
    subst (λ e → ⟨ e ∈ˢ RN.realCode α ⟩) (sym (BG.entry-agrees (BG.NG.Check.chk n) (fst p)))
      (RN.real-entry α n (fst p) hn (snd p) bit) ,
    subst ⟨_⟩ (sym (≈ˢ-paths _ _)) refl ∣₁ ∣₁ ∣₁

bit₁-forces : (α n : S) → ⟨ n ∈ˢ w ⟩ → (p : Cond)
  → ⟨ refinesΔ (fst p) (C.coordinate α n) C.bit₁ ⟩
  → ⟨ p ⊩ᴮ mem (BG.translated-check n) (realB α) ⟩
bit₁-forces α n hn p bit = ⊩ᴮ-intro p _ (⊆ˢ-trans
  (⊓-glb (BG.weight (realB α) (BG.translated-check n))
    (eq (BG.translated-check n) (BG.translated-check n)) (i p)
    (BG.weight-upper (realB α) (BG.translated-check n) (i p) entry)
    (subst (λ v → ⟨ i p ≤ᴮ v ⟩) (sym (BG.Laws.≈ᴮ-refl (BG.translated-check n))) (⊤-greatest (i p))))
  (BG.Atomic.∈ᴮ-ub (BG.translated-check n) (realB α) (BG.translated-check n)
    (BG.BSupport.entry-in (realB α) (BG.translated-check n) (fst (i p)) (snd (i p)) entry)))
  where
  entry = realB-entry α n hn p bit

opposite-incompatible : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩ → (p q : Cond)
  → ⟨ refinesΔ (fst p) (C.coordinate α n) C.bit₀ ⟩
  → ⟨ refinesΔ (fst q) (C.coordinate α n) C.bit₁ ⟩
  → ⟨ i q ≤ᴮ (¬ᴮ (i p)) ⟩
opposite-incompatible α n hα hn p q zero-bit one =
  decide (lem (((i q) ⊓ᴮ (i p) ≡ ⊥ᴮ) , isSetPt BG.B _ _))
  where
  decide : ((i q) ⊓ᴮ (i p) ≡ ⊥ᴮ) ⊎ (((i q) ⊓ᴮ (i p) ≡ ⊥ᴮ) → Empty.⊥)
    → ⟨ i q ≤ᴮ (¬ᴮ (i p)) ⟩
  decide (inl disjoint) = ⊓⊥→≤¬ (i q) (i p) disjoint
  decide (inr nonzero) = Empty.rec* (C.bits-distinct
    (MO.compatible→agrees (fst p) (fst q) (snd p) (snd q)
      (i-compat← p q (λ e → Empty.rec (nonzero (⊓-comm (i q) (i p) ∙ e))))
      (C.coordinate α n) (C.coordinate-in α n hα hn) C.bit₀ C.bit₀-in C.bit₁ C.bit₁-in (zero-bit , one)))

realB-entry-out : (α x : S) (b : Pt BG.B) → ⟨ BG.BK.entry x (fst b) ∈ˢ realB α ⟩
  → ∥ Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ × (Σ[ p ∈ Cond ]
    (⟨ refinesΔ (fst p) (C.coordinate α n) C.bit₁ ⟩ ×
      (x ≡ BG.translated-check n) × (b ≡ i p)))) ∥₁
realB-entry-out α x b he = PT.rec PT.squash₁
  (λ { (z , rest) → PT.rec PT.squash₁
    (λ { (p , rest') → PT.rec PT.squash₁
      (λ { (hp , source , path) → translated z p hp source path }) rest' }) rest })
  (subst ⟨_⟩ (BG.Translation.trᴮ-entries (RN.realCode α) _) he)
  where
  Result : Type ℓ
  Result = Σ[ n ∈ S ] (⟨ n ∈ˢ w ⟩ × (Σ[ p ∈ Cond ]
    (⟨ refinesΔ (fst p) (C.coordinate α n) C.bit₁ ⟩ ×
      (x ≡ BG.translated-check n) × (b ≡ i p))))

  translated : (z p : S) (hp : ⟨ p ∈ˢ C.carrier ⟩)
    → ⟨ BG.BK.entry z p ∈ˢ RN.realCode α ⟩
    → ⟨ BG.BK.entry x (fst b) ≈ˢ BG.BK.entry (BG.Translation.trᴮ z) (fst (i (p , hp))) ⟩
    → ∥ Result ∥₁
  translated z p hp source path = PT.rec PT.squash₁
    (λ { (n , hn , rest) → PT.rec PT.squash₁
      (λ { (q , hq , bit , sourcepath) → present n hn q hq bit sourcepath }) rest })
    (subst ⟨_⟩ (RN.real-spec α (BG.NG.K.entry z p))
      (subst (λ e → ⟨ e ∈ˢ RN.realCode α ⟩) (BG.entry-agrees z p) source))
    where
    present : (n : S) → ⟨ n ∈ˢ w ⟩ → (q : S) → ⟨ q ∈ˢ C.carrier ⟩
      → ⟨ refinesΔ q (C.coordinate α n) C.bit₁ ⟩
      → ⟨ BG.NG.K.entry z p ≈ˢ BG.NG.K.entry (BG.NG.Check.chk n) q ⟩
      → ∥ Result ∥₁
    present n hn q hq bit sourcepath = ∣ n , hn , (p , hp) ,
      subst (λ r → ⟨ refinesΔ r (C.coordinate α n) C.bit₁ ⟩)
        (sym (snd (BG.NG.K.entry-inj (≈→≡ sourcepath)))) bit ,
      fst (BG.BK.entry-inj (≈→≡ path)) ∙
        cong BG.Translation.trᴮ (fst (BG.NG.K.entry-inj (≈→≡ sourcepath))) ,
      Pt≡ (snd (BG.BK.entry-inj (≈→≡ path))) ∣₁

membership-entry-bound : (m n : S) (v : Pt BG.B)
  → ((x : S) (b : Pt BG.B) → ⟨ BG.BK.entry x (fst b) ∈ˢ n ⟩
    → ⟨ (b ⊓ᴮ eq m x) ≤ᴮ v ⟩)
  → ⟨ mem m n ≤ᴮ v ⟩
membership-entry-bound m n v upper = BG.Atomic.∈ᴮ-lub m n v
  (λ x hx → ⇒ᴮ-uncurry (BG.weight n x) (eq m x) v
    (BG.weight-least n x ((eq m x) ⇒ᴮ v)
      (λ b he → ⇒ᴮ-curry b (eq m x) v (upper x b he))))

bit₀-forces : (α n : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ n ∈ˢ w ⟩ → (p : Cond)
  → ⟨ refinesΔ (fst p) (C.coordinate α n) C.bit₀ ⟩
  → ⟨ p ⊩ᴮ (¬ᴮ (mem (BG.translated-check n) (realB α))) ⟩
bit₀-forces α n hα hn p zero-bit = ⊩ᴮ-intro p _
  (⊓⊥→≤¬ (i p) value (⊓-comm (i p) value ∙ ≤¬→⊓⊥ value (i p) bound))
  where
  value : Pt BG.B
  value = mem (BG.translated-check n) (realB α)

  bound : ⟨ value ≤ᴮ (¬ᴮ (i p)) ⟩
  bound = membership-entry-bound (BG.translated-check n) (realB α) (¬ᴮ (i p)) upper
    where
    upper : (x : S) (b : Pt BG.B) → ⟨ BG.BK.entry x (fst b) ∈ˢ realB α ⟩
      → ⟨ (b ⊓ᴮ eq (BG.translated-check n) x) ≤ᴮ (¬ᴮ (i p)) ⟩
    upper x b he = PT.rec (snd ((b ⊓ᴮ eq (BG.translated-check n) x) ≤ᴮ (¬ᴮ (i p)))) examine
      (realB-entry-out α x b he)
      where
      examine : Σ[ k ∈ S ] (⟨ k ∈ˢ w ⟩ × (Σ[ q ∈ Cond ]
        (⟨ refinesΔ (fst q) (C.coordinate α k) C.bit₁ ⟩ ×
          (x ≡ BG.translated-check k) × (b ≡ i q))))
        → ⟨ (b ⊓ᴮ eq (BG.translated-check n) x) ≤ᴮ (¬ᴮ (i p)) ⟩
      examine (k , hk , q , one , xpath , bpath) = decide (lem (n ≈ˢ k))
        where
        decide : ⟨ n ≈ˢ k ⟩ ⊎ (⟨ n ≈ˢ k ⟩ → Empty.⊥)
          → ⟨ (b ⊓ᴮ eq (BG.translated-check n) x) ≤ᴮ (¬ᴮ (i p)) ⟩
        decide (inl same) = ⊆ˢ-trans (⊓-lb₁ b (eq (BG.translated-check n) x))
          (subst (λ t → ⟨ t ≤ᴮ (¬ᴮ (i p)) ⟩) (sym bpath)
            (opposite-incompatible α n hα hn p q zero-bit
              (subst (λ t → ⟨ refinesΔ (fst q) (C.coordinate α t) C.bit₁ ⟩) (sym (≈→≡ same)) one)))
        decide (inr different) = ⊆ˢ-trans
          (subst (λ t → ⟨ (b ⊓ᴮ eq (BG.translated-check n) x) ≤ᴮ t ⟩)
            (cong (eq (BG.translated-check n)) xpath ∙ BG.translated-check-distinct n k (λ h → Empty.rec (different h)))
            (⊓-lb₂ b (eq (BG.translated-check n) x))) (⊥-least (¬ᴮ (i p)))

module Separation = K9.BooleanSeparation.Atomic.Checked 𝒮 extensional ≈ˢ-paths
  C.carrier C.order BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete (BG.Base.codedBase lem)
  eq mem BG.Atomic.≈ᴮ-sym BG.Laws.∈ᴮ-congʳ BG.translated-check w
  using ( Separating; coded-dense-forces; coded-dense-top )

module DenseDistinct
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  where

  module D = K8.DistinctDense 𝒮 extensional ≈ˢ-paths hasPair hasUnion pow hasSeparation find κ w hw
    using ( E; E-spec; E-dense )

  separates-at-E : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩ → (p : Cond)
    → ⟨ fst p ∈ˢ D.E α β ⟩ → ⟨ Separation.Separating p (realB α) (realB β) ⟩
  separates-at-E α β hα hβ p hpE = PT.rec (snd goal)
    (λ { (n , hn , rest) → PT.rec (snd goal)
      (λ { (u , hu , rest') → PT.rec (snd goal)
        (λ { (v , hv , ku , kv , values) → PT.rec (snd goal)
          (λ { (b , hb , right) → PT.rec (snd goal)
            (λ { (c , hc , pb , pc , neq) → ∣ n , hn ,
              orient n hn b c hb hc
                (subst (λ z → ⟨ refinesΔ (fst p) z b ⟩) (GS.ordered-unique u α n ku) pb)
                (subst (λ z → ⟨ refinesΔ (fst p) z c ⟩) (GS.ordered-unique v β n kv) pc)
                neq ∣₁ }) right }) values }) rest' }) rest })
    (snd (subst ⟨_⟩ (D.E-spec α β (fst p)) hpE))
    where
    goal : Ω
    goal = Separation.Separating p (realB α) (realB β)

    At : S → Ω
    At n =
      ((p ⊩ᴮ mem (BG.translated-check n) (realB α)) ⊓
        (p ⊩ᴮ (¬ᴮ (mem (BG.translated-check n) (realB β))))) ⊔
      ((p ⊩ᴮ mem (BG.translated-check n) (realB β)) ⊓
        (p ⊩ᴮ (¬ᴮ (mem (BG.translated-check n) (realB α)))))

    orient : (n : S) → ⟨ n ∈ˢ w ⟩ → (b c : S) → ⟨ b ∈ˢ C.two ⟩ → ⟨ c ∈ˢ C.two ⟩
      → ⟨ refinesΔ (fst p) (C.coordinate α n) b ⟩
      → ⟨ refinesΔ (fst p) (C.coordinate β n) c ⟩
      → (⟨ b ≈ˢ c ⟩ → ⟨ ⊥ ⟩) → ⟨ At n ⟩
    orient n hn b c hb hc pb pc neq = PT.rec (snd (At n))
      (λ left → PT.rec (snd (At n)) (case left) (GS.pairOf-out C.bit₀ C.bit₁ c hc))
      (GS.pairOf-out C.bit₀ C.bit₁ b hb)
      where
      collapse : (d : S) → ⟨ b ≈ˢ d ⟩ → ⟨ c ≈ˢ d ⟩ → ⟨ At n ⟩
      collapse d bd cd = Empty.rec* (neq
        (subst ⟨_⟩ (sym (≈ˢ-paths b c)) (≈→≡ bd ∙ sym (≈→≡ cd))))

      case : (⟨ b ≈ˢ C.bit₀ ⟩ ⊎ ⟨ b ≈ˢ C.bit₁ ⟩)
        → (⟨ c ≈ˢ C.bit₀ ⟩ ⊎ ⟨ c ≈ˢ C.bit₁ ⟩) → ⟨ At n ⟩
      case (inl b0) (inl c0) = collapse C.bit₀ b0 c0
      case (inr b1) (inr c1) = collapse C.bit₁ b1 c1
      case (inl b0) (inr c1) = ∣ inr
        (bit₁-forces β n hn p (subst (λ d → ⟨ refinesΔ (fst p) (C.coordinate β n) d ⟩) (≈→≡ c1) pc) ,
         bit₀-forces α n hα hn p (subst (λ d → ⟨ refinesΔ (fst p) (C.coordinate α n) d ⟩) (≈→≡ b0) pb)) ∣₁
      case (inr b1) (inl c0) = ∣ inl
        (bit₁-forces α n hn p (subst (λ d → ⟨ refinesΔ (fst p) (C.coordinate α n) d ⟩) (≈→≡ b1) pb) ,
         bit₀-forces β n hβ hn p (subst (λ d → ⟨ refinesΔ (fst p) (C.coordinate β n) d ⟩) (≈→≡ c0) pc)) ∣₁

  forces-distinct : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
    → (⟨ α ≈ˢ β ⟩ → ⟨ ⊥ ⟩) → (p : Cond) → ⟨ p ⊩ᴮ (¬ᴮ (eq (realB α) (realB β))) ⟩
  forces-distinct α β hα hβ different = Separation.coded-dense-forces (D.E α β) (realB α) (realB β)
    (D.E-dense lem α β hα hβ different) (separates-at-E α β hα hβ)
    (λ p hp → fst (subst ⟨_⟩ (D.E-spec α β p) hp))

  distinct-top : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
    → (⟨ α ≈ˢ β ⟩ → ⟨ ⊥ ⟩) → (¬ᴮ (eq (realB α) (realB β))) ≡ ⊤ᴮ
  distinct-top α β hα hβ different = Separation.coded-dense-top lem (D.E α β) (realB α) (realB β)
    (D.E-dense lem α β hα hβ different) (separates-at-E α β hα hβ)
    (λ p hp → fst (subst ⟨_⟩ (D.E-spec α β p) hp))
