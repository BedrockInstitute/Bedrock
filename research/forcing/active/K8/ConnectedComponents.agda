{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.ConnectedComponents
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮)
  (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; _⇒̇_; ¬̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ )
open import OrdinaryProfile 𝒮 using ( iff )
open import GroundDescription 𝒮 ext paths using ( ext-path )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( inl; inr )
import Cubical.Data.Empty as Empty
import K8.GroundSets
import K8.CountableStars
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed

module Family (F X : S) where
  module CS = K8.CountableStars.Family 𝒮 ext paths pair un pow sep coll find seed F X
  open CS using ( meets; meets-sym )

  Closed : S → Ω
  Closed d = ⋀ S (λ a → (a ∈ˢ d) ⇒
    ⋀ S (λ b → (b ∈ˢ F) ⇒ (meets a b ⇒ (b ∈ˢ d))))

  closedAt : ∀ {n} → Fin n → Formula S n
  closedAt d = ∀̇∈ (var d) (∀̇∈ (con F)
    ((∃̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero)))
      ⇒̇ (var zero ∈̇ var (suc (suc d)))))

  Reach : S → S → Ω
  Reach a b = ⋀ S (λ d → (d ∈ˢ GS.power F) ⇒
    ((a ∈ˢ d) ⇒ (Closed d ⇒ (b ∈ˢ d))))

  reachFormula : S → Formula S 1
  reachFormula a = ∀̇∈ (con (GS.power F))
    ((con a ∈̇ var zero) ⇒̇ (closedAt zero ⇒̇ (var (suc zero) ∈̇ var zero)))

  opaque
    component : S → S
    component a = GS.separator F (reachFormula a)

    component-spec : (a b : S)
      → (b ∈ˢ component a) ≡ ((b ∈ˢ F) ⊓ Reach a b)
    component-spec a b = GS.separator-spec F (reachFormula a) b

  component-sub : (a : S) → ⟨ subsetΔ (component a) F ⟩
  component-sub a b hb = fst (subst ⟨_⟩ (component-spec a b) hb)

  component-self : (a : S) → ⟨ a ∈ˢ F ⟩ → ⟨ a ∈ˢ component a ⟩
  component-self a ha = subst ⟨_⟩ (sym (component-spec a a))
    (ha , λ d hd ad closed → ad)

  component-closed : (a : S) → ⟨ Closed (component a) ⟩
  component-closed a b hb c hc meet = subst ⟨_⟩ (sym (component-spec a c))
    (hc , λ d hd ad closed → closed b
      (snd (subst ⟨_⟩ (component-spec a b) hb) d hd ad closed) c hc meet)

  component-least : (a d : S) → ⟨ subsetΔ d F ⟩ → ⟨ a ∈ˢ d ⟩ → ⟨ Closed d ⟩
    → ⟨ subsetΔ (component a) d ⟩
  component-least a d sub ad closed b hb =
    snd (subst ⟨_⟩ (component-spec a b) hb) d
      (subst ⟨_⟩ (sym (GS.power-spec F d)) sub) ad closed

  component-nested : (a b : S) → ⟨ b ∈ˢ component a ⟩
    → ⟨ subsetΔ (component b) (component a) ⟩
  component-nested a b hb = component-least b (component a)
    (component-sub a) hb (component-closed a)

  opaque
    outside : S → S
    outside d = GS.separator F (¬̇ (var zero ∈̇ con d))

    outside-spec : (d a : S) → (a ∈ˢ outside d) ≡ ((a ∈ˢ F) ⊓ ((a ∈ˢ d) ⇒ ⊥))
    outside-spec d a = GS.separator-spec F (¬̇ (var zero ∈̇ con d)) a

  outside-closed : (d : S) → ⟨ Closed d ⟩ → ⟨ Closed (outside d) ⟩
  outside-closed d closed a ha b hb meet = subst ⟨_⟩ (sym (outside-spec d b))
    (hb , λ bd → snd info (closed b bd a (fst info) (meets-sym a b meet)))
    where
    info = subst ⟨_⟩ (outside-spec d a) ha

  component-sym : LEM ℓ → (a b : S) → ⟨ a ∈ˢ F ⟩
    → ⟨ b ∈ˢ component a ⟩ → ⟨ a ∈ˢ component b ⟩
  component-sym lem a b ha hb with lem (a ∈ˢ component b)
  ... | inl yes = yes
  ... | inr no = Empty.rec* (snd (subst ⟨_⟩ (outside-spec (component b) b) outside-b)
      (component-self b (component-sub a b hb)))
    where
    outside-b : ⟨ b ∈ˢ outside (component b) ⟩
    outside-b = component-least a (outside (component b))
      (λ z hz → fst (subst ⟨_⟩ (outside-spec (component b) z) hz))
      (subst ⟨_⟩ (sym (outside-spec (component b) a)) (ha , λ h → Empty.rec (no h)))
      (outside-closed (component b) (component-closed b)) b hb

  component-equal : LEM ℓ → (a b : S) → ⟨ a ∈ˢ F ⟩
    → ⟨ b ∈ˢ component a ⟩ → component a ≡ component b
  component-equal lem a b ha hb = ext-path λ z → ⇔toPath
    (component-nested b a (component-sym lem a b ha hb) z)
    (component-nested a b hb z)

  adjacent-in-component : (a b : S) → ⟨ a ∈ˢ F ⟩ → ⟨ b ∈ˢ F ⟩
    → ⟨ meets a b ⟩ → ⟨ b ∈ˢ component a ⟩
  adjacent-in-component a b ha hb = component-closed a a (component-self a ha) b hb
