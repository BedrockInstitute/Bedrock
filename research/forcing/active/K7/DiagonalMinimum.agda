{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CardinalBridge
import K8.OmegaSuccessor

module K7.DiagonalMinimum {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pair : OrdinaryProfile.Pairing 𝒮) (un : OrdinaryProfile.Union 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮) (sep : OrdinaryProfile.Separation 𝒮)
  (coll : OrdinaryProfile.Collection 𝒮)
  (find : OrdinaryProfile.FoundationInduction 𝒮)
  (seed : ZFStructure.S 𝒮) (lem : LEM ℓ)
  (w : ZFStructure.S 𝒮) (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (d : ZFStructure.S 𝒮) (od : ⟨ CardinalBridge.isOrdinal 𝒮 d ⟩)
  (successor-closed : (a : ZFStructure.S 𝒮) → ⟨ ZFStructure._∈ˢ_ 𝒮 a d ⟩
    → ⟨ ZFStructure._∈ˢ_ 𝒮
      (K8.OmegaSuccessor.successor 𝒮 ext paths pair un pow sep find seed a) d ⟩)
  (members-countable : (a : ZFStructure.S 𝒮) → ⟨ ZFStructure._∈ˢ_ 𝒮 a d ⟩
    → ⟨ CardinalBridge.injectable 𝒮 a w ⟩)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; _∧̇_; ¬̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
import CodedVocabulary
import K7.LexicographicMinimum
import K7.OrdinalDiagonal
import K8.DiagonalOrder
import K8.GroundSets

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )
open PT using ( ∣_∣₁ )
module Code = CodedVocabulary 𝒮
module GS = K8.GroundSets.Ground 𝒮 ext paths pair un pow sep seed
  using ( product; product-out; separator; separator-spec )
module Lex = K7.LexicographicMinimum 𝒮 ext paths sep find lem d
module DO = K8.DiagonalOrder 𝒮 ext paths pair un pow sep coll find seed lem
  using ( Diag; module OM; module LX )
module OM = DO.OM using ( maxω; maxω-in; maxAt; maxRel; maxRel-witness; maxRel→maxω )
module Diagonal = K7.OrdinalDiagonal.AtOrdinal 𝒮 ext paths pair un pow sep coll find
  seed lem w hw d od successor-closed members-countable
  using ( P; lt; lt-out )

diag-lex : (a b c e : S) → ⟨ DO.Diag a b c e ⟩
  → ⟨ Lex.ReverseLex (b ∷ a ∷ OM.maxω a b ∷ []) (e ∷ c ∷ OM.maxω c e ∷ []) ⟩
diag-lex a b c e = PT.rec (snd target) λ
  { (inl less) → ∣ inl ∣ inl ∣ inr (tt* , less) ∣₁ ∣₁ ∣₁
  ; (inr (eq , rest)) → PT.rec (snd target) (λ
      { (inl less) → ∣ inl ∣ inr ((eq , tt*) , less) ∣₁ ∣₁
      ; (inr (equal , less)) → ∣ inr ((equal , eq , tt*) , less) ∣₁ }) rest }
  where
  target : Ω
  target = Lex.ReverseLex (b ∷ a ∷ OM.maxω a b ∷ []) (e ∷ c ∷ OM.maxω c e ∷ [])

Least : S → S → Ω
Least A p = (p ∈ˢ A) ⊓ ⋀ S (λ q → (q ∈ˢ A) ⇒ (Diagonal.lt q p ⇒ ⊥))

minimum : (A : S) → ⟨ Code.subsetΔ A Diagonal.P ⟩
  → ⟨ ⋁ S (λ p → p ∈ˢ A) ⟩ → ⟨ ⋁ S (Least A) ⟩
minimum A sub inhabited = PT.rec (snd (⋁ S (Least A))) finish
  (Lex.minimum 3 formula (PT.rec (snd candidates) fromPair inhabited))
  where
  formula : Formula S 3
  formula = ∃̇∈ (con A)
    (Code.prAtˢ zero (suc (suc zero)) (suc zero)
      ∧̇ OM.maxAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero))

  candidates : Ω
  candidates = ⋁ (Vec S 3) (Lex.Witness formula)

  fromPair : Σ[ p ∈ S ] ⟨ p ∈ˢ A ⟩ → ⟨ candidates ⟩
  fromPair (p , hp) = PT.map (λ { (a , b , ha , hb , kp) →
    (b ∷ a ∷ OM.maxω a b ∷ []) , (hb , ha , OM.maxω-in d a b ha hb , tt*)
      , ∣ p , hp , kp , OM.maxRel-witness a b ∣₁ })
    (GS.product-out d d p (sub p hp))

  finish : Σ[ ν ∈ Vec S 3 ] ⟨ Lex.Minimum formula ν ⟩ → ⟨ ⋁ S (Least A) ⟩
  finish (b ∷ a ∷ m ∷ [] , (bounded , witness) , least) = PT.map atPair witness
    where
    atPair : Σ[ p ∈ S ] ⟨ (p ∈ˢ A) ⊓ (Code.isKPairΔ p a b ⊓ OM.maxRel m a b) ⟩
      → Σ[ p ∈ S ] ⟨ Least A p ⟩
    atPair (p , hp , kp , hm) = p , hp , smaller
      where
      smaller : (q : S) → ⟨ q ∈ˢ A ⟩ → ⟨ Diagonal.lt q p ⟩ → ⟨ ⊥ ⟩
      smaller q hq below = PT.rec (snd ⊥)
        (λ { (c , e , hc , he , kq) →
          least (e ∷ c ∷ OM.maxω c e ∷ [])
            ((he , hc , OM.maxω-in d c e hc he , tt*) ,
              ∣ q , hq , kq , OM.maxRel-witness c e ∣₁)
            (subst (λ z → ⟨ Lex.ReverseLex (e ∷ c ∷ OM.maxω c e ∷ []) (b ∷ a ∷ z ∷ []) ⟩)
              (sym (OM.maxRel→maxω m a b hm))
              (diag-lex c e a b (Diagonal.lt-out q p c e a b kq kp below))) })
        (GS.product-out d d q (sub q hq))

induction : (φ : Formula S 1)
  → ((p : S) → ⟨ p ∈ˢ Diagonal.P ⟩
    → ((q : S) → ⟨ q ∈ˢ Diagonal.P ⟩ → ⟨ Diagonal.lt q p ⟩ → ⟨ (q ∷ []) ⊨ φ ⟩)
    → ⟨ (p ∷ []) ⊨ φ ⟩)
  → (p : S) → ⟨ p ∈ˢ Diagonal.P ⟩ → ⟨ (p ∷ []) ⊨ φ ⟩
induction φ step p hp = decide (lem ((p ∷ []) ⊨ φ))
  where
  bad : S
  bad = GS.separator Diagonal.P (¬̇ φ)

  spec : (q : S) → (q ∈ˢ bad) ≡ ((q ∈ˢ Diagonal.P) ⊓ (((q ∷ []) ⊨ φ) ⇒ ⊥))
  spec = GS.separator-spec Diagonal.P (¬̇ φ)

  contradiction : Σ[ q ∈ S ] ⟨ Least bad q ⟩ → ⟨ (p ∷ []) ⊨ φ ⟩
  contradiction (q , hq , least) = Empty.rec* (snd atq (step q (fst atq) predecessors))
    where
    atq : ⟨ (q ∈ˢ Diagonal.P) ⊓ (((q ∷ []) ⊨ φ) ⇒ ⊥) ⟩
    atq = subst ⟨_⟩ (spec q) hq

    predecessors : (r : S) → ⟨ r ∈ˢ Diagonal.P ⟩ → ⟨ Diagonal.lt r q ⟩
      → ⟨ (r ∷ []) ⊨ φ ⟩
    predecessors r hr below = choose (lem ((r ∷ []) ⊨ φ))
      where
      choose : ⟨ (r ∷ []) ⊨ φ ⟩ ⊎ (⟨ (r ∷ []) ⊨ φ ⟩ → Empty.⊥)
        → ⟨ (r ∷ []) ⊨ φ ⟩
      choose (inl yes) = yes
      choose (inr absent) = Empty.rec* (least r
        (subst ⟨_⟩ (sym (spec r)) (hr , λ h → Empty.rec (absent h))) below)

  decide : ⟨ (p ∷ []) ⊨ φ ⟩ ⊎ (⟨ (p ∷ []) ⊨ φ ⟩ → Empty.⊥)
    → ⟨ (p ∷ []) ⊨ φ ⟩
  decide (inl yes) = yes
  decide (inr no) = PT.rec (snd ((p ∷ []) ⊨ φ)) contradiction
    (minimum bad (λ q hq → fst (subst ⟨_⟩ (spec q) hq))
      ∣ p , subst ⟨_⟩ (sym (spec p)) (hp , λ h → Empty.rec (no h)) ∣₁)
