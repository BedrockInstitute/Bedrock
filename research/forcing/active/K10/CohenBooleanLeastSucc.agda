{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import CardinalBridge
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Sum as Sum
import K4.Algebra
import K4.Implication
import K10.CohenBooleanSuccApply

module K10.CohenBooleanLeastSucc
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (hw : ⟨ CardinalBridge.isOmega 𝒮 w ⟩)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var ; _∈̇_ ; _≐_ ; _∨̇_ ; _∧̇_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open PT using ( ∣_∣₁ )
import CardinalBridge

module Ap = K10.CohenBooleanSuccApply 𝒮 families accessible images pow
  κ w lem hw paths
module CB = CardinalBridge 𝒮

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice Ap.Ind.BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; _⊔ᴮ_ ; ⊤ᴮ ; ⊥ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb ; ⊔-lub )
open K4.Implication 𝒮 Ap.Ind.NG.extensional Ap.Ind.NG.≈ˢ-paths Ap.Ind.BAT.B
  Ap.Ind.BAT.IC.codedLattice Ap.Ind.BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ ; ⊓-comm ; ⇒ᴮ-curry ; ⇒ᴮ-mp
        ; ⇒ᴮ-⊤ˡ ; ⇒ᴮ-monotoneʳ ; _⇒ᴮ_ )

open Ap.Ind using ( checkNm ; emptyEnv )
open Ap using ( succInner ; succExists ; succClause ; memberR ; upR ; downR
              ; inner-shape ; up-body₃ ; down-body₃ )
open Ap.Ind.BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

⇒-antiˡ : (a a' b : Pt Ap.Ind.BAT.B) → ⟨ a' ≤ᴮ a ⟩
  → ⟨ (a ⇒ᴮ b) ≤ᴮ (a' ⇒ᴮ b) ⟩
⇒-antiˡ a a' b h = ⇒ᴮ-curry (a ⇒ᴮ b) a' b
  (⊆ˢ-trans
    (⊓-glb (a ⇒ᴮ b) a ((a ⇒ᴮ b) ⊓ᴮ a')
      (⊓-lb₁ (a ⇒ᴮ b) a')
      (⊆ˢ-trans (⊓-lb₂ (a ⇒ᴮ b) a') h))
    (⇒ᴮ-mp a b))

weight-≤-mem : (n x : S) → ⟨ x ∈ˢ Ap.Ind.BNG.BSupport.support n ⟩
  → ⟨ Ap.Ind.BNG.weight n x ≤ᴮ mem x n ⟩
weight-≤-mem n x hx =
  subst (λ z → ⟨ z ≤ᴮ mem x n ⟩) (⊓-⊤ (Ap.Ind.BNG.weight n x))
    (subst (λ z → ⟨ (Ap.Ind.BNG.weight n x ⊓ᴮ z) ≤ᴮ mem x n ⟩)
      (Ap.Ind.BAT.Laws.≈ᴮ-refl x)
      (Ap.Ind.BAT.Atomic.∈ᴮ-ub x n x hx))

env3' : Ap.Ind.VS.Nameᴮ → S → Ap.Ind.VS.Nameᴮ → Ap.Ind.VS.Envᴮ 3
env3' τ n σ = τ ∷ checkNm n ∷ σ ∷ emptyEnv

check-support-out : (a x : S)
  → ⟨ x ∈ˢ Ap.Ind.BNG.BSupport.support (Ap.Ind.BNG.Checked.check a) ⟩
  → PT.∥ Σ[ y ∈ S ] (⟨ y ∈ˢ a ⟩ × (x ≡ Ap.Ind.BNG.Checked.check y)) ∥₁
check-support-out a x h = PT.rec PT.squash₁
  (λ { (b , hb , hin) → PT.map
    (λ { (y , hy , eqn) →
      y , hy , fst (Ap.Ind.BNG.BK.entry-inj (Ap.Ind.≈→≡ eqn)) })
    (subst ⟨_⟩
      (Ap.Ind.BNG.Checked.check-spec a (Ap.Ind.BNG.BK.entry x b)) hin) })
  (Ap.Ind.BNG.BSupport.entry-out (Ap.Ind.BNG.Checked.check a) x h)

inner-val : (τ : Ap.Ind.VS.Nameᴮ) (n : S) (σ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val succInner (env3' τ n σ)
    ≡ (Ap.Ind.VS.val memberR (env3' τ n σ)
        ⊓ᴮ (Ap.Ind.VS.val upR (env3' τ n σ)
            ⊓ᴮ Ap.Ind.VS.val downR (env3' τ n σ)))
inner-val τ n σ =
  cong (λ φ → Ap.Ind.VS.val φ (env3' τ n σ)) inner-shape
  ∙ Ap.Ind.VS.law-∧ memberR (upR ∧̇ downR) (env3' τ n σ)
  ∙ cong (Ap.Ind.VS.val memberR (env3' τ n σ) ⊓ᴮ_)
      (Ap.Ind.VS.law-∧ upR downR (env3' τ n σ))

c≤member : (τ : Ap.Ind.VS.Nameᴮ) (n : S) (σ : Ap.Ind.VS.Nameᴮ)
  → ⟨ Ap.Ind.VS.val succInner (env3' τ n σ)
      ≤ᴮ Ap.Ind.VS.val memberR (env3' τ n σ) ⟩
c≤member τ n σ =
  subst (λ z → ⟨ z ≤ᴮ Ap.Ind.VS.val memberR (env3' τ n σ) ⟩)
    (sym (inner-val τ n σ))
    (⊓-lb₁ (Ap.Ind.VS.val memberR (env3' τ n σ))
      (Ap.Ind.VS.val upR (env3' τ n σ)
        ⊓ᴮ Ap.Ind.VS.val downR (env3' τ n σ)))

c≤up : (τ : Ap.Ind.VS.Nameᴮ) (n : S) (σ : Ap.Ind.VS.Nameᴮ)
  → ⟨ Ap.Ind.VS.val succInner (env3' τ n σ)
      ≤ᴮ Ap.Ind.VS.val upR (env3' τ n σ) ⟩
c≤up τ n σ =
  subst (λ z → ⟨ z ≤ᴮ Ap.Ind.VS.val upR (env3' τ n σ) ⟩)
    (sym (inner-val τ n σ))
    (⊆ˢ-trans
      (⊓-lb₂ (Ap.Ind.VS.val memberR (env3' τ n σ))
        (Ap.Ind.VS.val upR (env3' τ n σ)
          ⊓ᴮ Ap.Ind.VS.val downR (env3' τ n σ)))
      (⊓-lb₁ (Ap.Ind.VS.val upR (env3' τ n σ))
        (Ap.Ind.VS.val downR (env3' τ n σ))))

c≤down : (τ : Ap.Ind.VS.Nameᴮ) (n : S) (σ : Ap.Ind.VS.Nameᴮ)
  → ⟨ Ap.Ind.VS.val succInner (env3' τ n σ)
      ≤ᴮ Ap.Ind.VS.val downR (env3' τ n σ) ⟩
c≤down τ n σ =
  subst (λ z → ⟨ z ≤ᴮ Ap.Ind.VS.val downR (env3' τ n σ) ⟩)
    (sym (inner-val τ n σ))
    (⊆ˢ-trans
      (⊓-lb₂ (Ap.Ind.VS.val memberR (env3' τ n σ))
        (Ap.Ind.VS.val upR (env3' τ n σ)
          ⊓ᴮ Ap.Ind.VS.val downR (env3' τ n σ)))
      (⊓-lb₂ (Ap.Ind.VS.val upR (env3' τ n σ))
        (Ap.Ind.VS.val downR (env3' τ n σ))))

member-val : (τ : Ap.Ind.VS.Nameᴮ) (n : S) (σ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val memberR (env3' τ n σ)
    ≡ mem (Ap.Ind.BNG.Checked.check n) (fst τ)
member-val τ n σ = Ap.Ind.VS.law-∈ (suc zero) zero (env3' τ n σ)

disj-val : (ν : Ap.Ind.VS.Nameᴮ) (τ : Ap.Ind.VS.Nameᴮ) (n : S)
  (σ : Ap.Ind.VS.Nameᴮ)
  → Ap.Ind.VS.val down-body₃ (ν ∷ env3' τ n σ)
    ≡ (mem (fst ν) (Ap.Ind.BNG.Checked.check n)
        ⊔ᴮ eq (fst ν) (Ap.Ind.BNG.Checked.check n))
disj-val ν τ n σ =
  Ap.Ind.VS.law-∨ (var zero ∈̇ var (suc (suc zero)))
    (var zero ≐ var (suc (suc zero))) (ν ∷ env3' τ n σ)
  ∙ cong₂ _⊔ᴮ_
      (Ap.Ind.VS.law-∈ zero (suc (suc zero)) (ν ∷ env3' τ n σ))
      (Ap.Ind.VS.law-≐ zero (suc (suc zero)) (ν ∷ env3' τ n σ))

∈n→∈m : (m n : S) → ⟨ CB.isSuccOf m n ⟩ → (x : S)
  → ⟨ mem x (Ap.Ind.BNG.Checked.check n)
      ≤ᴮ mem x (Ap.Ind.BNG.Checked.check m) ⟩
∈n→∈m m n hsucc x = Ap.Ind.CM.check-∈-lub n x
  (mem x (Ap.Ind.BNG.Checked.check m))
  (λ k hk → Ap.Ind.CM.check-∈-ub m k x (hsucc .snd .fst k hk))

≈n→∈m : (m n : S) → ⟨ CB.isSuccOf m n ⟩ → (x : S)
  → ⟨ eq x (Ap.Ind.BNG.Checked.check n)
      ≤ᴮ mem x (Ap.Ind.BNG.Checked.check m) ⟩
≈n→∈m m n hsucc x =
  subst (λ z → ⟨ z ≤ᴮ mem x (Ap.Ind.BNG.Checked.check m) ⟩)
    (⊓-⊤ (eq (Ap.Ind.BNG.Checked.check n) x)
      ∙ Ap.Ind.BAT.Atomic.≈ᴮ-sym (Ap.Ind.BNG.Checked.check n) x)
    (subst (λ z → ⟨ (eq (Ap.Ind.BNG.Checked.check n) x ⊓ᴮ z)
                    ≤ᴮ mem x (Ap.Ind.BNG.Checked.check m) ⟩)
      (Ap.Ind.CM.check-∈-top n m (hsucc .fst))
      (Ap.Ind.BAT.Laws.∈ᴮ-congˡ (Ap.Ind.BNG.Checked.check n) x
        (Ap.Ind.BNG.Checked.check m)))

disj→∈m : (m n : S) → ⟨ CB.isSuccOf m n ⟩ → (x : S)
  → ⟨ (mem x (Ap.Ind.BNG.Checked.check n)
        ⊔ᴮ eq x (Ap.Ind.BNG.Checked.check n))
      ≤ᴮ mem x (Ap.Ind.BNG.Checked.check m) ⟩
disj→∈m m n hsucc x = ⊔-lub
  (mem x (Ap.Ind.BNG.Checked.check n))
  (eq x (Ap.Ind.BNG.Checked.check n))
  (mem x (Ap.Ind.BNG.Checked.check m))
  (∈n→∈m m n hsucc x) (≈n→∈m m n hsucc x)

succ-inner-le-eq : (m n : S) → ⟨ CB.isSuccOf m n ⟩
  → (τ σ : Ap.Ind.VS.Nameᴮ)
  → ⟨ Ap.Ind.VS.val succInner (env3' τ n σ)
      ≤ᴮ eq (fst τ) (Ap.Ind.BNG.Checked.check m) ⟩
succ-inner-le-eq m n hsucc τ σ =
  Ap.Ind.BAT.Atomic.≈ᴮ-glb (fst τ) (Ap.Ind.BNG.Checked.check m)
    (Ap.Ind.VS.val succInner (env3' τ n σ)) left right
  where
  c = Ap.Ind.VS.val succInner (env3' τ n σ)
  left : (x : S) → ⟨ x ∈ˢ Ap.Ind.BNG.BSupport.support (fst τ) ⟩
    → ⟨ c ≤ᴮ (Ap.Ind.BNG.weight (fst τ) x
              ⇒ᴮ mem x (Ap.Ind.BNG.Checked.check m)) ⟩
  left x hx =
    ⊆ˢ-trans down-to-disj
      (⊆ˢ-trans
        (⇒-antiˡ (mem x (fst τ)) (Ap.Ind.BNG.weight (fst τ) x) disj
          (weight-≤-mem (fst τ) x hx))
        (⇒ᴮ-monotoneʳ (Ap.Ind.BNG.weight (fst τ) x) disj
          (mem x (Ap.Ind.BNG.Checked.check m))
          (disj→∈m m n hsucc x)))
    where
    ν : Ap.Ind.VS.Nameᴮ
    ν = x , Ap.Ind.BNG.BSupport.K.child-is-name (fst τ) (snd τ) x
      (Ap.Ind.BNG.BSupport.support-out (fst τ) x hx)
    disj = mem x (Ap.Ind.BNG.Checked.check n)
      ⊔ᴮ eq x (Ap.Ind.BNG.Checked.check n)
    down-to-disj : ⟨ c ≤ᴮ (mem x (fst τ) ⇒ᴮ disj) ⟩
    down-to-disj =
      ⊆ˢ-trans (c≤down τ n σ)
        (subst (λ b → ⟨ Ap.Ind.VS.val downR (env3' τ n σ)
                        ≤ᴮ (mem x (fst τ) ⇒ᴮ b) ⟩)
          (disj-val ν τ n σ)
          (Ap.Ind.VS.law-∀∈-lb zero down-body₃ (env3' τ n σ) ν))
  right : (y : S)
    → ⟨ y ∈ˢ Ap.Ind.BNG.BSupport.support (Ap.Ind.BNG.Checked.check m) ⟩
    → ⟨ c ≤ᴮ (Ap.Ind.BNG.weight (Ap.Ind.BNG.Checked.check m) y
              ⇒ᴮ mem y (fst τ)) ⟩
  right y hy = PT.rec
    (snd (c ≤ᴮ (Ap.Ind.BNG.weight (Ap.Ind.BNG.Checked.check m) y
                ⇒ᴮ mem y (fst τ))))
    (λ { (k , hk , p) →
      subst (λ z → ⟨ c ≤ᴮ (Ap.Ind.BNG.weight (Ap.Ind.BNG.Checked.check m) z
                            ⇒ᴮ mem z (fst τ)) ⟩)
        (sym p) (from-k k hk) })
    (check-support-out m y hy)
    where
    from-k : (k : S) → ⟨ k ∈ˢ m ⟩
      → ⟨ c ≤ᴮ (Ap.Ind.BNG.weight (Ap.Ind.BNG.Checked.check m)
                  (Ap.Ind.BNG.Checked.check k)
                ⇒ᴮ mem (Ap.Ind.BNG.Checked.check k) (fst τ)) ⟩
    from-k k hk = ⇒ᴮ-curry c
      (Ap.Ind.BNG.weight (Ap.Ind.BNG.Checked.check m)
        (Ap.Ind.BNG.Checked.check k))
      (mem (Ap.Ind.BNG.Checked.check k) (fst τ))
      (⊆ˢ-trans (⊓-lb₁ c
        (Ap.Ind.BNG.weight (Ap.Ind.BNG.Checked.check m)
          (Ap.Ind.BNG.Checked.check k)))
        (PT.rec
          (snd (c ≤ᴮ mem (Ap.Ind.BNG.Checked.check k) (fst τ)))
          choose (hsucc .snd .snd k hk)))
      where
      choose : ⟨ k ∈ˢ n ⟩ Sum.⊎ ⟨ k ≈ˢ n ⟩
        → ⟨ c ≤ᴮ mem (Ap.Ind.BNG.Checked.check k) (fst τ) ⟩
      choose (Sum.inl kin) =
        ⊆ˢ-trans (c≤up τ n σ)
          (subst (λ z → ⟨ Ap.Ind.VS.val upR (env3' τ n σ) ≤ᴮ z ⟩)
            (cong (λ u → u ⇒ᴮ mem (Ap.Ind.BNG.Checked.check k) (fst τ))
              (Ap.Ind.CM.check-∈-top k n kin)
            ∙ ⇒ᴮ-⊤ˡ (mem (Ap.Ind.BNG.Checked.check k) (fst τ)))
            (subst (λ b → ⟨ Ap.Ind.VS.val upR (env3' τ n σ)
                            ≤ᴮ (mem (Ap.Ind.BNG.Checked.check k)
                                  (Ap.Ind.BNG.Checked.check n) ⇒ᴮ b) ⟩)
              (Ap.Ind.VS.law-∈ zero (suc zero)
                (checkNm k ∷ env3' τ n σ))
              (Ap.Ind.VS.law-∀∈-lb (suc zero) up-body₃
                (env3' τ n σ) (checkNm k))))
      choose (Sum.inr keq) =
        ⊆ˢ-trans (c≤member τ n σ)
          (subst (λ z → ⟨ z ≤ᴮ mem (Ap.Ind.BNG.Checked.check k) (fst τ) ⟩)
            (sym (member-val τ n σ ∙ eq-meet))
            (Ap.Ind.BAT.Laws.∈ᴮ-congˡ
              (Ap.Ind.BNG.Checked.check n)
              (Ap.Ind.BNG.Checked.check k) (fst τ)))
        where
        eq-meet :
          mem (Ap.Ind.BNG.Checked.check n) (fst τ)
          ≡ (eq (Ap.Ind.BNG.Checked.check n)
                (Ap.Ind.BNG.Checked.check k)
              ⊓ᴮ mem (Ap.Ind.BNG.Checked.check n) (fst τ))
        eq-meet =
          sym (⊓-⊤ (mem (Ap.Ind.BNG.Checked.check n) (fst τ)))
          ∙ cong (mem (Ap.Ind.BNG.Checked.check n) (fst τ) ⊓ᴮ_)
              (sym (Ap.Ind.BAT.Atomic.≈ᴮ-sym
                    (Ap.Ind.BNG.Checked.check n)
                    (Ap.Ind.BNG.Checked.check k)
                  ∙ Ap.Ind.check-eq-top keq))
          ∙ ⊓-comm (mem (Ap.Ind.BNG.Checked.check n) (fst τ))
              (eq (Ap.Ind.BNG.Checked.check n)
                (Ap.Ind.BNG.Checked.check k))

contains-check-succ : (m n : S) → ⟨ CB.isSuccOf m n ⟩
  → (σ : Ap.Ind.VS.Nameᴮ)
  → ⟨ Ap.Ind.VS.val succExists (checkNm n ∷ σ ∷ emptyEnv)
      ≤ᴮ mem (Ap.Ind.BNG.Checked.check m) (fst σ) ⟩
contains-check-succ m n hsucc σ =
  Ap.Ind.VS.law-∃∈-lub (suc zero) succInner (checkNm n ∷ σ ∷ emptyEnv)
    (mem (Ap.Ind.BNG.Checked.check m) (fst σ)) λ τ →
      ⊆ˢ-trans
        (⊓-glb (eq (fst τ) (Ap.Ind.BNG.Checked.check m)) (mem (fst τ) (fst σ))
          (mem (fst τ) (fst σ)
            ⊓ᴮ Ap.Ind.VS.val succInner (env3' τ n σ))
          (⊆ˢ-trans (⊓-lb₂ (mem (fst τ) (fst σ))
            (Ap.Ind.VS.val succInner (env3' τ n σ)))
            (succ-inner-le-eq m n hsucc τ σ))
          (⊓-lb₁ (mem (fst τ) (fst σ))
            (Ap.Ind.VS.val succInner (env3' τ n σ))))
        (Ap.Ind.BAT.Laws.∈ᴮ-congˡ (fst τ) (Ap.Ind.BNG.Checked.check m) (fst σ))

opaque
  contains-check-succ-clause : (m n : S) → ⟨ CB.isSuccOf m n ⟩
    → (σ : Ap.Ind.VS.Nameᴮ)
    → ⟨ (Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
          ⊓ᴮ mem (Ap.Ind.BNG.Checked.check n) (fst σ))
        ≤ᴮ mem (Ap.Ind.BNG.Checked.check m) (fst σ) ⟩
  contains-check-succ-clause m n hsucc σ =
    ⊆ˢ-trans
      (⊓-glb
        (mem (Ap.Ind.BNG.Checked.check n) (fst σ)
          ⇒ᴮ Ap.Ind.VS.val succExists (checkNm n ∷ σ ∷ emptyEnv))
        (mem (Ap.Ind.BNG.Checked.check n) (fst σ))
        (Ap.Ind.VS.val succClause (σ ∷ emptyEnv)
          ⊓ᴮ mem (Ap.Ind.BNG.Checked.check n) (fst σ))
        (⊆ˢ-trans
          (⊓-lb₁ (Ap.Ind.VS.val succClause (σ ∷ emptyEnv))
            (mem (Ap.Ind.BNG.Checked.check n) (fst σ)))
          (Ap.Ind.VS.law-∀∈-lb zero succExists (σ ∷ emptyEnv) (checkNm n)))
        (⊓-lb₂ (Ap.Ind.VS.val succClause (σ ∷ emptyEnv))
          (mem (Ap.Ind.BNG.Checked.check n) (fst σ))))
      (⊆ˢ-trans
        (⇒ᴮ-mp (mem (Ap.Ind.BNG.Checked.check n) (fst σ))
          (Ap.Ind.VS.val succExists (checkNm n ∷ σ ∷ emptyEnv)))
        (contains-check-succ m n hsucc σ))


