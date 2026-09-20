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
import K10.CohenBooleanLeastAll

module K10.CohenBooleanOmegaLeast
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
open import FOL.Syntax using ( var ; _∈̇_ ; _⇒̇_ ; ∀̇_ ; ∀̇∈ ; _∧̇_ )
open import FOL.Manipulation.Renaming using ( renameFo )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
import CardinalBridge

module All = K10.CohenBooleanLeastAll 𝒮 families accessible images pow
  κ w lem hw paths
module CB = CardinalBridge 𝒮

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ ; ⊆ˢ-trans )
open K4.Algebra.Lattice All.Su.Ap.Ind.BAT.IC.codedLattice
  using ( _⊓ᴮ_ ; ⊤ᴮ ; ⊓-lb₁ ; ⊓-lb₂ ; ⊓-glb )
open K4.Implication 𝒮 All.Su.Ap.Ind.NG.extensional All.Su.Ap.Ind.NG.≈ˢ-paths
  All.Su.Ap.Ind.BAT.B All.Su.Ap.Ind.BAT.IC.codedLattice
  All.Su.Ap.Ind.BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; ⊤-greatest ; ⊓-⊤ ; ⊓-comm ; ⇒ᴮ-curry ; ⇒ᴮ-mp
        ; ⇒ᴮ-⊤ˡ ; _⇒ᴮ_ )

open All.Su.Ap.Ind using ( checkNm ; emptyEnv )
open All.Su.Ap using ( indSrc )
open All.Su.Ap.Ind.BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

members : All.Su.Ap.Ind.VS.Src 2
members = ∀̇∈ (var (suc zero)) (var zero ∈̇ var (suc zero))

leastSrc : All.Su.Ap.Ind.VS.Src 1
leastSrc = ∀̇ ((renameFo CB.wk1 indSrc) ⇒̇ members)

omegaSrc : All.Su.Ap.Ind.VS.Src 1
omegaSrc = indSrc ∧̇ leastSrc

module FromAll
  (wk1-ind : (σ ρ : All.Su.Ap.Ind.VS.Nameᴮ)
    → All.Su.Ap.Ind.VS.val (renameFo CB.wk1 indSrc) (σ ∷ ρ ∷ emptyEnv)
      ≡ All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
  (contains-all : (σ : All.Su.Ap.Ind.VS.Nameᴮ) (n : S) → ⟨ n ∈ˢ w ⟩
    → ⟨ All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
        ≤ᴮ mem (All.Su.Ap.Ind.BNG.Checked.check n) (fst σ) ⟩)
  where

  members-from-contains : (σ : All.Su.Ap.Ind.VS.Nameᴮ)
    → ⟨ All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
        ≤ᴮ All.Su.Ap.Ind.VS.val members (σ ∷ checkNm w ∷ emptyEnv) ⟩
  members-from-contains σ =
    All.Su.Ap.Ind.VS.law-∀∈-glb (suc zero) (var zero ∈̇ var (suc zero))
      (σ ∷ checkNm w ∷ emptyEnv)
      (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)) λ τ →
        ⇒ᴮ-curry (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
          (mem (fst τ) (All.Su.Ap.Ind.BNG.Checked.check w))
          (All.Su.Ap.Ind.VS.val (var zero ∈̇ var (suc zero))
            (τ ∷ σ ∷ checkNm w ∷ emptyEnv))
          (subst (λ b → ⟨ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
                            ⊓ᴮ mem (fst τ) (All.Su.Ap.Ind.BNG.Checked.check w))
                          ≤ᴮ b ⟩)
            (sym (All.Su.Ap.Ind.VS.law-∈ zero (suc zero)
              (τ ∷ σ ∷ checkNm w ∷ emptyEnv)))
            (meet τ))
    where
    meet : (τ : All.Su.Ap.Ind.VS.Nameᴮ)
      → ⟨ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
            ⊓ᴮ mem (fst τ) (All.Su.Ap.Ind.BNG.Checked.check w))
          ≤ᴮ mem (fst τ) (fst σ) ⟩
    meet τ =
      ⊆ˢ-trans
        (⊓-glb
          (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
            ⇒ᴮ mem (fst τ) (fst σ))
          (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
          (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
            ⊓ᴮ mem (fst τ) (All.Su.Ap.Ind.BNG.Checked.check w))
          (⊆ˢ-trans
            (⊓-lb₂ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
              (mem (fst τ) (All.Su.Ap.Ind.BNG.Checked.check w)))
            (All.Su.Ap.Ind.CM.check-∈-lub w (fst τ)
              (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
                ⇒ᴮ mem (fst τ) (fst σ))
              (λ n hn → from-n n hn)))
          (⊓-lb₁ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
            (mem (fst τ) (All.Su.Ap.Ind.BNG.Checked.check w))))
        (⇒ᴮ-mp (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
          (mem (fst τ) (fst σ)))
      where
      from-n : (n : S) → ⟨ n ∈ˢ w ⟩
        → ⟨ eq (fst τ) (All.Su.Ap.Ind.BNG.Checked.check n)
            ≤ᴮ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
                 ⇒ᴮ mem (fst τ) (fst σ)) ⟩
      from-n n hn = ⇒ᴮ-curry
        (eq (fst τ) (All.Su.Ap.Ind.BNG.Checked.check n))
        (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
        (mem (fst τ) (fst σ))
        (subst (λ z → ⟨ z ≤ᴮ mem (fst τ) (fst σ) ⟩)
          (cong (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv) ⊓ᴮ_)
            (All.Su.Ap.Ind.BAT.Atomic.≈ᴮ-sym
              (All.Su.Ap.Ind.BNG.Checked.check n) (fst τ))
          ∙ ⊓-comm (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
              (eq (fst τ) (All.Su.Ap.Ind.BNG.Checked.check n)))
          (⊆ˢ-trans
            (⊓-glb
              (eq (All.Su.Ap.Ind.BNG.Checked.check n) (fst τ))
              (mem (All.Su.Ap.Ind.BNG.Checked.check n) (fst σ))
              (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)
                ⊓ᴮ eq (All.Su.Ap.Ind.BNG.Checked.check n) (fst τ))
              (⊓-lb₂ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
                (eq (All.Su.Ap.Ind.BNG.Checked.check n) (fst τ)))
              (⊆ˢ-trans
                (⊓-lb₁ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
                  (eq (All.Su.Ap.Ind.BNG.Checked.check n) (fst τ)))
                (contains-all σ n hn)))
            (All.Su.Ap.Ind.BAT.Laws.∈ᴮ-congˡ
              (All.Su.Ap.Ind.BNG.Checked.check n) (fst τ) (fst σ))))

  least-at-check : All.Su.Ap.Ind.VS.val leastSrc (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
  least-at-check = ≤ᴮ-antisym
    (⊤-greatest (All.Su.Ap.Ind.VS.val leastSrc (checkNm w ∷ emptyEnv)))
    (All.Su.Ap.Ind.VS.law-∀-glb
      ((renameFo CB.wk1 indSrc) ⇒̇ members)
      (checkNm w ∷ emptyEnv) ⊤ᴮ λ σ →
        subst (λ z → ⟨ ⊤ᴮ ≤ᴮ z ⟩)
          (sym (All.Su.Ap.Ind.VS.law-⇒ (renameFo CB.wk1 indSrc) members
            (σ ∷ checkNm w ∷ emptyEnv)))
          (subst (λ z → ⟨ ⊤ᴮ ≤ᴮ (z ⇒ᴮ All.Su.Ap.Ind.VS.val members
              (σ ∷ checkNm w ∷ emptyEnv)) ⟩)
            (sym (wk1-ind σ (checkNm w)))
            (⇒ᴮ-curry ⊤ᴮ
              (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv))
              (All.Su.Ap.Ind.VS.val members (σ ∷ checkNm w ∷ emptyEnv))
              (⊆ˢ-trans
                (⊓-lb₂ ⊤ᴮ (All.Su.Ap.Ind.VS.val indSrc (σ ∷ emptyEnv)))
                (members-from-contains σ)))))

  opaque
    omega-at-check : All.Su.Ap.Ind.VS.val omegaSrc (checkNm w ∷ emptyEnv) ≡ ⊤ᴮ
    omega-at-check =
      All.Su.Ap.Ind.VS.law-∧ indSrc leastSrc (checkNm w ∷ emptyEnv)
      ∙ cong₂ _⊓ᴮ_ All.Su.Ap.inductive-at-check least-at-check
      ∙ ⊓-⊤ ⊤ᴮ



