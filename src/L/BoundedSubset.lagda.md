# The bounded-subset lemma

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.BoundedSubset {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; Term; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
  ; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm; mapFo-comp; embed )
open import FOL.Manipulation.Renaming using ( renameFo; renameTm )
open import FOL.Manipulation.Parameters using ( countFo; padRight; lookup-map )
import FOL.Count
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isTransV; Lset; 𝒟ₒ; Lset-out; Lset-mono
        ; layer-trans; Lset-layer )
open import L.Condensation {ℓ} lem using
  ( DefBodyB; Δ₀-DefBodyB
  ; module GraphB
  )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf )
open import V.Presentation {ℓ} using ( fiber; member; ↪-inj )
open import V.Collapse {ℓ} using ( module Collapse; isExt )

open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; []; _++_ )
open import Cubical.Data.Sigma using ( _×_; _,_; Σ≡Prop )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module CS = hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ )

-- =====================================================================
-- SECTION 1: THE SIGMA-1 LEVEL-HOOD AT THE CLASS CARRIER.
-- =====================================================================

-- The bounded graph at the class carrier, at the environment
-- w ∷ v ∷ γ ∷ K ∷ δ (4 + n).  The witness w is variable zero; v is the
-- value, γ the ordinal index, K the bound.  The bounded existential
-- ranges over K (variable three).  This corrects the probe's bound,
-- which ranged over the ordinal slot.
module LevelHood {n : ℕ}
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin (7 + n)) where

  m : ℕ
  m = suc (suc (suc (suc (suc n))))

  module G = GraphB {m}
    (DefBodyB {m} (suc zero) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
      (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1))))))
    (DefBodyB {suc (suc m)} (suc zero) (suc (suc (suc (suc zero))))
      (suc (suc (suc (suc (suc M0)))))
      (suc (suc (suc (suc (suc M1)))))
      (suc (suc (suc (suc (suc M2)))))
      (suc (suc (suc (suc (suc M3)))))
      (suc (suc (suc (suc (suc M4)))))
      (suc (suc (suc (suc (suc M5)))))
      (suc (suc (suc (suc (suc M6)))))
      (suc (suc (suc (suc (suc M7)))))
      (suc (suc (suc (suc (suc M8)))))
      (suc (suc (suc (suc (suc M9)))))
      (suc (suc (suc (suc (suc M10)))))
      (suc (suc (suc (suc (suc M11)))))
      (suc (suc (suc (suc (suc s0)))))
      (suc (suc (suc (suc (suc s1))))))
    zero (suc (suc zero)) (suc (suc (suc zero)))

  -- The bounded matrix: exists w in K (graph w gamma K and v = w).
  levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
  levelHoodB =
    ∃̇∈ (var (suc (suc (suc zero))))
      (G.graphBndAt ∧̇ (var (suc zero) ≐ var zero))

  Δ₀-levelHoodB : Δ₀ levelHoodB
  Δ₀-levelHoodB =
    δ-∃∈ (δ-∧ (G.Δ₀-graphBndAt (Δ₀-DefBodyB (suc zero)
              (suc (suc (suc (suc zero))))
              (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
              (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
              (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
              (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
              (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
              (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11)))))
              (suc (suc (suc (suc (suc t0))))) (suc (suc (suc (suc (suc t1))))))
            (Δ₀-DefBodyB (suc zero) (suc (suc (suc (suc zero))))
              (suc (suc (suc (suc (suc M0)))))
              (suc (suc (suc (suc (suc M1)))))
              (suc (suc (suc (suc (suc M2)))))
              (suc (suc (suc (suc (suc M3)))))
              (suc (suc (suc (suc (suc M4)))))
              (suc (suc (suc (suc (suc M5)))))
              (suc (suc (suc (suc (suc M6)))))
              (suc (suc (suc (suc (suc M7)))))
              (suc (suc (suc (suc (suc M8)))))
              (suc (suc (suc (suc (suc M9)))))
              (suc (suc (suc (suc (suc M10)))))
              (suc (suc (suc (suc (suc M11)))))
              (suc (suc (suc (suc (suc s0)))))
              (suc (suc (suc (suc (suc s1)))))))
      δ-≐)

  -- The Sigma-1 form: the unbounded witness over the bounded matrix.
  levelHoodΣ₁ : Formula CS.S (suc (suc (suc n)))
  levelHoodΣ₁ = ∃̇ levelHoodB

  Σ₁-levelHood : Σ₁ levelHoodΣ₁
  Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)

-- =====================================================================
-- SECTION 2: THE SATISFACTION ISO-INVARIANCE UNDER THE COLLAPSE.
-- =====================================================================

module IsoInv (M : S) (PM : S)
  (p : S → S)
  (p∈ : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ p x ∈ˢ PM ⟩)
  (iso-fwd : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
           → ⟨ y ∈ˢ x ⟩ → ⟨ p y ∈ˢ p x ⟩)
  (iso-bwd : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
           → ⟨ p y ∈ˢ p x ⟩ → ⟨ y ∈ˢ x ⟩)
  (p-inj : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
          → p x ≡ p y → x ≡ y)
  (surj : (z : S) (z∈ : ⟨ z ∈ˢ PM ⟩)
        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (p y ≡ z)) ∥₁)
  where

  SM : Type (ℓ-suc ℓ)
  SM = Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩

  SPM : Type (ℓ-suc ℓ)
  SPM = Σ[ x ∈ S ] ⟨ x ∈ˢ PM ⟩

  g : SM → SPM
  g m = p (fst m) , p∈ (fst m) (snd m)

  module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ M))
  module SemPM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ PM))
  open module Mse = SemM.At SM id public renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )
  open module Pse = SemPM.At SPM id public renaming ( _⊨_ to _⊨ᵖᵐ_ ; ⟦_⟧ to ⟦_⟧ᵖᵐ )

  surj' : (p' : SPM) → ∥ Σ[ q ∈ SM ] (g q ≡ p') ∥₁
  surj' (z , z∈) = PT.map (λ { (y , y∈ , e) →
    (y , y∈) , Σ≡Prop (λ w → (w ∈ˢ PM) .snd) e }) (surj z z∈)

  private
    lookup-g : {n : ℕ} (i : Fin n) (δ : SM ^ n)
             → p (fst (lookup i δ)) ≡ fst (lookup i (map g δ))
    lookup-g zero (m ∷ δ) = refl
    lookup-g (suc i) (m ∷ δ) = lookup-g i δ

    tm-agree : {n : ℕ} (t : Term SM n) (δ : SM ^ n)
             → p (fst (⟦ t ⟧ᵐ δ)) ≡ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ))
    tm-agree (con m) δ = refl
    tm-agree (var i) δ = lookup-g i δ

  mutual
    iso-inv : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
            → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩
    iso-inv n (t ∈̇ u) δ h =
      subst (λ z → ⟨ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ∈ˢ z ⟩)
            (tm-agree u δ)
        (subst (λ z → ⟨ z ∈ˢ p (fst (⟦ u ⟧ᵐ δ)) ⟩) (tm-agree t δ)
          (iso-fwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
            (snd (⟦ t ⟧ᵐ δ)) h))
    iso-inv n (t ≐ u) δ h =
      subst (λ z → z ≡ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ))) (tm-agree t δ)
        (subst (λ z → p (fst (⟦ t ⟧ᵐ δ)) ≡ z) (tm-agree u δ) (cong p h))
    iso-inv n (φ ∧̇ ψ) δ h = iso-inv n φ δ (h .fst) , iso-inv n ψ δ (h .snd)
    iso-inv n (φ ∨̇ ψ) δ h =
      PT.map (λ { (inl hφ) → inl (iso-inv n φ δ hφ)
                ; (inr hψ) → inr (iso-inv n ψ δ hψ) }) h
    iso-inv n (φ ⇒̇ ψ) δ h h' =
      iso-inv n ψ δ (h (iso-inv-bwd n φ δ h'))
    iso-inv n (¬̇ φ) δ h h' = h (iso-inv-bwd n φ δ h')
    iso-inv n ⊤̇ δ _ = tt*
    iso-inv n ⊥̇ δ ()
    iso-inv n (∃̇ ψ) δ h =
      PT.rec (snd (map g δ ⊨ᵖᵐ mapFo g (∃̇ ψ))) go h
      where
      go : Σ[ q ∈ SM ] ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩
         → ⟨ map g δ ⊨ᵖᵐ mapFo g (∃̇ ψ) ⟩
      go (q , hq) = ∣ g q , iso-inv (suc n) ψ (q ∷ δ) hq ∣₁
    iso-inv n (∀̇ ψ) δ h =
      λ p' → PT.rec (snd ((p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ))
        (λ { (q , gq≡p) →
          subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩) (cong (λ z → z ∷ map g δ) gq≡p)
            (iso-inv (suc n) ψ (q ∷ δ) (h q)) })
        (surj' p')
    iso-inv n (∀̇∈ t ψ) δ h =
      λ p' p∈t → PT.rec (snd ((p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ))
        (λ { (q , gq≡p) →
          let p∈gx : ⟨ fst p' ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx = subst (λ z → ⟨ fst p' ∈ˢ z ⟩) (sym (tm-agree t δ)) p∈t
              p∈gx' : ⟨ fst (g q) ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx' = subst (λ z → ⟨ z ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩)
                        (sym (cong fst gq≡p)) p∈gx
              q∈t : ⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩
              q∈t = iso-bwd (fst (⟦ t ⟧ᵐ δ)) (fst q)
                      (snd (⟦ t ⟧ᵐ δ)) (snd q) p∈gx'
              hψ : ⟨ (g q ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩
              hψ = iso-inv (suc n) ψ (q ∷ δ) (h q q∈t)
          in subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩)
               (cong (λ z → z ∷ map g δ) gq≡p) hψ })
        (surj' p')
    iso-inv n (∃̇∈ t ψ) δ h =
      PT.map (λ { (q , q∈t , hψ) →
        g q ,
        ( subst (λ z → ⟨ p (fst q) ∈ˢ z ⟩) (tm-agree t δ)
            (iso-fwd (fst (⟦ t ⟧ᵐ δ)) (fst q) (snd (⟦ t ⟧ᵐ δ)) (snd q) q∈t)
        , iso-inv (suc n) ψ (q ∷ δ) hψ ) }) h

    iso-inv-bwd : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
                → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
    iso-inv-bwd n (t ∈̇ u) δ h =
      iso-bwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
        (snd (⟦ t ⟧ᵐ δ))
        (subst (λ z → ⟨ p (fst (⟦ t ⟧ᵐ δ)) ∈ˢ z ⟩) (sym (tm-agree u δ))
          (subst (λ z → ⟨ z ∈ˢ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ)) ⟩)
            (sym (tm-agree t δ)) h))
    iso-inv-bwd n (t ≐ u) δ h =
      p-inj (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ)) (snd (⟦ t ⟧ᵐ δ))
        (snd (⟦ u ⟧ᵐ δ))
        (subst (λ z → z ≡ p (fst (⟦ u ⟧ᵐ δ))) (sym (tm-agree t δ))
          (subst (λ z → fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ≡ z)
            (sym (tm-agree u δ)) h))
    iso-inv-bwd n (φ ∧̇ ψ) δ h =
      iso-inv-bwd n φ δ (h .fst) , iso-inv-bwd n ψ δ (h .snd)
    iso-inv-bwd n (φ ∨̇ ψ) δ h =
      PT.map (λ { (inl hφ) → inl (iso-inv-bwd n φ δ hφ)
                ; (inr hψ) → inr (iso-inv-bwd n ψ δ hψ) }) h
    iso-inv-bwd n (φ ⇒̇ ψ) δ h h' =
      iso-inv-bwd n ψ δ (h (iso-inv n φ δ h'))
    iso-inv-bwd n (¬̇ φ) δ h h' = h (iso-inv n φ δ h')
    iso-inv-bwd n ⊤̇ δ _ = tt*
    iso-inv-bwd n ⊥̇ δ ()
    iso-inv-bwd n (∃̇ ψ) δ h =
      PT.rec (snd (δ ⊨ᵐ (∃̇ ψ))) go h
      where
      go : Σ[ p' ∈ SPM ] ⟨ (p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩
         → ⟨ δ ⊨ᵐ (∃̇ ψ) ⟩
      go (p' , hp) = PT.rec (snd (δ ⊨ᵐ (∃̇ ψ))) go₂ (surj' p')
        where
        go₂ : Σ[ q ∈ SM ] (g q ≡ p') → ⟨ δ ⊨ᵐ (∃̇ ψ) ⟩
        go₂ (q , gq≡p) =
          ∣ q , iso-inv-bwd (suc n) ψ (q ∷ δ)
                (subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩)
                  (sym (cong (λ z → z ∷ map g δ) gq≡p)) hp) ∣₁
    iso-inv-bwd n (∀̇ ψ) δ h =
      λ q → iso-inv-bwd (suc n) ψ (q ∷ δ) (h (g q))
    iso-inv-bwd n (∀̇∈ t ψ) δ h =
      λ q q∈t →
        iso-inv-bwd (suc n) ψ (q ∷ δ)
          (h (g q)
            (subst (λ z → ⟨ p (fst q) ∈ˢ z ⟩) (tm-agree t δ)
              (iso-fwd (fst (⟦ t ⟧ᵐ δ)) (fst q)
                (snd (⟦ t ⟧ᵐ δ)) (snd q) q∈t)))
    iso-inv-bwd n (∃̇∈ t ψ) δ h =
      PT.rec (snd (δ ⊨ᵐ (∃̇∈ t ψ))) go h
      where
      go : Σ[ p' ∈ SPM ]
             (⟨ fst p' ∈ˢ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ⟩
            × ⟨ (p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩)
         → ⟨ δ ⊨ᵐ (∃̇∈ t ψ) ⟩
      go (p' , p∈t , hp) = PT.rec (snd (δ ⊨ᵐ (∃̇∈ t ψ))) go₂ (surj' p')
        where
        go₂ : Σ[ q ∈ SM ] (g q ≡ p') → ⟨ δ ⊨ᵐ (∃̇∈ t ψ) ⟩
        go₂ (q , gq≡p) =
          let p∈gx : ⟨ fst p' ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx = subst (λ z → ⟨ fst p' ∈ˢ z ⟩) (sym (tm-agree t δ)) p∈t
              p∈gx' : ⟨ fst (g q) ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx' = subst (λ z → ⟨ z ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩)
                        (sym (cong fst gq≡p)) p∈gx
              q∈t : ⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩
              q∈t = iso-bwd (fst (⟦ t ⟧ᵐ δ)) (fst q)
                      (snd (⟦ t ⟧ᵐ δ)) (snd q) p∈gx'
              hψ : ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩
              hψ = iso-inv-bwd (suc n) ψ (q ∷ δ)
                      (subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩)
                        (sym (cong (λ z → z ∷ map g δ) gq≡p)) hp)
          in ∣ q , q∈t , hψ ∣₁

-- The collapse instance: M = the carrier X, PM = the collapse image piX.
module CollapseIso (X : S) (Xext : isExt X) where
  module C = Collapse X
  module CI = C.InjExt Xext

  PM : S
  PM = C.πX

  p : S → S
  p = C.π

  p∈ : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ p x ∈ˢ PM ⟩
  p∈ = C.πX-intro

  iso-fwd : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
          → ⟨ y ∈ˢ x ⟩ → ⟨ p y ∈ˢ p x ⟩
  iso-fwd x y x∈ y∈ = CI.iso x y x∈ y∈ .fst

  iso-bwd : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
          → ⟨ p y ∈ˢ p x ⟩ → ⟨ y ∈ˢ x ⟩
  iso-bwd x y x∈ y∈ = CI.iso x y x∈ y∈ .snd

  p-inj : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
        → p x ≡ p y → x ≡ y
  p-inj = CI.π-inj

  surj : (z : S) (z∈ : ⟨ z ∈ˢ PM ⟩)
       → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (p y ≡ z)) ∥₁
  surj = C.πX-member

  module I = IsoInv X PM p p∈ iso-fwd iso-bwd p-inj surj

-- =====================================================================
-- SECTION 3: THE DOWN-REFLECTION AT M THROUGH hull-closed.
-- =====================================================================

module DownReflect (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα
  module H = ASt.Hull X X⊆L ∅∈α

  SM : Type (ℓ-suc ℓ)
  SM = Σ[ x ∈ S ] ⟨ x ∈ˢ H.T.Hull ⟩

  module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ))
                  (𝒮ᵥ ↾ (λ x → x ∈ˢ H.T.Hull))
  open module Mse = SemM.At SM id public renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )

  inL : SM → ASt.SL
  inL c = fst c , H.Hull⊆L (fst c) (snd c)

  codeValM : H.T.Code → SM
  codeValM c = fst (H.T.val c) , H.val-in-Hull c

  inL∘codeValM : H.T.Code → ASt.SL
  inL∘codeValM c = inL (codeValM c)

  inL∘codeValM≡val : (c : H.T.Code) → inL∘codeValM c ≡ H.T.val c
  inL∘codeValM≡val c =
    cong₂ _,_ refl ((fst (H.T.val c) ∈ˢ Lset α) .snd _ _)

  mapTm-ext : {n : ℕ} (t : Term H.T.Code n)
            → mapTm inL∘codeValM t ≡ mapTm H.T.val t
  mapTm-ext (con c) = cong con (inL∘codeValM≡val c)
  mapTm-ext (var i) = refl

  mapFo-ext : {n : ℕ} (φ : Formula H.T.Code n)
            → mapFo inL∘codeValM φ ≡ mapFo H.T.val φ
  mapFo-ext (t ∈̇ u)  = cong₂ _∈̇_ (mapTm-ext t) (mapTm-ext u)
  mapFo-ext (t ≐ u)  = cong₂ _≐_ (mapTm-ext t) (mapTm-ext u)
  mapFo-ext (φ ∧̇ ψ)  = cong₂ _∧̇_ (mapFo-ext φ) (mapFo-ext ψ)
  mapFo-ext (φ ∨̇ ψ)  = cong₂ _∨̇_ (mapFo-ext φ) (mapFo-ext ψ)
  mapFo-ext (φ ⇒̇ ψ)  = cong₂ _⇒̇_ (mapFo-ext φ) (mapFo-ext ψ)
  mapFo-ext (¬̇ φ)    = cong ¬̇_ (mapFo-ext φ)
  mapFo-ext ⊤̇        = refl
  mapFo-ext ⊥̇        = refl
  mapFo-ext (∃̇ φ)    = cong ∃̇_ (mapFo-ext φ)
  mapFo-ext (∀̇ φ)    = cong ∀̇_ (mapFo-ext φ)
  mapFo-ext (∀̇∈ t φ) = cong₂ ∀̇∈ (mapTm-ext t) (mapFo-ext φ)
  mapFo-ext (∃̇∈ t φ) = cong₂ ∃̇∈ (mapTm-ext t) (mapFo-ext φ)

  qOf : (a : ASt.SL) → ⟨ fst a ∈ˢ H.T.Hull ⟩ → SM
  qOf a a∈H = fst a , a∈H

  env-eq : (a : ASt.SL) (a∈H : ⟨ fst a ∈ˢ H.T.Hull ⟩)
         → map inL (qOf a a∈H ∷ []) ≡ a ∷ []
  env-eq a a∈H =
    cong₂ _∷_ (Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) refl) refl

  ElemDown : Type (ℓ-suc ℓ)
  ElemDown = (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
           → ⟨ map inL δ ASt.AbsL.⊨ᵐ (mapFo inL φ) ⟩ → ⟨ δ ⊨ᵐ φ ⟩

  module _ (ed : ElemDown) where

    env-trans : (φ : Formula H.T.Code 1) (a : ASt.SL) (a∈H : ⟨ fst a ∈ˢ H.T.Hull ⟩)
              → ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val φ) ⟩
              → ⟨ map inL (qOf a a∈H ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val φ) ⟩
    env-trans φ a a∈H = transport
      (cong (λ e → ⟨ e ASt.AbsL.⊨ᵐ (mapFo H.T.val φ) ⟩) (sym (env-eq a a∈H)))

    form-trans : (φ : Formula H.T.Code 1) (a : ASt.SL) (a∈H : ⟨ fst a ∈ˢ H.T.Hull ⟩)
               → ⟨ map inL (qOf a a∈H ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val φ) ⟩
               → ⟨ map inL (qOf a a∈H ∷ []) ASt.AbsL.⊨ᵐ (mapFo (inL∘codeValM) φ) ⟩
    form-trans φ a a∈H = transport
      (sym (cong (λ ψ → ⟨ map inL (qOf a a∈H ∷ []) ASt.AbsL.⊨ᵐ ψ ⟩) (mapFo-ext φ)))

    form-trans₂ : (φ : Formula H.T.Code 1) (a : ASt.SL) (a∈H : ⟨ fst a ∈ˢ H.T.Hull ⟩)
                → ⟨ map inL (qOf a a∈H ∷ []) ASt.AbsL.⊨ᵐ (mapFo (inL∘codeValM) φ) ⟩
                → ⟨ map inL (qOf a a∈H ∷ []) ASt.AbsL.⊨ᵐ
                      (mapFo inL (mapFo codeValM φ)) ⟩
    form-trans₂ φ a a∈H = transport
      (sym (cong (λ ψ → ⟨ map inL (qOf a a∈H ∷ []) ASt.AbsL.⊨ᵐ ψ ⟩)
        (mapFo-comp codeValM inL φ)))

    bridge : (φ : Formula H.T.Code 1) (a : ASt.SL) (a∈H : ⟨ fst a ∈ˢ H.T.Hull ⟩)
           → ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val φ) ⟩
           → ⟨ (qOf a a∈H ∷ []) ⊨ᵐ (mapFo codeValM φ) ⟩
    bridge φ a a∈H ha =
      ed 1 (mapFo codeValM φ) (qOf a a∈H ∷ [])
        (form-trans₂ φ a a∈H (form-trans φ a a∈H (env-trans φ a a∈H ha)))

    down-reflect : (φ : Formula H.T.Code 1)
                 → ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val φ)) ⟩
                 → ∥ Σ[ q ∈ SM ] ⟨ (q ∷ []) ⊨ᵐ (mapFo codeValM φ) ⟩ ∥₁
    down-reflect φ h = PT.rec squash₁ go (H.hull-closed φ h)
      where
      go : Σ[ a ∈ ASt.SL ] (⟨ fst a ∈ˢ H.T.Hull ⟩
                          × ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val φ) ⟩)
         → ∥ Σ[ q ∈ SM ] ⟨ (q ∷ []) ⊨ᵐ (mapFo codeValM φ) ⟩ ∥₁
      go (a , a∈H , ha) = ∣ qOf a a∈H , bridge φ a a∈H ha ∣₁

-- =====================================================================
-- WALL 2, PLACED ([LJ-1.53] probe A).  The parameter-to-code
-- relabelling inside TV/ElemDown.  The canonical code of each hull
-- member (the CodeSelect least-of pattern, over the ordinal's own
-- well-order and the code count), the generic close operation that
-- replaces the top parameters by their codes as constants, its
-- satisfaction adequacy, and the TarskiVaught instance at every arity
-- assembled from hull-closed through the two halves.  AtM.TV-thm
-- turns the instance into Elementary, hence ElemDown.
-- =====================================================================
module CanonCode (α : S) (oα : IsOrd α) (w : SWO {ℓ} ⟪ α ⟫)
  (M : S) (Code : Type ℓ) (val : Code → S)
  (mem-code : (x : S) → ⟨ x ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (val c ≡ x) ∥₁)
  (cnt : Code → ⟪ α ⟫) (cnt-inj : (c d : Code) → cnt c ≡ cnt d → c ≡ d) where

  cls : ⟪ M ⟫ → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  cls m y = ( ∥ Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ y)) ∥₁
            , squash₁ )

  nonempty : (m : ⟪ M ⟫) → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ cls m y ⟩ ∥₁
  nonempty m = PT.map (λ { (c , e) → cnt c , ∣ c , (e , refl) ∣₁ })
                      (mem-code (⟪ M ⟫↪ m) (member M m))

  isSet⟪α⟫ : isSet ⟪ α ⟫
  isSet⟪α⟫ = Embedding-into-isSet→isSet (⟪ α ⟫↪ , isEmb⟪ α ⟫↪) isSetS

  least : (m : ⟪ M ⟫) → ⟪ α ⟫
  least m = fst (leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m))

  least-wit : (m : ⟪ M ⟫)
            → ∥ Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ least m)) ∥₁
  least-wit m = fst (snd (leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m)))

  isPropFib : (m : ⟪ M ⟫)
            → isProp (Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m)
                                   × (cnt c ≡ least m)))
  isPropFib m (c , e , p) (d , e' , p') =
    Σ≡Prop (λ c → isProp× (isSetS (val c) (⟪ M ⟫↪ m))
                            (isSet⟪α⟫ (cnt c) (least m)))
      (cnt-inj c d (p ∙ sym p'))

  canonical : ⟪ M ⟫ → Code
  canonical m = fst (PT.rec (isPropFib m) (λ w → w) (least-wit m))

  canonical-spec : (m : ⟪ M ⟫) → val (canonical m) ≡ ⟪ M ⟫↪ m
  canonical-spec m = fst (snd (PT.rec (isPropFib m) (λ w → w) (least-wit m)))

-- The generic close operation (syntax): a formula of arity d + n has
-- its top n variables replaced by the constants δ, the
-- parameter-as-constant spelling.  The first d variables (the binders
-- already crossed) stay variables.  Both consumers are one recursion:
-- close keeps the witness variable free (d = 1), closeAll closes every
-- top variable (d = 0).
module CloseSyntax where

  closeTmAt : {K : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
            → Term K (d + n) → Term K d
  closeTmAt d n δ (con c) = con c
  closeTmAt zero zero δ (var ())
  closeTmAt zero (suc n) δ (var zero) = con (lookup zero δ)
  closeTmAt zero (suc n) δ (var (suc i)) = con (lookup (suc i) δ)
  closeTmAt (suc d) n δ (var zero) = var zero
  closeTmAt (suc d) n δ (var (suc j)) =
    renameTm suc (closeTmAt d n δ (var j))

  closeAt : {K : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
          → Formula K (d + n) → Formula K d
  closeAt d n δ (t ∈̇ u) = closeTmAt d n δ t ∈̇ closeTmAt d n δ u
  closeAt d n δ (t ≐ u) = closeTmAt d n δ t ≐ closeTmAt d n δ u
  closeAt d n δ (φ ∧̇ ψ) = closeAt d n δ φ ∧̇ closeAt d n δ ψ
  closeAt d n δ (φ ∨̇ ψ) = closeAt d n δ φ ∨̇ closeAt d n δ ψ
  closeAt d n δ (φ ⇒̇ ψ) = closeAt d n δ φ ⇒̇ closeAt d n δ ψ
  closeAt d n δ (¬̇ φ) = ¬̇ closeAt d n δ φ
  closeAt d n δ ⊤̇ = ⊤̇
  closeAt d n δ ⊥̇ = ⊥̇
  closeAt d n δ (∃̇ ψ) = ∃̇ (closeAt (suc d) n δ ψ)
  closeAt d n δ (∀̇ ψ) = ∀̇ (closeAt (suc d) n δ ψ)
  closeAt d n δ (∀̇∈ t ψ) = ∀̇∈ (closeTmAt d n δ t) (closeAt (suc d) n δ ψ)
  closeAt d n δ (∃̇∈ t ψ) = ∃̇∈ (closeTmAt d n δ t) (closeAt (suc d) n δ ψ)

  -- the closure of the parameter block and the witness variable
  close : {K : Type (ℓ-suc ℓ)} (n : ℕ) (δ : Vec K n)
        → (φ : Formula K (suc n)) → Formula K 1
  close n δ φ = closeAt 1 n δ φ

  -- the full closure (no witness variable left)
  closeAll : {K : Type (ℓ-suc ℓ)} (n : ℕ) (δ : Vec K n)
           → (φ : Formula K n) → Formula K 0
  closeAll n δ φ = closeAt 0 n δ φ

  -- relabelling and closure commute: closing after relabelling is
  -- relabelling after closing
  mapTm-rename : {K K' : Type (ℓ-suc ℓ)} {n m : ℕ} (g : K → K')
               → (ρ : Fin n → Fin m) (t : Term K n)
               → mapTm g (renameTm ρ t) ≡ renameTm ρ (mapTm g t)
  mapTm-rename g ρ (con c) = refl
  mapTm-rename g ρ (var j) = refl

  mapTm-close : {K K' : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
              → (g : K → K') (t : Term K (d + n))
              → mapTm g (closeTmAt d n δ t)
                ≡ closeTmAt d n (map g δ) (mapTm g t)
  mapTm-close d n δ g (con c) = refl
  mapTm-close zero zero δ g (var ())
  mapTm-close zero (suc n) δ g (var zero) =
    cong con (sym (lookup-map g δ zero))
  mapTm-close zero (suc n) δ g (var (suc i)) =
    cong con (sym (lookup-map g δ (suc i)))
  mapTm-close (suc d) n δ g (var zero) = refl
  mapTm-close (suc d) n δ g (var (suc j)) =
    mapTm-rename g suc (closeTmAt d n δ (var j))
    ∙ cong (renameTm suc) (mapTm-close d n δ g (var j))

  mapFo-close : {K K' : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
              → (g : K → K') (φ : Formula K (d + n))
              → mapFo g (closeAt d n δ φ)
                ≡ closeAt d n (map g δ) (mapFo g φ)
  mapFo-close d n δ g (t ∈̇ u) = cong₂ _∈̇_
    (mapTm-close d n δ g t) (mapTm-close d n δ g u)
  mapFo-close d n δ g (t ≐ u) = cong₂ _≐_
    (mapTm-close d n δ g t) (mapTm-close d n δ g u)
  mapFo-close d n δ g (φ ∧̇ ψ) = cong₂ _∧̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (φ ∨̇ ψ) = cong₂ _∨̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (φ ⇒̇ ψ) = cong₂ _⇒̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (¬̇ φ) = cong ¬̇_ (mapFo-close d n δ g φ)
  mapFo-close d n δ g ⊤̇ = refl
  mapFo-close d n δ g ⊥̇ = refl
  mapFo-close d n δ g (∃̇ ψ) = cong ∃̇_ (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∀̇ ψ) = cong ∀̇_ (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∀̇∈ t ψ) = cong₂ ∀̇∈
    (mapTm-close d n δ g t) (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∃̇∈ t ψ) = cong₂ ∃̇∈
    (mapTm-close d n δ g t) (mapFo-close (suc d) n δ g ψ)

-- The adequacy of the close operation (semantics): the original
-- formula at the environment γ ++ map ι δ is the closed formula at γ.
module CloseSem {𝒮 : ZFStructure (hPropAlgebra (ℓ-suc ℓ))}
                {K : Type (ℓ-suc ℓ)} (ι : K → ZFStructure.S 𝒮) where

  open ZFStructure 𝒮 renaming ( _∈ˢ_ to _∈ˢ𝒮_ ; _≈ˢ_ to _≈ˢ𝒮_ )
  module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮
  open Sem.At K ι using ( _⊨_; ⟦_⟧ )
  module Cl = CloseSyntax

  map-id : {ℓ'' : Level} {A : Type ℓ''} {n : ℕ} (v : Vec A n)
         → map (λ x → x) v ≡ v
  map-id [] = refl
  map-id (x ∷ v) = cong (x ∷_) (map-id v)

  -- a term lifted past a binder reads the tail of the environment
  renameTm-suc-sat : {d : ℕ} (X : Term K d) (y : ZFStructure.S 𝒮)
                   (γ : Sem._^_ (ZFStructure.S 𝒮) d)
                   → ⟦ renameTm suc X ⟧ (y ∷ γ) ≡ ⟦ X ⟧ γ
  renameTm-suc-sat (con c) y γ = refl
  renameTm-suc-sat (var i) y γ = refl

  -- the term-level adequacy: every clause is lookup-map or the
  -- induction hypothesis, and the kept variables are refl
  ⟦⟧-close : (d n : ℕ) (t : Term K (d + n)) (δ : Vec K n)
           (γ : Sem._^_ (ZFStructure.S 𝒮) d)
           → ⟦ t ⟧ (γ ++ map ι δ) ≡ ⟦ Cl.closeTmAt d n δ t ⟧ γ
  ⟦⟧-close d n (con c) δ γ = refl
  ⟦⟧-close zero zero (var ()) δ γ
  ⟦⟧-close zero (suc n) (var zero) δ [] = lookup-map ι δ zero
  ⟦⟧-close zero (suc n) (var (suc i)) δ [] = lookup-map ι δ (suc i)
  ⟦⟧-close (suc d) n (var zero) δ (y ∷ γ) = refl
  ⟦⟧-close (suc d) n (var (suc j)) δ (y ∷ γ) =
    ⟦⟧-close d n (var j) δ γ
    ∙ sym (renameTm-suc-sat (Cl.closeTmAt d n δ (var j)) y γ)

  -- the formula-level adequacy: the fourteen clauses of the semantics,
  -- each a congruence, the binders pushing a value onto the env
  ⊨-close : (d n : ℕ) (φ : Formula K (d + n)) (δ : Vec K n)
          (γ : Sem._^_ (ZFStructure.S 𝒮) d)
          → (γ ++ map ι δ) ⊨ φ ≡ γ ⊨ Cl.closeAt d n δ φ
  ⊨-close d n (t ∈̇ u) δ γ = cong₂ _∈ˢ𝒮_
    (⟦⟧-close d n t δ γ) (⟦⟧-close d n u δ γ)
  ⊨-close d n (t ≐ u) δ γ = cong₂ _≈ˢ𝒮_
    (⟦⟧-close d n t δ γ) (⟦⟧-close d n u δ γ)
  ⊨-close d n (φ ∧̇ ψ) δ γ = cong₂ _⊓_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (φ ∨̇ ψ) δ γ = cong₂ _⊔_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (φ ⇒̇ ψ) δ γ = cong₂ _⇒_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (¬̇ φ) δ γ = cong ¬_ (⊨-close d n φ δ γ)
  ⊨-close d n ⊤̇ δ γ = refl
  ⊨-close d n ⊥̇ δ γ = refl
  ⊨-close d n (∃̇ ψ) δ γ = cong (⋁ (ZFStructure.S 𝒮)) (funExt (λ x →
    ⊨-close (suc d) n ψ δ (x ∷ γ)))
  ⊨-close d n (∀̇ ψ) δ γ = cong (⋀ (ZFStructure.S 𝒮)) (funExt (λ x →
    ⊨-close (suc d) n ψ δ (x ∷ γ)))
  ⊨-close d n (∀̇∈ t ψ) δ γ = cong (⋀ (ZFStructure.S 𝒮)) (funExt (λ x →
    cong₂ _⇒_ (cong (x ∈ˢ𝒮_) (⟦⟧-close d n t δ γ))
      (⊨-close (suc d) n ψ δ (x ∷ γ))))
  ⊨-close d n (∃̇∈ t ψ) δ γ = cong (⋁ (ZFStructure.S 𝒮)) (funExt (λ x →
    cong₂ _⊓_ (cong (x ∈ˢ𝒮_) (⟦⟧-close d n t δ γ))
      (⊨-close (suc d) n ψ δ (x ∷ γ))))

  ⊨-close₁ : (n : ℕ) (φ : Formula K (suc n)) (δ : Vec K n) (x : ZFStructure.S 𝒮)
           → (x ∷ map ι δ) ⊨ φ ≡ (x ∷ []) ⊨ Cl.close n δ φ
  ⊨-close₁ n φ δ x = ⊨-close 1 n φ δ (x ∷ [])

  ⊨-closeAll : (n : ℕ) (φ : Formula K n) (δ : Vec K n)
             → map ι δ ⊨ φ ≡ [] ⊨ Cl.closeAll n δ φ
  ⊨-closeAll n φ δ = ⊨-close 0 n φ δ []

-- The hull instance: f is the canonical code of each hull member
-- (CanonCode at the consumer's count), and the module proves the
-- relabelling transfer, the TarskiVaught instance at every arity, and
-- ElemDown.
module HullElemDown (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα
  module H = ASt.Hull X X⊆L ∅∈α
  M : S
  M = H.T.Hull
  module A = ASt.AtM M H.Hull⊆L
  module Mse = A.SemM.At A.SM id

  module Cl = CloseSyntax
  module CseM = CloseSem {𝒮 = 𝒮ᵥ ↾ (λ x → x ∈ˢ M)} {K = A.SM} id
  module CseL = CloseSem {𝒮 = 𝒮ᵥ ↾ (λ x → x ∈ˢ Lset α)} {K = ASt.SL} id

  module WithCode (f : A.SM → H.T.Code)
    (f-spec : (q : A.SM) → fst (H.T.val (f q)) ≡ fst q) where

    -- val ∘ f and inL agree pointwise, so the relabelling preserves the
    -- formula up to the interpretation
    val∘f≡inL : (q : A.SM) → H.T.val (f q) ≡ A.inL q
    val∘f≡inL q = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) (f-spec q)

    rel : {n : ℕ} (φ : Formula A.SM n)
        → mapFo H.T.val (mapFo f φ) ≡ mapFo A.inL φ
    rel {n} φ =
      mapFo-comp f H.T.val φ
      ∙ cong (λ g → mapFo g φ) (funExt val∘f≡inL)

    -- TarskiVaught at every arity: the stage existential at the closed
    -- parameters is hull-closed, and the code formula reads back
    -- through the relabelling and the close transfer
    tv : (n : ℕ) (ψ : Formula A.SM (suc n)) (δ : Vec A.SM n)
       → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ)) ⟩
       → ∥ Σ[ q ∈ A.SM ]
            ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
    tv n ψ δ h = PT.rec squash₁ go (H.hull-closed ψ' h')
      where
      ψ' : Formula H.T.Code 1
      ψ' = mapFo f (Cl.close n δ ψ)

      h' : ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val ψ')) ⟩
      h' = subst (λ ψ → ⟨ [] ASt.AbsL.⊨ᵐ ψ ⟩) p
        (subst ⟨_⟩ (CseL.⊨-closeAll n (mapFo A.inL (∃̇ ψ)) (map A.inL δ)) h₁)
        where
        h₁ : fst (map (λ x → x) (map A.inL δ) ASt.AbsL.⊨ᵐ
                (mapFo A.inL (∃̇ ψ)))
        h₁ = subst (λ e → fst (e ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ))))
               (sym (CseL.map-id (map A.inL δ))) h
        p1 : CseL.Cl.closeAll n (map A.inL δ) (mapFo A.inL (∃̇ ψ))
           ≡ FOL.Syntax.∃̇_ (mapFo A.inL (Cl.close n δ ψ))
        p1 = cong FOL.Syntax.∃̇_
               (sym (Cl.mapFo-close 1 n δ A.inL ψ))
        p : CseL.Cl.closeAll n (map A.inL δ) (mapFo A.inL (∃̇ ψ))
          ≡ FOL.Syntax.∃̇_ (mapFo H.T.val ψ')
        p = p1 ∙ cong FOL.Syntax.∃̇_ (sym (rel (Cl.close n δ ψ)))

      go : Σ[ a ∈ ASt.SL ] (⟨ fst a ∈ˢ M ⟩
                          × ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩)
         → ∥ Σ[ q ∈ A.SM ]
              ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
      go (a , a∈H , hsat) = PT.rec squash₁ go₂ (H.hull-member (fst a) a∈H)
        where
        go₂ : Σ[ c ∈ H.T.Code ] (fst (H.T.val c) ≡ fst a)
            → ∥ Σ[ q ∈ A.SM ]
                 ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
        go₂ (c , e) = ∣ q , sat ∣₁
          where
          q : A.SM
          q = fst (H.T.val c) , H.val-in-Hull c
          q≡a : A.inL q ≡ a
          q≡a = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) e
          sat : ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩
          sat = subst (λ e' → ⟨ (A.inL q ∷ e') ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩)
                  (CseL.map-id (map A.inL δ))
                  (subst ⟨_⟩
                    (sym (CseL.⊨-close₁ n (mapFo A.inL ψ) (map A.inL δ) (A.inL q)))
                    sat₁)
            where
            sat₁ : ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ
                       (CseL.Cl.close n (map A.inL δ) (mapFo A.inL ψ)) ⟩
            sat₁ = subst (λ ψ → ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ ψ ⟩)
                     (sym q-path) sat₂
              where
              q-path : CseL.Cl.close n (map A.inL δ) (mapFo A.inL ψ)
                     ≡ mapFo H.T.val ψ'
              q-path = sym (Cl.mapFo-close 1 n δ A.inL ψ)
                       ∙ sym (rel (Cl.close n δ ψ))
              sat₂ : ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩
              sat₂ = subst (λ z → ⟨ (z ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩)
                       (sym q≡a)
                       hsat

    elem : A.Elementary
    elem = A.TV-thm .snd tv

    elem-down : (n : ℕ) (φ : Formula A.SM n) (δ : Vec A.SM n)
              → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ (mapFo A.inL φ) ⟩
              → fst (Mse._⊨_ δ φ)
    elem-down n φ δ h = subst ⟨_⟩ (sym (elem n φ δ)) h

-- The one instance: the level-hood statement at the hull of the stage,
-- with the collapse iso and the elementarity-down residue as the
-- assembly's priced hypotheses.
module AtHullInstance (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩)
  (Xext : isExt X) where

  module CIso = CollapseIso X Xext
  module DR = DownReflect α ordα X X⊆L ∅∈α

  transfer : {n : ℕ} (φ : Formula CIso.I.SM n) (δ : CIso.I.SM ^ n)
           → (⟨ δ CIso.I.⊨ᵐ φ ⟩ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ mapFo CIso.I.g φ ⟩)
          × (⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ mapFo CIso.I.g φ ⟩ → ⟨ δ CIso.I.⊨ᵐ φ ⟩)
  transfer {n} φ δ = CIso.I.iso-inv n φ δ , CIso.I.iso-inv-bwd n φ δ

  reflect : DR.ElemDown
          → (φ : Formula DR.H.T.Code 1)
          → ⟨ [] DR.ASt.AbsL.⊨ᵐ (∃̇ (mapFo DR.H.T.val φ)) ⟩
          → ∥ Σ[ q ∈ DR.SM ] ⟨ (q ∷ []) DR.⊨ᵐ (mapFo DR.codeValM φ) ⟩ ∥₁
  reflect = DR.down-reflect

-- =====================================================================
-- SECTION 4A: THE ORDINAL FORMULA, AND THE LEVEL-HOOD AT n = 0.
-- =====================================================================

-- "x is an ordinal" in the tree's sense: x is transitive and every
-- member of x is transitive.  Parameter-free; the same spelling embeds
-- to every carrier.
isOrdAt : Formula (⊥* {ℓ-suc ℓ}) 1
isOrdAt =
  (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero)))))
  ∧̇ (∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-isOrdAt : Δ₀ isOrdAt
Δ₀-isOrdAt =
  δ-∧ (δ-∀∈ (δ-∀∈ δ-∈))
      (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

-- The ambient reading of the parameter-free formulas: the full
-- hierarchy semantics at the empty constant domain.
module Amb where
  module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
  module AtP = SemV.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b)
  _⊨ₚ_ : {n : ℕ} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
  _⊨ₚ_ = AtP._⊨_

  isOrdAt-out : (x : S) → ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩ → IsOrd x
  isOrdAt-out x h =
      ( λ {x₁} {y} y∈x₁ x₁∈x → h .fst x₁ x₁∈x y y∈x₁ )
    , ( λ a a∈x {x₁} {y} y∈x₁ x₁∈a → h .snd a a∈x x₁ x₁∈a y y∈x₁ )

  isOrdAt-in : (x : S) → IsOrd x → ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩
  isOrdAt-in x o =
      ( λ a a∈x b hb → o .fst {a} {b} hb a∈x )
    , ( λ a a∈x b b∈a c hc → o .snd a a∈x {b} {c} hc b∈a )

-- The erase of a constant-free formula carries the Delta-0 witness:
-- erase is a pure syntactic erasure, so the certificate recurses.
erase-Δ₀ : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0)
         → Δ₀ φ → Δ₀ (Cnt.erase φ p)
erase-Δ₀ (t ∈̇ u) p δ-∈ = δ-∈
erase-Δ₀ (t ≐ u) p δ-≐ = δ-≐
erase-Δ₀ (φ ∧̇ ψ) p (δ-∧ c d) = δ-∧ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ (φ ∨̇ ψ) p (δ-∨ c d) = δ-∨ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ (φ ⇒̇ ψ) p (δ-⇒ c d) = δ-⇒ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ (¬̇ φ) p (δ-¬ c) = δ-¬ (erase-Δ₀ φ p c)
erase-Δ₀ ⊤̇ p δ-⊤ = δ-⊤
erase-Δ₀ ⊥̇ p δ-⊥ = δ-⊥
erase-Δ₀ (∀̇∈ t φ) p (δ-∀∈ c) = δ-∀∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇∈ t φ) p (δ-∃∈ c) = δ-∃∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇ φ) p ()
erase-Δ₀ (∀̇ φ) p ()

module LevelHood0
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin 5)
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin 7) where

  module LH = LevelHood {0} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- The bounded matrix at env w ∷ v ∷ γ ∷ K ∷ [].
  matrix : Formula CS.S 4
  matrix = LH.levelHoodB

  Δ₀-matrix : Δ₀ matrix
  Δ₀-matrix = LH.Δ₀-levelHoodB

  -- The Sigma-1 statement at env γ ∷ []: exists K, v, w in K.
  Σ₂ : Formula CS.S 1
  Σ₂ = ∃̇ (∃̇ (∃̇∈ (var (suc (suc zero))) LH.levelHoodB))

  Σ₁-Σ₂ : Σ₁ Σ₂
  Σ₁-Σ₂ = σ-∃ (σ-∃ (σ-Δ₀ (δ-∃∈ Δ₀-matrix)))

  -- The reverse statement at env y ∷ []: exists K, an ordinal gamma,
  -- v and w in K, with the matrix and y in v.  The matrix and the
  -- ordinal formula are weakened past the accumulating binders.
  reverse : Formula CS.S 1
  reverse =
    ∃̇ (∃̇ ( (renameFo (padRight 2) (embed isOrdAt))
          ∧̇ (∃̇ (∃̇∈ (var (suc (suc zero)))
                ( (renameFo (padRight 1) LH.levelHoodB)
                ∧̇ (var (suc (suc (suc (suc zero)))) ∈̇ var (suc zero)) ))) ))

-- =====================================================================
-- SECTION 4B: THE CONDENSATION THEOREM AT THE HULL INSTANCE.
-- =====================================================================

open import V.Smallness {ℓ} using ( separateFromSmall; module Δ₀Small )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡; rank-Lset )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rank {ℓ} using ( rank-fix )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
import L.StageCardinal
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_,_⁆; ⁅_⁆s; union-ax; pairing-ax
        ; SetPackage; SingletonPackage )  -- lint-agda: keep (SetPackage via record projection)
open InfinitySet using ( ω; sucV )
open import Cubical.Data.Sum using ( _⊎_ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.Foundations.Prelude using ( toPathP; PathP; transportRefl; J )

module D0 = Δ₀Small {ℓc = ℓ-suc ℓ} {K = ⊥* {ℓ-suc ℓ}} (λ b → Empty.rec* b)

-- The hull of X at the stage Lset λ, its collapse, and the condensation
-- theorem at this one instance (D-30: the consumer's shape, not the
-- general theory).  The two transfer hypotheses are Devlin's (h) and
-- (n)-(p): the collapse is closed under the level construction at its
-- own ordinals, and every hull member is covered by a level below the
-- collapse's ordinals.  [LJ-1.48] measured the skeleton around them
-- (elementarity, iso-invariance, the level-hood certificate) at
-- 0.0097 s per line; the level-hood instantiation at the hull is the
-- priced residue.
module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩) (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  module Condense
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁)
    where

    -- beta = the ordinals of the collapse, separated by the Delta-0
    -- ordinal formula.  This is the L-native supremum (ProbeT261's
    -- shape at the transitive carrier).
    β-sep : Σ[ s ∈ S ]
              (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ C.πX) ⊓ ((y ∷ []) Amb.⊨ₚ isOrdAt)))
    β-sep = separateFromSmall C.πX (λ y → (y ∷ []) Amb.⊨ₚ isOrdAt)
              (λ y → D0.Δ₀-small Δ₀-isOrdAt (y ∷ []))

    β : S
    β = β-sep .fst

    β-spec : (y : S) → (y ∈ˢ β) ≡ ((y ∈ˢ C.πX) ⊓ ((y ∷ []) Amb.⊨ₚ isOrdAt))
    β-spec = β-sep .snd

    β∈πX : (δ : S) → ⟨ δ ∈ˢ β ⟩ → ⟨ δ ∈ˢ C.πX ⟩
    β∈πX δ δ∈β = subst ⟨_⟩ (β-spec δ) δ∈β .fst

    β-ord : (δ : S) → ⟨ δ ∈ˢ β ⟩ → IsOrd δ
    β-ord δ δ∈β = Amb.isOrdAt-out δ (subst ⟨_⟩ (β-spec δ) δ∈β .snd)

    ord∈β : (δ : S) → ⟨ δ ∈ˢ C.πX ⟩ → IsOrd δ → ⟨ δ ∈ˢ β ⟩
    ord∈β δ δ∈πX oδ = subst ⟨_⟩ (sym (β-spec δ)) (δ∈πX , Amb.isOrdAt-in δ oδ)

    β-isOrd : IsOrd β
    β-isOrd = β-trans , β-mem
      where
      β-trans : isTransV β
      β-trans {x = x} {y = z} z∈x x∈β =
        subst ⟨_⟩ (sym (β-spec z))
          ( C.πX-trans {x = x} {y = z} z∈x (β∈πX x x∈β)
          , Amb.isOrdAt-in z (mem-ord {A = x} (β-ord x x∈β) z z∈x) )
      β-mem : (x : S) → ⟨ x ∈ˢ β ⟩ → isTransV x
      β-mem x x∈β = β-ord x x∈β .fst

    -- Every ordinal of the collapse is a member of a larger ordinal of
    -- the collapse: the transfer's cover plus the ordinals-in-stages
    -- fact (rank).  This is Devlin's lim(β) step.
    β-succ : (δ : S) → ⟨ δ ∈ˢ β ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
    β-succ δ δ∈β = PT.rec squash₁ go (C.πX-member δ (β∈πX δ δ∈β))
      where
      oδ : IsOrd δ
      oδ = β-ord δ δ∈β
      go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ δ))
         → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
      go (y , y∈M , e) = PT.rec squash₁ go₂ (cover y y∈M)
        where
        go₂ : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩)
            → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
        go₂ (γ , oγ , γ∈πX , h) =
          ∣ γ , ( oγ , δ∈γ , ord∈β γ γ∈πX oγ ) ∣₁
          where
          δ∈Lγ : ⟨ δ ∈ˢ Lset γ ⟩
          δ∈Lγ = subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) e h
          δ∈γ : ⟨ δ ∈ˢ γ ⟩
          δ∈γ = subst (λ w → ⟨ w ∈ˢ γ ⟩) (rank-fix δ oδ)
                  (rank-Lset γ oγ δ δ∈Lγ)

    sucV∈β : (δ : S) → ⟨ δ ∈ˢ β ⟩ → ⟨ sucV δ ∈ˢ β ⟩
    sucV∈β δ δ∈β = PT.rec (snd (sucV δ ∈ˢ β)) go (β-succ δ δ∈β)
      where
      oδ : IsOrd δ
      oδ = β-ord δ δ∈β
      go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩)
         → ⟨ sucV δ ∈ˢ β ⟩
      go (γ , oγ , δ∈γ , γ∈β) = ord∈β (sucV δ) sucV∈πX (suc-ord oδ)
        where
        sucV∈πX : ⟨ sucV δ ∈ˢ C.πX ⟩
        sucV∈πX = Sum.rec
          (λ s∈γ → C.πX-trans {x = γ} {y = sucV δ} s∈γ (β∈πX γ γ∈β))
          (λ s≡γ → subst (λ w → ⟨ w ∈ˢ C.πX ⟩) (sym s≡γ) (β∈πX γ γ∈β))
          (suc∈or≡ δ γ oδ oγ δ∈γ)

    -- The reverse inclusion: every member of the collapse lies in a
    -- level below beta.
    πX⊆Lβ : (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ x ∈ˢ Lset β ⟩
    πX⊆Lβ x x∈πX = PT.rec (snd (x ∈ˢ Lset β)) go (C.πX-member x x∈πX)
      where
      go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ x))
         → ⟨ x ∈ˢ Lset β ⟩
      go (y , y∈M , e) = PT.rec (snd (x ∈ˢ Lset β)) go₂ (cover y y∈M)
        where
        go₂ : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩)
            → ⟨ x ∈ˢ Lset β ⟩
        go₂ (γ , oγ , γ∈πX , h) =
          Lset-mono {α = β} {β = γ} (ord∈β γ γ∈πX oγ)
            (subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) e h)

    -- The forward inclusion: every level below beta lies in the
    -- collapse, via the transfer's levelIn and the successor closure.
    Lβ⊆πX : (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ C.πX ⟩
    Lβ⊆πX x x∈Lβ = PT.rec (snd (x ∈ˢ C.πX)) go (Lset-out β x x∈Lβ)
      where
      go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
         → ⟨ x ∈ˢ C.πX ⟩
      go (δ , δ∈β , x∈𝒟ₒδ) =
        C.πX-trans {x = Lset (sucV δ)} {y = x}
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟ₒδ)
          (levelIn (sucV δ) (suc-ord (β-ord δ δ∈β)) (β∈πX (sucV δ) (sucV∈β δ δ∈β)))

    -- The equality: the collapse is the level at beta.
    ext : C.πX ≡ Lset β
    ext = extensionality C.πX (Lset β) (sub , sup)
      where
      sub : (x : S) → ⟨ x ∈ₛ C.πX ⟩ → ⟨ x ∈ₛ Lset β ⟩
      sub x x∈ₛπX = ∈∈ₛ {a = x} {b = Lset β} .fst
        (πX⊆Lβ x (∈∈ₛ {a = x} {b = C.πX} .snd x∈ₛπX))
      sup : (x : S) → ⟨ x ∈ₛ Lset β ⟩ → ⟨ x ∈ₛ C.πX ⟩
      sup x x∈ₛLβ = ∈∈ₛ {a = x} {b = C.πX} .fst
        (Lβ⊆πX x (∈∈ₛ {a = x} {b = Lset β} .snd x∈ₛLβ))

    condenses : Σ[ γ ∈ S ] (IsOrd γ × (C.πX ≡ Lset γ))
    condenses = β , β-isOrd , ext

-- =====================================================================
-- SECTION 5: DEVLIN 5.5, THE BOUNDED-SUBSET LEMMA.
-- =====================================================================

open import L.Ordinal {ℓ} using ( ω-ord; #∈ω; ∅-ord )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ )

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

IsCardinal : S → Type (ℓ-suc ℓ)
IsCardinal κ = (δ : S) → ⟨ δ ∈ˢ κ ⟩ → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → Empty.⊥)

-- =====================================================================
-- THE INVERSE COLLAPSE, IN TWO GENERIC LEGS (ProbeDD25G3, transplanted).
-- The witness of a collapse value is a member of M, and THAT fibre is a
-- proposition because π is injective on M; only the code fibre is not a
-- proposition, and the least-of-the-class pattern over the ordinal's own
-- well-order (leastOf over L.StageCardinal.OrdSWO.ordSWO) picks a
-- canonical code.  The
-- composite replaces the `collapseCode` hypothesis outright.
-- =====================================================================

module InvColl (M : S) (Mext : isExt M) where
  module C = Collapse M
  module CI = C.InjExt Mext

  Fib : S → Type (ℓ-suc ℓ)
  Fib z = Σ[ m ∈ ⟪ M ⟫ ] (C.π (⟪ M ⟫↪ m) ≡ z)

  isPropFib : (z : S) → isProp (Fib z)
  isPropFib z (m , p) (n , q) = ΣPathP (mn , toPathP (isSetS _ _ _ _))
    where
    ↪mn : ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
    ↪mn = CI.π-inj (⟪ M ⟫↪ m) (⟪ M ⟫↪ n) (member M m) (member M n)
            (p ∙ sym q)
    mn : m ≡ n
    mn = ↪-inj {a = M} ↪mn

  getFib : (z : S) → ⟨ z ∈ˢ C.πX ⟩ → Fib z
  getFib z z∈ = PT.rec (isPropFib z) go (C.πX-member z z∈)
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) → Fib z
    go (y , y∈M , e) =
      fiber M y∈M .fst ,
      cong C.π (fiber M y∈M .snd) ∙ e

  inv : ⟪ C.πX ⟫ → ⟪ M ⟫
  inv p = getFib (⟪ C.πX ⟫↪ p) (member C.πX p) .fst

  inv-inj : (p q : ⟪ C.πX ⟫) → inv p ≡ inv q → p ≡ q
  inv-inj p q e = ↪-inj {a = C.πX} step
    where
    ep : C.π (⟪ M ⟫↪ (inv p)) ≡ ⟪ C.πX ⟫↪ p
    ep = getFib (⟪ C.πX ⟫↪ p) (member C.πX p) .snd
    eq : C.π (⟪ M ⟫↪ (inv q)) ≡ ⟪ C.πX ⟫↪ q
    eq = getFib (⟪ C.πX ⟫↪ q) (member C.πX q) .snd
    step : ⟪ C.πX ⟫↪ p ≡ ⟪ C.πX ⟫↪ q
    step = sym ep ∙ cong (λ m → C.π (⟪ M ⟫↪ m)) e ∙ eq

  leg1 : ⟪ C.πX ⟫ ↪ ⟪ M ⟫
  leg1 = inv , inv-inj

module CodeSelect (α : S) (oα : IsOrd α) (w : SWO {ℓ} ⟪ α ⟫)
  (M : S) (Code : Type ℓ) (val : Code → S)
  (mem-code : (x : S) → ⟨ x ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (val c ≡ x) ∥₁)
  (cnt : Code → ⟪ α ⟫)
  (cnt-inj : (c d : Code) → cnt c ≡ cnt d → c ≡ d)
  where

  cls : ⟪ M ⟫ → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  cls m y = ( ∥ Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ y)) ∥₁
            , squash₁ )

  nonempty : (m : ⟪ M ⟫) → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ cls m y ⟩ ∥₁
  nonempty m = PT.map (λ { (c , e) → cnt c , ∣ c , (e , refl) ∣₁ })
                      (mem-code (⟪ M ⟫↪ m) (member M m))

  h : ⟪ M ⟫ → ⟪ α ⟫
  h m = fst (leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m))

  h-inj : (m n : ⟪ M ⟫) → h m ≡ h n → m ≡ n
  h-inj m n e = ↪-inj {a = M} (go pm)
    where
    lm = leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m)
    ln = leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls n) (nonempty n)
    pm : ⟨ cls m (fst ln) ⟩
    pm = subst (λ y → ⟨ cls m y ⟩) e (fst (snd lm))
    pn : ⟨ cls n (fst ln) ⟩
    pn = fst (snd ln)
    go : ⟨ cls m (fst ln) ⟩ → ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
    go = PT.rec (isSetS (⟪ M ⟫↪ m) (⟪ M ⟫↪ n)) go₁
      where
      go₁ : Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ fst ln))
          → ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
      go₁ (c , (ec , en)) =
        PT.rec (isSetS (⟪ M ⟫↪ m) (⟪ M ⟫↪ n)) go₂ pn
        where
        go₂ : Σ[ d ∈ Code ] ((val d ≡ ⟪ M ⟫↪ n) × (cnt d ≡ fst ln))
            → ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
        go₂ (d , (ed , en')) =
          sym ec ∙ cong val (cnt-inj c d (en ∙ sym en')) ∙ ed

  leg2 : ⟪ M ⟫ ↪ ⟪ α ⟫
  leg2 = h , h-inj

-- The generator Lset α ∪ {x} and its stage facts: x is a member, the
-- generator lies in the stage, the generator is transitive when x is a
-- subset of the stage, and the empty set lies in the limit index.
module UnionKit (α lam x : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (α∈λ : ⟨ α ∈ˢ lam ⟩) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  X : S
  X = Lset α ∪ ⁅ x ⁆s

  -- the union membership of a singleton member
  x∈sgl : ⟨ x ∈ₛ ⁅ x ⁆s ⟩
  x∈sgl = SetPackage.classification (SingletonPackage x) x .snd refl

  x∈X : ⟨ x ∈ˢ X ⟩
  x∈X = ∈∈ₛ {a = x} {b = X} .snd
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ x .snd
      ∣ ⁅ x ⁆s , (pairing-ax (Lset α) (⁅ x ⁆s) (⁅ x ⁆s) .snd ∣ inr refl ∣₁ , x∈sgl) ∣₁)

  Lα∈X : (z : S) → ⟨ z ∈ˢ Lset α ⟩ → ⟨ z ∈ˢ X ⟩
  Lα∈X z z∈Lα = ∈∈ₛ {a = z} {b = X} .snd
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ z .snd
      ∣ Lset α , (pairing-ax (Lset α) (⁅ x ⁆s) (Lset α) .snd ∣ inl refl ∣₁
                , ∈∈ₛ {a = z} {b = Lset α} .fst z∈Lα) ∣₁)

  sgl≡ : (z : S) → ⟨ z ∈ˢ ⁅ x ⁆s ⟩ → z ≡ x
  sgl≡ z z∈sgl = SetPackage.classification (SingletonPackage x) z .fst
    (∈∈ₛ {a = z} {b = ⁅ x ⁆s} .fst z∈sgl)

  X-mem : (z : S) → ⟨ z ∈ˢ X ⟩
        → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
  X-mem z z∈X = PT.rec (snd ((z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s))) go
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ z .fst
      (∈∈ₛ {a = z} {b = X} .fst z∈X))
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ₛ ⁅ Lset α , ⁅ x ⁆s ⁆ ⟩ × ⟨ z ∈ₛ w ⟩)
       → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
    go (w , w∈ₛpair , z∈ₛw) = PT.rec
      (snd ((z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s))) go₂
      (pairing-ax (Lset α) (⁅ x ⁆s) w .fst w∈ₛpair)
      where
      go₂ : (w ≡ Lset α) ⊎ (w ≡ ⁅ x ⁆s)
          → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
      go₂ (inl e) = ∣ inl (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁
      go₂ (inr e) = ∣ inr (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁

  X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  X⊆Lλ z z∈X = PT.rec (snd (z ∈ˢ Lset lam)) go (X-mem z z∈X)
    where
    go : (⟨ z ∈ˢ Lset α ⟩ ⊎ ⟨ z ∈ˢ ⁅ x ⁆s ⟩) → ⟨ z ∈ˢ Lset lam ⟩
    go (inl z∈Lα) = Lset-mono {α = lam} {β = α} α∈λ z∈Lα
    go (inr z∈sgl) = subst (λ u → ⟨ u ∈ˢ Lset lam ⟩) (sym (sgl≡ z z∈sgl)) x∈Lλ

  Xtr : isTransV X
  Xtr {x = a} {y = b} b∈a a∈X = PT.rec (snd (b ∈ˢ X)) go (X-mem a a∈X)
    where
    go : (⟨ a ∈ˢ Lset α ⟩ ⊎ ⟨ a ∈ˢ ⁅ x ⁆s ⟩) → ⟨ b ∈ˢ X ⟩
    go (inl a∈Lα) = Lα∈X b (layer-trans (Lset-layer α) b∈a a∈Lα)
    go (inr a∈sgl) = Lα∈X b (x⊆Lα b
      (subst (λ u → ⟨ b ∈ˢ u ⟩) (sgl≡ a a∈sgl) b∈a))

  -- 1 = sucV ∅ lies in the infinite ordinal alpha, and the empty set
  -- lies in the limit index.
  one∈α : ⟨ sucV ∅ ∈ˢ α ⟩
  one∈α = Sum.rec
      (λ α∈ω → Empty.rec (α∉ω α∈ω))
      (Sum.rec (λ α≡ω → subst (λ w → ⟨ sucV ∅ ∈ˢ w ⟩) (sym α≡ω) (#∈ω 1))
               (λ ω∈α → ordα .fst (#∈ω 1) ω∈α))
      (ord-tri α ordα ω ω-ord)

  ∅∈Lset1 : ⟨ ∅ ∈ˢ Lset (sucV ∅) ⟩
  ∅∈Lset1 = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Lset-suc ∅)) (∅∈𝒟ₒ ∅)

  ∅∈Lλ : ⟨ ∅ ∈ˢ Lset lam ⟩
  ∅∈Lλ = Lset-mono {α = lam} {β = α} α∈λ
    (Lset-mono {α = α} {β = sucV ∅} one∈α ∅∈Lset1)

  ∅∈λ : ⟨ ∅ ∈ˢ lam ⟩
  ∅∈λ = subst (λ w → ⟨ w ∈ˢ lam ⟩) (rank-fix ∅ ∅-ord)
    (rank-Lset lam ordλ ∅ ∅∈Lλ)

-- =====================================================================
-- THE HULL IS EXTENSIONAL (discharges the `Mext` hypothesis of `Co`).
-- Two hull members that agree on the hull's memberships differ nowhere:
-- a global difference witness z ∈ x \ y would satisfy the difference
-- formula "v ∈ x ∧ v ∉ y" over the codes of x and y in the stage, so
-- hull-closed produces a hull member with the same property, and the
-- agreement hypothesis refutes it.  The codes come from the truncated
-- hull membership, eliminated into the proposition x ≡ y; no least-code
-- selection is needed.  The classical steps are the two directions of
-- extensionality contrapositive and the difference-witness extraction,
-- each one LEM on a proposition.
-- =====================================================================
module HullExt (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
  (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα
  module H = ASt.Hull X X⊆L ∅∈α

  M : S
  M = H.T.Hull

  -- the inclusion with the truncated membership, at the levels the hull
  -- speaks
  testP : S → S → Type (ℓ-suc ℓ)
  testP x y = (z : S) → fst (z ∈ˢ x) → fst (z ∈ˢ y)

  subF : S → S → hProp (ℓ-suc ℓ)
  subF x y = ( testP x y
             , isPropΠ (λ z → isPropΠ (λ _ → snd (z ∈ˢ y))) )

  -- a global difference witness in one direction, classically: from
  -- ¬ (x ⊆ y) extract a member of x that is not a member of y
  diff-witness : (x y : S) → ((⟨ subF x y ⟩) → Empty.⊥)
               → ∥ Σ[ z ∈ S ] ((z ∈ᵗ x) × ((z ∈ᵗ y) → Empty.⊥)) ∥₁
  diff-witness x y ¬xy = go (lem P)
    where
    P : hProp (ℓ-suc ℓ)
    P = ( ∥ Σ[ z ∈ S ] ((z ∈ᵗ x) × ((z ∈ᵗ y) → Empty.⊥)) ∥₁ , squash₁ )
    go : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → ⟨ P ⟩
    go (inl p) = p
    go (inr ¬p) = Empty.rec (¬xy (x⊆y))
      where
      x⊆y : ⟨ subF x y ⟩
      x⊆y z z∈x = Sum.rec (λ q → q)
        (λ nzy → Empty.rec (¬p ∣ z , (z∈x , nzy) ∣₁))
        (lem (z ∈ˢ y))

  -- extensionality contrapositive, in the two directions
  ext-contra : (x y : S) → (x ≡ y → Empty.⊥)
             → ((⟨ subF x y ⟩) → Empty.⊥) ⊎ ((⟨ subF y x ⟩) → Empty.⊥)
  ext-contra x y nxy = Sum.rec
    (λ hxy → inr (λ hyx → nxy (extensionalV (λ z → ⇔toPath (hxy z) (hyx z)))))
    (λ ¬hxy → inl ¬hxy)
    (lem (subF x y))

  -- the outer difference formula over the codes of the two hull members
  φ : (c d : H.T.Code) → Formula H.T.Code 1
  φ c d = (var zero ∈̇ con c) ∧̇ (¬̇ (var zero ∈̇ con d))

  -- the outer satisfaction from a global difference witness
  outer : (u v : S) (u∈M : u ∈ᵗ M)
        → (c d : H.T.Code) (ec : fst (H.T.val c) ≡ u) (ed : fst (H.T.val d) ≡ v)
        → (z : S) → (z ∈ᵗ u) → ((z ∈ᵗ v) → Empty.⊥)
        → ∥ Σ[ a ∈ ASt.SL ] ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ c d)) ⟩ ∥₁
  outer u v u∈M c d ec ed z zx nzy = ∣ a , sat ∣₁
    where
    z∈L : ⟨ z ∈ˢ Lset α ⟩
    z∈L = layer-trans (Lset-layer α) zx (H.Hull⊆L u u∈M)
    a : ASt.SL
    a = z , z∈L
    sat : ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ c d)) ⟩
    sat = ( subst (λ w → z ∈ᵗ w) (sym ec) zx
         , λ h → nzy (subst (λ w → z ∈ᵗ w) ed h) )

  -- the difference argument: hull-closed turns the outer witness into a
  -- hull member, and the agreement hypothesis refutes it
  refute : (x y : S) (x∈M : x ∈ᵗ M) (y∈M : y ∈ᵗ M)
         → (ag1 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
         → (c d : H.T.Code) (ec : fst (H.T.val c) ≡ x) (ed : fst (H.T.val d) ≡ y)
         → ((⟨ subF x y ⟩) → Empty.⊥) → Empty.⊥
  refute x y x∈M y∈M ag1 c d ec ed ¬xy = PT.rec Empty.isProp⊥ diff (diff-witness x y ¬xy)
    where
    diff : Σ[ z ∈ S ] ((z ∈ᵗ x) × ((z ∈ᵗ y) → Empty.⊥)) → Empty.⊥
    diff (z , zx , nzy) = PT.rec Empty.isProp⊥ go2 (H.hull-closed (φ c d) h)
      where
      h : ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val (φ c d))) ⟩
      h = outer x y x∈M c d ec ed z zx nzy
      go2 : Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩
                          × ⟨ (b ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ c d)) ⟩)
          → Empty.⊥
      go2 (b , b∈M , bsat) =
        nzy' (ag1 (fst b) b∈M (subst (λ w → ⟨ fst b ∈ˢ w ⟩) ec (fst bsat)))
        where
        nzy' : (fst b ∈ᵗ y → Empty.⊥)
        nzy' hy = snd bsat (subst (λ w → fst b ∈ᵗ w) (sym ed) hy)

  refute2 : (x y : S) (x∈M : x ∈ᵗ M) (y∈M : y ∈ᵗ M)
          → (ag2 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩)
          → (c d : H.T.Code) (ec : fst (H.T.val c) ≡ x) (ed : fst (H.T.val d) ≡ y)
          → ((⟨ subF y x ⟩) → Empty.⊥) → Empty.⊥
  refute2 x y x∈M y∈M ag2 c d ec ed ¬yx = PT.rec Empty.isProp⊥ diff (diff-witness y x ¬yx)
    where
    diff : Σ[ z ∈ S ] ((z ∈ᵗ y) × ((z ∈ᵗ x) → Empty.⊥)) → Empty.⊥
    diff (z , zy , nzx) = PT.rec Empty.isProp⊥ go2 (H.hull-closed (φ d c) h)
      where
      h : ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val (φ d c))) ⟩
      h = outer y x y∈M d c ed ec z zy nzx
      go2 : Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩
                          × ⟨ (b ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ d c)) ⟩)
          → Empty.⊥
      go2 (b , b∈M , bsat) =
        nzx' (ag2 (fst b) b∈M (subst (λ w → ⟨ fst b ∈ˢ w ⟩) ed (fst bsat)))
        where
        nzx' : (fst b ∈ᵗ x → Empty.⊥)
        nzx' hx = snd bsat (subst (λ w → fst b ∈ᵗ w) (sym ec) hx)

  hullExt : isExt M
  hullExt x y x∈M y∈M ag1 ag2 =
    PT.rec (isSetS x y) (λ cx → PT.rec (isSetS x y) (go cx) (H.hull-member y y∈M))
      (H.hull-member x x∈M)
    where
    go : Σ[ c ∈ H.T.Code ] (fst (H.T.val c) ≡ x)
       → Σ[ d ∈ H.T.Code ] (fst (H.T.val d) ≡ y) → x ≡ y
    go (c , ec) (d , ed) = Sum.rec (λ p → p) (λ np → Empty.rec (bad np))
      (lem ((x ≡ y) , isSetS x y))
      where
      bad : (x ≡ y → Empty.⊥) → Empty.⊥
      bad nxy = dir2 (dir1 nxy)
        where
        dir1 : (x ≡ y → Empty.⊥)
             → ((⟨ subF x y ⟩) → Empty.⊥) ⊎ ((⟨ subF y x ⟩) → Empty.⊥)
        dir1 = ext-contra x y
        dir2 : ((⟨ subF x y ⟩) → Empty.⊥) ⊎ ((⟨ subF y x ⟩) → Empty.⊥) → Empty.⊥
        dir2 (inl ¬xy) = refute x y x∈M y∈M ag1 c d ec ed ¬xy
        dir2 (inr ¬yx) = refute2 x y x∈M y∈M ag2 c d ec ed ¬yx

open import Cubical.Data.Nat.Properties using ( znots; snotz; injSuc )

module Devlin55
  (sq : (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ] ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y))
  (absorbs-subset : (α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                  → (x : S) → (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
                  → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  where

  module SC = L.StageCardinal {ℓ} lem sq
  module Up = SC.Upper

  stage-card-upper : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                   → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
  stage-card-upper = Up.stage-card-upper

  comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
  comp-inj (f , injf) (g , injg) =
    (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

  -- The ordinal embedding: a member of an ordinal embeds its index.
  ord-emb : (a b : S) → IsOrd b → ⟨ a ∈ˢ b ⟩ → ⟪ a ⟫ ↪ ⟪ b ⟫
  ord-emb a b ob a∈b = f , inj
    where
    f : ⟪ a ⟫ → ⟪ b ⟫
    f m = fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .fst
    inj : (m n : ⟪ a ⟫) → f m ≡ f n → m ≡ n
    inj m n e = ↪-inj {a = a}
      (sym (fiber b {x = ⟪ a ⟫↪ m} (ob .fst (member a m) a∈b) .snd)
        ∙ cong (⟪ b ⟫↪) e
        ∙ fiber b {x = ⟪ a ⟫↪ n} (ob .fst (member a n) a∈b) .snd)

  -- The bounded-subset lemma at one instance: the hull of Lset alpha
  -- union {x} at the limit stage lam, its collapse, the condensation
  -- (the two transfer hypotheses), the size chain and the cardinal
  -- argument.
  module BoundedSubsetAt
    (κ : S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ) (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (x : S) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (lam : S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) where

    module UK = UnionKit α lam x ordα ordλ α∈λ x⊆Lα x∈Lλ α∉ω
    module HS = HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ
    module HE = HullExt lam ordλ UK.X UK.X⊆Lλ UK.∅∈λ

    module Co
      (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩)
      (cover : (y : S) → ⟨ y ∈ˢ HS.M ⟩
             → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩) ∥₁)
      where

      module Cn = HS.Condense levelIn cover

      β : S
      β = Cn.condenses .fst

      β-isOrd : IsOrd β
      β-isOrd = Cn.condenses .snd .fst

      ext : HS.C.πX ≡ Lset β
      ext = Cn.condenses .snd .snd

      -- The code count: the hull's term algebra injects into alpha.
      module CodeCount (g : ⟪ UK.X ⟫ ↪ ⟪ α ⟫) where
        module B = SC.Bound α ordα α∉ω (sq α α∉ω)

        code-stable-suc : (k k' : ℕ) (p : k' ≡ k) (ψ : Formula (⊥* {ℓ}) (suc k'))
                        → FOL.Count.code (subst (λ j → Formula (⊥* {ℓ}) (suc j)) p ψ)
                          ≡ FOL.Count.code ψ
        code-stable-suc k k' p ψ =
          J (λ k p → FOL.Count.code (subst (λ j → Formula (⊥* {ℓ}) (suc j)) p ψ)
                     ≡ FOL.Count.code ψ)
            (cong FOL.Count.code (transportRefl ψ)) p

        mutual
          count : HS.H.T.Code → ⟪ α ⟫
          count (HS.H.T.base m) = B.pair (B.numeral 0) (fst g m)
          count (HS.H.T.wit k ψ cs) =
            B.pair (B.numeral (suc k))
              (B.pair (B.pair (B.numeral (FOL.Count.code ψ)) (B.numeral (suc k)))
                (tuple k cs))

          tuple : (j : ℕ) → Vec HS.H.T.Code j → ⟪ α ⟫
          tuple zero [] = B.numeral 0
          tuple (suc j) (c ∷ cs) = B.pair (count c) (tuple j cs)

          tuple-inj : (j : ℕ) (cs ds : Vec HS.H.T.Code j)
                    → tuple j cs ≡ tuple j ds → cs ≡ ds
          tuple-inj zero [] [] e = refl
          tuple-inj (suc j) (c ∷ cs) (d ∷ ds) e =
            cong₂ (λ (x : HS.H.T.Code) (y : Vec HS.H.T.Code j) → x ∷ y) hc hcs
            where
            p : (count c ≡ count d) × (tuple j cs ≡ tuple j ds)
            p = B.pair-inj (count c) (tuple j cs) (count d) (tuple j ds) e
            hc : c ≡ d
            hc = count-inj c d (fst p)
            hcs : cs ≡ ds
            hcs = tuple-inj j cs ds (snd p)

          tuple-stable : (j j' : ℕ) (p : j' ≡ j) (cs : Vec HS.H.T.Code j')
                       → tuple j (subst (Vec HS.H.T.Code) p cs) ≡ tuple j' cs
          tuple-stable j j' p cs =
            J (λ j p → tuple j (subst (Vec HS.H.T.Code) p cs) ≡ tuple j' cs)
              (cong (tuple j') (transportRefl cs)) p

          count-inj : (c d : HS.H.T.Code) → count c ≡ count d → c ≡ d
          count-inj (HS.H.T.base m) (HS.H.T.base m') e =
            cong HS.H.T.base (snd g m m' (B.pair-inj _ _ _ _ e .snd))
          count-inj (HS.H.T.base m) (HS.H.T.wit k' ψ' cs') e =
            Empty.rec (znots (B.numeral-inj 0 (suc k') (B.pair-inj _ _ _ _ e .fst)))
          count-inj (HS.H.T.wit k ψ cs) (HS.H.T.base m') e =
            Empty.rec (snotz (B.numeral-inj (suc k) 0 (B.pair-inj _ _ _ _ e .fst)))
          count-inj (HS.H.T.wit k ψ cs) (HS.H.T.wit k' ψ' cs') e = wit-eq
            where
            e-out : (B.numeral (suc k) ≡ B.numeral (suc k'))
                  × (B.pair (B.pair (B.numeral (FOL.Count.code ψ)) (B.numeral (suc k)))
                       (tuple k cs)
                    ≡ B.pair (B.pair (B.numeral (FOL.Count.code ψ')) (B.numeral (suc k')))
                       (tuple k' cs'))
            e-out = B.pair-inj (B.numeral (suc k))
                        (B.pair (B.pair (B.numeral (FOL.Count.code ψ)) (B.numeral (suc k)))
                          (tuple k cs))
                        (B.numeral (suc k'))
                        (B.pair (B.pair (B.numeral (FOL.Count.code ψ')) (B.numeral (suc k')))
                          (tuple k' cs'))
                        e
            psk : suc k ≡ suc k'
            psk = B.numeral-inj (suc k) (suc k') (fst e-out)
            pk : k ≡ k'
            pk = injSuc psk
            e-in : B.pair (B.pair (B.numeral (FOL.Count.code ψ)) (B.numeral (suc k)))
                        (tuple k cs)
                  ≡ B.pair (B.pair (B.numeral (FOL.Count.code ψ')) (B.numeral (suc k')))
                        (tuple k' cs')
            e-in = snd e-out
            e-fst : B.pair (B.numeral (FOL.Count.code ψ)) (B.numeral (suc k))
                  ≡ B.pair (B.numeral (FOL.Count.code ψ')) (B.numeral (suc k'))
            e-fst = fst (B.pair-inj _ _ _ _ e-in)
            e-code : FOL.Count.code ψ ≡ FOL.Count.code ψ'
            e-code = B.numeral-inj (FOL.Count.code ψ) (FOL.Count.code ψ') (fst (B.pair-inj _ _ _ _ e-fst))
            e-tup : tuple k cs ≡ tuple k' cs'
            e-tup = snd (B.pair-inj _ _ _ _ e-in)
            ψ₀ : Formula (⊥* {ℓ}) (suc k)
            ψ₀ = subst (λ j → Formula (⊥* {ℓ}) (suc j)) (sym pk) ψ'
            sψ : ψ ≡ ψ₀
            sψ = snd FOL.Count.shape-count-inj {k = suc k} {φ = ψ} {ψ = ψ₀}
                   (e-code ∙ sym (code-stable-suc k k' (sym pk) ψ'))
            qψ : PathP (λ i → Formula (⊥* {ℓ}) (suc (pk i))) ψ ψ'
            qψ = toPathP (cong (subst (λ j → Formula (⊥* {ℓ}) (suc j)) pk) sψ
                          ∙ substSubst⁻ (λ j → Formula (⊥* {ℓ}) (suc j)) pk ψ')
            cs₀ : Vec HS.H.T.Code k
            cs₀ = subst (Vec HS.H.T.Code) (sym pk) cs'
            scs : cs ≡ cs₀
            scs = tuple-inj k cs cs₀
                    (e-tup ∙ sym (tuple-stable k k' (sym pk) cs'))
            qcs : PathP (λ i → Vec HS.H.T.Code (pk i)) cs cs'
            qcs = toPathP (cong (subst (Vec HS.H.T.Code) pk) scs
                          ∙ substSubst⁻ (Vec HS.H.T.Code) pk cs')
            wit-eq : HS.H.T.wit k ψ cs ≡ HS.H.T.wit k' ψ' cs'
            wit-eq = cong (λ x → HS.H.T.wit (fst x) (fst (snd x)) (snd (snd x)))
              (ΣPathP {A = λ _ → ℕ} {B = λ i k →
                           Formula (⊥* {ℓ}) (suc k) × Vec HS.H.T.Code k}
                       (pk , ΣPathP {A = λ i → Formula (⊥* {ℓ}) (suc (pk i))}
                    {B = λ i _ → Vec HS.H.T.Code (pk i)}
                                    (qψ , qcs)))

      code-inj : ⟪ UK.X ⟫ ↪ ⟪ α ⟫
      code-inj = comp-inj (absorbs-subset α α∉ω x x⊆Lα) (stage-card-upper α ordα α∉ω)

      module CC = CodeCount code-inj

      module IC = InvColl HS.M HE.hullExt
      module CSel = CodeSelect α ordα (SC.OrdSWO.ordSWO α ordα)
        HS.M HS.H.T.Code (λ c → fst (HS.H.T.val c))
        HS.H.hull-member CC.count CC.count-inj

      -- WALL 2, PLACED.  The canonical code of each hull member at the
      -- delivered count (CanonCode at CC.count/CC.count-inj and the
      -- hull's own well-order), and the HullElemDown instance at the
      -- hull's stage.  The fibre coercion is V.Presentation.fiber: the
      -- hull-member type SM is the fiber of the embedding, so the
      -- canonical-code machinery (stated on ⟪ M ⟫) applies to it.
      module CCn = CanonCode α ordα (SC.OrdSWO.ordSWO α ordα)
        HS.M HS.H.T.Code (λ c → fst (HS.H.T.val c))
        HS.H.hull-member CC.count CC.count-inj

      hedF : (Σ[ x ∈ S ] ⟨ x ∈ˢ HS.M ⟩) → HS.H.T.Code
      hedF q = CCn.canonical (fiber HS.M (snd q) .fst)

      hedF-spec : (q : Σ[ x ∈ S ] ⟨ x ∈ˢ HS.M ⟩)
                → fst (HS.H.T.val (hedF q)) ≡ fst q
      hedF-spec q = go (fiber HS.M (snd q))
        where
        go : (f : Σ[ m ∈ ⟪ HS.M ⟫ ] (⟪ HS.M ⟫↪ m ≡ fst q))
           → fst (HS.H.T.val (CCn.canonical (f .fst))) ≡ fst q
        go f = CCn.canonical-spec (f .fst) ∙ f .snd

      module HED = HullElemDown lam ordλ UK.X UK.X⊆Lλ UK.∅∈λ
      module HEDC = HED.WithCode hedF hedF-spec

      -- The consumer-facing ElemDown at the hull: the stage reading of
      -- a formula over hull constants implies the hull reading, wired
      -- into DownReflect's ElemDown at the hull's stage.
      module DR54 = DownReflect lam ordλ UK.X UK.X⊆Lλ UK.∅∈λ

      elem-down : DR54.ElemDown
      elem-down = HEDC.elem-down

      -- The inverse collapse composite, with NO `collapseCode` hypothesis:
      -- leg 1 is the propositional fibre (π is injective on M), leg 2 is
      -- the least count over the ordinal's own well-order.
      πX↪α : ⟪ HS.C.πX ⟫ ↪ ⟪ α ⟫
      πX↪α = (λ p → CSel.h (IC.inv p))
           , (λ p q e → IC.inv-inj p q (CSel.h-inj (IC.inv p) (IC.inv q) e))

      β↪α : ⟪ β ⟫ ↪ ⟪ α ⟫
      β↪α = comp-inj
              (subst (λ A → ⟪ β ⟫ ↪ ⟪ A ⟫) (sym ext)
                (SC.stage-card-lower β β-isOrd))
              πX↪α

      -- x is a member of the collapse, fixed by the collapse.
      x∈M : ⟨ x ∈ˢ HS.M ⟩
      x∈M = HS.H.X⊆M x UK.x∈X

      x∈πX : ⟨ x ∈ˢ HS.C.πX ⟩
      x∈πX = subst (λ w → ⟨ w ∈ˢ HS.C.πX ⟩)
        (HS.C.fixes UK.X (λ a a∈ₛX → ∈∈ₛ {a = a} {b = HS.M} .fst
          (HS.H.X⊆M a (∈∈ₛ {a = a} {b = UK.X} .snd a∈ₛX))) UK.Xtr x UK.x∈X)
        (HS.C.πX-intro x x∈M)

      β∈κ : ⟨ β ∈ˢ κ ⟩
      β∈κ = Sum.rec
          (λ b∈κ → b∈κ)
          (Sum.rec (λ b≡κ → Empty.rec (cardκ α α∈κ
              (comp-inj (subst (λ A → ⟪ κ ⟫ ↪ ⟪ A ⟫) (sym b≡κ)
                ((λ m → m) , (λ m n e → e)))
                β↪α)))
                   (λ κ∈β → Empty.rec (cardκ α α∈κ
              (comp-inj (ord-emb κ β β-isOrd κ∈β) β↪α))))
          (ord-tri β β-isOrd κ ordκ)

      x∈Lκ : ⟨ x ∈ˢ Lset κ ⟩
      x∈Lκ = PT.rec (snd (x ∈ˢ Lset κ)) go (cover x x∈M)
        where
        go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π x ∈ˢ Lset γ ⟩)
           → ⟨ x ∈ˢ Lset κ ⟩
        go (γ , oγ , γ∈πX , h) =
          Lset-mono {α = κ} {β = γ} γ∈κ
            (subst (λ w → ⟨ w ∈ˢ Lset γ ⟩)
              (HS.C.fixes UK.X (λ a a∈ₛX → ∈∈ₛ {a = a} {b = HS.M} .fst
                (HS.H.X⊆M a (∈∈ₛ {a = a} {b = UK.X} .snd a∈ₛX))) UK.Xtr x UK.x∈X) h)
          where
          γ∈β : ⟨ γ ∈ˢ β ⟩
          γ∈β = Cn.ord∈β γ γ∈πX oγ
          γ∈κ : ⟨ γ ∈ˢ κ ⟩
          γ∈κ = ordκ .fst γ∈β β∈κ

      theorem : ⟨ x ∈ˢ Lset κ ⟩
      theorem = x∈Lκ

-- =====================================================================

```
