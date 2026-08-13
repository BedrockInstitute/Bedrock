{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.48] THE CONDENSATION THEOREM ASSEMBLY, MEASURED.
--
-- The probe builds the condensation core at ONE instance and measures
-- its seconds class.  Three pieces, per _build/lj-1.46-report.md:
--
--   1. The Sigma-1 level-hood statement at the class carrier with a
--      bounded witness: "x = Lset gamma" as
--      "exists w in K (graphBndAt w gamma K and x = w)", with the
--      Sigma-1 certificate at variable slots.  Uses the delivered
--      GraphB, DefBodyB and the block-1 certificate shape.
--   2. The satisfaction iso-invariance under the collapse at the hull
--      carrier: for M the hull inside L_lambda and pi the collapse,
--      the bounded graph formula's satisfaction transfers between M
--      and pi M and back.
--   3. The down-reflection at M: the same Sigma-1 statement reflects
--      from L_lambda into M through hull-closed.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ148 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; Term; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
  ; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm; mapFo-comp; embed; mapΔ₀ )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Model {ℓ}
  using ( appAt; extAt; extAt-in-both; envSetAt )
open import L.Condensation {ℓ} lem using
  ( extAtB; Δ₀-extAtB
  ; DefBodyB; Δ₀-DefBodyB
  ; module StepAtB; module ApproxB; module GraphB
  ; existCertAt; Σ₁-cert
  ; module EraseTransfer
  ; ride-only; ride-defines
  )
open import L.Hull {ℓ} lem using ( module AtStage )
open import V.Collapse {ℓ} using ( module Collapse; isExt; isTrans )

open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_; _,_; Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module CS = hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- SECTION 1: THE SIGMA-1 LEVEL-HOOD AT THE CLASS CARRIER.
-- =====================================================================

-- The bounded graph at the class carrier, at the environment
-- w ∷ x ∷ gamma ∷ K ∷ delta (4 + n).  The witness w is variable zero;
-- x is the value, gamma the ordinal index, K the bound.  The two
-- leaves are DefBodyB at the step and approximation arities, exactly
-- the delivered nesting of GraphB.
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

  -- The bounded matrix: exists w in K (graph w gamma K and x = w).
  levelHoodB : Formula CS.S (suc (suc (suc (suc n))))
  levelHoodB =
    ∃̇∈ (var (suc (suc zero)))
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

  -- The Sigma-1 form: the unbounded witness over the bounded matrix,
  -- exactly the block-1 certificate shape (existCertAt, Sigma-1-cert).
  levelHoodΣ₁ : Formula CS.S (suc (suc (suc n)))
  levelHoodΣ₁ = ∃̇ levelHoodB

  Σ₁-levelHood : Σ₁ levelHoodΣ₁
  Σ₁-levelHood = σ-∃ (σ-Δ₀ Δ₀-levelHoodB)

-- =====================================================================
-- SECTION 2: THE SATISFACTION ISO-INVARIANCE UNDER THE COLLAPSE.
-- =====================================================================

-- The iso-invariance is the formula-induction that transfers the
-- satisfaction of a formula between a carrier M and its collapse image
-- PM, along the membership isomorphism p.  The collapse supplies the
-- iso at the atoms (V.Collapse.InjExt.iso), the injectivity on the
-- carrier (InjExt.pi-inj) and the surjectivity of the range
-- (piX-member); the induction is the assembly's own content.
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

-- The collapse instance: M = the hull X, PM = the collapse image piX.
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

-- The hull at the stage Lset alpha with generator X; the Sigma-1
-- statement at L_lambda (a formula over Code, mapped by val) reflects
-- into the hull: hull-closed hands the witness in M, and the matrix
-- agreement at M is the elementarity-down residue, stated as the
-- hypothesis ElemDown (the hull-elementarity bridge, O2's priced
-- piece).  The Code-to-SM constant bridge is the probe's own glue.
module DownReflect (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα
  module H = ASt.Hull X X⊆L ∅∈α

  -- the hull's inner world, defined here (the delivered AtM does not
  -- export its renamed satisfaction)
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

  -- the elementarity-down residue (O2), stated at the exact shape the
  -- condensation transfer consumes
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

-- The one instance: the level-hood statement at the hull of the stage,
-- with the collapse iso and the elementarity-down residue as the
-- assembly's priced hypotheses.
module AtHullInstance (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩)
  (Xext : isExt X) where

  module CIso = CollapseIso X Xext
  module DR = DownReflect α ordα X X⊆L ∅∈α

  -- the bounded graph formula's satisfaction transfers between the hull
  -- and its collapse, both ways (the assembly's transfer legs)
  transfer : {n : ℕ} (φ : Formula CIso.I.SM n) (δ : CIso.I.SM ^ n)
           → (⟨ δ CIso.I.⊨ᵐ φ ⟩ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ mapFo CIso.I.g φ ⟩)
          × (⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ mapFo CIso.I.g φ ⟩ → ⟨ δ CIso.I.⊨ᵐ φ ⟩)
  transfer {n} φ δ = CIso.I.iso-inv n φ δ , CIso.I.iso-inv-bwd n φ δ

  -- the down-reflection of the Sigma-1 statement at the stage into the
  -- hull, given the elementarity-down residue
  reflect : DR.ElemDown
          → (φ : Formula DR.H.T.Code 1)
          → ⟨ [] DR.ASt.AbsL.⊨ᵐ (∃̇ (mapFo DR.H.T.val φ)) ⟩
          → ∥ Σ[ q ∈ DR.SM ] ⟨ (q ∷ []) DR.⊨ᵐ (mapFo DR.codeValM φ) ⟩ ∥₁
  reflect = DR.down-reflect
