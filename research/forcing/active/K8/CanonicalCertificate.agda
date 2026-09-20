{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module K8.CanonicalCertificate
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
    → ZFStructure._≈ˢ_ 𝒮 x y ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (sep : OrdinaryProfile.Separation 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import CodedVocabulary 𝒮 using ( subsetΔ; coneΔ; coneAtˢ; sepAt; sepAt-reading )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CodedVocabulary
import CodedCompletion
import Certificate
import K4.InstanceCoded
import GroundDescription

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module CC = CodedCompletion 𝒮
module G = Certificate 𝒮 ext paths
module CV = CodedVocabulary 𝒮
module GD = GroundDescription 𝒮 ext paths

module AtPresentation
  (𝔓 : CC.Presentation)
  (laws : CC.Coded.ForcingLaws 𝔓)
  where

  module P = CC.Coded 𝔓
  module R = CC.Core ext pow sep paths 𝔓 laws
  module K = CC.Classical ext pow sep paths 𝔓 laws
  module A = K4.InstanceCoded 𝒮 ext pow sep paths 𝔓 laws
  hostPresentation : G.Presentation
  hostPresentation = record
    { carrier = P.carrier
    ; _≼_ = λ p q → P._≼ᴵ_ (fst p) (fst q)
    ; ≼-refl = λ p → P.ForcingLaws.≼ᴵ-refl laws (fst p) (snd p)
    ; ≼-trans = λ {p} {q} {r} h k → P.ForcingLaws.≼ᴵ-trans laws
        (fst p) (fst q) (fst r) (snd p) (snd q) (snd r) h k
    ; inhabited = P.inhabited }
  module O = G.Over hostPresentation

  lattice : G.BoundedLattice R.B
  lattice = record
    { ⊤ᴮ = R.⊤ᴮ ; ⊥ᴮ = R.⊥ᴮ
    ; _⊓ᴮ_ = A.meetᴷ ; _⊔ᴮ_ = A.joinᴷ
    ; ⊓-lb₁ = A.⊓-lb₁ ; ⊓-lb₂ = A.⊓-lb₂ ; ⊓-glb = A.⊓-glb
    ; ⊔-ub₁ = A.⊔-ub₁ ; ⊔-ub₂ = A.⊔-ub₂ ; ⊔-lub = A.⊔-lub
    ; ⊥-least = A.⊥-least ; ⊤-greatest = A.⊤-greatest }

  boolean : G.IsBoolean R.B lattice
  boolean = record
    { ¬ᴮ_ = A.negᴷ ; ¬-⊓ = A.¬-⊓ ; ¬-⊔ = A.¬-⊔ ; ⊓-⊔-dist = A.⊓-⊔-dist }

  complete : G.CompleteForCoded R.B
  complete = record
    { supᴮ = A.supᴷ ; sup-ub = A.sup-ub ; sup-lub = A.sup-lub
    ; infᴮ = A.infᴷ ; inf-lb = A.inf-lb ; inf-glb = A.inf-glb }

  nontrivial : G.Nontrivial R.B lattice
  nontrivial e = PT.rec isProp⊥* step P.inhabited
    where
    step : Σ[ p ∈ S ] ⟨ p ∈ˢ P.carrier ⟩ → ⟨ ⊥ ⟩
    step (p , hp) = R.⊥ᴮ-empty p
      (subst (λ z → ⟨ p ∈ˢ fst z ⟩) (sym e) hp)

  coneFo : Formula S 3
  coneFo = CV.instFo emb
    (coneAtˢ zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))))
    where
    emb : Fin 4 → Term S 3
    emb zero = con P.carrier
    emb (suc zero) = con P.order
    emb (suc (suc zero)) = var (suc zero)
    emb (suc (suc (suc zero))) = var zero

  coneFo-reading : (x p u : S) → ((x ∷ p ∷ u ∷ []) ⊨ coneFo)
    ≡ coneΔ P.carrier P.order p x
  coneFo-reading x p u = CV.⊨-inst emb
    (coneAtˢ zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))))
    (x ∷ p ∷ u ∷ []) (P.carrier ∷ P.order ∷ p ∷ x ∷ []) fits
    where
    emb : Fin 4 → Term S 3
    emb zero = con P.carrier
    emb (suc zero) = con P.order
    emb (suc (suc zero)) = var (suc zero)
    emb (suc (suc (suc zero))) = var zero
    fits : CV.Fits emb (x ∷ p ∷ u ∷ []) (P.carrier ∷ P.order ∷ p ∷ x ∷ [])
    fits zero = refl
    fits (suc zero) = refl
    fits (suc (suc zero)) = refl
    fits (suc (suc (suc zero))) = refl

  open OrdinaryProfile.PathRealization 𝒮 paths using ( ≈ˢ-to-path; path-to-≈ˢ )

  member-below : (b : R.El) (p : P.Cond) → ⟨ fst p ∈ˢ fst b ⟩
    → ⟨ R.iᴮ p R.≤ᴮ b ⟩
  member-below b p hp y hy = R.B-regular (fst b) (snd b) .fst y yc
    (R.star²-mono (R.cone (fst p)) (R.mem (fst b)) sub y yc (w .snd))
    where
    w = subst ⟨_⟩ (R.iSet-mem (fst p) y) hy
    yc = w .fst
    sub : R.cone (fst p) R.⊑ R.mem (fst b)
    sub z hz k = R.B-down (fst b) (snd b) z (fst p) hz (snd p) k hp

  below : R.El → S
  below = fst

  below-sub : (b : R.El) → ⟨ subsetΔ (below b) P.carrier ⟩
  below-sub b = R.B-sub (fst b) (snd b)

  below-spec : (b : R.El) (p : P.Cond)
    → (fst p ∈ˢ below b) ≡ (R.iᴮ p R.≤ᴮ b)
  below-spec b p = ⇔toPath (member-below b p) (λ h → h (fst p) (R.i-self p))

  _↔̇_ : ∀ {n} → Formula S n → Formula S n → Formula S n
  φ ↔̇ ψ = (φ ⇒̇ ψ) ∧̇ (ψ ⇒̇ φ)

  imageFo : S → Formula S 1
  imageFo d = ∃̇∈ (con P.carrier)
    ((var zero ∈̇ con d) ∧̇ ∀̇ ((var zero ∈̇ var (suc (suc zero)))
      ↔̇ ((var zero ∈̇ con P.carrier) ∧̇ coneFo)))

  imageBody-reading : (u p : S)
    → ((x : S) → ⟨ ((x ∈ˢ u) ⇒ ((x ∈ˢ P.carrier) ⊓
        ((x ∷ p ∷ u ∷ []) ⊨ coneFo))) ⊓
        (((x ∈ˢ P.carrier) ⊓ ((x ∷ p ∷ u ∷ []) ⊨ coneFo)) ⇒ (x ∈ˢ u)) ⟩)
    → u ≡ R.iSet p
  imageBody-reading u p h = GD.ext-path λ x →
    ⇔toPath (h x .fst) (h x .snd)
      ∙ cong ((x ∈ˢ P.carrier) ⊓_) (coneFo-reading x p u)
      ∙ sym (R.iSet-mem p x)

  imageBody-intro : (u p : S) → u ≡ R.iSet p
    → (x : S) → ⟨ ((x ∈ˢ u) ⇒ ((x ∈ˢ P.carrier) ⊓
        ((x ∷ p ∷ u ∷ []) ⊨ coneFo))) ⊓
        (((x ∈ˢ P.carrier) ⊓ ((x ∷ p ∷ u ∷ []) ⊨ coneFo)) ⇒ (x ∈ˢ u)) ⟩
  imageBody-intro u p e x = subst ⟨_⟩ eq , subst ⟨_⟩ (sym eq)
    where
    eq = cong (x ∈ˢ_) e ∙ R.iSet-mem p x
      ∙ cong ((x ∈ˢ P.carrier) ⊓_) (sym (coneFo-reading x p u))

  opaque
    iImage : S → S
    iImage d = GD.separateOf sep R.B (imageFo d)

    image-spec : (d u : S) → (u ∈ˢ iImage d)
      ≡ ((u ∈ˢ R.B) ⊓ ((u ∷ []) ⊨ imageFo d))
    image-spec d = GD.separateOf-spec sep R.B (imageFo d)

  iImage-sub : (d : S) → ⟨ subsetΔ d P.carrier ⟩ → ⟨ subsetΔ (iImage d) R.B ⟩
  iImage-sub d _ u h = subst ⟨_⟩ (image-spec d u) h .fst

  iImage-spec : (d : S) (u : R.El) → (fst u ∈ˢ iImage d)
    ≡ ⋁ P.Cond (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (R.iᴮ p)))
  iImage-spec d u = ⇔toPath forward backward
    where
    forward : ⟨ fst u ∈ˢ iImage d ⟩
      → ⟨ ⋁ P.Cond (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (R.iᴮ p))) ⟩
    forward h = PT.map
      (λ { (p , hp , hd , eq) → (p , hp) , hd ,
        path-to-≈ˢ (fst u) (R.iSet p) (imageBody-reading (fst u) p eq) })
      (subst ⟨_⟩ (image-spec d (fst u)) h .snd)
    backward : ⟨ ⋁ P.Cond (λ p → (fst p ∈ˢ d) ⊓ (fst u ≈ˢ fst (R.iᴮ p))) ⟩
      → ⟨ fst u ∈ˢ iImage d ⟩
    backward h = subst ⟨_⟩ (sym (image-spec d (fst u))) (snd u , PT.map
      (λ { (p , hd , eq) → fst p , snd p , hd ,
        imageBody-intro (fst u) (fst p) (≈ˢ-to-path (fst u) (R.iSet (fst p)) eq) }) h)

  image-self : (d : S) (p : P.Cond) → ⟨ fst p ∈ˢ d ⟩
    → ⟨ fst (R.iᴮ p) ∈ˢ iImage d ⟩
  image-self d p hp = subst ⟨_⟩ (sym (image-spec d (R.iSet (fst p))))
    (R.iSet-inB (fst p) , ∣ fst p , snd p , hp ,
      imageBody-intro (R.iSet (fst p)) (fst p) refl ∣₁)

  recover : (b : R.El)
    → A.supᴷ (iImage (below b)) (iImage-sub (below b) (below-sub b)) ≡ b
  recover b = R.≤ᴮ-antisym sup b down up
    where
    X = iImage (below b)
    hX = iImage-sub (below b) (below-sub b)
    sup = A.supᴷ X hX
    down : ⟨ sup R.≤ᴮ b ⟩
    down = A.sup-lub X hX b λ u hu →
      PT.rec (snd (u R.≤ᴮ b))
        (λ { (p , hp , e) → subst (λ z → ⟨ subsetΔ z (fst b) ⟩)
          (sym (≈ˢ-to-path (fst u) (R.iSet (fst p)) e)) (member-below b p hp) })
        (subst ⟨_⟩ (iImage-spec (below b) u) hu)
    up : ⟨ b R.≤ᴮ sup ⟩
    up x hx = A.sup-ub X hX (R.iᴮ p)
      (image-self (below b) p hx) x (R.i-self p)
      where
      p : P.Cond
      p = x , below-sub b x hx

  opaque
    unfolding A.meetᴷ
    meet-split : (u v : R.El) (z : S) → ⟨ z ∈ˢ fst (A.meetᴷ u v) ⟩
      → ⟨ (z ∈ˢ fst u) ⊓ (z ∈ˢ fst v) ⟩
    meet-split = R.meet-split
    meet-join : (u v : R.El) (z : S) → ⟨ (z ∈ˢ fst u) ⊓ (z ∈ˢ fst v) ⟩
      → ⟨ z ∈ˢ fst (A.meetᴷ u v) ⟩
    meet-join = R.meet-join

  embedding : LEM ℓ → O.Embedding R.B lattice complete
  embedding lem = record
    { i = R.iᴮ
    ; i-mono = λ {p} {q} → R.i-mono p q
    ; i-pos = λ p → R.positive→nonzero (R.iᴮ p) (R.i-pos p)
    ; i-compat→ = λ p q h → R.positive→nonzero (A.meetᴷ (R.iᴮ p) (R.iᴮ q))
        (R.i-compat→-at p q (A.meetᴷ (R.iᴮ p) (R.iᴮ q))
          (meet-join (R.iᴮ p) (R.iᴮ q)) h)
    ; i-compat← = λ p q h → K.i-compat←-at lem p q
        (A.meetᴷ (R.iᴮ p) (R.iᴮ q)) (meet-split (R.iᴮ p) (R.iᴮ q))
        (K.nonzero→positive lem (A.meetᴷ (R.iᴮ p) (R.iᴮ q)) h)
    ; below = below ; below-sub = below-sub ; below-spec = below-spec
    ; iImage = iImage ; iImage-sub = iImage-sub ; iImage-spec = iImage-spec
    ; recover = recover }

  certificate : LEM ℓ → O.CertifiedCompletion
  certificate lem = record
    { B = R.B ; lattice = lattice ; boolean = boolean ; complete = complete
    ; nontrivial = nontrivial ; embedding = embedding lem }
