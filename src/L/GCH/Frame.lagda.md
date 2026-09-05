# The condensation frame

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Frame {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _≐_; _∈̇_; _∧̇_; ⊥̇; ⊤̇; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∧; δ-∀∈; δ-∃∈; δ-∈; δ-⊥; δ-⊤ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using
  ( embed; embed-⊨; mapΔ₀; mapFo; mapFo-comp )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isExt; isTrans )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; 𝒟ₒ )
open import L.Coding.Model {ℓ} using ( sucAtL )
open import L.Condensation {ℓ} lem using
  ( module GraphB; DefBodyB; Δ₀-DefBodyB; Δ₀-sucAtL )
open import L.BoundedSubset {ℓ} lem using
  ( module HullStage; module CollapseIso; module HullExt
  ; module Cnt; erase-Δ₀ )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( map; _∷_; [] )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The 𝒮ʟ carrier, for the syntax of the witness slot.  Same name as
-- src/L/BoundedSubset.lagda.md:58.
module CS = hPropStructure 𝒮ʟ using (S)

module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemVᵃ using ( _^_ )

-- =====================================================================
-- THE AMBIENT PARAMETER-FREE READING.  [LJ-1.652] Probe652.agda:46-91.
-- =====================================================================

module AtP = SemVᵃ.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b) using (_⊨_)

_⊨ₚ_ : {n : ℕ} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
_⊨ₚ_ = AtP._⊨_

-- A parameter-free formula is FIXED by every relabelling: `embed` has
-- already sent the empty constant domain everywhere, and there is
-- nothing left for `f` to move.
embed-map : {ℓ₁ ℓ₂ : Level} {K : Type ℓ₁} {K' : Type ℓ₂} (f : K → K')
            {n : ℕ} (φ : Formula (⊥* {ℓ-suc ℓ}) n)
          → mapFo f (embed φ) ≡ embed φ
embed-map f φ =
    mapFo-comp Empty.rec* f φ
  ∙ cong (λ h → mapFo h φ) (funExt (λ b → Empty.rec* b))

-- A Σ₀ matrix that carries its parameter in a SLOT and holds exactly
-- of the operation's value at that parameter.
Matrix₂ : (S → S) → Type (ℓ-suc ℓ)
Matrix₂ F =
  Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 2 ]
    ( Δ₀ φ
    × ((a p : S) → ⟨ (a ∷ p ∷ []) ⊨ₚ φ ⟩ → a ≡ F p)
    × ((a p : S) → a ≡ F p → ⟨ (a ∷ p ∷ []) ⊨ₚ φ ⟩) )

-- DEVLIN'S OWN SHAPE (dev/literature/devlin-II5.md:95): a Σ₀ formula
-- Φ(z, v, γ) with a WITNESS slot beside the value and the parameter.
-- The soundness half stays outright; the completeness half is not
-- part of the matrix, because producing a witness is the consumer's.
Witnessed : (S → S) → Type (ℓ-suc ℓ)
Witnessed F =
  Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 3 ]
    ( Δ₀ φ
    × ((a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ φ ⟩ → a ≡ F p) )

-- =====================================================================
-- THE FRAME OF [LJ-1.641].  Probe641.agda:58-72.  One hull stage and
-- the type `Commute`, which [LJ-1.652]'s `commute-641` is checked
-- against.
-- =====================================================================

module Frame641 (lam : S) (ordλ : IsOrd lam)
                (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
                (X : S)
                (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
                (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using (module ASt; module C; module Condense; module H; M)

  Commute : Type (ℓ-suc ℓ)
  Commute =
    (δ : S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

-- =====================================================================
-- THE FRAME.  [LJ-1.652] Probe652.agda:99-306, module `Frame652`.
-- One hull stage, the telescope of src/L/BoundedSubset.lagda.md
-- `HullStage`, plus the inner world `AtM` that carries `Elementary`.
-- =====================================================================

module Frame (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using (module ASt; module C; module Condense; module H; M)
  module F641 = Frame641 lam ordλ succλ X X⊆Lλ ∅∈λ using (Commute)
  module ASt = HS.ASt using (module AbsL; module AtM; Ltr; SL)
  module A = ASt.AtM HS.M HS.H.Hull⊆L using (Elementary; SM; inL; _⊨ᵐ_)

  -- SECTION 1.  THE READING OF A Σ₀ MATRIX AT A TRANSITIVE CARRIER.
  module AtTrans (U : S) (Utr : isTrans U) where

    module Ab = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ U) Utr using (SM; abs₀; _⊨ᵐ_)

    read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Ab.SM ^ n)
         → (δ Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    read {n} {φ} dφ δ =
        Ab.abs₀ (mapΔ₀ Empty.rec* dφ) δ
      ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = Ab.SM} fst φ (map fst δ)
      ∙ cong (λ ι → SemVᵃ.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
             (funExt (λ b → Empty.rec* b))

  -- SECTION 2.  THE CARRY.  Ambient truth at hull members becomes
  -- ambient truth at their collapse values: (1) down into the hull by
  -- `elem`, (2) across by the collapse iso `iso-inv`, (3) out of the
  -- collapse by Δ₀ absoluteness at the transitive range `πX`.
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ using (hullExt)

  Mext : isExt HS.M
  Mext = HE.hullExt

  module Carry (elem : A.Elementary) where

    module CIso = CollapseIso HS.M Mext using (module I; iso-fwd; iso-bwd)
    module TL = AtTrans (Lset lam) ASt.Ltr using (read)
    module Tπ = AtTrans HS.C.πX HS.C.πX-trans

    atL : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : ASt.SL ^ n)
        → (δ ASt.AbsL.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atL dφ δ = TL.read dφ δ

    atπ : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Tπ.Ab.SM ^ n)
        → (δ Tπ.Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atπ dφ δ = Tπ.read dφ δ

    atM : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
        → (δ CIso.I.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atM {n} {φ} dφ δ =
        elem n (embed φ) δ
      ∙ cong (λ ψ → map A.inL δ ASt.AbsL.⊨ᵐ ψ) (embed-map A.inL φ)
      ∙ atL dφ (map A.inL δ)
      ∙ cong (λ γ → γ ⊨ₚ φ) (map-inL-fst δ)
      where
      map-inL-fst : {m : ℕ} (γ : A.SM ^ m)
                  → map fst (map A.inL γ) ≡ map fst γ
      map-inL-fst [] = refl
      map-inL-fst (q ∷ γ) = cong (fst q ∷_) (map-inL-fst γ)

    -- THE CARRY ITSELF.
    push : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
         → ⟨ map fst δ ⊨ₚ φ ⟩
         → ⟨ map fst (map CIso.I.g δ) ⊨ₚ φ ⟩
    push {n} {φ} dφ δ h =
      subst ⟨_⟩ (atπ dφ (map CIso.I.g δ))
        (subst (λ ψ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ ψ ⟩)
               (embed-map CIso.I.g φ)
               (CIso.I.iso-inv n (embed φ) δ (subst ⟨_⟩ (sym (atM dφ δ)) h)))

  -- SECTION 3.  WHAT THE CARRY PRODUCES, AT THE TWO MATRIX SHAPES.
  module Op (elem : A.Elementary) where

    module Cy = Carry elem using (push)

    -- SHAPE A: a two-slot Σ₀ matrix.  The operation commutes with the
    -- collapse at every hull member WHOSE VALUE THE HULL CONTAINS.
    commute₂ : (F : S → S) → Matrix₂ F
             → (y : S) → ⟨ y ∈ˢ HS.M ⟩ → ⟨ F y ∈ˢ HS.M ⟩
             → HS.C.π (F y) ≡ F (HS.C.π y)
    commute₂ F (fo , dfo , out , into) y y∈M Fy∈M =
      out (HS.C.π (F y)) (HS.C.π y)
          (Cy.push dfo ((F y , Fy∈M) ∷ (y , y∈M) ∷ []) (into (F y) y refl))

    -- SHAPE B, DEVLIN'S OWN.  The witness must be a hull member; that,
    -- and the value's hull membership, are the whole residue.
    commute₃ : (F : S → S) (w : Witnessed F)
             → (y : S) → ⟨ y ∈ˢ HS.M ⟩
             → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ HS.M ⟩ × ⟨ F y ∈ˢ HS.M ⟩
                           × ⟨ (F y ∷ y ∷ z ∷ []) ⊨ₚ fst w ⟩) ∥₁
             → HS.C.π (F y) ≡ F (HS.C.π y)
    commute₃ F (fo , dfo , out) y y∈M hz =
      PT.rec (isSetS (HS.C.π (F y)) (F (HS.C.π y))) go hz
      where
      go : Σ[ z ∈ S ] (⟨ z ∈ˢ HS.M ⟩ × ⟨ F y ∈ˢ HS.M ⟩
                     × ⟨ (F y ∷ y ∷ z ∷ []) ⊨ₚ fo ⟩)
         → HS.C.π (F y) ≡ F (HS.C.π y)
      go (z , z∈M , Fy∈M , h) =
        out (HS.C.π (F y)) (HS.C.π y) (HS.C.π z)
            (Cy.push dfo ((F y , Fy∈M) ∷ (y , y∈M) ∷ (z , z∈M) ∷ []) h)

  -- SECTION 4.  THE TWO INSTANCES, SIDE BY SIDE.
  module Instances (elem : A.Elementary) where

    module O = Op elem using (commute₂; commute₃)

    -- (i) CLAUSE (iii)'s `Commute`.  It carries `⟨ Lset δ ∈ˢ M ⟩` as
    -- its OWN hypothesis.  The `IsOrd (π δ)` argument is never read.
    Commute : Type (ℓ-suc ℓ)
    Commute =
      (δ : S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
      → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
      → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

    commute-from-lset-formula : Matrix₂ Lset → Commute
    commute-from-lset-formula mx δ δ∈M _ Lδ∈M =
      O.commute₂ Lset mx δ δ∈M Lδ∈M

    -- the same at Devlin's shape, where a hull witness is also owed
    LsetGrounded : Witnessed Lset → Type (ℓ-suc ℓ)
    LsetGrounded w =
      (δ : S) → ⟨ δ ∈ˢ HS.M ⟩ → ⟨ Lset δ ∈ˢ HS.M ⟩
      → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ HS.M ⟩ × ⟨ Lset δ ∈ˢ HS.M ⟩
                    × ⟨ (Lset δ ∷ δ ∷ z ∷ []) ⊨ₚ fst w ⟩) ∥₁

    commute-from-witnessed : (w : Witnessed Lset) → LsetGrounded w → Commute
    commute-from-witnessed w g δ δ∈M _ Lδ∈M =
      O.commute₃ Lset w δ δ∈M (g δ δ∈M Lδ∈M)

    -- (ii) THE DEFINABLE POWERSET, stated at a general hull member with
    -- no side condition of its own, so `DeeInHull` is the residue.
    PiCommuteD : Type (ℓ-suc ℓ)
    PiCommuteD =
      (y : S) → ⟨ y ∈ˢ HS.M ⟩ → HS.C.π (𝒟ₒ y) ≡ 𝒟ₒ (HS.C.π y)

    DeeInHull : Type (ℓ-suc ℓ)
    DeeInHull = (y : S) → ⟨ y ∈ˢ HS.M ⟩ → ⟨ 𝒟ₒ y ∈ˢ HS.M ⟩

    picommute-D-from-hull : Matrix₂ 𝒟ₒ → DeeInHull → PiCommuteD
    picommute-D-from-hull mx dh y y∈M = O.commute₂ 𝒟ₒ mx y y∈M (dh y y∈M)

    DeeGrounded : Witnessed 𝒟ₒ → Type (ℓ-suc ℓ)
    DeeGrounded w =
      (y : S) → ⟨ y ∈ˢ HS.M ⟩
      → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ HS.M ⟩ × ⟨ 𝒟ₒ y ∈ˢ HS.M ⟩
                    × ⟨ (𝒟ₒ y ∷ y ∷ z ∷ []) ⊨ₚ fst w ⟩) ∥₁

    picommute-D-from-witness : (w : Witnessed 𝒟ₒ) → DeeGrounded w → PiCommuteD
    picommute-D-from-witness w g y y∈M = O.commute₃ 𝒟ₒ w y y∈M (g y y∈M)

    -- (iii) `Commute` above is checked against [LJ-1.641]'s own module.
    commute-641 : Matrix₂ Lset → F641.Commute
    commute-641 = commute-from-lset-formula

-- =====================================================================
-- THE GENERIC UNPACK.  [LJ-1.680] Probe680.agda:48-146.  Two ∃̇ and
-- two ≐ unpacked at a generic transitive carrier, then abs₀ at a
-- generic 3-slot Δ₀ formula.
-- =====================================================================

-- Two ∃̇ bind value then parameter; two ≐ pin those binders to
-- constants; the remaining free slot is the witness.
pin₃ : {ℓc : Level} {K : Type ℓc} → Formula K 3 → K → K → Formula K 1
pin₃ φ ca cp =
  ∃̇ (∃̇ (φ ∧̇ (var zero ≐ con ca) ∧̇ (var (suc zero) ≐ con cp)))

pin₃-map : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd}
           (f : K → K') (φ : Formula K 3) (ca cp : K)
         → mapFo f (pin₃ φ ca cp) ≡ pin₃ (mapFo f φ) (f ca) (f cp)
pin₃-map f φ ca cp = refl

module Unpack (U : S) (Utr : isTrans U) where

  module Ab = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ U) Utr using (SM; abs₀; _⊨ᵐ_)

  read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Ab.SM ^ n)
       → (δ Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
  read {n} {φ} dφ δ =
      Ab.abs₀ (mapΔ₀ Empty.rec* dφ) δ
    ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = Ab.SM} fst φ (map fst δ)
    ∙ cong (λ ι → SemVᵃ.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
           (funExt (λ b → Empty.rec* b))

  unpack-pin :
      (φ : Formula Ab.SM 3)
    → (ca cp a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ φ ca cp) ⟩
    → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
         ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
         × (fst y ≡ fst ca)
         × (fst x ≡ fst cp) ) ∥₁
  unpack-pin φ ca cp a h =
    PT.rec squash₁ outer h
    where
    outer : Σ[ x ∈ Ab.SM ]
              ⟨ (x ∷ a ∷ []) Ab.⊨ᵐ
                  (∃̇ (φ ∧̇ (var zero ≐ con ca)
                         ∧̇ (var (suc zero) ≐ con cp))) ⟩
          → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
               ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
               × (fst y ≡ fst ca)
               × (fst x ≡ fst cp) ) ∥₁
    outer (x , hx) =
      PT.rec squash₁ inner hx
      where
      inner : Σ[ y ∈ Ab.SM ]
                ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ
                    (φ ∧̇ (var zero ≐ con ca)
                       ∧̇ (var (suc zero) ≐ con cp)) ⟩
            → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
                 ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
                 × (fst y ≡ fst ca)
                 × (fst x ≡ fst cp) ) ∥₁
      inner (y , hy) = ∣ y , x , hy .fst , hy .snd .fst , hy .snd .snd ∣₁

  convert-generic :
      {φ : Formula (⊥* {ℓ-suc ℓ}) 3}
    → Δ₀ φ
    → (ca cp a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ (embed φ) ca cp) ⟩
    → ⟨ (fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩
  convert-generic {φ} dφ ca cp a h =
    PT.rec (snd ((fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ)) go
           (unpack-pin (embed φ) ca cp a h)
    where
    go : Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
           ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ embed φ ⟩
           × (fst y ≡ fst ca)
           × (fst x ≡ fst cp) )
       → ⟨ (fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩
    go (y , x , hφ , ey , ex) =
      subst (λ v → ⟨ (v ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩) ey
        (subst (λ p → ⟨ (fst y ∷ p ∷ fst a ∷ []) ⊨ₚ φ ⟩) ex
          (subst ⟨_⟩ (read dφ (y ∷ x ∷ a ∷ [])) hφ))

  convert-at-true = convert-generic {φ = ⊤̇} δ-⊤

-- =====================================================================
-- THE HULL CONVERT.  [LJ-1.689] Probe689.agda:37-71, module `Convert`
-- renamed `HullConvert`.  From hull-closed's hypothesis form
-- `mapFo val (inBound ca cp)` onto the generic unpack, taking the
-- equation `mapFo val (mapFo slide φ) ≡ embed φ` as a hypothesis.
-- =====================================================================

module HullConvert (U : S) (Utr : isTrans U) where
  open Unpack U Utr hiding ( convert-generic; convert-at-true )

  inBound : {ℓc : Level} {K : Type ℓc}
          → Formula (⊥* {ℓ-suc ℓ}) 3
          → (⊥* {ℓ-suc ℓ} → K) → K → K → Formula K 1
  inBound φ slide ca cp = pin₃ (mapFo slide φ) ca cp

  hull-convert :
      {ℓc : Level} {K : Type ℓc}
      {φ : Formula (⊥* {ℓ-suc ℓ}) 3}
    → Δ₀ φ
    → (slide : ⊥* {ℓ-suc ℓ} → K)
    → (val : K → Ab.SM)
    → (eq : mapFo val (mapFo slide φ) ≡ embed φ)
    → (ca cp : K) (a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (mapFo val (inBound φ slide ca cp)) ⟩
    → ⟨ (fst (val ca) ∷ fst (val cp) ∷ fst a ∷ []) ⊨ₚ φ ⟩
  hull-convert {φ = φ} dφ slide val eq ca cp a h =
    Unpack.convert-generic U Utr {φ = φ} dφ (val ca) (val cp) a
      (subst (λ ψ → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ ψ (val ca) (val cp)) ⟩) eq
        (subst (λ ψ → ⟨ (a ∷ []) Ab.⊨ᵐ ψ ⟩)
               (pin₃-map val (mapFo slide φ) ca cp)
               h))

-- =====================================================================
-- THE WITNESS SLOT, AS SYNTAX.  [LJ-1.520] Probe520.agda:53-128
-- (`Matrix`), then [LJ-1.667] runs/W3.agda:25-97 (`W3`): the bounded
-- matrix with the twelve tag slots bounded by the witness, erased
-- onto ⊥*.  Written at the 𝒮ʟ carrier `CS.S`.
-- =====================================================================

module Matrix {m : ℕ} (w b K : Fin m)
              (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where
  private
    sh5 : Fin m → Fin (5 + m)
    sh5 i = suc (suc (suc (suc (suc i))))

    sh7 : Fin m → Fin (7 + m)
    sh7 i = suc (suc (suc (suc (suc (suc (suc i))))))

  ψs : Formula CS.S (suc (suc (suc (5 + m))))
  ψs = DefBodyB {m} (suc zero) (sh5 K)
         (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
         (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
         (sh5 N0) (sh5 N1)

  ψa : Formula CS.S (suc (suc (suc (7 + m))))
  ψa = DefBodyB {2 + m} (suc zero) (sh7 K)
         (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
         (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
         (sh7 N0) (sh7 N1)

  module G = GraphB {m} ψs ψa w b K using (graphBndAt; Δ₀-graphBndAt; module A; module S)

  Δ₀-ψs : Δ₀ ψs
  Δ₀-ψs = Δ₀-DefBodyB {m} (suc zero) (sh5 K)
            (sh5 N0) (sh5 N1) (sh5 N2) (sh5 N3) (sh5 N4) (sh5 N5)
            (sh5 N6) (sh5 N7) (sh5 N8) (sh5 N9) (sh5 N10) (sh5 N11)
            (sh5 N0) (sh5 N1)

  Δ₀-ψa : Δ₀ ψa
  Δ₀-ψa = Δ₀-DefBodyB {2 + m} (suc zero) (sh7 K)
            (sh7 N0) (sh7 N1) (sh7 N2) (sh7 N3) (sh7 N4) (sh7 N5)
            (sh7 N6) (sh7 N7) (sh7 N8) (sh7 N9) (sh7 N10) (sh7 N11)
            (sh7 N0) (sh7 N1)

  -- K IS TRANSITIVE.
  transK : Formula CS.S m
  transK = ∀̇∈ (var K) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc K))))

  Δ₀-transK : Δ₀ transK
  Δ₀-transK = δ-∀∈ (δ-∀∈ δ-∈)

  -- THE TWELVE TAG SLOTS HOLD THE TWELVE NUMERALS, in the object
  -- language: N0 is empty, each next slot is the successor.
  pins : Formula CS.S m
  pins = ∀̇∈ (var N0) ⊥̇
       ∧̇ ( sucAtL N0 N1 ∧̇ ( sucAtL N1 N2 ∧̇ ( sucAtL N2 N3
       ∧̇ ( sucAtL N3 N4 ∧̇ ( sucAtL N4 N5 ∧̇ ( sucAtL N5 N6
       ∧̇ ( sucAtL N6 N7 ∧̇ ( sucAtL N7 N8 ∧̇ ( sucAtL N8 N9
       ∧̇ ( sucAtL N9 N10 ∧̇ sucAtL N10 N11 ))))))))))

  Δ₀-pins : Δ₀ pins
  Δ₀-pins =
    δ-∧ (δ-∀∈ δ-⊥)
      (δ-∧ (Δ₀-sucAtL N0 N1) (δ-∧ (Δ₀-sucAtL N1 N2) (δ-∧ (Δ₀-sucAtL N2 N3)
      (δ-∧ (Δ₀-sucAtL N3 N4) (δ-∧ (Δ₀-sucAtL N4 N5) (δ-∧ (Δ₀-sucAtL N5 N6)
      (δ-∧ (Δ₀-sucAtL N6 N7) (δ-∧ (Δ₀-sucAtL N7 N8) (δ-∧ (Δ₀-sucAtL N8 N9)
      (δ-∧ (Δ₀-sucAtL N9 N10) (Δ₀-sucAtL N10 N11)))))))))))

  -- THE WHOLE MATRIX, AND IT IS Δ₀.
  matrix : Formula CS.S m
  matrix = transK ∧̇ ( pins ∧̇ G.graphBndAt )

  Δ₀-matrix : Δ₀ matrix
  Δ₀-matrix = δ-∧ Δ₀-transK (δ-∧ Δ₀-pins (G.Δ₀-graphBndAt Δ₀-ψs Δ₀-ψa))

module W3 where

  -- Innermost environment, fifteen slots: n0..n11, a, p, z.  After
  -- twelve bounded existentials over z: a, p, z, which is
  -- Witnessed's (value ∷ parameter ∷ witness).
  private
    n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 ww bb kk : Fin 15
    n0  = zero
    n1  = suc zero
    n2  = suc (suc zero)
    n3  = suc (suc (suc zero))
    n4  = suc (suc (suc (suc zero)))
    n5  = suc (suc (suc (suc (suc zero))))
    n6  = suc (suc (suc (suc (suc (suc zero)))))
    n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
    n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    ww  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    bb  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
    kk  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))

  module Mx = Matrix {15} ww bb kk n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 using (matrix; Δ₀-matrix)

  lastFin : {n : ℕ} → Fin (suc n)
  lastFin {zero} = zero
  lastFin {suc n} = suc (lastFin {n})

  -- Result arity is `suc n`, so the bound term's last slot is `lastFin {n}`.
  wrap : {n : ℕ} → Formula CS.S (suc (suc n)) → Formula CS.S (suc n)
  wrap {n} φ = ∃̇∈ (var (lastFin {n})) φ

  δ-wrap : {n : ℕ} {φ : Formula CS.S (suc (suc n))} → Δ₀ φ → Δ₀ (wrap {n} φ)
  δ-wrap d = δ-∃∈ d

  -- Twelve bounded existentials, outermost env a ∷ p ∷ z.
  inner = Mx.matrix
  s14 = wrap {13} inner
  s13 = wrap {12} s14
  s12 = wrap {11} s13
  s11 = wrap {10} s12
  s10 = wrap {9}  s11
  s9  = wrap {8}  s10
  s8  = wrap {7}  s9
  s7  = wrap {6}  s8
  s6  = wrap {5}  s7
  s5  = wrap {4}  s6
  s4  = wrap {3}  s5
  three : Formula CS.S 3
  three = wrap {2} s4

  Δ₀-three : Δ₀ three
  Δ₀-three =
    δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap
      (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap Mx.Δ₀-matrix)))))))))))

  count-three : countFo three ≡ 0
  count-three = refl

  -- Erase onto the parameter-free alphabet Witnessed uses.
  erased : Formula (⊥* {ℓ-suc ℓ}) 3
  erased = Cnt.erase three count-three

  Δ₀-erased : Δ₀ erased
  Δ₀-erased = erase-Δ₀ three count-three Δ₀-three

  syntax₃ : Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 3 ] Δ₀ φ
  syntax₃ = erased , Δ₀-erased

-- Ordinality of the parameter, as a 3-slot conjunct, p at slot 1.
isOrd-at-p : Formula (⊥* {ℓ-suc ℓ}) 3
isOrd-at-p =
    (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc (suc zero))))))
  ∧̇ (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero)
        (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-isOrd-at-p : Δ₀ isOrd-at-p
Δ₀-isOrd-at-p = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

-- =====================================================================
-- THE LEFTOVER EQUATION.  [LJ-1.686] Probe686.agda:34-55, module `At`
-- renamed `EmbedAt`.  `mapFo val (mapFo slide φ) ≡ embed φ` by
-- mapFo-comp and uniqueness of maps out of ⊥*.
-- =====================================================================

lemma : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd} {n : ℕ}
        (φ : Formula (⊥* {ℓ-suc ℓ}) n)
        (slide : ⊥* {ℓ-suc ℓ} → K)
        (val : K → K')
      → mapFo val (mapFo slide φ) ≡ embed φ
lemma φ slide val =
    mapFo-comp slide val φ
  ∙ cong (λ h → mapFo h φ) (funExt (λ b → Empty.rec* b))

```
