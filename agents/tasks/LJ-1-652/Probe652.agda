{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.652] PROBE.  Does the collapse commute with the definable
-- powerset ONCE ELEMENTARITY IS IN HAND.  It runs in
-- agents/tasks/LJ-1-652/ and lands nothing in src/.
--
-- Nothing is postulated.  The file carries --safe and no hole.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-652.Probe652 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling
  using ( embed; embed-⊨; mapΔ₀; mapFo; mapFo-comp )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Collapse {ℓ} using ( isExt; isTrans )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module CollapseIso; module HullExt )
open import LJ-1-641.Probe641 {ℓ} lem using ( module Frame )

open import Cubical.Data.Vec using ( map; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemVᵃ = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemVᵃ using ( _^_ )

-- The ambient parameter-free reading, the shape of `Amb`
-- (src/L/BoundedSubset.lagda.md:807-811) restated at this file.
module AtP = SemVᵃ.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b)

_⊨ₚ_ : {n : ℕ} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
_⊨ₚ_ = AtP._⊨_

-- A parameter-free formula is FIXED by every relabelling: `embed` has
-- already sent the empty constant domain everywhere, and there is
-- nothing left for `f` to move.  Used at three different `f` below.
embed-map : {ℓ₁ ℓ₂ : Level} {K : Type ℓ₁} {K' : Type ℓ₂} (f : K → K')
            {n : ℕ} (φ : Formula (⊥* {ℓ-suc ℓ}) n)
          → mapFo f (embed φ) ≡ embed φ
embed-map f φ =
    mapFo-comp Empty.rec* f φ
  ∙ cong (λ h → mapFo h φ) (funExt (λ b → Empty.rec* b))

-- [LJ-1.651]'S DELIVERABLE, READ AT A UNARY OPERATION.  A Σ₀ matrix
-- that carries its parameter in a SLOT and holds exactly of the
-- operation's value at that parameter.  `lset-formula` is `Matrix₂
-- Lset` and the brief's "𝒟ₒ counterpart" is `Matrix₂ 𝒟ₒ`.
--
-- D-10, AND IT IS NOT MY OBLIGATION'S TRUTH THAT IS AT RISK BUT THIS
-- HYPOTHESIS'S.  The literature says the two-slot form does NOT exist:
-- dev/literature/devlin-II5.md:95 gives "there is a Σ₀ formula
-- Φ(z, v, γ)" WITH A WITNESS SLOT, and the graph is `∃z Φ`, which is
-- Σ₁ and not Δ₀.  `Witnessed` below is that true shape, and every
-- consumer here is built at BOTH, so nothing in this file depends on
-- which one [LJ-1.651] can deliver.
Matrix₂ : (S → S) → Type (ℓ-suc ℓ)
Matrix₂ F =
  Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 2 ]
    ( Δ₀ φ
    × ((a p : S) → ⟨ (a ∷ p ∷ []) ⊨ₚ φ ⟩ → a ≡ F p)
    × ((a p : S) → a ≡ F p → ⟨ (a ∷ p ∷ []) ⊨ₚ φ ⟩) )

-- DEVLIN'S OWN SHAPE.  dev/literature/devlin-II5.md:95 states the Σ₀
-- form the literature actually has: "there is a Σ₀ formula Φ(z, v, γ)",
-- with a WITNESS slot `z` beside the value and the parameter.  The
-- soundness half stays outright; the completeness half is not part of
-- the matrix, because producing a witness is what the consumer must do.
Witnessed : (S → S) → Type (ℓ-suc ℓ)
Witnessed F =
  Σ[ φ ∈ Formula (⊥* {ℓ-suc ℓ}) 3 ]
    ( Δ₀ φ
    × ((a p z : S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ φ ⟩ → a ≡ F p) )

-- =====================================================================
-- THE FRAME.  One hull stage, the telescope of
-- src/L/BoundedSubset.lagda.md:903-914 verbatim, plus the inner world
-- `AtM` that carries `Elementary` (src/L/Hull.lagda.md:174-175).
-- =====================================================================

module Frame652 (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module F641 = Frame lam ordλ succλ X X⊆Lλ ∅∈λ
  module ASt = HS.ASt
  module A = ASt.AtM HS.M HS.H.Hull⊆L

  -- ===================================================================
  -- SECTION 1.  THE READING OF A Σ₀ MATRIX AT A TRANSITIVE CARRIER.
  -- Written ONCE at a generic carrier (W2), instantiated twice below.
  -- ===================================================================

  module AtTrans (U : S) (Utr : isTrans U) where

    module Ab = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ U) Utr

    read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Ab.SM ^ n)
         → (δ Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    read {n} {φ} dφ δ =
        Ab.abs₀ (mapΔ₀ Empty.rec* dφ) δ
      ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = Ab.SM} fst φ (map fst δ)
      ∙ cong (λ ι → SemVᵃ.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
             (funExt (λ b → Empty.rec* b))

  -- ===================================================================
  -- SECTION 2.  THE CARRY.  AMBIENT TRUTH AT HULL MEMBERS BECOMES
  -- AMBIENT TRUTH AT THEIR COLLAPSE VALUES.
  --
  --   THIS IS THE WHOLE OF WHAT ELEMENTARITY BUYS, and it is generic in
  --   the arity and in the Σ₀ formula (W2): every consumer below is one
  --   instantiation and nothing is copied.  Three steps.
  --
  --     (1) DOWN INTO THE HULL, by `elem`.  The hull is NOT transitive,
  --         so Δ₀ absoluteness is unavailable here and elementarity is
  --         exactly what replaces it.  This is [LJ-1.489]'s missing
  --         ingredient, spent (its report, :139-140).
  --     (2) ACROSS, by the collapse iso `iso-inv`
  --         (src/L/BoundedSubset.lagda.md:195-196).  Satisfaction is
  --         invariant under an ∈-isomorphism, at every formula.
  --     (3) OUT OF THE COLLAPSE, by Δ₀ absoluteness again: the
  --         collapse's range IS transitive (`πX-trans`,
  --         src/V/Collapse.lagda.md:89).
  --
  --   THE SITE'S EXTENSIONALITY IS NOT A HYPOTHESIS.  `hullExt`
  --   (src/L/BoundedSubset.lagda.md:1340) is green in the tree, so the
  --   collapse iso costs this file nothing.
  -- ===================================================================

  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ

  Mext : isExt HS.M
  Mext = HE.hullExt

  module Carry (elem : A.Elementary) where

    module CIso = CollapseIso HS.M Mext
    module TL = AtTrans (Lset lam) ASt.Ltr
    module Tπ = AtTrans HS.C.πX HS.C.πX-trans

    -- (1) at the STAGE, and (3) at the COLLAPSE: one lemma, two carriers.
    atL : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : ASt.SL ^ n)
        → (δ ASt.AbsL.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atL dφ δ = TL.read dφ δ

    atπ : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Tπ.Ab.SM ^ n)
        → (δ Tπ.Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atπ dφ δ = Tπ.read dφ δ

    -- (2) at the HULL, through elementarity.
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

  -- ===================================================================
  -- SECTION 3.  WHAT THE CARRY PRODUCES, AT THE TWO MATRIX SHAPES.
  -- ===================================================================

  module Op (elem : A.Elementary) where

    module Cy = Carry elem

    -- SHAPE A, the brief's reading of [LJ-1.651]: a two-slot Σ₀ matrix.
    -- The operation commutes with the collapse at every hull member
    -- WHOSE VALUE THE HULL CONTAINS, and that side condition is the
    -- only thing the carry does not supply.
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

  -- ===================================================================
  -- SECTION 4.  THE TWO INSTANCES THE BRIEF NAMES, SIDE BY SIDE.
  --
  --   ONE PROOF, TWO OPERATIONS, TWO DIFFERENT ANSWERS, AND THE
  --   DIFFERENCE IS NOT THE MATHEMATICS.  It is that clause (iii)'s
  --   `Commute` CARRIES ITS SIDE CONDITION IN ITS OWN TYPE and the
  --   obligation of this task does not.
  -- ===================================================================

  module Instances (elem : A.Elementary) where

    module O = Op elem

    -- ---- (i) CLAUSE (iii)'s `Commute`.  IT CLOSES. ------------------
    -- The type is [LJ-1.641]'s, verbatim from
    -- agents/tasks/LJ-1-641/Probe641.agda:69-73.  It carries
    -- `⟨ Lset δ ∈ˢ M ⟩` as its OWN hypothesis, so `commute₂`'s one side
    -- condition is already paid inside the statement.  The
    -- `IsOrd (π δ)` argument is never read.
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

    -- ---- (ii) THIS TASK'S OBLIGATION, AND WHAT IT STILL OWES. -------
    -- The type is [LJ-1.489]'s `PiCommuteD`, verbatim from
    -- agents/tasks/LJ-1-489/Probe489.agda:139-141.
    PiCommuteD : Type (ℓ-suc ℓ)
    PiCommuteD =
      (y : S) → ⟨ y ∈ˢ HS.M ⟩ → HS.C.π (𝒟ₒ y) ≡ 𝒟ₒ (HS.C.π y)

    -- THE RESIDUE, AND IT IS THE ONLY ONE.  The obligation is stated at
    -- a GENERAL hull member and carries no side condition of its own,
    -- so nothing inside it pays `commute₂`'s.
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

    -- AND THE RESIDUE IS NOT A RESTATEMENT OF THE OBLIGATION.  It names
    -- no `π` at all, so [LJ-1.648]'s language argument
    -- (review-of-commute-from-keystone.md, part 3) does NOT bite on it:
    -- `hull-closed` (src/L/Hull.lagda.md:415) can in principle answer a
    -- search whose condition names only `𝒟ₒ` and a hull member.

    -- ---- (iii) THE TYPE IS NOT MY TRANSCRIPTION.  ------------------
    -- `Commute` above is checked against [LJ-1.641]'s own module rather
    -- than against my copy of its lines, so the claim in (i) is decided
    -- by Agda and not by a reader comparing two texts.
    commute-641 : Matrix₂ Lset → F641.Commute
    commute-641 = commute-from-lset-formula
