{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- [L3.32-T2] D-1 probe: the fresh-generic Sigma-1 face (gates 1 and 2
-- fused).  Untracked; no master touched; Everything untouched.
--
-- Subject: the ruled architecture's central bet.  The GCH wing's W1 IS a
-- fresh Sigma-1 face for the L-tower's level story, written
-- CARRIER-GENERIC from birth and instantiated where each consumer needs
-- it.  This probe builds the smallest honest version of that face:
--
--     σ(x) := ∃ f ∈ K(u) [ Cl(f,x) ∧ Rg(f,x) ]
--
-- "x is in the range of some L-tower initial segment lying in the
-- carrier", reduced to ONE Def-step clause (Cl, the object formula whose
-- adequacy against the meta-level Def-step DefStep is the tower content)
-- with its K(u)-binding witness (the bounded existential over the
-- binding set K(u), a member of the carrier) plus the range read (Rg,
-- whose adequacy against the meta-level range read is the tower
-- content).  The whole tower story (the 0-step, the limit step, the
-- functionhood and domain machinery) is deliberately not built.
--
-- The face is written ONCE (module FaceSigma), with the carrier a module
-- parameter (P-h at full strength) and the tower content (Cl, Rg and
-- the two adequacies c-ok/r-ok) as recorded hypotheses.  It is
-- instantiated at TWO carriers:
--   ARM A (gate 2, the face's statement layer): the GENERIC carrier,
--     ONE adequacy direction against the delivered defSet face;
--   ARM B (gate 1, the bridge's L-sigma): the RUD carrier ⟪ Sset C ⟫,
--     TWO-WAY adequacy against DefOf.defSet.
------------------------------------------------------------------------

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeFace {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; con; var; _∈̇_; _∧̇_; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Rud.Step {ℓ} lem A using ( Sset )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( _×_; _,_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Carrier-level bidirectional combinator (I-4: state bidirectional
-- claims over the carriers, never through content-of applied to a
-- defined hProp operator).
infix 1 _⟷_
_⟷_ : Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ) → Type (ℓ-suc ℓ)
A ⟷ B = (A → B) × (B → A)

infix 5 _∈ran_

-- THE RANGE READ, at the meta level: x ∈ ran f iff some a has pr a x ∈ f.
_∈ran_ : V ℓ → V ℓ → Type (ℓ-suc ℓ)
x ∈ran f = ∥ Σ[ a ∈ V ℓ ] ⟨ pr a x ∈ˢ f ⟩ ∥₁

-- THE ONE DEF-STEP CLAUSE, at the meta level: f is a definable set at
-- some member w of the carrier (the successor/Def step of the tower
-- story in Devlin's initial-segment formula, dev6.txt:1665-1678).  The
-- K(u)-binding witness is the bounded existential in σ; w ∈ u is the
-- carrier binding.
DefStep : V ℓ → V ℓ → Type (ℓ-suc ℓ)
DefStep u f = ∥ Σ[ w ∈ V ℓ ] Σ[ φ ∈ Formula ⟪ w ⟫ 1 ]
                ( ⟨ w ∈ˢ u ⟩ × (DefOf.defSet w φ ≡ f) ) ∥₁

------------------------------------------------------------------------
-- THE GENERIC FACE, ONCE.  P-h at full strength: the carrier u, the
-- K(u)-binding set K (a small index, R-35), and the two object-language
-- formulas Cl (the Def-step clause) and Rg (the range read) are module
-- parameters; the face never mentions a concrete carrier body or a
-- concrete tower body.
------------------------------------------------------------------------

module FaceSigma (u : V ℓ) (K : ⟪ u ⟫)
                 (Cl Rg : Formula ⟪ u ⟫ 2) where

  module U = DefOf u
  open U using ( SM; ι; _⊨ᵐ_; defSet; defSet-mem )

  σ : Formula ⟪ u ⟫ 1
  σ = ∃̇∈ (con K) (Cl ∧̇ Rg)

  Payload : ⟪ u ⟫ → Type (ℓ-suc ℓ)
  Payload x = Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                          × ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩
                          × ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩ )

  -- The two readings: a satisfied bounded existential IS the truncated
  -- sigma of the K-binding, the clause and the range read (hPropAlgebra
  -- clauses).  D-16's inner-world discipline: the "f lies in u" conjunct
  -- is carried by SM itself and never written down.
  σ-in : (x : ⟪ u ⟫) (f : SM)
       → ⟨ fst f ∈ˢ fst (ι K) ⟩ → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
       → ⟨ (ι x ∷ []) ⊨ᵐ σ ⟩
  σ-in x f hK hCl hRg = ∣ f , (hK , (hCl , hRg)) ∣₁

  σ-out : (x : ⟪ u ⟫) → ⟨ (ι x ∷ []) ⊨ᵐ σ ⟩ → ∥ Payload x ∥₁
  σ-out x h = h

  -- Adequacy against the delivered defSet face and the external reading.
  -- The tower content enters here and ONLY here: the object-language
  -- clause and range read must mean the meta-level DefStep and the
  -- meta-level range.  c-ok/r-ok are the face's recorded hypotheses
  -- (the tower readers' adequacy, priced separately); everything else
  -- below is hypothesis-free (no transitivity, no rud-closure, no LEM).
  module Adeq (c-ok : (f : SM) (x : ⟪ u ⟫)
                     → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ ⟷ DefStep u (fst f))
              (r-ok : (f : SM) (x : ⟪ u ⟫)
                     → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩ ⟷ (⟪ u ⟫↪ x) ∈ran (fst f)) where

    Elem : ⟪ u ⟫ → Type (ℓ-suc ℓ)
    Elem x = ∥ Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                           × DefStep u (fst f)
                           × ((⟪ u ⟫↪ x) ∈ran fst f) ) ∥₁

    -- Direction 1 (ARM A's direction): out of the defSet face.
    face-in : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩ → Elem m
    face-in m h = PT.map step (σ-out m (subst ⟨_⟩ (defSet-mem σ m) h))
      where
      step : Payload m
           → Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                          × DefStep u (fst f)
                          × ((⟪ u ⟫↪ m) ∈ran fst f) )
      step (f , hK , hCl , hRg) =
        f , ( hK , (c-ok f m .fst hCl , r-ok f m .fst hRg) )

    -- Direction 2: into the defSet face.
    face-out : (m : ⟪ u ⟫) → Elem m → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩
    face-out m = PT.rec (snd (⟪ u ⟫↪ m ∈ˢ defSet σ)) go
      where
      go : Σ[ f ∈ SM ] ( ⟨ fst f ∈ˢ fst (ι K) ⟩
                        × DefStep u (fst f)
                        × ((⟪ u ⟫↪ m) ∈ran fst f) )
         → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩
      go (f , hK , hDef , hRan) =
        subst ⟨_⟩ (sym (defSet-mem σ m))
          (σ-in m f hK (c-ok f m .snd hDef) (r-ok f m .snd hRan))

    -- The two-way adequacy, packaged.
    face-iff : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet σ ⟩ ⟷ Elem m
    face-iff m = face-in m , face-out m

------------------------------------------------------------------------
-- ARM A (gate 2): the face's statement layer at the GENERIC carrier,
-- ONE adequacy direction against the delivered defSet face.
------------------------------------------------------------------------

module ArmA (u : V ℓ) (K : ⟪ u ⟫)
            (Cl Rg : Formula ⟪ u ⟫ 2) where

  module U = DefOf u
  open U using ( ι; _⊨ᵐ_; defSet )
  module F = FaceSigma u K Cl Rg

  module AdeqA (c-ok : (f : U.SM) (x : ⟪ u ⟫)
                      → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩ ⟷ DefStep u (fst f))
               (r-ok : (f : U.SM) (x : ⟪ u ⟫)
                      → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩ ⟷ (⟪ u ⟫↪ x) ∈ran (fst f)) where
    module A = F.Adeq c-ok r-ok

    face-to-Elem : (m : ⟪ u ⟫) → ⟨ ⟪ u ⟫↪ m ∈ˢ defSet F.σ ⟩ → A.Elem m
    face-to-Elem = A.face-in

------------------------------------------------------------------------
-- ARM B (gate 1): the bridge's L-sigma at the RUD carrier ⟪ Sset C ⟫,
-- TWO-WAY adequacy against DefOf.defSet.
------------------------------------------------------------------------

module ArmB (C₀ : V ℓ) (K : ⟪ Sset C₀ ⟫)
            (Cl Rg : Formula ⟪ Sset C₀ ⟫ 2) where

  module U = DefOf (Sset C₀)
  open U using ( ι; _⊨ᵐ_; defSet )
  module F = FaceSigma (Sset C₀) K Cl Rg

  module AdeqB (c-ok : (f : U.SM) (x : ⟪ Sset C₀ ⟫)
                      → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Cl ⟩
                        ⟷ DefStep (Sset C₀) (fst f))
               (r-ok : (f : U.SM) (x : ⟪ Sset C₀ ⟫)
                      → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ Rg ⟩
                        ⟷ (⟪ Sset C₀ ⟫↪ x) ∈ran (fst f)) where
    module A = F.Adeq c-ok r-ok

    two-way : (m : ⟪ Sset C₀ ⟫)
            → ⟨ ⟪ Sset C₀ ⟫↪ m ∈ˢ defSet F.σ ⟩ ⟷ A.Elem m
    two-way = A.face-iff

------------------------------------------------------------------------
-- C-6 perturbation controls.
--   * POSITIVE: the readings are content-free.  At the generic carrier
--     the same clause checks for a NON-story garbage formula pair, so
--     nothing about the Def-step or the range content is used by it.
--   * NEGATIVE (run during development, then removed): σ-out at the
--     swapped conjunct order, σ-in dropping the K-binding conjunct, and
--     face-in without r-ok are all rejected by the typechecker; the
--     claim "the adequacy consumes no hypotheses" is refuted by
--     construction, c-ok/r-ok being in the Adeq telescope.
------------------------------------------------------------------------

module Perturb (u : V ℓ) (K : ⟪ u ⟫) where

  module U = DefOf u
  open U using ( ι; _⊨ᵐ_ )

  junk1 junk2 : Formula ⟪ u ⟫ 2
  junk1 = var zero ∈̇ var zero
  junk2 = var (suc zero) ∈̇ var zero

  module J = FaceSigma u K junk1 junk2

  ctl-in : (x : ⟪ u ⟫) (f : U.SM) → ⟨ fst f ∈ˢ fst (ι K) ⟩
         → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ junk1 ⟩ → ⟨ (f ∷ ι x ∷ []) ⊨ᵐ junk2 ⟩
         → ⟨ (ι x ∷ []) ⊨ᵐ J.σ ⟩
  ctl-in x f hK h1 h2 = J.σ-in x f hK h1 h2

  ctl-out : (x : ⟪ u ⟫) → ⟨ (ι x ∷ []) ⊨ᵐ J.σ ⟩ → ∥ J.Payload x ∥₁
  ctl-out x h = J.σ-out x h
