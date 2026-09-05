{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.611]  FACE G-, THE AMBIENT DECODE: NOT SUPPLIED, AND THE STOP
-- IS STATED.  The obligation is ONE term,
--
--   graph-ambient : GraphAmbient   (agents/tasks/LJ-1-606/Probe606.agda:168-172)
--
-- the face [LJ-1.606] named as "Devlin (a); [LJ-1.160]'s crossOut made
-- concrete".  The name is ABSENT from this file on purpose, and the
-- meter will say MISSING.  The stop is stated at
-- agents/tasks/LJ-1-611/review-of-graph-ambient.md.  What this probe
-- delivers instead, every piece green:
--
--   S1  the face, restated letter for letter (the W3 type, measured
--       alone first at runs/W3.agda: exit 0, 2.74 s, peak 672,088,064
--       bytes, runs/w3-2.out);
--   S2  the delivery shape the kit's own currency forces (a named
--       matrix), and TWO junk admissions as terms: the psi-quantified
--       misreading is REFUTED (a true matrix fails the face, the port
--       of [LJ-1.606]'s Top-fails-G-, Probe606.agda:262-273), and the
--       Sigma letter alone is satisfied VACUOUSLY by the false matrix;
--   S3  the corrected target: the face at a LIVE matrix, satisfiable
--       at every ordinal index.  That is the soundness half of the
--       level-graph adequacy, and it is what no delivered reading
--       reaches: see the report and the review file;
--   S4  what [LJ-1.160]'s crossOut already gives, AS A TERM: G-
--       supplies the concrete crossOut at the collapse image outright
--       and is strictly stronger (its telescope drops both containment
--       hypotheses and pins the level at the AMBIENT ordinal index).
--
-- WHY THE HONEST SUPPLIER IS NOT HERE.  The ambient reading of the
-- matrix is the satisfaction at AbsπX.SemV, the FULL ambient carrier:
-- every existential ranges over every ambient set and the environment
-- (x, v, gamma) is arbitrary.  Every adequacy the tree delivers for a
-- level-graph formula is the INNER satisfaction at S = the carrier of
-- S_ʟ, whose existentials range over L only (the DefOK gap,
-- src/L/Coding/Powerset.lagda.md:295-326), and the bounded Delta-zero
-- restatement's adequacy is conditional on the certificate frame's
-- site-facts telescope (LeafAgree, src/L/Condensation.lagda.md:7216).
-- [LJ-1.598] priced the INNER determination NO-GO on the formula side
-- (agents/tasks/LJ-1-598/lj-1.598-report.md, VERDICT); the ambient one
-- is strictly stronger than that.  A green graph-ambient today could
-- only be the vacuous or the index-pinned junk of S2, which the kit's
-- own G+ face refutes (Probe606.agda:275-285), and the brief forbids
-- exactly that delivery.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.  No
-- `graph-ambient` name anywhere in this file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-611.Probe611 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇; ⊥̇ )
open import FOL.LevyHierarchy using ( Δ₀; δ-⊤; δ-⊥ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ∅-ord )
open import V.Model {ℓ} using ( self∈sucV )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module HullExt; module CollapseIso )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ∅-empty )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( _∷_; [] )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_; isSetS )

-- =====================================================================
-- THE FRAME.  [LJ-1.606]'s six hull slots with the two modules face G-
-- spends: the hull stage, its extensionality, the collapse iso, and the
-- absoluteness machine at the transitive collapse image.  Nothing from
-- any probe enters this file.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CI = CollapseIso HS.M HE.hullExt
  module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ
                 (λ x → x ∈ˢ HS.C.πX) HS.C.πX-trans

  -- ===================================================================
  -- SECTION 1.  THE FACE, RESTATED.  [LJ-1.606]'s GraphAmbient letter
  -- for letter (Probe606.agda:168-172).  This is the W3 type
  -- (runs/W3.agda), crossOut re-ascribed: the abstract Bel becomes the
  -- ambient reading of the relabelled matrix, the witness takes the
  -- first slot, both containment hypotheses are gone, and psi stays a
  -- parameter because crossOut never chose one.
  -- ===================================================================

  GraphAmbient : Formula CI.I.SM 3 → Type (ℓ-suc ℓ)
  GraphAmbient ψ =
    (x v γ : SV.S) → IsOrd γ
    → ⟨ (x ∷ v ∷ γ ∷ []) AbsπX.⊨ᵛ mapFo CI.I.g ψ ⟩
    → v ≡ Lset γ

  -- ===================================================================
  -- SECTION 2.  THE DELIVERY SHAPE, AND THE TWO JUNK ADMISSIONS.
  --
  -- The kit's currency is a Sigma over the matrix, so a supplier NAMES
  -- psi; G- alone cannot be read as "for every psi", and the two terms
  -- below fence exactly that.
  -- ===================================================================

  G-face : Type (ℓ-suc ℓ)
  G-face = Σ[ ψ ∈ Formula CI.I.SM 3 ] (Δ₀ ψ × GraphAmbient ψ)

  -- JUNK ADMISSION ONE, REFUTATION.  The psi-quantified reading is
  -- FALSE: a TRUE matrix fails the face outright, because at the
  -- ordinal index EMPTY it would force every set to be the tower's
  -- value there, so EMPTY equals its own successor and the empty set
  -- would be a member of itself.  [LJ-1.606]'s Top-fails-G-
  -- (Probe606.agda:262-273), ported at this frame.
  quantified-refuted
    : ((ψ : Formula CI.I.SM 3) → Δ₀ ψ → GraphAmbient ψ) → Empty.⊥
  quantified-refuted all = ∅-empty ∅ (∈∈ₛ {a = ∅} {b = ∅} .fst ∅∈∅)
    where
    gamb : GraphAmbient ⊤̇
    gamb = all ⊤̇ δ-⊤
    e₁ : ∅ ≡ Lset ∅
    e₁ = gamb ∅ ∅ ∅ ∅-ord tt*
    e₂ : sucV ∅ ≡ Lset ∅
    e₂ = gamb ∅ (sucV ∅) ∅ ∅-ord tt*
    ∅≡sucV : ∅ ≡ sucV ∅
    ∅≡sucV = e₁ ∙ sym e₂
    ∅∈∅ : ⟨ ∅ ∈ˢ ∅ ⟩
    ∅∈∅ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym ∅≡sucV) (self∈sucV ∅)

  -- JUNK ADMISSION TWO, THE LETTER IS WEAK.  The Sigma letter ALONE is
  -- satisfied vacuously: the FALSE matrix carries Delta-zero for free
  -- and its ambient reading is the algebra's BOTTOM, so the face holds
  -- with no content at all.  This is the same measurement [LJ-1.598]
  -- made one clause over (only-level-vacuous,
  -- agents/tasks/LJ-1-598/Probe598.agda:104): the conjunct alone is
  -- free, and the content lives only under a satisfiable formula.
  vacuous-junk : G-face
  vacuous-junk = ⊥̇ , δ-⊥ , (λ x v γ oγ h → Empty.rec* h)

  -- ===================================================================
  -- SECTION 3.  THE CORRECTED TARGET.  A matrix that fills the kit must
  -- be LIVE: satisfiable at every ordinal index, which is G+'s witness
  -- content read at the ambient.  The false matrix fails it at the
  -- first ordinal, by the term below, and an index-pinned matrix (one
  -- that names the level by constants) fails it at every other index.
  -- Honest-G- is therefore exactly the soundness half of the
  -- level-graph adequacy, and it is the named residue this task stops
  -- at: no delivered reading reaches the ambient side of it.  See
  -- agents/tasks/LJ-1-611/review-of-graph-ambient.md.
  -- ===================================================================

  G-live : Formula CI.I.SM 3 → Type (ℓ-suc ℓ)
  G-live ψ = (γ : SV.S) → IsOrd γ
           → ∥ Σ[ x ∈ SV.S ] Σ[ v ∈ SV.S ]
                ⟨ (x ∷ v ∷ γ ∷ []) AbsπX.⊨ᵛ mapFo CI.I.g ψ ⟩ ∥₁

  Honest-G- : Type (ℓ-suc ℓ)
  Honest-G- = Σ[ ψ ∈ Formula CI.I.SM 3 ]
                (Δ₀ ψ × GraphAmbient ψ × G-live ψ)

  vacuous-fails-live : G-live ⊥̇ → Empty.⊥
  vacuous-fails-live gl =
    PT.rec (Empty.isProp⊥)
      (λ { (x , (v , h)) → Empty.rec* h }) (gl ∅ ∅-ord)

  -- ===================================================================
  -- SECTION 4.  WHAT crossOut ALREADY GIVES, AS A TERM.  [LJ-1.160]'s
  -- crossOut (agents/tasks/LJ-1-160/ProbeLJ1160A.agda:71-72), at the
  -- abstract Bel:
  --
  --    (v b : S) -> < v in P > -> < b in P > -> IsOrd b -> Bel v b
  --               -> v == Lset b
  --
  -- Made concrete at this frame: P is the collapse image, and Bel v b
  -- is the truncated ambient reading of the relabelled matrix with a
  -- witness.  G- supplies it outright, and G- is STRICTLY STRONGER:
  -- its telescope drops both containment hypotheses (arbitrary ambient
  -- v and b) and needs no truncation of the belief.  What "made
  -- concrete" ADDS is therefore the missing half: not the implication
  -- (that is the re-ascription, and it is what the junk terms cannot
  -- honestly supply), but the MATRIX psi whose ambient reading carries
  -- the tower's recursion.
  -- ===================================================================

  BelC : Formula CI.I.SM 3 → SV.S → SV.S → Type (ℓ-suc ℓ)
  BelC ψ v b = ∥ Σ[ x ∈ SV.S ]
                 ⟨ (x ∷ v ∷ b ∷ []) AbsπX.⊨ᵛ mapFo CI.I.g ψ ⟩ ∥₁

  crossOut-from-G- : (ψ : Formula CI.I.SM 3) → GraphAmbient ψ
                   → (v b : SV.S) → IsOrd b → BelC ψ v b → v ≡ Lset b
  crossOut-from-G- ψ gamb v b ob =
    PT.rec (isSetS v (Lset b)) (λ { (x , h) → gamb x v b ob h })

  -- The concrete crossOut, for comparison, is [LJ-1.160]'s Reroute
  -- hypothesis restated at this frame with Bel instantiated.  It
  -- CANNOT be turned around: nothing at this site reads an ambient
  -- satisfaction back into the machine's inner reading, which is the
  -- finding the review file states.
