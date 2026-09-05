{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.665]  The certificate's remaining debt, counted as one type.
--
--   THE OBLIGATION is `certificate-remainder`.  It inhabits THIS WEEK'S
--   three-clause object, not [LJ-1.578]'s original `Certificate`.
--   Section 2 names the three bridges that original still asks for.
--   Nothing in this file inhabits a clause: the three conjuncts are
--   produced from predecessors that already closed them, plus the
--   hypotheses those closures still carry.
--
--   W3 IS runs/W3.agda, typechecked ALONE first (runs/w3-1.out).
--   THE FLOOR is runs/FLOOR.agda.txt (runs/floor-1.out): the three
--   this-week probes imported, one designed hole, no wall.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-665.Probe665 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( module HullExt; module CollapseIso )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- THE PREDECESSORS, BY THE TYPE EACH ONE DELIVERED (coder clause,
-- owner 2026-08-20).  None of these three imported the 578 chain, so
-- the floor of importing them is the floor of this file
-- (runs/floor-1.out).  Probe578 is NOT imported: that chain walls
-- under the wide cap ([LJ-1.598] runs/chain-578.out, [LJ-1.650]
-- runs/floor-1.out).
import LJ-1-642.Probe642 {ℓ} lem as P642
import LJ-1-650.Probe650 {ℓ} lem as P650
import LJ-1-652.Probe652 {ℓ} lem as P652

-- =====================================================================
-- SECTION 1.  THE ASSEMBLY, AT ONE HULL.
--
--   LevelFormula (value slot 0, index slot 1, Probe650.agda:322-328)
--   pays clause (i) at the ruled index after one swap into Det/Wit's
--   order (index slot 0, value slot 1, Probe642.agda:91-97), and pays
--   clause (ii) with no swap (coded-cover-from-level,
--   Probe650.agda:385-386).  Elementary and Matrix₂ Lset pay clause
--   (iii) as [LJ-1.652] closed it (Probe652.agda:255-257, :305-306).
-- =====================================================================

module Site (lam : SV.S) (ordλ : IsOrd lam)
            (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
            (X : SV.S)
            (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
            (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module F642 = P642.Frame lam ordλ succλ X X⊆Lλ ∅∈λ
  module C650 = P650.Coded lam ordλ succλ X X⊆Lλ ∅∈λ
  module F652 = P652.Frame652 lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = F642.T
  module HS = F642.HS

  module RS = Sat (hPropAlgebra (ℓ-suc ℓ)) HS.ASt.AbsL.𝒮M {K = T.Code} T.val

  -- THE SWAP [LJ-1.659] already wrote (Probe659.agda:185-195), restated
  -- here because that file is a STOP on a different arrow and this
  -- assembly reads the swap at LevelFormula, the other way.  The
  -- mathematics is `⊨-rename` in src/ (W2: instantiated, not re-proved).
  swap : Fin 2 → Fin 2
  swap zero       = suc zero
  swap (suc zero) = zero

  swap-agrees : (a b : HS.ASt.SL) → RS.Agrees swap (a ∷ b ∷ []) (b ∷ a ∷ [])
  swap-agrees a b zero       = refl
  swap-agrees a b (suc zero) = refl

  transpose : (φ : Formula T.Code 2) (a b : HS.ASt.SL)
            → ((a ∷ b ∷ []) T.⊨c renameFo swap φ)
            ≡ ((b ∷ a ∷ []) T.⊨c φ)
  transpose φ a b =
    RS.⊨-rename swap φ (a ∷ b ∷ []) (b ∷ a ∷ []) (swap-agrees a b)

  -- ---- clause (i), from LevelFormula, via [LJ-1.642]'s graph route. --

  det-from-level : (lf : C650.LevelFormula)
                 → F642.Det (renameFo swap (fst lf))
  det-from-level (lv , so , _) b a _ h =
    so a b (subst ⟨_⟩ (transpose lv b a) h)

  wit-from-level : (lf : C650.LevelFormula)
                 → F642.Wit (renameFo swap (fst lf))
  wit-from-level (lv , _ , co) b ob = PT.map step (co b ob)
    where
    step : Σ[ v ∈ HS.ASt.SL ]
             ((fst v ≡ Lset (fst b)) × ⟨ (v ∷ b ∷ []) T.⊨c lv ⟩)
         → Σ[ a ∈ HS.ASt.SL ]
             ⟨ (b ∷ a ∷ []) T.⊨c renameFo swap lv ⟩
    step (v , _ , h) = v , subst ⟨_⟩ (sym (transpose lv b v)) h

  clause-i-from-level : C650.LevelFormula → F642.ClauseIAtOrd
  clause-i-from-level lf =
    F642.graph-gives-clause-i (renameFo swap (fst lf))
      (det-from-level lf) (wit-from-level lf)

  -- ---- clause (ii), already closed by [LJ-1.650]. -------------------

  cover-from-level : C650.LevelFormula → C650.CodedCover
  cover-from-level = C650.coded-cover-from-level

  -- ---- clause (iii), already closed by [LJ-1.652]. -------------------

  commute-from-mx : (elem : F652.A.Elementary) (mx : P652.Matrix₂ Lset)
                  → F652.Instances.Commute elem
  commute-from-mx elem mx =
    F652.Instances.commute-from-lset-formula elem mx

  pack : (lf : C650.LevelFormula)
         (elem : F652.A.Elementary)
         (mx : P652.Matrix₂ Lset)
       → F642.ClauseIAtOrd
       × C650.CodedCover
       × F652.Instances.Commute elem
  pack lf elem mx =
      clause-i-from-level lf
    , cover-from-level lf
    , commute-from-mx elem mx

  -- D-10 SIBLING.  [LJ-1.652] recorded that Matrix₂ Lset is not the
  -- shape the literature has (lj-1.652-report.md:91-107).  The
  -- corrected consumer is already green there.
  pack-witnessed : (lf : C650.LevelFormula)
                   (elem : F652.A.Elementary)
                   (w : P652.Witnessed Lset)
                   (g : F652.Instances.LsetGrounded elem w)
                 → F642.ClauseIAtOrd
                 × C650.CodedCover
                 × F652.Instances.Commute elem
  pack-witnessed lf elem w g =
      clause-i-from-level lf
    , cover-from-level lf
    , F652.Instances.commute-from-witnessed elem w g

  -- ===================================================================
  -- SECTION 2.  [LJ-1.578]'s Certificate, RESTATED, AND THE BRIDGES.
  --
  --   These types live in the SAME module as section 1.  That is W3:
  --   the frames meet.  The conclusions do not: the three bridges
  --   below are the extra debt 578's original still asks for, and
  --   `certificate-remainder` does not spend them.
  -- ===================================================================

  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CIso = CollapseIso HS.M HE.hullExt

  -- Probe578.agda:234-240.
  DefinesLevel : Type (ℓ-suc ℓ)
  DefinesLevel =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c)))
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → fst a ≡ Lset (fst (T.val c))) )

  -- Probe578.agda:244-251.
  DefinesCover : Type (ℓ-suc ℓ)
  DefinesCover =
    (c : T.Code)
    → Σ[ φ ∈ Formula T.Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) T.⊨c φ ⟩ ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) T.⊨c φ ⟩
           → IsOrd (HS.C.π (fst a))
           × ⟨ fst (T.val c) ∈ˢ Lset (fst a) ⟩) )

  -- Probe578.agda:503-510.
  DefinesLevelAcross : Type (ℓ-suc ℓ)
  DefinesLevelAcross =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → Σ[ φ ∈ Formula CIso.I.SM 1 ]
        ( ⟨ ((Lset δ , Lδ∈M) ∷ []) CIso.I.⊨ᵐ φ ⟩
        × ((b : CIso.I.SPM) → ⟨ (b ∷ []) CIso.I.⊨ᵖᵐ mapFo CIso.I.g φ ⟩
           → fst b ≡ Lset (HS.C.π δ)) )

  Certificate578 : Type (ℓ-suc ℓ)
  Certificate578 = DefinesLevel × DefinesCover × DefinesLevelAcross

  -- BRIDGE (i).  [LJ-1.642] deleted this hypothesis.  The one-liner is
  -- the WHOLE extra debt of 578's clause (i) over the ruled index.
  PreimageOrd : Type (ℓ-suc ℓ)
  PreimageOrd =
    (c : T.Code) → IsOrd (HS.C.π (fst (T.val c))) → IsOrd (fst (T.val c))

  to-578-i : PreimageOrd → F642.ClauseIAtOrd → DefinesLevel
  to-578-i po cio c oπ = cio c (po c oπ)

  -- BRIDGE (ii).  CodedCover names a code; DefinesCover names a
  -- formula, and asks ordinal-hood of the COLLAPSE of that code.
  -- [LJ-1.654] built the forward map `PiPreservesOrd`
  -- (Probe654.agda:337).  The formula half is not a predecessor term.
  -- Stated, not inhabited.
  BridgeII : Type (ℓ-suc ℓ)
  BridgeII = C650.CodedCover → DefinesCover

  -- BRIDGE (iii).  Commute is an equation.  DefinesLevelAcross is a
  -- formula in the hull.  Closing Commute does not produce that
  -- formula.  Stated, not inhabited.  The type lives one universe up
  -- because Elementary does (src/L/Hull.lagda.md:174).
  BridgeIII : Type (ℓ-suc (ℓ-suc ℓ))
  BridgeIII = (elem : F652.A.Elementary) → P652.Matrix₂ Lset → DefinesLevelAcross

-- =====================================================================
-- THE OBLIGATION.  Remaining debt in, this week's triple out.
-- =====================================================================

certificate-remainder :
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
    (lf : P650.Coded.LevelFormula lam ordλ succλ X X⊆Lλ ∅∈λ)
    (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ)
    (mx : P652.Matrix₂ Lset)
  → P642.Frame.ClauseIAtOrd lam ordλ succλ X X⊆Lλ ∅∈λ
  × P650.Coded.CodedCover lam ordλ succλ X X⊆Lλ ∅∈λ
  × P652.Frame652.Instances.Commute lam ordλ succλ X X⊆Lλ ∅∈λ elem
certificate-remainder lam ordλ succλ X X⊆Lλ ∅∈λ =
  Site.pack lam ordλ succλ X X⊆Lλ ∅∈λ

-- And the D-10 sibling, same remaining formula, corrected (iii).
certificate-remainder-witnessed :
    (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
    (lf : P650.Coded.LevelFormula lam ordλ succλ X X⊆Lλ ∅∈λ)
    (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ)
    (w : P652.Witnessed Lset)
    (g : P652.Frame652.Instances.LsetGrounded lam ordλ succλ X X⊆Lλ ∅∈λ elem w)
  → P642.Frame.ClauseIAtOrd lam ordλ succλ X X⊆Lλ ∅∈λ
  × P650.Coded.CodedCover lam ordλ succλ X X⊆Lλ ∅∈λ
  × P652.Frame652.Instances.Commute lam ordλ succλ X X⊆Lλ ∅∈λ elem
certificate-remainder-witnessed lam ordλ succλ X X⊆Lλ ∅∈λ =
  Site.pack-witnessed lam ordλ succλ X X⊆Lλ ∅∈λ
