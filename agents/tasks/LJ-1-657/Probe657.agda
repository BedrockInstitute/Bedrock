{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.657] PROBE.  Does [LJ-1.650]'s level formula drive on the road
-- [LJ-1.653] opened to `levelIn`?  Lands nothing in src/.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-657.Probe657 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; ⊤̇; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapFo-comp; embed; ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.BoundedSubset {ℓ} lem using ( module DownReflect )

import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( _×_; _,_; Σ≡Prop )
open import Cubical.Data.Vec using ( Vec; _∷_; []; map )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

-- THE TWO PREDECESSORS, BY IMPORT (coder clause, owner 2026-08-20).
-- The floor of this frame is measured at runs/floor-0.out.
import LJ-1-650.Probe650
import LJ-1-653.Probe653
import LJ-1-649.Probe649

module P650 = LJ-1-650.Probe650 {ℓ} lem
module P653 = LJ-1-653.Probe653 {ℓ} lem
module P649 = LJ-1-649.Probe649 {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module Bridge (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  -- [LJ-1.650]'s side: the level formula, at the STAGE, over CODES.
  module Lv = P650.Coded lam ordλ succλ X X⊆L ∅∈λ
  -- [LJ-1.653]'s side: the Hood pair, at the COLLAPSE, parameter-free.
  module Hd = P653.HullStage lam ordλ succλ X X⊆L ∅∈λ
  -- [LJ-1.649]'s side: the route to `levelIn` that spends step 4 and
  -- takes no formula at all.
  module Rt = P649.HullStage lam ordλ succλ X X⊆L ∅∈λ
  -- The tree's own code-to-hull dictionary and its named elementarity
  -- residue (src/L/BoundedSubset.lagda.md:356-412).
  module DR = DownReflect lam ordλ X X⊆L ∅∈λ
  -- The one term algebra all three modules share: [LJ-1.650]'s `Coded`
  -- opens it privately, so this file names the tree's own copy.
  module T = DR.H.T

  -- ===================================================================
  -- PART 1.  PREMISE 4, ANSWERED AS A TYPE.  THE ARITY MATCHES AND THE
  --          ALPHABET DOES NOT, AND THE GAP IS NOT A COST: IT IS A
  --          DEAD ROUTE.
  --
  --   `HoodExistsP` and `HoodSoundP` (Probe653.agda:283, :235) demand
  --   `Formula (⊥* {ℓ-suc ℓ}) 2`.  `LevelFormula` (Probe650.agda:322)
  --   delivers `Formula Code 2`.  Relabelling carries `⊥*` INTO any
  --   alphabet (`embed`, src/FOL/Manipulation/Relabelling.lagda.md:117)
  --   and never out of one: `mapFo f` needs `f : Code → ⊥*`, and the
  --   term below refutes every such `f` with no hypothesis at all.
  -- ===================================================================

  -- A code exists unconditionally: `wit` is a constructor
  -- (src/L/Hull.lagda.md:72-74) and it asks only for a parameter-free
  -- formula and a vector of codes, both of which `⊤̇` and `[]` supply.
  code-inhabited : T.Code
  code-inhabited = T.wit 0 ⊤̇ []

  no-relabelling-out-of-Code : (T.Code → ⊥* {ℓ-suc ℓ}) → Empty.⊥
  no-relabelling-out-of-Code f = Empty.rec* (f code-inhabited)

  -- ===================================================================
  -- PART 2.  THE ALPHABET THE TWO SIDES DO SHARE.
  --
  --   `[LJ-1.653]`'s UN-pinned pair (`HoodExists`, `HoodSound`,
  --   Probe653.agda:263, :191) is stated at `Formula CIso.I.SM 2`, and
  --   the tree already carries `Code → SM`: `DownReflect.codeValM`
  --   (src/L/BoundedSubset.lagda.md:377-378).  So the level formula
  --   reaches the un-pinned pair, and only the un-pinned pair.
  -- ===================================================================

  levelFo : Lv.LevelFormula → Formula Hd.CIso.I.SM 2
  levelFo lf = mapFo DR.codeValM (fst lf)

  -- ===================================================================
  -- PART 3.  THE TWO HYPOTHESES THE CROSSING NEEDS, EACH TAKEN AT THE
  --          TYPE THE TREE OR A PREDECESSOR ALREADY NAMES.
  --
  --   `LevelFormula` speaks at the STAGE `Lset lam`.  The Hood pair
  --   speaks at the COLLAPSE `C.πX`.  Between them stand two crossings
  --   and nothing else: the hull sits in the stage (elementarity), and
  --   the collapse sits opposite the hull (the delivered iso).
  -- ===================================================================

  -- The tree's OWN named residue, unchanged: src/L/BoundedSubset.lagda.md:410-412.
  -- `AtHullInstance.reflect` (src/L/BoundedSubset.lagda.md:781) already
  -- takes it, so this is not new debt.  `HullElemDown.elem`
  -- (src/L/BoundedSubset.lagda.md:762) discharges it from a code
  -- selection.
  ElemDown : Type (ℓ-suc ℓ)
  ElemDown = DR.ElemDown

  -- [LJ-1.649]'s FIFTH FACT, verbatim from
  -- agents/tasks/LJ-1-649/Probe649.agda:222-223, where it is named
  -- UNBUILT.  [LJ-1.653] built the forward direction only
  -- (π-ord, agents/tasks/LJ-1-653/Probe653.agda:136).
  PiReflectsOrd : Type (ℓ-suc ℓ)
  PiReflectsOrd = (y : S) → ⟨ y ∈ˢ Hd.M ⟩ → IsOrd (Hd.C.π y) → IsOrd y

  -- The one relabelling path used everywhere below: the level formula
  -- read at the hull, then at the stage, is the level formula read over
  -- codes.  `mapFo-ext` is the tree's (src/L/BoundedSubset.lagda.md:387).
  formPath : (lv : Formula T.Code 2)
           → mapFo DR.inL (mapFo DR.codeValM lv) ≡ mapFo T.val lv
  formPath lv = mapFo-comp DR.codeValM DR.inL lv ∙ DR.mapFo-ext lv

  readPath : (lv : Formula T.Code 2) (δ : Vec Hd.ASt.SL 2)
           → (δ Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL (mapFo DR.codeValM lv)))
           ≡ (δ T.⊨c lv)
  readPath lv δ =
    cong (λ ψ → δ Hd.ASt.AbsL.⊨ᵐ ψ) (formPath lv)
    ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) Hd.ASt.AbsL.𝒮M T.val id lv δ

  -- ===================================================================
  -- PART 4.  THE EXISTENTIAL HALF, AND IT COMES FREE.
  --
  --   `HoodExists` is what the COLLAPSE BELIEVES, and belief travels
  --   down from the stage by elementarity and across by the delivered
  --   iso.  Step 4 does not appear anywhere in this term.
  -- ===================================================================

  hoodExists-from-level :
      (lf : Lv.LevelFormula) → ElemDown → PiReflectsOrd
    → Hd.HoodExists (levelFo lf)
  hoodExists-from-level lf ed pro γ γ∈ oγ =
    PT.rec PT.squash₁ step (Hd.CIso.I.surj' (γ , γ∈))
    where
    lv : Formula T.Code 2
    lv = fst lf

    φM : Formula Hd.CIso.I.SM 2
    φM = mapFo DR.codeValM lv

    step : Σ[ q ∈ Hd.CIso.I.SM ] (Hd.CIso.I.g q ≡ (γ , γ∈))
         → ∥ Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ Hd.C.πX ⟩ ]
              ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ [])
                  Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g φM) ⟩ ∥₁
    step (q , gq) = PT.map out (ed 1 (∃̇ φM) (q ∷ []) stage-sat)
      where
      oq : IsOrd (fst q)
      oq = pro (fst q) (snd q) (subst IsOrd (sym (cong fst gq)) oγ)

      mk : Σ[ v ∈ Hd.ASt.SL ]
             ((fst v ≡ Lset (fst q)) × ⟨ (v ∷ DR.inL q ∷ []) T.⊨c lv ⟩)
         → Σ[ a ∈ Hd.ASt.SL ]
              ⟨ (a ∷ DR.inL q ∷ []) Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL φM) ⟩
      mk (v , _ , hv) =
        v , subst ⟨_⟩ (sym (readPath lv (v ∷ DR.inL q ∷ []))) hv

      stage-sat : ⟨ map DR.inL (q ∷ []) Hd.ASt.AbsL.⊨ᵐ
                      (mapFo DR.inL (∃̇ φM)) ⟩
      stage-sat = PT.map mk (snd (snd lf) (DR.inL q) oq)

      out : Σ[ w ∈ Hd.CIso.I.SM ] ⟨ (w ∷ q ∷ []) Hd.CIso.I.⊨ᵐ φM ⟩
          → Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ Hd.C.πX ⟩ ]
               ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ [])
                   Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g φM) ⟩
      out (w , hw) =
          fst (Hd.CIso.I.g w) , snd (Hd.CIso.I.g w)
        , subst (λ z → ⟨ (Hd.CIso.I.g w ∷ z ∷ [])
                           Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g φM) ⟩)
                gq (Hd.CIso.I.iso-inv 2 φM (w ∷ q ∷ []) hw)

  -- ===================================================================
  -- PART 5.  THE COMPLETENESS HALF, ALSO FREE.
  --
  --   `HoodComplete` (Probe653.agda:186) asks the HULL to believe that
  --   `Lset y` is the level at `y`.  The level formula's completeness
  --   names a stage witness EQUAL to `Lset y`, and `ElemDown` brings the
  --   belief into the hull.  `PiReflectsOrd` is not spent here: the
  --   consumer hands `IsOrd y` on the hull side already.
  -- ===================================================================

  hoodComplete-from-level :
      (lf : Lv.LevelFormula) → ElemDown → Hd.HoodComplete (levelFo lf)
  hoodComplete-from-level lf ed y y∈ oy Ly∈ =
    ed 2 φM ((Lset y , Ly∈) ∷ (y , y∈) ∷ []) stage-sat
    where
    lv : Formula T.Code 2
    lv = fst lf

    φM : Formula Hd.CIso.I.SM 2
    φM = mapFo DR.codeValM lv

    env : Vec Hd.ASt.SL 2
    env = DR.inL (Lset y , Ly∈) ∷ DR.inL (y , y∈) ∷ []

    mk : Σ[ v ∈ Hd.ASt.SL ]
           ((fst v ≡ Lset y) × ⟨ (v ∷ DR.inL (y , y∈) ∷ []) T.⊨c lv ⟩)
       → ⟨ env Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL φM) ⟩
    mk (v , ev , hv) =
      subst ⟨_⟩ (sym (readPath lv env))
        (subst (λ a → ⟨ (a ∷ DR.inL (y , y∈) ∷ []) T.⊨c lv ⟩) vpath hv)
      where
      vpath : v ≡ DR.inL (Lset y , Ly∈)
      vpath = Σ≡Prop (λ z → (z ∈ˢ Lset lam) .snd) ev

    stage-sat : ⟨ map DR.inL ((Lset y , Ly∈) ∷ (y , y∈) ∷ [])
                    Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL φM) ⟩
    stage-sat = PT.rec (snd (env Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL φM))) mk
                  (snd (snd lf) (DR.inL (y , y∈)) oy)

  -- ===================================================================
  -- PART 6.  THE SOUNDNESS HALF, AND IT IS NOT FREE.
  --
  --   `HoodSound` (Probe653.agda:191) is an AMBIENT claim: the value the
  --   COLLAPSE believes is the level really IS the level.  The level
  --   formula's soundness is an ambient claim at the STAGE.  Carrying
  --   one to the other along `π` is `C.π (Lset y) ≡ Lset (C.π y)`, which
  --   is [LJ-1.462]'s step 4 at ordinals.  It is spent at ONE line
  --   below, and nothing else in this file spends it.
  -- ===================================================================

  -- src/L/Hull.lagda.md:174-176, the tree's own `Elementary`, restated
  -- at this file's names.  `elem-restates-the-tree` below certifies the
  -- restatement by inhabiting one from the other with `λ e → e`.
  Elem : Type (ℓ-suc (ℓ-suc ℓ))
  Elem = (n : ℕ) (φ : Formula Hd.CIso.I.SM n) (δ : Vec Hd.CIso.I.SM n)
       → (δ DR.⊨ᵐ φ) ≡ (map DR.inL δ Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL φ))

  module A = Hd.ASt.AtM Hd.M Hd.H.Hull⊆L

  elem-restates-the-tree : A.Elementary → Elem
  elem-restates-the-tree e = e

  elem-down : Elem → ElemDown
  elem-down e n φ δ h = subst ⟨_⟩ (sym (e n φ δ)) h

  hoodSound-from-level :
      (lf : Lv.LevelFormula) → Elem → PiReflectsOrd
    → Hd.PiCommuteLsetOrd
    → Hd.HoodSound (levelFo lf)
  hoodSound-from-level lf e pro s4 v γ v∈ γ∈ oγ h =
    PT.rec (isSetS v (Lset γ)) atV (Hd.CIso.I.surj' (v , v∈))
    where
    lv : Formula T.Code 2
    lv = fst lf

    φM : Formula Hd.CIso.I.SM 2
    φM = mapFo DR.codeValM lv

    atV : Σ[ qv ∈ Hd.CIso.I.SM ] (Hd.CIso.I.g qv ≡ (v , v∈)) → v ≡ Lset γ
    atV (qv , gv) =
      PT.rec (isSetS v (Lset γ)) atG (Hd.CIso.I.surj' (γ , γ∈))
      where
      atG : Σ[ qg ∈ Hd.CIso.I.SM ] (Hd.CIso.I.g qg ≡ (γ , γ∈)) → v ≡ Lset γ
      atG (qg , gg) =
          sym (cong fst gv)
        ∙ cong Hd.C.π stage-sound
        ∙ s4 (fst qg) (snd qg) oqg
        ∙ cong Lset (cong fst gg)
        where
        oqg : IsOrd (fst qg)
        oqg = pro (fst qg) (snd qg) (subst IsOrd (sym (cong fst gg)) oγ)

        h₁ : ⟨ (Hd.CIso.I.g qv ∷ (γ , γ∈) ∷ [])
                 Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g φM) ⟩
        h₁ = subst (λ a → ⟨ (a ∷ (γ , γ∈) ∷ [])
                              Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g φM) ⟩)
                   (sym gv) h

        h₂ : ⟨ map Hd.CIso.I.g (qv ∷ qg ∷ [])
                 Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g φM) ⟩
        h₂ = subst (λ b → ⟨ (Hd.CIso.I.g qv ∷ b ∷ [])
                              Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g φM) ⟩)
                   (sym gg) h₁

        h₃ : ⟨ (qv ∷ qg ∷ []) Hd.CIso.I.⊨ᵐ φM ⟩
        h₃ = Hd.CIso.I.iso-inv-bwd 2 φM (qv ∷ qg ∷ []) h₂

        h₄ : ⟨ (DR.inL qv ∷ DR.inL qg ∷ []) T.⊨c lv ⟩
        h₄ = subst ⟨_⟩ (readPath lv (DR.inL qv ∷ DR.inL qg ∷ []))
               (subst ⟨_⟩ (e 2 φM (qv ∷ qg ∷ [])) h₃)

        stage-sound : fst qv ≡ Lset (fst qg)
        stage-sound = fst (snd lf) (DR.inL qv) (DR.inL qg) h₄

  -- ===================================================================
  -- PART 7.  THE OBLIGATION'S TYPE, AND WHY THIS FILE DOES NOT INHABIT
  --          IT.
  --
  --   THE OBLIGATION IS NOT INHABITED HERE AND THE STOP IS
  --   review-of-levelin-from-level-formula.md.  The terms below are the
  --   evidence, and each one typechecks.
  -- ===================================================================

  -- 7.1  THE BRIEF'S OBLIGATION, IN THE ONLY READING THAT CAN BE
  --      WRITTEN AT ALL.  Part 1 killed the pinned reading, so the
  --      un-pinned pair is what is left of it.
  LevelinFromLevelFormula : Type (ℓ-suc ℓ)
  LevelinFromLevelFormula =
    (lf : Lv.LevelFormula)
    → Hd.HoodExists (levelFo lf) × Hd.HoodSound (levelFo lf)

  -- 7.2  WHAT IS DELIVERED INSTEAD, WITH THE PRICE IN THE TYPE.  The
  --      existential half spends `ElemDown` and `PiReflectsOrd`; the
  --      soundness half spends step 4 as well.
  hood-pair-priced :
      (lf : Lv.LevelFormula) → Elem → PiReflectsOrd → Hd.PiCommuteLsetOrd
    → Hd.HoodExists (levelFo lf) × Hd.HoodSound (levelFo lf)
  hood-pair-priced lf e pro s4 =
      hoodExists-from-level lf (elem-down e) pro
    , hoodSound-from-level lf e pro s4

  -- 7.3  AND THE CONSUMER'S OWN GOAL, THROUGH [LJ-1.653]'s DELIVERED
  --      TERM (agents/tasks/LJ-1-653/Probe653.agda:272-274).
  levelin-priced :
      (lf : Lv.LevelFormula) → Elem → PiReflectsOrd → Hd.PiCommuteLsetOrd
    → Hd.LevelIn
  levelin-priced lf e pro s4 =
    Hd.levelin-from-hood (levelFo lf)
      (hoodExists-from-level lf (elem-down e) pro)
      (hoodSound-from-level lf e pro s4)

  -- 7.4  THE PRICE IS NOT A SIDE CONDITION.  IT IS THE SAME FACT UNDER
  --      A SECOND NAME.  [LJ-1.653]'s step4-at-ord
  --      (agents/tasks/LJ-1-653/Probe653.agda:200-203) runs the other
  --      way, and PART 5 supplies its completeness half for free, so
  --      the two implications close a circle.
  hoodsound-is-step4 :
      (lf : Lv.LevelFormula) → Elem → PiReflectsOrd → Hd.HullClosedLsetOrd
    → (Hd.PiCommuteLsetOrd → Hd.HoodSound (levelFo lf))
    × (Hd.HoodSound (levelFo lf) → Hd.PiCommuteLsetOrd)
  hoodsound-is-step4 lf e pro hcl =
      hoodSound-from-level lf e pro
    , (λ hs → Hd.step4-at-ord (levelFo lf)
                (hoodComplete-from-level lf (elem-down e)) hs hcl)

  -- 7.5  AND THE PRICED ROUTE IS DOMINATED.  [LJ-1.649]'s
  --      `levelin-from-647-ord-commute` (Probe649.agda:241-245, GREEN by
  --      agents/tasks/LJ-1-649/lj-1.649-report.md:147) reaches the SAME
  --      conclusion from a SUBSET of these hypotheses: no level formula
  --      and no elementarity.  The body below ignores `lf` and `e`, and
  --      that is the whole finding.
  Lj649Route : Type (ℓ-suc ℓ)
  Lj649Route = PiReflectsOrd → Hd.HullClosedLsetOrd → Hd.PiCommuteLsetOrd
             → Hd.LevelIn

  -- IT IS NOT A RESTATEMENT.  The predecessor's own term inhabits it,
  -- and the two types unify with no adapter.
  lj649-route : Lj649Route
  lj649-route = Rt.levelin-from-647-ord-commute

  levelin-priced-is-dominated :
      (lf : Lv.LevelFormula) → Elem → PiReflectsOrd → Hd.HullClosedLsetOrd
    → Hd.PiCommuteLsetOrd → Hd.LevelIn
  levelin-priced-is-dominated lf e pro hcl s4 = lj649-route pro hcl s4

  -- 7.6  WHAT THE LEVEL FORMULA DOES BUY, AND IT IS ONE HALF OF STEP
  --      4's OWN PRICE.  [LJ-1.653]'s step4-at-ord asks for BOTH
  --      adequacy halves.  With the level formula and `ElemDown` the
  --      completeness half is free, so step 4 is left owing SOUNDNESS
  --      alone.  This is the only thing this task moves, and it moves
  --      it without step 4 anywhere in the term.
  step4-owes-soundness-alone :
      (lf : Lv.LevelFormula) → ElemDown → Hd.HullClosedLsetOrd
    → Hd.HoodSound (levelFo lf) → Hd.PiCommuteLsetOrd
  step4-owes-soundness-alone lf ed hcl hs =
    Hd.step4-at-ord (levelFo lf) (hoodComplete-from-level lf ed) hs hcl

  -- 7.7  AND THE CONSUMER'S OWN GOAL OWES THE SAME ONE THING.  No step
  --      2 in this chain and no step 4 either: [LJ-1.653]'s second term
  --      takes the existential half, and PART 4 pays it.
  levelin-owes-soundness-alone :
      (lf : Lv.LevelFormula) → ElemDown → PiReflectsOrd
    → Hd.HoodSound (levelFo lf) → Hd.LevelIn
  levelin-owes-soundness-alone lf ed pro hs =
    Hd.levelin-from-hood (levelFo lf) (hoodExists-from-level lf ed pro) hs

  -- ===================================================================
  -- PART 8.  THE ALPHABET GAP IS CURABLE AT ITS SOURCE, AND THE CURE IS
  --          THE LITERATURE'S OWN SHAPE.
  --
  --   `dev/literature/level-formula-slot-roles.md:37` records
  --   Schindler-Zeman 1.10(2): the level-hood formula "does not depend
  --   on α".  Rows 3 to 9 of that table agree that the free pair is the
  --   VALUE and the ORDINAL and that nothing else stays free.  So the
  --   PARAMETER-FREE statement is the faithful one and
  --   `Lv.LevelFormula` (Probe650.agda:322-328) loses it by typing the
  --   formula at `Code`.
  --
  --   Stated parameter-free, the pinned pair IS reachable for the
  --   existential half.  IT IS STILL NOT REACHABLE FOR SOUNDNESS: PART
  --   6's price does not move, because it is a fact about the two
  --   CARRIERS and not about the alphabet.
  -- ===================================================================

  LevelFormulaP : Type (ℓ-suc ℓ)
  LevelFormulaP =
    Σ[ φ₀ ∈ Formula (⊥* {ℓ-suc ℓ}) 2 ]
      ( ((v γ : Hd.ASt.SL) → ⟨ (v ∷ γ ∷ []) T.⊨c (embed φ₀) ⟩
         → fst v ≡ Lset (fst γ))
      × ((γ : Hd.ASt.SL) → IsOrd (fst γ)
         → ∥ Σ[ v ∈ Hd.ASt.SL ]
              ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) T.⊨c (embed φ₀) ⟩) ∥₁) )

  -- The strengthening is a strengthening and nothing else: it lands in
  -- [LJ-1.650]'s own type with no adapter.
  levelP→level : LevelFormulaP → Lv.LevelFormula
  levelP→level (φ₀ , so , co) = embed φ₀ , (so , co)

  -- The relabelling to the hull fixes a parameter-free formula, the same
  -- way [LJ-1.653]'s `embed-fixed` (Probe653.agda:224-228) fixes it
  -- under the collapse.
  levelFo-embed : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)
                → mapFo DR.codeValM (embed φ₀) ≡ embed φ₀
  levelFo-embed φ₀ =
    mapFo-comp Empty.rec* DR.codeValM φ₀
    ∙ cong (λ f → mapFo f φ₀) (funExt (λ b → Empty.rec* b))

  hoodExistsP-from-levelP :
      (lfp : LevelFormulaP) → ElemDown → PiReflectsOrd
    → Hd.HoodExistsP (fst lfp)
  hoodExistsP-from-levelP lfp ed pro γ γ∈ oγ =
    PT.map fix (base γ γ∈ oγ)
    where
    φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2
    φ₀ = fst lfp

    base : Hd.HoodExists (embed φ₀)
    base = subst Hd.HoodExists (levelFo-embed φ₀)
             (hoodExists-from-level (levelP→level lfp) ed pro)

    fix : Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ Hd.C.πX ⟩ ]
            ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ [])
                Hd.CIso.I.⊨ᵖᵐ (mapFo Hd.CIso.I.g (embed φ₀)) ⟩
        → Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ Hd.C.πX ⟩ ]
            ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) Hd.CIso.I.⊨ᵖᵐ (embed φ₀) ⟩
    fix (v , v∈ , h) =
      v , v∈ , subst (λ ψ → ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) Hd.CIso.I.⊨ᵖᵐ ψ ⟩)
                     (Hd.embed-fixed φ₀) h

  -- AND THE PINNED SOUNDNESS HALF STILL COSTS STEP 4, UNCHANGED.
  hoodSoundP-from-levelP :
      (lfp : LevelFormulaP) → Elem → PiReflectsOrd → Hd.PiCommuteLsetOrd
    → Hd.HoodSoundP (fst lfp)
  hoodSoundP-from-levelP lfp e pro s4 v γ v∈ γ∈ oγ h =
    base v γ v∈ γ∈ oγ
      (subst (λ ψ → ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) Hd.CIso.I.⊨ᵖᵐ ψ ⟩)
             (sym (Hd.embed-fixed φ₀)) h)
    where
    φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2
    φ₀ = fst lfp

    base : Hd.HoodSound (embed φ₀)
    base = subst Hd.HoodSound (levelFo-embed φ₀)
             (hoodSound-from-level (levelP→level lfp) e pro s4)

  -- THE BRIEF'S OBLIGATION, INHABITED ONLY AFTER BOTH REPAIRS: the
  -- level formula stated parameter-free, AND step 4 paid.  Neither
  -- repair is this task's to make, and section 7.5 shows the second one
  -- already buys `levelIn` on its own.
  levelin-from-levelP-priced :
      (lfp : LevelFormulaP) → Elem → PiReflectsOrd → Hd.PiCommuteLsetOrd
    → Hd.HoodExistsP (fst lfp) × Hd.HoodSoundP (fst lfp)
  levelin-from-levelP-priced lfp e pro s4 =
      hoodExistsP-from-levelP lfp (elem-down e) pro
    , hoodSoundP-from-levelP lfp e pro s4
