{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.662] PROBE.  The EXISTENTIAL half of the hood, at the formula
-- the chapter itself writes.  Lands nothing in src/.
--
--   PART 1   The PINNED formula.  The chapter's LevelHood0 matrix
--            (src/L/BoundedSubset.lagda.md:848-849) re-slotted to the
--            pair the Hood predicates read and ERASED to the
--            parameter-free alphabet.  MEASURED: the matrix is
--            constant-free, so `erase` crosses the alphabet gap that
--            [LJ-1.657] measured FATAL for [LJ-1.650]'s LevelFormula.
--
--   PART 2   The composition.  [LJ-1.657]'s existential route with
--            [LJ-1.654]'s PiReflectsOrd DISCHARGED BY IMPORT, and with
--            the soundness half of LevelFormulaP dropped: the
--            existential half never reads it.
--
--   PART 3   PREMISE 3, measured at the VALUE slot, and the residue
--            named: what is left of the covering half is ONE fact.
--
--   PART 4   The pinned instance.
--
--   THE BRIEF'S OBLIGATION, `hoodexists-at-levelhood0` WITH NO
--   HYPOTHESIS, IS NOT IN THIS FILE.  `review-of-hoodexists.md` is the
--   stop and says why with file:line.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-662.Probe662 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula; var; ⊤̇; ∃̇_; ∃̇∈ )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Renaming using ( renameFo )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( mapFo; embed )
import FOL.Count
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; Lset-in; Lset-mono )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.BoundedSubset {ℓ} lem
  using ( module LevelHood0; module CS; module DownReflect )

open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Vec using ( Vec; _∷_; []; map )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

-- THE THREE PREDECESSORS, BY IMPORT (coder clause, owner 2026-08-20).
-- The floor of this frame is measured at runs/floor-2.out.
import LJ-1-653.Probe653
import LJ-1-654.Probe654
import LJ-1-657.Probe657

module P653 = LJ-1-653.Probe653 {ℓ} lem
module P654 = LJ-1-654.Probe654 {ℓ} lem
module P657 = LJ-1-657.Probe657 {ℓ} lem

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- PART 1.  THE PINNED FORMULA.
--
--   The chapter states the matrix at the environment u ∷ v ∷ γ ∷ K ∷ []
--   (src/L/BoundedSubset.lagda.md:68-72): slot zero unused, v the
--   value, γ the ordinal index, K the one bound.  `HoodExistsP` reads
--   the pair v ∷ γ ∷ [] and nothing else
--   (agents/tasks/LJ-1-653/Probe653.agda:283-287), so the bound and the
--   unused slot are closed off: K existentially, the unused slot by the
--   chapter's own bounded existential over K.
-- =====================================================================

-- u ∷ v ∷ γ ∷ K ∷ []  (the chapter's order)
-- u ∷ K ∷ v ∷ γ ∷ []  (the order under ∃̇ K then ∃̇∈ K u)
ρ : Fin 4 → Fin 4
ρ zero = zero
ρ (suc zero) = suc (suc zero)
ρ (suc (suc zero)) = suc (suc (suc zero))
ρ (suc (suc (suc zero))) = suc zero

module Pinned
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin 5)
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin 7) where

  module LH0 = LevelHood0 N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
                          M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1

  -- SEALED, AND THE SEAL IS MEASURED (P-l, dev/LESSONS.md:2367).  Left
  -- transparent, naming `φ₀` in a downstream TYPE unfolds the chapter's
  -- whole bounded code-set description inside the elaborator and the
  -- wide caliber's 2 GB is exhausted at 10.6 s (runs/p-3.out, exit 251,
  -- `Heap exhausted`, peak footprint 972,424,464 bytes).  Sealed, the
  -- same file reached 48 s before walling (runs/p-4.out), which is what
  -- said the seal was necessary and not sufficient.  The four facts
  -- below are the official readings and no consumer needs `unfolding`.
  opaque
    hood2 : Formula CS.S 2
    hood2 = ∃̇ (∃̇∈ (var zero) (renameFo ρ LH0.matrix))

    -- MEASURED, AND IT IS THE FINDING OF PART 1.  The chapter's matrix
    -- carries NO constant, so the erase to the parameter-free alphabet
    -- is a `refl` away.  [LJ-1.657] measured the SAME crossing DEAD for
    -- [LJ-1.650]'s LevelFormula, whose formula is typed at `Code`
    -- (agents/tasks/LJ-1-657/Probe657.agda:83-84).  The chapter's own
    -- shape is not typed at `Code` and the gap does not arise.
    count-hood2 : countFo hood2 ≡ 0
    count-hood2 = refl

    φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2
    φ₀ = Cnt.erase hood2 count-hood2

    -- The erasure is faithful: embedding it back is the chapter's own
    -- formula, unchanged.
    φ₀-inv : embed φ₀ ≡ hood2
    φ₀-inv = Cnt.erase-inv hood2 count-hood2


-- =====================================================================
-- PART 2.  THE COMPOSITION.
--
--   [LJ-1.657] routed `HoodExistsP` from THREE hypotheses: a
--   parameter-free LevelFormulaP, `ElemDown`, and `PiReflectsOrd`
--   (agents/tasks/LJ-1-657/Probe657.agda:435-437).  It called the last
--   one UNBUILT (Probe657.agda:118-121).  THAT IS STALE.  [LJ-1.654]
--   BUILT IT (agents/tasks/LJ-1-654/Probe654.agda:295-297), and this
--   module discharges it by IMPORT rather than by copy.
--
--   And the first hypothesis is spent by ONE HALF.  `LevelFormulaP`
--   (Probe657.agda:412-419) bundles a soundness half with a covering
--   half; the existential route reads `snd (snd lfp)` and never the
--   soundness (Probe657.agda:145-149, :435-437).  `CoverP` below is
--   that half alone, and `cover-restates-657` certifies the restatement
--   against the predecessor's own type by inhabiting one from the other.
-- =====================================================================

module Bridge (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  -- [LJ-1.657]'s `Bridge` IS NOT OPENED AS A MODULE HERE, and that is a
  -- heap measurement (coder clause, owner 2026-08-23).  The wholesale
  -- application `module Bd = P657.Bridge lam ...` specialises every one
  -- of that module's definitions at this telescope and costs
  -- 1,293,303,808 bytes ON ITS OWN, against a 0.70 GB frame
  -- (runs/b7-1.out against runs/floor-2.out).  Every name this file
  -- takes from it is PROJECTED instead, which specialises nothing.
  module Hd = P653.HullStage lam ordλ succλ X X⊆L ∅∈λ
  module DR = DownReflect lam ordλ X X⊆L ∅∈λ
  module T  = DR.H.T
  module R4 = P654.HullStage lam ordλ succλ X X⊆L ∅∈λ

  PiReflectsOrd : Type (ℓ-suc ℓ)
  PiReflectsOrd = (y : S) → ⟨ y ∈ˢ Hd.M ⟩ → IsOrd (Hd.C.π y) → IsOrd y

  -- The restatement is certified against [LJ-1.657]'s own type by
  -- inhabiting one from the other, the pattern that file uses at
  -- agents/tasks/LJ-1-657/Probe657.agda:247-248.
  pro-restates-657 : PiReflectsOrd
                   → P657.Bridge.PiReflectsOrd lam ordλ succλ X X⊆L ∅∈λ
  pro-restates-657 p = p

  -- PREMISE 4, CURED.  Not copied: the typechecker matches [LJ-1.654]'s
  -- delivered term against the type [LJ-1.657] named UNBUILT, in one
  -- process.
  pro : PiReflectsOrd
  pro = R4.PiReflectsOrd

  ElemDown : Type (ℓ-suc ℓ)
  ElemDown = DR.ElemDown

  elemdown-restates-657 : ElemDown
                        → P657.Bridge.ElemDown lam ordλ succλ X X⊆L ∅∈λ
  elemdown-restates-657 e = e

  -- The covering half of the level formula, stated parameter-free and
  -- ALONE.  It reads at the STAGE, over the hull's codes.
  CoverP : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  CoverP φ =
    (γ : Hd.ASt.SL) → IsOrd (fst γ)
    → ∥ Σ[ v ∈ Hd.ASt.SL ]
         ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) T.⊨c (embed φ) ⟩) ∥₁

  cover-restates-657 :
      (lfp : P657.Bridge.LevelFormulaP lam ordλ succλ X X⊆L ∅∈λ)
    → CoverP (fst lfp)
  cover-restates-657 lfp = snd (snd lfp)

  -- The one relabelling this route spends: the parameter-free formula
  -- read over the hull's constants is the same formula.  [LJ-1.657]'s
  -- `levelFo-embed` (Probe657.agda:428-432), used as delivered.
  readφ : (φ : Formula (⊥* {ℓ-suc ℓ}) 2) (δ : Vec Hd.ASt.SL 2)
        → (δ Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL (embed φ))) ≡ (δ T.⊨c (embed φ))
  readφ φ δ =
    cong (λ ψ → δ Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL ψ))
         (sym (P657.Bridge.levelFo-embed lam ordλ succλ X X⊆L ∅∈λ φ))
    ∙ P657.Bridge.readPath lam ordλ succλ X X⊆L ∅∈λ (embed φ) δ

  -- THE EXISTENTIAL HALF, FROM THE COVERING HALF ALONE.  The shape is
  -- [LJ-1.657]'s (Probe657.agda:146-183) with the soundness slot gone
  -- and `PiReflectsOrd` discharged above, so only TWO hypotheses stand.
  hoodExistsP-from-cover : (φ : Formula (⊥* {ℓ-suc ℓ}) 2)
                         → CoverP φ → ElemDown → Hd.HoodExistsP φ
  hoodExistsP-from-cover φ co ed γ γ∈ oγ =
    PT.rec PT.squash₁ step (Hd.CIso.I.surj' (γ , γ∈))
    where
    φM : Formula Hd.CIso.I.SM 2
    φM = embed φ

    step : Σ[ q ∈ Hd.CIso.I.SM ] (Hd.CIso.I.g q ≡ (γ , γ∈))
         → ∥ Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ Hd.C.πX ⟩ ]
              ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) Hd.CIso.I.⊨ᵖᵐ (embed φ) ⟩ ∥₁
    step (q , gq) = PT.map out (ed 1 (∃̇ φM) (q ∷ []) stage-sat)
      where
      oq : IsOrd (fst q)
      oq = pro (fst q) (snd q) (subst IsOrd (sym (cong fst gq)) oγ)

      mk : Σ[ v ∈ Hd.ASt.SL ]
             ((fst v ≡ Lset (fst (DR.inL q)))
              × ⟨ (v ∷ DR.inL q ∷ []) T.⊨c (embed φ) ⟩)
         → Σ[ a ∈ Hd.ASt.SL ]
              ⟨ (a ∷ DR.inL q ∷ []) Hd.ASt.AbsL.⊨ᵐ (mapFo DR.inL φM) ⟩
      mk (v , _ , hv) =
        v , subst ⟨_⟩ (sym (readφ φ (v ∷ DR.inL q ∷ []))) hv

      stage-sat : ⟨ map DR.inL (q ∷ []) Hd.ASt.AbsL.⊨ᵐ
                      (mapFo DR.inL (∃̇ φM)) ⟩
      stage-sat = PT.map mk (co (DR.inL q) oq)

      out : Σ[ w ∈ Hd.CIso.I.SM ] ⟨ (w ∷ q ∷ []) Hd.CIso.I.⊨ᵐ φM ⟩
          → Σ[ v ∈ S ] Σ[ v∈ ∈ ⟨ v ∈ˢ Hd.C.πX ⟩ ]
               ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ [])
                   Hd.CIso.I.⊨ᵖᵐ (embed φ) ⟩
      out (w , hw) =
          fst (Hd.CIso.I.g w) , snd (Hd.CIso.I.g w)
        , subst (λ z → ⟨ (Hd.CIso.I.g w ∷ z ∷ [])
                           Hd.CIso.I.⊨ᵖᵐ (embed φ) ⟩)
                gq
                (subst (λ ψ → ⟨ (Hd.CIso.I.g w ∷ Hd.CIso.I.g q ∷ [])
                                  Hd.CIso.I.⊨ᵖᵐ ψ ⟩)
                       (Hd.embed-fixed φ)
                       (Hd.CIso.I.iso-inv 2 φM (w ∷ q ∷ []) hw))

  -- ===================================================================
  -- PART 3.  PREMISE 3, MEASURED AT THE VALUE SLOT.
  --
  --   `CoverP` asks TWO things at once: that the stage NAME a value
  --   equal to `Lset γ`, and that the value SATISFY the formula.  The
  --   first half is free, and this term is the measurement.  [LJ-1.650]
  --   measured the same freedom one carrier out, for the covering
  --   ORDINAL (agents/tasks/LJ-1-650/Probe650.agda:333-347); this is the
  --   covering VALUE, which is what the level formula's witness is.
  -- ===================================================================

  level-in-stage : (γ : Hd.ASt.SL) → IsOrd (fst γ)
                 → ⟨ Lset (fst γ) ∈ˢ Lset lam ⟩
  level-in-stage (g , g∈) og =
    Lset-mono {α = lam} {β = sucV g} (succλ g g∈λ)
      (Lset-in (sucV g) g (Lset g) (self∈sucV g) self-def)
    where
    g∈λ : ⟨ g ∈ˢ lam ⟩
    g∈λ = ord∈Lset→∈ lam ordλ g og g∈
    -- The whole stage is a definable subset of itself, by ⊤̇
    -- (src/L/Definability.lagda.md:178-179).
    self-def : ⟨ Lset g ∈ˢ 𝒟ₒ (Lset g) ⟩
    self-def = 𝒟ₒ-intro (Lset g) (Lset g)
                 ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset g) ∣₁

  -- The residue with the free half spent: what is left of `CoverP` is
  -- the SATISFACTION at the canonical value and nothing else.
  SatAtLevel : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  SatAtLevel φ =
    (γ : Hd.ASt.SL) (oγ : IsOrd (fst γ))
    → ⟨ ((Lset (fst γ) , level-in-stage γ oγ) ∷ γ ∷ []) T.⊨c (embed φ) ⟩

  cover-from-sat : (φ : Formula (⊥* {ℓ-suc ℓ}) 2) → SatAtLevel φ → CoverP φ
  cover-from-sat φ s γ oγ =
    ∣ (Lset (fst γ) , level-in-stage γ oγ) , (refl , s γ oγ) ∣₁

  -- THE WHOLE EXISTENTIAL HALF, FROM THE SATISFACTION ALONE.
  hoodExistsP-from-sat : (φ : Formula (⊥* {ℓ-suc ℓ}) 2)
                       → SatAtLevel φ → ElemDown → Hd.HoodExistsP φ
  hoodExistsP-from-sat φ s ed =
    hoodExistsP-from-cover φ (cover-from-sat φ s) ed


-- THE CHAPTER'S OWN FORMULA, NAMED ONCE at the top level: the
-- LevelHood0 matrix (src/L/BoundedSubset.lagda.md:848-849) re-slotted
-- to the pair v ∷ γ ∷ [] and erased to the parameter-free alphabet.
-- PART 1 is where it is built and where the erasure is measured.
levelhood0 :
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin 5)
    (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin 7)
  → Formula (⊥* {ℓ-suc ℓ}) 2
levelhood0 = Pinned.φ₀

module AtLevelHood0 (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin 5)
  (M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1 : Fin 7)
  (φ : Formula (⊥* {ℓ-suc ℓ}) 2)
  (qφ : φ ≡ levelhood0 N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
                       M0 M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 M11 s0 s1)
  where

  -- PROJECTED, NOT OPENED, for the reason PART 2 measures.  With the
  -- wholesale applications in, this file walled (runs/p-5.out,
  -- runs/b2-1.out, both exit 251); with them out it closes at 1.47 GB
  -- (runs/join-2.out).
  -- The obligation, MINUS its one residue.
  hoodexists-at-levelhood0-from-cover :
      Bridge.CoverP lam ordλ succλ X X⊆L ∅∈λ φ → Bridge.ElemDown lam ordλ succλ X X⊆L ∅∈λ → P653.HullStage.HoodExistsP lam ordλ succλ X X⊆L ∅∈λ φ
  hoodexists-at-levelhood0-from-cover = Bridge.hoodExistsP-from-cover lam ordλ succλ X X⊆L ∅∈λ φ

  -- The same, with premise 3's free half already spent.
  hoodexists-at-levelhood0-from-sat :
      Bridge.SatAtLevel lam ordλ succλ X X⊆L ∅∈λ φ → Bridge.ElemDown lam ordλ succλ X X⊆L ∅∈λ → P653.HullStage.HoodExistsP lam ordλ succλ X X⊆L ∅∈λ φ
  hoodexists-at-levelhood0-from-sat = Bridge.hoodExistsP-from-sat lam ordλ succλ X X⊆L ∅∈λ φ

  -- PREMISE 1, COMPOSED.  With the sibling's soundness half the pair
  -- closes `levelIn` at the chapter's own formula, and neither term
  -- mentions step 4.
  levelin-at-levelhood0 :
      Bridge.SatAtLevel lam ordλ succλ X X⊆L ∅∈λ φ → Bridge.ElemDown lam ordλ succλ X X⊆L ∅∈λ → P653.HullStage.HoodSoundP lam ordλ succλ X X⊆L ∅∈λ φ
    → P653.HullStage.LevelIn lam ordλ succλ X X⊆L ∅∈λ
  levelin-at-levelhood0 s ed sound =
    P653.HullStage.levelin-from-hood-pf lam ordλ succλ X X⊆L ∅∈λ φ
      (Bridge.hoodExistsP-from-sat lam ordλ succλ X X⊆L ∅∈λ φ s ed) sound
