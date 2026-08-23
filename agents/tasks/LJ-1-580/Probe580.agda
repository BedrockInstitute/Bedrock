{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.580]  Give `β↪α` a code.
--
-- SECTION 1 is W3 and the brief ordered it written FIRST and typechecked
-- ALONE.  runs/w3-1.out is that run.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-580.Probe580 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans; Lset→isL; 𝒟ₒ; 𝒟ₒ-intro; Lset-in )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55; module CodeSelect; module InvColl )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module Comp )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( SWO )
open import V.Model {ℓ} using ( self∈sucV )
open import FOL.Syntax using ( ⊤̇ )

-- THE INTERFACE `[LJ-1.577]` WROTE, IMPORTED AND NOT RESTATED, so it
-- cannot drift (agents/tasks/LJ-1-577/Probe577.agda:363, :368).
open import LJ-1-577.Probe577 {ℓ} lem using ( GapAtPair; gap-is-a-code )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  THE CODE SELECTION LEG, RE-ASCRIBED ALONE.  TYPE ONLY.
--
--   The brief names this the widest unmeasured term: the code selection
--   inside `β↪α`, which "may already carry what you need".  The leg is
--   `CodeSelect` (src/L/BoundedSubset.lagda.md:1099-1140), applied at
--   the site as `CSel` (:1518-1520).  The question W3 settles is what
--   that module DELIVERS, at its own parameters and not at a copy.
-- =====================================================================

module W3
  (α : SV.S) (oα : IsOrd α) (w : SWO {ℓ} ⟪ α ⟫)
  (M : SV.S) (Code : Type ℓ) (val : Code → SV.S)
  (mem-code : (x : SV.S) → ⟨ x ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (val c ≡ x) ∥₁)
  (cnt : Code → ⟪ α ⟫)
  (cnt-inj : (c d : Code) → cnt c ≡ cnt d → c ≡ d)
  where

  module CSel = CodeSelect α oα w M Code val mem-code cnt cnt-inj

  -- WHAT THE LEG DELIVERS TODAY.  A bare `_↪_`: a function and an
  -- injectivity proof, with no `Formula` in the type and no `InjCode`.
  delivered : ⟪ M ⟫ ↪ ⟪ α ⟫
  delivered = CSel.leg2

  -- WHAT THE COMPOSITE NEEDS FROM IT.  TYPE ONLY.  NOT INHABITED HERE.
  Coded : ⟨ isL M ⟩ → ⟨ isL α ⟩ → Type (ℓ-suc ℓ)
  Coded Ml αl = InjL (M , Ml) (α , αl)

-- =====================================================================
-- SECTION 2.  TWO L-ELEMENT FACTS THE COMPOSITION NEEDS.
--
--   `Comp` (src/L/InjChain.lagda.md:314) composes two CODED injections
--   through an intermediate object, and every one of its five sets is
--   an L-element.  The intermediate object here is the collapse
--   `HS.C.πX`, and `ext` (src/L/BoundedSubset.lagda.md:1568) says it is
--   a STAGE.  So the composition needs level-hood of a stage, and the
--   tree does not carry it at this shape today.
-- =====================================================================

-- Every ordinal is an L-element.  `[LJ-1.386]`'s one-liner, restated
-- here rather than imported, because `L.SquareLawClosed` takes an
-- ordinal parameter this file has no use for
-- (src/L/SquareLawClosed.lagda.md:19-20, :51-52).
ord-isL : (γ : SV.S) → IsOrd γ → ⟨ isL γ ⟩
ord-isL γ oγ = Lset→isL (sucV γ) (suc-ord oγ) γ (ord∈Lset-suc γ oγ)

-- EVERY STAGE OF THE TOWER IS AN L-ELEMENT.  `grep -rn "isL (Lset" src/`
-- returns nothing, so this shape is not in the tree.  It is one line
-- from two things that ARE: `defSet ⊤̇ ≡ A`
-- (src/L/Definability.lagda.md:178) puts the whole stage inside its own
-- `𝒟ₒ`, and `Lset-in` (src/L/Constructible.lagda.md:319) raises that to
-- the next stage.
Lset-isL : (γ : SV.S) → IsOrd γ → ⟨ isL (Lset γ) ⟩
Lset-isL γ oγ = Lset→isL (sucV γ) (suc-ord oγ) (Lset γ)
  (Lset-in (sucV γ) γ (Lset γ) (self∈sucV γ)
    (𝒟ₒ-intro (Lset γ) (Lset γ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset γ) ∣₁))

-- =====================================================================
-- SECTION 3.  THE SITE, AND THE TWO LEGS NAMED AS TERMS.
--
--   `Devlin55.BoundedSubsetAt`'s telescope (src/L/BoundedSubset.lagda.md
--   :1385-1395), with κ carrying level-hood so the obligation's pair is
--   a pair of L-elements.  No ambient cardinal is claimed to exist: the
--   parameter is bound here and every term below is Π over it.
-- =====================================================================

module Site
  (κᴸ : SL.S) (ordκ : IsOrd (fst κᴸ)) (cardκ : IsCardinal (fst κᴸ))
  (κ∉ω : ⟨ fst κᴸ ∈ˢ ω ⟩ → Empty.⊥)
  (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ fst κᴸ ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : (δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v))
  (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module BSA = Devlin55.BoundedSubsetAt
    (fst κᴸ) ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
    lam ordλ α∈λ succλ x∈Lλ

  -- α is an L-element because κ is one and `isL` is transitive
  -- (src/L/Constructible.lagda.md:379).  This is [LJ-1.577]'s own lift,
  -- at Probe577.agda:254-255.
  αᴸ : SL.S
  αᴸ = α , isL-trans {x = fst κᴸ} {y = α} α∈κ (snd κᴸ)

  -- THE COUNT APPLIES `absorbs`.  `CC.count` on a base code is
  -- src/L/BoundedSubset.lagda.md:1422, and its `g` is `code-inj`
  -- (:1512-1513), which is `absorbs` composed with the stage-cardinality
  -- UPPER bound.  This `refl` is the elaborator's word for that, and not
  -- a reading of the page.
  count-applies-absorbs : (m : ⟪ Lset α ∪ ⁅ x ⁆s ⟫)
    → BSA.CC.count (BSA.HS.H.T.base m)
      ≡ BSA.CC.B.pair (BSA.CC.B.numeral 0)
          (fst (BSA.stage-card-upper α ordα (self∈sucV α) α∉ω)
               (fst absorbs m))
  count-applies-absorbs m = refl

  -- The step's own context: `Co`'s two transfer hypotheses, at the
  -- tree's own spelling (src/L/BoundedSubset.lagda.md:1555-1558).
  module CoAt
    (levelIn : (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩
             → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩)
    (cover : (y : SV.S) → ⟨ y ∈ˢ BSA.HS.M ⟩
           → ∥ Σ[ γ ∈ SV.S ]
                ( IsOrd γ × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩
                × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁)
    where

    module C = BSA.Co levelIn cover

    -- THE INJECTION THE BRIEF NAMES.  src/L/BoundedSubset.lagda.md:1578.
    the-injection : ⟪ C.β ⟫ ↪ ⟪ α ⟫
    the-injection = C.β↪α

    -- LEG 1.  The stage-cardinality bound at β
    -- (src/L/BoundedSubset.lagda.md:1581, body
    -- src/L/StageCardinal.lagda.md:209-211), moved along the
    -- condensation identity `ext` (:1568).
    leg1 : ⟪ C.β ⟫ ↪ ⟪ BSA.HS.C.πX ⟫
    leg1 = subst (λ A → ⟪ C.β ⟫ ↪ ⟪ A ⟫) (sym C.ext)
             (BSA.SC.stage-card-lower C.β C.β-isOrd)

    -- LEG 2.  The code selection after the inverse collapse
    -- (src/L/BoundedSubset.lagda.md:1574-1576).  `CSel.h ∘ IC.inv`.
    leg2 : ⟪ BSA.HS.C.πX ⟫ ↪ ⟪ α ⟫
    leg2 = C.πX↪α

    -- AND THE COMPOSITE IS THOSE TWO LEGS AND NOTHING ELSE.
    -- AND THE COMPOSITE IS THOSE TWO LEGS AND NOTHING ELSE.  This one
    -- `refl` cost 96 of the file's seconds (runs/s3-1.out against
    -- runs/s2-2.out): a `refl` across a module application must unfold
    -- the injection, and the injection pulls the whole hull.  That is
    -- [LJ-1.577]'s measured law at its own site (lj-1.577-report.md
    -- :130-141), re-measured here and not carried over.
    two-legs : the-injection ≡ Devlin55.comp-inj leg1 leg2
    two-legs = refl

    -- AND LEG 2 IS THE CODE SELECTION AFTER THE INVERSE COLLAPSE.
    -- `CSel` is src/L/BoundedSubset.lagda.md:1518, `IC` is :1517.
    leg2-is-code-selection : fst leg2 ≡ (λ p → BSA.CSel.h (BSA.IC.inv p))
    leg2-is-code-selection = refl

    -- ---------------------------------------------------------------
    -- SECTION 4.  LEG 1, CODED.
    --
    --   Leg 1 IS an inclusion: β ⊆ Lset β, moved along `ext`.  The tree
    --   codes any inclusion between two L-elements: `InclGraph`
    --   (src/L/InjChain.lagda.md:575-598) over the formula `inclFo`
    --   (:445-446), through `hasSeparationL`.  So leg 1 costs a module
    --   application and the two level-hood facts of SECTION 2.
    -- ---------------------------------------------------------------

    βᴸ : SL.S
    βᴸ = C.β , ord-isL C.β C.β-isOrd

    πXᴸ : SL.S
    πXᴸ = BSA.HS.C.πX
        , subst (λ w → ⟨ isL w ⟩) (sym C.ext) (Lset-isL C.β C.β-isOrd)

    -- β ⊆ πX.  This is leg 1's content: `Lower.α⊆Lset`
    -- (src/L/StageCardinal.lagda.md:193-195) says an ordinal's members
    -- lie in its own stage, and `ext` moves the stage to the collapse.
    β⊆πX : (z : SV.S) → ⟨ z ∈ˢ fst βᴸ ⟩ → ⟨ z ∈ˢ fst πXᴸ ⟩
    β⊆πX z z∈β = subst (λ w → ⟨ z ∈ˢ w ⟩) (sym C.ext)
      (BSA.SC.Lower.α⊆Lset C.β C.β-isOrd z z∈β)

    module Leg1 = InclGraph βᴸ πXᴸ β⊆πX

    -- THE FOUR CONJUNCTS AT ONE CARVE, PACKED.  `[LJ-1.566]` measured
    -- that packing three conjuncts from three SPELLINGS of one carve
    -- does not elaborate (lj-1.566-report.md:41-45).  Here the four come
    -- from ONE `Carve` at ONE `G`, which is the shape `src/` already
    -- packs at src/L/Absorption.lagda.md:619-620.  Re-measured, not
    -- assumed.
    leg1-coded : InjCode Leg1.G βᴸ πXᴸ
    leg1-coded = Leg1.sv , Leg1.dm , Leg1.ij , Leg1.ran

    -- ---------------------------------------------------------------
    -- SECTION 5.  THE COMPOSITION, AND WHAT IS LEFT AFTER IT.
    --
    --   `Comp` (src/L/InjChain.lagda.md:314-433) turns two coded
    --   injections into one, by separation and NOT by replacement.  With
    --   leg 1 coded, the whole obligation is leg 2's code and nothing
    --   else.  That is the residue this task returns, and it is ONE
    --   named statement.
    -- ---------------------------------------------------------------

    leg2-coded→at-β : InjL πXᴸ αᴸ → InjL βᴸ αᴸ
    leg2-coded→at-β = PT.map step
      where
      step : Σ[ H ∈ SL.S ] InjCode H πXᴸ αᴸ
           → Σ[ F ∈ SL.S ] InjCode F βᴸ αᴸ
      step (H , (svH , dmH , ijH , ranH)) =
        K.K , (K.svK , K.dmK , K.ijK , K.ranK)
        where
        module K = Comp βᴸ πXᴸ αᴸ Leg1.G H
                     Leg1.sv Leg1.dm Leg1.ij Leg1.ran
                     svH dmH ijH ranH

    -- AND THE PAIR THE STEP ACTUALLY SPENDS AT IS (κᴸ , αᴸ), NOT
    -- (βᴸ , αᴸ).  `[LJ-1.577]`'s critic said so in those words
    -- (agents/tasks/LJ-1-577/review-of-LJ-1-577-1.md, question 3: "The
    -- next brief must take `gap-is-a-code`, not the slogan").  In both
    -- refuted branches of the trichotomy κ ⊆ β, and a coded inclusion
    -- plus `Comp` carries the code across.
    at-β→at-κ :
        ((z : SV.S) → ⟨ z ∈ˢ fst κᴸ ⟩ → ⟨ z ∈ˢ C.β ⟩)
      → InjL βᴸ αᴸ → InjL κᴸ αᴸ
    at-β→at-κ κ⊆β = PT.map step
      where
      module Iκ = InclGraph κᴸ βᴸ κ⊆β
      step : Σ[ F ∈ SL.S ] InjCode F βᴸ αᴸ
           → Σ[ G ∈ SL.S ] InjCode G κᴸ αᴸ
      step (F , (svF , dmF , ijF , ranF)) =
        K.K , (K.svK , K.dmK , K.ijK , K.ranK)
        where
        module K = Comp κᴸ βᴸ αᴸ Iκ.G F
                     Iκ.sv Iκ.dm Iκ.ij Iκ.ran
                     svF dmF ijF ranF

    -- ---------------------------------------------------------------
    -- SECTION 6.  THE OBLIGATION, AND THE ONE THING THAT IS MISSING.
    --
    --   THE OBLIGATION `beta-into-alpha-coded` IS NOT IN THIS FILE.  It
    --   is a NO-GO and
    --   agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md states
    --   it.  `BetaIntoAlphaCoded` is its TYPE, `Leg2Coded` is the one
    --   residue, and `obligation-from-leg2` is the nearest term that
    --   exists.
    -- ---------------------------------------------------------------

    -- The obligation's type: `gap-is-a-code`'s antecedent
    -- (agents/tasks/LJ-1-577/Probe577.agda:368-369) at the pair the
    -- brief names.
    BetaIntoAlphaCoded : Type (ℓ-suc ℓ)
    BetaIntoAlphaCoded = ⟪ fst βᴸ ⟫ ↪ ⟪ fst αᴸ ⟫ → InjL βᴸ αᴸ

    -- THE RESIDUE.  Leg 2's code, and nothing else.
    Leg2Coded : Type (ℓ-suc ℓ)
    Leg2Coded = InjL πXᴸ αᴸ

    -- NOT THE OBLIGATION AND NOT OFFERED AS ONE.  The obligation has
    -- NOTHING to the left of its arrow beyond the ambient injection.
    -- This term carries `Leg2Coded`, and does not even read the ambient
    -- injection: once leg 2 is coded, the ambient input is dead weight.
    obligation-from-leg2 : Leg2Coded → BetaIntoAlphaCoded
    obligation-from-leg2 h _ = leg2-coded→at-β h

    -- AND THE RESIDUE IS A STATEMENT ABOUT A STAGE, NOT ABOUT THE HULL.
    -- `ext` (src/L/BoundedSubset.lagda.md:1568) says the collapse IS
    -- `Lset β`, so `Leg2Coded` reads: IN L, THE STAGE `Lset β` INJECTS
    -- INTO α.  That is Devlin 1.1(vii)'s size equation, internalised, at
    -- one pair.
    residue-is-a-stage-bound :
      Leg2Coded ≡ InjL (Lset C.β , Lset-isL C.β C.β-isOrd) αᴸ
    residue-is-a-stage-bound =
      cong (λ a → InjL a αᴸ)
        (Σ≡Prop {A = SV.S} {B = λ w → ⟨ isL w ⟩} (λ w → snd (isL w))
          {u = πXᴸ} {v = Lset C.β , Lset-isL C.β C.β-isOrd} C.ext)

    -- THE INTERFACE CLOSES ONCE THE RESIDUE IS PAID.  `gap-is-a-code` is
    -- IMPORTED, so nothing here restates it.
    gap-closed : Leg2Coded → GapAtPair βᴸ αᴸ
    gap-closed h = gap-is-a-code βᴸ αᴸ (obligation-from-leg2 h)
