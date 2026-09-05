{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.586]  `absorbs` IS DEFINABLE.
--
-- THE OBLIGATION IS `absorbs-definable`, SECTION 5.  It is INHABITED.
-- This file carries NO hole and NO postulate, so every reduction in it
-- is a measurement and not a claim.  NOTHING LANDS IN `src/`.
--
-- SECTION 1 IS W3 AND IT WAS WRITTEN FIRST AND TYPECHECKED ALONE.  The
-- slice is agents/tasks/LJ-1-586/runs/W3.agda; its runs are
-- runs/w3-2.out and runs/w3-3.out, exit 0.  Section 1 below repeats it
-- so this file stands alone.
--
-- THE ANSWER IN ONE LINE.  `absorbs` IS ONLY EVER A PARAMETER IN
-- `src/` (W3: one module application, ZERO terms), BUT THE SLOT HAS A
-- DELIVERED INHABITANT OUTSIDE `src/`, `[LJ-1.540]`'s `AbsorbsAt`, AND
-- THAT TERM IS DEFINABLE.  So the obligation is not the vacuous
-- "for any definable `absorbs`, it is definable": it is a DESCRIPTION
-- of the one term the campaign has built.
--
--   Section 1.  W3.  Parameter or term, and the pair as L-elements.
--   Section 2.  THE SITE, and `Def` at this `g`, ascribed.
--   Section 3.  THE FORMULA.  Three cases, mutually exclusive.
--   Section 4.  THE TWO DIRECTIONS.
--   Section 5.  THE OBLIGATION.
--   Section 6.  WHAT THIS DOES NOT SAY.
--
-- D-10 IS SECTION 1 AND IT CHANGED THE SHAPE OF THE TASK.  The brief
-- ordered the parameter/term question answered before any Agda, and
-- the answer moved the target from `src/` to `[LJ-1.540]`'s term.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )

module LJ-1-586.Probe586 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α : V ℓ) (ordα : IsOrd α)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ⊤̇ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; Lset→isL; 𝒟ₒ-intro; Lset-in )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Coding.InL {ℓ} using ( sglL; cupL )
open import L.Coding.Model {ℓ} using ( sucAtL; sucAtL-adequate )
open import L.BoundedSubset {ℓ} lem using ( _↪_ )
open import L.GCH {ℓ} lem using ( InjL )

open import Cubical.Data.Nat using ( ℕ; suc )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( _∪_; ⁅_⁆s )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open InfinitySet {ℓ} using ( ω; sucV; #_ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SL using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- THE PREDECESSORS, IMPORTED AND NEVER TRANSCRIBED.  Each is GO and
-- each probe is green, so every type below is the type that
-- typechecked in the file that delivered it.
import LJ-1-549.Probe549 {ℓ} lem as P549
import LJ-1-554.Probe554 {ℓ} lem as P554
import LJ-1-561.Probe561 {ℓ} lem α ordα sq as P561
import LJ-1-568.Probe568 {ℓ} lem α ordα sq as P568
import LJ-1-540.Probe540 {ℓ} lem as P540


-- ===================================================================
-- SECTION 1.  W3, BEFORE ANY OTHER AGDA.
--
--   THE BRIEF'S D-10: is `absorbs` a PARAMETER or a TERM?
--
--   THE GREP HALF.  `grep -rn "BoundedSubsetAt" src/` gives THREE
--   lines and exactly ONE is a module application:
--     src/L/BoundedSubset.lagda.md:1385   the declaration
--     src/L/StageBound.lagda.md:62        a comment
--     src/L/StageBound.lagda.md:74        THE ONLY APPLICATION
--   Its twelfth argument is the name `absorbs`
--   (src/L/StageBound.lagda.md:76), which is the enclosing module's OWN
--   parameter (:69).  The outer wrapper repeats the pass-through (:97
--   declared, :116 forwarded).  `L.StageBound` is imported by ONE file,
--   src/Everything.lagda.md:396, which only typechecks it.
--   SO THE COUNT OF CONCRETE TERMS SUPPLIED IN `src/` IS **ZERO**.
--
--   src/L/Absorption.lagda.md:635 carries the NAME at a DIFFERENT type,
--   `⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`, and does not fit the slot.  C-42:
--   a different statement at a different site, never read as this one.
--
--   THE AGDA HALF.  A parameter with no term is one thing; a parameter
--   with a DELIVERED inhabitant that `src/` has not yet plugged in is
--   another, and the two want different briefs.
-- ===================================================================

-- 1.1  THE SLOT'S TYPE, COPIED FROM THE PARAMETER LIST AND NOTHING
--      ELSE.  src/L/BoundedSubset.lagda.md:1391-1392.
Slot : (a b : SV.S) → Type ℓ
Slot a b = ⟪ Lset a ∪ ⁅ b ⁆s ⟫ ↪ ⟪ Lset a ⟫

-- 1.2  THE SLOT HAS A DELIVERED INHABITANT, AND IT IS NOT IN `src/`.
--      `[LJ-1.540]`'s `AbsorbsAt` (Probe540.agda:359-365) AT `Slot`.
candidate : (a b : SV.S) → IsOrd a → (⟨ a SV.∈ˢ ω ⟩ → Empty.⊥)
          → ((z : SV.S) → ⟨ z SV.∈ˢ b ⟩ → ⟨ z SV.∈ˢ Lset a ⟩)
          → Slot a b
candidate = P540.AbsorbsAt

-- 1.3  THE PAIR `Def` WOULD BE STATED AT, AS L-ELEMENTS.
--      `[LJ-1.568]`'s `Hyp` is `(a b : Sʟ) (g : ⟪ fst a ⟫ → ⟪ fst b ⟫)
--      → Type` (Probe568.agda:159-160).  `absorbs` is a map between the
--      members of two AMBIENT sets, so `Def` cannot even be STATED at
--      it until both sets are shown to be L-elements.
--      The stage is `[LJ-1.580]`'s `Lset-isL` (Probe580.agda:104-107),
--      re-typed rather than imported: importing Probe580 costs its
--      whole site telescope and this file needs four lines of it.
--      The union is TWO facts already in `src/`, `sglL` and `cupL`
--      (src/L/Coding/InL.lagda.md:206, :211).
Lset-isL : (γ : SV.S) → IsOrd γ → ⟨ isL (Lset γ) ⟩
Lset-isL γ oγ = Lset→isL (sucV γ) (suc-ord oγ) (Lset γ)
  (Lset-in (sucV γ) γ (Lset γ) (self∈sucV γ)
    (𝒟ₒ-intro (Lset γ) (Lset γ) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset γ) ∣₁))

dom-isL : (a lam b : SV.S) → IsOrd a → IsOrd lam → ⟨ b SV.∈ˢ Lset lam ⟩
        → ⟨ isL (Lset a ∪ ⁅ b ⁆s) ⟩
dom-isL a lam b oa oλ b∈Lλ =
  cupL (Lset-isL a oa) (sglL (Lset→isL lam oλ b b∈Lλ))


-- ===================================================================
-- SECTION 2.  THE SITE, AND `Def` AT THIS `g`.
--
--   The telescope is `Devlin55.BoundedSubsetAt`'s
--   (src/L/BoundedSubset.lagda.md:1385-1395) restricted to the
--   parameters the twelfth one depends on.  κ, cardκ, α∈κ, succλ and
--   the two transfer hypotheses are not read here and are not bound.
-- ===================================================================

module Site (lam xe : SV.S) (ordλ : IsOrd lam)
            (α∉ω : ⟨ α SV.∈ˢ ω ⟩ → Empty.⊥)
            (xe⊆Lα : (z : SV.S) → ⟨ z SV.∈ˢ xe ⟩ → ⟨ z SV.∈ˢ Lset α ⟩)
            (xe∈Lλ : ⟨ xe SV.∈ˢ Lset lam ⟩) where

  -- 2.1  THE TWO L-SETS.  `Dᴸ` is `UnionKit.X`
  --      (src/L/BoundedSubset.lagda.md:1149-1150) with its level-hood.
  Dᴸ : S
  Dᴸ = Lset α ∪ ⁅ xe ⁆s , dom-isL α lam xe ordα ordλ xe∈Lλ

  Cᴸ : S
  Cᴸ = Lset α , Lset-isL α ordα

  -- 2.2  THE ADJOINED ELEMENT, AS AN L-SET.  It is a member of a stage.
  xᴸ : S
  xᴸ = xe , Lset→isL lam ordλ xe xe∈Lλ

  -- 2.3  THE FUNCTION.  `[LJ-1.540]`'s term, and its shift machinery
  --      opened so the three readback lemmas are the ones that
  --      typechecked there and not copies.
  module Sh = P540.Shift α xe ordα α∉ω
  module SA = Sh.SA

  g : ⟪ fst Dᴸ ⟫ → ⟪ fst Cᴸ ⟫
  g = Sh.shift

  -- AND IT IS `absorbs`, NOT A LOOKALIKE.  `refl` is the elaborator's
  -- word that `g` is the first projection of the delivered `Slot` term.
  g-is-absorbs : g ≡ fst (candidate α xe ordα α∉ω xe⊆Lα)
  g-is-absorbs = refl

  -- 2.4  THE OBLIGATION'S TYPE.  `[LJ-1.568]`'s `Def`, IMPORTED
  --      (Probe568.agda:189-190), at this pair and this `g`.
  Target : Type (ℓ-suc ℓ)
  Target = P568.Def Dᴸ Cᴸ g

  -- 2.5  THE ASSIGNMENT `Def` READS.  `[LJ-1.568]`'s `val`
  --      (Probe568.agda:175) is `up b (g k)`, so `fst (s k)` is the
  --      ambient value of the shift at `k` and nothing else.
  s : ⟪ fst Dᴸ ⟫ → S
  s = P568.val Dᴸ Cᴸ g

  s-fst : (k : ⟪ fst Dᴸ ⟫) → fst (s k) ≡ ⟪ Lset α ⟫↪ (Sh.shift k)
  s-fst k = refl


  -- =================================================================
  -- SECTION 3.  THE FORMULA.
  --
  --   THREE CASES, AND THEY ARE `[LJ-1.540]`'s OWN THREE
  --   (Probe540.agda:235-238) READ AS SYNTAX.  Environment
  --   `(y ∷ u ∷ z ∷ [])`, so `var zero` is the VALUE and
  --   `var (suc zero)` is the ARGUMENT.  `z` is `LinkAt`'s spare and
  --   no case mentions it.
  --
  --   WHAT IS BORROWED FROM `src/L/Absorption.lagda.md:211-222`: the
  --   shape of the three cases and the `sucAtL` reading of the numeral
  --   case.  WHAT IS NOT, and each is a real difference:
  --
  --   * CASE 2 CARRIES `¬̇ (u ∈̇ ω)`.  `shiftCase2` (:215) does not,
  --     because `ShiftGraph` is handed `γ∉ω` (:540) and the top element
  --     is therefore never a numeral.  `[LJ-1.540]` has NO hypothesis
  --     on `xe` (Probe540.agda:35-38 is the measurement) and `xe` MAY
  --     be a numeral, in which case case 1 takes it.  Without this
  --     conjunct cases 1 and 2 would overlap and demand two values.
  --
  --   * CASE 3 TESTS `¬̇ (u ≐ xe)` AND NOT `u ∈̇ γ`.  `shiftCase3`
  --     (:218) discriminates by membership in the top ordinal and
  --     closes the overlap with `∈-irrefl`.  Here the domain is a union
  --     with a singleton, not a successor, so there is no such
  --     ordinal, and the negation of case 2's own test is what the
  --     ambient `shift-other` (Probe540.agda:276-279) actually consumes.
  --     THAT IS WHY THIS FILE NEEDS NO `D-in-dec`
  --     (src/L/Absorption.lagda.md:239-240): the three tests are
  --     decided by `lem` alone and are manifestly exclusive.
  --
  --   NO LEVY GRADE IS ASKED FOR.  The separation `Def` is spent
  --   through is `hasSeparationL` (src/L/Axioms/Full.lagda.md:144),
  --   which takes an ARBITRARY formula, so the two negations are free.
  --   `[LJ-1.568]`'s section 1.3 (Probe568.agda:185-188) records that.
  -- =================================================================

  Case1 : Formula S 3
  Case1 = (var (suc zero) ∈̇ con ωʟ) ∧̇ sucAtL (suc zero) zero

  Case2 : Formula S 3
  Case2 = ¬̇ (var (suc zero) ∈̇ con ωʟ)
        ∧̇ ((var (suc zero) ≐ con xᴸ) ∧̇ (var zero ≐ con ∅ʟ))

  Case3 : Formula S 3
  Case3 = ¬̇ (var (suc zero) ∈̇ con ωʟ)
        ∧̇ (¬̇ (var (suc zero) ≐ con xᴸ) ∧̇ (var zero ≐ var (suc zero)))

  Link : Formula S 3
  Link = Case1 ∨̇ (Case2 ∨̇ Case3)

  -- THE ONE ADEQUACY THE TREE SUPPLIES.  src/L/Coding/Model.lagda.md
  -- :1398-1400, at this environment.
  sucRead : (u y z : S) → ⟨ (y ∷ u ∷ z ∷ []) ⊨ sucAtL (suc zero) zero ⟩
          ≡ (fst y ≡ sucV (fst u))
  sucRead u y z = cong ⟨_⟩ (sucAtL-adequate (suc zero) zero (y ∷ u ∷ z ∷ []))

  -- THE EMPTY SET IS THE NUMERAL 0.  `[LJ-1.540]`'s case 2 lands on
  -- `# 0` (Probe540.agda:237) and the formula names `∅ʟ`
  -- (src/L/Axioms/Basic.lagda.md:507).  `refl` is the elaborator's word
  -- that they are the same set.
  ∅≡num0 : fst ∅ʟ ≡ # 0
  ∅≡num0 = refl


  -- =================================================================
  -- SECTION 4.  THE TWO DIRECTIONS.
  --
  --   Both are stated at a member `u` of the domain, whose index is
  --   `[LJ-1.549]`'s `ixOf` (Probe549.agda:262-263) and whose value
  --   equation is `ixOf-val` (:265-266).
  -- =================================================================

  module At (u : S) (m : ⟨ fst u ∈ fst Dᴸ ⟩) where

    k : ⟪ fst Dᴸ ⟫
    k = P549.ixOf Dᴸ u m

    kv : Sh.v-of k ≡ fst u
    kv = P549.ixOf-val Dᴸ u m

    val : V ℓ
    val = ⟪ Lset α ⟫↪ (Sh.shift k)

    -- 4.1  THE THREE READBACKS, MOVED FROM THE INDEX TO `fst u`.
    --      Each is `[LJ-1.540]`'s lemma with `kv` on the outside.
    numChain : (u∈ω : ⟨ fst u ∈ ω ⟩) → val ≡ sucV (fst u)
    numChain u∈ω =
      Sh.shift-num k v∈ω
      ∙ cong sucV (sym (SA.numeralOf-spec (Sh.v-of k) v∈ω))
      ∙ cong sucV kv
      where
      v∈ω : ⟨ Sh.v-of k ∈ ω ⟩
      v∈ω = subst (λ w → ⟨ w ∈ ω ⟩) (sym kv) u∈ω

    topChain : (¬u∈ω : ⟨ fst u ∈ ω ⟩ → Empty.⊥) → (fst u ≡ xe) → val ≡ # 0
    topChain ¬u∈ω u≡x = Sh.shift-top k ¬v∈ω (kv ∙ u≡x)
      where
      ¬v∈ω : ⟨ Sh.v-of k ∈ ω ⟩ → Empty.⊥
      ¬v∈ω h = ¬u∈ω (subst (λ w → ⟨ w ∈ ω ⟩) kv h)

    othChain : (¬u∈ω : ⟨ fst u ∈ ω ⟩ → Empty.⊥)
             → ((fst u ≡ xe) → Empty.⊥) → val ≡ fst u
    othChain ¬u∈ω ¬u≡x = Sh.shift-other k ¬v∈ω ¬v≡x ∙ kv
      where
      ¬v∈ω : ⟨ Sh.v-of k ∈ ω ⟩ → Empty.⊥
      ¬v∈ω h = ¬u∈ω (subst (λ w → ⟨ w ∈ ω ⟩) kv h)
      ¬v≡x : (Sh.v-of k ≡ xe) → Empty.⊥
      ¬v≡x h = ¬u≡x (sym kv ∙ h)

  -- 4.2  THE FORMULA IMPLIES THE VALUE.  `link-out`.
  link-out : (u y z : S) → ⟨ (y ∷ u ∷ z ∷ []) ⊨ Link ⟩
           → (m : ⟨ fst u ∈ fst Dᴸ ⟩) → fst y ≡ fst (s (P549.ixOf Dᴸ u m))
  link-out u y z h m = PT.rec (setIsSet (fst y) A.val) go h
    where
    module A = At u m
    go : ⟨ (y ∷ u ∷ z ∷ []) ⊨ Case1 ⟩
       ⊎ ⟨ (y ∷ u ∷ z ∷ []) ⊨ (Case2 ∨̇ Case3) ⟩
       → fst y ≡ A.val
    go (inl c1) =
      subst (λ T → T) (sucRead u y z) (snd c1) ∙ sym (A.numChain (fst c1))
    go (inr c23) = PT.rec (setIsSet (fst y) A.val) go23 c23
      where
      go23 : ⟨ (y ∷ u ∷ z ∷ []) ⊨ Case2 ⟩ ⊎ ⟨ (y ∷ u ∷ z ∷ []) ⊨ Case3 ⟩
           → fst y ≡ A.val
      go23 (inl c2) = snd (snd c2) ∙ ∅≡num0
                    ∙ sym (A.topChain (fst c2) (fst (snd c2)))
      go23 (inr c3) = snd (snd c3)
                    ∙ sym (A.othChain (fst c3) (fst (snd c3)))

  -- 4.3  THE VALUE IMPLIES THE FORMULA.  `link-in`.  Two decisions by
  --      `lem`, and every corner is one of the three cases.
  link-in : (u y z : S) (m : ⟨ fst u ∈ fst Dᴸ ⟩)
          → fst y ≡ fst (s (P549.ixOf Dᴸ u m))
          → ⟨ (y ∷ u ∷ z ∷ []) ⊨ Link ⟩
  link-in u y z m e = go (lem (fst u ∈ ω))
                         (lem ((fst u ≡ xe) , setIsSet (fst u) xe))
    where
    module A = At u m
    go : ⟨ fst u ∈ ω ⟩ ⊎ (⟨ fst u ∈ ω ⟩ → Empty.⊥)
       → (fst u ≡ xe) ⊎ ((fst u ≡ xe) → Empty.⊥)
       → ⟨ (y ∷ u ∷ z ∷ []) ⊨ Link ⟩
    go (inl u∈ω) _ = ∣ inl
      (u∈ω , subst (λ T → T) (sym (sucRead u y z)) (e ∙ A.numChain u∈ω)) ∣₁
    go (inr ¬u∈ω) (inl u≡x) = ∣ inr
      ∣ inl (¬u∈ω , (u≡x , (e ∙ A.topChain ¬u∈ω u≡x ∙ sym ∅≡num0))) ∣₁ ∣₁
    go (inr ¬u∈ω) (inr ¬u≡x) = ∣ inr
      ∣ inr (¬u∈ω , (¬u≡x , (e ∙ A.othChain ¬u∈ω ¬u≡x))) ∣₁ ∣₁


  -- =================================================================
  -- SECTION 5.  THE OBLIGATION.
  -- =================================================================

  definable : Target
  definable = Link , (link-in , link-out)

  -- 5.1  AND WHAT IT BUYS, THROUGH THE TWO PREDECESSORS AND NOTHING
  --      NEW.  `[LJ-1.568]`'s `def-restricted` (Probe568.agda:252-253)
  --      turns `Def` into the graph, and `[LJ-1.561]`'s `Code.code`
  --      (Probe561.agda:283-284) reads the four conjuncts off it.
  --      THE RESULT IS `absorbs` WITH A CODE.
  ginj : (k k' : ⟪ fst Dᴸ ⟫) → g k ≡ g k' → k ≡ k'
  ginj = Sh.shift-inj

  coded : InjL Dᴸ Cᴸ
  coded = PT.map
    (λ { (G , (gin , gout)) → G , P561.Code.code Dᴸ Cᴸ g ginj G gin gout })
    (P568.def-restricted Dᴸ Cᴸ g ginj definable)


-- ===================================================================
-- THE OBLIGATION, AT TOP LEVEL.
--
--   Stated at `fst (candidate ...)` and NOT at `Site.g`, so the type
--   names `[LJ-1.540]`'s delivered term and nothing this file invented.
--   `Site.g-is-absorbs` is the `refl` that lets it.
-- ===================================================================

absorbs-definable :
    (lam xe : SV.S) (ordλ : IsOrd lam)
    (α∉ω : ⟨ α SV.∈ˢ ω ⟩ → Empty.⊥)
    (xe⊆Lα : (z : SV.S) → ⟨ z SV.∈ˢ xe ⟩ → ⟨ z SV.∈ˢ Lset α ⟩)
    (xe∈Lλ : ⟨ xe SV.∈ˢ Lset lam ⟩)
  → P568.Def (Site.Dᴸ lam xe ordλ α∉ω xe⊆Lα xe∈Lλ)
             (Site.Cᴸ lam xe ordλ α∉ω xe⊆Lα xe∈Lλ)
             (fst (candidate α xe ordα α∉ω xe⊆Lα))
absorbs-definable = Site.definable

-- AND ITS CONSEQUENCE, WHICH IS WHAT B7 AND ROW 1 BOTH ASKED FOR.
absorbs-coded :
    (lam xe : SV.S) (ordλ : IsOrd lam)
    (α∉ω : ⟨ α SV.∈ˢ ω ⟩ → Empty.⊥)
    (xe⊆Lα : (z : SV.S) → ⟨ z SV.∈ˢ xe ⟩ → ⟨ z SV.∈ˢ Lset α ⟩)
    (xe∈Lλ : ⟨ xe SV.∈ˢ Lset lam ⟩)
  → InjL (Site.Dᴸ lam xe ordλ α∉ω xe⊆Lα xe∈Lλ)
         (Site.Cᴸ lam xe ordλ α∉ω xe⊆Lα xe∈Lλ)
absorbs-coded = Site.coded


-- ===================================================================
-- SECTION 6.  WHAT THIS DOES NOT SAY.
--
--   C-42's SWEEP, RUN AND COUNTED BEFORE ANY CLAIM ABOUT REACH.  The
--   shape is "a bare `_↪_` handed in as an open parameter and then
--   consumed by a coding step".
--   `grep -rn "( *[A-Za-z][A-Za-z0-9'-]* *: *⟪.*⟫ *↪ *⟪.*⟫ *)" src/`
--   returns SIX lines and they are THREE objects:
--
--     src/L/BoundedSubset.lagda.md:1392  `absorbs`, the real parameter
--     src/L/StageBound.lagda.md:69, :97  the SAME object, passed on
--     src/L/StageCardinal.lagda.md:281, :397  `ih`, the stage-bound
--                                        induction hypothesis
--     src/L/BoundedSubset.lagda.md:1409  `CodeCount`'s `g`, which is
--                                        NOT open: it is applied at
--                                        `code-inj` (:1515)
--
--   SO THE OPEN ONES ARE TWO: `absorbs` and the stage bound.  That is
--   `[LJ-1.580]`'s "two uncoded things" reached by a different route,
--   and it is the reason `[LJ-1.584]` and this task partition the work.
--   THIS FILE PAYS ONE OF THE TWO AND CLAIMS NOTHING ABOUT THE OTHER.
-- ===================================================================

-- 6.1  THE ARBITRARY CASE IS NOT TOUCHED.  TYPE ONLY, NOT INHABITED.
--      `[LJ-1.533]` refuted a code for an ARBITRARY ambient injection
--      (agents/tasks/LJ-1-533/lj-1.533-report.md:42-43), and this file
--      never quantifies over the injection: `absorbs-definable` names
--      `[LJ-1.540]`'s ONE term.  The difference is one Π, written here
--      so it cannot be read out of the obligation by mistake.
Arbitrary :
    (lam xe : SV.S) (ordλ : IsOrd lam)
    (α∉ω : ⟨ α SV.∈ˢ ω ⟩ → Empty.⊥)
    (xe⊆Lα : (z : SV.S) → ⟨ z SV.∈ˢ xe ⟩ → ⟨ z SV.∈ˢ Lset α ⟩)
    (xe∈Lλ : ⟨ xe SV.∈ˢ Lset lam ⟩)
  → Type (ℓ-suc ℓ)
Arbitrary lam xe ordλ α∉ω xe⊆Lα xe∈Lλ =
    (h : Slot α xe)
  → P568.Def (Site.Dᴸ lam xe ordλ α∉ω xe⊆Lα xe∈Lλ)
             (Site.Cᴸ lam xe ordλ α∉ω xe⊆Lα xe∈Lλ) (fst h)

-- 6.2  AND `src/` STILL SUPPLIES NOTHING.  W3's count is ZERO, so
--      `src/L/StageBound.lagda.md:69` still carries an OPEN `absorbs`
--      and no term of this file reaches it.  Closing that is a change
--      to `src/`, which this task is forbidden to make, and it is a
--      decision for the mathematician: either `L.StageBound` takes
--      `[LJ-1.540]`'s term as its default, or the parameter stays open
--      and gains a definability hypothesis beside it.
