{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.535]  Does the formula survive to where the injection is formed?
--
-- VERDICT: NO-GO on the brief's obligation.  `stage-card-upper-coded` is
-- NOT written in this file.  The obstruction is
-- agents/tasks/LJ-1-535/review-of-stage-card-upper-coded.md.
--
-- THIS FILE IS GREEN ON PURPOSE (the [LJ-1.533] discipline).  A hole
-- would make every line below a claim; green makes each one a
-- measurement.  What it measures:
--
--   W3.  THE FORMULA SURVIVES TO THE SITE AND NOT INTO THE VALUE.
--        Section 2 EXTRACTS it, untruncated, at the very ordinal where
--        `stage-card-upper` forms its injection: for every member x of
--        `Lset α` there is an honest `m : ⟪ α ⟫` and an honest
--        `φ : Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1` with
--        `defSet (Lset (⟪ α ⟫↪ m)) φ ≡ x` and `pack m φ ≡ f x`.
--        That is a Formula-carrying restatement and it typechecks.
--
--   AND IT IS STILL NOT ENOUGH.  Section 3 shows, by types alone, that
--        the formula does not reach the VALUE.  `count-bound`
--        (src/L/StageCardinal.lagda.md:124-129) builds `f x` from three
--        ingredients, and the formula is present in exactly one of them
--        and only as a NATURAL NUMBER:
--          * `code`, whose domain is the parameter-FREE shape
--            `Formula (⊥* {ℓ}) k` and whose codomain is `ℕ`
--            (src/FOL/Count.lagda.md:81);
--          * `tuple-g`, which embeds the parameters through a bare
--            ambient `g` that carries no `Formula`;
--          * `pair`, the module parameter `sq`, a bare ambient Σ that
--            carries no `Formula`.
--        The two ambient ingredients are exactly [LJ-1.533]'s uncoded
--        objects, so that wall reappears INSIDE the term.
--
--   THE EXEMPLAR EXISTS AND IT IS NOT THIS CHAPTER.  `L.Absorption`
--        writes `shiftFo : S → S → S → S → Formula S 1`
--        (src/L/Absorption.lagda.md:224) in the OBJECT language and
--        exports BOTH an ambient injection `absorbs` (:635-638) and an
--        `InjCode` `shift-coded` (:611-614) from the one graph.  That is
--        the shape a coded B9 needs and `L.StageCardinal` has no term of
--        it: its `Formula` is META-syntax used as a COUNTING DOMAIN, not
--        object syntax used as a DEFINITION.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty

-- The parameters are `L.StageCardinal`'s own, copied from
-- src/L/StageCardinal.lagda.md:15-19.  The consumer instantiates them the
-- way src/L/BoundedSubset.lagda.md:1397 does.
module LJ-1-535.Probe535 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.Count {ℓ} using ( code )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-inv )
open import L.Definability {ℓ} using ( module DefOf )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
import L.StageCardinal

open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪; isEmb⟪_⟫↪ )
open InfinitySet using ( ω; sucV )

open import Cubical.Foundations.Prelude using ( toPathP; PathP; I; isProp→PathP )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.Foundations.HLevels using ( isProp× )
open import Cubical.Functions.Embedding using ( Embedding-into-isSet→isSet )
open import Cubical.Data.Sigma using ( ΣPathP )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- The delivered chapter, at this pane's parameters.  NOT rebuilt.
module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

isSet⟪⟫ : (a : S) → isSet ⟪ a ⟫
isSet⟪⟫ a = Embedding-into-isSet→isSet (⟪ a ⟫↪ , isEmb⟪ a ⟫↪) isSetS

-- `limit-step`'s two operator arguments, copied from
-- src/L/StageCardinal.lagda.md:400-401.  Naming them here is what lets
-- section 2 open `LimitStep` at the SAME instance the chapter uses.
Dop : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S
Dop δ φ = DefOf.defSet (Lset δ) φ

invop : (δ : S) (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
      → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (Dop δ φ₀ ≡ y) ∥₁
invop δ y h = 𝒟ₒ-inv (Lset δ) y h

-- =====================================================================
-- SECTION 0.  THE OBLIGATION'S TYPE.
--
--   NAMED, NOT INHABITED.  Sections 2 and 3 say exactly which half is
--   built and which half is not.
--
--   The brief left the type to me, so the type is written here in the
--   strongest form the site supports: the injection `f`, the counting
--   map `pack` that the chapter uses to compute it, a formula for every
--   member of the domain WITH the equation that ties it to `f x`, and
--   the injectivity of `pack` at a fixed stage.  Section 2 inhabits
--   EXACTLY this type under a different name.
--
--   IT IS NOT THE OBLIGATION.  The obligation adds "from which an
--   InjCode is reachable", and section 3 measures that it is not.
-- =====================================================================

StageCardUpperCodedᵀ : Type (ℓ-suc ℓ)
StageCardUpperCodedᵀ =
    (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ]
    Σ[ pk ∈ ((m : ⟪ α ⟫) → Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1 → ⟪ α ⟫) ]
      ( ((x y : ⟪ Lset α ⟫) → f x ≡ f y → x ≡ y)
      × ((x : ⟪ Lset α ⟫)
           → Σ[ m ∈ ⟪ α ⟫ ] Σ[ φ ∈ Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1 ]
               ( (Dop (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x)
               × (pk m φ ≡ f x) ))
      × ((m : ⟪ α ⟫) (φ ψ : Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1)
           → pk m φ ≡ pk m ψ → φ ≡ ψ) )

-- =====================================================================
-- SECTION 1.  D-10, AND IT RAN BEFORE ANY TERM.
--
--   The brief's premise 9 is TRUE: `stage-card-upper`
--   (src/L/StageCardinal.lagda.md:564-565) returns a bare `_↪_` and the
--   formula is not in its type.  Restated here so the starting point is
--   checkable and not quoted.
-- =====================================================================

delivered : (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
          → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
delivered = SC.Upper.stage-card-upper

-- And the chapter's own union step accepts the delivered theorem as its
-- induction hypothesis, with NOTHING added.  This is what "restate it,
-- do not rebuild it" means at this site: `Upper.branch`
-- (src/L/StageCardinal.lagda.md:534-537) is the chapter's, and the IH
-- slot is filled by `delivered` itself.
ihOf : (α : S) (δ : S) → ⟨ δ ∈ˢ α ⟩ → SC.Upper.P δ
ihOf α δ _ = SC.Upper.stage-card-upper δ

-- =====================================================================
-- SECTION 2.  W3.  THE FORMULA IS IN SCOPE AT THE SITE, AND IT COMES
-- OUT UNTRUNCATED.
--
--   The formula lives inside `class-pred`
--   (src/L/StageCardinal.lagda.md:319-323) under `∥_∥₁`.  That
--   truncation is NOT a wall: at a FIXED value `y` the witness is a
--   PROPOSITION, because `pair` is injective (`pair-inj`, :71-75) and so
--   is the count (`cnt-inj`, :291-292).  `isPropWit` is that argument,
--   and it is the same computation `h-inj` (:353-394) already runs.
--   `SC.extract` (:419-420) then spends `lem` once and hands back the
--   witness.
--
--   COST, MEASURED, NOT GUESSED: the restatement is 49 non-blank lines
--   (:175-232) and `isPropWit` is 19 of them (:196-214).  The brief
--   estimated about 55 lines for the obligation.  The whole file is 112
--   non-blank non-comment lines against an estimate of about 190.
-- =====================================================================

module Restate (α : S) (oα : IsOrd α)
               (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
  ih = SC.Upper.branch α oα α∈suc infα (ihOf α)

  module LS = SC.LimitStep α α∈suc oα infα Dop invop ih

  -- the counting map, exactly as `class-pred` packs it
  pack : (m : ⟪ α ⟫) → Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1 → ⟪ α ⟫
  pack m φ = LS.B.pair m (LS.cnt m φ)

  pack-inj : (m : ⟪ α ⟫) (φ ψ : Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1)
           → pack m φ ≡ pack m ψ → φ ≡ ψ
  pack-inj m φ ψ e =
    LS.cnt-inj m φ ψ (snd (LS.B.pair-inj m (LS.cnt m φ) m (LS.cnt m ψ) e))

  Wit : ⟪ Lset α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  Wit x y = Σ[ m ∈ ⟪ α ⟫ ] Σ[ φ ∈ LS.F m ]
              ((Dop (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x) × (pack m φ ≡ y))

  isPropWit : (x : ⟪ Lset α ⟫) (y : ⟪ α ⟫) → isProp (Wit x y)
  isPropWit x y (m₁ , φ₁ , e₁ , c₁) (m₂ , φ₂ , e₂ , c₂) =
    ΣPathP (qm , ΣPathP (qφ , isProp→PathP rest _ _))
    where
    ec : pack m₁ φ₁ ≡ pack m₂ φ₂
    ec = c₁ ∙ sym c₂
    pp : (m₁ ≡ m₂) × (LS.cnt m₁ φ₁ ≡ LS.cnt m₂ φ₂)
    pp = LS.B.pair-inj m₁ (LS.cnt m₁ φ₁) m₂ (LS.cnt m₂ φ₂) ec
    qm : m₁ ≡ m₂
    qm = fst pp
    eφ : φ₁ ≡ subst LS.F (sym qm) φ₂
    eφ = LS.cnt-inj m₁ φ₁ (subst LS.F (sym qm) φ₂)
           (snd pp ∙ sym (LS.cnt-stable m₁ m₂ (sym qm) φ₂))
    qφ : PathP (λ i → LS.F (qm i)) φ₁ φ₂
    qφ = toPathP (cong (subst LS.F qm) eφ ∙ substSubst⁻ LS.F qm φ₂)
    rest : (i : I)
         → isProp ( (Dop (⟪ α ⟫↪ (qm i)) (qφ i) ≡ ⟪ Lset α ⟫↪ x)
                  × (pack (qm i) (qφ i) ≡ y) )
    rest i = isProp× (isSetS _ _) (isSet⟪⟫ α _ _)

  -- the chapter's own selection, re-formed here so its witness is in
  -- hand.  `fst sel x` is `LS.h x` on the nose.
  sel : (x : ⟪ Lset α ⟫) → Σ[ y ∈ ⟪ α ⟫ ] _
  sel x = leastOf (SC.OrdSWO.ordSWO α oα) lem (LS.class-pred x) (LS.nonempty x)

  witness : (x : ⟪ Lset α ⟫) → Wit x (LS.h x)
  witness x = SC.extract (isPropWit x (LS.h x)) (fst (snd (sel x)))

-- THE RESTATEMENT, AND IT TYPECHECKS.  This is `StageCardUpperCodedᵀ`
-- inhabited.  It is NOT named `stage-card-upper-coded`, because the
-- obligation asks for a term "from which an InjCode is reachable" and
-- section 3 measures that this is not one.
stage-card-upper-with-formula : StageCardUpperCodedᵀ
stage-card-upper-with-formula α oα α∈suc infα =
  R.LS.h , R.pack , (R.LS.h-inj , R.witness , R.pack-inj)
  where
  module R = Restate α oα α∈suc infα

-- WHAT THE RESTATEMENT IS AND IS NOT.  Its `f` is ONE union step of the
-- chapter's own `Upper.step` over the DELIVERED theorem at the members
-- of α (`ihOf`).  It is not claimed to be judgmentally the delivered
-- `stage-card-upper α`: that would need `∈-induction` to unfold, which
-- the tree gives no lemma for and which this task did not price.
-- Nothing below rests on such an identity.

-- =====================================================================
-- SECTION 3.  AND THE FORMULA STILL DOES NOT REACH THE VALUE.
--
--   `count-bound` (src/L/StageCardinal.lagda.md:124-129) is
--
--     count-bound g (k , (ψ , (n , cs))) =
--       pair (numeral k) (pair (pair (numeral (code ψ)) (numeral n))
--                              (tuple-g g k cs))
--
--   Three ingredients.  The types below are the measurement.
-- =====================================================================

-- 3.1  THE SYNTACTIC INGREDIENT IS A NATURAL NUMBER, AND ITS DOMAIN
-- CARRIES NO PARAMETER.  `code` (src/FOL/Count.lagda.md:81) has domain
-- `Formula (⊥* {ℓ}) k`, the parameter-FREE shape.  Whatever the chapter
-- knows about the formula, what reaches the ordinal is `ℕ`.
code-domain : (k : ℕ) → Formula (⊥* {ℓ}) k → ℕ
code-domain k ψ = code ψ

-- 3.2  THE PARAMETER INGREDIENT RUNS THROUGH A BARE AMBIENT MAP.
-- `tuple-g` (src/L/StageCardinal.lagda.md:100-102) takes `g` of exactly
-- this type and no other.  There is no `Formula` in it.
TupleInputᵀ : (β : S) → Type ℓ → Type ℓ
TupleInputᵀ β K = Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y)

-- and at the recursive site that `g` is the branch injection, which is
-- the chapter's `_↪_` and nothing more.  `ih` in section 2 has exactly
-- this type: an arbitrary ambient family.
branch-is-ambient : (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                  → (m : ⟪ α ⟫) → TupleInputᵀ α ⟪ Lset (⟪ α ⟫↪ m) ⟫
branch-is-ambient α oα α∈suc infα = Restate.ih α oα α∈suc infα

-- 3.3  THE PAIRING INGREDIENT IS THE MODULE PARAMETER `sq`, AND IT
-- CARRIES NO `Formula` EITHER.  This is `sq` at one band member, retyped
-- so the absence is a type and not a sentence.
SqAtᵀ : (δ : S) → Type ℓ
SqAtᵀ δ = TupleInputᵀ δ (⟪ δ ⟫ × ⟪ δ ⟫)

sq-is-ambient : (δ : S) → ⟨ δ ∈ˢ sucV α₀ ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥) → SqAtᵀ δ
sq-is-ambient = sq

-- 3.4  SO THE BILL, STATED.  Two of `count-bound`'s three ingredients
-- are `TupleInputᵀ`, which is [LJ-1.533]'s bare `_↪_` shape
-- (src/L/Cardinal.lagda.md:47-48) at a product carrier.  [LJ-1.533]
-- proved by types that nothing codes such a thing:
-- agents/tasks/LJ-1-533/review-of-StageCountedCoded.md.  The formula
-- section 2 extracts does not change either ingredient's type, so it
-- does not lift that refutation.  THAT is why the obligation is a
-- NO-GO and not a GO with a caveat.

-- =====================================================================
-- SECTION 4.  WHAT A CODED B9 WOULD ACTUALLY NEED, NAMED FROM THE
-- TREE'S OWN EXEMPLAR.  NOT BUILT (AD12: one obligation).
--
--   `L.Absorption` builds an object-language formula FIRST and reads the
--   ambient injection off the same graph:
--     shiftFo : S → S → S → S → Formula S 1   (:224)
--     absorbs : ... → ⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫   (:635-638)
--     shift-coded : ... → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁  (:611-614)
--   ONE `ShiftGraph` module, two exports.  That is the pattern, and its
--   `S` is the L-CARRIER, not a stage's members.
--
--   `L.StageCardinal` has no term of the first shape.  Its formulas are
--   `Formula ⟪ Lset δ ⟫ 1` (a stage's members as CONSTANTS, counted) and
--   `Formula (⊥* {ℓ}) k` (parameter-free, Gödel-numbered).  Neither is a
--   `Formula S 1` or `Formula S 2` over the L-carrier, which is what
--   `hasSeparationL` (src/L/Axioms/Full.lagda.md:144-146) and
--   `hasReplacementL` (:277-280) take.
-- =====================================================================
