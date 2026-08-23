{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.577]  The V = L residue, read out of Devlin and taken off the
-- hypothesis.
--
-- SECTION 1 is W3 and the brief ordered it written FIRST and
-- typechecked ALONE.  runs/w3-1.out is that run, GREEN.
-- SECTION 2 restates the telescope with the internal reading, and
-- measures that the hull leg reads NO cardinality hypothesis at all.
-- SECTION 3 is the obligation.
-- SECTION 4 compares the residue with [LJ-1.569]'s.
-- SECTION 5 names the step, as a term.
--
-- THE OBLIGATION `bounded-subset-internal` IS NOT HERE.  It is a NO-GO
-- and agents/tasks/LJ-1-577/review-of-bounded-subset-internal.md states
-- it.  `BoundedSubsetInternal` is its TYPE, written out in SECTION 3,
-- and `internal-plus-one-code` is the nearest term that exists: the
-- same conclusion from the internal reading PLUS one named residue.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-577.Probe577 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans )
open import L.Cardinal {ℓ} lem using ( IsCardinalL )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.BoundedSubset {ℓ} lem
  using ( IsCardinal; _↪_; module Devlin55; module UnionKit; module HullStage )
open import L.GCH {ℓ} lem using ( InjL )
open import L.CantorBernstein {ℓ} lem using ( readL )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

-- =====================================================================
-- SECTION 1.  W3.  THE CARDINALITY PARAMETER, RE-ASCRIBED.  TYPE ONLY.
--
--   The widest unmeasured term the brief names.  The question it
--   settles: does the module even FORM with the internal reading.
-- =====================================================================

-- The parameter as the tree states it, at src/L/BoundedSubset.lagda.md:1386.
CardHypAmbient : SV.S → Type (ℓ-suc ℓ)
CardHypAmbient κ = IsCardinal κ

-- The same parameter, re-ascribed.  `IsCardinalL` is stated at the
-- L-CARRIER (src/L/Cardinal.lagda.md:230) and `IsCardinal` at the
-- AMBIENT one (src/L/BoundedSubset.lagda.md:1046).  So the re-ascription
-- is NOT a swap of one identifier for another: the two predicates do not
-- share a domain, and the ordinal must carry level-hood first.
CardHypInternal : SL.S → Type (ℓ-suc ℓ)
CardHypInternal κ = IsCardinalL κ

-- THE ANSWER, AND IT IS A TYPE.  BoundedSubsetAt's first four
-- parameters, re-ascribed: the ordinal becomes an L-element and the
-- cardinality hypothesis becomes internal at that L-element.  Every
-- later parameter of the module reads the ordinal through `fst`.
ReAscribedHead : Type (ℓ-suc (ℓ-suc ℓ))
ReAscribedHead =
    (κᴸ : SL.S) → IsOrd (fst κᴸ) → CardHypInternal κᴸ
  → (⟨ fst κᴸ ∈ˢ ω ⟩ → Empty.⊥)
  → Type (ℓ-suc ℓ)

-- =====================================================================
-- SECTION 2.  THE TELESCOPE, WITH THE INTERNAL READING.
--
--   `SqLaw` is [LJ-1.550]'s (Probe550.agda:82-88), copied letter for
--   letter.  The telescope below is `Devlin55.BoundedSubsetAt`'s
--   (src/L/BoundedSubset.lagda.md:1385-1394) with the head re-ascribed
--   as SECTION 1 measured it, and NOTHING ELSE changed.
--
--   THE HULL LEG IS BUILT FROM THE TOP-LEVEL MODULES AND FROM NO
--   CARDINALITY HYPOTHESIS OF EITHER READING.  `UnionKit`
--   (src/L/BoundedSubset.lagda.md:1145) and `HullStage` (:903) take no
--   such parameter, so `levelIn` and `cover` can be stated without one.
--   `hull-is-hypothesis-free` and `levelIn-is-hypothesis-free` are the
--   elaborator's word for that, and not a grep's.
-- =====================================================================

SqLaw : SV.S → Type (ℓ-suc ℓ)
SqLaw α =
    (δ : SV.S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
  → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
      ((u v : ⟪ δ ⟫ × ⟪ δ ⟫) → f u ≡ f v → u ≡ v)

module TeleI
  (κᴸ : SL.S) (ordκ : IsOrd (fst κᴸ)) (cardκᴸ : IsCardinalL κᴸ)
  (κ∉ω : ⟨ fst κᴸ ∈ˢ ω ⟩ → Empty.⊥)
  (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ fst κᴸ ⟩)
  (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (sq : SqLaw α)
  (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
  (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
  (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  where

  module UK = UnionKit α lam x ordα ordλ α∈λ x⊆Lα x∈Lλ α∉ω
  module HS = HullStage lam ordλ succλ UK.X UK.X⊆Lλ UK.∅∈λ

  LevelIn : Type (ℓ-suc ℓ)
  LevelIn = (δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩

  Cover : Type (ℓ-suc ℓ)
  Cover = (y : SV.S) → ⟨ y ∈ˢ HS.M ⟩
        → ∥ Σ[ γ ∈ SV.S ]
             ( IsOrd γ × ⟨ γ ∈ˢ HS.C.πX ⟩ × ⟨ HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁

  -- THE CONCLUSION, unchanged: `Devlin55.BoundedSubsetAt.Co.theorem`
  -- (src/L/BoundedSubset.lagda.md:1621).  Nothing is weakened.
  At : Type (ℓ-suc ℓ)
  At = LevelIn → Cover → ⟨ x ∈ˢ Lset (fst κᴸ) ⟩

  -- The tree's own module, at a HYPOTHETICAL ambient hypothesis.  No
  -- ambient cardinal is claimed to exist: `c` is bound here and the
  -- section's terms are all Π over it.
  module WithAmbient (c : IsCardinal (fst κᴸ)) where

    module BSA = Devlin55.BoundedSubsetAt
      (fst κᴸ) ordκ c κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ

    hull-is-hypothesis-free : BSA.HS.M ≡ HS.M
    hull-is-hypothesis-free = refl

    collapse-is-hypothesis-free : BSA.HS.C.πX ≡ HS.C.πX
    collapse-is-hypothesis-free = refl

    -- The two `Co` parameters, at the tree's own spelling
    -- (src/L/BoundedSubset.lagda.md:1555-1558), are THIS section's
    -- types on the nose.
    levelIn-is-hypothesis-free :
      ((δ : SV.S) → IsOrd δ → ⟨ δ ∈ˢ BSA.HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ BSA.HS.C.πX ⟩)
      ≡ LevelIn
    levelIn-is-hypothesis-free = refl

    cover-is-hypothesis-free :
      ((y : SV.S) → ⟨ y ∈ˢ BSA.HS.M ⟩
        → ∥ Σ[ γ ∈ SV.S ]
             ( IsOrd γ × ⟨ γ ∈ˢ BSA.HS.C.πX ⟩
             × ⟨ BSA.HS.C.π y ∈ˢ Lset γ ⟩ ) ∥₁)
      ≡ Cover
    cover-is-hypothesis-free = refl

    at : At
    at li cv = BSA.Co.theorem li cv

    -- The step, entered.  `Co`'s two parameters are SECTION 2's types
    -- (the two `refl`s above), so the tree's own `Co` opens here.
    module CoAt (li : LevelIn) (cv : Cover) where
      module C = BSA.Co li cv

      -- THE ONE INJECTION THE STEP REFUTES.
      -- src/L/BoundedSubset.lagda.md:1582-1586.  Its two legs are the
      -- stage-cardinality lower bound at β (:1584-1585) and the inverse
      -- collapse composite `πX↪α` (:1578-1580), and `πX↪α` is
      -- `CSel.h ∘ IC.inv`: a CODE SELECTION over the hull's term
      -- algebra (:1518, :1517).  It carries no `InjCode`.
      the-injection : ⟪ C.β ⟫ ↪ ⟪ α ⟫
      the-injection = C.β↪α

      -- THE TWO CLOSED LEGS OF THE TRICHOTOMY, reproduced from
      -- src/L/BoundedSubset.lagda.md:1596-1602.  Each hands
      -- `cardκ α α∈κ` an AMBIENT injection ⟪κ⟫ ↪ ⟪α⟫ and nothing else.
      -- These two terms are the whole of what the ambient reading is
      -- spent on, and `β∈κ` (:1594) is the whole of where.
      leg-β≡κ : C.β ≡ fst κᴸ → ⟪ fst κᴸ ⟫ ↪ ⟪ α ⟫
      leg-β≡κ b≡κ = Devlin55.comp-inj
        (subst (λ A → ⟪ fst κᴸ ⟫ ↪ ⟪ A ⟫) (sym b≡κ)
          ((λ m → m) , (λ m n e → e)))
        C.β↪α

      leg-κ∈β : ⟨ fst κᴸ ∈ˢ C.β ⟩ → ⟪ fst κᴸ ⟫ ↪ ⟪ α ⟫
      leg-κ∈β κ∈β = Devlin55.comp-inj
        (Devlin55.ord-emb (fst κᴸ) C.β C.β-isOrd κ∈β) C.β↪α

  -- The ambient reading closes the telescope.  This is the tree as it
  -- stands, restated at this telescope and nothing more.
  ambient-gives-at : IsCardinal (fst κᴸ) → At
  ambient-gives-at c = WithAmbient.at c

  -- INERTNESS AT THE INJECTION IS NOT MEASURED HERE, AND THAT IS A
  -- REPORTED FAILURE AND NOT AN OMISSION.  The term
  --
  --   injection-hypothesis-free :
  --       (c d : IsCardinal (fst κᴸ)) (li : LevelIn) (cv : Cover)
  --     → WithAmbient.CoAt.the-injection c li cv
  --       ≡ WithAmbient.CoAt.the-injection d li cv
  --   injection-hypothesis-free c d li cv = refl
  --
  -- ran 3 min 58 s without converging and was killed by the agent
  -- (runs/s5-2.out, EXIT=143, NO heap exhaustion).  `refl` across a
  -- module application must unfold the injection, and the injection
  -- pulls the whole hull.  The four `refl`s above cost 9 seconds
  -- together because `HS.M` and `HS.C.πX` carry no occurrence of the
  -- hypothesis at all; the injection carries none either, but the
  -- elaborator cannot see that without unfolding it.
  --
  -- WHAT STANDS INSTEAD is the four `refl`s above plus the grep: the
  -- binder at src/L/BoundedSubset.lagda.md:1386 and exactly two
  -- spends, at :1597 and :1601, both `cardκ α α∈κ`.

-- =====================================================================
-- SECTION 3.  THE OBLIGATION'S TYPE, AND THE NEAREST TERM THAT EXISTS.
--
--   `BoundedSubsetInternal` is `Devlin55.BoundedSubsetAt`'s conclusion
--   with the cardinality hypothesis read INTERNALLY.  IT IS NOT
--   INHABITED HERE.  `internal-plus-one-code` inhabits it from ONE
--   residue, the residue is named here, and SECTION 4 prices it.
--
--   THE RESIDUE IS NOT A CARDINAL PRINCIPLE.  It is a CODING
--   principle: an ambient injection between two ordinals OF L carries
--   an `InjCode`.  That is what `Assume V = L`
--   (dev/literature/devlin-II5.md:147) hands Devlin for free, because
--   under V = L every ambient injection IS an element of L.
-- =====================================================================

-- The residue.  `InjL` is src/L/GCH.lagda.md:38, the truncated
-- `InjCode` existential over the L-carrier.
OrdInjCoded : Type (ℓ-suc ℓ)
OrdInjCoded =
    (a b : SL.S) → IsOrd (fst a) → IsOrd (fst b)
  → ⟨ fst b ∈ˢ fst a ⟩ → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ → InjL a b

-- Every member of an L-element is an L-element: `isL-trans`
-- (src/L/Constructible.lagda.md:379).  So the ambient Π of `IsCardinal`
-- over the members of an L-ordinal is a Π over L-elements, and the
-- residue converts it one member at a time.
internal→ambient :
    OrdInjCoded → (κᴸ : SL.S) → IsOrd (fst κᴸ) → IsCardinalL κᴸ
  → IsCardinal (fst κᴸ)
internal→ambient w κᴸ ordκ cκ δ δ∈κ inj =
  cκ δᴸ δ∈κ (w κᴸ δᴸ ordκ (mem-ord {A = fst κᴸ} ordκ δ δ∈κ) δ∈κ inj)
  where
  δᴸ : SL.S
  δᴸ = δ , isL-trans {x = fst κᴸ} {y = δ} δ∈κ (snd κᴸ)

-- THE OBLIGATION'S TYPE.  Every parameter is `BoundedSubsetAt`'s, in
-- `BoundedSubsetAt`'s order, with the head re-ascribed and the
-- conclusion untouched.
BoundedSubsetInternal : Type (ℓ-suc ℓ)
BoundedSubsetInternal =
    (κᴸ : SL.S) (ordκ : IsOrd (fst κᴸ)) (cardκᴸ : IsCardinalL κᴸ)
    (κ∉ω : ⟨ fst κᴸ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ fst κᴸ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → TeleI.At κᴸ ordκ cardκᴸ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ

-- NOT THE OBLIGATION AND NOT OFFERED AS ONE.  The obligation's type is
-- `BoundedSubsetInternal` with NOTHING to its left.  This term carries
-- `OrdInjCoded` to its left, and that residue is the answer this task
-- returns.
internal-plus-one-code : OrdInjCoded → BoundedSubsetInternal
internal-plus-one-code w κᴸ ordκ cardκᴸ κ∉ω α ordα α∈κ α∉ω sq
                        x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ =
  TeleI.ambient-gives-at κᴸ ordκ cardκᴸ κ∉ω α ordα α∈κ α∉ω sq
                         x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ
                         (internal→ambient w κᴸ ordκ cardκᴸ)

-- =====================================================================
-- SECTION 4.  WHAT THE RESIDUE COSTS, AGAINST [LJ-1.569]'S.
--
--   NOT AN IMPROVEMENT AND NOT OFFERED AS ONE.  `InternalToAmbient` is
--   [LJ-1.569]'s name for the route's ambient demand
--   (Probe569.agda:175-176), copied here letter for letter.  The two
--   terms below price this task's residue against it, and the price is
--   NOT LOWER: `OrdInjCoded` gives `InternalToAmbient` back at every
--   ordinal L-element, and `InternalToAmbient` closes this task's own
--   statement on its own.
--
--   SO RE-ASCRIBING THE PRINTED HYPOTHESIS BUYS NO GROUND BY ITSELF.
--   What it buys is a CHANGE OF KIND in the residue, and SECTION 5
--   measures that: the demand stops being a fact about cardinals and
--   becomes a fact about ONE injection.
-- =====================================================================

InternalToAmbient : Type (ℓ-suc ℓ)
InternalToAmbient = (μ : SL.S) → IsCardinalL μ → IsCardinal (fst μ)

-- Direction 1.  The residue gives [LJ-1.569]'s principle at every
-- ordinal L-element.  [LJ-1.569] needed it only at the successor pair
-- (Probe569.agda:187-188), so the residue is at least as strong.
residue-gives-569 :
    OrdInjCoded → (μ : SL.S) → IsOrd (fst μ) → IsCardinalL μ
  → IsCardinal (fst μ)
residue-gives-569 = internal→ambient

-- Direction 2.  [LJ-1.569]'s principle closes this task's statement
-- with no coding at all.  The internal reading is reachable from the
-- demand the campaign already had.
internal-from-569 : InternalToAmbient → BoundedSubsetInternal
internal-from-569 w κᴸ ordκ cardκᴸ κ∉ω α ordα α∈κ α∉ω sq
                                 x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ =
  TeleI.ambient-gives-at κᴸ ordκ cardκᴸ κ∉ω α ordα α∈κ α∉ω sq
                         x x⊆Lα absorbs lam ordλ α∈λ succλ x∈Lλ
                         (w κᴸ cardκᴸ)

-- =====================================================================
-- SECTION 5.  THE STEP, AND WHAT IT ACTUALLY ASKS FOR.
--
--   SECTION 2's `CoAt` already named the step as terms: `the-injection`
--   is the object both legs refute, and `leg-β≡κ` and `leg-κ∈β` are the
--   two legs, reproduced from src/L/BoundedSubset.lagda.md:1596-1602.
--   This section states what the step holds and what it wants, at the
--   ONE pair it spends at, and shows which of the two directions the
--   tree already has.
-- =====================================================================

-- What the step wants at the pair: no AMBIENT injection.
Spend : SV.S → SV.S → Type ℓ
Spend κ α = ⟪ κ ⟫ ↪ ⟪ α ⟫ → Empty.⊥

-- What the internal reading delivers at the pair: no CODED injection.
SpendInternal : SL.S → SL.S → Type (ℓ-suc ℓ)
SpendInternal a b = InjL a b → Empty.⊥

-- The ambient hypothesis, at the one argument the module applies it to.
ambient-spend : (κ α : SV.S) → IsCardinal κ → ⟨ α ∈ˢ κ ⟩ → Spend κ α
ambient-spend κ α c α∈κ = c α α∈κ

-- The internal hypothesis, at the same pair.
internal-spend :
    (κᴸ αᴸ : SL.S) → IsCardinalL κᴸ → ⟨ fst αᴸ ∈ˢ fst κᴸ ⟩
  → SpendInternal κᴸ αᴸ
internal-spend κᴸ αᴸ c α∈κ = c αᴸ α∈κ

-- THE DIRECTION THE TREE ALREADY HAS, and it is the wrong one.
-- `readL` (src/L/CantorBernstein.lagda.md:33-38) turns a code into an
-- ambient injection, so an AMBIENT refutation refutes the code too.
ambient-spend→internal-spend :
    (a b : SL.S) → Spend (fst a) (fst b) → SpendInternal a b
ambient-spend→internal-spend a b s =
  PT.rec Empty.isProp⊥ (λ code → s (readL a b code))

-- THE DIRECTION THE STEP NEEDS.  TYPE ONLY.  This file neither proves
-- it nor refutes it, and it is `OrdInjCoded` cut down to one pair.
GapAtPair : SL.S → SL.S → Type (ℓ-suc ℓ)
GapAtPair a b = SpendInternal a b → Spend (fst a) (fst b)

-- And the gap at the pair is exactly a code for the one injection the
-- step refutes.  Read the antecedent: it is `OrdInjCoded` at (a , b).
gap-is-a-code :
    (a b : SL.S) → (⟪ fst a ⟫ ↪ ⟪ fst b ⟫ → InjL a b) → GapAtPair a b
gap-is-a-code a b code s inj = s (code inj)
