{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.643]  DOES ANYTHING IN THE TREE PRODUCE AMBIENT CARDINALITY?
--
-- THE OBLIGATION.  `amb-card-supply`, section 1: the census of every term in
-- src/ whose conclusion is `IsCardinal κ` at some site, each row naming what
-- its producer consumes, and the alternate branch recording that the
-- predicate has no producer.
--
-- THE CENSUS IT SELLS: THREE PRODUCERS, all in src/L/CardinalAbove.lagda.md.
--   θ-card            src/L/CardinalAbove.lagda.md:160
--   cardAboveAt       src/L/CardinalAbove.lagda.md:207
--   ambientCardAbove  src/L/CardinalAbove.lagda.md:220
--   plus the tree's own `NoInjOrd` supplier, noInjOrd
--   (src/L/CardinalAbove.lagda.md:575), which is the truncated producer's
--   only external hypothesis and IS discharged in the tree.
--
-- TWO MEASUREMENTS SHAPED THIS FILE (2026-08-23 ruling: a heap wall is a
-- signal to restructure in the same dispatch).
--   1. This Agda build takes a `module M` imported through a `using` list
--      at module-BINDING position (`module T = Sep a β oβ`, runs/t1-2.out)
--      but refuses the `M args .item` sugar in type position
--      (runs/t1-1.out: NotInScope).  The `sep-site` helper names the
--      separation site as a value instead.
--   2. A `record` FIELD whose type concludes `IsCardinal` exhausts the 2 GB
--      wide-tier heap at 22 s in this build (runs/t6-1.out and
--      runs/t10-1.out: the minimal shape is one field `f : (β : SV.S) →
--      IsCardinal β`), while the same type at top level and as a product
--      factor does not (runs/t3-1.out, runs/t12-1.out).  The census is a
--      PRODUCT of the three row types, not a record.
--
-- THIS SURVEYS a supply.  It builds no cardinality: nothing in this file
-- concludes `IsCardinal` at a named site.  Nothing lands in src/.  No
-- postulate, no hole in the final file.
--
-- CALIBER.  The program set GHCRTS on this pane; I did not set it.
-- One Agda process at a time.  The floor was measured with a hole (runs/
-- floor) before the bodies landed, per the 2026-08-23 ruling.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-643.Probe643
  {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import L.CardinalAbove {ℓ} lem
  using ( NoInjOrd; cardAboveAt; ambientCardAbove; noInjOrd; module Sep )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using ( Unit* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ
open SV using ( S; _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  THE OBLIGATION, `amb-card-supply`.
--
-- The census has two outcomes, and the term takes a position in it:
-- either the tree has NO term whose conclusion is `IsCardinal κ`, or it
-- has the three producers, each row's TYPE being what that producer
-- consumes and its body being the producer itself, imported from src/.
--
-- THE NONE BRANCH IS BARE `Unit*`, and that is the honest form.  "The
-- tree has no producer" is a fact about the tree, not a mathematical
-- statement: no type can say "no source file contains a term of this
-- shape" without naming the files, and the mathematical cousin
-- (`∀ κ → IsCardinal κ → ⊥`) is FALSE, since the tree does contain
-- producers.  The branch records that the census ran and found nothing;
-- nothing more can be checked inside the language.
-- =====================================================================

CensusEmpty : Type
CensusEmpty = Unit*

-- THE SEPARATION SITE, NAMED APART.  `θ` inside `module Sep` is the
-- separation of β at the members that inject into a; this helper names
-- it as a value so that the row's type can say what the producer
-- consumes (measurement 1 above).
sep-site : (a β : SV.S) → (oβ : IsOrd β) → SV.S
sep-site a β oβ = T.θ
  where
  module T = Sep a β oβ

-- ROW 1.  src/L/CardinalAbove.lagda.md:160.  It consumes a bound ordinal β
-- and a witness that the separation site θ IS IN β; it produces
-- `IsCardinal θ` at the site θ that `module Sep` itself built (the
-- members of β that inject into a).  It says nothing about a site handed
-- in from outside.
Row1 : Type (ℓ-suc ℓ)
Row1 =
    ( a β : SV.S ) → (oβ : IsOrd β)
  → (θ∈β : ⟨ sep-site a β oβ ∈ˢ β ⟩)
  → IsCardinal (sep-site a β oβ)

-- ROW 2.  src/L/CardinalAbove.lagda.md:207.  It consumes an ordinal a and
-- ONE ordinal γ that does not inject into it; it produces a CHOSEN site
-- θ above a together with its `IsCardinal θ`, untruncated, in a Σ.
Row2 : Type (ℓ-suc ℓ)
Row2 =
    ( a : SV.S ) → (oa : IsOrd a)
  → Σ[ γ ∈ SV.S ] (IsOrd γ × (⟪ γ ⟫ ↪ ⟪ a ⟫ → Empty.⊥))
  → Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩)

-- ROW 3.  src/L/CardinalAbove.lagda.md:220.  It consumes the Hartogs fact
-- `NoInjOrd`, which the tree itself supplies (`noInjOrd`,
-- src/L/CardinalAbove.lagda.md:575), and an ordinal a; it produces the
-- same witnessed site, truncated.
Row3 : Type (ℓ-suc ℓ)
Row3 =
    NoInjOrd
  → ( a : SV.S ) → (oa : IsOrd a)
  → ∥ Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁

ProducerCensus : Type (ℓ-suc ℓ)
ProducerCensus = Row1 × Row2 × Row3

amb-card-supply : CensusEmpty ⊎ ProducerCensus
amb-card-supply = inr
  ( proj-θ-card , cardAboveAt , ambientCardAbove )
  where
  -- The import hands in the producer closed under its module parameters;
  -- this projection opens them so that the row's type names exactly what
  -- the producer consumes.
  proj-θ-card : Row1
  proj-θ-card a β oβ θ∈β = T.θ-card θ∈β
    where
    module T = Sep a β oβ

-- =====================================================================
-- SECTION 2.  W3: THE TRUNCATED PRODUCER, AT THE BILL'S SITE.
--
-- The bill's site is `[LJ-1.640]`'s: κ : SL.S with `IsOrd (fst κ)`, and
-- the owed input is `IsCardinal (fst κ)` (agents/tasks/LJ-1-640/
-- Probe640.agda:182).  Row 3's hypotheses are ALL dischargeable at that
-- site: `noInjOrd` comes from the tree (src/L/CardinalAbove.lagda.md:575,
-- below the Hartogs module), and a = fst κ with its ordinality is the
-- bill's own hypothesis.  So the row runs cold.
--
-- What it YIELDS is the point: a TRUNCATED Σ at a site θ the producer
-- CHOSES, above fst κ.  None of the three rows produces `IsCardinal` at
-- the site the bill names, untruncated.  The remaining crossing, from
-- the fresh site θ to the named site fst κ, is not in the tree.
-- =====================================================================

bill-site-truncated-supply :
    (κ : SL.S) → (oκ : IsOrd (fst κ))
  → ∥ Σ[ θ ∈ SV.S ] (IsOrd θ × IsCardinal θ × ⟨ fst κ ∈ˢ θ ⟩) ∥₁
bill-site-truncated-supply κ oκ = ambientCardAbove noInjOrd (fst κ) oκ
