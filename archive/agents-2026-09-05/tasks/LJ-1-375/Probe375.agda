{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.375 probe.  DD25 adversarial review of `[LJ-1.373]`.  It lands
-- nothing.  It runs in agents/tasks/LJ-1-375/.
--
-- THE TARGET'S CENTRAL CLAIM (agents/tasks/LJ-1-373/lj-1.373-report.md
-- :29-31): `BandChoice` is an INSTANCE of `SetChoice (ℓ-suc ℓ)`,
-- "exactly and with no residue".
--
-- THIS FILE SPLITS THAT CLAIM IN TWO, because the two halves have
-- different answers.
--
-- PART 1  `BandChoice` IS the substitution instance of the choice
--         SCHEMA at the index `BandIndex` and the fiber `sq ∘ fst`.
--         BOTH directions are green and neither uses `isSet` and
--         neither uses `Lift`.  The whole distance is currying.  So the
--         SCHEMA half of the target's claim stands, and stands harder
--         than the target measured: the target measured one direction.
--
-- PART 2  That schema instance is NOT an instance of the tree's own
--         `SetChoice ℓ'` at any single `ℓ'`.  `SetChoice` is
--         HOMOGENEOUS: the index and the fibers share one level
--         (src/Base/Choice.lagda.md:54-56).  Here the index is at
--         `ℓ-suc ℓ` and the fiber `sq δ` is at `ℓ`
--         (src/L/Ordinal/SquareLaw.lagda.md:685).  MustFail375A.agda
--         feeds the tree's interface the band's own fiber family with
--         no `Lift` and is refused.  So the residue is TWO lifts, and
--         it is forced.
--
-- PART 3  THE DIRECTION.  What the target measured is
--         `SetChoice (ℓ-suc ℓ) → BandChoice`, a SUFFICIENCY.  A
--         sufficiency gives no lower bound at all.  This part measures
--         how far the two are apart at the only end that can be
--         measured cheaply: `SetChoice (ℓ-suc ℓ)` gives back the whole
--         classical parameter every L chapter already carries, by the
--         tree's own `choice→lem`.  `BandChoice` is not known to give
--         anything.
--
-- PART 4  THE CHEAPER SUFFICIENT PURCHASE, and it is the one the brief
--         predicted.  Pointwise split support of `sq δ` gives
--         `BandChoice` in one line and needs no selection over the
--         index.  By Kraus et al. Theorem 16 that is exactly the
--         weakly constant endomap condition, which is the target's
--         SECOND obstruction.  So the band does not bottom out at the
--         V-to-ZFC interface.  It bottoms out one floor lower.
--
-- DD4: this file is a review instrument.  It edits no chapter, shared
-- or otherwise, and it lands nothing.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Base.Choice using ( SetChoice; choice→lem )

module LJ-1-375.Probe375 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )

open import LJ-1-337.ProbeLJ1337A {ℓ} lem using ( Closed )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand )
open import LJ-1-368.Probe368 {ℓ} lem using ( BandChoice; LimitBandT )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- PART 1.  THE SUBSTITUTION INSTANCE, BOTH DIRECTIONS, NO LIFT.
-- =====================================================================

BandIndex : Type (ℓ-suc ℓ)
BandIndex = Σ[ δ ∈ S ] Σ[ oδ ∈ IsOrd δ ] Σ[ ω∈δ ∈ ⟨ ω ∈ˢ δ ⟩ ]
  Σ[ cl ∈ Closed δ ] Σ[ ni ∈ (Init δ → Empty.⊥) ]
  ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)

--   The band's own fiber, at its own level.  `sq : S → Type ℓ`.
RawFiber : BandIndex → Type ℓ
RawFiber i = sq (fst i)

--   The choice schema at exactly this index and this fiber.  This is
--   what "an instance of set-indexed choice" means, written out.
RawInstance : Type (ℓ-suc ℓ)
RawInstance = ((i : BandIndex) → ∥ RawFiber i ∥₁)
            → ∥ ((i : BandIndex) → RawFiber i) ∥₁

band→raw : LimitBandT → ((i : BandIndex) → ∥ RawFiber i ∥₁)
band→raw t (δ , oδ , ω∈δ , cl , ni , ih) = t δ oδ ω∈δ cl ni ih

raw→band : ((i : BandIndex) → ∥ RawFiber i ∥₁) → LimitBandT
raw→band h δ oδ ω∈δ cl ni ih = h (δ , oδ , ω∈δ , cl , ni , ih)

sel→limit : ((i : BandIndex) → RawFiber i) → LimitBand
sel→limit s δ oδ ω∈δ cl ni ih = s (δ , oδ , ω∈δ , cl , ni , ih)

limit→sel : LimitBand → ((i : BandIndex) → RawFiber i)
limit→sel lb (δ , oδ , ω∈δ , cl , ni , ih) = lb δ oδ ω∈δ cl ni ih

--   BOTH directions.  No `isSet`, no `Lift`, no mathematics.
bandchoice-from-raw : RawInstance → BandChoice
bandchoice-from-raw r t = PT.map sel→limit (r (band→raw t))

raw-from-bandchoice : BandChoice → RawInstance
raw-from-bandchoice bc h = PT.map limit→sel (bc (raw→band h))

-- =====================================================================
-- PART 3.  THE DIRECTION, PRICED AT THE ONLY MEASURABLE END.
--
--   The tree proves that its choice interface returns the classical
--   parameter (src/Base/Choice.lagda.md:285-287).  So a chapter that
--   took `SetChoice (ℓ-suc ℓ)` would no longer need its own `lem`: the
--   interface pays for it.  That is the size of the purchase the
--   target's END ONE recommends against but calls "the same cost under
--   a wider name" (lj-1.373-report.md:210-211).
-- =====================================================================

lem-from-setchoice : SetChoice (ℓ-suc ℓ) → LEM (ℓ-suc ℓ)
lem-from-setchoice = choice→lem

-- =====================================================================
-- PART 4.  THE CHEAPER SUFFICIENT PURCHASE.
--
--   Pointwise split support of the fiber, `∥ sq δ ∥₁ → sq δ`, gives
--   `BandChoice` with no selection over the index.  Kraus, Escardó,
--   Coquand and Altenkirch Theorem 16 says split support and a weakly
--   constant endomap are the SAME condition
--   (dev/literature/truncation-and-selection.md:158-160).  So the
--   condition the target files as its SECOND obstruction already
--   suffices, and the choice interface is not needed for the band.
--
--   This builds no such endomap and assumes none (C-36).  It measures
--   only which purchase is enough.
-- =====================================================================

bandchoice-from-pointwise-split : ((δ : S) → ∥ sq δ ∥₁ → sq δ) → BandChoice
bandchoice-from-pointwise-split ss t =
  PT.∣ (λ δ oδ ω∈δ cl ni ih → ss δ (t δ oδ ω∈δ cl ni ih)) ∣₁
