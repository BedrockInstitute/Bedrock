{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.373 probe.  It lands nothing.  It runs in agents/tasks/LJ-1-373/.
--
-- THE BRIEF ASKS: can BandChoice be proved, or must it be assumed?
-- BandChoice = LimitBandT -> ∥ LimitBand ∥₁
-- (agents/tasks/LJ-1-368/Probe368.agda:226-227), a SELECTION from a
-- truncated family.
--
-- THE ORCHESTRATOR CORRECTED THE ORDER MID-TASK: the literature survey
-- runs FIRST, and Agda is permitted only to check a condition the
-- literature names.  The literature names ONE condition this file can
-- check: the index of the selection must be a SET (HoTT Book Lemma
-- 3.8.5 as digested at dev/literature/truncation-and-selection.md:231,
-- and the `isSet X` premise of this tree's own interface
-- `SetChoice`, src/Base/Choice.lagda.md).
--
-- THIS FILE MEASURES TWO THINGS.
--
--   1. `BandChoice` IS AN INSTANCE of the tree's own boundary
--      interface `SetChoice (ℓ-suc ℓ)`, stated levelwise at
--      src/Base/Choice.lagda.md.  The derivation below feeds SetChoice
--      the band's own index telescope as the index set, so it must
--      DISCHARGE `isSet` on that telescope for real.  If the telescope
--      were spelled wrong, `band-sel` and `band-inh` would refuse
--      against `LimitBandT` and `LimitBand`: the green pins the
--      spelling.
--
--   2. `SetChoice` STAYS A PARAMETER.  Nothing here proves it, and
--      nothing here assumes it.  The interface is the tree's own, with
--      `choice→lem` proved in src/Base/Choice.lagda.md and the
--      chapter's own prose that excluded middle does not return the
--      favour.  MustFail373A.agda records what the same derivation
--      does when `LEM` stands where `SetChoice` stands.
--
-- DD4: this term is a pure WRAP.  It edits no consumer and touches no
-- supplier, shared or otherwise.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Base.Choice using ( SetChoice )

module LJ-1-373.Probe373 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

open import LJ-1-337.ProbeLJ1337A {ℓ} lem using ( Closed; isPropClosed )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand )
open import LJ-1-368.Probe368 {ℓ} lem using ( BandChoice; LimitBandT; sq-set )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Foundations.HLevels
  using ( isSetΣ; isSetΠ; isOfHLevelLift )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_; isSetS )

-- =====================================================================
-- PART 1.  THE BAND'S INDEX TELESCOPE, AS ONE SET.
--
--   `LimitBandT`'s domain is the telescope below, and `LimitBand` runs
--   over the same telescope with the truncation removed.  Spelled as
--   one Σ, it is the index of the selection.  Every component after δ
--   is a proposition except the induction hypothesis, which is a
--   family of sets, hence a set.
-- =====================================================================

BandIndex : Type (ℓ-suc ℓ)
BandIndex = Σ[ δ ∈ S ] Σ[ oδ ∈ IsOrd δ ] Σ[ ω∈δ ∈ ⟨ ω ∈ˢ δ ⟩ ]
  Σ[ cl ∈ Closed δ ] Σ[ ni ∈ (Init δ → Empty.⊥) ]
  ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)

--   Every component after δ is a proposition except the induction
--   hypothesis, a family of sets, hence a set.  `isProp→isSet` comes
--   from Base.Prelude; the prop proofs are 1337A's own exports and
--   the membership hProp's own `snd`.
band-index-set : isSet BandIndex
band-index-set =
  isSetΣ isSetS
    (λ δ → isSetΣ (isProp→isSet (isPropIsOrd δ))
      (λ _ → isSetΣ (isProp→isSet (snd (ω ∈ˢ δ)))
        (λ _ → isSetΣ (isProp→isSet (isPropClosed δ))
          (λ _ → isSetΣ (isProp→isSet (isPropΠ (λ _ → Empty.isProp⊥)))
            (λ _ → isSetΠ (λ β → isSetΠ (λ _ → isSetΠ (λ _ →
              isSetΠ (λ _ → sq-set β)))))))))

-- =====================================================================
-- PART 2.  THE FIBERS ARE SETS, AND THE INSTANCE.
--
--   The fiber at an index is `sq δ`, lifted one universe up, which is
--   what `SetChoice (ℓ-suc ℓ)` asks of its family.  `sq δ` is a set by
--   `[LJ-1.319]`, re-derived in Probe368, so the family is a family of
--   SETS and the setting is HoTT Book 3.8.1's exactly.
-- =====================================================================

BandFiber : BandIndex → Type (ℓ-suc ℓ)
BandFiber i = Lift (sq (fst i))

band-fiber-set : (i : BandIndex) → isSet (BandFiber i)
band-fiber-set i = isOfHLevelLift 2 (sq-set (fst i))

--   The truncated hypothesis, pointwise.  The pattern match against the
--   telescope pins the spelling: a wrong telescope refuses here.
band-inh : (t : LimitBandT) → (i : BandIndex) → ∥ BandFiber i ∥₁
band-inh t (δ , oδ , ω∈δ , cl , ni , ih) =
  PT.map lift (t δ oδ ω∈δ cl ni ih)

--   The section, curried back into `LimitBand`'s own shape.  A wrong
--   telescope refuses here too.
band-sel : ((i : BandIndex) → BandFiber i) → LimitBand
band-sel s δ oδ ω∈δ cl ni ih =
  lower (s (δ , oδ , ω∈δ , cl , ni , ih))

-- =====================================================================
-- PART 3.  THE MEASUREMENT.
--
--   `BandChoice` is an instance of `SetChoice (ℓ-suc ℓ)`.  The price of
--   the instance is one `isSet` proof on the index, paid above, and the
--   lifts.  `SetChoice` remains a PARAMETER: the tree never assumes it
--   (src/Base/Choice.lagda.md), and the owner has ruled it may not be
--   assumed for this band either.  What this green measures is that NO
--   OTHER mathematical content separates the band from the interface:
--   the whole distance is the selection itself.
-- =====================================================================

bandchoice-from-setchoice : SetChoice (ℓ-suc ℓ) → BandChoice
bandchoice-from-setchoice sc t =
  PT.map band-sel (sc BandIndex band-index-set BandFiber (band-inh t))

-- =====================================================================
-- PART 4.  THE NEGATIVE CONTROL, AND WHAT IT MEASURED.
--
--   MustFail373A.agda holds THIS body with `LEM (ℓ-suc ℓ)` standing
--   where `SetChoice (ℓ-suc ℓ)` stands.  MEASURED, exit 42:
--
--     error: [UnequalTerms]
--     (Type (ℓ-suc ℓ)) !=<
--     (Σ (Type (ℓ-suc ℓ)) (Cubical.Foundations.HLevels.isOfHLevel 1))
--     when checking that the expression BandIndex has type
--     hProp (ℓ-suc ℓ)
--
--   The classical principle cannot even ACCEPT the index.  Its first
--   argument must be a proposition, and the band's index is a set of
--   data.  So the green above consumes the selection structure of
--   SetChoice and nothing that LEM's type offers (C-36: this refusal
--   measures this derivation, and no other).
-- =====================================================================
