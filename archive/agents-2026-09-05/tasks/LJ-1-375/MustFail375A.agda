{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.375 negative control A.  It MUST NOT typecheck.  It lands
-- nothing.  It runs in agents/tasks/LJ-1-375/.
--
-- WHAT IT MEASURES.  `[LJ-1.373]` says `BandChoice` is an instance of
-- `SetChoice (ℓ-suc ℓ)` "exactly and with no residue"
-- (lj-1.373-report.md:29-31).  Its own Agda pays a residue: the fiber
-- family is `Lift (sq (fst i))` and not `sq (fst i)`
-- (Probe373.agda:107).  This file removes ONLY the `Lift` and feeds
-- the tree's interface the band's own fiber family.  Agda must refuse,
-- because `SetChoice` is HOMOGENEOUS: `X : Type ℓ'` and
-- `B : X → Type ℓ'` share one level (src/Base/Choice.lagda.md:54-56),
-- while the band has its index at `ℓ-suc ℓ` and its fiber `sq δ` at
-- `ℓ` (src/L/Ordinal/SquareLaw.lagda.md:685).
--
-- So the residue is not a spelling choice.  It is forced by the shape
-- of the interface, and "no residue" is false as written.
--
-- WHAT IT DOES NOT MEASURE (C-36).  The refusal says nothing about
-- strength.  `Lift A ≃ A`, so the lifted instance and the raw instance
-- are inter-derivable.  What it measures is that the tree's interface
-- cannot be applied to this band without the lift.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Base.Choice using ( SetChoice )

module LJ-1-375.MustFail375A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )

open import LJ-1-337.ProbeLJ1337A {ℓ} lem using ( Closed; isPropClosed )
open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand )
open import LJ-1-368.Probe368 {ℓ} lem using ( BandChoice; LimitBandT; sq-set )

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Foundations.HLevels using ( isSetΣ; isSetΠ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_; isSetS )

BandIndex : Type (ℓ-suc ℓ)
BandIndex = Σ[ δ ∈ S ] Σ[ oδ ∈ IsOrd δ ] Σ[ ω∈δ ∈ ⟨ ω ∈ˢ δ ⟩ ]
  Σ[ cl ∈ Closed δ ] Σ[ ni ∈ (Init δ → Empty.⊥) ]
  ((β : S) → ⟨ β ∈ˢ δ ⟩ → IsOrd β → ⟨ ω ∈ˢ β ⟩ → sq β)

band-index-set : isSet BandIndex
band-index-set =
  isSetΣ isSetS
    (λ δ → isSetΣ (isProp→isSet (isPropIsOrd δ))
      (λ _ → isSetΣ (isProp→isSet (snd (ω ∈ˢ δ)))
        (λ _ → isSetΣ (isProp→isSet (isPropClosed δ))
          (λ _ → isSetΣ (isProp→isSet (isPropΠ (λ _ → Empty.isProp⊥)))
            (λ _ → isSetΠ (λ β → isSetΠ (λ _ → isSetΠ (λ _ →
              isSetΠ (λ _ → sq-set β)))))))))

--   THE ONE CHANGE.  Probe373.agda:107 writes `Lift (sq (fst i))`.
--   This writes the band's own fiber.
RawFiber : BandIndex → Type ℓ
RawFiber i = sq (fst i)

band-inh : (t : LimitBandT) → (i : BandIndex) → ∥ RawFiber i ∥₁
band-inh t (δ , oδ , ω∈δ , cl , ni , ih) = t δ oδ ω∈δ cl ni ih

band-sel : ((i : BandIndex) → RawFiber i) → LimitBand
band-sel s δ oδ ω∈δ cl ni ih = s (δ , oδ , ω∈δ , cl , ni , ih)

-- THE REFUSAL SITE.  The interface cannot accept a fiber family one
-- level below its index.
bandchoice-no-lift : SetChoice (ℓ-suc ℓ) → BandChoice
bandchoice-no-lift sc t =
  PT.map band-sel (sc BandIndex band-index-set RawFiber (band-inh t))
