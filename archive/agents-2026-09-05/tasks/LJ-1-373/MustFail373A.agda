{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.373 negative control A.  It MUST NOT typecheck.  It lands
-- nothing.  It runs in agents/tasks/LJ-1-373/.
--
-- THE CONTROL.  Probe373.agda's green body consumes exactly the
-- selection structure of `SetChoice (ℓ-suc ℓ)`.  This file feeds the
-- SAME body the SAME index, fibers and hypothesis, with `LEM
-- (ℓ-suc ℓ)` standing where `SetChoice (ℓ-suc ℓ)` stands.  Agda must
-- refuse, and the refusal must name the first argument: `BandIndex`
-- is a type and not a proposition, and LEM offers no product
-- selection at all.
--
-- WHAT IT MEASURES.  At this derivation shape, the classical boundary
-- the tree already spends cannot stand in for the selection.  This is
-- the term-level half of the brief's part 2.
--
-- WHAT IT DOES NOT MEASURE (C-36).  The refusal of MY body measures no
-- non-provability.  It measures that the green derivation's content
-- is the selection, and nothing in `LEM`'s type elaborates in its
-- place.  The non-provability claim rests on the literature and on
-- the tree's own boundary prose, not on this exit code.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-373.MustFail373A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd; 𝒮ʟ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq; Init )

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

BandFiber : BandIndex → Type (ℓ-suc ℓ)
BandFiber i = Lift (sq (fst i))

band-inh : (t : LimitBandT) → (i : BandIndex) → ∥ BandFiber i ∥₁
band-inh t (δ , oδ , ω∈δ , cl , ni , ih) =
  PT.map lift (t δ oδ ω∈δ cl ni ih)

band-sel : ((i : BandIndex) → BandFiber i) → LimitBand
band-sel s δ oδ ω∈δ cl ni ih =
  lower (s (δ , oδ , ω∈δ , cl , ni , ih))

-- THE REFUSAL SITE.  Everything above is Probe373.agda's own and is
-- green there.  Only the classical principle stands in place of the
-- selection principle.
bandchoice-from-lem : LEM (ℓ-suc ℓ) → BandChoice
bandchoice-from-lem lem′ t =
  PT.map band-sel (lem′ BandIndex band-index-set BandFiber (band-inh t))
