{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.384 probe.  Adversarial review of the sentence「every cheap
-- escape from the untruncation is closed」.  It lands nothing.  It runs
-- in agents/tasks/LJ-1-384/.
--
-- PART 1  THE LEG-2 REOPENING, MEASURED SHUT.  The brief asks whether
--         pointwise split support is provable here, which would reopen
--         leg 2 as a THEOREM.  This term measures that the hypothesis
--         of `bandchoice-from-pointwise-split`
--         (agents/tasks/LJ-1-375/Probe375.agda:142-144) is not a
--         cheaper target: it gives the FULL untruncation
--         `LimitBandT → LimitBand`, the exact debt `[LJ-1.332]` left
--         open, not only `BandChoice`.  So proving pointwise split
--         support IS paying the debt.  The reopening is the front door
--         under another name.
--
-- PART 2  THE THEOREM-17 DOOR, MEASURED SHUT AT THE UNIVERSAL LEVEL.
--         dev/literature/truncation-and-selection.md:161 digests Kraus
--         et al. Theorem 17 as「a MERELY weakly constant endomap is
--         enough」.  `merely-hasconst-free` measures that the merely
--         weakly constant endomap is FREE at every merely inhabited
--         type: `PT.map` of the constant map.
--         `universal-split-if-merely-suffices` then states the
--         collapse: if the digested reading were a theorem, every type
--         would have split support, and the digest's own section 2.6
--         (:214-221) records the refutation of that universal form.
--         So the line at :161 cannot weaken the band's supplier
--         obligation, and any dispatch funded on it must re-fetch the
--         paper first.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-384.Probe384 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )

open import LJ-1-337.ProbeLJ1337B {ℓ} lem using ( LimitBand )
open import LJ-1-368.Probe368 {ℓ} lem using ( LimitBandT )

open import Cubical.Foundations.Function using ( 2-Constant )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( S )

-- =====================================================================
-- PART 1.  Pointwise split support unlocks the WHOLE untruncation.
-- =====================================================================

pointwise-split-untruncates : ((δ : S) → ∥ sq δ ∥₁ → sq δ)
                            → LimitBandT → LimitBand
pointwise-split-untruncates ss t δ oδ ω∈δ cl ni ih =
  ss δ (t δ oδ ω∈δ cl ni ih)

-- =====================================================================
-- PART 2.  The merely weakly constant endomap is free, so the digested
--          Theorem 17 collapses to universal split support.
-- =====================================================================

merely-hasconst-free : {ℓ' : Level} (X : Type ℓ')
                     → ∥ X ∥₁ → ∥ Σ[ f ∈ (X → X) ] 2-Constant f ∥₁
merely-hasconst-free X = PT.map (λ x → (λ _ → x) , (λ u v → refl))

universal-split-if-merely-suffices : {ℓ' : Level}
  → ((X : Type ℓ') → ∥ Σ[ f ∈ (X → X) ] 2-Constant f ∥₁ → ∥ X ∥₁ → X)
  → ((X : Type ℓ') → ∥ X ∥₁ → X)
universal-split-if-merely-suffices h X t =
  h X (merely-hasconst-free X t) t
