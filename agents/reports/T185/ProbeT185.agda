{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T185] Statement-shape probe: below-lim as an induction over
-- limit ordinals.  T182 returned RED and named ONE ungated escape: the
-- theorem as an induction over limit ordinals, so at a general limit
-- the fact at every SMALLER limit is the induction hypothesis, exactly
-- what the top pair asks for.  This probe measures whether the shape
-- closes.  It does NOT prove the carried-sequence content again: the
-- STEP (given the fact at every limit below γ, the construction lands
-- Sset γ) is a module parameter, the content T159 built at the first
-- limit and T182 built up to the wall.  The probe proves the assembly:
-- the well-founded-induction frame, the top-pair discharge from the
-- induction hypothesis, and the compatibility with the Bridge's
-- delivered BelowLim residue.  Untracked probe, no git, no master.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeT185 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( ∅-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω; +ω-limit; +ω-mem; +ω-ord )
open import L.Rud.Step {ℓ} lem ∅ using ( Sset; limit-succ-mem )
open import L.Rud.Ops {ℓ} using ( F0 )
open import L.Rud.Bridge {ℓ} lem ∅ using ( BelowLim )
open import L.TowerKit {ℓ} lem ∅ using ( Lpair )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- ---------------------------------------------------------------------------
-- The T182 configuration: the first three OrdBlocks limits.  a0 is the
-- first limit (+ω ∅, the first instance's index), b0 = +ω a0 is the
-- second limit (T182's second-instance carrier index), b1 = +ω b0 is
-- the third limit (the carrier one level up).  T182's wall sits at
-- (carrier b1, pair at b0): Sset b0 ∈ Lset (sucV b0).
-- ---------------------------------------------------------------------------

a₀ : S
a₀ = +ω ∅

a₀-ord : IsOrd a₀
a₀-ord = +ω-ord ∅ ∅-ord

a₀-lim : ⟨ isLimit a₀ ⟩
a₀-lim = +ω-limit ∅ ∅-ord

β₀ : S
β₀ = +ω a₀

β₀-ord : IsOrd β₀
β₀-ord = +ω-ord a₀ a₀-ord

β₀-lim : ⟨ isLimit β₀ ⟩
β₀-lim = +ω-limit a₀ a₀-ord

β₁ : S
β₁ = +ω β₀

β₁-ord : IsOrd β₁
β₁-ord = +ω-ord β₀ β₀-ord

β₁-lim : ⟨ isLimit β₁ ⟩
β₁-lim = +ω-limit β₀ β₀-ord

β₀∈β₁ : ⟨ β₀ ∈ˢ β₁ ⟩
β₀∈β₁ = +ω-mem β₀

-- ---------------------------------------------------------------------------
-- The assembly.  The STEP is a module parameter (the Bridge's Reduce
-- pattern: below-lim is a Reduce parameter at
-- src/L/Rud/Bridge.lagda.md:1040).  Reason: this probe measures the
-- INDUCTION ASSEMBLY only; the step is the carried-sequence content
-- T159 built at the first limit and T182 built up to the wall, assumed
-- per the brief.
-- ---------------------------------------------------------------------------

module Assembly
  (stepHyp : (γ : S) → ⟨ isLimit γ ⟩
           → ((β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩)
           → ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩)
  where

  -- The theorem, assembled by the delivered well-founded induction on
  -- membership: V.Hierarchy's ∈-induction (src/V/Hierarchy.lagda.md:177),
  -- the same principle L.Ordinal.Stages uses for ord∈Lset-suc
  -- (src/L/Ordinal/Stages.lagda.md:435).  At a general limit γ the fact
  -- at every SMALLER limit is the induction hypothesis; the STEP lands
  -- Sset γ.
  below-lim : (γ : S) → ⟨ isLimit γ ⟩ → ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩
  below-lim = ∈-induction {P = P} step
    where
    P : S → Type (ℓ-suc ℓ)
    P γ = ⟨ isLimit γ ⟩ → ⟨ Sset γ ∈ˢ Lset (sucV γ) ⟩

    step : (γ : S) → ((β : S) → β ∈ᵗ γ → P β) → P γ
    step γ IH limγ = stepHyp γ limγ ih
      where
      ih : (β : S) → β ∈ᵗ γ → ⟨ isLimit β ⟩ → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩
      ih β β∈γ limβ = IH β β∈γ limβ

      -- The top-pair discharge FROM THE INDUCTION HYPOTHESIS, at a
      -- general limit: for any smaller limit β, the wall T182 hit at
      -- (γ = β₁, β = β₀) is IH at β.  This is the whole question of
      -- the brief; the wall is not separate content.
      wall : (β : S) → ⟨ isLimit β ⟩ → β ∈ᵗ γ
           → ⟨ Sset β ∈ˢ Lset (sucV β) ⟩
      wall β limβ β∈γ = IH β β∈γ limβ

      -- The top pair's pair frame at a smaller limit, placed one stage
      -- above the components: the first component by the ordinal step
      -- (ord∈Lset-suc, delivered), the second by the induction
      -- hypothesis.  The Kuratowski coding of pr (T159's pr≡F0,
      -- src/ProbeT159.agda:553-554) is the measured T126/T127 block;
      -- the frame is the piece T182's top-pair block was blocked from
      -- completing (src/ProbeT182.agda:364-398).
      topPair : (β : S) → ⟨ isLimit β ⟩ → β ∈ᵗ γ
              → ⟨ F0 β (Sset β) ∈ˢ Lset (sucV (sucV β)) ⟩
      topPair β limβ β∈γ = Lpair (sucV β) β (Sset β)
        (ord∈Lset-suc β (isLimit-ord β limβ)) (IH β β∈γ limβ)

  -- The first limit: T159's measured landing (via the identification
  -- Ssetω≡Lsetω at a₀ = ω, src/ProbeBelowLim.agda:282).  Under the
  -- induction shape it is the STEP at a₀, whose hypothesis has no
  -- smaller-limit facts to consume (no limit lies below a₀).
  wall₁ : ⟨ Sset a₀ ∈ˢ Lset (sucV a₀) ⟩
  wall₁ = below-lim a₀ a₀-lim

  -- The T182 wall at the second limit pair: the top pair
  -- T' = pr β₀ (Sset β₀) needs Sset β₀ ∈ Lset (sucV β₀)
  -- (src/ProbeT182.agda:364-398).  Under the induction shape this is
  -- below-lim AT THE PREVIOUS LIMIT β₀, the induction hypothesis at
  -- β₀ when the assembly sits at β₁.  The 269-350 term T182 priced for
  -- this discharge collapses into the frame.
  wall₂ : ⟨ Sset β₀ ∈ˢ Lset (sucV β₀) ⟩
  wall₂ = below-lim β₀ β₀-lim

  -- The pair frame at the second limit pair, the placement T182's
  -- top-pair block could not complete.
  topPair₂ : ⟨ F0 β₀ (Sset β₀) ∈ˢ Lset (sucV (sucV β₀)) ⟩
  topPair₂ = Lpair (sucV β₀) β₀ (Sset β₀) β₀∈Lsucβ₀ wall₂
    where
    β₀∈Lsucβ₀ : ⟨ β₀ ∈ˢ Lset (sucV β₀) ⟩
    β₀∈Lsucβ₀ = ord∈Lset-suc β₀ β₀-ord

  -- The Bridge's delivered residue statement, DERIVED from the induction
  -- shape: at a limit γ, a smaller limit β's S-level lands in Lset γ by
  -- the induction theorem at β plus the delivered successor closure and
  -- Lset monotonicity.  So the new shape SUPPLIES the Bridge's Reduce
  -- parameter (src/L/Rud/Bridge.lagda.md:1040); the consumer's
  -- interface needs no separate general-limit theorem.
  below-lim-old : BelowLim
  below-lim-old γ limγ β ordβ limβ β∈γ =
    Lset-mono {α = γ} {β = sucV β} (limit-succ-mem γ β limγ β∈γ)
      (below-lim β limβ)
