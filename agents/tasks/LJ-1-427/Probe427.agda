{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.427] PROBE.  Can the INTERNAL least cardinal stand where the
-- ambient one stood in [LJ-1.421]'s descent?
--
--   W3 FIRST  `delta-is-ordinal`.  IsOrd (fst δᴸ) alone, with
--              internal-nonempty as a bare module hypothesis and
--              nothing else built.  The type is well-formed.  The
--              body is a hole.  Good does not ask for ordinality
--              (src/L/Cardinal.lagda.md:239-240).  mem-ord does not
--              apply: the container is Lset β, not sucV of an ordinal
--              (contrast src/L/Cardinal.lagda.md:125-127).
--
--   TERM      `descent-from-internal`.  Not inhabited.  The two
--              induction uses that need an ordinal are the trichotomy
--              split (ord-tri, src/L/Ordinal/Linear.lagda.md:136) and
--              Init's first conjunct (src/L/Ordinal/SquareLaw.lagda.md:693).
--
--   MODULE HYPOTHESES.  internal-nonempty from [LJ-1.425]'s brief
--              (that task has not run).  coded-to-arrow from
--              [LJ-1.424]'s brief (that task has not run).  Neither
--              report exists, so neither is NO-GO.  No kappa-arrow-data,
--              no amb-to-coded, no coded-descent, no IsCardinalL.
--              No smuggled IsOrd hypothesis.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands
-- in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

module LJ-1-427.Probe427 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; module SiteBound; module InternalLeastCard )
open import L.Ordinal.SquareLaw {ℓ} lem using ( sq )
open hPropStructure 𝒮ʟ using ( S )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- =====================================================================
-- W3, FIRST.  IsOrd (fst δᴸ) alone.  internal-nonempty is the one
-- hypothesis, at [LJ-1.425]'s brief type (Good unfolded).  Nothing
-- else is built.  The body is a hole: the tree does not deliver an
-- inhabitant from this telescope.
-- =====================================================================

module W3
  (κ : S) (oκ : IsOrd (fst κ))
  (internal-nonempty :
      ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
          ∥ Σ[ F ∈ Mem (Lset (SiteBound.β κ)) ]
              InjCode (SiteBound.up κ F) κ (SiteBound.up κ δ) ∥₁ ∥₁)
  where

  nonempty : ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
                 ⟨ InternalLeastCard.Good κ oκ δ ⟩ ∥₁
  nonempty = internal-nonempty

  delta-is-ordinal :
      IsOrd (fst (InternalLeastCard.Selected.δᴸ κ oκ nonempty))
  delta-is-ordinal = {!!}

-- =====================================================================
-- THE OBLIGATION.  Same type as [LJ-1.421]'s descent-from-data.
-- Not inhabited.  The W3 hole is the obstruction.  coded-to-arrow
-- and internal-nonempty sit as module parameters at the types their
-- briefs name.  The telescope does not hold kappa-arrow-data,
-- amb-to-coded, coded-descent or IsCardinalL.
-- =====================================================================

module _
  (coded-to-arrow :
      (a b : S)
    → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
          InjCode (SiteBound.up a F) a b ∥₁
    → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫)
  (internal-nonempty :
      (κ : S) (oκ : IsOrd (fst κ))
    → ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
          ∥ Σ[ F ∈ Mem (Lset (SiteBound.β κ)) ]
              InjCode (SiteBound.up κ F) κ (SiteBound.up κ δ) ∥₁ ∥₁)
  where

  descent-from-internal :
      (x : V ℓ) → IsOrd x → ⟨ ω ∈ˢ x ⟩
    → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
    → sq x
  descent-from-internal = {!!}
