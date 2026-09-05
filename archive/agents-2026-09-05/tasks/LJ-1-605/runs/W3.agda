{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1-605]  W3.  THE WIDEST UNMEASURED TERM: does the tree already
-- carry a pairing on ordinals, and if so at which grain and in which
-- truncation.  TYPE ONLY, written FIRST and typechecked ALONE.
--
-- The grep ran before this file was written (report, section W3).
-- It found FOUR objects with the square shape, and this file
-- re-ascribes the three that are SUPPLIES:
--
--   ONE   `squareω`  at `src/L/InjChain.lagda.md:184-185`,
--         untruncated, at one site (ω).
--   TWO   `via-col-square` at `src/L/Ordinal/SquareLaw.lagda.md:960-961`,
--         untruncated, at every INITIAL ordinal, by `Init`-restriction.
--   THREE `sq-trunc-closed` at `src/L/SquareLawClosed.lagda.md:325-328`,
--         TRUNCATED, at the WHOLE BAND.
--
--   The fourth, `src/L/BoundedSubset.lagda.md:1388-1390`, is a module
--   PARAMETER, a consumer of a supply and not a supply.  So is
--   `sq` at `src/L/StageCardinal.lagda.md:17-19`, the obligation's
--   own target.
--
-- The re-ascribing stands on ONE conversion row, `fiber-identity`
-- below: the band fiber of `SqParam` is, fiber by fiber, the law
-- chapter's `sq`.  If that row were wrong, the three ascriptions
-- below would not line up with the obligation's type.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open import L.Constructible using ( IsOrd )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Data.Sigma using ( _×_ )

open import LJ-1-594.runs.W3 using ( SqParam )

module LJ-1-605.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀) where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )
  open InfinitySet {ℓ} using ( sucV; ω )

  open import L.Ordinal.SquareLaw {ℓ} lem
    using ( sq; Init; via-col-square )
  open import L.InjChain {ℓ} lem using ( squareω )
  open import L.SquareLawClosed {ℓ} lem α₀ oα₀ using ( sq-trunc-closed )

  -- W3.1  THE IDENTITY THE RE-ASCRIBING STANDS ON.  `SqParam α₀`, the
  --       obligation's own type, is the product over the band of the
  --       law chapter's fiber `sq δ`, and nothing else.  This is the
  --       no-coherence row of [LJ-1.604] (Probe604.agda:160-164) with
  --       the fiber named by the law chapter itself, and it is `refl`:
  --       the product carries no coherence between two sites.
  fiber-identity :
      SqParam α₀
        ≡ ((δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩
            → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ)
  fiber-identity = refl

  -- W3.2  SUPPLY ONE, UNTRUNCATED, AT ONE SITE.  `squareω` is the
  --       honest pairing at ω, built by the order route with zero
  --       arithmetic (src/L/InjChain.lagda.md:100, :184-185).
  supply-ω : sq ω
  supply-ω = squareω

  -- W3.3  SUPPLY TWO, UNTRUNCATED, AT EVERY INITIAL ORDINAL, and
  --       ONLY there.  The chapter's own prose states the
  --       restriction (src/L/Ordinal/SquareLaw.lagda.md:14-17): the
  --       via-collapse construction lands inside the ordinal at
  --       initial ordinals, and the non-initial case needs a
  --       least-of transfer the chapter does not build.
  supply-init : (δ : S) → Init δ → sq δ
  supply-init δ iδ = via-col-square δ iδ

  -- W3.4  SUPPLY THREE, AT THE WHOLE BAND, TRUNCATED.  `sq-trunc-closed`
  --       is an `∈-induction` (src/L/SquareLawClosed.lagda.md:328); it
  --       delivers, at every δ of the band with an infinitude clause,
  --       a TRUNCATED pairing.  The truncation is in the type, and no
  --       row of this file removes it.
  supply-band-truncated :
      (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → ∥ sq δ ∥₁
  supply-band-truncated δ d∈ d∉ = sq-trunc-closed δ d∈ d∉

  -- WHAT IS NOT IN THE TREE, stated here so the count is in a file
  -- and not only in the report: no supply of the band fiber
  -- UNTRUNCATED is held at any site the band leaves open.  The three
  -- rows above are the whole stock, and the third is truncated.
  -- That is the gap this brief asks about, and the probe's section 2
  -- prices what closing it would require.
