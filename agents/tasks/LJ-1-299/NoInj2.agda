{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.299] PROBE.  Build `noinj²`, the FOURTH row of `Init`
-- (src/L/Ordinal/SquareLaw.lagda.md:699-702), at the use site where
-- alpha is kappa with `IsCardinalL kappa`, or measure the obstruction.
--
-- The file proves THREE things and names ONE hole:
--
--   PART 1.  The two cardinal faces relate in ONE direction: the
--   AMBIENT face `IsCardinal` (src/L/BoundedSubset.lagda.md:1047)
--   refutes the CODED face `IsCardinalL` (src/L/Cardinal.lagda.md:230),
--   by the `Small` readback.  The reverse direction is the hole.
--
--   PART 2.  The corrected target: with the square law handed over
--   uniformly and the AMBIENT cardinal, `noinj²` at kappa is proved
--   outright.  No hole.
--
--   PART 3.  The target as stated: with the square law handed over and
--   `IsCardinalL` only, `noinj²` reduces to ONE named hole, the
--   ambient-to-code bridge `AmbientToCode`.  Nothing in the tree
--   supplies it, and the report argues it is not a tree debt.
--
-- Tracked; ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-299.NoInj2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( ↪-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Cardinal {ℓ} lem using ( _↪_; IsCardinalL; InjCode )
open import L.Coding.Injection {ℓ} lem using ( module Small )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- THE TARGET, Init's fourth row verbatim at alpha = fst kappa.  The
-- carrier is SquareLaw's S, the V-carrier, so beta ranges over V.
NoInj² : (κ : S) → Type (ℓ-suc ℓ)
NoInj² κ = (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst κ ⟩ → ⟨ ω ∈ˢ β ⟩
        → (f : ⟪ fst κ ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
        → ((m n : ⟪ fst κ ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥

-- ---------------------------------------------------------------------
-- PART 0.  Two one-line devices the reduction needs.

-- An infinite member of an ordinal is outside omega: otherwise omega
-- is a member of itself, by the ordinal's own transitivity.
ω∈β→β∉ω : (β : V ℓ) → IsOrd β → ⟨ ω ∈ˢ β ⟩ → (⟨ β ∈ˢ ω ⟩ → Empty.⊥)
ω∈β→β∉ω β oβ ω∈β β∈ω = ∈-irrefl ω (ω-ord .fst ω∈β β∈ω)

-- THE SQUARE LAW, HANDED OVER.  This is `SqShape`'s INTENDED body at
-- the V-carrier (src/L/GCH.lagda.md:41-44), with the parentheses the
-- master is missing: as written there, `A × B ↪ C` parses as
-- `A × (B ↪ C)` because `_↪_` is undeclared and so binds tighter than
-- `infixr 5 _×_`.  The probe `Mini.agda` measures both facts.  Every
-- reduction below consumes the square law as a hypothesis, so each
-- result prices exactly what remains beside it.
SqAll : Type (ℓ-suc ℓ)
SqAll = (b : V ℓ) → IsOrd b → (⟨ b ∈ˢ ω ⟩ → Empty.⊥)
      → (⟪ b ⟫ × ⟪ b ⟫) ↪ ⟪ b ⟫

-- The composite: kappa into the member's square, then the square into
-- the member.  This is the whole mathematical content of the descent,
-- and it is three lines once the square law is handed over.
κ→β : (κ : S) (β : V ℓ) → IsOrd β → ⟨ ω ∈ˢ β ⟩
   → SqAll → (f : ⟪ fst κ ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
   → ((m n : ⟪ fst κ ⟫) → f m ≡ f n → m ≡ n)
   → ⟪ fst κ ⟫ ↪ ⟪ β ⟫
κ→β κ β oβ ω∈β sqh f finj = (λ m → g (f m)) , hinj
  where
  g : ⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫
  g = sqh β oβ (ω∈β→β∉ω β oβ ω∈β) .fst
  gi : (p q : ⟪ β ⟫ × ⟪ β ⟫) → g p ≡ g q → p ≡ q
  gi = sqh β oβ (ω∈β→β∉ω β oβ ω∈β) .snd
  hinj : (m n : ⟪ fst κ ⟫) → g (f m) ≡ g (f n) → m ≡ n
  hinj m n e = finj m n (gi (f m) (f n) e)

-- ---------------------------------------------------------------------
-- PART 1.  The one-way street between the cardinal faces.
--
--   `IsCardinal` (ambient, BoundedSubset:1047) implies `IsCardinalL`
--   (coded, Cardinal:230): a code reads back to an ambient injection
--   by `Small`, and the ambient face refutes that.  No bridge, no
--   separation, one readback.

amb→code : (κ : S) → IsCardinal (fst κ) → IsCardinalL κ
amb→code κ amb δ δ∈ code =
  PT.rec Empty.isProp⊥ (λ c → amb (fst δ) δ∈ (readback c)) code
  where
  readback : Σ[ F ∈ S ] InjCode F κ δ → ⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫
  readback (F , (sv , (dm , (ij , ran)))) = Sm.small , Sm.small-inj
    where
    module Sm = Small F κ δ sv dm ij ran

-- ---------------------------------------------------------------------
-- PART 2.  THE CORRECTED TARGET.
--
--   With the square law and the AMBIENT cardinal, `noinj²` at kappa is
--   proved outright.  The ambient face refutes the composite directly;
--   no coded world is entered and no bridge is crossed.

noinj²-amb : SqAll → (κ : S) → IsCardinal (fst κ) → NoInj² κ
noinj²-amb sqh κ amb β oβ β∈κ ω∈β f finj =
  amb β β∈κ (κ→β κ β oβ ω∈β sqh f finj)

-- ---------------------------------------------------------------------
-- PART 3.  THE TARGET AS STATED.
--
--   With the square law and `IsCardinalL` only, the proof closes
--   through ONE named hole: the ambient-to-code bridge.  [LJ-1.294]
--   measured by grep that no such device exists in the tree (only the
--   reverse, `Small`, exists); this file names its exact type.

AmbientToCode : Type (ℓ-suc ℓ)
AmbientToCode = (a b : S) → (⟪ fst a ⟫ ↪ ⟪ fst b ⟫)
             → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁

noinj²-code : SqAll → AmbientToCode → (κ : S) → IsCardinalL κ → NoInj² κ
noinj²-code sqh atc κ cκ β oβ β∈κ ω∈β f finj =
  cκ βᴸ β∈ (atc κ βᴸ (κ→β κ β oβ ω∈β sqh f finj))
  where
  βᴸ : S
  βᴸ = β , isL-trans β∈κ (snd κ)
  β∈ : ⟨ fst βᴸ ∈ fst κ ⟩
  β∈ = β∈κ
