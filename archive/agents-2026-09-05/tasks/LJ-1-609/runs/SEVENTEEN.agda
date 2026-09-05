{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.609]  THE SEVENTEEN, IMPORTED AND RECOVERED (W2, in code).
--
--   The brief ordered the seventeen IMPORTED and not restated.  This
--   slice imports [LJ-1.550]'s green module (which the seventeen-slot
--   delivery lives in, Probe578.agda:413-427 taking
--   P550.Tele.BSA.elem-down through P570) and shows BOTH directions at
--   today's tree:
--     * `elem-down-taken` is the seventeen's own term, taken as is;
--     * `elem-down-taken-recovered` is THIS task's six-slot term,
--       applied at the seventeen's forced carrier UK.X = Lset α ∪ ⁅x⁆s
--       (src/L/BoundedSubset.lagda.md:1150), and it lands in the
--       seventeen's own type `Tele.BSA.DR54.ElemDown` with no coercion.
--   So the mathematics is written ONCE at the generic carrier, and the
--   seventeen-slot object is an instance of it: the W2 answer, checked.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-609.runs.SEVENTEEN {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal; _↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_⁆s; ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open InfinitySet {ℓ} using ( ω; sucV )
import Cubical.Data.Empty as Empty
import LJ-1-550.Probe550 {ℓ} lem as P550
import LJ-1-609.Probe609 {ℓ} lem as P609

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- THE SEVENTEEN'S OWN TERM, TAKEN (it is
-- agents/tasks/LJ-1-578/Probe578.agda:413-427's `elem-down-taken`,
-- whose body is P550.Tele.BSA.elem-down).
elem-down-taken :
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : P550.SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → P550.Tele.BSA.DR54.ElemDown
      κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ
elem-down-taken = P550.Tele.BSA.elem-down

-- THE SAME OBJECT, RECOVERED FROM THE SIX-SLOT TERM at the forced
-- carrier.  No coercion: the elaborator reads the six-slot result at
-- UK.X as the seventeen's own type.
elem-down-taken-recovered :
    (κ : SV.S) (ordκ : IsOrd κ) (cardκ : IsCardinal κ)
    (κ∉ω : ⟨ κ ∈ˢ ω ⟩ → Empty.⊥)
    (α : SV.S) (ordα : IsOrd α) (α∈κ : ⟨ α ∈ˢ κ ⟩)
    (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
    (sq : P550.SqLaw α)
    (x : SV.S) (x⊆Lα : (z : SV.S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
    (absorbs : ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫)
    (lam : SV.S) (ordλ : IsOrd lam) (α∈λ : ⟨ α ∈ˢ lam ⟩)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
  → P550.Tele.BSA.DR54.ElemDown
      κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
      lam ordλ α∈λ succλ x∈Lλ
elem-down-taken-recovered κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
                         lam ordλ α∈λ succλ x∈Lλ =
  P609.elem-down-at lam ordλ succλ
    (P550.Tele.BSA.UK.X κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
       lam ordλ α∈λ succλ x∈Lλ)
    (P550.Tele.BSA.UK.X⊆Lλ κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
       lam ordλ α∈λ succλ x∈Lλ)
    (P550.Tele.BSA.UK.∅∈λ κ ordκ cardκ κ∉ω α ordα α∈κ α∉ω sq x x⊆Lα absorbs
       lam ordλ α∈λ succλ x∈Lλ)
