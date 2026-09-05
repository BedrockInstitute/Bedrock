{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-278.BisectA34 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.Choice.Stage {ℓ} lem using ( stageBound )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The ambient injection type, as the square-law chain carries it.
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)


-- =====================================================================
-- The stage-bound device shared by the two internal faces (A3 and A4):
-- for an L-element, the ordinal β that `stageBound` returns, its
-- ordinal certificate, and the crossing `up` that lifts a member of
-- `Lset β` to an L-element.
-- =====================================================================

module SiteBound (a : S) where

  β : V ℓ
  β = stageBound (fst a) (snd a) .fst

  oβ : IsOrd β
  oβ = stageBound (fst a) (snd a) .snd .fst

  up : Mem (Lset β) → S
  up (x , m) = x , Lset→isL β oβ x m

-- =====================================================================
-- A3.  The canonical selection, β supplied by `stageBound`.
--
--   The selection `leastOf (orderAt β oβ)` over the bare graph atoms
--   (A2's `svAt`, `domAt`, `injAt`), with β and oβ PRODUCED rather than
--   assumed.  The module has no β hypothesis.
-- =====================================================================

module Canonical (a : S) (D : S) where

  open SiteBound a

  -- A2's predicate, over the graph carried by a member of the tower.
  Good : Mem (Lset β) → Ω
  Good A = ((up A ∷ D ∷ []) ⊨ svAt zero)
         ⊓ (((up A ∷ D ∷ []) ⊨ domAt zero (suc zero))
         ⊓  ((up A ∷ D ∷ []) ⊨ injAt zero))

  module _ (h : ∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁) where

    chosen : Σ[ A ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good A
    chosen = leastOf (orderAt β oβ) lem Good h

    F₀ : S
    F₀ = up (fst chosen)

    good : ⟨ Good (fst chosen) ⟩
    good = fst (snd chosen)

    sv : ⟨ (F₀ ∷ D ∷ []) ⊨ svAt zero ⟩
    sv = fst good

    dm : ⟨ (F₀ ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩
    dm = fst (snd good)

    ij : ⟨ (F₀ ∷ D ∷ []) ⊨ injAt zero ⟩
    ij = snd (snd good)

-- =====================================================================
-- A4.  The internal cardinal, and the internal least cardinal.
--
--   `InjCode` is A2's three conjuncts plus the value-in-b clause, the
--   four pieces A2's `Small` readback consumes.  `IsCardinalL` is the
--   internal cardinal: no smaller L-element admits a code.  The trophy
--   statement names both; the internal least-of selects δ by the sealed
--   `orderAt`, with the truncated L-element existential inside the
--   predicate.
-- =====================================================================

InjCode : S → S → S → Type (ℓ-suc ℓ)
InjCode F a b =
    ⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
  × ⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩
  × ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)

IsCardinalL : S → Type (ℓ-suc ℓ)
IsCardinalL κ =
  (δ : S) → ⟨ fst δ ∈ fst κ ⟩
          → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → Empty.⊥)

module InternalLeastCard (κ : S) (oκ : IsOrd (fst κ)) where

  open SiteBound κ

  Good : Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good δ = (∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁) , squash₁

  module Selected
    (nonempty : ∥ Σ[ δ ∈ Mem (Lset β) ] ⟨ Good δ ⟩ ∥₁)
    where

    least : Σ[ δ ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good δ
    least = leastOf (orderAt β oβ) lem Good nonempty

    δ-card : Mem (Lset β)
    δ-card = fst least

    -- the internal least cardinal, as an L-element
    δᴸ : S
    δᴸ = up δ-card

    -- the witness: some L-element codes ⟪κ⟫ ↪ ⟪δᴸ⟫, still truncated
    δ-inj : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ δᴸ ∥₁
    δ-inj = fst (snd least)

    -- leastness at a member of δᴸ: a smaller δ' with a code is absurd
    δ-min : (b : Mem (Lset β)) → ⟨ Good b ⟩
          → (SWO._<∙_ (orderAt β oβ) b δ-card → Empty.⊥)
    δ-min = snd (snd least)
