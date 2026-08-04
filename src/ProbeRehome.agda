{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T3] The choice re-home probe (gate 5).
--
-- With the bridge standing, `hasChoice` on L should flow from the DELIVERED
-- J-side well-order (`Jset-order`, Rud/Order:1026-1028) instead of the
-- 6,046-line L/Choice tree.  This probe builds the smallest honest version of
-- the transversal-shaped choice function over `Jset-order`: the pick and its
-- two obligations, with the bridge's isL-to-isJ step as a MODULE HYPOTHESIS
-- (the bridge is not built yet; that is the honest form).
--
-- Hypothesis consumed (exactly one, at the family):
--   bridgeL→J : (x : V ℓ) → ⟨ isL x ⟩
--             → ∥ Σ[ γ ∈ V ℓ ] Σ[ limγ ∈ ⟨ isLimit γ ⟩ ] ⟨ x ∈ Jset γ limγ ⟩ ∥₁
-- (the ambient `_∈_`; `∈ˢ` on `𝒮ᵥ` is this, Hierarchy:83).  This is the
-- class-level isL→isJ corollary of the delivered `Reduce.p2` clause
-- (`Lset β ∈ˢ Sset γ` for β ∈ γ, γ limit, Bridge:752) pushed by +ω
-- (`+ω-limit`/`+ω-mem`, OrdBlocks) and read through `Sset-trans`, with
-- `Jset γ _ = Sset γ` definitionally (Hierarchy:544-545).  It is taken as a
-- MODULE HYPOTHESIS because the bridge is not built: the current tree records
-- the limits identification `Matching` as FALSE (Devlin VI.2.4, the ω·2
-- counterexample, Bridge prose :440-468) and `Bridged` (the module that
-- derived isL→isJ from it) as RETIRED; the direction the tree delivers is the
-- reverse, `bridge-isJ→isL` (Bridge:842-843, read off `p4`).  The truncation
-- is inherent (isL and isJ are both truncated ⋁s), so the probe eliminates it
-- only into propositional targets: no honest strengthening.
--
-- Delivered exports consumed: `Jset-order` (the SWO), `Sset-trans` (one level
-- bounds the family, its cells and their members: the J-side "bound"),
-- `leastOf`/`IsLeast`/`isPropLeastOf` (the pick and its uniqueness), `lem`.
-- `Sset-choice`/`Jset-choice` are NOT enough: they hide the `IsLeast`
-- obligation, which `meetsOnce` spends (Transversal:314-341).
--
-- Line-count convention: non-blank lines inside the agda region (comments
-- included, blanks excluded), the pinned convention.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

module ProbeRehome {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; 𝒮ʟ )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.Step {ℓ} lem A using ( Jset; Sset-trans )
open import L.Rud.Order {ℓ} lem A using ( Jset-order )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( SWO; IsLeast; isPropLeastOf; leastOf )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Data.Sigma using ( Σ≡Prop )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- =====================================================================
-- The miniature: the transversal-shaped choice function over Jset-order.
-- =====================================================================

module Mini
  (bridgeL→J : (x : V ℓ) → ⟨ isL x ⟩
             → ∥ Σ[ γ ∈ V ℓ ] Σ[ limγ ∈ ⟨ isLimit γ ⟩ ] ⟨ x ∈ Jset γ limγ ⟩ ∥₁)
  where

  open hPropStructure 𝒮ᵥ

  MemAt : (γ : V ℓ) → (limγ : ⟨ isLimit γ ⟩) → Type (ℓ-suc ℓ)
  MemAt γ limγ = Σ[ m ∈ V ℓ ] ⟨ m ∈ˢ Jset γ limγ ⟩

  CellAt : (γ : V ℓ) (limγ : ⟨ isLimit γ ⟩) (x : V ℓ) → MemAt γ limγ → hProp (ℓ-suc ℓ)
  CellAt γ limγ x m = m .fst ∈ˢ x

  -- one level bounds the family, its cells and their members (transitivity)
  bound : (γ : V ℓ) → (limγ : ⟨ isLimit γ ⟩) → (x z : V ℓ)
        → ⟨ x ∈ˢ Jset γ limγ ⟩ → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Jset γ limγ ⟩
  bound γ limγ x z x∈J z∈x = Sset-trans γ z∈x x∈J

  -- the pick-level statement: existence of a choice function whose pick is a
  -- member (obligation 1) and canonical per the order (obligation 2)
  RawChoice : Type (ℓ-suc ℓ)
  RawChoice =
    (a : V ℓ) → ⟨ isL a ⟩
    → (inh : (x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ V ℓ ] ⟨ y ∈ˢ x ⟩ ∥₁)
    → ∥ Σ[ γ ∈ V ℓ ] Σ[ limγ ∈ ⟨ isLimit γ ⟩ ] Σ[ a∈J ∈ ⟨ a ∈ˢ Jset γ limγ ⟩ ]
        Σ[ ch ∈ ((x : V ℓ) → ⟨ x ∈ˢ a ⟩ → V ℓ) ]
          Σ[ pick∈ ∈ ((x : V ℓ) (h : ⟨ x ∈ˢ a ⟩) → ⟨ ch x h ∈ˢ x ⟩) ]
            ( (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩)
                → IsLeast (Jset-order γ limγ) (CellAt γ limγ x)
                    (ch x h , bound γ limγ x (ch x h) (Sset-trans γ h a∈J) (pick∈ x h)) )
    ∥₁

  -- the pick at a fixed witness (γ, limγ, a∈J): the family already placed by
  -- the bridge step; cells and members bounded by transitivity alone
  module Pick (a : V ℓ) (ha : ⟨ isL a ⟩)
              (γ : V ℓ) (limγ : ⟨ isLimit γ ⟩) (a∈J : ⟨ a ∈ˢ Jset γ limγ ⟩)
              (inh : (x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ V ℓ ] ⟨ y ∈ˢ x ⟩ ∥₁) where

    Mem : Type (ℓ-suc ℓ)
    Mem = MemAt γ limγ

    W : SWO Mem
    W = Jset-order γ limγ

    Cell : V ℓ → Mem → hProp (ℓ-suc ℓ)
    Cell x m = m .fst ∈ˢ x

    inLevel : (x : V ℓ) → ⟨ x ∈ˢ a ⟩ → ⟨ x ∈ˢ Jset γ limγ ⟩
    inLevel x h = Sset-trans γ h a∈J

    members : (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩) → ∥ Σ[ m ∈ Mem ] ⟨ Cell x m ⟩ ∥₁
    members x h = PT.map (λ { (y , y∈x) →
      (y , Sset-trans γ y∈x (inLevel x h)) , y∈x }) (inh x h)

    -- the pick: the least element of the cell under Jset-order (the search)
    pick : (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩) → Σ[ m ∈ Mem ] IsLeast W (Cell x) m
    pick x h = leastOf W lem (Cell x) (members x h)

    -- obligation 1: the pick is a member of its cell
    pickMember : (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩) → ⟨ fst (fst (pick x h)) ∈ˢ x ⟩
    pickMember x h = fst (snd (pick x h))

    -- obligation 2a: the pick is canonical, i.e. least per the order
    pickLeast : (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩) → IsLeast W (Cell x) (fst (pick x h))
    pickLeast x h = snd (pick x h)

    -- obligation 2b: least elements are unique per the order (trichotomy)
    leastUnique : (x : V ℓ) (m m' : Mem)
                → IsLeast W (Cell x) m → IsLeast W (Cell x) m' → m ≡ m'
    leastUnique x m m' lm lm' = cong fst (isPropLeastOf W (Cell x) (m , lm) (m' , lm'))

  -- the bridge step eliminated into the propositional target: the pick-level
  -- statement is delivered on the delivered machinery and the one hypothesis
  rawRehome : RawChoice
  rawRehome a ha inh = PT.rec PT.squash₁ go (bridgeL→J a ha)
    where
    go : Σ[ γ ∈ V ℓ ] Σ[ limγ ∈ ⟨ isLimit γ ⟩ ] ⟨ a ∈ˢ Jset γ limγ ⟩
       → ∥ Σ[ γ ∈ V ℓ ] Σ[ limγ ∈ ⟨ isLimit γ ⟩ ] Σ[ a∈J ∈ ⟨ a ∈ˢ Jset γ limγ ⟩ ]
           Σ[ ch ∈ ((x : V ℓ) → ⟨ x ∈ˢ a ⟩ → V ℓ) ]
             Σ[ pick∈ ∈ ((x : V ℓ) (h : ⟨ x ∈ˢ a ⟩) → ⟨ ch x h ∈ˢ x ⟩) ]
               ( (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩)
                   → IsLeast (Jset-order γ limγ) (CellAt γ limγ x)
                       (ch x h , bound γ limγ x (ch x h) (Sset-trans γ h a∈J) (pick∈ x h)) ) ∥₁
    go (γ , limγ , a∈J) = ∣ γ , limγ , a∈J , ch , pick∈ , canonical ∣₁
      where
      module P = Pick a ha γ limγ a∈J inh
      ch : (x : V ℓ) → ⟨ x ∈ˢ a ⟩ → V ℓ
      ch x h = fst (fst (P.pick x h))
      pick∈ : (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩) → ⟨ ch x h ∈ˢ x ⟩
      pick∈ x h = fst (snd (P.pick x h))
      canonical : (x : V ℓ) (h : ⟨ x ∈ˢ a ⟩)
                → IsLeast (Jset-order γ limγ) (CellAt γ limγ x)
                    (ch x h , bound γ limγ x (ch x h) (Sset-trans γ h a∈J) (pick∈ x h))
      canonical x h = subst (λ m → IsLeast (Jset-order γ limγ) (CellAt γ limγ x) m)
        (Σ≡Prop (λ m → snd (m ∈ˢ Jset γ limγ)) refl)
        (P.pickLeast x h)

-- =====================================================================
-- The Model:57 re-point's shape: what `L⊨ZFC`'s `hasChoice` field consumes.
-- The statement is the delivered `ChoiceStatement` verbatim over the L
-- carrier (𝒮ʟ); a re-home chapter's theorem must have this type so that
-- Model:99's `hasChoice = hasChoiceJ L⊨ZF` typechecks.  NOT proven here:
-- the carve (separate by a description naming the order) and the centre's
-- re-carriage (J→L, i.e. the reverse bridge half) are outside the probe.
-- =====================================================================

module Repoint where
  open hPropStructure 𝒮ʟ
  module ModelL = FOL.ZFModel 𝒮ʟ
  open ModelL using ( isZFModel )

  ChoiceStatement : isZFModel → Type (ℓ-suc ℓ)
  ChoiceStatement zf =
    (a : S)
    → ((x : S) → ⟨ x ∈ˢ a ⟩ → ∥ Σ[ y ∈ S ] ⟨ y ∈ˢ x ⟩ ∥₁)
    → ((x y : S) → ⟨ x ∈ˢ a ⟩ → ⟨ y ∈ˢ a ⟩
         → ∥ Σ[ z ∈ S ] (⟨ z ∈ˢ x ⟩ × ⟨ z ∈ˢ y ⟩) ∥₁ → x ≡ y)
    → ∥ Σ[ c ∈ S ] ((x : S) → ⟨ x ∈ˢ a ⟩
         → isContr (Σ[ z ∈ S ] ⟨ z ∈ˢ (c ∩ x) ⟩)) ∥₁
    where open ModelL.isZFModel zf using ( _∩_ )

  RehomedChoice : Type (ℓ-suc (ℓ-suc ℓ))
  RehomedChoice = (zf : isZFModel) → ChoiceStatement zf
