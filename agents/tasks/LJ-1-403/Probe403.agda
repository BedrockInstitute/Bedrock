{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.403] PROBE.  The descent, as data, in the shape the band recursion
-- owes.  It runs in agents/tasks/LJ-1-403/ and lands nothing in src/.
--
-- W3, FIRST: `goodplus-isProp`.  State `Good⁺` alone with its `isProp`,
-- run it, and report the number of code lines before writing anything
-- else.  The inner code existential stays truncated; membership of `κ`
-- and infinity are the two extra conjuncts, both hProps.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-403.Probe403 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; Lset )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( IsLeast; leastOf )
open import L.Cardinal {ℓ} lem
  using ( _↪_; InjCode; IsCardinalL; module SiteBound )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( ω )
open import Cubical.Foundations.HLevels using ( isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- W3.  `Good⁺` alone, with its `isProp`.  Generic in `κ`.  No numeral,
-- no named cardinal.
-- =====================================================================

module GoodPlus (κ : S) (oκ : IsOrd (fst κ)) where

  open SiteBound κ

  Good⁺ : Mem (Lset β) → hProp (ℓ-suc ℓ)
  Good⁺ δ =
    ( ⟨ fst (up δ) ∈ fst κ ⟩
    × ⟨ ω ∈ fst (up δ) ⟩
    × ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁ )
    , isProp× (snd (fst (up δ) ∈ fst κ))
              (isProp× (snd (ω ∈ fst (up δ)))
                       squash₁)

  goodplus-isProp : (δ : Mem (Lset β)) → isProp ⟨ Good⁺ δ ⟩
  goodplus-isProp δ = snd (Good⁺ δ)

-- The strengthened non-emptiness.  This is the type a caller must inhabit
-- to discharge `sel-descent`.  It is NOT proved here.
Ne⁺ : (κ : S) (oκ : IsOrd (fst κ)) → Type (ℓ-suc ℓ)
Ne⁺ κ oκ = ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
              ⟨ GoodPlus.Good⁺ κ oκ δ ⟩ ∥₁

-- What the band recursion's negative case actually holds, and what it
-- would have to prove.  Not inhabited.
CallerNe⁺ : (κ : S) (oκ : IsOrd (fst κ)) → Type (ℓ-suc ℓ)
CallerNe⁺ κ oκ =
    (IsCardinalL κ → Empty.⊥)
  → ⟨ ω ∈ fst κ ⟩
  → Ne⁺ κ oκ

-- =====================================================================
-- THE OBLIGATION.  One strengthened selection, then [LJ-1.401]'s
-- `isPropInjCode` and a second `leastOf`, then [LJ-1.402]'s readback.
-- The two hypotheses are taken at the types the assembly consumes:
-- `isPropInjCode` as [LJ-1.401] states it; `sel-arrow` as the generic
-- readback [LJ-1.402] measures (`Small`), not as the `Selected`-sited
-- type that names `InternalLeastCard.Selected.δᴸ` under unstrengthened
-- `Good`.  That sited type cannot consume a `Good⁺` selection.
-- =====================================================================

module _
  (isPropInjCode : (F a b : S) → isProp (InjCode F a b))
  (sel-arrow : (F a b : S) → InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫)
  where

  sel-descent :
      (κ : S) (oκ : IsOrd (fst κ))
    → (ne⁺ : Ne⁺ κ oκ)
    → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ fst κ ⟩
                 × ⟨ ω ∈ fst δ ⟩
                 × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )
  sel-descent κ oκ ne⁺ = up δ-mem , mem , inf , arrow
    where
    open SiteBound κ
    open GoodPlus κ oκ

    least⁺ : Σ[ δ ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) Good⁺ δ
    least⁺ = leastOf (orderAt β oβ) lem Good⁺ ne⁺

    δ-mem : Mem (Lset β)
    δ-mem = fst least⁺

    good : ⟨ Good⁺ δ-mem ⟩
    good = fst (snd least⁺)

    mem : ⟨ fst (up δ-mem) ∈ fst κ ⟩
    mem = fst good

    inf : ⟨ ω ∈ fst (up δ-mem) ⟩
    inf = fst (snd good)

    code-ne : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ-mem) ∥₁
    code-ne = snd (snd good)

    GoodCode : Mem (Lset β) → hProp (ℓ-suc ℓ)
    GoodCode F = InjCode (up F) κ (up δ-mem)
               , isPropInjCode (up F) κ (up δ-mem)

    chosen : Σ[ F ∈ Mem (Lset β) ] IsLeast (orderAt β oβ) GoodCode F
    chosen = leastOf (orderAt β oβ) lem GoodCode code-ne

    code : InjCode (up (fst chosen)) κ (up δ-mem)
    code = fst (snd chosen)

    arrow : ⟪ fst κ ⟫ ↪ ⟪ fst (up δ-mem) ⟫
    arrow = sel-arrow (up (fst chosen)) κ (up δ-mem) code
