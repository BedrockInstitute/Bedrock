{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.565] CONTROL x.  THE WHOLE INDUCTION, WITH THE WITNESS HELD
-- ABSTRACT FROM END TO END.
--
-- Control565h: the successor case, abstract witness, 27.37 s.
-- Control565w: the bridge back to [LJ-1.536]'s own statement, free at
--              a VARIABLE γ, 1.95 s.
-- Control565v: attempt 1's ordinal split, free, 1.84 s.  Its rows are
--              restated here because that file is a control and not a
--              module this one can import a `where` block from.
--
-- WHAT THIS FILE ASKS.  Whether those three compose into
-- `HierBelowAllH`, leaving the LIMIT case as the only hypothesis.
-- Attempt 1's `MoveAlong` walled twice (runs/ctls-0.out, ctlt-0.out)
-- carrying `HierBelow` along `sucV δ ≡ γ`.  Here the motive QUANTIFIES
-- over the witness, so the transport is a plain `subst` on a motive
-- that never names a computed witness, and no `PathP` is needed.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-565.runs.Control565x {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; hier-unique )
open import LJ-1-536.Probe536 {ℓ} lem
  using ( step; isL-ord; seq; HierBelow; HierBelowAll; StageHigh
        ; reduction; IsLimit; module Adjoin )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- ---- the abstract-witness statement, and the bridge back ----------

HierBelowH : (γ : V ℓ) → ⟨ isL γ ⟩ → IsOrd γ → Type (ℓ-suc ℓ)
HierBelowH γ hγ oγ = ⟨ fst (hierL γ hγ oγ) ∈ Lset (step 3 γ) ⟩

Motive : V ℓ → Type (ℓ-suc ℓ)
Motive γ = (h : ⟨ isL γ ⟩) (o : IsOrd γ) → HierBelowH γ h o

bridge : (γ : V ℓ) (oγ : IsOrd γ) → HierBelowH γ (isL-ord γ oγ) oγ → HierBelow γ oγ
bridge γ oγ x = x

-- ---- the two cures ------------------------------------------------

step-suc : (n : ℕ) (α : V ℓ) → step n (sucV α) ≡ sucV (step n α)
step-suc zero    α = refl
step-suc (suc n) α = cong sucV (step-suc n α)

move : (x α : V ℓ) → ⟨ x ∈ Lset (step 4 α) ⟩ → ⟨ x ∈ Lset (step 3 (sucV α)) ⟩
move x α p = subst (λ w → ⟨ x ∈ Lset w ⟩) (sym (step-suc 3 α)) p

hierL-irr : (β : V ℓ) (h₁ h₂ : ⟨ isL β ⟩) (o₁ o₂ : IsOrd β)
          → hierL β h₁ o₁ ≡ hierL β h₂ o₂
hierL-irr β h₁ h₂ o₁ o₂ =
  hier-unique β (hierL β h₁ o₁) (hierL β h₂ o₂)
    (hierL-spec β h₁ o₁) (hierL-spec β h₂ o₂)

successor-step : (α : V ℓ) (oα : IsOrd α)
                 (h : ⟨ isL (sucV α) ⟩) (o : IsOrd (sucV α))
               → HierBelow α oα → HierBelowH (sucV α) h o
successor-step α oα h o hyp =
  subst (λ w → ⟨ fst w ∈ Lset (step 3 (sucV α)) ⟩)
        (hierL-irr (sucV α) _ h _ o)
        (move (fst (seq α oα)) α (Adjoin.seq∈ α oα hyp))

-- ---- attempt 1's ordinal split (runs/Control565v.agda) ------------

Succ : V ℓ → hProp (ℓ-suc ℓ)
Succ γ = ∥ Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × (sucV δ ≡ γ)) ∥₁ , PT.squash₁

not-succ→limit : (γ : V ℓ) (oγ : IsOrd γ)
               → (⟨ Succ γ ⟩ → Empty.⊥) → IsLimit γ
not-succ→limit γ oγ ¬s δ δ∈γ = Sum.rec
  (λ s∈γ → s∈γ)
  (λ s≡γ → Empty.rec (¬s ∣ δ , (δ∈γ , s≡γ) ∣₁))
  (suc∈or≡ δ γ (mem-ord {A = γ} oγ δ δ∈γ) oγ δ∈γ)

-- ---- THE INDUCTION -------------------------------------------------

HierBelowAllH : Type (ℓ-suc ℓ)
HierBelowAllH = (γ : V ℓ) → Motive γ

HierBelowLimitH : Type (ℓ-suc ℓ)
HierBelowLimitH = (γ : V ℓ) (h : ⟨ isL γ ⟩) (o : IsOrd γ)
                → IsLimit γ → HierBelowH γ h o

closing : HierBelowLimitH → HierBelowAllH
closing lim = ∈-induction {P = Motive} go
  where
  go : (γ : V ℓ) → ((δ : V ℓ) → ⟨ δ ∈ γ ⟩ → Motive δ) → Motive γ
  go γ IH h o = Sum.rec succ-case limit-case (lem (Succ γ))
    where
    succ-case : ⟨ Succ γ ⟩ → HierBelowH γ h o
    succ-case = PT.rec (snd (fst (hierL γ h o) ∈ Lset (step 3 γ))) pick
      where
      pick : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × (sucV δ ≡ γ)) → HierBelowH γ h o
      pick (δ , (δ∈γ , p)) = subst Motive p
        (λ h' o' → successor-step δ oδ h' o'
                     (bridge δ oδ (IH δ δ∈γ (isL-ord δ oδ) oδ)))
        h o
        where
        oδ : IsOrd δ
        oδ = mem-ord {A = γ} o δ δ∈γ

    limit-case : (⟨ Succ γ ⟩ → Empty.⊥) → HierBelowH γ h o
    limit-case ¬s = lim γ h o (not-succ→limit γ o ¬s)

-- ---- AND OUT TO [LJ-1.536]'S OWN STATEMENT -------------------------

allH→all : HierBelowAllH → HierBelowAll
allH→all f γ oγ = bridge γ oγ (f γ (isL-ord γ oγ) oγ)

-- THE PAYOFF.  `StageHigh` rests on ONE open statement.
stage-high-from-limit : HierBelowLimitH → StageHigh
stage-high-from-limit lim = reduction (allH→all (closing lim))
