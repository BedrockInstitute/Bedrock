{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.416] W3 PROBE, then the obligation.  W3 FIRST:
-- `rank-recursion-elaborates`.  Recursion on `wf∙` alone, body `∅`
-- in every case.  No `boundingOrd`, no trichotomy, no membership.
-- Then, if that elaborates, `swo-rank`, `swo-rank-ord`, `swo-rank-mono`.
--
-- GENERIC in `A` and in `w`.  No stage, no cardinal, no numeral.
-- Carrier at `ℓ`, order at `ℓ-suc ℓ`.  No `leastOf`, no `PT.rec`.
--
-- ONE Agda process per run, GHCRTS as the program set it on this pane.
-- Nothing lands in src/.

open import Base.Prelude
open import Base.Truth

module LJ-1-416.Probe416 {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( boundingOrd; ∅-ord )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; module WFI; isPropAcc )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- W3.  Recursion alone.  Motive `A → S`.  Body returns `∅` at every
-- point.  The accessibility predicate lives at `ℓ-suc ℓ`; the carrier
-- lives at `ℓ`.  This term does not call `boundingOrd`.
-- =====================================================================

module Rank {A : Type ℓ} (w : SWO A) where
  open SWO w

  rank-recursion-elaborates : A → S
  rank-recursion-elaborates =
    WFI.induction wf∙ {P = λ _ → S} (λ _ _ → ∅)

  -- The family below `a` is indexed by the WHOLE carrier `A` (level `ℓ`),
  -- never by `Σ[ b ∈ A ] (b <∙ a)` (level `ℓ-suc ℓ`).  Trichotomy picks
  -- which indices contribute a rank; the other two cases contribute `∅`.

  RankAt : A → Type (ℓ-suc ℓ)
  RankAt _ = Σ[ ρ ∈ S ] IsOrd ρ

  predAt : (a b : A)
         → Tri (b <∙ a) (b ≡ a) (a <∙ b)
         → ((x : A) → x <∙ a → RankAt x)
         → RankAt b
  predAt a b (lt h) ih = ih b h
  predAt a b (eq _) _  = ∅ , ∅-ord
  predAt a b (gt _) _  = ∅ , ∅-ord

  pred : (a : A) → ((b : A) → b <∙ a → RankAt b) → (b : A) → RankAt b
  pred a ih b = predAt a b (tri∙ b a) ih

  -- Acc-recursion, not `WFI.induction-compute`.  A first attempt put
  -- `IsOrd` in that motive; the check ran 11 min at 526 MB RSS and had
  -- not returned.  Not a heap wall.  The compute path lands in `IsOrd`.

  go : (a : A) → Acc _<∙_ a → RankAt a
  go a (acc rs) = bnd .fst , bnd .snd .fst
    where
    ih : (x : A) → x <∙ a → RankAt x
    ih x h = go x (rs x h)
    bnd = boundingOrd A (λ x → pred a ih x .fst) (λ x → pred a ih x .snd)

  swo-rank : A → S
  swo-rank a = go a (wf∙ a) .fst

  swo-rank-ord : (a : A) → IsOrd (swo-rank a)
  swo-rank-ord a = go a (wf∙ a) .snd

  swo-rank-mono : (a b : A) → a <∙ b → ⟨ swo-rank a ∈ˢ swo-rank b ⟩
  swo-rank-mono a b a<b = fromAcc (wf∙ b)
    where
    fromAcc : (ab : Acc _<∙_ b) → ⟨ swo-rank a ∈ˢ go b ab .fst ⟩
    fromAcc (acc rs) =
      subst (λ σ → ⟨ σ ∈ˢ bnd .fst ⟩) (fromTri (tri∙ a b)) (bnd .snd .snd a)
      where
      ih : (x : A) → x <∙ b → RankAt x
      ih x h = go x (rs x h)
      bnd = boundingOrd A (λ x → pred b ih x .fst) (λ x → pred b ih x .snd)

      fromTri : (t : Tri (a <∙ b) (a ≡ b) (b <∙ a))
              → predAt b a t ih .fst ≡ swo-rank a
      fromTri (lt h) =
        cong (λ r → go a r .fst) (isPropAcc a (rs a h) (wf∙ a))
      fromTri (eq p) =
        Empty.rec (irr∙ b (subst (λ z → z <∙ b) p a<b))
      fromTri (gt h) =
        Empty.rec (irr∙ a (trans∙ a b a a<b h))

-- Top-level names the witness meter reads.  `A` and `w` stay generic.

rank-recursion-elaborates : {A : Type ℓ} (w : SWO A) → A → S
rank-recursion-elaborates w = Rank.rank-recursion-elaborates w

swo-rank : {A : Type ℓ} (w : SWO A) → A → S
swo-rank w = Rank.swo-rank w

swo-rank-ord : {A : Type ℓ} (w : SWO A) (a : A) → IsOrd (swo-rank w a)
swo-rank-ord w = Rank.swo-rank-ord w

swo-rank-mono : {A : Type ℓ} (w : SWO A) (a b : A)
              → SWO._<∙_ w a b
              → ⟨ swo-rank w a ∈ˢ swo-rank w b ⟩
swo-rank-mono w = Rank.swo-rank-mono w
