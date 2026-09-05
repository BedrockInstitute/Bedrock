{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.439] PROBE.  A limit ordinal above any ordinal, with
-- successor closure.  It runs in agents/tasks/LJ-1-439/ and lands
-- nothing in src/.
--
--   W3 FIRST  `plus-omega-suc`.  The third conjunct of `limit-above`.
--              Typechecked ALONE before `limit-above` is added.
--              Route 1: exported names of the +ω seal, trichotomy,
--              no unfolding.
--
--   TERM      `limit-above`.  The Sigma, witness `+ω u`, nothing else.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ-syntax )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

module LJ-1-439.Probe439 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-in; +ω-mem; +ω-sup; +ω-iter; sucIter-ord; +ω-ord )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- W3.  plus-omega-suc ALONE.  Route 1 through the exported names.
-- `limit-above` is omitted from this first check.
-- =====================================================================

plus-omega-suc :
    (u : S) → IsOrd u
  → (d : S) → ⟨ d ∈ˢ +ω u ⟩ → ⟨ sucV d ∈ˢ +ω u ⟩
plus-omega-suc u ou d d∈ = atD (ord-tri d od u ou)
  where
  oλ : IsOrd (+ω u)
  oλ = +ω-ord u ou
  od : IsOrd d
  od = mem-ord {A = +ω u} oλ d d∈
  osd : IsOrd (sucV d)
  osd = suc-ord od

  -- d ∈ u: trichotomy of sucV d against u, then introduce into the block.
  below : ⟨ d ∈ˢ u ⟩ → ⟨ sucV d ∈ˢ +ω u ⟩
  below d∈u = atS (ord-tri (sucV d) osd u ou)
    where
    atS : Tri (sucV d) u → ⟨ sucV d ∈ˢ +ω u ⟩
    atS (inl sd∈u) = +ω-sup u (sucV d) sd∈u
    atS (inr (inl sd≡u)) =
      subst (λ w → ⟨ w ∈ˢ +ω u ⟩) (sym sd≡u) (+ω-mem u)
    atS (inr (inr u∈sd)) =
      Empty.rec*
        (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* u∈sd
          (λ u∈d → lift (∈-irrefl u (ou .fst u∈d d∈u)))
          (λ u≡d → lift (∈-irrefl d
            (subst (λ w → ⟨ d ∈ˢ w ⟩) u≡d d∈u))))

  -- d ≡ u: sucV d is the first iterate, already in the block.
  equal : d ≡ u → ⟨ sucV d ∈ˢ +ω u ⟩
  equal d≡u = subst (λ w → ⟨ sucV w ∈ˢ +ω u ⟩) (sym d≡u) (+ω-iter 1 u)

  -- u ∈ d: trichotomy of sucV d against the block. Case ∈ is the goal.
  -- Case block ∈ sucV d is irreflexive. Case sucV d ≡ block is the residue.
  above : ⟨ u ∈ˢ d ⟩ → ⟨ sucV d ∈ˢ +ω u ⟩
  above u∈d = atL (ord-tri (sucV d) osd (+ω u) oλ)
    where
    -- sucV d ≡ +ω u and u ∈ d. Peel sucIter 1: either it equals d,
    -- which contradicts, or it sits in d, which the exports cannot
    -- finish. Route 1 stops at the inner hole.
    eq-above : sucV d ≡ +ω u → ⟨ sucV d ∈ˢ +ω u ⟩
    eq-above sd≡λ =
      ∈sucV-elim {P = ⟨ sucV d ∈ˢ +ω u ⟩} (snd (sucV d ∈ˢ +ω u)) suc1∈sd
        (λ _ → {!!})
        (λ suc1≡d → Empty.rec (iter-eq suc1≡d))
      where
      suc1∈sd : ⟨ sucV u ∈ˢ sucV d ⟩
      suc1∈sd = subst (λ w → ⟨ sucV u ∈ˢ w ⟩) (sym sd≡λ) (+ω-iter 1 u)
      iter-eq : sucV u ≡ d → Empty.⊥
      iter-eq suc1≡d =
        ∈-irrefl (+ω u) (oλ .fst (self∈sucV (+ω u)) next∈)
        where
        two≡λ : sucIter 2 u ≡ +ω u
        two≡λ = cong sucV suc1≡d ∙ sd≡λ
        next∈ : ⟨ sucV (+ω u) ∈ˢ +ω u ⟩
        next∈ = subst (λ w → ⟨ sucV w ∈ˢ +ω u ⟩) two≡λ (+ω-iter 3 u)

    not-below : ⟨ +ω u ∈ˢ sucV d ⟩ → ⟨ sucV d ∈ˢ +ω u ⟩
    not-below λ∈sd =
      Empty.rec*
        (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* λ∈sd
          (λ λ∈d → lift (∈-irrefl (+ω u) (oλ .fst λ∈d d∈)))
          (λ λ≡d → lift (∈-irrefl d
            (subst (λ w → ⟨ d ∈ˢ w ⟩) λ≡d d∈))))

    atL : Tri (sucV d) (+ω u) → ⟨ sucV d ∈ˢ +ω u ⟩
    atL (inl sd∈λ)       = sd∈λ
    atL (inr (inl sd≡λ)) = eq-above sd≡λ
    atL (inr (inr λ∈sd)) = not-below λ∈sd

  atD : Tri d u → ⟨ sucV d ∈ˢ +ω u ⟩
  atD (inl d∈u)       = below d∈u
  atD (inr (inl d≡u)) = equal d≡u
  atD (inr (inr u∈d)) = above u∈d

-- =====================================================================
-- Diagnostic: ONE export closes the residue. Not the obligation.
-- The type is the archived elimination, last green in
-- archive/src/2026-08-09-rud-route/L/Rud/OrdBlocks.lagda.md:107-108.
-- =====================================================================

module WithOut
  (+ω-out : (u x : S) → ⟨ x ∈ˢ +ω u ⟩
          → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁)
  where

  plus-omega-suc-from-out :
      (u : S) → IsOrd u
    → (d : S) → ⟨ d ∈ˢ +ω u ⟩ → ⟨ sucV d ∈ˢ +ω u ⟩
  plus-omega-suc-from-out u ou d d∈ =
    PT.rec (snd (sucV d ∈ˢ +ω u)) fromOut (+ω-out u d d∈)
    where
    od : IsOrd d
    od = mem-ord {A = +ω u} (+ω-ord u ou) d d∈
    osd : IsOrd (sucV d)
    osd = suc-ord od

    fromOut : Σ[ n ∈ ℕ ] ⟨ d ∈ˢ sucIter (suc n) u ⟩ → ⟨ sucV d ∈ˢ +ω u ⟩
    fromOut (n , d∈sn) =
      ∈sucV-elim {P = ⟨ sucV d ∈ˢ +ω u ⟩} (snd (sucV d ∈ˢ +ω u)) d∈sn
        (λ d∈n → climb d∈n (ord-tri (sucV d) osd (sucIter n u) (sucIter-ord n ou)))
        (λ d≡n → subst (λ w → ⟨ sucV w ∈ˢ +ω u ⟩) (sym d≡n)
                   (+ω-iter (suc n) u))
      where
      climb : ⟨ d ∈ˢ sucIter n u ⟩ → Tri (sucV d) (sucIter n u)
            → ⟨ sucV d ∈ˢ +ω u ⟩
      climb d∈n (inl sd∈n) = +ω-in u (sucV d) n (∈sucV-inl sd∈n)
      climb d∈n (inr (inl sd≡n)) =
        subst (λ w → ⟨ w ∈ˢ +ω u ⟩) (sym sd≡n) (+ω-iter n u)
      climb d∈n (inr (inr n∈sd)) =
        Empty.rec*
          (∈sucV-elim {P = Empty.⊥* {ℓ-suc ℓ}} Empty.isProp⊥* n∈sd
            (λ n∈d → lift (∈-irrefl (sucIter n u)
              (sucIter-ord n ou .fst n∈d d∈n)))
            (λ n≡d → lift (∈-irrefl d
              (subst (λ w → ⟨ d ∈ˢ w ⟩) n≡d d∈n))))

  limit-above-from-out :
      (u : S) → IsOrd u
    → Σ[ lam ∈ S ] ( IsOrd lam
                   × ⟨ u ∈ˢ lam ⟩
                   × ((d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) )
  limit-above-from-out u ou =
    +ω u , (+ω-ord u ou , +ω-mem u , plus-omega-suc-from-out u ou)

-- =====================================================================
-- THE OBLIGATION.  Witness `+ω u`.  The third conjunct is W3, unfilled.
-- =====================================================================

limit-above :
    (u : S) → IsOrd u
  → Σ[ lam ∈ S ] ( IsOrd lam
                 × ⟨ u ∈ˢ lam ⟩
                 × ((d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) )
limit-above u ou = +ω u , (+ω-ord u ou , +ω-mem u , plus-omega-suc u ou)
