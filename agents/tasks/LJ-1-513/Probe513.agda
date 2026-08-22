{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.513]  Re-base the order on membership, so the predecessor set forms.
--
-- The obligation is `preds`, section 2.  Section 1 is W3, the predecessor
-- TYPE alone: the whole obstruction [LJ-1.497] measured is one universe
-- level (agents/tasks/LJ-1-497/runs/cure-level.out).  Section 3 re-bases
-- the ordinal order on `_∈ₛ_`, which is what [LJ-1.497] named as this
-- task.  Section 4 is the decisive check: `boundingOrd` ACCEPTS both
-- predecessor carriers, which is the acceptance that failed before.
--
-- `swo-rank'` is NOT built here and the adequacy is NOT attempted: AD12
-- gives this brief one obligation.
--
-- Rebuilds [LJ-1.490]'s `OrdSWO` at the SMALL membership.  Does not import
-- a probe.  Nothing lands in src/.  Does not postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-513.Probe513 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; regularityV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj; ∈ₛ↪ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd )
open import L.Ordinal {ℓ} using ( boundingOrd; mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
-- THE RE-BASING IS THIS LINE.  [LJ-1.497] instantiated the order level at
-- `ℓ-suc ℓ` (agents/tasks/LJ-1-497/Probe497.agda:31).  Here it is `ℓ`.
open import L.WellOrder.Base {ℓ} using ( SWO; Tri; lt; eq; gt )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ; extensionality )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
open hPropStructure 𝒮ᵥ using ( _∈ᵗ_ )

-- =====================================================================
-- 1.  W3.  The predecessor TYPE, through `_∈ₛ_`, at the level a carrier
--     needs.  `Σ[ x ∈ A ] (x <∙ a)` landed at `Type (ℓ-suc ℓ)`; this Σ
--     is declared at `Type ℓ` and the declaration is the measurement.
-- =====================================================================

preds-type : (a : S) → IsOrd (fst a) → Type ℓ
preds-type a _ = Σ[ x ∈ ⟪ fst a ⟫ ] ⟨ ⟪ fst a ⟫↪ x ∈ₛ fst a ⟩

-- =====================================================================
-- 2.  THE OBLIGATION.  The predecessor type, sealed as a set of L.
--     It is the predecessors and nothing weaker: `is-α` proves it has
--     exactly the members of `a`.
-- =====================================================================

module Preds (a : S) (oa : IsOrd (fst a)) where

  α : V ℓ
  α = fst a

  P : Type ℓ
  P = preds-type a oa

  ix : P → V ℓ
  ix p = ⟪ α ⟫↪ (p .fst)

  predsV : V ℓ
  predsV = sett P ix

  -- every member of the predecessor set is a member of `a`
  into : (x : V ℓ) → ⟨ x ∈ₛ predsV ⟩ → ⟨ x ∈ₛ α ⟩
  into x h = PT.rec (snd (x ∈ₛ α)) step (∈∈ₛ {a = x} {b = predsV} .snd h)
    where
    step : Σ[ p ∈ P ] (ix p ≡ x) → ⟨ x ∈ₛ α ⟩
    step (p , e) = subst (λ v → ⟨ v ∈ₛ α ⟩) e (p .snd)

  -- and every member of `a` is a member of the predecessor set
  outo : (x : V ℓ) → ⟨ x ∈ₛ α ⟩ → ⟨ x ∈ₛ predsV ⟩
  outo x h = ∈∈ₛ {a = x} {b = predsV} .fst PT.∣ ((m , ∈ₛ↪ α m) , e) ∣₁
    where
    f = fiber α {x} (∈∈ₛ {a = x} {b = α} .snd h)
    m = f .fst
    e : ⟪ α ⟫↪ m ≡ x
    e = f .snd

  is-α : predsV ≡ α
  is-α = extensionality predsV α (into , outo)

  predsL : ⟨ isL predsV ⟩
  predsL = subst (λ v → ⟨ isL v ⟩) (sym is-α) (snd a)

  predsOrd : IsOrd predsV
  predsOrd = subst IsOrd (sym is-α) oa

preds : (a : S) → IsOrd (fst a) → S
preds a oa = Preds.predsV a oa , Preds.predsL a oa

-- the predecessor set is the predecessors: same members as `a`
preds-is-a : (a : S) (oa : IsOrd (fst a)) → fst (preds a oa) ≡ fst a
preds-is-a = Preds.is-α

-- =====================================================================
-- 3.  THE ORDER, RE-BASED ON `_∈ₛ_`.  [LJ-1.490]'s `OrdSWO` rebuilt with
--     `_≺ₛ_` at `Type ℓ` in place of `_≺_` at `Type (ℓ-suc ℓ)`
--     (agents/tasks/LJ-1-490/Probe490.agda:167).  The four laws are the
--     same laws; each converts through `∈∈ₛ` and nothing else changes.
-- =====================================================================

module OrdSWO∈ₛ (α : V ℓ) (oα : IsOrd α) where

  _≺ₛ_ : ⟪ α ⟫ → ⟪ α ⟫ → Type ℓ
  m ≺ₛ n = ⟨ ⟪ α ⟫↪ m ∈ₛ ⟪ α ⟫↪ n ⟩

  to∈ : {m n : ⟪ α ⟫} → m ≺ₛ n → ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n
  to∈ {m} {n} = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = ⟪ α ⟫↪ n} .snd

  fr∈ : {m n : ⟪ α ⟫} → ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n → m ≺ₛ n
  fr∈ {m} {n} = ∈∈ₛ {a = ⟪ α ⟫↪ m} {b = ⟪ α ⟫↪ n} .fst

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺ₛ n) (m ≡ n) (n ≺ₛ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺ₛ n) (m ≡ n) (n ≺ₛ m)
    go (inl h)       = lt (fr∈ h)
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt (fr∈ h)

  irr₁ : (m : ⟪ α ⟫) → (m ≺ₛ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) (to∈ h)

  trans₁ : (m n k : ⟪ α ⟫) → m ≺ₛ n → n ≺ₛ k → m ≺ₛ k
  trans₁ m n k h h' = fr∈ (ord-inord k .fst (to∈ h) (to∈ h'))

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺ₛ_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) (to∈ n≺m)))

  wf₁ : WellFounded _≺ₛ_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  w : SWO {ℓc = ℓ} ⟪ α ⟫
  w = record
    { _<∙_   = _≺ₛ_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

-- =====================================================================
-- 4.  THE DECISIVE CHECK.  `boundingOrd` wants a `Type ℓ` index
--     (src/L/Ordinal.lagda.md:154).  That is the acceptance which
--     `runs/cure-level.out` refused.  Both predecessor carriers are
--     accepted here, so the obstruction is REMOVED and not relocated.
-- =====================================================================

module Accepts (a : S) (oa : IsOrd (fst a)) where

  open Preds a oa using ( predsV; predsOrd )
  open OrdSWO∈ₛ (fst a) oa using ( _≺ₛ_; ord-inord )

  -- (i) through the SET the obligation delivers: its carrier is `Type ℓ`.
  viaSet : Σ[ β ∈ V ℓ ] (IsOrd β × ((x : ⟪ predsV ⟫) → ⟪ predsV ⟫↪ x ∈ᵗ β))
  viaSet = boundingOrd ⟪ predsV ⟫ ⟪ predsV ⟫↪
             (λ x → mem-ord {A = predsV} predsOrd (⟪ predsV ⟫↪ x) (member predsV x))

  -- (ii) through the ORDER, at an arbitrary carrier element.  This is
  --      exactly the Σ that `runs/cure-level.out` rejected, with `_<∙_`
  --      re-based on `_∈ₛ_`.
  predsAt : ⟪ fst a ⟫ → Type ℓ
  predsAt n = Σ[ x ∈ ⟪ fst a ⟫ ] (x ≺ₛ n)

  viaOrder : (n : ⟪ fst a ⟫)
           → Σ[ β ∈ V ℓ ] (IsOrd β × ((p : predsAt n) → ⟪ fst a ⟫↪ (p .fst) ∈ᵗ β))
  viaOrder n = boundingOrd (predsAt n) (λ p → ⟪ fst a ⟫↪ (p .fst))
                 (λ p → ord-inord (p .fst))

  -- (iii) the acceptance `Rank.go` itself needs, with the recursive call
  --       taken as a HYPOTHESIS.  This builds no rank: `ih` is given, not
  --       computed.  It measures that the index AND the family both sit
  --       at the level `boundingOrd` wants, which is the exact line
  --       agents/tasks/LJ-1-490/Probe490.agda:146 pads over `A` to avoid.
  viaRankFamily :
      (n : ⟪ fst a ⟫)
      (ih : (x : ⟪ fst a ⟫) → x ≺ₛ n → Σ[ ρ ∈ V ℓ ] IsOrd ρ)
    → Σ[ β ∈ V ℓ ] (IsOrd β × ((p : predsAt n) → ih (p .fst) (p .snd) .fst ∈ᵗ β))
  viaRankFamily n ih = boundingOrd (predsAt n)
                         (λ p → ih (p .fst) (p .snd) .fst)
                         (λ p → ih (p .fst) (p .snd) .snd)
