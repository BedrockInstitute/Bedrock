{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.531]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: EXTENSIONALITY OF THE ORDER, "because injectivity
-- of a rank over predecessors stands or falls on it", at the shape
--
--   preds-distinguish : (a : S) (oa : IsOrd (fst a)) (m m' : S)
--                     → (their predecessor sets agree) → fst m ≡ fst m'
--
-- and it orders the stop: "If it will not form, the lemma is false".
--
-- IT FORMS, AND IT FORMS AT THE `SWO` RECORD AND NOT AT THE SITE.  The
-- order `P521.swo-rank′` recurses on is `SWO._<∙_ w`
-- (agents/tasks/LJ-1-521/Probe521.agda:234-244: `Rank′.Pred a` is
-- `Σ[ x ∈ A ] (x <∙ a)` and `go`/`step` read nothing else), and the `SWO`
-- bundle CARRIES trichotomy as a field, `tri∙`
-- (src/L/WellOrder/Base.lagda.md:104).  So the extensionality is not a
-- property of the ordinal site that has to be transported in: it is two
-- fields of the record the rank already runs on, `tri∙` and `irr∙`
-- (:104-105).  The brief's `(a , oa)` telescope is not needed to state
-- it, and W2 says to state it at the generic carrier.
--
-- THE FILE IS GENERIC AND IMPORTS NO PROBE.  It does not name
-- `swo-rank′`, `rank-at′` or the site.  Nothing lands in src/.  Does not
-- postulate.

open import Base.Prelude
open import Base.Truth

module LJ-1-531.runs.W3 {ℓ : Level} where

open import L.WellOrder.Base {ℓ} using ( SWO; Tri; lt; eq; gt )
import Cubical.Data.Empty as Empty

module _ {A : Type ℓ} (w : SWO {ℓc = ℓ} A) where
  open SWO w

  -- "their predecessor sets agree", spelled out: each is below the
  -- other's predecessors and back.  This is the hypothesis the brief
  -- left in prose.
  preds-distinguish :
      (j k : A)
    → ((x : A) → x <∙ j → x <∙ k)
    → ((x : A) → x <∙ k → x <∙ j)
    → j ≡ k
  preds-distinguish j k to fro = go (tri∙ j k)
    where
    go : Tri (j <∙ k) (j ≡ k) (k <∙ j) → j ≡ k
    go (lt h) = Empty.rec (irr∙ j (fro j h))
    go (eq p) = p
    go (gt h) = Empty.rec (irr∙ k (to k h))

  -- The engine, alone: trichotomy plus irreflexivity turn ANY strictly
  -- monotone map into an injective one.  `preds-distinguish` above is
  -- one instance of it and the obligation is another, so the file
  -- measures the shape once.
  mono→inj :
      {B : Type ℓ} (R : B → B → Type ℓ)
    → ((b : B) → R b b → Empty.⊥)
    → (f : A → B)
    → ((x y : A) → x <∙ y → R (f x) (f y))
    → (j k : A) → f j ≡ f k → j ≡ k
  mono→inj R irrR f mono j k p = go (tri∙ j k)
    where
    go : Tri (j <∙ k) (j ≡ k) (k <∙ j) → j ≡ k
    go (lt h) = Empty.rec (irrR (f k) (subst (λ v → R v (f k)) p (mono j k h)))
    go (eq q) = q
    go (gt h) = Empty.rec (irrR (f j) (subst (λ v → R v (f j)) (sym p) (mono k j h)))
