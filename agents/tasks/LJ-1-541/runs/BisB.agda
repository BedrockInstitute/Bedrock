{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-541.runs.BisB {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( var; con; _≐_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( fiber )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.WellOrder.Base {ℓ} using ( SWO )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; domAt; domAt-intro )
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT

import LJ-1-521.Probe521 {ℓ} lem as P521
import LJ-1-529.Probe529 {ℓ} lem as P529
import LJ-1-537.Probe537 {ℓ} lem as P537

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  s2 : ∀ {n} → Fin n → Fin (suc (suc n))
  s2 i = suc (suc i)
  s3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  s3 i = suc (suc (suc i))


-- =====================================================================
-- 1.  D-10, MECHANISED.  The brief orders every piece `[LJ-1.537]` names
--     checked at its `file:line` BEFORE any Agda, and `[LJ-1.537]` states
--     the composition "as a reading of the types and not as a
--     measurement".  Each name below is a TYPE ASCRIPTION over a
--     delivered term, transcribed from the predecessor's own report.  A
--     drift between a report and the tree is then a type error in THIS
--     file, and not a sentence anybody has to believe.
--
--     None of the five is re-proved.  Every right-hand side is one name.
-- =====================================================================

-- (i)  the pair splits.  src/L/Coding/Model.lagda.md:329-330.
piece-pr : (x y : S) → fst (prʟ x y) ≡ pr (fst x) (fst y)
piece-pr = prʟ-fst

-- (ii)  the `Q` witness, INSTANTIATED and not hypothesised.
--       agents/tasks/LJ-1-521/Probe521.agda:1162-1164.
piece-Q : (a : S) (oa : IsOrd (fst a))
        → Σ[ Q ∈ S ] P521.ord-reads-Q Q a oa
piece-Q = P521.ord-set-witness

-- (iii)  the rank's one exported equation.
--        agents/tasks/LJ-1-521/Probe521.agda:438-442.
piece-val :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → fst (P521.rank-at′ a oa m mx)
    ≡ P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa) (fiber (fst a) mx .fst)
piece-val = P521.rank-at′-val

-- (iv)  the bound half.  agents/tasks/LJ-1-529/Probe529.agda:133-140.
piece-bound :
    (a : S) (oa : IsOrd (fst a))
  → Σ[ bnd ∈ S ]
      ((m : S) (mx : ⟨ fst m ∈ fst a ⟩)
        → ⟨ pr (fst m) (P521.swo-rank′ (P521.OrdSWO∈ₛ.w (fst a) oa)
                                       (fiber (fst a) mx .fst))
            ∈ fst bnd ⟩)
piece-bound = P529.rank-bound′

-- (v)  the satisfaction half's fourth existential.
--      agents/tasks/LJ-1-537/Probe537.agda:616-620.
piece-approx :
    (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
  → Σ[ f ∈ S ] P537.Approximates a oa m mx f
piece-approx = P537.approx-carve

-- AND THE ONE THE BRIEF CALLS ALREADY DELIVERED.  `[LJ-1.524]`'s reading
-- (lj-1.524-report.md:277), carried by `[LJ-1.529]` to the RE-BASED
-- bound (Probe529.agda:236-243).  It is the whole of `domAt`'s first
-- direction and section 5.1 spends it.
piece-read :
    (a : S) (oa : IsOrd (fst a)) (x y : S)
  → ⟨ pr (fst x) (fst y) ∈ fst (P529.Carve.G a oa) ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (pr (fst x) (fst y) ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
piece-read = P529.Carve.read

-- =====================================================================
-- 2.  THE CONJUNCT'S TYPE, read out of `InjCode` so that nothing can
--     drift (src/L/Cardinal.lagda.md:223-228).  `domAt zero (suc zero)`
--     at `(F ∷ a ∷ [])` reads slot 0 as the graph and slot 1 as the
--     domain, and the projection below typechecks only if `DomAtOf` is
--     definitionally the SECOND component there.
-- =====================================================================

DomAtOf : S → S → Type (ℓ-suc ℓ)
DomAtOf F a = ⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩

domAt-is-second-of-InjCode : (F a b : S) → InjCode F a b → DomAtOf F a
domAt-is-second-of-InjCode F a b h = h .snd .fst

-- =====================================================================
-- 3.  W3, THE ENVIRONMENT MATCH.  This is runs/W3.agda, repeated here
--     because a file cannot import the slice it was cut from.
--
--     `rankFo Q a` (Probe521.agda:493-501) at `(z ∷ [])` is
--
--       ∃ q. q ≐ Q ∧ ∃ m. ∃ r. ( prAtL z m r ∧ m ∈ a ∧ ∃ f. fn ∧ asg ∧ sup )
--
--     and at the innermost point the environment is
--     `(f ∷ r ∷ m ∷ q ∷ z ∷ [])`, which is `[LJ-1.521]`'s `Env.γ5`
--     (Probe521.agda:512-516).  `[LJ-1.537]` checked that environment in
--     a SIDE file against a hand-written telescope (runs/Pin.agda:46-62);
--     this section runs `approx-carve` inside the formula itself.
-- =====================================================================

module Sat (a : S) (oa : IsOrd (fst a)) (x : S) (xa : ⟨ fst x ∈ fst a ⟩)
  where

  -- slot q.  `[LJ-1.537]`'s `Qwit` (Probe537.agda:581-582), same term.
  Q : S
  Q = P521.ord-set-witness a oa .fst

  -- slot r.
  r : S
  r = P521.rank-at′ a oa x xa

  -- slot z.  `[LJ-1.537]`'s `Zof` (Probe537.agda:584-585), same term.
  z : S
  z = prʟ x r

  -- the first conjunct at `q := Q`: `refl`.  `≈ˢ` on the model is
  -- `λ u v → fst u ≈ˢ fst v` (src/FOL/ZFStructure.lagda.md:148) over
  -- `𝒮ᵥ`'s path equality (src/V/Hierarchy.lagda.md:82).
  qQ : ⟨ (Q ∷ z ∷ []) ⊨ (var zero ≐ con Q) ⟩
  qQ = refl

  -- the second conjunct: `prʟ-fst` through `prAtL-adequate`
  -- (src/L/Coding/Model.lagda.md:125-128).
  hpr : ⟨ (r ∷ x ∷ Q ∷ z ∷ []) ⊨ prAtL (s3 zero) (suc zero) zero ⟩
  hpr = subst ⟨_⟩
          (sym (prAtL-adequate (s3 zero) (suc zero) zero (r ∷ x ∷ Q ∷ z ∷ [])))
          (prʟ-fst x r)

  -- the third conjunct is `xa` itself; the fourth existential is
  -- `[LJ-1.537]`'s carve passed WHOLE, so no environment is re-spelled.
  sat : ⟨ (z ∷ []) ⊨ P521.rankFo Q a ⟩
  sat = PT.∣ Q , (qQ ,
          PT.∣ x ,
            PT.∣ r , (hpr , (xa , PT.∣ P537.approx-carve a oa x xa ∣₁)) ∣₁
          ∣₁) ∣₁

-- =====================================================================
-- 4.  THE CARVE, AT ONE NAME.  `[LJ-1.524]` measured what two spellings
--     of the carve cost (lj-1.524-report.md, section 3: two runs killed
--     at ten and at eight minutes).  So `G` below is `P529.Carve.G a oa`
--     and every type in sections 5 and 6 says `G`.
--
--     `Gmem` is the separation equation at that one name.  Its type
--     ascription is the ONE place where `fst (rank-graph Q a bnd)` and
--     `G` are compared, and it is compared at `_∈ˢ_` and not inside a
--     satisfaction predicate.
-- =====================================================================

module Dom (a : S) (oa : IsOrd (fst a)) where

  Q : S
  Q = P529.ordQ a oa

  bnd : S
  bnd = P529.Bound′.bnd a oa

  G : S
  G = P529.Carve.G a oa

  Gmem : (w : S)
       → (w ∈ˢ G) ≡ ((w ∈ˢ bnd) ⊓ ((w ∷ []) ⊨ P521.rankFo Q a))
  Gmem = snd (P529.rank-graph Q a bnd)

  into : (w : S) → ⟨ w ∈ˢ bnd ⟩ → ⟨ (w ∷ []) ⊨ P521.rankFo Q a ⟩
       → ⟨ w ∈ˢ G ⟩
  into w hb hs = subst ⟨_⟩ (sym (Gmem w)) (hb , hs)

  -- ---------------------------------------------------------------
  -- 4.1  THE BOUND HALF.  `[LJ-1.529]`'s `below` is stated at
  --      `swo-rank′ w (fiber (fst a) mx .fst)`; `rank-at′-val`
  --      (Probe521.agda:438-442) is the equation that carries it to
  --      `rank-at′`.  This is `[LJ-1.529]`'s own step for `rank-in-C`
  --      (Probe529.agda:261-266) at the bound instead of the codomain.
  -- ---------------------------------------------------------------


_check : (a : S) (oa : IsOrd (fst a)) → S
_check a oa = Dom.G a oa
