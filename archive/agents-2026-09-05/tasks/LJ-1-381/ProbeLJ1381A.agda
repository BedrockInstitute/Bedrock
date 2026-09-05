{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.381] probe.  PRICE THE φ₀ EXTRACTION.
--
-- THE QUESTION: [LJ-1.378] named `Extraction` (ProbeLJ1378A.agda,
-- Comp module) as the φ₀-side obligation and inventoried six legs,
-- four called mechanical or delivered and two called tedious or
-- unwritten.  Nobody has priced the factor.  This file builds the
-- extraction as a TERM at the honest leaf instantiation, so every leg
-- returns a line count instead of an adjective.
--
-- WHAT IS BUILT, leg by leg:
--   * the `embed`-`renameFo` commutation, GENERIC in both carriers
--     (the leg called unwritten, estimated at 12 lines): mapTm-ren,
--     mapFo-ren, emb-ren;
--   * the fourteen-fold `∃̇` unfold as ONE iterated elimination over
--     closeK 14's fully reduced spine (ex-14);
--   * the conjunct projection, one `.snd`;
--   * the rename-back along ρ through the delivered `⊨-rename`, with
--     `Agrees` as five cases: four `refl` and one `lookup-inj`;
--   * the un-erase folded into the DIALECT EQUATION
--     `embed base ≡ levelRow`, tried as `refl` (both dialects are
--     verbatim copies; the run decides);
--   * `extr`, the extraction as a term, with the Σ TRUNCATED: the
--     `∃̇` satisfaction is the truncated existential, so [LJ-1.378]'s
--     untruncated Σ is refused by the eliminator (Control381A.agda
--     measures the refusal).
--
-- The leaf contents ψs ψa are PINNED at `embed (Cnt.erase leaf)` of
-- LevelHood's own DefBodyB leaves, the same towers ProbeLJ1241A
-- instantiated: at an unrelated leaf the extraction statement is
-- false, so the honest price is measured at the matching leaf.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∃̇∈; ∀̇∈ )
import FOL.Absoluteness
open import FOL.Manipulation.Renaming using ( renameFo; renameTm; liftρ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm; embed )
open import FOL.Manipulation.Parameters using ( countFo )
import FOL.Count
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆ ) renaming ( module InfinitySet to Inf )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )
open import Cubical.Data.Vec using ( Vec; lookup; _∷_; []; _++_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )
import Cubical.Data.Empty as Empty

module LJ-1-381.ProbeLJ1381A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒟ₒ; 𝒮ʟ )
open Inf using ( #_; sucV )

import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A
import LJ-1-297.ProbeLJ1297C {ℓ} as P1297C
import LJ-1-238.GenSequence
import LJ-1-304.ProbeLJ1304A {ℓ} lem as P1304
open import L.Condensation {ℓ} lem using ( DefBodyB )

module A = P184.Ambient
module P1241 = P1297A.P1241
open P1297C using ( absFull )

-- The ambient-class reading and the renaming lemma, the instances
-- ProbeLJ1378A/B carried.  SC is taken as AbsF.SM itself: SC and
-- A.R.SC are definitionally equal (P1297A.ambient≡ is refl), but the
-- elaborator defers the Sigma-lambda comparison, and stating the
-- carrier as SM keeps every `⊨` at its own reading.
module AbsF = FOL.Absoluteness.Single 𝒮ᵥ P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
open AbsF using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

SC : Type (ℓ-suc ℓ)
SC = AbsF.SM

module RenSat = FOL.Manipulation.Renaming.Sat
  (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ P1297A.Full) id

module GS = LJ-1-238.GenSequence {ℓ} lem P1297A.Full
  (λ {x} {y} → P1297A.Full-tr {x} {y})
  (λ k → # k , tt*) (λ k → refl)
  (λ a b → ⁅ fst a , fst b ⁆ , tt*) (λ a b → refl)
  (λ a → sucV (fst a) , tt*) (λ a → refl)

-- The class-carrier count module, ProbeLJ1241A's own instance.
module CS = hPropStructure 𝒮ʟ
module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S

-- =====================================================================
-- LEG 1a (shared with every other pinned formula): the generic
-- mapFo/renameFo commutation.  Constants do not move under renaming,
-- variables do not move under relabelling: both term cases are refl,
-- every formula case is a congruence.
-- =====================================================================
mapTm-ren : {K K' : Type (ℓ-suc ℓ)} (f : K → K')
  {n m : ℕ} (ρ : Fin n → Fin m) (t : Term K n)
  → mapTm f (renameTm ρ t) ≡ renameTm ρ (mapTm f t)
mapTm-ren f ρ (con k) = refl
mapTm-ren f ρ (var i) = refl

mapFo-ren : {K K' : Type (ℓ-suc ℓ)} (f : K → K')
  {n m : ℕ} (ρ : Fin n → Fin m) (φ : Formula K n)
  → mapFo f (renameFo ρ φ) ≡ renameFo ρ (mapFo f φ)
mapFo-ren f ρ (t ∈̇ u) =
  cong₂ _∈̇_ (mapTm-ren f ρ t) (mapTm-ren f ρ u)
mapFo-ren f ρ (t ≐ u) =
  cong₂ _≐_ (mapTm-ren f ρ t) (mapTm-ren f ρ u)
mapFo-ren f ρ (φ ∧̇ ψ) =
  cong₂ _∧̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
mapFo-ren f ρ (φ ∨̇ ψ) =
  cong₂ _∨̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
mapFo-ren f ρ (φ ⇒̇ ψ) =
  cong₂ _⇒̇_ (mapFo-ren f ρ φ) (mapFo-ren f ρ ψ)
mapFo-ren f ρ (¬̇ φ)   = cong ¬̇_ (mapFo-ren f ρ φ)
mapFo-ren f ρ ⊤̇       = refl
mapFo-ren f ρ ⊥̇       = refl
mapFo-ren f ρ (∃̇ φ)   = cong ∃̇_ (mapFo-ren f (liftρ ρ) φ)
mapFo-ren f ρ (∀̇ φ)   = cong ∀̇_ (mapFo-ren f (liftρ ρ) φ)
mapFo-ren f ρ (∀̇∈ t φ) =
  cong₂ ∀̇∈ (mapTm-ren f ρ t) (mapFo-ren f (liftρ ρ) φ)
mapFo-ren f ρ (∃̇∈ t φ) =
  cong₂ ∃̇∈ (mapTm-ren f ρ t) (mapFo-ren f (liftρ ρ) φ)

-- THE COMMUTATION, at embed: `embed (renameFo ρ φ) ≡ renameFo ρ
-- (embed φ)`, one instance of the generic lemma.
emb-ren : {n m : ℕ} (ρ : Fin n → Fin m) (φ : Formula (⊥* {ℓ-suc ℓ}) n)
  → embed {K = SC} (renameFo ρ φ) ≡ renameFo ρ (embed {K = SC} φ)
emb-ren ρ φ = mapFo-ren Empty.rec* ρ φ

-- =====================================================================
-- LEG 1b: the fourteen-fold `∃̇` unfold, as one iterated elimination
-- over the reduced spine.  closeK 14 χ reduces to fourteen nested
-- `∃̇`; each satisfaction layer is the truncated existential, so each
-- peel is one `PT.rec` and the witnesses collect in spine order
-- (last peeled at slot zero).
-- =====================================================================
closeK : {K : Type (ℓ-suc ℓ)} {n : ℕ} (k : ℕ)
       → Formula K (k + n) → Formula K n
closeK zero    φ = φ
closeK (suc k) φ = closeK k (∃̇ φ)

ex-14 : (χ : Formula SC 16) (γ : Vec SC 2)
      → ⟨ γ ⊨ closeK 14 χ ⟩
      → ∥ (Σ[ pre ∈ Vec SC 14 ] ⟨ (pre ++ γ) ⊨ χ ⟩) ∥₁
ex-14 χ γ h =
  PT.rec squash₁ (λ (a13 , h13) →
  PT.rec squash₁ (λ (a12 , h12) →
  PT.rec squash₁ (λ (a11 , h11) →
  PT.rec squash₁ (λ (a10 , h10) →
  PT.rec squash₁ (λ (a9 , h9) →
  PT.rec squash₁ (λ (a8 , h8) →
  PT.rec squash₁ (λ (a7 , h7) →
  PT.rec squash₁ (λ (a6 , h6) →
  PT.rec squash₁ (λ (a5 , h5) →
  PT.rec squash₁ (λ (a4 , h4) →
  PT.rec squash₁ (λ (a3 , h3) →
  PT.rec squash₁ (λ (a2 , h2) →
  PT.rec squash₁ (λ (a1 , h1) →
  PT.rec squash₁ (λ (a0 , h0) →
    ∣ (a0 ∷ a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7
       ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ []) , h0 ∣₁)
    h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h

-- =====================================================================
-- THE PINNED LEAVES.  LevelHood's own DefBodyB applications at
-- ProbeLJ1241A's towers, erased and embedded: the leaf content φ₀
-- actually carries, at the ambient carrier.
-- =====================================================================
leafS : Formula CS.S 25
leafS = DefBodyB {17}
  (suc zero)
  (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {6} {11}  (P1241.fin-suc 5)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {7} {10}  (P1241.fin-suc 6)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {8} {9}   (P1241.fin-suc 7)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {9} {8}   (P1241.fin-suc 8)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {10} {7}  (P1241.fin-suc 9)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {11} {6}  (P1241.fin-suc 10)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {12} {5}  (P1241.fin-suc 11)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {13} {4}  (P1241.fin-suc 12)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {14} {3}  (P1241.fin-suc 13)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {15} {2}  (P1241.fin-suc 14)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {16} {1}  (P1241.fin-suc 15)))))))
  (suc (suc (suc (suc (suc (P1241.fin-suc 16))))))
  (suc (suc (suc (suc (suc zero)))))
  (suc (suc (suc (suc (suc zero)))))

leafA : Formula CS.S 27
leafA = DefBodyB {19}
  (suc zero)
  (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {6} {13}  (P1241.fin-suc 5)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {7} {12}  (P1241.fin-suc 6)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {8} {11}  (P1241.fin-suc 7)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {9} {10}  (P1241.fin-suc 8)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {10} {9}  (P1241.fin-suc 9)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {11} {8}  (P1241.fin-suc 10)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {12} {7}  (P1241.fin-suc 11)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {13} {6}  (P1241.fin-suc 12)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {14} {5}  (P1241.fin-suc 13)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {15} {4}  (P1241.fin-suc 14)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {16} {3}  (P1241.fin-suc 15)))))))
  (suc (suc (suc (suc (suc (P1241.inject+ {17} {2}  (P1241.fin-suc 16)))))))
  (suc (suc (suc (suc (suc zero)))))
  (suc (suc (suc (suc (suc zero)))))

ψs* : Formula SC 25
ψs* = embed (Cnt.erase leafS refl)

ψa* : Formula SC 27
ψa* = embed (Cnt.erase leafA refl)

-- =====================================================================
-- THE EXTRACTION, at the pinned leaves.  The Def-step trio stays a
-- parameter (the ambient rows are generic in it), exactly as
-- ProbeLJ1378A's Comp telescope.
-- =====================================================================
module Comp
  (DefAt : ∀ {n} → Fin n → Fin n → Formula SC n)
  (DefAt-in : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n)
            → fst (lookup w γ) ≡ fst X
            → fst (lookup u γ) ≡ 𝒟ₒ (fst X)
            → ⟨ γ ⊨ DefAt u w ⟩)
  (DefAt-out : (X : SC) → ∀ {n} (u w : Fin n) (γ : Vec SC n) → GS.DefOK X
             → fst (lookup w γ) ≡ fst X
             → ⟨ γ ⊨ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst X))
  where

  module S304 = P1304.Supply DefAt DefAt-in DefAt-out

  -- THE GRAPH ROW and THE LEVEL ROW, ProbeLJ1378A's definitions at
  -- the pinned leaves.
  graphRow : Formula SC 17
  graphRow =
    ∃̇∈ (var (suc (suc (suc (suc zero)))))
      (S304.approxBndAt ψa* zero
         (suc (suc (suc (suc zero))))
         (suc (suc (suc (suc (suc zero)))))
      ∧̇ S304.stepBndAt ψs* (suc zero)
         (suc (suc (suc (suc zero)))) zero
         (suc (suc (suc (suc (suc zero))))))

  levelRow : Formula SC 16
  levelRow =
    ∃̇∈ (var (suc (suc (suc zero))))
      (graphRow ∧̇ (var (suc (suc zero)) ≐ var zero))

  -- [LJ-1.378]'s statement, kept for the record: the Σ is NOT
  -- truncation-compatible with the `∃̇` satisfaction
  -- (Control381A.agda measures the refusal).
  Extraction : (γ : Vec SC 2) → Type (ℓ-suc ℓ)
  Extraction γ =
    ⟨ A.ambient γ (embed P1241.φ₀) ⟩
      → Σ[ frame ∈ SC ^ 16 ]
          ( (lookup (suc zero) frame ≡ lookup zero γ)
          × (lookup (suc (suc zero)) frame ≡ lookup (suc zero) γ)
          × ⟨ frame ⊨ levelRow ⟩ )

  -- THE HONEST FORM: the Σ truncated, consumable by `comp` through
  -- one `PT.rec` at the propositional conclusion.
  ExtractionT : (γ : Vec SC 2) → Type (ℓ-suc ℓ)
  ExtractionT γ =
    ⟨ A.ambient γ (embed P1241.φ₀) ⟩
      → ∥ Σ[ frame ∈ SC ^ 16 ]
           ( (lookup (suc zero) frame ≡ lookup zero γ)
           × (lookup (suc (suc zero)) frame ≡ lookup (suc zero) γ)
           × ⟨ frame ⊨ levelRow ⟩ ) ∥₁

  -- THE DIALECT EQUATION: erase and embed of the class `levelHoodB`
  -- against the ambient `levelRow` at the pinned leaves.  Tried as
  -- `refl`; the run decides.
  dia : embed P1241.base ≡ levelRow
  dia = refl

  -- LEG 5's slot arithmetic, one helper: `inject+` looks up in the
  -- concatenation exactly as in the front part.
  lookup-inj : {m n : ℕ} (i : Fin m) (xs : Vec SC m) (ys : Vec SC n)
             → lookup (P1241.inject+ i) (xs ++ ys) ≡ lookup i xs
  lookup-inj zero    (x ∷ xs) ys = refl
  lookup-inj (suc i) (x ∷ xs) ys = lookup-inj i xs ys

  -- The frame, from the fourteen witnesses in renamed layout
  -- (w, K, δ₀..δ₁₁) and γ's two slots, to the level row's layout
  -- (u, v, g, K, δ₀..δ₁₁): base's own layout, which is why the slot
  -- equations are `refl` at construction.
  frameOf : Vec SC 14 → SC → SC → SC ^ 16
  frameOf (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
           ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g =
    w ∷ v ∷ g ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
      ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []

  -- THE AGREEMENT: renamed layout to base layout along ρ.  Four
  -- cases compute; the fifth is `lookup-inj` at the δ slots.
  ag : (pre : Vec SC 14) (v g : SC)
     → RenSat.Agrees P1241.ρ (pre ++ (v ∷ g ∷ [])) (frameOf pre v g)
  ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
       ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g zero = refl
  ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
       ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g (suc zero) = refl
  ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
       ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g (suc (suc zero)) = refl
  ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
       ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g (suc (suc (suc zero))) = refl
  ag (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
       ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g
      (suc (suc (suc (suc i)))) =
    lookup-inj i (δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
                    ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) (v ∷ g ∷ [])

  fromAmb : ∀ {n} (φ : Formula SC n) (γ : Vec SC n)
          → ⟨ A.ambient γ φ ⟩ → ⟨ γ ⊨ φ ⟩
  fromAmb φ γ = subst ⟨_⟩ (sym (absFull φ γ))

  -- THE EXTRACTION AS A TERM: unfold, project, commute, rename back,
  -- cross the dialect, package.  Six legs, every one a delivered
  -- lemma or a built helper above.  The chain is split into three
  -- explicitly typed steps so each leg is checkable alone.
  step1 : (pre : Vec SC 14) (v g : SC)
        → ⟨ (pre ++ (v ∷ g ∷ [])) ⊨ embed P1241.renamed ⟩
        → ⟨ (pre ++ (v ∷ g ∷ [])) ⊨
               renameFo P1241.ρ (embed P1241.base) ⟩
  -- The commutation instance, named once at a fresh carrier meta:
  -- the path's own endpoints carry their type into the subst, the
  -- pattern ProbeLJ1378B used for its `eq`.
  e : embed {K = SC} P1241.renamed
      ≡ renameFo P1241.ρ (embed {K = SC} P1241.base)
  e = emb-ren P1241.ρ P1241.base

  step1 pre v g h = subst
    (λ ψ → ⟨ (pre ++ (v ∷ g ∷ [])) ⊨ ψ ⟩)
    e h

  step2 : (pre : Vec SC 14) (v g : SC)
        → ⟨ (pre ++ (v ∷ g ∷ [])) ⊨
               renameFo P1241.ρ (embed P1241.base) ⟩
        → ⟨ frameOf pre v g ⊨ embed P1241.base ⟩
  step2 pre v g h = subst ⟨_⟩
    (RenSat.⊨-rename P1241.ρ (embed P1241.base)
       (pre ++ (v ∷ g ∷ [])) (frameOf pre v g) (ag pre v g)) h

  step3 : (frame : SC ^ 16)
        → ⟨ frame ⊨ embed P1241.base ⟩ → ⟨ frame ⊨ levelRow ⟩
  step3 frame h = subst (λ ψ → ⟨ frame ⊨ ψ ⟩) dia h

  -- THE SLOT EQUATIONS, by destructuring: the frame's v and g slots
  -- are γ's own entries, `refl` once the witnesses are spelled out.
  eq1 : (pre : Vec SC 14) (v g : SC)
      → lookup (suc zero) (frameOf pre v g) ≡ v
  eq1 (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
       ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g = refl

  eq2 : (pre : Vec SC 14) (v g : SC)
      → lookup (suc (suc zero)) (frameOf pre v g) ≡ g
  eq2 (w ∷ K ∷ δ₀ ∷ δ₁ ∷ δ₂ ∷ δ₃ ∷ δ₄ ∷ δ₅ ∷ δ₆ ∷ δ₇
       ∷ δ₈ ∷ δ₉ ∷ δ₁₀ ∷ δ₁₁ ∷ []) v g = refl

  extr : (γ : Vec SC 2) → ExtractionT γ

  extr (v ∷ g ∷ []) h =
    PT.rec squash₁ (λ (pre , hbd) →
      ∣ frameOf pre v g , eq1 pre v g , eq2 pre v g ,
        step3 (frameOf pre v g)
          (step2 pre v g (step1 pre v g (hbd .snd))) ∣₁)
      (ex-14 (embed (P1241.pins ∧̇ P1241.renamed)) (v ∷ g ∷ [])
         (fromAmb (embed P1241.φ₀) (v ∷ g ∷ []) h))
