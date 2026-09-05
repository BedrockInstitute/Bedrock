{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.575] THE `TFacts` VALUE.  THERE IS NONE, AT ANY FRAME.
--
-- D-10 STAGE, AND IT IS THE WHOLE RESULT.  The brief asks for one
-- `TFacts` value at `KValue`'s frame and says: if the uncovered fields
-- cannot be supplied, the record cannot be built, name them and stop.
-- They cannot, and the reason is stronger than "not supplied": THREE
-- OF THE FIELDS ARE FALSE, at every frame, with no hypothesis at all.
--
-- `[LJ-1.71]` shipped a module whose telescope was uninhabited at EVERY
-- frame (archive/dev/LJ-dispatch-index.md:135).  `TFacts` is that same
-- defect, and section 1 is the machine's word for it.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.  Nothing lands in
-- src/.  I postulate nothing.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-575.Probe575 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans
        ; isTransV )
open import L.Axioms.Basic {ℓ} using ( isL-Lset; LsetS; finSet )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; tmValAt; tmValAt-con; consAtL; envSetAt )
open import L.Coding.Environment {ℓ} using ( env )
open import L.Coding.EnvSupply {ℓ} lem
  using ( module SupplyEnv; module SupplyMerge; module Fact )
open import L.Condensation {ℓ} lem using ( module KValue; module KFactsNS )
open import L.Condensation.TwelveAgree {ℓ} lem using ( TFacts )
open import L.Condensation.LowerAgree {ℓ} lem using ( LFacts )
open import L.Condensation.UpperAgree {ℓ} lem using ( UFacts )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅ )
open InfinitySet {ℓ} using ( #_; sucV; ω )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ
open KFactsNS
open KFacts

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The K slot at the record's own index, named once.
Kat : {n : ℕ} → Fin (5 + n) → S ^ (11 + n) → S
Kat K γ' = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

-- =====================================================================
-- 1.  THE SHAPE, REFUTED ONCE.
--
-- `tmValAt t e v` is a DISJUNCTION
--   (src/L/Coding/Model.lagda.md:1701-1702):
--
--     ∃̇ (tagAtL (suc t) 1 zero ∧̇ appAt (suc e) zero (suc v)) ∨̇ tagAtL t 0 v
--
-- The right disjunct, `tagAtL t 0 v`, says ONLY `T ≡ pr (# 0) Val`.  It
-- asks for NO membership: not of the value, not of the environment.
--
-- THE TREE'S OWN HONEST FORM KNOWS THIS.  `Fact.tmValK`
-- (src/L/Coding/EnvSupply.lagda.md:575-579) takes TWO memberships,
-- `eK` and `tK`, and its `conCase` (:589-592) is EXACTLY where `tK` is
-- spent: from `T ≡ pr (# 0) Val` and `T ∈ K` it reads `Val ∈ K` off
-- `prK`.  WITHOUT `tK` there is nothing to read.
--
-- So a field of this shape that quantifies over the TAG slot and takes
-- no `tK` is refuted by ONE instance: put the K slot itself in the
-- value cell, and `prʟ (numeralL 0)` of it in the tag cell.  The field
-- then returns `K ∈ K`, and `∈-irrefl` (src/V/Hierarchy.lagda.md:155)
-- closes it.
--
-- NO FRAME IS NAMED IN THIS SECTION.  `γ` and `Ks` are free, so the
-- refutation holds at `KValue`'s frame and at every other.
-- =====================================================================

module Shape {m : ℕ} (γ : S ^ m) (Ks : S) where

  -- The tag cell, built so the `Con` disjunct holds at `Ks`.
  tag : S
  tag = prʟ (numeralL 0) Ks

  tagEq : fst tag ≡ pr (# 0) (fst Ks)
  tagEq = prʟ-fst (numeralL 0) Ks
        ∙ cong (λ w → pr w (fst Ks)) (numeralL-fst 0)

  -- `valV`'s shape: nine free cells, tag at 6, environment at 2,
  -- value at 1 (src/L/Condensation/TwelveAgree.lagda.md:244-249).
  ValVShape : Type (ℓ-suc ℓ)
  ValVShape = (E yc b a ar c z v w : S)
            → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                        (suc (suc zero))
                        (suc zero) ⟩
            → ⟨ fst v ∈ fst Ks ⟩

  valV-absurd : ValVShape → Empty.⊥
  valV-absurd f = ∈-irrefl (fst Ks)
    (f Ks Ks Ks tag Ks Ks Ks Ks Ks
      (tmValAt-con (suc (suc (suc (suc (suc (suc zero))))))
                   (suc (suc zero))
                   (suc zero)
                   (Ks ∷ Ks ∷ Ks ∷ Ks ∷ Ks ∷ Ks ∷ tag ∷ Ks ∷ Ks ∷ γ)
                   tagEq))

  -- `valW`'s shape: tag at 5, environment at 2, value at 0
  -- (src/L/Condensation/TwelveAgree.lagda.md:250-255).
  ValWShape : Type (ℓ-suc ℓ)
  ValWShape = (E yc b a ar c z v w : S)
            → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                tmValAt (suc (suc (suc (suc (suc zero)))))
                        (suc (suc zero))
                        zero ⟩
            → ⟨ fst w ∈ fst Ks ⟩

  valW-absurd : ValWShape → Empty.⊥
  valW-absurd f = ∈-irrefl (fst Ks)
    (f Ks Ks tag Ks Ks Ks Ks Ks Ks
      (tmValAt-con (suc (suc (suc (suc (suc zero)))))
                   (suc (suc zero))
                   zero
                   (Ks ∷ Ks ∷ Ks ∷ Ks ∷ Ks ∷ tag ∷ Ks ∷ Ks ∷ Ks ∷ γ)
                   tagEq))

  -- `wKfact`'s shape: tag at 6, environment at 1, value at 0
  -- (src/L/Condensation/TwelveAgree.lagda.md:256-261).
  WKShape : Type (ℓ-suc ℓ)
  WKShape = (E ya yc b a ar c z w : S)
          → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
          → ⟨ fst w ∈ fst Ks ⟩

  wKfact-absurd : WKShape → Empty.⊥
  wKfact-absurd f = ∈-irrefl (fst Ks)
    (f Ks Ks Ks Ks tag Ks Ks Ks Ks
      (tmValAt-con (suc (suc (suc (suc (suc (suc zero))))))
                   (suc zero)
                   zero
                   (Ks ∷ Ks ∷ Ks ∷ Ks ∷ Ks ∷ Ks ∷ tag ∷ Ks ∷ Ks ∷ γ)
                   tagEq))

-- =====================================================================
-- 2.  THE THREE RECORDS, REFUTED.
--
-- Each line below is ONE projection off the master's own record fed to
-- ONE shape lemma.  Nothing is restated: if a field's type ever drifts
-- from the shape, the line stops checking.  This is `[LJ-1.545]`'s
-- `statement-matches` device used to REFUTE rather than to certify.
--
-- SIX FIELDS ACROSS THREE RECORDS, and each of the six alone is enough.
-- =====================================================================

tfacts-absurd : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → Empty.⊥
tfacts-absurd {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  Shape.valV-absurd γ' (Kat K γ') (TFacts.valV tf)

tfacts-absurd-valW : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → Empty.⊥
tfacts-absurd-valW {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  Shape.valW-absurd γ' (Kat K γ') (TFacts.valW tf)

tfacts-absurd-wKfact : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → Empty.⊥
tfacts-absurd-wKfact {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  Shape.wKfact-absurd γ' (Kat K γ') (TFacts.wKfact tf)

-- THE C-42 SWEEP, MEASURED AND NOT ASSUMED: the same shape is in the
-- two partial blocks the master splits `TFacts` into
-- (src/L/Condensation/TwelveAgree.lagda.md:403-481), so refuting
-- `TFacts` does not exhaust the defect.

lfacts-absurd : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ : S ^ (11 + n))
  → LFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ
  → Empty.⊥
lfacts-absurd {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ lf =
  Shape.valV-absurd γ (Kat K γ) (LFacts.valV lf)

lfacts-absurd-valW : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ : S ^ (11 + n))
  → LFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ
  → Empty.⊥
lfacts-absurd-valW {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ lf =
  Shape.valW-absurd γ (Kat K γ) (LFacts.valW lf)

ufacts-absurd : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ : S ^ (11 + n))
  → UFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ
  → Empty.⊥
ufacts-absurd {n} N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ uf =
  Shape.wKfact-absurd γ (Kat K γ) (UFacts.wKfact uf)

-- =====================================================================
-- 3.  W3, THE WIDEST UNMEASURED TERM AS THE BRIEF NAMES IT:
--     whether ALL FOUR predecessors' hypotheses hold together at ONE
--     frame, INHABITED.
--
-- IT RAN AFTER SECTION 1 AND NOT BEFORE IT, AND THAT IS DELIBERATE.
-- The brief orders D-10 before any Agda and W3 first among the Agda.
-- D-10 settled the target here, so W3 can no longer be the guard the
-- brief wants it to be.  It is still a measurement the next brief
-- needs, so it is here, and it is honest about what it now proves:
-- the four collections COMPOSE.  It does not make the record true.
--
-- THE FIVE FREE CELLS ARE PINNED, and pinning them is what makes this
-- an inhabitation rather than another hypothesis.  `[LJ-1.553]`'s
-- `graphK` reads cell 1 and its report says that cell is FREE
-- (agents/tasks/LJ-1-553/lj-1.553-report.md:47-49), so `[LJ-1.553]`
-- assumed the membership and did not pay it.  Here cell 1 is
-- `numeralL 0` and `KFacts.numK0` pays it from the tree.
-- =====================================================================

module W3
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ
  module SM = SupplyMerge lam ordλ succλ ∅∈λ

  -- `[LJ-1.551]`'s frame, with the five free cells PINNED to `numeralL 0`.
  γ★ : Vec S 20
  γ★ = SE.B₀ ∷ numeralL 0 ∷ numeralL 0 ∷ numeralL 0
     ∷ numeralL 0 ∷ numeralL 0 ∷ KV.Kenv

  -- The empty family and the environment over it, as `[LJ-1.563]` built
  -- them (agents/tasks/LJ-1-563/Probe563.agda:96-108).
  g₀ : Fin 0 → V ℓ
  g₀ ()

  env₀∈ : ⟨ env {0} g₀ ∈ Lset lam ⟩
  env₀∈ = SM.finSetK 0 (λ i → pr (# (toℕ i)) (g₀ i)) (λ ())

  z₀ : S
  z₀ = env {0} g₀
     , isL-trans {x = Lset lam} {y = env {0} g₀} env₀∈ (isL-Lset lam ordλ)

  -- THE UNION, AT ONE FRAME, IN ONE VALUE.
  --
  --   (551) the `EnvSupply` side lands at the record's own `K` slot.
  --   (553) the supplied membership at cell 1, PAID and not assumed.
  --   (563) the environment witness, the two memberships, and the
  --         truncated numeral arity.
  four-hypotheses-hold-together :
      ( (yc b a ar c E : S)
        → ∥ Σ[ p ∈ ℕ ] (fst ar ≡ # p) ∥₁
        → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ★) ⊨
            envSetAt zero (suc (suc (suc (suc zero))))
                      (suc (suc (suc (suc (suc (suc zero)))))) ⟩
        → ⟨ fst E ∈ fst (Kat KV.iK γ★) ⟩ )
    × ⟨ fst (lookup (suc zero) γ★) ∈ fst (Kat KV.iK γ★) ⟩
    × (Σ[ k ∈ ℕ ] Σ[ g ∈ (Fin k → V ℓ) ] (fst z₀ ≡ env g))
    × ( ⟨ fst z₀ ∈ fst (Kat KV.iK γ★) ⟩
      × ⟨ fst (numeralL 0) ∈ fst (Kat KV.iK γ★) ⟩ )
    × ∥ Σ[ p ∈ ℕ ] (fst (numeralL 0) ≡ # p) ∥₁
  four-hypotheses-hold-together =
      (λ yc b a ar c E arNum h →
        SE.envK-gen (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ★)
          zero (suc (suc (suc (suc zero))))
          (suc (suc (suc (suc (suc (suc zero))))))
          refl arNum h)
    , KV.facts .numK0
    , (0 , (g₀ , refl))
    , ( env₀∈ , KV.facts .numK0 )
    , ∣ 0 , numeralL-fst 0 ∣₁

four-hypotheses-hold-together = W3.four-hypotheses-hold-together

-- =====================================================================
-- 4.  WHAT THE REPAIR COSTS, MEASURED.
--
-- The brief says a NO-GO that names the uncovered fields tells the
-- mathematician what the record still costs, "which is a number nobody
-- has".  Here is the number for the three FALSE fields: TWO
-- MEMBERSHIPS EACH, ALREADY IN THE TREE, AND NO NEW LEMMA.
--
-- `Fact.tmValK` (src/L/Coding/EnvSupply.lagda.md:575-592) is already
-- slot-generic in the vector length and in the three slots, so the
-- three repaired fields are three applications of it and nothing else.
-- The record does not need a new proof.  IT NEEDS ITS HYPOTHESES BACK.
-- =====================================================================

record ThreeRepaired {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    valV+ : (E yc b a ar c z v w : S)
          → ⟨ fst z ∈ fst (Kat K γ') ⟩                        -- RESTORED
          → ⟨ fst a ∈ fst (Kat K γ') ⟩                        -- RESTORED
          → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc (suc zero))
                      (suc zero) ⟩
          → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))))
                            (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    valW+ : (E yc b a ar c z v w : S)
          → ⟨ fst z ∈ fst (Kat K γ') ⟩                        -- RESTORED
          → ⟨ fst b ∈ fst (Kat K γ') ⟩                        -- RESTORED
          → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
              tmValAt (suc (suc (suc (suc (suc zero)))))
                      (suc (suc zero))
                      zero ⟩
          → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                            (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    wKfact+ : (E ya yc b a ar c z w : S)
            → ⟨ fst z ∈ fst (Kat K γ') ⟩                      -- RESTORED
            → ⟨ fst a ∈ fst (Kat K γ') ⟩                      -- RESTORED
            → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                        (suc zero)
                        zero ⟩
            → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))))))
                              (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩

-- `statement-matches`: Agda's word that the three types above ARE the
-- master's own, weakened by the two RESTORED memberships and by nothing
-- else.  IT IS A STATEMENT CERTIFICATE AND IT CAN NEVER BE CALLED,
-- because section 2 shows its argument type has no value.  That is
-- exactly what it is here to certify.
statement-matches : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → ThreeRepaired {n} K γ'
statement-matches N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf = record
  { valV+ = λ E yc b a ar c z v w _ _ → TFacts.valV tf E yc b a ar c z v w
  ; valW+ = λ E yc b a ar c z v w _ _ → TFacts.valW tf E yc b a ar c z v w
  ; wKfact+ = λ E ya yc b a ar c z w _ _ → TFacts.wKfact tf E ya yc b a ar c z w }

-- THE THREE, REPAIRED, AT A GENERIC `K` AND A GENERIC `γ'` (W2).
module Repair {n : ℕ} (K : Fin (5 + n)) (γ' : S ^ (11 + n))
  (Ktr : isTransV (fst (Kat K γ'))) where

  module F = Fact (Kat K γ') Ktr

  three : ThreeRepaired {n} K γ'
  three = record
    { valV+ = λ E yc b a ar c z v w zK aK h →
        F.tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc zero))))))
          (suc (suc zero))
          (suc zero) zK aK h
    ; valW+ = λ E yc b a ar c z v w zK bK h →
        F.tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc zero)))))
          (suc (suc zero))
          zero zK bK h
    ; wKfact+ = λ E ya yc b a ar c z w zK aK h →
        F.tmValK (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')
          (suc (suc (suc (suc (suc (suc zero))))))
          (suc zero)
          zero zK aK h }

-- AT `KValue`'s FRAME, WITH `Ktr` PAID FROM THE TREE, exactly as
-- `[LJ-1.553]` pays it (agents/tasks/LJ-1-553/Probe553.agda:346-350).
module RepairAtFrame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  γ‡ : (g1 g2 g3 g4 g5 : S) → Vec S 20
  γ‡ g1 g2 g3 g4 g5 = SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv

  Ktr‡ : (g1 g2 g3 g4 g5 : S)
       → isTransV (fst (Kat KV.iK (γ‡ g1 g2 g3 g4 g5)))
  Ktr‡ g1 g2 g3 g4 g5 = layer-trans (Lset-layer lam)

  three-repaired-collected : (g1 g2 g3 g4 g5 : S)
    → ThreeRepaired {n = 9} KV.iK (γ‡ g1 g2 g3 g4 g5)
  three-repaired-collected g1 g2 g3 g4 g5 =
    Repair.three {n = 9} KV.iK (γ‡ g1 g2 g3 g4 g5) (Ktr‡ g1 g2 g3 g4 g5)

three-repaired-collected = RepairAtFrame.three-repaired-collected

-- =====================================================================
-- 5.  THE OBLIGATION.
--
--     tfacts-value : <a `TFacts` value at `KValue`'s frame>
--
-- IT IS NOT HERE, AND IT IS NOT HERE ON PURPOSE.  Section 2 proves
-- `TFacts ... → Empty.⊥` with no hypothesis, so any term of that type
-- would have to be a `postulate`, a hole or a lie.  The Boundary makes
-- a stop a deliverable, and the coder's own clause says a `NO-GO` is
-- stated by writing `review-of-*.md`, which I did:
--
--     agents/tasks/LJ-1-575/review-of-tfacts-value.md
--
-- THE FRAME IS NOT THE PROBLEM AND NO OTHER FRAME HELPS.  `Shape` above
-- names no frame: `γ` and `Ks` are free, so a `TFacts` value is
-- impossible at `KValue`'s frame, at the abstract frame, and at every
-- frame anyone builds later.
-- =====================================================================

-- =====================================================================
-- 6.  THREE OF THE "UNSUPPLIED" FIELDS ARE FREE, AND THE CENSUS MISSED
--     THEM BECAUSE IT LOOKED FOR A SUPPLIER AND NOT FOR A FRAME.
--
-- `[LJ-1.512]` reported five fields with no honest form anywhere
-- (agents/tasks/LJ-1-512/lj-1.512-report.md:47-49): `codesK`,
-- `codesK-un`, `t0eq`, `t1eq` and `t0K`.  Three of the five need no
-- supplier at all.  `t0` and `t1` are FRAME INDICES the instantiator
-- chooses (src/L/Condensation/TwelveAgree.lagda.md:130), and at
-- `t0 := KV.i0`, `t1 := KV.i1` the three are `KFacts`'s own `tagEq0`,
-- `tagEq1` and `numK0`, which `KValue` already delivers
-- (src/L/Condensation.lagda.md:7411-7425).
--
-- THIS DOES NOT RESCUE THE RECORD.  Section 2 refutes three other
-- fields.  It moves the count of genuinely open fields, which is what
-- the next brief needs.
-- =====================================================================

record TagFields {n : ℕ} (t0 t1 K : Fin (5 + n)) (γ' : S ^ (11 + n))
  : Type (ℓ-suc ℓ) where
  field
    t0eq : fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ') ≡ fst (numeralL 0)
    t1eq : fst (lookup (suc (suc (suc (suc (suc (suc t1)))))) γ') ≡ fst (numeralL 1)
    t0K : ⟨ fst (lookup (suc (suc (suc (suc (suc (suc t0)))))) γ')
            ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

tag-statement-matches : {n : ℕ}
    (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K : Fin (5 + n))
    (γ' : S ^ (11 + n))
  → TFacts N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ'
  → TagFields {n} t0 t1 K γ'
tag-statement-matches N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 K γ' tf =
  record { t0eq = TFacts.t0eq tf ; t1eq = TFacts.t1eq tf ; t0K = TFacts.t0K tf }

module TagsAtFrame
  (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩)
  (gam : V ℓ) (ordγ : IsOrd gam) (γ∈λ : ⟨ gam ∈ lam ⟩)
  (ω∈σ : ⟨ ω ∈ sucV gam ⟩) where

  module KV = KValue lam ordλ succλ ∅∈λ gam ordγ γ∈λ
  module SE = SupplyEnv lam ordλ succλ ∅∈λ gam ordγ γ∈λ ω∈σ

  γ‡ : (g1 g2 g3 g4 g5 : S) → Vec S 20
  γ‡ g1 g2 g3 g4 g5 = SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv

  -- THE THREE, PAID FROM `KValue` AND NOTHING ELSE.
  tag-fields-collected : (g1 g2 g3 g4 g5 : S)
    → TagFields {n = 9} KV.i0 KV.i1 KV.iK (γ‡ g1 g2 g3 g4 g5)
  tag-fields-collected g1 g2 g3 g4 g5 = record
    { t0eq = KV.facts .tagEq0
    ; t1eq = KV.facts .tagEq1
    ; t0K = KV.facts .numK0 }

tag-fields-collected = TagsAtFrame.tag-fields-collected
