{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.102] probe A: the Mem row restated in tied form.
--
-- MemAgree (src/L/Condensation.lagda.md:4141-4240) takes three of
-- the eleven refuted frame facts: tmKeyK (:4159), entryK (:4165),
-- arSubK (:4167).  This probe restates its telescope with the tied
-- forms read from src/ProbeLJ199A.agda and src/ProbeLJ1100A.agda:
--
--   tmKeyK   -> keyValK : the tag satisfaction pins k
--   entryK   -> entryK-tied : (E : S) -> E ∈ K -> (z x y : S)
--                            -> z ∈ E -> pr x y ∈ z
--                            -> x ∈ K × y ∈ K
--              (the four-step chain, Chain / Extended shape)
--   arSubK   -> arSubK-tied : x ∈ ar -> ar ∈ K -> x ∈ K
--
-- The row's OUT direction does not survive.  The EnvSet transfer
-- (master src/L/Condensation.lagda.md:2771-2874) is copied below as
-- EnvSetTied with the tied facts.  Its out direction (bounded ->
-- machine) has two components.  The first binds z ∈ E, the
-- env-set membership, and bnd→over closes there.  The second runs
-- over→bnd at a z where only z ∈ K is available (envInK z hz), and
-- the tied entryK demands z ∈ E; the second component cannot supply
-- it.  The hole below is that membership, and it stays unsolved
-- (exit 42).  The row's own binders give E ∈ K (EK, :4195) and
-- z ∈ E for the first component only; they carry no transitivity
-- z ∈ E -> z ∈ K, so the alternative ChainZ tie (premise z ∈ K,
-- ProbeLJ199A.ChainZ) would fail at the first component instead.
-- The abort criterion stops at the first failing step, so only the
-- out direction is attempted.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ1102A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( envOverAt; envSetAt; extAt-in-both; appAt; appAt-adequate; prʟ
        ; domAt-intro; domAt-out; domAt-in
        ; svAt-in; svAt-out
        ; valuesInAt-in; valuesInAt-out
        ; tagAtL; tmValAt )
open import L.Condensation {ℓ} lem
  using ( envBndGen; envSetB; arTagPairB; envHypB2T
        ; module Mem )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
open AbsL using ( _^_ )

-- =====================================================================
-- ENVSET, RESTATED IN TIED FORM.  Copy of
-- src/L/Condensation.lagda.md:2771-2874, with the two refuted facts
-- in their tied shapes:
--
-- The three site facts are tied.  The row instantiates the module
-- with its own binders: `entryK-tied E EK` carries the E ∈ K
-- premise (EK at :4195, :4219) and `λ x hx → arSubK-tied ... x hx
-- arK` carries the ar ∈ K premise (arK at :4195, :4215).
--
--   entryK : (z x y : S) -> z ∈ E -> pr x y ∈ z -> x ∈ K × y ∈ K
--   arSubK : (x : S) -> x ∈ ar -> x ∈ K
--   envInK : unchanged
--
-- bnd→over (story -> machine) closes: its z carries z ∈ E from the
-- bounded condition.  over→bnd (machine -> story) also closes when
-- given z ∈ E.  The out direction composes them: the FIRST component
-- binds z ∈ E and closes; the SECOND component has only z ∈ K
-- (envInK z hz) and cannot supply over→bnd's z ∈ E premise.  The
-- hole in `out` below is exactly that membership.
-- =====================================================================
module EnvSetTied {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : (z x y : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
          → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩
            × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where

  φB : Formula S (suc n)
  φB = envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B)

  φ : Formula S (suc n)
  φ = envOverAt zero (suc ar) (suc B)

  -- The app formula at the three-binder frame is the pair membership.
  app3 : (z x y y' : S)
       → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
            appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero) ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app3 z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app3' : (z x y y' : S)
        → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
             appAt (suc (suc (suc zero))) (suc (suc zero)) zero ⟩
        ≡ ⟨ pr (fst x) (fst y') ∈ fst z ⟩
  app3' z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) zero
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app2 : (z x y : S)
       → ⟨ (y ∷ x ∷ z ∷ γ) ⊨ appAt (suc (suc zero)) (suc zero) zero ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app2 z x y =
    cong ⟨_⟩ (appAt-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ z ∷ γ))

  -- STORY TO MACHINE, TIED: the K-bounded condition gives the
  -- machine's unbounded condition.  The z ∈ E premise is threaded
  -- from the bounded condition's first component, and the tied
  -- entryK / arSubK close at every use.  This half is writable.
  bnd→over-tied : (z : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
                → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  bnd→over-tied z z∈E hb =
      svAt-in zero (z ∷ γ)
        (λ x y y' p q →
          let xK = entryK z x y z∈E p .fst
              yK = entryK z x y z∈E p .snd
              y'K = entryK z x y' z∈E q .snd
          in hb .fst x xK y yK y' y'K
               (transport (sym (app3 z x y y')) p)
               (transport (sym (app3' z x y y')) q))
    , domAt-intro zero (suc ar) (z ∷ γ)
        (λ x →
            (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                      (λ { (y , p) →
                        hb .snd .fst x (entryK z x y z∈E p .fst) .fst
                          ∣ y , ( entryK z x y z∈E p .snd
                                , transport (sym (app2 z x y)) p ) ∣₁ })
                      hx)
          , (λ hxar → PT.map
                        (λ { (y , (yK , hp)) → y , transport (app2 z x y) hp })
                        (hb .snd .fst x (arSubK x hxar) .snd hxar)))
    , valuesInAt-in zero (suc B) (z ∷ γ)
        (λ x y p →
          hb .snd .snd .fst x (entryK z x y z∈E p .fst) y (entryK z x y z∈E p .snd)
            (transport (sym (app2 z x y)) p))
    , hb .snd .snd .snd

  -- MACHINE TO STORY, TIED: the machine's condition reaches the
  -- K-bounded one.  Given z ∈ E, every entryK use closes.  This half
  -- is writable; the failure is at the out direction's second
  -- component, which cannot supply the z ∈ E premise.
  over→bnd-tied : (z : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
                → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
  over→bnd-tied z z∈E h =
      (λ x xK y yK y' y'K p q →
        svAt-out zero (z ∷ γ) (h .fst) x y y'
          (transport (app3 z x y y') p) (transport (app3' z x y y') q))
    , (λ x xK →
          (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                    (λ { (y , (yK , hp)) →
                      domAt-out zero (suc ar) (z ∷ γ) (h .snd .fst) x y
                        (transport (app2 z x y) hp) })
                    hx)
        , (λ hxar → PT.rec squash₁
                      (λ { (y , p) →
                        ∣ y , ( entryK z x y z∈E p .snd
                              , transport (sym (app2 z x y)) p ) ∣₁ })
                      (domAt-in zero (suc ar) (z ∷ γ) (h .snd .fst) x hxar)))
    , (λ x xK y yK p →
        valuesInAt-out zero (suc B) (z ∷ γ) (h .snd .snd .fst) x y
          (transport (app2 z x y) p))
    , h .snd .snd .snd

  -- THE OUT DIRECTION, TIED: bounded -> machine.  The first
  -- component binds z ∈ E and closes.  The second component has only
  -- z ∈ K (envInK z hz); the term below cannot be written, and the
  -- hole is exactly the absent z ∈ E.
  out : ⟨ γ ⊨ envSetB E ar B K ⟩ → ⟨ γ ⊨ envSetAt E ar B ⟩
  out h = extAt-in-both E φ γ
    (λ z z∈ → bnd→over-tied z z∈ (h .fst z z∈))
    (λ z hz → h .snd z (envInK z hz) (over→bnd-tied z ? hz))

-- =====================================================================
-- THE ALTERNATIVE TIE, MEASURED.  If the row's tied entryK were the
-- ChainZ shape instead (premise z ∈ K, ProbeLJ199A.ChainZ), the out
-- direction's SECOND component would close (z ∈ K is available as
-- envInK z hz), but its FIRST component would fail: the bounded
-- condition binds z ∈ E, and the row holds no transitivity
-- z ∈ E -> z ∈ K (its telescope has no arityK/transK; source
-- verified at src/L/Condensation.lagda.md:4142-4185).  The hole
-- below is that membership, and it stays unsolved.
-- =====================================================================
module EnvSetTiedChainZ {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
          → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩
            × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where

  φB : Formula S (suc n)
  φB = envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B)

  φ : Formula S (suc n)
  φ = envOverAt zero (suc ar) (suc B)

  app3 : (z x y y' : S)
       → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
            appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero) ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app3 z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app3' : (z x y y' : S)
        → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
             appAt (suc (suc (suc zero))) (suc (suc zero)) zero ⟩
        ≡ ⟨ pr (fst x) (fst y') ∈ fst z ⟩
  app3' z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) zero
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app2 : (z x y : S)
       → ⟨ (y ∷ x ∷ z ∷ γ) ⊨ appAt (suc (suc zero)) (suc zero) zero ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app2 z x y =
    cong ⟨_⟩ (appAt-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ z ∷ γ))

  bnd→over-tied : (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
                → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  bnd→over-tied z zK hb =
      svAt-in zero (z ∷ γ)
        (λ x y y' p q →
          let xK = entryK z x y zK p .fst
              yK = entryK z x y zK p .snd
              y'K = entryK z x y' zK q .snd
          in hb .fst x xK y yK y' y'K
               (transport (sym (app3 z x y y')) p)
               (transport (sym (app3' z x y y')) q))
    , domAt-intro zero (suc ar) (z ∷ γ)
        (λ x →
            (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                      (λ { (y , p) →
                        hb .snd .fst x (entryK z x y zK p .fst) .fst
                          ∣ y , ( entryK z x y zK p .snd
                                , transport (sym (app2 z x y)) p ) ∣₁ })
                      hx)
          , (λ hxar → PT.map
                        (λ { (y , (yK , hp)) → y , transport (app2 z x y) hp })
                        (hb .snd .fst x (arSubK x hxar) .snd hxar)))
    , valuesInAt-in zero (suc B) (z ∷ γ)
        (λ x y p →
          hb .snd .snd .fst x (entryK z x y zK p .fst) y (entryK z x y zK p .snd)
            (transport (sym (app2 z x y)) p))
    , hb .snd .snd .snd

  -- THE FIRST COMPONENT, UNWRITABLE: the bounded condition binds
  -- z ∈ E, and the row has no z ∈ E -> z ∈ K.
  out : ⟨ γ ⊨ envSetB E ar B K ⟩ → ⟨ γ ⊨ envSetAt E ar B ⟩
  out h = extAt-in-both E φ γ
    (λ z z∈ → bnd→over-tied z ? (h .fst z z∈))
    (λ z hz → h .snd z (envInK z hz)
                (over→bnd-tied z (envInK z hz) hz))
    where
    over→bnd-tied : (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
                  → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
    over→bnd-tied z zK h =
        (λ x xK y yK y' y'K p q →
          svAt-out zero (z ∷ γ) (h .fst) x y y'
            (transport (app3 z x y y') p) (transport (app3' z x y y') q))
      , (λ x xK →
            (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                      (λ { (y , (yK , hp)) →
                        domAt-out zero (suc ar) (z ∷ γ) (h .snd .fst) x y
                          (transport (app2 z x y) hp) })
                      hx)
          , (λ hxar → PT.rec squash₁
                        (λ { (y , p) →
                          ∣ y , ( entryK z x y zK p .snd
                                , transport (sym (app2 z x y)) p ) ∣₁ })
                        (domAt-in zero (suc ar) (z ∷ γ) (h .snd .fst) x hxar)))
      , (λ x xK y yK p →
          valuesInAt-out zero (suc B) (z ∷ γ) (h .snd .snd .fst) x y
            (transport (app2 z x y) p))
      , h .snd .snd .snd

-- =====================================================================
-- THE MEM ROW, RESTATED.  Copy of MemAgree's telescope
-- (src/L/Condensation.lagda.md:4142-4185) with the three refuted
-- hypotheses in tied form.  The row's out instantiates EnvSetTied
-- with the row's own binders (EK and arK); the step E'.out henv
-- inherits the unsolved z ∈ E meta, so the row's out does not
-- elaborate.  The row's out tail after that step (hbM, the AtomLeaf
-- transfer, extAt→extAtB) is unchanged from the master :4204-4208
-- and is unreachable.
-- =====================================================================
module MemAgreeTied {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (keyValK : (E yc b a ar c w v z k : S)
           → ⟨ (k ∷ w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                tagAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) 1 zero ⟩
           → ⟨ fst k ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (envK : (yc b a ar c E : S) → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (entryK-tied : (E : S) → ⟨ fst E ∈ fst (lookup K γ) ⟩
               → (z x y : S) → ⟨ fst z ∈ fst E ⟩
               → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
               → ⟨ fst x ∈ fst (lookup K γ) ⟩
                 × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK-tied : (yc b a ar c x : S)
               → ⟨ fst x ∈ fst (lookup (suc (suc (suc zero)))
                                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
               → ⟨ fst (lookup (suc (suc (suc zero)))
                         (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ∈ fst (lookup K γ) ⟩
               → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (yc b a ar c E z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                           (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
         → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                           (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where

  φB : Formula S m
  φB = Mem.memBndAt C T B N K t0 t1

  -- THE ROW'S OUT, FIRST FAILING STEP.  The row binds EK and arK and
  -- instantiates EnvSetTied; E'.out henv is the step that does not
  -- survive.  The hole is inherited from EnvSetTied.out.
  rowOut-envSet : (c : S) → (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
                → (ar : S) → (arK : ⟨ fst ar ∈ fst (lookup K γ) ⟩)
                → (a : S) → (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩)
                → (b : S) → (bK : ⟨ fst b ∈ fst (lookup K γ) ⟩)
                → (yc : S) → (ycK : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
                → (shB : ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                            arTagPairB N K ⟩)
                → (hc : ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩)
                → (E : S) → (EK : ⟨ fst E ∈ fst (lookup K γ) ⟩)
                → (henv : ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                             envHypB2T B K ⟩)
                → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                     envSetAt zero (suc (suc (suc (suc zero))))
                               (suc (suc (suc (suc (suc (suc B)))))) ⟩
  rowOut-envSet c c∈ ar arK a aK b bK yc ycK shB hc E EK henv =
    let module E' = EnvSetTied {6 + m} zero (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc (suc B))))))
                           (suc (suc (suc (suc (suc (suc K))))))
                           (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                           (entryK-tied E EK)
                           (λ x hx → arSubK-tied yc b a ar c x hx arK)
                           (envInK yc b a ar c E)
    in E'.out henv
