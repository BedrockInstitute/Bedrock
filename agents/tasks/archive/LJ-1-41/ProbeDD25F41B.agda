{-# OPTIONS --cubical --safe --guardedness #-}

-- [DD25 / LJ-1.41 REVIEW] IS THE MACHINE'S envSetAt REACHABLE FROM A
-- Δ₀ BOUNDED RESTATEMENT, UNDER SITE FACTS?
--
-- The [LJ-1.41] return says NO:
--   "The bounded quantifiers cannot be lifted to the unbounded ones by
--    any site fact ... so the rows cannot be made equivalent within
--    the Δ₀ constraint."
--
-- This probe builds BOTH directions of
--     envSetB E ar B K   <->   envSetAt E ar B
-- where envSetB is the Δ₀ formula of ProbeDD25F41A, and envSetAt is
-- the machine's condition at src/L/Coding/Model.lagda.md:1149.
--
-- It uses ONLY delivered machinery:
--   extAtB->extAt / extAt->extAtB  (src/L/Condensation.lagda.md:2398)
--   envBndGen                      (src/L/Condensation.lagda.md:506)
--   envOverAt and its readers      (src/L/Coding/Model.lagda.md:483)
--
-- The site facts are hypotheses, exactly as SubValB2T, OpTransfer and
-- TmVal take theirs.  There are three:
--   entryK  : the two components of an entry of a candidate
--             environment lie in K;
--   arSubK  : the arity's members lie in K;
--   envInK  : every environment over ar with values in B lies in K.
--
-- EXPECTED: GREEN.  If it is green, "no site fact lifts the bounded
-- quantifiers" is refuted, and the nine rows' blocker is a missing
-- conjunct plus one new site fact, not an impossibility.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed; thrown away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25F41B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( Δ₀ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( envSetAt; envOverAt; extAt; appAt; appAt-adequate
        ; svAt-in; domAt-intro; valuesInAt-in
        ; svAt-out; domAt-out; domAt-in; valuesInAt-out )
open import L.Condensation {ℓ} lem
  using ( extAtB; Δ₀-extAtB; envBndGen; Δ₀-envBndGen
        ; extAtB→extAt; extAt→extAtB )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The K-bounded two-way environment-set condition, from F41A.
envSetB : ∀ {n} → (E ar B K : Fin n) → Formula S n
envSetB E ar B K =
  extAtB E K (envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))

Δ₀-envSetB : ∀ {n} (E ar B K : Fin n) → Δ₀ (envSetB E ar B K)
Δ₀-envSetB E ar B K =
  Δ₀-extAtB E K _ (Δ₀-envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))

-- =====================================================================
-- THE LEAF TRANSFER, BOTH WAYS.  envBndGen against envOverAt.
-- The story-to-machine leg (bnd->over) is the one the return says
-- cannot exist.
-- =====================================================================
module Leaf {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩)
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

  -- THE NEW DIRECTION.  The K-bounded condition gives the machine's
  -- unbounded condition, under the two site facts.
  bnd→over : (z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  bnd→over z hb =
      svAt-in zero (z ∷ γ)
        (λ x y y' p q →
          let xK = entryK z x y p .fst
              yK = entryK z x y p .snd
              y'K = entryK z x y' q .snd
          in hb .fst x xK y yK y' y'K
               (transport (sym (app3 z x y y')) p)
               (transport (sym (app3' z x y y')) q))
    , domAt-intro zero (suc ar) (z ∷ γ)
        (λ x →
            (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                      (λ { (y , p) →
                        hb .snd .fst x (entryK z x y p .fst) .fst
                          ∣ y , ( entryK z x y p .snd
                                , transport (sym (app2 z x y)) p ) ∣₁ })
                      hx)
          , (λ hxar → PT.map
                        (λ { (y , (yK , hp)) → y , transport (app2 z x y) hp })
                        (hb .snd .fst x (arSubK x hxar) .snd hxar)))
    , valuesInAt-in zero (suc B) (z ∷ γ)
        (λ x y p →
          hb .snd .snd .fst x (entryK z x y p .fst) y (entryK z x y p .snd)
            (transport (sym (app2 z x y)) p))
    , hb .snd .snd .snd

  -- The delivered direction, generic (EnvB2T does this at one layout).
  over→bnd : (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
  over→bnd z h =
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
                        ∣ y , ( entryK z x y p .snd
                              , transport (sym (app2 z x y)) p ) ∣₁ })
                      (domAt-in zero (suc ar) (z ∷ γ) (h .snd .fst) x hxar)))
    , (λ x xK y yK p →
        valuesInAt-out zero (suc B) (z ∷ γ) (h .snd .snd .fst) x y
          (transport (app2 z x y) p))
    , h .snd .snd .snd

-- =====================================================================
-- THE ENVIRONMENT-SET TRANSFER, BOTH WAYS.
-- =====================================================================
module EnvSet {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (entryK : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
          → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where

  module L = Leaf {n} E ar B K γ entryK arSubK

  -- STORY TO MACHINE: the Δ₀ bounded condition reaches the machine's.
  out : ⟨ γ ⊨ envSetB E ar B K ⟩ → ⟨ γ ⊨ envSetAt E ar B ⟩
  out = extAtB→extAt E K L.φB L.φ γ L.bnd→over L.over→bnd envInK

  -- MACHINE TO STORY: the machine's condition reaches the Δ₀ one.
  back : ⟨ γ ⊨ envSetAt E ar B ⟩ → ⟨ γ ⊨ envSetB E ar B K ⟩
  back = extAt→extAtB E K L.φB L.φ γ L.bnd→over L.over→bnd
