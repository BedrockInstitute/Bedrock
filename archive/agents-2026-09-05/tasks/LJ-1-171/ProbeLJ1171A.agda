{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.171 probe A.  The last gate before the build: the OBJECT-LEVEL
-- READING of the re-key arm's three-component key.
--
-- CRITERIA, FIXED IN WRITING BEFORE THE FIRST `agda` INVOCATION (D-1):
--   wall clock  10 minutes per agda invocation, GHCRTS="-A64m -I0 -M8g",
--               ONE process, cap NEVER raised.  A wall is reported with
--               its wall-clock and the task STOPS.
--   the target  GO at or below 60 in-fence lines for ONE `paramSetAtL`
--               conjunct WITH BOTH DIRECTIONS, against the delivered
--               `arityNumAtL` (`src/L/Coding/CodeSet.lagda.md:185-208`)
--               as the rate comparable.  NO-GO above 60.
--               The stop-line is `[LJ-1.170]`'s and it is NOT moved.
--   counting    non-blank, non-comment lines, the convention
--               `[LJ-1.167]`, `[LJ-1.169]` and `[LJ-1.170]` used.
--
-- WHAT THIS FILE MEASURES, AND THE CORRECTION IT CARRIES.
--
--   `[LJ-1.170]` measured the split key's BOUND with the parameter
--   component written as `finSet k (λ i → ⟪ Lset σ ⟫↪ (g i))`
--   (`agents/tasks/LJ-1-170/ProbeLJ1170A.agda:83-84`).  A `finSet` is
--   `sett (Lift (Fin n)) (λ i → h (lower i))`
--   (`src/L/Axioms/Basic.lagda.md:285-286`): it keeps NO index, so
--   `finSet-out` returns a TRUNCATED index and the vector is not
--   recoverable from the set.  The reading direction `AllCodes-out`
--   needs the vector, because `absFo φ` substitutes its parameters BY
--   POSITION.  So the parameter component must be a SEQUENCE.
--
--   The tree already has the sequence and its two directions:
--     `env`          `src/L/Coding/Environment.lagda.md:84-86`
--     `envOverAt`    `src/L/Coding/Model.lagda.md:483-485`
--     `envOver`      `src/L/Coding/EnvSet.lagda.md:232-283` (the -in)
--     `Recover`      `src/L/Coding/EnvSet.lagda.md:315-379` (the -out)
--   and Devlin's `K(u)` is finite SEQUENCES, not finite sets
--   (`_build/literature/dev2.txt:600-608`).
--
--   BLOCK 1 is the measured term: ONE conjunct saying, of a key slot,
--   that its payload is a pair of a code with an environment over the
--   CARRIER SLOT, the environment's length bound in `ωʟ`.  The carrier
--   is a SLOT and not a constant, which is what
--   `src/L/Coding/CodeSet.lagda.md:32-44` requires of every conjunct
--   the internal hierarchy speaks under its own binder.
--
-- P-i [F] is obeyed: every implicit set index at a concrete argument is
-- written out.
--
-- No master is edited.  This file is a probe and lives beside the
-- report, per D-1 and `AGENTS.md`.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-171.ProbeLJ1171A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; numL
        ; envOverAt; envOverAt-transport )
import L.Coding.EnvSet

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module EnvS = L.Coding.EnvSet {ℓ} lem

-- =====================================================================
-- BLOCK 1: THE MEASURED TERM.
--
-- The conjunct, and its two directions.  Five binders: the arity `ar`,
-- the payload `z`, the code `cd`, the parameter environment `p`, and
-- the environment's length `d`, which is pinned in `ωʟ` exactly as
-- `arityNumAtL` pins the arity.
-- =====================================================================

lift5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
lift5 i = suc (suc (suc (suc (suc i))))

paramSetAtL : ∀ {n} → Fin n → Fin n → Formula S n
paramSetAtL b c = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
  ( prAtL (lift5 c) (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
  ∧̇ ( prAtL (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
    ∧̇ ( (var zero ∈̇ con ωʟ)
      ∧̇ envOverAt (suc zero) zero (lift5 b) ) ) ) ))))

module _ (B : S) where
  Split : ∀ {n} → Fin n → S ^ n → Type (ℓ-suc ℓ)
  Split c γ = Σ[ ar ∈ S ] Σ[ cd ∈ S ] Σ[ k ∈ ℕ ] Σ[ g ∈ EnvS.Ix B k ]
    (fst (lookup c γ) ≡ pr (fst ar) (pr (fst cd) (fst (EnvS.envS B g))))

  paramSetAtL-out : ∀ {n} (b c : Fin n) (γ : S ^ n)
                  → fst (lookup b γ) ≡ fst B
                  → ⟨ γ ⊨ paramSetAtL b c ⟩ → ∥ Split c γ ∥₁
  paramSetAtL-out b c γ qb = PT.rec squash₁ (λ { (ar , h1) →
    PT.rec squash₁ (λ { (z , h2) → PT.rec squash₁ (λ { (cd , h3) →
    PT.rec squash₁ (λ { (p , h4) →
    PT.rec squash₁ (λ { (d , (hp , (hq , (hω , hov)))) → PT.map
      (λ { (m , qm) → ar , cd , lower m
         , EnvS.Recover.g B (lower m) (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ)
             (suc zero) zero (lift5 b)
             (qm ∙ numeralL-fst (lower m)) qb hov
         , ( subst ⟨_⟩ (prAtL-adequate (lift5 c)
               (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
               (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ)) hp
           ∙ cong (pr (fst ar))
               ( subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                   (suc (suc zero)) (suc zero)
                   (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ)) hq
               ∙ cong (pr (fst cd))
                   (EnvS.Recover.recovers B (lower m)
                     (d ∷ p ∷ cd ∷ z ∷ ar ∷ γ) (suc zero) zero (lift5 b)
                     (qm ∙ numeralL-fst (lower m)) qb hov) ) ) })
      (subst ⟨_⟩ (ω-specL d) hω) }) h4 }) h3 }) h2 }) h1 })

  paramSetAtL-in : ∀ {n} (b c : Fin n) (γ : S ^ n)
                 → fst (lookup b γ) ≡ fst B
                 → (ar cd : S) {k : ℕ} (g : EnvS.Ix B k)
                 → fst (lookup c γ)
                   ≡ pr (fst ar) (pr (fst cd) (fst (EnvS.envS B g)))
                 → ⟨ γ ⊨ paramSetAtL b c ⟩
  paramSetAtL-in {n} b c γ qb ar cd {k} g e =
    ∣ ar , ∣ prʟ cd (EnvS.envS B g) , ∣ cd , ∣ EnvS.envS B g , ∣ numeralL k
    , ( subst ⟨_⟩ (sym (prAtL-adequate (lift5 c)
          (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) δ))
          (e ∙ cong (pr (fst ar)) (sym (prʟ-fst cd (EnvS.envS B g))))
      , ( subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
            (suc (suc zero)) (suc zero) δ)) (prʟ-fst cd (EnvS.envS B g))
        , ( subst ⟨_⟩ (sym (ω-specL (numeralL k))) ∣ lift k , refl ∣₁
          , envOverAt-transport (B ∷ ((# k) , numL k) ∷ EnvS.envS B g ∷ [])
              δ (suc (suc zero)) (suc zero) zero (suc zero) zero (lift5 b)
              refl (sym (numeralL-fst k)) (sym qb)
              (EnvS.envOver B g) ) ) ) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    where
    δ : S ^ suc (suc (suc (suc (suc n))))
    δ = numeralL k ∷ EnvS.envS B g ∷ cd ∷ prʟ cd (EnvS.envS B g) ∷ ar ∷ γ
