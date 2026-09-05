{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.336] probe.  THE DIRTY SEVEN `Agree` MODULES, PORTED GENERIC IN
-- THE CLASS, WAVE 2 OF `q'`.
--
-- The scaffold is wave 1's, unchanged in shape: the eight parameters are
-- `GenModel`'s, and the codings come from `GenModel` applied at them.
-- Wave 1's port arrives as ONE module application, so the 113 blocks of
-- the seven's closure that wave 1 already ported are not copied twice.
--
-- Above the marker sit the eight committed gap names the seven reach and
-- `GenModel` does not deliver, re-stated VERBATIM from `src/L/Coding/`:
-- `keyArityAtL` and `hasWitnessAt` from `CodeSet`, `twelveAt` and
-- `satGraphAt` from `Graph`, `envOneAt`, `DefinesAt`, `isCodeAt` and
-- `DefBody` from `Powerset`.  Every one is syntax over `GenModel`
-- primitives, so each ports unchanged.  `shapedAt`, the ninth, arrives
-- from wave 1.  `satGraphAt` keeps its `opaque` seal, because
-- `SatGraphAgree` is the one site in the tree that unfolds it.
--
-- Below the marker, every block is copied VERBATIM from
-- `src/L/Condensation.lagda.md` at the line range the trailing manifest
-- records, in chapter order.  The diff against the original spans is the
-- task's number.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy using ( 𝒮ᵥ )
open import V.Coding using ( pr )
open import V.Model using ( pair-singleton )
open import L.Coding.Base using ( Δ₀-prAt )
open import L.Coding.Environment using ( Δ₀-consAt; Δ₀-sucAt )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

import LJ-1-306.GenAgree

module LJ-1-336.GenDirty {ℓ : Level}
  (M : V ℓ → hProp (ℓ-suc ℓ))
  (M-trans : Transitive (𝒮ᵥ {ℓ}) M)
  (numeralL : ℕ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (numeralL-fst : (k : ℕ) → fst (numeralL k) ≡ # k)
  (pairʟ : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (pairʟ-fst : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
             → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆)
  (sucʟ : Σ[ x ∈ V ℓ ] ⟨ M x ⟩ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (sucʟ-fst : (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a))
  where

module W1 = LJ-1-306.GenAgree {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open W1
open W1.GM
open W1.GM.ToL using ( Δ₀-liftFo )
open W1.KFactsNS
open W1.KFactsNS.KFacts

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M) using ( S )
open W1.GM.AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE COMMITTED GAP NAMES, RE-STATED.  Verbatim from `src/L/Coding/`,
-- one nested module per source module, so each source module's own
-- private helpers stay private here too.
-- =====================================================================

-- src/L/Coding/CodeSet.lagda.md:135-136 and :240-242
module CodeSetGap where

  keyArityAtL : ∀ {n} → Fin n → ℕ → Formula S n
  keyArityAtL c k = ∃̇ (tagAtL (suc c) k zero)

  hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n
  hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero)
                        ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A)))

open CodeSetGap public

-- src/L/Coding/Graph.lagda.md:85-92, :94-105, :186-192 and :203-205
module GraphGap where

  private
    Ci Ti Bi : ∀ {n} → Fin (suc (suc (suc n)))
    Ci = suc (suc zero)
    Ti = suc zero
    Bi = zero

    sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
    sh3 i = suc (suc (suc i))

  twelveAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  twelveAt C T B =
    memClauseAt C T B ∧̇ (eqClauseAt C T B
    ∧̇ (andClauseAt C T ∧̇ (orClauseAt C T
    ∧̇ (impClauseAt C T B ∧̇ (negClauseAt C T B
    ∧̇ (topClauseAt C T B ∧̇ (botClauseAt C T
    ∧̇ (existClauseAt C T B ∧̇ (forallClauseAt C T B
    ∧̇ (allInClauseAt C T B ∧̇ exInClauseAt C T B))))))))))

  private
    satGraphOn : ∀ {n} → Formula S (suc (suc (suc n)))
               → Fin n → Fin n → Formula S n
    satGraphOn pin x y =
      ∃̇ (∃̇ (∃̇ ( pin
              ∧̇ ( closedAt Ci
              ∧̇ ( domAt Ti Ci
              ∧̇ ( appAt Ti (sh3 x) (sh3 y)
              ∧̇ twelveAt Ci Ti Bi ))))))

  opaque
    satGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    satGraphAt B x y = satGraphOn (var Bi ≐ var (sh3 B)) x y

open GraphGap public

-- src/L/Coding/Powerset.lagda.md:128-129, :217-220, :297-298, :431-440
module PowersetGap where

  envOneAt : ∀ {n} → Fin n → Fin n → Formula S n
  envOneAt e y = extAt e (tagAtL zero 0 (suc y))

  DefinesAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  DefinesAt x w v = extAt x ( (var zero ∈̇ var (suc w))
                            ∧̇ ∃̇ ( envOneAt zero (suc zero)
                                 ∧̇ (var zero ∈̇ var (suc (suc v))) ) )

  isCodeAt : ∀ {n} → Fin n → Fin n → Formula S n
  isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c

  private
    sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
    sh3 i = suc (suc (suc i))

  DefBody : ∀ {n} → Fin n → Formula S (suc (suc (suc n)))
  DefBody w = isCodeAt (suc zero) (sh3 w)
              ∧̇ ( satGraphAt (sh3 w) (suc zero) zero
                ∧̇ DefinesAt (suc (suc zero)) (sh3 w) zero )

open PowersetGap public

-- =====================================================================
-- BELOW THIS LINE: VERBATIM FROM `src/L/Condensation.lagda.md`, in
-- chapter order.  The manifest at the file's end records each block's
-- source range.
-- =====================================================================
