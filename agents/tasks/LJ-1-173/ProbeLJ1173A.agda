{-# OPTIONS --cubical --safe --guardedness #-}

-- LJ-1.173 probe A.  THE GATE on the numeral-arity restriction of
-- `envSetK` (src/L/Condensation/TwelveAgree.lagda.md:271-275).
--
-- THE ONE DECLARATION THE GATE ASKS FOR:
--
--   envSetNumeral∈ : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ (B : S) (n : ℕ)
--                  → ⟨ fst B ∈ Lset σ ⟩
--                  → ⟨ fst (envSet B n) ∈ Lset (sucIter k σ) ⟩
--
-- with `k` a FIXED natural, the same for every `n`.  That is the
-- brief's "uniformly in n".
--
-- CRITERION, FIXED BEFORE THE FIRST RUN (D-1):
--   GO    at 40 or fewer non-blank, non-comment lines of Agda, module
--         header and imports excluded, with no postulate, no hole and
--         no unsolved meta.
--   NO-GO above 40, or if the declaration cannot be closed from
--         delivered material.  Report the figure and STOP.
--   20 minutes of wall time per agda invocation, GHCRTS="-A64m -I0
--   -M8g", ONE process, the cap NEVER raised.
--
-- THE ROUTE, and the two blocks are the two halves of the gate.
--   BLOCK 1  the SUBSET half.  Every member of `envSet B n` lies in a
--            FIXED iterate above the stage that holds `B`, uniformly
--            in `n`.  This is the half [LJ-1.172] measured, through
--            `paramEnv∈` (src/L/Coding/Key.lagda.md:71-81).
--   BLOCK 2  the MEMBERSHIP half.  A subset of a stage is a MEMBER of
--            the next stage only when it is DEFINABLE there.  The
--            tree's only stage-controlled carve, `AtStage.carve`
--            (src/L/Axioms/Separation.lagda.md:193-199), takes a Δ₀
--            formula.  The delivered description `envFo`
--            (src/L/Coding/EnvSet.lagda.md:176-180) is NOT Δ₀, so the
--            block must write a bounded one.  BLOCK 2 writes the
--            MANDATORY SYNTAX LAYER of that carve and nothing else:
--            the formula, its Δ₀ witness, its constant certificate,
--            and the `∈ 𝒟ₒ` step.  The adequacy is not written here;
--            the report prices it.
--
-- P-i [F] is obeyed: every lemma with an implicit set index applied at
-- a concrete argument gets the index EXPLICITLY.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-173.ProbeLJ1173A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∧̇_; _⇒̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-≐; δ-∧; δ-⇒; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Axioms.Separation {ℓ} lem using ( module AtStage )
open import L.Coding.Model {ℓ} using ( appAt; prAtL )
open import L.Condensation {ℓ} lem using ( Δ₀-appAt; Δ₀-prAtL )
open import L.Coding.Key {ℓ} lem using ( paramEnv∈ )
open import L.Coding.EnvSet {ℓ} lem using ( Ix; envS; envSet; envSet-out )
open import L.Ordinal.StageArith {ℓ} lem using ( sucIter )

open import Cubical.Data.FinData using ( Fin; zero; suc )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

-- =====================================================================
-- BLOCK 1.  THE SUBSET HALF.
-- =====================================================================

-- One environment over `B` of numeral length `n` lands three stages
-- above the stage that holds `B`, and the three is the same for every
-- `n`.  `paramEnv h = env h`, so the conclusion is already the shape
-- `envS` has.
memberIn : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : S) (n : ℕ)
         → ⟨ fst B ∈ Lset σ ⟩ → (g : Ix B n)
         → ⟨ fst (envS B g) ∈ Lset (sucIter 3 σ) ⟩
memberIn σ oσ ω∈ B n hB g =
  paramEnv∈ σ oσ ω∈ n (λ i → ⟪ fst B ⟫↪ (g i)) mem
  where
  mem : (i : Fin n) → ⟨ ⟪ fst B ⟫↪ (g i) ∈ Lset σ ⟩
  mem i = layer-trans (Lset-layer σ) {x = fst B} {y = ⟪ fst B ⟫↪ (g i)}
    (∈∈ₛ {a = ⟪ fst B ⟫↪ (g i)} {b = fst B} .snd (∈ₛ⟪ fst B ⟫↪ (g i))) hB

-- The whole set is therefore INSIDE the fixed iterate.  This is a
-- containment and it is NOT a membership.
setSub : (σ : V ℓ) → IsOrd σ → ⟨ ω ∈ σ ⟩ → (B : S) (n : ℕ)
       → ⟨ fst B ∈ Lset σ ⟩ → (x : S) → ⟨ x ∈ˢ envSet B n ⟩
       → ⟨ fst x ∈ Lset (sucIter 3 σ) ⟩
setSub σ oσ ω∈ B n hB x hx =
  PT.rec (snd (fst x ∈ Lset (sucIter 3 σ)))
    (λ { (g , q) → subst (λ w → ⟨ w ∈ Lset (sucIter 3 σ) ⟩) (sym q)
                     (memberIn σ oσ ω∈ B n hB g) })
    (envSet-out B n x hx)

-- =====================================================================
-- BLOCK 2.  THE MEMBERSHIP HALF: the mandatory syntax layer.
-- =====================================================================

-- A bounded description of "e is a function with domain `d` and values
-- in `B`".  Every quantifier is bounded, by `con d`, by `con B` or by
-- `e` itself, so the formula is Δ₀ and the carve at a stage is
-- available.  The delivered `envFo` is the same content with UNBOUNDED
-- quantifiers (`svAt` and `domAt` use `∀̇`, `inDomAt` uses `∃̇`), and
-- that is why it cannot be carved at a controlled stage.
module Carve (α : V ℓ) (oα : IsOrd α) (B d : S)
             (hB : ⟨ fst B ∈ Lset α ⟩) (hd : ⟨ fst d ∈ Lset α ⟩) where

  envFoB : Formula S 1
  envFoB =
    (∀̇∈ (con d) (∀̇∈ (con B) (∀̇∈ (con B)
       ( appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
       ⇒̇ ( appAt (suc (suc (suc zero))) (suc (suc zero)) zero
       ⇒̇ (var (suc zero) ≐ var zero) )))))
    ∧̇ ((∀̇∈ (con d) (∃̇∈ (con B) (appAt (suc (suc zero)) (suc zero) zero)))
    ∧̇ (∀̇∈ (var zero) (∃̇∈ (con d) (∃̇∈ (con B)
         (prAtL (suc (suc zero)) (suc zero) zero)))))

  Δ₀-envFoB : Δ₀ envFoB
  Δ₀-envFoB =
    δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈
          (δ-⇒ (Δ₀-appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero))
               (δ-⇒ (Δ₀-appAt (suc (suc (suc zero))) (suc (suc zero)) zero)
                    δ-≐)))))
        (δ-∧ (δ-∀∈ (δ-∃∈ (Δ₀-appAt (suc (suc zero)) (suc zero) zero)))
             (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero)))))

  bddEnvFoB : BoundedFo (AtStage.Below α oα) envFoB
  bddEnvFoB = ((hd , (hB , (hB , ((_ , _) , ((_ , _) , _)))))
              , ((hd , (hB , (_ , _))) , (_ , (hd , (hB , _)))))

  module AS = AtStage α oα

  carved : V ℓ
  carved = AS.carve (AS.RL.liftFo envFoB bddEnvFoB)

  -- The carved set IS a member of the next stage.  Nothing here says it
  -- is `envSet B n`; that identification is the adequacy the report
  -- prices, and it is not written.
  carved∈ : ⟨ carved ∈ Lset (sucV α) ⟩
  carved∈ = subst (λ w → ⟨ carved ∈ w ⟩) (sym (Lset-suc α))
    (AS.carve∈𝒟ₒ (AS.RL.liftFo envFoB bddEnvFoB))
