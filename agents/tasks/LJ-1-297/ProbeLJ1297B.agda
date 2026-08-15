{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.297] probe B.  THE ADVERSARIAL CHECK: IS `IntendedQ` `q`?
--
-- [LJ-1.293] refutes an equation it WRITES ITSELF
-- (`ProbeLJ1293A.agda:121-122`):
--
--   IntendedQ = Seq.LsetGraphAt {2} zero (suc zero) == embed P1241.f0
--
-- and it ties that equation to `q` by ONE stated `refl`
-- (`ProbeLJ1293A.agda:82-83`), which compares two CARRIERS.  A carrier
-- identity does not prove that `Seq.LsetGraphAt` can occupy the `Graph`
-- slot of `AmbientStep` (`ProbeLJ1184B.agda:104`), and it does not prove
-- that the module's own `q` (`ProbeLJ1184B.agda:112`) elaborates to
-- `IntendedQ`.  This probe makes the elaborator answer both, by
-- APPLICATION instead of by assertion.
--
--   `Graph*`      the ascription: `LsetGraphAt` at `AmbientStep`'s
--                 verbatim `Graph` type.
--   `AS`          `AmbientStep` APPLIED at `Graph := Graph*` and
--                 `f0 := P1241.f0`.  Its `q` slot takes my `q`.
--   `ambHere`     `amb` really does come out of that application.
--   `dead`        and the same telescope proves `Empty`, by
--                 [LJ-1.293]'s own term.
--
-- The six readings and the `DefAt` trio stay HYPOTHESES, so the result
-- holds for every Def-step coding and every reading supply.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-297.ProbeLJ1297B {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( embed )
open import L.Constructible {ℓ} using ( 𝒟ₒ )
import Cubical.Data.Empty as Empty
import LJ-1-184.ProbeLJ1184A {ℓ} as P184
import LJ-1-184.ProbeLJ1184B {ℓ} lem as P184B
import LJ-1-297.ProbeLJ1297A {ℓ} lem as P1297A

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

module A = P184.Ambient
module GS = P1297A.GS
module P1241 = P1297A.P1241
open P1297A.AbsL using ( _⊨ᵐ_ )

-- =====================================================================
-- THE DEF-STEP CODING, exactly [LJ-1.293]'s three hypotheses, with the
-- carrier written `A.R.SC` instead of `S`.  The elaborator now has to
-- IDENTIFY the two carriers to accept the application below, so the
-- stated `refl` at ProbeLJ1293A.agda:82-83 is not trusted here.
-- =====================================================================

module Fit
  (DefAt : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
  (DefAt-in : (X : A.R.SC) → ∀ {n} (u w : Fin n) (γ : Vec A.R.SC n)
            → fst (lookup w γ) ≡ fst X
            → fst (lookup u γ) ≡ 𝒟ₒ (fst X)
            → ⟨ γ ⊨ᵐ DefAt u w ⟩)
  (DefAt-out : (X : A.R.SC) → ∀ {n} (u w : Fin n) (γ : Vec A.R.SC n)
             → GS.DefOK X
             → fst (lookup w γ) ≡ fst X
             → ⟨ γ ⊨ᵐ DefAt u w ⟩
             → fst (lookup u γ) ≡ 𝒟ₒ (fst X))
  where

  module R = P1297A.RefuteQ DefAt DefAt-in DefAt-out

  -- THE ASCRIPTION.  `AmbientStep`'s `Graph` type, verbatim from
  -- ProbeLJ1184B.agda:104, inhabited by the sequence coding's graph.
  Graph* : ∀ {n} → Fin n → Fin n → Formula A.R.SC n
  Graph* {n} = R.Seq.LsetGraphAt {n}

  module Instantiate
    (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula A.R.SC n)
    (Approx : ∀ {n} → Fin n → Fin n → Formula A.R.SC n)
    (Step-out : P184B.Types.StepOutT Step Approx Graph*)
    (Step-back : P184B.Types.StepBackT Step Approx Graph*)
    (Approx-dom : P184B.Types.ApproxDomT Step Approx Graph*)
    (Approx-value : P184B.Types.ApproxValT Step Approx Graph*)
    (Approx-step : P184B.Types.ApproxStepT Step Approx Graph*)
    (Graph-out : P184B.Types.GraphOutT Step Approx Graph*)
    -- `AmbientStep`'s own `q`, at the intended instantiation.
    (q : Graph* {2} zero (suc zero) ≡ embed P1241.φ₀)
    where

    module AS = P184B.AmbientStep Step Approx Graph*
      Step-out Step-back Approx-dom Approx-value Approx-step Graph-out
      P1241.φ₀ q

    -- `amb` COMES OUT of this application, so the telescope above is
    -- the intended supply and not an adjacent one.
    ambHere = AS.amb

    -- AND THE SAME `q` PROVES `Empty`, by [LJ-1.293]'s term.
    dead : Empty.⊥
    dead = R.q-false q
