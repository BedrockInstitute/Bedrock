{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Classical using ( LEM )

module LJ-1-745.Probe745 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Coding.Model {ℓ} using ( appAt )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Vec using ( Vec; _∷_ )
import Cubical.Data.Empty as Empty
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem

open hPropStructure 𝒮ᵥ

-- [LJ-1.745] The implication leaf of Amb7b, landed as ONE instance
-- call.  The truncation elimination lives in the generic lemma; this
-- file takes that lemma as a HYPOTHESIS at the critic's type
-- (agents/tasks/LJ-1-732/review-of-LJ-1-732-1.md:163-166) and does not
-- inhabit it: the sibling task LJ-1.744 owns the proof.
--
-- WHY THE HYPOTHESIS IS step-killed's LEADING ARGUMENT.  The meter of
-- scripts/pod/witness.py always injects `--safe` into its witness, and
-- Agda 2.8.0 refuses a postulate under `--safe` ([SafeFlagPostulate],
-- measured this task, runs/floor745-warm3.out) and refuses importing a
-- module that was checked without `--safe` ([CoInfectiveImport],
-- minimal pair measured this task, quoted in lj-1.745-report.md).  A
-- module parameter would need `App` before the module header, and
-- would leave the witness unable to supply the argument
-- (binder_application emits a bare name).  A leading explicit argument
-- on step-killed itself is the tree's own parameter idiom (Frame652 in
-- LJ-1-652.Probe652), keeps `Target.step-killed` resolvable for the
-- obligation agents/tasks/LJ-1-745/Probe745.agda::step-killed, and
-- changes no motive: the conclusion is Amb7b's line 46 verbatim.  When
-- LJ-1.744 delivers the lemma, Amb7b's exact signature is one
-- application away, spelled out in lj-1.745-report.md.
--
-- Two spelling notes on the critic's prose type.  γ is written
-- `Vec S 15`, the critic's own spelling (`γ15 : S ^ 15` and `_^_ A n =
-- Vec A n`, so the instance call at γ15 is definitionally typed).  The
-- prose `¬ ⟨ env ⊨ₚ App ⟩` is written as its carrier: at the hProp
-- algebra `⟨ ¬ φ ⟩` unfolds to `⟨ φ ⟩ → Empty.⊥`.
--
-- Imports are trimmed to what these rows name (coder law, owner
-- ruling 2026-08-23): no PropTruncation (the elimination is the
-- hypothesis's own), no V.Model (empty-spec is inside the lemma's
-- proof, not the call), no Amb7a (MotiveEmpty is never written here;
-- the conclusion type it names is carried by step-killed's own type).

AppC : Formula CS.S 18
AppC = appAt (suc (suc zero)) (suc zero) zero

countAppC : countFo AppC ≡ 0
countAppC = refl

App : Formula (⊥* {ℓ-suc ℓ}) 18
App = CntS.erase AppC countAppC

step-killed :
    ( (u v : S)
      → (γ : Vec S 15)
      → ⟨ u ∈ˢ n 12 ⟩
      → ⟨ v ∈ˢ n 12 ⟩
      → ⟨ (v ∷ u ∷ n 0 ∷ γ) P652.⊨ₚ App ⟩
      → Empty.⊥ )
    → (u v : S)
    → ⟨ u ∈ˢ n 12 ⟩
    → ⟨ v ∈ˢ n 12 ⟩
    → ⟨ (v ∷ u ∷ n 0 ∷ γ15) P652.⊨ₚ App ⟩
    → ⟨ (v ∷ u ∷ n 0 ∷ γ15) P652.⊨ₚ CntS.erase Mx.G.A.S.stepBndAt countAS ⟩
step-killed gen u v u∈ v∈ ant =
    Empty.rec (gen u v γ15 u∈ v∈ ant)
