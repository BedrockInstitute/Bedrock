{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.746-SPLIT] runs/PT.  THE SPELLING MODULE WITHOUT THE
-- ASSEMBLY.  The brief's named move, isolated: the split-spelled row
-- types named once, and the rows carried into them by erase-cong
-- transports.  NO GraphAt assembly, NO bridge conversion: the file
-- holds only signatures and transports.
--
-- The plus-zero implicits are SPELLED (pA/pS): the unifier cannot
-- decompose countFo graphBndAt, a Def application, against a
-- meta-headed plus (measured runs/pt.out 89.42 s and runs/pt4.out
-- 92.80 s, both blocked on _a).  The split spellings are the pA/pS
-- spellings; the plus-zero chains are never written inline.
--
-- ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-746-SPLIT-SPLIT.runs.PT {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( var; _∧̇_ )
open import FOL.Manipulation.Parameters using ( countFo; countTm )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem
open import LJ-1-732.runs.Amb4a {ℓ} lem
open import LJ-1-732.runs.Amb5 {ℓ} lem
open import LJ-1-732.runs.Amb6 {ℓ} lem
open import LJ-1-746-SPLIT-SPLIT.runs.Amb7 {ℓ} lem
open import LJ-1-746-SPLIT-SPLIT.runs.EraseIrr {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module IrrC = Irr CS.S

-- THE SPLIT COUNT PROOFS, implicits spelled.
pA : countFo Mx.G.A.approxBndAt ≡ 0
pA =
  CntS.plus-zero-l
    {a = countFo Mx.G.A.approxBndAt}
    {b = countFo Mx.G.S.stepBndAt}
    (CntS.plus-zero-r
       {a = countTm {K = CS.S} (var kk)}
       {b = countFo (Mx.G.A.approxBndAt ∧̇ Mx.G.S.stepBndAt)}
       countGB)

pS : countFo Mx.G.S.stepBndAt ≡ 0
pS =
  CntS.plus-zero-r
    {a = countFo Mx.G.A.approxBndAt}
    {b = countFo Mx.G.S.stepBndAt}
    (CntS.plus-zero-r
       {a = countTm {K = CS.S} (var kk)}
       {b = countFo (Mx.G.A.approxBndAt ∧̇ Mx.G.S.stepBndAt)}
       countGB)

-- THE SPLIT-SPELLED ROW TYPES, named once, at the pA/pS proofs.
ApproxSlot : Type (ℓ-suc ℓ)
ApproxSlot =
  ⟨ (n 0 ∷ γ15) P652.⊨ₚ CntS.erase Mx.G.A.approxBndAt pA ⟩

StepSlot : Type (ℓ-suc ℓ)
StepSlot =
  ⟨ (n 0 ∷ γ15) P652.⊨ₚ CntS.erase Mx.G.S.stepBndAt pS ⟩

-- THE ROWS, carried into the split spellings by erase-cong.
approx-split : StepKilledGen → ApproxSlot
approx-split gen =
  subst (λ φ → ⟨ (n 0 ∷ γ15) P652.⊨ₚ φ ⟩)
        (IrrC.erase-cong Mx.G.A.approxBndAt countA pA)
        (approx-part gen)

step-split : StepKilledGen → StepSlot
step-split gen =
  subst (λ φ → ⟨ (n 0 ∷ γ15) P652.⊨ₚ φ ⟩)
        (IrrC.erase-cong Mx.G.S.stepBndAt countS pS)
        step-part
