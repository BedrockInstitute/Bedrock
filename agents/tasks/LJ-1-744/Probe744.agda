{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.744] PROBE.  The named probe of the 732 critic
-- (review-of-LJ-1-732-1.md, the named-probe section): the 732
-- universal's falsity content, with the truncation elimination moved
-- from the concrete instance (v :: u :: n 0 :: gamma15) to a symbolic
-- environment gamma (W2: one elimination at the generic carrier, then
-- the instance is a call).  Lands nothing in src/.
--
--   THE OBLIGATION  step-killed-gen.  GO means the instance-side
--                   PT.rec the critic named was shape-local, and the
--                   732 window stop stays overturned.
--   THE SHAPE       Imports exactly what Amb7b imports; AppC /
--                   countAppC / App as at Amb7b.agda:32-39; the same
--                   PT.rec, the same pattern (pr , pr-in-empty , _)
--                   and the same body Empty.rec* (subst (empty-spec)).
--   THE READING     The brief writes the conclusion as a negation of
--                   the truncated reading.  The only negation in
--                   scope is the truth algebra's, which takes the
--                   proposition itself (Base/Truth.lagda.md, the
--                   TruthAlgebra record), so the conclusion is spelled
--                   as the same function type directly: the carrier
--                   of the reading into the falsity of the algebra,
--                   which is what Empty.rec* discharges.
--
-- ONE Agda process at a time, pane caliber (GHCRTS is set on the pane
-- and untouched here).  Floor first: runs/Floor744.agda prices the
-- frame without the obligation.  Nothing is postulated.  No hole in
-- the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-744.Probe744 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Parameters using ( countFo )
open import L.Coding.Model {ℓ} using ( appAt )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import Cubical.Data.Vec using ( _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open import LJ-1-652.Probe652 {ℓ} lem as P652
open import V.Model {ℓ} using ( empty-spec )
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-732.runs.Amb1 {ℓ} lem
open import LJ-1-732.runs.Amb7a {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- the implication leaf of the approximation at the empty instance,
-- as at Amb7b.agda:32-39.
AppC : Formula CS.S 18
AppC = appAt (suc (suc zero)) (suc zero) zero

countAppC : countFo AppC ≡ 0
countAppC = refl

App : Formula (⊥* {ℓ-suc ℓ}) 18
App = CntS.erase AppC countAppC

-- THE OBLIGATION.  The same elimination Amb7b runs at gamma15, at a
-- symbolic environment.  Slot 2 stays the literal n 0, so the
-- witness's membership fact still lands in the empty set and the
-- generic empty-spec refutation still applies.
step-killed-gen :
    (u v : S) (γ : Vec S 15)
    → ⟨ u ∈ˢ n 12 ⟩
    → ⟨ v ∈ˢ n 12 ⟩
    → ⟨ (v ∷ u ∷ n 0 ∷ γ) P652.⊨ₚ App ⟩
    → Empty.⊥* {ℓ-suc ℓ}
step-killed-gen u v γ u∈ v∈ ant =
    PT.rec
      Empty.isProp⊥*
      (λ { (pr , pr∈∅ , _) →
            Empty.rec* (subst ⟨_⟩ (empty-spec pr) pr∈∅) })
      ant
