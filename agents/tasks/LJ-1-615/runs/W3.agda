{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.615]  W3 SLICE.  ValueIsL, THE SECOND FACTOR OF [LJ-1.611]'s
-- RECOVERED FACTORIZATION, RESTATED AT TODAY'S CARRIER, TYPE ONLY,
-- TYPECHECKED ALONE, WRITTEN FIRST.
--
-- The brief names the widest unmeasured term: "ValueIsL, restated at
-- today's carrier, TYPE ONLY, capped".
--
-- THE RECOVERY, AND WHY THIS FILE'S TYPE IS ITS SECOND SHAPE.  The
-- first shape (runs/w3-1.out, runs/w3-2.out, both green) read the
-- factor as the INNER determination, from [LJ-1.611]'s report alone:
-- the report gives the arrow ambientOnly-from : TransferL → ValueIsL →
-- AmbientOnly and describes ValueIsL as "the value's
-- constructibility", and the arrow type alone underdetermines the
-- split.  The C-42 sweep then surfaced the retired route's OWN task
-- records, which quote the type literally and agree five times over:
--
--   ValueIsL = (v b : S) → IsOrd b
--            → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt {2} zero (suc zero) ⟩
--            → ⟨ isL v ⟩
--
-- (agents/tasks/archive/L3-32-T51/l3.32-t51-report.md:55,
-- agents/tasks/archive/L3-32-T144/l3.32-t144-report.md:20,
-- agents/tasks/archive/L3-32-T130/l3.32-t130-report.md:69,
-- agents/tasks/archive/L3-31-IVPROBE/l3.31-ivprobe-report.md:222,
-- and the blocker measurement at
-- agents/tasks/archive/L3-32-T70/l3.32-t70-report.md:38-39).  The
-- first shape was therefore WRONG: the inner determination was
-- DELIVERED at the retired route already ("the delivered inner
-- Lset-only", T70:36-37), so it cannot be the factor the report says
-- was NOT delivered.  The recovered factor is the AMBIENT one: the
-- ambient satisfaction of the graph implies the VALUE is
-- constructible.  No git history was read; the archived records are
-- not git.
--
-- TODAY'S CARRIER.  v and b are AMBIENT sets (the satisfaction's
-- environment sits at the structure's carrier,
-- src/FOL/Semantics.lagda.md:91, so ⊨ᵛ takes ambient environments),
-- IsOrd and isL are today's at the ambient carrier
-- (src/L/Constructible.lagda.md), and the formula is TODAY'S rebuilt
-- graph (src/L/Coding/Sequence.lagda.md:291-292, opened at :349), not
-- the retired one.  That is the whole move: the shape is unchanged,
-- the formula under it is today's.
--
-- No formula is chosen and no inhabitant is claimed: this slice is a
-- TYPE.  Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-615.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( isL; isL-trans; IsOrd )
import FOL.Absoluteness
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import Cubical.Data.Vec using ( _∷_; [] )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

ValueIsL : Type (ℓ-suc ℓ)
ValueIsL = (v b : SV.S) → IsOrd b
         → ⟨ (v ∷ b ∷ []) AbsL.⊨ᵛ LsetGraphAt zero (suc zero) ⟩
         → ⟨ isL v ⟩
