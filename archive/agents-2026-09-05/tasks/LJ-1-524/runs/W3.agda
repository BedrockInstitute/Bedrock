{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.524]  W3, THE WIDEST UNMEASURED TERM, WRITTEN FIRST AND ALONE.
--
-- The brief names it: the INSTANTIATION.  The ruling of this task is that
-- `Q` is determined at `ord-set-witness a oa .fst` rather than carried as
-- a hypothesis, and nobody has fed that witness's `Q` to a consumer of
-- `rankFo-adequate′`.  If the witness's `Q` does not satisfy the
-- adequacy's own hypothesis `ord-reads-Q Q a oa` at this frame, the
-- ruling is wrong and the task stops here, at its cheapest point.
--
--   -- rankFo-adequate′ applied at Q := ord-set-witness a oa .fst
--
-- The obligation `svAt-at-carve` is OMITTED here on purpose.  So is the
-- carve.  This file is the instantiation and nothing else.
--
-- ONE IMPORT OF A PREDECESSOR PROBE, and it is deliberate.  The brief
-- says "DO NOT REBUILD `rankFo-adequate′`" and prices the whole task at
-- about 200 lines; `[LJ-1.521]` measured the adequacy at 1176 lines
-- (agents/tasks/LJ-1-521/lj-1.521-report.md:286).  The two can only both
-- hold if this task imports.  `bedrock.agda-lib` lists `agents/tasks` as
-- an include root (bedrock.agda-lib:2) and the tree already carries
-- cross-task probe imports: agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29
-- imports `LJ-1-178.ProbeLJ1178A`, and
-- agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24 imports
-- `LJ-1-210.GenModel`.
--
-- Nothing lands in src/.  Does not postulate.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-524.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import LJ-1-521.Probe521 {ℓ} lem as P521

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- W3.  The adequacy at the DETERMINED Q.  No `ord-reads-Q` argument
-- survives: the witness supplies it.  The telescope is
-- (a , oa , z) and nothing else.
-- =====================================================================

ordQ : (a : S) → IsOrd (fst a) → S
ordQ a oa = P521.ord-set-witness a oa .fst

adequate-at-witness :
    (a : S) (oa : IsOrd (fst a)) (z : S)
  → ⟨ (z ∷ []) ⊨ P521.rankFo (ordQ a oa) a ⟩
  → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
      (fst z ≡ pr (fst m) (fst (P521.rank-at′ a oa m mx)))
adequate-at-witness a oa z =
  P521.rankFo-adequate′ (ordQ a oa) a oa z (P521.ord-set-witness a oa .snd)
