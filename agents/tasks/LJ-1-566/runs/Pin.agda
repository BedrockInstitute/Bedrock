{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.566]  THE OBLIGATION IS PINNED TO `InjCode` AND CANNOT HAVE
-- DRIFTED FROM MY OWN TRANSCRIPTION.
--
-- This is `[LJ-1.529]`'s `range-is-fourth-of-InjCode` device
-- (Probe529.agda:190-191) and `[LJ-1.531]`'s `runs/Pin.agda`, turned on
-- the assembled term: the four conjuncts are projected BACK OUT of
-- `injcode-assembled` by the projections of `InjCode`
-- (src/L/Cardinal.lagda.md:224-228) and ascribed at the four types
-- `[LJ-1.524]`, `[LJ-1.559]`, `[LJ-1.531]` and `[LJ-1.529]` were briefed
-- at.  It builds NO new term: every binding is a projection.
--
-- IF THE ASSEMBLY HAD PUT A CONJUNCT IN THE WRONG SLOT, OR NAMED A TYPE
-- THAT IS NOT `InjCode`'s COMPONENT, THIS FILE WOULD NOT TYPECHECK.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-566.runs.Pin {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.Coding.Model {ℓ} using ( svAt; domAt )
open import L.Coding.Injection {ℓ} lem using ( injAt )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
import FOL.Absoluteness
open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

import LJ-1-566.Probe566 {ℓ} lem as P566

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- the assembled term, ascribed at `InjCode` and at nothing else
the-code :
    (a : S) (oa : IsOrd (fst a))
  → InjCode (P566.Carve.G a oa) a (P566.Carve.C a oa)
the-code = P566.injcode-assembled

-- and the four conjuncts, projected back out of it

conjunct-1-svAt :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ (P566.Carve.G a oa ∷ a ∷ []) ⊨ svAt zero ⟩
conjunct-1-svAt a oa = the-code a oa .fst

conjunct-2-domAt :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ (P566.Carve.G a oa ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩
conjunct-2-domAt a oa = the-code a oa .snd .fst

conjunct-3-injAt :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ (P566.Carve.G a oa ∷ a ∷ []) ⊨ injAt zero ⟩
conjunct-3-injAt a oa = the-code a oa .snd .snd .fst

conjunct-4-range :
    (a : S) (oa : IsOrd (fst a)) (x y : S)
  → ⟨ pr (fst x) (fst y) ∈ fst (P566.Carve.G a oa) ⟩
  → ⟨ fst y ∈ fst (P566.Carve.C a oa) ⟩
conjunct-4-range a oa = the-code a oa .snd .snd .snd

-- AND THE SHAPE THE NEXT CONSUMER WANTS: a truncated existential of a
-- code, which is what `IsCardinalL` (src/L/Cardinal.lagda.md:233-236)
-- and `InjL` (src/L/GCH.lagda.md:38) each quantify over.  NOT `InjL`:
-- this is the `Σ` under a truncation, and no `InjL` is formed.
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁; ∣_∣₁ )

some-code-exists :
    (a : S) (oa : IsOrd (fst a))
  → ∥ Σ[ F ∈ S ] InjCode F a (P566.Carve.C a oa) ∥₁
some-code-exists a oa = ∣ P566.Carve.G a oa , the-code a oa ∣₁
