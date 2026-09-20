{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track J, file 7 of 7. The ledger in one place, and the machine-checked
-- claim that it fits.
--
-- The four tier records and accessibility are proved in files 1, 2, 3 and 5.
-- Collecting them here is bookkeeping; what is NOT bookkeeping is the second
-- half of the file. A tier record that typechecks proves that the L instance
-- has the right SHAPE. It does not prove that the shape is the one the
-- consumers want, and in a package where four separate files each restate a
-- ground ledger in their own module telescope, "the right shape" is exactly
-- the claim that goes wrong silently. So the bottom of this file applies
-- Track B's and Track C's own instantiation modules to the records proved
-- here. If the application typechecks, the correspondence across five files
-- is machine checked and not read off by eye. Track C made the same move at
-- the same seam for the same reason (NameSpace.agda:841).
--
-- THE HEAP. This is the file the architecture calls the heap risk of the
-- package, and it is the one where the risk is real rather than inherited:
-- everything above it either stays at the tier records or applies the kernel
-- alone, while this file drives the whole name apparatus over the
-- constructible ground. The mitigation is the one K0 measured, and it is
-- structural rather than a flag: every tier record it passes in was sealed at
-- its point of definition, so what reaches the elaborator is five constants,
-- not five unfoldings of the L model. The measured outcome is in REPORT-J.md.
--
-- What this file deliberately does NOT do: it does not fix a weight carrier,
-- it does not build a completion, and it does not name a single name. The
-- weight carrier stays a module parameter, because the ground ledger is the
-- same for the poset-weighted and the Boolean-weighted hierarchy and pinning
-- one here would halve the value of the file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LInstanceGround {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import L.Constructible {ℓ} using ( 𝒮ʟ )

import NameKernel
import NameSupport
import NameSpace

module NK = NameKernel 𝒮ʟ

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )
open hPropStructure 𝒮ʟ

-- ---------------------------------------------------------------------
-- The ledger
-- ---------------------------------------------------------------------

-- Tier 0 and tier 1 are free of the excluded middle; tiers 2 and 3 take the
-- one LEM (ℓ-suc ℓ) that L⊨ZFC already takes; tier 4 is not here, and file 5
-- proves why it cannot be.

open import LInstanceCore {ℓ}
  using ( accessL; coreL; extensionalityL; pairingL; unionL; ≈ˢ-pathsL ) public
open import LInstanceSets {ℓ} lem
  using ( setsL; separationL; powerL ) public
open import LInstanceFamilies {ℓ} lem
  using ( familiesL; replacementL ) public

-- ---------------------------------------------------------------------
-- The tiers fit their consumers
-- ---------------------------------------------------------------------

-- Track B's Instantiate takes a tier 2 record, accessibility and a weight
-- carrier, and returns the whole support apparatus over them; Track C's takes
-- a tier 3 record and returns the closed families, the recognizer and the
-- name bound. Applying both to the records above is the test, and the test is
-- that the application elaborates at all: an L instance whose Separation had
-- the wrong environment shape, or whose ≈ˢ realization went through the wrong
-- equality, would fail here and nowhere earlier.

module Support (W : S) where
  open NameSupport.Instantiate 𝒮ʟ setsL accessL W public

module Space (W : S) where
  open NameSpace.Instantiate 𝒮ʟ familiesL accessL W public

-- The bound of section 1.6 is the one declaration in Track C that takes a
-- power set as an argument rather than reading it off a tier, so the L
-- instance supplies it here, at the point where the two meet.

nameBoundL : (W : S) (C : S) → S
nameBoundL W = Space.nameBound W powerL
