{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track J, file 1 of 7. Tier 0 and tier 1 of the ground ledger, discharged
-- at the constructible structure 𝒮ʟ = 𝒮ᵥ ↾ isL (src/L/Constructible.lagda.md:414-415).
--
-- THE TRAP THIS FILE EXISTS TO MAKE HARMLESS, stated once for the whole track.
-- This file and its six siblings import V.Hierarchy, V.Presentation and the
-- L.* chapters. That is CORRECT HERE and would have been WRONG in Tracks A to
-- I. Smallness and the small presentation of a set are facts about the
-- concrete cumulative hierarchy, not about an arbitrary ground: every set of
-- V is `sett X ix` for a SMALL index type, and nothing in ZFStructure or in
-- the ordinary profile says so. A K3 module that took an arbitrary ground and
-- reached for ⟪ a ⟫ would be proving its theorem about one model and stating
-- it about all of them, and because the two statements have the same type,
-- the typechecker would not object. Tracks A to I did not do this, measured:
-- their reports record zero occurrences of `import V.` and `import L.`. Track
-- J is the file where the ground STOPS being arbitrary, so here the import is
-- the content and not a leak. A later reviewer meeting `V.Presentation` in
-- LInstanceImage.agda should read this paragraph before raising an alarm.
--
-- Two more things this file fixes for the rest of the track.
--
-- The structure equality at L is NOT reflexivity. 𝒮ʟ inherits ≈ˢ from 𝒮ᵥ along
-- the first projection, so ⟨ x ≈ˢ y ⟩ is `fst x ≡ fst y`, while the kernel's
-- ≈ˢ-paths field asks for a path of TRUTH VALUES between that and `x ≡ y`.
-- The two are equivalent and not definitionally equal: the restriction's
-- reflection lemma (FOL/ZFStructure.lagda.md:194-197) supplies one direction,
-- `cong fst` the other, and ⇔toPath packages them. Two lines, and neither is
-- `refl`.
--
-- Tier 0 and tier 1 cost NO excluded middle. Accessibility, extensionality,
-- pairing and union are all theorems of L.Axioms.Basic, whose module
-- telescope is `{ℓ : Level}` and nothing else. The single LEM (ℓ-suc ℓ) that
-- L⊨ZFC takes enters this track only at tier 2 (Separation) and tier 3
-- (Collection). This is a genuine narrowing of the architecture's ledger and
-- it is measured by the import list below, not asserted.

open import Base.Prelude
open import Base.Truth

module LInstanceCore {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; ↾-reflects; module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL )
open import L.Axioms.Basic {ℓ}
  using ( extensionalL; regularityL; hasPairL; hasUnionL )

open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

import NameKernel
import OrdinaryProfile

module NK = NameKernel 𝒮ʟ
module OP = OrdinaryProfile 𝒮ʟ

open OP using ( Extensionality; Pairing; Union; iff-to-spec; spec-to-iff )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )
open hPropStructure 𝒮ʟ

-- ---------------------------------------------------------------------
-- Tier 0. Accessibility
-- ---------------------------------------------------------------------

-- The realization datum, and the one tier that is not a first-order axiom at
-- all. The ordinary profile carries only the induction schema, which returns
-- a truth value and no host Acc; at L the host Acc is available because the
-- hierarchy's own membership is well founded (V/Hierarchy.lagda.md:153,
-- `regularityV`) and the restriction inherits it pointwise
-- (src/L/Axioms/Basic.lagda.md:488-489). No excluded middle.

accessL : NK.Accessibility
accessL = regularityL

-- ---------------------------------------------------------------------
-- The path realization of ≈ˢ
-- ---------------------------------------------------------------------

-- Not refl. See the header. ↾-reflects is Σ≡Prop at the propositional class
-- isL, so the forward direction is where "membership in L is proof
-- irrelevant" is spent.

≈ˢ-pathsL : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y)
≈ˢ-pathsL x y = ⇔toPath (↾-reflects {𝒮 = 𝒮ᵥ} {M = isL} {a = x} {b = y}) (cong fst)

-- ---------------------------------------------------------------------
-- Tier 1. Extensionality, Pairing
-- ---------------------------------------------------------------------

-- Three remarks on the shape of these three proofs, because the same shape
-- recurs in files 2, 3 and 4.
--
-- The strong record states an axiom as `isContr (SetOf Q)`, a contractible
-- type of realizers; the ordinary profile states it as the host reading of a
-- first-order sentence, a TRUNCATED existential of a set whose membership is
-- an internal biconditional. Passing from the first to the second is
-- therefore two moves and never more: project the centre of the contraction,
-- and turn its pointwise path specification into the biconditional with
-- `spec-to-iff`. Nothing is lost in that direction, and K1 measured that the
-- converse direction fails for Replacement.
--
-- Extensionality is the one that does not fit that pattern, because it is not
-- an existence statement. L.Axioms.Basic proves it in the host form "members
-- agree implies equal"; the ordinary form wants the internal biconditional as
-- hypothesis and ⟨ a ≈ˢ b ⟩ as conclusion, so `iff-to-spec` converts the
-- hypothesis inward and `cong fst` converts the conclusion outward. The
-- `cong fst` is the same fact as ≈ˢ-pathsL, spelled at one point instead of
-- as a path of truth values.

extensionalityL : Extensionality
extensionalityL a b same = cong fst (extensionalL {a = a} {b = b} (iff-to-spec a b same))

pairingL : Pairing
pairingL a b = ∣ p , spec-to-iff p _ sp ∣₁
  where
  p  = hasPairL a b .fst .fst
  sp = hasPairL a b .fst .snd

-- Union is proved here rather than in file 2 because it is LEM free and
-- belongs with its neighbours; tier 2 consumes it.

unionL : Union
unionL a = ∣ v , spec-to-iff v _ sp ∣₁
  where
  v  = hasUnionL a .fst .fst
  sp = hasUnionL a .fst .snd

-- ---------------------------------------------------------------------
-- The tier 1 record, sealed
-- ---------------------------------------------------------------------

-- THE SEAL, and the reason it is not style. Exposing a full L model to the
-- typechecker exhausted the fixed 8 GB heap at exit 251 twice
-- (k0-material-names-value-sets-2026-09.md:94), and the version that compiled
-- sealed the proved ground record and unfolded it only locally. Every
-- consumer of this record reaches its fields through the kernel's module
-- telescope, where they are neutral variables; none needs an unfolding, and
-- an unfolding is exactly what nests the L hierarchy inside every definitional
-- comparison the name kernel performs. The same discipline, at the same
-- object, is what K0's own NameClosureStep.agda does with `opaque ground`.

opaque
  coreL : NK.Core
  coreL = record
    { extensional = extensionalityL
    ; hasPair     = pairingL
    ; ≈ˢ-paths    = ≈ˢ-pathsL }
