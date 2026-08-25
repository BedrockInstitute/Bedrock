{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.639]  THE RESIDUE'S IDENTIFICATION, WRITTEN DOWN AS A TERM.
--
-- THE BRIEF'S OBLIGATION, re-stated VERBATIM:
--
--     residue-is-kappa-inj :
--       <a row proving `[LJ-1.618]`'s `Inj-extract` is EXACTLY the
--        untruncation of `src/L/SquareLawClosed.lagda.md`'s `κ-injL`,
--        at the same `a` and `oa`, stated so that `refl` closes it if
--        the two types agree>
--
-- THIS RECORDS A FACT.  IT ATTACKS NOTHING.  No row of this file
-- inhabits the residue, and no row of this file weakens it.  The one
-- thing the file adds to the tree is that the identification, which
-- until now existed only in prose (in this task's brief, and in
-- agents/tasks/LJ-1-618/Probe618.agda:147-150's comment), is now a
-- term the elaborator checks.
--
-- WHY A TERM AND NOT A SENTENCE.  [LJ-1.623] tied `SiteFiber` to
-- `PairingAt` with one refl row
-- (agents/tasks/LJ-1-623/Probe623.agda:95-96) and that row is why the
-- campaign stopped attacking the same object twice.  This is the same
-- move one level up, at the term `src/` actually carries.
--
--   Section 0.  The payload family, ANCHORED to src/'s own term.
--   Section 1.  Untruncation, as an OPERATOR and not a re-spelling.
--   Section 2.  THE ROW.  One refl.
--   Section 3.  The identification USED, in both directions, and fed
--               src/'s own delivered witness at the same a and oa.
--   Section 4.  WHERE THE TRUNCATION COMES FROM: `leastOf`'s hProp
--               interface, as two more refl rows.
--   Section 5.  WHAT THE RESIDUE DOES NOT TOUCH: the minimality half.
--   Section 6.  THE RESIDUE IS A RESTRICTION, not the general ask.
--
-- CALIBER.  THE PROGRAM SET GHCRTS ON THIS PANE.  I DID NOT SET IT.
-- ONE AGDA PROCESS AT A TIME.  The floor was measured BEFORE the
-- final form (Section 2's row holed), per the heavy-object rule, and
-- every run is recorded under runs/ with its cap.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import L.Constructible using ( IsOrd )

module LJ-1-639.Probe639 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Ordinal {ℓ} using ( ω-ord )
open import L.Cardinal {ℓ} lem using ( _↪_; module LeastCardInjL )
open import L.SquareLawClosed {ℓ} lem ω ω-ord using ( κL; κ-injL; κ-min-atL )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

import LJ-1-618.Probe618

module P618 = LJ-1-618.Probe618 lem

-- ===================================================================
-- SECTION 0.  THE PAYLOAD FAMILY, ANCHORED TO src/'s OWN TERM.
--
-- `KappaInj` names the untruncated payload at one site.  On its own a
-- name proves nothing: a re-spelling can drift from what `src/`
-- carries and still typecheck.  The row BELOW it is the anchor.
-- `κ-injL` is `src/L/SquareLawClosed.lagda.md:82-84`, re-ascribed at
-- this family, so the elaborator checks src/'s own term against the
-- name.  If `KappaInj` ever stopped being the payload of `κ-injL`'s
-- truncation, this row, not Section 2's, is what would go red first.
-- ===================================================================

KappaInj : (a : S) → IsOrd (fst a) → Type ℓ
KappaInj a oa = ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫

kappa-injL-delivers : (a : S) (oa : IsOrd (fst a)) → ∥ KappaInj a oa ∥₁
kappa-injL-delivers = κ-injL

-- ===================================================================
-- SECTION 1.  UNTRUNCATION, AS AN OPERATOR.
--
-- Stating the residue's type a second time by hand would make
-- Section 2's refl vacuous: two identical strings are equal whatever
-- either one means.  So the untruncation is written ONCE, generically,
-- over an arbitrary doubly-indexed family, and Section 2 applies it to
-- the family Section 0 anchored.  The only way the row can hold is if
-- the residue really is this operator at this family.
-- ===================================================================

UnTrunc : ((a : S) → IsOrd (fst a) → Type ℓ) → Type (ℓ-suc ℓ)
UnTrunc T = (a : S) (oa : IsOrd (fst a)) → ∥ T a oa ∥₁ → T a oa

-- ===================================================================
-- SECTION 2.  THE ROW THIS TASK IS FOR.
--
-- [LJ-1.618]'s residue (agents/tasks/LJ-1-618/Probe618.agda:151-155)
-- IS the untruncation of `κ-injL`, at the same `a` and the same `oa`.
-- On the nose: `refl`, no transport and no unfolding hint.
-- ===================================================================

residue-is-kappa-inj : P618.Inj-extract ≡ UnTrunc KappaInj
residue-is-kappa-inj = refl

-- ===================================================================
-- SECTION 3.  THE IDENTIFICATION USED.
--
-- Section 2 is a path between types.  These three rows spend it as a
-- definitional equality, which is the form a later brief will want:
-- 3.1 and 3.2 pass a term across the identification with no coercion,
-- and 3.3 is the one that carries the brief's "at the same a and oa".
-- It feeds the residue src/'s OWN delivered witness, at the same two
-- arguments, and gets the untruncated injection out.  That is exactly
-- the application [LJ-1.618]'s descent case makes
-- (agents/tasks/LJ-1-618/Probe618.agda:204: `ext a ox (κ-injL a ox)`),
-- now stated as its own fact rather than buried in a recursion.
-- ===================================================================

residue→untrunc : P618.Inj-extract → UnTrunc KappaInj
residue→untrunc r = r

untrunc→residue : UnTrunc KappaInj → P618.Inj-extract
untrunc→residue u = u

residue-at-src-witness : P618.Inj-extract
                       → (a : S) (oa : IsOrd (fst a)) → KappaInj a oa
residue-at-src-witness ext a oa = ext a oa (kappa-injL-delivers a oa)

-- ===================================================================
-- SECTION 4.  WHERE THE TRUNCATION COMES FROM.
--
-- The brief's premise 3, as terms.  The `∥_∥₁` in the residue's
-- premise is NOT the injection's doing: it is `leastOf`'s INTERFACE.
-- `leastOf` takes an hProp-valued predicate, `Inj γ` is not one, so
-- `src/L/Cardinal.lagda.md:66-67` wraps it: `InjP γ = ∥ Inj γ ∥₁ ,
-- squash₁`.  4.1 says the residue's payload is `leastOf`'s predicate
-- payload at the site; 4.2 says the residue's premise is the
-- underlying type of `leastOf`'s hProp there.  Both on the nose.
--
-- These two rows are what makes the identification actionable rather
-- than decorative: they say the truncation is removable in principle
-- exactly where the hProp wrapper was added, and nowhere else.
-- ===================================================================

payload-is-leastOf-Inj :
    (a : S) (oa : IsOrd (fst a))
  → KappaInj a oa ≡ LeastCardInjL.Inj a oa (κL a oa)
payload-is-leastOf-Inj a oa = refl

premise-is-leastOf-InjP :
    (a : S) (oa : IsOrd (fst a))
  → ⟨ LeastCardInjL.InjP a oa (κL a oa) ⟩ ≡ ∥ KappaInj a oa ∥₁
premise-is-leastOf-InjP a oa = refl

-- ===================================================================
-- SECTION 5.  WHAT THE RESIDUE DOES NOT TOUCH.
--
-- The brief's premise 4.  `κ-inj` is the MEMBERSHIP half of `IsLeast`
-- alone, `fst (snd least)` (src/L/Cardinal.lagda.md:133-134); the
-- MINIMALITY half is `snd (snd least)`, exported separately as
-- `κ-min-at` and sealed at the L-carrier as `κ-min-atL`
-- (src/L/SquareLawClosed.lagda.md:86-89).  The residue quantifies over
-- the membership half and says nothing about minimality, so the row
-- below is the minimality half's type re-ascribed, UNCHANGED: it is
-- still truncated in its own premise and it is still available.
--
-- HONEST LIMIT.  `κ-injL` and `κ-min-atL` are `opaque`
-- (src/L/SquareLawClosed.lagda.md:72), so from outside the seal this
-- file can check the TYPES against src/ and not the bodies.  That
-- `κ-inj = fst (snd least)` is read at src/L/Cardinal.lagda.md:134 and
-- is not re-derived here.
-- ===================================================================

kappa-min-untouched :
    (a : S) (oa : IsOrd (fst a))
  → (δ : S) → ⟨ fst δ ∈ˢ fst (κL a oa) ⟩
  → ∥ ⟪ fst a ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
kappa-min-untouched = κ-min-atL

-- ===================================================================
-- SECTION 6.  THE RESIDUE IS A RESTRICTION.
--
-- For the next brief, so it does not have to re-derive this either.
-- The general untruncation of an ambient injection between two
-- ARBITRARY L-elements is written below, TYPE ONLY, and is NOT
-- inhabited by any row of this file.  The residue is its restriction
-- to the pairs `(a , κL a oa)`, so the implication runs one way only:
-- a route that inhabits the wide form inhabits the residue, and a
-- route that inhabits the residue gives nothing at any other pair.
-- Anyone pricing the residue against a general choice principle is
-- pricing the WIDE form, which is strictly more.
-- ===================================================================

Inj-extract-wide : Type (ℓ-suc ℓ)
Inj-extract-wide = (a b : S) → ∥ ⟪ fst a ⟫ ↪ ⟪ fst b ⟫ ∥₁
                             → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

wide→residue : Inj-extract-wide → P618.Inj-extract
wide→residue w a oa = w a (κL a oa)
