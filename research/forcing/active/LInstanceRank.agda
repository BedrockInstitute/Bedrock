{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track J, file 4 of 7. Section 1.12: the rank drop along the subname
-- relation, at the L instance, where `rank` is ambient.
--
-- THE QUESTION. K3 defines no ground-valued rank on names, and section 1.12
-- explains why: host accessibility already carries every recursion in the
-- package, which is the formal content of Bell 1.7. So what is a rank
-- statement for, and why exactly one?
--
-- It is for the ONE thing accessibility does not give: a MEASURE, an ordinal
-- that drops at each step and can therefore be compared, bounded and counted.
-- Accessibility says a descent terminates; it does not say how far down a
-- subname sits, and a later package that wants "the translation of a name has
-- rank at most γ + rank τ" (architecture N3) is asking a question
-- accessibility cannot hear. This file proves the smallest true statement of
-- that kind and refuses the rest: the ambient rank of a subname is a member
-- of the ambient rank of the name.
--
-- WHY IT IS NOT AVAILABLE AT AN ARBITRARY GROUND. `rank` is the ambient V
-- rank (src/L/Rank.lagda.md:99), defined by recursion on the hierarchy's own
-- membership through the small index ⟪ x ⟫. An arbitrary ground has no such
-- thing: it is a carrier with two relations, and nothing in the tier records
-- produces an ordinal-valued measure on it. That is the exact sense in which
-- section 1.12's statement is marked "at the L instance only", and it is the
-- second half of the trap recorded in file 1.
--
-- THE PROOF IS THREE MEMBERSHIPS, and they are K0's own chain. An entry of a
-- name is the Kuratowski pair {{x},{x,b}}, so a subname x lies three steps
-- below the name: x ∈ {x} ∈ entry x b ∈ n. Rank increases strictly along
-- membership (rank-mono) and ranks are ordinals, hence transitive, so a chain
-- of three memberships collapses to one membership of ranks; `trans≺`
-- (src/L/Coding/Descent.lagda.md:88) is exactly that collapse, packaged. The
-- architecture proposes routing the same fact through the coded pair `prʟ` and
-- `pair-component≺`; that route is available and costs one extra bridge lemma,
-- `entry x b ≡ prʟ x b`, from K0's CoordinateDecoder. It is not taken, because
-- the kernel's own `entry-left` and `singleOf-member` already expose the two
-- inner memberships, and the shorter route reads the entry through its
-- membership specification rather than through its identification with another
-- pair construction. Three lemmas instead of five, and no dependence on which
-- pair encoding the coding chapter chose.

open import Base.Prelude
open import Base.Truth

module LInstanceRank {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Rank {ℓ} using ( rank; rank-mono )
open import L.Coding.Descent {ℓ} using ( trans≺ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT

import NameKernel
open import LInstanceCore {ℓ} using ( coreL; accessL )

module NK = NameKernel 𝒮ʟ

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )
open hPropStructure 𝒮ʟ

-- ---------------------------------------------------------------------
-- The statement, against the kernel's interface and not against the kernel
-- ---------------------------------------------------------------------

-- Every upstream object this proof needs is a parameter: the entry, the
-- singleton, the two membership laws, the subname relation and its
-- eliminator. Nothing here can break if Track A changes how the entry is
-- built, so long as the entry still contains the singleton and the singleton
-- still contains its point. The instantiation at the bottom of the file is
-- the only line that knows which kernel is meant.
--
-- Read the telescope as the mathematical hypothesis it is: "the code of a
-- weighted entry contains the code of the singleton of its first coordinate,
-- and that singleton contains the coordinate". That, and the well-foundedness
-- of the ambient membership, is the whole content of the descent.

module Drop
  (entry          : S → S → S)
  (singleOf       : S → S)
  (singleOf-member : (x : S) → ⟨ x ∈ˢ singleOf x ⟩)
  (entry-left     : (x b : S) → ⟨ singleOf x ∈ˢ entry x b ⟩)
  (Child          : S → S → Type (ℓ-suc ℓ))
  (child-entry    : (x n : S) → Child x n
                  → PT.∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁)
  where

  -- The untruncated half. Note that the three arguments of each `trans≺` are
  -- underlying V sets: 𝒮ʟ inherits membership along the first projection, so
  -- ⟨ u ∈ˢ v ⟩ at L IS ⟨ fst u ∈ fst v ⟩ at V, and no transport is needed at
  -- this crossing. The rank that appears is the ambient one throughout; no
  -- constructible stage is mentioned, and architecture N4 forbids identifying
  -- the two without a comparison theorem that does not yet exist.

  entry-rank-drop : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩
                  → ⟨ rank (fst x) ∈ rank (fst n) ⟩
  entry-rank-drop x b n h =
    trans≺ (fst x) (fst (singleOf x)) (fst n) (singleOf-member x)
      (trans≺ (fst (singleOf x)) (fst (entry x b)) (fst n) (entry-left x b)
        (rank-mono (fst (entry x b)) (fst n) h))

  -- The weight is truncated inside Child, and it must stay truncated: a
  -- subname may sit in a name under many weights and the kernel makes no
  -- choice among them. The elimination is legitimate here for the same reason
  -- it is legitimate in the kernel's own descent proof, namely that the
  -- conclusion is a membership, hence a proposition; the weight never escapes.

  child-rank-drop : (x n : S) → Child x n → ⟨ rank (fst x) ∈ rank (fst n) ⟩
  child-rank-drop x n c =
    PT.rec (snd (rank (fst x) ∈ rank (fst n)))
      (λ { (b , h) → entry-rank-drop x b n h })
      (child-entry x n c)

-- ---------------------------------------------------------------------
-- At the kernel
-- ---------------------------------------------------------------------

-- One module application, and the weight carrier is still free: the subname
-- relation does not mention W, so the rank drop holds for the poset-weighted
-- and the Boolean-weighted hierarchy at once, with one proof. That is the
-- same economy the kernel itself is built for.

module AtKernel (W : S) where

  module K = NK.Kernel coreL accessL W

  open Drop K.entry K.singleOf K.singleOf-member K.entry-left K.Child
       (λ _ _ c → c) public

-- ---------------------------------------------------------------------
-- The unfilled contract of section 1.12
-- ---------------------------------------------------------------------

-- Section 1.12 asks K3 for exactly two things: the comparison theorem above,
-- and a contract that K3 does not fill. Here is the contract. It is stated
-- over an arbitrary ground and an arbitrary name layer, because its whole
-- purpose is to be filled by a LATER package at whatever ground that package
-- has, and it is stated with the ordinality reading as a parameter because
-- the reading is a fact about a formula and not about names; at L the reading
-- to pass is CardinalBridge's `IsOrdinalφ` through its adequacy theorem
-- (CardinalBridge.agda:522,538).
--
-- What the contract asks for is a GROUND-VALUED rank: an ordinal code inside
-- the model, assigned to each name, dropping at each entry. That is strictly
-- more than this file proves. The theorem above compares AMBIENT ranks of
-- codes, which is a statement in the metatheory about two V sets; a filler of
-- this record must produce an object of the model and prove the model thinks
-- it is an ordinal.

module Contract
  {ℓn} (Name : Type ℓn) (Index : Name → Type ℓn)
  (child : (τ : Name) → Index τ → Name)
  (isOrdinalᴵ : S → Ω)
  where

  record NameRankContract : Type (ℓ-max ℓn (ℓ-suc ℓ)) where
    field
      rkᴺ      : Name → S
      rkᴺ-ord  : (τ : Name) → ⟨ isOrdinalᴵ (rkᴺ τ) ⟩
      rkᴺ-mono : (τ : Name) (i : Index τ) → ⟨ rkᴺ (child τ i) ∈ˢ rkᴺ τ ⟩

-- TWO SIGNATURES THAT MUST NOT EXIST, in K3 and in any filler of the record
-- above that does not carry its own proved comparison theorem:
--
--   rkᴺ-is-rank  : (τ : Name) → rkᴺ τ ≡ rank (fst τ)
--   rkᴺ-is-stage : (τ : Name) → rkᴺ τ ≡ stage (fst τ) _
--
-- Architecture N4 measured why, and the measurement is a pair of greps rather
-- than an opinion: nothing in the tree relates the ambient rank to the
-- constructible stage. `rank` is L.Rank's ambient measure with rank-mono and
-- rank-ord; `stage` is L.Stage's earliest constructible layer with stage-ord,
-- stage-mem and stage-earliest; and no theorem anywhere compares them. A
-- filler that silently identifies its rkᴺ with either is unsound until such a
-- theorem exists, so the prohibition travels with the record.
