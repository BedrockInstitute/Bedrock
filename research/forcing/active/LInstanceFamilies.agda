{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track J, file 3 of 7. Tier 3 of the ground ledger at 𝒮ʟ: Collection, and
-- the record that Track C's `hereditary` consumes.
--
-- The mathematical question this file answers is the one the architecture's
-- section 1.2 isolates. Tier 3 adds Collection and nothing else, and Collection
-- is the ONE ordinary axiom that does not come off the strong record by
-- projection. The strong record's hasReplacement asks its formula to be
-- functional on the argument in the isContr sense, one output per input
-- (src/FOL/ZFModel.lagda.md:226-228); Bell's Collection asks only that each
-- input have SOME output, a truncated existential, and hands back a set
-- meeting each of those truncated classes. From "at least one" one cannot
-- manufacture "exactly one" without choosing, so the passage that worked for
-- pairing, union, separation and power fails here, and K1 measured that
-- failure rather than guessing it.
--
-- What does work at L is the direct argument, and it is the argument L uses
-- everywhere: reflect the matrix. For a fixed formula and a fixed environment
-- there is a LEAST constructible stage holding a witness (L.ExistentialReflection's
-- pickStage); the environments drawn from one stage form a SMALL family, so
-- their answering stages have a common ordinal bound (L.Ordinal's boundingOrd);
-- and that bound, realized as the stage set LsetS β, is a single member of the
-- model containing a witness for every member of the argument. Collection is
-- then read off. Smallness of the family of environments is the step that only
-- the concrete hierarchy supplies, which is the trap recorded in file 1.
--
-- PROVENANCE, stated so that nobody re-derives it. The proof of replacementL
-- below is K1's, at /tmp/bedrock-k1-probes/ProfileFromL.agda:120-186, where it
-- typechecked at exit 0 (chk-ProfileFromL.log). It is reproduced here rather
-- than imported because the K1 probe root is not on this compile root's include
-- path and because the K1 file also carries Infinity, Foundation and Choice,
-- three axioms that appear in no K3 tier and whose imports would enlarge this
-- file's dependency cone for nothing. Nothing in the argument is changed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LInstanceFamilies {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; IsOrd; Lset; Lset-mono; layer-trans; Lset-layer )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ using ( module At; _^_ )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Ordinal {ℓ} using ( boundingOrd; bound2 )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.ExistentialReflection {ℓ} lem
  using ( Sat; pickStage; pickStage-ord; pickWitness; LsetEnv; indexEnv; Below )

open import Cubical.Data.Unit using ( tt* )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

import NameKernel
import OrdinaryProfile
open import LInstanceSets {ℓ} lem using ( setsL )

module NK = NameKernel 𝒮ʟ
module OP = OrdinaryProfile 𝒮ʟ

open OP using ( Collection )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) hiding ( ¬_ )
open hPropStructure 𝒮ʟ
open At S id using ( _⊨_ )

-- ---------------------------------------------------------------------
-- Collection
-- ---------------------------------------------------------------------

-- Read the proof in four movements.
--
-- First, the argument `a` sits in a stage `sa`, its own earliest one, and by
-- transitivity of that stage every member of `a` sits there too. So the
-- environments the premise has to be applied at are all environments drawn
-- from one stage, and there is a small type of them: ⟪ Lset sa ⟫ ^ 1.
--
-- Second, `answer` sends each such environment to the stage that answers it.
-- The premise is a truncated existential, but pickStage does not choose a
-- witness: it names a stage, and pickWitness later produces the witness from
-- the truncation into a truncated conclusion. No host choice is made anywhere,
-- which is the ledger point the choice audit asks K3 to respect.
--
-- Third, boundingOrd bounds that small family of ordinals, and bound2 pushes
-- the bound past `sa` as well, so the single set LsetS β contains an answering
-- witness for every member of `a`.
--
-- Fourth, the member-witness clause transports along the fact that the
-- environment indexEnv produced for `x` is the environment `x ∷ []`, which is
-- where the small index and the host environment are reconciled.

replacementL : Collection
replacementL a φ total = ∣ boundStage , member-witness ∣₁
  where
  sa : V ℓ
  sa = stage (fst a) (a .snd)

  oSa : IsOrd sa
  oSa = stage-ord (fst a) (a .snd)

  fa∈sa : ⟨ fst a ∈ Lset sa ⟩
  fa∈sa = stage-mem (fst a) (a .snd)

  answer : ⟪ Lset sa ⟫ ^ 1 → V ℓ
  answer ms = pickStage φ (LsetEnv sa oSa ms)

  answered : Σ[ β ∈ V ℓ ] (IsOrd β
               × ((ms : ⟪ Lset sa ⟫ ^ 1) → ⟨ answer ms ∈ β ⟩)
               × ⟨ sa ∈ β ⟩)
  answered =
    let b = boundingOrd (⟪ Lset sa ⟫ ^ 1) answer
              (λ ms → pickStage-ord φ (LsetEnv sa oSa ms))
        m = bound2 (b .fst) sa (b .snd .fst) oSa
    in m .fst , (m .snd .fst , (λ ms →
         m .snd .fst .fst (b .snd .snd ms) (m .snd .snd .fst))
       , m .snd .snd .snd)

  β : V ℓ
  β = answered .fst

  oβ : IsOrd β
  oβ = answered .snd .fst

  boundStage : S
  boundStage = LsetS β oβ

  member-witness : (x : S) → ⟨ x ∈ˢ a ⟩
    → ⟨ ⋁ S (λ y → (y ∈ˢ boundStage) ⊓ ((y ∷ x ∷ []) ⊨ φ)) ⟩
  member-witness x x∈a =
    PT.map pack (pickWitness φ ρ₀ premise₀)
    where
    below : Below sa (x ∷ [])
    below = layer-trans (Lset-layer sa) x∈a fa∈sa , tt*

    chosen : Σ[ ms ∈ ⟪ Lset sa ⟫ ^ 1 ]
               (LsetEnv sa oSa ms ≡ (x ∷ []))
    chosen = indexEnv sa oSa (x ∷ []) below

    ρ₀ : S ^ 1
    ρ₀ = LsetEnv sa oSa (chosen .fst)

    e : ρ₀ ≡ (x ∷ [])
    e = chosen .snd

    premise₀ : ⟨ ⋁ S (λ y → (y ∷ ρ₀) ⊨ φ) ⟩
    premise₀ = subst ⟨_⟩
      (sym (cong (λ r → ⋁ S (λ y → (y ∷ r) ⊨ φ)) e)) (total x x∈a)

    ps∈β : ⟨ pickStage φ ρ₀ ∈ β ⟩
    ps∈β = answered .snd .snd .fst (chosen .fst)

    pack : Σ[ q ∈ S ] (⟨ fst q ∈ Lset (pickStage φ ρ₀) ⟩ × ⟨ Sat φ ρ₀ q ⟩)
         → Σ[ q ∈ S ] (⟨ q ∈ˢ boundStage ⟩ × ⟨ (q ∷ x ∷ []) ⊨ φ ⟩)
    pack (q , q∈ps , satq) =
      q , ( Lset-mono ps∈β q∈ps
          , subst ⟨_⟩ (cong (λ r → (q ∷ r) ⊨ φ) e) satq )

-- ---------------------------------------------------------------------
-- The tier 3 record, sealed
-- ---------------------------------------------------------------------

opaque
  familiesL : NK.Families
  familiesL = record
    { sets       = setsL
    ; hasCollect = replacementL }
