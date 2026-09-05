{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.487] PROBE.  CoverWitnessesInHull, the failing step of cover.
-- It runs in agents/tasks/LJ-1-487/ and lands nothing in src/.
--
--   STEP ONE, W3 FIRST  ord-by-wit.  Obligation omitted.
--                       wit at isOrdFo, not at a numeral formula.
--                       One ordinal in the hull. C-42: a numeral is
--                       not a general ordinal.
--
--   STEP TWO            CoverWitnessesInHull. See the report.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-487.Probe487 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∀̇∈; ∃̇_ )
open import FOL.Manipulation.Parameters using ( absFo; countFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isTransV; Lset; 𝒮ʟ )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( leastOf )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( Σ-syntax )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
module CS = hPropStructure 𝒮ʟ

-- W2: the ordinal formula once, generic in the constant domain.
-- Instantiated at ⊥* for wit. Same spelling as isOrdAt at
-- src/L/BoundedSubset.lagda.md:795-798, at Formula (⊥* {ℓ}) not
-- Formula (⊥* {ℓ-suc ℓ}).

isOrdFo : ∀ {ℓk} {K : Type ℓk} {n} (v : Fin n) → Formula K n
isOrdFo v =
    (∀̇∈ (var v) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc v)))))
  ∧̇ (∀̇∈ (var v) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

-- Telescope copied from src/L/BoundedSubset.lagda.md:903-914.
-- Nothing below module Condense is copied. levelIn is not a hypothesis.
-- cover is not a hypothesis.

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ

  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  open H.T using ( Code; val; wit; Sat; val-wit; inHull; _⊨₀_ )

  -- =====================================================================
  -- W3.  ord-by-wit.  Obligation omitted.
  -- =====================================================================

  φord : Formula (⊥* {ℓ}) 1
  φord = isOrdFo {K = ⊥* {ℓ}} {n = 1} zero

  emptySL : ASt.SL
  emptySL = ∅ , H.∅∈Lsetα

  sat-empty : ⟨ (emptySL ∷ []) ⊨₀ φord ⟩
  sat-empty =
    (λ x hx y hy →
      Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst hx)) )
    ,
    (λ x hx y hy z hz →
      Empty.rec (∅-empty (fst x) (∈∈ₛ {a = fst x} {b = ∅} .fst hx)) )

  w-ord : Sat 0 φord []
  w-ord = ∣ emptySL , sat-empty ∣₁

  c-ord : Code
  c-ord = wit 0 φord []

  found : Σ[ a ∈ ASt.SL ] _
  found = leastOf ASt.wL {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ []) ⊨₀ φord) w-ord

  isOrdFo-out : (a : ASt.SL) → ⟨ (a ∷ []) ⊨₀ φord ⟩ → IsOrd (fst a)
  isOrdFo-out a (htr , hmem) = atr , amem
    where
    atr : isTransV (fst a)
    atr {x} {y} y∈x x∈a =
      htr (x , ASt.Ltr {x = fst a} {y = x} x∈a (a .snd)) x∈a
          (y , ASt.Ltr {x = x} {y = y} y∈x
                 (ASt.Ltr {x = fst a} {y = x} x∈a (a .snd))) y∈x
    amem : (x : S) → ⟨ x ∈ˢ fst a ⟩ → isTransV x
    amem x x∈a {y} {z} z∈y y∈x =
      hmem (x , ASt.Ltr {x = fst a} {y = x} x∈a (a .snd)) x∈a
           (y , ASt.Ltr {x = x} {y = y} y∈x
                  (ASt.Ltr {x = fst a} {y = x} x∈a (a .snd))) y∈x
           (z , ASt.Ltr {x = y} {y = z} z∈y
                  (ASt.Ltr {x = x} {y = y} y∈x
                     (ASt.Ltr {x = fst a} {y = x} x∈a (a .snd)))) z∈y

  -- One ordinal in the hull, by wit at the ordinal formula.
  -- Not identified with a numeral. C-42.

  ord-by-wit : ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ) ∥₁
  ord-by-wit =
    ∣ fst (found .fst)
    , ( subst (λ z → ⟨ z ∈ˢ M ⟩)
          (cong fst (val-wit 0 φord [] w-ord))
          (inHull c-ord)
      , isOrdFo-out (found .fst) (found .snd .fst) ) ∣₁

  -- =====================================================================
  -- D-10.  The covering formula at the class carrier, packaged for wit.
  -- W2: isOrdFo is the generic ordinal formula, instantiated at CS.S.
  -- LsetGraphAt at src/L/Coding/Sequence.lagda.md:349. Packaging is
  -- absFo at src/FOL/Manipulation/Parameters.lagda.md:260, as [LJ-1.462]
  -- measured. This is not CoverWitnessesInHull. Sat at the hull's _⊨₀_
  -- is unbuilt: adequacy is at 𝒮ʟ (src/L/Hierarchy.lagda.md:334, :646).
  -- =====================================================================

  coverIndex : Formula CS.S 2
  coverIndex =
      isOrdFo {K = CS.S} {n = 2} zero
    ∧̇ ∃̇ ( LsetGraphAt {n = 3} zero (suc zero)
        ∧̇ (var (suc (suc zero)) ∈̇ var zero) )

  packagedCover : Formula (⊥* {ℓ}) (2 + countFo coverIndex)
  packagedCover = absFo {ℓz = ℓ} coverIndex

  -- Feed to wit. Extra Vec Code holds codes for the class-carrier
  -- constants. [LJ-1.474] filled that Vec for LsetGraph. This probe
  -- does not import that probe. The extra Vec is a parameter here.
  -- This term is not CoverWitnessesInHull.

  feed-cover : (c : Code) (cs : Vec Code (countFo coverIndex)) → Code
  feed-cover c cs = wit (suc (countFo coverIndex)) packagedCover (c ∷ cs)

  -- Step 4 of [LJ-1.484], the type that probe typechecked.
  -- Quote: agents/tasks/LJ-1-484/Probe484.agda:123-126.
  -- UNBUILT. Route 1 names the formula and does not discharge Sat.
  -- Route 2 needs M ≺_{Σ₁} L_lam at this language; the tree does not
  -- have it at this telescope. levelIn is not a hypothesis. cover is
  -- not a hypothesis. No term of this type. No second truncation.

  CoverWitnessesInHull : Type (ℓ-suc ℓ)
  CoverWitnessesInHull =
    (y : S) → ⟨ y ∈ˢ M ⟩
    → ∥ Σ[ γ ∈ S ] (⟨ γ ∈ˢ M ⟩ × IsOrd γ × ⟨ y ∈ˢ Lset γ ⟩) ∥₁

