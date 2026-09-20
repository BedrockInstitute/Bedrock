{-# OPTIONS --cubical --safe --guardedness #-}

-- O7, THE SUPPLY HALF. What the datum reduces to, and what it does not.
--
-- K6's ledger states the route as: "an internal description of `below` (or of
-- `i`), which composed with K4's `codeOf` and `describes` discharges every
-- sepΔ-shaped datum at once." This file makes the first half of that precise
-- and machine-checks it; the header of the second half records, with source,
-- the factor the ledger does not name.
--
-- STEP ONE, PROVED BELOW. Track E2 already exports the FORCED SET
-- (K6/ForcesTruth.agda:337-348): forcesSet φ ν is the ground set of conditions
-- forcing φ at ν, it is `below` at a value, and NO Separation is spent on it.
-- What varies, and what a single ground Separation cannot follow, is its
-- dependence on ν. So the whole of O7 is an INTERNAL GRAPH OF THAT OPERATOR:
--
--   setΔ         : ∀ {k} → Formula Nm k → Formula S (suc k)
--   setΔ-reading : ∀ {k} (φ) (ν) (w : S)
--                → ((w ∷ codesOf ν) ⊨ᴳ setΔ φ) ≡ (w ≈ˢ forcesSet φ ν)
--
-- and the step from there to forcesΔ is one existential and one Δ₀ membership,
-- which is what setΔ→forcesΔ below proves. Composing with O7/Definability.agda
-- this discharges sepΔ, powΔ and colΔ from setΔ alone.
--
-- STEP TWO, AND THE CORRECTION TO THE LEDGER. Unfolding Track E2,
--
--   forcesSet φ ν = below (val (srcOf φ) (envᴮ (ν ++ parsOf φ)))
--
-- (K6/ForcesTruth.agda:338 with K6/Definability.agda:89-90), so setΔ factors
-- into THREE internal descriptions, not two:
--
--   (a) below.  An internal graph of `below : Pt B → S`. FREE at the coded
--       completion, where below is fst and the graph is `var 0 ∈̇ var 1`,
--       Δ₀; a host field with no graph at the abstract frame
--       (K5/Frame.agda:199-201). This is the half the ledger names.
--   (b) val.    K4's codeOf and describes, K4/Compile.agda:1209-1214.
--       LANDED. This is the half the ledger names.
--   (c) envᴮ.   K5/ExtensionSat.agda:181-183 is envᴮ (σ ∷ ν) = ext-map σ ∷ …
--       and :179 is ext-map τ = trᴮ (fst τ) , …, so the environment codes that
--       reach `describes` are trᴮ of the name codes, while every consumer's
--       reading exposes the UNTRANSLATED code (`fst χ` at
--       K6/Separation.agda:282, `fst y` at K6/Power.agda:371, `fst τ` and
--       `fst χ` at K6/Replacement.agda:334). Since that slot is FREE, the
--       ground formula must compute trᴮ, so an internal graph of trᴮ on names
--       is a third datum. THE LEDGER DOES NOT NAME IT. trᴮ is itself [OPEN]
--       (obstruction O3b, K6/ForcesTruth.agda:287-293), it is a well founded
--       recursion over Child built on K3's tier 4 MemberImage
--       (TranslateForward.agda:185-188, TranslateReverse.agda:390-393), and it
--       is not the identity, so the factor does not vanish.
--
-- Consequence, and it is a measured negative: "an internal description of
-- below composed with codeOf and describes" is NOT by itself enough to supply
-- the datum. It is enough exactly when the translation layer is also
-- internally described. The value half is landed, the below half is free at
-- the coded completion, the translation half is unbuilt anywhere.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
open import Cubical.Functions.Logic using ( ⇔toPath )
import FOL.Semantics
import Cubical.HITs.PropositionalTruncation as PT
import O7.Definability
import CodedVocabulary

open PT using ( ∣_∣₁ )

module O7.Supply {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

private module SemG = FOL.Semantics (hPropAlgebra ℓ) 𝒮
open SemG using ( _^_ )
module SatG = SemG.At S id
open SatG using () renaming ( _⊨_ to _⊨ᴳ_ )

open Sat (hPropAlgebra ℓ) 𝒮 {K = S} id using ( Agrees; ⊨-rename )

open CodedVocabulary 𝒮 using ( isKPairΔ )

module O7C = O7.Definability 𝒮

module Reduce
  (IsNm : S → Ω)
  (paths : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  where

  open O7C.Names IsNm using ( Nm; codesOf )

  ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (paths x y)

  -- The insertion of the condition slot after the witness slot. K4/Compile's
  -- ρ₁ (:1213 region) at one fewer constant slot.

  ρS : ∀ {k} → Fin (suc k) → Fin (suc (suc k))
  ρS zero    = zero
  ρS (suc i) = suc (suc i)

  ρS-ag : ∀ {k} (w p : S) (xs : S ^ k) → Agrees ρS (w ∷ p ∷ xs) (w ∷ xs)
  ρS-ag w p xs zero    = refl
  ρS-ag w p xs (suc i) = refl

  module Step
    (Cond   : Type ℓ)
    (cnd    : Cond → S)
    (forces : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
    -- K6/ForcesTruth.agda:337-348, the forced set and its two entailments,
    -- verbatim up to `cnd` standing for that file's `fst`.
    (forcesSet : ∀ {k} → Formula Nm k → Vec Nm k → S)
    (forcesSet-in : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (p : Cond)
                  → ⟨ forces p φ ν ⟩ → ⟨ cnd p ∈ˢ forcesSet φ ν ⟩)
    (forcesSet-out : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (p : Cond)
                   → ⟨ cnd p ∈ˢ forcesSet φ ν ⟩ → ⟨ forces p φ ν ⟩)
    -- THE ONE DATUM THIS FILE REDUCES O7 TO.
    (setΔ : ∀ {k} → Formula Nm k → Formula S (suc k))
    (setΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (w : S)
                  → ((w ∷ codesOf ν) ⊨ᴳ setΔ φ) ≡ (w ≈ˢ forcesSet φ ν))
    where

    -- "some w is the forced set of φ at the names, and the condition is a
    -- member of it". The second conjunct is Δ₀ in the two slots.

    forcesΔ : ∀ {k} → Formula Nm k → Formula S (suc k)
    forcesΔ φ = ∃̇ (renameFo ρS (setΔ φ) ∧̇ (var (suc zero) ∈̇ var zero))

    forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                    → ((cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ) ≡ forces r φ ν
    forcesΔ-reading φ ν r =
      ⇔toPath {P = (cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ} {Q = forces r φ ν} to from
      where
        pick : Σ[ w ∈ S ] (⟨ (w ∷ cnd r ∷ codesOf ν) ⊨ᴳ renameFo ρS (setΔ φ) ⟩
                           × ⟨ cnd r ∈ˢ w ⟩)
             → ⟨ forces r φ ν ⟩
        pick (w , hs , hm) = forcesSet-out φ ν r
          (subst (λ u → ⟨ cnd r ∈ˢ u ⟩)
            (≈ˢ→≡ (subst ⟨_⟩
              (⊨-rename ρS (setΔ φ) (w ∷ cnd r ∷ codesOf ν) (w ∷ codesOf ν)
                 (ρS-ag w (cnd r) (codesOf ν))
               ∙ setΔ-reading φ ν w) hs))
            hm)

        to : ⟨ (cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ ⟩ → ⟨ forces r φ ν ⟩
        to = PT.rec (snd (forces r φ ν)) pick

        from : ⟨ forces r φ ν ⟩ → ⟨ (cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ ⟩
        from h = ∣ forcesSet φ ν , setPart , forcesSet-in φ ν r h ∣₁
          where
            setPart : ⟨ (forcesSet φ ν ∷ cnd r ∷ codesOf ν)
                          ⊨ᴳ renameFo ρS (setΔ φ) ⟩
            setPart = subst ⟨_⟩
              (sym (⊨-rename ρS (setΔ φ)
                      (forcesSet φ ν ∷ cnd r ∷ codesOf ν)
                      (forcesSet φ ν ∷ codesOf ν)
                      (ρS-ag (forcesSet φ ν) (cnd r) (codesOf ν))
                    ∙ setΔ-reading φ ν (forcesSet φ ν)))
              (subst ⟨_⟩ (sym (paths (forcesSet φ ν) (forcesSet φ ν))) refl)

    ----------------------------------------------------------------------
    -- The three projections, now standing on setΔ alone.
    ----------------------------------------------------------------------

    module Projections
      (entry         : S → S → S)
      (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
      (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
      (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
      where

      open O7C.Names.Kernel.Datum IsNm entry entry-isKPair kpair-unique
             entry-inj Cond cnd forces forcesΔ forcesΔ-reading
        public using ( sepΔ; sepΔ-reading; powΔ; powΔ-reading
                     ; colΔ; colΔ-reading )

  --------------------------------------------------------------------------
  -- THE CHAIN, AND WHAT IS ACTUALLY MISSING
  --------------------------------------------------------------------------

  -- The ledger's route, assembled. Reading the telescope top to bottom: the
  -- forced set is `below` at the compiled value (K6/ForcesTruth.agda:338 with
  -- K6/Definability.agda:89-90); `below` is co-extensional with the CODE of
  -- that value, which is exactly K5's CodeOfBelow and BelowOfCode
  -- (K5/Truth.agda:184-188), discharged by the identity function at
  -- K5/InstanceBase.agda:361-368; and the value's code has an internal graph,
  -- which is K4's codeOf and describes.
  --
  -- So belowΔ below is BUILT, not assumed: `var 0 ∈̇ var 1` is a correct
  -- internal graph of `below`, and the pair of entailments that says so is
  -- already a K5 datum with a discharged instance. The ledger's "an internal
  -- description of below ... is missing" does not hold.
  --
  -- What IS missing is the last parameter, valΔ: K4's describes reads at
  -- (b ∷ B ∷ codes ν) where ν is a Vec of B-side names, and Track E2 feeds it
  -- envᴮ (ν ++ parsOf φ), whose codes are trᴮ of the P-side codes
  -- (K5/ExtensionSat.agda:179, :181-183). Every consumer's reading exposes the
  -- UNTRANSLATED code. So valΔ is describes with the environment translation
  -- internalized, and trᴮ is a well founded recursion over child-wf whose step
  -- relabels each weight by iCode, the code of the frame's embedding
  -- (TranslateForward.agda:387-388, :409, :343). An internal graph of trᴮ
  -- therefore needs an internal graph of `i` AND the definability of that
  -- recursion. That is the residue, and it is the factor the ledger does not
  -- name.

  module Chain
    (Cond   : Type ℓ)
    (cnd    : Cond → S)
    (forces : ∀ {k} → Cond → Formula Nm k → Vec Nm k → Ω)
    (Pt     : Type ℓ)
    (ptCode : Pt → S)
    (below  : Pt → S)
    (valAt  : ∀ {k} → Formula Nm k → Vec Nm k → Pt)
    (forces-below : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                  → ⟨ forces r φ ν ⟩ → ⟨ cnd r ∈ˢ below (valAt φ ν) ⟩)
    (below-forces : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                  → ⟨ cnd r ∈ˢ below (valAt φ ν) ⟩ → ⟨ forces r φ ν ⟩)
    (cob : (b : Pt) (x : S) → ⟨ x ∈ˢ below b ⟩ → ⟨ x ∈ˢ ptCode b ⟩)
    (boc : (b : Pt) (x : S) → ⟨ x ∈ˢ ptCode b ⟩ → ⟨ x ∈ˢ below b ⟩)
    (valΔ : ∀ {k} → Formula Nm k → Formula S (suc k))
    (valΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (w : S)
                  → ((w ∷ codesOf ν) ⊨ᴳ valΔ φ) ≡ (w ≈ˢ ptCode (valAt φ ν)))
    where

    -- The internal graph of `below`, built from the K5 pair.

    belowΔ : Formula S 2
    belowΔ = var zero ∈̇ var (suc zero)

    belowΔ-reading : (b : Pt) (p : S)
                   → ((p ∷ ptCode b ∷ []) ⊨ᴳ belowΔ) ≡ (p ∈ˢ below b)
    belowΔ-reading b p =
      ⇔toPath {P = p ∈ˢ ptCode b} {Q = p ∈ˢ below b} (boc b p) (cob b p)

    forcesΔ : ∀ {k} → Formula Nm k → Formula S (suc k)
    forcesΔ φ = ∃̇ (renameFo ρS (valΔ φ) ∧̇ (var (suc zero) ∈̇ var zero))

    forcesΔ-reading : ∀ {k} (φ : Formula Nm k) (ν : Vec Nm k) (r : Cond)
                    → ((cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ) ≡ forces r φ ν
    forcesΔ-reading φ ν r =
      ⇔toPath {P = (cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ} {Q = forces r φ ν} to from
      where
        pick : Σ[ w ∈ S ] (⟨ (w ∷ cnd r ∷ codesOf ν) ⊨ᴳ renameFo ρS (valΔ φ) ⟩
                           × ⟨ cnd r ∈ˢ w ⟩)
             → ⟨ forces r φ ν ⟩
        pick (w , hs , hm) = below-forces φ ν r
          (boc (valAt φ ν) (cnd r)
            (subst (λ u → ⟨ cnd r ∈ˢ u ⟩)
              (≈ˢ→≡ (subst ⟨_⟩
                (⊨-rename ρS (valΔ φ) (w ∷ cnd r ∷ codesOf ν) (w ∷ codesOf ν)
                   (ρS-ag w (cnd r) (codesOf ν))
                 ∙ valΔ-reading φ ν w) hs))
              hm))

        to : ⟨ (cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ ⟩ → ⟨ forces r φ ν ⟩
        to = PT.rec (snd (forces r φ ν)) pick

        from : ⟨ forces r φ ν ⟩ → ⟨ (cnd r ∷ codesOf ν) ⊨ᴳ forcesΔ φ ⟩
        from h = ∣ ptCode (valAt φ ν) , valPart
                 , cob (valAt φ ν) (cnd r) (forces-below φ ν r h) ∣₁
          where
            valPart : ⟨ (ptCode (valAt φ ν) ∷ cnd r ∷ codesOf ν)
                          ⊨ᴳ renameFo ρS (valΔ φ) ⟩
            valPart = subst ⟨_⟩
              (sym (⊨-rename ρS (valΔ φ)
                      (ptCode (valAt φ ν) ∷ cnd r ∷ codesOf ν)
                      (ptCode (valAt φ ν) ∷ codesOf ν)
                      (ρS-ag (ptCode (valAt φ ν)) (cnd r) (codesOf ν))
                    ∙ valΔ-reading φ ν (ptCode (valAt φ ν))))
              (subst ⟨_⟩ (sym (paths (ptCode (valAt φ ν)) (ptCode (valAt φ ν)))) refl)

    -- The three projections, now standing on valΔ alone.

    module Projections
      (entry         : S → S → S)
      (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
      (kpair-unique  : (q x b : S) → ⟨ isKPairΔ q x b ⟩ → q ≡ entry x b)
      (entry-inj     : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
      where

      open O7C.Names.Kernel.Datum IsNm entry entry-isKPair kpair-unique
             entry-inj Cond cnd forces forcesΔ forcesΔ-reading
        public using ( sepΔ; sepΔ-reading; powΔ; powΔ-reading
                     ; colΔ; colΔ-reading )
