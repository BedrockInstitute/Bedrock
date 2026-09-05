{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.517] PROBE.  A witness for ApproxAt that lies in the stage and is
-- NOT hierL, the door [LJ-1.494] left open.  It runs in
-- agents/tasks/LJ-1-517/ and lands nothing in src/.
--
--   W3, FIRST      the census: every set in src/ that ApproxAt holds of,
--                  and whether the tree bounds it by a stage.
--   OBLIGATION     approx-in-stage.  Added after W3 is measured.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-517.Probe517 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd; 𝒟ₒ; Lset-out; 𝒟ₒ∋⊆
        ; layer-trans; Lset-layer )
open import L.Hierarchy {ℓ} lem
  using ( hierL; hierL-spec; IsHier; Values; Entries; Domain
        ; graph-table; approx-val; Lset-defines )
open import L.Coding.Sequence {ℓ} lem
  using ( StepAt; ApproxAt; ApproxAt-value; ApproxAt-in; LsetGraphAt )
open import L.Choice.Before {ℓ} lem using ( approxSet; smallStage )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax )
import Cubical.Data.Sum as Sum
open Sum using ( inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- ===================================================================
-- W3.  THE CENSUS, AS CHECKED TYPE ASCRIPTIONS.
--
-- Each row below is a name delivered by src/ re-declared at the type
-- this census claims for it.  A row that typechecks is evidence; a
-- comment is not.  The census question is: which sets does the tree
-- ever exhibit as an approximation, and which of them does it bound
-- by a stage?
-- ===================================================================

private

  -- ROW 1.  hierL, the internal hierarchy.  src/L/Hierarchy.lagda.md:621.
  -- It is the ONLY set the tree exhibits as an approximation of the
  -- L-tower.  Its specification is a membership equivalence, not a
  -- stage bound.
  row1-hierL : (α : V ℓ) (hα : ⟨ isL α ⟩) (oα : IsOrd α)
             → IsHier α (hierL α hα oα)
  row1-hierL = hierL-spec

  -- ROW 2.  THE WITNESS SLOT IS ALREADY GENERIC.  graph-table takes the
  -- approximation h as a PARAMETER: src/L/Hierarchy.lagda.md:382.  Any
  -- correct, complete, domain-pinned table on the argument serves.  The
  -- door [LJ-1.494] named is open at the level of the interface.
  row2-generic : {n : ℕ} (w b : Fin n) (γ : S ^ n)
               → (h : S) → IsOrd (fst (lookup b γ))
               → Values h (fst (lookup b γ)) → Entries h (fst (lookup b γ))
               → Domain h (fst (lookup b γ))
               → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
               → ⟨ γ ⊨ LsetGraphAt w b ⟩
  row2-generic = graph-table

  -- ROW 3.  Lset-defines, the ONE call site that fills the slot for the
  -- L-tower.  src/L/Hierarchy.lagda.md:646.  Its witness is hierL
  -- (src/L/Hierarchy.lagda.md:653).  There is no other call site: the
  -- construction at src/L/Hierarchy.lagda.md:560 passes the induction
  -- hypothesis's hierAt, which is the same family.
  row3-only-call-site : {n : ℕ} (w b : Fin n) (γ : S ^ n)
                      → IsOrd (fst (lookup b γ))
                      → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
                      → ⟨ γ ⊨ LsetGraphAt w b ⟩
  row3-only-call-site = Lset-defines

  -- ROW 4.  approxSet, an approximation the tree builds that is NOT
  -- hierL.  src/L/Choice/Before.lagda.md:1035.  It approximates the
  -- relAt recursion, not the L-tower, and it is indexed by a NUMERAL,
  -- so it is finite.  This row is the census's only negative answer to
  -- "is hierL the only approximation the tree ever builds".
  row4-approxSet : ℕ → S
  row4-approxSet = approxSet

  -- ROW 5.  AND IT IS STAGE-BOUNDED, but by an ordinal the construction
  -- CHOOSES.  src/L/Choice/Before.lagda.md:1013.  smallStage takes a
  -- small family and returns SOME σ that bounds it.  It never bounds a
  -- family by a stage given in advance.  That is the whole distance
  -- between row 4 and the obligation.
  row5-smallStage : (X : Type ℓ) (g : X → S)
                  → Σ[ σ ∈ V ℓ ] (IsOrd σ × ((x : X) → ⟨ fst (g x) ∈ Lset σ ⟩))
  row5-smallStage = smallStage

  -- ROW 6.  The reading that turns an approximation into its pairs.
  -- src/L/Coding/Sequence.lagda.md:298 and src/L/Hierarchy.lagda.md:274.
  -- These two are what the obligation would have to survive.
  row6-value : {n : ℕ} (f a : Fin n) (γ : S ^ n)
             → ⟨ γ ⊨ ApproxAt f a ⟩ → (c : S)
             → ⟨ fst c ∈ fst (lookup a γ) ⟩
             → ∥ (Σ[ z ∈ S ] ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩) ∥₁
  row6-value = ApproxAt-value

  row7-val : {n : ℕ} (f a : Fin n) (γ : S ^ n)
           → ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
           → (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst (lookup f γ) ⟩
           → fst z ≡ Lset (fst x)
  row7-val = approx-val


-- ===================================================================
-- THE OBLIGATION.  approx-in-stage: a witness for ApproxAt that lies
-- in the stage and is not hierL.
--
-- The brief writes ⟨ fst δ ∈ˢ Lset α ⟩.  𝒮ᵥ's ∈ˢ IS the base _∈_
-- (src/V/Hierarchy.lagda.md:83), and this file has 𝒮ʟ's ∈ˢ open, so
-- the V-level membership is spelled _∈_ throughout.
-- ===================================================================

module Obligation (α : V ℓ) where

  -- "f approximates the tower below δ" is the delivered ApproxAt at a
  -- two-slot environment: src/L/Coding/Sequence.lagda.md:286.
  Approximates : S → S → Type (ℓ-suc ℓ)
  Approximates δ f = ⟨ (f ∷ δ ∷ []) ⊨ ApproxAt zero (suc zero) ⟩

  -- THE BRIEF'S TYPE.  It forms.  It is NOT inhabited below, and no
  -- postulate stands in for it.
  ApproxInStage : Type (ℓ-suc ℓ)
  ApproxInStage = (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ Lset α ⟩
                → Σ[ f ∈ S ] (⟨ fst f ∈ Lset α ⟩ × Approximates δ f)

  private
    -- Every stage is transitive: src/L/Constructible.lagda.md:183,246.
    trα : {x y : V ℓ} → ⟨ y ∈ x ⟩ → ⟨ x ∈ Lset α ⟩ → ⟨ y ∈ Lset α ⟩
    trα = layer-trans (Lset-layer α)

    -- The two Kuratowski steps.  pr a b = ⁅ ⁅ a ⁆s , ⁅ a , b ⁆ ⁆,
    -- src/V/Coding.lagda.md:175-176.
    pairIn : (a b : V ℓ) → ⟨ ⁅ a , b ⁆ ∈ pr a b ⟩
    pairIn a b = ∈∈ₛ {a = ⁅ a , b ⁆} {b = pr a b} .snd
      (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ .snd ∣ inr refl ∣₁)

    sndIn : (a b : V ℓ) → ⟨ b ∈ ⁅ a , b ⁆ ⟩
    sndIn a b = ∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .snd
      (pairing-ax a b b .snd ∣ inr refl ∣₁)

    -- The pair the approximation must carry at every argument below δ.
    entryIn : (δ f : S) → IsOrd (fst δ) → Approximates δ f
            → (c : S) → ⟨ fst c ∈ fst δ ⟩
            → ⟨ pr (fst c) (Lset (fst c)) ∈ fst f ⟩
    entryIn δ f oδ ha c c∈ =
      PT.rec (snd (pr (fst c) (Lset (fst c)) ∈ fst f)) named
        (ApproxAt-value zero (suc zero) (f ∷ δ ∷ []) ha c c∈)
      where
      named : Σ[ z ∈ S ] ⟨ pr (fst c) (fst z) ∈ fst f ⟩
            → ⟨ pr (fst c) (Lset (fst c)) ∈ fst f ⟩
      named (z , p) = subst (λ t → ⟨ pr (fst c) t ∈ fst f ⟩)
        (approx-val zero (suc zero) (f ∷ δ ∷ []) ha oδ c z p) p

  -- THE REDUCTION, AND THE ANSWER TO THE BRIEF.  An approximation that
  -- lies in the stage forces the tower's value at EVERY argument below
  -- δ into the SAME stage.  That conclusion is levelIn below δ, and
  -- levelIn is a HYPOTHESIS everywhere it appears in the tree:
  -- src/L/BoundedSubset.lagda.md:917 and :1555.
  witness-forces-levelIn :
      (δ f : S) → IsOrd (fst δ) → Approximates δ f → ⟨ fst f ∈ Lset α ⟩
    → (c : S) → ⟨ fst c ∈ fst δ ⟩ → ⟨ Lset (fst c) ∈ Lset α ⟩
  witness-forces-levelIn δ f oδ ha hf c c∈ =
    trα (sndIn (fst c) (Lset (fst c)))
        (trα (pairIn (fst c) (Lset (fst c)))
             (trα (entryIn δ f oδ ha c c∈) hf))

  -- The same fact stated against the brief's own type.  ANY inhabitant
  -- of ApproxInStage, hierL or not, pays this price.
  obligation-gives-levelIn :
      ApproxInStage
    → (δ : S) → IsOrd (fst δ) → ⟨ fst δ ∈ Lset α ⟩
    → (c : S) → ⟨ fst c ∈ fst δ ⟩ → ⟨ Lset (fst c) ∈ Lset α ⟩
  obligation-gives-levelIn W δ oδ δ∈ =
    witness-forces-levelIn δ (W δ oδ δ∈ .fst) oδ
      (W δ oδ δ∈ .snd .snd) (W δ oδ δ∈ .snd .fst)

  -- HOW MUCH MORE THAN levelIn.  Unfolding the stage twice
  -- (src/L/Constructible.lagda.md:340,313) says the tower's value at c
  -- sits TWO stages below α, not merely inside it.  This is the number
  -- the next brief needs: the witness does not want room in Lset α, it
  -- wants room two ranks down.
  witness-forces-two-below :
      (δ f : S) → IsOrd (fst δ) → Approximates δ f → ⟨ fst f ∈ Lset α ⟩
    → (c : S) → ⟨ fst c ∈ fst δ ⟩
    → ∥ (Σ[ β ∈ V ℓ ] Σ[ γ ∈ V ℓ ]
           (⟨ β ∈ α ⟩ × ⟨ γ ∈ β ⟩ × ⟨ Lset (fst c) ∈ Lset γ ⟩)) ∥₁
  witness-forces-two-below δ f oδ ha hf c c∈ = PT.rec squash₁ outer
    (Lset-out α (pr (fst c) (Lset (fst c)))
      (trα (entryIn δ f oδ ha c c∈) hf))
    where
    G : Type (ℓ-suc ℓ)
    G = Σ[ β ∈ V ℓ ] Σ[ γ ∈ V ℓ ]
          (⟨ β ∈ α ⟩ × ⟨ γ ∈ β ⟩ × ⟨ Lset (fst c) ∈ Lset γ ⟩)

    outer : Σ[ β ∈ V ℓ ]
              (⟨ β ∈ α ⟩ × ⟨ pr (fst c) (Lset (fst c)) ∈ 𝒟ₒ (Lset β) ⟩)
          → ∥ G ∥₁
    outer (β , (β∈α , hpr)) = PT.map inner
      (Lset-out β ⁅ fst c , Lset (fst c) ⁆
        (𝒟ₒ∋⊆ (Lset β) (pr (fst c) (Lset (fst c))) hpr
          ⁅ fst c , Lset (fst c) ⁆ (pairIn (fst c) (Lset (fst c)))))
      where
      inner : Σ[ γ ∈ V ℓ ]
                (⟨ γ ∈ β ⟩ × ⟨ ⁅ fst c , Lset (fst c) ⁆ ∈ 𝒟ₒ (Lset γ) ⟩)
            → G
      inner (γ , (γ∈β , hp)) = β , γ , β∈α , γ∈β
        , 𝒟ₒ∋⊆ (Lset γ) ⁅ fst c , Lset (fst c) ⁆ hp
            (Lset (fst c)) (sndIn (fst c) (Lset (fst c)))
