{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.526]  Does the successor L-cardinal exist.
--
-- Section 1 is W3: does ANY set satisfy `IsCardinalL`.  The brief
-- ordered it written first and typechecked alone.
--
-- Nothing is postulated.  Nothing lands in src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-526.Probe526 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import L.Constructible {ℓ} using ( 𝒮ʟ; IsOrd; isL; isL-trans )
open import L.Ordinal {ℓ} using ( ∅-ord; ω-ord; mem-ord; suc-ord )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Cardinal {ℓ} lem
  using ( IsCardinalL; InjCode; _↪_; module LeastCardInjL )
open import L.BoundedSubset {ℓ} lem using ( IsCardinal )
open import L.CantorBernstein {ℓ} lem using ( readL )
open import L.InjChain {ℓ} lem using ( finite-excl-ω )
open import L.GCH {ℓ} lem using ( SuccCardL )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.SquareLaw {ℓ} lem using ( ordSWO )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )
open import V.Presentation {ℓ} using ( member; fiber )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.Foundations.HLevels using ( isPropΠ; isProp× )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The V-carrier and the L-carrier, named as [LJ-1.523] named them
-- (agents/tasks/LJ-1-523/Probe523.agda:36-42).
module SV = hPropStructure 𝒮ᵥ
module SL = hPropStructure 𝒮ʟ

open SV using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  W3.  DOES ANY SET SATISFY `IsCardinalL`.
--
--   `[LJ-1.90-A]` measured that the AMBIENT `IsCardinal`
--   (src/L/BoundedSubset.lagda.md:1046-1047) is never inhabited in the
--   tree.  The brief asks the same question of the INTERNAL
--   `IsCardinalL` (src/L/Cardinal.lagda.md:230-233) before anything is
--   built on it.
--
--   The answer is YES and it is VACUOUS.  `IsCardinalL κ` quantifies
--   over the members of κ, so the empty set satisfies it with nothing
--   to prove, exactly as `∅-ord` satisfies `IsOrd`
--   (src/L/Ordinal.lagda.md:77-79).  `∅ʟ` is the delivered L-element
--   (src/L/Axioms/Basic.lagda.md:508-509).
-- =====================================================================

someCardinalL : ∥ Σ[ κ ∈ SL.S ] (IsOrd (fst κ) × IsCardinalL κ) ∥₁
someCardinalL = ∣ ∅ʟ , ∅-ord , vacuous ∣₁
  where
  vacuous : IsCardinalL ∅ʟ
  vacuous δ δ∈∅ _ =
    Empty.rec (∅-empty (fst δ) (∈∈ₛ {a = fst δ} {b = ∅} .fst δ∈∅))

-- =====================================================================
-- SECTION 2.  D-10.  THE AMBIENT PREDICATE AGAINST THE INTERNAL ONE.
--
--   `IsCardinal κ = (δ : SV.S) → ⟨ δ ∈ˢ κ ⟩ → (⟪ κ ⟫ ↪ ⟪ δ ⟫ → ⊥)`
--   (src/L/BoundedSubset.lagda.md:1046-1047).  The refutand is an
--   AMBIENT function with an ambient injectivity proof.
--
--   `IsCardinalL κ = (δ : SL.S) → ⟨ fst δ ∈ fst κ ⟩
--                  → (∥ Σ[ F ∈ SL.S ] InjCode F κ δ ∥₁ → ⊥)`
--   (src/L/Cardinal.lagda.md:230-233).  The refutand is an L-ELEMENT
--   that CODES such a function inside the model.
--
--   THE DIRECTION IS THE WHOLE ANSWER.  `readL`
--   (src/L/CantorBernstein.lagda.md:33-38) turns a code into an ambient
--   injection, so a code is a HARDER thing to have than a function.
--   Refuting the harder thing is EASIER.  The implication below is
--   therefore ambient ⟹ internal, and `IsCardinalL` is the WEAKER
--   predicate.
--
--   `[LJ-1.91]` (archive/dev/LJ-dispatch-index.md:167) measured that
--   the AMBIENT predicate is out of reach at the internal ω₁.  A
--   statement being out of reach transfers UPWARD, to stronger
--   statements, never downward to weaker ones.  So that obstruction
--   does NOT reach `IsCardinalL`, and section 3 inhabits the internal
--   predicate at an infinite ordinal to prove it.
-- =====================================================================

ambient→internal : (κ : SL.S) → IsCardinal (fst κ) → IsCardinalL κ
ambient→internal κ c δ δ∈κ h =
  PT.rec Empty.isProp⊥ (λ w → c (fst δ) δ∈κ (readL κ δ w)) h

-- THE CONVERSE IS NOT WRITTEN, AND IT IS NOT AN OVERSIGHT.  It would
-- need every ambient injection between two L-elements to be coded by an
-- L-element, which is the definability direction of the readback.
-- `src/L/CantorBernstein.lagda.md` delivers `readL` and nothing in the
-- other direction.  This type is STATED and NOT inhabited.
internal→ambient : Type (ℓ-suc ℓ)
internal→ambient = (κ : SL.S) → IsCardinalL κ → IsCardinal (fst κ)

-- =====================================================================
-- SECTION 3.  W3, THE PART THAT MATTERS.  AN INFINITE L-CARDINAL.
--
--   Section 1 answered the brief's W3 literally and the answer was
--   vacuous.  The question behind it is whether the hypothesis triple
--   of `GCHStatement` (src/L/GCH.lagda.md:60-64) has any instance at
--   all, because κ there is required to be INFINITE.
--
--   It has one, and every piece is already in the tree.
--   `finite-excl-ω` (src/L/InjChain.lagda.md:152-156) refutes an
--   injection of ω into the SQUARE of a finite ordinal; the diagonal
--   turns a plain injection into that shape.
-- =====================================================================

-- ω IS AN AMBIENT CARDINAL.  `[LJ-1.90-A]`
-- (archive/dev/LJ-dispatch-index.md:166) recorded that `IsCardinal` had
-- no inhabitant in the tree.  This is one, and it is four lines.
ω-card : IsCardinal ω
ω-card δ δ∈ω (f , finj) =
  finite-excl-ω δ (mem-ord {A = ω} ω-ord δ δ∈ω) δ∈ω
    (λ x → f x , f x) (λ x y e → finj x y (cong fst e))

-- AND THEREFORE AN INTERNAL ONE, THROUGH SECTION 2.
ω-cardL : IsCardinalL ωʟ
ω-cardL = ambient→internal ωʟ ω-card

-- THE HYPOTHESIS TRIPLE OF `GCHStatement`, INHABITED.  This is the
-- statement's own κ slot (src/L/GCH.lagda.md:60-63), filled.
gchHypAtω : Σ[ κ ∈ SL.S ]
              (IsOrd (fst κ) × IsCardinalL κ × (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥))
gchHypAtω = ωʟ , ω-ord , ω-cardL , ∈-irrefl ω

-- =====================================================================
-- SECTION 4.  THE OBLIGATION, AND THE ONE INPUT IT REDUCES TO.
--
--   `SuccCardExists` is the brief's type, written at the brief's own
--   binding.  It is NOT inhabited here, and section `## WHAT IT NEEDS`
--   of the report says why with `file:line`.
--
--   What IS built is the reduction.  `SuccCardExists` follows from ONE
--   input, `CardAboveL`: SOME ordinal L-cardinal above κ.  Nothing else
--   is missing.  The leastness clause of `SuccCardL`
--   (src/L/GCH.lagda.md:50-53), which the brief forbade weakening, is
--   not weakened and is not assumed: it is PRODUCED by `leastOf`
--   (src/L/WellOrder/Base.lagda.md:158-160) over the ordinal
--   well-order, exactly as `LeastCardInjL` produces its own
--   (src/L/Cardinal.lagda.md:117-118).
-- =====================================================================

-- THE OBLIGATION.  Identical to `[LJ-1.523]`'s row B4
-- (agents/tasks/LJ-1-523/Probe523.agda:191-195).
SuccCardExists : Type (ℓ-suc ℓ)
SuccCardExists =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ SL.S ] SuccCardL δ κ ∥₁

-- THE ONE INPUT.  Existence with NO leastness and NO bound: some
-- ordinal L-cardinal strictly above κ.  This is the Hartogs fact, in
-- the weakest form the reduction can use.
CardAboveL : Type (ℓ-suc ℓ)
CardAboveL =
    (κ : SL.S) → IsOrd (fst κ) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ θ ∈ SL.S ]
       (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩) ∥₁

-- The selection, at one κ and one witness θ.  The domain is the tower
-- at `sucV (fst θ)`, so θ itself is in range and every candidate below
-- θ is too; a candidate ABOVE θ is handled by the ordinal order and
-- never enters the selection.
module Reduce (κ : SL.S) (oκ : IsOrd (fst κ))
              (θ : SL.S) (oθ : IsOrd (fst θ))
              (cθ : IsCardinalL θ) (κ∈θ : ⟨ fst κ ∈ˢ fst θ ⟩) where

  -- The crossing is not rebuilt: it is `LeastCardInjL`'s
  -- (src/L/Cardinal.lagda.md:77-79), at θ.
  open LeastCardInjL θ oθ using ( up; self; self-eq )

  A : Type ℓ
  A = ⟪ sucV (fst θ) ⟫

  -- SEALED, and the seal is `src/L/Cardinal.lagda.md:82-92` re-measured
  -- at this site: unsealed this file took 112.98 s
  -- (runs/s4-2.out, source kept at runs/unsealed.agda.txt).
  opaque
    w : SWO A
    w = ordSWO (sucV (fst θ)) (suc-ord oθ)

  -- The one read the seal needs (R-36), proved inside it.
  opaque
    unfolding w
    w-lt : (m n : A) → SWO._<∙_ w m n
         ≡ ⟨ ⟪ sucV (fst θ) ⟫↪ m ∈ˢ ⟪ sucV (fst θ) ⟫↪ n ⟩
    w-lt m n = refl

  isPropIsCardinalL : (x : SL.S) → isProp (IsCardinalL x)
  isPropIsCardinalL x =
    isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → Empty.isProp⊥)))

  -- THE PREDICATE IS THE CONCLUSION'S OWN TWO CLAUSES.  Because both
  -- are hProps, `leastOf` returns them AND their minimality in one
  -- object, and the leastness clause of `SuccCardL` costs nothing more.
  Good : A → hProp (ℓ-suc ℓ)
  Good b = (IsCardinalL (up b) × ⟨ fst κ ∈ˢ fst (up b) ⟩)
         , isProp× (isPropIsCardinalL (up b)) (snd (fst κ ∈ˢ fst (up b)))

  upSelf : up self ≡ θ
  upSelf = Σ≡Prop (λ x → snd (isL x)) self-eq

  nonempty : ∥ Σ[ b ∈ A ] ⟨ Good b ⟩ ∥₁
  nonempty = ∣ self
            , subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upSelf) (cθ , κ∈θ) ∣₁

  least : Σ[ b ∈ A ] IsLeast w Good b
  least = leastOf w lem Good nonempty

  δ : SL.S
  δ = up (fst least)

  δ∈sθ : ⟨ fst δ ∈ˢ sucV (fst θ) ⟩
  δ∈sθ = member (sucV (fst θ)) (fst least)

  oδ : IsOrd (fst δ)
  oδ = mem-ord {A = sucV (fst θ)} (suc-ord oθ) (fst δ) δ∈sθ

  cδ : IsCardinalL δ
  cδ = fst (fst (snd least))

  κ∈δ : ⟨ fst κ ∈ˢ fst δ ⟩
  κ∈δ = snd (fst (snd least))

  δ-min : (b : A) → ⟨ Good b ⟩ → (SWO._<∙_ w b (fst least) → Empty.⊥)
  δ-min = snd (snd least)

  -- THE LEASTNESS CLAUSE, UNWEAKENED (src/L/GCH.lagda.md:50-53).
  leastness : (c : SL.S) → IsOrd (fst c) → IsCardinalL c
            → ⟨ fst κ ∈ˢ fst c ⟩
            → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
  leastness c oc cc κ∈c = go (ord-tri (fst δ) oδ (fst c) oc)
    where
    go : Tri (fst δ) (fst c)
       → (x : SL.S) → ⟨ fst x ∈ˢ fst δ ⟩ → ⟨ fst x ∈ˢ fst c ⟩
    -- δ ∈ c: c is transitive, so δ ⊆ c.
    go (inl δ∈c)       x x∈δ = oc .fst x∈δ δ∈c
    -- δ = c: nothing to do.
    go (inr (inl e))   x x∈δ = subst (λ v → ⟨ fst x ∈ˢ v ⟩) e x∈δ
    -- c ∈ δ: c is a candidate BELOW the least one, which is absurd.
    go (inr (inr c∈δ)) x x∈δ = Empty.rec (δ-min b bGood b<δ)
      where
      c∈sθ : ⟨ fst c ∈ˢ sucV (fst θ) ⟩
      c∈sθ = suc-ord oθ .fst c∈δ δ∈sθ
      b : A
      b = fiber (sucV (fst θ)) c∈sθ .fst
      be : ⟪ sucV (fst θ) ⟫↪ b ≡ fst c
      be = fiber (sucV (fst θ)) c∈sθ .snd
      upb : up b ≡ c
      upb = Σ≡Prop (λ v → snd (isL v)) be
      bGood : ⟨ Good b ⟩
      bGood = subst (λ z → IsCardinalL z × ⟨ fst κ ∈ˢ fst z ⟩)
                (sym upb) (cc , κ∈c)
      b<δ : SWO._<∙_ w b (fst least)
      b<δ = transport (λ i → sym (w-lt b (fst least)) i)
              (subst (λ v → ⟨ v ∈ˢ fst δ ⟩) (sym be) c∈δ)

-- THE REDUCTION.  GREEN, NO HOLES.
reduction : CardAboveL → SuccCardExists
reduction ca κ oκ cκ κ∉ω = PT.map build (ca κ oκ cκ κ∉ω)
  where
  build : Σ[ θ ∈ SL.S ]
            (IsOrd (fst θ) × IsCardinalL θ × ⟨ fst κ ∈ˢ fst θ ⟩)
        → Σ[ δ ∈ SL.S ] SuccCardL δ κ
  build (θ , oθ , cθ , κ∈θ) = R.δ , R.oδ , R.cδ , R.κ∈δ , R.leastness
    where module R = Reduce κ oκ θ oθ cθ κ∈θ
