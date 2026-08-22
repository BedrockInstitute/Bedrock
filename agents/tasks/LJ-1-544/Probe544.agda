{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.544]  B8 of the GCH join: a limit stage above α that already holds x.
--
-- The obligation is `LimitAbove`, section 5.
--
-- SECTION 1 is W3 and the brief ordered it written first and typechecked
-- ALONE.  That slice is kept at agents/tasks/LJ-1-544/runs/w3-slice.agda.txt.
-- SECTION 2 merges α with the stage of x.  SECTION 3 builds the limit on
-- `Ladder`.  SECTION 4 is the construction with the stage handed over, and
-- it returns an EXPLICIT ordinal in a bare Σ.  SECTION 5 is the obligation:
-- section 4 under one `PT.map`.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-544.Probe544 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono; isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Reflect {ℓ} lem using ( module Ladder )

open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))

-- The V-carrier.  `𝒮ᵥ` sets `S = V ℓ` and `_∈ˢ_ = _∈_`
-- (src/V/Hierarchy.lagda.md:80,83), so a `V ℓ` fact is an `SV.S` fact with
-- no conversion.
module SV = hPropStructure 𝒮ᵥ
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  W3.  THE STAGE OF x.
--
--   The brief names `⟨ isL x ⟩` the widest unmeasured term, because the
--   fourth conjunct of B8 has no other source.  The question is whether
--   it yields an ordinal β with ⟨ x ∈ˢ Lset β ⟩.
--
--   `isL x = ⋁ S (λ α → (IsOrd α , isPropIsOrd α) ⊓ (x ∈ˢ Lset α))`
--   (src/L/Constructible.lagda.md:376).  `⋁` is the library's truncated
--   existential (src/Base/Truth.lagda.md:107) and `⊓` is the library's
--   meet (src/Base/Truth.lagda.md:100), so the two sides below are the
--   SAME type and the term is the identity.
-- =====================================================================

StageOf : Type (ℓ-suc ℓ)
StageOf = (x : SV.S) → ⟨ isL x ⟩
        → ∥ Σ[ β ∈ SV.S ] (IsOrd β × ⟨ x ∈ˢ Lset β ⟩) ∥₁

stageOf : StageOf
stageOf x hx = hx


-- =====================================================================
-- SECTION 2.  ONE ORDINAL ABOVE TWO.
--
--   The chain has to start above BOTH α and the stage β that section 1
--   returns, so the two must be merged first.  Trichotomy `ord-tri`
--   (src/L/Ordinal/Linear.lagda.md:136) does it in three cases, and
--   `sucV` of the larger holds both.
--
--   This is the file's only explicit comparison and one of its two
--   consumers of `lem`; the other is inside `suc∈or≡`
--   (src/L/Ordinal/Stages.lagda.md:137).
--
--   THE `go` FORM IS NOT A STYLE CHOICE.  It is measured: see the
--   report's `## THE BLOW-UP` section and runs/s2-1.out.
-- =====================================================================

TwoAbove : Type (ℓ-suc ℓ)
TwoAbove = (a b : SV.S) → IsOrd a → IsOrd b
         → Σ[ m ∈ SV.S ]
             ( IsOrd m × ⟨ a ∈ˢ sucV m ⟩ × ⟨ b ∈ˢ sucV m ⟩ )

twoAbove : TwoAbove
twoAbove a b oa ob = go (ord-tri a oa b ob)
  where
  Res : Type (ℓ-suc ℓ)
  Res = Σ[ m ∈ SV.S ] ( IsOrd m × ⟨ a ∈ˢ sucV m ⟩ × ⟨ b ∈ˢ sucV m ⟩ )

  go : ⟨ a ∈ˢ b ⟩ ⊎ ((a ≡ b) ⊎ ⟨ b ∈ˢ a ⟩) → Res
  go (inl a∈b)       = b , (ob , (∈sucV-inl a∈b , self∈sucV b))
  go (inr (inl a≡b)) = b , (ob , ( subst (λ w → ⟨ w ∈ˢ sucV b ⟩) (sym a≡b)
                                     (self∈sucV b)
                                 , self∈sucV b ))
  go (inr (inr b∈a)) = a , (oa , (self∈sucV a , ∈sucV-inl b∈a))

-- =====================================================================
-- SECTION 3.  THE LIMIT ABOVE ONE ORDINAL.
--
--   `Ladder` (src/L/Reflect.lagda.md:256) wants an ω-chain of ordinals
--   that climbs.  THE CHAIN IS THE ITERATED SUCCESSOR OF m, and its two
--   hypotheses are `suc-ord` (src/L/Ordinal.lagda.md:96) and
--   `self∈sucV` (src/V/Model.lagda.md:236).  Nothing else is chosen.
--
--   The module hands over four terms and this section uses all four:
--   `top` (src/L/Reflect.lagda.md:268), `top-ord` (:271), `G∈top` (:274)
--   and `δ∈top→fin` (:302).  `δ∈top→fin` is the union inversion and it
--   is the one `[LJ-1.543]` did not name: WITHOUT IT THE
--   SUCCESSOR-CLOSURE CONJUNCT HAS NO PROOF, because an ordinal below
--   the limit must be located on a rung before its successor can be put
--   on the next one.
-- =====================================================================

module Above (m : SV.S) (ordm : IsOrd m) where

  G : ℕ → SV.S
  G zero    = sucV m
  G (suc n) = sucV (G n)

  G-ord : (n : ℕ) → IsOrd (G n)
  G-ord zero    = suc-ord ordm
  G-ord (suc n) = suc-ord (G-ord n)

  G-up : (n : ℕ) → ⟨ G n ∈ˢ G (suc n) ⟩
  G-up n = self∈sucV (G n)

  module Lad = Ladder G G-ord G-up

  lam : SV.S
  lam = Lad.top

  -- CONJUNCT 1.
  lam-ord : IsOrd lam
  lam-ord = Lad.top-ord

  -- Anything on rung zero is under the limit: the limit is an ordinal
  -- and rung zero is one of its members.  CONJUNCT 2 is this at z := α.
  into : (z : SV.S) → ⟨ z ∈ˢ sucV m ⟩ → ⟨ z ∈ˢ lam ⟩
  into z z∈G0 = lam-ord .fst z∈G0 (Lad.G∈top zero)

  -- CONJUNCT 3, AND IT IS THE ONE `Ladder` DOES NOT CARRY.  Locate d on
  -- a rung, put its successor on that rung or on the next one, then
  -- reuse the argument of `into` one rung up.
  suc-closed : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩
  suc-closed d d∈lam =
    PT.rec (snd (sucV d ∈ˢ lam)) step (Lad.δ∈top→fin d d∈lam)
    where
    ordd : IsOrd d
    ordd = mem-ord {A = lam} lam-ord d d∈lam

    onRung : (n : ℕ) → ⟨ sucV d ∈ˢ G n ⟩ ⊎ (sucV d ≡ G n)
           → ⟨ sucV d ∈ˢ sucV (G n) ⟩
    onRung n (inl h) = ∈sucV-inl h
    onRung n (inr e) =
      subst (λ w → ⟨ w ∈ˢ sucV (G n) ⟩) (sym e) (self∈sucV (G n))

    step : Σ[ n ∈ ℕ ] ⟨ d ∈ˢ G n ⟩ → ⟨ sucV d ∈ˢ lam ⟩
    step (n , d∈Gn) =
      lam-ord .fst (onRung n (suc∈or≡ d (G n) ordd (G-ord n) d∈Gn))
                   (Lad.G∈top (suc n))

-- =====================================================================
-- SECTION 4.  THE CORE, WITH THE STAGE HANDED OVER.
--
--   The construction proper.  It takes the stage β as an argument
--   instead of `⟨ isL x ⟩` and it returns a BARE Σ: no `∥ … ∥₁` occurs
--   in this type and none is used in the term.  So the ordinal is
--   EXPLICIT, and nothing here selects a witness.
--
--   This is the answer to the brief's question about which conclusion
--   was delivered.  Section 5 shows the truncation of B8's own
--   conclusion is exactly the truncation already inside `isL`, and is
--   created nowhere in the proof.
-- =====================================================================

LimitAboveΣ : Type (ℓ-suc ℓ)
LimitAboveΣ =
    (α x β : SV.S) → IsOrd α → IsOrd β → ⟨ x ∈ˢ Lset β ⟩
  → Σ[ lam ∈ SV.S ]
      ( IsOrd lam
      × ⟨ α ∈ˢ lam ⟩
      × ((d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
      × ⟨ x ∈ˢ Lset lam ⟩ )

limitAboveΣ : LimitAboveΣ
limitAboveΣ α x β oα oβ x∈Lβ = A.lam
  , ( A.lam-ord                                              -- conjunct 1
    , ( A.into α (t .snd .snd .fst)                          -- conjunct 2
      , ( A.suc-closed                                       -- conjunct 3
        , Lset-mono {α = A.lam} {β = β}                      -- conjunct 4
            (A.into β (t .snd .snd .snd)) x∈Lβ ) ) )
  where
  t : Σ[ m ∈ SV.S ] ( IsOrd m × ⟨ α ∈ˢ sucV m ⟩ × ⟨ β ∈ˢ sucV m ⟩ )
  t = twoAbove α β oα oβ

  module A = Above (t .fst) (t .snd .fst)

-- =====================================================================
-- SECTION 5.  THE OBLIGATION.
--
--   `[LJ-1.523]`'s type, letter for letter
--   (agents/tasks/LJ-1-523/Probe523.agda:244-251).
--
--   It is section 4 under one `PT.map`, and `stageOf` is the identity,
--   so THE TRUNCATION IS THE WHOLE DIFFERENCE between the obligation
--   and the explicit construction.
-- =====================================================================

LimitAbove : Type (ℓ-suc ℓ)
LimitAbove =
    (α x : SV.S) → IsOrd α → ⟨ isL x ⟩
  → ∥ Σ[ lam ∈ SV.S ]
       ( IsOrd lam
       × ⟨ α ∈ˢ lam ⟩
       × ((d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
       × ⟨ x ∈ˢ Lset lam ⟩ ) ∥₁

limitAbove : LimitAbove
limitAbove α x oα hx =
  PT.map (λ { (β , (oβ , x∈Lβ)) → limitAboveΣ α x β oα oβ x∈Lβ })
         (stageOf x hx)
