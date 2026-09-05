{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.540]  B7: a stage absorbs one element, ambiently.
--
-- THE OBLIGATION IS `AbsorbsAt`, section 4.  It is INHABITED, with no
-- hole and no postulate.  Nothing lands in src/.  No `InjCode`, no
-- `Formula`: the conclusion is the bare ambient `_↪_`
-- (src/L/BoundedSubset.lagda.md:1043-1044) and neither coded route of
-- [LJ-1.533] and [LJ-1.535] is entered.
--
-- SECTION 1 IS W3 AND IT WAS TYPECHECKED ALONE FIRST.  The slice is kept
-- at agents/tasks/LJ-1-540/runs/w3-slice.agda.txt, its run at
-- runs/w3-1.out.  The answer: x goes to the numeral 0 of the stage, and
-- the whole cost of finding that place is "an infinite ordinal's stage
-- holds every numeral".  Nothing about x enters it.
--
-- SECTION 1B ANSWERS D-10 AND IT IS CHECKED, NOT ASSERTED.  x need NOT
-- be a member of the stage: α := ω and x := ω satisfy every hypothesis
-- of B7 and refute `x ∈ˢ Lset α`.  Adjoining it still does not grow the
-- stage, because the stage is Dedekind-infinite through its numerals.
--
-- WHAT TRANSFERS FROM `absorbs` (src/L/Absorption.lagda.md:635-638) is
-- PART 1 of that chapter only, `ShiftAbs` (:74-192): the three-case
-- split, the three readback lemmas and the sixteen-case injectivity
-- matrix.  Section 3 rewrites them at THIS domain.  What does NOT
-- transfer is named at section 3's head.  C-42: the two statements are
-- different and this file never reads one as the other.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-540.Probe540 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( numeral-ord; #∈ω; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; ord∈Lset→∈ )
open import L.Absorption {ℓ} lem using ( module ShiftAbs )
open import L.BoundedSubset {ℓ} lem using ( _↪_ )
open import V.Coding {ℓ} using ( #-inj′ )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; _∪_; ⁅_,_⁆; ⁅_⁆s; union-ax; pairing-ax
        ; SetPackage; SingletonPackage )  -- lint-agda: keep (SetPackage via record projection)
open InfinitySet {ℓ} using ( ω; sucV; #_ )
open import Cubical.Data.Nat.Properties using ( injSuc; znots; snotz )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S; _∈ˢ_ )

-- =====================================================================
-- SECTION 1.  W3.  WHERE x GOES.
--
--   The brief names the widest unmeasured term: "the image of ⁅ x ⁆s
--   under the injection, as a term".  The answer is `xImage`, and it
--   costs exactly one fact about the stage: `Lset α` holds every
--   numeral when α is an infinite ordinal.  NOTHING ABOUT x ENTERS.
--   That is the whole finding of W3 and it is why the rest is cheap.
-- =====================================================================

module W3 (α : S) (ordα : IsOrd α) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  -- Every numeral is a member of α.  `one∈α`
  -- (src/L/BoundedSubset.lagda.md:1206-1212) is this at k = 1; the
  -- generalization to every k costs nothing extra.  α ∉ ω plus
  -- trichotomy is the whole argument.
  num∈α : (k : ℕ) → ⟨ (# k) ∈ˢ α ⟩
  num∈α k = Sum.rec
      (λ α∈ω → Empty.rec (α∉ω α∈ω))
      (Sum.rec (λ α≡ω → subst (λ w → ⟨ (# k) ∈ˢ w ⟩) (sym α≡ω) (#∈ω k))
               (λ ω∈α → ordα .fst (#∈ω k) ω∈α))
      (ord-tri α ordα ω ω-ord)

  -- And therefore a member of the STAGE at α.  This is the exact shape
  -- of `numeral∈limit` (src/L/Choice/Name.lagda.md:121), with `ω`
  -- replaced by α: the numeral sits at the stage after itself and
  -- monotonicity carries it up.
  num∈L : (k : ℕ) → ⟨ (# k) ∈ˢ Lset α ⟩
  num∈L k = Lset-mono {α = α} {β = # (suc k)} (num∈α (suc k))
              {x = # k} (ord∈Lset-suc (# k) (numeral-ord k))

  -- THE ANSWER TO W3.  The place x goes is the member of `Lset α`
  -- whose value is the numeral 0.  It exists because the stage holds
  -- every numeral, and it is free of x entirely.
  xImage : ⟪ Lset α ⟫
  xImage = fiber (Lset α) (num∈L 0) .fst

  xImage-val : ⟪ Lset α ⟫↪ xImage ≡ # 0
  xImage-val = fiber (Lset α) (num∈L 0) .snd

-- =====================================================================
-- SECTION 1B.  D-10.  IS x A MEMBER OF THE STAGE?  NO, AND THE WITNESS
-- IS CHECKED RATHER THAN ASSERTED.
--
--   The brief orders the truth priced before the proof.  The type gives
--   only `x ⊆ Lset α` (the fourth hypothesis), never `x ∈ˢ Lset α`, and
--   the gap is real: α := ω and x := ω satisfy every hypothesis of B7
--   and refute the membership.  Both halves are terms below.
--
--   SO THE INJECTION MUST GENUINELY PLACE A NEW ELEMENT.  It does not
--   grow the stage because `Lset α` is Dedekind-infinite for every
--   infinite ordinal α: section 1 puts every numeral in it, and the
--   numerals are the room the shift uses.  NO LIMIT HYPOTHESIS IS
--   NEEDED, so this is no finding against [LJ-1.523]'s row.
-- =====================================================================

module D10 where

  ω∉ω : ⟨ ω ∈ˢ ω ⟩ → Empty.⊥
  ω∉ω = ∈-irrefl ω

  module Wω = W3 ω ω-ord ω∉ω
  module Sω = ShiftAbs ω ω-ord ω∉ω #∈ω

  -- The hypothesis holds at x := ω: every member of ω is a numeral and
  -- section 1 has already put every numeral in the stage.
  hypothesis-holds : (z : S) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ Lset ω ⟩
  hypothesis-holds z z∈ω =
    subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (Sω.numeralOf-spec z z∈ω))
      (Wω.num∈L (Sω.numeralOf z z∈ω))

  -- And the membership fails: an ordinal in a stage is a member of the
  -- index (src/L/Ordinal/Stages.lagda.md:265-266), so ω ∈ Lset ω would
  -- give ω ∈ ω.
  membership-fails : ⟨ ω ∈ˢ Lset ω ⟩ → Empty.⊥
  membership-fails ω∈Lω = ω∉ω (ord∈Lset→∈ ω ω-ord ω ω-ord ω∈Lω)

-- =====================================================================
-- SECTION 2.  THE ADJUNCTION, READ BACKWARDS.
--
--   `UnionKit` (src/L/BoundedSubset.lagda.md:1145-1147) has this
--   elimination already, as `X-mem` (:1171) and `sgl≡` (:1167).  IT IS
--   NOT REUSABLE HERE: that module takes `lam`, `ordλ`, `α∈λ` and
--   `x∈Lλ` as parameters and B7's type gives none of them.  So the one
--   direction this file needs is rewritten, at B7's own hypotheses.
--
--   The direction is: a member of `Lset α ∪ ⁅ x ⁆s` that is not x is a
--   member of `Lset α`.  Nothing else about the union is used.
-- =====================================================================

module Adjoin (α x : S) where

  X : S
  X = Lset α ∪ ⁅ x ⁆s

  x∈sgl : ⟨ x ∈ₛ ⁅ x ⁆s ⟩
  x∈sgl = SetPackage.classification (SingletonPackage x) x .snd refl

  x∈X : ⟨ x ∈ˢ X ⟩
  x∈X = ∈∈ₛ {a = x} {b = X} .snd
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ x .snd
      ∣ ⁅ x ⁆s , (pairing-ax (Lset α) (⁅ x ⁆s) (⁅ x ⁆s) .snd ∣ inr refl ∣₁
                , x∈sgl) ∣₁)

  sgl≡ : (z : S) → ⟨ z ∈ˢ ⁅ x ⁆s ⟩ → z ≡ x
  sgl≡ z z∈sgl = SetPackage.classification (SingletonPackage x) z .fst
    (∈∈ₛ {a = z} {b = ⁅ x ⁆s} .fst z∈sgl)

  -- THE ONLY ELIMINATION THIS FILE NEEDS.
  X-elim : (z : S) → ⟨ z ∈ˢ X ⟩ → ((z ≡ x) → Empty.⊥) → ⟨ z ∈ˢ Lset α ⟩
  X-elim z z∈X ¬z≡x = PT.rec (snd (z ∈ˢ Lset α)) go
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ z .fst (∈∈ₛ {a = z} {b = X} .fst z∈X))
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ₛ ⁅ Lset α , ⁅ x ⁆s ⁆ ⟩ × ⟨ z ∈ₛ w ⟩)
       → ⟨ z ∈ˢ Lset α ⟩
    go (w , w∈ₛpair , z∈ₛw) = PT.rec (snd (z ∈ˢ Lset α)) go₂
      (pairing-ax (Lset α) (⁅ x ⁆s) w .fst w∈ₛpair)
      where
      z∈w : ⟨ z ∈ˢ w ⟩
      z∈w = ∈∈ₛ {a = z} {b = w} .snd z∈ₛw
      go₂ : (w ≡ Lset α) ⊎ (w ≡ ⁅ x ⁆s) → ⟨ z ∈ˢ Lset α ⟩
      go₂ (inl e) = subst (λ u → ⟨ z ∈ˢ u ⟩) e z∈w
      go₂ (inr e) = Empty.rec
        (¬z≡x (sgl≡ z (subst (λ u → ⟨ z ∈ˢ u ⟩) e z∈w)))

-- =====================================================================
-- SECTION 3.  THE SHIFT, AT THE STAGE.
--
--   WHAT TRANSFERS from `ShiftAbs` (src/L/Absorption.lagda.md:74-192):
--     * the three-case split numeral / top / other, decided by `lem`;
--     * one readback lemma per case, each proved by re-running the two
--       decisions and discharging the impossible corners;
--     * the injectivity matrix, sixteen corners on four decisions.
--   WHAT DOES NOT TRANSFER, and each is a line of this file:
--     * `∈sucV-elim` (src/V/Model.lagda.md:218).  The domain is a union
--       with a singleton, not a successor.  `Adjoin.X-elim` replaces it.
--     * `numerals` as a HYPOTHESIS.  `ShiftAbs` is handed it; B7 must
--       DERIVE it for `Lset α`, which is section 1.
--     * `γ∉ω` at the top element.  `ShiftAbs` proves `shift-top` from
--       "the top is not a numeral", and B7 has NO such hypothesis: its
--       x may well be a numeral.  `shift-top` here therefore takes the
--       case decision `¬v∈ω` as an ARGUMENT.  That is the one real
--       change, and it is why B7 needs no hypothesis on x.
--     * PARTS 2 to 4 of that chapter (`ShiftFo`, `Carve`,
--       `ShiftGraph`, :193-626).  They build the `InjCode`.  This
--       obligation is ambient and enters none of them.
--
--   WHAT IS BORROWED WHOLE: three numeral lemmas, `numeralOf`,
--   `numeralOf-spec` and `numeralOf-uniq` (:78-89).  They mention no
--   module parameter, so instantiating `ShiftAbs` at γ := α (which
--   section 1 has already paid for) takes them at the identical type.
--   The elaborator settles that, not a sentence.
-- =====================================================================

module Shift (α x : S) (ordα : IsOrd α) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  module W = W3 α ordα α∉ω
  module A = Adjoin α x
  module SA = ShiftAbs α ordα α∉ω W.num∈α

  v-of : ⟪ A.X ⟫ → S
  v-of m = ⟪ A.X ⟫↪ m

  -- The "other" case's landing.  Note it does NOT consult ω: being
  -- unequal to x is already enough, because the adjunction has exactly
  -- two parts.
  v-in-Lα : (m : ⟪ A.X ⟫) → ((v-of m ≡ x) → Empty.⊥) → ⟨ v-of m ∈ˢ Lset α ⟩
  v-in-Lα m ¬v≡x = A.X-elim (v-of m) (member A.X m) ¬v≡x

  shift-dec : (m : ⟪ A.X ⟫)
            → ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
            → (v-of m ≡ x) ⊎ ((v-of m ≡ x) → Empty.⊥) → ⟪ Lset α ⟫
  shift-dec m (inl v∈ω) _ =
    fiber (Lset α) (W.num∈L (suc (SA.numeralOf (v-of m) v∈ω))) .fst
  shift-dec m (inr _) (inl v≡x) = fiber (Lset α) (W.num∈L 0) .fst
  shift-dec m (inr _) (inr ¬v≡x) = fiber (Lset α) (v-in-Lα m ¬v≡x) .fst

  shift : ⟪ A.X ⟫ → ⟪ Lset α ⟫
  shift m = shift-dec m (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ x) , setIsSet (v-of m) x))

  -- THE ONE CHANGE AGAINST `ShiftAbs.shift-top`
  -- (src/L/Absorption.lagda.md:113-122): the case decision `¬v∈ω` is an
  -- ARGUMENT, not a consequence of a hypothesis on the top element.
  -- `ShiftAbs` discharges the `inl` corner with `γ∉ω`; B7 has no such
  -- hypothesis and discharges it with the argument instead.  Every use
  -- of this lemma below already stands in an `inr` corner, so the
  -- argument is free at every call site.
  shift-top : (m : ⟪ A.X ⟫) (¬v∈ω : ⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
            → (v-of m ≡ x) → ⟪ Lset α ⟫↪ (shift m) ≡ # 0
  shift-top m ¬v∈ω v≡x = go (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ x) , setIsSet (v-of m) x))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ x) ⊎ ((v-of m ≡ x) → Empty.⊥))
       → ⟪ Lset α ⟫↪ (shift-dec m d e) ≡ # 0
    go (inl v∈ω) _ = Empty.rec (¬v∈ω v∈ω)
    go (inr _) (inl _) = fiber (Lset α) (W.num∈L 0) .snd
    go (inr _) (inr ¬v≡x) = Empty.rec (¬v≡x v≡x)

  shift-num : (m : ⟪ A.X ⟫) (v∈ω : ⟨ v-of m ∈ˢ ω ⟩)
            → ⟪ Lset α ⟫↪ (shift m) ≡ # (suc (SA.numeralOf (v-of m) v∈ω))
  shift-num m v∈ω = go (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ x) , setIsSet (v-of m) x))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ x) ⊎ ((v-of m ≡ x) → Empty.⊥))
       → ⟪ Lset α ⟫↪ (shift-dec m d e) ≡ # (suc (SA.numeralOf (v-of m) v∈ω))
    go (inl v∈ω') _ =
      fiber (Lset α) (W.num∈L (suc (SA.numeralOf (v-of m) v∈ω'))) .snd
        ∙ cong (λ k → # (suc k)) (SA.numeralOf-uniq (v-of m) v∈ω' v∈ω)
    go (inr ¬v∈ω) _ = Empty.rec (¬v∈ω v∈ω)

  shift-other : (m : ⟪ A.X ⟫) (¬v∈ω : ⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥)
              (¬v≡x : (v-of m ≡ x) → Empty.⊥)
            → ⟪ Lset α ⟫↪ (shift m) ≡ v-of m
  shift-other m ¬v∈ω ¬v≡x = go (lem (v-of m ∈ˢ ω))
    (lem ((v-of m ≡ x) , setIsSet (v-of m) x))
    where
    go : (d : ⟨ v-of m ∈ˢ ω ⟩ ⊎ (⟨ v-of m ∈ˢ ω ⟩ → Empty.⊥))
       → (e : (v-of m ≡ x) ⊎ ((v-of m ≡ x) → Empty.⊥))
       → ⟪ Lset α ⟫↪ (shift-dec m d e) ≡ v-of m
    go (inl v∈ω) _ = Empty.rec (¬v∈ω v∈ω)
    go (inr _) (inl v≡x) = Empty.rec (¬v≡x v≡x)
    go (inr _) (inr h₂) = fiber (Lset α) (v-in-Lα m h₂) .snd

  -- The matrix.  It is `ShiftAbs.shift-inj`
  -- (src/L/Absorption.lagda.md:148-190) corner for corner, with the
  -- three `shift-top` calls carrying the extra decision argument.
  shift-inj : (m₁ m₂ : ⟪ A.X ⟫) → shift m₁ ≡ shift m₂ → m₁ ≡ m₂
  shift-inj m₁ m₂ e = go (lem (v₁ ∈ˢ ω)) (lem ((v₁ ≡ x) , setIsSet v₁ x))
                         (lem (v₂ ∈ˢ ω)) (lem ((v₂ ≡ x) , setIsSet v₂ x))
    where
    v₁ : S
    v₁ = v-of m₁
    v₂ : S
    v₂ = v-of m₂
    eqv : ⟪ Lset α ⟫↪ (shift m₁) ≡ ⟪ Lset α ⟫↪ (shift m₂)
    eqv = cong (⟪ Lset α ⟫↪) e
    v₁≡v₂ : v₁ ≡ v₂ → m₁ ≡ m₂
    v₁≡v₂ q = ↪-inj {a = A.X} q
    go : ⟨ v₁ ∈ˢ ω ⟩ ⊎ (⟨ v₁ ∈ˢ ω ⟩ → Empty.⊥)
       → (v₁ ≡ x) ⊎ ((v₁ ≡ x) → Empty.⊥)
       → ⟨ v₂ ∈ˢ ω ⟩ ⊎ (⟨ v₂ ∈ˢ ω ⟩ → Empty.⊥)
       → (v₂ ≡ x) ⊎ ((v₂ ≡ x) → Empty.⊥) → m₁ ≡ m₂
    go (inl a₁) _ (inl a₂) _ = v₁≡v₂
      (SA.numeralOf-spec v₁ a₁
        ∙ cong (λ k → # k) (injSuc (#-inj′
            (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-num m₂ a₂)))
        ∙ sym (SA.numeralOf-spec v₂ a₂))
    go (inl a₁) _ (inr ¬a₂) (inl p₂) = Empty.rec
      (snotz (#-inj′ (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-top m₂ ¬a₂ p₂)))
    go (inl a₁) _ (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-num m₁ a₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
        (#∈ω (suc (SA.numeralOf v₁ a₁)))))
    go (inr ¬a₁) (inl p₁) (inl a₂) _ = Empty.rec
      (znots (#-inj′ (sym (shift-top m₁ ¬a₁ p₁) ∙ eqv ∙ shift-num m₂ a₂)))
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inl p₂) = v₁≡v₂ (p₁ ∙ sym p₂)
    go (inr ¬a₁) (inl p₁) (inr ¬a₂) (inr ¬p₂) = Empty.rec (¬a₂
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-top m₁ ¬a₁ p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)
        (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inl a₂) _ = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-num m₂ a₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁)
        (#∈ω (suc (SA.numeralOf v₂ a₂)))))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inl p₂) = Empty.rec (¬a₁
      (subst (λ w → ⟨ w ∈ˢ ω ⟩)
        (sym (shift-top m₂ ¬a₂ p₂) ∙ sym eqv ∙ shift-other m₁ ¬a₁ ¬p₁)
        (#∈ω 0)))
    go (inr ¬a₁) (inr ¬p₁) (inr ¬a₂) (inr ¬p₂) = v₁≡v₂
      (sym (shift-other m₁ ¬a₁ ¬p₁) ∙ eqv ∙ shift-other m₂ ¬a₂ ¬p₂)

  -- W3's term, at full strength: x itself, as a member of the domain,
  -- lands on the numeral 0.  This is `xImage` reached through the map
  -- rather than posited beside it.
  x-lands-at-0 : (¬x∈ω : ⟨ x ∈ˢ ω ⟩ → Empty.⊥)
               → ⟪ Lset α ⟫↪ (shift (fiber A.X A.x∈X .fst)) ≡ # 0
  x-lands-at-0 ¬x∈ω = shift-top mx
    (λ v∈ω → ¬x∈ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) (fiber A.X A.x∈X .snd) v∈ω))
    (fiber A.X A.x∈X .snd)
    where
    mx : ⟪ A.X ⟫
    mx = fiber A.X A.x∈X .fst

-- =====================================================================
-- SECTION 4.  THE OBLIGATION.
--
--   The brief's type, letter for letter.  `x⊆Lα` is bound and NOT
--   USED: see the report.  The type keeps it because the brief and
--   `BoundedSubsetAt`'s parameter list (src/L/BoundedSubset.lagda.md:
--   1391-1392) both have it, and a probe reports the surplus rather
--   than silently restating the target.
-- =====================================================================

AbsorbsAt :
    (α x : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫
AbsorbsAt α x ordα α∉ω _ = SH.shift , SH.shift-inj
  where
  module SH = Shift α x ordα α∉ω

-- THE SURPLUS, MEASURED BY THE ELABORATOR AND NOT BY A SENTENCE.
-- The same term at the same conclusion with the fourth hypothesis
-- deleted.  If `x⊆Lα` were needed anywhere below `AbsorbsAt`, this
-- would not typecheck.
absorbs-needs-no-subset-hypothesis :
    (α x : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫
absorbs-needs-no-subset-hypothesis α x ordα α∉ω = SH.shift , SH.shift-inj
  where
  module SH = Shift α x ordα α∉ω
