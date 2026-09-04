# Stage facts for the GCH chapter

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Stages {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relabelling using
  ( mapFo; mapFo-comp; mapΔ₀; embed; ⊨-map )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Coding {ℓ} using ( #-inj′ )
open import V.Collapse {ℓ} using ( module Collapse; isExt )
open import L.Constructible {ℓ} using
  ( 𝒮ʟ; IsOrd; Lset; Lset-mono; Lset-out; 𝒟ₒ; 𝒟ₒ∋⊆
  ; isL; isL-trans; Lset→isL )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; numeral-ord; #∈ω; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using
  ( Lset-cumul; ord∈Lset-suc; suc∈or≡ )
open import L.Reflect {ℓ} lem using ( module Ladder )
open import L.Absorption {ℓ} lem using ( module ShiftAbs )
open import L.BoundedSubset {ℓ} lem using
  ( _↪_; module HullStage; module HullExt; module CollapseIso )

open import Cubical.Data.Sigma using ( _×_ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Properties using ( injSuc; znots; snotz )
open import Cubical.Data.Vec using ( _∷_; []; map; lookup )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; _∪_; ⁅_,_⁆; ⁅_⁆s; union-ax; pairing-ax
        ; SetPackage; SingletonPackage; module InfinitySet )
open InfinitySet {ℓ} using ( ω; sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
open hPropStructure 𝒮ᵥ using () renaming ( _∈ˢ_ to _∈ˢᵥ_ )

-- The V-carrier.  `𝒮ᵥ` sets `S = V ℓ` and `_∈ˢ_ = _∈_`
-- (src/V/Hierarchy.lagda.md:80,83), so a `V ℓ` fact is an `SV.S` fact
-- with no conversion.
module SV = hPropStructure 𝒮ᵥ
-- The L-carrier.  `𝒮ʟ = 𝒮ᵥ ↾ isL`, so SL.S is Σ[ x ∈ SV.S ] ⟨ isL x ⟩
-- and SL._∈ˢ_ a b is definitionally fst a ∈ˢ fst b
-- (src/FOL/ZFStructure.lagda.md:149).
module SL = hPropStructure 𝒮ʟ
-- The same instance `src/L/GCH.lagda.md` names, at the same 𝒮ʟ.
module ModelL = FOL.ZFModel 𝒮ʟ

-- =====================================================================
-- Lset-trans-set.  Members of members of Lset γ lie in Lset γ.  The
-- content is the refinement of the operator (a member of D-o A never
-- has a member outside A) plus monotonicity:  one PT.rec over
-- Lset-out, closed by D-o∋⊆ and Lset-mono.
-- =====================================================================

Lset-trans-set : (γ a x : V ℓ)
               → ⟨ a ∈ˢᵥ x ⟩ → ⟨ x ∈ˢᵥ Lset γ ⟩ → ⟨ a ∈ˢᵥ Lset γ ⟩
Lset-trans-set γ a x a∈ x∈ = PT.rec (snd (a ∈ˢᵥ Lset γ)) step (Lset-out γ x x∈)
  where
  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢᵥ γ ⟩ × ⟨ x ∈ˢᵥ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ a ∈ˢᵥ Lset γ ⟩
  step (δ , (δ∈γ , x∈𝒟)) =
    Lset-mono {α = γ} {β = δ} δ∈γ {x = a}
      (𝒟ₒ∋⊆ (Lset δ) x x∈𝒟 a a∈)

-- =====================================================================
-- A member z of a member y of the internal power set of an ordinal κ:
-- z is constructible, a member of κ, and an ordinal.
--
--   `𝒫 κ = ℩ (hasPower κ)` and `hasPower` realizes the class
--   `λ x → x ⊆ˢ κ` (src/FOL/ZFModel.lagda.md:199), where `⊆ˢ` is the
--   INTERNAL subset relation: it quantifies over SL.S only.  So the
--   power-set hypothesis only speaks about CONSTRUCTIBLE members of
--   `y`, and `z` arrives ambient.  The bridge is transitivity of the
--   class `isL` (src/L/Constructible.lagda.md:379).
-- =====================================================================

zStrongest : ModelL.isZFModel → Type (ℓ-suc ℓ)
zStrongest zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩
  → (⟨ isL z ⟩ × ⟨ z ∈ˢ fst κ ⟩ × IsOrd z)
  where open ModelL.isZFModel zf using ( 𝒫 )

z-strongest : (zf : ModelL.isZFModel) → zStrongest zf
z-strongest zf κ y ordκ y∈𝒫κ z z∈y = isLz , z∈κ , mem-ord {A = fst κ} ordκ z z∈κ
  where
  open ModelL.isZFModel zf using ( 𝒫; hasPower )

  -- Door 1.  z is constructible, because y is and L is transitive.
  isLz : ⟨ isL z ⟩
  isLz = isL-trans z∈y (snd y)

  -- Door 2.  The power-set specification, read off `℩-spec`
  -- (src/FOL/ZFModel.lagda.md:123-124).  `𝒫 κ` IS `℩ (hasPower κ)` by
  -- definition, so no transport of the operation is needed.
  y⊆κ : ⟨ y ModelL.⊆ˢ κ ⟩
  y⊆κ = subst ⟨_⟩ (ModelL.℩-spec (hasPower κ) y) y∈𝒫κ

  -- And the two doors meet: z re-enters the internal subset relation
  -- as the L-element (z , isLz).
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = y⊆κ (z , isLz) z∈y

-- An ordinal below κ lands in the stage at κ: the tower's own
-- cumulation lemma, from `ord∈Lset-suc` and `Lset-cumul`.

ord-below-lands : (κ : SV.S) → IsOrd κ → (z : SV.S) → ⟨ z ∈ˢ κ ⟩
                → ⟨ z ∈ˢ Lset κ ⟩
ord-below-lands κ ordκ z z∈κ =
  Lset-cumul z κ ordz ordκ z∈κ (ord∈Lset-suc z ordz)
  where
  ordz : IsOrd z
  ordz = mem-ord {A = κ} ordκ z z∈κ

-- Every member of the internal power set of an ordinal κ is a subset
-- of Lset κ.  `𝒫` is a field of the model, so the model is bound.

SubsetIntoStageAt : ModelL.isZFModel → Type (ℓ-suc ℓ)
SubsetIntoStageAt zf =
    (κ y : SL.S) → IsOrd (fst κ) → ⟨ fst y ∈ˢ fst (𝒫 κ) ⟩
  → (z : SV.S) → ⟨ z ∈ˢ fst y ⟩ → ⟨ z ∈ˢ Lset (fst κ) ⟩
  where open ModelL.isZFModel zf using ( 𝒫 )

SubsetIntoStage : (zf : ModelL.isZFModel) → SubsetIntoStageAt zf
SubsetIntoStage zf κ y ordκ y∈𝒫κ z z∈y =
  ord-below-lands (fst κ) ordκ z z∈κ
  where
  z∈κ : ⟨ z ∈ˢ fst κ ⟩
  z∈κ = z-strongest zf κ y ordκ y∈𝒫κ z z∈y .snd .fst

-- =====================================================================
-- The stage of x.
--
--   `isL x = ⋁ S (λ α → (IsOrd α , isPropIsOrd α) ⊓ (x ∈ˢ Lset α))`
--   (src/L/Constructible.lagda.md:376).  `⋁` is the library's truncated
--   existential and `⊓` is the library's meet, so the two sides below
--   are the SAME type and the term is the identity.
-- =====================================================================

StageOf : Type (ℓ-suc ℓ)
StageOf = (x : SV.S) → ⟨ isL x ⟩
        → ∥ Σ[ β ∈ SV.S ] (IsOrd β × ⟨ x ∈ˢ Lset β ⟩) ∥₁

stageOf : StageOf
stageOf x hx = hx

-- =====================================================================
-- One ordinal above two.  Trichotomy `ord-tri`
-- (src/L/Ordinal/Linear.lagda.md) does it in three cases, and `sucV`
-- of the larger holds both.  THE `go` FORM IS NOT A STYLE CHOICE: it
-- is measured (agents/tasks/LJ-1-544/runs/s2-1.out).
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
-- The limit above one ordinal.
--
--   `Ladder` (src/L/Reflect.lagda.md) wants an ω-chain of ordinals
--   that climbs.  THE CHAIN IS THE ITERATED SUCCESSOR OF m, and its two
--   hypotheses are `suc-ord` and `self∈sucV`.  `δ∈top→fin` is the
--   union inversion: WITHOUT IT THE SUCCESSOR-CLOSURE CONJUNCT HAS NO
--   PROOF, because an ordinal below the limit must be located on a
--   rung before its successor can be put on the next one.
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
-- A limit stage above α that already holds x, with the stage handed
-- over.  It returns a BARE Σ: the ordinal is EXPLICIT, and nothing
-- here selects a witness.
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

-- The same under one `PT.map`; `stageOf` is the identity, so the
-- truncation is the whole difference from the explicit construction.

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

-- =====================================================================
-- A stage at an infinite ordinal holds every numeral, so it absorbs
-- one adjoined element: `Lset α ∪ ⁅ x ⁆s ↪ Lset α`.  Nothing about x
-- enters the place it goes; x lands on the numeral 0 and the numerals
-- shift up by one.
-- =====================================================================

module W3 (α : S) (ordα : IsOrd α) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  -- Every numeral is a member of α.  α ∉ ω plus trichotomy is the
  -- whole argument.
  num∈α : (k : ℕ) → ⟨ (# k) ∈ˢ α ⟩
  num∈α k = Sum.rec
      (λ α∈ω → Empty.rec (α∉ω α∈ω))
      (Sum.rec (λ α≡ω → subst (λ w → ⟨ (# k) ∈ˢ w ⟩) (sym α≡ω) (#∈ω k))
               (λ ω∈α → ordα .fst (#∈ω k) ω∈α))
      (ord-tri α ordα ω ω-ord)

  -- And therefore a member of the STAGE at α: the numeral sits at the
  -- stage after itself and monotonicity carries it up.
  num∈L : (k : ℕ) → ⟨ (# k) ∈ˢ Lset α ⟩
  num∈L k = Lset-mono {α = α} {β = # (suc k)} (num∈α (suc k))
              {x = # k} (ord∈Lset-suc (# k) (numeral-ord k))

  -- The place x goes is the member of `Lset α` whose value is the
  -- numeral 0.  It is free of x entirely.
  xImage : ⟪ Lset α ⟫
  xImage = fiber (Lset α) (num∈L 0) .fst

  xImage-val : ⟪ Lset α ⟫↪ xImage ≡ # 0
  xImage-val = fiber (Lset α) (num∈L 0) .snd

-- The adjunction, read backwards: a member of `Lset α ∪ ⁅ x ⁆s` that
-- is not x is a member of `Lset α`.

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

-- The shift, at the stage.  `ShiftAbs` (src/L/Absorption.lagda.md)
-- transfers its three-case split, its three readback lemmas and its
-- sixteen-case injectivity matrix; `Adjoin.X-elim` replaces
-- `∈sucV-elim`, `W3` derives the numerals, and `shift-top` takes the
-- case decision `¬v∈ω` as an ARGUMENT because x may be a numeral.

module Shift (α x : S) (ordα : IsOrd α) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  module W = W3 α ordα α∉ω
  module A = Adjoin α x
  module SA = ShiftAbs α ordα α∉ω W.num∈α

  v-of : ⟪ A.X ⟫ → S
  v-of m = ⟪ A.X ⟫↪ m

  -- The "other" case's landing.  Being unequal to x is already enough,
  -- because the adjunction has exactly two parts.
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

  -- The matrix, corner for corner as `ShiftAbs.shift-inj`, with the
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

  -- x itself, as a member of the domain, lands on the numeral 0.
  x-lands-at-0 : (¬x∈ω : ⟨ x ∈ˢ ω ⟩ → Empty.⊥)
               → ⟪ Lset α ⟫↪ (shift (fiber A.X A.x∈X .fst)) ≡ # 0
  x-lands-at-0 ¬x∈ω = shift-top mx
    (λ v∈ω → ¬x∈ω (subst (λ w → ⟨ w ∈ˢ ω ⟩) (fiber A.X A.x∈X .snd) v∈ω))
    (fiber A.X A.x∈X .snd)
    where
    mx : ⟪ A.X ⟫
    mx = fiber A.X A.x∈X .fst

-- The subset hypothesis `x ⊆ Lset α` is bound and NOT USED: the type
-- keeps it because `BoundedSubsetAt`'s parameter list
-- (src/L/BoundedSubset.lagda.md) has it.

AbsorbsAt :
    (α x : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  → ⟪ Lset α ∪ ⁅ x ⁆s ⟫ ↪ ⟪ Lset α ⟫
AbsorbsAt α x ordα α∉ω _ = SH.shift , SH.shift-inj
  where
  module SH = Shift α x ordα α∉ω

-- =====================================================================
-- The collapse image of the hull is constructible.  The generic core
-- is at an ARBITRARY carrier M: no hull, no stage, no extensionality,
-- no ordinal.
-- =====================================================================

module Coll (M : S) where
  module C = Collapse M

  -- The WEAKEST hypothesis that closes the target: every collapse
  -- VALUE of a member of M is constructible.
  CoverL : Type (ℓ-suc ℓ)
  CoverL = (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ isL (C.π y) ⟩

  -- The chapter's own hypothesis, src/L/BoundedSubset.lagda.md
  -- (module Condense's `cover`).
  Cover : Type (ℓ-suc ℓ)
  Cover = (y : S) → ⟨ y ∈ˢ M ⟩
        → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁

  PiXinL : Type (ℓ-suc ℓ)
  PiXinL = (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ isL x ⟩

  -- Every member of the collapse image is the collapse value of a
  -- member of M (C.πX-member, src/V/Collapse.lagda.md), and CoverL
  -- says every such value is constructible.
  πX⊆L : CoverL → PiXinL
  πX⊆L cl x x∈πX = PT.rec (snd (isL x)) go (C.πX-member x x∈πX)
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ x)) → ⟨ isL x ⟩
    go (y , y∈M , e) = subst (λ w → ⟨ isL w ⟩) e (cl y y∈M)

  -- The chapter's hypothesis is already enough: the ordinal index is
  -- used, and its membership in C.πX is DISCARDED.
  cover→coverL : Cover → CoverL
  cover→coverL cov y y∈M = PT.rec (snd (isL (C.π y))) go (cov y y∈M)
    where
    go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩)
       → ⟨ isL (C.π y) ⟩
    go (γ , oγ , _ , h) = Lset→isL γ oγ (C.π y) h

  πX⊆L-from-cover : Cover → PiXinL
  πX⊆L-from-cover cov = πX⊆L (cover→coverL cov)

-- The site: the chapter's own HullStage telescope
-- (src/L/BoundedSubset.lagda.md).

module Site (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆L ∅∈λ
  module K = Coll HS.M

  Cover : Type (ℓ-suc ℓ)
  Cover = K.Cover

  Target : Type (ℓ-suc ℓ)
  Target = (x : S) → ⟨ x ∈ˢ HS.C.πX ⟩ → ⟨ isL x ⟩

  -- `Coll HS.M`'s C and `HullStage`'s C are the SAME `Collapse HS.M`,
  -- so no transport is needed between them.
  pix-in-L-at : Cover → Target
  pix-in-L-at cov = K.πX⊆L-from-cover cov

  -- The hull is extensional, src/L/BoundedSubset.lagda.md (HullExt).
  module HE = HullExt lam ordλ X X⊆L ∅∈λ

  Mext : isExt HS.M
  Mext = HE.hullExt

  module CIso = CollapseIso HS.M Mext

  -- The two restricted carriers: the collapse image and the class
  -- carrier of L (src/L/Hierarchy.lagda.md).
  module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ HS.C.πX) HS.C.πX-trans
  module AbsL  = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
  open AbsL using ( _^_ )

  -- A member of the collapse is a member of L, with the SAME underlying
  -- set.  `fst (toL cov k)` is `fst k` by eta, which is what makes the
  -- relabelling below cost nothing.
  toL : Target → CIso.I.SPM → AbsL.SM
  toL pil k = fst k , pil (fst k) (snd k)

  -- The class-carrier reading of Lset-only (src/L/Hierarchy.lagda.md)
  -- at a pinned parameter-free formula, read at w = zero, b = suc zero.
  LsetOnlyAt : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  LsetOnlyAt φ₀ = (γL : AbsL.SM ^ 2)
                → ⟨ γL AbsL.⊨ᵐ (embed φ₀) ⟩
                → IsOrd (fst (lookup (suc zero) γL))
                → fst (lookup zero γL) ≡ Lset (fst (lookup (suc zero) γL))

  HoodSoundP : Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
  HoodSoundP φ₀ =
    (v γ : S) (v∈ : ⟨ v ∈ˢ HS.C.πX ⟩) (γ∈ : ⟨ γ ∈ˢ HS.C.πX ⟩) → IsOrd γ
    → ⟨ ((v , v∈) ∷ (γ , γ∈) ∷ []) CIso.I.⊨ᵖᵐ (embed φ₀) ⟩
    → v ≡ Lset γ

  -- The chain: the inner reading at C.πX equals the ambient reading
  -- (AbsπX.abs₀); the ambient reading does not see which constant
  -- domain carries it (⊨-map along toL, plus the parameter-free
  -- fixpoint); the ambient reading equals the inner reading at L
  -- (AbsL.abs₀, backwards); and Lset-only reads it off.
  soundP-from-pix : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
                  → Target → LsetOnlyAt φ₀ → HoodSoundP φ₀
  soundP-from-pix φ₀ dφ pil only v γ v∈ γ∈ oγ h = only γL inner oγ
    where
    f : CIso.I.SPM → AbsL.SM
    f = toL pil

    δ : CIso.I.SPM ^ 2
    δ = (v , v∈) ∷ (γ , γ∈) ∷ []

    γL : AbsL.SM ^ 2
    γL = map f δ

    embed-fixed : mapFo f (embed φ₀) ≡ embed φ₀
    embed-fixed =
      mapFo-comp Empty.rec* f φ₀
      ∙ cong (λ g → mapFo g φ₀) (funExt (λ b → Empty.rec* b))

    amb-πX : ⟨ (map fst δ) AbsπX.⊨ᵛ (embed φ₀) ⟩
    amb-πX = subst ⟨_⟩ (AbsπX.abs₀ (mapΔ₀ Empty.rec* dφ) δ) h

    amb-L : ⟨ (map fst δ) AbsL.⊨ᵛ (embed φ₀) ⟩
    amb-L = subst ⟨_⟩
      (sym (cong (λ ψ → (map fst δ) AbsL.⊨ᵛ ψ) (sym embed-fixed)
             ∙ ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ f fst (embed φ₀) (map fst δ)))
      amb-πX

    inner : ⟨ γL AbsL.⊨ᵐ (embed φ₀) ⟩
    inner = subst ⟨_⟩ (sym (AbsL.abs₀ (mapΔ₀ Empty.rec* dφ) γL)) amb-L

  soundP-from-lset-only : (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
                        → Cover → LsetOnlyAt φ₀ → HoodSoundP φ₀
  soundP-from-lset-only φ₀ dφ cov = soundP-from-pix φ₀ dφ (pix-in-L-at cov)

-- The two site facts at the top level.

pix-in-L : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Site.Cover lam ordλ succλ X X⊆L ∅∈λ
  → Site.Target lam ordλ succλ X X⊆L ∅∈λ
pix-in-L = Site.pix-in-L-at

soundP-leg2 : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2) → Δ₀ φ₀
  → Site.Cover lam ordλ succλ X X⊆L ∅∈λ
  → Site.LsetOnlyAt lam ordλ succλ X X⊆L ∅∈λ φ₀
  → Site.HoodSoundP lam ordλ succλ X X⊆L ∅∈λ φ₀
soundP-leg2 = Site.soundP-from-lset-only
```
