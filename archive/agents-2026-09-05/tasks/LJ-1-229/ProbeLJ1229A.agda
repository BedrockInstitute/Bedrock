{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.229] probe A: A2's range set and ranAt, the block every other
-- block names.  [LJ-1.134] measured the core (injAt + Part A + Part D)
-- at 78 lines and left two pieces unpriced: the range set, produced by
-- replacement over the graph, and the ranAt formula mirroring domAt.
-- This probe builds both, and separates the description plus adequacy
-- (what A4 consumes) from the readback (what A4 does not).
--
--   S1  injAt with injAt-out and injAt-in.  Description plus adequacy.
--   S2  Extract.  The readback, first half: Dom to S, with injectivity.
--   S3  rangeGraph with adequacy, and Range: the range set C, produced
--       by hasReplacementL over the graph.
--   S4  inRanAt, ranAt with out/in/intro, mirroring domAt.
--   S5  RanHolds: C satisfies ranAt, discharging [LJ-1.134]'s "every
--       value lies in C" hypothesis.
--   S6  Small.  The readback, second half: the honest injection between
--       the small index types, with C supplied rather than assumed.
--   A2  the whole, assembled.  Only sv, dm, ij are assumed.
--
-- Probe only.  Nothing lands in src/.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g"; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-229.ProbeLJ1229A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; svAt; svAt-out
        ; domAt; domAt-in; domAt-out
        ; prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.Axioms.Full {ℓ} lem using ( hasReplacementL )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- S1. Injectivity of a graph, in the object language.
-- The mirror of svAt: the second component determines the first.
-- ---------------------------------------------------------------------

injAt : ∀ {n} → Fin n → Formula S n
injAt f = ∀̇ (∀̇ (∀̇ (
      appAt (suc (suc (suc f))) (suc zero) (suc (suc zero))
  ⇒̇ (appAt (suc (suc (suc f))) zero (suc (suc zero))
  ⇒̇ (var (suc zero) ≐ var zero)))))

module _ {n : ℕ} (f : Fin n) (γ : S ^ n) where
  private
    Holds₀ : S → S → Type (ℓ-suc ℓ)
    Holds₀ x y = ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩

    at₁ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) (suc zero) (suc (suc zero)))
        ≡ (pr (fst x) (fst y) ∈ fst (lookup f γ))
    at₁ y x x' = appAt-adequate (suc (suc (suc f))) (suc zero) (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

    at₂ : (y x x' : S)
        → ((x' ∷ x ∷ y ∷ γ) ⊨ appAt (suc (suc (suc f))) zero (suc (suc zero)))
        ≡ (pr (fst x') (fst y) ∈ fst (lookup f γ))
    at₂ y x x' = appAt-adequate (suc (suc (suc f))) zero (suc (suc zero))
                   (x' ∷ x ∷ y ∷ γ)

  injAt-out : ⟨ γ ⊨ injAt f ⟩
            → (y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x'
  injAt-out h y x x' p q = h y x x'
    (subst ⟨_⟩ (sym (at₁ y x x')) p) (subst ⟨_⟩ (sym (at₂ y x x')) q)

  injAt-in : ((y x x' : S) → Holds₀ x y → Holds₀ x' y → fst x ≡ fst x')
           → ⟨ γ ⊨ injAt f ⟩
  injAt-in h y x x' p q = h y x x'
    (subst ⟨_⟩ (at₁ y x x') p) (subst ⟨_⟩ (at₂ y x x') q)

-- ---------------------------------------------------------------------
-- S2. The readback, first half: the fibre extraction.
-- ---------------------------------------------------------------------

module Extract (F D : S)
               (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
               (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

  γ : S ^ 2
  γ = F ∷ D ∷ []

  Holds : S → S → Type (ℓ-suc ℓ)
  Holds x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩

  Fib : S → Type (ℓ-suc ℓ)
  Fib x = Σ[ y ∈ S ] Holds x y

  isPropFib : (x : S) → isProp (Fib x)
  isPropFib x (y , p) (y' , q) =
    Σ≡Prop (λ w → snd (pr (fst x) (fst w) ∈ fst F))
      (Σ≡Prop (λ z → snd (isL z)) (svAt-out zero γ sv x y y' p q))

  toVal : (x : S) → ∥ Fib x ∥₁ → Fib x
  toVal x = PT.rec (isPropFib x) (λ z → z)

  Dom : Type (ℓ-suc ℓ)
  Dom = Σ[ x ∈ S ] ⟨ fst x ∈ fst D ⟩

  fib : (u : Dom) → Fib (fst u)
  fib (x , m) = toVal x (domAt-in zero (suc zero) γ dm x m)

  toFun : Dom → S
  toFun u = fst (fib u)

  toFun-graph : (u : Dom) → Holds (fst u) (toFun u)
  toFun-graph u = snd (fib u)

  module _ (ij : ⟨ γ ⊨ injAt zero ⟩) where

    toFun-inj : (u v : Dom) → fst (toFun u) ≡ fst (toFun v)
              → fst (fst u) ≡ fst (fst v)
    toFun-inj u v e = injAt-out zero γ ij (toFun v) (fst u) (fst v)
      (subst (λ w → ⟨ pr (fst (fst u)) w ∈ fst F ⟩) e (toFun-graph u))
      (toFun-graph v)

-- ---------------------------------------------------------------------
-- S3. The range graph, and the range set C produced by replacement.
-- ---------------------------------------------------------------------

-- The graph F, read with the value first and the argument second, as
-- hasReplacementL wants it: (y ∷ x ∷ []) ⊨ rangeGraph F means the pair
-- (x, y) lies in F.
rangeGraph : S → Formula S 2
rangeGraph F = ∃̇∈ (con F) (prAtL zero (suc (suc zero)) (suc zero))

rangeGraph-adequate : (F x y : S)
  → ((y ∷ x ∷ []) ⊨ rangeGraph F) ≡ (pr (fst x) (fst y) ∈ fst F)
rangeGraph-adequate F x y = ⇔toPath fwd bwd
  where
  a = fst x
  b = fst y

  read : (z : S) → ⟨ (z ∷ y ∷ x ∷ []) ⊨ prAtL zero (suc (suc zero)) (suc zero) ⟩
       → fst z ≡ pr a b
  read z h = subst ⟨_⟩ (prAtL-adequate zero (suc (suc zero)) (suc zero)
               (z ∷ y ∷ x ∷ [])) h

  fwd : ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩ → ⟨ pr a b ∈ fst F ⟩
  fwd = PT.rec (snd (pr a b ∈ fst F))
    (λ { (z , (z∈F , h)) → subst (λ w → ⟨ w ∈ fst F ⟩) (read z h) z∈F })

  bwd : ⟨ pr a b ∈ fst F ⟩ → ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩
  bwd h = ∣ prʟ x y
    , ( subst (λ w → ⟨ w ∈ fst F ⟩) (sym (prʟ-fst x y)) h
      , subst ⟨_⟩ (sym (prAtL-adequate zero (suc (suc zero)) (suc zero)
          (prʟ x y ∷ y ∷ x ∷ []))) (prʟ-fst x y) ) ∣₁

-- The range set.  The domain D with the graph formula, and the
-- functionality that single-valuedness plus the domain give it.
module Range (F D : S)
             (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
             (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

  open Extract F D sv dm

  funct : (x : S) → ⟨ x ∈ˢ D ⟩
        → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩)
  funct x x∈D = ctr , uniq
    where
    y₀ : Fib x
    y₀ = toVal x (domAt-in zero (suc zero) γ dm x x∈D)

    ctr : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩
    ctr = y₀ .fst , subst ⟨_⟩ (sym (rangeGraph-adequate F x (y₀ .fst))) (y₀ .snd)

    uniq : (r : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ rangeGraph F ⟩) → ctr ≡ r
    uniq (y , q) = Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ rangeGraph F))
      (Σ≡Prop (λ z → snd (isL z))
        (svAt-out zero γ sv x (y₀ .fst) y (y₀ .snd)
          (subst ⟨_⟩ (rangeGraph-adequate F x y) q)))

  Image : S → Ω
  Image y = ⋁ S (λ x → (x ∈ˢ D) ⊓ ((y ∷ x ∷ []) ⊨ rangeGraph F))

  rep : SetOf Image
  rep = hasReplacementL D (rangeGraph F) funct .fst

  C : S
  C = rep .fst

  C-mem : (y : S) → (y ∈ˢ C) ≡ Image y
  C-mem = rep .snd

-- ---------------------------------------------------------------------
-- S4. The range formula, mirroring domAt.
-- ---------------------------------------------------------------------

inRanAt : ∀ {n} → Fin n → Fin n → Formula S n
inRanAt f x = ∃̇ (appAt (suc f) zero (suc x))

inRanAt-adequate : ∀ {n} (f x : Fin n) (γ : S ^ n)
  → (γ ⊨ inRanAt f x)
  ≡ (∃[ y ∶ S ] (pr (fst y) (fst (lookup x γ)) ∈ fst (lookup f γ)))
inRanAt-adequate f x γ =
  cong (⋁ S) (funExt (λ y → appAt-adequate (suc f) zero (suc x) (y ∷ γ)))

ranAt : ∀ {n} → Fin n → Fin n → Formula S n
ranAt f c = ∀̇ ( (inRanAt (suc f) zero ⇒̇ (var zero ∈̇ var (suc c)))
             ∧̇ ((var zero ∈̇ var (suc c)) ⇒̇ inRanAt (suc f) zero) )

module _ {n : ℕ} (f c : Fin n) (γ : S ^ n) where
  private
    step : (y : S)
         → ((y ∷ γ) ⊨ inRanAt (suc f) zero)
         ≡ (∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)))
    step y = inRanAt-adequate (suc f) zero (y ∷ γ)

  ranAt-out : ⟨ γ ⊨ ranAt f c ⟩ → (x y : S)
            → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
            → ⟨ fst y ∈ fst (lookup c γ) ⟩
  ranAt-out h x y p = h y .fst (subst ⟨_⟩ (sym (step y)) ∣ x , p ∣₁)

  ranAt-in : ⟨ γ ⊨ ranAt f c ⟩ → (y : S) → ⟨ fst y ∈ fst (lookup c γ) ⟩
           → ∥ (Σ[ x ∈ S ] ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩) ∥₁
  ranAt-in h y m = subst ⟨_⟩ (step y) (h y .snd m)

  ranAt-intro : ((y : S)
                 → (⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩
                    → ⟨ fst y ∈ fst (lookup c γ) ⟩)
                 × (⟨ fst y ∈ fst (lookup c γ) ⟩
                    → ⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst (lookup f γ)) ⟩))
              → ⟨ γ ⊨ ranAt f c ⟩
  ranAt-intro g y = (λ h → g y .fst (subst ⟨_⟩ (step y) h))
                  , (λ m → subst ⟨_⟩ (sym (step y)) (g y .snd m))

-- ---------------------------------------------------------------------
-- S5. The range set satisfies ranAt.  This is where [LJ-1.134]'s
-- "every value lies in C" hypothesis is supplied.
-- ---------------------------------------------------------------------

module RanHolds (F D : S)
                (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
                (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩) where

  module R = Range F D sv dm

  C : S
  C = R.C

  holds : ⟨ (F ∷ C ∷ []) ⊨ ranAt zero (suc zero) ⟩
  holds = ranAt-intro zero (suc zero) (F ∷ C ∷ []) (λ y → fwd y , bwd y)
    where
    fwd : (y : S) → ⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
        → ⟨ fst y ∈ fst C ⟩
    fwd y = PT.rec (snd (fst y ∈ fst C))
      (λ { (x , p) → subst ⟨_⟩ (sym (R.C-mem y))
        ∣ x , (domAt-out zero (suc zero) (F ∷ D ∷ []) dm x y p
             , subst ⟨_⟩ (sym (rangeGraph-adequate F x y)) p) ∣₁ })

    bwd : (y : S) → ⟨ fst y ∈ fst C ⟩
        → ⟨ ∃[ x ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
    bwd y m = PT.map (λ { (x , (x∈D , g)) →
        x , subst ⟨_⟩ (rangeGraph-adequate F x y) g })
      (subst ⟨_⟩ (R.C-mem y) m)

-- ---------------------------------------------------------------------
-- S6. The readback, second half: the honest injection between the
-- small index types, with C supplied rather than assumed.
-- ---------------------------------------------------------------------

module Small (F D C : S)
             (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
             (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
             (ij : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
             (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst C ⟩) where

  module E = Extract F D sv dm

  toS : ⟪ fst D ⟫ → S
  toS m = ⟪ fst D ⟫↪ m
        , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

  at : ⟪ fst D ⟫ → E.Dom
  at m = toS m , member (fst D) m

  fib : (m : ⟪ fst D ⟫)
      → Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst (E.toFun (at m)))
  fib m = fiber (fst C)
    (ran (toS m) (E.toFun (at m)) (E.toFun-graph (at m)))

  small : ⟪ fst D ⟫ → ⟪ fst C ⟫
  small m = fst (fib m)

  small-inj : (m n : ⟪ fst D ⟫) → small m ≡ small n → m ≡ n
  small-inj m n e = ↪-inj {a = fst D} {m = m} {n = n}
    (E.toFun-inj ij (at m) (at n)
      (sym (snd (fib m)) ∙ cong ⟪ fst C ⟫↪ e ∙ snd (fib n)))

-- ---------------------------------------------------------------------
-- The whole of A2, assembled.  Only the graph hypotheses sv, dm, ij are
-- assumed.  C is produced, not assumed.
-- ---------------------------------------------------------------------

module A2 (F D : S)
          (sv : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
          (dm : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
          (ij : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩) where

  module H = RanHolds F D sv dm

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst H.C ⟩
  ran = ranAt-out zero (suc zero) (F ∷ H.C ∷ []) H.holds

  module S = Small F D H.C sv dm ij ran

  injection : ⟪ fst D ⟫ → ⟪ fst H.C ⟫
  injection = S.small

  injection-inj : (m n : ⟪ fst D ⟫) → injection m ≡ injection n → m ≡ n
  injection-inj = S.small-inj
