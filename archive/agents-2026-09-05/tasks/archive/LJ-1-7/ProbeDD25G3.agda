{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe G3: THE SECOND CURE.  The master takes
-- `collapseCode : ⟪ πX ⟫ ↪ Code` as a hypothesis and calls the code
-- fiber's non-prop-ness a wall.  This probe discharges the composite
-- the master actually consumes, `⟪ πX ⟫ ↪ ⟪ α ⟫`, in two legs:
--
--   leg 1  ⟪ πX ⟫ ↪ ⟪ M ⟫.  NO choice.  The collapse fibre IS a
--          proposition, because π is injective on M.
--   leg 2  ⟪ M ⟫ ↪ ⟪ α ⟫.  The delivered least-of-the-class pattern of
--          `L.StageCardinal.Successor` (:275-320), transplanted: the
--          order on the codes is the master's own `count`.
--
-- Both legs are generic in the carrier, the code type and the count.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25G3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import V.Collapse {ℓ} using ( module Collapse; isExt )
open import V.Presentation {ℓ} using ( fiber; member; ↪-inj )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma using ( _×_; _,_ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Foundations.Prelude using ( toPathP )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )

open hPropStructure 𝒮ᵥ

_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- =====================================================================
-- LEG 1.  The inverse collapse.  The fibre of π over a collapse value
-- is a PROPOSITION, so the truncation is absorbed and no order is
-- needed.  This is the leg the return calls blocked.
-- =====================================================================

module InvColl (M : S) (Mext : isExt M) where
  module C = Collapse M
  module CI = C.InjExt Mext

  Fib : S → Type (ℓ-suc ℓ)
  Fib z = Σ[ m ∈ ⟪ M ⟫ ] (C.π (⟪ M ⟫↪ m) ≡ z)

  isPropFib : (z : S) → isProp (Fib z)
  isPropFib z (m , p) (n , q) = ΣPathP (mn , toPathP (isSetS _ _ _ _))
    where
    ↪mn : ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
    ↪mn = CI.π-inj (⟪ M ⟫↪ m) (⟪ M ⟫↪ n) (member M m) (member M n)
            (p ∙ sym q)
    mn : m ≡ n
    mn = ↪-inj {a = M} ↪mn

  getFib : (z : S) → ⟨ z ∈ˢ C.πX ⟩ → Fib z
  getFib z z∈ = PT.rec (isPropFib z) go (C.πX-member z z∈)
    where
    go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) → Fib z
    go (y , y∈M , e) =
      fiber M y∈M .fst ,
      cong C.π (fiber M y∈M .snd) ∙ e

  inv : ⟪ C.πX ⟫ → ⟪ M ⟫
  inv p = getFib (⟪ C.πX ⟫↪ p) (member C.πX p) .fst

  inv-inj : (p q : ⟪ C.πX ⟫) → inv p ≡ inv q → p ≡ q
  inv-inj p q e = ↪-inj {a = C.πX} step
    where
    ep : C.π (⟪ M ⟫↪ (inv p)) ≡ ⟪ C.πX ⟫↪ p
    ep = getFib (⟪ C.πX ⟫↪ p) (member C.πX p) .snd
    eq : C.π (⟪ M ⟫↪ (inv q)) ≡ ⟪ C.πX ⟫↪ q
    eq = getFib (⟪ C.πX ⟫↪ q) (member C.πX q) .snd
    step : ⟪ C.πX ⟫↪ p ≡ ⟪ C.πX ⟫↪ q
    step = sym ep ∙ cong (λ m → C.π (⟪ M ⟫↪ m)) e ∙ eq

  leg1 : ⟪ C.πX ⟫ ↪ ⟪ M ⟫
  leg1 = inv , inv-inj

-- =====================================================================
-- LEG 2.  The least code.  `L.StageCardinal.Successor.h` (:292) does
-- exactly this for the definable powerset: a member is MERELY some
-- code, `leastOf` over the ordinal's own well-order picks the least
-- count value in the class, and injectivity uses count-injectivity and
-- ↪-inj only.  Transplanted verbatim in shape.
-- =====================================================================

-- The well-order `w` below is delivered: `L.StageCardinal.OrdSWO.ordSWO`
-- (:253) is exactly `SWO ⟪ α ⟫` for an ordinal α.

module CodeSelect (α : S) (oα : IsOrd α) (w : SWO {ℓ} ⟪ α ⟫)
  (M : S) (Code : Type ℓ) (val : Code → S)
  (mem-code : (x : S) → ⟨ x ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (val c ≡ x) ∥₁)
  (cnt : Code → ⟪ α ⟫)
  (cnt-inj : (c d : Code) → cnt c ≡ cnt d → c ≡ d)
  where

  cls : ⟪ M ⟫ → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  cls m y = ( ∥ Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ y)) ∥₁
            , squash₁ )

  nonempty : (m : ⟪ M ⟫) → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ cls m y ⟩ ∥₁
  nonempty m = PT.map (λ { (c , e) → cnt c , ∣ c , (e , refl) ∣₁ })
                      (mem-code (⟪ M ⟫↪ m) (member M m))

  h : ⟪ M ⟫ → ⟪ α ⟫
  h m = fst (leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m))

  h-inj : (m n : ⟪ M ⟫) → h m ≡ h n → m ≡ n
  h-inj m n e = ↪-inj {a = M} (go pm)
    where
    lm = leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls m) (nonempty m)
    ln = leastOf w {ℓ'' = ℓ-suc ℓ} lem (cls n) (nonempty n)
    pm : ⟨ cls m (fst ln) ⟩
    pm = subst (λ y → ⟨ cls m y ⟩) e (fst (snd lm))
    pn : ⟨ cls n (fst ln) ⟩
    pn = fst (snd ln)
    go : ⟨ cls m (fst ln) ⟩ → ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
    go = PT.rec (isSetS (⟪ M ⟫↪ m) (⟪ M ⟫↪ n)) go₁
      where
      go₁ : Σ[ c ∈ Code ] ((val c ≡ ⟪ M ⟫↪ m) × (cnt c ≡ fst ln))
          → ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
      go₁ (c , (ec , en)) =
        PT.rec (isSetS (⟪ M ⟫↪ m) (⟪ M ⟫↪ n)) go₂ pn
        where
        go₂ : Σ[ d ∈ Code ] ((val d ≡ ⟪ M ⟫↪ n) × (cnt d ≡ fst ln))
            → ⟪ M ⟫↪ m ≡ ⟪ M ⟫↪ n
        go₂ (d , (ed , en')) =
          sym ec ∙ cong val (cnt-inj c d (en ∙ sym en')) ∙ ed

  leg2 : ⟪ M ⟫ ↪ ⟪ α ⟫
  leg2 = h , h-inj

-- =====================================================================
-- THE COMPOSITE the master consumes: ⟪ πX ⟫ ↪ ⟪ α ⟫, with NO
-- `collapseCode` hypothesis.
-- =====================================================================

module Discharge (α : S) (oα : IsOrd α) (w : SWO {ℓ} ⟪ α ⟫)
  (M : S) (Mext : isExt M) (Code : Type ℓ) (val : Code → S)
  (mem-code : (x : S) → ⟨ x ∈ˢ M ⟩ → ∥ Σ[ c ∈ Code ] (val c ≡ x) ∥₁)
  (cnt : Code → ⟪ α ⟫)
  (cnt-inj : (c d : Code) → cnt c ≡ cnt d → c ≡ d)
  where

  module I = InvColl M Mext
  module CS = CodeSelect α oα w M Code val mem-code cnt cnt-inj

  πX↪α : ⟪ I.C.πX ⟫ ↪ ⟪ α ⟫
  πX↪α = (λ p → CS.h (I.inv p))
       , (λ p q e → I.inv-inj p q (CS.h-inj (I.inv p) (I.inv q) e))
