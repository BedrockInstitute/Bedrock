{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.327] PROBE.  The square law needs a FORMULA.  This file measures
-- the two pieces that a described `pairω` needs FIRST, and it measures
-- them at the delivered vocabulary.
--
-- PART 1.  THE DOMAIN L-SET.  `pairω : ⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫`
-- (src/L/InjChain.lagda.md:175-176) has a TYPE PRODUCT for a domain.
-- `InjCode F a b` (src/L/Cardinal.lagda.md:223-228) demands an L-SET for
-- a domain.  MEASURED by grep: `src/L` has no cartesian product set.
-- Part 1 builds it, generic in the two sets, from delivered parts only:
-- `PairBound` (src/L/InjChain.lagda.md:276-311) for the bound and
-- `hasSeparationL` (src/L/Axioms/Full.lagda.md:144-145) for the carve.
--
-- PART 2.  THE ORDER, AS A FORMULA.  `pairω` is the collapse of the
-- Gödel order `_≺_` (src/L/Ordinal/SquareLaw.lagda.md:215-218), whose
-- base is MEMBERSHIP (`:148-149`).  So the order is first-order over the
-- delivered atoms.  Part 2 writes the max atom and proves its adequacy
-- in both directions, at the ambient `maxOrd` (`:200-201`).
--
-- Nothing lands.  Tracked probe.  ONE agda process under
-- GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-327.ProbeLJ1327A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; con; var; ∃̇∈; _∈̇_; _≐_; _∧̇_; _∨̇_ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst )
open import L.InjChain {ℓ} lem using ( module PairBound )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( Tri; lt; eq; gt )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module ModelL = FOL.ZFModel 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- PART 1.  THE PRODUCT SET, carved.
--
-- De Bruijn: inside `∃̇∈ (con A)` the bound x is 0 and p is 1.  Inside
-- the inner `∃̇∈ (con B)` the bound y is 0, x is 1 and p is 2.
-- ---------------------------------------------------------------------

prodInner : S → Formula S 2
prodInner B = ∃̇∈ (con B) (prAtL (suc (suc zero)) (suc zero) zero)

prodFo : S → S → Formula S 1
prodFo A B = ∃̇∈ (con A) (prodInner B)

module Prod (A B : S) where

  private
    module PB = PairBound A B

    at : (p x y : S)
       → ⟨ (y ∷ x ∷ p ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
       ≡ (fst p ≡ pr (fst x) (fst y))
    at p x y = cong ⟨_⟩
      (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ p ∷ []))

  opaque
    P : S
    P = fst (fst (hasSeparationL PB.bnd (prodFo A B)))

    P-spec : (z : S) → (z ∈ˢ P) ≡ ((z ∈ˢ PB.bnd) ⊓ ((z ∷ []) ⊨ prodFo A B))
    P-spec = snd (fst (hasSeparationL PB.bnd (prodFo A B)))

  -- The two readings of membership, exactly the delivered shape.
  P-in : (x y : S) → ⟨ x ∈ˢ A ⟩ → ⟨ y ∈ˢ B ⟩
       → ⟨ pr (fst x) (fst y) ∈ fst P ⟩
  P-in x y mx my = subst (λ w → ⟨ w ∈ fst P ⟩) (prʟ-fst x y)
    (subst ⟨_⟩ (sym (P-spec q))
      ( subst (λ w → ⟨ w ∈ fst PB.bnd ⟩) (sym (prʟ-fst x y))
          (PB.below x y mx my)
      , ∣ x , (mx , ∣ y , (my , subst (λ T → T) (sym (at q x y))
          (prʟ-fst x y)) ∣₁) ∣₁ ))
    where
    q : S
    q = prʟ x y

  P-out : (z : S) → ⟨ z ∈ˢ P ⟩
        → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
            (⟨ x ∈ˢ A ⟩ × (⟨ y ∈ˢ B ⟩ × (fst z ≡ pr (fst x) (fst y)))) ∥₁
  P-out z h = PT.rec squash₁ outer (snd (subst ⟨_⟩ (P-spec z) h))
    where
    outer : Σ[ x ∈ S ] (⟨ x ∈ˢ A ⟩ × ⟨ (x ∷ z ∷ []) ⊨ prodInner B ⟩)
          → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ]
              (⟨ x ∈ˢ A ⟩ × (⟨ y ∈ˢ B ⟩ × (fst z ≡ pr (fst x) (fst y)))) ∥₁
    outer (x , (mx , hy)) = PT.map inner hy
      where
      inner : Σ[ y ∈ S ] (⟨ y ∈ˢ B ⟩
                × ⟨ (y ∷ x ∷ z ∷ []) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩)
            → Σ[ x' ∈ S ] Σ[ y ∈ S ]
                (⟨ x' ∈ˢ A ⟩ × (⟨ y ∈ˢ B ⟩ × (fst z ≡ pr (fst x') (fst y))))
      inner (y , (my , hp)) =
        x , y , mx , my , subst (λ T → T) (at z x y) hp

-- ---------------------------------------------------------------------
-- PART 2.  THE MAX ATOM, and its adequacy at the ambient `maxOrd`.
--
-- `maxOrd` (src/L/Ordinal/SquareLaw.lagda.md:200-201) is `maxGo` under
-- the trichotomy `tri₁` (`:195-198`, `:154-155`), and `_≺₁_` is
-- membership (`:148-149`).  So the max is a two-case first-order
-- condition over `∈̇` and `≐`.
-- ---------------------------------------------------------------------

maxAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
maxAt m a b = (((var b ∈̇ var a) ∨̇ (var b ≐ var a)) ∧̇ (var m ≐ var a))
           ∨̇ ((var a ∈̇ var b) ∧̇ (var m ≐ var b))

module MaxFo (α : S) (oα : IsOrd (fst α)) where

  private
    toS : ⟪ fst α ⟫ → S
    toS u = ⟪ fst α ⟫↪ u
          , isL-trans {x = fst α} {y = ⟪ fst α ⟫↪ u}
              (member (fst α) u) (snd α)

  mx : ⟪ fst α ⟫ → ⟪ fst α ⟫ → ⟪ fst α ⟫
  mx = SQ.maxOrd (fst α) oα

  -- The environment: b is 0, a is 1, m is 2.
  Ctx : S → ⟪ fst α ⟫ → ⟪ fst α ⟫ → S ^ 3
  Ctx m u v = toS v ∷ toS u ∷ m ∷ []

  Sat : S → ⟪ fst α ⟫ → ⟪ fst α ⟫ → Type (ℓ-suc ℓ)
  Sat m u v = ⟨ Ctx m u v ⊨ maxAt (suc (suc zero)) (suc zero) zero ⟩

  -- INTO.  The ambient max satisfies the atom.
  maxAt-in : (u v : ⟪ fst α ⟫) → Sat (toS (mx u v)) u v
  maxAt-in u v = go (SQ.tri₁ (fst α) oα u v)
    where
    go : (t : Tri (SQ._≺₁_ (fst α) oα u v) (u ≡ v) (SQ._≺₁_ (fst α) oα v u))
       → Sat (toS (SQ.maxGo (fst α) oα u v t)) u v
    go (lt h) = ∣ inr (h , refl) ∣₁
    go (eq p) = ∣ inl (∣ inr (cong (⟪ fst α ⟫↪) (sym p)) ∣₁ , refl) ∣₁
    go (gt h) = ∣ inl (∣ inl h ∣₁ , refl) ∣₁

  -- OUT.  Anything that satisfies the atom IS the ambient max.
  maxAt-out : (m : S) (u v : ⟪ fst α ⟫) → Sat m u v
            → fst m ≡ ⟪ fst α ⟫↪ (mx u v)
  maxAt-out m u v h =
    PT.rec (setIsSet (fst m) (⟪ fst α ⟫↪ (mx u v))) side h
    where
    tri = SQ.tri₁ (fst α) oα u v

    -- The left case says m is a, so the max must be a too.
    leftGo : (t : Tri (SQ._≺₁_ (fst α) oα u v) (u ≡ v) (SQ._≺₁_ (fst α) oα v u))
           → SQ._≺₁_ (fst α) oα v u ⊎ (⟪ fst α ⟫↪ v ≡ ⟪ fst α ⟫↪ u)
           → fst m ≡ ⟪ fst α ⟫↪ u
           → fst m ≡ ⟪ fst α ⟫↪ (SQ.maxGo (fst α) oα u v t)
    leftGo (lt hu) (inl hv) e =
      Empty.rec (SQ.irr₁ (fst α) oα u (SQ.trans₁ (fst α) oα u v u hu hv))
    leftGo (lt hu) (inr q) e =
      Empty.rec (SQ.irr₁ (fst α) oα u
        (subst (λ w → ⟨ ⟪ fst α ⟫↪ u ∈ w ⟩) q hu))
    leftGo (eq p) _ e = e
    leftGo (gt _) _ e = e

    rightGo : (t : Tri (SQ._≺₁_ (fst α) oα u v) (u ≡ v) (SQ._≺₁_ (fst α) oα v u))
            → SQ._≺₁_ (fst α) oα u v
            → fst m ≡ ⟪ fst α ⟫↪ v
            → fst m ≡ ⟪ fst α ⟫↪ (SQ.maxGo (fst α) oα u v t)
    rightGo (lt _) _ e = e
    rightGo (eq p) hu e =
      Empty.rec (SQ.irr₁ (fst α) oα u
        (subst (λ w → ⟨ ⟪ fst α ⟫↪ u ∈ w ⟩) (cong (⟪ fst α ⟫↪) (sym p)) hu))
    rightGo (gt hv) hu e =
      Empty.rec (SQ.irr₁ (fst α) oα u (SQ.trans₁ (fst α) oα u v u hu hv))

    side : (⟨ Ctx m u v ⊨ (((var zero ∈̇ var (suc zero))
                            ∨̇ (var zero ≐ var (suc zero)))
                          ∧̇ (var (suc (suc zero)) ≐ var (suc zero))) ⟩
            ⊎ ⟨ Ctx m u v ⊨ ((var (suc zero) ∈̇ var zero)
                          ∧̇ (var (suc (suc zero)) ≐ var zero)) ⟩)
         → fst m ≡ ⟪ fst α ⟫↪ (mx u v)
    side (inl (hd , e)) =
      PT.rec (setIsSet (fst m) (⟪ fst α ⟫↪ (mx u v)))
        (λ d → leftGo tri d e) hd
    side (inr (hd , e)) = rightGo tri hd e
