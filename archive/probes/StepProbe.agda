{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module StepProbe {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate )
open import L.Godel.Definable {ℓ}
  using ( interAt; interAt-out; interAt-in
        ; allTuplesAt; valuesAt; valuesAt-out; valuesAt-in )
open import L.Godel.Operations {ℓ} using ( _∩_; values )
open import L.Godel.Tuples {ℓ} using ( allTuples )
import FOL.Absoluteness

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 x = suc (suc x)

  sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
  sh3 x = suc (suc (suc x))

  sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
  sh4 x = suc (suc (suc (suc x)))

  sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
  sh5 x = suc (suc (suc (suc (suc x))))

-- ----------------------------------------------------------------
-- The closure layer, over slots.  A level is a TABLE: a functional
-- set of (numeral arity, family) pairs.  The layer formula is one
-- disjunction over a next-level slot: every member of the next level
-- is already in the previous level, or arises as one of the three
-- representative op-images (intersection, allTuples at its numeral,
-- values of an arity-one family).
-- ----------------------------------------------------------------

-- Functionality conjunct for the level table: the same arity key has
-- at most one family, so a member of a slice has a unique arity.
FunAt : ∀ {n} → Fin n → Formula S n
FunAt t = ∀̇ (∀̇ (∀̇ (
    ( appAt (sh3 t) (suc (suc zero)) (suc zero)
    ∧̇ appAt (sh3 t) (suc (suc zero)) zero )
  ⇒̇ (var (suc zero) ≐ var zero) )))

module _ {n : ℕ} (t : Fin n) (γ : S ^ n) where
  Fun-out : ⟨ γ ⊨ FunAt t ⟩ → (u v v' : S)
          → ⟨ pr (fst u) (fst v) ∈ fst (lookup t γ) ⟩
          → ⟨ pr (fst u) (fst v') ∈ fst (lookup t γ) ⟩
          → fst v ≡ fst v'
  Fun-out f u v v' p q =
    f u v v'
      ( subst ⟨_⟩ (sym (appAt-adequate (sh3 t) (suc (suc zero)) (suc zero)
          (v' ∷ v ∷ u ∷ γ))) p
      , subst ⟨_⟩ (sym (appAt-adequate (sh3 t) (suc (suc zero)) zero
          (v' ∷ v ∷ u ∷ γ))) q )

  Fun-in : ((u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup t γ) ⟩
          → ⟨ pr (fst u) (fst v') ∈ fst (lookup t γ) ⟩
          → fst v ≡ fst v')
         → ⟨ γ ⊨ FunAt t ⟩
  Fun-in hstep u v v' p =
    hstep u v v'
      ( subst ⟨_⟩ (appAt-adequate (sh3 t) (suc (suc zero)) (suc zero)
          (v' ∷ v ∷ u ∷ γ)) (p .fst) )
      ( subst ⟨_⟩ (appAt-adequate (sh3 t) (suc (suc zero)) zero
          (v' ∷ v ∷ u ∷ γ)) (p .snd) )

-- The intersection disjunct: the entry (e) is a pair (k, z) with
-- z = X ∩ Y for two same-arity members (k, X), (k, Y) of the
-- previous level (p).  Bound order: Y ∷ X ∷ z ∷ k ∷ γ.
InterDisjAt : ∀ {n} → Fin n → Fin n → Formula S n
InterDisjAt e p = ∃̇ (∃̇ (∃̇ (∃̇ (
    prAtL (sh4 e) (suc (suc (suc zero))) (suc (suc zero))
  ∧̇ ( appAt (sh4 p) (suc (suc (suc zero))) (suc zero)
    ∧̇ ( appAt (sh4 p) (suc (suc (suc zero))) zero
      ∧̇ interAt (suc (suc zero)) (suc zero) zero ))))))

module _ {n : ℕ} (e p : Fin n) (γ : S ^ n) where
  InterDisj-out : ⟨ γ ⊨ InterDisjAt e p ⟩
                → ∥ Σ[ k ∈ S ] Σ[ z ∈ S ] Σ[ X ∈ S ] Σ[ Y ∈ S ]
                    ( (fst (lookup e γ) ≡ pr (fst k) (fst z))
                    × ⟨ pr (fst k) (fst X) ∈ fst (lookup p γ) ⟩
                    × ⟨ pr (fst k) (fst Y) ∈ fst (lookup p γ) ⟩
                    × (fst z ≡ fst X ∩ fst Y) ) ∥₁
  InterDisj-out =
    PT.rec PT.squash₁ (λ { (k , w₁) →
    PT.rec PT.squash₁ (λ { (z , w₂) →
    PT.rec PT.squash₁ (λ { (X , w₃) →
    PT.rec PT.squash₁ (λ { (Y , body) →
      ∣ k , z , X , Y ,
        ( subst ⟨_⟩ (prAtL-adequate (sh4 e) (suc (suc (suc zero)))
            (suc (suc zero)) (Y ∷ X ∷ z ∷ k ∷ γ)) (body .fst)
        , ( subst ⟨_⟩ (appAt-adequate (sh4 p) (suc (suc (suc zero)))
              (suc zero) (Y ∷ X ∷ z ∷ k ∷ γ)) (body .snd .fst)
          , ( subst ⟨_⟩ (appAt-adequate (sh4 p) (suc (suc (suc zero))) zero
                (Y ∷ X ∷ z ∷ k ∷ γ)) (body .snd .snd .fst)
            , interAt-out (suc (suc zero)) (suc zero) zero
                (Y ∷ X ∷ z ∷ k ∷ γ) (body .snd .snd .snd) ) ) ) ∣₁
    }) w₃ }) w₂ }) w₁ })

-- The allTuples disjunct: the entry is a pair (m, z) with
-- z = allTuples A m.  Bound order: z ∷ m ∷ γ.  The arity enters as
-- the entry's own first component; the allTuplesAt reading is
-- conditional on that component being a numeral (the Table chapter's
-- conditional-clause pattern).
AllTuplesDisjAt : ∀ {n} → Fin n → Fin n → Formula S n
AllTuplesDisjAt {n} e a = ∃̇ (∃̇ (
    prAtL (sh2 e) (suc zero) zero
  ∧̇ allTuplesAt {n = suc (suc n)} zero (suc (suc a)) (suc zero) ))

-- The values disjunct: the entry is a pair (numeral 0, z) with
-- z = values X for an arity-one member (1, X) of the previous level.
-- Bound order: z ∷ k₀ ∷ k₁ ∷ X ∷ γ.
ValuesDisjAt : ∀ {n} → Fin n → Fin n → Formula S n
ValuesDisjAt e p = ∃̇ (∃̇ (∃̇ (∃̇ (
    prAtL (sh4 e) (suc zero) zero
  ∧̇ ( (var (suc zero) ≐ con (numeralL 0))
    ∧̇ ( appAt (sh4 p) (suc (suc zero)) (suc (suc (suc zero)))
      ∧̇ ( (var (suc (suc zero)) ≐ con (numeralL 1))
        ∧̇ valuesAt zero (suc (suc (suc zero))) ) ))))))

module _ {n : ℕ} (e p : Fin n) (γ : S ^ n) where
  ValuesDisj-out : ⟨ γ ⊨ ValuesDisjAt e p ⟩
                 → ∥ Σ[ X ∈ S ] Σ[ z ∈ S ]
                     ( (fst (lookup e γ) ≡ pr (fst (numeralL 0)) (fst z))
                     × ⟨ pr (fst (numeralL 1)) (fst X) ∈ fst (lookup p γ) ⟩
                     × (fst z ≡ values (fst X)) ) ∥₁
  ValuesDisj-out =
    PT.rec PT.squash₁ (λ { (X , w₁) →
    PT.rec PT.squash₁ (λ { (k₁ , w₂) →
    PT.rec PT.squash₁ (λ { (k₀ , w₃) →
    PT.rec PT.squash₁ (λ { (z , body) → finish X k₁ k₀ z body }) w₃ }) w₂ }) w₁ })
    where
    finish : (X k₁ k₀ z : S)
           → ⟨ (z ∷ k₀ ∷ k₁ ∷ X ∷ γ) ⊨
                ( prAtL (sh4 e) (suc zero) zero
                ∧̇ ( (var (suc zero) ≐ con (numeralL 0))
                  ∧̇ ( appAt (sh4 p) (suc (suc zero)) (suc (suc (suc zero)))
                    ∧̇ ( (var (suc (suc zero)) ≐ con (numeralL 1))
                      ∧̇ valuesAt zero (suc (suc (suc zero))) ) ) ) ) ⟩
           → ∥ Σ[ X ∈ S ] Σ[ z ∈ S ]
               ( (fst (lookup e γ) ≡ pr (fst (numeralL 0)) (fst z))
               × ⟨ pr (fst (numeralL 1)) (fst X) ∈ fst (lookup p γ) ⟩
               × (fst z ≡ values (fst X)) ) ∥₁
    finish X k₁ k₀ z (h1 , (h2 , (h3 , (h4 , h5)))) =
      let ek₀ : fst k₀ ≡ fst (numeralL 0)
          ek₀ = h2
          ek₁ : fst k₁ ≡ fst (numeralL 1)
          ek₁ = h4
      in ∣ X , z ,
           ( subst (λ q → fst (lookup e γ) ≡ pr q (fst z)) ek₀
               (subst ⟨_⟩ (prAtL-adequate (sh4 e) (suc zero) zero
                 (z ∷ k₀ ∷ k₁ ∷ X ∷ γ)) h1)
           , ( subst (λ q → ⟨ pr q (fst X) ∈ fst (lookup p γ) ⟩) ek₁
                 (subst ⟨_⟩ (appAt-adequate (sh4 p) (suc (suc zero))
                   (suc (suc (suc zero))) (z ∷ k₀ ∷ k₁ ∷ X ∷ γ)) h3)
             , valuesAt-out zero (suc (suc (suc zero)))
                 (z ∷ k₀ ∷ k₁ ∷ X ∷ γ) h5 ) ) ∣₁

-- The disjunctive layer formula over the next-level slot b, the
-- previous-level slot p, and the carrier slot a: every member of b is
-- a member of p or one of the three op-images.
LayerAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
LayerAt b p a = ∀̇ ( (var zero ∈̇ var (suc b)) ⇒̇
  ( (var zero ∈̇ var (suc p))
  ∨̇ ( InterDisjAt zero (suc p) )
  ∨̇ ( AllTuplesDisjAt zero (suc a) )
  ∨̇ ( ValuesDisjAt zero (suc p) ) ))

-- The layer with the level-table functionality conjunct, as one
-- description of the closure step's next level.
LayerDesc : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
LayerDesc b p a = LayerAt b p a ∧̇ FunAt b

-- The layer's out-reader for the intersection disjunct: unpack the
-- ∀-binder, the disjunction, and the four existential binders, and
-- land on the intersection shape via the delivered interAt.
module _ {n : ℕ} (b p a : Fin n) (γ : S ^ n) where
  -- The layer's out-reader for the intersection disjunct: the entry
  -- x is in the next level via the inter branch, so it is a pair
  -- (k, z) with z = X ∩ Y for same-arity members of the previous
  -- level.  This is InterDisj-out at the ∀-binder's member.
  Layer-inter-out : (x : S) → ⟨ (x ∷ γ) ⊨ InterDisjAt zero (suc p) ⟩
                  → ∥ Σ[ k ∈ S ] Σ[ z ∈ S ] Σ[ X ∈ S ] Σ[ Y ∈ S ]
                      ( (fst x ≡ pr (fst k) (fst z))
                      × ⟨ pr (fst k) (fst X) ∈ fst (lookup p γ) ⟩
                      × ⟨ pr (fst k) (fst Y) ∈ fst (lookup p γ) ⟩
                      × (fst z ≡ fst X ∩ fst Y) ) ∥₁
  Layer-inter-out x h = InterDisj-out zero (suc p) (x ∷ γ) h
