{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.32] Ladder point 5: the walling clause with FIVE constants in
-- bounded tag positions (8, 11, 1, 0, 1 -- the real clause's worst-case
-- count is exInClauseAt at 5).  Same matrix as ProbeDD25D, delivered
-- readers, same placement witness.  The count is asserted BEFORE the
-- placement witness.  Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ132C5 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; Σ₁; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
        ; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters
  using ( countFo; constantsFo; absFo; placeFo; padLeft )
open import FOL.Manipulation.Relabelling using ( embed; mapΔ₀ )
import Cubical.Data.Empty as Empty
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; Δ₀-sucAt )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; appAt; appAt-adequate
        ; consAtL; consAtL-adequate; sucAtL
        ; subValSuccAt; subValSuccAt-adequate
        ; tagAtL; tagAtL-adequate; arityTagAtL; arityTagAtL-adequate
        ; envSetAt; extAt; extAt-out; extAt-in
        ; body∃; body∃-in; body∃-out; QuantWit
        ; prʟ; prʟ-fst )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import Cubical.Data.Vec using ( Vec; _++_; map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

placeΔ₀ : ∀ {ℓz ℓc} {K : Type ℓc} {n k} {φ : Formula K n}
        → Δ₀ φ → (θ : Fin (countFo φ) → Fin (n + k))
        → Δ₀ (placeFo {ℓz = ℓz} φ θ)
placeΔ₀ δ-∈ θ = δ-∈
placeΔ₀ δ-≐ θ = δ-≐
placeΔ₀ (δ-∧ c d) θ = δ-∧ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-∨ c d) θ = δ-∨ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-⇒ c d) θ = δ-⇒ (placeΔ₀ c _) (placeΔ₀ d _)
placeΔ₀ (δ-¬ c)   θ = δ-¬ (placeΔ₀ c θ)
placeΔ₀ δ-⊤ θ = δ-⊤
placeΔ₀ δ-⊥ θ = δ-⊥
placeΔ₀ (δ-∀∈ c) θ = δ-∀∈ (placeΔ₀ c _)
placeΔ₀ (δ-∃∈ c) θ = δ-∃∈ (placeΔ₀ c _)

absΔ₀ : ∀ {ℓz ℓc} {K : Type ℓc} {n} {φ : Formula K n}
      → Δ₀ φ → Δ₀ (absFo {ℓz = ℓz} φ)
absΔ₀ {n = n} d = placeΔ₀ d (padLeft n)

-- The [LJ-1.27-R] walling matrix, with the numeral slot N : Fin (5 + n)
-- standing where `con (numeralL 8)` used to sit.  Count is 0.
module Clause {n : ℕ} (C T B : Fin n) where
  private
    K : Fin (suc n)
    K = zero

    C₁ T₁ B₁ : Fin (suc n)
    C₁ = suc C
    T₁ = suc T
    B₁ = suc B

  envBnd : Formula S (8 + n)
  envBnd =
    (∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
       (∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
         (∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
           (appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
           ⇒̇ (appAt (suc (suc (suc zero))) (suc (suc zero)) zero
             ⇒̇ (var (suc zero) ≐ var zero))))))
    ∧̇ (∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
         (((∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
             (appAt (suc (suc zero)) (suc zero) zero))
         ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc (suc zero))))))))
        ∧̇ ((var zero ∈̇ var (suc (suc (suc (suc (suc (suc zero)))))))
         ⇒̇ (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
             (appAt (suc (suc zero)) (suc zero) zero)))))
    ∧̇ (∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
         (∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
           (appAt (suc (suc zero)) (suc zero) zero
           ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc (suc (suc (suc (suc B₁)))))))))))))
    ∧̇ (∀̇∈ (var zero)
         (∃̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
           (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc B₁))))))))))
             (prAtL (suc (suc zero)) (suc zero) zero))))

  subValBnd : Formula S (9 + n)
  subValBnd =
    sucAtL (suc (suc (suc (suc (suc (suc zero)))))) (suc zero)
    ∧̇ prAtL zero (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero)))
    ∧̇ appAt (suc (suc (suc (suc (suc (suc (suc (suc T₁))))))))
            zero (suc (suc (suc zero)))

  bodyBnd : Formula S (8 + n)
  bodyBnd =
    (var zero ∈̇ var (suc zero))
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc B₁))))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
          (consAtL zero (suc zero) (suc (suc zero))
          ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ))

  shapeBnd : Formula S (5 + n)
  shapeBnd =
    ∃̇∈ (var (suc (suc (suc (suc zero)))))
      (prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero
      ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
          ((var zero ≐ con (numeralL 8))
          ∧̇ ((var (suc zero) ≐ con (numeralL 11))
          ∧̇ ((var (suc (suc zero)) ≐ con (numeralL 1))
          ∧̇ ((var (suc (suc (suc zero))) ≐ con (numeralL 0))
          ∧̇ ((var (suc (suc (suc (suc zero)))) ≐ con (numeralL 1))
          ∧̇ prAtL (suc zero) zero (suc (suc (suc zero)))))))))

  subValHyp : Formula S (7 + n)
  subValHyp =
    ∃̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
      (sucAtL (suc (suc (suc (suc (suc zero))))) zero
      ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
          subValBnd)

  envHyp : Formula S (7 + n)
  envHyp = ∀̇∈ (var zero) envBnd

  existBndAt : Formula S (suc n)
  existBndAt =
    ∀̇∈ (var C₁) (∀̇∈ (var (suc zero)) (∀̇∈ (var (suc (suc zero)))
      (∀̇∈ (var (suc (suc (suc zero))))
        (shapeBnd ⇒̇ (appAt (suc (suc (suc (suc T₁))))
                            (suc (suc (suc zero))) zero
        ⇒̇ (∀̇∈ (var (suc (suc (suc (suc zero)))))
            (∀̇∈ (var (suc (suc (suc (suc (suc zero))))))
              (subValHyp ⇒̇ (envHyp ⇒̇ (∀̇∈ (var (suc (suc zero))) bodyBnd))))))))))

  Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
  Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

  Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
  Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)

  Δ₀-appAt : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
  Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

  Δ₀-consAtL : ∀ {m} (e' m' e : Fin m) → Δ₀ (consAtL e' m' e)
  Δ₀-consAtL e' m' e = Δ₀-liftFo _ (Δ₀-consAt e' m' e)

  Δ₀-envBnd : Δ₀ envBnd
  Δ₀-envBnd =
    δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc (suc zero)))
                                            (suc (suc zero)) (suc zero))
                               (δ-⇒ (Δ₀-appAt (suc (suc (suc zero)))
                                              (suc (suc zero)) zero)
                                    δ-≐)))))
        (δ-∧ (δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt (suc (suc zero)) (suc zero) zero))
                              δ-∈)
                        (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt (suc (suc zero)) (suc zero) zero)))))
             (δ-∧ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc zero)) (suc zero) zero) δ-∈)))
                  (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero))))))

  Δ₀-subValBnd : Δ₀ subValBnd
  Δ₀-subValBnd =
    δ-∧ (Δ₀-sucAtL (suc (suc (suc (suc (suc (suc zero)))))) (suc zero))
        (δ-∧ (Δ₀-prAtL zero (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))))
             (Δ₀-appAt (suc (suc (suc (suc (suc (suc (suc (suc T₁))))))))
                       zero (suc (suc (suc zero)))))

  Δ₀-bodyBnd : Δ₀ bodyBnd
  Δ₀-bodyBnd =
    δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-consAtL zero (suc zero) (suc (suc zero)))
                              δ-∈)))

  Δ₀-shapeBnd : Δ₀ shapeBnd
  Δ₀-shapeBnd =
    δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero)
              (δ-∃∈ (δ-∧ δ-≐ (δ-∧ δ-≐ (δ-∧ δ-≐ (δ-∧ δ-≐ (δ-∧ δ-≐
                (Δ₀-prAtL (suc zero) zero (suc (suc (suc zero)))))))))))

  Δ₀-subValHyp : Δ₀ subValHyp
  Δ₀-subValHyp =
    δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc (suc (suc (suc (suc zero))))) zero)
              (δ-∃∈ Δ₀-subValBnd))

  Δ₀-envHyp : Δ₀ envHyp
  Δ₀-envHyp = δ-∀∈ Δ₀-envBnd

  Δ₀-existBndAt : Δ₀ existBndAt
  Δ₀-existBndAt =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ Δ₀-shapeBnd
      (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc T₁)))) (suc (suc (suc zero))) zero)
        (δ-∀∈ (δ-∀∈ (δ-⇒ Δ₀-subValHyp (δ-⇒ Δ₀-envHyp (δ-∀∈ Δ₀-bodyBnd))))))))))

-- The count, asserted BEFORE the placement witness.
_ : countFo (Clause.existBndAt {1} zero zero zero) ≡ 5
_ = refl

-- The placement witness at count 5: the measurement target.
module ClauseDecode {n : ℕ} (C T B : Fin n) (γ : S ^ suc n) where
  nφ : ℕ
  nφ = countFo (Clause.existBndAt {n} C T B)

  σL : Formula S (suc n + nφ)
  σL = embed (absFo {ℓz = ℓ} {ℓc = ℓ-suc ℓ} {K = S} (Clause.existBndAt {n} C T B))

  Δ₀-σL : Δ₀ σL
  Δ₀-σL = mapΔ₀ Empty.rec* (absΔ₀ (Clause.Δ₀-existBndAt {n} C T B))
