{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.37] PART C: THE BINARY FRAMES AND THE PROPOSITIONAL ROWS.
--
-- The binary frame binds the code in C, the arity and the two payload
-- components and the recorded value in K, then the relation's own
-- binders.  The propositional rows (and, or, imp) share one body shape:
-- two same-arity subvalues and an operation.  Untracked probe; thrown
-- away per D-1.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ137C {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; Δ₀-sucAt )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; sucAtL; consAtL )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)

Δ₀-appAt : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

extAtB : ∀ {n} → Fin n → Fin n → Formula S (suc n) → Formula S n
extAtB y K φ = ∀̇∈ (var y) φ
             ∧̇ ∀̇∈ (var K) (φ ⇒̇ (var zero ∈̇ var (suc y)))

Δ₀-extAtB : ∀ {n} (y K : Fin n) (φ : Formula S (suc n))
          → Δ₀ φ → Δ₀ (extAtB y K φ)
Δ₀-extAtB y K φ d = δ-∧ (δ-∀∈ d) (δ-∀∈ (δ-⇒ d δ-∈))

arTagPairB : ∀ {n} → Fin n → Formula S (6 + n)
arTagPairB tag =
  ∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
    (prAtL (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) zero
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
        ((var zero ≐ var (suc (suc (suc (suc (suc (suc (suc (suc tag)))))))))
        ∧̇ prAtL (suc zero) zero (suc (suc zero))
        ∧̇ prAtL (suc (suc zero)) (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))))

Δ₀-arTagPairB : ∀ {n} (tag : Fin n) → Δ₀ (arTagPairB tag)
Δ₀-arTagPairB tag =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) zero)
            (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-prAtL (suc zero) zero (suc (suc zero)))
                                 (Δ₀-prAtL (suc (suc zero))
                                           (suc (suc (suc (suc zero))))
                                           (suc (suc (suc zero))))))))

subValB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
subValB T ar a y K =
  ∃̇∈ (var K) (prAtL zero (suc ar) (suc a)
            ∧̇ appAt (suc T) zero (suc y))

Δ₀-subValB : ∀ {n} (T ar a y K : Fin n) → Δ₀ (subValB T ar a y K)
Δ₀-subValB T ar a y K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL zero (suc ar) (suc a))
            (Δ₀-appAt (suc T) zero (suc y)))

envBndGen : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
envBndGen e E yc ar K B =
    (∀̇∈ (var K) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
       (appAt (suc (suc (suc E))) (suc (suc zero)) (suc zero)
       ⇒̇ (appAt (suc (suc (suc E))) (suc (suc zero)) zero
         ⇒̇ (var (suc zero) ≐ var zero))))))
    ∧̇ (∀̇∈ (var K)
         (((∃̇∈ (var (suc K)) (appAt (suc (suc E)) (suc (suc e)) (suc zero)))
         ⇒̇ (var zero ∈̇ var (suc yc)))
        ∧̇ ((var zero ∈̇ var (suc yc))
         ⇒̇ (∃̇∈ (var (suc K)) (appAt (suc (suc E)) (suc (suc e)) (suc zero))))))
    ∧̇ (∀̇∈ (var K) (∀̇∈ (var (suc K))
         (appAt (suc (suc E)) (suc zero) zero
         ⇒̇ (var zero ∈̇ var (suc (suc B))))))
    ∧̇ (∀̇∈ (var e)
         (∃̇∈ (var (suc ar)) (∃̇∈ (var (suc (suc B)))
           (prAtL (suc (suc zero)) (suc zero) zero))))

Δ₀-envBndGen : ∀ {n} (e E yc ar K B : Fin n) → Δ₀ (envBndGen e E yc ar K B)
Δ₀-envBndGen e E yc ar K B =
  δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc (suc E)))
                                          (suc (suc zero)) (suc zero))
                             (δ-⇒ (Δ₀-appAt (suc (suc (suc E)))
                                            (suc (suc zero)) zero)
                                  δ-≐)))))
      (δ-∧ (δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt (suc (suc E)) (suc (suc e)) (suc zero)))
                            δ-∈)
                      (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt (suc (suc E)) (suc (suc e)) (suc zero))))))
           (δ-∧ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc E)) (suc zero) zero) δ-∈)))
                (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero))))))

interB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
interB y a b K =
  extAtB y K ((var zero ∈̇ var (suc a)) ∧̇ (var zero ∈̇ var (suc b)))

Δ₀-interB : ∀ {n} (y a b K : Fin n) → Δ₀ (interB y a b K)
Δ₀-interB y a b K = Δ₀-extAtB y K _ (δ-∧ δ-∈ δ-∈)

unionB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
unionB y a b K =
  extAtB y K ((var zero ∈̇ var (suc a)) ∨̇ (var zero ∈̇ var (suc b)))

Δ₀-unionB : ∀ {n} (y a b K : Fin n) → Δ₀ (unionB y a b K)
Δ₀-unionB y a b K = Δ₀-extAtB y K _ (δ-∨ δ-∈ δ-∈)

implB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
implB y e a b K =
  extAtB y K ((var zero ∈̇ var (suc e))
            ∧̇ ((var zero ∈̇ var (suc a)) ⇒̇ (var zero ∈̇ var (suc b))))

Δ₀-implB : ∀ {n} (y e a b K : Fin n) → Δ₀ (implB y e a b K)
Δ₀-implB y e a b K = Δ₀-extAtB y K _ (δ-∧ δ-∈ (δ-⇒ δ-∈ δ-∈))

-- =====================================================================
-- THE BINARY FRAME, FULL.  Binders:
--   c in C, ar in K, a in K, b in K, yc in K; shape; lookup;
--   ya in K, E in K; sub; env; every member e of yc satisfies body.
-- =====================================================================
binFullAt : ∀ {n} → Fin n → Fin n → Formula S (6 + n) → Formula S (8 + n)
          → Formula S (8 + n) → Formula S (9 + n) → Formula S (suc n)
binFullAt C T shape sub env body =
  ∀̇∈ (var (suc C)) (∀̇∈ (var (suc zero)) (∀̇∈ (var (suc (suc zero)))
    (∀̇∈ (var (suc (suc (suc zero)))) (∀̇∈ (var (suc (suc (suc (suc zero)))))
      (shape ⇒̇ (appAt (suc (suc (suc (suc (suc (suc T))))))
                       (suc (suc (suc (suc zero)))) zero
      ⇒̇ (∀̇∈ (var (suc (suc (suc (suc (suc zero))))))
          (∀̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
            (sub ⇒̇ (env ⇒̇ (∀̇∈ (var (suc (suc zero))) body)))))))))))

Δ₀-binFullAt : ∀ {n} (C T : Fin n) (shape : Formula S (6 + n))
             (sub env : Formula S (8 + n)) (body : Formula S (9 + n))
             → Δ₀ shape → Δ₀ sub → Δ₀ env → Δ₀ body
             → Δ₀ (binFullAt C T shape sub env body)
Δ₀-binFullAt C T shape sub env body ds dsub denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds
    (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc (suc (suc T))))))
                    (suc (suc (suc (suc zero)))) zero)
      (δ-∀∈ (δ-∀∈ (δ-⇒ dsub (δ-⇒ denv (δ-∀∈ dbody)))))))))))

-- =====================================================================
-- THE BINARY FRAME, ENVIRONMENT ONLY (no subvalue).  Used by the atom
-- rows.
-- =====================================================================
binEnvAt : ∀ {n} → Fin n → Fin n → Formula S (6 + n) → Formula S (7 + n)
         → Formula S (8 + n) → Formula S (suc n)
binEnvAt C T shape env body =
  ∀̇∈ (var (suc C)) (∀̇∈ (var (suc zero)) (∀̇∈ (var (suc (suc zero)))
    (∀̇∈ (var (suc (suc (suc zero)))) (∀̇∈ (var (suc (suc (suc (suc zero)))))
      (shape ⇒̇ (appAt (suc (suc (suc (suc (suc (suc T))))))
                       (suc (suc (suc (suc zero)))) zero
      ⇒̇ (∀̇∈ (var (suc (suc (suc (suc (suc zero))))))
            (env ⇒̇ (∀̇∈ (var (suc (suc zero))) body)))))))))

Δ₀-binEnvAt : ∀ {n} (C T : Fin n) (shape : Formula S (6 + n))
            (env : Formula S (7 + n)) (body : Formula S (8 + n))
            → Δ₀ shape → Δ₀ env → Δ₀ body
            → Δ₀ (binEnvAt C T shape env body)
Δ₀-binEnvAt C T shape env body ds denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds
    (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc (suc (suc T))))))
                    (suc (suc (suc (suc zero)))) zero)
      (δ-∀∈ (δ-⇒ denv (δ-∀∈ dbody)))))))))

-- =====================================================================
-- THE BINARY ENVIRONMENT HYPOTHESES.
-- =====================================================================
-- With the second value slot ya: at E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ K ∷ γ
-- (8 + n), B at 9 + B.
envHypB2 : ∀ {n} → Fin n → Formula S (8 + n)
envHypB2 {n} B = ∀̇∈ (var zero)
  (envBndGen {9 + n} zero (suc zero) (suc (suc (suc zero)))
    (suc (suc (suc (suc (suc (suc zero))))))
    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))

Δ₀-envHypB2 : ∀ {n} (B : Fin n) → Δ₀ (envHypB2 B)
Δ₀-envHypB2 {n} B = δ-∀∈ (Δ₀-envBndGen {9 + n} zero (suc zero)
  (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero))))))
  (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))

-- Without the second value slot (atom rows): at
--   E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ K ∷ γ  (7 + n), B at 8 + B.
envHypB2T : ∀ {n} → Fin n → Formula S (7 + n)
envHypB2T {n} B = ∀̇∈ (var zero)
  (envBndGen {8 + n} zero (suc zero) (suc (suc zero))
    (suc (suc (suc (suc (suc zero)))))
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))

Δ₀-envHypB2T : ∀ {n} (B : Fin n) → Δ₀ (envHypB2T B)
Δ₀-envHypB2T {n} B = δ-∀∈ (Δ₀-envBndGen {8 + n} zero (suc zero)
  (suc (suc zero)) (suc (suc (suc (suc (suc zero)))))
  (suc (suc (suc (suc (suc (suc (suc zero)))))))
  (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))

-- =====================================================================
-- THE PROPOSITIONAL BODY.  At the full binary body environment
--   e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ K ∷ γ  (9 + n):
-- the second value yb is bound in K, its subvalue is read, and the
-- operation speaks of the recorded value, the first and the second
-- subvalues.
-- =====================================================================
propBodyB : ∀ {n} → Fin n → Formula S (10 + n) → Formula S (9 + n)
propBodyB T op =
  ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    (subValB (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc T))))))))))
             (suc (suc (suc (suc (suc (suc (suc zero)))))))
             (suc (suc (suc (suc (suc zero)))))
             zero
             (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    ⇒̇ op)

Δ₀-propBodyB : ∀ {n} (T : Fin n) (op : Formula S (10 + n))
             → Δ₀ op → Δ₀ (propBodyB T op)
Δ₀-propBodyB T op dop =
  δ-∀∈ (δ-⇒ (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc T))))))))))
                         (suc (suc (suc (suc (suc (suc (suc zero)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         zero
                         (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
            dop)

-- =====================================================================
-- THE PROPOSITIONAL ROWS.
-- =====================================================================
module And {n : ℕ} (C T B N : Fin n) where
  private
    subA : Formula S (8 + n)
    subA = subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc zero)))))))

    opA : Formula S (10 + n)
    opA = interB (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  andBndAt : Formula S (suc n)
  andBndAt = binFullAt C T (arTagPairB N) subA (envHypB2 B) (propBodyB T opA)

  Δ₀-andBndAt : Δ₀ andBndAt
  Δ₀-andBndAt =
    Δ₀-binFullAt C T (arTagPairB N) subA (envHypB2 B) (propBodyB T opA)
      (Δ₀-arTagPairB N)
      (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (Δ₀-envHypB2 B)
      (Δ₀-propBodyB T opA
        (Δ₀-interB (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero)))
                   zero
                   (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

module Or {n : ℕ} (C T B N : Fin n) where
  private
    subO : Formula S (8 + n)
    subO = subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc zero)))))))

    opO : Formula S (10 + n)
    opO = unionB (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  orBndAt : Formula S (suc n)
  orBndAt = binFullAt C T (arTagPairB N) subO (envHypB2 B) (propBodyB T opO)

  Δ₀-orBndAt : Δ₀ orBndAt
  Δ₀-orBndAt =
    Δ₀-binFullAt C T (arTagPairB N) subO (envHypB2 B) (propBodyB T opO)
      (Δ₀-arTagPairB N)
      (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (Δ₀-envHypB2 B)
      (Δ₀-propBodyB T opO
        (Δ₀-unionB (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero)))
                   zero
                   (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

module Imp {n : ℕ} (C T B N : Fin n) where
  private
    subI : Formula S (8 + n)
    subI = subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc zero)))))))

    opI : Formula S (10 + n)
    opI = implB (suc (suc (suc (suc zero))))
                (suc (suc zero))
                (suc (suc (suc zero)))
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

  impBndAt : Formula S (suc n)
  impBndAt = binFullAt C T (arTagPairB N) subI (envHypB2 B) (propBodyB T opI)

  Δ₀-impBndAt : Δ₀ impBndAt
  Δ₀-impBndAt =
    Δ₀-binFullAt C T (arTagPairB N) subI (envHypB2 B) (propBodyB T opI)
      (Δ₀-arTagPairB N)
      (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (Δ₀-envHypB2 B)
      (Δ₀-propBodyB T opI
        (Δ₀-implB (suc (suc (suc (suc zero))))
                  (suc (suc zero))
                  (suc (suc (suc zero)))
                  zero
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
