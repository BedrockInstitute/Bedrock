{-# OPTIONS --cubical --safe --guardedness #-}

-- DD25 review probe G2: THE CURE.  The constant-carrying chain of the
-- bounded code-set description, restated with the tag numerals as
-- variable slots.  This is the file's own documented house style
-- (src/L/Condensation.lagda.md:1111-1114), which the twelve rows
-- already use through arTagB (:435) and arTagPairB (:450), applied to
-- the four *Bnum leaf helpers that the rows do not use.
--
-- The target: countFo ≡ 0, so Cnt.erase applies with refl, and the
-- Delta-0 certificate survives unchanged.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeDD25G2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊤; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Parameters using ( countFo )
open import Cubical.Data.Nat using ( _+_ )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-sucAt )
open import L.Coding.Model {ℓ} using ( prAtL; appAt; sucAtL )
open import L.Condensation {ℓ} lem using
  ( bothSameB; Δ₀-bothSameB; oneSameB; Δ₀-oneSameB
  ; oneSuccB; Δ₀-oneSuccB; succSndB; Δ₀-succSndB
  ; extAtB; Δ₀-extAtB )
open import L.BoundedSubset {ℓ} lem using ( erase-Δ₀ )

open hPropStructure 𝒮ʟ

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S

-- The three constant-free leaves, restated locally (they are local to
-- L.Condensation).
Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)

Δ₀-appAt : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

-- =====================================================================
-- THE FOUR LEAF HELPERS.  Each is Condensation's *Bnum body with
-- `con (numeralL k)` replaced by `var (shift tag)`.  Nothing else moves.
-- =====================================================================

-- Condensation :1455 keyArBnum.  Constant at binder depth 2.
keyArBS : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
keyArBS c tag K =
  ∃̇∈ (var K) (∃̇∈ (var (suc K))
  ((var zero ≐ var (suc (suc tag)))
  ∧̇ prAtL (suc (suc c)) zero (suc zero)))

Δ₀-keyArBS : ∀ {n} (c tag K : Fin n) → Δ₀ (keyArBS c tag K)
Δ₀-keyArBS c tag K =
  δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc (suc c)) zero (suc zero))))

-- Condensation :1465 tagBnum.  Constant at binder depth 1.
tagBS : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
tagBS s tag x K =
  ∃̇∈ (var K) ((var zero ≐ var (suc tag))
            ∧̇ prAtL (suc s) zero (suc x))

Δ₀-tagBS : ∀ {n} (s tag x K : Fin n) → Δ₀ (tagBS s tag x K)
Δ₀-tagBS s tag x K = δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc s) zero (suc x)))

-- Condensation :1475 arTagPairBnum.  Constant at binder depth 3.
arTagPairBS : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
arTagPairBS tag K =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
  (prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K)))))))
          ((var (suc zero) ≐ var (suc (suc (suc (suc (suc (suc (suc tag))))))))
          ∧̇ prAtL (suc (suc zero)) (suc zero) zero
          ∧̇ prAtL zero (suc (suc (suc (suc zero)))) (suc (suc (suc zero))))))

Δ₀-arTagPairBS : ∀ {m} (tag K : Fin m) → Δ₀ (arTagPairBS tag K)
Δ₀-arTagPairBS tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero)
            (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero)
                                       (Δ₀-prAtL zero (suc (suc (suc (suc zero))))
                                                 (suc (suc (suc zero)))))))))

-- Condensation :1494 arTagBnum.  Constant at binder depth 3.
arTagBS : ∀ {m} → Fin m → Fin m → Formula S (3 + m)
arTagBS tag K =
  ∃̇∈ (var (suc (suc (suc K))))
  (prAtL (suc (suc (suc zero))) (suc (suc zero)) zero
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc K)))))
        (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
          ((var zero ≐ var (suc (suc (suc (suc (suc (suc tag)))))))
          ∧̇ prAtL (suc zero) zero (suc (suc zero)))))

Δ₀-arTagBS : ∀ {m} (tag K : Fin m) → Δ₀ (arTagBS tag K)
Δ₀-arTagBS tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc zero))) (suc (suc zero)) zero)
            (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero (suc (suc zero)))))))

-- =====================================================================
-- THE FRAMES.  Unchanged apart from the tag's type: ℕ becomes Fin m.
-- =====================================================================

binShapeBS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m) → Formula S m
binShapeBS C tag K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
  (∀̇∈ (var (suc (suc (suc K))))
      (arTagPairBS tag K ⇒̇ rel))))

Δ₀-binShapeBS : ∀ {m} (C tag K : Fin m) (rel : Formula S (4 + m))
              → Δ₀ rel → Δ₀ (binShapeBS C tag K rel)
Δ₀-binShapeBS C tag K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagPairBS tag K) drel))))

unShapeBS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (3 + m) → Formula S m
unShapeBS C tag K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
  (arTagBS tag K ⇒̇ rel)))

Δ₀-unShapeBS : ∀ {m} (C tag K : Fin m) (rel : Formula S (3 + m))
             → Δ₀ rel → Δ₀ (unShapeBS C tag K rel)
Δ₀-unShapeBS C tag K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagBS tag K) drel)))

binFormBS : ∀ {m} → Fin m → Fin m → Formula S (4 + m) → Formula S (1 + m)
binFormBS tag K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) (∃̇∈ (var (suc (suc (suc K))))
  (arTagPairBS tag K ∧̇ rel)))

Δ₀-binFormBS : ∀ {m} (tag K : Fin m) (rel : Formula S (4 + m))
             → Δ₀ rel → Δ₀ (binFormBS tag K rel)
Δ₀-binFormBS tag K rel drel =
  δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-arTagPairBS tag K) drel)))

unFormBS : ∀ {m} → Fin m → Fin m → Formula S (3 + m) → Formula S (1 + m)
unFormBS tag K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K)))
  (arTagBS tag K ∧̇ rel))

Δ₀-unFormBS : ∀ {m} (tag K : Fin m) (rel : Formula S (3 + m))
            → Δ₀ rel → Δ₀ (unFormBS tag K rel)
Δ₀-unFormBS tag K rel drel =
  δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-arTagBS tag K) drel))

isTmBS : ∀ {m} → Fin (4 + m) → Fin m → Fin m → Fin m → Formula S (4 + m)
isTmBS t A K N0 =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
  (tagBS (suc t) (suc (suc (suc (suc (suc N0))))) zero
             (suc (suc (suc (suc (suc K)))))
  ∧̇ (var zero ∈̇ var (suc (suc (suc (suc (suc A)))))))

Δ₀-isTmBS : ∀ {m} (t : Fin (4 + m)) (A K N0 : Fin m) → Δ₀ (isTmBS t A K N0)
Δ₀-isTmBS t A K N0 =
  δ-∃∈ (δ-∧ (Δ₀-tagBS (suc t) (suc (suc (suc (suc (suc N0))))) zero
                          (suc (suc (suc (suc (suc K)))))) δ-∈)

bothTmBS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m)
bothTmBS A K N0 = isTmBS (suc zero) A K N0 ∧̇ isTmBS zero A K N0

Δ₀-bothTmBS : ∀ {m} (A K N0 : Fin m) → Δ₀ (bothTmBS A K N0)
Δ₀-bothTmBS A K N0 = δ-∧ (Δ₀-isTmBS (suc zero) A K N0) (Δ₀-isTmBS zero A K N0)

fstTmBS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m)
fstTmBS A K N0 = isTmBS (suc zero) A K N0

Δ₀-fstTmBS : ∀ {m} (A K N0 : Fin m) → Δ₀ (fstTmBS A K N0)
Δ₀-fstTmBS A K N0 = Δ₀-isTmBS (suc zero) A K N0

-- =====================================================================
-- THE TWO BODIES.  closedB uses eight tags; shapesB uses all twelve
-- plus two bare numeral-zero payloads, which become the N0 slot.
-- =====================================================================

closedBS : ∀ {m} → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula S m
closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 =
  binShapeBS C N2 K (bothSameB C)
  ∧̇ (binShapeBS C N3 K (bothSameB C)
  ∧̇ (binShapeBS C N4 K (bothSameB C)
  ∧̇ (unShapeBS C N5 K (oneSameB C)
  ∧̇ (unShapeBS C N8 K (oneSuccB C K)
  ∧̇ (unShapeBS C N9 K (oneSuccB C K)
  ∧̇ (binShapeBS C N10 K (succSndB C K)
  ∧̇ binShapeBS C N11 K (succSndB C K)))))))

Δ₀-closedBS : ∀ {m} (C K N2 N3 N4 N5 N8 N9 N10 N11 : Fin m)
            → Δ₀ (closedBS C K N2 N3 N4 N5 N8 N9 N10 N11)
Δ₀-closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 =
  δ-∧ (Δ₀-binShapeBS C N2 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-binShapeBS C N3 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-binShapeBS C N4 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-unShapeBS C N5 K (oneSameB C) (Δ₀-oneSameB C))
      (δ-∧ (Δ₀-unShapeBS C N8 K (oneSuccB C K) (Δ₀-oneSuccB C K))
      (δ-∧ (Δ₀-unShapeBS C N9 K (oneSuccB C K) (Δ₀-oneSuccB C K))
      (δ-∧ (Δ₀-binShapeBS C N10 K (succSndB C K) (Δ₀-succSndB C K))
           (Δ₀-binShapeBS C N11 K (succSndB C K) (Δ₀-succSndB C K))))))))

shapesBS : ∀ {m} → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula S (1 + m)
shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  binFormBS N0 K (bothTmBS A K N0)
  ∨̇ (binFormBS N1 K (bothTmBS A K N0)
  ∨̇ (binFormBS N2 K ⊤̇
  ∨̇ (binFormBS N3 K ⊤̇
  ∨̇ (binFormBS N4 K ⊤̇
  ∨̇ (unFormBS N5 K ⊤̇
  ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
  ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
  ∨̇ (unFormBS N8 K ⊤̇
  ∨̇ (unFormBS N9 K ⊤̇
  ∨̇ (binFormBS N10 K (fstTmBS A K N0)
  ∨̇ binFormBS N11 K (fstTmBS A K N0)))))))))))

Δ₀-shapesBS : ∀ {m} (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            → Δ₀ (shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)
Δ₀-shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  δ-∨ (Δ₀-binFormBS N0 K (bothTmBS A K N0) (Δ₀-bothTmBS A K N0))
      (δ-∨ (Δ₀-binFormBS N1 K (bothTmBS A K N0) (Δ₀-bothTmBS A K N0))
      (δ-∨ (Δ₀-binFormBS N2 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormBS N3 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormBS N4 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormBS N5 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormBS N6 K (var zero ≐ var (suc (suc (suc N0)))) δ-≐)
      (δ-∨ (Δ₀-unFormBS N7 K (var zero ≐ var (suc (suc (suc N0)))) δ-≐)
      (δ-∨ (Δ₀-unFormBS N8 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormBS N9 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormBS N10 K (fstTmBS A K N0) (Δ₀-fstTmBS A K N0))
           (Δ₀-binFormBS N11 K (fstTmBS A K N0) (Δ₀-fstTmBS A K N0))))))))))))

shapedBS : ∀ {m} → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula S m
shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  ∀̇∈ (var C) (shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)

Δ₀-shapedBS : ∀ {m} (C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            → Δ₀ (shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)
Δ₀-shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  δ-∀∈ (Δ₀-shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)

hasWitnessBS : ∀ {m} → Fin m → Fin m → Fin m
             → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
             → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
             → Formula S m
hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  ∃̇∈ (var K) ((var (suc x) ∈̇ var zero)
            ∧̇ (closedBS zero (suc K) (suc N2) (suc N3) (suc N4) (suc N5)
                        (suc N8) (suc N9) (suc N10) (suc N11)
            ∧̇ shapedBS zero (suc A) (suc K)
                        (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                        (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11)))

Δ₀-hasWitnessBS : ∀ {m} (A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
                → Δ₀ (hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)
Δ₀-hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  δ-∃∈ (δ-∧ δ-∈ (δ-∧ (Δ₀-closedBS zero (suc K) (suc N2) (suc N3) (suc N4)
                                  (suc N5) (suc N8) (suc N9) (suc N10) (suc N11))
                     (Δ₀-shapedBS zero (suc A) (suc K)
                        (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                        (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11))))

isCodeBS : ∀ {m} → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula S m
isCodeBS c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  keyArBS c N1 K ∧̇ hasWitnessBS w c K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11

Δ₀-isCodeBS : ∀ {m} (c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            → Δ₀ (isCodeBS c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)
Δ₀-isCodeBS c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  δ-∧ (Δ₀-keyArBS c N1 K)
      (Δ₀-hasWitnessBS w c K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)

-- Condensation :1705 envOneBnd and :1715 DefinesB.  The tag is the
-- numeral zero, so the N0 slot serves.
envOneBndS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (2 + m)
envOneBndS v K N0 =
  extAtB zero (suc (suc K))
  (tagBS zero (suc (suc (suc N0))) (suc (suc zero)) (suc (suc (suc K))))

Δ₀-envOneBndS : ∀ {m} (v K N0 : Fin m) → Δ₀ (envOneBndS v K N0)
Δ₀-envOneBndS v K N0 =
  Δ₀-extAtB zero (suc (suc K)) _
  (Δ₀-tagBS zero (suc (suc (suc N0))) (suc (suc zero)) (suc (suc (suc K))))

DefinesBS : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
DefinesBS x w v K N0 =
  extAtB x K
  ((var zero ∈̇ var (suc w))
  ∧̇ ∃̇∈ (var (suc K)) (envOneBndS v K N0
        ∧̇ (var zero ∈̇ var (suc (suc v)))))

Δ₀-DefinesBS : ∀ {m} (x w v K N0 : Fin m) → Δ₀ (DefinesBS x w v K N0)
Δ₀-DefinesBS x w v K N0 =
  Δ₀-extAtB x K _
    (δ-∧ δ-∈ (δ-∃∈ (δ-∧ (Δ₀-envOneBndS v K N0) δ-∈)))

-- =====================================================================
-- THE VERDICT.  countFo drops 29 to 0, erase applies with refl, and
-- the Delta-0 certificate rides the erasure.
-- =====================================================================

sample : Formula S 1
sample = isCodeBS zero zero zero zero zero zero zero zero
                  zero zero zero zero zero zero zero

count-is-zero : countFo sample ≡ 0
count-is-zero = refl

erased : Formula (⊥* {ℓ-suc ℓ}) 1
erased = Cnt.erase sample refl

erased-Δ₀ : Δ₀ erased
erased-Δ₀ = erase-Δ₀ sample refl
  (Δ₀-isCodeBS zero zero zero zero zero zero zero zero
               zero zero zero zero zero zero zero)

-- The whole DefBodyB leaf by parts: isCodeB 29, the closedB inside
-- satGraphB 8, DefinesB 4.  41 becomes 0.
leafParts : Formula S 1
leafParts =
  sample
  ∧̇ (closedBS zero zero zero zero zero zero zero zero zero zero
  ∧̇ DefinesBS zero zero zero zero zero)

leaf-count-zero : countFo leafParts ≡ 0
leaf-count-zero = refl

leaf-erased : Formula (⊥* {ℓ-suc ℓ}) 1
leaf-erased = Cnt.erase leafParts refl
