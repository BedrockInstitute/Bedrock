{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.336] probe.  THE DIRTY SEVEN `Agree` MODULES, PORTED GENERIC IN
-- THE CLASS, WAVE 2 OF `q'`.
--
-- The scaffold is wave 1's, unchanged in shape: the eight parameters are
-- `GenModel`'s, and the codings come from `GenModel` applied at them.
-- Wave 1's port arrives as ONE module application, so the 113 blocks of
-- the seven's closure that wave 1 already ported are not copied twice.
--
-- Above the marker sit the eight committed gap names the seven reach and
-- `GenModel` does not deliver, re-stated VERBATIM from `src/L/Coding/`:
-- `keyArityAtL` and `hasWitnessAt` from `CodeSet`, `twelveAt` and
-- `satGraphAt` from `Graph`, `envOneAt`, `DefinesAt`, `isCodeAt` and
-- `DefBody` from `Powerset`.  Every one is syntax over `GenModel`
-- primitives, so each ports unchanged.  `shapedAt`, the ninth, arrives
-- from wave 1.  `satGraphAt` keeps its `opaque` seal, because
-- `SatGraphAgree` is the one site in the tree that unfolds it.
--
-- Below the marker, every block is copied VERBATIM from
-- `src/L/Condensation.lagda.md` at the line range the trailing manifest
-- records, in chapter order.  The diff against the original spans is the
-- task's number.
--
-- ONE agda process under GHCRTS="-A64m -I0 -M8g".

open import Base.Prelude
open import Base.Truth

open import FOL.ZFStructure using ( module hPropStructure; Transitive; _↾_ )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy using ( 𝒮ᵥ )
open import V.Coding using ( pr )
open import V.Model using ( pair-singleton )
open import L.Coding.Base using ( Δ₀-prAt )
open import L.Coding.Environment using ( Δ₀-consAt; Δ₀-sucAt )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ )
open InfinitySet using ( #_; sucV )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁; ∥_∥₁ )

import LJ-1-306.GenAgree

module LJ-1-336.ControlA {ℓ : Level}
  (M : V ℓ → hProp (ℓ-suc ℓ))
  (M-trans : Transitive (𝒮ᵥ {ℓ}) M)
  (numeralL : ℕ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (numeralL-fst : (k : ℕ) → fst (numeralL k) ≡ # k)
  (pairʟ : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (pairʟ-fst : (a b : Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
             → fst (pairʟ a b) ≡ ⁅ fst a , fst b ⁆)
  (sucʟ : Σ[ x ∈ V ℓ ] ⟨ M x ⟩ → Σ[ x ∈ V ℓ ] ⟨ M x ⟩)
  (sucʟ-fst : (a : Σ[ x ∈ V ℓ ] ⟨ M x ⟩) → fst (sucʟ a) ≡ sucV (fst a))
  where

module W1 = LJ-1-306.GenAgree {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open W1
open W1.GM
open W1.GM.ToL using ( Δ₀-liftFo )
open W1.KFactsNS
open W1.KFactsNS.KFacts

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M) using ( S )
open W1.GM.AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE COMMITTED GAP NAMES, RE-STATED.  Verbatim from `src/L/Coding/`,
-- one nested module per source module, so each source module's own
-- private helpers stay private here too.
-- =====================================================================

-- src/L/Coding/CodeSet.lagda.md:135-136 and :240-242
module CodeSetGap where

  keyArityAtL : ∀ {n} → Fin n → ℕ → Formula S n
  keyArityAtL c k = ∃̇ (tagAtL (suc c) k zero)

  hasWitnessAt : ∀ {n} → Fin n → Fin n → Formula S n
  hasWitnessAt A x = ∃̇ ((var (suc x) ∈̇ var zero)
                        ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A)))

open CodeSetGap public

-- src/L/Coding/Graph.lagda.md:85-92, :94-105, :186-192 and :203-205
module GraphGap where

  private
    Ci Ti Bi : ∀ {n} → Fin (suc (suc (suc n)))
    Ci = suc (suc zero)
    Ti = suc zero
    Bi = zero

    sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
    sh3 i = suc (suc (suc i))

  twelveAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  twelveAt C T B =
    memClauseAt C T B ∧̇ (eqClauseAt C T B
    ∧̇ (andClauseAt C T ∧̇ (orClauseAt C T
    ∧̇ (impClauseAt C T B ∧̇ (negClauseAt C T B
    ∧̇ (topClauseAt C T B ∧̇ (botClauseAt C T
    ∧̇ (existClauseAt C T B ∧̇ (forallClauseAt C T B
    ∧̇ (allInClauseAt C T B ∧̇ exInClauseAt C T B))))))))))

  private
    satGraphOn : ∀ {n} → Formula S (suc (suc (suc n)))
               → Fin n → Fin n → Formula S n
    satGraphOn pin x y =
      ∃̇ (∃̇ (∃̇ ( pin
              ∧̇ ( closedAt Ci
              ∧̇ ( domAt Ti Ci
              ∧̇ ( appAt Ti (sh3 x) (sh3 y)
              ∧̇ twelveAt Ci Ti Bi ))))))

  opaque
    satGraphAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    satGraphAt B x y = satGraphOn (var Bi ≐ var (sh3 B)) x y

open GraphGap public

-- src/L/Coding/Powerset.lagda.md:128-129, :217-220, :297-298, :431-440
module PowersetGap where

  envOneAt : ∀ {n} → Fin n → Fin n → Formula S n
  envOneAt e y = extAt e (tagAtL zero 0 (suc y))

  DefinesAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  DefinesAt x w v = extAt x ( (var zero ∈̇ var (suc w))
                            ∧̇ ∃̇ ( envOneAt zero (suc zero)
                                 ∧̇ (var zero ∈̇ var (suc (suc v))) ) )

  isCodeAt : ∀ {n} → Fin n → Fin n → Formula S n
  isCodeAt c w = keyArityAtL c 1 ∧̇ hasWitnessAt w c

  private
    sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
    sh3 i = suc (suc (suc i))

  DefBody : ∀ {n} → Fin n → Formula S (suc (suc (suc n)))
  DefBody w = isCodeAt (suc zero) (sh3 w)
              ∧̇ ( satGraphAt (sh3 w) (suc zero) zero
                ∧̇ DefinesAt (suc (suc zero)) (sh3 w) zero )

open PowersetGap public

-- =====================================================================
-- BELOW THIS LINE: VERBATIM FROM `src/L/Condensation.lagda.md`, in
-- chapter order.  The manifest at the file's end records each block's
-- source range.
-- =====================================================================


keyArBS : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
keyArBS c tag K =
  ∃̇∈ (var K) (∃̇∈ (var (suc K))
  ((var zero ≐ var (suc (suc tag)))
  ∧̇ prAtL (suc (suc c)) zero (suc zero)))


Δ₀-arTagPairBS : ∀ {m} (tag K : Fin m) → Δ₀ (arTagPairBS tag K)
Δ₀-arTagPairBS tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero)
            (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero)
                                       (Δ₀-prAtL zero (suc (suc (suc (suc zero))))
                                                 (suc (suc (suc zero)))))))))


Δ₀-arTagBS : ∀ {m} (tag K : Fin m) → Δ₀ (arTagBS tag K)
Δ₀-arTagBS tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc zero))) (suc (suc zero)) zero)
            (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero (suc (suc zero))))))


Δ₀-binShapeBS : ∀ {m} (C tag K : Fin m) (rel : Formula S (4 + m))
              → Δ₀ rel → Δ₀ (binShapeBS C tag K rel)
Δ₀-binShapeBS C tag K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagPairBS tag K) drel))))


Δ₀-unShapeBS : ∀ {m} (C tag K : Fin m) (rel : Formula S (3 + m))
             → Δ₀ rel → Δ₀ (unShapeBS C tag K rel)
Δ₀-unShapeBS C tag K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagBS tag K) drel)))


Δ₀-bothSameB : ∀ {m} (C : Fin m) → Δ₀ (bothSameB C)
Δ₀-bothSameB C =
  δ-∧ (Δ₀-appAt (suc (suc (suc (suc C)))) (suc (suc zero)) (suc zero))
      (Δ₀-appAt (suc (suc (suc (suc C)))) (suc (suc zero)) zero)


Δ₀-oneSameB : ∀ {m} (C : Fin m) → Δ₀ (oneSameB C)
Δ₀-oneSameB C = Δ₀-appAt (suc (suc (suc C))) (suc zero) zero


Δ₀-oneSuccB : ∀ {m} (C K : Fin m) → Δ₀ (oneSuccB C K)
Δ₀-oneSuccB C K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc (suc zero)) zero)
            (Δ₀-appAt (suc (suc (suc (suc C)))) zero (suc zero)))


Δ₀-succSndB : ∀ {m} (C K : Fin m) → Δ₀ (succSndB C K)
Δ₀-succSndB C K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc (suc (suc zero))) zero)
            (Δ₀-appAt (suc (suc (suc (suc (suc C))))) zero (suc zero)))


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


isCodeBS : ∀ {m} → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula S m
isCodeBS c w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  keyArBS c N1 K ∧̇ hasWitnessBS w c K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11


Δ₀-domB : ∀ {m} (f d K : Fin m) → Δ₀ (domB f d K)
Δ₀-domB f d K =
  δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt (suc (suc f)) (suc zero) zero)) δ-∈)
            (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt (suc (suc f)) (suc zero) zero))))


envOneBndS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (2 + m)
envOneBndS v K N0 =
  extAtB zero (suc (suc K))
  (tagBS zero (suc (suc (suc N0))) (suc (suc zero)) (suc (suc (suc K))))


DefinesBS : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
DefinesBS x w v K N0 =
  extAtB x K
  ((var zero ∈̇ var (suc w))
  ∧̇ ∃̇∈ (var (suc K)) (envOneBndS v K N0
        ∧̇ (var zero ∈̇ var (suc (suc v)))))


module SatGraphB {n : ℕ} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where
  private
    K' : Fin (11 + n)
    K' = (suc (suc (suc (suc (suc (suc K))))))

  twelveB : Formula S (11 + n)
  twelveB =
    Mem.memBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N0)))))) K'
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ (Eq.eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N1)))))) K'
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ (And.andBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N2)))))) K'
    ∧̇ (Or.orBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N3)))))) K'
    ∧̇ (Imp.impBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N4)))))) K'
    ∧̇ (Neg.negBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N5)))))) K'
    ∧̇ (Top.topBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N6)))))) K'
    ∧̇ (Bot.botBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N7)))))) K'
    ∧̇ (Exist.existBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N8)))))) K'
    ∧̇ (Forall.forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N9)))))) K'
    ∧̇ (AllIn.allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N10)))))) K'
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1))))))
    ∧̇ (ExIn.exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero (suc (suc (suc (suc (suc (suc N11)))))) K'
      (suc (suc (suc (suc (suc (suc t0))))))
      (suc (suc (suc (suc (suc (suc t1)))))))))))))))))

  Δ₀-twelveB : Δ₀ twelveB
  Δ₀-twelveB =
    δ-∧ (Mem.Δ₀-memBndAt {11 + n} (suc (suc zero)) (suc zero) zero
           (suc (suc (suc (suc (suc (suc N0)))))) K'
           (suc (suc (suc (suc (suc (suc t0))))))
           (suc (suc (suc (suc (suc (suc t1)))))))
        (δ-∧ (Eq.Δ₀-eqBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N1)))))) K'
               (suc (suc (suc (suc (suc (suc t0))))))
               (suc (suc (suc (suc (suc (suc t1)))))))
        (δ-∧ (And.Δ₀-andBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N2)))))) K')
        (δ-∧ (Or.Δ₀-orBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N3)))))) K')
        (δ-∧ (Imp.Δ₀-impBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N4)))))) K')
        (δ-∧ (Neg.Δ₀-negBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N5)))))) K')
        (δ-∧ (Top.Δ₀-topBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N6)))))) K')
        (δ-∧ (Bot.Δ₀-botBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N7)))))) K')
        (δ-∧ (Exist.Δ₀-existBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N8)))))) K')
        (δ-∧ (Forall.Δ₀-forallBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N9)))))) K')
        (δ-∧ (AllIn.Δ₀-allInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N10)))))) K'
               (suc (suc (suc (suc (suc (suc t0))))))
               (suc (suc (suc (suc (suc (suc t1)))))))
             (ExIn.Δ₀-exInBndAt {11 + n} (suc (suc zero)) (suc zero) zero
               (suc (suc (suc (suc (suc (suc N11)))))) K'
               (suc (suc (suc (suc (suc (suc t0))))))
               (suc (suc (suc (suc (suc (suc t1)))))))))))))))))

  satGraphB : Formula S (suc (suc (suc (5 + n))))
  satGraphB =
    ∃̇∈ (var (suc (suc (suc K))))
      (∃̇∈ (var (suc (suc (suc (suc K)))))
        (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
          ((var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
          ∧̇ (closedBS (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
                (suc (suc (suc (suc (suc (suc N2))))))
                (suc (suc (suc (suc (suc (suc N3))))))
                (suc (suc (suc (suc (suc (suc N4))))))
                (suc (suc (suc (suc (suc (suc N5))))))
                (suc (suc (suc (suc (suc (suc N8))))))
                (suc (suc (suc (suc (suc (suc N9))))))
                (suc (suc (suc (suc (suc (suc N10))))))
                (suc (suc (suc (suc (suc (suc N11))))))
          ∧̇ (domB (suc zero) (suc (suc zero))
                   (suc (suc (suc (suc (suc (suc K))))))
          ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero)))
          ∧̇ twelveB))))))

  Δ₀-satGraphB : Δ₀ satGraphB
  Δ₀-satGraphB =
    δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐
      (δ-∧ (Δ₀-closedBS (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
               (suc (suc (suc (suc (suc (suc N2))))))
               (suc (suc (suc (suc (suc (suc N3))))))
               (suc (suc (suc (suc (suc (suc N4))))))
               (suc (suc (suc (suc (suc (suc N5))))))
               (suc (suc (suc (suc (suc (suc N8))))))
               (suc (suc (suc (suc (suc (suc N9))))))
               (suc (suc (suc (suc (suc (suc N10))))))
               (suc (suc (suc (suc (suc (suc N11)))))))
      (δ-∧ (Δ₀-domB (suc zero) (suc (suc zero))
                    (suc (suc (suc (suc (suc (suc K)))))))
      (δ-∧ (Δ₀-appAt (suc zero) (suc (suc (suc (suc zero))))
                     (suc (suc (suc zero))))
           Δ₀-twelveB))))))


DefBodyB : ∀ {n} → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Formula S (suc (suc (suc (5 + n))))
DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 =
  isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
    (suc (suc (suc N0))) (suc (suc (suc N1)))
    (suc (suc (suc N2))) (suc (suc (suc N3)))
    (suc (suc (suc N4))) (suc (suc (suc N5)))
    (suc (suc (suc N6))) (suc (suc (suc N7)))
    (suc (suc (suc N8))) (suc (suc (suc N9)))
    (suc (suc (suc N10))) (suc (suc (suc N11)))
  ∧̇ (SatGraphB.satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    ∧̇ DefinesBS (suc (suc zero)) (suc (suc (suc w))) zero
         (suc (suc (suc K))) (suc (suc (suc N0))))


module DomainAgree {n : ℕ} (f d K : Fin n) (γ : S ^ n)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (domK : (x : S) → ⟨ fst x ∈ fst (lookup d γ) ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩) where

  mem : (x y : S) → ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
      → ⟨ pr (fst x) (fst y) ∈ fst (lookup f γ) ⟩
  mem x y ap = subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero
                 (y ∷ x ∷ γ)) ap

  out : ⟨ γ ⊨ domAt f d ⟩ → ⟨ γ ⊨ domB f d K ⟩
  out h = λ x xK →
      ( λ hx → h x .snd
          (PT.rec squash₁ (λ { (y , (_ , ap)) → ∣ y , ap ∣₁ }) hx) )
    , ( λ hx → PT.rec squash₁
          (λ { (y , ap) →
            ∣ y , ( entryK x y (mem x y ap) .snd , ap ) ∣₁ })
          (h x .snd hx) )

  back : ⟨ γ ⊨ domB f d K ⟩ → ⟨ γ ⊨ domAt f d ⟩
  back h x =
      ( λ hx → PT.rec (snd (fst x ∈ fst (lookup d γ))) go hx )
    , ( λ m → PT.rec squash₁
          (λ { (y , (yK , p)) → ∣ y , p ∣₁ })
          (h x (domK x m) .snd m) )
    where
    go : Σ[ y ∈ S ] ⟨ (y ∷ x ∷ γ) ⊨ appAt (suc (suc f)) (suc zero) zero ⟩
       → ⟨ fst x ∈ fst (lookup d γ) ⟩
    go (y , ap) = h x (entryK x y (mem x y ap) .fst) .fst
      ∣ y , ( entryK x y (mem x y ap) .snd , ap ) ∣₁


module WitnessAgree {n : ℕ} (A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (f : KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
  (witK : (w : S) → ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
         → ⟨ fst w ∈ fst (lookup K γ) ⟩)
  -- THE WITNESS SET IS IN K, AND THESE THREE SAY SO ([LJ-1.153]).
  -- Without the tie, `w` is any set at all: pick the successor of a
  -- code whose components are the K slot itself, and the conclusion
  -- gives K ∈ K (agents/tasks/LJ-1-153/ProbeLJ1153A.agda:120, :137,
  -- exit 0, and that refutation needs NO hypothesis).  The tie is the
  -- one the sites hold: `witK` returns it in `out`, and the bounded
  -- witness carries it in `back`.  With K transitive it is also what
  -- makes the three TRUE, by [LJ-1.151]'s `prK`.
  (codesK : (w : S) → ⟨ fst w ∈ fst (lookup K γ) ⟩
           → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (unCodesK : (w : S) → ⟨ fst w ∈ fst (lookup K γ) ⟩
             → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (entryK : (w : S) → ⟨ fst w ∈ fst (lookup K γ) ⟩
           → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w ⟩
           → ⟨ fst x' ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ hasWitnessAt A x ⟩
      → ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ w ∈ S ] ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
           ∧̇ (closedAt zero ∧̇ shapedAt zero (suc A))) ⟩
       → ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
    go (w , (hxw , (hcl , hsh))) =
      ∣ w , ( wK , ( hxw , ( CA.out hcl , SA.out hsh ) ) ) ∣₁
      where
      -- The site fact this direction already computed and threw away.
      wK : ⟨ fst w ∈ fst (lookup K γ) ⟩
      wK = witK w (hxw , (hcl , hsh))
      module CA = ClosedAgree {1 + n} zero (suc K)
                    (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N8) (suc N9) (suc N10) (suc N11)
                    (suc A) (suc N0) (suc N1) (suc N6) (suc N7) (w ∷ γ)
                    (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ w f)
                    (codesK w wK) (unCodesK w wK) (entryK w wK)
      module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ w f)
                    (codesK w wK) (unCodesK w wK)

  back : ⟨ γ ⊨ hasWitnessBS A x K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ hasWitnessAt A x ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ w ∈ S ] (⟨ fst w ∈ fst (lookup K γ) ⟩
                    × ⟨ (w ∷ γ) ⊨ ((var (suc x) ∈̇ var zero)
                         ∧̇ (closedBS zero (suc K) (suc N2) (suc N3) (suc N4) (suc N5)
                               (suc N8) (suc N9) (suc N10) (suc N11)
                           ∧̇ shapedBS zero (suc A) (suc K)
                                (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                                (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11))) ⟩)
       → ⟨ γ ⊨ hasWitnessAt A x ⟩
    go (w , (wK , (hxw , (hcl , hsh)))) =
      ∣ w , ( hxw , ( CA.back hcl , SA.back hsh ) ) ∣₁
      where
      -- `wK` was bound by the pattern and unused before [LJ-1.153].
      module CA = ClosedAgree {1 + n} zero (suc K)
                    (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N8) (suc N9) (suc N10) (suc N11)
                    (suc A) (suc N0) (suc N1) (suc N6) (suc N7) (w ∷ γ)
                    (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ w f)
                    (codesK w wK) (unCodesK w wK) (entryK w wK)
      module SA = ShapedAgree {1 + n} zero (suc A) (suc K)
                    (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
                    (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11) (w ∷ γ)
                    (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ w f)
                    (codesK w wK) (unCodesK w wK)


module KeyAgree {n : ℕ} (c tag K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
            → ⟨ fst t ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ keyArityAtL c k ⟩ → ⟨ γ ⊨ keyArBS c tag K ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ t ∈ S ] ⟨ (t ∷ γ) ⊨ tagAtL (suc c) k zero ⟩
       → ⟨ γ ⊨ keyArBS c tag K ⟩
    go (t , ht) = ∣ t , ( keyValK t ht
        , ∣ numeralL k
            , ( numK , ( te' , hp ) ) ∣₁ ) ∣₁
      where
      te' : ⟨ (numeralL k ∷ t ∷ γ) ⊨ var zero ≐ var (suc (suc tag)) ⟩
      te' = sym tagEq
      hp : ⟨ (numeralL k ∷ t ∷ γ) ⊨ prAtL (suc (suc c)) zero (suc zero) ⟩
      hp = subst ⟨_⟩ (sym (prAtL-adequate {suc (suc n)} (suc (suc c)) zero (suc zero)
             (numeralL k ∷ t ∷ γ)))
        (subst (λ u → fst (lookup (suc (suc c)) (numeralL k ∷ t ∷ γ)) ≡ pr u (fst t))
          (sym (numeralL-fst k))
          (subst ⟨_⟩ (tagAtL-adequate (suc c) k zero (t ∷ γ)) ht))

  back : ⟨ γ ⊨ keyArBS c tag K ⟩ → ⟨ γ ⊨ keyArityAtL c k ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ t ∈ S ] (⟨ fst t ∈ fst (lookup K γ) ⟩
                    × ∥ Σ[ ar ∈ S ] (⟨ fst ar ∈ fst (lookup K γ) ⟩
                        × ⟨ (ar ∷ t ∷ γ) ⊨
                             ((var zero ≐ var (suc (suc tag)))
                              ∧̇ prAtL (suc (suc c)) zero (suc zero)) ⟩) ∥₁)
       → ⟨ γ ⊨ keyArityAtL c k ⟩
    go (t , tK , hw) = PT.rec squash₁ go₂ hw
      where
      go₂ : Σ[ ar ∈ S ] (⟨ fst ar ∈ fst (lookup K γ) ⟩
                        × ⟨ (ar ∷ t ∷ γ) ⊨
                             ((var zero ≐ var (suc (suc tag)))
                              ∧̇ prAtL (suc (suc c)) zero (suc zero)) ⟩)
          → ⟨ γ ⊨ keyArityAtL c k ⟩
      go₂ (ar , arK , (ae , ap)) =
        ∣ t , subst ⟨_⟩ (sym (tagAtL-adequate (suc c) k zero (t ∷ γ)))
              (subst (λ w → fst (lookup (suc c) (t ∷ γ)) ≡ pr w (fst (lookup zero (t ∷ γ))))
                (numeralL-fst k)
                (subst (λ u → fst (lookup (suc (suc c)) (ar ∷ t ∷ γ)) ≡ pr u (fst t))
                  (ae ∙ tagEq)
                  (subst ⟨_⟩ (prAtL-adequate {suc (suc n)} (suc (suc c)) zero (suc zero)
                    (ar ∷ t ∷ γ)) ap))) ∣₁


module EnvOneAgree {m : ℕ} (v K N0 : Fin m) (γ : S ^ (2 + m))
  (N0eq : fst (lookup (suc (suc N0)) γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc K)) γ) ⟩)
  (pairK : (z : S) → ⟨ (z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst z ∈ fst (lookup (suc (suc K)) γ) ⟩) where

  φB : Formula S (3 + m)
  φB = tagBS zero (suc (suc (suc N0))) (suc (suc zero)) (suc (suc (suc K)))

  φ : Formula S (3 + m)
  φ = tagAtL zero 0 (suc (suc zero))

  fwd : (z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  fwd z = T.back
    where
    module T = TagAgree {3 + m} zero (suc (suc (suc N0))) (suc (suc zero))
      (suc (suc (suc K))) (z ∷ γ) 0 N0eq numK

  bwd : (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
  bwd z = T.out
    where
    module T = TagAgree {3 + m} zero (suc (suc (suc N0))) (suc (suc zero))
      (suc (suc (suc K))) (z ∷ γ) 0 N0eq numK

  out : ⟨ γ ⊨ envOneAt zero (suc zero) ⟩ → ⟨ γ ⊨ envOneBndS v K N0 ⟩
  out = extAt→extAtB zero (suc (suc K)) φB φ γ fwd bwd

  back : ⟨ γ ⊨ envOneBndS v K N0 ⟩ → ⟨ γ ⊨ envOneAt zero (suc zero) ⟩
  back = extAtB→extAt zero (suc (suc K)) φB φ γ fwd bwd pairK


module DefinesAgree {m : ℕ} (x w v K N0 : Fin m) (γ : S ^ m)
  (N0eq : fst (lookup N0 γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (pairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
          → ⟨ fst w' ∈ fst (lookup K γ) ⟩)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨
             ((var zero ∈̇ var (suc w)) ∧̇
              ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))) ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩) where

  bodyB : Formula S (suc m)
  bodyB = (var zero ∈̇ var (suc w))
          ∧̇ ∃̇∈ (var (suc K)) (envOneBndS v K N0 ∧̇ (var zero ∈̇ var (suc (suc v))))

  bodyM : Formula S (suc m)
  bodyM = (var zero ∈̇ var (suc w))
          ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v))))

  fwd : (z : S) → ⟨ (z ∷ γ) ⊨ bodyB ⟩ → ⟨ (z ∷ γ) ⊨ bodyM ⟩
  fwd z (hz , hx) = hz , PT.rec squash₁ go hx
    where
    go : Σ[ E ∈ S ] (⟨ fst E ∈ fst (lookup K γ) ⟩
                    × ⟨ (E ∷ z ∷ γ) ⊨ envOneBndS v K N0
                         ∧̇ (var zero ∈̇ var (suc (suc v))) ⟩)
       → ⟨ (z ∷ γ) ⊨ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
    go (E , (EK , hE)) = ∣ E , ( eOne , hE .snd ) ∣₁
      where
      eOne : ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
      eOne = EA.back (hE .fst)
        where
        module EA = EnvOneAgree {m} v K N0 (E ∷ z ∷ γ) N0eq numK
          (λ w' hw → pairK E z w' hw)

  bwd : (z : S) → ⟨ (z ∷ γ) ⊨ bodyM ⟩ → ⟨ (z ∷ γ) ⊨ bodyB ⟩
  bwd z (hz , hx) = hz , PT.rec squash₁ go hx
    where
    go : Σ[ E ∈ S ] ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero)
                         ∧̇ (var zero ∈̇ var (suc (suc v))) ⟩
       → ⟨ (z ∷ γ) ⊨ ∃̇∈ (var (suc K))
             (envOneBndS v K N0 ∧̇ (var zero ∈̇ var (suc (suc v)))) ⟩
    go (E , (hE , hv)) = ∣ E , ( envK E z hE , ( eB , hv ) ) ∣₁
      where
      eB : ⟨ (E ∷ z ∷ γ) ⊨ envOneBndS v K N0 ⟩
      eB = EA.out hE
        where
        module EA = EnvOneAgree {m} v K N0 (E ∷ z ∷ γ) N0eq numK
          (λ w' hw → pairK E z w' hw)

  out : ⟨ γ ⊨ DefinesAt x w v ⟩ → ⟨ γ ⊨ DefinesBS x w v K N0 ⟩
  out = extAt→extAtB x K bodyB bodyM γ fwd bwd

  back : ⟨ γ ⊨ DefinesBS x w v K N0 ⟩ → ⟨ γ ⊨ DefinesAt x w v ⟩
  back = extAtB→extAt x K bodyB bodyM γ fwd bwd satK



module SatGraphAgree {n : ℕ} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (f : KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ)
  (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                          N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
  (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩
               → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
  -- THE CODE SET AND THE GRAPH ARE IN K ([LJ-1.153]).  The clause set
  -- is the `d` slot and the graph the `e` slot of the three-deep
  -- environment, and both are the hypothesis's OWN bound variables.
  -- Untied, a refuter picks them: `sucʟ` of a code whose components
  -- are the K slot gives K ∈ K, with NO hypothesis at all
  -- (agents/tasks/LJ-1-153/ProbeLJ1153A.agda:120, :137, :155, exit 0).
  -- `witK` below returns exactly these two memberships, so the tie
  -- costs the sites nothing.
  (codesK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (unCodesK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
               × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (closedEntryK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                  → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
                  → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                    × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
               → (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
               → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                 × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
          → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (witK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
             (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
             ∧̇ (closedAt (suc (suc zero))
               ∧̇ (domAt (suc zero) (suc (suc zero))
                 ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                   ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  lift3 : (x y z : S) → KFacts {11 + n}
            (suc (suc (suc (suc (suc (suc w))))))
            (suc (suc (suc (suc (suc (suc K))))))
            (suc (suc (suc (suc (suc (suc N0))))))
            (suc (suc (suc (suc (suc (suc N1))))))
            (suc (suc (suc (suc (suc (suc N2))))))
            (suc (suc (suc (suc (suc (suc N3))))))
            (suc (suc (suc (suc (suc (suc N4))))))
            (suc (suc (suc (suc (suc (suc N5))))))
            (suc (suc (suc (suc (suc (suc N6))))))
            (suc (suc (suc (suc (suc (suc N7))))))
            (suc (suc (suc (suc (suc (suc N8))))))
            (suc (suc (suc (suc (suc (suc N9))))))
            (suc (suc (suc (suc (suc (suc N10))))))
            (suc (suc (suc (suc (suc (suc N11))))))
            (z ∷ y ∷ x ∷ γ)
  lift3 x y z =
    KFactsCons
      (suc (suc (suc (suc (suc w))))) (suc (suc (suc (suc (suc K)))))
      (suc (suc (suc (suc (suc N0))))) (suc (suc (suc (suc (suc N1)))))
      (suc (suc (suc (suc (suc N2))))) (suc (suc (suc (suc (suc N3)))))
      (suc (suc (suc (suc (suc N4))))) (suc (suc (suc (suc (suc N5)))))
      (suc (suc (suc (suc (suc N6))))) (suc (suc (suc (suc (suc N7)))))
      (suc (suc (suc (suc (suc N8))))) (suc (suc (suc (suc (suc N9)))))
      (suc (suc (suc (suc (suc N10))))) (suc (suc (suc (suc (suc N11))))) (y ∷ x ∷ γ) z
      (KFactsCons
        (suc (suc (suc (suc w)))) (suc (suc (suc (suc K))))
        (suc (suc (suc (suc N0)))) (suc (suc (suc (suc N1))))
        (suc (suc (suc (suc N2)))) (suc (suc (suc (suc N3))))
        (suc (suc (suc (suc N4)))) (suc (suc (suc (suc N5))))
        (suc (suc (suc (suc N6)))) (suc (suc (suc (suc N7))))
        (suc (suc (suc (suc N8)))) (suc (suc (suc (suc N9))))
        (suc (suc (suc (suc N10)))) (suc (suc (suc (suc N11))))
        (x ∷ γ) y
        (KFactsCons
          (suc (suc (suc w))) (suc (suc (suc K)))
          (suc (suc (suc N0))) (suc (suc (suc N1)))
          (suc (suc (suc N2))) (suc (suc (suc N3)))
          (suc (suc (suc N4))) (suc (suc (suc N5)))
          (suc (suc (suc N6))) (suc (suc (suc N7)))
          (suc (suc (suc N8))) (suc (suc (suc N9)))
          (suc (suc (suc N10))) (suc (suc (suc N11))) γ x f))

  body-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedAt (suc (suc zero))
                 ∧̇ (domAt (suc zero) (suc (suc zero))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                     ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
           → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedBS (suc (suc zero))
                     (suc (suc (suc (suc (suc (suc K))))))
                     (suc (suc (suc (suc (suc (suc N2))))))
                     (suc (suc (suc (suc (suc (suc N3))))))
                     (suc (suc (suc (suc (suc (suc N4))))))
                     (suc (suc (suc (suc (suc (suc N5))))))
                     (suc (suc (suc (suc (suc (suc N8))))))
                     (suc (suc (suc (suc (suc (suc N9))))))
                     (suc (suc (suc (suc (suc (suc N10))))))
                     (suc (suc (suc (suc (suc (suc N11))))))
                 ∧̇ (domB (suc zero) (suc (suc zero))
                        (suc (suc (suc (suc (suc (suc K))))))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                              (suc (suc (suc zero)))
                     ∧̇ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                          N6 N7 N8 N9 N10 N11 t0 t1))) ⟩
  body-out d e f h = ( h .fst
                     , ( CA.out (h .snd .fst)
                       , ( DA.out (h .snd .snd .fst)
                         , ( h .snd .snd .snd .fst
                           , twelve-out d e f (h .snd .snd .snd .snd) ) ) ) )
    where
    -- `h` IS `witK`'s premise, at the same environment, so this
    -- direction supplies the two ties from what it already holds.
    ks = witK d e f h
    dK = ks .fst
    eK = ks .snd .fst
    module CA = ClosedAgree {11 + n} (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc N2))))))
                  (suc (suc (suc (suc (suc (suc N3))))))
                  (suc (suc (suc (suc (suc (suc N4))))))
                  (suc (suc (suc (suc (suc (suc N5))))))
                  (suc (suc (suc (suc (suc (suc N8))))))
                  (suc (suc (suc (suc (suc (suc N9))))))
                  (suc (suc (suc (suc (suc (suc N10))))))
                  (suc (suc (suc (suc (suc (suc N11))))))
                  (suc (suc (suc (suc (suc (suc w))))))
                  (suc (suc (suc (suc (suc (suc N0))))))
                  (suc (suc (suc (suc (suc (suc N1))))))
                  (suc (suc (suc (suc (suc (suc N6))))))
                  (suc (suc (suc (suc (suc (suc N7)))))) (f ∷ e ∷ d ∷ γ)
                  (lift3 d e f) (codesK d e f dK) (unCodesK d e f dK)
                  (closedEntryK d e f dK)
    module DA = DomainAgree {11 + n} (suc zero) (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K)))))) (f ∷ e ∷ d ∷ γ)
                  (domEntryK d e f eK) (domK d e f dK)

  -- The two site facts this direction takes as arguments ([LJ-1.153]).
  -- The bounded form gives `witK` nothing to act on, but `back` below
  -- ALREADY BINDS both memberships in its three patterns and threw
  -- them away, so the caller pays nothing.
  body-back : (d e f : S)
            → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
                (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                ∧̇ (closedBS (suc (suc zero))
                      (suc (suc (suc (suc (suc (suc K))))))
                      (suc (suc (suc (suc (suc (suc N2))))))
                      (suc (suc (suc (suc (suc (suc N3))))))
                      (suc (suc (suc (suc (suc (suc N4))))))
                      (suc (suc (suc (suc (suc (suc N5))))))
                      (suc (suc (suc (suc (suc (suc N8))))))
                      (suc (suc (suc (suc (suc (suc N9))))))
                      (suc (suc (suc (suc (suc (suc N10))))))
                      (suc (suc (suc (suc (suc (suc N11))))))
                  ∧̇ (domB (suc zero) (suc (suc zero))
                         (suc (suc (suc (suc (suc (suc K))))))
                    ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                               (suc (suc (suc zero)))
                      ∧̇ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1))) ⟩
            → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
                (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
                ∧̇ (closedAt (suc (suc zero))
                  ∧̇ (domAt (suc zero) (suc (suc zero))
                    ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                               (suc (suc (suc zero)))
                      ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
  body-back d e f dK eK h = ( h .fst
                      , ( CA.back (h .snd .fst)
                        , ( DA.back (h .snd .snd .fst)
                          , ( h .snd .snd .snd .fst
                            , twelve-back d e f (h .snd .snd .snd .snd) ) ) ) )
    where
    module CA = ClosedAgree {11 + n} (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K))))))
                  (suc (suc (suc (suc (suc (suc N2))))))
                  (suc (suc (suc (suc (suc (suc N3))))))
                  (suc (suc (suc (suc (suc (suc N4))))))
                  (suc (suc (suc (suc (suc (suc N5))))))
                  (suc (suc (suc (suc (suc (suc N8))))))
                  (suc (suc (suc (suc (suc (suc N9))))))
                  (suc (suc (suc (suc (suc (suc N10))))))
                  (suc (suc (suc (suc (suc (suc N11))))))
                  (suc (suc (suc (suc (suc (suc w))))))
                  (suc (suc (suc (suc (suc (suc N0))))))
                  (suc (suc (suc (suc (suc (suc N1))))))
                  (suc (suc (suc (suc (suc (suc N6))))))
                  (suc (suc (suc (suc (suc (suc N7)))))) (f ∷ e ∷ d ∷ γ)
                  (lift3 d e f) (codesK d e f dK) (unCodesK d e f dK)
                  (closedEntryK d e f dK)
    module DA = DomainAgree {11 + n} (suc zero) (suc (suc zero))
                  (suc (suc (suc (suc (suc (suc K)))))) (f ∷ e ∷ d ∷ γ)
                  (domEntryK d e f eK) (domK d e f dK)

  sh3 : ∀ {m} → Fin m → Fin (3 + m)
  sh3 i = suc (suc (suc i))

  -- THE ONLY PLACE IN THE TREE THAT OPENS THE SEAL.  These two read the
  -- three existentials of the machine's graph and rebuild them, so they must
  -- see the body.  Every other consumer of `satGraphAt` treats it as an atom
  -- and needs no `unfolding`.
  opaque
    unfolding satGraphAt

    out : ⟨ γ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
        → ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
    out h = PT.rec squash₁
      (λ { (d , hT) → PT.rec squash₁
        (λ { (e , hb) → PT.rec squash₁
          (λ { (f , body) →
            let ks = witK d e f body
            in ∣ d , ( ks .fst
                     , ∣ e , ( ks .snd .fst
                             , ∣ f , ( ks .snd .snd , body-out d e f body ) ∣₁ )
                       ∣₁ ) ∣₁ })
          hb })
        hT })
      h

    back : ⟨ γ ⊨ SatGraphB.satGraphB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
         → ⟨ γ ⊨ satGraphAt (sh3 w) (suc zero) zero ⟩
    back h = PT.rec squash₁
      (λ { (d , (dK , hT)) → PT.rec squash₁
        (λ { (e , (eK , hb)) → PT.rec squash₁
          (λ { (f , (fK , body)) →
            ∣ d , ∣ e , ∣ f , body-back d e f dK eK body ∣₁ ∣₁ ∣₁ })
          hb })
        hT })
      h


module LeafAgree {n : ℕ} (w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  (γ : S ^ (8 + n))
  (f : KFacts {8 + n} (suc (suc (suc w))) (suc (suc (suc K)))
         (suc (suc (suc N0))) (suc (suc (suc N1)))
         (suc (suc (suc N2))) (suc (suc (suc N3)))
         (suc (suc (suc N4))) (suc (suc (suc N5)))
         (suc (suc (suc N6))) (suc (suc (suc N7)))
         (suc (suc (suc N8))) (suc (suc (suc N9)))
         (suc (suc (suc N10))) (suc (suc (suc N11))) γ)
  (witK : (w' : S) → ⟨ (w' ∷ γ) ⊨ ((var (suc (suc zero)) ∈̇ var zero)
               ∧̇ (closedAt zero ∧̇ shapedAt zero (suc (suc (suc (suc w)))))) ⟩
         → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  -- THE SAME TIE, PASSED THROUGH ([LJ-1.153]).  LeafAgree proves
  -- nothing here: it hands these to WitnessAgree and SatGraphAgree,
  -- whose repaired telescopes need the containing set in K.
  (wCodesK : (w' : S) → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst w' ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (wUnCodesK : (w' : S) → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              → (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst w' ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (wEntryK : (w' : S) → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst w' ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (twelve-out : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩
              → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                           N6 N7 N8 N9 N10 N11 t0 t1 ⟩)
  (twelve-back : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ SatGraphB.twelveB {n} w K N0 N1 N2 N3 N4 N5
                                            N6 N7 N8 N9 N10 N11 t0 t1 ⟩
               → ⟨ (f ∷ e ∷ d ∷ γ) ⊨ twelveAt (suc (suc zero)) (suc zero) zero ⟩)
  (gCodesK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → (k : ℕ) → (c ar a b : S)
            → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
            → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst b ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (gUnCodesK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              → (k : ℕ) → (c ar a : S)
              → ⟨ fst c ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
              → fst c ≡ pr (fst ar) (pr (# k) (fst a))
              → ⟨ fst ar ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (gEntryK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
            → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
            → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domEntryK : (d e f : S) → ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
              → (x' y : S) → ⟨ pr (fst x') (fst y) ∈ fst (lookup (suc zero) (f ∷ e ∷ d ∷ γ)) ⟩
              → ⟨ fst x' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
                × ⟨ fst y ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (domK : (d e f : S) → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
         → (x : S) → ⟨ fst x ∈ fst (lookup (suc (suc zero)) (f ∷ e ∷ d ∷ γ)) ⟩
         → ⟨ fst x ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (graphWitK : (d e f : S) → ⟨ (f ∷ e ∷ d ∷ γ) ⊨
               (var zero ≐ var (suc (suc (suc (suc (suc (suc w)))))))
               ∧̇ (closedAt (suc (suc zero))
                 ∧̇ (domAt (suc zero) (suc (suc zero))
                   ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                     ∧̇ twelveAt (suc (suc zero)) (suc zero) zero))) ⟩
         → ⟨ fst d ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst e ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           × ⟨ fst f ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (keyValK : (t : S) → ⟨ (t ∷ γ) ⊨ tagAtL (suc (suc zero)) 1 zero ⟩
            → ⟨ fst t ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (envK : (E z : S) → ⟨ (E ∷ z ∷ γ) ⊨ envOneAt zero (suc zero) ⟩
         → ⟨ fst E ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (defPairK : (E z w' : S) → ⟨ (w' ∷ E ∷ z ∷ γ) ⊨ tagAtL zero 0 (suc (suc zero)) ⟩
             → ⟨ fst w' ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (satK : (z : S) → ⟨ (z ∷ γ) ⊨ ((var zero ∈̇ var (suc (suc (suc (suc w)))))
             ∧̇ ∃̇ (envOneAt zero (suc zero) ∧̇ (var zero ∈̇ var (suc (suc zero))))) ⟩
         → ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  module WA = WitnessAgree {8 + n} (suc (suc (suc w))) (suc zero) (suc (suc (suc K)))
                (suc (suc (suc N0))) (suc (suc (suc N1)))
                (suc (suc (suc N2))) (suc (suc (suc N3)))
                (suc (suc (suc N4))) (suc (suc (suc N5)))
                (suc (suc (suc N6))) (suc (suc (suc N7)))
                (suc (suc (suc N8))) (suc (suc (suc N9)))
                (suc (suc (suc N10))) (suc (suc (suc N11))) γ
                f witK wCodesK wUnCodesK wEntryK

  module KA = KeyAgree {8 + n} (suc zero) (suc (suc (suc N1))) (suc (suc (suc K))) γ 1
                (f .tagEq1) (f .numK1) keyValK

  module SG = SatGraphAgree {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 γ
                f twelve-out twelve-back
                gCodesK gUnCodesK gEntryK domEntryK domK graphWitK

  module DA = DefinesAgree {8 + n} (suc (suc zero)) (suc (suc (suc w))) zero
                (suc (suc (suc K))) (suc (suc (suc N0))) γ
                (f .tagEq0) (f .numK0) envK defPairK satK

  ic-out : ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
         → ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
  ic-out (hk , hw) = (KA.out hk , WA.out hw)

  ic-back : ⟨ γ ⊨ isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
               (suc (suc (suc N0))) (suc (suc (suc N1)))
               (suc (suc (suc N2))) (suc (suc (suc N3)))
               (suc (suc (suc N4))) (suc (suc (suc N5)))
               (suc (suc (suc N6))) (suc (suc (suc N7)))
               (suc (suc (suc N8))) (suc (suc (suc N9)))
               (suc (suc (suc N10))) (suc (suc (suc N11))) ⟩
         → ⟨ γ ⊨ isCodeAt (suc zero) (suc (suc (suc w))) ⟩
  ic-back (hk , hw) = (KA.back hk , WA.back hw)

  out : ⟨ γ ⊨ DefBody {5 + n} w ⟩ → ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
  out (hcode , (hgraph , hdef)) =
    ( ic-out hcode
    , ( SG.out hgraph
      , DA.out hdef ) )

  back : ⟨ γ ⊨ DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 ⟩
       → ⟨ γ ⊨ DefBody {5 + n} w ⟩
  back (hcode , (hgraph , hdef)) =
    ( ic-back hcode
    , ( SG.back hgraph
      , DA.back hdef ) )


-- =====================================================================
-- MANIFEST.  Each block, its source range in
-- src/L/Condensation.lagda.md, and its range in this file.
-- =====================================================================
-- keyArBS: :1474-1479  ->  this file :167-172
-- Δ₀-arTagPairBS: :1504-1510  ->  this file :174-180
-- Δ₀-arTagBS: :1521-1525  ->  this file :182-186
-- Δ₀-binShapeBS: :1533-1537  ->  this file :188-192
-- Δ₀-unShapeBS: :1543-1547  ->  this file :194-198
-- Δ₀-bothSameB: :1553-1557  ->  this file :200-204
-- Δ₀-oneSameB: :1561-1563  ->  this file :206-208
-- Δ₀-oneSuccB: :1570-1574  ->  this file :210-214
-- Δ₀-succSndB: :1581-1585  ->  this file :216-220
-- Δ₀-closedBS: :1599-1610  ->  this file :222-233
-- hasWitnessBS: :1712-1723  ->  this file :235-246
-- isCodeBS: :1733-1739  ->  this file :248-254
-- Δ₀-domB: :1754-1758  ->  this file :256-260
-- envOneBndS: :1763-1767  ->  this file :262-266
-- DefinesBS: :1773-1779  ->  this file :268-274
-- SatGraphB: :2230-2332  ->  this file :276-378
-- DefBodyB: :2335-2351  ->  this file :380-396
-- DomainAgree: :6510-6540  ->  this file :398-428
-- WitnessAgree: :6576-6657  ->  this file :430-511
-- KeyAgree: :6699-6747  ->  this file :513-561
-- EnvOneAgree: :6748-6777  ->  this file :563-592
-- DefinesAgree: :6778-6834  ->  this file :594-650
-- SatGraphAgree: :6844-7097  ->  this file :652-905
-- LeafAgree: :7107-7243  ->  this file :907-1043

