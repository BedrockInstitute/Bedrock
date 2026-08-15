{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.306] probe.  THE CLEAN `Agree` FAMILY, PORTED GENERIC IN THE
-- CLASS, WAVE 1 OF `q'`.
--
-- The scaffold is [LJ-1.298]'s `GenTagAgree` shape: the eight parameters
-- are `GenModel`'s, the codings come from `GenModel` applied at them.
-- ONE scaffold serves the whole chapter.  Below the marker, every block
-- is copied VERBATIM from `src/L/Condensation.lagda.md` at the line
-- range the trailing manifest records, in chapter order.  The diff
-- against the original spans is the task's number.
--
-- The `L.Coding.Shape` syntax that five of the modules name is re-stated
-- first, verbatim from `src/L/Coding/Shape.lagda.md:99-104`, `:140-142`
-- and `:170-191`: pure syntax over `GenModel` primitives, so it ports
-- unchanged.  `Δ₀-liftFo` comes from `GM.ToL`, the generic twin of
-- `L.Absoluteness`'s committed delivery, under the same name.
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

import LJ-1-210.GenModel

module LJ-1-306.GenAgree {ℓ : Level}
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

module GM = LJ-1-210.GenModel {ℓ} M M-trans
              numeralL numeralL-fst pairʟ pairʟ-fst sucʟ sucʟ-fst
open GM
open GM.ToL using ( Δ₀-liftFo )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure (𝒮ᵥ {ℓ} ↾ M) using ( S )
open GM.AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- THE `L.Coding.Shape` SYNTAX, RE-STATED.  Verbatim from
-- src/L/Coding/Shape.lagda.md:99-105, :140-142 and :169-190.
-- =====================================================================

module _ {n : ℕ} where
  binForm : ℕ → Formula S (4 + n) → Formula S (suc n)
  binForm k rel = ∃̇ (∃̇ (∃̇ (arityTagPairAtL
    (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero ∧̇ rel)))

  unForm : ℕ → Formula S (3 + n) → Formula S (suc n)
  unForm k rel = ∃̇ (∃̇ (arityTagAtL (suc (suc zero)) (suc zero) k zero ∧̇ rel))

isTmAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
isTmAt t N A = ∃̇ (tagAtL (suc t) 0 zero ∧̇ (var zero ∈̇ var (suc A)))
            ∨̇ ∃̇ (tagAtL (suc t) 1 zero ∧̇ (var zero ∈̇ var (suc N)))

module _ {n : ℕ} where
  bothTm fstTm : Fin n → Formula S (4 + n)
  bothTm A = isTmAt (suc zero) (suc (suc zero)) (suc (suc (suc (suc A))))
          ∧̇ isTmAt zero (suc (suc zero)) (suc (suc (suc (suc A))))
  fstTm  A = isTmAt (suc zero) (suc (suc zero)) (suc (suc (suc (suc A))))

  noneB : Formula S (4 + n)
  noneB = ⊤̇ {n = 4 + n}

  zeroPay noneU : Formula S (3 + n)
  zeroPay = var zero ≐ con (numeralL 0)
  noneU   = ⊤̇ {n = 3 + n}

  shapes : Fin n → Formula S (suc n)
  shapes A = binForm 0 (bothTm A) ∨̇ (binForm 1 (bothTm A)
           ∨̇ (binForm 2 noneB ∨̇ (binForm 3 noneB ∨̇ (binForm 4 noneB
           ∨̇ (unForm 5 noneU ∨̇ (unForm 6 zeroPay ∨̇ (unForm 7 zeroPay
           ∨̇ (unForm 8 noneU ∨̇ (unForm 9 noneU
           ∨̇ (binForm 10 (fstTm A) ∨̇ binForm 11 (fstTm A)))))))))))

  shapedAt : Fin n → Fin n → Formula S n
  shapedAt C A = ∀̇∈ (var C) (shapes A)

-- =====================================================================
-- BELOW THIS LINE: VERBATIM FROM `src/L/Condensation.lagda.md`, in
-- chapter order.  The manifest at the file's end records each block's
-- source range.
-- =====================================================================

Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)


Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)


Δ₀-appAt : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

-- The bounded extension frame: "the set at y is exactly the satisfiers
-- of phi, and every satisfier lies in K".  The bounded restatement of
-- the delivered `extAt`.

extAtB : ∀ {n} → Fin n → Fin n → Formula S (suc n) → Formula S n
extAtB y K φ = ∀̇∈ (var y) φ
             ∧̇ ∀̇∈ (var K) (φ ⇒̇ (var zero ∈̇ var (suc y)))


Δ₀-extAtB : ∀ {n} (y K : Fin n) (φ : Formula S (suc n))
          → Δ₀ φ → Δ₀ (extAtB y K φ)
Δ₀-extAtB y K φ d = δ-∧ (δ-∀∈ d) (δ-∀∈ (δ-⇒ d δ-∈))

module Clause {n : ℕ} (C T B N : Fin n) where
  private
    K : Fin (suc n)
    K = zero

    C₁ T₁ B₁ : Fin (suc n)
    C₁ = suc C
    T₁ = suc T
    B₁ = suc B

  -- envSet content at env e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=e 1=E 2=ya 3=yc 4=a 5=ar 6=c 7=K, B at 8+r
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

  -- subvalue content at env z₂ ∷ z₁ ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=z₂ 1=z₁ 3=ya 5=a 6=ar, T at 9+q
  subValBnd : Formula S (9 + n)
  subValBnd =
    prAtL zero (suc zero) (suc (suc (suc (suc (suc zero)))))
    ∧̇ appAt (suc (suc (suc (suc (suc (suc (suc (suc T₁))))))))
            zero (suc (suc (suc zero)))

  -- body content at env z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ, with z
  -- the extension candidate of `extBnd`
  -- slots: 0=z 1=E 4=ya 7=K, B at 8+r
  bodyBnd : Formula S (8 + n)
  bodyBnd =
    (var zero ∈̇ var (suc zero))
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc B₁))))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
          (consAtL zero (suc zero) (suc (suc zero))
          ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ))

  -- shape hypothesis at env yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=yc 1=a 2=ar 3=c 4=K
  shapeBnd : Formula S (5 + n)
  shapeBnd =
    ∃̇∈ (var (suc (suc (suc (suc zero)))))
      (prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero
      ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
          ((var zero ≐ var (suc (suc (suc (suc (suc (suc (suc N))))))))
          ∧̇ prAtL (suc zero) zero (suc (suc (suc zero)))))

  -- subvalue hypothesis at env E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=E 1=ya 2=yc 3=a 4=ar 5=c 6=K
  subValHyp : Formula S (7 + n)
  subValHyp =
    ∃̇∈ (var (suc (suc (suc (suc (suc (suc zero)))))))
      (sucAtL (suc (suc (suc (suc (suc zero))))) zero
      ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc zero))))))))
          subValBnd)

  -- env hypothesis at env E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ: "E is
  -- exactly the set of environments over ar with values in B, as K
  -- sees it".  The first conjunct is the old one-way shape; the
  -- second is the conjunct the machine's envSetAt demands ([LJ-1.41-R]).
  envHyp : Formula S (7 + n)
  envHyp = extAtB zero (suc (suc (suc (suc (suc (suc zero)))))) envBnd

  -- the extension frame at the innermost point: "yc is exactly the set
  -- of candidates z with bodyBnd(z)", with the satisfiers in K
  extBnd : Formula S (7 + n)
  extBnd = extAtB (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero))))))
                  bodyBnd

  -- full matrix, arity suc n, bound at slot zero
  -- binders: c(∀∈C) ar a yc (∀∈K) ya E (∀∈K) z (extAtB yc K)
  --          x (∃∈B) e' (∃∈K)
  existBndAt : Formula S (suc n)
  existBndAt =
    ∀̇∈ (var C₁) (∀̇∈ (var (suc zero)) (∀̇∈ (var (suc (suc zero)))
      (∀̇∈ (var (suc (suc (suc zero))))
        (shapeBnd ⇒̇ (appAt (suc (suc (suc (suc T₁))))
                            (suc (suc (suc zero))) zero
        ⇒̇ (∀̇∈ (var (suc (suc (suc (suc zero)))))
            (∀̇∈ (var (suc (suc (suc (suc (suc zero))))))
              (subValHyp ⇒̇ (envHyp ⇒̇ extBnd)))))))))

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
    δ-∧ (Δ₀-prAtL zero (suc zero) (suc (suc (suc (suc (suc zero))))))
        (Δ₀-appAt (suc (suc (suc (suc (suc (suc (suc (suc T₁))))))))
                  zero (suc (suc (suc zero))))

  Δ₀-bodyBnd : Δ₀ bodyBnd
  Δ₀-bodyBnd =
    δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) (suc (suc zero))))
                              δ-∈)))

  Δ₀-shapeBnd : Δ₀ shapeBnd
  Δ₀-shapeBnd =
    δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero)
              (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero (suc (suc (suc zero)))))))

  Δ₀-subValHyp : Δ₀ subValHyp
  Δ₀-subValHyp =
    δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc (suc (suc (suc (suc zero))))) zero)
              (δ-∃∈ Δ₀-subValBnd))

  Δ₀-envHyp : Δ₀ envHyp
  Δ₀-envHyp =
    Δ₀-extAtB zero (suc (suc (suc (suc (suc (suc zero)))))) _ Δ₀-envBnd

  Δ₀-existBndAt : Δ₀ existBndAt
  Δ₀-existBndAt =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ Δ₀-shapeBnd
      (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc T₁)))) (suc (suc (suc zero))) zero)
        (δ-∀∈ (δ-∀∈ (δ-⇒ Δ₀-subValHyp (δ-⇒ Δ₀-envHyp
          (Δ₀-extAtB (suc (suc zero))
                     (suc (suc (suc (suc (suc (suc zero))))))
                     bodyBnd Δ₀-bodyBnd))))))))))

-- The Sigma-1 certificate: one existential over the bound, on the Delta-0
-- matrix.  At variable slots C T B N, over a variable environment.

arTagB : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
arTagB tag K =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
    (prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        ((var zero ≐ var (suc (suc (suc (suc (suc (suc tag)))))))
        ∧̇ prAtL (suc zero) zero (suc (suc (suc zero)))))


Δ₀-arTagB : ∀ {m} (tag K : Fin m) → Δ₀ (arTagB tag K)
Δ₀-arTagB tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero)
            (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero (suc (suc (suc zero)))))))

-- The bounded binary shape, at the frame environment
-- yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (5 + m): "c = pr ar (pr tag (pr a b))".

arTagPairB : ∀ {m} → Fin m → Fin m → Formula S (5 + m)
arTagPairB tag K =
  ∃̇∈ (var (suc (suc (suc (suc (suc K))))))
    (prAtL (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) zero
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc K)))))))
        ((var zero ≐ var (suc (suc (suc (suc (suc (suc (suc tag))))))))
        ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc K))))))))
            (prAtL (suc (suc zero)) (suc zero) zero
            ∧̇ prAtL zero (suc (suc (suc (suc (suc zero)))))
                     (suc (suc (suc (suc zero)))))))


Δ₀-arTagPairB : ∀ {m} (tag K : Fin m) → Δ₀ (arTagPairB tag K)
Δ₀-arTagPairB tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) zero)
            (δ-∃∈ (δ-∧ δ-≐ (δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero)
                                       (Δ₀-prAtL zero
                                                 (suc (suc (suc (suc (suc zero)))))
                                                 (suc (suc (suc (suc zero))))))))))

-- The bounded subvalue lookups.  "pr (pr ar a) y in T" (same arity)
-- and at the successor arity, with the key in K.

subValB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
subValB T ar a y K =
  ∃̇∈ (var K) (prAtL zero (suc ar) (suc a)
            ∧̇ appAt (suc T) zero (suc y))


Δ₀-subValB : ∀ {n} (T ar a y K : Fin n) → Δ₀ (subValB T ar a y K)
Δ₀-subValB T ar a y K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL zero (suc ar) (suc a))
            (Δ₀-appAt (suc T) zero (suc y)))


subValSuccB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
subValSuccB T ar a y K =
  ∃̇∈ (var K) (sucAtL (suc ar) zero
    ∧̇ ∃̇∈ (var (suc K)) (prAtL zero (suc zero) (suc (suc a))
        ∧̇ appAt (suc (suc T)) zero (suc (suc y))))


Δ₀-subValSuccB : ∀ {n} (T ar a y K : Fin n) → Δ₀ (subValSuccB T ar a y K)
Δ₀-subValSuccB T ar a y K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc ar) zero)
            (δ-∃∈ (δ-∧ (Δ₀-prAtL zero (suc zero) (suc (suc a)))
                       (Δ₀-appAt (suc (suc T)) zero (suc (suc y))))))

-- The bounded term value: a variable term (t = pr tag1 z, pr z v in e)
-- or a constant term (t = pr tag0 v), with the keys in K.

tmValB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
tmValB t e v K t0 t1 =
    (∃̇∈ (var K) (∃̇∈ (var (suc K))
       ((var zero ≐ var (suc (suc t1)))
       ∧̇ prAtL (suc (suc t)) zero (suc zero)
       ∧̇ appAt (suc (suc e)) (suc zero) (suc (suc v)))))
  ∨̇ (∃̇∈ (var K) ((var zero ≐ var (suc t0))
               ∧̇ prAtL (suc t) zero (suc v)))


Δ₀-tmValB : ∀ {n} (t e v K t0 t1 : Fin n) → Δ₀ (tmValB t e v K t0 t1)
Δ₀-tmValB t e v K t0 t1 =
  δ-∨ (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐
         (δ-∧ (Δ₀-prAtL (suc (suc t)) zero (suc zero))
              (Δ₀-appAt (suc (suc e)) (suc zero) (suc (suc v)))))))
      (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc t) zero (suc v))))

-- The generic bounded environment condition: E is a set of
-- environments over ar with domain yc and values in B.  The six slot
-- positions are parameters, so one formula serves every frame layout.

envBndGen : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
envBndGen e E yc ar K B =
    (∀̇∈ (var K) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
       (appAt (suc (suc (suc e))) (suc (suc zero)) (suc zero)
       ⇒̇ (appAt (suc (suc (suc e))) (suc (suc zero)) zero
         ⇒̇ (var (suc zero) ≐ var zero))))))
    ∧̇ (∀̇∈ (var K)
         (((∃̇∈ (var (suc K)) (appAt (suc (suc e)) (suc zero) zero))
         ⇒̇ (var zero ∈̇ var (suc ar)))
        ∧̇ ((var zero ∈̇ var (suc ar))
         ⇒̇ (∃̇∈ (var (suc K)) (appAt (suc (suc e)) (suc zero) zero)))))
    ∧̇ (∀̇∈ (var K) (∀̇∈ (var (suc K))
         (appAt (suc (suc e)) (suc zero) zero
         ⇒̇ (var zero ∈̇ var (suc (suc B))))))
    ∧̇ (∀̇∈ (var e)
         (∃̇∈ (var (suc ar)) (∃̇∈ (var (suc (suc B)))
           (prAtL (suc (suc zero)) (suc zero) zero))))


Δ₀-envBndGen : ∀ {n} (e E yc ar K B : Fin n) → Δ₀ (envBndGen e E yc ar K B)
Δ₀-envBndGen e E yc ar K B =
  δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc (suc e)))
                                          (suc (suc zero)) (suc zero))
                             (δ-⇒ (Δ₀-appAt (suc (suc (suc e)))
                                            (suc (suc zero)) zero)
                                  δ-≐)))))
      (δ-∧ (δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt (suc (suc e)) (suc zero) zero))
                            δ-∈)
                      (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt (suc (suc e)) (suc zero) zero)))))
           (δ-∧ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc e)) (suc zero) zero) δ-∈)))
                (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero))))))

-- THE MISSING CONJUNCT, GENERIC ([LJ-1.41-R], ProbeDD25F41A).  The
-- bounded environment-set condition: "E is exactly the set of
-- environments over ar with values in B, as K sees it".  The first
-- conjunct is the delivered envHyp* shape; the second is the conjunct
-- the machine's envSetAt demands.  The E, ar, B and K arguments are
-- slot positions at the frame gamma, so one formula serves every frame
-- layout.

envSetB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
envSetB E ar B K =
  extAtB E K (envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))


Δ₀-envSetB : ∀ {n} (E ar B K : Fin n) → Δ₀ (envSetB E ar B K)
Δ₀-envSetB E ar B K =
  Δ₀-extAtB E K _ (Δ₀-envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B))

-- The bounded operations.  Each is the delivered operation with the
-- second universal bounded by K.

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


diffB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
diffB y a b K =
  extAtB y K ((var zero ∈̇ var (suc a)) ∧̇ ¬̇ (var zero ∈̇ var (suc b)))


Δ₀-diffB : ∀ {n} (y a b K : Fin n) → Δ₀ (diffB y a b K)
Δ₀-diffB y a b K = Δ₀-extAtB y K _ (δ-∧ δ-∈ (δ-¬ δ-∈))


sameB : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
sameB y a K = extAtB y K (var zero ∈̇ var (suc a))


Δ₀-sameB : ∀ {n} (y a K : Fin n) → Δ₀ (sameB y a K)
Δ₀-sameB y a K = Δ₀-extAtB y K _ δ-∈


emptyB : ∀ {n} → Fin n → Fin n → Formula S n
emptyB y K = extAtB y K ⊥̇


Δ₀-emptyB : ∀ {n} (y K : Fin n) → Δ₀ (emptyB y K)
Δ₀-emptyB y K = Δ₀-extAtB y K _ δ-⊥

-- The environment hypotheses, one per frame layout.  Each is the
-- two-conjunct envSetB at its layout: the delivered one-way shape
-- (every member of E satisfies the bounded condition) plus the
-- machine's missing conjunct (every member of K satisfying the
-- condition is in E).  The E slot is always zero; the ar, B and K
-- slots are the layout's own.
-- Unary (with the second value slot ya): E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ
-- (6 + m), B at 7 + B, K at 7 + K.

envHypU : ∀ {m} → Fin m → Fin m → Formula S (6 + m)
envHypU {m} B K =
  envSetB zero (suc (suc (suc (suc zero))))
           (suc (suc (suc (suc (suc (suc B))))))
           (suc (suc (suc (suc (suc (suc K))))))


Δ₀-envHypU : ∀ {m} (B K : Fin m) → Δ₀ (envHypU B K)
Δ₀-envHypU {m} B K =
  Δ₀-envSetB zero (suc (suc (suc (suc zero))))
                (suc (suc (suc (suc (suc (suc B))))))
                (suc (suc (suc (suc (suc (suc K))))))

-- Constant (no second value slot): E ∷ yc ∷ a ∷ ar ∷ c ∷ γ (5 + m),
-- B at 6 + B, K at 6 + K.

envHypT : ∀ {m} → Fin m → Fin m → Formula S (5 + m)
envHypT {m} B K =
  envSetB zero (suc (suc (suc zero)))
           (suc (suc (suc (suc (suc B)))))
           (suc (suc (suc (suc (suc K)))))


Δ₀-envHypT : ∀ {m} (B K : Fin m) → Δ₀ (envHypT B K)
Δ₀-envHypT {m} B K =
  Δ₀-envSetB zero (suc (suc (suc zero)))
                (suc (suc (suc (suc (suc B)))))
                (suc (suc (suc (suc (suc K)))))

-- Binary (with ya): E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (7 + m),
-- B at 8 + B, K at 8 + K.

envHypB2 : ∀ {m} → Fin m → Fin m → Formula S (7 + m)
envHypB2 {m} B K =
  envSetB zero (suc (suc (suc (suc (suc zero)))))
           (suc (suc (suc (suc (suc (suc (suc B)))))))
           (suc (suc (suc (suc (suc (suc (suc K)))))))


Δ₀-envHypB2 : ∀ {m} (B K : Fin m) → Δ₀ (envHypB2 B K)
Δ₀-envHypB2 {m} B K =
  Δ₀-envSetB zero (suc (suc (suc (suc (suc zero)))))
                (suc (suc (suc (suc (suc (suc (suc B)))))))
                (suc (suc (suc (suc (suc (suc (suc K)))))))

-- Binary without ya (atom rows): E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (6 + m),
-- B at 7 + B, K at 7 + K.

envHypB2T : ∀ {m} → Fin m → Fin m → Formula S (6 + m)
envHypB2T {m} B K =
  envSetB zero (suc (suc (suc (suc zero))))
           (suc (suc (suc (suc (suc (suc B))))))
           (suc (suc (suc (suc (suc (suc K))))))


Δ₀-envHypB2T : ∀ {m} (B K : Fin m) → Δ₀ (envHypB2T B K)
Δ₀-envHypB2T {m} B K =
  Δ₀-envSetB zero (suc (suc (suc (suc zero))))
                (suc (suc (suc (suc (suc (suc B))))))
                (suc (suc (suc (suc (suc (suc K))))))

-- =====================================================================
-- THE FIVE ROW FRAMES.  Each frame is generic in the environment arity
-- m and the K slot, so one formula serves the class carrier (K = 0)
-- and the graph's inner environment (K shifted by the three graph
-- binders).
-- =====================================================================
-- The unary frame, full: c in C, ar in K, a in K, yc in K; shape;
-- lookup; ya in K, E in K; sub; env; the body at the extension
-- candidate.  The body carries its own extension frame.

unFullAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m)
         → Formula S (6 + m) → Formula S (6 + m) → Formula S (6 + m)
         → Formula S m
unFullAt C T K shape sub env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
    (∀̇∈ (var (suc (suc (suc K))))
      (shape ⇒̇ (appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero
      ⇒̇ (∀̇∈ (var (suc (suc (suc (suc K)))))
          (∀̇∈ (var (suc (suc (suc (suc (suc K))))))
            (sub ⇒̇ (env ⇒̇ body)))))))))


Δ₀-unFullAt : ∀ {m} (C T K : Fin m) (shape : Formula S (4 + m))
            (sub env body : Formula S (6 + m))
            → Δ₀ shape → Δ₀ sub → Δ₀ env → Δ₀ body
            → Δ₀ (unFullAt C T K shape sub env body)
Δ₀-unFullAt C T K shape sub env body ds dsub denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds
    (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero)
      (δ-∀∈ (δ-∀∈ (δ-⇒ dsub (δ-⇒ denv dbody)))))))))

-- The unary frame, environment only (the constant row top).

unEnvAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m) → Formula S (5 + m)
        → Formula S (5 + m) → Formula S m
unEnvAt C T K shape env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
    (∀̇∈ (var (suc (suc (suc K))))
      (shape ⇒̇ (appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero
      ⇒̇ (∀̇∈ (var (suc (suc (suc (suc K)))))
            (env ⇒̇ body)))))))


Δ₀-unEnvAt : ∀ {m} (C T K : Fin m) (shape : Formula S (4 + m))
           (env body : Formula S (5 + m))
           → Δ₀ shape → Δ₀ env → Δ₀ body
           → Δ₀ (unEnvAt C T K shape env body)
Δ₀-unEnvAt C T K shape env body ds denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds
    (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero)
      (δ-∀∈ (δ-⇒ denv dbody)))))))

-- The unary frame, bare (the constant row bot).

unBareAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m) → Formula S (4 + m)
         → Formula S m
unBareAt C T K shape body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
    (∀̇∈ (var (suc (suc (suc K))))
      (shape ⇒̇ (appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero
      ⇒̇ body)))))


Δ₀-unBareAt : ∀ {m} (C T K : Fin m) (shape : Formula S (4 + m))
            (body : Formula S (4 + m))
            → Δ₀ shape → Δ₀ body → Δ₀ (unBareAt C T K shape body)
Δ₀-unBareAt C T K shape body ds dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds
    (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero)
      dbody)))))

-- The binary frame, full.

binFullAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (5 + m) → Formula S (7 + m)
          → Formula S (7 + m) → Formula S (7 + m) → Formula S m
binFullAt C T K shape sub env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
    (∀̇∈ (var (suc (suc (suc K)))) (∀̇∈ (var (suc (suc (suc (suc K)))))
      (shape ⇒̇ (appAt (suc (suc (suc (suc (suc T)))))
                       (suc (suc (suc (suc zero)))) zero
      ⇒̇ (∀̇∈ (var (suc (suc (suc (suc (suc K))))))
          (∀̇∈ (var (suc (suc (suc (suc (suc (suc K)))))))
            (sub ⇒̇ (env ⇒̇ body))))))))))


Δ₀-binFullAt : ∀ {m} (C T K : Fin m) (shape : Formula S (5 + m))
             (sub env body : Formula S (7 + m))
             → Δ₀ shape → Δ₀ sub → Δ₀ env → Δ₀ body
             → Δ₀ (binFullAt C T K shape sub env body)
Δ₀-binFullAt C T K shape sub env body ds dsub denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds
    (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc (suc T)))))
                    (suc (suc (suc (suc zero)))) zero)
      (δ-∀∈ (δ-∀∈ (δ-⇒ dsub (δ-⇒ denv dbody))))))))))

-- The binary frame, environment only (the atom rows).

binEnvAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (5 + m) → Formula S (6 + m)
         → Formula S (6 + m) → Formula S m
binEnvAt C T K shape env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
    (∀̇∈ (var (suc (suc (suc K)))) (∀̇∈ (var (suc (suc (suc (suc K)))))
      (shape ⇒̇ (appAt (suc (suc (suc (suc (suc T)))))
                       (suc (suc (suc (suc zero)))) zero
      ⇒̇ (∀̇∈ (var (suc (suc (suc (suc (suc K))))))
            (env ⇒̇ body))))))))


Δ₀-binEnvAt : ∀ {m} (C T K : Fin m) (shape : Formula S (5 + m))
            (env body : Formula S (6 + m))
            → Δ₀ shape → Δ₀ env → Δ₀ body
            → Δ₀ (binEnvAt C T K shape env body)
Δ₀-binEnvAt C T K shape env body ds denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds
    (δ-⇒ (Δ₀-appAt (suc (suc (suc (suc (suc T)))))
                    (suc (suc (suc (suc zero)))) zero)
      (δ-∀∈ (δ-⇒ denv dbody))))))))

-- The two-way decode of the full unary frame at the class carrier.
-- OUT: a satisfied frame gives the layered content.  IN: the layered
-- content assembles the frame.

propBodyB : ∀ {m} → Fin m → Fin m → Formula S (8 + m) → Formula S (7 + m)
propBodyB T K op =
  ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc K))))))))
    (subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
             (suc (suc (suc (suc (suc (suc zero))))))
             (suc (suc (suc (suc zero))))
             zero
             (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
    ⇒̇ op)


Δ₀-propBodyB : ∀ {m} (T K : Fin m) (op : Formula S (8 + m))
             → Δ₀ op → Δ₀ (propBodyB T K op)
Δ₀-propBodyB T K op dop =
  δ-∀∈ (δ-⇒ (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                         (suc (suc (suc (suc (suc (suc zero))))))
                         (suc (suc (suc (suc zero))))
                         zero
                         (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
            dop)

-- The atom body: "y in E, and there are term values v of a and w of b
-- in K with v cmp w".

atomBodyB : ∀ {m} → Fin m → Fin m → Fin m → Formula S (9 + m) → Formula S (7 + m)
atomBodyB t0 t1 K cmp =
  (var zero ∈̇ var (suc zero))
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc K))))))))
      (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
        (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc (suc zero))
                (suc zero)
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ∧̇ tmValB (suc (suc (suc (suc (suc zero)))))
                (suc (suc zero))
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ∧̇ cmp))


Δ₀-atomBodyB : ∀ {m} (t0 t1 K : Fin m) (cmp : Formula S (9 + m))
             → Δ₀ cmp → Δ₀ (atomBodyB t0 t1 K cmp)
Δ₀-atomBodyB t0 t1 K cmp dc =
  δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∧ d1 (δ-∧ d2 dc))))
  where
  d1 : Δ₀ (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                  (suc (suc zero))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))))
  d1 = Δ₀-tmValB (suc (suc (suc (suc (suc (suc zero))))))
                 (suc (suc zero))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))

  d2 : Δ₀ (tmValB (suc (suc (suc (suc (suc zero)))))
                  (suc (suc zero))
                  zero
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))))
  d2 = Δ₀-tmValB (suc (suc (suc (suc (suc zero)))))
                 (suc (suc zero))
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))

-- The bounded-quantifier bodies: "y in E, and for the term value w of
-- a (in K), for every x in B with x in w, every extended environment
-- e' in K satisfies e' in ya".

bndBodyAll : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (7 + m)
bndBodyAll B K t0 t1 =
  extAtB (suc (suc zero))
         (suc (suc (suc (suc (suc (suc (suc K)))))))
    ((var zero ∈̇ var (suc zero))
    ∧̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
        (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ⇒̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))
            ((var zero ∈̇ var (suc zero))
            ⇒̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))
                (consAtL zero (suc zero) (suc (suc (suc zero)))
                ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero))))))))))


bndBodyEx : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (7 + m)
bndBodyEx B K t0 t1 =
  extAtB (suc (suc zero))
         (suc (suc (suc (suc (suc (suc (suc K)))))))
    ((var zero ∈̇ var (suc zero))
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
        (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))
            ((var zero ∈̇ var (suc zero))
            ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))
                (consAtL zero (suc zero) (suc (suc (suc zero)))
                ∧̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero))))))))))


Δ₀-bndBodyAll : ∀ {m} (B K t0 t1 : Fin m) → Δ₀ (bndBodyAll B K t0 t1)
Δ₀-bndBodyAll B K t0 t1 =
  Δ₀-extAtB (suc (suc zero))
            (suc (suc (suc (suc (suc (suc (suc K))))))) _
    (δ-∧ δ-∈ (δ-∀∈ (δ-⇒ dt (δ-∀∈ (δ-⇒ δ-∈ (δ-∀∈ (δ-⇒ dc δ-∈)))))))
  where
  dt : Δ₀ (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                  (suc zero)
                  zero
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))))
  dt = Δ₀-tmValB (suc (suc (suc (suc (suc (suc zero))))))
                 (suc zero)
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))

  dc : Δ₀ (consAtL zero (suc zero) (suc (suc (suc zero))))
  dc = Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) (suc (suc (suc zero))))


Δ₀-bndBodyEx : ∀ {m} (B K t0 t1 : Fin m) → Δ₀ (bndBodyEx B K t0 t1)
Δ₀-bndBodyEx B K t0 t1 =
  Δ₀-extAtB (suc (suc zero))
            (suc (suc (suc (suc (suc (suc (suc K))))))) _
    (δ-∧ δ-∈ (δ-∃∈ (δ-∧ dt (δ-∃∈ (δ-∧ δ-∈ (δ-∃∈ (δ-∧ dc δ-∈)))))))
  where
  dt : Δ₀ (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                  (suc zero)
                  zero
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                  (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))))
  dt = Δ₀-tmValB (suc (suc (suc (suc (suc (suc zero))))))
                 (suc zero)
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                 (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))

  dc : Δ₀ (consAtL zero (suc zero) (suc (suc (suc zero))))
  dc = Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) (suc (suc (suc zero))))

-- =====================================================================
-- THE ELEVEN ROWS.  Each row is one instantiation of its frame at the
-- generic environment arity m, with its Delta-0 witness.  The tag
-- numerals are slots, so every formula is constant-free.
-- =====================================================================

module Bot {m : ℕ} (C T B N K : Fin m) where
  botBndAt : Formula S m
  botBndAt = unBareAt C T K (arTagB N K) (emptyB zero (suc (suc (suc (suc K)))))

  Δ₀-botBndAt : Δ₀ botBndAt
  Δ₀-botBndAt =
    Δ₀-unBareAt C T K (arTagB N K) (emptyB zero (suc (suc (suc (suc K)))))
      (Δ₀-arTagB N K) (Δ₀-emptyB zero (suc (suc (suc (suc K)))))


module Top {m : ℕ} (C T B N K : Fin m) where
  topBndAt : Formula S m
  topBndAt =
    unEnvAt C T K (arTagB N K) (envHypT B K)
      (sameB (suc zero) zero (suc (suc (suc (suc (suc K))))))

  Δ₀-topBndAt : Δ₀ topBndAt
  Δ₀-topBndAt =
    Δ₀-unEnvAt C T K (arTagB N K) (envHypT B K)
      (sameB (suc zero) zero (suc (suc (suc (suc (suc K))))))
      (Δ₀-arTagB N K) (Δ₀-envHypT B K)
      (Δ₀-sameB (suc zero) zero (suc (suc (suc (suc (suc K))))))


module Neg {m : ℕ} (C T B N K : Fin m) where
  subN : Formula S (6 + m)
  subN = subValB (suc (suc (suc (suc (suc (suc T))))))
                   (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero)))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc K))))))

  bodyN : Formula S (6 + m)
  bodyN = diffB (suc (suc zero)) zero (suc zero)
                  (suc (suc (suc (suc (suc (suc K))))))

  negBndAt : Formula S m
  negBndAt = unFullAt C T K (arTagB N K) subN (envHypU B K) bodyN

  Δ₀-negBndAt : Δ₀ negBndAt
  Δ₀-negBndAt =
    Δ₀-unFullAt C T K (arTagB N K) subN (envHypU B K) bodyN
      (Δ₀-arTagB N K)
      (Δ₀-subValB (suc (suc (suc (suc (suc (suc T))))))
                  (suc (suc (suc (suc zero))))
                  (suc (suc (suc zero)))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc K)))))))
      (Δ₀-envHypU B K)
      (Δ₀-diffB (suc (suc zero)) zero (suc zero)
                (suc (suc (suc (suc (suc (suc K)))))))


module Forall {m : ℕ} (C T B N K : Fin m) where
  subF : Formula S (6 + m)
  subF = subValSuccB (suc (suc (suc (suc (suc (suc T))))))
                       (suc (suc (suc (suc zero))))
                       (suc (suc (suc zero)))
                       (suc zero)
                       (suc (suc (suc (suc (suc (suc K))))))

  bodyFφ : Formula S (7 + m)
  bodyFφ =
      (var zero ∈̇ var (suc zero))
      ∧̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc B))))))))
          (∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
            (consAtL zero (suc zero) (suc (suc zero))
            ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc zero)))))))

  bodyF : Formula S (6 + m)
  bodyF = extAtB (suc (suc zero))
                   (suc (suc (suc (suc (suc (suc K))))))
                   bodyFφ

  Δ₀-bodyFφ : Δ₀ bodyFφ
  Δ₀-bodyFφ =
      δ-∧ δ-∈ (δ-∀∈ (δ-∀∈ (δ-⇒
        (Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) (suc (suc zero))))
        δ-∈)))

  forallBndAt : Formula S m
  forallBndAt = unFullAt C T K (arTagB N K) subF (envHypU B K) bodyF

  Δ₀-forallBndAt : Δ₀ forallBndAt
  Δ₀-forallBndAt =
    Δ₀-unFullAt C T K (arTagB N K) subF (envHypU B K) bodyF
      (Δ₀-arTagB N K)
      (Δ₀-subValSuccB (suc (suc (suc (suc (suc (suc T))))))
                      (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero)))
                      (suc zero)
                      (suc (suc (suc (suc (suc (suc K)))))))
      (Δ₀-envHypU B K)
      (Δ₀-extAtB (suc (suc zero))
                 (suc (suc (suc (suc (suc (suc K))))))
                 bodyFφ Δ₀-bodyFφ)


module And {m : ℕ} (C T B N K : Fin m) where
  subA : Formula S (7 + m)
  subA = subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K)))))))

  opA : Formula S (8 + m)
  opA = interB (suc (suc (suc zero)))
                 (suc (suc zero))
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc K))))))))

  andBndAt : Formula S m
  andBndAt = binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
              (propBodyB T K opA)

  Δ₀-andBndAt : Δ₀ andBndAt
  Δ₀-andBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
      (propBodyB T K opA)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc K))))))))
      (Δ₀-envHypB2 B K)
      (Δ₀-propBodyB T K opA
        (Δ₀-interB (suc (suc (suc zero)))
                   (suc (suc zero))
                   zero
                   (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))


module Or {m : ℕ} (C T B N K : Fin m) where
  subO : Formula S (7 + m)
  subO = subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K)))))))

  opO : Formula S (8 + m)
  opO = unionB (suc (suc (suc zero)))
                 (suc (suc zero))
                 zero
                 (suc (suc (suc (suc (suc (suc (suc (suc K))))))))

  orBndAt : Formula S m
  orBndAt = binFullAt C T K (arTagPairB N K) subO (envHypB2 B K)
             (propBodyB T K opO)

  Δ₀-orBndAt : Δ₀ orBndAt
  Δ₀-orBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subO (envHypB2 B K)
      (propBodyB T K opO)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc K))))))))
      (Δ₀-envHypB2 B K)
      (Δ₀-propBodyB T K opO
        (Δ₀-unionB (suc (suc (suc zero)))
                   (suc (suc zero))
                   zero
                   (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))


module Imp {m : ℕ} (C T B N K : Fin m) where
  subI : Formula S (7 + m)
  subI = subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K)))))))

  opI : Formula S (8 + m)
  opI = implB (suc (suc (suc zero)))
                (suc zero)
                (suc (suc zero))
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc K))))))))

  impBndAt : Formula S m
  impBndAt = binFullAt C T K (arTagPairB N K) subI (envHypB2 B K)
              (propBodyB T K opI)

  Δ₀-impBndAt : Δ₀ impBndAt
  Δ₀-impBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subI (envHypB2 B K)
      (propBodyB T K opI)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc (suc zero))))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc K))))))))
      (Δ₀-envHypB2 B K)
      (Δ₀-propBodyB T K opI
        (Δ₀-implB (suc (suc (suc zero)))
                  (suc zero)
                  (suc (suc zero))
                  zero
                  (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))


module Mem {m : ℕ} (C T B N K t0 t1 : Fin m) where
  bodyM : Formula S (6 + m)
  bodyM = extAtB (suc zero)
                   (suc (suc (suc (suc (suc (suc K))))))
                   (atomBodyB t0 t1 K (var (suc zero) ∈̇ var zero))

  memBndAt : Formula S m
  memBndAt = binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyM

  Δ₀-memBndAt : Δ₀ memBndAt
  Δ₀-memBndAt =
    Δ₀-binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyM
      (Δ₀-arTagPairB N K) (Δ₀-envHypB2T B K)
      (Δ₀-extAtB (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (atomBodyB t0 t1 K (var (suc zero) ∈̇ var zero))
                 (Δ₀-atomBodyB t0 t1 K (var (suc zero) ∈̇ var zero) δ-∈))


module Eq {m : ℕ} (C T B N K t0 t1 : Fin m) where
  bodyE : Formula S (6 + m)
  bodyE = extAtB (suc zero)
                   (suc (suc (suc (suc (suc (suc K))))))
                   (atomBodyB t0 t1 K (var (suc zero) ≐ var zero))

  eqBndAt : Formula S m
  eqBndAt = binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyE

  Δ₀-eqBndAt : Δ₀ eqBndAt
  Δ₀-eqBndAt =
    Δ₀-binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyE
      (Δ₀-arTagPairB N K) (Δ₀-envHypB2T B K)
      (Δ₀-extAtB (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (atomBodyB t0 t1 K (var (suc zero) ≐ var zero))
                 (Δ₀-atomBodyB t0 t1 K (var (suc zero) ≐ var zero) δ-≐))


module AllIn {m : ℕ} (C T B N K t0 t1 : Fin m) where
  subA : Formula S (7 + m)
  subA = subValSuccB (suc (suc (suc (suc (suc (suc (suc T)))))))
                       (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc zero)))
                       (suc zero)
                       (suc (suc (suc (suc (suc (suc (suc K)))))))

  allInBndAt : Formula S m
  allInBndAt = binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
                (bndBodyAll B K t0 t1)

  Δ₀-allInBndAt : Δ₀ allInBndAt
  Δ₀-allInBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
      (bndBodyAll B K t0 t1)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValSuccB (suc (suc (suc (suc (suc (suc (suc T)))))))
                      (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc zero)))
                      (suc zero)
                      (suc (suc (suc (suc (suc (suc (suc K))))))))
      (Δ₀-envHypB2 B K)
      (Δ₀-bndBodyAll B K t0 t1)


module ExIn {m : ℕ} (C T B N K t0 t1 : Fin m) where
  subE : Formula S (7 + m)
  subE = subValSuccB (suc (suc (suc (suc (suc (suc (suc T)))))))
                       (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc zero)))
                       (suc zero)
                       (suc (suc (suc (suc (suc (suc (suc K)))))))

  exInBndAt : Formula S m
  exInBndAt = binFullAt C T K (arTagPairB N K) subE (envHypB2 B K)
               (bndBodyEx B K t0 t1)

  Δ₀-exInBndAt : Δ₀ exInBndAt
  Δ₀-exInBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subE (envHypB2 B K)
      (bndBodyEx B K t0 t1)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValSuccB (suc (suc (suc (suc (suc (suc (suc T)))))))
                      (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc zero)))
                      (suc zero)
                      (suc (suc (suc (suc (suc (suc (suc K))))))))
      (Δ₀-envHypB2 B K)
      (Δ₀-bndBodyEx B K t0 t1)

-- The twelfth row, the bounded existential (block 1's clause at the
-- generic layout), for the twelve-row conjunction inside the graph.

module Exist {m : ℕ} (C T B N K : Fin m) where
  subE : Formula S (6 + m)
  subE = subValSuccB (suc (suc (suc (suc (suc (suc T))))))
                       (suc (suc (suc (suc zero))))
                       (suc (suc (suc zero)))
                       (suc zero)
                       (suc (suc (suc (suc (suc (suc K))))))

  bodyE : Formula S (7 + m)
  bodyE = (var zero ∈̇ var (suc zero))
            ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc B))))))))
                (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                  (consAtL zero (suc zero) (suc (suc zero))
                  ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero)))))))

  existBndAt : Formula S m
  existBndAt = unFullAt C T K (arTagB N K) subE (envHypU B K)
                 (extAtB (suc (suc zero))
                         (suc (suc (suc (suc (suc (suc K))))))
                         bodyE)

  Δ₀-existBndAt : Δ₀ existBndAt
  Δ₀-existBndAt =
    Δ₀-unFullAt C T K (arTagB N K) subE (envHypU B K)
      (extAtB (suc (suc zero))
              (suc (suc (suc (suc (suc (suc K))))))
              bodyE)
      (Δ₀-arTagB N K)
      (Δ₀-subValSuccB (suc (suc (suc (suc (suc (suc T))))))
                      (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero)))
                      (suc zero)
                      (suc (suc (suc (suc (suc (suc K)))))))
      (Δ₀-envHypU B K)
      (Δ₀-extAtB (suc (suc zero))
                 (suc (suc (suc (suc (suc (suc K))))))
                 bodyE
                 (δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∧
                   (Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) (suc (suc zero))))
                   δ-∈)))))

-- =====================================================================
-- THE BOUNDED CODE-SET DESCRIPTION.  The bounded restatement of the
-- three leaves of `DefBody` (src/L/Coding/Powerset.lagda.md:437-440):
-- the code predicate, the satisfaction graph and the definable-subset
-- condition.  The description is stated at the [LJ-1.35] leaf
-- environment v' ∷ c' ∷ x ∷ δ (8 + n), with the carrier w and the bound
-- K at slots 3 + w, 3 + K.  This section discharges the one surviving
-- Delta-0 premise of the story's step clause.  The arity tags are
-- SLOTS, one spelling with the rows: each row's numeral is a parameter
-- (N0 to N11, t0 and t1), so every formula here carries countFo = 0 by
-- refl and the erase route opens at the hull (P-v, P-u).
-- =====================================================================
-- The tag numerals are SLOTS (the file's own house style, :1111-1114),
-- so every formula in this chain is constant-free and `countFo ≡ 0` by
-- refl.  The site fact "the slot holds the numeral" is paid where an
-- adequacy proof consumes the chain; the erase route needs only the
-- zero count.

tagBS : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
tagBS s tag x K =
  ∃̇∈ (var K) ((var zero ≐ var (suc tag))
            ∧̇ prAtL (suc s) zero (suc x))


arTagPairBS : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
arTagPairBS tag K =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
  (prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K)))))))
          ((var (suc zero) ≐ var (suc (suc (suc (suc (suc (suc (suc tag))))))))
          ∧̇ prAtL (suc (suc zero)) (suc zero) zero
          ∧̇ prAtL zero (suc (suc (suc (suc zero)))) (suc (suc (suc zero))))))


arTagBS : ∀ {m} → Fin m → Fin m → Formula S (3 + m)
arTagBS tag K =
  ∃̇∈ (var (suc (suc (suc K))))
  (prAtL (suc (suc (suc zero))) (suc (suc zero)) zero
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc K)))))
        ((var zero ≐ var (suc (suc (suc (suc (suc tag))))))
        ∧̇ prAtL (suc zero) zero (suc (suc zero))))


binShapeBS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m) → Formula S m
binShapeBS C tag K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
  (∀̇∈ (var (suc (suc (suc K))))
      (arTagPairBS tag K ⇒̇ rel))))


unShapeBS : ∀ {m} → Fin m → Fin m → Fin m → Formula S (3 + m) → Formula S m
unShapeBS C tag K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
  (arTagBS tag K ⇒̇ rel)))


bothSameB : ∀ {m} → Fin m → Formula S (4 + m)
bothSameB C =
  appAt (suc (suc (suc (suc C)))) (suc (suc zero)) (suc zero)
  ∧̇ appAt (suc (suc (suc (suc C)))) (suc (suc zero)) zero


oneSameB : ∀ {m} → Fin m → Formula S (3 + m)
oneSameB C = appAt (suc (suc (suc C))) (suc zero) zero


oneSuccB : ∀ {m} → Fin m → Fin m → Formula S (3 + m)
oneSuccB C K =
  ∃̇∈ (var (suc (suc (suc K))))
  (sucAtL (suc (suc zero)) zero
  ∧̇ appAt (suc (suc (suc (suc C)))) zero (suc zero))


succSndB : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
succSndB C K =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
  (sucAtL (suc (suc (suc zero))) zero
  ∧̇ appAt (suc (suc (suc (suc (suc C))))) zero (suc zero))


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


binFormBS : ∀ {m} → Fin m → Fin m → Formula S (4 + m) → Formula S (1 + m)
binFormBS tag K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) (∃̇∈ (var (suc (suc (suc K))))
  (arTagPairBS tag K ∧̇ rel)))


unFormBS : ∀ {m} → Fin m → Fin m → Formula S (3 + m) → Formula S (1 + m)
unFormBS tag K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K)))
  (arTagBS tag K ∧̇ rel))


isTmBS : ∀ {m} → Fin (4 + m) → Fin m → Fin m → Fin m → Fin m
       → Formula S (4 + m)
isTmBS t A K N0 N1 =
    (∃̇∈ (var (suc (suc (suc (suc K)))))
       (tagBS (suc t) (suc (suc (suc (suc (suc N0))))) zero
              (suc (suc (suc (suc (suc K)))))
       ∧̇ (var zero ∈̇ var (suc (suc (suc (suc (suc A))))))))
  ∨̇ (∃̇∈ (var (suc (suc (suc (suc K)))))
       (tagBS (suc t) (suc (suc (suc (suc (suc N1))))) zero
              (suc (suc (suc (suc (suc K)))))
       ∧̇ (var zero ∈̇ var (suc (suc (suc zero))))))


bothTmBS : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (4 + m)
bothTmBS A K N0 N1 =
  isTmBS (suc zero) A K N0 N1 ∧̇ isTmBS zero A K N0 N1


fstTmBS : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (4 + m)
fstTmBS A K N0 N1 = isTmBS (suc zero) A K N0 N1


shapesBS : ∀ {m} → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula S (1 + m)
shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  binFormBS N0 K (bothTmBS A K N0 N1)
  ∨̇ (binFormBS N1 K (bothTmBS A K N0 N1)
  ∨̇ (binFormBS N2 K ⊤̇
  ∨̇ (binFormBS N3 K ⊤̇
  ∨̇ (binFormBS N4 K ⊤̇
  ∨̇ (unFormBS N5 K ⊤̇
  ∨̇ (unFormBS N6 K (var zero ≐ var (suc (suc (suc N0))))
  ∨̇ (unFormBS N7 K (var zero ≐ var (suc (suc (suc N0))))
  ∨̇ (unFormBS N8 K ⊤̇
  ∨̇ (unFormBS N9 K ⊤̇
  ∨̇ (binFormBS N10 K (fstTmBS A K N0 N1)
  ∨̇ binFormBS N11 K (fstTmBS A K N0 N1)))))))))))


shapedBS : ∀ {m} → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula S m
shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  ∀̇∈ (var C) (shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)


domB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
domB f d K =
  ∀̇∈ (var K)
  (((∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))
      ⇒̇ (var zero ∈̇ var (suc d)))
  ∧̇ ((var zero ∈̇ var (suc d))
      ⇒̇ (∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))))


extAtB→extAt : ∀ {n} (y K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  → ⟨ γ ⊨ extAtB y K φB ⟩ → ⟨ γ ⊨ extAt y φ ⟩
extAtB→extAt y K φB φ γ fwd bwd inK h =
  extAt-in-both y φ γ
    (λ z z∈ → fwd z (h .fst z z∈))
    (λ z hz → h .snd z (inK z hz) (bwd z hz))


extAt→extAtB : ∀ {n} (y K : Fin n) (φB φ : Formula S (suc n)) (γ : S ^ n)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
  → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩)
  → ⟨ γ ⊨ extAt y φ ⟩ → ⟨ γ ⊨ extAtB y K φB ⟩
extAt→extAtB y K φB φ γ fwd bwd h =
    (λ z z∈ → bwd z (h .fst z z∈))
  , (λ z _ hz → h .snd z (fwd z hz))

-- The unary shape transfer: the bounded arTagB against the machine's
-- arityTagAtL, at the 4-depth environment yc ∷ a ∷ ar ∷ c ∷ γ.

module UnaryShape {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (4 + m)) where
  -- The tag column holds the numeral, the numeral and the inner code
  -- lie in K.
  tagEq : Type (ℓ-suc ℓ)
  tagEq = fst (lookup (suc (suc (suc (suc tag)))) γ) ≡ fst (numeralL k)

  numK : Type (ℓ-suc ℓ)
  numK = ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩

  innerK : Type (ℓ-suc ℓ)
  innerK = (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
           → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩

  out : tagEq → ⟨ γ ⊨ arTagB tag K ⟩
      → ⟨ γ ⊨ arityTagAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) ⟩
  out te h = transport (cong fst (sym (arityTagAtL-adequate (suc (suc (suc zero)))
                         (suc (suc zero)) k (suc zero) γ))) target
    where
    target : fst (lookup (suc (suc (suc zero))) γ)
           ≡ pr (fst (lookup (suc (suc zero)) γ))
                (pr (# k) (fst (lookup (suc zero) γ)))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , (tt , zt))) →
          let a₀ = fst (lookup (suc zero) γ)
              ar₀ = fst (lookup (suc (suc zero)) γ)
              p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
                  ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                       (fst (lookup zero (z ∷ γ)))
              p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                    (suc (suc (suc zero))) zero (z ∷ γ))) p
              zt' : fst (lookup (suc zero) (t ∷ z ∷ γ))
                   ≡ pr (fst (lookup zero (t ∷ z ∷ γ)))
                        (fst (lookup (suc (suc (suc zero))) (t ∷ z ∷ γ)))
              zt' = transport (cong fst (prAtL-adequate (suc zero) zero (suc (suc (suc zero)))
                    (t ∷ z ∷ γ))) zt
              tt' : fst (lookup zero (t ∷ z ∷ γ))
                  ≡ fst (lookup (suc (suc (suc (suc tag)))) γ)
              tt' = tt
          in p' ∙ cong (pr ar₀) zt'
               ∙ cong (λ w → pr ar₀ (pr w a₀))
                      (tt' ∙ te ∙ numeralL-fst k) })
        kz })
      h

  in' : tagEq → numK → innerK
      → ⟨ fst (lookup (suc zero) γ) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
      → ⟨ γ ⊨ arityTagAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) ⟩
      → ⟨ γ ⊨ arTagB tag K ⟩
  in' te nk ik a₀K h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
              ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                   (fst (lookup zero (z ∷ γ)))
          p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                (suc (suc (suc zero))) zero (z ∷ γ))) p
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (fst (lookup (suc (suc zero)) (z ∷ γ)))
          tz' = transport (cong fst (tagAtL-adequate zero k (suc (suc zero)) (z ∷ γ))) tz
          a₀ : S
          a₀ = lookup (suc zero) γ
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                   (prʟ-fst (numeralL k) a₀ ∙ cong₂ pr (numeralL-fst k) refl)
                   (ik a₀ a₀K))
          zt : ⟨ (numeralL k ∷ z ∷ γ) ⊨ prAtL (suc zero) zero (suc (suc (suc zero))) ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc zero) zero (suc (suc (suc zero)))
                 (numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k)) refl)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( nk
                     , ( sym te
                       , zt ) )
                   ∣₁ ) ) ∣₁ })
    h

-- The binary shape transfer: the bounded arTagPairB against the
-- machine's arityTagPairAtL, at the 5-depth environment
-- yc ∷ b ∷ a ∷ ar ∷ c ∷ γ.

module BinaryShape {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (5 + m)) where
  tagEq : Type (ℓ-suc ℓ)
  tagEq = fst (lookup (suc (suc (suc (suc (suc tag))))) γ) ≡ fst (numeralL k)

  numK : Type (ℓ-suc ℓ)
  numK = ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  innerK : Type (ℓ-suc ℓ)
  innerK = (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
           → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
           → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  pairK : Type (ℓ-suc ℓ)
  pairK = (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
           → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  out : tagEq → ⟨ γ ⊨ arTagPairB tag K ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                               (suc (suc zero)) (suc zero) ⟩
  out te h = transport (cong fst (sym (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                         (suc (suc (suc zero))) k (suc (suc zero)) (suc zero) γ))) target
    where
    target : fst (lookup (suc (suc (suc (suc zero)))) γ)
           ≡ pr (fst (lookup (suc (suc (suc zero))) γ))
                (pr (# k) (pr (fst (lookup (suc (suc zero)) γ)) (fst (lookup (suc zero) γ))))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , (tt , kt))) → PT.rec (setIsSet _ _)
          (λ { (w , (w∈ , (zt , wb))) →
            let a₀ = fst (lookup (suc (suc zero)) γ)
                b₀ = fst (lookup (suc zero) γ)
                ar₀ = fst (lookup (suc (suc (suc zero))) γ)
                p' : fst (lookup (suc (suc (suc (suc (suc zero))))) (z ∷ γ))
                    ≡ pr (fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ)))
                         (fst (lookup zero (z ∷ γ)))
                p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) zero (z ∷ γ))) p
                zt' : fst (lookup (suc (suc zero)) (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup zero (w ∷ t ∷ z ∷ γ)))
                zt' = transport (cong fst (prAtL-adequate (suc (suc zero)) (suc zero) zero
                      (w ∷ t ∷ z ∷ γ))) zt
                wb' : fst (lookup zero (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc (suc (suc (suc (suc zero))))) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ)))
                wb' = transport (cong fst (prAtL-adequate zero (suc (suc (suc (suc (suc zero)))))
                      (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ))) wb
                tt' : fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ))
                    ≡ fst (lookup (suc (suc (suc (suc (suc tag))))) γ)
                tt' = tt
            in p' ∙ cong (pr ar₀) (zt' ∙ cong (pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))) wb')
                 ∙ cong (λ v → pr ar₀ (pr v (pr a₀ b₀)))
                        (tt' ∙ te ∙ numeralL-fst k) })
          kt })
        kz })
      h

  in' : tagEq → numK → innerK → pairK
      → ⟨ fst (lookup (suc (suc zero)) γ) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
      → ⟨ fst (lookup (suc zero) γ) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                               (suc (suc zero)) (suc zero) ⟩
      → ⟨ γ ⊨ arTagPairB tag K ⟩
  in' te nk ik pk a₀K b₀K h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let a₀ : S
          a₀ = lookup (suc (suc zero)) γ
          b₀ : S
          b₀ = lookup (suc zero) γ
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                              (fst (lookup (suc (suc zero)) (z ∷ γ))))
          tz' = transport (cong fst (tagPairAtL-adequate zero k (suc (suc (suc zero))) (suc (suc zero)) (z ∷ γ))) tz
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩)
                   (prʟ-fst (numeralL k) (prʟ a₀ b₀)
                    ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a₀ b₀))
                   (ik a₀ b₀ a₀K b₀K))
          zt : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k))
                    (sym (prʟ-fst a₀ b₀)))
          wb : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc zero)))) ⟩
          wb = transport (cong fst (sym (prAtL-adequate zero (suc (suc (suc (suc (suc zero)))))
                 (suc (suc (suc (suc zero))))
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (prʟ-fst a₀ b₀)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( nk
                     , ( sym te
                       , ∣ prʟ a₀ b₀
                         , ( pk a₀ b₀ a₀K b₀K
                           , ( zt , wb ) )
                         ∣₁ ) )
                   ∣₁ ) ) ∣₁ })
    h

-- The empty operation transfer, with no site facts.

emptyB→emptyAt : ∀ {n} (y K : Fin n) (γ : S ^ n)
  → ⟨ γ ⊨ emptyB y K ⟩ → ⟨ γ ⊨ emptyAt y ⟩
emptyB→emptyAt y K γ h =
  extAtB→extAt y K ⊥̇ ⊥̇ γ (λ z x → x) (λ z x → x) (λ z x → Empty.rec (x .lower)) h


emptyAt→emptyB : ∀ {n} (y K : Fin n) (γ : S ^ n)
  → ⟨ γ ⊨ emptyAt y ⟩ → ⟨ γ ⊨ emptyB y K ⟩
emptyAt→emptyB y K γ h =
  extAt→extAtB y K ⊥̇ ⊥̇ γ (λ z x → x) (λ z x → x) h

-- =====================================================================
-- THE GRAPH ENTRY THE CLAUSE FRAMES ALREADY BIND ([LJ-1.153]).
--
-- Between the shape and the relation, `binClauseAt` and `unClauseAt`
-- bind the reader `appAt T c yc`: the graph records the value `yc` at
-- the code `c` (src/L/Coding/Model.lagda.md:901 and :993).  Every row's
-- `back` binds it as `hc` and hands it straight on.
--
-- The site fact `valK` used to conclude `yc ∈ K` from the code alone,
-- and `yc` occurred in NO premise.  That statement is FALSE: take `yc`
-- to be the K slot itself and regularity closes it
-- (agents/tasks/LJ-1-153/ProbeLJ1153A.agda:89, exit 0; first measured
-- at [LJ-1.151]).  The repaired `valK` takes the graph entry as a
-- premise, and that is the fact [LJ-1.151] measured supplyable in 21
-- lines at a concrete level: `pr c yc` sits in the graph, the graph
-- sits in `K`, and `K` is transitive.
--
-- These two read `hc` through adequacy once.  The twelve rows share one
-- copy instead of writing twelve transports, and neither names a tower
-- (DD4).
-- =====================================================================

module GraphEntry {m : ℕ} (T : Fin m) (γ : S ^ m) where

  bin : (c ar a b yc : S)
      → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
           appAt (suc (suc (suc (suc (suc T)))))
                 (suc (suc (suc (suc zero)))) zero ⟩
      → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
  bin c ar a b yc = subst ⟨_⟩
    (appAt-adequate (suc (suc (suc (suc (suc T)))))
                    (suc (suc (suc (suc zero)))) zero
                    (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))

  un : (c ar a yc : S)
     → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
          appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero ⟩
     → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
  un c ar a yc = subst ⟨_⟩
    (appAt-adequate (suc (suc (suc (suc T))))
                    (suc (suc (suc zero))) zero
                    (yc ∷ a ∷ ar ∷ c ∷ γ))

-- The Bot row agreement at the class carrier.

module BotAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 7))
  (numK : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 7) a) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩) where

  private
    φB : Formula S m
    φB = Bot.botBndAt C T B N K

  bot-out : ⟨ γ ⊨ botClauseAt C T ⟩ → ⟨ γ ⊨ φB ⟩
  bot-out h = λ c c∈ ar arK a aK yc ycK shB hc →
    let shD = UnaryShape.out {m} N K 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
        hb = h c c∈ ar a yc shD hc
    in emptyAt→emptyB zero (suc (suc (suc (suc K)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

  bot-in : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ botClauseAt C T ⟩
  bot-in h = λ c c∈ ar a yc shD hc →
    let shEq : fst c ≡ pr (fst ar) (pr (# 7) (fst a))
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 7 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , arNum)) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq (GraphEntry.un {m} T γ c ar a yc hc)
        shB = UnaryShape.in' {m} N K 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq numK innerK aK shD
        hb = h c c∈ ar arK a aK yc ycK shB hc
    in emptyB→emptyAt zero (suc (suc (suc (suc K)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

-- THE FOUR-STEP PAIR CHAIN ([LJ-1.99]).  arityK is one step of
-- transitivity into K: v ∈ N and N ∈ K give v ∈ K.  Four
-- applications climb from the pair membership pr x y ∈ z and the
-- z ∈ K premise to the components x ∈ K and y ∈ K; the arSubK tie
-- is arityK once.  The chain is generic: one field plus the pair
-- encoding, nothing about definability.  The untied entryK is
-- refuted at the abstract frame ([LJ-1.97], ProbeLJ197A); the tied
-- form (premise z ∈ K) is the honest one, supplied by arityK.

module ChainZ {n : ℕ} (K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩) where

  -- The V-level pair pieces, from pairing-ax alone (the pair encoding).
  -- a ∈ ⁅ a ⁆s.
  a∈singl : (a : V ℓ) → ⟨ a ∈ ⁅ a ⁆s ⟩
  a∈singl a = subst (λ w → ⟨ a ∈ w ⟩) (pair-singleton a)
    (∈∈ₛ {a = a} {b = ⁅ a , a ⁆} .snd (pairing-ax a a a .snd ∣ inl refl ∣₁))

  -- ⁅ a ⁆s ∈ pr a b, the first component of the Kuratowski pair.
  singl∈pr : (a b : V ℓ) → ⟨ ⁅ a ⁆s ∈ pr a b ⟩
  singl∈pr a b = ∈∈ₛ {a = ⁅ a ⁆s} {b = pr a b} .snd
    (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a ⁆s .snd ∣ inl refl ∣₁)

  -- ⁅ a , b ⁆ ∈ pr a b, the second component of the Kuratowski pair.
  pair∈pr : (a b : V ℓ) → ⟨ ⁅ a , b ⁆ ∈ pr a b ⟩
  pair∈pr a b = ∈∈ₛ {a = ⁅ a , b ⁆} {b = pr a b} .snd
    (pairing-ax ⁅ a ⁆s ⁅ a , b ⁆ ⁅ a , b ⁆ .snd ∣ inr refl ∣₁)

  -- b ∈ ⁅ a , b ⁆.
  b∈pair : (a b : V ℓ) → ⟨ b ∈ ⁅ a , b ⁆ ⟩
  b∈pair a b = ∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .snd
    (pairing-ax a b b .snd ∣ inr refl ∣₁)

  -- Step 2: pr x y ∈ z and z ∈ K give pr x y ∈ K, one arityK
  -- through fst (prʟ x y) ≡ pr (fst x) (fst y).
  prʟxy∈z : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
           → ⟨ fst (prʟ x y) ∈ fst z ⟩
  prʟxy∈z z x y p = subst (λ w → ⟨ w ∈ fst z ⟩) (sym (prʟ-fst x y)) p

  prxy∈K : (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩
          → ⟨ fst (prʟ x y) ∈ fst (lookup K γ) ⟩
  prxy∈K z x y p zK' = arityK z (prʟ x y) (prʟxy∈z z x y p) zK'

  -- Step 3x: the singleton of x lies in pr x y.  The L-set singleton
  -- is pairʟ x x, whose fst is ⁅ A , A ⁆, definitionally ⁅ A ⁆s.
  xsingl∈prxy : (x y : S) → ⟨ fst (pairʟ x x) ∈ fst (prʟ x y) ⟩
  xsingl∈prxy x y =
    subst (λ w → ⟨ fst (pairʟ x x) ∈ w ⟩) (sym (prʟ-fst x y))
      (subst (λ w → ⟨ w ∈ pr (fst x) (fst y) ⟩) (sym (pairʟ-fst x x))
        (subst (λ w → ⟨ w ∈ pr (fst x) (fst y) ⟩)
               (sym (pair-singleton (fst x)))
               (singl∈pr (fst x) (fst y))))

  -- Step 4x: x ∈ fst (pairʟ x x).
  x∈pairʟxx : (x : S) → ⟨ fst x ∈ fst (pairʟ x x) ⟩
  x∈pairʟxx x =
    subst (λ w → ⟨ fst x ∈ w ⟩) (sym (pairʟ-fst x x))
      (subst (λ w → ⟨ fst x ∈ w ⟩) (sym (pair-singleton (fst x)))
        (a∈singl (fst x)))

  -- The x half: steps 2 to 4, from the z ∈ K premise.
  xK' : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
      → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
      → ⟨ fst x ∈ fst (lookup K γ) ⟩
  xK' z x y zK' p =
    arityK (pairʟ x x) x (x∈pairʟxx x)
      (arityK (prʟ x y) (pairʟ x x) (xsingl∈prxy x y)
        (prxy∈K z x y p zK'))

  -- Step 3y: ⁅ A , B ⁆ lies in pr A B, the second component.
  ysingl∈prxy : (x y : S) → ⟨ fst (pairʟ x y) ∈ fst (prʟ x y) ⟩
  ysingl∈prxy x y =
    subst (λ w → ⟨ fst (pairʟ x y) ∈ w ⟩) (sym (prʟ-fst x y))
      (subst (λ w → ⟨ w ∈ pr (fst x) (fst y) ⟩) (sym (pairʟ-fst x y))
        (pair∈pr (fst x) (fst y)))

  -- Step 4y: y ∈ fst (pairʟ x y).
  y∈pairʟxy : (x y : S) → ⟨ fst y ∈ fst (pairʟ x y) ⟩
  y∈pairʟxy x y =
    subst (λ w → ⟨ fst y ∈ w ⟩) (sym (pairʟ-fst x y))
      (b∈pair (fst x) (fst y))

  -- The y half: steps 2 to 4, from the z ∈ K premise.
  yK' : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
      → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
      → ⟨ fst y ∈ fst (lookup K γ) ⟩
  yK' z x y zK' p =
    arityK (pairʟ x y) y (y∈pairʟxy x y)
      (arityK (prʟ x y) (pairʟ x y) (ysingl∈prxy x y)
        (prxy∈K z x y p zK'))

  -- THE ENTRYK TIE: from the z ∈ K premise, the components of the
  -- pair close in K.
  entryK-tied-zK : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
                  → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
                  → ⟨ fst x ∈ fst (lookup K γ) ⟩
                    × ⟨ fst y ∈ fst (lookup K γ) ⟩
  entryK-tied-zK z x y zK' p = xK' z x y zK' p , yK' z x y zK' p

  -- THE ARSUBK TIE: x ∈ ar and ar ∈ K give x ∈ K, arityK once.
  arSubK-tied : (ar x : S) → ⟨ fst x ∈ fst ar ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩
              → ⟨ fst x ∈ fst (lookup K γ) ⟩
  arSubK-tied ar x hxar arK = arityK ar x hxar arK

-- THE GENERIC ENVIRONMENT-SET TRANSFER ([LJ-1.41-R], ProbeDD25F41B).
-- The story's two-conjunct bounded envSetB against the machine's
-- envSetAt, BOTH directions, under arityK plus the two memberships
-- E ∈ K and ar ∈ K, and the environment fact envInK.  The entryK
-- and arSubK ties are DERIVED inside from arityK (the ChainZ module
-- above), so no row states or repeats them.  The E, ar, B and K
-- arguments are slot positions at the frame gamma, so one copy
-- serves every frame layout and both towers.  The machine-to-story
-- direction needs envInK only; the story-to-machine direction needs
-- no envInK.

module EnvSet {n : ℕ} (E ar B K : Fin n) (γ : S ^ n)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (E∈K : ⟨ fst (lookup E γ) ∈ fst (lookup K γ) ⟩)
  (ar∈K : ⟨ fst (lookup ar γ) ∈ fst (lookup K γ) ⟩)
  (envInK : (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc ar) (suc B) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where

  -- The ChainZ entryK tie and the arSubK tie, derived ONCE from
  -- arityK and the two memberships.
  module Z = ChainZ {n} K γ arityK

  entryK : (z x y : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
         → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
         → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩
  entryK = Z.entryK-tied-zK

  arSubK : (x : S) → ⟨ fst x ∈ fst (lookup ar γ) ⟩
         → ⟨ fst x ∈ fst (lookup K γ) ⟩
  arSubK x hxar = Z.arSubK-tied (lookup ar γ) x hxar ar∈K

  φB : Formula S (suc n)
  φB = envBndGen zero (suc E) (suc E) (suc ar) (suc K) (suc B)

  φ : Formula S (suc n)
  φ = envOverAt zero (suc ar) (suc B)

  -- The app formula at the three-binder frame is the pair membership.
  app3 : (z x y y' : S)
       → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
            appAt (suc (suc (suc zero))) (suc (suc zero)) (suc zero) ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app3 z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) (suc zero)
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app3' : (z x y y' : S)
        → ⟨ (y' ∷ y ∷ x ∷ z ∷ γ) ⊨
             appAt (suc (suc (suc zero))) (suc (suc zero)) zero ⟩
        ≡ ⟨ pr (fst x) (fst y') ∈ fst z ⟩
  app3' z x y y' =
    cong ⟨_⟩ (appAt-adequate (suc (suc (suc zero))) (suc (suc zero)) zero
                (y' ∷ y ∷ x ∷ z ∷ γ))

  app2 : (z x y : S)
       → ⟨ (y ∷ x ∷ z ∷ γ) ⊨ appAt (suc (suc zero)) (suc zero) zero ⟩
       ≡ ⟨ pr (fst x) (fst y) ∈ fst z ⟩
  app2 z x y =
    cong ⟨_⟩ (appAt-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ z ∷ γ))

  -- STORY TO MACHINE, TIED: the K-bounded condition gives the
  -- machine's unbounded condition, under the z ∈ K premise.
  bnd→over : (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
           → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩
  bnd→over z zK hb =
      svAt-in zero (z ∷ γ)
        (λ x y y' p q →
          let xK = entryK z x y zK p .fst
              yK = entryK z x y zK p .snd
              y'K = entryK z x y' zK q .snd
          in hb .fst x xK y yK y' y'K
               (transport (sym (app3 z x y y')) p)
               (transport (sym (app3' z x y y')) q))
    , domAt-intro zero (suc ar) (z ∷ γ)
        (λ x →
            (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                      (λ { (y , p) →
                        hb .snd .fst x (entryK z x y zK p .fst) .fst
                          ∣ y , ( entryK z x y zK p .snd
                                , transport (sym (app2 z x y)) p ) ∣₁ })
                      hx)
          , (λ hxar → PT.map
                        (λ { (y , (yK , hp)) → y , transport (app2 z x y) hp })
                        (hb .snd .fst x (arSubK x hxar) .snd hxar)))
    , valuesInAt-in zero (suc B) (z ∷ γ)
        (λ x y p →
          hb .snd .snd .fst x (entryK z x y zK p .fst) y (entryK z x y zK p .snd)
            (transport (sym (app2 z x y)) p))
    , hb .snd .snd .snd

  -- MACHINE TO STORY, TIED: the machine's condition reaches the
  -- K-bounded one, under the z ∈ K premise.
  over→bnd : (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩
           → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩
  over→bnd z zK h =
      (λ x xK y yK y' y'K p q →
        svAt-out zero (z ∷ γ) (h .fst) x y y'
          (transport (app3 z x y y') p) (transport (app3' z x y y') q))
    , (λ x xK →
          (λ hx → PT.rec (snd (fst x ∈ fst (lookup ar γ)))
                    (λ { (y , (yK , hp)) →
                      domAt-out zero (suc ar) (z ∷ γ) (h .snd .fst) x y
                        (transport (app2 z x y) hp) })
                    hx)
        , (λ hxar → PT.rec squash₁
                      (λ { (y , p) →
                        ∣ y , ( entryK z x y zK p .snd
                              , transport (sym (app2 z x y)) p ) ∣₁ })
                      (domAt-in zero (suc ar) (z ∷ γ) (h .snd .fst) x hxar)))
    , (λ x xK y yK p →
        valuesInAt-out zero (suc B) (z ∷ γ) (h .snd .snd .fst) x y
          (transport (app2 z x y) p))
    , h .snd .snd .snd

  -- THE ENVIRONMENT-SET TRANSFER, BOTH WAYS.  The out direction's
  -- first component climbs z ∈ E to z ∈ K by arityK and E ∈ K; its
  -- second component takes z ∈ K from envInK.  The back direction
  -- closes with the same two supplies.
  out : ⟨ γ ⊨ envSetB E ar B K ⟩ → ⟨ γ ⊨ envSetAt E ar B ⟩
  out h = extAt-in-both E φ γ
    (λ z z∈ → bnd→over z (arityK (lookup E γ) z z∈ E∈K) (h .fst z z∈))
    (λ z hz → h .snd z (envInK z hz) (over→bnd z (envInK z hz) hz))

  -- MACHINE TO STORY.
  back : ⟨ γ ⊨ envSetAt E ar B ⟩ → ⟨ γ ⊨ envSetB E ar B K ⟩
  back h =
      (λ z z∈ → over→bnd z (arityK (lookup E γ) z z∈ E∈K) (h .fst z z∈))
    , (λ z zK hz → h .snd z (bnd→over z zK hz))

  -- Every member of the ambient set is an environment, and every
  -- environment lies in K.  From the bounded condition.
  memE-bnd : ⟨ γ ⊨ envSetB E ar B K ⟩
           → (z : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩
  memE-bnd h z zE = envInK z (bnd→over z (arityK (lookup E γ) z zE E∈K) (h .fst z zE))

  -- From the machine's condition, the same fact is one projection.
  memE-at : ⟨ γ ⊨ envSetAt E ar B ⟩
          → (z : S) → ⟨ fst z ∈ fst (lookup E γ) ⟩
          → ⟨ fst z ∈ fst (lookup K γ) ⟩
  memE-at h z zE = envInK z (h .fst z zE)

-- The term-value transfer: the bounded tmValB against the machine's
-- tmValAt, under the tag-column facts and the keys-in-K fact.

module TmVal {m : ℕ} (t e v K t0 t1 : Fin m) (γ : S ^ m) where
  t0eq : Type (ℓ-suc ℓ)
  t0eq = fst (lookup t0 γ) ≡ fst (numeralL 0)

  t1eq : Type (ℓ-suc ℓ)
  t1eq = fst (lookup t1 γ) ≡ fst (numeralL 1)

  t0K : Type (ℓ-suc ℓ)
  t0K = ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩

  -- The TIED key membership: the tag satisfaction pins the key, so
  -- the unconditional form is refuted at the abstract frame
  -- ([LJ-1.97], ProbeLJ197A) and this is the honest shape.
  keyK : Type (ℓ-suc ℓ)
  keyK = (k : S) → ⟨ (k ∷ γ) ⊨ tagAtL (suc t) 1 zero ⟩
       → ⟨ fst k ∈ fst (lookup K γ) ⟩

  num1K : Type (ℓ-suc ℓ)
  num1K = ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩

  out : t0eq → t1eq → ⟨ γ ⊨ tmValB t e v K t0 t1 ⟩ → ⟨ γ ⊨ tmValAt t e v ⟩
  out t0e t1e h = PT.rec squash₁
    (λ { (inl h1) → PT.rec squash₁
           (λ { (k , (k∈ , hz)) → PT.rec squash₁
             (λ { (z , (z∈ , (zt0 , (zt , hk)))) →
               let zt' : fst (lookup (suc (suc t)) (z ∷ k ∷ γ))
                        ≡ pr (fst z) (fst k)
                   zt' = transport (cong fst (prAtL-adequate (suc (suc t)) zero (suc zero)
                           (z ∷ k ∷ γ))) zt
                   zeq : fst z ≡ fst (lookup t1 γ)
                   zeq = zt0
                   ht-path : fst (lookup (suc (suc t)) (z ∷ k ∷ γ))
                            ≡ pr (# 1) (fst k)
                   ht-path = zt' ∙ cong₂ pr (zeq ∙ t1e) refl
                            ∙ cong₂ pr (numeralL-fst 1) refl
                   ht-sat : ⟨ (k ∷ γ) ⊨ tagAtL (suc t) 1 zero ⟩
                   ht-sat = transport (cong fst (sym (tagAtL-adequate (suc t) 1 zero (k ∷ γ))))
                              ht-path
                   hm-mem : ⟨ pr (fst k) (fst (lookup (suc (suc v)) (z ∷ k ∷ γ)))
                              ∈ fst (lookup (suc (suc e)) (z ∷ k ∷ γ)) ⟩
                   hm-mem = subst ⟨_⟩ (appAt-adequate (suc (suc e)) (suc zero) (suc (suc v))
                              (z ∷ k ∷ γ)) hk
                   hm-sat : ⟨ (k ∷ γ) ⊨ appAt (suc e) zero (suc v) ⟩
                   hm-sat = subst ⟨_⟩ (sym (appAt-adequate (suc e) zero (suc v) (k ∷ γ))) hm-mem
               in ∣ inl ∣ k , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc t) 1 zero (k ∷ γ)))
                                  ht-path
                              , hm-sat ) ∣₁ ∣₁ }) hz })
           h1
       ; (inr h2) → PT.rec squash₁
           (λ { (k , (k∈ , (kt , hc))) →
             let hc' : fst (lookup (suc t) (k ∷ γ))
                      ≡ pr (fst k) (fst (lookup (suc v) (k ∷ γ)))
                 hc' = transport (cong fst (prAtL-adequate (suc t) zero (suc v) (k ∷ γ))) hc
             in
             ∣ inr (subst ⟨_⟩ (sym (tagAtL-adequate t 0 v γ))
                      (hc' ∙ cong₂ pr kt refl ∙ cong₂ pr t0e refl ∙ cong₂ pr (numeralL-fst 0) refl)) ∣₁ }) h2 })
    h

  in' : t0eq → t1eq → t0K → keyK → num1K
      → ⟨ γ ⊨ tmValAt t e v ⟩ → ⟨ γ ⊨ tmValB t e v K t0 t1 ⟩
  in' t0e t1e t0k kk n1k h = PT.rec squash₁
    (λ { (inl h) → PT.rec squash₁
           (λ { (k , (ht , hm)) →
             let ht' : fst (lookup (suc t) (k ∷ γ)) ≡ pr (# 1) (fst k)
                 ht' = transport (cong fst (tagAtL-adequate (suc t) 1 zero (k ∷ γ))) ht
                 hm' : ⟨ pr (fst k) (fst (lookup (suc v) (k ∷ γ)))
                         ∈ fst (lookup (suc e) (k ∷ γ)) ⟩
                 hm' = subst ⟨_⟩ (appAt-adequate (suc e) zero (suc v) (k ∷ γ)) hm
             in ∣ inl (∣ k , ( kk k ht
                            , ∣ numeralL 1
                              , ( n1k
                                , ( sym t1e
                                  , ( transport (cong fst (sym (prAtL-adequate (suc (suc t))
                                         zero (suc zero) (numeralL 1 ∷ k ∷ γ))))
                                      (ht' ∙ cong₂ pr (sym (numeralL-fst 1)) refl)
                                    , subst ⟨_⟩ (sym (appAt-adequate (suc (suc e)) (suc zero)
                                         (suc (suc v)) (numeralL 1 ∷ k ∷ γ))) hm' ) ) )
                              ∣₁ ) ∣₁) ∣₁ }) h
       ; (inr h) →
           let ht : fst (lookup t γ) ≡ pr (# 0) (fst (lookup v γ))
               ht = transport (cong fst (tagAtL-adequate t 0 v γ)) h
           in ∣ inr (∣ lookup t0 γ
                 , ( t0k
                   , ( refl
                     , transport (cong fst (sym (prAtL-adequate (suc t) zero (suc v)
                          (lookup t0 γ ∷ γ))))
                         (ht ∙ cong₂ pr (sym (numeralL-fst 0)) refl ∙ cong₂ pr (sym t0e) refl) ) )
                 ∣₁) ∣₁ })
    h

module SubValB2T {m : ℕ} (T ar a y K : Fin m) (γ : S ^ m)
  (keyK : ⟨ pr (fst (lookup ar γ)) (fst (lookup a γ)) ∈ fst (lookup K γ) ⟩) where

  -- The shared core of the bounded and the unbounded subvalue
  -- formulas, stated once in the machine's spelling.
  core : Formula S (suc m)
  core = prAtL zero (suc ar) (suc a) ∧̇ appAt (suc T) zero (suc y)

  -- MACHINE TO STORY: the machine witness plus the key fact gives the
  -- bounded parts, which are definitionally the bounded satisfaction.
  out : ⟨ γ ⊨ subValAt T ar a y ⟩
      → ∥ Σ S (λ z → ⟨ fst z ∈ fst (lookup K γ) ⟩ × ⟨ (z ∷ γ) ⊨ core ⟩) ∥₁
  out = PT.rec squash₁
    (λ { (z , (p , a₁)) →
      let zK : ⟨ fst z ∈ fst (lookup K γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩)
                 (sym (subst ⟨_⟩ (prAtL-adequate zero (suc ar) (suc a) (z ∷ γ)) p))
                 keyK
      in ∣ z , (zK , (p , a₁)) ∣₁ })

  -- STORY TO MACHINE.  The parts-input shape checks fastest at a
  -- single call site; this transfer has two row consumers, and each
  -- consumer-side destructure re-elaborates the bounded satisfaction
  -- at its own concrete indices (P-m's instantiation class).  The
  -- measured whole-file effect of the parts-input shape was negative
  -- for this family too, so the truncated-input form stays (reverted
  -- 2026-08-11, [LJ-1.45], reported in the return).
  back : ⟨ γ ⊨ subValB T ar a y K ⟩ → ⟨ γ ⊨ subValAt T ar a y ⟩
  back = PT.rec squash₁
    (λ { (z , (zK , (p , a₁))) → ∣ z , (p , a₁) ∣₁ })

-- The successor-subvalue transfer: subValSuccB against subValSuccAt.
-- Restated in ONE spelling per P-v: the statements carry only the
-- machine's subValSuccAt and the meta-level bounded parts.  The
-- machine reads the subformula's value at the successor arity; the
-- story's witnesses are the successor and the successor key, both in
-- K.

module SubValSuccB2T {m : ℕ} (T ar a y K : Fin m) (γ : S ^ m)
  (succK : ⟨ sucV (fst (lookup ar γ)) ∈ fst (lookup K γ) ⟩)
  (keyK : ⟨ pr (sucV (fst (lookup ar γ))) (fst (lookup a γ)) ∈ fst (lookup K γ) ⟩) where

  -- The shared cores in ONE spelling, used by the restated out.
  core₁ : Formula S (suc m)
  core₁ = sucAtL (suc ar) zero

  core₂ : Formula S (suc (suc m))
  core₂ = prAtL zero (suc zero) (suc (suc a)) ∧̇ appAt (suc (suc T)) zero (suc (suc y))

  -- MACHINE TO STORY: the machine witness plus the site facts gives
  -- the bounded parts, which are definitionally the bounded
  -- satisfaction.
  out : ⟨ γ ⊨ subValSuccAt T ar a y ⟩
      → ∥ Σ S (λ z₁ → ⟨ fst z₁ ∈ fst (lookup K γ) ⟩
          × ⟨ (z₁ ∷ γ) ⊨ core₁ ⟩
          × ∥ Σ S (λ z₂ → ⟨ fst z₂ ∈ fst (lookup (suc K) (z₁ ∷ γ)) ⟩
              × ⟨ (z₂ ∷ z₁ ∷ γ) ⊨ core₂ ⟩) ∥₁) ∥₁
  out h = PT.rec squash₁
    (λ { (z₁ , (sz₁ , hz₁)) → PT.rec squash₁
      (λ { (z₂ , (p₂ , a₂)) →
        let z₁eq : fst z₁ ≡ sucV (fst (lookup ar γ))
            z₁eq = subst ⟨_⟩ (sucAtL-adequate (suc ar) zero (z₁ ∷ γ)) sz₁
            z₂eq : fst z₂ ≡ pr (sucV (fst (lookup ar γ))) (fst (lookup a γ))
            z₂eq = subst ⟨_⟩ (prAtL-adequate zero (suc zero) (suc (suc a)) (z₂ ∷ z₁ ∷ γ)) p₂
                   ∙ cong₂ pr z₁eq refl
            z₁K : ⟨ fst z₁ ∈ fst (lookup K γ) ⟩
            z₁K = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (sym z₁eq) succK
            z₂K : ⟨ fst z₂ ∈ fst (lookup K γ) ⟩
            z₂K = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (sym z₂eq) keyK
        in ∣ z₁ , (z₁K , (sz₁ , ∣ z₂ , (z₂K , (p₂ , a₂)) ∣₁)) ∣₁ }) hz₁ })
    h

  -- STORY TO MACHINE.  The parts-input shape checks fastest at a
  -- single call site; this transfer has four row consumers, and each
  -- consumer-side destructure re-elaborates the bounded satisfaction
  -- at its own concrete indices (P-m's instantiation class).  The
  -- measured whole-file effect of the parts-input shape was negative
  -- for this family, so the truncated-input form stays (reverted
  -- 2026-08-11, [LJ-1.45], reported in the return).
  back : ⟨ γ ⊨ subValSuccB T ar a y K ⟩ → ⟨ γ ⊨ subValSuccAt T ar a y ⟩
  back = PT.rec squash₁
    (λ { (z₁ , (z₁K , (sz₁ , hz₁))) → PT.rec squash₁
      (λ { (z₂ , (z₂K , (p₂ , a₂))) → ∣ z₁ , (sz₁ , ∣ z₂ , (p₂ , a₂) ∣₁) ∣₁ })
      hz₁ })

-- The operation transfer: the bounded operation against the machine's
-- operation, with the SAME body.  The story-to-machine direction
-- needs the satisfiers-in-K site fact.

module OpTransfer {n : ℕ} (y K : Fin n) (φ : Formula S (suc n)) (γ : S ^ n)
  (inK : (z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩) where
  out : ⟨ γ ⊨ extAt y φ ⟩ → ⟨ γ ⊨ extAtB y K φ ⟩
  out = extAt→extAtB y K φ φ γ (λ z x → x) (λ z x → x)

  back : ⟨ γ ⊨ extAtB y K φ ⟩ → ⟨ γ ⊨ extAt y φ ⟩
  back = extAtB→extAt y K φ φ γ (λ z x → x) (λ z x → x) inK

module PropAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m) (k : ℕ)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (keyK : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ ar a) ∈ fst (lookup K γ) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (subK₁ : (x y yc b a ar c : S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc zero))))
                         (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (subK₀ : (y ya yc b a ar c : S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc zero)))
                         zero ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (someEnv : (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → Σ S (λ E → ⟨ fst E ∈ fst (lookup K γ) ⟩ × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {m} B K ⟩))
  (subA : Formula S (7 + m))
  (subAEq : subA ≡ subValB (suc (suc (suc (suc (suc (suc (suc T)))))))
             (suc (suc (suc (suc (suc zero)))))
             (suc (suc (suc (suc zero))))
             (suc zero)
             (suc (suc (suc (suc (suc (suc (suc K))))))))
  (op₁ : Formula S (7 + m))
  (op₂ : Formula S (8 + m))
  (body₁ : Formula S (suc (7 + m)))
  (body₂ : Formula S (suc (8 + m)))
  (opEq₁ : op₁ ≡ extAt (suc (suc zero)) body₁)
  (opEq₂ : op₂ ≡ extAtB (suc (suc (suc zero)))
             (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) body₂)
  (fwd : (z yb E ya yc b a ar c : S)
         → ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₁ ⟩
         → ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₂ ⟩)
  (bwd : (z yb E ya yc b a ar c : S)
         → ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₂ ⟩
         → ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₁ ⟩)
  (inK : (z yb E ya yc b a ar c : S)
         → ⟨ fst ya ∈ fst (lookup K γ) ⟩
         → ⟨ fst yb ∈ fst (lookup K γ) ⟩
         → ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body₂ ⟩
         → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where

  -- The site fact's prʟ-pair is propositionally the hierarchy pair;
  -- the delivered prʟ-fst supplies the transport once, here.
  keyK₀ : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → ⟨ pr (fst ar) (fst a) ∈ fst (lookup K γ) ⟩
  keyK₀ ar a arK aK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (prʟ-fst ar a) (keyK ar a arK aK)

  -- The machine's first subvalue at the story's env is the same type
  -- at the machine's env: subValAt reads only slots 1, 4, 5 and the
  -- table, never slot 0, and both envs have the same length.

  -- The second subvalue crosses the E extension: the story's bounded
  -- form is at yb ∷ E ∷ ... (8 + m), the machine's unbounded form at
  -- yb ∷ ya ∷ ... (7 + m).  Restated in ONE spelling per P-v: the
  -- statements carry the machine's subValAt, the witness z, its
  -- K-membership, and the shared core at the extended env.  The reads
  -- shift by one, and the adequate targets are the same pairs, so the
  -- transfer is two transports.
  coreS : Formula S (9 + m)
  coreS =
    prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
              (suc (suc (suc (suc (suc zero)))))
    ∧̇ appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
            zero (suc zero)

  subB2T : (yb E ya yc b a ar c : S) (z : S)
    → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                      (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
    → ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ coreS ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  zero ⟩
  subB2T yb E ya yc b a ar c z zK (p , a₁) =
    let p' : ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 prAtL zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc zero)))) ⟩
        p' = subst ⟨_⟩
          (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero)))))
                            (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
           ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                            (suc (suc (suc (suc zero))))
                            (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
          p
        a₁' : ⟨ (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 appAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                       zero (suc zero) ⟩
        a₁' = subst ⟨_⟩
          (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                          zero (suc zero)
                          (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
           ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                          zero (suc zero)
                          (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
          a₁
    in ∣ z , (p' , a₁') ∣₁

  subB2T-back : (yb E ya yc b a ar c : S)
    → ⟨ fst (prʟ ar b) ∈ fst (lookup K γ) ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  zero ⟩
    → ∥ Σ S (λ z → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                                  (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
                × ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ coreS ⟩) ∥₁
  subB2T-back yb E ya yc b a ar c keyK₀ h = PT.rec squash₁
    (λ { (z , (p , a₁)) →
      let p' : ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero))))) ⟩
          p' = subst ⟨_⟩
            (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc zero))))
                              (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                              (suc (suc (suc (suc (suc zero)))))
                              (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            p
          zK : ⟨ fst z ∈ fst (lookup K γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩)
                 (prʟ-fst ar b
                  ∙ sym (subst ⟨_⟩ (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc zero))))
                              (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) p))
                 keyK₀
          a₁' : ⟨ (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                         zero (suc zero) ⟩
          a₁' = subst ⟨_⟩
            (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
             ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                            zero (suc zero)
                            (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
            a₁
      in ∣ z , (zK , (p' , a₁')) ∣₁ })
    h

  -- The operation transfer across the E extension: the machine's
  -- operation at yb ∷ ya ∷ ... against the story's bounded operation
  -- at yb ∷ E ∷ ....
  opOut : (yb E ya yc b a ar c : S)
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         extAt (suc (suc zero)) body₁ ⟩
    → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         extAtB (suc (suc (suc zero)))
                (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) body₂ ⟩
  opOut yb E ya yc b a ar c h =
      ( λ z z∈ → fwd z yb E ya yc b a ar c (h .fst z z∈) )
    , ( λ z zK hz → h .snd z (bwd z yb E ya yc b a ar c hz) )

  opBack : (yb E ya yc b a ar c : S)
    → (yaK : ⟨ fst ya ∈ fst (lookup K γ) ⟩)
    → (ybK : ⟨ fst yb ∈ fst (lookup K γ) ⟩)
    → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         extAtB (suc (suc (suc zero)))
                (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) body₂ ⟩
    → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
         extAt (suc (suc zero)) body₁ ⟩
  opBack yb E ya yc b a ar c yaK ybK h =
      ( λ z z∈ → bwd z yb E ya yc b a ar c (h .fst z z∈) )
    , ( λ z hz → h .snd z (inK z yb E ya yc b a ar c yaK ybK
                            (fwd z yb E ya yc b a ar c hz))
                    (fwd z yb E ya yc b a ar c hz) )

  -- The row agreement.  The machine's clause at the class carrier.
  out : ⟨ γ ⊨ binClauseAt C T k (propRel T op₁) ⟩
      → ⟨ γ ⊨ binFullAt C T K (arTagPairB N K)
           subA (envHypB2 B K) (propBodyB T K op₂) ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA henv →
    λ yb ybK hsubB →
      let shD = BinaryShape.out {m} N K k (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                  tagEq shB
          hya' = SubValB2T.back {m = 7 + m}
                   (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K)))))))
                   (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                   (keyK₀ ar a arK aK)
                   (subst (λ ψ → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) subAEq hsubA)
          hyb' = PT.rec squash₁
            (λ { (z , (zK , (p , a₁))) →
              subB2T yb E ya yc b a ar c z zK (p , a₁) })
            hsubB
          hop = h c c∈ ar a b yc shD hc ya yb hya' hyb'
      in subst (λ ψ → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) (sym opEq₂)
           (opOut yb E ya yc b a ar c
             (subst (λ ψ → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) opEq₁ hop))

  back : ⟨ γ ⊨ binFullAt C T K (arTagPairB N K)
           subA (envHypB2 B K) (propBodyB T K op₂) ⟩
       → ⟨ γ ⊨ binClauseAt C T k (propRel T op₁) ⟩
  back h = λ c c∈ ar a b yc shD hc ya yb hya hyb →
    let shEq = transport (cong fst (arityTagPairAtL-adequate
                   (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                   (suc (suc zero)) (suc zero) (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K k (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        yaK = subK₁ yb ya yc b a ar c hya
        ybK = subK₀ yb ya yc b a ar c hyb
        (E , (EK , henvE)) = someEnv ya yc b a ar c yaK ycK arK
        hsubA' = SubValB2T.out {m = 7 + m}
                   (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc (suc zero))))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K)))))))
                   (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                   (keyK₀ ar a arK aK)
                   hya
        hsubA'' = subst (λ ψ → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) (sym subAEq) hsubA'
        hsubB' = subB2T-back yb E ya yc b a ar c (keyK ar b arK bK) hyb
        hbody = h c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA'' henvE
        hop = hbody yb ybK hsubB'
    in subst (λ ψ → ⟨ (yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) (sym opEq₁)
         (opBack yb E ya yc b a ar c yaK ybK
           (subst (λ ψ → ⟨ (yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ψ ⟩) opEq₂ hop))


module AndAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 2))
  (numK : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 2) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 2) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 2) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (keyK : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ ar a) ∈ fst (lookup K γ) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (subK₁ : (x y yc b a ar c : S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc zero))))
                         (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (subK₀ : (y ya yc b a ar c : S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc zero)))
                         zero ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (someEnv : (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → Σ S (λ E → ⟨ fst E ∈ fst (lookup K γ) ⟩
             × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {m} B K ⟩))
  where
  module P = PropAgree {m} C T B N K γ 2
    tagEq numK innerK pairK codesK valK keyK transK subK₁ subK₀ someEnv
    (And.subA {m} C T B N K)
    refl
    (interAt (suc (suc zero)) (suc zero) zero)
    (And.opA {m} C T B N K)
    ((var zero ∈̇ var (suc (suc zero))) ∧̇ (var zero ∈̇ var (suc zero)))
    ((var zero ∈̇ var (suc (suc (suc zero)))) ∧̇ (var zero ∈̇ var (suc zero)))
    refl refl
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c yaK ybK hz →
       transK z (lookup (suc (suc (suc zero))) (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))
         (hz .fst) yaK)
  open P public

-- The Or row: the PropAgree instantiation at tag 3 with union.

module OrAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 3))
  (numK : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 3) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 3) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 3) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (keyK : (ar a : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ ar a) ∈ fst (lookup K γ) ⟩)
  (transK : (x a : S) → ⟨ fst x ∈ fst a ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩)
  (subK₁ : (x y yc b a ar c : S)
           → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc zero))))
                         (suc zero) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (subK₀ : (y ya yc b a ar c : S)
           → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                subValAt {7 + m} (suc (suc (suc (suc (suc (suc (suc T)))))))
                         (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc zero)))
                         zero ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩)
  (someEnv : (ya yc b a ar c : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → Σ S (λ E → ⟨ fst E ∈ fst (lookup K γ) ⟩
             × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 {m} B K ⟩))
  where
  module P = PropAgree {m} C T B N K γ 3
    tagEq numK innerK pairK codesK valK keyK transK subK₁ subK₀ someEnv
    (Or.subO {m} C T B N K)
    refl
    (unionAt (suc (suc zero)) (suc zero) zero)
    (Or.opO {m} C T B N K)
    ((var zero ∈̇ var (suc (suc zero))) ∨̇ (var zero ∈̇ var (suc zero)))
    ((var zero ∈̇ var (suc (suc (suc zero)))) ∨̇ (var zero ∈̇ var (suc zero)))
    refl refl
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c x → x)
    (λ z yb E ya yc b a ar c yaK ybK hz →
       PT.rec (snd (fst z ∈ fst (lookup K γ)))
         (λ { (inl p) →
                transK z (lookup (suc (suc (suc zero)))
                  (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) p yaK
            ; (inr p) →
                transK z (lookup (suc zero)
                  (z ∷ yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) p ybK })
         hz)
  open P public


module TopAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 6))
  (numK : ⟨ fst (numeralL 6) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 6) a) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 6) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 6) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (envK : (yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc zero)))
                       (suc (suc (suc (suc (suc B))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc zero))))
                          (suc (suc (suc (suc (suc (suc B)))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  private
    φB : Formula S m
    φB = Top.topBndAt C T B N K

  body : Formula S (suc (5 + m))
  body = var zero ∈̇ var (suc zero)

  out : ⟨ γ ⊨ topClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK yc ycK shB hc E EK henv →
    let shD = UnaryShape.out {m} N K 6 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 6 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        arNum = codesK c ar a c∈ shEq .snd .snd
        module E' = EnvSet {5 + m} zero (suc (suc (suc zero)))
                       (suc (suc (suc (suc (suc B)))))
                       (suc (suc (suc (suc (suc K)))))
                       (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc a ar c E arK arNum)
        hE' = E'.out henv
        hbM = h c c∈ ar a yc shD hc E hE'
    in extAt→extAtB (suc zero) (suc (suc (suc (suc (suc K))))) body body
         (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (λ z x → x) (λ z x → x) hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ topClauseAt C T B ⟩
  back h = λ c c∈ ar a yc shD hc E hE →
    let shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 6 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , arNum)) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq (GraphEntry.un {m} T γ c ar a yc hc)
        shB = UnaryShape.in' {m} N K 6 (yc ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK aK shD
        EK = envK yc a ar c E arNum hE
        module E' = EnvSet {5 + m} zero (suc (suc (suc zero)))
                       (suc (suc (suc (suc (suc B)))))
                       (suc (suc (suc (suc (suc K)))))
                       (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc a ar c E arK arNum)
        henv = E'.back hE
        hb = h c c∈ ar arK a aK yc ycK shB hc E EK henv
    in extAtB→extAt (suc zero) (suc (suc (suc (suc (suc K))))) body body
         (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (λ z x → x) (λ z x → x)
         (λ z hz → E'.memE-bnd henv z hz) hb

-- The Neg row: machine negClauseAt against Neg.negBndAt.  The body is
-- diffB against diffAt, one OpTransfer (the same formula).

module NegAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 5))
  (numK : ⟨ fst (numeralL 5) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 5) a) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 5) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
         → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ pr (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
                (fst (lookup (suc (suc (suc zero))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValAt (suc (suc (suc (suc (suc (suc T))))))
                      (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero)))
                      (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (ya yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (ya yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  private
    φB : Formula S m
    φB = Neg.negBndAt C T B N K

  body : Formula S (suc (6 + m))
  body = (var zero ∈̇ var (suc zero)) ∧̇ ¬̇ (var zero ∈̇ var (suc (suc zero)))

  out : ⟨ γ ⊨ negClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv →
    let shD = UnaryShape.out {m} N K 5 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 5 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        arNum = codesK c ar a c∈ shEq .snd .snd
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        hE' = E'.out henv
        hya' = SubValB2T.back {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (keyK E ya yc a ar c arK aK) hsub
        hbM = h c c∈ ar a yc shD hc ya E hya' hE'
    in extAt→extAtB (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         body body (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (λ z x → x) (λ z x → x) hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ negClauseAt C T B ⟩
  back h = λ c c∈ ar a yc shD hc ya E hya hE →
    let shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 5 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , arNum)) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq (GraphEntry.un {m} T γ c ar a yc hc)
        shB = UnaryShape.in' {m} N K 5 (yc ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK aK shD
        yaK = subK ya yc a ar c E hya
        EK = envK ya yc a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        henv = E'.back hE
        hsub = SubValB2T.out {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (keyK E ya yc a ar c arK aK) hya
        hb = h c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv
    in extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         body body (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (λ z x → x) (λ z x → x)
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb


keyU : ∀ {m} (C T B N K : Fin m) (γ : S ^ m) (E ya yc a ar c : S) → Type (ℓ-suc ℓ)
keyU {m} C T B N K γ E ya yc a ar c =
  ⟨ pr (sucV (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ))))
       (fst (lookup (suc (suc (suc zero))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
       ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩


succU : ∀ {m} (C T B N K : Fin m) (γ : S ^ m) (E ya yc a ar c : S) → Type (ℓ-suc ℓ)
succU {m} C T B N K γ E ya yc a ar c =
  ⟨ sucV (fst (lookup (suc (suc (suc (suc zero)))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)))
       ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩

-- The Forall row: machine forallClauseAt against Forall.forallBndAt.

module ForallAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 9))
  (numK : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 9) a) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (succK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → succU {m} C T B N K γ E ya yc a ar c)
  (keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → keyU {m} C T B N K γ E ya yc a ar c)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (ya yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (ya yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc zero)) ⟩
          → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = Forall.forallBndAt C T B N K

    bodyFφ : Formula S (7 + m)
    bodyFφ = Forall.bodyFφ C T B N K

  out : ⟨ γ ⊨ forallClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv →
    let shD = UnaryShape.out {m} N K 9 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 9 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        arNum = codesK c ar a c∈ shEq .snd .snd
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        hE' = E'.out henv
        hya' = SubValSuccB2T.back {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (succK E ya yc a ar c arK)
                 (keyK E ya yc a ar c arK aK) hsub
        hbM = h c c∈ ar a yc shD hc ya E hya' hE'
    in extAt→extAtB (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         bodyFφ (body∀ B) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)
         (λ z hz → hz .fst
                 , (λ x xB e' hc → hz .snd x xB e'
                     (consK ya yc a ar c E z x e' hc) hc))
         (λ z hz → hz .fst , (λ x xB e' e'K → hz .snd x xB e'))
         hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ forallClauseAt C T B ⟩
  back h = λ c c∈ ar a yc shD hc ya E hya hE →
    let shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 9 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , arNum)) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq (GraphEntry.un {m} T γ c ar a yc hc)
        shB = UnaryShape.in' {m} N K 9 (yc ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK aK shD
        yaK = subK ya yc a ar c E hya
        EK = envK ya yc a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        henv = E'.back hE
        hsub = SubValSuccB2T.out {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (succK E ya yc a ar c arK)
                 (keyK E ya yc a ar c arK aK) hya
        hb = h c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv
    in extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         bodyFφ (body∀ B) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)
         (λ z hz → hz .fst
                 , (λ x xB e' hc → hz .snd x xB e'
                     (consK ya yc a ar c E z x e' hc) hc))
         (λ z hz → hz .fst , (λ x xB e' e'K → hz .snd x xB e'))
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

-- The Exist row: machine existClauseAt against Exist.existBndAt.

module ExistAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 8))
  (numK : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 8) a) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (succK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → succU {m} C T B N K γ E ya yc a ar c)
  (keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → keyU {m} C T B N K γ E ya yc a ar c)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (ya yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (ya yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc zero))
               ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
          → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = Exist.existBndAt C T B N K

    bodyE : Formula S (7 + m)
    bodyE = Exist.bodyE C T B N K

  -- The existential leaf transfer, generic in the row's environment
  -- elements.  The story's bodyE and the machine's body∃ read the
  -- SAME consAtL at the same environment; the only difference is the
  -- story's K-membership witness on the extended environment e'.  The
  -- K-membership is a site fact (consK); dropping it is free.  No
  -- transport along the adequacy is needed: both sides mention the
  -- identical consAtL formula, so the satisfactions at the inner point
  -- are definitionally the same type, and the transfer is two
  -- truncation lifts with written branch types (I-5).
  module Leaf (E ya yc a ar c : S) where
    -- The x-membership of the bounded quantifier, the K-membership of
    -- the extended environment, and the body content, at the body frame.
    xB : (z x : S) → Type (ℓ-suc ℓ)
    xB z x =
      ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc B)))))))
                        (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩

    bodyK : (z x e' : S) → Type (ℓ-suc ℓ)
    bodyK z x e' =
      ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                        (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩

    bodyC : (z x e' : S) → Type (ℓ-suc ℓ)
    bodyC z x e' =
      ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
          consAtL zero (suc zero) (suc (suc zero))
          ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩

    -- STORY TO MACHINE: drop the K-membership of the extended
    -- environment.  Written branch types, named (I-5).
    exist-drop-step : (z x : S) → Σ S (λ e' → bodyK z x e' × bodyC z x e')
                                → ∥ Σ S (λ e' → bodyC z x e') ∥₁
    exist-drop-step z x (e' , (e'K , hc)) = ∣ e' , hc ∣₁

    exist-drop : (z x : S)
               → ∥ Σ S (λ e' → bodyK z x e' × bodyC z x e') ∥₁
               → ∥ Σ S (λ e' → bodyC z x e') ∥₁
    exist-drop z x hx = PT.rec squash₁ (exist-drop-step z x) hx

    drop-x : (z : S)
           → Σ S (λ x → xB z x × ∥ Σ S (λ e' → bodyK z x e' × bodyC z x e') ∥₁)
           → ∥ Σ S (λ x → xB z x × ∥ Σ S (λ e' → bodyC z x e') ∥₁) ∥₁
    drop-x z (x , (x∈ , hx)) = ∣ x , (x∈ , exist-drop z x hx) ∣₁

    -- MACHINE TO STORY: add the K-membership from the site fact.
    exist-lift-step : (z x : S) → Σ S (λ e' → bodyC z x e')
                                → ∥ Σ S (λ e' → bodyK z x e' × bodyC z x e') ∥₁
    exist-lift-step z x (e' , hc) =
      ∣ e' , (consK ya yc a ar c E z x e' hc , hc) ∣₁

    exist-lift : (z x : S)
               → ∥ Σ S (λ e' → bodyC z x e') ∥₁
               → ∥ Σ S (λ e' → bodyK z x e' × bodyC z x e') ∥₁
    exist-lift z x hx = PT.rec squash₁ (exist-lift-step z x) hx

    lift-x : (z : S)
           → Σ S (λ x → xB z x × ∥ Σ S (λ e' → bodyC z x e') ∥₁)
           → ∥ Σ S (λ x → xB z x × ∥ Σ S (λ e' → bodyK z x e' × bodyC z x e') ∥₁) ∥₁
    lift-x z (x , (x∈ , hx)) = ∣ x , (x∈ , exist-lift z x hx) ∣₁

    fwd : (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyE ⟩
                  → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body∃ B ⟩
    fwd z h = h .fst , PT.rec squash₁ (drop-x z) (h .snd)

    bwd : (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body∃ B ⟩
                  → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyE ⟩
    bwd z h = h .fst , PT.rec squash₁ (lift-x z) (h .snd)

  -- The row agreement.  The machine's clause at the class carrier.
  out : ⟨ γ ⊨ existClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv →
    let shD = UnaryShape.out {m} N K 8 (yc ∷ a ∷ ar ∷ c ∷ γ)
                tagEq shB
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 8 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        arNum = codesK c ar a c∈ shEq .snd .snd
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        hE' = E'.out henv
        module L = Leaf E ya yc a ar c
        hya' = SubValSuccB2T.back {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (succK E ya yc a ar c arK)
                 (keyK E ya yc a ar c arK aK) hsub
        hbM = h c c∈ ar a yc shD hc ya E hya' hE'
    in extAt→extAtB (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         bodyE (body∃ B) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ existClauseAt C T B ⟩
  back h = λ c c∈ ar a yc shD hc ya E hya hE →
    let shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 8 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , arNum)) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq (GraphEntry.un {m} T γ c ar a yc hc)
        shB = UnaryShape.in' {m} N K 8 (yc ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK aK shD
        yaK = subK ya yc a ar c E hya
        EK = envK ya yc a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK ya yc a ar c E arK arNum)
        henv = E'.back hE
        module L = Leaf E ya yc a ar c
        hsub = SubValSuccB2T.out {m = 6 + m}
                 (suc (suc (suc (suc (suc (suc T))))))
                 (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (suc zero)
                 (suc (suc (suc (suc (suc (suc K))))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) (succK E ya yc a ar c arK)
                 (keyK E ya yc a ar c arK aK) hya
        hb = h c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv
    in extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc K))))))
         bodyE (body∃ B) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

-- Block 1's agreement: the machine's existClauseAt against the
-- Clause.existBndAt matrix.  After the subvalue repair (subValBnd
-- reads the key pr z₁ a, not pr a ya), Clause.existBndAt is
-- definitionally the Exist row's existBndAt at the class carrier:
-- shapeBnd is arTagB (suc N) zero, subValHyp is Exist.subE, envHyp is
-- envHypU (suc B) zero, and bodyBnd is Exist.bodyE.  So block 1 IS the
-- Exist row, and the agreement is one instantiation of ExistAgree.

module ClauseAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 8))
  (numK : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 8) a) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 8) (fst a))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (succK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → succU {m} C T B N K γ E ya yc a ar c)
  (keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
          → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → keyU {m} C T B N K γ E ya yc a ar c)
  (subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (ya yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (ya yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc zero))
               ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
          → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  module E = ExistAgree {m} C T B N K γ
    tagEq numK innerK arityK codesK valK succK keyK subK envK envInK consK

  out : ⟨ γ ⊨ existClauseAt C T B ⟩
      → ⟨ γ ⊨ Exist.existBndAt C T B N K ⟩
  out = E.out

  back : ⟨ γ ⊨ Exist.existBndAt C T B N K ⟩
       → ⟨ γ ⊨ existClauseAt C T B ⟩
  back = E.back

-- =====================================================================
-- THE ATOM LEAF TRANSFER (Mem and Eq rows).  The machine's atomBody
-- against the story's atomBodyB at the atom body frame
-- z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ.  The story bounds the two term
-- values v and w by K and uses the bounded tmValB; the machine leaves
-- them unbounded with tmValAt.  The transfer is two nested truncation
-- lifts (I-5), with the K-membership of v from the site fact valK.
-- =====================================================================

module AtomLeaf {m : ℕ} (E yc b a ar c₀ : S) (γ : S ^ m)
  (t0 t1 K : Fin m)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (bK : ⟨ fst b ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (valK : (z v w : S)
          → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
               tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc zero))
                       (suc zero) ⟩
          → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                            (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩)
  (valW : (z v w : S)
          → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
               tmValAt (suc (suc (suc (suc (suc zero)))))
                       (suc (suc zero))
                       zero ⟩
          → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩)
  (cmp : Formula S (9 + m)) where

  bodyS : Formula S (7 + m)
  bodyS = atomBodyB t0 t1 K cmp

  bodyM : Formula S (7 + m)
  bodyM = atomBody cmp

  module Z = ChainZ {m} K γ arityK

  -- THE DERIVATION: from the code slot's membership, arityK, and
  -- the tag satisfaction (the code at slot c is pr (# 1) k), the
  -- key's membership k ∈ K follows by the pair chain.  tmKeyK is
  -- not a telescope hypothesis: its tied form keyValK is refuted at
  -- the abstract frame ([LJ-1.104], ProbeLJ1104A:118-120).
  keyK-of : (z v w : S) (c : Fin (9 + m))
          → ⟨ fst (lookup c (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ))
              ∈ fst (lookup K γ) ⟩
          → (k : S)
          → ⟨ (k ∷ w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
               tagAtL (suc c) 1 zero ⟩
          → ⟨ fst k ∈ fst (lookup K γ) ⟩
  keyK-of z v w c cK k ht =
    let γ' : S ^ (9 + m)
        γ' = w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ
        tagEq : fst (lookup c γ') ≡ pr (# 1) (fst k)
        tagEq = transport (cong fst (tagAtL-adequate (suc c) 1 zero (k ∷ γ'))) ht
        pʟ : fst (prʟ (numeralL 1) k) ≡ pr (# 1) (fst k)
        pʟ = prʟ-fst (numeralL 1) k ∙ cong₂ pr (numeralL-fst 1) refl
        pℓ : fst (pairʟ (numeralL 1) k) ≡ ⁅ # 1 , fst k ⁆
        pℓ = pairʟ-fst (numeralL 1) k ∙ cong₂ ⁅_,_⁆ (numeralL-fst 1) refl
        pair∈K : ⟨ fst (prʟ (numeralL 1) k) ∈ fst (lookup K γ) ⟩
        pair∈K = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (tagEq ∙ sym pʟ) cK
    in arityK (pairʟ (numeralL 1) k) k
         (subst (λ w → ⟨ fst k ∈ w ⟩) (sym pℓ) (Z.b∈pair (# 1) (fst k)))
         (arityK (prʟ (numeralL 1) k) (pairʟ (numeralL 1) k)
           (subst (λ w → ⟨ fst (pairʟ (numeralL 1) k) ∈ w ⟩) (sym pʟ)
             (subst (λ w → ⟨ w ∈ pr (# 1) (fst k) ⟩) (sym pℓ)
               (Z.pair∈pr (# 1) (fst k))))
           pair∈K)

  -- The innermost satisfaction types at the frame.
  vK : (z v : S) → Type (ℓ-suc ℓ)
  vK z v =
    ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                      (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩

  wK : (z v w : S) → Type (ℓ-suc ℓ)
  wK z v w =
    ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                      (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ)) ⟩

  cSat : (z v w : S) → Type (ℓ-suc ℓ)
  cSat z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ cmp ⟩

  tVS : (z v w : S) → Type (ℓ-suc ℓ)
  tVS z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc (suc zero))))))
               (suc (suc zero))
               (suc zero)
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tWS : (z v w : S) → Type (ℓ-suc ℓ)
  tWS z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc zero)))))
               (suc (suc zero))
               zero
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tVM : (z v w : S) → Type (ℓ-suc ℓ)
  tVM z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                (suc (suc zero))
                (suc zero) ⟩

  tWM : (z v w : S) → Type (ℓ-suc ℓ)
  tWM z v w =
    ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc zero)))))
                (suc (suc zero))
                zero ⟩

  -- The tmVal transfers at the innermost frame, per witness pair.
  tmV-out : (z v w : S) → tVS z v w → tVM z v w
  tmV-out z v w =
    TmVal.out {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc zero))
      (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq

  tmW-out : (z v w : S) → tWS z v w → tWM z v w
  tmW-out z v w =
    TmVal.out {m = 9 + m}
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero))
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq

  tmV-in : (z v w : S) → tVM z v w → tVS z v w
  tmV-in z v w =
    TmVal.in' {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc (suc zero))
      (suc zero)
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z v w (suc (suc (suc (suc (suc (suc zero)))))) aK k ht)
      num1K

  tmW-in : (z v w : S) → tWM z v w → tWS z v w
  tmW-in z v w =
    TmVal.in' {m = 9 + m}
      (suc (suc (suc (suc (suc zero)))))
      (suc (suc zero))
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z v w (suc (suc (suc (suc (suc zero))))) bK k ht)
      num1K

  -- STORY TO MACHINE: drop the K-memberships and bound the witnesses.
  drop-w : (z v : S) → Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w)))
                     → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁
  drop-w z v (w , (wK , (hv , (hw , hc)))) =
    ∣ w , (tmV-out z v w hv , (tmW-out z v w hw , hc)) ∣₁

  drop-v : (z : S)
         → Σ S (λ v → vK z v × ∥ Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁)
         → ∥ Σ S (λ v → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁) ∥₁
  drop-v z (v , (vK , h)) = ∣ v , PT.rec squash₁ (drop-w z v) h ∣₁

  fwd : (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyS ⟩
                → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyM ⟩
  fwd z h = h .fst , PT.rec squash₁ (drop-v z) (h .snd)

  -- MACHINE TO STORY: add the K-memberships from the site facts.
  lift-w : (z v : S) → Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w))
                     → ∥ Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁
  lift-w z v (w , (hv , (hw , hc))) =
    ∣ w , ( valW z v w hw
          , ( tmV-in z v w hv , ( tmW-in z v w hw , hc ) ) ) ∣₁

  vK-lift : (z v : S)
          → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁
          → vK z v
  vK-lift z v h = PT.rec
    (snd (fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                          (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ))))
    (λ { (w , (hv , _)) → valK z v w hv }) h

  lift-v : (z : S)
         → Σ S (λ v → ∥ Σ S (λ w → tVM z v w × (tWM z v w × cSat z v w)) ∥₁)
         → ∥ Σ S (λ v → vK z v × ∥ Σ S (λ w → wK z v w × (tVS z v w × (tWS z v w × cSat z v w))) ∥₁) ∥₁
  lift-v z (v , h) = ∣ v , (vK-lift z v h , PT.rec squash₁ (lift-w z v) h) ∣₁

  bwd : (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyM ⟩
                → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c₀ ∷ γ) ⊨ bodyS ⟩
  bwd z h = h .fst , PT.rec squash₁ (lift-v z) (h .snd)

-- The Mem row: machine memClauseAt against Mem.memBndAt.

module MemAgree {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 0))
  (numK : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 0) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (envK : (yc b a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (yc b a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                           (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
         → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                           (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = Mem.memBndAt C T B N K t0 t1

    cmp : Formula S (9 + m)
    cmp = var (suc zero) ∈̇ var zero

  out : ⟨ γ ⊨ memClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc E EK henv →
    let shD = BinaryShape.out {m} N K 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq shB
        shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 0 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        arNum = codesK c ar a b c∈ shEq .snd .snd .snd
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc b a ar c E arK arNum)
        hE' = E'.out henv
        hbM = h c c∈ ar a b yc shD hc E hE'
        module L = AtomLeaf E yc b a ar c γ t0 t1 K
                     arityK aK bK t0eq t1eq t0K num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
    in extAt→extAtB (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ memClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc E hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 0 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K 0 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        EK = envK yc b a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc b a ar c E arK arNum)
        henv = E'.back hE
        module L = AtomLeaf E yc b a ar c γ t0 t1 K
                     arityK aK bK t0eq t1eq t0K num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
        hb = h c c∈ ar arK a aK b bK yc ycK shB hc E EK henv
    in extAtB→extAt (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb

-- =====================================================================
-- THE IMPLICATION LEAF (the Imp row).  The machine's impRel lives at
-- the environment E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (8 + n); the
-- story's binFullAt frame lives at E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ
-- (7 + n), and the story's propBodyB pushes yb, so the operation sits
-- at yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ.  The two layouts differ by
-- the swap of the first two slots.  The subvalue transfers cross the
-- insertion; the operation bodies read the same three sets, so the
-- operation transfer is definitional (the satisfaction types compute
-- to the same memberships).  The environment-set transfer crosses the
-- insertion by envOverAt-transport.
-- =====================================================================

module ImpLeaf {m : ℕ} (T B K : Fin m) (E yb ya yc b a ar c : S) (γ : S ^ m)
  (keyK : (x y : S) → ⟨ fst x ∈ fst (lookup K γ) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ x y) ∈ fst (lookup K γ) ⟩) where

  γm : S ^ (8 + m)
  γm = E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  γs : S ^ (7 + m)
  γs = E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  γb : S ^ (8 + m)
  γb = yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ

  -- The shared cores of the two subvalue formulas at the story envs,
  -- stated once in the machine's spelling (P-v).
  yaCore : Formula S (suc (7 + m))
  yaCore =
    prAtL zero (suc (suc (suc (suc (suc (suc zero))))))
              (suc (suc (suc (suc (suc zero)))))
    ∧̇ appAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
            zero (suc (suc zero))

  ybCore : Formula S (suc (8 + m))
  ybCore =
    prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
              (suc (suc (suc (suc (suc zero)))))
    ∧̇ appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
            zero (suc zero)

  -- The machine's ya-subvalue at γm against the story's subI at γs.
  -- STORY TO MACHINE: the bounded parts give the machine witness.
  yaBack : (z : S)
    → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K))))))) γs) ⟩
    → ⟨ (z ∷ γs) ⊨ yaCore ⟩
    → ⟨ γm ⊨ subValAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                       (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc (suc zero)))))
                       (suc (suc zero)) ⟩
  yaBack z zK (p , a₁) =
    let p' : ⟨ (z ∷ γm) ⊨ prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                      (suc (suc (suc (suc (suc (suc zero)))))) ⟩
        p' = subst ⟨_⟩
          (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc (suc zero))))))
                            (z ∷ γm)
           ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                            (suc (suc (suc (suc (suc zero)))))
                            (z ∷ γs)))
          p
        a₁' : ⟨ (z ∷ γm) ⊨ appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                                  zero (suc (suc (suc zero))) ⟩
        a₁' = subst ⟨_⟩
          (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                          zero (suc (suc (suc zero)))
                          (z ∷ γm)
           ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                          zero (suc (suc zero))
                          (z ∷ γs)))
          a₁
    in ∣ z , (p' , a₁') ∣₁

  -- MACHINE TO STORY: the machine witness gives the bounded parts,
  -- which are definitionally the bounded satisfaction.
  yaOut : ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
         → ⟨ γm ⊨ subValAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc zero)) ⟩
         → ∥ Σ S (λ z → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K))))))) γs) ⟩
                       × ⟨ (z ∷ γs) ⊨ yaCore ⟩) ∥₁
  yaOut arK aK h = PT.rec squash₁
    (λ { (z , (p , a₁)) →
      let p' : ⟨ (z ∷ γs) ⊨ prAtL zero (suc (suc (suc (suc (suc (suc zero))))))
                                        (suc (suc (suc (suc (suc zero))))) ⟩
          p' = subst ⟨_⟩
            (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                              (suc (suc (suc (suc (suc zero)))))
                              (z ∷ γs)
             ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                              (suc (suc (suc (suc (suc (suc zero))))))
                              (z ∷ γm)))
            p
          arS : S
          arS = lookup {n = 7 + m} (suc (suc (suc (suc (suc zero))))) γs
          aS : S
          aS = lookup {n = 7 + m} (suc (suc (suc (suc zero)))) γs
          zPath : fst z ≡ pr (fst arS) (fst aS)
          zPath = subst ⟨_⟩ (prAtL-adequate zero (suc (suc (suc (suc (suc (suc zero))))))
                            (suc (suc (suc (suc (suc zero)))))
                            (z ∷ γs)) p
          zK : ⟨ fst z ∈ fst (lookup {n = 7 + m} (suc (suc (suc (suc (suc (suc (suc K)))))))
                                γs) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup {n = 7 + m} (suc (suc (suc (suc (suc (suc (suc K)))))))
                                         γs) ⟩)
                 (sym zPath)
                 (subst (λ w → ⟨ w ∈ fst (lookup {n = 7 + m} (suc (suc (suc (suc (suc (suc (suc K)))))))
                                          γs) ⟩)
                   (prʟ-fst arS aS)
                   (keyK arS aS arK aK))
          a₁' : ⟨ (z ∷ γs) ⊨ appAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                                    zero (suc (suc zero)) ⟩
          a₁' = subst ⟨_⟩
            (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                            zero (suc (suc zero))
                            (z ∷ γs)
             ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                            zero (suc (suc (suc zero)))
                            (z ∷ γm)))
            a₁
      in ∣ z , (zK , (p' , a₁')) ∣₁ })
    h

  -- The machine's yb-subvalue at γm against the story's bounded
  -- yb-subvalue at γb.  STORY TO MACHINE: the bounded parts give the
  -- machine witness.
  ybBack : (z : S)
    → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) γb) ⟩
    → ⟨ (z ∷ γb) ⊨ ybCore ⟩
    → ⟨ γm ⊨ subValAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                       (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc zero))))
                       (suc zero) ⟩
  ybBack z zK (p , a₁) =
    let p' : ⟨ (z ∷ γm) ⊨ prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                      (suc (suc (suc (suc (suc zero))))) ⟩
        p' = subst ⟨_⟩
          (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero)))))
                            (z ∷ γm)
           ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero)))))
                            (z ∷ γb)))
          p
        a₁' : ⟨ (z ∷ γm) ⊨ appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                                  zero (suc (suc zero)) ⟩
        a₁' = subst ⟨_⟩
          (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                          zero (suc (suc zero))
                          (z ∷ γm)
           ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                          zero (suc zero)
                          (z ∷ γb)))
          a₁
    in ∣ z , (p' , a₁') ∣₁

  -- MACHINE TO STORY: the machine witness gives the bounded parts,
  -- which are definitionally the bounded satisfaction.
  ybOut : ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
         → ⟨ γm ⊨ subValAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
         → ∥ Σ S (λ z → ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) γb) ⟩
                       × ⟨ (z ∷ γb) ⊨ ybCore ⟩) ∥₁
  ybOut arK bK h = PT.rec squash₁
    (λ { (z , (p , a₁)) →
      let p' : ⟨ (z ∷ γb) ⊨ prAtL zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                        (suc (suc (suc (suc (suc zero))))) ⟩
          p' = subst ⟨_⟩
            (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                              (suc (suc (suc (suc (suc zero)))))
                              (z ∷ γb)
             ∙ sym (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                              (suc (suc (suc (suc (suc zero)))))
                              (z ∷ γm)))
            p
          arB : S
          arB = lookup {n = 8 + m} (suc (suc (suc (suc (suc (suc zero)))))) γb
          bB : S
          bB = lookup {n = 8 + m} (suc (suc (suc (suc zero)))) γb
          zPath : fst z ≡ pr (fst arB) (fst bB)
          zPath = subst ⟨_⟩ (prAtL-adequate zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (suc (suc (suc (suc (suc zero)))))
                            (z ∷ γb)) p
          zK : ⟨ fst z ∈ fst (lookup {n = 8 + m} (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                                γb) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup {n = 8 + m} (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                                         γb) ⟩)
                 (sym zPath)
                 (subst (λ w → ⟨ w ∈ fst (lookup {n = 8 + m} (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                                          γb) ⟩)
                   (prʟ-fst arB bB)
                   (keyK arB bB arK bK))
          a₁' : ⟨ (z ∷ γb) ⊨ appAt (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                                    zero (suc zero) ⟩
          a₁' = subst ⟨_⟩
            (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                            zero (suc zero)
                            (z ∷ γb)
             ∙ sym (appAt-adequate (suc (suc (suc (suc (suc (suc (suc (suc (suc T)))))))))
                            zero (suc (suc zero))
                            (z ∷ γm)))
            a₁
      in ∣ z , (zK , (p' , a₁')) ∣₁ })
    h

  -- The operation: machine implAt at γm against the story's implB at
  -- γb.  The bodies read the same three sets, so the transfer is
  -- definitional.
  opBodyM : Formula S (9 + m)
  opBodyM =
    (var zero ∈̇ var (suc zero))
    ∧̇ ((var zero ∈̇ var (suc (suc (suc zero))))
        ⇒̇ (var zero ∈̇ var (suc (suc zero))))

  opBodyS : Formula S (9 + m)
  opBodyS =
    (var zero ∈̇ var (suc (suc zero)))
    ∧̇ ((var zero ∈̇ var (suc (suc (suc zero))))
        ⇒̇ (var zero ∈̇ var (suc zero)))

  opOut : ⟨ γm ⊨ implAt (suc (suc (suc zero))) zero (suc (suc zero)) (suc zero) ⟩
        → ⟨ γb ⊨ implB (suc (suc (suc zero))) (suc zero) (suc (suc zero)) zero
                       (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) ⟩
  opOut h =
      (λ z z∈ → h .fst z z∈)
    , (λ z zK hz → h .snd z hz)

  opBack : ⟨ γb ⊨ implB (suc (suc (suc zero))) (suc zero) (suc (suc zero)) zero
                        (suc (suc (suc (suc (suc (suc (suc (suc K)))))))) ⟩
         → (inK : (z : S) → ⟨ (z ∷ γb) ⊨ opBodyS ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩)
         → ⟨ γm ⊨ implAt (suc (suc (suc zero))) zero (suc (suc zero)) (suc zero) ⟩
  opBack h inK =
      (λ z z∈ → h .fst z z∈)
    , (λ z hz → h .snd z (inK z hz) hz)

  -- The environment-set shift across the yb insertion: the machine's
  -- envSetAt at γm against the story's at γs, by envOverAt-transport.
  envShift-out : (z : S)
               → ⟨ (z ∷ γm) ⊨ envOverAt zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                          (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))) ⟩
               → ⟨ (z ∷ γs) ⊨ envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                                          (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
  envShift-out z =
    envOverAt-transport (z ∷ γm) (z ∷ γs)
      zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
           (suc (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))
      zero (suc (suc (suc (suc (suc (suc zero))))))
           (suc (suc (suc (suc (suc (suc (suc (suc B))))))))
      refl refl refl

  envShift-back : (z : S)
                → ⟨ (z ∷ γs) ⊨ envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                                           (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
                → ⟨ (z ∷ γm) ⊨ envOverAt zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                           (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))) ⟩
  envShift-back z =
    envOverAt-transport (z ∷ γs) (z ∷ γm)
      zero (suc (suc (suc (suc (suc (suc zero))))))
           (suc (suc (suc (suc (suc (suc (suc (suc B))))))))
      zero (suc (suc (suc (suc (suc (suc (suc zero)))))))
           (suc (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))
      refl refl refl

  envSet-out : ⟨ γm ⊨ envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                                  (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
             → ⟨ γs ⊨ envSetAt zero (suc (suc (suc (suc (suc zero)))))
                                  (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
  envSet-out h =
      (λ z z∈ → envShift-out z (h .fst z z∈))
    , (λ z hz → h .snd z (envShift-back z hz))

  envSet-back : ⟨ γs ⊨ envSetAt zero (suc (suc (suc (suc (suc zero)))))
                                  (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
              → ⟨ γm ⊨ envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                                  (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
  envSet-back h =
      (λ z z∈ → envShift-back z (h .fst z z∈))
    , (λ z hz → h .snd z (envShift-out z hz))

-- =====================================================================
-- THE BOUNDED-QUANTIFIER LEAF (AllIn and ExIn rows).  The machine's
-- bodyAll/bodyEx at the body frame z ∷ E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ
-- against the story's bounded bodies at z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷
-- c ∷ γ.  The two envs have the same slot structure and differ only in
-- the name at slot 2, which no leaf formula reads; the leaf formulas
-- are therefore the same types at the two envs.  The story bounds the
-- term value w and the extended environment e' by K and uses tmValB;
-- the machine leaves them unbounded with tmValAt.  The site facts give
-- the two K-memberships from the machine's witnesses.
-- =====================================================================

module BndLeaf {m : ℕ} (B t0 t1 K : Fin m) (E ya yc b a ar c : S) (γ : S ^ m)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
          → ⟨ fst N ∈ fst (lookup K γ) ⟩
          → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (aK : ⟨ fst a ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (wK : (z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                      tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                              (suc zero)
                              zero ⟩
      → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                        (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (consK : (z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
           → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
                             (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where

  bodyS : Formula S (8 + m)
  bodyS =
    (var zero ∈̇ var (suc zero))
    ∧̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
        (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ⇒̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))
            ((var zero ∈̇ var (suc zero))
            ⇒̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))
                (consAtL zero (suc zero) (suc (suc (suc zero)))
                ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero)))))))))

  bodyM : Formula S (8 + m)
  bodyM = bodyAll B

  module Z = ChainZ {m} K γ arityK

  -- THE DERIVATION, ported from AtomLeaf: from the code slot's
  -- membership (aK at the allin layout), arityK, and the tag
  -- satisfaction, the key's membership k ∈ K follows by the pair
  -- chain.  tmKeyK is not a telescope hypothesis: its tied form
  -- keyValK is refuted at the abstract frame ([LJ-1.104],
  -- ProbeLJ1104A:118-120).
  keyK-of : (z w : S) (c₀ : Fin (9 + m))
          → ⟨ fst (lookup c₀ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))
              ∈ fst (lookup K γ) ⟩
          → (k : S)
          → ⟨ (k ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               tagAtL (suc c₀) 1 zero ⟩
          → ⟨ fst k ∈ fst (lookup K γ) ⟩
  keyK-of z w c₀ cK k ht =
    let γ' : S ^ (9 + m)
        γ' = w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ
        tagEq : fst (lookup c₀ γ') ≡ pr (# 1) (fst k)
        tagEq = transport (cong fst (tagAtL-adequate (suc c₀) 1 zero (k ∷ γ'))) ht
        pʟ : fst (prʟ (numeralL 1) k) ≡ pr (# 1) (fst k)
        pʟ = prʟ-fst (numeralL 1) k ∙ cong₂ pr (numeralL-fst 1) refl
        pℓ : fst (pairʟ (numeralL 1) k) ≡ ⁅ # 1 , fst k ⁆
        pℓ = pairʟ-fst (numeralL 1) k ∙ cong₂ ⁅_,_⁆ (numeralL-fst 1) refl
        pair∈K : ⟨ fst (prʟ (numeralL 1) k) ∈ fst (lookup K γ) ⟩
        pair∈K = subst (λ w → ⟨ w ∈ fst (lookup K γ) ⟩) (tagEq ∙ sym pʟ) cK
    in arityK (pairʟ (numeralL 1) k) k
         (subst (λ w → ⟨ fst k ∈ w ⟩) (sym pℓ) (Z.b∈pair (# 1) (fst k)))
         (arityK (prʟ (numeralL 1) k) (pairʟ (numeralL 1) k)
           (subst (λ w → ⟨ fst (pairʟ (numeralL 1) k) ∈ w ⟩) (sym pʟ)
             (subst (λ w → ⟨ w ∈ pr (# 1) (fst k) ⟩) (sym pℓ)
               (Z.pair∈pr (# 1) (fst k))))
           pair∈K)

  -- The innermost satisfaction types at the frame.
  wK' : (z w : S) → Type (ℓ-suc ℓ)
  wK' z w =
    ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                      (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  xB : (z w x : S) → Type (ℓ-suc ℓ)
  xB z w x =
    ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))
                      (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  xW : (z w x : S) → Type (ℓ-suc ℓ)
  xW z w x = ⟨ fst x ∈ fst w ⟩

  eK : (z w x e' : S) → Type (ℓ-suc ℓ)
  eK z w x e' =
    ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
                      (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  cSat : (z w x e' : S) → Type (ℓ-suc ℓ)
  cSat z w x e' =
    ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
        consAtL zero (suc zero) (suc (suc (suc zero))) ⟩

  ySat : (z w x e' : S) → Type (ℓ-suc ℓ)
  ySat z w x e' =
    ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc zero)))))
                      (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩

  tVS : (z w : S) → Type (ℓ-suc ℓ)
  tVS z w =
    ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
        tmValB (suc (suc (suc (suc (suc (suc zero))))))
               (suc zero)
               zero
               (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
               (suc (suc (suc (suc (suc (suc (suc (suc (suc t1))))))))) ⟩

  tVM : (z w : S) → Type (ℓ-suc ℓ)
  tVM z w =
    ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
        tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero ⟩

  tmOut : (z w : S) → tVS z w → tVM z w
  tmOut z w =
    TmVal.out {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc zero)
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) t0eq t1eq

  tmIn : (z w : S) → tVM z w → tVS z w
  tmIn z w =
    TmVal.in' {m = 9 + m}
      (suc (suc (suc (suc (suc (suc zero))))))
      (suc zero)
      zero
      (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
      (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
      (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) t0eq t1eq t0K
      (λ k ht → keyK-of z w (suc (suc (suc (suc (suc (suc zero)))))) aK k ht) num1K

  -- THE UNIVERSAL SHAPE (AllIn): no truncation.
  all-fwd : (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyS ⟩
                    → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyM ⟩
  all-fwd z h = h .fst , (λ w tmAt x x∈B x∈w e' cons →
    h .snd w (wK z w tmAt) (tmIn z w tmAt) x x∈B x∈w e' (consK z w x e' cons) cons)

  all-bwd : (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyM ⟩
                    → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyS ⟩
  all-bwd z h = h .fst , (λ w wK' tmB x x∈B x∈w e' e'K cons →
    h .snd w (tmOut z w tmB) x x∈B x∈w e' cons)

  -- THE EXISTENTIAL SHAPE (ExIn): three nested truncations, with
  -- written branch types (I-5).
  bodySx : Formula S (8 + m)
  bodySx =
    (var zero ∈̇ var (suc zero))
    ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
        (tmValB (suc (suc (suc (suc (suc (suc zero))))))
                (suc zero)
                zero
                (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t0)))))))))
                (suc (suc (suc (suc (suc (suc (suc (suc (suc t1)))))))))
        ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc B))))))))))
            ((var zero ∈̇ var (suc zero))
            ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K)))))))))))
                (consAtL zero (suc zero) (suc (suc (suc zero)))
                ∧̇ (var zero ∈̇ var (suc (suc (suc (suc (suc zero)))))))))

  bodyMx : Formula S (8 + m)
  bodyMx = bodyEx B

  ex-drop-e : (z w x : S) → Σ S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e'))
                          → ∥ Σ S (λ e' → cSat z w x e' × ySat z w x e') ∥₁
  ex-drop-e z w x (e' , (eK , (c , y))) = ∣ e' , (c , y) ∣₁

  ex-drop-x : (z w : S) → Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁))
                       → ∥ Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → cSat z w x e' × ySat z w x e') ∥₁)) ∥₁
  ex-drop-x z w (x , (x∈B , (x∈w , h))) = ∣ x , (x∈B , (x∈w , PT.rec squash₁ (ex-drop-e z w x) h)) ∣₁

  ex-drop-w : (z : S) → Σ S (λ w → wK' z w × (tVS z w × ∥ Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁)) ∥₁))
                      → ∥ Σ S (λ w → tVM z w × ∥ Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → cSat z w x e' × ySat z w x e') ∥₁)) ∥₁) ∥₁
  ex-drop-w z (w , (wK , (h , hx))) =
    ∣ w , (tmOut z w h , PT.rec squash₁ (ex-drop-x z w) hx) ∣₁

  ex-fwd : (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodySx ⟩
                   → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyMx ⟩
  ex-fwd z h = h .fst , PT.rec squash₁ (ex-drop-w z) (h .snd)

  ex-lift-e : (z w x : S) → Σ S (λ e' → cSat z w x e' × ySat z w x e')
                          → ∥ Σ S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁
  ex-lift-e z w x (e' , (c , y)) = ∣ e' , (consK z w x e' c , (c , y)) ∣₁

  ex-lift-x : (z w : S) → Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → cSat z w x e' × ySat z w x e') ∥₁))
                       → ∥ Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁)) ∥₁
  ex-lift-x z w (x , (x∈B , (x∈w , h))) = ∣ x , (x∈B , (x∈w , PT.rec squash₁ (ex-lift-e z w x) h)) ∣₁

  ex-lift-w : (z : S) → Σ S (λ w → tVM z w × ∥ Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → cSat z w x e' × ySat z w x e') ∥₁)) ∥₁)
                      → ∥ Σ S (λ w → wK' z w × (tVS z w × ∥ Σ S (λ x → xB z w x × (xW z w x × ∥ Σ S (λ e' → eK z w x e' × (cSat z w x e' × ySat z w x e')) ∥₁)) ∥₁)) ∥₁
  ex-lift-w z (w , (h , hx)) =
    ∣ w , (wK z w h , (tmIn z w h , PT.rec squash₁ (ex-lift-x z w) hx)) ∣₁

  ex-bwd : (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyMx ⟩
                   → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodySx ⟩
  ex-bwd z h = h .fst , PT.rec squash₁ (ex-lift-w z) (h .snd)

-- The AllIn row: machine allInClauseAt against AllIn.allInBndAt.

module AllInAgree {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 10))
  (numK : ⟨ fst (numeralL 10) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 10) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 10) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 10) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (succK : (E ya yc b a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨
             sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (keyK : (E ya yc b a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩ → ⟨
             pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))))
                (fst (lookup (suc (suc (suc zero)))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (subK : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc (suc T)))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (E ya yc b a ar c : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (E ya yc b a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
          → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (consK : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
          → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
                            (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = AllIn.allInBndAt C T B N K t0 t1

  out : ⟨ γ ⊨ allInClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA henv →
      let shD = BinaryShape.out {m} N K 10 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                  tagEq shB
          shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 10 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
          arNum = codesK c ar a b c∈ shEq .snd .snd .snd
          module E' = EnvSet {7 + m} zero (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc (suc (suc (suc B)))))))
                         (suc (suc (suc (suc (suc (suc (suc K)))))))
                         (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                         (envInK E ya yc b a ar c arK arNum)
          module L = BndLeaf B t0 t1 K E ya yc b a ar c γ
                       t0eq t1eq t0K arityK aK num1K (wKfact E ya yc b a ar c) (consK E ya yc b a ar c)
          hE' = E'.out henv
          hya' = SubValSuccB2T.back {m = 7 + m}
                   (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc zero)))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K)))))))
                   (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) (succK E ya yc b a ar c arK)
                   (keyK E ya yc b a ar c arK bK) hsubA
          hbM = h c c∈ ar a b yc shD hc ya E hya' hE'
      in extAt→extAtB (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc K)))))))
           L.bodyS L.bodyM (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.all-fwd L.all-bwd hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ allInClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc yb E hb hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 10 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K 10 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        yaK = subK E yb yc b a ar c hb
        EK = envK E yb yc b a ar c arNum hE
        module E' = EnvSet {7 + m} zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc B)))))))
                       (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK E yb yc b a ar c arK arNum)
        module L = BndLeaf B t0 t1 K E yb yc b a ar c γ
                     t0eq t1eq t0K arityK aK num1K (wKfact E yb yc b a ar c) (consK E yb yc b a ar c)
        henv = E'.back hE
        hsubA = SubValSuccB2T.out {m = 7 + m}
                  (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc K)))))))
                  (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) (succK E yb yc b a ar c arK)
                  (keyK E yb yc b a ar c arK bK) hb
        hb' = h c c∈ ar arK a aK b bK yc ycK shB hc yb yaK E EK hsubA henv
    in extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc K)))))))
         L.bodyS L.bodyM (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.all-fwd L.all-bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb'




module ExInAgree {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 11))
  (numK : ⟨ fst (numeralL 11) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 11) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 11) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 11) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (succK : (E ya yc b a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨
             sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (keyK : (E ya yc b a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
         → ⟨ fst b ∈ fst (lookup K γ) ⟩ → ⟨
             pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                            (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))))
                (fst (lookup (suc (suc (suc zero)))
                        (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)))
             ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (subK : (E ya yc b a ar c : S) → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             subValSuccAt (suc (suc (suc (suc (suc (suc (suc T)))))))
                          (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (envK : (E ya yc b a ar c : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (E ya yc b a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (wKfact : (E ya yc b a ar c z w : S) → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                      (suc zero)
                      zero ⟩
          → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                            (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (consK : (E ya yc b a ar c z w x e' : S) → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
          → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc K))))))))))
                            (x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = ExIn.exInBndAt C T B N K t0 t1

  out : ⟨ γ ⊨ exInClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA henv →
      let shD = BinaryShape.out {m} N K 11 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                  tagEq shB
          shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 11 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
          arNum = codesK c ar a b c∈ shEq .snd .snd .snd
          module E' = EnvSet {7 + m} zero (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc (suc (suc (suc B)))))))
                         (suc (suc (suc (suc (suc (suc (suc K)))))))
                         (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                         (envInK E ya yc b a ar c arK arNum)
          module L = BndLeaf B t0 t1 K E ya yc b a ar c γ
                       t0eq t1eq t0K arityK aK num1K (wKfact E ya yc b a ar c) (consK E ya yc b a ar c)
          hE' = E'.out henv
          hya' = SubValSuccB2T.back {m = 7 + m}
                   (suc (suc (suc (suc (suc (suc (suc T)))))))
                   (suc (suc (suc (suc (suc zero)))))
                   (suc (suc (suc zero)))
                   (suc zero)
                   (suc (suc (suc (suc (suc (suc (suc K)))))))
                   (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) (succK E ya yc b a ar c arK)
                   (keyK E ya yc b a ar c arK bK) hsubA
          hbM = h c c∈ ar a b yc shD hc ya E hya' hE'
      in extAt→extAtB (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc K)))))))
           L.bodySx L.bodyMx (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.ex-fwd L.ex-bwd hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ exInClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc yb E hb hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 11 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K 11 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        yaK = subK E yb yc b a ar c hb
        EK = envK E yb yc b a ar c arNum hE
        module E' = EnvSet {7 + m} zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc B)))))))
                       (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK E yb yc b a ar c arK arNum)
        module L = BndLeaf B t0 t1 K E yb yc b a ar c γ
                     t0eq t1eq t0K arityK aK num1K (wKfact E yb yc b a ar c) (consK E yb yc b a ar c)
        henv = E'.back hE
        hsubA = SubValSuccB2T.out {m = 7 + m}
                  (suc (suc (suc (suc (suc (suc (suc T)))))))
                  (suc (suc (suc (suc (suc zero)))))
                  (suc (suc (suc zero)))
                  (suc zero)
                  (suc (suc (suc (suc (suc (suc (suc K)))))))
                  (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) (succK E yb yc b a ar c arK)
                  (keyK E yb yc b a ar c arK bK) hb
        hb' = h c c∈ ar arK a aK b bK yc ycK shB hc yb yaK E EK hsubA henv
    in extAtB→extAt (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc K)))))))
         L.bodySx L.bodyMx (E ∷ yb ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.ex-fwd L.ex-bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb'

-- The Imp row: machine impClauseAt against Imp.impBndAt.

module ImpAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 4))
  (numK : ⟨ fst (numeralL 4) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 4) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 4) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 4) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (keyK : (x y : S) → ⟨ fst x ∈ fst (lookup K γ) ⟩ → ⟨ fst y ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ x y) ∈ fst (lookup K γ) ⟩)
  (subK₁ : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              subValAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                       (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc (suc zero)))))
                       (suc (suc zero)) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩)
  (subK₀ : (E yb ya yc b a ar c : S) → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
              subValAt (suc (suc (suc (suc (suc (suc (suc (suc T))))))))
                       (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc zero))))
                       (suc zero) ⟩ → ⟨ fst yb ∈ fst (lookup K γ) ⟩)
  (envK : (E yb ya yc b a ar c : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc (suc (suc zero))))))
                       (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (E ya yc b a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc (suc zero))))))
                          (suc (suc (suc (suc (suc (suc (suc (suc B)))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  where
  private
    φB : Formula S m
    φB = Imp.impBndAt C T B N K

    opI : Formula S (8 + m)
    opI = Imp.opI C T B N K

  out : ⟨ γ ⊨ impClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA henv →
    λ yb ybK hsubB →
      let shD = BinaryShape.out {m} N K 4 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                  tagEq shB
          shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 4 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
          arNum = codesK c ar a b c∈ shEq .snd .snd .snd
          module E' = EnvSet {7 + m} zero (suc (suc (suc (suc (suc zero)))))
                         (suc (suc (suc (suc (suc (suc (suc B)))))))
                         (suc (suc (suc (suc (suc (suc (suc K)))))))
                         (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                         (envInK E ya yc b a ar c arK arNum)
          module L = ImpLeaf T B K E yb ya yc b a ar c γ keyK
          hE' = E'.out henv
          hE'' = L.envSet-back hE'
          hya' = PT.rec squash₁
            (λ { (z , (zK , (p , a₁))) → L.yaBack z zK (p , a₁) }) hsubA
          hyb' = PT.rec squash₁
            (λ { (z , (zK , (p , a₁))) → L.ybBack z zK (p , a₁) }) hsubB
          hopM = h c c∈ ar a b yc shD hc ya yb E hya' hyb' hE''
      in L.opOut hopM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ impClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc ya yb E ha hb hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 4 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K 4 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        yaK = subK₁ E yb ya yc b a ar c ha
        ybK = subK₀ E yb ya yc b a ar c hb
        EK = envK E yb ya yc b a ar c arNum hE
        module E' = EnvSet {7 + m} zero (suc (suc (suc (suc (suc zero)))))
                       (suc (suc (suc (suc (suc (suc (suc B)))))))
                       (suc (suc (suc (suc (suc (suc (suc K)))))))
                       (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK E ya yc b a ar c arK arNum)
        module L = ImpLeaf T B K E yb ya yc b a ar c γ keyK
        henv = E'.back (L.envSet-out hE)
        hsubA = L.yaOut arK aK ha
        hsubB = L.ybOut arK bK hb
        hb' = h c c∈ ar arK a aK b bK yc ycK shB hc ya yaK E EK hsubA henv
        hopB = hb' yb ybK hsubB
    in L.opBack hopB (λ z hz → E'.memE-bnd henv z (hz .fst))


-- The Eq row: machine eqClauseAt against Eq.eqBndAt.

module EqAgree {m : ℕ} (C T B N K t0 t1 : Fin m) (γ : S ^ m)
  (tagEq : fst (lookup N γ) ≡ fst (numeralL 1))
  (numK : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL 1) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
           → ⟨ fst N ∈ fst (lookup K γ) ⟩
           → ⟨ fst v ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 1) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (valK : (c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 1) (pr (fst a) (fst b)))
         → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
         → ⟨ fst yc ∈ fst (lookup K γ) ⟩)
  (t0eq : fst (lookup t0 γ) ≡ fst (numeralL 0))
  (t1eq : fst (lookup t1 γ) ≡ fst (numeralL 1))
  (t0K : ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩)
  (num1K : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩)
  (envK : (yc b a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
         → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             envSetAt zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B)))))) ⟩
         → ⟨ fst E ∈ fst (lookup K γ) ⟩)
  (envInK : (yc b a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → (z : S) → ⟨ (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envOverAt zero (suc (suc (suc (suc (suc zero)))))
                          (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
           → ⟨ fst z ∈ fst (lookup K γ) ⟩)
  (valV : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc K)))))))
                           (z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  (valW : (E yc b a ar c z v w : S) → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
         → ⟨ fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                           (v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ⟩)
  where
  private
    φB : Formula S m
    φB = Eq.eqBndAt C T B N K t0 t1

    cmp : Formula S (9 + m)
    cmp = var (suc zero) ≐ var zero

  out : ⟨ γ ⊨ eqClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
  out h = λ c c∈ ar arK a aK b bK yc ycK shB hc E EK henv →
    let shD = BinaryShape.out {m} N K 1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq shB
        shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 1 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        arNum = codesK c ar a b c∈ shEq .snd .snd .snd
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc b a ar c E arK arNum)
        hE' = E'.out henv
        hbM = h c c∈ ar a b yc shD hc E hE'
        module L = AtomLeaf E yc b a ar c γ t0 t1 K
                     arityK aK bK t0eq t1eq t0K num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
    in extAt→extAtB (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd hbM

  back : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ eqClauseAt C T B ⟩
  back h = λ c c∈ ar a b yc shD hc E hE →
    let shEq = transport (cong fst (arityTagPairAtL-adequate (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero))) 1 (suc (suc zero)) (suc zero)
                   (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , (aK , (bK , arNum))) = codesK c ar a b c∈ shEq
        ycK = valK c ar a b yc c∈ shEq (GraphEntry.bin {m} T γ c ar a b yc hc)
        shB = BinaryShape.in' {m} N K 1 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
                tagEq numK innerK pairK aK bK shD
        EK = envK yc b a ar c E arNum hE
        module E' = EnvSet {6 + m} zero (suc (suc (suc (suc zero))))
                       (suc (suc (suc (suc (suc (suc B))))))
                       (suc (suc (suc (suc (suc (suc K))))))
                       (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) arityK EK arK
                       (envInK yc b a ar c E arK arNum)
        henv = E'.back hE
        module L = AtomLeaf E yc b a ar c γ t0 t1 K
                     arityK aK bK t0eq t1eq t0K num1K (valV E yc b a ar c) (valW E yc b a ar c) cmp
        hb = h c c∈ ar arK a aK b bK yc ycK shB hc E EK henv
    in extAtB→extAt (suc zero) (suc (suc (suc (suc (suc (suc K))))))
         L.bodyS L.bodyM (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) L.fwd L.bwd
         (λ z hz → E'.memE-bnd henv z (hz .fst)) hb


module UnShapeClosed {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (3 + m))
  (tagEq : fst (lookup (suc (suc (suc tag))) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
           → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩) where

  out : ⟨ γ ⊨ arTagBS tag K ⟩
      → ⟨ γ ⊨ arityTagAtL (suc (suc zero)) (suc zero) k zero ⟩
  out h = transport (cong fst (sym (arityTagAtL-adequate (suc (suc zero))
             (suc zero) k zero γ))) target
    where
    target : fst (lookup (suc (suc zero)) γ)
           ≡ pr (fst (lookup (suc zero) γ)) (pr (# k) (fst (lookup zero γ)))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , (tp , zt))) →
          let ar₀ = fst (lookup (suc zero) γ)
              a₀ = fst (lookup zero γ)
              p' : fst (lookup (suc (suc (suc zero))) (z ∷ γ))
                  ≡ pr (fst (lookup (suc (suc zero)) (z ∷ γ)))
                       (fst (lookup zero (z ∷ γ)))
              p' = transport (cong fst (prAtL-adequate (suc (suc (suc zero)))
                    (suc (suc zero)) zero (z ∷ γ))) p
              zt' : fst (lookup (suc zero) (t ∷ z ∷ γ))
                   ≡ pr (fst (lookup zero (t ∷ z ∷ γ)))
                        (fst (lookup (suc (suc zero)) (t ∷ z ∷ γ)))
              zt' = transport (cong fst (prAtL-adequate (suc zero) zero
                    (suc (suc zero)) (t ∷ z ∷ γ))) zt
              tp' : fst (lookup zero (t ∷ z ∷ γ))
                  ≡ fst (lookup (suc (suc (suc tag))) γ)
              tp' = tp
          in p' ∙ cong (pr ar₀) zt'
               ∙ cong (λ v → pr ar₀ (pr v a₀))
                      (tp' ∙ tagEq ∙ numeralL-fst k) })
        kz })
      h

  in' : ⟨ fst (lookup zero γ) ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
      → ⟨ γ ⊨ arityTagAtL (suc (suc zero)) (suc zero) k zero ⟩
      → ⟨ γ ⊨ arTagBS tag K ⟩
  in' a₀K h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let p' : fst (lookup (suc (suc (suc zero))) (z ∷ γ))
              ≡ pr (fst (lookup (suc (suc zero)) (z ∷ γ)))
                   (fst (lookup zero (z ∷ γ)))
          p' = transport (cong fst (prAtL-adequate (suc (suc (suc zero)))
                (suc (suc zero)) zero (z ∷ γ))) p
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (fst (lookup (suc zero) (z ∷ γ)))
          tz' = transport (cong fst (tagAtL-adequate zero k (suc zero) (z ∷ γ))) tz
          a₀ : S
          a₀ = lookup zero γ
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc K))) γ) ⟩)
                   (prʟ-fst (numeralL k) a₀ ∙ cong₂ pr (numeralL-fst k) refl)
                   (innerK a₀ (a₀K)))
          zt : ⟨ (numeralL k ∷ z ∷ γ) ⊨ prAtL (suc zero) zero (suc (suc zero)) ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc zero) zero
                 (suc (suc zero)) (numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k)) refl)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( numK
                     , ( sym tagEq
                       , zt ) )
                   ∣₁ ) ) ∣₁ })
    h


module BinShapeClosed {m : ℕ} (tag K : Fin m) (k : ℕ) (γ : S ^ (4 + m))
  (tagEq : fst (lookup (suc (suc (suc (suc tag)))) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
           → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
           → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
           → ⟨ fst b ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

  out : ⟨ γ ⊨ arTagPairBS tag K ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero ⟩
  out h = transport (cong fst (sym (arityTagPairAtL-adequate (suc (suc (suc zero)))
             (suc (suc zero)) k (suc zero) zero γ))) target
    where
    target : fst (lookup (suc (suc (suc zero))) γ)
           ≡ pr (fst (lookup (suc (suc zero)) γ))
                (pr (# k) (pr (fst (lookup (suc zero) γ)) (fst (lookup zero γ))))
    target = PT.rec (setIsSet _ _)
      (λ { (z , (z∈ , (p , kz))) → PT.rec (setIsSet _ _)
        (λ { (t , (t∈ , kt)) → PT.rec (setIsSet _ _)
          (λ { (w , (w∈ , (tp , (zt , wb)))) →
            let ar₀ = fst (lookup (suc (suc zero)) γ)
                p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
                    ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                         (fst (lookup zero (z ∷ γ)))
                p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero))) zero (z ∷ γ))) p
                zt' : fst (lookup (suc (suc zero)) (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup zero (w ∷ t ∷ z ∷ γ)))
                zt' = transport (cong fst (prAtL-adequate (suc (suc zero)) (suc zero) zero
                      (w ∷ t ∷ z ∷ γ))) zt
                wb' : fst (lookup zero (w ∷ t ∷ z ∷ γ))
                     ≡ pr (fst (lookup (suc (suc (suc (suc zero)))) (w ∷ t ∷ z ∷ γ)))
                          (fst (lookup (suc (suc (suc zero))) (w ∷ t ∷ z ∷ γ)))
                wb' = transport (cong fst (prAtL-adequate zero (suc (suc (suc (suc zero))))
                      (suc (suc (suc zero))) (w ∷ t ∷ z ∷ γ))) wb
                tp' : fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ))
                    ≡ fst (lookup (suc (suc (suc (suc tag)))) γ)
                tp' = tp
            in p' ∙ cong (pr ar₀) (zt' ∙ cong (pr (fst (lookup (suc zero) (w ∷ t ∷ z ∷ γ)))) wb')
                 ∙ cong (λ v → pr ar₀ (pr v (pr (fst (lookup (suc zero) γ)) (fst (lookup zero γ)))))
                        (tp' ∙ tagEq ∙ numeralL-fst k) })
          kt })
        kz })
      h

  in' : ⟨ fst (lookup (suc zero) γ) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
      → ⟨ fst (lookup zero γ) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero ⟩
      → ⟨ γ ⊨ arTagPairBS tag K ⟩
  in' a₀K b₀K h = PT.rec squash₁
    (λ { (z , (p , tz)) →
      let p' : fst (lookup (suc (suc (suc (suc zero)))) (z ∷ γ))
              ≡ pr (fst (lookup (suc (suc (suc zero))) (z ∷ γ)))
                   (fst (lookup zero (z ∷ γ)))
          p' = transport (cong fst (prAtL-adequate (suc (suc (suc (suc zero))))
                (suc (suc (suc zero))) zero (z ∷ γ))) p
          tz' : fst (lookup zero (z ∷ γ))
               ≡ pr (# k) (pr (fst (lookup (suc (suc zero)) (z ∷ γ)))
                              (fst (lookup (suc zero) (z ∷ γ))))
          tz' = transport (cong fst (tagPairAtL-adequate zero k (suc (suc zero))
                (suc zero) (z ∷ γ))) tz
          a₀ : S
          a₀ = lookup (suc zero) γ
          b₀ : S
          b₀ = lookup zero γ
          zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
          zK = subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                 (sym tz')
                 (subst (λ w → ⟨ w ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
                   (prʟ-fst (numeralL k) (prʟ a₀ b₀)
                    ∙ cong₂ pr (numeralL-fst k) (prʟ-fst a₀ b₀))
                   (innerK a₀ b₀ a₀K b₀K))
          zt : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
          zt = transport (cong fst (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (tz' ∙ cong₂ pr (sym (numeralL-fst k)) (sym (prʟ-fst a₀ b₀)))
          wb : ⟨ (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ)
                  ⊨ prAtL zero (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero))) ⟩
          wb = transport (cong fst (sym (prAtL-adequate zero (suc (suc (suc (suc zero))))
                 (suc (suc (suc zero)))
                 (prʟ a₀ b₀ ∷ numeralL k ∷ z ∷ γ))))
               (prʟ-fst a₀ b₀)
      in ∣ z , ( zK
               , ( p
                 , ∣ numeralL k
                   , ( numK
                     , ∣ prʟ a₀ b₀
                       , ( pairK a₀ b₀ a₀K b₀K
                         , ( sym tagEq , ( zt , wb ) ) )
                       ∣₁ )
                   ∣₁ ) ) ∣₁ })
    h


module TmBranch {m : ℕ} (t : Fin (4 + m)) (tag : Fin m) (k : ℕ)
  (x : Fin (4 + m)) (K : Fin m) (γ : S ^ (4 + m))
  (tagEq : fst (lookup (suc (suc (suc (suc tag)))) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (inK : (v : S) → ⟨ fst v ∈ fst (lookup x γ) ⟩
         → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

  story : Formula S (4 + m)
  story = ∃̇∈ (var (suc (suc (suc (suc K)))))
            (tagBS (suc t) (suc (suc (suc (suc (suc tag))))) zero
                   (suc (suc (suc (suc (suc K)))))
            ∧̇ (var zero ∈̇ var (suc x)))

  machine : Formula S (4 + m)
  machine = ∃̇ (tagAtL (suc t) k zero ∧̇ (var zero ∈̇ var (suc x)))

  out : ⟨ γ ⊨ story ⟩ → ⟨ γ ⊨ machine ⟩
  out h = PT.rec squash₁ go h
    where
    go : Σ[ v ∈ S ] (⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
                    × ⟨ (v ∷ γ) ⊨ tagBS (suc t) (suc (suc (suc (suc (suc tag))))) zero
                                        (suc (suc (suc (suc (suc K)))))
                         ∧̇ (var zero ∈̇ var (suc x)) ⟩)
       → ⟨ γ ⊨ machine ⟩
    go (v , (vK , (hTag , vx))) = ∣ v , ( tagAt , vx ) ∣₁
      where
      tagAt : ⟨ (v ∷ γ) ⊨ tagAtL (suc t) k zero ⟩
      tagAt = transport (cong fst (sym (tagAtL-adequate {5 + m} (suc t) k zero (v ∷ γ))))
        (PT.rec (setIsSet _ _)
          (λ { (z , (zK , (ze , zp))) →
            let zp' : fst (lookup (suc (suc t)) (z ∷ v ∷ γ))
                     ≡ pr (fst (lookup zero (z ∷ v ∷ γ)))
                          (fst (lookup (suc zero) (z ∷ v ∷ γ)))
                zp' = transport (cong fst (prAtL-adequate (suc (suc t)) zero
                      (suc zero) (z ∷ v ∷ γ))) zp
            in zp' ∙ cong (λ w → pr w (fst (lookup (suc zero) (z ∷ v ∷ γ))))
                         (ze ∙ tagEq ∙ numeralL-fst k) })
          hTag)

  in' : ⟨ γ ⊨ machine ⟩ → ⟨ γ ⊨ story ⟩
  in' h = PT.rec squash₁ go h
    where
    go : Σ[ v ∈ S ] ⟨ (v ∷ γ) ⊨ tagAtL (suc t) k zero
                         ∧̇ (var zero ∈̇ var (suc x)) ⟩
       → ⟨ γ ⊨ story ⟩
    go (v , (hTag , vx)) = ∣ v , ( inK v vx-raw , ( hTagB , vx ) ) ∣₁
      where
      vx-raw : ⟨ fst v ∈ fst (lookup x γ) ⟩
      vx-raw = vx
      hTagB : ⟨ (v ∷ γ) ⊨ tagBS (suc t) (suc (suc (suc (suc (suc tag))))) zero
                                  (suc (suc (suc (suc (suc K))))) ⟩
      hTagB = ∣ numeralL k , ( numK , ( sym tagEq , tagPart ) ) ∣₁
        where
        tz' : fst (lookup (suc t) (v ∷ γ)) ≡ pr (# k) (fst (lookup zero (v ∷ γ)))
        tz' = subst ⟨_⟩ (tagAtL-adequate (suc t) k zero (v ∷ γ)) hTag
        tagPart : ⟨ (numeralL k ∷ v ∷ γ) ⊨ prAtL (suc (suc t)) zero (suc zero) ⟩
        tagPart = transport (cong fst (sym (prAtL-adequate (suc (suc t)) zero
                    (suc zero) (numeralL k ∷ v ∷ γ))))
          (tz' ∙ cong₂ pr (sym (numeralL-fst k)) refl)


module TmAgree {m : ℕ} (t : Fin (4 + m)) (A K N0 N1 : Fin m) (γ : S ^ (4 + m))
  (tagEq0 : fst (lookup (suc (suc (suc (suc N0)))) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc (suc (suc (suc N1)))) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc A)))) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩)
  (arityK : (v : S) → ⟨ fst v ∈ fst (lookup (suc (suc zero)) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩) where

  module B0 = TmBranch {m} t N0 0 (suc (suc (suc (suc A)))) K γ
               tagEq0 numK0 carrierK
  module B1 = TmBranch {m} t N1 1 (suc (suc zero)) K γ
               tagEq1 numK1 arityK

  out : ⟨ γ ⊨ isTmBS t A K N0 N1 ⟩ → ⟨ γ ⊨ isTmAt t (suc (suc zero)) (suc (suc (suc (suc A)))) ⟩
  out h = PT.rec squash₁
    (λ { (inl h0) → ∣ inl (B0.out h0) ∣₁
       ; (inr h1) → ∣ inr (B1.out h1) ∣₁ })
    h

  in' : ⟨ γ ⊨ isTmAt t (suc (suc zero)) (suc (suc (suc (suc A)))) ⟩
      → ⟨ γ ⊨ isTmBS t A K N0 N1 ⟩
  in' h = PT.rec squash₁
    (λ { (inl h0) → ∣ inl (B0.in' h0) ∣₁
       ; (inr h1) → ∣ inr (B1.in' h1) ∣₁ })
    h


module BothTmRel {n : ℕ} (A K N0 N1 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc N1) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc K) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc K) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc A) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
           → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩) where

  out : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTmBS A K N0 N1 ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTm A ⟩
  out b a N hNK (h0 , h1) = (B0.out h0 , B1.out h1)
    where
    module B0 = TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (λ v hv → arityK N v hv hNK)
    module B1 = TmAgree {n} zero A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (λ v hv → arityK N v hv hNK)

  back : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTm A ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ bothTmBS A K N0 N1 ⟩
  back b a N hNK (h0 , h1) = (B0.in' h0 , B1.in' h1)
    where
    module B0 = TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (λ v hv → arityK N v hv hNK)
    module B1 = TmAgree {n} zero A K N0 N1 (b ∷ a ∷ N ∷ γ)
                   tagEq0 tagEq1 numK0 numK1 carrierK (λ v hv → arityK N v hv hNK)


module FstTmRel {n : ℕ} (A K N0 N1 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0))
  (tagEq1 : fst (lookup (suc N1) γ) ≡ fst (numeralL 1))
  (numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup (suc K) γ) ⟩)
  (numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup (suc K) γ) ⟩)
  (carrierK : (v : S) → ⟨ fst v ∈ fst (lookup (suc A) γ) ⟩
             → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩)
  (arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
           → ⟨ fst v ∈ fst (lookup (suc K) γ) ⟩) where

  out : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTmBS A K N0 N1 ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTm A ⟩
  out b a N hNK = B.out
    where
    module B = TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                  tagEq0 tagEq1 numK0 numK1 carrierK (λ v hv → arityK N v hv hNK)

  back : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTm A ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ fstTmBS A K N0 N1 ⟩
  back b a N hNK = B.in'
    where
    module B = TmAgree {n} (suc zero) A K N0 N1 (b ∷ a ∷ N ∷ γ)
                  tagEq0 tagEq1 numK0 numK1 carrierK (λ v hv → arityK N v hv hNK)


module TopBinRel {n : ℕ} (K : Fin n) (γ : S ^ (1 + n)) where
  out : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
                    → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
  out b a N hNK h = h

  back : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
                     → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ ⊤̇ {n = 4 + n} ⟩
  back b a N hNK h = h


module TopUnRel {n : ℕ} (γ : S ^ (1 + n)) where
  out : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
                  → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
  out a N h = h

  back : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
                   → ⟨ (a ∷ N ∷ γ) ⊨ ⊤̇ {n = 3 + n} ⟩
  back a N h = h


module ZeroPayRel {n : ℕ} (N0 : Fin n) (γ : S ^ (1 + n))
  (tagEq0 : fst (lookup (suc N0) γ) ≡ fst (numeralL 0)) where

  out : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ var (suc (suc (suc N0)))) ⟩
                  → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ con (numeralL 0)) ⟩
  out a N h = h ∙ tagEq0

  back : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ con (numeralL 0)) ⟩
                   → ⟨ (a ∷ N ∷ γ) ⊨ (var zero ≐ var (suc (suc (suc N0)))) ⟩
  back a N h = h ∙ sym tagEq0


module BinFormAgree {n : ℕ} (C : S) (tag K : Fin n) (k : ℕ)
  (γ : S ^ (1 + n))
  (tagEq : fst (lookup (suc tag) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc K) γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩ → ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
           → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc K) γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩ → ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup (suc K) γ) ⟩)
  (compK : (c N a b : S) → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁)
  (relB relM : Formula S (4 + n))
  (relOut : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
           → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relB ⟩
          → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relM ⟩)
  (relBack : (b a N : S) → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
           → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relM ⟩
           → ⟨ (b ∷ a ∷ N ∷ γ) ⊨ relB ⟩) where

  out : ⟨ fst (lookup zero γ) ∈ fst C ⟩
      → ⟨ γ ⊨ binForm k relM ⟩
      → ⟨ γ ⊨ binFormBS tag K relB ⟩
  out c∈C h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] ⟨ (N ∷ γ) ⊨ ∃̇ (∃̇ (arityTagPairAtL
           (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
           ∧̇ relM)) ⟩
       → ⟨ γ ⊨ binFormBS tag K relB ⟩
    go (N , hN) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] ⟨ (a ∷ N ∷ γ) ⊨ ∃̇ (arityTagPairAtL
              (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
              ∧̇ relM) ⟩
          → ⟨ γ ⊨ binFormBS tag K relB ⟩
      go₂ (a , ha) = PT.rec squash₁ go₃ ha
        where
        go₃ : Σ[ b ∈ S ] ⟨ (b ∷ a ∷ N ∷ γ) ⊨ arityTagPairAtL
                (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
                ∧̇ relM ⟩
            → ⟨ γ ⊨ binFormBS tag K relB ⟩
        go₃ (b , (hTag , hRel)) =
          ∣ N , ( ks .fst
                , ∣ a , ( ks .snd .fst
                        , ∣ b , ( ks .snd .snd .fst
                                , ( S.in' (ks .snd .fst) (ks .snd .snd .fst) hTag
                                  , relBack b a N (ks .fst) hRel ) ) ∣₁ )
                  ∣₁ ) ∣₁
          where
          module S = BinShapeClosed {n} tag K k (b ∷ a ∷ N ∷ γ)
                       tagEq numK innerK pairK
          shape : fst (lookup zero γ)
                ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
          shape = transport (cong fst (arityTagPairAtL-adequate
                    (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
                    (b ∷ a ∷ N ∷ γ))) hTag
          ks : ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
             × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
             × ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁
          ks = compK (lookup zero γ) N a b c∈C shape

  back : ⟨ γ ⊨ binFormBS tag K relB ⟩
       → ⟨ γ ⊨ binForm k relM ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] (⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                    × ⟨ (N ∷ γ) ⊨ ∃̇∈ (var (suc (suc K)))
                          (∃̇∈ (var (suc (suc (suc K))))
                            (arTagPairBS tag K ∧̇ relB)) ⟩)
       → ⟨ γ ⊨ binForm k relM ⟩
    go (N , (N∈ , hN)) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] (⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
                       × ⟨ (a ∷ N ∷ γ) ⊨ ∃̇∈ (var (suc (suc (suc K))))
                             (arTagPairBS tag K ∧̇ relB) ⟩)
          → ⟨ γ ⊨ binForm k relM ⟩
      go₂ (a , (a∈ , ha)) = PT.rec squash₁ go₃ ha
        where
        go₃ : Σ[ b ∈ S ] (⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
                         × ⟨ (b ∷ a ∷ N ∷ γ) ⊨ arTagPairBS tag K ∧̇ relB ⟩)
            → ⟨ γ ⊨ binForm k relM ⟩
        go₃ (b , (b∈ , (hTag , hRel))) =
          ∣ N , ∣ a , ∣ b , ( S.out hTag , relOut b a N N∈ hRel ) ∣₁ ∣₁ ∣₁
          where
          module S = BinShapeClosed {n} tag K k (b ∷ a ∷ N ∷ γ)
                       tagEq numK innerK pairK


module UnFormAgree {n : ℕ} (C : S) (tag K : Fin n) (k : ℕ)
  (γ : S ^ (1 + n))
  (tagEq : fst (lookup (suc tag) γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup (suc K) γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
           → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc K) γ) ⟩)
  (unCompK : (c N a : S) → ⟨ fst c ∈ fst C ⟩
            → fst c ≡ pr (fst N) (pr (# k) (fst a))
            → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁)
  (relB relM : Formula S (3 + n))
  (relOut : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ relB ⟩
          → ⟨ (a ∷ N ∷ γ) ⊨ relM ⟩)
  (relBack : (a N : S) → ⟨ (a ∷ N ∷ γ) ⊨ relM ⟩
           → ⟨ (a ∷ N ∷ γ) ⊨ relB ⟩) where

  out : ⟨ fst (lookup zero γ) ∈ fst C ⟩
      → ⟨ γ ⊨ unForm k relM ⟩
      → ⟨ γ ⊨ unFormBS tag K relB ⟩
  out c∈C h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] ⟨ (N ∷ γ) ⊨ ∃̇ (arityTagAtL
           (suc (suc zero)) (suc zero) k zero ∧̇ relM) ⟩
       → ⟨ γ ⊨ unFormBS tag K relB ⟩
    go (N , hN) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] ⟨ (a ∷ N ∷ γ) ⊨ arityTagAtL
              (suc (suc zero)) (suc zero) k zero ∧̇ relM ⟩
          → ⟨ γ ⊨ unFormBS tag K relB ⟩
      go₂ (a , (hTag , hRel)) =
        ∣ N , ( ks .fst
              , ∣ a , ( ks .snd .fst , ( S.in' (ks .snd .fst) hTag , relBack a N hRel ) ) ∣₁ ) ∣₁
        where
        module S = UnShapeClosed {n} tag K k (a ∷ N ∷ γ)
                     tagEq numK innerK
        shape : fst (lookup zero γ) ≡ pr (fst N) (pr (# k) (fst a))
        shape = transport (cong fst (arityTagAtL-adequate
                  (suc (suc zero)) (suc zero) k zero (a ∷ N ∷ γ))) hTag
        ks : ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
           × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
           × ∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁
        ks = unCompK (lookup zero γ) N a c∈C shape

  back : ⟨ γ ⊨ unFormBS tag K relB ⟩
       → ⟨ γ ⊨ unForm k relM ⟩
  back h = PT.rec squash₁ go h
    where
    go : Σ[ N ∈ S ] (⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
                    × ⟨ (N ∷ γ) ⊨ ∃̇∈ (var (suc (suc K)))
                          (arTagBS tag K ∧̇ relB) ⟩)
       → ⟨ γ ⊨ unForm k relM ⟩
    go (N , (N∈ , hN)) = PT.rec squash₁ go₂ hN
      where
      go₂ : Σ[ a ∈ S ] (⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
                       × ⟨ (a ∷ N ∷ γ) ⊨ arTagBS tag K ∧̇ relB ⟩)
          → ⟨ γ ⊨ unForm k relM ⟩
      go₂ (a , (a∈ , (hTag , hRel))) =
        ∣ N , ∣ a , ( S.out hTag , relOut a N hRel ) ∣₁ ∣₁
        where
        module S = UnShapeClosed {n} tag K k (a ∷ N ∷ γ)
                     tagEq numK innerK


module Lift12Back {n : ℕ} (γ : S ^ (1 + n))
  (P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁ : Type (ℓ-suc ℓ))
  (Q₀ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ Q₇ Q₈ Q₉ Q₁₀ Q₁₁ : Type (ℓ-suc ℓ))
  (r₀ : P₀ → Q₀) (r₁ : P₁ → Q₁) (r₂ : P₂ → Q₂) (r₃ : P₃ → Q₃)
  (r₄ : P₄ → Q₄) (r₅ : P₅ → Q₅) (r₆ : P₆ → Q₆) (r₇ : P₇ → Q₇)
  (r₈ : P₈ → Q₈) (r₉ : P₉ → Q₉) (r₁₀ : P₁₀ → Q₁₀) (r₁₁ : P₁₁ → Q₁₁) where

  s₁₀ : ∥ P₁₀ ⊎ P₁₁ ∥₁ → ∥ Q₁₀ ⊎ Q₁₁ ∥₁
  s₁₀ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₁₀ x) ∣₁
       ; (inr x) → ∣ inr (r₁₁ x) ∣₁ })

  s₉ : ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ → ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁
  s₉ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₉ x) ∣₁
       ; (inr x) → ∣ inr (s₁₀ x) ∣₁ })

  s₈ : ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁
  s₈ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₈ x) ∣₁
       ; (inr x) → ∣ inr (s₉ x) ∣₁ })

  s₇ : ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₇ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₇ x) ∣₁
       ; (inr x) → ∣ inr (s₈ x) ∣₁ })

  s₆ : ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₆ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₆ x) ∣₁
       ; (inr x) → ∣ inr (s₇ x) ∣₁ })

  s₅ : ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₅ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₅ x) ∣₁
       ; (inr x) → ∣ inr (s₆ x) ∣₁ })

  s₄ : ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₄ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₄ x) ∣₁
       ; (inr x) → ∣ inr (s₅ x) ∣₁ })

  s₃ : ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₃ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₃ x) ∣₁
       ; (inr x) → ∣ inr (s₄ x) ∣₁ })

  s₂ : ∥ P₂ ⊎ ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₂ ⊎ ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₂ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₂ x) ∣₁
       ; (inr x) → ∣ inr (s₃ x) ∣₁ })

  s₁ : ∥ P₁ ⊎ ∥ P₂ ⊎ ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
     → ∥ Q₁ ⊎ ∥ Q₂ ⊎ ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  s₁ = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₁ x) ∣₁
       ; (inr x) → ∣ inr (s₂ x) ∣₁ })

  back : ∥ P₀ ⊎ ∥ P₁ ⊎ ∥ P₂ ⊎ ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
       → ∥ Q₀ ⊎ ∥ Q₁ ⊎ ∥ Q₂ ⊎ ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  back = PT.rec squash₁
    (λ { (inl x) → ∣ inl (r₀ x) ∣₁
       ; (inr x) → ∣ inr (s₁ x) ∣₁ })

-- The forward-facing name of the same generic disjunction walk.
-- Lift12Out shares Lift12Back's whole body (DD4): the twelve-row
-- assembly at abstract propositions is direction-agnostic, so the
-- machine -> story walk is the same telescope with the roles of the
-- source and target propositions unchanged and the row functions
-- pointing the other way.  The name exists for P-v: a proof gets a
-- name and the consumers pass the name.

module Lift12Out {n : ℕ} (γ : S ^ (1 + n))
  (P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁ : Type (ℓ-suc ℓ))
  (Q₀ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ Q₇ Q₈ Q₉ Q₁₀ Q₁₁ : Type (ℓ-suc ℓ))
  (r₀ : P₀ → Q₀) (r₁ : P₁ → Q₁) (r₂ : P₂ → Q₂) (r₃ : P₃ → Q₃)
  (r₄ : P₄ → Q₄) (r₅ : P₅ → Q₅) (r₆ : P₆ → Q₆) (r₇ : P₇ → Q₇)
  (r₈ : P₈ → Q₈) (r₉ : P₉ → Q₉) (r₁₀ : P₁₀ → Q₁₀) (r₁₁ : P₁₁ → Q₁₁) where

  module L = Lift12Back {n} γ
    P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁
    Q₀ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ Q₇ Q₈ Q₉ Q₁₀ Q₁₁
    r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ r₁₀ r₁₁

  out : ∥ P₀ ⊎ ∥ P₁ ⊎ ∥ P₂ ⊎ ∥ P₃ ⊎ ∥ P₄ ⊎ ∥ P₅ ⊎ ∥ P₆ ⊎ ∥ P₇ ⊎ ∥ P₈ ⊎ ∥ P₉ ⊎ ∥ P₁₀ ⊎ P₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
      → ∥ Q₀ ⊎ ∥ Q₁ ⊎ ∥ Q₂ ⊎ ∥ Q₃ ⊎ ∥ Q₄ ⊎ ∥ Q₅ ⊎ ∥ Q₆ ⊎ ∥ Q₇ ⊎ ∥ Q₈ ⊎ ∥ Q₉ ⊎ ∥ Q₁₀ ⊎ Q₁₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁ ∥₁
  out = L.back

-- The fixed site-fact block of the shapedness/witness transfers: the
-- twelve arity-tag equalities, the twelve numeral memberships, and the
-- closure facts.  One record, so a transfer module states the block as
-- ONE parameter and re-elaborates it once per module instead of once
-- per instantiation site.

module KFactsNS where
  record KFacts {n : ℕ} (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
    (γ : S ^ n) : Type (ℓ-suc ℓ) where
    field
      tagEq0 : fst (lookup N0 γ) ≡ fst (numeralL 0)
      tagEq1 : fst (lookup N1 γ) ≡ fst (numeralL 1)
      tagEq2 : fst (lookup N2 γ) ≡ fst (numeralL 2)
      tagEq3 : fst (lookup N3 γ) ≡ fst (numeralL 3)
      tagEq4 : fst (lookup N4 γ) ≡ fst (numeralL 4)
      tagEq5 : fst (lookup N5 γ) ≡ fst (numeralL 5)
      tagEq6 : fst (lookup N6 γ) ≡ fst (numeralL 6)
      tagEq7 : fst (lookup N7 γ) ≡ fst (numeralL 7)
      tagEq8 : fst (lookup N8 γ) ≡ fst (numeralL 8)
      tagEq9 : fst (lookup N9 γ) ≡ fst (numeralL 9)
      tagEq10 : fst (lookup N10 γ) ≡ fst (numeralL 10)
      tagEq11 : fst (lookup N11 γ) ≡ fst (numeralL 11)
      numK0 : ⟨ fst (numeralL 0) ∈ fst (lookup K γ) ⟩
      numK1 : ⟨ fst (numeralL 1) ∈ fst (lookup K γ) ⟩
      numK2 : ⟨ fst (numeralL 2) ∈ fst (lookup K γ) ⟩
      numK3 : ⟨ fst (numeralL 3) ∈ fst (lookup K γ) ⟩
      numK4 : ⟨ fst (numeralL 4) ∈ fst (lookup K γ) ⟩
      numK5 : ⟨ fst (numeralL 5) ∈ fst (lookup K γ) ⟩
      numK6 : ⟨ fst (numeralL 6) ∈ fst (lookup K γ) ⟩
      numK7 : ⟨ fst (numeralL 7) ∈ fst (lookup K γ) ⟩
      numK8 : ⟨ fst (numeralL 8) ∈ fst (lookup K γ) ⟩
      numK9 : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩
      numK10 : ⟨ fst (numeralL 10) ∈ fst (lookup K γ) ⟩
      numK11 : ⟨ fst (numeralL 11) ∈ fst (lookup K γ) ⟩
      innerK : (k : ℕ) (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩
      innerPairK : (k : ℕ) (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
             → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩
      pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
             → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩
      carrierK : (v : S) → ⟨ fst v ∈ fst (lookup A γ) ⟩
               → ⟨ fst v ∈ fst (lookup K γ) ⟩
      arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩ → ⟨ fst N ∈ fst (lookup K γ) ⟩
             → ⟨ fst v ∈ fst (lookup K γ) ⟩
open KFactsNS
open KFacts

-- The same block one environment element deeper: `c ∷ γ` shifts every
-- lookup by one successor, so every field is definitionally the block's
-- own field and the record is rebuilt once here, not at each use.

KFactsCons : {n : ℕ} (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
           → (γ : S ^ n) (c : S)
           → KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
           → KFacts {1 + n} (suc A) (suc K)
               (suc N0) (suc N1) (suc N2) (suc N3)
               (suc N4) (suc N5) (suc N6) (suc N7)
               (suc N8) (suc N9) (suc N10) (suc N11) (c ∷ γ)
KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ c f = record
  { tagEq0 = f .tagEq0
  ; tagEq1 = f .tagEq1
  ; tagEq2 = f .tagEq2
  ; tagEq3 = f .tagEq3
  ; tagEq4 = f .tagEq4
  ; tagEq5 = f .tagEq5
  ; tagEq6 = f .tagEq6
  ; tagEq7 = f .tagEq7
  ; tagEq8 = f .tagEq8
  ; tagEq9 = f .tagEq9
  ; tagEq10 = f .tagEq10
  ; tagEq11 = f .tagEq11
  ; numK0 = f .numK0
  ; numK1 = f .numK1
  ; numK2 = f .numK2
  ; numK3 = f .numK3
  ; numK4 = f .numK4
  ; numK5 = f .numK5
  ; numK6 = f .numK6
  ; numK7 = f .numK7
  ; numK8 = f .numK8
  ; numK9 = f .numK9
  ; numK10 = f .numK10
  ; numK11 = f .numK11
  ; innerK = f .innerK
  ; innerPairK = f .innerPairK
  ; pairK = f .pairK
  ; carrierK = f .carrierK
  ; arityK = f .arityK }


module ShapesAgree {n : ℕ}
  (C : S) (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ (1 + n))
  (f : KFacts {1 + n} (suc A) (suc K)
         (suc N0) (suc N1) (suc N2) (suc N3)
         (suc N4) (suc N5) (suc N6) (suc N7)
         (suc N8) (suc N9) (suc N10) (suc N11) γ)
  (compK : (k : ℕ) (c N a b : S) → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst N) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
            × ⟨ fst b ∈ fst (lookup (suc K) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁)
  (unCompK : (k : ℕ) (c N a : S) → ⟨ fst c ∈ fst C ⟩
            → fst c ≡ pr (fst N) (pr (# k) (fst a))
            → ⟨ fst N ∈ fst (lookup (suc K) γ) ⟩
              × ⟨ fst a ∈ fst (lookup (suc K) γ) ⟩
            × ∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁) where

  module R0 = BothTmRel {n} A K N0 N1 γ (f .tagEq0) (f .tagEq1) (f .numK0) (f .numK1) (f .carrierK) (f .arityK)
  module R1 = BothTmRel {n} A K N0 N1 γ (f .tagEq0) (f .tagEq1) (f .numK0) (f .numK1) (f .carrierK) (f .arityK)
  module R10 = FstTmRel {n} A K N0 N1 γ (f .tagEq0) (f .tagEq1) (f .numK0) (f .numK1) (f .carrierK) (f .arityK)
  module R11 = FstTmRel {n} A K N0 N1 γ (f .tagEq0) (f .tagEq1) (f .numK0) (f .numK1) (f .carrierK) (f .arityK)
  module RT = TopBinRel {n} K γ
  module RU = TopUnRel {n} γ
  module R6 = ZeroPayRel {n} N0 γ (f .tagEq0)
  module R7 = ZeroPayRel {n} N0 γ (f .tagEq0)

  module B0 = BinFormAgree {n} C N0 K 0 γ (f .tagEq0) (f .numK0) (f .innerPairK 0) (f .pairK) (compK 0)
               (bothTmBS A K N0 N1) (bothTm A) R0.out R0.back
  module B1 = BinFormAgree {n} C N1 K 1 γ (f .tagEq1) (f .numK1) (f .innerPairK 1) (f .pairK) (compK 1)
               (bothTmBS A K N0 N1) (bothTm A) R1.out R1.back
  module B2 = BinFormAgree {n} C N2 K 2 γ (f .tagEq2) (f .numK2) (f .innerPairK 2) (f .pairK) (compK 2)
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out RT.back
  module B3 = BinFormAgree {n} C N3 K 3 γ (f .tagEq3) (f .numK3) (f .innerPairK 3) (f .pairK) (compK 3)
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out RT.back
  module B4 = BinFormAgree {n} C N4 K 4 γ (f .tagEq4) (f .numK4) (f .innerPairK 4) (f .pairK) (compK 4)
               (⊤̇ {n = 4 + n}) (⊤̇ {n = 4 + n}) RT.out RT.back
  module U5 = UnFormAgree {n} C N5 K 5 γ (f .tagEq5) (f .numK5) (f .innerK 5) (unCompK 5)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out RU.back
  module U6 = UnFormAgree {n} C N6 K 6 γ (f .tagEq6) (f .numK6) (f .innerK 6) (unCompK 6)
               (var zero ≐ var (suc (suc (suc N0)))) (var zero ≐ con (numeralL 0))
               R6.out R6.back
  module U7 = UnFormAgree {n} C N7 K 7 γ (f .tagEq7) (f .numK7) (f .innerK 7) (unCompK 7)
               (var zero ≐ var (suc (suc (suc N0)))) (var zero ≐ con (numeralL 0))
               R7.out R7.back
  module U8 = UnFormAgree {n} C N8 K 8 γ (f .tagEq8) (f .numK8) (f .innerK 8) (unCompK 8)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out RU.back
  module U9 = UnFormAgree {n} C N9 K 9 γ (f .tagEq9) (f .numK9) (f .innerK 9) (unCompK 9)
               (⊤̇ {n = 3 + n}) (⊤̇ {n = 3 + n}) RU.out RU.back
  module B10 = BinFormAgree {n} C N10 K 10 γ (f .tagEq10) (f .numK10) (f .innerPairK 10) (f .pairK) (compK 10)
                (fstTmBS A K N0 N1) (fstTm A) R10.out R10.back
  module B11 = BinFormAgree {n} C N11 K 11 γ (f .tagEq11) (f .numK11) (f .innerPairK 11) (f .pairK) (compK 11)
                (fstTmBS A K N0 N1) (fstTm A) R11.out R11.back

  module L = Lift12Back {n} γ
    (⟨ γ ⊨ binFormBS N0 K (bothTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binFormBS N1 K (bothTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binFormBS N2 K (⊤̇ {n = 4 + n}) ⟩)
    (⟨ γ ⊨ binFormBS N3 K (⊤̇ {n = 4 + n}) ⟩)
    (⟨ γ ⊨ binFormBS N4 K (⊤̇ {n = 4 + n}) ⟩)
    (⟨ γ ⊨ unFormBS N5 K (⊤̇ {n = 3 + n}) ⟩)
    (⟨ γ ⊨ unFormBS N6 K (var zero ≐ var (suc (suc (suc N0)))) ⟩)
    (⟨ γ ⊨ unFormBS N7 K (var zero ≐ var (suc (suc (suc N0)))) ⟩)
    (⟨ γ ⊨ unFormBS N8 K (⊤̇ {n = 3 + n}) ⟩)
    (⟨ γ ⊨ unFormBS N9 K (⊤̇ {n = 3 + n}) ⟩)
    (⟨ γ ⊨ binFormBS N10 K (fstTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binFormBS N11 K (fstTmBS A K N0 N1) ⟩)
    (⟨ γ ⊨ binForm 0 (bothTm A) ⟩)
    (⟨ γ ⊨ binForm 1 (bothTm A) ⟩)
    (⟨ γ ⊨ binForm 2 noneB ⟩)
    (⟨ γ ⊨ binForm 3 noneB ⟩)
    (⟨ γ ⊨ binForm 4 noneB ⟩)
    (⟨ γ ⊨ unForm 5 noneU ⟩)
    (⟨ γ ⊨ unForm 6 zeroPay ⟩)
    (⟨ γ ⊨ unForm 7 zeroPay ⟩)
    (⟨ γ ⊨ unForm 8 noneU ⟩)
    (⟨ γ ⊨ unForm 9 noneU ⟩)
    (⟨ γ ⊨ binForm 10 (fstTm A) ⟩)
    (⟨ γ ⊨ binForm 11 (fstTm A) ⟩)
    B0.back B1.back B2.back B3.back B4.back U5.back U6.back U7.back
    U8.back U9.back B10.back B11.back

  back : ⟨ γ ⊨ shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ shapes A ⟩
  back = L.back

  out : ⟨ fst (lookup zero γ) ∈ fst C ⟩
      → ⟨ γ ⊨ shapes A ⟩
      → ⟨ γ ⊨ shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out c∈C = L'.out
    where
    module L' = Lift12Out {n} γ
      (⟨ γ ⊨ binForm 0 (bothTm A) ⟩)
      (⟨ γ ⊨ binForm 1 (bothTm A) ⟩)
      (⟨ γ ⊨ binForm 2 noneB ⟩)
      (⟨ γ ⊨ binForm 3 noneB ⟩)
      (⟨ γ ⊨ binForm 4 noneB ⟩)
      (⟨ γ ⊨ unForm 5 noneU ⟩)
      (⟨ γ ⊨ unForm 6 zeroPay ⟩)
      (⟨ γ ⊨ unForm 7 zeroPay ⟩)
      (⟨ γ ⊨ unForm 8 noneU ⟩)
      (⟨ γ ⊨ unForm 9 noneU ⟩)
      (⟨ γ ⊨ binForm 10 (fstTm A) ⟩)
      (⟨ γ ⊨ binForm 11 (fstTm A) ⟩)
      (⟨ γ ⊨ binFormBS N0 K (bothTmBS A K N0 N1) ⟩)
      (⟨ γ ⊨ binFormBS N1 K (bothTmBS A K N0 N1) ⟩)
      (⟨ γ ⊨ binFormBS N2 K (⊤̇ {n = 4 + n}) ⟩)
      (⟨ γ ⊨ binFormBS N3 K (⊤̇ {n = 4 + n}) ⟩)
      (⟨ γ ⊨ binFormBS N4 K (⊤̇ {n = 4 + n}) ⟩)
      (⟨ γ ⊨ unFormBS N5 K (⊤̇ {n = 3 + n}) ⟩)
      (⟨ γ ⊨ unFormBS N6 K (var zero ≐ var (suc (suc (suc N0)))) ⟩)
      (⟨ γ ⊨ unFormBS N7 K (var zero ≐ var (suc (suc (suc N0)))) ⟩)
      (⟨ γ ⊨ unFormBS N8 K (⊤̇ {n = 3 + n}) ⟩)
      (⟨ γ ⊨ unFormBS N9 K (⊤̇ {n = 3 + n}) ⟩)
      (⟨ γ ⊨ binFormBS N10 K (fstTmBS A K N0 N1) ⟩)
      (⟨ γ ⊨ binFormBS N11 K (fstTmBS A K N0 N1) ⟩)
      (λ x → B0.out c∈C x) (λ x → B1.out c∈C x) (λ x → B2.out c∈C x)
      (λ x → B3.out c∈C x) (λ x → B4.out c∈C x) (λ x → U5.out c∈C x)
      (λ x → U6.out c∈C x) (λ x → U7.out c∈C x) (λ x → U8.out c∈C x)
      (λ x → U9.out c∈C x) (λ x → B10.out c∈C x) (λ x → B11.out c∈C x)

-- =====================================================================
-- THE CLOSEDNESS AND DOMAIN TRANSFERS, BOTH DIRECTIONS.  The generic
-- frame agreements (binShapeBS/unShapeBS against binShapeAt/unShapeAt
-- under a pointwise rel transfer), the closedness relations, the
-- eight-frame ClosedAgree (closedBS against closedAt) and the domain
-- transfer (domB against domAt).  The machine -> story directions
-- (`out`) are placed because producing `Adeq m` needs them; the
-- story -> machine directions (`back`) serve the decode consumers.
-- Ported from ProbeLJ156A sections 2 to 5.
-- =====================================================================

module BinFrameAgree {n : ℕ} (C tag K : Fin n) (k : ℕ) (γ : S ^ n)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (innerK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup K γ) ⟩)
  (pairK : (a b : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩ → ⟨ fst b ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ a b) ∈ fst (lookup K γ) ⟩)
  (codesK : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (relB relM : Formula S (4 + n))
  (relOut : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩
           → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩)
  (relBack : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
           → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩) where

  out : ⟨ γ ⊨ binShapeAt C k relM ⟩ → ⟨ γ ⊨ binShapeBS C tag K relB ⟩
  out h = λ c c∈ ar arK a aK b bK shapeB →
    let module S = BinShapeClosed {n} tag K k (b ∷ a ∷ ar ∷ c ∷ γ)
                     tagEq numK innerK pairK
    in relBack b a ar c
         (binShape-out C k relM γ h c ar a b c∈
           (subst fst (arityTagPairAtL-adequate
              (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
              (b ∷ a ∷ ar ∷ c ∷ γ)) (S.out shapeB)))

  back : ⟨ γ ⊨ binShapeBS C tag K relB ⟩ → ⟨ γ ⊨ binShapeAt C k relM ⟩
  back h = binShape-in C k relM γ go
    where
    go : (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
    go c ar a b c∈ shapeM =
      relOut b a ar c (h c c∈ ar arK a aK b bK
        (S.in' aK bK (subst ⟨_⟩ (sym (arityTagPairAtL-adequate
           (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) zero
           (b ∷ a ∷ ar ∷ c ∷ γ))) shapeM)))
      where
      module S = BinShapeClosed {n} tag K k (b ∷ a ∷ ar ∷ c ∷ γ)
                   tagEq numK innerK pairK
      ks : ⟨ fst ar ∈ fst (lookup K γ) ⟩
         × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
      ks = codesK c ar a b c∈ shapeM
      arK = ks .fst
      aK = ks .snd .fst
      bK = ks .snd .snd .fst


module UnFrameAgree {n : ℕ} (C tag K : Fin n) (k : ℕ) (γ : S ^ n)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩)
  (innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup K γ) ⟩)
  (unCodesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (relB relM : Formula S (3 + n))
  (relOut : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩
           → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩)
  (relBack : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
           → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relB ⟩) where

  out : ⟨ γ ⊨ unShapeAt C k relM ⟩ → ⟨ γ ⊨ unShapeBS C tag K relB ⟩
  out h = λ c c∈ ar arK a aK shapeB →
    let module S = UnShapeClosed {n} tag K k (a ∷ ar ∷ c ∷ γ)
                     tagEq numK innerK
    in relBack a ar c
         (unShape-out C k relM γ h c ar a c∈
           (subst fst (arityTagAtL-adequate
              (suc (suc zero)) (suc zero) k zero
              (a ∷ ar ∷ c ∷ γ)) (S.out shapeB)))

  back : ⟨ γ ⊨ unShapeBS C tag K relB ⟩ → ⟨ γ ⊨ unShapeAt C k relM ⟩
  back h = unShape-in C k relM γ go
    where
    go : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (fst a))
       → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ relM ⟩
    go c ar a c∈ shapeM =
      relOut a ar c (h c c∈ ar arK a aK
        (S.in' aK (subst ⟨_⟩ (sym (arityTagAtL-adequate
           (suc (suc zero)) (suc zero) k zero
           (a ∷ ar ∷ c ∷ γ))) shapeM)))
      where
      module S = UnShapeClosed {n} tag K k (a ∷ ar ∷ c ∷ γ)
                   tagEq numK innerK
      ks : ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
      ks = unCodesK c ar a c∈ shapeM
      arK = ks .fst
      aK = ks .snd .fst


module BothSameRel {n : ℕ} (C : Fin n) (γ : S ^ n) where
  out : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameB C ⟩
                       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameAt C ⟩
  out b a ar c h = h
  back : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameAt C ⟩
                        → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bothSameB C ⟩
  back b a ar c h = h


module OneSameRel {n : ℕ} (C : Fin n) (γ : S ^ n) where
  out : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameB C ⟩
                     → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameAt C ⟩
  out a ar c h = h
  back : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameAt C ⟩
                      → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSameB C ⟩
  back a ar c h = h


module OneSuccRel {n : ℕ} (C K : Fin n) (γ : S ^ n)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup C γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccAt C ⟩
                     → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccB C K ⟩
  out a ar c h = PT.rec squash₁ go h
    where
    go : Σ[ z ∈ S ]
         ⟨ (z ∷ a ∷ ar ∷ c ∷ γ) ⊨ (sucAtL (suc (suc zero)) zero
                                   ∧̇ appAt (suc (suc (suc (suc C)))) zero (suc zero)) ⟩
       → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccB C K ⟩
    go (z , (sz , ap)) = ∣ z , ( zK , ( sz , ap ) ) ∣₁
      where
      zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc K))) (a ∷ ar ∷ c ∷ γ)) ⟩
      zK = entryK z a
             (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc C)))) zero (suc zero)
                (z ∷ a ∷ ar ∷ c ∷ γ)) ap) .fst

  back : (a ar c : S) → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccB C K ⟩
                      → ⟨ (a ∷ ar ∷ c ∷ γ) ⊨ oneSuccAt C ⟩
  back a ar c = PT.map (λ { (z , _ , (sz , ap)) → z , (sz , ap) })


module SuccSndRel {n : ℕ} (C K : Fin n) (γ : S ^ n)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup C γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  out : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndAt C ⟩
                       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndB C K ⟩
  out b a ar c h = PT.rec squash₁ go h
    where
    go : Σ[ z ∈ S ]
         ⟨ (z ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ (sucAtL (suc (suc (suc zero))) zero
                                   ∧̇ appAt (suc (suc (suc (suc (suc C))))) zero (suc zero)) ⟩
       → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndB C K ⟩
    go (z , (sz , ap)) = ∣ z , ( zK , ( sz , ap ) ) ∣₁
      where
      zK : ⟨ fst z ∈ fst (lookup (suc (suc (suc (suc K)))) (b ∷ a ∷ ar ∷ c ∷ γ)) ⟩
      zK = entryK z b
             (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc C))))) zero (suc zero)
                (z ∷ b ∷ a ∷ ar ∷ c ∷ γ)) ap) .fst

  back : (b a ar c : S) → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndB C K ⟩
                        → ⟨ (b ∷ a ∷ ar ∷ c ∷ γ) ⊨ succSndAt C ⟩
  back b a ar c = PT.map (λ { (z , _ , (sz , ap)) → z , (sz , ap) })


module ClosedAgree {n : ℕ} (C K N2 N3 N4 N5 N8 N9 N10 N11 : Fin n)
  (A N0 N1 N6 N7 : Fin n)
  (γ : S ^ n)
  (f : KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
  (codesK : (k : ℕ) → (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (unCodesK : (k : ℕ) → (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (entryK : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup C γ) ⟩
           → ⟨ fst x ∈ fst (lookup K γ) ⟩ × ⟨ fst y ∈ fst (lookup K γ) ⟩) where

  module R2 = BothSameRel {n} C γ
  module R3 = BothSameRel {n} C γ
  module R4 = BothSameRel {n} C γ
  module R5 = OneSameRel {n} C γ
  module R8 = OneSuccRel {n} C K γ entryK
  module R9 = OneSuccRel {n} C K γ entryK
  module R10 = SuccSndRel {n} C K γ entryK
  module R11 = SuccSndRel {n} C K γ entryK

  module C2 = BinFrameAgree {n} C N2 K 2 γ (f .tagEq2) (f .numK2) (f .innerPairK 2) (f .pairK)
                (codesK 2) (bothSameB C) (bothSameAt C) R2.out R2.back
  module C3 = BinFrameAgree {n} C N3 K 3 γ (f .tagEq3) (f .numK3) (f .innerPairK 3) (f .pairK)
                (codesK 3) (bothSameB C) (bothSameAt C) R3.out R3.back
  module C4 = BinFrameAgree {n} C N4 K 4 γ (f .tagEq4) (f .numK4) (f .innerPairK 4) (f .pairK)
                (codesK 4) (bothSameB C) (bothSameAt C) R4.out R4.back
  module C5 = UnFrameAgree {n} C N5 K 5 γ (f .tagEq5) (f .numK5) (f .innerK 5)
                (unCodesK 5) (oneSameB C) (oneSameAt C) R5.out R5.back
  module C8 = UnFrameAgree {n} C N8 K 8 γ (f .tagEq8) (f .numK8) (f .innerK 8)
                (unCodesK 8) (oneSuccB C K) (oneSuccAt C) R8.back R8.out
  module C9 = UnFrameAgree {n} C N9 K 9 γ (f .tagEq9) (f .numK9) (f .innerK 9)
                (unCodesK 9) (oneSuccB C K) (oneSuccAt C) R9.back R9.out
  module C10 = BinFrameAgree {n} C N10 K 10 γ (f .tagEq10) (f .numK10) (f .innerPairK 10) (f .pairK)
                 (codesK 10) (succSndB C K) (succSndAt C) R10.back R10.out
  module C11 = BinFrameAgree {n} C N11 K 11 γ (f .tagEq11) (f .numK11) (f .innerPairK 11) (f .pairK)
                 (codesK 11) (succSndB C K) (succSndAt C) R11.back R11.out

  out : ⟨ γ ⊨ closedAt C ⟩ → ⟨ γ ⊨ closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 ⟩
  out h =
    ( C2.out (h .fst)
    , ( C3.out (h .snd .fst)
      , ( C4.out (h .snd .snd .fst)
        , ( C5.out (h .snd .snd .snd .fst)
          , ( C8.out (h .snd .snd .snd .snd .fst)
            , ( C9.out (h .snd .snd .snd .snd .snd .fst)
              , ( C10.out (h .snd .snd .snd .snd .snd .snd .fst)
                , C11.out (h .snd .snd .snd .snd .snd .snd .snd) )))))))

  back : ⟨ γ ⊨ closedBS C K N2 N3 N4 N5 N8 N9 N10 N11 ⟩ → ⟨ γ ⊨ closedAt C ⟩
  back h =
    ( C2.back (h .fst)
    , ( C3.back (h .snd .fst)
      , ( C4.back (h .snd .snd .fst)
        , ( C5.back (h .snd .snd .snd .fst)
          , ( C8.back (h .snd .snd .snd .snd .fst)
            , ( C9.back (h .snd .snd .snd .snd .snd .fst)
              , ( C10.back (h .snd .snd .snd .snd .snd .snd .fst)
                , C11.back (h .snd .snd .snd .snd .snd .snd .snd) )))))))


module ShapedAgree {n : ℕ} (C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin n)
  (γ : S ^ n)
  (f : KFacts A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
  (codesK : (k : ℕ) (c ar a b : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
           → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             × ⟨ fst a ∈ fst (lookup K γ) ⟩ × ⟨ fst b ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁)
  (unCodesK : (k : ℕ) (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
             × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁) where

  out : ⟨ γ ⊨ shapedAt C A ⟩ → ⟨ γ ⊨ shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  out h = λ c c∈ →
    let module S = ShapesAgree {n} (lookup C γ) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
          (c ∷ γ) (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ c f)
          codesK unCodesK
    in S.out c∈ (h c c∈)

  back : ⟨ γ ⊨ shapedBS C A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
       → ⟨ γ ⊨ shapedAt C A ⟩
  back h = λ c c∈ →
    let module S = ShapesAgree {n} (lookup C γ) A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
          (c ∷ γ) (KFactsCons A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ c f)
          codesK unCodesK
    in S.back (h c c∈)


private
  PairIs : V ℓ → V ℓ → Ω
  PairIs a p = (a ≡ p) , setIsSet a p


module TagAgree {n : ℕ} (s tag x K : Fin n) (γ : S ^ n) (k : ℕ)
  (tagEq : fst (lookup tag γ) ≡ fst (numeralL k))
  (numK : ⟨ fst (numeralL k) ∈ fst (lookup K γ) ⟩) where

  out : ⟨ γ ⊨ tagAtL s k x ⟩ → ⟨ γ ⊨ tagBS s tag x K ⟩
  out h = ∣ numeralL k , ( numK , ( sym tagEq , hp ) ) ∣₁
    where
    h' : ⟨ PairIs (fst (lookup s γ)) (pr (fst (numeralL k)) (fst (lookup x γ))) ⟩
    h' = subst ⟨_⟩
           (cong (λ w → PairIs (fst (lookup s γ)) (pr w (fst (lookup x γ))))
             (sym (numeralL-fst k)))
           (subst ⟨_⟩ (tagAtL-adequate s k x γ) h)
    hp : ⟨ (numeralL k ∷ γ) ⊨ prAtL (suc s) zero (suc x) ⟩
    hp = subst ⟨_⟩ (sym (prAtL-adequate {suc n} (suc s) zero (suc x) (numeralL k ∷ γ))) h'

  back : ⟨ γ ⊨ tagBS s tag x K ⟩ → ⟨ γ ⊨ tagAtL s k x ⟩
  back h = subst ⟨_⟩ (sym (tagAtL-adequate s k x γ))
    (subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
      (numeralL-fst k) go)
    where
    go : fst (lookup s γ) ≡ pr (fst (numeralL k)) (fst (lookup x γ))
    go = PT.rec (snd (PairIs (fst (lookup s γ))
                       (pr (fst (numeralL k)) (fst (lookup x γ)))))
      (λ { (t , (tK , (te , tp))) →
        subst (λ u → fst (lookup s γ) ≡ pr u (fst (lookup x γ)))
          (te ∙ tagEq)
          (subst ⟨_⟩ (prAtL-adequate {suc n} (suc s) zero (suc x) (t ∷ γ)) tp) })
      h



-- =====================================================================
-- MANIFEST: block name, source lines in src/L/Condensation.lagda.md.
-- =====================================================================
-- Δ₀-prAtL: :88-90
-- Δ₀-sucAtL: :91-93
-- Δ₀-appAt: :94-99
-- extAtB: :100-103
-- Δ₀-extAtB: :104-106
-- Clause: :117-265
-- arTagB: :446-453
-- Δ₀-arTagB: :454-460
-- arTagPairB: :461-471
-- Δ₀-arTagPairB: :472-482
-- subValB: :483-487
-- Δ₀-subValB: :488-492
-- subValSuccB: :493-498
-- Δ₀-subValSuccB: :499-506
-- tmValB: :507-515
-- Δ₀-tmValB: :516-525
-- envBndGen: :526-543
-- Δ₀-envBndGen: :544-563
-- envSetB: :564-567
-- Δ₀-envSetB: :568-573
-- interB: :574-577
-- Δ₀-interB: :578-580
-- unionB: :581-584
-- Δ₀-unionB: :585-587
-- implB: :588-592
-- Δ₀-implB: :593-595
-- diffB: :596-599
-- Δ₀-diffB: :600-602
-- sameB: :603-605
-- Δ₀-sameB: :606-608
-- emptyB: :609-611
-- Δ₀-emptyB: :612-622
-- envHypU: :623-628
-- Δ₀-envHypU: :629-636
-- envHypT: :637-642
-- Δ₀-envHypT: :643-650
-- envHypB2: :651-656
-- Δ₀-envHypB2: :657-664
-- envHypB2T: :665-670
-- Δ₀-envHypB2T: :671-685
-- unFullAt: :686-696
-- Δ₀-unFullAt: :697-706
-- unEnvAt: :707-715
-- Δ₀-unEnvAt: :716-725
-- unBareAt: :726-733
-- Δ₀-unBareAt: :734-742
-- binFullAt: :743-753
-- Δ₀-binFullAt: :754-764
-- binEnvAt: :765-774
-- Δ₀-binEnvAt: :775-787
-- propBodyB: :967-976
-- Δ₀-propBodyB: :977-988
-- atomBodyB: :989-1007
-- Δ₀-atomBodyB: :1008-1041
-- bndBodyAll: :1042-1059
-- bndBodyEx: :1060-1077
-- Δ₀-bndBodyAll: :1078-1099
-- Δ₀-bndBodyEx: :1100-1126
-- Bot: :1127-1135
-- Top: :1136-1148
-- Neg: :1149-1176
-- Forall: :1177-1220
-- And: :1221-1255
-- Or: :1256-1290
-- Imp: :1291-1327
-- Mem: :1328-1345
-- Eq: :1346-1363
-- AllIn: :1364-1388
-- ExIn: :1389-1415
-- Exist: :1416-1473
-- tagBS: :1484-1488
-- arTagPairBS: :1494-1503
-- arTagBS: :1513-1520
-- binShapeBS: :1527-1532
-- unShapeBS: :1538-1542
-- bothSameB: :1548-1552
-- oneSameB: :1558-1560
-- oneSuccB: :1564-1569
-- succSndB: :1575-1580
-- closedBS: :1586-1598
-- binFormBS: :1612-1616
-- unFormBS: :1622-1626
-- isTmBS: :1632-1643
-- bothTmBS: :1652-1655
-- fstTmBS: :1660-1662
-- shapesBS: :1666-1683
-- shapedBS: :1700-1706
-- domB: :1746-1753
-- extAtB→extAt: :2511-2520
-- extAt→extAtB: :2521-2530
-- UnaryShape: :2531-2613
-- BinaryShape: :2614-2720
-- emptyB→emptyAt: :2721-2725
-- emptyAt→emptyB: :2726-2751
-- GraphEntry: :2752-2773
-- BotAgree: :2774-2816
-- ChainZ: :2817-2925
-- EnvSet: :2926-3061
-- TmVal: :3062-3150
-- SubValB2T: :3172-3208
-- SubValSuccB2T: :3209-3258
-- OpTransfer: :3259-3265
-- PropAgree: :3282-3529
-- AndAgree: :3534-3588
-- OrAgree: :3589-3648
-- TopAgree: :3663-3735
-- NegAgree: :3736-3831
-- keyU: :3837-3842
-- succU: :3843-3848
-- ForallAgree: :3849-3960
-- ExistAgree: :3961-4142
-- ClauseAgree: :4143-4204
-- AtomLeaf: :4205-4408
-- MemAgree: :4409-4517
-- ImpLeaf: :4518-4798
-- BndLeaf: :4799-5008
-- AllInAgree: :5009-5137
-- ExInAgree: :5138-5265
-- ImpAgree: :5266-5366
-- EqAgree: :5367-5463
-- UnShapeClosed: :5479-5549
-- BinShapeClosed: :5550-5647
-- TmBranch: :5648-5707
-- TmAgree: :5708-5735
-- BothTmRel: :5736-5765
-- FstTmRel: :5766-5791
-- TopBinRel: :5792-5802
-- TopUnRel: :5803-5811
-- ZeroPayRel: :5812-5822
-- BinFormAgree: :5823-5912
-- UnFormAgree: :5913-5975
-- Lift12Back: :5976-6053
-- Lift12Out: :6054-6074
-- KFactsNS: :6075-6118
-- KFactsCons: :6119-6156
-- ShapesAgree: :6157-6288
-- BinFrameAgree: :6289-6338
-- UnFrameAgree: :6339-6383
-- BothSameRel: :6384-6391
-- OneSameRel: :6392-6399
-- OneSuccRel: :6400-6422
-- SuccSndRel: :6423-6445
-- ClosedAgree: :6446-6509
-- ShapedAgree: :6548-6575
-- private PairIs: :6666-6669
-- TagAgree: :6670-6698
