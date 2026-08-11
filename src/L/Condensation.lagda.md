# The condensation lemma

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Condensation {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Count
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; Δ₀-sucAt )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; sucAtL
        ; extAt; extAt-in-both
        ; arityTagAtL; arityTagPairAtL
        ; arityTagAtL-adequate; arityTagPairAtL-adequate
        ; tagAtL; tagAtL-adequate; tagPairAtL-adequate; prAtL-adequate
        ; prʟ; prʟ-fst
        ; emptyAt; botClauseAt
        ; tmValAt; envOverAt; domAt-out; pairsIn-out )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum using ( inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( #_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S
```

```agda
-- =====================================================================
-- TEMPLATE.  The lifted atoms and the bounded extension frame.  Every
-- row, including block 1's clause, ends in `extAtB`: "the set at y is
-- exactly the satisfiers of φ that lie in K".  This is the bounded
-- restatement of the delivered `extAt`, and it is what makes a row
-- constrain an EMPTY value (ProbeDD25E1).  Block 1 uses the frame
-- too, so it lives before the per-tower content.
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
```

```agda
-- =====================================================================
-- BLOCK 1, PER-TOWER (Def).  The bounded existential clause, restated
-- from the [LJ-1.15] hardest clause of the twelve-clause table.  The
-- arity tag is a slot N, not a constant, so the whole clause carries no
-- constant at a variable arity.  The J tower's certificate is structural
-- (D-26) and does not use this module.
-- =====================================================================
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
    sucAtL (suc (suc (suc (suc (suc (suc zero)))))) (suc zero)
    ∧̇ prAtL zero (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero)))
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

  -- env hypothesis at env E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  envHyp : Formula S (7 + n)
  envHyp = ∀̇∈ (var zero) envBnd

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
    δ-∧ (Δ₀-sucAtL (suc (suc (suc (suc (suc (suc zero)))))) (suc zero))
        (δ-∧ (Δ₀-prAtL zero (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))))
             (Δ₀-appAt (suc (suc (suc (suc (suc (suc (suc (suc T₁))))))))
                       zero (suc (suc (suc zero)))))

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
  Δ₀-envHyp = δ-∀∈ Δ₀-envBnd

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
existCertAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
existCertAt C T B N = ∃̇ (Clause.existBndAt C T B N)

Σ₁-cert : ∀ {n} (C T B N : Fin n) → Σ₁ (existCertAt C T B N)
Σ₁-cert C T B N = σ-∃ (σ-Δ₀ (Clause.Δ₀-existBndAt C T B N))
```

```agda
-- =====================================================================
-- TEMPLATE.  The erase transfer at the class carrier.  Any formula at
-- the class carrier with zero constants and a Delta-0 witness reaches
-- the parameter-free axis through the delivered erase, and the
-- embedding of the erased form is the original formula as syntax
-- (erase-inv).  The transfer is then two syntactic congs around one
-- abs₀ at the ORIGINAL clause: certify before you place (P-u).  Both
-- towers instantiate this module with their own formulas; nothing here
-- mentions L's Def syntax.
-- =====================================================================
module EraseTransfer {m : ℕ} (φ : Formula S m) (p : countFo φ ≡ 0)
                      (d : Δ₀ φ) (γ : S ^ m) where
  σL₀ : Formula (⊥* {ℓ-suc ℓ}) m
  σL₀ = Cnt.erase φ p

  σL : Formula S m
  σL = embed σL₀

  σL≡ : σL ≡ φ
  σL≡ = Cnt.erase-inv φ p

  σL-eq : ⟨ γ ⊨ φ ⟩ ≡ ⟨ γ ⊨ σL ⟩
  σL-eq = cong (λ ψ → ⟨ γ ⊨ ψ ⟩) (sym σL≡)

  σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-transfer =
      cong (λ ψ → ⟨ γ ⊨ ψ ⟩) σL≡
    ∙ cong ⟨_⟩ (AbsL.abs₀ d γ)
    ∙ cong (λ ψ → ⟨ map fst γ ⊨ᵛ ψ ⟩) (sym σL≡)

  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up h = transport σL-transfer h
```

```agda
-- =====================================================================
-- PER-TOWER (Def).  The two-way decode of the clause at the class
-- carrier, and the instantiation of the erase transfer at the clause.
-- The decode is per-tower content: it reads the layered content out of
-- the satisfied matrix and assembles the matrix from the content.
-- =====================================================================
module ClauseDecode {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  private
    K : Fin (suc n)
    K = zero

  -- OUT: a satisfied matrix gives the layered content.
  existBnd-out : ⟨ γ ⊨ Clause.existBndAt {n} C T B N ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.shapeBnd {n} C T B N ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup K γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.subValHyp {n} C T B N ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.envHyp {n} C T B N ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.extBnd {n} C T B N ⟩
  existBnd-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub hE =
    h c c∈ ar ar∈ a a∈ yc yc∈
      hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc (suc T)))))
                                      (suc (suc (suc zero))) zero
                                      (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)
      ya ya∈ E E∈ hsub hE

  -- IN: the layered content assembles the matrix.
  existBnd-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
                → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
                → ⟨ fst yc ∈ fst (lookup K γ) ⟩
                → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.shapeBnd {n} C T B N ⟩
                → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
                → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
                   → ⟨ fst E ∈ fst (lookup K γ) ⟩
                   → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.subValHyp {n} C T B N ⟩
                   → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.envHyp {n} C T B N ⟩
                   → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.extBnd {n} C T B N ⟩))
    → ⟨ γ ⊨ Clause.existBndAt {n} C T B N ⟩
  existBnd-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval ya ya∈ E E∈ hsub hE =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape
      (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc T)))))
                                 (suc (suc (suc zero))) zero
                                 (yc ∷ a ∷ ar ∷ c ∷ γ)) hval)
      ya E ya∈ E∈ hsub hE

  -- The parameter-free axis without a placement: the clause has no
  -- constant, so erase puts it on the axis and erase-inv says the
  -- embedding gives it back.  The arity is unchanged, so the
  -- environment stays γ.
  module E = EraseTransfer (Clause.existBndAt {n} C T B N) refl
                            (Clause.Δ₀-existBndAt {n} C T B N) γ

  σL : Formula S (suc n)
  σL = E.σL

  σL≡ : σL ≡ Clause.existBndAt {n} C T B N
  σL≡ = E.σL≡

  σL-eq : ⟨ γ ⊨ Clause.existBndAt {n} C T B N ⟩ ≡ ⟨ γ ⊨ σL ⟩
  σL-eq = E.σL-eq

  σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-transfer = E.σL-transfer

  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up = E.σL-up

  -- OUT: the embedded clause at the class carrier gives the layered content.
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.shapeBnd {n} C T B N ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup K γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.subValHyp {n} C T B N ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.envHyp {n} C T B N ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.extBnd {n} C T B N ⟩
  σL-out h = existBnd-out (transport (sym σL-eq) h)

  -- IN: the layered content assembles the embedded clause.
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → ⟨ fst yc ∈ fst (lookup K γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.shapeBnd {n} C T B N ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
             → ⟨ fst E ∈ fst (lookup K γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.subValHyp {n} C T B N ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.envHyp {n} C T B N ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.extBnd {n} C T B N ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in g = transport σL-eq (existBnd-in g)

-- The certificate's transfer: the Sigma-1 form moves up at L.  The
-- shape is the delivered σ₁-up at the per-tower certificate.
module CertTransfer {n : ℕ} (C T B N : Fin n) (γ' : S ^ n) where
  cert-transfer : ⟨ γ' ⊨ existCertAt C T B N ⟩ → ⟨ map fst γ' ⊨ᵛ existCertAt C T B N ⟩
  cert-transfer = AbsL.σ₁-up (Σ₁-cert C T B N) γ'

-- =====================================================================
-- DELIVERED, NEITHER TEMPLATE NOR PER-TOWER.  The tower-landing legs:
-- the graph at the class carrier reads the tower (Lset-only), and the
-- tower writes the graph (Lset-defines).  Both are delivered theorems,
-- ridden here at the class carrier.
-- =====================================================================
ride-only : {n : ℕ} (w b : Fin n) (γ : S ^ n)
          → ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
          → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
ride-only {n} w b γ = Lset-only w b γ

ride-defines : {n : ℕ} (w b : Fin n) (γ : S ^ n)
             → IsOrd (fst (lookup b γ))
             → fst (lookup w γ) ≡ Lset (fst (lookup b γ))
             → ⟨ γ ⊨ LsetGraphAt w b ⟩
ride-defines {n} w b γ = Lset-defines w b γ

-- =====================================================================
-- BLOCK 2, THE BOUNDED SATISFACTION SUBSTRATE.  The eleven remaining
-- table clauses and the bounded code-set description.
--
-- Every row is stated at a generic environment arity m with the bound
-- slot K a parameter of the environment.  The class-carrier instance
-- is m = suc n, K = zero, which reproduces the block-1 layout; the
-- graph instance inside the code-set description is m = 3 + k with
-- C = 2, T = 1, B = 0 and K shifted.  The tag numerals are slots, so
-- every row formula carries countFo = 0 and instantiates the
-- EraseTransfer template.
-- =====================================================================

-- The bounded unary shape, at the frame environment yc ∷ a ∷ ar ∷ c ∷ γ
-- (4 + m): "c = pr ar (pr tag yc)", with the inner code and the tag in
-- K.  This is block 1's shapeBnd with the numeral replaced by a slot.
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
    ∧̇ ∃̇∈ (var (suc K)) (prAtL zero (suc (suc ar)) (suc (suc a))
        ∧̇ appAt (suc (suc T)) zero (suc (suc y))))

Δ₀-subValSuccB : ∀ {n} (T ar a y K : Fin n) → Δ₀ (subValSuccB T ar a y K)
Δ₀-subValSuccB T ar a y K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc ar) zero)
            (δ-∃∈ (δ-∧ (Δ₀-prAtL zero (suc (suc ar)) (suc (suc a)))
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

-- The environment hypotheses, one per frame layout.  Each is
-- "for every member e of E, the bounded environment condition holds".
-- Unary (with the second value slot ya): E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ
-- (6 + m), B at 7 + B, K at 7 + K.
envHypU : ∀ {m} → Fin m → Fin m → Formula S (6 + m)
envHypU {m} B K = ∀̇∈ (var zero)
  (envBndGen {7 + m} zero (suc zero) (suc (suc (suc zero)))
    (suc (suc (suc (suc (suc zero)))))
    (suc (suc (suc (suc (suc (suc (suc K)))))))
    (suc (suc (suc (suc (suc (suc (suc B))))))))

Δ₀-envHypU : ∀ {m} (B K : Fin m) → Δ₀ (envHypU B K)
Δ₀-envHypU {m} B K = δ-∀∈ (Δ₀-envBndGen {7 + m} zero (suc zero)
  (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero)))))
  (suc (suc (suc (suc (suc (suc (suc K)))))))
  (suc (suc (suc (suc (suc (suc (suc B))))))))

-- Constant (no second value slot): E ∷ yc ∷ a ∷ ar ∷ c ∷ γ (5 + m),
-- B at 6 + B, K at 6 + K.
envHypT : ∀ {m} → Fin m → Fin m → Formula S (5 + m)
envHypT {m} B K = ∀̇∈ (var zero)
  (envBndGen {6 + m} zero (suc zero) (suc (suc zero))
    (suc (suc (suc (suc zero))))
    (suc (suc (suc (suc (suc (suc K))))))
    (suc (suc (suc (suc (suc (suc B)))))))

Δ₀-envHypT : ∀ {m} (B K : Fin m) → Δ₀ (envHypT B K)
Δ₀-envHypT {m} B K = δ-∀∈ (Δ₀-envBndGen {6 + m} zero (suc zero)
  (suc (suc zero)) (suc (suc (suc (suc zero))))
  (suc (suc (suc (suc (suc (suc K))))))
  (suc (suc (suc (suc (suc (suc B)))))))

-- Binary (with ya): E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (7 + m),
-- B at 8 + B, K at 8 + K.
envHypB2 : ∀ {m} → Fin m → Fin m → Formula S (7 + m)
envHypB2 {m} B K = ∀̇∈ (var zero)
  (envBndGen {8 + m} zero (suc zero) (suc (suc (suc zero)))
    (suc (suc (suc (suc (suc (suc zero))))))
    (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
    (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))

Δ₀-envHypB2 : ∀ {m} (B K : Fin m) → Δ₀ (envHypB2 B K)
Δ₀-envHypB2 {m} B K = δ-∀∈ (Δ₀-envBndGen {8 + m} zero (suc zero)
  (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero))))))
  (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
  (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))

-- Binary without ya (atom rows): E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (6 + m),
-- B at 7 + B, K at 7 + K.
envHypB2T : ∀ {m} → Fin m → Fin m → Formula S (6 + m)
envHypB2T {m} B K = ∀̇∈ (var zero)
  (envBndGen {7 + m} zero (suc zero) (suc (suc zero))
    (suc (suc (suc (suc (suc zero)))))
    (suc (suc (suc (suc (suc (suc (suc K)))))))
    (suc (suc (suc (suc (suc (suc (suc B))))))))

Δ₀-envHypB2T : ∀ {m} (B K : Fin m) → Δ₀ (envHypB2T B K)
Δ₀-envHypB2T {m} B K = δ-∀∈ (Δ₀-envBndGen {7 + m} zero (suc zero)
  (suc (suc zero)) (suc (suc (suc (suc (suc zero)))))
  (suc (suc (suc (suc (suc (suc (suc K)))))))
  (suc (suc (suc (suc (suc (suc (suc B))))))))

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
module UnFullDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (4 + m)) (sub env body : Formula S (6 + m))
         (γ : S ^ m) where
  unFull-out : ⟨ γ ⊨ unFullAt C T K shape sub env body ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup K γ) ⟩)
    → (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sub ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  unFull-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv =
    h c c∈ ar ar∈ a a∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc T))))
                                      (suc (suc (suc zero))) zero
                                      (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)
      ya ya∈ E E∈ hsub henv

  unFull-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ fst yc ∈ fst (lookup K γ) ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
              → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
              → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
                 → ⟨ fst E ∈ fst (lookup K γ) ⟩
                 → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sub ⟩
                 → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                 → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩))
    → ⟨ γ ⊨ unFullAt C T K shape sub env body ⟩
  unFull-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval ya ya∈ E E∈ hsub henv =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape
      (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc T))))
                                 (suc (suc (suc zero))) zero
                                 (yc ∷ a ∷ ar ∷ c ∷ γ)) hval)
      ya E ya∈ E∈ hsub henv

-- The two-way decode of the full binary frame.
module BinFullDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (5 + m)) (sub env body : Formula S (7 + m))
         (γ : S ^ m) where
  binFull-out : ⟨ γ ⊨ binFullAt C T K shape sub env body ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup K γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup K γ) ⟩)
    → (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ sub ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  binFull-out h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv =
    h c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc (suc T)))))
                                      (suc (suc (suc (suc zero)))) zero
                                      (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) hval)
      ya ya∈ E E∈ hsub henv

  binFull-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
               → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
               → ⟨ fst b ∈ fst (lookup K γ) ⟩ → ⟨ fst yc ∈ fst (lookup K γ) ⟩
               → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
               → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
               → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
                  → ⟨ fst E ∈ fst (lookup K γ) ⟩
                  → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ sub ⟩
                  → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                  → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩))
    → ⟨ γ ⊨ binFullAt C T K shape sub env body ⟩
  binFull-in g c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape hval ya ya∈ E E∈ hsub henv =
    g c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape
      (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc T)))))
                                 (suc (suc (suc (suc zero)))) zero
                                 (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) hval)
      ya E ya∈ E∈ hsub henv

-- The two-way decode of the bare unary frame.
module UnBareDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (4 + m)) (body : Formula S (4 + m))
         (γ : S ^ m) where
  unBare-out : ⟨ γ ⊨ unBareAt C T K shape body ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  unBare-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval =
    h c c∈ ar ar∈ a a∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc T))))
                                      (suc (suc (suc zero))) zero
                                      (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)

  unBare-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ fst yc ∈ fst (lookup K γ) ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩)
    → ⟨ γ ⊨ unBareAt C T K shape body ⟩
  unBare-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape hval

-- The two-way decode of the environment-only unary frame (top).
module UnEnvDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (4 + m)) (env : Formula S (5 + m))
         (body : Formula S (5 + m)) (γ : S ^ m) where
  unEnv-out : ⟨ γ ⊨ unEnvAt C T K shape env body ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → (E : S) (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
    → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  unEnv-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval E E∈ henv =
    h c c∈ ar ar∈ a a∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc T))))
                                      (suc (suc (suc zero))) zero
                                      (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)
      E E∈ henv

  unEnv-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → ⟨ fst yc ∈ fst (lookup K γ) ⟩
             → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
             → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  appAt (suc (suc (suc (suc T)))) (suc (suc (suc zero))) zero ⟩
             → ((E : S) → ⟨ fst E ∈ fst (lookup K γ) ⟩
                → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩))
    → ⟨ γ ⊨ unEnvAt C T K shape env body ⟩
  unEnv-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval E E∈ henv =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape
      hval E E∈ henv

-- The two-way decode of the environment-only binary frame (the atom
-- rows).
module BinEnvDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (5 + m)) (env : Formula S (6 + m))
         (body : Formula S (6 + m)) (γ : S ^ m) where
  binEnv-out : ⟨ γ ⊨ binEnvAt C T K shape env body ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup K γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → (E : S) (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  binEnv-out h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv =
    h c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc (suc T)))))
                                      (suc (suc (suc (suc zero)))) zero
                                      (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) hval)
      E E∈ henv

  binEnv-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ fst b ∈ fst (lookup K γ) ⟩ → ⟨ fst yc ∈ fst (lookup K γ) ⟩
              → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
              → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (suc (suc (suc (suc (suc T))))) (suc (suc (suc (suc zero)))) zero ⟩
              → ((E : S) → ⟨ fst E ∈ fst (lookup K γ) ⟩
                 → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                 → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩))
    → ⟨ γ ⊨ binEnvAt C T K shape env body ⟩
  binEnv-in g c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape hval E E∈ henv =
    g c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape
      hval E E∈ henv

-- The propositional body: the second value yb is bound in K, its
-- subvalue is read, and the operation speaks of the recorded value,
-- the first and the second subvalues.
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
    ∧̇ ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc B)))))))))
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
-- Delta-0 premise of the story's step clause.
-- =====================================================================
keyArBnum : ∀ {n} → Fin n → ℕ → Fin n → Formula S n
keyArBnum c k K =
  ∃̇∈ (var K) (∃̇∈ (var (suc K))
  ((var zero ≐ con (numeralL k))
  ∧̇ prAtL (suc (suc c)) zero (suc zero)))

Δ₀-keyArBnum : ∀ {n} (c : Fin n) (k : ℕ) (K : Fin n) → Δ₀ (keyArBnum c k K)
Δ₀-keyArBnum c k K =
  δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc (suc c)) zero (suc zero))))

tagBnum : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula S n
tagBnum s k x K =
  ∃̇∈ (var K) ((var zero ≐ con (numeralL k))
            ∧̇ prAtL (suc s) zero (suc x))

Δ₀-tagBnum : ∀ {n} (s : Fin n) (k : ℕ) (x K : Fin n) → Δ₀ (tagBnum s k x K)
Δ₀-tagBnum s k x K = δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc s) zero (suc x)))

-- The bounded binary shape with a numeral tag, at the closedness
-- environment b ∷ a ∷ ar ∷ c ∷ γ (4 + m).
arTagPairBnum : ∀ {m} → ℕ → Fin m → Formula S (4 + m)
arTagPairBnum k K =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
  (prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K)))))))
          ((var (suc zero) ≐ con (numeralL k))
          ∧̇ prAtL (suc (suc zero)) (suc zero) zero
          ∧̇ prAtL zero (suc (suc (suc (suc zero)))) (suc (suc (suc zero))))))

Δ₀-arTagPairBnum : ∀ {m} (k : ℕ) (K : Fin m) → Δ₀ (arTagPairBnum k K)
Δ₀-arTagPairBnum k K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) zero)
            (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-prAtL (suc (suc zero)) (suc zero) zero)
                                       (Δ₀-prAtL zero (suc (suc (suc (suc zero))))
                                                 (suc (suc (suc zero)))))))))

-- The bounded unary shape with a numeral tag, at the closedness
-- environment a ∷ ar ∷ c ∷ γ (3 + m).
arTagBnum : ∀ {m} → ℕ → Fin m → Formula S (3 + m)
arTagBnum k K =
  ∃̇∈ (var (suc (suc (suc K))))
  (prAtL (suc (suc (suc zero))) (suc (suc zero)) zero
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc K)))))
        (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
          ((var zero ≐ con (numeralL k))
          ∧̇ prAtL (suc zero) zero (suc (suc zero)))))

Δ₀-arTagBnum : ∀ {m} (k : ℕ) (K : Fin m) → Δ₀ (arTagBnum k K)
Δ₀-arTagBnum k K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc zero))) (suc (suc zero)) zero)
            (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero (suc (suc zero)))))))

-- The bounded shape frames for closedness.
binShapeB : ∀ {m} → Fin m → ℕ → Fin m → Formula S (4 + m) → Formula S m
binShapeB C k K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
  (∀̇∈ (var (suc (suc (suc K))))
      (arTagPairBnum k K ⇒̇ rel))))

Δ₀-binShapeB : ∀ {m} (C : Fin m) (k : ℕ) (K : Fin m) (rel : Formula S (4 + m))
             → Δ₀ rel → Δ₀ (binShapeB C k K rel)
Δ₀-binShapeB C k K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagPairBnum k K) drel))))

unShapeB : ∀ {m} → Fin m → ℕ → Fin m → Formula S (3 + m) → Formula S m
unShapeB C k K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (suc (suc K)))
  (arTagBnum k K ⇒̇ rel)))

Δ₀-unShapeB : ∀ {m} (C : Fin m) (k : ℕ) (K : Fin m) (rel : Formula S (3 + m))
            → Δ₀ rel → Δ₀ (unShapeB C k K rel)
Δ₀-unShapeB C k K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagBnum k K) drel)))

bothSameB : ∀ {m} → Fin m → Formula S (4 + m)
bothSameB C =
  appAt (suc (suc (suc (suc C)))) (suc (suc zero)) (suc zero)
  ∧̇ appAt (suc (suc (suc (suc C)))) (suc (suc zero)) zero

Δ₀-bothSameB : ∀ {m} (C : Fin m) → Δ₀ (bothSameB C)
Δ₀-bothSameB C =
  δ-∧ (Δ₀-appAt (suc (suc (suc (suc C)))) (suc (suc zero)) (suc zero))
      (Δ₀-appAt (suc (suc (suc (suc C)))) (suc (suc zero)) zero)

oneSameB : ∀ {m} → Fin m → Formula S (3 + m)
oneSameB C = appAt (suc (suc (suc C))) (suc (suc zero)) (suc zero)

Δ₀-oneSameB : ∀ {m} (C : Fin m) → Δ₀ (oneSameB C)
Δ₀-oneSameB C = Δ₀-appAt (suc (suc (suc C))) (suc (suc zero)) (suc zero)

oneSuccB : ∀ {m} → Fin m → Fin m → Formula S (3 + m)
oneSuccB C K =
  ∃̇∈ (var (suc (suc (suc K))))
  (sucAtL (suc (suc zero)) zero
  ∧̇ appAt (suc (suc (suc (suc C)))) zero (suc zero))

Δ₀-oneSuccB : ∀ {m} (C K : Fin m) → Δ₀ (oneSuccB C K)
Δ₀-oneSuccB C K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc (suc zero)) zero)
            (Δ₀-appAt (suc (suc (suc (suc C)))) zero (suc zero)))

succSndB : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
succSndB C K =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
  (sucAtL (suc (suc (suc zero))) zero
  ∧̇ appAt (suc (suc (suc (suc (suc C))))) zero (suc zero))

Δ₀-succSndB : ∀ {m} (C K : Fin m) → Δ₀ (succSndB C K)
Δ₀-succSndB C K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc (suc (suc zero))) zero)
            (Δ₀-appAt (suc (suc (suc (suc (suc C))))) zero (suc zero)))

closedB : ∀ {m} → Fin m → Fin m → Formula S m
closedB C K =
  binShapeB C 2 K (bothSameB C)
  ∧̇ (binShapeB C 3 K (bothSameB C)
  ∧̇ (binShapeB C 4 K (bothSameB C)
  ∧̇ (unShapeB C 5 K (oneSameB C)
  ∧̇ (unShapeB C 8 K (oneSuccB C K)
  ∧̇ (unShapeB C 9 K (oneSuccB C K)
  ∧̇ (binShapeB C 10 K (succSndB C K)
  ∧̇ binShapeB C 11 K (succSndB C K)))))))

Δ₀-closedB : ∀ {m} (C K : Fin m) → Δ₀ (closedB C K)
Δ₀-closedB C K =
  δ-∧ (Δ₀-binShapeB C 2 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-binShapeB C 3 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-binShapeB C 4 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-unShapeB C 5 K (oneSameB C) (Δ₀-oneSameB C))
      (δ-∧ (Δ₀-unShapeB C 8 K (oneSuccB C K) (Δ₀-oneSuccB C K))
      (δ-∧ (Δ₀-unShapeB C 9 K (oneSuccB C K) (Δ₀-oneSuccB C K))
      (δ-∧ (Δ₀-binShapeB C 10 K (succSndB C K) (Δ₀-succSndB C K))
           (Δ₀-binShapeB C 11 K (succSndB C K) (Δ₀-succSndB C K))))))))

-- The bounded shape forms for shapedness, at c ∷ γ (1 + m).
binFormB : ∀ {m} → ℕ → Fin m → Formula S (4 + m) → Formula S (1 + m)
binFormB k K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K))) (∃̇∈ (var (suc (suc (suc K))))
  (arTagPairBnum k K ∧̇ rel)))

Δ₀-binFormB : ∀ {m} (k : ℕ) (K : Fin m) (rel : Formula S (4 + m))
            → Δ₀ rel → Δ₀ (binFormB k K rel)
Δ₀-binFormB k K rel drel =
  δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-arTagPairBnum k K) drel)))

unFormB : ∀ {m} → ℕ → Fin m → Formula S (3 + m) → Formula S (1 + m)
unFormB k K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (suc (suc K)))
  (arTagBnum k K ∧̇ rel))

Δ₀-unFormB : ∀ {m} (k : ℕ) (K : Fin m) (rel : Formula S (3 + m))
           → Δ₀ rel → Δ₀ (unFormB k K rel)
Δ₀-unFormB k K rel drel =
  δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-arTagBnum k K) drel))

isTmB : ∀ {m} → Fin (4 + m) → Fin m → Fin m → Formula S (4 + m)
isTmB t A K =
  ∃̇∈ (var (suc (suc (suc (suc K)))))
  (tagBnum (suc t) 0 zero
             (suc (suc (suc (suc (suc K)))))
  ∧̇ (var zero ∈̇ var (suc (suc (suc (suc (suc A)))))))

Δ₀-isTmB : ∀ {m} (t : Fin (4 + m)) (A K : Fin m) → Δ₀ (isTmB t A K)
Δ₀-isTmB t A K =
  δ-∃∈ (δ-∧ (Δ₀-tagBnum (suc t) 0 zero
                          (suc (suc (suc (suc (suc K)))))) δ-∈)

bothTmB : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
bothTmB A K = isTmB (suc zero) A K ∧̇ isTmB zero A K

Δ₀-bothTmB : ∀ {m} (A K : Fin m) → Δ₀ (bothTmB A K)
Δ₀-bothTmB A K = δ-∧ (Δ₀-isTmB (suc zero) A K) (Δ₀-isTmB zero A K)

fstTmB : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
fstTmB A K = isTmB (suc zero) A K

Δ₀-fstTmB : ∀ {m} (A K : Fin m) → Δ₀ (fstTmB A K)
Δ₀-fstTmB A K = Δ₀-isTmB (suc zero) A K

shapesB : ∀ {m} → Fin m → Fin m → Formula S (1 + m)
shapesB A K =
  binFormB 0 K (bothTmB A K)
  ∨̇ (binFormB 1 K (bothTmB A K)
  ∨̇ (binFormB 2 K ⊤̇
  ∨̇ (binFormB 3 K ⊤̇
  ∨̇ (binFormB 4 K ⊤̇
  ∨̇ (unFormB 5 K ⊤̇
  ∨̇ (unFormB 6 K (var zero ≐ con (numeralL 0))
  ∨̇ (unFormB 7 K (var zero ≐ con (numeralL 0))
  ∨̇ (unFormB 8 K ⊤̇
  ∨̇ (unFormB 9 K ⊤̇
  ∨̇ (binFormB 10 K (fstTmB A K)
  ∨̇ binFormB 11 K (fstTmB A K)))))))))))

Δ₀-shapesB : ∀ {m} (A K : Fin m) → Δ₀ (shapesB A K)
Δ₀-shapesB A K =
  δ-∨ (Δ₀-binFormB 0 K (bothTmB A K) (Δ₀-bothTmB A K))
      (δ-∨ (Δ₀-binFormB 1 K (bothTmB A K) (Δ₀-bothTmB A K))
      (δ-∨ (Δ₀-binFormB 2 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormB 3 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormB 4 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormB 5 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormB 6 K (var zero ≐ con (numeralL 0)) δ-≐)
      (δ-∨ (Δ₀-unFormB 7 K (var zero ≐ con (numeralL 0)) δ-≐)
      (δ-∨ (Δ₀-unFormB 8 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormB 9 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormB 10 K (fstTmB A K) (Δ₀-fstTmB A K))
           (Δ₀-binFormB 11 K (fstTmB A K) (Δ₀-fstTmB A K))))))))))))

shapedB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
shapedB C A K = ∀̇∈ (var C) (shapesB A K)

Δ₀-shapedB : ∀ {m} (C A K : Fin m) → Δ₀ (shapedB C A K)
Δ₀-shapedB C A K = δ-∀∈ (Δ₀-shapesB A K)

hasWitnessB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
hasWitnessB A x K =
  ∃̇∈ (var K) ((var (suc x) ∈̇ var zero)
            ∧̇ (closedB zero (suc K) ∧̇ shapedB zero (suc A) (suc K)))

Δ₀-hasWitnessB : ∀ {m} (A x K : Fin m) → Δ₀ (hasWitnessB A x K)
Δ₀-hasWitnessB A x K =
  δ-∃∈ (δ-∧ δ-∈ (δ-∧ (Δ₀-closedB zero (suc K))
                     (Δ₀-shapedB zero (suc A) (suc K))))

isCodeB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
isCodeB c w K = keyArBnum c 1 K ∧̇ hasWitnessB w c K

Δ₀-isCodeB : ∀ {m} (c w K : Fin m) → Δ₀ (isCodeB c w K)
Δ₀-isCodeB c w K =
  δ-∧ (Δ₀-keyArBnum c 1 K) (Δ₀-hasWitnessB w c K)

domB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
domB f d K =
  ∀̇∈ (var K)
  (((∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))
      ⇒̇ (var zero ∈̇ var (suc d)))
  ∧̇ ((var zero ∈̇ var (suc d))
      ⇒̇ (∃̇∈ (var (suc K)) (appAt (suc (suc f)) (suc zero) zero))))

Δ₀-domB : ∀ {m} (f d K : Fin m) → Δ₀ (domB f d K)
Δ₀-domB f d K =
  δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt (suc (suc f)) (suc zero) zero)) δ-∈)
            (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt (suc (suc f)) (suc zero) zero))))

-- The bounded one-entry environment and the bounded definable-subset
-- condition, with the constant tag as the numeral 0.  At the
-- environment E ∷ x' ∷ γ (2 + m): "E is the set of exactly the one
-- entry z' = pr #0 x'", with the values in K.
envOneBnd : ∀ {m} → Fin m → Fin m → Formula S (2 + m)
envOneBnd v K =
  extAtB zero (suc (suc K))
  (tagBnum zero 0 (suc (suc zero)) (suc (suc (suc K))))

Δ₀-envOneBnd : ∀ {m} (v K : Fin m) → Δ₀ (envOneBnd v K)
Δ₀-envOneBnd v K =
  Δ₀-extAtB zero (suc (suc K)) _
  (Δ₀-tagBnum zero 0 (suc (suc zero)) (suc (suc (suc K))))

DefinesB : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S m
DefinesB x w v K =
  extAtB x K
  ((var zero ∈̇ var (suc w))
  ∧̇ ∃̇∈ (var (suc K)) (envOneBnd v K
        ∧̇ (var zero ∈̇ var (suc (suc v)))))

Δ₀-DefinesB : ∀ {m} (x w v K : Fin m) → Δ₀ (DefinesB x w v K)
Δ₀-DefinesB x w v K =
  Δ₀-extAtB x K _
    (δ-∧ δ-∈ (δ-∃∈ (δ-∧ (Δ₀-envOneBnd v K) δ-∈)))

-- =====================================================================
-- THE ERASE TRANSFER AT EACH ROW, AND THE SIGMA-1 CERTIFICATES.
-- Every row is constant-free, so each instantiates the delivered
-- EraseTransfer template with refl.  The two-way decode at the class
-- carrier is the row's frame decode composed with the transfer.
-- =====================================================================
module RowTransfer {m : ℕ} (φ : Formula S m) (p : countFo φ ≡ 0)
         (d : Δ₀ φ) (γ : S ^ m) where
  module E = EraseTransfer φ p d γ
  σL : Formula S m
  σL = E.σL
  σL≡ : σL ≡ φ
  σL≡ = E.σL≡
  σL-eq : ⟨ γ ⊨ φ ⟩ ≡ ⟨ γ ⊨ σL ⟩
  σL-eq = E.σL-eq
  σL-transfer : ⟨ γ ⊨ σL ⟩ ≡ ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-transfer = E.σL-transfer
  σL-up : ⟨ γ ⊨ σL ⟩ → ⟨ map fst γ ⊨ᵛ σL ⟩
  σL-up = E.σL-up

module RowDecode {m : ℕ} {L R : Type (ℓ-suc ℓ)}
         (φ : Formula S m) (p : countFo φ ≡ 0) (d : Δ₀ φ) (γ : S ^ m)
         (out : ⟨ γ ⊨ φ ⟩ → L → R) (rin : (L → R) → ⟨ γ ⊨ φ ⟩) where
  module T = RowTransfer φ p d γ
  open T
  σL-out : ⟨ γ ⊨ σL ⟩ → L → R
  σL-out = λ h x → out (transport (sym σL-eq) h) x
  σL-in : (L → R) → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (rin g)
module BotRow {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Bot.botBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  d : Δ₀ φ
  d = Bot.Δ₀-botBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  module D = UnBareDecode {suc n} (suc C) (suc T) zero
              (arTagB (suc N) zero)
              (emptyB zero (suc (suc (suc (suc zero))))) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ emptyB zero (suc (suc (suc (suc zero)))) ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval →
    D.unBare-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (suc (suc (suc (suc (suc T))))) (suc (suc (suc zero))) zero ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ emptyB zero (suc (suc (suc (suc zero)))) ⟩)
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.unBare-in g)
  botCertAt : Formula S n
  botCertAt = ∃̇ φ
  Σ₁-botCertAt : Σ₁ botCertAt
  Σ₁-botCertAt = σ-∃ (σ-Δ₀ d)
module TopRow {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Top.topBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  d : Δ₀ φ
  d = Top.Δ₀-topBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  module D = UnEnvDecode {suc n} (suc C) (suc T) zero
              (arTagB (suc N) zero) (envHypT (suc B) zero)
              (sameB (suc zero) zero (suc (suc (suc (suc (suc zero)))))) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (E : S) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypT (suc B) zero ⟩
    → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sameB (suc zero) zero (suc (suc (suc (suc (suc zero))))) ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval E E∈ henv →
    D.unEnv-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval E E∈ henv
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (suc (suc (suc (suc (suc T))))) (suc (suc (suc zero))) zero ⟩
          → ((E : S) → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypT (suc B) zero ⟩
             → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sameB (suc zero) zero (suc (suc (suc (suc (suc zero))))) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.unEnv-in g)
  topCertAt : Formula S n
  topCertAt = ∃̇ φ
  Σ₁-topCertAt : Σ₁ topCertAt
  Σ₁-topCertAt = σ-∃ (σ-Δ₀ d)
module NegRow {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Neg.negBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  d : Δ₀ φ
  d = Neg.Δ₀-negBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  module D = UnFullDecode {suc n} (suc C) (suc T) zero
              (arTagB (suc N) zero)
              (Neg.subN {suc n} (suc C) (suc T) (suc B) (suc N) zero)
              (envHypU (suc B) zero)
              (Neg.bodyN {suc n} (suc C) (suc T) (suc B) (suc N) zero) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup zero γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Neg.subN {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypU (suc B) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Neg.bodyN {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv →
    D.unFull-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩
             → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Neg.subN {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypU (suc B) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Neg.bodyN {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.unFull-in g)
  negCertAt : Formula S n
  negCertAt = ∃̇ φ
  Σ₁-negCertAt : Σ₁ negCertAt
  Σ₁-negCertAt = σ-∃ (σ-Δ₀ d)
module ForallRow {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Forall.forallBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  d : Δ₀ φ
  d = Forall.Δ₀-forallBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  module D = UnFullDecode {suc n} (suc C) (suc T) zero
              (arTagB (suc N) zero)
              (Forall.subF {suc n} (suc C) (suc T) (suc B) (suc N) zero)
              (envHypU (suc B) zero)
              (Forall.bodyF {suc n} (suc C) (suc T) (suc B) (suc N) zero) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup zero γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Forall.subF {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypU (suc B) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Forall.bodyF {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv →
    D.unFull-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩
             → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Forall.subF {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypU (suc B) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Forall.bodyF {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.unFull-in g)
  forallCertAt : Formula S n
  forallCertAt = ∃̇ φ
  Σ₁-forallCertAt : Σ₁ forallCertAt
  Σ₁-forallCertAt = σ-∃ (σ-Δ₀ d)
module AndRow {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = And.andBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  d : Δ₀ φ
  d = And.Δ₀-andBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  module D = BinFullDecode {suc n} (suc C) (suc T) zero
              (arTagPairB (suc N) zero)
              (And.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero)
              (envHypB2 (suc B) zero)
              (propBodyB (suc T) zero (And.opA {suc n} (suc C) (suc T) (suc B) (suc N) zero)) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup zero γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup zero γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ And.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (And.opA {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩
             → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ And.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (And.opA {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.binFull-in g)
  andCertAt : Formula S n
  andCertAt = ∃̇ φ
  Σ₁-andCertAt : Σ₁ andCertAt
  Σ₁-andCertAt = σ-∃ (σ-Δ₀ d)
module OrRow {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Or.orBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  d : Δ₀ φ
  d = Or.Δ₀-orBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  module D = BinFullDecode {suc n} (suc C) (suc T) zero
              (arTagPairB (suc N) zero)
              (Or.subO {suc n} (suc C) (suc T) (suc B) (suc N) zero)
              (envHypB2 (suc B) zero)
              (propBodyB (suc T) zero (Or.opO {suc n} (suc C) (suc T) (suc B) (suc N) zero)) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup zero γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup zero γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Or.subO {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Or.opO {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩
             → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Or.subO {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Or.opO {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.binFull-in g)
  orCertAt : Formula S n
  orCertAt = ∃̇ φ
  Σ₁-orCertAt : Σ₁ orCertAt
  Σ₁-orCertAt = σ-∃ (σ-Δ₀ d)
module ImpRow {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Imp.impBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  d : Δ₀ φ
  d = Imp.Δ₀-impBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero
  module D = BinFullDecode {suc n} (suc C) (suc T) zero
              (arTagPairB (suc N) zero)
              (Imp.subI {suc n} (suc C) (suc T) (suc B) (suc N) zero)
              (envHypB2 (suc B) zero)
              (propBodyB (suc T) zero (Imp.opI {suc n} (suc C) (suc T) (suc B) (suc N) zero)) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup zero γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup zero γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Imp.subI {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Imp.opI {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩
             → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Imp.subI {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Imp.opI {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.binFull-in g)
  impCertAt : Formula S n
  impCertAt = ∃̇ φ
  Σ₁-impCertAt : Σ₁ impCertAt
  Σ₁-impCertAt = σ-∃ (σ-Δ₀ d)
module MemRow {n : ℕ} (C T B N t0 t1 : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Mem.memBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  d : Δ₀ φ
  d = Mem.Δ₀-memBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  module D = BinEnvDecode {suc n} (suc C) (suc T) zero
              (arTagPairB (suc N) zero) (envHypB2T (suc B) zero)
              (Mem.bodyM {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup zero γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (E : S) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2T (suc B) zero ⟩
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Mem.bodyM {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv →
    D.binEnv-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (suc (suc (suc (suc (suc (suc T)))))) (suc (suc (suc (suc zero)))) zero ⟩
          → ((E : S) → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2T (suc B) zero ⟩
             → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Mem.bodyM {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.binEnv-in g)
  memCertAt : Formula S n
  memCertAt = ∃̇ φ
  Σ₁-memCertAt : Σ₁ memCertAt
  Σ₁-memCertAt = σ-∃ (σ-Δ₀ d)
module EqRow {n : ℕ} (C T B N t0 t1 : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = Eq.eqBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  d : Δ₀ φ
  d = Eq.Δ₀-eqBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  module D = BinEnvDecode {suc n} (suc C) (suc T) zero
              (arTagPairB (suc N) zero) (envHypB2T (suc B) zero)
              (Eq.bodyE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup zero γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (E : S) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2T (suc B) zero ⟩
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Eq.bodyE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv →
    D.binEnv-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (suc (suc (suc (suc (suc (suc T)))))) (suc (suc (suc (suc zero)))) zero ⟩
          → ((E : S) → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2T (suc B) zero ⟩
             → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Eq.bodyE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.binEnv-in g)
  eqCertAt : Formula S n
  eqCertAt = ∃̇ φ
  Σ₁-eqCertAt : Σ₁ eqCertAt
  Σ₁-eqCertAt = σ-∃ (σ-Δ₀ d)
module AllInRow {n : ℕ} (C T B N t0 t1 : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = AllIn.allInBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  d : Δ₀ φ
  d = AllIn.Δ₀-allInBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  module D = BinFullDecode {suc n} (suc C) (suc T) zero
              (arTagPairB (suc N) zero)
              (AllIn.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1))
              (envHypB2 (suc B) zero)
              (bndBodyAll (suc B) zero (suc t0) (suc t1)) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup zero γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup zero γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ AllIn.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyAll (suc B) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩
             → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ AllIn.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyAll (suc B) zero (suc t0) (suc t1) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.binFull-in g)
  allInCertAt : Formula S n
  allInCertAt = ∃̇ φ
  Σ₁-allInCertAt : Σ₁ allInCertAt
  Σ₁-allInCertAt = σ-∃ (σ-Δ₀ d)
module ExInRow {n : ℕ} (C T B N t0 t1 : Fin n) (γ : S ^ suc n) where
  φ : Formula S (suc n)
  φ = ExIn.exInBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  d : Δ₀ φ
  d = ExIn.Δ₀-exInBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1)
  module D = BinFullDecode {suc n} (suc C) (suc T) zero
              (arTagPairB (suc N) zero)
              (ExIn.subE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1))
              (envHypB2 (suc B) zero)
              (bndBodyEx (suc B) zero (suc t0) (suc t1)) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup zero γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup zero γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup zero γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ExIn.subE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyEx (suc B) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩
             → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ExIn.subE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyEx (suc B) zero (suc t0) (suc t1) ⟩))
    → ⟨ γ ⊨ σL ⟩
  σL-in = λ g → transport σL-eq (D.binFull-in g)
  exInCertAt : Formula S n
  exInCertAt = ∃̇ φ
  Σ₁-exInCertAt : Σ₁ exInCertAt
  Σ₁-exInCertAt = σ-∃ (σ-Δ₀ d)
module SatGraphB {n : ℕ} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where
  private
    K' : Fin (11 + n)
    K' = suc (suc (suc (suc (suc (suc K)))))

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
          ∧̇ (closedB zero (suc (suc (suc (suc (suc (suc K))))))
          ∧̇ (domB (suc zero) (suc (suc zero))
                   (suc (suc (suc (suc (suc (suc K))))))
          ∧̇ (appAt (suc zero) (suc (suc (suc (suc zero))))
                   (suc (suc (suc zero)))
          ∧̇ twelveB))))))

  Δ₀-satGraphB : Δ₀ satGraphB
  Δ₀-satGraphB =
    δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐
      (δ-∧ (Δ₀-closedB zero (suc (suc (suc (suc (suc (suc K)))))))
      (δ-∧ (Δ₀-domB (suc zero) (suc (suc zero))
                    (suc (suc (suc (suc (suc (suc K)))))))
      (δ-∧ (Δ₀-appAt (suc zero) (suc (suc (suc (suc zero))))
                     (suc (suc (suc zero))))
           Δ₀-twelveB))))))

-- The bounded code-set description: the three leaves of DefBody,
-- bounded by K, at the leaf environment v' ∷ c' ∷ x ∷ δ.
DefBodyB : ∀ {n} → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Formula S (suc (suc (suc (5 + n))))
DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 =
  isCodeB (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
  ∧̇ (SatGraphB.satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    ∧̇ DefinesB (suc (suc zero)) (suc (suc (suc w))) zero (suc (suc (suc K))))

Δ₀-DefBodyB : ∀ {n} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  → Δ₀ (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)
Δ₀-DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 =
  δ-∧ (Δ₀-isCodeB (suc zero) (suc (suc (suc w))) (suc (suc (suc K))))
      (δ-∧ (SatGraphB.Δ₀-satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
              t0 t1)
           (Δ₀-DefinesB (suc (suc zero)) (suc (suc (suc w))) zero
                        (suc (suc (suc K)))))
```

```agda
-- =====================================================================
-- BLOCK 3, THE BOUNDED STEP AND GRAPH MATRICES.  The bounded
-- restatements of the delivered StepAt, ApproxAt and LsetGraphAt
-- readings (src/L/Coding/Sequence.lagda.md:119-120, :173-176,
-- :182-184), at a variable environment with the bound K as a slot.
--
-- The step matrix is generic in the leaf content ψ, exactly the shape
-- [LJ-1.34-R] measured at 0.0072 s per line (src/ProbeDD25D5.agda),
-- with K a parameter instead of the fixed class-carrier slot.  The
-- concrete leaf is the bounded code-set description DefBodyB above.
-- The approximation and graph matrices ride the same step frame; each
-- nesting level shifts the leaf arity, so each carries its own leaf
-- content.
--
-- Slot convention: a module at arity m states its formula at arity m
-- with its parameters as direct slots; the class-carrier instance is
-- at arity suc n with the parameters lifted and K = 0.  This is the
-- rows' convention above.
-- =====================================================================
module StepB {m : ℕ} (ψ : Formula S (suc (suc (suc (4 + m)))))
            (v b f K : Fin m) where
  -- At γ : S ^ m, the body is at d ∷ w ∷ c ∷ z ∷ γ (4 + m); the leaf
  -- is at v' ∷ c' ∷ x ∷ δ with δ = d ∷ w ∷ c ∷ z ∷ γ (5 + m).  The
  -- bounds are: c ∈ b, w ∈ K, d ∈ K for the step witnesses; c' ∈ K
  -- and v' ∈ K for the leaf's code and value.
  leafB : Formula S (4 + m)
  leafB =
    extAtB zero (suc (suc (suc (suc K))))
      (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K))))))) ψ))

  bodyB : Formula S (4 + m)
  bodyB =
    (var (suc (suc zero)) ∈̇ var (suc (suc (suc (suc b)))))
    ∧̇ ( appAt (suc (suc (suc (suc f)))) (suc (suc zero)) (suc zero)
       ∧̇ ( leafB ∧̇ (var (suc (suc (suc zero))) ∈̇ var zero) ) )

  witB : Formula S (suc m)
  witB =
    ∃̇∈ (var (suc b))
      (∃̇∈ (var (suc (suc K)))
        (∃̇∈ (var (suc (suc (suc K))))
          bodyB))

  stepBndAt : Formula S m
  stepBndAt = extAtB v K witB

  Δ₀-leafB : Δ₀ ψ → Δ₀ leafB
  Δ₀-leafB d =
    Δ₀-extAtB zero (suc (suc (suc (suc K))))
      (∃̇∈ (var (suc (suc (suc (suc (suc K))))))
        (∃̇∈ (var (suc (suc (suc (suc (suc (suc K))))))) ψ))
      (δ-∃∈ (δ-∃∈ d))

  Δ₀-bodyB : Δ₀ ψ → Δ₀ bodyB
  Δ₀-bodyB d =
    δ-∧ δ-∈
      (δ-∧ (Δ₀-appAt (suc (suc (suc (suc f))))
                      (suc (suc zero)) (suc zero))
           (δ-∧ (Δ₀-leafB d) δ-∈))

  Δ₀-stepBndAt : Δ₀ ψ → Δ₀ stepBndAt
  Δ₀-stepBndAt d =
    Δ₀-extAtB v K witB
      (δ-∃∈ (δ-∃∈ (δ-∃∈ (Δ₀-bodyB d))))

-- The concrete step matrix at the class carrier.  The leaf δ is
-- d ∷ w ∷ c ∷ z ∷ γ (5 + n); DefBodyB takes its 16 slots there: the
-- carrier at δ slot 1 (the step's w), the bound at δ slot 4 (the class
-- carrier's K), and the twelve row tags and two term slots as
-- parameters.
module StepAtB {n : ℕ} (v b f : Fin n)
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n)) where
  ψ : Formula S (suc (suc (suc (5 + n))))
  ψ = DefBodyB (suc zero) (suc (suc (suc (suc zero))))
        N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1

  stepBndAt : Formula S (suc n)
  stepBndAt = StepB.stepBndAt {suc n} ψ (suc v) (suc b) (suc f) zero

  Δ₀-stepBndAt : Δ₀ stepBndAt
  Δ₀-stepBndAt =
    StepB.Δ₀-stepBndAt {suc n} ψ (suc v) (suc b) (suc f) zero
      (Δ₀-DefBodyB (suc zero) (suc (suc (suc (suc zero))))
        N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)

-- The bounded approximation and graph matrices.  ApproxAt f a =
-- domAt f a ∧̇ ∀̇ (∀̇ (appAt (sh2 f) 1 0 ⇒̇ Step zero (suc zero)
-- (sh2 f))); LsetGraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step
-- (suc w) (suc b) zero).  The bounded restatements bound the two
-- domain variables and the witness function by K, and replace the
-- inner step by the bounded step at the same K shifted past the
-- binders.  Each nesting level shifts the leaf arity, so each matrix
-- carries its own leaf content.
module ApproxB {m : ℕ} (ψ' : Formula S (suc (suc (suc (6 + m)))))
                (f a K : Fin m) where
  module S = StepB {2 + m} ψ' zero (suc zero) (suc (suc f)) (suc (suc K))

  approxBndAt : Formula S m
  approxBndAt =
    domB f a K
    ∧̇ ∀̇∈ (var K)
        (∀̇∈ (var (suc K))
          (appAt (suc (suc f)) (suc zero) zero
          ⇒̇ S.stepBndAt))

  Δ₀-approxBndAt : Δ₀ ψ' → Δ₀ approxBndAt
  Δ₀-approxBndAt d =
    δ-∧ (Δ₀-domB f a K)
        (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (suc f))
                                    (suc zero) zero)
                         (S.Δ₀-stepBndAt d))))

module GraphB {m : ℕ} (ψs : Formula S (suc (suc (suc (5 + m)))))
              (ψa : Formula S (suc (suc (suc (7 + m)))))
              (w b K : Fin m) where
  module A = ApproxB {1 + m} ψa zero (suc b) (suc K)
  module S = StepB {1 + m} ψs (suc w) (suc b) zero (suc K)

  graphBndAt : Formula S m
  graphBndAt = ∃̇∈ (var K) (A.approxBndAt ∧̇ S.stepBndAt)

  Δ₀-graphBndAt : Δ₀ ψs → Δ₀ ψa → Δ₀ graphBndAt
  Δ₀-graphBndAt ds da =
    δ-∃∈ (δ-∧ (A.Δ₀-approxBndAt da) (S.Δ₀-stepBndAt ds))
```

```agda
-- =====================================================================
-- THE ROW AGREEMENT (LEG D), AT THE CLASS CARRIER.  The bounded rows
-- against the delivered machine rows, at the satisfaction level.  The
-- site facts are hypotheses, exactly as [LJ-1.34-R] measured: the tag
-- columns hold the numerals, the numerals and the inner codes lie in
-- K, and the subcodes and recorded values of a shaped code lie in K.
-- This is what makes the repaired rows tested (C-35): each row's two
-- directions close only if the row means what the machine's row means.
-- =====================================================================

-- The extension-frame transfer, from ProbeDD25E2: the bounded two-way
-- frame reaches the machine's unbounded two-way frame under a leaf
-- agreement and the satisfiers-in-K site fact.
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
  innerK = (a : S) → ⟨ fst (prʟ (numeralL k) a) ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩

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

  in' : tagEq → numK → innerK → ⟨ γ ⊨ arityTagAtL (suc (suc (suc zero))) (suc (suc zero)) k (suc zero) ⟩
      → ⟨ γ ⊨ arTagB tag K ⟩
  in' te nk ik h = PT.rec squash₁
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
                   (ik a₀))
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
  innerK = (a b : S) → ⟨ fst (prʟ (numeralL k) (prʟ a b)) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

  pairK : Type (ℓ-suc ℓ)
  pairK = (a b : S) → ⟨ fst (prʟ a b) ∈ fst (lookup (suc (suc (suc (suc (suc K))))) γ) ⟩

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
      → ⟨ γ ⊨ arityTagPairAtL (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) k
                               (suc (suc zero)) (suc zero) ⟩
      → ⟨ γ ⊨ arTagPairB tag K ⟩
  in' te nk ik pk h = PT.rec squash₁
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
                   (ik a₀ b₀))
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
                         , ( pk a₀ b₀
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

-- The Bot row agreement at the class carrier.
module BotAgree {n : ℕ} (C T B N : Fin n) (γ : S ^ suc n)
  (tagEq : fst (lookup (suc N) γ) ≡ fst (numeralL 7))
  (numK : ⟨ fst (numeralL 7) ∈ fst (lookup zero γ) ⟩)
  (innerK : (a : S) → ⟨ fst (prʟ (numeralL 7) a) ∈ fst (lookup zero γ) ⟩)
  (codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
           → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ × ⟨ fst a ∈ fst (lookup zero γ) ⟩)
  (valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
         → fst c ≡ pr (fst ar) (pr (# 7) (fst a))
         → ⟨ fst yc ∈ fst (lookup zero γ) ⟩) where

  private
    φB : Formula S (suc n)
    φB = Bot.botBndAt {suc n} (suc C) (suc T) (suc B) (suc N) zero

  bot-out : ⟨ γ ⊨ botClauseAt (suc C) (suc T) ⟩ → ⟨ γ ⊨ φB ⟩
  bot-out h = λ c c∈ ar arK a aK yc ycK shB hc →
    let shD = UnaryShape.out {m = suc n} (suc N) zero 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
        hb = h c c∈ ar a yc shD hc
    in emptyAt→emptyB zero (suc (suc (suc (suc zero)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

  bot-in : ⟨ γ ⊨ φB ⟩ → ⟨ γ ⊨ botClauseAt (suc C) (suc T) ⟩
  bot-in h = λ c c∈ ar a yc shD hc →
    let shEq : fst c ≡ pr (fst ar) (pr (# 7) (fst a))
        shEq = transport (cong fst (arityTagAtL-adequate (suc (suc (suc zero)))
                 (suc (suc zero)) 7 (suc zero) (yc ∷ a ∷ ar ∷ c ∷ γ))) shD
        (arK , aK) = codesK c ar a c∈ shEq
        ycK = valK c ar a yc c∈ shEq
        shB = UnaryShape.in' {m = suc n} (suc N) zero 7 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq numK innerK shD
        hb = h c c∈ ar arK a aK yc ycK shB hc
    in emptyB→emptyAt zero (suc (suc (suc (suc zero)))) (yc ∷ a ∷ ar ∷ c ∷ γ) hb

-- The environment-condition transfer at the B2T layout (the atom rows).
-- The machine's envOverAt at the atom frame environment gives the
-- story's bounded envBndGen, under the witness-in-K site fact.
module EnvB2T {m : ℕ} (B K : Fin m) (γ : S ^ (6 + m)) where
  domWK : Type (ℓ-suc ℓ)
  domWK = (z w y : S) → ⟨ (y ∷ w ∷ z ∷ γ) ⊨ appAt (suc (suc zero)) (suc zero) zero ⟩
        → ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ) ⟩

  over→bnd : domWK
    → (z : S) → ⟨ (z ∷ γ) ⊨ envOverAt zero (suc (suc (suc (suc (suc zero)))))
                                    (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
    → ⟨ (z ∷ γ) ⊨ envBndGen zero (suc zero) (suc (suc zero))
                             (suc (suc (suc (suc (suc zero)))))
                             (suc (suc (suc (suc (suc (suc (suc K)))))))
                             (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
  over→bnd dwk z h =
    ( λ x1 x1∈ x2 x2∈ x3 x3∈ → h .fst x1 x2 x3 )
    , ( λ w w∈ →
          ( λ hw →
              PT.rec (snd (fst w ∈ fst (lookup (suc (suc (suc (suc (suc (suc zero)))))) (w ∷ z ∷ γ))))
                (λ { (y₀ , (y₀∈ , p)) →
                  domAt-out zero (suc (suc (suc (suc (suc zero))))) (z ∷ γ)
                    (h .snd .fst) w y₀
                    (subst ⟨_⟩ (appAt-adequate (suc (suc zero)) (suc zero) zero
                      (y₀ ∷ w ∷ z ∷ γ)) p) })
                hw )
        , ( λ war →
              PT.rec squash₁
                (λ { (y₀ , p) → ∣ y₀ , ( dwk z w y₀ p , p ) ∣₁ })
                (h .snd .fst w .snd war)) )
    , ( λ y1 y1∈ y2 y2∈ p → h .snd .snd .fst y1 y2 p )
    , ( λ s s∈ →
        PT.rec squash₁
          (λ { (u , (v₀ , (u∈ , (v∈ , q)))) →
              ∣ u , (u∈ , ∣ v₀ , (v∈ , subst ⟨_⟩
                    (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (v₀ ∷ u ∷ s ∷ z ∷ γ))) q) ∣₁) ∣₁ })
          (pairsIn-out zero (suc (suc (suc (suc (suc zero)))))
            (suc (suc (suc (suc (suc (suc (suc B))))))) (z ∷ γ)
            (h .snd .snd .snd) s s∈) )

-- The term-value transfer: the bounded tmValB against the machine's
-- tmValAt, under the tag-column facts and the keys-in-K fact.
module TmVal {m : ℕ} (t e v K t0 t1 : Fin m) (γ : S ^ m) where
  t0eq : Type (ℓ-suc ℓ)
  t0eq = fst (lookup t0 γ) ≡ fst (numeralL 0)

  t1eq : Type (ℓ-suc ℓ)
  t1eq = fst (lookup t1 γ) ≡ fst (numeralL 1)

  t0K : Type (ℓ-suc ℓ)
  t0K = ⟨ fst (lookup t0 γ) ∈ fst (lookup K γ) ⟩

  keyK : Type (ℓ-suc ℓ)
  keyK = (k : S) → ⟨ fst k ∈ fst (lookup K γ) ⟩

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
             in ∣ inl (∣ k , ( kk k
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
```
