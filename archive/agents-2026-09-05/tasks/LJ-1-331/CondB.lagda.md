# The condensation lemma

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-331.CondB {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

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
open import V.Model {ℓ} using ( pair-singleton )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; Lset; IsOrd )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; Δ₀-sucAt )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; pairʟ; pairʟ-fst )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; sucAtL; closedAt; domAt
        ; sucAtL-adequate
        ; extAt; extAt-in-both
        ; interAt; unionAt
        ; arityTagAtL; arityTagPairAtL
        ; arityTagAtL-adequate; arityTagPairAtL-adequate
        ; tagAtL; tagAtL-adequate; tagPairAtL-adequate; prAtL-adequate
        ; prʟ; prʟ-fst
        ; binShapeAt; unShapeAt; bothSameAt; oneSameAt; oneSuccAt; succSndAt
        ; binShape-out; binShape-in; unShape-out; unShape-in
        ; emptyAt; botClauseAt
        ; subValAt; subValSuccAt; binClauseAt; propRel
        ; negClauseAt; topClauseAt; forallClauseAt; existClauseAt
        ; body∀; body∃; bodyAll; bodyEx
        ; tmValAt; envSetAt; envOverAt; envOverAt-transport; implAt
        ; atomBody; memClauseAt; eqClauseAt; impClauseAt
        ; allInClauseAt; exInClauseAt
        ; svAt-in; svAt-out; domAt-intro; domAt-out; domAt-in
        ; valuesInAt-in; valuesInAt-out )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Coding.Shape {ℓ}
  using ( isTmAt; shapes; binForm; unForm; bothTm; fstTm; noneB; noneU; zeroPay
        ; shapedAt )
open import L.Coding.CodeSet {ℓ} lem using ( hasWitnessAt; keyArityAtL )
open import L.Coding.Graph {ℓ} lem using ( satGraphAt; twelveAt )
open import L.Coding.Powerset {ℓ} lem using ( isCodeAt; DefBody; DefinesAt; envOneAt )
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
keyArBS : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
keyArBS c tag K =
  ∃̇∈ (var K) (∃̇∈ (var (suc K))
  ((var zero ≐ var (suc (suc tag)))
  ∧̇ prAtL (suc (suc c)) zero (suc zero)))

Δ₀-keyArBS : ∀ {n} (c tag K : Fin n) → Δ₀ (keyArBS c tag K)
Δ₀-keyArBS c tag K =
  δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc (suc c)) zero (suc zero))))

tagBS : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
tagBS s tag x K =
  ∃̇∈ (var K) ((var zero ≐ var (suc tag))
            ∧̇ prAtL (suc s) zero (suc x))

Δ₀-tagBS : ∀ {n} (s tag x K : Fin n) → Δ₀ (tagBS s tag x K)
Δ₀-tagBS s tag x K = δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc s) zero (suc x)))

-- The bounded binary shape with a numeral tag, at the closedness
-- environment b ∷ a ∷ ar ∷ c ∷ γ (4 + m).
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

-- The bounded unary shape with a numeral tag, at the closedness
-- environment a ∷ ar ∷ c ∷ γ (3 + m).
arTagBS : ∀ {m} → Fin m → Fin m → Formula S (3 + m)
arTagBS tag K =
  ∃̇∈ (var (suc (suc (suc K))))
  (prAtL (suc (suc (suc zero))) (suc (suc zero)) zero
  ∧̇ ∃̇∈ (var (suc (suc (suc (suc K)))))
        ((var zero ≐ var (suc (suc (suc (suc (suc tag))))))
        ∧̇ prAtL (suc zero) zero (suc (suc zero))))

Δ₀-arTagBS : ∀ {m} (tag K : Fin m) → Δ₀ (arTagBS tag K)
Δ₀-arTagBS tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL (suc (suc (suc zero))) (suc (suc zero)) zero)
            (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero (suc (suc zero))))))

-- The bounded shape frames for closedness.
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

bothSameB : ∀ {m} → Fin m → Formula S (4 + m)
bothSameB C =
  appAt (suc (suc (suc (suc C)))) (suc (suc zero)) (suc zero)
  ∧̇ appAt (suc (suc (suc (suc C)))) (suc (suc zero)) zero

Δ₀-bothSameB : ∀ {m} (C : Fin m) → Δ₀ (bothSameB C)
Δ₀-bothSameB C =
  δ-∧ (Δ₀-appAt (suc (suc (suc (suc C)))) (suc (suc zero)) (suc zero))
      (Δ₀-appAt (suc (suc (suc (suc C)))) (suc (suc zero)) zero)

oneSameB : ∀ {m} → Fin m → Formula S (3 + m)
oneSameB C = appAt (suc (suc (suc C))) (suc zero) zero

Δ₀-oneSameB : ∀ {m} (C : Fin m) → Δ₀ (oneSameB C)
Δ₀-oneSameB C = Δ₀-appAt (suc (suc (suc C))) (suc zero) zero

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

-- The bounded shape forms for shapedness, at c ∷ γ (1 + m).
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

Δ₀-isTmBS : ∀ {m} (t : Fin (4 + m)) (A K N0 N1 : Fin m)
          → Δ₀ (isTmBS t A K N0 N1)
Δ₀-isTmBS t A K N0 N1 =
  δ-∨ (δ-∃∈ (δ-∧ (Δ₀-tagBS (suc t) (suc (suc (suc (suc (suc N0))))) zero
                          (suc (suc (suc (suc (suc K)))))) δ-∈))
      (δ-∃∈ (δ-∧ (Δ₀-tagBS (suc t) (suc (suc (suc (suc (suc N1))))) zero
                          (suc (suc (suc (suc (suc K)))))) δ-∈))

bothTmBS : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (4 + m)
bothTmBS A K N0 N1 =
  isTmBS (suc zero) A K N0 N1 ∧̇ isTmBS zero A K N0 N1

Δ₀-bothTmBS : ∀ {m} (A K N0 N1 : Fin m) → Δ₀ (bothTmBS A K N0 N1)
Δ₀-bothTmBS A K N0 N1 =
  δ-∧ (Δ₀-isTmBS (suc zero) A K N0 N1) (Δ₀-isTmBS zero A K N0 N1)

fstTmBS : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (4 + m)
fstTmBS A K N0 N1 = isTmBS (suc zero) A K N0 N1

Δ₀-fstTmBS : ∀ {m} (A K N0 N1 : Fin m) → Δ₀ (fstTmBS A K N0 N1)
Δ₀-fstTmBS A K N0 N1 = Δ₀-isTmBS (suc zero) A K N0 N1

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

Δ₀-shapesBS : ∀ {m} (A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            → Δ₀ (shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)
Δ₀-shapesBS A K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
  δ-∨ (Δ₀-binFormBS N0 K (bothTmBS A K N0 N1) (Δ₀-bothTmBS A K N0 N1))
      (δ-∨ (Δ₀-binFormBS N1 K (bothTmBS A K N0 N1) (Δ₀-bothTmBS A K N0 N1))
      (δ-∨ (Δ₀-binFormBS N2 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormBS N3 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormBS N4 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormBS N5 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormBS N6 K (var zero ≐ var (suc (suc (suc N0)))) δ-≐)
      (δ-∨ (Δ₀-unFormBS N7 K (var zero ≐ var (suc (suc (suc N0)))) δ-≐)
      (δ-∨ (Δ₀-unFormBS N8 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-unFormBS N9 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormBS N10 K (fstTmBS A K N0 N1) (Δ₀-fstTmBS A K N0 N1))
           (Δ₀-binFormBS N11 K (fstTmBS A K N0 N1) (Δ₀-fstTmBS A K N0 N1))))))))))))

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
-- condition, with the tag as the N0 slot (the site fact: the slot holds
-- the numeral 0).  At the environment E ∷ x' ∷ γ (2 + m): "E is the set
-- of exactly the one entry z' = pr #0 x'", with the values in K.
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

-- The bounded code-set description: the three leaves of DefBody,
-- bounded by K, at the leaf environment v' ∷ c' ∷ x ∷ δ.
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

Δ₀-DefBodyB : ∀ {n} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  → Δ₀ (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)
Δ₀-DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 =
  δ-∧ (Δ₀-isCodeBS (suc zero) (suc (suc (suc w))) (suc (suc (suc K)))
        (suc (suc (suc N0))) (suc (suc (suc N1)))
        (suc (suc (suc N2))) (suc (suc (suc N3)))
        (suc (suc (suc N4))) (suc (suc (suc N5)))
        (suc (suc (suc N6))) (suc (suc (suc N7)))
        (suc (suc (suc N8))) (suc (suc (suc N9)))
        (suc (suc (suc N10))) (suc (suc (suc N11))))
      (δ-∧ (SatGraphB.Δ₀-satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11
              t0 t1)
           (Δ₀-DefinesBS (suc (suc zero)) (suc (suc (suc w))) zero
                         (suc (suc (suc K))) (suc (suc (suc N0)))))
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
```

```agda
-- =====================================================================
-- THE ROW AGREEMENT (LEG D), PART 2: THE LEAF TRANSFERS.  Each story
-- leaf is the machine's leaf with its witnesses bounded by K.  The
-- machine-to-story direction needs the witness-in-K site facts; the
-- story-to-machine direction drops the bound and is free.  The
-- operation leaves share one frame transfer: the bounded extension
-- frame reaches the machine's extension frame, and the story's
-- operation body IS the machine's body, so the leaves agree by refl.
-- =====================================================================

-- The subvalue transfer: subValB (bounded witness in K) against
-- subValAt (unbounded witness).  Restated in ONE spelling per P-v:
-- the statements carry only the machine's subValAt and the meta-level
-- bounded parts (the witness z, its K-membership, and the shared core
-- formula).  The bounded satisfaction is definitionally the truncated
-- Sigma of those parts, so the row agreements consume the parts
-- directly and the machine-to-story direction returns them.  The
-- machine-to-story direction needs the key pr ar a in K.
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
```

```agda
-- The binary propositional agreement (the And and Or rows).  The
-- machine's clause has no environment set; the story's frame binds one
-- (E in K) and carries envHypB2.  The agreement closes because the
-- machine's operation does not mention E: the story's env hypothesis
-- is extra content the agreement receives and does not use, and the
-- site facts supply the bounded subvalues and an ambient set in K.
--
-- The two envs inside the body differ by the E slot: the machine's
-- operation is at yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ, the story's at
-- yb ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ.  The transfers below cross
-- that extension.  The first subvalue's formula reads no slot below
-- the insertion point, so its satisfaction is the same type at both
-- envs; the second subvalue and the operation shift by one.
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

```

```agda
-- The And row: the PropAgree instantiation at tag 2 with intersection.
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

```

```agda
-- =====================================================================
-- THE NINE ROW AGREEMENTS ([LJ-1.42]).  Each agreement closes the
-- story's bounded row against the machine's clause at the class
-- carrier, both directions, under the site facts.  The shared pieces
-- are the EnvSet transfer (the missing conjunct), the shape transfers
-- and the leaf transfers above; each row supplies only its own frame
-- instantiation.
-- =====================================================================

-- The Top row: machine topClauseAt against Top.topBndAt.  The body is
-- sameB against sameAt, which is one OpTransfer (the same formula).
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

```

```agda
-- The successor-subvalue key at the unary full frame (shared by the
-- Forall and Exist agreements).
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
-- [LJ-1.331] THE ONE CHANGE OF THIS PROBE.  The twelve tie hypotheses of
-- the Forall row are stated once as a record, in the style of the file's
-- own `KFacts` block, and the row module takes ONE parameter in place of
-- twelve.  The body of the row module below is unchanged.
module ForallTiesNS where
  record ForallTies {m : ℕ} (C T B N K : Fin m) (γ : S ^ m) : Type (ℓ-suc ℓ) where
    field
      tagEq : fst (lookup N γ) ≡ fst (numeralL 9)
      numK : ⟨ fst (numeralL 9) ∈ fst (lookup K γ) ⟩
      innerK : (a : S) → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → ⟨ fst (prʟ (numeralL 9) a) ∈ fst (lookup K γ) ⟩
      arityK : (N v : S) → ⟨ fst v ∈ fst N ⟩
             → ⟨ fst N ∈ fst (lookup K γ) ⟩
             → ⟨ fst v ∈ fst (lookup K γ) ⟩
      codesK : (c ar a : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ × ⟨ fst a ∈ fst (lookup K γ) ⟩
               × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
      valK : (c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
           → fst c ≡ pr (fst ar) (pr (# 9) (fst a))
           → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
           → ⟨ fst yc ∈ fst (lookup K γ) ⟩
      succK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
            → succU {m} C T B N K γ E ya yc a ar c
      keyK : (E ya yc a ar c : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
           → ⟨ fst a ∈ fst (lookup K γ) ⟩
           → keyU {m} C T B N K γ E ya yc a ar c
      subK : (ya yc a ar c E : S) → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               subValSuccAt (suc (suc (suc (suc (suc (suc T))))))
                            (suc (suc (suc (suc zero))))
                            (suc (suc (suc zero)))
                            (suc zero) ⟩ → ⟨ fst ya ∈ fst (lookup K γ) ⟩
      envK : (ya yc a ar c E : S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
           → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
               envSetAt zero (suc (suc (suc (suc zero))))
                         (suc (suc (suc (suc (suc (suc B)))))) ⟩
           → ⟨ fst E ∈ fst (lookup K γ) ⟩
      envInK : (ya yc a ar c E : S) → ⟨ fst ar ∈ fst (lookup K γ) ⟩
             → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → (z : S) → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 envOverAt zero (suc (suc (suc (suc (suc zero)))))
                            (suc (suc (suc (suc (suc (suc (suc B))))))) ⟩
             → ⟨ fst z ∈ fst (lookup K γ) ⟩
      consK : (ya yc a ar c E z x e' : S) → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                 consAtL zero (suc zero) (suc (suc zero)) ⟩
            → ⟨ fst e' ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc K))))))))
                              (x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)) ⟩

module ForallAgree {m : ℕ} (C T B N K : Fin m) (γ : S ^ m)
  (ties : ForallTiesNS.ForallTies C T B N K γ)
  where
  open ForallTiesNS.ForallTies ties
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
```
