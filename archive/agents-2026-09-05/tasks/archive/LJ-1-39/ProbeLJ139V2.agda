{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ139V2 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇ ; ∃̇_; ∃̇∈; ∀̇∈ )
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
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( prAtL; appAt; appAt-adequate; consAtL; sucAtL )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import Cubical.Data.Vec using ( map )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} S
private
  -- de Bruijn index abbreviations.  sh2 shifts a Fin index by two;
  -- z_d is the depth-d successor chain above zero.  Generic in the
  -- tail arity, so one kit serves every environment length (DD4).
  sh2 : {n : ℕ} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

  z2 : {n : ℕ} → Fin (suc (suc (suc (n))))
  z2 = suc (suc zero)

  z3 : {n : ℕ} → Fin (suc (suc (suc (suc (n)))))
  z3 = suc (suc (suc zero))

  z4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (n))))))
  z4 = suc (suc (suc (suc zero)))

  z5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (n)))))))
  z5 = suc (suc (suc (suc (suc zero))))

  z6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (n))))))))
  z6 = suc (suc (suc (suc (suc (suc zero)))))

  z7 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (n)))))))))
  z7 = suc (suc (suc (suc (suc (suc (suc zero))))))

  z8 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (n))))))))))
  z8 = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

  z9 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (n)))))))))))
  z9 = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

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
    (∀̇∈ (var z7) (∀̇∈ (var z8) (∀̇∈ (var z9) (appAt z3 z2 (suc zero) ⇒̇ (appAt z3 z2 zero
             ⇒̇ (var (suc zero) ≐ var zero))))))
    ∧̇ (∀̇∈ (var z7) (((∃̇∈ (var z8) (appAt z2 (suc zero) zero)) ⇒̇ (var zero ∈̇ var z6))
        ∧̇ ((var zero ∈̇ var z6) ⇒̇ (∃̇∈ (var z8) (appAt z2 (suc zero) zero)))))
    ∧̇ (∀̇∈ (var z7) (∀̇∈ (var z8) (appAt z2 (suc zero) zero
           ⇒̇ (var zero ∈̇ var (suc (sh2 (sh2 (sh2 (sh2 B₁)))))))))
    ∧̇ (∀̇∈ (var zero) (∃̇∈ (var z6) (∃̇∈ (var (suc (sh2 (sh2 (sh2 (sh2 B₁)))))) (prAtL z2 (suc zero) zero))))

  -- subvalue content at env z₂ ∷ z₁ ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=z₂ 1=z₁ 3=ya 5=a 6=ar, T at 9+q
  subValBnd : Formula S (9 + n)
  subValBnd =
    sucAtL z6 (suc zero)
    ∧̇ prAtL zero z5 z3
    ∧̇ appAt (sh2 (sh2 (sh2 (sh2 T₁))))
            zero z3

  -- body content at env e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=e 1=E 4=ya 7=K, B at 8+r
  bodyBnd : Formula S (8 + n)
  bodyBnd =
    (var zero ∈̇ var (suc zero))
    ∧̇ ∃̇∈ (var (suc (sh2 (sh2 (sh2 B₁)))))
        (∃̇∈ (var z8) (consAtL zero (suc zero) z2 ∧̇ (var zero ∈̇ var z4) ))

  -- shape hypothesis at env yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=yc 1=a 2=ar 3=c 4=K
  shapeBnd : Formula S (5 + n)
  shapeBnd =
    ∃̇∈ (var z4)
      (prAtL z4 z3 zero ∧̇ ∃̇∈ (var z5) ((var zero ≐ var (suc (sh2 (sh2 (sh2 N)))))
          ∧̇ prAtL (suc zero) zero z3))

  -- subvalue hypothesis at env E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=E 1=ya 2=yc 3=a 4=ar 5=c 6=K
  subValHyp : Formula S (7 + n)
  subValHyp =
    ∃̇∈ (var z6)
      (sucAtL z5 zero ∧̇ ∃̇∈ (var z7) subValBnd)

  -- env hypothesis at env E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  envHyp : Formula S (7 + n)
  envHyp = ∀̇∈ (var zero) envBnd

  -- full matrix, arity suc n, bound at slot zero
  -- binders: c(∀∈C) ar a yc (∀∈K) ya E (∀∈K) e (∀∈yc) x (∃∈B) e' (∃∈K)
  existBndAt : Formula S (suc n)
  existBndAt =
    ∀̇∈ (var C₁) (∀̇∈ (var (suc zero)) (∀̇∈ (var z2) (∀̇∈ (var z3) (shapeBnd ⇒̇ (appAt (sh2 (sh2 T₁)) z3 zero
        ⇒̇ (∀̇∈ (var z4) (∀̇∈ (var z5) (subValHyp ⇒̇ (envHyp ⇒̇ (∀̇∈ (var z2) bodyBnd))))))))))

  -- Delta-0 witnesses: the atoms are lifts of V-level Delta-0 formulas.
  Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
  Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

  Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
  Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)

  Δ₀-appAt : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
  Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

  Δ₀-envBnd : Δ₀ envBnd
  Δ₀-envBnd =
    δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt z3 z2 (suc zero)) (δ-⇒ (Δ₀-appAt z3 z2 zero) δ-≐)))))
        (δ-∧ (δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt z2 (suc zero) zero)) δ-∈)
                        (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt z2 (suc zero) zero)))))
             (δ-∧ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt z2 (suc zero) zero) δ-∈)))
                  (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtL z2 (suc zero) zero))))))

  Δ₀-subValBnd : Δ₀ subValBnd
  Δ₀-subValBnd =
    δ-∧ (Δ₀-sucAtL z6 (suc zero))
        (δ-∧ (Δ₀-prAtL zero z5 z3) (Δ₀-appAt (sh2 (sh2 (sh2 (sh2 T₁)))) zero z3))

  Δ₀-bodyBnd : Δ₀ bodyBnd
  Δ₀-bodyBnd =
    δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) z2)) δ-∈)))

  Δ₀-shapeBnd : Δ₀ shapeBnd
  Δ₀-shapeBnd =
    δ-∃∈ (δ-∧ (Δ₀-prAtL z4 z3 zero) (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero z3))))

  Δ₀-subValHyp : Δ₀ subValHyp
  Δ₀-subValHyp =
    δ-∃∈ (δ-∧ (Δ₀-sucAtL z5 zero) (δ-∃∈ Δ₀-subValBnd))

  Δ₀-envHyp : Δ₀ envHyp
  Δ₀-envHyp = δ-∀∈ Δ₀-envBnd

  Δ₀-existBndAt : Δ₀ existBndAt
  Δ₀-existBndAt =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ Δ₀-shapeBnd (δ-⇒ (Δ₀-appAt (sh2 (sh2 T₁)) z3 zero)
        (δ-∀∈ (δ-∀∈ (δ-⇒ Δ₀-subValHyp (δ-⇒ Δ₀-envHyp (δ-∀∈ Δ₀-bodyBnd))))))))))

-- The Sigma-1 certificate: one existential over the bound, on the Delta-0
-- matrix.  At variable slots C T B N, over a variable environment.
existCertAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
existCertAt C T B N = ∃̇ (Clause.existBndAt C T B N)

Σ₁-cert : ∀ {n} (C T B N : Fin n) → Σ₁ (existCertAt C T B N)
Σ₁-cert C T B N = σ-∃ (σ-Δ₀ (Clause.Δ₀-existBndAt C T B N))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.bodyBnd {n} C T B N ⟩
  existBnd-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub hE e e∈ =
    h c c∈ ar ar∈ a a∈ yc yc∈
      hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (sh2 (sh2 T))) z3 zero (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)
      ya ya∈ E E∈ hsub hE e e∈

  -- IN: the layered content assembles the matrix.
  existBnd-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
                → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
                → ⟨ fst yc ∈ fst (lookup K γ) ⟩
                → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.shapeBnd {n} C T B N ⟩
                → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
                → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩ → ⟨ fst E ∈ fst (lookup K γ) ⟩
                   → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.subValHyp {n} C T B N ⟩
                   → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.envHyp {n} C T B N ⟩
                   → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                      → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.bodyBnd {n} C T B N ⟩)))
    → ⟨ γ ⊨ Clause.existBndAt {n} C T B N ⟩
  existBnd-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval ya ya∈ E E∈ hsub hE e e∈ =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape
      (subst ⟨_⟩ (appAt-adequate (suc (sh2 (sh2 T))) z3 zero (yc ∷ a ∷ ar ∷ c ∷ γ)) hval)
      ya E ya∈ E∈ hsub hE e e∈

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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.bodyBnd {n} C T B N ⟩
  σL-out h = existBnd-out (transport (sym σL-eq) h)

  -- IN: the layered content assembles the embedded clause.
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
          → ⟨ fst yc ∈ fst (lookup K γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.shapeBnd {n} C T B N ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩ → ⟨ fst E ∈ fst (lookup K γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.subValHyp {n} C T B N ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.envHyp {n} C T B N ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩ → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Clause.bodyBnd {n} C T B N ⟩)))
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

-- The lifted atoms, exactly as block 1 builds them.
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

-- The bounded unary shape, at the frame environment yc ∷ a ∷ ar ∷ c ∷ γ
-- (4 + m): "c = pr ar (pr tag yc)", with the inner code and the tag in
-- K.  This is block 1's shapeBnd with the numeral replaced by a slot.
arTagB : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
arTagB tag K =
  ∃̇∈ (var (sh2 (sh2 K)))
    (prAtL z3 z2 zero ∧̇ ∃̇∈ (var (suc (sh2 (sh2 K)))) ((var zero ≐ var (sh2 (sh2 (sh2 tag))))
        ∧̇ prAtL (suc zero) zero z3))

Δ₀-arTagB : ∀ {m} (tag K : Fin m) → Δ₀ (arTagB tag K)
Δ₀-arTagB tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL z3 z2 zero) (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc zero) zero z3))))

-- The bounded binary shape, at the frame environment
-- yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (5 + m): "c = pr ar (pr tag (pr a b))".
arTagPairB : ∀ {m} → Fin m → Fin m → Formula S (5 + m)
arTagPairB tag K =
  ∃̇∈ (var (suc (sh2 (sh2 K))))
    (prAtL z4 z3 zero ∧̇ ∃̇∈ (var (sh2 (sh2 (sh2 K)))) ((var zero ≐ var (suc (sh2 (sh2 (sh2 tag)))))
        ∧̇ prAtL (suc zero) zero z2
        ∧̇ prAtL z2 z4
                 z3))

Δ₀-arTagPairB : ∀ {m} (tag K : Fin m) → Δ₀ (arTagPairB tag K)
Δ₀-arTagPairB tag K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL z4 z3 zero) (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-prAtL (suc zero) zero z2) (Δ₀-prAtL z2 z4 z3)))))

-- The bounded subvalue lookups.  "pr (pr ar a) y in T" (same arity)
-- and at the successor arity, with the key in K.
subValB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
subValB T ar a y K =
  ∃̇∈ (var K) (prAtL zero (suc ar) (suc a) ∧̇ appAt (suc T) zero (suc y))

Δ₀-subValB : ∀ {n} (T ar a y K : Fin n) → Δ₀ (subValB T ar a y K)
Δ₀-subValB T ar a y K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL zero (suc ar) (suc a)) (Δ₀-appAt (suc T) zero (suc y)))

subValSuccB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
subValSuccB T ar a y K =
  ∃̇∈ (var K) (sucAtL (suc ar) zero ∧̇ ∃̇∈ (var (suc K)) (prAtL zero (sh2 ar) (sh2 a) ∧̇ appAt (sh2 T) zero (sh2 y)))

Δ₀-subValSuccB : ∀ {n} (T ar a y K : Fin n) → Δ₀ (subValSuccB T ar a y K)
Δ₀-subValSuccB T ar a y K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL (suc ar) zero) (δ-∃∈ (δ-∧ (Δ₀-prAtL zero (sh2 ar) (sh2 a)) (Δ₀-appAt (sh2 T) zero (sh2 y)))))

-- The bounded term value: a variable term (t = pr tag1 z, pr z v in e)
-- or a constant term (t = pr tag0 v), with the keys in K.
tmValB : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
tmValB t e v K t0 t1 =
    (∃̇∈ (var K) (∃̇∈ (var (suc K)) ((var zero ≐ var (sh2 t1)) ∧̇ prAtL (sh2 t) zero (suc zero)
       ∧̇ appAt (sh2 e) zero (sh2 v))))
  ∨̇ (∃̇∈ (var K) ((var zero ≐ var (suc t0)) ∧̇ prAtL (suc t) zero (suc v)))

Δ₀-tmValB : ∀ {n} (t e v K t0 t1 : Fin n) → Δ₀ (tmValB t e v K t0 t1)
Δ₀-tmValB t e v K t0 t1 =
  δ-∨ (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-prAtL (sh2 t) zero (suc zero)) (Δ₀-appAt (sh2 e) zero (sh2 v))))))
      (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc t) zero (suc v))))

-- The generic bounded environment condition: E is a set of
-- environments over ar with domain yc and values in B.  The six slot
-- positions are parameters, so one formula serves every frame layout.
envBndGen : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
envBndGen e E yc ar K B =
    (∀̇∈ (var K) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (appAt (suc (sh2 E)) z2 (suc zero)
       ⇒̇ (appAt (suc (sh2 E)) z2 zero ⇒̇ (var (suc zero) ≐ var zero))))))
    ∧̇ (∀̇∈ (var K) (((∃̇∈ (var (suc K)) (appAt (sh2 E) (sh2 e) (suc zero))) ⇒̇ (var zero ∈̇ var (suc yc)))
        ∧̇ ((var zero ∈̇ var (suc yc)) ⇒̇ (∃̇∈ (var (suc K)) (appAt (sh2 E) (sh2 e) (suc zero))))))
    ∧̇ (∀̇∈ (var K) (∀̇∈ (var (suc K)) (appAt (sh2 E) (suc zero) zero ⇒̇ (var zero ∈̇ var (sh2 B)))))
    ∧̇ (∀̇∈ (var e) (∃̇∈ (var (suc ar)) (∃̇∈ (var (sh2 B)) (prAtL z2 (suc zero) zero))))

Δ₀-envBndGen : ∀ {n} (e E yc ar K B : Fin n) → Δ₀ (envBndGen e E yc ar K B)
Δ₀-envBndGen e E yc ar K B =
  δ-∧ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (suc (sh2 E)) z2 (suc zero)) (δ-⇒ (Δ₀-appAt (suc (sh2 E)) z2 zero) δ-≐)))))
      (δ-∧ (δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt (sh2 E) (sh2 e) (suc zero))) δ-∈)
                      (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt (sh2 E) (sh2 e) (suc zero))))))
           (δ-∧ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (sh2 E) (suc zero) zero) δ-∈)))
                (δ-∀∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAtL z2 (suc zero) zero))))))

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
  extAtB y K ((var zero ∈̇ var (suc e)) ∧̇ ((var zero ∈̇ var (suc a)) ⇒̇ (var zero ∈̇ var (suc b))))

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
  (envBndGen {7 + m} zero (suc zero) z3 z5 (suc (sh2 (sh2 (sh2 K)))) (suc (sh2 (sh2 (sh2 B)))))

Δ₀-envHypU : ∀ {m} (B K : Fin m) → Δ₀ (envHypU B K)
Δ₀-envHypU {m} B K = δ-∀∈ (Δ₀-envBndGen {7 + m} zero (suc zero) z3 z5 (suc (sh2 (sh2 (sh2 K))))
  (suc (sh2 (sh2 (sh2 B)))))

-- Constant (no second value slot): E ∷ yc ∷ a ∷ ar ∷ c ∷ γ (5 + m),
-- B at 6 + B, K at 6 + K.
envHypT : ∀ {m} → Fin m → Fin m → Formula S (5 + m)
envHypT {m} B K = ∀̇∈ (var zero)
  (envBndGen {6 + m} zero (suc zero) z2 z4 (sh2 (sh2 (sh2 K))) (sh2 (sh2 (sh2 B))))

Δ₀-envHypT : ∀ {m} (B K : Fin m) → Δ₀ (envHypT B K)
Δ₀-envHypT {m} B K = δ-∀∈ (Δ₀-envBndGen {6 + m} zero (suc zero) z2 z4 (sh2 (sh2 (sh2 K))) (sh2 (sh2 (sh2 B))))

-- Binary (with ya): E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (7 + m),
-- B at 8 + B, K at 8 + K.
envHypB2 : ∀ {m} → Fin m → Fin m → Formula S (7 + m)
envHypB2 {m} B K = ∀̇∈ (var zero)
  (envBndGen {8 + m} zero (suc zero) z3 z6 (sh2 (sh2 (sh2 (sh2 K)))) (sh2 (sh2 (sh2 (sh2 B)))))

Δ₀-envHypB2 : ∀ {m} (B K : Fin m) → Δ₀ (envHypB2 B K)
Δ₀-envHypB2 {m} B K = δ-∀∈ (Δ₀-envBndGen {8 + m} zero (suc zero) z3 z6 (sh2 (sh2 (sh2 (sh2 K))))
  (sh2 (sh2 (sh2 (sh2 B)))))

-- Binary without ya (atom rows): E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ (6 + m),
-- B at 7 + B, K at 7 + K.
envHypB2T : ∀ {m} → Fin m → Fin m → Formula S (6 + m)
envHypB2T {m} B K = ∀̇∈ (var zero)
  (envBndGen {7 + m} zero (suc zero) z2 z5 (suc (sh2 (sh2 (sh2 K)))) (suc (sh2 (sh2 (sh2 B)))))

Δ₀-envHypB2T : ∀ {m} (B K : Fin m) → Δ₀ (envHypB2T B K)
Δ₀-envHypB2T {m} B K = δ-∀∈ (Δ₀-envBndGen {7 + m} zero (suc zero) z2 z5 (suc (sh2 (sh2 (sh2 K))))
  (suc (sh2 (sh2 (sh2 B)))))

-- =====================================================================
-- THE FIVE ROW FRAMES.  Each frame is generic in the environment arity
-- m and the K slot, so one formula serves the class carrier (K = 0)
-- and the graph's inner environment (K shifted by the three graph
-- binders).
-- =====================================================================
-- The unary frame, full: c in C, ar in K, a in K, yc in K; shape;
-- lookup; ya in K, E in K; sub; env; every member e of yc satisfies
-- the body.
unFullAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m)
         → Formula S (6 + m) → Formula S (6 + m) → Formula S (7 + m)
         → Formula S m
unFullAt C T K shape sub env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (suc (sh2 K))) (shape ⇒̇ (appAt (sh2 (sh2 T)) z3 zero
      ⇒̇ (∀̇∈ (var (sh2 (sh2 K))) (∀̇∈ (var (suc (sh2 (sh2 K)))) (sub ⇒̇ (env ⇒̇ (∀̇∈ (var z2) body))))))))))

Δ₀-unFullAt : ∀ {m} (C T K : Fin m) (shape : Formula S (4 + m))
            (sub env : Formula S (6 + m)) (body : Formula S (7 + m))
            → Δ₀ shape → Δ₀ sub → Δ₀ env → Δ₀ body
            → Δ₀ (unFullAt C T K shape sub env body)
Δ₀-unFullAt C T K shape sub env body ds dsub denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds (δ-⇒ (Δ₀-appAt (sh2 (sh2 T)) z3 zero)
      (δ-∀∈ (δ-∀∈ (δ-⇒ dsub (δ-⇒ denv (δ-∀∈ dbody))))))))))

-- The unary frame, environment only (the constant row top).
unEnvAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m) → Formula S (5 + m)
        → Formula S (6 + m) → Formula S m
unEnvAt C T K shape env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (suc (sh2 K))) (shape ⇒̇ (appAt (sh2 (sh2 T)) z3 zero
      ⇒̇ (∀̇∈ (var (sh2 (sh2 K))) (env ⇒̇ (∀̇∈ (var (suc zero)) body))))))))

Δ₀-unEnvAt : ∀ {m} (C T K : Fin m) (shape : Formula S (4 + m))
           (env : Formula S (5 + m)) (body : Formula S (6 + m))
           → Δ₀ shape → Δ₀ env → Δ₀ body
           → Δ₀ (unEnvAt C T K shape env body)
Δ₀-unEnvAt C T K shape env body ds denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds (δ-⇒ (Δ₀-appAt (sh2 (sh2 T)) z3 zero) (δ-∀∈ (δ-⇒ denv (δ-∀∈ dbody))))))))

-- The unary frame, bare (the constant row bot).
unBareAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m) → Formula S (4 + m)
         → Formula S m
unBareAt C T K shape body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (suc (sh2 K))) (shape ⇒̇ (appAt (sh2 (sh2 T)) z3 zero
      ⇒̇ body)))))

Δ₀-unBareAt : ∀ {m} (C T K : Fin m) (shape : Formula S (4 + m))
            (body : Formula S (4 + m))
            → Δ₀ shape → Δ₀ body → Δ₀ (unBareAt C T K shape body)
Δ₀-unBareAt C T K shape body ds dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds (δ-⇒ (Δ₀-appAt (sh2 (sh2 T)) z3 zero) dbody)))))

-- The binary frame, full.
binFullAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (5 + m) → Formula S (7 + m)
          → Formula S (7 + m) → Formula S (8 + m) → Formula S m
binFullAt C T K shape sub env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (suc (sh2 K))) (∀̇∈ (var (sh2 (sh2 K)))
      (shape ⇒̇ (appAt (suc (sh2 (sh2 T))) z4 zero ⇒̇ (∀̇∈ (var (suc (sh2 (sh2 K)))) (∀̇∈ (var (sh2 (sh2 (sh2 K))))
            (sub ⇒̇ (env ⇒̇ (∀̇∈ (var z2) body)))))))))))

Δ₀-binFullAt : ∀ {m} (C T K : Fin m) (shape : Formula S (5 + m))
             (sub env : Formula S (7 + m)) (body : Formula S (8 + m))
             → Δ₀ shape → Δ₀ sub → Δ₀ env → Δ₀ body
             → Δ₀ (binFullAt C T K shape sub env body)
Δ₀-binFullAt C T K shape sub env body ds dsub denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds (δ-⇒ (Δ₀-appAt (suc (sh2 (sh2 T))) z4 zero)
      (δ-∀∈ (δ-∀∈ (δ-⇒ dsub (δ-⇒ denv (δ-∀∈ dbody)))))))))))

-- The binary frame, environment only (the atom rows).
binEnvAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S (5 + m) → Formula S (6 + m)
         → Formula S (7 + m) → Formula S m
binEnvAt C T K shape env body =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (suc (sh2 K))) (∀̇∈ (var (sh2 (sh2 K)))
      (shape ⇒̇ (appAt (suc (sh2 (sh2 T))) z4 zero ⇒̇ (∀̇∈ (var (suc (sh2 (sh2 K))))
            (env ⇒̇ (∀̇∈ (var (suc zero)) body)))))))))

Δ₀-binEnvAt : ∀ {m} (C T K : Fin m) (shape : Formula S (5 + m))
            (env : Formula S (6 + m)) (body : Formula S (7 + m))
            → Δ₀ shape → Δ₀ env → Δ₀ body
            → Δ₀ (binEnvAt C T K shape env body)
Δ₀-binEnvAt C T K shape env body ds denv dbody =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ ds (δ-⇒ (Δ₀-appAt (suc (sh2 (sh2 T))) z4 zero)
      (δ-∀∈ (δ-⇒ denv (δ-∀∈ dbody)))))))))

-- The two-way decode of the full unary frame at the class carrier.
-- OUT: a satisfied frame gives the layered content.  IN: the layered
-- content assembles the frame.
module UnFullDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (4 + m)) (sub env : Formula S (6 + m))
         (body : Formula S (7 + m)) (γ : S ^ m) where
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  unFull-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ =
    h c c∈ ar ar∈ a a∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (sh2 (sh2 T)) z3 zero (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)
      ya ya∈ E E∈ hsub henv e e∈

  unFull-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ fst yc ∈ fst (lookup K γ) ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
              → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
              → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩ → ⟨ fst E ∈ fst (lookup K γ) ⟩
                 → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sub ⟩
                 → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                 → ((e : S) → ⟨ fst e ∈ fst yc ⟩ → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩)))
    → ⟨ γ ⊨ unFullAt C T K shape sub env body ⟩
  unFull-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval ya ya∈ E E∈ hsub henv e e∈ =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape
      (subst ⟨_⟩ (appAt-adequate (sh2 (sh2 T)) z3 zero (yc ∷ a ∷ ar ∷ c ∷ γ)) hval)
      ya E ya∈ E∈ hsub henv e e∈

-- The two-way decode of the full binary frame.
module BinFullDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (5 + m)) (sub env : Formula S (7 + m))
         (body : Formula S (8 + m)) (γ : S ^ m) where
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  binFull-out h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ =
    h c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (sh2 (sh2 T))) z4 zero (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) hval)
      ya ya∈ E E∈ hsub henv e e∈

  binFull-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
               → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
               → ⟨ fst b ∈ fst (lookup K γ) ⟩ → ⟨ fst yc ∈ fst (lookup K γ) ⟩
               → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
               → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
               → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩ → ⟨ fst E ∈ fst (lookup K γ) ⟩
                  → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ sub ⟩
                  → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                  → ((e : S) → ⟨ fst e ∈ fst yc ⟩ → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩)))
    → ⟨ γ ⊨ binFullAt C T K shape sub env body ⟩
  binFull-in g c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape hval ya ya∈ E E∈ hsub henv e e∈ =
    g c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape
      (subst ⟨_⟩ (appAt-adequate (suc (sh2 (sh2 T))) z4 zero (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)) hval)
      ya E ya∈ E∈ hsub henv e e∈

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
      (subst ⟨_⟩ (sym (appAt-adequate (sh2 (sh2 T)) z3 zero (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)

  unBare-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ fst yc ∈ fst (lookup K γ) ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (sh2 (sh2 T)) z3 zero ⟩
              → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩)
    → ⟨ γ ⊨ unBareAt C T K shape body ⟩
  unBare-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape hval

-- The two-way decode of the environment-only unary frame (top).
module UnEnvDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (4 + m)) (env : Formula S (5 + m))
         (body : Formula S (6 + m)) (γ : S ^ m) where
  unEnv-out : ⟨ γ ⊨ unEnvAt C T K shape env body ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → (E : S) (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  unEnv-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval E E∈ henv e e∈ =
    h c c∈ ar ar∈ a a∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (sh2 (sh2 T)) z3 zero (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)
      E E∈ henv e e∈

  unEnv-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
             → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
             → ⟨ fst yc ∈ fst (lookup K γ) ⟩
             → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
             → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨
                  appAt (sh2 (sh2 T)) z3 zero ⟩
             → ((E : S) → ⟨ fst E ∈ fst (lookup K γ) ⟩ → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                → ((e : S) → ⟨ fst e ∈ fst yc ⟩ → ⟨ (e ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩)))
    → ⟨ γ ⊨ unEnvAt C T K shape env body ⟩
  unEnv-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval E E∈ henv e e∈ =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape
      hval E E∈ henv e e∈

-- The two-way decode of the environment-only binary frame (the atom
-- rows).
module BinEnvDecode {m : ℕ} (C T K : Fin m)
         (shape : Formula S (5 + m)) (env : Formula S (6 + m))
         (body : Formula S (7 + m)) (γ : S ^ m) where
  binEnv-out : ⟨ γ ⊨ binEnvAt C T K shape env body ⟩
    → (c ar a b yc : S) (c∈ : ⟨ fst c ∈ fst (lookup C γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (b∈ : ⟨ fst b ∈ fst (lookup K γ) ⟩) (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩
    → (E : S) (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩
  binEnv-out h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv e e∈ =
    h c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (sh2 (sh2 T))) z4 zero (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ))) hval)
      E E∈ henv e e∈

  binEnv-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup C γ) ⟩
              → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
              → ⟨ fst b ∈ fst (lookup K γ) ⟩ → ⟨ fst yc ∈ fst (lookup K γ) ⟩
              → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ shape ⟩
              → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
                   appAt (suc (sh2 (sh2 T))) z4 zero ⟩
              → ((E : S) → ⟨ fst E ∈ fst (lookup K γ) ⟩ → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ env ⟩
                 → ((e : S) → ⟨ fst e ∈ fst yc ⟩ → ⟨ (e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ body ⟩)))
    → ⟨ γ ⊨ binEnvAt C T K shape env body ⟩
  binEnv-in g c c∈ ar ar∈ a a∈ b b∈ yc yc∈ hshape hval E E∈ henv e e∈ =
    g c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape
      hval E E∈ henv e e∈

-- The propositional body: the second value yb is bound in K, its
-- subvalue is read, and the operation speaks of the recorded value,
-- the first and the second subvalues.
propBodyB : ∀ {m} → Fin m → Fin m → Formula S (9 + m) → Formula S (8 + m)
propBodyB T K op =
  ∀̇∈ (var (sh2 (sh2 (sh2 (sh2 K)))))
    (subValB (suc (sh2 (sh2 (sh2 (sh2 T))))) z7 z5 zero (suc (sh2 (sh2 (sh2 (sh2 K))))) ⇒̇ op)

Δ₀-propBodyB : ∀ {m} (T K : Fin m) (op : Formula S (9 + m))
             → Δ₀ op → Δ₀ (propBodyB T K op)
Δ₀-propBodyB T K op dop =
  δ-∀∈ (δ-⇒ (Δ₀-subValB (suc (sh2 (sh2 (sh2 (sh2 T))))) z7 z5 zero (suc (sh2 (sh2 (sh2 (sh2 K)))))) dop)

-- The atom body: "y in E, and there are term values v of a and w of b
-- in K with v cmp w".
atomBodyB : ∀ {m} → Fin m → Fin m → Fin m → Formula S (10 + m) → Formula S (8 + m)
atomBodyB t0 t1 K cmp =
  (var zero ∈̇ var z2)
  ∧̇ ∃̇∈ (var (sh2 (sh2 (sh2 (sh2 K)))))
      (∃̇∈ (var (suc (sh2 (sh2 (sh2 (sh2 K)))))) (tmValB z7 z3 (suc zero) (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))
        ∧̇ tmValB z6
                z3
                zero
                (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))
        ∧̇ cmp))

Δ₀-atomBodyB : ∀ {m} (t0 t1 K : Fin m) (cmp : Formula S (10 + m))
             → Δ₀ cmp → Δ₀ (atomBodyB t0 t1 K cmp)
Δ₀-atomBodyB t0 t1 K cmp dc =
  δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∧ d1 (δ-∧ d2 dc))))
  where
  d1 : Δ₀ (tmValB (suc (suc (suc (suc (suc (suc (suc zero))))))) z3 (suc zero) (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t1))))))
  d1 = Δ₀-tmValB z7
                 z3
                 (suc zero)
                 (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))

  d2 : Δ₀ (tmValB (suc (suc (suc (suc (suc (suc zero)))))) z3 zero (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t1))))))
  d2 = Δ₀-tmValB z6
                 z3
                 zero
                 (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))

-- The bounded-quantifier bodies: "y in E, and for the term value w of
-- a (in K), for every x in B with x in w, every extended environment
-- e' in K satisfies e' in ya".
bndBodyAll : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (8 + m)
bndBodyAll B K t0 t1 =
  extAtB z3
         (sh2 (sh2 (sh2 (sh2 K))))
    ((var zero ∈̇ var z2) ∧̇ ∀̇∈ (var (suc (sh2 (sh2 (sh2 (sh2 B)))))) (tmValB z7 z2 zero
                (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))
        ⇒̇ ∀̇∈ (var (sh2 (sh2 (sh2 (sh2 (sh2 B))))))
            ((var zero ∈̇ var (suc zero)) ⇒̇ ∀̇∈ (var (suc (sh2 (sh2 (sh2 (sh2 (sh2 K)))))))
                (consAtL zero (suc zero) z3 ⇒̇ (var zero ∈̇ var z6)))))

bndBodyEx : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S (8 + m)
bndBodyEx B K t0 t1 =
  extAtB z3
         (sh2 (sh2 (sh2 (sh2 K))))
    ((var zero ∈̇ var z2) ∧̇ ∃̇∈ (var (suc (sh2 (sh2 (sh2 (sh2 K)))))) (tmValB z7 z2 zero
                (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))
        ∧̇ ∃̇∈ (var (sh2 (sh2 (sh2 (sh2 (sh2 B))))))
            ((var zero ∈̇ var (suc zero)) ∧̇ ∃̇∈ (var (suc (sh2 (sh2 (sh2 (sh2 (sh2 K)))))))
                (consAtL zero (suc zero) z3 ∧̇ (var zero ∈̇ var z6)))))

Δ₀-bndBodyAll : ∀ {m} (B K t0 t1 : Fin m) → Δ₀ (bndBodyAll B K t0 t1)
Δ₀-bndBodyAll B K t0 t1 =
  Δ₀-extAtB z3
            (sh2 (sh2 (sh2 (sh2 K)))) _
    (δ-∧ δ-∈ (δ-∀∈ (δ-⇒ dt (δ-∀∈ (δ-⇒ δ-∈ (δ-∀∈ (δ-⇒ dc δ-∈)))))))
  where
  dt : Δ₀ (tmValB (suc (suc (suc (suc (suc (suc (suc zero))))))) z2 zero (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t1))))))
  dt = Δ₀-tmValB z7
                 z2
                 zero
                 (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))

  dc : Δ₀ (consAtL zero (suc zero) (suc (suc (suc zero))))
  dc = Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) z3)

Δ₀-bndBodyEx : ∀ {m} (B K t0 t1 : Fin m) → Δ₀ (bndBodyEx B K t0 t1)
Δ₀-bndBodyEx B K t0 t1 =
  Δ₀-extAtB z3
            (sh2 (sh2 (sh2 (sh2 K)))) _
    (δ-∧ δ-∈ (δ-∃∈ (δ-∧ dt (δ-∃∈ (δ-∧ δ-∈ (δ-∃∈ (δ-∧ dc δ-∈)))))))
  where
  dt : Δ₀ (tmValB (suc (suc (suc (suc (suc (suc (suc zero))))))) z2 zero (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                  (sh2 (sh2 (sh2 (sh2 (sh2 t1))))))
  dt = Δ₀-tmValB z7
                 z2
                 zero
                 (sh2 (sh2 (sh2 (sh2 (sh2 K)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t0)))))
                 (sh2 (sh2 (sh2 (sh2 (sh2 t1)))))

  dc : Δ₀ (consAtL zero (suc zero) (suc (suc (suc zero))))
  dc = Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) z3)

-- =====================================================================
-- THE ELEVEN ROWS.  Each row is one instantiation of its frame at the
-- generic environment arity m, with its Delta-0 witness.  The tag
-- numerals are slots, so every formula is constant-free.
-- =====================================================================
module Bot {m : ℕ} (C T B N K : Fin m) where
  botBndAt : Formula S m
  botBndAt = unBareAt C T K (arTagB N K) (emptyB zero (sh2 (sh2 K)))

  Δ₀-botBndAt : Δ₀ botBndAt
  Δ₀-botBndAt =
    Δ₀-unBareAt C T K (arTagB N K) (emptyB zero (sh2 (sh2 K)))
      (Δ₀-arTagB N K) (Δ₀-emptyB zero (sh2 (sh2 K)))

module Top {m : ℕ} (C T B N K : Fin m) where
  topBndAt : Formula S m
  topBndAt =
    unEnvAt C T K (arTagB N K) (envHypT B K)
      (sameB z2 (suc zero) (sh2 (sh2 (sh2 K))))

  Δ₀-topBndAt : Δ₀ topBndAt
  Δ₀-topBndAt =
    Δ₀-unEnvAt C T K (arTagB N K) (envHypT B K)
      (sameB z2 (suc zero) (sh2 (sh2 (sh2 K))))
      (Δ₀-arTagB N K) (Δ₀-envHypT B K)
      (Δ₀-sameB z2 (suc zero) (sh2 (sh2 (sh2 K))))

module Neg {m : ℕ} (C T B N K : Fin m) where
  subN : Formula S (6 + m)
  subN = subValB (sh2 (sh2 (sh2 T)))
                   z4
                   z3
                   (suc zero)
                   (sh2 (sh2 (sh2 K)))

  bodyN : Formula S (7 + m)
  bodyN = diffB z3 (suc zero) z2
                  (suc (sh2 (sh2 (sh2 K))))

  negBndAt : Formula S m
  negBndAt = unFullAt C T K (arTagB N K) subN (envHypU B K) bodyN

  Δ₀-negBndAt : Δ₀ negBndAt
  Δ₀-negBndAt =
    Δ₀-unFullAt C T K (arTagB N K) subN (envHypU B K) bodyN
      (Δ₀-arTagB N K)
      (Δ₀-subValB (sh2 (sh2 (sh2 T))) z4 z3 (suc zero) (sh2 (sh2 (sh2 K))))
      (Δ₀-envHypU B K)
      (Δ₀-diffB z3 (suc zero) z2 (suc (sh2 (sh2 (sh2 K)))))

module Forall {m : ℕ} (C T B N K : Fin m) where
  subF : Formula S (6 + m)
  subF = subValSuccB (sh2 (sh2 (sh2 T)))
                       z4
                       z3
                       (suc zero)
                       (sh2 (sh2 (sh2 K)))

  bodyFφ : Formula S (8 + m)
  bodyFφ =
      (var zero ∈̇ var z2)
      ∧̇ ∀̇∈ (var (sh2 (sh2 (sh2 (sh2 B)))))
          (∀̇∈ (var (suc (sh2 (sh2 (sh2 (sh2 K)))))) (consAtL zero (suc zero) z2 ⇒̇ (var zero ∈̇ var z4)))

  bodyF : Formula S (7 + m)
  bodyF = extAtB z3
                   (suc (sh2 (sh2 (sh2 K))))
                   bodyFφ

  Δ₀-bodyFφ : Δ₀ bodyFφ
  Δ₀-bodyFφ =
      δ-∧ δ-∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) z2)) δ-∈)))

  forallBndAt : Formula S m
  forallBndAt = unFullAt C T K (arTagB N K) subF (envHypU B K) bodyF

  Δ₀-forallBndAt : Δ₀ forallBndAt
  Δ₀-forallBndAt =
    Δ₀-unFullAt C T K (arTagB N K) subF (envHypU B K) bodyF
      (Δ₀-arTagB N K)
      (Δ₀-subValSuccB (sh2 (sh2 (sh2 T))) z4 z3 (suc zero) (sh2 (sh2 (sh2 K))))
      (Δ₀-envHypU B K)
      (Δ₀-extAtB z3 (suc (sh2 (sh2 (sh2 K)))) bodyFφ Δ₀-bodyFφ)

module And {m : ℕ} (C T B N K : Fin m) where
  subA : Formula S (7 + m)
  subA = subValB (suc (sh2 (sh2 (sh2 T))))
                   z5
                   z4
                   (suc zero)
                   (suc (sh2 (sh2 (sh2 K))))

  opA : Formula S (9 + m)
  opA = interB z4
                 z3
                 zero
                 (suc (sh2 (sh2 (sh2 (sh2 K)))))

  andBndAt : Formula S m
  andBndAt = binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
              (propBodyB T K opA)

  Δ₀-andBndAt : Δ₀ andBndAt
  Δ₀-andBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
      (propBodyB T K opA)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValB (suc (sh2 (sh2 (sh2 T)))) z5 z4 (suc zero) (suc (sh2 (sh2 (sh2 K)))))
      (Δ₀-envHypB2 B K)
      (Δ₀-propBodyB T K opA (Δ₀-interB z4 z3 zero (suc (sh2 (sh2 (sh2 (sh2 K)))))))

module Or {m : ℕ} (C T B N K : Fin m) where
  subO : Formula S (7 + m)
  subO = subValB (suc (sh2 (sh2 (sh2 T))))
                   z5
                   z4
                   (suc zero)
                   (suc (sh2 (sh2 (sh2 K))))

  opO : Formula S (9 + m)
  opO = unionB z4
                 z3
                 zero
                 (suc (sh2 (sh2 (sh2 (sh2 K)))))

  orBndAt : Formula S m
  orBndAt = binFullAt C T K (arTagPairB N K) subO (envHypB2 B K)
             (propBodyB T K opO)

  Δ₀-orBndAt : Δ₀ orBndAt
  Δ₀-orBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subO (envHypB2 B K)
      (propBodyB T K opO)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValB (suc (sh2 (sh2 (sh2 T)))) z5 z4 (suc zero) (suc (sh2 (sh2 (sh2 K)))))
      (Δ₀-envHypB2 B K)
      (Δ₀-propBodyB T K opO (Δ₀-unionB z4 z3 zero (suc (sh2 (sh2 (sh2 (sh2 K)))))))

module Imp {m : ℕ} (C T B N K : Fin m) where
  subI : Formula S (7 + m)
  subI = subValB (suc (sh2 (sh2 (sh2 T))))
                   z5
                   z4
                   (suc zero)
                   (suc (sh2 (sh2 (sh2 K))))

  opI : Formula S (9 + m)
  opI = implB z4
                z2
                z3
                zero
                (suc (sh2 (sh2 (sh2 (sh2 K)))))

  impBndAt : Formula S m
  impBndAt = binFullAt C T K (arTagPairB N K) subI (envHypB2 B K)
              (propBodyB T K opI)

  Δ₀-impBndAt : Δ₀ impBndAt
  Δ₀-impBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subI (envHypB2 B K)
      (propBodyB T K opI)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValB (suc (sh2 (sh2 (sh2 T)))) z5 z4 (suc zero) (suc (sh2 (sh2 (sh2 K)))))
      (Δ₀-envHypB2 B K)
      (Δ₀-propBodyB T K opI (Δ₀-implB z4 z2 z3 zero (suc (sh2 (sh2 (sh2 (sh2 K)))))))

module Mem {m : ℕ} (C T B N K t0 t1 : Fin m) where
  bodyM : Formula S (7 + m)
  bodyM = extAtB z2
                   (suc (sh2 (sh2 (sh2 K))))
                   (atomBodyB t0 t1 K (var (suc zero) ∈̇ var zero))

  memBndAt : Formula S m
  memBndAt = binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyM

  Δ₀-memBndAt : Δ₀ memBndAt
  Δ₀-memBndAt =
    Δ₀-binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyM
      (Δ₀-arTagPairB N K) (Δ₀-envHypB2T B K)
      (Δ₀-extAtB z2 (suc (sh2 (sh2 (sh2 K)))) (atomBodyB t0 t1 K (var (suc zero) ∈̇ var zero))
                 (Δ₀-atomBodyB t0 t1 K (var (suc zero) ∈̇ var zero) δ-∈))

module Eq {m : ℕ} (C T B N K t0 t1 : Fin m) where
  bodyE : Formula S (7 + m)
  bodyE = extAtB z2
                   (suc (sh2 (sh2 (sh2 K))))
                   (atomBodyB t0 t1 K (var (suc zero) ≐ var zero))

  eqBndAt : Formula S m
  eqBndAt = binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyE

  Δ₀-eqBndAt : Δ₀ eqBndAt
  Δ₀-eqBndAt =
    Δ₀-binEnvAt C T K (arTagPairB N K) (envHypB2T B K) bodyE
      (Δ₀-arTagPairB N K) (Δ₀-envHypB2T B K)
      (Δ₀-extAtB z2 (suc (sh2 (sh2 (sh2 K)))) (atomBodyB t0 t1 K (var (suc zero) ≐ var zero))
                 (Δ₀-atomBodyB t0 t1 K (var (suc zero) ≐ var zero) δ-≐))

module AllIn {m : ℕ} (C T B N K t0 t1 : Fin m) where
  subA : Formula S (7 + m)
  subA = subValSuccB (suc (sh2 (sh2 (sh2 T))))
                       z5
                       z3
                       (suc zero)
                       (suc (sh2 (sh2 (sh2 K))))

  allInBndAt : Formula S m
  allInBndAt = binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
                (bndBodyAll B K t0 t1)

  Δ₀-allInBndAt : Δ₀ allInBndAt
  Δ₀-allInBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subA (envHypB2 B K)
      (bndBodyAll B K t0 t1)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValSuccB (suc (sh2 (sh2 (sh2 T)))) z5 z3 (suc zero) (suc (sh2 (sh2 (sh2 K)))))
      (Δ₀-envHypB2 B K)
      (Δ₀-bndBodyAll B K t0 t1)

module ExIn {m : ℕ} (C T B N K t0 t1 : Fin m) where
  subE : Formula S (7 + m)
  subE = subValSuccB (suc (sh2 (sh2 (sh2 T))))
                       z5
                       z3
                       (suc zero)
                       (suc (sh2 (sh2 (sh2 K))))

  exInBndAt : Formula S m
  exInBndAt = binFullAt C T K (arTagPairB N K) subE (envHypB2 B K)
               (bndBodyEx B K t0 t1)

  Δ₀-exInBndAt : Δ₀ exInBndAt
  Δ₀-exInBndAt =
    Δ₀-binFullAt C T K (arTagPairB N K) subE (envHypB2 B K)
      (bndBodyEx B K t0 t1)
      (Δ₀-arTagPairB N K)
      (Δ₀-subValSuccB (suc (sh2 (sh2 (sh2 T)))) z5 z3 (suc zero) (suc (sh2 (sh2 (sh2 K)))))
      (Δ₀-envHypB2 B K)
      (Δ₀-bndBodyEx B K t0 t1)

-- The twelfth row, the bounded existential (block 1's clause at the
-- generic layout), for the twelve-row conjunction inside the graph.
module Exist {m : ℕ} (C T B N K : Fin m) where
  subE : Formula S (6 + m)
  subE = subValSuccB (sh2 (sh2 (sh2 T)))
                       z4
                       z3
                       (suc zero)
                       (sh2 (sh2 (sh2 K)))

  bodyE : Formula S (7 + m)
  bodyE = (var zero ∈̇ var (suc zero))
            ∧̇ ∃̇∈ (var (suc (sh2 (sh2 (sh2 B)))))
                (∃̇∈ (var (sh2 (sh2 (sh2 (sh2 K))))) (consAtL zero (suc zero) z2 ∧̇ (var zero ∈̇ var z4)))

  existBndAt : Formula S m
  existBndAt = unFullAt C T K (arTagB N K) subE (envHypU B K) bodyE

  Δ₀-existBndAt : Δ₀ existBndAt
  Δ₀-existBndAt =
    Δ₀-unFullAt C T K (arTagB N K) subE (envHypU B K) bodyE
      (Δ₀-arTagB N K)
      (Δ₀-subValSuccB (sh2 (sh2 (sh2 T))) z4 z3 (suc zero) (sh2 (sh2 (sh2 K))))
      (Δ₀-envHypU B K)
      (δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-liftFo _ (Δ₀-consAt zero (suc zero) z2)) δ-∈))))

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
  ∃̇∈ (var K) (∃̇∈ (var (suc K)) ((var zero ≐ con (numeralL k)) ∧̇ prAtL (sh2 c) zero (suc zero)))

Δ₀-keyArBnum : ∀ {n} (c : Fin n) (k : ℕ) (K : Fin n) → Δ₀ (keyArBnum c k K)
Δ₀-keyArBnum c k K =
  δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (sh2 c) zero (suc zero))))

tagBnum : ∀ {n} → Fin n → ℕ → Fin n → Fin n → Formula S n
tagBnum s k x K =
  ∃̇∈ (var K) ((var zero ≐ con (numeralL k)) ∧̇ prAtL (suc s) zero (suc x))

Δ₀-tagBnum : ∀ {n} (s : Fin n) (k : ℕ) (x K : Fin n) → Δ₀ (tagBnum s k x K)
Δ₀-tagBnum s k x K = δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL (suc s) zero (suc x)))

-- The bounded binary shape with a numeral tag, at the closedness
-- environment b ∷ a ∷ ar ∷ c ∷ γ (4 + m).
arTagPairBnum : ∀ {m} → ℕ → Fin m → Formula S (4 + m)
arTagPairBnum k K =
  ∃̇∈ (var (sh2 (sh2 K)))
  (prAtL z3 z2 zero ∧̇ ∃̇∈ (var (suc (sh2 (sh2 K)))) (∃̇∈ (var (sh2 (sh2 (sh2 K)))) ((var zero ≐ con (numeralL k))
          ∧̇ prAtL z2 (suc zero) zero
          ∧̇ prAtL zero z4 z3)))

Δ₀-arTagPairBnum : ∀ {m} (k : ℕ) (K : Fin m) → Δ₀ (arTagPairBnum k K)
Δ₀-arTagPairBnum k K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL z3 z2 zero) (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-prAtL z2 (suc zero) zero) (Δ₀-prAtL zero z4
                                                 z3))))))

-- The bounded unary shape with a numeral tag, at the closedness
-- environment a ∷ ar ∷ c ∷ γ (3 + m).
arTagBnum : ∀ {m} → ℕ → Fin m → Formula S (3 + m)
arTagBnum k K =
  ∃̇∈ (var (suc (sh2 K)))
  (prAtL z2 (suc zero) zero ∧̇ ∃̇∈ (var (sh2 (sh2 K))) (∃̇∈ (var (suc (sh2 (sh2 K)))) ((var zero ≐ con (numeralL k))
          ∧̇ prAtL z2 (suc zero) zero)))

Δ₀-arTagBnum : ∀ {m} (k : ℕ) (K : Fin m) → Δ₀ (arTagBnum k K)
Δ₀-arTagBnum k K =
  δ-∃∈ (δ-∧ (Δ₀-prAtL z2 (suc zero) zero) (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (Δ₀-prAtL z2 (suc zero) zero)))))

-- The bounded shape frames for closedness.
binShapeB : ∀ {m} → Fin m → ℕ → Fin m → Formula S (4 + m) → Formula S m
binShapeB C k K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (suc (sh2 K))) (arTagPairBnum k K ⇒̇ rel))))

Δ₀-binShapeB : ∀ {m} (C : Fin m) (k : ℕ) (K : Fin m) (rel : Formula S (4 + m))
             → Δ₀ rel → Δ₀ (binShapeB C k K rel)
Δ₀-binShapeB C k K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagPairBnum k K) drel))))

unShapeB : ∀ {m} → Fin m → ℕ → Fin m → Formula S (3 + m) → Formula S m
unShapeB C k K rel =
  ∀̇∈ (var C) (∀̇∈ (var (suc K)) (∀̇∈ (var (sh2 K)) (arTagBnum k K ⇒̇ rel)))

Δ₀-unShapeB : ∀ {m} (C : Fin m) (k : ℕ) (K : Fin m) (rel : Formula S (3 + m))
            → Δ₀ rel → Δ₀ (unShapeB C k K rel)
Δ₀-unShapeB C k K rel drel =
  δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-arTagBnum k K) drel)))

bothSameB : ∀ {m} → Fin m → Formula S (4 + m)
bothSameB C =
  appAt (sh2 (sh2 C)) z2 (suc zero)
  ∧̇ appAt (sh2 (sh2 C)) z2 zero

Δ₀-bothSameB : ∀ {m} (C : Fin m) → Δ₀ (bothSameB C)
Δ₀-bothSameB C =
  δ-∧ (Δ₀-appAt (sh2 (sh2 C)) z2 (suc zero))
      (Δ₀-appAt (sh2 (sh2 C)) z2 zero)

oneSameB : ∀ {m} → Fin m → Formula S (3 + m)
oneSameB C = appAt (suc (sh2 C)) z2 (suc zero)

Δ₀-oneSameB : ∀ {m} (C : Fin m) → Δ₀ (oneSameB C)
Δ₀-oneSameB C = Δ₀-appAt (suc (sh2 C)) z2 (suc zero)

oneSuccB : ∀ {m} → Fin m → Fin m → Formula S (3 + m)
oneSuccB C K =
  ∃̇∈ (var (suc (sh2 K)))
  (sucAtL z2 zero ∧̇ appAt (sh2 (sh2 C)) zero (suc zero))

Δ₀-oneSuccB : ∀ {m} (C K : Fin m) → Δ₀ (oneSuccB C K)
Δ₀-oneSuccB C K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL z2 zero) (Δ₀-appAt (sh2 (sh2 C)) zero (suc zero)))

succSndB : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
succSndB C K =
  ∃̇∈ (var (sh2 (sh2 K)))
  (sucAtL z3 zero ∧̇ appAt (suc (sh2 (sh2 C))) zero (suc zero))

Δ₀-succSndB : ∀ {m} (C K : Fin m) → Δ₀ (succSndB C K)
Δ₀-succSndB C K =
  δ-∃∈ (δ-∧ (Δ₀-sucAtL z3 zero) (Δ₀-appAt (suc (sh2 (sh2 C))) zero (suc zero)))

closedB : ∀ {m} → Fin m → Fin m → Formula S m
closedB C K =
  binShapeB C 2 K (bothSameB C)
  ∧̇ (binShapeB C 3 K (bothSameB C) ∧̇ (binShapeB C 4 K (bothSameB C) ∧̇ (unShapeB C 5 K (oneSameB C)
  ∧̇ (unShapeB C 8 K (oneSuccB C K) ∧̇ (unShapeB C 9 K (oneSuccB C K) ∧̇ (binShapeB C 10 K (succSndB C K)
  ∧̇ binShapeB C 11 K (succSndB C K)))))))

Δ₀-closedB : ∀ {m} (C K : Fin m) → Δ₀ (closedB C K)
Δ₀-closedB C K =
  δ-∧ (Δ₀-binShapeB C 2 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-binShapeB C 3 K (bothSameB C) (Δ₀-bothSameB C)) (δ-∧ (Δ₀-binShapeB C 4 K (bothSameB C) (Δ₀-bothSameB C))
      (δ-∧ (Δ₀-unShapeB C 5 K (oneSameB C) (Δ₀-oneSameB C)) (δ-∧ (Δ₀-unShapeB C 8 K (oneSuccB C K) (Δ₀-oneSuccB C K))
      (δ-∧ (Δ₀-unShapeB C 9 K (oneSuccB C K) (Δ₀-oneSuccB C K))
      (δ-∧ (Δ₀-binShapeB C 10 K (succSndB C K) (Δ₀-succSndB C K))
           (Δ₀-binShapeB C 11 K (succSndB C K) (Δ₀-succSndB C K))))))))

-- The bounded shape forms for shapedness, at c ∷ γ (1 + m).
binFormB : ∀ {m} → ℕ → Fin m → Formula S (4 + m) → Formula S (1 + m)
binFormB k K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (sh2 K)) (∃̇∈ (var (suc (sh2 K))) (arTagPairBnum k K ∧̇ rel)))

Δ₀-binFormB : ∀ {m} (k : ℕ) (K : Fin m) (rel : Formula S (4 + m))
            → Δ₀ rel → Δ₀ (binFormB k K rel)
Δ₀-binFormB k K rel drel =
  δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-arTagPairBnum k K) drel)))

unFormB : ∀ {m} → ℕ → Fin m → Formula S (3 + m) → Formula S (1 + m)
unFormB k K rel =
  ∃̇∈ (var (suc K)) (∃̇∈ (var (sh2 K)) (arTagBnum k K ∧̇ rel))

Δ₀-unFormB : ∀ {m} (k : ℕ) (K : Fin m) (rel : Formula S (3 + m))
           → Δ₀ rel → Δ₀ (unFormB k K rel)
Δ₀-unFormB k K rel drel =
  δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-arTagBnum k K) drel))

isTmB : ∀ {m} → Fin (4 + m) → Fin m → Fin m → Formula S (4 + m)
isTmB t A K =
  ∃̇∈ (var (sh2 (sh2 K)))
  (tagBnum (suc t) 0 zero (suc (sh2 (sh2 K))) ∧̇ (var zero ∈̇ var (suc (sh2 (sh2 A)))))

Δ₀-isTmB : ∀ {m} (t : Fin (4 + m)) (A K : Fin m) → Δ₀ (isTmB t A K)
Δ₀-isTmB t A K =
  δ-∃∈ (δ-∧ (Δ₀-tagBnum (suc t) 0 zero (suc (sh2 (sh2 K)))) δ-∈)

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
  ∨̇ (binFormB 1 K (bothTmB A K) ∨̇ (binFormB 2 K ⊤̇ ∨̇ (binFormB 3 K ⊤̇ ∨̇ (binFormB 4 K ⊤̇ ∨̇ (unFormB 5 K ⊤̇
  ∨̇ (unFormB 6 K (var zero ≐ con (numeralL 0)) ∨̇ (unFormB 7 K (var zero ≐ con (numeralL 0)) ∨̇ (unFormB 8 K ⊤̇
  ∨̇ (unFormB 9 K ⊤̇ ∨̇ (binFormB 10 K (fstTmB A K) ∨̇ binFormB 11 K (fstTmB A K)))))))))))

Δ₀-shapesB : ∀ {m} (A K : Fin m) → Δ₀ (shapesB A K)
Δ₀-shapesB A K =
  δ-∨ (Δ₀-binFormB 0 K (bothTmB A K) (Δ₀-bothTmB A K))
      (δ-∨ (Δ₀-binFormB 1 K (bothTmB A K) (Δ₀-bothTmB A K)) (δ-∨ (Δ₀-binFormB 2 K ⊤̇ δ-⊤) (δ-∨ (Δ₀-binFormB 3 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormB 4 K ⊤̇ δ-⊤) (δ-∨ (Δ₀-unFormB 5 K ⊤̇ δ-⊤) (δ-∨ (Δ₀-unFormB 6 K (var zero ≐ con (numeralL 0)) δ-≐)
      (δ-∨ (Δ₀-unFormB 7 K (var zero ≐ con (numeralL 0)) δ-≐) (δ-∨ (Δ₀-unFormB 8 K ⊤̇ δ-⊤) (δ-∨ (Δ₀-unFormB 9 K ⊤̇ δ-⊤)
      (δ-∨ (Δ₀-binFormB 10 K (fstTmB A K) (Δ₀-fstTmB A K)) (Δ₀-binFormB 11 K (fstTmB A K) (Δ₀-fstTmB A K))))))))))))

shapedB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
shapedB C A K = ∀̇∈ (var C) (shapesB A K)

Δ₀-shapedB : ∀ {m} (C A K : Fin m) → Δ₀ (shapedB C A K)
Δ₀-shapedB C A K = δ-∀∈ (Δ₀-shapesB A K)

hasWitnessB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
hasWitnessB A x K =
  ∃̇∈ (var K) ((var (suc x) ∈̇ var zero) ∧̇ (closedB zero (suc K) ∧̇ shapedB zero (suc A) (suc K)))

Δ₀-hasWitnessB : ∀ {m} (A x K : Fin m) → Δ₀ (hasWitnessB A x K)
Δ₀-hasWitnessB A x K =
  δ-∃∈ (δ-∧ δ-∈ (δ-∧ (Δ₀-closedB zero (suc K)) (Δ₀-shapedB zero (suc A) (suc K))))

isCodeB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
isCodeB c w K = keyArBnum c 1 K ∧̇ hasWitnessB w c K

Δ₀-isCodeB : ∀ {m} (c w K : Fin m) → Δ₀ (isCodeB c w K)
Δ₀-isCodeB c w K =
  δ-∧ (Δ₀-keyArBnum c 1 K) (Δ₀-hasWitnessB w c K)

domB : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
domB f d K =
  ∀̇∈ (var K)
  (((∃̇∈ (var (suc K)) (appAt (sh2 f) (suc zero) zero)) ⇒̇ (var zero ∈̇ var (suc d))) ∧̇ ((var zero ∈̇ var (suc d))
      ⇒̇ (∃̇∈ (var (suc K)) (appAt (sh2 f) (suc zero) zero))))

Δ₀-domB : ∀ {m} (f d K : Fin m) → Δ₀ (domB f d K)
Δ₀-domB f d K =
  δ-∀∈ (δ-∧ (δ-⇒ (δ-∃∈ (Δ₀-appAt (sh2 f) (suc zero) zero)) δ-∈) (δ-⇒ δ-∈ (δ-∃∈ (Δ₀-appAt (sh2 f) (suc zero) zero))))

-- The bounded one-entry environment and the bounded definable-subset
-- condition, with the constant tag as the numeral 0.  At the
-- environment E ∷ x' ∷ γ (2 + m): "E is the set of exactly the one
-- entry z' = pr #0 x'", with the values in K.
envOneBnd : ∀ {m} → Fin m → Fin m → Formula S (2 + m)
envOneBnd v K =
  extAtB zero (sh2 K)
  (tagBnum zero 0 z2 (suc (sh2 K)))

Δ₀-envOneBnd : ∀ {m} (v K : Fin m) → Δ₀ (envOneBnd v K)
Δ₀-envOneBnd v K =
  Δ₀-extAtB zero (sh2 K) _
  (Δ₀-tagBnum zero 0 z2 (suc (sh2 K)))

DefinesB : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S m
DefinesB x w v K =
  extAtB x K
  ((var zero ∈̇ var (suc w)) ∧̇ ∃̇∈ (var (suc K)) (envOneBnd v K ∧̇ (var zero ∈̇ var (sh2 v))))

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
              (emptyB zero z4) γ
  module T = RowTransfer φ refl d γ
  open T public
  σL-out : ⟨ γ ⊨ σL ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup zero γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup zero γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup zero γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ emptyB zero z4 ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval →
    D.unBare-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (suc (sh2 (sh2 T))) z3 zero ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ emptyB zero z4 ⟩)
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
              (sameB z2 (suc zero) z6) γ
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sameB z2 (suc zero) z6 ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval E E∈ henv e e∈ →
    D.unEnv-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval E E∈ henv e e∈
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (suc (sh2 (sh2 T))) z3 zero ⟩
          → ((E : S) → ⟨ fst E ∈ fst (lookup zero γ) ⟩ → ⟨ (E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypT (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩ → ⟨ (e ∷ E ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ sameB z2 (suc zero) z6 ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Neg.bodyN {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ →
    D.unFull-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩ → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Neg.subN {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypU (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Neg.bodyN {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Forall.bodyF {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
  σL-out = λ h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ →
    D.unFull-out (transport (sym σL-eq) h) c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈
  σL-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩ → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Forall.subF {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypU (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ Forall.bodyF {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (And.opA {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩ → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ And.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (And.opA {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Or.opO {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩ → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Or.subO {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Or.opO {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Imp.opI {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩ → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Imp.subI {suc n} (suc C) (suc T) (suc B) (suc N) zero ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ propBodyB (suc T) zero (Imp.opI {suc n} (suc C) (suc T) (suc B) (suc N) zero) ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Mem.bodyM {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv e e∈ →
    D.binEnv-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv e e∈
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (sh2 (sh2 (sh2 T))) z4 zero ⟩
          → ((E : S) → ⟨ fst E ∈ fst (lookup zero γ) ⟩ → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2T (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Mem.bodyM {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Eq.bodyE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv e e∈ →
    D.binEnv-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval E E∈ henv e e∈
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ appAt (sh2 (sh2 (sh2 T))) z4 zero ⟩
          → ((E : S) → ⟨ fst E ∈ fst (lookup zero γ) ⟩ → ⟨ (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2T (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ Eq.bodyE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyAll (suc B) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩ → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ AllIn.subA {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyAll (suc B) zero (suc t0) (suc t1) ⟩)))
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
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyEx (suc B) zero (suc t0) (suc t1) ⟩
  σL-out = λ h c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈ →
    D.binFull-out (transport (sym σL-eq) h) c ar a b yc c∈ ar∈ a∈ b∈ yc∈ hshape hval ya E ya∈ E∈ hsub henv e e∈
  σL-in : ((c ar a b yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
          → ⟨ fst ar ∈ fst (lookup zero γ) ⟩ → ⟨ fst a ∈ fst (lookup zero γ) ⟩
          → ⟨ fst b ∈ fst (lookup zero γ) ⟩ → ⟨ fst yc ∈ fst (lookup zero γ) ⟩
          → ⟨ (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ arTagPairB (suc N) zero ⟩
          → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
          → ((ya E : S) → ⟨ fst ya ∈ fst (lookup zero γ) ⟩ → ⟨ fst E ∈ fst (lookup zero γ) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ ExIn.subE {suc n} (suc C) (suc T) (suc B) (suc N) zero (suc t0) (suc t1) ⟩
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHypB2 (suc B) zero ⟩
             → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                → ⟨ (e ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨ bndBodyEx (suc B) zero (suc t0) (suc t1) ⟩)))
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
    K' = suc (suc (sh2 (sh2 K)))

  twelveB : Formula S (11 + n)
  twelveB =
    Mem.memBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N0))) K'
      (sh2 (sh2 (sh2 t0)))
      (sh2 (sh2 (sh2 t1)))
    ∧̇ (Eq.eqBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N1))) K' (sh2 (sh2 (sh2 t0))) (sh2 (sh2 (sh2 t1)))
    ∧̇ (And.andBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N2))) K'
    ∧̇ (Or.orBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N3))) K'
    ∧̇ (Imp.impBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N4))) K'
    ∧̇ (Neg.negBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N5))) K'
    ∧̇ (Top.topBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N6))) K'
    ∧̇ (Bot.botBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N7))) K'
    ∧̇ (Exist.existBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N8))) K'
    ∧̇ (Forall.forallBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N9))) K'
    ∧̇ (AllIn.allInBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N10))) K' (sh2 (sh2 (sh2 t0)))
      (sh2 (sh2 (sh2 t1)))
    ∧̇ (ExIn.exInBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N11))) K' (sh2 (sh2 (sh2 t0)))
      (sh2 (sh2 (sh2 t1))))))))))))))

  Δ₀-twelveB : Δ₀ twelveB
  Δ₀-twelveB =
    δ-∧ (Mem.Δ₀-memBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N0))) K' (sh2 (sh2 (sh2 t0)))
           (sh2 (sh2 (sh2 t1))))
        (δ-∧ (Eq.Δ₀-eqBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N1))) K' (sh2 (sh2 (sh2 t0)))
               (sh2 (sh2 (sh2 t1))))
        (δ-∧ (And.Δ₀-andBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N2))) K')
        (δ-∧ (Or.Δ₀-orBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N3))) K')
        (δ-∧ (Imp.Δ₀-impBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N4))) K')
        (δ-∧ (Neg.Δ₀-negBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N5))) K')
        (δ-∧ (Top.Δ₀-topBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N6))) K')
        (δ-∧ (Bot.Δ₀-botBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N7))) K')
        (δ-∧ (Exist.Δ₀-existBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N8))) K')
        (δ-∧ (Forall.Δ₀-forallBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N9))) K')
        (δ-∧ (AllIn.Δ₀-allInBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N10))) K' (sh2 (sh2 (sh2 t0)))
               (sh2 (sh2 (sh2 t1))))
             (ExIn.Δ₀-exInBndAt {11 + n} z2 (suc zero) zero (sh2 (sh2 (sh2 N11))) K' (sh2 (sh2 (sh2 t0)))
               (sh2 (sh2 (sh2 t1))))))))))))))

  satGraphB : Formula S (suc (suc (suc (5 + n))))
  satGraphB =
    ∃̇∈ (var (suc (sh2 K)))
      (∃̇∈ (var (sh2 (sh2 K))) (∃̇∈ (var (suc (sh2 (sh2 K)))) ((var zero ≐ var (sh2 (sh2 (sh2 w))))
          ∧̇ (closedB zero (sh2 (sh2 (sh2 K))) ∧̇ (domB (suc zero) z2 (sh2 (sh2 (sh2 K))) ∧̇ (appAt (suc zero) z4
                   z3
          ∧̇ twelveB))))))

  Δ₀-satGraphB : Δ₀ satGraphB
  Δ₀-satGraphB =
    δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ δ-≐ (δ-∧ (Δ₀-closedB zero (sh2 (sh2 (sh2 K)))) (δ-∧ (Δ₀-domB (suc zero) z2
                    (sh2 (sh2 (sh2 K))))
      (δ-∧ (Δ₀-appAt (suc zero) z4 z3) Δ₀-twelveB))))))

-- The bounded code-set description: the three leaves of DefBody,
-- bounded by K, at the leaf environment v' ∷ c' ∷ x ∷ δ.
DefBodyB : ∀ {n} → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Fin (5 + n) → Fin (5 + n)
         → Fin (5 + n) → Fin (5 + n) → Formula S (suc (suc (suc (5 + n))))
DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 =
  isCodeB (suc zero) (suc (sh2 w)) (suc (sh2 K))
  ∧̇ (SatGraphB.satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1
    ∧̇ DefinesB z2 (suc (sh2 w)) zero (suc (sh2 K)))

Δ₀-DefBodyB : ∀ {n} (w K : Fin (5 + n))
  (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 : Fin (5 + n))
  → Δ₀ (DefBodyB w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)
Δ₀-DefBodyB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1 =
  δ-∧ (Δ₀-isCodeB (suc zero) (suc (sh2 w)) (suc (sh2 K)))
      (δ-∧ (SatGraphB.Δ₀-satGraphB {n} w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 t0 t1)
           (Δ₀-DefinesB z2 (suc (sh2 w)) zero (suc (sh2 K))))
