{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.15] The one-clause probe: the existential clause of the satisfaction
-- table as a Delta-0 matrix with the bound as a free variable, the Sigma-1
-- certificate, and the two-way decode at a variable carrier.  Plus the
-- carrier facts (statement 2).  Untracked probe; one Agda process; no git.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ115 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; Σ₁; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
        ; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
import FOL.Absoluteness
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset; 𝒟ₒ-intro; IsOrd; Lset-mono )
open import L.Absoluteness {ℓ} using ( InL; Δ₀-liftFo )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import L.Coding.Base {ℓ}
  using ( sglConAt; pairConAt; tagAt; Δ₀-prAt )
open import L.Coding.Environment {ℓ}
  using ( shiftPairAt; consAt; Δ₀-consAt; sucAt; Δ₀-sucAt )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; boundingOrd )
open import L.Ordinal.Stages {ℓ} lem
  using ( ord∈Lset-suc; Lset-cumul; ord∈Lset→∈; suc∈or≡ )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ}
  using ( Lset-suc; LsetS; isL-Lset; pr∈Lset-suc )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; tagAtL; tagAtL-adequate; appAt; appAt-adequate
        ; subValAt; subValSuccAt; subValSuccAt-adequate; consAtL; consAtL-adequate
        ; envSetAt; envOverAt; svAt; domAt; valuesInAt; pairsInAt
        ; arityTagAtL; arityTagAtL-adequate; unClauseAt
        ; existClauseAt; extAt; extAt-out; extAt-in
        ; quantClause-out; quantClause-in
        ; body∃; body∃-in; body∃-out; QuantWit
        ; sucAtL; prʟ; prʟ-fst; numL )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- The matrix of the existential clause.  Arity suc n: the bound sits at
-- slot zero, the slots C T B are shifted by one.  Every quantifier is
-- bounded (by C, by K, by B, or by a bound variable).
module _ {n : ℕ} (C T B : Fin n) where
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

  -- body content at env e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ K ∷ γ
  -- slots: 0=e 1=E 4=ya 7=K, B at 8+r
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
          ((var zero ≐ con (numeralL 8))
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

  -- full matrix, arity suc n, bound at slot zero
  -- binders: c(∀∈C) ar a yc (∀∈K) ya E (∀∈K) e (∀∈yc) x (∃∈B) e' (∃∈K)
  existBndAt : Formula S (suc n)
  existBndAt =
    ∀̇∈ (var C₁) (∀̇∈ (var (suc zero)) (∀̇∈ (var (suc (suc zero)))
      (∀̇∈ (var (suc (suc (suc zero))))
        (shapeBnd ⇒̇ (appAt (suc (suc (suc (suc T₁))))
                            (suc (suc (suc zero))) zero
        ⇒̇ (∀̇∈ (var (suc (suc (suc (suc zero)))))
            (∀̇∈ (var (suc (suc (suc (suc (suc zero))))))
              (subValHyp ⇒̇ (envHyp ⇒̇ (∀̇∈ (var (suc (suc zero))) bodyBnd))))))))))

  -- Delta-0 witnesses: the atoms are lifts of V-level Delta-0 formulas.
  Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
  Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

  Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
  Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)

  Δ₀-appAt : ∀ {m} (f x y : Fin m) → Δ₀ (appAt f x y)
  Δ₀-appAt f x y = δ-∃∈ (Δ₀-prAtL zero (suc x) (suc y))

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
        (δ-∀∈ (δ-∀∈ (δ-⇒ Δ₀-subValHyp (δ-⇒ Δ₀-envHyp (δ-∀∈ Δ₀-bodyBnd))))))))))

-- The Sigma-1 certificate: one existential over the bound, on the Delta-0
-- matrix.  At variable slots C T B, over a variable environment.
existCertAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
existCertAt C T B = ∃̇ (existBndAt C T B)

Σ₁-cert : ∀ {n} (C T B : Fin n) → Σ₁ (existCertAt C T B)
Σ₁-cert C T B = σ-∃ (σ-Δ₀ (Δ₀-existBndAt C T B))

-- The two-way decode of the matrix at variable slots.  OUT: a satisfied
-- matrix gives the layered content (mirror of unClause-out + quantClause-out).
module _ {n : ℕ} (C T B : Fin n) (γ : S ^ suc n) where
  private
    K : Fin (suc n)
    K = zero

  existBnd-out : ⟨ γ ⊨ existBndAt C T B ⟩
    → (c ar a yc : S) (c∈ : ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩)
    → (ar∈ : ⟨ fst ar ∈ fst (lookup K γ) ⟩) (a∈ : ⟨ fst a ∈ fst (lookup K γ) ⟩)
    → (yc∈ : ⟨ fst yc ∈ fst (lookup K γ) ⟩)
    → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shapeBnd C T B ⟩
    → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
    → (ya E : S) (ya∈ : ⟨ fst ya ∈ fst (lookup K γ) ⟩) (E∈ : ⟨ fst E ∈ fst (lookup K γ) ⟩)
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ subValHyp C T B ⟩
    → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHyp C T B ⟩
    → (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyBnd C T B ⟩
  existBnd-out h c ar a yc c∈ ar∈ a∈ yc∈ hshape hval ya E ya∈ E∈ hsub hE e e∈ =
    h c c∈ ar ar∈ a a∈ yc yc∈
      hshape
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc (suc T)))))
                                      (suc (suc (suc zero))) zero
                                      (yc ∷ a ∷ ar ∷ c ∷ γ))) hval)
      ya ya∈ E E∈ hsub hE e e∈

  -- IN: the layered content assembles the matrix.
  existBnd-in : ((c ar a yc : S) → ⟨ fst c ∈ fst (lookup (suc C) γ) ⟩
                → ⟨ fst ar ∈ fst (lookup K γ) ⟩ → ⟨ fst a ∈ fst (lookup K γ) ⟩
                → ⟨ fst yc ∈ fst (lookup K γ) ⟩
                → ⟨ (yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ shapeBnd C T B ⟩
                → ⟨ pr (fst c) (fst yc) ∈ fst (lookup (suc T) γ) ⟩
                → ((ya E : S) → ⟨ fst ya ∈ fst (lookup K γ) ⟩
                   → ⟨ fst E ∈ fst (lookup K γ) ⟩
                   → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ subValHyp C T B ⟩
                   → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ envHyp C T B ⟩
                   → ((e : S) → ⟨ fst e ∈ fst yc ⟩
                      → ⟨ (e ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) ⊨ bodyBnd C T B ⟩)))
    → ⟨ γ ⊨ existBndAt C T B ⟩
  existBnd-in g c c∈ ar ar∈ a a∈ yc yc∈ hshape hval ya ya∈ E E∈ hsub hE e e∈ =
    g c ar a yc c∈ ar∈ a∈ yc∈ hshape
      (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc (suc T)))))
                                 (suc (suc (suc zero))) zero
                                 (yc ∷ a ∷ ar ∷ c ∷ γ)) hval)
      ya E ya∈ E∈ hsub hE e e∈

-- =====================================================================
-- STATEMENT 2: the carrier facts.  For δ < α at a limit α, the level
-- sequence hierL δ and the chosen bound live in Lset α.
-- =====================================================================

-- The whole level at β appears at the next stage.
Lset∈suc : (β : V ℓ) → ⟨ Lset β ∈ Lset (sucV β) ⟩
Lset∈suc β = subst (λ w → ⟨ Lset β ∈ w ⟩) (sym (Lset-suc β))
  (𝒟ₒ-intro (Lset β) (Lset β) ∣ ⊤̇ , DefOf.defSet⊤≡A (Lset β) ∣₁)

-- An ordinal member of δ lives in the level at δ.
ord∈Lset : (δ : V ℓ) (oδ : IsOrd δ) (β : V ℓ) (oβ : IsOrd β)
         → ⟨ β ∈ δ ⟩ → ⟨ β ∈ Lset δ ⟩
ord∈Lset δ oδ β oβ β∈δ = Lset-cumul β δ oβ oδ β∈δ (ord∈Lset-suc β oβ)

-- The successor of a member of δ is a member of the successor.
suc∈suc : (δ : V ℓ) (oδ : IsOrd δ) (β : V ℓ) (oβ : IsOrd β)
        → ⟨ β ∈ δ ⟩ → ⟨ sucV β ∈ sucV δ ⟩
suc∈suc δ oδ β oβ β∈δ =
  Sum.rec (λ s∈δ → ∈sucV-inl {A = δ} {x = sucV β} s∈δ)
          (λ s≡δ → subst (λ w → ⟨ w ∈ sucV δ ⟩) (sym s≡δ) (self∈sucV δ))
          (suc∈or≡ β δ oβ oδ β∈δ)

-- A recorded pair (β, Lset β) lives three successors above δ.
pair-stage : (δ : V ℓ) (oδ : IsOrd δ) (β : V ℓ) (oβ : IsOrd β)
           → ⟨ β ∈ δ ⟩
           → ⟨ pr β (Lset β) ∈ Lset (sucV (sucV (sucV δ))) ⟩
pair-stage δ oδ β oβ β∈δ =
  pr∈Lset-suc (sucV δ) β (Lset β) β∈Lsucδ Lsetβ∈Lsucδ
  where
  β∈Lsucδ : ⟨ β ∈ Lset (sucV δ) ⟩
  β∈Lsucδ = Lset-mono {α = sucV δ} {β = δ} (self∈sucV δ)
             (ord∈Lset δ oδ β oβ β∈δ)

  Lsetβ∈Lsucδ : ⟨ Lset β ∈ Lset (sucV δ) ⟩
  Lsetβ∈Lsucδ = Lset-mono {α = sucV δ} {β = sucV β} (suc∈suc δ oδ β oβ β∈δ)
    (Lset∈suc β)

-- Every member of the level sequence is at the common stage (via the
-- specification of the internal hierarchy).
graph-mem-stage : (δ : V ℓ) (hδ : ⟨ isL δ ⟩) (oδ : IsOrd δ)
                → (z : V ℓ) → ⟨ z ∈ fst (hierL δ hδ oδ) ⟩
                → ⟨ z ∈ Lset (sucV (sucV (sucV δ))) ⟩
graph-mem-stage δ hδ oδ z z∈ = PT.rec
  (snd (z ∈ Lset (sucV (sucV (sucV δ))))) read
  (subst ⟨_⟩ (hierL-spec δ hδ oδ (z , z∈L)) z∈)
  where
  z∈L : ⟨ isL z ⟩
  z∈L = isL-trans {x = fst (hierL δ hδ oδ)} {y = z} z∈ (snd (hierL δ hδ oδ))

  read : Σ[ c ∈ S ] (⟨ fst c ∈ δ ⟩ × (z ≡ pr (fst c) (Lset (fst c))))
       → ⟨ z ∈ Lset (sucV (sucV (sucV δ))) ⟩
  read (c , (c∈ , q)) = subst (λ w → ⟨ w ∈ Lset (sucV (sucV (sucV δ))) ⟩) (sym q)
    (pair-stage δ oδ (fst c) (mem-ord {A = δ} oδ (fst c) c∈) c∈)
