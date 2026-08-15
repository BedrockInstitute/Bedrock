
```agda
-- =====================================================================
-- LJ-1.266 bisection arm: the tower-neutral FACT fields only
-- ([LJ-1.258] + [LJ-1.259]), NO env supply, NO merge.
-- =====================================================================

open import L.Constructible {ℓ} using ( isTransV; Lset-layer; layer-trans )
open import L.Axioms.Basic {ℓ} using ( isL-Lset; finSet )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.Model {ℓ}
  using ( tmValAt-out; subValAt-adequate; subValSuccAt-adequate
        ; consAtL-adequate )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Vec using ( Vec; lookup )
import Cubical.Data.Sum as Sum

pattern one   = suc zero
pattern two   = suc one
pattern three = suc two
pattern four  = suc three
pattern five  = suc four
pattern six   = suc five
pattern seven = suc six
pattern eight = suc seven
pattern nine  = suc eight

module Fact (K : S) (Ktr : isTransV (fst K)) where

  prK : (x y : V ℓ) → ⟨ pr x y ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩ × ⟨ y ∈ fst K ⟩
  prK x y h = Ktr (mem x (inl refl)) pairInK , Ktr (mem y (inr refl)) pairInK
    where
    pairInK : ⟨ ⁅ x , y ⁆ ∈ fst K ⟩
    pairInK = Ktr (∈∈ₛ {a = ⁅ x , y ⁆} {b = pr x y} .snd
                (pairing-ax ⁅ x ⁆s ⁅ x , y ⁆ ⁅ x , y ⁆ .snd ∣ inr refl ∣₁)) h
    mem : (z : V ℓ) → (z ≡ x) Sum.⊎ (z ≡ y) → ⟨ z ∈ ⁅ x , y ⁆ ⟩
    mem z e = ∈∈ₛ {a = z} {b = ⁅ x , y ⁆} .snd (pairing-ax x y z .snd ∣ e ∣₁)

  valK : (C T : S) → ⟨ fst T ∈ fst K ⟩
       → (k : ℕ) (c ar a b yc : S)
       → ⟨ fst c ∈ fst C ⟩
       → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
       → ⟨ pr (fst c) (fst yc) ∈ fst T ⟩
       → ⟨ fst yc ∈ fst K ⟩
  valK C T TK k c ar a b yc c∈ shape hc =
    prK (fst c) (fst yc) (Ktr hc TK) .snd

  valK-un : (C T : S) → ⟨ fst T ∈ fst K ⟩
          → (k : ℕ) (c ar a yc : S)
          → ⟨ fst c ∈ fst C ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (fst a))
          → ⟨ pr (fst c) (fst yc) ∈ fst T ⟩
          → ⟨ fst yc ∈ fst K ⟩
  valK-un C T TK k c ar a yc c∈ shape hc =
    prK (fst c) (fst yc) (Ktr hc TK) .snd

  subK-gen : {n : ℕ} (γ : Vec S n) (T ar a y : Fin n)
           → ⟨ fst (lookup T γ) ∈ fst K ⟩
           → ⟨ γ ⊨ subValAt T ar a y ⟩
           → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subK-gen γ T ar a y TK h =
    prK (pr (fst (lookup ar γ)) (fst (lookup a γ))) (fst (lookup y γ))
      (Ktr (subst ⟨_⟩ (subValAt-adequate T ar a y γ) h) TK) .snd

  subKSucc-gen : {n : ℕ} (γ : Vec S n) (T ar a y : Fin n)
               → ⟨ fst (lookup T γ) ∈ fst K ⟩
               → ⟨ γ ⊨ subValSuccAt T ar a y ⟩
               → ⟨ fst (lookup y γ) ∈ fst K ⟩
  subKSucc-gen γ T ar a y TK h =
    prK (pr (sucV (fst (lookup ar γ))) (fst (lookup a γ))) (fst (lookup y γ))
      (Ktr (subst ⟨_⟩ (subValSuccAt-adequate T ar a y γ) h) TK) .snd

  subK₁-and : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (x y yc b a ar c : S)
            → ⟨ (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
            → ⟨ fst y ∈ fst K ⟩
  subK₁-and γ' TK x y yc b a ar c h =
    subK-gen (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five four one TK h

  subK₀-and : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (y ya yc b a ar c : S)
            → ⟨ (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc zero)))
                           zero ⟩
            → ⟨ fst y ∈ fst K ⟩
  subK₀-and γ' TK y ya yc b a ar c h =
    subK-gen (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five three zero TK h

  subK₁-imp : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (E yb ya yc b a ar c : S)
            → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc zero)) ⟩
            → ⟨ fst ya ∈ fst K ⟩
  subK₁-imp γ' TK E yb ya yc b a ar c h =
    subK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') nine six five two TK h

  subK₀-imp : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
            → (E yb ya yc b a ar c : S)
            → ⟨ (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                  subValAt (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                           (suc (suc (suc (suc zero))))
                           (suc zero) ⟩
            → ⟨ fst yb ∈ fst K ⟩
  subK₀-imp γ' TK E yb ya yc b a ar c h =
    subK-gen (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') nine six four one TK h

  subK-neg : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
           → (ya yc a ar c E : S)
           → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                 subValAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (suc (suc (suc (suc zero))))
                          (suc (suc (suc zero)))
                          (suc zero) ⟩
           → ⟨ fst ya ∈ fst K ⟩
  subK-neg γ' TK ya yc a ar c E h =
    subK-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') seven four three one TK h

  subK-un : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
          → (ya yc a ar c E : S)
          → ⟨ (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                subValSuccAt (suc (suc (suc (suc (suc (suc (suc zero)))))))
                             (suc (suc (suc (suc zero))))
                             (suc (suc (suc zero)))
                             (suc zero) ⟩
          → ⟨ fst ya ∈ fst K ⟩
  subK-un γ' TK ya yc a ar c E h =
    subKSucc-gen (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') seven four three one TK h

  subK-allin : (γ' : Vec S 2) → ⟨ fst (lookup (suc zero) γ') ∈ fst K ⟩
             → (E ya yc b a ar c : S)
             → ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                   subValSuccAt (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                (suc (suc (suc (suc (suc zero)))))
                                (suc (suc (suc zero)))
                                (suc zero) ⟩
             → ⟨ fst ya ∈ fst K ⟩
  subK-allin γ' TK E ya yc b a ar c h =
    subKSucc-gen (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') eight five three one TK h

  tmValK : {n : ℕ} (γ : Vec S n) (t e v : Fin n)
         → ⟨ fst (lookup e γ) ∈ fst K ⟩
         → ⟨ fst (lookup t γ) ∈ fst K ⟩
         → ⟨ γ ⊨ tmValAt t e v ⟩
         → ⟨ fst (lookup v γ) ∈ fst K ⟩
  tmValK γ t e v eK tK h =
    PT.rec (snd (fst (lookup v γ) ∈ fst K)) (λ { (inl q) → varCase q
                                              ; (inr q) → conCase q })
      (tmValAt-out t e v γ h)
    where
    varCase : (Σ[ k ∈ S ] ((fst (lookup t γ) ≡ pr (# 1) (fst k))
                            × ⟨ pr (fst k) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩))
            → ⟨ fst (lookup v γ) ∈ fst K ⟩
    varCase (k , (_ , kv∈e)) = prK (fst k) (fst (lookup v γ)) (Ktr kv∈e eK) .snd
    conCase : fst (lookup t γ) ≡ pr (# 0) (fst (lookup v γ))
            → ⟨ fst (lookup v γ) ∈ fst K ⟩
    conCase q = prK (# 0) (fst (lookup v γ))
      (subst (λ w → ⟨ w ∈ fst K ⟩) q tK) .snd

  valV : (γ' : Vec S 2) → (E yc b a ar c z v w : S)
       → ⟨ fst z ∈ fst K ⟩ → ⟨ fst a ∈ fst K ⟩
       → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                     (suc (suc zero))
                     (suc zero) ⟩
       → ⟨ fst v ∈ fst K ⟩
  valV γ' E yc b a ar c z v w zK aK h =
    tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') six two one zK aK h

  valW : (γ' : Vec S 2) → (E yc b a ar c z v w : S)
       → ⟨ fst z ∈ fst K ⟩ → ⟨ fst b ∈ fst K ⟩
       → ⟨ (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
             tmValAt (suc (suc (suc (suc (suc zero)))))
                     (suc (suc zero))
                     zero ⟩
       → ⟨ fst w ∈ fst K ⟩
  valW γ' E yc b a ar c z v w zK bK h =
    tmValK (w ∷ v ∷ z ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') five two zero zK bK h

  wKfact : (γ' : Vec S 2) → (E ya yc b a ar c z w : S)
         → ⟨ fst z ∈ fst K ⟩ → ⟨ fst a ∈ fst K ⟩
         → ⟨ (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
               tmValAt (suc (suc (suc (suc (suc (suc zero))))))
                       (suc zero)
                       zero ⟩
         → ⟨ fst w ∈ fst K ⟩
  wKfact γ' E ya yc b a ar c z w zK aK h =
    tmValK (w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') six one zero zK aK h

  module ConsK
    (envConsK : {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
              → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
              → ⟨ env (cons x g) ∈ fst K ⟩) where

    consK-forall : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                 → {k : ℕ} (g : Fin k → V ℓ)
                 → fst z ≡ env g
                 → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                 → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                     consAtL zero (suc zero) (suc (suc zero)) ⟩
                 → ⟨ fst e' ∈ fst K ⟩
    consK-forall γ' ya yc a ar c E z x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
               (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-allin : (γ' : Vec S 2) → (E ya yc b a ar c z w x e' : S)
                → {k : ℕ} (g : Fin k → V ℓ)
                → fst z ≡ env g
                → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-allin γ' E ya yc b a ar c z w x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
               (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-exist : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                → ⟨ fst ya ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc zero))
                    ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-exist γ' ya yc a ar c E z x e' yaK h =
      Ktr (h .snd) yaK

  module EnvClosure
    (numK0 : ⟨ # 0 ∈ fst K ⟩)
    (sucK : (a : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ sucV a ∈ fst K ⟩)
    (pairK : (a b : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ b ∈ fst K ⟩ → ⟨ pr a b ∈ fst K ⟩)
    (finSetK : (n : ℕ) (h : Fin n → V ℓ)
             → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩)
    where

    numK : (n : ℕ) → ⟨ # n ∈ fst K ⟩
    numK zero    = numK0
    numK (suc n) = sucK (# n) (numK n)

    env-entry : {k : ℕ} (g : Fin k → V ℓ) (i : Fin k)
              → ⟨ pr (# (toℕ i)) (g i) ∈ env g ⟩
    env-entry g i = ∣ lift i , refl ∣₁

    giK : {k : ℕ} (g : Fin k → V ℓ) (i : Fin k)
        → ⟨ env g ∈ fst K ⟩ → ⟨ g i ∈ fst K ⟩
    giK g i envgK = prK (# (toℕ i)) (g i) (Ktr (env-entry g i) envgK) .snd

    envConsK : {k : ℕ} (g : Fin k → V ℓ) (x : V ℓ)
             → ⟨ env g ∈ fst K ⟩ → ⟨ x ∈ fst K ⟩
             → ⟨ env (cons x g) ∈ fst K ⟩
    envConsK g x envgK xK =
      finSetK (suc _) (λ j → pr (# (toℕ j)) (cons x g j))
        (λ { zero    → pairK (# 0) x numK0 xK
           ; (suc i) → pairK (sucV (# (toℕ i))) (g i)
                         (sucK (# (toℕ i)) (numK (toℕ i))) (giK g i envgK) })

  module ConsKClosed
    (numK0 : ⟨ # 0 ∈ fst K ⟩)
    (sucK : (a : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ sucV a ∈ fst K ⟩)
    (pairK : (a b : V ℓ) → ⟨ a ∈ fst K ⟩ → ⟨ b ∈ fst K ⟩ → ⟨ pr a b ∈ fst K ⟩)
    (finSetK : (n : ℕ) (h : Fin n → V ℓ)
             → ((i : Fin n) → ⟨ h i ∈ fst K ⟩) → ⟨ finSet n h ∈ fst K ⟩)
    where

    open EnvClosure numK0 sucK pairK finSetK

    consK-forall : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                 → {k : ℕ} (g : Fin k → V ℓ)
                 → fst z ≡ env g
                 → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                 → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                     consAtL zero (suc zero) (suc (suc zero)) ⟩
                 → ⟨ fst e' ∈ fst K ⟩
    consK-forall γ' ya yc a ar c E z x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
               (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-allin : (γ' : Vec S 2) → (E ya yc b a ar c z w x e' : S)
                → {k : ℕ} (g : Fin k → V ℓ)
                → fst z ≡ env g
                → ⟨ fst z ∈ fst K ⟩ → ⟨ fst x ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-allin γ' E ya yc b a ar c z w x e' g zg zK xK h =
      subst (λ w → ⟨ w ∈ fst K ⟩) (sym e'eq)
        (envConsK g (fst x) (subst (λ w → ⟨ w ∈ fst K ⟩) zg zK) xK)
      where
      e'eq : fst e' ≡ env (cons (fst x) g)
      e'eq = subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
               (e' ∷ x ∷ w ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ') g zg) h

    consK-exist : (γ' : Vec S 2) → (ya yc a ar c E z x e' : S)
                → ⟨ fst ya ∈ fst K ⟩
                → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ') ⊨
                    consAtL zero (suc zero) (suc (suc zero))
                    ∧̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ⟩
                → ⟨ fst e' ∈ fst K ⟩
    consK-exist γ' ya yc a ar c E z x e' yaK h =
      Ktr (h .snd) yaK

levelK : (α : V ℓ) → IsOrd α → S
levelK α o = Lset α , isL-Lset α o

module AtLevel (α : V ℓ) (o : IsOrd α) =
  Fact (levelK α o) (layer-trans (Lset-layer α))
```
