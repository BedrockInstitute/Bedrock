{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.89] probe A: the repaired witK, assembled end to end by the
-- finite-family route.
--
-- The route of [LJ-1.88], all three steps measured:
--
--   1. w ⊆ AllCodes A, at the produced witness w = clo f h φ
--      (clo⊆All, ProbeLJ185B.agda:58-68, machine-checked).
--   2. AllCodes A ∈ Lset lam, the frame hypothesis (premise).
--   3. A finite family of members of a stage is a DEFINABLE subset of
--      that stage (finSet∈𝒟ₒ, L.Axioms.Basic.lagda.md:352-354), and the
--      successor stage IS the definable power set (Lset-suc, :196).
--
-- Assembly: Lset-out peels AllCodes A ∈ Lset lam to δ ∈ lam with
-- AllCodes A ∈ 𝒟ₒ (Lset δ); 𝒟ₒ∋⊆ plus clo⊆All give w ⊆ Lset δ; the
-- closure is a finite enumeration (closureFin below, the delivered
-- recursive closure shape L.Coding.InL.lagda.md:258-270); finSet-stage
-- lands the enumerated family one level up; succλ and Lset-mono carry
-- it into Lset lam.
--
-- The term is STAGED, NOT DISCHARGED (C-38): BoundedSubsetAt has no
-- instantiation, so nothing supplies the frame hypothesis
-- AllCodes A ∈ Lset lam.  A consumer of the bounded-subset lemma would
-- supply it.
--
-- Untracked probe; one Agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ189A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
open import FOL.Syntax
  using ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ∋⊆; Lset-out; Lset-mono )
open import L.Axioms.Basic {ℓ}
  using ( finSet; finSet-in; finSet-out; module FinOf; Lset-suc )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Coding.InL {ℓ}
  using ( key; closure; closure-inv; sgl-in; sgl-out; cup-inl; cup-inr; cup-out )
open import L.Coding.Closed {ℓ} using ( clo )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes; key∈AllCodes )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ; ∈ₛ⟪_⟫↪_; extensionality; ∈-asFiber; _⊆_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_⁆s; _∪_; module InfinitySet )
open import Cubical.Data.FinData using ( Fin; zero; suc; _++Fin_ )
open import Cubical.Data.FinData.Properties
  using ( module FinSumChar; ++FinElim )
open import Cubical.Data.Nat using ( ℕ; _+_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( sym; subst; cong; cong₂; funExt )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

Sʟ : Type (ℓ-suc ℓ)
Sʟ = ZFStructure.S 𝒮ʟ

-- =====================================================================
-- THE FINITENESS OF THE CLOSURE, AS A FINITE ENUMERATION.
-- The closure (L.Coding.InL.lagda.md:258-270) is a recursive family of
-- singletons and binary unions.  Each singleton is finSet 1, and a
-- binary union of two finite families is the ++Fin join of their
-- enumerations (finSet (m + n) (g ++Fin h)).  The recursion below
-- reads the closure's own shape and hands back, for every formula, the
-- enumeration together with the extensional identity.
-- =====================================================================
module ClosureFin {K : Type ℓ} (f : K → V ℓ) (h : (k : K) → ⟨ isL (f k) ⟩) where

  Key : ∀ {n} → Formula K n → V ℓ
  Key = key f h

  Cl : ∀ {n} → Formula K n → V ℓ
  Cl = closure f h

  -- A singleton is a one-element finite family.
  sglFin : (x : V ℓ) → ⁅ x ⁆s ≡ finSet (suc zero) (λ _ → x)
  sglFin x = extensionality (⁅ x ⁆s) (finSet (suc zero) (λ _ → x)) (sub₁ , sub₂)
    where
    sub₁ : ⟨ ⁅ x ⁆s ⊆ finSet (suc zero) (λ _ → x) ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = finSet (suc zero) (λ _ → x)} .fst
      (PT.rec (snd (y ∈ finSet (suc zero) (λ _ → x)))
        (λ q → finSet-in (suc zero) (λ _ → x) y ∣ zero , sym q ∣₁)
        ∣ sgl-out x y (∈∈ₛ {a = y} {b = ⁅ x ⁆s} .snd y∈ₛ) ∣₁)
    sub₂ : ⟨ finSet (suc zero) (λ _ → x) ⊆ ⁅ x ⁆s ⟩
    sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ ⁅ x ⁆s))
      (λ { (i , q) → ∈∈ₛ {a = y} {b = ⁅ x ⁆s} .fst (sgl-in x y (sym q)) })
      (finSet-out (suc zero) (λ _ → x) y
        (∈∈ₛ {a = y} {b = finSet (suc zero) (λ _ → x)} .snd y∈ₛ))

  -- A binary union of two finite families is the join of their
  -- enumerations.
  unionFin : {n m : ℕ} {g : Fin n → V ℓ} {h : Fin m → V ℓ}
           → finSet n g ∪ finSet m h ≡ finSet (n + m) (g ++Fin h)
  unionFin {n} {m} {g} {h} =
    extensionality (finSet n g ∪ finSet m h)
      (finSet (n + m) (g ++Fin h)) (sub₁ , sub₂)
    where
    sub₁ : ⟨ finSet n g ∪ finSet m h ⊆ finSet (n + m) (g ++Fin h) ⟩
    sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = finSet (n + m) (g ++Fin h)} .fst
      (PT.rec (snd (y ∈ finSet (n + m) (g ++Fin h))) go
        (cup-out (finSet n g) (finSet m h) y
          (∈∈ₛ {a = y} {b = finSet n g ∪ finSet m h} .snd y∈ₛ)))
      where
      go : (⟨ y ∈ finSet n g ⟩ ⊎ ⟨ y ∈ finSet m h ⟩)
         → ⟨ y ∈ finSet (n + m) (g ++Fin h) ⟩
      go (inl yg) = PT.rec (snd (y ∈ finSet (n + m) (g ++Fin h))) left
        (finSet-out n g y yg)
        where
        left : Σ[ i ∈ Fin n ] (g i ≡ y)
             → ⟨ y ∈ finSet (n + m) (g ++Fin h) ⟩
        left (i , q) = finSet-in (n + m) (g ++Fin h) y
          ∣ FinSumChar.fun n m (inl i) , sym (FinSumChar.++FinInl n m g h i) ∙ q ∣₁
      go (inr yh) = PT.rec (snd (y ∈ finSet (n + m) (g ++Fin h))) right
        (finSet-out m h y yh)
        where
        right : Σ[ i ∈ Fin m ] (h i ≡ y)
             → ⟨ y ∈ finSet (n + m) (g ++Fin h) ⟩
        right (i , q) = finSet-in (n + m) (g ++Fin h) y
          ∣ FinSumChar.fun n m (inr i) , sym (FinSumChar.++FinInr n m g h i) ∙ q ∣₁

    sub₂ : ⟨ finSet (n + m) (g ++Fin h) ⊆ finSet n g ∪ finSet m h ⟩
    sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = finSet n g ∪ finSet m h} .fst
      (PT.rec (snd (y ∈ finSet n g ∪ finSet m h)) go
        (finSet-out (n + m) (g ++Fin h) y
          (∈∈ₛ {a = y} {b = finSet (n + m) (g ++Fin h)} .snd y∈ₛ)))
      where
      P : V ℓ → Type (ℓ-suc ℓ)
      P x = ∥ (Σ[ j ∈ Fin n ] (x ≡ g j)) ⊎ (Σ[ j ∈ Fin m ] (x ≡ h j)) ∥₁

      PU : (j : Fin n) → P (g j)
      PU j = ∣ inl (j , refl) ∣₁

      PV : (j : Fin m) → P (h j)
      PV j = ∣ inr (j , refl) ∣₁

      go : Σ[ i ∈ Fin (n + m) ] ((g ++Fin h) i ≡ y)
         → ⟨ y ∈ finSet n g ∪ finSet m h ⟩
      go (i , q) = PT.rec (snd (y ∈ finSet n g ∪ finSet m h)) side
        (subst P q
          (++FinElim {P = P} {n = n} {m = m} g h PU PV i))
        where
        side : (Σ[ j ∈ Fin n ] (y ≡ g j)) ⊎ (Σ[ j ∈ Fin m ] (y ≡ h j))
             → ⟨ y ∈ finSet n g ∪ finSet m h ⟩
        side (inl (j , r)) = cup-inl (finSet n g) (finSet m h) y
          (finSet-in n g y ∣ j , sym r ∣₁)
        side (inr (j , r)) = cup-inr (finSet n g) (finSet m h) y
          (finSet-in m h y ∣ j , sym r ∣₁)

  -- A binary connective: the closure is the singleton of the key,
  -- union the closures of the two subformulas; the enumeration joins.
  bin : ∀ {n} (φ : Formula K n) (a b : Formula K n)
      → Σ[ mₐ ∈ ℕ ] Σ[ gₐ ∈ (Fin mₐ → V ℓ) ] (Cl a ≡ finSet mₐ gₐ)
      → Σ[ mᵦ ∈ ℕ ] Σ[ gᵦ ∈ (Fin mᵦ → V ℓ) ] (Cl b ≡ finSet mᵦ gᵦ)
      → Σ[ m ∈ ℕ ] Σ[ g ∈ (Fin m → V ℓ) ]
          (⁅ Key φ ⁆s ∪ (Cl a ∪ Cl b) ≡ finSet m g)
  bin φ a b (mₐ , gₐ , qₐ) (mᵦ , gᵦ , qᵦ) =
    suc zero + (mₐ + mᵦ)
    , _++Fin_ {n = suc zero} {m = mₐ + mᵦ}
        (λ _ → Key φ) (_++Fin_ {n = mₐ} {m = mᵦ} gₐ gᵦ) , q
    where
    q : ⁅ Key φ ⁆s ∪ (Cl a ∪ Cl b)
      ≡ finSet (suc zero + (mₐ + mᵦ))
          (_++Fin_ {n = suc zero} {m = mₐ + mᵦ}
            (λ _ → Key φ) (_++Fin_ {n = mₐ} {m = mᵦ} gₐ gᵦ))
    q = cong (λ w → ⁅ Key φ ⁆s ∪ w)
          ((cong₂ _∪_ qₐ qᵦ)
            ∙ unionFin {n = mₐ} {m = mᵦ} {g = gₐ} {h = gᵦ})
      ∙ cong (λ w → w ∪ finSet (mₐ + mᵦ)
            (_++Fin_ {n = mₐ} {m = mᵦ} gₐ gᵦ)) (sglFin (Key φ))
      ∙ unionFin {n = suc zero} {m = mₐ + mᵦ}
          {g = λ _ → Key φ}
          {h = _++Fin_ {n = mₐ} {m = mᵦ} gₐ gᵦ}

  -- A unary connective: the closure is the singleton of the key, union
  -- the closure of the subformula; the enumeration prepends the key.
  un : ∀ {n m} (φ : Formula K n) (a : Formula K m)
     → Σ[ mₐ ∈ ℕ ] Σ[ gₐ ∈ (Fin mₐ → V ℓ) ] (Cl a ≡ finSet mₐ gₐ)
     → Σ[ m ∈ ℕ ] Σ[ g ∈ (Fin m → V ℓ) ]
         (⁅ Key φ ⁆s ∪ Cl a ≡ finSet m g)
  un φ a (mₐ , gₐ , qₐ) =
    suc zero + mₐ , _++Fin_ {n = suc zero} {m = mₐ} (λ _ → Key φ) gₐ , q
    where
    q : ⁅ Key φ ⁆s ∪ Cl a ≡ finSet (suc zero + mₐ) ((λ _ → Key φ) ++Fin gₐ)
    q = cong (λ w → ⁅ Key φ ⁆s ∪ w) qₐ
      ∙ cong (λ w → w ∪ finSet mₐ gₐ) (sglFin (Key φ))
      ∙ unionFin {n = suc zero} {m = mₐ} {g = λ _ → Key φ} {h = gₐ}

  -- The closure, as a finite enumeration: every closure is extensionally
  -- a finSet over the keys of its subformulas, by recursion on the
  -- formula (the delivered closure shape, L.Coding.InL.lagda.md:258-270).
  closureFin : ∀ {n} (φ : Formula K n)
             → Σ[ m ∈ ℕ ] Σ[ g ∈ (Fin m → V ℓ) ] (Cl φ ≡ finSet m g)
  closureFin φ@(t ∈̇ u) = suc zero , (λ _ → Key φ) , sglFin (Key φ)
  closureFin φ@(t ≐ u) = suc zero , (λ _ → Key φ) , sglFin (Key φ)
  closureFin φ@⊤̇ = suc zero , (λ _ → Key φ) , sglFin (Key φ)
  closureFin φ@⊥̇ = suc zero , (λ _ → Key φ) , sglFin (Key φ)
  closureFin φ@(a ∧̇ b) = bin φ a b (closureFin a) (closureFin b)
  closureFin φ@(a ∨̇ b) = bin φ a b (closureFin a) (closureFin b)
  closureFin φ@(a ⇒̇ b) = bin φ a b (closureFin a) (closureFin b)
  closureFin φ@(¬̇ a) = un φ a (closureFin a)
  closureFin φ@(∃̇ a) = un φ a (closureFin a)
  closureFin φ@(∀̇ a) = un φ a (closureFin a)
  closureFin φ@(∀̇∈ t a) = un φ a (closureFin a)
  closureFin φ@(∃̇∈ t a) = un φ a (closureFin a)

-- =====================================================================
-- THE REPAIRED witK AT THE WITNESS'S BIRTH SITE.
-- Frame parameters are module-level (P-h): the carrier A, the limit
-- stage lam with its ordinality and successor-closure succλ, exactly
-- the frame hypotheses of BoundedSubsetAt
-- (L.BoundedSubset.lagda.md:1396-1402).
-- =====================================================================
module Frame (A : Sʟ) (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) where

  ι₀ : ⟪ fst A ⟫ → V ℓ
  ι₀ = ⟪ fst A ⟫↪

  ι∈₀ : (m : ⟪ fst A ⟫) → ⟨ ι₀ m ∈ fst A ⟩
  ι∈₀ m = ∈∈ₛ {a = ι₀ m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

  ιL₀ : (m : ⟪ fst A ⟫) → ⟨ isL (ι₀ m) ⟩
  ιL₀ m = isL-trans {x = fst A} {y = ι₀ m} (ι∈₀ m) (A .snd)

  module CF = ClosureFin ι₀ ιL₀

  -- The premise w ⊆ AllCodes A at the produced witness, machine-checked
  -- in [LJ-1.85] (ProbeLJ185B.agda:58-68), restated at the frame.
  clo⊆All : {n : ℕ} (φ : Formula ⟪ fst A ⟫ n) (x : V ℓ)
          → ⟨ x ∈ fst (clo ι₀ ιL₀ φ) ⟩ → ⟨ x ∈ fst (AllCodes A) ⟩
  clo⊆All φ x hx = PT.rec (snd (x ∈ fst (AllCodes A))) go
    (closure-inv ι₀ ιL₀ φ x hx)
    where
    go : Σ[ m ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst A ⟫ m ]
           ((x ≡ key ι₀ ιL₀ ψ)
            × ((z : V ℓ) → ⟨ z ∈ fst (clo ι₀ ιL₀ ψ) ⟩ → ⟨ z ∈ fst (clo ι₀ ιL₀ φ) ⟩))
       → ⟨ x ∈ fst (AllCodes A) ⟩
    go (m , ψ , q , _) = subst (λ w → ⟨ w ∈ fst (AllCodes A) ⟩) (sym q)
      (key∈AllCodes A ψ)

  -- The decisive finite-family step, restated from ProbeLJ188A.agda:56-61.
  finSet-stage : (σ : V ℓ) (oσ : IsOrd σ) (n : ℕ) (g : Fin n → ⟪ Lset σ ⟫)
               → ⟨ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i)) ∈ Lset (sucV σ) ⟩
  finSet-stage σ oσ n g =
    subst (λ w → ⟨ finSet n (λ i → ⟪ Lset σ ⟫↪ (g i)) ∈ w ⟩)
      (sym (Lset-suc σ))
      (FinOf.finSet∈𝒟ₒ σ oσ n g)

  -- THE REPAIRED witK, per witness, at the witness's birth site.
  -- The three inputs of the route: the frame hypothesis AllCodes A ∈
  -- Lset lam, the premise w ⊆ AllCodes A (supplied at the birth site by
  -- clo⊆All), and the delivered finiteness of the subformula closure
  -- (closureFin, from L.Coding.InL.lagda.md:258-270).
  witK : {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
       → ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩
       → ⟨ fst (clo ι₀ ιL₀ φ) ∈ˢ Lset lam ⟩
  witK {n} φ All∈Lλ =
    PT.rec (snd (fst (clo ι₀ ιL₀ φ) ∈ˢ Lset lam)) go
      (Lset-out lam (fst (AllCodes A)) All∈Lλ)
    where
    go : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩ × ⟨ fst (AllCodes A) ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ fst (clo ι₀ ιL₀ φ) ∈ˢ Lset lam ⟩
    go (δ , δ∈λ , AC∈𝒟ₒδ) =
      Lset-mono {α = lam} {β = sucV δ} (succλ δ δ∈λ)
        {x = fst (clo ι₀ ιL₀ φ)} closure∈Lsuc
      where
      w⊆Lδ : (z : V ℓ) → ⟨ z ∈ fst (clo ι₀ ιL₀ φ) ⟩ → ⟨ z ∈ Lset δ ⟩
      w⊆Lδ z z∈w = 𝒟ₒ∋⊆ (Lset δ) (fst (AllCodes A)) AC∈𝒟ₒδ z
        (clo⊆All φ z z∈w)

      rec = CF.closureFin φ
      m = rec .fst
      g = rec .snd .fst
      eq = rec .snd .snd

      gδ : Fin m → ⟪ Lset δ ⟫
      gδ i = ∈-asFiber {a = g i} {b = Lset δ}
        (w⊆Lδ (g i)
          (subst (λ w → ⟨ g i ∈ w ⟩) (sym eq)
            (finSet-in m g (g i) ∣ i , refl ∣₁))) .fst

      qδ : (i : Fin m) → ⟪ Lset δ ⟫↪ (gδ i) ≡ g i
      qδ i = ∈-asFiber {a = g i} {b = Lset δ}
        (w⊆Lδ (g i)
          (subst (λ w → ⟨ g i ∈ w ⟩) (sym eq)
            (finSet-in m g (g i) ∣ i , refl ∣₁))) .snd

      eqδ : fst (clo ι₀ ιL₀ φ)
          ≡ finSet m (λ i → ⟪ Lset δ ⟫↪ (gδ i))
      eqδ = eq ∙ cong (finSet m) (funExt (λ i → sym (qδ i)))

      closure∈Lsuc : ⟨ fst (clo ι₀ ιL₀ φ) ∈ Lset (sucV δ) ⟩
      closure∈Lsuc = subst (λ w → ⟨ w ∈ Lset (sucV δ) ⟩) (sym eqδ)
        (finSet-stage δ (mem-ord {A = lam} ordλ δ δ∈λ) m gδ)
