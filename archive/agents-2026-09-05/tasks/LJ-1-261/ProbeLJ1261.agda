{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.261] probe: the finite-supremum merge, the third unpriced L-row.
--
-- [LJ-1.259] measured that the three consK-* close over (K, Ktr) plus ONE
-- new hypothesis, finSetK.  This probe supplies finSetK at the concrete
-- site K = Lset lam.  The merge is an ordinal fact: finitely many stages
-- in lam merge into one stage in lam by iterating the binary union merge.
-- Every stage is a DIRECT term; ord-tri appears only in proofs of
-- propositions, never in a returned stage (P-i: a stage returned through
-- ord-tri forced normalization and walled).
--
-- ONE agda process, GHCRTS="-A64m -I0 -M8g", cap never raised.
-- Never committed.  Written incrementally (C-22).

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-261.ProbeLJ1261 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( IsOrd; isTransV; Lset; Lset-mono; 𝒟ₒ; ∪-trans; isPropIsTransV )
open import L.Axioms.Basic {ℓ} using ( Lset-suc; finSet; module FinOf )
open import L.Ordinal {ℓ} using ( suc-ord; mem-ord; ∅-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Coding.Bound {ℓ} lem using ( Lset-out′ )

open import Cubical.Data.FinData using ( Fin )
open import Cubical.Data.FinData.FiniteChoice using ( choice )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _,_ )
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⋃_; _∪_; union-ax; pairing-ax; ⁅_,_⁆; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈-asFiber; extensionality; _⊆_; _∈ₛ_ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- ===================================================================
-- Lset-fin, re-derived at the raw level (Key.lagda.md:130-135).
-- ===================================================================

Lset-fin : (σ : V ℓ) → IsOrd σ → (k : ℕ) (h : Fin k → V ℓ)
         → ((i : Fin k) → ⟨ h i ∈ Lset σ ⟩) → ⟨ finSet k h ∈ Lset (sucV σ) ⟩
Lset-fin σ oσ k h hm =
  subst (λ w → ⟨ finSet k h ∈ w ⟩) (sym (Lset-suc σ))
    (subst (λ w → ⟨ w ∈ 𝒟ₒ (Lset σ) ⟩)
      (cong (finSet k) (funExt (λ i → fib i .snd)))
      (FinOf.finSet∈𝒟ₒ σ oσ k (λ i → fib i .fst)))
  where
  fib : (i : Fin k) → Σ[ m ∈ ⟪ Lset σ ⟫ ] (⟪ Lset σ ⟫↪ m ≡ h i)
  fib i = ∈-asFiber {a = h i} {b = Lset σ} (hm i)

-- ===================================================================
-- The supply at the concrete site: the finite-supremum merge and its
-- use, finSetK.  All stages are DIRECT; ord-tri appears only in
-- propositions.
-- ===================================================================

module Supply (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ lam ⟩ → ⟨ sucV d ∈ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ lam ⟩) where

  -- Union membership, ∈ₛ-flavoured for the subset lemmas.
  ∈ₛ∪l : (a b x : S) → ⟨ x ∈ₛ a ⟩ → ⟨ x ∈ₛ a ∪ b ⟩
  ∈ₛ∪l a b x x∈a = union-ax ⁅ a , b ⁆ x .snd
    ∣ a , (pairing-ax a b a .snd ∣ inl refl ∣₁ , x∈a) ∣₁

  ∈ₛ∪r : (a b x : S) → ⟨ x ∈ₛ b ⟩ → ⟨ x ∈ₛ a ∪ b ⟩
  ∈ₛ∪r a b x x∈b = union-ax ⁅ a , b ⁆ x .snd
    ∣ b , (pairing-ax a b b .snd ∣ inr refl ∣₁ , x∈b) ∣₁

  -- Union membership, plain-∈-flavoured for the merge.
  ∈∪l : (a b x : S) → ⟨ x ∈ a ⟩ → ⟨ x ∈ a ∪ b ⟩
  ∈∪l a b x h = ∈∈ₛ {a = x} {b = a ∪ b} .snd
    (∈ₛ∪l a b x (∈∈ₛ {a = x} {b = a} .fst h))

  ∈∪r : (a b x : S) → ⟨ x ∈ b ⟩ → ⟨ x ∈ a ∪ b ⟩
  ∈∪r a b x h = ∈∈ₛ {a = x} {b = a ∪ b} .snd
    (∈ₛ∪r a b x (∈∈ₛ {a = x} {b = b} .fst h))

  -- Union of two ordinals is an ordinal.
  ∪-ord : (a b : S) → IsOrd a → IsOrd b → IsOrd (a ∪ b)
  ∪-ord a b oa ob = ∪-trans (oa .fst) (ob .fst) , memTr
    where
    memTr : (x : S) → ⟨ x ∈ a ∪ b ⟩ → isTransV x
    memTr x x∈∪ = PT.rec (isPropIsTransV x)
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (isPropIsTransV x)
          (λ { (inl v≡a) → oa .snd x (∈∈ₛ {a = x} {b = a} .snd
                              (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v))
             ; (inr v≡b) → ob .snd x (∈∈ₛ {a = x} {b = b} .snd
                              (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v)) })
          (pairing-ax a b v .fst v∈pair) })
      (union-ax ⁅ a , b ⁆ x .fst (∈∈ₛ {a = x} {b = a ∪ b} .fst x∈∪))

  -- a ∪ a ≡ a, by extensionality.
  union-idem : (a : S) → a ∪ a ≡ a
  union-idem a = extensionality (a ∪ a) a (sub , sup)
    where
    sup : ⟨ a ⊆ a ∪ a ⟩
    sup x x∈a = ∈ₛ∪l a a x x∈a
    sub : ⟨ a ∪ a ⊆ a ⟩
    sub x x∈∪ = PT.rec (snd (x ∈ₛ a))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ a))
          (λ { (inl v≡a) → subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v
             ; (inr v≡a) → subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v })
          (pairing-ax a a v .fst v∈pair) })
      (union-ax ⁅ a , a ⁆ x .fst x∈∪)

  -- a ∪ b ≡ b when a ⊆ b.
  union-eq : (a b : S) → ⟨ a ⊆ b ⟩ → a ∪ b ≡ b
  union-eq a b a⊆b = extensionality (a ∪ b) b (sub , sup)
    where
    sup : ⟨ b ⊆ a ∪ b ⟩
    sup x x∈b = ∈ₛ∪r a b x x∈b
    sub : ⟨ a ∪ b ⊆ b ⟩
    sub x x∈∪ = PT.rec (snd (x ∈ₛ b))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ b))
          (λ { (inl v≡a) → a⊆b x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v)
             ; (inr v≡b) → subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v })
          (pairing-ax a b v .fst v∈pair) })
      (union-ax ⁅ a , b ⁆ x .fst x∈∪)

  -- a ∪ b ≡ b ∪ a, by extensionality.
  ∪-comm : (a b : S) → a ∪ b ≡ b ∪ a
  ∪-comm a b = extensionality (a ∪ b) (b ∪ a) (sub , sup)
    where
    sub : ⟨ a ∪ b ⊆ b ∪ a ⟩
    sub x x∈ = PT.rec (snd (x ∈ₛ b ∪ a))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ b ∪ a))
          (λ { (inl v≡a) → ∈ₛ∪r b a x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v)
             ; (inr v≡b) → ∈ₛ∪l b a x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v) })
          (pairing-ax a b v .fst v∈pair) })
      (union-ax ⁅ a , b ⁆ x .fst x∈)
    sup : ⟨ b ∪ a ⊆ a ∪ b ⟩
    sup x x∈ = PT.rec (snd (x ∈ₛ a ∪ b))
      (λ { (v , (v∈pair , x∈v)) →
        PT.rec (snd (x ∈ₛ a ∪ b))
          (λ { (inl v≡b) → ∈ₛ∪r a b x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡b x∈v)
             ; (inr v≡a) → ∈ₛ∪l a b x (subst (λ w → ⟨ x ∈ₛ w ⟩) v≡a x∈v) })
          (pairing-ax b a v .fst v∈pair) })
      (union-ax ⁅ b , a ⁆ x .fst x∈)

  -- The binary union of two ordinals in lam stays in lam.  This is the
  -- two-ordinal merge, the analogue of pr∈λ's ord-tri split.
  union2∈λ : (a b : S) → IsOrd a → IsOrd b → ⟨ a ∈ lam ⟩ → ⟨ b ∈ lam ⟩
           → ⟨ a ∪ b ∈ lam ⟩
  union2∈λ a b oa ob ma mb = go (ord-tri a oa b ob)
    where
    go : (⟨ a ∈ b ⟩ ⊎ ((a ≡ b) ⊎ ⟨ b ∈ a ⟩)) → ⟨ a ∪ b ∈ lam ⟩
    go (inl a∈b) = subst (λ w → ⟨ w ∈ lam ⟩) (sym (union-eq a b a⊆b')) mb
      where
      a⊆b' : ⟨ a ⊆ b ⟩
      a⊆b' x x∈a = ∈∈ₛ {a = x} {b = b} .fst
        (ob .fst {x = a} {y = x} (∈∈ₛ {a = x} {b = a} .snd x∈a) a∈b)
    go (inr (inl a≡b)) = subst (λ w → ⟨ w ∈ lam ⟩) (sym (union-idem a) ∙ cong (λ w → a ∪ w) a≡b) ma
    go (inr (inr b∈a)) = subst (λ w → ⟨ w ∈ lam ⟩) (sym (∪-comm a b ∙ union-eq b a b⊆a')) ma
      where
      b⊆a' : ⟨ b ⊆ a ⟩
      b⊆a' x x∈b = ∈∈ₛ {a = x} {b = a} .fst
        (oa .fst {x = b} {y = x} (∈∈ₛ {a = x} {b = b} .snd x∈b) b∈a)

  -- The binary merge: a direct stage (sucV a ∪ sucV b), no ord-tri.
  merge2 : (a b : S) → IsOrd a → IsOrd b → ⟨ a ∈ lam ⟩ → ⟨ b ∈ lam ⟩
         → Σ[ τ ∈ S ] (IsOrd τ × ⟨ τ ∈ lam ⟩ × ⟨ a ∈ τ ⟩ × ⟨ b ∈ τ ⟩)
  merge2 a b oa ob ma mb = τ , (oτ , τ∈ , a∈τ , b∈τ)
    where
    τ = sucV a ∪ sucV b
    oτ = ∪-ord (sucV a) (sucV b) (suc-ord oa) (suc-ord ob)
    τ∈ = union2∈λ (sucV a) (sucV b) (suc-ord oa) (suc-ord ob)
           (succλ a ma) (succλ b mb)
    a∈τ = ∈∪l (sucV a) (sucV b) a (self∈sucV a)
    b∈τ = ∈∪r (sucV a) (sucV b) b (self∈sucV b)

  -- The n-ary merge by folding merge2.
  finSup : (n : ℕ) (γ : Fin n → S)
         → ((i : Fin n) → IsOrd (γ i))
         → ((i : Fin n) → ⟨ γ i ∈ lam ⟩)
         → Σ[ τ ∈ S ] (IsOrd τ × ⟨ τ ∈ lam ⟩ × ((i : Fin n) → ⟨ γ i ∈ τ ⟩))
  finSup zero γ oγ mγ = ∅ , (∅-ord , ∅∈λ , λ ())
  finSup (suc n) γ oγ mγ =
    τ , (oτ , τ∈ , all)
    where
    tail = finSup n (λ j → γ (suc j)) (λ j → oγ (suc j)) (λ j → mγ (suc j))
    τt = tail .fst
    oτt = tail .snd .fst
    τt∈ = tail .snd .snd .fst
    γt∈τt = tail .snd .snd .snd
    m2 = merge2 (γ zero) τt (oγ zero) oτt (mγ zero) τt∈
    τ = m2 .fst
    oτ = m2 .snd .fst
    τ∈ = m2 .snd .snd .fst
    γ0∈τ = m2 .snd .snd .snd .fst
    τt∈τ = m2 .snd .snd .snd .snd
    all : (i : Fin (suc n)) → ⟨ γ i ∈ τ ⟩
    all zero    = γ0∈τ
    all (suc j) = oτ .fst {x = τt} {y = γ (suc j)} (γt∈τt j) τt∈τ

  -- =================================================================
  -- finSetK, the supply.
  -- =================================================================

  finSetK : (n : ℕ) (h : Fin n → V ℓ)
          → ((i : Fin n) → ⟨ h i ∈ Lset lam ⟩)
          → ⟨ finSet n h ∈ Lset lam ⟩
  finSetK n h hm =
    PT.rec (snd (finSet n h ∈ Lset lam)) step
      (choice (λ i → Σ[ δ ∈ S ] (⟨ δ ∈ lam ⟩ × ⟨ h i ∈ Lset (sucV δ) ⟩))
        (λ i → Lset-out′ lam (h i) (hm i)))
    where
    step : ((i : Fin n) → Σ[ δ ∈ S ] (⟨ δ ∈ lam ⟩ × ⟨ h i ∈ Lset (sucV δ) ⟩))
         → ⟨ finSet n h ∈ Lset lam ⟩
    step stages =
      let
        δ : Fin n → S
        δ i = stages i .fst
        δ∈ : (i : Fin n) → ⟨ δ i ∈ lam ⟩
        δ∈ i = stages i .snd .fst
        h∈ : (i : Fin n) → ⟨ h i ∈ Lset (sucV (δ i)) ⟩
        h∈ i = stages i .snd .snd
        oδ : (i : Fin n) → IsOrd (δ i)
        oδ i = mem-ord {A = lam} ordλ (δ i) (δ∈ i)
        sup = finSup n (λ i → sucV (δ i)) (λ i → suc-ord (oδ i))
                (λ i → succλ (δ i) (δ∈ i))
        τ = sup .fst
        oτ = sup .snd .fst
        τ∈ = sup .snd .snd .fst
        sucδ∈τ = sup .snd .snd .snd
        h∈τ : (i : Fin n) → ⟨ h i ∈ Lset τ ⟩
        h∈τ i = Lset-mono {α = τ} {β = sucV (δ i)} (sucδ∈τ i) (h∈ i)
      in
      Lset-mono {α = lam} {β = sucV τ} (succλ τ τ∈)
        (Lset-fin τ oτ n h h∈τ)
