{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.97] probe A: refute the satisfier-in-K members with the
-- tmKeyK shape.
--
-- Ten facts of the family (TwelveAgree.lagda.md:118-243) either have
-- no premise and a conclusion universally quantified over an
-- unconstrained set (succK, keyK-un, keyK-neg, succK-allin,
-- keyK-allin), or have a premise that is a membership in a free
-- variable and is satisfiable at the singleton of the K-slot element
-- (entryK, arSubK-mem/neg/top/imp).  Each refutation below derives
-- Empty.⊥ from the fact's type at an arbitrary frame, using only the
-- delivered regularity lemmas.
--
-- Untracked probe; never committed.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ197A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV; pair-singleton )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )
open import L.Condensation {ℓ} lem using ( succU; keyU )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet using ( sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( _∈ₛ_; ∈∈ₛ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

-- =====================================================================
-- REGULARITY CYCLE LEMMAS (delivered ∈-induction only)
-- =====================================================================
module Reg where
  -- No 2-cycle: a ∈ b ∈ a is refuted by regularity.
  no-2-cycle : (a b : V ℓ) → ⟨ a ∈ b ⟩ → ⟨ b ∈ a ⟩ → Empty.⊥
  no-2-cycle a b a∈b b∈a = P-all a b b∈a a∈b
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P x = (y : V ℓ) → ⟨ y ∈ x ⟩ → ⟨ x ∈ y ⟩ → Empty.⊥
    step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → P y) → P x
    step x ih y y∈x x∈y = ih y y∈x x x∈y y∈x
    P-all : (x : V ℓ) → P x
    P-all = ∈-induction step

  -- No 3-cycle: a ∈ b ∈ c ∈ a is refuted by regularity.
  no-3-cycle : (a b c : V ℓ) → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ a ⟩ → Empty.⊥
  no-3-cycle a b c a∈b b∈c c∈a = P-all a b c a∈b b∈c c∈a
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P x = (y z : V ℓ) → ⟨ x ∈ y ⟩ → ⟨ y ∈ z ⟩ → ⟨ z ∈ x ⟩ → Empty.⊥
    step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → P y) → P x
    step x ih y z x∈y y∈z z∈x = ih z z∈x x y z∈x x∈y y∈z
    P-all : (x : V ℓ) → P x
    P-all = ∈-induction step

  -- No 4-cycle: a ∈ b ∈ c ∈ d ∈ a is refuted by regularity.
  no-4-cycle : (a b c d : V ℓ) → ⟨ a ∈ b ⟩ → ⟨ b ∈ c ⟩ → ⟨ c ∈ d ⟩ → ⟨ d ∈ a ⟩
             → Empty.⊥
  no-4-cycle a b c d a∈b b∈c c∈d d∈a = P-all a b c d a∈b b∈c c∈d d∈a
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P x = (y z w : V ℓ) → ⟨ x ∈ y ⟩ → ⟨ y ∈ z ⟩ → ⟨ z ∈ w ⟩ → ⟨ w ∈ x ⟩ → Empty.⊥
    step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → P y) → P x
    step x ih y z w x∈y y∈z z∈w w∈x = ih w w∈x x y z w∈x x∈y y∈z z∈w
    P-all : (x : V ℓ) → P x
    P-all = ∈-induction step

-- =====================================================================
-- THE REFUTATIONS, one module per frame
-- =====================================================================
module Refute (n : ℕ) (K : Fin (5 + n)) (γ' : S ^ (11 + n)) where

  -- The K slot's underlying element.
  X : S
  X = lookup (suc (suc (suc (suc (suc (suc K)))))) γ'

  A : V ℓ
  A = fst X

  -- A ∈ ⁅ A , A ⁆, by the hierarchy pairing axiom.
  A∈pair : ⟨ A ∈ ⁅ A , A ⁆ ⟩
  A∈pair = ∈∈ₛ {a = A} {b = ⁅ A , A ⁆} .snd
    (pairing-ax A A A .snd ∣ inl refl ∣₁)

  -- A ∈ ⁅ A ⁆s, the singleton of A.
  A∈singl : ⟨ A ∈ ⁅ A ⁆s ⟩
  A∈singl = subst (λ w → ⟨ A ∈ w ⟩) (pair-singleton A) A∈pair

  -- ⁅ A ⁆s ∈ pr A A, the pair's first singleton component.
  singl∈prAA : ⟨ ⁅ A ⁆s ∈ pr A A ⟩
  singl∈prAA = ∈∈ₛ {a = ⁅ A ⁆s} {b = pr A A} .snd
    (pairing-ax ⁅ A ⁆s ⁅ A , A ⁆ ⁅ A ⁆s .snd ∣ inl refl ∣₁)

  -- sucV A ∈ ⁅ sucV A ⁆s.
  sA∈singl : ⟨ sucV A ∈ ⁅ sucV A ⁆s ⟩
  sA∈singl = subst (λ w → ⟨ sucV A ∈ w ⟩)
    (pair-singleton (sucV A))
    (∈∈ₛ {a = sucV A} {b = ⁅ sucV A , sucV A ⁆} .snd
      (pairing-ax (sucV A) (sucV A) (sucV A) .snd ∣ inl refl ∣₁))

  -- ⁅ sucV A ⁆s ∈ pr (sucV A) A.
  sA∈pr : ⟨ ⁅ sucV A ⁆s ∈ pr (sucV A) A ⟩
  sA∈pr = ∈∈ₛ {a = ⁅ sucV A ⁆s} {b = pr (sucV A) A} .snd
    (pairing-ax ⁅ sucV A ⁆s ⁅ sucV A , A ⁆ ⁅ sucV A ⁆s .snd ∣ inl refl ∣₁)

  -- ================================================================
  -- succK (TwelveAgree.lagda.md:205-206): no premise; the conclusion
  -- is sucV (fst ar) ∈ K-slot for an unconstrained ar.  At ar = X the
  -- conclusion is sucV A ∈ A; with self∈sucV A : A ∈ sucV A that is a
  -- 2-cycle, refuted by regularity.
  -- ================================================================
  succK-type = (N : Fin (11 + n)) (E ya yc a ar c : S) →
    succU {11 + n} (suc (suc zero)) (suc zero) zero N
      (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c

  succK-refutes : succK-type → Empty.⊥
  succK-refutes succK =
    Reg.no-2-cycle A (sucV A) (self∈sucV A)
      (succK zero X X X X X X)

  -- ================================================================
  -- keyK-un (TwelveAgree.lagda.md:207-208): no premise; the
  -- conclusion is pr (sucV (fst ar)) (fst a) ∈ K-slot.  At ar = a = X
  -- the conclusion is pr (sucV A) A ∈ A; with A ∈ sucV A ∈
  -- ⁅ sucV A ⁆s ∈ pr (sucV A) A that is a 4-cycle.
  -- ================================================================
  keyK-un-type = (N : Fin (11 + n)) (E ya yc a ar c : S) →
    keyU {11 + n} (suc (suc zero)) (suc zero) zero N
      (suc (suc (suc (suc (suc (suc K)))))) γ' E ya yc a ar c

  keyK-un-refutes : keyK-un-type → Empty.⊥
  keyK-un-refutes keyK-un =
    Reg.no-4-cycle A (sucV A) ⁅ sucV A ⁆s (pr (sucV A) A)
      (self∈sucV A) sA∈singl sA∈pr
      (keyK-un zero X X X X X X)

  -- ================================================================
  -- keyK-neg (TwelveAgree.lagda.md:201-204): no premise; the
  -- conclusion is pr (fst ar) (fst a) ∈ K-slot.  At ar = a = X the
  -- conclusion is pr A A ∈ A; with A ∈ ⁅ A ⁆s ∈ pr A A that is a
  -- 3-cycle.
  -- ================================================================
  keyK-neg-type = (E ya yc a ar c : S) → ⟨
        pr (fst (lookup (suc (suc (suc (suc zero))))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')))
           (fst (lookup (suc (suc (suc zero)))
                 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')))
        ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc
           (suc (suc (suc (suc K)))))))))))) (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩

  keyK-neg-refutes : keyK-neg-type → Empty.⊥
  keyK-neg-refutes keyK-neg =
    Reg.no-3-cycle A ⁅ A ⁆s (pr A A) A∈singl singl∈prAA
      (keyK-neg X X X X X X)

  -- ================================================================
  -- succK-allin (TwelveAgree.lagda.md:224-228): no premise; the
  -- conclusion is sucV (fst ar) ∈ K-slot, same shape as succK.
  -- ================================================================
  succK-allin-type = (E ya yc b a ar c : S) → ⟨
        sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                      (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')))
        ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc
           (suc (suc (suc (suc (suc K))))))))))))) (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩

  succK-allin-refutes : succK-allin-type → Empty.⊥
  succK-allin-refutes succK-allin =
    Reg.no-2-cycle A (sucV A) (self∈sucV A)
      (succK-allin X X X X X X X)

  -- ================================================================
  -- keyK-allin (TwelveAgree.lagda.md:229-235): no premise; the
  -- conclusion is pr (sucV (fst ar)) (fst b) ∈ K-slot, same shape as
  -- keyK-un.
  -- ================================================================
  keyK-allin-type = (E ya yc b a ar c : S) → ⟨
        pr (sucV (fst (lookup (suc (suc (suc (suc (suc zero)))))
                         (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ'))))
           (fst (lookup (suc (suc (suc zero)))
                         (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')))
        ∈ fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc
           (suc (suc (suc (suc (suc K))))))))))))) (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩

  keyK-allin-refutes : keyK-allin-type → Empty.⊥
  keyK-allin-refutes keyK-allin =
    Reg.no-4-cycle A (sucV A) ⁅ sucV A ⁆s (pr (sucV A) A)
      (self∈sucV A) sA∈singl sA∈pr
      (keyK-allin X X X X X X X)

  -- ================================================================
  -- entryK (TwelveAgree.lagda.md:118-120): for arbitrary z, if
  -- pr (fst x) (fst y) ∈ fst z then x, y ∈ K-slot.  Take z = the
  -- L-singleton of pr A A, x = y = X.  The premise is
  -- pr A A ∈ ⁅ pr A A ⁆s, which holds; the conclusion is A ∈ A,
  -- refuted by ∈-irrefl.
  -- ================================================================
  entryK-type = (z x y : S) → ⟨ pr (fst x) (fst y) ∈ fst z ⟩
              → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩
                × ⟨ fst y ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

  zS : S
  zS = pairʟ (prʟ X X) (prʟ X X)

  fstZ≡singl : fst zS ≡ ⁅ pr A A ⁆s
  fstZ≡singl =
      pairʟ-fst (prʟ X X) (prʟ X X)
    ∙ cong₂ ⁅_,_⁆ (prʟ-fst X X) (prʟ-fst X X)
    ∙ pair-singleton (pr A A)

  prAA∈singl : ⟨ pr A A ∈ ⁅ pr A A ⁆s ⟩
  prAA∈singl =
    subst (λ w → ⟨ pr A A ∈ w ⟩) (pair-singleton (pr A A))
      (∈∈ₛ {a = pr A A} {b = ⁅ pr A A , pr A A ⁆} .snd
        (pairing-ax (pr A A) (pr A A) (pr A A) .snd ∣ inl refl ∣₁))

  prAA∈z : ⟨ pr A A ∈ fst zS ⟩
  prAA∈z = subst (λ w → ⟨ pr A A ∈ w ⟩) (sym fstZ≡singl) prAA∈singl

  entryK-refutes : entryK-type → Empty.⊥
  entryK-refutes entryK = ∈-irrefl A (entryK zS X X prAA∈z .fst)

  -- ================================================================
  -- arSubK-mem (TwelveAgree.lagda.md:121-123): if x ∈ ar then x ∈
  -- K-slot.  Take ar = pairʟ X X (the L-singleton of A), x = X.  The
  -- premise A ∈ fst ar holds; the conclusion is A ∈ A.
  -- ================================================================
  arSubK-mem-type = (yc b a ar c x : S) → ⟨ fst x ∈ fst
    (lookup (suc (suc (suc zero))) (yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

  arSubK-mem-refutes : arSubK-mem-type → Empty.⊥
  arSubK-mem-refutes arSubK-mem =
    ∈-irrefl A (arSubK-mem X X X (pairʟ X X) X X
      (subst (λ w → ⟨ A ∈ w ⟩) (sym (pairʟ-fst X X)) A∈pair))

  -- ================================================================
  -- arSubK-neg (TwelveAgree.lagda.md:124-126): if x ∈ ar then x ∈
  -- K-slot.  Same refutation at ar = pairʟ X X.
  -- ================================================================
  arSubK-neg-type = (ya yc a ar c x : S) → ⟨ fst x ∈ fst
    (lookup (suc (suc (suc zero))) (ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

  arSubK-neg-refutes : arSubK-neg-type → Empty.⊥
  arSubK-neg-refutes arSubK-neg =
    ∈-irrefl A (arSubK-neg X X X (pairʟ X X) X X
      (subst (λ w → ⟨ A ∈ w ⟩) (sym (pairʟ-fst X X)) A∈pair))

  -- ================================================================
  -- arSubK-top (TwelveAgree.lagda.md:127-129): if x ∈ ar then x ∈
  -- K-slot.  Same refutation.
  -- ================================================================
  arSubK-top-type = (yc a ar c x : S) → ⟨ fst x ∈ fst
    (lookup (suc (suc zero)) (yc ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

  arSubK-top-refutes : arSubK-top-type → Empty.⊥
  arSubK-top-refutes arSubK-top =
    ∈-irrefl A (arSubK-top X X (pairʟ X X) X X
      (subst (λ w → ⟨ A ∈ w ⟩) (sym (pairʟ-fst X X)) A∈pair))

  -- ================================================================
  -- arSubK-imp (TwelveAgree.lagda.md:130-132): if x ∈ ar then x ∈
  -- K-slot.  Same refutation.
  -- ================================================================
  arSubK-imp-type = (ya yc b a ar c x : S) → ⟨ fst x ∈ fst
    (lookup (suc (suc (suc (suc zero)))) (ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ')) ⟩
    → ⟨ fst x ∈ fst (lookup (suc (suc (suc (suc (suc (suc K)))))) γ') ⟩

  arSubK-imp-refutes : arSubK-imp-type → Empty.⊥
  arSubK-imp-refutes arSubK-imp =
    ∈-irrefl A (arSubK-imp X X X X (pairʟ X X) X X
      (subst (λ w → ⟨ A ∈ w ⟩) (sym (pairʟ-fst X X)) A∈pair))
