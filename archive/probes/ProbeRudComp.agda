{-# OPTIONS --cubical --safe --guardedness #-}
-- ProbeRudComp: miniature price of the realization induction of the rud
-- route: every Delta-0-definable subset of a transitive u is EVAL of a
-- finite composite of basis operations.  Probe-local, untracked, exempt
-- from make check and from the literate format.  No postulates, no holes.
module ProbeRudComp (ℓ : Agda.Primitive.Level) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isProp×)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.HITs.CumulativeHierarchy.Base using (V; _∈_; elimProp)
open import Cubical.HITs.CumulativeHierarchy.Properties
  using (_∈ₛ_; _⊆_; extensionality; _≡ₕ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; identityPrinciple)
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using (⁅_∶_⁆; separation-ax)
open import Cubical.Functions.Logic
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using (Acc; acc; isPropAcc; WellFounded; wf→x≮x)

-- Explicit-level propositional connectives for signatures (the library
-- connectives carry an unsolved result level that fails in type positions).

infixr 8 _⊓ₚ_ _⊔ₚ_ _⊓ₚ⁺_ _⊓₂_
infixr 4 _⇔ₚ_

_⊓ₚ_ : hProp ℓ → hProp ℓ → hProp ℓ
A ⊓ₚ B = A ⊓ B

_⊓ₚ⁺_ : hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ)
A ⊓ₚ⁺ B = A ⊓ B

_⊓₂_ : hProp ℓ → hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ)
A ⊓₂ B = A ⊓ B

_⊔ₚ_ : hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ) → hProp (ℓ-suc ℓ)
A ⊔ₚ B = A ⊔ B

¬ₚ : hProp ℓ → hProp ℓ
¬ₚ A = ¬ A

_⇔ₚ_ : hProp ℓ → hProp ℓ → hProp ℓ
A ⇔ₚ B = A ⇔ B

∃ₚ : (V ℓ → hProp ℓ) → hProp (ℓ-suc ℓ)
∃ₚ P = ∃[ x ] P x

∃ₚ⁺ : (V ℓ → hProp (ℓ-suc ℓ)) → hProp (ℓ-suc ℓ)
∃ₚ⁺ P = ∃[ x ] P x

-- ====================================================================
-- 1. The abstract basis (lesson P-h: module parameters, nothing unfolds;
--    the probe stays neutral between the SZ F0..F15 and Mathias R0..R8
--    bases).  The induction consumes diff, inter, union, col, chSep and
--    (in module Realize) img; pair/prod/mem are carried so the interface
--    spans both candidate bases, and are consumed by the relation-route
--    version that the extrapolation covers.
-- ====================================================================

module Basis
  (pairOp : V ℓ → V ℓ → V ℓ)
  (pairSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ pairOp a b ⟩ → ⟨ (y ≡ₕ a) ⊔ₚ (y ≡ₕ b) ⟩)
    × (⟨ (y ≡ₕ a) ⊔ₚ (y ≡ₕ b) ⟩ → ⟨ y ∈ₛ pairOp a b ⟩))
  (diffOp : V ℓ → V ℓ → V ℓ)
  (diffSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ diffOp a b ⟩ → ⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥))
    × ((⟨ y ∈ₛ a ⟩ × (⟨ y ∈ₛ b ⟩ → Empty.⊥)) → ⟨ y ∈ₛ diffOp a b ⟩))
  (interOp : V ℓ → V ℓ → V ℓ)
  (interSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ interOp a b ⟩ → ⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩)
    × ((⟨ y ∈ₛ a ⟩ × ⟨ y ∈ₛ b ⟩) → ⟨ y ∈ₛ interOp a b ⟩))
  (prodOp : V ℓ → V ℓ → V ℓ)
  (prodSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ prodOp a b ⟩
       → ⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z))))) ⟩)
    × (⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ b) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z))))) ⟩
       → ⟨ y ∈ₛ prodOp a b ⟩))
  (memOp : V ℓ → V ℓ)
  (memSpec : (a y : V ℓ)
    → (⟨ y ∈ₛ memOp a ⟩
       → ⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂ ((x ∈ₛ z) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z)))))) ⟩)
    × (⟨ ∃ₚ⁺ (λ x → ∃ₚ⁺ (λ z → (x ∈ₛ a) ⊓₂ ((z ∈ₛ a) ⊓₂ ((x ∈ₛ z) ⊓₂ (y ≡ₕ pairOp (pairOp x x) (pairOp x z)))))) ⟩
       → ⟨ y ∈ₛ memOp a ⟩))
  (unionOp : V ℓ → V ℓ)
  (unionSpec : (a y : V ℓ)
    → (⟨ y ∈ₛ unionOp a ⟩ → ⟨ ∃ₚ (λ z → (z ∈ₛ a) ⊓ₚ (y ∈ₛ z)) ⟩)
    × (⟨ ∃ₚ (λ z → (z ∈ₛ a) ⊓ₚ (y ∈ₛ z)) ⟩ → ⟨ y ∈ₛ unionOp a ⟩))
  (colOp : V ℓ → V ℓ → V ℓ)
  (colSpec : (a b y : V ℓ)
    → (⟨ y ∈ₛ colOp a b ⟩ → ⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩)
    × ((⟨ y ∈ₛ b ⟩ × ⟨ a ∈ₛ y ⟩) → ⟨ y ∈ₛ colOp a b ⟩))
  (chSepOp : V ℓ → V ℓ → V ℓ → V ℓ)
  (chSepSpec : (a b c y : V ℓ)
    → (⟨ y ∈ₛ chSepOp a b c ⟩ → ⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩)
    × ((⟨ y ∈ₛ c ⟩ × ⟨ a ∈ₛ b ⟩) → ⟨ y ∈ₛ chSepOp a b c ⟩))
  where
  
  -- 2. Transitivity (∈ₛ form) and the self-membership refutation ---------
  
  Trans : V ℓ → Type (ℓ-suc ℓ)
  Trans u = (x y : V ℓ) → ⟨ x ∈ₛ y ⟩ → ⟨ y ∈ₛ u ⟩ → ⟨ x ∈ₛ u ⟩
  
  ∈ₛ-wf : WellFounded (λ (x y : V ℓ) → ⟨ x ∈ y ⟩)
  ∈ₛ-wf = elimProp (λ s → isPropAcc s)
    (λ X ix rec → acc (λ y y∈ → PT.rec (isPropAcc y)
      (λ { (i , p) → subst (Acc (λ a b → ⟨ a ∈ b ⟩)) p (rec i) }) y∈))
  
  ∈ₛ-irrefl : (x : V ℓ) → ⟨ x ∈ₛ x ⟩ → Empty.⊥
  ∈ₛ-irrefl x h = wf→x≮x ∈ₛ-wf {x = x} (∈∈ₛ {a = x} {b = x} .snd h)
  
  -- 3. The miniature Delta-0 fragment.  FmQ = quantifier-free body language
  --    (atoms x ∈ y only, ∧, ¬); Fm adds bounded ∃ whose bodies are
  --    quantifier-free.  Variables: 0 = the separated x, 1 = the family
  --    variable (family theorem), 2..n+1 = the parameters ρ.  bex j ψ:
  --    ∃ fresh ∈ ρⱼ, fresh appended at index 1, parameters shifted.
  
  data FmQ : ℕ → Type where
    memq : {n : ℕ} → Fin n → Fin n → FmQ n
    _∧q_ : {n : ℕ} → FmQ n → FmQ n → FmQ n
    ¬q_  : {n : ℕ} → FmQ n → FmQ n
  
  data Fm : ℕ → Type where
    emb  : {n : ℕ} → FmQ n → Fm n
    _∧₀_ : {n : ℕ} → Fm n → Fm n → Fm n
    ¬₀_  : {n : ℕ} → Fm n → Fm n
    bex  : {n : ℕ} → Fin n → FmQ (suc (suc n)) → Fm (suc n)
  
  insert : {n : ℕ} → V ℓ → (Fin (suc n) → V ℓ) → Fin (suc (suc n)) → V ℓ
  insert z σ zero = σ zero
  insert z σ (suc zero) = z
  insert z σ (suc (suc k)) = σ (suc k)
  
  env₁ : {n : ℕ} → (Fin n → V ℓ) → V ℓ → Fin (suc n) → V ℓ
  env₁ ρ x zero = x
  env₁ ρ x (suc k) = ρ k
  
  env₂ : {n : ℕ} → (Fin n → V ℓ) → V ℓ → V ℓ → Fin (suc (suc n)) → V ℓ
  env₂ ρ y x = insert y (env₁ ρ x)
  
  SatQ : {n : ℕ} → FmQ n → (Fin n → V ℓ) → hProp ℓ
  SatQ (memq i j) σ = σ i ∈ₛ σ j
  SatQ (φ ∧q ψ) σ = SatQ φ σ ⊓ SatQ ψ σ
  SatQ (¬q φ) σ = ¬ SatQ φ σ
  
  Sat : {n : ℕ} → Fm n → (Fin n → V ℓ) → hProp ℓ
  Sat (emb φ) σ = SatQ φ σ
  Sat (φ ∧₀ ψ) σ = Sat φ σ ⊓ Sat ψ σ
  Sat (¬₀ φ) σ = ¬ Sat φ σ
  Sat (bex j ψ) σ = ∃[ i ] (SatQ ψ (insert (⟪ σ (suc j) ⟫↪ i) σ))
  
  -- 4. The definable subset: probe-local sett, the library's separation
  --    constructor (whose membership classification is `separation-ax`).
  
  SepSet : {n : ℕ} → (u : V ℓ) → Fm (suc n) → (Fin n → V ℓ) → V ℓ
  SepSet u φ ρ = ⁅ u ∶ (λ x → Sat φ (env₁ ρ x)) ⁆
  
  sep-mem : {n : ℕ} (u : V ℓ) (φ : Fm (suc n)) (ρ : Fin n → V ℓ) (x : V ℓ)
          → ⟨ (x ∈ₛ SepSet u φ ρ) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Sat φ (env₁ ρ x)) ⟩
  sep-mem u φ ρ x = separation-ax u (λ y → Sat φ (env₁ ρ y)) x
  
  -- 5. Unary composites (the rud functions of the miniature): one free
  --    variable, closed under the consumed set-formers.  The image
  --    operation is applied at the composite level in module Realize.
  
  data Comp1 : Type (ℓ-suc ℓ) where
    varF   : Comp1
    conF   : V ℓ → Comp1
    interF : Comp1 → Comp1 → Comp1
    diffF  : Comp1 → Comp1 → Comp1
    unionF : Comp1 → Comp1
    colF   : Comp1 → Comp1 → Comp1
    chSepF : Comp1 → Comp1 → Comp1 → Comp1
  
  eval1 : Comp1 → V ℓ → V ℓ
  eval1 varF y = y
  eval1 (conF x) y = x
  eval1 (interF f g) y = interOp (eval1 f y) (eval1 g y)
  eval1 (diffF f g) y = diffOp (eval1 f y) (eval1 g y)
  eval1 (unionF f) y = unionOp (eval1 f y)
  eval1 (colF f g) y = colOp (eval1 f y) (eval1 g y)
  eval1 (chSepF f g h) y = chSepOp (eval1 f y) (eval1 g y) (eval1 h y)
  
  -- 6. Realization.  The image operation's function argument is the
  --    composite syntax, so it is parameterized one level down (this is the
  --    R8/F8 "image of a family" of the paper blueprint).
  
  module Realize
    (imgOp : Comp1 → V ℓ → V ℓ)
    (imgSpec : (f : Comp1) (p z : V ℓ)
      → (⟨ z ∈ₛ imgOp f p ⟩ → ⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ eval1 f y)) ⟩)
      × (⟨ ∃ₚ⁺ (λ y → (y ∈ₛ p) ⊓₂ (z ≡ₕ eval1 f y)) ⟩ → ⟨ z ∈ₛ imgOp f p ⟩))
      where
  
    data Comp : Type (ℓ-suc ℓ) where
      conC   : V ℓ → Comp
      interC : Comp → Comp → Comp
      diffC  : Comp → Comp → Comp
      unionC : Comp → Comp
      colC   : Comp → Comp → Comp
      chSepC : Comp → Comp → Comp → Comp
      imgC   : Comp1 → Comp → Comp
  
    eval : Comp → V ℓ
    eval (conC x) = x
    eval (interC a b) = interOp (eval a) (eval b)
    eval (diffC a b) = diffOp (eval a) (eval b)
    eval (unionC a) = unionOp (eval a)
    eval (colC a b) = colOp (eval a) (eval b)
    eval (chSepC a b c) = chSepOp (eval a) (eval b) (eval c)
    eval (imgC f a) = imgOp f (eval a)
  
    -- clause helpers ------------------------------------------------------
  
    sepDiag-spec : (u x : V ℓ) → ⟨ (x ∈ₛ diffOp u u) ⇔ₚ ((x ∈ₛ u) ⊓ₚ (x ∈ₛ x)) ⟩
    sepDiag-spec u x = fwd , bwd
      where
      fwd : ⟨ x ∈ₛ diffOp u u ⟩ → ⟨ x ∈ₛ u ⟩ × ⟨ x ∈ₛ x ⟩
      fwd h = Empty.rec (diffSpec u u x .fst h .snd (diffSpec u u x .fst h .fst))
      bwd : ⟨ x ∈ₛ u ⟩ × ⟨ x ∈ₛ x ⟩ → ⟨ x ∈ₛ diffOp u u ⟩
      bwd (p , xx) = Empty.rec (∈ₛ-irrefl x xx)
  
    inter-char : (a b : Comp) (x : V ℓ)
              → ⟨ (x ∈ₛ eval (interC a b)) ⇔ₚ ((x ∈ₛ eval a) ⊓ₚ (x ∈ₛ eval b)) ⟩
    inter-char a b x = interSpec (eval a) (eval b) x
  
    neg-char : (u : V ℓ) (a : Comp) (x : V ℓ)
            → ⟨ (x ∈ₛ eval (diffC (conC u) a)) ⇔ₚ ((x ∈ₛ u) ⊓ₚ ¬ₚ (x ∈ₛ eval a)) ⟩
    neg-char u a x = diffSpec u (eval a) x
  
    inter-char1 : (f g : Comp1) (y x : V ℓ)
               → ⟨ (x ∈ₛ eval1 (interF f g) y) ⇔ₚ ((x ∈ₛ eval1 f y) ⊓ₚ (x ∈ₛ eval1 g y)) ⟩
    inter-char1 f g y x = interSpec (eval1 f y) (eval1 g y) x
  
    neg-char1 : (u : V ℓ) (f : Comp1) (y x : V ℓ)
             → ⟨ (x ∈ₛ eval1 (diffF (conF u) f) y) ⇔ₚ ((x ∈ₛ u) ⊓ₚ ¬ₚ (x ∈ₛ eval1 f y)) ⟩
    neg-char1 u f y x = diffSpec u (eval1 f y) x

    and-ch : (u : V ℓ) (a b : Comp) (Q₁ Q₂ : V ℓ → hProp ℓ)
           → ((x : V ℓ) → ⟨ (x ∈ₛ eval a) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Q₁ x) ⟩)
           → ((x : V ℓ) → ⟨ (x ∈ₛ eval b) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Q₂ x) ⟩)
           → (x : V ℓ) → ⟨ (x ∈ₛ eval (interC a b)) ⇔ₚ ((x ∈ₛ u) ⊓ₚ (Q₁ x ⊓ₚ Q₂ x)) ⟩
    and-ch u a b Q₁ Q₂ ch₁ ch₂ x = fwd , bwd
      where
      fwd : ⟨ x ∈ₛ eval (interC a b) ⟩ → ⟨ x ∈ₛ u ⟩ × ⟨ Q₁ x ⊓ₚ Q₂ x ⟩
      fwd h = let (a∈ , b∈) = inter-char a b x .fst h
                  (p , q₁) = ch₁ x .fst a∈
                  (_ , q₂) = ch₂ x .fst b∈
              in (p , q₁ , q₂)
      bwd : ⟨ x ∈ₛ u ⟩ × ⟨ Q₁ x ⊓ₚ Q₂ x ⟩ → ⟨ x ∈ₛ eval (interC a b) ⟩
      bwd (p , q₁ , q₂) = inter-char a b x .snd ((ch₁ x .snd (p , q₁)) , (ch₂ x .snd (p , q₂)))
  
    neg-ch : (u : V ℓ) (a : Comp) (Q : V ℓ → hProp ℓ)
           → ((x : V ℓ) → ⟨ (x ∈ₛ eval a) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Q x) ⟩)
         → (x : V ℓ) → ⟨ (x ∈ₛ eval (diffC (conC u) a)) ⇔ₚ ((x ∈ₛ u) ⊓ₚ ¬ₚ (Q x)) ⟩
    neg-ch u a Q ch x = fwd , bwd
      where
      fwd : ⟨ x ∈ₛ eval (diffC (conC u) a) ⟩ → ⟨ x ∈ₛ u ⟩ × ⟨ ¬ₚ (Q x) ⟩
      fwd h = let (p , n) = neg-char u a x .fst h in (p , λ q → n (ch x .snd (p , q)))
      bwd : ⟨ x ∈ₛ u ⟩ × ⟨ ¬ₚ (Q x) ⟩ → ⟨ x ∈ₛ eval (diffC (conC u) a) ⟩
      bwd (p , nq) = neg-char u a x .snd (p , λ h → nq (ch x .fst h .snd))
  
    and-ch1 : (u : V ℓ) (f g : Comp1) (Q₁ Q₂ : V ℓ → V ℓ → hProp ℓ)
            → ((y : V ℓ) → ⟨ y ∈ₛ u ⟩ → (x : V ℓ) → ⟨ (x ∈ₛ eval1 f y) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Q₁ y x) ⟩)
            → ((y : V ℓ) → ⟨ y ∈ₛ u ⟩ → (x : V ℓ) → ⟨ (x ∈ₛ eval1 g y) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Q₂ y x) ⟩)
            → (y : V ℓ) → ⟨ y ∈ₛ u ⟩ → (x : V ℓ)
            → ⟨ (x ∈ₛ eval1 (interF f g) y) ⇔ₚ ((x ∈ₛ u) ⊓ₚ (Q₁ y x ⊓ₚ Q₂ y x)) ⟩
    and-ch1 u f g Q₁ Q₂ ch₁ ch₂ y hy x = fwd , bwd
      where
      fwd : ⟨ x ∈ₛ eval1 (interF f g) y ⟩ → ⟨ x ∈ₛ u ⟩ × ⟨ Q₁ y x ⊓ₚ Q₂ y x ⟩
      fwd h = let (a∈ , b∈) = inter-char1 f g y x .fst h
                  (p , q₁) = ch₁ y hy x .fst a∈
                  (_ , q₂) = ch₂ y hy x .fst b∈
              in (p , q₁ , q₂)
      bwd : ⟨ x ∈ₛ u ⟩ × ⟨ Q₁ y x ⊓ₚ Q₂ y x ⟩ → ⟨ x ∈ₛ eval1 (interF f g) y ⟩
      bwd (p , q₁ , q₂) = inter-char1 f g y x .snd ((ch₁ y hy x .snd (p , q₁)) , (ch₂ y hy x .snd (p , q₂)))
  
    neg-ch1 : (u : V ℓ) (f : Comp1) (Q : V ℓ → V ℓ → hProp ℓ)
            → ((y : V ℓ) → ⟨ y ∈ₛ u ⟩ → (x : V ℓ) → ⟨ (x ∈ₛ eval1 f y) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Q y x) ⟩)
            → (y : V ℓ) → ⟨ y ∈ₛ u ⟩ → (x : V ℓ)
          → ⟨ (x ∈ₛ eval1 (diffF (conF u) f) y) ⇔ₚ ((x ∈ₛ u) ⊓ₚ ¬ₚ (Q y x)) ⟩
    neg-ch1 u f Q ch y hy x = fwd , bwd
      where
      fwd : ⟨ x ∈ₛ eval1 (diffF (conF u) f) y ⟩ → ⟨ x ∈ₛ u ⟩ × ⟨ ¬ₚ (Q y x) ⟩
      fwd h = let (p , n) = neg-char1 u f y x .fst h in (p , λ q → n (ch y hy x .snd (p , q)))
      bwd : ⟨ x ∈ₛ u ⟩ × ⟨ ¬ₚ (Q y x) ⟩ → ⟨ x ∈ₛ eval1 (diffF (conF u) f) y ⟩
      bwd (p , nq) = neg-char1 u f y x .snd (p , λ h → nq (ch y hy x .fst h .snd))
  
    -- the bounded-∃ clause: {x ∈ u | ∃ z ∈ ρⱼ. ψ} = ⋃ (imgOp fψ (ρⱼ)),
    -- where fψ is the family z ↦ u ∩ {x | ψ(x, z)}; transitivity supplies
    -- z ∈ u from z ∈ ρⱼ ∈ u, exactly where the paper proof uses it.
  
    bex-mem : {n : ℕ} (ψ : FmQ (suc (suc n))) (u : V ℓ) (tu : Trans u)
            → (ρ : Fin n → V ℓ) → ((k : Fin n) → ⟨ ρ k ∈ₛ u ⟩)
          → (fψ : Comp1)
          → ((z : V ℓ) → ⟨ z ∈ₛ u ⟩ → (x : V ℓ)
             → ⟨ (x ∈ₛ eval1 fψ z) ⇔ₚ ((x ∈ₛ u) ⊓ₚ SatQ ψ (env₂ ρ z x)) ⟩)
          → (j : Fin n) (x : V ℓ)
          → ⟨ (x ∈ₛ eval (unionC (imgC fψ (conC (ρ j)))))
              ⇔ₚ ((x ∈ₛ u) ⊓ₚ Sat (bex j ψ) (env₁ ρ x)) ⟩
    bex-mem ψ u tu ρ hρ fψ feq j x = fwd , bwd
      where
      b = ρ j
      b∈u = hρ j
      prop : isProp (⟨ x ∈ₛ u ⟩ × ⟨ Sat (bex j ψ) (env₁ ρ x) ⟩)
      prop = isProp× (snd (x ∈ₛ u)) (isProp⟨⟩ (Sat (bex j ψ) (env₁ ρ x)))
      fwd : ⟨ x ∈ₛ unionOp (imgOp fψ b) ⟩ → ⟨ x ∈ₛ u ⟩ × ⟨ Sat (bex j ψ) (env₁ ρ x) ⟩
      fwd hx = PT.rec prop go (unionSpec (imgOp fψ b) x .fst hx)
        where
        go : Σ[ w ∈ V ℓ ] (⟨ w ∈ₛ imgOp fψ b ⟩ × ⟨ x ∈ₛ w ⟩)
           → ⟨ x ∈ₛ u ⟩ × ⟨ Sat (bex j ψ) (env₁ ρ x) ⟩
        go (w , w∈ , x∈w) = PT.rec prop go₂ (imgSpec fψ b w .fst w∈)
          where
          go₂ : Σ[ z ∈ V ℓ ] (⟨ z ∈ₛ b ⟩ × (w ≡ eval1 fψ z))
              → ⟨ x ∈ₛ u ⟩ × ⟨ Sat (bex j ψ) (env₁ ρ x) ⟩
          go₂ (z , z∈b , wz) = (x∈u , ∣ i , sat₁ ∣₁)
            where
            z∈u = tu z b z∈b b∈u
            x∈fz = subst (λ w' → ⟨ x ∈ₛ w' ⟩) wz x∈w
            i = z∈b .fst
            p : ⟪ b ⟫↪ i ≡ z
            p = identityPrinciple .fst (z∈b .snd)
            x∈u = feq z z∈u x .fst x∈fz .fst
            sat = feq z z∈u x .fst x∈fz .snd
            sat₁ : ⟨ SatQ ψ (insert (⟪ b ⟫↪ i) (env₁ ρ x)) ⟩
            sat₁ = subst (λ w → ⟨ SatQ ψ (insert w (env₁ ρ x)) ⟩) (sym p) sat
      bwd : ⟨ x ∈ₛ u ⟩ × ⟨ Sat (bex j ψ) (env₁ ρ x) ⟩ → ⟨ x ∈ₛ unionOp (imgOp fψ b) ⟩
      bwd (x∈u , sat) = PT.rec (snd (x ∈ₛ unionOp (imgOp fψ b))) go sat
        where
        go : Σ[ i ∈ ⟪ b ⟫ ] ⟨ SatQ ψ (insert (⟪ b ⟫↪ i) (env₁ ρ x)) ⟩
           → ⟨ x ∈ₛ unionOp (imgOp fψ b) ⟩
        go (i , sat) = unionSpec (imgOp fψ b) x .snd ∣ eval1 fψ z , x∈img , x∈fz ∣₁
          where
          z = ⟪ b ⟫↪ i
          z∈b = ∈ₛ⟪ b ⟫↪ i
          z∈u = tu z b z∈b b∈u
          x∈fz = feq z z∈u x .snd (x∈u , sat)
          x∈img = imgSpec fψ b (eval1 fψ z) .snd ∣ z , z∈b , refl ∣₁
  
    -- realization, quantifier-free, closed composites (Comp) ------------
  
    realizeQ : {n : ℕ} (φ : FmQ (suc n)) → (u : V ℓ) → Trans u → (ρ : Fin n → V ℓ)
           → ((k : Fin n) → ⟨ ρ k ∈ₛ u ⟩)
           → Σ[ t ∈ Comp ] ((x : V ℓ)
              → ⟨ (x ∈ₛ eval t) ⇔ₚ ((x ∈ₛ u) ⊓ₚ SatQ φ (env₁ ρ x)) ⟩)
    realizeQ (memq zero zero) u tu ρ hρ =
      diffC (conC u) (conC u) , λ x → sepDiag-spec u x
    realizeQ (memq zero (suc k)) u tu ρ hρ =
      interC (conC u) (conC (ρ k)) , λ x → interSpec u (ρ k) x
    realizeQ (memq (suc k) zero) u tu ρ hρ =
      colC (conC (ρ k)) (conC u) , λ x → colSpec (ρ k) u x
    realizeQ (memq (suc k) (suc l)) u tu ρ hρ =
      chSepC (conC (ρ k)) (conC (ρ l)) (conC u) , λ x → chSepSpec (ρ k) (ρ l) u x
    realizeQ (φ ∧q ψ) u tu ρ hρ =
      let (t₁ , ch₁) = realizeQ φ u tu ρ hρ
          (t₂ , ch₂) = realizeQ ψ u tu ρ hρ
      in interC t₁ t₂ , λ x → and-ch u t₁ t₂ (λ x' → SatQ φ (env₁ ρ x')) (λ x' → SatQ ψ (env₁ ρ x')) ch₁ ch₂ x
    realizeQ (¬q φ) u tu ρ hρ =
      let (t₁ , ch₁) = realizeQ φ u tu ρ hρ
      in diffC (conC u) t₁ , λ x → neg-ch u t₁ (λ x' → SatQ φ (env₁ ρ x')) ch₁ x
  
    -- realization, quantifier-free, as a family in y (Comp1) ------------
  
    realizeFam : {n : ℕ} (ψ : FmQ (suc (suc n))) → (u : V ℓ) → Trans u → (ρ : Fin n → V ℓ)
             → ((k : Fin n) → ⟨ ρ k ∈ₛ u ⟩)
             → Σ[ f ∈ Comp1 ] ((y : V ℓ) → ⟨ y ∈ₛ u ⟩ → (x : V ℓ)
                → ⟨ (x ∈ₛ eval1 f y) ⇔ₚ ((x ∈ₛ u) ⊓ₚ SatQ ψ (env₂ ρ y x)) ⟩)
    realizeFam (memq zero zero) u tu ρ hρ =
      diffF (conF u) (conF u) , λ y hy x → sepDiag-spec u x
    realizeFam (memq zero (suc zero)) u tu ρ hρ =
      interF (conF u) varF , λ y hy x → interSpec u y x
    realizeFam (memq zero (suc (suc k))) u tu ρ hρ =
      interF (conF u) (conF (ρ k)) , λ y hy x → interSpec u (ρ k) x
    realizeFam (memq (suc zero) zero) u tu ρ hρ =
      colF varF (conF u) , λ y hy x → colSpec y u x
    realizeFam (memq (suc zero) (suc zero)) u tu ρ hρ =
      chSepF varF varF (conF u) , λ y hy x → chSepSpec y y u x
    realizeFam (memq (suc zero) (suc (suc k))) u tu ρ hρ =
      chSepF varF (conF (ρ k)) (conF u) , λ y hy x → chSepSpec y (ρ k) u x
    realizeFam (memq (suc (suc k)) zero) u tu ρ hρ =
      colF (conF (ρ k)) (conF u) , λ y hy x → colSpec (ρ k) u x
    realizeFam (memq (suc (suc k)) (suc zero)) u tu ρ hρ =
      chSepF (conF (ρ k)) varF (conF u) , λ y hy x → chSepSpec (ρ k) y u x
    realizeFam (memq (suc (suc k)) (suc (suc l))) u tu ρ hρ =
      chSepF (conF (ρ k)) (conF (ρ l)) (conF u) , λ y hy x → chSepSpec (ρ k) (ρ l) u x
    realizeFam (φ ∧q ψ) u tu ρ hρ =
      let (f₁ , ch₁) = realizeFam φ u tu ρ hρ
          (f₂ , ch₂) = realizeFam ψ u tu ρ hρ
      in interF f₁ f₂ , λ y hy x → and-ch1 u f₁ f₂ (λ y' x' → SatQ φ (env₂ ρ y' x')) (λ y' x' → SatQ ψ (env₂ ρ y' x')) ch₁ ch₂ y hy x
    realizeFam (¬q φ) u tu ρ hρ =
      let (f₁ , ch₁) = realizeFam φ u tu ρ hρ
        in diffF (conF u) f₁ , λ y hy x → neg-ch1 u f₁ (λ y' x' → SatQ φ (env₂ ρ y' x')) ch₁ y hy x
  
    -- realization, full miniature fragment (Comp) ------------------------
  
    realizeCh : {n : ℕ} (φ : Fm (suc n)) → (u : V ℓ) → Trans u → (ρ : Fin n → V ℓ)
            → ((k : Fin n) → ⟨ ρ k ∈ₛ u ⟩)
            → Σ[ t ∈ Comp ] ((x : V ℓ)
               → ⟨ (x ∈ₛ eval t) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Sat φ (env₁ ρ x)) ⟩)
    realizeCh (emb φ) u tu ρ hρ = realizeQ φ u tu ρ hρ
    realizeCh (φ ∧₀ ψ) u tu ρ hρ =
      let (t₁ , ch₁) = realizeCh φ u tu ρ hρ
          (t₂ , ch₂) = realizeCh ψ u tu ρ hρ
      in interC t₁ t₂ , λ x → and-ch u t₁ t₂ (λ x' → Sat φ (env₁ ρ x')) (λ x' → Sat ψ (env₁ ρ x')) ch₁ ch₂ x
    realizeCh (¬₀ φ) u tu ρ hρ =
      let (t₁ , ch₁) = realizeCh φ u tu ρ hρ
      in diffC (conC u) t₁ , λ x → neg-ch u t₁ (λ x' → Sat φ (env₁ ρ x')) ch₁ x
    realizeCh (bex j ψ) u tu ρ hρ =
      let (fψ , feq) = realizeFam ψ u tu ρ hρ
      in unionC (imgC fψ (conC (ρ j))) , λ x → bex-mem ψ u tu ρ hρ fψ feq j x
  
    -- the statement: eval t extensionally equals the definable subset -----
  
    ext≡ : {n : ℕ} (u : V ℓ) (φ : Fm (suc n)) (ρ : Fin n → V ℓ) (t : Comp)
       → ((x : V ℓ) → ⟨ (x ∈ₛ eval t) ⇔ₚ ((x ∈ₛ u) ⊓ₚ Sat φ (env₁ ρ x)) ⟩)
       → eval t ≡ SepSet u φ ρ
    ext≡ u φ ρ t ch = extensionality (eval t) (SepSet u φ ρ) (sub₁ , sub₂)
      where
      sub₁ : ⟨ eval t ⊆ SepSet u φ ρ ⟩
      sub₁ x x∈t = sep-mem u φ ρ x .snd (ch x .fst x∈t)
      sub₂ : ⟨ SepSet u φ ρ ⊆ eval t ⟩
      sub₂ x x∈s = ch x .snd (sep-mem u φ ρ x .fst x∈s)
  
    realize : {n : ℕ} (φ : Fm (suc n)) → (u : V ℓ) → Trans u → (ρ : Fin n → V ℓ)
            → ((k : Fin n) → ⟨ ρ k ∈ₛ u ⟩)
            → Σ[ t ∈ Comp ] (eval t ≡ SepSet u φ ρ)
    realize φ u tu ρ hρ = let (t , ch) = realizeCh φ u tu ρ hρ in t , ext≡ u φ ρ t ch
