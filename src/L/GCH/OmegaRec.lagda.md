# Internal ω-recursion of a definable step

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.OmegaRec {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj )
open import V.Model {ℓ} using ( pair-spec; union-spec; self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Ordinal {ℓ} using ( #∈ω; ∈#-elim )
open import L.Axioms.Numerals {ℓ}
  using ( pairʟ; pairʟ-fst; unionʟ; unionʟ-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; sucAtL; sucAtL-adequate; prʟ; prʟ-fst; numL )
open import L.GCH.OrderType {ℓ} lem using ( module PairFo )

open import Cubical.Data.Nat.Order
  using ( _≤_; _<_; ≤-refl; ≤-suc; ≤-trans; <-weaken; <-split
        ; pred-≤-pred; suc-≤-suc; ¬-<-zero )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV; #_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S; _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- Renaming, read at the same satisfaction as `_⊨_` (as OrderType does).
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id

isSetS : isSet S
isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))

S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
S≡ = Σ≡Prop (λ v → snd (isL v))

-- "The pair (x, y) is a member of F", the shape every clause below reads.
Holds : S → S → S → Type (ℓ-suc ℓ)
Holds F x y = ⟨ pr (fst x) (fst y) ∈ fst F ⟩

-- The numeral k as an element of L.
nn : ℕ → S
nn k = # k , numL k

-- =====================================================================
-- MEMBERSHIP IN THE MODEL'S PAIR AND UNION, read through the projection
-- equations of src/L/Axioms/Numerals.lagda.md and the hierarchy's specs.
-- =====================================================================

pairʟ-in : (a b y : S) → (fst y ≡ fst a) ⊎ (fst y ≡ fst b) → ⟨ y ∈ˢ pairʟ a b ⟩
pairʟ-in a b y k = subst (λ w → ⟨ fst y ∈ w ⟩) (sym (pairʟ-fst a b))
  (subst ⟨_⟩ (sym (pair-spec (fst a) (fst b) (fst y))) ∣ k ∣₁)

pairʟ-out : (a b y : S) → ⟨ y ∈ˢ pairʟ a b ⟩ → ∥ (fst y ≡ fst a) ⊎ (fst y ≡ fst b) ∥₁
pairʟ-out a b y h = subst ⟨_⟩ (pair-spec (fst a) (fst b) (fst y))
  (subst (λ w → ⟨ fst y ∈ w ⟩) (pairʟ-fst a b) h)

unionʟ-in : (A y B : S) → ⟨ fst B ∈ fst A ⟩ → ⟨ fst y ∈ fst B ⟩ → ⟨ y ∈ˢ unionʟ A ⟩
unionʟ-in A y B hB hy = subst (λ w → ⟨ fst y ∈ w ⟩) (sym (unionʟ-fst A))
  (subst ⟨_⟩ (sym (union-spec (fst A) (fst y))) ∣ fst B , (hB , hy) ∣₁)

unionʟ-out : (A y : S) → ⟨ y ∈ˢ unionʟ A ⟩
           → ∥ Σ[ B ∈ V ℓ ] (⟨ B ∈ fst A ⟩ × ⟨ fst y ∈ B ⟩) ∥₁
unionʟ-out A y h = subst ⟨_⟩ (union-spec (fst A) (fst y))
  (subst (λ w → ⟨ fst y ∈ w ⟩) (unionʟ-fst A) h)

-- =====================================================================
-- THE RECURSION.  `a` is the start, `stepFo` defines `step` on the whole
-- model (the two directions of src/L/Recursion.lagda.md's `Definition`,
-- with no domain clause), and `it` is the iteration, in the host.
-- =====================================================================

module Iterate (a : S) (stepFo : Formula S 2) (step : S → S)
               (defines : (x : S) → ⟨ (step x ∷ x ∷ []) ⊨ stepFo ⟩)
               (only : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ stepFo ⟩ → y ≡ step x) where

  it : ℕ → S
  it zero    = a
  it (suc n) = step (it n)

  it-suc : (n : ℕ) → it (suc n) ≡ step (it n)
  it-suc n = refl

  -- ===================================================================
  -- SECTION 1.  THE APPROXIMATION FORMULA, AND HOW TO READ IT.
  --
  --   A set F of pairs is CORRECT when its entries at 0 are a, any two
  --   entries at successive indices are related by the step, and every
  --   entry at x' has an entry at each member of x'.  No domain clause
  --   and no single-valuedness: section 2 shows every entry at a numeral
  --   is the iterate there, and section 3 builds one correct set per n.
  -- ===================================================================

  Zero : S → Type (ℓ-suc ℓ)
  Zero F = (v : S) → Holds F (nn 0) v → fst v ≡ fst a

  Step : S → Type (ℓ-suc ℓ)
  Step F = (x v x' v' : S) → Holds F x v → Holds F x' v'
         → fst x' ≡ sucV (fst x) → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩

  Down : S → Type (ℓ-suc ℓ)
  Down F = (x' v' x : S) → Holds F x' v' → ⟨ fst x ∈ fst x' ⟩
         → ∥ Σ[ v ∈ S ] Holds F x v ∥₁

  Correct : S → Type (ℓ-suc ℓ)
  Correct F = Zero F × (Step F × Down F)

  -- "Every entry of f at 0 is a."  Inside: z is 0; then v is 0, z is 1.
  opaque
    zeroAt : ∀ {n} → Fin n → Formula S n
    zeroAt f = ∀̇ ( (var zero ≐ con (nn 0))
                 ⇒̇ ∀̇ ( appAt (suc (suc f)) (suc zero) zero ⇒̇ (var zero ≐ con a) ) )

    zero-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ zeroAt f ⟩ → Zero (lookup f γ)
    zero-out f γ h v hv = h (nn 0) refl v
      (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ nn 0 ∷ γ))) hv)

    zero-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Zero (lookup f γ) → ⟨ γ ⊨ zeroAt f ⟩
    zero-in f γ h z ez v hv = h v
      (subst (λ t → ⟨ pr t (fst v) ∈ fst (lookup f γ) ⟩) ez
        (subst ⟨_⟩ (appAt-adequate (suc (suc f)) (suc zero) zero (v ∷ z ∷ γ)) hv))

  -- "Entries at x and at x' = suc x are related by the step."  Inside:
  -- x is 3, v is 2, x' is 1, v' is 0; the step formula reads (v' ∷ v ∷ []).
  private
    ρ : ∀ {n} → Fin 2 → Fin (suc (suc (suc (suc n))))
    ρ zero       = zero
    ρ (suc zero) = suc (suc zero)

    ag : ∀ {n} (γ : S ^ n) (x v x' v' : S)
       → Ren.Agrees ρ (v' ∷ x' ∷ v ∷ x ∷ γ) (v' ∷ v ∷ [])
    ag γ x v x' v' zero       = refl
    ag γ x v x' v' (suc zero) = refl

  opaque
    stepAt : ∀ {n} → Fin n → Formula S n
    stepAt f = ∀̇ (∀̇ (∀̇ (∀̇ (
        appAt (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero))
      ⇒̇ ( appAt (suc (suc (suc (suc f)))) (suc zero) zero
      ⇒̇ ( sucAtL (suc (suc (suc zero))) (suc zero)
      ⇒̇ renameFo ρ stepFo ) ) ))))

    private
      gr : ∀ {n} (γ : S ^ n) (x v x' v' : S)
         → ⟨ (v' ∷ x' ∷ v ∷ x ∷ γ) ⊨ renameFo ρ stepFo ⟩ ≡ ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
      gr γ x v x' v' = cong ⟨_⟩
        (Ren.⊨-rename ρ stepFo (v' ∷ x' ∷ v ∷ x ∷ γ) (v' ∷ v ∷ []) (ag γ x v x' v'))

    step-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ stepAt f ⟩ → Step (lookup f γ)
    step-out f γ h x v x' v' p q s = transport (gr γ x v x' v')
      (h x v x' v'
        (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero)) (v' ∷ x' ∷ v ∷ x ∷ γ))) p)
        (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v' ∷ x' ∷ v ∷ x ∷ γ))) q)
        (subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc (suc zero))) (suc zero) (v' ∷ x' ∷ v ∷ x ∷ γ))) s))

    step-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Step (lookup f γ) → ⟨ γ ⊨ stepAt f ⟩
    step-in f γ h x v x' v' p q s = transport (sym (gr γ x v x' v'))
      (h x v x' v'
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc (suc (suc zero))) (suc (suc zero)) (v' ∷ x' ∷ v ∷ x ∷ γ)) p)
        (subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v' ∷ x' ∷ v ∷ x ∷ γ)) q)
        (subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc zero))) (suc zero) (v' ∷ x' ∷ v ∷ x ∷ γ)) s))

  -- "Every entry at x' has an entry at each member x of x'."  Inside:
  -- x' is 2, v' is 1, x is 0; then v is 0, x is 1, x' is 3.
  opaque
    downAt : ∀ {n} → Fin n → Formula S n
    downAt f = ∀̇ (∀̇ (∀̇ (
        appAt (suc (suc (suc f))) (suc (suc zero)) (suc zero)
      ⇒̇ ( (var zero ∈̇ var (suc (suc zero)))
      ⇒̇ ∃̇ (appAt (suc (suc (suc (suc f)))) (suc zero) zero) ) )))

    down-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ downAt f ⟩ → Down (lookup f γ)
    down-out f γ h x' v' x p m = PT.map
      (λ { (v , q) → v , subst ⟨_⟩ (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v ∷ x ∷ v' ∷ x' ∷ γ)) q })
      (h x' v' x (subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero) (x ∷ v' ∷ x' ∷ γ))) p) m)

    down-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Down (lookup f γ) → ⟨ γ ⊨ downAt f ⟩
    down-in f γ h x' v' x p m = PT.map
      (λ { (v , q) → v , subst ⟨_⟩ (sym (appAt-adequate (suc (suc (suc (suc f)))) (suc zero) zero (v ∷ x ∷ v' ∷ x' ∷ γ))) q })
      (h x' v' x (subst ⟨_⟩ (appAt-adequate (suc (suc (suc f))) (suc (suc zero)) (suc zero) (x ∷ v' ∷ x' ∷ γ)) p) m)

  opaque
    corrAt : ∀ {n} → Fin n → Formula S n
    corrAt f = zeroAt f ∧̇ (stepAt f ∧̇ downAt f)

    corr-out : ∀ {n} (f : Fin n) (γ : S ^ n) → ⟨ γ ⊨ corrAt f ⟩ → Correct (lookup f γ)
    corr-out f γ (z , (s , d)) = zero-out f γ z , (step-out f γ s , down-out f γ d)

    corr-in : ∀ {n} (f : Fin n) (γ : S ^ n) → Correct (lookup f γ) → ⟨ γ ⊨ corrAt f ⟩
    corr-in f γ (z , (s , d)) = zero-in f γ z , (step-in f γ s , down-in f γ d)

  -- THE GRAPH FORMULA, over (y ∷ q ∷ []): "y is recorded at q by some
  -- correct set".  Inside: F is 0, y is 1, q is 2.
  opaque
    itFo : Formula S 2
    itFo = ∃̇ ( corrAt zero ∧̇ appAt zero (suc (suc zero)) (suc zero) )

    itFo-out : (y q : S) → ⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
             → ∥ Σ[ F ∈ S ] (Correct F × Holds F q y) ∥₁
    itFo-out y q = PT.map (λ { (F , (hc , ha)) → F
      , ( corr-out zero (F ∷ y ∷ q ∷ []) hc
        , subst ⟨_⟩ (appAt-adequate zero (suc (suc zero)) (suc zero) (F ∷ y ∷ q ∷ [])) ha ) })

    itFo-in : (y q F : S) → Correct F → Holds F q y → ⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
    itFo-in y q F hc hq = ∣ F
      , ( corr-in zero (F ∷ y ∷ q ∷ []) hc
        , subst ⟨_⟩ (sym (appAt-adequate zero (suc (suc zero)) (suc zero) (F ∷ y ∷ q ∷ []))) hq ) ∣₁

  -- Transport of the graph formula along an equation of the index.
  itFo-at : (v : S) {x y : S} → x ≡ y
          → ⟨ (v ∷ x ∷ []) ⊨ itFo ⟩ → ⟨ (v ∷ y ∷ []) ⊨ itFo ⟩
  itFo-at v e = subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ itFo ⟩) e

  -- ===================================================================
  -- SECTION 2.  UNIQUENESS: a correct set records the iterate at every
  -- numeral.  One induction on the numeral.
  -- ===================================================================

  corr-val : (F : S) → Correct F → (k : ℕ) (v : S)
           → Holds F (nn k) v → fst v ≡ fst (it k)
  corr-val F (z , (s , d)) zero    v h = z v h
  corr-val F (z , (s , d)) (suc k) v h =
    PT.rec (setIsSet (fst v) (fst (it (suc k)))) read
      (d (nn (suc k)) v (nn k) h (self∈sucV (# k)))
    where
    read : Σ[ u ∈ S ] Holds F (nn k) u → fst v ≡ fst (it (suc k))
    read (u , hu) = cong fst (only (it k) v
      (subst (λ t → ⟨ (v ∷ t ∷ []) ⊨ stepFo ⟩)
        (S≡ (corr-val F (z , (s , d)) k u hu))
        (s (nn k) u (nn (suc k)) v hu h refl)))

  itFo-val : (k : ℕ) (v : S) → ⟨ (v ∷ nn k ∷ []) ⊨ itFo ⟩ → fst v ≡ fst (it k)
  itFo-val k v h = PT.rec (setIsSet (fst v) (fst (it k)))
    (λ { (F , (hc , hv)) → corr-val F hc k v hv }) (itFo-out v (nn k) h)

  -- ===================================================================
  -- SECTION 3.  EXISTENCE: the finite table { (k, it k) : k ≤ n }, built
  -- by one pair and one union per step, is correct.
  -- ===================================================================

  private
    e : ℕ → S
    e k = prʟ (nn k) (it k)

  Fn : ℕ → S
  Fn zero    = pairʟ (e 0) (e 0)
  Fn (suc n) = unionʟ (pairʟ (Fn n) (pairʟ (e (suc n)) (e (suc n))))

  private
    Fn-in′ : (n k : ℕ) → k ≤ n → ⟨ e k ∈ˢ Fn n ⟩
    Fn-in′ zero    zero    _ = pairʟ-in (e 0) (e 0) (e 0) (inl refl)
    Fn-in′ zero    (suc k) p = Empty.rec (¬-<-zero p)
    Fn-in′ (suc n) k       p = go (<-split (suc-≤-suc p))
      where
      P = pairʟ (Fn n) (pairʟ (e (suc n)) (e (suc n)))
      go : (k < suc n) ⊎ (k ≡ suc n) → ⟨ e k ∈ˢ Fn (suc n) ⟩
      go (inl q) = unionʟ-in P (e k) (Fn n)
        (pairʟ-in (Fn n) (pairʟ (e (suc n)) (e (suc n))) (Fn n) (inl refl))
        (Fn-in′ n k (pred-≤-pred q))
      go (inr q) = unionʟ-in P (e k) (pairʟ (e (suc n)) (e (suc n)))
        (pairʟ-in (Fn n) (pairʟ (e (suc n)) (e (suc n))) (pairʟ (e (suc n)) (e (suc n))) (inr refl))
        (pairʟ-in (e (suc n)) (e (suc n)) (e k) (inl (cong (λ j → fst (e j)) q)))

    Fn-out′ : (n : ℕ) (y : S) → ⟨ y ∈ˢ Fn n ⟩
            → ∥ Σ[ k ∈ ℕ ] ((k ≤ n) × (fst y ≡ fst (e k))) ∥₁
    Fn-out′ zero y h = PT.map (λ { (inl q) → 0 , (≤-refl , q) ; (inr q) → 0 , (≤-refl , q) })
      (pairʟ-out (e 0) (e 0) y h)
    Fn-out′ (suc n) y h = PT.rec squash₁ outer (unionʟ-out P y h)
      where
      P = pairʟ (Fn n) (pairʟ (e (suc n)) (e (suc n)))
      outer : Σ[ B ∈ V ℓ ] (⟨ B ∈ fst P ⟩ × ⟨ fst y ∈ B ⟩)
            → ∥ Σ[ k ∈ ℕ ] ((k ≤ suc n) × (fst y ≡ fst (e k))) ∥₁
      outer (B , (hB , hy)) = PT.rec squash₁ inner
        (pairʟ-out (Fn n) (pairʟ (e (suc n)) (e (suc n)))
          (B , isL-trans {x = fst P} {y = B} hB (snd P)) hB)
        where
        inner : (B ≡ fst (Fn n)) ⊎ (B ≡ fst (pairʟ (e (suc n)) (e (suc n))))
              → ∥ Σ[ k ∈ ℕ ] ((k ≤ suc n) × (fst y ≡ fst (e k))) ∥₁
        inner (inl q) = PT.map (λ { (k , (p , r)) → k , (≤-suc p , r) })
          (Fn-out′ n y (subst (λ w → ⟨ fst y ∈ w ⟩) q hy))
        inner (inr q) = PT.map (λ { (inl r) → suc n , (≤-refl , r) ; (inr r) → suc n , (≤-refl , r) })
          (pairʟ-out (e (suc n)) (e (suc n)) y (subst (λ w → ⟨ fst y ∈ w ⟩) q hy))

  Fn-in : (n k : ℕ) → k ≤ n → Holds (Fn n) (nn k) (it k)
  Fn-in n k p = subst (λ w → ⟨ w ∈ fst (Fn n) ⟩) (prʟ-fst (nn k) (it k)) (Fn-in′ n k p)

  Fn-out : (n : ℕ) (y : S) → ⟨ y ∈ˢ Fn n ⟩
         → ∥ Σ[ k ∈ ℕ ] ((k ≤ n) × (fst y ≡ pr (# k) (fst (it k)))) ∥₁
  Fn-out n y h = PT.map (λ { (k , (p , q)) → k , (p , q ∙ prʟ-fst (nn k) (it k)) }) (Fn-out′ n y h)

  -- A pair in the table, read as an index and a value.
  Fn-pair : (n : ℕ) (x v : S) → Holds (Fn n) x v
          → ∥ Σ[ k ∈ ℕ ] ((k ≤ n) × ((fst x ≡ # k) × (fst v ≡ fst (it k)))) ∥₁
  Fn-pair n x v h = PT.map (λ { (k , (p , q)) → k , (p , pr-inj (sym (prʟ-fst x v) ∙ q)) })
    (Fn-out n (prʟ x v) (subst (λ w → ⟨ w ∈ fst (Fn n) ⟩) (sym (prʟ-fst x v)) h))

  Fn-correct : (n : ℕ) → Correct (Fn n)
  Fn-correct n = zeroC , (stepC , downC)
    where
    zeroC : Zero (Fn n)
    zeroC v h = PT.rec (setIsSet (fst v) (fst a))
      (λ { (k , (_ , (ex , ev))) → ev ∙ cong (λ j → fst (it j)) (sym (#-inj 0 k ex)) })
      (Fn-pair n (nn 0) v h)

    stepC : Step (Fn n)
    stepC x v x' v' hxv hx'v' s = PT.rec (snd ((v' ∷ v ∷ []) ⊨ stepFo)) outer (Fn-pair n x v hxv)
      where
      outer : Σ[ k ∈ ℕ ] ((k ≤ n) × ((fst x ≡ # k) × (fst v ≡ fst (it k))))
            → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
      outer (k , (_ , (ex , ev))) = PT.rec (snd ((v' ∷ v ∷ []) ⊨ stepFo)) inner (Fn-pair n x' v' hx'v')
        where
        inner : Σ[ k' ∈ ℕ ] ((k' ≤ n) × ((fst x' ≡ # k') × (fst v' ≡ fst (it k'))))
              → ⟨ (v' ∷ v ∷ []) ⊨ stepFo ⟩
        inner (k' , (_ , (ex' , ev'))) =
          subst2 (λ p q → ⟨ (p ∷ q ∷ []) ⊨ stepFo ⟩)
            (S≡ (sym (ev' ∙ cong (λ j → fst (it j)) k'≡)))
            (S≡ (sym ev))
            (defines (it k))
          where
          k'≡ : k' ≡ suc k
          k'≡ = #-inj k' (suc k) (sym ex' ∙ s ∙ cong sucV ex)

    downC : Down (Fn n)
    downC x' v' x h m = PT.rec squash₁ outer (Fn-pair n x' v' h)
      where
      outer : Σ[ k' ∈ ℕ ] ((k' ≤ n) × ((fst x' ≡ # k') × (fst v' ≡ fst (it k'))))
            → ∥ Σ[ v ∈ S ] Holds (Fn n) x v ∥₁
      outer (k' , (p' , (ex' , _))) = PT.map
        (λ { (j , (j< , ej)) → it j
           , subst (λ t → ⟨ pr t (fst (it j)) ∈ fst (Fn n) ⟩) (sym ej)
               (Fn-in n j (≤-trans (<-weaken j<) p')) })
        (∈#-elim k' (fst x) (subst (λ w → ⟨ fst x ∈ w ⟩) ex' m))

  -- THE GRAPH FORMULA HOLDS OF THE ITERATE, at every numeral.
  it-graph : (k : ℕ) → ⟨ (it k ∷ nn k ∷ []) ⊨ itFo ⟩
  it-graph k = itFo-in (it k) (nn k) (Fn k) (Fn-correct k) (Fn-in k k ≤-refl)

  -- ===================================================================
  -- SECTION 4.  THE TABLES: the values, their union, and the graph, in L.
  -- ===================================================================

  Num : S → Type (ℓ-suc ℓ)
  Num q = Σ[ k ∈ ℕ ] (nn k ≡ q)

  ω-num : (q : S) → ⟨ q ∈ˢ ωʟ ⟩ → ∥ Num q ∥₁
  ω-num q = PT.map (λ { (i , p) → lower i , S≡ p })

  private
    valR : Recursion
    valR = record
      { dom   = ωʟ
      ; graph = itFo
      ; funct = λ q q∈ → mereFunct itFo q (PT.map (wit q) (ω-num q q∈)) }
      where
      wit : (q : S) → Num q
          → Σ[ y ∈ S ] (⟨ (y ∷ q ∷ []) ⊨ itFo ⟩
                       × ((y' : S) → ⟨ (y' ∷ q ∷ []) ⊨ itFo ⟩ → y' ≡ y))
      wit q (k , eq) = it k
        , ( itFo-at (it k) eq (it-graph k)
          , λ y' h → S≡ (itFo-val k y' (itFo-at y' (sym eq) h)) )

    module VR = Of valR

  values : S
  values = VR.table

  values-in : (n : ℕ) → ⟨ fst (it n) ∈ fst values ⟩
  values-in n = VR.table-in (nn n) (it n) (#∈ω n) (it-graph n)

  values-out : (y : S) → ⟨ y ∈ˢ values ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ fst (it n)) ∥₁
  values-out y hy = PT.rec squash₁
    (λ { (q , (q∈ , h)) → PT.map
      (λ { (k , eq) → k , itFo-val k y (itFo-at y (sym eq) h) }) (ω-num q q∈) })
    (VR.table-out y hy)

  iterUnion : S
  iterUnion = unionʟ values

  iterUnion-in : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ z ∈ˢ iterUnion ⟩
  iterUnion-in n z hz = unionʟ-in values z (it n) (values-in n) hz

  iterUnion-out : (z : S) → ⟨ z ∈ˢ iterUnion ⟩ → ∥ Σ[ n ∈ ℕ ] ⟨ fst z ∈ fst (it n) ⟩ ∥₁
  iterUnion-out z h = PT.rec squash₁
    (λ { (B , (hB , hz)) → PT.map
      (λ { (n , eB) → n , subst (λ w → ⟨ fst z ∈ w ⟩) eB hz })
      (values-out (B , isL-trans {x = fst values} {y = B} hB (snd values)) hB) })
    (unionʟ-out values z h)

  -- The graph { (n, it n) : n ∈ ℕ }, through OrderType's pair form.
  module PF = PairFo itFo

  private
    tabR : Recursion
    tabR = record
      { dom   = ωʟ
      ; graph = PF.pairFo
      ; funct = λ q q∈ → mereFunct PF.pairFo q (PT.map (wit q) (ω-num q q∈)) }
      where
      wit : (q : S) → Num q
          → Σ[ p ∈ S ] (⟨ (p ∷ q ∷ []) ⊨ PF.pairFo ⟩
                       × ((p' : S) → ⟨ (p' ∷ q ∷ []) ⊨ PF.pairFo ⟩ → p' ≡ p))
      wit q (k , eq) = prʟ q (it k)
        , ( PF.pair-in (prʟ q (it k)) q (it k) (prʟ-fst q (it k)) (itFo-at (it k) eq (it-graph k))
          , λ p' hp' → PT.rec (isSetS p' (prʟ q (it k)))
              (λ { (v , (ev , hv)) → S≡
                 (ev ∙ cong (pr (fst q)) (itFo-val k v (itFo-at v (sym eq) hv))
                     ∙ sym (prʟ-fst q (it k))) })
              (PF.pair-out p' q hp') )

    module TR = Of tabR

  iter : S
  iter = TR.table

  iter-in : (n : ℕ) → ⟨ pr (# n) (fst (it n)) ∈ fst iter ⟩
  iter-in n = subst (λ w → ⟨ w ∈ fst iter ⟩) (prʟ-fst (nn n) (it n))
    (TR.table-in (nn n) (prʟ (nn n) (it n)) (#∈ω n)
      (PF.pair-in (prʟ (nn n) (it n)) (nn n) (it n) (prʟ-fst (nn n) (it n)) (it-graph n)))

  iter-out : (y : S) → ⟨ y ∈ˢ iter ⟩ → ∥ Σ[ n ∈ ℕ ] (fst y ≡ pr (# n) (fst (it n))) ∥₁
  iter-out y hy = PT.rec squash₁
    (λ { (q , (q∈ , h)) → PT.rec squash₁
      (λ { (v , (ev , hv)) → PT.map
        (λ { (k , eq) → k
           , ev ∙ cong₂ pr (cong fst (sym eq)) (itFo-val k v (itFo-at v (sym eq) hv)) })
        (ω-num q q∈) })
      (PF.pair-out y q h) })
    (TR.table-out y hy)

  -- ===================================================================
  -- SECTION 5.  ONE INSTANCE: a step that only grows.  The union starts
  -- at a, every stage sits below the next, and the step of any set
  -- bounded by a stage lands inside the union.
  -- ===================================================================

  module Closure (grows : (x z : S) → ⟨ fst z ∈ fst x ⟩ → ⟨ fst z ∈ fst (step x) ⟩) where

    it-mono : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ fst z ∈ fst (it (suc n)) ⟩
    it-mono n z = grows (it n) z

    it-up : (n k : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ fst z ∈ fst (it (k + n)) ⟩
    it-up n zero    z h = h
    it-up n (suc k) z h = it-mono (k + n) z (it-up n k z h)

    start : (z : S) → ⟨ fst z ∈ fst a ⟩ → ⟨ z ∈ˢ iterUnion ⟩
    start = iterUnion-in 0

    stage : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (it n) ⟩ → ⟨ z ∈ˢ iterUnion ⟩
    stage = iterUnion-in

    closed-stage : (n : ℕ) (z : S) → ⟨ fst z ∈ fst (step (it n)) ⟩ → ⟨ z ∈ˢ iterUnion ⟩
    closed-stage n = iterUnion-in (suc n)

    module Mono (mono : (x y : S) → ((z : S) → ⟨ fst z ∈ fst x ⟩ → ⟨ fst z ∈ fst y ⟩)
                      → (z : S) → ⟨ fst z ∈ fst (step x) ⟩ → ⟨ fst z ∈ fst (step y) ⟩) where

      closed : (x : S) (n : ℕ) → ((z : S) → ⟨ fst z ∈ fst x ⟩ → ⟨ fst z ∈ fst (it n) ⟩)
             → (z : S) → ⟨ fst z ∈ fst (step x) ⟩ → ⟨ z ∈ˢ iterUnion ⟩
      closed x n sub z hz = iterUnion-in (suc n) z (mono x (it n) sub z hz)
```
