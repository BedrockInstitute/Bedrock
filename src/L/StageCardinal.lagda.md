# The size of a stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
import Cubical.Data.Empty as Empty

module L.StageCardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (sq : (α : V ℓ) → (⟨ α ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫) ]
          ((x y : ⟪ α ⟫ × ⟪ α ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula )
open import FOL.Count {ℓ} using ( composed-count; code; shape-count-inj )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction; regularityV )
open import V.Model {ℓ} using ( ∈sucV-inl )
open import V.Presentation {ℓ} using ( fiber; member; ↪-inj )
open import V.Coding {ℓ} using ( #-inj′ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-inv; Lset-out )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Ordinal {ℓ}
  using ( #∈ω; numeral-ord; numeral-mem; mem-ord; ω-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; Lset-cumul )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; Tri; lt; eq; gt; leastOf )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet using ( ω; #_; sucV )

open import Cubical.Foundations.Prelude using ( J; transportRefl; substRefl; PathP; toPathP )
open import Cubical.Foundations.Transport using ( substSubst⁻ )
open import Cubical.Data.Sigma.Properties using ( ΣPathP )
open import Cubical.Data.Vec using ( Vec )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

```agda
-- The counting bound: the formulas over K with one free variable inject into
-- an infinite ordinal β, given an injection of K into β and the square law
-- (pairing) at β. The numerals inside β come from β ∉ ω by trichotomy. This
-- is Devlin's |ℒ_K| = max(|K|, ω) in the honest injection shape: the
-- successor step of the level-size theorem is exactly this bound at
-- K = ⟪ Lset α ⟫, and the chain's 5.4 consumes the same shape at the hull.
module Bound (β : S) (oβ : IsOrd β) (infβ : ⟨ β ∈ˢ ω ⟩ → Empty.⊥)
             (pairing : Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
                          ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y)) where

  pair : ⟪ β ⟫ → ⟪ β ⟫ → ⟪ β ⟫
  pair x y = fst pairing (x , y)

  pair-inj : (x y x' y' : ⟪ β ⟫) → pair x y ≡ pair x' y' → (x ≡ x') × (y ≡ y')
  pair-inj x y x' y' e = cong fst p , cong snd p
    where
    p : (x , y) ≡ (x' , y')
    p = snd pairing (x , y) (x' , y') e

  -- every numeral is a member of an infinite ordinal, by trichotomy against ω
  numeral∈β : (n : ℕ) → ⟨ (# n) ∈ˢ β ⟩
  numeral∈β n = go (ord-tri (# n) (numeral-ord n) β oβ)
    where
    go : (⟨ (# n) ∈ˢ β ⟩ ⊎ (((# n) ≡ β) ⊎ ⟨ β ∈ˢ (# n) ⟩)) → ⟨ (# n) ∈ˢ β ⟩
    go (inl h) = h
    go (inr (inl q)) =
      Empty.rec (infβ (subst (λ w → ⟨ w ∈ˢ ω ⟩) q (#∈ω n)))
    go (inr (inr h)) = Empty.rec (infβ (numeral-mem n β h))

  numeral : ℕ → ⟪ β ⟫
  numeral n = fiber β {x = # n} (numeral∈β n) .fst

  numeral-inj : (n m : ℕ) → numeral n ≡ numeral m → n ≡ m
  numeral-inj n m e = #-inj′ (sym (fiber β {x = # n} (numeral∈β n) .snd)
    ∙ cong (⟪ β ⟫↪) e ∙ fiber β {x = # m} (numeral∈β m) .snd)

  code-stable : (k k' : ℕ) (p : k' ≡ k) (ψ : Formula (⊥* {ℓ}) k')
              → code (subst (Formula (⊥* {ℓ})) p ψ) ≡ code ψ
  code-stable k k' p ψ =
    J (λ k p → code (subst (Formula (⊥* {ℓ})) p ψ) ≡ code ψ)
      (cong code (transportRefl ψ)) p

  tuple-g : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
          → (k : ℕ) → Vec K k → ⟪ β ⟫
  tuple-g g zero [] = numeral 0
  tuple-g g (suc k) (x ∷ xs) = pair (fst g x) (tuple-g g k xs)

  tuple-g-inj : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
              → (k : ℕ) (xs ys : Vec K k) → tuple-g g k xs ≡ tuple-g g k ys → xs ≡ ys
  tuple-g-inj g zero [] [] _ = refl
  tuple-g-inj g (suc k) (x ∷ xs) (y ∷ ys) e = cong₂ _∷_ xeq (tuple-g-inj g k xs ys xs≡ys)
    where
    p : (fst g x , tuple-g g k xs) ≡ (fst g y , tuple-g g k ys)
    p = snd pairing (fst g x , tuple-g g k xs) (fst g y , tuple-g g k ys) e
    xeq : x ≡ y
    xeq = snd g x y (cong fst p)
    xs≡ys : tuple-g g k xs ≡ tuple-g g k ys
    xs≡ys = cong snd p

  tuple-g-stable : (K : Type ℓ) (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                 → (k k' : ℕ) (p : k' ≡ k) (cs : Vec K k')
                 → tuple-g {K} g k (subst (Vec K) p cs) ≡ tuple-g {K} g k' cs
  tuple-g-stable K g k k' p cs =
    J (λ k p → tuple-g {K} g k (subst (Vec K) p cs) ≡ tuple-g {K} g k' cs)
      (cong (tuple-g {K} g k') (transportRefl cs)) p

  count-bound : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
              → Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k)) → ⟪ β ⟫
  count-bound g (k , (ψ , (n , cs))) =
    pair (numeral k) (pair (pair (numeral (code ψ)) (numeral n)) (tuple-g g k cs))

  count-bound-inj : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                  → (x y : Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) k × (ℕ × Vec K k)))
                  → count-bound g x ≡ count-bound g y → x ≡ y
  count-bound-inj {K} g (k , (ψ , (n , cs))) (k' , (ψ' , (n' , cs'))) e = outer
    where
    P : ⟪ β ⟫
    P = pair (pair (numeral (code ψ)) (numeral n)) (tuple-g g k cs)
    P' : ⟪ β ⟫
    P' = pair (pair (numeral (code ψ')) (numeral n')) (tuple-g g k' cs')
    e-out : (numeral k , P) ≡ (numeral k' , P')
    e-out = snd pairing (numeral k , P) (numeral k' , P') e
    pk : k ≡ k'
    pk = numeral-inj k k' (cong fst e-out)
    e-in : P ≡ P'
    e-in = cong snd e-out
    e-pair : (pair (numeral (code ψ)) (numeral n) , tuple-g g k cs)
           ≡ (pair (numeral (code ψ')) (numeral n') , tuple-g g k' cs')
    e-pair = snd pairing (pair (numeral (code ψ)) (numeral n) , tuple-g g k cs)
                         (pair (numeral (code ψ')) (numeral n') , tuple-g g k' cs') e-in
    e-code : code ψ ≡ code ψ'
    e-code = numeral-inj (code ψ) (code ψ')
      (cong fst (snd pairing (numeral (code ψ) , numeral n) (numeral (code ψ') , numeral n') (cong fst e-pair)))
    e-num : numeral n ≡ numeral n'
    e-num = cong snd (snd pairing (numeral (code ψ) , numeral n) (numeral (code ψ') , numeral n') (cong fst e-pair))
    qn : PathP (λ _ → ℕ) n n'
    qn = numeral-inj n n' e-num
    e-tup : tuple-g g k cs ≡ tuple-g g k' cs'
    e-tup = cong snd e-pair
    ψ₀ : Formula (⊥* {ℓ}) k
    ψ₀ = subst (Formula (⊥* {ℓ})) (sym pk) ψ'
    sψ : ψ ≡ ψ₀
    sψ = snd shape-count-inj {k = k} {φ = ψ} {ψ = ψ₀} (e-code ∙ sym (code-stable k k' (sym pk) ψ'))
    qψ : PathP (λ i → Formula (⊥* {ℓ}) (pk i)) ψ ψ'
    qψ = toPathP (cong (subst (Formula (⊥* {ℓ})) pk) sψ ∙ substSubst⁻ (Formula (⊥* {ℓ})) pk ψ')
    cs₀ : Vec K k
    cs₀ = subst (Vec K) (sym pk) cs'
    scs : cs ≡ cs₀
    scs = tuple-g-inj g k cs cs₀ (e-tup ∙ sym (tuple-g-stable K g k k' (sym pk) cs'))
    qcs : PathP (λ i → Vec K (pk i)) cs cs'
    qcs = toPathP (cong (subst (Vec K) pk) scs ∙ substSubst⁻ (Vec K) pk cs')
    inner₂ : PathP (λ i → ℕ × Vec K (pk i)) (n , cs) (n' , cs')
    inner₂ = ΣPathP {A = λ _ → ℕ} {B = λ i _ → Vec K (pk i)} (qn , qcs)
    inner₁ : PathP (λ i → Formula (⊥* {ℓ}) (pk i) × (ℕ × Vec K (pk i)))
                   (ψ , (n , cs)) (ψ' , (n' , cs'))
    inner₁ = ΣPathP {A = λ i → Formula (⊥* {ℓ}) (pk i)} {B = λ i _ → ℕ × Vec K (pk i)} (qψ , inner₂)
    outer : (k , (ψ , (n , cs))) ≡ (k' , (ψ' , (n' , cs')))
    outer = ΣPathP {A = λ _ → ℕ} {B = λ _ k → Formula (⊥* {ℓ}) k × (ℕ × Vec K k)} (pk , inner₁)

  formula-bound : {K : Type ℓ} (g : Σ[ f ∈ (K → ⟪ β ⟫) ] ((x y : K) → f x ≡ f y → x ≡ y))
                → Σ[ f ∈ (Formula K 1 → ⟪ β ⟫) ] ((φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ)
  formula-bound {K} g = f , inj
    where
    f : Formula K 1 → ⟪ β ⟫
    f φ = count-bound g (fst (composed-count {K}) φ)
    inj : (φ ψ : Formula K 1) → f φ ≡ f ψ → φ ≡ ψ
    inj φ ψ e = snd (composed-count {K}) φ ψ
      (count-bound-inj g (fst (composed-count {K}) φ) (fst (composed-count {K}) ψ) e)
```

```agda
-- The lower half: the ordinals of a stage are exactly the members of its
-- index, so the index injects into the stage.
module Lower (α : S) (oα : IsOrd α) where

  α⊆Lset : (β : S) → ⟨ β ∈ˢ α ⟩ → ⟨ β ∈ˢ Lset α ⟩
  α⊆Lset β β∈α = Lset-cumul β α (mem-ord {A = α} oα β β∈α) oα β∈α
    (ord∈Lset-suc β (mem-ord {A = α} oα β β∈α))

  ord-inj : ⟪ α ⟫ → ⟪ Lset α ⟫
  ord-inj m = fiber (Lset α) {x = ⟪ α ⟫↪ m} (α⊆Lset (⟪ α ⟫↪ m) (member α m)) .fst

  ord-inj-inj : (m n : ⟪ α ⟫) → ord-inj m ≡ ord-inj n → m ≡ n
  ord-inj-inj m n e =
    ↪-inj {a = α}
      (sym (fiber (Lset α) {x = ⟪ α ⟫↪ m} (α⊆Lset (⟪ α ⟫↪ m) (member α m)) .snd)
        ∙ cong (⟪ Lset α ⟫↪) e
        ∙ fiber (Lset α) {x = ⟪ α ⟫↪ n} (α⊆Lset (⟪ α ⟫↪ n) (member α n)) .snd)

-- The lower half of the stage-cardinality statement: for every ordinal α,
-- the index injects into the stage.
stage-card-lower : (α : S) → IsOrd α
                 → Σ[ g ∈ (⟪ α ⟫ → ⟪ Lset α ⟫) ] ((x y : ⟪ α ⟫) → g x ≡ g y → x ≡ y)
stage-card-lower α oα = ord-inj , ord-inj-inj
  where
  module Lw = Lower α oα
  ord-inj : ⟪ α ⟫ → ⟪ Lset α ⟫
  ord-inj = Lw.ord-inj
  ord-inj-inj : (x y : ⟪ α ⟫) → ord-inj x ≡ ord-inj y → x ≡ y
  ord-inj-inj = Lw.ord-inj-inj
```

```agda
_↪_ : Type ℓ → Type ℓ → Type ℓ
X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

-- The ordinal's own strict well-order, re-derived at the descent's consumer
-- site (P-k). A member of an ordinal is an ordinal (mem-ord), so trichotomy
-- comes from the linearity chapter, transitivity from ordinal transitivity,
-- irreflexivity from regularity, and well-foundedness from regularity on V.
module OrdSWO (α : S) (oα : IsOrd α) where

  _≺_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)
  m ≺ n = ⟪ α ⟫↪ m ∈ᵗ ⟪ α ⟫↪ n

  ord-inord : (m : ⟪ α ⟫) → IsOrd (⟪ α ⟫↪ m)
  ord-inord m = mem-ord {A = α} oα (⟪ α ⟫↪ m) (member α m)

  tri₁ : (m n : ⟪ α ⟫) → Tri (m ≺ n) (m ≡ n) (n ≺ m)
  tri₁ m n = go (ord-tri (⟪ α ⟫↪ m) (ord-inord m) (⟪ α ⟫↪ n) (ord-inord n))
    where
    go : (⟨ ⟪ α ⟫↪ m ∈ˢ ⟪ α ⟫↪ n ⟩
          ⊎ ((⟪ α ⟫↪ m ≡ ⟪ α ⟫↪ n) ⊎ ⟨ ⟪ α ⟫↪ n ∈ˢ ⟪ α ⟫↪ m ⟩))
       → Tri (m ≺ n) (m ≡ n) (n ≺ m)
    go (inl h)       = lt h
    go (inr (inl p)) = eq (↪-inj {a = α} p)
    go (inr (inr h)) = gt h

  irr₁ : (m : ⟪ α ⟫) → (m ≺ m → Empty.⊥)
  irr₁ m h = ∈-irrefl (⟪ α ⟫↪ m) h

  trans₁ : (m n k : ⟪ α ⟫) → m ≺ n → n ≺ k → m ≺ k
  trans₁ m n k h h' = ord-inord k .fst h h'

  acc₁ : (m : ⟪ α ⟫) → Acc _∈ᵗ_ (⟪ α ⟫↪ m) → Acc _≺_ m
  acc₁ m (acc r) = acc (λ n n≺m → acc₁ n (r (⟪ α ⟫↪ n) n≺m))

  wf₁ : WellFounded _≺_
  wf₁ m = acc₁ m (regularityV (⟪ α ⟫↪ m))

  ordSWO : SWO ⟪ α ⟫
  ordSWO = record
    { _<∙_   = _≺_
    ; tri∙   = tri₁
    ; irr∙   = irr₁
    ; trans∙ = trans₁
    ; wf∙    = wf₁ }

-- The generic successor step, re-derived from the T85 cure. At every
-- infinite ordinal α, the next stage's index injects into ⟪ α ⟫, given the
-- induction hypothesis at α. Route: Bound.formula-bound at β = α bounds
-- Formula ⟪ Lset α ⟫ 1 by ⟪ α ⟫ (pairing = sq α infα); each member of
-- 𝒟ₒ (Lset α) is merely some defSet φ (𝒟ₒ-inv); leastOf over ordSWO picks
-- the least count value in the class. Injectivity uses count-injectivity
-- and ↪-inj only. The only ordinal hypotheses are IsOrd and infinity: sq
-- is parameterized over every infinite ordinal, so Init's limit clause is
-- never needed here.
module Successor (α : S) (oα : IsOrd α)
                 (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                 (g : ⟪ Lset α ⟫ ↪ ⟪ α ⟫) where

  module B = Bound α oα infα (sq α infα)

  count : Formula ⟪ Lset α ⟫ 1 ↪ ⟪ α ⟫
  count = B.formula-bound {K = ⟪ Lset α ⟫} g

  class-pred : (m : ⟪ 𝒟ₒ (Lset α) ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  class-pred m y = ( ∥ Σ[ φ ∈ Formula ⟪ Lset α ⟫ 1 ]
                        ( ( DefOf.defSet (Lset α) φ ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ m )
                        × ( fst count φ ≡ y ) ) ∥₁
                   , squash₁ )

  nonempty : (m : ⟪ 𝒟ₒ (Lset α) ⟫)
           → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred m y ⟩ ∥₁
  nonempty m = PT.map
    (λ { (φ , e) → fst count φ , ∣ φ , (e , refl) ∣₁ })
    (𝒟ₒ-inv (Lset α) (⟪ 𝒟ₒ (Lset α) ⟫↪ m) (member (𝒟ₒ (Lset α)) m))

  h : ⟪ 𝒟ₒ (Lset α) ⟫ → ⟪ α ⟫
  h m = fst (leastOf (OrdSWO.ordSWO α oα) lem (class-pred m) (nonempty m))

  h-inj : (m n : ⟪ 𝒟ₒ (Lset α) ⟫) → h m ≡ h n → m ≡ n
  h-inj m n e = ↪-inj {a = 𝒟ₒ (Lset α)} (go pm)
    where
    lm = leastOf (OrdSWO.ordSWO α oα) lem (class-pred m) (nonempty m)
    ln = leastOf (OrdSWO.ordSWO α oα) lem (class-pred n) (nonempty n)
    pm : ⟨ class-pred m (fst ln) ⟩
    pm = subst (λ y → ⟨ class-pred m y ⟩) e (fst (snd lm))
    pn : ⟨ class-pred n (fst ln) ⟩
    pn = fst (snd ln)
    go : ⟨ class-pred m (fst ln) ⟩
       → ⟪ 𝒟ₒ (Lset α) ⟫↪ m ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n
    go = PT.rec (isSetS (⟪ 𝒟ₒ (Lset α) ⟫↪ m) (⟪ 𝒟ₒ (Lset α) ⟫↪ n)) go₁
      where
      go₁ : Σ[ φ ∈ Formula ⟪ Lset α ⟫ 1 ]
              ( ( DefOf.defSet (Lset α) φ ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ m )
              × ( fst count φ ≡ fst ln ) )
          → ⟪ 𝒟ₒ (Lset α) ⟫↪ m ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n
      go₁ (φ , (eφ , ec)) =
        PT.rec (isSetS (⟪ 𝒟ₒ (Lset α) ⟫↪ m) (⟪ 𝒟ₒ (Lset α) ⟫↪ n)) go₂ pn
        where
        go₂ : Σ[ ψ ∈ Formula ⟪ Lset α ⟫ 1 ]
                ( ( DefOf.defSet (Lset α) ψ ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n )
                × ( fst count ψ ≡ fst ln ) )
            → ⟪ 𝒟ₒ (Lset α) ⟫↪ m ≡ ⟪ 𝒟ₒ (Lset α) ⟫↪ n
        go₂ (ψ , (eψ , ec')) =
          sym eφ ∙ cong (DefOf.defSet (Lset α)) (snd count φ ψ (ec ∙ sym ec')) ∙ eψ

op-step : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
        → ⟪ Lset α ⟫ ↪ ⟪ α ⟫ → ⟪ 𝒟ₒ (Lset α) ⟫ ↪ ⟪ α ⟫
op-step α oα infα g = Successor.h α oα infα g , Successor.h-inj α oα infα g

successor-step : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
              → ⟪ Lset α ⟫ ↪ ⟪ α ⟫ → ⟪ Lset (sucV α) ⟫ ↪ ⟪ α ⟫
successor-step α oα infα g = subst
  (λ A → Σ[ f ∈ (⟪ A ⟫ → ⟪ α ⟫) ] ((x y : ⟪ A ⟫) → f x ≡ f y → x ≡ y))
  (sym (Lset-suc α)) (op-step α oα infα g)

-- The upper half at a successor ordinal: the next stage's index injects
-- into the successor's own index, by composing the step's injection into
-- ⟪ α ⟫ with the embedding of ⟪ α ⟫ into ⟪ sucV α ⟫ (a member of α is a
-- member of sucV α, ∈sucV-inl).
module SucUpper (α : S) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                (g : ⟪ Lset α ⟫ ↪ ⟪ α ⟫) where

  idx-suc : ⟪ α ⟫ → ⟪ sucV α ⟫
  idx-suc m = fiber (sucV α) {x = ⟪ α ⟫↪ m} (∈sucV-inl (member α m)) .fst

  idx-suc-inj : (m n : ⟪ α ⟫) → idx-suc m ≡ idx-suc n → m ≡ n
  idx-suc-inj m n e = ↪-inj {a = α}
    (sym (fiber (sucV α) {x = ⟪ α ⟫↪ m} (∈sucV-inl (member α m)) .snd)
      ∙ cong (⟪ sucV α ⟫↪) e
      ∙ fiber (sucV α) {x = ⟪ α ⟫↪ n} (∈sucV-inl (member α n)) .snd)

  stage-card-suc : ⟪ Lset (sucV α) ⟫ ↪ ⟪ sucV α ⟫
  stage-card-suc = f , inj
    where
    f : ⟪ Lset (sucV α) ⟫ → ⟪ sucV α ⟫
    f x = idx-suc (fst (successor-step α oα infα g) x)
    inj : (x y : ⟪ Lset (sucV α) ⟫) → f x ≡ f y → x ≡ y
    inj x y e =
      snd (successor-step α oα infα g) x y
        (idx-suc-inj (fst (successor-step α oα infα g) x)
                     (fst (successor-step α oα infα g) y) e)

stage-card-suc : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
               → ⟪ Lset α ⟫ ↪ ⟪ α ⟫ → ⟪ Lset (sucV α) ⟫ ↪ ⟪ sucV α ⟫
stage-card-suc α oα infα g = SucUpper.stage-card-suc α oα infα g

-- The union (limit) step at every infinite ordinal α: the stage's index
-- injects into ⟪ α ⟫, given an injection of every member stage's index into
-- ⟪ α ⟫ (the composed induction hypothesis). Route: each member of
-- Lset α is merely a member of 𝒟ₒ (Lset δ) for δ ∈ α (Lset-out), hence
-- merely a defSet φ over Formula ⟪ Lset δ ⟫ 1 (𝒟ₒ-inv); the count of that
-- formula type into ⟪ α ⟫ is Bound.formula-bound at β = α with the supplied
-- branch injection; packing the stage index m and the count value through
-- the pairing, and leastOf over ordSWO, picks the least packed value in the
-- class. Injectivity: equal packed values split by pair-inj, the stage
-- paths are eliminated by J, so no transport-coherence of the branch family
-- is needed, and count-injectivity with defSet-stability close the loop.
module LimitStep (α : S) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
                 (D : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S)
                 (inv : (δ : S) (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
                      → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
                 (ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫) where

  module B = Bound α oα infα (sq α infα)

  F : ⟪ α ⟫ → Type ℓ
  F m = Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1

  cnt : (m : ⟪ α ⟫) → F m → ⟪ α ⟫
  cnt m = fst (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m))

  cnt-inj : (m : ⟪ α ⟫) (φ ψ : F m) → cnt m φ ≡ cnt m ψ → φ ≡ ψ
  cnt-inj m = snd (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m))

  cnt-stable : (m₁ m₂ : ⟪ α ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
             → cnt m₁ (subst F q φ) ≡ cnt m₂ φ
  cnt-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → cnt m₁ (subst F q φ) ≡ cnt m₂ φ)
      (λ φ → cong (cnt m₂) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable : (m₁ m₂ : ⟪ α ⟫) (q : m₂ ≡ m₁) (φ : F m₂)
                → D (⟪ α ⟫↪ m₁) (subst F q φ)
                  ≡ D (⟪ α ⟫↪ m₂) φ
  defset-stable m₁ m₂ q φ =
    J (λ m₁ q → (φ : F m₂) → D (⟪ α ⟫↪ m₁) (subst F q φ)
                ≡ D (⟪ α ⟫↪ m₂) φ)
      (λ φ → cong (D (⟪ α ⟫↪ m₂)) (substRefl {B = F} {x = m₂} φ)) q φ

  defset-stable-δ : (δ₁ δ₂ : S) (p : δ₁ ≡ δ₂) (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1)
                  → D δ₁ φ₀
                    ≡ D δ₂
                        (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀)
  defset-stable-δ δ₁ δ₂ p φ₀ =
    J (λ δ₂ p → (φ₀ : Formula ⟪ Lset δ₁ ⟫ 1) → D δ₁ φ₀
                ≡ D δ₂
                    (subst (λ w → Formula ⟪ Lset w ⟫ 1) p φ₀))
      (λ φ₀ → sym (cong (D δ₁)
                   (substRefl {B = λ w → Formula ⟪ Lset w ⟫ 1} {x = δ₁} φ₀))) p φ₀

  class-pred : (x : ⟪ Lset α ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  class-pred x y = ( ∥ Σ[ m ∈ ⟪ α ⟫ ] Σ[ φ ∈ F m ]
                        ( ( D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x )
                        × ( B.pair m (cnt m φ) ≡ y ) ) ∥₁
                   , squash₁ )

  nonempty : (x : ⟪ Lset α ⟫)
           → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩ ∥₁
  nonempty x = PT.rec (squash₁) toWitness
    (Lset-out α (⟪ Lset α ⟫↪ x) (member (Lset α) x))
    where
    toWitness : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ ⟪ Lset α ⟫↪ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
              → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩ ∥₁
    toWitness (δ , (δ∈α , x∈𝒟ₒδ)) =
      PT.map mk (inv δ (⟪ Lset α ⟫↪ x) x∈𝒟ₒδ)
      where
      fib = fiber α {x = δ} δ∈α
      m : ⟪ α ⟫
      m = fib .fst
      p : ⟪ α ⟫↪ m ≡ δ
      p = fib .snd
      mk : Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ]
             (D δ φ₀ ≡ ⟪ Lset α ⟫↪ x)
         → Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred x y ⟩
      mk (φ₀ , e₀) = (B.pair m (cnt m φ) , ∣ (m , φ , (e , refl)) ∣₁)
        where
        φ : F m
        φ = subst (λ w → Formula ⟪ Lset w ⟫ 1) (sym p) φ₀
        e : D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x
        e = sym (defset-stable-δ δ (⟪ α ⟫↪ m) (sym p) φ₀) ∙ e₀

  h : ⟪ Lset α ⟫ → ⟪ α ⟫
  h x = fst (leastOf (OrdSWO.ordSWO α oα) lem (class-pred x) (nonempty x))

  h-inj : (x y : ⟪ Lset α ⟫) → h x ≡ h y → x ≡ y
  h-inj x y e = ↪-inj {a = Lset α} (go pm)
    where
    lx = leastOf (OrdSWO.ordSWO α oα) lem (class-pred x) (nonempty x)
    ly = leastOf (OrdSWO.ordSWO α oα) lem (class-pred y) (nonempty y)
    pm : ⟨ class-pred x (fst ly) ⟩
    pm = subst (λ z → ⟨ class-pred x z ⟩) e (fst (snd lx))
    py : ⟨ class-pred y (fst ly) ⟩
    py = fst (snd ly)
    go : ⟨ class-pred x (fst ly) ⟩
       → ⟪ Lset α ⟫↪ x ≡ ⟪ Lset α ⟫↪ y
    go = PT.rec (isSetS (⟪ Lset α ⟫↪ x) (⟪ Lset α ⟫↪ y)) go₁
      where
      go₁ : Σ[ m₁ ∈ ⟪ α ⟫ ] Σ[ φ₁ ∈ F m₁ ]
              ( ( D (⟪ α ⟫↪ m₁) φ₁ ≡ ⟪ Lset α ⟫↪ x )
              × ( B.pair m₁ (cnt m₁ φ₁) ≡ fst ly ) )
          → ⟪ Lset α ⟫↪ x ≡ ⟪ Lset α ⟫↪ y
      go₁ (m₁ , φ₁ , eφ₁ , ec₁) =
        PT.rec (isSetS (⟪ Lset α ⟫↪ x) (⟪ Lset α ⟫↪ y)) go₂ py
        where
        go₂ : Σ[ m₂ ∈ ⟪ α ⟫ ] Σ[ φ₂ ∈ F m₂ ]
                ( ( D (⟪ α ⟫↪ m₂) φ₂ ≡ ⟪ Lset α ⟫↪ y )
                × ( B.pair m₂ (cnt m₂ φ₂) ≡ fst ly ) )
            → ⟪ Lset α ⟫↪ x ≡ ⟪ Lset α ⟫↪ y
        go₂ (m₂ , φ₂ , eφ₂ , ec₂) = sym eφ₁ ∙ eq-defset ∙ eφ₂
          where
          ec : B.pair m₁ (cnt m₁ φ₁) ≡ B.pair m₂ (cnt m₂ φ₂)
          ec = ec₁ ∙ sym ec₂
          p-pair : (m₁ ≡ m₂) × (cnt m₁ φ₁ ≡ cnt m₂ φ₂)
          p-pair = B.pair-inj m₁ (cnt m₁ φ₁) m₂ (cnt m₂ φ₂) ec
          qm : m₁ ≡ m₂
          qm = fst p-pair
          ecount : cnt m₁ φ₁ ≡ cnt m₂ φ₂
          ecount = snd p-pair
          ecount' : cnt m₁ φ₁ ≡ cnt m₁ (subst F (sym qm) φ₂)
          ecount' = ecount ∙ sym (cnt-stable m₁ m₂ (sym qm) φ₂)
          eφ : φ₁ ≡ subst F (sym qm) φ₂
          eφ = cnt-inj m₁ φ₁ (subst F (sym qm) φ₂) ecount'
          eq-defset : D (⟪ α ⟫↪ m₁) φ₁
                    ≡ D (⟪ α ⟫↪ m₂) φ₂
          eq-defset = cong (D (⟪ α ⟫↪ m₁)) eφ
                    ∙ defset-stable m₁ m₂ (sym qm) φ₂

limit-step : (α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ((m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫)
           → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
limit-step α oα infα ih =
  LimitStep.h α oα infα (λ δ φ → DefOf.defSet (Lset δ) φ)
    (λ δ x h → 𝒟ₒ-inv (Lset δ) x h) ih
    , LimitStep.h-inj α oα infα (λ δ φ → DefOf.defSet (Lset δ) φ)
        (λ δ x h → 𝒟ₒ-inv (Lset δ) x h) ih

-- The assembly: the upper half of |Lset α| = |α| at every infinite ordinal
-- α, by ∈-induction. The union step is generic, so one step serves both
-- successor and limit ordinals. The induction hypothesis supplies the
-- branch injection at every member δ ∈ α: at an infinite δ the composed
-- IH, at δ = ω the IH at ω itself, and at a finite δ the parameter fin-inj
-- (the ω-base, priced separately). The only genuinely missing piece for
-- the chain is fin-inj: the finite stages' injections into ω.
module Upper (fin-inj : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ⟪ Lset δ ⟫ ↪ ⟪ ω ⟫) where

  comp-inj : {A B C : Type ℓ} → A ↪ B → B ↪ C → A ↪ C
  comp-inj (f , injf) (g , injg) =
    (λ x → g (f x)) , λ x y e → injf x y (injg (f x) (f y) e)

  module Emb (α : S) (oα : IsOrd α) where

    emb : (δ : S) → ⟨ δ ∈ˢ α ⟩ → ⟪ δ ⟫ ↪ ⟪ α ⟫
    emb δ δ∈α = f , inj
      where
      f : ⟪ δ ⟫ → ⟪ α ⟫
      f m = fiber α {x = ⟪ δ ⟫↪ m} (oα .fst (member δ m) δ∈α) .fst
      inj : (m n : ⟪ δ ⟫) → f m ≡ f n → m ≡ n
      inj m n e = ↪-inj {a = δ}
        (sym (fiber α {x = ⟪ δ ⟫↪ m} (oα .fst (member δ m) δ∈α) .snd)
          ∙ cong (⟪ α ⟫↪) e
          ∙ fiber α {x = ⟪ δ ⟫↪ n} (oα .fst (member δ n) δ∈α) .snd)

  module WOEmb (α : S) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

    id-inj : ⟪ ω ⟫ ↪ ⟪ ω ⟫
    id-inj = (λ x → x) , λ x y p → p

    ω-inj : ⟪ ω ⟫ ↪ ⟪ α ⟫
    ω-inj = go (ord-tri ω ω-ord α oα)
      where
      go : ⟨ ω ∈ˢ α ⟩ ⊎ ((ω ≡ α) ⊎ ⟨ α ∈ˢ ω ⟩) → ⟪ ω ⟫ ↪ ⟪ α ⟫
      go (inl ω∈α) = Emb.emb α oα ω ω∈α
      go (inr (inl e)) = subst (λ A → ⟪ ω ⟫ ↪ ⟪ A ⟫) e id-inj
      go (inr (inr α∈ω)) = Empty.rec (infα α∈ω)

  P : S → Type (ℓ-suc ℓ)
  P α = IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ Lset α ⟫ → ⟪ α ⟫) ] ((x y : ⟪ Lset α ⟫) → f x ≡ f y → x ≡ y)

  branch : (α : S) (oα : IsOrd α) (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
         → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P δ)
         → (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
  branch α oα infα IH m = go (ord-tri δ oδ ω ω-ord)
    where
    δ : S
    δ = ⟪ α ⟫↪ m
    δ∈α : ⟨ δ ∈ˢ α ⟩
    δ∈α = member α m
    oδ : IsOrd δ
    oδ = mem-ord {A = α} oα δ δ∈α
    go : ⟨ δ ∈ˢ ω ⟩ ⊎ ((δ ≡ ω) ⊎ ⟨ ω ∈ˢ δ ⟩) → ⟪ Lset δ ⟫ ↪ ⟪ α ⟫
    go (inl δ∈ω) = comp-inj (fin-inj δ δ∈ω) (WOEmb.ω-inj α oα infα)
    go (inr (inl e)) = subst (λ w → ⟪ Lset w ⟫ ↪ ⟪ α ⟫) (sym e)
      (comp-inj (IH ω (subst (λ w → ⟨ w ∈ˢ α ⟩) e δ∈α) ω-ord (∈-irrefl ω))
                (WOEmb.ω-inj α oα infα))
    go (inr (inr ω∈δ)) =
      comp-inj (IH δ δ∈α oδ infδ) (Emb.emb α oα δ δ∈α)
      where
      infδ : ⟨ δ ∈ˢ ω ⟩ → Empty.⊥
      infδ h = ∈-irrefl ω (ω-ord .fst ω∈δ h)

  step : (α : S) → ((δ : S) → ⟨ δ ∈ˢ α ⟩ → P δ) → P α
  step α IH oα infα = limit-step α oα infα (branch α oα infα IH)

  stage-card-upper : (α : S) → IsOrd α
                   → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
  stage-card-upper = ∈-induction step
```
