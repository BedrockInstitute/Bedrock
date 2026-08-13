{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
import Cubical.Data.Empty as Empty


module ProbeLJ124Base {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
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
