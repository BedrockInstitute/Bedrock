{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.435] PROBE.  The limit step from a POINTWISE truncated branch
-- family.  It runs in agents/tasks/LJ-1-435/ and lands nothing in src/.
--
--   W3 FIRST  `h-trunc`.  The VALUE half: least member of class-pred',
--             whose witness carries the branch injection.  Stated alone
--             and run before injectivity, per the brief.
--
--   TERM      `limit-step-trunc`.  Hole by design: h'-inj needs
--             cnt-cross, which is refuted in PART 3.
--
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M8g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( ω; sucV; #_ )
open import L.Constructible using ( IsOrd; Lset )
import Cubical.Data.Empty as Empty

module LJ-1-435.Probe435 {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

open import FOL.Syntax using ( Formula; _≐_; var; con )
open import FOL.Count {ℓ} using ( composed-count; code; module Count )
open import FOL.Manipulation.Parameters using ( countFo; constantsFo )
open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( fiber; member )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒟ₒ; 𝒟ₒ-inv; Lset-out )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ} using ( leastOf )
import L.StageCardinal
open import Cubical.Foundations.Prelude using ( J; substRefl; transportRefl )
open import Cubical.Data.Bool using ( Bool; true; false; false≢true )
open import Cubical.Data.FinData as FD using ( Fin )
open import Cubical.Data.Vec using ( Vec; _∷_; []; head )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SC = L.StageCardinal {ℓ} lem α₀ oα₀ sq
open SC using ( _↪_ )

-- =====================================================================
-- W3.  THE VALUE HALF, ALONE.  class-pred' carries the branch injection
-- inside the truncation that is already there.  The pairing stays data
-- at Bound, exactly as src/L/StageCardinal.lagda.md:283.
-- =====================================================================

module LimitStepTrunc
  (α : S) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
  (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  (D : (δ : S) → Formula ⟪ Lset δ ⟫ 1 → S)
  (inv : (δ : S) (y : S) → ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩
       → ∥ Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ] (D δ φ₀ ≡ y) ∥₁)
  (ih : (m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫ ∥₁) where

  module B = SC.Bound α oα infα (sq α α∈suc infα)

  F : ⟪ α ⟫ → Type ℓ
  F m = Formula ⟪ Lset (⟪ α ⟫↪ m) ⟫ 1

  cnt-of : {m : ⟪ α ⟫} → (⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫) → F m → ⟪ α ⟫
  cnt-of {m} g = fst (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} g)

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

  class-pred' : (x : ⟪ Lset α ⟫) → ⟪ α ⟫ → hProp (ℓ-suc ℓ)
  class-pred' x y = ( ∥ Σ[ m ∈ ⟪ α ⟫ ] Σ[ g ∈ (⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫) ]
                        Σ[ φ ∈ F m ]
                        ( ( D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x )
                        × ( B.pair m (cnt-of g φ) ≡ y ) ) ∥₁
                    , squash₁ )

  nonempty : (x : ⟪ Lset α ⟫)
           → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred' x y ⟩ ∥₁
  nonempty x = PT.rec squash₁ toWitness
    (Lset-out α (⟪ Lset α ⟫↪ x) (member (Lset α) x))
    where
    toWitness : Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ ⟪ Lset α ⟫↪ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
              → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred' x y ⟩ ∥₁
    toWitness (δ , (δ∈α , x∈𝒟ₒδ)) =
      PT.rec squash₁ go (inv δ (⟪ Lset α ⟫↪ x) x∈𝒟ₒδ)
      where
      fib = fiber α {x = δ} δ∈α
      m : ⟪ α ⟫
      m = fib .fst
      p : ⟪ α ⟫↪ m ≡ δ
      p = fib .snd
      go : Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ]
             (D δ φ₀ ≡ ⟪ Lset α ⟫↪ x)
         → ∥ Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred' x y ⟩ ∥₁
      go φe = PT.map (mk φe) (ih m)
        where
        mk : Σ[ φ₀ ∈ Formula ⟪ Lset δ ⟫ 1 ]
               (D δ φ₀ ≡ ⟪ Lset α ⟫↪ x)
           → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫
           → Σ[ y ∈ ⟪ α ⟫ ] ⟨ class-pred' x y ⟩
        mk (φ₀ , e₀) g = (B.pair m (cnt-of g φ) , ∣ (m , g , φ , (e , refl)) ∣₁)
          where
          φ : F m
          φ = subst (λ w → Formula ⟪ Lset w ⟫ 1) (sym p) φ₀
          e : D (⟪ α ⟫↪ m) φ ≡ ⟪ Lset α ⟫↪ x
          e = sym (defset-stable-δ δ (⟪ α ⟫↪ m) (sym p) φ₀) ∙ e₀

  h : ⟪ Lset α ⟫ → ⟪ α ⟫
  h x = fst (leastOf (SC.OrdSWO.ordSWO α oα) lem (class-pred' x) (nonempty x))

h-trunc :
    (α : S) (α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩) (oα : IsOrd α)
    (infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫ ∥₁)
  → ⟪ Lset α ⟫ → ⟪ α ⟫
h-trunc α α∈suc oα infα ih =
  LimitStepTrunc.h α α∈suc oα infα
    (λ δ φ → DefOf.defSet (Lset δ) φ)
    (λ δ x h → 𝒟ₒ-inv (Lset δ) x h)
    ih

-- =====================================================================
-- THE OBLIGATION, AS THE BRIEF STATES IT.  UNINHABITED: see PART 3.
-- h'-inj needs cnt-cross at src/L/StageCardinal.lagda.md:390, which
-- is cnt-inj at TWO injections.  The tree delivers cnt-inj at ONE.
-- =====================================================================

limit-step-trunc :
    (α : S) → ⟨ α ∈ˢ sucV α₀ ⟩ → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
  → ((m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫ ∥₁)
  → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁
limit-step-trunc = ?

-- The type h'-inj needs after pair-inj splits the packed values and
-- the two stage indices are identified.  formula-bound at TWO
-- injections, one equation of counts, conclusion the formulas match.

fb : (β : S) (oβ : IsOrd β) (infβ : ⟨ β ∈ˢ ω ⟩ → Empty.⊥)
   → (pairing : Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
                  ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y))
   → {K : Type ℓ} → (K ↪ ⟪ β ⟫) → Formula K 1 → ⟪ β ⟫
fb β oβ infβ pairing {K} g =
  fst (SC.Bound.formula-bound β oβ infβ pairing {K} g)

CntCross : Type (ℓ-suc ℓ)
CntCross =
    (β : S) (oβ : IsOrd β) (infβ : ⟨ β ∈ˢ ω ⟩ → Empty.⊥)
  → (pairing : Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
                 ((x y : ⟪ β ⟫ × ⟪ β ⟫) → f x ≡ f y → x ≡ y))
  → {K : Type ℓ}
  → (g₁ g₂ : K ↪ ⟪ β ⟫)
  → (φ ψ : Formula K 1)
  → fb β oβ infβ pairing g₁ φ ≡ fb β oβ infβ pairing g₂ ψ
  → φ ≡ ψ

-- =====================================================================
-- PART 3.  THE REFUTATION.  The site is β := ω, with any pairing.
--
--   K is Lift ℓ Bool.  g₁ sends lift false to m0 and lift true to m1.
--   g₂ is the swap.  φ is (var 0 ≐ con (lift false)), ψ is the same
--   with lift true.  encTm ignores the constant value
--   (src/FOL/Count.lagda.md:284-285), so the shapes match, and
--   tuple-g g₁ of [false, false] equals tuple-g g₂ of [true, true]
--   because g₂ (lift true) ≡ m0 ≡ g₁ (lift false).  CntCross would
--   then force φ ≡ ψ, hence lift false ≡ lift true.
-- =====================================================================

m0 : ⟪ ω ⟫
m0 = fiber ω {x = # 0} (#∈ω 0) .fst

m1 : ⟪ ω ⟫
m1 = fiber ω {x = # 1} (#∈ω 1) .fst

m0≢m1 : m0 ≡ m1 → Empty.⊥
m0≢m1 e = ∈-irrefl (# 0) (subst (λ w → ⟨ (# 0) ∈ˢ w ⟩) (sym eq01) n0∈n1)
  where
  eq01 : # 0 ≡ # 1
  eq01 = sym (fiber ω {x = # 0} (#∈ω 0) .snd)
       ∙ cong (⟪ ω ⟫↪) e
       ∙ fiber ω {x = # 1} (#∈ω 1) .snd
  n0∈n1 : ⟨ (# 0) ∈ˢ (# 1) ⟩
  n0∈n1 = subst (λ w → ⟨ (# 0) ∈ˢ w ⟩) suc#0 (self∈sucV (# 0))
    where
    suc#0 : sucV (# 0) ≡ # 1
    suc#0 = refl

K₂ : Type ℓ
K₂ = Lift {ℓ-zero} {ℓ} Bool

g₁ : K₂ → ⟪ ω ⟫
g₁ (lift false) = m0
g₁ (lift true)  = m1

g₁-inj : (x y : K₂) → g₁ x ≡ g₁ y → x ≡ y
g₁-inj (lift false) (lift false) _ = refl
g₁-inj (lift true)  (lift true)  _ = refl
g₁-inj (lift false) (lift true)  e = Empty.rec (m0≢m1 e)
g₁-inj (lift true)  (lift false) e = Empty.rec (m0≢m1 (sym e))

g₂ : K₂ → ⟪ ω ⟫
g₂ (lift false) = m1
g₂ (lift true)  = m0

g₂-inj : (x y : K₂) → g₂ x ≡ g₂ y → x ≡ y
g₂-inj (lift false) (lift false) _ = refl
g₂-inj (lift true)  (lift true)  _ = refl
g₂-inj (lift false) (lift true)  e = Empty.rec (m0≢m1 (sym e))
g₂-inj (lift true)  (lift false) e = Empty.rec (m0≢m1 e)

g₁↪ : K₂ ↪ ⟪ ω ⟫
g₁↪ = g₁ , g₁-inj

g₂↪ : K₂ ↪ ⟪ ω ⟫
g₂↪ = g₂ , g₂-inj

φ₀ : Formula K₂ 1
φ₀ = var FD.zero ≐ con (lift false)

ψ₀ : Formula K₂ 1
ψ₀ = var FD.zero ≐ con (lift true)

only-con : Formula K₂ 1 → K₂
only-con (_ ≐ con c) = c
only-con _           = lift false

lift-false≢true : lift {ℓ-zero} {ℓ} false ≡ lift {ℓ-zero} {ℓ} true → Empty.⊥
lift-false≢true e = false≢true (cong lower e)

module CK = Count K₂

atom : K₂ → Formula K₂ 1
atom c = var FD.zero ≐ con c

encode-cs : (c : K₂) → Vec K₂ (fst (CK.encode (atom c)))
encode-cs c = CK.encode (atom c) .snd .snd

-- The subst inside encode is along `refl {x = countFo (atom c)}`,
-- not along `refl {x = 1}`.  substRefl at that index opens it.
encode-cs-snoc :
    (c : K₂)
  → encode-cs c
      ≡ CK.snoc
          (subst (Vec K₂) (refl {x = countFo (atom c)}) (constantsFo (atom c)))
          (CK.head (subst (Vec K₂) (refl {x = countFo (atom c)})
                    (constantsFo (atom c))))
encode-cs-snoc c = refl

encode-cs-open :
    (c : K₂)
  → encode-cs c ≡ (c ∷ c ∷ [])
encode-cs-open c =
  encode-cs-snoc c
  ∙ cong₂ CK.snoc
      (substRefl {B = Vec K₂} {x = countFo (atom c)} (constantsFo (atom c))
       ∙ constantsFo-atom c)
      (cong CK.head
        (substRefl {B = Vec K₂} {x = countFo (atom c)} (constantsFo (atom c))
         ∙ constantsFo-atom c)
       ∙ head-cons c)
  ∙ snoc-two c
  where
  constantsFo-atom : (c : K₂) → constantsFo (atom c) ≡ (c ∷ [])
  constantsFo-atom c = refl
  head-cons : (c : K₂) → CK.head (c ∷ []) ≡ c
  head-cons c = refl
  snoc-two : (c : K₂) → CK.snoc (c ∷ []) c ≡ (c ∷ c ∷ [])
  snoc-two c = refl

encode-k : (c : K₂) → fst (CK.encode (atom c)) ≡ 2
encode-k c = refl

counts-eq-prf :
    (pairing : Σ[ f ∈ (⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫) ]
                 ((x y : ⟪ ω ⟫ × ⟪ ω ⟫) → f x ≡ f y → x ≡ y))
  → fb ω ω-ord (∈-irrefl ω) pairing g₁↪ φ₀
    ≡ fb ω ω-ord (∈-irrefl ω) pairing g₂↪ ψ₀
counts-eq-prf pairing = goal
  where
  module Bω = SC.Bound ω ω-ord (∈-irrefl ω) pairing
  pktφ = fst (composed-count {K = K₂}) φ₀
  pktψ = fst (composed-count {K = K₂}) ψ₀
  kφ = pktφ .fst
  kψ = pktψ .fst
  shapeφ = pktφ .snd .fst
  shapeψ = pktψ .snd .fst
  nφ = pktφ .snd .snd .fst
  nψ = pktψ .snd .snd .fst
  csφ = pktφ .snd .snd .snd
  csψ = pktψ .snd .snd .snd
  k-eq : kφ ≡ kψ
  k-eq = refl
  shape-eq : shapeφ ≡ shapeψ
  shape-eq = refl
  n-eq : nφ ≡ nψ
  n-eq = refl
  -- composed-count's vector is encode's vector
  -- (src/FOL/Count.lagda.md:702).
  csφ-enc : csφ ≡ encode-cs (lift false)
  csφ-enc = refl
  csψ-enc : csψ ≡ encode-cs (lift true)
  csψ-enc = refl
  tup-repeat : (g : K₂ ↪ ⟪ ω ⟫) (c : K₂)
             → Bω.tuple-g g 2 (c ∷ c ∷ [])
               ≡ Bω.pair (fst g c) (Bω.pair (fst g c) (Bω.numeral 0))
  tup-repeat g c = refl
  g₁false≡g₂true : g₁ (lift false) ≡ g₂ (lift true)
  g₁false≡g₂true = refl
  tup-eq : Bω.tuple-g g₁↪ kφ csφ ≡ Bω.tuple-g g₂↪ kψ csψ
  tup-eq =
      cong (Bω.tuple-g g₁↪ kφ) csφ-enc
    ∙ cong (Bω.tuple-g g₁↪ 2) (encode-cs-open (lift false))
    ∙ tup-repeat g₁↪ (lift false)
    ∙ cong₂ Bω.pair g₁false≡g₂true (cong₂ Bω.pair g₁false≡g₂true refl)
    ∙ sym (tup-repeat g₂↪ (lift true))
    ∙ sym (cong (Bω.tuple-g g₂↪ 2) (encode-cs-open (lift true)))
    ∙ sym (cong (Bω.tuple-g g₂↪ kψ) csψ-enc)
  goal : Bω.count-bound g₁↪ pktφ ≡ Bω.count-bound g₂↪ pktψ
  goal = cong₂ Bω.pair
           (cong Bω.numeral k-eq)
           (cong₂ Bω.pair
             (cong₂ Bω.pair
               (cong Bω.numeral (cong code shape-eq))
               (cong Bω.numeral n-eq))
             tup-eq)

cnt-cross-refuted :
    (pairing : Σ[ f ∈ (⟪ ω ⟫ × ⟪ ω ⟫ → ⟪ ω ⟫) ]
                 ((x y : ⟪ ω ⟫ × ⟪ ω ⟫) → f x ≡ f y → x ≡ y))
  → CntCross
  → Empty.⊥
cnt-cross-refuted pairing cc =
  lift-false≢true (cong only-con (cc ω ω-ord (∈-irrefl ω) pairing g₁↪ g₂↪ φ₀ ψ₀ (counts-eq-prf pairing)))

