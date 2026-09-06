# A definable injection is a coded injection

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Definable {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Renaming using ( module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Recursion {ℓ} lem using ( Recursion; module Of )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.OrderType {ℓ} lem using ( module PairFo )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Foundations.HLevels using ( isPropΣ; isSetΣSndProp )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Renaming, read at the same satisfaction as `_⊨_` (as `L.Axioms.Full` does).

```agda
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id using ( Agrees; ⊨-rename )
```

## Section 1. The form

A function on the members of a set of L, landing in a set of L, whose graph an
object-language formula defines: the formula holds of the function's own value
(`defines`) and of nothing else (`only`). Value first, index second, as
`Recursion.graph`.

```agda
record DefinableMap : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    dom cod : S
    fn      : (x : S) → ⟨ fst x ∈ˢ fst dom ⟩ → S
    into    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) → ⟨ fst (fn x m) ∈ˢ fst cod ⟩
    graph   : Formula S 2
    defines : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩)
            → ⟨ (fn x m ∷ x ∷ []) ⊨ graph ⟩
    only    : (x : S) (m : ⟨ fst x ∈ˢ fst dom ⟩) (y : S)
            → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ fn x m
```

## Section 2. The pair formula

## Section 3. The graph as a set of L, and three conjuncts

`Recursion.funct` takes the membership proof, so `fn` fills it as it stands: no
total extension off `dom` and no use of `lem`. The table is the replacement
image (src/L/Recursion.lagda.md, `Of`).

```agda
module Graph (M : DefinableMap) where
  open DefinableMap M public

  -- Membership in the domain, as `fn` consumes it.
  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ˢ fst dom ⟩

  isPropMem : (x : S) → isProp (Mem x)
  isPropMem x = snd (fst x ∈ˢ fst dom)

  private
    module Fo = PairFo graph renaming ( pairFo to fo; pair-out to out; pair-in to into )

    isSetS : isSet S
    isSetS = isSetΣSndProp setIsSet (λ v → snd (isL v))

    -- The value does not depend on which membership proof was given.
    fn-irr : (x : S) (m m' : Mem x) → fn x m ≡ fn x m'
    fn-irr x m m' = cong (fn x) (isPropMem x m m')

    -- The pair, as an element of L.
    pairOf : (x : S) → Mem x → S
    pairOf x m = prʟ x (fn x m)

    uniq : (x : S) (m : Mem x) (p : S) → ⟨ (p ∷ x ∷ []) ⊨ Fo.fo ⟩ → p ≡ pairOf x m
    uniq x m p h = PT.rec (isSetS p (pairOf x m))
      (λ { (z , (e , g)) → Σ≡Prop (λ v → snd (isL v))
        (e ∙ cong (λ w → pr (fst x) (fst w)) (only x m z g) ∙ sym (prʟ-fst x (fn x m))) })
      (Fo.out p x h)

    R : Recursion
    R = record
      { dom   = dom
      ; graph = Fo.fo
      ; funct = λ x m →
          ( pairOf x m
          , Fo.into (pairOf x m) x (fn x m) (prʟ-fst x (fn x m)) (defines x m) )
        , λ { (p , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ Fo.fo)) (sym (uniq x m p h)) } }

    module T = Of R using ( table; table-in; table-out )

  F : S
  F = T.table

  F-in : (x : S) (m : Mem x) → ⟨ pr (fst x) (fst (fn x m)) ∈ fst F ⟩
  F-in x m = subst (λ w → ⟨ w ∈ fst F ⟩) (prʟ-fst x (fn x m))
    (T.table-in x (pairOf x m) m
      (Fo.into (pairOf x m) x (fn x m) (prʟ-fst x (fn x m)) (defines x m)))

  F-out : (p : V ℓ) → ⟨ p ∈ˢ fst F ⟩
        → ∥ Σ[ x ∈ S ] Σ[ m ∈ Mem x ] (p ≡ pr (fst x) (fst (fn x m))) ∥₁
  F-out p h = PT.rec squash₁ step (T.table-out pS h)
    where
    pS : S
    pS = p , isL-trans {x = fst F} {y = p} h (snd F)

    step : Σ[ x ∈ S ] (Mem x × ⟨ (pS ∷ x ∷ []) ⊨ Fo.fo ⟩)
         → ∥ Σ[ x ∈ S ] Σ[ m ∈ Mem x ] (p ≡ pr (fst x) (fst (fn x m))) ∥₁
    step (x , (m , g)) = PT.map
      (λ { (z , (e , gz)) →
        x , m , (e ∙ cong (λ w → pr (fst x) (fst w)) (only x m z gz)) })
      (Fo.out pS x g)

  -- A pair in F, read as a value of `fn`.  The target is a proposition,
  -- so the truncation comes off.
  Fib : S → S → Type (ℓ-suc ℓ)
  Fib x y = Σ[ m ∈ Mem x ] (fst y ≡ fst (fn x m))

  isPropFib : (x y : S) → isProp (Fib x y)
  isPropFib x y = isPropΣ (isPropMem x) (λ m → setIsSet (fst y) (fst (fn x m)))

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → Fib x y
  pair-out x y h = PT.rec (isPropFib x y) step (F-out (pr (fst x) (fst y)) h)
    where
    step : Σ[ x' ∈ S ] Σ[ m' ∈ Mem x' ] (pr (fst x) (fst y) ≡ pr (fst x') (fst (fn x' m')))
         → Fib x y
    step (x' , m' , e) = m , (snd q ∙ sym val)
      where
      q : (fst x ≡ fst x') × (fst y ≡ fst (fn x' m'))
      q = pr-inj e
      xx : x ≡ x'
      xx = Σ≡Prop (λ v → snd (isL v)) (fst q)
      m : Mem x
      m = subst Mem (sym xx) m'
      val : fst (fn x m) ≡ fst (fn x' m')
      val = subst (λ w → (k : Mem w) → fst (fn x m) ≡ fst (fn w k)) xx
              (λ k → cong (λ v → fst (fn x v)) (isPropMem x m k)) m'

  -- THE CONJUNCTS.
  γ : S ^ 2
  γ = F ∷ dom ∷ []

  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ (λ x y y' p q →
    let (m , e)   = pair-out x y p
        (m' , e') = pair-out x y' q
    in e ∙ cong fst (fn-irr x m m') ∙ sym e')

  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → Mem x
    fwd x = PT.rec (isPropMem x) (λ { (y , p) → fst (pair-out x y p) })

    bwd : (x : S) → Mem x → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩
    bwd x m = ∣ fn x m , F-in x m ∣₁

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst cod ⟩
  ran x y h = subst (λ w → ⟨ w ∈ fst cod ⟩) (sym e) (into x m)
    where
    m = fst (pair-out x y h)
    e = snd (pair-out x y h)
```

## Section 4. Injective, hence coded

```agda
module Inj (M : DefinableMap)
           (inj : (x : S) (m : ⟨ fst x ∈ˢ fst (DefinableMap.dom M) ⟩)
                  (x' : S) (m' : ⟨ fst x' ∈ˢ fst (DefinableMap.dom M) ⟩)
                → fst (DefinableMap.fn M x m) ≡ fst (DefinableMap.fn M x' m')
                → fst x ≡ fst x') where

  open Graph M public

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ (λ y x x' p q →
    let (m , e)   = pair-out x y p
        (m' , e') = pair-out x' y q
    in inj x m x' m' (sym e ∙ e'))

  code : InjCode F dom cod
  code = sv , dm , ij , ran

  injL : InjL dom cod
  injL = ∣ F , code ∣₁
```
