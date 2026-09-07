# Injections into L, composed and paired

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.InjChain {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _≐_; _∧̇_; ∃̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( ω-ord; #∈ω )
import L.Ordinal.SquareLaw {ℓ} lem as SQ
open SQ using ( module FiniteBase )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Model {ℓ} using ( appC; appC-adequate ) public
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-out; injAt-in; module Small )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH.Definable {ℓ} lem
  using ( DefinableMap ) renaming ( module Inj to DefinableInj )

import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
open import Cubical.Foundations.Prelude using ( subst2 )
import Cubical.Foundations.Equiv as Equiv
open Equiv using ( equivFun; invEq; retEq; _≃_ )
open import Cubical.Foundations.Univalence using ( pathToEquiv )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_; ω )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )


open FiniteBase using ( ω-mem→numeral; toFin; toFin-inj; fromFin; fromFin-inj )
open FiniteBase using ( module AbstractChase )
```

The shared bound is `Recursion.smallDom`: a small family of elements of L
lies in one stage. The bound and its membership reader stay sealed, since every
consumer uses the bound as an atom.

```agda
module StageBound (I : Type ℓ) (g : I → S) where

  opaque
    bnd : S
    bnd = smallDom I g .fst

    below : (i : I) → ⟨ fst (g i) ∈ fst bnd ⟩
    below = smallDom I g .snd
```

Row 5. The pairing on `ω`, by the order route, zero arithmetic.

The square law at an initial ordinal wanted three hypotheses, and `ω` is not
initial (it would need `⟨ ω ∈ˢ ω ⟩`, refuted by `∈-irrefl`), so the three are
supplied at `ω` directly. Of the three only `finite-excl-ω` still has a
consumer; the ambient law they fed is retired to
`archive/src-2026-09-06/L/Ordinal/SquareLawAmbient.lagda.md`.

Successor closure at `ω`: every member of `ω` is a numeral.

```agda
ω-limit : (γ : V ℓ) → ⟨ γ ∈ ω ⟩ → ⟨ sucV γ ∈ ω ⟩
ω-limit γ γ∈ω = PT.rec (snd (sucV γ ∈ ω)) go (ω-mem→numeral γ γ∈ω)
  where
  go : Σ[ n ∈ ℕ ] (γ ≡ # n) → ⟨ sucV γ ∈ ω ⟩
  go (n , p) = subst (λ w → ⟨ sucV w ∈ ω ⟩) (sym p) (#∈ω (suc n))
```

No member of `ω` contains `ω`.

The numeral-into-`ω` injection, without `ω ∈ ω`.

```agda
numeral-into-ω : (m : ℕ) → ⟪ # m ⟫ → ⟪ ω ⟫
numeral-into-ω m i = fiber ω (ω-ord .fst (member (# m) i) (#∈ω m)) .fst

numeral-into-ω-inj : (m : ℕ) (i₁ i₂ : ⟪ # m ⟫)
                   → numeral-into-ω m i₁ ≡ numeral-into-ω m i₂ → i₁ ≡ i₂
numeral-into-ω-inj m i₁ i₂ e = ↪-inj {a = # m}
  (sym (fiber ω (ω-ord .fst (member (# m) i₁) (#∈ω m)) .snd)
    ∙ cong (⟪ ω ⟫↪) e
    ∙ fiber ω (ω-ord .fst (member (# m) i₂) (#∈ω m)) .snd)
```

No injection of `ω` into a finite square.

```agda
no-inj-finite-ω : (n : ℕ) → (f : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫)
                → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
no-inj-finite-ω n f finj =
  AbstractChase.NoInj.no-inj
    (λ n → ⟪ # n ⟫)
    toFin toFin-inj
    fromFin fromFin-inj
    (⟪ ω ⟫)
    (numeral-into-ω)
    (numeral-into-ω-inj)
    n f finj
```

The finite-exclusion clause at `ω`.

```agda
finite-excl-ω : (β : V ℓ) → IsOrd β → ⟨ β ∈ ω ⟩
              → (f : ⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
              → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
finite-excl-ω β oβ β∈ω f finj =
  PT.rec Empty.isProp⊥ go (ω-mem→numeral β β∈ω)
  where
  go : Σ[ n ∈ ℕ ] (β ≡ # n) → Empty.⊥
  go (n , p) = no-inj-finite-ω n f' finj'
    where
    e : ⟪ β ⟫ × ⟪ β ⟫ ≃ ⟪ # n ⟫ × ⟪ # n ⟫
    e = pathToEquiv (cong (λ w → ⟪ w ⟫ × ⟪ w ⟫) p)
    f' : ⟪ ω ⟫ → ⟪ # n ⟫ × ⟪ # n ⟫
    f' x = equivFun e (f x)
    finj' : (x y : ⟪ ω ⟫) → f' x ≡ f' y → x ≡ y
    finj' x y e' = finj x y
      (sym (retEq e (f x)) ∙ cong (invEq e) e' ∙ retEq e (f y))
```

Row 1. The composition of two injection graphs, by separation.

`appC` reads each graph at a constant. The shared bounded relation binds the
two endpoints; the composite condition binds their intermediate value.

The bound for row 1, as an instance of the shared device.  The index
type is the pairs of a domain member and a codomain member, and the
family sends each pair to its coded ordered pair.  Nothing here builds
a bound: `StageBound` builds it once, for every row and for A6.

```agda
module PairBound (D C : S) where

  Ix : Type ℓ
  Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫

  private
    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

    pw : Ix → S
    pw (m , k) = prʟ (toD m) (toC k)

    module SB = StageBound Ix pw
```

An alias of a SEALED name, so it is an atom here too.

```agda
  bnd : S
  bnd = SB.bnd

  below : (x z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
        → ⟨ pr (fst x) (fst z) ∈ fst bnd ⟩
  below x z mx mz = subst (λ w → ⟨ w ∈ fst bnd ⟩) pa (SB.below i)
    where
    fD : Σ[ m ∈ ⟪ fst D ⟫ ] (⟪ fst D ⟫↪ m ≡ fst x)
    fD = fiber (fst D) mx
    fC : Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst z)
    fC = fiber (fst C) mz
    i : Ix
    i = fD .fst , fC .fst
    pa : fst (pw i) ≡ pr (fst x) (fst z)
    pa = prʟ-fst (toD (fD .fst)) (toC (fC .fst))
       ∙ cong₂ pr (fD .snd) (fC .snd)
```

A bounded relation uses the same separation and pair-injectivity proof for
products, orders, and counting graphs. Its description reads over `(y, x, e)`;
the host predicate depends only on the two components.

```agda
module Relation (D C : S) (φ : Formula S 3) (P : S → S → hProp (ℓ-suc ℓ))
                (read : (x y e : S) → ⟨ (y ∷ x ∷ e ∷ []) ⊨ φ ⟩ → ⟨ P x y ⟩)
                (fill : (x y e : S) → ⟨ P x y ⟩ → ⟨ (y ∷ x ∷ e ∷ []) ⊨ φ ⟩) where

  opaque
    fo : Formula S 1
    fo = ∃̇ (∃̇ (prAtL (suc (suc zero)) (suc zero) zero ∧̇ φ))

    rel : S
    rel = hasSeparationL (PairBound.bnd D C) fo .fst .fst

    out : (e : S) → ⟨ fst e ∈ fst rel ⟩
        → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ] ((fst e ≡ pr (fst x) (fst y)) × ⟨ P x y ⟩) ∥₁
    out e h = PT.rec squash₁ (λ { (x , hx) → PT.map
      (λ { (y , q , hy) → x , y
         , subst ⟨_⟩ (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ e ∷ [])) q
         , read x y e hy }) hx })
      (subst ⟨_⟩ (hasSeparationL (PairBound.bnd D C) fo .fst .snd e) h .snd)

    into : (x y : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst y ∈ fst C ⟩ → ⟨ P x y ⟩
         → ⟨ pr (fst x) (fst y) ∈ fst rel ⟩
    into x y mx my h = subst (λ w → ⟨ w ∈ fst rel ⟩) (prʟ-fst x y)
      (subst ⟨_⟩ (sym (hasSeparationL (PairBound.bnd D C) fo .fst .snd (prʟ x y)))
        ( subst (λ w → ⟨ w ∈ fst (PairBound.bnd D C) ⟩) (sym (prʟ-fst x y))
            (PairBound.below D C x y mx my)
        , ∣ x , ∣ y
          , subst ⟨_⟩ (sym (prAtL-adequate (suc (suc zero)) (suc zero) zero (y ∷ x ∷ prʟ x y ∷ [])))
              (prʟ-fst x y)
          , fill x y (prʟ x y) h ∣₁ ∣₁ ))

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst rel ⟩ → ⟨ P x y ⟩
  pair-out x y h = PT.rec (snd (P x y))
    (λ { (x' , y' , q , h') →
      subst2 (λ a b → ⟨ P a b ⟩)
        (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj (sym (prʟ-fst x y) ∙ q) .fst)))
        (Σ≡Prop (λ v → snd (isL v)) (sym (pr-inj (sym (prʟ-fst x y) ∙ q) .snd))) h' })
    (out (prʟ x y) (subst (λ w → ⟨ w ∈ fst rel ⟩) (sym (prʟ-fst x y)) h))
```

The composite. Two graphs, four conjuncts each, not one replacement.

```agda
module Comp (D E C F H : S)
            (svF : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
            (dmF : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijF : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
            (ranF : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst E ⟩)
            (svH : ⟨ (H ∷ E ∷ []) ⊨ svAt zero ⟩)
            (dmH : ⟨ (H ∷ E ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijH : ⟨ (H ∷ E ∷ []) ⊨ injAt zero ⟩)
            (ranH : (y z : S) → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
                  → ⟨ fst z ∈ fst C ⟩) where

  private
    γF : S ^ 2
    γF = F ∷ D ∷ []

    γH : S ^ 2
    γH = H ∷ E ∷ []
```

The composite condition has one intermediate witness. Its two readings only
interpret the two application atoms; `Relation` supplies the pair graph.

```agda
  private
    Chain : S → S → Type (ℓ-suc ℓ)
    Chain x z = ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                             × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁

    opaque
      body : Formula S 3
      body = ∃̇ (appC F (suc (suc zero)) zero ∧̇ appC H zero (suc zero))

      read : (x z p : S) → ⟨ (z ∷ x ∷ p ∷ []) ⊨ body ⟩ → Chain x z
      read x z p = PT.map (λ { (y , hf , hh) → y
        , subst ⟨_⟩ (appC-adequate F (suc (suc zero)) zero (y ∷ z ∷ x ∷ p ∷ [])) hf
        , subst ⟨_⟩ (appC-adequate H zero (suc zero) (y ∷ z ∷ x ∷ p ∷ [])) hh })

      fill : (x z p : S) → Chain x z → ⟨ (z ∷ x ∷ p ∷ []) ⊨ body ⟩
      fill x z p = PT.map (λ { (y , hf , hh) → y
        , subst ⟨_⟩ (sym (appC-adequate F (suc (suc zero)) zero (y ∷ z ∷ x ∷ p ∷ []))) hf
        , subst ⟨_⟩ (sym (appC-adequate H zero (suc zero) (y ∷ z ∷ x ∷ p ∷ []))) hh })

    module Composite = Relation D C body (λ x z → Chain x z , squash₁) read fill

  K : S
  K = Composite.rel

  K-out : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
        → ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                      × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁
  K-out = Composite.pair-out

  K-in : (x y z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
       → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
       → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
  K-in x y z mx mz hf hh = Composite.into x z mx mz ∣ y , hf , hh ∣₁
```

The four conjuncts, for the composite.

```agda
  γK : S ^ 2
  γK = K ∷ D ∷ []

  svK : ⟨ γK ⊨ svAt zero ⟩
  svK = svAt-in zero γK (λ x y y' p q →
    PT.rec (setIsSet (fst y) (fst y'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst y) (fst y'))
        (λ { (w' , (hf' , hh')) →
          svAt-out zero γH svH w y y' hh
            (subst (λ t → ⟨ pr t (fst y') ∈ fst H ⟩)
              (sym (svAt-out zero γF svF x w w' hf hf')) hh') })
        (K-out x y' q) })
      (K-out x y p))

  ijK : ⟨ γK ⊨ injAt zero ⟩
  ijK = injAt-in zero γK (λ y x x' p q →
    PT.rec (setIsSet (fst x) (fst x'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst x) (fst x'))
        (λ { (w' , (hf' , hh')) →
          injAt-out zero γF ijF w x x' hf
            (subst (λ t → ⟨ pr (fst x') t ∈ fst F ⟩)
              (sym (injAt-out zero γH ijH y w w' hh hh')) hf') })
        (K-out x' y q) })
      (K-out x y p))

  dmK : ⟨ γK ⊨ domAt zero (suc zero) ⟩
  dmK = domAt-intro zero (suc zero) γK (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
        (λ { (w , (hf , _)) → domAt-out zero (suc zero) γF dmF x w hf })
        (K-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
    bwd x mx = PT.rec squash₁
      (λ { (w , hf) → PT.rec squash₁
        (λ { (z , hh) → ∣ z , K-in x w z mx (ranH w z hh) hf hh ∣₁ })
        (domAt-in zero (suc zero) γH dmH w (ranF x w hf)) })
      (domAt-in zero (suc zero) γF dmF x mx)

  ranK : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩ → ⟨ fst z ∈ fst C ⟩
  ranK x z h = PT.rec (snd (fst z ∈ fst C))
    (λ { (w , (_ , hh)) → ranH w z hh }) (K-out x z h)
```

The composite, read back as an honest function. Sealed.

```agda
  private
    module Sm = Small K D C svK dmK ijK ranK
```

Row 3. The inclusion of one set into another.

The identity function on the domain has the graph formula `y = x`. The shared
definable-injection construction collects its argument-value pairs and supplies
the four coded-injection conjuncts. Equality gives uniqueness and injectivity;
the given subset inclusion supplies the range proof.

```agda
module InclGraph (D C : S)
                 (sub : (z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩) where

  private
    M : DefinableMap
    M = record
      { dom = D ; cod = C
      ; fn = λ x _ → x
      ; into = λ x mx → sub (fst x) mx
      ; graph = var zero ≐ var (suc zero)
      ; defines = λ _ _ → refl
      ; only = λ _ _ _ h → Σ≡Prop (λ w → snd (isL w)) h }

    module I = DefinableInj M (λ _ _ _ _ e → e)
      using ( F; code )

  opaque
    G : S
    G = I.F

```

The shared construction packages the opaque graph with its four injection
conjuncts. The small presentation consumes that package without exposing the
replacement graph.

```agda
  opaque
    unfolding G
    code : InjCode G D C
    code = I.code
```

The small presentation reads the same identity graph. The value remains sealed:
an unsealed `Small` application at this site previously exhausted an 8g heap.

```agda
  private
    module Sm = Small G D C (code .fst) (code .snd .fst)
      (code .snd .snd .fst) (code .snd .snd .snd)

  opaque
    incl : ⟪ fst D ⟫ → ⟪ fst C ⟫
    incl = Sm.small
```

The ordinal inclusion, which is A5's row-3 object. The module is generic in the
ordinal: nothing below names a stage, a numeral or `ω`. The ordinal supplies the
subset witness through its own transitivity, and that is all it supplies.

```agda
module OrdIncl (C : S) (oC : IsOrd (fst C))
               (D : S) (D∈C : ⟨ fst D ∈ fst C ⟩) where

  open InclGraph D C (λ _ z∈D → oC .fst z∈D D∈C) public
```
