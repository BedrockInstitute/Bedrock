# The satisfaction table: the frame, the clauses and their readers

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Clauses {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊤̇; ⊥̇; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using
  ( checkΔ₀; Δ₀; δ-∧; δ-⇒; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Base {ℓ} using ( Δ₀-prAt; ∈pair-introL; ∈pair-introR )
open import L.Coding.Environment {ℓ} using ( Δ₀-sucAt; env; cons; lookup-spec )
open import L.Axioms.Numerals {ℓ} using ( numeralL-fst; sucʟ; sucʟ-fst )
open import L.Coding.Model {ℓ} using
  ( prAtL; appAt; appAt-adequate; sucAtL; sucAtL-adequate
  ; consAtL; consAtL-adequate; numL )
open import L.Coding.Model {ℓ} using ( Container; container ) public
import L.Coding.Model {ℓ} as CodingModel
module E = CodingModel.PairExpression
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Coding.Tower {ℓ} lem using
  ( module Tower; i0; i1; i2; i3; pr-out; pr-in; down ) public

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Slot arithmetic. `sh k` pushes an outer slot past `k` binders; the names `i0` ..
`i11` are the innermost slots at any arity.

```agda
sh : ∀ {m} (k : ℕ) → Fin m → Fin (k + m)
sh zero i = i
sh (suc k) i = suc (sh k i)

i4 : ∀ {j} → Fin (5 + j)
i4 = suc i3
i5 : ∀ {j} → Fin (6 + j)
i5 = suc i4
i6 : ∀ {j} → Fin (7 + j)
i6 = suc i5
i7 : ∀ {j} → Fin (8 + j)
i7 = suc i6
i8 : ∀ {j} → Fin (9 + j)
i8 = suc i7
i9 : ∀ {j} → Fin (10 + j)
i9 = suc i8
i10 : ∀ {j} → Fin (11 + j)
i10 = suc i9
i11 : ∀ {j} → Fin (12 + j)
i11 = suc i10
i12 : ∀ {j} → Fin (13 + j)
i12 = suc i11
i13 : ∀ {j} → Fin (14 + j)
i13 = suc i12
i14 : ∀ {j} → Fin (15 + j)
i14 = suc i13
i15 : ∀ {j} → Fin (16 + j)
i15 = suc i14
i16 : ∀ {j} → Fin (17 + j)
i16 = suc i15
i17 : ∀ {j} → Fin (18 + j)
i17 = suc i16
i18 : ∀ {j} → Fin (19 + j)
i18 = suc i17
i19 : ∀ {j} → Fin (20 + j)
i19 = suc i18
```

The atoms and their certificates.

```agda
Δ₀-prAtL : ∀ {m} (q u v : Fin m) → Δ₀ (prAtL q u v)
Δ₀-prAtL q u v = Δ₀-liftFo _ (Δ₀-prAt q u v)

Δ₀-sucAtL : ∀ {m} (i j : Fin m) → Δ₀ (sucAtL i j)
Δ₀-sucAtL i j = Δ₀-liftFo _ (Δ₀-sucAt i j)
```

The successor reader, both ways, at a variable environment.

```agda
suc-out : ∀ {m} (i j : Fin m) (γ : S ^ m) → ⟨ γ ⊨ sucAtL i j ⟩
        → fst (lookup j γ) ≡ sucV (fst (lookup i γ))
suc-out i j γ h = subst ⟨_⟩ (sucAtL-adequate i j γ) h

suc-in : ∀ {m} (i j : Fin m) (γ : S ^ m)
       → fst (lookup j γ) ≡ sucV (fst (lookup i γ)) → ⟨ γ ⊨ sucAtL i j ⟩
suc-in i j γ e = subst ⟨_⟩ (sym (sucAtL-adequate i j γ)) e
```

The pair as a container. Both components of `pr u v` lie in the member
`⁅ u , v ⁆` of it. This is what lets a Δ₀ formula bind the components of a pair
it holds, with no ambient bound at all.

The opaque pair container is supplied by `L.Coding.Model` and shared with
its structural pair-expression reader.

The destructors. Four macros bind the components of a pair held at a slot: the
second component alone (the first is a slot already), or both, each under an
existential or a universal. The body sits at `v ∷ s ∷ γ`, or at
`v ∷ u ∷ s ∷ γ`, with `s` the container. Every reader is at a variable
environment; the container is junk the reader supplies.

```agda
sndEx : ∀ {m} → Fin m → Fin m → Formula S (2 + m) → Formula S m
sndEx x u body =
  ∃̇∈ (var x) (∃̇∈ (var i0) (prAtL (sh 2 x) (sh 2 u) i0 ∧̇ body))

sndAll : ∀ {m} → Fin m → Fin m → Formula S (2 + m) → Formula S m
sndAll x u body =
  ∀̇∈ (var x) (∀̇∈ (var i0) (prAtL (sh 2 x) (sh 2 u) i0 ⇒̇ body))

bothEx : ∀ {m} → Fin m → Formula S (3 + m) → Formula S m
bothEx x body =
  ∃̇∈ (var x) (∃̇∈ (var i0) (∃̇∈ (var i1) (prAtL (sh 3 x) i1 i0 ∧̇ body)))

bothAll : ∀ {m} → Fin m → Formula S (3 + m) → Formula S m
bothAll x body =
  ∀̇∈ (var x) (∀̇∈ (var i0) (∀̇∈ (var i1) (prAtL (sh 3 x) i1 i0 ⇒̇ body)))

Δ₀-sndEx : ∀ {m} (x u : Fin m) (body : Formula S (2 + m)) → Δ₀ body → Δ₀ (sndEx x u body)
Δ₀-sndEx x u body d = δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL (sh 2 x) (sh 2 u) i0) d))

Δ₀-sndAll : ∀ {m} (x u : Fin m) (body : Formula S (2 + m)) → Δ₀ body → Δ₀ (sndAll x u body)
Δ₀-sndAll x u body d = δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-prAtL (sh 2 x) (sh 2 u) i0) d))

Δ₀-bothAll : ∀ {m} (x : Fin m) (body : Formula S (3 + m)) → Δ₀ body → Δ₀ (bothAll x body)
Δ₀-bothAll x body d = δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-prAtL (sh 3 x) i1 i0) d)))

module _ {m : ℕ} (x u : Fin m) (body : Formula S (2 + m)) (γ : S ^ m) where
  private
    X = fst (lookup x γ)
    U = fst (lookup u γ)
```

Out: the witness's second component is pinned by pair injectivity.

```agda
  sndEx-out : ⟨ γ ⊨ sndEx x u body ⟩
            → ∥ Σ[ v ∈ S ] Σ[ s ∈ S ] ((X ≡ pr U (fst v)) × ⟨ (v ∷ s ∷ γ) ⊨ body ⟩) ∥₁
  sndEx-out = PT.rec squash₁ (λ { (s , (s∈ , h)) → PT.map
    (λ { (v , (v∈ , (e , hb))) → v , s , (pr-out (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e , hb) })
    h })

  sndEx-in : (v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst v ∈ fst s ⟩ → X ≡ pr U (fst v)
           → ⟨ (v ∷ s ∷ γ) ⊨ body ⟩ → ⟨ γ ⊨ sndEx x u body ⟩
  sndEx-in v s s∈ v∈ e hb = ∣ s , (s∈ , ∣ v , (v∈ , (pr-in (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e , hb)) ∣₁) ∣₁

  sndAll-out : ⟨ γ ⊨ sndAll x u body ⟩
             → (v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst v ∈ fst s ⟩ → X ≡ pr U (fst v)
             → ⟨ (v ∷ s ∷ γ) ⊨ body ⟩
  sndAll-out h v s s∈ v∈ e = h s s∈ v v∈ (pr-in (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e)

  sndAll-in : ((v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst v ∈ fst s ⟩ → X ≡ pr U (fst v)
               → ⟨ (v ∷ s ∷ γ) ⊨ body ⟩)
            → ⟨ γ ⊨ sndAll x u body ⟩
  sndAll-in k s s∈ v v∈ e = k v s s∈ v∈ (pr-out (sh 2 x) (sh 2 u) i0 (v ∷ s ∷ γ) e)

module _ {m : ℕ} (x : Fin m) (body : Formula S (3 + m)) (γ : S ^ m) where
  private
    X = fst (lookup x γ)

  bothEx-out : ⟨ γ ⊨ bothEx x body ⟩
             → ∥ Σ[ u ∈ S ] Σ[ v ∈ S ] Σ[ s ∈ S ]
                 ((X ≡ pr (fst u) (fst v)) × ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩) ∥₁
  bothEx-out = PT.rec squash₁ (λ { (s , (s∈ , h)) → PT.rec squash₁
    (λ { (u , (u∈ , h')) → PT.map
      (λ { (v , (v∈ , (e , hb))) → u , v , s , (pr-out (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e , hb) })
      h' })
    h })

  bothEx-in : (u v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst u ∈ fst s ⟩ → ⟨ fst v ∈ fst s ⟩
            → X ≡ pr (fst u) (fst v) → ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩ → ⟨ γ ⊨ bothEx x body ⟩
  bothEx-in u v s s∈ u∈ v∈ e hb =
    ∣ s , (s∈ , ∣ u , (u∈ , ∣ v , (v∈ , (pr-in (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e , hb)) ∣₁) ∣₁) ∣₁

  bothAll-out : ⟨ γ ⊨ bothAll x body ⟩
              → (u v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst u ∈ fst s ⟩ → ⟨ fst v ∈ fst s ⟩
              → X ≡ pr (fst u) (fst v) → ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩
  bothAll-out h u v s s∈ u∈ v∈ e = h s s∈ u u∈ v v∈ (pr-in (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e)

  bothAll-in : ((u v s : S) → ⟨ fst s ∈ X ⟩ → ⟨ fst u ∈ fst s ⟩ → ⟨ fst v ∈ fst s ⟩
                → X ≡ pr (fst u) (fst v) → ⟨ (v ∷ u ∷ s ∷ γ) ⊨ body ⟩)
             → ⟨ γ ⊨ bothAll x body ⟩
  bothAll-in k s s∈ u u∈ v v∈ e = k u v s s∈ u∈ v∈ (pr-out (sh 3 x) i1 i0 (v ∷ u ∷ s ∷ γ) e)
```

Supplying the junk: a pair at a slot, with its components as
elements, fills any of the four.

```agda
module _ {m : ℕ} (x : Fin m) (γ : S ^ m) (u v : S)
         (e : fst (lookup x γ) ≡ pr (fst u) (fst v)) where
  private
    c = container (lookup x γ) u v e

  fillSnd : (body : Formula S (2 + m)) → ⟨ (v ∷ c .fst ∷ γ) ⊨ body ⟩
          → (ui : Fin m) → fst (lookup ui γ) ≡ fst u → ⟨ γ ⊨ sndEx x ui body ⟩
  fillSnd body hb ui qu = sndEx-in x ui body γ v (c .fst) (c .snd .fst) (c .snd .snd .snd)
    (e ∙ cong (λ w → pr w (fst v)) (sym qu)) hb

  fillBoth : (body : Formula S (3 + m)) → ⟨ (v ∷ u ∷ c .fst ∷ γ) ⊨ body ⟩
           → ⟨ γ ⊨ bothEx x body ⟩
  fillBoth body hb = bothEx-in x body γ u v (c .fst) (c .snd .fst) (c .snd .snd .fst)
    (c .snd .snd .snd) e hb

  useSnd : (body : Formula S (2 + m)) (ui : Fin m) → fst (lookup ui γ) ≡ fst u
         → ⟨ γ ⊨ sndAll x ui body ⟩ → ⟨ (v ∷ c .fst ∷ γ) ⊨ body ⟩
  useSnd body ui qu h = sndAll-out x ui body γ h v (c .fst) (c .snd .fst) (c .snd .snd .snd)
    (e ∙ cong (λ w → pr w (fst v)) (sym qu))

  useBoth : (body : Formula S (3 + m)) → ⟨ γ ⊨ bothAll x body ⟩
          → ⟨ (v ∷ u ∷ c .fst ∷ γ) ⊨ body ⟩
  useBoth body h = bothAll-out x body γ h u v (c .fst) (c .snd .fst) (c .snd .snd .fst)
    (c .snd .snd .snd) e
```

The environment tower. `E` is the set of pairs `(n, Eₙ)`, `Eₙ` the set of
environments of arity `n` over `w`, generated by cons from `∅`: `(0, ⁅∅⁆)` is an
entry; above every entry sits its successor entry, holding exactly the
extensions of its members by members of `w`; and every entry is the base or sits
above another. The last clause is what `∈`-induction on the arity reads; the
second is what `ℕ`-induction produces. Both are Δ₀ because a pair holds its
components.

```agda
emptyAll : ∀ {m} → Fin m → Formula S m
emptyAll x = ∀̇∈ (var x) ⊥̇
```

`F = ⁅ ∅ ⁆`: a member with no members, and every member has none.

```agda
sglEmpty : ∀ {m} → Fin m → Formula S m
sglEmpty F = ∃̇∈ (var F) (emptyAll i0) ∧̇ ∀̇∈ (var F) (emptyAll i0)
```

`F'` is the set of extensions of the members of `F` by members of `w`.

```agda
consImage : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
consImage F' F w =
    ∀̇∈ (var F') (∃̇∈ (var (sh 1 w)) (∃̇∈ (var (sh 2 F)) (consAtL i2 i1 i0)))
  ∧̇ ∀̇∈ (var F) (∀̇∈ (var (sh 1 w)) (∃̇∈ (var (sh 2 F')) (consAtL i0 i1 i2)))
```

At `F ∷ n ∷ s ∷ p ∷ γ`, the entry `p = (n, F)` is being read.

```agda
private
  upBody downBody : ∀ {m} → Fin m → Formula S (8 + m)
  upBody w = sucAtL i5 i1 ∧̇ consImage i0 i4 (sh 8 w)
  downBody w = sucAtL i1 i5 ∧̇ consImage i4 i0 (sh 8 w)

  towerUp : ∀ {m} → Fin m → Fin m → Formula S (4 + m)
  towerUp E w = ∃̇∈ (var (sh 4 E)) (bothEx i0 (upBody w))

  towerDown : ∀ {m} → Fin m → Fin m → Fin m → Formula S (4 + m)
  towerDown E w N0 =
      ((var i1 ≐ var (sh 4 N0)) ∧̇ sglEmpty i0)
    ∨̇ ∃̇∈ (var (sh 4 E)) (bothEx i0 (downBody w))

towerAt : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
towerAt E w N0 =
    ∃̇∈ (var E) (sndEx i0 (sh 1 N0) (sglEmpty i0))
  ∧̇ ( ∀̇∈ (var E) (bothAll i0 (towerUp E w))
    ∧̇ ∀̇∈ (var E) (bothAll i0 (towerDown E w N0)) )
```

<!--en-->
Every quantifier in this description has a bound. The sound boundedness checker
reads the constructed formula and supplies its Δ₀ witness; the same check will
certify the descriptions of codes and tables below.
<!--zh-->
这个描述中的每个量词都有界。已证明可靠的有界性检查器读取构造出的公式，给出它的 Δ₀ 见证；下面对码与表的描述也由同一检查给出证书。
<!--/-->

```agda
Δ₀-towerAt : ∀ {m} (E w N0 : Fin m) → Δ₀ (towerAt E w N0)
Δ₀-towerAt E w N0 = checkΔ₀ (towerAt E w N0) tt
```

What the environment sets are. Three facts about
src/L/Coding/EnvSet.lagda.md `envSet`: at arity 0 it is `⁅ ∅ ⁆`, and at a
successor arity it is the cons image of the arity below.

```agda
open import L.Coding.EnvSet {ℓ} lem using ( envSet; envSet-in; envSet-out; envS; Ix )
open import V.Model {ℓ} using ( self∈sucV )
open import Cubical.Data.FinData using ( toℕ )

module EnvFacts (W : S) where
  private
    ι : ⟪ fst W ⟫ → V ℓ
    ι = ⟪ fst W ⟫↪

    ι∈ : (q : ⟪ fst W ⟫) → ⟨ ι q ∈ fst W ⟩
    ι∈ q = ∈∈ₛ {a = ι q} {b = fst W} .snd (∈ₛ⟪ fst W ⟫↪ q)

    g0 : Ix W 0
    g0 ()
```

An empty set is the empty environment.

```agda
  noMembers→env0 : (z : V ℓ) → ((y : V ℓ) → ⟨ y ∈ z ⟩ → Empty.⊥) → z ≡ fst (envS W g0)
  noMembers→env0 z k = extensionalV (λ y → ⇔toPath
    (λ hy → Empty.rec (k y hy))
    (PT.rec (snd (y ∈ z)) (λ { (lift () , _) })))

  envAny0-noMembers : (g : Ix W 0) (y : V ℓ) → ⟨ y ∈ fst (envS W g) ⟩ → Empty.⊥
  envAny0-noMembers g y = PT.rec Empty.isProp⊥ (λ { (lift () , _) })

  envSet0-out : (z : V ℓ) → ⟨ z ∈ fst (envSet W 0) ⟩
              → (y : V ℓ) → ⟨ y ∈ z ⟩ → Empty.⊥
  envSet0-out z hz y hy = PT.rec Empty.isProp⊥
    (λ { (g , e) → envAny0-noMembers g y (subst (λ u → ⟨ y ∈ u ⟩) e hy) })
    (envSet-out W 0 (down (envSet W 0) z hz) hz)

  envSet0-in : (z : V ℓ) → ((y : V ℓ) → ⟨ y ∈ z ⟩ → Empty.⊥) → ⟨ z ∈ fst (envSet W 0) ⟩
  envSet0-in z k = subst (λ u → ⟨ u ∈ fst (envSet W 0) ⟩) (sym (noMembers→env0 z k)) (envSet-in W g0)
```

The cons of a member onto an environment is an environment.

```agda
  cons-env : (q : ⟪ fst W ⟫) {k : ℕ} (g : Ix W k)
           → env (cons (ι q) (λ i → ι (g i))) ≡ fst (envS W (cons q g))
  cons-env q g = cong env (funExt (λ { zero → refl ; (suc i) → refl }))

  envCons∈ : {k : ℕ} (x : V ℓ) → ⟨ x ∈ fst W ⟩ → (g : Ix W k)
           → ⟨ env (cons x (λ i → ι (g i))) ∈ fst (envSet W (suc k)) ⟩
  envCons∈ {k} x x∈ g =
    subst (λ u → ⟨ u ∈ fst (envSet W (suc k)) ⟩)
      (sym (cong (λ v → env (cons v (λ i → ι (g i)))) (sym (fib .snd)) ∙ cons-env (fib .fst) g))
      (envSet-in W (cons (fib .fst) g))
    where
    fib : Σ[ q ∈ ⟪ fst W ⟫ ] (ι q ≡ x)
    fib = ∈-asFiber {a = x} {b = fst W} x∈

  envSuc-in : {k : ℕ} (x e' : S) → ⟨ fst x ∈ fst W ⟩ → (g : Ix W k)
            → fst e' ≡ env (cons (fst x) (λ i → ι (g i)))
            → ⟨ fst e' ∈ fst (envSet W (suc k)) ⟩
  envSuc-in {k} x e' x∈ g qe' =
    subst (λ u → ⟨ u ∈ fst (envSet W (suc k)) ⟩) (sym qe') (envCons∈ (fst x) x∈ g)
```

An environment at a successor arity splits as a cons.

```agda
  env-split : {k : ℕ} (g' : Ix W (suc k))
            → fst (envS W g') ≡ env (cons (ι (g' zero)) (λ i → ι (g' (suc i))))
  env-split g' = cong env (funExt (λ { zero → refl ; (suc i) → refl }))
```

A member of the successor set is a cons.

```agda
  envSuc-out : {k : ℕ} (e' : S) → ⟨ fst e' ∈ fst (envSet W (suc k)) ⟩
             → ∥ Σ[ q ∈ ⟪ fst W ⟫ ] Σ[ g ∈ Ix W k ]
                  (fst e' ≡ env (cons (ι q) (λ i → ι (g i)))) ∥₁
  envSuc-out {k} e' h = PT.map
    (λ { (g' , e) → g' zero , (λ i → g' (suc i)) , (e ∙ env-split g') })
    (envSet-out W (suc k) e' h)
```

The tower, read. Soundness: every entry is `(# k, envSet k)`, by `∈`-induction
on the arity component; and every `(# k, envSet k)` is an entry, by
`ℕ`-induction. Completeness: the tower set of the next section satisfies the
description.

```agda
module ConsImageRead {m : ℕ} (F' F w : Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) where
  open EnvFacts W
  private
    ι : ⟪ fst W ⟫ → V ℓ
    ι = ⟪ fst W ⟫↪

    ι∈' : (q : ⟪ fst W ⟫) → ⟨ ι q ∈ fst W ⟩
    ι∈' q = ∈∈ₛ {a = ι q} {b = fst W} .snd (∈ₛ⟪ fst W ⟫↪ q)
```

Out: the members of `F'` are exactly the cons of members of `w` onto members of
`F`, so at `F = envSet k`, `F' = envSet (suc k)`.

```agda
  consImage-out : (k : ℕ) → fst (lookup F γ) ≡ fst (envSet W k)
                → ⟨ γ ⊨ consImage F' F w ⟩ → fst (lookup F' γ) ≡ fst (envSet W (suc k))
  consImage-out k qF (h1 , h2) = extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : V ℓ) → ⟨ z ∈ fst (lookup F' γ) ⟩ → ⟨ z ∈ fst (envSet W (suc k)) ⟩
    fwd z hz = PT.rec (snd (z ∈ fst (envSet W (suc k))))
      (λ { (x , (x∈ , hx)) → PT.rec (snd (z ∈ fst (envSet W (suc k))))
        (λ { (e , (e∈ , hc)) → PT.rec (snd (z ∈ fst (envSet W (suc k))))
          (λ { (g , qe) →
            envSuc-in x zS (subst (λ u → ⟨ fst x ∈ u ⟩) qw x∈) g
              (subst ⟨_⟩ (consAtL-adequate i2 i1 i0 (e ∷ x ∷ zS ∷ γ) (λ i → ι (g i)) qe) hc) })
          (envSet-out W k e (subst (λ u → ⟨ fst e ∈ u ⟩) qF e∈)) })
        hx })
      (h1 zS hz)
      where
      zS : S
      zS = down (lookup F' γ) z hz

    bwd : (z : V ℓ) → ⟨ z ∈ fst (envSet W (suc k)) ⟩ → ⟨ z ∈ fst (lookup F' γ) ⟩
    bwd z hz = PT.rec (snd (z ∈ fst (lookup F' γ)))
      (λ { (q , g , qz) → PT.rec (snd (z ∈ fst (lookup F' γ)))
        (λ { (e' , (e'∈ , hc)) →
          subst (λ u → ⟨ u ∈ fst (lookup F' γ) ⟩)
            (subst ⟨_⟩ (consAtL-adequate i0 i1 i2 (e' ∷ xS q ∷ envS W g ∷ γ) (λ i → ι (g i)) refl) hc
             ∙ sym qz)
            e'∈ })
        (h2 (envS W g) (subst (λ u → ⟨ fst (envS W g) ∈ u ⟩) (sym qF) (envSet-in W g))
            (xS q) (subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈' q))) })
      (envSuc-out zS hz)
      where
      zS : S
      zS = down (envSet W (suc k)) z hz
      xS : ⟪ fst W ⟫ → S
      xS q = ι q , isL-trans {x = fst W} {y = ι q} (ι∈' q) (snd W)

  consImage-in : (k : ℕ) → fst (lookup F γ) ≡ fst (envSet W k)
               → fst (lookup F' γ) ≡ fst (envSet W (suc k))
               → ⟨ γ ⊨ consImage F' F w ⟩
  consImage-in k qF qF' = h1 , h2
    where
    h1 : (e' : S) → ⟨ fst e' ∈ fst (lookup F' γ) ⟩
       → ⟨ (e' ∷ γ) ⊨ ∃̇∈ (var (sh 1 w)) (∃̇∈ (var (sh 2 F)) (consAtL i2 i1 i0)) ⟩
    h1 e' he' = PT.map
      (λ { (q , g , qe') →
        let xS : S
            xS = ι q , isL-trans {x = fst W} {y = ι q} (ι∈' q) (snd W)
        in xS , ( subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈' q)
              , ∣ envS W g , ( subst (λ u → ⟨ fst (envS W g) ∈ u ⟩) (sym qF) (envSet-in W g)
                             , subst ⟨_⟩ (sym (consAtL-adequate i2 i1 i0 (envS W g ∷ xS ∷ e' ∷ γ) (λ i → ι (g i)) refl)) qe' ) ∣₁ ) })
      (envSuc-out e' (subst (λ u → ⟨ fst e' ∈ u ⟩) qF' he'))

    h2 : (e : S) → ⟨ fst e ∈ fst (lookup F γ) ⟩ → (x : S) → ⟨ fst x ∈ fst (lookup w γ) ⟩
       → ⟨ (x ∷ e ∷ γ) ⊨ ∃̇∈ (var (sh 2 F')) (consAtL i0 i1 i2) ⟩
    h2 e he x hx = PT.map
      (λ { (g , qe) →
        let m : ⟨ env (cons (fst x) (λ i → ι (g i))) ∈ fst (envSet W (suc k)) ⟩
            m = envCons∈ (fst x) (subst (λ u → ⟨ fst x ∈ u ⟩) qw hx) g
            e' : S
            e' = down (envSet W (suc k)) (env (cons (fst x) (λ i → ι (g i)))) m
        in e' , ( subst (λ u → ⟨ fst e' ∈ u ⟩) (sym qF') m
                , subst ⟨_⟩ (sym (consAtL-adequate i0 i1 i2 (e' ∷ x ∷ e ∷ γ) (λ i → ι (g i)) qe)) refl ) })
      (envSet-out W k e (subst (λ u → ⟨ fst e ∈ u ⟩) qF he))
```

```agda
open import FOL.Syntax using ( ∃̇_; ∀̇_ )
```

The numeral `k`, as an element of L.

```agda
nn : ℕ → S
nn k = # k , numL k
```

The tower, read. Soundness by `∈`-induction on the arity component and
`ℕ`-induction on the arity; completeness at the tower set.

`⁅ ∅ ⁆` at a slot is the environment set of arity zero.

```agda
module SglEmpty (W : S) {m : ℕ} (F : Fin m) (γ : S ^ m) where
  open EnvFacts W

  sglEmpty-out : ⟨ γ ⊨ sglEmpty F ⟩ → fst (lookup F γ) ≡ fst (envSet W 0)
  sglEmpty-out (hex , hall) = extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
    where
    Fv = fst (lookup F γ)
    none : (z : S) → ⟨ (z ∷ γ) ⊨ emptyAll i0 ⟩ → (y : V ℓ) → ⟨ y ∈ fst z ⟩ → Empty.⊥
    none z k y hy = Empty.rec* (k (down z y hy) hy)

    fwd : (z : V ℓ) → ⟨ z ∈ Fv ⟩ → ⟨ z ∈ fst (envSet W 0) ⟩
    fwd z hz = envSet0-in z (none (down (lookup F γ) z hz) (hall (down (lookup F γ) z hz) hz))

    bwd : (z : V ℓ) → ⟨ z ∈ fst (envSet W 0) ⟩ → ⟨ z ∈ Fv ⟩
    bwd z hz = PT.rec (snd (z ∈ Fv))
      (λ { (e , (e∈ , he)) →
        subst (λ u → ⟨ u ∈ Fv ⟩)
          (noMembers→env0 (fst e) (none e he) ∙ sym (noMembers→env0 z (envSet0-out z hz)))
          e∈ })
      hex

  sglEmpty-in : fst (lookup F γ) ≡ fst (envSet W 0) → ⟨ γ ⊨ sglEmpty F ⟩
  sglEmpty-in q =
      ∣ e0 , ( subst (λ u → ⟨ fst e0 ∈ u ⟩) (sym q) (envSet-in W (λ ()))
             , (λ y hy → lift (envAny0-noMembers (λ ()) (fst y) hy)) ) ∣₁
    , (λ z hz y hy → lift (envSet0-out (fst z) (subst (λ u → ⟨ fst z ∈ u ⟩) q hz) (fst y) hy))
    where
    e0 : S
    e0 = envS W (λ ())

module TowerRead {m : ℕ} (E w N0 : Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qN0 : fst (lookup N0 γ) ≡ # 0)
  (h : ⟨ γ ⊨ towerAt E w N0 ⟩) where
  private
    Ev = fst (lookup E γ)
    hbase = h .fst
    hup = h .snd .fst
    hdown = h .snd .snd

  Entry : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Entry n F = ∥ Σ[ k ∈ ℕ ] ((n ≡ # k) × (F ≡ fst (envSet W k))) ∥₁
```

Every entry is `(# k, envSet k)`.

```agda
  entry-out : (n F : S) → ⟨ pr (fst n) (fst F) ∈ Ev ⟩ → Entry (fst n) (fst F)
  entry-out n F = ∈-induction {P = P} step (fst n) n F refl
    where
    P : V ℓ → Type (ℓ-suc ℓ)
    P nv = (n F : S) → fst n ≡ nv → ⟨ pr (fst n) (fst F) ∈ Ev ⟩ → Entry (fst n) (fst F)

    step : (nv : V ℓ) → ((y : V ℓ) → ⟨ y ∈ nv ⟩ → P y) → P nv
    step nv IH n F qn p∈ = PT.rec squash₁ cases
      (useBoth i0 (pS ∷ γ) n F refl (towerDown E w N0) (hdown pS p∈))
      where
      pS : S
      pS = down (lookup E γ) (pr (fst n) (fst F)) p∈
      c = container pS n F refl
      δ : S ^ (4 + m)
      δ = F ∷ n ∷ c .fst ∷ pS ∷ γ

      cases : ((fst n ≡ fst (lookup N0 γ)) × ⟨ δ ⊨ sglEmpty i0 ⟩)
            ⊎ ⟨ δ ⊨ ∃̇∈ (var (sh 4 E)) (bothEx i0 (downBody w)) ⟩
            → Entry (fst n) (fst F)
      cases (inl (qn0 , hF)) = ∣ 0 , (qn0 ∙ qN0 , SglEmpty.sglEmpty-out W i0 δ hF) ∣₁
      cases (inr hs) = PT.rec squash₁
        (λ { (p' , (p'∈ , hb)) → PT.rec squash₁
          (λ { (n' , F' , s' , (qp' , (hsuc , hci))) →
            let δ' = F' ∷ n' ∷ s' ∷ p' ∷ δ
                qsuc : fst n ≡ sucV (fst n')
                qsuc = suc-out i1 i5 δ' hsuc
                n'∈ : ⟨ fst n' ∈ nv ⟩
                n'∈ = subst (λ u → ⟨ fst n' ∈ u ⟩) (sym qsuc ∙ qn) (self∈sucV (fst n'))
            in PT.map
              (λ { (k , (qk , qF')) →
                suc k , ( qsuc ∙ cong sucV qk
                        , ConsImageRead.consImage-out i4 i0 (sh 8 w) δ' W qw k qF' hci ) })
              (IH (fst n') n'∈ n' F' refl
                (subst (λ u → ⟨ u ∈ Ev ⟩) qp' p'∈)) })
          (bothEx-out i0 (downBody w) (p' ∷ δ) hb) })
        hs
```

Every `(# k, envSet k)` is an entry.

```agda
  entry-in : (k : ℕ) → ⟨ pr (# k) (fst (envSet W k)) ∈ Ev ⟩
  entry-in zero = PT.rec (snd (pr (# 0) (fst (envSet W 0)) ∈ Ev))
    (λ { (p , (p∈ , hs)) → PT.rec (snd (pr (# 0) (fst (envSet W 0)) ∈ Ev))
      (λ { (F , s , (qp , hF)) →
        subst (λ u → ⟨ u ∈ Ev ⟩)
          (qp ∙ cong₂ pr qN0 (SglEmpty.sglEmpty-out W i0 (F ∷ s ∷ p ∷ γ) hF))
          p∈ })
      (sndEx-out i0 (sh 1 N0) (sglEmpty i0) (p ∷ γ) hs) })
    hbase
  entry-in (suc k) = PT.rec (snd (pr (# (suc k)) (fst (envSet W (suc k))) ∈ Ev))
    (λ { (p' , (p'∈ , hb)) → PT.rec (snd (pr (# (suc k)) (fst (envSet W (suc k))) ∈ Ev))
      (λ { (n' , F' , s' , (qp' , (hsuc , hci))) →
        let δ' = F' ∷ n' ∷ s' ∷ p' ∷ δ
        in subst (λ u → ⟨ u ∈ Ev ⟩)
             (qp' ∙ cong₂ pr (suc-out i5 i1 δ' hsuc)
                             (ConsImageRead.consImage-out i0 i4 (sh 8 w) δ' W qw k refl hci))
             p'∈ })
      (bothEx-out i0 (upBody w) (p' ∷ δ) hb) })
    (useBoth i0 (pS ∷ γ) (nn k) (envSet W k) refl (towerUp E w) (hup pS (entry-in k)))
    where
    pS : S
    pS = down (lookup E γ) (pr (# k) (fst (envSet W k))) (entry-in k)
    c = container pS (nn k) (envSet W k) refl
    δ : S ^ (4 + m)
    δ = envSet W k ∷ nn k ∷ c .fst ∷ pS ∷ γ

module TowerHolds {m : ℕ} (E w N0 : Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qE : fst (lookup E γ) ≡ fst (Tower.tower W))
  (qN0 : fst (lookup N0 γ) ≡ # 0) where
  private
    Ev = fst (lookup E γ)

    entry∈ : (k : ℕ) → ⟨ pr (# k) (fst (envSet W k)) ∈ Ev ⟩
    entry∈ k = subst (λ u → ⟨ pr (# k) (fst (envSet W k)) ∈ u ⟩) (sym qE) (Tower.tower-in′ W k)

    entryS : (k : ℕ) → S
    entryS k = down (lookup E γ) (pr (# k) (fst (envSet W k))) (entry∈ k)

    read : (p : S) → ⟨ fst p ∈ Ev ⟩ → ∥ Σ[ k ∈ ℕ ] (fst p ≡ pr (# k) (fst (envSet W k))) ∥₁
    read p p∈ = Tower.tower-out W p (subst (λ u → ⟨ fst p ∈ u ⟩) qE p∈)

  holds : ⟨ γ ⊨ towerAt E w N0 ⟩
  holds = hbase , (hup , hdown)
    where
    hbase : ⟨ γ ⊨ ∃̇∈ (var E) (sndEx i0 (sh 1 N0) (sglEmpty i0)) ⟩
    hbase = ∣ entryS 0 , ( entry∈ 0
      , fillSnd i0 (entryS 0 ∷ γ) (lookup N0 γ) (envSet W 0)
          (cong (λ a → pr a (fst (envSet W 0))) (sym qN0))
          (sglEmpty i0)
          (SglEmpty.sglEmpty-in W i0
            (envSet W 0 ∷ container (lookup i0 (entryS 0 ∷ γ)) (lookup N0 γ) (envSet W 0)
               (cong (λ a → pr a (fst (envSet W 0))) (sym qN0)) .fst ∷ entryS 0 ∷ γ) refl)
          (sh 1 N0) refl ) ∣₁

    hup : (p : S) → ⟨ fst p ∈ Ev ⟩ → ⟨ (p ∷ γ) ⊨ bothAll i0 (towerUp E w) ⟩
    hup p p∈ = bothAll-in i0 (towerUp E w) (p ∷ γ) (λ n F s s∈ n∈ F∈ e →
      PT.rec (snd ((F ∷ n ∷ s ∷ p ∷ γ) ⊨ towerUp E w))
        (λ { (k , qp) →
          let q = pr-inj (sym e ∙ qp)
              δ1 = entryS (suc k) ∷ F ∷ n ∷ s ∷ p ∷ γ
              c' = container (lookup i0 δ1) (nn (suc k)) (envSet W (suc k)) refl
              δ2 = envSet W (suc k) ∷ nn (suc k) ∷ c' .fst ∷ δ1
          in ∣ entryS (suc k) , ( entry∈ (suc k)
             , fillBoth i0 δ1 (nn (suc k)) (envSet W (suc k)) refl (upBody w)
                 ( suc-in i5 i1 δ2 (cong sucV (sym (q .fst)))
                 , ConsImageRead.consImage-in i0 i4 (sh 8 w) δ2 W qw k (q .snd) refl ) ) ∣₁ })
        (read p p∈))

    hdown : (p : S) → ⟨ fst p ∈ Ev ⟩ → ⟨ (p ∷ γ) ⊨ bothAll i0 (towerDown E w N0) ⟩
    hdown p p∈ = bothAll-in i0 (towerDown E w N0) (p ∷ γ) (λ n F s s∈ n∈ F∈ e →
      PT.rec (snd ((F ∷ n ∷ s ∷ p ∷ γ) ⊨ towerDown E w N0))
        (λ { (zero , qp) →
          let q = pr-inj (sym e ∙ qp)
          in ∣ inl (q .fst ∙ sym qN0 , SglEmpty.sglEmpty-in W i0 (F ∷ n ∷ s ∷ p ∷ γ) (q .snd)) ∣₁
           ; (suc j , qp) →
          let q = pr-inj (sym e ∙ qp)
              δ1 = entryS j ∷ F ∷ n ∷ s ∷ p ∷ γ
              c' = container (lookup i0 δ1) (nn j) (envSet W j) refl
              δ2 = envSet W j ∷ nn j ∷ c' .fst ∷ δ1
          in ∣ inr ∣ entryS j , ( entry∈ j
             , fillBoth i0 δ1 (nn j) (envSet W j) refl (downBody w)
                 ( suc-in i1 i5 δ2 (q .fst)
                 , ConsImageRead.consImage-in i4 i0 (sh 8 w) δ2 W qw j refl (q .snd) ) ) ∣₁ ∣₁ })
        (read p p∈))
```

The code set. `C` is the set of keys `(n, code)` of the formulas over `w` at
every arity. Two clauses in Devlin polarity: every member is a key of one of the
ten shapes, at an arity the tower holds, with its subkeys in `C` and its term
parts over `w` or the arity (soundness reads this by `∈`-induction); and `C` is
closed under the ten code-forming operations (completeness reads this by
induction on the formula).

A term code over the arity `ar` and the carrier `w`: `(N0, x)` with `x` in `w`,
or `(N1, i)` with `i` in `ar`.

```agda
isTm : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
isTm t ar w N0 N1 =
    sndEx t N0 (var i0 ∈̇ var (sh 2 w))
  ∨̇ sndEx t N1 (var i0 ∈̇ var (sh 2 ar))
```

`(suc ar, r)` is in `C`: some member of `C` is the pair of a successor of `ar`
with `r`.

```agda
keyUp : ∀ {m} → Fin m → Fin m → Fin m → Formula S m
keyUp C ar r =
  ∃̇∈ (var C) (∃̇∈ (var i0) (∃̇∈ (var i0)
    (prAtL i2 i0 (sh 3 r) ∧̇ sucAtL (sh 3 ar) i0)))
```

A key expression records the arity, tag and payload. Its bounded membership
reader and both semantic directions use the structural pair-expression proof.

```agda
keyExpr : ∀ {m} → Fin m → Fin m → E.Expr m → E.Expr m
keyExpr ar N p = E.pair (E.slot ar) (E.pair (E.slot N) p)

atomKeyExpr : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → E.Expr m
atomKeyExpr ar N Nx x Ny y = keyExpr ar N
  (E.pair (E.pair (E.slot Nx) (E.slot x))
    (E.pair (E.slot Ny) (E.slot y)))

bndKeyExpr : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → E.Expr m
bndKeyExpr ar N Nx x a = keyExpr ar N
  (E.pair (E.pair (E.slot Nx) (E.slot x)) (E.slot a))
```

The unary key `(ar, (N, a))` exists in `C`.

```agda
unKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula S m
unKey C ar N a = E.member (keyExpr ar N (E.slot a)) (var C)
```

The binary key `(ar, (N, (a, b)))`.

```agda
binKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
binKey C ar N a b = E.member (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C)
```

The atom key `(ar, (N, ((Nx, x), (Ny, y))))`.

```agda
atomKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
atomKey C ar N Nx x Ny y = E.member (atomKeyExpr ar N Nx x Ny y) (var C)
```

The bounded-quantifier key `(ar, (N, ((Nx, x), a)))`.

```agda
bndKey : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula S m
bndKey C ar N Nx x a = E.member (bndKeyExpr ar N Nx x a) (var C)
```

The tag slots, as one function from the ten tags. `f k` names the tag `k`;
`Tags γ N` says the slots hold the numerals.

```agda
pattern f0 = zero
pattern f1 = suc f0
pattern f2 = suc f1
pattern f3 = suc f2
pattern f4 = suc f3
pattern f5 = suc f4
pattern f6 = suc f5
pattern f7 = suc f6
pattern f8 = suc f7
pattern f9 = suc f8

Tags : ∀ {m} (γ : S ^ m) (N : Fin 10 → Fin m) → Type (ℓ-suc ℓ)
Tags γ N = (k : Fin 10) → fst (lookup (N k) γ) ≡ # (toℕ k)

shN : ∀ {m} (j : ℕ) → (Fin 10 → Fin m) → Fin 10 → Fin (j + m)
shN j N k = sh j (N k)
```

The chain over the tags. Every tag-indexed chain in this chapter is the same
fold of a family, right-nested with the last tag as its base, and its four
readers are the fold's introduction and elimination. Nothing here is
tag-specific.

```agda
bigOr bigAnd : ∀ {m} (n : ℕ) → (Fin (suc n) → Formula S m) → Formula S m
bigOr 0 φ = φ zero
bigOr (suc n) φ = φ zero ∨̇ bigOr n (λ k → φ (suc k))
bigAnd 0 φ = φ zero
bigAnd (suc n) φ = φ zero ∧̇ bigAnd n (λ k → φ (suc k))

module _ {m : ℕ} (γ : S ^ m) where
  bigOr-in : (n : ℕ) (φ : Fin (suc n) → Formula S m) (k : Fin (suc n))
           → ⟨ γ ⊨ φ k ⟩ → ⟨ γ ⊨ bigOr n φ ⟩
  bigOr-in 0 φ zero h = h
  bigOr-in (suc n) φ zero h = ∣ inl h ∣₁
  bigOr-in (suc n) φ (suc k) h = ∣ inr (bigOr-in n (λ j → φ (suc j)) k h) ∣₁

  bigOr-out : (n : ℕ) (φ : Fin (suc n) → Formula S m) → ⟨ γ ⊨ bigOr n φ ⟩
            → ∥ Σ[ k ∈ Fin (suc n) ] ⟨ γ ⊨ φ k ⟩ ∥₁
  bigOr-out 0 φ h = ∣ zero , h ∣₁
  bigOr-out (suc n) φ = PT.rec squash₁
    (λ { (inl h) → ∣ zero , h ∣₁
       ; (inr h) → PT.map (λ { (k , hk) → suc k , hk }) (bigOr-out n (λ j → φ (suc j)) h) })

  bigAnd-in : (n : ℕ) (φ : Fin (suc n) → Formula S m)
            → ((k : Fin (suc n)) → ⟨ γ ⊨ φ k ⟩) → ⟨ γ ⊨ bigAnd n φ ⟩
  bigAnd-in 0 φ h = h zero
  bigAnd-in (suc n) φ h = h zero , bigAnd-in n (λ j → φ (suc j)) (λ k → h (suc k))

  bigAnd-out : (n : ℕ) (φ : Fin (suc n) → Formula S m) → ⟨ γ ⊨ bigAnd n φ ⟩
             → (k : Fin (suc n)) → ⟨ γ ⊨ φ k ⟩
  bigAnd-out 0 φ h zero = h
  bigAnd-out (suc n) φ h zero = h .fst
  bigAnd-out (suc n) φ h (suc k) = bigAnd-out n (λ j → φ (suc j)) (h .snd) k
```

The shape clause. At `r ∷ s'' ∷ p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ` (9 + m): the
payload `r` of the tag `N`, with `ar` at `i5` and `c` at `i8`.

```agda
module Shape {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) where
  private
    C9 w9 : Fin (9 + m)
    C9 = sh 9 C
    w9 = sh 9 w

  atomPay binPay conPay quPay bqPay : Formula S (9 + m)
  atomPay = bothEx i0 (isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ isTm i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)))
  binPay  = bothEx i0 (appAt (sh 12 C) i8 i1 ∧̇ appAt (sh 12 C) i8 i0)
  conPay  = var i0 ≐ var (sh 9 (N f0))
  quPay   = keyUp C9 i5 i0
  bqPay   = bothEx i0 (isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ keyUp (sh 12 C) i8 i0)
```

The payload formula of each tag, by the tag's number.

```agda
  payN : ℕ → Formula S (9 + m)
  payN 0 = atomPay
  payN 1 = atomPay
  payN 2 = binPay
  payN 3 = binPay
  payN 4 = binPay
  payN 5 = conPay
  payN 6 = quPay
  payN 7 = quPay
  payN 8 = bqPay
  payN 9 = bqPay
  payN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = ⊥̇

  pay : Fin 10 → Formula S (9 + m)
  pay k = payN (toℕ k)
```

At `p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ` (7 + m): `p` is `(N k, r)` for one of the
ten tags, with `r`'s payload condition.

```agda
  at : Fin 10 → Formula S (7 + m)
  at k = sndEx i0 (sh 7 (N k)) (pay k)

  ten : Formula S (7 + m)
  ten = bigOr 9 at
```

Every member of `C` is a key: `∀ c ∈ C`, `∃ (ar, F) ∈ E`, `c = (ar, p)`, `p` one
of the ten.

```agda
shapeAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
shapeAt C w E N =
  ∀̇∈ (var C) (∃̇∈ (var (sh 1 E)) (bothEx i0 (sndEx i4 i1 (Shape.ten C w N))))
```

The closure clauses, each under `∀ (ar, F) ∈ E`, at `F ∷ ar ∷ s ∷ q ∷ γ`
(4 + m): `ar` at `i1`, `C` at `sh 4 C`, `w` at `sh 4 w`.

```agda
module Close {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) where
  private
    C4 w4 : Fin (4 + m)
    C4 = sh 4 C
    w4 = sh 4 w
```

`X` and `Y` are bounds at 4 + m and 5 + m: the carrier or the arity.

```agda
  atomClose : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m)) → Formula S (4 + m)
  atomClose k Nx Ny X Y =
    ∀̇∈ (var X) (∀̇∈ (var Y) (atomKey (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0))

  binClose : (k : Fin 10) → Formula S (4 + m)
  binClose k =
    ∀̇∈ (var C4) (sndAll i0 i2 (∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))))

  conClose : (k : Fin 10) → Formula S (4 + m)
  conClose k = unKey C4 i1 (sh 4 (N k)) (sh 4 (N f0))
```

At `a ∷ ar' ∷ s ∷ c₁ ∷ F ∷ ar ∷ s ∷ q ∷ γ` (8 + m): `ar` at `i5`, `ar'` at
`i1`.

```agda
  quClose : (k : Fin 10) → Formula S (4 + m)
  quClose k = ∀̇∈ (var C4) (bothAll i0 (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0))

  bqClose : (k Nx : Fin 10) (X : Fin (8 + m)) → Formula S (4 + m)
  bqClose k Nx X =
    ∀̇∈ (var C4) (bothAll i0 (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1)))
```

The eighteen instances: four term combinations for each atom, two for each
bounded quantifier.

```agda
  all : Formula S (4 + m)
  all =
      atomClose f0 f0 f0 w4 (sh 1 w4) ∧̇ (atomClose f0 f0 f1 w4 i2
    ∧̇ (atomClose f0 f1 f0 i1 (sh 1 w4) ∧̇ (atomClose f0 f1 f1 i1 i2
    ∧̇ (atomClose f1 f0 f0 w4 (sh 1 w4) ∧̇ (atomClose f1 f0 f1 w4 i2
    ∧̇ (atomClose f1 f1 f0 i1 (sh 1 w4) ∧̇ (atomClose f1 f1 f1 i1 i2
    ∧̇ (binClose f2 ∧̇ (binClose f3 ∧̇ (binClose f4
    ∧̇ (conClose f5 ∧̇ (quClose f6 ∧̇ (quClose f7
    ∧̇ (bqClose f8 f0 (sh 8 w) ∧̇ (bqClose f8 f1 i5
    ∧̇ (bqClose f9 f0 (sh 8 w) ∧̇ bqClose f9 f1 i5))))))))))))))))

closeAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
closeAt C w E N = ∀̇∈ (var E) (bothAll i0 (Close.all C w N))

codesAt : ∀ {m} → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
codesAt C w E N = shapeAt C w E N ∧̇ closeAt C w E N

Δ₀-codesAt : ∀ {m} (C w E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (codesAt C w E N)
Δ₀-codesAt C w E N = checkΔ₀ (codesAt C w E N) tt
```

The codes, read. The semantic content of the ten payloads, and one reader per
macro, at variable environments.

```agda
open import V.Coding {ℓ} using ( #-inj′; #mono; module VCode )
open import Cubical.Data.FinData.Properties using ( toℕ<n )
```

A term code over the carrier `Wv` at the arity `ar`.

```agda
IsTmV : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
IsTmV Wv t ar = ∥ (Σ[ x ∈ V ℓ ] ((t ≡ pr (# 0) x) × ⟨ x ∈ Wv ⟩))
                ⊎ (Σ[ i ∈ V ℓ ] ((t ≡ pr (# 1) i) × ⟨ i ∈ ar ⟩)) ∥₁

module CodesSem (Wv Cv : V ℓ) where
  AtomP BinP ConP QuP BqP : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  AtomP ar r = ∥ Σ[ t ∈ V ℓ ] Σ[ u ∈ V ℓ ] ((r ≡ pr t u) × (IsTmV Wv t ar × IsTmV Wv u ar)) ∥₁
  BinP ar r = ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] ((r ≡ pr a b) × (⟨ pr ar a ∈ Cv ⟩ × ⟨ pr ar b ∈ Cv ⟩)) ∥₁
  ConP ar r = r ≡ # 0
  QuP ar r = ⟨ pr (sucV ar) r ∈ Cv ⟩
  BqP ar r = ∥ Σ[ t ∈ V ℓ ] Σ[ a ∈ V ℓ ] ((r ≡ pr t a) × (IsTmV Wv t ar × ⟨ pr (sucV ar) a ∈ Cv ⟩)) ∥₁

  PayN : ℕ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  PayN 0 = AtomP
  PayN 1 = AtomP
  PayN 2 = BinP
  PayN 3 = BinP
  PayN 4 = BinP
  PayN 5 = ConP
  PayN 6 = QuP
  PayN 7 = QuP
  PayN 8 = BqP
  PayN 9 = BqP
  PayN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) _ _ = Empty.⊥*
```

`p` is the tagged payload of some tag.

```agda
  Key : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Key ar p = ∥ Σ[ k ∈ Fin 10 ] Σ[ r ∈ V ℓ ] ((p ≡ pr (# (toℕ k)) r) × PayN (toℕ k) ar r) ∥₁
```

The term reader, at any frame.

```agda
module _ {k : ℕ} (t ar w N0 N1 : Fin k) (δ : S ^ k)
  (q0 : fst (lookup N0 δ) ≡ # 0) (q1 : fst (lookup N1 δ) ≡ # 1) where
  private
    Wv = fst (lookup w δ)

  isTm-out : ⟨ δ ⊨ isTm t ar w N0 N1 ⟩ → IsTmV Wv (fst (lookup t δ)) (fst (lookup ar δ))
  isTm-out = PT.rec squash₁
    (λ { (inl h) → PT.map
           (λ { (v , s , (e , v∈)) → inl (fst v , (e ∙ cong (λ a → pr a (fst v)) q0 , v∈)) })
           (sndEx-out t N0 (var i0 ∈̇ var (sh 2 w)) δ h)
       ; (inr h) → PT.map
           (λ { (v , s , (e , v∈)) → inr (fst v , (e ∙ cong (λ a → pr a (fst v)) q1 , v∈)) })
           (sndEx-out t N1 (var i0 ∈̇ var (sh 2 ar)) δ h) })

  isTm-in : IsTmV Wv (fst (lookup t δ)) (fst (lookup ar δ)) → ⟨ δ ⊨ isTm t ar w N0 N1 ⟩
  isTm-in = PT.rec (snd (δ ⊨ isTm t ar w N0 N1))
    (λ { (inl (x , (e , x∈))) →
           ∣ inl (fillSnd t δ (lookup N0 δ) (down (lookup w δ) x x∈)
                    (e ∙ cong (λ a → pr a x) (sym q0)) (var i0 ∈̇ var (sh 2 w)) x∈ N0 refl) ∣₁
       ; (inr (i , (e , i∈))) →
           ∣ inr (fillSnd t δ (lookup N1 δ) (down (lookup ar δ) i i∈)
                    (e ∙ cong (λ a → pr a i) (sym q1)) (var i0 ∈̇ var (sh 2 ar)) i∈ N1 refl) ∣₁ })
```

The successor key.

```agda
module _ {k : ℕ} (C ar r : Fin k) (δ : S ^ k) where
  keyUp-out : ⟨ δ ⊨ keyUp C ar r ⟩ → ⟨ pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ) ⟩
  keyUp-out = PT.rec (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
    (λ { (c' , (c'∈ , h)) → PT.rec (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
      (λ { (s , (s∈ , h')) → PT.rec (snd (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ)))
        (λ { (ar' , (ar'∈ , (e , hs))) →
          subst (λ u → ⟨ u ∈ fst (lookup C δ) ⟩)
            (pr-out i2 i0 (sh 3 r) (ar' ∷ s ∷ c' ∷ δ) e
             ∙ cong (λ a → pr a (fst (lookup r δ))) (suc-out (sh 3 ar) i0 (ar' ∷ s ∷ c' ∷ δ) hs))
            c'∈ })
        h' })
      h })

  keyUp-in : ⟨ pr (sucV (fst (lookup ar δ))) (fst (lookup r δ)) ∈ fst (lookup C δ) ⟩ → ⟨ δ ⊨ keyUp C ar r ⟩
  keyUp-in h = ∣ c' , (h , ∣ c .fst , (c .snd .fst , ∣ ar' , (c .snd .snd .fst
    , ( pr-in i2 i0 (sh 3 r) (ar' ∷ c .fst ∷ c' ∷ δ) (sym (cong (λ a → pr a (fst (lookup r δ))) (sucʟ-fst (lookup ar δ))))
      , suc-in (sh 3 ar) i0 (ar' ∷ c .fst ∷ c' ∷ δ) (sucʟ-fst (lookup ar δ)) )) ∣₁) ∣₁) ∣₁
    where
    ar' : S
    ar' = sucʟ (lookup ar δ)
    c' : S
    c' = down (lookup C δ) (pr (sucV (fst (lookup ar δ))) (fst (lookup r δ))) h
    c = container c' ar' (lookup r δ) (cong (λ a → pr a (fst (lookup r δ))) (sym (sucʟ-fst (lookup ar δ))))
```

The key readers are instances of structural membership adequacy.

```agda
module _ {k : ℕ} (C ar N a : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)

  unKey-out : ⟨ δ ⊨ unKey C ar N a ⟩ → ⟨ pr A (pr Nv (fst (lookup a δ))) ∈ Cv ⟩
  unKey-out = E.member-out (keyExpr ar N (E.slot a)) (var C) δ

  unKey-in : ⟨ pr A (pr Nv (fst (lookup a δ))) ∈ Cv ⟩ → ⟨ δ ⊨ unKey C ar N a ⟩
  unKey-in = E.member-in (keyExpr ar N (E.slot a)) (var C) δ

module _ {k : ℕ} (C ar N a b : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
    P = pr (fst (lookup a δ)) (fst (lookup b δ))

  binKey-out : ⟨ δ ⊨ binKey C ar N a b ⟩ → ⟨ pr A (pr Nv P) ∈ Cv ⟩
  binKey-out = E.member-out (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C) δ

  binKey-in : ⟨ pr A (pr Nv P) ∈ Cv ⟩ → ⟨ δ ⊨ binKey C ar N a b ⟩
  binKey-in = E.member-in (keyExpr ar N (E.pair (E.slot a) (E.slot b))) (var C) δ

module _ {k : ℕ} (C ar N Nx x Ny y : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
    T = pr (fst (lookup Nx δ)) (fst (lookup x δ))
    U = pr (fst (lookup Ny δ)) (fst (lookup y δ))

  atomKey-out : ⟨ δ ⊨ atomKey C ar N Nx x Ny y ⟩ → ⟨ pr A (pr Nv (pr T U)) ∈ Cv ⟩
  atomKey-out = E.member-out (atomKeyExpr ar N Nx x Ny y) (var C) δ

  atomKey-in : ⟨ pr A (pr Nv (pr T U)) ∈ Cv ⟩ → ⟨ δ ⊨ atomKey C ar N Nx x Ny y ⟩
  atomKey-in = E.member-in (atomKeyExpr ar N Nx x Ny y) (var C) δ

module _ {k : ℕ} (C ar N Nx x a : Fin k) (δ : S ^ k) where
  private
    Cv = fst (lookup C δ)
    A = fst (lookup ar δ)
    Nv = fst (lookup N δ)
    T = pr (fst (lookup Nx δ)) (fst (lookup x δ))
    Av = fst (lookup a δ)

  bndKey-out : ⟨ δ ⊨ bndKey C ar N Nx x a ⟩ → ⟨ pr A (pr Nv (pr T Av)) ∈ Cv ⟩
  bndKey-out = E.member-out (bndKeyExpr ar N Nx x a) (var C) δ

  bndKey-in : ⟨ pr A (pr Nv (pr T Av)) ∈ Cv ⟩ → ⟨ δ ⊨ bndKey C ar N Nx x a ⟩
  bndKey-in = E.member-in (bndKeyExpr ar N Nx x a) (var C) δ
```

The components of a pair held as an element of L, as elements of L.

```agda
fstS sndS : (x : S) (u v : V ℓ) → fst x ≡ pr u v → S
fstS x u v e = down (down x ⁅ u , v ⁆ (subst (λ z → ⟨ ⁅ u , v ⁆ ∈ z ⟩) (sym e) (∈pair-introR {u = ⁅ u ⁆s} {v = ⁅ u , v ⁆} refl))) u (∈pair-introL {u = u} {v = v} refl)
sndS x u v e = down (down x ⁅ u , v ⁆ (subst (λ z → ⟨ ⁅ u , v ⁆ ∈ z ⟩) (sym e) (∈pair-introR {u = ⁅ u ⁆s} {v = ⁅ u , v ⁆} refl))) v (∈pair-introR {u = u} {v = v} refl)
```

The payloads, read. At `r ∷ s'' ∷ p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ`.

```agda
module PayRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (9 + m))
  (tg : Tags δ (shN 9 N)) where
  private
    Cv = fst (lookup (sh 9 C) δ)
    Wv = fst (lookup (sh 9 w) δ)
    A = fst (lookup i5 δ)
    R = fst (lookup i0 δ)
    q0 = tg f0
    q1 = tg f1
    rS = lookup i0 δ
    module Sh = Shape C w N
  open CodesSem Wv Cv

  private
    tmBody : Formula S (12 + m)
    tmBody = isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ isTm i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1))
    binBody : Formula S (12 + m)
    binBody = appAt (sh 12 C) i8 i1 ∧̇ appAt (sh 12 C) i8 i0
    bqBody : Formula S (12 + m)
    bqBody = isTm i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) ∧̇ keyUp (sh 12 C) i8 i0

  atom-out : ⟨ δ ⊨ Sh.atomPay ⟩ → AtomP A R
  atom-out h = PT.map
    (λ { (t , u , s , (e , (ht , hu))) → fst t , fst u
       , ( e , ( isTm-out i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (u ∷ t ∷ s ∷ δ) q0 q1 ht
               , isTm-out i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (u ∷ t ∷ s ∷ δ) q0 q1 hu ) ) })
    (bothEx-out i0 tmBody δ h)

  atom-in : AtomP A R → ⟨ δ ⊨ Sh.atomPay ⟩
  atom-in = PT.rec (snd (δ ⊨ Sh.atomPay))
    (λ { (t , u , (e , (ht , hu))) →
      fillBoth i0 δ (fstS rS t u e) (sndS rS t u e) e tmBody
        ( isTm-in i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t u e) q0 q1 ht
        , isTm-in i0 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t u e) q0 q1 hu ) })
    where
    δ12 : (t u : V ℓ) (e : R ≡ pr t u) → S ^ (12 + m)
    δ12 t u e = sndS rS t u e ∷ fstS rS t u e ∷ container rS (fstS rS t u e) (sndS rS t u e) e .fst ∷ δ

  bin-out : ⟨ δ ⊨ Sh.binPay ⟩ → BinP A R
  bin-out h = PT.map
    (λ { (a , b , s , (e , (ha , hb))) → fst a , fst b
       , ( e , ( subst ⟨_⟩ (appAt-adequate (sh 12 C) i8 i1 (b ∷ a ∷ s ∷ δ)) ha
               , subst ⟨_⟩ (appAt-adequate (sh 12 C) i8 i0 (b ∷ a ∷ s ∷ δ)) hb ) ) })
    (bothEx-out i0 binBody δ h)

  bin-in : BinP A R → ⟨ δ ⊨ Sh.binPay ⟩
  bin-in = PT.rec (snd (δ ⊨ Sh.binPay))
    (λ { (a , b , (e , (ha , hb))) →
      fillBoth i0 δ (fstS rS a b e) (sndS rS a b e) e binBody
        ( subst ⟨_⟩ (sym (appAt-adequate (sh 12 C) i8 i1 (δ12 a b e))) ha
        , subst ⟨_⟩ (sym (appAt-adequate (sh 12 C) i8 i0 (δ12 a b e))) hb ) })
    where
    δ12 : (a b : V ℓ) (e : R ≡ pr a b) → S ^ (12 + m)
    δ12 a b e = sndS rS a b e ∷ fstS rS a b e ∷ container rS (fstS rS a b e) (sndS rS a b e) e .fst ∷ δ

  con-out : ⟨ δ ⊨ Sh.conPay ⟩ → ConP A R
  con-out h = h ∙ q0

  con-in : ConP A R → ⟨ δ ⊨ Sh.conPay ⟩
  con-in h = h ∙ sym q0

  qu-out : ⟨ δ ⊨ Sh.quPay ⟩ → QuP A R
  qu-out = keyUp-out (sh 9 C) i5 i0 δ

  qu-in : QuP A R → ⟨ δ ⊨ Sh.quPay ⟩
  qu-in = keyUp-in (sh 9 C) i5 i0 δ

  bq-out : ⟨ δ ⊨ Sh.bqPay ⟩ → BqP A R
  bq-out h = PT.map
    (λ { (t , a , s , (e , (ht , ha))) → fst t , fst a
       , ( e , ( isTm-out i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (a ∷ t ∷ s ∷ δ) q0 q1 ht
               , keyUp-out (sh 12 C) i8 i0 (a ∷ t ∷ s ∷ δ) ha ) ) })
    (bothEx-out i0 bqBody δ h)

  bq-in : BqP A R → ⟨ δ ⊨ Sh.bqPay ⟩
  bq-in = PT.rec (snd (δ ⊨ Sh.bqPay))
    (λ { (t , a , (e , (ht , ha))) →
      fillBoth i0 δ (fstS rS t a e) (sndS rS t a e) e bqBody
        ( isTm-in i1 i8 (sh 12 w) (sh 12 (N f0)) (sh 12 (N f1)) (δ12 t a e) q0 q1 ht
        , keyUp-in (sh 12 C) i8 i0 (δ12 t a e) ha ) })
    where
    δ12 : (t a : V ℓ) (e : R ≡ pr t a) → S ^ (12 + m)
    δ12 t a e = sndS rS t a e ∷ fstS rS t a e ∷ container rS (fstS rS t a e) (sndS rS t a e) e .fst ∷ δ

  payN-out : (k : ℕ) → ⟨ δ ⊨ Sh.payN k ⟩ → PayN k A R
  payN-out 0 = atom-out
  payN-out 1 = atom-out
  payN-out 2 = bin-out
  payN-out 3 = bin-out
  payN-out 4 = bin-out
  payN-out 5 = con-out
  payN-out 6 = qu-out
  payN-out 7 = qu-out
  payN-out 8 = bq-out
  payN-out 9 = bq-out
  payN-out (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) h = h

  payN-in : (k : ℕ) → PayN k A R → ⟨ δ ⊨ Sh.payN k ⟩
  payN-in 0 = atom-in
  payN-in 1 = atom-in
  payN-in 2 = bin-in
  payN-in 3 = bin-in
  payN-in 4 = bin-in
  payN-in 5 = con-in
  payN-in 6 = qu-in
  payN-in 7 = qu-in
  payN-in 8 = bq-in
  payN-in 9 = bq-in
  payN-in (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) h = h
```

The ten, read. At `p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ`.

```agda
module TenRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (7 + m))
  (tg : Tags δ (shN 7 N)) where
  private
    Cv = fst (lookup (sh 7 C) δ)
    Wv = fst (lookup (sh 7 w) δ)
    A = fst (lookup i3 δ)
    P = fst (lookup i0 δ)
    pS = lookup i0 δ
    module Sh = Shape C w N
  open CodesSem Wv Cv

  at-out : (j : Fin 10) → ⟨ δ ⊨ Sh.at j ⟩ → Key A P
  at-out j h = PT.map
    (λ { (r , s , (e , hp)) → j , fst r
       , ( e ∙ cong (λ a → pr a (fst r)) (tg j)
         , PayRead.payN-out C w N (r ∷ s ∷ δ) tg (toℕ j) hp ) })
    (sndEx-out i0 (sh 7 (N j)) (Sh.pay j) δ h)

  at-in : (j : Fin 10) (r : V ℓ) (e : P ≡ pr (# (toℕ j)) r) → PayN (toℕ j) A r → ⟨ δ ⊨ Sh.at j ⟩
  at-in j r e pay =
    fillSnd i0 δ (lookup (sh 7 (N j)) δ) rS e' (Sh.pay j)
      (PayRead.payN-in C w N (rS ∷ container pS (lookup (sh 7 (N j)) δ) rS e' .fst ∷ δ) tg (toℕ j) pay)
      (sh 7 (N j)) refl
    where
    rS : S
    rS = sndS pS (# (toℕ j)) r e
    e' : P ≡ pr (fst (lookup (sh 7 (N j)) δ)) (fst rS)
    e' = e ∙ cong (λ a → pr a r) (sym (tg j))

  ten-out : ⟨ δ ⊨ Sh.ten ⟩ → Key A P
  ten-out h = PT.rec squash₁ (λ { (j , hj) → at-out j hj }) (bigOr-out δ 9 Sh.at h)

  ten-in : Key A P → ⟨ δ ⊨ Sh.ten ⟩
  ten-in = PT.rec (snd (δ ⊨ Sh.ten))
    (λ { (j , r , (e , pay)) → bigOr-in δ 9 Sh.at j (at-in j r e pay) })
```

The shape clause, read.

```agda
module ShapeRead {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Cv = fst (lookup C γ)
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    module Sh = Shape C w N
    inner : Formula S (5 + m)
    inner = sndEx i4 i1 Sh.ten
  open CodesSem Wv Cv

  Shaped : V ℓ → Type (ℓ-suc ℓ)
  Shaped c = ∥ Σ[ ar ∈ V ℓ ] Σ[ F ∈ V ℓ ] Σ[ p ∈ V ℓ ]
               (⟨ pr ar F ∈ Ev ⟩ × ((c ≡ pr ar p) × Key ar p)) ∥₁

  shape-out : ⟨ γ ⊨ shapeAt C w E N ⟩ → (c : S) → ⟨ fst c ∈ Cv ⟩ → Shaped (fst c)
  shape-out h c c∈ = PT.rec squash₁
    (λ { (q , (q∈ , hb)) → PT.rec squash₁
      (λ { (ar , F , s , (eq , hs)) → PT.map
        (λ { (p , s' , (ec , ht)) →
          fst ar , fst F , fst p
          , ( subst (λ u → ⟨ u ∈ Ev ⟩) eq q∈
            , ( ec , TenRead.ten-out C w N (p ∷ s' ∷ F ∷ ar ∷ s ∷ q ∷ c ∷ γ) tg ht ) ) })
        (sndEx-out i4 i1 Sh.ten (F ∷ ar ∷ s ∷ q ∷ c ∷ γ) hs) })
      (bothEx-out i0 inner (q ∷ c ∷ γ) hb) })
    (h c c∈)

  shape-in : ((c : S) → ⟨ fst c ∈ Cv ⟩ → Shaped (fst c)) → ⟨ γ ⊨ shapeAt C w E N ⟩
  shape-in k c c∈ = PT.rec (snd ((c ∷ γ) ⊨ ∃̇∈ (var (sh 1 E)) (bothEx i0 inner)))
    (λ { (ar , F , p , (q∈ , (ec , key))) →
      let qS = down (lookup E γ) (pr ar F) q∈
          arS = fstS qS ar F refl
          FS = sndS qS ar F refl
          δ2 = qS ∷ c ∷ γ
          cq = container qS arS FS refl
          δ5 = FS ∷ arS ∷ cq .fst ∷ δ2
          pS = sndS c ar p ec
          cp = container c arS pS ec
          δ7 = pS ∷ cp .fst ∷ δ5
      in ∣ qS , ( q∈ , fillBoth i0 δ2 arS FS refl inner
            (fillSnd i4 δ5 arS pS ec Sh.ten
              (TenRead.ten-in C w N δ7 tg key) i1 refl) ) ∣₁ })
    (k c c∈)
```

The closure clauses, read. At `F ∷ ar ∷ s ∷ q ∷ γ`, with `ar` at `i1`.

```agda
module CloseRead {m : ℕ} (C w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (4 + m)) (tg : Tags δ (shN 4 N)) where
  private
    Cv = fst (lookup (sh 4 C) δ)
    A = fst (lookup i1 δ)
    arS = lookup i1 δ
    CS = lookup (sh 4 C) δ
    module Cl = Close C w N
```

The atoms.

```agda
  atomClose-out : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
                → ⟨ δ ⊨ Cl.atomClose k Nx Ny X Y ⟩
                → (x y : S) → ⟨ fst x ∈ fst (lookup X δ) ⟩ → ⟨ fst y ∈ fst (lookup Y (x ∷ δ)) ⟩
                → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y)))) ∈ Cv ⟩
  atomClose-out k Nx Ny X Y h x y x∈ y∈ =
    subst (λ u → ⟨ u ∈ Cv ⟩)
      (cong (pr A) (cong₂ pr (tg k) (cong₂ pr (cong (λ a → pr a (fst x)) (tg Nx)) (cong (λ a → pr a (fst y)) (tg Ny)))))
      (atomKey-out (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0 (y ∷ x ∷ δ) (h x x∈ y y∈))

  atomClose-in : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
               → ((x y : S) → ⟨ fst x ∈ fst (lookup X δ) ⟩ → ⟨ fst y ∈ fst (lookup Y (x ∷ δ)) ⟩
                  → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y)))) ∈ Cv ⟩)
               → ⟨ δ ⊨ Cl.atomClose k Nx Ny X Y ⟩
  atomClose-in k Nx Ny X Y g x x∈ y y∈ =
    atomKey-in (sh 6 C) i3 (sh 6 (N k)) (sh 6 (N Nx)) i1 (sh 6 (N Ny)) i0 (y ∷ x ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩)
        (sym (cong (pr A) (cong₂ pr (tg k) (cong₂ pr (cong (λ a → pr a (fst x)) (tg Nx)) (cong (λ a → pr a (fst y)) (tg Ny))))))
        (g x y x∈ y∈))
```

The binary connectives.

```agda
  binClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.binClose k ⟩
               → (c₁ c₂ a b : S) → ⟨ fst c₁ ∈ Cv ⟩ → ⟨ fst c₂ ∈ Cv ⟩
               → fst c₁ ≡ pr A (fst a) → fst c₂ ≡ pr A (fst b)
               → ⟨ pr A (pr (# (toℕ k)) (pr (fst a) (fst b))) ∈ Cv ⟩
  binClose-out k h c₁ c₂ a b c₁∈ c₂∈ e₁ e₂ =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong (λ v → pr v (pr (fst a) (fst b))) (tg k)))
      (binKey-out (sh 10 C) i7 (sh 10 (N k)) i3 i0 δ10
        (useSnd i0 δ8 arS b e₂ (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0) i5 refl
          (useSnd i0 (c₁ ∷ δ) arS a e₁ inner i2 refl (h c₁ c₁∈) c₂ c₂∈)))
    where
    inner : Formula S (7 + m)
    inner = ∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))
    δ7 : S ^ (7 + m)
    δ7 = a ∷ container c₁ arS a e₁ .fst ∷ c₁ ∷ δ
    δ8 : S ^ (8 + m)
    δ8 = c₂ ∷ δ7
    δ10 : S ^ (10 + m)
    δ10 = b ∷ container c₂ arS b e₂ .fst ∷ δ8

  binClose-in : (k : Fin 10)
              → ((c₁ c₂ a b : S) → ⟨ fst c₁ ∈ Cv ⟩ → ⟨ fst c₂ ∈ Cv ⟩
                 → fst c₁ ≡ pr A (fst a) → fst c₂ ≡ pr A (fst b)
                 → ⟨ pr A (pr (# (toℕ k)) (pr (fst a) (fst b))) ∈ Cv ⟩)
              → ⟨ δ ⊨ Cl.binClose k ⟩
  binClose-in k g c₁ c₁∈ = sndAll-in i0 i2 (∀̇∈ (var (sh 7 C)) (sndAll i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0))) (c₁ ∷ δ) (λ a s s∈ a∈ e₁ c₂ c₂∈ →
    sndAll-in i0 i5 (binKey (sh 10 C) i7 (sh 10 (N k)) i3 i0) (c₂ ∷ a ∷ s ∷ c₁ ∷ δ) (λ b s' s'∈ b∈ e₂ →
      binKey-in (sh 10 C) i7 (sh 10 (N k)) i3 i0 (b ∷ s' ∷ c₂ ∷ a ∷ s ∷ c₁ ∷ δ)
        (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong (λ v → pr v (pr (fst a) (fst b))) (tg k))))
          (g c₁ c₂ a b c₁∈ c₂∈ e₁ e₂))))
```

The constants.

```agda
  conClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.conClose k ⟩ → ⟨ pr A (pr (# (toℕ k)) (# 0)) ∈ Cv ⟩
  conClose-out k h =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong₂ pr (tg k) (tg f0)))
      (unKey-out (sh 4 C) i1 (sh 4 (N k)) (sh 4 (N f0)) δ h)

  conClose-in : (k : Fin 10) → ⟨ pr A (pr (# (toℕ k)) (# 0)) ∈ Cv ⟩ → ⟨ δ ⊨ Cl.conClose k ⟩
  conClose-in k h =
    unKey-in (sh 4 C) i1 (sh 4 (N k)) (sh 4 (N f0)) δ
      (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong₂ pr (tg k) (tg f0)))) h)
```

The unbounded quantifiers.

```agda
  quClose-out : (k : Fin 10) → ⟨ δ ⊨ Cl.quClose k ⟩
              → (c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
              → ⟨ pr A (pr (# (toℕ k)) (fst a)) ∈ Cv ⟩
  quClose-out k h c₁ ar' a c₁∈ e₁ es =
    subst (λ u → ⟨ u ∈ Cv ⟩) (cong (pr A) (cong (λ v → pr v (fst a)) (tg k)))
      (unKey-out (sh 8 C) i5 (sh 8 (N k)) i0 δ8
        (useBoth i0 (c₁ ∷ δ) ar' a e₁ (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0) (h c₁ c₁∈)
          (suc-in i5 i1 δ8 es)))
    where
    δ8 : S ^ (8 + m)
    δ8 = a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ

  quClose-in : (k : Fin 10)
             → ((c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
                → ⟨ pr A (pr (# (toℕ k)) (fst a)) ∈ Cv ⟩)
             → ⟨ δ ⊨ Cl.quClose k ⟩
  quClose-in k g c₁ c₁∈ = bothAll-in i0 (sucAtL i5 i1 ⇒̇ unKey (sh 8 C) i5 (sh 8 (N k)) i0) (c₁ ∷ δ) (λ ar' a s s∈ ar'∈ a∈ e₁ hs →
    unKey-in (sh 8 C) i5 (sh 8 (N k)) i0 (a ∷ ar' ∷ s ∷ c₁ ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩) (sym (cong (pr A) (cong (λ v → pr v (fst a)) (tg k))))
        (g c₁ ar' a c₁∈ e₁ (suc-out i5 i1 (a ∷ ar' ∷ s ∷ c₁ ∷ δ) hs))))
```

The bounded quantifiers. The bound `X` is read at the frame the container
makes, which reduces at either instance.

```agda
  bqClose-out : (k Nx : Fin 10) (X : Fin (8 + m)) → ⟨ δ ⊨ Cl.bqClose k Nx X ⟩
              → (c₁ ar' a : S) → ⟨ fst c₁ ∈ Cv ⟩ → (e₁ : fst c₁ ≡ pr (fst ar') (fst a)) → fst ar' ≡ sucV A
              → (x : S) → ⟨ fst x ∈ fst (lookup X (a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ)) ⟩
              → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a))) ∈ Cv ⟩
  bqClose-out k Nx X h c₁ ar' a c₁∈ e₁ es x x∈ =
    subst (λ u → ⟨ u ∈ Cv ⟩)
      (cong (pr A) (cong₂ pr (tg k) (cong (λ v → pr v (fst a)) (cong (λ v → pr v (fst x)) (tg Nx)))))
      (bndKey-out (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1 (x ∷ δ8)
        (useBoth i0 (c₁ ∷ δ) ar' a e₁ (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1))
          (h c₁ c₁∈) (suc-in i5 i1 δ8 es) x x∈))
    where
    δ8 : S ^ (8 + m)
    δ8 = a ∷ ar' ∷ container c₁ ar' a e₁ .fst ∷ c₁ ∷ δ

  bqClose-in : (k Nx : Fin 10) (X : Fin (8 + m))
             → ((c₁ ar' a s : S) → ⟨ fst c₁ ∈ Cv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
                → (x : S) → ⟨ fst x ∈ fst (lookup X (a ∷ ar' ∷ s ∷ c₁ ∷ δ)) ⟩
                → ⟨ pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a))) ∈ Cv ⟩)
             → ⟨ δ ⊨ Cl.bqClose k Nx X ⟩
  bqClose-in k Nx X g c₁ c₁∈ = bothAll-in i0 (sucAtL i5 i1 ⇒̇ ∀̇∈ (var X) (bndKey (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1)) (c₁ ∷ δ) (λ ar' a s s∈ ar'∈ a∈ e₁ hs x x∈ →
    bndKey-in (sh 9 C) i6 (sh 9 (N k)) (sh 9 (N Nx)) i0 i1 (x ∷ a ∷ ar' ∷ s ∷ c₁ ∷ δ)
      (subst (λ u → ⟨ u ∈ Cv ⟩)
        (sym (cong (pr A) (cong₂ pr (tg k) (cong (λ v → pr v (fst a)) (cong (λ v → pr v (fst x)) (tg Nx))))))
        (g c₁ ar' a s c₁∈ e₁ (suc-out i5 i1 (a ∷ ar' ∷ s ∷ c₁ ∷ δ) hs) x x∈)))
```

`C` is sound: every member is the key of a formula over `w`. The Δ₀ shape clause
supplies src/L/Coding/Model.lagda.md `closedAt` and
src/L/Coding/Shape.lagda.md `shapedAt` for `C` itself, and the decode of
src/L/Coding/CodeSet.lagda.md `witnessAt-out` does the rest.

```agda
open import L.Coding.Model {ℓ} using
  ( closedAt; binSameClosed-in; unSuccClosed-in; binSuccClosed-in
  ; tagAtL-adequate )
open import L.Coding.Shape {ℓ} using
  ( shapedAt; shaped-in; ShapeWit; BinWit; bothTm; fstTm; noneB; isTmAt )
open import L.Coding.CodeSet {ℓ} lem using
  ( AllCodes; AllCodes-out; key∈AllCodes; keyS; codeS; witnessAt-out )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import Cubical.Foundations.Prelude using ( J; substRefl )
open import Cubical.Foundations.HLevels using ( isProp× )

module _ (Wv Cv : V ℓ) where
  open CodesSem Wv Cv

  isPropPayN : (n : ℕ) (ar r : V ℓ) → isProp (PayN n ar r)
  isPropPayN 0 ar r = squash₁
  isPropPayN 1 ar r = squash₁
  isPropPayN 2 ar r = squash₁
  isPropPayN 3 ar r = squash₁
  isPropPayN 4 ar r = squash₁
  isPropPayN 5 ar r = setIsSet r (# 0)
  isPropPayN 6 ar r = snd (pr (sucV ar) r ∈ Cv)
  isPropPayN 7 ar r = snd (pr (sucV ar) r ∈ Cv)
  isPropPayN 8 ar r = squash₁
  isPropPayN 9 ar r = squash₁
  isPropPayN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) ar r = Empty.isProp⊥*
```

A key read at a stated tag.

```agda
  keyAt : (ar p : V ℓ) → Key ar p → (n : ℕ) (r : V ℓ) → p ≡ pr (# n) r → PayN n ar r
  keyAt ar p key n r e = PT.rec (isPropPayN n ar r)
    (λ { (k , r' , (e' , pay)) →
      let q = pr-inj (sym e ∙ e')
      in subst2 (λ j x → PayN j ar x) (sym (#-inj′ (q .fst))) (sym (q .snd)) pay })
    key
```

A term witness for src/L/Coding/Shape.lagda.md `isTmAt`, at any frame.

```agda
tmWit : ∀ {j} (ti Ni Ai : Fin j) (env : S ^ j)
      → IsTmV (fst (lookup Ai env)) (fst (lookup ti env)) (fst (lookup Ni env))
      → ⟨ env ⊨ isTmAt ti Ni Ai ⟩
tmWit ti Ni Ai env = PT.rec (snd (env ⊨ isTmAt ti Ni Ai))
  (λ { (inl (x , (e , x∈))) →
         ∣ inl ∣ down (lookup Ai env) x x∈
           , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc ti) 0 zero (down (lookup Ai env) x x∈ ∷ env))) e
             , x∈ ) ∣₁ ∣₁
     ; (inr (i , (e , i∈))) →
         ∣ inr ∣ down (lookup Ni env) i i∈
           , ( subst ⟨_⟩ (sym (tagAtL-adequate (suc ti) 1 zero (down (lookup Ni env) i i∈ ∷ env))) e
             , i∈ ) ∣₁ ∣₁ })

module CodesSound {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (arity : (n F : S) → ⟨ pr (fst n) (fst F) ∈ fst (lookup E γ) ⟩ → ∥ Σ[ k ∈ ℕ ] (fst n ≡ # k) ∥₁)
  (hs : ⟨ γ ⊨ shapeAt C w E N ⟩) where
  private
    Cv = fst (lookup C γ)
    CS = lookup C γ
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    module SR = ShapeRead C w E N γ tg
  open CodesSem Wv Cv

  private
```

The frame the decode reads in: `C` at slot zero, the member at one.

```agda
    δ' : S → S ^ (2 + m)
    δ' c = CS ∷ c ∷ γ
```

The shape of a member, at a stated tag.

```agda
    at : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (ar r : V ℓ) → fst c ≡ pr ar (pr (# n) r)
       → PayN n ar r
    at c c∈ n ar r e = PT.rec (isPropPayN Wv Cv n ar r)
      (λ { (ar' , F , p , (q∈ , (ec , key))) →
        let q = pr-inj (sym ec ∙ e)
        in subst (λ a → PayN n a r) (q .fst) (keyAt Wv Cv ar' p key n r (q .snd)) })
      (SR.shape-out hs c c∈)

    binAt : (k : ℕ) → PayN k ≡ BinP → (c ar a b : S) → ⟨ fst c ∈ Cv ⟩
          → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
          → ⟨ pr (fst ar) (fst a) ∈ Cv ⟩ × ⟨ pr (fst ar) (fst b) ∈ Cv ⟩
    binAt k eq c ar a b c∈ e = PT.rec (isProp× (snd (pr (fst ar) (fst a) ∈ Cv)) (snd (pr (fst ar) (fst b) ∈ Cv)))
      (λ { (a' , b' , (er , (ha , hb))) →
        let q = pr-inj er
        in subst (λ u → ⟨ pr (fst ar) u ∈ Cv ⟩) (sym (q .fst)) ha
         , subst (λ u → ⟨ pr (fst ar) u ∈ Cv ⟩) (sym (q .snd)) hb })
      (subst (λ P → P (fst ar) (pr (fst a) (fst b))) eq (at c c∈ k (fst ar) (pr (fst a) (fst b)) e))

    bqAt : (k : ℕ) → PayN k ≡ BqP → (c ar a b : S) → ⟨ fst c ∈ Cv ⟩
         → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
         → ⟨ pr (sucV (fst ar)) (fst b) ∈ Cv ⟩
    bqAt k eq c ar a b c∈ e = PT.rec (snd (pr (sucV (fst ar)) (fst b) ∈ Cv))
      (λ { (t , a' , (er , (ht , ha))) →
        subst (λ u → ⟨ pr (sucV (fst ar)) u ∈ Cv ⟩) (sym (pr-inj er .snd)) ha })
      (subst (λ P → P (fst ar) (pr (fst a) (fst b))) eq (at c c∈ k (fst ar) (pr (fst a) (fst b)) e))

    hcl : (c : S) → ⟨ δ' c ⊨ closedAt zero ⟩
    hcl c =
        binSameClosed-in zero 2 (δ' c) (binAt 2 refl)
      , ( binSameClosed-in zero 3 (δ' c) (binAt 3 refl)
      , ( binSameClosed-in zero 4 (δ' c) (binAt 4 refl)
      , ( unSuccClosed-in zero 6 (δ' c) (λ c' ar a c'∈ e → at c' c'∈ 6 (fst ar) (fst a) e)
      , ( unSuccClosed-in zero 7 (δ' c) (λ c' ar a c'∈ e → at c' c'∈ 7 (fst ar) (fst a) e)
      , ( binSuccClosed-in zero 8 (δ' c) (bqAt 8 refl)
      ,   binSuccClosed-in zero 9 (δ' c) (bqAt 9 refl) )))))
```

A member's shape witness for `shapedAt`.

```agda
    wit : (c c' : S) → ⟨ fst c' ∈ Cv ⟩ → ∥ ShapeWit (sh 2 w) (δ' c) c' ∥₁
    wit c c' c'∈ = PT.rec squash₁
      (λ { (ar , F , p , (q∈ , (ec , key))) → PT.rec squash₁
        (λ { (k , r , (e' , pay)) →
          let qS = down (lookup E γ) (pr ar F) q∈
              arS = fstS qS ar F refl
              pS = sndS c' ar p ec
              rS = sndS pS (# (toℕ k)) r e'
              ek : fst c' ≡ pr (fst arS) (pr (# (toℕ k)) (fst rS))
              ek = ec ∙ cong (pr ar) e'
          in fill k c' arS rS pay ek })
        key })
      (SR.shape-out hs c' c'∈)
      where
      env4 : (c' arS b a : S) → S ^ (6 + m)
      env4 c' arS b a = b ∷ a ∷ arS ∷ c' ∷ δ' c
```

The pair witness of an atom, a connective or a bounded quantifier.

```agda
      pairWit : (k : ℕ) (rel : Formula S (4 + (2 + m))) (c' arS rS : S)
              → fst c' ≡ pr (fst arS) (pr (# k) (fst rS))
              → (t u : V ℓ) → fst rS ≡ pr t u
              → ((tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ rel ⟩)
              → BinWit k rel (δ' c) c'
      pairWit k rel c' arS rS ek t u er g =
        arS , (fstS rS t u er , (sndS rS t u er
        , ( ek ∙ cong (λ v → pr (fst arS) (pr (# k) v)) er
          , g (fstS rS t u er) (sndS rS t u er) refl refl )))

      both : (c' arS : S) (t u : V ℓ) → IsTmV Wv t (fst arS) → IsTmV Wv u (fst arS)
           → (tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ bothTm (sh 2 w) ⟩
      both c' arS t u ht hu tS uS qt qu =
          tmWit (suc zero) (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
            (subst (λ x → IsTmV Wv x (fst arS)) (sym qt) ht)
        , tmWit zero (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
            (subst (λ x → IsTmV Wv x (fst arS)) (sym qu) hu)

      first : (c' arS : S) (t u : V ℓ) → IsTmV Wv t (fst arS)
            → (tS uS : S) → fst tS ≡ t → fst uS ≡ u → ⟨ env4 c' arS uS tS ⊨ fstTm (sh 2 w) ⟩
      first c' arS t u ht tS uS qt qu =
        tmWit (suc zero) (suc (suc zero)) (sh 4 (sh 2 w)) (env4 c' arS uS tS)
          (subst (λ x → IsTmV Wv x (fst arS)) (sym qt) ht)

      fill : (k : Fin 10) (c' arS rS : S) → PayN (toℕ k) (fst arS) (fst rS)
           → fst c' ≡ pr (fst arS) (pr (# (toℕ k)) (fst rS))
           → ∥ ShapeWit (sh 2 w) (δ' c) c' ∥₁
      fill zero c' arS rS pay ek = PT.map
        (λ { (t , u , (er , (ht , hu))) → inl (pairWit 0 (bothTm (sh 2 w)) c' arS rS ek t u er (both c' arS t u ht hu)) })
        pay
      fill (suc zero) c' arS rS pay ek = PT.map
        (λ { (t , u , (er , (ht , hu))) → inr (inl (pairWit 1 (bothTm (sh 2 w)) c' arS rS ek t u er (both c' arS t u ht hu))) })
        pay
      fill (suc (suc zero)) c' arS rS pay ek = PT.map
        (λ { (a , b , (er , _)) → inr (inr (inl (pairWit 2 noneB c' arS rS ek a b er (λ _ _ _ _ b → b)))) })
        pay
      fill (suc (suc (suc zero))) c' arS rS pay ek = PT.map
        (λ { (a , b , (er , _)) → inr (inr (inr (inl (pairWit 3 noneB c' arS rS ek a b er (λ _ _ _ _ b → b))))) })
        pay
      fill (suc (suc (suc (suc zero)))) c' arS rS pay ek = PT.map
        (λ { (a , b , (er , _)) → inr (inr (inr (inr (inl (pairWit 4 noneB c' arS rS ek a b er (λ _ _ _ _ b → b)))))) })
        pay
      fill (suc (suc (suc (suc (suc zero))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inl (arS , (rS , (ek , pay ∙ sym (numeralL-fst 0))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc zero)))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inr (inl (arS , (rS , (ek , (λ b → b)))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc (suc zero))))))) c' arS rS pay ek =
        ∣ inr (inr (inr (inr (inr (inr (inr (inl (arS , (rS , (ek , (λ b → b))))))))))) ∣₁
      fill (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) c' arS rS pay ek = PT.map
        (λ { (t , a , (er , (ht , _))) → inr (inr (inr (inr (inr (inr (inr (inr (inl
          (pairWit 8 (fstTm (sh 2 w)) c' arS rS ek t a er (first c' arS t a ht)))))))))) })
        pay
      fill (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) c' arS rS pay ek = PT.map
        (λ { (t , a , (er , (ht , _))) → inr (inr (inr (inr (inr (inr (inr (inr (inr
          (pairWit 9 (fstTm (sh 2 w)) c' arS rS ek t a er (first c' arS t a ht)))))))))) })
        pay

    hsh : (c : S) → ⟨ δ' c ⊨ shapedAt zero (sh 2 w) ⟩
    hsh c = shaped-in zero (sh 2 w) (δ' c) (wit c)
```

The same eight, read at `C` in `γ` rather than at the decode's frame.

```agda
  closed : ⟨ γ ⊨ closedAt C ⟩
  closed =
      binSameClosed-in C 2 γ (binAt 2 refl)
    , ( binSameClosed-in C 3 γ (binAt 3 refl)
    , ( binSameClosed-in C 4 γ (binAt 4 refl)
    , ( unSuccClosed-in C 6 γ (λ c' ar a c'∈ e → at c' c'∈ 6 (fst ar) (fst a) e)
    , ( unSuccClosed-in C 7 γ (λ c' ar a c'∈ e → at c' c'∈ 7 (fst ar) (fst a) e)
    , ( binSuccClosed-in C 8 γ (bqAt 8 refl)
    ,   binSuccClosed-in C 9 γ (bqAt 9 refl) )))))

  key-out : (c : S) → ⟨ fst c ∈ Cv ⟩
          → ∥ Σ[ k ∈ ℕ ] Σ[ ψ ∈ Formula ⟪ fst W ⟫ k ] (fst c ≡ fst (keyS W ψ)) ∥₁
  key-out c c∈ = PT.rec squash₁
    (λ { (ar , F , p , (q∈ , (ec , key))) → PT.rec squash₁
      (λ { (k , qk) → PT.map (λ { (ψ , e) → k , ψ , e })
        (witnessAt-out W (suc w) zero (c ∷ γ) qw
          ∣ CS , (c∈ , (hcl c , hsh c)) ∣₁
          k (sndS c ar p ec) (ec ∙ cong (λ a → pr a p) qk)) })
      (arity (fstS (down (lookup E γ) (pr ar F) q∈) ar F refl)
             (sndS (down (lookup E γ) (pr ar F) q∈) ar F refl) q∈) })
    (SR.shape-out hs c c∈)
```

`C` is complete: the key of every formula over `w` is a member, by induction on
the formula through the closure clauses.

```agda
open import L.Ordinal {ℓ} using ( ∈#-elim )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId' )
```

The alphabet of w, its codes and its terms' codes.

```agda
module Alphabet (W : S) where
  Ab : Type ℓ
  Ab = ⟪ fst W ⟫

  ι : Ab → V ℓ
  ι = ⟪ fst W ⟫↪

  ι∈ : (q : Ab) → ⟨ ι q ∈ fst W ⟩
  ι∈ q = ∈∈ₛ {a = ι q} {b = fst W} .snd (∈ₛ⟪ fst W ⟫↪ q)

  cd : ∀ {n} → Formula Ab n → V ℓ
  cd ψ = VCode.⌜ mapFo ι ψ ⌝

  ct : ∀ {n} → Term Ab n → V ℓ
  ct t = VCode.⌜ mapTm ι t ⌝ᵗ

  cd-subst : ∀ {n n'} (e : n ≡ n') (ψ : Formula Ab n) → cd (subst (Formula Ab) e ψ) ≡ cd ψ
  cd-subst {n} e ψ = J (λ n' e' → cd (subst (Formula Ab) e' ψ) ≡ cd ψ)
    (cong cd (substRefl {B = Formula Ab} ψ)) e
```

A term's code is a term code.

```agda
  tmV : ∀ {n} (Wv : V ℓ) → ((q : Ab) → ⟨ ι q ∈ Wv ⟩) → (t : Term Ab n) → IsTmV Wv (ct t) (# n)
  tmV Wv into (con q) = ∣ inl (ι q , (refl , into q)) ∣₁
  tmV {n} Wv into (var i) = ∣ inr (# (toℕ i) , (refl , #mono (toℕ i) n (toℕ<n i))) ∣₁

module CodesComplete {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (tg : Tags γ N)
  (arity∈ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ fst (lookup E γ) ⟩)
  (hc : ⟨ γ ⊨ closeAt C w E N ⟩) where
  open Alphabet W
  private
    Cv = fst (lookup C γ)

    ι∈w : (q : Ab) → ⟨ ι q ∈ fst (lookup w γ) ⟩
    ι∈w q = subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈ q)

    ιS : Ab → S
    ιS q = down (lookup w γ) (ι q) (ι∈w q)

    qS : ℕ → S
    qS n = down (lookup E γ) (pr (# n) (fst (envSet W n))) (arity∈ n)

    δ4 : ℕ → S ^ (4 + m)
    δ4 n = envSet W n ∷ nn n ∷ container (qS n) (nn n) (envSet W n) refl .fst ∷ qS n ∷ γ

    frame : (n : ℕ) → ⟨ δ4 n ⊨ Close.all C w N ⟩
    frame n = useBoth i0 (qS n ∷ γ) (nn n) (envSet W n) refl (Close.all C w N) (hc (qS n) (arity∈ n))

    module CR (n : ℕ) = CloseRead C w N (δ4 n) tg
```

The variable index as a member of the arity numeral.

```agda
    var∈ : (n : ℕ) (i : Fin n) → ⟨ # (toℕ i) ∈ # n ⟩
    var∈ n i = #mono (toℕ i) n (toℕ<n i)

  key-in : ∀ {n} (ψ : Formula Ab n) → ⟨ fst (keyS W ψ) ∈ Cv ⟩
  key-in {n} (con x ∈̇ con y) = CR.atomClose-out n f0 f0 f0 (sh 4 w) (sh 5 w) (frame n .fst) (ιS x) (ιS y) (ι∈w x) (ι∈w y)
  key-in {n} (con x ∈̇ var j) = CR.atomClose-out n f0 f0 f1 (sh 4 w) i2 (frame n .snd .fst) (ιS x) (nn (toℕ j)) (ι∈w x) (var∈ n j)
  key-in {n} (var i ∈̇ con y) = CR.atomClose-out n f0 f1 f0 i1 (sh 5 w) (frame n .snd .snd .fst) (nn (toℕ i)) (ιS y) (var∈ n i) (ι∈w y)
  key-in {n} (var i ∈̇ var j) = CR.atomClose-out n f0 f1 f1 i1 i2 (frame n .snd .snd .snd .fst) (nn (toℕ i)) (nn (toℕ j)) (var∈ n i) (var∈ n j)
  key-in {n} (con x ≐ con y) = CR.atomClose-out n f1 f0 f0 (sh 4 w) (sh 5 w) (frame n .snd .snd .snd .snd .fst) (ιS x) (ιS y) (ι∈w x) (ι∈w y)
  key-in {n} (con x ≐ var j) = CR.atomClose-out n f1 f0 f1 (sh 4 w) i2 (frame n .snd .snd .snd .snd .snd .fst) (ιS x) (nn (toℕ j)) (ι∈w x) (var∈ n j)
  key-in {n} (var i ≐ con y) = CR.atomClose-out n f1 f1 f0 i1 (sh 5 w) (frame n .snd .snd .snd .snd .snd .snd .fst) (nn (toℕ i)) (ιS y) (var∈ n i) (ι∈w y)
  key-in {n} (var i ≐ var j) = CR.atomClose-out n f1 f1 f1 i1 i2 (frame n .snd .snd .snd .snd .snd .snd .snd .fst) (nn (toℕ i)) (nn (toℕ j)) (var∈ n i) (var∈ n j)
  key-in {n} (a ∧̇ b) = CR.binClose-out n f2 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} (a ∨̇ b) = CR.binClose-out n f3 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} (a ⇒̇ b) = CR.binClose-out n f4 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (keyS W b) (codeS W a) (codeS W b) (key-in a) (key-in b) refl refl
  key-in {n} ⊥̇ = CR.conClose-out n f5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)
  key-in {n} (∃̇ a) = CR.quClose-out n f6 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl
  key-in {n} (∀̇ a) = CR.quClose-out n f7 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl
  key-in {n} (∀̇∈ (con x) a) =
    CR.bqClose-out n f8 f0 (sh 8 w) (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (ιS x) (ι∈w x)
  key-in {n} (∀̇∈ (var i) a) =
    CR.bqClose-out n f8 f1 i5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (nn (toℕ i)) (var∈ n i)
  key-in {n} (∃̇∈ (con x) a) =
    CR.bqClose-out n f9 f0 (sh 8 w) (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (ιS x) (ι∈w x)
  key-in {n} (∃̇∈ (var i) a) =
    CR.bqClose-out n f9 f1 i5 (frame n .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd ) (keyS W a) (nn (suc n)) (codeS W a) (key-in a) refl refl (nn (toℕ i)) (var∈ n i)
```

The code set satisfies the description, at `C = AllCodes w` and `E` the tower.
Shape: every member is decoded to its formula. Closure: the key of the formula
the parts decode to is a member.

```agda
module CodesHolds {m : ℕ} (C w E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (W : S)
  (qw : fst (lookup w γ) ≡ fst W) (qC : fst (lookup C γ) ≡ fst (AllCodes W))
  (qE : fst (lookup E γ) ≡ fst (Tower.tower W)) (tg : Tags γ N) where
  open Alphabet W
  private
    Cv = fst (lookup C γ)
    Wv = fst (lookup w γ)
    Ev = fst (lookup E γ)
    open CodesSem Wv Cv

    ι∈w : (q : Ab) → ⟨ ι q ∈ Wv ⟩
    ι∈w q = subst (λ u → ⟨ ι q ∈ u ⟩) (sym qw) (ι∈ q)

    mem : ∀ {n} (ψ : Formula Ab n) → ⟨ fst (keyS W ψ) ∈ Cv ⟩
    mem ψ = subst (λ u → ⟨ fst (keyS W ψ) ∈ u ⟩) (sym qC) (key∈AllCodes W ψ)

    entry∈ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ Ev ⟩
    entry∈ n = subst (λ u → ⟨ pr (# n) (fst (envSet W n)) ∈ u ⟩) (sym qE) (Tower.tower-in′ W n)

    tm : ∀ {n} (t : Term Ab n) → IsTmV Wv (ct t) (# n)
    tm = tmV Wv ι∈w
```

The key of every formula, as the description sees it.

```agda
    keyOf : ∀ {n} (ψ : Formula Ab n) → Key (# n) (cd ψ)
    keyOf (t ∈̇ u) = ∣ f0 , pr (ct t) (ct u) , (refl , ∣ ct t , ct u , (refl , (tm t , tm u)) ∣₁) ∣₁
    keyOf (t ≐ u) = ∣ f1 , pr (ct t) (ct u) , (refl , ∣ ct t , ct u , (refl , (tm t , tm u)) ∣₁) ∣₁
    keyOf (a ∧̇ b) = ∣ f2 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf (a ∨̇ b) = ∣ f3 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf (a ⇒̇ b) = ∣ f4 , pr (cd a) (cd b) , (refl , ∣ cd a , cd b , (refl , (mem a , mem b)) ∣₁) ∣₁
    keyOf ⊥̇ = ∣ f5 , # 0 , (refl , refl) ∣₁
    keyOf (∃̇ a) = ∣ f6 , cd a , (refl , mem a) ∣₁
    keyOf (∀̇ a) = ∣ f7 , cd a , (refl , mem a) ∣₁
    keyOf (∀̇∈ t a) = ∣ f8 , pr (ct t) (cd a) , (refl , ∣ ct t , cd a , (refl , (tm t , mem a)) ∣₁) ∣₁
    keyOf (∃̇∈ t a) = ∣ f9 , pr (ct t) (cd a) , (refl , ∣ ct t , cd a , (refl , (tm t , mem a)) ∣₁) ∣₁

    shape : ⟨ γ ⊨ shapeAt C w E N ⟩
    shape = ShapeRead.shape-in C w E N γ tg (λ c c∈ → PT.map
      (λ { (n , ψ , e) → # n , fst (envSet W n) , cd ψ , (entry∈ n , (e , keyOf ψ)) })
      (AllCodes-out W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈)))
```

A member handed over as a key at a stated arity decodes to a formula at that
arity.

```agda
    decodeAt : (c : S) → ⟨ fst c ∈ Cv ⟩ → (n : ℕ) (z : V ℓ) → fst c ≡ pr (# n) z
             → ∥ Σ[ ψ ∈ Formula Ab n ] (z ≡ cd ψ) ∥₁
    decodeAt c c∈ n z e = PT.map
      (λ { (n₁ , ψ₁ , e₁) →
        let q = pr-inj (sym e₁ ∙ e)
            nq = #-inj′ (q .fst)
        in subst (Formula Ab) nq ψ₁ , (sym (q .snd) ∙ sym (cd-subst nq ψ₁)) })
      (AllCodes-out W c (subst (λ u → ⟨ fst c ∈ u ⟩) qC c∈))
```

The term decoders: a member of `w` is a constant's code, a member of the arity
is a variable's.

```agda
    TmDec : ∀ {n} → Fin 10 → V ℓ → Type (ℓ-suc ℓ)
    TmDec {n} Nx bound = (x : V ℓ) → ⟨ x ∈ bound ⟩ → ∥ Σ[ t ∈ Term Ab n ] (ct t ≡ pr (# (toℕ Nx)) x) ∥₁

    conDec : ∀ {n} → TmDec {n} f0 Wv
    conDec x x∈ = ∣ con (fib .fst) , cong (pr (# 0)) (fib .snd) ∣₁
      where
      fib : Σ[ q ∈ Ab ] (ι q ≡ x)
      fib = ∈-asFiber {a = x} {b = fst W} (subst (λ u → ⟨ x ∈ u ⟩) qw x∈)

    varDec : (n : ℕ) (A : V ℓ) → A ≡ # n → TmDec {n} f1 A
    varDec n A qa x x∈ = PT.map
      (λ { (j , (p , ex)) → var (fromℕ' n j p) , cong (pr (# 1)) (cong #_ (toFromId' n j p) ∙ sym ex) })
      (∈#-elim n x (subst (λ u → ⟨ x ∈ u ⟩) qa x∈))
```

The closure clauses at an entry `(ar, F)` of the tower, `ar = # n`.

```agda
    module At (q : S) (q∈ : ⟨ fst q ∈ Ev ⟩) (ar F s : S) (n : ℕ) (qa : fst ar ≡ # n) where
      private
        δ4 : S ^ (4 + m)
        δ4 = F ∷ ar ∷ s ∷ q ∷ γ
        A = fst ar
        module CR = CloseRead C w N δ4 tg
        module Cl = Close C w N

        in-key : ∀ {k} (ψ : Formula Ab k) (x : V ℓ) → x ≡ fst (keyS W ψ) → ⟨ x ∈ Cv ⟩
        in-key ψ x e = subst (λ u → ⟨ u ∈ Cv ⟩) (sym e) (mem ψ)
```

Every truncated payload is named before `PT.rec` sees it (the law of
src/L/Coding/CodeSet.lagda.md, met again).

```agda
        TmAt : (Nx : Fin 10) (x : V ℓ) → Type (ℓ-suc ℓ)
        TmAt Nx x = Σ[ t ∈ Term Ab n ] (ct t ≡ pr (# (toℕ Nx)) x)

        FoAt : (k : ℕ) (z : V ℓ) → Type (ℓ-suc ℓ)
        FoAt k z = Σ[ ψ ∈ Formula Ab k ] (z ≡ cd ψ)

        atomIn : (k Nx Ny : Fin 10) (X : Fin (4 + m)) (Y : Fin (5 + m))
               → (op : Term Ab n → Term Ab n → Formula Ab n)
               → ((t u : Term Ab n) → cd (op t u) ≡ pr (# (toℕ k)) (pr (ct t) (ct u)))
               → TmDec Nx (fst (lookup X δ4)) → ((x : S) → TmDec Ny (fst (lookup Y (x ∷ δ4))))
               → ⟨ δ4 ⊨ Cl.atomClose k Nx Ny X Y ⟩
        atomIn k Nx Ny X Y op code dx dy = CR.atomClose-in k Nx Ny X Y (λ x y x∈ y∈ →
          let d1 : ∥ TmAt Nx (fst x) ∥₁
              d1 = dx (fst x) x∈
              d2 : ∥ TmAt Ny (fst y) ∥₁
              d2 = dy x (fst y) y∈
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (pr (# (toℕ Ny)) (fst y))))
          in PT.rec (snd (G ∈ Cv))
            (λ { (t , et) → PT.rec (snd (G ∈ Cv))
              (λ { (u , eu) → in-key (op t u) G
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr (sym et) (sym eu)) ∙ sym (code t u))) })
              d2 })
            d1)

        binIn : (k : Fin 10) (op : Formula Ab n → Formula Ab n → Formula Ab n)
              → ((a b : Formula Ab n) → cd (op a b) ≡ pr (# (toℕ k)) (pr (cd a) (cd b)))
              → ⟨ δ4 ⊨ Cl.binClose k ⟩
        binIn k op code = CR.binClose-in k (λ c₁ c₂ a b c₁∈ c₂∈ e₁ e₂ →
          let d1 : ∥ FoAt n (fst a) ∥₁
              d1 = decodeAt c₁ c₁∈ n (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) qa)
              d2 : ∥ FoAt n (fst b) ∥₁
              d2 = decodeAt c₂ c₂∈ n (fst b) (e₂ ∙ cong (λ v → pr v (fst b)) qa)
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (fst a) (fst b)))
          in PT.rec (snd (G ∈ Cv))
            (λ { (ψ₁ , ea) → PT.rec (snd (G ∈ Cv))
              (λ { (ψ₂ , eb) → in-key (op ψ₁ ψ₂) G
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr ea eb) ∙ sym (code ψ₁ ψ₂))) })
              d2 })
            d1)

        conIn : (k : Fin 10) (c₀ : Formula Ab n) → cd c₀ ≡ pr (# (toℕ k)) (# 0) → ⟨ δ4 ⊨ Cl.conClose k ⟩
        conIn k c₀ code = CR.conClose-in k (in-key c₀ (pr A (pr (# (toℕ k)) (# 0))) (cong₂ pr qa (sym code)))

        quIn : (k : Fin 10) (op : Formula Ab (suc n) → Formula Ab n)
             → ((a : Formula Ab (suc n)) → cd (op a) ≡ pr (# (toℕ k)) (cd a))
             → ⟨ δ4 ⊨ Cl.quClose k ⟩
        quIn k op code = CR.quClose-in k (λ c₁ ar' a c₁∈ e₁ es →
          let d1 : ∥ FoAt (suc n) (fst a) ∥₁
              d1 = decodeAt c₁ c₁∈ (suc n) (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) (es ∙ cong sucV qa))
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (fst a))
          in PT.rec (snd (G ∈ Cv))
            (λ { (ψ₁ , ea) → in-key (op ψ₁) G (cong₂ pr qa (cong (pr (# (toℕ k))) ea ∙ sym (code ψ₁))) })
            d1)

        bqIn : (k Nx : Fin 10) (X : Fin (8 + m))
             → (op : Term Ab n → Formula Ab (suc n) → Formula Ab n)
             → ((t : Term Ab n) (a : Formula Ab (suc n)) → cd (op t a) ≡ pr (# (toℕ k)) (pr (ct t) (cd a)))
             → ((ar' a s' c₁ : S) → TmDec Nx (fst (lookup X (a ∷ ar' ∷ s' ∷ c₁ ∷ δ4))))
             → ⟨ δ4 ⊨ Cl.bqClose k Nx X ⟩
        bqIn k Nx X op code dx = CR.bqClose-in k Nx X (λ c₁ ar' a s' c₁∈ e₁ es x x∈ →
          let d1 : ∥ TmAt Nx (fst x) ∥₁
              d1 = dx ar' a s' c₁ (fst x) x∈
              d2 : ∥ FoAt (suc n) (fst a) ∥₁
              d2 = decodeAt c₁ c₁∈ (suc n) (fst a) (e₁ ∙ cong (λ v → pr v (fst a)) (es ∙ cong sucV qa))
              G : V ℓ
              G = pr A (pr (# (toℕ k)) (pr (pr (# (toℕ Nx)) (fst x)) (fst a)))
          in PT.rec (snd (G ∈ Cv))
            (λ { (t , et) → PT.rec (snd (G ∈ Cv))
              (λ { (ψ₁ , ea) → in-key (op t ψ₁) G
                (cong₂ pr qa (cong (pr (# (toℕ k))) (cong₂ pr (sym et) ea) ∙ sym (code t ψ₁))) })
              d2 })
            d1)

      all : ⟨ δ4 ⊨ Cl.all ⟩
      all =
          atomIn f0 f0 f0 (sh 4 w) (sh 5 w) _∈̇_ (λ _ _ → refl) conDec (λ _ → conDec)
        , ( atomIn f0 f0 f1 (sh 4 w) i2 _∈̇_ (λ _ _ → refl) conDec (λ _ → varDec n A qa)
        , ( atomIn f0 f1 f0 i1 (sh 5 w) _∈̇_ (λ _ _ → refl) (varDec n A qa) (λ _ → conDec)
        , ( atomIn f0 f1 f1 i1 i2 _∈̇_ (λ _ _ → refl) (varDec n A qa) (λ _ → varDec n A qa)
        , ( atomIn f1 f0 f0 (sh 4 w) (sh 5 w) _≐_ (λ _ _ → refl) conDec (λ _ → conDec)
        , ( atomIn f1 f0 f1 (sh 4 w) i2 _≐_ (λ _ _ → refl) conDec (λ _ → varDec n A qa)
        , ( atomIn f1 f1 f0 i1 (sh 5 w) _≐_ (λ _ _ → refl) (varDec n A qa) (λ _ → conDec)
        , ( atomIn f1 f1 f1 i1 i2 _≐_ (λ _ _ → refl) (varDec n A qa) (λ _ → varDec n A qa)
        , ( binIn f2 _∧̇_ (λ _ _ → refl)
        , ( binIn f3 _∨̇_ (λ _ _ → refl)
        , ( binIn f4 _⇒̇_ (λ _ _ → refl)
        , ( conIn f5 ⊥̇ refl
        , ( quIn f6 ∃̇_ (λ _ → refl)
        , ( quIn f7 ∀̇_ (λ _ → refl)
        , ( bqIn f8 f0 (sh 8 w) ∀̇∈ (λ _ _ → refl) (λ _ _ _ _ → conDec)
        , ( bqIn f8 f1 i5 ∀̇∈ (λ _ _ → refl) (λ _ _ _ _ → varDec n A qa)
        , ( bqIn f9 f0 (sh 8 w) ∃̇∈ (λ _ _ → refl) (λ _ _ _ _ → conDec)
        ,   bqIn f9 f1 i5 ∃̇∈ (λ _ _ → refl) (λ _ _ _ _ → varDec n A qa) ))))))))))))))))

    close : ⟨ γ ⊨ closeAt C w E N ⟩
    close q q∈ = bothAll-in i0 (Close.all C w N) (q ∷ γ) (λ ar F s s∈ ar∈ F∈ e →
      PT.rec (snd ((F ∷ ar ∷ s ∷ q ∷ γ) ⊨ Close.all C w N))
        (λ { (n , qp) → At.all q q∈ ar F s n (pr-inj (sym e ∙ qp) .fst) })
        (Tower.tower-out W q (subst (λ u → ⟨ fst q ∈ u ⟩) qE q∈)))

  holds : ⟨ γ ⊨ codesAt C w E N ⟩
  holds = shape , close
```

The table. `T` is the satisfaction table: a set of pairs `(c, yc)`, `c` a key in
`C`, one at every key, whose values obey the ten clauses. Each clause is
stated at the frame
`yc ∷ s''' ∷ e ∷ r ∷ s'' ∷ p ∷ s' ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ` (12 + m), read off
`(ar, F) ∈ E`, `c = (ar, p) ∈ C`, `p = (N k, r)` and `(c, yc) ∈ T`, and says
what `yc` is: the members of `F` with the property the constructor gives, in the
value polarity of `extB`.

`y` is exactly the set of members of `F` satisfying `φ`.

```agda
extB : ∀ {j} → Fin j → Fin j → Formula S (1 + j) → Formula S j
extB y F φ = ∀̇∈ (var y) ((var i0 ∈̇ var (sh 1 F)) ∧̇ φ)
           ∧̇ ∀̇∈ (var F) (φ ⇒̇ (var i0 ∈̇ var (sh 1 y)))
```

The first component, universally.

```agda
fstAll : ∀ {j} → Fin j → Fin j → Formula S (2 + j) → Formula S j
fstAll x v body = ∀̇∈ (var x) (∀̇∈ (var i0) (prAtL (sh 2 x) i0 (sh 2 v) ⇒̇ body))
```

The value at the subkey `(ar, a)`: every entry `(c₁, ya)` of `T` with
`c₁ = (ar, a)`, body at `ya ∷ c₁ ∷ s ∷ e' ∷ γ`.

```agda
subAt : ∀ {j} → Fin j → Fin j → Fin j → Formula S (4 + j) → Formula S j
subAt T ar a body = ∀̇∈ (var T) (bothAll i0 (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body))
```

The value at the subkey `(suc ar, a)`: body at
`ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ γ`.

```agda
subSucAt : ∀ {j} → Fin j → Fin j → Fin j → Formula S (6 + j) → Formula S j
subSucAt T ar a body =
  ∀̇∈ (var T) (bothAll i0 (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)))
```

`v` is the value of the term code `t` in the environment `z`: `t` is the
constant `v`, or `t` is the variable `i` and `(i, v)` is an entry of `z`.

```agda
tmIs : ∀ {j} → Fin j → Fin j → Fin j → Fin j → Fin j → Formula S j
tmIs t z v N0 N1 =
  prAtL t N0 v ∨̇ sndEx t N1 (∃̇∈ (var (sh 2 z)) (prAtL i0 i1 (sh 3 v)))
```

The ten relations, at the frame (12 + m): `yc` at `i0`, `r` at `i3`, `F` at
`i8`, `ar` at `i9`. Each relation binds its subvalues and ends in an extension
fact whose body is named, so that a reader can hand the body back at the frame
it was read in.

```agda
module Rel {m : ℕ} (T w : Fin m) (N : Fin 10 → Fin m) where
  private
    N0 N1 : ∀ {j} → Fin (j + m)
    N0 {j} = sh j (N f0)
    N1 {j} = sh j (N f1)
```

At `z ∷ yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ frame`: `ya` at
`i5`, `yb` at `i1`.

```agda
  binBody : (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (24 + m)
  binBody op = op (var i0 ∈̇ var i5) (var i0 ∈̇ var i1)
```

At `z ∷ ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ frame`: `ya` at `i3`, `w` at `sh 19 w`.

```agda
  quBody : (∀ {j} → Term S j → Formula S (suc j) → Formula S j) → Formula S (19 + m)
  quBody q = q (var (sh 19 w)) (∃̇∈ (var i4) (consAtL i0 i1 i2))
```

At `z ∷ ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ frame`: `ya` at `i3`, `t` at
`i8`, `w` at `sh 22 w`.

```agda
  bqBody : (∀ {j} → Term S j → Formula S (suc j) → Formula S j)
         → (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (22 + m)
  bqBody q c =
    q (var (sh 22 w)) (c (tmIs i9 i1 i0 N0 N1)
      (q (var (sh 23 w)) (c (var i0 ∈̇ var i1) (∃̇∈ (var i5) (consAtL i0 i1 i3)))))
```

At `z ∷ u ∷ t ∷ s ∷ frame`: `u` at `i1`, `t` at `i2`, `w` at `sh 16 w`; `rel` at
`x ∷ v ∷ z ∷ u ∷ t ∷ s ∷ frame`, `v` at `i1`, `x` at `i0`.

```agda
  atomBody : Formula S (18 + m) → Formula S (16 + m)
  atomBody rel =
    ∃̇∈ (var (sh 16 w)) (∃̇∈ (var (sh 17 w))
      (tmIs i4 i2 i1 N0 N1 ∧̇ (tmIs i3 i2 i0 N0 N1 ∧̇ rel)))

  botRel : Formula S (12 + m)
  botRel = extB i0 i8 ⊥̇

  binRel : (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (12 + m)
  binRel op =
    bothAll i3 (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (binBody op))))

  quRel : (∀ {j} → Term S j → Formula S (suc j) → Formula S j) → Formula S (12 + m)
  quRel q = subSucAt (sh 12 T) i9 i3 (extB i6 i14 (quBody q))

  bqRel : (∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → (∀ {j} → Formula S j → Formula S j → Formula S j) → Formula S (12 + m)
  bqRel q c = bothAll i3 (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (bqBody q c)))

  atomRel : Formula S (18 + m) → Formula S (12 + m)
  atomRel rel = bothAll i3 (extB i3 i11 (atomBody rel))

  relN : ℕ → Formula S (12 + m)
  relN 0 = atomRel (var i1 ∈̇ var i0)
  relN 1 = atomRel (var i1 ≐ var i0)
  relN 2 = binRel _∧̇_
  relN 3 = binRel _∨̇_
  relN 4 = binRel _⇒̇_
  relN 5 = botRel
  relN 6 = quRel ∃̇∈
  relN 7 = quRel ∀̇∈
  relN 8 = bqRel ∀̇∈ _⇒̇_
  relN 9 = bqRel ∃̇∈ _∧̇_
  relN (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = ⊤̇
```

The frame, and the clauses.

```agda
module Clause {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) where
  private
    module R = Rel T w N

  clause : Fin 10 → Formula S m
  clause k =
    ∀̇∈ (var E) (bothAll i0 (∀̇∈ (var (sh 4 C)) (sndAll i0 i2 (sndAll i0 (sh 7 (N k))
      (∀̇∈ (var (sh 9 T)) (sndAll i0 i5 (R.relN (toℕ k))))))))
```

Every key has an entry, and every entry is at a key.

```agda
  total onC : Formula S m
  total = ∀̇∈ (var C) (∃̇∈ (var (sh 1 T)) (sndEx i0 i1 ⊤̇))
  onC = ∀̇∈ (var T) (bothEx i0 (var i1 ∈̇ var (sh 4 C)))

  ten : Formula S m
  ten = bigAnd 9 clause

tableAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → (Fin 10 → Fin m) → Formula S m
tableAt T w C E N = Clause.total T w C E N ∧̇ (Clause.onC T w C E N ∧̇ Clause.ten T w C E N)

Δ₀-tableAt : ∀ {m} (T w C E : Fin m) (N : Fin 10 → Fin m) → Δ₀ (tableAt T w C E N)
Δ₀-tableAt T w C E N = checkΔ₀ (tableAt T w C E N) tt
```

The table, read. The frame and the subvalue macros are read at variable
environments; each relation is read to an extension fact whose condition is the
relation's own body at the frame the reader makes.

`y` is exactly the members of `F` with the property `P`.

```agda
ExtFact : (y F : V ℓ) (P : S → Type (ℓ-suc ℓ)) → Type (ℓ-suc ℓ)
ExtFact y F P = ((z : S) → ⟨ fst z ∈ y ⟩ → ⟨ fst z ∈ F ⟩ × P z)
              × ((z : S) → ⟨ fst z ∈ F ⟩ → P z → ⟨ fst z ∈ y ⟩)

module _ {j : ℕ} (y F : Fin j) (φ : Formula S (1 + j)) (δ : S ^ j) where
  extB-out : ⟨ δ ⊨ extB y F φ ⟩ → ExtFact (fst (lookup y δ)) (fst (lookup F δ)) (λ z → ⟨ (z ∷ δ) ⊨ φ ⟩)
  extB-out h = h

  extB-in : ExtFact (fst (lookup y δ)) (fst (lookup F δ)) (λ z → ⟨ (z ∷ δ) ⊨ φ ⟩) → ⟨ δ ⊨ extB y F φ ⟩
  extB-in h = h
```

Two extension facts with the same condition name the same set.

```agda
ext-unique : (y y' F : S) (P : S → Type (ℓ-suc ℓ))
           → ExtFact (fst y) (fst F) P → ExtFact (fst y') (fst F) P → fst y ≡ fst y'
ext-unique y y' F P (o1 , i1') (o2 , i2') =
  cong fst (extensionalL {a = y} {b = y'} (λ z → ⇔toPath
    (λ hz → i2' z (o1 z hz .fst) (o1 z hz .snd))
    (λ hz → i1' z (o2 z hz .fst) (o2 z hz .snd))))
```

The subvalue macros, read.

```agda
module _ {j : ℕ} (T ar a : Fin j) (body : Formula S (4 + j)) (δ : S ^ j) where
  private
    Tv = fst (lookup T δ)
    TS = lookup T δ
    A = fst (lookup ar δ)
    Av = fst (lookup a δ)

  subAt-out : ⟨ δ ⊨ subAt T ar a body ⟩ → (c₁ ya : S) (m : ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩)
            → fst c₁ ≡ pr A Av
            → ⟨ (ya ∷ c₁ ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
                 ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) ⊨ body ⟩
  subAt-out h c₁ ya m e =
    useBoth i0 (down TS (pr (fst c₁) (fst ya)) m ∷ δ) c₁ ya refl (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body)
      (h (down TS (pr (fst c₁) (fst ya)) m) m)
      (pr-in i1 (sh 4 ar) (sh 4 a)
        (ya ∷ c₁ ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
           ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) e)

  subAt-in : ((c₁ ya s e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr A Av
              → ⟨ (ya ∷ c₁ ∷ s ∷ e' ∷ δ) ⊨ body ⟩)
           → ⟨ δ ⊨ subAt T ar a body ⟩
  subAt-in g e' e'∈ = bothAll-in i0 (prAtL i1 (sh 4 ar) (sh 4 a) ⇒̇ body) (e' ∷ δ)
    (λ c₁ ya s s∈ c₁∈ ya∈ e hp → g c₁ ya s e' e'∈ e (pr-out i1 (sh 4 ar) (sh 4 a) (ya ∷ c₁ ∷ s ∷ e' ∷ δ) hp))

module _ {j : ℕ} (T ar a : Fin j) (body : Formula S (6 + j)) (δ : S ^ j) where
  private
    Tv = fst (lookup T δ)
    TS = lookup T δ
    A = fst (lookup ar δ)
    Av = fst (lookup a δ)

  subSucAt-out : ⟨ δ ⊨ subSucAt T ar a body ⟩ → (c₁ ya ar' : S) (m : ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩)
               → (e : fst c₁ ≡ pr (fst ar') Av) → fst ar' ≡ sucV A
               → ⟨ (ar' ∷ container c₁ ar' (lookup a δ) e .fst ∷ ya ∷ c₁
                    ∷ container (down TS (pr (fst c₁) (fst ya)) m) c₁ ya refl .fst
                    ∷ down TS (pr (fst c₁) (fst ya)) m ∷ δ) ⊨ body ⟩
  subSucAt-out h c₁ ya ar' m e es =
    (h4 (container c₁ ar' (lookup a δ) e .fst) (container c₁ ar' (lookup a δ) e .snd .fst)
        ar' (container c₁ ar' (lookup a δ) e .snd .snd .fst)
        (pr-in (sh 2 i1) i0 (sh 2 (sh 4 a)) δ6 e))
      (suc-in (sh 6 ar) i0 δ6 es)
    where
    e'S = down TS (pr (fst c₁) (fst ya)) m
    δ4 : S ^ (4 + j)
    δ4 = ya ∷ c₁ ∷ container e'S c₁ ya refl .fst ∷ e'S ∷ δ
    δ6 : S ^ (6 + j)
    δ6 = ar' ∷ container c₁ ar' (lookup a δ) e .fst ∷ δ4
    h4 : ⟨ δ4 ⊨ fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body) ⟩
    h4 = useBoth i0 (e'S ∷ δ) c₁ ya refl (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)) (h e'S m)

  subSucAt-in : ((c₁ ya ar' s s' e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
                 → fst c₁ ≡ pr (fst ar') Av → fst ar' ≡ sucV A
                 → ⟨ (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) ⊨ body ⟩)
              → ⟨ δ ⊨ subSucAt T ar a body ⟩
  subSucAt-in g e' e'∈ = bothAll-in i0 (fstAll i1 (sh 4 a) (sucAtL (sh 6 ar) i0 ⇒̇ body)) (e' ∷ δ)
    (λ c₁ ya s s∈ c₁∈ ya∈ e s' s'∈ ar' ar'∈ hp hs →
      g c₁ ya ar' s s' e' e'∈ e
        (pr-out (sh 2 i1) i0 (sh 2 (sh 4 a)) (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) hp)
        (suc-out (sh 6 ar) i0 (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) hs))
```

The term value, read.

```agda
TmIsV : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
TmIsV t z v = ∥ (t ≡ pr (# 0) v) ⊎ (Σ[ i ∈ V ℓ ] ((t ≡ pr (# 1) i) × ⟨ pr i v ∈ z ⟩)) ∥₁

module _ {j : ℕ} (t z v N0 N1 : Fin j) (δ : S ^ j)
  (q0 : fst (lookup N0 δ) ≡ # 0) (q1 : fst (lookup N1 δ) ≡ # 1) where
  private
    Tv = fst (lookup t δ)
    Z = fst (lookup z δ)
    Vv = fst (lookup v δ)
    N1v = fst (lookup N1 δ)

    inner : Formula S (2 + j)
    inner = ∃̇∈ (var (sh 2 z)) (prAtL i0 i1 (sh 3 v))

    Inner : (i s : S) → Type (ℓ-suc ℓ)
    Inner i s = ∥ Σ[ q ∈ S ] (⟨ fst q ∈ Z ⟩ × ⟨ (q ∷ i ∷ s ∷ δ) ⊨ prAtL i0 i1 (sh 3 v) ⟩) ∥₁

    Outer : Type (ℓ-suc ℓ)
    Outer = ∥ Σ[ i ∈ S ] Σ[ s ∈ S ] ((Tv ≡ pr N1v (fst i)) × ⟨ (i ∷ s ∷ δ) ⊨ inner ⟩) ∥₁

    viaQ : (i s : S) → Tv ≡ pr N1v (fst i) → Inner i s → TmIsV Tv Z Vv
    viaQ i s e = PT.map
      (λ { (q , (q∈ , hp)) → inr (fst i , ( e ∙ cong (λ a → pr a (fst i)) q1
         , subst (λ u → ⟨ u ∈ Z ⟩) (pr-out i0 i1 (sh 3 v) (q ∷ i ∷ s ∷ δ) hp) q∈ )) })

    viaI : Outer → TmIsV Tv Z Vv
    viaI = PT.rec squash₁ (λ { (i , s , (e , hq)) → viaQ i s e hq })

    cases : ⟨ δ ⊨ prAtL t N0 v ⟩ ⊎ ⟨ δ ⊨ sndEx t N1 inner ⟩ → TmIsV Tv Z Vv
    cases (inl h) = ∣ inl (pr-out t N0 v δ h ∙ cong (λ a → pr a Vv) q0) ∣₁
    cases (inr h) = viaI (sndEx-out t N1 inner δ h)

  tmIs-out : ⟨ δ ⊨ tmIs t z v N0 N1 ⟩ → TmIsV Tv Z Vv
  tmIs-out h = PT.rec squash₁ cases h

  private
    build : (Tv ≡ pr (# 0) Vv) ⊎ (Σ[ i ∈ V ℓ ] ((Tv ≡ pr (# 1) i) × ⟨ pr i Vv ∈ Z ⟩))
          → ⟨ δ ⊨ tmIs t z v N0 N1 ⟩
    build (inl e) = ∣ inl (pr-in t N0 v δ (e ∙ cong (λ a → pr a Vv) (sym q0))) ∣₁
    build (inr (i , (e , hp))) = ∣ inr (fillSnd t δ (lookup N1 δ) iS e' inner hq N1 refl) ∣₁
      where
      iS : S
      iS = sndS (lookup t δ) (# 1) i e
      qS : S
      qS = down (lookup z δ) (pr i Vv) hp
      e' : Tv ≡ pr N1v (fst iS)
      e' = e ∙ cong (λ a → pr a i) (sym q1)
      δ3 : S ^ (3 + j)
      δ3 = qS ∷ iS ∷ container (lookup t δ) (lookup N1 δ) iS e' .fst ∷ δ
      hq : ⟨ (iS ∷ container (lookup t δ) (lookup N1 δ) iS e' .fst ∷ δ) ⊨ inner ⟩
      hq = ∣ qS , (hp , pr-in i0 i1 (sh 3 v) δ3 refl) ∣₁

  tmIs-in : TmIsV Tv Z Vv → ⟨ δ ⊨ tmIs t z v N0 N1 ⟩
  tmIs-in = PT.rec (snd (δ ⊨ tmIs t z v N0 N1)) build
```

The frame, read. The ten-slot frame at the data of an entry.

```agda
module Frame {m : ℕ} (T w C E : Fin m) (N : Fin 10 → Fin m) (γ : S ^ m) (tg : Tags γ N) where
  private
    Tv = fst (lookup T γ)
    Cv = fst (lookup C γ)
    Ev = fst (lookup E γ)
    module Cl = Clause T w C E N
    module R = Rel T w N
    inner9 : Fin 10 → Formula S (9 + m)
    inner9 k = ∀̇∈ (var (sh 9 T)) (sndAll i0 i5 (R.relN (toℕ k)))
    inner7 : Fin 10 → Formula S (7 + m)
    inner7 k = sndAll i0 (sh 7 (N k)) (inner9 k)
    inner4 : Fin 10 → Formula S (4 + m)
    inner4 k = ∀̇∈ (var (sh 4 C)) (sndAll i0 i2 (inner7 k))
```

The frame environment of an entry, with its containers.

```agda
  module At (ar F c p r yc : S) (q∈ : ⟨ pr (fst ar) (fst F) ∈ Ev ⟩)
            (ec : fst c ≡ pr (fst ar) (fst p)) (k : Fin 10)
            (ep : fst p ≡ pr (fst (lookup (N k) γ)) (fst r))
            (e∈ : ⟨ pr (fst c) (fst yc) ∈ Tv ⟩) where
    qS eS : S
    qS = down (lookup E γ) (pr (fst ar) (fst F)) q∈
    eS = down (lookup T γ) (pr (fst c) (fst yc)) e∈

    δ4 : S ^ (4 + m)
    δ4 = F ∷ ar ∷ container qS ar F refl .fst ∷ qS ∷ γ
    δ7 : S ^ (7 + m)
    δ7 = p ∷ container c ar p ec .fst ∷ c ∷ δ4
    δ9 : S ^ (9 + m)
    δ9 = r ∷ container p (lookup (N k) γ) r ep .fst ∷ δ7
    δ12 : S ^ (12 + m)
    δ12 = yc ∷ container eS c yc refl .fst ∷ eS ∷ δ9

  clause-out : (k : Fin 10) → ⟨ γ ⊨ Cl.clause k ⟩
             → (ar F c p r yc : S) (q∈ : ⟨ pr (fst ar) (fst F) ∈ Ev ⟩) → ⟨ fst c ∈ Cv ⟩
             → (ec : fst c ≡ pr (fst ar) (fst p)) → (ep : fst p ≡ pr (# (toℕ k)) (fst r))
             → (e∈ : ⟨ pr (fst c) (fst yc) ∈ Tv ⟩)
             → ⟨ At.δ12 ar F c p r yc q∈ ec k (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) e∈ ⊨ R.relN (toℕ k) ⟩
  clause-out k h ar F c p r yc q∈ c∈ ec ep e∈ =
    useSnd i0 (A.eS ∷ A.δ9) c yc refl (R.relN (toℕ k)) i5 refl (h9 A.eS e∈)
    where
    module A = At ar F c p r yc q∈ ec k (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) e∈
    h4 : ⟨ A.δ4 ⊨ inner4 k ⟩
    h4 = useBoth i0 (A.qS ∷ γ) ar F refl (inner4 k) (h A.qS q∈)
    h7 : ⟨ A.δ7 ⊨ inner7 k ⟩
    h7 = useSnd i0 (c ∷ A.δ4) ar p ec (inner7 k) i2 refl (h4 c c∈)
    h9 : ⟨ A.δ9 ⊨ inner9 k ⟩
    h9 = useSnd i0 A.δ7 (lookup (N k) γ) r (ep ∙ cong (λ a → pr a (fst r)) (sym (tg k))) (inner9 k) (sh 7 (N k)) refl h7

  clause-in : (k : Fin 10)
            → ((q ar F s c p s1 r s2 e yc s3 : S) → ⟨ fst q ∈ Ev ⟩ → fst q ≡ pr (fst ar) (fst F)
               → ⟨ fst c ∈ Cv ⟩ → fst c ≡ pr (fst ar) (fst p) → fst p ≡ pr (# (toℕ k)) (fst r)
               → ⟨ fst e ∈ Tv ⟩ → fst e ≡ pr (fst c) (fst yc)
               → ⟨ (yc ∷ s3 ∷ e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) ⊨ R.relN (toℕ k) ⟩)
            → ⟨ γ ⊨ Cl.clause k ⟩
  clause-in k g q q∈ = bothAll-in i0 (inner4 k) (q ∷ γ) (λ ar F s s∈ ar∈ F∈ eq c c∈ →
    sndAll-in i0 i2 (inner7 k) (c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ p s1 s1∈ p∈ ec →
      sndAll-in i0 (sh 7 (N k)) (inner9 k) (p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ r s2 s2∈ r∈ ep e e∈ →
        sndAll-in i0 i5 (R.relN (toℕ k)) (e ∷ r ∷ s2 ∷ p ∷ s1 ∷ c ∷ F ∷ ar ∷ s ∷ q ∷ γ) (λ yc s3 s3∈ yc∈ ee →
          g q ar F s c p s1 r s2 e yc s3 q∈ eq c∈ ec (ep ∙ cong (λ a → pr a (fst r)) (tg k)) e∈ ee))))
```

Totality and the domain.

```agda
  total-out : ⟨ γ ⊨ Cl.total ⟩ → (c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁
  total-out h c c∈ = PT.rec squash₁
    (λ { (e , (e∈ , hs)) → PT.map
      (λ { (yc , s , (ee , _)) → yc , subst (λ u → ⟨ u ∈ Tv ⟩) ee e∈ })
      (sndEx-out i0 i1 ⊤̇ (e ∷ c ∷ γ) hs) })
    (h c c∈)

  total-in : ((c : S) → ⟨ fst c ∈ Cv ⟩ → ∥ Σ[ yc ∈ S ] ⟨ pr (fst c) (fst yc) ∈ Tv ⟩ ∥₁) → ⟨ γ ⊨ Cl.total ⟩
  total-in g c c∈ = PT.map
    (λ { (yc , m) → down (lookup T γ) (pr (fst c) (fst yc)) m
       , ( m , fillSnd i0 (down (lookup T γ) (pr (fst c) (fst yc)) m ∷ c ∷ γ) c yc refl ⊤̇ (λ b → b) i1 refl ) })
    (g c c∈)

  onC-out : ⟨ γ ⊨ Cl.onC ⟩ → (e : S) → ⟨ fst e ∈ Tv ⟩
          → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁
  onC-out h e e∈ = PT.map (λ { (c , yc , s , (ee , c∈)) → c , yc , (ee , c∈) })
    (bothEx-out i0 (var i1 ∈̇ var (sh 4 C)) (e ∷ γ) (h e e∈))

  onC-in : ((e : S) → ⟨ fst e ∈ Tv ⟩ → ∥ Σ[ c ∈ S ] Σ[ yc ∈ S ] ((fst e ≡ pr (fst c) (fst yc)) × ⟨ fst c ∈ Cv ⟩) ∥₁)
         → ⟨ γ ⊨ Cl.onC ⟩
  onC-in g e e∈ = PT.rec (snd ((e ∷ γ) ⊨ bothEx i0 (var i1 ∈̇ var (sh 4 C))))
    (λ { (c , yc , (ee , c∈)) → fillBoth i0 (e ∷ γ) c yc ee (var i1 ∈̇ var (sh 4 C)) c∈ })
    (g e e∈)
```

The relations, read. Each reader hands back the extension fact at the body's own
frame; the junk slots are existential going out and universal coming in.

```agda
module RelRead {m : ℕ} (T w : Fin m) (N : Fin 10 → Fin m) (δ : S ^ (12 + m)) where
  private
    module R = Rel T w N
    yc = lookup i0 δ
    r = lookup i3 δ
    F = lookup i8 δ
    ar = lookup i9 δ
    Tv = fst (lookup (sh 12 T) δ)
    A = fst ar
    Rv = fst r
```

The extension fact of `yc` in `F` with the body at a frame.

```agda
  Ext : ∀ {k} (env : S ^ k) (φ : Formula S (1 + k)) → Type (ℓ-suc ℓ)
  Ext env φ = ExtFact (fst yc) (fst F) (λ z → ⟨ (z ∷ env) ⊨ φ ⟩)
```

The binary connectives.

```agda
  bin-out : (op : ∀ {j} → Formula S j → Formula S j → Formula S j) → ⟨ δ ⊨ R.binRel op ⟩
          → (a b c₁ ya c₂ yb : S) → Rv ≡ pr (fst a) (fst b)
          → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr A (fst a)
          → ⟨ pr (fst c₂) (fst yb) ∈ Tv ⟩ → fst c₂ ≡ pr A (fst b)
          → ∥ Σ[ s ∈ S ] Σ[ s₁ ∈ S ] Σ[ e₁ ∈ S ] Σ[ s₂ ∈ S ] Σ[ e₂ ∈ S ]
              Ext (yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ) (R.binBody op) ∥₁
  bin-out op h a b c₁ ya c₂ yb er m₁ e₁ m₂ e₂ =
    ∣ container r a b er .fst , container e₁S c₁ ya refl .fst , e₁S , container e₂S c₂ yb refl .fst , e₂S ,
      subAt-out (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)) δ19
        (subAt-out (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op))) δ15
          (useBoth i3 δ a b er (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)))) h)
          c₁ ya m₁ e₁)
        c₂ yb m₂ e₂ ∣₁
    where
    δ15 : S ^ (15 + m)
    δ15 = b ∷ a ∷ container r a b er .fst ∷ δ
    e₁S : S
    e₁S = down (lookup (sh 15 T) δ15) (pr (fst c₁) (fst ya)) m₁
    δ19 : S ^ (19 + m)
    δ19 = ya ∷ c₁ ∷ container e₁S c₁ ya refl .fst ∷ e₁S ∷ δ15
    e₂S : S
    e₂S = down (lookup (sh 19 T) δ19) (pr (fst c₂) (fst yb)) m₂

  bin-in : (op : ∀ {j} → Formula S j → Formula S j → Formula S j)
         → ((a b s c₁ ya s₁ e₁ c₂ yb s₂ e₂ : S) → Rv ≡ pr (fst a) (fst b)
            → ⟨ fst e₁ ∈ Tv ⟩ → fst e₁ ≡ pr (fst c₁) (fst ya) → fst c₁ ≡ pr A (fst a)
            → ⟨ fst e₂ ∈ Tv ⟩ → fst e₂ ≡ pr (fst c₂) (fst yb) → fst c₂ ≡ pr A (fst b)
            → Ext (yb ∷ c₂ ∷ s₂ ∷ e₂ ∷ ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ) (R.binBody op))
         → ⟨ δ ⊨ R.binRel op ⟩
  bin-in op g = bothAll-in i3 (subAt (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)))) δ
    (λ a b s s∈ a∈ b∈ er →
      subAt-in (sh 15 T) i12 i1 (subAt (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op))) (b ∷ a ∷ s ∷ δ)
        (λ c₁ ya s₁ e₁ e₁∈ ee₁ e₁' →
          subAt-in (sh 19 T) i16 i4 (extB i11 i19 (R.binBody op)) (ya ∷ c₁ ∷ s₁ ∷ e₁ ∷ b ∷ a ∷ s ∷ δ)
            (λ c₂ yb s₂ e₂ e₂∈ ee₂ e₂' →
              g a b s c₁ ya s₁ e₁ c₂ yb s₂ e₂ er e₁∈ ee₁ e₁' e₂∈ ee₂ e₂')))
```

The unbounded quantifiers.

```agda
  qu-out : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j) → ⟨ δ ⊨ R.quRel q ⟩
         → (c₁ ya ar' : S) → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr (fst ar') Rv → fst ar' ≡ sucV A
         → ∥ Σ[ s ∈ S ] Σ[ s' ∈ S ] Σ[ e' ∈ S ] Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) (R.quBody q) ∥₁
  qu-out q h c₁ ya ar' mem e es =
    ∣ container e'S c₁ ya refl .fst , container c₁ ar' r e .fst , e'S
    , subSucAt-out (sh 12 T) i9 i3 (extB i6 i14 (R.quBody q)) δ h c₁ ya ar' mem e es ∣₁
    where
    e'S : S
    e'S = down (lookup (sh 12 T) δ) (pr (fst c₁) (fst ya)) mem

  qu-in : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → ((c₁ ya ar' s s' e' : S) → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
           → fst c₁ ≡ pr (fst ar') Rv → fst ar' ≡ sucV A
           → Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s ∷ e' ∷ δ) (R.quBody q))
        → ⟨ δ ⊨ R.quRel q ⟩
  qu-in q g = subSucAt-in (sh 12 T) i9 i3 (extB i6 i14 (R.quBody q)) δ g
```

The bounded quantifiers.

```agda
  bq-out : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
         → (c : ∀ {j} → Formula S j → Formula S j → Formula S j) → ⟨ δ ⊨ R.bqRel q c ⟩
         → (t a c₁ ya ar' : S) → Rv ≡ pr (fst t) (fst a)
         → ⟨ pr (fst c₁) (fst ya) ∈ Tv ⟩ → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
         → ∥ Σ[ s ∈ S ] Σ[ s₁ ∈ S ] Σ[ s' ∈ S ] Σ[ e' ∈ S ]
             Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ δ) (R.bqBody q c) ∥₁
  bq-out q c h t a c₁ ya ar' er mem e es =
    ∣ container r t a er .fst , container e'S c₁ ya refl .fst , container c₁ ar' a e .fst , e'S ,
      subSucAt-out (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c)) δ15
        (useBoth i3 δ t a er (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c))) h)
        c₁ ya ar' mem e es ∣₁
    where
    δ15 : S ^ (15 + m)
    δ15 = a ∷ t ∷ container r t a er .fst ∷ δ
    e'S : S
    e'S = down (lookup (sh 15 T) δ15) (pr (fst c₁) (fst ya)) mem

  bq-in : (q : ∀ {j} → Term S j → Formula S (suc j) → Formula S j)
        → (c : ∀ {j} → Formula S j → Formula S j → Formula S j)
        → ((t a s c₁ ya ar' s₁ s' e' : S) → Rv ≡ pr (fst t) (fst a)
           → ⟨ fst e' ∈ Tv ⟩ → fst e' ≡ pr (fst c₁) (fst ya)
           → fst c₁ ≡ pr (fst ar') (fst a) → fst ar' ≡ sucV A
           → Ext (ar' ∷ s' ∷ ya ∷ c₁ ∷ s₁ ∷ e' ∷ a ∷ t ∷ s ∷ δ) (R.bqBody q c))
        → ⟨ δ ⊨ R.bqRel q c ⟩
  bq-in q c g = bothAll-in i3 (subSucAt (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c))) δ
    (λ t a s s∈ t∈ a∈ er →
      subSucAt-in (sh 15 T) i12 i0 (extB i9 i17 (R.bqBody q c)) (a ∷ t ∷ s ∷ δ)
        (λ c₁ ya ar' s₁ s' e' e'∈ ee e es → g t a s c₁ ya ar' s₁ s' e' er e'∈ ee e es))
```

The atoms.

```agda
  atom-out : (rel : Formula S (18 + m)) → ⟨ δ ⊨ R.atomRel rel ⟩
           → (t u : S) → Rv ≡ pr (fst t) (fst u)
           → ∥ Σ[ s ∈ S ] Ext (u ∷ t ∷ s ∷ δ) (R.atomBody rel) ∥₁
  atom-out rel h t u er = ∣ container r t u er .fst , useBoth i3 δ t u er (extB i3 i11 (R.atomBody rel)) h ∣₁

  atom-in : (rel : Formula S (18 + m))
          → ((t u s : S) → Rv ≡ pr (fst t) (fst u) → Ext (u ∷ t ∷ s ∷ δ) (R.atomBody rel))
          → ⟨ δ ⊨ R.atomRel rel ⟩
  atom-in rel g = bothAll-in i3 (extB i3 i11 (R.atomBody rel)) δ (λ t u s s∈ t∈ u∈ er → g t u s er)
```

The bridge to the meta-level value. For every constructor, the value
src/L/Coding/Sat.lagda.md builds is the extension of the clause's body over the
environment set: each bridge is `Sat-mem` read back, with the term and cons
readers carried between the clause's frame and the recursion's.

```agda
open import L.Coding.Sat {ℓ} lem using
  ( Sat; Sat-mem; cond )
open import L.Coding.Bridge {ℓ} lem using ( asConst )
import L.Coding.Bridge {ℓ} lem as Semantic
open import Cubical.Data.Nat using ( znots; snotz )
open import Cubical.Data.FinData using ( toℕ )

module Bridge (W : S) where
  open Alphabet W
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ( _⊓_; _⊔_; _⇒_ )
  private
    module DB = Semantic.DB W
    module Sem = Semantic.SemB W
    open Sem.At DB.SM id using () renaming ( _⊨_ to _⊨ᴮ_ ; ⟦_⟧ to ⟦_⟧ᴮ )

    Meaning : ∀ {n} → Formula Ab n → DB.SM ^ n → hProp (ℓ-suc ℓ)
    Meaning ψ δ = δ ⊨ᴮ mapFo DB.ι ψ

  private
    Wv = fst W

  toS : ∀ {n} → Formula Ab n → Formula S n
  toS = mapFo (asConst W)

  SatW : ∀ {n} → Formula Ab n → S
  SatW ψ = Sat W (toS ψ)
```

An environment over `W` is recovered as a vector of members by
`envSet-vectors` in src/L/Coding/Bridge.lagda.md. Its term values therefore lie
in `W`, and its extension is the graph of the vector with one member prepended.
The same chapter identifies membership in the recursion's value with satisfaction
at this vector, so the clause readers can use that interpretation directly.

The recursion's value, read.

```agda
  Sat-out : ∀ {n} (ψ : Formula Ab n) (z : S) → ⟨ fst z ∈ fst (SatW ψ) ⟩
          → ⟨ fst z ∈ fst (envSet W n) ⟩ × ⟨ (z ∷ []) ⊨ cond W (toS ψ) ⟩
  Sat-out ψ z h = subst ⟨_⟩ (Sat-mem W (toS ψ) z) h

  Sat-in : ∀ {n} (ψ : Formula Ab n) (z : S) → ⟨ fst z ∈ fst (envSet W n) ⟩
         → ⟨ (z ∷ []) ⊨ cond W (toS ψ) ⟩ → ⟨ fst z ∈ fst (SatW ψ) ⟩
  Sat-in ψ z hz hc = subst ⟨_⟩ (sym (Sat-mem W (toS ψ) z)) (hz , hc)
```

A pointwise reading of the recursion's condition determines its extension.
The environment witness is eliminated once for both directions.

```agda
  private
    extension-path : ∀ {n} (ψ : Formula Ab n) (P : S → hProp (ℓ-suc ℓ))
                   → ((z : S) → ((z ∷ []) ⊨ cond W (toS ψ)) ≡ P z)
                   → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ P z ⟩)
    extension-path ψ P e =
        (λ z hz → Sat-out ψ z hz .fst , subst ⟨_⟩ (e z) (Sat-out ψ z hz .snd))
      , (λ z hz hp → Sat-in ψ z hz (subst ⟨_⟩ (sym (e z)) hp))
```

The constant.

```agda
  botBridge : (n : ℕ) {k : ℕ} (env : S ^ k)
            → ExtFact (fst (SatW (⊥̇ {n = n}))) (fst (envSet W n)) (λ z → ⟨ (z ∷ env) ⊨ ⊥̇ ⟩)
  botBridge n env = (λ z hz → Sat-out ⊥̇ z hz .fst , Sat-out ⊥̇ z hz .snd) , (λ z hz b → Empty.rec* b)
```

The connectives, with the subvalues at slots.

```agda
  andBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
            → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
            → ExtFact (fst (SatW (a ∧̇ b))) (fst (envSet W n))
                (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∧̇ (var i0 ∈̇ var (suc yb)) ⟩)
  andBridge a b env ya yb qa qb = extension-path (a ∧̇ b)
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∧̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⊓ (fst z ∈ sym qb i))

  orBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
           → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
           → ExtFact (fst (SatW (a ∨̇ b))) (fst (envSet W n))
               (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∨̇ (var i0 ∈̇ var (suc yb)) ⟩)
  orBridge a b env ya yb qa qb = extension-path (a ∨̇ b)
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ∨̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⊔ (fst z ∈ sym qb i))

  impBridge : ∀ {n} (a b : Formula Ab n) {k : ℕ} (env : S ^ k) (ya yb : Fin k)
            → fst (lookup ya env) ≡ fst (SatW a) → fst (lookup yb env) ≡ fst (SatW b)
            → ExtFact (fst (SatW (a ⇒̇ b))) (fst (envSet W n))
                (λ z → ⟨ (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ⇒̇ (var i0 ∈̇ var (suc yb)) ⟩)
  impBridge a b env ya yb qa qb = extension-path (a ⇒̇ b)
    (λ z → (z ∷ env) ⊨ (var i0 ∈̇ var (suc ya)) ⇒̇ (var i0 ∈̇ var (suc yb)))
    (λ z i → (fst z ∈ sym qa i) ⇒ (fst z ∈ sym qb i))

```

The unbounded quantifiers. The body at `z`: for some/every `x` in `w`, some
member of `ya` is `cons x z`.

```agda
  quEx quAll : ∀ {k} → Fin k → Fin k → Formula S (1 + k)
  quEx wi yai = ∃̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2))
  quAll wi yai = ∀̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc yai))) (consAtL i0 i1 i2))
```

Recover the environment vector once, then read the clause as ordinary
satisfaction. A child value is the graph of the extended vector; its membership
in the recursive value is precisely satisfaction of the child formula.

```agda
  private
    direct-extension : ∀ {n} (ψ : Formula Ab n) (P : S → hProp (ℓ-suc ℓ))
      → ((δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ Meaning ψ δ ⟩ → ⟨ P z ⟩)
      → ((δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ P z ⟩ → ⟨ Meaning ψ δ ⟩)
      → ExtFact (fst (SatW ψ)) (fst (envSet W n)) (λ z → ⟨ P z ⟩)
    direct-extension {n} ψ P f b = out , inn
      where
      out : (z : S) → ⟨ fst z ∈ fst (SatW ψ) ⟩ → ⟨ fst z ∈ fst (envSet W n) ⟩ × ⟨ P z ⟩
      out z hz = Sat-out ψ z hz .fst , PT.rec (snd (P z))
        (λ { (δ , q) → f δ z q (subst ⟨_⟩ (Semantic.Sat-small-spec W ψ δ z q) hz) })
        (Semantic.envSet-vectors W z (Sat-out ψ z hz .fst))
      inn : (z : S) → ⟨ fst z ∈ fst (envSet W n) ⟩ → ⟨ P z ⟩ → ⟨ fst z ∈ fst (SatW ψ) ⟩
      inn z hz hp = PT.rec (snd (fst z ∈ fst (SatW ψ)))
        (λ { (δ , q) → subst ⟨_⟩ (sym (Semantic.Sat-small-spec W ψ δ z q)) (b δ z q hp) })
        (Semantic.envSet-vectors W z hz)

    child : ∀ {n k} (a : Formula Ab (suc n)) (δ : DB.SM ^ n) (x : DB.SM)
      (γ : S ^ k) (zi yai : Fin k) → fst (lookup zi γ) ≡ Semantic.graph W δ
      → fst (lookup yai γ) ≡ fst (SatW a)
      → ((Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)))
        ≡ Meaning a (x ∷ δ)
    child a δ x γ zi yai qz qa = ⇔toPath out inn
      where
      out : ⟨ (Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)) ⟩
          → ⟨ Meaning a (x ∷ δ) ⟩
      out = PT.rec (snd (Meaning a (x ∷ δ))) (λ { (e , he , hc) →
        subst ⟨_⟩ (Semantic.Sat-small-spec W a (x ∷ δ) e
          (Semantic.consAtL-out W δ x (e ∷ Semantic.intoL W x ∷ γ) i0 i1 (sh 2 zi) qz refl hc))
          (subst (λ X → ⟨ fst e ∈ X ⟩) qa he) })
      inn : ⟨ Meaning a (x ∷ δ) ⟩
          → ⟨ (Semantic.intoL W x ∷ γ) ⊨ ∃̇∈ (var (suc yai)) (consAtL i0 i1 (sh 2 zi)) ⟩
      inn h = ∣ Semantic.envFor W (x ∷ δ)
        , subst (λ X → ⟨ fst (Semantic.envFor W (x ∷ δ)) ∈ X ⟩) (sym qa)
          (subst ⟨_⟩ (sym (Semantic.Sat-small-spec W a (x ∷ δ) (Semantic.envFor W (x ∷ δ))
            (Semantic.envFor-graph W (x ∷ δ)))) h)
        , Semantic.consAtL-in W δ x (Semantic.envFor W (x ∷ δ) ∷ Semantic.intoL W x ∷ γ)
            i0 i1 (sh 2 zi) qz refl (Semantic.envFor-graph W (x ∷ δ)) ∣₁

  exBridge : ∀ {n} (a : Formula Ab (suc n)) {k : ℕ} (γ : S ^ k) (wi yai : Fin k)
           → fst (lookup wi γ) ≡ Wv → fst (lookup yai γ) ≡ fst (SatW a)
           → ExtFact (fst (SatW (∃̇ a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ γ) ⊨ quEx wi yai ⟩)
  exBridge a γ wi yai qw qa = direct-extension (∃̇ a) (λ z → (z ∷ γ) ⊨ quEx wi yai)
    (λ δ z qz → PT.map (λ { (x , h) → Semantic.intoL W x
      , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x)
      , subst ⟨_⟩ (sym (child a δ x (z ∷ γ) i0 (suc yai) qz qa)) h }))
    (λ δ z qz → PT.map (λ { (x , hx , h) → (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
      , subst ⟨_⟩ (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
        (z ∷ γ) i0 (suc yai) qz qa) h }))

  allBridge : ∀ {n} (a : Formula Ab (suc n)) {k : ℕ} (γ : S ^ k) (wi yai : Fin k)
            → fst (lookup wi γ) ≡ Wv → fst (lookup yai γ) ≡ fst (SatW a)
            → ExtFact (fst (SatW (∀̇ a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ γ) ⊨ quAll wi yai ⟩)
  allBridge a γ wi yai qw qa = direct-extension (∀̇ a) (λ z → (z ∷ γ) ⊨ quAll wi yai)
    (λ δ z qz h x hx → subst ⟨_⟩
      (sym (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx) (z ∷ γ) i0 (suc yai) qz qa))
      (h (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)))
    (λ δ z qz h x → subst ⟨_⟩ (child a δ x (z ∷ γ) i0 (suc yai) qz qa)
      (h (Semantic.intoL W x) (subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x))))
```

The bounded quantifiers. The body at `z`: for the value `v` of `t` at `z` and
some/every `x ∈ w` with `x ∈ v`, some member of `ya` is `cons x z`.

```agda
  bqAll bqEx : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S (1 + k)
  bqAll wi ti yai N0i N1i =
    ∀̇∈ (var (suc wi)) (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i))
      ⇒̇ ∀̇∈ (var (suc (suc wi))) ((var i0 ∈̇ var i1) ⇒̇ ∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3)))
  bqEx wi ti yai N0i N1i =
    ∃̇∈ (var (suc wi)) (tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i))
      ∧̇ ∃̇∈ (var (suc (suc wi))) ((var i0 ∈̇ var i1) ∧̇ ∃̇∈ (var (suc (suc (suc yai)))) (consAtL i0 i1 i3)))
```

The term readers at any frame and slots.

```agda
  private
    value : ∀ {n} → Term Ab n → DB.SM ^ n → DB.SM
    value t δ = ⟦ mapTm DB.ι t ⟧ᴮ δ

    term-out : ∀ {n} (t : Term Ab n) (δ : DB.SM ^ n) (z v : S)
      → fst z ≡ Semantic.graph W δ → TmIsV (ct t) (fst z) (fst v)
      → fst v ≡ fst (value t δ)
    term-out (con q) δ z v qz = PT.rec (setIsSet _ _)
      (λ { (inl e) → sym (pr-inj e .snd)
         ; (inr (i , e , _)) → Empty.rec (znots (#-inj′ {0} {1} (pr-inj e .fst))) })
    term-out (var i) δ z v qz = PT.rec (setIsSet _ _)
      (λ { (inl e) → Empty.rec (snotz (#-inj′ {1} {0} (pr-inj e .fst)))
         ; (inr (j , e , hp)) → subst ⟨_⟩ (lookup-spec (Semantic.values W δ) i (fst v))
             (subst2 (λ a E → ⟨ pr a (fst v) ∈ E ⟩) (sym (pr-inj e .snd)) qz hp) })

    term-in : ∀ {n} (t : Term Ab n) (δ : DB.SM ^ n) (z v : S)
      → fst z ≡ Semantic.graph W δ → fst v ≡ fst (value t δ)
      → TmIsV (ct t) (fst z) (fst v)
    term-in (con q) δ z v qz e = ∣ inl (cong (pr (# 0)) (sym e)) ∣₁
    term-in (var i) δ z v qz e = ∣ inr (# (toℕ i) , refl
      , subst (λ E → ⟨ pr (# (toℕ i)) (fst v) ∈ E ⟩) (sym qz)
          (subst ⟨_⟩ (sym (lookup-spec (Semantic.values W δ) i (fst v))) e)) ∣₁

  module BqBridge {n : ℕ} (t : Term Ab n) (a : Formula Ab (suc n)) {k : ℕ} (Γ : S ^ k)
    (wi ti yai N0i N1i : Fin k)
    (qw : fst (lookup wi Γ) ≡ Wv) (qt : fst (lookup ti Γ) ≡ ct t) (qa : fst (lookup yai Γ) ≡ fst (SatW a))
    (q0 : fst (lookup N0i Γ) ≡ # 0) (q1 : fst (lookup N1i Γ) ≡ # 1) where

    private
```

The term, read at `v ∷ z ∷ Γ` and carried to the recursion's frame.

```agda
      tmOut : (z v : S) → ⟨ (v ∷ z ∷ Γ) ⊨ tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) ⟩
            → TmIsV (ct t) (fst z) (fst v)
      tmOut z v h = subst (λ u → TmIsV u (fst z) (fst v)) qt
        (tmIs-out (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) (v ∷ z ∷ Γ) q0 q1 h)

      tmIn' : (z v : S) → TmIsV (ct t) (fst z) (fst v)
            → ⟨ (v ∷ z ∷ Γ) ⊨ tmIs (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) ⟩
      tmIn' z v h = tmIs-in (suc (suc ti)) i1 i0 (suc (suc N0i)) (suc (suc N1i)) (v ∷ z ∷ Γ) q0 q1
        (subst (λ u → TmIsV u (fst z) (fst v)) (sym qt) h)

      bound : DB.SM ^ n → S
      bound δ = Semantic.intoL W (value t δ)

      bound∈W : (δ : DB.SM ^ n) → ⟨ fst (bound δ) ∈ fst (lookup wi Γ) ⟩
      bound∈W δ = subst (λ X → ⟨ fst (value t δ) ∈ X ⟩)
        (sym qw) (snd (value t δ))

      bound-term : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
                 → TmIsV (ct t) (fst z) (fst (bound δ))
      bound-term δ z qz = term-in t δ z (bound δ) qz refl

      bound-read : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
                 → ⟨ (bound δ ∷ z ∷ Γ)
                     ⊨ tmIs (suc (suc ti)) i1 i0
                         (suc (suc N0i)) (suc (suc N1i)) ⟩
      bound-read δ z qz = tmIn' z (bound δ) (bound-term δ z qz)
```

The bound term has its semantic value in `W`. Both bounded quantifiers use
that value and the same child-satisfaction path as the unbounded quantifiers.

```agda
    allInBridge : ExtFact (fst (SatW (∀̇∈ t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ bqAll wi ti yai N0i N1i ⟩)
    allInBridge = direct-extension (∀̇∈ t a) (λ z → (z ∷ Γ) ⊨ bqAll wi ti yai N0i N1i)
      (λ δ z qz h v hv ht x hx hxv → subst ⟨_⟩
        (sym (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          (v ∷ z ∷ Γ) i1 (sh 2 yai) qz qa))
        (h (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          (subst (λ V → ⟨ fst x ∈ V ⟩) (term-out t δ z v qz (tmOut z v ht)) hxv)))
      (λ δ z qz h x hx → subst ⟨_⟩
        (child a δ x (bound δ ∷ z ∷ Γ) i1 (sh 2 yai) qz qa)
        (h (bound δ) (bound∈W δ) (bound-read δ z qz)
          (Semantic.intoL W x) (subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x)) hx))

    exInBridge : ExtFact (fst (SatW (∃̇∈ t a))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ bqEx wi ti yai N0i N1i ⟩)
    exInBridge = direct-extension (∃̇∈ t a) (λ z → (z ∷ Γ) ⊨ bqEx wi ti yai N0i N1i)
      (λ δ z qz → PT.map (λ { (x , hx , h) → bound δ
        , bound∈W δ
        , bound-read δ z qz
        , ∣ Semantic.intoL W x , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd x) , hx
            , subst ⟨_⟩ (sym (child a δ x (bound δ ∷ z ∷ Γ) i1 (sh 2 yai) qz qa)) h ∣₁ }))
      (λ δ z qz → PT.rec squash₁ (λ { (v , hv , ht , h) → PT.map
        (λ { (x , hx , hxv , hc) → (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
          , subst (λ V → ⟨ fst x ∈ V ⟩) (term-out t δ z v qz (tmOut z v ht)) hxv
          , subst ⟨_⟩ (child a δ (fst x , subst (λ X → ⟨ fst x ∈ X ⟩) qw hx)
              (v ∷ z ∷ Γ) i1 (sh 2 yai) qz qa) hc }) h }))
```

The atoms. The body at `z`: for the values `v`, `x` of `t`, `u` at `z`,
`v rel x`.

```agda
  atomEx : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S (3 + k) → Formula S (1 + k)
  atomEx wi ti ui N0i N1i rel =
    ∃̇∈ (var (suc wi)) (∃̇∈ (var (suc (suc wi)))
      (tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i)
        ∧̇ (tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ∧̇ rel)))

  module AtomBridge {n : ℕ} (t u : Term Ab n) {k : ℕ} (Γ : S ^ k)
    (wi ti ui N0i N1i : Fin k)
    (qw : fst (lookup wi Γ) ≡ Wv) (qt : fst (lookup ti Γ) ≡ ct t) (qu : fst (lookup ui Γ) ≡ ct u)
    (q0 : fst (lookup N0i Γ) ≡ # 0) (q1 : fst (lookup N1i Γ) ≡ # 1)
    (op : ∀ {j} → Term Ab j → Term Ab j → Formula Ab j)
    (R : V ℓ → V ℓ → Type (ℓ-suc ℓ))
    (rel : Formula S (3 + k))
    (agree : (z v x : S) → (⟨ (x ∷ v ∷ z ∷ Γ) ⊨ rel ⟩ → R (fst v) (fst x))
                           × (R (fst v) (fst x) → ⟨ (x ∷ v ∷ z ∷ Γ) ⊨ rel ⟩))
    (cnd-out : (δ : DB.SM ^ n) → ⟨ Meaning (op t u) δ ⟩ → R (fst (value t δ)) (fst (value u δ)))
    (cnd-in : (δ : DB.SM ^ n) → R (fst (value t δ)) (fst (value u δ)) → ⟨ Meaning (op t u) δ ⟩) where

    private
      δ3 : (z v x : S) → S ^ (3 + k)
      δ3 z v x = x ∷ v ∷ z ∷ Γ

      tOut : (z v x : S) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) ⟩ → TmIsV (ct t) (fst z) (fst v)
      tOut z v x h = subst (λ w → TmIsV w (fst z) (fst v)) qt
        (tmIs-out (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1 h)
      uOut : (z v x : S) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ⟩ → TmIsV (ct u) (fst z) (fst x)
      uOut z v x h = subst (λ w → TmIsV w (fst z) (fst x)) qu
        (tmIs-out (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1 h)
      tIn : (z v x : S) → TmIsV (ct t) (fst z) (fst v) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) ⟩
      tIn z v x h = tmIs-in (suc (suc (suc ti))) i2 i1 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1
        (subst (λ w → TmIsV w (fst z) (fst v)) (sym qt) h)
      uIn : (z v x : S) → TmIsV (ct u) (fst z) (fst x) → ⟨ δ3 z v x ⊨ tmIs (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) ⟩
      uIn z v x h = tmIs-in (suc (suc (suc ui))) i2 i0 (sh 3 N0i) (sh 3 N1i) (δ3 z v x) q0 q1
        (subst (λ w → TmIsV w (fst z) (fst x)) (sym qu) h)

    atomBridge : ExtFact (fst (SatW (op t u))) (fst (envSet W n)) (λ z → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩)
    atomBridge = direct-extension (op t u) (λ z → (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel) out inn
      where
      out : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ → ⟨ Meaning (op t u) δ ⟩
          → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩
      out δ z qz h = ∣ v , subst (λ X → ⟨ fst v ∈ X ⟩) (sym qw) (snd (value t δ))
        , ∣ x , subst (λ X → ⟨ fst x ∈ X ⟩) (sym qw) (snd (value u δ))
          , tIn z v x (term-in t δ z v qz refl)
          , uIn z v x (term-in u δ z x qz refl)
          , agree z v x .snd (cnd-out δ h) ∣₁ ∣₁
        where
        v x : S
        v = Semantic.intoL W (value t δ)
        x = Semantic.intoL W (value u δ)

      inn : (δ : DB.SM ^ n) (z : S) → fst z ≡ Semantic.graph W δ
          → ⟨ (z ∷ Γ) ⊨ atomEx wi ti ui N0i N1i rel ⟩ → ⟨ Meaning (op t u) δ ⟩
      inn δ z qz = PT.rec (snd (Meaning (op t u) δ)) (λ { (v , hv , h) →
        PT.rec (snd (Meaning (op t u) δ)) (λ { (x , hx , ht , hu , hr) →
          cnd-in δ (subst2 R (term-out t δ z v qz (tOut z v x ht))
            (term-out u δ z x qz (uOut z v x hu)) (agree z v x .fst hr)) }) h })
```
