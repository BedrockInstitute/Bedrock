# The environment tower

<!--en-->
The satisfaction construction needs one set containing every environment arity. Starting from coded-pair quantification and the environment sets, this chapter builds that tower and proves its formula specification and readers.
<!--zh-->
满足关系的构造需要一个同时容纳所有元数环境的集合。本章从码化配对量词与环境集出发，构造该塔并证明其公式刻画和读式。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Tower {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; ⊥̇; ∃̇_; ∃̇∈; ∀̇∈ )
open import FOL.LevyHierarchy using ( checkΔ₀; Δ₀ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Environment {ℓ} using ( env; cons )
open import L.Coding.Model {ℓ} using ( prAtL; prʟ; prʟ-fst; container )
open import L.Coding.Expressions {ℓ} using
  ( envSetAt; sucAtL; consAtL; consAtL-adequate; numL )
open import L.Coding.Quantification {ℓ} using
  ( i0; i1; i2; i3; sh; pr-out; pr-in; down; suc-out; suc-in
  ; i4; i5
  ; sndEx; bothEx; bothAll
  ; sndEx-out; bothEx-out; bothAll-in
  ; fillSnd; fillBoth; useBoth )
open import L.Coding.EnvSet {ℓ} lem using ( envSet; envSet-in; envSet-out; envS; Ix )
open import L.Coding.Sound {ℓ} lem using ( module Ambient; module AmbientHolds )
open import L.Recursion {ℓ} lem using ( smallDom )
open import L.Axioms.Basic {ℓ} using ( extensionalL )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ; ω-specL )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Vec using ( _∷_; []; lookup )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ( _⊓_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

The slot arithmetic this chapter needs, at the four innermost slots.

```agda

```

The tower set: the pairs `(n, Eₙ)`, cut by separation out of a stage that holds
every entry. The cutting formula is not Δ₀ and need not be: it builds the set,
and only its two readers leave this section.

```agda
module Tower (W : S) where
  entry : ℕ → S
  entry n = prʟ (numeralL n) (envSet W n)

  private
    dom : Σ[ d ∈ S ] ((k : Lift {ℓ-zero} {ℓ} ℕ) → ⟨ fst (entry (lower k)) ∈ fst d ⟩)
    dom = smallDom (Lift {ℓ-zero} {ℓ} ℕ) (λ k → entry (lower k))
```

At `F ∷ n ∷ b ∷ z ∷ []`: `b = W`, `z = (n, F)`, `n ∈ ω`, `F` the environment set
of arity `n` over `b`.

```agda
    towerFo : Formula S 1
    towerFo = ∃̇ (∃̇ (∃̇ ( (var i2 ≐ con W)
                      ∧̇ ( prAtL i3 i1 i0
                      ∧̇ ( (var i1 ∈̇ con ωʟ)
                      ∧̇ envSetAt i0 i1 i2 )))))

  opaque
    tower : S
    tower = hasSeparationL (dom .fst) towerFo .fst .fst

    tower-mem : (x : S)
              → (fst x ∈ fst tower) ≡ ((fst x ∈ fst (dom .fst)) ⊓ ((x ∷ []) ⊨ towerFo))
    tower-mem = hasSeparationL (dom .fst) towerFo .fst .snd

  private
    holdsAt : (n : ℕ) → ⟨ (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ []) ⊨ envSetAt i0 i1 i2 ⟩
    holdsAt n = AmbientHolds.holds W (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ [])
                  i0 i1 i2 n refl (numeralL-fst n) refl

    tower-in : (n : ℕ) → ⟨ fst (entry n) ∈ fst tower ⟩
    tower-in n = subst ⟨_⟩ (sym (tower-mem (entry n)))
      ( dom .snd (lift n)
      , ∣ W , ∣ numeralL n , ∣ envSet W n
        , ( refl
          , ( pr-in i3 i1 i0 (envSet W n ∷ numeralL n ∷ W ∷ entry n ∷ [])
                (prʟ-fst (numeralL n) (envSet W n))
            , ( subst ⟨_⟩ (sym (ω-specL (numeralL n))) ∣ lift n , refl ∣₁
              , holdsAt n ))) ∣₁ ∣₁ ∣₁ )

  tower-in′ : (n : ℕ) → ⟨ pr (# n) (fst (envSet W n)) ∈ fst tower ⟩
  tower-in′ n = subst (λ u → ⟨ u ∈ fst tower ⟩)
    (prʟ-fst (numeralL n) (envSet W n) ∙ cong (λ u → pr u (fst (envSet W n))) (numeralL-fst n))
    (tower-in n)

  tower-out : (x : S) → ⟨ fst x ∈ fst tower ⟩
            → ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet W n))) ∥₁
  tower-out x hx = PT.rec squash₁ byB (subst ⟨_⟩ (tower-mem x) hx .snd)
    where
    Goal : Type (ℓ-suc ℓ)
    Goal = ∥ Σ[ n ∈ ℕ ] (fst x ≡ pr (# n) (fst (envSet W n))) ∥₁

    byB : Σ[ b ∈ S ] ⟨ (b ∷ x ∷ []) ⊨ ∃̇ (∃̇ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 )))) ⟩ → Goal
    byB (b , hb) = PT.rec squash₁ byN hb
      where
      byN : Σ[ n ∈ S ] ⟨ (n ∷ b ∷ x ∷ []) ⊨ ∃̇ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
      byN (n , hn) = PT.rec squash₁ byE hn
        where
        byE : Σ[ F ∈ S ] ⟨ (F ∷ n ∷ b ∷ x ∷ []) ⊨ ( (var i2 ≐ con W)
                    ∧̇ ( prAtL i3 i1 i0
                    ∧̇ ( (var i1 ∈̇ con ωʟ)
                    ∧̇ envSetAt i0 i1 i2 ))) ⟩ → Goal
        byE (F , (qb , (hp , (hω , hE)))) = PT.rec squash₁ byK (subst ⟨_⟩ (ω-specL n) hω)
          where
          xq : fst x ≡ pr (fst n) (fst F)
          xq = pr-out i3 i1 i0 (F ∷ n ∷ b ∷ x ∷ []) hp

          byK : Σ[ k ∈ Lift {ℓ-zero} {ℓ-suc ℓ} ℕ ] (fst n ≡ fst (numeralL (lower k))) → Goal
          byK (k , qn) = ∣ lower k , xq ∙ cong₂ pr (qn ∙ numeralL-fst (lower k)) Eq ∣₁
            where
            module Am = Ambient W (F ∷ n ∷ b ∷ x ∷ []) i0 i1 i2 (lower k)
                          (qn ∙ numeralL-fst (lower k)) qb hE using (into; outof)
            Eq : fst F ≡ fst (envSet W (lower k))
            Eq = cong fst (extensionalL {a = F} {b = envSet W (lower k)}
              (λ z → ⇔toPath (Am.into z) (Am.outof z)))
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
