<!--en-->
# Least witnesses form a definable map

On a well-ordered domain, a predicate with a witness has a least witness. This chapter proves that when the predicate is definable, selecting that least witness is itself a definable map.
<!--zh-->
# 最小见证构成可定义映射

在良序定义域上，一个有见证的谓词有最小见证。本章证明，当该谓词可定义时，选取最小见证本身也构成可定义映射。
<!--ja-->
# 最小の証人が定義可能な写像をなす

整列された領域では、証人をもつ述語には最小の証人がある。本章では、述語が定義可能ならば、その最小の証人を選ぶ操作も定義可能な写像になることを示す。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.LeastWitnessMap {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∀̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo; module Sat )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset→isL )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Choice.StageOrders {ℓ} lem using ( orderAt; relOf ) renaming ( Mem to MemOf )
open import L.Choice.InternalWellOrder {ℓ} lem using ( relL; relL-fill; relL-rep )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; leastOf; lt; eq; gt ) renaming ( Tri to Tri∙ )
open import L.DefinableInjection {ℓ} lem using ( DefinableMap; module Graph )
open import L.GCH.CardinalSquareLaw {ℓ} lem using ( isL-ord )
open import L.InjectionComposition {ℓ} lem using ( appC; appC-adequate )

open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

Renaming, read at the same satisfaction as `_⊨_` (as `L.DefinableInjection` does).

```agda
module Ren = Sat (hPropAlgebra (ℓ-suc ℓ)) 𝒮ʟ id using ( Agrees; ⊨-rename )

private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
```

Two elements of L with the same underlying set are equal.

```agda
  S≡ : {x y : S} → fst x ≡ fst y → x ≡ y
  S≡ = Σ≡Prop (λ v → snd (isL v))
```

The tool. `P` is a predicate over `(w ∷ x ∷ [])`, "`w` witnesses `x`", and every
`x ∈ X` has a witness in the stage `L_γ`. `x ↦` the stage-order-least witness in
`L_γ` is a definable map `X → L_γ`: its graph is "`P w x`, `w ∈ L_γ`, and no
`w' ∈ L_γ` below `w` in the stage order witnesses `x`", its table is a set of L,
and its readers give the witness, its leastness and its uniqueness. Inside the
bounded binder `w'` is 0, `w` is 1, `x` is 2; `P` is renamed from
`(w' ∷ x ∷ [])` into that environment.

Five parameters: the bound `γ` with its ordinality, the index set `X`, the
predicate `P`, and the existence of a witness at the bound.

```agda
```

<!--en-->
## Selecting the least satisfying member

Inside the stage order at `γ`, the formula first restricts candidates to `X` and then asks that `P` hold. Least-element search chooses the first candidate and proves that the choice is unchanged by equivalent environments.
<!--zh-->
## 选取最小的满足成员

在 `γ` 处的层序中，公式先把候选限制在 `X` 内，再要求 `P` 成立。最小元搜索选出第一个候选，并证明等价环境不会改变这一选择。
<!--ja-->
## 条件を満たす最小の要素を選ぶ

`γ` における段階順序の中で、論理式は候補をまず `X` に制限し、次に `P` を要求する。最小要素の探索で最初の候補を選び、同値な環境では選択が変わらないことを示す。
<!--/-->

```agda
module Least (γ : V ℓ) (oγ : IsOrd γ) (X : S) (P : Formula S 2)
  (have : (x : S) → ⟨ fst x ∈ fst X ⟩
        → ∥ Σ[ w ∈ S ] (⟨ fst w ∈ Lset γ ⟩ × ⟨ (w ∷ x ∷ []) ⊨ P ⟩) ∥₁) where
```

Sealed: the elements that reach a slot.

```agda
  opaque
    Lγ : S
    Lγ = LsetS γ oγ

    Lγ-fst : fst Lγ ≡ Lset γ
    Lγ-fst = refl

    hγ : ⟨ isL γ ⟩
    hγ = isL-ord γ oγ

  Rγ : S
  Rγ = relL γ hγ oγ

  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ fst X ⟩

  private
    Mγ : Type (ℓ-suc ℓ)
    Mγ = MemOf (Lset γ)

    memS : Mγ → S
    memS c = fst c , Lset→isL γ oγ (fst c) (snd c)

    At : S → S → hProp (ℓ-suc ℓ)
    At w x = (w ∷ x ∷ []) ⊨ P

    Good : S → Mγ → hProp (ℓ-suc ℓ)
    Good x c = At (memS c) x
```

A satisfaction at `w`, moved to the member `w` names.

```agda
    toMem : (x w : S) (hw : ⟨ fst w ∈ Lset γ ⟩) → ⟨ At w x ⟩ → ⟨ Good x (fst w , hw) ⟩
    toMem x w hw = subst (λ v → ⟨ At v x ⟩) (S≡ refl)

  module Sel (x : S) (m : Mem x) where

    private
      nonempty : ∥ Σ[ c ∈ Mγ ] ⟨ Good x c ⟩ ∥₁
      nonempty = PT.map (λ { (w , hw , hp) → (fst w , hw) , toMem x w hw hp }) (have x m)
```

The selection, sealed with its two facts.

```agda
    opaque
      c : Mγ
      c = fst (leastOf (orderAt γ oγ) lem (Good x) nonempty)

      c-good : ⟨ Good x c ⟩
      c-good = fst (snd (leastOf (orderAt γ oγ) lem (Good x) nonempty))

      minimal : (c' : Mγ) → ⟨ Good x c' ⟩ → relOf (orderAt γ oγ) c' c → Empty.⊥
      minimal = snd (snd (leastOf (orderAt γ oγ) lem (Good x) nonempty))

    e : S
    e = memS c

    e-holds : ⟨ (e ∷ x ∷ []) ⊨ P ⟩
    e-holds = c-good

    e∈Lγ : ⟨ fst e ∈ Lset γ ⟩
    e∈Lγ = snd c
```

THE MAP, with its three readers.

```agda
  fn : (x : S) → Mem x → S
  fn x m = Sel.e x m

  fn-holds : (x : S) (m : Mem x) → ⟨ (fn x m ∷ x ∷ []) ⊨ P ⟩
  fn-holds x m = Sel.e-holds x m

  fn-in : (x : S) (m : Mem x) → ⟨ fst (fn x m) ∈ Lset γ ⟩
  fn-in x m = Sel.e∈Lγ x m

  fn-least : (x : S) (m : Mem x) (w' : S) → ⟨ fst w' ∈ Lset γ ⟩ → ⟨ (w' ∷ x ∷ []) ⊨ P ⟩
           → ⟨ pr (fst w') (fst (fn x m)) ∈ fst Rγ ⟩ → Empty.⊥
  fn-least x m w' hw' hp hr = Sel.minimal x m (fst w' , hw') (toMem x w' hw' hp)
    (relL-rep γ hγ oγ (fst w' , hw') (Sel.c x m) hr)
```

The graph, read on the host side.

```agda
  TWit : (w x : S) → Type (ℓ-suc ℓ)
  TWit w x =
      ⟨ (w ∷ x ∷ []) ⊨ P ⟩
    × ⟨ fst w ∈ Lset γ ⟩
    × ((w' : S) → ⟨ fst w' ∈ Lset γ ⟩ → ⟨ (w' ∷ x ∷ []) ⊨ P ⟩
        → ⟨ pr (fst w') (fst w) ∈ fst Rγ ⟩ → Empty.⊥)
```

Anything the graph holds of is the selected witness.

```agda
  fn-unique : (x : S) (m : Mem x) (w : S) → TWit w x → fst w ≡ fst (fn x m)
  fn-unique x m w (hp , hw , mn) = go (SWO.tri∙ (orderAt γ oγ) c' (Sel.c x m))
    where
    c' : Mγ
    c' = fst w , hw
    go : Tri∙ (relOf (orderAt γ oγ) c' (Sel.c x m)) (c' ≡ Sel.c x m)
              (relOf (orderAt γ oγ) (Sel.c x m) c')
       → fst w ≡ fst (fn x m)
    go (lt k) = Empty.rec (Sel.minimal x m c' (toMem x w hw hp) k)
    go (eq q) = cong fst q
    go (gt k) = Empty.rec (mn (fn x m) (fn-in x m) (fn-holds x m)
      (relL-fill γ hγ oγ (Sel.c x m) c' k))

  private
    ρ : Fin 2 → Fin 3
    ρ zero       = zero
    ρ (suc zero) = suc (suc zero)

    ag : (w' w x : S) → Ren.Agrees ρ (w' ∷ w ∷ x ∷ []) (w' ∷ x ∷ [])
    ag w' w x zero       = refl
    ag w' w x (suc zero) = refl

  opaque
    private
      leastFo : Formula S 2
      leastFo = ∀̇∈ (con Lγ) (¬̇ (appC Rγ i0 i1 ∧̇ renameFo ρ P))

      ren : (w' w x : S)
          → ⟨ (w' ∷ w ∷ x ∷ []) ⊨ renameFo ρ P ⟩ ≡ ⟨ (w' ∷ x ∷ []) ⊨ P ⟩
      ren w' w x = cong ⟨_⟩ (Ren.⊨-rename ρ P (w' ∷ w ∷ x ∷ []) (w' ∷ x ∷ []) (ag w' w x))

    fo : Formula S 2
    fo = P ∧̇ ((var i0 ∈̇ con Lγ) ∧̇ leastFo)

    fo-out : (w x : S) → ⟨ (w ∷ x ∷ []) ⊨ fo ⟩ → TWit w x
    fo-out w x (hp , (hl , hm)) =
        hp
      , subst (λ v → ⟨ fst w ∈ v ⟩) Lγ-fst hl
      , λ w' hw' hp' hr → lower (hm w' (subst (λ v → ⟨ fst w' ∈ v ⟩) (sym Lγ-fst) hw')
          ( subst ⟨_⟩ (sym (appC-adequate Rγ i0 i1 (w' ∷ w ∷ x ∷ []))) hr
          , transport (sym (ren w' w x)) hp' ))

    fo-in : (w x : S) → TWit w x → ⟨ (w ∷ x ∷ []) ⊨ fo ⟩
    fo-in w x (hp , hl , mn) =
        hp
      , subst (λ v → ⟨ fst w ∈ v ⟩) (sym Lγ-fst) hl
      , λ w' hw' hc → lift (mn w' (subst (λ v → ⟨ fst w' ∈ v ⟩) Lγ-fst hw')
          (transport (ren w' w x) (snd hc))
          (subst ⟨_⟩ (appC-adequate Rγ i0 i1 (w' ∷ w ∷ x ∷ [])) (fst hc)))
```

THE DEFINABLE MAP, into the stage.

```agda
  Dmap : DefinableMap
  Dmap = record
    { dom = X ; cod = Lγ ; fn = fn
    ; into = λ x m → subst (λ v → ⟨ fst (fn x m) ∈ v ⟩) (sym Lγ-fst) (fn-in x m)
    ; graph = fo
    ; defines = λ x m → fo-in (fn x m) x (fn-holds x m , fn-in x m , fn-least x m)
    ; only = λ x m w h → S≡ (fn-unique x m w (fo-out w x h)) }

  private
    module Gr = Graph Dmap using ( F; F-in; pair-out )
```

THE TABLE: the set of pairs `(x, fn x)`, `x ∈ X`.

```agda
  T : S
  T = Gr.F

  T-in : (x : S) (m : Mem x) → ⟨ pr (fst x) (fst (fn x m)) ∈ fst T ⟩
  T-in = Gr.F-in

  T-out : (x w : S) → ⟨ pr (fst x) (fst w) ∈ fst T ⟩
        → Σ[ m ∈ Mem x ] (fst w ≡ fst (fn x m))
  T-out = Gr.pair-out
```
