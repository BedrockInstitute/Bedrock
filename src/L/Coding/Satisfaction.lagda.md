# Satisfaction, internalized

<!--en-->
The instance. For a formula of the meta-language and a set of `L` its
environments range over, the satisfaction table is an element of `L`, defined
there by an object-language formula.

`funct`{.Agda} is the two halves meeting. Existence hands the graph the objects
the previous chapters built: the slot as the index set, the table over it, the
carrier as the constant. Uniqueness takes an arbitrary table the graph accepts
and pins its value against the one the meta-level recursion built. Neither half
does anything here; both were finished before this chapter opened, and this is
the page where they are applied.
<!--zh-->
那个实例。给定元语言的一条公式，以及诸环境所落之上的 `L` 的一个集合，满足关系那张表是 `L` 的元素，并且在那里由一条对象语言的公式定义。

`funct`{.Agda} 就是那两半的会合。存在性把前几章造出的对象递给那个图：槽作索引集、其上的表、载体作常元。唯一性取图所接受的任意一张表，把它的取值对着元语言递归造出的那个钉死。两半在此处都不做任何事；它们在本章开篇之前就已完成，而这一页只是施用它们的地方。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Satisfaction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Coding.Model {ℓ} using ( prʟ-fst; domAt; domAt-intro; domAt-out )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Table {ℓ} lem
  using ( keyʟ; slot; satTable; tree; ent; slot-ent; total; inSlot
        ; module Parts )
open import L.Coding.Slot {ℓ} lem using ( slotClosed )
open import L.Coding.Sound {ℓ} lem using ( soundness )
open import L.Coding.Unique {ℓ} lem using ( module Good )
open import L.Coding.Graph {ℓ} lem using ( satGraph; graph-in; graph-out )
open import L.Recursion {ℓ} lem using ( Recursion; mereFunct; module Of )

open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
## The instance
<!--zh-->
## 那个实例
<!--/-->

<!--en-->
The domain is the slot; the graph is the one the previous chapter wrote; and
`funct`{.Agda} is filled through `mereFunct`{.Agda}, because a merely existing
unique solution is a contractible one and contractibility is a proposition. That
was the first finding of this whole goal, made before any of it was built, and
this is where it is spent.
<!--zh-->
定义域是那个槽；图是上一章写下的那一个；而 `funct`{.Agda} 经 `mereFunct`{.Agda} 交付，因为「仅仅存在的唯一解」就是可缩解，而可缩性是命题。那是整个目标的第一个发现，作出于任何东西被造出之前，而此处正是它被花掉的地方。
<!--/-->

```agda
module _ (B : S) {n : ℕ} (φ : Formula S n) where
  private
    C T : S
    C = slot B φ
    T = satTable B φ

    Ci Ti : Fin 5
    Ci = suc (suc zero)
    Ti = suc zero

    δ : (x y : S) → S ^ 5
    δ x y = B ∷ T ∷ C ∷ y ∷ x ∷ []

    hdom : (x y : S) → ⟨ δ x y ⊨ domAt Ti Ci ⟩
    hdom x y = domAt-intro Ti Ci (δ x y)
      (λ z → (λ h → PT.rec (snd (fst z ∈ fst C))
                (λ { (w , hw) → inSlot B φ (fst z) (fst w) hw }) h)
           , (λ h → total B φ (fst z) h))

    entry : ∀ {m} (ψ : Formula S m) (x : S) → fst x ≡ fst (keyʟ ψ)
          → ((z : V ℓ) → ⟨ z ∈ fst (tree B (ent B) ψ) ⟩ → ⟨ z ∈ fst T ⟩)
          → ⟨ pr (fst x) (fst (Sat B ψ)) ∈ fst T ⟩
    entry ψ x q incl =
      subst (λ w → ⟨ pr w (fst (Sat B ψ)) ∈ fst T ⟩) (sym q)
        (incl (pr (fst (keyʟ ψ)) (fst (Sat B ψ)))
          (subst (λ w → ⟨ w ∈ fst (tree B (ent B) ψ) ⟩)
            (prʟ-fst (keyʟ ψ) (Sat B ψ)) (Parts.self B (ent B) ψ)))

  satRec : Recursion
  Recursion.dom satRec = C
  Recursion.graph satRec = satGraph B
  Recursion.funct satRec x x∈ = mereFunct (satGraph B) x (PT.map
    (λ { (m , ψ , (q , incl)) → Sat B ψ
       , ( graph-in B x (Sat B ψ)
             ∣ C , (T , (B , (refl
             , ( slotClosed B φ (Sat B ψ ∷ x ∷ [])
             , ( hdom x (Sat B ψ)
             , ( entry ψ x q incl
             , soundness B φ (Sat B ψ ∷ x ∷ []) )))))) ∣₁
         , (λ y' hy' → Σ≡Prop (λ v → snd (isL v))
             (PT.rec (setIsSet (fst y') (fst (Sat B ψ)))
               (λ { (C' , (T' , (b , (eb , (hc , (hd , (ha , h12))))))) →
                 Good.pinned (b ∷ T' ∷ C' ∷ y' ∷ x ∷ []) Ci Ti zero
                     hc hd h12 ψ x y' q
                     (domAt-out Ti Ci (b ∷ T' ∷ C' ∷ y' ∷ x ∷ []) hd x y' ha) ha
                 ∙ cong (λ w → fst (Sat w ψ))
                     (Σ≡Prop (λ v → snd (isL v)) eb) })
               (graph-out B x y' hy'))) ) })
    (slot-ent B φ (fst x) x∈))

  module Table = Of satRec
```
