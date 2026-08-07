# The tower's step, described

<!--en-->
The tower's step is described from the inside here. An entry of the step is a
pair of a code with its value, and the table chapter already said, one
constructor at a time, what an entry must look like against the family it sits
in. What that chapter could not say is what this one can: that the entry is
readable as a code at all. A naked existential over tables admits junk, because
the clause shapes are conditional on numeral-ness and nothing else pins the
payload down. The certificate closes the gap with local conditions only: each
branch pins its tag by a sealed numeral, its payload pieces as members of ω or
of the carrier, its children present in the main table, and its annotations in
a table that is required functional, so an annotation is unique and can be
trusted. Reading a certificate back into an honest term of the syntax is the
next section's work; here the certificate shape is described, not yet
recovered.
<!--zh-->
本章从内部描述塔的一步。步的条目是码与其取值的对，表章已逐构造子说出条目对着所在族必须长什么样。表章说不出、而本章能说的，是条目根本可被读作码。对诸表的裸存在量词接纳垃圾，因为子句形状以数码性为条件，此外再无别物把载荷钉住。证书只用局部条件补上这个缺口：每个分支以封印数码钉住标签，以 ω 或载体的成员钉住载荷诸件，以主表钉住孩子的在场，并把注解放进一条被要求为函数性的表，故注解唯一而可信任。把证书读回语法中诚实的项，是下一节的工作；此处描述证书形状，尚未收回。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Godel.Tower {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV; extensionalV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′ )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; Lset→isL; IsOrd; Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Axioms.Basic {ℓ} using ( finSet; finSet-in; finSet-out; module FinOf )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate; appAt; appAt-adequate
        ; sucAtL; sucAtL-adequate; numL )
open import L.Godel.Table {ℓ}
  using ( tagPrAt; tagPr-out; tagPr-in; ApproxAt; Approx-step; ClauseOf; Clause-out
        ; module Denote )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK; shiftK
        ; ⟦_⟧ᴷ; termDef )
  renaming ( module WithLEM to TermsLEM )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Godel.InL {ℓ} using ( stageFam; denoteL; valuesL )
open import L.Godel.Definable {ℓ} using ( valuesAt; valuesAt-in; valuesAt-out )
open import L.Godel.Operations {ℓ} using ( values )
open import L.Godel.Codes {ℓ}
  using ( module Codes; tagNe; SubK; sizeK; subK; subSplitK; selfIxK; sub-selfK
        ; interIdxL; interIdxR; unionIdxL; unionIdxR )
open import L.Ordinal {ℓ} using ( suc-ord; ω-ord; ∈#-elim; #∈ω )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( znots; snotz; injSuc; _+_ )
open import Cubical.Data.Nat.Order using ( _<_ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties
  using ( fromℕ'; toFromId'; toℕ<n; module FinSumChar )
open import Cubical.Data.Bool using ( true; false )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
open import Cubical.Induction.WellFounded using ( Acc; acc )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ⁅_,_⁆; ⁅_⁆s )
open InfinitySet using ( sucV; #_; ω )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_; _∈ᵗ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )
```

<!--en-->
One piece of infrastructure is laid down before the classical modules, since
nothing classical is involved. The honesty proof recurses on the accessibility
of the transitive closure of membership, not of membership itself: a child code
sits four membership steps below its node code, and the termination checker
follows only one step at a time. The closure records the whole descent in a
single derivation, `_∈⁺_`, built once from the one-step relation `_∈ᵗ_`, with
its accessibility transported in from regularity, along with the two-step
chains that reach the components of a Kuratowski pair and the transitivity that
composes chains to depth four.
<!--zh-->
在经典模块之前先铺下一件基础设施，因为它不涉经典。诚实性证明跑在成员关系传递闭包的可及性上，而非成员关系本身的可及性上：孩子码坐在节点码之下四步成员关系处，而终止检查器一次只跟一步。闭包把整段下降记在一条推导 `_∈⁺_` 里，由一步关系 `_∈ᵗ_` 一次建成，其可及性从正则搬运过来，并配上直达 Kuratowski 对两个分量的两步链与把链复合到四层深的传递性。
<!--/-->

```agda
private
  data _∈⁺_ : V ℓ → V ℓ → Type (ℓ-suc ℓ) where
    here  : {u v : V ℓ} → u ∈ᵗ v → u ∈⁺ v
    there : {u w v : V ℓ} → u ∈⁺ w → w ∈ᵗ v → u ∈⁺ v

  accTC : (x : V ℓ) → Acc _∈ᵗ_ x → Acc _∈⁺_ x
  goTC  : (x : V ℓ) → Acc _∈ᵗ_ x → (y : V ℓ) → y ∈⁺ x → Acc _∈⁺_ y
  accTC x ax = acc (goTC x ax)
  goTC x (acc r) y (here hy)            = accTC y (r y hy)
  goTC x (acc r) y (there {w = w} p hw) = goTC w (r w hw) y p

  wf⁺ : (x : V ℓ) → Acc _∈⁺_ x
  wf⁺ x = accTC x (regularityV x)

  chainFst : (u v : V ℓ) → u ∈⁺ pr u v
  chainFst u v = there (here ∣ lift false , refl ∣₁) ∣ lift true , refl ∣₁

  chainSnd : (u v : V ℓ) → v ∈⁺ pr u v
  chainSnd u v = there (here ∣ lift true , refl ∣₁) ∣ lift true , refl ∣₁

  trans⁺ : {u w v : V ℓ} → u ∈⁺ w → w ∈⁺ v → u ∈⁺ v
  trans⁺ p (here h)     = there p h
  trans⁺ p (there q h)  = there (trans⁺ p q) h

  appRead : ∀ {n} (f x y : Fin n) (γ : S ^ n) → ⟨ γ ⊨ appAt f x y ⟩
          → ⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ) ⟩
  appRead f x y γ = subst ⟨_⟩ (appAt-adequate f x y γ)

  appFill : ∀ {n} (f x y : Fin n) (γ : S ^ n)
          → ⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ) ⟩
          → ⟨ γ ⊨ appAt f x y ⟩
  appFill f x y γ = subst ⟨_⟩ (sym (appAt-adequate f x y γ))

  prIsL₁ : {Z x y : V ℓ} → ⟨ isL Z ⟩ → ⟨ pr x y ∈ Z ⟩ → ⟨ isL x ⟩
  prIsL₁ {Z} {x} {y} lZ h = isL-trans {x = ⁅ x ⁆s} {y = x} (∣ tt* , refl ∣₁)
    (isL-trans {x = pr x y} {y = ⁅ x ⁆s} (∣ lift false , refl ∣₁)
      (isL-trans {x = Z} {y = pr x y} h lZ))

  prRead : ∀ {n} (q u v : Fin n) (γ : S ^ n) → ⟨ γ ⊨ prAtL q u v ⟩
         → fst (lookup q γ) ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
  prRead q u v γ = subst ⟨_⟩ (prAtL-adequate q u v γ)

  prFill : ∀ {n} (q u v : Fin n) (γ : S ^ n)
         → fst (lookup q γ) ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
         → ⟨ γ ⊨ prAtL q u v ⟩
  prFill q u v γ = subst ⟨_⟩ (sym (prAtL-adequate q u v γ))

  sucRead : ∀ {n} (i j : Fin n) (γ : S ^ n) → ⟨ γ ⊨ sucAtL i j ⟩
          → fst (lookup j γ) ≡ sucV (fst (lookup i γ))
  sucRead i j γ = subst ⟨_⟩ (sucAtL-adequate i j γ)

  sucFill : ∀ {n} (i j : Fin n) (γ : S ^ n)
          → fst (lookup j γ) ≡ sucV (fst (lookup i γ))
          → ⟨ γ ⊨ sucAtL i j ⟩
  sucFill i j γ = subst ⟨_⟩ (sym (sucAtL-adequate i j γ))

  prIsL₂ : {Z x y : V ℓ} → ⟨ isL Z ⟩ → ⟨ pr x y ∈ Z ⟩ → ⟨ isL y ⟩
  prIsL₂ {Z} {x} {y} lZ h = isL-trans {x = ⁅ x , y ⁆} {y = y} (∣ lift true , refl ∣₁)
    (isL-trans {x = pr x y} {y = ⁅ x , y ⁆} (∣ lift true , refl ∣₁)
      (isL-trans {x = Z} {y = pr x y} h lZ))
```

<!--en-->
## The arity of a code
<!--zh-->
## 码的元数
<!--/-->

<!--en-->
A code determines its arity, and the honest layer of this chapter is built on
that fact. The proof is one double case split over the eight constructors:
sixty-four cases in all. The fifty-six off-diagonal cases cannot happen,
because the two codes carry different tags: both sides rewrite by their code
equations to a pair with tag `j` on the left and tag `k` on the right, and the
discrimination helpers reduce the clash to an inequality of natural numbers,
exactly as the table chapter's twelve clashes do around its own matrix. The
eight diagonal cases peel the payload with pair injectivity: the leaves and
the complement read their recorded arity directly, the two binary nodes recurse
on their first children, and the shift peels its successor with injectivity.
The recursion is structural on the first argument throughout.
<!--zh-->
码决定其元数，本章的诚实层正建立在这一事实上。证明是对八个构造子的一次双重分情形：共六十四个情形。五十六个非对角情形不可能发生，因为两个码携带不同标签：两边都沿各自的码等式重写为左边标签 `j`、右边标签 `k` 的对，判别辅助件把冲突化归为自然数的不等，恰如表章在自己矩阵周围筑起的十二条冲突。八个对角情形以对单射性剥开载荷：诸叶与补直接读出记录的元数，两条二元节点递归于第一个孩子，移位经单射性剥掉后继。递归全程对第一参数结构地缩减。
<!--/-->

```agda
module _ (A : V ℓ) (lA : ⟨ isL A ⟩) where
  private
    module C = Codes A lA

    neS : {a b : ℕ} → (a ≡ b → Empty.⊥) → suc a ≡ suc b → Empty.⊥
    neS ne q = ne (injSuc q)

    n1z n2z n3z n4z n5z n6z : {k : ℕ} → _
    n1z {k} = neS (znots {n = k})
    n2z {k} = neS (n1z {k})
    n3z {k} = neS (n2z {k})
    n4z {k} = neS (n3z {k})
    n5z {k} = neS (n4z {k})
    n6z {k} = neS (n5z {k})

    n1s n2s n3s n4s n5s n6s : {k : ℕ} → _
    n1s {k} = neS (snotz {n = k})
    n2s {k} = neS (n1s {k})
    n3s {k} = neS (n2s {k})
    n4s {k} = neS (n3s {k})
    n5s {k} = neS (n4s {k})
    n6s {k} = neS (n5s {k})

  codeArity : {n₁ n₂ : ℕ} (s : KT ⟪ A ⟫ n₁) (s' : KT ⟪ A ⟫ n₂)
            → C.code s ≡ C.code s' → n₁ ≡ n₂
  codeArity {n₁} {n₂} allK allK q =
    #-inj′ (pr-inj (sym (C.code-allK n₁) ∙ q ∙ C.code-allK n₂) .snd)
  codeArity {n₁} {n₂} allK (selMemK i j) q =
    Empty.rec (tagNe 0 1 znots (sym (C.code-allK n₁) ∙ q ∙ C.code-selMemK n₂ i j))
  codeArity {n₁} {n₂} allK (selEqK i j) q =
    Empty.rec (tagNe 0 2 znots (sym (C.code-allK n₁) ∙ q ∙ C.code-selEqK n₂ i j))
  codeArity {n₁} {n₂} allK (selEqConK i a) q =
    Empty.rec (tagNe 0 3 znots (sym (C.code-allK n₁) ∙ q ∙ C.code-selEqConK n₂ i a))
  codeArity {n₁} {n₂} allK (interK s t) q =
    Empty.rec (tagNe 0 4 znots (sym (C.code-allK n₁) ∙ q ∙ C.code-interK s t))
  codeArity {n₁} {n₂} allK (unionK s t) q =
    Empty.rec (tagNe 0 5 znots (sym (C.code-allK n₁) ∙ q ∙ C.code-unionK s t))
  codeArity {n₁} {n₂} allK (complK t) q =
    Empty.rec (tagNe 0 6 znots (sym (C.code-allK n₁) ∙ q ∙ C.code-complK t))
  codeArity {n₁} {n₂} allK (shiftK t) q =
    Empty.rec (tagNe 0 7 znots (sym (C.code-allK n₁) ∙ q ∙ C.code-shiftK t))
  codeArity {n₁} {n₂} (selMemK i j) allK q =
    Empty.rec (tagNe 1 0 snotz (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-allK n₂))
  codeArity {n₁} {n₂} (selMemK i j) (selMemK i' j') q =
    #-inj′ (pr-inj (pr-inj (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-selMemK n₂ i' j') .snd) .fst)
  codeArity {n₁} {n₂} (selMemK i j) (selEqK i' j') q =
    Empty.rec (tagNe 1 2 n1z (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-selEqK n₂ i' j'))
  codeArity {n₁} {n₂} (selMemK i j) (selEqConK i' a') q =
    Empty.rec (tagNe 1 3 n1z (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-selEqConK n₂ i' a'))
  codeArity {n₁} {n₂} (selMemK i j) (interK s' t') q =
    Empty.rec (tagNe 1 4 n1z (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-interK s' t'))
  codeArity {n₁} {n₂} (selMemK i j) (unionK s' t') q =
    Empty.rec (tagNe 1 5 n1z (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-unionK s' t'))
  codeArity {n₁} {n₂} (selMemK i j) (complK t') q =
    Empty.rec (tagNe 1 6 n1z (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-complK t'))
  codeArity {n₁} {n₂} (selMemK i j) (shiftK t') q =
    Empty.rec (tagNe 1 7 n1z (sym (C.code-selMemK n₁ i j) ∙ q ∙ C.code-shiftK t'))
  codeArity {n₁} {n₂} (selEqK i j) allK q =
    Empty.rec (tagNe 2 0 snotz (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-allK n₂))
  codeArity {n₁} {n₂} (selEqK i j) (selMemK i' j') q =
    Empty.rec (tagNe 2 1 n1s (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-selMemK n₂ i' j'))
  codeArity {n₁} {n₂} (selEqK i j) (selEqK i' j') q =
    #-inj′ (pr-inj (pr-inj (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-selEqK n₂ i' j') .snd) .fst)
  codeArity {n₁} {n₂} (selEqK i j) (selEqConK i' a') q =
    Empty.rec (tagNe 2 3 n2z (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-selEqConK n₂ i' a'))
  codeArity {n₁} {n₂} (selEqK i j) (interK s' t') q =
    Empty.rec (tagNe 2 4 n2z (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-interK s' t'))
  codeArity {n₁} {n₂} (selEqK i j) (unionK s' t') q =
    Empty.rec (tagNe 2 5 n2z (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-unionK s' t'))
  codeArity {n₁} {n₂} (selEqK i j) (complK t') q =
    Empty.rec (tagNe 2 6 n2z (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-complK t'))
  codeArity {n₁} {n₂} (selEqK i j) (shiftK t') q =
    Empty.rec (tagNe 2 7 n2z (sym (C.code-selEqK n₁ i j) ∙ q ∙ C.code-shiftK t'))
  codeArity {n₁} {n₂} (selEqConK i a) allK q =
    Empty.rec (tagNe 3 0 snotz (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-allK n₂))
  codeArity {n₁} {n₂} (selEqConK i a) (selMemK i' j') q =
    Empty.rec (tagNe 3 1 n1s (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-selMemK n₂ i' j'))
  codeArity {n₁} {n₂} (selEqConK i a) (selEqK i' j') q =
    Empty.rec (tagNe 3 2 n2s (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-selEqK n₂ i' j'))
  codeArity {n₁} {n₂} (selEqConK i a) (selEqConK i' a') q =
    #-inj′ (pr-inj (pr-inj (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-selEqConK n₂ i' a') .snd) .fst)
  codeArity {n₁} {n₂} (selEqConK i a) (interK s' t') q =
    Empty.rec (tagNe 3 4 n3z (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-interK s' t'))
  codeArity {n₁} {n₂} (selEqConK i a) (unionK s' t') q =
    Empty.rec (tagNe 3 5 n3z (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-unionK s' t'))
  codeArity {n₁} {n₂} (selEqConK i a) (complK t') q =
    Empty.rec (tagNe 3 6 n3z (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-complK t'))
  codeArity {n₁} {n₂} (selEqConK i a) (shiftK t') q =
    Empty.rec (tagNe 3 7 n3z (sym (C.code-selEqConK n₁ i a) ∙ q ∙ C.code-shiftK t'))
  codeArity {n₁} {n₂} (interK s t) allK q =
    Empty.rec (tagNe 4 0 snotz (sym (C.code-interK s t) ∙ q ∙ C.code-allK n₂))
  codeArity {n₁} {n₂} (interK s t) (selMemK i' j') q =
    Empty.rec (tagNe 4 1 n1s (sym (C.code-interK s t) ∙ q ∙ C.code-selMemK n₂ i' j'))
  codeArity {n₁} {n₂} (interK s t) (selEqK i' j') q =
    Empty.rec (tagNe 4 2 n2s (sym (C.code-interK s t) ∙ q ∙ C.code-selEqK n₂ i' j'))
  codeArity {n₁} {n₂} (interK s t) (selEqConK i' a') q =
    Empty.rec (tagNe 4 3 n3s (sym (C.code-interK s t) ∙ q ∙ C.code-selEqConK n₂ i' a'))
  codeArity {n₁} {n₂} (interK s t) (interK s' t') q =
    codeArity s s' (pr-inj (pr-inj (sym (C.code-interK s t) ∙ q ∙ C.code-interK s' t') .snd) .fst)
  codeArity {n₁} {n₂} (interK s t) (unionK s' t') q =
    Empty.rec (tagNe 4 5 n4z (sym (C.code-interK s t) ∙ q ∙ C.code-unionK s' t'))
  codeArity {n₁} {n₂} (interK s t) (complK t') q =
    Empty.rec (tagNe 4 6 n4z (sym (C.code-interK s t) ∙ q ∙ C.code-complK t'))
  codeArity {n₁} {n₂} (interK s t) (shiftK t') q =
    Empty.rec (tagNe 4 7 n4z (sym (C.code-interK s t) ∙ q ∙ C.code-shiftK t'))
  codeArity {n₁} {n₂} (unionK s t) allK q =
    Empty.rec (tagNe 5 0 snotz (sym (C.code-unionK s t) ∙ q ∙ C.code-allK n₂))
  codeArity {n₁} {n₂} (unionK s t) (selMemK i' j') q =
    Empty.rec (tagNe 5 1 n1s (sym (C.code-unionK s t) ∙ q ∙ C.code-selMemK n₂ i' j'))
  codeArity {n₁} {n₂} (unionK s t) (selEqK i' j') q =
    Empty.rec (tagNe 5 2 n2s (sym (C.code-unionK s t) ∙ q ∙ C.code-selEqK n₂ i' j'))
  codeArity {n₁} {n₂} (unionK s t) (selEqConK i' a') q =
    Empty.rec (tagNe 5 3 n3s (sym (C.code-unionK s t) ∙ q ∙ C.code-selEqConK n₂ i' a'))
  codeArity {n₁} {n₂} (unionK s t) (interK s' t') q =
    Empty.rec (tagNe 5 4 n4s (sym (C.code-unionK s t) ∙ q ∙ C.code-interK s' t'))
  codeArity {n₁} {n₂} (unionK s t) (unionK s' t') q =
    codeArity s s' (pr-inj (pr-inj (sym (C.code-unionK s t) ∙ q ∙ C.code-unionK s' t') .snd) .fst)
  codeArity {n₁} {n₂} (unionK s t) (complK t') q =
    Empty.rec (tagNe 5 6 n5z (sym (C.code-unionK s t) ∙ q ∙ C.code-complK t'))
  codeArity {n₁} {n₂} (unionK s t) (shiftK t') q =
    Empty.rec (tagNe 5 7 n5z (sym (C.code-unionK s t) ∙ q ∙ C.code-shiftK t'))
  codeArity {n₁} {n₂} (complK t) allK q =
    Empty.rec (tagNe 6 0 snotz (sym (C.code-complK t) ∙ q ∙ C.code-allK n₂))
  codeArity {n₁} {n₂} (complK t) (selMemK i' j') q =
    Empty.rec (tagNe 6 1 n1s (sym (C.code-complK t) ∙ q ∙ C.code-selMemK n₂ i' j'))
  codeArity {n₁} {n₂} (complK t) (selEqK i' j') q =
    Empty.rec (tagNe 6 2 n2s (sym (C.code-complK t) ∙ q ∙ C.code-selEqK n₂ i' j'))
  codeArity {n₁} {n₂} (complK t) (selEqConK i' a') q =
    Empty.rec (tagNe 6 3 n3s (sym (C.code-complK t) ∙ q ∙ C.code-selEqConK n₂ i' a'))
  codeArity {n₁} {n₂} (complK t) (interK s' t') q =
    Empty.rec (tagNe 6 4 n4s (sym (C.code-complK t) ∙ q ∙ C.code-interK s' t'))
  codeArity {n₁} {n₂} (complK t) (unionK s' t') q =
    Empty.rec (tagNe 6 5 n5s (sym (C.code-complK t) ∙ q ∙ C.code-unionK s' t'))
  codeArity {n₁} {n₂} (complK t) (complK t') q =
    #-inj′ (pr-inj (pr-inj (sym (C.code-complK t) ∙ q ∙ C.code-complK t') .snd) .fst)
  codeArity {n₁} {n₂} (complK t) (shiftK t') q =
    Empty.rec (tagNe 6 7 n6z (sym (C.code-complK t) ∙ q ∙ C.code-shiftK t'))
  codeArity {n₁} {n₂} (shiftK t) allK q =
    Empty.rec (tagNe 7 0 snotz (sym (C.code-shiftK t) ∙ q ∙ C.code-allK n₂))
  codeArity {n₁} {n₂} (shiftK t) (selMemK i' j') q =
    Empty.rec (tagNe 7 1 n1s (sym (C.code-shiftK t) ∙ q ∙ C.code-selMemK n₂ i' j'))
  codeArity {n₁} {n₂} (shiftK t) (selEqK i' j') q =
    Empty.rec (tagNe 7 2 n2s (sym (C.code-shiftK t) ∙ q ∙ C.code-selEqK n₂ i' j'))
  codeArity {n₁} {n₂} (shiftK t) (selEqConK i' a') q =
    Empty.rec (tagNe 7 3 n3s (sym (C.code-shiftK t) ∙ q ∙ C.code-selEqConK n₂ i' a'))
  codeArity {n₁} {n₂} (shiftK t) (interK s' t') q =
    Empty.rec (tagNe 7 4 n4s (sym (C.code-shiftK t) ∙ q ∙ C.code-interK s' t'))
  codeArity {n₁} {n₂} (shiftK t) (unionK s' t') q =
    Empty.rec (tagNe 7 5 n5s (sym (C.code-shiftK t) ∙ q ∙ C.code-unionK s' t'))
  codeArity {n₁} {n₂} (shiftK t) (complK t') q =
    Empty.rec (tagNe 7 6 n6s (sym (C.code-shiftK t) ∙ q ∙ C.code-complK t'))
  codeArity {n₁} {n₂} (shiftK t) (shiftK t') q =
    injSuc (codeArity t t' (pr-inj (sym (C.code-shiftK t) ∙ q ∙ C.code-shiftK t') .snd))
```

<!--en-->
## The honest annotation table
<!--zh-->
## 诚实注解表
<!--/-->

<!--en-->
The honest annotation table writes the arity down, once per subterm. Where the
approximation records each entry as the sealed pair of a code with its
denotation, the annotation records the same code paired with the numeral of the
subterm's arity: the same term enumeration, the same finite set over one stage,
sealed at birth. The three facts mirror the approximation's three: membership
at every index, the outward reading back into an index, and self-membership at
the head. The self-membership proof is the approximation's own, with the
denotation projection replaced by the numeral's projection.
<!--zh-->
诚实注解表把元数写下，每个子项一次。逼近把每个条目记录为码与其指称的封印对，注解则在同一个码上配上该子项元数之数码：同样的项枚举、同样的单阶段有穷集、出生即封印。三条事实镜像逼近的三条：每个索引处的成员、向外读回索引的读式、头处的自身成员。自身成员的证明就是逼近的那条，只是把指称投影换成数码投影。
<!--/-->

```agda
  hEntry : SubK ⟪ A ⟫ → S
  hEntry (m , s) = prʟ (C.codeS s) (numeralL m)

  hEntry-eq : (p : SubK ⟪ A ⟫)
            → fst (hEntry p) ≡ pr (C.code (p .snd)) (# (p .fst))
  hEntry-eq (m , s) = prʟ-fst (C.codeS s) (numeralL m)
    ∙ cong₂ pr refl (numeralL-fst m)

  private
    hBnd : {n : ℕ} (T : KT ⟪ A ⟫ n)
         → ∥ Σ[ σ ∈ V ℓ ] (IsOrd σ
           × ((i : Fin (sizeK T)) → ⟨ fst (hEntry (subK T i)) ∈ Lset σ ⟩)) ∥₁
    hBnd T = stageFam (sizeK T) (λ i → fst (hEntry (subK T i)))
      (λ i → hEntry (subK T i) .snd)

  opaque
    hS : {n : ℕ} → KT ⟪ A ⟫ n → S
    hS T = finSet (sizeK T) (λ i → fst (hEntry (subK T i))) , isl
      where
      isl : ⟨ isL (finSet (sizeK T) (λ i → fst (hEntry (subK T i)))) ⟩
      isl = PT.rec (snd (isL (finSet (sizeK T) (λ i → fst (hEntry (subK T i))))))
        (λ { (σ , oσ , mem) →
          FinOf.finSetL σ oσ (sizeK T) (λ i → fst (hEntry (subK T i))) mem })
        (hBnd T)

    hS-in : {n : ℕ} (T : KT ⟪ A ⟫ n) (i : Fin (sizeK T))
          → ⟨ fst (hEntry (subK T i)) ∈ fst (hS T) ⟩
    hS-in T i = finSet-in (sizeK T) (λ j → fst (hEntry (subK T j)))
      (fst (hEntry (subK T i))) ∣ i , refl ∣₁

    hS-out : {n : ℕ} (T : KT ⟪ A ⟫ n) (z : V ℓ) → ⟨ z ∈ fst (hS T) ⟩
           → ∥ Σ[ i ∈ Fin (sizeK T) ] (fst (hEntry (subK T i)) ≡ z) ∥₁
    hS-out T z = finSet-out (sizeK T) (λ j → fst (hEntry (subK T j))) z

  hSelf∈ : {n : ℕ} (t : KT ⟪ A ⟫ n)
         → ⟨ pr (C.code t) (# n) ∈ fst (hS t) ⟩
  hSelf∈ {n} t = subst (λ u → ⟨ u ∈ fst (hS t) ⟩)
    ( hEntry-eq (subK t (selfIxK t))
    ∙ (λ ι → pr (C.code (sub-selfK t ι .snd)) (# (sub-selfK t ι .fst))) )
    (hS-in t (selfIxK t))
```

<!--en-->
## The functionality of the honest table
<!--zh-->
## 诚实表的函数性
<!--/-->

<!--en-->
Functionality is exactly the fact that a code determines its arity, read
through the table: two memberships of the same code force the two recorded
numerals to agree. The outward reading turns each membership into a subterm
index, each entry is a code paired with its arity's numeral, pair injectivity
splits both pairs, the two code components meet through the shared argument,
and `codeArity` applies. The goal is a path in a set, so both truncations are
eliminated against set-ness.
<!--zh-->
函数性正是「码决定其元数」这一事实经表读出的样子：同一个码的两条成员关系迫使两个被记录的数码一致。向外的读式把每条成员变成子项索引，每个条目都是码与其元数数码的对，对单射性把两个对都拆开，两个码分量经共享的自变量相遇，`codeArity` 随之可用。目标是一条集合中的道路，故两次截断都对着集性消去。
<!--/-->

```agda
  hS-fun : {n : ℕ} (T : KT ⟪ A ⟫ n) (u v v' : V ℓ)
         → ⟨ pr u v ∈ fst (hS T) ⟩ → ⟨ pr u v' ∈ fst (hS T) ⟩ → v ≡ v'
  hS-fun T u v v' p q = PT.rec (setIsSet v v') step₁ (hS-out T (pr u v) p)
    where
    step₁ : Σ[ i ∈ Fin (sizeK T) ] (fst (hEntry (subK T i)) ≡ pr u v) → v ≡ v'
    step₁ (i , ei) = PT.rec (setIsSet v v') step₂ (hS-out T (pr u v') q)
      where
      step₂ : Σ[ j ∈ Fin (sizeK T) ] (fst (hEntry (subK T j)) ≡ pr u v') → v ≡ v'
      step₂ (j , ej) = vi ∙ cong #_ mi≡mj ∙ vj
        where
        qi : pr (C.code (subK T i .snd)) (# (subK T i .fst)) ≡ pr u v
        qi = sym (hEntry-eq (subK T i)) ∙ ei
        qj : pr (C.code (subK T j .snd)) (# (subK T j .fst)) ≡ pr u v'
        qj = sym (hEntry-eq (subK T j)) ∙ ej
        vi : v ≡ # (subK T i .fst)
        vi = sym (pr-inj qi .snd)
        vj : # (subK T j .fst) ≡ v'
        vj = pr-inj qj .snd
        ar : C.code (subK T i .snd) ≡ C.code (subK T j .snd)
        ar = pr-inj qi .fst ∙ sym (pr-inj qj .fst)
        mi≡mj : subK T i .fst ≡ subK T j .fst
        mi≡mj = codeArity (subK T i .snd) (subK T j .snd) ar
```

<!--en-->
## The packaged omega
<!--zh-->
## 打包的 ω
<!--/-->

<!--en-->
The branch shapes pin numeral payloads by membership in ω, so the chapter needs
ω as a constant of the object language: an element of the model whose underlying
set is the hierarchy's ω. That ω is constructible is the axiom-of-infinity step,
settled classically by the stage chapter: an ordinal appears at the stage after
itself. This chapter inherits the price exactly as the table chapter's tail
does, so everything below lives in one module under the excluded middle; the
constructibility proof is the choice chapter's one line.
<!--zh-->
分支形状以「属于 ω」钉住数码载荷，故本章需要 ω 作为对象语言的常元：一个模型元素，其底集是层级的 ω。ω 可构造正是无穷公理那一步，由阶段章以经典方式了结：序数现身于自身之后的阶段。本章照表章尾部的方式继承这份代价，故以下一切住进排中律之下的同一个模块；可构造性证明就是选择章的那一行。
<!--/-->

```agda
module WithLEM (lem : LEM (ℓ-suc ℓ)) where
  open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )

  private
    ω-isL : ⟨ isL ω ⟩
    ω-isL = Lset→isL (sucV ω) (suc-ord ω-ord) ω (ord∈Lset-suc ω ω-ord)

    ωS : S
    ωS = ω , ω-isL
```

<!--en-->
## The functionality of the annotation table
<!--zh-->
## 注解表的函数性
<!--/-->

<!--en-->
An annotation pairs a code with a numeral, and the certificate will trust it,
so the same code must have at most one annotation. The first conjunct of the
certificate says exactly this: the h-slot is a functional set of pairs. Three
binders pick the argument and the two recorded values, two application readers
read the two pairs out of h, and one object equality forces the values to
agree. The two readings are the model chapter's single-valuedness pair, with
the hypothesis read through the conjunction; per the recorded law they travel
as two directions, never as a path, and each direction's application facts are
transported through the adequacy equation.
<!--zh-->
注解把码与数码配成对，而证书将要信任它，故同一个码至多有一条注解。证书的第一条合取说的恰是这一点：h 槽位是一个函数性的有序对之集。三个绑定子挑出自变量与两个被记录的取值，两条应用读式从 h 中读出两个对，一条对象等式迫使两个取值一致。两个读式是模型章的单值性那一对，假设改经合取读出；按在案定律，它们以两个方向行走，绝不以一条路径，每个方向的应用事实都经充分性等式传输。
<!--/-->

```agda
  private
    f1 : {n : ℕ} → Fin (suc (suc n))
    f1 = suc zero
    f2 : {n : ℕ} → Fin (suc (suc (suc n)))
    f2 = suc f1
    f3 : {n : ℕ} → Fin (suc (suc (suc (suc n))))
    f3 = suc f2
    f4 : {n : ℕ} → Fin (suc (suc (suc (suc (suc n)))))
    f4 = suc f3
    f5 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc n))))))
    f5 = suc f4
    f6 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
    f6 = suc f5
    f7 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
    f7 = suc f6
    f8 : {n : ℕ} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
    f8 = suc f7

    sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
    sh2 x = suc (suc x)

    sh3 : ∀ {n} → Fin n → Fin (suc (suc (suc n)))
    sh3 x = suc (suc (suc x))

    sh4 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc n))))
    sh4 x = suc (suc (suc (suc x)))

    sh5 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc n)))))
    sh5 x = suc (suc (suc (suc (suc x))))

    sh6 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc n))))))
    sh6 x = suc (suc (suc (suc (suc (suc x)))))

  FunAt : ∀ {n} → Fin n → Formula S n
  FunAt h = ∀̇ (∀̇ (∀̇ (
      ( appAt (sh3 h) f2 f1
      ∧̇ appAt (sh3 h) f2 zero )
    ⇒̇ (var f1 ≐ var zero) )))

  module _ {n : ℕ} (h : Fin n) (γ : S ^ n) where
    Fun-out : ⟨ γ ⊨ FunAt h ⟩ → (u v v' : S)
            → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
            → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
            → fst v ≡ fst v'
    Fun-out f u v v' p q =
      f u v v'
        ( appFill (sh3 h) f2 f1 (v' ∷ v ∷ u ∷ γ) p
        , appFill (sh3 h) f2 zero (v' ∷ v ∷ u ∷ γ) q )

    Fun-in : ((u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
            → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
            → fst v ≡ fst v')
           → ⟨ γ ⊨ FunAt h ⟩
    Fun-in hstep u v v' p =
      hstep u v v'
        ( appRead (sh3 h) f2 f1 (v' ∷ v ∷ u ∷ γ) (p .fst) )
        ( appRead (sh3 h) f2 zero (v' ∷ v ∷ u ∷ γ) (p .snd) )
```

<!--en-->
## The certificate branches
<!--zh-->
## 证书分支
<!--/-->

<!--en-->
One frame per constructor, in tag order, each with its meta shape and both
readings, following the node clauses of the table chapter. The shapes are the
certificate's meta-level content: the numeral payloads against ω, the indices
as members of their numerals, the parameter leaf as a member of the carrier,
the children present in the main table, and the annotations agreeing.
<!--zh-->
每构造子一个框架，按标签排序，各带元层形状与双向读式，沿表章的节点子句。形状是证书的元层内容：数码载荷对着 ω，指标作为其数码的成员，参数叶作为载体的成员，孩子在场于主表，注解彼此一致。
<!--/-->

<!--en-->
The allK leaf is the base: x is the pair of tag zero with a numeral payload m,
m is a member of ω, and the pair (x, m) is annotated in h. Its meta shape is
the smallest of the eight: one existential, three conjuncts, and both readings
assemble directly from the tag reader and the application reader, no
composition needed.
<!--zh-->
allK 叶是基底：x 是标签零与数码载荷 m 的对，m 是 ω 的成员，而对 (x, m) 在 h 中被注解。它的元层形状是八个中最小的：一个存在量词、三条合取，两个读式由标签读式与应用读式直接组装，无需复合。
<!--/-->

```agda
  Cert0At : ∀ {n} → Fin n → Fin n → Formula S n
  Cert0At x h = ∃̇
    ( (var zero ∈̇ con ωS)
    ∧̇ ( tagPrAt 0 (suc x) zero
      ∧̇ appAt (suc h) (suc x) zero ) )

  Cert0Of : V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert0Of h x = Σ[ mv ∈ S ]
    ( ⟨ fst mv ∈ˢ ω ⟩ × (x ≡ pr (# 0) (fst mv)) × ⟨ pr x (fst mv) ∈ h ⟩ )

  module _ {n : ℕ} (x h : Fin n) (γ : S ^ n) where
    Cert0-out : ⟨ γ ⊨ Cert0At x h ⟩
              → ∥ Cert0Of (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
    Cert0-out = PT.rec PT.squash₁ (λ { (mv , body) → finish mv body })
      where
      finish : (mv : S)
             → ⟨ (mv ∷ γ) ⊨ (var zero ∈̇ con ωS)
                   ∧̇ ( tagPrAt 0 (suc x) zero
                     ∧̇ appAt (suc h) (suc x) zero ) ⟩
             → ∥ Cert0Of (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      finish mv (h1 , (h2 , h3)) =
        ∣ mv
        , ( h1
          , ( tagPr-out 0 (suc x) zero (mv ∷ γ) h2
            , appRead (suc h) (suc x) zero (mv ∷ γ) h3 ) )
        ∣₁

    Cert0-in : Cert0Of (fst (lookup h γ)) (fst (lookup x γ))
             → ⟨ γ ⊨ Cert0At x h ⟩
    Cert0-in (mv , (m∈ω , (qe , eh))) =
      ∣ mv
      , ( m∈ω
        , ( tagPr-in 0 (suc x) zero (mv ∷ γ) qe
          , appFill (suc h) (suc x) zero (mv ∷ γ) eh ) )
      ∣₁
```

<!--en-->
The two selection leaves share one frame: the payload is a pair of pairs, so
the tag reader's payload is one intermediate pair value, split twice by the
pair reader into a numeral n and two indices i and j, each a member of n. The
memberships are n against ω and the two indices against n, and the annotation
pairs x with n. The meta shape collapses the intermediates into one composed
equation, exactly as the table chapter's selection leaf does, and both readings
walk the same chain in opposite directions.
<!--zh-->
两条选择叶共用一个框架：载荷是两层对，故标签读式的载荷是一个中间对值，由对读式两次拆成数码 n 与两个指标 i、j，各为 n 的成员。成员关系是 n 对 ω、两个指标对 n，而注解把 x 与 n 配成对。元层形状把中间件塌缩成一条复合等式，恰如表章的选择叶，两个读式沿同一条链反向行走。
<!--/-->

```agda
  module CertSel (tg : ℕ) where
    CertSelAt : ∀ {n} → Fin n → Fin n → Formula S n
    CertSelAt x h = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
      ( tagPrAt tg (sh5 x) f4
      ∧̇ ( prAtL f4 f2
            f3
      ∧̇ ( prAtL f3 f1 zero
      ∧̇ ( (var f2 ∈̇ con ωS)
      ∧̇ ( (var f1 ∈̇ var f2)
      ∧̇ ( (var zero ∈̇ var f2)
      ∧̇ appAt (sh5 h) (sh5 x) f2 ))))))))))

    CertSelOf : V ℓ → V ℓ → Type (ℓ-suc ℓ)
    CertSelOf h x = Σ[ nv ∈ S ] Σ[ iv ∈ S ] Σ[ jv ∈ S ]
      ( ⟨ fst nv ∈ˢ ω ⟩ × ⟨ fst iv ∈ˢ fst nv ⟩ × ⟨ fst jv ∈ˢ fst nv ⟩
      × (x ≡ pr (# tg) (pr (fst nv) (pr (fst iv) (fst jv))))
      × ⟨ pr x (fst nv) ∈ h ⟩ )

    module _ {n : ℕ} (x h : Fin n) (γ : S ^ n) where
      CertSel-out : ⟨ γ ⊨ CertSelAt x h ⟩
                  → ∥ CertSelOf (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      CertSel-out =
        PT.rec PT.squash₁ (λ { (p₁ , w₁) →
        PT.rec PT.squash₁ (λ { (p₂ , w₂) →
        PT.rec PT.squash₁ (λ { (nv , w₃) →
        PT.rec PT.squash₁ (λ { (iv , w₄) →
        PT.rec PT.squash₁ (λ { (jv , body) → finish p₁ p₂ nv iv jv body })
        w₄ }) w₃ }) w₂ }) w₁ })
        where
        finish : (p₁ p₂ nv iv jv : S)
               → ⟨ (jv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ)
                     ⊨ ( tagPrAt tg (sh5 x) f4
                       ∧̇ ( prAtL f4 f2
                             f3
                       ∧̇ ( prAtL f3 f1 zero
                       ∧̇ ( (var f2 ∈̇ con ωS)
                       ∧̇ ( (var f1 ∈̇ var f2)
                       ∧̇ ( (var zero ∈̇ var f2)
                       ∧̇ appAt (sh5 h) (sh5 x) f2 )))))) ⟩
               → ∥ CertSelOf (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
        finish p₁ p₂ nv iv jv (h1 , (h2 , (h3 , (h4 , (h5 , (h6 , h7)))))) =
          ∣ nv , iv , jv ,
            ( h4
            , ( h5
              , ( h6
                , ( ( tagPr-out tg (sh5 x) f4 env h1
                    ∙ cong (pr (# tg))
                        ( prRead f4 f2 f3 env h2
                        ∙ cong (pr (fst nv)) (prRead f3 f1 zero env h3) ) )
                  , appRead (sh5 h) (sh5 x) f2 env h7 ) ) ) ) ∣₁
          where
          env : S ^ (suc (suc (suc (suc (suc n)))))
          env = jv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ

      CertSel-in : CertSelOf (fst (lookup h γ)) (fst (lookup x γ))
                 → ⟨ γ ⊨ CertSelAt x h ⟩
      CertSel-in (nv , iv , jv , (n∈ω , (i∈n , (j∈n , (qe , eh))))) =
        ∣ prʟ nv (prʟ iv jv) , ∣ prʟ iv jv , ∣ nv , ∣ iv , ∣ jv ,
          ( tagPr-in tg (sh5 x) f4 env
              (qe ∙ cong (pr (# tg))
                (sym ( prʟ-fst nv (prʟ iv jv)
                     ∙ cong (pr (fst nv)) (prʟ-fst iv jv) )))
          , ( prFill f4 f2 f3 env (prʟ-fst nv (prʟ iv jv))
          , ( prFill f3 f1 zero env (prʟ-fst iv jv)
          , ( n∈ω
            , ( i∈n
              , ( j∈n
                , appFill (sh5 h) (sh5 x) f2 env eh ) ) ) ) ) )
        ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
        where
        env : S ^ (suc (suc (suc (suc (suc n)))))
        env = jv ∷ iv ∷ nv ∷ prʟ iv jv ∷ prʟ nv (prʟ iv jv) ∷ γ

  module CertSelMem = CertSel 1
  module CertSelEq = CertSel 2
```

<!--en-->
The constant selection leaf is the selection shape with the second index
replaced by a parameter: the payload splits into a numeral n, an index i inside
n, and a member p of the carrier a. The memberships are n against ω, i against
n, and p against the carrier; the annotation still pairs x with n.
<!--zh-->
常量选择叶把选择形状的第二个指标换成参数：载荷拆成数码 n、n 内的指标 i 与载体 a 的成员 p。成员关系是 n 对 ω、i 对 n、p 对载体；注解仍把 x 与 n 配成对。
<!--/-->

```agda
  Cert3At : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  Cert3At x h a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt 3 (sh5 x) f4
    ∧̇ ( prAtL f4 f2
          f3
    ∧̇ ( prAtL f3 f1 zero
    ∧̇ ( (var f2 ∈̇ con ωS)
    ∧̇ ( (var f1 ∈̇ var f2)
    ∧̇ ( (var zero ∈̇ var (sh5 a))
    ∧̇ appAt (sh5 h) (sh5 x) f2 ))))))))))

  Cert3Of : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert3Of a h x = Σ[ nv ∈ S ] Σ[ iv ∈ S ] Σ[ pv ∈ S ]
    ( ⟨ fst nv ∈ˢ ω ⟩ × ⟨ fst iv ∈ˢ fst nv ⟩ × ⟨ fst pv ∈ˢ a ⟩
    × (x ≡ pr (# 3) (pr (fst nv) (pr (fst iv) (fst pv))))
    × ⟨ pr x (fst nv) ∈ h ⟩ )

  module _ {n : ℕ} (x h a : Fin n) (γ : S ^ n) where
    Cert3-out : ⟨ γ ⊨ Cert3At x h a ⟩
              → ∥ Cert3Of (fst (lookup a γ)) (fst (lookup h γ))
                    (fst (lookup x γ)) ∥₁
    Cert3-out =
      PT.rec PT.squash₁ (λ { (p₁ , w₁) →
      PT.rec PT.squash₁ (λ { (p₂ , w₂) →
      PT.rec PT.squash₁ (λ { (nv , w₃) →
      PT.rec PT.squash₁ (λ { (iv , w₄) →
      PT.rec PT.squash₁ (λ { (pv , body) → finish p₁ p₂ nv iv pv body })
      w₄ }) w₃ }) w₂ }) w₁ })
      where
      finish : (p₁ p₂ nv iv pv : S)
             → ⟨ (pv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ)
                   ⊨ ( tagPrAt 3 (sh5 x) f4
                     ∧̇ ( prAtL f4 f2
                           f3
                     ∧̇ ( prAtL f3 f1 zero
                     ∧̇ ( (var f2 ∈̇ con ωS)
                     ∧̇ ( (var f1 ∈̇ var f2)
                     ∧̇ ( (var zero ∈̇ var (sh5 a))
                     ∧̇ appAt (sh5 h) (sh5 x) f2 )))))) ⟩
             → ∥ Cert3Of (fst (lookup a γ)) (fst (lookup h γ))
                   (fst (lookup x γ)) ∥₁
      finish p₁ p₂ nv iv pv (h1 , (h2 , (h3 , (h4 , (h5 , (h6 , h7)))))) =
        ∣ nv , iv , pv ,
          ( h4
          , ( h5
            , ( h6
              , ( ( tagPr-out 3 (sh5 x) f4 env h1
                  ∙ cong (pr (# 3))
                      ( prRead f4 f2 f3 env h2
                      ∙ cong (pr (fst nv)) (prRead f3 f1 zero env h3) ) )
                , appRead (sh5 h) (sh5 x) f2 env h7 ) ) ) ) ∣₁
        where
        env : S ^ (suc (suc (suc (suc (suc n)))))
        env = pv ∷ iv ∷ nv ∷ p₂ ∷ p₁ ∷ γ

    Cert3-in : Cert3Of (fst (lookup a γ)) (fst (lookup h γ))
                 (fst (lookup x γ))
             → ⟨ γ ⊨ Cert3At x h a ⟩
    Cert3-in (nv , iv , pv , (n∈ω , (i∈n , (p∈a , (qe , eh))))) =
      ∣ prʟ nv (prʟ iv pv) , ∣ prʟ iv pv , ∣ nv , ∣ iv , ∣ pv ,
        ( tagPr-in 3 (sh5 x) f4 env
            (qe ∙ cong (pr (# 3))
              (sym ( prʟ-fst nv (prʟ iv pv)
                   ∙ cong (pr (fst nv)) (prʟ-fst iv pv) )))
        , ( prFill f4 f2 f3 env (prʟ-fst nv (prʟ iv pv))
        , ( prFill f3 f1 zero env (prʟ-fst iv pv)
        , ( n∈ω
          , ( i∈n
            , ( p∈a
              , appFill (sh5 h) (sh5 x) f2 env eh ) ) ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      env : S ^ (suc (suc (suc (suc (suc n)))))
      env = pv ∷ iv ∷ nv ∷ prʟ iv pv ∷ prʟ nv (prʟ iv pv) ∷ γ
```

<!--en-->
The two binary nodes share one frame: the payload is the pair of the children's
codes, read as one intermediate pair value, then split; a numeral m is a member
of ω; the children are present in the main table with their values; and the
annotations agree, x with m and each child with the same m. The meta shape
keeps the equation for x composed and the five V-facts flat, mirroring the node
clause's shape.
<!--zh-->
两条二元节点共用一个框架：载荷是两个孩子码的对，作为一个中间对值读出、再行拆开；数码 m 是 ω 的成员；孩子连同取值在场于主表；注解彼此一致，x 对 m、每个孩子对同一个 m。元层形状把 x 的等式保持复合、五个 V 事实平放，镜像节点子句的形状。
<!--/-->

```agda
  module CertBin (tg : ℕ) where
    CertBinAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    CertBinAt x g h = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇
      ( tagPrAt tg (sh6 x) f5
      ∧̇ ( prAtL f5
            f4 f3
      ∧̇ ( (var f2 ∈̇ con ωS)
      ∧̇ ( appAt (sh6 g) f4 f1
      ∧̇ ( appAt (sh6 g) f3 zero
      ∧̇ ( appAt (sh6 h) (sh6 x) f2
      ∧̇ ( appAt (sh6 h) f4 f2
      ∧̇ appAt (sh6 h) f3 f2 ))))))))))))

    CertBinOf : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
    CertBinOf g h x = Σ[ c₁ ∈ S ] Σ[ c₂ ∈ S ] Σ[ mv ∈ S ] Σ[ y₁ ∈ S ] Σ[ y₂ ∈ S ]
      ( (x ≡ pr (# tg) (pr (fst c₁) (fst c₂)))
      × ( ⟨ fst mv ∈ˢ ω ⟩
      × ( ⟨ pr (fst c₁) (fst y₁) ∈ g ⟩
      × ( ⟨ pr (fst c₂) (fst y₂) ∈ g ⟩
      × ( ⟨ pr x (fst mv) ∈ h ⟩
      × ( ⟨ pr (fst c₁) (fst mv) ∈ h ⟩
        × ⟨ pr (fst c₂) (fst mv) ∈ h ⟩ ))))))

    module _ {n : ℕ} (x g h : Fin n) (γ : S ^ n) where
      CertBin-out : ⟨ γ ⊨ CertBinAt x g h ⟩
                  → ∥ CertBinOf (fst (lookup g γ)) (fst (lookup h γ))
                        (fst (lookup x γ)) ∥₁
      CertBin-out =
        PT.rec PT.squash₁ (λ { (p₁ , w₁) →
        PT.rec PT.squash₁ (λ { (c₁ , w₂) →
        PT.rec PT.squash₁ (λ { (c₂ , w₃) →
        PT.rec PT.squash₁ (λ { (mv , w₄) →
        PT.rec PT.squash₁ (λ { (y₁ , w₅) →
        PT.rec PT.squash₁ (λ { (y₂ , body) → finish p₁ c₁ c₂ mv y₁ y₂ body })
        w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
        where
        finish : (p₁ c₁ c₂ mv y₁ y₂ : S)
               → ⟨ (y₂ ∷ y₁ ∷ mv ∷ c₂ ∷ c₁ ∷ p₁ ∷ γ)
                     ⊨ ( tagPrAt tg (sh6 x) f5
                       ∧̇ ( prAtL f5
                             f4 f3
                       ∧̇ ( (var f2 ∈̇ con ωS)
                       ∧̇ ( appAt (sh6 g) f4 f1
                       ∧̇ ( appAt (sh6 g) f3 zero
                       ∧̇ ( appAt (sh6 h) (sh6 x) f2
                       ∧̇ ( appAt (sh6 h) f4
                             f2
                       ∧̇ appAt (sh6 h) f3 f2
                            ))))))) ⟩
               → ∥ CertBinOf (fst (lookup g γ)) (fst (lookup h γ))
                     (fst (lookup x γ)) ∥₁
        finish p₁ c₁ c₂ mv y₁ y₂ (h1 , (h2 , (h3 , (h4 , (h5 , (h6 , (h7 , h8))))))) =
          ∣ c₁ , c₂ , mv , y₁ , y₂ ,
            ( ( tagPr-out tg (sh6 x) f5 env h1
                ∙ cong (pr (# tg)) (prRead f5 f4 f3 env h2) )
            , ( h3
              , ( appRead (sh6 g) f4 f1 env h4
                , ( appRead (sh6 g) f3 zero env h5
                  , ( appRead (sh6 h) (sh6 x) f2 env h6
                    , ( appRead (sh6 h) f4 f2 env h7
                      , appRead (sh6 h) f3 f2 env h8 ) ) ) ) ) ) ∣₁
          where
          env : S ^ (suc (suc (suc (suc (suc (suc n))))))
          env = y₂ ∷ y₁ ∷ mv ∷ c₂ ∷ c₁ ∷ p₁ ∷ γ

      CertBin-in : CertBinOf (fst (lookup g γ)) (fst (lookup h γ))
                     (fst (lookup x γ))
                 → ⟨ γ ⊨ CertBinAt x g h ⟩
      CertBin-in (c₁ , c₂ , mv , y₁ , y₂ , (qe , (m∈ω , (e1 , (e2 , (e3 , (e4 , e5))))))) =
        ∣ prʟ c₁ c₂ , ∣ c₁ , ∣ c₂ , ∣ mv , ∣ y₁ , ∣ y₂ ,
          ( tagPr-in tg (sh6 x) f5 env
              (qe ∙ cong (pr (# tg)) (sym (prʟ-fst c₁ c₂)))
          , ( prFill f5 f4 f3 env (prʟ-fst c₁ c₂)
          , ( m∈ω
            , ( appFill (sh6 g) f4 f1 env e1
              , ( appFill (sh6 g) f3 zero env e2
                , ( appFill (sh6 h) (sh6 x) f2 env e3
                  , ( appFill (sh6 h) f4 f2 env e4
                    , appFill (sh6 h) f3 f2 env e5 ) ) ) ) ) ) )
        ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
        where
        env : S ^ (suc (suc (suc (suc (suc (suc n))))))
        env = y₂ ∷ y₁ ∷ mv ∷ c₂ ∷ c₁ ∷ prʟ c₁ c₂ ∷ γ

  module CertBin4 = CertBin 4
  module CertBin5 = CertBin 5
```

<!--en-->
The complement node is the unary sibling: the payload splits into a numeral n
and a child code c, the child is present in the main table with its value, and
the annotations agree, x with n and the child with the same n.
<!--zh-->
补节点是一元的同胞：载荷拆成数码 n 与孩子码 c，孩子连同取值在场于主表，注解彼此一致，x 对 n、孩子对同一个 n。
<!--/-->

```agda
  Cert6At : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  Cert6At x g h = ∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt 6 (sh4 x) f3
    ∧̇ ( prAtL f3 f2 f1
    ∧̇ ( (var f2 ∈̇ con ωS)
    ∧̇ ( appAt (sh4 g) f1 zero
    ∧̇ ( appAt (sh4 h) (sh4 x) f2
    ∧̇ appAt (sh4 h) f1 f2 ))))))))

  Cert6Of : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert6Of g h x = Σ[ nv ∈ S ] Σ[ cv ∈ S ] Σ[ yv ∈ S ]
    ( ⟨ fst nv ∈ˢ ω ⟩
    × (x ≡ pr (# 6) (pr (fst nv) (fst cv)))
    × ( ⟨ pr (fst cv) (fst yv) ∈ g ⟩
    × ( ⟨ pr x (fst nv) ∈ h ⟩
      × ⟨ pr (fst cv) (fst nv) ∈ h ⟩ )))

  module _ {n : ℕ} (x g h : Fin n) (γ : S ^ n) where
    Cert6-out : ⟨ γ ⊨ Cert6At x g h ⟩
              → ∥ Cert6Of (fst (lookup g γ)) (fst (lookup h γ))
                    (fst (lookup x γ)) ∥₁
    Cert6-out =
      PT.rec PT.squash₁ (λ { (p₁ , w₁) →
      PT.rec PT.squash₁ (λ { (nv , w₂) →
      PT.rec PT.squash₁ (λ { (cv , w₃) →
      PT.rec PT.squash₁ (λ { (yv , body) → finish p₁ nv cv yv body })
      w₃ }) w₂ }) w₁ })
      where
      finish : (p₁ nv cv yv : S)
             → ⟨ (yv ∷ cv ∷ nv ∷ p₁ ∷ γ)
                   ⊨ ( tagPrAt 6 (sh4 x) f3
                     ∧̇ ( prAtL f3 f2 f1
                     ∧̇ ( (var f2 ∈̇ con ωS)
                     ∧̇ ( appAt (sh4 g) f1 zero
                     ∧̇ ( appAt (sh4 h) (sh4 x) f2
                     ∧̇ appAt (sh4 h) f1 f2 ))))) ⟩
             → ∥ Cert6Of (fst (lookup g γ)) (fst (lookup h γ))
                   (fst (lookup x γ)) ∥₁
      finish p₁ nv cv yv (h1 , (h2 , (h3 , (h4 , (h5 , h6))))) =
        ∣ nv , cv , yv ,
          ( h3
          , ( ( tagPr-out 6 (sh4 x) f3 env h1
              ∙ cong (pr (# 6)) (prRead f3 f2 f1 env h2) )
          , ( appRead (sh4 g) f1 zero env h4
            , ( appRead (sh4 h) (sh4 x) f2 env h5
              , appRead (sh4 h) f1 f2 env h6 ) ) ) ) ∣₁
        where
        env : S ^ (suc (suc (suc (suc n))))
        env = yv ∷ cv ∷ nv ∷ p₁ ∷ γ

    Cert6-in : Cert6Of (fst (lookup g γ)) (fst (lookup h γ))
                 (fst (lookup x γ))
             → ⟨ γ ⊨ Cert6At x g h ⟩
    Cert6-in (nv , cv , yv , (n∈ω , (qe , (e1 , (e2 , e3))))) =
      ∣ prʟ nv cv , ∣ nv , ∣ cv , ∣ yv ,
        ( tagPr-in 6 (sh4 x) f3 env
            (qe ∙ cong (pr (# 6)) (sym (prʟ-fst nv cv)))
        , ( prFill f3 f2 f1 env (prʟ-fst nv cv)
        , ( n∈ω
          , ( appFill (sh4 g) f1 zero env e1
            , ( appFill (sh4 h) (sh4 x) f2 env e2
              , appFill (sh4 h) f1 f2 env e3 ) ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁
      where
      env : S ^ (suc (suc (suc (suc n))))
      env = yv ∷ cv ∷ nv ∷ prʟ nv cv ∷ γ
```

<!--en-->
The shift is the one branch whose annotation is not the shared numeral itself:
x is the pair of tag seven with a child code c, a numeral m is a member of ω,
and the child's annotation is the internal successor of m, read by the
successor atom, while the shift's own annotation is m. The meta shape therefore
records the m'-value as sucV of the m-value.
<!--zh-->
移位是注解并非共享数码本身的那一个分支：x 是标签七与孩子码 c 的对，数码 m 是 ω 的成员，孩子的注解是 m 的内层后继，由后继原子读出，而移位自身的注解是 m。元层形状因此把 m′ 的取值记为 m 取值的 sucV。
<!--/-->

```agda
  Cert7At : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  Cert7At x g h = ∃̇ (∃̇ (∃̇ (∃̇
    ( tagPrAt 7 (sh4 x) f3
    ∧̇ ( (var f2 ∈̇ con ωS)
    ∧̇ ( sucAtL f2 f1
    ∧̇ ( appAt (sh4 g) f3 zero
    ∧̇ ( appAt (sh4 h) (sh4 x) f2
    ∧̇ appAt (sh4 h) f3 f1 ))))))))

  Cert7Of : V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  Cert7Of g h x = Σ[ cv ∈ S ] Σ[ mv ∈ S ] Σ[ mv' ∈ S ] Σ[ yv ∈ S ]
    ( (x ≡ pr (# 7) (fst cv))
    × ( ⟨ fst mv ∈ˢ ω ⟩
    × ( (fst mv' ≡ sucV (fst mv))
    × ( ⟨ pr (fst cv) (fst yv) ∈ g ⟩
    × ( ⟨ pr x (fst mv) ∈ h ⟩
      × ⟨ pr (fst cv) (fst mv') ∈ h ⟩ )))))

  module _ {n : ℕ} (x g h : Fin n) (γ : S ^ n) where
    Cert7-out : ⟨ γ ⊨ Cert7At x g h ⟩
              → ∥ Cert7Of (fst (lookup g γ)) (fst (lookup h γ))
                    (fst (lookup x γ)) ∥₁
    Cert7-out =
      PT.rec PT.squash₁ (λ { (cv , w₁) →
      PT.rec PT.squash₁ (λ { (mv , w₂) →
      PT.rec PT.squash₁ (λ { (mv' , w₃) →
      PT.rec PT.squash₁ (λ { (yv , body) → finish cv mv mv' yv body })
      w₃ }) w₂ }) w₁ })
      where
      finish : (cv mv mv' yv : S)
             → ⟨ (yv ∷ mv' ∷ mv ∷ cv ∷ γ)
                   ⊨ ( tagPrAt 7 (sh4 x) f3
                     ∧̇ ( (var f2 ∈̇ con ωS)
                     ∧̇ ( sucAtL f2 f1
                     ∧̇ ( appAt (sh4 g) f3 zero
                     ∧̇ ( appAt (sh4 h) (sh4 x) f2
                     ∧̇ appAt (sh4 h) f3 f1 ))))) ⟩
             → ∥ Cert7Of (fst (lookup g γ)) (fst (lookup h γ))
                   (fst (lookup x γ)) ∥₁
      finish cv mv mv' yv (h1 , (h2 , (h3 , (h4 , (h5 , h6))))) =
        ∣ cv , mv , mv' , yv ,
          ( tagPr-out 7 (sh4 x) f3 env h1
          , ( h2
            , ( sucRead f2 f1 env h3
              , ( appRead (sh4 g) f3 zero env h4
                , ( appRead (sh4 h) (sh4 x) f2 env h5
                  , appRead (sh4 h) f3 f1 env h6 ) ) ) ) ) ∣₁
        where
        env : S ^ (suc (suc (suc (suc n))))
        env = yv ∷ mv' ∷ mv ∷ cv ∷ γ

    Cert7-in : Cert7Of (fst (lookup g γ)) (fst (lookup h γ))
                 (fst (lookup x γ))
             → ⟨ γ ⊨ Cert7At x g h ⟩
    Cert7-in (cv , mv , mv' , yv , (qe , (m∈ω , (qq , (e1 , (e2 , e3)))))) =
      ∣ cv , ∣ mv , ∣ mv' , ∣ yv ,
        ( tagPr-in 7 (sh4 x) f3 env qe
        , ( m∈ω
          , ( sucFill f2 f1 env qq
            , ( appFill (sh4 g) f3 zero env e1
              , ( appFill (sh4 h) (sh4 x) f2 env e2
                , appFill (sh4 h) f3 f1 env e3 ) ) ) ) )
      ∣₁ ∣₁ ∣₁ ∣₁
      where
      env : S ^ (suc (suc (suc (suc n))))
      env = yv ∷ mv' ∷ mv ∷ cv ∷ γ
```

<!--en-->
## The disjunction
<!--zh-->
## 析取
<!--/-->

<!--en-->
Eight shapes, one disjunction, in tag order, with the same right-nested
associativity as the table chapter's clause. The outward reader peels the
disjunction and hands each branch to its own reader; the eight injections are
what the certificate uses on the way in, one per branch; and the inward reader
dispatches the meta shape back to the disjunction through the injections, so
the certificate can assemble satisfaction from a shape.
<!--zh-->
八个形状，一个析取，按标签排序，与表章子句同样的右嵌套结合。向外的读式剥开析取，把每个分支递给自己的读式；八个注入是证书进入方向将使用的东西，每分支一个；向内的读式把元层形状经注入分发回析取，使证书能从形状装配满足。
<!--/-->

```agda
  CertShapeAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  CertShapeAt x g h a =
    Cert0At x h
    ∨̇ ( CertSelMem.CertSelAt x h
    ∨̇ ( CertSelEq.CertSelAt x h
    ∨̇ ( Cert3At x h a
    ∨̇ ( CertBin4.CertBinAt x g h
    ∨̇ ( CertBin5.CertBinAt x g h
    ∨̇ ( Cert6At x g h
      ∨̇ Cert7At x g h ))))))

  CertOf : V ℓ → V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
  CertOf a g h x =
    Cert0Of h x
    ⊎ ( CertSelMem.CertSelOf h x
    ⊎ ( CertSelEq.CertSelOf h x
    ⊎ ( Cert3Of a h x
    ⊎ ( CertBin4.CertBinOf g h x
    ⊎ ( CertBin5.CertBinOf g h x
    ⊎ ( Cert6Of g h x
      ⊎ Cert7Of g h x ))))))

  module _ {n : ℕ} (x g h a : Fin n) (γ : S ^ n) where
    CertShape-out : ⟨ γ ⊨ CertShapeAt x g h a ⟩
                  → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                        (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
    CertShape-out = PT.rec PT.squash₁ br₁
      where
      br₈ : ⟨ γ ⊨ Cert6At x g h ⟩ ⊎ ⟨ γ ⊨ Cert7At x g h ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₈ (inl p) = PT.map (λ c → inr (inr (inr (inr (inr (inr (inl c)))))))
        (Cert6-out x g h γ p)
      br₈ (inr p) = PT.map (λ c → inr (inr (inr (inr (inr (inr (inr c)))))))
        (Cert7-out x g h γ p)
      br₇ : ⟨ γ ⊨ CertBin5.CertBinAt x g h ⟩
          ⊎ ⟨ γ ⊨ (Cert6At x g h ∨̇ Cert7At x g h) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₇ (inl p) = PT.map (λ c → inr (inr (inr (inr (inr (inl c))))))
        (CertBin5.CertBin-out x g h γ p)
      br₇ (inr r) = PT.rec PT.squash₁ br₈ r
      br₆ : ⟨ γ ⊨ CertBin4.CertBinAt x g h ⟩
          ⊎ ⟨ γ ⊨ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h)) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₆ (inl p) = PT.map (λ c → inr (inr (inr (inr (inl c)))))
        (CertBin4.CertBin-out x g h γ p)
      br₆ (inr r) = PT.rec PT.squash₁ br₇ r
      br₅ : ⟨ γ ⊨ Cert3At x h a ⟩
          ⊎ ⟨ γ ⊨ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₅ (inl p) = PT.map (λ c → inr (inr (inr (inl c))))
        (Cert3-out x h a γ p)
      br₅ (inr r) = PT.rec PT.squash₁ br₆ r
      br₄ : ⟨ γ ⊨ CertSelEq.CertSelAt x h ⟩
          ⊎ ⟨ γ ⊨ (Cert3At x h a
                ∨̇ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h)))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₄ (inl p) = PT.map (λ c → inr (inr (inl c)))
        (CertSelEq.CertSel-out x h γ p)
      br₄ (inr r) = PT.rec PT.squash₁ br₅ r
      br₃ : ⟨ γ ⊨ CertSelMem.CertSelAt x h ⟩
          ⊎ ⟨ γ ⊨ (CertSelEq.CertSelAt x h
                ∨̇ (Cert3At x h a
                ∨̇ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h))))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₃ (inl p) = PT.map (λ c → inr (inl c))
        (CertSelMem.CertSel-out x h γ p)
      br₃ (inr r) = PT.rec PT.squash₁ br₄ r
      br₁ : ⟨ γ ⊨ Cert0At x h ⟩
          ⊎ ⟨ γ ⊨ (CertSelMem.CertSelAt x h
                ∨̇ (CertSelEq.CertSelAt x h
                ∨̇ (Cert3At x h a
                ∨̇ (CertBin4.CertBinAt x g h
                ∨̇ (CertBin5.CertBinAt x g h
                ∨̇ (Cert6At x g h ∨̇ Cert7At x g h)))))) ⟩
          → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                (fst (lookup h γ)) (fst (lookup x γ)) ∥₁
      br₁ (inl p) = PT.map inl (Cert0-out x h γ p)
      br₁ (inr r) = PT.rec PT.squash₁ br₃ r

    cert₀ : ⟨ γ ⊨ Cert0At x h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₀ p = ∣ inl p ∣₁
    cert₁ : ⟨ γ ⊨ CertSelMem.CertSelAt x h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₁ p = ∣ inr ∣ inl p ∣₁ ∣₁
    cert₂ : ⟨ γ ⊨ CertSelEq.CertSelAt x h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₂ p = ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁
    cert₃ : ⟨ γ ⊨ Cert3At x h a ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₃ p = ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁
    cert₄ : ⟨ γ ⊨ CertBin4.CertBinAt x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₄ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    cert₅ : ⟨ γ ⊨ CertBin5.CertBinAt x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₅ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    cert₆ : ⟨ γ ⊨ Cert6At x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₆ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    cert₇ : ⟨ γ ⊨ Cert7At x g h ⟩ → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    cert₇ p = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr p ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

    CertShape-in : CertOf (fst (lookup a γ)) (fst (lookup g γ))
                     (fst (lookup h γ)) (fst (lookup x γ))
                 → ⟨ γ ⊨ CertShapeAt x g h a ⟩
    CertShape-in (inl c) = cert₀ (Cert0-in x h γ c)
    CertShape-in (inr (inl c)) = cert₁ (CertSelMem.CertSel-in x h γ c)
    CertShape-in (inr (inr (inl c))) = cert₂ (CertSelEq.CertSel-in x h γ c)
    CertShape-in (inr (inr (inr (inl c)))) = cert₃ (Cert3-in x h a γ c)
    CertShape-in (inr (inr (inr (inr (inl c))))) =
      cert₄ (CertBin4.CertBin-in x g h γ c)
    CertShape-in (inr (inr (inr (inr (inr (inl c)))))) =
      cert₅ (CertBin5.CertBin-in x g h γ c)
    CertShape-in (inr (inr (inr (inr (inr (inr (inl c))))))) =
      cert₆ (Cert6-in x g h γ c)
    CertShape-in (inr (inr (inr (inr (inr (inr (inr c))))))) =
      cert₇ (Cert7-in x g h γ c)
```

<!--en-->
## The certificate
<!--zh-->
## 证书
<!--/-->

<!--en-->
The certificate is the step condition, approximation-shaped: functionality of
the annotation table, then two binders reading the main table's membership at
the pair (x, y) and demanding the certificate shape at x, with the carrier and
both tables riding at their own slots. Its three readers are the
approximation's three, with the functionality split out: the outward direction
yields the functional reading and the step reading, and the inward direction
reassembles the formula from the two.
<!--zh-->
证书就是那条步条件，逼近形状：注解表的函数性，然后两个绑定子读出主表在对 (x, y) 处的隶属，并要求 x 处的证书形状，载体与两张表落在各自的槽位上。它的三个读式是逼近的三个，只是把函数性单独拆出：向外得出函数读式与步读式，向内从二者重新组装公式。
<!--/-->

```agda
  CertAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  CertAt g h a = FunAt h ∧̇ ∀̇ (∀̇ ( appAt (sh2 g) f1 zero
                                ⇒̇ CertShapeAt f1 (sh2 g) (sh2 h) (sh2 a) ))

  module _ {n : ℕ} (g h a : Fin n) (γ : S ^ n) where
    Cert-fun : ⟨ γ ⊨ CertAt g h a ⟩ → (u v v' : S)
             → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
             → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
             → fst v ≡ fst v'
    Cert-fun cert u v v' p q = Fun-out h γ (cert .fst) u v v' p q

    Cert-step : ⟨ γ ⊨ CertAt g h a ⟩ → (x y : S)
              → ⟨ pr (fst x) (fst y) ∈ fst (lookup g γ) ⟩
              → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                    (fst (lookup h γ)) (fst x) ∥₁
    Cert-step cert x y p =
      CertShape-out f1 (sh2 g) (sh2 h) (sh2 a) (y ∷ x ∷ γ)
        (cert .snd x y (appFill (sh2 g) f1 zero (y ∷ x ∷ γ) p))

    Cert-in : ((u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
             → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
             → fst v ≡ fst v')
            → ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup g γ) ⟩
               → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                     (fst (lookup h γ)) (fst x) ∥₁)
            → ⟨ γ ⊨ CertAt g h a ⟩
    Cert-in hstep xstep =
      Fun-in h γ hstep
      , (λ x y p →
          PT.rec PT.squash₁
            (CertShape-in f1 (sh2 g) (sh2 h) (sh2 a) (y ∷ x ∷ γ))
            (xstep x y (appRead (sh2 g) f1 zero (y ∷ x ∷ γ) p)))
```

<!--en-->
## Honesty
<!--zh-->
## 诚实性
<!--/-->

<!--en-->
Honesty is the certificate's payoff: every pair in a certified table, at its
unique annotation m, is the code of an honest term of arity m. The recursion
that reads the branches back into terms runs on the accessibility of the
transitive closure, not of membership itself. A child code sits four
membership steps below its node code, and the termination checker follows only
one step, so composing accessibility projections through helper functions
would be rejected; the closure records the whole descent in one derivation, and
each recursive call applies the matched accessibility function to a chain.
The eight branches are the eight code equations run backwards. A branch pins
its tag, numeral, indices, parameter leaf, and children locally, and each
continuation assembles a term constructor, rewrites the branch's shape
equation along the numeral paths, and closes against the constructor's code
equation. Functionality is what lets the given arity meet the branch's
recorded one: the annotation table is functional by the certificate's first
conjunct, so the annotated pair (x, # m) and the pair (x, mv) force
`fst mv ≡ # m`, and every numeral-shaped datum of the branch is then read at
the arity the caller supplied.
<!--zh-->
诚实性是证书的兑现：受证的表中的每个对，在其唯一注解 m 处，就是元数 m 的诚实项的码。把各分支读回项的递归，跑在传递闭包的可及性上，而非成员关系本身的可及性上。孩子码坐在节点码之下四步成员关系处，而终止检查器只跟一步，故经辅助函数复合可及性投影会被拒绝；闭包把整段下降记在一条推导里，每次递归调用把被匹配的可及性函数施于一条链。八个分支就是把八条码等式反向运行。分支在局部钉住标签、数码、指标、参数叶与孩子，每条续延组装一个项构造子，沿数码路径重写分支的形状等式，再对构造子的码等式反向收口。函数性正是让给定元数与分支记录的元数相遇的地方：注解表由证书第一条合取保证函数性，故被注解的对 (x, # m) 与 (x, mv) 迫使 `fst mv ≡ # m`，分支的每个数码形数据随后都按调用者给出的元数读出。
<!--/-->

```agda
  module Honest {n : ℕ} (g h a : Fin n) (γ : S ^ n)
                (cert : ⟨ γ ⊨ CertAt g h a ⟩) where
    private
      G  = fst (lookup g γ)
      H  = fst (lookup h γ)
      A₀ = fst (lookup a γ)
      module C = Codes A₀ (snd (lookup a γ))

    Honest : V ℓ → ℕ → Type (ℓ-suc ℓ)
    Honest x m = ∥ Σ[ t ∈ KT ⟪ A₀ ⟫ m ] (x ≡ C.code t) ∥₁

    honest : (x : V ℓ) → Acc _∈⁺_ x
           → (y : V ℓ) → ⟨ pr x y ∈ G ⟩
           → (m : ℕ) → ⟨ pr x (# m) ∈ H ⟩
           → Honest x m
    honest x (acc r) y hy m hm =
      PT.rec PT.squash₁ fromShape
        (Cert-step g h a γ cert (x , lx) (y , ly) hy)
      where
      lx : ⟨ isL x ⟩
      lx = prIsL₁ (snd (lookup h γ)) hm

      ly : ⟨ isL y ⟩
      ly = prIsL₂ (snd (lookup g γ)) hy

      l#m : ⟨ isL (# m) ⟩
      l#m = subst (λ z → ⟨ isL z ⟩) (numeralL-fst m) (numeralL m .snd)

      mEq : (mv : S) → ⟨ fst mv ∈ˢ ω ⟩ → ⟨ pr x (fst mv) ∈ H ⟩ → fst mv ≡ # m
      mEq mv mω ann = sym (Cert-fun g h a γ cert (x , lx) (# m , l#m) mv hm ann)

      fromB0 : Cert0Of H x → Honest x m
      fromB0 (mv , (mω , (qe , ann))) =
        ∣ allK
        , ( qe
          ∙ cong (pr (# 0)) (mEq mv mω ann)
          ∙ sym (C.code-allK m) ) ∣₁

      fromSel : (tg : ℕ) (mk : (i j : Fin m) → KT ⟪ A₀ ⟫ m)
              → ((i j : Fin m) → C.code (mk i j)
                    ≡ pr (# tg) (pr (# m) (pr (# (toℕ i)) (# (toℕ j)))))
              → Σ[ nv ∈ S ] Σ[ iv ∈ S ] Σ[ jv ∈ S ]
                  ( ⟨ fst nv ∈ˢ ω ⟩ × ⟨ fst iv ∈ˢ fst nv ⟩
                  × ⟨ fst jv ∈ˢ fst nv ⟩
                  × (x ≡ pr (# tg) (pr (fst nv) (pr (fst iv) (fst jv))))
                  × ⟨ pr x (fst nv) ∈ H ⟩ )
              → Honest x m
      fromSel tg mk codeEq (nv , iv , jv , (nω , (i∈n , (j∈n , (qe , ann))))) =
        PT.rec PT.squash₁
          (λ { (î , î<m , ivEq) →
          PT.rec PT.squash₁
            (λ { (ĵ , ĵ<m , jvEq) →
              let
                i : Fin m
                i = fromℕ' m î î<m
                j : Fin m
                j = fromℕ' m ĵ ĵ<m
                iv→#i : # (toℕ i) ≡ fst iv
                iv→#i = cong #_ (toFromId' m î î<m) ∙ sym ivEq
                jv→#j : # (toℕ j) ≡ fst jv
                jv→#j = cong #_ (toFromId' m ĵ ĵ<m) ∙ sym jvEq
                eq : x ≡ C.code (mk i j)
                eq = qe
                   ∙ cong (pr (# tg))
                       ( cong (pr (fst nv))
                           ( cong (pr (fst iv)) (sym jv→#j)
                           ∙ cong₂ pr (sym iv→#i) refl )
                       ∙ cong₂ pr nv→m refl )
                   ∙ sym (codeEq i j)
              in ∣ mk i j , eq ∣₁ })
            (∈#-elim m (fst jv) j∈m) })
          (∈#-elim m (fst iv) i∈m)
        where
        nv→m : fst nv ≡ # m
        nv→m = mEq nv nω ann
        i∈m : ⟨ fst iv ∈ˢ (# m) ⟩
        i∈m = subst (λ w → ⟨ fst iv ∈ˢ w ⟩) nv→m i∈n
        j∈m : ⟨ fst jv ∈ˢ (# m) ⟩
        j∈m = subst (λ w → ⟨ fst jv ∈ˢ w ⟩) nv→m j∈n

      fromSelMem : CertSelMem.CertSelOf H x → Honest x m
      fromSelMem = fromSel 1 selMemK (C.code-selMemK m)

      fromSelEq : CertSelEq.CertSelOf H x → Honest x m
      fromSelEq = fromSel 2 selEqK (C.code-selEqK m)

      fromCon : Cert3Of A₀ H x → Honest x m
      fromCon (nv , iv , pv , (nω , (i∈n , (p∈a , (qe , ann))))) =
        PT.rec PT.squash₁
          (λ { (î , î<m , ivEq) →
            let
              i : Fin m
              i = fromℕ' m î î<m
              iv→#i : # (toℕ i) ≡ fst iv
              iv→#i = cong #_ (toFromId' m î î<m) ∙ sym ivEq
              par : ⟪ A₀ ⟫
              par = ∈-asFiber {a = fst pv} {b = A₀} p∈a .fst
              epar : ⟪ A₀ ⟫↪ par ≡ fst pv
              epar = ∈-asFiber {a = fst pv} {b = A₀} p∈a .snd
              eq : x ≡ C.code (selEqConK i par)
              eq = qe
                 ∙ cong (pr (# 3))
                     ( cong (pr (fst nv))
                         ( cong (pr (fst iv)) (sym epar)
                         ∙ cong₂ pr (sym iv→#i) refl )
                     ∙ cong₂ pr nv→m refl )
                 ∙ sym (C.code-selEqConK m i par)
            in ∣ selEqConK i par , eq ∣₁ })
          (∈#-elim m (fst iv) i∈m)
        where
        nv→m : fst nv ≡ # m
        nv→m = mEq nv nω ann
        i∈m : ⟨ fst iv ∈ˢ (# m) ⟩
        i∈m = subst (λ w → ⟨ fst iv ∈ˢ w ⟩) nv→m i∈n

      fromBin : (tg : ℕ) (mk : KT ⟪ A₀ ⟫ m → KT ⟪ A₀ ⟫ m → KT ⟪ A₀ ⟫ m)
              → ((s' t' : KT ⟪ A₀ ⟫ m) → C.code (mk s' t')
                    ≡ pr (# tg) (pr (C.code s') (C.code t')))
              → CertBin.CertBinOf tg G H x → Honest x m
      fromBin tg mk codeEq (c₁ , c₂ , mv , y₁ , y₂ ,
                 (qe , (mω , (e1 , (e2 , (ann , (ann₁₀ , ann₂₀))))))) =
        PT.rec PT.squash₁
          (λ { (t₁ , e₁) →
          PT.rec PT.squash₁
            (λ { (t₂ , e₂) →
              let
                eq : x ≡ C.code (mk t₁ t₂)
                eq = qe
                   ∙ cong (pr (# tg))
                       ( cong (pr (fst c₁)) e₂
                       ∙ cong₂ pr e₁ refl )
                   ∙ sym (codeEq t₁ t₂)
              in ∣ mk t₁ t₂ , eq ∣₁ })
            (honest (fst c₂) (r (fst c₂) chain₂) (fst y₂) e2 m ann₂) })
          (honest (fst c₁) (r (fst c₁) chain₁) (fst y₁) e1 m ann₁)
        where
        nv→m : fst mv ≡ # m
        nv→m = mEq mv mω ann
        ann₁ : ⟨ pr (fst c₁) (# m) ∈ H ⟩
        ann₁ = subst (λ w → ⟨ pr (fst c₁) w ∈ H ⟩) nv→m ann₁₀
        ann₂ : ⟨ pr (fst c₂) (# m) ∈ H ⟩
        ann₂ = subst (λ w → ⟨ pr (fst c₂) w ∈ H ⟩) nv→m ann₂₀
        chain₀ : fst c₁ ∈⁺ pr (# tg) (pr (fst c₁) (fst c₂))
        chain₀ = trans⁺ (chainFst (fst c₁) (fst c₂))
                         (chainSnd (# tg) (pr (fst c₁) (fst c₂)))
        chain₁ : fst c₁ ∈⁺ x
        chain₁ = subst (λ w → fst c₁ ∈⁺ w) (sym qe) chain₀
        chain₂₀ : fst c₂ ∈⁺ pr (# tg) (pr (fst c₁) (fst c₂))
        chain₂₀ = trans⁺ (chainSnd (fst c₁) (fst c₂))
                          (chainSnd (# tg) (pr (fst c₁) (fst c₂)))
        chain₂ : fst c₂ ∈⁺ x
        chain₂ = subst (λ w → fst c₂ ∈⁺ w) (sym qe) chain₂₀

      fromInter : CertBin4.CertBinOf G H x → Honest x m
      fromInter = fromBin 4 interK (λ s' t' → C.code-interK s' t')

      fromUnion : CertBin5.CertBinOf G H x → Honest x m
      fromUnion = fromBin 5 unionK (λ s' t' → C.code-unionK s' t')

      fromCompl : Cert6Of G H x → Honest x m
      fromCompl (nv , cv , yv , (nω , (qe , (e1 , (ann , ann₀))))) =
        PT.rec PT.squash₁
          (λ { (t' , e') →
            let
              eq : x ≡ C.code (complK t')
              eq = qe
                 ∙ cong (pr (# 6))
                     ( cong (pr (fst nv)) e'
                     ∙ cong₂ pr nv→m refl )
                 ∙ sym (C.code-complK t')
            in ∣ complK t' , eq ∣₁ })
          (honest (fst cv) (r (fst cv) chain) (fst yv) e1 m ann₁)
        where
        nv→m : fst nv ≡ # m
        nv→m = mEq nv nω ann
        ann₁ : ⟨ pr (fst cv) (# m) ∈ H ⟩
        ann₁ = subst (λ w → ⟨ pr (fst cv) w ∈ H ⟩) nv→m ann₀
        chain₀ : fst cv ∈⁺ pr (# 6) (pr (fst nv) (fst cv))
        chain₀ = trans⁺ (chainSnd (fst nv) (fst cv))
                         (chainSnd (# 6) (pr (fst nv) (fst cv)))
        chain : fst cv ∈⁺ x
        chain = subst (λ w → fst cv ∈⁺ w) (sym qe) chain₀

      fromShift : Cert7Of G H x → Honest x m
      fromShift (cv , mv , mv' , yv , (qe , (mω , (qq , (e1 , (ann , ann₀)))))) =
        PT.rec PT.squash₁
          (λ { (t' , e') →
            let
              eq : x ≡ C.code (shiftK t')
              eq = qe ∙ cong (pr (# 7)) e' ∙ sym (C.code-shiftK t')
            in ∣ shiftK t' , eq ∣₁ })
          (honest (fst cv) (r (fst cv) chain) (fst yv) e1 (suc m) ann₁)
        where
        mv→m : fst mv ≡ # m
        mv→m = mEq mv mω ann
        mv'→m' : fst mv' ≡ # (suc m)
        mv'→m' = qq ∙ cong sucV mv→m
        ann₁ : ⟨ pr (fst cv) (# (suc m)) ∈ H ⟩
        ann₁ = subst (λ w → ⟨ pr (fst cv) w ∈ H ⟩) mv'→m' ann₀
        chain₀ : fst cv ∈⁺ pr (# 7) (fst cv)
        chain₀ = chainSnd (# 7) (fst cv)
        chain : fst cv ∈⁺ x
        chain = subst (λ w → fst cv ∈⁺ w) (sym qe) chain₀

      fromShape : CertOf A₀ G H x → Honest x m
      fromShape (inl c) = fromB0 c
      fromShape (inr (inl c)) = fromSelMem c
      fromShape (inr (inr (inl c))) = fromSelEq c
      fromShape (inr (inr (inr (inl c)))) = fromCon c
      fromShape (inr (inr (inr (inr (inl c))))) = fromInter c
      fromShape (inr (inr (inr (inr (inr (inl c)))))) = fromUnion c
      fromShape (inr (inr (inr (inr (inr (inr (inl c))))))) = fromCompl c
      fromShape (inr (inr (inr (inr (inr (inr (inr c))))))) = fromShift c
```

<!--en-->
## The certificate's fill
<!--zh-->
## 证书的填充
<!--/-->

<!--en-->
The certificate's fill is the honest side of the bargain: the honest pair of
tables, the approximation and the annotation over the same term, is certified.
The route is the approximation family's own structural recursion, now
recording arities. A pair in the main table is, by the outward reading, the
entry of some subterm; each constructor case assembles its branch shape from
the code equation run forwards, the numeral memberships at the recorded arity,
the index memberships by the numeral-order introduction, the parameter leaf by
the embedding's membership, and the children's entries and annotations through
membership functions threaded down the recursion. The thread is grounded at
the head by the two self-memberships and extended by the approximation's
monotonicity, now stated twice, once per table. The functionality conjunct is
the honest table's functionality transported along the h-pin, and the
per-pair certificates assemble the certificate through the inward reader.
<!--zh-->
证书的填充是契约的诚实一侧：诚实的一对表，同一项上的逼近与注解，是受证的。路线是逼近族自己跑的那条结构递归，如今记录元数。主表中的对经向外的读式是某个子项的条目；每个构造子情形以正向运行的码等式、记录元数处的数码成员、经数码序引入的指标成员、嵌入的成员关系的参数叶，以及经递归中穿引的成员函数的孩子条目与孩子注解，装配出分支形状。线头由两条自身成员奠基，并经逼近的单调性延展，而单调性如今陈述两次，每张表一次。函数性合取是诚实表的函数性经 h 钉传输而来，逐对的证书经向内读式组装出整张证书。
<!--/-->

```agda
  module CertFill (A : V ℓ) (lA : ⟨ isL A ⟩) where
    private
      module C = Codes A lA
      module D = Denote A lA

      #∈# : (a b : ℕ) → a < b → ⟨ (# a) ∈ˢ (# b) ⟩
      #∈# a zero (k , p) = Empty.rec (clash k p)
        where
        clash : (k : ℕ) → k + suc a ≡ 0 → Empty.⊥
        clash zero p = snotz p
        clash (suc k) p = snotz p
      #∈# a (suc b) (zero , p) =
        subst (λ w → ⟨ w ∈ˢ sucV (# b) ⟩) (sym (cong #_ (injSuc p))) (self∈sucV (# b))
      #∈# a (suc b) (suc k , p) =
        ∈sucV-inl {A = # b} {x = # a} (#∈# a b (k , injSuc p))

      monoInterL : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                 → ⟨ z ∈ fst (D.apxS s) ⟩ → ⟨ z ∈ fst (D.apxS (interK s t)) ⟩
      monoInterL s t z hz = PT.rec (snd (z ∈ fst (D.apxS (interK s t)))) named
        (D.apx-out s z hz)
        where
        named : Σ[ i ∈ Fin (sizeK s) ] (D.entry (subK s i) ≡ z)
              → ⟨ z ∈ fst (D.apxS (interK s t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (D.apxS (interK s t)) ⟩)
          (cong D.entry (interIdxL s t i) ∙ q)
          (D.apx-in (interK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))))

      monoInterR : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                 → ⟨ z ∈ fst (D.apxS t) ⟩ → ⟨ z ∈ fst (D.apxS (interK s t)) ⟩
      monoInterR s t z hz = PT.rec (snd (z ∈ fst (D.apxS (interK s t)))) named
        (D.apx-out t z hz)
        where
        named : Σ[ j ∈ Fin (sizeK t) ] (D.entry (subK t j) ≡ z)
              → ⟨ z ∈ fst (D.apxS (interK s t)) ⟩
        named (j , q) = subst (λ e → ⟨ e ∈ fst (D.apxS (interK s t)) ⟩)
          (cong D.entry (interIdxR s t j) ∙ q)
          (D.apx-in (interK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))))

      monoUnionL : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                 → ⟨ z ∈ fst (D.apxS s) ⟩ → ⟨ z ∈ fst (D.apxS (unionK s t)) ⟩
      monoUnionL s t z hz = PT.rec (snd (z ∈ fst (D.apxS (unionK s t)))) named
        (D.apx-out s z hz)
        where
        named : Σ[ i ∈ Fin (sizeK s) ] (D.entry (subK s i) ≡ z)
              → ⟨ z ∈ fst (D.apxS (unionK s t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (D.apxS (unionK s t)) ⟩)
          (cong D.entry (unionIdxL s t i) ∙ q)
          (D.apx-in (unionK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))))

      monoUnionR : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                 → ⟨ z ∈ fst (D.apxS t) ⟩ → ⟨ z ∈ fst (D.apxS (unionK s t)) ⟩
      monoUnionR s t z hz = PT.rec (snd (z ∈ fst (D.apxS (unionK s t)))) named
        (D.apx-out t z hz)
        where
        named : Σ[ j ∈ Fin (sizeK t) ] (D.entry (subK t j) ≡ z)
              → ⟨ z ∈ fst (D.apxS (unionK s t)) ⟩
        named (j , q) = subst (λ e → ⟨ e ∈ fst (D.apxS (unionK s t)) ⟩)
          (cong D.entry (unionIdxR s t j) ∙ q)
          (D.apx-in (unionK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))))

      monoCompl : {n : ℕ} (t : KT ⟪ A ⟫ n) (z : V ℓ)
                → ⟨ z ∈ fst (D.apxS t) ⟩ → ⟨ z ∈ fst (D.apxS (complK t)) ⟩
      monoCompl t z hz = PT.rec (snd (z ∈ fst (D.apxS (complK t)))) named
        (D.apx-out t z hz)
        where
        named : Σ[ i ∈ Fin (sizeK t) ] (D.entry (subK t i) ≡ z)
              → ⟨ z ∈ fst (D.apxS (complK t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (D.apxS (complK t)) ⟩) q
          (D.apx-in (complK t) (suc i))

      monoShift : {n : ℕ} (t : KT ⟪ A ⟫ (suc n)) (z : V ℓ)
                → ⟨ z ∈ fst (D.apxS t) ⟩ → ⟨ z ∈ fst (D.apxS (shiftK t)) ⟩
      monoShift t z hz = PT.rec (snd (z ∈ fst (D.apxS (shiftK t)))) named
        (D.apx-out t z hz)
        where
        named : Σ[ i ∈ Fin (sizeK t) ] (D.entry (subK t i) ≡ z)
              → ⟨ z ∈ fst (D.apxS (shiftK t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (D.apxS (shiftK t)) ⟩) q
          (D.apx-in (shiftK t) (suc i))

      hMonoInterL : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                  → ⟨ z ∈ fst (hS A lA s) ⟩ → ⟨ z ∈ fst (hS A lA (interK s t)) ⟩
      hMonoInterL s t z hz = PT.rec (snd (z ∈ fst (hS A lA (interK s t)))) named
        (hS-out A lA s z hz)
        where
        named : Σ[ i ∈ Fin (sizeK s) ] (fst (hEntry A lA (subK s i)) ≡ z)
              → ⟨ z ∈ fst (hS A lA (interK s t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (hS A lA (interK s t)) ⟩)
          (cong fst (cong (hEntry A lA) (interIdxL s t i)) ∙ q)
          (hS-in A lA (interK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))))

      hMonoInterR : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                  → ⟨ z ∈ fst (hS A lA t) ⟩ → ⟨ z ∈ fst (hS A lA (interK s t)) ⟩
      hMonoInterR s t z hz = PT.rec (snd (z ∈ fst (hS A lA (interK s t)))) named
        (hS-out A lA t z hz)
        where
        named : Σ[ j ∈ Fin (sizeK t) ] (fst (hEntry A lA (subK t j)) ≡ z)
              → ⟨ z ∈ fst (hS A lA (interK s t)) ⟩
        named (j , q) = subst (λ e → ⟨ e ∈ fst (hS A lA (interK s t)) ⟩)
          (cong fst (cong (hEntry A lA) (interIdxR s t j)) ∙ q)
          (hS-in A lA (interK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))))

      hMonoUnionL : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                  → ⟨ z ∈ fst (hS A lA s) ⟩ → ⟨ z ∈ fst (hS A lA (unionK s t)) ⟩
      hMonoUnionL s t z hz = PT.rec (snd (z ∈ fst (hS A lA (unionK s t)))) named
        (hS-out A lA s z hz)
        where
        named : Σ[ i ∈ Fin (sizeK s) ] (fst (hEntry A lA (subK s i)) ≡ z)
              → ⟨ z ∈ fst (hS A lA (unionK s t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (hS A lA (unionK s t)) ⟩)
          (cong fst (cong (hEntry A lA) (unionIdxL s t i)) ∙ q)
          (hS-in A lA (unionK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inl i))))

      hMonoUnionR : {n : ℕ} (s t : KT ⟪ A ⟫ n) (z : V ℓ)
                  → ⟨ z ∈ fst (hS A lA t) ⟩ → ⟨ z ∈ fst (hS A lA (unionK s t)) ⟩
      hMonoUnionR s t z hz = PT.rec (snd (z ∈ fst (hS A lA (unionK s t)))) named
        (hS-out A lA t z hz)
        where
        named : Σ[ j ∈ Fin (sizeK t) ] (fst (hEntry A lA (subK t j)) ≡ z)
              → ⟨ z ∈ fst (hS A lA (unionK s t)) ⟩
        named (j , q) = subst (λ e → ⟨ e ∈ fst (hS A lA (unionK s t)) ⟩)
          (cong fst (cong (hEntry A lA) (unionIdxR s t j)) ∙ q)
          (hS-in A lA (unionK s t) (suc (FinSumChar.fun (sizeK s) (sizeK t) (inr j))))

      hMonoCompl : {n : ℕ} (t : KT ⟪ A ⟫ n) (z : V ℓ)
                 → ⟨ z ∈ fst (hS A lA t) ⟩ → ⟨ z ∈ fst (hS A lA (complK t)) ⟩
      hMonoCompl t z hz = PT.rec (snd (z ∈ fst (hS A lA (complK t)))) named
        (hS-out A lA t z hz)
        where
        named : Σ[ i ∈ Fin (sizeK t) ] (fst (hEntry A lA (subK t i)) ≡ z)
              → ⟨ z ∈ fst (hS A lA (complK t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (hS A lA (complK t)) ⟩) q
          (hS-in A lA (complK t) (suc i))

      hMonoShift : {n : ℕ} (t : KT ⟪ A ⟫ (suc n)) (z : V ℓ)
                 → ⟨ z ∈ fst (hS A lA t) ⟩ → ⟨ z ∈ fst (hS A lA (shiftK t)) ⟩
      hMonoShift t z hz = PT.rec (snd (z ∈ fst (hS A lA (shiftK t)))) named
        (hS-out A lA t z hz)
        where
        named : Σ[ i ∈ Fin (sizeK t) ] (fst (hEntry A lA (subK t i)) ≡ z)
              → ⟨ z ∈ fst (hS A lA (shiftK t)) ⟩
        named (i , q) = subst (λ e → ⟨ e ∈ fst (hS A lA (shiftK t)) ⟩) q
          (hS-in A lA (shiftK t) (suc i))

    certClause : {m : ℕ} (T : KT ⟪ A ⟫ m) (i : Fin (sizeK T)) {n : ℕ}
               → (g h a : Fin n) (γ : S ^ n)
               → ((z : V ℓ) → ⟨ z ∈ fst (D.apxS T) ⟩ → ⟨ z ∈ fst (lookup g γ) ⟩)
               → ((z : V ℓ) → ⟨ z ∈ fst (hS A lA T) ⟩ → ⟨ z ∈ fst (lookup h γ) ⟩)
               → fst (lookup a γ) ≡ A
               → CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                   (C.code (subK T i .snd))
    certClause {m} allK zero g h a γ embG embH qa = all-cont
      where
      all-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                   (C.code allK)
      all-cont = inl ( (# m , numL m)
        , ( #∈ω m
          , ( C.code-allK m
            , embH (pr (C.code allK) (# m)) (hSelf∈ A lA allK) ) ) )
    certClause {m} (selMemK i j) zero g h a γ embG embH qa = selMem-cont
      where
      selMem-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                      (C.code (selMemK i j))
      selMem-cont = inr (inl
        ( (# m , numL m) , (# (toℕ i) , numL (toℕ i)) , (# (toℕ j) , numL (toℕ j))
        , ( #∈ω m
          , ( #∈# (toℕ i) m (toℕ<n i)
            , ( #∈# (toℕ j) m (toℕ<n j)
              , ( C.code-selMemK m i j
                , embH (pr (C.code (selMemK i j)) (# m)) (hSelf∈ A lA (selMemK i j)) ) ) ) ) ) )
    certClause {m} (selEqK i j) zero g h a γ embG embH qa = selEq-cont
      where
      selEq-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                     (C.code (selEqK i j))
      selEq-cont = inr (inr (inl
        ( (# m , numL m) , (# (toℕ i) , numL (toℕ i)) , (# (toℕ j) , numL (toℕ j))
        , ( #∈ω m
          , ( #∈# (toℕ i) m (toℕ<n i)
            , ( #∈# (toℕ j) m (toℕ<n j)
              , ( C.code-selEqK m i j
                , embH (pr (C.code (selEqK i j)) (# m)) (hSelf∈ A lA (selEqK i j)) ) ) ) ) ) ) )
    certClause {m} (selEqConK i a') zero g h a γ embG embH qa = con-cont
      where
      con-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                   (C.code (selEqConK i a'))
      con-cont = inr (inr (inr (inl
        ( (# m , numL m) , (# (toℕ i) , numL (toℕ i)) , C.paramS a'
        , ( #∈ω m
          , ( #∈# (toℕ i) m (toℕ<n i)
            , ( subst (λ w → ⟨ ⟪ A ⟫↪ a' ∈ˢ w ⟩) (sym qa)
                  (∈∈ₛ {a = ⟪ A ⟫↪ a'} {b = A} .snd (∈ₛ⟪ A ⟫↪ a'))
              , ( C.code-selEqConK m i a'
                , embH (pr (C.code (selEqConK i a')) (# m)) (hSelf∈ A lA (selEqConK i a')) ) ) ) ) ) ) ) )
    certClause {m} (interK u v) zero g h a γ embG embH qa = inter-cont
      where
      inter-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                     (C.code (interK u v))
      inter-cont = inr (inr (inr (inr (inl
        ( C.codeS u , C.codeS v , (# m , numL m)
        , (⟦_⟧ᴷ A u , denoteL A lA u) , (⟦_⟧ᴷ A v , denoteL A lA v)
        , ( C.code-interK u v
          , ( #∈ω m
            , ( embG (pr (C.code u) (⟦_⟧ᴷ A u))
                  (monoInterL u v (pr (C.code u) (⟦_⟧ᴷ A u)) (D.entrySelf∈ u))
              , ( embG (pr (C.code v) (⟦_⟧ᴷ A v))
                    (monoInterR u v (pr (C.code v) (⟦_⟧ᴷ A v)) (D.entrySelf∈ v))
                , ( embH (pr (C.code (interK u v)) (# m)) (hSelf∈ A lA (interK u v))
                  , ( embH (pr (C.code u) (# m))
                        (hMonoInterL u v (pr (C.code u) (# m)) (hSelf∈ A lA u))
                    , embH (pr (C.code v) (# m))
                        (hMonoInterR u v (pr (C.code v) (# m)) (hSelf∈ A lA v)) ) ) ) ) ) ) )))))
    certClause {m} (unionK u v) zero g h a γ embG embH qa = union-cont
      where
      union-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                     (C.code (unionK u v))
      union-cont = inr (inr (inr (inr (inr (inl
        ( C.codeS u , C.codeS v , (# m , numL m)
        , (⟦_⟧ᴷ A u , denoteL A lA u) , (⟦_⟧ᴷ A v , denoteL A lA v)
        , ( C.code-unionK u v
          , ( #∈ω m
            , ( embG (pr (C.code u) (⟦_⟧ᴷ A u))
                  (monoUnionL u v (pr (C.code u) (⟦_⟧ᴷ A u)) (D.entrySelf∈ u))
              , ( embG (pr (C.code v) (⟦_⟧ᴷ A v))
                    (monoUnionR u v (pr (C.code v) (⟦_⟧ᴷ A v)) (D.entrySelf∈ v))
                , ( embH (pr (C.code (unionK u v)) (# m)) (hSelf∈ A lA (unionK u v))
                  , ( embH (pr (C.code u) (# m))
                        (hMonoUnionL u v (pr (C.code u) (# m)) (hSelf∈ A lA u))
                    , embH (pr (C.code v) (# m))
                        (hMonoUnionR u v (pr (C.code v) (# m)) (hSelf∈ A lA v)) ) ) ) ) ) ) ))))))
    certClause {m} (complK t) zero g h a γ embG embH qa = compl-cont
      where
      compl-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                     (C.code (complK t))
      compl-cont = inr (inr (inr (inr (inr (inr (inl
        ( (# m , numL m) , C.codeS t , (⟦_⟧ᴷ A t , denoteL A lA t)
        , ( #∈ω m
          , ( C.code-complK t
            , ( embG (pr (C.code t) (⟦_⟧ᴷ A t))
                  (monoCompl t (pr (C.code t) (⟦_⟧ᴷ A t)) (D.entrySelf∈ t))
              , ( embH (pr (C.code (complK t)) (# m)) (hSelf∈ A lA (complK t))
                , embH (pr (C.code t) (# m))
                    (hMonoCompl t (pr (C.code t) (# m)) (hSelf∈ A lA t)) ) ) ) ) )))))))
    certClause {m} (shiftK t) zero g h a γ embG embH qa = shift-cont
      where
      shift-cont : CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                     (C.code (shiftK t))
      shift-cont = inr (inr (inr (inr (inr (inr (inr
        ( C.codeS t , (# m , numL m) , (# (suc m) , numL (suc m))
        , (⟦_⟧ᴷ A t , denoteL A lA t)
        , ( C.code-shiftK t
          , ( #∈ω m
            , ( refl
              , ( embG (pr (C.code t) (⟦_⟧ᴷ A t))
                    (monoShift t (pr (C.code t) (⟦_⟧ᴷ A t)) (D.entrySelf∈ t))
                , ( embH (pr (C.code (shiftK t)) (# m)) (hSelf∈ A lA (shiftK t))
                  , embH (pr (C.code t) (# (suc m)))
                      (hMonoShift t (pr (C.code t) (# (suc m))) (hSelf∈ A lA t)) ) ) ) ) ))))))))
    certClause (interK u v) (suc k') g h a γ embG embH qa =
      goSplit (FinSumChar.inv (sizeK u) (sizeK v) k')
      where
      goSplit : (x' : Fin (sizeK u) ⊎ Fin (sizeK v))
              → CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                  (C.code (subSplitK u v x' .snd))
      goSplit (inl i') = certClause u i' g h a γ
        (λ z hz → embG z (monoInterL u v z hz))
        (λ z hz → embH z (hMonoInterL u v z hz))
        qa
      goSplit (inr j') = certClause v j' g h a γ
        (λ z hz → embG z (monoInterR u v z hz))
        (λ z hz → embH z (hMonoInterR u v z hz))
        qa
    certClause (unionK u v) (suc k') g h a γ embG embH qa =
      goSplit (FinSumChar.inv (sizeK u) (sizeK v) k')
      where
      goSplit : (x' : Fin (sizeK u) ⊎ Fin (sizeK v))
              → CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                  (C.code (subSplitK u v x' .snd))
      goSplit (inl i') = certClause u i' g h a γ
        (λ z hz → embG z (monoUnionL u v z hz))
        (λ z hz → embH z (hMonoUnionL u v z hz))
        qa
      goSplit (inr j') = certClause v j' g h a γ
        (λ z hz → embG z (monoUnionR u v z hz))
        (λ z hz → embH z (hMonoUnionR u v z hz))
        qa
    certClause (complK t) (suc k') g h a γ embG embH qa =
      certClause t k' g h a γ
        (λ z hz → embG z (monoCompl t z hz))
        (λ z hz → embH z (hMonoCompl t z hz))
        qa
    certClause (shiftK t) (suc k') g h a γ embG embH qa =
      certClause t k' g h a γ
        (λ z hz → embG z (monoShift t z hz))
        (λ z hz → embH z (hMonoShift t z hz))
        qa

    certApx : {n' : ℕ} (T : KT ⟪ A ⟫ n') {n : ℕ} (g h a : Fin n) (γ : S ^ n)
            → fst (lookup g γ) ≡ fst (D.apxS T)
            → fst (lookup h γ) ≡ fst (hS A lA T)
            → fst (lookup a γ) ≡ A
            → ⟨ γ ⊨ CertAt g h a ⟩
    certApx T g h a γ qg qh qa = Cert-in g h a γ hstep xstep
      where
      hstep : (u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst (lookup h γ) ⟩
            → ⟨ pr (fst u) (fst v') ∈ fst (lookup h γ) ⟩
            → fst v ≡ fst v'
      hstep u v v' p q = hS-fun A lA T (fst u) (fst v) (fst v')
        (subst (λ w → ⟨ pr (fst u) (fst v) ∈ w ⟩) qh p)
        (subst (λ w → ⟨ pr (fst u) (fst v') ∈ w ⟩) qh q)

      xstep : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst (lookup g γ) ⟩
            → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                  (fst x) ∥₁
      xstep x y e = PT.rec PT.squash₁ named
        (D.apx-out T (pr (fst x) (fst y))
          (subst (λ w → ⟨ pr (fst x) (fst y) ∈ w ⟩) qg e))
        where
        named : Σ[ i ∈ Fin (sizeK T) ] (D.entry (subK T i) ≡ pr (fst x) (fst y))
              → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ)) (fst (lookup h γ))
                    (fst x) ∥₁
        named (i , q) =
          subst (λ u → ∥ CertOf (fst (lookup a γ)) (fst (lookup g γ))
                            (fst (lookup h γ)) u ∥₁)
            (pr-inj (sym (D.entry-eq (subK T i)) ∙ q) .fst)
            ∣ certClause T i g h a γ embG embH qa ∣₁
          where
          embG : (z : V ℓ) → ⟨ z ∈ fst (D.apxS T) ⟩ → ⟨ z ∈ fst (lookup g γ) ⟩
          embG z hz = subst (λ w → ⟨ z ∈ w ⟩) (sym qg) hz
          embH : (z : V ℓ) → ⟨ z ∈ fst (hS A lA T) ⟩ → ⟨ z ∈ fst (lookup h γ) ⟩
          embH z hz = subst (λ w → ⟨ z ∈ w ⟩) (sym qh) hz
```

<!--en-->
## The step body, and its two laws
<!--zh-->
## 步本体，与它的两条定律
<!--/-->

<!--en-->
The step body quantifies a certified, approximated pair of tables and one
arity-one entry, and cuts the member as the values of that entry. Two binders
read the main table and the annotation table out of the environment; the
certificate and the approximation hold over the carrier at its own slot; three
more binders read an entry (x, y) of the main table whose annotation is the
numeral one, and the member is pinned to the values of y. The formula mentions
no carrier, so the family recursion ahead can instantiate it at any stage.
<!--zh-->
步本体量化一对受证且被逼近的表与一个元数一的条目，并把成员裁为该条目的取值。两个绑定子从环境中读出主表与注解表；证书与逼近在载体于自己的槽位上成立；再三个绑定子读出主表的一个条目 (x, y)，其注解是数码一，成员则被钉在 y 的取值上。公式不提及载体，故前方的族递归可在任一层处实例化它。
<!--/-->

```agda
  private
    nameBody : ∀ {n} → Fin n → Formula S (suc (suc (suc (suc (suc n)))))
    nameBody v = (var zero ≐ con (numeralL 1))
               ∧̇ ( appAt f4 f2 f1
                 ∧̇ ( appAt f3 f2 zero
                   ∧̇ valuesAt (sh5 v) f1 ))

    nameAt : ∀ {n} → Fin n → Fin n → Formula S n
    nameAt v a = ∃̇ (∃̇ ( CertAt f1 zero (sh2 a)
                      ∧̇ ( ApproxAt f1 (sh2 a)
                        ∧̇ ∃̇ (∃̇ (∃̇ (nameBody v))) )))

  StepAt : ∀ {n} → Fin n → Fin n → Formula S n
  StepAt b a = ∀̇ ( ( (var zero ∈̇ var (suc b)) ⇒̇ nameAt zero (suc a) )
                 ∧̇ ( nameAt zero (suc a) ⇒̇ (var zero ∈̇ var (suc b)) ) )
```

<!--en-->
The outward law spends the three facts in sequence. Reading a certified,
approximated entry back into the definable powerset is honesty at the
arity-one annotation, then the table chapter's value lemma pins the entry's
second component to the denotation of the honest term, and the terms chapter's
banked equivalence, transported forward, lands the member in `𝒟ₒ`. The inward
law assembles the same entry from the fill side's witnesses, applied at one
term: a member of `𝒟ₒ` is, by the same equivalence transported backwards, the
values of some arity-one term, and the approximation, the annotation, the
certificate, and the membership facts are the honest pair of tables the fill
already certified. The two laws share one reading and one filling, per member.
<!--zh-->
向外定律按顺序花掉三条事实：把受证的被逼近条目读回可定义幂集，先是元数一注解处的诚实性，再是表章的值引理把条目的第二分量钉在诚实项的指称上，最后是项章的入账等价向前搬运，把成员送进 `𝒟ₒ`。向内定律用填充一侧的见证装配同一条目，一次施于一个项：`𝒟ₒ` 的成员经同一等价向后搬运，就是某个元数一项的取值，而逼近、注解、证书与诸成员事实，正是填充已受证的那一对诚实表。两条定律共用一个读式与一个填式，逐成员进行。
<!--/-->

```agda
  module StepLaws {n : ℕ} (b a : Fin n) (γ : S ^ n) where
    private
      B    = fst (lookup b γ)
      A₀   = fst (lookup a γ)
      lA₀  = snd (lookup a γ)

      module C  = Codes A₀ lA₀
      module D  = Denote A₀ lA₀
      module CF = CertFill A₀ lA₀
      module TW = TermsLEM A₀ lem

    read-name : (v : S) → ⟨ (v ∷ γ) ⊨ nameAt zero (suc a) ⟩ → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
    read-name v = PT.rec (snd (fst v ∈ˢ 𝒟ₒ A₀)) stepG
      where
      finish : (g₀ h₀ x y o : S)
             → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ CertAt f1 zero (sh2 (suc a)) ⟩
             → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ ApproxAt f1 (sh2 (suc a)) ⟩
             → ⟨ (o ∷ y ∷ x ∷ h₀ ∷ g₀ ∷ v ∷ γ) ⊨ nameBody zero ⟩
             → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
      finish g₀ h₀ x y o cert approx (op , (gf , (hf , vf))) =
        PT.rec (snd (fst v ∈ˢ 𝒟ₒ A₀)) land
          (H.honest (fst x) (wf⁺ (fst x)) (fst y) gF 1 hF)
        where
        env : S ^ (suc (suc (suc (suc (suc (suc n))))))
        env = o ∷ y ∷ x ∷ h₀ ∷ g₀ ∷ v ∷ γ

        module H = Honest f1 zero (sh2 (suc a)) (h₀ ∷ g₀ ∷ v ∷ γ) cert

        gF : ⟨ pr (fst x) (fst y) ∈ fst g₀ ⟩
        gF = appRead f4 f2 f1 env gf

        hF : ⟨ pr (fst x) (# 1) ∈ fst h₀ ⟩
        hF = subst (λ w → ⟨ pr (fst x) w ∈ fst h₀ ⟩) (op ∙ numeralL-fst 1)
          (appRead f3 f2 zero env hf)

        lx : ⟨ isL (fst x) ⟩
        lx = prIsL₁ (h₀ .snd) hF

        ly : ⟨ isL (fst y) ⟩
        ly = prIsL₂ (g₀ .snd) gF

        land : Σ[ t ∈ KT ⟪ A₀ ⟫ 1 ] (fst x ≡ C.code t) → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
        land (t , codeEq) = 𝒟ₒ-intro A₀ (fst v) inDef
          where
          step' : (x' y' : S) → ⟨ pr (fst x') (fst y') ∈ fst g₀ ⟩
                → ∥ ClauseOf A₀ (fst g₀) (fst x') (fst y') ∥₁
          step' x' y' e = Clause-out f1 zero (sh2 f1)
            (sh2 (sh2 (suc a))) (y' ∷ x' ∷ h₀ ∷ g₀ ∷ v ∷ γ)
            (Approx-step f1 (sh2 (suc a)) (h₀ ∷ g₀ ∷ v ∷ γ)
              approx x' y' e)

          val : fst y ≡ ⟦_⟧ᴷ A₀ t
          val = D.approx-val (fst g₀) step' t (fst x , lx) (fst y , ly) codeEq gF

          vEq : fst v ≡ values (fst y)
          vEq = valuesAt-out (sh5 zero) f1 env vf

          valEq : fst v ≡ values (⟦_⟧ᴷ A₀ t)
          valEq = vEq ∙ cong values val

          memb : ⟨ fst v ∈ termDef A₀ ⟩
          memb = ∣ t , sym valEq ∣₁

          inDef : ⟨ fst v ∈ DefOf.Def A₀ ⟩
          inDef = subst (λ z → ⟨ fst v ∈ z ⟩) TW.termDef≡Def memb

      stepO : (g₀ h₀ x y : S)
            → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ CertAt f1 zero (sh2 (suc a)) ⟩
            → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ ApproxAt f1 (sh2 (suc a)) ⟩
            → Σ[ o ∈ S ] ⟨ (o ∷ y ∷ x ∷ h₀ ∷ g₀ ∷ v ∷ γ) ⊨ nameBody zero ⟩
            → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
      stepO g₀ h₀ x y cert approx (o , w₅) = finish g₀ h₀ x y o cert approx w₅

      stepY : (g₀ h₀ x : S)
            → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ CertAt f1 zero (sh2 (suc a)) ⟩
            → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ ApproxAt f1 (sh2 (suc a)) ⟩
            → Σ[ y ∈ S ] ⟨ (y ∷ x ∷ h₀ ∷ g₀ ∷ v ∷ γ) ⊨ ∃̇ nameBody zero ⟩
            → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
      stepY g₀ h₀ x cert approx (y , w₄) = PT.rec (snd (fst v ∈ˢ 𝒟ₒ A₀))
        (stepO g₀ h₀ x y cert approx) w₄

      stepX : (g₀ h₀ : S)
            → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ CertAt f1 zero (sh2 (suc a)) ⟩
            → ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨ ApproxAt f1 (sh2 (suc a)) ⟩
            → Σ[ x ∈ S ] ⟨ (x ∷ h₀ ∷ g₀ ∷ v ∷ γ) ⊨ ∃̇ (∃̇ nameBody zero) ⟩
            → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
      stepX g₀ h₀ cert approx (x , w₃) = PT.rec (snd (fst v ∈ˢ 𝒟ₒ A₀))
        (stepY g₀ h₀ x cert approx) w₃

      stepH : (g₀ : S) → Σ[ h₀ ∈ S ] ⟨ (h₀ ∷ g₀ ∷ v ∷ γ) ⊨
                  CertAt f1 zero (sh2 (suc a))
                  ∧̇ ( ApproxAt f1 (sh2 (suc a))
                    ∧̇ ∃̇ (∃̇ (∃̇ nameBody zero)) ) ⟩
            → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
      stepH g₀ (h₀ , w₂) = PT.rec (snd (fst v ∈ˢ 𝒟ₒ A₀))
        (stepX g₀ h₀ (w₂ .fst) (w₂ .snd .fst)) (w₂ .snd .snd)

      stepG : Σ[ g₀ ∈ S ] ⟨ (g₀ ∷ v ∷ γ) ⊨
                  ∃̇ ( CertAt f1 zero (sh2 (suc a))
                     ∧̇ ( ApproxAt f1 (sh2 (suc a))
                       ∧̇ ∃̇ (∃̇ (∃̇ nameBody zero)) )) ⟩
            → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩
      stepG (g₀ , w₁) = PT.rec (snd (fst v ∈ˢ 𝒟ₒ A₀)) (stepH g₀) w₁

    fill-name : (v : S) → ⟨ fst v ∈ˢ 𝒟ₒ A₀ ⟩ → ⟨ (v ∷ γ) ⊨ nameAt zero (suc a) ⟩
    fill-name v h = PT.rec (snd ((v ∷ γ) ⊨ nameAt zero (suc a))) build
      (subst (λ z → ⟨ fst v ∈ z ⟩) (sym TW.termDef≡Def) (𝒟ₒ-inv A₀ (fst v) h))
      where
      build : Σ[ t ∈ KT ⟪ A₀ ⟫ 1 ] (values (⟦_⟧ᴷ A₀ t) ≡ fst v)
            → ⟨ (v ∷ γ) ⊨ nameAt zero (suc a) ⟩
      build (t , e) = ∣ D.apxS t
        , ∣ hS A₀ lA₀ t
          , ( cert
            , ( approx
              , ∣ C.codeS t
                , ∣ (⟦_⟧ᴷ A₀ t , denoteL A₀ lA₀ t)
                  , ∣ numeralL 1
                    , ( refl , ( gf , ( hf , vf ) ) ) ∣₁ ∣₁ ∣₁ ) )
        ∣₁ ∣₁
        where
        env : S ^ (suc (suc (suc (suc (suc (suc n))))))
        env = numeralL 1 ∷ (⟦_⟧ᴷ A₀ t , denoteL A₀ lA₀ t)
            ∷ C.codeS t ∷ hS A₀ lA₀ t ∷ D.apxS t ∷ v ∷ γ

        cert : ⟨ (hS A₀ lA₀ t ∷ D.apxS t ∷ v ∷ γ)
                  ⊨ CertAt f1 zero (sh2 (suc a)) ⟩
        cert = CF.certApx t f1 zero (sh2 (suc a))
          (hS A₀ lA₀ t ∷ D.apxS t ∷ v ∷ γ) refl refl refl

        approx : ⟨ (hS A₀ lA₀ t ∷ D.apxS t ∷ v ∷ γ)
                    ⊨ ApproxAt f1 (sh2 (suc a)) ⟩
        approx = D.apx-approx t f1 (sh2 (suc a))
          (hS A₀ lA₀ t ∷ D.apxS t ∷ v ∷ γ) refl refl

        gf : ⟨ env ⊨ appAt f4
                  f2 f1 ⟩
        gf = appFill f4 f2 f1 env (D.entrySelf∈ t)

        hf : ⟨ env ⊨ appAt f3 f2 zero ⟩
        hf = appFill f3 f2 zero env
          (subst (λ w → ⟨ pr (fst (C.codeS t)) w ∈ fst (hS A₀ lA₀ t) ⟩)
            (sym (numeralL-fst 1)) (hSelf∈ A₀ lA₀ t))

        vf : ⟨ env ⊨ valuesAt (sh5 zero) f1 ⟩
        vf = valuesAt-in (sh5 zero) f1 env (sym e)

    step-out : ⟨ γ ⊨ StepAt b a ⟩ → B ≡ 𝒟ₒ A₀
    step-out h = extensionalV λ v → ⇔toPath (fwdV v) (bwdV v)
      where
      fwdV : (v : V ℓ) → ⟨ v ∈ B ⟩ → ⟨ v ∈ 𝒟ₒ A₀ ⟩
      fwdV v v∈B = read-name (v , lv) (h (v , lv) .fst v∈B)
        where
        lv : ⟨ isL v ⟩
        lv = isL-trans {x = B} {y = v} v∈B (snd (lookup b γ))

      bwdV : (v : V ℓ) → ⟨ v ∈ 𝒟ₒ A₀ ⟩ → ⟨ v ∈ B ⟩
      bwdV v v∈D = h (v , lv) .snd (fill-name (v , lv) v∈D)
        where
        lv : ⟨ isL v ⟩
        lv = PT.rec (snd (isL v)) land
          (subst (λ z → ⟨ v ∈ z ⟩) (sym TW.termDef≡Def) (𝒟ₒ-inv A₀ v v∈D))
          where
          land : Σ[ t ∈ KT ⟪ A₀ ⟫ 1 ] (values (⟦_⟧ᴷ A₀ t) ≡ v) → ⟨ isL v ⟩
          land (t , e) = subst (λ w → ⟨ isL w ⟩) e (valuesL (denoteL A₀ lA₀ t))

    step-in : B ≡ 𝒟ₒ A₀ → ⟨ γ ⊨ StepAt b a ⟩
    step-in eq v =
      ( (λ v∈B → fill-name v (subst (λ z → ⟨ fst v ∈ z ⟩) eq v∈B))
      , (λ nameSat → subst (λ z → ⟨ fst v ∈ z ⟩) (sym eq) (read-name v nameSat)) )
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The certificate describes the tower's step with local conditions only, and
this chapter now closes over it. Each branch pins its tag by a sealed numeral,
its payload pieces as members of ω or of the carrier, its children in the main
table, and its annotations in a functional table, so every numeral-shaped leaf
is genuinely numeral and every annotation is unique and trustworthy. The fill
certifies the honest pair of tables by the same structural recursion the
approximation family runs, now recording arities, and honesty reads every
certified pair back, at its unique annotation, as the code of an honest term.
The step body quantifies that certified, approximated pair of tables and an
arity-one entry, and its two laws read the entry's values back into `𝒟ₒ` of
the carrier and fill them in again: the tower's step is now internally
describable, both ways, over codes and tables, which is exactly what the
family recursion ahead will quantify.
<!--zh-->
证书只用局部条件描述塔的一步，而本章现在把它闭合。每个分支以封印数码钉住标签，以 ω 或载体钉住载荷诸件，以主表钉住孩子，并以函数性的表钉住注解，故每个数码形叶真是数码、每条注解唯一而可信任。填充以逼近族同一条结构递归使诚实的一对表受证，如今记录元数；诚实性再把每个受证的对在唯一注解处读回为诚实项的码。步本体量化那一对受证且被逼近的表与一个元数一的条目，两条定律把条目的取值读进载体的 `𝒟ₒ`、又再填回来：塔的一步如今两个方向都可在码与表之上作内部描述，而这正是前方的族递归将要量化的东西。
<!--/-->
