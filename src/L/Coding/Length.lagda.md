# The length guard

<!--en-->
One more piece of bookkeeping, and it is the one that keeps the certificates
honest. A clause about satisfaction mentions three things at once: a formula's
code, its arity, and an environment. Nothing said so far forces the arity to be
the *length* of that environment. Without such a constraint a certificate would
be satisfied by junk, an environment of the wrong length paired with a code that
never applied to it, and the soundness argument would have nothing to push
against.

This chapter supplies the constraint as an object formula. It says that the keys
of the environment are exactly the members of the arity numeral, which by the
previous chapters means: every entry of the environment has a key below the
arity, and every number below the arity is the key of an entry. Two clauses,
both bounded, so the guard is Δ₀ and can sit inside a certificate.

Adequacy comes in two directions, and they do different jobs. One says the guard
holds of a genuine environment at its genuine length, which is what a certificate
must produce. The other says that if the guard holds then the numeral component
*is* the length, which is what kills the junk: it pins a number that was
otherwise free.
<!--zh-->
还有一件记账工作，而正是它使诸证书保持诚实。关于满足关系的子句一次提到三样东西：公式的码、它的元数，以及一个环境。迄今没有任何东西迫使那个元数就是该环境的**长度**。没有这样一条约束，证书就会被垃圾满足，即长度不对的环境配上一个从不作用于它的码，而可靠性论证便无处着力。

本章以一条对象公式供上这条约束。它说环境的键恰是元数数码的成员，而按前几章这意味着：环境的每个条目的键都低于元数，且低于元数的每个数都是某条目的键。两条子句，都有界，故这道守卫是 Δ₀ 的，可以坐进证书里面。

适足性分两个方向，各司其职。一个说守卫对真环境在其真长度处成立，那是证书必须产出的东西。另一个说若守卫成立则数码分量**就是**长度，那是杀死垃圾的东西：它把一个原本自由的数钉死。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Coding.Length {ℓ : Level} where

open import FOL.Syntax using ( var; Formula; _∧̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; δ-∧; δ-∀∈; δ-∃∈ )
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Ordinal {ℓ} using ( ∈#-elim; #∈#-elim )
open import L.Coding.Base {ℓ}
  using ( prAt; Δ₀-prAt; prAt-adequate; ∈pair-introR )
open import L.Coding.Environment {ℓ} using ( env )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
open import Cubical.Data.Nat.Order
  using ( _<_; ¬-<-zero; pred-≤-pred; ¬m<m; _≟_; lt; eq; gt )
open import Cubical.Data.FinData using ( toℕ; toℕ<n )
import Cubical.Data.Empty as Empty
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open Sem using ( _^_ )
open Sem.At (V ℓ) id using ( _⊨_; ⟦_⟧ )
```

<!--en-->
## Finding an index from a bound
<!--zh-->
## 从一个界找回索引
<!--/-->

<!--en-->
A number below `k` names an index into a family of length `k`. The conversion is
a routine recursion, and the equation saying it round-trips is another. Both are
private: they exist only so that the second adequacy direction can turn a bound
back into the entry it points at.
<!--zh-->
低于 `k` 的数为长度为 `k` 的族命名一个索引。这个转换是一次例行递归，说它往返一致的方程是另一次。二者都私有：它们的存在只是为了让第二个适足方向能把一个界换回它所指的那个条目。
<!--/-->

```agda
private
  mkFin : (m k : ℕ) → m < k → Fin k
  mkFin m       zero    p = Empty.rec (¬-<-zero p)
  mkFin zero    (suc k) p = zero
  mkFin (suc m) (suc k) p = suc (mkFin m k (pred-≤-pred p))

  toℕ-mkFin : (m k : ℕ) (p : m < k) → toℕ (mkFin m k p) ≡ m
  toℕ-mkFin m       zero    p = Empty.rec (¬-<-zero p)
  toℕ-mkFin zero    (suc k) p = refl
  toℕ-mkFin (suc m) (suc k) p = cong suc (toℕ-mkFin m k (pred-≤-pred p))
```

<!--en-->
## The guard
<!--zh-->
## 守卫
<!--/-->

<!--en-->
Two clauses, mirror images. Every member of the environment is a pair whose key
lies in the arity; every member of the arity is the key of some pair in the
environment. Each clause opens three bounded quantifiers to name the key, the
value and the intermediate set the Kuratowski encoding needs, and then the pair
reader pins the shape. The de Bruijn arithmetic is entirely determined by that
nesting.
<!--zh-->
两条子句，互为镜像。环境的每个成员是一个对，其键落在元数之中；元数的每个成员是环境中某个对的键。每条子句开三层有界量词，为键、值以及 Kuratowski 编码所需的中间集合命名，然后由对读式钉住形状。de Bruijn 的算术完全由那个嵌套决定。
<!--/-->

```agda
lenAt : ∀ {n} → Fin n → Fin n → Formula (V ℓ) n
lenAt e N =
  (∀̇∈ (var e)
    (∃̇∈ (var (suc N))
      (∃̇∈ (var (suc zero))
        (∃̇∈ (var zero)
          (prAt (suc (suc (suc zero))) (suc (suc zero)) zero)))))
  ∧̇ (∀̇∈ (var N)
      (∃̇∈ (var (suc e))
        (∃̇∈ (var zero)
          (∃̇∈ (var zero)
            (prAt (suc (suc zero)) (suc (suc (suc zero))) zero)))))

Δ₀-lenAt : ∀ {n} (e N : Fin n) → Δ₀ (lenAt e N)
Δ₀-lenAt e N =
  δ-∧ (δ-∀∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
        (Δ₀-prAt (suc (suc (suc zero))) (suc (suc zero)) zero)))))
      (δ-∀∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
        (Δ₀-prAt (suc (suc zero)) (suc (suc (suc zero))) zero)))))
```

<!--en-->
## The guard holds of a real environment
<!--zh-->
## 守卫对真环境成立
<!--/-->

<!--en-->
Given an actual environment of length `k` and the numeral for `k`, both clauses
go through. The first takes an entry, reads off its index, and observes that the
index is below `k` so its numeral belongs to the numeral for `k`. The second takes
a member of that numeral, recovers the index it names, and exhibits the entry
sitting there. Both then have to produce the intermediate sets by hand, which is
what the nested truncations are.

The two conjunct types are left to inference. Writing them out is four lines of
de Bruijn shape each and says nothing the formula above does not.
<!--zh-->
给定一个长度为 `k` 的真环境与 `k` 的数码，两条子句都走得通。第一条取一个条目，读出它的索引，注意到索引低于 `k`，故其数码属于 `k` 的数码。第二条取那个数码的一个成员，还原它所命名的索引，并拿出坐在那里的条目。随后两条都必须手工造出中间集合，那正是那些嵌套截断的内容。

两个合取分量的类型交给推断。把它们写出来，各是四行 de Bruijn 形状，而且并不比上面那条公式多说什么。
<!--/-->

```agda
lenAt-intro : ∀ {n} (e N : Fin n) (γ : (V ℓ) ^ n)
  {k : ℕ} (g : Fin k → V ℓ)
  → ⟦ var e ⟧ γ ≡ env g
  → ⟦ var N ⟧ γ ≡ # k
  → ⟨ γ ⊨ lenAt e N ⟩
lenAt-intro e N γ {k} g hE hN = conj₁ , conj₂
  where
  conj₁ : _
  conj₁ p p∈E = PT.rec
    (((p ∷ γ) ⊨ ∃̇∈ (var (suc N)) (∃̇∈ (var (suc zero)) (∃̇∈ (var zero)
       (prAt (suc (suc (suc zero))) (suc (suc zero)) zero)))) .snd)
    (λ { (li , peq) →
      ∣ # (toℕ (lower li))
      , subst (λ z → ⟨ # (toℕ (lower li)) ∈ z ⟩) (sym hN)
          (#mono (toℕ (lower li)) k (toℕ<n (lower li)))
      , ∣ ⁅ # (toℕ (lower li)) , g (lower li) ⁆
        , subst (λ z → ⟨ ⁅ # (toℕ (lower li)) , g (lower li) ⁆ ∈ z ⟩) peq
            (∈pair-introR {u = ⁅ # (toℕ (lower li)) ⁆s}
                          {v = ⁅ # (toℕ (lower li)) , g (lower li) ⁆}
                          {y = ⁅ # (toℕ (lower li)) , g (lower li) ⁆} refl)
        , ∣ g (lower li)
          , ∈pair-introR {u = # (toℕ (lower li))} {v = g (lower li)}
                         {y = g (lower li)} refl
          , subst ⟨_⟩
              (sym (prAt-adequate (suc (suc (suc zero))) (suc (suc zero)) zero
                (g (lower li) ∷ ⁅ # (toℕ (lower li)) , g (lower li) ⁆
                 ∷ # (toℕ (lower li)) ∷ p ∷ γ)))
              (sym peq)
          ∣₁
        ∣₁
      ∣₁ })
    (subst (λ z → ⟨ p ∈ z ⟩) hE p∈E)

  conj₂ : _
  conj₂ i i∈N = PT.rec
    (((i ∷ γ) ⊨ ∃̇∈ (var (suc e)) (∃̇∈ (var zero) (∃̇∈ (var zero)
       (prAt (suc (suc zero)) (suc (suc (suc zero))) zero)))) .snd)
    (λ { (m , p< , ie) →
      ∣ pr (# (toℕ (mkFin m k p<))) (g (mkFin m k p<))
      , subst (λ z → ⟨ pr (# (toℕ (mkFin m k p<))) (g (mkFin m k p<)) ∈ z ⟩)
          (sym hE) ∣ lift (mkFin m k p<) , refl ∣₁
      , ∣ ⁅ # (toℕ (mkFin m k p<)) , g (mkFin m k p<) ⁆
        , ∈pair-introR {u = ⁅ # (toℕ (mkFin m k p<)) ⁆s}
                       {v = ⁅ # (toℕ (mkFin m k p<)) , g (mkFin m k p<) ⁆}
                       {y = ⁅ # (toℕ (mkFin m k p<)) , g (mkFin m k p<) ⁆} refl
        , ∣ g (mkFin m k p<)
          , ∈pair-introR {u = # (toℕ (mkFin m k p<))} {v = g (mkFin m k p<)}
                         {y = g (mkFin m k p<)} refl
          , subst ⟨_⟩
              (sym (prAt-adequate (suc (suc zero)) (suc (suc (suc zero))) zero
                (g (mkFin m k p<) ∷ ⁅ # (toℕ (mkFin m k p<)) , g (mkFin m k p<) ⁆
                 ∷ pr (# (toℕ (mkFin m k p<))) (g (mkFin m k p<)) ∷ i ∷ γ)))
              (cong₂ pr (cong #_ (toℕ-mkFin m k p<) ∙ sym ie) refl)
          ∣₁
        ∣₁
      ∣₁ })
    (∈#-elim k i (subst (λ z → ⟨ i ∈ z ⟩) hN i∈N))
```

<!--en-->
## The guard pins the length
<!--zh-->
## 守卫钉死长度
<!--/-->

<!--en-->
And the direction that does the work. Suppose the guard holds with numeral
component `j` while the environment has length `k`. Compare the two numbers. If
`k` were smaller, the second clause applied to the numeral for `k` would produce
an entry of the environment whose key is `k` itself, and an entry's key is below
`k`. If `j` were smaller, the first clause applied to the entry at index `j`
would place the numeral for `j` inside itself. Both are refuted, so the numbers
are equal.
<!--zh-->
然后是真正出力的那个方向。设守卫在数码分量为 `j` 时成立，而环境长度为 `k`。比较这两个数。若 `k` 更小，则第二条子句施于 `k` 的数码会产出一个键恰为 `k` 的环境条目，而条目的键低于 `k`。若 `j` 更小，则第一条子句施于索引 `j` 处的条目会把 `j` 的数码放进它自身。两者都被驳倒，故两数相等。
<!--/-->

```agda
lenAt-len : ∀ {n} (e N : Fin n) (γ : (V ℓ) ^ n)
  {k : ℕ} (g : Fin k → V ℓ) (j : ℕ)
  → ⟦ var e ⟧ γ ≡ env g
  → ⟦ var N ⟧ γ ≡ # j
  → ⟨ γ ⊨ lenAt e N ⟩
  → j ≡ k
lenAt-len e N γ {k} g j hE hN (conj₁ , conj₂) = decide (j ≟ k)
  where
  ¬kj : k < j → Empty.⊥
  ¬kj k<j = PT.rec Empty.isProp⊥
    (λ { (p , p∈E , inner₁) → PT.rec Empty.isProp⊥
      (λ { (c , _ , inner₂) → PT.rec Empty.isProp⊥
        (λ { (v , _ , sat) → PT.rec Empty.isProp⊥
          (λ { (li , peq) →
            ¬m<m {m = k}
              (subst (_< k)
                (#-inj′ (pr-inj
                  (peq ∙ subst ⟨_⟩
                    (prAt-adequate (suc (suc zero)) (suc (suc (suc zero))) zero
                      (v ∷ c ∷ p ∷ # k ∷ γ)) sat) .fst))
                (toℕ<n (lower li))) })
          (subst (λ z → ⟨ p ∈ z ⟩) hE p∈E) })
        inner₂ })
      inner₁ })
    (conj₂ (# k) (subst (λ z → ⟨ # k ∈ z ⟩) (sym hN) (#mono k j k<j)))

  ¬jk : j < k → Empty.⊥
  ¬jk j<k = PT.rec Empty.isProp⊥
    (λ { (i , i∈N , inner₁) → PT.rec Empty.isProp⊥
      (λ { (c , _ , inner₂) → PT.rec Empty.isProp⊥
        (λ { (v , _ , sat) →
          ¬m<m {m = j}
            (#∈#-elim j j
              (subst (λ z → ⟨ z ∈ # j ⟩)
                (sym (pr-inj (subst ⟨_⟩
                  (prAt-adequate (suc (suc (suc zero))) (suc (suc zero)) zero
                    (v ∷ c ∷ i ∷ p₀ ∷ γ)) sat) .fst)
                 ∙ cong #_ (toℕ-mkFin j k j<k))
                (subst (λ z → ⟨ i ∈ z ⟩) hN i∈N))) })
        inner₂ })
      inner₁ })
    (conj₁ p₀ (subst (λ z → ⟨ p₀ ∈ z ⟩) (sym hE) ∣ lift (mkFin j k j<k) , refl ∣₁))
    where
    p₀ : V ℓ
    p₀ = pr (# (toℕ (mkFin j k j<k))) (g (mkFin j k j<k))

  decide : _ → j ≡ k
  decide (lt j<k) = Empty.rec (¬jk j<k)
  decide (eq q)   = q
  decide (gt k<j) = Empty.rec (¬kj k<j)
```

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
`lenAt`{.Agda} ties a certificate's arity component to the length of its
environment, `lenAt-intro`{.Agda} supplies it for a genuine environment, and
`lenAt-len`{.Agda} extracts the length from it. The second is what makes the
guard worth having: without it a certificate would admit environments of any
length, and every soundness argument downstream would have to carry the
disambiguation itself.
<!--zh-->
`lenAt`{.Agda} 把证书的元数分量与其环境的长度系在一起，`lenAt-intro`{.Agda} 为真环境供上它，而 `lenAt-len`{.Agda} 从中取出长度。第二条才是这道守卫值得拥有的原因：没有它，证书就会接纳任意长度的环境，而下游每一个可靠性论证都得自己扛起那份消歧工作。
<!--/-->
