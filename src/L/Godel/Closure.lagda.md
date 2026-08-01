# The closure, opened

<!--en-->
The option-B closure tower re-bases the internal tower on a kinded closure:
levels of an arity-indexed table, each level one round of operation images,
the cut at slice zero. This chapter lays the meta groundwork the closure will
spend. Four items arrive: the values generalization, saying the tuple family's
first entries range over the whole carrier at every positive arity; the two
selection equations, reading a selection over a satisfaction set as one more
conjunction with the atom that selects; the renaming law, saying a
satisfaction set survives a shift of all variables, and the forward pinning
inclusion, cutting the full extension down to the constant's singleton, the
two halves of the family-extension equation the kinded invariant's
constant-atom clause will consume; and the singleton family, the one operation
the delivered stock is missing, with its membership laws. The closure
recursion itself is the next chapter's work.
<!--zh-->
选项 B 的闭包塔把内部塔重新奠基在带种类的闭包上：元数索引的表之诸层，每层是一轮运算像，切口在零号切片。本章铺设闭包将要花掉的元层地基。四件物品到场：取值泛化，说元组族的首条目在每个正元数处跑遍整个载体；两条选择等式，把满足集上的一次选择读作与选中原子的一次合取；变量变换律，说满足集经全体变元移位而存活，与正向钉住包含，把整个扩张裁到常元的单点集，即带种类不变量之常元原子子句将要消费的族扩张等式的两半；以及单例族，即已交付存货缺掉的那一个运算，连同它的隶属定律。闭包递归本身是下一章的工作。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )

module L.Godel.Closure {ℓ : Level} where

open import FOL.Syntax
  using ( Formula; var; con
        ; _∈̇_; _≐_; _∧̇_ )
open import FOL.Manipulation.Renaming using ( renameFo )
import FOL.Manipulation.Renaming as Renaming
open import V.Hierarchy {ℓ} using ( extensionalV; 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( self∈sucV; numeralV≡# )
open import L.Coding.Environment {ℓ} using ( lookup-spec; cons )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Godel.Operations {ℓ}
  using ( _∩_; ∩-in; ∩-out
        ; selectMember; selectMember-in; selectMember-sub; selectMember-wit
        ; selectEqual; selectEqual-in; selectEqual-sub; selectEqual-wit
        ; extendGraph; extendGraph-zero; extendGraph-out
        ; extendFamily; extendFamily-in; extendFamily-out
        ; values; values-in; values-wit
        ; singleton-self; singleton-in; singleton-out )
open import L.Godel.Tuples {ℓ}
  using ( allTuples; allTuples-suc; tuple; tuple-entry; tuple-extend )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.Equiv using ( equivFun; invEq )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; #_ )


```

<!--en-->
## The values generalization

The probe proved the arity-two case; the tuple algebra generalizes it to every
positive arity. The proof reads the `values` of an extension off the family
extension: every member of `extendFamily X A` is the graph of a nonempty
assignment, whose first entry is a member of `A`, so the values of the whole
extension are exactly `A`, regardless of the family being extended. The zero
case is excluded: an empty assignment has no first entry, and the values of the
empty graph are empty, not the carrier. No transitivity is needed anywhere in
this proof, so the statement is at a bare carrier.
<!--zh-->
探针证了元数二的情形；元组代数把它推广到每个正元数。证明从族扩张上读出 `values`：`extendFamily X A` 的每个成员都是某个非空赋值的图，其首条目属于 `A`，故整个扩张的取值恰是 `A`，与被扩张的族无关。零情形被排除：空赋值没有首条目，而空图的取值是空集，不是载体。此证无处需要传递性，故陈述立于裸载体。
<!--/-->

```agda
module _ (A : V ℓ) where
  open DefOf A using ( SM; ι; _⊨ᵐ_; ⊨ᵐ-small )
  open hPropStructure 𝒮ᵥ

  module Ren = Renaming.Sat (hPropAlgebra (ℓ-suc ℓ))
                 (DefOf.𝒮M A) (DefOf.ι A)

  private
    κ : ⟪ A ⟫ → V ℓ
    κ = ⟪ A ⟫↪

    memb : (m : ⟪ A ⟫) → ⟨ κ m ∈ A ⟩
    memb m = ∈∈ₛ {a = κ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)

    fwdV : (n : ℕ) (v : V ℓ)
         → ⟨ v ∈ values (allTuples A (suc n)) ⟩ → ⟨ v ∈ A ⟩
    fwdV n v h = PT.rec (snd (v ∈ A)) go
      (values-wit {X = allTuples A (suc n)} {v = v} h)
      where
      go : Σ[ γ ∈ V ℓ ]
             (⟨ γ ∈ allTuples A (suc n) ⟩ × ⟨ pr (# 0) v ∈ γ ⟩)
         → ⟨ v ∈ A ⟩
      go (γ , hγ , hv) = PT.rec (snd (v ∈ A)) step
        (extendFamily-out {X = allTuples A n} {Y = A} {w = γ}
          (subst (λ z → ⟨ γ ∈ z ⟩) (allTuples-suc A n) hγ))
        where
        step : Σ[ γ' ∈ V ℓ ] Σ[ y ∈ V ℓ ]
                 (⟨ γ' ∈ allTuples A n ⟩ × ⟨ y ∈ A ⟩ × (γ ≡ extendGraph y γ'))
             → ⟨ v ∈ A ⟩
        step (γ' , y , hγ' , hy , eγ) = PT.rec (snd (v ∈ A)) step2
          (extendGraph-out {y = y} {γ = γ'} {z = pr (# 0) v}
            (subst (λ z → ⟨ pr (# 0) v ∈ z ⟩) eγ hv))
          where
          step2 : (pr (# 0) v ≡ pr ∅ y)
                ⊎ (Σ[ a ∈ V ℓ ] Σ[ w ∈ V ℓ ]
                     (⟨ pr a w ∈ γ' ⟩ × (pr (# 0) v ≡ pr (sucV a) w)))
                → ⟨ v ∈ A ⟩
          step2 (inl e) = subst (λ z → ⟨ z ∈ A ⟩)
            (sym (pr-inj {a = # 0} {b = v} {c = ∅} {d = y} e .snd)) hy
          step2 (inr (a , w , haw , e2)) =
            Empty.rec (∅-empty a
              (∈∈ₛ {a = a} {b = ∅} .fst
                (subst (λ z → ⟨ a ∈ z ⟩)
                  (sym (pr-inj {a = # 0} {b = v} {c = sucV a} {d = w} e2 .fst)
                    ∙ sym (numeralV≡# 0))
                  (self∈sucV a))))

    bwdV : (n : ℕ) (v : V ℓ)
         → ⟨ v ∈ A ⟩ → ⟨ v ∈ values (allTuples A (suc n)) ⟩
    bwdV n v hv = PT.rec (snd (v ∈ values (allTuples A (suc n)))) go
      ∣ ∈-asFiber {a = v} {b = A} hv ∣₁
      where
      go : Σ[ m ∈ ⟪ A ⟫ ] (κ m ≡ v)
         → ⟨ v ∈ values (allTuples A (suc n)) ⟩
      go (m , e) = subst (λ z → ⟨ z ∈ values (allTuples A (suc n)) ⟩) e
        (values-in {X = allTuples A (suc n)}
          {γ = tuple A (λ _ → m)} {v = κ m}
          ∣ (λ _ → m) , refl ∣₁
          ∣ lift zero , refl ∣₁)

  valuesAllTuples : (n : ℕ) → values (allTuples A (suc n)) ≡ A
  valuesAllTuples n =
    extensionalV λ v → ⇔toPath (fwdV n v) (bwdV n v)
```

<!--en-->
## The selection equations

The satisfaction chapter proved the atoms from the selection over all
assignments; these equations run the other way. A selection over a satisfaction
set selects exactly the assignments that satisfy the formula and the atom, so
it is the satisfaction set of the conjunction. Each proof is one
extensionality whose two inclusions swap the selection's witness against the
atom equation's, with the sub-reader keeping the formula's membership on the
way out and the in-reader rebuilding it on the way in. Two local helpers
tabulate an assignment into the inner world's vector form, exactly as the
satisfaction chapter does, since the equations must read the selection's
witness against the tuple's lookup specification.
<!--zh-->
满足关系章从「全体赋值上的选择」证出原子；这两条等式反向运行。满足集上的一次选择，选出的恰是同时满足公式与原子的那些赋值，故它就是合取的满足集。每个证明是一次外延性，其两个包含把选择的见证与原子等式的见证互换，出去时用子读式保住公式的隶属，进来时用入读式把它重建。两个局部辅助把赋值制表成内层世界的向量形式，与满足关系章所做的一致，因为等式必须把选择的见证对着元组的查值规格去读。
<!--/-->

```agda
  private
    tab : ∀ {ℓ'} {X : Type ℓ'} {n : ℕ} → (Fin n → X) → Vec X n
    tab {n = zero}  f = []
    tab {n = suc n} f = f zero ∷ tab (λ i → f (suc i))

    lookup-tab : ∀ {ℓ'} {X : Type ℓ'} {n : ℕ} (f : Fin n → X) (i : Fin n)
               → lookup i (tab f) ≡ f i
    lookup-tab f zero    = refl
    lookup-tab f (suc i) = lookup-tab (λ j → f (suc j)) i

    vec : {n : ℕ} → (Fin n → ⟪ A ⟫) → Vec SM n
    vec g = tab (λ i → ι (g i))

    lk : {n : ℕ} (g : Fin n → ⟪ A ⟫) (i : Fin n)
       → fst (lookup i (vec g)) ≡ κ (g i)
    lk g i = cong fst (lookup-tab (λ j → ι (g j)) i)

    vec-inj : {n : ℕ} {g h : Fin n → ⟪ A ⟫}
            → tuple A g ≡ tuple A h → vec g ≡ vec h
    vec-inj {n} {g} {h} e = cong tab (funExt λ i →
      Σ≡Prop (λ v → snd (v ∈ A)) (tuple-entry A e i))

  satSet : {n : ℕ} → Formula ⟪ A ⟫ n → V ℓ
  satSet {n} φ =
    sett (Σ[ g ∈ (Fin n → ⟪ A ⟫) ] ⟨ ⊨ᵐ-small φ (vec g) .fst ⟩)
         (λ p → tuple A (p .fst))

  sat-in : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (g : Fin n → ⟪ A ⟫)
         → ⟨ vec g ⊨ᵐ φ ⟩ → ⟨ tuple A g ∈ satSet φ ⟩
  sat-in φ g h =
    ∣ (g , equivFun (⊨ᵐ-small φ (vec g) .snd) h) , refl ∣₁

  sat-out : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (x : V ℓ) → ⟨ x ∈ satSet φ ⟩
          → ∥ Σ[ g ∈ (Fin n → ⟪ A ⟫) ]
              (⟨ vec g ⊨ᵐ φ ⟩ × (tuple A g ≡ x)) ∥₁
  sat-out φ x = PT.map
    λ { ((g , s) , e) → g , invEq (⊨ᵐ-small φ (vec g) .snd) s , e }

  sat-∧ : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
        → satSet (φ ∧̇ ψ) ≡ satSet φ ∩ satSet ψ
  sat-∧ {n} φ ψ = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    T : V ℓ
    T = satSet φ ∩ satSet ψ
    to : (w : V ℓ) → ⟨ w ∈ satSet (φ ∧̇ ψ) ⟩ → ⟨ w ∈ T ⟩
    to w h = PT.rec (snd (w ∈ T))
      (λ { (g , hc , e) →
        subst (λ z → ⟨ z ∈ T ⟩) e
          (∩-in {X = satSet φ} {Y = satSet ψ}
            (sat-in φ g (hc .fst)) (sat-in ψ g (hc .snd))) })
      (sat-out (φ ∧̇ ψ) w h)
    fro : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (φ ∧̇ ψ) ⟩
    fro w h = PT.rec (snd (w ∈ satSet (φ ∧̇ ψ)))
      (λ { (g , hφ , e) → PT.rec (snd (w ∈ satSet (φ ∧̇ ψ)))
        (λ { (g' , hψ , e') →
          subst (λ z → ⟨ z ∈ satSet (φ ∧̇ ψ) ⟩) e
            (sat-in (φ ∧̇ ψ) g
              ( hφ
              , subst (λ δ → ⟨ δ ⊨ᵐ ψ ⟩) (vec-inj (e' ∙ sym e)) hψ )) })
        (sat-out ψ w (∩-out {X = satSet φ} {Y = satSet ψ} h .snd)) })
      (sat-out φ w (∩-out {X = satSet φ} {Y = satSet ψ} h .fst))

  sat-∈vv : {n : ℕ} (i j : Fin n)
          → satSet (var i ∈̇ var j)
          ≡ selectMember (allTuples A n) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
  sat-∈vv {n} i j = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    Ki Kj T : V ℓ
    Ki = ⁅ # (toℕ i) ⁆s
    Kj = ⁅ # (toℕ j) ⁆s
    T = selectMember (allTuples A n) Ki Kj
    to : (w : V ℓ) → ⟨ w ∈ satSet (var i ∈̇ var j) ⟩ → ⟨ w ∈ T ⟩
    to w hw = PT.rec (snd (w ∈ T))
      (λ { (g , hs , e) →
        subst (λ z → ⟨ z ∈ T ⟩) e
          (selectMember-in {X = allTuples A n} {Ka = Ki} {Kb = Kj}
            {w = tuple A g}
            {a = # (toℕ i)} {b = # (toℕ j)} {u = κ (g i)} {v = κ (g j)}
            ∣ g , refl ∣₁
            (singleton-self (# (toℕ i))) (singleton-self (# (toℕ j)))
            ∣ lift i , refl ∣₁ ∣ lift j , refl ∣₁
            (subst2 (λ p q → ⟨ p ∈ q ⟩) (lk g i) (lk g j) hs)) })
      (sat-out (var i ∈̇ var j) w hw)
    fro : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (var i ∈̇ var j) ⟩
    fro w h = PT.rec (snd (w ∈ satSet (var i ∈̇ var j)))
      (λ { (g , eg) → PT.rec (snd (w ∈ satSet (var i ∈̇ var j)))
        (λ { (a , b , u , v , ha , hb , hau , hbv , huv) →
          let hau' : ⟨ pr (# (toℕ i)) u ∈ tuple A g ⟩
              hau' = subst (λ p → ⟨ pr p u ∈ tuple A g ⟩)
                       (singleton-out ha)
                       (subst (λ z → ⟨ pr a u ∈ z ⟩) (sym eg) hau)
              hbv' : ⟨ pr (# (toℕ j)) v ∈ tuple A g ⟩
              hbv' = subst (λ p → ⟨ pr p v ∈ tuple A g ⟩)
                       (singleton-out hb)
                       (subst (λ z → ⟨ pr b v ∈ z ⟩) (sym eg) hbv)
              eu : u ≡ κ (g i)
              eu = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) i u) hau'
              ev : v ≡ κ (g j)
              ev = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) j v) hbv'
          in subst (λ z → ⟨ z ∈ satSet (var i ∈̇ var j) ⟩) eg
               (sat-in (var i ∈̇ var j) g
                 (subst2 (λ p q → ⟨ p ∈ q ⟩)
                   (eu ∙ sym (lk g i)) (ev ∙ sym (lk g j)) huv)) })
        (selectMember-wit {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h) })
      (selectMember-sub {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h)

  sat-≐vv : {n : ℕ} (i j : Fin n)
          → satSet (var i ≐ var j)
          ≡ selectEqual (allTuples A n) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
  sat-≐vv {n} i j = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    Ki Kj T : V ℓ
    Ki = ⁅ # (toℕ i) ⁆s
    Kj = ⁅ # (toℕ j) ⁆s
    T = selectEqual (allTuples A n) Ki Kj
    to : (w : V ℓ) → ⟨ w ∈ satSet (var i ≐ var j) ⟩ → ⟨ w ∈ T ⟩
    to w hw = PT.rec (snd (w ∈ T))
      (λ { (g , hs , e) →
        subst (λ z → ⟨ z ∈ T ⟩) e
          (selectEqual-in {X = allTuples A n} {Ka = Ki} {Kb = Kj}
            {w = tuple A g}
            {a = # (toℕ i)} {b = # (toℕ j)} {u = κ (g i)}
            ∣ g , refl ∣₁
            (singleton-self (# (toℕ i))) (singleton-self (# (toℕ j)))
            ∣ lift i , refl ∣₁
            (subst (λ q → ⟨ pr (# (toℕ j)) q ∈ tuple A g ⟩)
              (sym (subst2 _≡_ (lk g i) (lk g j) hs))
              ∣ lift j , refl ∣₁)) })
      (sat-out (var i ≐ var j) w hw)
    fro : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (var i ≐ var j) ⟩
    fro w h = PT.rec (snd (w ∈ satSet (var i ≐ var j)))
      (λ { (g , eg) → PT.rec (snd (w ∈ satSet (var i ≐ var j)))
        (λ { (a , b , u , ha , hb , hau , hbu) →
          let hau' : ⟨ pr (# (toℕ i)) u ∈ tuple A g ⟩
              hau' = subst (λ p → ⟨ pr p u ∈ tuple A g ⟩)
                       (singleton-out ha)
                       (subst (λ z → ⟨ pr a u ∈ z ⟩) (sym eg) hau)
              hbu' : ⟨ pr (# (toℕ j)) u ∈ tuple A g ⟩
              hbu' = subst (λ p → ⟨ pr p u ∈ tuple A g ⟩)
                       (singleton-out hb)
                       (subst (λ z → ⟨ pr b u ∈ z ⟩) (sym eg) hbu)
              eu : u ≡ κ (g i)
              eu = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) i u) hau'
              ev : u ≡ κ (g j)
              ev = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) j u) hbu'
          in subst (λ z → ⟨ z ∈ satSet (var i ≐ var j) ⟩) eg
               (sat-in (var i ≐ var j) g
                 (subst2 _≡_ (sym (lk g i)) (sym (lk g j))
                   (sym eu ∙ ev))) })
        (selectEqual-wit {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h) })
      (selectEqual-sub {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h)
```

```agda
  sat-∈vv-sel : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (i j : Fin n)
              → selectMember (satSet φ)
                  ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
              ≡ satSet (φ ∧̇ (var i ∈̇ var j))
  sat-∈vv-sel {n} φ i j = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    Ki Kj : V ℓ
    Ki = ⁅ # (toℕ i) ⁆s
    Kj = ⁅ # (toℕ j) ⁆s
    L R : V ℓ
    L = selectMember (satSet φ) Ki Kj
    R = satSet (φ ∧̇ (var i ∈̇ var j))
    atom = satSet (var i ∈̇ var j)
    to : (w : V ℓ) → ⟨ w ∈ L ⟩ → ⟨ w ∈ R ⟩
    to w h = PT.rec (snd (w ∈ R)) build
      (sat-out φ w
        (selectMember-sub {X = satSet φ} {Ka = Ki} {Kb = Kj} {w = w} h))
      where
      hAtom : {g : Fin n → ⟪ A ⟫}
            → ⟨ tuple A g ∈ selectMember (satSet φ) Ki Kj ⟩
            → ⟨ vec g ⊨ᵐ (var i ∈̇ var j) ⟩
      hAtom {g} hs = PT.rec (snd (vec g ⊨ᵐ (var i ∈̇ var j))) go
        (selectMember-wit {X = satSet φ} {Ka = Ki} {Kb = Kj}
          {w = tuple A g} hs)
        where
        go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
               ( ⟨ a ∈ Ki ⟩ × ⟨ b ∈ Kj ⟩
               × ⟨ pr a u ∈ tuple A g ⟩ × ⟨ pr b v ∈ tuple A g ⟩ × ⟨ u ∈ v ⟩ )
           → ⟨ vec g ⊨ᵐ (var i ∈̇ var j) ⟩
        go (a , b , u , v , ha , hb , hau , hbv , huv) =
          subst2 (λ p q → ⟨ p ∈ q ⟩)
            (eu a u ha hau ∙ sym (lk g i))
            (ev b v hb hbv ∙ sym (lk g j))
            huv
          where
          eu : (a u : V ℓ) → ⟨ a ∈ Ki ⟩ → ⟨ pr a u ∈ tuple A g ⟩
             → u ≡ κ (g i)
          eu a u ha hau = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) i u)
            (subst (λ p → ⟨ pr p u ∈ tuple A g ⟩)
              (singleton-out ha) hau)
          ev : (b v : V ℓ) → ⟨ b ∈ Kj ⟩ → ⟨ pr b v ∈ tuple A g ⟩
             → v ≡ κ (g j)
          ev b v hb hbv = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) j v)
            (subst (λ p → ⟨ pr p v ∈ tuple A g ⟩)
              (singleton-out hb) hbv)
      build : Σ[ g ∈ (Fin n → ⟪ A ⟫) ]
                (⟨ vec g ⊨ᵐ φ ⟩ × (tuple A g ≡ w))
            → ⟨ w ∈ R ⟩
      build (g , hφ , e) =
        let hwφ : ⟨ tuple A g ∈ satSet φ ⟩
            hwφ = sat-in φ g hφ
            hsel : ⟨ tuple A g ∈ selectMember (satSet φ) Ki Kj ⟩
            hsel = subst (λ z → ⟨ z ∈ selectMember (satSet φ) Ki Kj ⟩) (sym e) h
            hwa : ⟨ tuple A g ∈ atom ⟩
            hwa = sat-in (var i ∈̇ var j) g (hAtom hsel)
        in subst (λ z → ⟨ z ∈ R ⟩) e
             (subst (λ z → ⟨ tuple A g ∈ z ⟩)
               (sym (sat-∧ φ (var i ∈̇ var j)))
               (∩-in {X = satSet φ} {Y = atom} hwφ hwa))
    fro : (w : V ℓ) → ⟨ w ∈ R ⟩ → ⟨ w ∈ L ⟩
    fro w h = PT.rec (snd (w ∈ L)) build
      (sat-out (φ ∧̇ (var i ∈̇ var j)) w h)
      where
      build : Σ[ g ∈ (Fin n → ⟪ A ⟫) ]
                (⟨ vec g ⊨ᵐ (φ ∧̇ (var i ∈̇ var j)) ⟩ × (tuple A g ≡ w))
            → ⟨ w ∈ L ⟩
      build (g , hc , e) =
        let hwφ : ⟨ tuple A g ∈ satSet φ ⟩
            hwφ = sat-in φ g (hc .fst)
            hwa : ⟨ tuple A g ∈ atom ⟩
            hwa = sat-in (var i ∈̇ var j) g (hc .snd)
            w∈ : ⟨ tuple A g ∈ L ⟩
            w∈ = selectMember-in {X = satSet φ} {Ka = Ki} {Kb = Kj}
                   {w = tuple A g}
                   {a = # (toℕ i)} {b = # (toℕ j)} {u = κ (g i)} {v = κ (g j)}
                   hwφ (singleton-self (# (toℕ i))) (singleton-self (# (toℕ j)))
                   ∣ lift i , refl ∣₁ ∣ lift j , refl ∣₁
                   (subst2 (λ p q → ⟨ p ∈ q ⟩) (lk g i) (lk g j)
                     (hc .snd))
        in subst (λ z → ⟨ z ∈ L ⟩) e w∈

  sat-≐vv-sel : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (i j : Fin n)
              → selectEqual (satSet φ)
                  ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
              ≡ satSet (φ ∧̇ (var i ≐ var j))
  sat-≐vv-sel {n} φ i j = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    Ki Kj : V ℓ
    Ki = ⁅ # (toℕ i) ⁆s
    Kj = ⁅ # (toℕ j) ⁆s
    L R : V ℓ
    L = selectEqual (satSet φ) Ki Kj
    R = satSet (φ ∧̇ (var i ≐ var j))
    atom = satSet (var i ≐ var j)
    to : (w : V ℓ) → ⟨ w ∈ L ⟩ → ⟨ w ∈ R ⟩
    to w h = PT.rec (snd (w ∈ R)) build
      (sat-out φ w
        (selectEqual-sub {X = satSet φ} {Ka = Ki} {Kb = Kj} {w = w} h))
      where
      hAtom : {g : Fin n → ⟪ A ⟫}
            → ⟨ tuple A g ∈ selectEqual (satSet φ) Ki Kj ⟩
            → ⟨ vec g ⊨ᵐ (var i ≐ var j) ⟩
      hAtom {g} hs = PT.rec (snd (vec g ⊨ᵐ (var i ≐ var j))) go
        (selectEqual-wit {X = satSet φ} {Ka = Ki} {Kb = Kj}
          {w = tuple A g} hs)
        where
        go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ]
               ( ⟨ a ∈ Ki ⟩ × ⟨ b ∈ Kj ⟩
               × ⟨ pr a u ∈ tuple A g ⟩ × ⟨ pr b u ∈ tuple A g ⟩ )
           → ⟨ vec g ⊨ᵐ (var i ≐ var j) ⟩
        go (a , b , u , ha , hb , hau , hbu) =
          subst2 _≡_ (sym (lk g i)) (sym (lk g j))
            (sym (eu a u ha hau) ∙ ev b u hb hbu)
          where
          eu : (a u : V ℓ) → ⟨ a ∈ Ki ⟩ → ⟨ pr a u ∈ tuple A g ⟩
             → u ≡ κ (g i)
          eu a u ha hau = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) i u)
            (subst (λ p → ⟨ pr p u ∈ tuple A g ⟩)
              (singleton-out ha) hau)
          ev : (b u : V ℓ) → ⟨ b ∈ Kj ⟩ → ⟨ pr b u ∈ tuple A g ⟩
             → u ≡ κ (g j)
          ev b u hb hbu = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) j u)
            (subst (λ p → ⟨ pr p u ∈ tuple A g ⟩)
              (singleton-out hb) hbu)
      build : Σ[ g ∈ (Fin n → ⟪ A ⟫) ]
                (⟨ vec g ⊨ᵐ φ ⟩ × (tuple A g ≡ w))
            → ⟨ w ∈ R ⟩
      build (g , hφ , e) =
        let hwφ : ⟨ tuple A g ∈ satSet φ ⟩
            hwφ = sat-in φ g hφ
            hsel : ⟨ tuple A g ∈ selectEqual (satSet φ) Ki Kj ⟩
            hsel = subst (λ z → ⟨ z ∈ selectEqual (satSet φ) Ki Kj ⟩) (sym e) h
            hwa : ⟨ tuple A g ∈ atom ⟩
            hwa = sat-in (var i ≐ var j) g (hAtom hsel)
        in subst (λ z → ⟨ z ∈ R ⟩) e
             (subst (λ z → ⟨ tuple A g ∈ z ⟩)
               (sym (sat-∧ φ (var i ≐ var j)))
               (∩-in {X = satSet φ} {Y = atom} hwφ hwa))
    fro : (w : V ℓ) → ⟨ w ∈ R ⟩ → ⟨ w ∈ L ⟩
    fro w h = PT.rec (snd (w ∈ L)) build
      (sat-out (φ ∧̇ (var i ≐ var j)) w h)
      where
      build : Σ[ g ∈ (Fin n → ⟪ A ⟫) ]
                (⟨ vec g ⊨ᵐ (φ ∧̇ (var i ≐ var j)) ⟩ × (tuple A g ≡ w))
            → ⟨ w ∈ L ⟩
      build (g , hc , e) =
        let hwφ : ⟨ tuple A g ∈ satSet φ ⟩
            hwφ = sat-in φ g (hc .fst)
            hwa : ⟨ tuple A g ∈ atom ⟩
            hwa = sat-in (var i ≐ var j) g (hc .snd)
            w∈ : ⟨ tuple A g ∈ L ⟩
            w∈ = selectEqual-in {X = satSet φ} {Ka = Ki} {Kb = Kj}
                   {w = tuple A g}
                   {a = # (toℕ i)} {b = # (toℕ j)} {u = κ (g i)}
                   hwφ (singleton-self (# (toℕ i))) (singleton-self (# (toℕ j)))
                   ∣ lift i , refl ∣₁
                   (subst (λ q → ⟨ pr (# (toℕ j)) q ∈ tuple A g ⟩)
                     (sym (subst2 _≡_ (lk g i) (lk g j) (hc .snd)))
                     ∣ lift j , refl ∣₁)
        in subst (λ z → ⟨ z ∈ L ⟩) e w∈
```

<!--en-->
## The family-extension equation

The constant-atom composite's engine, in the shape the kinded invariant's
extendFamily clause will consume. Reading `Terms.sound`'s `selEqConK` case
backward: the term is a shift of a selection over the family of assignments
extended by the constant, so the extension itself must be a satisfaction set.
The statement pins the shape: extending a satisfaction set by a constant is
the satisfaction set of the constant-pinned, shifted formula, the formula
whose fresh first variable records the constant and whose remaining variables
are the original ones shifted up by one. Two lemmas compose it: the renaming
law, saying a satisfaction set survives a shift of all variables, and the
pinning law, saying the equality atom at the fresh variable cuts the full
extension down to the constant's singleton.
<!--zh-->
常元原子复合体的引擎，形状即带种类不变量的族扩张子句将要消费的样子。把 `Terms.sound` 的 `selEqConK` 情形反向读：该项是「被常元扩张的诸赋值之族」上一次选择之后的移位，故扩张本身必须是满足集。陈述把形状钉死：满足集被常元扩张，就是「钉住常元并移位后的公式」的满足集，即新首变元记录常元、其余变元整体上移一位的那条公式。两条引理把它复合出来：变量变换律，说满足集经全体变元移位而存活；钉住律，说新变元处的等词原子把整个扩张裁到常元的单点集。
<!--/-->

```agda
  satSet-rename-shift : {n : ℕ} (φ : Formula ⟪ A ⟫ n)
                      → satSet (renameFo suc φ) ≡ extendFamily (satSet φ) A
  satSet-rename-shift {n} φ = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    T : V ℓ
    T = extendFamily (satSet φ) A
    agrees-suc : (g : Fin (suc n) → ⟪ A ⟫)
               → Ren.Agrees suc (vec g) (vec (λ i → g (suc i)))
    agrees-suc g i = Σ≡Prop (λ x → snd (x ∈ˢ A))
      (cong fst (lookup-tab (λ j → ι (g j)) (suc i))
       ∙ sym (cong fst (lookup-tab (λ j → ι (g (suc j))) i)))
    to : (w : V ℓ) → ⟨ w ∈ satSet (renameFo suc φ) ⟩ → ⟨ w ∈ T ⟩
    to w h = PT.rec (snd (w ∈ T)) build
      (sat-out (renameFo suc φ) w h)
      where
      renBack : (g : Fin (suc n) → ⟪ A ⟫)
              → ⟨ vec g ⊨ᵐ renameFo suc φ ⟩
              → ⟨ vec (λ i → g (suc i)) ⊨ᵐ φ ⟩
      renBack g hg = subst ⟨_⟩ (Ren.⊨-rename suc φ (vec g) (vec (λ i → g (suc i)))
        (agrees-suc g)) hg
      build : Σ[ g ∈ (Fin (suc n) → ⟪ A ⟫) ]
                (⟨ vec g ⊨ᵐ renameFo suc φ ⟩ × (tuple A g ≡ w))
            → ⟨ w ∈ T ⟩
      build (g , hg , e) =
        subst (λ z → ⟨ z ∈ T ⟩)
          (sym (tuple-extend A g) ∙ e)
          (extendFamily-in {X = satSet φ} {Y = A}
            (sat-in φ (λ i → g (suc i)) (renBack g hg))
            (memb (g zero)))
    fro : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (renameFo suc φ) ⟩
    fro w h = PT.rec (snd (w ∈ satSet (renameFo suc φ))) build
      (extendFamily-out {X = satSet φ} {Y = A} {w = w} h)
      where
      renFwd : (g : Fin (suc n) → ⟪ A ⟫)
             → ⟨ vec (λ i → g (suc i)) ⊨ᵐ φ ⟩
             → ⟨ vec g ⊨ᵐ renameFo suc φ ⟩
      renFwd g hg = subst ⟨_⟩ (sym (Ren.⊨-rename suc φ (vec g)
        (vec (λ i → g (suc i))) (agrees-suc g))) hg
      build : Σ[ γ ∈ V ℓ ] Σ[ y ∈ V ℓ ]
                (⟨ γ ∈ satSet φ ⟩ × ⟨ y ∈ A ⟩ × (w ≡ extendGraph y γ))
            → ⟨ w ∈ satSet (renameFo suc φ) ⟩
      build (γ , y , hγ , hy , e) = PT.rec (snd (w ∈ satSet (renameFo suc φ)))
        (λ { (g , hg , eg) →
          let m : ⟪ A ⟫
              m = ∈-asFiber {a = y} {b = A} hy .fst
              g' : Fin (suc n) → ⟪ A ⟫
              g' = cons m g
              y≡ : κ m ≡ y
              y≡ = ∈-asFiber {a = y} {b = A} hy .snd
              w≡ : w ≡ tuple A g'
              w≡ = e
                  ∙ sym (cong₂ extendGraph y≡ eg)
                  ∙ sym (tuple-extend A g')
          in subst (λ z → ⟨ z ∈ satSet (renameFo suc φ) ⟩) (sym w≡)
               (sat-in (renameFo suc φ) g'
                 (renFwd g' hg)) })
        (sat-out φ γ hγ)
```

<!--en-->
## The singleton family

The one operation the delivered stock is missing, and the price item the cut
probe found. The constant-atom composite needs the family of singletons of the
carrier's members as the value family the extension consumes, so the closure's
level table must contain it. The definition follows the operations idiom: one
direct `sett`, no union, one index telescope, and no `⋃`-tower in the index,
so no seal is needed at the birth site. Its two membership laws read the
fiber, and the description reuses the singleton reader from the bridge
chapter, whose two directions the defining formula at a stage makes
definitional.
<!--zh-->
已交付存货缺掉的那一个运算，也是切探针找到的价目项。常元原子复合体需要「载体成员的诸单点集」之族作为扩张所消费的取值族，故闭包的表层必须装下它。定义遵循运算章的行事：一个直接的 `sett`，没有并，一个索引望远镜，索引里没有 `⋃` 塔，故诞生处无需封印。它的两条隶属定律读出纤维，而描述复用桥梁章的单点读式，其两个方向被阶段处的定义公式变得定义性。
<!--/-->

```agda
  singletons : V ℓ → V ℓ
  singletons X = sett ⟪ X ⟫ (λ m → ⁅ ⟪ X ⟫↪ m ⁆s)

  singletons-in : {X x : V ℓ} → ⟨ x ∈ X ⟩ → ⟨ ⁅ x ⁆s ∈ singletons X ⟩
  singletons-in {X} {x} hx = ∣ f .fst , cong ⁅_⁆s (f .snd) ∣₁
    where f = ∈-asFiber {a = x} {b = X} hx

  singletons-out : {X w : V ℓ} → ⟨ w ∈ singletons X ⟩
                 → ∥ Σ[ x ∈ V ℓ ] (⟨ x ∈ X ⟩ × (w ≡ ⁅ x ⁆s)) ∥₁
  singletons-out {X} = PT.map λ { (m , e) →
    ⟪ X ⟫↪ m
    , ∈∈ₛ {a = ⟪ X ⟫↪ m} {b = X} .snd (∈ₛ⟪ X ⟫↪ m)
    , sym e }
```


<!--en-->
## The pinning law

The extension cut down to the constant's singleton. A member of the full
extension is the graph of an assignment extended by some carrier member; the
equality atom at the fresh key asks that extended member to be exactly the
constant, and the two together cut the family down to the singleton. The proof
uses the selection reading of the equality atom and the two-entry reading of
the extension, and the head of a graph held by the equality-satisfying tuple is
read against the lookup specification, exactly as the satisfaction chapter
does.
<!--zh-->
## 钉住律

被裁到常元单点集的扩张。全扩张的成员是「被某载体成员扩张的赋值」的图；新键处的等词原子要求被扩张成员恰是常元，两者一起把族裁到单点集。证明使用等词原子的选择读式与扩张的两条目读式，而满足等式之元组的图首，对着查值规格去读，恰如满足关系章所做。
<!--/-->

```agda
  -- The forward inclusion: a member of the full extension whose head is the
  -- constant already lies in the singleton extension.
  extendFamily-pin : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (a : ⟪ A ⟫)
                   → (w : V ℓ)
                   → ⟨ w ∈ satSet (var zero ≐ con a) ∩ extendFamily (satSet φ) A ⟩
                   → ⟨ w ∈ extendFamily (satSet φ) ⁅ κ a ⁆s ⟩
  extendFamily-pin {n} φ a = λ w h →
    PT.rec (snd (w ∈ extendFamily (satSet φ) ⁅ κ a ⁆s)) (build w h)
      (sat-out (var zero ≐ con a) w (∩-out {X = satSet (var zero ≐ con a)}
        {Y = extendFamily (satSet φ) A} h .fst))
    where
    headEq : (g : Fin (suc n) → ⟪ A ⟫)
           → ⟨ vec g ⊨ᵐ (var zero ≐ con a) ⟩ → κ (g zero) ≡ κ a
    headEq g hg = sym (lk g zero) ∙ hg
    headOfGraph : (w : V ℓ) (g : Fin (suc n) → ⟪ A ⟫) (γ y : V ℓ) → w ≡ tuple A g
                → w ≡ extendGraph y γ → ⟨ pr (# 0) y ∈ w ⟩ → y ≡ κ (g zero)
    headOfGraph w g γ y e eg hyw = PT.rec (setIsSet y (κ (g zero))) step
      (extendGraph-out {y = y} {γ = γ} {z = pr (# 0) y}
        (subst (λ z → ⟨ pr (# 0) y ∈ z ⟩) eg hyw))
      where
      step : (pr (# 0) y ≡ pr ∅ y)
           ⊎ (Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ pr a v ∈ γ ⟩ × (pr (# 0) y ≡ pr (sucV a) v)))
           → y ≡ κ (g zero)
      step (inl _) = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) zero y)
        (subst (λ z → ⟨ pr (# 0) y ∈ z ⟩) e hyw)
      step (inr (a , v , hav , eq)) = Empty.rec
        (∅-empty a
          (∈∈ₛ {a = a} {b = ∅} .fst
            (subst (λ z → ⟨ a ∈ z ⟩)
              (sym (pr-inj {a = # 0} {b = y} {c = sucV a} {d = v} eq .fst)
                ∙ sym (numeralV≡# 0))
              (self∈sucV a))))
    build : (w : V ℓ)
          → ⟨ w ∈ satSet (var zero ≐ con a) ∩ extendFamily (satSet φ) A ⟩
          → Σ[ g ∈ (Fin (suc n) → ⟪ A ⟫) ]
              (⟨ vec g ⊨ᵐ (var zero ≐ con a) ⟩ × (tuple A g ≡ w))
          → ⟨ w ∈ extendFamily (satSet φ) ⁅ κ a ⁆s ⟩
    build w h (g , hg , e) = PT.rec (snd (w ∈ extendFamily (satSet φ) ⁅ κ a ⁆s))
      (λ { (γ , y , hγ , hy , eγ) →
        let a≡ : y ≡ κ a
            a≡ = headOfGraph w g γ y (sym e) eγ
                   (subst (λ z → ⟨ pr (# 0) y ∈ z ⟩) (sym eγ)
                     (extendGraph-zero {y = y} {γ = γ})) ∙ headEq g hg
        in subst (λ z → ⟨ z ∈ extendFamily (satSet φ) ⁅ κ a ⁆s ⟩) (sym eγ)
             (extendFamily-in {X = satSet φ} {Y = ⁅ κ a ⁆s}
               hγ (singleton-in a≡)) })
      (extendFamily-out {X = satSet φ} {Y = A} {w = w}
        (∩-out {X = satSet (var zero ≐ con a)}
          {Y = extendFamily (satSet φ) A} h .snd))

```


<!--en-->
## Recap

The values generalization `valuesAllTuples`{.Agda}, at every positive arity;
the two selection equations `sat-∈vv-sel`{.Agda} and `sat-≐vv-sel`{.Agda},
reading a selection over a satisfaction set as one more conjunction; the
renaming law `satSet-rename-shift`{.Agda}, saying a satisfaction set survives
a shift of all variables; the forward pinning inclusion `extendFamily-pin`{.Agda},
saying the equality atom at the fresh key cuts the full extension down to the
constant's singleton; and the singleton family `singletons`{.Agda} with its two
membership laws, the one operation the delivered stock was missing. The
reverse pinning inclusion, the full family-extension equation, and the
singleton family's description and constructibility are the closure chapter's
own consumption, recorded for the next batch.
<!--zh-->
## 小结

取值泛化 `valuesAllTuples`{.Agda}，在每个正元数处；两条选择等式 `sat-∈vv-sel`{.Agda} 与 `sat-≐vv-sel`{.Agda}，把满足集上的一次选择读作一次合取；变量变换律 `satSet-rename-shift`{.Agda}，说满足集经全体变元移位而存活；正向钉住包含 `extendFamily-pin`{.Agda}，说新键处的等词原子把整个扩张裁到常元的单点集；以及单例族 `singletons`{.Agda} 连同它的两条隶属定律，即已交付存货缺掉的那一个运算。反向钉住包含、完整的族扩张等式，与单例族的描述和可构造性，是闭包章自己要消费的东西，留给下一批。
<!--/-->
