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
the delivered stock is missing, with its membership laws, its description, and
its constructibility. The reverse pinning inclusion completes the pair, and
the full family-extension equation assembled from the renaming law and the
two inclusions now stands whole, the shape the kinded invariant's constant-atom
clause will consume. Four further items arrive: the kinded level family, an
arity-indexed, level-cumulative family of shelves where every operation shops
only on its own shelf and whose seed is the singleton family; the kinded
invariant, every member of a positive-arity slice a satisfaction set, by plain
induction on the level, replacing the certificate's honesty induction;
terms-to-levels, every term denotation landing in the levels by one term
induction with a computable level witness; and the cut theorem, the values-cut
of the levels equal to the definable powerset. The closure recursion itself is
the next chapter's work.
<!--zh-->
选项 B 的闭包塔把内部塔重新奠基在带种类的闭包上：元数索引的表之诸层，每层是一轮运算像，切口在零号切片。本章铺设闭包将要花掉的元层地基。四件物品到场：取值泛化，说元组族的首条目在每个正元数处跑遍整个载体；两条选择等式，把满足集上的一次选择读作与选中原子的一次合取；变量变换律，说满足集经全体变元移位而存活，与正向钉住包含，把整个扩张裁到常元的单点集，即带种类不变量之常元原子子句将要消费的族扩张等式的两半；以及单例族，即已交付存货缺掉的那一个运算，连同它的隶属定律、描述与可构造性。反向钉住包含补全包含对，而由变量变换律与两条包含装配出的完整族扩张等式现已整体立住，即带种类不变量之常元原子子句将要消费的形状。再四件物品到场：带种类的诸层族，一个元数索引、随层累积的架位族，每个运算只在自己的架位上作业，种子即单例族；带种类的不变量，正元数片的每个成员都是满足集，凭对层级的朴素归纳，取代证书的诚实性归纳；项到诸层，每个项的指称凭一次项归纳、带可计算的层级见证落进诸层；以及切定理，诸层的取值切口等于可定义幂集。闭包递归本身是下一章的工作。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth using ( hPropAlgebra )
open import FOL.ZFStructure using ( module hPropStructure )

module L.Godel.Closure {ℓ : Level} where

open import Base.Classical using ( LEM )

open import FOL.Syntax
  using ( Formula; var; con
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; ¬̇_; ∃̇_; ⊤̇; ∀̇∈; ∃̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo )
import FOL.Manipulation.Renaming as Renaming
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( extensionalV; 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( self∈sucV; numeralV≡# )
open import L.Coding.Environment {ℓ} using ( lookup-spec; cons )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( isL; isL-trans; Lset; Lset-mono; Lset-layer; layer-trans
        ; Lset-in; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Ordinal {ℓ} using ( suc-ord )
open import L.Axioms.Basic {ℓ} using ( defSet→isL; isL-directed )
open import L.Coding.Model {ℓ} using ( extAt )
open import L.Coding.InL {ℓ} using ( sglL )
open import L.Godel.Operations {ℓ}
  using ( _∩_; ∩-in; ∩-out; _∪_; ∪-left; ∪-right; ∪-out
        ; _∖_; ∖-in; ∖-out
        ; selectMember; selectMember-in; selectMember-sub; selectMember-wit
        ; selectEqual; selectEqual-in; selectEqual-sub; selectEqual-wit
        ; extendGraph; extendGraph-zero; extendGraph-out
        ; extendFamily; extendFamily-in; extendFamily-out
        ; values; values-in; values-wit
        ; tailGraph; shiftDown; shiftDown-in; shiftDown-out
        ; singleton-self; singleton-in; singleton-out )
open import L.Godel.Tuples {ℓ}
  using ( allTuples; allTuples-suc; tuple; tuple-entry; tuple-extend
        ; tupleTail )
open import L.Godel.Definable {ℓ} using ( module Describes )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK; shiftK
        ; ⟦_⟧ᴷ )
import L.Godel.Terms as Terms

open import Cubical.Data.FinData using ( Fin; toℕ )
open import Cubical.Data.Nat using ( _+_; +-zero; +-suc )
open import Cubical.Data.Unit using ( Unit*; tt* )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Foundations.Equiv using ( equivFun; invEq )
open import Cubical.Data.Sigma using ( Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base
  using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
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
  open DefOf A using ( SM; ι; _⊨ᵐ_; ⊨ᵐ-small; defSet; defSet-mem )
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
are the original ones shifted up by one. The equation now stands whole,
assembled from the renaming law and the pinning inclusion pair: the forward
direction, saying the equality atom at the fresh variable cuts the full
extension down to the constant's singleton, and its reverse, saying every
member of the singleton extension records the constant at the fresh key. The
kinded invariant's constant-atom clause will consume the equation to trade
the extended family for the pinned, shifted formula's satisfaction set, and
then read the selection off the conjunction with the selection equations of
this chapter.
<!--zh-->
常元原子复合体的引擎，形状即带种类不变量的族扩张子句将要消费的样子。把 `Terms.sound` 的 `selEqConK` 情形反向读：该项是「被常元扩张的诸赋值之族」上一次选择之后的移位，故扩张本身必须是满足集。陈述把形状钉死：满足集被常元扩张，就是「钉住常元并移位后的公式」的满足集，即新首变元记录常元、其余变元整体上移一位的那条公式。等式现已整体立住，由变量变换律与钉住包含对装配而成：正向说新变元处的等词原子把整个扩张裁到常元的单点集，反向说单点扩张的每个成员都在新键处记录常元。带种类不变量之常元原子子句将消费这条等式，把被扩张的族换成「钉住常元并移位后的公式」的满足集，再沿本章的选择等式把选择读下去。
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
fiber. Its internal face has two more pieces, both what the closure recursion
will consume in the next batch. The description `singletonsAt` sits in the
`Describes` frame: the body exists a member of the carrier slot whose
singleton the bound member is, and both readers run at variable slots and
environments. The singleton atom class `sglAt′` is private in the bridge
chapter, so it is restated locally, exactly as this chapter restated its
satisfaction machinery. The constructibility `singletonsL` follows the bridge
chapter's pattern: one stage from directedness, the defining formula over the
next stage, and `defSet→isL`, with the singleton climb restated locally after
its precedent there.
<!--zh-->
已交付存货缺掉的那一个运算，也是切探针找到的价目项。常元原子复合体需要「载体成员的诸单点集」之族作为扩张所消费的取值族，故闭包的表层必须装下它。定义遵循运算章的行事：一个直接的 `sett`，没有并，一个索引望远镜，索引里没有 `⋃` 塔，故诞生处无需封印。它的两条隶属定律读出纤维。它的内面还有两件，皆为闭包递归下一批将要消费之物。描述 `singletonsAt` 坐进 `Describes` 框架：体存在一个载体槽位的成员，使被描述的成员成为它的单点集，两条读式都立于可变槽位与环境。单点原子类 `sglAt′` 在桥梁章是私有的，故像本章重述满足机制那样在本地重述。可构造性 `singletonsL` 走桥梁章的行事：从有向性取一个阶段，在下一阶段写下定义公式，再经 `defSet→isL` 关门，单点爬升按那里的先例本地重述。
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

  -- The singleton atom class is restated locally: `sglAt′` is private in the
  -- bridge chapter, and the description needs it as a reader over this
  -- chapter's carrier, exactly as the satisfaction machinery was restated.
  private
    sglAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Formula K n
    sglAt′ k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))

    module SglDesc where
      module Abs = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
      SL : Type (ℓ-suc ℓ)
      SL = Σ[ x ∈ V ℓ ] ⟨ isL x ⟩
      open Abs using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

      singletonsAt : {n : ℕ} → Fin n → Fin n → Formula SL n
      singletonsAt {n} k i =
        extAt k (∃̇∈ (var (suc i)) (sglAt′ {n = suc (suc n)} (suc zero) zero))

      module _ {n : ℕ} (k i : Fin n) (γ : SL ^ n) where
        private
          X : V ℓ
          X = fst (lookup i γ)

          Φ : Formula SL (suc n)
          Φ = ∃̇∈ (var (suc i)) (sglAt′ {n = suc (suc n)} (suc zero) zero)

          memL : (y : V ℓ) → ⟨ y ∈ singletons X ⟩ → ⟨ isL y ⟩
          memL y hy = PT.rec (snd (isL y))
            (λ { (x , hx , e) → subst (λ w → ⟨ isL w ⟩) (sym e)
              (sglL (isL-trans {x = X} {y = x} hx (lookup i γ .snd))) })
            (singletons-out {X = X} {w = y} hy)

          read : (z : SL) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ singletons X ⟩
          read z hz = PT.rec (snd (fst z ∈ singletons X)) build hz
            where
            build : Σ[ x ∈ SL ] (⟨ fst x ∈ˢ fst (lookup i γ) ⟩
                     × ⟨ (x ∷ z ∷ γ) ⊨ sglAt′ {n = suc (suc n)} (suc zero) zero ⟩)
                  → ⟨ fst z ∈ singletons X ⟩
            build (x , hx , s) =
              let z≡ : fst z ≡ ⁅ fst x ⁆s
                  z≡ = extensionality (fst z) ⁅ fst x ⁆s (sub₁ , sub₂)
              in subst (λ w → ⟨ w ∈ singletons X ⟩) (sym z≡)
                   (singletons-in {X = X} {x = fst x} hx)
              where
              sub₁ : ⟨ fst z ⊆ ⁅ fst x ⁆s ⟩
              sub₁ v v∈ₛ = ∈∈ₛ {a = v} {b = ⁅ fst x ⁆s} .fst
                (singleton-in (s₂ v v∈z))
                where
                v∈z : ⟨ v ∈ fst z ⟩
                v∈z = ∈∈ₛ {a = v} {b = fst z} .snd v∈ₛ
                s₂ : (v : V ℓ) → ⟨ v ∈ fst z ⟩ → v ≡ fst x
                s₂ v v∈z =
                  s .snd (v , isL-trans {x = fst z} {y = v} v∈z (z .snd))
                       v∈z
              sub₂ : ⟨ ⁅ fst x ⁆s ⊆ fst z ⟩
              sub₂ v v∈ₛ = ∈∈ₛ {a = v} {b = fst z} .fst
                (subst (λ w → ⟨ w ∈ fst z ⟩)
                  (sym (singleton-out (∈∈ₛ {a = v} {b = ⁅ fst x ⁆s} .snd v∈ₛ)))
                  (s .fst))

          fill : (z : SL) → ⟨ fst z ∈ singletons X ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
          fill z hz = PT.rec (snd ((z ∷ γ) ⊨ Φ)) build
            (singletons-out {X = X} {w = fst z} hz)
            where
            build : Σ[ v ∈ V ℓ ] (⟨ v ∈ X ⟩ × (fst z ≡ ⁅ v ⁆s))
                  → ⟨ (z ∷ γ) ⊨ Φ ⟩
            build (v , hv , e) =
              ∣ ( v , isL-trans {x = X} {y = v} hv (lookup i γ .snd) )
              , hv
              , ( subst (λ w → ⟨ v ∈ w ⟩) (sym e) (singleton-self v)
                , λ y y∈z →
                    singleton-out
                      (subst (λ w → ⟨ fst y ∈ w ⟩) e
                        y∈z) )
              ∣₁

          module D = Describes k Φ γ (singletons X) memL read fill

        singletonsAt-out : ⟨ γ ⊨ singletonsAt k i ⟩
                         → fst (lookup k γ) ≡ singletons X
        singletonsAt-out = D.describes-out

        singletonsAt-in : fst (lookup k γ) ≡ singletons X
                        → ⟨ γ ⊨ singletonsAt k i ⟩
        singletonsAt-in = D.describes-in

    -- The singleton climb restated locally, `sglUp`-class: a member of a
    -- stage has its singleton in the next stage, proved through the defining
    -- formula `var zero ≐ con mx` and the definable-subset door.
    sglUp-mini : (σ : V ℓ) {x : V ℓ} → ⟨ x ∈ Lset σ ⟩ → ⟨ ⁅ x ⁆s ∈ Lset (sucV σ) ⟩
    sglUp-mini σ {x} x∈ = Lset-in (sucV σ) σ ⁅ x ⁆s (self∈sucV σ)
      (𝒟ₒ-intro (Lset σ) ⁅ x ⁆s ∣ Φ , defSet≡ ∣₁)
      where
      module DefA = DefOf (Lset σ)
      mx = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
      qx : ⟪ Lset σ ⟫↪ mx ≡ x
      qx = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd
      Φ : Formula ⟪ Lset σ ⟫ 1
      Φ = var zero ≐ con mx
      defSet≡ : DefA.defSet Φ ≡ ⁅ x ⁆s
      defSet≡ = extensionality (DefA.defSet Φ) ⁅ x ⁆s (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet Φ ⊆ ⁅ x ⁆s ⟩
        sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ⁅ x ⁆s))
          (λ { ((m , h) , q) →
            subst (λ w → ⟨ w ∈ₛ ⁅ x ⁆s ⟩) q
              (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = ⁅ x ⁆s} .fst
                (singleton-in
                  (subst ⟨_⟩ (DefA.defSet-mem Φ m) ∣ (m , h) , refl ∣₁ ∙ qx))) })
          (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
        sub₂ : ⟨ ⁅ x ⁆s ⊆ DefA.defSet Φ ⟩
        sub₂ y y∈ₛ = subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) (qx ∙ sym ex)
          (∈∈ₛ {a = ⟪ Lset σ ⟫↪ mx} {b = DefA.defSet Φ} .fst
            (subst ⟨_⟩ (sym (DefA.defSet-mem Φ mx)) refl))
          where
          ex : y ≡ x
          ex = singleton-out (∈∈ₛ {a = y} {b = ⁅ x ⁆s} .snd y∈ₛ)

    module SglFam (X σ : V ℓ) (X∈ : ⟨ X ∈ Lset σ ⟩) where
      module DefA = DefOf (Lset (sucV σ))
      Atr = layer-trans (Lset-layer σ)

      E : ⟪ Lset (sucV σ) ⟫ → V ℓ
      E m = ⟪ Lset (sucV σ) ⟫↪ m

      X∈' : ⟨ X ∈ Lset (sucV σ) ⟩
      X∈' = Lset-mono {sucV σ} {σ} (self∈sucV σ) X∈
      mX = ∈-asFiber {a = X} {b = Lset (sucV σ)} X∈' .fst
      qX : E mX ≡ X
      qX = ∈-asFiber {a = X} {b = Lset (sucV σ)} X∈' .snd

      Φ : Formula ⟪ Lset (sucV σ) ⟫ 1
      Φ = ∃̇∈ (con mX) (sglAt′ {n = 2} (suc zero) zero)

      defSet≡ : DefA.defSet Φ ≡ singletons X
      defSet≡ = extensionality (DefA.defSet Φ) (singletons X) (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet Φ ⊆ singletons X ⟩
        sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ singletons X))
          (λ { ((m , h) , q) →
            subst (λ w → ⟨ w ∈ₛ singletons X ⟩) q
              (∈∈ₛ {a = E m} {b = singletons X} .fst
                (fromSat m (subst ⟨_⟩ (DefA.defSet-mem Φ m) ∣ (m , h) , refl ∣₁))) })
          (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
          where
          fromSat : (m : ⟪ Lset (sucV σ) ⟫)
                  → ⟨ (DefA.ι m ∷ []) DefA.⊨ᵐ Φ ⟩
                  → ⟨ E m ∈ singletons X ⟩
          fromSat m = PT.rec (snd (E m ∈ singletons X)) (go m)
            where
            go : (m : ⟪ Lset (sucV σ) ⟫)
               → Σ[ x ∈ DefA.SM ]
                   (⟨ fst x ∈ˢ fst (DefA.ι mX) ⟩
                  × ⟨ (x ∷ DefA.ι m ∷ []) DefA.⊨ᵐ sglAt′ {n = 2} (suc zero) zero ⟩)
               → ⟨ E m ∈ singletons X ⟩
            go m (x , hx , s) =
              let z≡ : E m ≡ ⁅ fst x ⁆s
                  z≡ = extensionality (E m) ⁅ fst x ⁆s (t₁ , t₂)
              in subst (λ w → ⟨ w ∈ singletons X ⟩) (sym z≡)
                   (singletons-in {X = X} {x = fst x}
                     (subst (λ w → ⟨ fst x ∈ w ⟩) qX hx))
              where
              Atr' = layer-trans (Lset-layer (sucV σ))
              membL : (m : ⟪ Lset (sucV σ) ⟫)
                    → ⟨ E m ∈ Lset (sucV σ) ⟩
              membL m = ∈∈ₛ {a = E m} {b = Lset (sucV σ)} .snd
                (∈ₛ⟪ Lset (sucV σ) ⟫↪ m)
              t₁ : ⟨ E m ⊆ ⁅ fst x ⁆s ⟩
              t₁ v v∈ₛ = ∈∈ₛ {a = v} {b = ⁅ fst x ⁆s} .fst
                (singleton-in (s₂ v (∈∈ₛ {a = v} {b = E m} .snd v∈ₛ)))
                where
                s₂ : (v : V ℓ) → ⟨ v ∈ E m ⟩ → v ≡ fst x
                s₂ v v∈Em =
                  s .snd (v , Atr' {x = E m} {y = v} v∈Em (membL m))
                         v∈Em
              t₂ : ⟨ ⁅ fst x ⁆s ⊆ E m ⟩
              t₂ v v∈ₛ = ∈∈ₛ {a = v} {b = E m} .fst
                (subst (λ w → ⟨ w ∈ E m ⟩)
                  (sym (singleton-out (∈∈ₛ {a = v} {b = ⁅ fst x ⁆s} .snd v∈ₛ)))
                  (s .fst))
        sub₂ : ⟨ singletons X ⊆ DefA.defSet Φ ⟩
        sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build
          (singletons-out {X = X} {w = y}
            (∈∈ₛ {a = y} {b = singletons X} .snd y∈ₛ))
          where
          build : Σ[ v ∈ V ℓ ] (⟨ v ∈ X ⟩ × (y ≡ ⁅ v ⁆s))
                → ⟨ y ∈ₛ DefA.defSet Φ ⟩
          build (v , hv , e) =
            let v∈σ : ⟨ v ∈ Lset σ ⟩
                v∈σ = Atr {x = X} {y = v} hv X∈
                y∈ⁱ : ⟨ y ∈ Lset (sucV σ) ⟩
                y∈ⁱ = subst (λ w → ⟨ w ∈ Lset (sucV σ) ⟩) (sym e) (sglUp-mini σ v∈σ)
                m' = ∈-asFiber {a = y} {b = Lset (sucV σ)} y∈ⁱ .fst
                q' : E m' ≡ y
                q' = ∈-asFiber {a = y} {b = Lset (sucV σ)} y∈ⁱ .snd
                v∈ⁱ' : ⟨ v ∈ Lset (sucV σ) ⟩
                v∈ⁱ' = Lset-mono {sucV σ} {σ} (self∈sucV σ) v∈σ
                sat : ⟨ (DefA.ι m' ∷ []) DefA.⊨ᵐ Φ ⟩
                sat = ∣ ( v , v∈ⁱ' ) , subst (λ w → ⟨ v ∈ w ⟩) (sym qX) hv
                    , ( subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ e)) (singleton-self v)
                      , λ y' y'∈ →
                          singleton-out
                            (subst (λ w → ⟨ fst y' ∈ w ⟩) (q' ∙ e)
                              y'∈) )
                    ∣₁
            in subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
                 (∈∈ₛ {a = E m'} {b = DefA.defSet Φ} .fst
                   (subst ⟨_⟩ (sym (DefA.defSet-mem Φ m')) sat))

  singletonsL : {X : V ℓ} → ⟨ isL X ⟩ → ⟨ isL (singletons X) ⟩
  singletonsL {X} lX = PT.rec (snd (isL (singletons X)))
    (λ { (σ , oσ , X∈ , _) →
      defSet→isL (sucV σ) (suc-ord oσ) (singletons X)
        ∣ SglFam.Φ X σ X∈ , SglFam.defSet≡ X σ X∈ ∣₁ })
    (isL-directed X X lX lX)
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
does. The reverse direction runs the same reading the other way: a member of
the singleton extension is the graph of an assignment extended by the constant
itself, so the tuple's head re-assembles the pinned formula's satisfaction
while the extension membership stays in the full family. With the renaming law
the two inclusions assemble into the full equation
`extendFamily (satSet φ) ⁅ κ a ⁆s ≡ satSet ((var zero ≐ con a) ∧̇ renameFo suc φ)`
delivered as `extendFamily-pin-eq`{.Agda}, the shape the kinded invariant's
constant-atom clause will consume.
<!--zh-->
## 钉住律

被裁到常元单点集的扩张。全扩张的成员是「被某载体成员扩张的赋值」的图；新键处的等词原子要求被扩张成员恰是常元，两者一起把族裁到单点集。证明使用等词原子的选择读式与扩张的两条目读式，而满足等式之元组的图首，对着查值规格去读，恰如满足关系章所做。反向读式把同一读法倒着跑：单点扩张的成员就是「被常元本身扩张的赋值」的图，故元组的图首重新装出被钉公式的满足，而扩张隶属留在全族里。与变量变换律一起，两条包含装配出完整的等式 `extendFamily (satSet φ) ⁅ κ a ⁆s ≡ satSet ((var zero ≐ con a) ∧̇ renameFo suc φ)`，即 `extendFamily-pin-eq`{.Agda}，也就是带种类不变量之常元原子子句将要消费的形状。
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

  -- The reverse inclusion: every member of the singleton extension records
  -- the constant at the fresh key, so it satisfies the pinned formula and
  -- lives in the full extension at the same time.
  extendFamily-pin-rev : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (a : ⟪ A ⟫)
                       → (w : V ℓ)
                       → ⟨ w ∈ extendFamily (satSet φ) ⁅ κ a ⁆s ⟩
                       → ⟨ w ∈ satSet {n = suc n} (var zero ≐ con a)
                           ∩ extendFamily (satSet φ) A ⟩
  extendFamily-pin-rev {n} φ a = λ w h →
    PT.rec (snd (w ∈ satSet {n = suc n} (var zero ≐ con a)
                 ∩ extendFamily (satSet φ) A)) (build w)
      (extendFamily-out {X = satSet φ} {Y = ⁅ κ a ⁆s} {w = w} h)
    where
    build : (w : V ℓ)
          → Σ[ γ ∈ V ℓ ] Σ[ y ∈ V ℓ ]
              (⟨ γ ∈ satSet φ ⟩ × ⟨ y ∈ ⁅ κ a ⁆s ⟩ × (w ≡ extendGraph y γ))
          → ⟨ w ∈ satSet {n = suc n} (var zero ≐ con a)
              ∩ extendFamily (satSet φ) A ⟩
    build w (γ , y , hγ , hy , eγ) = PT.rec tgt step (sat-out φ γ hγ)
      where
      tgt = snd (w ∈ satSet {n = suc n} (var zero ≐ con a)
                ∩ extendFamily (satSet φ) A)
      step : Σ[ g ∈ (Fin n → ⟪ A ⟫) ]
               (⟨ vec g ⊨ᵐ φ ⟩ × (tuple A g ≡ γ))
           → ⟨ w ∈ satSet {n = suc n} (var zero ≐ con a)
               ∩ extendFamily (satSet φ) A ⟩
      step (g , hg , eg) =
        let y≡ : y ≡ κ a
            y≡ = singleton-out hy
            g' : Fin (suc n) → ⟪ A ⟫
            g' = cons a g
            w≡ : w ≡ tuple A g'
            w≡ = eγ
               ∙ cong₂ extendGraph y≡ (sym eg)
               ∙ sym (tuple-extend A g')
            hw : ⟨ tuple A g' ∈ satSet {n = suc n} (var zero ≐ con a) ⟩
            hw = sat-in (var zero ≐ con a) g' (lk g' zero)
            w∈S : ⟨ w ∈ satSet {n = suc n} (var zero ≐ con a) ⟩
            w∈S = subst (λ z → ⟨ z ∈ satSet {n = suc n} (var zero ≐ con a) ⟩)
                   (sym w≡) hw
            y∈A : ⟨ y ∈ A ⟩
            y∈A = subst (λ z → ⟨ z ∈ A ⟩) (sym y≡) (memb a)
            w∈F : ⟨ w ∈ extendFamily (satSet φ) A ⟩
            w∈F = subst (λ z → ⟨ z ∈ extendFamily (satSet φ) A ⟩) (sym eγ)
                    (extendFamily-in {X = satSet φ} {Y = A} hγ y∈A)
        in ∩-in {X = satSet {n = suc n} (var zero ≐ con a)}
                {Y = extendFamily (satSet φ) A} w∈S w∈F

  -- The full family-extension equation, assembled from the renaming law and
  -- the two pinning inclusions.
  extendFamily-pin-eq : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (a : ⟪ A ⟫)
                      → extendFamily (satSet φ) ⁅ κ a ⁆s
                      ≡ satSet ((var zero ≐ con a) ∧̇ renameFo suc φ)
  extendFamily-pin-eq {n} φ a = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    L T : V ℓ
    L = extendFamily (satSet φ) ⁅ κ a ⁆s
    T = satSet ((var zero ≐ con a) ∧̇ renameFo suc φ)
    to : (w : V ℓ) → ⟨ w ∈ L ⟩ → ⟨ w ∈ T ⟩
    to w h = subst (λ z → ⟨ w ∈ z ⟩)
               (sym (sat-∧ (var zero ≐ con a) (renameFo suc φ)))
               (∩-in {X = satSet {n = suc n} (var zero ≐ con a)}
                     {Y = satSet (renameFo suc φ)}
                 (∩-out {X = satSet {n = suc n} (var zero ≐ con a)}
                   {Y = extendFamily (satSet φ) A} (extendFamily-pin-rev φ a w h) .fst)
                 (subst (λ z → ⟨ w ∈ z ⟩) (sym (satSet-rename-shift φ))
                   (∩-out {X = satSet {n = suc n} (var zero ≐ con a)}
                     {Y = extendFamily (satSet φ) A} (extendFamily-pin-rev φ a w h) .snd)))
    fro : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ L ⟩
    fro w h = extendFamily-pin φ a w
      (∩-in {X = satSet {n = suc n} (var zero ≐ con a)}
            {Y = extendFamily (satSet φ) A}
        (∩-out {X = satSet {n = suc n} (var zero ≐ con a)}
               {Y = satSet (renameFo suc φ)}
           (subst (λ z → ⟨ w ∈ z ⟩)
             (sat-∧ (var zero ≐ con a) (renameFo suc φ)) h) .fst)
        (subst (λ z → ⟨ w ∈ z ⟩) (satSet-rename-shift φ)
           (∩-out {X = satSet {n = suc n} (var zero ≐ con a)}
                  {Y = satSet (renameFo suc φ)}
             (subst (λ z → ⟨ w ∈ z ⟩)
               (sat-∧ (var zero ≐ con a) (renameFo suc φ)) h) .snd)))

```


<!--en-->
## The kinded levels

The closure's level structure now carries the arity as data. `slice A n k` is
the arity-`k` slice at level `n`: the shelf of arity-`k` families the closure
has built by level `n`. Different arities live on different shelves, and every
operation shops only on its own shelf, which is what makes the probe's junk
impossible by construction: a mixed-arity intersection, a complement across
arities, or a seed cut drawn from the carrier's raw members cannot arise,
because no clause of the step applies an operation across two shelves.

The seed is deliberately split. Level zero seeds the arity-zero shelf with the
singleton family of the carrier: `slice A 0 0 = singletons A`, and every higher
shelf starts empty. The carrier's own members enter the closure only as their
singletons, and only on the arity-zero shelf: a raw member of `A` is not
generally a subset of `A`, so seeding it into a shelf the cut can read would
let the values-cut escape the definable powerset (the probe's escape case);
its singleton `⁅ κ a ⁆s` is exactly the argument the constant-atom composite
feeds to the family extension, which is why the singleton family seeds this
shelf, entering from the B2 machinery.

Each level is one round of operation images, cumulative in the level:
`slice A (suc n) k = slice A n k ∪ step A n k`. The step applies each operation
only inside the arity it respects: intersection, union, difference, and the two
selections stay within a slice; `allTuples A k` enters slice `k` from nothing
but the numeral; the family extension moves a slice up by one arity, drawing
its first argument from a positive-arity slice and its second argument from the
seeded arity-zero shelf; the shift moves a slice down by one; and `values`
reads the arity-one slice and writes the arity-zero shelf.

The membership laws are direction-paired. Each clause has its `slice-in` law,
building the image's fiber from the arguments' memberships; `slice-out` is the
disjunctive inversion, reading a member of the next level back into an old
member or one of the step's tagged images with its payload. The cumulative
level is a union, and its reading is exactly the pair of directions of `_∪_`:
`slice-old` is the old-member inclusion, and the images enter through the
step's fiber. The definition follows the operations idiom: each clause image
is one direct `sett` over a sum of presentations of the previous level,
union-free at the definition level, and the level union sits at the top of
`slice`, never under a sealed index, so no seal is needed at the birth site
(the P-b/P-c reading adopted here: union-free where a membership obligation
will ever read the clauses, and the one union that is a membership obligation,
the cumulative level, is direction-paired and unsealed).
<!--zh-->
## 带种类的诸层

闭包的层结构如今把元数作为数据携带。`slice A n k` 是第 `n` 层的第 `k` 元数片：到第 `n` 层为止闭包已经搭起的第 `k` 元数诸族所住的架位。不同元数分居不同的架位，每个运算只在自己的架位上作业，这正使探针的垃圾按构造成为不可能：混合元数的交、跨元数的补、或从载体原始成员取出的种子切口无从出现，因为步骤的每条子句都不让运算跨架位。

种子被有意拆分。第零层以载体的单例族播种第零元数片：`slice A 0 0 = singletons A`，其余更高片从空开始。载体的成员只以它们的单例进场，且只进第零元数片：`A` 的原始成员一般不是 `A` 的子集，把它播进切定理可读的片会让取值切口逃出可定义幂集 (探针的逃逸情形)；而它的单例 `⁅ κ a ⁆s` 恰是常元原子复合体喂给族扩张的那个实参，这正是单例族播种这片、自 B2 机制进场的原因。

每层是一轮运算像，随层累积：`slice A (suc n) k = slice A n k ∪ step A n k`。步骤只把每个运算施于它所尊重的元数之内：交、并、差与两个选择都留在片内；`allTuples A k` 除数码外不取任何实参即进入第 `k` 片；族扩张把片向上移一元数，首实参取自正元数片，次实参取自被播种的第零元数片；移位把片向下移一元数；`values` 读第一元数片、写第零元数片。

隶属定律双向配对。每条子句有它的 `slice-in` 律，从诸实参的隶属装出像的纤维；`slice-out` 是析取式的反转，把下一层的成员读回旧成员或某个带标签的步骤像连同其载荷。累积层就是一次并，其读法恰是 `_∪_` 的两个方向：`slice-old` 是旧成员包含，诸像经步骤的纤维进场。定义遵循运算章行事：每条子句的像都是落在上一层诸表示之和一个和上的单个 `sett`，定义层无并；层并坐在 `slice` 的顶端，从不在封印的索引之下，故诞生处无需封印 (此处采用的 P-b/P-c 读法：凡隶属义务将要读到的子句皆无并，而那一次身为隶属义务的并，即累积层，双向配对且不封印)。
<!--/-->

```agda
  data StepTag : ℕ → Type ℓ where
    tagInter tagUnion tagDiff : {k : ℕ} → StepTag k
    tagSelM tagSelE : {k : ℕ} → StepTag k
    tagAll : {k : ℕ} → StepTag k
    tagExt : {k : ℕ} → StepTag (suc (suc k))
    tagShift : {k : ℕ} → StepTag k
    tagValues : StepTag 0

  mutual
    slice : ℕ → ℕ → V ℓ
    slice zero zero = singletons A
    slice zero (suc k) = ∅
    slice (suc n) k = slice n k ∪ step n k

    step : ℕ → ℕ → V ℓ
    step n k = sett (Σ[ t ∈ StepTag k ] StepPayload n k t)
                    (λ { (t , p) → stepImage t p })

    StepPayload : (n k : ℕ) → StepTag k → Type ℓ
    StepPayload n k tagInter = ⟪ slice n k ⟫ × ⟪ slice n k ⟫
    StepPayload n k tagUnion = ⟪ slice n k ⟫ × ⟪ slice n k ⟫
    StepPayload n k tagDiff = ⟪ slice n k ⟫ × ⟪ slice n k ⟫
    StepPayload n k tagSelM = Σ[ m ∈ ⟪ slice n k ⟫ ] Fin k × Fin k
    StepPayload n k tagSelE = Σ[ m ∈ ⟪ slice n k ⟫ ] Fin k × Fin k
    StepPayload n k tagAll = Unit* {ℓ}
    StepPayload n (suc (suc k)) tagExt = Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] ⟪ A ⟫
    StepPayload n k tagShift = ⟪ slice n (suc k) ⟫
    StepPayload n 0 tagValues = ⟪ slice n 1 ⟫

    stepImage : {n k : ℕ} (t : StepTag k) (p : StepPayload n k t) → V ℓ
    stepImage {n} {k} tagInter (m , q) = ⟪ slice n k ⟫↪ m ∩ ⟪ slice n k ⟫↪ q
    stepImage {n} {k} tagUnion (m , q) = ⟪ slice n k ⟫↪ m ∪ ⟪ slice n k ⟫↪ q
    stepImage {n} {k} tagDiff (m , q) = ⟪ slice n k ⟫↪ m ∖ ⟪ slice n k ⟫↪ q
    stepImage {n} {k} tagSelM (m , i , j) =
      selectMember (⟪ slice n k ⟫↪ m) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
    stepImage {n} {k} tagSelE (m , i , j) =
      selectEqual (⟪ slice n k ⟫↪ m) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
    stepImage {n} {k} tagAll tt* = allTuples A k
    stepImage {n} {suc (suc k)} tagExt (m , a) =
      extendFamily (⟪ slice n (suc k) ⟫↪ m) ⁅ κ a ⁆s
    stepImage {n} {k} tagShift m = shiftDown (⟪ slice n (suc k) ⟫↪ m)
    stepImage {n} {zero} tagValues m = values (⟪ slice n 1 ⟫↪ m)

  -- The membership laws, one `slice-in` per clause and `slice-out` as the
  -- disjunctive inversion, direction-paired.
  slice-∩-in : {n k : ℕ} {X Y : V ℓ}
             → ⟨ X ∈ slice n k ⟩ → ⟨ Y ∈ slice n k ⟩
             → ⟨ X ∩ Y ∈ slice (suc n) k ⟩
  slice-∩-in {n} {k} {X} {Y} hX hY =
    ∪-right {X = slice n k} {Y = step n k}
      ∣ (tagInter , (fX .fst , fY .fst))
      , cong₂ _∩_ (fX .snd) (fY .snd) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n k} hX
    fY : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ Y)
    fY = ∈-asFiber {a = Y} {b = slice n k} hY

  slice-∪-in : {n k : ℕ} {X Y : V ℓ}
             → ⟨ X ∈ slice n k ⟩ → ⟨ Y ∈ slice n k ⟩
             → ⟨ X ∪ Y ∈ slice (suc n) k ⟩
  slice-∪-in {n} {k} {X} {Y} hX hY =
    ∪-right {X = slice n k} {Y = step n k}
      ∣ (tagUnion , (fX .fst , fY .fst))
      , cong₂ _∪_ (fX .snd) (fY .snd) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n k} hX
    fY : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ Y)
    fY = ∈-asFiber {a = Y} {b = slice n k} hY

  slice-∖-in : {n k : ℕ} {X Y : V ℓ}
             → ⟨ X ∈ slice n k ⟩ → ⟨ Y ∈ slice n k ⟩
             → ⟨ X ∖ Y ∈ slice (suc n) k ⟩
  slice-∖-in {n} {k} {X} {Y} hX hY =
    ∪-right {X = slice n k} {Y = step n k}
      ∣ (tagDiff , (fX .fst , fY .fst))
      , cong₂ _∖_ (fX .snd) (fY .snd) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n k} hX
    fY : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ Y)
    fY = ∈-asFiber {a = Y} {b = slice n k} hY

  slice-selM-in : {n k : ℕ} {X : V ℓ} (i j : Fin k)
                → ⟨ X ∈ slice n k ⟩
                → ⟨ selectMember X ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
                     ∈ slice (suc n) k ⟩
  slice-selM-in {n} {k} {X} i j hX =
    ∪-right {X = slice n k} {Y = step n k}
      ∣ (tagSelM , (fX .fst , i , j))
      , cong (λ W → selectMember W ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s) (fX .snd) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n k} hX

  slice-selE-in : {n k : ℕ} {X : V ℓ} (i j : Fin k)
                → ⟨ X ∈ slice n k ⟩
                → ⟨ selectEqual X ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
                     ∈ slice (suc n) k ⟩
  slice-selE-in {n} {k} {X} i j hX =
    ∪-right {X = slice n k} {Y = step n k}
      ∣ (tagSelE , (fX .fst , i , j))
      , cong (λ W → selectEqual W ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s) (fX .snd) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n k ⟫ ] (⟪ slice n k ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n k} hX

  slice-allTuples-in : {n k : ℕ} → ⟨ allTuples A k ∈ slice (suc n) k ⟩
  slice-allTuples-in {n} {k} =
    ∪-right {X = slice n k} {Y = step n k} ∣ (tagAll , tt*) , refl ∣₁

  slice-extendFamily-in : {n k : ℕ} {X : V ℓ} (a : ⟪ A ⟫)
                        → ⟨ X ∈ slice n (suc k) ⟩ → ⟨ ⁅ κ a ⁆s ∈ slice n 0 ⟩
                        → ⟨ extendFamily X ⁅ κ a ⁆s ∈ slice (suc n) (suc (suc k)) ⟩
  slice-extendFamily-in {n} {k} {X} a hX ha =
    ∪-right {X = slice n (suc (suc k))} {Y = step n (suc (suc k))}
      ∣ (tagExt , (fX .fst , fa .fst))
      , cong₂ extendFamily (fX .snd) (cong ⁅_⁆s (fa .snd)) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] (⟪ slice n (suc k) ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n (suc k)} hX
    fa : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ κ a)
    fa = ∈-asFiber {a = κ a} {b = A} (memb a)

  slice-shiftDown-in : {n k : ℕ} {X : V ℓ}
                     → ⟨ X ∈ slice n (suc k) ⟩ → ⟨ shiftDown X ∈ slice (suc n) k ⟩
  slice-shiftDown-in {n} {k} {X} hX =
    ∪-right {X = slice n k} {Y = step n k}
      ∣ (tagShift , fX .fst) , cong shiftDown (fX .snd) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] (⟪ slice n (suc k) ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n (suc k)} hX

  slice-values-in : {n : ℕ} {X : V ℓ}
                  → ⟨ X ∈ slice n 1 ⟩ → ⟨ values X ∈ slice (suc n) 0 ⟩
  slice-values-in {n} {X} hX =
    ∪-right {X = slice n 0} {Y = step n 0}
      ∣ (tagValues , fX .fst) , cong values (fX .snd) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n 1 ⟫ ] (⟪ slice n 1 ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n 1} hX

  slice-step-out : {n k : ℕ} (u : V ℓ) → ⟨ u ∈ step n k ⟩
                 → ∥ Σ[ t ∈ StepTag k ] Σ[ p ∈ StepPayload n k t ]
                       (stepImage {n} {k} t p ≡ u) ∥₁
  slice-step-out {n} {k} u = PT.map
    λ { ((t , p) , e) → t , p , e }

  slice-out : {n k : ℕ} (u : V ℓ) → ⟨ u ∈ slice (suc n) k ⟩
            → ∥ ⟨ u ∈ slice n k ⟩
              ⊎ (Σ[ t ∈ StepTag k ] Σ[ p ∈ StepPayload n k t ]
                   (stepImage {n} {k} t p ≡ u)) ∥₁
  slice-out {n} {k} u hu = PT.rec squash₁ go
    (∪-out {X = slice n k} {Y = step n k} {x = u} hu)
    where
    go : ⟨ u ∈ slice n k ⟩ ⊎ ⟨ u ∈ step n k ⟩
       → ∥ ⟨ u ∈ slice n k ⟩
         ⊎ (Σ[ t ∈ StepTag k ] Σ[ p ∈ StepPayload n k t ]
              (stepImage {n} {k} t p ≡ u)) ∥₁
    go (inl h) = ∣ inl h ∣₁
    go (inr hs) = PT.map inr (slice-step-out u hs)

  -- The seed's law and the level merge: a member of a lower level sits in
  -- every higher level, once by the old-member inclusion and then by
  -- iteration on either side of the addition.
  slice-singleton-seed : (a : ⟪ A ⟫) → ⟨ ⁅ κ a ⁆s ∈ slice 0 0 ⟩
  slice-singleton-seed a = singletons-in {X = A} {x = κ a} (memb a)

  slice-old : {n k : ℕ} {X : V ℓ} → ⟨ X ∈ slice n k ⟩ → ⟨ X ∈ slice (suc n) k ⟩
  slice-old {n} {k} {X} h = ∪-left {X = slice n k} {Y = step n k} {x = X} h

  slice-addR : (n m k : ℕ) (X : V ℓ)
             → ⟨ X ∈ slice n k ⟩ → ⟨ X ∈ slice (n + m) k ⟩
  slice-addR n zero k X h = subst (λ z → ⟨ X ∈ slice z k ⟩) (sym (+-zero n)) h
  slice-addR n (suc m) k X h =
    subst (λ z → ⟨ X ∈ slice z k ⟩) (sym (+-suc n m))
      (slice-old {n = n + m} {k} {X} (slice-addR n m k X h))

  slice-addL : (n m k : ℕ) (X : V ℓ)
             → ⟨ X ∈ slice n k ⟩ → ⟨ X ∈ slice (m + n) k ⟩
  slice-addL n zero k X h = h
  slice-addL n (suc m) k X h =
    slice-old {n = m + n} {k} {X} (slice-addL n m k X h)
```


<!--en-->
## The kinded invariant

Every member of a positive-arity slice at every level is an arity-`k`
satisfaction set over the carrier: `slice-inv` states
`u ∈ slice A n (suc k)` gives `∥ Σ[ φ ∈ Formula ⟪ A ⟫ (suc k) ] (u ≡ satSet φ) ∥₁`,
by induction on the level. At level zero the higher shelves are empty, so the
base is vacuous. At a successor level, `slice-out` splits the member into an
old member, handed to the induction hypothesis, or one of the step's tagged
images, and each image case is the delivered equation stock run backward: the
intersection lands by `sat-∧`, the union by `sat-∨`, the difference by the
conjunction-with-negation equation assembled here from `sat-∧`, `sat-¬`, and
the bound `satSet⊆` (a satisfaction set never leaves the tuple family it
describes), the two selections by this chapter's `sat-∈vv-sel` and
`sat-≐vv-sel`, the tuple family by `sat-⊤`, the family extension by the
pinning equation `extendFamily-pin-eq`, and the shift by `sat-∃`. This is the
closure analog of `Terms.sound`, and it replaces the certificate's honesty
induction: no codes, no annotation table, plain structural induction on the
level, one case per clause, each discharged by an equation. The arity-zero
shelf is deliberately outside its scope: it is the value shelf, where `values`
lands and the singleton family seeds the constant-atom arguments, not a shelf
of tuple families.
<!--zh-->
## 带种类的不变量

每个正元数片在每个层级的每个成员，都是载体上的 `k` 元数满足集：`slice-inv` 说 `u ∈ slice A n (suc k)` 推出 `∥ Σ[ φ ∈ Formula ⟪ A ⟫ (suc k) ] (u ≡ satSet φ) ∥₁`，按层级归纳。在第零层，更高片皆空，基步空然成立。在后继层，`slice-out` 把成员拆成旧成员 (交给归纳假设) 或某个带标签的步骤像，而每个像的情形都是已交付等式存货的反向运行：交经 `sat-∧` 落地，并经 `sat-∨`，差经此处由 `sat-∧`、`sat-¬` 与界 `satSet⊆` (满足集永不离开它所描述的元组族) 装配出的「合取加否定」等式，两个选择经本章的 `sat-∈vv-sel` 与 `sat-≐vv-sel`，元组族经 `sat-⊤`，族扩张经钉住等式 `extendFamily-pin-eq`，移位经 `sat-∃`。这是 `Terms.sound` 的闭包对应物，它取代证书的诚实性归纳：没有码，没有注解表，只是对层级的朴素结构归纳，每个子句一个情形，每个情形由一条等式消去。第零元数片被有意排除在范围之外：它是取值片，`values` 落在那里、单例族在那里播种常元原子的实参，而不是元组族之片。
<!--/-->

```agda
  -- The satisfaction equations the invariant consumes, restated locally
  -- against this chapter's satSet: Satisfaction's tabulation is private, so
  -- its stock cannot be reused by import, exactly as B1 restated the atoms
  -- and the conjunction.
  sat-⊤ : {n : ℕ} → satSet {n} ⊤̇ ≡ allTuples A n
  sat-⊤ {n} = extensionalV λ w → ⇔toPath
    (PT.rec (snd (w ∈ allTuples A n)) (λ { ((g , _) , e) → ∣ g , e ∣₁ }))
    (PT.rec (snd (w ∈ satSet ⊤̇))
      (λ { (g , e) → subst (λ z → ⟨ z ∈ satSet ⊤̇ ⟩) e (sat-in ⊤̇ g tt*) }))

  sat-∨ : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
        → satSet (φ ∨̇ ψ) ≡ satSet φ ∪ satSet ψ
  sat-∨ {n} φ ψ = extensionalV λ w → ⇔toPath (fwdOr w) (bwdOr w)
    where
    T : V ℓ
    T = satSet φ ∪ satSet ψ
    fwdOr : (w : V ℓ) → ⟨ w ∈ satSet (φ ∨̇ ψ) ⟩ → ⟨ w ∈ T ⟩
    fwdOr w h = PT.rec (snd (w ∈ T))
      (λ { (g , hd , e) → PT.rec (snd (w ∈ T))
        (Sum.rec
          (λ hφ → subst (λ z → ⟨ z ∈ T ⟩) e
            (∪-left {X = satSet φ} {Y = satSet ψ} (sat-in φ g hφ)))
          (λ hψ → subst (λ z → ⟨ z ∈ T ⟩) e
            (∪-right {X = satSet φ} {Y = satSet ψ} (sat-in ψ g hψ))))
        hd })
      (sat-out (φ ∨̇ ψ) w h)
    bwdOr : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (φ ∨̇ ψ) ⟩
    bwdOr w h = PT.rec (snd (w ∈ satSet (φ ∨̇ ψ)))
      (Sum.rec
        (λ hφ → PT.rec (snd (w ∈ satSet (φ ∨̇ ψ)))
          (λ { (g , hg , e) →
            subst (λ z → ⟨ z ∈ satSet (φ ∨̇ ψ) ⟩) e
              (sat-in (φ ∨̇ ψ) g ∣ Sum.inl hg ∣₁) })
          (sat-out φ w hφ))
        (λ hψ → PT.rec (snd (w ∈ satSet (φ ∨̇ ψ)))
          (λ { (g , hg , e) →
            subst (λ z → ⟨ z ∈ satSet (φ ∨̇ ψ) ⟩) e
              (sat-in (φ ∨̇ ψ) g ∣ Sum.inr hg ∣₁) })
          (sat-out ψ w hψ)))
      (∪-out {X = satSet φ} {Y = satSet ψ} {x = w} h)

  sat-¬ : {n : ℕ} (φ : Formula ⟪ A ⟫ n)
        → satSet (¬̇ φ) ≡ allTuples A n ∖ satSet φ
  sat-¬ {n} φ = extensionalV λ w → ⇔toPath (fwdNeg w) (bwdNeg w)
    where
    T : V ℓ
    T = allTuples A n ∖ satSet φ
    fwdNeg : (w : V ℓ) → ⟨ w ∈ satSet (¬̇ φ) ⟩ → ⟨ w ∈ T ⟩
    fwdNeg w h = PT.rec (snd (w ∈ T))
      (λ { (g , hn , e) →
        subst (λ z → ⟨ z ∈ T ⟩) e
          (∖-in {X = allTuples A n} {Y = satSet φ}
            ∣ g , refl ∣₁
            (λ hw → PT.rec Empty.isProp⊥
              (λ { (g' , hg' , e') →
                hn (subst (λ δ → ⟨ δ ⊨ᵐ φ ⟩) (vec-inj e') hg') })
              (sat-out φ (tuple A g) hw))) })
      (sat-out (¬̇ φ) w h)
    bwdNeg : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (¬̇ φ) ⟩
    bwdNeg w h = PT.rec (snd (w ∈ satSet (¬̇ φ)))
      (λ { (g , e) →
        subst (λ z → ⟨ z ∈ satSet (¬̇ φ) ⟩) e
          (sat-in (¬̇ φ) g
            (λ hg → ∖-out {X = allTuples A n} {Y = satSet φ} {x = w} h .snd
              (subst (λ z → ⟨ z ∈ satSet φ ⟩) e (sat-in φ g hg)))) })
      (∖-out {X = allTuples A n} {Y = satSet φ} {x = w} h .fst)

  sat-∃ : {n : ℕ} (ψ : Formula ⟪ A ⟫ (suc n))
        → satSet (∃̇ ψ) ≡ shiftDown (satSet ψ)
  sat-∃ {n} ψ = extensionalV λ w → ⇔toPath (fwdEx w) (bwdEx w)
    where
    T : V ℓ
    T = shiftDown (satSet ψ)
    fwdEx : (w : V ℓ) → ⟨ w ∈ satSet (∃̇ ψ) ⟩ → ⟨ w ∈ T ⟩
    fwdEx w hw = PT.rec (snd (w ∈ T))
      (λ { (g , hex , e) → PT.rec (snd (w ∈ T))
        (λ { (x , hx) →
          let fx = ∈-asFiber {a = fst x} {b = A} (x .snd)
              m : ⟪ A ⟫
              m = fx .fst
              x≡ιm : x ≡ ι m
              x≡ιm = Σ≡Prop (λ v → snd (v ∈ A)) (sym (fx .snd))
              hψ : ⟨ vec (cons m g) ⊨ᵐ ψ ⟩
              hψ = subst (λ z → ⟨ (z ∷ vec g) ⊨ᵐ ψ ⟩) x≡ιm hx
          in subst (λ z → ⟨ z ∈ T ⟩)
               (tupleTail A (cons m g) ∙ e)
               (shiftDown-in {X = satSet ψ} (sat-in ψ (cons m g) hψ)) })
        hex })
      (sat-out (∃̇ ψ) w hw)
    bwdEx : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (∃̇ ψ) ⟩
    bwdEx w h = PT.rec (snd (w ∈ satSet (∃̇ ψ)))
      (λ { (z , hz , ez) → PT.rec (snd (w ∈ satSet (∃̇ ψ)))
        (λ { (f , hf , ef) →
          subst (λ q → ⟨ q ∈ satSet (∃̇ ψ) ⟩)
            (sym (tupleTail A f) ∙ cong tailGraph ef ∙ ez)
            (sat-in (∃̇ ψ) (λ i → f (suc i)) ∣ ι (f zero) , hf ∣₁) })
        (sat-out ψ z hz) })
      (shiftDown-out {X = satSet ψ} h)

  sat-defSet : (φ : Formula ⟪ A ⟫ 1)
             → values (satSet φ) ≡ defSet φ
  sat-defSet φ = extensionalV λ v → ⇔toPath (fwdVal v) (bwdVal v)
    where
    fwdVal : (v : V ℓ) → ⟨ v ∈ values (satSet φ) ⟩ → ⟨ v ∈ defSet φ ⟩
    fwdVal v h = PT.rec (snd (v ∈ defSet φ))
      (λ { (γ , hγ , hv) → PT.rec (snd (v ∈ defSet φ))
        (λ { (g , hg , e) →
          let ev : v ≡ κ (g zero)
              ev = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) zero v)
                     (subst (λ q → ⟨ pr (# 0) v ∈ q ⟩) (sym e) hv)
          in subst (λ q → ⟨ q ∈ defSet φ ⟩) (sym ev)
               (subst ⟨_⟩ (sym (defSet-mem φ (g zero))) hg) })
        (sat-out φ γ hγ) })
      (values-wit {X = satSet φ} {v = v} h)
    bwdVal : (v : V ℓ) → ⟨ v ∈ defSet φ ⟩ → ⟨ v ∈ values (satSet φ) ⟩
    bwdVal v = PT.rec (snd (v ∈ values (satSet φ)))
      (λ { ((m , s) , e) →
        subst (λ q → ⟨ q ∈ values (satSet φ) ⟩) e
          (values-in {X = satSet φ}
            {γ = tuple A (λ _ → m)} {v = κ m}
            (sat-in φ (λ _ → m)
              (invEq (⊨ᵐ-small φ (ι m ∷ []) .snd) s))
            ∣ lift zero , refl ∣₁) })

  satSet⊆ : {n : ℕ} (φ : Formula ⟪ A ⟫ n) (x : V ℓ)
          → ⟨ x ∈ satSet φ ⟩ → ⟨ x ∈ allTuples A n ⟩
  satSet⊆ {n} φ x hx = PT.rec (snd (x ∈ allTuples A n))
    (λ { (g , _ , e) → subst (λ z → ⟨ z ∈ allTuples A n ⟩) e ∣ g , refl ∣₁ })
    (sat-out φ x hx)

  satSet-∖ : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
           → satSet φ ∖ satSet ψ ≡ satSet (φ ∧̇ ¬̇ ψ)
  satSet-∖ {n} φ ψ = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    L : V ℓ
    L = satSet φ ∖ satSet ψ
    R : V ℓ
    R = satSet (φ ∧̇ ¬̇ ψ)
    to : (w : V ℓ) → ⟨ w ∈ L ⟩ → ⟨ w ∈ R ⟩
    to w h = subst (λ z → ⟨ w ∈ z ⟩) (sym (sat-∧ φ (¬̇ ψ)))
      (∩-in {X = satSet φ} {Y = satSet (¬̇ ψ)}
        (∖-out {X = satSet φ} {Y = satSet ψ} {x = w} h .fst)
        (subst (λ z → ⟨ w ∈ z ⟩) (sym (sat-¬ ψ))
          (∖-in {X = allTuples A n} {Y = satSet ψ}
            (satSet⊆ φ w (∖-out {X = satSet φ} {Y = satSet ψ} {x = w} h .fst))
            (∖-out {X = satSet φ} {Y = satSet ψ} {x = w} h .snd))))
    fro : (w : V ℓ) → ⟨ w ∈ R ⟩ → ⟨ w ∈ L ⟩
    fro w h = PT.rec (snd (w ∈ L)) build (sat-out (φ ∧̇ ¬̇ ψ) w h)
      where
      build : Σ[ g ∈ (Fin n → ⟪ A ⟫) ]
                (⟨ vec g ⊨ᵐ (φ ∧̇ ¬̇ ψ) ⟩ × (tuple A g ≡ w))
            → ⟨ w ∈ L ⟩
      build (g , hc , e) =
        let nψ : ⟨ tuple A g ∈ satSet ψ ⟩ → Empty.⊥
            nψ hψ = ∖-out {X = allTuples A n} {Y = satSet ψ} {x = w}
              (subst (λ z → ⟨ w ∈ z ⟩) (sat-¬ ψ)
                (subst (λ z → ⟨ z ∈ satSet (¬̇ ψ) ⟩) e (sat-in (¬̇ ψ) g (hc .snd))))
              .snd (subst (λ z → ⟨ z ∈ satSet ψ ⟩) e hψ)
        in subst (λ z → ⟨ z ∈ L ⟩) e
             (∖-in {X = satSet φ} {Y = satSet ψ}
               (sat-in φ g (hc .fst)) nψ)

  slice-inv : (n k : ℕ) (u : V ℓ) → ⟨ u ∈ slice n (suc k) ⟩
            → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ (suc k) ] (u ≡ satSet φ) ∥₁
  slice-inv zero k u hu = Empty.rec (∅-empty u (∈∈ₛ {a = u} {b = ∅} .fst hu))
  slice-inv (suc n) k u hu = PT.rec squash₁ split (slice-out u hu)
    where
    T : Type (ℓ-suc ℓ)
    T = Σ[ φ ∈ Formula ⟪ A ⟫ (suc k) ] (u ≡ satSet φ)

    inter-case : (m q : ⟪ slice n (suc k) ⟫)
               → stepImage {n} {suc k} tagInter (m , q) ≡ u → ∥ T ∥₁
    inter-case m q e =
      let X : V ℓ
          X = ⟪ slice n (suc k) ⟫↪ m
          hX : ⟨ X ∈ slice n (suc k) ⟩
          hX = ∈∈ₛ {a = X} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) m)
          Y : V ℓ
          Y = ⟪ slice n (suc k) ⟫↪ q
          hY : ⟨ Y ∈ slice n (suc k) ⟩
          hY = ∈∈ₛ {a = Y} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) q)
      in PT.rec squash₁ (λ { (φ , eφ) → PT.rec squash₁
            (λ { (ψ , eψ) → ∣ φ ∧̇ ψ
                , sym e ∙ cong₂ _∩_ eφ eψ ∙ sym (sat-∧ φ ψ) ∣₁ })
            (slice-inv n k Y hY) })
        (slice-inv n k X hX)

    union-case : (m q : ⟪ slice n (suc k) ⟫)
               → stepImage {n} {suc k} tagUnion (m , q) ≡ u → ∥ T ∥₁
    union-case m q e =
      let X : V ℓ
          X = ⟪ slice n (suc k) ⟫↪ m
          hX : ⟨ X ∈ slice n (suc k) ⟩
          hX = ∈∈ₛ {a = X} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) m)
          Y : V ℓ
          Y = ⟪ slice n (suc k) ⟫↪ q
          hY : ⟨ Y ∈ slice n (suc k) ⟩
          hY = ∈∈ₛ {a = Y} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) q)
      in PT.rec squash₁ (λ { (φ , eφ) → PT.rec squash₁
            (λ { (ψ , eψ) → ∣ φ ∨̇ ψ
                , sym e ∙ cong₂ _∪_ eφ eψ ∙ sym (sat-∨ φ ψ) ∣₁ })
            (slice-inv n k Y hY) })
        (slice-inv n k X hX)

    diff-case : (m q : ⟪ slice n (suc k) ⟫)
              → stepImage {n} {suc k} tagDiff (m , q) ≡ u → ∥ T ∥₁
    diff-case m q e =
      let X : V ℓ
          X = ⟪ slice n (suc k) ⟫↪ m
          hX : ⟨ X ∈ slice n (suc k) ⟩
          hX = ∈∈ₛ {a = X} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) m)
          Y : V ℓ
          Y = ⟪ slice n (suc k) ⟫↪ q
          hY : ⟨ Y ∈ slice n (suc k) ⟩
          hY = ∈∈ₛ {a = Y} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) q)
      in PT.rec squash₁ (λ { (φ , eφ) → PT.rec squash₁
            (λ { (ψ , eψ) → ∣ φ ∧̇ ¬̇ ψ
                , sym e ∙ cong₂ _∖_ eφ eψ ∙ satSet-∖ φ ψ ∣₁ })
            (slice-inv n k Y hY) })
        (slice-inv n k X hX)

    selM-case : (m : ⟪ slice n (suc k) ⟫) (i j : Fin (suc k))
              → stepImage {n} {suc k} tagSelM (m , i , j) ≡ u → ∥ T ∥₁
    selM-case m i j e =
      let X : V ℓ
          X = ⟪ slice n (suc k) ⟫↪ m
          hX : ⟨ X ∈ slice n (suc k) ⟩
          hX = ∈∈ₛ {a = X} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) m)
      in PT.rec squash₁ (λ { (φ , eφ) → ∣ φ ∧̇ (var i ∈̇ var j)
            , sym e
            ∙ cong (λ W → selectMember W ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s) eφ
            ∙ sat-∈vv-sel φ i j ∣₁ })
        (slice-inv n k X hX)

    selE-case : (m : ⟪ slice n (suc k) ⟫) (i j : Fin (suc k))
              → stepImage {n} {suc k} tagSelE (m , i , j) ≡ u → ∥ T ∥₁
    selE-case m i j e =
      let X : V ℓ
          X = ⟪ slice n (suc k) ⟫↪ m
          hX : ⟨ X ∈ slice n (suc k) ⟩
          hX = ∈∈ₛ {a = X} {b = slice n (suc k)} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k)) m)
      in PT.rec squash₁ (λ { (φ , eφ) → ∣ φ ∧̇ (var i ≐ var j)
            , sym e
            ∙ cong (λ W → selectEqual W ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s) eφ
            ∙ sat-≐vv-sel φ i j ∣₁ })
        (slice-inv n k X hX)

    ext-case : (k' : ℕ) (m : ⟪ slice n (suc k') ⟫) (a : ⟪ A ⟫)
             → stepImage {n} {suc (suc k')} tagExt (m , a) ≡ u
             → ∥ Σ[ φ ∈ Formula ⟪ A ⟫ (suc (suc k')) ] (u ≡ satSet φ) ∥₁
    ext-case k' m a e =
      let X : V ℓ
          X = ⟪ slice n (suc k') ⟫↪ m
          hX : ⟨ X ∈ slice n (suc k') ⟩
          hX = ∈∈ₛ {a = X} {b = slice n (suc k')} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc k')) m)
      in PT.rec squash₁ (λ { (φ , eφ) →
            ∣ (var zero ≐ con a) ∧̇ renameFo suc φ
            , sym e
            ∙ cong (λ W → extendFamily W ⁅ κ a ⁆s) eφ
            ∙ extendFamily-pin-eq φ a ∣₁ })
        (slice-inv n k' X hX)

    shift-case : (m : ⟪ slice n (suc (suc k)) ⟫)
               → stepImage {n} {suc k} tagShift m ≡ u → ∥ T ∥₁
    shift-case m e =
      let X : V ℓ
          X = ⟪ slice n (suc (suc k)) ⟫↪ m
          hX : ⟨ X ∈ slice n (suc (suc k)) ⟩
          hX = ∈∈ₛ {a = X} {b = slice n (suc (suc k))} .snd
                 (∈ₛ⟪_⟫↪_ (slice n (suc (suc k))) m)
      in PT.rec squash₁ (λ { (ψ , eψ) → ∣ ∃̇ ψ
            , sym e ∙ cong shiftDown eψ ∙ sym (sat-∃ ψ) ∣₁ })
        (slice-inv n (suc k) X hX)

    step' : Σ[ t ∈ StepTag (suc k) ] Σ[ p ∈ StepPayload n (suc k) t ]
              (stepImage {n} {suc k} t p ≡ u)
          → ∥ T ∥₁
    step' (tagInter , (m , q) , e) = inter-case m q e
    step' (tagUnion , (m , q) , e) = union-case m q e
    step' (tagDiff , (m , q) , e) = diff-case m q e
    step' (tagSelM , (m , i , j) , e) = selM-case m i j e
    step' (tagSelE , (m , i , j) , e) = selE-case m i j e
    step' (tagAll , tt* , e) = ∣ ⊤̇ , sym e ∙ sym (sat-⊤ {n = suc k}) ∣₁
    step' (tagExt {k'} , (m , a) , e) = ext-case k' m a e
    step' (tagShift , m , e) = shift-case m e

    split : ⟨ u ∈ slice n (suc k) ⟩
          ⊎ (Σ[ t ∈ StepTag (suc k) ] Σ[ p ∈ StepPayload n (suc k) t ]
               (stepImage {n} {suc k} t p ≡ u))
          → ∥ T ∥₁
    split (inl h) = slice-inv n k u h
    split (inr pay) = PT.rec squash₁ step' ∣ pay ∣₁
```


<!--en-->
## Terms to levels

Every term denotation lands in the levels, with a computable level witness.
`levelOf` computes the level by term induction: the leaves sit at their fixed
levels (`allTuples` at one, the variable selections at two, the constant-atom
composite at four), the binary nodes at the sum of the children's levels plus
one, and the shift at its child's level plus one. Because the witness is
computable, the statement is untruncated:
`terms-in-levels : (t : KT ⟪ A ⟫ k) → ⟨ ⟦_⟧ᴷ A t ∈ slice A (levelOf t) k ⟩`,
one term induction, each constructor's case the corresponding `slice-in` law.
The binary cases need both children on one shelf, and the two level-merge
lemmas of the kinded-levels section (`slice-addR` and `slice-addL`) lift a
member of any lower level to the summed level on either side of the addition,
so no maximum, no ordering, and no truncation enter the proof: the level
arithmetic is plain addition of the two computable witnesses.
<!--zh-->
## 项到诸层

每个项的指称都落进诸层，且层级见证可计算。`levelOf` 按项归纳计算层级：诸叶坐在各自的固定层级 (元组族在一，变元选择在二，常元原子复合体在四)，二元节点在两个孩子层级之和加一，移位在孩子层级加一。见证可计算，故陈述不截断：`terms-in-levels : (t : KT ⟪ A ⟫ k) → ⟨ ⟦_⟧ᴷ A t ∈ slice A (levelOf t) k ⟩`，一次项归纳，每个构造子的情形就是相应的 `slice-in` 律。二元情形需要两个孩子同处一架，带种类诸层一节的两条层级合并引理 (`slice-addR` 与 `slice-addL`) 把任意低层成员抬到和式层级、落在加号任一侧，故最大、序、截断一概不进证明：层级算术就是两个可计算见证的朴素加法。
<!--/-->

```agda
  levelOf : {k : ℕ} → KT ⟪ A ⟫ k → ℕ
  levelOf allK = 1
  levelOf (selMemK i j) = 2
  levelOf (selEqK i j) = 2
  levelOf (selEqConK i a) = 4
  levelOf (interK s t) = suc (levelOf s + levelOf t)
  levelOf (unionK s t) = suc (levelOf s + levelOf t)
  levelOf (complK t) = suc (1 + levelOf t)
  levelOf (shiftK t) = suc (levelOf t)

  terms-in-levels : {k : ℕ} (t : KT ⟪ A ⟫ k) → ⟨ ⟦_⟧ᴷ A t ∈ slice (levelOf t) k ⟩
  terms-in-levels allK = slice-allTuples-in {n = 0}
  terms-in-levels (selMemK i j) =
    slice-selM-in i j (slice-allTuples-in {n = 0})
  terms-in-levels (selEqK i j) =
    slice-selE-in i j (slice-allTuples-in {n = 0})
  terms-in-levels (selEqConK {zero} () _)
  terms-in-levels (selEqConK {suc k} i a) =
    slice-shiftDown-in
      (slice-selE-in (suc i) zero
        (slice-extendFamily-in {n = 1} {k} a
          (slice-allTuples-in {n = 0})
          (slice-addR 0 1 0 (⁅ κ a ⁆s) (slice-singleton-seed a))))
  terms-in-levels {k} (interK s t) =
    slice-∩-in (slice-addR (levelOf s) (levelOf t) k (⟦_⟧ᴷ A s) (terms-in-levels s))
               (slice-addL (levelOf t) (levelOf s) k (⟦_⟧ᴷ A t) (terms-in-levels t))
  terms-in-levels {k} (unionK s t) =
    slice-∪-in (slice-addR (levelOf s) (levelOf t) k (⟦_⟧ᴷ A s) (terms-in-levels s))
               (slice-addL (levelOf t) (levelOf s) k (⟦_⟧ᴷ A t) (terms-in-levels t))
  terms-in-levels {k} (complK t) =
    slice-∖-in (slice-addR 1 (levelOf t) k (allTuples A k) (slice-allTuples-in {n = 0}))
               (slice-addL (levelOf t) 1 k (⟦_⟧ᴷ A t) (terms-in-levels t))
  terms-in-levels (shiftK t) =
    slice-shiftDown-in (terms-in-levels t)
```


<!--en-->
## The cut theorem

The values-cut of the levels is the definable powerset. `cut-sound` reads one
direction: a member of the arity-one slice at any level has its `values` in
`𝒟ₒ A`, by the invariant (`u ≡ satSet φ`), the values bridge `sat-defSet`
(`values (satSet φ) ≡ defSet φ`), and the sanctioned opening `𝒟ₒ-intro`.
`cut-complete` reads the other, under the chapter's `WithLEM` exactly as
`Terms` scopes its classical half: every `v ∈ 𝒟ₒ A` is `values u` for some
`u` in the arity-one slice of the level `levelOf t` computed from the mirror
term `t`, via the sanctioned opening `𝒟ₒ-inv`, the terms chapter's
`termDef≡Def`, and `terms-in-levels`. The probe's `⊆ allTuples A 1` guard is
absorbed by the kinded design, not carried as a hypothesis: `slice1⊆allTuples`
derives it from the invariant and the satisfaction sets' bound, so the cut is
stated against the slices alone.
<!--zh-->
## 切定理

诸层的取值切口就是可定义幂集。`cut-sound` 读一个方向：第一元数片在任何层级的成员，其 `values` 落在 `𝒟ₒ A` 里，经不变量 (`u ≡ satSet φ`)、取值之桥 `sat-defSet` (`values (satSet φ) ≡ defSet φ`) 与钦定开口 `𝒟ₒ-intro`。`cut-complete` 读另一方向，立于本章的 `WithLEM`，与 `Terms` 划出经典半场的方式一致：每个 `v ∈ 𝒟ₒ A` 都是某个 `u` 的 `values`，而 `u` 坐在由镜像项 `t` 算出的 `levelOf t` 层第一元数片里，经钦定开口 `𝒟ₒ-inv`、项章的 `termDef≡Def` 与 `terms-in-levels`。探针的 `⊆ allTuples A 1` 卫式被带种类设计吸收，不再作为假设携带：`slice1⊆allTuples` 从不变量与满足集的界把它推出来，故切定理只对诸片陈述。
<!--/-->

```agda
  slice1⊆allTuples : {n : ℕ} {u : V ℓ} → ⟨ u ∈ slice n 1 ⟩ → ⟨ u ⊆ allTuples A 1 ⟩
  slice1⊆allTuples {n} {u} hu = PT.rec (snd (u ⊆ allTuples A 1)) go
    (slice-inv n 0 u hu)
    where
    go : Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (u ≡ satSet φ) → ⟨ u ⊆ allTuples A 1 ⟩
    go (φ , e) x hx = ∈∈ₛ {a = x} {b = allTuples A 1} .fst
      (satSet⊆ φ x (subst (λ z → ⟨ x ∈ z ⟩) e (∈∈ₛ {a = x} {b = u} .snd hx)))

  cut-sound : {n : ℕ} {u : V ℓ} → ⟨ u ∈ slice n 1 ⟩ → ⟨ values u ∈ 𝒟ₒ A ⟩
  cut-sound {n} {u} hu = PT.rec (snd (values u ∈ 𝒟ₒ A)) go
    (slice-inv n 0 u hu)
    where
    go : Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (u ≡ satSet φ) → ⟨ values u ∈ 𝒟ₒ A ⟩
    go (φ , e) = 𝒟ₒ-intro A (values u)
      ∣ φ , sym (cong values e ∙ sat-defSet φ) ∣₁

  module WithLEM (lem : LEM (ℓ-suc ℓ)) where
    module TW = Terms.WithLEM A lem

    cut-complete : {v : V ℓ} → ⟨ v ∈ 𝒟ₒ A ⟩
                 → ∥ Σ[ n ∈ ℕ ] Σ[ u ∈ V ℓ ]
                       (⟨ u ∈ slice n 1 ⟩ × (values u ≡ v)) ∥₁
    cut-complete {v} hv = PT.rec squash₁ go (𝒟ₒ-inv A v hv)
      where
      go : Σ[ φ ∈ Formula ⟪ A ⟫ 1 ] (DefOf.defSet A φ ≡ v)
         → ∥ Σ[ n ∈ ℕ ] Σ[ u ∈ V ℓ ]
               (⟨ u ∈ slice n 1 ⟩ × (values u ≡ v)) ∥₁
      go (φ , e) = PT.rec squash₁ build
        (subst (λ z → ⟨ v ∈ z ⟩) (sym TW.termDef≡Def) ∣ φ , e ∣₁)
        where
        build : Σ[ t ∈ KT ⟪ A ⟫ 1 ] (values (⟦_⟧ᴷ A t) ≡ v)
              → ∥ Σ[ n ∈ ℕ ] Σ[ u ∈ V ℓ ]
                    (⟨ u ∈ slice n 1 ⟩ × (values u ≡ v)) ∥₁
        build (t , ev) =
          ∣ levelOf t , ⟦_⟧ᴷ A t , (terms-in-levels t , ev) ∣₁
```


<!--en-->
## Recap

The values generalization `valuesAllTuples`{.Agda}, at every positive arity;
the two selection equations `sat-∈vv-sel`{.Agda} and `sat-≐vv-sel`{.Agda},
reading a selection over a satisfaction set as one more conjunction; the
renaming law `satSet-rename-shift`{.Agda}, saying a satisfaction set survives
a shift of all variables; the forward pinning inclusion `extendFamily-pin`{.Agda},
saying the equality atom at the fresh key cuts the full extension down to the
constant's singleton, and the reverse pinning inclusion
`extendFamily-pin-rev`{.Agda}, saying every member of the singleton extension
records the constant at the fresh key; the full family-extension equation
`extendFamily-pin-eq`{.Agda}, assembled from the renaming law and the two
inclusions in the shape the kinded invariant's constant-atom clause will
consume; and the singleton family `singletons`{.Agda} with its two membership
laws, its `At`-description `singletonsAt`{.Agda} with both readers, and its
constructibility `singletonsL`{.Agda}, the one operation the delivered stock
was missing together with its internal face. Then the meta heart of option B:
the kinded level family `slice`{.Agda}, cumulative in the level, its seed the
singleton family on the arity-zero shelf and every higher shelf bare, with the
`slice-in` law per clause and `slice-out` as the disjunctive inversion, the
shelf discipline that makes the mixed-arity junk impossible by construction;
the kinded invariant `slice-inv`{.Agda}, every member of a positive-arity slice
an arity-`k` satisfaction set by induction on the level, one clause case per
equation, replacing the certificate's honesty induction; terms-to-levels with
the computable witness `levelOf`{.Agda} and `terms-in-levels`{.Agda}, one term
induction against the slice-in laws; and the cut theorem, `cut-sound`{.Agda}
and `cut-complete`{.Agda} under the chapter's `WithLEM`, the values-cut of the
levels equal to the definable powerset, with the probe's arity guard absorbed
by the invariant (`slice1⊆allTuples`{.Agda}). Nothing is deferred.
<!--zh-->
## 小结

取值泛化 `valuesAllTuples`{.Agda}，在每个正元数处；两条选择等式 `sat-∈vv-sel`{.Agda} 与 `sat-≐vv-sel`{.Agda}，把满足集上的一次选择读作一次合取；变量变换律 `satSet-rename-shift`{.Agda}，说满足集经全体变元移位而存活；正向钉住包含 `extendFamily-pin`{.Agda}，说新键处的等词原子把整个扩张裁到常元的单点集，与反向钉住包含 `extendFamily-pin-rev`{.Agda}，说单点扩张的每个成员都在新键处记录常元；完整的族扩张等式 `extendFamily-pin-eq`{.Agda}，由变量变换律与两条包含装配而成，形状即带种类不变量之常元原子子句将要消费的样子；以及单例族 `singletons`{.Agda} 连同它的两条隶属定律、`At` 描述 `singletonsAt`{.Agda} 及其两条读式、与可构造性 `singletonsL`{.Agda}，即已交付存货缺掉的那一个运算连同它的内面。然后是选项 B 的元层心脏：带种类的诸层族 `slice`{.Agda}，随层累积，种子即在第零元数片上的单例族、更高片皆空，连同每条子句一条 `slice-in` 律与作为析取反转的 `slice-out`，即让混合元数垃圾按构造成为不可能的架位纪律；带种类的不变量 `slice-inv`{.Agda}，正元数片的每个成员凭对层级的归纳都是 `k` 元数满足集，每个子句一个情形、每条等式消去一个情形，取代证书的诚实性归纳；带可计算见证 `levelOf`{.Agda} 与 `terms-in-levels`{.Agda} 的项到诸层，一次项归纳对着诸 `slice-in` 律；以及切定理，`cut-sound`{.Agda} 与立于本章 `WithLEM` 的 `cut-complete`{.Agda}，诸层的取值切口等于可定义幂集，探针的元数卫式被不变量吸收 (`slice1⊆allTuples`{.Agda})。本批无遗留。
<!--/-->
