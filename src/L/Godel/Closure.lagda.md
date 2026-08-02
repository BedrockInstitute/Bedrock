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
import FOL.Semantics

module L.Godel.Closure {ℓ : Level} where

open import Base.Classical using ( LEM )

open import FOL.Syntax
  using ( Formula; Term; var; con
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ⊤̇; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-∀∈; δ-∃∈ )
open import FOL.Manipulation.Renaming using ( renameFo )
import FOL.Manipulation.Renaming as Renaming
open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( extensionalV; 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-inl; numeralV≡# )
open import L.Coding.Environment {ℓ} using ( lookup-spec; cons )
open import L.Coding.Environment {ℓ} using ( sucAt-adequate )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ}
  using ( isL; isL-trans; Lset; Lset-mono; Lset-layer; layer-trans
        ; Lset-in; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Ordinal {ℓ} using ( suc-ord; ∈#-elim )
open import L.Axioms.Basic {ℓ} using ( defSet→isL; isL-directed )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Base {ℓ}
  using ( prAt-adequate; ∈pair-introL; ∈pair-introR; ∈pair-elim )
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
        ; tailGraph; tailGraph-in; tailGraph-out
        ; shiftDown; shiftDown-in; shiftDown-out
        ; singleton-self; singleton-in; singleton-out )
open import L.Godel.Tuples {ℓ}
  using ( allTuples; allTuples-suc; tuple; tuple-entry; tuple-extend
        ; tupleTail )
open import L.Godel.InL {ℓ} using ( stageFam; allTuplesL )
open import L.Godel.Definable {ℓ} using ( module Describes )
open import L.Godel.Terms {ℓ}
  using ( KT; allK; selMemK; selEqK; selEqConK; interK; unionK; complK; shiftK
        ; ⟦_⟧ᴷ )
import L.Godel.Terms as Terms

open import Cubical.Data.FinData using ( Fin; toℕ )
open import Cubical.Data.FinData.Properties using ( fromℕ'; toFromId'; toℕ<n )
open import Cubical.Data.Nat.Order using ( _<_ )
open import Cubical.Data.Nat using ( snotz; injSuc )
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
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; module InfinitySet )
module IS = InfinitySet {ℓ}
open IS using ( sucV; #_ )

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV.At (V ℓ) id renaming ( _⊨_ to _⊨v_ )

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

    -- The pair reader and the application atom, restated over any domain
    -- exactly as the bridge chapter restates them: `prAt′` is `L.Coding.Base`'s
    -- `prAt` (definitionally, since the atoms are the same expressions), so its
    -- adequacy is the delivered `prAt-adequate` at the outer satisfaction.
    pairAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
    pairAt′ k i j = (var i ∈̇ var k) ∧̇ ((var j ∈̇ var k)
                ∧̇ (∀̇∈ (var k) ((var zero ≐ var (suc i)) ∨̇ (var zero ≐ var (suc j)))))

    prAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
    prAt′ q u v = (∃̇∈ (var q) (sglAt′ zero (suc u)))
               ∧̇ ((∃̇∈ (var q) (pairAt′ zero (suc u) (suc v)))
               ∧̇ (∀̇∈ (var q) (sglAt′ zero (suc u) ∨̇ pairAt′ zero (suc u) (suc v))))

    appAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Fin n → Formula K n
    appAt′ f x y = ∃̇∈ (var f) (prAt′ zero (suc x) (suc y))

    Δ₀-sglAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (k i : Fin n)
              → Δ₀ (sglAt′ {K = K} k i)
    Δ₀-sglAt′ k i = δ-∧ δ-∈ (δ-∀∈ δ-≐)

    Δ₀-pairAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (k i j : Fin n)
               → Δ₀ (pairAt′ {K = K} k i j)
    Δ₀-pairAt′ k i j = δ-∧ δ-∈ (δ-∧ δ-∈ (δ-∀∈ (δ-∨ δ-≐ δ-≐)))

    Δ₀-prAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (q u v : Fin n)
             → Δ₀ (prAt′ {K = K} q u v)
    Δ₀-prAt′ q u v = δ-∧ (δ-∃∈ (Δ₀-sglAt′ zero (suc u)))
      (δ-∧ (δ-∃∈ (Δ₀-pairAt′ zero (suc u) (suc v)))
           (δ-∀∈ (δ-∨ (Δ₀-sglAt′ zero (suc u)) (Δ₀-pairAt′ zero (suc u) (suc v)))))

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
## The closure is constructible

The step's sett splits by tag, and each tag's fiber is a definable image-set of
the shelves it reads. Seven images are delivered here: the inter image is the
set of intersections of two members of the shelf, the union image the set of
unions, the difference image the set of differences, the tuple image the
singleton of the tuple family, the values image the values of the arity-one
shelf, and the two selections, the membership selection and the equality
selection, at the numeral keys the payload records. Each is constructible by
one `defSet→isL` in the bridge chapter's
idiom: one stage from `isL-directed` (or `stageFam`, where the values image
also needs the zero-key singleton) over the shelves involved, a defining
formula with bounded existentials over the shelf slots and the operation's
delivered description as the body atom, and the extensionality of the
described set against the tag's fiber, whose two directions are the
description's readers. The images live one or two stages above the shelves: a
member of a shelf sits in the stage, an operation result on such members is a
definable subset of the stage, hence a member of the next one (`mkUp`{.Agda},
the bridge chapter's one-step climb restated in the three lines the door
costs), and the image set, being a set of such results, is definable over the
next stage again. The two inclusions of each pin are bounded: the first over
the image itself, the second over the stage (which is a member of the next
stage by the true formula, so the pin stays Δ₀). The selection walks follow
the bridge chapter's SelMem/SelEq idiom with the shelves, the keys and the
stage all abstract module parameters, so the adequacy transfers meet only
variables and the walks never mention `slice` or any concrete `sett`; the
frames apply them at the real shelves only in the two directions of the pin,
with the payload keys read through the numeral memberships. The shift and the
extension images, the step as the finite union of at most nine such images,
and the slice induction are not delivered here: the shift image's deep
seek-sentence satisfaction does not finish within the wall in this
formulation, and the items behind it are blocked until a ruling on that wall.
<!--zh-->
## 闭包可构造

步骤的 `sett` 按标签裂开，而每个标签的纤维都是它所读架位的可定义像集。此处交付七个像：交像是架位两成员之交的集合，并像是两成员之并的集合，差像是两成员之差的集合，元组像是元组族的单点集，取值像是第一元数架位的取值集合，以及两个选择，隶属选择与相等选择，落在载荷所记录的两个数码键处。每个像集凭一次 `defSet→isL` 走桥梁章的行事而可构造：从 `isL-directed` (或在取值像处用 `stageFam`，还需零键单点集) 取一个装下所涉架位的阶段，一条带架位槽上有界存在、以运算已交付描述为体原子的定义公式，再加上被描述集对标签纤维的外延等同，其两个方向正是描述的读式。诸像坐在架位之上的一层或两层：架位成员坐在阶段里，对这种成员施一次运算的结果是阶段的可定义子集，故是下一层的成员 (`mkUp`{.Agda}，桥梁章一步爬升的本地重述，只花那道门的三行)；而像集作为这种结果的集合，又在再下一层上可定义。每条钉子的两个包含皆有界：第一个在像自身上，第二个在阶段上 (阶段经真公式是下一层的成员，故钉子保持 Δ₀)。选择行走桥梁章 SelMem/SelEq 的行事，架位、键与阶段全部作为抽象模块参数，适足搬运只遇到变元，行走从不提 `slice` 或任何具体 `sett`；框架只在钉子的两个方向于真实架位处实例化它们，载荷键经数码隶属读出。移位像与扩张像、作为至多九个像集之有穷并的步骤、以及片归纳此处未交付：移位像的深寻句满足在本表述下越墙而不终，其后的条目被此墙挡住，须待对此墙的裁决。
<!--/-->

```agda
  -- The tag images: the step's sett splits by tag, each fiber the sett of the
  -- tag's own payloads.  The step is their nine-fold union (below).
  interImg : ℕ → ℕ → V ℓ
  interImg n k = sett (StepPayload n k tagInter) (λ p → stepImage {n} {k} tagInter p)

  unionImg : ℕ → ℕ → V ℓ
  unionImg n k = sett (StepPayload n k tagUnion) (λ p → stepImage {n} {k} tagUnion p)

  diffImg : ℕ → ℕ → V ℓ
  diffImg n k = sett (StepPayload n k tagDiff) (λ p → stepImage {n} {k} tagDiff p)

  selMImg : ℕ → ℕ → V ℓ
  selMImg n k = sett (StepPayload n k tagSelM) (λ p → stepImage {n} {k} tagSelM p)

  selEImg : ℕ → ℕ → V ℓ
  selEImg n k = sett (StepPayload n k tagSelE) (λ p → stepImage {n} {k} tagSelE p)

  allImg : ℕ → ℕ → V ℓ
  allImg n k = sett (StepPayload n k tagAll) (λ p → stepImage {n} {k} tagAll p)

  extImg : ℕ → ℕ → V ℓ
  extImg n k = sett (StepPayload n (suc (suc k)) tagExt)
                 (λ p → stepImage {n} {suc (suc k)} tagExt p)

  shiftImg : ℕ → ℕ → V ℓ
  shiftImg n k = sett (StepPayload n k tagShift) (λ p → stepImage {n} {k} tagShift p)

  valuesImg : ℕ → V ℓ
  valuesImg n = sett (StepPayload n 0 tagValues)
                 (λ p → stepImage {n} {0} tagValues p)

  -- The one-step climb, restated after the bridge chapter: a set definable
  -- over a stage is a member of the next one.
  mkUp : (σ x : V ℓ) (Φ : Formula ⟪ Lset σ ⟫ 1) → DefOf.defSet (Lset σ) Φ ≡ x
       → ⟨ x ∈ Lset (sucV σ) ⟩
  mkUp σ x Φ e = Lset-in (sucV σ) σ x (self∈sucV σ) (𝒟ₒ-intro (Lset σ) x ∣ Φ , e ∣₁)

  -- The binary operation results on stage members are definable subsets of the
  -- stage, hence members of the next one: the three two-line formulas z ∈ X
  -- with the connective of the operation, and the membership laws of the
  -- operations chapter for the two inclusions.
  private
    module BinWalk (τ : V ℓ) where
      module DefAτ = DefOf (Lset τ)

      capW : (X Y : V ℓ) → ⟨ X ∈ Lset τ ⟩ → ⟨ Y ∈ Lset τ ⟩
           → ⟨ X ∩ Y ∈ Lset (sucV τ) ⟩
      capW X Y X∈τ Y∈τ = mkUp τ (X ∩ Y) Φ cap≡
        where
        mX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .fst
        qX : ⟪ Lset τ ⟫↪ mX ≡ X
        qX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .snd
        mY = ∈-asFiber {a = Y} {b = Lset τ} Y∈τ .fst
        qY : ⟪ Lset τ ⟫↪ mY ≡ Y
        qY = ∈-asFiber {a = Y} {b = Lset τ} Y∈τ .snd
        Φ : Formula ⟪ Lset τ ⟫ 1
        Φ = (var zero ∈̇ con mX) ∧̇ (var zero ∈̇ con mY)
        cap≡ : DefAτ.defSet Φ ≡ X ∩ Y
        cap≡ = extensionality (DefAτ.defSet Φ) (X ∩ Y) (sub₁ , sub₂)
          where
          sub₁ : ⟨ DefAτ.defSet Φ ⊆ X ∩ Y ⟩
          sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ X ∩ Y))
            (λ { ((m , h) , q) →
              subst (λ w → ⟨ w ∈ₛ X ∩ Y ⟩) q
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m} {b = X ∩ Y} .fst
                  (∩-in {X = X} {Y = Y} {x = ⟪ Lset τ ⟫↪ m}
                    (subst (λ w → ⟨ ⟪ Lset τ ⟫↪ m ∈ w ⟩) qX
                      ((subst ⟨_⟩ (DefAτ.defSet-mem Φ m) ∣ (m , h) , refl ∣₁) .fst))
                    (subst (λ w → ⟨ ⟪ Lset τ ⟫↪ m ∈ w ⟩) qY
                      ((subst ⟨_⟩ (DefAτ.defSet-mem Φ m) ∣ (m , h) , refl ∣₁) .snd)))) })
            (∈∈ₛ {a = z} {b = DefAτ.defSet Φ} .snd z∈ₛ)
          sub₂ : ⟨ X ∩ Y ⊆ DefAτ.defSet Φ ⟩
          sub₂ z z∈ₛ = build
            (∩-out {X = X} {Y = Y} {x = z} (∈∈ₛ {a = z} {b = X ∩ Y} .snd z∈ₛ))
            where
            build : ⟨ z ∈ X ⟩ × ⟨ z ∈ Y ⟩ → ⟨ z ∈ₛ DefAτ.defSet Φ ⟩
            build (hX , hY) =
              subst (λ w → ⟨ w ∈ₛ DefAτ.defSet Φ ⟩) q'
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m'} {b = DefAτ.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (DefAτ.defSet-mem Φ m')) sat))
              where
              z∈τ : ⟨ z ∈ Lset τ ⟩
              z∈τ = layer-trans (Lset-layer τ) {x = X} {y = z} hX X∈τ
              m' = ∈-asFiber {a = z} {b = Lset τ} z∈τ .fst
              q' : ⟪ Lset τ ⟫↪ m' ≡ z
              q' = ∈-asFiber {a = z} {b = Lset τ} z∈τ .snd
              sat : ⟨ (DefAτ.ι m' ∷ []) DefAτ.⊨ᵐ Φ ⟩
              sat = subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qX) hX
                  , subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qY) hY

      unionW : (X Y : V ℓ) → ⟨ X ∈ Lset τ ⟩ → ⟨ Y ∈ Lset τ ⟩
             → ⟨ X ∪ Y ∈ Lset (sucV τ) ⟩
      unionW X Y X∈τ Y∈τ = mkUp τ (X ∪ Y) Φ union≡
        where
        mX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .fst
        qX : ⟪ Lset τ ⟫↪ mX ≡ X
        qX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .snd
        mY = ∈-asFiber {a = Y} {b = Lset τ} Y∈τ .fst
        qY : ⟪ Lset τ ⟫↪ mY ≡ Y
        qY = ∈-asFiber {a = Y} {b = Lset τ} Y∈τ .snd
        Φ : Formula ⟪ Lset τ ⟫ 1
        Φ = (var zero ∈̇ con mX) ∨̇ (var zero ∈̇ con mY)
        union≡ : DefAτ.defSet Φ ≡ X ∪ Y
        union≡ = extensionality (DefAτ.defSet Φ) (X ∪ Y) (sub₁ , sub₂)
          where
          sub₁ : ⟨ DefAτ.defSet Φ ⊆ X ∪ Y ⟩
          sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ X ∪ Y))
            (λ { ((m , h) , q) →
              subst (λ w → ⟨ w ∈ₛ X ∪ Y ⟩) q
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m} {b = X ∪ Y} .fst
                  (PT.rec (snd (⟪ Lset τ ⟫↪ m ∈ X ∪ Y)) (stepm m)
                    (subst ⟨_⟩ (DefAτ.defSet-mem Φ m) ∣ (m , h) , refl ∣₁)))
              })
            (∈∈ₛ {a = z} {b = DefAτ.defSet Φ} .snd z∈ₛ)
            where
            stepm : (m : ⟪ Lset τ ⟫)
                  → ⟨ (DefAτ.ι m ∷ []) DefAτ.⊨ᵐ
                        (var zero ∈̇ con mX) ⟩
                  ⊎ ⟨ (DefAτ.ι m ∷ []) DefAτ.⊨ᵐ
                        (var zero ∈̇ con mY) ⟩
                  → ⟨ ⟪ Lset τ ⟫↪ m ∈ X ∪ Y ⟩
            stepm m (inl hX) = ∪-left {X = X} {Y = Y} {x = ⟪ Lset τ ⟫↪ m}
              (subst (λ w → ⟨ ⟪ Lset τ ⟫↪ m ∈ w ⟩) qX hX)
            stepm m (inr hY) = ∪-right {X = X} {Y = Y} {x = ⟪ Lset τ ⟫↪ m}
              (subst (λ w → ⟨ ⟪ Lset τ ⟫↪ m ∈ w ⟩) qY hY)
          sub₂ : ⟨ X ∪ Y ⊆ DefAτ.defSet Φ ⟩
          sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefAτ.defSet Φ)) build
            (∪-out {X = X} {Y = Y} {x = z} (∈∈ₛ {a = z} {b = X ∪ Y} .snd z∈ₛ))
            where
            build : ⟨ z ∈ X ⟩ ⊎ ⟨ z ∈ Y ⟩ → ⟨ z ∈ₛ DefAτ.defSet Φ ⟩
            build c =
              subst (λ w → ⟨ w ∈ₛ DefAτ.defSet Φ ⟩) q'
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m'} {b = DefAτ.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (DefAτ.defSet-mem Φ m')) sat))
              where
              z∈τ : ⟨ z ∈ Lset τ ⟩
              z∈τ = Sum.rec (λ hX → layer-trans (Lset-layer τ) {x = X} {y = z} hX X∈τ)
                             (λ hY → layer-trans (Lset-layer τ) {x = Y} {y = z} hY Y∈τ) c
              m' = ∈-asFiber {a = z} {b = Lset τ} z∈τ .fst
              q' : ⟪ Lset τ ⟫↪ m' ≡ z
              q' = ∈-asFiber {a = z} {b = Lset τ} z∈τ .snd
              sat : ⟨ (DefAτ.ι m' ∷ []) DefAτ.⊨ᵐ Φ ⟩
              sat = ∣ Sum.map (subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qX))
                              (subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qY)) c ∣₁

      diffW : (X Y : V ℓ) → ⟨ X ∈ Lset τ ⟩ → ⟨ Y ∈ Lset τ ⟩
            → ⟨ X ∖ Y ∈ Lset (sucV τ) ⟩
      diffW X Y X∈τ Y∈τ = mkUp τ (X ∖ Y) Φ diff≡
        where
        mX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .fst
        qX : ⟪ Lset τ ⟫↪ mX ≡ X
        qX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .snd
        mY = ∈-asFiber {a = Y} {b = Lset τ} Y∈τ .fst
        qY : ⟪ Lset τ ⟫↪ mY ≡ Y
        qY = ∈-asFiber {a = Y} {b = Lset τ} Y∈τ .snd
        Φ : Formula ⟪ Lset τ ⟫ 1
        Φ = (var zero ∈̇ con mX) ∧̇ (¬̇ (var zero ∈̇ con mY))
        diff≡ : DefAτ.defSet Φ ≡ X ∖ Y
        diff≡ = extensionality (DefAτ.defSet Φ) (X ∖ Y) (sub₁ , sub₂)
          where
          sub₁ : ⟨ DefAτ.defSet Φ ⊆ X ∖ Y ⟩
          sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ X ∖ Y))
            (λ { ((m , h) , q) →
              subst (λ w → ⟨ w ∈ₛ X ∖ Y ⟩) q
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m} {b = X ∖ Y} .fst
                  (∖-in {X = X} {Y = Y} {x = ⟪ Lset τ ⟫↪ m}
                    (subst (λ w → ⟨ ⟪ Lset τ ⟫↪ m ∈ w ⟩) qX
                      ((subst ⟨_⟩ (DefAτ.defSet-mem Φ m) ∣ (m , h) , refl ∣₁) .fst))
                    (λ hY → (subst ⟨_⟩ (DefAτ.defSet-mem Φ m) ∣ (m , h) , refl ∣₁) .snd
                      (subst (λ w → ⟨ ⟪ Lset τ ⟫↪ m ∈ w ⟩) (sym qY) hY)))) })
            (∈∈ₛ {a = z} {b = DefAτ.defSet Φ} .snd z∈ₛ)
          sub₂ : ⟨ X ∖ Y ⊆ DefAτ.defSet Φ ⟩
          sub₂ z z∈ₛ = build
            (∖-out {X = X} {Y = Y} {x = z} (∈∈ₛ {a = z} {b = X ∖ Y} .snd z∈ₛ))
            where
            build : ⟨ z ∈ X ⟩ × (⟨ z ∈ Y ⟩ → Empty.⊥) → ⟨ z ∈ₛ DefAτ.defSet Φ ⟩
            build (hX , nY) =
              subst (λ w → ⟨ w ∈ₛ DefAτ.defSet Φ ⟩) q'
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m'} {b = DefAτ.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (DefAτ.defSet-mem Φ m')) sat))
              where
              z∈τ : ⟨ z ∈ Lset τ ⟩
              z∈τ = layer-trans (Lset-layer τ) {x = X} {y = z} hX X∈τ
              m' = ∈-asFiber {a = z} {b = Lset τ} z∈τ .fst
              q' : ⟪ Lset τ ⟫↪ m' ≡ z
              q' = ∈-asFiber {a = z} {b = Lset τ} z∈τ .snd
              sat : ⟨ (DefAτ.ι m' ∷ []) DefAτ.⊨ᵐ Φ ⟩
              sat = subst2 (λ u w → ⟨ u ∈ w ⟩) (sym q') (sym qX) hX
                  , (λ hY → nY (subst2 (λ u w → ⟨ u ∈ w ⟩) q' qY hY))

  -- The binary images.  One shared frame per pair of shelves: the stage one
  -- step above the shelf stage, the defining formula with two bounded
  -- existentials over the shelf, the extensionality of the described set
  -- against the tag's fiber, and the constructibility.
  private
    module BinImg (n k : ℕ) (τ : V ℓ) (S∈ : ⟨ slice n k ∈ Lset τ ⟩) where
      Shelf : V ℓ
      Shelf = slice n k

      module DefA = DefOf (Lset (sucV τ))
      module RefA = DefA.Refine (layer-trans (Lset-layer (sucV τ)))

      E : ⟪ Lset (sucV τ) ⟫ → V ℓ
      E m = ⟪ Lset (sucV τ) ⟫↪ m

      Shelf' : ⟨ Shelf ∈ Lset (sucV τ) ⟩
      Shelf' = Lset-mono {sucV τ} {τ} (self∈sucV τ) S∈
      mS = ∈-asFiber {a = Shelf} {b = Lset (sucV τ)} Shelf' .fst
      qS : E mS ≡ Shelf
      qS = ∈-asFiber {a = Shelf} {b = Lset (sucV τ)} Shelf' .snd

      fibers : (W : V ℓ) (hW : ⟨ W ∈ Shelf ⟩)
             → Cubical.Foundations.Equiv.fiber (⟪ Shelf ⟫↪) W
      fibers W hW = ∈-asFiber {a = W} {b = Shelf} hW

      capΦ : Formula ⟪ Lset (sucV τ) ⟫ 1
      capΦ = ∃̇∈ (con mS) (∃̇∈ (con mS)
               ( (∀̇∈ (var (suc (suc zero)))
                    (var zero ∈̇ var (suc (suc zero))
                     ∧̇ var zero ∈̇ var (suc zero)))
               ∧̇ (∀̇∈ (var (suc zero))
                    (var zero ∈̇ var (suc zero)
                     ⇒̇ var zero ∈̇ var (suc (suc (suc zero)))))))

      dCap : Δ₀ capΦ
      dCap = δ-∃∈ (δ-∃∈ (δ-∧ (δ-∀∈ (δ-∧ δ-∈ δ-∈)) (δ-∀∈ (δ-⇒ δ-∈ δ-∈))))

      chain : ∀ m → (E m ∈ DefA.defSet capΦ)
                  ≡ ((E m ∷ []) ⊨v mapFo fst (mapFo DefA.ι capΦ))
      chain m = RefA.abs-defSet capΦ dCap m
              ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                      (mapFo DefA.ι capΦ) (E m ∷ []))

      capOut : (z : V ℓ) → ⟨ z ∈ interImg n k ⟩
             → ∥ Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ q ∈ ⟪ Shelf ⟫ ]
                   (stepImage {n} {k} tagInter (m , q) ≡ z) ∥₁
      capOut z = PT.map λ { ((m , q) , e) → m , q , e }

      capDefSet≡ : DefA.defSet capΦ ≡ interImg n k
      capDefSet≡ = extensionality (DefA.defSet capΦ) (interImg n k) (sub₁ , sub₂)
        where
        fromSat : (m' : ⟪ Lset (sucV τ) ⟫)
                → ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι capΦ) ⟩
                → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                      (stepImage {n} {k} tagInter (mX , mY) ≡ E m') ∥₁
        fromSat m' big = PT.rec squash₁ (λ { (X , hX , w₁) →
          PT.rec squash₁ (λ { (Y , hY , body) →
            finish X Y (subst (λ w → ⟨ X ∈ w ⟩) qS hX)
                   (subst (λ w → ⟨ Y ∈ w ⟩) qS hY)
                   (λ v hv → body .fst v hv)
                   (λ v hXv hYv → body .snd v hXv hYv) }) w₁ }) big
          where
          finish : (X Y : V ℓ) → ⟨ X ∈ Shelf ⟩ → ⟨ Y ∈ Shelf ⟩
                 → ((v : V ℓ) → ⟨ v ∈ E m' ⟩ → ⟨ v ∈ X ⟩ × ⟨ v ∈ Y ⟩)
                 → ((v : V ℓ) → ⟨ v ∈ X ⟩ → ⟨ v ∈ Y ⟩ → ⟨ v ∈ E m' ⟩)
                 → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                       (stepImage {n} {k} tagInter (mX , mY) ≡ E m') ∥₁
          finish X Y hX' hY' h₁ h₂ =
            ∣ pay .fst , pay .snd ∣₁
            where
            e : E m' ≡ X ∩ Y
            e = extensionality (E m') (X ∩ Y) (t₁ , t₂)
              where
              t₁ : ⟨ E m' ⊆ X ∩ Y ⟩
              t₁ v v∈ₛ = ∈∈ₛ {a = v} {b = X ∩ Y} .fst
                (∩-in {X = X} {Y = Y} {x = v}
                  (h₁ v (∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ) .fst)
                  (h₁ v (∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ) .snd))
              t₂ : ⟨ X ∩ Y ⊆ E m' ⟩
              t₂ v v∈ₛ = ∈∈ₛ {a = v} {b = E m'} .fst
                (h₂ v (∩-out {X = X} {Y = Y} {x = v}
                        (∈∈ₛ {a = v} {b = X ∩ Y} .snd v∈ₛ) .fst)
                       (∩-out {X = X} {Y = Y} {x = v}
                        (∈∈ₛ {a = v} {b = X ∩ Y} .snd v∈ₛ) .snd))
            pay : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                    (stepImage {n} {k} tagInter (mX , mY) ≡ E m')
            pay = fibers X hX' .fst
                , (fibers Y hY' .fst
                  , (cong₂ _∩_ (fibers X hX' .snd) (fibers Y hY' .snd) ∙ sym e))

        sub₁ : ⟨ DefA.defSet capΦ ⊆ interImg n k ⟩
        sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ interImg n k)) go
          (∈∈ₛ {a = z} {b = DefA.defSet capΦ} .snd z∈ₛ)
          where
          go : Σ[ p ∈ Σ[ m ∈ ⟪ Lset (sucV τ) ⟫ ] ⟨ DefA.smallSat capΦ m ⟩ ]
                 (E (p .fst) ≡ z)
             → ⟨ z ∈ₛ interImg n k ⟩
          go ((m , h) , q) = PT.rec (snd (z ∈ₛ interImg n k)) build
            (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))
            where
            build : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                      (stepImage {n} {k} tagInter (mX , mY) ≡ E m)
                  → ⟨ z ∈ₛ interImg n k ⟩
            build (mX , mY , e) = subst (λ w → ⟨ w ∈ₛ interImg n k ⟩) (e ∙ q)
              (∈∈ₛ {a = stepImage {n} {k} tagInter (mX , mY)} {b = interImg n k} .fst
                ∣ (mX , mY) , refl ∣₁)

        sub₂ : ⟨ interImg n k ⊆ DefA.defSet capΦ ⟩
        sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet capΦ)) build (capOut z z∈ₛm)
          where
          z∈ₛm : ⟨ z ∈ interImg n k ⟩
          z∈ₛm = ∈∈ₛ {a = z} {b = interImg n k} .snd z∈ₛ
          build : Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ q ∈ ⟪ Shelf ⟫ ]
                    (stepImage {n} {k} tagInter (m , q) ≡ z)
                → ⟨ z ∈ₛ DefA.defSet capΦ ⟩
          build (m , q , e) =
            let X : V ℓ
                X = ⟪ Shelf ⟫↪ m
                Y : V ℓ
                Y = ⟪ Shelf ⟫↪ q
                hX : ⟨ X ∈ Shelf ⟩
                hX = ∈∈ₛ {a = X} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ m)
                hY : ⟨ Y ∈ Shelf ⟩
                hY = ∈∈ₛ {a = Y} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ q)
                z≡ : z ≡ X ∩ Y
                z≡ = sym e
                X∈τ : ⟨ X ∈ Lset τ ⟩
                X∈τ = layer-trans (Lset-layer τ) {x = Shelf} {y = X} hX S∈
                Y∈τ : ⟨ Y ∈ Lset τ ⟩
                Y∈τ = layer-trans (Lset-layer τ) {x = Shelf} {y = Y} hY S∈
                z∈ⁱ : ⟨ z ∈ Lset (sucV τ) ⟩
                z∈ⁱ = subst (λ w → ⟨ w ∈ Lset (sucV τ) ⟩) (sym z≡)
                        (BinWalk.capW τ X Y X∈τ Y∈τ)
                m' = ∈-asFiber {a = z} {b = Lset (sucV τ)} z∈ⁱ .fst
                q' : E m' ≡ z
                q' = ∈-asFiber {a = z} {b = Lset (sucV τ)} z∈ⁱ .snd
                hXˢ : ⟨ X ∈ˢ fst (DefA.ι mS) ⟩
                hXˢ = subst (λ w → ⟨ X ∈ˢ w ⟩) (sym qS) hX
                hYˢ : ⟨ Y ∈ˢ fst (DefA.ι mS) ⟩
                hYˢ = subst (λ w → ⟨ Y ∈ˢ w ⟩) (sym qS) hY
                h₁ : (v : V ℓ) → ⟨ v ∈ E m' ⟩
                    → ⟨ (v ∷ Y ∷ X ∷ E m' ∷ []) ⊨v
                          (var zero ∈̇ var (suc (suc zero))
                           ∧̇ var zero ∈̇ var (suc zero)) ⟩
                h₁ v hv = ( ∩-out {X = X} {Y = Y} {x = v}
                              (subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv) .fst
                          , ∩-out {X = X} {Y = Y} {x = v}
                              (subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv) .snd )
                h₂ : (v : V ℓ) → ⟨ v ∈ X ⟩ → ⟨ v ∈ Y ⟩ → ⟨ v ∈ E m' ⟩
                h₂ v hXv hYv =
                  subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ z≡))
                    (∩-in {X = X} {Y = Y} {x = v} hXv hYv)
                sat : ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι capΦ) ⟩
                sat = ∣ X , (hXˢ , ∣ Y , (hYˢ , (h₁ , h₂)) ∣₁) ∣₁
            in subst (λ w → ⟨ w ∈ₛ DefA.defSet capΦ ⟩) q'
                 (∈∈ₛ {a = E m'} {b = DefA.defSet capΦ} .fst
                   (subst ⟨_⟩ (sym (chain m')) sat))

      unionΦ : Formula ⟪ Lset (sucV τ) ⟫ 1
      unionΦ = ∃̇∈ (con mS) (∃̇∈ (con mS)
               ( (∀̇∈ (var (suc (suc zero)))
                    (var zero ∈̇ var (suc (suc zero))
                     ∨̇ var zero ∈̇ var (suc zero)))
               ∧̇ ( (∀̇∈ (var (suc zero))
                      (var zero ∈̇ var (suc (suc (suc zero)))))
                  ∧̇ (∀̇∈ (var zero)
                      (var zero ∈̇ var (suc (suc (suc zero))))))))

      dUn : Δ₀ unionΦ
      dUn = δ-∃∈ (δ-∃∈ (δ-∧ (δ-∀∈ (δ-∨ δ-∈ δ-∈))
                    (δ-∧ (δ-∀∈ δ-∈) (δ-∀∈ δ-∈))))

      unionChain : ∀ m → (E m ∈ DefA.defSet unionΦ)
                  ≡ ((E m ∷ []) ⊨v mapFo fst (mapFo DefA.ι unionΦ))
      unionChain m = RefA.abs-defSet unionΦ dUn m
                   ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                           (mapFo DefA.ι unionΦ) (E m ∷ []))

      unionOut : (z : V ℓ) → ⟨ z ∈ unionImg n k ⟩
               → ∥ Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ q ∈ ⟪ Shelf ⟫ ]
                     (stepImage {n} {k} tagUnion (m , q) ≡ z) ∥₁
      unionOut z = PT.map λ { ((m , q) , e) → m , q , e }

      unionDefSet≡ : DefA.defSet unionΦ ≡ unionImg n k
      unionDefSet≡ = extensionality (DefA.defSet unionΦ) (unionImg n k) (sub₁ , sub₂)
        where
        fromSat : (m' : ⟪ Lset (sucV τ) ⟫)
                → ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι unionΦ) ⟩
                → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                      (stepImage {n} {k} tagUnion (mX , mY) ≡ E m') ∥₁
        fromSat m' big = PT.rec squash₁ (λ { (X , hX , w₁) →
          PT.rec squash₁ (λ { (Y , hY , body) →
            finish X Y (subst (λ w → ⟨ X ∈ w ⟩) qS hX)
                   (subst (λ w → ⟨ Y ∈ w ⟩) qS hY)
                   (body .fst) (body .snd .fst) (body .snd .snd) }) w₁ }) big
          where
          finish : (X Y : V ℓ) → ⟨ X ∈ Shelf ⟩ → ⟨ Y ∈ Shelf ⟩
                 → ((v : V ℓ) → ⟨ v ∈ E m' ⟩ → ∥ ⟨ v ∈ X ⟩ ⊎ ⟨ v ∈ Y ⟩ ∥₁)
                 → ((v : V ℓ) → ⟨ v ∈ X ⟩ → ⟨ v ∈ E m' ⟩)
                 → ((v : V ℓ) → ⟨ v ∈ Y ⟩ → ⟨ v ∈ E m' ⟩)
                 → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                       (stepImage {n} {k} tagUnion (mX , mY) ≡ E m') ∥₁
          finish X Y hX' hY' h₁ h₂ h₃ = ∣ pay .fst , pay .snd ∣₁
            where
            e : E m' ≡ X ∪ Y
            e = extensionality (E m') (X ∪ Y) (t₁ , t₂)
              where
              t₁ : ⟨ E m' ⊆ X ∪ Y ⟩
              t₁ v v∈ₛ = ∈∈ₛ {a = v} {b = X ∪ Y} .fst
                (PT.rec (snd (v ∈ X ∪ Y)) (go₁ v) (h₁ v v∈E))
                where
                v∈E : ⟨ v ∈ E m' ⟩
                v∈E = ∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ
                go₁ : (v : V ℓ) → ⟨ v ∈ X ⟩ ⊎ ⟨ v ∈ Y ⟩ → ⟨ v ∈ X ∪ Y ⟩
                go₁ v (inl hXv) = ∪-left {X = X} {Y = Y} {x = v} hXv
                go₁ v (inr hYv) = ∪-right {X = X} {Y = Y} {x = v} hYv
              t₂ : ⟨ X ∪ Y ⊆ E m' ⟩
              t₂ v v∈ₛ = ∈∈ₛ {a = v} {b = E m'} .fst
                (PT.rec (snd (v ∈ E m')) (go₂ v)
                  (∪-out {X = X} {Y = Y} {x = v}
                    (∈∈ₛ {a = v} {b = X ∪ Y} .snd v∈ₛ)))
                where
                go₂ : (v : V ℓ) → ⟨ v ∈ X ⟩ ⊎ ⟨ v ∈ Y ⟩ → ⟨ v ∈ E m' ⟩
                go₂ v (inl hXv) = h₂ v hXv
                go₂ v (inr hYv) = h₃ v hYv
            pay : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                    (stepImage {n} {k} tagUnion (mX , mY) ≡ E m')
            pay = fibers X hX' .fst
                , (fibers Y hY' .fst
                  , (cong₂ _∪_ (fibers X hX' .snd) (fibers Y hY' .snd) ∙ sym e))

        sub₁ : ⟨ DefA.defSet unionΦ ⊆ unionImg n k ⟩
        sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ unionImg n k)) go
          (∈∈ₛ {a = z} {b = DefA.defSet unionΦ} .snd z∈ₛ)
          where
          go : Σ[ p ∈ Σ[ m ∈ ⟪ Lset (sucV τ) ⟫ ] ⟨ DefA.smallSat unionΦ m ⟩ ]
                 (E (p .fst) ≡ z)
             → ⟨ z ∈ₛ unionImg n k ⟩
          go ((m , h) , q) = PT.rec (snd (z ∈ₛ unionImg n k)) build
            (fromSat m (subst ⟨_⟩ (unionChain m) ∣ (m , h) , refl ∣₁))
            where
            build : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                      (stepImage {n} {k} tagUnion (mX , mY) ≡ E m)
                  → ⟨ z ∈ₛ unionImg n k ⟩
            build (mX , mY , e) = subst (λ w → ⟨ w ∈ₛ unionImg n k ⟩) (e ∙ q)
              (∈∈ₛ {a = stepImage {n} {k} tagUnion (mX , mY)} {b = unionImg n k} .fst
                ∣ (mX , mY) , refl ∣₁)

        sub₂ : ⟨ unionImg n k ⊆ DefA.defSet unionΦ ⟩
        sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet unionΦ)) build (unionOut z z∈ₛm)
          where
          z∈ₛm : ⟨ z ∈ unionImg n k ⟩
          z∈ₛm = ∈∈ₛ {a = z} {b = unionImg n k} .snd z∈ₛ
          build : Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ q ∈ ⟪ Shelf ⟫ ]
                    (stepImage {n} {k} tagUnion (m , q) ≡ z)
                → ⟨ z ∈ₛ DefA.defSet unionΦ ⟩
          build (m , q , e) =
            let X : V ℓ
                X = ⟪ Shelf ⟫↪ m
                Y : V ℓ
                Y = ⟪ Shelf ⟫↪ q
                hX : ⟨ X ∈ Shelf ⟩
                hX = ∈∈ₛ {a = X} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ m)
                hY : ⟨ Y ∈ Shelf ⟩
                hY = ∈∈ₛ {a = Y} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ q)
                z≡ : z ≡ X ∪ Y
                z≡ = sym e
                X∈τ : ⟨ X ∈ Lset τ ⟩
                X∈τ = layer-trans (Lset-layer τ) {x = Shelf} {y = X} hX S∈
                Y∈τ : ⟨ Y ∈ Lset τ ⟩
                Y∈τ = layer-trans (Lset-layer τ) {x = Shelf} {y = Y} hY S∈
                z∈ⁱ : ⟨ z ∈ Lset (sucV τ) ⟩
                z∈ⁱ = subst (λ w → ⟨ w ∈ Lset (sucV τ) ⟩) (sym z≡)
                        (BinWalk.unionW τ X Y X∈τ Y∈τ)
                m' = ∈-asFiber {a = z} {b = Lset (sucV τ)} z∈ⁱ .fst
                q' : E m' ≡ z
                q' = ∈-asFiber {a = z} {b = Lset (sucV τ)} z∈ⁱ .snd
                hXˢ : ⟨ X ∈ˢ fst (DefA.ι mS) ⟩
                hXˢ = subst (λ w → ⟨ X ∈ˢ w ⟩) (sym qS) hX
                hYˢ : ⟨ Y ∈ˢ fst (DefA.ι mS) ⟩
                hYˢ = subst (λ w → ⟨ Y ∈ˢ w ⟩) (sym qS) hY
                h₁ : (v : V ℓ) → ⟨ v ∈ E m' ⟩
                    → ⟨ (v ∷ Y ∷ X ∷ E m' ∷ []) ⊨v
                          (var zero ∈̇ var (suc (suc zero))
                           ∨̇ var zero ∈̇ var (suc zero)) ⟩
                h₁ v hv = ∪-out {X = X} {Y = Y} {x = v}
                             (subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv)
                h₂ : (v : V ℓ) → ⟨ v ∈ X ⟩
                    → ⟨ (v ∷ Y ∷ X ∷ E m' ∷ []) ⊨v
                          var zero ∈̇ var (suc (suc (suc zero))) ⟩
                h₂ v hXv = subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ z≡))
                  (∪-left {X = X} {Y = Y} {x = v} hXv)
                h₃ : (v : V ℓ) → ⟨ v ∈ Y ⟩
                    → ⟨ (v ∷ Y ∷ X ∷ E m' ∷ []) ⊨v
                          var zero ∈̇ var (suc (suc (suc zero))) ⟩
                h₃ v hYv = subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ z≡))
                  (∪-right {X = X} {Y = Y} {x = v} hYv)
                sat : ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι unionΦ) ⟩
                sat = ∣ X , (hXˢ , ∣ Y , (hYˢ , (h₁ , (h₂ , h₃))) ∣₁) ∣₁
            in subst (λ w → ⟨ w ∈ₛ DefA.defSet unionΦ ⟩) q'
                 (∈∈ₛ {a = E m'} {b = DefA.defSet unionΦ} .fst
                   (subst ⟨_⟩ (sym (unionChain m')) sat))

      diffΦ : Formula ⟪ Lset (sucV τ) ⟫ 1
      diffΦ = ∃̇∈ (con mS) (∃̇∈ (con mS)
               ( (∀̇∈ (var (suc (suc zero)))
                    (var zero ∈̇ var (suc (suc zero))
                     ∧̇ ¬̇ (var zero ∈̇ var (suc zero))))
               ∧̇ (∀̇∈ (var (suc zero))
                    (¬̇ (var zero ∈̇ var (suc zero))
                     ⇒̇ var zero ∈̇ var (suc (suc (suc zero)))))))

      dDi : Δ₀ diffΦ
      dDi = δ-∃∈ (δ-∃∈ (δ-∧ (δ-∀∈ (δ-∧ δ-∈ (δ-¬ δ-∈)))
                    (δ-∀∈ (δ-⇒ (δ-¬ δ-∈) δ-∈))))

      diffChain : ∀ m → (E m ∈ DefA.defSet diffΦ)
                  ≡ ((E m ∷ []) ⊨v mapFo fst (mapFo DefA.ι diffΦ))
      diffChain m = RefA.abs-defSet diffΦ dDi m
                  ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                          (mapFo DefA.ι diffΦ) (E m ∷ []))

      diffOut : (z : V ℓ) → ⟨ z ∈ diffImg n k ⟩
              → ∥ Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ q ∈ ⟪ Shelf ⟫ ]
                    (stepImage {n} {k} tagDiff (m , q) ≡ z) ∥₁
      diffOut z = PT.map λ { ((m , q) , e) → m , q , e }

      diffDefSet≡ : DefA.defSet diffΦ ≡ diffImg n k
      diffDefSet≡ = extensionality (DefA.defSet diffΦ) (diffImg n k) (sub₁ , sub₂)
        where
        fromSat : (m' : ⟪ Lset (sucV τ) ⟫)
                → ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι diffΦ) ⟩
                → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                      (stepImage {n} {k} tagDiff (mX , mY) ≡ E m') ∥₁
        fromSat m' big = PT.rec squash₁ (λ { (X , hX , w₁) →
          PT.rec squash₁ (λ { (Y , hY , body) →
            finish X Y (subst (λ w → ⟨ X ∈ w ⟩) qS hX)
                   (subst (λ w → ⟨ Y ∈ w ⟩) qS hY)
                   (body .fst) (body .snd) }) w₁ }) big
          where
          finish : (X Y : V ℓ) → ⟨ X ∈ Shelf ⟩ → ⟨ Y ∈ Shelf ⟩
                 → ((v : V ℓ) → ⟨ v ∈ E m' ⟩ → ⟨ v ∈ X ⟩ × (⟨ v ∈ Y ⟩ → Empty.⊥))
                 → ((v : V ℓ) → ⟨ v ∈ X ⟩ → (⟨ v ∈ Y ⟩ → Empty.⊥) → ⟨ v ∈ E m' ⟩)
                 → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                       (stepImage {n} {k} tagDiff (mX , mY) ≡ E m') ∥₁
          finish X Y hX' hY' h₁ h₂ = ∣ pay .fst , pay .snd ∣₁
            where
            e : E m' ≡ X ∖ Y
            e = extensionality (E m') (X ∖ Y) (t₁ , t₂)
              where
              t₁ : ⟨ E m' ⊆ X ∖ Y ⟩
              t₁ v v∈ₛ = ∈∈ₛ {a = v} {b = X ∖ Y} .fst
                (∖-in {X = X} {Y = Y} {x = v}
                  (h₁ v (∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ) .fst)
                  (h₁ v (∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ) .snd))
              t₂ : ⟨ X ∖ Y ⊆ E m' ⟩
              t₂ v v∈ₛ = ∈∈ₛ {a = v} {b = E m'} .fst
                (h₂ v (∖-out {X = X} {Y = Y} {x = v}
                        (∈∈ₛ {a = v} {b = X ∖ Y} .snd v∈ₛ) .fst)
                       (∖-out {X = X} {Y = Y} {x = v}
                        (∈∈ₛ {a = v} {b = X ∖ Y} .snd v∈ₛ) .snd))
            pay : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                    (stepImage {n} {k} tagDiff (mX , mY) ≡ E m')
            pay = fibers X hX' .fst
                , (fibers Y hY' .fst
                  , (cong₂ _∖_ (fibers X hX' .snd) (fibers Y hY' .snd) ∙ sym e))

        sub₁ : ⟨ DefA.defSet diffΦ ⊆ diffImg n k ⟩
        sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ diffImg n k)) go
          (∈∈ₛ {a = z} {b = DefA.defSet diffΦ} .snd z∈ₛ)
          where
          go : Σ[ p ∈ Σ[ m ∈ ⟪ Lset (sucV τ) ⟫ ] ⟨ DefA.smallSat diffΦ m ⟩ ]
                 (E (p .fst) ≡ z)
             → ⟨ z ∈ₛ diffImg n k ⟩
          go ((m , h) , q) = PT.rec (snd (z ∈ₛ diffImg n k)) build
            (fromSat m (subst ⟨_⟩ (diffChain m) ∣ (m , h) , refl ∣₁))
            where
            build : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ mY ∈ ⟪ Shelf ⟫ ]
                      (stepImage {n} {k} tagDiff (mX , mY) ≡ E m)
                  → ⟨ z ∈ₛ diffImg n k ⟩
            build (mX , mY , e) = subst (λ w → ⟨ w ∈ₛ diffImg n k ⟩) (e ∙ q)
              (∈∈ₛ {a = stepImage {n} {k} tagDiff (mX , mY)} {b = diffImg n k} .fst
                ∣ (mX , mY) , refl ∣₁)

        sub₂ : ⟨ diffImg n k ⊆ DefA.defSet diffΦ ⟩
        sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet diffΦ)) build (diffOut z z∈ₛm)
          where
          z∈ₛm : ⟨ z ∈ diffImg n k ⟩
          z∈ₛm = ∈∈ₛ {a = z} {b = diffImg n k} .snd z∈ₛ
          build : Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ q ∈ ⟪ Shelf ⟫ ]
                    (stepImage {n} {k} tagDiff (m , q) ≡ z)
                → ⟨ z ∈ₛ DefA.defSet diffΦ ⟩
          build (m , q , e) =
            let X : V ℓ
                X = ⟪ Shelf ⟫↪ m
                Y : V ℓ
                Y = ⟪ Shelf ⟫↪ q
                hX : ⟨ X ∈ Shelf ⟩
                hX = ∈∈ₛ {a = X} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ m)
                hY : ⟨ Y ∈ Shelf ⟩
                hY = ∈∈ₛ {a = Y} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ q)
                z≡ : z ≡ X ∖ Y
                z≡ = sym e
                X∈τ : ⟨ X ∈ Lset τ ⟩
                X∈τ = layer-trans (Lset-layer τ) {x = Shelf} {y = X} hX S∈
                Y∈τ : ⟨ Y ∈ Lset τ ⟩
                Y∈τ = layer-trans (Lset-layer τ) {x = Shelf} {y = Y} hY S∈
                z∈ⁱ : ⟨ z ∈ Lset (sucV τ) ⟩
                z∈ⁱ = subst (λ w → ⟨ w ∈ Lset (sucV τ) ⟩) (sym z≡)
                        (BinWalk.diffW τ X Y X∈τ Y∈τ)
                m' = ∈-asFiber {a = z} {b = Lset (sucV τ)} z∈ⁱ .fst
                q' : E m' ≡ z
                q' = ∈-asFiber {a = z} {b = Lset (sucV τ)} z∈ⁱ .snd
                hXˢ : ⟨ X ∈ˢ fst (DefA.ι mS) ⟩
                hXˢ = subst (λ w → ⟨ X ∈ˢ w ⟩) (sym qS) hX
                hYˢ : ⟨ Y ∈ˢ fst (DefA.ι mS) ⟩
                hYˢ = subst (λ w → ⟨ Y ∈ˢ w ⟩) (sym qS) hY
                h₁ : (v : V ℓ) → ⟨ v ∈ E m' ⟩
                    → ⟨ (v ∷ Y ∷ X ∷ E m' ∷ []) ⊨v
                          (var zero ∈̇ var (suc (suc zero))
                           ∧̇ ¬̇ (var zero ∈̇ var (suc zero))) ⟩
                h₁ v hv = ( ∖-out {X = X} {Y = Y} {x = v}
                              (subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv) .fst
                          , ∖-out {X = X} {Y = Y} {x = v}
                              (subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv) .snd )
                h₂ : (v : V ℓ) → ⟨ v ∈ X ⟩ → (⟨ v ∈ Y ⟩ → Empty.⊥)
                    → ⟨ (v ∷ Y ∷ X ∷ E m' ∷ []) ⊨v
                          var zero ∈̇ var (suc (suc (suc zero))) ⟩
                h₂ v hXv nYv = subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ z≡))
                  (∖-in {X = X} {Y = Y} {x = v} hXv nYv)
                sat : ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι diffΦ) ⟩
                sat = ∣ X , (hXˢ , ∣ Y , (hYˢ , (h₁ , h₂)) ∣₁) ∣₁
            in subst (λ w → ⟨ w ∈ₛ DefA.defSet diffΦ ⟩) q'
                 (∈∈ₛ {a = E m'} {b = DefA.defSet diffΦ} .fst
                   (subst ⟨_⟩ (sym (diffChain m')) sat))

  interImgL : (n k : ℕ) → ⟨ isL (slice n k) ⟩ → ⟨ isL (interImg n k) ⟩
  interImgL n k lS = PT.rec (snd (isL (interImg n k)))
    (λ { (τ , oτ , S∈ , _) →
      defSet→isL (sucV τ) (suc-ord oτ) (interImg n k)
        ∣ BinImg.capΦ n k τ S∈ , BinImg.capDefSet≡ n k τ S∈ ∣₁ })
    (isL-directed (slice n k) (slice n k) lS lS)

  unionImgL : (n k : ℕ) → ⟨ isL (slice n k) ⟩ → ⟨ isL (unionImg n k) ⟩
  unionImgL n k lS = PT.rec (snd (isL (unionImg n k)))
    (λ { (τ , oτ , S∈ , _) →
      defSet→isL (sucV τ) (suc-ord oτ) (unionImg n k)
        ∣ BinImg.unionΦ n k τ S∈ , BinImg.unionDefSet≡ n k τ S∈ ∣₁ })
    (isL-directed (slice n k) (slice n k) lS lS)

  diffImgL : (n k : ℕ) → ⟨ isL (slice n k) ⟩ → ⟨ isL (diffImg n k) ⟩
  diffImgL n k lS = PT.rec (snd (isL (diffImg n k)))
    (λ { (τ , oτ , S∈ , _) →
      defSet→isL (sucV τ) (suc-ord oτ) (diffImg n k)
        ∣ BinImg.diffΦ n k τ S∈ , BinImg.diffDefSet≡ n k τ S∈ ∣₁ })
    (isL-directed (slice n k) (slice n k) lS lS)

  -- The tuple image is the singleton of the tuple family: the payload is a
  -- unit, so the image set is the singleton of the constant image, which is
  -- constructible by the singleton lemma on the delivered tuple-family
  -- constructibility.
  allImg-singleton : (n k : ℕ) → allImg n k ≡ ⁅ allTuples A k ⁆s
  allImg-singleton n k = extensionality (allImg n k) ⁅ allTuples A k ⁆s (t₁ , t₂)
    where
    t₁ : ⟨ allImg n k ⊆ ⁅ allTuples A k ⁆s ⟩
    t₁ x x∈ₛ = ∈∈ₛ {a = x} {b = ⁅ allTuples A k ⁆s} .fst
      (PT.rec (snd (x ∈ ⁅ allTuples A k ⁆s))
        (λ { (u , e) → singleton-in (sym e) })
        (∈∈ₛ {a = x} {b = allImg n k} .snd x∈ₛ))
    t₂ : ⟨ ⁅ allTuples A k ⁆s ⊆ allImg n k ⟩
    t₂ x x∈ₛ = ∈∈ₛ {a = x} {b = allImg n k} .fst
      (subst (λ w → ⟨ w ∈ allImg n k ⟩) (sym x∈⁅⁆) w∈img)
      where
      x∈⁅⁆ : x ≡ allTuples A k
      x∈⁅⁆ = singleton-out {z = allTuples A k} {x = x}
               (∈∈ₛ {a = x} {b = ⁅ allTuples A k ⁆s} .snd x∈ₛ)
      w∈img : ⟨ allTuples A k ∈ allImg n k ⟩
      w∈img = ∣ tt* , refl ∣₁

  allImgL : (n k : ℕ) → ⟨ isL A ⟩ → ⟨ isL (allImg n k) ⟩
  allImgL n k lA = subst (λ w → ⟨ isL w ⟩) (sym (allImg-singleton n k))
    (sglL (allTuplesL A lA k))

  -- The values image: the values of the arity-one shelf.  The stage holds the
  -- shelf and the zero-key singleton, exactly as the bridge chapter's values
  -- lemma needs them; the walk places each values set in the next stage by the
  -- same two-line definability argument, and the image's defining formula pins
  -- the member by the delivered values description's body, bounded.
  private
    module ValImg (n : ℕ) (τ : V ℓ)
      (S∈ : ⟨ slice n 1 ∈ Lset τ ⟩) (K0∈ : ⟨ ⁅ # 0 ⁆s ∈ Lset τ ⟩) where
      Shelf : V ℓ
      Shelf = slice n 1

      module DefA = DefOf (Lset (sucV (sucV τ)))
      module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV τ))))
      Atr = layer-trans (Lset-layer τ)

      E : ⟪ Lset (sucV (sucV τ)) ⟫ → V ℓ
      E m = ⟪ Lset (sucV (sucV τ)) ⟫↪ m

      -- The image formula lives two stages above the shelf stage: the second
      -- inclusion of the pin ranges over the stage itself, which is a member
      -- of the next one (`defSet ⊤̇ ≡ Lset (sucV τ)`, the stage named by the
      -- true formula), so the pin stays bounded and Δ₀.
      σ∈ : ⟨ Lset (sucV τ) ∈ Lset (sucV (sucV τ)) ⟩
      σ∈ = mkUp (sucV τ) (Lset (sucV τ)) ⊤̇
             (DefOf.defSet⊤≡A (Lset (sucV τ)))
      mσ = ∈-asFiber {a = Lset (sucV τ)} {b = Lset (sucV (sucV τ))} σ∈ .fst
      qσ : E mσ ≡ Lset (sucV τ)
      qσ = ∈-asFiber {a = Lset (sucV τ)} {b = Lset (sucV (sucV τ))} σ∈ .snd

      Shelf' : ⟨ Shelf ∈ Lset (sucV (sucV τ)) ⟩
      Shelf' = Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ))
                 (Lset-mono {sucV τ} {τ} (self∈sucV τ) S∈)
      mS = ∈-asFiber {a = Shelf} {b = Lset (sucV (sucV τ))} Shelf' .fst
      qS : E mS ≡ Shelf
      qS = ∈-asFiber {a = Shelf} {b = Lset (sucV (sucV τ))} Shelf' .snd
      K0' : ⟨ ⁅ # 0 ⁆s ∈ Lset (sucV (sucV τ)) ⟩
      K0' = Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ))
              (Lset-mono {sucV τ} {τ} (self∈sucV τ) K0∈)
      mK0' = ∈-asFiber {a = ⁅ # 0 ⁆s} {b = Lset (sucV (sucV τ))} K0' .fst
      qK0' : E mK0' ≡ ⁅ # 0 ⁆s
      qK0' = ∈-asFiber {a = ⁅ # 0 ⁆s} {b = Lset (sucV (sucV τ))} K0' .snd

      fibers : (W : V ℓ) (hW : ⟨ W ∈ Shelf ⟩)
             → Cubical.Foundations.Equiv.fiber (⟪ Shelf ⟫↪) W
      fibers W hW = ∈-asFiber {a = W} {b = Shelf} hW

      -- The body atom: the delivered values description's body, bounded.  A
      -- key is taken from the zero-key singleton, a family member from the
      -- shelf, and the recorded pair is the application atom's witness.
      shape : Formula ⟪ Lset (sucV (sucV τ)) ⟫ (suc (suc (suc zero)))
      shape = ∃̇∈ (con mK0')
                (∃̇∈ (var (suc (suc zero)))
                   (appAt′ zero (suc zero) (suc (suc zero))))

      dShape : Δ₀ shape
      dShape = δ-∃∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAt′ zero (suc (suc zero)) (suc (suc (suc zero))))))

      shapeV : Formula (V ℓ) (suc (suc (suc zero)))
      shapeV = mapFo fst (mapFo DefA.ι shape)

      Φ : Formula ⟪ Lset (sucV (sucV τ)) ⟫ 1
      Φ = ∃̇∈ (con mS)
            ( (∀̇∈ (var (suc zero))
                 (var zero ∈̇ var (suc (suc zero)) ⇒̇ shape))
            ∧̇ (∀̇∈ (con mσ)
                 (shape ⇒̇ var zero ∈̇ var (suc (suc zero)))) )

      dΦ : Δ₀ Φ
      dΦ = δ-∃∈ (δ-∧ (δ-∀∈ (δ-⇒ δ-∈ dShape)) (δ-∀∈ (δ-⇒ dShape δ-∈)))

      chain : ∀ m → (E m ∈ DefA.defSet Φ)
                  ≡ ((E m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ))
      chain m = RefA.abs-defSet Φ dΦ m
              ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                      (mapFo DefA.ι Φ) (E m ∷ []))

      valuesOut : (z : V ℓ) → ⟨ z ∈ valuesImg n ⟩
                → ∥ Σ[ m ∈ ⟪ Shelf ⟫ ] (values (⟪ Shelf ⟫↪ m) ≡ z) ∥₁
      valuesOut z = PT.map λ { (m , e) → m , e }

      -- The walk: each values set of a shelf member is definable over the
      -- stage, hence a member of the next one.
      module ValsWalk (X : V ℓ) (hX : ⟨ X ∈ Shelf ⟩) where
        module DefAτ = DefOf (Lset τ)
        module RefAτ = DefAτ.Refine (layer-trans (Lset-layer τ))
        Atrans = layer-trans (Lset-layer τ)

        Eτ : ⟪ Lset τ ⟫ → V ℓ
        Eτ m = ⟪ Lset τ ⟫↪ m

        f2 : Fin (suc (suc (suc (suc zero))))
        f2 = suc (suc zero)
        f3 : Fin (suc (suc (suc (suc zero))))
        f3 = suc (suc (suc zero))

        X∈τ : ⟨ X ∈ Lset τ ⟩
        X∈τ = Atrans {x = Shelf} {y = X} hX S∈
        mX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .fst
        qX : Eτ mX ≡ X
        qX = ∈-asFiber {a = X} {b = Lset τ} X∈τ .snd
        mK0 = ∈-asFiber {a = ⁅ # 0 ⁆s} {b = Lset τ} K0∈ .fst
        qK0 : Eτ mK0 ≡ ⁅ # 0 ⁆s
        qK0 = ∈-asFiber {a = ⁅ # 0 ⁆s} {b = Lset τ} K0∈ .snd

        ΦVals : Formula ⟪ Lset τ ⟫ 1
        ΦVals = ∃̇∈ (con mK0) (∃̇∈ (con mX) (∃̇∈ (var zero) (prAt′ zero f2 f3)))
        dVals : Δ₀ ΦVals
        dVals = δ-∃∈ (δ-∃∈ (δ-∃∈ (Δ₀-prAt′ zero f2 f3)))
        chainV : ∀ m → (Eτ m ∈ DefAτ.defSet ΦVals)
                      ≡ ((Eτ m ∷ []) ⊨v mapFo fst (mapFo DefAτ.ι ΦVals))
        chainV m = RefAτ.abs-defSet ΦVals dVals m
                 ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                         (mapFo DefAτ.ι ΦVals) (Eτ m ∷ []))
        vals≡ : DefAτ.defSet ΦVals ≡ values X
        vals≡ = extensionality (DefAτ.defSet ΦVals) (values X) (sub₁ , sub₂)
          where
          sub₁ : ⟨ DefAτ.defSet ΦVals ⊆ values X ⟩
          sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ values X))
            (λ { ((m , h) , q) →
              subst (λ w → ⟨ w ∈ₛ values X ⟩) q
                (∈∈ₛ {a = Eτ m} {b = values X} .fst
                  (fromSat m (subst ⟨_⟩ (chainV m) ∣ (m , h) , refl ∣₁))) })
            (∈∈ₛ {a = y} {b = DefAτ.defSet ΦVals} .snd y∈ₛ)
            where
            fromSat : (m : ⟪ Lset τ ⟫)
                    → ⟨ (Eτ m ∷ []) ⊨v mapFo fst (mapFo DefAτ.ι ΦVals) ⟩
                    → ⟨ Eτ m ∈ values X ⟩
            fromSat m big = PT.rec (snd (Eτ m ∈ values X)) (λ { (k , hk , w₁) →
              PT.rec (snd (Eτ m ∈ values X)) (λ { (γ , hγ , w₂) →
                PT.rec (snd (Eτ m ∈ values X)) (λ { (p , hp , s) →
                  values-in {X = X} {γ = γ} {v = Eτ m}
                    (subst (λ z → ⟨ γ ∈ z ⟩) qX hγ)
                    (subst (λ z → ⟨ pr z (Eτ m) ∈ γ ⟩)
                      (singleton-out (subst (λ z → ⟨ k ∈ z ⟩) qK0 hk))
                      (subst (λ z → ⟨ z ∈ γ ⟩)
                        (subst ⟨_⟩ (prAt-adequate zero f2 f3
                          (p ∷ γ ∷ k ∷ Eτ m ∷ [])) s)
                        hp)) })
                w₂ }) w₁ }) big
          sub₂ : ⟨ values X ⊆ DefAτ.defSet ΦVals ⟩
          sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefAτ.defSet ΦVals)) build
            (values-wit {X = X} {v = y} (∈∈ₛ {a = y} {b = values X} .snd y∈ₛ))
            where
            build : Σ[ γ ∈ V ℓ ] (⟨ γ ∈ X ⟩ × ⟨ pr (# 0) y ∈ γ ⟩)
                  → ⟨ y ∈ₛ DefAτ.defSet ΦVals ⟩
            build (γ , hγ , hv) =
              subst (λ w → ⟨ w ∈ₛ DefAτ.defSet ΦVals ⟩) q'
                (∈∈ₛ {a = Eτ m'} {b = DefAτ.defSet ΦVals} .fst
                  (subst ⟨_⟩ (sym (chainV m')) sat))
              where
              y∈A : ⟨ y ∈ Lset τ ⟩
              y∈A = Atrans {x = ⁅ # 0 , y ⁆} {y = y} (∈pair-introR refl)
                      (Atrans {x = pr (# 0) y} {y = ⁅ # 0 , y ⁆} (∈pair-introR refl)
                        (Atrans {x = γ} {y = pr (# 0) y} hv
                          (Atrans {x = X} {y = γ} hγ X∈τ)))
              m' = ∈-asFiber {a = y} {b = Lset τ} y∈A .fst
              q' : Eτ m' ≡ y
              q' = ∈-asFiber {a = y} {b = Lset τ} y∈A .snd
              Ew : V ℓ
              Ew = Eτ m'
              sat : ⟨ (Ew ∷ []) ⊨v mapFo fst (mapFo DefAτ.ι ΦVals) ⟩
              sat = ∣ # 0 , subst (λ z → ⟨ (# 0) ∈ z ⟩) (sym qK0) (singleton-self (# 0))
                  , ∣ γ , subst (λ z → ⟨ γ ∈ z ⟩) (sym qX) hγ
                  , ∣ pr (# 0) Ew , subst (λ z → ⟨ pr (# 0) z ∈ γ ⟩) (sym q') hv
                  , subst ⟨_⟩ (sym (prAt-adequate zero f2 f3
                      (pr (# 0) Ew ∷ γ ∷ # 0 ∷ Ew ∷ []))) refl
                  ∣₁ ∣₁ ∣₁
        valsWalk : ⟨ values X ∈ Lset (sucV τ) ⟩
        valsWalk = mkUp τ (values X) ΦVals vals≡

        valsMember : (v : V ℓ) → ⟨ v ∈ values X ⟩ → ⟨ v ∈ Lset τ ⟩
        valsMember v hv = PT.rec (snd (v ∈ Lset τ)) go
          (values-wit {X = X} {v = v} hv)
          where
          go : Σ[ γ ∈ V ℓ ] (⟨ γ ∈ X ⟩ × ⟨ pr (# 0) v ∈ γ ⟩) → ⟨ v ∈ Lset τ ⟩
          go (γ , hγ , hpr) =
            Atrans {x = ⁅ # 0 , v ⁆} {y = v} (∈pair-introR refl)
              (Atrans {x = pr (# 0) v} {y = ⁅ # 0 , v ⁆} (∈pair-introR refl)
                (Atrans {x = γ} {y = pr (# 0) v} hpr
                  (Atrans {x = X} {y = γ} hγ X∈τ)))

      -- The two directions of the pin: the shape satisfaction reads into the
      -- values membership by the delivered laws, and fills back from them.
      shape-read : (X v z : V ℓ) (hX : ⟨ X ∈ Shelf ⟩)
                 → ⟨ (v ∷ X ∷ z ∷ []) ⊨v shapeV ⟩ → ⟨ v ∈ values X ⟩
      shape-read X v z hX h = PT.rec (snd (v ∈ values X)) (λ { (k0 , hk0 , w₁) →
        PT.rec (snd (v ∈ values X)) (λ { (g , hg , w₂) →
          PT.rec (snd (v ∈ values X)) (λ { (q , hq , r) →
            let hk0' : ⟨ k0 ∈ ⁅ # 0 ⁆s ⟩
                hk0' = subst (λ w → ⟨ k0 ∈ w ⟩) qK0' hk0
                pEq : q ≡ pr (# 0) v
                pEq = subst ⟨_⟩ (prAt-adequate zero (suc (suc zero)) (suc (suc (suc zero)))
                        (q ∷ g ∷ k0 ∷ v ∷ X ∷ z ∷ [])) r
                    ∙ cong (λ w → pr w v) (singleton-out hk0')
                hv : ⟨ pr (# 0) v ∈ g ⟩
                hv = subst (λ w → ⟨ w ∈ g ⟩) pEq hq
            in values-in {X = X} {γ = g} {v = v} hg hv })
          w₂ }) w₁ }) h

      shape-fill : (X v z : V ℓ) (hX : ⟨ X ∈ Shelf ⟩)
                 → ⟨ v ∈ values X ⟩ → ⟨ (v ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
      shape-fill X v z hX hv = PT.rec (snd ((v ∷ X ∷ z ∷ []) ⊨v shapeV)) build
        (values-wit {X = X} {v = v} hv)
        where
        build : Σ[ γ ∈ V ℓ ] (⟨ γ ∈ X ⟩ × ⟨ pr (# 0) v ∈ γ ⟩)
              → ⟨ (v ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
        build (γ , hγ , hpr) =
          ∣ # 0 , ( k0∈
                  , ∣ γ , ( hγ
                          , ∣ pr (# 0) v , ( hpr , prAt-sat ) ∣₁ ) ∣₁ )
          ∣₁
          where
          k0∈ : ⟨ (# 0) ∈ˢ fst (DefA.ι mK0') ⟩
          k0∈ = subst (λ w → ⟨ (# 0) ∈ˢ w ⟩) (sym qK0') (singleton-self (# 0))
          prAt-sat : ⟨ (pr (# 0) v ∷ γ ∷ # 0 ∷ v ∷ X ∷ z ∷ []) ⊨v
                        prAt′ zero (suc (suc zero)) (suc (suc (suc zero))) ⟩
          prAt-sat = subst ⟨_⟩ (sym (prAt-adequate zero (suc (suc zero)) (suc (suc (suc zero)))
                        (pr (# 0) v ∷ γ ∷ # 0 ∷ v ∷ X ∷ z ∷ []))) refl

      valDefSet≡ : DefA.defSet Φ ≡ valuesImg n
      valDefSet≡ = extensionality (DefA.defSet Φ) (valuesImg n) (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet Φ ⊆ valuesImg n ⟩
        sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ valuesImg n)) go
          (∈∈ₛ {a = z} {b = DefA.defSet Φ} .snd z∈ₛ)
          where
          go : Σ[ p ∈ Σ[ m ∈ ⟪ Lset (sucV (sucV τ)) ⟫ ] ⟨ DefA.smallSat Φ m ⟩ ]
                 (E (p .fst) ≡ z)
             → ⟨ z ∈ₛ valuesImg n ⟩
          go ((m , h) , q) = PT.rec (snd (z ∈ₛ valuesImg n)) build
            (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))
            where
            fromSat : (m' : ⟪ Lset (sucV (sucV τ)) ⟫)
                    → ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
                    → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] (values (⟪ Shelf ⟫↪ mX) ≡ E m') ∥₁
            fromSat m' big = PT.rec squash₁ (λ { (X , hX , body) →
              finish X (subst (λ w → ⟨ X ∈ w ⟩) qS hX)
                     (λ v hv → body .fst v hv hv)
                     (λ v vσ hshape → body .snd v vσ hshape) }) big
              where
              finish : (X : V ℓ) (hX' : ⟨ X ∈ Shelf ⟩)
                     → ((v : V ℓ) → ⟨ v ∈ E m' ⟩ → ⟨ (v ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩)
                     → ((v : V ℓ) → ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                        → ⟨ (v ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩ → ⟨ v ∈ E m' ⟩)
                     → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] (values (⟪ Shelf ⟫↪ mX) ≡ E m') ∥₁
              finish X hX' h₁ h₂ =
                ∣ fibers X hX' .fst , (cong values (fibers X hX' .snd) ∙ sym e) ∣₁
                where
                e : E m' ≡ values X
                e = extensionality (E m') (values X) (t₁ , t₂)
                  where
                  t₁ : ⟨ E m' ⊆ values X ⟩
                  t₁ v v∈ₛ = ∈∈ₛ {a = v} {b = values X} .fst
                    (shape-read X v (E m') hX' (h₁ v v∈E))
                    where
                    v∈E : ⟨ v ∈ E m' ⟩
                    v∈E = ∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ
                  t₂ : ⟨ values X ⊆ E m' ⟩
                  t₂ v v∈ₛ = ∈∈ₛ {a = v} {b = E m'} .fst
                    (h₂ v (subst (λ w → ⟨ v ∈ˢ w ⟩) (sym qσ)
                             (Lset-mono {sucV τ} {τ} (self∈sucV τ)
                               (ValsWalk.valsMember X hX' v v∈X)))
                           (shape-fill X v (E m') hX' v∈X))
                    where
                    v∈X : ⟨ v ∈ values X ⟩
                    v∈X = ∈∈ₛ {a = v} {b = values X} .snd v∈ₛ
            build : Σ[ mX ∈ ⟪ Shelf ⟫ ] (values (⟪ Shelf ⟫↪ mX) ≡ E m)
                  → ⟨ z ∈ₛ valuesImg n ⟩
            build (mX , e) = subst (λ w → ⟨ w ∈ₛ valuesImg n ⟩) (e ∙ q)
              (∈∈ₛ {a = values (⟪ Shelf ⟫↪ mX)} {b = valuesImg n} .fst
                ∣ mX , refl ∣₁)

        sub₂ : ⟨ valuesImg n ⊆ DefA.defSet Φ ⟩
        sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet Φ)) build (valuesOut z z∈ₛm)
          where
          z∈ₛm : ⟨ z ∈ valuesImg n ⟩
          z∈ₛm = ∈∈ₛ {a = z} {b = valuesImg n} .snd z∈ₛ
          build : Σ[ m ∈ ⟪ Shelf ⟫ ] (values (⟪ Shelf ⟫↪ m) ≡ z)
                → ⟨ z ∈ₛ DefA.defSet Φ ⟩
          build (m , e) =
            let X : V ℓ
                X = ⟪ Shelf ⟫↪ m
                hX : ⟨ X ∈ Shelf ⟩
                hX = ∈∈ₛ {a = X} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ m)
                z≡ : z ≡ values X
                z≡ = sym e
                z∈ⁱ : ⟨ z ∈ Lset (sucV (sucV τ)) ⟩
                z∈ⁱ = subst (λ w → ⟨ w ∈ Lset (sucV (sucV τ)) ⟩) (sym z≡)
                        (Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ))
                          (ValsWalk.valsWalk X hX))
                m' = ∈-asFiber {a = z} {b = Lset (sucV (sucV τ))} z∈ⁱ .fst
                q' : E m' ≡ z
                q' = ∈-asFiber {a = z} {b = Lset (sucV (sucV τ))} z∈ⁱ .snd
                hXˢ : ⟨ X ∈ˢ fst (DefA.ι mS) ⟩
                hXˢ = subst (λ w → ⟨ X ∈ˢ w ⟩) (sym qS) hX
                h₁ : (v : V ℓ) → ⟨ v ∈ E m' ⟩ → ⟨ v ∈ E m' ⟩
                    → ⟨ (v ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩
                h₁ v hv = λ _ → shape-fill X v (E m') hX
                  (subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv)
                h₂ : (v : V ℓ) → ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                    → ⟨ (v ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩ → ⟨ v ∈ E m' ⟩
                h₂ v vσ hshape = subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ z≡))
                  (shape-read X v (E m') hX hshape)
                sat : ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
                sat = ∣ X , (hXˢ , (h₁ , h₂)) ∣₁
            in subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
                 (∈∈ₛ {a = E m'} {b = DefA.defSet Φ} .fst
                   (subst ⟨_⟩ (sym (chain m')) sat))

  valuesImgL : (n : ℕ) → ⟨ isL (slice n 1) ⟩ → ⟨ isL (valuesImg n) ⟩
  valuesImgL n lS = PT.rec (snd (isL (valuesImg n)))
    (λ { (τ , oτ , mem2) →
      defSet→isL (sucV (sucV τ)) (suc-ord (suc-ord oτ)) (valuesImg n)
        ∣ ValImg.Φ n τ (mem2 zero) (mem2 (suc zero))
        , ValImg.valDefSet≡ n τ (mem2 zero) (mem2 (suc zero)) ∣₁ })
    (stageFam 2 fam famL)
    where
    zeroL : ⟨ isL (# 0) ⟩
    zeroL = subst (λ w → ⟨ isL w ⟩) (numeralL-fst 0) (numeralL 0 .snd)
    fam : Fin 2 → V ℓ
    fam zero = slice n 1
    fam (suc zero) = ⁅ # 0 ⁆s
    famL : (i : Fin 2) → ⟨ isL (fam i) ⟩
    famL zero = lS
    famL (suc zero) = sglL zeroL

  -- The numerals are von Neumann ordinals: the numeral for m is a member of
  -- the numeral for n exactly when m < n.  The two directions (this one and
  -- `∈#-elim`) read the payload indices out of the key memberships.
  num∈num : (m n : ℕ) → m < n → ⟨ # m ∈ # n ⟩
  num∈num m zero (k , p) = Empty.rec (snotz (subst (λ w → w ≡ zero) (+-suc k m) p))
  num∈num m (suc n) (zero , p) =
    subst (λ w → ⟨ w ∈ # (suc n) ⟩) (sym (cong (λ q → # q) (injSuc p))) (self∈sucV (# n))
  num∈num m (suc n) (suc k , p) = ∈sucV-inl (num∈num m n (k , injSuc p))

  -- walk places the selection of an abstract family and two abstract key sets
  -- in the next stage by the one-step climb, and the frame applies it at the
  -- real shelves only at the lemma-assembly level.
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

  -- The shift's seek machinery, restated after the bridge chapter: the
  -- successor atom says one set is the von Neumann successor of another, and
  -- the seek sentence says a surveyed member is the tail of a recorded pair,
  -- with the pair chain bound inside the member.  The two readers move the
  -- sentence between the satisfaction and the pair equation.
  private
    sucAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Formula K n
    sucAt′ i j = (var i ∈̇ var j)
              ∧̇ ((∀̇∈ (var i) (var zero ∈̇ var (suc j)))
              ∧̇ (∀̇∈ (var j) ((var zero ∈̇ var (suc i)) ∨̇ (var zero ≐ var (suc i)))))

    Δ₀-sucAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} (i j : Fin n)
              → Δ₀ (sucAt′ {K = K} i j)
    Δ₀-sucAt′ i j = δ-∧ δ-∈ (δ-∧ (δ-∀∈ δ-∈) (δ-∀∈ (δ-∨ δ-∈ δ-≐)))

    tailBody : {ℓ' : Level} {K : Type ℓ'} {m : ℕ}
             → Formula K (suc (suc (suc (suc (suc (suc (suc m)))))))
    tailBody = prAt′ f5 f3 f1 ∧̇ (sucAt′ zero f3 ∧̇ prAt′ f6 zero f1)

    tailSeek : {ℓ' : Level} {K : Type ℓ'} {m : ℕ} → Term K (suc m) → Formula K (suc m)
    tailSeek B = ∃̇∈ B (∃̇∈ (var zero) (∃̇∈ (var zero)
                   (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var f2) tailBody)))))

    Δ₀-tailSeek : {ℓ' : Level} {K : Type ℓ'} {m : ℕ} (B : Term K (suc m))
                → Δ₀ (tailSeek B)
    Δ₀-tailSeek B = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
      (δ-∧ (Δ₀-prAt′ f5 f3 f1)
           (δ-∧ (Δ₀-sucAt′ zero f3) (Δ₀-prAt′ f6 zero f1))))))))

    seekOut : {n : ℕ} (B : Term (V ℓ) (suc n)) (δ : (V ℓ) SemV.^ (suc n))
            → ⟨ δ ⊨v tailSeek B ⟩
            → ∥ Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                ((⟦ var zero ⟧ δ ≡ pr a v) × ⟨ pr (sucV a) v ∈ ⟦ B ⟧ δ ⟩) ∥₁
    seekOut B δ =
      PT.rec PT.squash₁ (λ { (p , hp , w₁) →
      PT.rec PT.squash₁ (λ { (d₁ , hd₁ , w₂) →
      PT.rec PT.squash₁ (λ { (s , hs , w₃) →
      PT.rec PT.squash₁ (λ { (d₂ , hd₂ , w₄) →
      PT.rec PT.squash₁ (λ { (v , hv , w₅) →
      PT.rec PT.squash₁ (λ { (a , ha , (e₁ , e₂ , e₃)) →
        ∣ a , v
        , subst ⟨_⟩ (prAt-adequate f6 zero f1
            (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₃
        , subst (λ w → ⟨ w ∈ ⟦ B ⟧ δ ⟩)
            (subst ⟨_⟩ (prAt-adequate f5 f3 f1
              (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₁
             ∙ cong (λ w → pr w v)
                 (subst ⟨_⟩ (sucAt-adequate zero f3
                   (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ δ)) e₂))
            hp ∣₁ })
      w₅ }) w₄ }) w₃ }) w₂ }) w₁ })

    seekIn : {n : ℕ} (B : Term (V ℓ) (suc n)) (δ : (V ℓ) SemV.^ (suc n)) (a v : V ℓ)
           → ⟦ var zero ⟧ δ ≡ pr a v → ⟨ pr (sucV a) v ∈ ⟦ B ⟧ δ ⟩
           → ⟨ δ ⊨v tailSeek B ⟩
    seekIn B δ a v e h =
      ∣ pr (sucV a) v , h
      , ∣ ⁅ sucV a ⁆s , ∈pair-introL refl
      , ∣ sucV a , singleton-self (sucV a)
      , ∣ ⁅ sucV a , v ⁆ , ∈pair-introR refl
      , ∣ v , ∈pair-introR refl
      , ∣ a , self∈sucV a
      , ( subst ⟨_⟩ (sym (prAt-adequate f5 f3 f1 env′)) refl
        , subst ⟨_⟩ (sym (sucAt-adequate zero f3 env′)) refl
        , subst ⟨_⟩ (sym (prAt-adequate f6 zero f1 env′)) e )
      ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      env′ : (V ℓ) SemV.^ (suc (suc (suc (suc (suc (suc (suc _)))))))
      env′ = a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s ∷ pr (sucV a) v ∷ δ

  -- The staging moves restated after the bridge chapter: the unordered pair
  -- of two stage members climbs one stage, the Kuratowski pair climbs two,
  -- and the tail graph of a stage member climbs three, by its seek sentence.
  pairUp : (σ : V ℓ) {x y : V ℓ} → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
         → ⟨ ⁅ x , y ⁆ ∈ Lset (sucV σ) ⟩
  pairUp σ {x} {y} x∈ y∈ = mkUp σ ⁅ x , y ⁆ Φ defSet≡
    where
    module DefA = DefOf (Lset σ)
    module RefA = DefA.Refine (layer-trans (Lset-layer σ))
    mx = ∈-asFiber {a = x} {b = Lset σ} x∈ .fst
    qx : ⟪ Lset σ ⟫↪ mx ≡ x
    qx = ∈-asFiber {a = x} {b = Lset σ} x∈ .snd
    my = ∈-asFiber {a = y} {b = Lset σ} y∈ .fst
    qy : ⟪ Lset σ ⟫↪ my ≡ y
    qy = ∈-asFiber {a = y} {b = Lset σ} y∈ .snd
    Φ : Formula ⟪ Lset σ ⟫ 1
    Φ = (var zero ≐ con mx) ∨̇ (var zero ≐ con my)
    defSet≡ : DefA.defSet Φ ≡ ⁅ x , y ⁆
    defSet≡ = extensionality (DefA.defSet Φ) ⁅ x , y ⁆ (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Φ ⊆ ⁅ x , y ⁆ ⟩
      sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ⁅ x , y ⁆))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ ⁅ x , y ⁆ ⟩) q
            (∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = ⁅ x , y ⁆} .fst
              (mem m (subst ⟨_⟩ (DefA.defSet-mem Φ m) ∣ (m , h) , refl ∣₁))) })
        (∈∈ₛ {a = z} {b = DefA.defSet Φ} .snd z∈ₛ)
        where
        mem : (m : ⟪ Lset σ ⟫)
            → ⟨ (⟪ Lset σ ⟫↪ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
            → ⟨ ⟪ Lset σ ⟫↪ m ∈ ⁅ x , y ⁆ ⟩
        mem m = PT.rec (snd (⟪ Lset σ ⟫↪ m ∈ ⁅ x , y ⁆))
          λ { (inl e) → ∈pair-introL (e ∙ qx)
            ; (inr e) → ∈pair-introR (e ∙ qy) }
      sub₂ : ⟨ ⁅ x , y ⁆ ⊆ DefA.defSet Φ ⟩
      sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet Φ))
        (λ { (inl e) →
              subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) (qx ∙ sym e)
                (∈∈ₛ {a = ⟪ Lset σ ⟫↪ mx} {b = DefA.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (DefA.defSet-mem Φ mx)) ∣ inl refl ∣₁))
           ; (inr e) →
              subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) (qy ∙ sym e)
                (∈∈ₛ {a = ⟪ Lset σ ⟫↪ my} {b = DefA.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (DefA.defSet-mem Φ my)) ∣ inr refl ∣₁)) })
        (∈pair-elim (∈∈ₛ {a = z} {b = ⁅ x , y ⁆} .snd z∈ₛ))

  prUp : (σ : V ℓ) {x y : V ℓ} → ⟨ x ∈ Lset σ ⟩ → ⟨ y ∈ Lset σ ⟩
       → ⟨ pr x y ∈ Lset (sucV (sucV σ)) ⟩
  prUp σ {x} {y} x∈ y∈ = pairUp (sucV σ) (sglUp-mini σ x∈) (pairUp σ x∈ y∈)

  tailStage : (σ : V ℓ) {z : V ℓ} → ⟨ z ∈ Lset σ ⟩
            → ⟨ tailGraph z ∈ Lset (sucV (sucV (sucV σ))) ⟩
  tailStage σ {z} z∈ = mkUp (sucV (sucV σ)) (tailGraph z) Ψ defSet≡
    where
    Atr = layer-trans (Lset-layer σ)
    module DefA = DefOf (Lset (sucV (sucV σ)))
    module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV σ))))
    z∈² : ⟨ z ∈ Lset (sucV (sucV σ)) ⟩
    z∈² = Lset-mono {sucV (sucV σ)} {sucV σ} (self∈sucV (sucV σ))
            (Lset-mono {sucV σ} {σ} (self∈sucV σ) z∈)
    mz = ∈-asFiber {a = z} {b = Lset (sucV (sucV σ))} z∈² .fst
    qz : ⟪ Lset (sucV (sucV σ)) ⟫↪ mz ≡ z
    qz = ∈-asFiber {a = z} {b = Lset (sucV (sucV σ))} z∈² .snd

    Ψ : Formula ⟪ Lset (sucV (sucV σ)) ⟫ 1
    Ψ = tailSeek (con mz)

    chain : ∀ m → (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∈ DefA.defSet Ψ)
                ≡ ((⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Ψ))
    chain m = RefA.abs-defSet Ψ (Δ₀-tailSeek (con mz)) m
            ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                    (mapFo DefA.ι Ψ) (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []))

    defSet≡ : DefA.defSet Ψ ≡ tailGraph z
    defSet≡ = extensionality (DefA.defSet Ψ) (tailGraph z) (sub₁ , sub₂)
      where
      sub₁ : ⟨ DefA.defSet Ψ ⊆ tailGraph z ⟩
      sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ tailGraph z))
        (λ { ((m , h) , q) →
          subst (λ w → ⟨ w ∈ₛ tailGraph z ⟩) q
            (mem m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁)) })
        (∈∈ₛ {a = y} {b = DefA.defSet Ψ} .snd y∈ₛ)
        where
        mem : (m : ⟪ Lset (sucV (sucV σ)) ⟫)
            → ⟨ (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Ψ) ⟩
            → ⟨ ⟪ Lset (sucV (sucV σ)) ⟫↪ m ∈ₛ tailGraph z ⟩
        mem m sat = PT.rec (snd (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∈ₛ tailGraph z))
          (λ { (a , v , e , h) →
            ∈∈ₛ {a = ⟪ Lset (sucV (sucV σ)) ⟫↪ m} {b = tailGraph z} .fst
              (subst (λ w → ⟨ w ∈ tailGraph z ⟩) (sym e)
                (tailGraph-in
                  (subst (λ w → ⟨ pr (sucV a) v ∈ w ⟩) qz h))) })
          (seekOut (con (⟪ Lset (sucV (sucV σ)) ⟫↪ mz))
            (⟪ Lset (sucV (sucV σ)) ⟫↪ m ∷ []) sat)
      sub₂ : ⟨ tailGraph z ⊆ DefA.defSet Ψ ⟩
      sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet Ψ)) build
        (tailGraph-out {w = z} {z = y} (∈∈ₛ {a = y} {b = tailGraph z} .snd y∈ₛ))
        where
        build : Σ[ a ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ pr (sucV a) v ∈ z ⟩ × (y ≡ pr a v))
              → ⟨ y ∈ₛ DefA.defSet Ψ ⟩
        build (a , v , h , e) =
          subst (λ w → ⟨ w ∈ₛ DefA.defSet Ψ ⟩) q'
            (∈∈ₛ {a = ⟪ Lset (sucV (sucV σ)) ⟫↪ m'} {b = DefA.defSet Ψ} .fst
              (subst ⟨_⟩ (sym (chain m'))
                (seekIn (con (⟪ Lset (sucV (sucV σ)) ⟫↪ mz))
                  (⟪ Lset (sucV (sucV σ)) ⟫↪ m' ∷ []) a v (q' ∙ e)
                  (subst (λ w → ⟨ pr (sucV a) v ∈ w ⟩) (sym qz) h))))
          where
          prz∈ : ⟨ pr (sucV a) v ∈ Lset σ ⟩
          prz∈ = Atr {x = z} {y = pr (sucV a) v} h z∈
          a∈ : ⟨ a ∈ Lset σ ⟩
          a∈ = Atr {x = sucV a} {y = a} (self∈sucV a)
            (Atr {x = ⁅ sucV a ⁆s} {y = sucV a} (singleton-self (sucV a))
              (Atr {x = pr (sucV a) v} {y = ⁅ sucV a ⁆s} (∈pair-introL refl) prz∈))
          v∈ : ⟨ v ∈ Lset σ ⟩
          v∈ = Atr {x = ⁅ sucV a , v ⁆} {y = v} (∈pair-introR refl)
            (Atr {x = pr (sucV a) v} {y = ⁅ sucV a , v ⁆} (∈pair-introR refl) prz∈)
          y∈² : ⟨ y ∈ Lset (sucV (sucV σ)) ⟩
          y∈² = subst (λ w → ⟨ w ∈ Lset (sucV (sucV σ)) ⟩) (sym e)
            (prUp σ a∈ v∈)
          m' = ∈-asFiber {a = y} {b = Lset (sucV (sucV σ))} y∈² .fst
          q' : ⟪ Lset (sucV (sucV σ)) ⟫↪ m' ≡ y
          q' = ∈-asFiber {a = y} {b = Lset (sucV (sucV σ))} y∈² .snd

  -- The selection walks, in the bridge chapter's SelMem/SelEq idiom but with
  -- the shelves, the keys and the stage all abstract module parameters: the
  -- formulas and the fromSat readers never mention `slice`, `satSet`, or any
  -- concrete `sett`, so the adequacy transfers meet only variables.  Each
  private
    module SelWalk (X Ka Kb τ : V ℓ)
      (X∈ : ⟨ X ∈ Lset τ ⟩) (Ka∈ : ⟨ Ka ∈ Lset τ ⟩) (Kb∈ : ⟨ Kb ∈ Lset τ ⟩) where

      module DefA = DefOf (Lset τ)
      Atrans = layer-trans (Lset-layer τ)
      module RefA = DefA.Refine Atrans

      mX = ∈-asFiber {a = X} {b = Lset τ} X∈ .fst
      qX : ⟪ Lset τ ⟫↪ mX ≡ X
      qX = ∈-asFiber {a = X} {b = Lset τ} X∈ .snd
      mKa = ∈-asFiber {a = Ka} {b = Lset τ} Ka∈ .fst
      qKa : ⟪ Lset τ ⟫↪ mKa ≡ Ka
      qKa = ∈-asFiber {a = Ka} {b = Lset τ} Ka∈ .snd
      mKb = ∈-asFiber {a = Kb} {b = Lset τ} Kb∈ .fst
      qKb : ⟪ Lset τ ⟫↪ mKb ≡ Kb
      qKb = ∈-asFiber {a = Kb} {b = Lset τ} Kb∈ .snd

      Φ : Formula ⟪ Lset τ ⟫ 1
      Φ = (var zero ∈̇ con mX)
       ∧̇ (∃̇∈ (con mKa) (∃̇∈ (con mKb)
            (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var zero)
              (∃̇∈ (var f5) (∃̇∈ (var zero) (∃̇∈ (var zero)
                (prAt′ f5 f7 f3 ∧̇ (prAt′ f2 f6 zero ∧̇ (var f3 ∈̇ var zero)))))))))))

      dΦ : Δ₀ Φ
      dΦ = δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
             (δ-∧ (Δ₀-prAt′ f5 f7 f3) (δ-∧ (Δ₀-prAt′ f2 f6 zero) δ-∈))))))))))

      chain : ∀ m → (⟪ Lset τ ⟫↪ m ∈ DefA.defSet Φ)
                  ≡ ((⟪ Lset τ ⟫↪ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ))
      chain m = RefA.abs-defSet Φ dΦ m
              ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                      (mapFo DefA.ι Φ) (⟪ Lset τ ⟫↪ m ∷ []))

      defSet≡ : DefA.defSet Φ ≡ selectMember X Ka Kb
      defSet≡ = extensionality (DefA.defSet Φ) (selectMember X Ka Kb) (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet Φ ⊆ selectMember X Ka Kb ⟩
        sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ selectMember X Ka Kb))
          (λ { ((m , h) , q) →
            subst (λ w → ⟨ w ∈ₛ selectMember X Ka Kb ⟩) q
              (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m} {b = selectMember X Ka Kb} .fst
                (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
          (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
          where
          fromSat : (m : ⟪ Lset τ ⟫)
                  → ⟨ (⟪ Lset τ ⟫↪ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
                  → ⟨ ⟪ Lset τ ⟫↪ m ∈ selectMember X Ka Kb ⟩
          fromSat m (hXm , big) =
            PT.rec tgt (λ { (a , ha , w₁) →
            PT.rec tgt (λ { (b , hb , w₂) →
            PT.rec tgt (λ { (p , hp , w₃) →
            PT.rec tgt (λ { (d , hd , w₄) →
            PT.rec tgt (λ { (u , hu , w₅) →
            PT.rec tgt (λ { (p' , hp' , w₆) →
            PT.rec tgt (λ { (d' , hd' , w₇) →
            PT.rec tgt (λ { (v , hv , (sa , sb , huv)) →
              selectMember-in {X = X} {Ka = Ka} {Kb = Kb} {w = ⟪ Lset τ ⟫↪ m}
                {a = a} {b = b} {u = u} {v = v}
                (subst (λ z → ⟨ ⟪ Lset τ ⟫↪ m ∈ z ⟩) qX hXm)
                (subst (λ z → ⟨ a ∈ z ⟩) qKa ha)
                (subst (λ z → ⟨ b ∈ z ⟩) qKb hb)
                (subst (λ z → ⟨ z ∈ ⟪ Lset τ ⟫↪ m ⟩)
                  (subst ⟨_⟩ (prAt-adequate f5 f7 f3
                    (v ∷ d' ∷ p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset τ ⟫↪ m ∷ [])) sa)
                  hp)
                (subst (λ z → ⟨ z ∈ ⟪ Lset τ ⟫↪ m ⟩)
                  (subst ⟨_⟩ (prAt-adequate f2 f6 zero
                    (v ∷ d' ∷ p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset τ ⟫↪ m ∷ [])) sb)
                  hp')
                huv })
              w₇ }) w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ }) big
            where
            tgt = snd (⟪ Lset τ ⟫↪ m ∈ selectMember X Ka Kb)
        sub₂ : ⟨ selectMember X Ka Kb ⊆ DefA.defSet Φ ⟩
        sub₂ y y∈ₛ = mem (∈∈ₛ {a = y} {b = selectMember X Ka Kb} .snd y∈ₛ)
          where
          mem : ⟨ y ∈ selectMember X Ka Kb ⟩ → ⟨ y ∈ₛ DefA.defSet Φ ⟩
          mem hy = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build
            (selectMember-wit {X = X} {Ka = Ka} {Kb = Kb} {w = y} hy)
            where
            y∈X : ⟨ y ∈ X ⟩
            y∈X = selectMember-sub {X = X} {Ka = Ka} {Kb = Kb} {w = y} hy
            y∈A : ⟨ y ∈ Lset τ ⟩
            y∈A = Atrans {x = X} {y = y} y∈X X∈
            m' = ∈-asFiber {a = y} {b = Lset τ} y∈A .fst
            q' : ⟪ Lset τ ⟫↪ m' ≡ y
            q' = ∈-asFiber {a = y} {b = Lset τ} y∈A .snd
            build : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                    ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩
                    × ⟨ pr a u ∈ y ⟩ × ⟨ pr b v ∈ y ⟩ × ⟨ u ∈ v ⟩ )
                  → ⟨ y ∈ₛ DefA.defSet Φ ⟩
            build (a , b , u , v , ha , hb , hau , hbv , huv) =
              subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m'} {b = DefA.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (chain m')) sat))
              where
              E : V ℓ
              E = ⟪ Lset τ ⟫↪ m'
              env : (V ℓ) SemV.^ 9
              env = v ∷ ⁅ b , v ⁆ ∷ pr b v ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a ∷ E ∷ []
              sat : ⟨ (E ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
              sat = subst (λ z → ⟨ E ∈ z ⟩) (sym qX)
                      (subst (λ z → ⟨ z ∈ X ⟩) (sym q') y∈X)
                  , ∣ a , subst (λ z → ⟨ a ∈ z ⟩) (sym qKa) ha
                  , ∣ b , subst (λ z → ⟨ b ∈ z ⟩) (sym qKb) hb
                  , ∣ pr a u , subst (λ z → ⟨ pr a u ∈ z ⟩) (sym q') hau
                  , ∣ ⁅ a , u ⁆ , ∈pair-introR refl
                  , ∣ u , ∈pair-introR refl
                  , ∣ pr b v , subst (λ z → ⟨ pr b v ∈ z ⟩) (sym q') hbv
                  , ∣ ⁅ b , v ⁆ , ∈pair-introR refl
                  , ∣ v , ∈pair-introR refl
                  , ( subst ⟨_⟩ (sym (prAt-adequate f5 f7 f3 env)) refl
                    , subst ⟨_⟩ (sym (prAt-adequate f2 f6 zero env)) refl
                    , huv )
                  ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

      walk : ⟨ selectMember X Ka Kb ∈ Lset (sucV τ) ⟩
      walk = Lset-in (sucV τ) τ (selectMember X Ka Kb) (self∈sucV τ)
              (𝒟ₒ-intro (Lset τ) (selectMember X Ka Kb) ∣ Φ , defSet≡ ∣₁)

    module SelEWalk (X Ka Kb τ : V ℓ)
      (X∈ : ⟨ X ∈ Lset τ ⟩) (Ka∈ : ⟨ Ka ∈ Lset τ ⟩) (Kb∈ : ⟨ Kb ∈ Lset τ ⟩) where

      module DefA = DefOf (Lset τ)
      Atrans = layer-trans (Lset-layer τ)
      module RefA = DefA.Refine Atrans

      mX = ∈-asFiber {a = X} {b = Lset τ} X∈ .fst
      qX : ⟪ Lset τ ⟫↪ mX ≡ X
      qX = ∈-asFiber {a = X} {b = Lset τ} X∈ .snd
      mKa = ∈-asFiber {a = Ka} {b = Lset τ} Ka∈ .fst
      qKa : ⟪ Lset τ ⟫↪ mKa ≡ Ka
      qKa = ∈-asFiber {a = Ka} {b = Lset τ} Ka∈ .snd
      mKb = ∈-asFiber {a = Kb} {b = Lset τ} Kb∈ .fst
      qKb : ⟪ Lset τ ⟫↪ mKb ≡ Kb
      qKb = ∈-asFiber {a = Kb} {b = Lset τ} Kb∈ .snd

      Φ : Formula ⟪ Lset τ ⟫ 1
      Φ = (var zero ∈̇ con mX)
       ∧̇ (∃̇∈ (con mKa) (∃̇∈ (con mKb)
            (∃̇∈ (var f2) (∃̇∈ (var zero) (∃̇∈ (var zero)
              (∃̇∈ (var f5) (prAt′ f3 f5 f1 ∧̇ prAt′ zero f4 f1)))))))

      dΦ : Δ₀ Φ
      dΦ = δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
             (δ-∧ (Δ₀-prAt′ f3 f5 f1) (Δ₀-prAt′ zero f4 f1))))))))

      chain : ∀ m → (⟪ Lset τ ⟫↪ m ∈ DefA.defSet Φ)
                  ≡ ((⟪ Lset τ ⟫↪ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ))
      chain m = RefA.abs-defSet Φ dΦ m
              ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                      (mapFo DefA.ι Φ) (⟪ Lset τ ⟫↪ m ∷ []))

      defSet≡ : DefA.defSet Φ ≡ selectEqual X Ka Kb
      defSet≡ = extensionality (DefA.defSet Φ) (selectEqual X Ka Kb) (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet Φ ⊆ selectEqual X Ka Kb ⟩
        sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ selectEqual X Ka Kb))
          (λ { ((m , h) , q) →
            subst (λ w → ⟨ w ∈ₛ selectEqual X Ka Kb ⟩) q
              (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m} {b = selectEqual X Ka Kb} .fst
                (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
          (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
          where
          fromSat : (m : ⟪ Lset τ ⟫)
                  → ⟨ (⟪ Lset τ ⟫↪ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
                  → ⟨ ⟪ Lset τ ⟫↪ m ∈ selectEqual X Ka Kb ⟩
          fromSat m (hXm , big) =
            PT.rec tgt (λ { (a , ha , w₁) →
            PT.rec tgt (λ { (b , hb , w₂) →
            PT.rec tgt (λ { (p , hp , w₃) →
            PT.rec tgt (λ { (d , hd , w₄) →
            PT.rec tgt (λ { (u , hu , w₅) →
            PT.rec tgt (λ { (p' , hp' , (sa , sb)) →
              selectEqual-in {X = X} {Ka = Ka} {Kb = Kb} {w = ⟪ Lset τ ⟫↪ m}
                {a = a} {b = b} {u = u}
                (subst (λ z → ⟨ ⟪ Lset τ ⟫↪ m ∈ z ⟩) qX hXm)
                (subst (λ z → ⟨ a ∈ z ⟩) qKa ha)
                (subst (λ z → ⟨ b ∈ z ⟩) qKb hb)
                (subst (λ z → ⟨ z ∈ ⟪ Lset τ ⟫↪ m ⟩)
                  (subst ⟨_⟩ (prAt-adequate f3 f5 f1
                    (p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset τ ⟫↪ m ∷ [])) sa)
                  hp)
                (subst (λ z → ⟨ z ∈ ⟪ Lset τ ⟫↪ m ⟩)
                  (subst ⟨_⟩ (prAt-adequate zero f4 f1
                    (p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ ⟪ Lset τ ⟫↪ m ∷ [])) sb)
                  hp') })
              w₅ }) w₄ }) w₃ }) w₂ }) w₁ }) big
            where
            tgt = snd (⟪ Lset τ ⟫↪ m ∈ selectEqual X Ka Kb)
        sub₂ : ⟨ selectEqual X Ka Kb ⊆ DefA.defSet Φ ⟩
        sub₂ y y∈ₛ = mem (∈∈ₛ {a = y} {b = selectEqual X Ka Kb} .snd y∈ₛ)
          where
          mem : ⟨ y ∈ selectEqual X Ka Kb ⟩ → ⟨ y ∈ₛ DefA.defSet Φ ⟩
          mem hy = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build
            (selectEqual-wit {X = X} {Ka = Ka} {Kb = Kb} {w = y} hy)
            where
            y∈X : ⟨ y ∈ X ⟩
            y∈X = selectEqual-sub {X = X} {Ka = Ka} {Kb = Kb} {w = y} hy
            y∈A : ⟨ y ∈ Lset τ ⟩
            y∈A = Atrans {x = X} {y = y} y∈X X∈
            m' = ∈-asFiber {a = y} {b = Lset τ} y∈A .fst
            q' : ⟪ Lset τ ⟫↪ m' ≡ y
            q' = ∈-asFiber {a = y} {b = Lset τ} y∈A .snd
            build : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ]
                    ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩
                    × ⟨ pr a u ∈ y ⟩ × ⟨ pr b u ∈ y ⟩ )
                  → ⟨ y ∈ₛ DefA.defSet Φ ⟩
            build (a , b , u , ha , hb , hau , hbu) =
              subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
                (∈∈ₛ {a = ⟪ Lset τ ⟫↪ m'} {b = DefA.defSet Φ} .fst
                  (subst ⟨_⟩ (sym (chain m')) sat))
              where
              E : V ℓ
              E = ⟪ Lset τ ⟫↪ m'
              env : (V ℓ) SemV.^ 7
              env = pr b u ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a ∷ E ∷ []
              sat : ⟨ (E ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
              sat = subst (λ z → ⟨ E ∈ z ⟩) (sym qX)
                      (subst (λ z → ⟨ z ∈ X ⟩) (sym q') y∈X)
                  , ∣ a , subst (λ z → ⟨ a ∈ z ⟩) (sym qKa) ha
                  , ∣ b , subst (λ z → ⟨ b ∈ z ⟩) (sym qKb) hb
                  , ∣ pr a u , subst (λ z → ⟨ pr a u ∈ z ⟩) (sym q') hau
                  , ∣ ⁅ a , u ⁆ , ∈pair-introR refl
                  , ∣ u , ∈pair-introR refl
                  , ∣ pr b u , subst (λ z → ⟨ pr b u ∈ z ⟩) (sym q') hbu
                  , ( subst ⟨_⟩ (sym (prAt-adequate f3 f5 f1 env)) refl
                    , subst ⟨_⟩ (sym (prAt-adequate zero f4 f1 env)) refl )
                  ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

      walk : ⟨ selectEqual X Ka Kb ∈ Lset (sucV τ) ⟩
      walk = Lset-in (sucV τ) τ (selectEqual X Ka Kb) (self∈sucV τ)
              (𝒟ₒ-intro (Lset τ) (selectEqual X Ka Kb) ∣ Φ , defSet≡ ∣₁)

  -- The selection image frame, shared by the two selections.  The stage holds
  -- the shelf, the numeral (the key set of the arity, whose members are the
  -- payload keys), and the singletons of those keys.  The defining formula
  -- ranges over the shelf and over the singletons of the numeral's members,
  -- with the selection description's membership shape as the body atom and
  -- the pin's second inclusion bounded over the stage; the walk is applied at
  -- the real shelves only here, in the two directions of the pin.
  private
    module SelMImg (n k : ℕ) (τ : V ℓ)
      (S∈ : ⟨ slice n k ∈ Lset τ ⟩)
      (K∈ : ⟨ # k ∈ Lset τ ⟩)
      (KS∈ : (i : Fin k) → ⟨ ⁅ # (toℕ i) ⁆s ∈ Lset τ ⟩) where
      Shelf : V ℓ
      Shelf = slice n k

      module DefA = DefOf (Lset (sucV (sucV τ)))
      module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV τ))))
      Atr = layer-trans (Lset-layer τ)

      E : ⟪ Lset (sucV (sucV τ)) ⟫ → V ℓ
      E m = ⟪ Lset (sucV (sucV τ)) ⟫↪ m

      -- The stage one step above the shelf stage, as a member of the image
      -- stage: the pin's second inclusion is bounded over it.
      σ∈ : ⟨ Lset (sucV τ) ∈ Lset (sucV (sucV τ)) ⟩
      σ∈ = mkUp (sucV τ) (Lset (sucV τ)) ⊤̇ (DefOf.defSet⊤≡A (Lset (sucV τ)))
      mσ = ∈-asFiber {a = Lset (sucV τ)} {b = Lset (sucV (sucV τ))} σ∈ .fst
      qσ : E mσ ≡ Lset (sucV τ)
      qσ = ∈-asFiber {a = Lset (sucV τ)} {b = Lset (sucV (sucV τ))} σ∈ .snd

      -- The shelf and the key family (the singletons of the numeral's
      -- members) in the image stage.
      Shelf' : ⟨ Shelf ∈ Lset (sucV (sucV τ)) ⟩
      Shelf' = Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ))
                 (Lset-mono {sucV τ} {τ} (self∈sucV τ) S∈)
      mS = ∈-asFiber {a = Shelf} {b = Lset (sucV (sucV τ))} Shelf' .fst
      qS : E mS ≡ Shelf
      qS = ∈-asFiber {a = Shelf} {b = Lset (sucV (sucV τ))} Shelf' .snd

      Keys∈ : ⟨ singletons (# k) ∈ Lset (sucV (sucV τ)) ⟩
      Keys∈ = Lset-in (sucV (sucV τ)) (sucV τ) (singletons (# k)) (self∈sucV (sucV τ))
                (𝒟ₒ-intro (Lset (sucV τ)) (singletons (# k))
                  ∣ SglFam.Φ (# k) τ K∈ , SglFam.defSet≡ (# k) τ K∈ ∣₁)
      mKeys = ∈-asFiber {a = singletons (# k)} {b = Lset (sucV (sucV τ))} Keys∈ .fst
      qKeys : E mKeys ≡ singletons (# k)
      qKeys = ∈-asFiber {a = singletons (# k)} {b = Lset (sucV (sucV τ))} Keys∈ .snd

      -- The membership shape, the delivered selection description's body: a
      -- member of the selection is a member of the family holding, at the two
      -- keys, two recorded values in membership, with the pair chain bound
      -- inside the member.  Over the stage the keys are bound, not constants.
      shape : Formula ⟪ Lset (sucV (sucV τ)) ⟫ (suc (suc (suc (suc (suc zero)))))
      shape = (var zero ∈̇ var (suc (suc (suc zero))))
            ∧̇ (∃̇∈ (var (suc (suc zero)))
                 (∃̇∈ (var (suc (suc zero)))
                   (∃̇∈ (var (suc (suc zero)))
                     (∃̇∈ (var zero)
                       (∃̇∈ (var zero)
                         (∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
                           (∃̇∈ (var zero)
                             (∃̇∈ (var zero)
                               ((prAt′ f5 f7 f3)
                                ∧̇ ((prAt′ f2 f6 zero) ∧̇ (var f3 ∈̇ var zero)))))))))))

      dShape : Δ₀ shape
      dShape = δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
                 (δ-∧ (Δ₀-prAt′ f5 f7 f3) (δ-∧ (Δ₀-prAt′ f2 f6 zero) δ-∈))))))))))

      shapeV : Formula (V ℓ) (suc (suc (suc (suc (suc zero)))))
      shapeV = mapFo fst (mapFo DefA.ι shape)

      ΦM : Formula ⟪ Lset (sucV (sucV τ)) ⟫ 1
      ΦM = ∃̇∈ (con mS) (∃̇∈ (con mKeys) (∃̇∈ (con mKeys)
             ( (∀̇∈ (var (suc (suc (suc zero)))) shape)
             ∧̇ (∀̇∈ (con mσ)
                  (shape ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))))) )))

      dΦM : Δ₀ ΦM
      dΦM = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (δ-∀∈ dShape)
             (δ-∀∈ (δ-⇒ dShape δ-∈)))))

      chain : ∀ m → (E m ∈ DefA.defSet ΦM)
                  ≡ ((E m ∷ []) ⊨v mapFo fst (mapFo DefA.ι ΦM))
      chain m = RefA.abs-defSet ΦM dΦM m
              ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                      (mapFo DefA.ι ΦM) (E m ∷ []))

      -- The two readers of the description, at the stage: the satisfaction of
      -- the shape is the membership in the selection, and back.
      shape-read : (X Ka Kb v z : V ℓ)
                 → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
                 → ⟨ v ∈ selectMember X Ka Kb ⟩
      shape-read X Ka Kb v z h = PT.rec (snd (v ∈ selectMember X Ka Kb))
        (λ { (a , ha , w₁) → PT.rec (snd (v ∈ selectMember X Ka Kb))
          (λ { (b , hb , w₂) → PT.rec (snd (v ∈ selectMember X Ka Kb))
            (λ { (p , hp , w₃) → PT.rec (snd (v ∈ selectMember X Ka Kb))
              (λ { (d , hd , w₄) → PT.rec (snd (v ∈ selectMember X Ka Kb))
                (λ { (u , hu , w₅) → PT.rec (snd (v ∈ selectMember X Ka Kb))
                  (λ { (p' , hp' , w₆) → PT.rec (snd (v ∈ selectMember X Ka Kb))
                    (λ { (d' , hd' , w₇) → PT.rec (snd (v ∈ selectMember X Ka Kb))
                      (λ { (w , hw , (sa , sb , huv)) →
                        selectMember-in {X = X} {Ka = Ka} {Kb = Kb} {w = v}
                          {a = a} {b = b} {u = u} {v = w}
                          (h .fst)
                          ha hb
                          (subst (λ q → ⟨ q ∈ v ⟩)
                            (subst ⟨_⟩ (prAt-adequate f5 f7 f3
                              (w ∷ d' ∷ p' ∷ u ∷ d ∷ p ∷ b ∷ a
                                ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ [])) sa)
                            hp)
                          (subst (λ q → ⟨ q ∈ v ⟩)
                            (subst ⟨_⟩ (prAt-adequate f2 f6 zero
                              (w ∷ d' ∷ p' ∷ u ∷ d ∷ p ∷ b ∷ a
                                ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ [])) sb)
                            hp')
                          huv })
                      w₇ }) w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ }) (h .snd)

      shape-fill : (X Ka Kb v z : V ℓ)
                 → ⟨ v ∈ selectMember X Ka Kb ⟩
                 → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
      shape-fill X Ka Kb v z hv = PT.rec
        (snd ((v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV)) build
        (selectMember-wit {X = X} {Ka = Ka} {Kb = Kb} {w = v} hv)
        where
        build : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ] Σ[ w ∈ V ℓ ]
                ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩
                × ⟨ pr a u ∈ v ⟩ × ⟨ pr b w ∈ v ⟩ × ⟨ u ∈ w ⟩ )
              → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
        build (a , b , u , w , ha , hb , hau , hbv , huv) =
          selectMember-sub {X = X} {Ka = Ka} {Kb = Kb} {w = v} hv
          , ∣ a , ha
          , ∣ b , hb
          , ∣ pr a u , hau
          , ∣ ⁅ a , u ⁆ , ∈pair-introR refl
          , ∣ u , ∈pair-introR refl
          , ∣ pr b w , hbv
          , ∣ ⁅ b , w ⁆ , ∈pair-introR refl
          , ∣ w , ∈pair-introR refl
          , ( subst ⟨_⟩ (sym (prAt-adequate f5 f7 f3
                (w ∷ ⁅ b , w ⁆ ∷ pr b w ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a
                  ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []))) refl
            , subst ⟨_⟩ (sym (prAt-adequate f2 f6 zero
                (w ∷ ⁅ b , w ⁆ ∷ pr b w ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a
                  ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []))) refl
            , huv )
          ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

      selMOut : (z : V ℓ) → ⟨ z ∈ selMImg n k ⟩
              → ∥ Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                   (stepImage {n} {k} tagSelM (m , i , j) ≡ z) ∥₁
      selMOut z = PT.map λ { ((m , (i , j)) , e) → m , i , j , e }

      selMDefSet≡ : DefA.defSet ΦM ≡ selMImg n k
      selMDefSet≡ = extensionality (DefA.defSet ΦM) (selMImg n k) (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet ΦM ⊆ selMImg n k ⟩
        sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ selMImg n k)) go
          (∈∈ₛ {a = z} {b = DefA.defSet ΦM} .snd z∈ₛ)
          where
          go : Σ[ p ∈ Σ[ m ∈ ⟪ Lset (sucV (sucV τ)) ⟫ ] ⟨ DefA.smallSat ΦM m ⟩ ]
                 (E (p .fst) ≡ z)
             → ⟨ z ∈ₛ selMImg n k ⟩
          go ((m , h) , q) = PT.rec (snd (z ∈ₛ selMImg n k)) build
            (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))
            where
            build : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                      (stepImage {n} {k} tagSelM (mX , i , j) ≡ E m)
                  → ⟨ z ∈ₛ selMImg n k ⟩
            build (mX , i , j , e) = subst (λ w → ⟨ w ∈ₛ selMImg n k ⟩) (e ∙ q)
              (∈∈ₛ {a = stepImage {n} {k} tagSelM (mX , i , j)} {b = selMImg n k} .fst
                ∣ (mX , i , j) , refl ∣₁)
            fromSat : (m' : ⟪ Lset (sucV (sucV τ)) ⟫)
                    → ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι ΦM) ⟩
                    → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                         (stepImage {n} {k} tagSelM (mX , i , j) ≡ E m') ∥₁
            fromSat m' big = PT.rec squash₁ (λ { (X , hX , w₁) →
              PT.rec squash₁ (λ { (Ka , hKa , w₂) →
              PT.rec squash₁ (λ { (Kb , hKb , body) →
                finish X Ka Kb (subst (λ w → ⟨ X ∈ w ⟩) qS hX)
                       (subst (λ w → ⟨ Ka ∈ w ⟩) qKeys hKa)
                       (subst (λ w → ⟨ Kb ∈ w ⟩) qKeys hKb)
                       (body .fst) (body .snd) }) w₂ }) w₁ }) big
              where
              finish : (X Ka Kb : V ℓ) → ⟨ X ∈ Shelf ⟩ → ⟨ Ka ∈ singletons (# k) ⟩
                     → ⟨ Kb ∈ singletons (# k) ⟩
                     → ((v : V ℓ) → ⟨ v ∈ E m' ⟩
                        → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩)
                     → ((v : V ℓ) → ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                        → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩
                        → ⟨ v ∈ E m' ⟩)
                     → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                          (stepImage {n} {k} tagSelM (mX , i , j) ≡ E m') ∥₁
              finish X Ka Kb hX' hKa' hKb' h₁ h₂ =
                PT.rec squash₁ (λ { (a , ha , eqa) →
                PT.rec squash₁ (λ { (b , hb , eqb) →
                  goKey a ha eqa b hb eqb }) (singletons-out {X = # k} {w = Kb} hKb') })
                (singletons-out {X = # k} {w = Ka} hKa')
                where
                goKey : (a : V ℓ) → ⟨ a ∈ # k ⟩ → Ka ≡ ⁅ a ⁆s
                      → (b : V ℓ) → ⟨ b ∈ # k ⟩ → Kb ≡ ⁅ b ⁆s
                      → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                           (stepImage {n} {k} tagSelM (mX , i , j) ≡ E m') ∥₁
                eSel : E m' ≡ selectMember X Ka Kb
                eSel = extensionality (E m') (selectMember X Ka Kb) (t₁ , t₂)
                  where
                  t₁ : ⟨ E m' ⊆ selectMember X Ka Kb ⟩
                  t₁ v v∈ₛ = ∈∈ₛ {a = v} {b = selectMember X Ka Kb} .fst
                    (shape-read X Ka Kb v (E m')
                      (h₁ v (∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ)))
                  t₂ : ⟨ selectMember X Ka Kb ⊆ E m' ⟩
                  t₂ v v∈ₛ = ∈∈ₛ {a = v} {b = E m'} .fst
                    (h₂ v v∈σ (shape-fill X Ka Kb v (E m') v∈Sel))
                    where
                    v∈Sel : ⟨ v ∈ selectMember X Ka Kb ⟩
                    v∈Sel = ∈∈ₛ {a = v} {b = selectMember X Ka Kb} .snd v∈ₛ
                    v∈σ : ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                    v∈σ = subst (λ w → ⟨ v ∈ˢ w ⟩) (sym qσ)
                      (Lset-mono {sucV τ} {τ} (self∈sucV τ)
                        (Atr {x = X} {y = v}
                          (selectMember-sub {X = X} {Ka = Ka} {Kb = Kb} {w = v} v∈Sel)
                          (Atr {x = Shelf} {y = X} hX' S∈)))
                goKey a ha eqa b hb eqb =
                  PT.rec squash₁ (λ { (m , hm , eqm) →
                  PT.rec squash₁ (λ { (l , hl , eql) →
                    let i : Fin k
                        i = fromℕ' k m hm
                        j : Fin k
                        j = fromℕ' k l hl
                        eqi : # (toℕ i) ≡ a
                        eqi = cong (λ q → # q) (toFromId' k m hm) ∙ sym eqm
                        eqj : # (toℕ j) ≡ b
                        eqj = cong (λ q → # q) (toFromId' k l hl) ∙ sym eql
                        eqiKa : ⁅ # (toℕ i) ⁆s ≡ Ka
                        eqiKa = cong ⁅_⁆s eqi ∙ sym eqa
                        eqjKb : ⁅ # (toℕ j) ⁆s ≡ Kb
                        eqjKb = cong ⁅_⁆s eqj ∙ sym eqb
                    in let fX : Σ[ mX ∈ ⟪ Shelf ⟫ ] (⟪ Shelf ⟫↪ mX ≡ X)
                           fX = ∈-asFiber {a = X} {b = Shelf} hX'
                           step≡ : stepImage {n} {k} tagSelM (fX .fst , i , j) ≡ E m'
                           step≡ =
                             cong (λ w → selectMember w ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s) (fX .snd)
                             ∙ cong (λ w → selectMember X w ⁅ # (toℕ j) ⁆s) eqiKa
                             ∙ cong (λ w → selectMember X Ka w) eqjKb
                             ∙ sym eSel
                       in ∣ (fX .fst , (i , (j , step≡))) ∣₁
                    }) (∈#-elim k b hb) })
                  (∈#-elim k a ha)

        sub₂ : ⟨ selMImg n k ⊆ DefA.defSet ΦM ⟩
        sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet ΦM)) build (selMOut z z∈ₛm)
          where
          z∈ₛm : ⟨ z ∈ selMImg n k ⟩
          z∈ₛm = ∈∈ₛ {a = z} {b = selMImg n k} .snd z∈ₛ
          build : Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                    (stepImage {n} {k} tagSelM (m , i , j) ≡ z)
                → ⟨ z ∈ₛ DefA.defSet ΦM ⟩
          build (m , i , j , e) =
            subst (λ w → ⟨ w ∈ₛ DefA.defSet ΦM ⟩) q'
              (∈∈ₛ {a = E m'} {b = DefA.defSet ΦM} .fst
                (subst ⟨_⟩ (sym (chain m')) sat))
            where
            X : V ℓ
            X = ⟪ Shelf ⟫↪ m
            hX : ⟨ X ∈ Shelf ⟩
            hX = ∈∈ₛ {a = X} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ m)
            Ka : V ℓ
            Ka = ⁅ # (toℕ i) ⁆s
            Kb : V ℓ
            Kb = ⁅ # (toℕ j) ⁆s
            X∈τ : ⟨ X ∈ Lset τ ⟩
            X∈τ = Atr {x = Shelf} {y = X} hX S∈
            Ka∈τ : ⟨ Ka ∈ Lset τ ⟩
            Ka∈τ = KS∈ i
            Kb∈τ : ⟨ Kb ∈ Lset τ ⟩
            Kb∈τ = KS∈ j
            z≡ : z ≡ selectMember X Ka Kb
            z≡ = sym e
            z∈τ : ⟨ z ∈ Lset (sucV τ) ⟩
            z∈τ = subst (λ w → ⟨ w ∈ Lset (sucV τ) ⟩) (sym z≡)
                    (SelWalk.walk X Ka Kb τ X∈τ Ka∈τ Kb∈τ)
            z∈ⁱ : ⟨ z ∈ Lset (sucV (sucV τ)) ⟩
            z∈ⁱ = Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ)) z∈τ
            m' = ∈-asFiber {a = z} {b = Lset (sucV (sucV τ))} z∈ⁱ .fst
            q' : E m' ≡ z
            q' = ∈-asFiber {a = z} {b = Lset (sucV (sucV τ))} z∈ⁱ .snd
            hXˢ : ⟨ X ∈ˢ fst (DefA.ι mS) ⟩
            hXˢ = subst (λ w → ⟨ X ∈ˢ w ⟩) (sym qS) hX
            hKaˢ : ⟨ Ka ∈ˢ fst (DefA.ι mKeys) ⟩
            hKaˢ = subst (λ w → ⟨ Ka ∈ˢ w ⟩) (sym qKeys)
                     (singletons-in {X = # k} {x = # (toℕ i)} (num∈num (toℕ i) k (toℕ<n i)))
            hKbˢ : ⟨ Kb ∈ˢ fst (DefA.ι mKeys) ⟩
            hKbˢ = subst (λ w → ⟨ Kb ∈ˢ w ⟩) (sym qKeys)
                     (singletons-in {X = # k} {x = # (toℕ j)} (num∈num (toℕ j) k (toℕ<n j)))
            h₁ : (v : V ℓ) → ⟨ v ∈ E m' ⟩
                → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩
            h₁ v hv = shape-fill X Ka Kb v (E m') v∈Sel
              where
              v∈Sel : ⟨ v ∈ selectMember X Ka Kb ⟩
              v∈Sel = subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv
            h₂ : (v : V ℓ) → ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩ → ⟨ v ∈ E m' ⟩
            h₂ v vσ hshape = subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ z≡))
              (shape-read X Ka Kb v (E m') hshape)
            sat : ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι ΦM) ⟩
            sat = ∣ X , (hXˢ , ∣ Ka , (hKaˢ , ∣ Kb , (hKbˢ , (h₁ , h₂)) ∣₁) ∣₁) ∣₁

  private
    module SelEImg (n k : ℕ) (τ : V ℓ)
      (S∈ : ⟨ slice n k ∈ Lset τ ⟩)
      (K∈ : ⟨ # k ∈ Lset τ ⟩)
      (KS∈ : (i : Fin k) → ⟨ ⁅ # (toℕ i) ⁆s ∈ Lset τ ⟩) where
      Shelf : V ℓ
      Shelf = slice n k

      module DefA = DefOf (Lset (sucV (sucV τ)))
      module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV τ))))
      Atr = layer-trans (Lset-layer τ)

      E : ⟪ Lset (sucV (sucV τ)) ⟫ → V ℓ
      E m = ⟪ Lset (sucV (sucV τ)) ⟫↪ m

      -- The stage one step above the shelf stage, as a member of the image
      -- stage: the pin's second inclusion is bounded over it.
      σ∈ : ⟨ Lset (sucV τ) ∈ Lset (sucV (sucV τ)) ⟩
      σ∈ = mkUp (sucV τ) (Lset (sucV τ)) ⊤̇ (DefOf.defSet⊤≡A (Lset (sucV τ)))
      mσ = ∈-asFiber {a = Lset (sucV τ)} {b = Lset (sucV (sucV τ))} σ∈ .fst
      qσ : E mσ ≡ Lset (sucV τ)
      qσ = ∈-asFiber {a = Lset (sucV τ)} {b = Lset (sucV (sucV τ))} σ∈ .snd

      -- The shelf and the key family (the singletons of the numeral's
      -- members) in the image stage.
      Shelf' : ⟨ Shelf ∈ Lset (sucV (sucV τ)) ⟩
      Shelf' = Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ))
                 (Lset-mono {sucV τ} {τ} (self∈sucV τ) S∈)
      mS = ∈-asFiber {a = Shelf} {b = Lset (sucV (sucV τ))} Shelf' .fst
      qS : E mS ≡ Shelf
      qS = ∈-asFiber {a = Shelf} {b = Lset (sucV (sucV τ))} Shelf' .snd

      Keys∈ : ⟨ singletons (# k) ∈ Lset (sucV (sucV τ)) ⟩
      Keys∈ = Lset-in (sucV (sucV τ)) (sucV τ) (singletons (# k)) (self∈sucV (sucV τ))
                (𝒟ₒ-intro (Lset (sucV τ)) (singletons (# k))
                  ∣ SglFam.Φ (# k) τ K∈ , SglFam.defSet≡ (# k) τ K∈ ∣₁)
      mKeys = ∈-asFiber {a = singletons (# k)} {b = Lset (sucV (sucV τ))} Keys∈ .fst
      qKeys : E mKeys ≡ singletons (# k)
      qKeys = ∈-asFiber {a = singletons (# k)} {b = Lset (sucV (sucV τ))} Keys∈ .snd

      -- The membership shape, the delivered selection description's body: a
      -- member of the selection is a member of the family holding, at the two
      -- keys, two recorded values in membership, with the pair chain bound
      -- inside the member.  Over the stage the keys are bound, not constants.
      shape : Formula ⟪ Lset (sucV (sucV τ)) ⟫ (suc (suc (suc (suc (suc zero)))))
      shape = (var zero ∈̇ var (suc (suc (suc zero))))
            ∧̇ (∃̇∈ (var (suc (suc zero)))
                 (∃̇∈ (var (suc (suc zero)))
                   (∃̇∈ (var (suc (suc zero)))
                     (∃̇∈ (var zero)
                       (∃̇∈ (var zero)
                         (∃̇∈ (var (suc (suc (suc (suc (suc zero))))))
                           ((prAt′ f3 f5 f1) ∧̇ (prAt′ zero f4 f1))))))))

      dShape : Δ₀ shape
      dShape = δ-∧ δ-∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∃∈
                 (δ-∧ (Δ₀-prAt′ f3 f5 f1) (Δ₀-prAt′ zero f4 f1))))))))

      shapeV : Formula (V ℓ) (suc (suc (suc (suc (suc zero)))))
      shapeV = mapFo fst (mapFo DefA.ι shape)

      ΦM : Formula ⟪ Lset (sucV (sucV τ)) ⟫ 1
      ΦM = ∃̇∈ (con mS) (∃̇∈ (con mKeys) (∃̇∈ (con mKeys)
             ( (∀̇∈ (var (suc (suc (suc zero)))) shape)
             ∧̇ (∀̇∈ (con mσ)
                  (shape ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))))) )))

      dΦM : Δ₀ ΦM
      dΦM = δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (δ-∀∈ dShape)
             (δ-∀∈ (δ-⇒ dShape δ-∈)))))

      chain : ∀ m → (E m ∈ DefA.defSet ΦM)
                  ≡ ((E m ∷ []) ⊨v mapFo fst (mapFo DefA.ι ΦM))
      chain m = RefA.abs-defSet ΦM dΦM m
              ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                      (mapFo DefA.ι ΦM) (E m ∷ []))

      -- The two readers of the description, at the stage: the satisfaction of
      -- the shape is the membership in the selection, and back.
      shape-read : (X Ka Kb v z : V ℓ)
                 → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
                 → ⟨ v ∈ selectEqual X Ka Kb ⟩
      shape-read X Ka Kb v z h = PT.rec (snd (v ∈ selectEqual X Ka Kb))
        (λ { (a , ha , w₁) → PT.rec (snd (v ∈ selectEqual X Ka Kb))
          (λ { (b , hb , w₂) → PT.rec (snd (v ∈ selectEqual X Ka Kb))
            (λ { (p , hp , w₃) → PT.rec (snd (v ∈ selectEqual X Ka Kb))
              (λ { (d , hd , w₄) → PT.rec (snd (v ∈ selectEqual X Ka Kb))
                (λ { (u , hu , w₅) → PT.rec (snd (v ∈ selectEqual X Ka Kb))
                  (λ { (p' , hp' , (sa , sb)) →
                    selectEqual-in {X = X} {Ka = Ka} {Kb = Kb} {w = v}
                      {a = a} {b = b} {u = u}
                      (h .fst)
                      ha hb
                      (subst (λ q → ⟨ q ∈ v ⟩)
                        (subst ⟨_⟩ (prAt-adequate f3 f5 f1
                          (p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ [])) sa)
                        hp)
                      (subst (λ q → ⟨ q ∈ v ⟩)
                        (subst ⟨_⟩ (prAt-adequate zero f4 f1
                          (p' ∷ u ∷ d ∷ p ∷ b ∷ a ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ [])) sb)
                        hp') })
                  w₅ }) w₄ }) w₃ }) w₂ }) w₁ }) (h .snd)

      shape-fill : (X Ka Kb v z : V ℓ)
                 → ⟨ v ∈ selectEqual X Ka Kb ⟩
                 → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
      shape-fill X Ka Kb v z hv = PT.rec
        (snd ((v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV)) build
        (selectEqual-wit {X = X} {Ka = Ka} {Kb = Kb} {w = v} hv)
        where
        build : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ u ∈ V ℓ ]
                ( ⟨ a ∈ Ka ⟩ × ⟨ b ∈ Kb ⟩ × ⟨ pr a u ∈ v ⟩ × ⟨ pr b u ∈ v ⟩ )
              → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []) ⊨v shapeV ⟩
        build (a , b , u , ha , hb , hau , hbu) =
          selectEqual-sub {X = X} {Ka = Ka} {Kb = Kb} {w = v} hv
          , ∣ a , ha
          , ∣ b , hb
          , ∣ pr a u , hau
          , ∣ ⁅ a , u ⁆ , ∈pair-introR refl
          , ∣ u , ∈pair-introR refl
          , ∣ pr b u , hbu
          , ( subst ⟨_⟩ (sym (prAt-adequate f3 f5 f1
                (pr b u ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []))) refl
            , subst ⟨_⟩ (sym (prAt-adequate zero f4 f1
                (pr b u ∷ u ∷ ⁅ a , u ⁆ ∷ pr a u ∷ b ∷ a ∷ v ∷ Kb ∷ Ka ∷ X ∷ z ∷ []))) refl )
          ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

      selEOut : (z : V ℓ) → ⟨ z ∈ selEImg n k ⟩
              → ∥ Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                   (stepImage {n} {k} tagSelE (m , i , j) ≡ z) ∥₁
      selEOut z = PT.map λ { ((m , (i , j)) , e) → m , i , j , e }

      selEDefSet≡ : DefA.defSet ΦM ≡ selEImg n k
      selEDefSet≡ = extensionality (DefA.defSet ΦM) (selEImg n k) (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet ΦM ⊆ selEImg n k ⟩
        sub₁ z z∈ₛ = PT.rec (snd (z ∈ₛ selEImg n k)) go
          (∈∈ₛ {a = z} {b = DefA.defSet ΦM} .snd z∈ₛ)
          where
          go : Σ[ p ∈ Σ[ m ∈ ⟪ Lset (sucV (sucV τ)) ⟫ ] ⟨ DefA.smallSat ΦM m ⟩ ]
                 (E (p .fst) ≡ z)
             → ⟨ z ∈ₛ selEImg n k ⟩
          go ((m , h) , q) = PT.rec (snd (z ∈ₛ selEImg n k)) build
            (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))
            where
            build : Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                      (stepImage {n} {k} tagSelE (mX , i , j) ≡ E m)
                  → ⟨ z ∈ₛ selEImg n k ⟩
            build (mX , i , j , e) = subst (λ w → ⟨ w ∈ₛ selEImg n k ⟩) (e ∙ q)
              (∈∈ₛ {a = stepImage {n} {k} tagSelE (mX , i , j)} {b = selEImg n k} .fst
                ∣ (mX , i , j) , refl ∣₁)
            fromSat : (m' : ⟪ Lset (sucV (sucV τ)) ⟫)
                    → ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι ΦM) ⟩
                    → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                         (stepImage {n} {k} tagSelE (mX , i , j) ≡ E m') ∥₁
            fromSat m' big = PT.rec squash₁ (λ { (X , hX , w₁) →
              PT.rec squash₁ (λ { (Ka , hKa , w₂) →
              PT.rec squash₁ (λ { (Kb , hKb , body) →
                finish X Ka Kb (subst (λ w → ⟨ X ∈ w ⟩) qS hX)
                       (subst (λ w → ⟨ Ka ∈ w ⟩) qKeys hKa)
                       (subst (λ w → ⟨ Kb ∈ w ⟩) qKeys hKb)
                       (body .fst) (body .snd) }) w₂ }) w₁ }) big
              where
              finish : (X Ka Kb : V ℓ) → ⟨ X ∈ Shelf ⟩ → ⟨ Ka ∈ singletons (# k) ⟩
                     → ⟨ Kb ∈ singletons (# k) ⟩
                     → ((v : V ℓ) → ⟨ v ∈ E m' ⟩
                        → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩)
                     → ((v : V ℓ) → ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                        → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩
                        → ⟨ v ∈ E m' ⟩)
                     → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                          (stepImage {n} {k} tagSelE (mX , i , j) ≡ E m') ∥₁
              finish X Ka Kb hX' hKa' hKb' h₁ h₂ =
                PT.rec squash₁ (λ { (a , ha , eqa) →
                PT.rec squash₁ (λ { (b , hb , eqb) →
                  goKey a ha eqa b hb eqb }) (singletons-out {X = # k} {w = Kb} hKb') })
                (singletons-out {X = # k} {w = Ka} hKa')
                where
                goKey : (a : V ℓ) → ⟨ a ∈ # k ⟩ → Ka ≡ ⁅ a ⁆s
                      → (b : V ℓ) → ⟨ b ∈ # k ⟩ → Kb ≡ ⁅ b ⁆s
                      → ∥ Σ[ mX ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                           (stepImage {n} {k} tagSelE (mX , i , j) ≡ E m') ∥₁
                eSel : E m' ≡ selectEqual X Ka Kb
                eSel = extensionality (E m') (selectEqual X Ka Kb) (t₁ , t₂)
                  where
                  t₁ : ⟨ E m' ⊆ selectEqual X Ka Kb ⟩
                  t₁ v v∈ₛ = ∈∈ₛ {a = v} {b = selectEqual X Ka Kb} .fst
                    (shape-read X Ka Kb v (E m')
                      (h₁ v (∈∈ₛ {a = v} {b = E m'} .snd v∈ₛ)))
                  t₂ : ⟨ selectEqual X Ka Kb ⊆ E m' ⟩
                  t₂ v v∈ₛ = ∈∈ₛ {a = v} {b = E m'} .fst
                    (h₂ v v∈σ (shape-fill X Ka Kb v (E m') v∈Sel))
                    where
                    v∈Sel : ⟨ v ∈ selectEqual X Ka Kb ⟩
                    v∈Sel = ∈∈ₛ {a = v} {b = selectEqual X Ka Kb} .snd v∈ₛ
                    v∈σ : ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                    v∈σ = subst (λ w → ⟨ v ∈ˢ w ⟩) (sym qσ)
                      (Lset-mono {sucV τ} {τ} (self∈sucV τ)
                        (Atr {x = X} {y = v}
                          (selectEqual-sub {X = X} {Ka = Ka} {Kb = Kb} {w = v} v∈Sel)
                          (Atr {x = Shelf} {y = X} hX' S∈)))
                goKey a ha eqa b hb eqb =
                  PT.rec squash₁ (λ { (m , hm , eqm) →
                  PT.rec squash₁ (λ { (l , hl , eql) →
                    let i : Fin k
                        i = fromℕ' k m hm
                        j : Fin k
                        j = fromℕ' k l hl
                        eqi : # (toℕ i) ≡ a
                        eqi = cong (λ q → # q) (toFromId' k m hm) ∙ sym eqm
                        eqj : # (toℕ j) ≡ b
                        eqj = cong (λ q → # q) (toFromId' k l hl) ∙ sym eql
                        eqiKa : ⁅ # (toℕ i) ⁆s ≡ Ka
                        eqiKa = cong ⁅_⁆s eqi ∙ sym eqa
                        eqjKb : ⁅ # (toℕ j) ⁆s ≡ Kb
                        eqjKb = cong ⁅_⁆s eqj ∙ sym eqb
                    in let fX : Σ[ mX ∈ ⟪ Shelf ⟫ ] (⟪ Shelf ⟫↪ mX ≡ X)
                           fX = ∈-asFiber {a = X} {b = Shelf} hX'
                           step≡ : stepImage {n} {k} tagSelE (fX .fst , i , j) ≡ E m'
                           step≡ =
                             cong (λ w → selectEqual w ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s) (fX .snd)
                             ∙ cong (λ w → selectEqual X w ⁅ # (toℕ j) ⁆s) eqiKa
                             ∙ cong (λ w → selectEqual X Ka w) eqjKb
                             ∙ sym eSel
                       in ∣ (fX .fst , (i , (j , step≡))) ∣₁
                    }) (∈#-elim k b hb) })
                  (∈#-elim k a ha)

        sub₂ : ⟨ selEImg n k ⊆ DefA.defSet ΦM ⟩
        sub₂ z z∈ₛ = PT.rec (snd (z ∈ₛ DefA.defSet ΦM)) build (selEOut z z∈ₛm)
          where
          z∈ₛm : ⟨ z ∈ selEImg n k ⟩
          z∈ₛm = ∈∈ₛ {a = z} {b = selEImg n k} .snd z∈ₛ
          build : Σ[ m ∈ ⟪ Shelf ⟫ ] Σ[ i ∈ Fin k ] Σ[ j ∈ Fin k ]
                    (stepImage {n} {k} tagSelE (m , i , j) ≡ z)
                → ⟨ z ∈ₛ DefA.defSet ΦM ⟩
          build (m , i , j , e) =
            subst (λ w → ⟨ w ∈ₛ DefA.defSet ΦM ⟩) q'
              (∈∈ₛ {a = E m'} {b = DefA.defSet ΦM} .fst
                (subst ⟨_⟩ (sym (chain m')) sat))
            where
            X : V ℓ
            X = ⟪ Shelf ⟫↪ m
            hX : ⟨ X ∈ Shelf ⟩
            hX = ∈∈ₛ {a = X} {b = Shelf} .snd (∈ₛ⟪ Shelf ⟫↪ m)
            Ka : V ℓ
            Ka = ⁅ # (toℕ i) ⁆s
            Kb : V ℓ
            Kb = ⁅ # (toℕ j) ⁆s
            X∈τ : ⟨ X ∈ Lset τ ⟩
            X∈τ = Atr {x = Shelf} {y = X} hX S∈
            Ka∈τ : ⟨ Ka ∈ Lset τ ⟩
            Ka∈τ = KS∈ i
            Kb∈τ : ⟨ Kb ∈ Lset τ ⟩
            Kb∈τ = KS∈ j
            z≡ : z ≡ selectEqual X Ka Kb
            z≡ = sym e
            z∈τ : ⟨ z ∈ Lset (sucV τ) ⟩
            z∈τ = subst (λ w → ⟨ w ∈ Lset (sucV τ) ⟩) (sym z≡)
                    (SelEWalk.walk X Ka Kb τ X∈τ Ka∈τ Kb∈τ)
            z∈ⁱ : ⟨ z ∈ Lset (sucV (sucV τ)) ⟩
            z∈ⁱ = Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ)) z∈τ
            m' = ∈-asFiber {a = z} {b = Lset (sucV (sucV τ))} z∈ⁱ .fst
            q' : E m' ≡ z
            q' = ∈-asFiber {a = z} {b = Lset (sucV (sucV τ))} z∈ⁱ .snd
            hXˢ : ⟨ X ∈ˢ fst (DefA.ι mS) ⟩
            hXˢ = subst (λ w → ⟨ X ∈ˢ w ⟩) (sym qS) hX
            hKaˢ : ⟨ Ka ∈ˢ fst (DefA.ι mKeys) ⟩
            hKaˢ = subst (λ w → ⟨ Ka ∈ˢ w ⟩) (sym qKeys)
                     (singletons-in {X = # k} {x = # (toℕ i)} (num∈num (toℕ i) k (toℕ<n i)))
            hKbˢ : ⟨ Kb ∈ˢ fst (DefA.ι mKeys) ⟩
            hKbˢ = subst (λ w → ⟨ Kb ∈ˢ w ⟩) (sym qKeys)
                     (singletons-in {X = # k} {x = # (toℕ j)} (num∈num (toℕ j) k (toℕ<n j)))
            h₁ : (v : V ℓ) → ⟨ v ∈ E m' ⟩
                → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩
            h₁ v hv = shape-fill X Ka Kb v (E m') v∈Sel
              where
              v∈Sel : ⟨ v ∈ selectEqual X Ka Kb ⟩
              v∈Sel = subst (λ w → ⟨ v ∈ w ⟩) (q' ∙ z≡) hv
            h₂ : (v : V ℓ) → ⟨ v ∈ˢ fst (DefA.ι mσ) ⟩
                → ⟨ (v ∷ Kb ∷ Ka ∷ X ∷ E m' ∷ []) ⊨v shapeV ⟩ → ⟨ v ∈ E m' ⟩
            h₂ v vσ hshape = subst (λ w → ⟨ v ∈ w ⟩) (sym (q' ∙ z≡))
              (shape-read X Ka Kb v (E m') hshape)
            sat : ⟨ (E m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι ΦM) ⟩
            sat = ∣ X , (hXˢ , ∣ Ka , (hKaˢ , ∣ Kb , (hKbˢ , (h₁ , h₂)) ∣₁) ∣₁) ∣₁

  selMImgL : (n k : ℕ) → ⟨ isL (slice n k) ⟩ → ⟨ isL (selMImg n k) ⟩
  selMImgL n k lS = PT.rec (snd (isL (selMImg n k)))
    (λ { (τ , oτ , mem) →
      defSet→isL (sucV (sucV τ)) (suc-ord (suc-ord oτ)) (selMImg n k)
        ∣ SelMImg.ΦM n k τ (mem zero) (mem (suc zero))
            (λ i → mem (suc (suc i)))
        , SelMImg.selMDefSet≡ n k τ (mem zero) (mem (suc zero))
            (λ i → mem (suc (suc i))) ∣₁ })
    (stageFam (suc (suc k)) fam famL)
    where
    isL-numeral : (m : ℕ) → ⟨ isL (# m) ⟩
    isL-numeral m = subst (λ w → ⟨ isL w ⟩) (numeralL-fst m) (numeralL m .snd)
    fam : Fin (suc (suc k)) → V ℓ
    fam zero = slice n k
    fam (suc zero) = # k
    fam (suc (suc i)) = ⁅ # (toℕ i) ⁆s
    famL : (i : Fin (suc (suc k))) → ⟨ isL (fam i) ⟩
    famL zero = lS
    famL (suc zero) = isL-numeral k
    famL (suc (suc i)) = sglL (isL-numeral (toℕ i))


  selEImgL : (n k : ℕ) → ⟨ isL (slice n k) ⟩ → ⟨ isL (selEImg n k) ⟩
  selEImgL n k lS = PT.rec (snd (isL (selEImg n k)))
    (λ { (τ , oτ , mem) →
      defSet→isL (sucV (sucV τ)) (suc-ord (suc-ord oτ)) (selEImg n k)
        ∣ SelEImg.ΦM n k τ (mem zero) (mem (suc zero))
            (λ i → mem (suc (suc i)))
        , SelEImg.selEDefSet≡ n k τ (mem zero) (mem (suc zero))
            (λ i → mem (suc (suc i))) ∣₁ })
    (stageFam (suc (suc k)) fam famL)
    where
    isL-numeral : (m : ℕ) → ⟨ isL (# m) ⟩
    isL-numeral m = subst (λ w → ⟨ isL w ⟩) (numeralL-fst m) (numeralL m .snd)
    fam : Fin (suc (suc k)) → V ℓ
    fam zero = slice n k
    fam (suc zero) = # k
    fam (suc (suc i)) = ⁅ # (toℕ i) ⁆s
    famL : (i : Fin (suc (suc k))) → ⟨ isL (fam i) ⟩
    famL zero = lS
    famL (suc zero) = isL-numeral k
    famL (suc (suc i)) = sglL (isL-numeral (toℕ i))

  -- The shift walk: shiftDown of an abstract family is definable over the
  -- third stage above, by the tail's seek sentence with the family a
  -- constant, exactly the bridge chapter's SftD with abstract arguments.
  private
    module ShiftWalk (X τ : V ℓ) (X∈ : ⟨ X ∈ Lset τ ⟩) where
      Atr = layer-trans (Lset-layer τ)
      module DefA = DefOf (Lset (sucV (sucV (sucV τ))))
      module RefA = DefA.Refine (layer-trans (Lset-layer (sucV (sucV (sucV τ)))))

      E³ : ⟪ Lset (sucV (sucV (sucV τ))) ⟫ → V ℓ
      E³ m = ⟪ Lset (sucV (sucV (sucV τ))) ⟫↪ m

      X∈³ : ⟨ X ∈ Lset (sucV (sucV (sucV τ))) ⟩
      X∈³ = Lset-mono {sucV (sucV (sucV τ))} {sucV (sucV τ)} (self∈sucV (sucV (sucV τ)))
              (Lset-mono {sucV (sucV τ)} {sucV τ} (self∈sucV (sucV τ))
                (Lset-mono {sucV τ} {τ} (self∈sucV τ) X∈))
      mX = ∈-asFiber {a = X} {b = Lset (sucV (sucV (sucV τ)))} X∈³ .fst
      qX : E³ mX ≡ X
      qX = ∈-asFiber {a = X} {b = Lset (sucV (sucV (sucV τ)))} X∈³ .snd

      Φ : Formula ⟪ Lset (sucV (sucV (sucV τ))) ⟫ 1
      Φ = ∃̇∈ (con mX)
            ( (∀̇∈ (var f1) (tailSeek (var f1)))
            ∧̇ (∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero)
                 (∀̇∈ (var f2) (∀̇∈ (var zero) (∀̇∈ (var f2)
                   ((prAt′ f5 f3 f1 ∧̇ sucAt′ zero f3)
                     ⇒̇ ∃̇∈ (var f7) (prAt′ zero f1 f2)))))))) )

      dΦ : Δ₀ Φ
      dΦ = δ-∃∈ (δ-∧ (δ-∀∈ (Δ₀-tailSeek (var f1)))
             (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈
               (δ-⇒ (δ-∧ (Δ₀-prAt′ f5 f3 f1) (Δ₀-sucAt′ zero f3))
                    (δ-∃∈ (Δ₀-prAt′ zero f1 f2))))))))))

      chain : ∀ m → (E³ m ∈ DefA.defSet Φ)
                  ≡ ((E³ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ))
      chain m = RefA.abs-defSet Φ dΦ m
              ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ fst id
                      (mapFo DefA.ι Φ) (E³ m ∷ []))

      defSet≡ : DefA.defSet Φ ≡ shiftDown X
      defSet≡ = extensionality (DefA.defSet Φ) (shiftDown X) (sub₁ , sub₂)
        where
        sub₁ : ⟨ DefA.defSet Φ ⊆ shiftDown X ⟩
        sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ shiftDown X))
          (λ { ((m , h) , q) →
            subst (λ w → ⟨ w ∈ₛ shiftDown X ⟩) q
              (∈∈ₛ {a = E³ m} {b = shiftDown X} .fst
                (fromSat m (subst ⟨_⟩ (chain m) ∣ (m , h) , refl ∣₁))) })
          (∈∈ₛ {a = y} {b = DefA.defSet Φ} .snd y∈ₛ)
          where
          fromSat : (m : ⟪ Lset (sucV (sucV (sucV τ))) ⟫)
                  → ⟨ (E³ m ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
                  → ⟨ E³ m ∈ shiftDown X ⟩
          fromSat m = PT.rec (snd (E³ m ∈ shiftDown X))
            (λ { (γ , hγ , membV , imgV) →
              subst (λ w → ⟨ w ∈ shiftDown X ⟩) (sym (T≡ γ membV imgV))
                (shiftDown-in {X = X} {z = γ}
                  (subst (λ w → ⟨ γ ∈ w ⟩) qX hγ)) })
            where
            T = E³ m
            T≡ : (γ : V ℓ)
               → ((z : V ℓ) → ⟨ z ∈ T ⟩ → ⟨ (z ∷ γ ∷ T ∷ []) ⊨v tailSeek (var f1) ⟩)
               → ((p : V ℓ) → ⟨ p ∈ γ ⟩ → (d₁ : V ℓ) → ⟨ d₁ ∈ p ⟩
                  → (s : V ℓ) → ⟨ s ∈ d₁ ⟩ → (d₂ : V ℓ) → ⟨ d₂ ∈ p ⟩
                  → (v : V ℓ) → ⟨ v ∈ d₂ ⟩ → (a : V ℓ) → ⟨ a ∈ s ⟩
                  → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ γ ∷ T ∷ [])
                        ⊨v (prAt′ f5 f3 f1 ∧̇ sucAt′ zero f3) ⟩
                  → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ γ ∷ T ∷ [])
                        ⊨v ∃̇∈ (var f7) (prAt′ zero f1 f2) ⟩)
               → T ≡ tailGraph γ
            T≡ γ membV imgV = extensionality T (tailGraph γ) (t₁ , t₂)
              where
              t₁ : ⟨ T ⊆ tailGraph γ ⟩
              t₁ z z∈ₛ = PT.rec (snd (z ∈ₛ tailGraph γ))
                (λ { (a , v , e , h) →
                  ∈∈ₛ {a = z} {b = tailGraph γ} .fst
                    (subst (λ w → ⟨ w ∈ tailGraph γ ⟩) (sym e)
                      (tailGraph-in h)) })
                (seekOut (var f1) (z ∷ γ ∷ T ∷ [])
                  (membV z (∈∈ₛ {a = z} {b = T} .snd z∈ₛ)))
              t₂ : ⟨ tailGraph γ ⊆ T ⟩
              t₂ z z∈ₛ = PT.rec (snd (z ∈ₛ T))
                (λ { (a , v , h , e) → reach a v h e })
                (tailGraph-out {w = γ} {z = z}
                  (∈∈ₛ {a = z} {b = tailGraph γ} .snd z∈ₛ))
                where
                reach : (a v : V ℓ) → ⟨ pr (sucV a) v ∈ γ ⟩ → z ≡ pr a v
                      → ⟨ z ∈ₛ T ⟩
                reach a v h e = PT.rec (snd (z ∈ₛ T))
                  (λ { (z' , hz' , s') →
                    ∈∈ₛ {a = z} {b = T} .fst
                      (subst (λ w → ⟨ w ∈ T ⟩)
                        (subst ⟨_⟩ (prAt-adequate zero f1 f2
                          (z' ∷ a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s
                            ∷ pr (sucV a) v ∷ γ ∷ T ∷ [])) s'
                         ∙ sym e)
                        hz') })
                  (imgV (pr (sucV a) v) h
                    ⁅ sucV a ⁆s (∈pair-introL refl)
                    (sucV a) (singleton-self (sucV a))
                    ⁅ sucV a , v ⁆ (∈pair-introR refl)
                    v (∈pair-introR refl)
                    a (self∈sucV a)
                    ( subst ⟨_⟩ (sym (prAt-adequate f5 f3 f1
                        (a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s
                          ∷ pr (sucV a) v ∷ γ ∷ T ∷ []))) refl
                    , subst ⟨_⟩ (sym (sucAt-adequate zero f3
                        (a ∷ v ∷ ⁅ sucV a , v ⁆ ∷ sucV a ∷ ⁅ sucV a ⁆s
                          ∷ pr (sucV a) v ∷ γ ∷ T ∷ []))) refl ))
        sub₂ : ⟨ shiftDown X ⊆ DefA.defSet Φ ⟩
        sub₂ y y∈ₛ = PT.rec (snd (y ∈ₛ DefA.defSet Φ)) build
          (shiftDown-out {X = X} {w = y} (∈∈ₛ {a = y} {b = shiftDown X} .snd y∈ₛ))
          where
          build : Σ[ z ∈ V ℓ ] (⟨ z ∈ X ⟩ × (tailGraph z ≡ y))
                → ⟨ y ∈ₛ DefA.defSet Φ ⟩
          build (z , hz , e) =
            subst (λ w → ⟨ w ∈ₛ DefA.defSet Φ ⟩) q'
              (∈∈ₛ {a = E³ m'} {b = DefA.defSet Φ} .fst
                (subst ⟨_⟩ (sym (chain m')) sat))
            where
            z∈σ : ⟨ z ∈ Lset τ ⟩
            z∈σ = Atr {x = X} {y = z} hz X∈
            y∈³ : ⟨ y ∈ Lset (sucV (sucV (sucV τ))) ⟩
            y∈³ = subst (λ w → ⟨ w ∈ Lset (sucV (sucV (sucV τ))) ⟩) e
              (tailStage τ z∈σ)
            m' = ∈-asFiber {a = y} {b = Lset (sucV (sucV (sucV τ)))} y∈³ .fst
            q' : E³ m' ≡ y
            q' = ∈-asFiber {a = y} {b = Lset (sucV (sucV (sucV τ)))} y∈³ .snd
            tail≡ : tailGraph z ≡ E³ m'
            tail≡ = e ∙ sym q'
            membV : (zz : V ℓ) → ⟨ zz ∈ E³ m' ⟩
                  → ⟨ (zz ∷ z ∷ E³ m' ∷ []) ⊨v tailSeek (var f1) ⟩
            membV zz hzz = PT.rec
              (snd ((zz ∷ z ∷ E³ m' ∷ []) ⊨v tailSeek (var f1)))
              (λ { (a , v , h , e'') →
                seekIn (var f1) (zz ∷ z ∷ E³ m' ∷ []) a v e'' h })
              (tailGraph-out {w = z} {z = zz}
                (subst (λ w → ⟨ zz ∈ w ⟩) (sym tail≡) hzz))
            imgV : (p : V ℓ) → ⟨ p ∈ z ⟩ → (d₁ : V ℓ) → ⟨ d₁ ∈ p ⟩
                 → (s : V ℓ) → ⟨ s ∈ d₁ ⟩ → (d₂ : V ℓ) → ⟨ d₂ ∈ p ⟩
                 → (v : V ℓ) → ⟨ v ∈ d₂ ⟩ → (a : V ℓ) → ⟨ a ∈ s ⟩
                 → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])
                       ⊨v (prAt′ f5 f3 f1 ∧̇ sucAt′ zero f3) ⟩
                 → ⟨ (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])
                       ⊨v ∃̇∈ (var f7) (prAt′ zero f1 f2) ⟩
            imgV p hp d₁ hd₁ s hs d₂ hd₂ v hv a ha (s₁ , s₂) =
              ∣ pr a v
              , subst (λ w → ⟨ pr a v ∈ w ⟩) tail≡
                  (tailGraph-in
                    (subst (λ w → ⟨ w ∈ z ⟩)
                      (subst ⟨_⟩ (prAt-adequate f5 f3 f1
                        (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])) s₁
                       ∙ cong (λ w → pr w v)
                           (subst ⟨_⟩ (sucAt-adequate zero f3
                             (a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ [])) s₂))
                      hp))
              , subst ⟨_⟩ (sym (prAt-adequate zero f1 f2
                  (pr a v ∷ a ∷ v ∷ d₂ ∷ s ∷ d₁ ∷ p ∷ z ∷ E³ m' ∷ []))) refl
              ∣₁
            sat : ⟨ (E³ m' ∷ []) ⊨v mapFo fst (mapFo DefA.ι Φ) ⟩
            sat = ∣ z , subst (λ w → ⟨ z ∈ w ⟩) (sym qX) hz
                , membV , imgV ∣₁

      walk : ⟨ shiftDown X ∈ Lset (sucV (sucV (sucV (sucV τ)))) ⟩
      walk = Lset-in (sucV (sucV (sucV (sucV τ)))) (sucV (sucV (sucV τ)))
               (shiftDown X) (self∈sucV (sucV (sucV (sucV τ))))
               (𝒟ₒ-intro (Lset (sucV (sucV (sucV τ)))) (shiftDown X) ∣ Φ , defSet≡ ∣₁)

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
by the invariant (`slice1⊆allTuples`{.Agda}). The closure is constructible
where this batch reached it: the seven delivered tag images (the binaries, the
tuple, the values, and the two selections) each sit in the next stage by one
`defSet→isL`, with the selection walks abstract-parameterized so the adequacy
transfers meet only variables. The shift and the extension images, the step
as the union of the images, and the slice induction remain: the shift image's
deep seek-sentence satisfaction does not finish within the wall in this
formulation, and the items behind it wait on a ruling.
<!--zh-->
## 小结

取值泛化 `valuesAllTuples`{.Agda}，在每个正元数处；两条选择等式 `sat-∈vv-sel`{.Agda} 与 `sat-≐vv-sel`{.Agda}，把满足集上的一次选择读作一次合取；变量变换律 `satSet-rename-shift`{.Agda}，说满足集经全体变元移位而存活；正向钉住包含 `extendFamily-pin`{.Agda}，说新键处的等词原子把整个扩张裁到常元的单点集，与反向钉住包含 `extendFamily-pin-rev`{.Agda}，说单点扩张的每个成员都在新键处记录常元；完整的族扩张等式 `extendFamily-pin-eq`{.Agda}，由变量变换律与两条包含装配而成，形状即带种类不变量之常元原子子句将要消费的样子；以及单例族 `singletons`{.Agda} 连同它的两条隶属定律、`At` 描述 `singletonsAt`{.Agda} 及其两条读式、与可构造性 `singletonsL`{.Agda}，即已交付存货缺掉的那一个运算连同它的内面。然后是选项 B 的元层心脏：带种类的诸层族 `slice`{.Agda}，随层累积，种子即在第零元数片上的单例族、更高片皆空，连同每条子句一条 `slice-in` 律与作为析取反转的 `slice-out`，即让混合元数垃圾按构造成为不可能的架位纪律；带种类的不变量 `slice-inv`{.Agda}，正元数片的每个成员凭对层级的归纳都是 `k` 元数满足集，每个子句一个情形、每条等式消去一个情形，取代证书的诚实性归纳；带可计算见证 `levelOf`{.Agda} 与 `terms-in-levels`{.Agda} 的项到诸层，一次项归纳对着诸 `slice-in` 律；以及切定理，`cut-sound`{.Agda} 与立于本章 `WithLEM` 的 `cut-complete`{.Agda}，诸层的取值切口等于可定义幂集，探针的元数卫式被不变量吸收 (`slice1⊆allTuples`{.Agda})。闭包的可构造性在本批到达之处交付：七个已交付的标签像 (二元三像、元组像、取值像与两个选择像) 各凭一次 `defSet→isL` 落在下一阶段，选择行走抽象参数化，使适足搬运只遇变元。移位像与扩张像、作为诸像之并的步骤、以及片归纳仍待交付：移位像的深寻句满足在本表述下越墙而不终，其后的条目等待裁决。
<!--/-->
