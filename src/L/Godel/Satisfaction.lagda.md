# Satisfaction, as a set, case by case

<!--en-->
For a formula over a carrier, the set of coded assignments that satisfy it in
the carrier's inner world. This chapter proves, one constructor at a time,
that the satisfaction set is an **operation composition**: falsity is the
empty set, truth is all assignments, conjunction and disjunction are the
intersection and the union, negation is the difference from all assignments,
the membership atom at two variables is one selection, and the existential is
the shift. Each case is one extensional identity, and none of it mentions
codes of formulas: the formula stays in the meta language, and only its
satisfaction set exists as an object.

The equations land in the order the connectives are cheap, and the file grows
with the remaining constructors in later commits; what is stated here is
final as stated.
<!--zh-->
给定载体之上的一条公式，在载体的内层世界中满足它的诸被编码赋值之集。本章逐构造子证明：满足集是一个**运算复合**：假是空集，真是全体赋值，合取与析取是交与并，否定是对全体赋值的差，两变元的隶属原子是一次选择，存在量词是移位。每个情形是一条外延等同，且无一提及公式的码：公式留在元语言里，只有它的满足集作为对象存在。

诸等式按联结词便宜的次序落地，文件随其余构造子在后续提交中生长；此处已陈述者按其陈述即为定稿。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Godel.Satisfaction {ℓ : Level} where

open import Base.Classical using ( LEM )

open import FOL.Syntax
  using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ⊤̇; ⊥̇ )
open import V.Hierarchy {ℓ} using ( extensionalV )
open import V.Coding {ℓ} using ( pr )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Coding.Environment {ℓ} using ( cons; lookup-spec )
open import L.Godel.Operations {ℓ}
  using ( singleton-self; singleton-out
        ; _∪_; ∪-left; ∪-right; ∪-out; _∩_; ∩-in; ∩-out; _∖_; ∖-in; ∖-out
        ; selectMember; selectMember-in; selectMember-sub; selectMember-wit
        ; selectEqual; selectEqual-in; selectEqual-sub; selectEqual-wit
        ; tailGraph; shiftDown; shiftDown-in; shiftDown-out )
open import L.Godel.Tuples {ℓ}
  using ( tuple; tupleTail; tuple-entry; allTuples )

open import Cubical.Foundations.Equiv using ( equivFun; invEq )
open import Cubical.Foundations.Prelude using ( subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
```

<!--en-->
## The satisfaction set

The carrier is fixed for the whole chapter; assignments are valued in it and
enter as their graphs, per the tuple chapter. The satisfaction set of a
formula is one set former over the assignments satisfying it, with the
inner-world smallness certificate as the index's second component, and its
two readings are the certificate's two directions. Two private helpers
tabulate an assignment into the inner world's vector form; a third turns the
tuple chapter's entrywise injectivity into an inner-world vector equation,
which is what a binary case spends when its two memberships hand back two
assignments for one set.
<!--zh-->
## 满足集

载体对全章固定；赋值取值其中，并按元组那一章以图的身份进场。公式的满足集是「满足它的诸赋值」上的单个集合形成子，以内层世界的小性证书为索引的第二分量，而它的两条读式就是证书的两个方向。两个私有辅助把赋值制表成内层世界的向量形式；第三个把元组那一章的逐条目单射性变成内层世界的向量等式，二元情形在两份隶属交回同一集合的两个赋值时花的就是它。
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

module _ (A : V ℓ) where
  open DefOf A using ( ι; SM; _⊨ᵐ_; ⊨ᵐ-small )

  private
    κ : ⟪ A ⟫ → V ℓ
    κ = ⟪ A ⟫↪

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
```

<!--en-->
## The propositional cases

Falsity, truth, conjunction, disjunction, negation. Each proof is one
extensionality whose two inclusions convert the connective's inner-world
value into the operation's fiber and back, and the conversions are
definitional: a conjunction's value is the pair the intersection carries, a
disjunction's the truncated sum the union indexes over, and a negation's the
refutation the difference carries. Falsity has nothing to convert, truth
converts a trivial value, and only the conjunction pays the vector equation,
because it is the one case whose operation holds both memberships at once.
<!--zh-->
## 命题诸情形

假、真、合取、析取、否定。每个证明是一次外延性，其两个包含把联结词的内层取值转换为运算的纤维、再转换回来，而转换是定义性的：合取的取值就是交所携带的对，析取的就是并所索引的截断和，否定的就是差所携带的反驳。假无可转换，真转换一个平凡取值，而只有合取要付那条向量等式，因为它是唯一一个其运算同时握有两份隶属的情形。
<!--/-->

```agda
  sat-⊥ : {n : ℕ} → satSet {n} ⊥̇ ≡ ∅
  sat-⊥ {n} = extensionalV λ w → ⇔toPath
    (PT.rec (snd (w ∈ ∅))
      (λ { ((g , s) , _) →
        Empty.rec (lower (invEq (⊨ᵐ-small ⊥̇ (vec g) .snd) s)) }))
    (λ h → Empty.rec (∅-empty w (∈∈ₛ {a = w} {b = ∅} .fst h)))

  sat-⊤ : {n : ℕ} → satSet {n} ⊤̇ ≡ allTuples A n
  sat-⊤ {n} = extensionalV λ w → ⇔toPath
    (PT.rec (snd (w ∈ allTuples A n)) (λ { ((g , _) , e) → ∣ g , e ∣₁ }))
    (PT.rec (snd (w ∈ satSet ⊤̇))
      (λ { (g , e) →
        subst (λ z → ⟨ z ∈ satSet ⊤̇ ⟩) e (sat-in ⊤̇ g tt*) }))

  sat-∧ : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
        → satSet (φ ∧̇ ψ) ≡ satSet φ ∩ satSet ψ
  sat-∧ {n} φ ψ = extensionalV λ w → ⇔toPath (fwdAnd w) (bwdAnd w)
    where
    T : V ℓ
    T = satSet φ ∩ satSet ψ
    fwdAnd : (w : V ℓ) → ⟨ w ∈ satSet (φ ∧̇ ψ) ⟩ → ⟨ w ∈ T ⟩
    fwdAnd w h = PT.rec (snd (w ∈ T))
      (λ { (g , hc , e) →
        subst (λ z → ⟨ z ∈ T ⟩) e
          (∩-in {X = satSet φ} {Y = satSet ψ}
            (sat-in φ g (hc .fst)) (sat-in ψ g (hc .snd))) })
      (sat-out (φ ∧̇ ψ) w h)
    bwdAnd : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet (φ ∧̇ ψ) ⟩
    bwdAnd w h = PT.rec (snd (w ∈ satSet (φ ∧̇ ψ)))
      (λ { (g , hφ , e) → PT.rec (snd (w ∈ satSet (φ ∧̇ ψ)))
        (λ { (g' , hψ , e') →
          subst (λ z → ⟨ z ∈ satSet (φ ∧̇ ψ) ⟩) e
            (sat-in (φ ∧̇ ψ) g
              ( hφ
              , subst (λ δ → ⟨ δ ⊨ᵐ ψ ⟩) (vec-inj (e' ∙ sym e)) hψ )) })
        (sat-out ψ w (∩-out {X = satSet φ} {Y = satSet ψ} h .snd)) })
      (sat-out φ w (∩-out {X = satSet φ} {Y = satSet ψ} h .fst))

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
```

<!--en-->
## The membership atom, at two variables

The atom's satisfaction set is one selection over all assignments, with the
two variable indices entering as singleton key sets: the recorded value at
the one key is a member of the recorded value at the other. Forward, the
assignment's own entries witness the selection; backward, the selection's
witness is read against the assignment's lookup specification, entry by
entry, and lands back in the inner world along the tabulation.
<!--zh-->
## 隶属原子，落在两个变元上

原子的满足集是全体赋值上的一次选择，两个变元指标以单点键集进场：一个键处被记录的取值隶属于另一个键处被记录的取值。正向，赋值自己的条目为选择作见证；反向，选择的见证对着赋值的查值规格逐条目去读，再沿制表落回内层世界。
<!--/-->

```agda
  sat-∈vv : {n : ℕ} (i j : Fin n)
          → satSet (var i ∈̇ var j)
          ≡ selectMember (allTuples A n) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
  sat-∈vv {n} i j = extensionalV λ w → ⇔toPath (fwdAtom w) (bwdAtom w)
    where
    φ : Formula ⟪ A ⟫ n
    φ = var i ∈̇ var j
    Ki Kj T : V ℓ
    Ki = ⁅ # (toℕ i) ⁆s
    Kj = ⁅ # (toℕ j) ⁆s
    T = selectMember (allTuples A n) Ki Kj
    fwdAtom : (w : V ℓ) → ⟨ w ∈ satSet φ ⟩ → ⟨ w ∈ T ⟩
    fwdAtom w hw = PT.rec (snd (w ∈ T))
      (λ { (g , hs , e) →
        subst (λ z → ⟨ z ∈ T ⟩) e
          (selectMember-in {X = allTuples A n} {Ka = Ki} {Kb = Kj}
            {w = tuple A g}
            {a = # (toℕ i)} {b = # (toℕ j)} {u = κ (g i)} {v = κ (g j)}
            ∣ g , refl ∣₁
            (singleton-self (# (toℕ i)))
            (singleton-self (# (toℕ j)))
            ∣ lift i , refl ∣₁
            ∣ lift j , refl ∣₁
            (subst2 (λ p q → ⟨ p ∈ q ⟩) (lk g i) (lk g j) hs)) })
      (sat-out φ w hw)
    bwdAtom : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet φ ⟩
    bwdAtom w h = PT.rec (snd (w ∈ satSet φ))
      (λ { (g , eg) → PT.rec (snd (w ∈ satSet φ))
        (λ { (a , b , u , v , ha , hb , hau , hbv , huv) →
          let hau' : ⟨ pr (# (toℕ i)) u ∈ tuple A g ⟩
              hau' = subst2 (λ p z → ⟨ pr p u ∈ z ⟩)
                       (singleton-out ha) (sym eg) hau
              hbv' : ⟨ pr (# (toℕ j)) v ∈ tuple A g ⟩
              hbv' = subst2 (λ p z → ⟨ pr p v ∈ z ⟩)
                       (singleton-out hb) (sym eg) hbv
              eu : u ≡ κ (g i)
              eu = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) i u) hau'
              ev : v ≡ κ (g j)
              ev = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) j v) hbv'
          in subst (λ z → ⟨ z ∈ satSet φ ⟩) eg
               (sat-in φ g
                 (subst2 (λ p q → ⟨ p ∈ q ⟩)
                   (eu ∙ sym (lk g i)) (ev ∙ sym (lk g j)) huv)) })
        (selectMember-wit {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h) })
      (selectMember-sub {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h)
```

<!--en-->
## The existential

The binder takes the first position of the assignment, so on graphs the
quantifier is the shift: a member of the existential's set is the shift of a
member of the body's set, and conversely every shifted body member drops its
first entry and lands in the existential's set. The repackaging between "a
member of the carrier" and "an inner-world element" is one propositional pair
equation each way.
<!--zh-->
## 存在量词

束缚元占据赋值的首位，故在图上量词就是移位：存在式之集的成员是体之集某成员的移位，反之每个被移位的体成员弃掉首条目、落进存在式之集。「载体的成员」与「内层世界的元素」之间的改装，每个方向是一条命题性的对等式。
<!--/-->

```agda
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
```

<!--en-->
## The equality atom, at two variables

The same selection shape with the relating fact gone: the two keys record
**one** value, and equality never enters the object side as an equation. The
inner world's equality delegates to the hierarchy's, which is a path, so the
conversions are the entry readings composed with two tabulation equations.
<!--zh-->
## 等词原子，落在两个变元上

同一个选择形状，只是关联事实消失了：两个键记录**同一个**取值，相等从不以等式的身份进入对象侧。内层世界的等词委托给层级的等词，即一条路径，故转换就是条目读式复合上两条制表等式。
<!--/-->

```agda
  sat-≐vv : {n : ℕ} (i j : Fin n)
          → satSet (var i ≐ var j)
          ≡ selectEqual (allTuples A n) ⁅ # (toℕ i) ⁆s ⁅ # (toℕ j) ⁆s
  sat-≐vv {n} i j = extensionalV λ w → ⇔toPath (fwdEq w) (bwdEq w)
    where
    φ : Formula ⟪ A ⟫ n
    φ = var i ≐ var j
    Ki Kj T : V ℓ
    Ki = ⁅ # (toℕ i) ⁆s
    Kj = ⁅ # (toℕ j) ⁆s
    T = selectEqual (allTuples A n) Ki Kj
    fwdEq : (w : V ℓ) → ⟨ w ∈ satSet φ ⟩ → ⟨ w ∈ T ⟩
    fwdEq w hw = PT.rec (snd (w ∈ T))
      (λ { (g , hs , e) →
        subst (λ z → ⟨ z ∈ T ⟩) e
          (selectEqual-in {X = allTuples A n} {Ka = Ki} {Kb = Kj}
            {w = tuple A g}
            {a = # (toℕ i)} {b = # (toℕ j)} {u = κ (g i)}
            ∣ g , refl ∣₁
            (singleton-self (# (toℕ i)))
            (singleton-self (# (toℕ j)))
            ∣ lift i , refl ∣₁
            (subst (λ q → ⟨ pr (# (toℕ j)) q ∈ tuple A g ⟩)
              (sym (subst2 _≡_ (lk g i) (lk g j) hs))
              ∣ lift j , refl ∣₁)) })
      (sat-out φ w hw)
    bwdEq : (w : V ℓ) → ⟨ w ∈ T ⟩ → ⟨ w ∈ satSet φ ⟩
    bwdEq w h = PT.rec (snd (w ∈ satSet φ))
      (λ { (g , eg) → PT.rec (snd (w ∈ satSet φ))
        (λ { (a , b , u , ha , hb , hau , hbu) →
          let hau' : ⟨ pr (# (toℕ i)) u ∈ tuple A g ⟩
              hau' = subst2 (λ p z → ⟨ pr p u ∈ z ⟩)
                       (singleton-out ha) (sym eg) hau
              hbu' : ⟨ pr (# (toℕ j)) u ∈ tuple A g ⟩
              hbu' = subst2 (λ p z → ⟨ pr p u ∈ z ⟩)
                       (singleton-out hb) (sym eg) hbu
              eu : u ≡ κ (g i)
              eu = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) i u) hau'
              ev : u ≡ κ (g j)
              ev = subst ⟨_⟩ (lookup-spec (λ x → κ (g x)) j u) hbu'
          in subst (λ z → ⟨ z ∈ satSet φ ⟩) eg
               (sat-in φ g
                 (subst2 _≡_ (sym (lk g i)) (sym (lk g j))
                   (sym eu ∙ ev))) })
        (selectEqual-wit {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h) })
      (selectEqual-sub {X = allTuples A n} {Ka = Ki} {Kb = Kj} {w = w} h)
```

<!--en-->
## Respect, and the classical cases

Two formulas whose satisfactions agree at every environment have the same
satisfaction set: `sat-resp`{.Agda} converts a member through the pointwise
identity and back, and it is what turns a semantic reduction into a case
equation for free. The implication and the universal are exactly such
reductions, and they are the chapter's only classical content: material
implication is the negated conjunction, and the universal is the negated
existential of the negation, each priced at one instance of the excluded
middle inside a double negation. Their satisfaction sets then come out as
compositions of the cases already proved, with not one new extensionality.
<!--zh-->
## 换步，与经典诸情形

在每个环境处满足相符的两条公式有相同的满足集：`sat-resp`{.Agda} 把成员经逐点等同转换过去再回来，它使一次语义化归免费变成一条情形等式。蕴含与全称恰是这样的化归，也是本章仅有的经典内容：实质蕴含是被否定的合取，全称是否定之存在式的否定，各花双重否定之内的一份排中律。于是它们的满足集作为已证情形的复合而得，一次新的外延性都不写。
<!--/-->

```agda
  sat-resp : {n : ℕ} {φ ψ : Formula ⟪ A ⟫ n}
           → ((δ : Vec SM n) → (δ ⊨ᵐ φ) ≡ (δ ⊨ᵐ ψ))
           → satSet φ ≡ satSet ψ
  sat-resp {n} {φ} {ψ} pt = extensionalV λ w → ⇔toPath (to w) (fro w)
    where
    to : (w : V ℓ) → ⟨ w ∈ satSet φ ⟩ → ⟨ w ∈ satSet ψ ⟩
    to w h = PT.rec (snd (w ∈ satSet ψ))
      (λ { (g , hg , e) →
        subst (λ z → ⟨ z ∈ satSet ψ ⟩) e
          (sat-in ψ g (subst ⟨_⟩ (pt (vec g)) hg)) })
      (sat-out φ w h)
    fro : (w : V ℓ) → ⟨ w ∈ satSet ψ ⟩ → ⟨ w ∈ satSet φ ⟩
    fro w h = PT.rec (snd (w ∈ satSet φ))
      (λ { (g , hg , e) →
        subst (λ z → ⟨ z ∈ satSet φ ⟩) e
          (sat-in φ g (subst ⟨_⟩ (sym (pt (vec g))) hg)) })
      (sat-out ψ w h)

  module Classical (lem : LEM (ℓ-suc ℓ)) where
    private
      dne : (P : hProp (ℓ-suc ℓ))
          → ((⟨ P ⟩ → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
      dne P hnn = Sum.rec (λ p → p) (λ np → Empty.rec (hnn np)) (lem P)

      imp-not : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n) (δ : Vec SM n)
              → (δ ⊨ᵐ (φ ⇒̇ ψ)) ≡ (δ ⊨ᵐ (¬̇ (φ ∧̇ (¬̇ ψ))))
      imp-not φ ψ δ = ⇔toPath
        (λ imp hc → hc .snd (imp (hc .fst)))
        (λ hn hφ → dne (δ ⊨ᵐ ψ) (λ nψ → hn (hφ , nψ)))

      all-not : {n : ℕ} (ψ : Formula ⟪ A ⟫ (suc n)) (δ : Vec SM n)
              → (δ ⊨ᵐ (∀̇ ψ)) ≡ (δ ⊨ᵐ (¬̇ (∃̇ (¬̇ ψ))))
      all-not ψ δ = ⇔toPath
        (λ hall hex → PT.rec Empty.isProp⊥
            (λ { (x , hnx) → hnx (hall x) }) hex)
        (λ hn x → dne ((x ∷ δ) ⊨ᵐ ψ) (λ nx → hn ∣ x , nx ∣₁))

    sat-⇒ : {n : ℕ} (φ ψ : Formula ⟪ A ⟫ n)
          → satSet (φ ⇒̇ ψ)
          ≡ allTuples A n ∖ (satSet φ ∩ (allTuples A n ∖ satSet ψ))
    sat-⇒ {n} φ ψ =
        sat-resp {φ = φ ⇒̇ ψ} {ψ = ¬̇ (φ ∧̇ (¬̇ ψ))} (imp-not φ ψ)
      ∙ sat-¬ (φ ∧̇ (¬̇ ψ))
      ∙ cong (allTuples A n ∖_)
          (sat-∧ φ (¬̇ ψ) ∙ cong (satSet φ ∩_) (sat-¬ ψ))

    sat-∀ : {n : ℕ} (ψ : Formula ⟪ A ⟫ (suc n))
          → satSet (∀̇ ψ)
          ≡ allTuples A n ∖ shiftDown (allTuples A (suc n) ∖ satSet ψ)
    sat-∀ {n} ψ =
        sat-resp {φ = ∀̇ ψ} {ψ = ¬̇ (∃̇ (¬̇ ψ))} (all-not ψ)
      ∙ sat-¬ (∃̇ (¬̇ ψ))
      ∙ cong (allTuples A n ∖_)
          (sat-∃ (¬̇ ψ) ∙ cong shiftDown (sat-¬ ψ))
```

<!--en-->
## Recap

The satisfaction set `satSet`{.Agda} with its two readings; eight
constructive case equations, `sat-⊥`{.Agda}, `sat-⊤`{.Agda}, `sat-∧`{.Agda},
`sat-∨`{.Agda}, `sat-¬`{.Agda}, `sat-∈vv`{.Agda}, `sat-≐vv`{.Agda} and
`sat-∃`{.Agda}; the respect lemma `sat-resp`{.Agda}; and the two classical
cases `sat-⇒`{.Agda} and `sat-∀`{.Agda}, compositions of the constructive
ones priced at one excluded middle each. Each equation is an extensional
identity between a satisfaction set and an operation composition. The atoms
with constants and the bounded quantifiers join in later commits; the
normal-form theorem then reads every equation off in one induction.
<!--zh-->
## 小结

满足集 `satSet`{.Agda} 连同它的两条读式；八条构造性情形等式 `sat-⊥`{.Agda}、`sat-⊤`{.Agda}、`sat-∧`{.Agda}、`sat-∨`{.Agda}、`sat-¬`{.Agda}、`sat-∈vv`{.Agda}、`sat-≐vv`{.Agda} 与 `sat-∃`{.Agda}；换步引理 `sat-resp`{.Agda}；以及两个经典情形 `sat-⇒`{.Agda} 与 `sat-∀`{.Agda}，即各花一份排中律的构造性情形之复合。每条等式都是满足集与运算复合之间的外延等同。带常元的原子与有界量词在后续提交中加入；范式定理届时以一次归纳把每条等式读出。
<!--/-->
