# Finite trees over a well-ordered alphabet

<!--en-->
A classical well-order, stated once and generically: the finite labelled
trees over a well-ordered alphabet are well-ordered by shortlex. Size rules
first, then the root label, then the children; lists of children compare by
length first, then pointwise. The size and length gates are load-bearing and
not a convenience: the pure pointwise order on lists of unequal length admits
an infinite descent (grow the tail while the head steps down), and it is
exactly the gates that close it. The chapter delivers the order and its four
laws; the part after the order asks nothing of the alphabet beyond its own
four.
<!--zh-->
一个经典良序，一次且泛型地陈述：良序字母表上的有穷带标签树按 shortlex 良序。尺寸先行，其次根标签，再次孩子；孩子表先比长度，再逐点比较。尺寸门与长度门是承重的而非便利：变长表上的纯逐点序容许无穷下降 (头下降的同时让尾生长)，正是这两道门把它关死。本章交付该序与其四条定律；序之后的部分对字母表别无所求，只用它自己的四条。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude

module L.WellOrder.Tree {ℓ : Level} where

open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; Tri; lt; eq; gt )

open import Cubical.Data.Nat using ( _+_; znots; snotz; injSuc )
open import Cubical.Data.Nat.Order
  using ( _<_; _≤_; <-trans; ¬m<m; Trichotomy; _≟_
        ; ≤-refl; ≤-trans; ≤-+k; suc-≤-suc; zero-≤
        ; ≤SumLeft; ≤SumRight; pred-≤-pred; ≤<-trans; ¬-<-zero; isProp≤ )
open Trichotomy
open import Cubical.Data.List using ( List; []; _∷_; length )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
open import Cubical.Relation.Nullary using ( ¬_ )
```

<!--en-->
## The type, and the order
<!--zh-->
## 类型，与序
<!--/-->

<!--en-->
One constructor: a label and a list of children. The three relations are
mutual, one per layer, every numeric or path component lifted to the order's
level. A tree strictly precedes another if it is smaller; at equal size, if
its root label precedes; at equal label, if its children do. A list precedes
another if it is shorter; at equal length, pointwise-lexicographically. The
empty list precedes nothing pointwise, and nothing precedes it.
<!--zh-->
一个构造子：一个标签与一个孩子表。三个关系互递归，每层一个，数值与道路分量都提升到序所在的层级。一棵树严格先于另一棵，若它更小；尺寸相等时，若根标签先于；标签相等时，若孩子表先于。一个表先于另一个，若它更短；长度相等时，按逐点字典序。空表逐点不先于任何表，也没有表逐点先于它。
<!--/-->

```agda
data Tree (L : Type ℓ) : Type ℓ where
  node : L → List (Tree L) → Tree L

module _ {L : Type ℓ} where
  size  : Tree L → ℕ
  sizes : List (Tree L) → ℕ
  size (node l cs) = suc (sizes cs)
  sizes [] = 0
  sizes (t ∷ ts) = size t + sizes ts

module TreeOrder {L : Type ℓ} (w : SWO L) where
  private
    open SWO w using () renaming ( _<∙_ to _<ᴸ_ )

    ℕ≺ : ℕ → ℕ → Type (ℓ-suc ℓ)
    ℕ≺ a b = Lift {ℓ-zero} {ℓ-suc ℓ} (a < b)

    ℕ≋ : ℕ → ℕ → Type (ℓ-suc ℓ)
    ℕ≋ a b = Lift {ℓ-zero} {ℓ-suc ℓ} (a ≡ b)

    P≋ : {X : Type ℓ} → X → X → Type (ℓ-suc ℓ)
    P≋ x y = Lift {ℓ} {ℓ-suc ℓ} (x ≡ y)

    ⊥̂ : Type (ℓ-suc ℓ)
    ⊥̂ = Lift {ℓ-zero} {ℓ-suc ℓ} Empty.⊥

  _≺ᵗ_ : Tree L → Tree L → Type (ℓ-suc ℓ)
  _≺ˡ_ : List (Tree L) → List (Tree L) → Type (ℓ-suc ℓ)
  _≺ᵖ_ : List (Tree L) → List (Tree L) → Type (ℓ-suc ℓ)

  node l cs ≺ᵗ node l' cs' =
    ℕ≺ (sizes cs) (sizes cs')
    ⊎ ( ℕ≋ (sizes cs) (sizes cs')
      × ( (l <ᴸ l') ⊎ (P≋ l l' × (cs ≺ˡ cs')) ) )

  cs ≺ˡ cs' =
    ℕ≺ (length cs) (length cs')
    ⊎ ( ℕ≋ (length cs) (length cs') × (cs ≺ᵖ cs') )

  [] ≺ᵖ _ = ⊥̂
  (t ∷ ts) ≺ᵖ [] = ⊥̂
  (t ∷ ts) ≺ᵖ (t' ∷ ts') = (t ≺ᵗ t') ⊎ (P≋ t t' × (ts ≺ᵖ ts'))
```

<!--en-->
## Trichotomy, irreflexivity, transitivity
<!--zh-->
## 三歧、反自反、传递
<!--/-->

<!--en-->
Trichotomy stacks the component trichotomies: sizes by the numeric one,
labels by the alphabet's, children by length and then pointwise, with the
equality branches assembling constructor paths and the pointwise comparison
guarded by a length equation whose mismatched cases are numeric clashes.
Irreflexivity and transitivity are read off the same stack, transitivity
transporting along the equality components where the layers mix.
<!--zh-->
三歧性把分量的三歧性叠起来：尺寸用数值的，标签用字母表的，孩子先长度后逐点，相等分支组装构造子道路，而逐点比较由一条长度等式看守，其错配情形是数值冲突。反自反与传递沿同一叠读出，传递在层混合处沿相等分量搬运。
<!--/-->

```agda
  triᵗ : (a b : Tree L) → Tri (a ≺ᵗ b) (a ≡ b) (b ≺ᵗ a)
  triˡ : (cs cs' : List (Tree L)) → Tri (cs ≺ˡ cs') (cs ≡ cs') (cs' ≺ˡ cs)
  triᵖ : (cs cs' : List (Tree L)) → length cs ≡ length cs'
       → Tri (cs ≺ᵖ cs') (cs ≡ cs') (cs' ≺ᵖ cs)

  triᵗ (node l cs) (node l' cs') with sizes cs ≟ sizes cs'
  ... | lt p = lt (inl (lift p))
  ... | gt p = gt (inl (lift p))
  ... | eq p with SWO.tri∙ w l l'
  ...   | lt q = lt (inr (lift p , inl q))
  ...   | gt q = gt (inr (lift (sym p) , inl q))
  ...   | eq q with triˡ cs cs'
  ...     | lt r = lt (inr (lift p , inr (lift q , r)))
  ...     | eq r = eq (λ ι → node (q ι) (r ι))
  ...     | gt r = gt (inr (lift (sym p) , inr (lift (sym q) , r)))

  triˡ cs cs' with length cs ≟ length cs'
  ... | lt p = lt (inl (lift p))
  ... | gt p = gt (inl (lift p))
  ... | eq p with triᵖ cs cs' p
  ...   | lt r = lt (inr (lift p , r))
  ...   | eq r = eq r
  ...   | gt r = gt (inr (lift (sym p) , r))

  triᵖ [] [] _ = eq refl
  triᵖ [] (x ∷ xs) p = Empty.rec (znots p)
  triᵖ (x ∷ xs) [] p = Empty.rec (snotz p)
  triᵖ (x ∷ xs) (y ∷ ys) p with triᵗ x y
  ... | lt q = lt (inl q)
  ... | gt q = gt (inl q)
  ... | eq q with triᵖ xs ys (injSuc p)
  ...   | lt r = lt (inr (lift q , r))
  ...   | eq r = eq (λ ι → q ι ∷ r ι)
  ...   | gt r = gt (inr (lift (sym q) , r))

  irrᵗ : (a : Tree L) → ¬ a ≺ᵗ a
  irrˡ : (cs : List (Tree L)) → ¬ cs ≺ˡ cs
  irrᵖ : (cs : List (Tree L)) → ¬ cs ≺ᵖ cs

  irrᵗ (node l cs) (inl p) = ¬m<m (lower p)
  irrᵗ (node l cs) (inr (_ , inl q)) = SWO.irr∙ w l q
  irrᵗ (node l cs) (inr (_ , inr (_ , r))) = irrˡ cs r

  irrˡ cs (inl p) = ¬m<m (lower p)
  irrˡ cs (inr (_ , r)) = irrᵖ cs r

  irrᵖ [] p = lower p
  irrᵖ (x ∷ xs) (inl q) = irrᵗ x q
  irrᵖ (x ∷ xs) (inr (_ , r)) = irrᵖ xs r

  transᵗ : (a b c : Tree L) → a ≺ᵗ b → b ≺ᵗ c → a ≺ᵗ c
  transˡ : (u v z : List (Tree L)) → u ≺ˡ v → v ≺ˡ z → u ≺ˡ z
  transᵖ : (u v z : List (Tree L)) → u ≺ᵖ v → v ≺ᵖ z → u ≺ᵖ z

  transᵗ (node l₁ cs₁) (node l₂ cs₂) (node l₃ cs₃) (inl p) (inl q) =
    inl (lift (<-trans (lower p) (lower q)))
  transᵗ (node l₁ cs₁) (node l₂ cs₂) (node l₃ cs₃) (inl p) (inr (q , _)) =
    inl (lift (subst (λ z → sizes cs₁ < z) (lower q) (lower p)))
  transᵗ (node l₁ cs₁) (node l₂ cs₂) (node l₃ cs₃) (inr (p , _)) (inl q) =
    inl (lift (subst (λ z → z < sizes cs₃) (sym (lower p)) (lower q)))
  transᵗ (node l₁ cs₁) (node l₂ cs₂) (node l₃ cs₃)
    (inr (p , inl a)) (inr (q , inl b)) =
    inr (lift (lower p ∙ lower q) , inl (SWO.trans∙ w l₁ l₂ l₃ a b))
  transᵗ (node l₁ cs₁) (node l₂ cs₂) (node l₃ cs₃)
    (inr (p , inl a)) (inr (q , inr (e , _))) =
    inr (lift (lower p ∙ lower q) , inl (subst (λ z → l₁ <ᴸ z) (lower e) a))
  transᵗ (node l₁ cs₁) (node l₂ cs₂) (node l₃ cs₃)
    (inr (p , inr (e , _))) (inr (q , inl b)) =
    inr (lift (lower p ∙ lower q) , inl (subst (λ z → z <ᴸ l₃) (sym (lower e)) b))
  transᵗ (node l₁ cs₁) (node l₂ cs₂) (node l₃ cs₃)
    (inr (p , inr (e , x))) (inr (q , inr (e' , y))) =
    inr ( lift (lower p ∙ lower q)
        , inr (lift (lower e ∙ lower e') , transˡ cs₁ cs₂ cs₃ x y) )

  transˡ u v z (inl p) (inl q) = inl (lift (<-trans (lower p) (lower q)))
  transˡ u v z (inl p) (inr (q , _)) =
    inl (lift (subst (λ k → length u < k) (lower q) (lower p)))
  transˡ u v z (inr (p , _)) (inl q) =
    inl (lift (subst (λ k → k < length z) (sym (lower p)) (lower q)))
  transˡ u v z (inr (p , x)) (inr (q , y)) =
    inr (lift (lower p ∙ lower q) , transᵖ u v z x y)

  transᵖ [] v z p q = Empty.rec (lower p)
  transᵖ (x ∷ xs) [] z p q = Empty.rec (lower p)
  transᵖ (x ∷ xs) (y ∷ ys) [] p q = Empty.rec (lower q)
  transᵖ (x ∷ xs) (y ∷ ys) (z ∷ zs) (inl a) (inl b) =
    inl (transᵗ x y z a b)
  transᵖ (x ∷ xs) (y ∷ ys) (z ∷ zs) (inl a) (inr (e , _)) =
    inl (subst (λ v → x ≺ᵗ v) (lower e) a)
  transᵖ (x ∷ xs) (y ∷ ys) (z ∷ zs) (inr (e , _)) (inl b) =
    inl (subst (λ v → v ≺ᵗ z) (sym (lower e)) b)
  transᵖ (x ∷ xs) (y ∷ ys) (z ∷ zs) (inr (e , p)) (inr (e' , q)) =
    inr (lift (lower e ∙ lower e') , transᵖ xs ys zs p q)
```

<!--en-->
## Well-foundedness
<!--zh-->
## 良基性
<!--/-->

<!--en-->
By strong induction on size, with nested accessibility inductions inside each
size class. The load-bearing observations: a strict predecessor never exceeds
the tree in size, so the outer induction absorbs every size drop; inside a
fixed size class every list in sight totals at most that size, so every
element is accessible by the outer hypothesis; and a pointwise head descent
rebuilds the tail's accessibility at one shorter length, which is what makes
the rebuild terminate. The bounded lists travel as pairs with their bound,
head and label equalities transport the finished accessibility along a path
rather than an argument into a recursive call, and each nest descends one of
its own structures, size first, then a component accessibility.
<!--zh-->
对尺寸作强归纳，每个尺寸类内部再嵌可及性归纳。承重的观察：严格前驱的尺寸绝不超过原树，故外层归纳吸收每次尺寸下降；固定尺寸类内视野中的每个表总量都不超过该尺寸，故每个元素都由外层假设可及；而逐点头下降在少一的长度上重建尾表的可及性，这正是重建得以终止的原因。有界表连同其界作为序对旅行，头与标签的相等沿道路搬运**做完的**可及性、而非把可及性实参搬进递归调用，于是每层嵌套都在下降自己的某个结构：先尺寸，再某个分量可及性。
<!--/-->

```agda
  private
    one≤size : (t : Tree L) → 1 ≤ size t
    one≤size (node l cs) = suc-≤-suc zero-≤

    len≤sizes : (us : List (Tree L)) → length us ≤ sizes us
    len≤sizes [] = zero-≤
    len≤sizes (u ∷ us) =
      ≤-trans (suc-≤-suc (len≤sizes us)) (≤-+k {k = sizes us} (one≤size u))

    module Class (n : ℕ) (below : (u : Tree L) → size u < n → Acc _≺ᵗ_ u)
                 (s : ℕ) (s<n : s < n) where

      BL : Type ℓ
      BL = Σ[ us ∈ List (Tree L) ] (sizes us ≤ s)

      _≺ᵉ_ : BL → BL → Type (ℓ-suc ℓ)
      p ≺ᵉ q = ℕ≋ (length (p .fst)) (length (q .fst)) × (p .fst ≺ᵖ q .fst)

      _≺ᴮ_ : BL → BL → Type (ℓ-suc ℓ)
      p ≺ᴮ q = p .fst ≺ˡ q .fst

      eqBnd : (us : List (Tree L)) → sizes us ≡ s → sizes us ≤ s
      eqBnd us e = subst (λ x → sizes us ≤ x) e ≤-refl

      headAcc : (u : Tree L) (us : List (Tree L)) → sizes (u ∷ us) ≤ s
              → Acc _≺ᵗ_ u
      headAcc u us b = below u (≤<-trans (≤-trans ≤SumLeft b) s<n)

      tailB : (u : Tree L) (us : List (Tree L)) → sizes (u ∷ us) ≤ s
            → sizes us ≤ s
      tailB u us b = ≤-trans ≤SumRight b

      accE : (k : ℕ) (p : BL) → length (p .fst) ≡ k → Acc _≺ᵉ_ p
      accE zero ([] , b) q = acc λ where
        ([] , _) (_ , r) → Empty.rec (lower r)
        ((v ∷ vs) , _) (_ , r) → Empty.rec (lower r)
      accE zero ((u ∷ us) , b) q = Empty.rec (snotz q)
      accE (suc k) ([] , b) q = Empty.rec (znots q)
      accE (suc k) ((u ∷ us) , b) q =
        goE u (headAcc u us b) us (injSuc q) b
          (accE k (us , tailB u us b) (injSuc q))
        where
        goE : (u' : Tree L) → Acc _≺ᵗ_ u'
            → (us' : List (Tree L)) → length us' ≡ k
            → (b' : sizes (u' ∷ us') ≤ s)
            → Acc _≺ᵉ_ (us' , tailB u' us' b')
            → Acc _≺ᵉ_ ((u' ∷ us') , b')
        goE u' (acc ru) = inner
          where
          inner : (us' : List (Tree L)) → length us' ≡ k
                → (b' : sizes (u' ∷ us') ≤ s)
                → Acc _≺ᵉ_ (us' , tailB u' us' b')
                → Acc _≺ᵉ_ ((u' ∷ us') , b')
          inner us' lq b' (acc rus) = acc (λ where
            ([] , _) (_ , r) → Empty.rec (lower r)
            ((v ∷ vs) , bv) (le , inl v≺u') →
              goE v (ru v v≺u') vs (injSuc (lower le) ∙ lq) bv
                (accE k (vs , tailB v vs bv) (injSuc (lower le) ∙ lq))
            ((v ∷ vs) , bv) (le , inr (ve , tailrel)) →
              let b'' = subst (λ x → sizes (x ∷ vs) ≤ s) (lower ve) bv
              in subst (λ z → Acc _≺ᵉ_ z)
                   (Σ≡Prop (λ _ → isProp≤)
                     {u = (u' ∷ vs) , b''} {v = (v ∷ vs) , bv}
                     (cong (_∷ vs) (sym (lower ve))))
                   (inner vs (injSuc (lower le) ∙ lq) b''
                     (rus (vs , tailB u' vs b'')
                       (lift (injSuc (lower le)) , tailrel))))

      accL : (k : ℕ) (p : BL) → length (p .fst) < k → Acc _≺ᴮ_ p
      accL zero p q = Empty.rec (¬-<-zero q)
      accL (suc k) p q = inner p (accE (length (p .fst)) p refl) q
        where
        inner : (p' : BL) → Acc _≺ᵉ_ p' → length (p' .fst) < suc k
              → Acc _≺ᴮ_ p'
        inner p' (acc re) q' = acc step
          where
          step : (p'' : BL) → p'' ≺ᴮ p' → Acc _≺ᴮ_ p''
          step p'' (inl len<) =
            accL k p'' (≤-trans (lower len<) (pred-≤-pred q'))
          step p'' (inr (le , edesc)) =
            inner p'' (re p'' (le , edesc))
              (subst (λ m → m < suc k) (sym (lower le)) q')

      nodeAcc : (l' : L) → Acc _<ᴸ_ l'
              → (cs' : List (Tree L)) (se : sizes cs' ≡ s)
              → Acc _≺ᵗ_ (node l' cs')
      nodeAcc l' (acc rl) = goN
        where
        goN : (cs' : List (Tree L)) (se : sizes cs' ≡ s)
            → Acc _≺ᵗ_ (node l' cs')
        goN cs' se = inner cs' se
          (accL (suc s) (cs' , eqBnd cs' se)
            (suc-≤-suc (≤-trans (len≤sizes cs') (eqBnd cs' se))))
          where
          inner : (cs'' : List (Tree L)) (se' : sizes cs'' ≡ s)
                → Acc _≺ᴮ_ (cs'' , eqBnd cs'' se')
                → Acc _≺ᵗ_ (node l' cs'')
          inner cs₀ se₀ (acc rcs) = acc (λ where
            (node l'' cs'') (inl sz<) → below (node l'' cs'')
              (≤<-trans (subst (λ x → suc (sizes cs'') ≤ x) se₀ (lower sz<))
                s<n)
            (node l'' cs'') (inr (se'' , inl l''<)) →
              nodeAcc l'' (rl l'' l''<) cs'' (lower se'' ∙ se₀)
            (node l'' cs'') (inr (se'' , inr (le , csrel))) →
              subst (λ x → Acc _≺ᵗ_ (node x cs'')) (sym (lower le))
                (inner cs'' (lower se'' ∙ se₀)
                  (rcs (cs'' , eqBnd cs'' (lower se'' ∙ se₀)) csrel)))

    SA : (n : ℕ) (t : Tree L) → size t < n → Acc _≺ᵗ_ t
    SA zero t q = Empty.rec (¬-<-zero q)
    SA (suc n) (node l cs) q = C.nodeAcc l (SWO.wf∙ w l) cs refl
      where
      module C = Class n (SA n) (sizes cs) (pred-≤-pred q)

  wfᵗ : WellFounded _≺ᵗ_
  wfᵗ t = SA (suc (size t)) t ≤-refl
```

<!--en-->
## The bundle
<!--zh-->
## 打包
<!--/-->

<!--en-->
The four laws assemble into the record the well-order chapters consume: given
a strict well-order on the alphabet, the finite labelled trees over it carry
one.
<!--zh-->
四条定律装进良序诸章所消费的那个 record：给定字母表上的严格良序，其上的有穷带标签树也带一个。
<!--/-->

```agda
  treeSWO : SWO (Tree L)
  treeSWO = record
    { _<∙_   = _≺ᵗ_
    ; tri∙   = triᵗ
    ; irr∙   = irrᵗ
    ; trans∙ = transᵗ
    ; wf∙    = wfᵗ }
```
