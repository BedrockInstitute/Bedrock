# The prefix table, internally

<!--en-->
The meta closure of the previous chapter is the semantics this chapter
describes from the inside. The internal object is the finite prefix table: the
levels up to a bound, carried as one set of entries, each entry a pair of a
composite key (level numeral, arity numeral) with the slice value at that key.
Nothing infinite is quantified, and nothing is certified: functionality plus
the base clauses plus the successor clause determine every entry from the
entries below, so a meta-induction on the level numeral pins any satisfying
table into the meta slices. This is the option-B determination discipline, the
direct internal replacement for the certificate the delivered route carried.
<!--zh-->
上一章的元层闭包是本章从内部描述的对象。内部对象是有穷前缀表：到某个界为止的诸层，作为一组条目被携带，每条目是「复合键 (层级数码，元数码) 与其键处片值」的对。没有无穷的东西被量化，也没有任何证书：函数性加上基子句与后继子句，从下方诸条目决定每条条目，故对层级数码的元层归纳就把任何满足描述的表钉进元层诸片。这就是选项 B 的决定纪律，也是已交付路线所携证书的直接内部替代。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth

module L.Godel.Levels {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #-inj′; #mono )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; sucʟ; sucʟ-fst )
open import L.Ordinal {ℓ} using ( #∈#-elim )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate
        ; appAt; appAt-adequate; sucAtL; sucAtL-adequate; extAt )
open import L.Godel.Operations {ℓ}
  using ( values; _∩_; _∪_; ∪-left; ∪-right; ∪-out; _∖_
        ; singleton-self; singleton-in; singleton-out
        ; selectMember; selectEqual; shiftDown; extendFamily )
open import L.Godel.Definable {ℓ}
  using ( module Describes
        ; interAt; interAt-out; interAt-in
        ; unionAt; unionAt-out; unionAt-in
        ; diffAt; diffAt-out; diffAt-in
        ; selectMemberAt; selectMemberAt-out; selectMemberAt-in
        ; selectEqualAt; selectEqualAt-out; selectEqualAt-in
        ; valuesAt; valuesAt-out; valuesAt-in
        ; allTuplesAt; allTuplesAt-out; allTuplesAt-in
        ; shiftDownAt; shiftDownAt-out; shiftDownAt-in
        ; extendFamilyAt; extendFamilyAt-out; extendFamilyAt-in )
open import L.Godel.Tuples {ℓ} using ( allTuples )
import L.Godel.Closure
open import L.Coding.InL {ℓ} using ( sglL )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( _+_; +-zero; +-suc )
open import Cubical.Data.Nat.Order using ( _<_; _≤_; suc-≤-suc; ≤-refl; ≤-split; ≤-trans; ≤-sucℕ; isProp≤ )
open import Cubical.Data.FinData using ( Fin; toℕ )
open import Cubical.Data.Unit using ( Unit*; tt* )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )



private
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

  sh7 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc (suc n)))))))
  sh7 x = suc (suc (suc (suc (suc (suc (suc x))))))

  sh8 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
  sh8 x = suc (suc (suc (suc (suc (suc (suc (suc x)))))))

  sh9 : ∀ {n} → Fin n → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
  sh9 x = suc (suc (suc (suc (suc (suc (suc (suc (suc x))))))))

module _ (A : V ℓ) where
  -- The singleton family and its two membership laws are restated locally:
  -- the closure chapter's copies are only reachable through abbreviations
  -- that the elaborator cannot unify against this chapter's carrier, so the
  -- six lines are written out, line for line, per the B1/B2 precedent.
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

  -- The layer of new families at level n, arity k: the entries the successor
  -- clause joins into the previous entry.  One disjunctive formula over the
  -- slots (layer b, previous table p, level numeral l, arity numeral k,
  -- carrier a): a member of the layer is a family arising as one of the nine
  -- operation images, whose arguments the disjuncts read from the previous
  -- entries at the composite keys the level and arity numerals determine.

  -- InterDisjAt e p l k a: the member at e is X ∩ Y for members X, Y of the
  -- previous entry at the key (l, k).  Binders (outer to inner): κ, S, X, Y;
  -- env Y ∷ X ∷ S ∷ κ ∷ γ.
  InterDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  InterDisjAt e p l k a = ∃̇ (∃̇ (∃̇ (∃̇ (
      prAtL (suc (suc (suc zero))) (sh4 l) (sh4 k)
    ∧̇ ( appAt (sh4 p) (suc (suc (suc zero))) (suc (suc zero))
      ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
        ∧̇ ( (var zero ∈̇ var (suc (suc zero)))
          ∧̇ interAt (sh4 e) (suc zero) zero ) ))))))

  UnionDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  UnionDisjAt e p l k a = ∃̇ (∃̇ (∃̇ (∃̇ (
      prAtL (suc (suc (suc zero))) (sh4 l) (sh4 k)
    ∧̇ ( appAt (sh4 p) (suc (suc (suc zero))) (suc (suc zero))
      ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
        ∧̇ ( (var zero ∈̇ var (suc (suc zero)))
          ∧̇ unionAt (sh4 e) (suc zero) zero ) ))))))

  DiffDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  DiffDisjAt e p l k a = ∃̇ (∃̇ (∃̇ (∃̇ (
      prAtL (suc (suc (suc zero))) (sh4 l) (sh4 k)
    ∧̇ ( appAt (sh4 p) (suc (suc (suc zero))) (suc (suc zero))
      ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
        ∧̇ ( (var zero ∈̇ var (suc (suc zero)))
          ∧̇ diffAt (sh4 e) (suc zero) zero ) ))))))

  -- SelMDisjAt e p l k a: the member at e is selectMember X ⁅i⁆s ⁅j⁆s for a
  -- member X of the previous entry at (l, k) and indices i, j of the arity
  -- numeral k.  Binders: κ, S, X, i, j; env j ∷ i ∷ X ∷ S ∷ κ ∷ γ.
  SelMDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  SelMDisjAt e p l k a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (
      prAtL (suc (suc (suc (suc zero)))) (sh5 l) (sh5 k)
    ∧̇ ( appAt (sh5 p) (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
      ∧̇ ( (var (suc (suc zero)) ∈̇ var (suc (suc (suc zero))))
        ∧̇ ( (var (suc zero) ∈̇ var (sh5 k))
          ∧̇ ( (var zero ∈̇ var (sh5 k))
            ∧̇ selectMemberAt (sh5 e) (suc (suc zero))
                (suc zero) zero ) ) )))))))

  SelEDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  SelEDisjAt e p l k a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (
      prAtL (suc (suc (suc (suc zero)))) (sh5 l) (sh5 k)
    ∧̇ ( appAt (sh5 p) (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
      ∧̇ ( (var (suc (suc zero)) ∈̇ var (suc (suc (suc zero))))
        ∧̇ ( (var (suc zero) ∈̇ var (sh5 k))
          ∧̇ ( (var zero ∈̇ var (sh5 k))
            ∧̇ selectEqualAt (sh5 e) (suc (suc zero))
                (suc zero) zero ) ) )))))))

  -- AllTuplesDisjAt e a k: the member at e is the tuple family at the arity
  -- numeral k over the carrier a.
  AllTuplesDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  AllTuplesDisjAt e a k = allTuplesAt e a k

  -- ExtDisjAt e p l k a: the member at e is extendFamily X ⁅y⁆s for a member
  -- X of the previous entry at the key (l, s) with s the predecessor of k,
  -- and a member y of the carrier.  Binders: s, κ, S, X, y;
  -- env y ∷ X ∷ S ∷ κ ∷ s ∷ γ.
  ExtDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  ExtDisjAt e p l k a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (
      sucAtL (suc (suc (suc (suc zero)))) (sh5 k)
    ∧̇ ( prAtL (suc (suc (suc zero))) (sh5 l) (suc (suc (suc (suc zero))))
      ∧̇ ( appAt (sh5 p) (suc (suc (suc zero))) (suc (suc zero))
        ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
          ∧̇ ( (var zero ∈̇ var (sh5 a))
            ∧̇ extendFamilyAt (sh5 e) (suc zero) zero ) ) )))))))

  -- ShiftDisjAt e p l k: the member at e is shiftDown X for a member X of the
  -- previous entry at the key (l, s) with s = suc k.  Binders: s, κ, S, X;
  -- env X ∷ S ∷ κ ∷ s ∷ γ.
  ShiftDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  ShiftDisjAt e p l k = ∃̇ (∃̇ (∃̇ (∃̇ (
      sucAtL (sh4 k) (suc (suc (suc zero)))
    ∧̇ ( prAtL (suc (suc zero)) (sh4 l) (suc (suc (suc zero)))
      ∧̇ ( appAt (sh4 p) (suc (suc zero)) (suc zero)
        ∧̇ ( (var zero ∈̇ var (suc zero))
          ∧̇ shiftDownAt (sh4 e) zero ) ))))))

  -- ValuesDisjAt e p l: the member at e is values X for a member X of the
  -- previous entry at the key (l, n1) with n1 the numeral one.  Binders:
  -- n1, κ, S, X; env X ∷ S ∷ κ ∷ n1 ∷ γ.
  ValuesDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  ValuesDisjAt e p l = ∃̇ (∃̇ (∃̇ (∃̇ (
      var (suc (suc (suc zero))) ≐ con (numeralL 1)
    ∧̇ ( prAtL (suc (suc zero)) (sh4 l) (suc (suc (suc zero)))
      ∧̇ ( appAt (sh4 p) (suc (suc zero)) (suc zero)
        ∧̇ ( (var zero ∈̇ var (suc zero))
          ∧̇ valuesAt (sh4 e) zero ) ))))))

  LayerDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  LayerDisjAt e p l k a =
      InterDisjAt e p l k a
    ∨̇ ( UnionDisjAt e p l k a
    ∨̇ ( DiffDisjAt e p l k a
    ∨̇ ( SelMDisjAt e p l k a
    ∨̇ ( SelEDisjAt e p l k a
    ∨̇ ( AllTuplesDisjAt e a k
    ∨̇ ( ExtDisjAt e p l k a
    ∨̇ ( ShiftDisjAt e p l k
    ∨̇ ValuesDisjAt e p l )))))))

  -- The layer description over slots: every member of the layer slot b is one
  -- of the operation images, at the level and arity the numeral slots hold.
  LayerAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  LayerAt b p l k a =
    ∀̇ ( (var zero ∈̇ var (suc b)) ⇒̇
          LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) )

  -- The prefix table's functionality at the composite key, Tower's FunAt
  -- idiom: two entries with the same key agree on their value.
  FunAt : ∀ {n} → Fin n → Formula S n
  FunAt t = ∀̇ (∀̇ (∀̇ (
      ( appAt (sh3 t) (suc (suc zero)) (suc zero)
      ∧̇ appAt (sh3 t) (suc (suc zero)) zero )
    ⇒̇ (var (suc zero) ≐ var zero) )))

  -- The singleton-atom class and the singleton-family description are
  -- restated locally: `sglAt′` and the description are private in the bridge
  -- and closure chapters, exactly as B1 and B2 restated private machinery.
  private
    sglAt′ : {ℓ' : Level} {K : Type ℓ'} {n : ℕ} → Fin n → Fin n → Formula K n
    sglAt′ k i = (var i ∈̇ var k) ∧̇ (∀̇∈ (var k) (var zero ≐ var (suc i)))

  module SglDesc where
    SL : Type (ℓ-suc ℓ)
    SL = Σ[ x ∈ V ℓ ] ⟨ isL x ⟩

    singletonsAt : {n : ℕ} → Fin n → Fin n → Formula SL n
    singletonsAt {n} k i =
      extAt k (∃̇∈ (var (suc i)) (sglAt′ {n = suc (suc n)} (suc zero) zero))

  module _ {n : ℕ} (k i : Fin n) (γ : SglDesc.SL ^ n) where
    private
      X : V ℓ
      X = fst (lookup i γ)

      Φ : Formula SglDesc.SL (suc n)
      Φ = ∃̇∈ (var (suc i)) (sglAt′ {n = suc (suc n)} (suc zero) zero)

      memL : (y : V ℓ) → ⟨ y ∈ singletons X ⟩ → ⟨ isL y ⟩
      memL y hy = PT.rec (snd (isL y))
        (λ { (x , hx , e) → subst (λ w → ⟨ isL w ⟩) (sym e)
          (sglL (isL-trans {x = X} {y = x} hx (lookup i γ .snd))) })
        (L.Godel.Closure.singletons-out A {X} {y} hy)

      read : (z : SglDesc.SL) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ singletons X ⟩
      read z hz = PT.rec (snd (fst z ∈ singletons X)) build hz
        where
        build : Σ[ x ∈ SglDesc.SL ] (⟨ fst x ∈ˢ fst (lookup i γ) ⟩
                 × ⟨ (x ∷ z ∷ γ) ⊨ sglAt′ {n = suc (suc n)} (suc zero) zero ⟩)
              → ⟨ fst z ∈ singletons X ⟩
        build (x , hx , s) =
          let z≡ : fst z ≡ ⁅ fst x ⁆s
              z≡ = extensionality (fst z) ⁅ fst x ⁆s (sub₁ , sub₂)
          in subst (λ w → ⟨ w ∈ singletons X ⟩) (sym z≡)
               (L.Godel.Closure.singletons-in A {X} {fst x} hx)
          where
          sub₁ : ⟨ fst z ⊆ ⁅ fst x ⁆s ⟩
          sub₁ v v∈ₛ = ∈∈ₛ {a = v} {b = ⁅ fst x ⁆s} .fst
            (singleton-in (s₂ v v∈z))
            where
            v∈z : ⟨ v ∈ fst z ⟩
            v∈z = ∈∈ₛ {a = v} {b = fst z} .snd v∈ₛ
            s₂ : (v : V ℓ) → ⟨ v ∈ fst z ⟩ → v ≡ fst x
            s₂ v v∈z = s .snd (v , isL-trans {x = fst z} {y = v} v∈z (z .snd))
                               v∈z
          sub₂ : ⟨ ⁅ fst x ⁆s ⊆ fst z ⟩
          sub₂ v v∈ₛ = ∈∈ₛ {a = v} {b = fst z} .fst
            (subst (λ w → ⟨ w ∈ fst z ⟩)
              (sym (singleton-out (∈∈ₛ {a = v} {b = ⁅ fst x ⁆s} .snd v∈ₛ)))
              (s .fst))

      fill : (z : SglDesc.SL) → ⟨ fst z ∈ singletons X ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
      fill z hz = PT.rec (snd ((z ∷ γ) ⊨ Φ)) build
        (L.Godel.Closure.singletons-out A {X} {fst z} hz)
        where
        build : Σ[ v ∈ V ℓ ] (⟨ v ∈ X ⟩ × (fst z ≡ ⁅ v ⁆s))
              → ⟨ (z ∷ γ) ⊨ Φ ⟩
        build (v , hv , e) =
          ∣ ( v , isL-trans {x = X} {y = v} hv (lookup i γ .snd) )
          , hv
          , ( subst (λ w → ⟨ v ∈ w ⟩) (sym e) (singleton-self v)
            , λ y y∈z →
                singleton-out (subst (λ w → ⟨ fst y ∈ w ⟩) e y∈z) )
          ∣₁

    module D = Describes k Φ γ (singletons X) memL read fill

    singletonsAt-out : ⟨ γ ⊨ SglDesc.singletonsAt k i ⟩
                     → fst (lookup k γ) ≡ singletons X
    singletonsAt-out = D.describes-out

    singletonsAt-in : fst (lookup k γ) ≡ singletons X
                    → ⟨ γ ⊨ SglDesc.singletonsAt k i ⟩
    singletonsAt-in = D.describes-in

  -- The base clause at level zero arity zero: the entry is the singleton
  -- family of the carrier.
  Base0 : ∀ {n} → Fin n → Fin n → Formula S n
  Base0 t a = ∃̇ (∃̇ (∃̇ (∃̇ (
      var (suc (suc (suc zero))) ≐ con (numeralL 0)
    ∧̇ ( var (suc (suc zero)) ≐ con (numeralL 0)
      ∧̇ ( prAtL (suc zero) (suc (suc (suc zero))) (suc (suc zero))
        ∧̇ ( appAt (sh4 t) (suc zero) zero
          ∧̇ SglDesc.singletonsAt zero (sh4 a) )))))))

  -- The base clause at level zero at positive arity: the entry is empty.
  -- Ranges over the predecessor numeral k'' (k = suc k'') with k'' ≤ b.
  inSuc : ∀ {n} → Fin n → Fin n → Formula S n
  inSuc i j = (var i ≐ var j) ∨̇ (var i ∈̇ var j)

  inSucSuc : ∀ {n} → Fin n → Fin n → Formula S n
  inSucSuc i j = ∃̇ ( sucAtL (suc j) zero
                  ∧̇ ∃̇ ( sucAtL (suc zero) zero
                      ∧̇ var (suc (suc i)) ∈̇ var zero ) )

  BaseS : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  BaseS t b a = ∀̇ ( inSuc zero (suc b) ⇒̇
      ∃̇ (∃̇ (∃̇ (∃̇ (
          var (suc (suc (suc zero))) ≐ con (numeralL 0)
        ∧̇ ( sucAtL (suc (suc zero)) (suc (suc (suc (suc zero))))
          ∧̇ ( prAtL (suc zero) (suc (suc (suc zero))) (suc (suc zero))
            ∧̇ ( appAt (sh5 t) (suc zero) zero
              ∧̇ var zero ≐ con ∅ʟ ) )))))))

  -- The successor clause at (n', k') with n' < b and k' ≤ b: the entry at
  -- (suc n', k') is the union of the entry at (n', k') with the layer, whose
  -- members the layer disjunction pins.  Binders (outer to inner): n', k',
  -- s₁, κ₁, κ₂, E', E, L; the layer's own ∀̇ then binds z.
  SucClause : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  SucClause t b a = ∀̇ (∀̇ (
      ( var (suc zero) ∈̇ var (suc (suc b))
      ∧̇ inSuc zero (suc (suc b))
      ⇒̇ ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (
          sucAtL (suc (suc (suc (suc (suc (suc (suc zero)))))))
                (suc (suc (suc (suc (suc zero)))))
        ∧̇ ( prAtL (suc (suc (suc (suc zero))))
              (suc (suc (suc (suc (suc zero)))))
              (suc (suc (suc (suc (suc (suc zero))))))
          ∧̇ ( appAt (sh8 t) (suc (suc (suc (suc zero)))) (suc (suc zero))
            ∧̇ ( prAtL (suc (suc (suc zero)))
                  (suc (suc (suc (suc (suc (suc (suc zero)))))))
                  (suc (suc (suc (suc (suc (suc zero))))))
              ∧̇ ( appAt (sh8 t) (suc (suc (suc zero))) (suc zero)
                ∧̇ ( unionAt (suc (suc zero)) (suc zero) zero
                  ∧̇ ∀̇ ( (var zero ∈̇ var (suc zero)) ⇒̇
                        ( (var zero ∈̇ var (suc (suc zero)))
                        ∨̇ LayerDisjAt zero (sh9 t)
                            (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                            (suc (suc (suc (suc (suc (suc (suc zero)))))))
                            (sh9 a) ) ) ) ) ) ) ) ) ) )))))))

  -- Domain adequacy: every key (n, k) with n ≤ b and k ≤ b + 1 is present.
  DomAdeq : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  DomAdeq t b a = ∀̇ (∀̇ (
      ( inSuc (suc zero) (suc (suc b))
      ∧̇ inSucSuc zero (suc (suc b))
      ⇒̇ ∃̇ (∃̇ (
          prAtL (suc zero) (suc (suc (suc zero))) (suc (suc zero))
        ∧̇ appAt (sh4 t) (suc zero) zero ) ) )))

  PrefixAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  PrefixAt t b a =
      FunAt t
    ∧̇ ( Base0 t a
    ∧̇ ( BaseS t b a
    ∧̇ ( SucClause t b a
    ∧̇ DomAdeq t b a )))

  -- The layer readers, per disjunct, at the meta numerals the slots hold.
  -- The out-reader turns a disjunct's satisfaction at the member z into the
  -- meta shape: the previous entry S at the composite key, the arguments as
  -- members of S, and the operation equation.  The in-reader builds the
  -- satisfaction back from the shape.
  -- The meta level family is private in the closure chapter (its tag
  -- structure is sealed there), so the semantics this chapter describes are
  -- restated locally, line for line, exactly as B1 and B2 restated private
  -- machinery: the kinded levels `slice`, the step of operation images, the
  -- membership laws one per clause, and the disjunctive inversion.
  private
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
        extendFamily (⟪ slice n (suc k) ⟫↪ m) ⁅ ⟪ A ⟫↪ a ⁆s
      stepImage {n} {k} tagShift m = shiftDown (⟪ slice n (suc k) ⟫↪ m)
      stepImage {n} {zero} tagValues m = values (⟪ slice n 1 ⟫↪ m)

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
                        → ⟨ X ∈ slice n (suc k) ⟩ → ⟨ ⁅ ⟪ A ⟫↪ a ⁆s ∈ slice n 0 ⟩
                        → ⟨ extendFamily X ⁅ ⟪ A ⟫↪ a ⁆s ∈ slice (suc n) (suc (suc k)) ⟩
  slice-extendFamily-in {n} {k} {X} a hX ha =
    ∪-right {X = slice n (suc (suc k))} {Y = step n (suc (suc k))}
      ∣ (tagExt , (fX .fst , fa .fst))
      , cong₂ extendFamily (fX .snd) (cong ⁅_⁆s (fa .snd)) ∣₁
    where
    fX : Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] (⟪ slice n (suc k) ⟫↪ m ≡ X)
    fX = ∈-asFiber {a = X} {b = slice n (suc k)} hX
    fa : Σ[ m ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ m ≡ ⟪ A ⟫↪ a)
    fa = ∈-asFiber {a = ⟪ A ⟫↪ a} {b = A}
      (∈∈ₛ {a = ⟪ A ⟫↪ a} {b = A} .snd (∈ₛ⟪ A ⟫↪ a))

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

  module LayerLaws {n : ℕ} (b p l k a : Fin n) (γ : S ^ n) where
    InterDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ InterDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ] Σ[ Y ∈ S ]
           ( ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩ × ⟨ fst Y ∈ fst W ⟩
           × (fst z ≡ fst X ∩ fst Y) ) ∥₁
    InterDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (κ , w₁) →
      PT.rec squash₁ (λ { (W , w₂) → PT.rec squash₁ (λ { (X , w₃) →
        PT.rec squash₁ (λ { (Y , body) →
          let env = Y ∷ X ∷ W ∷ κ ∷ z ∷ γ
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                      (sh5 l) (sh5 k) env) (body .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh5 p)
                       (suc (suc (suc zero))) (suc (suc zero)) env)
                       (body .snd .fst)
              hX = body .snd .snd .fst
              hY = body .snd .snd .snd .fst
              hInter = body .snd .snd .snd .snd
              key : fst κ ≡ pr (# n₀) (# k₀)
              key = hPr ∙ cong₂ pr ql qk
              eS : ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
              eS = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     key hApp
              e : fst z ≡ fst X ∩ fst Y
              e = interAt-out (sh4 zero) (suc zero) zero env hInter
          in ∣ W , X , Y , (eS , (hX , (hY , e))) ∣₁ }) w₃ }) w₂ }) w₁ }) hz

    UnionDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ UnionDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ] Σ[ Y ∈ S ]
           ( ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩ × ⟨ fst Y ∈ fst W ⟩
           × (fst z ≡ fst X ∪ fst Y) ) ∥₁
    UnionDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (κ , w₁) →
      PT.rec squash₁ (λ { (W , w₂) → PT.rec squash₁ (λ { (X , w₃) →
        PT.rec squash₁ (λ { (Y , body) →
          let env = Y ∷ X ∷ W ∷ κ ∷ z ∷ γ
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                      (sh5 l) (sh5 k) env) (body .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh5 p)
                       (suc (suc (suc zero))) (suc (suc zero)) env)
                       (body .snd .fst)
              hX = body .snd .snd .fst
              hY = body .snd .snd .snd .fst
              hUn = body .snd .snd .snd .snd
              key : fst κ ≡ pr (# n₀) (# k₀)
              key = hPr ∙ cong₂ pr ql qk
              eS : ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
              eS = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     key hApp
              e : fst z ≡ fst X ∪ fst Y
              e = unionAt-out (sh4 zero) (suc zero) zero env hUn
          in ∣ W , X , Y , (eS , (hX , (hY , e))) ∣₁ }) w₃ }) w₂ }) w₁ }) hz

    DiffDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ DiffDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ] Σ[ Y ∈ S ]
           ( ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩ × ⟨ fst Y ∈ fst W ⟩
           × (fst z ≡ fst X ∖ fst Y) ) ∥₁
    DiffDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (κ , w₁) →
      PT.rec squash₁ (λ { (W , w₂) → PT.rec squash₁ (λ { (X , w₃) →
        PT.rec squash₁ (λ { (Y , body) →
          let env = Y ∷ X ∷ W ∷ κ ∷ z ∷ γ
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                      (sh5 l) (sh5 k) env) (body .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh5 p)
                       (suc (suc (suc zero))) (suc (suc zero)) env)
                       (body .snd .fst)
              hX = body .snd .snd .fst
              hY = body .snd .snd .snd .fst
              hDi = body .snd .snd .snd .snd
              key : fst κ ≡ pr (# n₀) (# k₀)
              key = hPr ∙ cong₂ pr ql qk
              eS : ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
              eS = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     key hApp
              e : fst z ≡ fst X ∖ fst Y
              e = diffAt-out (sh4 zero) (suc zero) zero env hDi
          in ∣ W , X , Y , (eS , (hX , (hY , e))) ∣₁ }) w₃ }) w₂ }) w₁ }) hz

    SelMDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ SelMDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ] Σ[ i ∈ S ] Σ[ j ∈ S ]
           ( ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩ × ⟨ fst i ∈ # k₀ ⟩ × ⟨ fst j ∈ # k₀ ⟩
           × (fst z ≡ selectMember (fst X) ⁅ fst i ⁆s ⁅ fst j ⁆s) ) ∥₁
    SelMDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (κ , w₁) →
      PT.rec squash₁ (λ { (W , w₂) → PT.rec squash₁ (λ { (X , w₃) →
        PT.rec squash₁ (λ { (i , w₄) → PT.rec squash₁ (λ { (j , body) →
          let env = j ∷ i ∷ X ∷ W ∷ κ ∷ z ∷ γ
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                      (sh6 l) (sh6 k) env) (body .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh6 p)
                       (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) env)
                       (body .snd .fst)
              hX = body .snd .snd .fst
              hi = subst (λ q → ⟨ fst i ∈ q ⟩) qk (body .snd .snd .snd .fst)
              hj = subst (λ q → ⟨ fst j ∈ q ⟩) qk (body .snd .snd .snd .snd .fst)
              hSel = body .snd .snd .snd .snd .snd
              key : fst κ ≡ pr (# n₀) (# k₀)
              key = hPr ∙ cong₂ pr ql qk
              eS : ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
              eS = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     key hApp
              e : fst z ≡ selectMember (fst X) ⁅ fst i ⁆s ⁅ fst j ⁆s
              e = selectMemberAt-out (sh5 zero) (suc (suc zero))
                    (suc zero) zero env hSel
          in ∣ W , X , i , j , (eS , (hX , (hi , (hj , e)))) ∣₁ })
        w₄ }) w₃ }) w₂ }) w₁ }) hz

    SelEDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ SelEDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ] Σ[ i ∈ S ] Σ[ j ∈ S ]
           ( ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩ × ⟨ fst i ∈ # k₀ ⟩ × ⟨ fst j ∈ # k₀ ⟩
           × (fst z ≡ selectEqual (fst X) ⁅ fst i ⁆s ⁅ fst j ⁆s) ) ∥₁
    SelEDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (κ , w₁) →
      PT.rec squash₁ (λ { (W , w₂) → PT.rec squash₁ (λ { (X , w₃) →
        PT.rec squash₁ (λ { (i , w₄) → PT.rec squash₁ (λ { (j , body) →
          let env = j ∷ i ∷ X ∷ W ∷ κ ∷ z ∷ γ
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                      (sh6 l) (sh6 k) env) (body .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh6 p)
                       (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) env)
                       (body .snd .fst)
              hX = body .snd .snd .fst
              hi = subst (λ q → ⟨ fst i ∈ q ⟩) qk (body .snd .snd .snd .fst)
              hj = subst (λ q → ⟨ fst j ∈ q ⟩) qk (body .snd .snd .snd .snd .fst)
              hEq = body .snd .snd .snd .snd .snd
              key : fst κ ≡ pr (# n₀) (# k₀)
              key = hPr ∙ cong₂ pr ql qk
              eS : ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
              eS = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     key hApp
              e : fst z ≡ selectEqual (fst X) ⁅ fst i ⁆s ⁅ fst j ⁆s
              e = selectEqualAt-out (sh5 zero) (suc (suc zero))
                    (suc zero) zero env hEq
          in ∣ W , X , i , j , (eS , (hX , (hi , (hj , e)))) ∣₁ })
        w₄ }) w₃ }) w₂ }) w₁ }) hz

    AllTuplesDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ AllTuplesDisjAt zero (suc a) (suc k) ⟩
      → fst (lookup k γ) ≡ # k₀
      → fst z ≡ allTuples (fst (lookup a γ)) k₀
    AllTuplesDisj-out n₀ k₀ z hz qk =
      allTuplesAt-out zero (suc a) (suc k) (z ∷ γ) k₀ qk' hz
      where
      qk' : fst (lookup (suc k) (z ∷ γ)) ≡ # k₀
      qk' = qk

    ExtDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ ExtDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ s ∈ S ] Σ[ W ∈ S ] Σ[ X ∈ S ] Σ[ y ∈ S ]
           ( ⟨ fst s ∈ # k₀ ⟩
           × ⟨ pr (pr (# n₀) (fst s)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩ × ⟨ fst y ∈ fst (lookup a γ) ⟩
           × (fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s) ) ∥₁
    ExtDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (s , w₁) →
      PT.rec squash₁ (λ { (κ , w₂) → PT.rec squash₁ (λ { (W , w₃) →
        PT.rec squash₁ (λ { (X , w₄) → PT.rec squash₁ (λ { (y , body) →
          let env = y ∷ X ∷ W ∷ κ ∷ s ∷ z ∷ γ
              hSuc = subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc (suc zero)))) (sh6 k)
                       env) (body .fst)
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                      (sh6 l) (suc (suc (suc (suc zero)))) env) (body .snd .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh6 p)
                       (suc (suc (suc zero))) (suc (suc zero)) env) (body .snd .snd .fst)
              hX = body .snd .snd .snd .fst
              hy = body .snd .snd .snd .snd .fst
              hEx = body .snd .snd .snd .snd .snd
              es : sucV (fst s) ≡ # k₀
              es = sym hSuc ∙ qk
              hs : ⟨ fst s ∈ # k₀ ⟩
              hs = subst (λ q → ⟨ fst s ∈ q ⟩) es (self∈sucV (fst s))
              eW : ⟨ pr (pr (# n₀) (fst s)) (fst W) ∈ fst (lookup p γ) ⟩
              eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     (hPr ∙ cong₂ pr ql refl) hApp
              e : fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
              e = extendFamilyAt-out (sh5 zero) (suc zero) zero env hEx
          in ∣ s , W , X , y , (hs , (eW , (hX , (hy , e)))) ∣₁ })
        w₄ }) w₃ }) w₂ }) w₁ }) hz

    ShiftDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ ShiftDisjAt zero (suc p) (suc l) (suc k) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ]
           ( ⟨ pr (pr (# n₀) (sucV (# k₀))) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩
           × (fst z ≡ shiftDown (fst X)) ) ∥₁
    ShiftDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (s , w₁) →
      PT.rec squash₁ (λ { (κ , w₂) → PT.rec squash₁ (λ { (W , w₃) →
        PT.rec squash₁ (λ { (X , body) →
          let env = X ∷ W ∷ κ ∷ s ∷ z ∷ γ
              hSuc = subst ⟨_⟩ (sucAtL-adequate (sh5 k)
                       (suc (suc (suc zero))) env) (body .fst)
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc zero))
                      (sh5 l) (suc (suc (suc zero))) env) (body .snd .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh5 p)
                       (suc (suc zero)) (suc zero) env) (body .snd .snd .fst)
              hX = body .snd .snd .snd .fst
              hSh = body .snd .snd .snd .snd
              es : fst s ≡ sucV (# k₀)
              es = hSuc ∙ cong sucV qk
              eW : ⟨ pr (pr (# n₀) (sucV (# k₀))) (fst W) ∈ fst (lookup p γ) ⟩
              eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     (hPr ∙ cong₂ pr ql es) hApp
              e : fst z ≡ shiftDown (fst X)
              e = shiftDownAt-out (sh4 zero) zero env hSh
          in ∣ W , X , (eW , (hX , e)) ∣₁ }) w₃ }) w₂ }) w₁ }) hz



    ValuesDisj-out : (n₀ k₀ : ℕ) (z : S)
      → ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc p) (suc l) ⟩
      → fst (lookup l γ) ≡ # n₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ]
           ( ⟨ pr (pr (# n₀) (# 1)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩
           × (fst z ≡ values (fst X)) ) ∥₁
    ValuesDisj-out n₀ k₀ z hz ql = PT.rec squash₁ (λ { (n1 , w₁) →
      PT.rec squash₁ (λ { (κ , w₂) → PT.rec squash₁ (λ { (W , w₃) →
        PT.rec squash₁ (λ { (X , body) →
          let env = X ∷ W ∷ κ ∷ n1 ∷ z ∷ γ
              hN1 = body .fst
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc zero))
                      (sh5 l) (suc (suc (suc zero))) env) (body .snd .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh5 p)
                       (suc (suc zero)) (suc zero) env) (body .snd .snd .fst)
              hX = body .snd .snd .snd .fst
              hV = body .snd .snd .snd .snd
              en1 : fst n1 ≡ # 1
              en1 = hN1 ∙ numeralL-fst 1
              eW : ⟨ pr (pr (# n₀) (# 1)) (fst W) ∈ fst (lookup p γ) ⟩
              eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     (hPr ∙ cong₂ pr ql en1) hApp
              e : fst z ≡ values (fst X)
              e = valuesAt-out (sh4 zero) zero env hV
          in ∣ W , X , (eW , (hX , e)) ∣₁ }) w₃ }) w₂ }) w₁ }) hz
    InterDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X Y : S) → ⟨ fst X ∈ fst W ⟩ → ⟨ fst Y ∈ fst W ⟩ → fst z ≡ fst X ∩ fst Y
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ InterDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
    InterDisj-in n₀ k₀ z W eW X Y hX hY e ql qk =
      ∣ κ , ∣ W , ∣ X , ∣ Y , (hPr , (hApp , (hX , (hY , hInter)))) ∣₁ ∣₁ ∣₁ ∣₁
      where
      κ : S
      κ = prʟ (numeralL n₀) (numeralL k₀)
      env = Y ∷ X ∷ W ∷ κ ∷ z ∷ γ
      κ≡ : fst κ ≡ pr (# n₀) (# k₀)
      κ≡ = prʟ-fst (numeralL n₀) (numeralL k₀)
        ∙ cong₂ pr (numeralL-fst n₀) (numeralL-fst k₀)
      hPr : ⟨ env ⊨ prAtL (suc (suc (suc zero))) (sh5 l) (sh5 k) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
              (sh5 l) (sh5 k) env)) (κ≡ ∙ sym (cong₂ pr ql qk))
      hApp : ⟨ env ⊨ appAt (sh5 p) (suc (suc (suc zero))) (suc (suc zero)) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh5 p)
               (suc (suc (suc zero))) (suc (suc zero)) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hInter : ⟨ env ⊨ interAt (sh4 zero) (suc zero) zero ⟩
      hInter = interAt-in (sh4 zero) (suc zero) zero env e

    UnionDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X Y : S) → ⟨ fst X ∈ fst W ⟩ → ⟨ fst Y ∈ fst W ⟩ → fst z ≡ fst X ∪ fst Y
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ UnionDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
    UnionDisj-in n₀ k₀ z W eW X Y hX hY e ql qk =
      ∣ κ , ∣ W , ∣ X , ∣ Y , (hPr , (hApp , (hX , (hY , hUn)))) ∣₁ ∣₁ ∣₁ ∣₁
      where
      κ : S
      κ = prʟ (numeralL n₀) (numeralL k₀)
      env = Y ∷ X ∷ W ∷ κ ∷ z ∷ γ
      κ≡ : fst κ ≡ pr (# n₀) (# k₀)
      κ≡ = prʟ-fst (numeralL n₀) (numeralL k₀)
        ∙ cong₂ pr (numeralL-fst n₀) (numeralL-fst k₀)
      hPr : ⟨ env ⊨ prAtL (suc (suc (suc zero))) (sh5 l) (sh5 k) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
              (sh5 l) (sh5 k) env)) (κ≡ ∙ sym (cong₂ pr ql qk))
      hApp : ⟨ env ⊨ appAt (sh5 p) (suc (suc (suc zero))) (suc (suc zero)) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh5 p)
               (suc (suc (suc zero))) (suc (suc zero)) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hUn : ⟨ env ⊨ unionAt (sh4 zero) (suc zero) zero ⟩
      hUn = unionAt-in (sh4 zero) (suc zero) zero env e

    DiffDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X Y : S) → ⟨ fst X ∈ fst W ⟩ → ⟨ fst Y ∈ fst W ⟩ → fst z ≡ fst X ∖ fst Y
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ DiffDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
    DiffDisj-in n₀ k₀ z W eW X Y hX hY e ql qk =
      ∣ κ , ∣ W , ∣ X , ∣ Y , (hPr , (hApp , (hX , (hY , hDi)))) ∣₁ ∣₁ ∣₁ ∣₁
      where
      κ : S
      κ = prʟ (numeralL n₀) (numeralL k₀)
      env = Y ∷ X ∷ W ∷ κ ∷ z ∷ γ
      κ≡ : fst κ ≡ pr (# n₀) (# k₀)
      κ≡ = prʟ-fst (numeralL n₀) (numeralL k₀)
        ∙ cong₂ pr (numeralL-fst n₀) (numeralL-fst k₀)
      hPr : ⟨ env ⊨ prAtL (suc (suc (suc zero))) (sh5 l) (sh5 k) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
              (sh5 l) (sh5 k) env)) (κ≡ ∙ sym (cong₂ pr ql qk))
      hApp : ⟨ env ⊨ appAt (sh5 p) (suc (suc (suc zero))) (suc (suc zero)) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh5 p)
               (suc (suc (suc zero))) (suc (suc zero)) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hDi : ⟨ env ⊨ diffAt (sh4 zero) (suc zero) zero ⟩
      hDi = diffAt-in (sh4 zero) (suc zero) zero env e

    SelMDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X i j : S) → ⟨ fst X ∈ fst W ⟩ → ⟨ fst i ∈ # k₀ ⟩ → ⟨ fst j ∈ # k₀ ⟩
      → fst z ≡ selectMember (fst X) ⁅ fst i ⁆s ⁅ fst j ⁆s
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ SelMDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
    SelMDisj-in n₀ k₀ z W eW X i j hX hi hj e ql qk =
      ∣ κ , ∣ W , ∣ X , ∣ i , ∣ j ,
          (hPr , (hApp , (hX , (hi' , (hj' , hSel))))) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      κ : S
      κ = prʟ (numeralL n₀) (numeralL k₀)
      env = j ∷ i ∷ X ∷ W ∷ κ ∷ z ∷ γ
      κ≡ : fst κ ≡ pr (# n₀) (# k₀)
      κ≡ = prʟ-fst (numeralL n₀) (numeralL k₀)
        ∙ cong₂ pr (numeralL-fst n₀) (numeralL-fst k₀)
      hPr : ⟨ env ⊨ prAtL (suc (suc (suc (suc zero)))) (sh6 l) (sh6 k) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc zero))))
              (sh6 l) (sh6 k) env)) (κ≡ ∙ sym (cong₂ pr ql qk))
      hApp : ⟨ env ⊨ appAt (sh6 p) (suc (suc (suc (suc zero))))
                  (suc (suc (suc zero))) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh6 p)
               (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hi' : ⟨ env ⊨ var (suc zero) ∈̇ var (sh6 k) ⟩
      hi' = subst (λ q → ⟨ fst i ∈ q ⟩) (sym qk) hi
      hj' : ⟨ env ⊨ var zero ∈̇ var (sh6 k) ⟩
      hj' = subst (λ q → ⟨ fst j ∈ q ⟩) (sym qk) hj
      hSel : ⟨ env ⊨ selectMemberAt (sh5 zero) (suc (suc zero))
                  (suc zero) zero ⟩
      hSel = selectMemberAt-in (sh5 zero) (suc (suc zero)) (suc zero) zero env e

    SelEDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X i j : S) → ⟨ fst X ∈ fst W ⟩ → ⟨ fst i ∈ # k₀ ⟩ → ⟨ fst j ∈ # k₀ ⟩
      → fst z ≡ selectEqual (fst X) ⁅ fst i ⁆s ⁅ fst j ⁆s
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ SelEDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
    SelEDisj-in n₀ k₀ z W eW X i j hX hi hj e ql qk =
      ∣ κ , ∣ W , ∣ X , ∣ i , ∣ j ,
          (hPr , (hApp , (hX , (hi' , (hj' , hEq))))) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      κ : S
      κ = prʟ (numeralL n₀) (numeralL k₀)
      env = j ∷ i ∷ X ∷ W ∷ κ ∷ z ∷ γ
      κ≡ : fst κ ≡ pr (# n₀) (# k₀)
      κ≡ = prʟ-fst (numeralL n₀) (numeralL k₀)
        ∙ cong₂ pr (numeralL-fst n₀) (numeralL-fst k₀)
      hPr : ⟨ env ⊨ prAtL (suc (suc (suc (suc zero)))) (sh6 l) (sh6 k) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc (suc zero))))
              (sh6 l) (sh6 k) env)) (κ≡ ∙ sym (cong₂ pr ql qk))
      hApp : ⟨ env ⊨ appAt (sh6 p) (suc (suc (suc (suc zero))))
                  (suc (suc (suc zero))) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh6 p)
               (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hi' : ⟨ env ⊨ var (suc zero) ∈̇ var (sh6 k) ⟩
      hi' = subst (λ q → ⟨ fst i ∈ q ⟩) (sym qk) hi
      hj' : ⟨ env ⊨ var zero ∈̇ var (sh6 k) ⟩
      hj' = subst (λ q → ⟨ fst j ∈ q ⟩) (sym qk) hj
      hEq : ⟨ env ⊨ selectEqualAt (sh5 zero) (suc (suc zero))
                  (suc zero) zero ⟩
      hEq = selectEqualAt-in (sh5 zero) (suc (suc zero)) (suc zero) zero env e

    AllTuplesDisj-in : (n₀ k₀ : ℕ) (z : S)
      → fst z ≡ allTuples (fst (lookup a γ)) k₀
      → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ AllTuplesDisjAt zero (suc a) (suc k) ⟩
    AllTuplesDisj-in n₀ k₀ z e qk =
      allTuplesAt-in zero (suc a) (suc k) (z ∷ γ) k₀ qk e

    ExtDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (s : S) → fst (lookup k γ) ≡ sucV (fst s)
      → (W : S) → ⟨ pr (pr (# n₀) (fst s)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X y : S) → ⟨ fst X ∈ fst W ⟩ → ⟨ fst y ∈ fst (lookup a γ) ⟩
      → fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ ExtDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
    ExtDisj-in n₀ k₀ z s ks W eW X y hX hy e ql qk =
      ∣ s , ∣ κ , ∣ W , ∣ X , ∣ y ,
          (hSuc , (hPr , (hApp , (hX , (hy , hEx))))) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      κ : S
      κ = prʟ (numeralL n₀) s
      env = y ∷ X ∷ W ∷ κ ∷ s ∷ z ∷ γ
      hSuc : ⟨ env ⊨ sucAtL (suc (suc (suc (suc zero)))) (sh6 k) ⟩
      hSuc = subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc (suc (suc zero))))
               (sh6 k) env)) ks
      κ≡ : fst κ ≡ pr (# n₀) (fst s)
      κ≡ = prʟ-fst (numeralL n₀) s
        ∙ cong₂ pr (numeralL-fst n₀) refl
      hPr : ⟨ env ⊨ prAtL (suc (suc (suc zero))) (sh6 l)
                  (suc (suc (suc (suc zero)))) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc (suc zero)))
              (sh6 l) (suc (suc (suc (suc zero)))) env))
        (κ≡ ∙ sym (cong₂ pr ql refl))
      hApp : ⟨ env ⊨ appAt (sh6 p) (suc (suc (suc zero))) (suc (suc zero)) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh6 p)
               (suc (suc (suc zero))) (suc (suc zero)) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hEx : ⟨ env ⊨ extendFamilyAt (sh5 zero) (suc zero) zero ⟩
      hEx = extendFamilyAt-in (sh5 zero) (suc zero) zero env e

    ShiftDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (W : S) → ⟨ pr (pr (# n₀) (sucV (# k₀))) (fst W) ∈ fst (lookup p γ) ⟩
      → (X : S) → ⟨ fst X ∈ fst W ⟩ → fst z ≡ shiftDown (fst X)
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ ShiftDisjAt zero (suc p) (suc l) (suc k) ⟩
    ShiftDisj-in n₀ k₀ z W eW X hX e ql qk =
      ∣ s , ∣ κ , ∣ W , ∣ X , (hSuc , (hPr , (hApp , (hX , hSh)))) ∣₁ ∣₁ ∣₁ ∣₁
      where
      s : S
      s = sucʟ (numeralL k₀)
      κ : S
      κ = prʟ (numeralL n₀) s
      env = X ∷ W ∷ κ ∷ s ∷ z ∷ γ
      es : fst s ≡ sucV (# k₀)
      es = sucʟ-fst (numeralL k₀) ∙ cong sucV (numeralL-fst k₀)
      hSuc : ⟨ env ⊨ sucAtL (sh5 k) (suc (suc (suc zero))) ⟩
      hSuc = subst ⟨_⟩ (sym (sucAtL-adequate (sh5 k)
               (suc (suc (suc zero))) env))
        (es ∙ sym (cong sucV qk))
      κ≡ : fst κ ≡ pr (# n₀) (sucV (# k₀))
      κ≡ = prʟ-fst (numeralL n₀) s ∙ cong₂ pr (numeralL-fst n₀) es
      hPr : ⟨ env ⊨ prAtL (suc (suc zero)) (sh5 l) (suc (suc (suc zero))) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc zero))
              (sh5 l) (suc (suc (suc zero))) env))
        (κ≡ ∙ sym (cong₂ pr ql es))
      hApp : ⟨ env ⊨ appAt (sh5 p) (suc (suc zero)) (suc zero) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh5 p)
               (suc (suc zero)) (suc zero) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hSh : ⟨ env ⊨ shiftDownAt (sh4 zero) zero ⟩
      hSh = shiftDownAt-in (sh4 zero) zero env e

    ValuesDisj-in : (n₀ k₀ : ℕ) (z : S)
      → (W : S) → ⟨ pr (pr (# n₀) (# 1)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X : S) → ⟨ fst X ∈ fst W ⟩ → fst z ≡ values (fst X)
      → fst (lookup l γ) ≡ # n₀
      → ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc p) (suc l) ⟩
    ValuesDisj-in n₀ k₀ z W eW X hX e ql =
      ∣ n1 , ∣ κ , ∣ W , ∣ X , (hN1 , (hPr , (hApp , (hX , hV)))) ∣₁ ∣₁ ∣₁ ∣₁
      where
      n1 : S
      n1 = numeralL 1
      κ : S
      κ = prʟ (numeralL n₀) n1
      env = X ∷ W ∷ κ ∷ n1 ∷ z ∷ γ
      hN1 : ⟨ env ⊨ var (suc (suc (suc zero))) ≐ con (numeralL 1) ⟩
      hN1 = refl
      κ≡ : fst κ ≡ pr (# n₀) (# 1)
      κ≡ = prʟ-fst (numeralL n₀) n1 ∙ cong₂ pr (numeralL-fst n₀) (numeralL-fst 1)
      hPr : ⟨ env ⊨ prAtL (suc (suc zero)) (sh5 l) (suc (suc (suc zero))) ⟩
      hPr = subst ⟨_⟩ (sym (prAtL-adequate (suc (suc zero))
              (sh5 l) (suc (suc (suc zero))) env))
        (κ≡ ∙ sym (cong₂ pr ql (numeralL-fst 1)))
      hApp : ⟨ env ⊨ appAt (sh5 p) (suc (suc zero)) (suc zero) ⟩
      hApp = subst ⟨_⟩ (sym (appAt-adequate (sh5 p)
               (suc (suc zero)) (suc zero) env))
        (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩) (sym κ≡) eW)
      hV : ⟨ env ⊨ valuesAt (sh4 zero) zero ⟩
      hV = valuesAt-in (sh4 zero) zero env e

  -- Numeral membership helpers: the inSuc/inSucSuc satisfactions at the
  -- concrete numerals, and the ≤-splits the ranges need.

  #mono∈ : (m N : ℕ) → m < N → ⟨ (# m) ∈ˢ (# N) ⟩
  #mono∈ m N p = #mono m N p

  #∈-< : (m N : ℕ) → ⟨ (# m) ∈ˢ (# N) ⟩ → m < N
  #∈-< m N h = #∈#-elim m N h

  le-member : (m N : ℕ) → m ≤ N → ⟨ (# m) ∈ˢ (# (suc N)) ⟩
  le-member m N p = #mono m (suc N) (suc-≤-suc p)

  module _ {n : ℕ} (γ : S ^ n) where
    inSuc-sat : {n₀ k₀ : ℕ} → k₀ ≤ n₀
              → ⟨ (numeralL k₀ ∷ numeralL n₀ ∷ γ) ⊨ inSuc zero (suc zero) ⟩
    inSuc-sat {n₀} {k₀} p = go (≤-split p)
      where
      go : (k₀ < n₀) ⊎ (k₀ ≡ n₀)
         → ⟨ (numeralL k₀ ∷ numeralL n₀ ∷ γ) ⊨ inSuc zero (suc zero) ⟩
      go (inl h) = ∣ inr (subst (λ q → ⟨ fst (numeralL k₀) ∈ q ⟩)
        (sym (numeralL-fst n₀))
        (subst (λ q → ⟨ q ∈ (# n₀) ⟩) (sym (numeralL-fst k₀))
          (#mono∈ k₀ n₀ h))) ∣₁
      go (inr e) = ∣ inl (cong fst (cong numeralL e)) ∣₁

    inSuc-out : {n₀ k₀ : ℕ}
              → ⟨ (numeralL k₀ ∷ numeralL n₀ ∷ γ) ⊨ inSuc zero (suc zero) ⟩
              → k₀ ≤ n₀
    inSuc-out {n₀} {k₀} h = PT.rec (isProp≤ {k₀} {n₀}) go h
      where
      go : (fst (numeralL k₀) ≡ fst (numeralL n₀))
         ⊎ ⟨ fst (numeralL k₀) ∈ fst (numeralL n₀) ⟩ → k₀ ≤ n₀
      go (inl e) = subst (k₀ ≤_)
        (#-inj′ (sym (numeralL-fst k₀) ∙ e ∙ numeralL-fst n₀)) ≤-refl
      go (inr h) = ≤-trans ≤-sucℕ (k₀<n₀)
        where
        numeralLk₀L : ⟨ isL (# k₀) ⟩
        numeralLk₀L = subst (λ w → ⟨ isL w ⟩) (numeralL-fst k₀) (numeralL k₀ .snd)
        k₀<n₀ : k₀ < n₀
        k₀<n₀ = #∈-< k₀ n₀
          (subst (λ q → ⟨ q ∈ (# n₀) ⟩) (numeralL-fst k₀)
            (subst (λ q → ⟨ fst (numeralL k₀) ∈ q ⟩) (numeralL-fst n₀) h))

    inSucSuc-sat : {n₀ k₀ : ℕ} → k₀ ≤ suc n₀
                 → ⟨ (numeralL k₀ ∷ numeralL n₀ ∷ γ)
                       ⊨ inSucSuc zero (suc zero) ⟩
    inSucSuc-sat {n₀} {k₀} p = ∣ sucʟ (numeralL n₀)
      , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc zero)) zero
            (sucʟ (numeralL n₀) ∷ numeralL k₀ ∷ numeralL n₀ ∷ γ)))
          (sucʟ-fst (numeralL n₀))
        , ∣ sucʟ (sucʟ (numeralL n₀))
            , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc zero) zero
                  (sucʟ (sucʟ (numeralL n₀)) ∷ sucʟ (numeralL n₀)
                    ∷ numeralL k₀ ∷ numeralL n₀ ∷ γ)))
                (sucʟ-fst (sucʟ (numeralL n₀)))
              , subst (λ q → ⟨ q ∈ fst (sucʟ (sucʟ (numeralL n₀))) ⟩)
                  (sym (numeralL-fst k₀))
                  (subst (λ q → ⟨ # k₀ ∈ q ⟩) (sym s₂≡)
                    (le-member k₀ (suc n₀) p)) ) ∣₁ ) ∣₁
              where
              s₂≡ : fst (sucʟ (sucʟ (numeralL n₀))) ≡ # (suc (suc n₀))
              s₂≡ = sucʟ-fst (sucʟ (numeralL n₀))
                ∙ cong sucV (sucʟ-fst (numeralL n₀))
                ∙ cong sucV (cong sucV (numeralL-fst n₀))

  module _ {n : ℕ} (t b l k a : Fin n) (γ : S ^ n) where
    fun-out : ⟨ γ ⊨ FunAt t ⟩
            → (u v v' : S)
            → ⟨ pr (fst u) (fst v) ∈ fst (lookup t γ) ⟩
            → ⟨ pr (fst u) (fst v') ∈ fst (lookup t γ) ⟩
            → fst v ≡ fst v'
    fun-out h u v v' p q =
      h u v v'
        ( subst ⟨_⟩ (sym (appAt-adequate (sh3 t) (suc (suc zero)) (suc zero)
            (v' ∷ v ∷ u ∷ γ))) p
        , subst ⟨_⟩ (sym (appAt-adequate (sh3 t) (suc (suc zero)) zero
            (v' ∷ v ∷ u ∷ γ))) q )

    base0-out : (h : ⟨ γ ⊨ PrefixAt t b a ⟩)
              → (E : S) → ⟨ pr (pr (# 0) (# 0)) (fst E) ∈ fst (lookup t γ) ⟩
              → fst E ≡ singletons (fst (lookup a γ))
    base0-out h E eE = PT.rec
      (setIsSet (fst E) (singletons (fst (lookup a γ)))) go₁ (h .snd .fst)
      where
      goal : isProp (fst E ≡ singletons (fst (lookup a γ)))
      goal = setIsSet (fst E) (singletons (fst (lookup a γ)))
      finish : (n0 k0 κ W : S)
             → ⟨ (W ∷ κ ∷ k0 ∷ n0 ∷ γ)
                   ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                     ∧̇ ( var (suc (suc zero)) ≐ con (numeralL 0)
                       ∧̇ ( prAtL (suc zero) (suc (suc (suc zero)))
                             (suc (suc zero))
                         ∧̇ ( appAt (sh4 t) (suc zero) zero
                           ∧̇ SglDesc.singletonsAt zero (sh4 a) ) ) ) ) ⟩
             → fst E ≡ singletons (fst (lookup a γ))
      finish n0 k0 κ W body =
        let env = W ∷ κ ∷ k0 ∷ n0 ∷ γ
            κ≡0 : fst κ ≡ pr (# 0) (# 0)
            κ≡0 = subst ⟨_⟩ (prAtL-adequate (suc zero)
                    (suc (suc (suc zero))) (suc (suc zero)) env)
                    (body .snd .snd .fst)
                  ∙ cong₂ pr (body .fst ∙ numeralL-fst 0)
                      (body .snd .fst ∙ numeralL-fst 0)
            eW : ⟨ pr (pr (# 0) (# 0)) (fst W) ∈ fst (lookup t γ) ⟩
            eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩) κ≡0
              (subst ⟨_⟩ (appAt-adequate (sh4 t) (suc zero) zero env)
                (body .snd .snd .snd .fst))
            u : S
            u = prʟ (numeralL 0) (numeralL 0)
            u≡ : fst u ≡ pr (# 0) (# 0)
            u≡ = prʟ-fst (numeralL 0) (numeralL 0)
              ∙ cong₂ pr (numeralL-fst 0) (numeralL-fst 0)
            eq : fst E ≡ fst W
            eq = fun-out (h .fst) u E W
              (subst (λ q → ⟨ pr q (fst E) ∈ fst (lookup t γ) ⟩) (sym u≡) eE)
              (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩) (sym u≡) eW)
            S≡ : fst W ≡ singletons (fst (lookup a γ))
            S≡ = singletonsAt-out {suc (suc (suc (suc n)))} zero (sh4 a)
                   (W ∷ κ ∷ k0 ∷ n0 ∷ γ) (body .snd .snd .snd .snd)
        in eq ∙ S≡
      go₃ : (n0 k0 κ : S)
          → ∥ Σ[ W ∈ S ]
              ⟨ (W ∷ κ ∷ k0 ∷ n0 ∷ γ)
                  ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                    ∧̇ ( var (suc (suc zero)) ≐ con (numeralL 0)
                      ∧̇ ( prAtL (suc zero) (suc (suc (suc zero)))
                            (suc (suc zero))
                        ∧̇ ( appAt (sh4 t) (suc zero) zero
                          ∧̇ SglDesc.singletonsAt zero (sh4 a) ) ) ) ) ⟩ ∥₁
          → fst E ≡ singletons (fst (lookup a γ))
      go₃ n0 k0 κ = PT.rec goal (λ { (W , body) → finish n0 k0 κ W body })

      go₂ : (n0 k0 : S)
          → ∥ Σ[ κ ∈ S ] ∥ Σ[ W ∈ S ]
              ⟨ (W ∷ κ ∷ k0 ∷ n0 ∷ γ)
                  ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                    ∧̇ ( var (suc (suc zero)) ≐ con (numeralL 0)
                      ∧̇ ( prAtL (suc zero) (suc (suc (suc zero)))
                            (suc (suc zero))
                        ∧̇ ( appAt (sh4 t) (suc zero) zero
                          ∧̇ SglDesc.singletonsAt zero (sh4 a) ) ) ) ) ⟩ ∥₁ ∥₁
          → fst E ≡ singletons (fst (lookup a γ))
      go₂ n0 k0 = PT.rec goal (λ { (κ , w₃) → go₃ n0 k0 κ w₃ })

      go₁ : Σ[ n0 ∈ S ] ∥ Σ[ k0 ∈ S ] ∥ Σ[ κ ∈ S ] ∥ Σ[ W ∈ S ]
             ⟨ (W ∷ κ ∷ k0 ∷ n0 ∷ γ)
                 ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                   ∧̇ ( var (suc (suc zero)) ≐ con (numeralL 0)
                     ∧̇ ( prAtL (suc zero) (suc (suc (suc zero)))
                           (suc (suc zero))
                       ∧̇ ( appAt (sh4 t) (suc zero) zero
                         ∧̇ SglDesc.singletonsAt zero (sh4 a) ) ) ) ) ⟩ ∥₁ ∥₁ ∥₁
           → fst E ≡ singletons (fst (lookup a γ))
      go₁ (n0 , w₁) = PT.rec goal (λ { (k0 , w₂) → go₂ n0 k0 w₂ }) w₁

    -- The successor reader: at a successor key, extract the previous entry
    -- and the layer, with the union equation and the layer's out-direction.
    suc-out : (h : ⟨ γ ⊨ PrefixAt t b a ⟩)
            → (b₀ : ℕ) → fst (lookup b γ) ≡ # b₀
            → (m k₀ : ℕ) → m < b₀ → k₀ ≤ b₀
            → fst (lookup l γ) ≡ # m → fst (lookup k γ) ≡ # k₀
            → (E' : S) → ⟨ pr (pr (# (suc m)) (# k₀)) (fst E')
                            ∈ fst (lookup t γ) ⟩
            → ∥ Σ[ E ∈ S ] Σ[ L ∈ S ]
                 ( ⟨ pr (pr (# m) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩
                 × (fst E' ≡ fst E ∪ fst L)
                 × ( (z : S) → ⟨ fst z ∈ fst L ⟩ → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁ ) ) ∥₁


    suc-out h b₀ qb m k₀ m<b₀ k₀≤b₀ ql qk E' eE' =
      PT.rec squash₁ (λ { (s₁ , w₁) → PT.rec squash₁ (λ { (κ₁ , w₂) →
        PT.rec squash₁ (λ { (κ₂ , w₃) → PT.rec squash₁ (λ { (E'c , w₄) →
          PT.rec squash₁ (λ { (E , w₅) → PT.rec squash₁ (λ { (L , w₆) →
            finish s₁ κ₁ κ₂ E'c E L w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
        ((h .snd .snd .snd .fst) n'm k'₀ cond-sat)
      where
      n'm = numeralL m
      k'₀ = numeralL k₀

      cond-sat : ⟨ (k'₀ ∷ n'm ∷ γ)
                     ⊨ ( (var (suc zero) ∈̇ var (suc (suc b)))
                       ∧̇ inSuc zero (suc (suc b)) ) ⟩
      cond-sat = hN'∈b , hInSuc
        where
        hN'∈b : ⟨ (k'₀ ∷ n'm ∷ γ) ⊨ var (suc zero) ∈̇ var (suc (suc b)) ⟩
        hN'∈b = subst (λ q → ⟨ q ∈ fst (lookup b γ) ⟩) (sym (numeralL-fst m))
          (subst (λ q → ⟨ # m ∈ q ⟩) (sym qb) (#mono∈ m b₀ m<b₀))
        hInSuc : ⟨ (k'₀ ∷ n'm ∷ γ) ⊨ inSuc zero (suc (suc b)) ⟩
        hInSuc = go (≤-split k₀≤b₀)
          where
          go : (k₀ < b₀) ⊎ (k₀ ≡ b₀)
             → ⟨ (k'₀ ∷ n'm ∷ γ) ⊨ inSuc zero (suc (suc b)) ⟩
          go (inl h) = ∣ inr (subst (λ q → ⟨ fst (numeralL k₀) ∈ q ⟩)
            (sym qb)
            (subst (λ q → ⟨ q ∈ (# b₀) ⟩) (sym (numeralL-fst k₀))
              (#mono∈ k₀ b₀ h))) ∣₁
          go (inr e) = ∣ inl (cong fst (cong numeralL e)
            ∙ numeralL-fst b₀ ∙ sym qb) ∣₁

      finish : (s₁ κ₁ κ₂ E'c E L : S)
             → ⟨ (L ∷ E ∷ E'c ∷ κ₂ ∷ κ₁ ∷ s₁ ∷ k'₀ ∷ n'm ∷ γ)
                   ⊨ ( sucAtL (suc (suc (suc (suc (suc (suc (suc zero)))))))
                         (suc (suc (suc (suc (suc zero)))))
                     ∧̇ ( prAtL (suc (suc (suc (suc zero))))
                           (suc (suc (suc (suc (suc zero)))))
                           (suc (suc (suc (suc (suc (suc zero))))))
                       ∧̇ ( appAt (sh8 t) (suc (suc (suc (suc zero))))
                             (suc (suc zero))
                         ∧̇ ( prAtL (suc (suc (suc zero)))
                               (suc (suc (suc (suc (suc (suc (suc zero)))))))
                               (suc (suc (suc (suc (suc (suc zero))))))
                           ∧̇ ( appAt (sh8 t) (suc (suc (suc zero))) (suc zero)
                             ∧̇ ( unionAt (suc (suc zero))
                                   (suc zero) zero
                               ∧̇ ∀̇ ( (var zero ∈̇ var (suc zero)) ⇒̇
                                     ( (var zero ∈̇ var (suc (suc zero)))
                                     ∨̇ LayerDisjAt zero (sh9 t)
                                         (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                         (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                         (sh9 a) ) ) ) ) ) ) ) ) ⟩
             → ∥ Σ[ E ∈ S ] Σ[ L ∈ S ]
                  ( ⟨ pr (pr (# m) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩
                  × (fst E' ≡ fst E ∪ fst L)
                  × ( (z : S) → ⟨ fst z ∈ fst L ⟩ → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁ ) ) ∥₁


      finish s₁ κ₁ κ₂ E'c E L w₆ = ∣ E , L , (eE , (unEq , layerOut)) ∣₁
        where
          env = L ∷ E ∷ E'c ∷ κ₂ ∷ κ₁ ∷ s₁ ∷ k'₀ ∷ n'm ∷ γ
          hSuc = subst ⟨_⟩ (sucAtL-adequate
                       (suc (suc (suc (suc (suc (suc (suc zero)))))))
                       (suc (suc (suc (suc (suc zero))))) env)
                       (w₆ .fst)
          hPr₁ = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero))))
                        (suc (suc (suc (suc (suc zero)))))
                        (suc (suc (suc (suc (suc (suc zero)))))) env)
                        (w₆ .snd .fst)
          hApp₁ = subst ⟨_⟩ (appAt-adequate (sh8 t)
                        (suc (suc (suc (suc zero)))) (suc (suc zero)) env)
                        (w₆ .snd .snd .fst)
          hPr₂ = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                        (suc (suc (suc (suc (suc (suc (suc zero)))))))
                        (suc (suc (suc (suc (suc (suc zero)))))) env)
                        (w₆ .snd .snd .snd .fst)
          hApp₂ = subst ⟨_⟩ (appAt-adequate (sh8 t)
                        (suc (suc (suc zero))) (suc zero) env)
                        (w₆ .snd .snd .snd .snd .fst)
          hUn = w₆ .snd .snd .snd .snd .snd .fst
          hLayer = w₆ .snd .snd .snd .snd .snd .snd
          key₂ : fst κ₂ ≡ pr (# m) (# k₀)
          key₂ = hPr₂ ∙ cong₂ pr (numeralL-fst m) (numeralL-fst k₀)
          eE : ⟨ pr (pr (# m) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩
          eE = subst (λ q → ⟨ pr q (fst E) ∈ fst (lookup t γ) ⟩) key₂ hApp₂
          es₁ : fst s₁ ≡ sucV (# m)
          es₁ = hSuc ∙ cong sucV (numeralL-fst m)
          key₁ : fst κ₁ ≡ pr (# (suc m)) (# k₀)
          key₁ = hPr₁ ∙ cong₂ pr es₁ (numeralL-fst k₀)
          eE'c : ⟨ pr (pr (# (suc m)) (# k₀)) (fst E'c) ∈ fst (lookup t γ) ⟩
          eE'c = subst (λ q → ⟨ pr q (fst E'c) ∈ fst (lookup t γ) ⟩) key₁ hApp₁
          u : S
          u = prʟ (sucʟ (numeralL m)) (numeralL k₀)
          u≡ : fst u ≡ pr (# (suc m)) (# k₀)
          u≡ = prʟ-fst (sucʟ (numeralL m)) (numeralL k₀)
            ∙ cong₂ pr (sucʟ-fst (numeralL m)
                ∙ cong sucV (numeralL-fst m)) (numeralL-fst k₀)
          eqE' : fst E' ≡ fst E'c
          eqE' = fun-out (h .fst) u E' E'c
            (subst (λ q → ⟨ pr q (fst E') ∈ fst (lookup t γ) ⟩)
              (sym u≡) eE')
            (subst (λ q → ⟨ pr q (fst E'c) ∈ fst (lookup t γ) ⟩)
              (sym u≡) eE'c)
          unEq : fst E' ≡ fst E ∪ fst L
          unEq = eqE' ∙ unionAt-out (suc (suc zero))
                       (suc zero) zero env hUn
          layerOut : (z : S) → ⟨ fst z ∈ fst L ⟩ → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
          layerOut z hz = PT.rec squash₁
                    go (hLayer (fst z , isL-trans {x = fst L} {y = fst z} hz (L .snd)) hz)
              where
              clEnv : S ^ (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
              clEnv = z ∷ env
              module CLI = LayerLaws {suc (suc (suc (suc (suc (suc (suc (suc n)))))))}
                zero (sh8 t) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                (suc (suc (suc (suc (suc (suc zero)))))) (sh8 a) env
              module RDI = LayerLaws {n} b t l k a γ
              qlm : fst (lookup (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) clEnv)
                   ≡ # m
              qlm = numeralL-fst m
              qkk : fst (lookup (suc (suc (suc (suc (suc (suc (suc zero))))))) clEnv)
                   ≡ # k₀
              qkk = numeralL-fst k₀
              w0 : ⟨ (z ∷ γ) ⊨ InterDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w0 h = ∣ inr (∣ inl h ∣₁) ∣₁

              w1 : ⟨ (z ∷ γ) ⊨ UnionDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w1 h = ∣ inr (∣ inr (∣ inl h ∣₁) ∣₁) ∣₁

              w2 : ⟨ (z ∷ γ) ⊨ DiffDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w2 h = ∣ inr (∣ inr (∣ inr (∣ inl h ∣₁) ∣₁) ∣₁) ∣₁

              w3 : ⟨ (z ∷ γ) ⊨ SelMDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w3 h = ∣ inr (∣ inr (∣ inr (∣ inr (∣ inl h ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

              w4 : ⟨ (z ∷ γ) ⊨ SelEDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w4 h = ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl h ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

              w5 : ⟨ (z ∷ γ) ⊨ AllTuplesDisjAt zero (suc a) (suc k) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w5 h = ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl h ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

              w6 : ⟨ (z ∷ γ) ⊨ ExtDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w6 h = ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl h ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

              w7 : ⟨ (z ∷ γ) ⊨ ShiftDisjAt zero (suc t) (suc l) (suc k) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w7 h = ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl h ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

              w8 : ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc t) (suc l) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w8 h = ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr h ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

              hS' : ⟨ clEnv ⊨ ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                  → ⟨ (z ∷ γ) ⊨ ShiftDisjAt zero (suc t) (suc l) (suc k) ⟩
              hS' hS = PT.rec squash₁
                  (λ { (W , X , (eW , (hX , e))) →
                    RDI.ShiftDisj-in m k₀ z W eW X hX e ql qk })
                  (CLI.ShiftDisj-out m k₀ z hS qlm qkk)

              hV' : ⟨ clEnv ⊨ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ⟩
                  → ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc t) (suc l) ⟩
              hV' hV = PT.rec squash₁
                  (λ { (W , X , (eW , (hX , e))) →
                    RDI.ValuesDisj-in m k₀ z W eW X hX e ql })
                  (CLI.ValuesDisj-out m k₀ z hV qlm)

              hA' : ⟨ clEnv ⊨ AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                  → ⟨ (z ∷ γ) ⊨ AllTuplesDisjAt zero (suc a) (suc k) ⟩
              hA' hA = RDI.AllTuplesDisj-in m k₀ z (CLI.AllTuplesDisj-out m k₀ z hA qkk) qk

              hX' : ⟨ clEnv ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                  → ⟨ (z ∷ γ) ⊨ ExtDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
              hX' hX = PT.rec squash₁ (λ { (s , w₁) →
                PT.rec squash₁ (λ { (κ , w₂) → PT.rec squash₁ (λ { (W , w₃) →
                  PT.rec squash₁ (λ { (X , w₄) → PT.rec squash₁ (λ { (y , body) →
                    let envX = y ∷ X ∷ W ∷ κ ∷ s ∷ clEnv
                        hSuc = subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc (suc zero))))
                                (sh6 (suc (suc (suc (suc (suc (suc zero))))))) envX) (body .fst)
                        es : sucV (fst s) ≡ # k₀
                        es = sym hSuc ∙ qkk
                        hPr' = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                                (sh6 (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                (suc (suc (suc (suc zero)))) envX) (body .snd .fst)
                        hApp' = subst ⟨_⟩ (appAt-adequate (sh6 (sh8 t))
                                 (suc (suc (suc zero))) (suc (suc zero)) envX) (body .snd .snd .fst)
                        hXw = body .snd .snd .snd .fst
                        hyw = body .snd .snd .snd .snd .fst
                        hEx = body .snd .snd .snd .snd .snd
                        κ≡ : fst κ ≡ pr (# m) (fst s)
                        κ≡ = hPr' ∙ cong₂ pr (numeralL-fst m) refl
                        eW' : ⟨ pr (pr (# m) (fst s)) (fst W) ∈ fst (lookup t γ) ⟩
                        eW' = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩) κ≡ hApp'
                        e' : fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
                        e' = extendFamilyAt-out (sh5 zero) (suc zero) zero envX hEx
                    in RDI.ExtDisj-in m k₀ z s (qk ∙ sym es) W eW' X y hXw hyw e' ql qk })
                  w₄ }) w₃ }) w₂ }) w₁ }) hX
              hE' : ⟨ clEnv ⊨ SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                  → ⟨ (z ∷ γ) ⊨ SelEDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
              hE' hE = PT.rec squash₁
                  (λ { (W , X , i , j , (eW , (hX , (hi , (hj , e))))) →
                    RDI.SelEDisj-in m k₀ z W eW X i j hX hi hj e ql qk })
                  (CLI.SelEDisj-out m k₀ z hE qlm qkk)

              hM' : ⟨ clEnv ⊨ SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                  → ⟨ (z ∷ γ) ⊨ SelMDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
              hM' hM = PT.rec squash₁
                  (λ { (W , X , i , j , (eW , (hX , (hi , (hj , e))))) →
                    RDI.SelMDisj-in m k₀ z W eW X i j hX hi hj e ql qk })
                  (CLI.SelMDisj-out m k₀ z hM qlm qkk)

              hDi' : ⟨ clEnv ⊨ DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                  → ⟨ (z ∷ γ) ⊨ DiffDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
              hDi' hDi = PT.rec squash₁
                  (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
                    RDI.DiffDisj-in m k₀ z W eW X Y hX hY e ql qk })
                  (CLI.DiffDisj-out m k₀ z hDi qlm qkk)

              hUn' : ⟨ clEnv ⊨ UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                  → ⟨ (z ∷ γ) ⊨ UnionDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
              hUn' hUn = PT.rec squash₁
                  (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
                    RDI.UnionDisj-in m k₀ z W eW X Y hX hY e ql qk })
                  (CLI.UnionDisj-out m k₀ z hUn qlm qkk)

              hInt' : ⟨ clEnv ⊨ InterDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                  → ⟨ (z ∷ γ) ⊨ InterDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
              hInt' hInt = PT.rec squash₁
                  (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
                    RDI.InterDisj-in m k₀ z W eW X Y hX hY e ql qk })
                  (CLI.InterDisj-out m k₀ z hInt qlm qkk)
              rest7 : ⟨ clEnv ⊨ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest7 hDisj = PT.rec squash₁ (λ { (inl hS) → w7 (hS' hS)
                                  ; (inr hV) → w8 (hV' hV) }) hDisj

              rest6 : ⟨ clEnv ⊨ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest6 hDisj = PT.rec squash₁ (λ { (inl hX) → w6 (hX' hX)
                                  ; (inr hRest) → rest7 hRest }) hDisj

              rest5 : ⟨ clEnv ⊨ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest5 hDisj = PT.rec squash₁ (λ { (inl hA) → w5 (hA' hA)
                                  ; (inr hRest) → rest6 hRest }) hDisj

              rest4 : ⟨ clEnv ⊨ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest4 hDisj = PT.rec squash₁ (λ { (inl hE) → w4 (hE' hE)
                                  ; (inr hRest) → rest5 hRest }) hDisj

              rest3 : ⟨ clEnv ⊨ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ) ) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest3 hDisj = PT.rec squash₁ (λ { (inl hM) → w3 (hM' hM)
                                  ; (inr hRest) → rest4 hRest }) hDisj

              rest2 : ⟨ clEnv ⊨ ( DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ) ) ) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest2 hDisj = PT.rec squash₁ (λ { (inl hDi) → w2 (hDi' hDi)
                                  ; (inr hRest) → rest3 hRest }) hDisj

              rest : ⟨ clEnv ⊨ ( UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ) ) ) ) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest hDisj = PT.rec squash₁ (λ { (inl hUn) → w1 (hUn' hUn)
                                  ; (inr hRest) → rest2 hRest }) hDisj

              go : (⟨ fst z ∈ fst E ⟩ ⊎ ⟨ clEnv ⊨ LayerDisjAt zero (sh9 t)
                     (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                     (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩)
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              go (inl hzE) = ∣ inl hzE ∣₁
              go (inr hDisj) = PT.rec squash₁ (λ { (inl hInt) → w0 (hInt' hInt)
                                  ; (inr hRest) → rest hRest }) hDisj

```

<!--en-->
## The layer, clause by clause

The step's layer is the set of the nine operation images, spelled out over
slots. Each disjunct carries the member at the slot `e`, the previous entry at
the composite key, the level and arity the clause reads, and the carrier. The
readers are direction-paired: the out-reader turns a disjunct's satisfaction at
the member into the meta shape (the previous entry, the arguments as members,
and the operation equation), and the in-reader builds the satisfaction back
from the shape. The successor reader `suc-out` then unpacks the clause: at a
successor key it extracts the previous entry and the layer, with the union
equation and the layer's out-direction, at the concrete numerals the slots
hold.
<!--zh-->
## 层，逐子句

步进的层就是九个运算像的集合，写到槽上。每个析取支把成员放在槽 `e` 上、把前一条目放在复合键处、把该子句读的层级与元数以及载体放在各自的槽上。读式双向配对：出向读式把析取支在成员处的满足读成元层形状 (前一条目、诸实参作为成员、运算等式)，入向读式再把满足从形状装回来。后继读式 `suc-out` 随后解开子句：在后继键处抽出前一条目与层，连同并等式与层的出向方向，都落在诸槽所持的具体数码上。
<!--/-->

<!--en-->
## The prefix-table description

`PrefixAt` puts the pieces together over the table, the bound, and the
carrier: functionality at the composite key (two entries with the same key
agree on their value), the base clauses (level zero arity zero is the
singleton family of the carrier; level zero at positive arity is empty), the
successor clause (the entry at `suc n` is the entry at `n` joined with the
layer), and domain adequacy (every key up to the bound is present).
<!--zh-->
## 前缀表描述

`PrefixAt` 把各件拼到表、界与载体之上：复合键处的函数性 (同键的两条条目取值一致)、两条基子句 (层级零元数零处是载体的单例族；层级零正元数处为空)、后继子句 (`suc n` 处的条目是 `n` 处条目并上那一层)，以及定义域充分性 (到界为止的每个键都在场)。
<!--/-->
