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
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; #-inj′; #mono )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Basic {ℓ} using ( ∅ʟ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst; sucʟ; sucʟ-fst )
open import L.Ordinal {ℓ} using ( #∈#-elim; ∈#-elim )
open import L.Coding.Model {ℓ}
  using ( prʟ; prʟ-fst; prAtL; prAtL-adequate
        ; appAt; appAt-adequate; sucAtL; sucAtL-adequate; extAt )
open import L.Godel.Operations {ℓ}
  using ( values; _∩_; _∪_; _∖_
        ; ∪-left; ∪-right; ∪-out
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
open import L.Godel.InL {ℓ}
  using ( capL; cupL; diffL; selectMemberL; selectEqualL; allTuplesL
        ; shiftDownL; extendFamilyL; valuesL )
open import L.Coding.Model {ℓ} using ( numL )

open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Nat using ( _+_; +-zero; +-suc; injSuc; snotz; _∸_ )
open import Cubical.Data.Nat.Order
  using ( _<_; _≤_; suc-≤-suc; ≤-refl; ≤-split; ≤-trans; ≤-sucℕ; isProp≤
        ; <-trans; ≤<-trans; ≤-+-≤; ≤-+k-trans )
open import Cubical.Data.FinData using ( Fin; toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId' )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ⁅_⁆s; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans

open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )



private
  +2≡sucsuc : (k : ℕ) → k + 2 ≡ suc (suc k)
  +2≡sucsuc k = +-suc k (suc zero) ∙ cong suc (+-suc k zero) ∙ cong (λ w → suc (suc w)) (+-zero k)

  2≤k→k≡sucsuc : (k : ℕ) → 2 ≤ k → Σ[ k' ∈ ℕ ] (k ≡ suc (suc k'))
  2≤k→k≡sucsuc zero p = Empty.rec (snotz (subst (λ w → w ≡ 0) (+2≡sucsuc (fst p)) (snd p)))
  2≤k→k≡sucsuc (suc zero) p = Empty.rec (snotz
    (injSuc (subst (λ w → w ≡ suc zero) (+2≡sucsuc (fst p)) (snd p))))
  2≤k→k≡sucsuc (suc (suc k)) p = k , refl

  ∸-suc : (k : ℕ) → 2 ≤ k → k ∸ 1 ≡ suc (k ∸ 2)
  ∸-suc k p = subst (λ w → w ∸ 1 ≡ suc (w ∸ 2)) (sym (2≤k→k≡sucsuc k p .snd)) refl

  suc-∸1 : (k : ℕ) → 1 ≤ k → suc (k ∸ 1) ≡ k
  suc-∸1 zero p = Empty.rec (snotz
    (subst (λ w → w ≡ 0) (+-suc (fst p) zero ∙ cong suc (+-zero (fst p))) (snd p)))
  suc-∸1 (suc k) p = refl

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
  -- The closure chapter's level family is now public (the `private` on the
  -- tag block was removed there), so the semantics this chapter describes
  -- are imported directly rather than restated: one instantiation at the
  -- carrier supplies `slice`, `step`, the tags and payloads, the membership
  -- laws, and the singleton family.
  module C = L.Godel.Closure

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
  -- and a member y of the carrier, guarded to a positive source: the meta
  -- tagExt draws its first argument from a positive-arity slice only
  -- (`StepPayload n (suc (suc k)) tagExt = Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] ...`),
  -- so the source slot is pinned away from the zero numeral (refuted at
  -- layer arity one by numeral injectivity, satisfiable at every arity ≥ 2).
  -- Binders: s, κ, S, X, y; env y ∷ X ∷ S ∷ κ ∷ s ∷ γ.
  ExtDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
  ExtDisjAt e p l k a = ∃̇ (∃̇ (∃̇ (∃̇ (∃̇ (
      sucAtL (suc (suc (suc (suc zero)))) (sh5 k)
    ∧̇ ( ¬̇ (var (suc (suc (suc (suc zero)))) ≐ con (numeralL 0))
      ∧̇ ( prAtL (suc (suc (suc zero))) (sh5 l) (suc (suc (suc (suc zero))))
        ∧̇ ( appAt (sh5 p) (suc (suc (suc zero))) (suc (suc zero))
          ∧̇ ( (var (suc zero) ∈̇ var (suc (suc zero)))
            ∧̇ ( (var zero ∈̇ var (sh5 a))
              ∧̇ extendFamilyAt (sh5 e) (suc zero) zero ) ) ) ) ))))))

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

  -- ValuesDisjAt e p l k: the member at e is values X for a member X of the
  -- previous entry at the key (l, n1) with n1 the numeral one, guarded to the
  -- arity slot k pinning the zero numeral: the meta values image exists only
  -- on the arity-zero shelf (`tagValues : StepTag 0`), so at positive arities
  -- the guard is refuted by numeral injectivity while at zero it reads shelf
  -- one exactly as the meta step does.  Binders: n1, κ, S, X;
  -- env X ∷ S ∷ κ ∷ n1 ∷ γ.
  ValuesDisjAt : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  ValuesDisjAt e p l k = ∃̇ (∃̇ (∃̇ (∃̇ (
      var (suc (suc (suc zero))) ≐ con (numeralL 1)
    ∧̇ ( var (sh4 k) ≐ con (numeralL 0)
      ∧̇ ( prAtL (suc (suc zero)) (sh4 l) (suc (suc (suc zero)))
        ∧̇ ( appAt (sh4 p) (suc (suc zero)) (suc zero)
          ∧̇ ( (var zero ∈̇ var (suc zero))
            ∧̇ valuesAt (sh4 e) zero ) ) ) ) ) )))

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
    ∨̇ ValuesDisjAt e p l k )))))))

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

      memL : (y : V ℓ) → ⟨ y ∈ C.singletons A X ⟩ → ⟨ isL y ⟩
      memL y hy = PT.rec (snd (isL y))
        (λ { (x , hx , e) → subst (λ w → ⟨ isL w ⟩) (sym e)
          (sglL (isL-trans {x = X} {y = x} hx (lookup i γ .snd))) })
        (C.singletons-out A {X} {w = y} hy)

      read : (z : SglDesc.SL) → ⟨ (z ∷ γ) ⊨ Φ ⟩ → ⟨ fst z ∈ C.singletons A X ⟩
      read z hz = PT.rec (snd (fst z ∈ C.singletons A X)) build hz
        where
        build : Σ[ x ∈ SglDesc.SL ] (⟨ fst x ∈ˢ fst (lookup i γ) ⟩
                 × ⟨ (x ∷ z ∷ γ) ⊨ sglAt′ {n = suc (suc n)} (suc zero) zero ⟩)
              → ⟨ fst z ∈ C.singletons A X ⟩
        build (x , hx , s) =
          let z≡ : fst z ≡ ⁅ fst x ⁆s
              z≡ = extensionality (fst z) ⁅ fst x ⁆s (sub₁ , sub₂)
          in subst (λ w → ⟨ w ∈ C.singletons A X ⟩) (sym z≡)
               (C.singletons-in A {X} {x = fst x} hx)
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

      fill : (z : SglDesc.SL) → ⟨ fst z ∈ C.singletons A X ⟩ → ⟨ (z ∷ γ) ⊨ Φ ⟩
      fill z hz = PT.rec (snd ((z ∷ γ) ⊨ Φ)) build
        (C.singletons-out A {X} {w = fst z} hz)
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

    module D = Describes k Φ γ (C.singletons A X) memL read fill

    singletonsAt-out : ⟨ γ ⊨ SglDesc.singletonsAt k i ⟩
                     → fst (lookup k γ) ≡ C.singletons A X
    singletonsAt-out = D.describes-out

    singletonsAt-in : fst (lookup k γ) ≡ C.singletons A X
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

  -- The successor clause's reverse direction: every member the layer
  -- disjunction describes is in the layer.  The forward direction alone
  -- (`SucClause`) admits junk tables whose layer omits the operation images,
  -- which would break the pinning theorem; the conjunction of the two
  -- per-member directions makes the entry at the successor key a definite
  -- description of `slice A (suc n) k` given the entry at `n`.  Binders as
  -- in `SucClause`; the inner ∀̇ now reads the disjunction back into the
  -- layer membership.
  SucClauseRev : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  SucClauseRev t b a = ∀̇ (∀̇ (
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
                  ∧̇ ∀̇ ( LayerDisjAt zero (sh9 t)
                          (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                          (suc (suc (suc (suc (suc (suc (suc zero)))))))
                          (sh9 a) ⇒̇ (var zero ∈̇ var (suc zero)) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )

  PrefixAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
  PrefixAt t b a =
      FunAt t
    ∧̇ ( Base0 t a
    ∧̇ ( BaseS t b a
    ∧̇ ( SucClause t b a
    ∧̇ ( DomAdeq t b a
      ∧̇ SucClauseRev t b a ))))

  -- The layer readers, per disjunct, at the meta numerals the slots hold.
  -- The out-reader turns a disjunct's satisfaction at the member z into the
  -- meta shape: the previous entry S at the composite key, the arguments as
  -- members of S, and the operation equation.  The in-reader builds the
  -- satisfaction back from the shape.
  -- The closure level family and its membership laws are imported from the
  -- closure chapter via `C` above; nothing is restated here.

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
           × (sucV (fst s) ≡ # k₀)
           × ((fst s ≡ fst (numeralL 0)) → Empty.⊥)
           × ⟨ pr (pr (# n₀) (fst s)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩ × ⟨ fst y ∈ fst (lookup a γ) ⟩
           × (fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s) ) ∥₁
    ExtDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (s , w₁) →
      PT.rec squash₁ (λ { (κ , w₂) → PT.rec squash₁ (λ { (W , w₃) →
        PT.rec squash₁ (λ { (X , w₄) → PT.rec squash₁ (λ { (y , body) →
          let env = y ∷ X ∷ W ∷ κ ∷ s ∷ z ∷ γ
              hSuc = subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc (suc zero)))) (sh6 k)
                       env) (body .fst)
              hPos = body .snd .fst
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                      (sh6 l) (suc (suc (suc (suc zero)))) env) (body .snd .snd .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh6 p)
                       (suc (suc (suc zero))) (suc (suc zero)) env) (body .snd .snd .snd .fst)
              hX = body .snd .snd .snd .snd .fst
              hy = body .snd .snd .snd .snd .snd .fst
              hEx = body .snd .snd .snd .snd .snd .snd
              es : sucV (fst s) ≡ # k₀
              es = sym hSuc ∙ qk
              hs : ⟨ fst s ∈ # k₀ ⟩
              hs = subst (λ q → ⟨ fst s ∈ q ⟩) es (self∈sucV (fst s))
              hPos' : (fst s ≡ fst (numeralL 0)) → Empty.⊥
              hPos' = hPos
              eW : ⟨ pr (pr (# n₀) (fst s)) (fst W) ∈ fst (lookup p γ) ⟩
              eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     (hPr ∙ cong₂ pr ql refl) hApp
              e : fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
              e = extendFamilyAt-out (sh5 zero) (suc zero) zero env hEx
          in ∣ s , W , X , y , (hs , (es , (hPos' , (eW , (hX , (hy , e)))))) ∣₁ })
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
      → ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc p) (suc l) (suc k) ⟩
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ∥ Σ[ W ∈ S ] Σ[ X ∈ S ]
           ( ⟨ pr (pr (# n₀) (# 1)) (fst W) ∈ fst (lookup p γ) ⟩
           × ⟨ fst X ∈ fst W ⟩
           × (fst z ≡ values (fst X)) × (k₀ ≡ 0) ) ∥₁
    ValuesDisj-out n₀ k₀ z hz ql qk = PT.rec squash₁ (λ { (n1 , w₁) →
      PT.rec squash₁ (λ { (κ , w₂) → PT.rec squash₁ (λ { (W , w₃) →
        PT.rec squash₁ (λ { (X , body) →
          let env = X ∷ W ∷ κ ∷ n1 ∷ z ∷ γ
              hN1 = body .fst
              hZ = body .snd .fst
              hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc zero))
                      (sh5 l) (suc (suc (suc zero))) env) (body .snd .snd .fst)
              hApp = subst ⟨_⟩ (appAt-adequate (sh5 p)
                       (suc (suc zero)) (suc zero) env) (body .snd .snd .snd .fst)
              hX = body .snd .snd .snd .snd .fst
              hV = body .snd .snd .snd .snd .snd
              en1 : fst n1 ≡ # 1
              en1 = hN1 ∙ numeralL-fst 1
              eW : ⟨ pr (pr (# n₀) (# 1)) (fst W) ∈ fst (lookup p γ) ⟩
              eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup p γ) ⟩)
                     (hPr ∙ cong₂ pr ql en1) hApp
              e : fst z ≡ values (fst X)
              e = valuesAt-out (sh4 zero) zero env hV
              zq : k₀ ≡ 0
              zq = #-inj′ (sym qk ∙ hZ ∙ numeralL-fst 0)
          in ∣ W , X , (eW , (hX , (e , zq))) ∣₁ }) w₃ }) w₂ }) w₁ }) hz
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
      → (hPos : (fst s ≡ fst (numeralL 0)) → Empty.⊥)
      → (W : S) → ⟨ pr (pr (# n₀) (fst s)) (fst W) ∈ fst (lookup p γ) ⟩
      → (X y : S) → ⟨ fst X ∈ fst W ⟩ → ⟨ fst y ∈ fst (lookup a γ) ⟩
      → fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀
      → ⟨ (z ∷ γ) ⊨ ExtDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
    ExtDisj-in n₀ k₀ z s ks hPos W eW X y hX hy e ql qk =
      ∣ s , ∣ κ , ∣ W , ∣ X , ∣ y ,
          (hSuc , (hPos , (hPr , (hApp , (hX , (hy , hEx)))))) ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
      where
      κ : S
      κ = prʟ (numeralL n₀) s
      env : S ^ (suc (suc (suc (suc (suc (suc n))))))
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
      → fst (lookup l γ) ≡ # n₀ → fst (lookup k γ) ≡ # k₀ → k₀ ≡ 0
      → ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc p) (suc l) (suc k) ⟩
    ValuesDisj-in n₀ k₀ z W eW X hX e ql qk zq =
      ∣ n1 , ∣ κ , ∣ W , ∣ X , (hN1 , (hZ , (hPr , (hApp , (hX , hV))))) ∣₁ ∣₁ ∣₁ ∣₁
      where
      n1 : S
      n1 = numeralL 1
      κ : S
      κ = prʟ (numeralL n₀) n1
      env = X ∷ W ∷ κ ∷ n1 ∷ z ∷ γ
      hN1 : ⟨ env ⊨ var (suc (suc (suc zero))) ≐ con (numeralL 1) ⟩
      hN1 = refl
      hZ : ⟨ env ⊨ var (sh4 (suc k)) ≐ con (numeralL 0) ⟩
      hZ = qk ∙ cong #_ zq ∙ sym (numeralL-fst 0)
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

  -- The meta-to-disjunct bridge: one named case per tag reads a member of
  -- the meta step (a tagged image with its payload) into the layer
  -- disjunction's satisfaction.  The disjuncts read the previous entries at
  -- the clause's keys, so each case takes its own entry witness: the
  -- same-arity shelf for the binary, selection, and tuple clauses; the shelf
  -- one arity up for the shift; one arity down for the extension; and the
  -- arity-one shelf for values.  The image's own constructibility is
  -- computed per case and returned with the satisfaction, since a member of
  -- the step is an S-element only with its witness.  The dispatcher
  -- `layerIn` supplies all entries from one per-arity family, which is the
  -- shape the fill's packed table provides.
  module LayerIn {n : ℕ} (b p l k a : Fin n) (γ : S ^ n) where
    module LL = LayerLaws {n} b p l k a γ
    module _ (n₀ k₀ : ℕ)
             (ql : fst (lookup l γ) ≡ # n₀) (qk : fst (lookup k γ) ≡ # k₀)
             (qa : fst (lookup a γ) ≡ A) where
      lA : ⟨ isL A ⟩
      lA = subst (λ w → ⟨ isL w ⟩) qa (lookup a γ .snd)

      -- An S-element for a fiber member of the shelf at arity k', with the
      -- membership in the given entry and the constructibility from it.
      membW : (W : S) (k' : ℕ) → fst W ≡ C.slice A n₀ k'
            → (m : ⟪ C.slice A n₀ k' ⟫) → S
      membW W k' qW m = (⟪ C.slice A n₀ k' ⟫↪ m , lX)
        where
        hX0 : ⟨ ⟪ C.slice A n₀ k' ⟫↪ m ∈ C.slice A n₀ k' ⟩
        hX0 = ∈∈ₛ {a = ⟪ C.slice A n₀ k' ⟫↪ m} {b = C.slice A n₀ k'} .snd
                (∈ₛ⟪ C.slice A n₀ k' ⟫↪ m)
        hX : ⟨ ⟪ C.slice A n₀ k' ⟫↪ m ∈ fst W ⟩
        hX = subst (λ w → ⟨ ⟪ C.slice A n₀ k' ⟫↪ m ∈ w ⟩) (sym qW) hX0
        lX : ⟨ isL (⟪ C.slice A n₀ k' ⟫↪ m) ⟩
        lX = isL-trans {x = fst W} {y = ⟪ C.slice A n₀ k' ⟫↪ m} hX (W .snd)

      membW∈ : (W : S) (k' : ℕ) → fst W ≡ C.slice A n₀ k'
             → (m : ⟪ C.slice A n₀ k' ⟫) → ⟨ ⟪ C.slice A n₀ k' ⟫↪ m ∈ fst W ⟩
      membW∈ W k' qW m = subst (λ w → ⟨ ⟪ C.slice A n₀ k' ⟫↪ m ∈ w ⟩) (sym qW)
        (∈∈ₛ {a = ⟪ C.slice A n₀ k' ⟫↪ m} {b = C.slice A n₀ k'} .snd
          (∈ₛ⟪ C.slice A n₀ k' ⟫↪ m))

      -- A member of the carrier as an S-element.
      membA : ⟪ A ⟫ → S
      membA aa = (⟪ A ⟫↪ aa , lY)
        where
        hy : ⟨ ⟪ A ⟫↪ aa ∈ A ⟩
        hy = ∈∈ₛ {a = ⟪ A ⟫↪ aa} {b = A} .snd (∈ₛ⟪ A ⟫↪ aa)
        hy' : ⟨ ⟪ A ⟫↪ aa ∈ fst (lookup a γ) ⟩
        hy' = subst (λ w → ⟨ ⟪ A ⟫↪ aa ∈ w ⟩) (sym qa) hy
        lY : ⟨ isL (⟪ A ⟫↪ aa) ⟩
        lY = isL-trans {x = fst (lookup a γ)} {y = ⟪ A ⟫↪ aa} hy' (lookup a γ .snd)

      membA∈ : (aa : ⟪ A ⟫) → ⟨ fst (membA aa) ∈ fst (lookup a γ) ⟩
      membA∈ aa = subst (λ w → ⟨ ⟪ A ⟫↪ aa ∈ w ⟩) (sym qa)
        (∈∈ₛ {a = ⟪ A ⟫↪ aa} {b = A} .snd (∈ₛ⟪ A ⟫↪ aa))

      -- The index numerals as S-elements with their numeral memberships.
      idxS : Fin k₀ → S
      idxS i = (# (toℕ i) , numL (toℕ i))
      idx∈ : (i : Fin k₀) → ⟨ fst (idxS i) ∈ # k₀ ⟩
      idx∈ i = #mono (toℕ i) k₀ (toℕ<n i)

      inter-layer : (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
                  → fst W ≡ C.slice A n₀ k₀
                  → (m q : ⟪ C.slice A n₀ k₀ ⟫)
                  → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} C.tagInter (m , q)) ⟩ ]
                        ⟨ ((C.stepImage A {n₀} {k₀} C.tagInter (m , q) , lZ) ∷ γ)
                            ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      inter-layer W eW qW m q = ∣ lZ , ∣ inl sat ∣₁ ∣₁
        where
        X = membW W k₀ qW m
        Y = membW W k₀ qW q
        lZ : ⟨ isL (C.stepImage A {n₀} {k₀} C.tagInter (m , q)) ⟩
        lZ = capL (X .snd) (Y .snd)
        sat : ⟨ ((C.stepImage A {n₀} {k₀} C.tagInter (m , q) , lZ) ∷ γ)
                  ⊨ InterDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
        sat = LL.InterDisj-in n₀ k₀ (C.stepImage A {n₀} {k₀} C.tagInter (m , q) , lZ)
                W eW X Y (membW∈ W k₀ qW m) (membW∈ W k₀ qW q) refl ql qk

      union-layer : (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
                  → fst W ≡ C.slice A n₀ k₀
                  → (m q : ⟪ C.slice A n₀ k₀ ⟫)
                  → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} C.tagUnion (m , q)) ⟩ ]
                        ⟨ ((C.stepImage A {n₀} {k₀} C.tagUnion (m , q) , lZ) ∷ γ)
                            ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      union-layer W eW qW m q = ∣ lZ , ∣ inr (∣ inl sat ∣₁) ∣₁ ∣₁
        where
        X = membW W k₀ qW m
        Y = membW W k₀ qW q
        lZ : ⟨ isL (C.stepImage A {n₀} {k₀} C.tagUnion (m , q)) ⟩
        lZ = cupL (X .snd) (Y .snd)
        sat : ⟨ ((C.stepImage A {n₀} {k₀} C.tagUnion (m , q) , lZ) ∷ γ)
                  ⊨ UnionDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
        sat = LL.UnionDisj-in n₀ k₀ (C.stepImage A {n₀} {k₀} C.tagUnion (m , q) , lZ)
                W eW X Y (membW∈ W k₀ qW m) (membW∈ W k₀ qW q) refl ql qk

      diff-layer : (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
                 → fst W ≡ C.slice A n₀ k₀
                 → (m q : ⟪ C.slice A n₀ k₀ ⟫)
                 → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} C.tagDiff (m , q)) ⟩ ]
                       ⟨ ((C.stepImage A {n₀} {k₀} C.tagDiff (m , q) , lZ) ∷ γ)
                           ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      diff-layer W eW qW m q = ∣ lZ , ∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁ ∣₁
        where
        X = membW W k₀ qW m
        Y = membW W k₀ qW q
        lZ : ⟨ isL (C.stepImage A {n₀} {k₀} C.tagDiff (m , q)) ⟩
        lZ = diffL (X .snd) (Y .snd)
        sat : ⟨ ((C.stepImage A {n₀} {k₀} C.tagDiff (m , q) , lZ) ∷ γ)
                  ⊨ DiffDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
        sat = LL.DiffDisj-in n₀ k₀ (C.stepImage A {n₀} {k₀} C.tagDiff (m , q) , lZ)
                W eW X Y (membW∈ W k₀ qW m) (membW∈ W k₀ qW q) refl ql qk

      selM-layer : (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
                 → fst W ≡ C.slice A n₀ k₀
                 → (m : ⟪ C.slice A n₀ k₀ ⟫) (i j : Fin k₀)
                 → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} C.tagSelM (m , i , j)) ⟩ ]
                       ⟨ ((C.stepImage A {n₀} {k₀} C.tagSelM (m , i , j) , lZ) ∷ γ)
                           ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      selM-layer W eW qW m i j = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
        where
        X = membW W k₀ qW m
        I = idxS i
        J = idxS j
        lZ : ⟨ isL (C.stepImage A {n₀} {k₀} C.tagSelM (m , i , j)) ⟩
        lZ = selectMemberL {X = fst X} {Ka = ⁅ # (toℕ i) ⁆s} {Kb = ⁅ # (toℕ j) ⁆s}
               (X .snd) (sglL (I .snd)) (sglL (J .snd))
        sat : ⟨ ((C.stepImage A {n₀} {k₀} C.tagSelM (m , i , j) , lZ) ∷ γ)
                  ⊨ SelMDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
        sat = LL.SelMDisj-in n₀ k₀ (C.stepImage A {n₀} {k₀} C.tagSelM (m , i , j) , lZ)
                W eW X I J (membW∈ W k₀ qW m) (idx∈ i) (idx∈ j) refl ql qk

      selE-layer : (W : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst W) ∈ fst (lookup p γ) ⟩
                 → fst W ≡ C.slice A n₀ k₀
                 → (m : ⟪ C.slice A n₀ k₀ ⟫) (i j : Fin k₀)
                 → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} C.tagSelE (m , i , j)) ⟩ ]
                       ⟨ ((C.stepImage A {n₀} {k₀} C.tagSelE (m , i , j) , lZ) ∷ γ)
                           ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      selE-layer W eW qW m i j = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
        where
        X = membW W k₀ qW m
        I = idxS i
        J = idxS j
        lZ : ⟨ isL (C.stepImage A {n₀} {k₀} C.tagSelE (m , i , j)) ⟩
        lZ = selectEqualL {X = fst X} {Ka = ⁅ # (toℕ i) ⁆s} {Kb = ⁅ # (toℕ j) ⁆s}
               (X .snd) (sglL (I .snd)) (sglL (J .snd))
        sat : ⟨ ((C.stepImage A {n₀} {k₀} C.tagSelE (m , i , j) , lZ) ∷ γ)
                  ⊨ SelEDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
        sat = LL.SelEDisj-in n₀ k₀ (C.stepImage A {n₀} {k₀} C.tagSelE (m , i , j) , lZ)
                W eW X I J (membW∈ W k₀ qW m) (idx∈ i) (idx∈ j) refl ql qk

      all-layer : ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} C.tagAll tt*) ⟩ ]
                       ⟨ ((C.stepImage A {n₀} {k₀} C.tagAll tt* , lZ) ∷ γ)
                           ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      all-layer = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
        where
        lZ : ⟨ isL (allTuples A k₀) ⟩
        lZ = allTuplesL A lA k₀
        sat : ⟨ ((allTuples A k₀ , lZ) ∷ γ) ⊨ AllTuplesDisjAt zero (suc a) (suc k) ⟩
        sat = LL.AllTuplesDisj-in n₀ k₀ (allTuples A k₀ , lZ)
                (cong (λ W → allTuples W k₀) (sym qa)) qk

      ext-layer : (k' : ℕ) → k₀ ≡ suc (suc k')
                → (W : S) → ⟨ pr (pr (# n₀) (# (suc k'))) (fst W) ∈ fst (lookup p γ) ⟩
                → fst W ≡ C.slice A n₀ (suc k')
                → (m : ⟪ C.slice A n₀ (suc k') ⟫) (aa : ⟪ A ⟫)
                → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {suc (suc k')} (C.tagExt {k = k'}) (m , aa)) ⟩ ]
                      ⟨ ((C.stepImage A {n₀} {suc (suc k')} (C.tagExt {k = k'}) (m , aa) , lZ) ∷ γ)
                          ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      ext-layer k' qk₀ W eW qW m aa = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
        where
        X = membW W (suc k') qW m
        Y = membA aa
        lZ : ⟨ isL (C.stepImage A {n₀} {suc (suc k')} (C.tagExt {k = k'}) (m , aa)) ⟩
        lZ = extendFamilyL {X = fst X} {Y = ⁅ fst Y ⁆s} (X .snd) (sglL (Y .snd))
        s : S
        s = numeralL (suc k')
        hPos : (fst s ≡ fst (numeralL 0)) → Empty.⊥
        hPos h = snotz (#-inj′ (sym (numeralL-fst (suc k')) ∙ h ∙ numeralL-fst 0))
        ks : fst (lookup k γ) ≡ sucV (fst s)
        ks = qk ∙ cong (λ w → # w) qk₀ ∙ sym (cong sucV (numeralL-fst (suc k')))
        eW' : ⟨ pr (pr (# n₀) (fst s)) (fst W) ∈ fst (lookup p γ) ⟩
        eW' = subst (λ w → ⟨ pr (pr (# n₀) w) (fst W) ∈ fst (lookup p γ) ⟩)
                (sym (numeralL-fst (suc k'))) eW
        sat : ⟨ ((C.stepImage A {n₀} {suc (suc k')} (C.tagExt {k = k'}) (m , aa) , lZ) ∷ γ)
                  ⊨ ExtDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩
        sat = LL.ExtDisj-in n₀ (suc (suc k')) (C.stepImage A {n₀} {suc (suc k')} (C.tagExt {k = k'}) (m , aa) , lZ)
                s ks hPos W eW' X Y (membW∈ W (suc k') qW m) (membA∈ aa) refl ql (qk ∙ cong (λ w → # w) qk₀)

      shift-layer : (W : S) → ⟨ pr (pr (# n₀) (sucV (# k₀))) (fst W) ∈ fst (lookup p γ) ⟩
                  → fst W ≡ C.slice A n₀ (suc k₀)
                  → (m : ⟪ C.slice A n₀ (suc k₀) ⟫)
                  → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} C.tagShift m) ⟩ ]
                        ⟨ ((C.stepImage A {n₀} {k₀} C.tagShift m , lZ) ∷ γ)
                            ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      shift-layer W eW qW m = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
        where
        X = membW W (suc k₀) qW m
        lZ : ⟨ isL (C.stepImage A {n₀} {k₀} C.tagShift m) ⟩
        lZ = shiftDownL {X = fst X} (X .snd)
        sat : ⟨ ((C.stepImage A {n₀} {k₀} C.tagShift m , lZ) ∷ γ)
                  ⊨ ShiftDisjAt zero (suc p) (suc l) (suc k) ⟩
        sat = LL.ShiftDisj-in n₀ k₀ (C.stepImage A {n₀} {k₀} C.tagShift m , lZ)
                W eW X (membW∈ W (suc k₀) qW m) refl ql qk

      values-layer : (W : S) → ⟨ pr (pr (# n₀) (# 1)) (fst W) ∈ fst (lookup p γ) ⟩
                   → fst W ≡ C.slice A n₀ 1
                   → k₀ ≡ 0
                   → (m : ⟪ C.slice A n₀ 1 ⟫)
                   → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {zero} C.tagValues m) ⟩ ]
                         ⟨ ((C.stepImage A {n₀} {zero} C.tagValues m , lZ) ∷ γ)
                             ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
      values-layer W eW qW zq m = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
        where
        X = membW W 1 qW m
        lZ : ⟨ isL (C.stepImage A {n₀} {zero} C.tagValues m) ⟩
        lZ = valuesL {X = fst X} (X .snd)
        sat : ⟨ ((C.stepImage A {n₀} {zero} C.tagValues m , lZ) ∷ γ)
                  ⊨ ValuesDisjAt zero (suc p) (suc l) (suc k) ⟩
        sat = LL.ValuesDisj-in n₀ k₀ (C.stepImage A {n₀} {zero} C.tagValues m , lZ)
                W eW X (membW∈ W 1 qW m) refl ql qk zq

      -- The dispatcher: all entries come from one per-arity family, the
      -- shape the fill's packed table provides.
      module _ (entryAt : ℕ → S)
               (eW : (k' : ℕ) → ⟨ pr (pr (# n₀) (# k')) (fst (entryAt k'))
                                  ∈ fst (lookup p γ) ⟩)
               (qW : (k' : ℕ) → fst (entryAt k') ≡ C.slice A n₀ k') where
          layerIn : (t : C.StepTag A k₀) (pp : C.StepPayload A n₀ k₀ t)
                  → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {n₀} {k₀} t pp) ⟩ ]
                        ⟨ ((C.stepImage A {n₀} {k₀} t pp , lZ) ∷ γ)
                            ⊨ LayerDisjAt zero (suc p) (suc l) (suc k) (suc a) ⟩ ∥₁
          layerIn C.tagInter (m , q) = inter-layer (entryAt k₀) (eW k₀) (qW k₀) m q
          layerIn C.tagUnion (m , q) = union-layer (entryAt k₀) (eW k₀) (qW k₀) m q
          layerIn C.tagDiff (m , q) = diff-layer (entryAt k₀) (eW k₀) (qW k₀) m q
          layerIn C.tagSelM (m , i , j) = selM-layer (entryAt k₀) (eW k₀) (qW k₀) m i j
          layerIn C.tagSelE (m , i , j) = selE-layer (entryAt k₀) (eW k₀) (qW k₀) m i j
          layerIn C.tagAll tt* = all-layer
          layerIn (C.tagExt {k = k}) (m , aa) = ext-layer k refl (entryAt (suc k)) (eW (suc k)) (qW (suc k)) m aa
          layerIn C.tagShift m = shift-layer (entryAt (suc k₀)) (eW (suc k₀)) (qW (suc k₀)) m
          layerIn C.tagValues m = values-layer (entryAt 1) (eW 1) (qW 1) refl m


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
              → fst E ≡ C.singletons A (fst (lookup a γ))
    base0-out h E eE = PT.rec
      (setIsSet (fst E) (C.singletons A (fst (lookup a γ)))) go₁ (h .snd .fst)
      where
      goal : isProp (fst E ≡ C.singletons A (fst (lookup a γ)))
      goal = setIsSet (fst E) (C.singletons A (fst (lookup a γ)))
      finish : (n0 k0 κ W : S)
             → ⟨ (W ∷ κ ∷ k0 ∷ n0 ∷ γ)
                   ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                     ∧̇ ( var (suc (suc zero)) ≐ con (numeralL 0)
                       ∧̇ ( prAtL (suc zero) (suc (suc (suc zero)))
                             (suc (suc zero))
                         ∧̇ ( appAt (sh4 t) (suc zero) zero
                           ∧̇ SglDesc.singletonsAt zero (sh4 a) ) ) ) ) ⟩
             → fst E ≡ C.singletons A (fst (lookup a γ))
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
            S≡ : fst W ≡ C.singletons A (fst (lookup a γ))
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
          → fst E ≡ C.singletons A (fst (lookup a γ))
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
          → fst E ≡ C.singletons A (fst (lookup a γ))
      go₂ n0 k0 = PT.rec goal (λ { (κ , w₃) → go₃ n0 k0 κ w₃ })

      go₁ : Σ[ n0 ∈ S ] ∥ Σ[ k0 ∈ S ] ∥ Σ[ κ ∈ S ] ∥ Σ[ W ∈ S ]
             ⟨ (W ∷ κ ∷ k0 ∷ n0 ∷ γ)
                 ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                   ∧̇ ( var (suc (suc zero)) ≐ con (numeralL 0)
                     ∧̇ ( prAtL (suc zero) (suc (suc (suc zero)))
                           (suc (suc zero))
                       ∧̇ ( appAt (sh4 t) (suc zero) zero
                         ∧̇ SglDesc.singletonsAt zero (sh4 a) ) ) ) ) ⟩ ∥₁ ∥₁ ∥₁
           → fst E ≡ C.singletons A (fst (lookup a γ))
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

              w8 : ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc t) (suc l) (suc k) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              w8 h = ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr h ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁

              hS' : ⟨ clEnv ⊨ ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                  → ⟨ (z ∷ γ) ⊨ ShiftDisjAt zero (suc t) (suc l) (suc k) ⟩
              hS' hS = PT.rec squash₁
                  (λ { (W , X , (eW , (hX , e))) →
                    RDI.ShiftDisj-in m k₀ z W eW X hX e ql qk })
                  (CLI.ShiftDisj-out m k₀ z hS qlm qkk)

              hV' : ⟨ clEnv ⊨ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                  → ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc t) (suc l) (suc k) ⟩
              hV' hV = PT.rec squash₁
                  (λ { (W , X , (eW , (hX , e , zq))) →
                    RDI.ValuesDisj-in m k₀ z W eW X hX e ql qk zq })
                  (CLI.ValuesDisj-out m k₀ z hV qlm qkk)

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
                        hPos = body .snd .fst
                        hPr' = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                                (sh6 (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                (suc (suc (suc (suc zero)))) envX) (body .snd .snd .fst)
                        hApp' = subst ⟨_⟩ (appAt-adequate (sh6 (sh8 t))
                                 (suc (suc (suc zero))) (suc (suc zero)) envX) (body .snd .snd .snd .fst)
                        hXw = body .snd .snd .snd .snd .fst
                        hyw = body .snd .snd .snd .snd .snd .fst
                        hEx = body .snd .snd .snd .snd .snd .snd
                        κ≡ : fst κ ≡ pr (# m) (fst s)
                        κ≡ = hPr' ∙ cong₂ pr (numeralL-fst m) refl
                        eW' : ⟨ pr (pr (# m) (fst s)) (fst W) ∈ fst (lookup t γ) ⟩
                        eW' = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩) κ≡ hApp'
                        e' : fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
                        e' = extendFamilyAt-out (sh5 zero) (suc zero) zero envX hEx
                    in RDI.ExtDisj-in m k₀ z s (qk ∙ sym es) hPos W eW' X y hXw hyw e' ql qk })
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
              rest7 : ⟨ clEnv ⊨ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest7 hDisj = PT.rec squash₁ (λ { (inl hS) → w7 (hS' hS)
                                  ; (inr hV) → w8 (hV' hV) }) hDisj

              rest6 : ⟨ clEnv ⊨ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest6 hDisj = PT.rec squash₁ (λ { (inl hX) → w6 (hX' hX)
                                  ; (inr hRest) → rest7 hRest }) hDisj

              rest5 : ⟨ clEnv ⊨ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest5 hDisj = PT.rec squash₁ (λ { (inl hA) → w5 (hA' hA)
                                  ; (inr hRest) → rest6 hRest }) hDisj

              rest4 : ⟨ clEnv ⊨ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest4 hDisj = PT.rec squash₁ (λ { (inl hE) → w4 (hE' hE)
                                  ; (inr hRest) → rest5 hRest }) hDisj

              rest3 : ⟨ clEnv ⊨ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest3 hDisj = PT.rec squash₁ (λ { (inl hM) → w3 (hM' hM)
                                  ; (inr hRest) → rest4 hRest }) hDisj

              rest2 : ⟨ clEnv ⊨ ( DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ) ) ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩ ∥₁
              rest2 hDisj = PT.rec squash₁ (λ { (inl hDi) → w2 (hDi' hDi)
                                  ; (inr hRest) → rest3 hRest }) hDisj

              rest : ⟨ clEnv ⊨ ( UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ) ) ) ⟩
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

    -- The successor reader, reverse direction: the same unpacking, but the
    -- per-member property runs the other way, spending the successor clause's
    -- reverse conjunct (`SucClauseRev`): a member the layer disjunction
    -- describes is in the layer.
    suc-out-rev : (h : ⟨ γ ⊨ PrefixAt t b a ⟩)
            → (b₀ : ℕ) → fst (lookup b γ) ≡ # b₀
            → (m k₀ : ℕ) → m < b₀ → k₀ ≤ b₀
            → fst (lookup l γ) ≡ # m → fst (lookup k γ) ≡ # k₀
            → (E' : S) → ⟨ pr (pr (# (suc m)) (# k₀)) (fst E')
                            ∈ fst (lookup t γ) ⟩
            → ∥ Σ[ E ∈ S ] Σ[ L ∈ S ]
                 ( ⟨ pr (pr (# m) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩
                 × (fst E' ≡ fst E ∪ fst L)
                 × ( (z : S) → ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                         → ⟨ fst z ∈ fst L ⟩ ) ) ∥₁


    suc-out-rev h b₀ qb m k₀ m<b₀ k₀≤b₀ ql qk E' eE' =
      PT.rec squash₁ (λ { (s₁ , w₁) → PT.rec squash₁ (λ { (κ₁ , w₂) →
        PT.rec squash₁ (λ { (κ₂ , w₃) → PT.rec squash₁ (λ { (E'c , w₄) →
          PT.rec squash₁ (λ { (E , w₅) → PT.rec squash₁ (λ { (L , w₆) →
            finish s₁ κ₁ κ₂ E'c E L w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
        ((h .snd .snd .snd .snd .snd) n'm k'₀ cond-sat)
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
                               ∧̇ ∀̇ ( LayerDisjAt zero (sh9 t)
                                         (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
                                         (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                         (sh9 a) ⇒̇ (var zero ∈̇ var (suc zero)) ) ) ) ) ) ) ) ⟩
             → ∥ Σ[ E ∈ S ] Σ[ L ∈ S ]
                  ( ⟨ pr (pr (# m) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩
                  × (fst E' ≡ fst E ∪ fst L)
                  × ( (z : S) → ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                          → ⟨ fst z ∈ fst L ⟩ ) ) ∥₁


      finish s₁ κ₁ κ₂ E'c E L w₆ = ∣ E , L , (eE , (unEq , layerIn)) ∣₁
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
          hLayerRev = w₆ .snd .snd .snd .snd .snd .snd
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
          layerIn : (z : S) → ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                          → ⟨ fst z ∈ fst L ⟩
          layerIn z hz = go hz
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
            -- The per-disjunct RDI-to-CLI converters: read the goal-level
            -- disjunct into the meta shape with RDI's out-reader, rebuild the
            -- clause-level disjunct with CLI's in-reader.
            hInt'' : ⟨ (z ∷ γ) ⊨ InterDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                   → ⟨ clEnv ⊨ InterDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
            hInt'' h = PT.rec (snd (clEnv ⊨ InterDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
              (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
                CLI.InterDisj-in m k₀ z W eW X Y hX hY e qlm qkk })
              (RDI.InterDisj-out m k₀ z h ql qk)
            hUn'' : ⟨ (z ∷ γ) ⊨ UnionDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                  → ⟨ clEnv ⊨ UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
            hUn'' h = PT.rec (snd (clEnv ⊨ UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
              (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
                CLI.UnionDisj-in m k₀ z W eW X Y hX hY e qlm qkk })
              (RDI.UnionDisj-out m k₀ z h ql qk)
            hDi'' : ⟨ (z ∷ γ) ⊨ DiffDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                  → ⟨ clEnv ⊨ DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
            hDi'' h = PT.rec (snd (clEnv ⊨ DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
              (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
                CLI.DiffDisj-in m k₀ z W eW X Y hX hY e qlm qkk })
              (RDI.DiffDisj-out m k₀ z h ql qk)
            hM'' : ⟨ (z ∷ γ) ⊨ SelMDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ⟨ clEnv ⊨ SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
            hM'' h = PT.rec (snd (clEnv ⊨ SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
              (λ { (W , X , i , j , (eW , (hX , (hi , (hj , e))))) →
                CLI.SelMDisj-in m k₀ z W eW X i j hX hi hj e qlm qkk })
              (RDI.SelMDisj-out m k₀ z h ql qk)
            hE'' : ⟨ (z ∷ γ) ⊨ SelEDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ⟨ clEnv ⊨ SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
            hE'' h = PT.rec (snd (clEnv ⊨ SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
              (λ { (W , X , i , j , (eW , (hX , (hi , (hj , e))))) →
                CLI.SelEDisj-in m k₀ z W eW X i j hX hi hj e qlm qkk })
              (RDI.SelEDisj-out m k₀ z h ql qk)
            hA'' : ⟨ (z ∷ γ) ⊨ AllTuplesDisjAt zero (suc a) (suc k) ⟩
                 → ⟨ clEnv ⊨ AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
            hA'' h = CLI.AllTuplesDisj-in m k₀ z (RDI.AllTuplesDisj-out m k₀ z h qk) qkk
            hX'' : ⟨ (z ∷ γ) ⊨ ExtDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                 → ⟨ clEnv ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
            hX'' h = PT.rec (snd (clEnv ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
              (λ { (s , w₁) → PT.rec (snd (clEnv ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
                (λ { (κ , w₂) → PT.rec (snd (clEnv ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
                  (λ { (W , w₃) → PT.rec (snd (clEnv ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
                    (λ { (X , w₄) → PT.rec (snd (clEnv ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)))
                      (λ { (y , body) →
                        let envX = y ∷ X ∷ W ∷ κ ∷ s ∷ z ∷ γ
                            hSuc = subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc (suc zero))))
                                    (sh6 k) envX) (body .fst)
                            es : sucV (fst s) ≡ # k₀
                            es = sym hSuc ∙ qk
                            hPos = body .snd .fst
                            hPr = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                                    (sh6 l) (suc (suc (suc (suc zero)))) envX) (body .snd .snd .fst)
                            hApp = subst ⟨_⟩ (appAt-adequate (sh6 t)
                                     (suc (suc (suc zero))) (suc (suc zero)) envX) (body .snd .snd .snd .fst)
                            hXw = body .snd .snd .snd .snd .fst
                            hyw = body .snd .snd .snd .snd .snd .fst
                            hEx = body .snd .snd .snd .snd .snd .snd
                            eW : ⟨ pr (pr (# m) (fst s)) (fst W) ∈ fst (lookup t γ) ⟩
                            eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩)
                                   (hPr ∙ cong₂ pr ql refl) hApp
                            e' : fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
                            e' = extendFamilyAt-out (sh5 zero) (suc zero) zero envX hEx
                        in CLI.ExtDisj-in m k₀ z s (qkk ∙ sym es) hPos W eW X y hXw hyw e' qlm qkk })
                      w₄ }) w₃ }) w₂ }) w₁ }) h
            hS'' : ⟨ (z ∷ γ) ⊨ ShiftDisjAt zero (suc t) (suc l) (suc k) ⟩
                 → ⟨ clEnv ⊨ ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
            hS'' h = PT.rec (snd (clEnv ⊨ ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))))
              (λ { (W , X , (eW , (hX , e))) →
                CLI.ShiftDisj-in m k₀ z W eW X hX e qlm qkk })
              (RDI.ShiftDisj-out m k₀ z h ql qk)
            hV'' : ⟨ (z ∷ γ) ⊨ ValuesDisjAt zero (suc t) (suc l) (suc k) ⟩
                 → ⟨ clEnv ⊨ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
            hV'' h = PT.rec (snd (clEnv ⊨ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))))
              (λ { (W , X , (eW , (hX , e , zq))) →
                CLI.ValuesDisj-in m k₀ z W eW X hX e qlm qkk zq })
              (RDI.ValuesDisj-out m k₀ z h ql qk)
            step8 : ⟨ (z ∷ γ) ⊨ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ⟩
                  → ⟨ fst z ∈ fst L ⟩
            step8 h = PT.rec (snd (fst z ∈ fst L))
              (λ { (inl hSh) → hLayerRev z (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl (hS'' hSh) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)
                 ; (inr hV) → hLayerRev z (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (hV'' hV) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) }) h
            step7 : ⟨ (z ∷ γ) ⊨ ( ExtDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                ∨̇ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                   ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ) ⟩
                  → ⟨ fst z ∈ fst L ⟩
            step7 h = PT.rec (snd (fst z ∈ fst L))
              (λ { (inl hX) → hLayerRev z (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl (hX'' hX) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)
                 ; (inr hRest) → step8 hRest }) h
            step6 : ⟨ (z ∷ γ) ⊨ ( AllTuplesDisjAt zero (suc a) (suc k)
                                ∨̇ ( ExtDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                   ∨̇ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                      ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ) ) ⟩
                  → ⟨ fst z ∈ fst L ⟩
            step6 h = PT.rec (snd (fst z ∈ fst L))
              (λ { (inl hA) → hLayerRev z (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl (hA'' hA) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)
                 ; (inr hRest) → step7 hRest }) h
            step5 : ⟨ (z ∷ γ) ⊨ ( SelEDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                ∨̇ ( AllTuplesDisjAt zero (suc a) (suc k)
                                   ∨̇ ( ExtDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                      ∨̇ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                         ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ) ) ) ⟩
                  → ⟨ fst z ∈ fst L ⟩
            step5 h = PT.rec (snd (fst z ∈ fst L))
              (λ { (inl hE) → hLayerRev z (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl (hE'' hE) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)
                 ; (inr hRest) → step6 hRest }) h
            step4 : ⟨ (z ∷ γ) ⊨ ( SelMDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                ∨̇ ( SelEDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                   ∨̇ ( AllTuplesDisjAt zero (suc a) (suc k)
                                      ∨̇ ( ExtDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                         ∨̇ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                            ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ) ) ) ) ⟩
                  → ⟨ fst z ∈ fst L ⟩
            step4 h = PT.rec (snd (fst z ∈ fst L))
              (λ { (inl hM) → hLayerRev z (∣ inr (∣ inr (∣ inr (∣ inl (hM'' hM) ∣₁) ∣₁) ∣₁) ∣₁)
                 ; (inr hRest) → step5 hRest }) h
            step3 : ⟨ (z ∷ γ) ⊨ ( DiffDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                ∨̇ ( SelMDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                   ∨̇ ( SelEDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                      ∨̇ ( AllTuplesDisjAt zero (suc a) (suc k)
                                         ∨̇ ( ExtDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                            ∨̇ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                               ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ) ) ) ) ) ⟩
                  → ⟨ fst z ∈ fst L ⟩
            step3 h = PT.rec (snd (fst z ∈ fst L))
              (λ { (inl hDi) → hLayerRev z (∣ inr (∣ inr (∣ inl (hDi'' hDi) ∣₁) ∣₁) ∣₁)
                 ; (inr hRest) → step4 hRest }) h
            step2 : ⟨ (z ∷ γ) ⊨ ( UnionDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                ∨̇ ( DiffDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                   ∨̇ ( SelMDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                      ∨̇ ( SelEDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                         ∨̇ ( AllTuplesDisjAt zero (suc a) (suc k)
                                            ∨̇ ( ExtDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                               ∨̇ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                                  ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ) ) ) ) ) ) ⟩
                  → ⟨ fst z ∈ fst L ⟩
            step2 h = PT.rec (snd (fst z ∈ fst L))
              (λ { (inl hUn) → hLayerRev z (∣ inr (∣ inl (hUn'' hUn) ∣₁) ∣₁)
                 ; (inr hRest) → step3 hRest }) h
            step1 : (⟨ (z ∷ γ) ⊨ InterDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
                     ⊎ ⟨ (z ∷ γ) ⊨ ( UnionDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                    ∨̇ ( DiffDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                       ∨̇ ( SelMDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                          ∨̇ ( SelEDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                             ∨̇ ( AllTuplesDisjAt zero (suc a) (suc k)
                                                ∨̇ ( ExtDisjAt zero (suc t) (suc l) (suc k) (suc a)
                                                   ∨̇ ( ShiftDisjAt zero (suc t) (suc l) (suc k)
                                                      ∨̇ ValuesDisjAt zero (suc t) (suc l) (suc k) ) ) ) ) ) ) ) ⟩)
                  → ⟨ fst z ∈ fst L ⟩
            step1 (inl hInt) = hLayerRev z (∣ inl (hInt'' hInt) ∣₁)
            step1 (inr hRest) = step2 hRest
            go : ⟨ (z ∷ γ) ⊨ LayerDisjAt zero (suc t) (suc l) (suc k) (suc a) ⟩
               → ⟨ fst z ∈ fst L ⟩
            go hz = PT.rec (snd (fst z ∈ fst L)) step1 hz

    -- The predecessor of a numeral: `sucV x ≡ # (suc k)` pins `x ≡ # k`,
    -- because members of a numeral are lower numerals (`∈#-elim`) and `#_`
    -- is injective.
    sucV-pre : (k : ℕ) (x : V ℓ) → sucV x ≡ # (suc k) → x ≡ # k
    sucV-pre k x h = PT.rec (setIsSet x (# k)) go (∈#-elim (suc k) x x∈)
      where
      x∈ : ⟨ x ∈ˢ (# (suc k)) ⟩
      x∈ = subst (λ w → ⟨ x ∈ˢ w ⟩) h (self∈sucV x)
      go : Σ[ m ∈ ℕ ] ((m < suc k) × (x ≡ # m)) → x ≡ # k
      go (m , m< , e) = e ∙ cong #_ (injSuc (#-inj′ (sym (cong sucV e) ∙ h)))

    -- The base reader at level zero and positive arity: the entry is empty,
    -- reading `BaseS`'s ∀̇ at the successor numeral (the clause's ∀̇ ranges
    -- over the arity `suc k'` and pins the predecessor slot to `# k'`).
    baseS-out : (h : ⟨ γ ⊨ PrefixAt t b a ⟩)
              → (b₀ : ℕ) → fst (lookup b γ) ≡ # b₀
              → (k' : ℕ) → suc k' ≤ b₀
              → (E : S) → ⟨ pr (pr (# 0) (# k')) (fst E) ∈ fst (lookup t γ) ⟩
              → fst E ≡ ∅
    baseS-out h b₀ qb k' sk'≤b E eE = PT.rec (setIsSet (fst E) ∅) go₁
      ((h .snd .snd .fst) (numeralL (suc k')) cond-sat)
      where
      cond-sat : ⟨ (numeralL (suc k') ∷ γ) ⊨ inSuc zero (suc b) ⟩
      cond-sat = go (≤-split sk'≤b)
        where
        go : (suc k' < b₀) ⊎ (suc k' ≡ b₀)
           → ⟨ (numeralL (suc k') ∷ γ) ⊨ inSuc zero (suc b) ⟩
        go (inl h) = ∣ inr (subst (λ q → ⟨ fst (numeralL (suc k')) ∈ q ⟩)
          (sym qb)
          (subst (λ q → ⟨ q ∈ (# b₀) ⟩) (sym (numeralL-fst (suc k')))
            (#mono∈ (suc k') b₀ h))) ∣₁
        go (inr e) = ∣ inl (cong fst (cong numeralL e) ∙ numeralL-fst b₀ ∙ sym qb) ∣₁

      go₄ : (W κ k'' n0 : S)
          → ⟨ (W ∷ κ ∷ k'' ∷ n0 ∷ numeralL (suc k') ∷ γ)
                ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                  ∧̇ ( sucAtL (suc (suc zero)) (suc (suc (suc (suc zero))))
                    ∧̇ ( prAtL (suc zero) (suc (suc (suc zero))) (suc (suc zero))
                      ∧̇ ( appAt (sh5 t) (suc zero) zero
                        ∧̇ var zero ≐ con ∅ʟ ) ) ) ) ⟩
          → fst E ≡ ∅
      go₄ W κ k'' n0 body =
        let env = W ∷ κ ∷ k'' ∷ n0 ∷ numeralL (suc k') ∷ γ
            hSuc = subst ⟨_⟩ (sucAtL-adequate (suc (suc zero)) (suc (suc (suc (suc zero)))) env)
                     (body .snd .fst)
            hPr = subst ⟨_⟩ (prAtL-adequate (suc zero) (suc (suc (suc zero))) (suc (suc zero)) env)
                     (body .snd .snd .fst)
            hApp = subst ⟨_⟩ (appAt-adequate (sh5 t) (suc zero) zero env)
                     (body .snd .snd .snd .fst)
            h∅ = body .snd .snd .snd .snd
            k''≡ : fst k'' ≡ # k'
            k''≡ = sucV-pre k' (fst k'')
                     (sym hSuc ∙ numeralL-fst (suc k'))
            key : fst κ ≡ pr (# 0) (# k')
            key = hPr ∙ cong₂ pr (body .fst ∙ numeralL-fst 0) k''≡
            eW : ⟨ pr (pr (# 0) (# k')) (fst W) ∈ fst (lookup t γ) ⟩
            eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩) key hApp
            u : S
            u = prʟ (numeralL 0) (numeralL k')
            u≡ : fst u ≡ pr (# 0) (# k')
            u≡ = prʟ-fst (numeralL 0) (numeralL k')
              ∙ cong₂ pr (numeralL-fst 0) (numeralL-fst k')
            eq : fst E ≡ fst W
            eq = fun-out (h .fst) u E W
              (subst (λ q → ⟨ pr q (fst E) ∈ fst (lookup t γ) ⟩) (sym u≡) eE)
              (subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩) (sym u≡) eW)
            W≡∅ : fst W ≡ ∅
            W≡∅ = h∅
        in eq ∙ W≡∅

      go₃ : (κ k'' n0 : S)
          → ∥ Σ[ W ∈ S ]
              ⟨ (W ∷ κ ∷ k'' ∷ n0 ∷ numeralL (suc k') ∷ γ)
                  ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                    ∧̇ ( sucAtL (suc (suc zero)) (suc (suc (suc (suc zero))))
                      ∧̇ ( prAtL (suc zero) (suc (suc (suc zero))) (suc (suc zero))
                        ∧̇ ( appAt (sh5 t) (suc zero) zero
                          ∧̇ var zero ≐ con ∅ʟ ) ) ) ) ⟩ ∥₁
          → fst E ≡ ∅
      go₃ κ k'' n0 = PT.rec (setIsSet (fst E) ∅) (λ { (W , w) → go₄ W κ k'' n0 w })

      go₂ : (n0 k'' : S)
          → ∥ Σ[ κ ∈ S ] ∥ Σ[ W ∈ S ]
              ⟨ (W ∷ κ ∷ k'' ∷ n0 ∷ numeralL (suc k') ∷ γ)
                  ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                    ∧̇ ( sucAtL (suc (suc zero)) (suc (suc (suc (suc zero))))
                      ∧̇ ( prAtL (suc zero) (suc (suc (suc zero))) (suc (suc zero))
                        ∧̇ ( appAt (sh5 t) (suc zero) zero
                          ∧̇ var zero ≐ con ∅ʟ ) ) ) ) ⟩ ∥₁ ∥₁
          → fst E ≡ ∅
      go₂ n0 k'' = PT.rec (setIsSet (fst E) ∅) (λ { (κ , w₃) → go₃ κ k'' n0 w₃ })

      go₁ : Σ[ n0 ∈ S ] ∥ Σ[ k'' ∈ S ] ∥ Σ[ κ ∈ S ] ∥ Σ[ W ∈ S ]
             ⟨ (W ∷ κ ∷ k'' ∷ n0 ∷ numeralL (suc k') ∷ γ)
                 ⊨ ( var (suc (suc (suc zero))) ≐ con (numeralL 0)
                   ∧̇ ( sucAtL (suc (suc zero)) (suc (suc (suc (suc zero))))
                     ∧̇ ( prAtL (suc zero) (suc (suc (suc zero))) (suc (suc zero))
                       ∧̇ ( appAt (sh5 t) (suc zero) zero
                         ∧̇ var zero ≐ con ∅ʟ ) ) ) ) ⟩ ∥₁ ∥₁ ∥₁
           → fst E ≡ ∅
      go₁ (n0 , w₁) = PT.rec (setIsSet (fst E) ∅) (λ { (k'' , w₂) → go₂ n0 k'' w₂ }) w₁

    -- The domain-adequacy reader: every key (n, k) with n ≤ b and k ≤ b + 1
    -- is present, extracting the entry witness.
    domadeq-out : (h : ⟨ γ ⊨ PrefixAt t b a ⟩)
                → (b₀ : ℕ) → fst (lookup b γ) ≡ # b₀
                → (n' k' : ℕ) → n' ≤ b₀ → k' ≤ suc b₀
                → ∥ Σ[ E ∈ S ] ⟨ pr (pr (# n') (# k')) (fst E) ∈ fst (lookup t γ) ⟩ ∥₁
    domadeq-out h b₀ qb n' k' n≤b k≤sb = PT.rec squash₁ (λ { (κ , w₂) →
      PT.rec squash₁ (λ { (W , w₃) →
        let eW : ⟨ pr (pr (# n') (# k')) (fst W) ∈ fst (lookup t γ) ⟩
            eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩)
                   (subst ⟨_⟩ (prAtL-adequate (suc zero) (suc (suc (suc zero))) (suc (suc zero))
                     (W ∷ κ ∷ numeralL k' ∷ numeralL n' ∷ γ)) (w₃ .fst)
                     ∙ cong₂ pr (numeralL-fst n') (numeralL-fst k'))
                   (subst ⟨_⟩ (appAt-adequate (sh4 t) (suc zero) zero
                     (W ∷ κ ∷ numeralL k' ∷ numeralL n' ∷ γ)) (w₃ .snd))
        in ∣ W , eW ∣₁ }) w₂ })
      ((h .snd .snd .snd .snd .fst) (numeralL n') (numeralL k') cond-sat)
      where
      env = numeralL k' ∷ numeralL n' ∷ γ
      cond-sat : ⟨ env ⊨ ( inSuc (suc zero) (suc (suc b))
                         ∧̇ inSucSuc zero (suc (suc b)) ) ⟩
      cond-sat = hN≤b , hK≤sb
        where
        hN≤b : ⟨ env ⊨ inSuc (suc zero) (suc (suc b)) ⟩
        hN≤b = goN (≤-split n≤b)
          where
          goN : (n' < b₀) ⊎ (n' ≡ b₀)
              → ⟨ env ⊨ inSuc (suc zero) (suc (suc b)) ⟩
          goN (inl h) = ∣ inr (subst (λ q → ⟨ fst (numeralL n') ∈ q ⟩)
            (sym qb)
            (subst (λ q → ⟨ q ∈ (# b₀) ⟩) (sym (numeralL-fst n'))
              (#mono∈ n' b₀ h))) ∣₁
          goN (inr e) = ∣ inl (cong fst (cong numeralL e) ∙ numeralL-fst b₀ ∙ sym qb) ∣₁
        hK≤sb : ⟨ env ⊨ inSucSuc zero (suc (suc b)) ⟩
        hK≤sb = ∣ sucʟ (numeralL b₀)
          , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc (suc (suc b))) zero
                (sucʟ (numeralL b₀) ∷ numeralL k' ∷ numeralL n' ∷ γ)))
              (sucʟ-fst (numeralL b₀) ∙ cong sucV (numeralL-fst b₀)
                ∙ cong sucV (sym qb))
            , ∣ sucʟ (sucʟ (numeralL b₀))
                , ( subst ⟨_⟩ (sym (sucAtL-adequate (suc zero) zero
                      (sucʟ (sucʟ (numeralL b₀)) ∷ sucʟ (numeralL b₀)
                        ∷ numeralL k' ∷ numeralL n' ∷ γ)))
                    (sucʟ-fst (sucʟ (numeralL b₀)))
                  , subst (λ q → ⟨ q ∈ fst (sucʟ (sucʟ (numeralL b₀))) ⟩)
                      (sym (numeralL-fst k'))
                      (subst (λ q → ⟨ # k' ∈ q ⟩) (sym s₂≡)
                        (le-member k' (suc b₀) k≤sb)) ) ∣₁ ) ∣₁
              where
              s₂≡ : fst (sucʟ (sucʟ (numeralL b₀))) ≡ # (suc (suc b₀))
              s₂≡ = sucʟ-fst (sucʟ (numeralL b₀))
                ∙ cong sucV (sucʟ-fst (numeralL b₀))
                ∙ cong sucV (cong sucV (numeralL-fst b₀))


    -- The pinning theorem.  Any table satisfying `PrefixAt` at bound b has
    -- its entry at every key (n, k) with n ≤ b and k < b equal to the meta
    -- slice, by induction on the level numeral.  The layer at the successor
    -- key is identified with the meta step per level, at the clause's own
    -- numerals (the binders), so the layer directions are the clause body's
    -- witnesses and no environment conversion is needed: the recursion
    -- pins every arity the clauses shop on (the same arity, one up, the
    -- arity-one shelf, and one down), so the strict range is forced by
    -- those shelves themselves: at successor levels the arity is at least
    -- two (the extension reads one arity down) and the level-plus-arity
    -- stays below the bound, so each shelf is pinned at the level below
    -- (`DomAdeq` presents the top shelf but no clause constrains it).

    m+sn : (m n : ℕ) → m + suc n ≡ suc m + n
    m+sn zero n = refl
    m+sn (suc m) n = +-suc (suc m) n

    m+2≡sucsuc : (m : ℕ) → m + 2 ≡ suc (suc m)
    m+2≡sucsuc m = +-suc m (suc zero) ∙ cong suc (+-suc m zero)
      ∙ cong (λ w → suc (suc w)) (+-zero m)

    ∸1≤ : (k : ℕ) → k ∸ 1 ≤ k
    ∸1≤ zero = ≤-refl
    ∸1≤ (suc k) = ≤-sucℕ

    -- The pinning's arithmetic: the combined condition `n₀ + suc k₀ < b₀`
    -- (level plus arity below the bound) is closed under exactly the shelves
    -- the layer's disjuncts shop on.  The same-arity and shift pins stay
    -- below the bound by the level-plus-arity shape (`m + suc (suc k)` is
    -- `suc m + suc k` up to `m+sn`), the values shelf at arity zero and the
    -- extension shelf one down are bounded by the monotonicity chain, and
    -- the successor clause's own range conditions follow from the bound.
    m+sk<sm+sk : (m k : ℕ) → m + suc k < suc m + suc k
    m+sk<sm+sk m k = ≤-refl

    cond-same : (m k b : ℕ) → suc m + suc k < b → m + suc k < b
    cond-same m k b h = <-trans (m+sk<sm+sk m k) h

    cond-shift : (m k b : ℕ) → suc m + suc k < b → m + suc (suc k) < b
    cond-shift m k b h = subst (λ w → w < b) (sym (m+sn m (suc k))) h

    +-mono-≤r : (a b m : ℕ) → a ≤ b → m + a ≤ m + b
    +-mono-≤r a b m p = ≤-+-≤ ≤-refl p

    m<sm+sk : (m k : ℕ) → m < suc m + suc k
    m<sm+sk m k = ≤-+k-trans {m = suc m} {k = suc k} ≤-refl

    k<sm+sk : (m k : ℕ) → k < suc m + suc k
    k<sm+sk m k = suc m , refl

    cond-m<b : (m k b : ℕ) → suc m + suc k < b → m < b
    cond-m<b m k b h = <-trans (m<sm+sk m k) h

    cond-k≤b : (m k b : ℕ) → suc m + suc k < b → k ≤ b
    cond-k≤b m k b h = ≤-trans ≤-sucℕ (<-trans (k<sm+sk m k) h)

    cond-ext : (m k'' k₀ b : ℕ) → k'' < k₀ → suc m + suc k₀ < b
             → m + suc k'' < b
    cond-ext m k'' k₀ b h₀ h = <-trans (<-trans step (m+sk<sm+sk m k₀)) h
      where
      k₀<s : m + k₀ < m + suc k₀
      k₀<s = subst (λ w → suc (m + k₀) ≤ w) (sym (+-suc m k₀)) ≤-refl
      step : m + suc k'' < m + suc k₀
      step = ≤<-trans (+-mono-≤r (suc k'') k₀ m h₀) k₀<s

    cond-values : (m k₀ b : ℕ) → k₀ ≡ 0 → suc m + suc k₀ < b
                → m + suc 1 < b
    cond-values m k₀ b zq h =
      subst (λ k → m + suc (suc k) < b) zq (cond-shift m k₀ b h)

    -- The layer disjunction at the clause's own numerals (the binders), and
    -- the two successor clause bodies, abbreviating the giant types below.
    layerDisjCl : Formula S (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))
    layerDisjCl = LayerDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)

    sucBody : Formula S (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
    sucBody = sucAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero)))))
            ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero))))))
              ∧̇ ( appAt (sh8 t) (suc (suc (suc (suc zero)))) (suc (suc zero))
                ∧̇ ( prAtL (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero))))))
                  ∧̇ ( appAt (sh8 t) (suc (suc (suc zero))) (suc zero)
                    ∧̇ ( unionAt (suc (suc zero)) (suc zero) zero
                      ∧̇ ∀̇ ( (var zero ∈̇ var (suc zero)) ⇒̇
                            ( (var zero ∈̇ var (suc (suc zero)))
                            ∨̇ layerDisjCl ) ) ) ) ) ) )

    sucBodyRev : Formula S (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
    sucBodyRev = sucAtL (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero)))))
               ∧̇ ( prAtL (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero))))))
                 ∧̇ ( appAt (sh8 t) (suc (suc (suc (suc zero)))) (suc (suc zero))
                   ∧̇ ( prAtL (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero))))))
                     ∧̇ ( appAt (sh8 t) (suc (suc (suc zero))) (suc zero)
                       ∧̇ ( unionAt (suc (suc zero)) (suc zero) zero
                         ∧̇ ∀̇ ( layerDisjCl ⇒̇ (var zero ∈̇ var (suc zero)) ) ) ) ) ) )

    -- The concrete clause environment, from the clause's own binders, so
    -- the layer machinery's slots reduce to the table's.
    clEnvF : (m k'' : ℕ) → (s₁ κ₁ κ₂ E'c E L : S) → S ^ (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
    clEnvF m k'' s₁ κ₁ κ₂ E'c E L =
      L ∷ E ∷ E'c ∷ κ₂ ∷ κ₁ ∷ s₁ ∷ numeralL k'' ∷ numeralL m ∷ γ

    -- The clause-level successor reader: both clauses at the binder numerals
    -- (m, k''), returning the previous entry, the layer, the union equation,
    -- and both per-member layer directions, each over its own clause
    -- environment.  The forward direction is `SucClause`'s ∀̇, the reverse
    -- `SucClauseRev`'s; both read the layer disjunction at the binders, so
    -- any column is readable without the environment's arity slot.
    suc-clause : (h : ⟨ γ ⊨ PrefixAt t b a ⟩)
               → (b₀ : ℕ) → fst (lookup b γ) ≡ # b₀
               → (m k'' : ℕ) → m < b₀ → k'' ≤ b₀
               → (E' : S) → ⟨ pr (pr (# (suc m)) (# k'')) (fst E')
                               ∈ fst (lookup t γ) ⟩
               → ∥ Σ[ s₁ ∈ S ] Σ[ κ₁ ∈ S ] Σ[ κ₂ ∈ S ] Σ[ E'c ∈ S ] Σ[ E ∈ S ] Σ[ L ∈ S ]
                    ( ⟨ pr (pr (# m) (# k'')) (fst E) ∈ fst (lookup t γ) ⟩
                    × (fst E' ≡ fst E ∪ fst L)
                    × ( (z : S) → ⟨ fst z ∈ fst L ⟩
                                → ∥ ⟨ fst z ∈ fst E ⟩ ⊎
                                    ⟨ (z ∷ clEnvF m k'' s₁ κ₁ κ₂ E'c E L) ⊨ layerDisjCl ⟩ ∥₁ )
                    × ( ∥ Σ[ s₁₀ ∈ S ] Σ[ κ₁₀ ∈ S ] Σ[ κ₂₀ ∈ S ] Σ[ E'c₀ ∈ S ]
                            Σ[ E₀ ∈ S ] Σ[ L₀ ∈ S ]
                            ( ⟨ pr (pr (# m) (# k'')) (fst E₀) ∈ fst (lookup t γ) ⟩
                            × (fst E' ≡ fst E₀ ∪ fst L₀)
                            × ( (z : S) → ⟨ (z ∷ clEnvF m k'' s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀) ⊨ layerDisjCl ⟩
                                        → ⟨ fst z ∈ fst L₀ ⟩ ) ) ∥₁ ) ) ∥₁
    suc-clause h b₀ qb m k'' m<b₀ k''≤b₀ E' eE' =
      PT.rec squash₁ (λ { (s₁ , w₁) → PT.rec squash₁ (λ { (κ₁ , w₂) →
        PT.rec squash₁ (λ { (κ₂ , w₃) → PT.rec squash₁ (λ { (E'c , w₄) →
          PT.rec squash₁ (λ { (E , w₅) → PT.rec squash₁ (λ { (L , w₆) →
            finish s₁ κ₁ κ₂ E'c E L w₆ }) w₅ }) w₄ }) w₃ }) w₂ }) w₁ })
        ((h .snd .snd .snd .fst) n'm k'₀ cond-sat)
      where
      n'm = numeralL m
      k'₀ = numeralL k''

      cond-sat : ⟨ (k'₀ ∷ n'm ∷ γ)
                     ⊨ ( (var (suc zero) ∈̇ var (suc (suc b)))
                       ∧̇ inSuc zero (suc (suc b)) ) ⟩
      cond-sat = hN'∈b , hInSuc
        where
        hN'∈b : ⟨ (k'₀ ∷ n'm ∷ γ) ⊨ var (suc zero) ∈̇ var (suc (suc b)) ⟩
        hN'∈b = subst (λ q → ⟨ q ∈ fst (lookup b γ) ⟩) (sym (numeralL-fst m))
          (subst (λ q → ⟨ # m ∈ q ⟩) (sym qb) (#mono∈ m b₀ m<b₀))
        hInSuc : ⟨ (k'₀ ∷ n'm ∷ γ) ⊨ inSuc zero (suc (suc b)) ⟩
        hInSuc = go (≤-split k''≤b₀)
          where
          go : (k'' < b₀) ⊎ (k'' ≡ b₀)
             → ⟨ (k'₀ ∷ n'm ∷ γ) ⊨ inSuc zero (suc (suc b)) ⟩
          go (inl h) = ∣ inr (subst (λ q → ⟨ fst (numeralL k'') ∈ q ⟩)
            (sym qb)
            (subst (λ q → ⟨ q ∈ (# b₀) ⟩) (sym (numeralL-fst k''))
              (#mono∈ k'' b₀ h))) ∣₁
          go (inr e) = ∣ inl (cong fst (cong numeralL e)
            ∙ numeralL-fst b₀ ∙ sym qb) ∣₁

      finish : (s₁ κ₁ κ₂ E'c E L : S)
             → ⟨ (L ∷ E ∷ E'c ∷ κ₂ ∷ κ₁ ∷ s₁ ∷ k'₀ ∷ n'm ∷ γ) ⊨ sucBody ⟩
             → ∥ Σ[ s₁ ∈ S ] Σ[ κ₁ ∈ S ] Σ[ κ₂ ∈ S ] Σ[ E'c ∈ S ] Σ[ E ∈ S ] Σ[ L ∈ S ]
                  ( ⟨ pr (pr (# m) (# k'')) (fst E) ∈ fst (lookup t γ) ⟩
                  × (fst E' ≡ fst E ∪ fst L)
                  × ( (z : S) → ⟨ fst z ∈ fst L ⟩
                              → ∥ ⟨ fst z ∈ fst E ⟩ ⊎
                                  ⟨ (z ∷ clEnvF m k'' s₁ κ₁ κ₂ E'c E L) ⊨ layerDisjCl ⟩ ∥₁ )
                  × ( ∥ Σ[ s₁₀ ∈ S ] Σ[ κ₁₀ ∈ S ] Σ[ κ₂₀ ∈ S ] Σ[ E'c₀ ∈ S ]
                          Σ[ E₀ ∈ S ] Σ[ L₀ ∈ S ]
                          ( ⟨ pr (pr (# m) (# k'')) (fst E₀) ∈ fst (lookup t γ) ⟩
                          × (fst E' ≡ fst E₀ ∪ fst L₀)
                          × ( (z : S) → ⟨ (z ∷ clEnvF m k'' s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀) ⊨ layerDisjCl ⟩
                                      → ⟨ fst z ∈ fst L₀ ⟩ ) ) ∥₁ ) ) ∥₁
      finish s₁ κ₁ κ₂ E'c E L w₆ =
        ∣ s₁ , κ₁ , κ₂ , E'c , E , L , (eE , (unEq , (layerOut , rev))) ∣₁
        where
        env = L ∷ E ∷ E'c ∷ κ₂ ∷ κ₁ ∷ s₁ ∷ k'₀ ∷ n'm ∷ γ
        hSuc = subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) env) (w₆ .fst)
        hPr₁ = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) env)
                      (w₆ .snd .fst)
        hApp₁ = subst ⟨_⟩ (appAt-adequate (sh8 t) (suc (suc (suc (suc zero)))) (suc (suc zero)) env)
                      (w₆ .snd .snd .fst)
        hPr₂ = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) env)
                      (w₆ .snd .snd .snd .fst)
        hApp₂ = subst ⟨_⟩ (appAt-adequate (sh8 t) (suc (suc (suc zero))) (suc zero) env)
                      (w₆ .snd .snd .snd .snd .fst)
        hUn = w₆ .snd .snd .snd .snd .snd .fst
        hLayer = w₆ .snd .snd .snd .snd .snd .snd
        key₂ : fst κ₂ ≡ pr (# m) (# k'')
        key₂ = hPr₂ ∙ cong₂ pr (numeralL-fst m) (numeralL-fst k'')
        eE : ⟨ pr (pr (# m) (# k'')) (fst E) ∈ fst (lookup t γ) ⟩
        eE = subst (λ q → ⟨ pr q (fst E) ∈ fst (lookup t γ) ⟩) key₂ hApp₂
        es₁ : fst s₁ ≡ sucV (# m)
        es₁ = hSuc ∙ cong sucV (numeralL-fst m)
        key₁ : fst κ₁ ≡ pr (# (suc m)) (# k'')
        key₁ = hPr₁ ∙ cong₂ pr es₁ (numeralL-fst k'')
        eE'c : ⟨ pr (pr (# (suc m)) (# k'')) (fst E'c) ∈ fst (lookup t γ) ⟩
        eE'c = subst (λ q → ⟨ pr q (fst E'c) ∈ fst (lookup t γ) ⟩) key₁ hApp₁
        u : S
        u = prʟ (sucʟ (numeralL m)) (numeralL k'')
        u≡ : fst u ≡ pr (# (suc m)) (# k'')
        u≡ = prʟ-fst (sucʟ (numeralL m)) (numeralL k'')
          ∙ cong₂ pr (sucʟ-fst (numeralL m)
              ∙ cong sucV (numeralL-fst m)) (numeralL-fst k'')
        eqE' : fst E' ≡ fst E'c
        eqE' = fun-out (h .fst) u E' E'c
          (subst (λ q → ⟨ pr q (fst E') ∈ fst (lookup t γ) ⟩) (sym u≡) eE')
          (subst (λ q → ⟨ pr q (fst E'c) ∈ fst (lookup t γ) ⟩) (sym u≡) eE'c)
        unEq : fst E' ≡ fst E ∪ fst L
        unEq = eqE' ∙ unionAt-out (suc (suc zero)) (suc zero) zero env hUn
        layerOut : (z : S) → ⟨ fst z ∈ fst L ⟩
                 → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ env) ⊨ layerDisjCl ⟩ ∥₁
        layerOut z hz = hLayer z hz

        -- The reverse clause's unpacking, for the layer-in direction: the
        -- layer disjunction reads the same slots in either clause env, so
        -- the reverse ∀̇ is used over its own env, and the union equations
        -- bridge the two layers at the union level.
        finish' : (s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀ : S)
                → ⟨ (L₀ ∷ E₀ ∷ E'c₀ ∷ κ₂₀ ∷ κ₁₀ ∷ s₁₀ ∷ k'₀ ∷ n'm ∷ γ)
                      ⊨ sucBodyRev ⟩
                → ∥ Σ[ s₁₀ ∈ S ] Σ[ κ₁₀ ∈ S ] Σ[ κ₂₀ ∈ S ] Σ[ E'c₀ ∈ S ]
                     Σ[ E₀ ∈ S ] Σ[ L₀ ∈ S ]
                     ( ⟨ pr (pr (# m) (# k'')) (fst E₀) ∈ fst (lookup t γ) ⟩
                     × (fst E' ≡ fst E₀ ∪ fst L₀)
                     × ( (z : S) → ⟨ (z ∷ clEnvF m k'' s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀) ⊨ layerDisjCl ⟩
                                 → ⟨ fst z ∈ fst L₀ ⟩ ) ) ∥₁
        finish' s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀ w₆' =
          ∣ s₁₀ , κ₁₀ , κ₂₀ , E'c₀ , E₀ , L₀ , (eE₀ , (unEq₀ , layerIn)) ∣₁
          where
          env' = L₀ ∷ E₀ ∷ E'c₀ ∷ κ₂₀ ∷ κ₁₀ ∷ s₁₀ ∷ k'₀ ∷ n'm ∷ γ
          hPr₂₀ = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) env')
                        (w₆' .snd .snd .snd .fst)
          hApp₂₀ = subst ⟨_⟩ (appAt-adequate (sh8 t) (suc (suc (suc zero))) (suc zero) env')
                        (w₆' .snd .snd .snd .snd .fst)
          hSuc₀ = subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) env') (w₆' .fst)
          hPr₁₀ = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) env')
                        (w₆' .snd .fst)
          hApp₁₀ = subst ⟨_⟩ (appAt-adequate (sh8 t) (suc (suc (suc (suc zero)))) (suc (suc zero)) env')
                        (w₆' .snd .snd .fst)
          hUn₀ = w₆' .snd .snd .snd .snd .snd .fst
          hLayerRev = w₆' .snd .snd .snd .snd .snd .snd
          key₂₀ : fst κ₂₀ ≡ pr (# m) (# k'')
          key₂₀ = hPr₂₀ ∙ cong₂ pr (numeralL-fst m) (numeralL-fst k'')
          eE₀ : ⟨ pr (pr (# m) (# k'')) (fst E₀) ∈ fst (lookup t γ) ⟩
          eE₀ = subst (λ q → ⟨ pr q (fst E₀) ∈ fst (lookup t γ) ⟩) key₂₀ hApp₂₀
          es₁₀ : fst s₁₀ ≡ sucV (# m)
          es₁₀ = hSuc₀ ∙ cong sucV (numeralL-fst m)
          key₁₀ : fst κ₁₀ ≡ pr (# (suc m)) (# k'')
          key₁₀ = hPr₁₀ ∙ cong₂ pr es₁₀ (numeralL-fst k'')
          eE'c₀ : ⟨ pr (pr (# (suc m)) (# k'')) (fst E'c₀) ∈ fst (lookup t γ) ⟩
          eE'c₀ = subst (λ q → ⟨ pr q (fst E'c₀) ∈ fst (lookup t γ) ⟩) key₁₀ hApp₁₀
          u₀ : S
          u₀ = prʟ (sucʟ (numeralL m)) (numeralL k'')
          u≡₀ : fst u₀ ≡ pr (# (suc m)) (# k'')
          u≡₀ = prʟ-fst (sucʟ (numeralL m)) (numeralL k'')
            ∙ cong₂ pr (sucʟ-fst (numeralL m)
                ∙ cong sucV (numeralL-fst m)) (numeralL-fst k'')
          eqE'₀ : fst E' ≡ fst E'c₀
          eqE'₀ = fun-out (h .fst) u₀ E' E'c₀
            (subst (λ q → ⟨ pr q (fst E') ∈ fst (lookup t γ) ⟩) (sym u≡₀) eE')
            (subst (λ q → ⟨ pr q (fst E'c₀) ∈ fst (lookup t γ) ⟩) (sym u≡₀) eE'c₀)
          unEq₀ : fst E' ≡ fst E₀ ∪ fst L₀
          unEq₀ = eqE'₀ ∙ unionAt-out (suc (suc zero)) (suc zero) zero env' hUn₀
          layerIn : (z : S) → ⟨ (z ∷ env') ⊨ layerDisjCl ⟩ → ⟨ fst z ∈ fst L₀ ⟩
          layerIn z hz = hLayerRev z hz
        rev : ∥ Σ[ s₁₀ ∈ S ] Σ[ κ₁₀ ∈ S ] Σ[ κ₂₀ ∈ S ] Σ[ E'c₀ ∈ S ]
                Σ[ E₀ ∈ S ] Σ[ L₀ ∈ S ]
                ( ⟨ pr (pr (# m) (# k'')) (fst E₀) ∈ fst (lookup t γ) ⟩
                × (fst E' ≡ fst E₀ ∪ fst L₀)
                × ( (z : S) → ⟨ (z ∷ clEnvF m k'' s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀) ⊨ layerDisjCl ⟩
                            → ⟨ fst z ∈ fst L₀ ⟩ ) ) ∥₁
        rev = PT.rec squash₁ (λ { (s₁₀ , w₁') → PT.rec squash₁ (λ { (κ₁₀ , w₂') →
                PT.rec squash₁ (λ { (κ₂₀ , w₃') → PT.rec squash₁ (λ { (E'c₀ , w₄') →
                  PT.rec squash₁ (λ { (E₀ , w₅') → PT.rec squash₁ (λ { (L₀ , w₆') →
                    finish' s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀ w₆' }) w₅' }) w₄' }) w₃' }) w₂' }) w₁' })
            ((h .snd .snd .snd .snd .snd) n'm k'₀ cond-sat)

    -- The pinning theorem.  Any table satisfying `PrefixAt` at bound b has
    -- its entry at every key (n₀, k₀) with the combined condition
    -- `n₀ + suc k₀ < b₀` (level plus arity below the bound) equal to the
    -- meta slice, by induction on the level numeral.  At the successor key
    -- the entry is the union of the previous entry with the layer; the two
    -- per-member directions are the clause bodies' own witnesses
    -- (`suc-clause`'s `layerOut` and the reverse `layerIn`), read at the
    -- clause's binder numerals, and the layer disjunction is dispatched per
    -- disjunct against the meta `stepImage` laws: the recursion pins every
    -- shelf the clauses shop on (the same arity, one up, one down, and the
    -- arity-one values shelf), which is exactly why the statement quantifies
    -- all keys at once.
    prefix-pins : (h : ⟨ γ ⊨ PrefixAt t b a ⟩)
                → (b₀ : ℕ) → fst (lookup b γ) ≡ # b₀
                → (qa : fst (lookup a γ) ≡ A)
                → (n₀ k₀ : ℕ) → n₀ + suc k₀ < b₀
                → (E : S) → ⟨ pr (pr (# n₀) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩
                → fst E ≡ C.slice A n₀ k₀
    prefix-pins h b₀ qb qa zero zero cond E eE =
      base0-out h E eE ∙ cong (C.singletons A) qa
    prefix-pins h b₀ qb qa zero (suc k') cond E eE =
      baseS-out h b₀ qb (suc k') (≤-trans ≤-sucℕ cond) E eE
    prefix-pins h b₀ qb qa (suc m) k₀ cond E' eE' =
      PT.rec (setIsSet (fst E') (C.slice A (suc m) k₀))
        (λ { (s₁ , (κ₁ , (κ₂ , (E'c , (E , (L , w₆)))))) →
          finish s₁ κ₁ κ₂ E'c E L w₆ })
        (suc-clause h b₀ qb m k₀ m<b₀ k₀≤b₀ E' eE')
      where
      m<b₀ : m < b₀
      m<b₀ = cond-m<b m k₀ b₀ cond
      k₀≤b₀ : k₀ ≤ b₀
      k₀≤b₀ = cond-k≤b m k₀ b₀ cond
      m≤b₀ : m ≤ b₀
      m≤b₀ = ≤-trans ≤-sucℕ m<b₀

      finish : (s₁ κ₁ κ₂ E'c E L : S)
             → ( ⟨ pr (pr (# m) (# k₀)) (fst E) ∈ fst (lookup t γ) ⟩
               × (fst E' ≡ fst E ∪ fst L)
               × ( (z : S) → ⟨ fst z ∈ fst L ⟩
                           → ∥ ⟨ fst z ∈ fst E ⟩ ⊎ ⟨ (z ∷ clEnvF m k₀ s₁ κ₁ κ₂ E'c E L) ⊨ layerDisjCl ⟩ ∥₁ )
               × ( ∥ Σ[ s₁₀ ∈ S ] Σ[ κ₁₀ ∈ S ] Σ[ κ₂₀ ∈ S ] Σ[ E'c₀ ∈ S ]
                      Σ[ E₀ ∈ S ] Σ[ L₀ ∈ S ]
                      ( ⟨ pr (pr (# m) (# k₀)) (fst E₀) ∈ fst (lookup t γ) ⟩
                      × (fst E' ≡ fst E₀ ∪ fst L₀)
                      × ( (z : S) → ⟨ (z ∷ clEnvF m k₀ s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀) ⊨ layerDisjCl ⟩
                                  → ⟨ fst z ∈ fst L₀ ⟩ ) ) ∥₁ ) )
             → fst E' ≡ C.slice A (suc m) k₀
      finish s₁ κ₁ κ₂ E'c E L (eE , unEq , layerOut , rev) =
        extensionality (fst E') (C.slice A (suc m) k₀) (sub₁ , sub₂)
        where
        clEnv : S ^ (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
        clEnv = clEnvF m k₀ s₁ κ₁ κ₂ E'c E L
        module CLI = LayerLaws {suc (suc (suc (suc (suc (suc (suc (suc n)))))))}
          zero (sh8 t) (suc (suc (suc (suc (suc (suc (suc zero)))))))
          (suc (suc (suc (suc (suc (suc zero)))))) (sh8 a) clEnv
        qlm : fst (lookup (suc (suc (suc (suc (suc (suc (suc zero))))))) clEnv) ≡ # m
        qlm = numeralL-fst m
        qkk : fst (lookup (suc (suc (suc (suc (suc (suc zero)))))) clEnv) ≡ # k₀
        qkk = numeralL-fst k₀

        pinE : fst E ≡ C.slice A m k₀
        pinE = prefix-pins h b₀ qb qa m k₀ (cond-same m k₀ b₀ cond) E eE

        -- The layer-out direction, per disjunct: a member the clause-level
        -- disjunction describes is landed in the meta slice by the matching
        -- `slice-in` law, spending the pin at the shelf the disjunct reads.
        lInt : (z : S)
             → ⟨ (z ∷ clEnv) ⊨ InterDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
             → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lInt z hInt = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
          (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
            let pinW : fst W ≡ C.slice A m k₀
                pinW = prefix-pins h b₀ qb qa m k₀ (cond-same m k₀ b₀ cond) W eW
                hX' : ⟨ fst X ∈ C.slice A m k₀ ⟩
                hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hX
                hY' : ⟨ fst Y ∈ C.slice A m k₀ ⟩
                hY' = subst (λ w → ⟨ fst Y ∈ w ⟩) (pinW) hY
            in subst (λ w → ⟨ w ∈ C.slice A (suc m) k₀ ⟩) (sym e)
                 (C.slice-∩-in A hX' hY') })
          (CLI.InterDisj-out m k₀ z hInt qlm qkk)

        lUn : (z : S)
             → ⟨ (z ∷ clEnv) ⊨ UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
             → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lUn z hUn = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
          (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
            let pinW : fst W ≡ C.slice A m k₀
                pinW = prefix-pins h b₀ qb qa m k₀ (cond-same m k₀ b₀ cond) W eW
                hX' : ⟨ fst X ∈ C.slice A m k₀ ⟩
                hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hX
                hY' : ⟨ fst Y ∈ C.slice A m k₀ ⟩
                hY' = subst (λ w → ⟨ fst Y ∈ w ⟩) (pinW) hY
            in subst (λ w → ⟨ w ∈ C.slice A (suc m) k₀ ⟩) (sym e)
                 (C.slice-∪-in A hX' hY') })
          (CLI.UnionDisj-out m k₀ z hUn qlm qkk)

        lDi : (z : S)
             → ⟨ (z ∷ clEnv) ⊨ DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
             → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lDi z hDi = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
          (λ { (W , X , Y , (eW , (hX , (hY , e)))) →
            let pinW : fst W ≡ C.slice A m k₀
                pinW = prefix-pins h b₀ qb qa m k₀ (cond-same m k₀ b₀ cond) W eW
                hX' : ⟨ fst X ∈ C.slice A m k₀ ⟩
                hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hX
                hY' : ⟨ fst Y ∈ C.slice A m k₀ ⟩
                hY' = subst (λ w → ⟨ fst Y ∈ w ⟩) (pinW) hY
            in subst (λ w → ⟨ w ∈ C.slice A (suc m) k₀ ⟩) (sym e)
                 (C.slice-∖-in A hX' hY') })
          (CLI.DiffDisj-out m k₀ z hDi qlm qkk)

        -- A member of the arity numeral is a lower numeral, read back as a
        -- `Fin` index for the meta selection laws.
        finOf : (n₀ : ℕ) (x : V ℓ) → ⟨ x ∈ # n₀ ⟩
              → ∥ Σ[ i ∈ Fin n₀ ] (# (toℕ i) ≡ x) ∥₁
        finOf n₀ x hx = PT.rec squash₁
          (λ { (k'' , (h₀ , e₀)) →
            ∣ fromℕ' n₀ k'' h₀ , (cong #_ (toFromId' n₀ k'' h₀) ∙ sym e₀) ∣₁ })
          (∈#-elim n₀ x hx)

        lM : (z : S)
           → ⟨ (z ∷ clEnv) ⊨ SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
           → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lM z hM = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
          (λ { (W , X , i , j , (eW , (hX , (hi , (hj , e))))) →
            PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (i' , qi) →
              PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (j' , qj) →
                let pinW : fst W ≡ C.slice A m k₀
                    pinW = prefix-pins h b₀ qb qa m k₀ (cond-same m k₀ b₀ cond) W eW
                    hX' : ⟨ fst X ∈ C.slice A m k₀ ⟩
                    hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hX
                    e' : fst z ≡ selectMember (fst X) ⁅ # (toℕ i') ⁆s ⁅ # (toℕ j') ⁆s
                    e' = e ∙ cong₂ (λ a b → selectMember (fst X) ⁅ a ⁆s ⁅ b ⁆s)
                           (sym qi) (sym qj)
                in subst (λ w → ⟨ w ∈ C.slice A (suc m) k₀ ⟩) (sym e')
                     (C.slice-selM-in A i' j' hX') })
              (finOf k₀ (fst j) hj) })
            (finOf k₀ (fst i) hi) })
          (CLI.SelMDisj-out m k₀ z hM qlm qkk)

        lE : (z : S)
           → ⟨ (z ∷ clEnv) ⊨ SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
           → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lE z hE = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
          (λ { (W , X , i , j , (eW , (hX , (hi , (hj , e))))) →
            PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (i' , qi) →
              PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (j' , qj) →
                let pinW : fst W ≡ C.slice A m k₀
                    pinW = prefix-pins h b₀ qb qa m k₀ (cond-same m k₀ b₀ cond) W eW
                    hX' : ⟨ fst X ∈ C.slice A m k₀ ⟩
                    hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hX
                    e' : fst z ≡ selectEqual (fst X) ⁅ # (toℕ i') ⁆s ⁅ # (toℕ j') ⁆s
                    e' = e ∙ cong₂ (λ a b → selectEqual (fst X) ⁅ a ⁆s ⁅ b ⁆s)
                           (sym qi) (sym qj)
                in subst (λ w → ⟨ w ∈ C.slice A (suc m) k₀ ⟩) (sym e')
                     (C.slice-selE-in A i' j' hX') })
              (finOf k₀ (fst j) hj) })
            (finOf k₀ (fst i) hi) })
          (CLI.SelEDisj-out m k₀ z hE qlm qkk)

        lA : (z : S)
           → ⟨ (z ∷ clEnv) ⊨ AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lA z hA = subst (λ w → ⟨ w ∈ C.slice A (suc m) k₀ ⟩) (sym e')
          (C.slice-allTuples-in A)
          where
          e' : fst z ≡ allTuples A k₀
          e' = subst (λ w → fst z ≡ allTuples w k₀) qa
                 (CLI.AllTuplesDisj-out m k₀ z hA qkk)

        lS : (z : S)
           → ⟨ (z ∷ clEnv) ⊨ ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lS z hS = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
          (λ { (W , X , (eW , (hX , e))) →
            let pinW : fst W ≡ C.slice A m (suc k₀)
                pinW = prefix-pins h b₀ qb qa m (suc k₀) (cond-shift m k₀ b₀ cond) W eW
                hX' : ⟨ fst X ∈ C.slice A m (suc k₀) ⟩
                hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hX
            in subst (λ w → ⟨ w ∈ C.slice A (suc m) k₀ ⟩) (sym e)
                 (C.slice-shiftDown-in A hX') })
          (CLI.ShiftDisj-out m k₀ z hS qlm qkk)

        lV : (z : S)
           → ⟨ (z ∷ clEnv) ⊨ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
           → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lV z hV = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
          (λ { (W , X , (eW , (hX , (e , zq)))) →
            let pinW : fst W ≡ C.slice A m 1
                pinW = prefix-pins h b₀ qb qa m 1 (cond-values m k₀ b₀ zq cond) W eW
                hX' : ⟨ fst X ∈ C.slice A m 1 ⟩
                hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hX
                land : ⟨ fst z ∈ C.slice A (suc m) 0 ⟩
                land = subst (λ w → ⟨ w ∈ C.slice A (suc m) 0 ⟩) (sym e)
                         (C.slice-values-in A hX')
            in subst (λ k → ⟨ fst z ∈ C.slice A (suc m) k ⟩) (sym zq) land })
          (CLI.ValuesDisj-out m k₀ z hV qlm qkk)

        -- The seed lift: a singleton of a carrier member sits in the
        -- arity-zero shelf at every level.
        seedLift : (l : ℕ) (a0 : ⟪ A ⟫) → ⟨ ⁅ ⟪ A ⟫↪ a0 ⁆s ∈ C.slice A l 0 ⟩
        seedLift zero a0 = C.singletons-in A {X = A} {x = ⟪ A ⟫↪ a0}
          (∈∈ₛ {a = ⟪ A ⟫↪ a0} {b = A} .snd (∈ₛ⟪ A ⟫↪ a0))
        seedLift (suc l) a0 = C.slice-old A (seedLift l a0)
        lX : (z : S)
           → ⟨ (z ∷ clEnv) ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
           → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
        lX z hX = PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (s , w₁) →
          PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (κ , w₂) →
            PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (W , w₃) →
              PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (X , w₄) →
                PT.rec (snd (fst z ∈ C.slice A (suc m) k₀)) (λ { (y , body) →
                let hSuc = body .fst
                    hPos = body .snd .fst
                    hPr = body .snd .snd .fst
                    hApp = body .snd .snd .snd .fst
                    hXw = body .snd .snd .snd .snd .fst
                    hy = body .snd .snd .snd .snd .snd .fst
                    hEx = body .snd .snd .snd .snd .snd .snd
                    envX = y ∷ X ∷ W ∷ κ ∷ s ∷ z ∷ clEnv
                    es : sucV (fst s) ≡ # k₀
                    es = sym (subst ⟨_⟩ (sucAtL-adequate (suc (suc (suc (suc zero))))
                            (sh5 (suc (suc (suc (suc (suc (suc (suc zero)))))))) envX) hSuc) ∙ qkk
                    hPr' : fst κ ≡ pr (fst (numeralL m)) (fst s)
                    hPr' = subst ⟨_⟩ (prAtL-adequate (suc (suc (suc zero)))
                             (sh5 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
                             (suc (suc (suc (suc zero)))) envX) hPr
                    hApp' : ⟨ pr (fst κ) (fst W) ∈ fst (lookup t γ) ⟩
                    hApp' = subst ⟨_⟩ (appAt-adequate (sh5 (sh9 t))
                             (suc (suc (suc zero))) (suc (suc zero)) envX) hApp
                    eW : ⟨ pr (pr (# m) (fst s)) (fst W) ∈ fst (lookup t γ) ⟩
                    eW = subst (λ q → ⟨ pr q (fst W) ∈ fst (lookup t γ) ⟩)
                           (hPr' ∙ cong₂ pr (numeralL-fst m) refl) hApp'
                    e : fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
                    e = extendFamilyAt-out (sh5 zero) (suc zero) zero envX hEx
                in PT.rec (snd (fst z ∈ C.slice A (suc m) k₀))
                     (goK s W X y es hPos eW hXw hy e)
                     (∈#-elim k₀ (fst s)
                       (subst (λ q → ⟨ fst s ∈ q ⟩) es (self∈sucV (fst s)))) })
                  w₄ }) w₃ }) w₂ }) w₁ }) hX
          where
          goK : (s W X y : S) → sucV (fst s) ≡ # k₀
              → ((fst s ≡ fst (numeralL 0)) → Empty.⊥)
              → ⟨ pr (pr (# m) (fst s)) (fst W) ∈ fst (lookup t γ) ⟩
              → ⟨ fst X ∈ fst W ⟩ → ⟨ fst y ∈ fst (lookup a γ) ⟩
              → fst z ≡ extendFamily (fst X) ⁅ fst y ⁆s
              → Σ[ k'' ∈ ℕ ] ((k'' < k₀) × (fst s ≡ # k''))
              → ⟨ fst z ∈ C.slice A (suc m) k₀ ⟩
          goK s W X y es hPos eW hXw hy e (zero , (h₀ , e₀)) =
            Empty.rec (hPos (subst (λ w → fst s ≡ w) (sym (numeralL-fst 0)) e₀))
          goK s W X y es hPos eW hXw hy e (suc k''' , (h₀ , e₀)) =
            let eW' : ⟨ pr (pr (# m) (# (suc k'''))) (fst W) ∈ fst (lookup t γ) ⟩
                eW' = subst (λ w → ⟨ pr (pr (# m) w) (fst W) ∈ fst (lookup t γ) ⟩) e₀ eW
                pinW : fst W ≡ C.slice A m (suc k''')
                pinW = prefix-pins h b₀ qb qa m (suc k''') (cond-ext m (suc k''') k₀ b₀ h₀ cond) W eW'
                hX' : ⟨ fst X ∈ C.slice A m (suc k''') ⟩
                hX' = subst (λ w → ⟨ fst X ∈ w ⟩) (pinW) hXw
                hy' : ⟨ fst y ∈ A ⟩
                hy' = subst (λ w → ⟨ fst y ∈ w ⟩) qa hy
                fA : Σ[ a0 ∈ ⟪ A ⟫ ] (⟪ A ⟫↪ a0 ≡ fst y)
                fA = ∈-asFiber {a = fst y} {b = A} hy'
                ha : ⟨ ⁅ ⟪ A ⟫↪ (fA .fst) ⁆s ∈ C.slice A m 0 ⟩
                ha = seedLift m (fA .fst)
                img : ⟨ extendFamily (fst X) ⁅ ⟪ A ⟫↪ (fA .fst) ⁆s
                         ∈ C.slice A (suc m) (suc (suc k''')) ⟩
                img = C.slice-extendFamily-in A (fA .fst) hX' ha
                k₀≡ : suc (suc k''') ≡ k₀
                k₀≡ = #-inj′ (refl ∙ sym (cong sucV e₀) ∙ es)
                eq' : fst z ≡ extendFamily (fst X) ⁅ ⟪ A ⟫↪ (fA .fst) ⁆s
                eq' = e ∙ cong (λ w → extendFamily (fst X) ⁅ w ⁆s) (sym (fA .snd))
            in subst (λ w → ⟨ fst z ∈ C.slice A (suc m) w ⟩) k₀≡
                 (subst (λ w → ⟨ w ∈ C.slice A (suc m) (suc (suc k''')) ⟩) (sym eq') img)

        -- The member direction of the layer identification: every member of
        -- the entry at the successor key is in the meta slice, either as an
        -- old member of the pinned previous entry or as one of the layer
        -- disjunction's images landed by the landers above.
        sub₁ : ⟨ fst E' ⊆ C.slice A (suc m) k₀ ⟩
        sub₁ z z∈ₛE' = ∈∈ₛ {a = z} {b = C.slice A (suc m) k₀} .fst
          (PT.rec (snd (z ∈ C.slice A (suc m) k₀)) go₁
            (∪-out {X = fst E} {Y = fst L} {x = z}
              (subst (λ w → ⟨ z ∈ w ⟩) unEq (∈∈ₛ {a = z} {b = fst E'} .snd z∈ₛE'))))
          where
          go₁ : ⟨ z ∈ fst E ⟩ ⊎ ⟨ z ∈ fst L ⟩ → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
          go₁ (inl hzE) = C.slice-old A
            (subst (λ w → ⟨ z ∈ w ⟩) pinE hzE)
          go₁ (inr hzL) = PT.rec (snd (z ∈ C.slice A (suc m) k₀)) go₂
            (layerOut (z , lz) hzL)
            where
            lz : ⟨ isL z ⟩
            lz = isL-trans {x = fst L} {y = z} hzL (L .snd)
            zS : S
            zS = (z , lz)
            dispatch1 : ⟨ ((zS ∷ clEnv) ⊨
                           ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                             ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) )) ⟩
                       → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch1 h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hS) → lS zS hS ; (inr hV) → lV zS hV }) h
            dispatch2 : ⟨ ((z , lz) ∷ clEnv)
                           ⊨ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                             ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                               ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ⟩
                       → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch2 h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hX) → lX (z , lz) hX ; (inr hRest) → dispatch1 hRest }) h
            dispatch3 : ⟨ ((z , lz) ∷ clEnv)
                           ⊨ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                             ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                               ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                 ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ⟩
                       → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch3 h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hA) → lA (z , lz) hA ; (inr hRest) → dispatch2 hRest }) h
            dispatch4 : ⟨ ((z , lz) ∷ clEnv)
                           ⊨ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                             ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                               ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                 ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                   ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ⟩
                       → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch4 h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hE) → lE (z , lz) hE ; (inr hRest) → dispatch3 hRest }) h
            dispatch5 : ⟨ ((z , lz) ∷ clEnv)
                           ⊨ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                             ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                               ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                 ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                   ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                     ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ) ⟩
                       → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch5 h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hM) → lM (z , lz) hM ; (inr hRest) → dispatch4 hRest }) h
            dispatch6 : ⟨ ((z , lz) ∷ clEnv)
                           ⊨ ( DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                             ∨̇ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                               ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                 ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                   ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                     ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                       ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ) ) ⟩
                       → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch6 h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hDi) → lDi (z , lz) hDi ; (inr hRest) → dispatch5 hRest }) h
            dispatch7 : ⟨ ((z , lz) ∷ clEnv)
                           ⊨ ( UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                             ∨̇ ( DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                               ∨̇ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                 ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                   ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                     ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                       ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                         ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ) ) ) ⟩
                       → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch7 h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hUn) → lUn (z , lz) hUn ; (inr hRest) → dispatch6 hRest }) h
            dispatch : ⟨ ((z , lz) ∷ clEnv)
                          ⊨ ( InterDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                            ∨̇ ( UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                              ∨̇ ( DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                ∨̇ ( SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                  ∨̇ ( SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                    ∨̇ ( AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                      ∨̇ ( ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a)
                                        ∨̇ ( ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                                          ∨̇ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ) ) ) ) ) ) ) ) ⟩
                      → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            dispatch h = PT.rec (snd (z ∈ C.slice A (suc m) k₀))
              (λ { (inl hInt) → lInt (z , lz) hInt
                 ; (inr hRest) → dispatch7 hRest }) h
            go₂ : ⟨ z ∈ fst E ⟩ ⊎ ⟨ ((z , lz) ∷ clEnv) ⊨ LayerDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                → ⟨ z ∈ C.slice A (suc m) k₀ ⟩
            go₂ (inl hzE) = C.slice-old A
              (subst (λ w → ⟨ z ∈ w ⟩) pinE hzE)
            go₂ (inr hDisj) = dispatch hDisj


        lA' : ⟨ isL A ⟩
        lA' = subst (λ w → ⟨ isL w ⟩) qa (lookup a γ .snd)

        membW : (W : S) (k' : ℕ) → fst W ≡ C.slice A m k'
              → (i : ⟪ C.slice A m k' ⟫) → S
        membW W k' qW i = (⟪ C.slice A m k' ⟫↪ i , lWX)
          where
          hX : ⟨ ⟪ C.slice A m k' ⟫↪ i ∈ fst W ⟩
          hX = subst (λ w → ⟨ ⟪ C.slice A m k' ⟫↪ i ∈ w ⟩) (sym qW)
            (∈∈ₛ {a = ⟪ C.slice A m k' ⟫↪ i} {b = C.slice A m k'} .snd
              (∈ₛ⟪ C.slice A m k' ⟫↪ i))
          lWX : ⟨ isL (⟪ C.slice A m k' ⟫↪ i) ⟩
          lWX = isL-trans {x = fst W} {y = ⟪ C.slice A m k' ⟫↪ i} hX (W .snd)

        membW∈ : (W : S) (k' : ℕ) (qW : fst W ≡ C.slice A m k')
               → (i : ⟪ C.slice A m k' ⟫) → ⟨ fst (membW W k' qW i) ∈ fst W ⟩
        membW∈ W k' qW i = subst (λ w → ⟨ ⟪ C.slice A m k' ⟫↪ i ∈ w ⟩) (sym qW)
          (∈∈ₛ {a = ⟪ C.slice A m k' ⟫↪ i} {b = C.slice A m k'} .snd
            (∈ₛ⟪ C.slice A m k' ⟫↪ i))

        membA : ⟪ A ⟫ → S
        membA aa = (⟪ A ⟫↪ aa , lY)
          where
          hy : ⟨ ⟪ A ⟫↪ aa ∈ A ⟩
          hy = ∈∈ₛ {a = ⟪ A ⟫↪ aa} {b = A} .snd (∈ₛ⟪ A ⟫↪ aa)
          lY : ⟨ isL (⟪ A ⟫↪ aa) ⟩
          lY = isL-trans {x = A} {y = ⟪ A ⟫↪ aa} hy lA'

        membA∈ : (aa : ⟪ A ⟫) → ⟨ fst (membA aa) ∈ A ⟩
        membA∈ aa = ∈∈ₛ {a = ⟪ A ⟫↪ aa} {b = A} .snd (∈ₛ⟪ A ⟫↪ aa)

        idxS : Fin k₀ → S
        idxS i = (# (toℕ i) , numL (toℕ i))

        idx∈ : (i : Fin k₀) → ⟨ fst (idxS i) ∈ # k₀ ⟩
        idx∈ i = #mono (toℕ i) k₀ (toℕ<n i)

        sub₂ : ⟨ C.slice A (suc m) k₀ ⊆ fst E' ⟩
        sub₂ z hz = PT.rec (snd (z ∈ₛ fst E')) go-slice-out
          (C.slice-out A {n = m} {k = k₀} z (∈∈ₛ {a = z} {b = C.slice A (suc m) k₀} .snd hz))
          where
          go-slice-out : ⟨ z ∈ C.slice A m k₀ ⟩
                       ⊎ (Σ[ t ∈ C.StepTag A k₀ ] Σ[ p ∈ C.StepPayload A m k₀ t ]
                            (C.stepImage A {m} {k₀} t p ≡ z))
                       → ⟨ z ∈ₛ fst E' ⟩
          go-slice-out (inl hzOld) = ∈∈ₛ {a = z} {b = fst E'} .fst
            (subst (λ w → ⟨ z ∈ w ⟩) (sym unEq)
              (∪-left {X = fst E} {Y = fst L} {x = z}
                (subst (λ w → ⟨ z ∈ w ⟩) (sym pinE) hzOld)))
          go-slice-out (inr (tg , p , eq)) = PT.rec (snd (z ∈ₛ fst E')) unpack-rev rev
            where
            finish-rev : (s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀ : S)
                       → ( ⟨ pr (pr (# m) (# k₀)) (fst E₀) ∈ fst (lookup t γ) ⟩
                         × (fst E' ≡ fst E₀ ∪ fst L₀)
                         × ( (z' : S) → ⟨ (z' ∷ clEnvF m k₀ s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀) ⊨ layerDisjCl ⟩
                                     → ⟨ fst z' ∈ fst L₀ ⟩ ) )
                       → ⟨ z ∈ₛ fst E' ⟩
            finish-rev s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀ (eE₀ , (unEq₀ , layerIn)) =
              PT.rec (snd (z ∈ₛ fst E')) finish-img (step→layer tg p)
              where
              clEnv₀ : S ^ (suc (suc (suc (suc (suc (suc (suc (suc n))))))))
              clEnv₀ = clEnvF m k₀ s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀
              module CLI₀ = LayerLaws {suc (suc (suc (suc (suc (suc (suc (suc n)))))))}
                zero (sh8 t) (suc (suc (suc (suc (suc (suc (suc zero)))))))
                (suc (suc (suc (suc (suc (suc zero)))))) (sh8 a) clEnv₀
              pinE₀ : fst E₀ ≡ C.slice A m k₀
              pinE₀ = prefix-pins h b₀ qb qa m k₀ (cond-same m k₀ b₀ cond) E₀ eE₀
              entryAt : (k' : ℕ) → k' ≤ suc b₀ → m + suc k' < b₀
                      → ∥ Σ[ W ∈ S ] ( ⟨ pr (pr (# m) (# k')) (fst W) ∈ fst (lookup t γ) ⟩
                                     × (fst W ≡ C.slice A m k') ) ∥₁
              entryAt k' k'≤sb c = PT.rec squash₁
                (λ { (W , eW) → ∣ W , (eW , prefix-pins h b₀ qb qa m k' c W eW) ∣₁ })
                (domadeq-out h b₀ qb m k' m≤b₀ k'≤sb)
              step→layer : (t' : C.StepTag A k₀) (p' : C.StepPayload A m k₀ t')
                         → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {m} {k₀} t' p') ⟩ ]
                               ⟨ ((C.stepImage A {m} {k₀} t' p' , lZ) ∷ clEnv₀) ⊨ layerDisjCl ⟩ ∥₁
              step→layer C.tagInter (m₁ , q₁) = ∣ lZ , ∣ inl sat ∣₁ ∣₁
                where
                X = membW E₀ k₀ pinE₀ m₁
                Y = membW E₀ k₀ pinE₀ q₁
                lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagInter (m₁ , q₁)) ⟩
                lZ = capL (X .snd) (Y .snd)
                sat : ⟨ ((C.stepImage A {m} {k₀} C.tagInter (m₁ , q₁) , lZ) ∷ clEnv₀)
                          ⊨ InterDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                sat = CLI₀.InterDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagInter (m₁ , q₁) , lZ)
                        E₀ eE₀ X Y (membW∈ E₀ k₀ pinE₀ m₁) (membW∈ E₀ k₀ pinE₀ q₁)
                        refl qlm qkk
              step→layer C.tagUnion (m₁ , q₁) = ∣ lZ , ∣ inr (∣ inl sat ∣₁) ∣₁ ∣₁
                where
                X = membW E₀ k₀ pinE₀ m₁
                Y = membW E₀ k₀ pinE₀ q₁
                lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagUnion (m₁ , q₁)) ⟩
                lZ = cupL (X .snd) (Y .snd)
                sat : ⟨ ((C.stepImage A {m} {k₀} C.tagUnion (m₁ , q₁) , lZ) ∷ clEnv₀)
                          ⊨ UnionDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                sat = CLI₀.UnionDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagUnion (m₁ , q₁) , lZ)
                        E₀ eE₀ X Y (membW∈ E₀ k₀ pinE₀ m₁) (membW∈ E₀ k₀ pinE₀ q₁)
                        refl qlm qkk
              step→layer C.tagDiff (m₁ , q₁) = ∣ lZ , ∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁ ∣₁
                where
                X = membW E₀ k₀ pinE₀ m₁
                Y = membW E₀ k₀ pinE₀ q₁
                lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagDiff (m₁ , q₁)) ⟩
                lZ = diffL (X .snd) (Y .snd)
                sat : ⟨ ((C.stepImage A {m} {k₀} C.tagDiff (m₁ , q₁) , lZ) ∷ clEnv₀)
                          ⊨ DiffDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                sat = CLI₀.DiffDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagDiff (m₁ , q₁) , lZ)
                        E₀ eE₀ X Y (membW∈ E₀ k₀ pinE₀ m₁) (membW∈ E₀ k₀ pinE₀ q₁)
                        refl qlm qkk
              step→layer C.tagSelM (m₁ , i , j) = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
                where
                X = membW E₀ k₀ pinE₀ m₁
                lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagSelM (m₁ , i , j)) ⟩
                lZ = selectMemberL {X = fst X} {Ka = ⁅ # (toℕ i) ⁆s} {Kb = ⁅ # (toℕ j) ⁆s}
                       (X .snd) (sglL (idxS i .snd)) (sglL (idxS j .snd))
                sat : ⟨ ((C.stepImage A {m} {k₀} C.tagSelM (m₁ , i , j) , lZ) ∷ clEnv₀)
                          ⊨ SelMDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                sat = CLI₀.SelMDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagSelM (m₁ , i , j) , lZ)
                        E₀ eE₀ X (idxS i) (idxS j) (membW∈ E₀ k₀ pinE₀ m₁)
                        (idx∈ i) (idx∈ j) refl qlm qkk
              step→layer C.tagSelE (m₁ , i , j) = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
                where
                X = membW E₀ k₀ pinE₀ m₁
                lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagSelE (m₁ , i , j)) ⟩
                lZ = selectEqualL {X = fst X} {Ka = ⁅ # (toℕ i) ⁆s} {Kb = ⁅ # (toℕ j) ⁆s}
                       (X .snd) (sglL (idxS i .snd)) (sglL (idxS j .snd))
                sat : ⟨ ((C.stepImage A {m} {k₀} C.tagSelE (m₁ , i , j) , lZ) ∷ clEnv₀)
                          ⊨ SelEDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                sat = CLI₀.SelEDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagSelE (m₁ , i , j) , lZ)
                        E₀ eE₀ X (idxS i) (idxS j) (membW∈ E₀ k₀ pinE₀ m₁)
                        (idx∈ i) (idx∈ j) refl qlm qkk
              step→layer C.tagAll tt* = ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
                where
                lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagAll tt*) ⟩
                lZ = allTuplesL A lA' k₀
                sat : ⟨ ((C.stepImage A {m} {k₀} C.tagAll tt* , lZ) ∷ clEnv₀)
                          ⊨ AllTuplesDisjAt zero (sh9 a) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                sat = CLI₀.AllTuplesDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagAll tt* , lZ)
                        (cong (λ w → allTuples w k₀) (sym qa)) qkk
              step→layer (C.tagExt {k = k'}) (m₁ , aa) =
                PT.rec squash₁ build
                  (entryAt (suc k') sk'≤sb condExt)
                where
                sk'<k₀ : suc k' < k₀
                sk'<k₀ = ≤-refl
                sk'≤sb : suc k' ≤ suc b₀
                sk'≤sb = ≤-trans (≤-trans ≤-sucℕ sk'<k₀)
                           (≤-trans (cond-k≤b m k₀ b₀ cond) ≤-sucℕ)
                condExt : m + suc (suc k') < b₀
                condExt = cond-ext m (suc k') k₀ b₀ sk'<k₀ cond
                build : Σ[ W ∈ S ] ( ⟨ pr (pr (# m) (# (suc k'))) (fst W) ∈ fst (lookup t γ) ⟩
                                  × (fst W ≡ C.slice A m (suc k')) )
                      → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {m} {k₀} (C.tagExt {k = k'}) (m₁ , aa)) ⟩ ]
                            ⟨ ((C.stepImage A {m} {k₀} (C.tagExt {k = k'}) (m₁ , aa) , lZ) ∷ clEnv₀) ⊨ layerDisjCl ⟩ ∥₁
                build (W , eW , pinW) =
                  ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
                  where
                  X = membW W (suc k') pinW m₁
                  Y = membA aa
                  lZ : ⟨ isL (C.stepImage A {m} {k₀} (C.tagExt {k = k'}) (m₁ , aa)) ⟩
                  lZ = extendFamilyL {X = fst X} {Y = ⁅ fst Y ⁆s} (X .snd) (sglL (Y .snd))
                  s₀ : S
                  s₀ = numeralL (suc k')
                  ks : fst (lookup (suc (suc (suc (suc (suc (suc zero)))))) clEnv₀) ≡ sucV (fst s₀)
                  ks = numeralL-fst (suc (suc k'))
                    ∙ sym (cong sucV (numeralL-fst (suc k')))
                  hPos : (fst s₀ ≡ fst (numeralL 0)) → Empty.⊥
                  hPos h = snotz (#-inj′ (sym (numeralL-fst (suc k')) ∙ h ∙ numeralL-fst 0))
                  eW' : ⟨ pr (pr (# m) (fst s₀)) (fst W) ∈ fst (lookup t γ) ⟩
                  eW' = subst (λ w → ⟨ pr (pr (# m) w) (fst W) ∈ fst (lookup t γ) ⟩)
                          (sym (numeralL-fst (suc k'))) eW
                  sat : ⟨ ((C.stepImage A {m} {k₀} (C.tagExt {k = k'}) (m₁ , aa) , lZ) ∷ clEnv₀)
                            ⊨ ExtDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (sh9 a) ⟩
                  sat = CLI₀.ExtDisj-in m k₀ (C.stepImage A {m} {k₀} (C.tagExt {k = k'}) (m₁ , aa) , lZ)
                          s₀ ks hPos W eW' X Y (membW∈ W (suc k') pinW m₁)
                          (subst (λ w → ⟨ fst (membA aa) ∈ w ⟩) (sym qa) (membA∈ aa))
                          refl qlm qkk
              step→layer C.tagShift m₁ =
                PT.rec squash₁ build
                  (entryAt (suc k₀) sk₀≤sb condShift)
                where
                sk₀≤sb : suc k₀ ≤ suc b₀
                sk₀≤sb = suc-≤-suc k₀≤b₀
                condShift : m + suc (suc k₀) < b₀
                condShift = cond-shift m k₀ b₀ cond
                build : Σ[ W ∈ S ] ( ⟨ pr (pr (# m) (# (suc k₀))) (fst W) ∈ fst (lookup t γ) ⟩
                                  × (fst W ≡ C.slice A m (suc k₀)) )
                      → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {m} {k₀} C.tagShift m₁) ⟩ ]
                            ⟨ ((C.stepImage A {m} {k₀} C.tagShift m₁ , lZ) ∷ clEnv₀) ⊨ layerDisjCl ⟩ ∥₁
                build (W , eW , pinW) =
                  ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inl sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
                  where
                  X = membW W (suc k₀) pinW m₁
                  lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagShift m₁) ⟩
                  lZ = shiftDownL {X = fst X} (X .snd)
                  sat : ⟨ ((C.stepImage A {m} {k₀} C.tagShift m₁ , lZ) ∷ clEnv₀)
                            ⊨ ShiftDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                  sat = CLI₀.ShiftDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagShift m₁ , lZ)
                          W eW X (membW∈ W (suc k₀) pinW m₁) refl qlm qkk
              step→layer C.tagValues m₁ =
                PT.rec squash₁ build
                  (entryAt 1 1≤sb condV)
                where
                1≤sb : 1 ≤ suc b₀
                1≤sb = suc-≤-suc (b₀ , +-zero b₀)
                condV : m + suc 1 < b₀
                condV = cond-values m k₀ b₀ refl cond
                build : Σ[ W ∈ S ] ( ⟨ pr (pr (# m) (# 1)) (fst W) ∈ fst (lookup t γ) ⟩
                                   × (fst W ≡ C.slice A m 1) )
                      → ∥ Σ[ lZ ∈ ⟨ isL (C.stepImage A {m} {k₀} C.tagValues m₁) ⟩ ]
                            ⟨ ((C.stepImage A {m} {k₀} C.tagValues m₁ , lZ) ∷ clEnv₀) ⊨ layerDisjCl ⟩ ∥₁
                build (W , eW , pinW) =
                  ∣ lZ , ∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr (∣ inr sat ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁ ∣₁
                  where
                  X = membW W 1 pinW m₁
                  lZ : ⟨ isL (C.stepImage A {m} {k₀} C.tagValues m₁) ⟩
                  lZ = valuesL {X = fst X} (X .snd)
                  sat : ⟨ ((C.stepImage A {m} {k₀} C.tagValues m₁ , lZ) ∷ clEnv₀)
                            ⊨ ValuesDisjAt zero (sh9 t) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ⟩
                  sat = CLI₀.ValuesDisj-in m k₀ (C.stepImage A {m} {k₀} C.tagValues m₁ , lZ)
                          W eW X (membW∈ W 1 pinW m₁) refl qlm qkk refl
              finish-img : Σ[ lZ ∈ ⟨ isL (C.stepImage A {m} {k₀} tg p) ⟩ ]
                             ⟨ ((C.stepImage A {m} {k₀} tg p , lZ) ∷ clEnv₀) ⊨ layerDisjCl ⟩
                         → ⟨ z ∈ₛ fst E' ⟩
              finish-img (lZ , sat) = ∈∈ₛ {a = z} {b = fst E'} .fst
                (subst (λ w → ⟨ z ∈ w ⟩) (sym unEq₀)
                  (∪-right {X = fst E₀} {Y = fst L₀} {x = z}
                     (subst (λ w → ⟨ w ∈ fst L₀ ⟩) eq
                       (layerIn (C.stepImage A {m} {k₀} tg p , lZ) sat))))
            unpack-rev : Σ[ s₁₀ ∈ S ] Σ[ κ₁₀ ∈ S ] Σ[ κ₂₀ ∈ S ] Σ[ E'c₀ ∈ S ]
                           Σ[ E₀ ∈ S ] Σ[ L₀ ∈ S ]
                           ( ⟨ pr (pr (# m) (# k₀)) (fst E₀) ∈ fst (lookup t γ) ⟩
                           × (fst E' ≡ fst E₀ ∪ fst L₀)
                           × ( (z' : S) → ⟨ (z' ∷ clEnvF m k₀ s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀) ⊨ layerDisjCl ⟩
                                       → ⟨ fst z' ∈ fst L₀ ⟩ ) )
                         → ⟨ z ∈ₛ fst E' ⟩
            unpack-rev (s₁₀ , (κ₁₀ , (κ₂₀ , (E'c₀ , (E₀ , (L₀ , w₆)))))) =
              finish-rev s₁₀ κ₁₀ κ₂₀ E'c₀ E₀ L₀ w₆
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
Two disjuncts carry guards, and both guards exist because the meta step's
images exist only on the shelves the clauses read. The values image exists only
on the value shelf: `tagValues : StepTag 0`, and the meta `stepImage` for it
reads the arity-one shelf and writes the arity-zero shelf, so the values
disjunct pins the layer's arity slot to the zero numeral. At arity zero the
guard is satisfiable and the disjunct reads shelf one exactly as the meta
`tagValues` does; at positive arities the guard is refuted by numeral
injectivity, so the over-description disappears, refuted rather than
untypeable, which is what the dispatch chains need. The extension disjunct is
guarded the same way on the positive side: the meta `tagExt` draws its first
argument from a positive-arity slice only
(`StepPayload n (suc (suc k)) tagExt = Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] ⟪ A ⟫`),
so the source slot is pinned away from the zero numeral. At layer arity one
the guard is refuted (the meta step has no extension image there), and at every
arity from two on the disjunct reads the shelf one arity down, exactly as the
meta step does. The other seven disjuncts match the meta step at every arity
already: the binary and selection clauses stay on the same shelf, the tuple
family comes from the numeral alone (arity zero included), and the shift reads
the shelf one arity up.
<!--zh-->
两条析取支带卫式，两条卫式都因为元步的像只存在于子句所读的架位而存在。取值像只存在于取值片：`tagValues : StepTag 0`，元 `stepImage` 对它读第一元数片、写第零元数片，故取值析取支把层的元数槽钉到数码零。元数为零时卫式可满足，析取支恰如元 `tagValues` 那样读第一片；正元数处卫式被数码单射所驳斥，过描述随之消失，是被驳斥而非不可类型化，这正是分发链所需。族扩张析取支以同样方式在正侧加卫：元 `tagExt` 只从正元数片取首实参 (`StepPayload n (suc (suc k)) tagExt = Σ[ m ∈ ⟪ slice n (suc k) ⟫ ] ⟪ A ⟫`)，故源槽被钉离数码零。层元数一时卫式被驳斥 (元步在那里没有扩张像)，从元数二起每个元数上析取支都读下移一片的架位，恰如元步。其余七条析取支在每个元数上已经与元步吻合：二元与选择子句留同架，元组族只从数码来 (含元数零)，移位读上移一片的架位。
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

<!--en-->
## The pinning theorem

Any table satisfying `PrefixAt` at the bound `b` is pinned into the meta
slices: `prefix-pins` shows, by induction on the level numeral, that the entry
at every key `(n₀, k₀)` with the combined condition `n₀ + suc k₀ < b₀` (level
plus arity below the bound) equals `slice A n₀ k₀`. The condition is exactly
what the recursion needs: at the successor key the layer's disjuncts shop on
the same-arity shelf, the shelf one arity up (the shift), the shelf one arity
down (the extension), and the arity-one shelf (the values, at arity zero
only), and the level-plus-arity bound stays constant down each of those
shelves, which is why the statement quantifies all keys at once rather than
recursing per column. The two per-member directions are the successor clause's
own witnesses, read at the clause's binder numerals: the out-direction lands
every layer member in the meta slice by the matching `slice-in` law, spending
the pin at the shelf the disjunct reads, and the in-direction rebuilds each
tagged step image with its payload into the clause-level layer disjunction,
spending the pins at the shelves the payload draws from, then returns it to the
entry through the reverse clause witness. The step's arity-one key is pinned
the same way, and the values-cut of that pinned shelf is the definable
powerset (the closure chapter's cut theorem), which is the step the next
sections describe.
<!--zh-->
## 钉住定理

任何满足界 `b` 处 `PrefixAt` 的表都被钉进元层诸片：`prefix-pins` 对层级数码归纳，证明满足组合条件 `n₀ + suc k₀ < b₀` (层级加元数在界下) 的每个键 `(n₀, k₀)` 处条目等于 `slice A n₀ k₀`。条件恰为递归所需：后继键处层的各析取支在同元数架、上移一架 (移位)、下移一架 (族扩张) 与第一元数片 (取值，仅元数零) 上购物，而层级加元数之界沿每一条这类架位保持不变，这正是陈述一次量化全部键而非逐列递归的原因。两条逐成员方向就是后继子句自己的见证，在子句的绑定数码处读出：出向方向用相配的 `slice-in` 律把每个层成员落到元片，花掉析取支所读架位处的钉，入向方向把每个带载荷的标签步像重建成子句级层析取，花掉载荷所取架位处的钉，再经反向子句见证送回条目。步的元数一键以同一方式被钉，而该钉住片上的取值切口正是可定义幂集 (闭包章的切定理)，即下文诸节所描述的步。
<!--/-->

<!--en-->
## Recap

The prefix table is now determined from the inside. The layer disjunction
matches the meta step exactly at every arity: the values image lives only on
the value shelf and its guard pins the arity-zero numeral, the extension
draws only from positive shelves and its guard pins the source away from zero,
and the remaining disjuncts already match shelf by shelf. The pinning theorem
then reads any table satisfying `PrefixAt` back into the meta slices at every
key below the combined bound, by the successor clause's own two per-member
directions. What remains is the fill, which certifies the table built from the
slices themselves, and the step, which cuts the pinned arity-one entry into
the definable powerset.
<!--zh-->
## 小结

前缀表现在从内部被决定。层析取在每个元数上精确匹配元步：取值像只存在于取值片，其卫式钉住数码零；族扩张只从正片取实参，其卫式把源钉离零；其余析取支已经一架一架吻合。钉住定理随后把任何满足 `PrefixAt` 的表在组合界下的每个键处读回元片，走后继子句自己的两条逐成员方向。剩下的是填充，它使由诸片本身搭起的表受证，以及步，它把被钉住的元数一条目裁进可定义幂集。
<!--/-->
