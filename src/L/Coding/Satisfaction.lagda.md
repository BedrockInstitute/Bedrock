<!--en-->
# Satisfaction by recursion on formulas

Given a set B in L and a formula, we construct the set of environments over B that satisfy that formula. Recursion on the formula reduces this construction to separation from the set of environments. The resulting membership equations describe the ten formula constructors and will identify the values recorded in a satisfaction table.
<!--zh-->
# 沿公式递归构造满足关系

给定 L 中的集合 B 和一条公式，我们构造 B 上满足该公式的环境所组成的集合。沿公式递归，将这项构造化为在环境集上作分离。所得的隶属关系等式分别描述十个公式构造子，并将用来确定满足关系表记录的取值。
<!--ja-->
# 論理式上の再帰による充足関係

L の集合 B と論理式を与え、その論理式を充足する B 上の環境の集合を構成します。論理式上の再帰により、この構成を環境の集合からの分出に帰着させます。得られる所属関係の等式は十の論理式構成子に対応し、充足関係表に記録する値を特徴付けます。
<!--/-->

<!--en-->
Nothing here is internal. The recursion is on a formula Agda can see, so each
step may name the sets the previous steps produced as constants, and the object
language never has to quantify over a code. That is what makes every step a
single separation off the ambient set, and what makes the ten clauses of the
internal recursion, when they come, into identities rather than definitions.

The atoms are shorter here than in the internal clauses for the same reason. A
term of the meta-language is a variable or a constant and the recursion knows
which, so the reader for its value is one case rather than two.
<!--zh-->
此处没有任何内部的东西。递归沿一条 Agda 看得见的公式进行，故每一步都可以把前几步产出的集合以常元点名，而对象语言始终不必对码作量化。正是这一点使每一步只是「在周遭集合上作一次分离」，也正是这一点使内部递归那十条子句到来时成为**等式**而非定义。

出于同样理由，此处的原子比内部子句短。元语言的一个词项要么是变元、要么是常元，而递归知道是哪个，故读它取值的读式只有一种情形，不是两种。
<!--/-->


```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Coding.Satisfaction {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Coding.Model {ℓ} using ( appAt; appAt-adequate )
open import L.Coding.Expressions {ℓ} using ( consAtL; numL )
open import L.Coding.EnvironmentSet {ℓ} lem using ( envSet )

open import Cubical.Data.FinData using ( toℕ )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )
```


<!--en-->
## Evaluating variables and constants

A variable obtains its value from the environment at its index; a constant already names its value. We express these two cases by an object-language formula, which will supply the term values in the atomic clauses.
<!--zh-->
## 变元与常元的求值

变元从环境中取得其索引处的值，常元则直接指称自己的值。我们用对象语言公式表达这两种情形，为原子子句提供词项的取值。
<!--ja-->
## 変数と定数の評価

変数の値はその添字に対応する環境の成分であり、定数は自らの値を指定しています。この二つの場合を対象言語の論理式で表し、原子式の節で使う項の値を与えます。
<!--/-->


```agda
private
  nn : ℕ → S
  nn k = # k , numL k

tmIs : ∀ {n m} → Term S n → Fin m → Fin m → Formula S m
tmIs (var i) v e =
  ∃̇ ((var zero ≐ con (nn (toℕ i))) ∧̇ appAt (suc e) zero (suc v))
tmIs (con c) v e = var v ≐ con c

tmIs-var-in : ∀ {n m} (i : Fin n) (γ : S ^ m) (v e : Fin m)
            → ⟨ pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩
            → ⟨ γ ⊨ tmIs {n} (var i) v e ⟩
tmIs-var-in i γ v e h = ∣ nn (toℕ i)
  , ( refl
    , subst ⟨_⟩ (sym (appAt-adequate (suc e) zero (suc v) (nn (toℕ i) ∷ γ))) h ) ∣₁

tmIs-var-out : ∀ {n m} (i : Fin n) (γ : S ^ m) (v e : Fin m)
             → ⟨ γ ⊨ tmIs {n} (var i) v e ⟩
             → ⟨ pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩
tmIs-var-out i γ v e = PT.rec
  (snd (pr (# (toℕ i)) (fst (lookup v γ)) ∈ fst (lookup e γ)))
  (λ { (x , (qx , m)) →
    subst (λ w → ⟨ pr w (fst (lookup v γ)) ∈ fst (lookup e γ) ⟩) qx
      (subst ⟨_⟩ (appAt-adequate (suc e) zero (suc v) (x ∷ γ)) m) })
```


<!--en-->
## The set of satisfying environments

For each constructor, a formula describes which environments to retain by separation. Connectives combine the sets already obtained for subformulas. Quantifiers test an extended environment against the set for their subformula, whose arity is one larger.
<!--zh-->
## 满足公式的环境集

对每个构造子，一条公式描述分离时应当保留哪些环境。联结词组合子公式已经得到的集合；量词则扩展环境，并检验它是否属于元数多一的子公式所对应的集合。
<!--ja-->
## 論理式を充足する環境の集合

各構成子について、分出で残す環境を論理式によって指定します。結合子は部分式について既に得られた集合を組み合わせます。量化子は環境を拡張し、アリティが一つ大きい部分式に対応する集合への所属を調べます。
<!--/-->

<!--en-->
The quantifiers cons a member of the carrier onto the environment and ask whether
the result is in the value below, which is one arity up. The two bounded ones do
the same, and the member is drawn **from the carrier and guarded by the bounding
term's value**, not from that value alone. Drawing it from the value alone is
wrong for the same reason it was wrong in the internal clauses, where an audit
caught it: a member of the bound need not be a member of the carrier, so the
environment it would be consed onto would not be an environment, and the two
sides would not agree.
<!--zh-->
两个量词把载体的一个成员接到环境头上，再问结果是否落在下面那个取值之中，而后者高一个元数。两个有界量词做同样的事，而那个成员**取自载体、由界项的取值设防**，不是单取自那个取值。单取自那个取值是错的，理由与它在内部诸子句里曾经错的理由相同 (那次由一次审计抓出)：界的成员未必是载体的成员，于是被接上去的环境根本不是环境，两侧也就对不上。
<!--/-->


```agda
private
  opaque
    sep : (a : S) → Formula S 1 → S
    sep a φ = hasSeparationL a φ .fst .fst

    sep-mem : (a : S) (φ : Formula S 1) (x : S)
            → (x ∈ˢ sep a φ) ≡ ((x ∈ˢ a) ⊓ ((x ∷ []) ⊨ φ))
    sep-mem a φ = hasSeparationL a φ .fst .snd

module _ (B : S) where
  cond : ∀ {n} → Formula S n → Formula S 1

  Sat : ∀ {n} → Formula S n → S
  Sat {n} φ = sep (envSet B n) (cond φ)

  Sat-mem : ∀ {n} (φ : Formula S n) (x : S)
          → (x ∈ˢ Sat φ) ≡ ((x ∈ˢ envSet B n) ⊓ ((x ∷ []) ⊨ cond φ))
  Sat-mem {n} φ = sep-mem (envSet B n) (cond φ)

  cond (t ∈̇ u) =
    (∃̇ (∃̇ ( tmIs t (suc zero) (suc (suc zero))
          ∧̇ ( tmIs u zero (suc (suc zero))
          ∧̇ (var (suc zero) ∈̇ var zero) ))))
  cond (t ≐ u) =
    (∃̇ (∃̇ ( tmIs t (suc zero) (suc (suc zero))
          ∧̇ ( tmIs u zero (suc (suc zero))
          ∧̇ (var (suc zero) ≐ var zero) ))))
  cond (a ∧̇ b) =
    ((var zero ∈̇ con (Sat a)) ∧̇ (var zero ∈̇ con (Sat b)))
  cond (a ∨̇ b) =
    ((var zero ∈̇ con (Sat a)) ∨̇ (var zero ∈̇ con (Sat b)))
  cond (a ⇒̇ b) =
    ((var zero ∈̇ con (Sat a)) ⇒̇ (var zero ∈̇ con (Sat b)))
  cond ⊥̇ = ⊥̇
  cond (∃̇ a) =
    (∃̇∈ (con B) (∃̇ ( consAtL zero (suc zero) (suc (suc zero))
                  ∧̇ (var zero ∈̇ con (Sat a)) )))
  cond (∀̇ a) =
    (∀̇∈ (con B) (∀̇ ( consAtL zero (suc zero) (suc (suc zero))
                  ⇒̇ (var zero ∈̇ con (Sat a)) )))
  cond (∀̇∈ t a) =
    (∀̇ ( tmIs t zero (suc zero)
      ⇒̇ ∀̇∈ (con B) ( (var zero ∈̇ var (suc zero))
                   ⇒̇ ∀̇ ( consAtL zero (suc zero) (suc (suc (suc zero)))
                       ⇒̇ (var zero ∈̇ con (Sat a)) ) ) ))
  cond (∃̇∈ t a) =
    (∃̇ ( tmIs t zero (suc zero)
      ∧̇ ∃̇∈ (con B) ( (var zero ∈̇ var (suc zero))
                   ∧̇ ∃̇ ( consAtL zero (suc zero) (suc (suc (suc zero)))
                       ∧̇ (var zero ∈̇ con (Sat a)) ) ) ))
```


<!--en-->
## Membership equations for the ten constructors

Unfolding separation yields a membership equation for each constructor. These equations relate a formula's set of satisfying environments to those of its subformulas. They provide the precise identities needed to show that the constructed table satisfies the internal semantic clauses.
<!--zh-->
## 十个构造子的隶属关系等式

展开分离的刻画，就得到每个构造子对应的隶属关系等式。这些等式把一条公式的环境集与其子公式的环境集联系起来，从而为证明所构造的表满足内部语义子句提供精确的等式。
<!--ja-->
## 十の構成子に対する所属関係の等式

分出の特徴付けを展開すると、各構成子に対応する所属関係の等式が得られます。これらは論理式を充足する環境の集合と、部分式に対応する集合を結び付けます。この等式を用いて、構成した表が内部の意味論的な節を満たすことを示せます。
<!--/-->

<!--en-->
Each is the separation's own specification with the constructor's condition
already substituted, which is why they are one line apiece.
<!--zh-->
每一条都是那次分离自己的规格，且构造子的条件已代入，这就是它们一条一行的原因。
<!--/-->


```agda
  CondAtom : ∀ {n} → Term S n → Term S n
           → (S → S → Type (ℓ-suc ℓ)) → S → Type (ℓ-suc ℓ)
  CondAtom t u R z = Σ[ v ∈ S ] (Σ[ w ∈ S ]
    (⟨ (w ∷ v ∷ z ∷ []) ⊨ tmIs t (suc zero) (suc (suc zero)) ⟩
     × (⟨ (w ∷ v ∷ z ∷ []) ⊨ tmIs u zero (suc (suc zero)) ⟩ × R v w)))

  cond∈-in : ∀ {n} (t u : Term S n) (z : S)
           → ∥ CondAtom t u (λ v w → ⟨ fst v ∈ fst w ⟩) z ∥₁
           → ⟨ (z ∷ []) ⊨ cond (t ∈̇ u) ⟩
  cond∈-in t u z = PT.map (λ { (v , (w , r)) → v , ∣ w , r ∣₁ })

  cond∈-out : ∀ {n} (t u : Term S n) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (t ∈̇ u) ⟩
            → ∥ CondAtom t u (λ v w → ⟨ fst v ∈ fst w ⟩) z ∥₁
  cond∈-out t u z = PT.rec squash₁
    (λ { (v , hv) → PT.map (λ { (w , r) → v , (w , r) }) hv })

  cond≐-in : ∀ {n} (t u : Term S n) (z : S)
           → ∥ CondAtom t u (λ v w → fst v ≡ fst w) z ∥₁
           → ⟨ (z ∷ []) ⊨ cond (t ≐ u) ⟩
  cond≐-in t u z = PT.map (λ { (v , (w , r)) → v , ∣ w , r ∣₁ })

  cond≐-out : ∀ {n} (t u : Term S n) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (t ≐ u) ⟩
            → ∥ CondAtom t u (λ v w → fst v ≡ fst w) z ∥₁
  cond≐-out t u z = PT.rec squash₁
    (λ { (v , hv) → PT.map (λ { (w , r) → v , (w , r) }) hv })

  CondQuant : ∀ {n} → Formula S (suc n) → S → Type (ℓ-suc ℓ)
  CondQuant a z = Σ[ x ∈ S ] (⟨ fst x ∈ fst B ⟩
    × (Σ[ e' ∈ S ] (⟨ (e' ∷ x ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
                    × ⟨ fst e' ∈ fst (Sat a) ⟩)))

  cond∃-in : ∀ {n} (a : Formula S (suc n)) (z : S)
           → ∥ CondQuant a z ∥₁ → ⟨ (z ∷ []) ⊨ cond (∃̇ a) ⟩
  cond∃-in a z = PT.map (λ { (x , (x∈ , (e' , r))) → x , (x∈ , ∣ e' , r ∣₁) })

  cond∃-out : ∀ {n} (a : Formula S (suc n)) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (∃̇ a) ⟩ → ∥ CondQuant a z ∥₁
  cond∃-out a z = PT.rec squash₁
    (λ { (x , (x∈ , hv)) → PT.map (λ { (e' , r) → x , (x∈ , (e' , r)) }) hv })

  cond∀-in : ∀ {n} (a : Formula S (suc n)) (z : S)
           → ((x e' : S) → ⟨ fst x ∈ fst B ⟩
              → ⟨ (e' ∷ x ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
              → ⟨ fst e' ∈ fst (Sat a) ⟩)
           → ⟨ (z ∷ []) ⊨ cond (∀̇ a) ⟩
  cond∀-in a z k x x∈ e' hc = k x e' x∈ hc

  cond∀-out : ∀ {n} (a : Formula S (suc n)) (z : S)
            → ⟨ (z ∷ []) ⊨ cond (∀̇ a) ⟩
            → ((x e' : S) → ⟨ fst x ∈ fst B ⟩
               → ⟨ (e' ∷ x ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc zero)) ⟩
               → ⟨ fst e' ∈ fst (Sat a) ⟩)
  cond∀-out a z h x e' x∈ hc = h x x∈ e' hc

  CondBnd : ∀ {n} → Formula S (suc n) → S → S → Type (ℓ-suc ℓ)
  CondBnd a z w = Σ[ x ∈ S ] ((⟨ fst x ∈ fst B ⟩ × ⟨ fst x ∈ fst w ⟩)
    × (Σ[ e' ∈ S ]
        (⟨ (e' ∷ x ∷ w ∷ z ∷ []) ⊨ consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
         × ⟨ fst e' ∈ fst (Sat a) ⟩)))

  cond∃∈-in : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
            → ∥ (Σ[ w ∈ S ] (⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
                             × ∥ CondBnd a z w ∥₁)) ∥₁
            → ⟨ (z ∷ []) ⊨ cond (∃̇∈ t a) ⟩
  cond∃∈-in t a z = PT.map
    (λ { (w , (hw , hx)) → w , (hw , PT.map
      (λ { (x , ((x∈B , x∈w) , (e' , r))) → x , (x∈B , (x∈w , ∣ e' , r ∣₁)) })
      hx) })

  cond∃∈-out : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
             → ⟨ (z ∷ []) ⊨ cond (∃̇∈ t a) ⟩
             → ∥ (Σ[ w ∈ S ] (⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
                              × ∥ CondBnd a z w ∥₁)) ∥₁
  cond∃∈-out t a z = PT.map
    (λ { (w , (hw , hx)) → w , (hw , PT.rec squash₁
      (λ { (x , (x∈B , (x∈w , hv))) → PT.map
        (λ { (e' , r) → x , ((x∈B , x∈w) , (e' , r)) }) hv })
      hx) })

  cond∀∈-in : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
            → ((w : S) → ⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
               → (x e' : S) → ⟨ fst x ∈ fst B ⟩ → ⟨ fst x ∈ fst w ⟩
               → ⟨ (e' ∷ x ∷ w ∷ z ∷ [])
                    ⊨ consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
               → ⟨ fst e' ∈ fst (Sat a) ⟩)
            → ⟨ (z ∷ []) ⊨ cond (∀̇∈ t a) ⟩
  cond∀∈-in t a z k w hw x x∈B x∈w e' hc = k w hw x e' x∈B x∈w hc

  cond∀∈-out : ∀ {n} (t : Term S n) (a : Formula S (suc n)) (z : S)
             → ⟨ (z ∷ []) ⊨ cond (∀̇∈ t a) ⟩
             → ((w : S) → ⟨ (w ∷ z ∷ []) ⊨ tmIs t zero (suc zero) ⟩
                → (x e' : S) → ⟨ fst x ∈ fst B ⟩ → ⟨ fst x ∈ fst w ⟩
                → ⟨ (e' ∷ x ∷ w ∷ z ∷ [])
                     ⊨ consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
                → ⟨ fst e' ∈ fst (Sat a) ⟩)
  cond∀∈-out t a z h w hw x e' x∈B x∈w hc = h w hw x x∈B x∈w e' hc


```
