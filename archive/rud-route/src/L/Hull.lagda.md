# The definable hull

<!--en-->
The condensation lemma recognizes a transitive set as a level, and the
consumer side of that recognition is an elementary substructure of a level.
This chapter forges the other half of the pair: elementarity at a set carrier,
with the Tarski-Vaught criterion as the machine that proves it, and the
definable hull, the smallest elementary substructure containing a given set.
The scoping recon priced the reflection machinery as the wrong instrument
here: its closures cannot be iterated into a hull, so the direct formulation,
Devlin 5.3, is the honest route, and its order is not a formula but the
delivered meta well-order `orderAt` at the carrier, with `leastOf` picking
witnesses. That choice is the meta-pick formulation the recon recommended,
and this chapter settles the flag by building: the hull's elementarity goes
through the criterion induction, no reflection package is reached for, and
the order formula residue is confined to the two consequences, minimality and
the full elementary reading, that the leastness encoding costs.
<!--zh-->
凝聚引理把传递集识别为一层，而该识别的消费方一侧就是某层的初等子结构。本章锻造这一对的另一半：集合载体处的初等性，以 Tarski-Vaught 判据作为证明它的机器，以及可定义外壳，即含给定集合的最小初等子结构。范围侦察把反射机制定价为这里用错的工具：它的闭包无法迭代成外壳，因此直接形态，即 Devlin 5.3，才是诚实的路线，而其序不是公式，而是已交付的载体处元层良序 `orderAt`，由 `leastOf` 挑选见证。这个选择就是侦察所推荐的元选取形态，而本章以建造来落定那面旗：外壳的初等性穿过判据归纳，完全不触及反射包，而序公式残余被限制在两条推论，极小性与全初等读式上，正是最小性编码所费的两条。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Hull {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Smallness {ℓ} using ( module InnerSmall )
open import L.Constructible {ℓ} using
  ( isTransV; IsOrd; Lset; layer-trans; Lset-layer )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open import L.Choice.Step {ℓ} lem using ( orderAt )

open import Cubical.Data.Vec using ( map; lookup )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_; _,_ )
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Equiv
  using ( _≃_; equivFun; invEquiv; compEquiv; invEq; propBiimpl→Equiv )
open import Cubical.Data.Sigma using ( Σ-cong-equiv-snd )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; presentation )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
```

<!--en-->
## The stage
<!--zh-->
## 阶段
<!--/-->

<!--en-->
Everything below is relative to one stage `Lset α` of the tower. The stage is
transitive, so the absoluteness framework instantiates at it in one line: the
inner world `SL` of the stage's members, with the inner satisfaction `⊨ᵐ` and
the ambient reading `⊨ᵛ`. The order the hull will search along is the
delivered well-order `orderAt α ordα` on exactly that carrier, which is the
shape the scoping recon pinned: no internal order formula is reached for.
<!--zh-->
以下一切都相对于塔的某一层 `Lset α`。该层传递，故绝对性框架在它处一行实例化：层成员的内层世界 `SL`，连同内层满足 `⊨ᵐ` 与环境读式 `⊨ᵛ`。外壳将要沿之搜索的序，是已交付的良序 `orderAt α ordα`，恰落在那个载体上，这正是范围侦察钉下的形状：不触碰任何内部序公式。
<!--/-->

```agda
module AtStage (α : S) (ordα : IsOrd α) where

  Ltr : isTransV (Lset α)
  Ltr = layer-trans (Lset-layer α)

  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ Lset α) Ltr

  SL : Type (ℓ-suc ℓ)
  SL = AbsL.SM

  wL : SWO SL
  wL = orderAt α ordα
```

<!--en-->
## Elementarity at a set carrier
<!--zh-->
## 集合载体处的初等性
<!--/-->

<!--en-->
The elementary-substructure notion is stated at a transitive set carrier `M`
inside the stage. The formulas with parameters from `M` form the constant
domain `SM`; the same formula family is read twice, at `M` and at the stage,
the constants moved along `inL`. `M` is an elementary substructure of the
stage, written `Elementary`, when the two readings agree on every formula and
every environment of `M`'s members. The Tarski-Vaught criterion, `TarskiVaught`,
is witness closure: whenever the stage satisfies an existential, a witness
can be found in `M`. Devlin 5.1 is the equivalence of the two.
<!--zh-->
初等子结构概念陈述在阶段内部的传递集载体 `M` 处。带 `M` 中参数的公式构成常量域 `SM`；同一族公式读两遍，在 `M` 处与在阶段处，常量沿 `inL` 迁移。`M` 是阶段的初等子结构，写作 `Elementary`，当两套读式在每条公式与每个由 `M` 成员构成的环境上一致。Tarski-Vaught 判据 `TarskiVaught` 即见证封闭：凡阶段满足一个存在式，就有见证落在 `M` 中。Devlin 5.1 正是二者的等价。
<!--/-->

```agda
  module AtM (M : S) (Mtr : isTransV M) (M⊆L : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

    module AbsM = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ M) Mtr

    SM : Type (ℓ-suc ℓ)
    SM = AbsM.SM

    inL : SM → SL
    inL c = fst c , M⊆L (fst c) (snd c)

    Elementary : Type (ℓ-suc (ℓ-suc ℓ))
    Elementary = (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
               → (δ AbsM.⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))

    TarskiVaught : Type (ℓ-suc ℓ)
    TarskiVaught = (n : ℕ) (φ : Formula SM (suc n)) (δ : SM ^ n)
                 → ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ φ)) ⟩
                 → ∥ Σ[ q ∈ SM ] ⟨ (inL q ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL φ) ⟩ ∥₁
```

<!--en-->
The equivalence is proved in the two directions. Elementarity gives witness
closure by reading the existential sentence at `M` and moving the witness
back out through the agreement on the matrix. Witness closure gives
elementarity by one induction over the full syntax: the atoms and connectives
are congruences on the two semantics; the existential case consumes the
criterion; the universal case is the classical step, a double-negation
elimination at the stage reading; and the bounded quantifiers consume the
transitivity of `M`, exactly where the absoluteness chapter spent it.
<!--zh-->
等价分两个方向证明。初等性给出见证封闭：把存在句读在 `M` 处，再经矩阵上的一致把见证搬回来。见证封闭给出初等性：对完整语法做一次归纳，原子与联结词是两个语义上的同余；存在情形消费判据；全称情形是经典一步，在阶段读式处做双重否定消去；有界量词消费 `M` 的传递性，恰是绝对性章花掉它的地方。
<!--/-->

```agda
    private
      lookup-inL : {n : ℕ} (i : Fin n) (δ : SM ^ n)
                 → lookup i (map inL δ) ≡ inL (lookup i δ)
      lookup-inL zero (c ∷ δ) = refl
      lookup-inL (suc i) (c ∷ δ) = lookup-inL i δ

      tm-agree : (n : ℕ) (t : Term SM n) (δ : SM ^ n)
               → fst (AbsM.⟦ t ⟧ᵐ δ) ≡ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ))
      tm-agree n (con c) δ = refl
      tm-agree n (var i) δ = sym (cong fst (lookup-inL i δ))

      dne : (P : hProp (ℓ-suc ℓ)) → (((⟨ P ⟩) → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
      dne P h = Sum.rec (λ p → p)
        (λ (np : ⟨ P ⟩ → Empty.⊥) → Empty.rec (h np)) (lem P)

    elem→TV : Elementary → TarskiVaught
    elem→TV elem n φ δ h =
      PT.map (λ { (q , hq) →
        q , subst ⟨_⟩ (elem (suc n) φ (q ∷ δ)) hq })
        (subst ⟨_⟩ (sym (elem n (∃̇ φ) δ)) h)

    TV→elem : TarskiVaught → Elementary
    TV→elem tv n φ δ = go n φ δ
      where
      go : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
         → (δ AbsM.⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))
      go n (t ∈̇ u) δ = cong₂ _∈ˢ_ (tm-agree n t δ) (tm-agree n u δ)
      go n (t ≐ u) δ = cong₂ _≈ˢ_ (tm-agree n t δ) (tm-agree n u δ)
      go n (φ ∧̇ ψ) δ = cong₂ _⊓_ (go n φ δ) (go n ψ δ)
      go n (φ ∨̇ ψ) δ = cong₂ _⊔_ (go n φ δ) (go n ψ δ)
      go n (φ ⇒̇ ψ) δ = cong₂ _⇒_ (go n φ δ) (go n ψ δ)
      go n (¬̇ φ) δ = cong ¬_ (go n φ δ)
      go n ⊤̇ δ = refl
      go n ⊥̇ δ = refl
      go n (∃̇ ψ) δ = ⇔toPath fwd bwd
        where
        fwd : ⟨ δ AbsM.⊨ᵐ (∃̇ ψ) ⟩ → ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ ψ)) ⟩
        fwd = PT.rec (snd (map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ ψ))))
          (λ { (q , hq) → ∣ inL q , subst ⟨_⟩ (go (suc n) ψ (q ∷ δ)) hq ∣₁ })
        bwd : ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ ψ)) ⟩ → ⟨ δ AbsM.⊨ᵐ (∃̇ ψ) ⟩
        bwd h = PT.map (λ { (q , hq) → q , subst ⟨_⟩ (sym (go (suc n) ψ (q ∷ δ))) hq })
          (tv n ψ δ h)
      go n (∀̇ ψ) δ = ⇔toPath fwd bwd
        where
        fwd : ((q : SM) → ⟨ (q ∷ δ) AbsM.⊨ᵐ ψ ⟩)
            → (x : SL) → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩
        fwd h x = dne ((x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ)) λ nx →
          PT.rec isProp⊥ (λ { (q , hq) →
            hq (subst ⟨_⟩ (go (suc n) ψ (q ∷ δ)) (h q)) })
            (tv n (¬̇ ψ) δ ∣ x , nx ∣₁)
        bwd : ((x : SL) → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩)
            → (q : SM) → ⟨ (q ∷ δ) AbsM.⊨ᵐ ψ ⟩
        bwd h q = subst ⟨_⟩ (sym (go (suc n) ψ (q ∷ δ))) (h (inL q))
      go n (∀̇∈ t ψ) δ = ⇔toPath fwd bwd
        where
        fwd : ((q : SM) → ⟨ fst q ∈ˢ fst (AbsM.⟦ t ⟧ᵐ δ) ⟩ → ⟨ (q ∷ δ) AbsM.⊨ᵐ ψ ⟩)
            → (x : SL) → ⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
            → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩
        fwd h x hx =
          let hxL : ⟨ fst x ∈ˢ fst (AbsM.⟦ t ⟧ᵐ δ) ⟩
              hxL = subst (λ s → ⟨ fst x ∈ˢ s ⟩) (sym (tm-agree n t δ)) hx
              xM : SM
              xM = fst x , Mtr {x = fst (AbsM.⟦ t ⟧ᵐ δ)} {y = fst x} hxL (snd (AbsM.⟦ t ⟧ᵐ δ))
          in subst (λ e → ⟨ (e ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩)
                   (Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) refl)
                   (subst ⟨_⟩ (go (suc n) ψ (xM ∷ δ)) (h xM hxL))
        bwd : ((x : SL) → ⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
                     → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩)
            → (q : SM) → ⟨ fst q ∈ˢ fst (AbsM.⟦ t ⟧ᵐ δ) ⟩ → ⟨ (q ∷ δ) AbsM.⊨ᵐ ψ ⟩
        bwd h q hq =
          subst ⟨_⟩ (sym (go (suc n) ψ (q ∷ δ)))
            (h (inL q) (subst (λ s → ⟨ fst q ∈ˢ s ⟩) (tm-agree n t δ) hq))
      go n (∃̇∈ t ψ) δ = ⇔toPath fwd bwd
        where
        fwd : ∥ Σ[ q ∈ SM ] (⟨ fst q ∈ˢ fst (AbsM.⟦ t ⟧ᵐ δ) ⟩ × ⟨ (q ∷ δ) AbsM.⊨ᵐ ψ ⟩) ∥₁
            → ∥ Σ[ x ∈ SL ] (⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
                          × ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩) ∥₁
        fwd = PT.map (λ { (q , hq , hψ) →
          inL q , (subst (λ s → ⟨ fst q ∈ˢ s ⟩) (tm-agree n t δ) hq ,
                   subst ⟨_⟩ (go (suc n) ψ (q ∷ δ)) hψ) })
        bwd : ∥ Σ[ x ∈ SL ] (⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
                          × ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩) ∥₁
            → ∥ Σ[ q ∈ SM ] (⟨ fst q ∈ˢ fst (AbsM.⟦ t ⟧ᵐ δ) ⟩ × ⟨ (q ∷ δ) AbsM.⊨ᵐ ψ ⟩) ∥₁
        bwd = PT.map (λ { (x , hx , hψ) →
          let hxL : ⟨ fst x ∈ˢ fst (AbsM.⟦ t ⟧ᵐ δ) ⟩
              hxL = subst (λ s → ⟨ fst x ∈ˢ s ⟩) (sym (tm-agree n t δ)) hx
              xM : SM
              xM = fst x , Mtr {x = fst (AbsM.⟦ t ⟧ᵐ δ)} {y = fst x} hxL (snd (AbsM.⟦ t ⟧ᵐ δ))
          in xM , hxL ,
             subst ⟨_⟩ (sym (go (suc n) ψ (xM ∷ δ)))
               (subst (λ e → ⟨ (e ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩)
                      (Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) refl)
                      hψ) })

    TV-thm : (Elementary → TarskiVaught) × (TarskiVaught → Elementary)
    TV-thm = elem→TV , TV→elem
```

<!--en-->
## The definable hull
<!--zh-->
## 可定义外壳
<!--/-->

<!--en-->
The hull is built from a set `X` of parameters inside the stage. Devlin's
membership, "definable from `X`", is taken in the least-witness shape the
scoping recon chose: an element lies in the hull when it is the
`<_L`-least witness, in the meta well-order, of a formula with parameters from
`X`. The small satisfaction of the essentially-small world compresses the
existence of a witness one universe down, so the hull's index, a formula
paired with a small witness, is small and the hull is a set with no resizing.
The value of an index is the least witness itself, produced by `leastOf` over
the delivered order, so the hull is a `sett` over formulas, exactly the index
the cardinal chapter's count will run on.
<!--zh-->
外壳由阶段内部的参数集 `X` 建成。Devlin 的隶属，「由 `X` 可定义」，取范围侦察所选的最小见证形态：一个元素落在外壳中，当它是某条带 `X` 中参数的公式在元层良序 `<_L` 下的最小见证。本质小世界的小满足把见证的存在压低一层宇宙，故外壳的索引，一条公式配一个小见证，是小的，外壳成为集合而不花降层。索引的值即最小见证本身，由 `leastOf` 在已交付的序上产出，故外壳是公式上的 `sett`，恰是基数章计数将要跑的那个索引。
<!--/-->

```agda
    module Hull (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

      eL : ⟪ Lset α ⟫ ≃ SL
      eL = compEquiv (invEquiv (presentation (Lset α)))
             (Σ-cong-equiv-snd (λ v →
               propBiimpl→Equiv (snd (v ∈ₛ Lset α)) (snd (v ∈ˢ Lset α))
                 (∈∈ₛ {a = v} {b = Lset α} .snd) (∈∈ₛ {a = v} {b = Lset α} .fst)))

      toSL : ⟪ Lset α ⟫ → SL
      toSL m = ⟪ Lset α ⟫↪ m , member (Lset α) m

      inStg : ⟪ X ⟫ → SL
      inStg m = ⟪ X ⟫↪ m , X⊆L (⟪ X ⟫↪ m) (member X m)

      module Small = InnerSmall (λ x → x ∈ˢ Lset α) ⟪ Lset α ⟫ eL {K = ⟪ X ⟫} inStg

      SatAt : Formula ⟪ X ⟫ 1 → SL → Type (ℓ-suc ℓ)
      SatAt φ a = ⟨ (a ∷ []) Small.⊨ᵐ φ ⟩

      SatAt-h : Formula ⟪ X ⟫ 1 → SL → hProp (ℓ-suc ℓ)
      SatAt-h φ a = (SatAt φ a , snd ((a ∷ []) Small.⊨ᵐ φ))

      Witnessed : Formula ⟪ X ⟫ 1 → Type (ℓ-suc ℓ)
      Witnessed φ = ∥ Σ[ a ∈ SL ] SatAt φ a ∥₁

      Witnessed-small : Formula ⟪ X ⟫ 1 → Type ℓ
      Witnessed-small φ = ∥ Σ[ m ∈ ⟪ Lset α ⟫ ]
        ⟨ Small.⊨ᵐ-small φ (toSL m ∷ []) .fst ⟩ ∥₁

      small→big : (φ : Formula ⟪ X ⟫ 1) → Witnessed-small φ → Witnessed φ
      small→big φ = PT.map (λ { (m , hm) →
        toSL m , invEq (Small.⊨ᵐ-small φ (toSL m ∷ []) .snd) hm })

      big→small : (φ : Formula ⟪ X ⟫ 1) → Witnessed φ → Witnessed-small φ
      big→small φ = PT.map (λ { (a , ha) →
        let m = fiber (Lset α) (a .snd) .fst
        in m , equivFun (Small.⊨ᵐ-small φ (toSL m ∷ []) .snd)
                 (subst (λ e → ⟨ (e ∷ []) Small.⊨ᵐ φ ⟩)
                        (Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd)
                           (sym (fiber (Lset α) (a .snd) .snd)))
                        ha) })

      opaque
        leastSearch : (φ : Formula ⟪ X ⟫ 1) (w : Witnessed-small φ)
                    → Σ[ a ∈ SL ] IsLeast wL (SatAt-h φ) a
        leastSearch φ w = leastOf wL {ℓ'' = ℓ-suc ℓ} lem (SatAt-h φ) (small→big φ w)

      opaque
        unfolding leastSearch
        leastSearch-spec : (φ : Formula ⟪ X ⟫ 1) (w : Witnessed-small φ)
                         → leastSearch φ w
                         ≡ leastOf wL {ℓ'' = ℓ-suc ℓ} lem (SatAt-h φ) (small→big φ w)
        leastSearch-spec φ w = refl

      leastWit : (φ : Formula ⟪ X ⟫ 1) → Witnessed-small φ → SL
      leastWit φ w = leastSearch φ w .fst

      leastWit-spec : (φ : Formula ⟪ X ⟫ 1) (w : Witnessed-small φ)
                    → IsLeast wL (SatAt-h φ) (leastWit φ w)
      leastWit-spec φ w = leastSearch φ w .snd

      leastVal : (φ : Formula ⟪ X ⟫ 1) → Witnessed-small φ → S
      leastVal φ w = fst (leastWit φ w)

      leastVal-spec : (φ : Formula ⟪ X ⟫ 1) (w : Witnessed-small φ)
                    → leastVal φ w ≡ fst (leastWit φ w)
      leastVal-spec φ w = refl

      hullVal : Σ[ φ ∈ Formula ⟪ X ⟫ 1 ] Witnessed-small φ → S
      hullVal (φ , w) = fst (leastWit φ w)

      Hull : S
      Hull = sett (Σ[ φ ∈ Formula ⟪ X ⟫ 1 ] Witnessed-small φ) hullVal
```

<!--en-->
The hull contains `X`: each member `x` of `X` is the least witness of the
formula "the variable is `x`", and the least witness of a formula with a
witness is unique, so the hull value at that formula is `x` itself. The
elementarity of the hull is the Tarski criterion at its own parameter source:
whenever the stage satisfies an existential formula with parameters from `X`,
the least witness of that formula lies in the hull and satisfies it. That is
the criterion instance the meta-pick formulation delivers without any order
formula.
<!--zh-->
外壳含 `X`：`X` 的每个成员 `x` 都是公式「该变量是 `x`」的最小见证，而有见证的公式的最小见证唯一，故外壳在该公式处的值正是 `x` 自身。外壳的初等性是 Tarski 判据在其自身参数源处的实例：凡阶段满足带 `X` 中参数的存在公式，该公式的最小见证就落在外壳中并满足它。这正是元选取形态无需任何序公式便交付的判据实例。
<!--/-->

```agda
      module XInM (x : S) (x∈X : ⟨ x ∈ˢ X ⟩) where
        mx : ⟪ X ⟫
        mx = fiber X x∈X .fst

        xL : SL
        xL = x , X⊆L x x∈X

        φₓ : Formula ⟪ X ⟫ 1
        φₓ = var zero ≐ con mx

        xWit : SatAt φₓ xL
        xWit = sym (fiber X x∈X .snd)

        witness-eq : (b : SL) → SatAt φₓ b → b ≡ xL
        witness-eq b hb = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd)
          (hb ∙ sym xWit)

        xLeast : IsLeast wL (SatAt-h φₓ) xL
        xLeast = xWit , λ b hb hlt →
          SWO.irr∙ wL xL (subst (λ z → SWO._<∙_ wL z xL) (witness-eq b hb) hlt)

        wₓ : Witnessed-small φₓ
        wₓ = big→small φₓ ∣ xL , xWit ∣₁

        x≡x : fst (leastWit φₓ wₓ) ≡ x
        x≡x = leastWit-spec φₓ wₓ .fst ∙ sym xWit

        inM : ⟨ x ∈ˢ Hull ⟩
        inM = ∣ (φₓ , wₓ) , x≡x ∣₁

      X⊆M : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Hull ⟩
      X⊆M x x∈X = XInM.inM x x∈X

      hull-closed : (φ : Formula ⟪ X ⟫ 1) → ⟨ [] Small.⊨ᵐ (∃̇ φ) ⟩
                  → ∥ Σ[ a ∈ SL ] (⟨ fst a ∈ˢ Hull ⟩ × SatAt φ a) ∥₁
      hull-closed φ h = ∣ a , (a∈H , sat) ∣₁
        where
        w : Witnessed-small φ
        w = big→small φ h
        a : SL
        a = leastWit φ w
        least : IsLeast wL (SatAt-h φ) a
        least = leastWit-spec φ w
        a∈H : ⟨ fst a ∈ˢ Hull ⟩
        a∈H = ∣ (φ , w) , refl ∣₁
        sat : SatAt φ a
        sat = least .fst
```

<!--en-->
## The order formula residue
<!--zh-->
## 序公式残余
<!--/-->

<!--en-->
The scoping recon's flagged question is settled by what is delivered above:
the direct hull builds, elementarity runs through the criterion induction, and
no reflection package is reached for. The meta-pick formulation has one
measured cost. The hull's membership, "least witness of a formula from `X`",
carries the order only at the meta level, and two consequences of Devlin 5.3
need the order inside the object language: the full elementary reading at
parameters from the hull, and the smallestness, `Hull ⊆ N` for every
elementary `N` containing `X`. Each reduces to one residue, the adequate
internal order formula `σ_<` at the carrier (the W3 residual), which encodes
"no smaller witness" as a formula, turning every hull member into the unique
witness of a formula with parameters from `X`. The full elementary reading
additionally needs the constants-to-variables face of the relabelling kit.
Both are stated in the report, priced, and left standing.
<!--zh-->
范围侦察所旗标的那个问题，由上文交付的内容落定：直接外壳建成，初等性穿过判据归纳，完全不触及反射包。元选取形态有一条测得的代价。外壳的隶属，「某条带 `X` 中参数的公式的最小见证」，只在元层携带序，而 Devlin 5.3 的两条推论需要序进入对象语言：带外壳中参数的全初等读式，以及最小性，即对所有含 `X` 的初等 `N` 有 `Hull ⊆ N`。每条都化归到同一条残余，即载体处适足的内部序公式 `σ_<` (即 W3 残余)，它把「没有更小见证」编码为公式，使外壳的每个成员都成为某条带 `X` 中参数的公式的唯一见证。全初等读式还额外需要重标工具组的「常量变变量」那一面。两者都在报告中陈述、定价并留待后继。
<!--/-->

<!--en-->
## Recap
<!--zh-->
## 小结
<!--/-->

<!--en-->
The chapter delivers elementarity at a transitive set carrier and its
Tarski-Vaught criterion, equivalent over the full syntax by one formula
induction, with the bounded-quantifier cases consuming transitivity and the
universal case consuming the excluded middle. Over that base, the definable
hull of a set `X` is built as the set of least witnesses of `X`-parameter
formulas: a `sett` over the formulas themselves, so the cardinal chapter's
count will run on the delivered index; it contains `X`, and it satisfies the
Tarski criterion at its own parameter source. The order formula residue
closes the two remaining consequences of Devlin 5.3, the full elementary
reading and the smallestness, and is the flagged risk's measured cost.
<!--zh-->
本章交付传递集载体处的初等性及其 Tarski-Vaught 判据，二者经一次公式归纳在完整语法上等价，有界量词情形消费传递性，全称情形消费排中律。在这块基底上，集合 `X` 的可定义外壳建成「带 `X` 中参数的公式的最小见证」之集：一个以公式自身为索引的 `sett`，故基数章的计数将跑在已交付的索引上；它含 `X`，并在其自身参数源处满足 Tarski 判据。序公式残余闭合 Devlin 5.3 剩余的两条推论，全初等读式与最小性，也正是那面被旗标的旗的测得代价。
<!--/-->
