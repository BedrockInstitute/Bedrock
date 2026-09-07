<!--en-->
# Building and collapsing a Skolem hull

A Skolem hull closes a chosen set under least witnesses, making an elementary part of a constructible stage. This chapter constructs that hull, proves its elementarity, collapses it to a transitive set, and records how satisfaction and bounded formulas pass across the collapse.
<!--zh-->
# 构造并塌缩 Skolem 壳

Skolem 壳把给定集合对最小见证闭合，从而得到可构造阶段的一个初等部分。本章构造该壳，证明其初等性，把它塌缩为传递集，并记录满足关系与有界公式如何跨过这次塌缩。
<!--ja-->
# Skolem 包を構成して崩壊させる

Skolem 包は選んだ集合を最小の証人について閉じ、構成可能段階の初等部分を作る。本章ではその包を構成して初等性を示し、推移的集合へ崩壊させ、充足関係と有界論理式が崩壊を越えてどう移るかを整理する。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.SkolemHull {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
import FOL.Manipulation.ConstantOccurrences
import FOL.Semantics
open import FOL.Manipulation.ConstantOccurrences using ( countFo; constantsFo )
open import FOL.Manipulation.ParameterAbstraction using ( absFo; ⊨-abs )
open import FOL.Manipulation.ConstantMapping using ( mapFo; mapTm; mapFo-comp; embed )
open import FOL.Manipulation.Relabelling using ( embed-⊨; mapΔ₀; ⊨-map )
open import FOL.Manipulation.Renaming using ( renameTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Collapse {ℓ} using ( module Collapse; isExt; isTrans )
open import V.Smallness {ℓ} using ( separateFromSmall; module Δ₀Small )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ; Lset-suc )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isTransV; IsOrd; Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ
        ; layer-trans; Lset-layer )
open import L.Ordinal {ℓ} using ( mem-ord; ω-ord; #∈ω; ∅-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset→∈; rank-Lset )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rank {ℓ} using ( rank-fix )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf )
open import L.Choice.StageOrders {ℓ} lem using ( orderAt )
open import L.Coding.CodeConstructibility {ℓ} using ( cup-out; cup-inl; cup-inr; sgl-out )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; []; _++_ )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_; _,_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; _∪_; ⁅_,_⁆; ⁅_⁆s; union-ax; pairing-ax; module InfinitySet
        ; SetPackage; SingletonPackage )  -- lint-agda: keep (SetPackage via record projection)
open InfinitySet using ( ω; sucV )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; extensionality )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ using ( _^_; module At )
open SemV using ( _^_ )
```

The 𝒮ʟ carrier, for the syntax of the witness slot, and the
constant count at it.

```agda
module CS = hPropStructure 𝒮ʟ using ( S )
module Cnt = FOL.Manipulation.ConstantOccurrences.ZeroOccurrences CS.S using ( erase; erase-inv )

module D0 = Δ₀Small {ℓc = ℓ-suc ℓ} {K = ⊥* {ℓ-suc ℓ}} (λ b → Empty.rec* b)
  using ( Δ₀-small )
```

J tower instantiates the same core (DD4).

```agda
module TermAlgebra (𝒮 : ZFStructure (hPropAlgebra (ℓ-suc ℓ)))
                   (toSet : ZFStructure.S 𝒮 → V ℓ)
                   (wo : SWO (ZFStructure.S 𝒮))
                   (junk : ZFStructure.S 𝒮)
                   {K : Type ℓ} (emb : K → ZFStructure.S 𝒮) where

  open ZFStructure 𝒮 hiding ( _∈ˢ_ ) renaming ( S to S𝒮 )

  private module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮
  open Sem using () renaming ( _^_ to _^𝒮_ )
  module At0 = Sem.At (⊥* {ℓ}) Empty.rec* using ( _⊨_ )
  _⊨₀_ : {n : ℕ} → S𝒮 ^𝒮 n → Formula (⊥* {ℓ}) n → hProp (ℓ-suc ℓ)
  _⊨₀_ = At0._⊨_

  data Code : Type ℓ where
    base : K → Code
    wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code

  Sat : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec S𝒮 k → Type (ℓ-suc ℓ)
  Sat k ψ vs = ∥ Σ[ a ∈ S𝒮 ] ⟨ (a ∷ vs) ⊨₀ ψ ⟩ ∥₁

  search : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (vs : Vec S𝒮 k)
         → Sat k ψ vs → S𝒮
  search k ψ vs w = leastOf wo {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ vs) ⊨₀ ψ) w .fst

  mutual
    vals : {m : ℕ} → Vec Code m → Vec S𝒮 m
    vals [] = []
    vals (c ∷ cs') = val c ∷ vals cs'

    val : Code → S𝒮
    val (base m) = emb m
    val (wit k ψ cs) = Sum.rec (search k ψ (vals cs)) (λ _ → junk)
                       (lem (Sat k ψ (vals cs) , squash₁))

```

The junk split hides the search; open it when a witness exists, since the
other branch carries a contradiction.

```agda
  sum-stuck : {X : Type (ℓ-suc ℓ)} (x : X) (px : isProp X)
            → (f : X → S𝒮) (g : (X → Empty.⊥) → S𝒮) (s : X ⊎ (X → Empty.⊥))
            → Sum.rec f g s ≡ f x
  sum-stuck x px f g (Sum.inl x') = sym (cong f (px x x'))
  sum-stuck x px f g (Sum.inr h)  = Empty.rec (h x)

  val-wit : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
          → (w : Sat k ψ (vals cs)) → val (wit k ψ cs) ≡ search k ψ (vals cs) w
  val-wit k ψ cs w = sum-stuck w squash₁ (search k ψ (vals cs)) (λ _ → junk)
                       (lem (Sat k ψ (vals cs) , squash₁))

  vals≡map : {m : ℕ} (cs : Vec Code m) → vals cs ≡ map val cs
  vals≡map [] = refl
  vals≡map (c ∷ cs') = cong₂ _∷_ refl (vals≡map cs')

  Hull : V ℓ
  Hull = sett Code (λ c → toSet (val c))

  inHull : (c : Code) → ⟨ toSet (val c) ∈ˢ Hull ⟩
  inHull c = ∣ c , refl ∣₁

  closed : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
         → Sat k ψ (vals cs)
         → ∥ Σ[ a ∈ S𝒮 ]
              (⟨ toSet a ∈ˢ Hull ⟩ × ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩) ∥₁
  closed k ψ cs w = ∣ a , a∈H , sat ∣₁
    where
    a : S𝒮
    a = search k ψ (vals cs) w

    pa : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
    pa = leastOf wo {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ vals cs) ⊨₀ ψ) w .snd .fst

    a∈H : ⟨ toSet a ∈ˢ Hull ⟩
    a∈H = subst (λ z → ⟨ toSet z ∈ˢ Hull ⟩) (val-wit k ψ cs w)
            (inHull (wit k ψ cs))

    sat : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
    sat = pa
```

<!--en-->
## Transporting satisfaction along a carrier map

A single induction on formulas compares satisfaction before and after a map of carriers. Atomic formulas require preservation of membership and equality; existential formulas require every outer witness to have an inner preimage.
<!--zh-->
## 沿载体映射搬运满足关系

对公式作一次归纳，即可比较载体映射前后的满足关系。原子公式要求保持隶属与相等；存在公式要求每个外部见证都有内部原像。
<!--ja-->
## 台の写像に沿って充足関係を移す

論理式について一度帰納すれば、台の写像の前後で充足関係を比較できる。原子論理式では所属と等号の保存を、存在論理式では外側の各証人が内側に逆像をもつことを仮定する。
<!--/-->

One ten-clause recursion, shared by the inclusion of a carrier into the
stage and by the collapse bijection: the non-atomic clauses are the same in
both, so the atoms and the witness principle are parameters.

```agda
module SatTransfer (MA MB : S → hProp (ℓ-suc ℓ)) where

  SA : Type (ℓ-suc ℓ)
  SA = Σ[ x ∈ S ] ⟨ MA x ⟩

  SB : Type (ℓ-suc ℓ)
  SB = Σ[ x ∈ S ] ⟨ MB x ⟩

  module SemA = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ MA)
    using ( module At )
  module SemB = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ MB)
    using ( module At )
  open SemA.At SA id renaming ( _⊨_ to _⊨ᴬ_ ; ⟦_⟧ to ⟦_⟧ᴬ )
  open SemB.At SB id renaming ( _⊨_ to _⊨ᴮ_ ; ⟦_⟧ to ⟦_⟧ᴮ )

  Agree : (SA → SB) → Type (ℓ-suc (ℓ-suc ℓ))
  Agree g = (n : ℕ) (φ : Formula SA n) (δ : SA ^ n)
          → (δ ⊨ᴬ φ) ≡ (map g δ ⊨ᴮ mapFo g φ)
```

Every outer witness of an existential is met by an inner one.

```agda
  Witness : (SA → SB) → Type (ℓ-suc ℓ)
  Witness g = (n : ℕ) (φ : Formula SA (suc n)) (δ : SA ^ n)
            → ⟨ map g δ ⊨ᴮ mapFo g (∃̇ φ) ⟩
            → ∥ Σ[ q ∈ SA ] ⟨ (g q ∷ map g δ) ⊨ᴮ mapFo g φ ⟩ ∥₁

  module Along (g : SA → SB)
    (at∈ : (n : ℕ) (t u : Term SA n) (δ : SA ^ n)
         → (δ ⊨ᴬ (t ∈̇ u)) ≡ (map g δ ⊨ᴮ mapFo g (t ∈̇ u)))
    (at≐ : (n : ℕ) (t u : Term SA n) (δ : SA ^ n)
         → (δ ⊨ᴬ (t ≐ u)) ≡ (map g δ ⊨ᴮ mapFo g (t ≐ u)))
    (wit : Witness g) where

    private
      renA : {n : ℕ} (t : Term SA n) (x : SA) (δ : SA ^ n)
           → ⟦ renameTm suc t ⟧ᴬ (x ∷ δ) ≡ ⟦ t ⟧ᴬ δ
      renA (con c) x δ = refl
      renA (var i) x δ = refl

      renB : {n : ℕ} (t : Term SB n) (x : SB) (δ : SB ^ n)
           → ⟦ renameTm suc t ⟧ᴮ (x ∷ δ) ≡ ⟦ t ⟧ᴮ δ
      renB (con c) x δ = refl
      renB (var i) x δ = refl
```

Relabelling and weakening commute on terms.

```agda
      mapTm-ren : {n : ℕ} (t : Term SA n)
                → mapTm g (renameTm suc t) ≡ renameTm suc (mapTm g t)
      mapTm-ren (con c) = refl
      mapTm-ren (var i) = refl

      renG : {n : ℕ} (t : Term SA n) (x : SB) (δ : SA ^ n)
           → ⟦ mapTm g (renameTm suc t) ⟧ᴮ (x ∷ map g δ) ≡ ⟦ mapTm g t ⟧ᴮ (map g δ)
      renG t x δ = cong (λ u → ⟦ u ⟧ᴮ (x ∷ map g δ)) (mapTm-ren t)
                 ∙ renB (mapTm g t) x (map g δ)

      memRen : {n : ℕ} (t : Term SA n) (x : SB) (δ : SA ^ n)
             → (fst x ∈ˢ fst (⟦ mapTm g (renameTm suc t) ⟧ᴮ (x ∷ map g δ)))
             ≡ (fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)))
      memRen t x δ = cong (λ s → fst x ∈ˢ fst s) (renG t x δ)
```

The side condition of a bounded quantifier, read across the map.

```agda
      memPath : {n : ℕ} (t : Term SA n) (q : SA) (δ : SA ^ n)
              → (fst q ∈ˢ fst (⟦ t ⟧ᴬ δ))
              ≡ (fst (g q) ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)))
      memPath {n} t q δ =
        cong (λ s → fst q ∈ˢ fst s) (sym (renA t q δ))
        ∙ at∈ (suc n) (var zero) (renameTm suc t) (q ∷ δ)
        ∙ memRen t (g q) δ

      dne : (P : hProp (ℓ-suc ℓ)) → (((⟨ P ⟩) → Empty.⊥) → Empty.⊥) → ⟨ P ⟩
      dne P h = Sum.rec (λ p → p)
        (λ (np : ⟨ P ⟩ → Empty.⊥) → Empty.rec (h np)) (lem P)

    agree : Agree g
    agree n (t ∈̇ u) δ = at∈ n t u δ
    agree n (t ≐ u) δ = at≐ n t u δ
    agree n (φ ∧̇ ψ) δ = cong₂ _⊓_ (agree n φ δ) (agree n ψ δ)
    agree n (φ ∨̇ ψ) δ = cong₂ _⊔_ (agree n φ δ) (agree n ψ δ)
    agree n (φ ⇒̇ ψ) δ = cong₂ _⇒_ (agree n φ δ) (agree n ψ δ)
    agree n ⊥̇ δ = refl
    agree n (∃̇ ψ) δ = ⇔toPath fwd bwd
      where
      fwd : ⟨ δ ⊨ᴬ (∃̇ ψ) ⟩ → ⟨ map g δ ⊨ᴮ mapFo g (∃̇ ψ) ⟩
      fwd = PT.rec (snd (map g δ ⊨ᴮ mapFo g (∃̇ ψ)))
        (λ { (q , hq) → ∣ g q , subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ)) hq ∣₁ })
      bwd : ⟨ map g δ ⊨ᴮ mapFo g (∃̇ ψ) ⟩ → ⟨ δ ⊨ᴬ (∃̇ ψ) ⟩
      bwd h = PT.map (λ { (q , hq) →
        q , subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ))) hq }) (wit n ψ δ h)
    agree n (∀̇ ψ) δ = ⇔toPath fwd bwd
      where
      fwd : ((q : SA) → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩)
          → (x : SB) → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩
      fwd h x = dne ((x ∷ map g δ) ⊨ᴮ mapFo g ψ) λ nx →
        PT.rec isProp⊥ (λ { (q , hq) →
          lower (hq (subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ)) (h q))) })
          (wit n (¬̇ ψ) δ ∣ x , (λ yes → lift (nx yes)) ∣₁)
      bwd : ((x : SB) → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩)
          → (q : SA) → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩
      bwd h q = subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ))) (h (g q))
    agree n (∀̇∈ t ψ) δ = ⇔toPath fwd bwd
      where
      mat : Formula SA (suc n)
      mat = (var zero ∈̇ renameTm suc t) ∧̇ ¬̇ ψ
      fwd : ((q : SA) → ⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩)
          → (x : SB) → ⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
          → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩
      fwd h x hx =
        dne ((x ∷ map g δ) ⊨ᴮ mapFo g ψ) λ nx →
        PT.rec isProp⊥ (λ { (q , hq) →
          lower (hq .snd (subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ))
            (h q (subst ⟨_⟩ (sym (memPath t q δ))
                    (subst ⟨_⟩ (memRen t (g q) δ) (hq .fst)))))) })
          (wit n mat δ ∣ x , (subst ⟨_⟩ (sym (memRen t x δ)) hx
            , (λ yes → lift (nx yes))) ∣₁)
      bwd : ((x : SB) → ⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
                   → ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩)
          → (q : SA) → ⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ → ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩
      bwd h q hq =
        subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ)))
          (h (g q) (subst ⟨_⟩ (memPath t q δ) hq))
    agree n (∃̇∈ t ψ) δ = ⇔toPath fwd bwd
      where
      mat : Formula SA (suc n)
      mat = (var zero ∈̇ renameTm suc t) ∧̇ ψ
      fwd : ∥ Σ[ q ∈ SA ] (⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ × ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩) ∥₁
          → ∥ Σ[ x ∈ SB ] (⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
                        × ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩) ∥₁
      fwd = PT.map (λ { (q , hq , hψ) →
        g q , (subst ⟨_⟩ (memPath t q δ) hq ,
               subst ⟨_⟩ (agree (suc n) ψ (q ∷ δ)) hψ) })
      bwd : ∥ Σ[ x ∈ SB ] (⟨ fst x ∈ˢ fst (⟦ mapTm g t ⟧ᴮ (map g δ)) ⟩
                        × ⟨ (x ∷ map g δ) ⊨ᴮ mapFo g ψ ⟩) ∥₁
          → ∥ Σ[ q ∈ SA ] (⟨ fst q ∈ˢ fst (⟦ t ⟧ᴬ δ) ⟩ × ⟨ (q ∷ δ) ⊨ᴬ ψ ⟩) ∥₁
      bwd h = PT.map (λ { (q , hq) →
        q , ( subst ⟨_⟩ (sym (memPath t q δ))
                (subst ⟨_⟩ (memRen t (g q) δ) (hq .fst))
            , subst ⟨_⟩ (sym (agree (suc n) ψ (q ∷ δ))) (hq .snd)) })
        (wit n mat δ (PT.map (λ { (x , hx , hψ) →
          x , (subst ⟨_⟩ (sym (memRen t x δ)) hx , hψ) }) h))
```

<!--en-->
## The Tarski-Vaught criterion inside a stage

For a carrier contained in `Lset α`, inclusion into the stage is elementary once existential witnesses can always be chosen from the carrier. The preceding transfer turns exactly this witness property into elementarity.
<!--zh-->
## 阶段内部的 Tarski-Vaught 判据

对于包含在 `Lset α` 中的载体，只要存在见证总能从该载体中选出，载体到阶段的包含就是初等的。上一节的搬运恰好把这一见证性质化为初等性。
<!--ja-->
## 段階内部の Tarski-Vaught 判定条件

`Lset α` に含まれる台では、存在の証人を常にその台から選べれば、段階への包含は初等的になる。前節の移送は、まさにこの証人条件を初等性へ変える。
<!--/-->

```agda
module AtStage (α : S) (ordα : IsOrd α) where

  Ltr : isTransV (Lset α)
  Ltr = layer-trans (Lset-layer α)

  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ Lset α) Ltr
    using ( SM; 𝒮M; _⊨ᵐ_; ⟦_⟧ᵐ; abs₀ )

  SL : Type (ℓ-suc ℓ)
  SL = AbsL.SM

  wL : SWO SL
  wL = orderAt α ordα
```

The equivalence holds at any carrier: the inner world is the restricted
structure, and the bounded cases route through the criterion (Devlin 5.1).

```agda
  module AtM (M : S) (M⊆L : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

    SM : Type (ℓ-suc ℓ)
    SM = Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩

    module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ M))
      using ( module At )
    open SemM.At SM id renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )

    inL : SM → SL
    inL c = fst c , M⊆L (fst c) (snd c)

    Elementary : Type (ℓ-suc (ℓ-suc ℓ))
    Elementary = (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
               → (δ ⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))

    TarskiVaught : Type (ℓ-suc ℓ)
    TarskiVaught = (n : ℕ) (φ : Formula SM (suc n)) (δ : SM ^ n)
                 → ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ φ)) ⟩
                 → ∥ Σ[ q ∈ SM ] ⟨ (inL q ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL φ) ⟩ ∥₁

    private
      lookup-inL : {n : ℕ} (i : Fin n) (δ : SM ^ n)
                 → lookup i (map inL δ) ≡ inL (lookup i δ)
      lookup-inL zero (c ∷ δ) = refl
      lookup-inL (suc i) (c ∷ δ) = lookup-inL i δ

      tm-agree : (n : ℕ) (t : Term SM n) (δ : SM ^ n)
               → fst (⟦ t ⟧ᵐ δ) ≡ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ))
      tm-agree n (con c) δ = refl
      tm-agree n (var i) δ = sym (cong fst (lookup-inL i δ))
```

The stage inclusion is the map; the atoms are congruences of the term
dictionary, and `TarskiVaught` is exactly the witness principle.

```agda
    module Tr = SatTransfer (λ x → x ∈ˢ M) (λ x → x ∈ˢ Lset α)

    TV→elem : TarskiVaught → Elementary
    TV→elem tv = Tr.Along.agree inL
      (λ n t u δ → cong₂ _∈ˢ_ (tm-agree n t δ) (tm-agree n u δ))
      (λ n t u δ → cong₂ _≈ˢ_ (tm-agree n t δ) (tm-agree n u δ))
      tv
```

<!--en-->
## Closing the starting set under least witnesses

The term algebra starts from `X` and repeatedly adds the least witness for each coded existential query. Its values form the Skolem hull: it contains `X`, remains inside `Lset α`, and presents every member by a finite code.
<!--zh-->
## 对最小见证闭合起始集合

项代数从 `X` 出发，并为每个编码的存在查询反复加入最小见证。它的值构成 Skolem 壳：该壳包含 `X`，仍位于 `Lset α` 之内，而且每个成员都由有限码呈现。
<!--ja-->
## 始集合を最小の証人について閉じる

項代数は `X` から始め、符号化された各存在問いに対する最小の証人を繰り返し加える。その値が Skolem 包をなし、`X` を含み、`Lset α` の内部にとどまり、各要素を有限なコードで提示する。
<!--/-->

```agda
  module Hull (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
               (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where
```

The junk value: the empty set, a member of every nonempty stage.

```agda
    ∅∈Lsetα : ⟨ ∅ ∈ˢ Lset α ⟩
    ∅∈Lsetα = Lset-in α ∅ ∅ ∅∈α (∅∈𝒟ₒ ∅)

    inStg : ⟪ X ⟫ → SL
    inStg m = ⟪ X ⟫↪ m , X⊆L (⟪ X ⟫↪ m) (member X m)

    module T = TermAlgebra AbsL.𝒮M fst wL (∅ , ∅∈Lsetα) {K = ⟪ X ⟫} inStg
    open T using ( Code; base; val; Hull; inHull )

```

The hull lies in the stage: every code value is a stage member.

```agda
    Hull⊆L : (x : S) → ⟨ x ∈ˢ Hull ⟩ → ⟨ x ∈ˢ Lset α ⟩
    Hull⊆L x x∈H = PT.rec (snd (x ∈ˢ Lset α)) go x∈H
      where
      go : Σ[ c ∈ Code ] (fst (val c) ≡ x) → ⟨ x ∈ˢ Lset α ⟩
      go (c , q) = subst (λ z → ⟨ z ∈ˢ Lset α ⟩) q (snd (val c))
```

Reading the hull's membership back: a member is the value of a code.

```agda
    hull-member : (x : S) → ⟨ x ∈ˢ Hull ⟩
                → ∥ Σ[ c ∈ Code ] (fst (val c) ≡ x) ∥₁
    hull-member x x∈H = x∈H

    val-in-Hull : (c : Code) → ⟨ fst (val c) ∈ˢ Hull ⟩
    val-in-Hull c = inHull c

    module XInM (x : S) (x∈X : ⟨ x ∈ˢ X ⟩) where
      mx : ⟪ X ⟫
      mx = fiber X x∈X .fst

      x≡val : ⟪ X ⟫↪ mx ≡ x
      x≡val = fiber X x∈X .snd

      inM : ⟨ x ∈ˢ Hull ⟩
      inM = subst (λ z → ⟨ z ∈ˢ Hull ⟩) x≡val (inHull (base mx))

    X⊆M : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Hull ⟩
    X⊆M x x∈X = XInM.inM x x∈X
```

<!--en-->
## Satisfaction is invariant under the collapse isomorphism

The Mostowski collapse identifies the hull with a transitive set through a membership-preserving bijection. Induction on formulas shows that satisfaction is unchanged by this isomorphism in either direction.
<!--zh-->
## 满足关系在塌缩同构下不变

Mostowski 塌缩通过保持隶属关系的双射，把 Skolem 壳与一个传递集等同起来。对公式归纳即可证明满足关系沿该同构的两个方向都保持不变。
<!--ja-->
## 充足関係は崩壊同型で不変である

Mostowski 崩壊は、所属を保つ全単射によって Skolem 包を推移的集合と同一視する。論理式についての帰納により、この同型のどちらの向きでも充足関係が変わらないことが分かる。
<!--/-->

```agda
module IsoInv (M : S) (PM : S)
  (p : S → S)
  (p∈ : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ p x ∈ˢ PM ⟩)
  (iso-fwd : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
           → ⟨ y ∈ˢ x ⟩ → ⟨ p y ∈ˢ p x ⟩)
  (iso-bwd : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
           → ⟨ p y ∈ˢ p x ⟩ → ⟨ y ∈ˢ x ⟩)
  (p-inj : (x y : S) (x∈ : ⟨ x ∈ˢ M ⟩) (y∈ : ⟨ y ∈ˢ M ⟩)
          → p x ≡ p y → x ≡ y)
  (surj : (z : S) (z∈ : ⟨ z ∈ˢ PM ⟩)
        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (p y ≡ z)) ∥₁)
  where

  SM : Type (ℓ-suc ℓ)
  SM = Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩

  SPM : Type (ℓ-suc ℓ)
  SPM = Σ[ x ∈ S ] ⟨ x ∈ˢ PM ⟩

  g : SM → SPM
  g m = p (fst m) , p∈ (fst m) (snd m)

  module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ M))
    using ( module At )
  module SemPM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ PM))
    using ( module At )
  open module Mse = SemM.At SM id public renaming ( _⊨_ to _⊨ᵐ_ ; ⟦_⟧ to ⟦_⟧ᵐ )
  open module Pse = SemPM.At SPM id public renaming ( _⊨_ to _⊨ᵖᵐ_ ; ⟦_⟧ to ⟦_⟧ᵖᵐ )

  surj' : (p' : SPM) → ∥ Σ[ q ∈ SM ] (g q ≡ p') ∥₁
  surj' (z , z∈) = PT.map (λ { (y , y∈ , e) →
    (y , y∈) , Σ≡Prop (λ w → (w ∈ˢ PM) .snd) e }) (surj z z∈)

  module Tr = SatTransfer (λ x → x ∈ˢ M) (λ x → x ∈ˢ PM)

  private
    lookup-g : {n : ℕ} (i : Fin n) (δ : SM ^ n)
             → p (fst (lookup i δ)) ≡ fst (lookup i (map g δ))
    lookup-g zero (m ∷ δ) = refl
    lookup-g (suc i) (m ∷ δ) = lookup-g i δ

    tm-agree : {n : ℕ} (t : Term SM n) (δ : SM ^ n)
             → p (fst (⟦ t ⟧ᵐ δ)) ≡ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ))
    tm-agree (con m) δ = refl
    tm-agree (var i) δ = lookup-g i δ
```

The atoms of the collapse: forward by the order isomorphism, backward by its
inverse and injectivity.

```agda
    at∈ : (n : ℕ) (t u : Term SM n) (δ : SM ^ n)
        → (δ ⊨ᵐ (t ∈̇ u)) ≡ (map g δ ⊨ᵖᵐ mapFo g (t ∈̇ u))
    at∈ n t u δ = ⇔toPath
      (λ h → subst (λ z → ⟨ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ∈ˢ z ⟩) (tm-agree u δ)
        (subst (λ z → ⟨ z ∈ˢ p (fst (⟦ u ⟧ᵐ δ)) ⟩) (tm-agree t δ)
          (iso-fwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
            (snd (⟦ t ⟧ᵐ δ)) h)))
      (λ h → iso-bwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
        (snd (⟦ t ⟧ᵐ δ))
        (subst (λ z → ⟨ p (fst (⟦ t ⟧ᵐ δ)) ∈ˢ z ⟩) (sym (tm-agree u δ))
          (subst (λ z → ⟨ z ∈ˢ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ)) ⟩)
            (sym (tm-agree t δ)) h)))

    at≐ : (n : ℕ) (t u : Term SM n) (δ : SM ^ n)
        → (δ ⊨ᵐ (t ≐ u)) ≡ (map g δ ⊨ᵖᵐ mapFo g (t ≐ u))
    at≐ n t u δ = ⇔toPath
      (λ h → subst (λ z → z ≡ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ))) (tm-agree t δ)
        (subst (λ z → p (fst (⟦ t ⟧ᵐ δ)) ≡ z) (tm-agree u δ) (cong p h)))
      (λ h → p-inj (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ)) (snd (⟦ t ⟧ᵐ δ))
        (snd (⟦ u ⟧ᵐ δ))
        (subst (λ z → z ≡ p (fst (⟦ u ⟧ᵐ δ))) (sym (tm-agree t δ))
          (subst (λ z → fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ≡ z)
            (sym (tm-agree u δ)) h)))
```

Surjectivity supplies the witness principle.

```agda
    wit : Tr.Witness g
    wit n ψ δ h = PT.rec squash₁
      (λ { (p' , hp) → PT.map
        (λ { (q , gq≡p) →
          q , subst (λ z → ⟨ (z ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩) (sym gq≡p) hp })
        (surj' p') }) h

  agree : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
        → (δ ⊨ᵐ φ) ≡ (map g δ ⊨ᵖᵐ mapFo g φ)
  agree = Tr.Along.agree g at∈ at≐ wit

  iso-inv : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
          → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩
  iso-inv n φ δ = subst ⟨_⟩ (agree n φ δ)

  iso-inv-bwd : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
              → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
  iso-inv-bwd n φ δ = subst ⟨_⟩ (sym (agree n φ δ))
```

The collapse instance: `M` = the carrier `X`, `PM` = the collapse image `piX`.

```agda
module CollapseIso (X : S) (Xext : isExt X) where
  module C = Collapse X using ( module InjExt; π; πX; πX-intro; πX-member )
  module CI = C.InjExt Xext using ( iso; π-inj )

  PM : S
  PM = C.πX

  p : S → S
  p = C.π

  p∈ : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ p x ∈ˢ PM ⟩
  p∈ = C.πX-intro

  iso-fwd : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
          → ⟨ y ∈ˢ x ⟩ → ⟨ p y ∈ˢ p x ⟩
  iso-fwd x y x∈ y∈ = CI.iso x y x∈ y∈ .fst

  iso-bwd : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
          → ⟨ p y ∈ˢ p x ⟩ → ⟨ y ∈ˢ x ⟩
  iso-bwd x y x∈ y∈ = CI.iso x y x∈ y∈ .snd

  p-inj : (x y : S) (x∈ : ⟨ x ∈ˢ X ⟩) (y∈ : ⟨ y ∈ˢ X ⟩)
        → p x ≡ p y → x ≡ y
  p-inj = CI.π-inj

  surj : (z : S) (z∈ : ⟨ z ∈ˢ PM ⟩)
       → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ X ⟩ × (p y ≡ z)) ∥₁
  surj = C.πX-member

  module I = IsoInv X PM p p∈ iso-fwd iso-bwd p-inj surj
    using ( SM; SPM; g; surj'; iso-inv; iso-inv-bwd; _⊨ᵐ_; _⊨ᵖᵐ_; ⟦_⟧ᵐ; ⟦_⟧ᵖᵐ )
```

<!--en-->
## The Skolem hull is elementary

Every finite environment in the hull has term-algebra codes. If the surrounding stage satisfies an existential formula there, least-witness closure supplies a witness in the hull, and Tarski-Vaught gives elementarity.
<!--zh-->
## Skolem 壳是初等的

壳中的每个有限环境都有项代数的码。若外围阶段在该环境下满足一个存在公式，对最小见证的闭合便在壳中给出见证，于是 Tarski-Vaught 判据推出初等性。
<!--ja-->
## Skolem 包は初等的である

包の各有限環境には項代数のコードがある。周囲の段階がそこで存在論理式を満たせば、最小の証人についての閉性が包の中に証人を与え、Tarski-Vaught の判定条件から初等性が従う。
<!--/-->

Wall 2, placed ([LJ-1.53] probe A). The parameter-to-code relabelling inside
`TV`/`ElemDown` supplies the TarskiVaught instance at every arity through the
term algebra's search closure. `AtM.TV→elem` turns that instance into
`Elementary`, hence `ElemDown`.

The term algebra already accepts a vector of parameters. The hull instance codes
that vector directly, so the TarskiVaught witness needs no syntactic closure of
its free variables.

The hull instance: the codes of the constants of one formula, read off the hull
membership at each call, then the TarskiVaught instance at every arity, and
`ElemDown`.

```agda
module HullElemDown (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα using ( module AbsL; module AtM; module Hull; SL )
  module H = ASt.Hull X X⊆L ∅∈α
    using ( module T; Hull⊆L; hull-member )
  M : S
  M = H.T.Hull
  module A = ASt.AtM M H.Hull⊆L using ( Elementary; SM; module SemM; TV→elem; inL )
  module Mse = A.SemM.At A.SM id using ( _⊨_ )
```

D-30: the consumer needs codes only for a finite environment, not a total
section of `val`. Each code comes from hull membership, and every truncation
stays outside the propositional goal of `tv`.

```agda
  codeOf : (q : A.SM) → ∥ Σ[ c ∈ H.T.Code ] (H.T.val c ≡ A.inL q) ∥₁
  codeOf q = PT.map (λ { (c , e) → c , Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) e })
    (H.hull-member (fst q) (snd q))

  codeEnv : {n : ℕ} (δ : Vec A.SM n)
          → ∥ Σ[ ds ∈ Vec H.T.Code n ]
               (map H.T.val ds ≡ map A.inL δ) ∥₁
  codeEnv [] = ∣ [] , refl ∣₁
  codeEnv (q ∷ δ) = PT.map2
    (λ { (c , ec) (ds , eds) → c ∷ ds , cong₂ _∷_ ec eds })
    (codeOf q) (codeEnv δ)

  inL-++ : {n m : ℕ} (δ : Vec A.SM n) (σ : Vec A.SM m)
          → map A.inL (δ ++ σ) ≡ map A.inL δ ++ map A.inL σ
  inL-++ [] σ = refl
  inL-++ (q ∷ δ) σ = cong (A.inL q ∷_) (inL-++ δ σ)
```

Abstract the formula first. Its finitely many constant occurrences join the
free-variable environment, and that one vector is coded for the term algebra.
The same semantic path reads the abstracted body both into and out of the bare
search closure.

```agda
  tv : (n : ℕ) (ψ : Formula A.SM (suc n)) (δ : Vec A.SM n)
     → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ)) ⟩
     → ∥ Σ[ q ∈ A.SM ]
          ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
  tv n ψ δ h = PT.rec squash₁ takeEnvironment (codeEnv params)
    where
    bodyFo : Formula (⊥* {ℓ}) (suc (n + countFo ψ))
    bodyFo = absFo ψ

    params : Vec A.SM (n + countFo ψ)
    params = δ ++ constantsFo ψ

    takeEnvironment : Σ[ ds ∈ Vec H.T.Code (n + countFo ψ) ]
                        (map H.T.val ds ≡ map A.inL params)
                    → ∥ Σ[ q ∈ A.SM ]
                         ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ
                             (mapFo A.inL ψ) ⟩ ∥₁
    takeEnvironment (ds , eds) = PT.map finish (H.T.closed _ bodyFo ds witness)
      where
      vals-env : H.T.vals ds
               ≡ map A.inL δ ++ map A.inL (constantsFo ψ)
      vals-env = H.T.vals≡map ds ∙ eds ∙ inL-++ δ (constantsFo ψ)

      body-path : (b : ASt.SL)
                → ((b ∷ H.T.vals ds) H.T.⊨₀ bodyFo)
                ≡ ((b ∷ map A.inL δ) ASt.AbsL.⊨ᵐ mapFo A.inL ψ)
      body-path b =
          cong (λ ε → ε H.T.⊨₀ bodyFo) (cong (b ∷_) vals-env)
        ∙ sym (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) ASt.AbsL.𝒮M A.inL ψ
                 (b ∷ map A.inL δ))
        ∙ sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) ASt.AbsL.𝒮M A.inL id ψ
                 (b ∷ map A.inL δ))

      witness : H.T.Sat (n + countFo ψ) bodyFo (H.T.vals ds)
      witness = PT.map (λ { (b , hb) →
        b , subst ⟨_⟩ (sym (body-path b)) hb }) h

      finish : Σ[ a ∈ ASt.SL ]
                 ( ⟨ fst a ∈ˢ M ⟩
                 × ⟨ (a ∷ H.T.vals ds) H.T.⊨₀ bodyFo ⟩ )
             → Σ[ q ∈ A.SM ]
                 ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩
      finish (a , a∈H , ha) = q , sat
        where
        q : A.SM
        q = fst a , a∈H

        q≡a : A.inL q ≡ a
        q≡a = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) refl

        sat : ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩
        sat = subst (λ b → ⟨ (b ∷ map A.inL δ) ASt.AbsL.⊨ᵐ
                                (mapFo A.inL ψ) ⟩)
                (sym q≡a) (subst ⟨_⟩ (body-path a) ha)

  elem : A.Elementary
  elem = A.TV→elem tv
```

<!--en-->
## Reading parameter-free formulas in the ambient universe

With an empty constant domain, a parameter-free formula has the same interpretation under every relabelling. This connects the hull's restricted semantics to the ambient semantics used by condensation.
<!--zh-->
## 在外围宇宙中读取无参公式

常元域为空时，无参公式在每次常元改名下都有相同解释。这把 Skolem 壳的受限语义连接到凝聚所用的外围语义。
<!--ja-->
## パラメータなし論理式を周囲の宇宙で読む

定数領域が空なら、パラメータなし論理式の解釈はどの定数の改名でも変わらない。この事実が Skolem 包の制限された意味論と、凝縮で用いる周囲の意味論を結ぶ。
<!--/-->

The ambient reading of the parameter-free formulas: the full
hierarchy semantics at the empty constant domain.

```agda
module AtP = SemV.At (⊥* {ℓ-suc ℓ}) (λ b → Empty.rec* b) using ( _⊨_ )

_⊨ₚ_ : {n : ℕ} → S ^ n → Formula (⊥* {ℓ-suc ℓ}) n → hProp (ℓ-suc ℓ)
_⊨ₚ_ = AtP._⊨_
```

A parameter-free formula is FIXED by every relabelling: `embed` has
already sent the empty constant domain everywhere, and there is
nothing left for `f` to move.

```agda
embed-map : {ℓ₁ ℓ₂ : Level} {K : Type ℓ₁} {K' : Type ℓ₂} (f : K → K')
            {n : ℕ} (φ : Formula (⊥* {ℓ-suc ℓ}) n)
          → mapFo f (embed φ) ≡ embed φ
embed-map f φ =
    mapFo-comp Empty.rec* f φ
  ∙ cong (λ h → mapFo h φ) (funExt (λ b → Empty.rec* b))
```

Ordinality, as a one-slot Δ₀ formula.  Sealed: its readers are the
two below, and every other consumer reads it through them.

```agda
opaque
  isOrdAt : Formula (⊥* {ℓ-suc ℓ}) 1
  isOrdAt =
    (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero)))))
    ∧̇ (∀̇∈ (var zero) (∀̇∈ (var zero) (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

  Δ₀-isOrdAt : Δ₀ isOrdAt
  Δ₀-isOrdAt =
    δ-∧ (δ-∀∈ (δ-∀∈ δ-∈))
        (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))

module Amb where
  opaque
    unfolding isOrdAt

    isOrdAt-out : (x : S) → ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩ → IsOrd x
    isOrdAt-out x h =
        ( λ {x₁} {y} y∈x₁ x₁∈x → h .fst x₁ x₁∈x y y∈x₁ )
      , ( λ a a∈x {x₁} {y} y∈x₁ x₁∈a → h .snd a a∈x x₁ x₁∈a y y∈x₁ )

    isOrdAt-in : (x : S) → IsOrd x → ⟨ (x ∷ []) ⊨ₚ isOrdAt ⟩
    isOrdAt-in x o =
        ( λ a a∈x b hb → o .fst {a} {b} hb a∈x )
      , ( λ a a∈x b b∈a c hc → o .snd a a∈x {b} {c} hc b∈a )
```

Ordinality of the parameter, as a 3-slot conjunct, `p` at slot 1. Not sealed:
`L.GCH.CondensationTransfer` and `L.GCH.AdequateStages` read its shape.

```agda
isOrd-at-p : Formula (⊥* {ℓ-suc ℓ}) 3
isOrd-at-p =
    (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc (suc zero))))))
  ∧̇ (∀̇∈ (var (suc zero))
      (∀̇∈ (var zero)
        (∀̇∈ (var zero) (var zero ∈̇ var (suc (suc zero))))))

Δ₀-isOrd-at-p : Δ₀ isOrd-at-p
Δ₀-isOrd-at-p = δ-∧ (δ-∀∈ (δ-∀∈ δ-∈)) (δ-∀∈ (δ-∀∈ (δ-∀∈ δ-∈)))
```

The erase of a constant-free formula carries the Delta-0 witness:
erase is a pure syntactic erasure, so the certificate recurses.

```agda
erase-Δ₀ : {m : ℕ} (φ : Formula CS.S m) (p : countFo φ ≡ 0)
         → Δ₀ φ → Δ₀ (Cnt.erase φ p)
erase-Δ₀ (t ∈̇ u) p δ-∈ = δ-∈
erase-Δ₀ (t ≐ u) p δ-≐ = δ-≐
erase-Δ₀ (φ ∧̇ ψ) p (δ-∧ c d) = δ-∧ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ (φ ∨̇ ψ) p (δ-∨ c d) = δ-∨ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ (φ ⇒̇ ψ) p (δ-⇒ c d) = δ-⇒ (erase-Δ₀ φ _ c) (erase-Δ₀ ψ _ d)
erase-Δ₀ ⊥̇ p δ-⊥ = δ-⊥
erase-Δ₀ (∀̇∈ t φ) p (δ-∀∈ c) = δ-∀∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇∈ t φ) p (δ-∃∈ c) = δ-∃∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇ φ) p ()
erase-Δ₀ (∀̇ φ) p ()
```

<!--en-->
## The hull data required by condensation

At `Lset λ`, the hull, its Mostowski collapse, and the collapse image are assembled into one interface. The remaining hypotheses describe closure of the image under levels and coverage of each hull member below the image's ordinals.
<!--zh-->
## 凝聚所需的壳数据

在 `Lset λ` 处，Skolem 壳、它的 Mostowski 塌缩与塌缩像被装入同一个接口。余下假设描述该像对层构造的闭合，以及每个壳成员如何被该像的序数以下的层覆盖。
<!--ja-->
## 凝縮に必要な包のデータ

`Lset λ` において、Skolem 包、その Mostowski 崩壊、崩壊像を一つのインターフェースにまとめる。残る仮定は、像の階層構成に対する閉性と、各包の要素が像の順序数より下の階層に覆われることを述べる。
<!--/-->

The hull of `X` at the stage `Lset λ`, its collapse, and the condensation
theorem at this one instance (D-30: the consumer's shape, not the general
theory). The two transfer hypotheses are Devlin's (h) and (n)-(p): the collapse
is closed under the level construction at its own ordinals, and every hull
member is covered by a level below the collapse's ordinals. [LJ-1.48] measured
the skeleton around them (elementarity, iso-invariance, the level-hood
certificate) at 0.0097 s per line; the level-hood instantiation at the hull is
the priced residue.

```agda
module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩) (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
    using ( module AbsL; module AtM; module Hull; Ltr; SL; wL )

  module H = ASt.Hull X X⊆L ∅∈λ
    using ( module T; module XInM; Hull⊆L; X⊆M; hull-member
          ; val-in-Hull; ∅∈Lsetα; inStg )

  M : S
  M = H.T.Hull

  module C = Collapse M
    using ( module InjExt; π; πX; πX-intro; πX-member; πX-trans; fixes )

  module Condense
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁)
    where
```

Beta = the ordinals of the collapse, separated by the Delta-0 ordinal formula.
This is the L-native supremum (ProbeT261's shape at the transitive carrier).

```agda
    β-sep : Σ[ s ∈ S ]
              (∀ y → (y ∈ˢ s) ≡ ((y ∈ˢ C.πX) ⊓ ((y ∷ []) ⊨ₚ isOrdAt)))
    β-sep = separateFromSmall C.πX (λ y → (y ∷ []) ⊨ₚ isOrdAt)
              (λ y → D0.Δ₀-small Δ₀-isOrdAt (y ∷ []))

    β : S
    β = β-sep .fst

    β-spec : (y : S) → (y ∈ˢ β) ≡ ((y ∈ˢ C.πX) ⊓ ((y ∷ []) ⊨ₚ isOrdAt))
    β-spec = β-sep .snd

    β∈πX : (δ : S) → ⟨ δ ∈ˢ β ⟩ → ⟨ δ ∈ˢ C.πX ⟩
    β∈πX δ δ∈β = subst ⟨_⟩ (β-spec δ) δ∈β .fst

    β-ord : (δ : S) → ⟨ δ ∈ˢ β ⟩ → IsOrd δ
    β-ord δ δ∈β = Amb.isOrdAt-out δ (subst ⟨_⟩ (β-spec δ) δ∈β .snd)

    ord∈β : (δ : S) → ⟨ δ ∈ˢ C.πX ⟩ → IsOrd δ → ⟨ δ ∈ˢ β ⟩
    ord∈β δ δ∈πX oδ = subst ⟨_⟩ (sym (β-spec δ)) (δ∈πX , Amb.isOrdAt-in δ oδ)

    β-isOrd : IsOrd β
    β-isOrd = β-trans , β-mem
      where
      β-trans : isTransV β
      β-trans {x = x} {y = z} z∈x x∈β =
        subst ⟨_⟩ (sym (β-spec z))
          ( C.πX-trans {x = x} {y = z} z∈x (β∈πX x x∈β)
          , Amb.isOrdAt-in z (mem-ord {A = x} (β-ord x x∈β) z z∈x) )
      β-mem : (x : S) → ⟨ x ∈ˢ β ⟩ → isTransV x
      β-mem x x∈β = β-ord x x∈β .fst
```

The transfer's cover lifts from hull members to collapse members once. Both the
limit proof and the reverse inclusion use this same lifted form.

```agda
    covered : (x : S) → ⟨ x ∈ˢ C.πX ⟩
            → ∥ Σ[ γ ∈ S ]
                 (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ x ∈ˢ Lset γ ⟩) ∥₁
    covered x x∈πX = PT.rec squash₁ go (C.πX-member x x∈πX)
      where
      go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ x))
         → ∥ Σ[ γ ∈ S ]
              (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ x ∈ˢ Lset γ ⟩) ∥₁
      go (y , y∈M , e) = PT.map
        (λ { (γ , oγ , γ∈πX , h) →
          γ , oγ , γ∈πX , subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) e h })
        (cover y y∈M)
```

Every ordinal of the collapse is a member of a larger ordinal of the collapse.
This is Devlin's lim(β) step.

```agda
    β-succ : (δ : S) → ⟨ δ ∈ˢ β ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
    β-succ δ δ∈β = PT.map go (covered δ (β∈πX δ δ∈β))
      where
      oδ : IsOrd δ
      oδ = β-ord δ δ∈β
      go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ δ ∈ˢ Lset γ ⟩)
         → Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩)
      go (γ , oγ , γ∈πX , δ∈Lγ) =
        γ , oγ , ord∈Lset→∈ γ oγ δ oδ δ∈Lγ , ord∈β γ γ∈πX oγ
```

The reverse inclusion: every member of the collapse lies in a level below
beta.

```agda
    πX⊆Lβ : (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ x ∈ˢ Lset β ⟩
    πX⊆Lβ x x∈πX = PT.rec (snd (x ∈ˢ Lset β)) go (covered x x∈πX)
      where
      go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ x ∈ˢ Lset γ ⟩)
         → ⟨ x ∈ˢ Lset β ⟩
      go (γ , oγ , γ∈πX , x∈Lγ) =
        Lset-mono {α = β} {β = γ} (ord∈β γ γ∈πX oγ) x∈Lγ
```

The forward inclusion uses the larger ordinal supplied by `β-succ` directly.

```agda
    Lβ⊆πX : (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ C.πX ⟩
    Lβ⊆πX x x∈Lβ = PT.rec (snd (x ∈ˢ C.πX)) go (Lset-out β x x∈Lβ)
      where
      go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
         → ⟨ x ∈ˢ C.πX ⟩
      go (δ , δ∈β , x∈𝒟ₒδ) = PT.rec (snd (x ∈ˢ C.πX)) liftStage (β-succ δ δ∈β)
        where
        liftStage : Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩)
             → ⟨ x ∈ˢ C.πX ⟩
        liftStage (γ , oγ , δ∈γ , γ∈β) =
          C.πX-trans {x = Lset γ} {y = x}
            (Lset-in γ δ x δ∈γ x∈𝒟ₒδ)
            (levelIn γ oγ (β∈πX γ γ∈β))
```

The equality: the collapse is the level at beta.

```agda
    ext : C.πX ≡ Lset β
    ext = extensionality C.πX (Lset β) (sub , sup)
      where
      sub : (x : S) → ⟨ x ∈ₛ C.πX ⟩ → ⟨ x ∈ₛ Lset β ⟩
      sub x x∈ₛπX = ∈∈ₛ {a = x} {b = Lset β} .fst
        (πX⊆Lβ x (∈∈ₛ {a = x} {b = C.πX} .snd x∈ₛπX))
      sup : (x : S) → ⟨ x ∈ₛ Lset β ⟩ → ⟨ x ∈ₛ C.πX ⟩
      sup x x∈ₛLβ = ∈∈ₛ {a = x} {b = C.πX} .fst
        (Lβ⊆πX x (∈∈ₛ {a = x} {b = Lset β} .snd x∈ₛLβ))

    condenses : Σ[ γ ∈ S ] (IsOrd γ × (C.πX ≡ Lset γ))
    condenses = β , β-isOrd , ext
```

The generator `Lset α ∪ {x}` and its stage facts: `x` is a member, the generator
lies in the stage, the generator is transitive when `x` is a subset of the
stage, and the empty set lies in the limit index.

```agda
module UnionKit (α lam x : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (α∈λ : ⟨ α ∈ˢ lam ⟩) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  X : S
  X = Lset α ∪ ⁅ x ⁆s
```

The union membership of a singleton member.

```agda
  x∈sgl : ⟨ x ∈ₛ ⁅ x ⁆s ⟩
  x∈sgl = SetPackage.classification (SingletonPackage x) x .snd refl

  x∈X : ⟨ x ∈ˢ X ⟩
  x∈X = cup-inr (Lset α) ⁅ x ⁆s x (∈∈ₛ {a = x} {b = ⁅ x ⁆s} .snd x∈sgl)

  Lα∈X : (z : S) → ⟨ z ∈ˢ Lset α ⟩ → ⟨ z ∈ˢ X ⟩
  Lα∈X = cup-inl (Lset α) ⁅ x ⁆s

  sgl≡ : (z : S) → ⟨ z ∈ˢ ⁅ x ⁆s ⟩ → z ≡ x
  sgl≡ = sgl-out x

  X-mem : (z : S) → ⟨ z ∈ˢ X ⟩
        → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
  X-mem = cup-out (Lset α) ⁅ x ⁆s

  X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩
  X⊆Lλ z z∈X = PT.rec (snd (z ∈ˢ Lset lam)) go (X-mem z z∈X)
    where
    go : (⟨ z ∈ˢ Lset α ⟩ ⊎ ⟨ z ∈ˢ ⁅ x ⁆s ⟩) → ⟨ z ∈ˢ Lset lam ⟩
    go (inl z∈Lα) = Lset-mono {α = lam} {β = α} α∈λ z∈Lα
    go (inr z∈sgl) = subst (λ u → ⟨ u ∈ˢ Lset lam ⟩) (sym (sgl≡ z z∈sgl)) x∈Lλ

  Xtr : isTransV X
  Xtr {x = a} {y = b} b∈a a∈X = PT.rec (snd (b ∈ˢ X)) go (X-mem a a∈X)
    where
    go : (⟨ a ∈ˢ Lset α ⟩ ⊎ ⟨ a ∈ˢ ⁅ x ⁆s ⟩) → ⟨ b ∈ˢ X ⟩
    go (inl a∈Lα) = Lα∈X b (layer-trans (Lset-layer α) b∈a a∈Lα)
    go (inr a∈sgl) = Lα∈X b (x⊆Lα b
      (subst (λ u → ⟨ b ∈ˢ u ⟩) (sgl≡ a a∈sgl) b∈a))
```

1 = `sucV ∅` lies in the infinite ordinal alpha, and the empty set lies in the
limit index.

```agda
  one∈α : ⟨ sucV ∅ ∈ˢ α ⟩
  one∈α = Sum.rec
      (λ α∈ω → Empty.rec (α∉ω α∈ω))
      (Sum.rec (λ α≡ω → subst (λ w → ⟨ sucV ∅ ∈ˢ w ⟩) (sym α≡ω) (#∈ω 1))
               (λ ω∈α → ordα .fst (#∈ω 1) ω∈α))
      (ord-tri α ordα ω ω-ord)

  ∅∈Lset1 : ⟨ ∅ ∈ˢ Lset (sucV ∅) ⟩
  ∅∈Lset1 = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Lset-suc ∅)) (∅∈𝒟ₒ ∅)

  ∅∈Lλ : ⟨ ∅ ∈ˢ Lset lam ⟩
  ∅∈Lλ = Lset-mono {α = lam} {β = α} α∈λ
    (Lset-mono {α = α} {β = sucV ∅} one∈α ∅∈Lset1)

  ∅∈λ : ⟨ ∅ ∈ˢ lam ⟩
  ∅∈λ = subst (λ w → ⟨ w ∈ˢ lam ⟩) (rank-fix ∅ ∅-ord)
    (rank-Lset lam ordλ ∅ ∅∈Lλ)
```

The hull is extensional (the `Mext` hypothesis of the collapse iso). Two hull
members that agree on the hull's memberships differ nowhere: a global difference
witness `z ∈ x \ y` satisfies the formula "`v ∈ x ∧ v ∉ y`" in the stage.
Elementarity brings a witness into the hull, where the agreement hypothesis
refutes it. The classical steps are the two directions of extensionality
contrapositive and the difference-witness extraction, each one LEM on a
proposition.

```agda
module HullExt (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
  (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα using ( module AbsL; module AtM; module Hull; SL )
  module H = ASt.Hull X X⊆L ∅∈α using ( module T; Hull⊆L )
  module A = ASt.AtM H.T.Hull H.Hull⊆L using ( SM; inL; module SemM )
  module E = HullElemDown α ordα X X⊆L ∅∈α using ( elem )
  module Mse = A.SemM.At A.SM id using ( _⊨_ )

  M : S
  M = H.T.Hull
```

The symmetric difference, at the levels the hull speaks.

```agda
  Different : S → S → S → Type (ℓ-suc ℓ)
  Different x y z = (z ∈ᵗ x × (z ∈ᵗ y → Empty.⊥))
                  ⊎ (z ∈ᵗ y × (z ∈ᵗ x → Empty.⊥))
```

Unequal sets have a point in their symmetric difference, classically.

```agda
  different : (x y : S) → (x ≡ y → Empty.⊥) → ∥ Σ[ z ∈ S ] Different x y z ∥₁
  different x y nxy = go (lem P)
    where
    P : hProp (ℓ-suc ℓ)
    P = ∥ Σ[ z ∈ S ] Different x y z ∥₁ , squash₁
    go : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → ⟨ P ⟩
    go (inl p) = p
    go (inr np) = Empty.rec (nxy (extensionalV (λ z → ⇔toPath (fwd z) (bwd z))))
      where
      fwd : (z : S) → z ∈ᵗ x → z ∈ᵗ y
      fwd z zx = Sum.rec (λ zy → zy)
        (λ nzy → Empty.rec (np ∣ z , inl (zx , nzy) ∣₁)) (lem (z ∈ˢ y))
      bwd : (z : S) → z ∈ᵗ y → z ∈ᵗ x
      bwd z zy = Sum.rec (λ zx → zx)
        (λ nzx → Empty.rec (np ∣ z , inr (zy , nzx) ∣₁)) (lem (z ∈ˢ x))
```

The difference formula over two hull members.

```agda
  φ : A.SM → A.SM → Formula A.SM 1
  φ x y = ((var zero ∈̇ con x) ∧̇ (¬̇ (var zero ∈̇ con y)))
        ∨̇ ((var zero ∈̇ con y) ∧̇ (¬̇ (var zero ∈̇ con x)))
```

The stage satisfaction from a global difference witness.

```agda
  outer : (u v : S) (u∈M : u ∈ᵗ M) (v∈M : v ∈ᵗ M)
        → (z : S) → Different u v z
        → ∥ Σ[ a ∈ ASt.SL ]
            ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo A.inL (φ (u , u∈M) (v , v∈M))) ⟩ ∥₁
  outer u v u∈M v∈M z d = ∣ a , ∣ objectDifferent d ∣₁ ∣₁
    where
    objectDifferent = Sum.map
      (λ (zu , nzv) → zu , λ zv → lift (nzv zv))
      (λ (zv , nzu) → zv , λ zu → lift (nzu zu))
    z∈L : ⟨ z ∈ˢ Lset α ⟩
    z∈L = Sum.rec
      (λ (zx , _) → layer-trans (Lset-layer α) zx (H.Hull⊆L u u∈M))
      (λ (zv , _) → layer-trans (Lset-layer α) zv (H.Hull⊆L v v∈M)) d
    a : ASt.SL
    a = z , z∈L
```

Elementarity brings the difference witness into the hull, and the agreement
hypothesis refutes it.

```agda
  refute : (x y : S) (x∈M : x ∈ᵗ M) (y∈M : y ∈ᵗ M)
         → (ag1 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
         → (ag2 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩)
         → (x ≡ y → Empty.⊥) → Empty.⊥
  refute x y x∈M y∈M ag1 ag2 nxy = PT.rec Empty.isProp⊥ diff (different x y nxy)
    where
    xS : A.SM
    xS = x , x∈M
    yS : A.SM
    yS = y , y∈M

    diff : Σ[ z ∈ S ] Different x y z → Empty.⊥
    diff (z , d) = PT.rec Empty.isProp⊥ inside h
      where
      h : ⟨ [] Mse.⊨ (∃̇ (φ xS yS)) ⟩
      h = subst ⟨_⟩ (sym (E.elem 0 (∃̇ (φ xS yS)) []))
        (outer x y x∈M y∈M z d)
      inside : Σ[ b ∈ A.SM ] ⟨ (b ∷ []) Mse.⊨ φ xS yS ⟩ → Empty.⊥
      inside (b , q) = PT.rec Empty.isProp⊥ cases q
        where
        cases : (⟨ fst b ∈ˢ x ⟩ × (⟨ fst b ∈ˢ y ⟩ → Lift Empty.⊥))
              ⊎ (⟨ fst b ∈ˢ y ⟩ × (⟨ fst b ∈ˢ x ⟩ → Lift Empty.⊥))
              → Empty.⊥
        cases (inl (bx , nby)) = lower (nby (ag1 (fst b) (snd b) bx))
        cases (inr (by , nbx)) = lower (nbx (ag2 (fst b) (snd b) by))

  hullExt : isExt M
  hullExt x y x∈M y∈M ag1 ag2 =
    Sum.rec (λ p → p) (λ np → Empty.rec (bad np))
      (lem ((x ≡ y) , isSetS x y))
    where
    bad : (x ≡ y → Empty.⊥) → Empty.⊥
    bad = refute x y x∈M y∈M ag1 ag2
```

<!--en-->
## Carrying bounded formulas across the collapse

A bounded formula has the same truth value in a transitive substructure as in the ambient universe. Combining this absoluteness with collapse transfer gives the reading used by condensation.
<!--zh-->
## 沿塌缩搬运有界公式

有界公式在传递子结构中与在外围宇宙中具有相同真值。把这一绝对性与塌缩搬运结合起来，就得到凝聚所需的读法。
<!--ja-->
## 崩壊を通して有界論理式を移す

有界論理式は、推移的部分構造でも周囲の宇宙でも同じ真理値をもつ。この絶対性を崩壊による移送と組み合わせると、凝縮で使う読み方が得られる。
<!--/-->

Delta-0 formulas can be read from any transitive substructure in the ambient
universe.

```agda
module Unpack (U : S) (Utr : isTrans U) where

  module Ab = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ U) Utr using (SM; abs₀; _⊨ᵐ_)

  read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Ab.SM ^ n)
       → (δ Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
  read {n} {φ} dφ δ =
      Ab.abs₀ (mapΔ₀ Empty.rec* dφ) δ
    ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = Ab.SM} fst φ (map fst δ)
    ∙ cong (λ ι → SemV.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
           (funExt (λ b → Empty.rec* b))
```

The frame packages this reading with the hull stage and its collapse transfer.

```agda
module Frame (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using (module ASt; module C; module Condense; module H; M)
  module ASt = HS.ASt using (module AbsL; module AtM; Ltr; SL)
  module A = ASt.AtM HS.M HS.H.Hull⊆L using (Elementary; SM; module SemM; inL)
```

Section 2. The carry. Ambient truth at hull members becomes ambient truth at
their collapse values: (1) down into the hull by `elem`, (2) across by the
collapse iso `iso-inv`, (3) out of the collapse by Δ₀ absoluteness at the
transitive range `πX`.

```agda
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ using (hullExt)

  Mext : isExt HS.M
  Mext = HE.hullExt

  module Carry (elem : A.Elementary) where

    module CIso = CollapseIso HS.M Mext using (module I; iso-fwd; iso-bwd)
    module TL = Unpack (Lset lam) ASt.Ltr using (read)
    module Tπ = Unpack HS.C.πX HS.C.πX-trans using (module Ab; read)

    atL : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : ASt.SL ^ n)
        → (δ ASt.AbsL.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atL dφ δ = TL.read dφ δ

    atπ : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Tπ.Ab.SM ^ n)
        → (δ Tπ.Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atπ dφ δ = Tπ.read dφ δ

    atM : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
        → (δ CIso.I.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
    atM {n} {φ} dφ δ =
        elem n (embed φ) δ
      ∙ cong (λ ψ → map A.inL δ ASt.AbsL.⊨ᵐ ψ) (embed-map A.inL φ)
      ∙ atL dφ (map A.inL δ)
      ∙ cong (λ γ → γ ⊨ₚ φ) (map-inL-fst δ)
      where
      map-inL-fst : {m : ℕ} (γ : A.SM ^ m)
                  → map fst (map A.inL γ) ≡ map fst γ
      map-inL-fst [] = refl
      map-inL-fst (q ∷ γ) = cong (fst q ∷_) (map-inL-fst γ)
```

The carry itself.

```agda
    push : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
         → ⟨ map fst δ ⊨ₚ φ ⟩
         → ⟨ map fst (map CIso.I.g δ) ⊨ₚ φ ⟩
    push {n} {φ} dφ δ h =
      subst ⟨_⟩ (atπ dφ (map CIso.I.g δ))
        (subst (λ ψ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ ψ ⟩)
               (embed-map CIso.I.g φ)
               (CIso.I.iso-inv n (embed φ) δ (subst ⟨_⟩ (sym (atM dφ δ)) h)))
```
