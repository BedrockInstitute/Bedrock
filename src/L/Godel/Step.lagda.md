# The step order, at the term names

<!--en-->
This chapter is deliberate scaffolding, and says so. The step of the choice
construction builds the order on a successor stage from an order below by
comparing least names, and its spine does not care which naming chapter it
consumes: the code below is line for line the step chapter's, with one import
re-pointed from the internalized names to the term names. It exists so that
both routes stay green side by side while the term route's internal side is
built against it; at the final rewire one of the two copies retires, and the
surviving step keeps the term names. The mathematics is narrated once, in the
step chapter; this copy is the same narration's object at the other naming,
not a second narration.
<!--zh-->
本章是有意为之的脚手架，并且明说。选取构造的步进以比较最小名字的方式从下方的序造出后继阶段上的序，而其骨架并不在乎消费哪一章的名字：下方的代码与步进章逐行同源，唯一的改动是把一个导入从内化名字改指向项名字。它的存在是为了让两条路线并排保持全绿，同时项路线的内部侧对着它陈述；到最终重接线时两份之一退役，幸存的步进保留项名字。数学只在步进章叙述一次；这一份是同一叙述在另一套名字处的对象，不是第二次叙述。
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Godel.Step {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl; ∈-induction; ∈-induction-compute )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( IsOrd; isPropIsOrd; isL; Lset; Lset-out; Lset-mono; Lset→isL; 𝒟ₒ )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem; stage-earliest )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Choice.Stage {ℓ} lem using ( IsPredOf; isPropPredOf )
open import L.Choice.Finite {ℓ} lem using ( Tri-map )
open import L.Godel.Name {ℓ} lem using ( module Naming )
open import L.WellOrder.Base {ℓ-suc ℓ}
  using ( Tri; lt; eq; gt; SWO; IsLeast; isPropLeastOf )

open import Cubical.Foundations.Prelude using ( J; PathP; subst2 )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Embedding using ( isEmbedding→Inj )
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; isEmb⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ
```

```agda
private
  decideSuc : (x : S) (p : ⟨ isL x ⟩) (δ : S) → IsOrd δ
            → ⟨ x ∈ˢ Lset (sucV δ) ⟩
            → ⟨ sucV δ ∈ˢ stage x p ⟩ ⊎ (sucV δ ≡ stage x p)
            → sucV δ ≡ stage x p
  decideSuc x p δ ordδ m (inl s∈) =
    Empty.rec (stage-earliest x p (sucV δ) (suc-ord ordδ) m s∈)
  decideSuc x p δ ordδ m (inr e) = e

  atCarve : (x : S) (p : ⟨ isL x ⟩)
          → Σ[ δ ∈ S ] (⟨ δ ∈ˢ stage x p ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
          → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
  atCarve x p (δ , (δ∈ , x∈)) = δ , (ordδ , suc≡)
    where
    ordδ : IsOrd δ
    ordδ = mem-ord {A = stage x p} (stage-ord x p) δ δ∈
    atSuc : ⟨ x ∈ˢ Lset (sucV δ) ⟩
    atSuc = subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈
    suc≡ : sucV δ ≡ stage x p
    suc≡ = decideSuc x p δ ordδ atSuc
      (suc∈or≡ δ (stage x p) ordδ (stage-ord x p) δ∈)

theCarve : (x : S) (p : ⟨ isL x ⟩) → Σ[ δ ∈ S ] IsPredOf (stage x p) δ
theCarve x p = PT.rec (isPropPredOf (stage x p)) (atCarve x p)
  (Lset-out (stage x p) x (stage-mem x p))

opaque
  birth : (x : S) → ⟨ isL x ⟩ → S
  birth x p = theCarve x p .fst

opaque
  unfolding birth
  birth-ord : (x : S) (p : ⟨ isL x ⟩) → IsOrd (birth x p)
  birth-ord x p = theCarve x p .snd .fst

  birth-suc : (x : S) (p : ⟨ isL x ⟩) → sucV (birth x p) ≡ stage x p
  birth-suc x p = theCarve x p .snd .snd
```

```agda
birth-mem : (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset (sucV (birth x p)) ⟩
birth-mem x p =
  subst (λ w → ⟨ x ∈ˢ Lset w ⟩) (sym (birth-suc x p)) (stage-mem x p)

birth-stage : (x : S) (p : ⟨ isL x ⟩) → ⟨ birth x p ∈ˢ stage x p ⟩
birth-stage x p =
  subst (λ w → ⟨ birth x p ∈ˢ w ⟩) (birth-suc x p) (self∈sucV (birth x p))

birth-proof : (x : S) (p q : ⟨ isL x ⟩) → birth x p ≡ birth x q
birth-proof x p q = cong (birth x) (snd (isL x) p q)

private
  decideIn : (γ x : S) → IsOrd γ → (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset γ ⟩
           → ⟨ γ ∈ˢ stage x p ⟩ ⊎ ((γ ≡ stage x p) ⊎ ⟨ stage x p ∈ˢ γ ⟩)
           → ⟨ birth x p ∈ˢ γ ⟩
  decideIn γ x ordγ p h (inl γ∈) = Empty.rec (stage-earliest x p γ ordγ h γ∈)
  decideIn γ x ordγ p h (inr (inl e)) =
    subst (λ w → ⟨ birth x p ∈ˢ w ⟩) (sym e) (birth-stage x p)
  decideIn γ x ordγ p h (inr (inr s∈)) = ordγ .fst (birth-stage x p) s∈

birth-in : (γ : S) → IsOrd γ → (x : S) (p : ⟨ isL x ⟩) → ⟨ x ∈ˢ Lset γ ⟩
         → ⟨ birth x p ∈ˢ γ ⟩
birth-in γ ordγ x p h =
  decideIn γ x ordγ p h (ord-tri γ ordγ (stage x p) (stage-ord x p))
```

```agda
Mem : S → Type (ℓ-suc ℓ)
Mem A = Σ[ x ∈ S ] ⟨ x ∈ˢ A ⟩

module _ {ℓc : Level} {A : Type ℓc} (w : SWO A) where
  open SWO w using () renaming ( _<∙_ to _<ʷ_ )

  relOf : A → A → Type (ℓ-suc ℓ)
  relOf a b = a <ʷ b

module _ {ℓb ℓc : Level} (B : Type ℓb) (C : Type ℓc) (w : SWO C)
         (f : B → C) (finj : (u v : B) → f u ≡ f v → u ≡ v) where
  open SWO w using () renaming
    ( _<∙_ to _<ᶜ_ ; tri∙ to triᶜ ; irr∙ to irrᶜ
    ; trans∙ to transᶜ ; wf∙ to wfᶜ )

  private
    _<ᵇ_ : B → B → Type (ℓ-suc ℓ)
    u <ᵇ v = f u <ᶜ f v

    pullTri : (u v : B) → Tri (u <ᵇ v) (u ≡ v) (v <ᵇ u)
    pullTri u v = Tri-map id (finj u v) id (triᶜ (f u) (f v))

    pullAcc : (u : B) → Acc _<ᶜ_ (f u) → Acc _<ᵇ_ u
    pullAcc u (acc r) = acc (λ v h → pullAcc v (r (f v) h))

  pullOrder : SWO B
  pullOrder = record
    { _<∙_   = _<ᵇ_
    ; tri∙   = pullTri
    ; irr∙   = λ u h → irrᶜ (f u) h
    ; trans∙ = λ u v z → transᶜ (f u) (f v) (f z)
    ; wf∙    = λ u → pullAcc u (wfᶜ (f u)) }
```

```agda
memOf : (A : S) (m : ⟪ A ⟫) → ⟨ ⟪ A ⟫↪ m ∈ˢ A ⟩
memOf A m = ∈∈ₛ {a = ⟪ A ⟫↪ m} {b = A} .snd (∈ₛ⟪ A ⟫↪ m)

carry : (A : S) → SWO (Mem A) → SWO ⟪ A ⟫
carry A w = pullOrder ⟪ A ⟫ (Mem A) w (λ m → ⟪ A ⟫↪ m , memOf A m) inj
  where
  inj : (u v : ⟪ A ⟫)
      → _≡_ {A = Mem A} (⟪ A ⟫↪ u , memOf A u) (⟪ A ⟫↪ v , memOf A v) → u ≡ v
  inj u v q = isEmbedding→Inj isEmb⟪ A ⟫↪ u v (cong fst q)

```

```agda
New : S → Type (ℓ-suc ℓ)
New δ = Mem (Lset (sucV δ))

```

```agda
module _ (δ : S) (w : SWO ⟪ Lset δ ⟫) where
  private
    module NM = Naming (Lset δ) w

  denotesAt : S → NM.Name → hProp (ℓ-suc ℓ)
  denotesAt x n = (NM.denote n ≡ x) , setIsSet (NM.denote n) x

  private
    denotes : New δ → NM.Name → hProp (ℓ-suc ℓ)
    denotes a = denotesAt (a .fst)

    hasName : (a : New δ) → ∥ Σ[ n ∈ NM.Name ] ⟨ denotes a n ⟩ ∥₁
    hasName a = NM.names-complete (a .fst)
      (subst (λ v → ⟨ a .fst ∈ˢ v ⟩) (Lset-suc δ) (a .snd))

    leastOfNew : (a : New δ)
               → Σ[ n ∈ NM.Name ] IsLeast NM.nameOrder (denotes a) n
    leastOfNew a = NM.leastName (denotes a) (hasName a)

    theName : New δ → NM.Name
    theName a = leastOfNew a .fst

    theName-denote : (a : New δ) → NM.denote (theName a) ≡ a .fst
    theName-denote a = leastOfNew a .snd .fst

    nameInj : (u v : New δ) → theName u ≡ theName v → u ≡ v
    nameInj u v q = Σ≡Prop (λ x → snd (x ∈ˢ Lset (sucV δ)))
      (sym (theName-denote u) ∙ cong NM.denote q ∙ theName-denote v)

  byName : SWO (New δ)
  byName = pullOrder (New δ) NM.Name NM.nameOrder theName nameInj
```

```agda
  IsLeastName : NM.Name → S → Type (ℓ-suc ℓ)
  IsLeastName t x = IsLeast NM.nameOrder (denotesAt x) t

  leastNameOf : (a : New δ) → Σ[ t ∈ NM.Name ] IsLeastName t (fst a)
  leastNameOf a = leastOfNew a

  private
    pin : (c : New δ) (t : NM.Name) → IsLeastName t (fst c) → theName c ≡ t
    pin c t h = cong fst
      (isPropLeastOf NM.nameOrder (denotes c) (leastOfNew c) (t , h))

    byName-least : (a b : New δ) (t₁ t₂ : NM.Name)
                 → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                 → relOf byName a b ≡ NM._≺ₙ_ t₁ t₂
    byName-least a b t₁ t₂ h₁ h₂ = cong₂ NM._≺ₙ_ (pin a t₁ h₁) (pin b t₂ h₂)

```

```agda
  opaque
    stepAt : SWO (New δ)
    stepAt = byName
```

```agda
  opaque
    unfolding stepAt

    stepAt-fill : (a b : New δ) (t₁ t₂ : NM.Name)
                → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                → NM._≺ₙ_ t₁ t₂ → relOf stepAt a b
    stepAt-fill a b t₁ t₂ h₁ h₂ =
      transport (sym (byName-least a b t₁ t₂ h₁ h₂))

    stepAt-read : (a b : New δ) (t₁ t₂ : NM.Name)
                → IsLeastName t₁ (fst a) → IsLeastName t₂ (fst b)
                → relOf stepAt a b → NM._≺ₙ_ t₁ t₂
    stepAt-read a b t₁ t₂ h₁ h₂ =
      transport (byName-least a b t₁ t₂ h₁ h₂)
```

```agda
Under : (δ : S) → SWO (New δ) → S → S → Type (ℓ-suc ℓ)
Under δ v x y = Σ[ hx ∈ ⟨ x ∈ˢ Lset (sucV δ) ⟩ ]
                Σ[ hy ∈ ⟨ y ∈ˢ Lset (sucV δ) ⟩ ]
                relOf v (x , hx) (y , hy)

under-at : (δ : S) (v : SWO (New δ)) (x y : S)
           (hx : ⟨ x ∈ˢ Lset (sucV δ) ⟩) (hy : ⟨ y ∈ˢ Lset (sucV δ) ⟩)
         → Under δ v x y → relOf v (x , hx) (y , hy)
under-at δ v x y hx hy (kx , ky , h) =
  subst2 (λ p q → relOf v (x , p) (y , q))
    (snd (x ∈ˢ Lset (sucV δ)) kx hx) (snd (y ∈ˢ Lset (sucV δ)) ky hy) h
```

```agda
module Family (γ : S)
              (IH : (δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → SWO (Mem (Lset δ)))
              (ordγ : IsOrd γ) where
  private
    Member : Type (ℓ-suc ℓ)
    Member = Mem (Lset γ)

    memberL : (a : Member) → ⟨ isL (a .fst) ⟩
    memberL a = Lset→isL γ ordγ (a .fst) (a .snd)

    newIn : (a : Member) → ⟨ a .fst ∈ˢ Lset (sucV (birth (a .fst) (memberL a))) ⟩
    newIn a = birth-mem (a .fst) (memberL a)

  bornAt : Member → Mem γ
  bornAt a = birth (a .fst) (memberL a)
           , birth-in γ ordγ (a .fst) (memberL a) (a .snd)

  stepIn : (d : Mem γ) → SWO (New (d .fst))
  stepIn d = stepAt (d .fst) (carry (Lset (d .fst))
    (IH (d .fst) (d .snd) (mem-ord {A = γ} ordγ (d .fst) (d .snd))))

  UnderAt : (d : Mem γ) → Member → Member → Type (ℓ-suc ℓ)
  UnderAt d a b = Under (d .fst) (stepIn d) (a .fst) (b .fst)

  _≺_ : Member → Member → Type (ℓ-suc ℓ)
  a ≺ b = ⟨ bornAt a .fst ∈ˢ bornAt b .fst ⟩
        ⊎ ((bornAt b .fst ≡ bornAt a .fst) × UnderAt (bornAt a) a b)

  private
    packBirth : (d z : Mem γ) → d .fst ≡ z .fst → d ≡ z
    packBirth d z = Σ≡Prop (λ v → snd (v ∈ˢ γ))
```

```agda
  private
    ≺-irr : (a : Member) → a ≺ a → Empty.⊥
    ≺-irr a (inl h) = ∈-irrefl (bornAt a .fst) h
    ≺-irr a (inr (_ , u)) =
      SWO.irr∙ (stepIn (bornAt a)) (a .fst , newIn a)
        (under-at (bornAt a .fst) (stepIn (bornAt a)) (a .fst) (a .fst)
          (newIn a) (newIn a) u)

    ≺-trans : (a b c : Member) → a ≺ b → b ≺ c → a ≺ c
    ≺-trans a b c (inl h) (inl k) =
      inl (birth-ord (c .fst) (memberL c) .fst h k)
    ≺-trans a b c (inl h) (inr (e , _)) =
      inl (subst (λ v → ⟨ bornAt a .fst ∈ˢ v ⟩) (sym e) h)
    ≺-trans a b c (inr (e , _)) (inl k) =
      inl (subst (λ v → ⟨ v ∈ˢ bornAt c .fst ⟩) e k)
    ≺-trans a b c (inr (e , u)) (inr (eb , v)) = inr (eb ∙ e , joined)
      where
      d : Mem γ
      d = bornAt a
      moved : UnderAt d b c
      moved = subst (λ z → UnderAt z b c) (packBirth (bornAt b) d e) v
      joined : UnderAt d a c
      joined = u .fst , (moved .snd .fst
        , SWO.trans∙ (stepIn d) (a .fst , u .fst) (b .fst , moved .fst)
            (c .fst , moved .snd .fst)
            (under-at (d .fst) (stepIn d) (a .fst) (b .fst)
              (u .fst) (moved .fst) u)
            (under-at (d .fst) (stepIn d) (b .fst) (c .fst)
              (moved .fst) (moved .snd .fst) moved))

    ≺-tri : (a b : Member) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
    ≺-tri a b = byBirth (ord-tri (bornAt a .fst) (birth-ord (a .fst) (memberL a))
                                 (bornAt b .fst) (birth-ord (b .fst) (memberL b)))
      where
      byBirth : ⟨ bornAt a .fst ∈ˢ bornAt b .fst ⟩
              ⊎ ((bornAt a .fst ≡ bornAt b .fst) ⊎ ⟨ bornAt b .fst ∈ˢ bornAt a .fst ⟩)
              → Tri (a ≺ b) (a ≡ b) (b ≺ a)
      byBirth (inl h)       = lt (inl h)
      byBirth (inr (inr h)) = gt (inl h)
      byBirth (inr (inl e)) =
        bySteps (SWO.tri∙ (stepIn (bornAt a)) (a .fst , ha) (b .fst , hb))
        where
        same : bornAt b .fst ≡ bornAt a .fst
        same = sym e
        ha : ⟨ a .fst ∈ˢ Lset (sucV (bornAt a .fst)) ⟩
        ha = newIn a
        hb : ⟨ b .fst ∈ˢ Lset (sucV (bornAt a .fst)) ⟩
        hb = subst (λ v → ⟨ b .fst ∈ˢ Lset (sucV v) ⟩) (sym e) (newIn b)
        bySteps : Tri (relOf (stepIn (bornAt a)) (a .fst , ha) (b .fst , hb))
                      ((a .fst , ha) ≡ (b .fst , hb))
                      (relOf (stepIn (bornAt a)) (b .fst , hb) (a .fst , ha))
                → Tri (a ≺ b) (a ≡ b) (b ≺ a)
        bySteps (lt h) = lt (inr (same , (ha , hb , h)))
        bySteps (eq q) = eq (Σ≡Prop (λ v → snd (v ∈ˢ Lset γ)) (cong fst q))
        bySteps (gt h) = gt (inr (sym same
          , subst (λ z → UnderAt z b a)
              (packBirth (bornAt a) (bornAt b) (sym same)) (hb , ha , h)))
```

```agda
  private
    accInside : (d : Mem γ)
              → ((z : Mem γ) → ⟨ z .fst ∈ˢ d .fst ⟩
                 → (b : Member) → bornAt b ≡ z → Acc _≺_ b)
              → (u : New (d .fst)) → Acc (relOf (stepIn d)) u
              → (b : Member) → bornAt b ≡ d → b .fst ≡ u .fst → Acc _≺_ b
    accInside d ih u (acc r) b q qu = acc step
      where
      step : (c : Member) → c ≺ b → Acc _≺_ c
      step c (inl h) = ih (bornAt c)
        (subst (λ v → ⟨ bornAt c .fst ∈ˢ v ⟩) (cong fst q) h) c refl
      step c (inr (eb , v)) =
        accInside d ih (c .fst , hc) (r (c .fst , hc) below) c qc refl
        where
        qc : bornAt c ≡ d
        qc = packBirth (bornAt c) d (sym eb ∙ cong fst q)
        moved : UnderAt d c b
        moved = subst (λ z → UnderAt z c b) qc v
        hc : ⟨ c .fst ∈ˢ Lset (sucV (d .fst)) ⟩
        hc = moved .fst
        below : relOf (stepIn d) (c .fst , hc) u
        below = subst (λ z → relOf (stepIn d) (c .fst , hc) z)
          (Σ≡Prop (λ x → snd (x ∈ˢ Lset (sucV (d .fst)))) qu)
          (under-at (d .fst) (stepIn d) (c .fst) (b .fst)
            hc (moved .snd .fst) moved)

    accByBirth : (δ : S) (i : ⟨ δ ∈ˢ γ ⟩)
               → (b : Member) → bornAt b ≡ (δ , i) → Acc _≺_ b
    accByBirth = ∈-induction {P = Motive} outer
      where
      Motive : S → Type (ℓ-suc ℓ)
      Motive δ = (i : ⟨ δ ∈ˢ γ ⟩) (b : Member) → bornAt b ≡ (δ , i) → Acc _≺_ b
      outer : (δ : S) → ((z : S) → ⟨ z ∈ˢ δ ⟩ → Motive z) → Motive δ
      outer δ ih i b q = accInside (δ , i) inner (b .fst , hb)
        (SWO.wf∙ (stepIn (δ , i)) (b .fst , hb)) b q refl
        where
        hb : ⟨ b .fst ∈ˢ Lset (sucV δ) ⟩
        hb = subst (λ z → ⟨ b .fst ∈ˢ Lset (sucV (z .fst)) ⟩) q (newIn b)
        inner : (z : Mem γ) → ⟨ z .fst ∈ˢ δ ⟩
              → (c : Member) → bornAt c ≡ z → Acc _≺_ c
        inner z h c qz = ih (z .fst) h (z .snd) c qz

    ≺-wf : WellFounded _≺_
    ≺-wf a = accByBirth (bornAt a .fst) (bornAt a .snd) a refl

  famOrder : SWO (Mem (Lset γ))
  famOrder = record
    { _<∙_   = _≺_
    ; tri∙   = ≺-tri
    ; irr∙   = ≺-irr
    ; trans∙ = ≺-trans
    ; wf∙    = ≺-wf }
```

```agda
famStep : (γ : S) → ((δ : S) → ⟨ δ ∈ˢ γ ⟩ → IsOrd δ → SWO (Mem (Lset δ)))
        → IsOrd γ → SWO (Mem (Lset γ))
famStep = Family.famOrder

opaque
  orderAt : (γ : S) → IsOrd γ → SWO (Mem (Lset γ))
  orderAt = ∈-induction famStep

opaque
  unfolding orderAt
  orderAt-step : (γ : S) → orderAt γ ≡ famStep γ (λ δ _ → orderAt δ)
  orderAt-step = ∈-induction-compute famStep

stageOrder : (γ : S) → IsOrd γ → SWO ⟪ Lset γ ⟫
stageOrder γ oγ = carry (Lset γ) (orderAt γ oγ)
```

```agda
private
  stepPath : (δ : S) (o : IsOrd δ) (δ' : S) (e : δ ≡ δ') (o' : IsOrd δ')
           → PathP (λ k → SWO (New (e k)))
               (stepAt δ (carry (Lset δ) (orderAt δ o)))
               (stepAt δ' (carry (Lset δ') (orderAt δ' o')))
  stepPath δ o δ' e o' = J Motive base e o'
    where
    Motive : (z : S) → δ ≡ z → Type (ℓ-suc (ℓ-suc ℓ))
    Motive z ez = (oz : IsOrd z) → PathP (λ k → SWO (New (ez k)))
      (stepAt δ (carry (Lset δ) (orderAt δ o)))
      (stepAt z (carry (Lset z) (orderAt z oz)))
    base : Motive δ refl
    base oz =
      cong (λ q → stepAt δ (carry (Lset δ) (orderAt δ q))) (isPropIsOrd δ o oz)
```

```agda
module _ (γ β : S) (oγ : IsOrd γ) (oβ : IsOrd β) (i : ⟨ γ ∈ˢ β ⟩) where
  private
    module Fγ = Family γ (λ δ _ → orderAt δ) oγ
    module Fβ = Family β (λ δ _ → orderAt δ) oβ
    open Fγ using () renaming ( _≺_ to _≺ᵍ_ ; bornAt to bornγ )
    open Fβ using () renaming ( _≺_ to _≺ᵇ_ ; bornAt to bornβ )

    up : Mem (Lset γ) → Mem (Lset β)
    up a = a .fst , Lset-mono {α = β} {β = γ} i {x = a .fst} (a .snd)

    sameBirth : (a : Mem (Lset γ)) → bornγ a .fst ≡ bornβ (up a) .fst
    sameBirth a = birth-proof (a .fst) _ _

    sameStep : (a : Mem (Lset γ))
             → PathP (λ k → SWO (New (sameBirth a k)))
                 (Fγ.stepIn (bornγ a)) (Fβ.stepIn (bornβ (up a)))
    sameStep a = stepPath (bornγ a .fst) _ (bornβ (up a) .fst) (sameBirth a) _

    agree : (a b : Mem (Lset γ)) → (a ≺ᵍ b) ≡ (up a ≺ᵇ up b)
    agree a b k = ⟨ sameBirth a k ∈ˢ sameBirth b k ⟩
                ⊎ ( (sameBirth b k ≡ sameBirth a k)
                  × Under (sameBirth a k) (sameStep a k) (a .fst) (b .fst) )

    unfoldγ : (a b : Mem (Lset γ)) → relOf (orderAt γ oγ) a b ≡ (a ≺ᵍ b)
    unfoldγ a b = cong (λ z → relOf (z oγ) a b) (orderAt-step γ)

    unfoldβ : (a b : Mem (Lset β)) → relOf (orderAt β oβ) a b ≡ (a ≺ᵇ b)
    unfoldβ a b = cong (λ z → relOf (z oβ) a b) (orderAt-step β)

  endExtension : (a b : Mem (Lset γ))
               → relOf (orderAt γ oγ) a b ≡ relOf (orderAt β oβ) (up a) (up b)
  endExtension a b = unfoldγ a b ∙ agree a b ∙ sym (unfoldβ (up a) (up b))
```
