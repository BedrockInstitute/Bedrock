# The Skolem hull

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Hull {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax
  using ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; Σ₁; δ-∧; δ-≐; δ-∃∈; σ-Δ₀; σ-∃ )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Manipulation.Parameters
  using ( countFo; constantsFo; absFo; ⊨-abs )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm; ⊨-map )
open import FOL.Manipulation.Renaming using ( renameTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ )
open import L.Constructible {ℓ}
  using ( isTransV; IsOrd; isL; Lset; Lset-in; layer-trans; Lset-layer )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open import L.Choice.Step {ℓ} lem using ( orderAt; Mem; relOf )
open import L.Choice.Order {ℓ} lem using ( module Bound; relL; relL-fill; relL-rep )
open import L.Coding.Base {ℓ} using ( prAt; Δ₀-prAt; prAt-adequate )

open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; [] )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_; _,_ )
open import Cubical.Data.Sum using ( _⊎_ )
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions using ( ∅ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module AtS = SemV.At S id

-- the term algebra, generic in the carrier, the order and the junk, so the
-- J tower instantiates the same core (DD4)
module TermAlgebra (𝒮 : ZFStructure (hPropAlgebra (ℓ-suc ℓ)))
                   (toSet : ZFStructure.S 𝒮 → V ℓ)
                   (wo : SWO (ZFStructure.S 𝒮))
                   (junk : ZFStructure.S 𝒮)
                   {K : Type ℓ} (emb : K → ZFStructure.S 𝒮) where

  open ZFStructure 𝒮 hiding ( _∈ˢ_ ) renaming ( S to S𝒮 )

  private module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮
  open Sem using () renaming ( _^_ to _^𝒮_ )
  module At0 = Sem.At (⊥* {ℓ}) Empty.rec*
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

  module AtCode = Sem.At Code val
  _⊨c_ : {n : ℕ} → S𝒮 ^𝒮 n → Formula Code n → hProp (ℓ-suc ℓ)
  _⊨c_ = AtCode._⊨_

  -- the junk split hides the search; open it when a witness exists, since
  -- the other branch carries a contradiction
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

  closed : (φ : Formula Code 1)
         → ∥ Σ[ a ∈ S𝒮 ] ⟨ (a ∷ []) ⊨c φ ⟩ ∥₁
         → ∥ Σ[ a ∈ S𝒮 ] (⟨ toSet a ∈ˢ Hull ⟩ × ⟨ (a ∷ []) ⊨c φ ⟩) ∥₁
  closed φ h = ∣ a , (a∈H , sat) ∣₁
    where
    ψ : Formula (⊥* {ℓ}) (suc (countFo φ))
    ψ = absFo φ
    cs : Vec Code (countFo φ)
    cs = constantsFo φ
    w : Sat (countFo φ) ψ (vals cs)
    w = PT.map (λ { (b , hb) →
      b , subst ⟨_⟩ (cong (λ vs → (b ∷ vs) ⊨₀ ψ) (sym (vals≡map cs)))
            (subst ⟨_⟩ (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) 𝒮 val φ (b ∷ [])) hb) }) h
    a : S𝒮
    a = search (countFo φ) ψ (vals cs) w
    pa : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
    pa = leastOf wo {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ vals cs) ⊨₀ ψ) w .snd .fst
    a∈H : ⟨ toSet a ∈ˢ Hull ⟩
    a∈H = subst (λ z → ⟨ toSet z ∈ˢ Hull ⟩) (val-wit (countFo φ) ψ cs w)
            (inHull (wit (countFo φ) ψ cs))
    sat : ⟨ (a ∷ []) ⊨c φ ⟩
    sat = subst ⟨_⟩ (sym (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) 𝒮 val φ (a ∷ [])))
            (subst ⟨_⟩ (cong (λ vs → (a ∷ vs) ⊨₀ ψ) (vals≡map cs)) pa)
```

## Elementarity at a set carrier inside a stage

```agda
module AtStage (α : S) (ordα : IsOrd α) where

  Ltr : isTransV (Lset α)
  Ltr = layer-trans (Lset-layer α)

  module AbsL = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ Lset α) Ltr

  SL : Type (ℓ-suc ℓ)
  SL = AbsL.SM

  wL : SWO SL
  wL = orderAt α ordα

  -- the equivalence holds at any carrier: the inner world is the restricted
  -- structure, and the bounded cases route through the criterion (Devlin 5.1)
  module AtM (M : S) (M⊆L : (x : S) → ⟨ x ∈ˢ M ⟩ → ⟨ x ∈ˢ Lset α ⟩) where

    SM : Type (ℓ-suc ℓ)
    SM = Σ[ x ∈ S ] ⟨ x ∈ˢ M ⟩

    module SemM = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) (𝒮ᵥ ↾ (λ x → x ∈ˢ M))
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

      -- weakening one variable is meaning-preserving at the stage
      renL : {n : ℕ} (t : Term SL n) (x : SL) (δ : SL ^ n)
           → AbsL.⟦ renameTm suc t ⟧ᵐ (x ∷ δ) ≡ AbsL.⟦ t ⟧ᵐ δ
      renL (con c) x δ = refl
      renL (var i) x δ = refl

      -- relabelling and renaming commute on terms
      mapTm-rename : {n m : ℕ} (f : SM → SL) (ρ : Fin n → Fin m) (t : Term SM n)
                   → mapTm f (renameTm ρ t) ≡ renameTm ρ (mapTm f t)
      mapTm-rename f ρ (con c) = refl
      mapTm-rename f ρ (var i) = refl

      -- the outer membership of x in t survives the weakening of t
      mem-ren : {n : ℕ} (t : Term SM n) (x : SL) (δ : SM ^ n)
              → ⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
              → ⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL (renameTm suc t) ⟧ᵐ (x ∷ map inL δ)) ⟩
      mem-ren t x δ hx =
        subst (λ s → ⟨ fst x ∈ˢ s ⟩)
          (sym (cong fst
            (cong (λ u → AbsL.⟦ u ⟧ᵐ (x ∷ map inL δ)) (mapTm-rename inL suc t)
               ∙ renL (mapTm inL t) x (map inL δ))))
          hx

      -- the criterion's outer witness q reads back into the inner membership
      mem-inner : {n : ℕ} (t : Term SM n) (q : SM) (δ : SM ^ n)
                → ⟨ fst q ∈ˢ fst (AbsL.⟦ mapTm inL (renameTm suc t) ⟧ᵐ (inL q ∷ map inL δ)) ⟩
                → ⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩
      mem-inner {n} t q δ hq =
        subst (λ s → ⟨ fst q ∈ˢ s ⟩) (sym (tm-agree n t δ))
          (subst (λ s → ⟨ fst q ∈ˢ s ⟩)
            (cong fst
              (cong (λ u → AbsL.⟦ u ⟧ᵐ (inL q ∷ map inL δ)) (mapTm-rename inL suc t)
                 ∙ renL (mapTm inL t) (inL q) (map inL δ)))
            hq)

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
         → (δ ⊨ᵐ φ) ≡ (map inL δ AbsL.⊨ᵐ (mapFo inL φ))
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
        fwd : ⟨ δ ⊨ᵐ (∃̇ ψ) ⟩ → ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ ψ)) ⟩
        fwd = PT.rec (snd (map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ ψ))))
          (λ { (q , hq) → ∣ inL q , subst ⟨_⟩ (go (suc n) ψ (q ∷ δ)) hq ∣₁ })
        bwd : ⟨ map inL δ AbsL.⊨ᵐ (mapFo inL (∃̇ ψ)) ⟩ → ⟨ δ ⊨ᵐ (∃̇ ψ) ⟩
        bwd h = PT.map (λ { (q , hq) → q , subst ⟨_⟩ (sym (go (suc n) ψ (q ∷ δ))) hq })
          (tv n ψ δ h)
      go n (∀̇ ψ) δ = ⇔toPath fwd bwd
        where
        fwd : ((q : SM) → ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩)
            → (x : SL) → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩
        fwd h x = dne ((x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ)) λ nx →
          PT.rec isProp⊥ (λ { (q , hq) →
            hq (subst ⟨_⟩ (go (suc n) ψ (q ∷ δ)) (h q)) })
            (tv n (¬̇ ψ) δ ∣ x , nx ∣₁)
        bwd : ((x : SL) → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩)
            → (q : SM) → ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩
        bwd h q = subst ⟨_⟩ (sym (go (suc n) ψ (q ∷ δ))) (h (inL q))
      go n (∀̇∈ t ψ) δ = ⇔toPath fwd bwd
        where
        mat : Formula SM (suc n)
        mat = (var zero ∈̇ renameTm suc t) ∧̇ ¬̇ ψ
        fwd : ((q : SM) → ⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩ → ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩)
            → (x : SL) → ⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
            → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩
        fwd h x hx =
          dne ((x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ)) λ nx →
          PT.rec isProp⊥ (λ { (q , hq) →
            hq .snd (subst ⟨_⟩ (go (suc n) ψ (q ∷ δ)) (h q (mem-inner t q δ (hq .fst)))) })
            (tv n mat δ ∣ x , (mem-ren t x δ hx , nx) ∣₁)
        bwd : ((x : SL) → ⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
                     → ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩)
            → (q : SM) → ⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩ → ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩
        bwd h q hq =
          subst ⟨_⟩ (sym (go (suc n) ψ (q ∷ δ)))
            (h (inL q) (subst (λ s → ⟨ fst q ∈ˢ s ⟩) (tm-agree n t δ) hq))
      go n (∃̇∈ t ψ) δ = ⇔toPath fwd bwd
        where
        mat : Formula SM (suc n)
        mat = (var zero ∈̇ renameTm suc t) ∧̇ ψ
        fwd : ∥ Σ[ q ∈ SM ] (⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩ × ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩) ∥₁
            → ∥ Σ[ x ∈ SL ] (⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
                          × ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩) ∥₁
        fwd = PT.map (λ { (q , hq , hψ) →
          inL q , (subst (λ s → ⟨ fst q ∈ˢ s ⟩) (tm-agree n t δ) hq ,
                   subst ⟨_⟩ (go (suc n) ψ (q ∷ δ)) hψ) })
        bwd : ∥ Σ[ x ∈ SL ] (⟨ fst x ∈ˢ fst (AbsL.⟦ mapTm inL t ⟧ᵐ (map inL δ)) ⟩
                          × ⟨ (x ∷ map inL δ) AbsL.⊨ᵐ (mapFo inL ψ) ⟩) ∥₁
            → ∥ Σ[ q ∈ SM ] (⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩ × ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩) ∥₁
        bwd h = PT.map (λ { (q , hq) →
          q , (mem-inner t q δ (hq .fst) , subst ⟨_⟩ (sym (go (suc n) ψ (q ∷ δ))) (hq .snd)) })
          (tv n mat δ (PT.map (λ { (x , hx , hψ) → x , (mem-ren t x δ hx , hψ) }) h))

    TV-thm : (Elementary → TarskiVaught) × (TarskiVaught → Elementary)
    TV-thm = elem→TV , TV→elem
```

## The definable hull

```agda
  module Hull (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
               (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

    -- the junk value: the empty set, a member of every nonempty stage
    ∅∈Lsetα : ⟨ ∅ ∈ˢ Lset α ⟩
    ∅∈Lsetα = Lset-in α ∅ ∅ ∅∈α (∅∈𝒟ₒ ∅)

    inStg : ⟪ X ⟫ → SL
    inStg m = ⟪ X ⟫↪ m , X⊆L (⟪ X ⟫↪ m) (member X m)

    module T = TermAlgebra AbsL.𝒮M fst wL (∅ , ∅∈Lsetα) {K = ⟪ X ⟫} inStg
    open T using ( Code; base; vals; val; Hull; inHull; closed; _⊨c_; _⊨₀_; Sat )

    toSL : ⟪ Lset α ⟫ → SL
    toSL m = ⟪ Lset α ⟫↪ m , member (Lset α) m

    -- the hull lies in the stage: every code value is a stage member
    Hull⊆L : (x : S) → ⟨ x ∈ˢ Hull ⟩ → ⟨ x ∈ˢ Lset α ⟩
    Hull⊆L x x∈H = PT.rec (snd (x ∈ˢ Lset α)) go x∈H
      where
      go : Σ[ c ∈ Code ] (fst (val c) ≡ x) → ⟨ x ∈ˢ Lset α ⟩
      go (c , q) = subst (λ z → ⟨ z ∈ˢ Lset α ⟩) q (snd (val c))

    -- reading the hull's membership back: a member is the value of a code
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

    -- re-stated over Code: a small witness lives in the stage's
    -- presentation, a big witness in the stage's inner world
    Witnessed-small : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k))
                    → (cs : Vec Code k) → Type (ℓ-suc ℓ)
    Witnessed-small k ψ cs =
      ∥ Σ[ m ∈ ⟪ Lset α ⟫ ] ⟨ (toSL m ∷ vals cs) ⊨₀ ψ ⟩ ∥₁

    small→big : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
              → Witnessed-small k ψ cs → Sat k ψ (vals cs)
    small→big k ψ cs = PT.map (λ { (m , hm) → toSL m , hm })

    big→small : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
              → Sat k ψ (vals cs) → Witnessed-small k ψ cs
    big→small k ψ cs = PT.map (λ { (a , ha) → toSmall a ha })
      where
      toSmall : (a : SL) → ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
              → Σ[ m ∈ ⟪ Lset α ⟫ ] ⟨ (toSL m ∷ vals cs) ⊨₀ ψ ⟩
      toSmall a ha =
        let m = fiber (Lset α) (snd a) .fst
            p : a ≡ toSL m
            p = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) (sym (fiber (Lset α) (snd a) .snd))
        in m , subst (λ (e : SL) → fst ((e ∷ vals cs) ⊨₀ ψ)) p ha

    SatAt-h : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
            → SL → hProp (ℓ-suc ℓ)
    SatAt-h k ψ cs a =
      (fst ((a ∷ vals cs) ⊨₀ ψ) , snd ((a ∷ vals cs) ⊨₀ ψ))

    -- perf: the search unfolds to a descent; seal at birth, spec as the read
    -- lemma (R-36)
    opaque
      leastSearch : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
                  → Witnessed-small k ψ cs
                  → Σ[ a ∈ SL ] IsLeast wL (SatAt-h k ψ cs) a
      leastSearch k ψ cs w =
        leastOf wL {ℓ'' = ℓ-suc ℓ} lem (SatAt-h k ψ cs) (small→big k ψ cs w)

    opaque
      unfolding leastSearch
      leastSearch-spec : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
                       → (w : Witnessed-small k ψ cs)
                       → leastSearch k ψ cs w
                       ≡ leastOf wL {ℓ'' = ℓ-suc ℓ} lem (SatAt-h k ψ cs)
                           (small→big k ψ cs w)
      leastSearch-spec k ψ cs w = refl

    leastWit : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
             → Witnessed-small k ψ cs → SL
    leastWit k ψ cs w = leastSearch k ψ cs w .fst

    leastWit-spec : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (cs : Vec Code k)
                  → (w : Witnessed-small k ψ cs)
                  → IsLeast wL (SatAt-h k ψ cs) (leastWit k ψ cs w)
    leastWit-spec k ψ cs w = leastSearch k ψ cs w .snd

    hullVal : Code → S
    hullVal c = fst (val c)

    hull-closed : (φ : Formula Code 1) → ⟨ [] AbsL.⊨ᵐ (∃̇ (mapFo val φ)) ⟩
                → ∥ Σ[ a ∈ SL ] (⟨ fst a ∈ˢ Hull ⟩
                               × ⟨ (a ∷ []) AbsL.⊨ᵐ (mapFo val φ) ⟩) ∥₁
    hull-closed φ h = PT.map (λ { (a , a∈H , sat) → a , a∈H ,
      subst ⟨_⟩ (sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) AbsL.𝒮M val id φ (a ∷ [])))
        sat })
      (closed φ w')
      where
      w' : ∥ Σ[ b ∈ SL ] ⟨ (b ∷ []) ⊨c φ ⟩ ∥₁
      w' = PT.map (λ { (b , hb) →
        b , subst ⟨_⟩ (⊨-map (hPropAlgebra (ℓ-suc ℓ)) AbsL.𝒮M val id φ (b ∷ []))
              hb }) h

```

## The order atom

```agda
-- The one fixed atom: the order membership `pr x y ∈̇ con orderL`. The
-- relation is bound to the delivered order element by an equality, and the
-- pair reader `prAt` reads the membership. The module is generic in the
-- ordinal; the two instances below fix the order element and nothing else
module OrderAt (o : S) (o-isL : ⟨ isL o ⟩) (o-ord : IsOrd o) where

  ordL : S
  ordL = fst (relL o o-isL o-ord)

  ordL-fill : (x y : Mem (Lset o)) → relOf (orderAt o o-ord) x y
            → ⟨ pr (fst x) (fst y) ∈ ordL ⟩
  ordL-fill = relL-fill o o-isL o-ord

  ordL-rep : (x y : Mem (Lset o)) → ⟨ pr (fst x) (fst y) ∈ ordL ⟩
           → relOf (orderAt o o-ord) x y
  ordL-rep = relL-rep o o-isL o-ord

  φ< : Formula S 2
  φ< = ∃̇ ( (var zero ≐ con ordL)
        ∧̇ ∃̇∈ (var zero) (prAt zero (suc (suc zero)) (suc (suc (suc zero)))) )

  -- the Levy certificate: the body is Δ₀ (the pair reader is), so the order
  -- membership is Σ₁, the class the condensation transfers ride
  Δ₀-φbody : Δ₀ {n = 3} ( (var zero ≐ con ordL)
                       ∧̇ ∃̇∈ (var zero) (prAt zero (suc (suc zero)) (suc (suc (suc zero)))) )
  Δ₀-φbody = δ-∧ δ-≐ (δ-∃∈ (Δ₀-prAt zero (suc (suc zero)) (suc (suc (suc zero)))))

  Σ₁-φ< : Σ₁ φ<
  Σ₁-φ< = σ-∃ (σ-Δ₀ Δ₀-φbody)

  φ<-fill : (x y : Mem (Lset o)) → relOf (orderAt o o-ord) x y
          → ⟨ (fst x ∷ fst y ∷ []) AtS.⊨ φ< ⟩
  φ<-fill x y lt = ∣ ordL ,
    ( refl
    , ∣ pr (fst x) (fst y) ,
        ( ordL-fill x y lt
        , subst ⟨_⟩ (sym (prAt-adequate zero (suc (suc zero)) (suc (suc (suc zero)))
                            (pr (fst x) (fst y) ∷ ordL ∷ fst x ∷ fst y ∷ [])))
            refl ) ∣₁ ) ∣₁

  φ<-rep : (x y : Mem (Lset o))
         → ⟨ (fst x ∷ fst y ∷ []) AtS.⊨ φ< ⟩
         → ∥ relOf (orderAt o o-ord) x y ∥₁
  φ<-rep x y h = PT.rec squash₁ go h
    where
    go : Σ[ r ∈ S ] ⟨ (r ∷ fst x ∷ fst y ∷ []) AtS.⊨
           ((var zero ≐ con ordL)
             ∧̇ ∃̇∈ (var zero) (prAt zero (suc (suc zero)) (suc (suc (suc zero))))) ⟩
       → ∥ relOf (orderAt o o-ord) x y ∥₁
    go (r , (er , hw)) = PT.rec squash₁ go₂ hw
      where
      go₂ : Σ[ w ∈ S ] ( ⟨ w ∈ r ⟩
                       × ⟨ (w ∷ r ∷ fst x ∷ fst y ∷ []) AtS.⊨
                           prAt zero (suc (suc zero)) (suc (suc (suc zero))) ⟩ )
          → ∥ relOf (orderAt o o-ord) x y ∥₁
      go₂ (w , (w∈r , hpr)) =
        let w≡p : w ≡ pr (fst x) (fst y)
            w≡p = subst ⟨_⟩ (prAt-adequate zero (suc (suc zero)) (suc (suc (suc zero)))
                              (w ∷ r ∷ fst x ∷ fst y ∷ [])) hpr
            p∈r : ⟨ pr (fst x) (fst y) ∈ r ⟩
            p∈r = subst (λ u → ⟨ u ∈ r ⟩) w≡p w∈r
            p∈o : ⟨ pr (fst x) (fst y) ∈ ordL ⟩
            p∈o = subst (λ s → ⟨ pr (fst x) (fst y) ∈ s ⟩) er p∈r
        in ∣ ordL-rep x y p∈o ∣₁

  φ<-irr : (x : Mem (Lset o)) → ⟨ (fst x ∷ fst x ∷ []) AtS.⊨ ¬̇ φ< ⟩
  φ<-irr x = λ h →
    PT.rec isProp⊥ (λ lt → SWO.irr∙ (orderAt o o-ord) x lt) (φ<-rep x x h)

  φ<-trans : (x y z : Mem (Lset o))
           → ⟨ (fst x ∷ fst y ∷ []) AtS.⊨ φ< ⟩
           → ⟨ (fst y ∷ fst z ∷ []) AtS.⊨ φ< ⟩
           → ∥ relOf (orderAt o o-ord) x z ∥₁
  φ<-trans x y z hxy hyz =
    PT.rec squash₁ (λ ltxy →
      PT.rec squash₁ (λ ltyz →
        ∣ SWO.trans∙ (orderAt o o-ord) x y z ltxy ltyz ∣₁)
        (φ<-rep y z hyz))
      (φ<-rep x y hxy)

-- the instance the recon names: the delivered order element at the bounding
-- ordinal of a constructible set, with its adequacy `orderL-fill`/`orderL-rep`
module OrderAtom (a : S) (p : ⟨ isL a ⟩) where
  module B = Bound a p
  module A = OrderAt B.boundOrd B.boundOrd-isL B.boundOrd-ord
  open A public

-- the same atom at the hull's own stage: the order element `relL α` with the
-- delivered `relL-fill`/`relL-rep` adequacy at `orderAt α ordα`
module OrderAtStage (α : S) (ordα : IsOrd α) (α-isL : ⟨ isL α ⟩) where
  module A = OrderAt α α-isL ordα
  open A public
```
