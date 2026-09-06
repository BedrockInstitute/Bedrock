# The Skolem hull and its collapse

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Hull {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; _↾_ )
open import FOL.Syntax using
  ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈ )
import FOL.Absoluteness
import FOL.Count
import FOL.Semantics
open import FOL.Manipulation.Parameters
  using ( countFo; constantsFo; absFo; ⊨-abs; lookup-map )
open import FOL.Manipulation.Relabelling
  using ( mapFo; mapTm; mapFo-comp; embed; embed-⊨; mapΔ₀; ⊨-map )
open import FOL.Manipulation.Renaming using ( renameTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Collapse {ℓ} using ( module Collapse; isExt; isTrans )
open import V.Smallness {ℓ} using ( separateFromSmall; module Δ₀Small )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ; Lset-suc )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isTransV; IsOrd; Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ
        ; layer-trans; Lset-layer )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω; ∅-ord )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡; rank-Lset )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.Rank {ℓ} using ( rank-fix )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open import L.Choice.Step {ℓ} lem using ( orderAt )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( Vec; map; lookup; _∷_; []; _++_ )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_; _,_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using ( tt* )
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
module Cnt = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S using ( erase; erase-inv )

module D0 = Δ₀Small {ℓc = ℓ-suc ℓ} {K = ⊥* {ℓ-suc ℓ}} (λ b → Empty.rec* b)
  using ( Δ₀-small )
```

J tower instantiates the same core (DD4)

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

  module AtCode = Sem.At Code val using ( _⊨_ )
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
    using ( SM; 𝒮M; _⊨ᵐ_; ⟦_⟧ᵐ; abs₀ )

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

## The collapse of the hull, and the iso-invariance of satisfaction

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

  private
    lookup-g : {n : ℕ} (i : Fin n) (δ : SM ^ n)
             → p (fst (lookup i δ)) ≡ fst (lookup i (map g δ))
    lookup-g zero (m ∷ δ) = refl
    lookup-g (suc i) (m ∷ δ) = lookup-g i δ

    tm-agree : {n : ℕ} (t : Term SM n) (δ : SM ^ n)
             → p (fst (⟦ t ⟧ᵐ δ)) ≡ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ))
    tm-agree (con m) δ = refl
    tm-agree (var i) δ = lookup-g i δ

  mutual
    iso-inv : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
            → ⟨ δ ⊨ᵐ φ ⟩ → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩
    iso-inv n (t ∈̇ u) δ h =
      subst (λ z → ⟨ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ∈ˢ z ⟩)
            (tm-agree u δ)
        (subst (λ z → ⟨ z ∈ˢ p (fst (⟦ u ⟧ᵐ δ)) ⟩) (tm-agree t δ)
          (iso-fwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
            (snd (⟦ t ⟧ᵐ δ)) h))
    iso-inv n (t ≐ u) δ h =
      subst (λ z → z ≡ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ))) (tm-agree t δ)
        (subst (λ z → p (fst (⟦ t ⟧ᵐ δ)) ≡ z) (tm-agree u δ) (cong p h))
    iso-inv n (φ ∧̇ ψ) δ h = iso-inv n φ δ (h .fst) , iso-inv n ψ δ (h .snd)
    iso-inv n (φ ∨̇ ψ) δ h =
      PT.map (λ { (inl hφ) → inl (iso-inv n φ δ hφ)
                ; (inr hψ) → inr (iso-inv n ψ δ hψ) }) h
    iso-inv n (φ ⇒̇ ψ) δ h h' =
      iso-inv n ψ δ (h (iso-inv-bwd n φ δ h'))
    iso-inv n (¬̇ φ) δ h h' = h (iso-inv-bwd n φ δ h')
    iso-inv n ⊤̇ δ _ = tt*
    iso-inv n ⊥̇ δ ()
    iso-inv n (∃̇ ψ) δ h =
      PT.rec (snd (map g δ ⊨ᵖᵐ mapFo g (∃̇ ψ))) go h
      where
      go : Σ[ q ∈ SM ] ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩
         → ⟨ map g δ ⊨ᵖᵐ mapFo g (∃̇ ψ) ⟩
      go (q , hq) = ∣ g q , iso-inv (suc n) ψ (q ∷ δ) hq ∣₁
    iso-inv n (∀̇ ψ) δ h =
      λ p' → PT.rec (snd ((p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ))
        (λ { (q , gq≡p) →
          subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩) (cong (λ z → z ∷ map g δ) gq≡p)
            (iso-inv (suc n) ψ (q ∷ δ) (h q)) })
        (surj' p')
    iso-inv n (∀̇∈ t ψ) δ h =
      λ p' p∈t → PT.rec (snd ((p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ))
        (λ { (q , gq≡p) →
          let p∈gx : ⟨ fst p' ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx = subst (λ z → ⟨ fst p' ∈ˢ z ⟩) (sym (tm-agree t δ)) p∈t
              p∈gx' : ⟨ fst (g q) ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx' = subst (λ z → ⟨ z ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩)
                        (sym (cong fst gq≡p)) p∈gx
              q∈t : ⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩
              q∈t = iso-bwd (fst (⟦ t ⟧ᵐ δ)) (fst q)
                      (snd (⟦ t ⟧ᵐ δ)) (snd q) p∈gx'
              hψ : ⟨ (g q ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩
              hψ = iso-inv (suc n) ψ (q ∷ δ) (h q q∈t)
          in subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩)
               (cong (λ z → z ∷ map g δ) gq≡p) hψ })
        (surj' p')
    iso-inv n (∃̇∈ t ψ) δ h =
      PT.map (λ { (q , q∈t , hψ) →
        g q ,
        ( subst (λ z → ⟨ p (fst q) ∈ˢ z ⟩) (tm-agree t δ)
            (iso-fwd (fst (⟦ t ⟧ᵐ δ)) (fst q) (snd (⟦ t ⟧ᵐ δ)) (snd q) q∈t)
        , iso-inv (suc n) ψ (q ∷ δ) hψ ) }) h

    iso-inv-bwd : (n : ℕ) (φ : Formula SM n) (δ : SM ^ n)
                → ⟨ map g δ ⊨ᵖᵐ mapFo g φ ⟩ → ⟨ δ ⊨ᵐ φ ⟩
    iso-inv-bwd n (t ∈̇ u) δ h =
      iso-bwd (fst (⟦ u ⟧ᵐ δ)) (fst (⟦ t ⟧ᵐ δ)) (snd (⟦ u ⟧ᵐ δ))
        (snd (⟦ t ⟧ᵐ δ))
        (subst (λ z → ⟨ p (fst (⟦ t ⟧ᵐ δ)) ∈ˢ z ⟩) (sym (tm-agree u δ))
          (subst (λ z → ⟨ z ∈ˢ fst (⟦ mapTm g u ⟧ᵖᵐ (map g δ)) ⟩)
            (sym (tm-agree t δ)) h))
    iso-inv-bwd n (t ≐ u) δ h =
      p-inj (fst (⟦ t ⟧ᵐ δ)) (fst (⟦ u ⟧ᵐ δ)) (snd (⟦ t ⟧ᵐ δ))
        (snd (⟦ u ⟧ᵐ δ))
        (subst (λ z → z ≡ p (fst (⟦ u ⟧ᵐ δ))) (sym (tm-agree t δ))
          (subst (λ z → fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ≡ z)
            (sym (tm-agree u δ)) h))
    iso-inv-bwd n (φ ∧̇ ψ) δ h =
      iso-inv-bwd n φ δ (h .fst) , iso-inv-bwd n ψ δ (h .snd)
    iso-inv-bwd n (φ ∨̇ ψ) δ h =
      PT.map (λ { (inl hφ) → inl (iso-inv-bwd n φ δ hφ)
                ; (inr hψ) → inr (iso-inv-bwd n ψ δ hψ) }) h
    iso-inv-bwd n (φ ⇒̇ ψ) δ h h' =
      iso-inv-bwd n ψ δ (h (iso-inv n φ δ h'))
    iso-inv-bwd n (¬̇ φ) δ h h' = h (iso-inv n φ δ h')
    iso-inv-bwd n ⊤̇ δ _ = tt*
    iso-inv-bwd n ⊥̇ δ ()
    iso-inv-bwd n (∃̇ ψ) δ h =
      PT.rec (snd (δ ⊨ᵐ (∃̇ ψ))) go h
      where
      go : Σ[ p' ∈ SPM ] ⟨ (p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩
         → ⟨ δ ⊨ᵐ (∃̇ ψ) ⟩
      go (p' , hp) = PT.rec (snd (δ ⊨ᵐ (∃̇ ψ))) go₂ (surj' p')
        where
        go₂ : Σ[ q ∈ SM ] (g q ≡ p') → ⟨ δ ⊨ᵐ (∃̇ ψ) ⟩
        go₂ (q , gq≡p) =
          ∣ q , iso-inv-bwd (suc n) ψ (q ∷ δ)
                (subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩)
                  (sym (cong (λ z → z ∷ map g δ) gq≡p)) hp) ∣₁
    iso-inv-bwd n (∀̇ ψ) δ h =
      λ q → iso-inv-bwd (suc n) ψ (q ∷ δ) (h (g q))
    iso-inv-bwd n (∀̇∈ t ψ) δ h =
      λ q q∈t →
        iso-inv-bwd (suc n) ψ (q ∷ δ)
          (h (g q)
            (subst (λ z → ⟨ p (fst q) ∈ˢ z ⟩) (tm-agree t δ)
              (iso-fwd (fst (⟦ t ⟧ᵐ δ)) (fst q)
                (snd (⟦ t ⟧ᵐ δ)) (snd q) q∈t)))
    iso-inv-bwd n (∃̇∈ t ψ) δ h =
      PT.rec (snd (δ ⊨ᵐ (∃̇∈ t ψ))) go h
      where
      go : Σ[ p' ∈ SPM ]
             (⟨ fst p' ∈ˢ fst (⟦ mapTm g t ⟧ᵖᵐ (map g δ)) ⟩
            × ⟨ (p' ∷ map g δ) ⊨ᵖᵐ mapFo g ψ ⟩)
         → ⟨ δ ⊨ᵐ (∃̇∈ t ψ) ⟩
      go (p' , p∈t , hp) = PT.rec (snd (δ ⊨ᵐ (∃̇∈ t ψ))) go₂ (surj' p')
        where
        go₂ : Σ[ q ∈ SM ] (g q ≡ p') → ⟨ δ ⊨ᵐ (∃̇∈ t ψ) ⟩
        go₂ (q , gq≡p) =
          let p∈gx : ⟨ fst p' ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx = subst (λ z → ⟨ fst p' ∈ˢ z ⟩) (sym (tm-agree t δ)) p∈t
              p∈gx' : ⟨ fst (g q) ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩
              p∈gx' = subst (λ z → ⟨ z ∈ˢ p (fst (⟦ t ⟧ᵐ δ)) ⟩)
                        (sym (cong fst gq≡p)) p∈gx
              q∈t : ⟨ fst q ∈ˢ fst (⟦ t ⟧ᵐ δ) ⟩
              q∈t = iso-bwd (fst (⟦ t ⟧ᵐ δ)) (fst q)
                      (snd (⟦ t ⟧ᵐ δ)) (snd q) p∈gx'
              hψ : ⟨ (q ∷ δ) ⊨ᵐ ψ ⟩
              hψ = iso-inv-bwd (suc n) ψ (q ∷ δ)
                      (subst (λ e → ⟨ e ⊨ᵖᵐ mapFo g ψ ⟩)
                        (sym (cong (λ z → z ∷ map g δ) gq≡p)) hp)
          in ∣ q , q∈t , hψ ∣₁
```

The collapse instance: M = the carrier X, PM = the collapse image piX.

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

## The elementarity of the hull

WALL 2, PLACED ([LJ-1.53] probe A).  The parameter-to-code
relabelling inside TV/ElemDown.  The generic close operation that
replaces the top parameters by their codes as constants, its
satisfaction adequacy, and the TarskiVaught instance at every arity
assembled from hull-closed through the two halves.  AtM.TV-thm
turns the instance into Elementary, hence ElemDown.

The generic close operation (syntax): a formula of arity d + n has
its top n variables replaced by the constants δ, the
parameter-as-constant spelling.  The first d variables (the binders
already crossed) stay variables.  Both consumers are one recursion:
close keeps the witness variable free (d = 1), closeAll closes every
top variable (d = 0).

```agda
module CloseSyntax where

  closeTmAt : {K : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
            → Term K (d + n) → Term K d
  closeTmAt d n δ (con c) = con c
  closeTmAt zero zero δ (var ())
  closeTmAt zero (suc n) δ (var zero) = con (lookup zero δ)
  closeTmAt zero (suc n) δ (var (suc i)) = con (lookup (suc i) δ)
  closeTmAt (suc d) n δ (var zero) = var zero
  closeTmAt (suc d) n δ (var (suc j)) =
    renameTm suc (closeTmAt d n δ (var j))

  closeAt : {K : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
          → Formula K (d + n) → Formula K d
  closeAt d n δ (t ∈̇ u) = closeTmAt d n δ t ∈̇ closeTmAt d n δ u
  closeAt d n δ (t ≐ u) = closeTmAt d n δ t ≐ closeTmAt d n δ u
  closeAt d n δ (φ ∧̇ ψ) = closeAt d n δ φ ∧̇ closeAt d n δ ψ
  closeAt d n δ (φ ∨̇ ψ) = closeAt d n δ φ ∨̇ closeAt d n δ ψ
  closeAt d n δ (φ ⇒̇ ψ) = closeAt d n δ φ ⇒̇ closeAt d n δ ψ
  closeAt d n δ (¬̇ φ) = ¬̇ closeAt d n δ φ
  closeAt d n δ ⊤̇ = ⊤̇
  closeAt d n δ ⊥̇ = ⊥̇
  closeAt d n δ (∃̇ ψ) = ∃̇ (closeAt (suc d) n δ ψ)
  closeAt d n δ (∀̇ ψ) = ∀̇ (closeAt (suc d) n δ ψ)
  closeAt d n δ (∀̇∈ t ψ) = ∀̇∈ (closeTmAt d n δ t) (closeAt (suc d) n δ ψ)
  closeAt d n δ (∃̇∈ t ψ) = ∃̇∈ (closeTmAt d n δ t) (closeAt (suc d) n δ ψ)

  -- the closure of the parameter block and the witness variable
  close : {K : Type (ℓ-suc ℓ)} (n : ℕ) (δ : Vec K n)
        → (φ : Formula K (suc n)) → Formula K 1
  close n δ φ = closeAt 1 n δ φ

  -- the full closure (no witness variable left)
  closeAll : {K : Type (ℓ-suc ℓ)} (n : ℕ) (δ : Vec K n)
           → (φ : Formula K n) → Formula K 0
  closeAll n δ φ = closeAt 0 n δ φ

  -- relabelling and closure commute: closing after relabelling is
  -- relabelling after closing
  mapTm-rename : {K K' : Type (ℓ-suc ℓ)} {n m : ℕ} (g : K → K')
               → (ρ : Fin n → Fin m) (t : Term K n)
               → mapTm g (renameTm ρ t) ≡ renameTm ρ (mapTm g t)
  mapTm-rename g ρ (con c) = refl
  mapTm-rename g ρ (var j) = refl

  mapTm-close : {K K' : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
              → (g : K → K') (t : Term K (d + n))
              → mapTm g (closeTmAt d n δ t)
                ≡ closeTmAt d n (map g δ) (mapTm g t)
  mapTm-close d n δ g (con c) = refl
  mapTm-close zero zero δ g (var ())
  mapTm-close zero (suc n) δ g (var zero) =
    cong con (sym (lookup-map g δ zero))
  mapTm-close zero (suc n) δ g (var (suc i)) =
    cong con (sym (lookup-map g δ (suc i)))
  mapTm-close (suc d) n δ g (var zero) = refl
  mapTm-close (suc d) n δ g (var (suc j)) =
    mapTm-rename g suc (closeTmAt d n δ (var j))
    ∙ cong (renameTm suc) (mapTm-close d n δ g (var j))

  mapFo-close : {K K' : Type (ℓ-suc ℓ)} (d n : ℕ) (δ : Vec K n)
              → (g : K → K') (φ : Formula K (d + n))
              → mapFo g (closeAt d n δ φ)
                ≡ closeAt d n (map g δ) (mapFo g φ)
  mapFo-close d n δ g (t ∈̇ u) = cong₂ _∈̇_
    (mapTm-close d n δ g t) (mapTm-close d n δ g u)
  mapFo-close d n δ g (t ≐ u) = cong₂ _≐_
    (mapTm-close d n δ g t) (mapTm-close d n δ g u)
  mapFo-close d n δ g (φ ∧̇ ψ) = cong₂ _∧̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (φ ∨̇ ψ) = cong₂ _∨̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (φ ⇒̇ ψ) = cong₂ _⇒̇_
    (mapFo-close d n δ g φ) (mapFo-close d n δ g ψ)
  mapFo-close d n δ g (¬̇ φ) = cong ¬̇_ (mapFo-close d n δ g φ)
  mapFo-close d n δ g ⊤̇ = refl
  mapFo-close d n δ g ⊥̇ = refl
  mapFo-close d n δ g (∃̇ ψ) = cong ∃̇_ (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∀̇ ψ) = cong ∀̇_ (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∀̇∈ t ψ) = cong₂ ∀̇∈
    (mapTm-close d n δ g t) (mapFo-close (suc d) n δ g ψ)
  mapFo-close d n δ g (∃̇∈ t ψ) = cong₂ ∃̇∈
    (mapTm-close d n δ g t) (mapFo-close (suc d) n δ g ψ)
```

The adequacy of the close operation (semantics): the original
formula at the environment γ ++ map ι δ is the closed formula at γ.

```agda
module CloseSem {𝒮 : ZFStructure (hPropAlgebra (ℓ-suc ℓ))}
                {K : Type (ℓ-suc ℓ)} (ι : K → ZFStructure.S 𝒮) where

  open ZFStructure 𝒮 renaming ( _∈ˢ_ to _∈ˢ𝒮_ ; _≈ˢ_ to _≈ˢ𝒮_ )
  module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮 using ( module At; _^_ )
  open Sem.At K ι using ( _⊨_; ⟦_⟧ )
  module Cl = CloseSyntax using ( closeTmAt; closeAt; close; closeAll )

  map-id : {ℓ'' : Level} {A : Type ℓ''} {n : ℕ} (v : Vec A n)
         → map (λ x → x) v ≡ v
  map-id [] = refl
  map-id (x ∷ v) = cong (x ∷_) (map-id v)

  -- a term lifted past a binder reads the tail of the environment
  renameTm-suc-sat : {d : ℕ} (X : Term K d) (y : ZFStructure.S 𝒮)
                   (γ : Sem._^_ (ZFStructure.S 𝒮) d)
                   → ⟦ renameTm suc X ⟧ (y ∷ γ) ≡ ⟦ X ⟧ γ
  renameTm-suc-sat (con c) y γ = refl
  renameTm-suc-sat (var i) y γ = refl

  -- the term-level adequacy: every clause is lookup-map or the
  -- induction hypothesis, and the kept variables are refl
  ⟦⟧-close : (d n : ℕ) (t : Term K (d + n)) (δ : Vec K n)
           (γ : Sem._^_ (ZFStructure.S 𝒮) d)
           → ⟦ t ⟧ (γ ++ map ι δ) ≡ ⟦ Cl.closeTmAt d n δ t ⟧ γ
  ⟦⟧-close d n (con c) δ γ = refl
  ⟦⟧-close zero zero (var ()) δ γ
  ⟦⟧-close zero (suc n) (var zero) δ [] = lookup-map ι δ zero
  ⟦⟧-close zero (suc n) (var (suc i)) δ [] = lookup-map ι δ (suc i)
  ⟦⟧-close (suc d) n (var zero) δ (y ∷ γ) = refl
  ⟦⟧-close (suc d) n (var (suc j)) δ (y ∷ γ) =
    ⟦⟧-close d n (var j) δ γ
    ∙ sym (renameTm-suc-sat (Cl.closeTmAt d n δ (var j)) y γ)

  -- the formula-level adequacy: the fourteen clauses of the semantics,
  -- each a congruence, the binders pushing a value onto the env
  ⊨-close : (d n : ℕ) (φ : Formula K (d + n)) (δ : Vec K n)
          (γ : Sem._^_ (ZFStructure.S 𝒮) d)
          → (γ ++ map ι δ) ⊨ φ ≡ γ ⊨ Cl.closeAt d n δ φ
  ⊨-close d n (t ∈̇ u) δ γ = cong₂ _∈ˢ𝒮_
    (⟦⟧-close d n t δ γ) (⟦⟧-close d n u δ γ)
  ⊨-close d n (t ≐ u) δ γ = cong₂ _≈ˢ𝒮_
    (⟦⟧-close d n t δ γ) (⟦⟧-close d n u δ γ)
  ⊨-close d n (φ ∧̇ ψ) δ γ = cong₂ _⊓_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (φ ∨̇ ψ) δ γ = cong₂ _⊔_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (φ ⇒̇ ψ) δ γ = cong₂ _⇒_
    (⊨-close d n φ δ γ) (⊨-close d n ψ δ γ)
  ⊨-close d n (¬̇ φ) δ γ = cong ¬_ (⊨-close d n φ δ γ)
  ⊨-close d n ⊤̇ δ γ = refl
  ⊨-close d n ⊥̇ δ γ = refl
  ⊨-close d n (∃̇ ψ) δ γ = cong (⋁ (ZFStructure.S 𝒮)) (funExt (λ x →
    ⊨-close (suc d) n ψ δ (x ∷ γ)))
  ⊨-close d n (∀̇ ψ) δ γ = cong (⋀ (ZFStructure.S 𝒮)) (funExt (λ x →
    ⊨-close (suc d) n ψ δ (x ∷ γ)))
  ⊨-close d n (∀̇∈ t ψ) δ γ = cong (⋀ (ZFStructure.S 𝒮)) (funExt (λ x →
    cong₂ _⇒_ (cong (x ∈ˢ𝒮_) (⟦⟧-close d n t δ γ))
      (⊨-close (suc d) n ψ δ (x ∷ γ))))
  ⊨-close d n (∃̇∈ t ψ) δ γ = cong (⋁ (ZFStructure.S 𝒮)) (funExt (λ x →
    cong₂ _⊓_ (cong (x ∈ˢ𝒮_) (⟦⟧-close d n t δ γ))
      (⊨-close (suc d) n ψ δ (x ∷ γ))))

  ⊨-close₁ : (n : ℕ) (φ : Formula K (suc n)) (δ : Vec K n) (x : ZFStructure.S 𝒮)
           → (x ∷ map ι δ) ⊨ φ ≡ (x ∷ []) ⊨ Cl.close n δ φ
  ⊨-close₁ n φ δ x = ⊨-close 1 n φ δ (x ∷ [])

  ⊨-closeAll : (n : ℕ) (φ : Formula K n) (δ : Vec K n)
             → map ι δ ⊨ φ ≡ [] ⊨ Cl.closeAll n δ φ
  ⊨-closeAll n φ δ = ⊨-close 0 n φ δ []
```

The hull instance: the codes of the constants of one formula, read
off the hull membership at each call, then the TarskiVaught instance
at every arity, and ElemDown.

```agda
module HullElemDown (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩) (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα using ( module AbsL; module AtM; module Hull; SL )
  module H = ASt.Hull X X⊆L ∅∈α
    using ( module T; Hull⊆L; hull-closed; hull-member; val-in-Hull )
  M : S
  M = H.T.Hull
  module A = ASt.AtM M H.Hull⊆L using ( Elementary; SM; module SemM; TV-thm; inL )
  module Mse = A.SemM.At A.SM id using ( _⊨_ )

  module Cl = CloseSyntax using ( close; mapFo-close )
  module CseL = CloseSem {𝒮 = 𝒮ᵥ ↾ (λ x → x ∈ˢ Lset α)} {K = ASt.SL} id
    using ( module Cl; map-id; ⊨-closeAll; ⊨-close₁ )

  -- D-30: the consumer needs a code for each constant that OCCURS, not
  -- a total section of `val`.  A formula is finite, so the codes come
  -- out of the hull membership one constant at a time, and each
  -- truncation stays outside the goal of `tv`, which is a proposition.
  codeOf : (q : A.SM) → ∥ Σ[ c ∈ H.T.Code ] (H.T.val c ≡ A.inL q) ∥₁
  codeOf q = PT.map (λ { (c , e) → c , Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) e })
    (H.hull-member (fst q) (snd q))

  codeTm : {n : ℕ} (t : Term A.SM n)
         → ∥ Σ[ t' ∈ Term H.T.Code n ] (mapTm H.T.val t' ≡ mapTm A.inL t) ∥₁
  codeTm (con q) = PT.map (λ { (c , e) → con c , cong con e }) (codeOf q)
  codeTm (var i) = ∣ var i , refl ∣₁

  codeFo : {n : ℕ} (φ : Formula A.SM n)
         → ∥ Σ[ φ' ∈ Formula H.T.Code n ] (mapFo H.T.val φ' ≡ mapFo A.inL φ) ∥₁
  codeFo (t ∈̇ u) = PT.map2
    (λ { (t' , e) (u' , d) → (t' ∈̇ u') , cong₂ _∈̇_ e d }) (codeTm t) (codeTm u)
  codeFo (t ≐ u) = PT.map2
    (λ { (t' , e) (u' , d) → (t' ≐ u') , cong₂ _≐_ e d }) (codeTm t) (codeTm u)
  codeFo (φ ∧̇ ψ) = PT.map2
    (λ { (φ' , e) (ψ' , d) → (φ' ∧̇ ψ') , cong₂ _∧̇_ e d }) (codeFo φ) (codeFo ψ)
  codeFo (φ ∨̇ ψ) = PT.map2
    (λ { (φ' , e) (ψ' , d) → (φ' ∨̇ ψ') , cong₂ _∨̇_ e d }) (codeFo φ) (codeFo ψ)
  codeFo (φ ⇒̇ ψ) = PT.map2
    (λ { (φ' , e) (ψ' , d) → (φ' ⇒̇ ψ') , cong₂ _⇒̇_ e d }) (codeFo φ) (codeFo ψ)
  codeFo (¬̇ φ) = PT.map (λ { (φ' , e) → ¬̇ φ' , cong ¬̇_ e }) (codeFo φ)
  codeFo ⊤̇ = ∣ ⊤̇ , refl ∣₁
  codeFo ⊥̇ = ∣ ⊥̇ , refl ∣₁
  codeFo (∃̇ φ) = PT.map (λ { (φ' , e) → ∃̇ φ' , cong ∃̇_ e }) (codeFo φ)
  codeFo (∀̇ φ) = PT.map (λ { (φ' , e) → ∀̇ φ' , cong ∀̇_ e }) (codeFo φ)
  codeFo (∀̇∈ t φ) = PT.map2
    (λ { (t' , e) (φ' , d) → ∀̇∈ t' φ' , cong₂ ∀̇∈ e d }) (codeTm t) (codeFo φ)
  codeFo (∃̇∈ t φ) = PT.map2
    (λ { (t' , e) (φ' , d) → ∃̇∈ t' φ' , cong₂ ∃̇∈ e d }) (codeTm t) (codeFo φ)

  -- TarskiVaught at every arity: the stage existential at the closed
  -- parameters is hull-closed, and the code formula reads back
  -- through the relabelling and the close transfer
  tv : (n : ℕ) (ψ : Formula A.SM (suc n)) (δ : Vec A.SM n)
     → ⟨ map A.inL δ ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ)) ⟩
     → ∥ Σ[ q ∈ A.SM ]
          ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
  tv n ψ δ h = PT.rec squash₁ step (codeFo (Cl.close n δ ψ))
    where
    step : Σ[ ψ' ∈ Formula H.T.Code 1 ]
             (mapFo H.T.val ψ' ≡ mapFo A.inL (Cl.close n δ ψ))
         → ∥ Σ[ q ∈ A.SM ]
              ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
    step (ψ' , rel) = PT.rec squash₁ go (H.hull-closed ψ' h')
      where
      h' : ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val ψ')) ⟩
      h' = subst (λ ψ → ⟨ [] ASt.AbsL.⊨ᵐ ψ ⟩) p
        (subst ⟨_⟩ (CseL.⊨-closeAll n (mapFo A.inL (∃̇ ψ)) (map A.inL δ)) h₁)
        where
        h₁ : fst (map (λ x → x) (map A.inL δ) ASt.AbsL.⊨ᵐ
                (mapFo A.inL (∃̇ ψ)))
        h₁ = subst (λ e → fst (e ASt.AbsL.⊨ᵐ (mapFo A.inL (∃̇ ψ))))
               (sym (CseL.map-id (map A.inL δ))) h
        p1 : CseL.Cl.closeAll n (map A.inL δ) (mapFo A.inL (∃̇ ψ))
           ≡ FOL.Syntax.∃̇_ (mapFo A.inL (Cl.close n δ ψ))
        p1 = cong FOL.Syntax.∃̇_
               (sym (Cl.mapFo-close 1 n δ A.inL ψ))
        p : CseL.Cl.closeAll n (map A.inL δ) (mapFo A.inL (∃̇ ψ))
          ≡ FOL.Syntax.∃̇_ (mapFo H.T.val ψ')
        p = p1 ∙ cong FOL.Syntax.∃̇_ (sym rel)

      go : Σ[ a ∈ ASt.SL ] (⟨ fst a ∈ˢ M ⟩
                          × ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩)
         → ∥ Σ[ q ∈ A.SM ]
              ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
      go (a , a∈H , hsat) = PT.rec squash₁ go₂ (H.hull-member (fst a) a∈H)
        where
        go₂ : Σ[ c ∈ H.T.Code ] (fst (H.T.val c) ≡ fst a)
            → ∥ Σ[ q ∈ A.SM ]
                 ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩ ∥₁
        go₂ (c , e) = ∣ q , sat ∣₁
          where
          q : A.SM
          q = fst (H.T.val c) , H.val-in-Hull c
          q≡a : A.inL q ≡ a
          q≡a = Σ≡Prop (λ z → (z ∈ˢ Lset α) .snd) e
          sat : ⟨ (A.inL q ∷ map A.inL δ) ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩
          sat = subst (λ e' → ⟨ (A.inL q ∷ e') ASt.AbsL.⊨ᵐ (mapFo A.inL ψ) ⟩)
                  (CseL.map-id (map A.inL δ))
                  (subst ⟨_⟩
                    (sym (CseL.⊨-close₁ n (mapFo A.inL ψ) (map A.inL δ) (A.inL q)))
                    sat₁)
            where
            sat₁ : ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ
                       (CseL.Cl.close n (map A.inL δ) (mapFo A.inL ψ)) ⟩
            sat₁ = subst (λ ψ → ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ ψ ⟩)
                     (sym q-path) sat₂
              where
              q-path : CseL.Cl.close n (map A.inL δ) (mapFo A.inL ψ)
                     ≡ mapFo H.T.val ψ'
              q-path = sym (Cl.mapFo-close 1 n δ A.inL ψ) ∙ sym rel
              sat₂ : ⟨ (A.inL q ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩
              sat₂ = subst (λ z → ⟨ (z ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val ψ') ⟩)
                       (sym q≡a)
                       hsat

  elem : A.Elementary
  elem = A.TV-thm .snd tv

```

## The ambient parameter-free reading

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

Ordinality of the parameter, as a 3-slot conjunct, p at slot 1.  Not
sealed: `L.GCH.Condense` and `L.GCH.Complete` read its shape.

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
erase-Δ₀ (¬̇ φ) p (δ-¬ c) = δ-¬ (erase-Δ₀ φ p c)
erase-Δ₀ ⊤̇ p δ-⊤ = δ-⊤
erase-Δ₀ ⊥̇ p δ-⊥ = δ-⊥
erase-Δ₀ (∀̇∈ t φ) p (δ-∀∈ c) = δ-∀∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇∈ t φ) p (δ-∃∈ c) = δ-∃∈ (erase-Δ₀ φ _ c)
erase-Δ₀ (∃̇ φ) p ()
erase-Δ₀ (∀̇ φ) p ()
```

THE LEFTOVER EQUATION.  [LJ-1.686] Probe686.agda:34-55, module `At`
renamed `EmbedAt`.  `mapFo val (mapFo slide φ) ≡ embed φ` by
mapFo-comp and uniqueness of maps out of ⊥*.

```agda
lemma : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd} {n : ℕ}
        (φ : Formula (⊥* {ℓ-suc ℓ}) n)
        (slide : ⊥* {ℓ-suc ℓ} → K)
        (val : K → K')
      → mapFo val (mapFo slide φ) ≡ embed φ
lemma φ slide val =
    mapFo-comp slide val φ
  ∙ cong (λ h → mapFo h φ) (funExt (λ b → Empty.rec* b))
```

## The hull stage and its condensation

The hull of X at the stage Lset λ, its collapse, and the condensation
theorem at this one instance (D-30: the consumer's shape, not the
general theory).  The two transfer hypotheses are Devlin's (h) and
(n)-(p): the collapse is closed under the level construction at its
own ordinals, and every hull member is covered by a level below the
collapse's ordinals.  [LJ-1.48] measured the skeleton around them
(elementarity, iso-invariance, the level-hood certificate) at
0.0097 s per line; the level-hood instantiation at the hull is the
priced residue.

```agda
module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩) (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
    using ( module AbsL; module AtM; module Hull; Ltr; SL; wL )

  module H = ASt.Hull X X⊆L ∅∈λ
    using ( module T; module XInM; Hull⊆L; X⊆M; hull-member; hull-closed
          ; val-in-Hull; ∅∈Lsetα; inStg; toSL; hullVal; leastWit; leastWit-spec )

  M : S
  M = H.T.Hull

  module C = Collapse M
    using ( module InjExt; π; πX; πX-intro; πX-member; πX-trans; fixes )

  module Condense
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁)
    where

    -- beta = the ordinals of the collapse, separated by the Delta-0
    -- ordinal formula.  This is the L-native supremum (ProbeT261's
    -- shape at the transitive carrier).
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

    -- Every ordinal of the collapse is a member of a larger ordinal of
    -- the collapse: the transfer's cover plus the ordinals-in-stages
    -- fact (rank).  This is Devlin's lim(β) step.
    β-succ : (δ : S) → ⟨ δ ∈ˢ β ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
    β-succ δ δ∈β = PT.rec squash₁ go (C.πX-member δ (β∈πX δ δ∈β))
      where
      oδ : IsOrd δ
      oδ = β-ord δ δ∈β
      go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ δ))
         → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
      go (y , y∈M , e) = PT.rec squash₁ go₂ (cover y y∈M)
        where
        go₂ : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩)
            → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩) ∥₁
        go₂ (γ , oγ , γ∈πX , h) =
          ∣ γ , ( oγ , δ∈γ , ord∈β γ γ∈πX oγ ) ∣₁
          where
          δ∈Lγ : ⟨ δ ∈ˢ Lset γ ⟩
          δ∈Lγ = subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) e h
          δ∈γ : ⟨ δ ∈ˢ γ ⟩
          δ∈γ = subst (λ w → ⟨ w ∈ˢ γ ⟩) (rank-fix δ oδ)
                  (rank-Lset γ oγ δ δ∈Lγ)

    sucV∈β : (δ : S) → ⟨ δ ∈ˢ β ⟩ → ⟨ sucV δ ∈ˢ β ⟩
    sucV∈β δ δ∈β = PT.rec (snd (sucV δ ∈ˢ β)) go (β-succ δ δ∈β)
      where
      oδ : IsOrd δ
      oδ = β-ord δ δ∈β
      go : Σ[ γ ∈ S ] (IsOrd γ × ⟨ δ ∈ˢ γ ⟩ × ⟨ γ ∈ˢ β ⟩)
         → ⟨ sucV δ ∈ˢ β ⟩
      go (γ , oγ , δ∈γ , γ∈β) = ord∈β (sucV δ) sucV∈πX (suc-ord oδ)
        where
        sucV∈πX : ⟨ sucV δ ∈ˢ C.πX ⟩
        sucV∈πX = Sum.rec
          (λ s∈γ → C.πX-trans {x = γ} {y = sucV δ} s∈γ (β∈πX γ γ∈β))
          (λ s≡γ → subst (λ w → ⟨ w ∈ˢ C.πX ⟩) (sym s≡γ) (β∈πX γ γ∈β))
          (suc∈or≡ δ γ oδ oγ δ∈γ)

    -- The reverse inclusion: every member of the collapse lies in a
    -- level below beta.
    πX⊆Lβ : (x : S) → ⟨ x ∈ˢ C.πX ⟩ → ⟨ x ∈ˢ Lset β ⟩
    πX⊆Lβ x x∈πX = PT.rec (snd (x ∈ˢ Lset β)) go (C.πX-member x x∈πX)
      where
      go : Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ x))
         → ⟨ x ∈ˢ Lset β ⟩
      go (y , y∈M , e) = PT.rec (snd (x ∈ˢ Lset β)) go₂ (cover y y∈M)
        where
        go₂ : Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩)
            → ⟨ x ∈ˢ Lset β ⟩
        go₂ (γ , oγ , γ∈πX , h) =
          Lset-mono {α = β} {β = γ} (ord∈β γ γ∈πX oγ)
            (subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) e h)

    -- The forward inclusion: every level below beta lies in the
    -- collapse, via the transfer's levelIn and the successor closure.
    Lβ⊆πX : (x : S) → ⟨ x ∈ˢ Lset β ⟩ → ⟨ x ∈ˢ C.πX ⟩
    Lβ⊆πX x x∈Lβ = PT.rec (snd (x ∈ˢ C.πX)) go (Lset-out β x x∈Lβ)
      where
      go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩)
         → ⟨ x ∈ˢ C.πX ⟩
      go (δ , δ∈β , x∈𝒟ₒδ) =
        C.πX-trans {x = Lset (sucV δ)} {y = x}
          (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟ₒδ)
          (levelIn (sucV δ) (suc-ord (β-ord δ δ∈β)) (β∈πX (sucV δ) (sucV∈β δ δ∈β)))

    -- The equality: the collapse is the level at beta.
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

The generator Lset α ∪ {x} and its stage facts: x is a member, the
generator lies in the stage, the generator is transitive when x is a
subset of the stage, and the empty set lies in the limit index.

```agda
module UnionKit (α lam x : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (α∈λ : ⟨ α ∈ˢ lam ⟩) (x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)
  (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩) (α∉ω : ⟨ α ∈ˢ ω ⟩ → Empty.⊥) where

  X : S
  X = Lset α ∪ ⁅ x ⁆s

  -- the union membership of a singleton member
  x∈sgl : ⟨ x ∈ₛ ⁅ x ⁆s ⟩
  x∈sgl = SetPackage.classification (SingletonPackage x) x .snd refl

  x∈X : ⟨ x ∈ˢ X ⟩
  x∈X = ∈∈ₛ {a = x} {b = X} .snd
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ x .snd
      ∣ ⁅ x ⁆s , (pairing-ax (Lset α) (⁅ x ⁆s) (⁅ x ⁆s) .snd ∣ inr refl ∣₁ , x∈sgl) ∣₁)

  Lα∈X : (z : S) → ⟨ z ∈ˢ Lset α ⟩ → ⟨ z ∈ˢ X ⟩
  Lα∈X z z∈Lα = ∈∈ₛ {a = z} {b = X} .snd
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ z .snd
      ∣ Lset α , (pairing-ax (Lset α) (⁅ x ⁆s) (Lset α) .snd ∣ inl refl ∣₁
                , ∈∈ₛ {a = z} {b = Lset α} .fst z∈Lα) ∣₁)

  sgl≡ : (z : S) → ⟨ z ∈ˢ ⁅ x ⁆s ⟩ → z ≡ x
  sgl≡ z z∈sgl = SetPackage.classification (SingletonPackage x) z .fst
    (∈∈ₛ {a = z} {b = ⁅ x ⁆s} .fst z∈sgl)

  X-mem : (z : S) → ⟨ z ∈ˢ X ⟩
        → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
  X-mem z z∈X = PT.rec (snd ((z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s))) go
    (union-ax ⁅ Lset α , ⁅ x ⁆s ⁆ z .fst
      (∈∈ₛ {a = z} {b = X} .fst z∈X))
    where
    go : Σ[ w ∈ S ] (⟨ w ∈ₛ ⁅ Lset α , ⁅ x ⁆s ⁆ ⟩ × ⟨ z ∈ₛ w ⟩)
       → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
    go (w , w∈ₛpair , z∈ₛw) = PT.rec
      (snd ((z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s))) go₂
      (pairing-ax (Lset α) (⁅ x ⁆s) w .fst w∈ₛpair)
      where
      go₂ : (w ≡ Lset α) ⊎ (w ≡ ⁅ x ⁆s)
          → ⟨ (z ∈ˢ Lset α) ⊔ (z ∈ˢ ⁅ x ⁆s) ⟩
      go₂ (inl e) = ∣ inl (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁
      go₂ (inr e) = ∣ inr (subst (λ u → ⟨ z ∈ˢ u ⟩) e (∈∈ₛ {a = z} {b = w} .snd z∈ₛw)) ∣₁

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

  -- 1 = sucV ∅ lies in the infinite ordinal alpha, and the empty set
  -- lies in the limit index.
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

THE HULL IS EXTENSIONAL (the `Mext` hypothesis of the collapse iso).
Two hull members that agree on the hull's memberships differ nowhere:
a global difference witness z ∈ x \ y would satisfy the difference
formula "v ∈ x ∧ v ∉ y" over the codes of x and y in the stage, so
hull-closed produces a hull member with the same property, and the
agreement hypothesis refutes it.  The codes come from the truncated
hull membership, eliminated into the proposition x ≡ y; no least-code
selection is needed.  The classical steps are the two directions of
extensionality contrapositive and the difference-witness extraction,
each one LEM on a proposition.

```agda
module HullExt (α : S) (ordα : IsOrd α)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
  (∅∈α : ⟨ ∅ ∈ˢ α ⟩) where

  module ASt = AtStage α ordα using ( module AbsL; module Hull; SL )
  module H = ASt.Hull X X⊆L ∅∈α using ( module T; Hull⊆L; hull-closed; hull-member )

  M : S
  M = H.T.Hull

  -- the inclusion with the truncated membership, at the levels the hull
  -- speaks
  testP : S → S → Type (ℓ-suc ℓ)
  testP x y = (z : S) → fst (z ∈ˢ x) → fst (z ∈ˢ y)

  subF : S → S → hProp (ℓ-suc ℓ)
  subF x y = ( testP x y
             , isPropΠ (λ z → isPropΠ (λ _ → snd (z ∈ˢ y))) )

  -- a global difference witness in one direction, classically: from
  -- ¬ (x ⊆ y) extract a member of x that is not a member of y
  diff-witness : (x y : S) → ((⟨ subF x y ⟩) → Empty.⊥)
               → ∥ Σ[ z ∈ S ] ((z ∈ᵗ x) × ((z ∈ᵗ y) → Empty.⊥)) ∥₁
  diff-witness x y ¬xy = go (lem P)
    where
    P : hProp (ℓ-suc ℓ)
    P = ( ∥ Σ[ z ∈ S ] ((z ∈ᵗ x) × ((z ∈ᵗ y) → Empty.⊥)) ∥₁ , squash₁ )
    go : ⟨ P ⟩ ⊎ (⟨ P ⟩ → Empty.⊥) → ⟨ P ⟩
    go (inl p) = p
    go (inr ¬p) = Empty.rec (¬xy (x⊆y))
      where
      x⊆y : ⟨ subF x y ⟩
      x⊆y z z∈x = Sum.rec (λ q → q)
        (λ nzy → Empty.rec (¬p ∣ z , (z∈x , nzy) ∣₁))
        (lem (z ∈ˢ y))

  -- extensionality contrapositive, in the two directions
  ext-contra : (x y : S) → (x ≡ y → Empty.⊥)
             → ((⟨ subF x y ⟩) → Empty.⊥) ⊎ ((⟨ subF y x ⟩) → Empty.⊥)
  ext-contra x y nxy = Sum.rec
    (λ hxy → inr (λ hyx → nxy (extensionalV (λ z → ⇔toPath (hxy z) (hyx z)))))
    (λ ¬hxy → inl ¬hxy)
    (lem (subF x y))

  -- the outer difference formula over the codes of the two hull members
  φ : (c d : H.T.Code) → Formula H.T.Code 1
  φ c d = (var zero ∈̇ con c) ∧̇ (¬̇ (var zero ∈̇ con d))

  -- the outer satisfaction from a global difference witness
  outer : (u v : S) (u∈M : u ∈ᵗ M)
        → (c d : H.T.Code) (ec : fst (H.T.val c) ≡ u) (ed : fst (H.T.val d) ≡ v)
        → (z : S) → (z ∈ᵗ u) → ((z ∈ᵗ v) → Empty.⊥)
        → ∥ Σ[ a ∈ ASt.SL ] ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ c d)) ⟩ ∥₁
  outer u v u∈M c d ec ed z zx nzy = ∣ a , sat ∣₁
    where
    z∈L : ⟨ z ∈ˢ Lset α ⟩
    z∈L = layer-trans (Lset-layer α) zx (H.Hull⊆L u u∈M)
    a : ASt.SL
    a = z , z∈L
    sat : ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ c d)) ⟩
    sat = ( subst (λ w → z ∈ᵗ w) (sym ec) zx
         , λ h → nzy (subst (λ w → z ∈ᵗ w) ed h) )

  -- the difference argument: hull-closed turns the outer witness into a
  -- hull member, and the agreement hypothesis refutes it
  refute : (x y : S) (x∈M : x ∈ᵗ M) (y∈M : y ∈ᵗ M)
         → (ag1 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
         → (c d : H.T.Code) (ec : fst (H.T.val c) ≡ x) (ed : fst (H.T.val d) ≡ y)
         → ((⟨ subF x y ⟩) → Empty.⊥) → Empty.⊥
  refute x y x∈M y∈M ag1 c d ec ed ¬xy = PT.rec Empty.isProp⊥ diff (diff-witness x y ¬xy)
    where
    diff : Σ[ z ∈ S ] ((z ∈ᵗ x) × ((z ∈ᵗ y) → Empty.⊥)) → Empty.⊥
    diff (z , zx , nzy) = PT.rec Empty.isProp⊥ go2 (H.hull-closed (φ c d) h)
      where
      h : ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val (φ c d))) ⟩
      h = outer x y x∈M c d ec ed z zx nzy
      go2 : Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩
                          × ⟨ (b ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ c d)) ⟩)
          → Empty.⊥
      go2 (b , b∈M , bsat) =
        nzy' (ag1 (fst b) b∈M (subst (λ w → ⟨ fst b ∈ˢ w ⟩) ec (fst bsat)))
        where
        nzy' : (fst b ∈ᵗ y → Empty.⊥)
        nzy' hy = snd bsat (subst (λ w → fst b ∈ᵗ w) (sym ed) hy)

  refute2 : (x y : S) (x∈M : x ∈ᵗ M) (y∈M : y ∈ᵗ M)
          → (ag2 : (z : S) → z ∈ᵗ M → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩)
          → (c d : H.T.Code) (ec : fst (H.T.val c) ≡ x) (ed : fst (H.T.val d) ≡ y)
          → ((⟨ subF y x ⟩) → Empty.⊥) → Empty.⊥
  refute2 x y x∈M y∈M ag2 c d ec ed ¬yx = PT.rec Empty.isProp⊥ diff (diff-witness y x ¬yx)
    where
    diff : Σ[ z ∈ S ] ((z ∈ᵗ y) × ((z ∈ᵗ x) → Empty.⊥)) → Empty.⊥
    diff (z , zy , nzx) = PT.rec Empty.isProp⊥ go2 (H.hull-closed (φ d c) h)
      where
      h : ⟨ [] ASt.AbsL.⊨ᵐ (∃̇ (mapFo H.T.val (φ d c))) ⟩
      h = outer y x y∈M d c ed ec z zy nzx
      go2 : Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩
                          × ⟨ (b ∷ []) ASt.AbsL.⊨ᵐ (mapFo H.T.val (φ d c)) ⟩)
          → Empty.⊥
      go2 (b , b∈M , bsat) =
        nzx' (ag2 (fst b) b∈M (subst (λ w → ⟨ fst b ∈ˢ w ⟩) ed (fst bsat)))
        where
        nzx' : (fst b ∈ᵗ x → Empty.⊥)
        nzx' hx = snd bsat (subst (λ w → fst b ∈ᵗ w) (sym ec) hx)

  hullExt : isExt M
  hullExt x y x∈M y∈M ag1 ag2 =
    PT.rec (isSetS x y) (λ cx → PT.rec (isSetS x y) (go cx) (H.hull-member y y∈M))
      (H.hull-member x x∈M)
    where
    go : Σ[ c ∈ H.T.Code ] (fst (H.T.val c) ≡ x)
       → Σ[ d ∈ H.T.Code ] (fst (H.T.val d) ≡ y) → x ≡ y
    go (c , ec) (d , ed) = Sum.rec (λ p → p) (λ np → Empty.rec (bad np))
      (lem ((x ≡ y) , isSetS x y))
      where
      bad : (x ≡ y → Empty.⊥) → Empty.⊥
      bad nxy = dir2 (dir1 nxy)
        where
        dir1 : (x ≡ y → Empty.⊥)
             → ((⟨ subF x y ⟩) → Empty.⊥) ⊎ ((⟨ subF y x ⟩) → Empty.⊥)
        dir1 = ext-contra x y
        dir2 : ((⟨ subF x y ⟩) → Empty.⊥) ⊎ ((⟨ subF y x ⟩) → Empty.⊥) → Empty.⊥
        dir2 (inl ¬xy) = refute x y x∈M y∈M ag1 c d ec ed ¬xy
        dir2 (inr ¬yx) = refute2 x y x∈M y∈M ag2 c d ec ed ¬yx
```

## The carry across the collapse

THE GENERIC UNPACK.  [LJ-1.680] Probe680.agda:48-146.  Two ∃̇ and
two ≐ unpacked at a generic transitive carrier, then abs₀ at a
generic 3-slot Δ₀ formula.

Two ∃̇ bind value then parameter; two ≐ pin those binders to
constants; the remaining free slot is the witness.

```agda
pin₃ : {ℓc : Level} {K : Type ℓc} → Formula K 3 → K → K → Formula K 1
pin₃ φ ca cp =
  ∃̇ (∃̇ (φ ∧̇ (var zero ≐ con ca) ∧̇ (var (suc zero) ≐ con cp)))

pin₃-map : {ℓc ℓd : Level} {K : Type ℓc} {K' : Type ℓd}
           (f : K → K') (φ : Formula K 3) (ca cp : K)
         → mapFo f (pin₃ φ ca cp) ≡ pin₃ (mapFo f φ) (f ca) (f cp)
pin₃-map f φ ca cp = refl

module Unpack (U : S) (Utr : isTrans U) where

  module Ab = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ U) Utr using (SM; abs₀; _⊨ᵐ_)

  read : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : Ab.SM ^ n)
       → (δ Ab.⊨ᵐ embed φ) ≡ (map fst δ ⊨ₚ φ)
  read {n} {φ} dφ δ =
      Ab.abs₀ (mapΔ₀ Empty.rec* dφ) δ
    ∙ embed-⊨ (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ {K = Ab.SM} fst φ (map fst δ)
    ∙ cong (λ ι → SemV.At._⊨_ (⊥* {ℓ-suc ℓ}) ι (map fst δ) φ)
           (funExt (λ b → Empty.rec* b))

  unpack-pin :
      (φ : Formula Ab.SM 3)
    → (ca cp a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ φ ca cp) ⟩
    → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
         ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
         × (fst y ≡ fst ca)
         × (fst x ≡ fst cp) ) ∥₁
  unpack-pin φ ca cp a h =
    PT.rec squash₁ outer h
    where
    outer : Σ[ x ∈ Ab.SM ]
              ⟨ (x ∷ a ∷ []) Ab.⊨ᵐ
                  (∃̇ (φ ∧̇ (var zero ≐ con ca)
                         ∧̇ (var (suc zero) ≐ con cp))) ⟩
          → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
               ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
               × (fst y ≡ fst ca)
               × (fst x ≡ fst cp) ) ∥₁
    outer (x , hx) =
      PT.rec squash₁ inner hx
      where
      inner : Σ[ y ∈ Ab.SM ]
                ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ
                    (φ ∧̇ (var zero ≐ con ca)
                       ∧̇ (var (suc zero) ≐ con cp)) ⟩
            → ∥ Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
                 ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ φ ⟩
                 × (fst y ≡ fst ca)
                 × (fst x ≡ fst cp) ) ∥₁
      inner (y , hy) = ∣ y , x , hy .fst , hy .snd .fst , hy .snd .snd ∣₁

  convert-generic :
      {φ : Formula (⊥* {ℓ-suc ℓ}) 3}
    → Δ₀ φ
    → (ca cp a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ (embed φ) ca cp) ⟩
    → ⟨ (fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩
  convert-generic {φ} dφ ca cp a h =
    PT.rec (snd ((fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ)) go
           (unpack-pin (embed φ) ca cp a h)
    where
    go : Σ[ y ∈ Ab.SM ] Σ[ x ∈ Ab.SM ]
           ( ⟨ (y ∷ x ∷ a ∷ []) Ab.⊨ᵐ embed φ ⟩
           × (fst y ≡ fst ca)
           × (fst x ≡ fst cp) )
       → ⟨ (fst ca ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩
    go (y , x , hφ , ey , ex) =
      subst (λ v → ⟨ (v ∷ fst cp ∷ fst a ∷ []) ⊨ₚ φ ⟩) ey
        (subst (λ p → ⟨ (fst y ∷ p ∷ fst a ∷ []) ⊨ₚ φ ⟩) ex
          (subst ⟨_⟩ (read dφ (y ∷ x ∷ a ∷ [])) hφ))

  convert-at-true = convert-generic {φ = ⊤̇} δ-⊤
```

THE HULL CONVERT.  [LJ-1.689] Probe689.agda:37-71, module `Convert`
renamed `HullConvert`.  From hull-closed's hypothesis form
`mapFo val (inBound ca cp)` onto the generic unpack, taking the
equation `mapFo val (mapFo slide φ) ≡ embed φ` as a hypothesis.

```agda
module HullConvert (U : S) (Utr : isTrans U) where
  open Unpack U Utr hiding ( convert-generic; convert-at-true )

  inBound : {ℓc : Level} {K : Type ℓc}
          → Formula (⊥* {ℓ-suc ℓ}) 3
          → (⊥* {ℓ-suc ℓ} → K) → K → K → Formula K 1
  inBound φ slide ca cp = pin₃ (mapFo slide φ) ca cp

  hull-convert :
      {ℓc : Level} {K : Type ℓc}
      {φ : Formula (⊥* {ℓ-suc ℓ}) 3}
    → Δ₀ φ
    → (slide : ⊥* {ℓ-suc ℓ} → K)
    → (val : K → Ab.SM)
    → (eq : mapFo val (mapFo slide φ) ≡ embed φ)
    → (ca cp : K) (a : Ab.SM)
    → ⟨ (a ∷ []) Ab.⊨ᵐ (mapFo val (inBound φ slide ca cp)) ⟩
    → ⟨ (fst (val ca) ∷ fst (val cp) ∷ fst a ∷ []) ⊨ₚ φ ⟩
  hull-convert {φ = φ} dφ slide val eq ca cp a h =
    Unpack.convert-generic U Utr {φ = φ} dφ (val ca) (val cp) a
      (subst (λ ψ → ⟨ (a ∷ []) Ab.⊨ᵐ (pin₃ ψ (val ca) (val cp)) ⟩) eq
        (subst (λ ψ → ⟨ (a ∷ []) Ab.⊨ᵐ ψ ⟩)
               (pin₃-map val (mapFo slide φ) ca cp)
               h))

module Frame (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ using (module ASt; module C; module Condense; module H; M)
  module ASt = HS.ASt using (module AbsL; module AtM; Ltr; SL)
  module A = ASt.AtM HS.M HS.H.Hull⊆L using (Elementary; SM; inL)

  -- SECTION 2.  THE CARRY.  Ambient truth at hull members becomes
  -- ambient truth at their collapse values: (1) down into the hull by
  -- `elem`, (2) across by the collapse iso `iso-inv`, (3) out of the
  -- collapse by Δ₀ absoluteness at the transitive range `πX`.
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

    -- THE CARRY ITSELF.
    push : {n : ℕ} {φ : Formula (⊥* {ℓ-suc ℓ}) n} → Δ₀ φ → (δ : A.SM ^ n)
         → ⟨ map fst δ ⊨ₚ φ ⟩
         → ⟨ map fst (map CIso.I.g δ) ⊨ₚ φ ⟩
    push {n} {φ} dφ δ h =
      subst ⟨_⟩ (atπ dφ (map CIso.I.g δ))
        (subst (λ ψ → ⟨ map CIso.I.g δ CIso.I.⊨ᵖᵐ ψ ⟩)
               (embed-map CIso.I.g φ)
               (CIso.I.iso-inv n (embed φ) δ (subst ⟨_⟩ (sym (atM dφ δ)) h)))
```
