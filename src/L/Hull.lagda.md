# The Skolem hull

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.Hull {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure; _↾_ )
open import FOL.Syntax
  using ( Formula; Term; con; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; Σ₁; δ-∧; δ-≐; δ-∃∈; σ-Δ₀; σ-∃ )
import FOL.Absoluteness
import FOL.Semantics
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import FOL.Manipulation.Renaming using ( renameTm )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
module SemV = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ
open SemV using ( _^_ )
open import V.Coding {ℓ} using ( pr )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Smallness {ℓ} using ( module InnerSmall )
open import L.Constructible {ℓ}
  using ( isTransV; IsOrd; isL; Lset; layer-trans; Lset-layer )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf; IsLeast )
open import L.Choice.Step {ℓ} lem using ( orderAt; Mem; relOf )
open import L.Choice.Order {ℓ} lem using ( module Bound; relL; relL-fill; relL-rep )
open import L.Coding.Base {ℓ} using ( prAt; Δ₀-prAt; prAt-adequate )

open import Cubical.Data.Vec using ( map; lookup )
open import Cubical.Data.Sigma using ( Σ≡Prop; _×_; _,_; Σ-cong-equiv-snd )
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Empty.Properties using ( isProp⊥ )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Foundations.Equiv
  using ( _≃_; equivFun; invEquiv; compEquiv; invEq; propBiimpl→Equiv )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; presentation )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

module AtS = SemV.At S id
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

      -- perf: the search unfolds to a descent; seal at birth, spec as the read
      -- lemma (R-36)
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

      Hull⊆L : (x : S) → ⟨ x ∈ˢ Hull ⟩ → ⟨ x ∈ˢ Lset α ⟩
      Hull⊆L x x∈H = PT.rec (snd (x ∈ˢ Lset α)) go x∈H
        where
        go : Σ[ p ∈ Σ[ φ ∈ Formula ⟪ X ⟫ 1 ] Witnessed-small φ ] (hullVal p ≡ x)
           → ⟨ x ∈ˢ Lset α ⟩
        go (p , q) = subst (λ z → ⟨ z ∈ˢ Lset α ⟩) q (snd (leastWit (p .fst) (p .snd)))

      -- reading the hull's membership back: a member of the hull is the value
      -- of the least-witness search at some formula-and-witness pair
      hull-member : (x : S) → ⟨ x ∈ˢ Hull ⟩
                  → ∥ Σ[ p ∈ Σ[ φ ∈ Formula ⟪ X ⟫ 1 ] Witnessed-small φ ]
                      (fst (leastWit (p .fst) (p .snd)) ≡ x) ∥₁
      hull-member x x∈H = x∈H

      leastWit-in-Hull : (φ : Formula ⟪ X ⟫ 1) (w : Witnessed-small φ)
                       → ⟨ fst (leastWit φ w) ∈ˢ Hull ⟩
      leastWit-in-Hull φ w = ∣ (φ , w) , refl ∣₁

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
