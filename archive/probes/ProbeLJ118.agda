{-# OPTIONS --cubical --safe --guardedness #-}
-- ProbeLJ118: [LJ-1.18] D-1 probe of the meta term algebra (fourth shape).
-- Generic in carrier, order, junk (P-l, P-h).  Throwaway.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module ProbeLJ118 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

  open import FOL.ZFStructure using ( ZFStructure; module hPropStructure )
  open import FOL.Syntax using ( Formula; ∃̇_ )
  import FOL.Semantics
  open import FOL.Manipulation.Parameters using ( countFo; constantsFo; absFo; ⊨-abs )
  open import FOL.Manipulation.Relabelling using ( mapFo; ⊨-map )
  open import L.WellOrder.Base {ℓ-suc ℓ} using ( SWO; leastOf )
  open import Cubical.Data.Vec using ( Vec; map; _++_; _∷_; [] )
  open import Cubical.Data.Sigma using ( _×_; _,_ )
  open import Cubical.Data.Sum using ( _⊎_; inl; inr; rec )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
  open import Cubical.HITs.CumulativeHierarchy.Base using ( V; sett )
  open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
  import Cubical.Data.Empty as Empty
  import FOL.Absoluteness
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import V.Presentation {ℓ} using ( member )
  open import L.Constructible {ℓ} using ( isTransV; IsOrd; Lset; layer-trans; Lset-layer )
  open import L.Choice.Step {ℓ} lem using ( orderAt )

  open hPropStructure 𝒮ᵥ hiding ( S )

  module TermAlgebra (𝒮 : ZFStructure (hPropAlgebra (ℓ-suc ℓ)))
                     (toSet : ZFStructure.S 𝒮 → V ℓ)
                     (wo : SWO (ZFStructure.S 𝒮))
                     (junk : ZFStructure.S 𝒮)
                     {K : Type ℓ} (emb : K → ZFStructure.S 𝒮) where

    open ZFStructure 𝒮 hiding ( _∈ˢ_ )
    private module Sem = FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮
    open Sem using ( _^_ )
    open Sem.At (⊥* {ℓ}) Empty.rec* using () renaming ( _⊨_ to _⊨₀_ )

    data Code : Type ℓ where
      base : K → Code
      wit  : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec Code k → Code

    Sat : (k : ℕ) → Formula (⊥* {ℓ}) (suc k) → Vec S k → Type (ℓ-suc ℓ)
    Sat k ψ vs = ∥ Σ[ a ∈ S ] ⟨ (a ∷ vs) ⊨₀ ψ ⟩ ∥₁

    search : (k : ℕ) (ψ : Formula (⊥* {ℓ}) (suc k)) (vs : Vec S k)
           → Sat k ψ vs → S
    search k ψ vs w = leastOf wo {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ vs) ⊨₀ ψ) w .fst

    mutual
      vals : {m : ℕ} → Vec Code m → Vec S m
      vals [] = []
      vals (c ∷ cs') = val c ∷ vals cs'

      val : Code → S
      val (base m) = emb m
      val (wit k ψ cs) = rec (search k ψ (vals cs)) (λ _ → junk)
                         (lem (Sat k ψ (vals cs) , squash₁))

    module AtCode = Sem.At Code val
    _⊨c_ : {n : ℕ} → S ^ n → Formula Code n → hProp (ℓ-suc ℓ)
    _⊨c_ = AtCode._⊨_

    sum-stuck : {X : Type (ℓ-suc ℓ)} (x : X) (px : isProp X)
              → (f : X → S) (g : (X → Empty.⊥) → S) (s : X ⊎ (X → Empty.⊥))
              → rec f g s ≡ f x
    sum-stuck x px f g (inl x') = sym (cong f (px x x'))
    sum-stuck x px f g (inr h)  = Empty.rec (h x)

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
           → ∥ Σ[ a ∈ S ] ⟨ (a ∷ []) ⊨c φ ⟩ ∥₁
           → ∥ Σ[ a ∈ S ] (⟨ toSet a ∈ˢ Hull ⟩ × ⟨ (a ∷ []) ⊨c φ ⟩) ∥₁
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
      a : S
      a = search (countFo φ) ψ (vals cs) w
      pa : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
      pa = leastOf wo {ℓ'' = ℓ-suc ℓ} lem (λ a → (a ∷ vals cs) ⊨₀ ψ) w .snd .fst
      a∈H : ⟨ toSet a ∈ˢ Hull ⟩
      a∈H = subst (λ z → ⟨ toSet z ∈ˢ Hull ⟩) (val-wit (countFo φ) ψ cs w)
              (inHull (wit (countFo φ) ψ cs))
      sat : ⟨ (a ∷ []) ⊨c φ ⟩
      sat = subst ⟨_⟩ (sym (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) 𝒮 val φ (a ∷ [])))
              (subst ⟨_⟩ (cong (λ vs → (a ∷ vs) ⊨₀ ψ) (vals≡map cs)) pa)

  module AtStage (α : V ℓ) (ordα : IsOrd α) where

    Ltr : isTransV (Lset α)
    Ltr = layer-trans (Lset-layer α)

    module AbsL = FOL.Absoluteness.Single 𝒮ᵥ (λ x → x ∈ˢ Lset α) Ltr

    SL = AbsL.SM

    wL = orderAt α ordα

    module Hull (X : V ℓ) (X⊆L : (x : V ℓ) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset α ⟩)
                 (junk : SL) where

      inStg : ⟪ X ⟫ → SL
      inStg m = ⟪ X ⟫↪ m , X⊆L (⟪ X ⟫↪ m) (member X m)

      module T = TermAlgebra AbsL.𝒮M fst wL junk {K = ⟪ X ⟫} inStg
      open T using ( Code; val; Hull; closed; _⊨c_ )

      hullClosed : (φ : Formula Code 1) → ⟨ [] AbsL.⊨ᵐ (∃̇ (mapFo val φ)) ⟩
                 → ∥ Σ[ a ∈ SL ] (⟨ fst a ∈ˢ Hull ⟩
                                × ⟨ (a ∷ []) AbsL.⊨ᵐ (mapFo val φ) ⟩) ∥₁
      hullClosed φ h = PT.map (λ { (a , a∈H , sat) → a , a∈H ,
        subst ⟨_⟩ (sym (⊨-map (hPropAlgebra (ℓ-suc ℓ)) AbsL.𝒮M val id φ (a ∷ []))) sat })
        (T.closed φ w')
        where
        w' : ∥ Σ[ b ∈ SL ] ⟨ (b ∷ []) ⊨c φ ⟩ ∥₁
        w' = PT.map (λ { (b , hb) →
          b , subst ⟨_⟩ (⊨-map (hPropAlgebra (ℓ-suc ℓ)) AbsL.𝒮M val id φ (b ∷ [])) hb }) h
