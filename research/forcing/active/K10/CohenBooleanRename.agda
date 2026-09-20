{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.Data.Empty as Empty
import K4.Algebra
import K4.Implication
import K9.BooleanAtomic
import K9.NameGround
import K10.CohenValSeam

module K10.CohenBooleanRename
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula ; Term ; var ; con ; _∈̇_ ; _≐_ ; _∧̇_ ; _∨̇_ ; _⇒̇_
        ; ⊥̇ ; ∃̇_ ; ∀̇_ ; ∃̇∈ ; ∀̇∈ )
open import FOL.Manipulation.Renaming using ( renameFo ; renameTm ; liftρ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional ; ≈ˢ-paths )
module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module IC )
open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BAT.B
  BAT.IC.codedLattice BAT.IC.codedComplement
  using ( ≤ᴮ-antisym ; _⇒ᴮ_ )
module VS = K10.CohenValSeam 𝒮 families accessible images pow κ w lem paths

open VS using ( Src ; Nameᴮ ; Envᴮ ; val )
open BAT.Atomic using () renaming ( _∈ᴮ_ to mem ; _≈ᴮ_ to eq )

tabulate : ∀ {n} {A : Type ℓ} → (Fin n → A) → Vec A n
tabulate {n = zero} f = []
tabulate {n = suc n} f = f zero ∷ tabulate (λ i → f (suc i))

lookup-tabulate : ∀ {n} {A : Type ℓ} (f : Fin n → A) (i : Fin n)
  → lookup i (tabulate f) ≡ f i
lookup-tabulate f zero = refl
lookup-tabulate f (suc i) = lookup-tabulate (λ j → f (suc j)) i

renameEnv : ∀ {n m} → (Fin n → Fin m) → Envᴮ m → Envᴮ n
renameEnv ρ ν = tabulate (λ i → lookup (ρ i) ν)

lookup-rename : ∀ {n m} (ρ : Fin n → Fin m) (ν : Envᴮ m) (i : Fin n)
  → lookup i (renameEnv ρ ν) ≡ lookup (ρ i) ν
lookup-rename ρ ν i = lookup-tabulate (λ j → lookup (ρ j) ν) i

renameEnv-lift : ∀ {n m} (ρ : Fin n → Fin m) (ν : Envᴮ m) (σ : Nameᴮ)
  → renameEnv (liftρ ρ) (σ ∷ ν) ≡ (σ ∷ renameEnv ρ ν)
renameEnv-lift ρ ν σ = refl

idx : ∀ {n} → Term (⊥* {ℓ}) n → Fin n
idx (var i) = i
idx (con e) = Empty.rec* e

idx-rename : ∀ {n m} (ρ : Fin n → Fin m) (t : Term (⊥* {ℓ}) n)
  → idx (renameTm ρ t) ≡ ρ (idx t)
idx-rename ρ (var i) = refl
idx-rename ρ (con e) = Empty.rec* e

term-var : ∀ {n} (t : Term (⊥* {ℓ}) n) → t ≡ var (idx t)
term-var (var i) = refl
term-var (con e) = Empty.rec* e

atom-∈ : ∀ {n} (t u : Term (⊥* {ℓ}) n) (ν : Envᴮ n)
  → val (t ∈̇ u) ν ≡ mem (fst (lookup (idx t) ν)) (fst (lookup (idx u) ν))
atom-∈ (var i) (var j) ν = VS.law-∈ i j ν
atom-∈ (con e) _ ν = Empty.rec* e
atom-∈ (var _) (con e) ν = Empty.rec* e

atom-≐ : ∀ {n} (t u : Term (⊥* {ℓ}) n) (ν : Envᴮ n)
  → val (t ≐ u) ν ≡ eq (fst (lookup (idx t) ν)) (fst (lookup (idx u) ν))
atom-≐ (var i) (var j) ν = VS.law-≐ i j ν
atom-≐ (con e) _ ν = Empty.rec* e
atom-≐ (var _) (con e) ν = Empty.rec* e

bound-idx : ∀ {n} (t : Term (⊥* {ℓ}) n) (ν : Envᴮ n)
  → ∀̇∈ t ≡ ∀̇∈ (var (idx t))
bound-idx (var i) ν = refl
bound-idx (con e) ν = Empty.rec* e

val-rename : ∀ {n m} (ρ : Fin n → Fin m) (φ : Src n) (ν : Envᴮ m)
  → val (renameFo ρ φ) ν ≡ val φ (renameEnv ρ ν)
val-rename ρ (t ∈̇ u) ν =
  atom-∈ (renameTm ρ t) (renameTm ρ u) ν
  ∙ cong₂ (λ i j → mem (fst (lookup i ν)) (fst (lookup j ν)))
      (idx-rename ρ t) (idx-rename ρ u)
  ∙ cong₂ (λ σ τ → mem (fst σ) (fst τ))
      (sym (lookup-rename ρ ν (idx t))) (sym (lookup-rename ρ ν (idx u)))
  ∙ sym (atom-∈ t u (renameEnv ρ ν))
val-rename ρ (t ≐ u) ν =
  atom-≐ (renameTm ρ t) (renameTm ρ u) ν
  ∙ cong₂ (λ i j → eq (fst (lookup i ν)) (fst (lookup j ν)))
      (idx-rename ρ t) (idx-rename ρ u)
  ∙ cong₂ (λ σ τ → eq (fst σ) (fst τ))
      (sym (lookup-rename ρ ν (idx t))) (sym (lookup-rename ρ ν (idx u)))
  ∙ sym (atom-≐ t u (renameEnv ρ ν))
val-rename ρ (φ ∧̇ ψ) ν =
  VS.law-∧ (renameFo ρ φ) (renameFo ρ ψ) ν
  ∙ cong₂ _⊓ᴮ_ (val-rename ρ φ ν) (val-rename ρ ψ ν)
  ∙ sym (VS.law-∧ φ ψ (renameEnv ρ ν))
  where open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ )
val-rename ρ (φ ∨̇ ψ) ν =
  VS.law-∨ (renameFo ρ φ) (renameFo ρ ψ) ν
  ∙ cong₂ _⊔ᴮ_ (val-rename ρ φ ν) (val-rename ρ ψ ν)
  ∙ sym (VS.law-∨ φ ψ (renameEnv ρ ν))
  where open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊔ᴮ_ )
val-rename ρ (φ ⇒̇ ψ) ν =
  VS.law-⇒ (renameFo ρ φ) (renameFo ρ ψ) ν
  ∙ cong₂ _⇒ᴮ_ (val-rename ρ φ ν) (val-rename ρ ψ ν)
  ∙ sym (VS.law-⇒ φ ψ (renameEnv ρ ν))
val-rename ρ ⊥̇ ν = VS.law-⊥ ν ∙ sym (VS.law-⊥ (renameEnv ρ ν))
val-rename ρ (∃̇ φ) ν = ≤ᴮ-antisym le ge
  where
  le : ⟨ val (∃̇ renameFo (liftρ ρ) φ) ν ≤ᴮ val (∃̇ φ) (renameEnv ρ ν) ⟩
  le = VS.law-∃-lub (renameFo (liftρ ρ) φ) ν (val (∃̇ φ) (renameEnv ρ ν))
    (λ σ → subst (λ z → ⟨ z ≤ᴮ val (∃̇ φ) (renameEnv ρ ν) ⟩)
      (sym (val-rename (liftρ ρ) φ (σ ∷ ν)
            ∙ cong (val φ) (renameEnv-lift ρ ν σ)))
      (VS.law-∃-ub φ (renameEnv ρ ν) σ))
  ge : ⟨ val (∃̇ φ) (renameEnv ρ ν) ≤ᴮ val (∃̇ renameFo (liftρ ρ) φ) ν ⟩
  ge = VS.law-∃-lub φ (renameEnv ρ ν) (val (∃̇ renameFo (liftρ ρ) φ) ν)
    (λ σ → subst (λ z → ⟨ z ≤ᴮ val (∃̇ renameFo (liftρ ρ) φ) ν ⟩)
      (val-rename (liftρ ρ) φ (σ ∷ ν)
        ∙ cong (val φ) (renameEnv-lift ρ ν σ))
      (VS.law-∃-ub (renameFo (liftρ ρ) φ) ν σ))
val-rename ρ (∀̇ φ) ν = ≤ᴮ-antisym le ge
  where
  le : ⟨ val (∀̇ renameFo (liftρ ρ) φ) ν ≤ᴮ val (∀̇ φ) (renameEnv ρ ν) ⟩
  le = VS.law-∀-glb φ (renameEnv ρ ν) (val (∀̇ renameFo (liftρ ρ) φ) ν)
    (λ σ → subst (λ z → ⟨ val (∀̇ renameFo (liftρ ρ) φ) ν ≤ᴮ z ⟩)
      (val-rename (liftρ ρ) φ (σ ∷ ν) ∙ cong (val φ) (renameEnv-lift ρ ν σ))
      (VS.law-∀-lb (renameFo (liftρ ρ) φ) ν σ))
  ge : ⟨ val (∀̇ φ) (renameEnv ρ ν) ≤ᴮ val (∀̇ renameFo (liftρ ρ) φ) ν ⟩
  ge = VS.law-∀-glb (renameFo (liftρ ρ) φ) ν (val (∀̇ φ) (renameEnv ρ ν))
    (λ σ → subst (λ z → ⟨ val (∀̇ φ) (renameEnv ρ ν) ≤ᴮ z ⟩)
      (sym (val-rename (liftρ ρ) φ (σ ∷ ν)))
      (subst (λ μ → ⟨ val (∀̇ φ) (renameEnv ρ ν) ≤ᴮ val φ μ ⟩)
        (sym (renameEnv-lift ρ ν σ))
        (VS.law-∀-lb φ (renameEnv ρ ν) σ)))
val-rename ρ (∃̇∈ t φ) ν =
  cong₂ (λ u ψ → val (∃̇∈ u ψ) ν) (term-var (renameTm ρ t)) refl
  ∙ body (idx t) (idx-rename ρ t)
  ∙ cong (λ u → val (∃̇∈ u φ) (renameEnv ρ ν)) (sym (term-var t))
  where
  open K4.Algebra.Lattice BAT.IC.codedLattice using ( _⊓ᴮ_ )
  body : (i : Fin _) (eqi : idx (renameTm ρ t) ≡ ρ i)
    → val (∃̇∈ (var (idx (renameTm ρ t))) (renameFo (liftρ ρ) φ)) ν
      ≡ val (∃̇∈ (var i) φ) (renameEnv ρ ν)
  body i eqi = ≤ᴮ-antisym le ge
    where
    mem-idx : (σ : Nameᴮ)
      → mem (fst σ) (fst (lookup (idx (renameTm ρ t)) ν))
        ≡ mem (fst σ) (fst (lookup i (renameEnv ρ ν)))
    mem-idx σ =
      cong (λ j → mem (fst σ) (fst (lookup j ν))) eqi
      ∙ cong (λ τ → mem (fst σ) (fst τ)) (sym (lookup-rename ρ ν i))
    body-eq : (σ : Nameᴮ)
      → val (renameFo (liftρ ρ) φ) (σ ∷ ν)
        ≡ val φ (σ ∷ renameEnv ρ ν)
    body-eq σ =
      val-rename (liftρ ρ) φ (σ ∷ ν) ∙ cong (val φ) (renameEnv-lift ρ ν σ)
    le = VS.law-∃∈-lub (idx (renameTm ρ t)) (renameFo (liftρ ρ) φ) ν
      (val (∃̇∈ (var i) φ) (renameEnv ρ ν))
      (λ σ → subst
        (λ mb → ⟨ (fst mb ⊓ᴮ snd mb) ≤ᴮ val (∃̇∈ (var i) φ) (renameEnv ρ ν) ⟩)
        (cong₂ _,_ (sym (mem-idx σ)) (sym (body-eq σ)))
        (VS.law-∃∈-ub i φ (renameEnv ρ ν) σ))
    ge = VS.law-∃∈-lub i φ (renameEnv ρ ν)
      (val (∃̇∈ (var (idx (renameTm ρ t))) (renameFo (liftρ ρ) φ)) ν)
      (λ σ → subst
        (λ mb → ⟨ (fst mb ⊓ᴮ snd mb)
                  ≤ᴮ val (∃̇∈ (var (idx (renameTm ρ t)))
                    (renameFo (liftρ ρ) φ)) ν ⟩)
        (cong₂ _,_ (mem-idx σ) (body-eq σ))
        (VS.law-∃∈-ub (idx (renameTm ρ t)) (renameFo (liftρ ρ) φ) ν σ))
val-rename ρ (∀̇∈ t φ) ν =
  cong₂ (λ u ψ → val (∀̇∈ u ψ) ν) (term-var (renameTm ρ t)) refl
  ∙ body (idx t) (idx-rename ρ t)
  ∙ cong (λ u → val (∀̇∈ u φ) (renameEnv ρ ν)) (sym (term-var t))
  where
  body : (i : Fin _) (eqi : idx (renameTm ρ t) ≡ ρ i)
    → val (∀̇∈ (var (idx (renameTm ρ t))) (renameFo (liftρ ρ) φ)) ν
      ≡ val (∀̇∈ (var i) φ) (renameEnv ρ ν)
  body i eqi = ≤ᴮ-antisym le ge
    where
    mem-idx : (σ : Nameᴮ)
      → mem (fst σ) (fst (lookup (idx (renameTm ρ t)) ν))
        ≡ mem (fst σ) (fst (lookup i (renameEnv ρ ν)))
    mem-idx σ =
      cong (λ j → mem (fst σ) (fst (lookup j ν))) eqi
      ∙ cong (λ τ → mem (fst σ) (fst τ)) (sym (lookup-rename ρ ν i))
    body-eq : (σ : Nameᴮ)
      → val (renameFo (liftρ ρ) φ) (σ ∷ ν)
        ≡ val φ (σ ∷ renameEnv ρ ν)
    body-eq σ =
      val-rename (liftρ ρ) φ (σ ∷ ν) ∙ cong (val φ) (renameEnv-lift ρ ν σ)
    le = VS.law-∀∈-glb i φ (renameEnv ρ ν)
      (val (∀̇∈ (var (idx (renameTm ρ t))) (renameFo (liftρ ρ) φ)) ν)
      (λ σ → subst
        (λ mb → ⟨ val (∀̇∈ (var (idx (renameTm ρ t)))
                        (renameFo (liftρ ρ) φ)) ν
                  ≤ᴮ (fst mb ⇒ᴮ snd mb) ⟩)
        (cong₂ _,_ (mem-idx σ) (body-eq σ))
        (VS.law-∀∈-lb (idx (renameTm ρ t)) (renameFo (liftρ ρ) φ) ν σ))
    ge = VS.law-∀∈-glb (idx (renameTm ρ t)) (renameFo (liftρ ρ) φ) ν
      (val (∀̇∈ (var i) φ) (renameEnv ρ ν))
      (λ σ → subst
        (λ mb → ⟨ val (∀̇∈ (var i) φ) (renameEnv ρ ν)
                  ≤ᴮ (fst mb ⇒ᴮ snd mb) ⟩)
        (cong₂ _,_ (sym (mem-idx σ)) (sym (body-eq σ)))
        (VS.law-∀∈-lb i φ (renameEnv ρ ν) σ))
