{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import CodedVocabulary
import K4.Compile
import K4.AtomicGraph

module K10.CohenGoodFormula
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula ; var ; _∈̇_ ; ∀̇_ ; _⇒̇_ ; _∧̇_ ; ∃̇_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( _^_ ; module At )
open At (ZFStructure.S 𝒮) id using ( _⊨_ )
open import CodedVocabulary 𝒮 using ( isKPairΔ ; prAtˢ )
open import Cubical.Foundations.HLevels using ( isPropΠ ; isProp× )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module KIT = K4.Compile 𝒮 ext paths
  using ( _⊆̇_ ; ⊆̇-reading ; meetAtˢ ; meetΔ ; meetAtˢ-reading )
module AG = K4.AtomicGraph 𝒮 paths
  using ( entryΔ ; entryAtˢ ; entryAtˢ-reading )

bump5 : ∀ {k} → Fin k → Fin (suc (suc (suc (suc (suc k)))))
bump5 s = suc (suc (suc (suc (suc s))))

upperAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
upperAt h x y w q =
  ∀̇ ( ∀̇ ( ∀̇ ( ∀̇ ( ∀̇ (
    (var (suc (suc (suc (suc zero)))) ∈̇ var (bump5 y))
      ⇒̇ ( prAtˢ (suc (suc (suc (suc zero)))) (suc (suc (suc zero)))
                (suc (suc zero)) )
      ⇒̇ ( (var (suc (suc zero))) ∈̇ (var (bump5 w)) )
      ⇒̇ ( (var (suc zero)) ∈̇ (var (bump5 w)) )
      ⇒̇ ( AG.entryAtˢ (bump5 h) (bump5 x) (suc (suc (suc zero))) (suc zero) )
      ⇒̇ ( KIT.meetAtˢ (bump5 w) (suc (suc zero)) (suc zero) zero )
      ⇒̇ ( KIT._⊆̇_ zero (bump5 q) )
  ) ) ) ) )

upperΔ : (H x y W q : S) → Ω
upperΔ H x y W q =
  ⋀ S (λ p → ⋀ S (λ z → ⋀ S (λ a → ⋀ S (λ e → ⋀ S (λ v →
    (p ∈ˢ y) ⇒ isKPairΔ p z a ⇒ (a ∈ˢ W) ⇒ (e ∈ˢ W) ⇒
    AG.entryΔ H x z e ⇒ KIT.meetΔ W a e v ⇒ (v ⊆ˢ q))))))

upperAt-reading : ∀ {k} (h x y w q : Fin k) (γ : S ^ k)
  → (γ ⊨ upperAt h x y w q)
    ≡ upperΔ (lookup h γ) (lookup x γ) (lookup y γ) (lookup w γ) (lookup q γ)
upperAt-reading h x y w q γ = refl

imgAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
imgAt h x y b w =
    (var b ∈̇ var w)
  ∧̇ upperAt h x y w b
  ∧̇ ∀̇ ( (var zero ∈̇ var (suc w))
          ⇒̇ upperAt (suc h) (suc x) (suc y) (suc w) zero
          ⇒̇ (KIT._⊆̇_ (suc b) zero) )

imgΔ : (H x y b W : S) → Ω
imgΔ H x y b W =
  (b ∈ˢ W)
    ⊓ upperΔ H x y W b
    ⊓ ⋀ S (λ q → (q ∈ˢ W) ⇒ upperΔ H x y W q ⇒ (b ⊆ˢ q))

imgAt-reading : ∀ {k} (h x y b w : Fin k) (γ : S ^ k)
  → (γ ⊨ imgAt h x y b w)
    ≡ imgΔ (lookup h γ) (lookup x γ) (lookup y γ) (lookup b γ) (lookup w γ)
imgAt-reading h x y b w γ = refl

lowerLeftAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
lowerLeftAt h x y w b =
  ∀̇ ( ∀̇ ( ∀̇ ( ∀̇ ( ∀̇ (
    (var (suc (suc (suc (suc zero)))) ∈̇ var (bump5 x))
      ⇒̇ ( prAtˢ (suc (suc (suc (suc zero))))
                (suc (suc (suc zero))) (suc (suc zero)) )
      ⇒̇ ( (var (suc (suc zero))) ∈̇ (var (bump5 w)) )
      ⇒̇ imgAt (bump5 h) (suc (suc (suc zero))) (bump5 y) (suc zero) (bump5 w)
      ⇒̇ ( KIT.meetAtˢ (bump5 w) (bump5 b) (suc (suc zero)) zero )
      ⇒̇ ( KIT._⊆̇_ zero (suc zero) )
  ) ) ) ) )

lowerRightAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
lowerRightAt h x y w b =
  ∀̇ ( ∀̇ ( ∀̇ ( ∀̇ ( ∀̇ (
    (var (suc (suc (suc (suc zero)))) ∈̇ var (bump5 y))
      ⇒̇ ( prAtˢ (suc (suc (suc (suc zero))))
                (suc (suc (suc zero))) (suc (suc zero)) )
      ⇒̇ ( (var (suc (suc zero))) ∈̇ (var (bump5 w)) )
      ⇒̇ imgAt (bump5 h) (suc (suc (suc zero))) (bump5 x) (suc zero) (bump5 w)
      ⇒̇ ( KIT.meetAtˢ (bump5 w) (bump5 b) (suc (suc zero)) zero )
      ⇒̇ ( KIT._⊆̇_ zero (suc zero) )
  ) ) ) ) )

lowerAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
lowerAt h x y w b = lowerLeftAt h x y w b ∧̇ lowerRightAt h x y w b

lowerΔ : (H x y W b : S) → Ω
lowerΔ H x y W b =
  ( ⋀ S (λ p → ⋀ S (λ z → ⋀ S (λ a → ⋀ S (λ c → ⋀ S (λ v →
      (p ∈ˢ x) ⇒ isKPairΔ p z a ⇒ (a ∈ˢ W) ⇒
      imgΔ H z y c W ⇒ KIT.meetΔ W b a v ⇒ (v ⊆ˢ c)))))))
  ⊓
  ( ⋀ S (λ p → ⋀ S (λ z → ⋀ S (λ a → ⋀ S (λ c → ⋀ S (λ v →
      (p ∈ˢ y) ⇒ isKPairΔ p z a ⇒ (a ∈ˢ W) ⇒
      imgΔ H z x c W ⇒ KIT.meetΔ W b a v ⇒ (v ⊆ˢ c)))))))

lowerAt-reading : ∀ {k} (h x y w b : Fin k) (γ : S ^ k)
  → (γ ⊨ lowerAt h x y w b)
    ≡ lowerΔ (lookup h γ) (lookup x γ) (lookup y γ)
                (lookup w γ) (lookup b γ)
lowerAt-reading h x y w b γ = refl

stepΔ : (H x y W b : S) → Ω
stepΔ H x y W b =
  (b ∈ˢ W)
    ⊓ lowerΔ H x y W b
    ⊓ ⋀ S (λ b' → (b' ∈ˢ W) ⇒ lowerΔ H x y W b' ⇒ (b' ⊆ˢ b))

goodΔ : (W C H : S) → Ω
goodΔ W C H =
  ⋀ S (λ x → (x ∈ˢ C) ⇒ ⋀ S (λ y → (y ∈ˢ C) ⇒
    ⋁ S (λ b → (b ∈ˢ W) ⊓ AG.entryΔ H x y b)))
  ⊓ ⋀ S (λ x → (x ∈ˢ C) ⇒ ⋀ S (λ y → (y ∈ˢ C) ⇒
    ⋀ S (λ b → AG.entryΔ H x y b ⇒ ((b ∈ˢ W)))))
  ⊓ ⋀ S (λ x → (x ∈ˢ C) ⇒ ⋀ S (λ y → (y ∈ˢ C) ⇒
    ⋀ S (λ b → AG.entryΔ H x y b ⇒ stepΔ H x y W b)))

stepAt : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k
stepAt h x y w b =
    (var b ∈̇ var w)
  ∧̇ lowerAt h x y w b
  ∧̇ ∀̇ ( (var zero ∈̇ var (suc w))
          ⇒̇ lowerAt (suc h) (suc x) (suc y) (suc w) zero
          ⇒̇ (KIT._⊆̇_ zero (suc b)) )

stepAt-reading : ∀ {k} (h x y w b : Fin k) (γ : S ^ k)
  → (γ ⊨ stepAt h x y w b)
    ≡ stepΔ (lookup h γ) (lookup x γ) (lookup y γ)
                (lookup w γ) (lookup b γ)
stepAt-reading h x y w b γ = refl

goodAt : ∀ {k} → Fin k → Fin k → Fin k → Formula S k
goodAt w c h =
  (∀̇ ( (var zero) ∈̇ (var (suc c))
    ⇒̇ ∀̇ ( (var zero) ∈̇ (var (suc (suc c)))
      ⇒̇ ∃̇ ( (var zero) ∈̇ (var (suc (suc (suc w))))
        ∧̇ AG.entryAtˢ (suc (suc (suc h))) (suc (suc zero)) (suc zero) zero ) ) ) )
  ∧̇ (∀̇ ( (var zero) ∈̇ (var (suc c))
    ⇒̇ ∀̇ ( (var zero) ∈̇ (var (suc (suc c)))
      ⇒̇ ∀̇ ( AG.entryAtˢ (suc (suc (suc h))) (suc (suc zero)) (suc zero) zero
        ⇒̇ (var zero) ∈̇ (var (suc (suc (suc w)))) ) ) ) )
  ∧̇ (∀̇ ( (var zero) ∈̇ (var (suc c))
    ⇒̇ ∀̇ ( (var zero) ∈̇ (var (suc (suc c)))
      ⇒̇ ∀̇ ( AG.entryAtˢ (suc (suc (suc h))) (suc (suc zero)) (suc zero) zero
        ⇒̇ stepAt (suc (suc (suc h))) (suc (suc zero)) (suc zero)
                  (suc (suc (suc w))) zero ) ) ) )

goodAt-reading : ∀ {k} (w c h : Fin k) (γ : S ^ k)
  → (γ ⊨ goodAt w c h)
    ≡ goodΔ (lookup w γ) (lookup c γ) (lookup h γ)
goodAt-reading w c h γ = refl
