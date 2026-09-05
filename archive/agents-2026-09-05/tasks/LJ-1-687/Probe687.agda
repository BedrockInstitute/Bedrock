{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.687] PROBE.  The supplier Describes still owes, beyond
-- the singleton family.  It runs in agents/tasks/LJ-1-687/ and
-- lands nothing in src/.
--
-- THE OBLIGATION the brief names is describes-supplier: Dee⊆stage
-- and StagePowDef at a pair, consumed by from-hyps.  The consumer
-- is [LJ-1.683]'s, imported, not rewritten (W2).  The singleton
-- family is [LJ-1.677]'s and is not re-inhabited.
--
-- WHAT IS SETTLED.
--   1. Describes, Dee⊆stage, StagePowDef, from-hyps: imported from
--      agents/tasks/LJ-1-683/Probe683.agda.
--   2. eq∈dee (W2): the singleton of a member is definable over
--      the carrier, by the equality formula.
--   3. classify (W2): LEM splits a subset of a pair into the four
--      subsets.
--   4. describes-supplier: from-hyps at a pair, from the four
--      stage-memberships the pair's definable powerset needs.
--
-- WHAT IS NOT SETTLED.
--   Describes at a member that is not a pair and not a singleton
--   and not a stage.  A generic y still owes StagePowDef and
--   Dee⊆stage.  A Formula Code 1 for 𝒟ₒ stays a second debt.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-687.Probe687 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; ⊤̇; ⊥̇ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ∋⊆ )
open import LJ-1-683.Probe683 {ℓ}
  using ( Describes ; Dee⊆stage ; StagePowDef ; from-hyps )

open import Cubical.Data.Sigma using ( _,_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; _⊆_; extensionality; ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax
        ; SingletonPackage; SetPackage  -- lint-agda: keep (SetPackage via record projection)
        )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- D-10.  THE PAIR FAMILY.
--
-- [LJ-1.683] paid from-hyps.  [LJ-1.677] paid the singleton family
-- with pair∈𝒟ₒ, not with from-hyps.  A pair {a, b} has four subsets
-- under LEM: ∅, {a}, {b}, {a, b}.  Each is definable over the pair.
-- from-hyps then carves them from a stage that already holds all
-- four.
-- =====================================================================

∈sgl : {a z : S} → ⟨ z ∈ˢ ⁅ a ⁆s ⟩ → z ≡ a
∈sgl {a} {z} h =
  SetPackage.classification (SingletonPackage a) z .fst
    (∈∈ₛ {a = z} {b = ⁅ a ⁆s} .fst h)

pair∈l : {a b : S} → ⟨ a ∈ˢ ⁅ a , b ⁆ ⟩
pair∈l {a} {b} = ∈∈ₛ {a = a} {b = ⁅ a , b ⁆} .snd
  (pairing-ax a b a .snd ∣ inl refl ∣₁)

pair∈r : {a b : S} → ⟨ b ∈ˢ ⁅ a , b ⁆ ⟩
pair∈r {a} {b} = ∈∈ₛ {a = b} {b = ⁅ a , b ⁆} .snd
  (pairing-ax a b b .snd ∣ inr refl ∣₁)

∈pair : {a b z : S} → ⟨ z ∈ˢ ⁅ a , b ⁆ ⟩ → ∥ (z ≡ a) ⊎ (z ≡ b) ∥₁
∈pair {a} {b} {z} h = pairing-ax a b z .fst
  (∈∈ₛ {a = z} {b = ⁅ a , b ⁆} .fst h)

-- W2: falsehood carves ∅ from an arbitrary carrier.  Copied from
-- agents/tasks/LJ-1-677/Probe677.agda:86-98.
empty∈dee : (A : S) → ⟨ ∅ ∈ˢ 𝒟ₒ A ⟩
empty∈dee A = 𝒟ₒ-intro A ∅ ∣ ⊥̇ , defSet⊥≡∅ ∣₁
  where
  module DefA = DefOf A
  defSet⊥≡∅ : DefA.defSet ⊥̇ ≡ ∅
  defSet⊥≡∅ = extensionality (DefA.defSet ⊥̇) ∅ (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefA.defSet ⊥̇ ⊆ ∅ ⟩
    sub₁ y y∈ₛ = PT.rec (snd (y ∈ₛ ∅))
      (λ { ((m , h) , q) → Empty.rec* h })
      (∈∈ₛ {a = y} {b = DefA.defSet ⊥̇} .snd y∈ₛ)
    sub₂ : ⟨ ∅ ⊆ DefA.defSet ⊥̇ ⟩
    sub₂ y y∈ₛ = Empty.rec (∅-empty y y∈ₛ)

-- W2: the tautology puts every carrier in its own definable powerset.
-- Copied from agents/tasks/LJ-1-668/Probe668.agda:79-80.
A∈𝒟ₒ : (A : S) → ⟨ A ∈ˢ 𝒟ₒ A ⟩
A∈𝒟ₒ A = 𝒟ₒ-intro A A ∣ ⊤̇ , DefOf.defSet⊤≡A A ∣₁

-- W2: the singleton of a member is definable over the carrier, by
-- the equality formula.  Instantiated at a pair below.
eq∈dee : (A c : S) → ⟨ c ∈ˢ A ⟩ → ⟨ ⁅ c ⁆s ∈ˢ 𝒟ₒ A ⟩
eq∈dee A c c∈ = 𝒟ₒ-intro A (⁅ c ⁆s) ∣ φ , defSet≡ ∣₁
  where
  module DefC = DefOf A
  mᶜ = ∈-asFiber {a = c} {b = A} c∈ .fst
  qᶜ : ⟪ A ⟫↪ mᶜ ≡ c
  qᶜ = ∈-asFiber {a = c} {b = A} c∈ .snd
  φ : Formula ⟪ A ⟫ 1
  φ = var zero ≐ con mᶜ

  defSet≡ : DefC.defSet φ ≡ ⁅ c ⁆s
  defSet≡ = extensionality (DefC.defSet φ) ⁅ c ⁆s (sub₁ , sub₂)
    where
    sub₁ : ⟨ DefC.defSet φ ⊆ ⁅ c ⁆s ⟩
    sub₁ w w∈ₛ = PT.rec (snd (w ∈ₛ ⁅ c ⁆s))
      (λ { ((m , h) , q) →
        let sat : ⟨ (DefC.ι m ∷ []) DefC.⊨ᵐ φ ⟩
            sat = subst ⟨_⟩ (DefC.defSet-mem φ m) ∣ (m , h) , refl ∣₁
        in subst (λ v → ⟨ v ∈ₛ ⁅ c ⁆s ⟩) q
             (SetPackage.classification (SingletonPackage c) (⟪ A ⟫↪ m) .snd
               (sat ∙ qᶜ)) })
      (∈∈ₛ {a = w} {b = DefC.defSet φ} .snd w∈ₛ)

    sub₂ : ⟨ ⁅ c ⁆s ⊆ DefC.defSet φ ⟩
    sub₂ w w∈ₛ =
      subst (λ v → ⟨ v ∈ₛ DefC.defSet φ ⟩)
        (sym (SetPackage.classification (SingletonPackage c) w .fst w∈ₛ))
        (∈∈ₛ {a = c} {b = DefC.defSet φ} .fst c∈def)
      where
      c∈def : ⟨ c ∈ˢ DefC.defSet φ ⟩
      c∈def = subst (λ v → ⟨ v ∈ˢ DefC.defSet φ ⟩) qᶜ
        (subst ⟨_⟩ (sym (DefC.defSet-mem φ mᶜ)) refl)

-- W2: LEM classifies a subset of a pair as one of the four subsets.
classify :
    (a b x : S)
  → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ ⁅ a , b ⁆ ⟩)
  → (x ≡ ∅) ⊎ ((x ≡ ⁅ a ⁆s) ⊎ ((x ≡ ⁅ b ⁆s) ⊎ (x ≡ ⁅ a , b ⁆)))
classify a b x x⊆y = from (lem (a ∈ˢ x)) (lem (b ∈ˢ x))
  where
  from : ⟨ a ∈ˢ x ⟩ ⊎ (⟨ a ∈ˢ x ⟩ → Empty.⊥)
       → ⟨ b ∈ˢ x ⟩ ⊎ (⟨ b ∈ˢ x ⟩ → Empty.⊥)
       → (x ≡ ∅) ⊎ ((x ≡ ⁅ a ⁆s) ⊎ ((x ≡ ⁅ b ⁆s) ⊎ (x ≡ ⁅ a , b ⁆)))
  from (inl a∈x) (inl b∈x) = inr (inr (inr x≡pair))
    where
    x≡pair : x ≡ ⁅ a , b ⁆
    x≡pair = extensionality x ⁅ a , b ⁆ (xs₁ , xs₂)
      where
      xs₁ : ⟨ x ⊆ ⁅ a , b ⁆ ⟩
      xs₁ z z∈ₛ = ∈∈ₛ {a = z} {b = ⁅ a , b ⁆} .fst
        (x⊆y z (∈∈ₛ {a = z} {b = x} .snd z∈ₛ))
      xs₂ : ⟨ ⁅ a , b ⁆ ⊆ x ⟩
      xs₂ z z∈ₛ = PT.rec (snd (z ∈ₛ x))
        (λ { (inl e) → subst (λ w → ⟨ w ∈ₛ x ⟩) (sym e)
                         (∈∈ₛ {a = a} {b = x} .fst a∈x)
           ; (inr e) → subst (λ w → ⟨ w ∈ₛ x ⟩) (sym e)
                         (∈∈ₛ {a = b} {b = x} .fst b∈x) })
        (pairing-ax a b z .fst z∈ₛ)
  from (inl a∈x) (inr b∉x) = inr (inl x≡sgla)
    where
    x≡sgla : x ≡ ⁅ a ⁆s
    x≡sgla = extensionality x (⁅ a ⁆s) (xs₁ , xs₂)
      where
      xs₁ : ⟨ x ⊆ ⁅ a ⁆s ⟩
      xs₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ⁅ a ⁆s))
        (λ { (inl e) → SetPackage.classification (SingletonPackage a) z .snd e
           ; (inr e) → Empty.rec (b∉x (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x)) })
        (∈pair (x⊆y z z∈x))
        where
        z∈x : ⟨ z ∈ˢ x ⟩
        z∈x = ∈∈ₛ {a = z} {b = x} .snd z∈ₛ
      xs₂ : ⟨ ⁅ a ⁆s ⊆ x ⟩
      xs₂ z z∈ₛ = subst (λ w → ⟨ w ∈ₛ x ⟩)
        (sym (∈sgl (∈∈ₛ {a = z} {b = ⁅ a ⁆s} .snd z∈ₛ)))
        (∈∈ₛ {a = a} {b = x} .fst a∈x)
  from (inr a∉x) (inl b∈x) = inr (inr (inl x≡sglb))
    where
    x≡sglb : x ≡ ⁅ b ⁆s
    x≡sglb = extensionality x (⁅ b ⁆s) (xs₁ , xs₂)
      where
      xs₁ : ⟨ x ⊆ ⁅ b ⁆s ⟩
      xs₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ⁅ b ⁆s))
        (λ { (inl e) → Empty.rec (a∉x (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x))
           ; (inr e) → SetPackage.classification (SingletonPackage b) z .snd e })
        (∈pair (x⊆y z z∈x))
        where
        z∈x : ⟨ z ∈ˢ x ⟩
        z∈x = ∈∈ₛ {a = z} {b = x} .snd z∈ₛ
      xs₂ : ⟨ ⁅ b ⁆s ⊆ x ⟩
      xs₂ z z∈ₛ = subst (λ w → ⟨ w ∈ₛ x ⟩)
        (sym (∈sgl (∈∈ₛ {a = z} {b = ⁅ b ⁆s} .snd z∈ₛ)))
        (∈∈ₛ {a = b} {b = x} .fst b∈x)
  from (inr a∉x) (inr b∉x) = inl x≡∅
    where
    x≡∅ : x ≡ ∅
    x≡∅ = extensionality x ∅ (xe₁ , xe₂)
      where
      xe₁ : ⟨ x ⊆ ∅ ⟩
      xe₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ∅))
        (λ { (inl e) → Empty.rec (a∉x (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x))
           ; (inr e) → Empty.rec (b∉x (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x)) })
        (∈pair (x⊆y z z∈x))
        where
        z∈x : ⟨ z ∈ˢ x ⟩
        z∈x = ∈∈ₛ {a = z} {b = x} .snd z∈ₛ
      xe₂ : ⟨ ∅ ⊆ x ⟩
      xe₂ z z∈ₛ = Empty.rec (∅-empty z z∈ₛ)

-- StagePowDef at a pair.  The stage membership of x is unused:
-- every subset of a pair is definable over the pair, under LEM.
pair-spd : (σ a b : S) → StagePowDef σ (⁅ a , b ⁆)
pair-spd σ a b x _ x⊆ = go (classify a b x x⊆ˢ)
  where
  y = ⁅ a , b ⁆
  x⊆ˢ : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩
  x⊆ˢ z z∈ = ∈∈ₛ {a = z} {b = y} .snd
    (x⊆ z (∈∈ₛ {a = z} {b = x} .fst z∈))
  go : (x ≡ ∅) ⊎ ((x ≡ ⁅ a ⁆s) ⊎ ((x ≡ ⁅ b ⁆s) ⊎ (x ≡ y)))
     → ⟨ x ∈ˢ 𝒟ₒ y ⟩
  go (inl e) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (empty∈dee y)
  go (inr (inl e)) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (eq∈dee y a pair∈l)
  go (inr (inr (inl e))) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (eq∈dee y b pair∈r)
  go (inr (inr (inr e))) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (A∈𝒟ₒ y)

-- Dee⊆stage at a pair, from a stage that already holds the four.
pair-dee⊆ : (σ a b : S)
          → ⟨ ∅ ∈ˢ Lset σ ⟩
          → ⟨ ⁅ a ⁆s ∈ˢ Lset σ ⟩
          → ⟨ ⁅ b ⁆s ∈ˢ Lset σ ⟩
          → ⟨ ⁅ a , b ⁆ ∈ˢ Lset σ ⟩
          → Dee⊆stage σ (⁅ a , b ⁆)
pair-dee⊆ σ a b ∅∈ sgla∈ sglb∈ y∈ x x∈dee = go (classify a b x (𝒟ₒ∋⊆ y x x∈dee))
  where
  y = ⁅ a , b ⁆
  go : (x ≡ ∅) ⊎ ((x ≡ ⁅ a ⁆s) ⊎ ((x ≡ ⁅ b ⁆s) ⊎ (x ≡ y)))
     → ⟨ x ∈ˢ Lset σ ⟩
  go (inl e) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) ∅∈
  go (inr (inl e)) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) sgla∈
  go (inr (inr (inl e))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) sglb∈
  go (inr (inr (inr e))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) y∈

-- THE OBLIGATION.  The supplier beyond the singleton family, at
-- the shape [LJ-1.683] left.  The consumer is imported.
describes-supplier :
    (σ a b : S)
  → ⟨ ⁅ a , b ⁆ ∈ˢ Lset σ ⟩
  → ⟨ ∅ ∈ˢ Lset σ ⟩
  → ⟨ ⁅ a ⁆s ∈ˢ Lset σ ⟩
  → ⟨ ⁅ b ⁆s ∈ˢ Lset σ ⟩
  → Describes σ (⁅ a , b ⁆)
describes-supplier σ a b y∈ ∅∈ sgla∈ sglb∈ =
  from-hyps σ (⁅ a , b ⁆) y∈
    (pair-dee⊆ σ a b ∅∈ sgla∈ sglb∈ y∈)
    (pair-spd σ a b)
