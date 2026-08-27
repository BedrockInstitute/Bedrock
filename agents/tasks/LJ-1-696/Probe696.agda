{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.696] PROBE.  Describes at the three-element ordinal the
-- finite iterate from ∅ actually reaches.  It runs in
-- agents/tasks/LJ-1-696/ and lands nothing in src/.
--
-- THE OBLIGATION the brief names is describes-at-n3: Describes at
-- n3 = sucV³ ∅.  The consumer is [LJ-1.683]'s from-hyps, imported,
-- not rewritten (W2).  The four paid families are not re-inhabited.
--
-- WHAT IS SETTLED.
--   1. Describes, Dee⊆stage, StagePowDef, from-hyps: imported from
--      agents/tasks/LJ-1-683/Probe683.agda.
--   2. empty∈dee, A∈𝒟ₒ, eq∈dee: imported from
--      agents/tasks/LJ-1-687/Probe687.agda (W2).
--   3. pair∈dee (W2): the pair of two members is definable over the
--      carrier, by the disjunction of two equalities.
--   4. classify3 (W2): LEM splits a subset of a three-element set
--      into the eight subsets.
--   5. describes-at-n3: from-hyps at n3, closed at σ = sucV n3.
--
-- WHAT IS NOT SETTLED.
--   Describes at a member of size four or more.  A generic y still
--   owes StagePowDef and Dee⊆stage.  A Formula Code 1 for 𝒟ₒ stays
--   a second debt.  PowIter as a closed term stays unpaid.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-696.Probe696 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _≐_; _∨̇_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV; ∈sucV-inl )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( Lset; 𝒟ₒ; 𝒟ₒ-intro; 𝒟ₒ∋⊆; IsOrd; Lset-mono )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import L.Axioms.Basic {ℓ} using ( pair∈Lset-suc; sgl∈Lset-suc )
open import LJ-1-683.Probe683 {ℓ}
  using ( Describes ; Dee⊆stage ; StagePowDef ; from-hyps )
open import LJ-1-687.Probe687 {ℓ} lem
  using ( empty∈dee ; A∈𝒟ₒ ; eq∈dee )

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
        ; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- D-10.  THE THREE-ELEMENT FAMILY.
--
-- [LJ-1.683] paid from-hyps.  [LJ-1.687] paid the pair family.
-- A three-element y has eight subsets under LEM.  Each is definable
-- over y.  from-hyps then carves them from a stage that already
-- holds all eight.
-- =====================================================================

∈sgl : {a z : S} → ⟨ z ∈ˢ ⁅ a ⁆s ⟩ → z ≡ a
∈sgl {a} {z} h =
  SetPackage.classification (SingletonPackage a) z .fst
    (∈∈ₛ {a = z} {b = ⁅ a ⁆s} .fst h)

-- W2: the pair of two members is definable over the carrier, by the
-- disjunction of two equalities.  The proof is the generic form of
-- pair∈𝒟ₒ (src/L/Axioms/Basic.lagda.md:547-585).
pair∈dee : (A c d : S) → ⟨ c ∈ˢ A ⟩ → ⟨ d ∈ˢ A ⟩ → ⟨ ⁅ c , d ⁆ ∈ˢ 𝒟ₒ A ⟩
pair∈dee A c d c∈ d∈ = 𝒟ₒ-intro A (⁅ c , d ⁆) ∣ φ , defSet≡ ∣₁
  where
  module DefC = DefOf A
  mᶜ = ∈-asFiber {a = c} {b = A} c∈ .fst
  qᶜ : ⟪ A ⟫↪ mᶜ ≡ c
  qᶜ = ∈-asFiber {a = c} {b = A} c∈ .snd
  mᵈ = ∈-asFiber {a = d} {b = A} d∈ .fst
  qᵈ : ⟪ A ⟫↪ mᵈ ≡ d
  qᵈ = ∈-asFiber {a = d} {b = A} d∈ .snd
  φ : Formula ⟪ A ⟫ 1
  φ = (var zero ≐ con mᶜ) ∨̇ (var zero ≐ con mᵈ)

  defSet≡ : DefC.defSet φ ≡ ⁅ c , d ⁆
  defSet≡ =
      extensionality (DefC.defSet φ) ⁅ ⟪ A ⟫↪ mᶜ , ⟪ A ⟫↪ mᵈ ⁆
        (sub₁ , sub₂)
    ∙ cong₂ ⁅_,_⁆ qᶜ qᵈ
    where
    sub₁ : ⟨ DefC.defSet φ ⊆ ⁅ ⟪ A ⟫↪ mᶜ , ⟪ A ⟫↪ mᵈ ⁆ ⟩
    sub₁ w w∈ₛ = PT.rec (snd (w ∈ₛ ⁅ ⟪ A ⟫↪ mᶜ , ⟪ A ⟫↪ mᵈ ⁆))
      (λ { ((m , h) , q) →
        subst (λ v → ⟨ v ∈ₛ ⁅ ⟪ A ⟫↪ mᶜ , ⟪ A ⟫↪ mᵈ ⁆ ⟩) q
          (pairing-ax (⟪ A ⟫↪ mᶜ) (⟪ A ⟫↪ mᵈ) (⟪ A ⟫↪ m) .snd
            (subst ⟨_⟩ (DefC.defSet-mem φ m) ∣ (m , h) , refl ∣₁)) })
      (∈∈ₛ {a = w} {b = DefC.defSet φ} .snd w∈ₛ)
    sub₂ : ⟨ ⁅ ⟪ A ⟫↪ mᶜ , ⟪ A ⟫↪ mᵈ ⁆ ⊆ DefC.defSet φ ⟩
    sub₂ w w∈ₛ = PT.rec (snd (w ∈ₛ DefC.defSet φ))
      (λ { (inl p) → memOf mᶜ ∣ inl refl ∣₁ p
         ; (inr p) → memOf mᵈ ∣ inr refl ∣₁ p })
      (pairing-ax (⟪ A ⟫↪ mᶜ) (⟪ A ⟫↪ mᵈ) w .fst w∈ₛ)
      where
      memOf : (mᵢ : ⟪ A ⟫) → ⟨ (DefC.ι mᵢ ∷ []) DefC.⊨ᵐ φ ⟩
            → w ≡ ⟪ A ⟫↪ mᵢ → ⟨ w ∈ₛ DefC.defSet φ ⟩
      memOf mᵢ sat p = subst (λ v → ⟨ v ∈ₛ DefC.defSet φ ⟩) (sym p)
        (∈∈ₛ {a = ⟪ A ⟫↪ mᵢ} {b = DefC.defSet φ} .fst
          (subst ⟨_⟩ (sym (DefC.defSet-mem φ mᵢ)) sat))

-- Three-way membership, as a type, so the eight-way split and the
-- remaps share one carrier.
Mem3 : (a b c x : S) → Type (ℓ-suc ℓ)
Mem3 a b c x =
  (z : S) → ⟨ z ∈ˢ x ⟩ → ∥ (z ≡ a) ⊎ ((z ≡ b) ⊎ (z ≡ c)) ∥₁

mem-bac : (a b c x : S) → Mem3 a b c x → Mem3 b a c x
mem-bac a b c x m z z∈ = PT.map go (m z z∈)
  where
  go : (z ≡ a) ⊎ ((z ≡ b) ⊎ (z ≡ c)) → (z ≡ b) ⊎ ((z ≡ a) ⊎ (z ≡ c))
  go (inl e) = inr (inl e)
  go (inr (inl e)) = inl e
  go (inr (inr e)) = inr (inr e)

mem-cab : (a b c x : S) → Mem3 a b c x → Mem3 c a b x
mem-cab a b c x m z z∈ = PT.map go (m z z∈)
  where
  go : (z ≡ a) ⊎ ((z ≡ b) ⊎ (z ≡ c)) → (z ≡ c) ⊎ ((z ≡ a) ⊎ (z ≡ b))
  go (inl e) = inr (inl e)
  go (inr (inl e)) = inr (inr e)
  go (inr (inr e)) = inl e

mem-acb : (a b c x : S) → Mem3 a b c x → Mem3 a c b x
mem-acb a b c x m z z∈ = PT.map go (m z z∈)
  where
  go : (z ≡ a) ⊎ ((z ≡ b) ⊎ (z ≡ c)) → (z ≡ a) ⊎ ((z ≡ c) ⊎ (z ≡ b))
  go (inl e) = inl e
  go (inr (inl e)) = inr (inr e)
  go (inr (inr e)) = inr (inl e)

mem-bca : (a b c x : S) → Mem3 a b c x → Mem3 b c a x
mem-bca a b c x m z z∈ = PT.map go (m z z∈)
  where
  go : (z ≡ a) ⊎ ((z ≡ b) ⊎ (z ≡ c)) → (z ≡ b) ⊎ ((z ≡ c) ⊎ (z ≡ a))
  go (inl e) = inr (inr e)
  go (inr (inl e)) = inl e
  go (inr (inr e)) = inr (inl e)

only-empty :
    (a b c x : S)
  → (⟨ a ∈ˢ x ⟩ → Empty.⊥) → (⟨ b ∈ˢ x ⟩ → Empty.⊥) → (⟨ c ∈ˢ x ⟩ → Empty.⊥)
  → Mem3 a b c x
  → x ≡ ∅
only-empty a b c x a∉ b∉ c∉ mem =
  extensionality x ∅ (xe₁ , xe₂)
  where
  xe₁ : ⟨ x ⊆ ∅ ⟩
  xe₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ∅))
    (λ { (inl e) → Empty.rec (a∉ (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x))
       ; (inr (inl e)) → Empty.rec (b∉ (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x))
       ; (inr (inr e)) → Empty.rec (c∉ (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x)) })
    (mem z z∈x)
    where
    z∈x : ⟨ z ∈ˢ x ⟩
    z∈x = ∈∈ₛ {a = z} {b = x} .snd z∈ₛ
  xe₂ : ⟨ ∅ ⊆ x ⟩
  xe₂ z z∈ₛ = Empty.rec (∅-empty z z∈ₛ)

only-sgl :
    (a b c x : S)
  → ⟨ a ∈ˢ x ⟩ → (⟨ b ∈ˢ x ⟩ → Empty.⊥) → (⟨ c ∈ˢ x ⟩ → Empty.⊥)
  → Mem3 a b c x
  → x ≡ ⁅ a ⁆s
only-sgl a b c x a∈ b∉ c∉ mem =
  extensionality x (⁅ a ⁆s) (xs₁ , xs₂)
  where
  xs₁ : ⟨ x ⊆ ⁅ a ⁆s ⟩
  xs₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ⁅ a ⁆s))
    (λ { (inl e) → SetPackage.classification (SingletonPackage a) z .snd e
       ; (inr (inl e)) → Empty.rec (b∉ (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x))
       ; (inr (inr e)) → Empty.rec (c∉ (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x)) })
    (mem z z∈x)
    where
    z∈x : ⟨ z ∈ˢ x ⟩
    z∈x = ∈∈ₛ {a = z} {b = x} .snd z∈ₛ
  xs₂ : ⟨ ⁅ a ⁆s ⊆ x ⟩
  xs₂ z z∈ₛ = subst (λ w → ⟨ w ∈ₛ x ⟩)
    (sym (∈sgl (∈∈ₛ {a = z} {b = ⁅ a ⁆s} .snd z∈ₛ)))
    (∈∈ₛ {a = a} {b = x} .fst a∈)

only-pair :
    (a b c x : S)
  → ⟨ a ∈ˢ x ⟩ → ⟨ b ∈ˢ x ⟩ → (⟨ c ∈ˢ x ⟩ → Empty.⊥)
  → Mem3 a b c x
  → x ≡ ⁅ a , b ⁆
only-pair a b c x a∈ b∈ c∉ mem =
  extensionality x ⁅ a , b ⁆ (xs₁ , xs₂)
  where
  xs₁ : ⟨ x ⊆ ⁅ a , b ⁆ ⟩
  xs₁ z z∈ₛ = PT.rec (snd (z ∈ₛ ⁅ a , b ⁆))
    (λ { (inl e) → pairing-ax a b z .snd ∣ inl e ∣₁
       ; (inr (inl e)) → pairing-ax a b z .snd ∣ inr e ∣₁
       ; (inr (inr e)) → Empty.rec (c∉ (subst (λ w → ⟨ w ∈ˢ x ⟩) e z∈x)) })
    (mem z z∈x)
    where
    z∈x : ⟨ z ∈ˢ x ⟩
    z∈x = ∈∈ₛ {a = z} {b = x} .snd z∈ₛ
  xs₂ : ⟨ ⁅ a , b ⁆ ⊆ x ⟩
  xs₂ z z∈ₛ = PT.rec (snd (z ∈ₛ x))
    (λ { (inl e) → subst (λ w → ⟨ w ∈ₛ x ⟩) (sym e)
                     (∈∈ₛ {a = a} {b = x} .fst a∈)
       ; (inr e) → subst (λ w → ⟨ w ∈ₛ x ⟩) (sym e)
                     (∈∈ₛ {a = b} {b = x} .fst b∈) })
    (pairing-ax a b z .fst z∈ₛ)

only-triple :
    (y a b c x : S)
  → ⟨ a ∈ˢ x ⟩ → ⟨ b ∈ˢ x ⟩ → ⟨ c ∈ˢ x ⟩
  → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
  → Mem3 a b c y
  → x ≡ y
only-triple y a b c x a∈ b∈ c∈ x⊆y memy =
  extensionality x y (xs₁ , xs₂)
  where
  xs₁ : ⟨ x ⊆ y ⟩
  xs₁ z z∈ₛ = ∈∈ₛ {a = z} {b = y} .fst
    (x⊆y z (∈∈ₛ {a = z} {b = x} .snd z∈ₛ))
  xs₂ : ⟨ y ⊆ x ⟩
  xs₂ z z∈ₛ = PT.rec (snd (z ∈ₛ x))
    (λ { (inl e) → subst (λ w → ⟨ w ∈ₛ x ⟩) (sym e)
                     (∈∈ₛ {a = a} {b = x} .fst a∈)
       ; (inr (inl e)) → subst (λ w → ⟨ w ∈ₛ x ⟩) (sym e)
                         (∈∈ₛ {a = b} {b = x} .fst b∈)
       ; (inr (inr e)) → subst (λ w → ⟨ w ∈ₛ x ⟩) (sym e)
                         (∈∈ₛ {a = c} {b = x} .fst c∈) })
    (memy z (∈∈ₛ {a = z} {b = y} .snd z∈ₛ))

-- W2: LEM classifies a subset of a three-element set as one of the
-- eight subsets.
classify3 :
    (y a b c x : S)
  → ⟨ a ∈ˢ y ⟩ → ⟨ b ∈ˢ y ⟩ → ⟨ c ∈ˢ y ⟩
  → Mem3 a b c y
  → ((z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩)
  → (x ≡ ∅)
    ⊎ ((x ≡ ⁅ a ⁆s)
    ⊎ ((x ≡ ⁅ b ⁆s)
    ⊎ ((x ≡ ⁅ c ⁆s)
    ⊎ ((x ≡ ⁅ a , b ⁆)
    ⊎ ((x ≡ ⁅ a , c ⁆)
    ⊎ ((x ≡ ⁅ b , c ⁆)
    ⊎ (x ≡ y)))))))
classify3 y a b c x a∈y b∈y c∈y memy x⊆y =
  from (lem (a ∈ˢ x)) (lem (b ∈ˢ x)) (lem (c ∈ˢ x))
  where
  memx : Mem3 a b c x
  memx z z∈ = memy z (x⊆y z z∈)
  from : ⟨ a ∈ˢ x ⟩ ⊎ (⟨ a ∈ˢ x ⟩ → Empty.⊥)
       → ⟨ b ∈ˢ x ⟩ ⊎ (⟨ b ∈ˢ x ⟩ → Empty.⊥)
       → ⟨ c ∈ˢ x ⟩ ⊎ (⟨ c ∈ˢ x ⟩ → Empty.⊥)
       → (x ≡ ∅)
         ⊎ ((x ≡ ⁅ a ⁆s)
         ⊎ ((x ≡ ⁅ b ⁆s)
         ⊎ ((x ≡ ⁅ c ⁆s)
         ⊎ ((x ≡ ⁅ a , b ⁆)
         ⊎ ((x ≡ ⁅ a , c ⁆)
         ⊎ ((x ≡ ⁅ b , c ⁆)
         ⊎ (x ≡ y)))))))
  from (inl a∈) (inl b∈) (inl c∈) =
    inr (inr (inr (inr (inr (inr (inr
      (only-triple y a b c x a∈ b∈ c∈ x⊆y memy)))))))
  from (inl a∈) (inl b∈) (inr c∉) =
    inr (inr (inr (inr (inl (only-pair a b c x a∈ b∈ c∉ memx)))))
  from (inl a∈) (inr b∉) (inl c∈) =
    inr (inr (inr (inr (inr (inl
      (only-pair a c b x a∈ c∈ b∉ (mem-acb a b c x memx)))))))
  from (inl a∈) (inr b∉) (inr c∉) =
    inr (inl (only-sgl a b c x a∈ b∉ c∉ memx))
  from (inr a∉) (inl b∈) (inl c∈) =
    inr (inr (inr (inr (inr (inr (inl
      (only-pair b c a x b∈ c∈ a∉ (mem-bca a b c x memx))))))))
  from (inr a∉) (inl b∈) (inr c∉) =
    inr (inr (inl (only-sgl b a c x b∈ a∉ c∉ (mem-bac a b c x memx))))
  from (inr a∉) (inr b∉) (inl c∈) =
    inr (inr (inr (inl (only-sgl c a b x c∈ a∉ b∉ (mem-cab a b c x memx)))))
  from (inr a∉) (inr b∉) (inr c∉) =
    inl (only-empty a b c x a∉ b∉ c∉ memx)

-- StagePowDef at a three-element set.  The stage membership of x is
-- unused: every subset of a three-element set is definable over it,
-- under LEM.
triple-spd :
    (σ y a b c : S)
  → ⟨ a ∈ˢ y ⟩ → ⟨ b ∈ˢ y ⟩ → ⟨ c ∈ˢ y ⟩
  → Mem3 a b c y
  → StagePowDef σ y
triple-spd σ y a b c a∈ b∈ c∈ memy x _ x⊆ = go (classify3 y a b c x a∈ b∈ c∈ memy x⊆ˢ)
  where
  x⊆ˢ : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ y ⟩
  x⊆ˢ z z∈ = ∈∈ₛ {a = z} {b = y} .snd
    (x⊆ z (∈∈ₛ {a = z} {b = x} .fst z∈))
  go : (x ≡ ∅)
     ⊎ ((x ≡ ⁅ a ⁆s)
     ⊎ ((x ≡ ⁅ b ⁆s)
     ⊎ ((x ≡ ⁅ c ⁆s)
     ⊎ ((x ≡ ⁅ a , b ⁆)
     ⊎ ((x ≡ ⁅ a , c ⁆)
     ⊎ ((x ≡ ⁅ b , c ⁆)
     ⊎ (x ≡ y)))))))
     → ⟨ x ∈ˢ 𝒟ₒ y ⟩
  go (inl e) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (empty∈dee y)
  go (inr (inl e)) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (eq∈dee y a a∈)
  go (inr (inr (inl e))) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (eq∈dee y b b∈)
  go (inr (inr (inr (inl e)))) = subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (eq∈dee y c c∈)
  go (inr (inr (inr (inr (inl e))))) =
    subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (pair∈dee y a b a∈ b∈)
  go (inr (inr (inr (inr (inr (inl e)))))) =
    subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (pair∈dee y a c a∈ c∈)
  go (inr (inr (inr (inr (inr (inr (inl e))))))) =
    subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (pair∈dee y b c b∈ c∈)
  go (inr (inr (inr (inr (inr (inr (inr e))))))) =
    subst (λ w → ⟨ w ∈ˢ 𝒟ₒ y ⟩) (sym e) (A∈𝒟ₒ y)

-- Dee⊆stage at a three-element set, from a stage that already holds
-- the eight.
triple-dee⊆ :
    (σ y a b c : S)
  → ⟨ a ∈ˢ y ⟩ → ⟨ b ∈ˢ y ⟩ → ⟨ c ∈ˢ y ⟩
  → Mem3 a b c y
  → ⟨ ∅ ∈ˢ Lset σ ⟩
  → ⟨ ⁅ a ⁆s ∈ˢ Lset σ ⟩
  → ⟨ ⁅ b ⁆s ∈ˢ Lset σ ⟩
  → ⟨ ⁅ c ⁆s ∈ˢ Lset σ ⟩
  → ⟨ ⁅ a , b ⁆ ∈ˢ Lset σ ⟩
  → ⟨ ⁅ a , c ⁆ ∈ˢ Lset σ ⟩
  → ⟨ ⁅ b , c ⁆ ∈ˢ Lset σ ⟩
  → ⟨ y ∈ˢ Lset σ ⟩
  → Dee⊆stage σ y
triple-dee⊆ σ y a b c a∈ b∈ c∈ memy ∅∈ sgla∈ sglb∈ sglc∈ pab∈ pac∈ pbc∈ y∈
  x x∈dee = go (classify3 y a b c x a∈ b∈ c∈ memy (𝒟ₒ∋⊆ y x x∈dee))
  where
  go : (x ≡ ∅)
     ⊎ ((x ≡ ⁅ a ⁆s)
     ⊎ ((x ≡ ⁅ b ⁆s)
     ⊎ ((x ≡ ⁅ c ⁆s)
     ⊎ ((x ≡ ⁅ a , b ⁆)
     ⊎ ((x ≡ ⁅ a , c ⁆)
     ⊎ ((x ≡ ⁅ b , c ⁆)
     ⊎ (x ≡ y)))))))
     → ⟨ x ∈ˢ Lset σ ⟩
  go (inl e) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) ∅∈
  go (inr (inl e)) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) sgla∈
  go (inr (inr (inl e))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) sglb∈
  go (inr (inr (inr (inl e)))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) sglc∈
  go (inr (inr (inr (inr (inl e))))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) pab∈
  go (inr (inr (inr (inr (inr (inl e)))))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) pac∈
  go (inr (inr (inr (inr (inr (inr (inl e))))))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) pbc∈
  go (inr (inr (inr (inr (inr (inr (inr e))))))) = subst (λ w → ⟨ w ∈ˢ Lset σ ⟩) (sym e) y∈

-- W2: Describes at a three-element member, from a stage that already
-- holds the eight subsets.  Instantiated at n3 below.
describes-triple :
    (σ y a b c : S)
  → ⟨ a ∈ˢ y ⟩ → ⟨ b ∈ˢ y ⟩ → ⟨ c ∈ˢ y ⟩
  → Mem3 a b c y
  → ⟨ y ∈ˢ Lset σ ⟩
  → ⟨ ∅ ∈ˢ Lset σ ⟩
  → ⟨ ⁅ a ⁆s ∈ˢ Lset σ ⟩
  → ⟨ ⁅ b ⁆s ∈ˢ Lset σ ⟩
  → ⟨ ⁅ c ⁆s ∈ˢ Lset σ ⟩
  → ⟨ ⁅ a , b ⁆ ∈ˢ Lset σ ⟩
  → ⟨ ⁅ a , c ⁆ ∈ˢ Lset σ ⟩
  → ⟨ ⁅ b , c ⁆ ∈ˢ Lset σ ⟩
  → Describes σ y
describes-triple σ y a b c a∈ b∈ c∈ memy y∈ ∅∈ sgla∈ sglb∈ sglc∈ pab∈ pac∈ pbc∈ =
  from-hyps σ y y∈
    (triple-dee⊆ σ y a b c a∈ b∈ c∈ memy ∅∈ sgla∈ sglb∈ sglc∈ pab∈ pac∈ pbc∈ y∈)
    (triple-spd σ y a b c a∈ b∈ c∈ memy)

-- The witness.  Named first so the obligation type does not mention
-- a nested sucV chain (P-l).
n0 n1 n2 n3 σ₄ : S
n0 = ∅
n1 = sucV n0
n2 = sucV n1
n3 = sucV n2
σ₄ = sucV n3

n0-ord : IsOrd n0
n0-ord = ∅-ord
n1-ord : IsOrd n1
n1-ord = suc-ord n0-ord
n2-ord : IsOrd n2
n2-ord = suc-ord n1-ord
n3-ord : IsOrd n3
n3-ord = suc-ord n2-ord

n0∈n1 : ⟨ n0 ∈ˢ n1 ⟩
n0∈n1 = self∈sucV n0
n0∈n2 : ⟨ n0 ∈ˢ n2 ⟩
n0∈n2 = ∈sucV-inl n0∈n1
n0∈n3 : ⟨ n0 ∈ˢ n3 ⟩
n0∈n3 = ∈sucV-inl n0∈n2
n1∈n2 : ⟨ n1 ∈ˢ n2 ⟩
n1∈n2 = self∈sucV n1
n1∈n3 : ⟨ n1 ∈ˢ n3 ⟩
n1∈n3 = ∈sucV-inl n1∈n2
n2∈n3 : ⟨ n2 ∈ˢ n3 ⟩
n2∈n3 = self∈sucV n2

∈n3 : Mem3 n0 n1 n2 n3
∈n3 z z∈ = ∈sucV-elim {A = n2} {x = z} PT.squash₁ z∈
  (λ z∈n2 → ∈sucV-elim {A = n1} {x = z} PT.squash₁ z∈n2
    (λ z∈n1 → ∈sucV-elim {A = n0} {x = z} PT.squash₁ z∈n1
      (λ z∈∅ → Empty.rec (∅-empty z (∈∈ₛ {a = z} {b = n0} .fst z∈∅)))
      (λ e → ∣ inl e ∣₁))
    (λ e → ∣ inr (inl e) ∣₁))
  (λ e → ∣ inr (inr e) ∣₁)

n0∈Lset-n3 : ⟨ n0 ∈ˢ Lset n3 ⟩
n0∈Lset-n3 = Lset-mono {α = n3} {β = n1} n1∈n3 (ord∈Lset-suc n0 n0-ord)
n1∈Lset-n3 : ⟨ n1 ∈ˢ Lset n3 ⟩
n1∈Lset-n3 = Lset-mono {α = n3} {β = n2} n2∈n3 (ord∈Lset-suc n1 n1-ord)
n2∈Lset-n3 : ⟨ n2 ∈ˢ Lset n3 ⟩
n2∈Lset-n3 = ord∈Lset-suc n2 n2-ord

n3∈σ₄ : ⟨ n3 ∈ˢ Lset σ₄ ⟩
n3∈σ₄ = ord∈Lset-suc n3 n3-ord
∅∈σ₄ : ⟨ ∅ ∈ˢ Lset σ₄ ⟩
∅∈σ₄ = Lset-mono {α = σ₄} {β = n3} (self∈sucV n3) n0∈Lset-n3
sgl0∈σ₄ : ⟨ ⁅ n0 ⁆s ∈ˢ Lset σ₄ ⟩
sgl0∈σ₄ = sgl∈Lset-suc n3 n0 n0∈Lset-n3
sgl1∈σ₄ : ⟨ ⁅ n1 ⁆s ∈ˢ Lset σ₄ ⟩
sgl1∈σ₄ = sgl∈Lset-suc n3 n1 n1∈Lset-n3
sgl2∈σ₄ : ⟨ ⁅ n2 ⁆s ∈ˢ Lset σ₄ ⟩
sgl2∈σ₄ = sgl∈Lset-suc n3 n2 n2∈Lset-n3
pair01∈σ₄ : ⟨ ⁅ n0 , n1 ⁆ ∈ˢ Lset σ₄ ⟩
pair01∈σ₄ = pair∈Lset-suc n3 n0 n1 n0∈Lset-n3 n1∈Lset-n3
pair02∈σ₄ : ⟨ ⁅ n0 , n2 ⁆ ∈ˢ Lset σ₄ ⟩
pair02∈σ₄ = pair∈Lset-suc n3 n0 n2 n0∈Lset-n3 n2∈Lset-n3
pair12∈σ₄ : ⟨ ⁅ n1 , n2 ⁆ ∈ˢ Lset σ₄ ⟩
pair12∈σ₄ = pair∈Lset-suc n3 n1 n2 n1∈Lset-n3 n2∈Lset-n3

-- THE OBLIGATION.  Describes at the three-element ordinal, closed at
-- the stage the iterate reaches it.
describes-at-n3 : Describes σ₄ n3
describes-at-n3 =
  describes-triple σ₄ n3 n0 n1 n2 n0∈n3 n1∈n3 n2∈n3 ∈n3
    n3∈σ₄ ∅∈σ₄ sgl0∈σ₄ sgl1∈σ₄ sgl2∈σ₄ pair01∈σ₄ pair02∈σ₄ pair12∈σ₄
