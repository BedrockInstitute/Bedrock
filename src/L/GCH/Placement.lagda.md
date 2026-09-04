# Placement inside a closed stage

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Placement {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( Transitive; module hPropStructure )
open import FOL.Syntax
  using ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∃∈; δ-∀∈ )
open import FOL.Manipulation.Relabelling using ( mapTm; mapFo )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Coding {ℓ} using ( pr; module VCode )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-layer; layer-trans
        ; Lset-mono; Lset-out; Lset→isL; 𝒟ₒ; 𝒟ₒ∋⊆; 𝒟ₒ-intro )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord; ω-ord; #∈ω )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Ordinal.StageArith {ℓ} lem
  using ( sucIter; +ω; +ω-mem; +ω-iter; +ω-sup; +ω-ord; closedω )
open import L.Choice.Name {ℓ} lem using ( numeral∈limit )
open import L.Axioms.Basic {ℓ} using ( LsetS; Lset-suc; pr∈Lset-suc )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.CodeSet {ℓ} lem using ( keyS )
open import L.Coding.EnvSet {ℓ} lem using ( envSet )
open import L.Coding.Key {ℓ} lem using ( envSetNumeral∈ )
open import L.Coding.Bridge {ℓ} lem using ( asConst )
open import L.Coding.Bound {ℓ} lem using ( module Bound; Lset-out′ )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst; tagAtL; prAtL )

open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Nat.Properties using ( +-comm )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum as Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt; tt* )
import Cubical.Data.Empty as Empty
open import Cubical.Foundations.Equiv using ( invEq )
open import Cubical.Foundations.Function using ( _∘_ )
open import Cubical.Foundations.HLevels using ( isOfHLevelLift )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; _⊆_; extensionality )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( #_; ω; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
-- Membership `_∈ˢ_` below is the V structure's (definitionally `_∈_`);
-- `S` is the L carrier, and the L structure's membership is `_∈ˢʟ_`.
open hPropStructure 𝒮ᵥ hiding ( S )
open hPropStructure 𝒮ʟ using ( S ) renaming ( _∈ˢ_ to _∈ˢʟ_ )

-- =====================================================================
-- SECTION 0.  Transitivity of a stage, and the successor closer.
-- =====================================================================

-- Members of members of Lset γ lie in Lset γ (LJ-1.739/743).
private
  Lset-trans-set′ : (γ a x : V ℓ)
                  → ⟨ a ∈ x ⟩ → ⟨ x ∈ Lset γ ⟩ → ⟨ a ∈ Lset γ ⟩
  Lset-trans-set′ γ a x a∈ x∈ = PT.rec (snd (a ∈ Lset γ)) step (Lset-out γ x x∈)
    where
    step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ γ ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩)
         → ⟨ a ∈ Lset γ ⟩
    step (δ , (δ∈γ , x∈𝒟)) =
      Lset-mono {α = γ} {β = δ} δ∈γ {x = a}
        (𝒟ₒ∋⊆ (Lset δ) x x∈𝒟 a a∈)

-- The closer (LJ-1.737-SPLIT, trimmed at LJ-1.747).
module Closer (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ) where

  -- closedω forbids γ to be a successor:  γ = sucV x with x ∈ γ would
  -- put +ω x inside sucV x, and +ω x is neither below nor equal to x.
  no-succ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → sucV x ≡ γ → Empty.⊥
  no-succ x x∈ eq = lower
    (∈sucV-elim (isOfHLevelLift 1 Empty.isProp⊥) +ω∈sucx
      (λ h → lift (kA h)) (λ h → lift (k≡ h)))
    where
    ox : IsOrd x
    ox = mem-ord {A = γ} oγ x x∈
    +ω∈sucx : ⟨ +ω x ∈ˢ sucV x ⟩
    +ω∈sucx = subst (λ w → ⟨ +ω x ∈ˢ w ⟩) (sym eq) (clγ x x∈)
    kA : ⟨ +ω x ∈ˢ x ⟩ → Empty.⊥
    kA h = ∈-irrefl x (ox .fst (+ω-mem x) h)
    k≡ : +ω x ≡ x → Empty.⊥
    k≡ h≡ = ∈-irrefl x (subst (λ w → ⟨ x ∈ˢ w ⟩) h≡ (+ω-mem x))

  -- The strict successor step:  closedω makes every successor of a
  -- member a member.
  suc∈γ : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ → ⟨ sucV x ∈ˢ γ ⟩
  suc∈γ x x∈ = Sum.rec id (λ h → Empty.rec (no-succ x x∈ h))
    (suc∈or≡ x γ (mem-ord {A = γ} oγ x x∈) oγ x∈)

-- Finite successor iterates of a member stay inside γ (LJ-1.751/752).
sucIter-in-γ :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
    (n : ℕ) → ⟨ sucIter n x ∈ˢ γ ⟩
sucIter-in-γ γ oγ clγ x x∈ zero = x∈
sucIter-in-γ γ oγ clγ x x∈ (suc n) =
  suc∈γ (sucIter n x) (sucIter-in-γ γ oγ clγ x x∈ n)
  where
  open Closer γ oγ clγ

-- A member of a finite iterate's stage sits in Lset γ (LJ-1.752).
block∈Lγ :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (x : V ℓ) → ⟨ x ∈ˢ γ ⟩ →
    (n : ℕ) (b : V ℓ) →
    ⟨ b ∈ˢ Lset (sucIter n x) ⟩ → ⟨ b ∈ˢ Lset γ ⟩
block∈Lγ γ oγ clγ x x∈ n b b∈ =
  Lset-mono {α = γ} {β = sucIter n x} (sucIter-in-γ γ oγ clγ x x∈ n) b∈

-- =====================================================================
-- SECTION 1.  The finite-iterate shift and the Kuratowski step
-- (LJ-1.734).
-- =====================================================================

sucIter-sucV : (X : V ℓ) (b : ℕ) → sucV (sucIter b X) ≡ sucIter b (sucV X)
sucIter-sucV X zero    = refl
sucIter-sucV X (suc b) = cong sucV (sucIter-sucV X b)

sucIter-shift : (u : V ℓ) (a b : ℕ) → sucIter (a + b) u ≡ sucIter b (sucIter a u)
sucIter-shift u zero    b = refl
sucIter-shift u (suc a) b =
  cong sucV (sucIter-shift u a b) ∙ sucIter-sucV (sucIter a u) b

-- b iterates above any stage W.  The zero case is definitional.
iter-up : (W : V ℓ) (b : ℕ) (x : V ℓ)
        → ⟨ x ∈ˢ Lset W ⟩ → ⟨ x ∈ˢ Lset (sucIter b W) ⟩
iter-up W zero    x h = h
iter-up W (suc b) x h =
  Lset-mono {α = sucV (sucIter b W)} {β = sucIter b W}
    (self∈sucV (sucIter b W)) (iter-up W b x h)

pr∈iter : (σ : V ℓ) (ja jb : ℕ) (x y : V ℓ)
        → ⟨ x ∈ˢ Lset (sucIter ja σ) ⟩ → ⟨ y ∈ˢ Lset (sucIter jb σ) ⟩
        → ⟨ pr x y ∈ˢ Lset (sucIter (suc (suc (ja + jb))) σ) ⟩
pr∈iter σ ja jb x y hx hy =
  pr∈Lset-suc (sucIter (ja + jb) σ) x y
    (subst (λ W → ⟨ x ∈ˢ Lset W ⟩) (sym (sucIter-shift σ ja jb))
      (iter-up (sucIter ja σ) jb x hx))
    (subst (λ W → ⟨ y ∈ˢ Lset W ⟩) (cong (λ W → sucIter W σ) (+-comm jb ja))
      (subst (λ W → ⟨ y ∈ˢ Lset W ⟩) (sym (sucIter-shift σ jb ja))
        (iter-up (sucIter jb σ) ja y hy)))

-- The climb: the code of a formula's mapFo image sits at SOME finite
-- iterate of the stage holding the alphabet's values and the numerals.
module Climb (σ : V ℓ) {K : Type ℓ} (f : K → V ℓ)
             (hf : (k : K) → ⟨ f k ∈ˢ Lset σ ⟩)
             (hnum : (k : ℕ) → ⟨ (# k) ∈ˢ Lset σ ⟩) where

  pairStep : (k ja jb : ℕ) (x y : V ℓ)
           → ⟨ x ∈ˢ Lset (sucIter ja σ) ⟩ → ⟨ y ∈ˢ Lset (sucIter jb σ) ⟩
           → Σ[ j ∈ ℕ ] ⟨ pr (# k) (pr x y) ∈ˢ Lset (sucIter j σ) ⟩
  pairStep k ja jb x y hx hy =
    suc (suc (suc (suc (ja + jb))))
    , pr∈iter σ 0 (suc (suc (ja + jb))) (# k) (pr x y)
        (hnum k) (pr∈iter σ ja jb x y hx hy)

  tagStep : (k jb : ℕ) (y : V ℓ)
          → ⟨ y ∈ˢ Lset (sucIter jb σ) ⟩
          → Σ[ j ∈ ℕ ] ⟨ pr (# k) y ∈ˢ Lset (sucIter j σ) ⟩
  tagStep k jb y hy =
    suc (suc jb) , pr∈iter σ 0 jb (# k) y (hnum k) hy

  codeTm∈iter : ∀ {n} (t : Term K n)
              → Σ[ j ∈ ℕ ] ⟨ VCode.⌜ mapTm f t ⌝ᵗ ∈ˢ Lset (sucIter j σ) ⟩
  codeTm∈iter (con c) = tagStep 0 0 (f c) (hf c)
  codeTm∈iter (var i) = tagStep 1 0 (# (toℕ i)) (hnum (toℕ i))

  code∈iter : ∀ {n} (φ : Formula K n)
            → Σ[ j ∈ ℕ ] ⟨ VCode.⌜ mapFo f φ ⌝ ∈ˢ Lset (sucIter j σ) ⟩
  code∈iter (t ∈̇ u) =
    pairStep 0 (fst (codeTm∈iter t)) (fst (codeTm∈iter u))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapTm f u ⌝ᵗ
      (snd (codeTm∈iter t)) (snd (codeTm∈iter u))
  code∈iter (t ≐ u) =
    pairStep 1 (fst (codeTm∈iter t)) (fst (codeTm∈iter u))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapTm f u ⌝ᵗ
      (snd (codeTm∈iter t)) (snd (codeTm∈iter u))
  code∈iter (a ∧̇ b) =
    pairStep 2 (fst (code∈iter a)) (fst (code∈iter b))
      VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝
      (snd (code∈iter a)) (snd (code∈iter b))
  code∈iter (a ∨̇ b) =
    pairStep 3 (fst (code∈iter a)) (fst (code∈iter b))
      VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝
      (snd (code∈iter a)) (snd (code∈iter b))
  code∈iter (a ⇒̇ b) =
    pairStep 4 (fst (code∈iter a)) (fst (code∈iter b))
      VCode.⌜ mapFo f a ⌝ VCode.⌜ mapFo f b ⌝
      (snd (code∈iter a)) (snd (code∈iter b))
  code∈iter (¬̇ a) = tagStep 5 (fst (code∈iter a)) (VCode.⌜ mapFo f a ⌝) (snd (code∈iter a))
  code∈iter ⊤̇    = tagStep 6 0 (# 0) (hnum 0)
  code∈iter ⊥̇    = tagStep 7 0 (# 0) (hnum 0)
  code∈iter (∃̇ a) = tagStep 8 (fst (code∈iter a)) (VCode.⌜ mapFo f a ⌝) (snd (code∈iter a))
  code∈iter (∀̇ a) = tagStep 9 (fst (code∈iter a)) (VCode.⌜ mapFo f a ⌝) (snd (code∈iter a))
  code∈iter (∀̇∈ t a) =
    pairStep 10 (fst (codeTm∈iter t)) (fst (code∈iter a))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝
      (snd (codeTm∈iter t)) (snd (code∈iter a))
  code∈iter (∃̇∈ t a) =
    pairStep 11 (fst (codeTm∈iter t)) (fst (code∈iter a))
      VCode.⌜ mapTm f t ⌝ᵗ VCode.⌜ mapFo f a ⌝
      (snd (codeTm∈iter t)) (snd (code∈iter a))

-- The key set of a carrier formula sits in the carrier's stage (LJ-1.734).
keyS-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (ω∈γ : ⟨ ω ∈ˢ γ ⟩)
    (A : S) (hA : ⟨ fst A ∈ Lset γ ⟩)
    {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
  → ⟨ keyS A φ ∈ˢʟ LsetS γ oγ ⟩
keyS-in-carrier-lim γ oγ clγ ω∈γ A hA {n} φ =
  PT.rec (snd (keyS A φ ∈ˢʟ LsetS γ oγ)) step (Lset-out γ (fst A) hA)
  where
  ι : ⟪ fst A ⟫ → V ℓ
  ι = ⟪ fst A ⟫↪

  ι∈ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢ fst A ⟩
  ι∈ m = ∈∈ₛ {a = ι m} {b = fst A} .snd (∈ₛ⟪ fst A ⟫↪ m)

  hL : ⟨ isL (fst A) ⟩
  hL = Lset→isL γ oγ (fst A) hA

  ιL : (m : ⟪ fst A ⟫) → ⟨ isL (ι m) ⟩
  ιL m = isL-trans {x = fst A} {y = ι m} (ι∈ m) hL

  𝒟𝒟 : (δ : V ℓ) → ⟨ fst A ∈ˢ 𝒟ₒ (Lset δ) ⟩
     → (m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢ Lset δ ⟩
  𝒟𝒟 δ A∈𝒟 m = 𝒟ₒ∋⊆ (Lset δ) (fst A) A∈𝒟 (ι m) (ι∈ m)

  close : (σ : V ℓ) → ⟨ σ ∈ˢ γ ⟩
        → ((k : ℕ) → ⟨ (# k) ∈ˢ Lset σ ⟩)
        → ((m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢ Lset σ ⟩)
        → ⟨ keyS A φ ∈ˢʟ LsetS γ oγ ⟩
  close σ σ∈γ hnum' hfc =
    Lset-mono {α = γ} {β = +ω σ} (clγ σ σ∈γ)
      (Lset-mono {α = +ω σ} {β = sucIter (suc (suc (fst Cj))) σ}
        (+ω-iter (suc (suc (fst Cj))) σ)
        (pr∈iter σ 0 (fst Cj) (# n) (VCode.⌜ mapFo ι φ ⌝)
          (hnum' n) (snd Cj)))
    where
    module C = Climb σ ι hfc hnum'
    Cj = C.code∈iter φ

  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ γ ⟩ × ⟨ fst A ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ keyS A φ ∈ˢʟ LsetS γ oγ ⟩
  step (δ , δ∈γ , A∈𝒟) = helper (ord-tri ω ω-ord δ oδ)
    where
    oδ : IsOrd δ
    oδ = mem-ord {A = γ} oγ δ δ∈γ

    hfcδ : (m : ⟪ fst A ⟫) → ⟨ ι m ∈ˢ Lset δ ⟩
    hfcδ m = 𝒟𝒟 δ A∈𝒟 m

    helper : Tri ω δ → ⟨ keyS A φ ∈ˢʟ LsetS γ oγ ⟩
    helper (inl ω∈δ) =
      close δ δ∈γ (λ k → Lset-mono {α = δ} {β = ω} ω∈δ (numeral∈limit k)) hfcδ
    helper (inr (inl ω≡δ)) =
      close δ δ∈γ
        (λ k → subst (λ W → ⟨ (# k) ∈ˢ Lset W ⟩) ω≡δ (numeral∈limit k)) hfcδ
    helper (inr (inr δ∈ω)) =
      close ω ω∈γ numeral∈limit (λ m → Lset-mono {α = ω} {β = δ} δ∈ω (hfcδ m))

-- =====================================================================
-- SECTION 2.  The environment set (LJ-1.735).
-- =====================================================================

envSet-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢ γ ⟩
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → (n : ℕ)
    → ⟨ envSet A n ∈ˢʟ LsetS γ oγ ⟩
envSet-in-carrier-lim γ oγ clγ ω∈γ A hA n =
  PT.rec (snd (envSet A n ∈ˢʟ LsetS γ oγ)) step (Lset-out γ (fst A) hA)
  where
  step : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ γ ⟩ × ⟨ fst A ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → ⟨ envSet A n ∈ˢʟ LsetS γ oγ ⟩
  step (δ , δ∈γ , A∈𝒟) = resolve (ord-tri ω ω-ord δ oδ)
    where
    oδ : IsOrd δ
    oδ = mem-ord {A = γ} oγ δ δ∈γ

    -- The carrier, one successor above its own bounding stage.
    A∈sucδ : ⟨ fst A ∈ Lset (sucV δ) ⟩
    A∈sucδ = subst (λ w → ⟨ fst A ∈ w ⟩) (sym (Lset-suc δ)) A∈𝒟

    close : (m : V ℓ) (om : IsOrd m) → ⟨ m ∈ˢ γ ⟩
          → ⟨ ω ∈ˢ +ω m ⟩ → ⟨ sucV δ ∈ˢ +ω m ⟩
          → ⟨ envSet A n ∈ˢʟ LsetS γ oγ ⟩
    close m om m∈γ ω∈+ωm sucδ∈+ωm =
      Lset-mono {α = γ} {β = +ω (+ω m)} (clγ (+ω m) (clγ m m∈γ))
        (Lset-mono {α = +ω (+ω m)} {β = sucIter 4 (+ω m)}
          (+ω-iter 4 (+ω m))
          (envSetNumeral∈ (+ω m) (+ω-ord m om) ω∈+ωm A n
            (Lset-mono {α = +ω m} {β = sucV δ} sucδ∈+ωm A∈sucδ)))

    below : ⟨ ω ∈ˢ δ ⟩ → ⟨ envSet A n ∈ˢʟ LsetS γ oγ ⟩
    below ω∈δ = close δ oδ δ∈γ
      ((+ω-ord δ oδ) .fst ω∈δ (+ω-mem δ))
      (+ω-iter 1 δ)

    eq-case : ω ≡ δ → ⟨ sucV δ ∈ˢ +ω ω ⟩
    eq-case ω≡δ = subst (λ w → ⟨ sucV w ∈ˢ +ω ω ⟩) ω≡δ (+ω-iter 1 ω)

    gt-case : ⟨ δ ∈ˢ ω ⟩ → ⟨ sucV δ ∈ˢ +ω ω ⟩
    gt-case δ∈ω = Sum.rec
      (λ sucδ∈ω → +ω-sup ω (sucV δ) sucδ∈ω)
      (λ sucδ≡ω → subst (λ w → ⟨ w ∈ˢ +ω ω ⟩) (sym sucδ≡ω) (+ω-mem ω))
      (suc∈or≡ δ ω oδ ω-ord δ∈ω)

    atω : (ω ≡ δ) ⊎ ⟨ δ ∈ˢ ω ⟩ → ⟨ envSet A n ∈ˢʟ LsetS γ oγ ⟩
    atω (inl ω≡δ) = close ω ω-ord ω∈γ (+ω-mem ω) (eq-case ω≡δ)
    atω (inr δ∈ω) = close ω ω-ord ω∈γ (+ω-mem ω) (gt-case δ∈ω)

    resolve : Tri ω δ → ⟨ envSet A n ∈ˢʟ LsetS γ oγ ⟩
    resolve (inl ω∈δ)  = below ω∈δ
    resolve (inr triω) = atω triω

-- =====================================================================
-- SECTION 3.  A carrier member as a constant (LJ-1.739).
-- =====================================================================

asConst-in-carrier :
    (γ : V ℓ) (oγ : IsOrd γ)
    (A : S) → ⟨ fst A ∈ Lset γ ⟩
  → (m : ⟪ fst A ⟫)
  → ⟨ fst (asConst A m) ∈ Lset γ ⟩
asConst-in-carrier γ oγ A hA m =
  Lset-trans-set′ γ (fst (asConst A m)) (fst A)
    (DefOf.ι (fst A) m .snd) hA

-- =====================================================================
-- SECTION 4.  The definable subset of a carrier formula (LJ-1.741).
-- =====================================================================

infixl 30 _^_
_^_ : ∀ {ℓ''} → Type ℓ'' → ℕ → Type ℓ''
A ^ n = Vec A n

-- The transfer, at one carrier and one transitive stage holding it.
module Carrier (a : V ℓ) (σ : V ℓ) (oσ : IsOrd σ) (a∈σ : ⟨ a ∈ Lset σ ⟩) where
  module DA = DefOf a
  module DS = DefOf (Lset σ)

  DA-in : (m : ⟪ a ⟫) → ⟨ ⟪ a ⟫↪ m ∈ a ⟩
  DA-in m = ∈∈ₛ {a = ⟪ a ⟫↪ m} {b = a} .snd (∈ₛ⟪ a ⟫↪ m)

  Atr : Transitive 𝒮ᵥ DS.M
  Atr = layer-trans (Lset-layer σ)

  -- The fiber of a carrier member in the stage.
  κ : ⟪ a ⟫ → ⟪ Lset σ ⟫
  κ m = ∈-asFiber {a = ⟪ a ⟫↪ m} {b = Lset σ} (Atr (DA-in m) a∈σ) .fst

  κEq : (m : ⟪ a ⟫) → ⟪ Lset σ ⟫↪ (κ m) ≡ ⟪ a ⟫↪ m
  κEq m = ∈-asFiber {a = ⟪ a ⟫↪ m} {b = Lset σ} (Atr (DA-in m) a∈σ) .snd

  -- The fiber of the carrier itself in the stage: the bound constant.
  mA : ⟪ Lset σ ⟫
  mA = ∈-asFiber {a = a} {b = Lset σ} a∈σ .fst

  mAEq : ⟪ Lset σ ⟫↪ mA ≡ a
  mAEq = ∈-asFiber {a = a} {b = Lset σ} a∈σ .snd

  -- Environment entries: a member of a sits in the transitive stage.
  repack : DA.SM → DS.SM
  repack p = fst p , Atr (snd p) a∈σ

  repV : ∀ {n} → DA.SM ^ n → DS.SM ^ n
  repV [] = []
  repV (x ∷ δ) = repack x ∷ repV δ

  rep-fst : ∀ {n} (i : Fin n) (δ : DA.SM ^ n)
          → fst (lookup i (repV δ)) ≡ fst (lookup i δ)
  rep-fst zero (x ∷ δ) = refl
  rep-fst (suc i) (x ∷ δ) = rep-fst i δ

  tm-fst : ∀ {n} (t : Term ⟪ a ⟫ n) (δ : DA.SM ^ n)
         → fst (DS.⟦ mapTm κ t ⟧ᵐ (repV δ)) ≡ fst (DA.⟦ t ⟧ᵐ δ)
  tm-fst (con m) δ = κEq m
  tm-fst (var i) δ = rep-fst i δ

  -- The bounded-quantifier guard reads its bound term one variable
  -- up (the new var 0 is the bound one), so the term shifts arity.
  tmSuc : ∀ {n} → Term ⟪ a ⟫ n → Term ⟪ Lset σ ⟫ (suc n)
  tmSuc (con m) = con (κ m)
  tmSuc (var i) = var (suc i)

  tm-fst1 : ∀ {n} (t : Term ⟪ a ⟫ n) (x : DS.SM) (δ : DA.SM ^ n)
          → fst (DS.⟦ tmSuc t ⟧ᵐ (x ∷ repV δ)) ≡ fst (DA.⟦ t ⟧ᵐ δ)
  tm-fst1 (con m) x δ = κEq m
  tm-fst1 (var i) x δ = rep-fst i δ

  -- The relativized image.  Atoms pass through mapFo κ; the unbounded
  -- quantifiers are bounded by the carrier's fiber; the bounded
  -- quantifiers keep their bound and gain the carrier guard.
  cnd : ∀ {n} → Formula ⟪ a ⟫ n → Formula ⟪ Lset σ ⟫ n
  cnd (t ∈̇ u)  = mapFo κ (t ∈̇ u)
  cnd (t ≐ u)  = mapFo κ (t ≐ u)
  cnd (φ ∧̇ χ)  = cnd φ ∧̇ cnd χ
  cnd (φ ∨̇ χ)  = cnd φ ∨̇ cnd χ
  cnd (φ ⇒̇ χ)  = cnd φ ⇒̇ cnd χ
  cnd (¬̇ φ)    = ¬̇ cnd φ
  cnd ⊤̇        = ⊤̇
  cnd ⊥̇        = ⊥̇
  cnd (∃̇ φ)    = ∃̇∈ (con mA) (cnd φ)
  cnd (∀̇ φ)    = ∀̇∈ (con mA) (cnd φ)
  cnd (∀̇∈ t φ) = ∀̇∈ (con mA) (var zero ∈̇ tmSuc t ⇒̇ cnd φ)
  cnd (∃̇∈ t φ) = ∃̇∈ (con mA) (var zero ∈̇ tmSuc t ∧̇ cnd φ)

  Δ₀-cnd : ∀ {n} (ψ : Formula ⟪ a ⟫ n) → Δ₀ (cnd ψ)
  Δ₀-cnd (t ∈̇ u)  = δ-∈
  Δ₀-cnd (t ≐ u)  = δ-≐
  Δ₀-cnd (φ ∧̇ χ)  = δ-∧ (Δ₀-cnd φ) (Δ₀-cnd χ)
  Δ₀-cnd (φ ∨̇ χ)  = δ-∨ (Δ₀-cnd φ) (Δ₀-cnd χ)
  Δ₀-cnd (φ ⇒̇ χ)  = δ-⇒ (Δ₀-cnd φ) (Δ₀-cnd χ)
  Δ₀-cnd (¬̇ φ)    = δ-¬ (Δ₀-cnd φ)
  Δ₀-cnd ⊤̇        = δ-⊤
  Δ₀-cnd ⊥̇        = δ-⊥
  Δ₀-cnd (∃̇ φ)    = δ-∃∈ (Δ₀-cnd φ)
  Δ₀-cnd (∀̇ φ)    = δ-∀∈ (Δ₀-cnd φ)
  Δ₀-cnd (∀̇∈ t φ) = δ-∀∈ (δ-⇒ δ-∈ (Δ₀-cnd φ))
  Δ₀-cnd (∃̇∈ t φ) = δ-∃∈ (δ-∧ δ-∈ (Δ₀-cnd φ))

  bnd : Formula ⟪ a ⟫ 1 → Formula ⟪ Lset σ ⟫ 1
  bnd ψ = (var zero ∈̇ con mA) ∧̇ cnd ψ

  Δ₀-bnd : (ψ : Formula ⟪ a ⟫ 1) → Δ₀ (bnd ψ)
  Δ₀-bnd ψ = δ-∧ δ-∈ (Δ₀-cnd ψ)

  -- The transfer, stated as two functions rather than a path.
  sat≈ : ∀ {n} (ψ : Formula ⟪ a ⟫ n) (δ : DA.SM ^ n)
       → (⟨ (δ DA.⊨ᵐ ψ) ⟩
           → ⟨ (repV δ) DS.⊨ᵐ (cnd ψ) ⟩)
       × (⟨ (repV δ) DS.⊨ᵐ (cnd ψ) ⟩
           → ⟨ (δ DA.⊨ᵐ ψ) ⟩)
  sat≈ (t ∈̇ u) δ =
    ( λ h →
        subst (λ W → ⟨ fst (DS.⟦ mapTm κ t ⟧ᵐ (repV δ)) ∈ W ⟩)
          (sym (tm-fst u δ))
          (subst (λ W → ⟨ W ∈ fst (DA.⟦ u ⟧ᵐ δ) ⟩)
            (sym (tm-fst t δ)) h) )
    , ( λ h →
        subst (λ W → ⟨ W ∈ fst (DA.⟦ u ⟧ᵐ δ) ⟩)
          (tm-fst t δ)
          (subst (λ W → ⟨ fst (DS.⟦ mapTm κ t ⟧ᵐ (repV δ)) ∈ W ⟩)
            (tm-fst u δ) h) )
  sat≈ (t ≐ u) δ =
    ( λ h → tm-fst t δ ∙ h ∙ sym (tm-fst u δ) )
    , ( λ h → sym (tm-fst t δ) ∙ h ∙ tm-fst u δ )
  sat≈ (φ ∧̇ χ) δ =
    ( λ { (h , h′) → sat≈ φ δ .fst h , sat≈ χ δ .fst h′ } )
    , ( λ { (h , h′) → sat≈ φ δ .snd h , sat≈ χ δ .snd h′ } )
  sat≈ (φ ∨̇ χ) δ =
    ( PT.map (Sum.map (sat≈ φ δ .fst) (sat≈ χ δ .fst)) )
    , ( PT.map (Sum.map (sat≈ φ δ .snd) (sat≈ χ δ .snd)) )
  sat≈ (φ ⇒̇ χ) δ =
    ( λ f → sat≈ χ δ .fst ∘ f ∘ sat≈ φ δ .snd )
    , ( λ f → sat≈ χ δ .snd ∘ f ∘ sat≈ φ δ .fst )
  sat≈ (¬̇ φ)    δ =
    ( λ f → f ∘ sat≈ φ δ .snd )
    , ( λ f → f ∘ sat≈ φ δ .fst )
  sat≈ ⊤̇       δ = (λ _ → tt*) , (λ h → h)
  sat≈ ⊥̇       δ = (λ h → h) , (λ h → h)
  sat≈ (∃̇ φ)   δ =
    ( PT.map λ { (xm , hxm) →
        repack xm
        , ( subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm)
          , sat≈ φ (xm ∷ δ) .fst hxm ) } )
    , ( PT.map λ { (x , (gx , hx)) →
        ( fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx )
        , ( sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .snd
              (subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
                (sym (cong (λ E → E ∷ repV δ)
                  (Σ≡Prop (λ y → snd (DS.M y)) refl)))
                hx) ) } )
  sat≈ (∀̇ φ)   δ =
    ( λ f x gx →
        subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
          (cong (λ E → E ∷ repV δ) (Σ≡Prop (λ y → snd (DS.M y)) refl))
          (sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .fst
            (f (fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx))) )
    , ( λ f xm →
        sat≈ φ (xm ∷ δ) .snd
          (f (repack xm) (subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm))) )
  sat≈ (∃̇∈ t φ) δ =
    ( PT.map λ { (xm , (g , hxm)) →
        repack xm
        , ( subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm)
          , ( subst (λ W → ⟨ fst xm ∈ W ⟩) (sym (tm-fst1 t (repack xm) δ)) g
            , sat≈ φ (xm ∷ δ) .fst hxm ) ) } )
    , ( PT.map λ { (x , (gx , (g , hx))) →
        ( fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx )
        , ( subst (λ W → ⟨ fst x ∈ W ⟩) (tm-fst1 t x δ) g
          , sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .snd
              (subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
                (sym (cong (λ E → E ∷ repV δ)
                  (Σ≡Prop (λ y → snd (DS.M y)) refl)))
                hx) ) } )
  sat≈ (∀̇∈ t φ) δ =
    ( λ f x gx g →
        subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd φ) ⟩)
          (cong (λ E → E ∷ repV δ) (Σ≡Prop (λ y → snd (DS.M y)) refl))
          (sat≈ φ ((fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx) ∷ δ) .fst
            (f (fst x , subst (λ w → ⟨ fst x ∈ w ⟩) mAEq gx)
              (subst (λ W → ⟨ fst x ∈ W ⟩) (tm-fst1 t x δ) g))) )
    , ( λ f xm g →
        sat≈ φ (xm ∷ δ) .snd
          (f (repack xm) (subst (λ w → ⟨ fst xm ∈ w ⟩) (sym mAEq) (snd xm))
            (subst (λ W → ⟨ fst xm ∈ W ⟩) (sym (tm-fst1 t (repack xm) δ)) g)) )

  -- One environment entry, two namings.
  repκ : (m : ⟪ a ⟫) → repack (DA.ι m) ≡ DS.ι (κ m)
  repκ m = Σ≡Prop (λ y → snd (DS.M y)) (sym (κEq m))

  -- The two carves are one set.
  bnd≡ : (ψ : Formula ⟪ a ⟫ 1) → DS.defSet (bnd ψ) ≡ DA.defSet ψ
  bnd≡ ψ = extensionality (DS.defSet (bnd ψ)) (DA.defSet ψ) (sub₁ , sub₂)
    where
    sub₁ : ⟨ DS.defSet (bnd ψ) ⊆ DA.defSet ψ ⟩
    sub₁ y y∈ =
      ∈∈ₛ {a = y} {b = DA.defSet ψ} .fst
        (PT.rec (snd (y ∈ DA.defSet ψ)) fromFib
          (∈∈ₛ {a = y} {b = DS.defSet (bnd ψ)} .snd y∈))
      where
      fromFib : Σ[ p ∈ Σ[ k ∈ ⟪ Lset σ ⟫ ] (⟨ DS.smallSat (bnd ψ) k ⟩) ]
                (⟪ Lset σ ⟫↪ (p .fst) ≡ y)
              → ⟨ y ∈ DA.defSet ψ ⟩
      fromFib ((k , hk) , q) = goal
        where
        hb : ⟨ (DS.ι k ∷ []) DS.⊨ᵐ (bnd ψ) ⟩
        hb = invEq (DS.⊨ᵐ-small (bnd ψ) (DS.ι k ∷ []) .snd) hk
        guard : ⟨ ⟪ Lset σ ⟫↪ k ∈ a ⟩
        guard = subst (λ w → ⟨ ⟪ Lset σ ⟫↪ k ∈ w ⟩) mAEq (fst hb)
        y∈a : ⟨ y ∈ a ⟩
        y∈a = subst (λ u → ⟨ u ∈ a ⟩) q guard
        fib = ∈-asFiber {a = y} {b = a} y∈a
        m₀ = fib .fst
        q₀ = fib .snd
        entryEq : DS.ι k ≡ DS.ι (κ m₀)
        entryEq = Σ≡Prop (λ z → snd (DS.M z))
          (q ∙ sym q₀ ∙ sym (κEq m₀))
        bodyκ : ⟨ (DS.ι (κ m₀) ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        bodyκ = subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd ψ) ⟩)
                  (cong (λ E → E ∷ []) entryEq) (snd hb)
        bodyEnv : ⟨ repV (DA.ι m₀ ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        bodyEnv =
          subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd ψ) ⟩)
            (cong (λ E → E ∷ []) (sym (repκ m₀))) bodyκ
        satA : ⟨ (DA.ι m₀ ∷ []) DA.⊨ᵐ ψ ⟩
        satA = sat≈ ψ (DA.ι m₀ ∷ []) .snd bodyEnv
        goal : ⟨ y ∈ DA.defSet ψ ⟩
        goal = subst (λ u → ⟨ u ∈ DA.defSet ψ ⟩) q₀
          (subst ⟨_⟩ (sym (DA.defSet-mem ψ m₀)) satA)

    sub₂ : ⟨ DA.defSet ψ ⊆ DS.defSet (bnd ψ) ⟩
    sub₂ y y∈ =
      ∈∈ₛ {a = y} {b = DS.defSet (bnd ψ)} .fst
        (PT.rec (snd (y ∈ DS.defSet (bnd ψ))) fromFib
          (∈∈ₛ {a = y} {b = DA.defSet ψ} .snd y∈))
      where
      fromFib : Σ[ p ∈ Σ[ m ∈ ⟪ a ⟫ ] (⟨ DA.smallSat ψ m ⟩) ]
                (⟪ a ⟫↪ (p .fst) ≡ y)
              → ⟨ y ∈ DS.defSet (bnd ψ) ⟩
      fromFib ((m , hm) , q) = goal
        where
        hs : ⟨ (DA.ι m ∷ []) DA.⊨ᵐ ψ ⟩
        hs = invEq (DA.⊨ᵐ-small ψ (DA.ι m ∷ []) .snd) hm
        hsκ : ⟨ repV (DA.ι m ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        hsκ = sat≈ ψ (DA.ι m ∷ []) .fst hs
        hsκ′ : ⟨ (DS.ι (κ m) ∷ []) DS.⊨ᵐ (cnd ψ) ⟩
        hsκ′ = subst (λ Γ → ⟨ Γ DS.⊨ᵐ (cnd ψ) ⟩)
                 (cong (λ E → E ∷ []) (repκ m)) hsκ
        guard : ⟨ ⟪ Lset σ ⟫↪ (κ m) ∈ ⟪ Lset σ ⟫↪ mA ⟩
        guard = subst (λ w → ⟨ ⟪ Lset σ ⟫↪ (κ m) ∈ w ⟩) (sym mAEq)
                  (subst (λ u → ⟨ u ∈ a ⟩) (sym (κEq m)) (DA-in m))
        hband : ⟨ (DS.ι (κ m) ∷ []) DS.⊨ᵐ (bnd ψ) ⟩
        hband = guard , hsκ′
        goal : ⟨ y ∈ DS.defSet (bnd ψ) ⟩
        goal = subst (λ u → ⟨ u ∈ DS.defSet (bnd ψ) ⟩) (κEq m ∙ q)
          (subst ⟨_⟩ (sym (DS.defSet-mem (bnd ψ) (κ m))) hband)

landing : (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
        → (A : S) (ψ : Formula ⟪ fst A ⟫ 1)
        → (δ : V ℓ) → ⟨ δ ∈ γ ⟩ → ⟨ fst A ∈ 𝒟ₒ (Lset δ) ⟩
        → ⟨ DefOf.defSet (fst A) ψ ∈ Lset γ ⟩
landing γ oγ clγ A ψ δ δ∈γ A∈𝒟δ =
  Lset-mono {α = γ} {β = +ω δ} (clγ δ δ∈γ)
    (Lset-mono {α = +ω δ} {β = sucV (sucV δ)} (+ω-iter 2 δ)
      (subst (λ w → ⟨ DefOf.defSet (fst A) ψ ∈ w ⟩) (sym (Lset-suc σ)) d∈𝒟σ))
  where
  σ : V ℓ
  σ = sucV δ
  oδ : IsOrd δ
  oδ = mem-ord {A = γ} oγ δ δ∈γ
  oσ : IsOrd σ
  oσ = suc-ord oδ
  A∈Lσ : ⟨ fst A ∈ Lset σ ⟩
  A∈Lσ = subst (λ w → ⟨ fst A ∈ w ⟩) (sym (Lset-suc δ)) A∈𝒟δ
  module X = Carrier (fst A) σ oσ A∈Lσ
  d∈𝒟σ : ⟨ DefOf.defSet (fst A) ψ ∈ 𝒟ₒ (Lset σ) ⟩
  d∈𝒟σ = 𝒟ₒ-intro (Lset σ) (DefOf.defSet (fst A) ψ)
           ∣ X.bnd ψ , X.bnd≡ ψ ∣₁

defSet-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → (A : S) → ⟨ fst A ∈ Lset γ ⟩
    → (ψ : Formula ⟪ fst A ⟫ 1)
    → ⟨ DefOf.defSet (fst A) ψ ∈ Lset γ ⟩
defSet-in-carrier-lim γ oγ clγ A hA ψ =
  PT.rec (snd (DefOf.defSet (fst A) ψ ∈ Lset γ))
    (λ { (δ , (δ∈γ , A∈𝒟δ)) → landing γ oγ clγ A ψ δ δ∈γ A∈𝒟δ })
    (Lset-out γ (fst A) hA)

-- =====================================================================
-- SECTION 5.  Numerals and pairs (LJ-1.747, 748, 749, 750).
-- =====================================================================

-- `Bound` instantiated at `lam := γ` (LJ-1.747).
module NumeralCarrier (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
                      (ω∈γ : ⟨ ω ∈ˢ γ ⟩) where
  open Closer γ oγ clγ

  ∅∈λ : ⟨ ∅ ∈ˢ γ ⟩
  ∅∈λ = oγ .fst (#∈ω zero) ω∈γ

  module B = Bound γ oγ suc∈γ ∅∈λ

numeralL-in-carrier-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢ γ ⟩
    → (k : ℕ)
    → ⟨ fst (numeralL k) ∈ˢ Lset γ ⟩
numeralL-in-carrier-lim γ oγ clγ ω∈γ = NumeralCarrier.B.num∈λ γ oγ clγ ω∈γ

-- The pairing closure at a limit, transcribed from BoundOver.pr∈λ at
-- T := Lset (LJ-1.748).
module PairLim (lam : V ℓ) (ordλ : IsOrd lam)
  (succλ : (d : V ℓ) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) where

  At : V ℓ → Type (ℓ-suc ℓ)
  At x = Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ lam ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩)

  pr∈λ : (x y : V ℓ) → ⟨ x ∈ˢ Lset lam ⟩ → ⟨ y ∈ˢ Lset lam ⟩
       → ⟨ pr x y ∈ˢ Lset lam ⟩
  pr∈λ x y hx hy = PT.rec (snd (pr x y ∈ˢ Lset lam))
    (λ px → PT.rec (snd (pr x y ∈ˢ Lset lam)) (both px) (Lset-out′ lam y hy))
    (Lset-out′ lam x hx)
    where
    climb : (σ : V ℓ) → ⟨ σ ∈ˢ lam ⟩ → ⟨ x ∈ˢ Lset σ ⟩ → ⟨ y ∈ˢ Lset σ ⟩
          → ⟨ pr x y ∈ˢ Lset lam ⟩
    climb σ σ∈ hxσ hyσ =
      Lset-mono {α = lam} {β = sucV (sucV σ)}
        (succλ (sucV σ) (succλ σ σ∈)) {x = pr x y}
        (pr∈Lset-suc σ x y hxσ hyσ)
    both : At x → At y → ⟨ pr x y ∈ˢ Lset lam ⟩
    both (δ , (δ∈ , hxδ)) (ε , (ε∈ , hyε)) =
      Sum.rec
        (λ p → climb (sucV ε) (succλ ε ε∈)
                 (Lset-mono {α = sucV ε} {β = sucV δ} p {x = x} hxδ) hyε)
        (Sum.rec
          (λ q → climb (sucV ε) (succλ ε ε∈)
                   (subst (λ w → ⟨ x ∈ˢ Lset w ⟩) q hxδ) hyε)
          (λ r → climb (sucV δ) (succλ δ δ∈) hxδ
                   (Lset-mono {α = sucV δ} {β = sucV ε} r {x = y} hyε)))
        (ord-tri (sucV δ) (suc-ord {A = δ} (mem-ord {A = lam} ordλ δ δ∈))
                 (sucV ε) (suc-ord {A = ε} (mem-ord {A = lam} ordλ ε ε∈)))

pr-in-Lset-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (x y : V ℓ)
    → ⟨ x ∈ˢ Lset γ ⟩ → ⟨ y ∈ˢ Lset γ ⟩
    → ⟨ pr x y ∈ˢ Lset γ ⟩
pr-in-Lset-lim γ oγ clγ = PairLim.pr∈λ γ oγ (Closer.suc∈γ γ oγ clγ)

-- The L presentation of the pair leaf (LJ-1.749).
prʟ-in-Lset-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    (a b : S)
    → ⟨ fst a ∈ˢ Lset γ ⟩ → ⟨ fst b ∈ˢ Lset γ ⟩
    → ⟨ fst (prʟ a b) ∈ˢ Lset γ ⟩
prʟ-in-Lset-lim γ oγ clγ a b ha hb =
  subst (λ w → ⟨ w ∈ˢ Lset γ ⟩) (sym (prʟ-fst a b))
    (pr-in-Lset-lim γ oγ clγ (fst a) (fst b) ha hb)

-- A numeral code paired with a stage member (LJ-1.750).
prʟ-numeral-in-Lset-lim :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢ γ ⟩
    → (k : ℕ) → (a : S)
    → ⟨ fst a ∈ˢ Lset γ ⟩
    → ⟨ fst (prʟ (numeralL k) a) ∈ˢ Lset γ ⟩
prʟ-numeral-in-Lset-lim γ oγ clγ ω∈γ k a ha =
  prʟ-in-Lset-lim γ oγ clγ (numeralL k) a
    (numeralL-in-carrier-lim γ oγ clγ ω∈γ k) ha

-- =====================================================================
-- SECTION 6.  The BoundedFo certificate of tagAtL (LJ-1.754).
-- =====================================================================

-- prAtL's tree is all variables, so its certificate is a closed nest
-- of Lift Units at any predicate.
prAtL-triv : ∀ {ℓp : Level} (P : S → Type ℓp) {n} (q u v : Fin n)
           → BoundedFo P (prAtL q u v)
prAtL-triv P q u v = _

tagAtL-bounded-at-γ :
    (γ : V ℓ) (oγ : IsOrd γ) (clγ : closedω γ)
    → ⟨ ω ∈ˢ γ ⟩
    → {n : ℕ}
    → (s : Fin n)
    → (k : ℕ)
    → (x : Fin n)
    → BoundedFo (λ (c : S) → ⟨ fst c ∈ˢ Lset γ ⟩) (tagAtL s k x)
tagAtL-bounded-at-γ γ oγ clγ ω∈γ s k x =
  ( lift tt , numeralL-in-carrier-lim γ oγ clγ ω∈γ k )
    , prAtL-triv (λ (c : S) → ⟨ fst c ∈ˢ Lset γ ⟩) (suc s) zero (suc x)
```
