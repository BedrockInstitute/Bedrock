{-# OPTIONS --cubical --safe --guardedness #-}

-- L3.31-W5p D-1 probe: the Mostowski collapse over the HIT V, in miniature.
-- Fixed ambient set u; π : V → V by ∈-recursion over the filtered small index
--   Fiber x = Σ[ m ∈ ⟪ x ⟫ ] (⟪ x ⟫↪ m ∈ₛ u),
-- i.e. the set of π-images of the members of x that lie in u.
-- Pieces: recursor + computation law, image transitivity, extensional
-- injectivity on a transitive u, and the iso reading.

open import Base.Prelude
open import Base.Truth

module ProbeCollapse {ℓ : Level} where

open import FOL.ZFStructure using ( ZFStructure; module hPropStructure; Transitive )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; ∈-induction-compute )

import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.Foundations.Equiv using ( fiber )
open import Cubical.HITs.CumulativeHierarchy.Base using ( sett; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_; ∈-asFiber; extensionality; _⊆_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- transitivity of a set u, in the absoluteness-chapter shape
isTrans : S → Type (ℓ-suc ℓ)
isTrans u = Transitive 𝒮ᵥ (λ x → x ∈ˢ u)

module Collapse (u : S) where

  -- the filtered small index: small members of x that are small members of u.
  -- The filter uses the library's SMALL membership ∈ₛ (a free smallness atom),
  -- so no resizing/impredicativity is spent; ∈∈ₛ bridges to the big
  -- membership in the statements.
  Fiber : S → Type ℓ
  Fiber x = Σ[ m ∈ ⟪ x ⟫ ] ⟨ ⟪ x ⟫↪ m ∈ₛ u ⟩

  -- the ∈-recursion step, exactly the LsetStep index discipline
  step : (x : S) → (∀ y → y ∈ᵗ x → S) → S
  step x rec = sett (Fiber x) (λ p → rec (⟪ x ⟫↪ (p .fst)) (mem p))
    where
    mem : (p : Fiber x) → ⟪ x ⟫↪ (p .fst) ∈ᵗ x
    mem p = ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .fst))

  -- piece 1: the recursor, set-valued through ∈-induction (P x = S), and its
  -- computation law as a propositional path in the h-set codomain.
  opaque
    π : S → S
    π = ∈-induction step

  opaque
    unfolding π
    π-compute : (x : S) → π x ≡ step x (λ y _ → π y)
    π-compute = ∈-induction-compute step

  -- piece 2: every member of π x is the π-image of a member of u ∩ x;
  -- the range class is transitive (x ∈ u is not even needed here).
  π-member : (x z : S) → ⟨ z ∈ˢ π x ⟩
           → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ u ⟩ × (π y ≡ z)) ∥₁
  π-member x z z∈ = PT.map mk (subst (λ w → ⟨ z ∈ˢ w ⟩) (π-compute x) z∈)
    where
    mk : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ z)
       → Σ[ y ∈ S ] (⟨ y ∈ˢ u ⟩ × (π y ≡ z))
    mk (p , q) = ⟪ x ⟫↪ (p .fst)
               , ( ∈∈ₛ {a = ⟪ x ⟫↪ (p .fst)} {b = u} .snd (p .snd)
                 , q )

  -- piece 4 (forward): members of u collapse into the image
  π∈-fwd : (x y : S) → y ∈ᵗ x → y ∈ᵗ u → ⟨ π y ∈ˢ π x ⟩
  π∈-fwd x y yx yu = subst (λ w → ⟨ π y ∈ˢ w ⟩) (sym (π-compute x)) wit
    where
    fib : fiber ⟪ x ⟫↪ y
    fib = ∈-asFiber {a = y} {b = x} yx
    m : ⟪ x ⟫
    m = fib .fst
    p : ⟪ x ⟫↪ m ≡ y
    p = fib .snd
    sm : ⟨ ⟪ x ⟫↪ m ∈ₛ u ⟩
    sm = ∈∈ₛ {a = ⟪ x ⟫↪ m} {b = u} .fst (subst (λ w → ⟨ w ∈ˢ u ⟩) (sym p) yu)
    wit : ⟨ π y ∈ˢ sett (Fiber x) (λ q → π (⟪ x ⟫↪ (q .fst))) ⟩
    wit = ∣ (m , sm) , cong π p ∣₁

  -- piece 3 + 4 (backward): double ∈-induction on a transitive u
  module Inj (uTrans : isTrans u) where

    P : S → Type (ℓ-suc ℓ)
    P x = (y : S) → x ∈ᵗ u → y ∈ᵗ u → π x ≡ π y → x ≡ y

    -- direction 1: move a member z of x into y; the IH fires at z ∈ x
    in⊆ : (x y z : S) → x ∈ᵗ u → y ∈ᵗ u → z ∈ᵗ x → z ∈ᵗ u
        → π x ≡ π y
        → ((a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ u → π a ≡ π b → a ≡ b)
        → ⟨ z ∈ₛ y ⟩
    in⊆ x y z xu yu zx zu e ih = ∈∈ₛ {a = z} {b = y} .fst
      (PT.rec (snd (z ∈ˢ y)) step2 (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute y)
        (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd x z zx zu))))
      where
      step2 : Σ[ p ∈ Fiber y ] (π (⟪ y ⟫↪ (p .fst)) ≡ π z) → ⟨ z ∈ˢ y ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ y ⟩) (sym z≡b) by
        where
        b : S
        b = ⟪ y ⟫↪ (p .fst)
        by : ⟨ b ∈ˢ y ⟩
        by = ∈∈ₛ {a = b} {b = y} .snd (∈ₛ⟪ y ⟫↪ (p .fst))
        bu : ⟨ b ∈ˢ u ⟩
        bu = uTrans {x = y} {y = b} by yu
        z≡b : z ≡ b
        z≡b = ih z zx b bu (sym q)

    -- direction 2: move a member z of y into x; the IH fires at the
    -- witness b ∈ x extracted from the collapsed membership
    out⊆ : (x y z : S) → x ∈ᵗ u → y ∈ᵗ u → z ∈ᵗ y → z ∈ᵗ u
         → π y ≡ π x
         → ((a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ u → π a ≡ π b → a ≡ b)
         → ⟨ z ∈ₛ x ⟩
    out⊆ x y z xu yu zy zu e ih = ∈∈ₛ {a = z} {b = x} .fst
      (PT.rec (snd (z ∈ˢ x)) step2 (subst (λ w → ⟨ π z ∈ˢ w ⟩) (π-compute x)
        (subst (λ w → ⟨ π z ∈ˢ w ⟩) e (π∈-fwd y z zy zu))))
      where
      step2 : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ π z) → ⟨ z ∈ˢ x ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) b≡z bx
        where
        b : S
        b = ⟪ x ⟫↪ (p .fst)
        bx : ⟨ b ∈ˢ x ⟩
        bx = ∈∈ₛ {a = b} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .fst))
        bu : ⟨ b ∈ˢ u ⟩
        bu = uTrans {x = x} {y = b} bx xu
        b≡z : b ≡ z
        b≡z = ih b bx z zu q

    step-inj : (x : S) → ((a : S) → a ∈ᵗ x → P a) → P x
    step-inj x IH y xu yu e = extensionality x y (⊆xy , ⊆yx)
      where
      ih4 : (a : S) → a ∈ᵗ x → (b : S) → b ∈ᵗ u → π a ≡ π b → a ≡ b
      ih4 a ax b bu eq = IH a ax b (uTrans {x = x} {y = a} ax xu) bu eq
      ⊆xy : ⟨ x ⊆ y ⟩
      ⊆xy z z∈ₛx = let zx = ∈∈ₛ {a = z} {b = x} .snd z∈ₛx
                   in in⊆ x y z xu yu zx (uTrans {x = x} {y = z} zx xu) e ih4
      ⊆yx : ⟨ y ⊆ x ⟩
      ⊆yx z z∈ₛy = let zy = ∈∈ₛ {a = z} {b = y} .snd z∈ₛy
                   in out⊆ x y z xu yu zy (uTrans {x = y} {y = z} zy yu) (sym e) ih4

    -- piece 3: extensional injectivity on u, by ∈-induction
    π-inj : (x y : S) → x ∈ᵗ u → y ∈ᵗ u → π x ≡ π y → x ≡ y
    π-inj = ∈-induction step-inj

    -- piece 4 (backward)
    π∈-bwd : (x y : S) → x ∈ᵗ u → y ∈ᵗ u → ⟨ π y ∈ˢ π x ⟩ → y ∈ᵗ x
    π∈-bwd x y xu yu h =
      PT.rec (snd (y ∈ˢ x)) step2 (subst (λ w → ⟨ π y ∈ˢ w ⟩) (π-compute x) h)
      where
      step2 : Σ[ p ∈ Fiber x ] (π (⟪ x ⟫↪ (p .fst)) ≡ π y) → ⟨ y ∈ˢ x ⟩
      step2 (p , q) = subst (λ w → ⟨ w ∈ˢ x ⟩) (c≡y) cx
        where
        c : S
        c = ⟪ x ⟫↪ (p .fst)
        cx : ⟨ c ∈ˢ x ⟩
        cx = ∈∈ₛ {a = c} {b = x} .snd (∈ₛ⟪ x ⟫↪ (p .fst))
        cu : ⟨ c ∈ˢ u ⟩
        cu = uTrans {x = x} {y = c} cx xu
        c≡y : c ≡ y
        c≡y = π-inj c y cu yu q

    -- piece 4: the iso reading on members of u, both directions
    iso : (x y : S) → x ∈ᵗ u → y ∈ᵗ u
        → (⟨ y ∈ˢ x ⟩ → ⟨ π y ∈ˢ π x ⟩) × (⟨ π y ∈ˢ π x ⟩ → ⟨ y ∈ˢ x ⟩)
    iso x y xu yu = (λ yx → π∈-fwd x y yx yu) , π∈-bwd x y xu yu
