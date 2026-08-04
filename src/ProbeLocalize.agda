{-# OPTIONS --cubical --safe --guardedness #-}
-- ProbeLocalize: the [L3.31-R2p] D-1 probe.
--
-- QUESTION (from _build/p2-fork-recon.md 2.0): does `LsetGraph` localize from
-- the class carrier 𝒮ʟ to a rud level ⟪ Sset γ ⟫, i.e. is `hierL λ` a
-- `DefOf.defSet` over `Sset γ`?
--
-- Probe-local, untracked, exempt from make check and from the literate format.
-- No postulates, no holes, no TERMINATING pragmas.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeLocalize {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraph )
open import Cubical.Data.Nat using ( ℕ; zero; suc; _+_ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import L.Constructible {ℓ} using ( isL; isL-trans; IsOrd; Lset; 𝒮ʟ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Hierarchy {ℓ} lem using ( hierL; hierL-spec; IsHier; Recorded )
open import L.Rud.Step {ℓ} lem A using ( Sset )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.CodeSet {ℓ} lem A using ( module InLevel )

open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Coding.Model {ℓ} using ( prʟ; prʟ-fst )

open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; _⊆_; ∈∈ₛ; ∈-asFiber; extensionality )
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( S ; _∈ˢ_ )
open hPropStructure 𝒮ʟ using () renaming ( S to Sʟ )

------------------------------------------------------------------------
-- P1.  The target statement.
------------------------------------------------------------------------

-- `hierL λ` is a definable subset of the rud level `Sset γ`.
Localizes : (γ lam : V ℓ) → ⟨ isL lam ⟩ → IsOrd lam → Type (ℓ-suc ℓ)
Localizes γ lam hl ol =
  Σ[ φ ∈ Formula ⟪ Sset γ ⟫ 1 ]
    (DefOf.defSet (Sset γ) φ ≡ fst (hierL lam hl ol))

------------------------------------------------------------------------
-- P2.  The containment half:  hierL λ ⊆ Sset γ.
------------------------------------------------------------------------

module Contain (γ lam : V ℓ) (limγ : ⟨ isLimit γ ⟩)
               (hl : ⟨ isL lam ⟩) (ol : IsOrd lam)
               -- (h2a) every ordinal below λ is a member of the rud level
               (h2a : (β : S) → ⟨ β ∈ˢ lam ⟩ → ⟨ β ∈ˢ Sset γ ⟩)
               -- (h2b) every L-level below λ is a member of the rud level
               (h2b : (β : S) → ⟨ β ∈ˢ lam ⟩ → ⟨ Lset β ∈ˢ Sset γ ⟩)
               where

  open InLevel γ limγ using ( pr∈J )

  H : Sʟ
  H = hierL lam hl ol

  sp : IsHier lam H
  sp = hierL-spec lam hl ol

  contain : (z : Sʟ) → ⟨ fst z ∈ˢ fst H ⟩ → ⟨ fst z ∈ˢ Sset γ ⟩
  contain z z∈ = PT.rec (snd (fst z ∈ˢ Sset γ)) read (subst ⟨_⟩ (sp z) z∈)
    where
    read : Σ[ c ∈ Sʟ ] (⟨ fst c ∈ˢ lam ⟩
             × (fst z ≡ pr (fst c) (Lset (fst c))))
         → ⟨ fst z ∈ˢ Sset γ ⟩
    read (c , (c∈ , eq)) = subst (λ w → ⟨ w ∈ˢ Sset γ ⟩) (sym eq)
      (pr∈J (fst c) (Lset (fst c)) (h2a (fst c) c∈) (h2b (fst c) c∈))

------------------------------------------------------------------------
-- P3.  The assembly: crossing hypothesis in, `Localizes` out.
------------------------------------------------------------------------

-- The inner satisfaction of a one-variable formula at a member of the rud
-- level.  This is the face `defSet` is specified against.
Sat1 : (γ : V ℓ) → Formula ⟪ Sset γ ⟫ 1 → ⟪ Sset γ ⟫ → Type (ℓ-suc ℓ)
Sat1 γ φ m = ⟨ DefOf._⊨ᵐ_ (Sset γ) (DefOf.ι (Sset γ) m ∷ []) φ ⟩

-- Every set the internal hierarchy records is constructible: it is a pair of
-- an ordinal below λ with the tower's value there, and the model has pairing.
recL : (lam : V ℓ) → IsOrd lam → (y : S) → ⟨ Recorded lam y ⟩ → ⟨ isL y ⟩
recL lam ol y = PT.rec (snd (isL y)) read
  where
  read : Σ[ c ∈ Sʟ ] (⟨ fst c ∈ˢ lam ⟩ × (y ≡ pr (fst c) (Lset (fst c))))
       → ⟨ isL y ⟩
  read (c , (c∈ , eq)) = subst (λ w → ⟨ isL w ⟩) (sym (eq ∙ sym q)) (snd P)
    where
    oc : IsOrd (fst c)
    oc = mem-ord {A = lam} ol (fst c) c∈
    P : Sʟ
    P = prʟ c (LsetS (fst c) oc)
    q : fst P ≡ pr (fst c) (Lset (fst c))
    q = prʟ-fst c (LsetS (fst c) oc)

module Assemble (γ lam : V ℓ) (limγ : ⟨ isLimit γ ⟩)
                (hl : ⟨ isL lam ⟩) (ol : IsOrd lam)
                (h2a : (β : S) → ⟨ β ∈ˢ lam ⟩ → ⟨ β ∈ˢ Sset γ ⟩)
                (h2b : (β : S) → ⟨ β ∈ˢ lam ⟩ → ⟨ Lset β ∈ˢ Sset γ ⟩)
                (φ : Formula ⟪ Sset γ ⟫ 1)
                -- THE CROSSING, both directions, at the rud carrier.
                (cross-out : (m : ⟪ Sset γ ⟫)
                           → Sat1 γ φ m
                           → ⟨ Recorded lam (⟪ Sset γ ⟫↪ m) ⟩)
                (cross-in : (m : ⟪ Sset γ ⟫)
                          → ⟨ Recorded lam (⟪ Sset γ ⟫↪ m) ⟩
                          → Sat1 γ φ m)
                where

  open Contain γ lam limγ hl ol h2a h2b using ( H; sp; contain )
  open DefOf (Sset γ) using ( defSet; defSet-mem; defSet⊆A )

  sub₁ : ⟨ defSet φ ⊆ fst H ⟩
  sub₁ y y∈ₛ = ∈∈ₛ {a = y} {b = fst H} .fst
    (subst ⟨_⟩ (sym (sp z)) rec)
    where
    y∈ : ⟨ y ∈ˢ defSet φ ⟩
    y∈ = ∈∈ₛ {a = y} {b = defSet φ} .snd y∈ₛ
    fy : Σ[ m ∈ ⟪ Sset γ ⟫ ] (⟪ Sset γ ⟫↪ m ≡ y)
    fy = ∈-asFiber {a = y} {b = Sset γ} (defSet⊆A φ y y∈)
    sat : Sat1 γ φ (fy .fst)
    sat = subst ⟨_⟩ (defSet-mem φ (fy .fst))
      (subst (λ w → ⟨ w ∈ˢ defSet φ ⟩) (sym (fy .snd)) y∈)
    rec : ⟨ Recorded lam y ⟩
    rec = subst (λ w → ⟨ Recorded lam w ⟩) (fy .snd)
            (cross-out (fy .fst) sat)
    z : Sʟ
    z = y , recL lam ol y rec

  sub₂ : ⟨ fst H ⊆ defSet φ ⟩
  sub₂ y y∈ₛ = ∈∈ₛ {a = y} {b = defSet φ} .fst
    (subst (λ w → ⟨ w ∈ˢ defSet φ ⟩) (fy .snd)
      (subst ⟨_⟩ (sym (defSet-mem φ (fy .fst)))
        (cross-in (fy .fst)
          (subst (λ w → ⟨ Recorded lam w ⟩) (sym (fy .snd)) rec))))
    where
    y∈ : ⟨ y ∈ˢ fst H ⟩
    y∈ = ∈∈ₛ {a = y} {b = fst H} .snd y∈ₛ
    yL : ⟨ isL y ⟩
    yL = isL-trans {x = fst H} {y = y} y∈ (snd H)
    rec : ⟨ Recorded lam y ⟩
    rec = subst ⟨_⟩ (sp (y , yL)) y∈
    fy : Σ[ m ∈ ⟪ Sset γ ⟫ ] (⟪ Sset γ ⟫↪ m ≡ y)
    fy = ∈-asFiber {a = y} {b = Sset γ} (contain (y , yL) y∈)

  result : Localizes γ lam hl ol
  result = φ , extensionality (defSet φ) (fst H) (sub₁ , sub₂)

------------------------------------------------------------------------
-- P4.  How big is the object the crossing has to traverse?
------------------------------------------------------------------------
-- The crossing needs `LsetGraph` re-read at ⟪ Sset γ ⟫.  Its constant domain
-- is Sʟ, so it must first be relabelled along a map into ⟪ Sset γ ⟫, which
-- costs a `BoundedFo` certificate: one component per node of the formula.
-- These two measurements price that walk (and time the conversion).

szTm : ∀ {K : Type (ℓ-suc ℓ)} {n} → Term K n → ℕ
szTm (con _) = 1
szTm (var _) = 1

sz : ∀ {K : Type (ℓ-suc ℓ)} {n} → Formula K n → ℕ
sz (t ∈̇ u)  = szTm t + szTm u
sz (t ≐ u)  = szTm t + szTm u
sz (φ ∧̇ ψ)  = suc (sz φ + sz ψ)
sz (φ ∨̇ ψ)  = suc (sz φ + sz ψ)
sz (φ ⇒̇ ψ)  = suc (sz φ + sz ψ)
sz (¬̇ φ)    = suc (sz φ)
sz ⊤̇        = 1
sz ⊥̇        = 1
sz (∃̇ φ)    = suc (sz φ)
sz (∀̇ φ)    = suc (sz φ)
sz (∀̇∈ t φ) = suc (szTm t + sz φ)
sz (∃̇∈ t φ) = suc (szTm t + sz φ)

ncTm : ∀ {K : Type (ℓ-suc ℓ)} {n} → Term K n → ℕ
ncTm (con _) = 1
ncTm (var _) = 0

nc : ∀ {K : Type (ℓ-suc ℓ)} {n} → Formula K n → ℕ
nc (t ∈̇ u)  = ncTm t + ncTm u
nc (t ≐ u)  = ncTm t + ncTm u
nc (φ ∧̇ ψ)  = nc φ + nc ψ
nc (φ ∨̇ ψ)  = nc φ + nc ψ
nc (φ ⇒̇ ψ)  = nc φ + nc ψ
nc (¬̇ φ)    = nc φ
nc ⊤̇        = 0
nc ⊥̇        = 0
nc (∃̇ φ)    = nc φ
nc (∀̇ φ)    = nc φ
nc (∀̇∈ t φ) = ncTm t + nc φ
nc (∃̇∈ t φ) = ncTm t + nc φ

measure-size : sz LsetGraph ≡ 169683
measure-size = refl

measure-cons : nc LsetGraph ≡ 1688
measure-cons = refl

-- Unbounded quantifiers.  `abs₀` (Δ₀ absoluteness) applies only when there
-- are none; `σ₁-up`/`π₁-down` only strip LEADING unbounded quantifiers of one
-- kind over a Δ₀ core.  Both counts below are the whole verdict on whether
-- any delivered transfer theorem reaches this formula.

nEx : ∀ {K : Type (ℓ-suc ℓ)} {n} → Formula K n → ℕ
nEx (t ∈̇ u)  = 0
nEx (t ≐ u)  = 0
nEx (φ ∧̇ ψ)  = nEx φ + nEx ψ
nEx (φ ∨̇ ψ)  = nEx φ + nEx ψ
nEx (φ ⇒̇ ψ)  = nEx φ + nEx ψ
nEx (¬̇ φ)    = nEx φ
nEx ⊤̇        = 0
nEx ⊥̇        = 0
nEx (∃̇ φ)    = suc (nEx φ)
nEx (∀̇ φ)    = nEx φ
nEx (∀̇∈ t φ) = nEx φ
nEx (∃̇∈ t φ) = nEx φ

nAll : ∀ {K : Type (ℓ-suc ℓ)} {n} → Formula K n → ℕ
nAll (t ∈̇ u)  = 0
nAll (t ≐ u)  = 0
nAll (φ ∧̇ ψ)  = nAll φ + nAll ψ
nAll (φ ∨̇ ψ)  = nAll φ + nAll ψ
nAll (φ ⇒̇ ψ)  = nAll φ + nAll ψ
nAll (¬̇ φ)    = nAll φ
nAll ⊤̇        = 0
nAll ⊥̇        = 0
nAll (∃̇ φ)    = nAll φ
nAll (∀̇ φ)    = suc (nAll φ)
nAll (∀̇∈ t φ) = nAll φ
nAll (∃̇∈ t φ) = nAll φ

measure-ex : nEx LsetGraph ≡ 2287
measure-ex = refl

measure-all : nAll LsetGraph ≡ 2159
measure-all = refl
