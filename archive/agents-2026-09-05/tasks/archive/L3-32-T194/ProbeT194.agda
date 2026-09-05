{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T194] D22 gate: the Q-lim residue at a general limit.
-- Probe: state Q-lim at a general limit over the delivered first-limit
-- instance and measure the transfer.  Part 1 measures the landing frame
-- (the parts that re-instantiate from delivered machinery: the carrier
-- geometry, the full switch at (γ l, U l), the union closure, the union
-- assembly), with the family equality at the carrier as module parameters
-- (the content the transfer would have to build).  Part 2 records the
-- induction answer: the tower hypothesis IS the induction hypothesis at
-- the smaller ordinals, so Q-lim at a smaller limit is available; the
-- T185-style frame is the delivered qstep (Bridge:1055-1078), not new
-- content.  Part 3 records the structural obstruction on the transfer's
-- non-overshoot side: the first-limit carve-⊇ moved the exact bound into
-- ω by ord∈HF→∈ω (HF:224), the carrier's ordinal content at the FIRST
-- limit; at a general limit the carrier is Sset (U l), whose ordinal
-- members reach up to U l, and "a ∈ U l" does not imply "a < l"
-- (witness: sucV ω ∈ U ω ∖ ω).  Untracked probe, never committed, no
-- git, no master, no postulate, no hole, no TERMINATING.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT194 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV; ∈-irrefl )
open import V.Model {ℓ} using ( self∈sucV )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ω; ⋃_; union-ax; module InfinitySet )
open InfinitySet using ( sucV; #_ )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( ∅-ord; #∈ω )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit )
open import L.Rud.OrdBlocks {ℓ} lem using ( +ω-in )
open import L.Rud.Step {ℓ} lem ∅ using
  ( Sset; Jset-rud; f5; Fof-f5; limit-succ-mem )
open import L.Rud.Bridge {ℓ} lem ∅ using
  ( U; U-lim; Ul∈γl; γ; γ-lim; γ-suc; γδ⊆U; Lset-union-limit )
open import L.Rud.SatSets {ℓ} lem ∅ using ( module LimitFullSwitch )
open import L.Rud.HF {ℓ} lem ∅ using ( γ∅≡ω )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; _∈ₛ_; ⟪_⟫ )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Extensional equality from the two inclusions (the tree's standing form).
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ {u} {v} sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

-- -------------------------------------------------------------------------
-- Part 1: the general Q-lim clause at a general limit l.  The landing
-- frame re-instantiates from delivered machinery; the family equality at
-- the carrier (σ, F, carve-⊆, carve-⊇) is the content the transfer would
-- have to build, stated here as module parameters (T185's stepHyp shape).
-- -------------------------------------------------------------------------
module GeneralQlim
  (l : S) (ordl : IsOrd l) (liml : ⟨ isLimit l ⟩)
  (tower : (δ : S) → ⟨ δ ∈ˢ l ⟩ → ⟨ Lset δ ∈ˢ Sset (γ δ) ⟩)
  (σ : Formula ⟪ Sset (U l) ⟫ 1)
  (F : S) (F≡ : F ≡ DefOf.defSet (Sset (U l)) σ)
  (carve-⊆ : (y : S) → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ l ⟩ × (y ≡ Lset δ)) ∥₁
           → ⟨ y ∈ˢ F ⟩)
  (carve-⊇ : (y : S) → ⟨ y ∈ˢ F ⟩
           → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ l ⟩ × (y ≡ Lset δ)) ∥₁)
  where

  -- The T185 question, answered in code: the tower hypothesis supplies Q
  -- at every smaller ordinal, in particular Q-lim at every smaller limit.
  Q-smaller : (μ : S) → ⟨ μ ∈ˢ l ⟩ → ⟨ isLimit μ ⟩ → ⟨ Lset μ ∈ˢ Sset (γ μ) ⟩
  Q-smaller μ μ∈l _ = tower μ μ∈l

  -- The full switch at the landing pair (γ l, U l).  The certificate
  -- U l ∈ γ l and the sup-is-limit fact are delivered (Bridge:853-859).
  module LFS = LimitFullSwitch (γ l) (γ-lim l) (U l) (U-lim l liml) (Ul∈γl l)

  -- The family lands one ω-block above the running sup.
  landing : ⟨ F ∈ˢ Sset (γ l) ⟩
  landing = subst (λ w → ⟨ w ∈ˢ Sset (γ l) ⟩) (sym F≡) (LFS.full-switch-⊇ σ)

  -- The limit stage is the union of the family, both directions.
  Lsetl≡⋃F : Lset l ≡ (⋃ F)
  Lsetl≡⋃F = ext-⊆ L⊆⋃F ⋃F⊆L
    where
    L⊆⋃F : Lset l ⊆ (⋃ F)
    L⊆⋃F x x∈L = PT.rec (snd (x ∈ˢ (⋃ F))) go (Lset-union-limit l liml x x∈L)
      where
      go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ l ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩) → ⟨ x ∈ˢ (⋃ F) ⟩
      go (δ , δ∈l , x∈Lsuc) = ∈∈ₛ {a = x} {b = ⋃ F} .snd
        (union-ax F x .snd ∣ Lset (sucV δ) , (Lset∈ₛF , x∈ₛLsuc) ∣₁)
        where
        sδ∈l : ⟨ sucV δ ∈ˢ l ⟩
        sδ∈l = limit-succ-mem l δ liml δ∈l
        Lset∈F : ⟨ Lset (sucV δ) ∈ˢ F ⟩
        Lset∈F = carve-⊆ (Lset (sucV δ)) ∣ sucV δ , (sδ∈l , refl) ∣₁
        Lset∈ₛF : ⟨ Lset (sucV δ) ∈ₛ F ⟩
        Lset∈ₛF = ∈∈ₛ {a = Lset (sucV δ)} {b = F} .fst Lset∈F
        x∈ₛLsuc : ⟨ x ∈ₛ Lset (sucV δ) ⟩
        x∈ₛLsuc = ∈∈ₛ {a = x} {b = Lset (sucV δ)} .fst x∈Lsuc
    ⋃F⊆L : (⋃ F) ⊆ Lset l
    ⋃F⊆L x x∈⋃ = PT.rec (snd (x ∈ˢ Lset l)) go
      (union-ax F x .fst (∈∈ₛ {a = x} {b = ⋃ F} .fst x∈⋃))
      where
      go : Σ[ f ∈ S ] (⟨ f ∈ₛ F ⟩ × ⟨ x ∈ₛ f ⟩) → ⟨ x ∈ˢ Lset l ⟩
      go (f , (f∈ₛF , x∈ₛf)) = PT.rec (snd (x ∈ˢ Lset l)) fStep (carve-⊇ f f∈F)
        where
        f∈F : ⟨ f ∈ˢ F ⟩
        f∈F = ∈∈ₛ {a = f} {b = F} .snd f∈ₛF
        x∈f : ⟨ x ∈ˢ f ⟩
        x∈f = ∈∈ₛ {a = x} {b = f} .snd x∈ₛf
        fStep : Σ[ δ ∈ S ] (⟨ δ ∈ˢ l ⟩ × (f ≡ Lset δ)) → ⟨ x ∈ˢ Lset l ⟩
        fStep (δ , δ∈l , f≡) = Lset-mono {α = l} {β = δ} δ∈l
          (subst (λ w → ⟨ x ∈ˢ w ⟩) f≡ x∈f)

  -- The union lands in the same level, by the rud closure's union op.
  ⋃F∈Ssetγl : ⟨ (⋃ F) ∈ˢ Sset (γ l) ⟩
  ⋃F∈Ssetγl = subst (λ w → ⟨ w ∈ˢ Sset (γ l) ⟩) (Fof-f5 F F)
    (Jset-rud (γ l) (γ-lim l) f5 F F landing landing)

  -- The general clause's conclusion at l, the type of
  -- Q-lim-statement l ordl liml tower (Bridge:983-986): from the tower
  -- hypothesis at a general limit, the landing closes.
  Q-lim-closed : ⟨ Lset l ∈ˢ Sset (γ l) ⟩
  Q-lim-closed = subst (λ w → ⟨ w ∈ˢ Sset (γ l) ⟩) (sym Lsetl≡⋃F) ⋃F∈Ssetγl

-- -------------------------------------------------------------------------
-- Part 2: the transfer's non-overshoot side does not re-instantiate.  The
-- first-limit carve-⊇ moved the exact bound into ω by ord∈HF→∈ω
-- (HF:224-225), the carrier's ordinal content at the FIRST limit, proved
-- there by finiteness and tally (HF:100-224), not by a general argument.
-- At a general limit the carrier is Sset (U l), and the analogous bridge
-- "a ∈ U l → a < l" is FALSE: at the first limit's own configuration,
-- ω ∈ U ω ∖ ω (the first limit is a member of its own running sup but is
-- not below itself).
-- -------------------------------------------------------------------------
module Obstruction where

  -- ω ∈ γ 1 = +ω (γ ∅) = +ω ω: the tower's successor step holds the
  -- first limit itself.
  ω∈γ1 : ⟨ ω ∈ˢ γ (sucV ∅) ⟩
  ω∈γ1 = subst (λ w → ⟨ ω ∈ˢ w ⟩) (sym (γ-suc ∅ ∅-ord))
    (+ω-in (γ ∅) ω 0
      (subst (λ w → ⟨ ω ∈ˢ sucV w ⟩) (sym γ∅≡ω) (self∈sucV ω)))

  -- The tower value at 1 lies inside the running sup at ω.
  ω∈Uω : ⟨ ω ∈ˢ U ω ⟩
  ω∈Uω = γδ⊆U ω (# 1) (#∈ω 1) ω ω∈γ1

  -- But ω is not below itself.
  ω∉ω : ⟨ ω ∈ˢ ω ⟩ → Empty.⊥
  ω∉ω h = ∈-irrefl ω h
