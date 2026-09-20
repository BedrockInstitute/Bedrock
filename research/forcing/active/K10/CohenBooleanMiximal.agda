{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import Cubical.HITs.PropositionalTruncation as PT
import K4.Algebra
import K6.NameBuildAtGround
import K9.BooleanAtomic
import K9.BooleanNameGround
import K9.NameGround
import K10.CohenBooleanCands

module K10.CohenBooleanMiximal
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
module NB = K6.NameBuildAtGround.Seam 𝒮 families accessible NG.C.carrier
module Cands = K10.CohenBooleanCands 𝒮 families accessible images pow κ w
module BNG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
open BNG using ( module Translation )
module BAT = K9.BooleanAtomic.Atomic 𝒮 families accessible images pow κ w lem
  using ( _∈ᴮ_ )
open K4.Algebra 𝒮 using ( Pt )
open K4.Algebra.Lattice BNG.IC.codedLattice using ( ⊤ᴮ ; ⊤-greatest )

open NG using ( ≈ˢ-paths )
open NG.GS using ( ≈→≡ )

omegaDom : S
omegaDom = NB.BG.support (NG.Check.chk w)

memCode : S → S → S
memCode x τ = fst (BAT._∈ᴮ_ (Translation.trᴮ x) τ)

opaque
  spreadBelow : S → S → S
  spreadBelow x b = NG.Image.imageOn b (λ p → NG.K.entry x p)

  spreadBelow-spec : (x b e : S)
    → (e ∈ˢ spreadBelow x b)
      ≡ ⋁ S (λ p → (p ∈ˢ b) ⊓ (e ≈ˢ NG.K.entry x p))
  spreadBelow-spec x b = NG.Image.imageOn-spec b (λ p → NG.K.entry x p)

  miximalOf : S → S
  miximalOf τ =
    NG.Union.bigUnion
      (NG.Image.imageOn omegaDom (λ x → spreadBelow x (memCode x τ)))

  miximal-spec : (τ e : S)
    → (e ∈ˢ miximalOf τ)
      ≡ ⋁ S (λ x → (x ∈ˢ omegaDom) ⊓
           ⋁ S (λ p → (p ∈ˢ memCode x τ) ⊓ (e ≈ˢ NG.K.entry x p)))
  miximal-spec τ e = ⇔toPath forward backward
    where
    Target : Ω
    Target = ⋁ S (λ x → (x ∈ˢ omegaDom) ⊓
      ⋁ S (λ p → (p ∈ˢ memCode x τ) ⊓ (e ≈ˢ NG.K.entry x p)))

    layers : S
    layers = NG.Image.imageOn omegaDom (λ x → spreadBelow x (memCode x τ))

    forward : ⟨ e ∈ˢ miximalOf τ ⟩ → ⟨ Target ⟩
    forward h = PT.rec (snd Target)
      (λ { (u , hu , eu) → PT.map
        (λ { (x , hx , eq) → x , hx ,
          subst ⟨_⟩ (spreadBelow-spec x (memCode x τ) e)
            (subst (λ z → ⟨ e ∈ˢ z ⟩) (≈→≡ eq) eu) })
        (subst ⟨_⟩ (NG.Image.imageOn-spec omegaDom
          (λ x → spreadBelow x (memCode x τ)) u) hu) })
      (subst ⟨_⟩ (NG.Union.bigUnion-spec layers e) h)

    backward : ⟨ Target ⟩ → ⟨ e ∈ˢ miximalOf τ ⟩
    backward = PT.rec (snd (e ∈ˢ miximalOf τ))
      (λ { (x , hx , ps) → subst ⟨_⟩
        (sym (NG.Union.bigUnion-spec layers e))
        ∣ spreadBelow x (memCode x τ)
        , subst ⟨_⟩
            (sym (NG.Image.imageOn-spec omegaDom
              (λ y → spreadBelow y (memCode y τ))
              (spreadBelow x (memCode x τ))))
            ∣ x , hx ,
              subst ⟨_⟩ (sym (≈ˢ-paths
                (spreadBelow x (memCode x τ))
                (spreadBelow x (memCode x τ)))) refl ∣₁
        , subst ⟨_⟩ (sym (spreadBelow-spec x (memCode x τ) e)) ps ∣₁ })

weight-in-carrier : (x τ p : S)
  → ⟨ p ∈ˢ memCode x τ ⟩
  → ⟨ p ∈ˢ NG.C.carrier ⟩
weight-in-carrier x τ p hp =
  subst (λ z → ⟨ p ∈ˢ z ⟩) top-is-carrier
    (⊤-greatest (BAT._∈ᴮ_ (Translation.trᴮ x) τ) p hp)
  where
  top-is-carrier : fst ⊤ᴮ ≡ NG.C.carrier
  top-is-carrier = refl

child-is-source-name : (x : S) → ⟨ x ∈ˢ omegaDom ⟩ → ⟨ NG.K.IsName x ⟩
child-is-source-name x hx =
  NB.BG.support-valid (NG.Check.chk w) (NG.chk-name w) x hx

miximal-name : (τ : S) → ⟨ NG.K.IsName (miximalOf τ) ⟩
miximal-name τ = NG.entries-name (miximalOf τ) λ e he → PT.rec PT.squash₁
  (λ { (x , hx , ps) → PT.map
    (λ { (p , hp , ep) →
      x , p , ≈→≡ ep , weight-in-carrier x τ p hp , child-is-source-name x hx })
    ps })
  (subst ⟨_⟩ (miximal-spec τ e) he)

miximal-child : (τ x : S) → NG.K.Child x (miximalOf τ) → ⟨ x ∈ˢ omegaDom ⟩
miximal-child τ x = PT.rec (snd (x ∈ˢ omegaDom))
  (λ { (b , hb) → PT.rec (snd (x ∈ˢ omegaDom))
    (λ { (y , hy , ps) → PT.rec (snd (x ∈ˢ omegaDom))
      (λ { (p , hp , ep) →
        subst (λ z → ⟨ z ∈ˢ omegaDom ⟩)
          (sym (fst (NG.K.entry-inj (≈→≡ ep)))) hy })
      ps })
    (subst ⟨_⟩ (miximal-spec τ (NG.K.entry x b)) hb) })

miximal-in-cands : (τ : S) → ⟨ miximalOf τ ∈ˢ Cands.cands ⟩
miximal-in-cands τ =
  NB.Valid.candidates-contains NG.hasSeparation pow (NG.Check.chk w)
    (miximalOf τ) (miximal-name τ) (miximal-child τ)

miximal-entry : (τ x p : S)
  → ⟨ x ∈ˢ omegaDom ⟩
  → ⟨ p ∈ˢ memCode x τ ⟩
  → ⟨ NG.K.entry x p ∈ˢ miximalOf τ ⟩
miximal-entry τ x p hx hp =
  subst ⟨_⟩ (sym (miximal-spec τ (NG.K.entry x p)))
    ∣ x , hx , ∣ p , hp ,
      subst ⟨_⟩ (sym (≈ˢ-paths (NG.K.entry x p) (NG.K.entry x p))) refl ∣₁ ∣₁
