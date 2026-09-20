{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile
import K4.AtomicGraph
import K4.Algebra
import K8.GroundSets
import NameSpace
import K9.BooleanAtomic
import K10.CohenAtomicTable
import K10.CohenGoodFormula
import K10.CohenGoodProof
import K10.CohenImageValue
import K10.CohenCompare

module K10.CohenDomain
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
open import FOL.Syntax using ( Formula )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( _^_ ; module At )
open At (ZFStructure.S 𝒮) id using ( _⊨_ )
open import Cubical.Data.Sum using ( _⊎_ ; inl ; inr )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ ; ∥_∥₁ ; squash₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module BAT = K9.BooleanAtomic 𝒮 families accessible images pow κ w lem
  using ( B ; module Atomic ; module NG ; module BK )
module GS = K8.GroundSets.Ground 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths
  BAT.NG.hasPair BAT.NG.hasUnion pow BAT.NG.hasSeparation κ
  using ( join ; join-spec )
module NS = NameSpace 𝒮
module NSB = NS.Instantiate families accessible BAT.B
module AG = K4.AtomicGraph 𝒮 paths
  using ( closedΔ ; closed-union ; entryΔ ; module Graph )
module CGF = K10.CohenGoodFormula 𝒮 BAT.NG.extensional BAT.NG.≈ˢ-paths
module CGP = K10.CohenGoodProof 𝒮 families accessible images pow κ w lem paths
module CAT = K10.CohenAtomicTable 𝒮 families accessible images pow κ w lem paths
module CIV = K10.CohenImageValue 𝒮 families accessible images pow κ w lem paths
module CMP = K10.CohenCompare 𝒮 families accessible images pow κ w lem paths

open NSB using ( hereditary )
open NSB.CR using ( ClosedFamily )

join-closed : (C D : S)
  → ⟨ AG.closedΔ BAT.B C ⟩ → ⟨ AG.closedΔ BAT.B D ⟩
  → ⟨ AG.closedΔ BAT.B (GS.join C D) ⟩
join-closed C D clC clD =
  AG.closed-union BAT.B C D (GS.join C D)
    (λ z hz → subst ⟨_⟩ (sym (GS.join-spec C D z)) ∣ inl hz ∣₁)
    (λ z hz → subst ⟨_⟩ (sym (GS.join-spec C D z)) ∣ inr hz ∣₁)
    (λ z hz → subst ⟨_⟩ (GS.join-spec C D z) hz)
    clC clD

join-inˡ : (C D z : S) → ⟨ z ∈ˢ C ⟩ → ⟨ z ∈ˢ GS.join C D ⟩
join-inˡ C D z hz = subst ⟨_⟩ (sym (GS.join-spec C D z)) ∣ inl hz ∣₁

join-inʳ : (C D z : S) → ⟨ z ∈ˢ D ⟩ → ⟨ z ∈ˢ GS.join C D ⟩
join-inʳ C D z hz = subst ⟨_⟩ (sym (GS.join-spec C D z)) ∣ inr hz ∣₁

pair-domain : (m n : S)
  → ⟨ BAT.BK.IsName m ⟩ → ⟨ BAT.BK.IsName n ⟩
  → ∥ Σ[ Cd ∈ S ] (⟨ AG.closedΔ BAT.B Cd ⟩ × ⟨ m ∈ˢ Cd ⟩ × ⟨ n ∈ˢ Cd ⟩) ∥₁
pair-domain m n hm hn =
  PT.rec squash₁
    (λ cfM → PT.rec squash₁
      (λ cfN → ∣ assemble cfM cfN ∣₁)
      (hereditary n hn))
    (hereditary m hm)
  where
  assemble : ClosedFamily m → ClosedFamily n
    → Σ[ Cd ∈ S ] (⟨ AG.closedΔ BAT.B Cd ⟩ × ⟨ m ∈ˢ Cd ⟩ × ⟨ n ∈ˢ Cd ⟩)
  assemble cfM cfN =
    GS.join (ClosedFamily.C cfM) (ClosedFamily.C cfN)
    , join-closed (ClosedFamily.C cfM) (ClosedFamily.C cfN)
        (ClosedFamily.coded cfM) (ClosedFamily.coded cfN)
    , join-inˡ (ClosedFamily.C cfM) (ClosedFamily.C cfN) m (ClosedFamily.contains cfM)
    , join-inʳ (ClosedFamily.C cfM) (ClosedFamily.C cfN) n (ClosedFamily.contains cfN)

goodAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Formula S k
goodAtˢ c h w = CGF.goodAt w c h

goodAtˢ-reading : ∀ {k} (c h w : Fin k) (γ : S ^ k)
  → (γ ⊨ goodAtˢ c h w)
    ≡ CGF.goodΔ (lookup w γ) (lookup c γ) (lookup h γ)
goodAtˢ-reading c h w γ = CGF.goodAt-reading w c h γ

module G = AG.Graph BAT.B BAT.Atomic._≈ᴮ_ BAT.Atomic._∈ᴮ_
  BAT.BK.IsName
  goodAtˢ CGF.goodΔ goodAtˢ-reading
  CGF.imgAt CGF.imgΔ CGF.imgAt-reading

tc : G.TableComparison
tc = record
  { eq-unique = λ C D H K x y b c clC clD gdH gdK →
      CMP.eq-unique C D clC clD H K x y b c gdH gdK
  ; mem-unique = λ C D H K x y b c clC clD gdH gdK →
      CMP.mem-unique C D clC clD H K x y b c gdH gdK }

canonical-table : (Cd : S) → ⟨ AG.closedΔ BAT.B Cd ⟩ → G.ValueTable Cd
canonical-table Cd cl = record
  { table = Can.graphH
  ; domain = cl
  ; good = Can.good-canonical
  ; eqVal = λ x y _ _ → BAT.Atomic._≈ᴮ_ x y
  ; memVal = λ x y _ _ → BAT.Atomic._∈ᴮ_ x y
  ; eq-entry = λ x y hx hy →
      EQ.R.entryΔ-from x y (fst (BAT.Atomic._≈ᴮ_ x y)) hx hy refl
  ; mem-entry = λ x y hx hy →
      CIV.ImageChar.Closed.img-total Cd x y hx hy cl }
  where
  module Can = CGP.Canonical Cd cl
  module EQ = CAT.EQTable Cd

canonical-adequate : (Cd : S) (cl : ⟨ AG.closedΔ BAT.B Cd ⟩)
  → G.Adequate Cd (canonical-table Cd cl)
canonical-adequate Cd cl = record
  { eq-value = λ _ _ _ _ → refl
  ; mem-value = λ _ _ _ _ → refl }

supply : G.TableSupply
supply m n hm hn =
  PT.map
    (λ { (Cd , cl , hmC , hnC) →
      Cd , canonical-table Cd cl
         , canonical-adequate Cd cl
         , hmC , hnC })
    (pair-domain m n hm hn)

atomicGraph : G.AtomicGraph
atomicGraph = G.table→graph tc supply
