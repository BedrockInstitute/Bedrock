{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.GraphNames
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
import K9.NameGround
import K9.IndexedNames
import K9.PairNames
import K9.RealNames

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Ground = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module K; module Check; chk-name )
module Indexed = K9.IndexedNames 𝒮 families accessible images pow κ w
  using ( indexed; supportBound; indexed-support )
module Pair = K9.PairNames 𝒮 families accessible images pow κ w using ( orderedNm )
module Real = K9.RealNames 𝒮 families accessible images pow κ w using ( real )
private
  module K = Ground.K
  module Check = Ground.Check

checkNm : S → K.Name
checkNm a = Check.chk a , Ground.chk-name a

vertex : S → K.Name
vertex α = Pair.orderedNm (checkNm α) (Real.real α)

graph : K.Name
graph = Indexed.indexed κ vertex

graphCode : S
graphCode = fst graph

graphSupport : S
graphSupport = Indexed.supportBound κ (λ α → fst (vertex α))

graph-support : (x : S) → K.Child x graphCode → ⟨ x ∈ˢ graphSupport ⟩
graph-support x = Indexed.indexed-support κ (λ α → fst (vertex α)) x
