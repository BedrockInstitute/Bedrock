{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K10.CohenPreservation {ℓ}
  (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  (lem : LEM ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import GroundDescription
import K8.GroundSets
import K8.CohenCCC
open import CodedVocabulary 𝒮 using ( prAtˢ; isKPairΔ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import FOL.Semantics
import ForcingNotion
import CardinalBridge
import K7.CardinalOrder
import K7.PossibleValues
import K7.PreservationAtTruth
import K7.ChainConditions
import K7.CountableOrdinalSuccessor
import K7.OrdinalSquare
import K4.Algebra
import K4.Implication
import K5.InstanceBase
import K5.ExtensionSat
import K6.TruthSeam
import K6.Definability
import K6.ForcesTruth
import K9.NameGround
import K9.BooleanNameGround
import K10.CheckedForcing
import K10.CohenAgreementSeam
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

module NG = K9.NameGround 𝒮 families accessible images pow κ w
  using ( extensional; ≈ˢ-paths; hasPair; hasUnion; hasSeparation; hasCollect; core
    ; module C; module K; module GS; module Check; module PS; notion; chk-name; empty-spec )
module BG = K9.BooleanNameGround 𝒮 families accessible images pow κ w lem
  using ( B; entry-agrees; module BK; module Base; module IC; module Atomic; module Translation )
module Checks = K10.CheckedForcing 𝒮 families accessible images pow κ w lem
  using ( checked-name; checked-name-reflection; module Forcing; module Frame )
module BooleanKernel = NameKernel.Kernel 𝒮 NG.core accessible BG.B
  using ( child-is-name )
module Order = ForcingNotion.ForcingNotion NG.notion
  using ( _≼_; ≼-refl; ≼-trans; nonempty )
module GroundCardinal = CardinalBridge 𝒮 using ( IsOrdinalφ; isCardinal; isOmega; injectable )
module Ordinals = K7.CardinalOrder 𝒮 using ( Δ₀-IsOrdinalφ )
module GroundSemantics = FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
module GroundSat = GroundSemantics.At S id using ( _⊨_ )
module Names = K7.PossibleValues.Names 𝒮 NG.≈ˢ-paths NG.K.IsName using ( codesOf )
module Chain = K7.ChainConditions 𝒮 NG.extensional NG.≈ˢ-paths using ( CCC₂ᴵ )
module Dense = K5.InstanceBase.AtDense 𝒮 NG.extensional pow NG.hasSeparation
  NG.≈ˢ-paths NG.C.presentation NG.C.laws lem using ( codeOfBelow; belowOfCode )
module TSM = K6.TruthSeam 𝒮 NG.extensional NG.≈ˢ-paths NG.hasSeparation
  NG.C.carrier NG.C.order BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
  (BG.Base.codedBase lem) BG.BK.IsName using ( module TAF; Nameᴮ )

open K4.Algebra 𝒮 using ( Pt; _≤ᴮ_ )
open K4.Implication 𝒮 NG.extensional NG.≈ˢ-paths BG.B BG.IC.codedLattice
  BG.IC.codedComplement using ( _⊓ᴮ_; _⊔ᴮ_; _⇒ᴮ_; ⊥ᴮ )

Src : ℕ → Type ℓ
Src n = Formula (⊥* {ℓ}) n

eqᴬ memᴬ : S → S → Pt BG.B
eqᴬ = BG.Atomic._≈ᴮ_
memᴬ = BG.Atomic._∈ᴮ_

boolean-child-name : (n : S) → ⟨ BG.BK.IsName n ⟩
  → (x : S) → NG.K.Child x n → ⟨ BG.BK.IsName x ⟩
boolean-child-name n hn x ch = BooleanKernel.child-is-name n hn x
  (PT.map (λ { (b , h) → b , subst (λ e → ⟨ e ∈ˢ n ⟩)
    (sym (BG.entry-agrees x b)) h }) ch)

module Description = GroundDescription 𝒮 NG.extensional NG.≈ˢ-paths
  using ( separateOf; separateOf-spec )
module Pairs = K8.GroundSets.Ground 𝒮 NG.extensional NG.≈ˢ-paths
  NG.hasPair NG.hasUnion pow NG.hasSeparation κ
  using ( ordered; ordered-witness; ordered-components )
module Images = NameKernel.MemberImage images using ( image; image-spec )

mk : OrdinaryProfile.Separation 𝒮 → S → Formula S 1 → S
mk = Description.separateOf

mk-in : (s : OrdinaryProfile.Separation 𝒮) (b : S) (θ : Formula S 1) (a : S)
  → ⟨ a ∈ˢ b ⟩ → ⟨ (a ∷ []) GroundSat.⊨ θ ⟩ → ⟨ a ∈ˢ mk s b θ ⟩
mk-in s b θ a h q = subst ⟨_⟩ (sym (Description.separateOf-spec s b θ a)) (h , q)

mk-bound : (s : OrdinaryProfile.Separation 𝒮) (b : S) (θ : Formula S 1) (a : S)
  → ⟨ a ∈ˢ mk s b θ ⟩ → ⟨ a ∈ˢ b ⟩
mk-bound s b θ a h = fst (subst ⟨_⟩ (Description.separateOf-spec s b θ a) h)

mk-sat : (s : OrdinaryProfile.Separation 𝒮) (b : S) (θ : Formula S 1) (a : S)
  → ⟨ a ∈ˢ mk s b θ ⟩ → ⟨ (a ∷ []) GroundSat.⊨ θ ⟩
mk-sat s b θ a h = snd (subst ⟨_⟩ (Description.separateOf-spec s b θ a) h)

checkGraph : S → S
checkGraph β = Images.image β
  (λ ξ → Pairs.ordered (fst ξ) (fst (Checks.checked-name (fst ξ))))

checks : S → Formula S 2
checks β = ∃̇∈ (con (checkGraph β)) (prAtˢ zero (suc (suc zero)) (suc zero))

checks-reading : (β u ξ : S) → ⟨ ξ ∈ˢ β ⟩
  → ((u ∷ ξ ∷ []) GroundSat.⊨ checks β) ≡ (u ≈ˢ fst (Checks.checked-name ξ))
checks-reading β u ξ hξ = ⇔toPath forward backward
  where
  graph-spec : (z : S) → (z ∈ˢ checkGraph β)
    ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ β ⟩
      (λ _ → z ≈ˢ Pairs.ordered x (fst (Checks.checked-name x))))
  graph-spec = Images.image-spec β
    (λ x → Pairs.ordered (fst x) (fst (Checks.checked-name (fst x))))

  forward : ⟨ (u ∷ ξ ∷ []) GroundSat.⊨ checks β ⟩
    → ⟨ u ≈ˢ fst (Checks.checked-name ξ) ⟩
  forward = PT.rec (snd (u ≈ˢ fst (Checks.checked-name ξ)))
    λ { (z , hz , q) → PT.rec (snd (u ≈ˢ fst (Checks.checked-name ξ)))
      (λ { (x , hx) → PT.rec (snd (u ≈ˢ fst (Checks.checked-name ξ)))
        (λ { (_ , e) → conclude z x q e }) hx })
      (subst ⟨_⟩ (graph-spec z) hz) }
    where
    conclude : (z x : S) → ⟨ isKPairΔ z ξ u ⟩
      → ⟨ z ≈ˢ Pairs.ordered x (fst (Checks.checked-name x)) ⟩
      → ⟨ u ≈ˢ fst (Checks.checked-name ξ) ⟩
    conclude z x q e = subst ⟨_⟩
      (sym (NG.≈ˢ-paths u (fst (Checks.checked-name ξ))))
      (snd components ∙ cong (λ a → fst (Checks.checked-name a)) (sym (fst components)))
      where
      components : (ξ ≡ x) × (u ≡ fst (Checks.checked-name x))
      components = Pairs.ordered-components z ξ u x (fst (Checks.checked-name x)) q
        (subst (λ t → ⟨ isKPairΔ t x (fst (Checks.checked-name x)) ⟩)
          (sym (subst ⟨_⟩ (NG.≈ˢ-paths z (Pairs.ordered x (fst (Checks.checked-name x)))) e))
          (Pairs.ordered-witness x (fst (Checks.checked-name x))))

  backward : ⟨ u ≈ˢ fst (Checks.checked-name ξ) ⟩
    → ⟨ (u ∷ ξ ∷ []) GroundSat.⊨ checks β ⟩
  backward e = ∣ z , member , pair ∣₁
    where
    z : S
    z = Pairs.ordered ξ (fst (Checks.checked-name ξ))
    member : ⟨ z ∈ˢ checkGraph β ⟩
    member = subst ⟨_⟩ (sym (graph-spec z))
      ∣ ξ , ∣ hξ , subst ⟨_⟩ (sym (NG.≈ˢ-paths z z)) refl ∣₁ ∣₁
    pair : ⟨ isKPairΔ z ξ u ⟩
    pair = subst (λ t → ⟨ isKPairΔ z ξ t ⟩)
      (sym (subst ⟨_⟩ (NG.≈ˢ-paths u (fst (Checks.checked-name ξ))) e))
      (Pairs.ordered-witness ξ (fst (Checks.checked-name ξ)))

module AtGeneric (G : NG.PS.P.Sub) where

  extension : ZFStructure (hPropAlgebra ℓ)
  extension = NG.PS.𝒮ᴾ[ G ]

  module ExtensionCardinal = CardinalBridge extension using ( IsOrdinalφ; isCardinal )
  module ExtensionSemantics = FOL.Semantics (hPropAlgebra ℓ) extension using ( module At )
  module ExtensionSat = ExtensionSemantics.At NG.K.Name id using ( _⊨_ )
  module E = K9.NameGround.AtGeneric.E 𝒮 families accessible images pow κ w G
    using ( _≈[G]_; _∈[G]_ )

  positive : Ω
  positive = ⋁ Checks.Frame.Cond G

  module AtPositive (pos : ⟨ positive ⟩) where

    module Copy = K9.NameGround.AtGeneric.Copy.WithPos
      𝒮 families accessible images pow κ w G pos
      using ( check-faithful; check-value; groundSat )

    checked-membership : (a b : S) → ⟨ a ∈ˢ b ⟩
      → ⟨ fst (Checks.checked-name a) E.∈[G] fst (Checks.checked-name b) ⟩
    checked-membership a b = subst ⟨_⟩ (sym (Copy.check-faithful a b))

    checked-members : (a : S) (τ : NG.K.Name)
      → ⟨ fst τ E.∈[G] fst (Checks.checked-name a) ⟩
      → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ E.≈[G] fst (Checks.checked-name y))) ⟩
    checked-members a τ = subst ⟨_⟩ (Copy.check-value a (fst τ))

    checked-ordinal : (a : S)
      → ((Checks.checked-name a ∷ []) ExtensionSat.⊨ ExtensionCardinal.IsOrdinalφ)
        ≡ ((a ∷ []) GroundSat.⊨ GroundCardinal.IsOrdinalφ)
    checked-ordinal a = Copy.groundSat GroundCardinal.IsOrdinalφ
      Ordinals.Δ₀-IsOrdinalφ (a ∷ [])

  reflected-checked-equality : (r : Checks.Frame.Cond) (a b : S)
    → ⟨ Checks.Forcing._⊩ᴮ_ r
      (BG.Atomic._≈ᴮ_ (BG.Translation.trᴮ (fst (Checks.checked-name a)))
        (BG.Translation.trᴮ (fst (Checks.checked-name b)))) ⟩
    → ⟨ a ≈ˢ b ⟩
  reflected-checked-equality = Checks.checked-name-reflection

  module TA = K6.TruthSeam.Kernel.At
    𝒮 NG.extensional NG.≈ˢ-paths NG.hasSeparation NG.C.carrier NG.C.order
    BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
    (BG.Base.codedBase lem) BG.BK.IsName
    NG.K.entry NG.K.Child NG.K.isPropChild (λ x b n h → ∣ b , h ∣₁)
    NG.K.child-wf NG.GS.empty NG.empty-spec boolean-child-name G
    using ( _∈ᵁ_; _≈ᵁ_ )
  module EA = K5.ExtensionSat.Transfer.At
    𝒮 NG.K.entry NG.K.Child NG.K.isPropChild (λ x b n h → ∣ b , h ∣₁)
    NG.K.child-wf NG.GS.empty NG.empty-spec
    NG.C.carrier Order._≼_ Order.≼-refl
    (λ {p} {q} {r} → Order.≼-trans {p} {q} {r}) Order.nonempty
    NG.K.IsName NG.K.child-is-name BG.B BG.IC.codedLattice BG.BK.IsName boolean-child-name
    G (TSM.TAF.GI.Uof G) using ( _≈[G]_; _∈[G]_; _≈[U]_; _∈[U]_ )
  module D = K6.Definability 𝒮 NG.extensional NG.≈ˢ-paths NG.C.carrier NG.C.order
    BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
    (BG.Base.codedBase lem) extension using ( srcOf )
  module Engine
    (fil : TSM.TAF.GI.FS.isFilter G)
    (meets : TSM.TAF.C.MeetsAll G)
    (val : ∀ {k} → Src k → Vec TSM.Nameᴮ k → Pt BG.B)
    (law-∈ : ∀ {k} (a b : Fin k) (ν : Vec TSM.Nameᴮ k)
           → val (var a ∈̇ var b) ν ≡ memᴬ (fst (lookup a ν)) (fst (lookup b ν)))
    (law-≐ : ∀ {k} (a b : Fin k) (ν : Vec TSM.Nameᴮ k)
           → val (var a ≐ var b) ν ≡ eqᴬ (fst (lookup a ν)) (fst (lookup b ν)))
    (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Vec TSM.Nameᴮ k)
           → val (φ ∧̇ ψ) ν ≡ (val φ ν ⊓ᴮ val ψ ν))
    (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Vec TSM.Nameᴮ k)
           → val (φ ∨̇ ψ) ν ≡ (val φ ν ⊔ᴮ val ψ ν))
    (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Vec TSM.Nameᴮ k)
           → val (φ ⇒̇ ψ) ν ≡ (val φ ν ⇒ᴮ val ψ ν))
    (law-⊥ : ∀ {k} (ν : Vec TSM.Nameᴮ k) → val {k} ⊥̇ ν ≡ ⊥ᴮ)
    (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (σ : TSM.Nameᴮ)
                → ⟨ val φ (σ ∷ ν) ≤ᴮ val (∃̇ φ) ν ⟩)
    (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (c : Pt BG.B)
                → ((σ : TSM.Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
                → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
    (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (σ : TSM.Nameᴮ)
                → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
    (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (c : Pt BG.B)
                → ((σ : TSM.Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
                → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
    (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                  (σ : TSM.Nameᴮ)
                → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                    ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
    (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                  (c : Pt BG.B)
                → ((σ : TSM.Nameᴮ)
                   → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν)) ≤ᴮ c ⟩)
                → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
    (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                  (σ : TSM.Nameᴮ)
                → ⟨ val (∀̇∈ (var j) φ) ν
                    ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
    (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                  (c : Pt BG.B)
                → ((σ : TSM.Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                            ⇒ᴮ val φ (σ ∷ ν)) ⟩)
                → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
    (atom-∈ : (σ τ : TSM.Nameᴮ) → TA._∈ᵁ_ σ τ ≡ TSM.TAF.GI.Uof G (memᴬ (fst σ) (fst τ)))
    (atom-≐ : (σ τ : TSM.Nameᴮ) → TA._≈ᵁ_ σ τ ≡ TSM.TAF.GI.Uof G (eqᴬ (fst σ) (fst τ)))
    where

    module TC = K6.TruthSeam.Kernel.At.Conditional
      𝒮 NG.extensional NG.≈ˢ-paths NG.hasSeparation NG.C.carrier NG.C.order
      BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
      (BG.Base.codedBase lem) BG.BK.IsName
      NG.K.entry NG.K.Child NG.K.isPropChild (λ x b n h → ∣ b , h ∣₁)
      NG.K.child-wf NG.GS.empty NG.empty-spec boolean-child-name G
      fil meets Dense.codeOfBelow Dense.belowOfCode
                  eqᴬ memᴬ val
                  law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
                  law-∃-ub law-∃-lub law-∀-lb law-∀-glb
                  law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb
                  atom-∈ atom-≐
      using ( Supply )


    Supply : ∀ {k} → Src k → Type (ℓ-suc ℓ)
    Supply = TC.Supply

    module AGR = K10.CohenAgreementSeam.FromGeneric 𝒮 families accessible images pow κ w lem G fil meets
      using ( ≈-agree ; ∈-agree ; ext-surjective )

    module Conditional
      (supply : ∀ {k} (φ : Formula NG.K.Name k) → Supply (D.srcOf φ))
      where

      module Actual = K6.ForcesTruth.Kernel.At.Engine.Conditional
        𝒮 NG.extensional NG.≈ˢ-paths NG.hasSeparation NG.C.carrier NG.C.order
        BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
        (BG.Base.codedBase lem) NG.K.IsName BG.BK.IsName
        NG.K.entry NG.K.Child NG.K.isPropChild (λ x b n h → ∣ b , h ∣₁)
        NG.K.child-wf NG.GS.empty NG.empty-spec
        Order._≼_ Order.≼-refl (λ {p} {q} {r} → Order.≼-trans {p} {q} {r})
        Order.nonempty NG.K.child-is-name boolean-child-name
        G fil meets Dense.codeOfBelow Dense.belowOfCode eqᴬ memᴬ val
        law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
        law-∃-ub law-∃-lub law-∀-lb law-∀-glb
        law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb atom-∈ atom-≐
        BG.Translation.trᴮ BG.Translation.trᴮ-name
        AGR.≈-agree AGR.∈-agree AGR.ext-surjective supply lem
        using ( forces )

      module Definable
        (forcesΔ : ∀ {k} → Formula NG.K.Name k → Formula S (suc k))
        (forcesΔ-reading : ∀ {k} (φ : Formula NG.K.Name k) (ν : Vec NG.K.Name k)
          (r : Checks.Frame.Cond)
          → ((fst r ∷ Names.codesOf ν) GroundSat.⊨ forcesΔ φ) ≡ Actual.forces r φ ν)
        where

        module AtBound (μ : S)
          (find : OrdinaryProfile.FoundationInduction 𝒮)
          (choice : OrdinaryProfile.ChoiceSet 𝒮)
          where

          module Preservation = K7.PreservationAtTruth.Kernel.At.Engine.Conditional.AtCheck.AtBound.GroundProfile.WithDefinedFamilies
            𝒮 NG.extensional NG.≈ˢ-paths NG.hasSeparation NG.C.carrier NG.C.order
            BG.B BG.IC.codedLattice BG.IC.codedComplement BG.IC.codedComplete
            (BG.Base.codedBase lem) NG.K.IsName BG.BK.IsName
            NG.K.entry NG.K.Child NG.K.isPropChild (λ x b n h → ∣ b , h ∣₁)
            NG.K.child-wf NG.GS.empty NG.empty-spec
            Order._≼_ Order.≼-refl (λ {p} {q} {r} → Order.≼-trans {p} {q} {r})
            Order.nonempty NG.K.child-is-name boolean-child-name
            G fil meets Dense.codeOfBelow Dense.belowOfCode eqᴬ memᴬ val
            law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
            law-∃-ub law-∃-lub law-∀-lb law-∀-glb
            law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb atom-∈ atom-≐
            BG.Translation.trᴮ BG.Translation.trᴮ-name
            AGR.≈-agree AGR.∈-agree AGR.ext-surjective supply lem
            Checks.checked-name forcesΔ forcesΔ-reading mk mk-in mk-bound mk-sat
            μ (checks μ) (checks-reading μ) reflected-checked-equality
            (λ pos → AtPositive.checked-membership pos)
            (λ pos → AtPositive.checked-members pos)
            (AtPositive.checked-ordinal (TSM.TAF.GI.FS.isFilter.inhabited fil))
            NG.hasPair NG.hasUnion pow NG.hasCollect find κ choice checks checks-reading
            using ( module AtCountableCardinal; module AtLargerCardinal )

          module AtCountableCardinal
            (ω : S) (hω : ⟨ GroundCardinal.isOmega ω ⟩)
            (hμ : ⟨ GroundCardinal.isCardinal μ ⟩) (hωμ : ⟨ ω ∈ˢ μ ⟩)
            (members-countable : (β : S) → ⟨ β ∈ˢ μ ⟩
              → ⟨ GroundCardinal.injectable β ω ⟩)
            (pairE : OrdinaryProfile.Pairing extension)
            (sepE : OrdinaryProfile.Separation extension)
            (collE : OrdinaryProfile.Collection extension)
            where

            module Result = Preservation.AtCountableCardinal ω hω hμ hωμ
              members-countable pairE sepE collE using ( preserved-cardinal )

            preserved-cardinal : ⟨ Chain.CCC₂ᴵ NG.C.carrier NG.C.order ω ⟩
              → ⟨ ExtensionCardinal.isCardinal (Checks.checked-name μ) ⟩
            preserved-cardinal = Result.preserved-cardinal

          module AtOmega (hw : ⟨ GroundCardinal.isOmega w ⟩) where

            private
              module CCC = K8.CohenCCC.AtOmega
                𝒮 NG.extensional NG.≈ˢ-paths NG.hasPair NG.hasUnion pow
                NG.hasSeparation NG.hasCollect find κ w lem choice hw using ( ccc )

            cohen-ccc : ⟨ Chain.CCC₂ᴵ NG.C.carrier NG.C.order w ⟩
            cohen-ccc = CCC.ccc

            module AtCountableBound
              (hμ : ⟨ GroundCardinal.isCardinal μ ⟩) (hwμ : ⟨ w ∈ˢ μ ⟩)
              (members-countable : (β : S) → ⟨ β ∈ˢ μ ⟩
                → ⟨ GroundCardinal.injectable β w ⟩)
              (pairE : OrdinaryProfile.Pairing extension)
              (sepE : OrdinaryProfile.Separation extension)
              (collE : OrdinaryProfile.Collection extension)
              where

              private
                module Result = Preservation.AtCountableCardinal w hw hμ hwμ
                  members-countable pairE sepE collE using ( preserved-cardinal )

              preserved-cardinal : ⟨ ExtensionCardinal.isCardinal (Checks.checked-name μ) ⟩
              preserved-cardinal = Result.preserved-cardinal cohen-ccc

            module AtLargerBound
              (d : S) (hμ : ⟨ GroundCardinal.isCardinal μ ⟩)
              (hdμ : ⟨ d ∈ˢ μ ⟩) (wd : ⟨ GroundCardinal.injectable w d ⟩)
              (below : (β : S) → ⟨ β ∈ˢ μ ⟩ → ⟨ GroundCardinal.injectable β d ⟩)
              (pairE : OrdinaryProfile.Pairing extension)
              (sepE : OrdinaryProfile.Separation extension)
              (collE : OrdinaryProfile.Collection extension)
              where

              private
                module Result = Preservation.AtLargerCardinal w d hμ hdμ wd below
                  pairE sepE collE using ( preserved-cardinal; module Result )

              squareBound : Ω
              squareBound = Result.Result.squareBound

              preserved-cardinal : ⟨ squareBound ⟩
                → ⟨ ExtensionCardinal.isCardinal (Checks.checked-name μ) ⟩
              preserved-cardinal square = Result.preserved-cardinal square cohen-ccc

            module AtSuccessorCardinal
              (d : S) (hd : ⟨ GroundCardinal.isCardinal d ⟩) (hwd : ⟨ w ∈ˢ d ⟩)
              (members-countable : (a : S) → ⟨ a ∈ˢ d ⟩
                → ⟨ GroundCardinal.injectable a w ⟩)
              (hμ : ⟨ GroundCardinal.isCardinal μ ⟩) (hdμ : ⟨ d ∈ˢ μ ⟩)
              (below : (β : S) → ⟨ β ∈ˢ μ ⟩ → ⟨ GroundCardinal.injectable β d ⟩)
              (pairE : OrdinaryProfile.Pairing extension)
              (sepE : OrdinaryProfile.Separation extension)
              (collE : OrdinaryProfile.Collection extension)
              where

              private
                module Successor = K7.CountableOrdinalSuccessor.AtOmega
                  𝒮 NG.extensional NG.≈ˢ-paths NG.hasPair NG.hasUnion pow
                  NG.hasSeparation NG.hasCollect find w lem choice w hw
                  using ( successor-closed )
                module Square = K7.OrdinalSquare
                  𝒮 NG.extensional NG.≈ˢ-paths NG.hasPair NG.hasUnion pow
                  NG.hasSeparation NG.hasCollect find w lem w hw d hd hwd
                  (Successor.successor-closed d hd hwd members-countable)
                  members-countable using ( square-bound )
                module Inclusion = K7.CardinalOrder.Order 𝒮 NG.extensional
                  (λ x y z e → cong (λ t → t ∈ˢ z) (subst ⟨_⟩ (NG.≈ˢ-paths x y) e))
                  (λ x y z e → cong (x ∈ˢ_) (subst ⟨_⟩ (NG.≈ˢ-paths y z) e))
                  using ( injectable-incl )

                countable-in-d : ⟨ GroundCardinal.injectable w d ⟩
                countable-in-d = Inclusion.injectable-incl
                  NG.hasSeparation NG.hasCollect NG.hasPair w d (hd .fst .fst w hwd)

                module Result = AtLargerBound d hμ hdμ countable-in-d below pairE sepE collE
                  using ( squareBound; preserved-cardinal )

              square-bound : ⟨ Result.squareBound ⟩
              square-bound = Square.square-bound

              preserved-cardinal : ⟨ ExtensionCardinal.isCardinal (Checks.checked-name μ) ⟩
              preserved-cardinal = Result.preserved-cardinal square-bound

          module AtLargerCardinal
            (ω d : S) (hμ : ⟨ GroundCardinal.isCardinal μ ⟩)
            (hdμ : ⟨ d ∈ˢ μ ⟩) (ωd : ⟨ GroundCardinal.injectable ω d ⟩)
            (below : (β : S) → ⟨ β ∈ˢ μ ⟩ → ⟨ GroundCardinal.injectable β d ⟩)
            (pairE : OrdinaryProfile.Pairing extension)
            (sepE : OrdinaryProfile.Separation extension)
            (collE : OrdinaryProfile.Collection extension)
            where

            module Result = Preservation.AtLargerCardinal ω d hμ hdμ ωd below
              pairE sepE collE using ( preserved-cardinal; module Result )

            squareBound : Ω
            squareBound = Result.Result.squareBound

            preserved-cardinal : ⟨ squareBound ⟩
              → ⟨ Chain.CCC₂ᴵ NG.C.carrier NG.C.order ω ⟩
              → ⟨ ExtensionCardinal.isCardinal (Checks.checked-name μ) ⟩
            preserved-cardinal = Result.preserved-cardinal
