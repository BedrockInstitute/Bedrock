{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )

open import FOL.Syntax using ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.HITs.PropositionalTruncation using ( ∥_∥₁ )
import OrdinaryProfile
import Valuation
import K4.Algebra
import K4.Implication
import K5.Frame
import K5.Structures
import K5.ExtensionSat
import K6.Definability
import K6.TruthSeam
import K7.ValuesAtTruth
import K7.PreserveAtTracks
import K7.FunctionalValuesAtNames
import K7.CardinalOrder
import K7.ChainConditions
import CodedVocabulary
import CardinalBridge
import FOL.Semantics

module K7.PreservationAtTruth
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep : OrdinaryProfile.Separation 𝒮)
  (carrier order : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  (IsNameᴾ IsNameᴮ : ZFStructure.S 𝒮 → hProp ℓ)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮 using ( Pt ; _≤ᴮ_ )
open K4.Implication 𝒮 ext paths B L Cm using ( _⊓ᴮ_ ; _⊔ᴮ_ ; _⇒ᴮ_ ; ⊥ᴮ )
open Valuation 𝒮 using ( Conditions )

module FP = K5.Frame.Poset 𝒮 carrier order using ( Cond )
module TSM = K6.TruthSeam 𝒮 ext paths sep carrier order B L Cm Kc fb IsNameᴮ
  using ( module Kernel; module TAF; Nameᴮ )
module GroundSemantics = FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
module GroundSat = GroundSemantics.At S id using ( _⊨_ )

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k



module Kernel
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (_≼ᶜ_        : Conditions carrier → Conditions carrier → Ω)
  (≼ᶜ-refl     : (p : Conditions carrier) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrier} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrier ∥₁)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  (child-nameᴮ : (n : S) → ⟨ IsNameᴮ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴮ x ⟩)
  where

  module TK = TSM.Kernel entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
                child-nameᴮ
    using ( module At )
  module KS = K5.Structures.Kernel 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
    using ( module PosetSide )
  module PS = KS.PosetSide carrier _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                IsNameᴾ child-nameᴾ
    using ( module P; 𝒮ᴾ[_]; ext[_] )
  module ES = K5.ExtensionSat.Transfer 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
                carrier _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ IsNameᴾ child-nameᴾ
                B L IsNameᴮ child-nameᴮ
    using ( module At )

  module At (G : PS.P.Sub) where

    module TA = TK.At G using ( module Conditional; _∈ᵁ_; _≈ᵁ_ )
    module EA = ES.At G (TSM.TAF.GI.Uof G)
      using ( _≈[G]_; _∈[G]_; _≈[U]_; _∈[U]_ )
    module D  = K6.Definability 𝒮 ext paths carrier order B L Cm Kc fb PS.𝒮ᴾ[ G ]
      using ( Nm; srcOf )


    Nameᴾ : Type ℓ
    Nameᴾ = D.Nm

    G∈ : FP.Cond → Ω
    G∈ p = TSM.TAF.GI.FS._∈ᴾ_ p G


    module Engine
      (fil : TSM.TAF.GI.FS.isFilter G)
      (meets : TSM.TAF.C.MeetsAll G)
      (cob : TSM.TAF.C.CodeOfBelow)
      (boc : TSM.TAF.C.BelowOfCode)
      (eqᴬ memᴬ : S → S → Pt B)
      (val : ∀ {k} → Src k → Vec TSM.Nameᴮ k → Pt B)
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
      (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (c : Pt B)
                  → ((σ : TSM.Nameᴮ) → ⟨ val φ (σ ∷ ν) ≤ᴮ c ⟩)
                  → ⟨ val (∃̇ φ) ν ≤ᴮ c ⟩)
      (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (σ : TSM.Nameᴮ)
                  → ⟨ val (∀̇ φ) ν ≤ᴮ val φ (σ ∷ ν) ⟩)
      (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k) (c : Pt B)
                  → ((σ : TSM.Nameᴮ) → ⟨ c ≤ᴮ val φ (σ ∷ ν) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇ φ) ν ⟩)
      (law-∃∈-ub  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (σ : TSM.Nameᴮ)
                  → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν))
                      ≤ᴮ val (∃̇∈ (var j) φ) ν ⟩)
      (law-∃∈-lub : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (c : Pt B)
                  → ((σ : TSM.Nameᴮ)
                     → ⟨ (memᴬ (fst σ) (fst (lookup j ν)) ⊓ᴮ val φ (σ ∷ ν)) ≤ᴮ c ⟩)
                  → ⟨ val (∃̇∈ (var j) φ) ν ≤ᴮ c ⟩)
      (law-∀∈-lb  : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (σ : TSM.Nameᴮ)
                  → ⟨ val (∀̇∈ (var j) φ) ν
                      ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν)) ⇒ᴮ val φ (σ ∷ ν)) ⟩)
      (law-∀∈-glb : ∀ {k} (j : Fin k) (φ : Src (suc k)) (ν : Vec TSM.Nameᴮ k)
                    (c : Pt B)
                  → ((σ : TSM.Nameᴮ) → ⟨ c ≤ᴮ (memᴬ (fst σ) (fst (lookup j ν))
                                              ⇒ᴮ val φ (σ ∷ ν)) ⟩)
                  → ⟨ c ≤ᴮ val (∀̇∈ (var j) φ) ν ⟩)
      (atom-∈ : (σ τ : TSM.Nameᴮ) → TA._∈ᵁ_ σ τ ≡ TSM.TAF.GI.Uof G (memᴬ (fst σ) (fst τ)))
      (atom-≐ : (σ τ : TSM.Nameᴮ) → TA._≈ᵁ_ σ τ ≡ TSM.TAF.GI.Uof G (eqᴬ (fst σ) (fst τ)))
      where

      module TC = TA.Conditional fil meets cob boc
                    eqᴬ memᴬ val
                    law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
                    law-∃-ub law-∃-lub law-∀-lb law-∀-glb
                    law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb
                    atom-∈ atom-≐
        using ( Supply )


      Supply : ∀ {k} → Src k → Type (ℓ-suc ℓ)
      Supply = TC.Supply


      module Conditional
        (trᴮ         : S → S)
        (trᴮ-name    : (n : S) → ⟨ IsNameᴾ n ⟩ → ⟨ IsNameᴮ (trᴮ n) ⟩)
        (≈-agree     : (m n : S) → EA._≈[G]_ m n ≡ EA._≈[U]_ (trᴮ m) (trᴮ n))
        (∈-agree     : (m n : S) → EA._∈[G]_ m n ≡ EA._∈[U]_ (trᴮ m) (trᴮ n))
        (ext-surjective : (n : S) → ⟨ IsNameᴮ n ⟩
                        → Σ[ τ ∈ (Σ[ m ∈ S ] ⟨ IsNameᴾ m ⟩) ]
                            ⟨ EA._≈[U]_ (trᴮ (fst τ)) n ⟩)
        (supply : ∀ {k} (φ : Formula Nameᴾ k) → Supply (D.srcOf φ))
        (lem : LEM ℓ)
        where

        module Producer = K7.ValuesAtTruth.Kernel.At.Engine.Conditional
          𝒮 ext paths sep carrier order B L Cm Kc fb IsNameᴾ IsNameᴮ
          entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
          _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ child-nameᴾ child-nameᴮ
          G fil meets cob boc eqᴬ memᴬ val
          law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
          law-∃-ub law-∃-lub law-∀-lb law-∀-glb
          law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb
          atom-∈ atom-≐ trᴮ trᴮ-name ≈-agree ∈-agree ext-surjective supply lem
          using ( module Actual; module AtCheck; module Values )
        module Actual = Producer.Actual using ( forces; truth-at; forces-mono )
        module Names = Producer.Values using ( codesOf )
        module Extension = PS.P.Ext G using ( sat-cong; ≈-refl; _⊨_ )
        module ExtensionCardinal = CardinalBridge PS.𝒮ᴾ[ G ]
          using ( isCardinal; IsOrdinalφ )
        module GroundCardinal = CardinalBridge 𝒮
          using ( injectable; isOmega; isCardinal; IsOrdinalφ )
        module Chain = K7.ChainConditions 𝒮 ext paths using ( CCC₂ᴵ )
        module GroundVocabulary = CodedVocabulary 𝒮 using ( refinesΔ )
        module GroundOrder = K7.CardinalOrder.Order 𝒮 ext
          (λ x y z e → cong (λ a → a ∈ˢ z) (subst ⟨_⟩ (paths x y) e))
          (λ x y z e → cong (x ∈ˢ_) (subst ⟨_⟩ (paths y z) e))
          using ( injectable-trans )

        mem-left : (x y z : Nameᴾ) → ⟨ fst x EA.≈[G] fst y ⟩
          → (fst x EA.∈[G] fst z) ≡ (fst y EA.∈[G] fst z)
        mem-left x y z e = Extension.sat-cong
          (var zero ∈̇ var (suc zero)) (x ∷ z ∷ []) (y ∷ z ∷ [])
          (λ { zero → e; (suc zero) → Extension.≈-refl (fst z) })

        mem-right : (x y z : Nameᴾ) → ⟨ fst y EA.≈[G] fst z ⟩
          → (fst x EA.∈[G] fst y) ≡ (fst x EA.∈[G] fst z)
        mem-right x y z e = Extension.sat-cong
          (var zero ∈̇ var (suc zero)) (x ∷ y ∷ []) (x ∷ z ∷ [])
          (λ { zero → Extension.≈-refl (fst x); (suc zero) → e })

        module ExtensionValues = K7.FunctionalValuesAtNames.AtLaws
          𝒮 paths IsNameᴾ EA._≈[G]_ EA._∈[G]_ PS.ext[ G ] mem-left mem-right
          using ( onto-at-names )

        module AtCheck (chk : S → Nameᴾ) where

          module Checked = Producer.AtCheck chk using ( checkedEq; function-values )
          positive : ⟨ ⋁ FP.Cond G∈ ⟩
          positive = TSM.TAF.GI.FS.isFilter.inhabited fil

          localOrder : FP.Cond → FP.Cond → Ω
          localOrder r p = GroundVocabulary.refinesΔ order (fst r) (fst p)

          directed : (p q : FP.Cond) → ⟨ G∈ p ⟩ → ⟨ G∈ q ⟩
            → ⟨ ⋁ FP.Cond (λ r → G∈ r ⊓ (localOrder r p ⊓ localOrder r q)) ⟩
          directed = TSM.TAF.GI.FS.isFilter.directed fil

          order-refl : (r : FP.Cond) → ⟨ localOrder r r ⟩
          order-refl r = TSM.TAF.FB.≼-refl (fst r) (snd r)

          order-trans : (r q p : FP.Cond)
            → ⟨ localOrder r q ⟩ → ⟨ localOrder q p ⟩ → ⟨ localOrder r p ⟩
          order-trans r q p = TSM.TAF.FB.≼-trans
            (fst r) (fst q) (fst p) (snd r) (snd q) (snd p)

          module AtBound
            (forcesΔ : ∀ {k} → Formula Nameᴾ k → Formula S (suc k))
            (forcesΔ-reading : ∀ {k} (φ : Formula Nameᴾ k) (ν : Vec Nameᴾ k) (r : FP.Cond)
              → ((fst r ∷ Names.codesOf ν) GroundSat.⊨ forcesΔ φ) ≡ Actual.forces r φ ν)
            (mk : OrdinaryProfile.Separation 𝒮 → S → Formula S 1 → S)
            (mk-in : (s : OrdinaryProfile.Separation 𝒮) (b : S) (θ : Formula S 1) (a : S)
              → ⟨ a ∈ˢ b ⟩ → ⟨ (a ∷ []) GroundSat.⊨ θ ⟩ → ⟨ a ∈ˢ mk s b θ ⟩)
            (mk-bound : (s : OrdinaryProfile.Separation 𝒮) (b : S) (θ : Formula S 1) (a : S)
              → ⟨ a ∈ˢ mk s b θ ⟩ → ⟨ a ∈ˢ b ⟩)
            (mk-sat : (s : OrdinaryProfile.Separation 𝒮) (b : S) (θ : Formula S 1) (a : S)
              → ⟨ a ∈ˢ mk s b θ ⟩ → ⟨ (a ∷ []) GroundSat.⊨ θ ⟩)
            (κ : S) (chkFo : Formula S 2)
            (chkFo-reading : (u a : S) → ⟨ a ∈ˢ κ ⟩
              → ((u ∷ a ∷ []) GroundSat.⊨ chkFo) ≡ (u ≈ˢ fst (chk a)))
            (checked-reflect : (r : FP.Cond) (a b : S)
              → ⟨ Checked.checkedEq r a b ⟩ → ⟨ a ≈ˢ b ⟩)
            (chk-mem← : ⟨ ⋁ FP.Cond G∈ ⟩ → (a b : S) → ⟨ a ∈ˢ b ⟩
              → ⟨ fst (chk a) EA.∈[G] fst (chk b) ⟩)
            (copy-members : ⟨ ⋁ FP.Cond G∈ ⟩ → (a : S) (τ : Nameᴾ)
              → ⟨ fst τ EA.∈[G] fst (chk a) ⟩
              → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ (fst τ EA.≈[G] fst (chk y))) ⟩)
            (chk-ordinal : (a : S)
              → ((chk a ∷ []) Extension.⊨ ExtensionCardinal.IsOrdinalφ)
                ≡ ((a ∷ []) GroundSat.⊨ GroundCardinal.IsOrdinalφ))
            where

            module GroundProfile
              (pair : OrdinaryProfile.Pairing 𝒮)
              (un : OrdinaryProfile.Union 𝒮)
              (pow : OrdinaryProfile.PowerSet 𝒮)
              (coll : OrdinaryProfile.Collection 𝒮)
              (find : OrdinaryProfile.FoundationInduction 𝒮)
              (seed : S) (choice : OrdinaryProfile.ChoiceSet 𝒮)
              where

              module Antichains = K7.PreserveAtTracks.Names.AtG.AtNotion.Probe.WithAntichains
                𝒮 ext paths IsNameᴾ EA._≈[G]_ EA._∈[G]_
                carrier FP.Cond fst (λ r → snd r) (λ q hq → q , hq)
                (λ q hq → refl) G∈ chk order
                (λ s c → GroundOrder.injectable-trans s c pair)
                Actual.forces Actual.truth-at
                (λ r p hrp φ ν → Actual.forces-mono p r φ ν hrp)
                directed forcesΔ forcesΔ-reading mk mk-in mk-bound mk-sat
                κ chkFo chkFo-reading Extension.sat-cong Extension.≈-refl
                chk-mem← copy-members chk-ordinal ExtensionValues.onto-at-names
                Checked.checkedEq Checked.function-values checked-reflect
                order-refl order-trans
                pair un pow coll find seed lem choice
                using ( module WithDefinedFamilies )

              module WithDefinedFamilies
                (checks : S → Formula S 2)
                (checks-reading : (β u ξ : S) → ⟨ ξ ∈ˢ β ⟩
                  → ((u ∷ ξ ∷ []) GroundSat.⊨ checks β) ≡ (u ≈ˢ fst (chk ξ)))
                where

                module Family = Antichains.WithDefinedFamilies checks checks-reading
                  using ( module AtCountableCardinal; module AtLargerCardinal )

                module AtCountableCardinal
                  (w : S) (hw : ⟨ GroundCardinal.isOmega w ⟩)
                  (hκ : ⟨ GroundCardinal.isCardinal κ ⟩) (hwκ : ⟨ w ∈ˢ κ ⟩)
                  (members-countable : (β : S) → ⟨ β ∈ˢ κ ⟩
                    → ⟨ GroundCardinal.injectable β w ⟩)
                  (pairE : OrdinaryProfile.Pairing PS.𝒮ᴾ[ G ])
                  (sepE : OrdinaryProfile.Separation PS.𝒮ᴾ[ G ])
                  (collE : OrdinaryProfile.Collection PS.𝒮ᴾ[ G ])
                  where

                  module Result = Family.AtCountableCardinal sep w hw hκ hwκ
                    members-countable PS.ext[ G ] pairE sepE collE
                    (chk w) (chk-mem← positive w κ hwκ)
                    using ( preserved-cardinal )

                  preserved-cardinal : ⟨ Chain.CCC₂ᴵ carrier order w ⟩
                    → ⟨ ExtensionCardinal.isCardinal (chk κ) ⟩
                  preserved-cardinal = Result.preserved-cardinal positive

                module AtLargerCardinal
                  (w d : S) (hκ : ⟨ GroundCardinal.isCardinal κ ⟩)
                  (hdκ : ⟨ d ∈ˢ κ ⟩) (wd : ⟨ GroundCardinal.injectable w d ⟩)
                  (below : (β : S) → ⟨ β ∈ˢ κ ⟩ → ⟨ GroundCardinal.injectable β d ⟩)
                  (pairE : OrdinaryProfile.Pairing PS.𝒮ᴾ[ G ])
                  (sepE : OrdinaryProfile.Separation PS.𝒮ᴾ[ G ])
                  (collE : OrdinaryProfile.Collection PS.𝒮ᴾ[ G ])
                  where

                  module Result = Family.AtLargerCardinal sep w d hκ hdκ wd below
                    PS.ext[ G ] pairE sepE collE
                    (chk d) (chk-mem← positive d κ hdκ)
                    using ( preserved-cardinal; squareBound )

                  preserved-cardinal :
                    ⟨ Result.squareBound ⟩
                    → ⟨ Chain.CCC₂ᴵ carrier order w ⟩
                    → ⟨ ExtensionCardinal.isCardinal (chk κ) ⟩
                  preserved-cardinal square = Result.preserved-cardinal square positive
