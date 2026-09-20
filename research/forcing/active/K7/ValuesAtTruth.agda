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
import K6.ForcesTruth
import K7.ForcedFunctionValuesAtClauses
import K7.ValueAbstraction
import K7.PossibleValues
import CardinalBridge

module K7.ValuesAtTruth
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

module FP = K5.Frame.Poset 𝒮 carrier order
module TSM = K6.TruthSeam 𝒮 ext paths sep carrier order B L Cm Kc fb IsNameᴮ

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
  module KS = K5.Structures.Kernel 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
  module PS = KS.PosetSide carrier _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                IsNameᴾ child-nameᴾ
  module ES = K5.ExtensionSat.Transfer 𝒮
                entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
                carrier _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ IsNameᴾ child-nameᴾ
                B L IsNameᴮ child-nameᴮ

  module At (G : PS.P.Sub) where

    module TA = TK.At G
    module EA = ES.At G (TSM.TAF.GI.Uof G)
    module D  = K6.Definability 𝒮 ext paths carrier order B L Cm Kc fb PS.𝒮ᴾ[ G ]


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

        module ESat = EA.Sat trᴮ trᴮ-name ≈-agree ∈-agree ext-surjective
          using ( ext-map )

        module Actual = K6.ForcesTruth.Kernel.At.Engine.Conditional
          𝒮 ext paths sep carrier order B L Cm Kc fb IsNameᴾ IsNameᴮ
          entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
          _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ child-nameᴾ child-nameᴮ
          G fil meets cob boc eqᴬ memᴬ val
          law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
          law-∃-ub law-∃-lub law-∀-lb law-∀-glb
          law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb
          atom-∈ atom-≐ trᴮ trᴮ-name ≈-agree ∈-agree ext-surjective supply lem
          using ( forces; truth-at; forces-mono )

        module Values = K7.PossibleValues.Names 𝒮 paths IsNameᴾ
        module Cardinal = CardinalBridge PS.𝒮ᴾ[ G ]
        module Abstraction = K7.ValueAbstraction 𝒮
        module Source = Abstraction.Names paths IsNameᴾ

        module Primitive = K7.ForcedFunctionValuesAtClauses
          𝒮 ext paths B L Cm carrier FP._≼ᶜ_ IsNameᴮ
        module Proof = Primitive.Core
          TSM.TAF.FB.i TSM.TAF.FF._⊩ᴮ_ TSM.TAF.FF.⊩ᴮ-spec
          TSM.TAF.FB.≼-refl TSM.TAF.FB.≼-trans
          TSM.TAF.FF.⊩ᴮ-mono TSM.TAF.FF.⊩ᴮ-down TSM.TAF.FF.⊩ᴮ-reg
          TSM.TAF.FF.⊩ᴮ-⊥ TSM.TAF.FF.⊩ᴮ-extend
          eqᴬ memᴬ val
          law-∈ law-≐ law-∧ law-∨ law-⇒ law-⊥
          law-∃-ub law-∃-lub law-∀-lb law-∀-glb
          law-∃∈-ub law-∃∈-lub law-∀∈-lb law-∀∈-glb
          using ( module Actual )
        module Result = Proof.Actual lem using ( forced-function-values; functionFo; valueFo )
        open TSM.TAF.FF using ( _⊩ᴮ_ )

        -- These seams compare actual parameter abstraction with the source
        -- formulas proved from K5's clauses. The value has exactly one
        -- constant occurrence, so its last environment entry is the graph.
        value-source : (f : Nameᴾ) → D.srcOf (Values.valueFo f) ≡ Result.valueFo
        value-source = Source.value-source

        function-source : D.srcOf Cardinal.IsFunctionφ ≡ Result.functionFo
        function-source = refl

        -- The condition is arbitrary. Translation maps only the names;
        -- no membership in the chosen generic is used to prove equality.
        forced-function-values : (p : FP.Cond) (f x y z : Nameᴾ)
          → ⟨ Actual.forces p Cardinal.IsFunctionφ (f ∷ []) ⟩
          → ⟨ Actual.forces p (Values.valueFo f) (x ∷ y ∷ []) ⟩
          → ⟨ Actual.forces p (Values.valueFo f) (x ∷ z ∷ []) ⟩
          → ⟨ p ⊩ᴮ eqᴬ (trᴮ (fst y)) (trᴮ (fst z)) ⟩
        forced-function-values p f x y z =
          Result.forced-function-values p
            (ESat.ext-map f) (ESat.ext-map x) (ESat.ext-map y) (ESat.ext-map z)

        module AtCheck (chk : S → Nameᴾ) where

          checkedEq : FP.Cond → S → S → Ω
          checkedEq r a b = r ⊩ᴮ eqᴬ (trᴮ (fst (chk a))) (trᴮ (fst (chk b)))

          function-values : (r : FP.Cond) (f : Nameᴾ) (ξ a b : S)
            → ⟨ Actual.forces r Cardinal.IsFunctionφ (f ∷ []) ⟩
            → ⟨ Actual.forces r (Values.valueFo f) (chk ξ ∷ chk a ∷ []) ⟩
            → ⟨ Actual.forces r (Values.valueFo f) (chk ξ ∷ chk b ∷ []) ⟩
            → ⟨ checkedEq r a b ⟩
          function-values r f ξ a b = forced-function-values r f (chk ξ) (chk a) (chk b)
