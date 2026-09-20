{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import NameKernel
import OrdinaryProfile

module K9.GraphInjection
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (families : NameKernel.Families 𝒮)
  (accessible : NameKernel.Accessibility 𝒮)
  (images : NameKernel.MemberImage 𝒮)
  (pow : OrdinaryProfile.PowerSet 𝒮)
  (κ w : ZFStructure.S 𝒮)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁ )
import CardinalBridge
import K7.CardinalOrder
import K9.NameGround
import K9.IndexedNames
import K9.PairNames
import K9.RealNames
import K9.GraphNames

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
module Ground = K9.NameGround 𝒮 families accessible images pow κ w
  using ( module GS; module K; module P; module PS; module AtGeneric )
module Indexed = K9.IndexedNames 𝒮 families accessible images pow κ w
  using ( module AtGeneric )
module Pair = K9.PairNames 𝒮 families accessible images pow κ w
  using ( pairNm; module AtGeneric )
module Real = K9.RealNames 𝒮 families accessible images pow κ w using ( real )
module Graph = K9.GraphNames 𝒮 families accessible images pow κ w
  using ( checkNm; vertex; graph; graphCode )
private module K = Ground.K

module Injection
  (G : Ground.P.Sub)
  (positive : ⟨ Ground.P.positive G ⟩)
  (fil : Ground.P.isFilter G)
  where

  module A = Ground.AtGeneric G using ( module E; module Copy )
  module E = A.E using
    ( _≈[G]_; _∈[G]_; ≈-refl; ≈-sym; ≈-trans; ∈-congˡ; ∈-congʳ )
  module Copy = A.Copy.WithPos positive using
    ( check-value; check-≈-inj; check-faithful; chk-≈ )
  module Values = Indexed.AtGeneric G positive using ( indexed-value )
  module Pairs = Pair.AtGeneric G using ( pair-value; isKPair )
  module CB = CardinalBridge Ground.PS.𝒮ᴾ[ G ] using
    ( isSingleton; isPair; isKPair; isRelation; isInjection; isSubset; isPowerSet )
  private
    module CO = K7.CardinalOrder Ground.PS.𝒮ᴾ[ G ] using ( module Order )
    module Order = CO.Order (Ground.PS.P.Ext.extensional G)
      (λ σ τ ρ e → ⇔toPath (E.∈-congˡ e) (E.∈-congˡ (E.≈-sym e)))
      (λ σ τ ρ e → ⇔toPath (E.∈-congʳ e) (E.∈-congʳ (E.≈-sym e)))
      using ( kpair-components; kpair-subst )

  graph-value : (χ : S) → (χ E.∈[G] Graph.graphCode)
    ≡ ⋁ S (λ α → (α ∈ˢ κ) ⊓ (χ E.≈[G] fst (Graph.vertex α)))
  graph-value = Values.indexed-value κ (λ α → fst (Graph.vertex α))

  private
    kpair-cong : (q p x y : K.Name) → ⟨ fst q E.≈[G] fst p ⟩
               → ⟨ CB.isKPair p x y ⟩ → ⟨ CB.isKPair q x y ⟩
    kpair-cong q p x y eq hp t =
        (λ ht → hp t .fst (E.∈-congʳ eq ht))
      , (λ shape → E.∈-congʳ (E.≈-sym eq) (hp t .snd shape))

    extensionPairing : OrdinaryProfile.Pairing Ground.PS.𝒮ᴾ[ G ]
    extensionPairing σ τ = ∣ Pair.pairNm σ τ , (λ ρ →
        subst ⟨_⟩ (Pairs.pair-value fil (fst σ) (fst τ) (fst ρ))
      , subst ⟨_⟩ (sym (Pairs.pair-value fil (fst σ) (fst τ) (fst ρ)))) ∣₁

    canonical-pair : (α : S)
                   → ⟨ CB.isKPair (Graph.vertex α) (Graph.checkNm α) (Real.real α) ⟩
    canonical-pair α = Pairs.isKPair fil (Graph.checkNm α) (Real.real α)

    graph-in : (α : S) → ⟨ α ∈ˢ κ ⟩
             → ⟨ fst (Graph.vertex α) E.∈[G] Graph.graphCode ⟩
    graph-in α hα = subst ⟨_⟩ (sym (graph-value (fst (Graph.vertex α))))
      ∣ α , hα , E.≈-refl (fst (Graph.vertex α)) ∣₁

    Components : K.Name → K.Name → K.Name → S → Type ℓ
    Components p x y α =
      ⟨ (fst x E.≈[G] fst (Graph.checkNm α)) ⊓
        (fst y E.≈[G] fst (Real.real α)) ⟩

    components : (p x y : K.Name) (α : S)
               → ⟨ fst p E.≈[G] fst (Graph.vertex α) ⟩ → ⟨ CB.isKPair p x y ⟩
               → Components p x y α
    components p x y α pα hp =
      Order.kpair-components extensionPairing p x y (Graph.checkNm α) (Real.real α)
        hp (kpair-cong p (Graph.vertex α) (Graph.checkNm α) (Real.real α) pα
          (canonical-pair α))

    ground-eq→real-eq : (α β : S) → ⟨ α ≈ˢ β ⟩
                      → ⟨ fst (Real.real α) E.≈[G] fst (Real.real β) ⟩
    ground-eq→real-eq α β eq = subst
      (λ δ → ⟨ fst (Real.real α) E.≈[G] fst (Real.real δ) ⟩)
      (Ground.GS.≈→≡ eq) (E.≈-refl (fst (Real.real α)))

    relation : ⟨ CB.isRelation Graph.graph ⟩
    relation p hp = PT.rec (snd (⋁ K.Name (λ x → ⋁ K.Name (λ y → CB.isKPair p x y))))
      (λ { (α , hα , pα) → ∣ Graph.checkNm α , ∣ Real.real α ,
        kpair-cong p (Graph.vertex α) (Graph.checkNm α) (Real.real α) pα
          (canonical-pair α) ∣₁ ∣₁ })
      (subst ⟨_⟩ (graph-value (fst p)) hp)

  graph-domain : (p x y : K.Name) → ⟨ fst p E.∈[G] Graph.graphCode ⟩
               → ⟨ CB.isKPair p x y ⟩
               → ⟨ fst x E.∈[G] fst (Graph.checkNm κ) ⟩
  graph-domain p x y hp hxy = PT.rec (snd (fst x E.∈[G] fst (Graph.checkNm κ)))
    (λ { (α , hα , pα) → E.∈-congˡ
      (E.≈-sym (fst (components p x y α pα hxy)))
      (subst ⟨_⟩ (sym (Copy.check-faithful α κ)) hα) })
    (subst ⟨_⟩ (graph-value (fst p)) hp)

  isInjection :
    (lem : LEM ℓ)
    (real-subset : (α : S) → ⟨ CB.isSubset (Real.real α) (Graph.checkNm w) ⟩)
    (real-distinct : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
      → ⟨ (α ≈ˢ β) ⇒ ⊥ ⟩
      → ⟨ fst (Real.real α) E.≈[G] fst (Real.real β) ⟩ → ⟨ ⊥ ⟩)
    (Y : K.Name)
    (powerY : ⟨ CB.isPowerSet Y (Graph.checkNm w) ⟩)
    → ⟨ CB.isInjection Graph.graph (Graph.checkNm κ) Y ⟩
  isInjection lem real-subset real-distinct Y powerY =
      (relation , single-valued)
    , domain-total
    , range-in
    , injective
    where
    single-valued : (p : K.Name) → ⟨ fst p E.∈[G] Graph.graphCode ⟩
      → (q : K.Name) → ⟨ fst q E.∈[G] Graph.graphCode ⟩
      → (x y z : K.Name) → ⟨ (CB.isKPair p x y) ⊓ (CB.isKPair q x z) ⟩
      → ⟨ fst y E.≈[G] fst z ⟩
    single-valued p hp q hq x y z (hpy , hqz) = PT.rec (snd (fst y E.≈[G] fst z))
      (λ { (α , hα , pα) → PT.rec (snd (fst y E.≈[G] fst z))
        (λ { (β , hβ , qβ) →
          let py = components p x y α pα hpy
              qz = components q x z β qβ hqz
              checked = E.≈-trans (E.≈-sym (fst py)) (fst qz)
              ground = Copy.check-≈-inj α β checked
          in E.≈-trans (snd py)
               (E.≈-trans (ground-eq→real-eq α β ground) (E.≈-sym (snd qz))) })
        (subst ⟨_⟩ (graph-value (fst q)) hq) })
      (subst ⟨_⟩ (graph-value (fst p)) hp)

    domain-total : (x : K.Name) → ⟨ fst x E.∈[G] fst (Graph.checkNm κ) ⟩
      → ⟨ ⋁ K.Name (λ y → ⋁ K.Name (λ p →
        (fst p E.∈[G] Graph.graphCode) ⊓ CB.isKPair p x y)) ⟩
    domain-total x hx = PT.rec PT.squash₁
      (λ { (α , hα , xα) → ∣ Real.real α , ∣ Graph.vertex α , graph-in α hα ,
        Order.kpair-subst (Graph.vertex α) (Graph.checkNm α) x (Real.real α) (Real.real α)
          (E.≈-sym xα) (E.≈-refl (fst (Real.real α))) (canonical-pair α) ∣₁ ∣₁ })
      (subst ⟨_⟩ (Copy.check-value κ (fst x)) hx)

    range-in : (p : K.Name) → ⟨ fst p E.∈[G] Graph.graphCode ⟩ → (x y : K.Name)
             → ⟨ CB.isKPair p x y ⟩ → ⟨ fst y E.∈[G] fst Y ⟩
    range-in p hp x y hxy = PT.rec (snd (fst y E.∈[G] fst Y))
      (λ { (α , hα , pα) →
        let xy = components p x y α pα hxy
            real∈Y = powerY (Real.real α) .snd (real-subset α)
        in E.∈-congˡ (E.≈-sym (snd xy)) real∈Y })
      (subst ⟨_⟩ (graph-value (fst p)) hp)

    injective : (p : K.Name) → ⟨ fst p E.∈[G] Graph.graphCode ⟩
      → (q : K.Name) → ⟨ fst q E.∈[G] Graph.graphCode ⟩
      → (x y z : K.Name) → ⟨ (CB.isKPair p x y) ⊓ (CB.isKPair q z y) ⟩
      → ⟨ fst x E.≈[G] fst z ⟩
    injective p hp q hq x y z (hpx , hqz) = PT.rec (snd (fst x E.≈[G] fst z))
      (λ { (α , hα , pα) → PT.rec (snd (fst x E.≈[G] fst z))
        (λ { (β , hβ , qβ) →
          let px = components p x y α pα hpx
              qz = components q z y β qβ hqz
              realEq = E.≈-trans (E.≈-sym (snd px)) (snd qz)
              groundEq = choose α β hα hβ realEq
              checkEq = subst ⟨_⟩ (sym (Copy.chk-≈ α β)) groundEq
          in E.≈-trans (fst px) (E.≈-trans checkEq (E.≈-sym (fst qz))) })
        (subst ⟨_⟩ (graph-value (fst q)) hq) })
      (subst ⟨_⟩ (graph-value (fst p)) hp)
      where
      choose : (α β : S) → ⟨ α ∈ˢ κ ⟩ → ⟨ β ∈ˢ κ ⟩
             → ⟨ fst (Real.real α) E.≈[G] fst (Real.real β) ⟩ → ⟨ α ≈ˢ β ⟩
      choose α β hα hβ eq = cases (lem (α ≈ˢ β))
        where
        cases : ⟨ α ≈ˢ β ⟩ ⊎ (⟨ α ≈ˢ β ⟩ → Empty.⊥) → ⟨ α ≈ˢ β ⟩
        cases (inl yes) = yes
        cases (inr no) = Empty.rec
          (lower (real-distinct α β hα hβ (λ e → lift (no e)) eq))
