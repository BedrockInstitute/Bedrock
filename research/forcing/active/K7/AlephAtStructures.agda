{-# OPTIONS --cubical --safe --guardedness #-}

-- K7 Track G, SEAM PROBE. Nothing new is proved here. Every slot of
-- K7.Aleph's telescope that a LANDED layer can fill is filled from that layer
-- BY NAME, so a drift in any one of them fails here rather than passing
-- silently inside a file whose own telescope is a list of variables.
--
-- The architecture's sentence for this device, and it is the reason the file
-- exists: a K7 track that builds its own lookalike structure and does not add
-- this probe ships a well typed theorem about nothing. Track G's exposure to
-- that is the largest in the package, because ITS conclusions are the ones K10
-- assembles the headline contradiction from. If 𝒮ᴱ here were a private copy
-- rather than K5's own extension structure, every theorem of K7/Aleph.agda
-- would still typecheck and none of them would be about the Cohen extension.
--
-- FOUR THINGS THIS PROBE IS AIMED AT.
--
--   * The identity of the extension structure. K7/Aleph.agda assembles 𝒮ᴱ from
--     the flat value relation so that satisfaction computes. structure-agrees
--     asks Agda whether that assembly IS K5's P.Ext.structure, by refl.
--   * The identity of satisfaction. carrier-agrees and sat-agrees ask for
--     Track G's _⊨_ at K5's own Sat._⊨_, likewise by refl.
--   * The K6 transfers. copy-members and check-faithful arrive here as K6's
--     OWN exports at K5's OWN positivity predicate, not at Track G's spelling
--     of either. This is X7's corrected device D-II: a positive check runs at
--     the APPLICATION and never at the definition.
--   * chk-ordinal, which K6/Ordinals.agda:179-180 takes as a parameter and no
--     file in the compile root has ever filled. It is filled here, for real,
--     out of K5's groundSat and a Δ₀ certificate built by normalization. Two
--     of Track B's deliverables fall out of that and are asserted below.
--
--   * Track B's ord-compare AT THE EXTENSION. Track G's hardest slot. It is
--     not asserted here, it is built: K7.CardinalOrder is applied at 𝒮ᴱ and
--     its module Order is fed K5's own Extensionality and two membership
--     congruences made out of the value relation's laws. The slot is then
--     filled by the landed theorem.
--
-- WHAT IS NOT FILLED, AND WHY THAT IS NOT A DEFECT. no-collapse is Track F's
-- and its own seam probe is K7/PreserveAtTracks.agda, so it stays a parameter
-- here rather than being applied twice; chk-injectable has no owner anywhere
-- and stays a parameter because there is nothing to fill it with. CCC₂ᴵ and
-- the presentation's carrier and order arrive opaque for the same reason Track
-- F keeps them opaque: no body may specialize a chain condition to one notion.
--
-- The telescope is K5's Kernel and PosetSide telescopes concatenated, exactly
-- as K6/GroundTransferAtStructures.agda:47-64 and :68-88 do it.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using ( Formula )
import OrdinaryProfile
import Valuation
import CardinalBridge
import K5.Structures
import K6.GroundTransfer
import K7.Aleph
import K7.CardinalOrder
import Cubical.HITs.PropositionalTruncation as PT

module K7.AlephAtStructures {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
open import FOL.LevyHierarchy using ( Δ₀ ; checkΔ₀ )
open import FOL.Manipulation.ConstantMapping using ( mapFo )
open import Cubical.Induction.WellFounded using ( WellFounded )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Base.Classical using ( LEM )
open PT using ( ∥_∥₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

private module VL = Valuation 𝒮
open VL using ( Conditions )

module CBᴳ = CardinalBridge 𝒮
open At S id using () renaming ( _⊨_ to _⊨ᴳ_ )

-- THE Δ₀ CERTIFICATE FOR K1's ORDINAL FORMULA, by normalization. K7
-- architecture 1.5 records this as unverified, with the reasoning that
-- IsOrdinalφ (CardinalBridge.agda:522-529) uses only ∧̇, ∀̇∈, ∨̇, ∈̇ and ≐, so
-- bounded computes to true and checkΔ₀ builds the witness from tt. Verified
-- here. It is Track B's Δ₀-IsOrdinalφ and it costs one line, as predicted.

Δ₀-IsOrdinalφ : Δ₀ CBᴳ.IsOrdinalφ
Δ₀-IsOrdinalφ = checkΔ₀ CBᴳ.IsOrdinalφ tt

module Seam
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  (carrierᶠ    : S)
  (_≼ᶜ_        : Conditions carrierᶠ → Conditions carrierᶠ → Ω)
  (≼ᶜ-refl     : (p : Conditions carrierᶠ) → ⟨ p ≼ᶜ p ⟩)
  (≼ᶜ-trans    : {p q r : Conditions carrierᶠ} → ⟨ p ≼ᶜ q ⟩ → ⟨ q ≼ᶜ r ⟩ → ⟨ p ≼ᶜ r ⟩)
  (inhabitedᶜ  : ∥ Conditions carrierᶠ ∥₁)
  (IsNameᴾ     : S → Ω)
  (child-nameᴾ : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n → ⟨ IsNameᴾ x ⟩)
  where

  private
    module KS = K5.Structures.Kernel 𝒮
                  entry Child isPropChild child-entry child-wf ∅ᴺ ∅ᴺ-spec
    module PS = KS.PosetSide carrierᶠ _≼ᶜ_ ≼ᶜ-refl ≼ᶜ-trans inhabitedᶜ
                  IsNameᴾ child-nameᴾ

  module AtG (G : PS.P.Sub)
    (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
    (≈ˢ-paths    : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
    (ext-path    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
    (chk         : S → S)
    (chk-spec    : (a e : S) → (e ∈ˢ chk a)
                 ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrierᶠ)
                        ⊓ (e ≈ˢ entry (chk y) p))))
    (Γ           : S)
    (Γ-spec      : (e : S) → (e ∈ˢ Γ)
                 ≡ ⋁ S (λ p → (p ∈ˢ carrierᶠ) ⊓ (e ≈ˢ entry (chk p) p)))
    (chk-name    : (a : S) → ⟨ IsNameᴾ (chk a) ⟩)
    (inf         : OrdinaryProfile.Infinity 𝒮)
    where

    private
      module E  = PS.P.Ext G
      module C  = E.Copy entry-inj ≈ˢ-paths ext-path chk chk-spec Γ Γ-spec chk-name

      module T  = K6.GroundTransfer.Transfer 𝒮 IsNameᴾ E._≈[G]_ E._∈[G]_ PS.P.Cond G
      module TC = T.Copy entry carrierᶠ chk chk-spec Γ Γ-spec chk-name

    chkEnv-one : (u : S) → C.chkEnv (u ∷ []) ≡ (TC.groundName u ∷ [])
    chkEnv-one u = refl

    private
      module TG = TC.Ground C.chkEnv chkEnv-one
                    C.WithPos.groundSat C.WithPos.check-value
                    C.WithPos.check-faithful C.WithPos.chk-≈ inf

      -- Track G's own spine, applied at K5's value relation and nowhere else.

      module AN = K7.Aleph.Names 𝒮 IsNameᴾ
      module AL = AN.AtG E._≈[G]_ E._∈[G]_

    --------------------------------------------------------------------------
    -- ASSERTION 1. The structure and its satisfaction are K5's, by refl
    --------------------------------------------------------------------------

    carrier-agrees : AN.Nm ≡ PS.Nameᴾ
    carrier-agrees = refl

    structure-agrees : AL.𝒮ᴱ ≡ PS.𝒮ᴾ[ G ]
    structure-agrees = refl

    sat-agrees : ∀ {k} (ν : Vec PS.Nameᴾ k) (φ : Formula PS.Nameᴾ k)
               → AL._⊨_ ν φ ≡ E.Sat._⊨_ ν φ
    sat-agrees ν φ = refl

    -- And the same for K6's side, so that a drift between Track C's structure
    -- and Track G's is caught here and not two packages downstream.

    structure-agrees-K6 : AL.𝒮ᴱ ≡ T.𝒮ᴾ
    structure-agrees-K6 = refl

    --------------------------------------------------------------------------
    -- ASSERTION 2. chk-ordinal, filled for real
    --------------------------------------------------------------------------

    -- K6/Ordinals.agda:179-180 takes this as a parameter and nothing in the
    -- compile root has ever supplied it. The route is K6's own transfer-body
    -- (K6/GroundTransfer.agda:361-363) at K1's ordinal formula instead of at
    -- the infinity body: rewrite the copied environment at arity one, then
    -- apply K5's groundSat to the Δ₀ certificate. No mapFo computation lemma
    -- is owed, for the reason K6/GroundTransfer.agda:251-252 gives: IsOrdinalφ
    -- carries no constants, so mapFo groundName sends it to itself
    -- definitionally. That is Track B's ordinalφ-mapFo, and the refl below is
    -- the whole of its proof.

    ordinalφ-mapFo : mapFo TC.groundName CBᴳ.IsOrdinalφ ≡ AL.CBᴱ.IsOrdinalφ
    ordinalφ-mapFo = refl

    chk-ordinal : ⟨ PS.P.positive G ⟩ → (a : S)
                → AL._⊨_ (TC.groundName a ∷ []) AL.CBᴱ.IsOrdinalφ
                ≡ ((a ∷ []) ⊨ᴳ CBᴳ.IsOrdinalφ)
    chk-ordinal pos a =
      sym (cong (λ ν → E._⊨_ ν (mapFo TC.groundName CBᴳ.IsOrdinalφ))
                (chkEnv-one a))
      ∙ C.WithPos.groundSat pos CBᴳ.IsOrdinalφ Δ₀-IsOrdinalφ (a ∷ [])

    --------------------------------------------------------------------------
    -- ASSERTION 3. Track B's ord-compare EXISTS at the extension
    --------------------------------------------------------------------------

    -- This is the load-bearing unknown of Track G and it is settled here
    -- rather than asserted. K7/Aleph.agda's ord-compare slot is Track B's
    -- theorem (K7/CardinalOrder.agda:478-480) at 𝒮ᴱ, and Track B's file is
    -- structure-polymorphic, so the question is only whether its module Order
    -- (K7/CardinalOrder.agda:252-256) can be applied at the extension at all.
    -- It takes Extensionality and the two membership congruences. K5 exports
    -- the first (K5/Structures.agda:794-795) and the value relation's own laws
    -- give the other two, each as one ⇔toPath out of ∈-cong and ≈-sym
    -- (Valuation.agda:442, :445, :377). None of the three costs a profile
    -- axiom, so ord-compare is available at the extension for the price Track
    -- B states and no more: FoundationInduction, Separation and LEM ℓ.

    memLᴱ : (x y z : PS.Nameᴾ) → ⟨ fst x E.≈[G] fst y ⟩
          → (fst x E.∈[G] fst z) ≡ (fst y E.∈[G] fst z)
    memLᴱ x y z e = ⇔toPath (E.∈-congˡ e) (E.∈-congˡ (E.≈-sym e))

    memRᴱ : (x y z : PS.Nameᴾ) → ⟨ fst y E.≈[G] fst z ⟩
          → (fst x E.∈[G] fst y) ≡ (fst x E.∈[G] fst z)
    memRᴱ x y z e = ⇔toPath (E.∈-congʳ e) (E.∈-congʳ (E.≈-sym e))

    private
      module CO  = K7.CardinalOrder AL.𝒮ᴱ
      module COO = CO.Order PS.ext[ G ] memLᴱ memRᴱ

    -- And the slot filled, at exactly the type K7/Aleph.agda declares.

    ord-compareᴱ : AL.OPᴱ.FoundationInduction → AL.OPᴱ.Separation → LEM ℓ
                 → (α δ : PS.Nameᴾ)
                 → ⟨ AL.CBᴱ.isOrdinal α ⟩ → ⟨ AL.CBᴱ.isOrdinal δ ⟩
                 → ⟨ (α AL.∈ᴱ δ) ⊔ ((α AL.≈ᴱ δ) ⊔ (δ AL.∈ᴱ α)) ⟩
    ord-compareᴱ = COO.ord-compare

    -- K10's third prerequisite, which architecture 3.8 reduced to injectable
    -- composition. Both halves exist at the extension for the same reason and
    -- are named here so K10 does not have to rediscover where they live. Their
    -- hypothesis columns are Track B's own and are NOT this track's.

    injectable-transᴱ : AL.OPᴱ.Separation → AL.OPᴱ.Collection → AL.OPᴱ.Pairing
                      → (a b d : PS.Nameᴾ)
                      → ⟨ AL.CBᴱ.injectable a b ⟩ → ⟨ AL.CBᴱ.injectable b d ⟩
                      → ⟨ AL.CBᴱ.injectable a d ⟩
    injectable-transᴱ = COO.injectable-trans

    injectable-inclᴱ : AL.OPᴱ.Separation → AL.OPᴱ.Collection → AL.OPᴱ.Pairing
                     → (a b : PS.Nameᴾ) → ⟨ CO.isSubset a b ⟩
                     → ⟨ AL.CBᴱ.injectable a b ⟩
    injectable-inclᴱ = COO.injectable-incl

    --------------------------------------------------------------------------
    -- ASSERTION 4. Track G's theorems, at the real suppliers
    --------------------------------------------------------------------------

    -- Six slots are filled by name from K5 and K6; the rest are the slots
    -- whose suppliers do not exist, and they stay parameters here so that the
    -- reader can count them. Positivity is ForcingNotion's own predicate at
    -- K5's own G, never Track G's spelling of it.

    module Filled
      (c o : S)
      (CCC₂ᴵ : S → S → S → Ω)
      (Supplies : Type ℓ)
      (no-collapse : Supplies → ⟨ PS.P.positive G ⟩ → (v κ : S)
                   → ⟨ CBᴳ.isOmega v ⟩ → ⟨ CBᴳ.isCardinal κ ⟩ → ⟨ v ∈ˢ κ ⟩
                   → ⟨ CCC₂ᴵ c o v ⟩
                   → ⟨ AL.CBᴱ.isCardinal (TC.groundName κ) ⟩)
      (chk-injectable : (a b : S) → ⟨ CBᴳ.injectable a b ⟩
                      → ⟨ AL.CBᴱ.injectable (TC.groundName a) (TC.groundName b) ⟩)
      (w ω₁ ω₂ : S)
      (w-omega : ⟨ CBᴳ.isOmega w ⟩)
      (ω₁-succ : ⟨ CBᴳ.isSuccCardinal ω₁ w ⟩)
      (ω₂-succ : ⟨ CBᴳ.isSuccCardinal ω₂ ω₁ ⟩)
      (ω₁-members-countable : (b : S) → ⟨ b ∈ˢ ω₁ ⟩ → ⟨ CBᴳ.injectable b w ⟩)
      (pos : ⟨ PS.P.positive G ⟩)
      where

      private
        module AA = AL.Aleph
          E.sat-cong E.≈-refl E.≈-sym TC.groundName
          (PS.P.positive G) TG.copy-members C.WithPos.check-faithful
          (chk-ordinal pos)
          c o CCC₂ᴵ Supplies no-collapse
          ord-compareᴱ chk-injectable
          w ω₁ ω₂ w-omega ω₁-succ ω₂-succ ω₁-members-countable pos

      -- The three delivered statements, re-asked at K5's structure and K5's
      -- positivity. Nothing on either side of a colon below is Track G's
      -- spelling of anything.

      ω₁-is-cardinal : Supplies → ⟨ CCC₂ᴵ c o w ⟩
                     → ⟨ CardinalBridge.isCardinal PS.𝒮ᴾ[ G ] (TC.groundName ω₁) ⟩
      ω₁-is-cardinal = AA.ω₁-is-cardinal

      ω₂-is-cardinal : Supplies → ⟨ CCC₂ᴵ c o w ⟩
                     → ⟨ CardinalBridge.isCardinal PS.𝒮ᴾ[ G ] (TC.groundName ω₂) ⟩
      ω₂-is-cardinal = AA.ω₂-is-cardinal

      ω₁-identified : Supplies → ⟨ CCC₂ᴵ c o w ⟩
                    → OrdinaryProfile.FoundationInduction PS.𝒮ᴾ[ G ]
                    → OrdinaryProfile.Separation PS.𝒮ᴾ[ G ] → LEM ℓ
                    → ⟨ CardinalBridge.isSuccCardinal PS.𝒮ᴾ[ G ]
                          (TC.groundName ω₁) (TC.groundName w) ⟩
      ω₁-identified = AA.ω₁-identified

      -- And the unconditional one, at ForcingNotion's positivity and nothing
      -- else. Its hypothesis column is the assertion: if a filter law, an
      -- excluded middle or any engine component had crept into aleph-members,
      -- this line would not typecheck.

      aleph-members : ⟨ PS.P.positive G ⟩ → (κ : S) (τ : PS.Nameᴾ)
                    → ⟨ fst τ E.∈[G] chk κ ⟩
                    → ⟨ ⋁ S (λ a → (a ∈ˢ κ) ⊓ (fst τ E.≈[G] chk a)) ⟩
      aleph-members = AA.aleph-members
