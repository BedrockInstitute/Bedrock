{-# OPTIONS --cubical --safe --guardedness #-}

-- K6 Track J: the refutation and control track.
--
-- Rule 14 governs every line below. Each statement a competent reader of the
-- K6 architecture would write is transcribed under its own name and then
-- shown false, or shown to hold where the reader expected it to fail. Nothing
-- is repaired here and no landed file is edited.
--
-- Section 1 is the degenerate-G audit, stated at an ABSTRACT structure whose
-- membership is empty and whose equality is full. Three fields are refuted at
-- it and SIX are INHABITED at it, so the audit gives no evidence about those
-- six. Architecture 4.10's table lists four non-discriminated fields; the two
-- it omits are `extensional` and `ChoiceSet`, and both are proved below.
--
-- Section 2 discharges the two abstract hypotheses of section 1 at the real
-- extension structure, from `G = λ _ → ⊥` and nothing else.
--
-- Section 3 is R1 to R7.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module K6.Refuted {ℓ : Level} where

open import FOL.ZFStructure using ( module hPropStructure )
import Cubical.Data.Empty as Empty
import Cubical.Functions.Logic as Logic
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Induction.WellFounded
  using ( Acc; acc; isPropAcc; WellFounded; module WFI )

import OrdinaryProfile
open import FOL.Syntax using ( Formula )
open import Cubical.Data.Sigma using ( _×_ )

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 1. The degenerate audit, at an abstract structure
--------------------------------------------------------------------------------

-- The two hypotheses are exactly what `G = λ _ → ⊥` delivers, and section 2
-- derives them there. Stating them abstractly keeps this section free of every
-- K3 and K5 module application, and makes the audit a statement about ANY
-- structure with an empty membership and a full equality, which is strictly
-- more than the one instance needs.
--
-- `σ₀` is needed only by the two refutations whose field type begins with a
-- universally quantified set, `Pairing` and `PowerSet`. `Infinity` is a closed
-- sentence and is refuted without it.

module Degenerate
  (𝒮ᴱ      : ZFStructure (hPropAlgebra ℓ))
  (σ₀      : ZFStructure.S 𝒮ᴱ)
  (∈-empty : (x a : ZFStructure.S 𝒮ᴱ)
           → ⟨ ZFStructure._∈ˢ_ 𝒮ᴱ x a ⟩ → ⟨ ⊥ ⟩)
  (≈-full  : (x a : ZFStructure.S 𝒮ᴱ) → ⟨ ZFStructure._≈ˢ_ 𝒮ᴱ x a ⟩)
  where

  open hPropStructure 𝒮ᴱ
  module OP = OrdinaryProfile 𝒮ᴱ

  ------------------------------------------------------------------------------
  -- 1a. The three fields the audit DOES discriminate
  ------------------------------------------------------------------------------

  -- Pairing fails because the pair of σ₀ with itself must contain σ₀, and the
  -- description side of the biconditional is satisfied by the full equality
  -- while the membership side is empty. Caught by: the value of the two
  -- relations, not by any reading theorem.

  no-pairing : OP.Pairing → ⟨ ⊥ ⟩
  no-pairing pr = PT.rec (snd ⊥) step (pr σ₀ σ₀)
    where
    step : Σ[ p ∈ S ] ⟨ ⋀ S (λ x → OP.iff (x ∈ˢ p) ((x ≈ˢ σ₀) ⊔ (x ≈ˢ σ₀))) ⟩
         → ⟨ ⊥ ⟩
    step (p , h) = ∈-empty σ₀ p (snd (h σ₀) (Logic.inl (≈-full σ₀ σ₀)))

  -- Power Set fails for the same reason one step up: "every member of σ₀ is a
  -- member of σ₀" is vacuously true, so σ₀ is forced into the power set, which
  -- is empty.

  no-power : OP.PowerSet → ⟨ ⊥ ⟩
  no-power pw = PT.rec (snd ⊥) step (pw σ₀)
    where
    step : Σ[ v ∈ S ] ⟨ ⋀ S (λ x → OP.iff (x ∈ˢ v)
                          (⋀ S (λ y → (y ∈ˢ x) ⇒ (y ∈ˢ σ₀)))) ⟩
         → ⟨ ⊥ ⟩
    step (v , h) =
      ∈-empty σ₀ v (snd (h σ₀) (λ y hy → Empty.rec* (∈-empty y σ₀ hy)))

  -- Infinity fails at its FIRST conjunct and not at the successor clause: the
  -- inductive set must have a memberless member, and a memberless member is
  -- still a member.

  no-infinity : OP.Infinity → ⟨ ⊥ ⟩
  no-infinity inf = PT.rec (snd ⊥) outer inf
    where
    inner : Σ[ e ∈ S ] ⟨ (e ∈ˢ σ₀) ⊓ (⋀ S (λ z → (z ∈ˢ e) ⇒ ⊥)) ⟩ → ⟨ ⊥ ⟩
    inner (e , heu , _) = ∈-empty e σ₀ heu
    outer : Σ[ u ∈ S ] ⟨ (⋁ S (λ e → (e ∈ˢ u) ⊓ (⋀ S (λ z → (z ∈ˢ e) ⇒ ⊥))))
                       ⊓ (⋀ S (λ x → (x ∈ˢ u) ⇒
                            (⋁ S (λ y → (y ∈ˢ u) ⊓ (x ∈ˢ y))))) ⟩
          → ⟨ ⊥ ⟩
    outer (u , hasE , _) =
      PT.rec (snd ⊥) (λ { (e , heu , _) → ∈-empty e u heu }) hasE

  ------------------------------------------------------------------------------
  -- 1b. The six fields the audit does NOT discriminate
  ------------------------------------------------------------------------------

  -- Every one of the six is INHABITED at the degenerate structure. A proof of
  -- any of them that happened to be vacuous would therefore pass the audit
  -- unremarked, which is the whole reason ruling D8 asks for a positive
  -- control. Note that four of the six take the argument set itself as the
  -- witness for their existential, so the witness costs nothing at all.

  yes-extensional : OP.Extensionality
  yes-extensional a b _ = ≈-full a b

  yes-union : OP.Union
  yes-union a = ∣ a , (λ x →
      (λ h → Empty.rec* (∈-empty x a h))
    , (λ h → PT.rec (snd (x ∈ˢ a))
               (λ { (y , hya , _) → Empty.rec* (∈-empty y a hya) }) h)) ∣₁

  yes-separation : OP.Separation
  yes-separation a φ = ∣ a , (λ x →
      (λ h → Empty.rec* (∈-empty x a h)) , fst) ∣₁

  yes-collection : OP.Collection
  yes-collection a φ _ = ∣ a , (λ x h → Empty.rec* (∈-empty x a h)) ∣₁

  yes-foundation : OP.FoundationInduction
  yes-foundation φ st x = st x (λ y hy → Empty.rec* (∈-empty y x hy))

  yes-choice : OP.ChoiceSet
  yes-choice a _ _ = ∣ a , (λ x h → Empty.rec* (∈-empty x a h)) ∣₁

  -- The audit's verdict as one statement: seven of the nine components of
  -- OrdinaryZFC are simultaneously inhabited here and three are refuted, so
  -- the audit separates the eight-field record into 3 and 6 and no further.

  audit-nondiscriminating :
      OP.Extensionality × (OP.Union × (OP.Separation
    × (OP.Collection × (OP.FoundationInduction × OP.ChoiceSet))))
  audit-nondiscriminating =
    yes-extensional , yes-union , yes-separation
      , yes-collection , yes-foundation , yes-choice

  audit-discriminating :
      (OP.Pairing → ⟨ ⊥ ⟩) × ((OP.PowerSet → ⟨ ⊥ ⟩) × (OP.Infinity → ⟨ ⊥ ⟩))
  audit-discriminating = no-pairing , no-power , no-infinity

--------------------------------------------------------------------------------
-- 2. The extension spine, and the degeneracy discharged at G = λ _ → ⊥
--------------------------------------------------------------------------------

-- Every parameter below is transcribed from the cited source line and is a
-- VARIABLE here: no K3 or K5 module is applied in this file (architecture part
-- 4, the paragraph above 4.0). `Nm` and `𝒮ᴾ` are DEFINED rather than taken,
-- from K5/Structures.agda:264 and :285-290 respectively, so that the profile's
-- field types can be named at the extension structure at all.

module Extension
  (𝒮        : ZFStructure (hPropAlgebra ℓ))
  (entry    : ZFStructure.S 𝒮 → ZFStructure.S 𝒮 → ZFStructure.S 𝒮)
  (Child    : ZFStructure.S 𝒮 → ZFStructure.S 𝒮 → Type ℓ)
  (carrierᶠ : ZFStructure.S 𝒮)
  (IsNameᴾ  : ZFStructure.S 𝒮 → Ω)
  where

  open hPropStructure 𝒮

  -- Valuation.agda:121-122, verbatim.

  Cond : Type ℓ
  Cond = Σ[ p ∈ S ] ⟨ p ∈ˢ carrierᶠ ⟩

  -- ForcingNotion.agda:88-89, at this carrier.

  Sub : Type (ℓ-suc ℓ)
  Sub = Cond → Ω

  -- K5/Structures.agda:263-264, verbatim. `nmOf` is K5's `fst`; rule 11
  -- forbids binding the name `fst`, so the projection is named here.

  Nm : Type ℓ
  Nm = Σ[ n ∈ S ] ⟨ IsNameᴾ n ⟩

  nmOf : Nm → S
  nmOf σ = fst σ

  isSetNm : isSet Nm
  isSetNm = isSetΣSndProp isSetS (λ n → snd (IsNameᴾ n))

  module AtOneG
    (G           : Sub)
    (‖Active‖    : S → S → Ω)
    (_≈[G]_      : S → S → Ω)
    (_∈[G]_      : S → S → Ω)
    -- Valuation.agda:244-248, the definition of ‖Active‖ read forward.
    (active-unfold : (x n : S) → ⟨ ‖Active‖ x n ⟩
                   → ∥ Σ[ p ∈ S ] Σ[ hp ∈ ⟨ p ∈ˢ carrierᶠ ⟩ ]
                        (⟨ entry x p ∈ˢ n ⟩ × ⟨ G (p , hp) ⟩) ∥₁)
    -- Valuation.agda:294-295.
    (∈-unfold    : (m n : S)
                 → (m ∈[G] n) ≡ ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y)))
    -- Valuation.agda:338-344.
    (≈-intro     : {m n : S}
                 → ((x : S) → ⟨ ‖Active‖ x m ⟩
                    → ⟨ ⋁ S (λ y → ‖Active‖ y n ⊓ (x ≈[G] y)) ⟩)
                 → ((y : S) → ⟨ ‖Active‖ y n ⟩
                    → ⟨ ⋁ S (λ x → ‖Active‖ x m ⊓ (x ≈[G] y)) ⟩)
                 → ⟨ m ≈[G] n ⟩)
    -- Valuation.agda:349, :442-446.
    (≈-refl      : (m : S) → ⟨ m ≈[G] m ⟩)
    (∈-congˡ     : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩)
    (∈-congʳ     : {m n n' : S} → ⟨ n ≈[G] n' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m ∈[G] n' ⟩)
    where

    -- K5/Structures.agda:285-290, verbatim. This record IS
    -- K5.Structures.Kernel.Side.Ext.structure once the seven kernel
    -- parameters and the two side parameters are supplied; the seam probe of
    -- another track is what checks that, not this file.

    𝒮ᴾ : ZFStructure (hPropAlgebra ℓ)
    𝒮ᴾ = record
      { S      = Nm
      ; isSetS = isSetNm
      ; _≈ˢ_   = λ σ τ → nmOf σ ≈[G] nmOf τ
      ; _∈ˢ_   = λ σ τ → nmOf σ ∈[G] nmOf τ }

    module OPᴾ = OrdinaryProfile 𝒮ᴾ

    ----------------------------------------------------------------------------
    -- 2a. The degenerate G
    ----------------------------------------------------------------------------

    -- The single hypothesis of the audit, and it is what `G = λ _ → ⊥` is.
    -- Nothing else about G is used below.

    module AtEmptyG
      (G-empty : (p : S) (hp : ⟨ p ∈ˢ carrierᶠ ⟩) → ⟨ G (p , hp) ⟩ → ⟨ ⊥ ⟩)
      where

      active-empty : (x n : S) → ⟨ ‖Active‖ x n ⟩ → ⟨ ⊥ ⟩
      active-empty x n ha = PT.rec (snd ⊥)
        (λ { (p , hp , _ , hG) → G-empty p hp hG }) (active-unfold x n ha)

      ∈-empty : (x a : Nm) → ⟨ nmOf x ∈[G] nmOf a ⟩ → ⟨ ⊥ ⟩
      ∈-empty x a h = PT.rec (snd ⊥)
        (λ { (y , hy , _) → active-empty y (nmOf a) hy })
        (subst ⟨_⟩ (∈-unfold (nmOf x) (nmOf a)) h)

      ≈-full : (x a : Nm) → ⟨ nmOf x ≈[G] nmOf a ⟩
      ≈-full x a = ≈-intro
        (λ u hu → Empty.rec* (active-empty u (nmOf x) hu))
        (λ v hv → Empty.rec* (active-empty v (nmOf a) hv))

      -- The audit at the real extension structure, by one application of
      -- section 1 and nothing else. `σ₀` is any name; `∅ᴺ` supplies one,
      -- NameKernel.agda:538-545.

      module Audit (σ₀ : Nm) = Degenerate 𝒮ᴾ σ₀ ∈-empty ≈-full

    ----------------------------------------------------------------------------
    -- 2b. R5. The poison parameter T-D1 survives the degenerate audit
    ----------------------------------------------------------------------------

    -- Architecture 4.4's trap T-D1 is the hypothesis
    --   ext-acc : (σ : Nm) → Acc (λ ρ τ → ⟨ nm ρ ∈[G] nm τ ⟩) σ
    -- which makes `foundation` immediate and is available at no interesting G.
    -- 4.4 asserts "it is also true at the degenerate G ... so no degenerate
    -- audit catches it". That assertion is PROVED here rather than relayed:
    -- with no edges at all every name is accessible in one step. So the
    -- degenerate audit is not a control for T-D1 and only the telescope
    -- censuses F1, F2 and F3 are.
    --
    -- COORDINATION NOTE: this is the only occurrence of `Acc` in a K6 .agda
    -- file, and Track D's census F1 greps `\bAcc\b` over all of K6/. The
    -- census must exclude K6/Refuted.agda or it reports a false positive here.

    ExtAcc : Type ℓ
    ExtAcc = (σ : Nm) → Acc (λ ρ τ → ⟨ nmOf ρ ∈[G] nmOf τ ⟩) σ

    module _
      (G-empty : (p : S) (hp : ⟨ p ∈ˢ carrierᶠ ⟩) → ⟨ G (p , hp) ⟩ → ⟨ ⊥ ⟩)
      where

      open AtEmptyG G-empty using ( ∈-empty )

      poison-survives-audit : ExtAcc
      poison-survives-audit σ = acc (λ τ h → Empty.rec* (∈-empty τ σ h))

    ----------------------------------------------------------------------------
    -- 2c. R1. A pair name at one fixed condition
    ----------------------------------------------------------------------------

    -- The reader's pair name is {(σ, p₀), (τ, p₀)} at a chosen condition p₀.
    -- Its activity clause is PairAtOne below, read straight off Active
    -- (Valuation.agda:245-247): every active entry of the code witnesses that
    -- p₀ lies in G. The statement that this code satisfies the Pairing
    -- biconditional is FALSE whenever p₀ is outside G, and no filter law puts
    -- a CHOSEN condition into G: isFilter's `inhabited` field is
    -- ⟨ positive G ⟩ (ForcingNotion.agda:177), a TRUNCATED existential, from
    -- which no condition can be projected into the data of a ground set.
    -- Track A's `spread`, which places a subname at EVERY condition, is what
    -- repairs this; that repair is Track A's and is not made here.
    --
    -- Caught by: the value of ∈[G], through ∈-unfold. No reading theorem and
    -- no scoping check sees it, because the code and the formula are both
    -- well formed.

    PairSpec : Nm → Nm → Nm → Type ℓ
    PairSpec π σ τ =
      ⟨ ⋀ Nm (λ x → OPᴾ.iff (nmOf x ∈[G] nmOf π)
          ((nmOf x ≈[G] nmOf σ) ⊔ (nmOf x ≈[G] nmOf τ))) ⟩

    PairAtOne : (p₀ : S) → ⟨ p₀ ∈ˢ carrierᶠ ⟩ → Nm → Type ℓ
    PairAtOne p₀ hp₀ π =
      (x : S) → ⟨ ‖Active‖ x (nmOf π) ⟩ → ⟨ G (p₀ , hp₀) ⟩

    pair-at-one-condition-fails :
        (p₀ : S) (hp₀ : ⟨ p₀ ∈ˢ carrierᶠ ⟩) (π σ τ : Nm)
      → (⟨ G (p₀ , hp₀) ⟩ → ⟨ ⊥ ⟩)
      → PairAtOne p₀ hp₀ π
      → PairSpec π σ τ
      → ⟨ ⊥ ⟩
    pair-at-one-condition-fails p₀ hp₀ π σ τ out only spec =
      PT.rec (snd ⊥)
        (λ { (y , hy , _) → out (only y hy) })
        (subst ⟨_⟩ (∈-unfold (nmOf σ) (nmOf π))
          (snd (spec σ) (Logic.inl (≈-refl (nmOf σ)))))

    ----------------------------------------------------------------------------
    -- 2d. R2. The union name without the refinement conjuncts
    ----------------------------------------------------------------------------

    -- The correct union name collects the members of the ACTIVE subnames of σ
    -- and weights each by a common refinement of the two conditions involved.
    -- The naive one drops the refinement and collects the members of EVERY
    -- subname, active or not. NaiveUnionOf is that inclusion, and the theorem
    -- says it is inconsistent with the Union biconditional at any σ that has
    -- an inactive subname with a member found in no active subname.
    --
    -- Caught by: the value of ∈[G] again. This is the shape 4.10 calls the
    -- most likely silent error in the package, and nothing in the syntax layer
    -- sees it: both codes are names and both formulas are Δ₀.
    --
    -- MEASURED NEGATIVE, and it is the K5 Track J shape. The three hypotheses
    -- are jointly satisfiable only at a notion with at least two conditions
    -- and a G omitting one. This file's companion K6/OnePoint.agda supplies a
    -- CODED notion for the first time in the programme, but it supplies a
    -- ONE-point one, at which the middle hypothesis is unsatisfiable. So R2
    -- remains an implication whose antecedent the programme does not witness,
    -- and the owner of the witness is K8.

    NaiveUnionOf : Nm → Nm → Type ℓ
    NaiveUnionOf σ ν =
      (υ ξ : Nm) → Child (nmOf υ) (nmOf σ) → ⟨ nmOf ξ ∈[G] nmOf υ ⟩
                 → ⟨ nmOf ξ ∈[G] nmOf ν ⟩

    UnionSpec : Nm → Nm → Type ℓ
    UnionSpec ν a =
      ⟨ ⋀ Nm (λ x → OPᴾ.iff (nmOf x ∈[G] nmOf ν)
          (⋁ Nm (λ y → (nmOf y ∈[G] nmOf a) ⊓ (nmOf x ∈[G] nmOf y)))) ⟩

    naive-union-fails :
        (σ ν υ ξ : Nm)
      → NaiveUnionOf σ ν
      → Child (nmOf υ) (nmOf σ)
      → ⟨ nmOf ξ ∈[G] nmOf υ ⟩
      → ((y : Nm) → ⟨ nmOf y ∈[G] nmOf σ ⟩ → ⟨ nmOf ξ ∈[G] nmOf y ⟩ → ⟨ ⊥ ⟩)
      → UnionSpec ν σ
      → ⟨ ⊥ ⟩
    naive-union-fails σ ν υ ξ naive edge memb nowhere spec =
      PT.rec (snd ⊥)
        (λ { (y , hyσ , hξy) → nowhere y hyσ hξy })
        (fst (spec ξ) (naive υ ξ edge memb))

    ----------------------------------------------------------------------------
    -- 2e. R3. The separation name without the χ ∈ α conjunct
    ----------------------------------------------------------------------------

    -- Q stands for the class the Separation instance cuts by; at the profile's
    -- own field it is λ x → ⟨ (x ∷ []) ⊨ φ ⟩ (OrdinaryProfile.agda:89-91) and
    -- the refutation does not read it, which is the point: the defect is in
    -- the BOUND and not in the formula. Dropping the χ ∈ α conjunct admits one
    -- member from outside α and the forward direction of the biconditional
    -- dies in one step.
    --
    -- Caught by: type checking of the biconditional's first projection. This
    -- is the cheapest of the seven and it is here so that the expensive ones
    -- are not mistaken for the norm.

    SepSpec : Nm → Nm → (Nm → Ω) → Type ℓ
    SepSpec s a Q =
      ⟨ ⋀ Nm (λ x → OPᴾ.iff (nmOf x ∈[G] nmOf s)
          ((nmOf x ∈[G] nmOf a) ⊓ Q x)) ⟩

    naive-separation-fails :
        (s a ξ : Nm) (Q : Nm → Ω)
      → ⟨ nmOf ξ ∈[G] nmOf s ⟩
      → (⟨ nmOf ξ ∈[G] nmOf a ⟩ → ⟨ ⊥ ⟩)
      → SepSpec s a Q
      → ⟨ ⊥ ⟩
    naive-separation-fails s a ξ Q inS outA spec = outA (fst (fst (spec ξ) inS))

    ----------------------------------------------------------------------------
    -- 2f. R7. The ChoiceSet host-path premise, ruling D11
    ----------------------------------------------------------------------------

    -- TRANSCRIPTION, OrdinaryProfile.agda:111-113 and :115-124, read in this
    -- session. The comment says uniqueness is "internal ... up to the
    -- structure's ≈ˢ". The conclusion's inner uniqueness clause does use ≈ˢ
    -- (:123-124). The DISJOINTNESS PREMISE does not: it concludes a host path
    -- x ≡ y (:119-120). At every ground instance in the programme ≈ˢ IS the
    -- host path, so nothing caught it; at 𝒮ᴾ[ G ] a host path between names is
    -- strictly finer than ≈[G].
    --
    -- THE ARGUMENT, AND IT CLOSES. Nothing is assumed about G. The premise,
    -- applied to an inhabited member and to any value-equal name, forces the
    -- two CODES to be equal, because ∈[G] is a congruence on both sides
    -- (K5/Structures.agda:278-279) and so a value-equal partner of a member of
    -- a is a member of a sharing all of its members.

    ChoiceInhabited : Nm → Type ℓ
    ChoiceInhabited a =
      (x : Nm) → ⟨ nmOf x ∈[G] nmOf a ⟩ → ∥ Σ[ y ∈ Nm ] ⟨ nmOf y ∈[G] nmOf x ⟩ ∥₁

    ChoiceDisjoint : Nm → Type ℓ
    ChoiceDisjoint a =
      (x y : Nm) → ⟨ nmOf x ∈[G] nmOf a ⟩ → ⟨ nmOf y ∈[G] nmOf a ⟩
        → ∥ Σ[ z ∈ Nm ] (⟨ nmOf z ∈[G] nmOf x ⟩ × ⟨ nmOf z ∈[G] nmOf y ⟩) ∥₁
        → x ≡ y

    -- The premise pair collapses the whole value-equality class of any
    -- inhabited member of a to ONE code.

    choice-premise-forces-code-equality :
        (a x x' : Nm)
      → ChoiceInhabited a → ChoiceDisjoint a
      → ⟨ nmOf x ∈[G] nmOf a ⟩ → ⟨ nmOf x ≈[G] nmOf x' ⟩
      → x ≡ x'
    choice-premise-forces-code-equality a x x' inh disj hxa hxx' =
      disj x x' hxa (∈-congˡ hxx' hxa)
        (PT.map (λ { (y , hyx) → y , hyx , ∈-congʳ hxx' hyx }) (inh x hxa))

    -- The vacuity corollary. If ONE inhabited member of a has a code-distinct
    -- value-equal partner, the two premises cannot both hold and the field
    -- says nothing at that a.

    choiceset-vacuous-at :
        (a x x' : Nm)
      → ChoiceInhabited a → ChoiceDisjoint a
      → ⟨ nmOf x ∈[G] nmOf a ⟩ → ⟨ nmOf x ≈[G] nmOf x' ⟩
      → (nmOf x ≡ nmOf x' → ⟨ ⊥ ⟩)
      → ⟨ ⊥ ⟩
    choiceset-vacuous-at a x x' inh disj hxa hxx' distinct =
      distinct (cong nmOf (choice-premise-forces-code-equality
                            a x x' inh disj hxa hxx'))

    -- THE PROPOSAL, ruling D11. Editing OrdinaryProfile.agda is forbidden, so
    -- the corrected premise is declared here and never used. Under it the
    -- theorem above degenerates to its own hypothesis and constrains no code.
    -- `choiceFromStrong` (ProfileFromStrong.agda:162-199) must be re-checked
    -- against this shape before anyone adopts it.

    ChoiceDisjointProposed : Nm → Type ℓ
    ChoiceDisjointProposed a =
      (x y : Nm) → ⟨ nmOf x ∈[G] nmOf a ⟩ → ⟨ nmOf y ∈[G] nmOf a ⟩
        → ∥ Σ[ z ∈ Nm ] (⟨ nmOf z ∈[G] nmOf x ⟩ × ⟨ nmOf z ∈[G] nmOf y ⟩) ∥₁
        → ⟨ nmOf x ≈[G] nmOf y ⟩

    proposed-premise-is-weaker :
        (a : Nm) → ChoiceDisjoint a → ChoiceDisjointProposed a
    proposed-premise-is-weaker a disj x y hx hy sh =
      subst (λ w → ⟨ nmOf x ≈[G] nmOf w ⟩) (disj x y hx hy sh)
        (≈-refl (nmOf x))

    ----------------------------------------------------------------------------
    -- 2g. RULE 15 RE-MEASURED. The poison is a THEOREM at 𝒮ᴾ[ G ]
    ----------------------------------------------------------------------------

    -- The coordinator's rule 15, transcribed verbatim from the message that
    -- carried it:
    --
    --   "A FIELD'S TYPE CAN FAIL TO DISCRIMINATE A LEGITIMATE PROOF FROM A
    --    POISONED ONE. THE TELESCOPE IS THE ONLY PROTECTION."
    --   "ext-wf : WellFounded (λ (ρ τ : NameOf IsNameᴾ) → ⟨ fst ρ ∈[G] fst τ ⟩)
    --    ... That is Bell's external well-foundedness of the extension's
    --    membership: K13's, forbidden to K6 by the roadmap, and FALSE at a
    --    genuine forcing extension."
    --   "`atom-∈`, `atom-≐`, `ext-surjective`, `Supply` and `LEM ℓ` pass: they
    --    are unproved at this layer, not false at the instance. `ext-wf`
    --    fails."
    --
    -- MEASURED NEGATIVE, ruling 13. `ext-wf` does not fail, because it is not
    -- false at any instance: it is a THEOREM of the shared spine, proved below
    -- from `child-wf` and four spine facts, with no hypothesis on G at all.
    --
    -- The mathematics, and it is one line. Bell's equivalence between
    -- well-foundedness of the extension's membership and genericity is about
    -- the QUOTIENT carrier and its transitive collapse; K5's own non-claim 3
    -- gives that as its reason (K5/Structures.agda:507-512). But 𝒮ᴾ[ G ]'s
    -- carrier is `Nm`, a plain Σ-type over S (K5/Structures.agda:263-264), and
    -- architecture 3.1's Leg 1 says so in terms. On `Nm` the relation still
    -- descends the CODE: a value-member of τ is value-EQUAL to an active
    -- subname of τ, an active subname is a Child (Valuation.agda:257), and
    -- value-equal codes have the SAME ∈[G]-predecessors, by ∈-congʳ. So the
    -- accessibility transports sideways along ≈[G] and downwards along Child,
    -- and child-wf finishes it. Genericity is nowhere in the argument.
    --
    -- CONSEQUENCE, and it is the whole point of transcribing rule 15 rather
    -- than obeying it. A `foundation` proof routed through `ext-wf` at
    -- 𝒮ᴾ[ G ] is INDIRECT, not vacuous: its hypothesis is discharged below.
    -- Rule 15 as a general principle is untouched and its census is still
    -- worth running; its one named witness is not a witness.
    --
    -- What IS true about ext-wf, and it is a different statement: it is not
    -- available at the K13 QUOTIENT, where Bell's equivalence bites, and a K6
    -- file that proved `foundation` at a quotient carrier this way would be
    -- doing K13's work without K13's hypothesis. No K6 file has a quotient
    -- carrier; `SetQuotients` measures 0 across K6.

    module WithKernel
      (child-wf     : WellFounded Child)
      -- Valuation.agda:257.
      (active-child : (x n : S) → ⟨ ‖Active‖ x n ⟩ → Child x n)
      -- K5/Structures.agda:250.
      (child-nameᴾ  : (n : S) → ⟨ IsNameᴾ n ⟩ → (x : S) → Child x n
                    → ⟨ IsNameᴾ x ⟩)
      where

      _<ᴾ_ : Nm → Nm → Type ℓ
      ρ <ᴾ τ = ⟨ nmOf ρ ∈[G] nmOf τ ⟩

      -- Value-equal codes have the same ∈[G]-predecessors, so accessibility is
      -- a congruence for ≈[G]. This is the step that would be missing at a
      -- quotient carrier, where the two codes are ONE point and there is
      -- nothing to transport.

      acc-≈ : (ρ υ : Nm) → ⟨ nmOf ρ ≈[G] nmOf υ ⟩ → Acc _<ᴾ_ υ → Acc _<ᴾ_ ρ
      acc-≈ ρ υ e (acc f) = acc (λ ζ hζ → f ζ (∈-congʳ e hζ))

      ext-wf : WellFounded _<ᴾ_
      ext-wf σ = WFI.induction child-wf {P = Motive} go (nmOf σ) (snd σ)
        where
        Motive : S → Type ℓ
        Motive n = (hn : ⟨ IsNameᴾ n ⟩) → Acc _<ᴾ_ (n , hn)

        go : (n : S) → ((x : S) → Child x n → Motive x) → Motive n
        go n IH hn = acc (λ ρ hρ → PT.rec (isPropAcc ρ)
          (λ { (y , hy , e) →
                 acc-≈ ρ (y , child-nameᴾ n hn y (active-child y n hy)) e
                   (IH y (active-child y n hy)
                        (child-nameᴾ n hn y (active-child y n hy))) })
          (subst ⟨_⟩ (∈-unfold (nmOf ρ) n) hρ))

      -- The same fact in the shape the coordinator's message quotes, so that a
      -- reviewer can diff it against Track D's negative control directly.

      ext-acc : (σ : Nm) → Acc (λ ρ τ → ⟨ nmOf ρ ∈[G] nmOf τ ⟩) σ
      ext-acc = ext-wf

      -- And therefore the poisoned proof of Foundation is a proof. It is
      -- reported here as a MEASUREMENT and it is not offered as the field:
      -- Track D owns `foundation` and proved it the direct way.

      foundation-via-ext-wf : OPᴾ.FoundationInduction
      foundation-via-ext-wf φ = WFI.induction ext-wf

--------------------------------------------------------------------------------
-- 3. R6, transcribed and NOT refuted
--------------------------------------------------------------------------------

-- K5/Structures.agda:503-505, quoted from source:
--
--   Elementarity : (S → Nm) → Type (ℓ-suc ℓ)
--   Elementarity h = ∀ {k} (φ : Formula S k) (γ : Vec S k)
--                  → (mapEnv h γ ⊨ mapFo h φ) ≡ Gr._⊨_ γ φ
--
-- and K5's own reason at :495-501, quoted: refuting it "needs a concrete
-- forcing notion at which some unbounded formula changes truth value, and K5
-- has an instance of the FRAME and not of the NOTION."
--
-- THE OBSTRUCTION, AND IT IS NOT THE ONE THE ARCHITECTURE NAMES. 4.10 says
-- R6 is blocked because "O4 says none exists". As of this file O4's first
-- half is discharged: K6/OnePoint.agda is an inhabitant of
-- CodedCompletion.Presentation (:201-208), the first in the programme. R6 is
-- still blocked, for a DIFFERENT reason, and the difference matters to whoever
-- schedules K8: the notion R6 needs is one that ADDS a set, and the one-point
-- notion is precisely the one at which the extension IS the ground
-- (K5/Structures.agda:527-531). So the remaining obstruction is "no NONTRIVIAL
-- coded presentation", which is a strictly smaller claim than O4 as written,
-- and K6/OnePoint.agda section 6 records it beside the notion itself.
--
-- Claiming a refutation here would be the failure. None is claimed.

--------------------------------------------------------------------------------
-- 4. The reading-theorem control, rule 6
--------------------------------------------------------------------------------

-- Rule 6: "A pure off-by-one is caught by intrinsic scoping before any
-- reading, but uniform-depth formulas get protection ONLY from their reading
-- theorems." Architecture 3.5 hands Track G an arity trap at exactly such a
-- formula: the name recogniser nameAtˢ is stated at ARITY TWO
-- (NameSpace.agda:176-177) and its adequacy at (t ∷ W ∷ []), while separateOf
-- takes a Formula S 1, so the weight set must be frozen into the formula.
--
-- The control below is the SWAP, not the off-by-one. Both formulas are
-- Formula S 2, both are well scoped, and no intrinsic check separates them.
-- Their readings are two DIFFERENT elements of Ω, and both readings are refl,
-- so the reading theorem is the only mechanism that sees the difference. This
-- is K5 Track C's instantiation-vector swap in the smallest form that still
-- exhibits it.

module ReadingControl (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

  open hPropStructure 𝒮
  open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At )
  open At S id using ( _⊨_ )
  open import NameSpace 𝒮 using ( nameAtˢ; nameΔ )

  -- The recogniser as 3.5 requires it: t at slot zero, the weight set W at
  -- slot one. Its reading is nameΔ W t, which name-adequate
  -- (NameSpace.agda:951-953) equates with IsName t.

  correct-reading : (t W : S)
                  → ((t ∷ W ∷ []) ⊨ nameAtˢ zero (suc zero)) ≡ nameΔ W t
  correct-reading t W = refl

  -- The swap. Same type, same depth, same scoping, different sentence: it says
  -- that W is a name with weight bound t.

  swapped-reading : (t W : S)
                  → ((t ∷ W ∷ []) ⊨ nameAtˢ (suc zero) zero) ≡ nameΔ t W
  swapped-reading t W = refl

  -- The control's content, stated as a type so that it is checked rather than
  -- asserted: the two formulas are both accepted at Formula S 2, so acceptance
  -- carries no information. Only the two readings above distinguish them, and
  -- a Track G that freezes the weight set without stating a reading theorem
  -- for the frozen arity-one form has no mechanism left.

  both-well-formed : (Formula S 2) × (Formula S 2)
  both-well-formed = nameAtˢ zero (suc zero) , nameAtˢ (suc zero) zero

--------------------------------------------------------------------------------
-- 5. THE TELESCOPE AUDIT, rule 15, run over every K6 file
--------------------------------------------------------------------------------

-- The question, as the coordinator states it: "for every module parameter of
-- every K6 file, does an inhabitant exist at a genuine forcing extension?"
--
-- Three answers are possible and the exit ledger must keep them apart, because
-- the middle one is the whole of K6's honest headline (architecture 6.3):
--
--   (i)   INHABITED. A theorem of a lower layer. No risk.
--   (ii)  UNSUPPLIED. Not proved at this layer and not refuted at any
--         instance. O1's atom-∈ and atom-≐, O3b's image datum, Supply,
--         ext-surjective. The conclusion is conditional, not cheap.
--   (iii) FALSIFIED. An inhabitant would contradict a theorem about a genuine
--         instance. THIS is the poison rule 15 names, and the census below
--         finds NONE in K6.
--
-- THE FOUR GREPS, runnable as written from the compile root, with the counts
-- measured in this session beside them.
--
-- C1, the F3 instantiation audit of architecture 4.4, run independently here:
--
--   grep -rnE 'child-wf|WellFounded' K6/*.agda | grep -vE ':[0-9]+: *--'
--
--   MEASURED 2026-09-12, over the 24 K6 .agda files present at that moment:
--   40 lines in 16 files. EVERY ONE is either an import, a module
--   PARAMETER, or one module parameter passed to another module's parameter.
--   There is NO site in K6 where Child and child-wf are instantiated to
--   NameKernel.Kernel.Child (NameKernel.agda:368) and .child-wf (:392) by
--   name. FINDING: check F3 as written in 4.4 has zero sites inside K6 and
--   therefore passes VACUOUSLY. It protects nothing today. The obligation is
--   the CONSUMER's, at K8 or at the instance, and the exit checklist must say
--   "F3: no sites in K6, obligation forwarded" rather than "F3: 0".
--
-- C2, the rule-15 shape census. A parameter is a candidate when its type
-- mentions a HOST STRUCTURAL predicate and an EXTENSION token together:
--
--   grep -rnE '(WellFounded|\bAcc\b|isContr|Discrete|isEquiv|\bIso\b|isSurjection|\bDec\b|≃)[^-]*(∈\[|≈\[|\bNm\b|Nameᴾ|Nameᴮ|𝒮ᴾ|𝒮ᴮ|Uof|Pt B)' K6/*.agda \
--     | grep -vE ':[0-9]+: *--'
--
--   MEASURED: exactly TWO lines, both this file's own transcription of the
--   rule-15 witness, at :289 and :568, and section 2g proves it is a theorem.
--   So the census is 1 candidate, restated twice, and 0 poisons. Note
--   that Child contains none of the extension tokens, so child-wf cannot trip
--   this grep, which is why C2 and not C1 is the sound form of the check.
--
-- C3, the host-path census. A hypothesis asserting a host path between two
-- elements of the extension carrier is strictly finer than ≈[G] and is the
-- ChoiceSet defect of architecture 2.2:
--
--   grep -rnE '∥₁ *(→|->) *[A-Za-zσταξ]+ *≡ *[A-Za-zσταξ]+' K6/*.agda \
--     | grep -vE ':[0-9]+: *--'
--
--   MEASURED over K6: 0 today, because Track I has not landed. The hit is in
--   the LANDED K1 file that K6 may not edit, OrdinaryProfile.agda:119-120, and
--   section 2f is the argument. FINDING: this census must be run over the
--   PROFILE as well as over K6, or it reports clean while the defect sits one
--   layer below.
--
-- C4, the third category the other three do not see: a parameter of class
-- (ii). It is not a grep, it is the ledger of Part 6.1, and the point of
-- listing it here is that C1 to C3 all return clean for `atom-∈`. A clean
-- telescope census is NOT evidence that a field is unconditional.
--
-- THE VERDICT, by class, over every K6 .agda file present when this ran:
--
--   ground profile axioms, paths, ext          (i)   inhabited at the ground
--   entry, entry-inj, Child, child-entry,
--     isPropChild, child-wf, ∅ᴺ, ∅ᴺ-spec, acc∈ (i)   K3 theorems, blind to G
--   ‖Active‖, ≈[G], ∈[G], ∈-unfold,
--     active-child, entry-value, ≈-refl/sym,
--     ∈-congˡ, ∈-congʳ, sat-cong, Agree        (i)   K3/K5 at arbitrary G
--   IsNameᴾ, child-nameᴾ, name-introᴾ           (i)   K3, at W = carrierᶠ
--   atom-∈, atom-≐, Supply, LEM ℓ              (ii)  O1, and the ledger
--   image, image-spec, ext-surjective          (ii)  O3b, and the ledger
--   ExtAcc / ext-wf                            (i)   PROVED in section 2g
--
--   FALSIFIED: none.
--
-- TWO EXIT-CHECKLIST FAILURES FOUND WHILE RUNNING THE ABOVE, both in landed
-- K6 files that are not this track's and neither of which is edited here:
--
--   X3. `image-spec` (K6/GroundTransferAtCheck.agda:68), `imageOn`
--   (:97, :101), `StandardNames.Weighted` applied (:90) and the host-fiat
--   shape `(a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S` (:67) are all four
--   on exit item X3's zero-expected list over EVERY K6 file. They are class
--   (ii), O3b taken visibly as a hypothesis, so the disposition is a RECORDED
--   exception and not a repair; but X3 as written fails today and a reviewer
--   running it at exit will meet four hits with no ruling to point at.
--
--   X7 / clause L5. `Separated` is on the forbidden list with exactly one
--   ruled exception, AdequateDomain in Track H (ruling D10). It occurs at
--   K6/Separation.agda:175 and K6/SeparationAtStructure.agda:121. Verified by
--   grep that neither is K4/Witnesses.agda:565's record: both are a NEW module
--   of that name. So the grep fires on a name collision. The cheap fix is a
--   rename in Track F; the alternative is a second recorded exception.

--------------------------------------------------------------------------------
-- 6. TWO AUDIT PATTERNS OF THE PACKAGE ARE UNSOUND AS WRITTEN
--------------------------------------------------------------------------------

-- A control that flags a correct file is not a weaker control, it is a broken
-- one: the next reader either chases the phantom or learns to ignore the
-- pattern, and after that the pattern protects nothing. Both fixes below were
-- re-measured in this session rather than relayed.
--
-- P1. THE CHECK-NAME PATTERN. Exit item X6 and architecture 2.4 both carry
--
--     grep -cE 'chk [a-z] ≈\[G\] [a-z]'      -- expected 0
--
-- which is UNSOUND. `[a-z]` matches the leading `c` of a second `chk`, so the
-- pattern flags Bell 1.23(ii), `chk a ≈[G] chk c`, which is K5's own chk-≈ and
-- is exactly right. MEASURED over K6 in this session: 3 hits, at
-- K6/GroundTransfer.agda:345, :511 and :518, and all three are of that
-- legitimate shape. The forbidden sentence is a check name value-equal to a
-- NON-check name, so the second operand needs a guard:
--
--     grep -rnP 'chk [a-z] ≈\[G\] (?!chk)' K6/*.agda     -- MEASURED 0
--     grep -rnP '(?<!chk )[a-z] ≈\[G\] chk [a-z]' K6/*.agda  -- MEASURED 0
--
-- Use both, because the sentence is symmetric and the first pattern alone
-- misses the reversed spelling.
--
-- P2. THE IMAGE PATTERN NEEDS ITS QUALIFIER STATED. `MemberImage`,
-- `member→image`, `image-spec`, `imageOn` and `StandardNames.Weighted` are all
-- on X3's zero-expected list, and rule 14 REQUIRES the forbidden route to be
-- transcribed in prose wherever a track declines it, so raw hits are expected
-- and are not findings. Every X3 count must therefore be stated as
-- comment-stripped. The filter used throughout this file is
--
--     | grep -vE ':[0-9]+: *--'
--
-- and section 5's four X3 hits in K6/GroundTransferAtCheck.agda SURVIVE it:
-- :67 and :68 are telescope entries, :90 is a module application, :97 and :101
-- are definitions. They are code, and the finding stands.
--
-- P3. THE STATE OF K6/breaks/ AT THE TIME THIS RAN. 30 entries, of which 29
-- are parked as `.agda-break` and ONE is a live `.agda`,
-- K6/breaks/PowerHostDomain.agda. A directory-wide typecheck picks that one up
-- and fails. Exit checklist item, owned by the coordinator at package close:
-- no live `.agda` under K6/breaks/. This file's own break is already parked,
-- at K6/breaks/HostPower.agda-break.

--------------------------------------------------------------------------------
-- 7. THE RULE-15 CONTRAST, four rows, because two are not enough
--------------------------------------------------------------------------------

-- The coordinator's pair is `acc∈` against `ext-wf`, same spelling and
-- opposite status, and the pair is the right idea. The measurement in section
-- 2g adds a row and moves one, and ruling 13 says the measurement wins.
--
--  1. acc∈ : WellFounded _∈ᵗ_                      (StandardNames.agda:266)
--     The GROUND's membership. True at any transitive ground, and it is what
--     StandardNames.Weighted recurses on to BUILD chk (:319-320).
--     Class (i), inhabited.
--
--  2. child-wf : WellFounded Child                 (NameKernel.agda:392)
--     The SUBNAME relation on ground codes. Blind to carrierᶠ and to G by
--     construction (NameKernel.agda:368-369), derived from ground regularity
--     through the three ∈-steps. Class (i), inhabited.
--
--  3. ext-wf : WellFounded (λ ρ τ → ⟨ nm ρ ∈[G] nm τ ⟩) at carrier Nm
--     The EXTENSION's membership, ON NAMES. The coordinator's rule-15 message
--     places this in class (iii), "FALSE at a genuine forcing extension".
--     MEASURED OTHERWISE: section 2g proves it, from row 2 plus active-child,
--     child-nameᴾ, ∈-unfold and ∈-congʳ, with no hypothesis on G. Class (i),
--     inhabited. A `foundation` proof routed through it is indirect, not
--     vacuous.
--
--  4. the same statement at a QUOTIENT carrier.
--     THIS is the class (iii) row, and it is the one Bell's equivalence with
--     genericity is about; K5's non-claim 3 gives the transitive collapse of
--     the quotient carrier as its reason (K5/Structures.agda:507-512). No K6
--     file has a quotient carrier: `SetQuotients` measures 0 across K6, and
--     𝒮ᴾ[ G ]'s carrier is a plain Σ-type (K5/Structures.agda:263-264).
--     Class (iii), and UNOCCUPIED in K6.
--
-- So the reviewer's question is sharper than "which relation". It is: which
-- relation, AND on which carrier. Rows 3 and 4 have the same relation and
-- differ only in the carrier, and that difference is the whole of Bell's
-- theorem. Rule 15 as a principle is untouched by this and its census is worth
-- running; the census over K6 returns one candidate and no poison.
