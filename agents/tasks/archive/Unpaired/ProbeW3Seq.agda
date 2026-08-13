{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- [L3.32-T50] The W3 gate: the sequence-witness order at the first
-- non-vacuous level (untracked probe).  Settles whether the
-- tower-of-relations formulation of the internal order is expressible
-- and adequate at beta = sucV (sucV empty), without the retired cone.
-- Protocol: GHCRTS=-M10g, one process, stop-line 400, no
-- postulate/hole/TERMINATING/type-in-type; report at
-- _build/l3.32-t50-report.md.
------------------------------------------------------------------------

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeW3Seq {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isPropIsOrd )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord )
open import Cubical.HITs.CumulativeHierarchy.Constructions using
  ( ∅; ∅-empty; module InfinitySet )
open InfinitySet using ( sucV )
open import L.Rud.Step {ℓ} lem ∅ using
  ( Sset; step; step-in; step-in-self; step-in-img; step-out; StepArm
  ; arm-member; arm-self; arm-image
  ; u'; u'-in; u-self-in; u'-cases
  ; Op16; op0; op1; op2; op3; op4; op5; op6; op7
  ; op8; op9; op10; op11; op12; op13; op14; op15
  ; Fof; Fof-f1; Fof-f15; F15A-spec
  ; F15A
  ; Sset-zero; Sset-suc; Sset-in; Sset-out; Sset-mono; Sset-mem )
open import L.Rud.Order {ℓ} lem ∅ using
  ( Member; memberKey; memberKey-inj; member-trace; memberStage
  ; memberStage-in; memberStage-new; prod-stage; prod-value
  ; prod-self; prod-image; Producer; Ord; Trace; prod-mem
  ; StageBounded; Earlier; SelfAt; isPropStageBounded
  ; leastTrace; leastTrace-least; leastTrace-value; traceTri
  ; Sset-below; _⊰_; _≺_; opIx; opSWO )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( Tri; lt; eq; gt; SWO )
open import Cubical.HITs.CumulativeHierarchy.Properties using
  ( ⟪_⟫; ⟪_⟫↪; _∈ₛ_; ∈∈ₛ; ∈ₛ⟪_⟫↪_; _≡ₕ_; _⊆_; extensionality; ∈-asFiber )
open import V.Model {ℓ} using ( ∈sucV-elim; self∈sucV )
open import V.Hierarchy {ℓ} using ( ∈-irrefl )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import L.Rud.Ops {ℓ} using ( F1; F1-spec )
open import Cubical.Data.Nat.Order using ( _<_ )
open import Cubical.Data.Sigma using ( _×_; _,_; Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( Unit*; tt* )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

------------------------------------------------------------------------
-- STEP 0 (D-10 truth check).  T48 records that the level membership at
-- sucV (sucV ∅) is a finite enumeration of 17 values.  Two readings are
-- measured: (a) the members of the PREVIOUS level Sset (sucV ∅), the
-- old members at beta (17 slots); (b) the members of the level itself
-- Sset (sucV (sucV ∅)), the carrier the last relation ranges over.
------------------------------------------------------------------------

module Step0 where

  γ : V ℓ
  γ = sucV ∅

  β : V ℓ
  β = sucV γ

  ordγ : IsOrd γ
  ordγ = suc-ord ∅-ord

  ordβ : IsOrd β
  ordβ = suc-ord ordγ

  -- Reading (a): the 17-slot enumeration of Mem (Sset γ).
  oldVal : Op16 → V ℓ
  oldVal i = Fof i ∅ ∅

  ∅∈Sγ : ⟨ ∅ ∈ˢ Sset γ ⟩
  ∅∈Sγ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym (Sset-suc ∅))
          (subst (λ w → ⟨ ∅ ∈ˢ step w ⟩) (sym Sset-zero) (step-in-self ∅))

  img∈Sγ : (i : Op16) → ⟨ oldVal i ∈ˢ Sset γ ⟩
  img∈Sγ i = subst (λ w → ⟨ oldVal i ∈ˢ w ⟩) (sym (Sset-suc ∅))
              (subst (λ w → ⟨ oldVal i ∈ˢ step w ⟩) (sym Sset-zero)
                (step-in-img ∅ (oldVal i) i ∅ ∅ (u-self-in ∅) (u-self-in ∅) refl))

  oldGoal : V ℓ → Type (ℓ-suc ℓ)
  oldGoal x = ∥ (x ≡ ∅) ⊎ (Σ[ i ∈ Op16 ] x ≡ Fof i ∅ ∅) ∥₁

  -- Completeness: every member of Sset γ is one of the 17 slots.
  oldArm : (x : V ℓ) → StepArm ∅ x → oldGoal x
  oldArm x (arm-member x∈∅) =
    Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst x∈∅))
  oldArm x (arm-self x≡∅) = ∣ inl x≡∅ ∣₁
  oldArm x (arm-image i a b a∈∅ b∈∅ x≡) = go₁ a∈∅
    where
    go₁ : (⟨ a ∈ˢ ∅ ⟩ ⊎ (a ≡ ∅)) → oldGoal x
    go₁ (inl h) = Empty.rec (∅-empty a (∈∈ₛ {a = a} {b = ∅} .fst h))
    go₁ (inr a≡∅) = go₂ b∈∅
      where
      go₂ : (⟨ b ∈ˢ ∅ ⟩ ⊎ (b ≡ ∅)) → oldGoal x
      go₂ (inl h) = Empty.rec (∅-empty b (∈∈ₛ {a = b} {b = ∅} .fst h))
      go₂ (inr b≡∅) =
        ∣ inr (i , subst (λ t → x ≡ t) (cong₂ (Fof i) a≡∅ b≡∅) x≡) ∣₁

  oldCover : (x : V ℓ) → ⟨ x ∈ˢ Sset γ ⟩ → oldGoal x
  oldCover x h = PT.rec squash₁ oldStep (Sset-out γ x h)
    where
    oldStep : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ γ ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → oldGoal x
    oldStep (δ , δ∈γ , x∈stepSδ) =
      ∈sucV-elim {A = ∅} {x = δ} (squash₁) δ∈γ
        (λ δ∈∅ → Empty.rec
          (∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈∅)))
        (λ δ≡∅ → PT.rec squash₁ (oldArm x)
           (step-out ∅ x (subst (λ w → ⟨ x ∈ˢ step w ⟩) (Sset-zero)
              (subst (λ s → ⟨ x ∈ˢ step (Sset s) ⟩) δ≡∅ x∈stepSδ))))

  -- Reading (b): the members of the level itself, Sset β = step (Sset
  -- γ): the old members (17), the level itself (1), and the images over
  -- u' (Sset γ) (16 x 18 x 18 = 5184).  Total: 5202 slots.
  Uγ : V ℓ
  Uγ = u' (Sset γ)

  topArmData : V ℓ → Type (ℓ-suc ℓ)
  topArmData x = Σ[ i ∈ Op16 ] Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                  ((⟨ a ∈ˢ Uγ ⟩ × ⟨ b ∈ˢ Uγ ⟩) × (x ≡ Fof i a b))

  topGoal : V ℓ → Type (ℓ-suc ℓ)
  topGoal x = ∥ ⟨ x ∈ˢ Sset γ ⟩ ⊎ ((x ≡ Sset γ) ⊎ topArmData x) ∥₁

  u'-both : (u a : V ℓ) → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → ⟨ a ∈ˢ u' u ⟩
  u'-both u a (inl a∈u) = u'-in u a a∈u
  u'-both u a (inr a≡u) = subst (λ w → ⟨ w ∈ˢ u' u ⟩) (sym a≡u) (u-self-in u)

  topArm : (x : V ℓ) → StepArm (Sset γ) x → topGoal x
  topArm x (arm-member x∈Sγ) = ∣ inl x∈Sγ ∣₁
  topArm x (arm-self x≡Sγ) = ∣ inr (inl x≡Sγ) ∣₁
  topArm x (arm-image i a b aS bS x≡) =
    ∣ inr (inr (i , a , b , ((u'-both (Sset γ) a aS , u'-both (Sset γ) b bS) , x≡))) ∣₁

  topCover : (x : V ℓ) → ⟨ x ∈ˢ Sset β ⟩ → topGoal x
  topCover x h = PT.rec squash₁ topStep (Sset-out β x h)
    where
    topStep : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ β ⟩ × ⟨ x ∈ˢ step (Sset δ) ⟩) → topGoal x
    topStep (δ , δ∈β , x∈stepSδ) =
      ∈sucV-elim {A = γ} {x = δ} (squash₁) δ∈β
        (λ δ∈γ → ∈sucV-elim {A = ∅} {x = δ} (squash₁) δ∈γ
          (λ δ∈∅ → Empty.rec
            (∅-empty δ (∈∈ₛ {a = δ} {b = ∅} .fst δ∈∅)))
          (λ δ≡∅ → ∣ inl (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Sset-suc ∅))
                     (subst (λ s → ⟨ x ∈ˢ step (Sset s) ⟩) δ≡∅ x∈stepSδ)) ∣₁))
        (λ δ≡γ → PT.rec squash₁ (topArm x)
           (step-out (Sset γ) x
             (subst (λ s → ⟨ x ∈ˢ step (Sset s) ⟩) δ≡γ x∈stepSδ)))

  -- Distinctness, partially: Fof op1 ∅ ∅ = ∅ = Fof op15 ∅ ∅ (F15 is the
  -- relativization slot; the plain trunk instantiates A as ∅), so the
  -- distinct count is at most 15.
  F1∅-ext : F1 ∅ ∅ ≡ ∅
  F1∅-ext = extensionality (F1 ∅ ∅) ∅ (sub , sup)
    where
    sub : ⟨ F1 ∅ ∅ ⊆ ∅ ⟩
    sub x x∈ = Empty.rec (∅-empty x
      (∈∈ₛ {a = x} {b = ∅} .fst (F1-spec ∅ ∅ x .fst
        (∈∈ₛ {a = x} {b = F1 ∅ ∅} .snd x∈) .fst)))
    sup : ⟨ ∅ ⊆ F1 ∅ ∅ ⟩
    sup x x∈∅ = Empty.rec (∅-empty x x∈∅)

  F1∅∅ : Fof op1 ∅ ∅ ≡ ∅
  F1∅∅ = Fof-f1 ∅ ∅ ∙ F1∅-ext

  F15A∅-ext : F15A ∅ ≡ ∅
  F15A∅-ext = extensionality (F15A ∅) ∅ (sub , sup)
    where
    sub : ⟨ F15A ∅ ⊆ ∅ ⟩
    sub x x∈ = Empty.rec (∅-empty x
      (∈∈ₛ {a = x} {b = ∅} .fst
        (F15A-spec ∅ x (∈∈ₛ {a = x} {b = F15A ∅} .snd x∈))))
    sup : ⟨ ∅ ⊆ F15A ∅ ⟩
    sup x x∈∅ = Empty.rec (∅-empty x x∈∅)

  F15∅∅ : Fof op15 ∅ ∅ ≡ ∅
  F15∅∅ = Fof-f15 ∅ ∅ ∙ F15A∅-ext

  distinct : Fof op1 ∅ ∅ ≡ Fof op15 ∅ ∅
  distinct = F1∅∅ ∙ sym F15∅∅

------------------------------------------------------------------------
-- STEP 2 CONTENT: the flattening lemma at the top step (the gate's
-- real question at the content level).  The producer lex at the top
-- step compares the KEY producers of the two fresh members, descending
-- into their argument producers; the flattening replaces that descent
-- by the atomic read in the EARLIER entry: p ≺ q read as the pair
-- membership pr (value p) (value q) ∈ r₁, with the self boundary.  The
-- lemma checks that substitution: for the parameters of a top-step
-- producer, p ≺ q ⟺ the flattened read, whose right side carries no
-- producer recursion at all.
------------------------------------------------------------------------

module Flatten where
  open Step0

  -- The producer of a parameter of a top-step image: the key at level
  -- γ for an old member (its stage is a member of γ), the self
  -- producer for the level itself.
  parKey : (a : V ℓ) → (⟨ a ∈ˢ Sset γ ⟩ ⊎ (a ≡ Sset γ)) → Producer
  parKey a (inl a∈) = memberKey γ ordγ (a , a∈) .fst
  parKey a (inr a≡) = prod-self (γ , ordγ)

  -- The flattened argument comparison, read at the relation level: the
  -- pair-membership content of "pr a c ∈ r₁" is Sset-below at γ when
  -- both parameters are old (r₁ is the order at γ), and the self
  -- boundary is "an old parameter precedes the level itself".
  argcmp : (a c : V ℓ)
         → (⟨ a ∈ˢ Sset γ ⟩ ⊎ (a ≡ Sset γ))
         → (⟨ c ∈ˢ Sset γ ⟩ ⊎ (c ≡ Sset γ))
         → Type (ℓ-suc ℓ)
  argcmp a c (inl a∈) (inl c∈) = Sset-below γ ordγ (a , a∈) (c , c∈)
  argcmp a c (inl a∈) (inr c≡) = Unit* {ℓ-suc ℓ}
  argcmp a c (inr a≡) (inl c∈) = ⊥* {ℓ-suc ℓ}
  argcmp a c (inr a≡) (inr c≡) = ⊥* {ℓ-suc ℓ}

  -- The key of an old member sits at a stage inside γ, so it precedes
  -- the self producer of γ.
  old-below-self : (a : V ℓ) (a∈ : ⟨ a ∈ˢ Sset γ ⟩)
                 → memberKey γ ordγ (a , a∈) .fst ≺ prod-self (γ , ordγ)
  old-below-self a a∈ = pshape (memberKey γ ordγ (a , a∈) .fst)
                          (memberStage-in γ ordγ (a , a∈))
    where
    pshape : (p : Producer) → ⟨ prod-stage p .fst ∈ˢ γ ⟩
           → p ≺ prod-self (γ , ordγ)
    pshape (prod-self δ) h = h
    pshape (prod-image δ i p q) h = h

  -- The self producer of γ precedes no old member: its stage is γ,
  -- which is not a member of any stage inside γ.
  self-not-below-old : (c : V ℓ) (c∈ : ⟨ c ∈ˢ Sset γ ⟩)
                     → prod-self (γ , ordγ) ≺ memberKey γ ordγ (c , c∈) .fst
                     → Empty.⊥
  self-not-below-old c c∈ = pshape (memberKey γ ordγ (c , c∈) .fst)
                             (memberStage-in γ ordγ (c , c∈))
    where
    pshape : (p : Producer) → ⟨ prod-stage p .fst ∈ˢ γ ⟩
           → prod-self (γ , ordγ) ≺ p → Empty.⊥
    pshape (prod-self δ) h e = ∈-irrefl γ (ordγ .fst {x = δ .fst} {y = γ} e h)
    pshape (prod-image δ i p q) h (inl e) = ∈-irrefl γ (ordγ .fst {x = δ .fst} {y = γ} e h)
    pshape (prod-image δ i p q) h (inr e) =
      ∈-irrefl γ (subst (λ z → ⟨ z ∈ˢ γ ⟩) (sym (cong (λ d → d .fst) e)) h)

  -- The flattening lemma: for parameters a, c of a top-step producer,
  -- the producer comparison is exactly the flattened read.  The four
  -- cases are the two old-old pair (definitional, by the pullback that
  -- defines Sset-below) and the three self-boundary cases.
  flatten : (a c : V ℓ)
          → (sa : ⟨ a ∈ˢ Sset γ ⟩ ⊎ (a ≡ Sset γ))
          → (sc : ⟨ c ∈ˢ Sset γ ⟩ ⊎ (c ≡ Sset γ))
          → (parKey a sa ≺ parKey c sc) ⟷ argcmp a c sa sc
  flatten a c (inl a∈) (inl c∈) = (λ h → h) , (λ h → h)
  flatten a c (inl a∈) (inr c≡) = (λ _ → tt*) , λ _ → old-below-self a a∈
  flatten a c (inr a≡) (inl c∈) = (λ h → lift (self-not-below-old c c∈ h)) , λ h → Empty.rec* h
  flatten a c (inr a≡) (inr c≡) = (λ h → lift (∈-irrefl γ h)) , λ h → Empty.rec* h

------------------------------------------------------------------------
-- STEP 2 CONTENT, continued: the op-leastness decode against the key
-- (T22's content, kept at x3, written but never checked).  At the
-- non-vacuous level the conjuncts are: x is Fof i of parameters in
-- u' (Sset γ) and x is produced by no smaller operation.  The theorem
-- decodes them: the key of a fresh, non-self member of Sset β is an
-- image producer at stage γ with op index i.  The argument-part of the
-- decode (the key's parameters are the keys of a and b) is the residue.
------------------------------------------------------------------------

module Decode where
  open Step0
  open Flatten

  -- A parameter of a top-step image, as a trace: the key at level γ
  -- for an old member, the self producer for the level itself.
  parTrace : (a : V ℓ) → (⟨ a ∈ˢ Sset γ ⟩ ⊎ (a ≡ Sset γ)) → Trace
  parTrace a (inl a∈) = memberKey γ ordγ (a , a∈)
  parTrace a (inr a≡) = (prod-self (γ , ordγ) , tt*)

  parVal : (a : V ℓ) (sa : ⟨ a ∈ˢ Sset γ ⟩ ⊎ (a ≡ Sset γ))
         → prod-value (parTrace a sa .fst) ≡ a
  parVal a (inl a∈) = leastTrace-value a (member-trace γ ordγ (a , a∈))
  parVal a (inr a≡) = sym a≡

  -- The stage bound of a parameter trace: stage-bounded and earlier
  -- than the top stage.
  parB : (a : V ℓ) (sa : ⟨ a ∈ˢ Sset γ ⟩ ⊎ (a ≡ Sset γ))
       → StageBounded (parTrace a sa .fst) × Earlier (γ , ordγ) (parTrace a sa .fst)
  parB a (inl a∈) = memberKey γ ordγ (a , a∈) .snd , inl (memberStage-in γ ordγ (a , a∈))
  parB a (inr a≡) = tt* , inr refl

  -- The parameter split of a key argument, read off its stage bound.
  splitOf : (p : Producer) (w : StageBounded p) → Earlier (γ , ordγ) p
          → ⟨ prod-value p ∈ˢ Sset γ ⟩ ⊎ (prod-value p ≡ Sset γ)
  splitOf p w (inl h) = inl (prod-mem γ ordγ p w h)
  splitOf (prod-self δ) w (inr e) = inr (cong (λ d → Sset (d .fst)) e)
  splitOf (prod-image δ i p q) w (inr e) = Empty.rec* e

  -- The key decomposition at β (T22's cured shape: the case analysis
  -- runs on the key as data through a named helper, never `with`-cased
  -- on the transparent least-witness term).
  data KeyShape : Type (ℓ-suc ℓ) where
    kself : Ord → KeyShape
    kimg  : Ord → Op16 → Producer → Producer → KeyShape

  keyBack : (m : Member β) → Trace → KeyShape → Type (ℓ-suc ℓ)
  keyBack m t (kself δ) = memberKey β ordβ m ≡ (prod-self δ , tt*)
  keyBack m t (kimg δ i p q) =
    Σ[ w ∈ StageBounded (prod-image δ i p q) ]
      (memberKey β ordβ m ≡ (prod-image δ i p q , w))

  keyDecomp : (m : Member β) → Σ[ s ∈ KeyShape ] keyBack m (memberKey β ordβ m) s
  keyDecomp m = go (memberKey β ordβ m) refl
    where
    go : (t : Trace) → memberKey β ordβ m ≡ t
       → Σ[ s ∈ KeyShape ] keyBack m t s
    go (prod-self δ , w) e = kself δ , e
    go (prod-image δ i p q , w) e = kimg δ i p q , (w , e)

  keyStageβ : (m : Member β) (fresh : ⟨ m .fst ∈ˢ Sset γ ⟩ → Empty.⊥)
            → prod-stage (memberKey β ordβ m .fst) ≡ (γ , ordγ)
  keyStageβ m fresh = Σ≡Prop isPropIsOrd (memberStage-new γ ordγ m fresh)

  -- The producer of a trace (a named helper, I-5: written type, so the
  -- elaboration runs once instead of once per constraint).
  traceFst : Trace → Producer
  traceFst t = t .fst

  module OpDecode (x : V ℓ) (hx : ⟨ x ∈ˢ Sset β ⟩)
                  (fresh : ⟨ x ∈ˢ Sset γ ⟩ → Empty.⊥)
                  (nself : x ≡ Sset γ → Empty.⊥)
                  (i : Op16) (a b : V ℓ)
                  (sa : ⟨ a ∈ˢ Sset γ ⟩ ⊎ (a ≡ Sset γ))
                  (sb : ⟨ b ∈ˢ Sset γ ⟩ ⊎ (b ≡ Sset γ))
                  (x≡ : x ≡ Fof i a b)
                  (noOp : (k : Op16) → opIx k < opIx i → (a' b' : V ℓ)
                        → (sa' : ⟨ a' ∈ˢ Sset γ ⟩ ⊎ (a' ≡ Sset γ))
                        → (sb' : ⟨ b' ∈ˢ Sset γ ⟩ ⊎ (b' ≡ Sset γ))
                        → x ≡ Fof k a' b' → Empty.⊥) where

    m : Member β
    m = x , hx

    -- The representation of x at the stated operation, as a trace.
    rep : Trace
    rep = ( prod-image (γ , ordγ) i (parTrace a sa .fst) (parTrace b sb .fst)
          , ((parB a sa .fst , parB a sa .snd) , (parB b sb .fst , parB b sb .snd)) )

    repVal : prod-value (rep .fst) ≡ x
    repVal = cong₂ (Fof i) (parVal a sa) (parVal b sb) ∙ sym x≡

    opOf : Producer → Op16
    opOf (prod-self _) = op0
    opOf (prod-image _ j p q) = j

    -- The key is an image producer at stage γ with op index i.
    keyImg : Σ[ p ∈ Producer ] Σ[ q ∈ Producer ]
               Σ[ w ∈ StageBounded (prod-image (γ , ordγ) i p q) ]
               (memberKey β ordβ m ≡ (prod-image (γ , ordγ) i p q , w))
    keyImg = go (keyDecomp m)
      where
      go : Σ[ s ∈ KeyShape ] keyBack m (memberKey β ordβ m) s
         → Σ[ p ∈ Producer ] Σ[ q ∈ Producer ]
               Σ[ w ∈ StageBounded (prod-image (γ , ordγ) i p q) ]
               (memberKey β ordβ m ≡ (prod-image (γ , ordγ) i p q , w))
      go (kself δ , e) = Empty.rec (nself selfVal)
        where
        δγ : δ ≡ (γ , ordγ)
        δγ = sym (cong (λ t → prod-stage (t .fst)) e) ∙ keyStageβ m fresh
        selfVal : x ≡ Sset γ
        selfVal = sym (leastTrace-value x (member-trace β ordβ m))
          ∙ cong (λ t → prod-value (t .fst)) e
          ∙ cong (λ d → Sset (d .fst)) δγ
      go (kimg δ j p q , (w , e)) = p , q , w' , path
        where
        δγ : δ ≡ (γ , ordγ)
        δγ = sym (cong (λ t → prod-stage (t .fst)) e) ∙ keyStageβ m fresh
        keyFst : Producer
        keyFst = memberKey β ordβ m .fst
        γOrd : Ord
        γOrd = γ , ordγ
        ke : keyFst ≡ prod-image γOrd j p q
        ke = cong traceFst e
          ∙ subst (λ (d : Ord) → prod-image δ j p q ≡ prod-image d j p q) δγ refl
        kv : x ≡ Fof j (prod-value p) (prod-value q)
        kv = sym (leastTrace-value x (member-trace β ordβ m))
          ∙ cong prod-value ke
        p' : Producer
        p' = parTrace a sa .fst
        q' : Producer
        q' = parTrace b sb .fst
        ep' : Earlier (γ , ordγ) p
        ep' = subst (λ d → Earlier d p) δγ (w .fst .snd)
        eq' : Earlier (γ , ordγ) q
        eq' = subst (λ d → Earlier d q) δγ (w .snd .snd)
        sp : ⟨ prod-value p ∈ˢ Sset γ ⟩ ⊎ (prod-value p ≡ Sset γ)
        sp = splitOf p (w .fst .fst) ep'
        sq : ⟨ prod-value q ∈ˢ Sset γ ⟩ ⊎ (prod-value q ≡ Sset γ)
        sq = splitOf q (w .snd .fst) eq'
        ji : j ≡ i
        ji = triCase (traceTri (memberKey β ordβ m) rep)
          where
          fromLt : memberKey β ordβ m ⊰ rep → j ≡ i
          fromLt h = cmpCase (subst (λ t → t ≺ rep .fst) ke h)
            where
            cmpCase : prod-image (γ , ordγ) j p q ≺ prod-image (γ , ordγ) i p' q'
                    → j ≡ i
            cmpCase (inl eγ) = Empty.rec (∈-irrefl γ eγ)
            cmpCase (inr (_ , cmp)) = opCase cmp
              where
              opCase : SWO._<∙_ opSWO j i
                     ⊎ ((j ≡ i) × ((p ≺ p') ⊎ ((p ≡ p') × (q ≺ q'))))
                     → j ≡ i
              opCase (inl jlti) =
                Empty.rec (noOp j (lower jlti) (prod-value p) (prod-value q) sp sq kv)
              opCase (inr (je , _)) = je
          fromEq : memberKey β ordβ m ≡ rep → j ≡ i
          fromEq e' = cong opOf (sym ke ∙ cong (λ t → t .fst) e')
          triCase : Tri (memberKey β ordβ m ⊰ rep)
                         (memberKey β ordβ m ≡ rep)
                         (rep ⊰ memberKey β ordβ m)
                 → j ≡ i
          triCase (lt h) = fromLt h
          triCase (eq e') = fromEq e'
          triCase (gt h) = Empty.rec
            (leastTrace-least x (member-trace β ordβ m) rep repVal h)
        w' : StageBounded (prod-image (γ , ordγ) i p q)
        w' = subst (λ d → StageBounded (prod-image d i p q)) δγ
               (subst (λ k → StageBounded (prod-image δ k p q)) ji w)
        pp : prod-image δ j p q ≡ prod-image (γ , ordγ) i p q
        pp = λ k → prod-image (δγ k) (ji k) p q
        pair-path : (prod-image δ j p q , w) ≡ (prod-image (γ , ordγ) i p q , w')
        pair-path = Σ≡Prop isPropStageBounded pp
        path : memberKey β ordβ m ≡ (prod-image (γ , ordγ) i p q , w')
        path = e ∙ pair-path
