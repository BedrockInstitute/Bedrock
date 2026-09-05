{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T145] Gate the graph-layer supply: what below-lim needs from the
-- retired StepInL.  Untracked probe, no master, no git, zero retiring
-- imports.  The three roles are stated exactly as the below-lim consumers
-- use them (values∈L StepInL:370-371; stepSet∈L :2419-2422; the op graphs
-- :2139-2160 with the Clause layer, StepStory:79-103).  The probe proves
-- the assembly from stated obligations whose delivered inhabitants live
-- in the archived StepInL.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V )

module ProbeT145 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using
  ( Lset; 𝒟ₒ; 𝒟ₒ-intro; isTransV )
open import L.Definability {ℓ} using ( module DefOf )
open import L.LevelKit {ℓ} using ( module LevelKit )
open import L.Rud.Step {ℓ} lem A using
  ( Op16; op0; op1; op2; op3; op4; op5; op6; op7; op8; op9; op10; op11
  ; op12; op13; op14; op15; Fof; step )
open import L.Rud.Bridge {ℓ} lem A using
  ( Ltr; 𝒟ₒ⊆Lsuc; ValuesInU; suc⁴; ext-⊆ )
open import L.InitialSegment {ℓ} using ( _⟷_ )
open import Cubical.Data.FinData.Base using ( Fin )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Sum using ( _⊎_; inl; inr; rec )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ⟪_⟫; ⟪_⟫↪; ∈-asFiber )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

private
  f0 : {n : ℕ} → Fin (suc n)
  f0 = zero
  f1 : {n : ℕ} → Fin (suc (suc n))
  f1 = suc f0
  f2 : {n : ℕ} → Fin (suc (suc (suc n)))
  f2 = suc f1

-- ==== Role 1: values∈L (StepInL:370-371). ====

-- Obligation A, the values lex: the sixteen value-membership clauses.
-- Delivered: `Values.valueMem` (StepInL:205-330, 125 in-fence lines), fed
-- by `values∈L`'s stage dance (StepInL:367-431, 62 in-fence lines).
record ValuesLex : Type (ℓ-suc ℓ) where
  field
    vm : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩
       → (i : Op16) (a b : S) → (⟨ a ∈ˢ u ⟩ ⊎ (a ≡ u)) → (⟨ b ∈ˢ u ⟩ ⊎ (b ≡ u))
       → (v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ Lset (suc⁴ ζ) ⟩

-- The role closes definitionally once the lex is given.
values∈L : ValuesLex → (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ValuesInU u (suc⁴ ζ)
values∈L lex = ValuesLex.vm lex

-- ==== Role 3: the op graphs, at the Clause telescope's layer shape. ====

-- The layer at a generic transitive carrier, exactly the archived `Slot`'s
-- telescope (StepInL:1117-1122).
module Layer (C : S) (Ctr : isTransV C) (mA : ⟪ C ⟫) (qA : ⟪ C ⟫↪ mA ≡ A)
             (∅∈C : ⟨ ∅ ∈ˢ C ⟩) where

  module K = LevelKit C Ctr
  open K public

  -- The equality frame, fresh (the archive's Desc:710-736, 27 in-fence
  -- lines), closed over survivors (`ext-⊆`, `PK.pt`, `PK.entry∈`, `Ctr`).
  eqFrame : {n : ℕ} → Fin n → Formula ⟪ C ⟫ (suc n) → Formula ⟪ C ⟫ n
  eqFrame k M = (∀̇∈ (var k) M) ∧̇ (∀̇ (M ⇒̇ (var f0 ∈̇ var (suc k))))

  eqFrame-out : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
                (δ : Vec SM n) (W : S)
              → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩ → ⟨ v ∈ˢ W ⟩)
              → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩ → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩)
              → ⟨ δ ⊨ᵐ eqFrame k M ⟩ → fst (lookup k δ) ≡ W
  eqFrame-out k M δ W wsub mout min (h₁ , h₂) = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ fst (lookup k δ) ⟩ → ⟨ x ∈ˢ W ⟩
    sub x h = mout x (PK.entry∈ k δ x h) (h₁ (PK.pt x (PK.entry∈ k δ x h)) h)
    sup : (x : S) → ⟨ x ∈ˢ W ⟩ → ⟨ x ∈ˢ fst (lookup k δ) ⟩
    sup x h = h₂ (PK.pt x (wsub x h)) (min x (wsub x h) h)

  eqFrame-in : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
               (δ : Vec SM n) (W : S)
             → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩ → ⟨ v ∈ˢ W ⟩)
             → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩ → ⟨ (PK.pt v v∈ ∷ δ) ⊨ᵐ M ⟩)
             → fst (lookup k δ) ≡ W → ⟨ δ ⊨ᵐ eqFrame k M ⟩
  eqFrame-in k M δ W wsub mout min e = (part₁ , part₂)
    where
    part₁ : (xm : SM) → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩ → ⟨ (xm ∷ δ) ⊨ᵐ M ⟩
    part₁ xm h = min (fst xm) (snd xm) (subst (λ t → ⟨ fst xm ∈ˢ t ⟩) e h)
    part₂ : (xm : SM) → ⟨ (xm ∷ δ) ⊨ᵐ M ⟩ → ⟨ fst xm ∈ˢ fst (lookup k δ) ⟩
    part₂ xm h = subst (λ t → ⟨ fst xm ∈ˢ t ⟩) (sym e)
      (mout (fst xm) (snd xm) h)

  -- Obligation B: the sixteen membership formulas and their 32 two-way
  -- decodes.  Delivered: formulas StepInL:1153-1170 (18 in-fence lines),
  -- decodes :1183-2100 (868), dispatchers :2101-2138 (36).  The decodes'
  -- cone includes the projection/slice frames (`leftMem`, `rightMem`,
  -- `sliceMem`, Desc:781-838 and Frames:845-1115, about 210), StepInL's
  -- own, over the surviving specs and pair atoms.
  module Graphs (memOf : Op16 → Formula ⟪ C ⟫ 4)
                (memOut : (i : Op16) (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩)
                          (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩)
                        → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                            ⊨ᵐ memOf i ⟩ → ⟨ z ∈ˢ Fof i a b ⟩)
                (memIn : (i : Op16) (z b a y : S) (z∈ : ⟨ z ∈ˢ C ⟩)
                         (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩) (y∈ : ⟨ y ∈ˢ C ⟩)
                       → ⟨ z ∈ˢ Fof i a b ⟩
                       → ⟨ (PK.pt z z∈ ∷ PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ [])
                           ⊨ᵐ memOf i ⟩) where

    graphOf : Op16 → Formula ⟪ C ⟫ 3
    graphOf i = eqFrame f2 (memOf i)

    graph-out : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
                (y∈ : ⟨ y ∈ˢ C ⟩)
              → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
              → ⟨ (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ graphOf i ⟩
              → y ≡ Fof i a b
    graph-out i b a y b∈ a∈ y∈ sub h = eqFrame-out f2 (memOf i)
      (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) (Fof i a b) sub
      (λ v v∈ k → memOut i v b a y v∈ b∈ a∈ y∈ k)
      (λ v v∈ k → memIn i v b a y v∈ b∈ a∈ y∈ k) h

    graph-in : (i : Op16) (b a y : S) (b∈ : ⟨ b ∈ˢ C ⟩) (a∈ : ⟨ a ∈ˢ C ⟩)
               (y∈ : ⟨ y ∈ˢ C ⟩)
             → ((v : S) → ⟨ v ∈ˢ Fof i a b ⟩ → ⟨ v ∈ˢ C ⟩)
             → y ≡ Fof i a b
             → ⟨ (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) ⊨ᵐ graphOf i ⟩
    graph-in i b a y b∈ a∈ y∈ sub e = eqFrame-in f2 (memOf i)
      (PK.pt b b∈ ∷ PK.pt a a∈ ∷ PK.pt y y∈ ∷ []) (Fof i a b) sub
      (λ v v∈ k → memOut i v b a y v∈ b∈ a∈ y∈ k)
      (λ v v∈ k → memIn i v b a y v∈ b∈ a∈ y∈ k) e

    orTail0 orTail1 orTail2 orTail3 orTail4 orTail5 orTail6 orTail7
      orTail8 orTail9 orTail10 orTail11 orTail12 orTail13 orTail14 orTail15 :
      Formula ⟪ C ⟫ 3
    orTail0 = graphOf op0 ∨̇ orTail1
    orTail1 = graphOf op1 ∨̇ orTail2
    orTail2 = graphOf op2 ∨̇ orTail3
    orTail3 = graphOf op3 ∨̇ orTail4
    orTail4 = graphOf op4 ∨̇ orTail5
    orTail5 = graphOf op5 ∨̇ orTail6
    orTail6 = graphOf op6 ∨̇ orTail7
    orTail7 = graphOf op7 ∨̇ orTail8
    orTail8 = graphOf op8 ∨̇ orTail9
    orTail9 = graphOf op9 ∨̇ orTail10
    orTail10 = graphOf op10 ∨̇ orTail11
    orTail11 = graphOf op11 ∨̇ orTail12
    orTail12 = graphOf op12 ∨̇ orTail13
    orTail13 = graphOf op13 ∨̇ orTail14
    orTail14 = graphOf op14 ∨̇ orTail15
    orTail15 = graphOf op15

    bigOr : Formula ⟪ C ⟫ 3
    bigOr = orTail0

    bigOr-in : (i : Op16) (δ : Vec SM 3) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ δ ⊨ᵐ bigOr ⟩
    bigOr-in op0 δ h = ∣ inl h ∣₁
    bigOr-in op1 δ h = ∣ inr ∣ inl h ∣₁ ∣₁
    bigOr-in op2 δ h = ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁
    bigOr-in op3 δ h = ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op4 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op5 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op6 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op7 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op8 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op9 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op10 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op11 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op12 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op13 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op14 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inl h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁
    bigOr-in op15 δ h = ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr ∣ inr h ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁ ∣₁

    orStep : (φ ψ : Formula ⟪ C ⟫ 3) (δ : Vec SM 3) (R : hProp (ℓ-suc ℓ))
           → (⟨ δ ⊨ᵐ φ ⟩ → ⟨ R ⟩) → (⟨ δ ⊨ᵐ ψ ⟩ → ⟨ R ⟩)
           → ⟨ δ ⊨ᵐ (φ ∨̇ ψ) ⟩ → ⟨ R ⟩
    orStep φ ψ δ R f g = PT.rec (snd R) (rec f g)

    bigOr-out : (δ : Vec SM 3) (R : hProp (ℓ-suc ℓ))
              → ((i : Op16) → ⟨ δ ⊨ᵐ graphOf i ⟩ → ⟨ R ⟩)
              → ⟨ δ ⊨ᵐ bigOr ⟩ → ⟨ R ⟩
    bigOr-out δ R k = go0
      where
      go15 : ⟨ δ ⊨ᵐ orTail15 ⟩ → ⟨ R ⟩
      go15 = k op15
      go14 : ⟨ δ ⊨ᵐ orTail14 ⟩ → ⟨ R ⟩
      go14 h = orStep (graphOf op14) orTail15 δ R (k op14) go15 h
      go13 : ⟨ δ ⊨ᵐ orTail13 ⟩ → ⟨ R ⟩
      go13 h = orStep (graphOf op13) orTail14 δ R (k op13) go14 h
      go12 : ⟨ δ ⊨ᵐ orTail12 ⟩ → ⟨ R ⟩
      go12 h = orStep (graphOf op12) orTail13 δ R (k op12) go13 h
      go11 : ⟨ δ ⊨ᵐ orTail11 ⟩ → ⟨ R ⟩
      go11 h = orStep (graphOf op11) orTail12 δ R (k op11) go12 h
      go10 : ⟨ δ ⊨ᵐ orTail10 ⟩ → ⟨ R ⟩
      go10 h = orStep (graphOf op10) orTail11 δ R (k op10) go11 h
      go9 : ⟨ δ ⊨ᵐ orTail9 ⟩ → ⟨ R ⟩
      go9 h = orStep (graphOf op9) orTail10 δ R (k op9) go10 h
      go8 : ⟨ δ ⊨ᵐ orTail8 ⟩ → ⟨ R ⟩
      go8 h = orStep (graphOf op8) orTail9 δ R (k op8) go9 h
      go7 : ⟨ δ ⊨ᵐ orTail7 ⟩ → ⟨ R ⟩
      go7 h = orStep (graphOf op7) orTail8 δ R (k op7) go8 h
      go6 : ⟨ δ ⊨ᵐ orTail6 ⟩ → ⟨ R ⟩
      go6 h = orStep (graphOf op6) orTail7 δ R (k op6) go7 h
      go5 : ⟨ δ ⊨ᵐ orTail5 ⟩ → ⟨ R ⟩
      go5 h = orStep (graphOf op5) orTail6 δ R (k op5) go6 h
      go4 : ⟨ δ ⊨ᵐ orTail4 ⟩ → ⟨ R ⟩
      go4 h = orStep (graphOf op4) orTail5 δ R (k op4) go5 h
      go3 : ⟨ δ ⊨ᵐ orTail3 ⟩ → ⟨ R ⟩
      go3 h = orStep (graphOf op3) orTail4 δ R (k op3) go4 h
      go2 : ⟨ δ ⊨ᵐ orTail2 ⟩ → ⟨ R ⟩
      go2 h = orStep (graphOf op2) orTail3 δ R (k op2) go3 h
      go1 : ⟨ δ ⊨ᵐ orTail1 ⟩ → ⟨ R ⟩
      go1 h = orStep (graphOf op1) orTail2 δ R (k op1) go2 h
      go0 : ⟨ δ ⊨ᵐ orTail0 ⟩ → ⟨ R ⟩
      go0 h = orStep (graphOf op0) orTail1 δ R (k op0) go1 h

    eqFrame-ok : {n : ℕ} (k : Fin n) (M : Formula ⟪ C ⟫ (suc n))
                 (δ : Vec SM n) (W : S)
               → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
               → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩ → ⟨ v ∈ˢ W ⟩)
               → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩ → ⟨ ((v , v∈) ∷ δ) ⊨ᵐ M ⟩)
               → ⟨ δ ⊨ᵐ eqFrame k M ⟩ ⟷ fst (lookup k δ) ≡ W
    eqFrame-ok k M δ W wsub mout min =
      ( eqFrame-out k M δ W wsub mout min
      , eqFrame-in k M δ W wsub mout min )

-- ==== Role 2: stepSet∈L (StepInL:2419-2422). ====

-- The defSet extensionality, fresh (the archive's Desc:480-502, about 20
-- in-fence lines), closed over the surviving `DefOf` and `ext-⊆`.
module Described (C : S) (Ctr : isTransV C) where

  module K = LevelKit C Ctr
  open K public

  described : (Φ : Formula ⟪ C ⟫ 1) (W : S)
            → ((v : S) → ⟨ v ∈ˢ W ⟩ → ⟨ v ∈ˢ C ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ W ⟩
               → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ Φ ⟩)
            → ((v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ Φ ⟩
               → ⟨ v ∈ˢ W ⟩)
            → DefOf.defSet C Φ ≡ W
  described Φ W wsub din dout = ext-⊆ sub sup
    where
    sub : (x : S) → ⟨ x ∈ˢ DefOf.defSet C Φ ⟩ → ⟨ x ∈ˢ W ⟩
    sub x h = dout x x∈ sat
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = DefOf.defSet⊆A C Φ x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈
      sat : ⟨ (PK.pt x x∈ ∷ []) ⊨ᵐ Φ ⟩
      sat = subst (λ e → ⟨ (e ∷ []) ⊨ᵐ Φ ⟩)
        (Σ≡Prop (λ w → snd (w ∈ˢ C)) (fib .snd))
        (subst ⟨_⟩ (DefOf.defSet-mem C Φ (fib .fst))
          (subst (λ w → ⟨ w ∈ˢ DefOf.defSet C Φ ⟩) (sym (fib .snd)) h))
    sup : (x : S) → ⟨ x ∈ˢ W ⟩ → ⟨ x ∈ˢ DefOf.defSet C Φ ⟩
    sup x h = subst (λ w → ⟨ w ∈ˢ DefOf.defSet C Φ ⟩) (fib .snd)
      (subst ⟨_⟩ (sym (DefOf.defSet-mem C Φ (fib .fst)))
        (subst (λ e → ⟨ (e ∷ []) ⊨ᵐ Φ ⟩)
          (sym (Σ≡Prop (λ w → snd (w ∈ˢ C)) (fib .snd)))
          (din x x∈ h)))
      where
      x∈ : ⟨ x ∈ˢ C ⟩
      x∈ = wsub x h
      fib : Σ[ m ∈ ⟪ C ⟫ ] (⟪ C ⟫↪ m ≡ x)
      fib = ∈-asFiber {a = x} {b = C} x∈

-- Obligation C, the constant step description: `stepForm` with its two-way
-- decode, the archive's `AtStep` (StepInL:2283-2399, 105 in-fence lines).
-- A record with a presentation-typed field walls here; the Σ-type checks.
module StepDesc (C : S) (Ctr : isTransV C) where

  module K = LevelKit C Ctr
  open K public

  StepDescObl : Type (ℓ-suc ℓ)
  StepDescObl =
    Σ[ stepForm ∈ ((u : S) (mu : ⟪ C ⟫) (qu : ⟪ C ⟫↪ mu ≡ u)
                 → ((v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ C ⟩) → Formula ⟪ C ⟫ 1) ]
      Σ[ din ∈ ((u : S) (mu : ⟪ C ⟫) (qu : ⟪ C ⟫↪ mu ≡ u)
              → (stepSub : (v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ C ⟩)
              → (v : S) (v∈ : ⟨ v ∈ˢ C ⟩) → ⟨ v ∈ˢ step u ⟩
              → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ stepForm u mu qu stepSub ⟩) ]
        ((u : S) (mu : ⟪ C ⟫) (qu : ⟪ C ⟫↪ mu ≡ u)
          → (stepSub : (v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ C ⟩)
          → (v : S) (v∈ : ⟨ v ∈ˢ C ⟩)
          → ⟨ (PK.pt v v∈ ∷ []) ⊨ᵐ stepForm u mu qu stepSub ⟩ → ⟨ v ∈ˢ step u ⟩)

-- The role closes once the description is given: `step u` is the carve of
-- `stepForm`, and the surviving `𝒟ₒ`-machinery places it one stage up.
stepSet∈L : (u ζ : S) → ⟨ u ∈ˢ Lset ζ ⟩ → ⟨ A ∈ˢ Lset ζ ⟩
          → ((v : S) → ⟨ v ∈ˢ step u ⟩ → ⟨ v ∈ˢ Lset ζ ⟩)
          → StepDesc.StepDescObl (Lset ζ) (Ltr ζ)
          → ⟨ step u ∈ˢ Lset (sucV ζ) ⟩
stepSet∈L u ζ u∈ A∈ sub obl = 𝒟ₒ⊆Lsuc ζ (step u)
  (𝒟ₒ-intro (Lset ζ) (step u) ∣ stepForm-u , desc ∣₁)
  where
  fibu : Σ[ m ∈ ⟪ Lset ζ ⟫ ] (⟪ Lset ζ ⟫↪ m ≡ u)
  fibu = ∈-asFiber {a = u} {b = Lset ζ} u∈
  mu : ⟪ Lset ζ ⟫
  mu = fibu .fst
  qu : ⟪ Lset ζ ⟫↪ mu ≡ u
  qu = fibu .snd
  module D = Described (Lset ζ) (Ltr ζ)
  stepForm-u : Formula ⟪ Lset ζ ⟫ 1
  stepForm-u = obl .fst u mu qu sub
  desc : DefOf.defSet (Lset ζ) stepForm-u ≡ step u
  desc = D.described stepForm-u (step u) sub
    (obl .snd .fst u mu qu sub)
    (obl .snd .snd u mu qu sub)
