{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.753-SPLIT] THE OBLIGATION.  One term: BoundInStage at the codes
-- of empty, from the named mirror package (746-SPLIT-SPLIT's
-- graph-mirror, imported beside PT per that task's measured scoping
-- fact).  The 673 At telescope is taken as leading arguments, in 673's
-- own inner-module shape (Probe673.agda:57-63).
--
-- THE CURE THIS SPLIT TESTS (the brief's ordered move).  [LJ-1.753]
-- wrote the full term and localized its heap wall at the domB
-- antecedent-type: the ascription there spelled the demand's 21-node
-- count chain with INFERRED plus-implicits, and the unifier blocked on
-- them against Def-headed countFo applications (the b7-3 failure mode
-- PT measured: runs/PT.agda:12-16).  This file applies PT's measured
-- shape at this site:
--
--   1. the domB antecedent formula is named once (phiA);
--   2. the ORIGINAL spelling's proof is refl over that constructor-
--      headed formula (countDom), never over the Def-headed `three`;
--   3. the SPLIT spelling's proof is a ONE-node chain with EXPLICIT
--      implicits over a constructor-headed base (pDom over countAppDom);
--   4. the row is carried between the spellings by IrrC.erase-cong
--      (EraseIrr.agda:56), the transport PT measured green.
--
-- The demand's domB-annotation (AbsL.⊨ᵐ of mapFo val ∘ mapFo slide of
-- CntS.erase phiA P-demand) meets this file's spelling only through
-- formula-level conversion, which never compares count proofs: erase
-- matches on the formula, and eraseTm's var clauses ignore their proof
-- argument.  No count chain of this file touches W3.count-three, so no
-- unifier ever decomposes a Def-headed countFo against a plus.
--
-- ONE Agda process, caliber from the pane, never set here.
-- Nothing is postulated.  No hole in the delivered file.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-753-SPLIT.Probe753Split {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.Syntax using ( Formula; var; ∃̇∈; _⇒̇_; _∧̇_; _∈̇_; ∀̇∈ )
open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import FOL.Manipulation.Parameters using ( countFo; countTm )
import FOL.Count
open import L.Constructible {ℓ} using ( 𝒮ʟ )
module CS = hPropStructure 𝒮ʟ
module CntS = FOL.Count.Count {ℓ = ℓ-suc ℓ} CS.S
open import Cubical.Data.Nat using ( ℕ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset; Lset-in; Lset-mono )
open import L.Axioms.Basic {ℓ} using ( ∅∈𝒟ₒ )
open import L.Coding.Model {ℓ} using ( appAt )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import V.Model {ℓ} using ( empty-spec; self∈sucV; ∈sucV-inl; ∈sucV-elim )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.Data.Empty as Empty
open import LJ-1-652.Probe652 {ℓ} lem as P652
import LJ-1-673.Probe673 {ℓ} lem as P673
import LJ-1-667.Probe667 {ℓ} lem as P667
import LJ-1-667.runs.W3 {ℓ} lem as W3
open import LJ-1-732.runs.Num {ℓ} lem
open import LJ-1-746-SPLIT-SPLIT.runs.Amb7 {ℓ} lem
open import LJ-1-746-SPLIT-SPLIT.runs.PT {ℓ} lem
open import LJ-1-746-SPLIT-SPLIT.runs.EraseIrr {ℓ} lem

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE 673 At TELESCOPE, as leading arguments (Probe673.agda:57-63).
-- =====================================================================

module At (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  (elem : P652.Frame652.A.Elementary lam ordλ succλ X X⊆Lλ ∅∈λ) where

  module At673 = P673.At lam ordλ succλ X X⊆Lλ ∅∈λ elem

  open At673 using ( BoundInStage )
  open At673.F.HS.H.T using ( Code; val )

  -- the restricted carrier, named once (P-l)
  SL : Type (ℓ-suc ℓ)
  SL = At673.F.HS.ASt.SL

  module AbsL = At673.F.HS.ASt.AbsL

  -- ===================================================================
  -- THE SL WITNESSES.  The frame's ∅∈λ and succλ climb the numerals
  -- into lam; Lset-mono lifts each into Lset lam.
  -- ===================================================================

  nin-lam : (k : ℕ) → ⟨ n k ∈ˢ lam ⟩
  nin-lam zero    = ∅∈λ
  nin-lam (suc k) = succλ (n k) (nin-lam k)

  ∅∈Lλ : ⟨ ∅ ∈ˢ Lset lam ⟩
  ∅∈Lλ = Lset-in lam ∅ ∅ ∅∈λ (∅∈𝒟ₒ ∅)

  Lset∅∈Lλ : ⟨ Lset ∅ ∈ˢ Lset lam ⟩
  Lset∅∈Lλ =
    Lset-mono (succλ ∅ ∅∈λ)
      (subst (λ s → ⟨ s ∈ˢ Lset (sucV ∅) ⟩) ∅≡Lset∅ (ord∈Lset-suc ∅ (ordn 0)))

  n∈Lλ : (k : ℕ) → ⟨ n k ∈ˢ Lset lam ⟩
  n∈Lλ k = Lset-mono (nin-lam (suc k)) (ord∈Lset-suc (n k) (ordn k))

  -- sucPin re-spelled at the restricted carrier: the ∀̇∈ domains are
  -- SL-pairs, the atoms read first projections (Num's sucPin shape,
  -- agents/tasks/LJ-1-732/runs/Num.agda:104-116).
  sucPinS : (a : S)
    → ( ⟨ a ∈ˢ sucV a ⟩
      × ( (x : SL) → ⟨ x .fst ∈ˢ a ⟩ → ⟨ x .fst ∈ˢ sucV a ⟩ )
      × ( (x : SL) → ⟨ x .fst ∈ˢ sucV a ⟩
                  → ∥ ⟨ x .fst ∈ˢ a ⟩ ⊎ (x .fst ≡ a) ∥₁ ) )
  sucPinS a =
      self∈sucV a
    , (λ _ hx → ∈sucV-inl hx)
    , (λ (x , _) hx →
        ∈sucV-elim {A = a} {x = x}
          {P = ∥ ⟨ x ∈ˢ a ⟩ ⊎ (x ≡ a) ∥₁}
          squash₁ hx (λ hh → ∣ inl hh ∣₁) (λ q → ∣ inr q ∣₁))

  -- ===================================================================
  -- THE OBLIGATION.  Written as one term against the demand's own
  -- reading; the where-block names only carrier-level pieces.
  -- ===================================================================

  bound-in-stage-from-mirror :
      StepKilledGen
    → (ca cp : Code)
    → fst (val cp) ≡ ∅
    → fst (val ca) ≡ Lset ∅
    → BoundInStage ca cp
  bound-in-stage-from-mirror gen ca cp hcp hca =
    ∣ wxs , ∣ ysl , ∣ zsl ,
      ( ( ( isOrd₁ , isOrd₂ ) , twelve )
      , sym hca
      , sym hcp )
    ∣₁ ∣₁ ∣₁
    where
    -- the three existential witnesses, at the restricted carrier
    zsl ysl wxs : SL
    zsl = Lset ∅ , Lset∅∈Lλ
    ysl = ∅ , ∅∈Lλ
    wxs = n 12 , n∈Lλ 12

    -- the fifteen-slot inner environment, γ15's order at the carrier
    env15 : Vec SL 15
    env15 =
      (n 0 , n∈Lλ 0) ∷ (n 1 , n∈Lλ 1) ∷ (n 2 , n∈Lλ 2) ∷ (n 3 , n∈Lλ 3)
      ∷ (n 4 , n∈Lλ 4) ∷ (n 5 , n∈Lλ 5) ∷ (n 6 , n∈Lλ 6) ∷ (n 7 , n∈Lλ 7)
      ∷ (n 8 , n∈Lλ 8) ∷ (n 9 , n∈Lλ 9) ∷ (n 10 , n∈Lλ 10) ∷ (n 11 , n∈Lλ 11)
      ∷ zsl ∷ ysl ∷ wxs ∷ []

    -- isOrd-at-p at the empty parameter: both conjuncts die at the
    -- first ∀̇∈ guard, a membership in the empty parameter
    isOrd₁ :
      (u : SL) → ⟨ u .fst ∈ˢ ysl .fst ⟩ →
      (v : SL) → ⟨ v .fst ∈ˢ u .fst ⟩ → ⟨ v .fst ∈ˢ ysl .fst ⟩
    isOrd₁ = λ (u , _) h₁ (v , _) h₂ →
      Empty.rec* (subst ⟨_⟩ (empty-spec u) h₁)

    isOrd₂ :
      (u : SL) → ⟨ u .fst ∈ˢ ysl .fst ⟩ →
      (v : SL) → ⟨ v .fst ∈ˢ u .fst ⟩ →
      (w : SL) → ⟨ w .fst ∈ˢ v .fst ⟩ → ⟨ w .fst ∈ˢ u .fst ⟩
    isOrd₂ = λ (u , _) h₁ (v , _) h₂ (w , _) h₃ →
      Empty.rec* (subst ⟨_⟩ (empty-spec u) h₁)

    -- =================================================================
    -- THE DOMB ANNOTATION, PT-SHAPE AT THE TRUE SLOT.  The graph slot
    -- hands the domB row as one function: the forall-binder at the
    -- 16-slot env genv16, then the folded semantics of the two domB
    -- implications (src/L/Condensation.lagda.md:1749-1754).  domBf is
    -- named once (P-l); countDom is refl over the CONSTRUCTOR-headed
    -- domBf; pDom is the SPLIT spelling, explicit-implicit nodes over
    -- constructor-headed subformulas, ending at countAppDom.  No name
    -- here has a Def-headed countFo under it, so no unifier ever faces
    -- the PT-measured decomposition block.
    -- =================================================================

    -- the graph witness rides the env: 16 slots at the domB row
    genv16 : Vec SL 16
    genv16 = (n 0 , n∈Lλ 0) ∷ env15

    Aimp : Formula CS.S 17
    Aimp =
      (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))
        (appAt {n = 18} (suc (suc zero)) (suc zero) zero))
      ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))
    Bimp : Formula CS.S 17
    Bimp =
      (var zero ∈̇ var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))
      ⇒̇ (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))
        (appAt {n = 18} (suc (suc zero)) (suc zero) zero))
    domBf : Formula CS.S 17
    domBf = Aimp ∧̇ Bimp

    countAppDom : countFo (appAt {n = 18} (suc (suc zero)) (suc zero) zero) ≡ 0
    countAppDom = refl

    -- the ORIGINAL spelling: refl, over the constructor-headed domBf
    countDom : countFo domBf ≡ 0
    countDom = refl

    -- the SPLIT spelling: explicit-implicit nodes, base countAppDom
    pDom : countFo domBf ≡ 0
    pDom =
      CntS.plus-zero-l
        {a = countFo Aimp}
        {b = countFo Bimp}
        (CntS.plus-zero-r
           {a = countFo Aimp}
           {b = countFo Bimp}
           (CntS.plus-zero-l
              {a = countFo (∃̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))
                              (appAt {n = 18} (suc (suc zero)) (suc zero) zero))}
              {b = countFo {K = CS.S} {n = 17} (var {n = 17} zero ∈̇ var {n = 17} (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))}
              (CntS.plus-zero-r
                 {a = countTm {K = CS.S} {n = 17} (var {n = 17} (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))}
                 {b = countFo (appAt {n = 18} (suc (suc zero)) (suc zero) zero)}
                 countAppDom)))

    -- the SPLIT-spelled row type, named once (PT's ApproxSlot shape,
    -- runs/PT.agda:61-64)
    DomSlot : Type (ℓ-suc ℓ)
    DomSlot =
      (x : SL) → ⟨ x .fst ∈ˢ n 12 ⟩ →
      ⟨ (x ∷ genv16) AbsL.⊨ᵐ
        (mapFo val (mapFo At673.slide (CntS.erase domBf pDom))) ⟩

    -- the domB row at the ORIGINAL spelling: the first implication
    -- kills at the appAt's own ∅-guard (its bound var 2 reads the
    -- n 0 witness); the converse dies in the empty parameter
    domB-row :
      (x : SL) → ⟨ x .fst ∈ˢ n 12 ⟩ →
      ⟨ (x ∷ genv16) AbsL.⊨ᵐ
        (mapFo val (mapFo At673.slide (CntS.erase domBf countDom))) ⟩
    domB-row = λ x hu →
      ( (λ ant →
          Empty.rec* (PT.rec (Empty.isProp⊥* {ℓ-suc ℓ})
            (λ { (w , w∈ , appat) →
              Empty.rec* (PT.rec (Empty.isProp⊥* {ℓ-suc ℓ})
                (λ { (pr , pr∈∅ , _) →
                  Empty.rec* (subst ⟨_⟩ (empty-spec (pr .fst)) pr∈∅) })
                appat) })
            ant))
      , λ h → Empty.rec* (subst ⟨_⟩ (empty-spec (x .fst)) h) )

    -- THE ERASE-CONG TRANSPORT (EraseIrr.agda:56), the brief's ordered
    -- cure, in PT's approx-split shape (runs/PT.agda:72-78): the row
    -- is carried from the original spelling into the split spelling
    domB-split : StepKilledGen → DomSlot
    domB-split gen = λ x hu →
      subst (λ ψ → ⟨ (x ∷ genv16) AbsL.⊨ᵐ (mapFo val (mapFo At673.slide ψ)) ⟩)
            (IrrC.erase-cong domBf countDom pDom)
            (domB-row x hu)

    -- the implication row (approxBndAt's tail): its formula is named
    -- once; the step-side subformula is W3's own Mx.G.A.S.stepBndAt,
    -- consumed by name, never re-spelled
    tailf : Formula CS.S 17
    tailf =
      ∀̇∈ (var (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))
        (appAt {n = 18} (suc (suc zero)) (suc zero) zero
        ⇒̇ W3.Mx.G.A.S.stepBndAt)

    countTailStep : countFo W3.Mx.G.A.S.stepBndAt ≡ 0
    countTailStep = refl

    -- the ORIGINAL spelling: refl over the constructor-headed tailf
    countTail : countFo tailf ≡ 0
    countTail = refl

    -- the SPLIT spelling: explicit-implicit nodes over countAppDom
    -- and countTailStep, both refl over constructor-headed formulas
    pTail : countFo tailf ≡ 0
    pTail =
      CntS.plus-zero-r
        {a = countTm {K = CS.S} {n = 17} (var {n = 17} (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))}
        {b = countFo (appAt {n = 18} (suc (suc zero)) (suc zero) zero
                       ⇒̇ W3.Mx.G.A.S.stepBndAt)}
        (CntS.plus-zero-l
           {a = countFo (appAt {n = 18} (suc (suc zero)) (suc zero) zero)}
           {b = countFo W3.Mx.G.A.S.stepBndAt}
           countAppDom)

    -- the SPLIT-spelled row type, named once
    TailSlot : Type (ℓ-suc ℓ)
    TailSlot =
      (x : SL) → ⟨ x .fst ∈ˢ n 12 ⟩ →
      ⟨ (x ∷ genv16) AbsL.⊨ᵐ
        (mapFo val (mapFo At673.slide (CntS.erase tailf pTail))) ⟩

    -- the tail row at the ORIGINAL spelling: the appAt's own guard
    -- reads the n 0 witness at slot 2 and dies
    tail-row :
      (x : SL) → ⟨ x .fst ∈ˢ n 12 ⟩ →
      ⟨ (x ∷ genv16) AbsL.⊨ᵐ
        (mapFo val (mapFo At673.slide (CntS.erase tailf countTail))) ⟩
    tail-row = λ x hu u hu' ant →
      Empty.rec* (PT.rec (Empty.isProp⊥* {ℓ-suc ℓ})
        (λ { (c , c∈∅ , _) →
          Empty.rec* (subst ⟨_⟩ (empty-spec (c .fst)) c∈∅) })
        ant)

    -- THE ERASE-CONG TRANSPORT, the brief's ordered cure
    tail-split : StepKilledGen → TailSlot
    tail-split gen = λ x hu →
      subst (λ ψ → ⟨ (x ∷ genv16) AbsL.⊨ᵐ (mapFo val (mapFo At673.slide ψ)) ⟩)
            (IrrC.erase-cong tailf countTail pTail)
            (tail-row x hu)

    -- φ₃: the twelve numerals ride the witness bound, then the 520
    -- matrix at the fifteen-slot inner environment
    twelve =
      ∣ (n 11 , n∈Lλ 11) , (mem11 ,
      ∣ (n 10 , n∈Lλ 10) , (mem10 ,
      ∣ (n 9 , n∈Lλ 9) , (mem9 ,
      ∣ (n 8 , n∈Lλ 8) , (mem8 ,
      ∣ (n 7 , n∈Lλ 7) , (mem7 ,
      ∣ (n 6 , n∈Lλ 6) , (mem6 ,
      ∣ (n 5 , n∈Lλ 5) , (mem5 ,
      ∣ (n 4 , n∈Lλ 4) , (mem4 ,
      ∣ (n 3 , n∈Lλ 3) , (mem3 ,
      ∣ (n 2 , n∈Lλ 2) , (mem2 ,
      ∣ (n 1 , n∈Lλ 1) , (mem1 ,
      ∣ (n 0 , n∈Lλ 0) , (mem0 , matrix15)
      ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁)
      ∣₁) ∣₁) ∣₁) ∣₁) ∣₁) ∣₁
      where
      -- the 520 matrix: transitivity, pins, the empty-table graph
      matrix15 = transK , (pins , graph)
        where
        transK :
          (u : SL) → ⟨ u .fst ∈ˢ n 12 ⟩ →
          (v : SL) → ⟨ v .fst ∈ˢ u .fst ⟩ → ⟨ v .fst ∈ˢ n 12 ⟩
        transK = λ (u , _) hu (v , _) hv → trZ hv hu

        pins =
            (λ (x , _) h → Empty.rec* (subst ⟨_⟩ (empty-spec x) h))
          , ( sucPinS (n 0)
            , ( sucPinS (n 1)
            , ( sucPinS (n 2)
            , ( sucPinS (n 3)
            , ( sucPinS (n 4)
            , ( sucPinS (n 5)
            , ( sucPinS (n 6)
            , ( sucPinS (n 7)
            , ( sucPinS (n 8)
            , ( sucPinS (n 9)
            , sucPinS (n 10) ) ) ) ) ) ) ) ) ) )

        graph = ∣ (n 0 , n∈Lλ 0) , (mem0 , approx , step) ∣₁
          where
          -- the approximation row: the domB row at its true slot, and
          -- the implication row (diagnostic: its slot prints next)
          approx = domB-split gen , tail-split gen

          -- the step row at the empty table: the first conjunct's
          -- guard is a membership in Lset ∅ (zsl at slot 13) and the
          -- second's witness chain dies in ∅ (Amb6)
          step =
              (λ (x , _) h → Empty.rec* (Lset∅-empty x h))
            , (λ (u , _) hu hw →
                Empty.rec* (PT.rec (Empty.isProp⊥* {ℓ-suc ℓ})
                  (λ { (c , c∈∅ , _) →
                    Empty.rec* (subst ⟨_⟩ (empty-spec (c .fst)) c∈∅) })
                  hw))
