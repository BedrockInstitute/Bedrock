{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.650]  Clause (ii)'s coded covering ordinal, measured against
--             [LJ-1.646]'s keystone.
--
--   THE FRAME WALLED FIRST.  The honest way to take a predecessor's
--   type is to IMPORT it, and that is what this file tried.  Importing
--   LJ-1-595.Probe595 pulls the 544/550/558/564/570/578 chain and
--   EXHAUSTS the wide caliber's 2 GB heap on the frame ALONE, with no
--   term of this task's own in the file: runs/FLOOR-IMPORT595.agda.txt,
--   runs/floor-1.out, exit 251 at 1,911,226,368 bytes after 63.18 s.
--   Restructured (coder clause, owner 2026-08-23): src/ only, and the
--   two predecessor types RESTATED VERBATIM, each cited at the line it
--   was read.  runs/floor-2.out is that frame, exit 0 in 3.67 s.
--
--   THE SECOND PROOF IN SECTION 3 IS W2-EXCUSED BY THAT WALL.  Section
--   3 is [LJ-1.595]'s section 4 re-read at this file.  W2 forbids a
--   second proof of the same fact without a reason; the reason is the
--   measured wall above, and nothing else.
--
--   Nothing is postulated.  No hole.  Nothing lands in src/.
--   ONE Agda process, caliber from the pane, never set here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-650.Probe650 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; var; _∈̇_; _∧̇_; ∃̇_ )
open import FOL.Manipulation.Parameters
  using ( countFo; constantsFo; absFo; ⊨-abs )
open import FOL.Manipulation.Relabelling
  using ( embed; mapFo; mapFo-comp; mapΔ₀; ⊨-map )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Model {ℓ} using ( self∈sucV )
open import L.Constructible {ℓ}
  using ( IsOrd; Lset; 𝒟ₒ; Lset-in; Lset-out )
open import L.Ordinal {ℓ} using ( ∅-ord; suc-ord; mem-ord )
open import L.Ordinal.Stages {ℓ} lem
  using ( ord∈Lset-suc; ord∈Lset→∈; Lset-cumul )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; isOrdAt; Δ₀-isOrdAt; module Amb )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( leastOf )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Vec using ( Vec; _∷_; [] )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open InfinitySet {ℓ} using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

module Coded (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module T = HS.H.T
  module AB = HS.ASt.AbsL
  open T using ( Code; val; wit; vals; Sat; _⊨c_; _⊨₀_ )

  -- ===================================================================
  -- SECTION 1.  THE TWO PREDECESSOR TYPES, AND THE OBLIGATION'S TYPE.
  --
  --   Each is restated VERBATIM from the probe that typechecked it, and
  --   the citation is the line range.  The import route is measured
  --   dead at the head of this file.
  -- ===================================================================

  -- agents/tasks/LJ-1-462/Probe462.agda:118-121.  [LJ-1.646]'s
  -- obligation, and it is NOT BUILT ANYWHERE: `ls agents/tasks/`
  -- returns no LJ-1-646 directory in this worktree.  It enters here
  -- only as a hypothesis, exactly as the brief orders.
  LsetCodeOrd : Type (ℓ-suc ℓ)
  LsetCodeOrd =
    (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  -- agents/tasks/LJ-1-595/Probe595.agda:353-357, unchanged.
  CodedCover : Type (ℓ-suc ℓ)
  CodedCover = (c : Code)
             → Σ[ d ∈ Code ]
                 ( IsOrd (fst (val d))
                 × ⟨ fst (val c) ∈ˢ Lset (fst (val d)) ⟩ )

  -- THE BRIEF'S OBLIGATION, AS A TYPE.  Section 7 says why this file
  -- does not inhabit it, and review-of-coded-cover.md is the stop.
  CodedCoverFromKeystone : Type (ℓ-suc ℓ)
  CodedCoverFromKeystone = LsetCodeOrd → CodedCover

  -- ===================================================================
  -- SECTION 2.  W3.  THE CODED SKOLEM WITNESS, UNTRUNCATED.
  --
  --   The brief's widest unmeasured term is "whether the covering
  --   ordinal's code needs `Lset` named at the STAGE rather than at a
  --   hull code".  The term that settles it is this one, and the tree
  --   does not have it: `L.Hull`'s `closed`
  --   (src/L/Hull.lagda.md:120-142) proves the same fact and then
  --   FORGETS the code and truncates.  `CodedCover` is untruncated and
  --   asks for the code itself, so `closed` cannot serve it.
  --
  --   The proof is `closed`'s, with the Skolem constant `wit k ψ cs`
  --   kept instead of discarded.  `val-wit` (src/L/Hull.lagda.md:105-107)
  --   is what makes the keeping legal.
  --
  --   THE MINIATURE RAN ALONE FIRST: runs/W3.agda, runs/w3-1.out,
  --   exit 0 in 3.83 s.
  -- ===================================================================

  skolemCode : (φ : Formula Code 1)
             → ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) ⊨c φ ⟩ ∥₁
             → Σ[ d ∈ Code ] ⟨ (val d ∷ []) ⊨c φ ⟩
  skolemCode φ h = d , sat
    where
    k : ℕ
    k = countFo φ
    ψ : Formula (⊥* {ℓ}) (suc k)
    ψ = absFo φ
    cs : Vec Code k
    cs = constantsFo φ
    w : Sat k ψ (vals cs)
    w = PT.map
      (λ { (b , hb) → b
         , subst ⟨_⟩ (cong (λ vs → (b ∷ vs) ⊨₀ ψ) (sym (T.vals≡map cs)))
             (subst ⟨_⟩
               (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) AB.𝒮M val φ (b ∷ [])) hb) }) h
    d : Code
    d = wit k ψ cs
    a : HS.ASt.SL
    a = T.search k ψ (vals cs) w
    pa : ⟨ (a ∷ vals cs) ⊨₀ ψ ⟩
    pa = leastOf HS.ASt.wL {ℓ'' = ℓ-suc ℓ} lem
           (λ b → (b ∷ vals cs) ⊨₀ ψ) w .snd .fst
    val-d : val d ≡ a
    val-d = T.val-wit k ψ cs w
    sat-a : ⟨ (a ∷ []) ⊨c φ ⟩
    sat-a = subst ⟨_⟩
      (sym (⊨-abs (hPropAlgebra (ℓ-suc ℓ)) AB.𝒮M val φ (a ∷ [])))
      (subst ⟨_⟩ (cong (λ vs → (a ∷ vs) ⊨₀ ψ) (T.vals≡map cs)) pa)
    sat : ⟨ (val d ∷ []) ⊨c φ ⟩
    sat = subst (λ b → ⟨ (b ∷ []) ⊨c φ ⟩) (sym val-d) sat-a

  -- ===================================================================
  -- SECTION 3.  THE ORDINAL FORMULA, READ AT THE STAGE'S INNER WORLD.
  --
  --   [LJ-1.595]'s section 4 (Probe595.agda:206-255), re-read here
  --   because the import of that file walls.  Nothing is changed.
  -- ===================================================================

  ordFo : Formula Code 1
  ordFo = embed isOrdAt

  ordSL : Formula HS.ASt.SL 1
  ordSL = embed isOrdAt

  prj : HS.ASt.SL → SV.S
  prj = fst

  private
    ι-irr : (λ (b : Empty.⊥* {ℓ-suc ℓ}) → val (Empty.rec* b))
          ≡ (λ (b : Empty.⊥* {ℓ-suc ℓ}) → Empty.rec* b)
    ι-irr = funExt (λ b → Empty.rec* b)

  ord-relabel : mapFo val ordFo ≡ ordSL
  ord-relabel = mapFo-comp Empty.rec* val isOrdAt
              ∙ cong (λ f → mapFo f isOrdAt) ι-irr

  private
    step-code : (a : HS.ASt.SL)
              → ((a ∷ []) AB.⊨ᵐ (mapFo val ordFo)) ≡ ((a ∷ []) ⊨c ordFo)
    step-code a = ⊨-map (hPropAlgebra (ℓ-suc ℓ)) AB.𝒮M val id ordFo (a ∷ [])

    step-amb : (a : HS.ASt.SL)
             → ((fst a ∷ []) AB.⊨ᵛ ordSL) ≡ ((fst a ∷ []) Amb.⊨ₚ isOrdAt)
    step-amb a =
      ⊨-map (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ Empty.rec* prj isOrdAt (fst a ∷ [])

    step-abs : (a : HS.ASt.SL)
             → ((a ∷ []) AB.⊨ᵐ ordSL) ≡ ((fst a ∷ []) AB.⊨ᵛ ordSL)
    step-abs a = AB.abs₀ (mapΔ₀ Empty.rec* Δ₀-isOrdAt) (a ∷ [])

  ord-read : (a : HS.ASt.SL)
           → ((a ∷ []) ⊨c ordFo) ≡ ((fst a ∷ []) Amb.⊨ₚ isOrdAt)
  ord-read a = sym (step-code a)
             ∙ cong (λ χ → (a ∷ []) AB.⊨ᵐ χ) ord-relabel
             ∙ step-abs a ∙ step-amb a

  ord-out : (a : HS.ASt.SL) → ⟨ (a ∷ []) ⊨c ordFo ⟩ → IsOrd (fst a)
  ord-out a h = Amb.isOrdAt-out (fst a) (subst ⟨_⟩ (ord-read a) h)

  ord-in : (a : HS.ASt.SL) → IsOrd (fst a) → ⟨ (a ∷ []) ⊨c ordFo ⟩
  ord-in a o = subst ⟨_⟩ (sym (ord-read a)) (Amb.isOrdAt-in (fst a) o)

  -- ===================================================================
  -- SECTION 4.  THE HULL HAS AN ORDINAL CODE, UNCONDITIONALLY.
  --
  --   Section 2 is not plumbing, and this is the cheapest witness of
  --   that: `ordFo` is satisfiable at the empty set, so the hull NAMES
  --   an ordinal, and the name is returned unwrapped.  No hypothesis,
  --   no keystone, no level formula.
  -- ===================================================================

  ∅L : HS.ASt.SL
  ∅L = ∅ , HS.H.∅∈Lsetα

  ordinal-code : Σ[ d ∈ Code ] IsOrd (fst (val d))
  ordinal-code = fst got , ord-out (val (fst got)) (snd got)
    where
    got : Σ[ d ∈ Code ] ⟨ (val d ∷ []) ⊨c ordFo ⟩
    got = skolemCode ordFo ∣ ∅L , ord-in ∅L ∅-ord ∣₁

  -- ===================================================================
  -- SECTION 5.  `CodedCover` AT AN ORDINAL VALUE, UNCONDITIONALLY.
  --
  --   THIS IS THE HALF THE KEYSTONE WAS SUPPOSED TO BUY, AND IT COSTS
  --   NOTHING.  [LJ-1.595] paid the ordinal case at the CLAUSE level
  --   (`cover-at-ordinal`, Probe595.agda:324-352) and left `CodedCover`
  --   whole.  With section 2 the same formula pays it at the CODE
  --   level: the selecting formula is "x is an ordinal and c is a
  --   member of x", both conjuncts are already read, and `wit` names
  --   the witness.
  --
  --   The formula and the two halves of its adequacy are
  --   [LJ-1.595]'s, at Probe595.agda:324-352.
  -- ===================================================================

  coded-cover-at-ordinal :
      (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ]
        ( IsOrd (fst (val d)) × ⟨ fst (val c) ∈ˢ Lset (fst (val d)) ⟩ )
  coded-cover-at-ordinal c oc =
      fst got
    , ( oa
      , Lset-cumul vc (fst (val (fst got))) oc oa (snd got .snd)
          (ord∈Lset-suc vc oc) )
    where
    vc : SV.S
    vc = fst (val c)
    φ : Formula Code 1
    φ = ordFo ∧̇ (con c ∈̇ var zero)
    osvc : IsOrd (sucV vc)
    osvc = suc-ord oc
    vc∈λ : ⟨ vc ∈ˢ lam ⟩
    vc∈λ = ord∈Lset→∈ lam ordλ vc oc (snd (val c))
    a₀ : HS.ASt.SL
    a₀ = sucV vc
       , Lset-cumul (sucV vc) lam osvc ordλ (succλ vc vc∈λ)
           (ord∈Lset-suc (sucV vc) osvc)
    got : Σ[ d ∈ Code ] ⟨ (val d ∷ []) ⊨c φ ⟩
    got = skolemCode φ ∣ a₀ , (ord-in a₀ osvc , self∈sucV vc) ∣₁
    oa : IsOrd (fst (val (fst got)))
    oa = ord-out (val (fst got)) (snd got .fst)

  -- ===================================================================
  -- SECTION 6.  WHAT DOES CLOSE `CodedCover`, AND IT IS A FORMULA.
  --
  --   `InternalCover` is [LJ-1.595]'s own (Probe595.agda:409-416),
  --   verbatim: a formula that COVERS, one code at a time, with the
  --   ordinal half dropped.  [LJ-1.595] took it to clause (ii)
  --   (`cover-from-internal`, Probe595.agda:418-430) and could not take
  --   it to `CodedCover`, because it had no way to name the witness.
  --   Section 2 is that way, and this is the term [LJ-1.595] could not
  --   write.
  --
  --   READ THE HYPOTHESIS AGAINST THE KEYSTONE.  `InternalCover` binds
  --   the covering ordinal INSIDE a formula.  `LsetCodeOrd` names a
  --   level at an ordinal ALREADY GIVEN.  That is the same binder
  --   difference [LJ-1.595] measured between clause (i) and clause (ii)
  --   (lj-1.595-report.md:154-156), recurring one level down.
  -- ===================================================================

  InternalCover : Type (ℓ-suc ℓ)
  InternalCover =
    (c : Code)
    → Σ[ χ ∈ Formula Code 1 ]
        ( ∥ Σ[ a ∈ HS.ASt.SL ]
             (IsOrd (fst a) × ⟨ (a ∷ []) ⊨c χ ⟩) ∥₁
        × ((a : HS.ASt.SL) → ⟨ (a ∷ []) ⊨c χ ⟩
           → ⟨ fst (val c) ∈ˢ Lset (fst a) ⟩) )

  coded-cover-from-internal : InternalCover → CodedCover
  coded-cover-from-internal ic c =
      fst got
    , ( ord-out (val (fst got)) (snd got .fst)
      , snd (snd (ic c)) (val (fst got)) (snd got .snd) )
    where
    χ : Formula Code 1
    χ = fst (ic c)
    sat : ∥ Σ[ a ∈ HS.ASt.SL ] ⟨ (a ∷ []) ⊨c (ordFo ∧̇ χ) ⟩ ∥₁
    sat = PT.map (λ { (a , oa , hχ) → a , (ord-in a oa , hχ) })
            (fst (snd (ic c)))
    got : Σ[ d ∈ Code ] ⟨ (val d ∷ []) ⊨c (ordFo ∧̇ χ) ⟩
    got = skolemCode (ordFo ∧̇ χ) sat

  -- ===================================================================
  -- SECTION 6.5.  AND THE FORMULA THAT SUPPLIES `InternalCover` IS THE
  --               LEVEL GRAPH, READ AT THE STAGE.
  --
  --   `LevelFormula` is one formula in TWO variables, sound and
  --   complete for "v is the level indexed by γ" at the stage's inner
  --   world.  Its shape is [LJ-1.595]'s `Shared`
  --   (Probe595.agda:481-494) with Devlin's Σ₀ witness variable
  --   dropped, because nothing below uses it.
  --
  --   IT REACHES `CodedCover` WITH NO SUBSTITUTION.  The consumer binds
  --   the LEVEL and leaves the INDEX free, so `∃̇` is the only operation
  --   spent.  [LJ-1.595] recorded the OTHER direction, index bound by a
  --   constant, as a renaming it did not price
  --   (lj-1.595-report.md:167-169), and that is the direction
  --   `LsetCodeOrd` needs.  So this formula is BELOW both, and it is
  --   nearer to `CodedCover` than to the keystone.
  -- ===================================================================

  LevelFormula : Type (ℓ-suc ℓ)
  LevelFormula =
    Σ[ lv ∈ Formula Code 2 ]
      ( ((v γ : HS.ASt.SL) → ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩ → fst v ≡ Lset (fst γ))
      × ((γ : HS.ASt.SL) → IsOrd (fst γ)
         → ∥ Σ[ v ∈ HS.ASt.SL ]
              ((fst v ≡ Lset (fst γ)) × ⟨ (v ∷ γ ∷ []) ⊨c lv ⟩) ∥₁) )

  -- [LJ-1.595]'s section 5 (Probe595.agda:270-287), re-read here for
  -- the same measured reason as section 3: the import walls.  The
  -- covering ordinal is FREE at the stage; only its NAME costs.
  cover-in-stage : (y : SV.S) (y∈ : ⟨ y ∈ˢ Lset lam ⟩)
                 → ∥ Σ[ a ∈ HS.ASt.SL ]
                      (IsOrd (fst a) × ⟨ y ∈ˢ Lset (fst a) ⟩) ∥₁
  cover-in-stage y y∈ = PT.map go (Lset-out lam y y∈)
    where
    go : Σ[ δ ∈ SV.S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset δ) ⟩)
       → Σ[ a ∈ HS.ASt.SL ] (IsOrd (fst a) × ⟨ y ∈ˢ Lset (fst a) ⟩)
    go (δ , δ∈λ , y∈𝒟) =
        (sucV δ , sδ∈Lλ)
      , ( osδ , Lset-in (sucV δ) δ y (self∈sucV δ) y∈𝒟 )
      where
      oδ : IsOrd δ
      oδ = mem-ord {A = lam} ordλ δ δ∈λ
      osδ : IsOrd (sucV δ)
      osδ = suc-ord oδ
      sδ∈Lλ : ⟨ sucV δ ∈ˢ Lset lam ⟩
      sδ∈Lλ = Lset-cumul (sucV δ) lam osδ ordλ (succλ δ δ∈λ)
                (ord∈Lset-suc (sucV δ) osδ)

  internal-from-level : LevelFormula → InternalCover
  internal-from-level (lv , so , co) c = χ , (sat , adeq)
    where
    vc : SV.S
    vc = fst (val c)
    χ : Formula Code 1
    χ = ∃̇ (lv ∧̇ (con c ∈̇ var zero))
    sat : ∥ Σ[ a ∈ HS.ASt.SL ]
             (IsOrd (fst a) × ⟨ (a ∷ []) ⊨c χ ⟩) ∥₁
    sat = PT.rec PT.squash₁ mk (cover-in-stage vc (snd (val c)))
      where
      mk : Σ[ a ∈ HS.ASt.SL ] (IsOrd (fst a) × ⟨ vc ∈ˢ Lset (fst a) ⟩)
         → ∥ Σ[ a ∈ HS.ASt.SL ]
              (IsOrd (fst a) × ⟨ (a ∷ []) ⊨c χ ⟩) ∥₁
      mk (a , oa , h) = PT.map mk₂ (co a oa)
        where
        mk₂ : Σ[ v ∈ HS.ASt.SL ]
                ((fst v ≡ Lset (fst a)) × ⟨ (v ∷ a ∷ []) ⊨c lv ⟩)
            → Σ[ a' ∈ HS.ASt.SL ]
                (IsOrd (fst a') × ⟨ (a' ∷ []) ⊨c χ ⟩)
        mk₂ (v , e , hlv) =
          a , ( oa
              , ∣ v , (hlv , subst (λ w → ⟨ vc ∈ˢ w ⟩) (sym e) h) ∣₁ )
    adeq : (a : HS.ASt.SL) → ⟨ (a ∷ []) ⊨c χ ⟩ → ⟨ vc ∈ˢ Lset (fst a) ⟩
    adeq a h = PT.rec (snd (vc ∈ˢ Lset (fst a))) go h
      where
      go : Σ[ v ∈ HS.ASt.SL ]
             ⟨ (v ∷ a ∷ []) ⊨c (lv ∧̇ (con c ∈̇ var zero)) ⟩
         → ⟨ vc ∈ˢ Lset (fst a) ⟩
      go (v , hv) =
        subst (λ w → ⟨ vc ∈ˢ w ⟩) (so v a (hv .fst)) (hv .snd)

  -- THE WHOLE OF CLAUSE (ii)'s CODED RESIDUE, FROM ONE FORMULA.
  coded-cover-from-level : LevelFormula → CodedCover
  coded-cover-from-level lf = coded-cover-from-internal (internal-from-level lf)

  -- ===================================================================
  -- SECTION 7.  THE KEYSTONE, AND WHERE IT STOPS.
  --
  --   THE OBLIGATION IS NOT INHABITED IN THIS FILE AND THE STOP IS
  --   review-of-coded-cover.md.  The three terms below are the
  --   evidence, and each one typechecks.
  -- ===================================================================

  -- 7.1  WHAT THE KEYSTONE IS, AS A MAP: an ordinal code in, a LEVEL
  --      code out.  Its output value is `Lset (...)`, never an ordinal.
  keystone-output-is-a-level :
      LsetCodeOrd → (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))
  keystone-output-is-a-level ko = ko

  -- 7.2  IT IS NOT VACUOUS.  Section 4 gives it an argument, so the
  --      keystone does produce a code, unconditionally on the hull.
  keystone-applied : LsetCodeOrd
                   → Σ[ d ∈ Code ] Σ[ e ∈ Code ]
                       (fst (val e) ≡ Lset (fst (val d)))
  keystone-applied ko = fst ordinal-code
                      , ko (fst ordinal-code) (snd ordinal-code)

  -- 7.3  AND IT STILL DOES NOT REACH `CodedCover`.  This is the whole
  --      keystone route to one row of `CodedCover`, written out: it
  --      applies only where the value is ALREADY an ordinal, and even
  --      there it needs TWO facts the tree does not have, both about
  --      the LEVEL it returns.  Section 5 pays the same row with
  --      NEITHER of them and with no keystone at all.
  keystone-row-at-ordinal :
      LsetCodeOrd
    → (c : Code) → (oc : IsOrd (fst (val c)))
    → IsOrd (Lset (fst (val c)))                        -- NOT IN THE TREE
    → ⟨ fst (val c) ∈ˢ Lset (Lset (fst (val c))) ⟩      -- NOT IN THE TREE
    → Σ[ d ∈ Code ]
        ( IsOrd (fst (val d)) × ⟨ fst (val c) ∈ˢ Lset (fst (val d)) ⟩ )
  keystone-row-at-ordinal ko c oc oL covL =
      fst (ko c oc)
    , ( subst IsOrd (sym (snd (ko c oc))) oL
      , subst (λ w → ⟨ fst (val c) ∈ˢ Lset w ⟩) (sym (snd (ko c oc))) covL )
