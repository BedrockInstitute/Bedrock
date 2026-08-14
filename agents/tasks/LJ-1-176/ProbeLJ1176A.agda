{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.176] Probe A.  THE INCLUSION, BUILT INTO L.
--
-- THE OBJECT.  Block A5's object list holds `Incl`, the inclusion
-- `beta -> kappa` (agents/tasks/LJ-1-136/lj-1.136-report.md:212).  In the
-- chain as [LJ-1.156] rewrote it the object survives as `NonInitial.j`,
-- an injection from the small type of the smaller ordinal into the small
-- type of the larger one (agents/tasks/LJ-1-156/ProbeLJ1156A.agda:482-489).
-- [LJ-1.156] built it in V.  This file builds it in L.
--
-- THE GATE (DD8).  The widest unmeasured term of A5: does a build of one
-- of A5's objects into L need a `hasReplacementL`?  [LJ-1.156] measured
-- ZERO for the AMBIENT chain and stated that its probe "does not build a
-- single L-element" (agents/tasks/LJ-1-156/lj-1.156-report.md:640-642).
-- So the L side was unmeasured.  This file measures it.
--
-- P-l.  [LJ-1.154] measured that the separation carve BUILDS the IDENTITY
-- graph, whose domain and codomain are the SAME set.  The inclusion has
-- TWO sets and a subset obligation.  That cure is NOT transferred here by
-- analogy; the carve is re-run at this object with the extra parameter.
--
-- WHAT IS BUILT.
--   Part 1  `inclFo`, the description.  It takes ONE place.
--   Part 2  `StageBound`, the bound, GENERIC in the index type and the
--           family.  From [LJ-1.154] (ProbeLJ1154A.agda:128-152).
--   Part 3  `Carve`, THE GRAPH, between TWO sets.  The bound, the subset
--           witness and the separation field are all PARAMETERS, so no
--           line of Part 3 names an L axiom or an L stage.  DD4.
--   Part 4  `InclGraph`, the L instantiation.  It supplies the bound and
--           `hasSeparationL`, and nothing else.
--   Part 5  `OrdIncl`, the ORDINAL inclusion, which is A5's object.  It
--           is generic in the ordinal: any ordinal, any member.
--   Part 6  The C-38 guard, at two concrete ordinals of L.
--
-- ABORT CRITERION, fixed in agents/tasks/LJ-1-176/lj-1.176-report.md
-- section 1 BEFORE this file was written:
--   PRICED               the object builds with `hasSeparationL` alone,
--                        and A5 gets ONE number with a named basis.
--   WALLED               the build needs something nothing supplies.
--                        Name the term and stop.
--   REPLACEMENT REQUIRED the build needs a `hasReplacementL`.  Then A5's
--                        price is seconds and not only lines.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g"; never
-- committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-176.ProbeLJ1176A {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd; numeral-ord )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ}
  using ( numeralL; numeralL-fst; numeralL-suc )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro )

open import ProbeLJ1134A {ℓ} lem
  using ( injAt; injAt-in; module Small )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sum using ( inr )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- PART 1.  THE DESCRIPTION, AND IT TAKES ONE PLACE.
--
-- "p is the pair <x,x> for some x in D".  The codomain does NOT appear.
-- That is the whole reason the inclusion is as cheap as the identity
-- graph: an inclusion IS the identity on its domain, and the codomain
-- enters the four conjuncts, not the formula.  Inside the binder the
-- bound variable x is 0 and the free variable p is 1.
-- ---------------------------------------------------------------------

inclFo : S → Formula S 1
inclFo D = ∃̇∈ (con D) (prAtL (suc zero) zero zero)

module InclFo (D : S) where

  private
    at : (p x : S) → ⟨ (x ∷ p ∷ []) ⊨ prAtL (suc zero) zero zero ⟩
       ≡ (fst p ≡ pr (fst x) (fst x))
    at p x = cong ⟨_⟩ (prAtL-adequate (suc zero) zero zero (x ∷ p ∷ []))

  out : (p : S) → ⟨ (p ∷ []) ⊨ inclFo D ⟩
      → ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ D ⟩ × (fst p ≡ pr (fst x) (fst x))) ∥₁
  out p = PT.map (λ { (x , (m , h)) → x , (m , subst (λ T → T) (at p x) h) })

  into : (p x : S) → ⟨ x ∈ˢ D ⟩ → fst p ≡ pr (fst x) (fst x)
       → ⟨ (p ∷ []) ⊨ inclFo D ⟩
  into p x m e = ∣ x , (m , subst (λ T → T) (sym (at p x)) e) ∣₁

-- ---------------------------------------------------------------------
-- PART 2.  THE BOUND, GENERIC IN THE INDEX TYPE AND THE FAMILY.
--
-- [LJ-1.154]'s `StageBound` (ProbeLJ1154A.agda:128-152), unchanged.  It
-- bounds a SMALL family of L-elements and no more, so it serves every
-- carve in both towers.  DD4: one bound, every object.
-- ---------------------------------------------------------------------

module StageBound (I : Type ℓ) (g : I → S) where

  private
    stg : I → V ℓ
    stg i = stage (fst (g i)) (snd (g i))

    b : Σ[ β ∈ V ℓ ] (IsOrd β × ((i : I) → ⟨ stg i ∈ β ⟩))
    b = boundingOrd I stg (λ i → stage-ord (fst (g i)) (snd (g i)))

  -- SEALED.  Every consumer wants the bound as an ATOM.
  opaque
    β : V ℓ
    β = b .fst

    oβ : IsOrd β
    oβ = b .snd .fst

    bnd : S
    bnd = LsetS β oβ

    below : (i : I) → ⟨ fst (g i) ∈ fst bnd ⟩
    below i = Lset-mono {α = β} {β = stg i} (b .snd .snd i)
                (stage-mem (fst (g i)) (snd (g i)))

-- ---------------------------------------------------------------------
-- PART 3.  THE GRAPH, CARVED BETWEEN TWO SETS.  NOT ONE
-- `hasReplacementL`.
--
-- This module is a STRICT GENERALIZATION of [LJ-1.154]'s `Carve`, which
-- fixes the codomain to the domain (ProbeLJ1154A.agda:167-170).  Part 5
-- below instantiates it at an ordinal and its member; `Carve D D bnd
-- (\ _ m -> m) below sep` gives [LJ-1.154]'s object back.
--
-- The bound, the SUBSET WITNESS and the separation field are all
-- parameters, so no line below names an L axiom or an L stage.  The
-- residue, stated rather than hidden: the module still sits over the
-- structure `S` and the coding layer (`prʟ`, `prAtL`, `svAt`, `domAt`,
-- `injAt`).  That is the model's pair vocabulary, not L's axioms.
-- ---------------------------------------------------------------------

module Carve (D C bnd : S)
             (sub : (z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩)
             (below : (x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ pr (fst x) (fst x) ∈ fst bnd ⟩)
             (sep : (b : S) (φ : Formula S 1)
                  → isContr (SetOf (λ z → (z ∈ˢ b) ⊓ ((z ∷ []) ⊨ φ)))) where

  private
    module Fo = InclFo D

  -- THE GRAPH.  One separation, and the file names `hasReplacementL`
  -- nowhere.  SEALED, for the reason [LJ-1.136] section 16.4 measured.
  opaque
    G : S
    G = fst (fst (sep bnd (inclFo D)))

    G-spec : (z : S) → (z ∈ˢ G) ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ inclFo D))
    G-spec = snd (fst (sep bnd (inclFo D)))

  G-out : (z : S) → ⟨ z ∈ˢ G ⟩
        → ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ D ⟩ × (fst z ≡ pr (fst x) (fst x))) ∥₁
  G-out z h = Fo.out z (snd (subst ⟨_⟩ (G-spec z) h))

  G-in : (z x : S) → ⟨ x ∈ˢ D ⟩ → fst z ≡ pr (fst x) (fst x) → ⟨ z ∈ˢ G ⟩
  G-in z x m e = subst ⟨_⟩ (sym (G-spec z))
    ( subst (λ w → ⟨ w ∈ fst bnd ⟩) (sym e) (below x m)
    , Fo.into z x m e )

  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
           → ∥ (fst x ≡ fst y) × ⟨ x ∈ˢ D ⟩ ∥₁
  pair-out x y h = PT.map step (G-out (prʟ x y) h')
    where
    h' : ⟨ prʟ x y ∈ˢ G ⟩
    h' = subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst x y)) h
    step : Σ[ u ∈ S ] (⟨ u ∈ˢ D ⟩ × (fst (prʟ x y) ≡ pr (fst u) (fst u)))
         → (fst x ≡ fst y) × ⟨ x ∈ˢ D ⟩
    step (u , (m , e)) = (xu ∙ sym yu) , subst (λ w → ⟨ w ∈ fst D ⟩) (sym xu) m
      where
      q : (fst x ≡ fst u) × (fst y ≡ fst u)
      q = pr-inj (sym (prʟ-fst x y) ∙ e)
      xu = fst q
      yu = snd q

  pair-in : (x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ pr (fst x) (fst x) ∈ fst G ⟩
  pair-in x m = subst (λ w → ⟨ w ∈ fst G ⟩) (prʟ-fst x x)
                  (G-in (prʟ x x) x m (prʟ-fst x x))

  -- =====================================================================
  -- THE FOUR CONJUNCTS of [LJ-1.136] Probe A, PROVED.  The statements
  -- are that file's, word for word (src/ProbeLJ1136A.agda:134-169), with
  -- the parameter renamed and the RANGE conjunct now landing in the
  -- CODOMAIN.  That last one is the whole delta against [LJ-1.154], and
  -- it is where the subset witness is spent.
  -- =====================================================================

  γ : S ^ 2
  γ = G ∷ D ∷ []

  sv : ⟨ γ ⊨ svAt zero ⟩
  sv = svAt-in zero γ (λ x y y' p q →
    PT.rec (setIsSet (fst y) (fst y'))
      (λ r → PT.rec (setIsSet (fst y) (fst y'))
        (λ r' → sym (fst r) ∙ fst r') (pair-out x y' q))
      (pair-out x y p))

  ij : ⟨ γ ⊨ injAt zero ⟩
  ij = injAt-in zero γ (λ y x x' p q →
    PT.rec (setIsSet (fst x) (fst x'))
      (λ r → PT.rec (setIsSet (fst x) (fst x'))
        (λ r' → fst r ∙ sym (fst r')) (pair-out x' y q))
      (pair-out x y p))

  dm : ⟨ γ ⊨ domAt zero (suc zero) ⟩
  dm = domAt-intro zero (suc zero) γ (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D)) snd (pair-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ x , pair-in x m ∣₁

  -- THE ONE LINE THE IDENTITY GRAPH DOES NOT HAVE.
  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst C ⟩
  ran x y h = PT.rec (snd (fst y ∈ fst C))
    (λ r → sub (fst y) (subst (λ w → ⟨ w ∈ fst D ⟩) (fst r) (snd r)))
    (pair-out x y h)

  -- =====================================================================
  -- THE GRAPH, READ BACK AS AN HONEST INJECTION BETWEEN THE SMALL TYPES.
  -- That is the shape the square-law chain consumes
  -- (agents/tasks/LJ-1-156/ProbeLJ1156A.agda:482-489).  SEALED at the
  -- definition: [LJ-1.136] measured that an unsealed `Small` application
  -- exhausts an 8g heap (report section 16.4).
  -- =====================================================================

  private
    module Sm = Small G D C sv dm ij ran

  opaque
    incl : ⟪ fst D ⟫ → ⟪ fst C ⟫
    incl = Sm.small

    incl-inj : (m n : ⟪ fst D ⟫) → incl m ≡ incl n → m ≡ n
    incl-inj = Sm.small-inj

    -- AND IT IS THE INCLUSION.  C-38: a graph that carves, proves four
    -- conjuncts and reads back as SOME injection is not evidence for
    -- THIS object.  This line says the value is the same SET.
    incl-val : (m : ⟪ fst D ⟫) → ⟪ fst C ⟫↪ (incl m) ≡ ⟪ fst D ⟫↪ m
    incl-val m = snd (Sm.fib m) ∙ sym val
      where
      val : ⟪ fst D ⟫↪ m ≡ fst (Sm.E.toFun (Sm.at m))
      val = PT.rec (setIsSet (⟪ fst D ⟫↪ m) (fst (Sm.E.toFun (Sm.at m)))) fst
        (pair-out (Sm.toS m) (Sm.E.toFun (Sm.at m))
          (Sm.E.toFun-graph (Sm.at m)))

-- ---------------------------------------------------------------------
-- PART 4.  THE L INSTANTIATION.
--
-- This part supplies two things and no more: the stage bound, and
-- `hasSeparationL`.  Part 2 and this part are where L enters.
-- ---------------------------------------------------------------------

module InclGraph (D C : S)
                 (sub : (z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩) where

  private
    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    -- The pairs live inside a set you can name BEFORE you build them.
    -- The family is indexed by the SMALL type of members of D.
    dg : ⟪ fst D ⟫ → S
    dg m = prʟ (toD m) (toD m)

    module SB = StageBound ⟪ fst D ⟫ dg

    bel : (x : S) → ⟨ x ∈ˢ D ⟩ → ⟨ pr (fst x) (fst x) ∈ fst SB.bnd ⟩
    bel x mx = subst (λ w → ⟨ w ∈ fst SB.bnd ⟩) pa (SB.below (fD .fst))
      where
      fD : Σ[ m ∈ ⟪ fst D ⟫ ] (⟪ fst D ⟫↪ m ≡ fst x)
      fD = fiber (fst D) mx
      pa : fst (dg (fD .fst)) ≡ pr (fst x) (fst x)
      pa = prʟ-fst (toD (fD .fst)) (toD (fD .fst))
         ∙ cong₂ pr (fD .snd) (fD .snd)

  open Carve D C SB.bnd sub bel hasSeparationL public

-- ---------------------------------------------------------------------
-- PART 5.  THE ORDINAL INCLUSION.  THIS IS A5's OBJECT.
--
-- `NonInitial.j` in [LJ-1.156]'s chain is the inclusion of a member
-- ordinal into its host (ProbeLJ1156A.agda:482-489), and there it is a
-- metatheoretic function.  Here it is an ELEMENT of L which reads back
-- as that function.
--
-- DD4: the module is generic in the ordinal.  Nothing below names a
-- stage, a numeral or `omega`.  The ordinal supplies the subset witness
-- through its own transitivity, and that is all it supplies.
-- ---------------------------------------------------------------------

module OrdIncl (C : S) (oC : IsOrd (fst C))
               (D : S) (D∈C : ⟨ fst D ∈ fst C ⟩) where

  open InclGraph D C (λ _ z∈D → oC .fst z∈D D∈C) public

-- ---------------------------------------------------------------------
-- PART 6.  THE C-38 GUARD.
--
-- "A restatement that nothing can satisfy makes the module vacuously
-- true: it typechecks, it is fast, and it proves nothing."
-- dev/LESSONS.md:3427.  So Part 5 is instantiated at TWO REAL ORDINALS
-- OF L, the numerals 1 and 2, which are distinct and stand in the
-- membership the module wants.  The witness shows the graph is
-- inhabited at a concrete pair, and that the honest injection sends the
-- member to itself.
-- ---------------------------------------------------------------------

module Witness where

  one : S
  one = numeralL 1

  two : S
  two = numeralL 2

  oTwo : IsOrd (fst two)
  oTwo = subst IsOrd (sym (numeralL-fst 2)) (numeral-ord 2)

  -- 1 is a member of 2, which is the ordinal fact the module consumes.
  one∈two : ⟨ fst one ∈ fst two ⟩
  one∈two = numeralL-suc 1 one .snd ∣ inr refl ∣₁

  module J = OrdIncl two oTwo one one∈two

  -- 0 is a member of 1, so the domain is NOT empty.
  zero∈one : ⟨ fst (numeralL 0) ∈ fst one ⟩
  zero∈one = numeralL-suc 0 (numeralL 0) .snd ∣ inr refl ∣₁

  -- The graph HOLDS the pair <0,0>.  Not vacuous.
  inG : ⟨ pr (fst (numeralL 0)) (fst (numeralL 0)) ∈ fst J.G ⟩
  inG = J.pair-in (numeralL 0) zero∈one

  -- The graph RUNS: an honest injection from the small type of 1 into
  -- the small type of 2.
  theIncl : ⟪ fst one ⟫ → ⟪ fst two ⟫
  theIncl = J.incl

  theIncl-inj : (m n : ⟪ fst one ⟫) → theIncl m ≡ theIncl n → m ≡ n
  theIncl-inj = J.incl-inj

  -- AND IT IS THE INCLUSION: the value is the same set as the argument.
  theIncl-val : (m : ⟪ fst one ⟫) → ⟪ fst two ⟫↪ (theIncl m) ≡ ⟪ fst one ⟫↪ m
  theIncl-val = J.incl-val
