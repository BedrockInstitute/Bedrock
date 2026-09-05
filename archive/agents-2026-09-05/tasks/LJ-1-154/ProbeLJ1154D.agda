{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.154] Probe D.  DOES THE PARAMETER HIDE THE COST?
--
-- Probe D is Probe A with ONE change: `Carve` names `hasSeparationL`
-- directly instead of taking the separation field as a parameter.
--
-- The objection this run answers: Probe A's `Carve` takes `sep` as a
-- module parameter, so the elaborator sees an ATOM and never opens the
-- separation.  If that is where Probe A's seconds went, the DD4 answer
-- is bought with a measurement that does not hold when the field is
-- named.  Probe D names it.  The difference is the price of the
-- generality.
--
-- ABORT CRITERION: none.  This is a control, not a decision.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-154.ProbeLJ1154D {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; con; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; domAt; domAt-intro )

open import ProbeLJ1134A {ℓ} lem
  using ( injAt; injAt-in; module Small; module Concrete )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( _×_ )
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
-- Replacement takes a TWO-place description and a functionality proof
-- (src/ProbeLJ1136A.agda:72-93).  Separation takes a ONE-place formula.
-- The identity graph fits the one-place shape because the set A goes in
-- as a CONSTANT, exactly as [LJ-1.152]'s `appC` carries its graph
-- (agents/tasks/LJ-1-152/ProbeLJ1152E.agda:94-95).
--
-- "p is the pair <x,x> for some x in A".  Inside the binder the bound
-- variable x is 0 and the free variable p is 1.
-- ---------------------------------------------------------------------

idFo : S → Formula S 1
idFo A = ∃̇∈ (con A) (prAtL (suc zero) zero zero)

module IdFo (A : S) where

  private
    at : (p x : S) → ⟨ (x ∷ p ∷ []) ⊨ prAtL (suc zero) zero zero ⟩
       ≡ (fst p ≡ pr (fst x) (fst x))
    at p x = cong ⟨_⟩ (prAtL-adequate (suc zero) zero zero (x ∷ p ∷ []))

  out : (p : S) → ⟨ (p ∷ []) ⊨ idFo A ⟩
      → ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ A ⟩ × (fst p ≡ pr (fst x) (fst x))) ∥₁
  out p = PT.map (λ { (x , (m , h)) → x , (m , subst (λ T → T) (at p x) h) })

  into : (p x : S) → ⟨ x ∈ˢ A ⟩ → fst p ≡ pr (fst x) (fst x)
       → ⟨ (p ∷ []) ⊨ idFo A ⟩
  into p x m e = ∣ x , (m , subst (λ T → T) (sym (at p x)) e) ∣₁

-- ---------------------------------------------------------------------
-- PART 2.  THE BOUND, GENERIC IN THE INDEX TYPE AND THE FAMILY.
--
-- [LJ-1.152]'s `PairBound` bounds the pairs between two sets
-- (agents/tasks/LJ-1-152/ProbeLJ1152E.agda:195-248).  Nothing in it is
-- about pairs: it bounds a SMALL family of L-elements and no more.  So
-- the module here takes the index type and the family, and `PairBound`
-- is this module at the index type of pairs.  DD4: one bound, every
-- carve.
--
-- The device is `hasPowerL`'s (src/L/Axioms/Power.lagda.md:143-190)
-- with the resizing dropped: `boundingOrd` bounds a small family of
-- ordinals (src/L/Ordinal.lagda.md:154-155), and a stage is an element
-- of L (src/L/Axioms/Basic.lagda.md:160-161).
-- ---------------------------------------------------------------------

module StageBound (I : Type ℓ) (g : I → S) where

  private
    stg : I → V ℓ
    stg i = stage (fst (g i)) (snd (g i))

    b : Σ[ β ∈ V ℓ ] (IsOrd β × ((i : I) → ⟨ stg i ∈ β ⟩))
    b = boundingOrd I stg (λ i → stage-ord (fst (g i)) (snd (g i)))

  -- SEALED.  Every consumer wants the bound as an ATOM.  P-y prices a
  -- seal by the definitions that look INSIDE, and here that is `below`
  -- alone.
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
-- PART 3.  THE GRAPH, CARVED.  NOT ONE `hasReplacementL`.
--
-- The bound and the separation field are PARAMETERS.  Nothing below
-- names L, so the J tower re-instantiates this module instead of
-- writing it again.  DD4.
-- ---------------------------------------------------------------------

module Carve (A bnd : S)
             (below : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ pr (fst x) (fst x) ∈ fst bnd ⟩)
             where

  private
    module Fo = IdFo A

  -- THE GRAPH.  One separation, and the file names `hasReplacementL`
  -- nowhere.  SEALED, for the reason [LJ-1.136] section 16.4 measured.
  opaque
    G : S
    G = fst (fst (hasSeparationL bnd (idFo A)))

    G-spec : (z : S) → (z ∈ˢ G) ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ idFo A))
    G-spec = snd (fst (hasSeparationL bnd (idFo A)))

  G-out : (z : S) → ⟨ z ∈ˢ G ⟩
        → ∥ Σ[ x ∈ S ] (⟨ x ∈ˢ A ⟩ × (fst z ≡ pr (fst x) (fst x))) ∥₁
  G-out z h = Fo.out z (snd (subst ⟨_⟩ (G-spec z) h))

  -- The write direction, and the bound is what separation asks for that
  -- replacement did not.
  G-in : (z x : S) → ⟨ x ∈ˢ A ⟩ → fst z ≡ pr (fst x) (fst x) → ⟨ z ∈ˢ G ⟩
  G-in z x m e = subst ⟨_⟩ (sym (G-spec z))
    ( subst (λ w → ⟨ w ∈ fst bnd ⟩) (sym e) (below x m)
    , Fo.into z x m e )

  -- The pair reading, in the shape the conjuncts consume.
  pair-out : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩
           → ∥ (fst x ≡ fst y) × ⟨ x ∈ˢ A ⟩ ∥₁
  pair-out x y h = PT.map step (G-out (prʟ x y) h')
    where
    h' : ⟨ prʟ x y ∈ˢ G ⟩
    h' = subst (λ w → ⟨ w ∈ fst G ⟩) (sym (prʟ-fst x y)) h
    step : Σ[ u ∈ S ] (⟨ u ∈ˢ A ⟩ × (fst (prʟ x y) ≡ pr (fst u) (fst u)))
         → (fst x ≡ fst y) × ⟨ x ∈ˢ A ⟩
    step (u , (m , e)) = (xu ∙ sym yu) , subst (λ w → ⟨ w ∈ fst A ⟩) (sym xu) m
      where
      q : (fst x ≡ fst u) × (fst y ≡ fst u)
      q = pr-inj (sym (prʟ-fst x y) ∙ e)
      xu = fst q
      yu = snd q

  pair-in : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ pr (fst x) (fst x) ∈ fst G ⟩
  pair-in x m = subst (λ w → ⟨ w ∈ fst G ⟩) (prʟ-fst x x)
                  (G-in (prʟ x x) x m (prʟ-fst x x))

  -- =====================================================================
  -- THE FOUR CONJUNCTS of [LJ-1.136] Probe A, PROVED.  The statements
  -- are that file's, word for word (src/ProbeLJ1136A.agda:134-169).
  -- =====================================================================

  γ : S ^ 2
  γ = G ∷ A ∷ []

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
        → ⟨ fst x ∈ fst A ⟩
    fwd x = PT.rec (snd (fst x ∈ fst A))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst A)) snd (pair-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst A ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst G) ⟩
    bwd x m = ∣ x , pair-in x m ∣₁

  ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst A ⟩
  ran x y h = PT.rec (snd (fst y ∈ fst A))
    (λ r → subst (λ w → ⟨ w ∈ fst A ⟩) (fst r) (snd r)) (pair-out x y h)

  -- =====================================================================
  -- THE GRAPH, READ BACK AS AN HONEST FUNCTION.  SEALED at the
  -- definition: [LJ-1.136] measured that an unsealed `Small` application
  -- exhausts an 8g heap (report section 16.4).
  -- =====================================================================

  private
    module Sm = Small G A A sv dm ij ran

  opaque
    idFun : ⟪ fst A ⟫ → ⟪ fst A ⟫
    idFun = Sm.small

    idFun-inj : (m n : ⟪ fst A ⟫) → idFun m ≡ idFun n → m ≡ n
    idFun-inj = Sm.small-inj

    -- AND IT IS THE IDENTITY.  C-38: a graph that carves, proves four
    -- conjuncts and reads back as something else is the wrong graph.
    idFun-is-id : (m : ⟪ fst A ⟫) → idFun m ≡ m
    idFun-is-id m = ↪-inj {a = fst A} {m = idFun m} {n = m}
      (snd (Sm.fib m) ∙ sym val)
      where
      val : ⟪ fst A ⟫↪ m ≡ fst (Sm.E.toFun (Sm.at m))
      val = PT.rec (setIsSet (⟪ fst A ⟫↪ m) (fst (Sm.E.toFun (Sm.at m)))) fst
        (pair-out (Sm.toS m) (Sm.E.toFun (Sm.at m))
          (Sm.E.toFun-graph (Sm.at m)))

-- ---------------------------------------------------------------------
-- PART 4.  THE L INSTANTIATION.
--
-- Here the separation is named inside `Carve` itself, so this part
-- supplies the stage bound and nothing else.
-- ---------------------------------------------------------------------

module IdGraph (A : S) where

  private
    toA : ⟪ fst A ⟫ → S
    toA m = ⟪ fst A ⟫↪ m
          , isL-trans {x = fst A} {y = ⟪ fst A ⟫↪ m} (member (fst A) m) (snd A)

    -- THE FAMILY THE BOUND NEEDS, and this is the whole answer to
    -- "do the pairs live inside a set you can name?".  They are indexed
    -- by the SMALL type of members of A, and `prʟ` builds each one, so
    -- the family exists BEFORE the graph does.
    dg : ⟪ fst A ⟫ → S
    dg m = prʟ (toA m) (toA m)

    module SB = StageBound ⟪ fst A ⟫ dg

    bel : (x : S) → ⟨ x ∈ˢ A ⟩ → ⟨ pr (fst x) (fst x) ∈ fst SB.bnd ⟩
    bel x mx = subst (λ w → ⟨ w ∈ fst SB.bnd ⟩) pa (SB.below (fA .fst))
      where
      fA : Σ[ m ∈ ⟪ fst A ⟫ ] (⟪ fst A ⟫↪ m ≡ fst x)
      fA = fiber (fst A) mx
      pa : fst (dg (fA .fst)) ≡ pr (fst x) (fst x)
      pa = prʟ-fst (toA (fA .fst)) (toA (fA .fst))
         ∙ cong₂ pr (fA .snd) (fA .snd)

  open Carve A SB.bnd bel public

-- ---------------------------------------------------------------------
-- PART 5.  THE C-38 GUARD.
--
-- "A restatement that nothing can satisfy makes the module vacuously
-- true: it typechecks, it is fast, and it proves nothing."
-- dev/LESSONS.md:3427.  So Part 4 is instantiated at [LJ-1.134]'s
-- concrete non-degenerate set {a} (src/ProbeLJ1134A.agda:190-222), and
-- the carved graph is shown to be EXACTLY {<a,a>}: inhabited by that
-- pair, and holding nothing else.
-- ---------------------------------------------------------------------

module Witness (a : S) where

  module Cc = Concrete a
  module Id = IdGraph Cc.Dm

  -- The graph is NOT empty.
  inG : ⟨ pr (fst a) (fst a) ∈ fst Id.G ⟩
  inG = Id.pair-in a Cc.inD

  -- And it holds nothing else.  With `inG`, the carved graph on {a} is
  -- [LJ-1.134]'s concrete graph {<a,a>}, member for member.
  onlyPair : (z : S) → ⟨ z ∈ˢ Id.G ⟩ → fst z ≡ pr (fst a) (fst a)
  onlyPair z h = PT.rec (setIsSet (fst z) (pr (fst a) (fst a)))
    (λ { (x , (m , e)) →
      e ∙ cong₂ pr (Cc.memD (fst x) m) (Cc.memD (fst x) m) })
    (Id.G-out z h)

  -- The graph runs: an honest injection, and it is the identity.
  theIdFun : ⟪ fst Cc.Dm ⟫ → ⟪ fst Cc.Dm ⟫
  theIdFun = Id.idFun

  theIdFun-inj : (m n : ⟪ fst Cc.Dm ⟫) → theIdFun m ≡ theIdFun n → m ≡ n
  theIdFun-inj = Id.idFun-inj

  theIdFun-is-id : (m : ⟪ fst Cc.Dm ⟫) → theIdFun m ≡ m
  theIdFun-is-id = Id.idFun-is-id

-- A fully concrete instance, at the numeral zero.
module WitnessZero = Witness (numeralL 0)
