{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.152] Probe E.  CAN TWO L-GRAPHS COMPOSE WITHOUT A SECOND
-- `hasReplacementL`?
--
-- [LJ-1.136] section 17.5 named this measurement and did not run it
-- (agents/tasks/LJ-1-136/lj-1.136-report.md:1125-1140).  A5 needs six
-- injections built into L.  At one replacement each, [LJ-1.136] INFERRED
-- about 25 minutes of cold check for the block.  If a composite can be
-- carved by SEPARATION out of a set already in L, A5 pays the
-- replacement once, not six times.
--
-- WHAT IS BUILT.
--   Part 1  `appC`, the application reader with the graph as a CONSTANT.
--           `appAt` takes the graph from the context; separation takes a
--           ONE-place formula, so the graph must be a constant instead.
--   Part 2  `compFo`, the composite condition, and both readings.
--   Part 3  `PairBound`, the bound the separation carves.  It is a
--           STAGE, and no replacement builds it: the pairs form a family
--           over a SMALL index type, and `boundingOrd` bounds it.
--   Part 4  `Comp`, THE COMPOSITE, with all four conjuncts of
--           [LJ-1.136] Probe B's selection predicate, and the honest
--           injection read back through `Small`.
--   Part 5  The C-38 guard, at [LJ-1.134]'s concrete graph.
--
-- ABORT CRITERION, fixed in agents/tasks/LJ-1-152/lj-1.152-report.md
-- section 1 BEFORE this file was written:
--   GO     the composite elaborates with no second `hasReplacementL`,
--          and its cold seconds are nearer 3.51 than 254.
--   NO-GO  composition needs its own replacement.
--   STOP   the composite does not elaborate at all.
--
-- Tracked probe; ONE agda process under GHCRTS="-A64m -I0 -M8g";
-- never committed to src/.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-152.ProbeLJ1152E {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; con; _∧̇_; ∃̇_; ∃̇∈ )
import FOL.Absoluteness
import FOL.ZFModel
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr; pr-inj )
open import V.Presentation {ℓ} using ( member; fiber )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; Lset; Lset-mono )
open import L.Ordinal {ℓ} using ( boundingOrd )
open import L.Stage {ℓ} lem using ( stage; stage-ord; stage-mem )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Axioms.Full {ℓ} lem using ( hasSeparationL )
open import L.Axioms.Numerals {ℓ} using ( numeralL )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst
        ; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )

open import ProbeLJ1134A {ℓ} lem
  using ( injAt; injAt-in; injAt-out; module Small; module Concrete )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Functions.Logic using ( ⇔toPath; ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module ModelL = FOL.ZFModel 𝒮ʟ
open ModelL using ( SetOf )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- ---------------------------------------------------------------------
-- PART 1.  The application reader, with the graph as a CONSTANT.
--
-- `appAt f x y` reads the graph out of the context at index f
-- (src/L/Coding/Model.lagda.md:160-161).  Separation takes a formula of
-- ONE place, so a composite condition cannot keep the two graphs in the
-- context.  The delivered constant term is what carries them instead,
-- exactly as `subFo` carries its set (src/L/Axioms/Power.lagda.md:108).
--
-- The proof is `appAt-adequate` (:163-187) with the constant in place of
-- the lookup.  Nothing else changes, which is the point: the reader is
-- GENERIC in where the graph comes from.
-- ---------------------------------------------------------------------

appC : ∀ {n} → S → Fin n → Fin n → Formula S n
appC F x y = ∃̇∈ (con F) (prAtL zero (suc x) (suc y))

appC-adequate : ∀ {n} (F : S) (x y : Fin n) (γ : S ^ n)
  → (γ ⊨ appC F x y)
  ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst F)
appC-adequate F x y γ = ⇔toPath fwd bwd
  where
  a = fst (lookup x γ)
  b = fst (lookup y γ)

  read : (z : S) → ⟨ (z ∷ γ) ⊨ prAtL zero (suc x) (suc y) ⟩ → fst z ≡ pr a b
  read z h = subst ⟨_⟩ (prAtL-adequate zero (suc x) (suc y) (z ∷ γ)) h

  fwd : ⟨ γ ⊨ appC F x y ⟩ → ⟨ pr a b ∈ fst F ⟩
  fwd = PT.rec (snd (pr a b ∈ fst F))
    (λ { (z , (z∈F , h)) → subst (λ w → ⟨ w ∈ fst F ⟩) (read z h) z∈F })

  bwd : ⟨ pr a b ∈ fst F ⟩ → ⟨ γ ⊨ appC F x y ⟩
  bwd h = ∣ zS , (h , subst ⟨_⟩
      (sym (prAtL-adequate zero (suc x) (suc y) (zS ∷ γ))) refl) ∣₁
    where
    zS : S
    zS = pr a b , isL-trans {x = fst F} {y = pr a b} h (F .snd)

-- ---------------------------------------------------------------------
-- PART 2.  The composite condition, as ONE formula of one place.
--
-- "p is the ordered pair of x and z, and F sends x to y, and H sends y
-- to z."  Three unbounded existentials over the model, which cost
-- nothing here, and three delivered readers.
--
-- The context inside the three binders is (z ∷ y ∷ x ∷ p ∷ []), so p is
-- variable 3, x is 2, y is 1 and z is 0.
-- ---------------------------------------------------------------------

compFo : (F H : S) → Formula S 1
compFo F H = ∃̇ (∃̇ (∃̇ (
       prAtL (suc (suc (suc zero))) (suc (suc zero)) zero
    ∧̇ (appC F (suc (suc zero)) (suc zero)
    ∧̇  appC H (suc zero) zero))))

module CompFo (F H : S) where

  Chain : S → S → S → S → Type (ℓ-suc ℓ)
  Chain p x y z = (fst p ≡ pr (fst x) (fst z))
                × (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                × ⟨ pr (fst y) (fst z) ∈ fst H ⟩)

  private
    ctx : (p x y z : S) → S ^ 4
    ctx p x y z = z ∷ y ∷ x ∷ p ∷ []

    atPr : (p x y z : S)
         → ((ctx p x y z) ⊨ prAtL (suc (suc (suc zero))) (suc (suc zero)) zero)
         ≡ ((fst p ≡ pr (fst x) (fst z)) , setIsSet (fst p) (pr (fst x) (fst z)))
    atPr p x y z =
      prAtL-adequate (suc (suc (suc zero))) (suc (suc zero)) zero (ctx p x y z)

    atF : (p x y z : S)
        → ((ctx p x y z) ⊨ appC F (suc (suc zero)) (suc zero))
        ≡ (pr (fst x) (fst y) ∈ fst F)
    atF p x y z = appC-adequate F (suc (suc zero)) (suc zero) (ctx p x y z)

    atH : (p x y z : S)
        → ((ctx p x y z) ⊨ appC H (suc zero) zero)
        ≡ (pr (fst y) (fst z) ∈ fst H)
    atH p x y z = appC-adequate H (suc zero) zero (ctx p x y z)

  out : (p : S) → ⟨ (p ∷ []) ⊨ compFo F H ⟩
      → ∥ Σ[ x ∈ S ] Σ[ y ∈ S ] Σ[ z ∈ S ] Chain p x y z ∥₁
  out p = PT.rec squash₁ (λ { (x , hx) →
          PT.rec squash₁ (λ { (y , hy) →
          PT.rec squash₁ (λ { (z , (hp , (hf , hh))) →
            ∣ x , y , z
            , ( subst ⟨_⟩ (atPr p x y z) hp
              , ( subst ⟨_⟩ (atF p x y z) hf
                , subst ⟨_⟩ (atH p x y z) hh ) ) ∣₁ }) hy }) hx })

  into : (p x y z : S) → Chain p x y z → ⟨ (p ∷ []) ⊨ compFo F H ⟩
  into p x y z (hp , (hf , hh)) =
    ∣ x , ∣ y , ∣ z
    , ( subst ⟨_⟩ (sym (atPr p x y z)) hp
      , ( subst ⟨_⟩ (sym (atF p x y z)) hf
        , subst ⟨_⟩ (sym (atH p x y z)) hh ) ) ∣₁ ∣₁ ∣₁

-- ---------------------------------------------------------------------
-- PART 3.  The bound, and NO replacement builds it.
--
-- Separation carves a subset out of a set that is already in L.  The
-- composite lives in the product of the two end sets, and no delivered
-- field gives that product.  A STAGE gives it instead: the pairs form a
-- family indexed by the SMALL type of pairs of members, `boundingOrd`
-- bounds any small family of ordinals (src/L/Ordinal.lagda.md:154-155),
-- and a stage is an element of L (src/L/Axioms/Basic.lagda.md:160-161).
--
-- This is `hasPowerL`'s own device (src/L/Axioms/Power.lagda.md:143-190)
-- with the resizing dropped, because a pair of L-elements is
-- constructible by construction and needs no resized statement.
-- ---------------------------------------------------------------------

module PairBound (D C : S) where

  Ix : Type ℓ
  Ix = ⟪ fst D ⟫ × ⟪ fst C ⟫

  private
    toD : ⟪ fst D ⟫ → S
    toD m = ⟪ fst D ⟫↪ m
          , isL-trans {x = fst D} {y = ⟪ fst D ⟫↪ m} (member (fst D) m) (snd D)

    toC : ⟪ fst C ⟫ → S
    toC k = ⟪ fst C ⟫↪ k
          , isL-trans {x = fst C} {y = ⟪ fst C ⟫↪ k} (member (fst C) k) (snd C)

    pw : Ix → S
    pw (m , k) = prʟ (toD m) (toC k)

    stg : Ix → V ℓ
    stg i = stage (fst (pw i)) (snd (pw i))

    b : Σ[ β ∈ V ℓ ] (IsOrd β × ((i : Ix) → ⟨ stg i ∈ β ⟩))
    b = boundingOrd Ix stg (λ i → stage-ord (fst (pw i)) (snd (pw i)))

  -- SEALED.  Every consumer below wants the bound as an ATOM; nothing
  -- wants to look inside `boundingOrd`.  P-y prices a seal by the
  -- definitions that look INSIDE, and here that is `below` alone.
  opaque
    β : V ℓ
    β = b .fst

    oβ : IsOrd β
    oβ = b .snd .fst

    bnd : S
    bnd = LsetS β oβ

    below : (x z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
          → ⟨ pr (fst x) (fst z) ∈ fst bnd ⟩
    below x z mx mz = subst (λ w → ⟨ w ∈ Lset β ⟩) pa
      (Lset-mono {α = β} {β = stg i} (b .snd .snd i)
        (stage-mem (fst (pw i)) (snd (pw i))))
      where
      -- Agda never infers a type inside an `opaque` block, so both
      -- fibres are named.  That is the seal's whole cost here.
      fD : Σ[ m ∈ ⟪ fst D ⟫ ] (⟪ fst D ⟫↪ m ≡ fst x)
      fD = fiber (fst D) mx
      fC : Σ[ k ∈ ⟪ fst C ⟫ ] (⟪ fst C ⟫↪ k ≡ fst z)
      fC = fiber (fst C) mz
      i : Ix
      i = fD .fst , fC .fst
      pa : fst (pw i) ≡ pr (fst x) (fst z)
      pa = prʟ-fst (toD (fD .fst)) (toC (fC .fst))
         ∙ cong₂ pr (fD .snd) (fC .snd)

-- ---------------------------------------------------------------------
-- PART 4.  THE COMPOSITE.
--
-- Two graphs, four conjuncts each, and NOT ONE `hasReplacementL`.
-- Every set is a PARAMETER, so P-l holds: no type below names a
-- transparent presentation.
-- ---------------------------------------------------------------------

module Comp (D E C F H : S)
            (svF : ⟨ (F ∷ D ∷ []) ⊨ svAt zero ⟩)
            (dmF : ⟨ (F ∷ D ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijF : ⟨ (F ∷ D ∷ []) ⊨ injAt zero ⟩)
            (ranF : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩
                  → ⟨ fst y ∈ fst E ⟩)
            (svH : ⟨ (H ∷ E ∷ []) ⊨ svAt zero ⟩)
            (dmH : ⟨ (H ∷ E ∷ []) ⊨ domAt zero (suc zero) ⟩)
            (ijH : ⟨ (H ∷ E ∷ []) ⊨ injAt zero ⟩)
            (ranH : (y z : S) → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
                  → ⟨ fst z ∈ fst C ⟩) where

  private
    module PB = PairBound D C
    module CF = CompFo F H

    γF : S ^ 2
    γF = F ∷ D ∷ []

    γH : S ^ 2
    γH = H ∷ E ∷ []

  -- THE COMPOSITE, BY SEPARATION.  This is the whole answer to the
  -- brief: one `hasSeparationL`, and the file names `hasReplacementL`
  -- nowhere.  SEALED, for the reason [LJ-1.136] section 16.4 measured.
  opaque
    K : S
    K = fst (fst (hasSeparationL PB.bnd (compFo F H)))

    K-spec : (p : S) → (p ∈ˢ K)
           ≡ ((p ∈ˢ PB.bnd) ⊓ ((p ∷ []) ⊨ compFo F H))
    K-spec = snd (fst (hasSeparationL PB.bnd (compFo F H)))

  -- The two readings of membership, in the shape the conjuncts consume.
  K-out : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
        → ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                      × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁
  K-out x z h = PT.rec squash₁ step (CF.out (prʟ x z) (snd (subst ⟨_⟩ (K-spec (prʟ x z)) h')))
    where
    h' : ⟨ prʟ x z ∈ˢ K ⟩
    h' = subst (λ w → ⟨ w ∈ fst K ⟩) (sym (prʟ-fst x z)) h

    step : (Σ[ u ∈ S ] Σ[ v ∈ S ] Σ[ w ∈ S ] CF.Chain (prʟ x z) u v w)
         → ∥ Σ[ y ∈ S ] (⟨ pr (fst x) (fst y) ∈ fst F ⟩
                       × ⟨ pr (fst y) (fst z) ∈ fst H ⟩) ∥₁
    step (u , v , w , (hp , (hf , hh))) = ∣ v , (hf' , hh') ∣₁
      where
      q : (fst x ≡ fst u) × (fst z ≡ fst w)
      q = pr-inj (sym (prʟ-fst x z) ∙ hp)
      hf' : ⟨ pr (fst x) (fst v) ∈ fst F ⟩
      hf' = subst (λ t → ⟨ pr t (fst v) ∈ fst F ⟩) (sym (fst q)) hf
      hh' : ⟨ pr (fst v) (fst z) ∈ fst H ⟩
      hh' = subst (λ t → ⟨ pr (fst v) t ∈ fst H ⟩) (sym (snd q)) hh

  K-in : (x y z : S) → ⟨ fst x ∈ fst D ⟩ → ⟨ fst z ∈ fst C ⟩
       → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ pr (fst y) (fst z) ∈ fst H ⟩
       → ⟨ pr (fst x) (fst z) ∈ fst K ⟩
  K-in x y z mx mz hf hh =
    subst (λ w → ⟨ w ∈ fst K ⟩) (prʟ-fst x z)
      (subst ⟨_⟩ (sym (K-spec (prʟ x z)))
        ( subst (λ w → ⟨ w ∈ fst PB.bnd ⟩) (sym (prʟ-fst x z))
            (PB.below x z mx mz)
        , CF.into (prʟ x z) x y z (prʟ-fst x z , (hf , hh)) ))

  -- =====================================================================
  -- THE FOUR CONJUNCTS, for the COMPOSITE.
  -- =====================================================================

  γK : S ^ 2
  γK = K ∷ D ∷ []

  svK : ⟨ γK ⊨ svAt zero ⟩
  svK = svAt-in zero γK (λ x y y' p q →
    PT.rec (setIsSet (fst y) (fst y'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst y) (fst y'))
        (λ { (w' , (hf' , hh')) →
          svAt-out zero γH svH w y y' hh
            (subst (λ t → ⟨ pr t (fst y') ∈ fst H ⟩)
              (sym (svAt-out zero γF svF x w w' hf hf')) hh') })
        (K-out x y' q) })
      (K-out x y p))

  ijK : ⟨ γK ⊨ injAt zero ⟩
  ijK = injAt-in zero γK (λ y x x' p q →
    PT.rec (setIsSet (fst x) (fst x'))
      (λ { (w , (hf , hh)) → PT.rec (setIsSet (fst x) (fst x'))
        (λ { (w' , (hf' , hh')) →
          injAt-out zero γF ijF w x x' hf
            (subst (λ t → ⟨ pr (fst x') t ∈ fst F ⟩)
              (sym (injAt-out zero γH ijH y w w' hh hh')) hf') })
        (K-out x' y q) })
      (K-out x y p))

  dmK : ⟨ γK ⊨ domAt zero (suc zero) ⟩
  dmK = domAt-intro zero (suc zero) γK (λ x → fwd x , bwd x)
    where
    fwd : (x : S) → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
        → ⟨ fst x ∈ fst D ⟩
    fwd x = PT.rec (snd (fst x ∈ fst D))
      (λ { (y , p) → PT.rec (snd (fst x ∈ fst D))
        (λ { (w , (hf , _)) → domAt-out zero (suc zero) γF dmF x w hf })
        (K-out x y p) })

    bwd : (x : S) → ⟨ fst x ∈ fst D ⟩
        → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst K) ⟩
    bwd x mx = PT.rec squash₁
      (λ { (w , hf) → PT.rec squash₁
        (λ { (z , hh) → ∣ z , K-in x w z mx (ranH w z hh) hf hh ∣₁ })
        (domAt-in zero (suc zero) γH dmH w (ranF x w hf)) })
      (domAt-in zero (suc zero) γF dmF x mx)

  ranK : (x z : S) → ⟨ pr (fst x) (fst z) ∈ fst K ⟩ → ⟨ fst z ∈ fst C ⟩
  ranK x z h = PT.rec (snd (fst z ∈ fst C))
    (λ { (w , (_ , hh)) → ranH w z hh }) (K-out x z h)

  -- =====================================================================
  -- THE COMPOSITE, READ BACK AS AN HONEST FUNCTION.
  -- SEALED at the definition.  [LJ-1.136] measured that an unsealed
  -- `Small` application exhausts an 8g heap (report section 16.4).
  -- =====================================================================

  private
    module Sm = Small K D C svK dmK ijK ranK

  opaque
    compFun : ⟪ fst D ⟫ → ⟪ fst C ⟫
    compFun = Sm.small

    compFun-inj : (m n : ⟪ fst D ⟫) → compFun m ≡ compFun n → m ≡ n
    compFun-inj = Sm.small-inj

-- ---------------------------------------------------------------------
-- PART 5.  THE C-38 GUARD.
--
-- "A restatement that nothing can satisfy makes the module vacuously
-- true: it typechecks, it is fast, and it proves nothing."
-- dev/LESSONS.md:3427.  So Part 4 is instantiated at [LJ-1.134]'s
-- concrete non-degenerate graph {<a,a>} over {a}, composed WITH ITSELF,
-- and the composite is shown INHABITED.
-- ---------------------------------------------------------------------

module Witness (a : S) where

  module Cc = Concrete a

  ranC : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst Cc.G ⟩ → ⟨ fst y ∈ fst Cc.Dm ⟩
  ranC x y h = subst (λ w → ⟨ w ∈ fst Cc.Dm ⟩)
                 (sym (snd (Cc.split x y h))) Cc.inD

  module Co = Comp Cc.Dm Cc.Dm Cc.Dm Cc.G Cc.G
                   Cc.sv Cc.dm Cc.ij ranC
                   Cc.sv Cc.dm Cc.ij ranC

  -- The composite is NOT empty: the pair <a,a> is in it.  Nothing above
  -- is vacuous.
  inK : ⟨ pr (fst a) (fst a) ∈ fst Co.K ⟩
  inK = Co.K-in a a a Cc.inD Cc.inD Cc.inG Cc.inG

  -- And the composite runs: an honest injection out of the domain.
  theComposite : ⟪ fst Cc.Dm ⟫ → ⟪ fst Cc.Dm ⟫
  theComposite = Co.compFun

  theComposite-inj : (m n : ⟪ fst Cc.Dm ⟫)
                   → theComposite m ≡ theComposite n → m ≡ n
  theComposite-inj = Co.compFun-inj

-- A fully concrete instance, at the numeral zero.
module WitnessZero = Witness (numeralL 0)
