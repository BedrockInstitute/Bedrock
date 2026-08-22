{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.557]  An internal code for one member of the successor.
--
-- W3 IS SECTION 1, AND IT WAS WRITTEN FIRST AND TYPECHECKED ALONE.
-- The slice is agents/tasks/LJ-1-557/runs/W3.agda, runs w3-1.out to
-- w3-3.out, exit 0, 1.50 s / 1.46 s / 1.48 s.
--
-- THE OBLIGATION IS INHABITED.  `member-code-into-kappa` is section 4.
-- This file carries NO hole and NO postulate, so every reduction in it
-- is a measurement and not a claim ([LJ-1.533]'s discipline, kept by
-- [LJ-1.549] and [LJ-1.552]).  Nothing lands in src/.
--
-- WHAT THIS FILE MEASURES, IN ONE LINE EACH.
--
--   Section 1.  W3, AND IT IS THE D-10.  The stage
--               `InternalLeastCard` selects over, at this frame, TYPE
--               ONLY, with the one bridge that is free and the one
--               that is not.
--   Section 2.  THE TWO CHECKS, ANSWERED IN AGDA WHERE AGDA CAN
--               ANSWER THEM.  Check 1 is NO and check 2 is NO, BOTH
--               ABOUT `InternalLeastCard` AND NEITHER ABOUT THE
--               OBLIGATION.  The two NOs name the frame that works.
--   Section 3.  THE TWO FREE CODES.  `incl-code` is one application
--               of `InclGraph`, and it pays BOTH the identity code on
--               `a` and the ordinal inclusion `c ⊆ κ`.  `comp-code`
--               is one application of `Comp`.
--   Section 4.  THE OBLIGATION.  `InternalCardOf` runs the selection
--               at `LeastCardInjL`'s frame, with the code quantified
--               over the whole L-carrier, and the leastness of δ then
--               refutes the bad branch INTERNALLY.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-557.Probe557 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-irrefl )
open import V.Presentation {ℓ} using ( member; fiber )
open import V.Model {ℓ} using ( ∈sucV-elim )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; IsOrd; Lset )
open import L.Ordinal {ℓ} using ( mem-ord; suc-ord )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Cardinal {ℓ} lem
  using ( InjCode; IsCardinalL; module SiteBound; module LeastCardInjL )
open import L.GCH {ℓ} lem using ( SuccCardL )
open import L.InjChain {ℓ} lem using ( module InclGraph; module Comp )
open import L.Choice.Step {ℓ} lem using ( Mem; orderAt )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; IsLeast; leastOf; module SWO )

open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Sigma using ( _×_; Σ≡Prop )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )
open hPropStructure 𝒮ʟ using ( S )

-- =====================================================================
-- SECTION 0.  THE OBLIGATION'S PREDICATE, ONCE.
--
--   `Code a b` is the brief's own conclusion, named so that the two
--   frames of section 1 can be compared as types.  The code is
--   quantified over the WHOLE L-carrier: the obligation carries no
--   stage side condition on `F`, and that is the whole difference
--   between it and `InternalLeastCard.Good`.
-- =====================================================================

Code : S → S → Type (ℓ-suc ℓ)
Code a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁

-- A path of the L-carrier is a path of its first component: `isL` is an
-- hProp (src/L/Constructible.lagda.md:376).  Written once, because
-- `Σ≡Prop` cannot infer the family from the V-path alone
-- (runs/red-2.out).
S-path : (u v : S) → fst u ≡ fst v → u ≡ v
S-path u v = Σ≡Prop (λ x → snd (isL x))

-- =====================================================================
-- SECTION 1.  W3.  THE STAGE `InternalLeastCard` SELECTS OVER, AT THIS
-- FRAME, TYPE ONLY.  Written first, typechecked alone; this section IS
-- runs/W3.agda.
-- =====================================================================

module Frame (a : S) (oa : IsOrd (fst a)) where

  -- THE STAGE.  `InternalLeastCard`'s site is `SiteBound`'s β
  -- (src/L/Cardinal.lagda.md:237), and `SiteBound` is `stageBound`
  -- (src/L/Cardinal.lagda.md:163-169).
  open SiteBound a using ( β; oβ; up )

  site : V ℓ
  site = β

  -- THE ORDER `InternalLeastCard` SELECTS WITH
  -- (src/L/Cardinal.lagda.md:247, :249).  It is `orderAt`, the BIRTH
  -- order on the members of a stage (src/L/Choice/Step.lagda.md:730,
  -- built from `bornAt` at :690-710).
  sel : SWO (Mem (Lset β))
  sel = orderAt β oβ

  -- WHAT `InternalLeastCard.Good` DEMANDS at this frame, in the
  -- direction the obligation wants (src/L/Cardinal.lagda.md:239-243,
  -- transposed).  THE CODE IS A MEMBER OF THE STAGE.
  Demand : Mem (Lset β) → Type (ℓ-suc ℓ)
  Demand γ = ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a (up γ) ∥₁

  -- THE ONE FREE DIRECTION: a stage-bounded code IS a code.
  bridge : (γ : Mem (Lset β)) → Demand γ → Code a (up γ)
  bridge γ = PT.map (λ { (F , c) → up F , c })

  -- THE OTHER DIRECTION, TYPE ONLY.  This is the `F` conjunct
  -- [LJ-1.425] left as a hole (agents/tasks/LJ-1-425/Probe425.agda:92,
  -- runs/final-hole.out, exit 42).  NOTHING IN THIS FILE INHABITS IT
  -- and no term of this file is named `Converse`.
  Converse : Type (ℓ-suc ℓ)
  Converse = (γ : Mem (Lset β)) → Code a (up γ) → Demand γ

  -- THE ORDER THIS TASK SELECTS WITH INSTEAD: `LeastCardInjL`'s sealed
  -- `w` (src/L/Cardinal.lagda.md:96-98), whose comparison IS ambient
  -- membership (`w-lt`, src/L/Cardinal.lagda.md:102-105).
  private
    module M = LeastCardInjL a oa

  memOrd : SWO ⟪ sucV (fst a) ⟫
  memOrd = M.w

  -- CHECK 2, AS A TYPE.  `w-lt` says the comparison of `memOrd` IS
  -- membership, so leastness at `memOrd` is leastness at `∈`.  The
  -- tree states NO such equation for `sel`, and `IsCardinalL`
  -- (src/L/Cardinal.lagda.md:230-232) asks for leastness at `∈`.
  order-is-membership : (m n : ⟪ sucV (fst a) ⟫)
    → SWO._<∙_ memOrd m n
     ≡ ⟨ ⟪ sucV (fst a) ⟫↪ m ∈ˢ ⟪ sucV (fst a) ⟫↪ n ⟩
  order-is-membership = M.w-lt

-- =====================================================================
-- SECTION 2.  THE TWO FREE CODES.
--
--   ONE application of `InclGraph` and ONE of `Comp`, both at the
--   generic carrier, so that the four module applications the naive
--   route would make become two.  `Carve`'s `Small` instance is
--   private and sealed (src/L/InjChain.lagda.md:549-556), and no term
--   below opens it: [LJ-1.425] recorded an unsealed `Small`
--   application as the 8g warning.
-- =====================================================================

-- ROW 3 of the chain, read as a code.  The subset witness is the only
-- input, so the SAME term pays the identity on `a` and the ordinal
-- inclusion `c ⊆ κ`.
incl-code : (D C : S) → ((z : V ℓ) → ⟨ z ∈ fst D ⟩ → ⟨ z ∈ fst C ⟩)
          → Σ[ F ∈ S ] InjCode F D C
incl-code D C sub = I.G , (I.sv , (I.dm , (I.ij , I.ran)))
  where
  module I = InclGraph D C sub

-- ROW 1 of the chain, read as a code.
comp-code : (D E C : S)
          → Σ[ F ∈ S ] InjCode F D E → Σ[ H ∈ S ] InjCode H E C
          → Σ[ K ∈ S ] InjCode K D C
comp-code D E C (F , (svF , (dmF , (ijF , ranF))))
                (H , (svH , (dmH , (ijH , ranH)))) =
  K.K , (K.svK , (K.dmK , (K.ijK , K.ranK)))
  where
  module K = Comp D E C F H svF dmF ijF ranF svH dmH ijH ranH

-- THE IDENTITY CODE, FREE AT EVERY L-ELEMENT.  This is the term
-- `InternalLeastCard`'s `nonempty` could not place in `Lset β`
-- ([LJ-1.425]'s stop).  Here nothing asks where it lives.
id-code : (a : S) → Code a a
id-code a = ∣ incl-code a a (λ _ h → h) ∣₁

-- =====================================================================
-- SECTION 3.  THE INTERNAL CARDINALITY OF ONE L-ELEMENT.
--
--   `LeastCardInjL`'s frame (src/L/Cardinal.lagda.md:61-77) with the
--   AMBIENT injection predicate replaced by the INTERNAL code
--   predicate.  Everything else is that module's: its crossing `up`,
--   its sealed membership order `w`, and its one read `w-lt`.  So the
--   selection costs one `leastOf` and nothing is rebuilt.
-- =====================================================================

module InternalCardOf (a : S) (oa : IsOrd (fst a)) where

  open LeastCardInjL a oa using ( up; self; self-eq; w; w-lt )

  upPath : (m : ⟪ sucV (fst a) ⟫) (d : S)
         → ⟪ sucV (fst a) ⟫↪ m ≡ fst d → up m ≡ d
  upPath m d = S-path (up m) d

  Good : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
  Good γ = Code a (up γ) , squash₁

  nonempty : ∥ Σ[ γ ∈ ⟪ sucV (fst a) ⟫ ] ⟨ Good γ ⟩ ∥₁
  nonempty = ∣ self , subst (Code a) (sym (upPath self a self-eq)) (id-code a) ∣₁

  least : Σ[ γ ∈ ⟪ sucV (fst a) ⟫ ] IsLeast w Good γ
  least = leastOf w lem Good nonempty

  γ-card : ⟪ sucV (fst a) ⟫
  γ-card = fst least

  -- THE INTERNAL CARDINALITY OF `a`, as an L-element.
  c : S
  c = up γ-card

  c∈sa : ⟨ fst c ∈ˢ sucV (fst a) ⟩
  c∈sa = member (sucV (fst a)) γ-card

  oc : IsOrd (fst c)
  oc = mem-ord {A = sucV (fst a)} (suc-ord oa) (fst c) c∈sa

  -- THE WITNESS: some L-element codes `a` into `c`, still truncated.
  c-code : Code a c
  c-code = fst (snd least)

  c-min : (b : ⟪ sucV (fst a) ⟫) → ⟨ Good b ⟩
        → (SWO._<∙_ w b γ-card → Empty.⊥)
  c-min = snd (snd least)

  -- LEASTNESS IN THE MEMBERSHIP ORDER, which is what `IsCardinalL`
  -- asks for.  `LeastCardInjL.κ-min-at` (src/L/Cardinal.lagda.md:
  -- 141-155) is the same five lines at the ambient predicate; `w-lt`
  -- is what turns the sealed comparison back into membership.
  c-min-at : (d : S) → ⟨ fst d ∈ˢ fst c ⟩ → Code a d → Empty.⊥
  c-min-at d d∈c h = c-min b bGood b<γ
    where
    d∈sa : ⟨ fst d ∈ˢ sucV (fst a) ⟩
    d∈sa = suc-ord oa .fst {x = fst c} {y = fst d} d∈c c∈sa
    b : ⟪ sucV (fst a) ⟫
    b = fiber (sucV (fst a)) d∈sa .fst
    bd : ⟪ sucV (fst a) ⟫↪ b ≡ fst d
    bd = fiber (sucV (fst a)) d∈sa .snd
    bGood : ⟨ Good b ⟩
    bGood = subst (Code a) (sym (upPath b d bd)) h
    b<γ : SWO._<∙_ w b γ-card
    b<γ = transport (λ i → sym (w-lt b γ-card) i)
            (subst (λ z → ⟨ z ∈ˢ fst c ⟩) (sym bd) d∈c)

  -- CHECK 2, PAID.  `c` is an INTERNAL cardinal.  The bad branch of
  -- the leastness is refuted by COMPOSITION and not by an ambient
  -- counting argument: a code `c ↪ d` below `c` composes with the
  -- code `a ↪ c` to beat the selection.
  cardL : IsCardinalL c
  cardL d d∈c h =
    PT.rec Empty.isProp⊥ (λ hcd → PT.rec Empty.isProp⊥ (step hcd) c-code) h
    where
    step : Σ[ H ∈ S ] InjCode H c d → Σ[ F ∈ S ] InjCode F a c → Empty.⊥
    step hcd hac = c-min-at d d∈c ∣ comp-code a c d hac hcd ∣₁

-- =====================================================================
-- SECTION 4.  THE OBLIGATION.
--
--   The brief's type, transcribed once.  The shape is [LJ-1.552]'s
--   `member-into-kappa` (agents/tasks/LJ-1-552/Probe552.agda:158-194)
--   with EVERY ambient object replaced by a coded one:
--   `LeastCardInjL` by `InternalCardOf`, `card-of` plus
--   `ambient→internal` by `InternalCardOf.cardL`, and `ord-emb` plus
--   `comp-inj` by `incl-code` plus `comp-code`.
-- =====================================================================

member-code-into-kappa :
    (δ κ : S) → SuccCardL δ κ → (a : S) → ⟨ fst a ∈ fst δ ⟩
  → ∥ Σ[ F ∈ S ] InjCode F a κ ∥₁
member-code-into-kappa δ κ (oδ , (_ , (κ∈δ , leastδ))) a a∈δ =
  go (ord-tri (fst M.c) M.oc (fst κ) oκ)
  where
  oa : IsOrd (fst a)
  oa = mem-ord {A = fst δ} oδ (fst a) a∈δ
  oκ : IsOrd (fst κ)
  oκ = mem-ord {A = fst δ} oδ (fst κ) κ∈δ
  module M = InternalCardOf a oa

  -- If κ were BELOW the internal cardinality of `a`, then δ would be
  -- below it too, by the fourth component of `SuccCardL`
  -- (src/L/GCH.lagda.md:51-52); and the cardinality of `a` never
  -- leaves `a`.  `∈sucV-elim`'s motive lives in `Type (ℓ-suc ℓ)` and
  -- `Empty.⊥` does not, so the conclusion is the lifted empty type
  -- ([LJ-1.549] item 4, [LJ-1.552] runs/w3-red-1.out).
  absurd : ⟨ fst κ ∈ˢ fst M.c ⟩ → Empty.⊥* {ℓ-suc ℓ}
  absurd κ∈c = ∈sucV-elim {A = fst a} {x = fst M.c}
                 Empty.isProp⊥* M.c∈sa below same
    where
    a∈c : ⟨ fst a ∈ˢ fst M.c ⟩
    a∈c = leastδ M.c M.oc M.cardL κ∈c a a∈δ
    below : ⟨ fst M.c ∈ˢ fst a ⟩ → Empty.⊥* {ℓ-suc ℓ}
    below c∈a = Empty.rec (∈-irrefl (fst a) (oa .fst a∈c c∈a))
    same : fst M.c ≡ fst a → Empty.⊥* {ℓ-suc ℓ}
    same e = Empty.rec (∈-irrefl (fst a)
               (subst (λ v → ⟨ fst a ∈ˢ v ⟩) e a∈c))

  go : Tri (fst M.c) (fst κ) → ∥ Σ[ F ∈ S ] InjCode F a κ ∥₁
  go (inl c∈κ) = PT.map compose M.c-code
    where
    incl : Σ[ H ∈ S ] InjCode H M.c κ
    incl = incl-code M.c κ (λ _ z∈c → oκ .fst z∈c c∈κ)
    compose : Σ[ F ∈ S ] InjCode F a M.c → Σ[ F ∈ S ] InjCode F a κ
    compose hac = comp-code a M.c κ hac incl
  go (inr (inl e)) =
    subst (Code a) (S-path M.c κ e) M.c-code
  go (inr (inr κ∈c)) = Empty.rec* (absurd κ∈c)
