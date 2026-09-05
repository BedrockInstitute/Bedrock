{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.725] PROBE.  The equation [LJ-1.698] named as its first miss,
--                     carved ≡ fst (hierL γ …), from table-sat.
-- Lands nothing in src/.
--
--   THE OBLIGATION  carved-is-hier, at the brief's type with [LJ-1.724]'s
--                   table-sat as the only hypothesis.  NOT INHABITED.
--                   review-of-carved-is-hier.md states the stop: the
--                   reverse inclusion waits on a bounded reading of the
--                   tower graph the tree does not carry.
--   DELIVERED       table-sat: the hypothesis type, [LJ-1.724]'s
--                     obligation verbatim.
--                   hierL-into-carved: hierL ⊆ carved, REAL, from
--                     table-sat alone.
--                   carved-member-read: a member of carved read as the
--                     witness (u ∈ γ, z ∈ Lset γ, pair equation,
--                     relativized GraphAt conjunct).  REAL.
--                   stage-read: the missing fact.  STATED, NOT
--                     INHABITED.
--                   carved-into-hierL-from: carved ⊆ hierL from
--                     stage-read.  REAL, as an assembly.
--                   carved-is-hier-from: the equation from table-sat
--                     and stage-read.  REAL, as an assembly.
--
-- ONE Agda process per run, GHCRTS wide caliber, set on the pane by
-- the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-725.Probe725 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula )
open import FOL.LevyHierarchy using ( Δ₀ )
open import FOL.Manipulation.Relativize using ( relativize; Δ₀-relativize )
open import Cubical.Data.FinData using ( zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _⊆_; extensionality; ∈-asFiber; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import FOL.Semantics (hPropAlgebra (ℓ-suc ℓ)) 𝒮ᵥ using ( _^_ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; IsOrd; Lset; Lset→isL; isL-trans )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import FOL.Manipulation.Bounding using ( BoundedFo )
open import L.Axioms.Separation {ℓ} lem
  using ( mkBoundedFo; Below′; module AtStage )
import FOL.Absoluteness
module AbsL725 = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL725 using () renaming ( _⊨ᵐ_ to _⊨_ )
open import L.Coding.Model {ℓ} using ( prAtL; prAtL-adequate )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem
  using ( hierL; hierL-spec; IsHier; Recorded; hier-in )
open import LJ-1-698.Probe698 {ℓ} lem
  using ( recordedFo; module Carved )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module At (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) = Carved γ oγ hγ


-- =====================================================================
-- SECTION 1.  THE HYPOTHESIS.  [LJ-1.724]'s obligation, verbatim.
--
-- The brief takes table-sat as a HYPOTHESIS, typed as [LJ-1.724]'s
-- obligation (agents/tasks/LJ-1-724/LJ-1.724.md, THE OBLIGATION).
-- [LJ-1.724]'s brief writes membership as ∈ˢ over 𝒮ᵥ, whose ∈ˢ is
-- `_∈_` on V by definition (src/V/Hierarchy.lagda.md:83), so the type
-- here is written with `_∈_` and is the same type.
-- =====================================================================

table-sat : Type (ℓ-suc ℓ)
table-sat =
    (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
    (x : V ℓ) → ⟨ x ∈ γ ⟩
  → ⟨ pr x (Lset x) ∈ At.carved γ oγ hγ ⟩


-- =====================================================================
-- SECTION 2.  THE FIRST INCLUSION, REAL.  hierL ⊆ carved, from
-- table-sat alone.
--
-- A member w of fst (hierL γ hγ oγ) is constructible (isL-trans, the
-- class is transitive), so it can be made an element of S; the spec
-- of hierL turns its membership into Recorded γ w; Recorded hands
-- over c ∈ γ with w ≡ pr c (Lset c); table-sat puts that pair in
-- carved; transport along the equation.
-- =====================================================================

hierL-into-carved :
    table-sat
  → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
    (w : V ℓ) → ⟨ w ∈ fst (hierL γ hγ oγ) ⟩
  → ⟨ w ∈ At.carved γ oγ hγ ⟩
hierL-into-carved ts γ oγ hγ w w∈ =
  PT.rec (snd (w ∈ At.carved γ oγ hγ))
    (λ { (c , (c∈ , peq)) →
      subst (λ t → ⟨ t ∈ At.carved γ oγ hγ ⟩) (sym peq)
        (ts γ oγ hγ (fst c) c∈) })
    (subst ⟨_⟩ (hierL-spec γ hγ oγ (w , isLw)) w∈)
  where
  isLw : ⟨ isL w ⟩
  isLw = isL-trans w∈ (hierL γ hγ oγ .snd)


-- =====================================================================
-- SECTION 3.  READING A MEMBER OF carved.  REAL.
--
-- imageOut turns membership of carved into satisfaction of φᵣ, the
-- relativized recording, read over 𝒮ʟ.  φᵣ computes to
--
--   ∃̇∈ (con (γ , hγ))
--     (∃̇∈ (con (LsetS γ oγ))
--       ( prAtL 2 1 0
--         ∧̇ relativize (LsetS γ oγ) (GraphAt zero (suc zero)) ))
--
-- because relativize leaves bounded quantifiers and atoms alone
-- (src/FOL/Manipulation/Relativize.lagda.md:48-60) and prAtL is all
-- bounded (sglAt is, src/L/Coding/Base.lagda.md:249).  So the two
-- existentials are plain truncations, the pair conjunct reads through
-- prAtL-adequate, and only the last conjunct stays a satisfaction.
-- =====================================================================

carved-read : (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) (w : V ℓ)
            → Type (ℓ-suc ℓ)
carved-read γ oγ hγ w =
  Σ[ u ∈ S ] (⟨ fst u ∈ γ ⟩
    × (Σ[ z ∈ S ] (⟨ fst z ∈ Lset γ ⟩
      × ( (w ≡ pr (fst u) (fst z))
        × (Σ[ W ∈ S ] ((fst W ≡ w)
          × ⟨ (z ∷ u ∷ W ∷ []) ⊨ relativize (LsetS γ oγ)
                                (LsetGraphAt zero (suc zero)) ⟩ ))))))

carved-member-read :
    (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩) (w : V ℓ)
  → ⟨ w ∈ At.carved γ oγ hγ ⟩
  → ∥ carved-read γ oγ hγ w ∥₁

-- The extraction runs at a NEUTRAL σ, exactly as Separation's own proofs
-- do (src/L/Axioms/Separation.lagda.md:303-326), so no constraint about
-- the stuck stage  bound-of γ oγ hγ .fst  ever reaches the elaborator.
module Fib (σ : V ℓ) (oσ : IsOrd σ) (ψ : Formula S 1)
           (hψ : BoundedFo (Below′ σ) ψ) (dψ : Δ₀ ψ) where
  module St = AtStage σ oσ

  memberIsL : (m : ⟪ Lset σ ⟫) → ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩
  memberIsL m = Lset→isL σ oσ (⟪ Lset σ ⟫↪ m)
    ((∈∈ₛ {a = ⟪ Lset σ ⟫↪ m} {b = Lset σ} .snd) (∈ₛ⟪ Lset σ ⟫↪ m))

  extract : (w : V ℓ) → ⟨ w ∈ St.carve (St.RL.liftFo ψ hψ) ⟩
          → Σ[ m ∈ ⟪ Lset σ ⟫ ]
              (⟪ Lset σ ⟫↪ m ≡ w)
            × (Σ[ xL ∈ ⟨ isL (⟪ Lset σ ⟫↪ m) ⟩ ]
                ⟨ ((⟪ Lset σ ⟫↪ m , xL) ∷ []) ⊨ ψ ⟩)
  extract w mem = fib .fst , (fib .snd , (memberIsL (fib .fst) , sat))
    where
    fib = ∈-asFiber {a = w} {b = Lset σ}
            (St.carve⊆ (St.RL.liftFo ψ hψ) w mem)
    xL : ⟨ isL (⟪ Lset σ ⟫↪ (fib .fst)) ⟩
    xL = memberIsL (fib .fst)
    mem' : ⟨ ⟪ Lset σ ⟫↪ (fib .fst) ∈ St.carve (St.RL.liftFo ψ hψ) ⟩
    mem' = subst (λ t → ⟨ t ∈ St.carve (St.RL.liftFo ψ hψ) ⟩)
             (sym (fib .snd)) mem
    sat : ⟨ ((⟪ Lset σ ⟫↪ (fib .fst) , xL) ∷ []) ⊨ ψ ⟩
    sat = St.imageOut ψ hψ dψ (fib .fst) xL mem'

carved-member-read γ oγ hγ w mem =
  step1 sat
  where
  module Cγ = Carved γ oγ hγ

  dφ₀ : Δ₀ Cγ.φᵣ
  dφ₀ = Δ₀-relativize (LsetS γ oγ) (recordedFo (γ , hγ))

  module Fibγ = Fib Cγ.σ Cγ.oσ Cγ.φᵣ Cγ.hφ dφ₀

  m : ⟪ Lset Cγ.σ ⟫
  m = Fibγ.extract w mem .fst

  eqw : ⟪ Lset Cγ.σ ⟫↪ m ≡ w
  eqw = Fibγ.extract w mem .snd .fst

  xL : ⟨ isL (⟪ Lset Cγ.σ ⟫↪ m) ⟩
  xL = Fibγ.extract w mem .snd .snd .fst

  e₀ : S ^ 1
  e₀ = (⟪ Lset Cγ.σ ⟫↪ m , xL) ∷ []

  sat : ⟨ e₀ ⊨ Cγ.φᵣ ⟩
  sat = Fibγ.extract w mem .snd .snd .snd

  step1 : ⟨ e₀ ⊨ Cγ.φᵣ ⟩ → ∥ carved-read γ oγ hγ w ∥₁
  step1 s =
    PT.rec squash₁
      (λ { (u , (u∈ᵧ , uBody)) → PT.rec squash₁ (inner u u∈ᵧ) uBody })
      s
    where
    inner : (u : S) → ⟨ fst u ∈ γ ⟩
          → (Σ[ z ∈ S ] (⟨ fst z ∈ Lset γ ⟩
              × (⟨ (z ∷ u ∷ e₀) ⊨ prAtL (suc (suc zero)) (suc zero) zero ⟩
                × ⟨ (z ∷ u ∷ e₀) ⊨ relativize (LsetS γ oγ)
                                    (LsetGraphAt zero (suc zero)) ⟩)))
          → ∥ carved-read γ oγ hγ w ∥₁
    inner u u∈ᵧ (z , (z∈A , (pSat , gsat))) =
      ∣ ( u , (u∈ᵧ
        , z , (z∈A
          , ( sym eqw ∙ pairEq
            , ( (⟪ Lset Cγ.σ ⟫↪ m , xL) , (eqw , gsat) ) )) )) ∣₁
      where
      pairEq : ⟪ Lset Cγ.σ ⟫↪ m ≡ pr (fst u) (fst z)
      pairEq = subst ⟨_⟩
        (prAtL-adequate (suc (suc zero)) (suc zero) zero (z ∷ u ∷ e₀))
        pSat


-- =====================================================================
-- SECTION 4.  THE MISSING FACT.  STATED, NOT INHABITED.
--
-- Everything read out of carved in section 3 is usable EXCEPT the last
-- conjunct: it is a satisfaction of the RELATIVIZED tower graph.  The
-- tree's graph reading, Lset-only (src/L/Hierarchy.lagda.md:334-337),
-- consumes the UNRELATIVIZED satisfaction over 𝒮ᵥ ↾ isL, the same
-- _⊨ᵐ_ this file renamed to _⊨_ (src/L/Hierarchy.lagda.md:79).  What
-- stands between is not the syntax gap: relativize-correct
-- (src/FOL/Manipulation/Relativize.lagda.md:143) turns the conjunct
-- into the A-bounded semantics at A = Lset γ.  What is missing is the
-- UNGUARDING spine: every unbounded ∀ of LsetGraphAt (domAt's is one,
-- src/L/Coding/Base.lagda.md:278-279; extAt's and ApproxAt's are the
-- others) is guarded at A under that semantics, and the un-guarded
-- readings approx-val and step-Lset consume instantiate them at
-- members of members of A.  Closing that needs set-transitivity of
-- Lset γ (assemblable from Lset-out + Lset-mono,
-- src/L/Constructible.lagda.md:346, :365, but not landed as one
-- lemma) and a bespoke conversion over the whole graph formula.  The
-- model knows the statement is true at the frame's earliest stage
-- ([LJ-1.704], report, five sentences); the tree does not carry its
-- content lemma.  The name stage-read is the precise shape of what is
-- missing.
-- =====================================================================

stage-read : Type (ℓ-suc ℓ)
stage-read =
    (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
    (u z W : S) → ⟨ fst u ∈ γ ⟩ → ⟨ fst z ∈ Lset γ ⟩
  → ⟨ (z ∷ u ∷ W ∷ []) ⊨ relativize (LsetS γ oγ)
                        (LsetGraphAt zero (suc zero)) ⟩
  → fst z ≡ Lset (fst u)


-- =====================================================================
-- SECTION 5.  THE SECOND INCLUSION, FROM stage-read.  REAL, AS AN
-- ASSEMBLY.
-- =====================================================================

carved-into-hierL-from :
    stage-read
  → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
    (w : V ℓ) → ⟨ w ∈ At.carved γ oγ hγ ⟩
  → ⟨ w ∈ fst (hierL γ hγ oγ) ⟩
carved-into-hierL-from sr γ oγ hγ w mem =
  PT.rec (snd (w ∈ fst (hierL γ hγ oγ))) close
    (carved-member-read γ oγ hγ w mem)
  where
  close : carved-read γ oγ hγ w
        → ⟨ w ∈ fst (hierL γ hγ oγ) ⟩
  close (u , (u∈ , (z , (z∈A , (pweq , (_ , (_ , gsat))))))) =
    subst (λ t → ⟨ t ∈ fst (hierL γ hγ oγ) ⟩)
      (sym (pweq ∙ cong (pr (fst u)) (sr γ oγ hγ u z _ u∈ z∈A gsat)))
      (hier-in γ oγ (hierL γ hγ oγ) (hierL-spec γ hγ oγ) u u∈)


-- =====================================================================
-- SECTION 6.  THE EQUATION, FROM BOTH.  REAL, AS AN ASSEMBLY.
-- =====================================================================

carved-is-hier-from :
    table-sat → stage-read
  → (γ : V ℓ) (oγ : IsOrd γ) (hγ : ⟨ isL γ ⟩)
  → At.carved γ oγ hγ ≡ fst (hierL γ hγ oγ)
carved-is-hier-from ts sr γ oγ hγ =
  extensionality (At.carved γ oγ hγ) (fst (hierL γ hγ oγ))
    ( (λ x x∈ₛ → (∈∈ₛ {a = x} {b = fst (hierL γ hγ oγ)} .fst)
                    (carved-into-hierL-from sr γ oγ hγ x
                      ((∈∈ₛ {a = x} {b = At.carved γ oγ hγ} .snd) x∈ₛ)))
    , (λ x x∈ₛ → (∈∈ₛ {a = x} {b = At.carved γ oγ hγ} .fst)
                    (hierL-into-carved ts γ oγ hγ x
                      ((∈∈ₛ {a = x} {b = fst (hierL γ hγ oγ)} .snd) x∈ₛ))) )


-- =====================================================================
-- SECTION 7.  THE OBLIGATION NAME IS ABSENT ON PURPOSE.
--
-- carved-is-hier at the brief's type takes table-sat and NOTHING
-- else.  Sections 2-6 measure that table-sat pays the first inclusion
-- whole, and that the second costs stage-read, a bounded reading of
-- the tower graph that no landed lemma supplies.  Inhabiting the name
-- with stage-read as a second hypothesis would report the brief's
-- target as discharged when it is not; review-of-carved-is-hier.md
-- states the stop instead.
-- =====================================================================
