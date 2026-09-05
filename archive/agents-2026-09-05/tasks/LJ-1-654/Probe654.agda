{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.654] PROBE.  `PiReflectsOrd`: the collapse REFLECTS ordinality
-- along the hull.  It runs in agents/tasks/LJ-1-654/ and lands nothing
-- in src/.
--
-- THE OBLIGATION IS `PiReflectsOrd`, at the foot of this file.
--
-- WHAT THE TASK MEASURES, IN ONE SENTENCE.  The fact [LJ-1.649] named
-- and did not build is TRUE, it costs two lemmas and three formulas,
-- and with it [LJ-1.649]'s `levelin-from-647` loses its fifth
-- hypothesis at every consumer.
--
-- THE TYPE IS THE PREDECESSOR'S, TAKEN BY IMPORT AND NOT BY COPY.
-- `fifth` below inhabits `LJ-1-649.Probe649`'s own `PiReflectsOrd`
-- (agents/tasks/LJ-1-649/Probe649.agda:222-223), so the standing coder
-- clause "a module hypothesis taken from a predecessor is the type that
-- predecessor delivered" is answered by the typechecker.
--
-- WHY THE PROOF NEEDS THE HULL AND NOT ONLY THE COLLAPSE.  The hull `M`
-- is NOT transitive, so a member of a hull member need not be a hull
-- member, and `IE.π∈-bwd` wants BOTH endpoints inside `M`
-- (src/V/Collapse.lagda.md:282-283).  [LJ-1.649] section 4.1 flagged
-- exactly this and did not price it.  The cure is the hull's own
-- definable closure: replace the global witness by a hull witness of
-- the SAME formula before crossing to the range.  That replacement is
-- `lift-to-hull`, written once and generic in the formula.
--
-- Nothing is postulated.  Nothing is holed.  Nothing lands in src/.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-654.Probe654 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; var; con; _∈̇_; _∧̇_; ¬̇_; ∃̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; isTransV; isPropIsTransV; Lset )
open import L.Hull {ℓ} lem using ( module AtStage )
open import L.BoundedSubset {ℓ} lem using ( module HullExt )
open import V.Collapse {ℓ} using ( module Collapse; isExt )

import LJ-1-649.Probe649

open import Cubical.Data.Sigma using ( Σ-syntax; _×_ )
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- [LJ-1.649]'s probe at this file's level and this file's `lem`.
module Pred = LJ-1-649.Probe649 {ℓ} lem

-- =====================================================================
-- THE TELESCOPE.  [LJ-1.649]'s HullStage verbatim
-- (agents/tasks/LJ-1-649/Probe649.agda:61-64), which is
-- src/L/BoundedSubset.lagda.md:903-914.  `succλ` is unused by every
-- term in this file and is KEPT, because the consumer site carries it
-- and the consumer must lift these terms verbatim.
--
-- TWO MODULES ARE ADDED OVER [LJ-1.649]'s FRAME, and they are exactly
-- the two tree facts [LJ-1.649] section 4.1 named:
--   `HullExt`      src/L/BoundedSubset.lagda.md:1235, `hullExt` at :1340
--   `C.InjExt`     src/V/Collapse.lagda.md:220, `π∈-bwd` at :282
-- `HullExt`'s telescope is this one MINUS `succλ`, so its `M` is this
-- `M` and Agda checks that rather than being told it.
-- =====================================================================

module HullStage (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module ASt = AtStage lam ordλ
  module H = ASt.Hull X X⊆L ∅∈λ

  M : S
  M = H.T.Hull

  module C = Collapse M

  module HE = HullExt lam ordλ X X⊆L ∅∈λ

  hullExt : isExt M
  hullExt = HE.hullExt

  module IE = C.InjExt hullExt

  open H.T using ( Code; val )

  -- satisfaction of a one-variable code formula at one stage element,
  -- relativized to the stage.  This abbreviation is the whole of the
  -- syntax bookkeeping in this file
  Sat : ASt.SL → Formula Code 1 → Type (ℓ-suc ℓ)
  Sat a φ = ⟨ (a ∷ []) ASt.AbsL.⊨ᵐ (mapFo val φ) ⟩

  -- ===================================================================
  -- W2 (DD4).  THE MATHEMATICS ONCE, AT A GENERIC FORMULA.  The hull is
  -- closed under definable witnesses, so a GLOBAL witness of any
  -- one-variable formula over the hull's codes can be replaced by a
  -- HULL member satisfying the same formula.  Every use of the hull in
  -- this file goes through this one term, and it is `H.hull-closed`
  -- (src/L/Hull.lagda.md:415-417) with the truncation introduced.
  --
  -- It is instantiated THREE times below, at `φ-deep`, `φ-mid` and
  -- `φ-bad`, and it is the only place the hull's closure is spent.
  -- ===================================================================

  lift-to-hull : (φ : Formula Code 1) (a : ASt.SL) → Sat a φ
               → ∥ Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩ × Sat b φ) ∥₁
  lift-to-hull φ a sat = H.hull-closed φ ∣ a , sat ∣₁

  -- ===================================================================
  -- THE THREE FORMULAS.  Each has ONE free variable, `var zero`, which
  -- is the slot the hull fills.  De Bruijn: under `∃̇`, `var zero` is
  -- the newly bound variable and the outer ones shift by `suc`.
  -- ===================================================================

  -- "w sits one level too deep in c":  ∃t (w ∈ t ∧ t ∈ c) ∧ ¬ (w ∈ c)
  φ-deep : Code → Formula Code 1
  φ-deep c = (∃̇ ((var (suc zero) ∈̇ var zero) ∧̇ (var zero ∈̇ con c)))
           ∧̇ (¬̇ (var zero ∈̇ con c))

  -- "w is a member of c holding d":  d ∈ w ∧ w ∈ c.  This is the second
  -- pass, and it is what makes the INTERMEDIATE set a hull member too;
  -- `φ-deep` alone only lands the lower endpoint
  φ-mid : Code → Code → Formula Code 1
  φ-mid c d = (con d ∈̇ var zero) ∧̇ (var zero ∈̇ con c)

  -- "w is a non-transitive member of c":
  --   ∃u ∃v ((v ∈ u ∧ u ∈ w) ∧ ¬ (v ∈ w)) ∧ w ∈ c
  φ-bad : Code → Formula Code 1
  φ-bad c = (∃̇ (∃̇ (((var zero ∈̇ var (suc zero))
                   ∧̇ (var (suc zero) ∈̇ var (suc (suc zero))))
                  ∧̇ (¬̇ (var zero ∈̇ var (suc (suc zero)))))))
          ∧̇ (var zero ∈̇ con c)

  -- ===================================================================
  -- STEP 1.  THE COLLAPSE REFLECTS TRANSITIVITY AT A HULL MEMBER.
  --
  -- Take `u ∈ y` and `v ∈ u`, and suppose `v ∉ y`.  Neither `u` nor `v`
  -- need be a hull member, so neither `π∈-fwd` nor `π∈-bwd` can be
  -- applied to them.  `lift-to-hull` at `φ-deep` replaces `v` by a hull
  -- member `v'` with the same defect; `lift-to-hull` at `φ-mid` then
  -- replaces `u` by a hull member `u'` holding THAT `v'`.  Now both
  -- endpoints are inside `M`, the range's transitivity fires, and
  -- injectivity carries the membership back.  The contradiction is with
  -- the defect `v' ∉ y` that `φ-deep` carried across.
  -- ===================================================================

  trans-reflect : (y : S) → ⟨ y ∈ˢ M ⟩ → isTransV (C.π y) → isTransV y
  trans-reflect y y∈M tπy {u} {v} v∈u u∈y =
    Sum.rec (λ h → h) (λ nh → Empty.rec (bad nh)) (lem (v ∈ˢ y))
    where
    y∈L : ⟨ y ∈ˢ Lset lam ⟩
    y∈L = H.Hull⊆L y y∈M
    u∈L : ⟨ u ∈ˢ Lset lam ⟩
    u∈L = ASt.Ltr u∈y y∈L
    v∈L : ⟨ v ∈ˢ Lset lam ⟩
    v∈L = ASt.Ltr v∈u u∈L

    bad : (⟨ v ∈ˢ y ⟩ → Empty.⊥) → Empty.⊥
    bad nh = PT.rec Empty.isProp⊥ withCode (H.hull-member y y∈M)
      where
      withCode : Σ[ c ∈ Code ] (fst (val c) ≡ y) → Empty.⊥
      withCode (c , ec) =
        PT.rec Empty.isProp⊥ deep (lift-to-hull (φ-deep c) (v , v∈L) sat)
        where
        sat : Sat (v , v∈L) (φ-deep c)
        sat = ∣ (u , u∈L) , (v∈u , subst (λ w → ⟨ u ∈ˢ w ⟩) (sym ec) u∈y) ∣₁
            , λ h → nh (subst (λ w → ⟨ v ∈ˢ w ⟩) ec h)

        -- the lower endpoint, now a hull member, and its code
        deep : Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩ × Sat b (φ-deep c))
             → Empty.⊥
        deep (b , b∈M , (ex , nb)) =
          PT.rec Empty.isProp⊥ withCodeD (H.hull-member (fst b) b∈M)
          where
          v' : S
          v' = fst b
          nv' : ⟨ v' ∈ˢ y ⟩ → Empty.⊥
          nv' h = nb (subst (λ w → ⟨ v' ∈ˢ w ⟩) (sym ec) h)

          withCodeD : Σ[ d ∈ Code ] (fst (val d) ≡ v') → Empty.⊥
          withCodeD (d , ed) = PT.rec Empty.isProp⊥ mid ex
            where
            -- the intermediate set the outer `∃` named.  It is global,
            -- so the second pass is needed
            mid : Σ[ t ∈ ASt.SL ]
                    (⟨ v' ∈ˢ fst t ⟩ × ⟨ fst t ∈ˢ fst (val c) ⟩)
                → Empty.⊥
            mid (t , v'∈t , t∈c) =
              PT.rec Empty.isProp⊥ close (lift-to-hull (φ-mid c d) t sat₂)
              where
              sat₂ : Sat t (φ-mid c d)
              sat₂ = subst (λ w → ⟨ w ∈ˢ fst t ⟩) (sym ed) v'∈t , t∈c

              close : Σ[ q ∈ ASt.SL ] (⟨ fst q ∈ˢ M ⟩ × Sat q (φ-mid c d))
                    → Empty.⊥
              close (q , q∈M , (dq , qc)) = nv' v'∈y
                where
                u' : S
                u' = fst q
                v'∈u' : ⟨ v' ∈ˢ u' ⟩
                v'∈u' = subst (λ w → ⟨ w ∈ˢ u' ⟩) ed dq
                u'∈y : ⟨ u' ∈ˢ y ⟩
                u'∈y = subst (λ w → ⟨ u' ∈ˢ w ⟩) ec qc
                πv'∈πu' : ⟨ C.π v' ∈ˢ C.π u' ⟩
                πv'∈πu' = C.π∈-fwd u' v' v'∈u' b∈M
                πu'∈πy : ⟨ C.π u' ∈ˢ C.π y ⟩
                πu'∈πy = C.π∈-fwd y u' u'∈y q∈M
                v'∈y : ⟨ v' ∈ˢ y ⟩
                v'∈y = IE.π∈-bwd y v' y∈M b∈M (tπy πv'∈πu' πu'∈πy)

  -- ===================================================================
  -- STEP 2.  EVERY MEMBER OF A HULL MEMBER IS TRANSITIVE.
  --
  -- The member `x ∈ y` need not be a hull member either, so the range's
  -- second ordinal conjunct cannot be read at it.  `lift-to-hull` at
  -- `φ-bad` replaces `x` by a hull member `x'` that is a member of `y`
  -- AND carries the same non-transitivity.  At `x'` the range's second
  -- conjunct fires, and STEP 1 turns it back into transitivity of `x'`,
  -- which its own defect contradicts.  Step 1 is used here and nowhere
  -- reproved.
  -- ===================================================================

  mem-trans : (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd (C.π y)
            → (x : S) → ⟨ x ∈ˢ y ⟩ → isTransV x
  mem-trans y y∈M oπy x x∈y {u} {v} v∈u u∈x =
    Sum.rec (λ h → h) (λ nh → Empty.rec (bad nh)) (lem (v ∈ˢ x))
    where
    y∈L : ⟨ y ∈ˢ Lset lam ⟩
    y∈L = H.Hull⊆L y y∈M
    x∈L : ⟨ x ∈ˢ Lset lam ⟩
    x∈L = ASt.Ltr x∈y y∈L
    u∈L : ⟨ u ∈ˢ Lset lam ⟩
    u∈L = ASt.Ltr u∈x x∈L
    v∈L : ⟨ v ∈ˢ Lset lam ⟩
    v∈L = ASt.Ltr v∈u u∈L

    bad : (⟨ v ∈ˢ x ⟩ → Empty.⊥) → Empty.⊥
    bad nh = PT.rec Empty.isProp⊥ withCode (H.hull-member y y∈M)
      where
      withCode : Σ[ c ∈ Code ] (fst (val c) ≡ y) → Empty.⊥
      withCode (c , ec) =
        PT.rec Empty.isProp⊥ got (lift-to-hull (φ-bad c) (x , x∈L) sat)
        where
        sat : Sat (x , x∈L) (φ-bad c)
        sat = ∣ (u , u∈L) , ∣ (v , v∈L) , ((v∈u , u∈x) , nh) ∣₁ ∣₁
            , subst (λ w → ⟨ x ∈ˢ w ⟩) (sym ec) x∈y

        got : Σ[ b ∈ ASt.SL ] (⟨ fst b ∈ˢ M ⟩ × Sat b (φ-bad c))
            → Empty.⊥
        got (b , b∈M , (ex , b∈c)) = PT.rec Empty.isProp⊥ outer ex
          where
          x' : S
          x' = fst b
          x'∈y : ⟨ x' ∈ˢ y ⟩
          x'∈y = subst (λ w → ⟨ x' ∈ˢ w ⟩) ec b∈c
          tx' : isTransV x'
          tx' = trans-reflect x' b∈M
                  (oπy .snd (C.π x') (C.π∈-fwd y x' x'∈y b∈M))

          outer : Σ[ p ∈ ASt.SL ]
                    ∥ Σ[ r ∈ ASt.SL ]
                        ((⟨ fst r ∈ˢ fst p ⟩ × ⟨ fst p ∈ˢ x' ⟩)
                         × (⟨ fst r ∈ˢ x' ⟩ → Empty.⊥)) ∥₁
                → Empty.⊥
          outer (p , inn) = PT.rec Empty.isProp⊥ inner inn
            where
            inner : Σ[ r ∈ ASt.SL ]
                      ((⟨ fst r ∈ˢ fst p ⟩ × ⟨ fst p ∈ˢ x' ⟩)
                       × (⟨ fst r ∈ˢ x' ⟩ → Empty.⊥))
                  → Empty.⊥
            inner (r , ((r∈p , p∈x') , nr)) = nr (tx' r∈p p∈x')

  -- ===================================================================
  -- THE OBLIGATION.  `IsOrd` is a transitive set of transitive sets
  -- (src/L/Constructible.lagda.md:141-142), so it is exactly step 1 at
  -- the range's first conjunct and step 2 at its second.
  -- ===================================================================

  PiReflectsOrd : (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd (C.π y) → IsOrd y
  PiReflectsOrd y y∈M oπy =
    trans-reflect y y∈M (oπy .fst) , mem-trans y y∈M oπy

  -- ===================================================================
  -- BEYOND THE OBLIGATION, AND HERE BECAUSE THE SWEEP FOUND ITS
  -- CONSUMER.  The brief asked for the REFLECTION only.  The four
  -- consumer sites the sweep counts each carry `levelIn` beside a
  -- `cover`, and `cover` PRODUCES `IsOrd γ` at a `γ ∈ˢ C.πX`
  -- (src/L/BoundedSubset.lagda.md:919), which is the FORWARD direction
  -- and not this task's.  So the forward direction is priced here, in
  -- the same frame, while the frame is live.
  --
  -- IT IS MUCH CHEAPER, AND THE REASON IS EXACT: it never leaves the
  -- hull, so it never needs `lift-to-hull`.  `π-member` hands back
  -- preimages that are ALREADY hull members
  -- (src/V/Collapse.lagda.md:63-64), where a member of a hull member
  -- is not.  Injectivity is the only tree fact it spends.
  -- ===================================================================

  trans-preserve : (y : S) → ⟨ y ∈ˢ M ⟩ → isTransV y → isTransV (C.π y)
  trans-preserve y y∈M ty {a} {b} b∈a a∈πy =
    PT.rec (snd (b ∈ˢ C.π y)) go (C.π-member y a a∈πy)
    where
    go : Σ[ u ∈ S ] (⟨ u ∈ˢ M ⟩ × (C.π u ≡ a)) → ⟨ b ∈ˢ C.π y ⟩
    go (u , u∈M , eu) = PT.rec (snd (b ∈ˢ C.π y)) go₂ (C.π-member u b b∈πu)
      where
      b∈πu : ⟨ b ∈ˢ C.π u ⟩
      b∈πu = subst (λ w → ⟨ b ∈ˢ w ⟩) (sym eu) b∈a
      u∈y : ⟨ u ∈ˢ y ⟩
      u∈y = IE.π∈-bwd y u y∈M u∈M
              (subst (λ z → ⟨ z ∈ˢ C.π y ⟩) (sym eu) a∈πy)
      go₂ : Σ[ w ∈ S ] (⟨ w ∈ˢ M ⟩ × (C.π w ≡ b)) → ⟨ b ∈ˢ C.π y ⟩
      go₂ (w , w∈M , ew) =
        subst (λ z → ⟨ z ∈ˢ C.π y ⟩) ew (C.π∈-fwd y w w∈y w∈M)
        where
        w∈u : ⟨ w ∈ˢ u ⟩
        w∈u = IE.π∈-bwd u w u∈M w∈M
                (subst (λ z → ⟨ z ∈ˢ C.π u ⟩) (sym ew) b∈πu)
        w∈y : ⟨ w ∈ˢ y ⟩
        w∈y = ty w∈u u∈y

  PiPreservesOrd : (y : S) → ⟨ y ∈ˢ M ⟩ → IsOrd y → IsOrd (C.π y)
  PiPreservesOrd y y∈M oy = trans-preserve y y∈M (oy .fst) , second
    where
    second : (a : S) → ⟨ a ∈ˢ C.π y ⟩ → isTransV a
    second a a∈πy = PT.rec (isPropIsTransV a) go (C.π-member y a a∈πy)
      where
      go : Σ[ u ∈ S ] (⟨ u ∈ˢ M ⟩ × (C.π u ≡ a)) → isTransV a
      go (u , u∈M , eu) =
        subst isTransV eu (trans-preserve u u∈M (oy .snd u u∈y))
        where
        u∈y : ⟨ u ∈ˢ y ⟩
        u∈y = IE.π∈-bwd y u y∈M u∈M
                (subst (λ z → ⟨ z ∈ˢ C.π y ⟩) (sym eu) a∈πy)

  -- THE TWO DIRECTIONS AS ONE STATEMENT.  This is the ordinal half of
  -- the isomorphism reading `C.InjExt.iso` gives for membership
  -- (src/V/Collapse.lagda.md:299-301).
  pi-ord-iso : (y : S) → ⟨ y ∈ˢ M ⟩
             → (IsOrd y → IsOrd (C.π y)) × (IsOrd (C.π y) → IsOrd y)
  pi-ord-iso y y∈M = PiPreservesOrd y y∈M , PiReflectsOrd y y∈M

  -- ===================================================================
  -- THE PREDECESSOR'S OWN TYPE, INHABITED.  `Pred.HullStage` is
  -- [LJ-1.649]'s module at this telescope, so the three names below are
  -- ITS types and not a copy of them.  Agda checks the match.
  -- ===================================================================

  module P649 = Pred.HullStage lam ordλ succλ X X⊆L ∅∈λ

  fifth : P649.PiReflectsOrd
  fifth = PiReflectsOrd

  -- WHAT THE GO IS WORTH.  [LJ-1.649]'s `levelin-from-647`
  -- (Probe649.agda:227-230) took FOUR hypotheses.  With `fifth`
  -- discharged it takes THREE, and the remaining two objects are
  -- [LJ-1.462]'s step 2 (in [LJ-1.647]'s ordinal-conditioned form) and
  -- its step 4.  Nothing else is left of the fifth fact.
  levelin-discharged : P649.HullClosedLsetOrd → P649.PiCommuteLset
                     → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩
                     → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-discharged = P649.levelin-from-647 fifth

  -- The same, with [LJ-1.649]'s ordinal-conditioned step 4.  Kept
  -- because [LJ-1.477] closed NO-GO on the UNconditioned commute
  -- (agents/tasks/LJ-1-477/lj-1.477-report.md:273-275), so this is the
  -- variant a consumer is more likely to be able to supply.
  levelin-discharged-ord-commute
    : P649.HullClosedLsetOrd → P649.PiCommuteLsetOrd
    → (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
  levelin-discharged-ord-commute = P649.levelin-from-647-ord-commute fifth

-- =====================================================================
-- THE OBLIGATION AT THE TOP LEVEL, WHICH IS WHERE THE WITNESS METER
-- READS IT.  `witness = Target.<dotted-name>` (scripts/pod/witness.py:278)
-- resolves against the probe module and not into a nested one, so the
-- brief's declared name lives here.  Same shape as [LJ-1.649]'s
-- top-level `levelin-from-steps`.
-- =====================================================================

PiReflectsOrd : (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → (y : S) → ⟨ y ∈ˢ HullStage.M lam ordλ succλ X X⊆L ∅∈λ ⟩
  → IsOrd (Collapse.π (HullStage.M lam ordλ succλ X X⊆L ∅∈λ) y)
  → IsOrd y
PiReflectsOrd lam ordλ succλ X X⊆L ∅∈λ =
  HullStage.PiReflectsOrd lam ordλ succλ X X⊆L ∅∈λ
