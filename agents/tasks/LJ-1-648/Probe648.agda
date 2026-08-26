{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.648] PROBE.  Clause (iii)'s commute, measured against
-- [LJ-1.646]'s keystone TAKEN AS A HYPOTHESIS.  It runs in
-- agents/tasks/LJ-1-648/ and lands nothing in src/.
--
-- Nothing is postulated.  Nothing is holed.  The file carries --safe.
-- ONE Agda process per run, GHCRTS="-A64m -I0 -M2g", the wide caliber,
-- set on the pane by the program and untouched here.
--
-- THE FLOOR WAS PRICED BEFORE ANY PROOF (D-10, and the standing coder
-- clause).  runs/FLOOR.agda.txt states the obligation at a HOLE in this
-- file's frame: runs/floor-1.out, exit 42 at the one designed hole,
-- 4.64 s, peak 740,999,168 bytes against the 2,147,483,648-byte cap.
--
-- WHAT THE READER SHOULD READ FIRST: review-of-commute-from-keystone.md,
-- beside this file.  The obligation is NOT inhabited here and the reason
-- is measured, not argued.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-648.Probe648 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( ∈sucV-elim; ∈sucV-inl; self∈sucV )
open import L.Constructible {ℓ} using ( IsOrd; Lset; 𝒟ₒ; Lset-in; Lset-out )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.BoundedSubset {ℓ} lem using ( module HullStage )
open import LJ-1-641.Probe641 {ℓ} lem using ( module Frame )

open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Data.Sigma using ( _×_; Σ-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; module InfinitySet )
open InfinitySet using ( sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- =====================================================================
-- THE FRAME.  [LJ-1.641]'s `Frame` telescope (Probe641.agda:58-64)
-- verbatim, so every term that task delivered is reachable here by
-- instantiation and nothing is rebuilt (the brief's premise 3).  The
-- hull's `Code` and `val` are opened on top, because the keystone's type
-- names them and [LJ-1.641] never opened them.
-- =====================================================================

module Frame648 (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (X : S) (X⊆Lλ : (z : S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module F641 = Frame lam ordλ succλ X X⊆Lλ ∅∈λ

  open HS.H.T using ( Code; val )
  open F641 using ( Commute; IndexInHull; DefFwd; DefBwd
                  ; π-member'; π-into; commute-from-gaps )

  -- ===================================================================
  -- SECTION 1.  W3, THE WIDEST UNMEASURED TERM, ANSWERED FIRST.
  --
  --   The brief names W3: "Whether `DefFwd` and `DefBwd` need the
  --   keystone at `𝒟ₒ` as well as at `Lset`", at 80 to 170 lines.
  --
  --   THE ANSWER IS NO, AND IT COSTS ONE LINE.  `𝒟ₒ` AT A LEVEL IS
  --   `Lset` AT A SUCCESSOR: `Lset-suc` (src/L/Axioms/Basic.lagda.md:196)
  --   is `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` and it holds for EVERY `σ`, with
  --   no ordinality hypothesis at all.  That file says so in terms at
  --   :185-189: "It was stated with an ordinality hypothesis and the
  --   hypothesis turned out to be dead".  So a hypothesis about `Lset`
  --   already speaks about every `𝒟ₒ` this obligation names, and there
  --   is no second keystone left to want.
  --
  --   The estimate is refuted DOWNWARD, and the question W3 should have
  --   asked is section 4's.
  -- ===================================================================

  𝒟-at-level : (β : S) → 𝒟ₒ (Lset β) ≡ Lset (sucV β)
  𝒟-at-level β = sym (Lset-suc β)

  -- The three gaps of [LJ-1.641] with every `𝒟ₒ` removed.  Nothing is
  -- weakened: the conversions below are `subst` along `𝒟-at-level` and
  -- go both ways.
  IndexInHullSuc : Type (ℓ-suc ℓ)
  IndexInHullSuc =
    (δ : S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)
    → (β : S) → ⟨ β ∈ˢ δ ⟩
    → (y : S) → ⟨ y ∈ˢ HS.M ⟩ → ⟨ y ∈ˢ Lset (sucV β) ⟩
    → ∥ Σ[ β' ∈ S ]
         (⟨ β' ∈ˢ δ ⟩ × ⟨ β' ∈ˢ HS.M ⟩ × ⟨ y ∈ˢ Lset (sucV β') ⟩) ∥₁

  DefFwdSuc : Type (ℓ-suc ℓ)
  DefFwdSuc =
    (β y : S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ y ∈ˢ HS.M ⟩
    → ⟨ y ∈ˢ Lset (sucV β) ⟩
    → ⟨ HS.C.π y ∈ˢ Lset (sucV (HS.C.π β)) ⟩

  DefBwdSuc : Type (ℓ-suc ℓ)
  DefBwdSuc =
    (β z : S) → ⟨ β ∈ˢ HS.M ⟩
    → ⟨ z ∈ˢ Lset (sucV (HS.C.π β)) ⟩
    → ∥ Σ[ y ∈ S ]
         (⟨ y ∈ˢ Lset (sucV β) ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z)) ∥₁

  private
    at : (β : S) {y : S} → ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩ → ⟨ y ∈ˢ Lset (sucV β) ⟩
    at β {y} = subst (λ w → ⟨ y ∈ˢ w ⟩) (𝒟-at-level β)

    ta : (β : S) {y : S} → ⟨ y ∈ˢ Lset (sucV β) ⟩ → ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩
    ta β {y} = subst (λ w → ⟨ y ∈ˢ w ⟩) (sym (𝒟-at-level β))

  index-suc : IndexInHullSuc → IndexInHull
  index-suc ih δ δ∈M oπδ β β∈δ y y∈M y∈𝒟 =
    PT.map (λ { (β' , a , b , c) → β' , a , b , ta β' c })
           (ih δ δ∈M oπδ β β∈δ y y∈M (at β y∈𝒟))

  fwd-suc : DefFwdSuc → DefFwd
  fwd-suc df β y β∈M y∈M y∈𝒟 = ta (HS.C.π β) (df β y β∈M y∈M (at β y∈𝒟))

  bwd-suc : DefBwdSuc → DefBwd
  bwd-suc db β z β∈M z∈𝒟 =
    PT.map (λ { (y , a , b , c) → y , ta β a , b , c })
           (db β z β∈M (at (HS.C.π β) z∈𝒟))

  -- and the obligation follows from the three restated gaps, through
  -- [LJ-1.641]'s assembly and nothing new
  commute-from-suc-gaps
    : IndexInHullSuc → DefFwdSuc → DefBwdSuc → Commute
  commute-from-suc-gaps ih df db =
    commute-from-gaps (index-suc ih) (fwd-suc df) (bwd-suc db)

  -- ===================================================================
  -- SECTION 2.  THE KEYSTONE, AND EXACTLY HOW STRONG IT IS.
  --
  --   [LJ-1.646] is a SIBLING queued in the same block as this task, not
  --   a predecessor: `agents/tasks/LJ-1-646/` does not exist and the
  --   mathematician says so in terms, "Four consumers take the keystone
  --   as a hypothesis, so backlog item 27 does not bite: nothing reads a
  --   RUNNING sibling's output" (dev/pod/queue.toml:6216-6217).  So the
  --   type is taken from the tree, verbatim from [LJ-1.462]'s own D-10
  --   correction (agents/tasks/LJ-1-462/Probe462.agda:118-121), which is
  --   the source the same queue block cites (:6207).  [LJ-1.647] did the
  --   same for the same reason (its report, "THE PREDECESSOR QUESTION").
  --
  --   THEN THE STRENGTH IS MEASURED RATHER THAN ASSUMED.  The two terms
  --   at the foot of this section are a round trip: the keystone gives
  --   hull-closure under `Lset` at ordinals, AND hull-closure under
  --   `Lset` at ordinals gives the keystone back.  So, up to the
  --   truncation [LJ-1.647] measured to be free (its `hull-closed-lset∥`,
  --   Probe647.agda:171-173), THE KEYSTONE IS EXACTLY THAT CLOSURE AND
  --   IT IS NOTHING ELSE.  Section 4 spends this fact.
  -- ===================================================================

  LsetCodeOrd : Type (ℓ-suc ℓ)
  LsetCodeOrd =
    (c : Code) → IsOrd (fst (val c))
    → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

  LsetCodeOrd∥ : Type (ℓ-suc ℓ)
  LsetCodeOrd∥ =
    (c : Code) → IsOrd (fst (val c))
    → ∥ Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c))) ∥₁

  HullClosedLsetOrd : Type (ℓ-suc ℓ)
  HullClosedLsetOrd =
    (y : S) → ⟨ y ∈ˢ HS.M ⟩ → IsOrd y → ⟨ Lset y ∈ˢ HS.M ⟩

  -- W2 (DD4).  The mathematics ONCE, at a generic operation and a
  -- generic side condition, from the WEAKEST form of the hypothesis.
  -- This is [LJ-1.647]'s `hull-closed-op∥` (Probe647.agda:135-149),
  -- which that report asks this task to take rather than rebuild ("[LJ-1.648]
  -- and [LJ-1.650] should take `hull-closed-op∥` and supply their own
  -- `F`", lj-1.647-report.md).  It cannot be IMPORTED: that task's
  -- telescope drops `module C = Collapse M` (Probe647.agda:62-63) and
  -- this obligation's type is written with `HS.C.π` throughout, so the
  -- two `HullStage`s are different modules.  The proof is the same
  -- proof and the credit is [LJ-1.647]'s.
  hull-closed-op∥ : (F : S → S) (P : S → Type (ℓ-suc ℓ))
                  → ((c : Code) → P (fst (val c))
                     → ∥ Σ[ d ∈ Code ] (fst (val d) ≡ F (fst (val c))) ∥₁)
                  → (y : S) → ⟨ y ∈ˢ HS.M ⟩ → P y → ⟨ F y ∈ˢ HS.M ⟩
  hull-closed-op∥ F P code y y∈M py =
    PT.rec (snd (F y ∈ˢ HS.M)) go (HS.H.hull-member y y∈M)
    where
    go : Σ[ c ∈ Code ] (fst (val c) ≡ y) → ⟨ F y ∈ˢ HS.M ⟩
    go (c , q) =
      PT.rec (snd (F y ∈ˢ HS.M))
             (λ dq → subst (λ z → ⟨ z ∈ˢ HS.M ⟩)
                           (snd dq ∙ cong F q)
                           (HS.H.val-in-Hull (fst dq)))
             (code c (subst P (sym q) py))

  keystone∥ : LsetCodeOrd → LsetCodeOrd∥
  keystone∥ k c oc = ∣ k c oc ∣₁

  -- FORWARD.  The keystone closes the hull under `Lset` at ordinals.
  keystone-closure : LsetCodeOrd∥ → HullClosedLsetOrd
  keystone-closure k = hull-closed-op∥ Lset IsOrd k

  -- BACKWARD, AND THIS IS THE MEASUREMENT.  The closure gives the
  -- keystone back, because hull membership IS "is the value of a code"
  -- (src/L/Hull.lagda.md:337-339, where `hull-member`'s proof is its own
  -- argument).  No formula, no search, no new hypothesis.
  closure-keystone : HullClosedLsetOrd → LsetCodeOrd∥
  closure-keystone hc c oc =
    HS.H.hull-member (Lset (fst (val c)))
                     (hc (fst (val c)) (HS.H.val-in-Hull c) oc)

  -- ===================================================================
  -- SECTION 3.  THE COLLAPSE COMMUTES WITH THE SUCCESSOR.  A LEMMA THE
  -- TREE OWED, AND THE ONE THIS TASK ADDS TO THE STOCK.
  --
  --   `HS.C.π (sucV β) ≡ sucV (HS.C.π β)` at any hull member `β`.  It
  --   needs no keystone, no ordinality, no extensionality of the hull
  --   and no formula: the members of `sucV β` are the members of `β`
  --   together with `β` itself, the collapse sees exactly the ones that
  --   lie in the hull, and `β` is one of them by hypothesis.
  --
  --   IT IS THE HINGE OF SECTION 4.  Without it "the commute at
  --   `sucV β`" and "the commute with `𝒟ₒ` at `β`" are two statements;
  --   with it and with `𝒟-at-level` they are ONE.
  -- ===================================================================

  π-sucV : (β : S) → ⟨ β ∈ˢ HS.M ⟩ → HS.C.π (sucV β) ≡ sucV (HS.C.π β)
  π-sucV β β∈M = extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : S) → ⟨ z ∈ˢ HS.C.π (sucV β) ⟩
        → ⟨ z ∈ˢ sucV (HS.C.π β) ⟩
    fwd z z∈ =
      PT.rec (snd (z ∈ˢ sucV (HS.C.π β))) go (π-member' (sucV β) z z∈)
      where
      go : Σ[ u ∈ S ]
             (⟨ u ∈ˢ sucV β ⟩ × ⟨ u ∈ˢ HS.M ⟩ × (HS.C.π u ≡ z))
         → ⟨ z ∈ˢ sucV (HS.C.π β) ⟩
      go (u , u∈s , u∈M , πu≡z) =
        subst (λ w → ⟨ w ∈ˢ sucV (HS.C.π β) ⟩) πu≡z
          (∈sucV-elim {A = β} {x = u}
            (snd (HS.C.π u ∈ˢ sucV (HS.C.π β))) u∈s
            (λ u∈β → ∈sucV-inl (π-into β u u∈β u∈M))
            (λ u≡β → subst (λ w → ⟨ HS.C.π w ∈ˢ sucV (HS.C.π β) ⟩)
                           (sym u≡β) (self∈sucV (HS.C.π β))))
    bwd : (z : S) → ⟨ z ∈ˢ sucV (HS.C.π β) ⟩
        → ⟨ z ∈ˢ HS.C.π (sucV β) ⟩
    bwd z z∈ =
      ∈sucV-elim {A = HS.C.π β} {x = z}
        (snd (z ∈ˢ HS.C.π (sucV β))) z∈
        (λ z∈πβ → PT.rec (snd (z ∈ˢ HS.C.π (sucV β))) go
                         (π-member' β z z∈πβ))
        (λ z≡πβ → subst (λ w → ⟨ w ∈ˢ HS.C.π (sucV β) ⟩) (sym z≡πβ)
                    (π-into (sucV β) β (self∈sucV β) β∈M))
      where
      go : Σ[ u ∈ S ] (⟨ u ∈ˢ β ⟩ × ⟨ u ∈ˢ HS.M ⟩ × (HS.C.π u ≡ z))
         → ⟨ z ∈ˢ HS.C.π (sucV β) ⟩
      go (u , u∈β , u∈M , πu≡z) =
        subst (λ w → ⟨ w ∈ˢ HS.C.π (sucV β) ⟩) πu≡z
          (π-into (sucV β) u (∈sucV-inl u∈β) u∈M)

  -- ===================================================================
  -- SECTION 4.  THE MEASUREMENT THIS TASK EXISTS TO MAKE.
  --
  --   `DefFwd` AND `DefBwd` TOGETHER ARE NOT A REDUCTION OF THE
  --   OBLIGATION.  THEY ARE THE OBLIGATION, AT A SUCCESSOR.
  --
  --   `CommuteAtSuc` below is `Commute`'s own conclusion instantiated at
  --   `δ := sucV β`, rewritten by `π-sucV` (section 3) so that no `π`
  --   stands inside an `Lset`.  Then the two implications
  --   `def-gaps-from-commute-suc` and `commute-suc-from-def-gaps` are an
  --   EQUIVALENCE: the pair `DefFwdSuc × DefBwdSuc` and `CommuteAtSuc`
  --   give each other, with `π-member'` and `π∈-fwd` and nothing else.
  --
  --   AND `commute-at-suc-is-an-instance` shows `CommuteAtSuc` really is
  --   an instance of the obligation and not a stronger statement: from
  --   `Commute` and the three side conditions `Commute` itself demands,
  --   it follows.
  --
  --   SO THE TWO DEFINABILITY GAPS SIT AT THE SAME HEIGHT AS THE
  --   OBLIGATION, NOT BELOW IT.  Anything that produces them produces
  --   the obligation at every successor of a hull member.  Section 5
  --   spends this against the keystone.
  -- ===================================================================

  CommuteAtSuc : Type (ℓ-suc ℓ)
  CommuteAtSuc =
    (β : S) → ⟨ β ∈ˢ HS.M ⟩
    → HS.C.π (Lset (sucV β)) ≡ Lset (sucV (HS.C.π β))

  fwd-from-commute-suc : CommuteAtSuc → DefFwdSuc
  fwd-from-commute-suc c β y β∈M y∈M y∈L =
    subst (λ w → ⟨ HS.C.π y ∈ˢ w ⟩) (c β β∈M)
          (π-into (Lset (sucV β)) y y∈L y∈M)

  bwd-from-commute-suc : CommuteAtSuc → DefBwdSuc
  bwd-from-commute-suc c β z β∈M z∈ =
    π-member' (Lset (sucV β)) z
      (subst (λ w → ⟨ z ∈ˢ w ⟩) (sym (c β β∈M)) z∈)

  commute-suc-from-def-gaps : DefFwdSuc → DefBwdSuc → CommuteAtSuc
  commute-suc-from-def-gaps df db β β∈M =
    extensionalV (λ z → ⇔toPath (fwd z) (bwd z))
    where
    fwd : (z : S) → ⟨ z ∈ˢ HS.C.π (Lset (sucV β)) ⟩
        → ⟨ z ∈ˢ Lset (sucV (HS.C.π β)) ⟩
    fwd z z∈ =
      PT.rec (snd (z ∈ˢ Lset (sucV (HS.C.π β)))) go
             (π-member' (Lset (sucV β)) z z∈)
      where
      go : Σ[ y ∈ S ]
             (⟨ y ∈ˢ Lset (sucV β) ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z))
         → ⟨ z ∈ˢ Lset (sucV (HS.C.π β)) ⟩
      go (y , y∈L , y∈M , πy≡z) =
        subst (λ w → ⟨ w ∈ˢ Lset (sucV (HS.C.π β)) ⟩) πy≡z
              (df β y β∈M y∈M y∈L)
    bwd : (z : S) → ⟨ z ∈ˢ Lset (sucV (HS.C.π β)) ⟩
        → ⟨ z ∈ˢ HS.C.π (Lset (sucV β)) ⟩
    bwd z z∈ =
      PT.rec (snd (z ∈ˢ HS.C.π (Lset (sucV β)))) go (db β z β∈M z∈)
      where
      go : Σ[ y ∈ S ]
             (⟨ y ∈ˢ Lset (sucV β) ⟩ × ⟨ y ∈ˢ HS.M ⟩ × (HS.C.π y ≡ z))
         → ⟨ z ∈ˢ HS.C.π (Lset (sucV β)) ⟩
      go (y , y∈L , y∈M , πy≡z) =
        subst (λ w → ⟨ w ∈ˢ HS.C.π (Lset (sucV β)) ⟩) πy≡z
              (π-into (Lset (sucV β)) y y∈L y∈M)

  -- `CommuteAtSuc` is an INSTANCE of the obligation.  The three
  -- hypotheses are the three the obligation itself carries, read at
  -- `sucV β`; the keystone supplies the third from the first, which is
  -- the one place in this file where it does real work
  -- (`keystone-closure`, section 2).
  commute-at-suc-is-an-instance
    : Commute
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ sucV β ∈ˢ HS.M ⟩)
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → IsOrd (HS.C.π (sucV β)))
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ Lset (sucV β) ∈ˢ HS.M ⟩)
    → CommuteAtSuc
  commute-at-suc-is-an-instance c s∈M oπs L∈M β β∈M =
    c (sucV β) (s∈M β β∈M) (oπs β β∈M) (L∈M β β∈M)
    ∙ cong Lset (π-sucV β β∈M)

  -- ===================================================================
  -- SECTION 5.  THE INDEX GAP, WITH `𝒟ₒ` AND THE STRAY `β` BOTH GONE.
  --
  --   `IndexInHull` reads as a statement about a member `β` of `δ` and a
  --   definable subset over it.  It is not.  Once `𝒟ₒ` is `Lset` at a
  --   successor (section 1), the `β` the statement is handed can be
  --   dropped and recovered by `Lset-out`, and what is left is one
  --   sentence about the hull alone:
  --
  --     A HULL MEMBER OF `Lset δ` HAS A LEVEL INDEX INSIDE THE HULL.
  --
  --   `RankInHull` is that sentence and the two implications below are
  --   an equivalence with `IndexInHullSuc`.  This is where [LJ-1.641]'s
  --   reading survives review: this gap IS a hull-member search, its
  --   condition names `Lset`, and `hull-closed` (src/L/Hull.lagda.md:415)
  --   is the only rule that answers a search.  It wants the FORMULA, not
  --   the code map (review-of-commute-from-keystone.md, part 3).
  -- ===================================================================

  RankInHull : Type (ℓ-suc ℓ)
  RankInHull =
    (δ : S) → ⟨ δ ∈ˢ HS.M ⟩ → IsOrd (HS.C.π δ)
    → (y : S) → ⟨ y ∈ˢ HS.M ⟩ → ⟨ y ∈ˢ Lset δ ⟩
    → ∥ Σ[ β' ∈ S ]
         (⟨ β' ∈ˢ δ ⟩ × ⟨ β' ∈ˢ HS.M ⟩ × ⟨ y ∈ˢ Lset (sucV β') ⟩) ∥₁

  index-from-rank : RankInHull → IndexInHullSuc
  index-from-rank rk δ δ∈M oπδ β β∈δ y y∈M y∈L =
    rk δ δ∈M oπδ y y∈M (Lset-in δ β y β∈δ (ta β y∈L))

  rank-from-index : IndexInHullSuc → RankInHull
  rank-from-index ih δ δ∈M oπδ y y∈M y∈Lδ =
    PT.rec PT.squash₁ go (Lset-out δ y y∈Lδ)
    where
    go : Σ[ β ∈ S ] (⟨ β ∈ˢ δ ⟩ × ⟨ y ∈ˢ 𝒟ₒ (Lset β) ⟩)
       → ∥ Σ[ β' ∈ S ]
            (⟨ β' ∈ˢ δ ⟩ × ⟨ β' ∈ˢ HS.M ⟩ × ⟨ y ∈ˢ Lset (sucV β') ⟩) ∥₁
    go (β , β∈δ , y∈𝒟) = ih δ δ∈M oπδ β β∈δ y y∈M (at β y∈𝒟)

  -- ===================================================================
  -- SECTION 6.  THE RESIDUE, AND THE KEYSTONE PRESENT AND UNUSED.
  --
  --   `Residue` is [LJ-1.641]'s three gaps after sections 1, 4 and 5:
  --   the index gap with `𝒟ₒ` gone, and the two definability gaps folded
  --   into the ONE statement they are, the obligation at a successor.
  --
  --   `commute-from-keystone-and-residue` IS THE MEASUREMENT, AND ITS
  --   FIRST ARGUMENT IS AN UNDERSCORE.  The keystone is taken and never
  --   eliminated: no row of the assembly reads it.  That is not a
  --   stylistic choice, it is the finding, and Agda checks it.
  --
  --   THE OBLIGATION `commute-from-keystone` IS NOT DECLARED IN THIS
  --   FILE.  review-of-commute-from-keystone.md states the NO-GO and
  --   gives the evidence.
  -- ===================================================================

  Residue : Type (ℓ-suc ℓ)
  Residue = RankInHull × CommuteAtSuc

  commute-from-residue : Residue → Commute
  commute-from-residue (rk , cs) =
    commute-from-suc-gaps (index-from-rank rk)
                          (fwd-from-commute-suc cs)
                          (bwd-from-commute-suc cs)

  commute-from-keystone-and-residue : LsetCodeOrd → Residue → Commute
  commute-from-keystone-and-residue _ = commute-from-residue

  -- And the residue is not weaker than the obligation plus the index
  -- gap: the obligation gives `CommuteAtSuc` back, through section 4.
  residue-from-commute
    : Commute
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ sucV β ∈ˢ HS.M ⟩)
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → IsOrd (HS.C.π (sucV β)))
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ Lset (sucV β) ∈ˢ HS.M ⟩)
    → CommuteAtSuc
  residue-from-commute = commute-at-suc-is-an-instance

  -- THE ONE PLACE THE KEYSTONE PAYS.  It supplies the third side
  -- condition of that instance, from the first.  It touches no gap.
  keystone-supplies-side
    : LsetCodeOrd∥
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ sucV β ∈ˢ HS.M ⟩)
    → ((β : S) → ⟨ β ∈ˢ HS.M ⟩ → IsOrd (sucV β))
    → (β : S) → ⟨ β ∈ˢ HS.M ⟩ → ⟨ Lset (sucV β) ∈ˢ HS.M ⟩
  keystone-supplies-side k s∈M os β β∈M =
    keystone-closure k (sucV β) (s∈M β β∈M) (os β β∈M)
