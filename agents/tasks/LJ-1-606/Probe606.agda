{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.606]  THE CROSSING FROM AN INNER WORLD TO THE AMBIENT TOWER:
-- the set-level commute clause (iii) needs, REDUCED to its named faces.
--
-- W3 IS runs/W3.agda, written FIRST and typechecked ALONE: exit 0 at
-- 2.41 s, peak 600,702,976 bytes (runs/w3-2.out), under the brief's
-- two-minute cap.  The type is the commute of [LJ-1.602] section 3
-- (Probe602.agda:178-181), which that task measured EQUIVALENT to
-- clause (iii) at the clause's own hypotheses (Probe602.agda:189-219).
--
-- THE FLOOR WAS MEASURED BEFORE ANY PROOF (D-10 and the owner's ruling
-- of 2026-08-23): runs/FLOOR.agda is this file's frame with the
-- obligation at a bare meta; runs/floor-2.out is exit 42 at the one
-- designed hole, 3.56 s, peak 656,900,096 bytes.  runs/floor-1.out is
-- a SYNTAX failure and not a measurement: the import list carried
-- `_⇒_` for `_⇒̇_` and the Absoluteness import pattern was wrong;
-- both are recorded and neither is priced.
--
-- WHAT THIS PROBE LANDS.  ONE term, `inner-to-ambient`: the commute,
-- INHABITED FROM THREE NAMED FACES.  The brief's obligation sentence
-- allows exactly this shape ("the term naming precisely what it
-- lacks").  The outright commute is NOT inhabited here and the stop is
-- stated at agents/tasks/LJ-1-606/review-of-inner-to-ambient.md.
--
-- THE FINDING IS THE SHAPE OF THE REMAINDER.  The commute is ONE
-- transfer of the level-graph statement: it needs NO induction on the
-- tower, NO Fact A below delta, and NO def-hood lifting.  Reading the
-- graph statement at the hull's level pair, one chain moves it
-- stage -> hull -> collapse image -> ambient, and the four legs are:
--   FACE G+ (GraphStage)  the stage carries the graph at the tower's
--                         own values: UNBUILT, the witness-in-carrier
--                         half of Devlin 5.2's (b), the Adeq shape of
--                         [LJ-1.570] (Probe570.agda:319-322);
--   FACE E  (ElemDownAt)  elementarity down at the hull, the reading
--                         move stage -> hull: UNBUILT at this six-slot
--                         frame, DELIVERED at [LJ-1.570]'s seventeen
--                         slots (Probe578.agda, elem-down-taken);
--   the collapse iso hull -> image: DELIVERED (src/L/BoundedSubset
--                         .lagda.md:195 and :250, instantiated at
--                         :321 by CollapseIso);
--   FACE G- (GraphAmbient) the ambient graph statement at an ORDINAL
--                         index pins the tower's level: UNBUILT, the
--                         (a) half of Devlin 5.2, [LJ-1.160]'s
--                         crossOut face made concrete
--                         (ProbeLJ1160A.agda:71-72);
--   the Sigma-1 lift image -> ambient: DELIVERED
--                         (src/FOL/Absoluteness.lagda.md, sigma-one-up,
--                         which [LJ-1.160] measured opens at piX in one
--                         line, ProbeLJ1160A.agda:49-53).
-- The commute's own `IsOrd (pi delta)` is spent at FACE G- alone, and
-- FACE G+ alone carries the all-index reading: see the report.
--
-- Nothing is postulated.  Nothing lands in src/.  No hole in the
-- delivered file.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M2g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-606.Probe606 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
        ; ∀̇∈; ∃̇∈; ∃̇_ )
open import FOL.LevyHierarchy
  using ( Δ₀; δ-∈; δ-≐; δ-∧; δ-∨; δ-⇒; δ-¬; δ-⊤; δ-⊥; δ-∀∈; δ-∃∈
        ; Σ₁; σ-Δ₀; σ-∃ )
open import FOL.Manipulation.Relabelling using ( mapFo )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import L.Constructible {ℓ} using ( IsOrd; Lset )
open import L.Ordinal {ℓ} using ( ∅-ord )
open import V.Model {ℓ} using ( self∈sucV )
open import L.BoundedSubset {ℓ} lem
  using ( module HullStage; module HullExt; module CollapseIso
        ; module DownReflect )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet; ∅; ∅-empty )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ )
open InfinitySet {ℓ} using ( sucV )
open import Cubical.Data.Vec using ( map; _∷_; [] )
open import Cubical.Data.Unit using ( tt* )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
module SV = hPropStructure 𝒮ᵥ
open SV using ( _∈ˢ_ )

-- =====================================================================
-- THE FRAME.  One hull stage at a limit index, its extensionality, its
-- collapse iso, its down-reflection module, and the absoluteness
-- machine at the transitive collapse image.  Nothing from any probe
-- enters this file: the frame is [LJ-1.602]'s, with the two modules
-- the crossing additionally spends.
-- =====================================================================

module Frame (lam : SV.S) (ordλ : IsOrd lam)
             (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
             (X : SV.S)
             (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
             (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  module HS = HullStage lam ordλ succλ X X⊆Lλ ∅∈λ
  module HE = HullExt lam ordλ X X⊆Lλ ∅∈λ
  module CI = CollapseIso HS.M HE.hullExt
  module DR = DownReflect lam ordλ X X⊆Lλ ∅∈λ
  module AbsπX = FOL.Absoluteness.Single 𝒮ᵥ
                 (λ x → x ∈ˢ HS.C.πX) HS.C.πX-trans

  -- ===================================================================
  -- SECTION 1.  W3.  THE COMMUTE, RESTATED ALONE.
  --
  --   [LJ-1.602]'s section 3 commute, letter for letter
  --   (Probe602.agda:178-181): the collapse of the hull's level at
  --   delta IS the tower's level at the collapsed index.  At the
  --   clause's own four hypotheses; equivalent to clause (iii) exactly
  --   (Probe602.agda:189-219, both directions as terms there).
  -- ===================================================================

  Commute : Type (ℓ-suc ℓ)
  Commute =
    (δ : SV.S) (δ∈M : ⟨ δ ∈ˢ HS.M ⟩) → IsOrd (HS.C.π δ)
    → (Lδ∈M : ⟨ Lset δ ∈ˢ HS.M ⟩)
    → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)

  -- ===================================================================
  -- SECTION 2.  THE FACES.  What the commute lacks, each ONE type,
  -- each named.  The term of section 4 consumes exactly these and
  -- nothing else, so the type of `inner-to-ambient` IS the statement
  -- of what the crossing lacks.
  -- ===================================================================

  -- FACE E.  Elementarity down at the hull: the stage's inner reading
  -- of a mapped formula implies the hull's own reading.  This is
  -- `DownReflect.ElemDown` at this frame
  -- (src/L/BoundedSubset.lagda.md:410), delivered by [LJ-1.570]'s canonical-code
  -- machinery at the SEVENTEEN-slot frame
  -- (agents/tasks/LJ-1-578/Probe578.agda, elem-down-taken) and unbuilt
  -- at these six slots, where the code count needs the square law.
  ElemDownAt : Type (ℓ-suc ℓ)
  ElemDownAt = DR.ElemDown

  -- FACE G+.  The stage CARRIES the level graph at the tower's own
  -- values: at a hull pair whose value IS the tower's level at the
  -- index, the stage's inner world satisfies the Sigma-one closure of
  -- the graph matrix.  This is the witness-in-carrier half of Devlin
  -- 5.2's (b) (dev/literature/devlin-II5.md, section 2.3, item 2), the
  -- Adeq shape of [LJ-1.570] (Probe570.agda:319-322).  UNBUILT.
  GraphStage : Formula CI.I.SM 3 → Type (ℓ-suc ℓ)
  GraphStage ψ =
    (q γ : CI.I.SM) → fst q ≡ Lset (fst γ)
    → ⟨ map DR.inL (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ mapFo DR.inL (∃̇ ψ) ⟩

  -- FACE G-.  The AMBIENT graph statement at an ORDINAL index pins the
  -- tower's level: any ambient witness of the carried matrix at (v,
  -- gamma), with gamma ordinal, forces v to be the tower's level
  -- there.  This is Devlin 5.2's (a) read at the collapsed constants,
  -- [LJ-1.160]'s crossOut face made concrete (ProbeLJ1160A.agda:71-72).
  -- UNBUILT.  The commute's own `IsOrd (HS.C.π δ)` is spent HERE and
  -- nowhere else.
  GraphAmbient : Formula CI.I.SM 3 → Type (ℓ-suc ℓ)
  GraphAmbient ψ =
    (x v γ : SV.S) → IsOrd γ
    → ⟨ (x ∷ v ∷ γ ∷ []) AbsπX.⊨ᵛ mapFo CI.I.g ψ ⟩
    → v ≡ Lset γ

  -- THE CROSSING KIT.  One Delta-zero graph matrix over the hull's own
  -- constants, with both adequacy faces.  No degenerate matrix passes:
  -- a true matrix fails G-, a false one fails G+, so the kit is
  -- exactly the level-graph adequacy at this site.
  Crossing : Type (ℓ-suc ℓ)
  Crossing =
    Σ[ ψ ∈ Formula CI.I.SM 3 ] ( Δ₀ ψ × GraphStage ψ × GraphAmbient ψ )

  -- ===================================================================
  -- SECTION 3.  THE FRAME'S SYNTAX LEGS.  The Delta-zero witness and
  -- the Sigma-one closure survive relabelling: pure syntax, no set
  -- theory, priced by the floor run above.
  -- ===================================================================

  mapFo-Δ₀ : {K K' : Type (ℓ-suc ℓ)} {n : ℕ} (f : K → K')
           → (ψ : Formula K n) → Δ₀ ψ → Δ₀ (mapFo f ψ)
  mapFo-Δ₀ f (t ∈̇ u) d = δ-∈
  mapFo-Δ₀ f (t ≐ u) d = δ-≐
  mapFo-Δ₀ f (ψ ∧̇ χ) (δ-∧ d e) = δ-∧ (mapFo-Δ₀ f ψ d) (mapFo-Δ₀ f χ e)
  mapFo-Δ₀ f (ψ ∨̇ χ) (δ-∨ d e) = δ-∨ (mapFo-Δ₀ f ψ d) (mapFo-Δ₀ f χ e)
  mapFo-Δ₀ f (ψ ⇒̇ χ) (δ-⇒ d e) = δ-⇒ (mapFo-Δ₀ f ψ d) (mapFo-Δ₀ f χ e)
  mapFo-Δ₀ f (¬̇ ψ) (δ-¬ d) = δ-¬ (mapFo-Δ₀ f ψ d)
  mapFo-Δ₀ f ⊤̇ d = δ-⊤
  mapFo-Δ₀ f ⊥̇ d = δ-⊥
  mapFo-Δ₀ f (∀̇∈ t ψ) (δ-∀∈ d) = δ-∀∈ (mapFo-Δ₀ f ψ d)
  mapFo-Δ₀ f (∃̇∈ t ψ) (δ-∃∈ d) = δ-∃∈ (mapFo-Δ₀ f ψ d)

  Σ₁-carried : {K K' : Type (ℓ-suc ℓ)} (f : K → K') {n : ℕ}
             → (ψ : Formula K (suc n)) → Δ₀ ψ
             → Σ₁ (mapFo f (∃̇ ψ))
  Σ₁-carried f ψ d = σ-∃ (σ-Δ₀ (mapFo-Δ₀ f ψ d))

  -- ===================================================================
  -- SECTION 4.  THE OBLIGATION.  The commute from the faces, in one
  -- chain: G+ puts the graph statement in the stage's inner world at
  -- the hull's own level pair; E reads it into the hull; the delivered
  -- collapse iso carries it to the image; the delivered Sigma-one lift
  -- reads it out to the ambient at the collapsed constants; G- decodes
  -- it there, at the ordinal index, as the tower's level.  NO
  -- induction, NO Fact A, NO def-hood lifting: the whole commute is
  -- one transfer of one statement.
  -- ===================================================================

  inner-to-ambient : ElemDownAt → Crossing → Commute
  inner-to-ambient ed (ψ , dψ , gst , gamb) δ δ∈M oπδ Lδ∈M =
    PT.rec (SV.isSetS _ _) body (σ₁-amb)
    where
    q : CI.I.SM
    q = Lset δ , Lδ∈M
    γ : CI.I.SM
    γ = δ , δ∈M
    -- leg 1, FACE G+: the stage's inner world at the hull's level pair
    stage : ⟨ map DR.inL (q ∷ γ ∷ []) DR.ASt.AbsL.⊨ᵐ mapFo DR.inL (∃̇ ψ) ⟩
    stage = gst q γ refl
    -- leg 2, FACE E: the hull's own reading
    hull : ⟨ (q ∷ γ ∷ []) CI.I.⊨ᵐ (∃̇ ψ) ⟩
    hull = ed 2 (∃̇ ψ) (q ∷ γ ∷ []) stage
    -- leg 3, DELIVERED: the collapse iso to the image
    image : ⟨ map CI.I.g (q ∷ γ ∷ []) CI.I.⊨ᵖᵐ mapFo CI.I.g (∃̇ ψ) ⟩
    image = CI.I.iso-inv 2 (∃̇ ψ) (q ∷ γ ∷ []) hull
    -- leg 4, DELIVERED: the Sigma-one lift to the ambient, at the
    -- collapsed constants, where `fst (g m)` is `HS.C.π (fst m)`
    σ₁-amb : ⟨ map fst (map CI.I.g (q ∷ γ ∷ []))
                AbsπX.⊨ᵛ mapFo CI.I.g (∃̇ ψ) ⟩
    σ₁-amb = AbsπX.σ₁-up (Σ₁-carried CI.I.g ψ dψ)
               (map CI.I.g (q ∷ γ ∷ [])) image
    -- leg 5, FACE G-: the ambient witness decodes as the tower's level
    -- at the ordinal collapsed index
    body : Σ[ x ∈ SV.S ]
             ⟨ (x ∷ fst (CI.I.g q) ∷ fst (CI.I.g γ) ∷ [])
                 AbsπX.⊨ᵛ mapFo CI.I.g ψ ⟩
         → HS.C.π (Lset δ) ≡ Lset (HS.C.π δ)
    body (x , hmat) = gamb x (HS.C.π (Lset δ)) (HS.C.π δ) oπδ hmat

  -- ===================================================================
  -- SECTION 5.  THE KIT CARRIES NO DEGENERATE MATRIX, BOTH WAYS, AS
  -- TERMS.  A TRUE matrix fails FACE G- outright: at the ordinal
  -- index ∅ it would force EVERY set to be the tower's value there, so
  -- ∅ ≡ sucV ∅, and the empty set would be a member of itself.  A
  -- FALSE matrix fails FACE G+ at any genuine level-pair: the stage's
  -- reading of its existential closure detonates on the witness the
  -- reading itself supplies.  So neither half of the kit can be
  -- filled with junk: the crossing kit is exactly the level-graph
  -- adequacy.
  -- ===================================================================

  module NoDegenerate where

    ⊤-fails-G- : GraphAmbient ⊤̇ → Empty.⊥
    ⊤-fails-G- gamb =
      ∅-empty ∅ (∈∈ₛ {a = ∅} {b = ∅} .fst ∅∈∅)
      where
      e₁ : ∅ ≡ Lset ∅
      e₁ = gamb ∅ ∅ ∅ ∅-ord tt*
      e₂ : sucV ∅ ≡ Lset ∅
      e₂ = gamb ∅ (sucV ∅) ∅ ∅-ord tt*
      ∅≡sucV : ∅ ≡ sucV ∅
      ∅≡sucV = e₁ ∙ sym e₂
      ∅∈∅ : ⟨ ∅ ∈ˢ ∅ ⟩
      ∅∈∅ = subst (λ w → ⟨ ∅ ∈ˢ w ⟩) (sym ∅≡sucV) (self∈sucV ∅)

    ⊥-fails-G+ : (q : CI.I.SM) → fst q ≡ Lset (fst q)
               → GraphStage ⊥̇ → Empty.⊥
    ⊥-fails-G+ q fix gst = go (gst q q fix)
      where
      go : ⟨ map DR.inL (q ∷ q ∷ []) DR.ASt.AbsL.⊨ᵐ
             mapFo DR.inL (∃̇ ⊥̇) ⟩
         → Empty.⊥
      go h = PT.rec (Empty.isProp⊥) (λ { (x , hx) → Empty.rec* hx }) h

  -- ===================================================================
  -- SECTION 6.  WHAT THE FACES ARE, AS STATUS.  The residue of row 3
  -- in this probe's own currency: two of the four legs are delivered
  -- in src/, one is delivered at a wider frame, and the other two are
  -- the two halves of the level-graph adequacy, which is clause (i)'s
  -- own residue ([LJ-1.598]).  The stop is stated at
  -- agents/tasks/LJ-1-606/review-of-inner-to-ambient.md.
  -- ===================================================================

-- =====================================================================
-- THE OBLIGATION, HOISTED.  The six slots and the two faces in ONE
-- telescope, so the name `inner-to-ambient` sits at the probe's top
-- level and the witness meter's term-reference form reaches it
-- (scripts/pod/witness.py, the dotted-name rule: the brief declares
-- `Probe606.agda::inner-to-ambient` with no `Frame` segment).  A
-- parameterised submodule's contents apply to their parameters;
-- nothing is copied and nothing is restated.
-- =====================================================================

inner-to-ambient
  : (lam : SV.S) (ordλ : IsOrd lam)
    (succλ : (d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
    (X : SV.S)
    (X⊆Lλ : (z : SV.S) → ⟨ z ∈ˢ X ⟩ → ⟨ z ∈ˢ Lset lam ⟩)
    (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩)
  → Frame.ElemDownAt lam ordλ succλ X X⊆Lλ ∅∈λ
  → Frame.Crossing lam ordλ succλ X X⊆Lλ ∅∈λ
  → Frame.Commute lam ordλ succλ X X⊆Lλ ∅∈λ
inner-to-ambient lam ordλ succλ X X⊆Lλ ∅∈λ =
  Frame.inner-to-ambient lam ordλ succλ X X⊆Lλ ∅∈λ
