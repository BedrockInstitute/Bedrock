{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track A, file 3 of 3: the infinitary lemmas Bell's proofs actually spend.
--
-- What this module is for. Bell's proofs of 1.15 to 1.18 repeatedly take a
-- supremum over a class and then meet it with a fixed value, which in his
-- setting is licensed by the infinite distributive law of a complete Boolean
-- algebra. K4 may NOT use that law. Measured, re-run for this file:
--
--   grep -c "dist" CodedCompletion.agda   = 0
--
-- and the only infinite distributive law in the tree, Algebra.agda:339 ⋁-dist,
-- lives inside module CompleteTheory (bl : BooleanLaws) (ch : CompleteHost)
-- (Algebra.agda:335), whose CompleteHost field (Algebra.agda:116-119) asserts
-- that the algebra's own ⋁ is the supremum of EVERY host family. The coded
-- algebra is not such an algebra: CodedCompletion.agda:899-913 takes a
-- supremum only of a family that is realized as a ground set.
--
-- The replacement is sup-residual below, and its proof is three lines of
-- residuation: curry the pointwise bound into an implication, take the least
-- upper bound against that implication, uncurry. No distributive law is
-- named, and the empty family is covered without a side condition.
--
-- The rest of the file is the monotonicity, congruence and empty-family
-- calculus for supᴮ and infᴮ. sup-cong is what lets a value set be replaced by
-- any set with the same members, which is the only form in which the compiler
-- of K4.5 can ever compare two constructions; sup-empty is the general lemma
-- behind the empty-value case, and it is NOT redundant with NameWeight.agda's
-- weightᴮ-zero (:333-337), which is the weight-specific instance of it.
--
-- A MEASURED NEGATIVE ON THE ARCHITECTURE IS RECORDED BELOW, at inf-residual.
-- The statement the architecture prints for inf-residual is false, and the
-- counterexample is the empty family. Read the note there before using it.
--
-- Hypotheses. The structure, Extensionality, the path realization, B, a
-- Lattice, a Complement and a CodedComplete. Extensionality and the path
-- realization are consumed only through ≤ᴮ-antisym of K4/Implication.agda; the
-- Complement is consumed only through the implication and its adjunction.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication
import Cubical.Data.Empty as Empty

module K4.Infinitary
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (B : ZFStructure.S 𝒮)
  (L : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- See the scope contract at the head of K4/Implication.agda. K4.Algebra is
-- opened here without `public` for the same reason, so that a consumer can
-- open K4.Algebra and this module together.

open K4.Algebra 𝒮
  using ( Pt; isSetPt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

open K4.Implication 𝒮 ext paths B L Cm public
open CodedComplete Kc public

--------------------------------------------------------------------------------
-- Monotonicity and congruence
--------------------------------------------------------------------------------

-- A larger value set has a larger supremum. Note the shape of the hypothesis:
-- ⟨ X ⊆ˢ Y ⟩ unfolds to a function taking a CODE and a membership proof, so
-- the point u is taken apart at the call and only its first projection is
-- passed on. This is the same discipline that makes ⊆ˢ-trans a statement about
-- codes rather than about points.

sup-mono : (X Y : S) (hX : ⟨ X ⊆ˢ B ⟩) (hY : ⟨ Y ⊆ˢ B ⟩)
         → ⟨ X ⊆ˢ Y ⟩ → ⟨ supᴮ X hX ≤ᴮ supᴮ Y hY ⟩
sup-mono X Y hX hY sub =
  sup-lub X hX (supᴮ Y hY) (λ u hu → sup-ub Y hY u (sub (fst u) hu))

-- The infimum reverses it: a larger value set has a smaller infimum.

inf-mono : (X Y : S) (hX : ⟨ X ⊆ˢ B ⟩) (hY : ⟨ Y ⊆ˢ B ⟩)
         → ⟨ X ⊆ˢ Y ⟩ → ⟨ infᴮ Y hY ≤ᴮ infᴮ X hX ⟩
inf-mono X Y hX hY sub =
  inf-glb X hX (infᴮ Y hY) (λ u hu → inf-lb Y hY u (sub (fst u) hu))

-- Two sets with the same members have the same supremum, whatever proofs of
-- subsethood they carry. This is the ONLY way K4 ever identifies two values
-- built by different constructions: the two attainment laws are compared as
-- membership statements, never the two constructions as terms. It is also why
-- no K4 signature has to name the proof h of X ⊆ˢ B.

sup-cong : (X Y : S) (hX : ⟨ X ⊆ˢ B ⟩) (hY : ⟨ Y ⊆ˢ B ⟩)
         → ((b : S) → (b ∈ˢ X) ≡ (b ∈ˢ Y)) → supᴮ X hX ≡ supᴮ Y hY
sup-cong X Y hX hY e =
  ≤ᴮ-antisym (sup-mono X Y hX hY (λ x h → subst ⟨_⟩ (e x) h))
             (sup-mono Y X hY hX (λ x h → subst ⟨_⟩ (sym (e x)) h))

inf-cong : (X Y : S) (hX : ⟨ X ⊆ˢ B ⟩) (hY : ⟨ Y ⊆ˢ B ⟩)
         → ((b : S) → (b ∈ˢ X) ≡ (b ∈ˢ Y)) → infᴮ X hX ≡ infᴮ Y hY
inf-cong X Y hX hY e =
  ≤ᴮ-antisym (inf-mono Y X hY hX (λ x h → subst ⟨_⟩ (sym (e x)) h))
             (inf-mono X Y hX hY (λ x h → subst ⟨_⟩ (e x) h))

-- Independence of the subsethood proof is the degenerate case of congruence,
-- and it is worth a name because a value set is usually produced together with
-- one such proof and consumed with another.

sup-irr : (X : S) (h h' : ⟨ X ⊆ˢ B ⟩) → supᴮ X h ≡ supᴮ X h'
sup-irr X h h' = sup-cong X X h h' (λ b → refl)

inf-irr : (X : S) (h h' : ⟨ X ⊆ˢ B ⟩) → infᴮ X h ≡ infᴮ X h'
inf-irr X h h' = inf-cong X X h h' (λ b → refl)

--------------------------------------------------------------------------------
-- The empty family
--------------------------------------------------------------------------------

-- The supremum of a family with no members is bottom and the infimum is top.
-- The hypothesis is stated as a refutation of membership, ⟨ b ∈ˢ X ⟩ → ⟨ ⊥ ⟩,
-- with the ALGEBRA'S bottom on the right and never the host empty type, which
-- is K2's notation rule (Certificate.agda:40-43) and K4 keeps it.
--
-- These are the general lemmas. NameWeight.agda:333-337 already proves the
-- weight-specific instance weightᴮ-zero from weightᴮ-lub and ⊥ᴮ-empty; that
-- one is not K4's to rebuild, and this one is not derivable from it.

sup-empty : (X : S) (hX : ⟨ X ⊆ˢ B ⟩)
          → ((b : S) → ⟨ b ∈ˢ X ⟩ → ⟨ ⊥ ⟩) → supᴮ X hX ≡ ⊥ᴮ
sup-empty X hX e =
  ≤ᴮ-antisym (sup-lub X hX ⊥ᴮ (λ u hu → Empty.rec* (e (fst u) hu)))
             (⊥-least (supᴮ X hX))

inf-empty : (X : S) (hX : ⟨ X ⊆ˢ B ⟩)
          → ((b : S) → ⟨ b ∈ˢ X ⟩ → ⟨ ⊥ ⟩) → infᴮ X hX ≡ ⊤ᴮ
inf-empty X hX e =
  ≤ᴮ-antisym (⊤-greatest (infᴮ X hX))
             (inf-glb X hX ⊤ᴮ (λ u hu → Empty.rec* (e (fst u) hu)))

--------------------------------------------------------------------------------
-- Residuation: the replacement for the infinite distributive law
--------------------------------------------------------------------------------

-- THE LEMMA. To bound a ⊓ᴮ ⋁X below v it is enough to bound a ⊓ᴮ u below v for
-- each member u of X. In a complete Boolean algebra this is the infinite
-- distributive law; here it is residuation, and the three steps are named:
-- curry each pointwise bound into ⟨ u ≤ᴮ (a ⇒ᴮ v) ⟩, apply sup-lub to get
-- ⟨ ⋁X ≤ᴮ (a ⇒ᴮ v) ⟩, uncurry. Nothing is assumed about X, and in particular
-- the empty family is covered: there ⋁X is ⊥ᴮ and the conclusion is trivial.

sup-residual : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (a v : Pt B)
             → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ (a ⊓ᴮ u) ≤ᴮ v ⟩)
             → ⟨ (a ⊓ᴮ supᴮ X h) ≤ᴮ v ⟩
sup-residual X h a v f =
  subst (λ z → ⟨ z ≤ᴮ v ⟩) (⊓-comm (supᴮ X h) a)
    (⇒ᴮ-uncurry (supᴮ X h) a v
      (sup-lub X h (a ⇒ᴮ v)
        (λ u hu → ⇒ᴮ-curry u a v
                    (subst (λ z → ⟨ z ≤ᴮ v ⟩) (⊓-comm a u) (f u hu)))))

-- The same content with the meet already curried away. This is the shape a
-- reader of Bell will look for, since he writes the step as
-- ⋀ u (u ⇒ v) = (⋁ u) ⇒ v and uses the right hand side.

sup-residual-⇒ : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (a v : Pt B)
               → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ a ≤ᴮ (u ⇒ᴮ v) ⟩)
               → ⟨ a ≤ᴮ (supᴮ X h ⇒ᴮ v) ⟩
sup-residual-⇒ X h a v f =
  ⇒ᴮ-curry a (supᴮ X h) v
    (sup-residual X h a v (λ u hu → ⇒ᴮ-uncurry a u v (f u hu)))

-- THE DUAL, AND A MEASURED NEGATIVE ON THE ARCHITECTURE.
--
-- The architecture prints, at K4/Infinitary.agda in section 1.2:
--
--   inf-residual : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (a v : Pt B)
--                → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ a ≤ᴮ (u ⇒ᴮ v) ⟩)
--                → ⟨ a ≤ᴮ (infᴮ X h ⇒ᴮ v) ⟩
--
-- That statement is FALSE, and the counterexample is the empty family. Take X
-- with no members. Then infᴮ X h ≡ ⊤ᴮ by inf-empty above, so
-- infᴮ X h ⇒ᴮ v ≡ ⊤ᴮ ⇒ᴮ v ≡ v by ⇒ᴮ-⊤ˡ, while the hypothesis is vacuous. The
-- statement would therefore give ⟨ a ≤ᴮ v ⟩ for arbitrary a and v, which in a
-- nondegenerate algebra is refuted by a := ⊤ᴮ, v := ⊥ᴮ. The error is a swap of
-- infᴮ for supᴮ: the identity Bell uses is ⋀ u (u ⇒ v) = (⋁ u) ⇒ v, which is
-- sup-residual-⇒ above and not an infimum statement at all.
--
-- Two repairs ship, so that no consumer has to choose blind.
--
-- inf-residual is the GENUINE dual of sup-residual: the infimum on the RIGHT
-- of the implication, proved by inf-glb under the adjunction, unconditional
-- and covering the empty family. This is the name a later track should reach
-- for by default.

inf-residual : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (a v : Pt B)
             → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ a ≤ᴮ (v ⇒ᴮ u) ⟩)
             → ⟨ a ≤ᴮ (v ⇒ᴮ infᴮ X h) ⟩
inf-residual X h a v f =
  ⇒ᴮ-curry a v (infᴮ X h)
    (inf-glb X h (a ⊓ᴮ v) (λ u hu → ⇒ᴮ-uncurry a v u (f u hu)))

-- inf-residual-witnessed is the architecture's literal statement with the
-- hypothesis it was missing: ONE member of X. That is all the proof needs,
-- since infᴮ X h ≤ᴮ w for that member and the implication is antitone on the
-- left. A track that genuinely wants the architecture's shape can use this and
-- must supply the witness.

inf-residual-witnessed : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (a v w : Pt B)
                       → ⟨ fst w ∈ˢ X ⟩
                       → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ a ≤ᴮ (u ⇒ᴮ v) ⟩)
                       → ⟨ a ≤ᴮ (infᴮ X h ⇒ᴮ v) ⟩
inf-residual-witnessed X h a v w hw f =
  ⊆ˢ-trans (f w hw) (⇒ᴮ-antitoneˡ w (infᴮ X h) v (inf-lb X h w hw))

-- One more shape the atomic layer of K4.2 will want: an infimum bounds a fixed
-- value from below only through one of its members, so a bound on the whole
-- infimum is obtained from a bound on any single member.

inf-below : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u v : Pt B)
          → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ v ⟩ → ⟨ infᴮ X h ≤ᴮ v ⟩
inf-below X h u v hu k = ⊆ˢ-trans (inf-lb X h u hu) k

sup-above : (X : S) (h : ⟨ X ⊆ˢ B ⟩) (u v : Pt B)
          → ⟨ fst u ∈ˢ X ⟩ → ⟨ v ≤ᴮ u ⟩ → ⟨ v ≤ᴮ supᴮ X h ⟩
sup-above X h u v hu k = ⊆ˢ-trans k (sup-ub X h u hu)

--------------------------------------------------------------------------------
-- The measured negative, machine checked
--------------------------------------------------------------------------------

-- The paragraph above asserts that the architecture's printed inf-residual is
-- false. An assertion in a comment is not evidence, so the refutation is a
-- theorem. ArchInfResidual is the architecture's type, transcribed verbatim.

ArchInfResidual : Type ℓ
ArchInfResidual = (X : S) (h : ⟨ X ⊆ˢ B ⟩) (a v : Pt B)
                → ((u : Pt B) → ⟨ fst u ∈ˢ X ⟩ → ⟨ a ≤ᴮ (u ⇒ᴮ v) ⟩)
                → ⟨ a ≤ᴮ (infᴮ X h ⇒ᴮ v) ⟩

-- Read at an empty family it collapses the order: every value refines every
-- other. The hypothesis of the architecture's statement is vacuous there, and
-- its conclusion reduces to ⟨ a ≤ᴮ v ⟩ by inf-empty and ⇒ᴮ-⊤ˡ.

arch-collapses : ArchInfResidual
               → (X : S) (h : ⟨ X ⊆ˢ B ⟩)
               → ((b : S) → ⟨ b ∈ˢ X ⟩ → ⟨ ⊥ ⟩)
               → (a v : Pt B) → ⟨ a ≤ᴮ v ⟩
arch-collapses ir X h e a v =
  subst (λ z → ⟨ a ≤ᴮ z ⟩)
        (cong (_⇒ᴮ v) (inf-empty X h e) ∙ ⇒ᴮ-⊤ˡ v)
        (ir X h a v (λ u hu → Empty.rec* (e (fst u) hu)))

-- Hence the algebra is degenerate, which is the statement K2 fixes as the
-- negation of nontriviality (Certificate.agda:212-214). Any ground with
-- Separation has an empty coded subset of B, namely separateOf sep B ⊥̇
-- (CodedCompletion.agda:523-533 builds exactly that set and proves it empty),
-- so the premise of this theorem is not a vacuous one.
--
-- THIS IS THE REFUTATION. It is not a hole and not a stop report: the
-- architecture's inf-residual cannot be proved, and the two repairs above are
-- what a consumer gets instead.

arch-inf-residual-degenerate : ArchInfResidual
                             → (X : S) (h : ⟨ X ⊆ˢ B ⟩)
                             → ((b : S) → ⟨ b ∈ˢ X ⟩ → ⟨ ⊥ ⟩)
                             → ⊥ᴮ ≡ ⊤ᴮ
arch-inf-residual-degenerate ir X h e =
  sym (≤⊥→≡⊥ ⊤ᴮ (arch-collapses ir X h e ⊤ᴮ ⊥ᴮ))
