{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 Track D: the internalization contract.
--
-- Every name-valued construction of K3 has one shape. A host function
-- f : S -> S is already defined, and the question is whether the image of
-- the members of a ground code under f is again a ground code. K0 named
-- this hazard and forbade taking it silently: "A generic ground adapter
-- must prove the corresponding closure and decoding laws; it may not
-- receive unrestricted host-family closure as an implicit convenience"
-- (k0-representation-decision-2026-09.md, "Selected representation and
-- component boundaries", third paragraph).
--
-- What every downstream package consumes is the record InternalImage. It
-- is never a field of a ground record, and it is never an implicit
-- argument. Two routes discharge it and neither is a field either.
--
--   Route G, a definable graph, consumes Collection and Separation only.
--   Route I, the realization datum MemberImage of section 1.2 tier 4,
--   which is NOT a first order axiom: Collection reads a Formula S 2 and
--   a host function f : Pt a -> S has none, so no instance of Collection
--   applies to it (OrdinaryProfile.agda:95-101).
--
-- The tier 4 datum is isolated absolutely. It is not a parameter of this
-- module, it is not a field of any record declared here, and it occurs in
-- exactly one signature, member->image, as two flat arguments. Nothing
-- else in the file can reach it. The canonical home of the record is
-- NameGround.MemberImage; the two arguments are its two fields, so the
-- coordinator instantiates with
--   member->image (MemberImage.image M) (MemberImage.image-spec M).
--
-- The hypotheses of the module, and this is the whole list: the structure,
-- ordinary Extensionality, and the path realization of the structure
-- equality. These are exactly GroundDescription's, because the image term
-- is read off by its description bridge. Collection and Separation are
-- arguments of the theorems that consume them, never module parameters,
-- on the discipline of GroundDescription.hasImage' (GroundDescription.agda:181).
--
-- No L. import, no V. import, no isZFModel, no LEM, no PowerSet, no
-- Union, no Pairing, no Infinity, no accessibility.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile

module NameImage
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Term; con; var; Formula; _∧̇_; ∃̇_; ∃̇∈ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_; ⟦_⟧ )

-- Opened directly rather than through a module alias. An alias such as
-- GroundDescription's `module OP` is re-exported, so any consumer that
-- makes the same alias fails with ShadowedModule; measured, and recorded
-- in this track's report.
open import OrdinaryProfile 𝒮 using ( Separation; Collection )

open import GroundDescription 𝒮 ext paths
  using ( SetExists; the; the-spec; ext-path; hasImage′ )

open import CodedVocabulary 𝒮
  using ( isKPairΔ; prAtˢ; instFo; Fits; ⊨-inst )

-- ---------------------------------------------------------------------
-- The contract
-- ---------------------------------------------------------------------

-- The image class, written once. "z is a value of f at some member of a".
-- The existential is the algebra's join over the carrier, so the class is
-- Ω valued and the record below is a statement about paths in Ω.

ImageClass : (S → S) → S → S → Ω
ImageClass f a z = ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))

-- What Tracks F, G and H consume. Neither discharge route is a field:
-- the consumer sees an operation and its membership specification, and
-- learns nothing about how the operation was obtained.
--
-- The level is forced. img is at Type ℓ, but img-spec is a path in
-- Ω = hProp ℓ : Type (ℓ-suc ℓ), so the record is at Type (ℓ-suc ℓ) and
-- cannot index a join over a small type. Section 1.1's rule, applied.

record InternalImage (f : S → S) : Type (ℓ-suc ℓ) where
  field
    img      : S → S
    img-spec : (a z : S) → (z ∈ˢ img a) ≡ ImageClass f a z

-- The internalization of a given f is unique where it exists, so a
-- consumer that receives two of them receives one operation. This is
-- Extensionality and nothing else, and it is why the contract may be
-- passed around as data without a coherence obligation.

img-unique : {f : S → S} (I J : InternalImage f) (a : S)
           → InternalImage.img I a ≡ InternalImage.img J a
img-unique I J a = ext-path (λ z →
  InternalImage.img-spec I a z ∙ sym (InternalImage.img-spec J a z))

-- ---------------------------------------------------------------------
-- Route G. Definable graphs
-- ---------------------------------------------------------------------

-- The relativized form. A graph formula has to define f only at the
-- members of the set whose image is being taken, and that is all any
-- consumer of the route ever has: an approximation to a recursion knows
-- the values below one point and nothing above it. The production record
-- L.Recursion.Definition is relativized in exactly this way, by its dom
-- field (src/L/Recursion.lagda.md:292-299), and the strong record's
-- hasReplacement takes its functionality hypothesis relativized too
-- (src/FOL/ZFModel.lagda.md:226-228).
--
-- The level is Type ℓ, not Type (ℓ-suc ℓ): Formula S 2 is at Type ℓ
-- (FOL/Syntax, data Formula {ℓ} (K : Type ℓ) (n : ℕ) : Type ℓ) and both
-- other fields are ⟨_⟩ of an element of Ω, so at Type ℓ as well. Nothing
-- here is a path in Ω.

record DefinableGraphOn (a : S) (f : S → S) : Type ℓ where
  field
    graph   : Formula S 2
    defines : (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (f x ∷ x ∷ []) ⊨ graph ⟩
    only    : (x : S) → ⟨ x ∈ˢ a ⟩ → (y : S)
            → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ f x

-- The total form, for a function whose graph is definable everywhere.
-- This is L.Recursion.Definition minus its dom field. L.Recursion accepts
-- any complexity of graph formula, so a Σ₁ graph is legal here and no Δ₀
-- witness is asked for anywhere in this file.

record DefinableGraph (f : S → S) : Type ℓ where
  field
    graph   : Formula S 2
    defines : (x : S) → ⟨ (f x ∷ x ∷ []) ⊨ graph ⟩
    only    : (x y : S) → ⟨ (y ∷ x ∷ []) ⊨ graph ⟩ → y ≡ f x

total→on : {f : S → S} → DefinableGraph f → (a : S) → DefinableGraphOn a f
total→on D a = record
  { graph   = D.graph
  ; defines = λ x _ → D.defines x
  ; only    = λ x _ y h → D.only x y h }
  where module D = DefinableGraph D

-- Functionality in the shape the image theorem wants. The type of
-- realizers of the graph at one argument is contractible, because the
-- value is a centre and being a realizer is a proposition. This is the
-- body of asRecursion (src/L/Recursion.lagda.md:305-312), relativized.

graph-functional : {a : S} {f : S → S} (D : DefinableGraphOn a f)
                 → (x : S) → ⟨ x ∈ˢ a ⟩
                 → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ DefinableGraphOn.graph D ⟩)
graph-functional {f = f} D x x∈ =
  (f x , D.defines x x∈)
  , λ { (y , h) → Σ≡Prop (λ w → snd ((w ∷ x ∷ []) ⊨ D.graph))
                    (sym (D.only x x∈ y h)) }
  where module D = DefinableGraphOn D

-- The route, in one theorem. Collection and Separation produce a set
-- whose members are the realizers of the graph over a; the two
-- directions of the graph then rewrite "realizes the graph at x" as
-- "is the value at x", by the path realization of the structure equality.
-- The class argument of `the` is written out as the named Q, per
-- GroundDescription.agda:113-121.

-- The two are sealed together in one opaque block. The image term is a
-- description term, `the Q ex`, and a description term unfolds into a stuck
-- truncation eliminator on a ground axiom field; nesting several of them is
-- what exhausts the typechecker. Track A measured the cost of leaving one
-- unsealed: 761 s user at 1.05 GB and no result, against 1.04 s at 327 MB
-- sealed. K3's name constructions nest these three deep, so the seal goes
-- on at the point of definition. `opaque` composes, so a consumer that
-- genuinely needs the unfolding writes an unfolding declaration.
--
-- The contract record seals the other route by construction: a consumer of
-- InternalImage sees img as a record field of a parameter, which is stuck
-- for the same reason without anyone having to ask.

opaque
  graph→image : Collection → Separation → (f : S → S) (a : S)
              → DefinableGraphOn a f
              → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T) ≡ ImageClass f a z)
  graph→image coll sep f a D = the Q ex , the-spec Q ex
    where
    module D = DefinableGraphOn D

    Q : S → Ω
    Q = ImageClass f a

    fwd : (z x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (z ∷ x ∷ []) ⊨ D.graph ⟩ → ⟨ z ≈ˢ f x ⟩
    fwd z x x∈ h = subst ⟨_⟩ (sym (paths z (f x))) (D.only x x∈ z h)

    bwd : (z x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ z ≈ˢ f x ⟩ → ⟨ (z ∷ x ∷ []) ⊨ D.graph ⟩
    bwd z x x∈ e =
      subst (λ w → ⟨ (w ∷ x ∷ []) ⊨ D.graph ⟩)
        (sym (subst ⟨_⟩ (paths z (f x)) e)) (D.defines x x∈)

    ex : ⟨ SetExists Q ⟩
    ex = PT.map
      (λ { (b , h) → b , (λ z →
             (λ z∈b → PT.map (λ { (x , x∈ , h') → x , x∈ , fwd z x x∈ h' })
                        (h z .fst z∈b))
           , (λ q → h z .snd (PT.map (λ { (x , x∈ , e) → x , x∈ , bwd z x x∈ e })
                        q))) })
      (hasImage′ sep coll a D.graph (graph-functional D))

  graph→internal : Collection → Separation → (f : S → S)
                 → DefinableGraph f → InternalImage f
  graph→internal coll sep f D = record
    { img      = λ a → fst (graph→image coll sep f a (total→on D a))
    ; img-spec = λ a → snd (graph→image coll sep f a (total→on D a)) }

-- ---------------------------------------------------------------------
-- Route I. The realization datum
-- ---------------------------------------------------------------------

-- The class the datum specifies. The index of the join is the type of
-- members of a, at Type ℓ, so the join is legal; writing the second join
-- over S, as the architecture's section 1.7 does, is not, because the
-- proof of membership is not an element of the carrier.

MemberClass : (a : S) → (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩ → S) → S → Ω
MemberClass a f z = ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h)))

-- A host function on the carrier is in particular a host function on the
-- members of any code, so the datum internalizes it. The only content is
-- that a join over the proofs of a proposition collapses to a meet with
-- that proposition.

member→image :
    (image : (a : S) → (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩ → S) → S)
  → (image-spec : (a : S) (g : Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩ → S) (z : S)
                → (z ∈ˢ image a g) ≡ MemberClass a g z)
  → (f : S → S) → InternalImage f
member→image image image-spec f = record
  { img      = λ a → image a (λ p → f (fst p))
  ; img-spec = λ a z → image-spec a (λ p → f (fst p)) z ∙ collapse a z }
  where
  -- Lesson 1 of the preamble, met head on. The two endpoints of ⇔toPath
  -- are elements of Ω, and Ω is a pair of a type and a proof that the
  -- type is a proposition. Unifying the goal fixes the carrier half and
  -- leaves the isProp half an unsolved metavariable, measured here with
  -- the exact error in this track's report. The fix is the preamble's
  -- fix: name the endpoint through a local with a written out type.
  step : (a z x : S)
       → (⋁ ⟨ x ∈ˢ a ⟩ (λ _ → z ≈ˢ f x)) ≡ ((x ∈ˢ a) ⊓ (z ≈ˢ f x))
  step a z x = ⇔toPath
    (PT.rec (snd ((x ∈ˢ a) ⊓ (z ≈ˢ f x))) (λ { (h , e) → h , e }))
    (λ { (h , e) → ∣ h , e ∣₁ })

  collapse : (a z : S) → MemberClass a (λ p → f (fst p)) z ≡ ImageClass f a z
  collapse a z = cong (⋁ S) (funExt (step a z))

-- ---------------------------------------------------------------------
-- Two free variables and constants: the shape Collection wants
-- ---------------------------------------------------------------------

-- CodedVocabulary supplies sepAt, which freezes every slot but one into a
-- constant and hands Separation its Formula S 1 (CodedVocabulary.agda:541).
-- Collection wants two free slots, and the tree has no such operation.
-- This is that operation, built from the same instFo and proved by the
-- same ⊨-inst, so no new formula manipulation enters K3.

atCon₂ : ∀ {k} → Vec S k → Fin (suc (suc k)) → Term S 2
atCon₂ ps zero          = var zero
atCon₂ ps (suc zero)    = var (suc zero)
atCon₂ ps (suc (suc i)) = con (lookup i ps)

atCon₂-fits : ∀ {k} (ps : Vec S k) (y x : S)
            → Fits (atCon₂ ps) (y ∷ x ∷ []) (y ∷ x ∷ ps)
atCon₂-fits ps y x zero          = refl
atCon₂-fits ps y x (suc zero)    = refl
atCon₂-fits ps y x (suc (suc i)) = refl

colAt : ∀ {k} → Formula S (suc (suc k)) → Vec S k → Formula S 2
colAt φ ps = instFo (atCon₂ ps) φ

colAt-reading : ∀ {k} (φ : Formula S (suc (suc k))) (ps : Vec S k) (y x : S)
              → ((y ∷ x ∷ []) ⊨ colAt φ ps) ≡ ((y ∷ x ∷ ps) ⊨ φ)
colAt-reading φ ps y x =
  ⊨-inst (atCon₂ ps) φ (y ∷ x ∷ []) (y ∷ x ∷ ps) (atCon₂-fits ps y x)

-- ---------------------------------------------------------------------
-- The worked discharge: the check name
-- ---------------------------------------------------------------------

-- Bell's check name sends a ground set a to the name whose entries are
-- the pairs (check y, top) for y a member of a (Bell 1.22,
-- bell-2005-boolean-valued-models.fulltext.md:2336). The three data below
-- are Track A's interface, taken flat: the module states the hypothesis
-- and the coordinator instantiates it when the kernel lands. entry and
-- entry-isKPair are Track A deliverables verbatim (section 1.3);
-- entry-canonical is the Kuratowski converse, which follows from
-- entry-spec and Extensionality and which Track A should export beside
-- entry-inj. w₀ is the weight code, ⊤ᴮ at the Boolean instance; the
-- opacity rule keeps the Boolean algebra out of this file, so it is a set.

module CheckDischarge
  (entry : S → S → S)
  (entry-isKPair : (x b : S) → ⟨ isKPairΔ (entry x b) x b ⟩)
  (entry-canonical : (q u v : S) → ⟨ isKPairΔ q u v ⟩ → q ≡ entry u v)
  (w₀ : S)
  where

  -- The graph formula. Read it as: y is the entry of the check value of
  -- x, that is, some v is paired with x in the table F and y is the
  -- Kuratowski pair of v and the weight. The leading existential is
  -- unbounded, so the formula is Σ₁ and carries no Δ₀ witness; Collection
  -- accepts any Formula S 2 and L.Recursion accepts any complexity, so
  -- neither consumer asks for one. No slot is a constant: every argument
  -- position is a Fin n, so the formula can be placed inside a larger one
  -- and is frozen into Formula S 2 by colAt at the end.

  checkFo : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Formula S n
  checkFo y x F w =
      ∃̇ ( (∃̇∈ (var (suc F)) (prAtˢ zero (suc (suc x)) (suc zero)))
        ∧̇ prAtˢ (suc y) zero (suc w) )

  CheckΔ : S → S → S → Ω
  CheckΔ F y x =
    ⋁ S (λ v → (⋁ S (λ e → (e ∈ˢ F) ⊓ isKPairΔ e x v)) ⊓ isKPairΔ y v w₀)

  checkFo-reading : ∀ {n} (y x F w : Fin n) (γ : S ^ n)
    → (γ ⊨ checkFo y x F w)
    ≡ ⋁ S (λ v → (⋁ S (λ e → (e ∈ˢ lookup F γ) ⊓ isKPairΔ e (lookup x γ) v))
               ⊓ isKPairΔ (lookup y γ) v (lookup w γ))
  checkFo-reading y x F w γ = refl

  checkAtˢ : S → Formula S 2
  checkAtˢ F =
    colAt (checkFo zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))))
          (F ∷ w₀ ∷ [])

  checkAtˢ-reading : (F y x : S) → ((y ∷ x ∷ []) ⊨ checkAtˢ F) ≡ CheckΔ F y x
  checkAtˢ-reading F y x =
    colAt-reading (checkFo zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))))
      (F ∷ w₀ ∷ []) y x

  -- One stage of the recursion. F is a table for chk over a: it holds the
  -- pair of x with chk x for every member x of a, and it records no other
  -- value at a member of a. Nothing says F is a function, nothing says a
  -- is transitive, and nothing says chk is the check operation anywhere
  -- outside a. This is the weakest hypothesis under which the stage's
  -- image is definable, and it is what an approximation supplies.

  module Stage (a F : S) (chk : S → S)
    (F-mem  : (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ entry x (chk x) ∈ˢ F ⟩)
    (F-only : (e u v : S) → ⟨ u ∈ˢ a ⟩ → ⟨ e ∈ˢ F ⟩
            → ⟨ isKPairΔ e u v ⟩ → v ≡ chk u)
    where

    valueOf : S → S
    valueOf x = entry (chk x) w₀

    check-graph : DefinableGraphOn a valueOf
    check-graph = record { graph = checkAtˢ F ; defines = def ; only = onl }
      where
      def : (x : S) → ⟨ x ∈ˢ a ⟩ → ⟨ (valueOf x ∷ x ∷ []) ⊨ checkAtˢ F ⟩
      def x x∈ = subst ⟨_⟩ (sym (checkAtˢ-reading F (valueOf x) x))
        ∣ chk x
        , ( ∣ entry x (chk x) , (F-mem x x∈ , entry-isKPair x (chk x)) ∣₁
          , entry-isKPair (chk x) w₀ ) ∣₁

      onl : (x : S) → ⟨ x ∈ˢ a ⟩ → (y : S)
          → ⟨ (y ∷ x ∷ []) ⊨ checkAtˢ F ⟩ → y ≡ valueOf x
      onl x x∈ y h = PT.rec (isSetS y (valueOf x))
        (λ { (v , inF , kp) → PT.rec (isSetS y (valueOf x))
             (λ { (e , e∈F , kpe) →
                  entry-canonical y v w₀ kp
                  ∙ cong (λ u → entry u w₀) (F-only e x v x∈ e∈F kpe) })
             inF })
        (subst ⟨_⟩ (checkAtˢ-reading F y x) h)

    -- The stage image itself: the set of entries the check name at a must
    -- have. This is the one worked discharge, and it is worked at the only
    -- granularity at which Collection can reach the check recursion.

    check-image : Collection → Separation
                → Σ[ T ∈ S ] ((z : S) → (z ∈ˢ T) ≡ ImageClass valueOf a z)
    check-image coll sep = graph→image coll sep valueOf a check-graph

  -- And the reason the stage is where the work is. The recursion equation
  -- of the check name and the internalization contract for its entry map
  -- are the SAME statement: the pair of the operation chk and its
  -- membership specification is literally an InternalImage record, and
  -- conversely an InternalImage record whose operation is chk is literally
  -- the recursion equation. The contract of this module produces img for a
  -- GIVEN f; check is the fixed point at which f is built from img itself,
  -- and no tier of section 1.2 produces a fixed point.

  CheckSpec : (S → S) → Type (ℓ-suc ℓ)
  CheckSpec chk =
    (a z : S) → (z ∈ˢ chk a) ≡ ImageClass (λ y → entry (chk y) w₀) a z

  check-spec→internal : (chk : S → S) → CheckSpec chk
                      → InternalImage (λ y → entry (chk y) w₀)
  check-spec→internal chk sp = record { img = chk ; img-spec = sp }

  internal→check-spec : (chk : S → S) (I : InternalImage (λ y → entry (chk y) w₀))
                      → ((a : S) → InternalImage.img I a ≡ chk a)
                      → CheckSpec chk
  internal→check-spec chk I fix a z =
    cong (z ∈ˢ_) (sym (fix a)) ∙ InternalImage.img-spec I a z
