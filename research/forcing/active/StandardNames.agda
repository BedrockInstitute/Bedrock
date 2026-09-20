{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 module K3.8 (Track H): the standard names.
--
-- Two constructions and one diagonal. The check name embeds a ground set as
-- a name whose value is that same set again, and the generic name is the
-- name whose value is the generic filter itself. Bell's Definition 1.22
-- (bell-2005-boolean-valued-models.fulltext.md:2336) writes the first as
--
--     x̌ = { ⟨y̌ , 1⟩ : y ∈ x }
--
-- "a definition by recursion on the well-founded relation y ∈ x", in Bell's
-- own words on the next line. The Boolean side weights every entry by the
-- top of the algebra. The poset side has no top to weight with: K2's
-- ForcingNotion record carries no largest element, Top is standalone data
-- (ForcingNotion.agda:267-268), so the poset check name weights each entry
-- by EVERY condition. Section 1.10's decision is that this is not a second
-- design but the image of the first under the reverse translation, because
-- below ⊤ᴮ is the whole carrier.
--
-- This file takes that seriously in the only way that survives compilation:
-- ONE weighted recursion, taken over an abstract weight set W₀, instantiated
-- twice. At W₀ = {⊤ᴮ} it is check; at W₀ = carrier it is checkᴾ. The bridge
-- to the reverse translation is then a THEOREM (module Reverse), not the
-- definition of checkᴾ. Section 3 of REPORT-H.md gives the evidence for
-- turning the architecture's dependency around; the short version is that
-- Track D measured trᴾ's internalization to be the same unreached fixed
-- point as check's, and Track I is already finished and waiting for checkᴾ.
--
-- ---------------------------------------------------------------------
-- The ledger, which is the module telescope and nothing else
-- ---------------------------------------------------------------------
--
-- Nothing is imported from Track A, D, G or K2. Every interface is a flat
-- module parameter, so this file compiles against no other K3 track and a
-- change upstream cannot invalidate it. Section 6 of REPORT-H.md gives the
-- character-for-character correspondence with the landed files.
--
-- Track A's kernel interface (NameKernel.agda): entry, entry-inj, singleOf,
-- singleOf-spec, singleOf-member, Child, an eliminator for Child, and Core's
-- own ≈ˢ-paths. Per weight carrier: Shape with its introduction rule, IsName,
-- and name-intro.
--
-- Tier 0 (NameKernel.Accessibility): acc∈ : WellFounded _∈ᵗ_. This is the
-- MEMBERSHIP accessibility of the ground and it is a different datum from the
-- name-level child-wf that Track A derives from it. child-wf does not appear
-- in this file. Bell's recursion is on y ∈ x and on nothing else, and a name
-- built by a Child-recursion would be a different object; keeping the two
-- apart is the whole point of section 1.10's second decision.
--
-- Tier 4 (NameKernel.MemberImage): image and image-spec, flat. This is the
-- widening Track D's finding F8 predicted and priced. It is not derivable
-- from any first-order axiom, it is load bearing jointly with tier 0, and
-- neither alone produces check. See section 2 of REPORT-H.md.
--
-- Tier 2, the Union half only: unionOf and unionOf-spec, flat. Charged once,
-- and charged only by the poset side. Track B's ⋃ᴳ and ⋃ᴳ-spec
-- (NameSupport.agda:444-448) are these two parameters character for character,
-- already built through the description bridge with the class written out and
-- already sealed with the specification in one opaque block. See section 2.3 of
-- REPORT-H.md for the one caveat about where they sit.
--
-- K2, as codes: carrier, B, ⊤ᴮ with ⊤ᴮ ∈ˢ B, and the inhabitedness of the
-- carrier. Track G's below and trᴾ enter only in module Reverse.
--
-- NOT taken, and the absences are part of the contract: no Separation, no
-- Collection, no PowerSet, no Infinity, no Foundation schema, no LEM at any
-- level, no isZFModel, no L import, no V import, no order on the carrier, no
-- Boolean algebra, no completion record, and no i. The architecture's Track H
-- parameter list names i; nothing here can use it, and section 3.5 of
-- REPORT-H.md records that as a measured over-declaration.
--
-- ---------------------------------------------------------------------
-- The three mechanical lessons of the shared preamble, as they apply here
-- ---------------------------------------------------------------------
--
-- (1) Every equality of Ω-valued expressions below is closed by ⇔toPath with
-- both maps written out, or by cong at a single-argument function. No bare
-- refl ever sits inside a congruence over ⊓, ⋁ or ⇒, so no isProp component
-- is left as a metavariable.
--
-- (2) The implicit-class trap cannot arise, because this file uses no
-- description operator. Every ground code former is a module parameter, and a
-- parameter is a variable: it has no unfolding at all. That is also why the
-- opacity rule Track A measured (NameKernel.agda's pairOf: 761 s transparent,
-- 1.04 s sealed) costs this file nothing to obey. Section 4 of REPORT-H.md
-- reports the measurement. Whoever discharges image and unionOf from the
-- description bridge must seal each with its specification there, which Track B
-- has already done for the union (NameSupport.agda:443-448).
--
-- (3) There is no negation anywhere in this file, so the bottom-element trap
-- cannot arise either.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )

module StandardNames {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

--------------------------------------------------------------------------------
-- One join that collapses, and the internalization contract
--------------------------------------------------------------------------------

-- The member-image specification joins over the membership witness, which is
-- a proposition. A join over a proposition, at a family that does not depend
-- on the witness, is just a meet. This is the only lemma in the file that is
-- pure truth-value algebra, and it is used at every place where an image
-- specification is turned into the ⊓-shaped form the architecture writes.

∃-prop : (A Q : Ω) → ⋁ ⟨ A ⟩ (λ _ → Q) ≡ (A ⊓ Q)
∃-prop A Q = ⇔toPath
  (PT.rec (snd (A ⊓ Q)) (λ z → z))
  (λ z → ∣ z ∣₁)

-- Track D's contract record (NameImage.agda:97), restated so that this file
-- imports nothing. A consumer receives an operation and its membership
-- specification and learns nothing about how the operation was obtained.
-- check-internal below is an inhabitant of it, and it is exactly what Track
-- D's check-spec→internal (NameImage.agda:401) produces from check-spec.

record InternalImage (f : S → S) : Type (ℓ-suc ℓ) where
  field
    img      : S → S
    img-spec : (a z : S) → (z ∈ˢ img a) ≡ ⋁ S (λ x → (x ∈ˢ a) ⊓ (z ≈ˢ f x))

--------------------------------------------------------------------------------
-- The kernel interface
--------------------------------------------------------------------------------

-- Track A owns every parameter of this module. entry x b is the Kuratowski
-- pair weighting the subname x by b, singleOf is the singleton, Child is the
-- subname relation, and ≈ˢ-paths is Core's own field realizing the
-- structure's equality as a host path.
--
-- child-elim is the elimination rule for Child at an Ω-valued motive. Track A
-- defines Child x n = ∥ Σ[ b ∈ S ] ⟨ entry x b ∈ˢ n ⟩ ∥₁ transparently
-- (NameKernel.agda:368), so it is discharged by one PT.rec; it is taken as a
-- parameter rather than read off the definition so that this file still works
-- if Track A ever seals Child. Track I took the introduction rule child-entry
-- for the same reason and noted the same thing; validity needs the other half.
--
-- ext-path is GroundDescription's one-line host-path extensionality
-- (GroundDescription.agda:77), reachable as Kernel.GD.ext-path. It is the
-- only form in which ordinary Extensionality enters, and it enters at exactly
-- two theorems: chk-inj and checkᴾ-is-reverse.

module Kernel
  (entry           : S → S → S)
  (entry-inj       : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
  (singleOf        : S → S)
  (singleOf-spec   : (a z : S) → ⟨ z ∈ˢ singleOf a ⟩ → z ≡ a)
  (singleOf-member : (a : S) → ⟨ a ∈ˢ singleOf a ⟩)
  (Child           : S → S → Type ℓ)
  (child-elim      : (x n : S) (Q : Ω) → Child x n
                   → ((b : S) → ⟨ entry x b ∈ˢ n ⟩ → ⟨ Q ⟩) → ⟨ Q ⟩)
  (≈ˢ-paths        : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
  (ext-path        : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
  where

-- Equality in the two shapes the two layers use. Every crossing below goes
-- through one of these three lines and through nothing else.

  ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
  ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (≈ˢ-paths x y)

  ≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
  ≡→≈ˢ {x} {y} = subst ⟨_⟩ (sym (≈ˢ-paths x y))

  ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
  ≈ˢ-refl x = ≡→≈ˢ refl

--------------------------------------------------------------------------------
-- Validity, once, for an arbitrary weight carrier
--------------------------------------------------------------------------------

-- Being a name is a shape clause plus a hereditary clause. The shape clause
-- says every member is an entry whose weight lies in W; the hereditary clause
-- says every child is itself a name. All four standard names below are
-- presented the same way, by listing their members, so all four validity
-- proofs are one lemma.
--
-- shape-intro is the identity at Track A's definition: Shape n's carrier IS
-- that Π type (NameKernel.agda:442-444). It is named rather than inlined so
-- that this module does not depend on Shape being transparent.

  module Validity
    (W           : S)
    (Shape       : S → Ω)
    (shape-intro : (n : S)
                 → ((e : S) → ⟨ e ∈ˢ n ⟩
                    → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ] ((e ≡ entry x b) × ⟨ b ∈ˢ W ⟩) ∥₁)
                 → ⟨ Shape n ⟩)
    (IsName      : S → Ω)
    (name-intro  : (n : S) → ⟨ Shape n ⟩
                 → ((x : S) → Child x n → ⟨ IsName x ⟩) → ⟨ IsName n ⟩)
    where

-- The one validity lemma. Read the hypothesis as a listing of the code's
-- members: each is an entry, its weight lies in the carrier, and its first
-- coordinate is already a name. The hereditary clause is where injectivity of
-- the entry is spent, and it is spent exactly once: a child arrives with SOME
-- weight, the listing hands back an entry equal to that one, and entry-inj
-- identifies the two first coordinates so the child inherits the name proof
-- the listing carried.

    entries-name : (n : S)
                 → ((e : S) → ⟨ e ∈ˢ n ⟩
                    → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                        ((e ≡ entry x b) × (⟨ b ∈ˢ W ⟩ × ⟨ IsName x ⟩)) ∥₁)
                 → ⟨ IsName n ⟩
    entries-name n h = name-intro n shape hered
      where
        shape : ⟨ Shape n ⟩
        shape = shape-intro n (λ e m →
          PT.map (λ { (x , b , p , hb , _) → x , b , p , hb }) (h e m))

        hered : (x : S) → Child x n → ⟨ IsName x ⟩
        hered x edge = child-elim x n (IsName x) edge
          (λ b m → PT.rec (snd (IsName x))
            (λ { (u , c , p , _ , hu) →
                   subst (λ t → ⟨ IsName t ⟩) (sym (fst (entry-inj p))) hu })
            (h (entry x b) m))

--------------------------------------------------------------------------------
-- The weighted check recursion
--------------------------------------------------------------------------------

-- Now the mathematics. Bell's recursion sends a ground set a to the name
-- whose entries pair the check name of each member with a weight. Two
-- questions have to be answered before a line of Agda can be written, and the
-- architecture answers only the first.
--
-- The first is what the recursion recurses on. It recurses on the ground's
-- membership, because y ranges over the members of a and nothing else
-- descends. The name-level Child relation is not available: the object being
-- built is the name, so there is no name yet to take children of. That is
-- section 1.10's second decision and it is why acc∈ is a parameter here.
--
-- The second is what makes the step's output a ground SET rather than a class.
-- The step forms { entry (check y) p : y ∈ a , p ∈ W₀ }, and no first-order
-- axiom of the ordinary profile forms it: Collection reads a Formula S 2, and
-- check at the moment the step runs is a host function with no formula. Track
-- D measured this as its keystone negative and measured the positive
-- complement in a four-line probe (REPORT-D.md, findings F5 and F6): tier-0
-- accessibility together with the tier-4 member image gives check and its full
-- recursion equation, and neither datum alone does. image and image-spec below
-- are that datum, flat.
--
-- Why the weight set is abstract. The Boolean check name attaches one weight,
-- the top; the poset check name attaches all of them. If those were two
-- recursions there would be two objects to prove things about twice. Taken
-- over an abstract W₀ they are one object with two instantiations, which is
-- precisely the discipline Track A used for the kernel itself.

  module Weighted
    (acc∈         : WellFounded _∈ᵗ_)
    (image        : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) → S)
    (image-spec   : (a : S) (f : (Σ[ x ∈ S ] ⟨ x ∈ˢ a ⟩) → S) (z : S)
                  → (z ∈ˢ image a f)
                  ≡ ⋁ S (λ x → ⋁ ⟨ x ∈ˢ a ⟩ (λ h → z ≈ˢ f (x , h))))
    (unionOf      : S → S)
    (unionOf-spec : (t z : S) → (z ∈ˢ unionOf t)
                  ≡ ⋁ S (λ u → (u ∈ˢ t) ⊓ (z ∈ˢ u)))
    where

-- The image of a HOST function over a code. Most images taken below do not
-- read the membership witness at all, and for those the tier-4 datum's
-- specification collapses to the ⊓-shaped form the architecture writes. Only
-- the recursion itself needs the witness, because the recursive call does.

    imageOn : S → (S → S) → S
    imageOn c f = image c (λ q → f (fst q))

    imageOn-spec : (c : S) (f : S → S) (z : S)
                 → (z ∈ˢ imageOn c f) ≡ ⋁ S (λ x → (x ∈ˢ c) ⊓ (z ≈ˢ f x))
    imageOn-spec c f z =
      image-spec c (λ q → f (fst q)) z
      ∙ cong (⋁ S) (funExt (λ x → ∃-prop (x ∈ˢ c) (z ≈ˢ f x)))

-- The weight set is fixed from here down. Everything in this module is
-- stated for an arbitrary W₀ and instantiated twice below.

    module Over (W₀ : S) where

-- One subname, spread over the whole weight set. This is the layer of a
-- check name contributed by a single member, and it is the only place the
-- weights enter.

      spread : S → S
      spread x = imageOn W₀ (λ p → entry x p)

      spread-spec : (x e : S) → (e ∈ˢ spread x)
                  ≡ ⋁ S (λ p → (p ∈ˢ W₀) ⊓ (e ≈ˢ entry x p))
      spread-spec x e = imageOn-spec W₀ (λ p → entry x p) e

-- The recursion. The step takes the union of the layers of the members, and
-- the Union is charged here and nowhere else. Note that at a SINGLETON weight
-- set each layer is a singleton, so the union is inessential and the step is
-- just image a; section 2.3 of REPORT-H.md records that the Boolean check
-- name alone does not need Union, and the corresponding one-line definition.
--
-- The computation law is PROPOSITIONAL, as every well-founded recursion in
-- the host is. Nothing below expects chk to reduce; every use rewrites along
-- chk-host, or, much more often, along chk-spec.

      chkStep : (a : S) → ((y : S) → y ∈ᵗ a → S) → S
      chkStep a rec = unionOf (image a (λ q → spread (rec (fst q) (snd q))))

      chk : S → S
      chk = WFI.induction acc∈ {P = λ _ → S} chkStep

      chk-host : (a : S) → chk a ≡ unionOf (imageOn a (λ y → spread (chk y)))
      chk-host = WFI.induction-compute acc∈ {P = λ _ → S} chkStep

-- And the membership specification, which is the form every consumer uses.
-- Reading it: e is a member of the check name of a exactly when some member y
-- of a and some weight p of the weight set make e the entry pairing the check
-- name of y with p. The two layers of the definition, the union and the
-- image, have both been absorbed; a consumer never sees them again.

      chk-spec : (a e : S) → (e ∈ˢ chk a)
               ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ W₀) ⊓ (e ≈ˢ entry (chk y) p)))
      chk-spec a e =
          cong (e ∈ˢ_) (chk-host a)
        ∙ unionOf-spec (imageOn a (λ y → spread (chk y))) e
        ∙ ⇔toPath to fro
        where
          to : ⟨ ⋁ S (λ u → (u ∈ˢ imageOn a (λ y → spread (chk y))) ⊓ (e ∈ˢ u)) ⟩
             → ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ W₀) ⊓ (e ≈ˢ entry (chk y) p))) ⟩
          to = PT.rec PT.squash₁ (λ { (u , hu , he) →
            PT.rec PT.squash₁
              (λ { (y , hy , equ) → ∣ y , hy
                 , subst ⟨_⟩ (spread-spec (chk y) e)
                     (subst (λ t → ⟨ e ∈ˢ t ⟩) (≈ˢ→≡ equ) he) ∣₁ })
              (subst ⟨_⟩ (imageOn-spec a (λ y → spread (chk y)) u) hu) })

          fro : ⟨ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ W₀) ⊓ (e ≈ˢ entry (chk y) p))) ⟩
              → ⟨ ⋁ S (λ u → (u ∈ˢ imageOn a (λ y → spread (chk y))) ⊓ (e ∈ˢ u)) ⟩
          fro = PT.rec PT.squash₁ (λ { (y , hy , hp) →
            ∣ spread (chk y)
            , subst ⟨_⟩ (sym (imageOn-spec a (λ y' → spread (chk y')) (spread (chk y))))
                ∣ y , hy , ≈ˢ-refl (spread (chk y)) ∣₁
            , subst ⟨_⟩ (sym (spread-spec (chk y) e)) hp ∣₁ })

-- The two directions of the specification, packaged. Every later proof in
-- this file uses these and not chk-spec directly. entry-out discards the
-- weight: which weight carried the entry is not recoverable from the entry
-- alone once entry-inj has been applied to the first coordinate, and no
-- theorem here asks for it.

      entry-in : (m z p : S) → ⟨ z ∈ˢ m ⟩ → ⟨ p ∈ˢ W₀ ⟩
               → ⟨ entry (chk z) p ∈ˢ chk m ⟩
      entry-in m z p hz hp = subst ⟨_⟩ (sym (chk-spec m (entry (chk z) p)))
        ∣ z , hz , ∣ p , hp , ≈ˢ-refl (entry (chk z) p) ∣₁ ∣₁

      entry-out : (m x p : S) → ⟨ entry x p ∈ˢ chk m ⟩
                → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ m ⟩ × (x ≡ chk y)) ∥₁
      entry-out m x p h = PT.rec PT.squash₁
        (λ { (y , hy , inner) → PT.map
               (λ { (q , _ , eq) → y , hy , fst (entry-inj (≈ˢ→≡ eq)) })
               inner })
        (subst ⟨_⟩ (chk-spec m (entry x p)) h)

-- Validity of the check name, at any weight carrier W that contains the
-- weight set. The induction is on the ground's membership again, because the
-- children of chk a are the chk y for y ∈ a, and those descend in ∈ and not
-- in anything else. This is the second and last use of acc∈ on the Boolean
-- side.

      module Valid
        (W            : S)
        (IsName       : S → Ω)
        (entries-name : (n : S)
                      → ((e : S) → ⟨ e ∈ˢ n ⟩
                         → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                             ((e ≡ entry x b) × (⟨ b ∈ˢ W ⟩ × ⟨ IsName x ⟩)) ∥₁)
                      → ⟨ IsName n ⟩)
        (w₀-in        : (p : S) → ⟨ p ∈ˢ W₀ ⟩ → ⟨ p ∈ˢ W ⟩)
        where

        chk-name : (a : S) → ⟨ IsName (chk a) ⟩
        chk-name = WFI.induction acc∈ {P = λ a → ⟨ IsName (chk a) ⟩} step
          where
            step : (a : S) → ((y : S) → y ∈ᵗ a → ⟨ IsName (chk y) ⟩)
                 → ⟨ IsName (chk a) ⟩
            step a ih = entries-name (chk a) listing
              where
                listing : (e : S) → ⟨ e ∈ˢ chk a ⟩
                        → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                            ((e ≡ entry x b) × (⟨ b ∈ˢ W ⟩ × ⟨ IsName x ⟩)) ∥₁
                listing e he = PT.rec PT.squash₁
                  (λ { (y , hy , inner) → PT.map
                         (λ { (p , hp , eq) →
                                chk y , p , ≈ˢ→≡ eq , w₀-in p hp , ih y hy })
                         inner })
                  (subst ⟨_⟩ (chk-spec a e) he)

-- Faithfulness. Bell 1.23(iii) says the check map is one to one
-- (fulltext:2358). The proof is a membership induction and the ONLY ground
-- axiom it spends is Extensionality, in the form of ext-path.
--
-- The inhabitedness hypothesis is not decoration. If the weight set were
-- empty then every check name would be the empty code and the map would
-- collapse; the Boolean side discharges it with the top and the poset side
-- with Presentation.inhabited (CodedCompletion.agda:207), which is exactly
-- why section 1.2 chose that inhabitant and kept Infinity out of the ledger.
--
-- Both directions of the extensionality argument use the induction
-- hypothesis, and they use it at different arguments: forward at the member
-- of a that is being tested, backward at the member of c that was produced.
-- Writing only one direction and appealing to symmetry does not work, because
-- the induction is on the first coordinate alone.

      chk-inj : ⟨ ⋁ S (λ p → p ∈ˢ W₀) ⟩ → (a c : S) → chk a ≡ chk c → a ≡ c
      chk-inj inhab =
        WFI.induction acc∈ {P = λ a → (c : S) → chk a ≡ chk c → a ≡ c} step
        where
          step : (a : S) → ((y : S) → y ∈ᵗ a → (c : S) → chk y ≡ chk c → y ≡ c)
               → (c : S) → chk a ≡ chk c → a ≡ c
          step a ih c path = ext-path (λ z → ⇔toPath (to z) (fro z))
            where
              to : (z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ c ⟩
              to z hz = PT.rec (snd (z ∈ˢ c))
                (λ { (p₀ , hp₀) → PT.rec (snd (z ∈ˢ c))
                       (λ { (y , hy , eqn) →
                              subst (λ t → ⟨ t ∈ˢ c ⟩) (sym (ih z hz y eqn)) hy })
                       (entry-out c (chk z) p₀
                         (subst (λ t → ⟨ entry (chk z) p₀ ∈ˢ t ⟩) path
                           (entry-in a z p₀ hz hp₀))) })
                inhab

              fro : (z : S) → ⟨ z ∈ˢ c ⟩ → ⟨ z ∈ˢ a ⟩
              fro z hz = PT.rec (snd (z ∈ˢ a))
                (λ { (p₀ , hp₀) → PT.rec (snd (z ∈ˢ a))
                       (λ { (y , hy , eqn) →
                              subst (λ t → ⟨ t ∈ˢ a ⟩) (ih y hy z (sym eqn)) hy })
                       (entry-out a (chk z) p₀
                         (subst (λ t → ⟨ entry (chk z) p₀ ∈ˢ t ⟩) (sym path)
                           (entry-in c z p₀ hz hp₀))) })
                inhab

--------------------------------------------------------------------------------
-- The standard names
--------------------------------------------------------------------------------

-- The two instantiations and the two diagonal names. B and carrier are the
-- two weight carriers of the package; ⊤ᴮ is the code of the Boolean top, and
-- ⊤ᴮ = carrier holds in K2 (CodedCompletion.agda:511-512) but is NOT assumed
-- here: this module takes ⊤ᴮ as an arbitrary member of B, so the Boolean
-- check name is correct whatever the top turns out to be. below-⊤ is where
-- that identification is used, and it is a hypothesis of module Reverse.
--
-- The two IsName predicates are Track A's kernel at its two instantiations,
-- and entries-nameᴮ and entries-nameᴾ are module Validity applied at each.
-- The coordinator supplies them; nothing here can conflate the two, because
-- the weight carrier is a parameter of each.

    module Standard
      (carrier B ⊤ᴮ       : S)
      (⊤ᴮ∈B               : ⟨ ⊤ᴮ ∈ˢ B ⟩)
      (carrier-inhabited  : ⟨ ⋁ S (λ p → p ∈ˢ carrier) ⟩)
      (IsNameᴮ            : S → Ω)
      (entries-nameᴮ      : (n : S)
                          → ((e : S) → ⟨ e ∈ˢ n ⟩
                             → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                                 ((e ≡ entry x b) × (⟨ b ∈ˢ B ⟩ × ⟨ IsNameᴮ x ⟩)) ∥₁)
                          → ⟨ IsNameᴮ n ⟩)
      (IsNameᴾ            : S → Ω)
      (entries-nameᴾ      : (n : S)
                          → ((e : S) → ⟨ e ∈ˢ n ⟩
                             → ∥ Σ[ x ∈ S ] Σ[ b ∈ S ]
                                 ((e ≡ entry x b) × (⟨ b ∈ˢ carrier ⟩ × ⟨ IsNameᴾ x ⟩)) ∥₁)
                          → ⟨ IsNameᴾ n ⟩)
      where

      module Bs = Over (singleOf ⊤ᴮ)
      module Ps = Over carrier

-- The Boolean check name, Bell 1.22. One entry per member, weighted by the
-- top.

      check : S → S
      check = Bs.chk

-- The poset check name. Its entries range over ALL conditions, and that is
-- visible in the specification rather than asserted in a comment. Track I
-- reads exactly this shape (Valuation.agda:493-502) and its whole reason for
-- needing nothing but the filter's inhabitedness is that a check name's
-- entries are weighted by every condition, so any condition at all in the
-- filter activates every one of them.

      checkᴾ : S → S
      checkᴾ = Ps.chk

-- The Boolean side's weight set is a singleton, so the inner join collapses
-- and the specification takes the shape section 1.10 writes.

      single-collapse : (x e : S)
                      → ⋁ S (λ p → (p ∈ˢ singleOf ⊤ᴮ) ⊓ (e ≈ˢ entry x p))
                      ≡ (e ≈ˢ entry x ⊤ᴮ)
      single-collapse x e = ⇔toPath
        (PT.rec (snd (e ≈ˢ entry x ⊤ᴮ))
          (λ { (p , hp , eq) →
                 subst (λ t → ⟨ e ≈ˢ entry x t ⟩) (singleOf-spec ⊤ᴮ p hp) eq }))
        (λ eq → ∣ ⊤ᴮ , singleOf-member ⊤ᴮ , eq ∣₁)

      check-spec : (a e : S) → (e ∈ˢ check a)
                 ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (e ≈ˢ entry (check y) ⊤ᴮ))
      check-spec a e = Bs.chk-spec a e
        ∙ cong (⋁ S) (funExt (λ y →
            cong (λ Q → (y ∈ˢ a) ⊓ Q) (single-collapse (check y) e)))

      checkᴾ-spec : (a e : S) → (e ∈ˢ checkᴾ a)
                  ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrier)
                         ⊓ (e ≈ˢ entry (checkᴾ y) p)))
      checkᴾ-spec = Ps.chk-spec

      check-host : (a : S) → check a ≡ unionOf (imageOn a (λ y → Bs.spread (check y)))
      check-host = Bs.chk-host

      checkᴾ-host : (a : S) → checkᴾ a ≡ unionOf (imageOn a (λ y → Ps.spread (checkᴾ y)))
      checkᴾ-host = Ps.chk-host

-- The internalization contract, discharged. Track D proved that check's
-- recursion equation and the internal image of its entry-forming map are the
-- SAME statement (NameImage.agda:401-412), so this is not a second obligation:
-- it is check-spec, repackaged. Note what f is. It is NOT check, as section
-- 1.10 writes; the image taken at each stage is of the map that sends a member
-- to its ENTRY, and an InternalImage check would be a different and useless
-- object. Section 3.2 of REPORT-H.md records the correction.

      check-internal : InternalImage (λ y → entry (check y) ⊤ᴮ)
      check-internal = record { img = check ; img-spec = check-spec }

-- The poset side has no such single-function form, because a member
-- contributes a whole layer rather than one entry. Its internalization is the
-- image of the layer map, and the check name is the union of that image.
-- Together with checkᴾ-host this says everything the Boolean statement says.

      checkᴾ-layers : InternalImage (λ y → Ps.spread (checkᴾ y))
      checkᴾ-layers = record
        { img      = λ a → imageOn a (λ y → Ps.spread (checkᴾ y))
        ; img-spec = λ a z → imageOn-spec a (λ y → Ps.spread (checkᴾ y)) z }

-- Validity. The Boolean side needs the top to be a legitimate weight, which
-- is ⊤ᴮ∈B; the poset side needs nothing, because its weight set IS its weight
-- carrier.

      module BsValid = Bs.Valid B IsNameᴮ entries-nameᴮ
        (λ p hp → subst (λ t → ⟨ t ∈ˢ B ⟩) (sym (singleOf-spec ⊤ᴮ p hp)) ⊤ᴮ∈B)

      module PsValid = Ps.Valid carrier IsNameᴾ entries-nameᴾ (λ p hp → hp)

      check-name : (a : S) → ⟨ IsNameᴮ (check a) ⟩
      check-name = BsValid.chk-name

      checkᴾ-name : (a : S) → ⟨ IsNameᴾ (checkᴾ a) ⟩
      checkᴾ-name = PsValid.chk-name

-- Bell 1.23(iii), on both sides. Extensionality and nothing else, as section
-- 1.10 requires; the conclusion is stated in the structure's own equality,
-- which is where the architecture puts it, and the host path is available
-- beside it because ≈ˢ-paths is already in the ledger for entry-inj's sake.

      check-inj : (a b : S) → check a ≡ check b → ⟨ a ≈ˢ b ⟩
      check-inj a b p =
        ≡→≈ˢ (Bs.chk-inj ∣ ⊤ᴮ , singleOf-member ⊤ᴮ ∣₁ a b p)

      checkᴾ-inj : (a b : S) → checkᴾ a ≡ checkᴾ b → ⟨ a ≈ˢ b ⟩
      checkᴾ-inj a b p = ≡→≈ˢ (Ps.chk-inj carrier-inhabited a b p)

--------------------------------------------------------------------------------
-- The generic name, and Bell's U*
--------------------------------------------------------------------------------

-- Γᴾ is the diagonal. Its entries pair the check name of a condition with
-- that same condition as weight, one entry per condition. The point of the
-- diagonal is that an entry is activated exactly when its own weight is in
-- the filter, so the name reads the filter off itself.
--
-- What the value theorem can say at this stage, and what it cannot. Track I
-- proved generic-value (Valuation.agda:633): for any condition p,
--
--     (checkᴾ (fst p) ∈[G] Γᴾ) ≡ (p ∈ᴾ G)
--
-- under the filter's inhabitedness alone. That is a statement about the value
-- RELATION of section 1.11, which is a relation on ground CODES, and it is a
-- pre-generic statement: isGeneric appears in no K3 signature, and host
-- genericity is in fact refutable (no-host-generic, ForcingNotion.agda:315).
--
-- It does NOT say that Γᴾ denotes a set. It does not say the value is a
-- filter, that the value relation is well founded, that a Mostowski collapse
-- exists, or that anything satisfies Foundation. Track I measured the reason
-- and it is sharp: a quotient carrier exists for any G at all, but Bell makes
-- well-foundedness of the quotient membership EQUIVALENT to genericity
-- (fulltext:5109-5115), so a target that behaves like a set does not exist
-- before the generic filter is supplied. Nothing in this file promises one,
-- and no theorem here should be read as an approximation to one.
--
-- Γᴾ and U̇ are two different coded objects and K3 does not claim they agree.
-- U̇ has one entry for every element of B (Bell's U*, fulltext:5166-5167),
-- while Γᴾ has entries only at conditions. The bridge between them is
-- recover (Certificate.agda:420), a statement about Boolean joins, and it
-- needs K4's values. Section 1.10's third decision, unchanged.

      Γᴾ : S
      Γᴾ = imageOn carrier (λ p → entry (checkᴾ p) p)

      Γᴾ-spec : (e : S) → (e ∈ˢ Γᴾ)
              ≡ ⋁ S (λ p → (p ∈ˢ carrier) ⊓ (e ≈ˢ entry (checkᴾ p) p))
      Γᴾ-spec = imageOn-spec carrier (λ p → entry (checkᴾ p) p)

      Γᴾ-name : ⟨ IsNameᴾ Γᴾ ⟩
      Γᴾ-name = entries-nameᴾ Γᴾ (λ e he → PT.map
        (λ { (p , hp , eq) → checkᴾ p , p , ≈ˢ→≡ eq , hp , checkᴾ-name p })
        (subst ⟨_⟩ (Γᴾ-spec e) he))

-- Bell's U*, the Boolean-side analogue: dom(U*) = { b̌ : b ∈ B } and
-- U*(b̌) = b (fulltext:5166-5167). Same diagonal, taken over the Boolean
-- algebra's carrier instead of the conditions. It is included here because it
-- is the same construction and costs three lines; the theorem that makes it
-- interesting, that its value is the ultrafilter, is Bell 4.18 and is K4's.

      U̇ : S
      U̇ = imageOn B (λ b → entry (check b) b)

      U̇-spec : (e : S) → (e ∈ˢ U̇)
             ≡ ⋁ S (λ b → (b ∈ˢ B) ⊓ (e ≈ˢ entry (check b) b))
      U̇-spec = imageOn-spec B (λ b → entry (check b) b)

      U̇-name : ⟨ IsNameᴮ U̇ ⟩
      U̇-name = entries-nameᴮ U̇ (λ e he → PT.map
        (λ { (b , hb , eq) → check b , b , ≈ˢ→≡ eq , hb , check-name b })
        (subst ⟨_⟩ (U̇-spec e) he))

-- The generic name is also the internal image of its own diagonal, which is
-- the form a later track will want when it asks what Γᴾ's domain is.

      Γᴾ-internal : InternalImage (λ p → entry (checkᴾ p) p)
      Γᴾ-internal = record
        { img      = λ c → imageOn c (λ p → entry (checkᴾ p) p)
        ; img-spec = λ c z → imageOn-spec c (λ p → entry (checkᴾ p) p) z }

--------------------------------------------------------------------------------
-- The bridge to the reverse translation
--------------------------------------------------------------------------------

-- Section 1.10 makes checkᴾ = trᴾ ∘ check a DEFINITION. It is delivered here
-- as a THEOREM instead, and the reason is a dependency fact rather than a
-- preference. Track D measured that trᴾ needs an internal image at a function
-- it is itself defining, exactly as check does, and that no tier of the ledger
-- supplies that fixed point (REPORT-D.md, F5 and F8's closing paragraph). If
-- checkᴾ were defined through trᴾ then Track I, which is finished at exit 0
-- and whose module Standard is waiting for checkᴾ and Γᴾ, would be waiting on
-- an unreached fixed point in a second track. Defined directly, checkᴾ needs
-- only what check needs, and the architecture's identity survives in full as
-- the theorem below.
--
-- Two signature corrections are forced and are recorded in section 3 of
-- REPORT-H.md. below is stated over the pair of a code and its membership
-- proof, because El is that Σ-type and this file may not import it; and
-- trᴾ-entries joins over the membership witness at its own type, not over S,
-- which is the same repair Track A made to MemberImage.image-spec.
--
-- The mathematics: an entry of trᴾ (check a) comes from an entry of check a,
-- whose weight is the top, and below the top is the whole carrier, so the
-- entry is spread over exactly the conditions. That is the content of the
-- decision that the reverse translation is the whole cone and never a
-- selection, and it is visible here as the step where below-⊤ is used.

      module Reverse
        (below       : (Σ[ b ∈ S ] ⟨ b ∈ˢ B ⟩) → S)
        (below-⊤     : below (⊤ᴮ , ⊤ᴮ∈B) ≡ carrier)
        (trᴾ         : S → S)
        (trᴾ-entries : (n e : S) → (e ∈ˢ trᴾ n)
                     ≡ ⋁ S (λ x → ⋁ S (λ b → ⋁ ⟨ b ∈ˢ B ⟩ (λ hb → ⋁ S (λ p →
                          (entry x b ∈ˢ n) ⊓ ((p ∈ˢ below (b , hb))
                             ⊓ (e ≈ˢ entry (trᴾ x) p)))))))
        where

        checkᴾ-is-reverse : (a : S) → checkᴾ a ≡ trᴾ (check a)
        checkᴾ-is-reverse =
          WFI.induction acc∈ {P = λ a → checkᴾ a ≡ trᴾ (check a)} step
          where
            step : (a : S) → ((y : S) → y ∈ᵗ a → checkᴾ y ≡ trᴾ (check y))
                 → checkᴾ a ≡ trᴾ (check a)
            step a ih = ext-path (λ e → ⇔toPath (to e) (fro e))
              where
                to : (e : S) → ⟨ e ∈ˢ checkᴾ a ⟩ → ⟨ e ∈ˢ trᴾ (check a) ⟩
                to e he = PT.rec (snd (e ∈ˢ trᴾ (check a)))
                  (λ { (y , hy , inner) → PT.rec (snd (e ∈ˢ trᴾ (check a)))
                    (λ { (p , hp , eq) →
                      subst ⟨_⟩ (sym (trᴾ-entries (check a) e))
                        ∣ check y , ∣ ⊤ᴮ , ∣ ⊤ᴮ∈B , ∣ p
                          , ( subst ⟨_⟩ (sym (check-spec a (entry (check y) ⊤ᴮ)))
                                ∣ y , hy , ≈ˢ-refl (entry (check y) ⊤ᴮ) ∣₁
                            , ( subst (λ t → ⟨ p ∈ˢ t ⟩) (sym below-⊤) hp
                              , subst (λ t → ⟨ e ≈ˢ entry t p ⟩) (ih y hy) eq ) )
                          ∣₁ ∣₁ ∣₁ ∣₁ })
                    inner })
                  (subst ⟨_⟩ (checkᴾ-spec a e) he)

                fro : (e : S) → ⟨ e ∈ˢ trᴾ (check a) ⟩ → ⟨ e ∈ˢ checkᴾ a ⟩
                fro e he = PT.rec (snd (e ∈ˢ checkᴾ a))
                  (λ { (x , rest1) → PT.rec (snd (e ∈ˢ checkᴾ a))
                    (λ { (b , rest2) → PT.rec (snd (e ∈ˢ checkᴾ a))
                      (λ { (hb , rest3) → PT.rec (snd (e ∈ˢ checkᴾ a))
                        (λ { (p , inCheck , inBelow , eq) → PT.rec (snd (e ∈ˢ checkᴾ a))
                          (λ { (y , hy , same) →
                            subst ⟨_⟩ (sym (checkᴾ-spec a e))
                              ∣ y , hy
                              , ∣ p
                                , subst (λ t → ⟨ p ∈ˢ t ⟩)
                                    (cong below (Σ≡Prop (λ t → snd (t ∈ˢ B))
                                                        (snd (entry-inj same)))
                                     ∙ below-⊤)
                                    inBelow
                                , subst (λ t → ⟨ e ≈ˢ entry t p ⟩)
                                    (cong trᴾ (fst (entry-inj same)) ∙ sym (ih y hy))
                                    eq
                                ∣₁ ∣₁ })
                          (PT.map (λ { (y , hy , eqn) → y , hy , ≈ˢ→≡ eqn })
                                  (subst ⟨_⟩ (check-spec a (entry x b)) inCheck)) })
                        rest3 })
                      rest2 })
                    rest1 })
                  (subst ⟨_⟩ (trᴾ-entries (check a) e) he)
