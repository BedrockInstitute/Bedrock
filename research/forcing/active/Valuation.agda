{-# OPTIONS --cubical --safe --guardedness #-}

-- K3 module K3.9 (Track I): the value of a name at a filter.
--
-- WHAT THIS FILE DELIVERS, AND WHAT IT REFUSES TO DELIVER.
--
-- A valuation should send a name and a filter to the object the name denotes
-- in the extension. That object does not exist yet. The poset extension is
-- K6's and the ordinary quotient is K13's, so at K3 there is no target to
-- land in, and inventing one costs a new hypothesis: a `val : Name → X`
-- forces either a smallness assumption on G, because Sub = Cond → Ω lives in
-- Type (ℓ-suc ℓ) (ForcingNotion.agda:88-89) and no set-former takes a large
-- index, or a set quotient, which is exactly K13's object. Neither is a K3
-- hypothesis, so neither is taken here.
--
-- Be precise about which half of that is a theorem and which is a rule, or a
-- later package will look for work that is already done. A CARRIER is
-- available today: the set quotient of the names by the relation below is a
-- legal Type ℓ and an h-set for any G whatever, and the ValueStructure record
-- at the foot of this file would be inhabited by it, its four fields
-- discharged by exactly the lemmas proved here and by nothing else. That
-- inhabitant is withheld by a package rule, not by a missing theorem: K3 may
-- not import Cubical.HITs.SetQuotients, and the quotient belongs to K13,
-- where a second one with no comparison theorem would be a real defect. What
-- is genuinely unavailable before genericity is a target that BEHAVES like a
-- set: Bell makes well-foundedness of the quotient membership equivalent to
-- genericity (fulltext:5109-5115), so there is no collapse, no transitive
-- target, and no ∈-induction on values. A val shipped now would look like a
-- valuation and satisfy none of the laws that make one worth having.
--
-- What CAN be given at this stage is the two-place relation that any such
-- valuation must induce, together with its recursion and its laws. That is
-- what this file ships:
--
--   _≈[G]_ : S → S → Ω     equality of values, by recursion on both codes
--   _∈[G]_ : S → S → Ω     membership between values, DEFINED from _≈[G]_
--
-- and, at the end, the record ValueStructure, which is the interface a later
-- package fills when it does have a carrier. The record is declared and NOT
-- inhabited. Declaring it here rather than in K6 is what lets K5 and K6 be
-- written against a fixed shape while the carrier is still open.
--
-- The relation is an honest weakening, not a placeholder, and it is exactly
-- as strong as Bell's clauses 1.15/1.16 (fulltext:2001-2030) with the Boolean
-- weights replaced by membership in G. Bell himself reaches M[U] only in his
-- chapter 4, by quotient and collapse (fulltext:5063), and makes
-- well-foundedness of the quotient membership EQUIVALENT to genericity
-- (:5109-5115). So even in the source there is no target before genericity,
-- and every theorem below is pre-generic: isGeneric appears in no signature
-- in this file.
--
-- THE PARAMETER LEDGER. Three nested modules, three parameter groups.
--
--  * module Names takes the name kernel's interface (Track A / section 1.3)
--    as flat parameters, and takes SEVEN of them. It does NOT take a name
--    predicate: Child is opaque here, used only as the recursion's edge
--    relation, and the only way this file ever produces an edge is
--    `child-entry` from a weighted entry. There is exactly one IsName in the
--    package and it is not in this file. It takes no ground axiom either:
--    the three ground facts used for the standard names are parameters of
--    module Standard, so the module boundary itself records which half of the
--    file needs the ground and which half does not.
--  * module Poset takes the coded carrier and the order data, and builds
--    K2's ForcingNotion record from them, so that `isFilter` below IS
--    ForcingNotion.agda:175-182 and not a re-spelling of it. Instantiation is
--    one line: those four parameters are the four laws
--    CodedCompletion.Coded.decode supplies (CodedCompletion.agda:236-246).
--    NOTHING in this file consumes the order; it is here only so that the
--    filter record is the real one.
--  * module Value takes the filter G as a bare Sub. It is NOT a filter here.
--    The relation, its unfolding, reflexivity, symmetry, transitivity, both
--    congruences, extensionality and the empty value are all proved for an
--    arbitrary host subset of conditions, with no filter law used anywhere.
--    The filter enters only in module Standard, and there only through
--    `inhabited`, which is made checkable by giving the proofs in a submodule
--    whose single parameter is ⟨ positive G ⟩.
--
-- Why the K2 completion is absent. The architecture's section 1.11 writes the
-- module header as `(𝔓 : Presentation) (laws : Coded.ForcingLaws 𝔓)`. That is
-- not available and not needed. CodedCompletion.agda is not on this compile
-- root's include path, and nothing below reads an order code, a Boolean
-- element or a completion: the value relation quantifies over conditions and
-- over G, and that is all. Taking `carrier` and the order as parameters keeps
-- the ledger accurate and keeps this track independent, as section 2 of the
-- architecture predicted.
--
-- Three mechanical lessons of the shared preamble, as they apply here.
-- (1) Every ⊓/⋀/⋁/⇒ equality below is closed by ⇔toPath with both maps
-- written out, never by a bare refl inside a congruence, so no isProp
-- component is ever left as a metavariable. (2) No description operator is
-- used, so the implicit-class trap cannot arise: this file constructs no set.
-- (3) The single negation in this file, in empty-value, is spelled with the
-- algebra's own ⊥, and its elimination is Empty.rec*, never the library's ¬.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import ForcingNotion as FN

module Valuation {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import Cubical.Foundations.Equiv using ( _≃_ )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Functions.Logic using ( ⇔toPath )
open import Cubical.Induction.WellFounded using ( WellFounded; module WFI )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

-- The conditions of a coded forcing notion, as a host type. This is
-- CodedCompletion.Coded.Cond (CodedCompletion.agda:222-223) and
-- Certificate.Pt carrier (Certificate.agda:104-105), which the architecture's
-- Correction 2 records as the same type; stating it here costs nothing and
-- lets the order parameters of module Poset be written down at all.

Conditions : S → Type ℓ
Conditions c = Σ[ p ∈ S ] ⟨ p ∈ˢ c ⟩

isSetConditions : (c : S) → isSet (Conditions c)
isSetConditions c = isSetΣSndProp isSetS (λ p → snd (p ∈ˢ c))

--------------------------------------------------------------------------------
-- The name kernel's interface
--------------------------------------------------------------------------------

-- Track A owns every one of these; here they are hypotheses. `entry x b` is
-- the Kuratowski pair {{x},{x,b}} weighting the subname x by b, `Child` is the
-- subname relation, and `child-wf` is the accessibility Track A derives from
-- the ground's regularity through the three ∈-steps x ∈ {x} ∈ entry x b ∈ n.
--
-- Note what is NOT asked for, and that this list is the whole of it. No
-- IsName, no Name, no Shape, no support, no weight family, no PowerSet, no
-- Separation, no Union, no Collection, no Infinity, no LEM, and no ground
-- axiom of any kind: not Extensionality, not even the realization of ≈ˢ as a
-- host path. The value relation and every one of its laws is definable from
-- these seven kernel facts and nothing else. The three ground facts K3 does
-- use are parameters of module Standard at the bottom of the file, where the
-- standard names are read: Core's own field ≈ˢ-paths (NameKernel.agda:106),
-- GroundDescription's one-line ext-path (GroundDescription.agda:77), and the
-- kernel's entry-inj (NameKernel.agda:309). No new hypothesis in either
-- place.

module Names
  (entry       : S → S → S)
  (Child       : S → S → Type ℓ)
  (isPropChild : (x n : S) → isProp (Child x n))
  (child-entry : (x b n : S) → ⟨ entry x b ∈ˢ n ⟩ → Child x n)
  (child-wf    : WellFounded Child)
  (∅ᴺ          : S)
  (∅ᴺ-spec     : (z : S) → (z ∈ˢ ∅ᴺ) ≡ ⊥)
  where

-- Recursion on two names at once, with both coordinates descending. This is
-- K0's NameDescent.PairRecursion verbatim (k0-material-names-value-sets:394-405,
-- restored at k0-reference/NameDescent.agda): the outer induction is on the
-- first coordinate at the motive "for every second coordinate", and the inner
-- step discards the second coordinate's edge. The parameter taken is child-wf
-- (NameKernel.agda:380) rather than the recursor itself, for two reasons that
-- are both about accuracy: this file needs the pair recursion at exactly one
-- motive, λ _ _ → Ω, so a level-polymorphic parameter would over-state what
-- is consumed; and child-wf is what Track A's RawPairRec is itself built
-- from, so the two agree by construction and no second recursion principle
-- enters the package.
--
-- The computation law is PROPOSITIONAL. WFI.induction-compute is a path, not
-- a definitional equality, and every use below goes through ≈-unfold rather
-- than expecting the relation to reduce.

  module PairRec {ℓp} (P : S → S → Type ℓp)
    (st : (x y : S) → ((u v : S) → Child u x → Child v y → P u v) → P x y)
    where

    private
      Q : S → Type (ℓ-max ℓ ℓp)
      Q x = (y : S) → P x y

      firstStep : (x : S) → ((u : S) → Child u x → Q u) → Q x
      firstStep x below y = st x y (λ u v left right → below u left v)

    result : (x y : S) → P x y
    result = WFI.induction child-wf {P = Q} firstStep

    computation : (x y : S) → result x y ≡ st x y (λ u v _ _ → result u v)
    computation x y =
      cong (λ f → f y) (WFI.induction-compute child-wf {P = Q} firstStep x)

--------------------------------------------------------------------------------
-- The forcing notion, as the filter's home
--------------------------------------------------------------------------------

-- These four parameters are the four laws CodedCompletion.Coded.decode
-- supplies (CodedCompletion.agda:236-246); `notion` below is that record.
-- The only reason they are here is that isFilter is stated over a
-- ForcingNotion and K3 must use K2's record rather than restate it.

  module Poset (carrier : S)
    (_≼ᴾ_      : Conditions carrier → Conditions carrier → Ω)
    (≼ᴾ-refl   : (p : Conditions carrier) → ⟨ p ≼ᴾ p ⟩)
    (≼ᴾ-trans  : {p q r : Conditions carrier} → ⟨ p ≼ᴾ q ⟩ → ⟨ q ≼ᴾ r ⟩ → ⟨ p ≼ᴾ r ⟩)
    (inhabited : ∥ Conditions carrier ∥₁)
    where

    Cond : Type ℓ
    Cond = Conditions carrier

    notion : FN.ForcingNotion {ℓ}
    notion = record
      { Cond     = Conditions carrier
      ; isSetC   = isSetConditions carrier
      ; _≼_      = _≼ᴾ_
      ; ≼-refl   = ≼ᴾ-refl
      ; ≼-trans  = ≼ᴾ-trans
      ; nonempty = inhabited }

    open FN.Structure notion public using ( Sub; _∈ᴾ_; positive; isFilter )

-- A filter is positive. This is the ONLY filter law any theorem in this file
-- consumes, and naming it here is what makes that claim checkable: every
-- theorem that needs it is proved in module Standard.WithPositivity, whose
-- single parameter is ⟨ positive G ⟩.

    filter-positive : {G : Sub} → isFilter G → ⟨ positive G ⟩
    filter-positive fil = isFilter.inhabited fil

--------------------------------------------------------------------------------
-- The value relation
--------------------------------------------------------------------------------

    module Value (G : Sub) where

-- An entry ⟨x, p⟩ of n is ACTIVE when its weight is a condition in G. Bell's
-- B-valued reading asks for the weight's truth value; the poset reading asks
-- for membership in the filter, and that is the whole of the translation
-- between the two at this level. Active is data, ‖Active‖ its truncation:
-- the untruncated form is not a proposition, since a name may carry the same
-- subname at many weights, and this file states no theorem that the entry
-- presentation is unique. That is the "no functional weight map" rule of
-- section 1.5, met by never forming one.

      Active : S → S → Type ℓ
      Active x n = Σ[ p ∈ S ] Σ[ hp ∈ ⟨ p ∈ˢ carrier ⟩ ]
                     (⟨ entry x p ∈ˢ n ⟩ × ⟨ (p , hp) ∈ᴾ G ⟩)

      ‖Active‖ : S → S → Ω
      ‖Active‖ x n = ∥ Active x n ∥₁ , PT.squash₁

-- An active entry is a Child edge. This is the one bridge between the value
-- layer and the recursion's edge relation, and it runs one way only: Child
-- quantifies its weight over all of S and knows nothing about carrier or G,
-- so a Child edge does not give back an active entry.

      active-child : (x n : S) → ⟨ ‖Active‖ x n ⟩ → Child x n
      active-child x n = PT.rec (isPropChild x n)
        (λ { (p , _ , member , _) → child-entry x p n member })

-- The recursion's step. The two clauses quantify over CHILDREN of the two
-- codes, not over S, because the recursive call is available only where an
-- edge is: ⋀ and ⋁ take an arbitrary small index type, so Σ[ x ∈ S ] Child x n
-- is a legitimate index and no guard has to be smuggled past the recursor.
-- ≈-unfold below turns this back into the S-indexed form the rest of the file
-- and every later package reads, which is possible because an active entry
-- carries its own edge and Child is a proposition.

      Below : S → Type ℓ
      Below n = Σ[ x ∈ S ] Child x n

      stepΩ : (m n : S) → ((u v : S) → Child u m → Child v n → Ω) → Ω
      stepΩ m n rec =
          ⋀ (Below m) (λ u → ‖Active‖ (fst u) m ⇒
              ⋁ (Below n) (λ v → ‖Active‖ (fst v) n
                                 ⊓ rec (fst u) (fst v) (snd u) (snd v)))
        ⊓ ⋀ (Below n) (λ v → ‖Active‖ (fst v) n ⇒
              ⋁ (Below m) (λ u → ‖Active‖ (fst u) m
                                 ⊓ rec (fst u) (fst v) (snd u) (snd v)))

      module ≈Rec = PairRec (λ _ _ → Ω) stepΩ

      infix 20 _≈[G]_ _∈[G]_

      _≈[G]_ : S → S → Ω
      _≈[G]_ = ≈Rec.result

-- Membership is DEFINED from equality and is never mutually recursive with
-- it. K0 fixed this dependency order (k0-material-names-value-sets:34) and the
-- reason is structural: the pair kernel's step demands that BOTH coordinates
-- descend, and a mutual clause would call equality at (m, y) with m not a
-- child of anything.

      _∈[G]_ : S → S → Ω
      m ∈[G] n = ⋁ S (λ y → ‖Active‖ y n ⊓ (m ≈[G] y))

      private
        ≈Body : S → S → Ω
        ≈Body m n =
            ⋀ S (λ x → ‖Active‖ x m ⇒ ⋁ S (λ y → ‖Active‖ y n ⊓ (x ≈[G] y)))
          ⊓ ⋀ S (λ y → ‖Active‖ y n ⇒ ⋁ S (λ x → ‖Active‖ x m ⊓ (x ≈[G] y)))

        toBody : (m n : S) → ⟨ stepΩ m n (λ u v _ _ → u ≈[G] v) ⟩ → ⟨ ≈Body m n ⟩
        toBody m n (c₁ , c₂) =
            (λ x hx → PT.map (λ { ((y , _) , hy , e) → y , hy , e })
                             (c₁ (x , active-child x m hx) hx))
          , (λ y hy → PT.map (λ { ((x , _) , hx , e) → x , hx , e })
                             (c₂ (y , active-child y n hy) hy))

        fromBody : (m n : S) → ⟨ ≈Body m n ⟩ → ⟨ stepΩ m n (λ u v _ _ → u ≈[G] v) ⟩
        fromBody m n (c₁ , c₂) =
            (λ u hu → PT.map (λ { (y , hy , e) → (y , active-child y n hy) , hy , e })
                             (c₁ (fst u) hu))
          , (λ v hv → PT.map (λ { (x , hx , e) → (x , active-child x m hx) , hx , e })
                             (c₂ (fst v) hv))

-- THE UNFOLDING. Two codes have the same value when every active entry of
-- each is matched, in value, by an active entry of the other. This is the
-- statement the rest of K3 and all of K5 read; ≈Rec.computation is never used
-- again after this line.

      ≈-unfold : (m n : S) → (m ≈[G] n)
        ≡ ( ⋀ S (λ x → ‖Active‖ x m ⇒ ⋁ S (λ y → ‖Active‖ y n ⊓ (x ≈[G] y)))
          ⊓ ⋀ S (λ y → ‖Active‖ y n ⇒ ⋁ S (λ x → ‖Active‖ x m ⊓ (x ≈[G] y))) )
      ≈-unfold m n = ≈Rec.computation m n ∙ ⇔toPath (toBody m n) (fromBody m n)

-- The three ways the unfolding is used, named once so that no later proof
-- substitutes along it by hand.

      ≈-fwd : {m n : S} → ⟨ m ≈[G] n ⟩ → (x : S) → ⟨ ‖Active‖ x m ⟩
            → ⟨ ⋁ S (λ y → ‖Active‖ y n ⊓ (x ≈[G] y)) ⟩
      ≈-fwd {m} {n} h = fst (subst ⟨_⟩ (≈-unfold m n) h)

      ≈-bwd : {m n : S} → ⟨ m ≈[G] n ⟩ → (y : S) → ⟨ ‖Active‖ y n ⟩
            → ⟨ ⋁ S (λ x → ‖Active‖ x m ⊓ (x ≈[G] y)) ⟩
      ≈-bwd {m} {n} h = snd (subst ⟨_⟩ (≈-unfold m n) h)

      ≈-intro : {m n : S}
              → ((x : S) → ⟨ ‖Active‖ x m ⟩
                 → ⟨ ⋁ S (λ y → ‖Active‖ y n ⊓ (x ≈[G] y)) ⟩)
              → ((y : S) → ⟨ ‖Active‖ y n ⟩
                 → ⟨ ⋁ S (λ x → ‖Active‖ x m ⊓ (x ≈[G] y)) ⟩)
              → ⟨ m ≈[G] n ⟩
      ≈-intro {m} {n} f g = subst ⟨_⟩ (sym (≈-unfold m n)) (f , g)

-- Reflexivity. Every active entry matches itself, and the value equality it
-- needs is the induction hypothesis at that entry's subname, which is a child.

      ≈-refl : (m : S) → ⟨ m ≈[G] m ⟩
      ≈-refl = WFI.induction child-wf {P = λ m → ⟨ m ≈[G] m ⟩} st
        where
        st : (m : S) → ((x : S) → Child x m → ⟨ x ≈[G] x ⟩) → ⟨ m ≈[G] m ⟩
        st m IH = ≈-intro
          (λ x hx → ∣ x , hx , IH x (active-child x m hx) ∣₁)
          (λ y hy → ∣ y , hy , IH y (active-child y m hy) ∣₁)

-- Symmetry, BEFORE anything that needs the second Bell clause. K0 fixed this
-- order and it is not negotiable: the two clauses of the unfolding are not
-- symmetric as written, since both name the first code's child first, so the
-- second clause only becomes Bell's "every active entry of n is a value-member
-- of m" once symmetry is available. The induction is on the FIRST coordinate
-- alone; the witness produced in either clause is a child of m, and that is
-- where the induction hypothesis applies.

      private
        sym-aux : (m n : S) → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩
        sym-aux = WFI.induction child-wf {P = λ m → (n : S) → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩} st
          where
          st : (m : S) → ((x : S) → Child x m → (n : S) → ⟨ x ≈[G] n ⟩ → ⟨ n ≈[G] x ⟩)
             → (n : S) → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩
          st m IH n h = ≈-intro
            (λ y hy → PT.map (λ { (x , hx , e) → x , hx , IH x (active-child x m hx) y e })
                             (≈-bwd h y hy))
            (λ w hw → PT.map (λ { (y , hy , e) → y , hy , IH w (active-child w m hw) y e })
                             (≈-fwd h w hw))

      ≈-sym : {m n : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] m ⟩
      ≈-sym {m} {n} = sym-aux m n

-- Transitivity, also by first-coordinate induction. Chasing a value through
-- the middle code lands on a child of the first, so one induction suffices;
-- no second recursion and no pair induction is needed here.

      private
        trans-aux : (m n r : S) → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ m ≈[G] r ⟩
        trans-aux = WFI.induction child-wf
          {P = λ m → (n r : S) → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ m ≈[G] r ⟩} st
          where
          st : (m : S)
             → ((x : S) → Child x m → (n r : S) → ⟨ x ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ x ≈[G] r ⟩)
             → (n r : S) → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ m ≈[G] r ⟩
          st m IH n r h k = ≈-intro c₁ c₂
            where
            c₁ : (x : S) → ⟨ ‖Active‖ x m ⟩
               → ⟨ ⋁ S (λ z → ‖Active‖ z r ⊓ (x ≈[G] z)) ⟩
            c₁ x hx = PT.rec PT.squash₁
              (λ { (y , hy , e₁) → PT.map
                     (λ { (z , hz , e₂) → z , hz , IH x (active-child x m hx) y z e₁ e₂ })
                     (≈-fwd k y hy) })
              (≈-fwd h x hx)
            c₂ : (z : S) → ⟨ ‖Active‖ z r ⟩
               → ⟨ ⋁ S (λ x → ‖Active‖ x m ⊓ (x ≈[G] z)) ⟩
            c₂ z hz = PT.rec PT.squash₁
              (λ { (y , hy , e₂) → PT.map
                     (λ { (x , hx , e₁) → x , hx , IH x (active-child x m hx) y z e₁ e₂ })
                     (≈-bwd h y hy) })
              (≈-bwd k z hz)

      ≈-trans : {m n r : S} → ⟨ m ≈[G] n ⟩ → ⟨ n ≈[G] r ⟩ → ⟨ m ≈[G] r ⟩
      ≈-trans {m} {n} {r} = trans-aux m n r

-- THE SECOND BELL CLAUSE. With symmetry in hand the unfolding takes Bell's
-- own shape (fulltext:2013-2030): the value of m equals the value of n when
-- every active entry of either is a value-member of the other. This is the
-- form every downstream argument wants, and it is a theorem here rather than
-- the definition because the definition has to be readable by the pair
-- recursion, where the two coordinates are not interchangeable.

      ≈-unfold-∈ : (m n : S) → (m ≈[G] n)
        ≡ ( ⋀ S (λ x → ‖Active‖ x m ⇒ (x ∈[G] n))
          ⊓ ⋀ S (λ y → ‖Active‖ y n ⇒ (y ∈[G] m)) )
      ≈-unfold-∈ m n = ≈-unfold m n ∙ ⇔toPath
        (λ { (c₁ , c₂) → c₁
           , (λ y hy → PT.map (λ { (x , hx , e) → x , hx , ≈-sym e }) (c₂ y hy)) })
        (λ { (c₁ , c₂) → c₁
           , (λ y hy → PT.map (λ { (x , hx , e) → x , hx , ≈-sym e }) (c₂ y hy)) })

-- An active entry is a value-member, by reflexivity. This is the poset form
-- of Bell's 1.16(i) and the only introduction rule for _∈[G]_ there is.

      active-value : {x n : S} → ⟨ ‖Active‖ x n ⟩ → ⟨ x ∈[G] n ⟩
      active-value {x} hx = ∣ x , hx , ≈-refl x ∣₁

      entry-value : (n x p : S) (hp : ⟨ p ∈ˢ carrier ⟩) → ⟨ (p , hp) ∈ᴾ G ⟩
                  → ⟨ entry x p ∈ˢ n ⟩ → ⟨ x ∈[G] n ⟩
      entry-value n x p hp hG member = active-value ∣ p , hp , member , hG ∣₁

-- Membership respects value equality on both sides. On the left by symmetry
-- and transitivity; on the right by chasing the witness through the first
-- clause of the unfolding.

      ∈-congˡ : {m m' n : S} → ⟨ m ≈[G] m' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m' ∈[G] n ⟩
      ∈-congˡ e = PT.map (λ { (y , hy , d) → y , hy , ≈-trans (≈-sym e) d })

      ∈-congʳ : {m n n' : S} → ⟨ n ≈[G] n' ⟩ → ⟨ m ∈[G] n ⟩ → ⟨ m ∈[G] n' ⟩
      ∈-congʳ e = PT.rec PT.squash₁
        (λ { (y , hy , d) → PT.map
               (λ { (y' , hy' , d') → y' , hy' , ≈-trans d d' })
               (≈-fwd e y hy) })

-- Extensionality FOR VALUES. Two codes whose value-members agree have equal
-- values. This is the direction that matters for K6: it says the relation is
-- already extensional, so the carrier a later package builds by quotienting
-- will satisfy Extensionality without a further condition on names.

      value-extensional : (m n : S) → ((r : S) → (r ∈[G] m) ≡ (r ∈[G] n))
                        → ⟨ m ≈[G] n ⟩
      value-extensional m n agree = subst ⟨_⟩ (sym (≈-unfold-∈ m n))
        ( (λ x hx → subst ⟨_⟩ (agree x) (active-value hx))
        , (λ y hy → subst ⟨_⟩ (sym (agree y)) (active-value hy)) )

-- The empty value. Nothing is active in the empty name, so the second clause
-- is vacuous and the first says exactly that nothing is active in n either.
-- The negation is the algebra's ⊥, as the preamble requires.

      no-active-∅ : (y : S) → ⟨ ‖Active‖ y ∅ᴺ ⟩ → ⟨ ⊥ ⟩
      no-active-∅ y = PT.rec (snd ⊥)
        (λ { (p , _ , member , _) → subst ⟨_⟩ (∅ᴺ-spec (entry y p)) member })

      empty-value : (n : S) → (n ≈[G] ∅ᴺ) ≡ ⋀ S (λ x → ‖Active‖ x n ⇒ ⊥)
      empty-value n = ≈-unfold n ∅ᴺ ∙ ⇔toPath
        (λ { (c₁ , _) → λ x hx → PT.rec (snd ⊥)
               (λ { (y , hy , _) → no-active-∅ y hy }) (c₁ x hx) })
        (λ f → (λ x hx → Empty.rec* (f x hx))
             , (λ y hy → Empty.rec* (no-active-∅ y hy)))

--------------------------------------------------------------------------------
-- The two computations that validate the standard names
--------------------------------------------------------------------------------

-- checkᴾ and Γᴾ belong to Track H (section 1.10); here they are interfaces,
-- exactly as the architecture's section 2 says every non-keystone track
-- consumes its neighbours. The specifications below are section 1.10's
-- checkᴾ-spec and Γᴾ-spec verbatim.
--
-- Note the shape of the P-side check name: its entries range over ALL
-- conditions, because the reverse translation carries the Boolean check
-- name's single ⊤-weighted entry onto the whole cone below ⊤, which is the
-- carrier. That is why a filter's mere inhabitedness already activates every
-- entry of a check name, and it is the reason the two computations below need
-- nothing else from the filter.

      module Standard
        (entry-inj   : {x b y c : S} → entry x b ≡ entry y c → (x ≡ y) × (b ≡ c))
        (≈ˢ-paths    : (x y : S) → (x ≈ˢ y) ≡ ((x ≡ y) , isSetS x y))
        (ext-path    : {a b : S} → ((x : S) → (x ∈ˢ a) ≡ (x ∈ˢ b)) → a ≡ b)
        (checkᴾ      : S → S)
        (checkᴾ-spec : (a e : S) → (e ∈ˢ checkᴾ a)
                     ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ ⋁ S (λ p → (p ∈ˢ carrier)
                            ⊓ (e ≈ˢ entry (checkᴾ y) p))))
        (Γᴾ          : S)
        (Γᴾ-spec     : (e : S) → (e ∈ˢ Γᴾ)
                     ≡ ⋁ S (λ p → (p ∈ˢ carrier) ⊓ (e ≈ˢ entry (checkᴾ p) p)))
        where

-- The structure's equality is host path equality, in both directions. Every
-- decoding step below goes through these, because entry-inj speaks of paths
-- while every membership specification speaks of ≈ˢ. Nothing above this line
-- needs either, which is the ledger fact the module boundary records: the
-- value relation and all of its laws are definable from the name kernel
-- alone, with no ground axiom and no realization of ≈ˢ as a path.

        ≈ˢ→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
        ≈ˢ→≡ {x} {y} = subst ⟨_⟩ (≈ˢ-paths x y)

        ≡→≈ˢ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
        ≡→≈ˢ {x} {y} = subst ⟨_⟩ (sym (≈ˢ-paths x y))

        ≈ˢ-refl : (x : S) → ⟨ x ≈ˢ x ⟩
        ≈ˢ-refl x = ≡→≈ˢ refl

        module WithPositivity (G-pos : ⟨ positive G ⟩) where

-- Reading an active entry of a check name. The entry is a Kuratowski pair, so
-- entry-inj recovers the subname, and the subname is the check name of a
-- member. The weight is discarded: which condition activated the entry is not
-- recoverable and no theorem here asks for it.

          check-active→ : (a z : S) → ⟨ ‖Active‖ z (checkᴾ a) ⟩
                        → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ a ⟩ × (z ≡ checkᴾ y)) ∥₁
          check-active→ a z = PT.rec PT.squash₁
            (λ { (p , _ , member , _) → PT.rec PT.squash₁
                   (λ { (y , hy , rest) → PT.map
                          (λ { (q , _ , eq) → y , hy , fst (entry-inj (≈ˢ→≡ eq)) })
                          rest })
                   (subst ⟨_⟩ (checkᴾ-spec a (entry z p)) member) })

-- And building one. This is where the filter is used, and it is used only
-- here: SOME condition lies in G, and every condition weights every entry of
-- a check name, so every member's check name is active.

          check-active← : (a y : S) → ⟨ y ∈ˢ a ⟩
                        → ⟨ ‖Active‖ (checkᴾ y) (checkᴾ a) ⟩
          check-active← a y hy = PT.map
            (λ { ((p , hp) , hG) → p , hp
               , subst ⟨_⟩ (sym (checkᴾ-spec a (entry (checkᴾ y) p)))
                   ∣ y , hy , ∣ p , hp , ≈ˢ-refl (entry (checkᴾ y) p) ∣₁ ∣₁
               , hG })
            G-pos

          check-value : (a τ : S) → (τ ∈[G] checkᴾ a)
                      ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (τ ≈[G] checkᴾ y))
          check-value a τ = ⇔toPath
            (PT.rec PT.squash₁
              (λ { (z , hz , e) → PT.map
                     (λ { (y , hy , path) → y , hy , subst (λ t → ⟨ τ ≈[G] t ⟩) path e })
                     (check-active→ a z hz) }))
            (PT.map (λ { (y , hy , e) → checkᴾ y , check-active← a y hy , e }))

-- Check names are FAITHFUL: two of them have the same value only if the two
-- ground sets are equal. The induction is on the name code, along Child, and
-- it is the one place in this file where the ground's extensionality is used.
-- Note what it is NOT: this is not injectivity of checkᴾ, which is a path
-- statement Track H proves from Extensionality alone. Here the hypothesis is
-- only that the two check names have the same value at G, which is weaker,
-- and the conclusion is recovered member by member.

          private
            Faithful : S → Type ℓ
            Faithful n = (a c : S) → n ≡ checkᴾ a → ⟨ n ≈[G] checkᴾ c ⟩ → a ≡ c

            faithful-aux : (n : S) → Faithful n
            faithful-aux = WFI.induction child-wf {P = Faithful} st
              where
              st : (n : S) → ((x : S) → Child x n → Faithful x) → Faithful n
              st n IH a c e h = ext-path pointwise
                where
                h' : ⟨ checkᴾ a ≈[G] checkᴾ c ⟩
                h' = subst (λ t → ⟨ t ≈[G] checkᴾ c ⟩) e h

                edgeL : (z : S) → ⟨ z ∈ˢ a ⟩ → Child (checkᴾ z) n
                edgeL z hz = subst (Child (checkᴾ z)) (sym e)
                  (active-child (checkᴾ z) (checkᴾ a) (check-active← a z hz))

                to : (z : S) → ⟨ z ∈ˢ a ⟩ → ⟨ z ∈ˢ c ⟩
                to z hz = PT.rec (snd (z ∈ˢ c))
                  (λ { (y , hy , d) → PT.rec (snd (z ∈ˢ c))
                         (λ { (w , hw , py) → subst (λ t → ⟨ t ∈ˢ c ⟩)
                                (sym (IH (checkᴾ z) (edgeL z hz) z w refl
                                       (subst (λ t → ⟨ checkᴾ z ≈[G] t ⟩) py d)))
                                hw })
                         (check-active→ c y hy) })
                  (≈-fwd h' (checkᴾ z) (check-active← a z hz))

                from : (z : S) → ⟨ z ∈ˢ c ⟩ → ⟨ z ∈ˢ a ⟩
                from z hz = PT.rec (snd (z ∈ˢ a))
                  (λ { (x , hx , d) → PT.rec (snd (z ∈ˢ a))
                         (λ { (u , hu , px) → subst (λ t → ⟨ t ∈ˢ a ⟩)
                                (IH (checkᴾ u) (edgeL u hu) u z refl
                                  (subst (λ t → ⟨ t ≈[G] checkᴾ z ⟩) px d))
                                hu })
                         (check-active→ a x hx) })
                  (≈-bwd h' (checkᴾ z) (check-active← c z hz))

                pointwise : (z : S) → (z ∈ˢ a) ≡ (z ∈ˢ c)
                pointwise z = ⇔toPath (to z) (from z)

          check-≈-inj : (a c : S) → ⟨ checkᴾ a ≈[G] checkᴾ c ⟩ → ⟨ a ≈ˢ c ⟩
          check-≈-inj a c h = ≡→≈ˢ (faithful-aux (checkᴾ a) a c refl h)

          check-faithful : (a b : S) → (checkᴾ a ∈[G] checkᴾ b) ≡ (a ∈ˢ b)
          check-faithful a b = ⇔toPath
            (λ h → PT.rec (snd (a ∈ˢ b))
              (λ { (y , hy , d) → subst (λ t → ⟨ t ∈ˢ b ⟩)
                     (sym (≈ˢ→≡ (check-≈-inj a y d))) hy })
              (subst ⟨_⟩ (check-value b (checkᴾ a)) h))
            (λ hab → subst ⟨_⟩ (sym (check-value b (checkᴾ a)))
                       ∣ a , hab , ≈-refl (checkᴾ a) ∣₁)

-- The generic name's value is the filter itself. Reading an active entry of Γᴾ
-- gives back a condition IN G, because Γᴾ weights the check name of p by p
-- alone, and the weight is what the filter is tested on.

          Γ-active→ : (z : S) → ⟨ ‖Active‖ z Γᴾ ⟩
                    → ∥ Σ[ r ∈ Cond ] ((z ≡ checkᴾ (fst r)) × ⟨ r ∈ᴾ G ⟩) ∥₁
          Γ-active→ z = PT.rec PT.squash₁
            (λ { (q , hq , member , hG) → PT.map
                   (λ { (r , _ , eq) →
                          let dec = entry-inj (≈ˢ→≡ eq)
                          in (q , hq) , (fst dec ∙ cong checkᴾ (sym (snd dec))) , hG })
                   (subst ⟨_⟩ (Γᴾ-spec (entry z q)) member) })

          generic-value : (p : Cond) → (checkᴾ (fst p) ∈[G] Γᴾ) ≡ (p ∈ᴾ G)
          generic-value p = ⇔toPath
            (PT.rec (snd (p ∈ᴾ G))
              (λ { (z , hz , d) → PT.rec (snd (p ∈ᴾ G))
                     (λ { (r , pz , hG) → subst (λ t → ⟨ t ∈ᴾ G ⟩)
                            (sym (Σ≡Prop (λ x → snd (x ∈ˢ carrier))
                                   (≈ˢ→≡ (check-≈-inj (fst p) (fst r)
                                     (subst (λ t → ⟨ checkᴾ (fst p) ≈[G] t ⟩) pz d)))))
                            hG })
                     (Γ-active→ z hz) }))
            (λ hG → active-value ∣ fst p , snd p
                    , subst ⟨_⟩ (sym (Γᴾ-spec (entry (checkᴾ (fst p)) (fst p))))
                        ∣ fst p , snd p , ≈ˢ-refl (entry (checkᴾ (fst p)) (fst p)) ∣₁
                    , hG ∣₁)

-- The architecture's signatures, with isFilter where the proofs above take
-- only positivity. Nothing is reproved; the filter is projected and discarded.

        check-value : isFilter G → (a τ : S) → (τ ∈[G] checkᴾ a)
                    ≡ ⋁ S (λ y → (y ∈ˢ a) ⊓ (τ ≈[G] checkᴾ y))
        check-value fil = WithPositivity.check-value (filter-positive fil)

        check-faithful : isFilter G → (a b : S)
                       → (checkᴾ a ∈[G] checkᴾ b) ≡ (a ∈ˢ b)
        check-faithful fil = WithPositivity.check-faithful (filter-positive fil)

        generic-value : isFilter G → (p : Cond)
                      → (checkᴾ (fst p) ∈[G] Γᴾ) ≡ (p ∈ᴾ G)
        generic-value fil = WithPositivity.generic-value (filter-positive fil)

--------------------------------------------------------------------------------
-- The target K3 does not fix
--------------------------------------------------------------------------------

-- A later package that HAS a carrier fills this record. Name is abstract here
-- rather than Σ[ n ∈ S ] ⟨ IsName n ⟩ for one reason: the package must contain
-- exactly one IsName, and it is Track A's. At the instantiation Name is that
-- Σ-type and `code` is fst, so val-eq and val-mem read exactly as section 1.11
-- writes them.
--
-- Read the fields as a specification of what a valuation MUST satisfy, not as
-- a definition of one. val-onto says the carrier has no elements beyond the
-- values of names; val-eq says the carrier's equality is the value relation
-- and nothing finer; val-mem says its membership is the value membership. Any
-- two fillers are therefore isomorphic over the relation, which is why this
-- record is safe to write down before the carrier exists. Inhabiting it is
-- exactly the work K6 and K13 own, and no inhabitant appears in K3.

      module Target (Name : Type ℓ) (code : Name → S) where

        record ValueStructure : Type (ℓ-suc ℓ) where
          field
            Carrier  : Type ℓ
            isSetC   : isSet Carrier
            val      : Name → Carrier
            val-onto : (c : Carrier) → ∥ Σ[ τ ∈ Name ] (val τ ≡ c) ∥₁
            val-eq   : (τ σ : Name) → (val τ ≡ val σ) ≃ ⟨ code τ ≈[G] code σ ⟩
            mem      : Carrier → Carrier → Ω
            val-mem  : (τ σ : Name) → mem (val τ) (val σ) ≡ (code τ ∈[G] code σ)

-- DELIBERATELY ABSENT FROM THIS FILE, and from all of K3. The absence of each
-- is checkable by grep and is part of the deliverable.
--
--   val : Name → X               for any concrete X. There is no X yet.
--   any inhabitant of ValueStructure.
--   ≈-mono : ⟨ G ⊆ᴾ G' ⟩ → …     the relation is NOT monotone in G, in either
--                                direction: enlarging G activates entries on
--                                both sides of _≈[G]_, so it can both create
--                                and destroy a match, and no inclusion between
--                                the relations survives.
--   valᵁ : Nameᴮ → …             the Boolean-valued valuation is K4's; it needs
--                                Boolean values of formulas, which K3 does not
--                                have.
--   an internal graph for the valuation: no Formula, no Δ₀ certificate, no
--                                Separation instance appears anywhere in this
--                                file. The value relation is a host relation
--                                on codes and is not claimed to be definable.
--   isGeneric: every theorem here is pre-generic. Host genericity is
--                                refutable (ForcingNotion.agda:315) and
--                                genericity first becomes necessary at K5's
--                                truth lemma.
--   any round trip between a name and its value, in either order: K4 and K5
--                                own those.
