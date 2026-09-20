{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track C: the coded dense sets, and the generic correspondence they make
-- work.
--
-- WHAT THIS MODULE DEFENDS. Ledger clause L4: the only genericity notion in
-- K5 is K2's `meets` field, quantified over a CODE d : S with
-- ⟨ d ⊆ˢ carrier ⟩ and ⟨ denseΔ carrier order d ⟩, and never over a host
-- subset of conditions, an antichain, a maximal antichain or a predense set.
-- Every set built below is one Separation over the carrier against a Δ₀
-- formula with ground constants, so each of them IS such a code, and the
-- density statements are stated at exactly the shape K2's field consumes. The
-- name MeetsAll at the end of this file is that obligation as a TYPE, and it
-- elaborates at Type ℓ precisely because its dense sets are codes; the
-- deliberate break in the report replaces the code by a host subset and the
-- annotation fails. That level move is the type-level tell K2 records at
-- CodedCompletion.agda:989-994.
--
-- FOUR SETS, NOT THREE. Architecture section 1.6 lists decideAt, coneOrApart
-- and witnessAt, and says generic-meets-denseBelow is built from coneOrApart.
-- It is not, and cannot be: coneOrApart p yields a member of the filter
-- refining p, after which the dense-below set d is still only dense below p
-- and the member of d it produces need not lie in the filter. The set that
-- works is memOrApart d r, "in d, or incompatible with r", which is Bell's own
-- union and which mentions d itself. Measured correction, section 4 of
-- REPORT-C. coneOrApart is still built here, unchanged, because Track D's
-- generic-reflect consumes it.
--
-- HOW TRACK A ENTERS. Track A owns the record ForcingBase, the sealed _⊩ᴮ_
-- with its six direct poset lemmas and ⊩ᴮ-extend, and the top-level
-- denseBelowΔ. This file imports K5.Frame and declares none of them again;
-- that is preamble rule 9 and Track A's own instruction 3.
--
-- CLASSICAL LEDGER. LEM ℓ is an explicit first argument of exactly four
-- declarations: decideAt-dense, coneOrApart-dense, memOrApart-dense and
-- witnessAt-denseBelow, together with the two theorems that call them,
-- generic-meets-denseBelow and witnessAt-denseBelow-sup. Nothing else in the
-- file names LEM. Every use is at one of two proposition shapes, `x ≡ ⊥ᴮ` for
-- x : Pt B and compatᶜ p q, and there is no host choice of any kind, no
-- elimination of a truncated sigma into data, and no appeal to an antichain or
-- to separativity.
--
-- THE ONE HYPOTHESIS THAT IS NOT TRACK A'S. witnessAt is a Separation over a
-- coded VALUE SET V whose members are the CODES of algebra elements, so its
-- reading speaks x ∈ˢ u for u ∈ˢ V, while forcing speaks the frame's abstract
-- belowᶜ. At the coded completion the two coincide, because decision D1 sets
-- below := fst and K5/ProbeD1.agda verifies it at exit 0. At the ABSTRACT
-- frame they do not, so the two entailments are named here as CodeOfBelow and
-- BelowOfCode and appear in the type of every witnessAt lemma that needs them.
-- decideAt, coneOrApart, memOrApart and generic-meets-denseBelow need neither.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import GroundDescription
import CodedVocabulary
import ForcingNotion as FN
import K4.Algebra
import K4.Implication
import K5.Frame

module K5.Dense
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (sep   : OrdinaryProfile.Separation 𝒮)
  (carrier order : ZFStructure.S 𝒮)
  (B : ZFStructure.S 𝒮)
  (L  : K4.Algebra.Lattice 𝒮 B)
  (Cm : K4.Algebra.Complement 𝒮 B L)
  (Kc : K4.Algebra.CodedComplete 𝒮 B L)
  (fb : K5.Frame.Poset.ForcingBase 𝒮 carrier order B L Cm)
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; con; var; Formula; _∈̇_; _∨̇_; _⇒̇_; ¬̇_; ⊥̇; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮
open At S id using ( _⊨_ )

module OP = OrdinaryProfile 𝒮
module CV = CodedVocabulary 𝒮
module GD = GroundDescription 𝒮 ext paths

open CV
  using ( refinesΔ; compatibleΔ; denseΔ
        ; orderAtˢ; compatAtˢ; sepAt; sepAt-reading )
open GD using ( separateOf; separateOf-spec )

-- The scope contract of K4/Implication.agda:64-77 verbatim: the record TYPE
-- names come from K4.Algebra and never from a module that re-exports them.

open K4.Algebra 𝒮
  using ( Pt; isSetPt; Pt≡; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans
        ; Lattice; Complement; CodedComplete )

open K4.Implication 𝒮 ext paths B L Cm
open CodedComplete Kc using ( supᴮ; sup-lub )

-- Track A's export surface. Ledger clause L9 forbids the local names `i` and
-- `below`, so the two record fields are renamed on the way in; every other
-- field keeps the name Track A gave it.

open K5.Frame 𝒮 using ( denseBelowΔ ; module Poset )
open Poset carrier order
open ForcingBase fb renaming ( i to iᶜ ; below to belowᶜ )
open Forcing ext paths B L Cm Kc fb

--------------------------------------------------------------------------------
-- The forcing notion of the frame, and the filter vocabulary
--------------------------------------------------------------------------------

-- K1's ForcingNotion is a record, so building one is producing an INHABITANT
-- and not declaring a second copy; preamble rule 9 is not in play. Track C
-- needs one for the isFilter hypothesis of generic-meets-denseBelow. Track D
-- independently builds frameNotion (K5/Generic.agda:120-134) field for field
-- the same way, and K5/ProbeC.agda checks by refl that the two are the SAME
-- inhabitant, so no consumer can be caught between them; which of the two the
-- package keeps is a coordinator's choice and not a correctness question.
--
-- Three fields and nothing else: the frame's own preorder, read off the coded
-- order graph, and its inhabitedness. This is K2's decode
-- (CodedCompletion.agda:243-256) at an abstract frame instead of at a
-- Presentation.

notionᶜ : FN.ForcingNotion {ℓ}
notionᶜ = record
  { Cond     = Cond
  ; isSetC   = isSetΣSndProp isSetS (λ x → snd (x ∈ˢ carrier))
  ; _≼_      = λ p q → fst p ≼ᶜ fst q
  ; ≼-refl   = λ p → ForcingBase.≼-refl fb (fst p) (snd p)
  ; ≼-trans  = λ {p} {q} {r} h k →
                 ForcingBase.≼-trans fb (fst p) (fst q) (fst r)
                   (snd p) (snd q) (snd r) h k
  ; nonempty = PT.map (λ { (p , hp) → p , hp }) inhabited }

module FS = FN.Structure notionᶜ
open FS using ( Sub; _∈ᴾ_; isFilter; compatible; filter-compatible )

-- K1 states compatibility over the decoded conditions and Track E states it
-- over the two codes. The map from the first to the second is free and is
-- K2's compat-transfer← (CodedCompletion.agda:1027) at an abstract frame.

compatᶜ-of-host : (p q : Cond) → ⟨ compatible p q ⟩ → ⟨ compatᶜ p q ⟩
compatᶜ-of-host p q =
  PT.map (λ { (r , h₁ , h₂) → fst r , (snd r , (h₁ , h₂)) })

--------------------------------------------------------------------------------
-- The decision set
--------------------------------------------------------------------------------

-- "the conditions that decide b": those lying in the coded extension of b or
-- in the coded extension of its complement. The formula is a disjunction of
-- two atoms with ground constants, so it is Δ₀ by the Boolean traversal and
-- the Separation reads it.
--
-- SIGNATURE CORRECTION, and it is what makes this set unconditional at the
-- abstract frame. Architecture section 1.6 writes the two constants as
-- `fst b` and `fst (¬ᴮ b)`, the elements' own codes. That is decision D1
-- read at the coded completion; at an abstract ForcingBase the code of an
-- element carries no relation to forcing, and the operator that does is the
-- frame's belowᶜ, with below-in and below-out as its two entailments. The two
-- agree at the instance and the set is the same set there.

decideφ : Pt B → Formula S 1
decideφ b = (var zero ∈̇ con (belowᶜ b)) ∨̇ (var zero ∈̇ con (belowᶜ (¬ᴮ b)))

Δ₀-decideφ : (b : Pt B) → Δ₀ (decideφ b)
Δ₀-decideφ b = checkΔ₀ (decideφ b) tt

-- THE SEAL, and it is preamble rule 2 in the exact shape the rule prescribes.
-- separateOf is a DESCRIPTION-OPERATOR term (GroundDescription.agda:130-131,
-- `the` over ℩), and K2 contains no seal at all, so an unsealed coded set is
-- exactly what the rule was written about. MEASURED HERE, NOT ASSUMED, under
-- the one option set of ledger clause L11:
--
--   this file with the four sets unsealed   no finish in 11 min, 2.2 GB
--   the same file, this one seal removed    no finish in 300 s
--   truncated at decideAt-intro, unsealed   exit 0, seconds
--   this file as it stands                  exit 0, 1.70 s, 386 MB
--
-- so the threshold is one declaration, decideAt-dense, and it is the first
-- declaration whose PROOF puts the separated set under a ⋁ and then converts
-- against it. Everything before it only transports along the Separation
-- specification and costs nothing unsealed.
--
-- The reading travels in the same opaque block, on Track A's model at
-- K5/Frame.agda:251-256, so every consumer below has the membership
-- specification as a PATH and never as an unfolding of the seal. Each of the
-- four sets gets its OWN block: that is rule 2b, and separate blocks are load
-- bearing.

opaque
  decideAt : Pt B → S
  decideAt b = separateOf sep carrier (decideφ b)

  -- The reading is the Separation specification and nothing more: the
  -- formula's own value is already the host disjunction, by refl.

  decideAt-mem : (b : Pt B) (x : S)
               → (x ∈ˢ decideAt b)
                 ≡ ((x ∈ˢ carrier)
                    ⊓ ((x ∈ˢ belowᶜ b) ⊔ (x ∈ˢ belowᶜ (¬ᴮ b))))
  decideAt-mem b x = separateOf-spec sep carrier (decideφ b) x

decideAt-sub : (b : Pt B) → ⟨ decideAt b ⊆ˢ carrier ⟩
decideAt-sub b x h = subst ⟨_⟩ (decideAt-mem b x) h .fst

-- The reading in poset vocabulary, which is the form every consumer wants and
-- the form ledger clause L6 demands. Both directions are free, because
-- Track A's ⊩ᴮ-mem and ⊩ᴮ-from are.

decideAt-spec : (b : Pt B) (q : Cond) → ⟨ fst q ∈ˢ decideAt b ⟩
              → ⟨ (q ⊩ᴮ b) ⊔ (q ⊩ᴮ (¬ᴮ b)) ⟩
decideAt-spec b q h =
  PT.map (λ { (inl hb) → inl (⊩ᴮ-from q b hb)
            ; (inr hn) → inr (⊩ᴮ-from q (¬ᴮ b) hn) })
         (subst ⟨_⟩ (decideAt-mem b (fst q)) h .snd)

decideAt-intro : (b : Pt B) (q : Cond) → ⟨ (q ⊩ᴮ b) ⊔ (q ⊩ᴮ (¬ᴮ b)) ⟩
               → ⟨ fst q ∈ˢ decideAt b ⟩
decideAt-intro b q h =
  subst ⟨_⟩ (sym (decideAt-mem b (fst q)))
    ( snd q
    , PT.map (λ { (inl hb) → inl (⊩ᴮ-mem q b hb)
                ; (inr hn) → inr (⊩ᴮ-mem q (¬ᴮ b) hn) }) h )

-- Density, and it costs exactly one excluded middle, at the proposition
-- `i q ⊓ᴮ b ≡ ⊥ᴮ`. If the meet is nonzero, Track A's ⊩ᴮ-extend hands back a
-- refinement of q forcing b, and that refinement lies in the left disjunct.
-- If the meet is zero then q itself already forces the complement, by
-- ⊓⊥→≤¬ (K4/Implication.agda:193), and q lies in the right disjunct. Note
-- which way the classical step runs: the excluded middle is spent on the
-- VALUE fact and never on the order, so no order reflection is involved.

decideAt-dense : LEM ℓ → (b : Pt B) → ⟨ denseΔ carrier order (decideAt b) ⟩
decideAt-dense lem b q hq = decide (lem meetΩ)
  where
    qc : Cond
    qc = q , hq

    goal : Ω
    goal = ⋁ S (λ p → (p ∈ˢ decideAt b) ⊓ refinesΔ order p q)

    meetΩ : Ω
    meetΩ = ((iᶜ qc ⊓ᴮ b) ≡ ⊥ᴮ) , isSetPt B (iᶜ qc ⊓ᴮ b) ⊥ᴮ

    fromBelow : Σ[ r ∈ Cond ] ⟨ (fst r ≼ᶜ fst qc) ⊓ (r ⊩ᴮ b) ⟩ → ⟨ goal ⟩
    fromBelow (r , hrq , hrb) =
      ∣ fst r , (decideAt-intro b r ∣ inl hrb ∣₁ , hrq) ∣₁

    decide : ⟨ meetΩ ⟩ ⊎ (⟨ meetΩ ⟩ → Empty.⊥) → ⟨ goal ⟩
    decide (inl e) =
      ∣ q , ( decideAt-intro b qc
                ∣ inr (⊩ᴮ-intro qc (¬ᴮ b) (⊓⊥→≤¬ (iᶜ qc) b e)) ∣₁
            , ForcingBase.≼-refl fb q hq ) ∣₁
    decide (inr nz) =
      PT.rec (snd goal) fromBelow (⊩ᴮ-extend qc b (λ e → Empty.rec (nz e)))

-- The degenerate audit of exit item X3, proved rather than asserted. At the
-- bottom the decision set is the whole carrier: nothing forces ⊥ᴮ, but
-- everything forces its complement, because i p ⊓ᴮ ⊥ᴮ is ⊥ᴮ outright. So this
-- one instance of the density is FREE, and the LEM ℓ of decideAt-dense is
-- spent on the general b and not on the shape of the statement.

decideAt-⊥-total : (p : Cond) → ⟨ fst p ∈ˢ decideAt ⊥ᴮ ⟩
decideAt-⊥-total p =
  decideAt-intro ⊥ᴮ p
    ∣ inr (⊩ᴮ-intro p (¬ᴮ ⊥ᴮ) (⊓⊥→≤¬ (iᶜ p) ⊥ᴮ (⊓-⊥ (iᶜ p)))) ∣₁

decideAt-⊥-dense : ⟨ denseΔ carrier order (decideAt ⊥ᴮ) ⟩
decideAt-⊥-dense q hq =
  ∣ q , (decideAt-⊥-total (q , hq) , ForcingBase.≼-refl fb q hq) ∣₁

--------------------------------------------------------------------------------
-- The cone-or-apart set
--------------------------------------------------------------------------------

-- "the conditions that refine p or are incompatible with p". Track D's
-- generic-reflect meets this one set and nothing else, which is the whole
-- reason the reverse of the generic correspondence needs no maximal antichain.
--
-- Every slot of the two vocabulary formulas is a variable, so the formula is
-- assembled variable-indexed and instantiated at the three ground constants by
-- CodedVocabulary's sepAt, exactly as K2 assembles coneφ
-- (CodedCompletion.agda:555-560). Slot zero is the separated variable, slot
-- one the carrier, slot two the order and slot three the condition's code.

coneOrApartψ : Formula S 4
coneOrApartψ =
      orderAtˢ (suc (suc zero)) zero (suc (suc (suc zero)))
  ∨̇ ¬̇ (compatAtˢ (suc zero) (suc (suc zero)) zero (suc (suc (suc zero))))

coneOrApartφ : S → Formula S 1
coneOrApartφ p = sepAt coneOrApartψ (carrier ∷ order ∷ p ∷ [])

Δ₀-coneOrApartφ : (p : S) → Δ₀ (coneOrApartφ p)
Δ₀-coneOrApartφ p = checkΔ₀ (coneOrApartφ p) tt

opaque
  coneOrApart : Cond → S
  coneOrApart p = separateOf sep carrier (coneOrApartφ (fst p))

  coneOrApart-mem : (p : Cond) (x : S)
                  → (x ∈ˢ coneOrApart p)
                    ≡ ((x ∈ˢ carrier)
                       ⊓ ((x ≼ᶜ fst p)
                          ⊔ (compatibleΔ carrier order x (fst p) ⇒ ⊥)))
  coneOrApart-mem p x =
      separateOf-spec sep carrier (coneOrApartφ (fst p)) x
    ∙ cong (λ w → (x ∈ˢ carrier) ⊓ w)
        (sepAt-reading coneOrApartψ (carrier ∷ order ∷ fst p ∷ []) x)

coneOrApart-sub : (p : Cond) → ⟨ coneOrApart p ⊆ˢ carrier ⟩
coneOrApart-sub p x h = subst ⟨_⟩ (coneOrApart-mem p x) h .fst

coneOrApart-cone : (p r : Cond) → ⟨ fst r ≼ᶜ fst p ⟩
                 → ⟨ fst r ∈ˢ coneOrApart p ⟩
coneOrApart-cone p r h =
  subst ⟨_⟩ (sym (coneOrApart-mem p (fst r))) (snd r , ∣ inl h ∣₁)

coneOrApart-apart : (p r : Cond) → (⟨ compatᶜ r p ⟩ → ⟨ ⊥ ⟩)
                  → ⟨ fst r ∈ˢ coneOrApart p ⟩
coneOrApart-apart p r h =
  subst ⟨_⟩ (sym (coneOrApart-mem p (fst r))) (snd r , ∣ inr h ∣₁)

-- The reading back out, which is what Track D consumes: a member of the set is
-- either a refinement of p or apart from p, and nothing else.

coneOrApart-spec : (p r : Cond) → ⟨ fst r ∈ˢ coneOrApart p ⟩
                 → ⟨ (fst r ≼ᶜ fst p) ⊔ (compatᶜ r p ⇒ ⊥) ⟩
coneOrApart-spec p r h = subst ⟨_⟩ (coneOrApart-mem p (fst r)) h .snd

-- Density, one excluded middle, at compatibility this time and not at a value.
-- If q is compatible with p a common refinement lies in the cone half; if it
-- is not, q itself lies in the apart half. Nothing here mentions the algebra
-- at all, which is why this set is the cheapest of the four.

coneOrApart-dense : LEM ℓ → (p : Cond)
                  → ⟨ denseΔ carrier order (coneOrApart p) ⟩
coneOrApart-dense lem p q hq = decide (lem (compatᶜ (q , hq) p))
  where
    goal : Ω
    goal = ⋁ S (λ r → (r ∈ˢ coneOrApart p) ⊓ refinesΔ order r q)

    fromCommon : Σ[ r ∈ S ]
                   ⟨ (r ∈ˢ carrier)
                     ⊓ (refinesΔ order r q ⊓ refinesΔ order r (fst p)) ⟩
               → ⟨ goal ⟩
    fromCommon (r , hrc , hrq , hrp) =
      ∣ r , (coneOrApart-cone p (r , hrc) hrp , hrq) ∣₁

    decide : ⟨ compatᶜ (q , hq) p ⟩ ⊎ (⟨ compatᶜ (q , hq) p ⟩ → Empty.⊥)
           → ⟨ goal ⟩
    decide (inl c)  = PT.rec (snd goal) fromCommon c
    decide (inr nc) =
      ∣ q , ( coneOrApart-apart p (q , hq) (λ h → Empty.rec (nc h))
            , ForcingBase.≼-refl fb q hq ) ∣₁

--------------------------------------------------------------------------------
-- The mem-or-apart set, and dense below
--------------------------------------------------------------------------------

-- "in d, or incompatible with r". This is the fourth coded set, the one
-- architecture section 1.6 does not list, and the whole of Bell Problem
-- 4.34(i) is its density plus one appeal to filter-compatible.
--
-- Why coneOrApart cannot stand in for it. Meeting coneOrApart r at a filter
-- containing r yields a member of the filter refining r; d is then dense below
-- that member, but the member of d it produces is only a condition of the
-- carrier and there is nothing to put it back inside the filter. The left
-- disjunct has to BE d, and the whole point of the construction is that the
-- enlargement is dense outright while its excess is disjoint from the filter.

memOrApartψ : S → Formula S 4
memOrApartψ d =
      (var zero ∈̇ con d)
  ∨̇ ¬̇ (compatAtˢ (suc zero) (suc (suc zero)) zero (suc (suc (suc zero))))

memOrApartφ : S → S → Formula S 1
memOrApartφ d p = sepAt (memOrApartψ d) (carrier ∷ order ∷ p ∷ [])

Δ₀-memOrApartφ : (d p : S) → Δ₀ (memOrApartφ d p)
Δ₀-memOrApartφ d p = checkΔ₀ (memOrApartφ d p) tt

opaque
  memOrApart : S → Cond → S
  memOrApart d p = separateOf sep carrier (memOrApartφ d (fst p))

  memOrApart-mem : (d : S) (p : Cond) (x : S)
                 → (x ∈ˢ memOrApart d p)
                   ≡ ((x ∈ˢ carrier)
                      ⊓ ((x ∈ˢ d)
                         ⊔ (compatibleΔ carrier order x (fst p) ⇒ ⊥)))
  memOrApart-mem d p x =
      separateOf-spec sep carrier (memOrApartφ d (fst p)) x
    ∙ cong (λ w → (x ∈ˢ carrier) ⊓ w)
        (sepAt-reading (memOrApartψ d) (carrier ∷ order ∷ fst p ∷ []) x)

memOrApart-sub : (d : S) (p : Cond) → ⟨ memOrApart d p ⊆ˢ carrier ⟩
memOrApart-sub d p x h = subst ⟨_⟩ (memOrApart-mem d p x) h .fst

memOrApart-left : (d : S) (p : Cond) (x : S) → ⟨ x ∈ˢ carrier ⟩
                → ⟨ x ∈ˢ d ⟩ → ⟨ x ∈ˢ memOrApart d p ⟩
memOrApart-left d p x hc h =
  subst ⟨_⟩ (sym (memOrApart-mem d p x)) (hc , ∣ inl h ∣₁)

memOrApart-right : (d : S) (p : Cond) (x : S) → ⟨ x ∈ˢ carrier ⟩
                 → (⟨ compatibleΔ carrier order x (fst p) ⟩ → ⟨ ⊥ ⟩)
                 → ⟨ x ∈ˢ memOrApart d p ⟩
memOrApart-right d p x hc h =
  subst ⟨_⟩ (sym (memOrApart-mem d p x)) (hc , ∣ inr h ∣₁)

-- The enlargement of a set dense BELOW r is dense OUTRIGHT. One excluded
-- middle, at compatibility with r. Below a condition compatible with r the
-- density hypothesis fires at a common refinement; below a condition apart
-- from r the enlargement already contains that condition.

memOrApart-dense : LEM ℓ → (d : S) → ⟨ d ⊆ˢ carrier ⟩ → (r : Cond)
                 → ⟨ denseBelowΔ carrier order (fst r) d ⟩
                 → ⟨ denseΔ carrier order (memOrApart d r) ⟩
memOrApart-dense lem d sub r db q hq = decide (lem (compatᶜ (q , hq) r))
  where
    goal : Ω
    goal = ⋁ S (λ p → (p ∈ˢ memOrApart d r) ⊓ refinesΔ order p q)

    below-s : (s : S) → ⟨ s ∈ˢ carrier ⟩ → ⟨ refinesΔ order s q ⟩
            → Σ[ t ∈ S ] ⟨ (t ∈ˢ d) ⊓ refinesΔ order t s ⟩
            → Σ[ t ∈ S ] ⟨ (t ∈ˢ memOrApart d r) ⊓ refinesΔ order t q ⟩
    below-s s hsc hsq (t , htd , hts) =
        t
      , ( memOrApart-left d r t (sub t htd) htd
        , ForcingBase.≼-trans fb t s q (sub t htd) hsc hq hts hsq )

    fromCommon : Σ[ s ∈ S ]
                   ⟨ (s ∈ˢ carrier)
                     ⊓ (refinesΔ order s q ⊓ refinesΔ order s (fst r)) ⟩
               → ⟨ goal ⟩
    fromCommon (s , hsc , hsq , hsr) =
      PT.map (below-s s hsc hsq) (db s hsc hsr)

    decide : ⟨ compatᶜ (q , hq) r ⟩ ⊎ (⟨ compatᶜ (q , hq) r ⟩ → Empty.⊥)
           → ⟨ goal ⟩
    decide (inl c)  = PT.rec (snd goal) fromCommon c
    decide (inr nc) =
      ∣ q , ( memOrApart-right d r q hq (λ h → Empty.rec (nc h))
            , ForcingBase.≼-refl fb q hq ) ∣₁

--------------------------------------------------------------------------------
-- The genericity obligation, and Bell Problem 4.34(i)
--------------------------------------------------------------------------------

-- MeetsAll IS ledger clause L4, as a type. Its dense sets are CODES: the
-- quantifier is (d : S), the two hypotheses are ⟨ d ⊆ˢ carrier ⟩ and
-- ⟨ denseΔ carrier order d ⟩, and the body is K2's meets field character for
-- character from CodedCompletion.agda:1073-1074, with subsetOf and denseᴵ
-- unfolded to what they are defined to be at :996-1002. Nothing here is
-- weakened to an antichain, a maximal antichain or a predense set, and the
-- checkable reason is K2's own: at an empty coded d the antichain condition
-- (:1012-1017) is vacuously true while the density condition is false, so an
-- antichain-routed obligation is satisfied by nothing. The K5 side of that
-- reason is empty-not-dense below.
--
-- The declared level is Type ℓ, and it is Type ℓ BECAUSE the dense sets are
-- codes. Replace (d : S) by a host subset and the annotation fails; that
-- deliberate break is run and reported in REPORT-C section 6.

MeetsAll : Sub → Type ℓ
MeetsAll G =
  (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseΔ carrier order d ⟩
  → ⟨ ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (fst p ∈ˢ d)) ⟩

-- Bell Problem 4.34(i), which K2 does not have: reading
-- CodedCompletion.agda:1063-1092 in full shows isGeneric, generic-inhabited,
-- generic-as-host and generic-meets-predense and nothing else, and denseBelowᴵ
-- (:1007) appears in no lemma mentioning isGeneric.
--
-- A filter that meets every coded dense set meets every coded set that is
-- merely dense below one of its own members. The enlargement is dense, the
-- filter meets it, and the member it meets it at cannot lie in the apart half
-- because two members of a filter are compatible.

generic-meets-denseBelow :
    LEM ℓ → (G : Sub) → MeetsAll G → isFilter G
  → (r : Cond) → ⟨ r ∈ᴾ G ⟩
  → (d : S) → ⟨ d ⊆ˢ carrier ⟩ → ⟨ denseBelowΔ carrier order (fst r) d ⟩
  → ⟨ ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (fst p ∈ˢ d)) ⟩
generic-meets-denseBelow lem G meets fil r hr d sub db =
  PT.rec (snd goal) step
    (meets (memOrApart d r) (memOrApart-sub d r)
           (memOrApart-dense lem d sub r db))
  where
    goal : Ω
    goal = ⋁ Cond (λ p → (p ∈ᴾ G) ⊓ (fst p ∈ˢ d))

    step : Σ[ p ∈ Cond ] ⟨ (p ∈ᴾ G) ⊓ (fst p ∈ˢ memOrApart d r) ⟩ → ⟨ goal ⟩
    step (p , hpG , hpe) =
      PT.rec (snd goal)
        (λ { (inl hpd) → ∣ p , (hpG , hpd) ∣₁
           ; (inr nc)  →
               Empty.rec*
                 (nc (compatᶜ-of-host p r
                        (filter-compatible G fil p r hpG hr))) })
        (subst ⟨_⟩ (memOrApart-mem d r (fst p)) hpe .snd)

-- The checkable reason behind ledger clause L4, on this side. An empty coded
-- set is not dense, because the carrier is inhabited; so a density hypothesis
-- is never vacuous and never free. The antichain condition at the same empty
-- set holds, which is why no K5 statement routes genericity through one.

empty-not-dense : (d : S) → ((x : S) → ⟨ x ∈ˢ d ⟩ → ⟨ ⊥ ⟩)
                → ⟨ denseΔ carrier order d ⟩ → ⟨ ⊥ ⟩
empty-not-dense d no dn =
  PT.rec (snd ⊥)
    (λ { (q , hq) →
         PT.rec (snd ⊥) (λ { (p , hpd , _) → no p hpd }) (dn q hq) })
    inhabited

--------------------------------------------------------------------------------
-- The witness set
--------------------------------------------------------------------------------

-- The load-bearing new set: "the conditions lying in some member of the coded
-- value set V". V is Admits.values (K4/ValueSets.agda:291-294), which the
-- compiler already builds at every quantifier node (Compile.agda:980-984), so
-- no WitnessDomain contract, no AdequateDomain, no Fullness and no
-- MaximumPrincipleContract is needed to have it.
--
-- The formula is K2's memUnionAtˢ (CodedCompletion.agda:78-79) with the family
-- slot taken as a ground constant instead of a variable, since V is a set and
-- not a slot of a larger formula. Trap T-C3, checked and not assumed: the
-- bounded existential is Δ₀ by the constructor δ-∃∈
-- (FOL/LevyHierarchy.lagda.md:75), whose bounding TERM is an arbitrary
-- Term S n and therefore may be a con; the Boolean traversal agrees
-- (bounded (∃̇∈ t φ) = bounded φ, :112), so checkΔ₀ … tt closes it, exactly as
-- Δ₀-pseudoAtˢ (CodedVocabulary.agda:254) does for the model case.

witnessφ : S → Formula S 1
witnessφ V = ∃̇∈ (con V) (var (suc zero) ∈̇ var zero)

Δ₀-witnessφ : (V : S) → Δ₀ (witnessφ V)
Δ₀-witnessφ V = checkΔ₀ (witnessφ V) tt

opaque
  witnessAt : S → S
  witnessAt V = separateOf sep carrier (witnessφ V)

  witnessAt-mem : (V x : S)
                → (x ∈ˢ witnessAt V)
                  ≡ ((x ∈ˢ carrier) ⊓ ⋁ S (λ u → (u ∈ˢ V) ⊓ (x ∈ˢ u)))
  witnessAt-mem V x = separateOf-spec sep carrier (witnessφ V) x

witnessAt-sub : (V : S) → ⟨ witnessAt V ⊆ˢ carrier ⟩
witnessAt-sub V x h = subst ⟨_⟩ (witnessAt-mem V x) h .fst

-- DECISION D1, as the two entailments this file consumes, and no more. The
-- members of V are the CODES of algebra elements, so the reading above speaks
-- x ∈ˢ u while forcing speaks the frame's belowᶜ. At the coded completion
-- below is fst and both entailments are the identity, verified at exit 0 in
-- K5/ProbeD1.agda; at an abstract ForcingBase neither is derivable, since the
-- record relates belowᶜ to the order and never to the code. They are stated as
-- two entailments rather than as the path below b ≡ fst b so that each lemma
-- below carries only the direction it spends.

CodeOfBelow : Type ℓ
CodeOfBelow = (b : Pt B) (x : S) → ⟨ x ∈ˢ belowᶜ b ⟩ → ⟨ x ∈ˢ fst b ⟩

BelowOfCode : Type ℓ
BelowOfCode = (b : Pt B) (x : S) → ⟨ x ∈ˢ fst b ⟩ → ⟨ x ∈ˢ belowᶜ b ⟩

-- Forcing a member of V puts the condition into the witness set.

witnessAt-intro : CodeOfBelow → (V : S) (u : Pt B) → ⟨ fst u ∈ˢ V ⟩
                → (r : Cond) → ⟨ r ⊩ᴮ u ⟩ → ⟨ fst r ∈ˢ witnessAt V ⟩
witnessAt-intro cob V u huV r h =
  subst ⟨_⟩ (sym (witnessAt-mem V (fst r)))
    (snd r , ∣ fst u , (huV , cob u (fst r) (⊩ᴮ-mem r u h)) ∣₁)

-- And out again, which is the step the truth lemma's existential clause takes:
-- a condition in the witness set forces SOME member of V. The conclusion is a
-- ⋁ over Pt B, a Type ℓ, so it is an element of Ω and may be the target of
-- attained-elim (K4/ValueSets.agda:312-318). No index of the value family is
-- produced anywhere, which is what keeps host choice out.

witnessAt-force : BelowOfCode → (V : S) → ⟨ V ⊆ˢ B ⟩ → (r : Cond)
                → ⟨ fst r ∈ˢ witnessAt V ⟩
                → ⟨ ⋁ (Pt B) (λ u → (fst u ∈ˢ V) ⊓ (r ⊩ᴮ u)) ⟩
witnessAt-force boc V hV r h =
  PT.map
    (λ { (u , huV , hru) →
           (u , hV u huV)
         , (huV , ⊩ᴮ-from r (u , hV u huV) (boc (u , hV u huV) (fst r) hru)) })
    (subst ⟨_⟩ (witnessAt-mem V (fst r)) h .snd)

-- TRAP T-C1, obeyed. There is NO bare witnessAt-dense, and there cannot be:
-- below a condition whose image misses the join of V the witness set is empty.
-- What is true is density BELOW a condition whose image lies under an upper
-- bound of V, and only the LEAST-upper-bound half of the join is used, so the
-- statement is a universal property and never an equation naming a constructed
-- join. That is preamble rule 7, and it is also what keeps CodedComplete out
-- of this type.
--
-- The argument. Fix s refining p. Were no refinement of s in the witness set,
-- then for every u in V the meet i s ⊓ᴮ u would be zero, since a nonzero meet
-- hands back a refinement of s forcing u through Track A's ⊩ᴮ-extend, and that
-- refinement is in the witness set by witnessAt-intro. Zero meets make every u
-- lie under ¬ᴮ (i s), so the bound b does too, so i s lies under both b and
-- ¬ᴮ (i s) and is therefore zero, which i-nonzero forbids. One excluded middle
-- for the goal and one per member for the meet; both at propositions of the
-- frame, neither at a host subset.

witnessAt-denseBelow :
    LEM ℓ → CodeOfBelow → (V : S) (b : Pt B)
  → ((v : Pt B) → ((u : Pt B) → ⟨ fst u ∈ˢ V ⟩ → ⟨ u ≤ᴮ v ⟩) → ⟨ b ≤ᴮ v ⟩)
  → (p : Cond) → ⟨ iᶜ p ≤ᴮ b ⟩
  → ⟨ denseBelowΔ carrier order (fst p) (witnessAt V) ⟩
witnessAt-denseBelow lem cob V b blub p hpb s hsc hsp = decide (lem goal)
  where
    sc : Cond
    sc = s , hsc

    goal : Ω
    goal = ⋁ S (λ t → (t ∈ˢ witnessAt V) ⊓ refinesΔ order t s)

    hitGoal : (u : Pt B) → ⟨ fst u ∈ˢ V ⟩
            → (((iᶜ sc ⊓ᴮ u) ≡ ⊥ᴮ) → Empty.⊥) → ⟨ goal ⟩
    hitGoal u huV nz =
      PT.rec (snd goal)
        (λ { (t , hts , htu) →
             ∣ fst t , (witnessAt-intro cob V u huV t htu , hts) ∣₁ })
        (⊩ᴮ-extend sc u (λ e → Empty.rec (nz e)))

    apart : (⟨ goal ⟩ → Empty.⊥) → (u : Pt B) → ⟨ fst u ∈ˢ V ⟩
          → ⟨ u ≤ᴮ (¬ᴮ (iᶜ sc)) ⟩
    apart no u huV = ⊓⊥→≤¬ u (iᶜ sc) (⊓-comm u (iᶜ sc) ∙ pick (lem meetΩ))
      where
        meetΩ : Ω
        meetΩ = ((iᶜ sc ⊓ᴮ u) ≡ ⊥ᴮ) , isSetPt B (iᶜ sc ⊓ᴮ u) ⊥ᴮ

        pick : ⟨ meetΩ ⟩ ⊎ (⟨ meetΩ ⟩ → Empty.⊥) → (iᶜ sc ⊓ᴮ u) ≡ ⊥ᴮ
        pick (inl e)  = e
        pick (inr nz) = Empty.rec (no (hitGoal u huV nz))

    decide : ⟨ goal ⟩ ⊎ (⟨ goal ⟩ → Empty.⊥) → ⟨ goal ⟩
    decide (inl g)  = g
    decide (inr no) =
      Empty.rec*
        (i-nonzero sc
          (≤-both-⊥ (iᶜ sc) (iᶜ sc) (≤ᴮ-refl (iᶜ sc))
            (⊆ˢ-trans (⊆ˢ-trans (i-mono p sc hsp) hpb)
                      (blub (¬ᴮ (iᶜ sc)) (apart no)))))

-- The same statement at the coded supremum, for a consumer that has one. The
-- join appears in this type, which preamble rules 3 and 7 warn about; it is
-- safe here for rule 2's reason, that supᴮ is a projection out of a module
-- PARAMETER and so is a variable that cannot unfold. The universal-property
-- form above is the one Track G should prefer.

witnessAt-denseBelow-sup :
    LEM ℓ → CodeOfBelow → (V : S) (hV : ⟨ V ⊆ˢ B ⟩) (p : Cond)
  → ⟨ iᶜ p ≤ᴮ supᴮ V hV ⟩
  → ⟨ denseBelowΔ carrier order (fst p) (witnessAt V) ⟩
witnessAt-denseBelow-sup lem cob V hV p =
  witnessAt-denseBelow lem cob V (supᴮ V hV) (sup-lub V hV) p

-- The other half of the degenerate audit of exit item X3: at an empty value
-- set the witness set is empty, hence by empty-not-dense not dense. So the
-- hypotheses of witnessAt-denseBelow are carried and not decorative.

witnessAt-empty : (V : S) → ((u : S) → ⟨ u ∈ˢ V ⟩ → ⟨ ⊥ ⟩)
                → (x : S) → ⟨ x ∈ˢ witnessAt V ⟩ → ⟨ ⊥ ⟩
witnessAt-empty V no x h =
  PT.rec (snd ⊥) (λ { (u , huV , _) → no u huV })
         (subst ⟨_⟩ (witnessAt-mem V x) h .snd)

witnessAt-empty-not-dense : (V : S) → ((u : S) → ⟨ u ∈ˢ V ⟩ → ⟨ ⊥ ⟩)
                          → ⟨ denseΔ carrier order (witnessAt V) ⟩ → ⟨ ⊥ ⟩
witnessAt-empty-not-dense V no =
  empty-not-dense (witnessAt V) (witnessAt-empty V no)

--------------------------------------------------------------------------------
-- The non-claims this track is required to state beside its signatures
--------------------------------------------------------------------------------

-- GENERICITY IS NEVER WEAKENED TO AN ANTICHAIN. MeetsAll above is the only
-- genericity obligation this file states or consumes, its dense sets are codes
-- and its statement is K2's meets field taken flat. isGeneric itself is not
-- re-declared anywhere here (preamble rule 9); the instance file supplies
-- isGeneric.meets g.
--
-- O6. No coded order graph of B exists, so isGeneric in K2's sense
-- (CodedCompletion.agda:1070-1074) cannot be stated of a subset of the
-- algebra. That is an unbuilt interface and not an unproved theorem, and
-- nothing above is to be read as supplying it.
--
-- THE REVERSE CORRESPONDENCE IS OUT OF SCOPE BY RULING, not by omission. The
-- pullback G-of U is K6's or K11's, under an explicit separativity hypothesis:
-- directedness of a filter demands a common refinement INSIDE the filter
-- (ForcingNotion.agda:175-180) and the image of an ultrafilter gives only
-- separate compatibility. No statement above claims it.
--
-- D1 IS A HYPOTHESIS AND NOT A THEOREM HERE. CodeOfBelow and BelowOfCode are
-- free at the coded completion and undischarged at an abstract ForcingBase;
-- every witnessAt lemma that spends one names it in its type, and the other
-- eleven deliverables of this file name neither.
--
-- ORDER REFLECTION is not assumed, derived or used. Every density argument
-- above travels through compatibility and a common refinement, either its own
-- excluded middle at compatᶜ or Track A's ⊩ᴮ-extend, and never reads an order
-- relation back off an inequality between images. K2 refutes the reflection at
-- InstancesCompletion.agda:131-134.
--
-- SEPARATIVITY is not a field, not a hypothesis and not used.
