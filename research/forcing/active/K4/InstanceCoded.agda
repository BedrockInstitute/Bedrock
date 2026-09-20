{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track K, file 2 of 4. The transport instance: the coded completion of
-- an arbitrary presentation is a K4 algebra, complement and all.
--
-- THE GAP THIS FILE CLOSES, and it is a planned gap and not an accident.
-- CodedCompletion.agda:1184-1189 says in its own words: "A coded element is
-- read as a host subset of the decoded conditions; the reading is injective
-- and preserves every finite operation, so every BOOLEAN LAW of the coded
-- algebra is transported from Track C's roLaws along reads-inj, and not one
-- of them is proved internally here." K2 built the injection and left the
-- transport unwritten. K4 needs three of those laws, because they are exactly
-- the three fields of Complement, and this file writes the transport.
--
-- THE OBSTACLE, MEASURED, AND THE REPAIR. Writing the transport the obvious
-- way does not elaborate. The cause is not the transport and not the host
-- algebra: it is that a K4 law is a statement about a NEST of two coded
-- operations, and a statement whose type contains such a nest sends the
-- elaborator into a check that does not finish. The threshold is exact and
-- it was isolated here by a ladder of probes under one option set, plain
-- `agda`, each capped and each reproduced:
--
--   a term of nested depth two, with no statement about it      0.94 s
--   a STATEMENT at nested depth one, any operation              0.84 s
--   a statement at nested depth two, pure order, no complement  no finish in 200 s
--   the same at the complement, through reads                   no finish in 200 s
--   the whole file as first written                             no finish in 25 min, 943 MB
--
-- Depth one is free and depth two is unreachable, and which operations are
-- nested makes no difference: u ⊓ᴮ (u ⊓ᴮ v) fails exactly as u ⊓ᴮ (¬ᴮ u)
-- does. K2 met the same wall from the other side and recorded it at
-- CodedCompletion.agda:1146-1152, at the composite iᴮ p ⊓ᴮ iᴮ q, with three
-- drafts killed at 19, 11 and 11 minutes at about 1.15 GB; its remedy was to
-- state its two unpackings at variables and let the caller instantiate. That
-- remedy does not reach a K4 law, because a K4 law IS the statement at the
-- composite and there is no caller left to push the problem to.
--
-- The repair is project rule 2, applied on the K4 side to objects K2 left
-- transparent. Not one occurrence of `opaque` exists in CodedCompletion.agda
-- (grep count 0, re-run here), so every coded operation is an unsealed
-- description-operator term: the meet is a separateOf over a formula whose
-- constant is the second argument's code, and nesting puts one description
-- inside the syntax of another. Sealing each operation on this side and
-- OPENING EACH SEAL ALONE makes the inner argument of a nest neutral, which
-- is the shape K2's own lemmas already elaborate at. Measured: the first
-- complement law, transported through reads, reads-inj and the host law,
-- elaborates in 1.38 s sealed against no finish in 200 s unsealed, nothing
-- else changed.
--
-- WHAT THAT COSTS A CONSUMER, stated plainly because it is the price of the
-- file. The five operations below are propositionally the coded ones and are
-- not definitionally so outside an `opaque unfolding` block. A consumer that
-- needs the unfolding writes one, and a consumer that takes the three records
-- as module parameters, which is every K4 track, never needs one. K3 measured
-- the same trade and reported that a record only ever passed as a parameter
-- is never definitionally compared, so the seal there was free; here the seal
-- is not merely free, it is what makes the file exist.
--
-- HOW A TRANSPORT ALONG AN INJECTION WORKS, since the shape recurs. To prove
-- an equation between two coded elements, apply reads to both sides, rewrite
-- each side by the homomorphism lemmas until both sides are host expressions
-- in reads u, reads v, reads w, quote the host law, and conclude by
-- injectivity. The homomorphism lemmas are reads-⊤, reads-⊥, reads-⊓,
-- reads-¬ and reads-⊔ (CodedCompletion.agda:1236-1262); the host laws are
-- HostRegularOpen's ¬ᴮ-⊓ᴮ, ¬ᴮ-⊔ᴮ and ⊓ᴮ-⊔ᴮ-dist (:570, :579, :533);
-- injectivity is reads-inj (:1229). Each of the three transports is stated
-- first as a lemma over BARE VARIABLES with the readings as hypotheses, and
-- then instantiated at the sealed operations. Both halves of that are needed:
-- the variables keep the elaborated statement at depth one, and the seals
-- keep the instantiation at depth one as well.
--
-- WHAT MAY NOT BE TRANSPORTED THIS WAY, stated here because this file is the
-- one place in K4 where both carriers are in scope. The preamble's rule R6
-- says reads preserves only the FINITE operations: grep for reads-sup,
-- reads-inf, reads-⋁, reads-⋀ in CodedCompletion.agda returns 0, re-run for
-- this file. A supremum or an infimum of a coded family is therefore NOT
-- known to be read as the host join or meet, and no infinitary law is
-- transported below. The three laws this file moves are all finite. Rule R5's
-- prohibition on an infinite distributive law over Pt B is untouched: the
-- distributivity proved here is the BINARY one, which is the third field of
-- Complement and nothing more.
--
-- THE TWO LATTICE LAWS THAT NEED NO TRANSPORT. ⊥-least and ⊤-greatest are
-- the two Lattice fields with no counterpart among K2's named lemmas, and
-- neither needs the host algebra. The coded bottom is the empty code, so its
-- order statement is empty elimination; the coded top is the carrier itself,
-- so its order statement is the subset law every element of B already
-- carries. Both are one line and both are proved here rather than assumed.
--
-- HYPOTHESES, the whole list: the structure, Extensionality, PowerSet,
-- Separation, the path realization, a Presentation and its forcing laws.
-- That is CodedCompletion.Core's telescope verbatim and nothing is added. No
-- excluded middle: this file mentions no member of CodedCompletion.Classical.
-- No nontriviality either, except in the last declaration, which takes a
-- condition as an explicit argument for the reason HostRegularOpen.agda:625
-- gives: nondegeneracy FAILS for the empty forcing notion.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using ( tt* )
import OrdinaryProfile
import CodedCompletion
import K4.Algebra

module K4.InstanceCoded
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext   : OrdinaryProfile.Extensionality 𝒮)
  (pow   : OrdinaryProfile.PowerSet 𝒮)
  (sep   : OrdinaryProfile.Separation 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  (𝔓     : CodedCompletion.Presentation 𝒮)
  (laws  : CodedCompletion.Coded.ForcingLaws 𝒮 𝔓)
  where

open import FOL.ZFStructure using ( module hPropStructure )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import K4.Algebra 𝒮 using ( Pt; _≤ᴮ_; Lattice; Complement; CodedComplete )

-- The one module application in this file. Everything below is a projection
-- out of it, which is why the file is thin: the elaboration cost of the
-- completion is paid once, here, and measured at 0.91 s on its own.

module CO = CodedCompletion.Core 𝒮 ext pow sep paths 𝔓 laws
module RO = CO.RO

open CO using ( El; reads; reads-inj; reads-⊤; reads-⊥; reads-⊓; reads-¬; reads-⊔ )

-- ---------------------------------------------------------------------
-- The five seals
-- ---------------------------------------------------------------------

-- One seal per operation, in five separate blocks, so that a proof can open
-- exactly the one it needs. A single block holding all five would be useless:
-- opening it to unfold the meet would also unfold the complement, and the
-- nest would be transparent again.

opaque
  negᴷ : El → El
  negᴷ = CO.¬ᴮ_

opaque
  meetᴷ : El → El → El
  meetᴷ = CO._⊓ᴮ_

opaque
  joinᴷ : El → El → El
  joinᴷ = CO._⊔ᴮ_

-- The two infinitary operations are sealed on the same reasoning, although
-- no law in this file nests them. A consumer that writes supᴮ of a value set
-- and then states a fact about it is at depth two in exactly the sense
-- measured above, and rule R3 already forbids that signature for a different
-- reason; the seal is the mechanical half of the same discipline.

opaque
  supᴷ : (X : S) → ⟨ X ⊆ˢ CO.B ⟩ → El
  supᴷ = CO.supᴮ

opaque
  infᴷ : (X : S) → ⟨ X ⊆ˢ CO.B ⟩ → El
  infᴷ = CO.infᴮ

-- ---------------------------------------------------------------------
-- The bounded lattice
-- ---------------------------------------------------------------------

-- Every statement in this block is at depth one, which is what lets it
-- elaborate at all. Eight of the ten fields are K2's own named lemmas under
-- K4's field names: K2 names its order lemmas after the order (⊓ᴮ-le₁,
-- ⊔ᴮ-ge₁) and K4 after the universal property (⊓-lb₁, ⊔-ub₁), and the
-- statements are identical, both being about fst u ⊆ˢ fst v.

opaque
  unfolding meetᴷ

  ⊓-lb₁ : (u v : El) → ⟨ meetᴷ u v ≤ᴮ u ⟩
  ⊓-lb₁ = CO.⊓ᴮ-le₁

  ⊓-lb₂ : (u v : El) → ⟨ meetᴷ u v ≤ᴮ v ⟩
  ⊓-lb₂ = CO.⊓ᴮ-le₂

  ⊓-glb : (u v w : El) → ⟨ w ≤ᴮ u ⟩ → ⟨ w ≤ᴮ v ⟩ → ⟨ w ≤ᴮ meetᴷ u v ⟩
  ⊓-glb = CO.⊓ᴮ-glb

opaque
  unfolding joinᴷ

  ⊔-ub₁ : (u v : El) → ⟨ u ≤ᴮ joinᴷ u v ⟩
  ⊔-ub₁ = CO.⊔ᴮ-ge₁

  ⊔-ub₂ : (u v : El) → ⟨ v ≤ᴮ joinᴷ u v ⟩
  ⊔-ub₂ = CO.⊔ᴮ-ge₂

  ⊔-lub : (u v w : El) → ⟨ u ≤ᴮ w ⟩ → ⟨ v ≤ᴮ w ⟩ → ⟨ joinᴷ u v ≤ᴮ w ⟩
  ⊔-lub = CO.⊔ᴮ-lub

-- The bottom is the empty code, so the order statement is empty elimination.

⊥-least : (u : El) → ⟨ CO.⊥ᴮ ≤ᴮ u ⟩
⊥-least u x h = Empty.rec* (CO.⊥ᴮ-empty x h)

-- The top is the carrier, definitionally (CodedCompletion.agda:512-513), so
-- "every element is below the top" is "every element's code is a subset of
-- the carrier", which is B-sub (:441-442) applied to the element's own
-- membership proof. No unfolding of the regular-open construction is
-- involved and the proof does not mention the star operator at all.

⊤-greatest : (u : El) → ⟨ u ≤ᴮ CO.⊤ᴮ ⟩
⊤-greatest u = CO.B-sub (fst u) (snd u)

codedLattice : Lattice CO.B
codedLattice = record
  { ⊤ᴮ         = CO.⊤ᴮ
  ; ⊥ᴮ         = CO.⊥ᴮ
  ; _⊓ᴮ_       = meetᴷ
  ; _⊔ᴮ_       = joinᴷ
  ; ⊓-lb₁      = ⊓-lb₁
  ; ⊓-lb₂      = ⊓-lb₂
  ; ⊓-glb      = ⊓-glb
  ; ⊔-ub₁      = ⊔-ub₁
  ; ⊔-ub₂      = ⊔-ub₂
  ; ⊔-lub      = ⊔-lub
  ; ⊥-least    = ⊥-least
  ; ⊤-greatest = ⊤-greatest }

-- ---------------------------------------------------------------------
-- The readings of the sealed operations
-- ---------------------------------------------------------------------

-- Each is K2's homomorphism lemma restated at the sealed operation, inside
-- the one seal it concerns. The statements are at variables, so each is a
-- depth-one statement and each elaborates.

opaque
  unfolding negᴷ
  negᴷ-reads : (u : El) → reads (negᴷ u) ≡ RO.¬ᴮ_ (reads u)
  negᴷ-reads = reads-¬

opaque
  unfolding meetᴷ
  meetᴷ-reads : (u v : El) → reads (meetᴷ u v) ≡ RO._⊓ᴮ_ (reads u) (reads v)
  meetᴷ-reads = reads-⊓

opaque
  unfolding joinᴷ
  joinᴷ-reads : (u v : El) → reads (joinᴷ u v) ≡ RO._⊔ᴮ_ (reads u) (reads v)
  joinᴷ-reads = reads-⊔

-- ---------------------------------------------------------------------
-- The three transports, at variables
-- ---------------------------------------------------------------------

-- Rule R3's own remedy: the composite is a VARIABLE and its reading is a
-- hypothesis. Read each of these as the mathematics without the bookkeeping:
-- "if n reads as the host complement of u, and m reads as the host meet of u
-- and n, then m is the coded bottom". The three host laws fire once each.

module Transport where

  ¬-⊓-at : (u n m : El)
         → reads n ≡ RO.¬ᴮ_ (reads u)
         → reads m ≡ RO._⊓ᴮ_ (reads u) (reads n)
         → m ≡ CO.⊥ᴮ
  ¬-⊓-at u n m hn hm = reads-inj m CO.⊥ᴮ
    ( hm
    ∙ cong (λ t → RO._⊓ᴮ_ (reads u) t) hn
    ∙ RO.¬ᴮ-⊓ᴮ (reads u)
    ∙ sym reads-⊥ )

  ¬-⊔-at : (u n m : El)
         → reads n ≡ RO.¬ᴮ_ (reads u)
         → reads m ≡ RO._⊔ᴮ_ (reads u) (reads n)
         → m ≡ CO.⊤ᴮ
  ¬-⊔-at u n m hn hm = reads-inj m CO.⊤ᴮ
    ( hm
    ∙ cong (λ t → RO._⊔ᴮ_ (reads u) t) hn
    ∙ RO.¬ᴮ-⊔ᴮ (reads u)
    ∙ sym reads-⊤ )

  -- Seven names and six hypotheses, because the binary distributive law has
  -- a compound on both sides: a for v ⊔ w, b for the left-hand meet, c and d
  -- for the two meets on the right, e for their join. No congruence is
  -- applied to two arguments at once; rule R1's single-argument form keeps
  -- every endpoint written out.

  dist-at : (u v w a b c d e : El)
          → reads a ≡ RO._⊔ᴮ_ (reads v) (reads w)
          → reads b ≡ RO._⊓ᴮ_ (reads u) (reads a)
          → reads c ≡ RO._⊓ᴮ_ (reads u) (reads v)
          → reads d ≡ RO._⊓ᴮ_ (reads u) (reads w)
          → reads e ≡ RO._⊔ᴮ_ (reads c) (reads d)
          → b ≡ e
  dist-at u v w a b c d e ha hb hc hd he = reads-inj b e
    ( hb
    ∙ cong (λ t → RO._⊓ᴮ_ (reads u) t) ha
    ∙ RO.⊓ᴮ-⊔ᴮ-dist (reads u) (reads v) (reads w)
    ∙ cong (λ t → RO._⊔ᴮ_ t (RO._⊓ᴮ_ (reads u) (reads w))) (sym hc)
    ∙ cong (λ t → RO._⊔ᴮ_ (reads c) t) (sym hd)
    ∙ sym he )

-- ---------------------------------------------------------------------
-- The complement
-- ---------------------------------------------------------------------

-- The instantiations. Every argument below is built from sealed operations,
-- so every one of them is neutral and the elaborator never meets a nest it
-- can see into. This is the block that did not finish before the seals.

¬-⊓ : (u : El) → meetᴷ u (negᴷ u) ≡ CO.⊥ᴮ
¬-⊓ u = Transport.¬-⊓-at u (negᴷ u) (meetᴷ u (negᴷ u))
          (negᴷ-reads u) (meetᴷ-reads u (negᴷ u))

¬-⊔ : (u : El) → joinᴷ u (negᴷ u) ≡ CO.⊤ᴮ
¬-⊔ u = Transport.¬-⊔-at u (negᴷ u) (joinᴷ u (negᴷ u))
          (negᴷ-reads u) (joinᴷ-reads u (negᴷ u))

⊓-⊔-dist : (u v w : El)
         → meetᴷ u (joinᴷ v w) ≡ joinᴷ (meetᴷ u v) (meetᴷ u w)
⊓-⊔-dist u v w =
  Transport.dist-at u v w
    (joinᴷ v w) (meetᴷ u (joinᴷ v w)) (meetᴷ u v) (meetᴷ u w)
    (joinᴷ (meetᴷ u v) (meetᴷ u w))
    (joinᴷ-reads v w) (meetᴷ-reads u (joinᴷ v w))
    (meetᴷ-reads u v) (meetᴷ-reads u w)
    (joinᴷ-reads (meetᴷ u v) (meetᴷ u w))

codedComplement : Complement CO.B codedLattice
codedComplement = record
  { ¬ᴮ_      = negᴷ
  ; ¬-⊓      = ¬-⊓
  ; ¬-⊔      = ¬-⊔
  ; ⊓-⊔-dist = ⊓-⊔-dist }

-- ---------------------------------------------------------------------
-- Completeness for the coded families
-- ---------------------------------------------------------------------

-- No transport here, and none is possible: rule R6 again. K2 proves the four
-- universal properties internally (CodedCompletion.agda:914-917 collects
-- them) and they are taken as they stand, restated at the sealed operations.

opaque
  unfolding supᴷ

  sup-ub : (X : S) (h : ⟨ X ⊆ˢ CO.B ⟩) (u : El)
         → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ supᴷ X h ⟩
  sup-ub = CO.sup-upper

  sup-lub : (X : S) (h : ⟨ X ⊆ˢ CO.B ⟩) (v : El)
          → ((u : El) → ⟨ fst u ∈ˢ X ⟩ → ⟨ u ≤ᴮ v ⟩)
          → ⟨ supᴷ X h ≤ᴮ v ⟩
  sup-lub = CO.sup-least

opaque
  unfolding infᴷ

  inf-lb : (X : S) (h : ⟨ X ⊆ˢ CO.B ⟩) (u : El)
         → ⟨ fst u ∈ˢ X ⟩ → ⟨ infᴷ X h ≤ᴮ u ⟩
  inf-lb = CO.inf-lower

  inf-glb : (X : S) (h : ⟨ X ⊆ˢ CO.B ⟩) (v : El)
          → ((u : El) → ⟨ fst u ∈ˢ X ⟩ → ⟨ v ≤ᴮ u ⟩)
          → ⟨ v ≤ᴮ infᴷ X h ⟩
  inf-glb = CO.inf-greatest

codedComplete : CodedComplete CO.B codedLattice
codedComplete = record
  { supᴮ    = supᴷ
  ; sup-ub  = sup-ub
  ; sup-lub = sup-lub
  ; infᴮ    = infᴷ
  ; inf-lb  = inf-lb
  ; inf-glb = inf-glb }

-- ---------------------------------------------------------------------
-- Nontriviality, on a condition
-- ---------------------------------------------------------------------

-- The shared preamble's first banner: Bell 1.23(ii) is false at a degenerate
-- algebra, K4 assumes nontriviality nowhere, and the instance must carry it.
-- Here is where it comes from, and it is not free: HostRegularOpen.agda:625
-- records that nondegeneracy FAILS for the empty forcing notion, where Reg
-- has one element, so the hypothesis is a condition and not a theorem. The
-- proof transports the host nondegeneracy backwards along reads, which is
-- legal because it is a statement about two of the finite constants and
-- involves no nest.

codedNontrivial : CO.FS.Cond → (CO.⊥ᴮ ≡ CO.⊤ᴮ) → ⟨ ⊥ ⟩
codedNontrivial p e = RO.Reg⊑ RO.⊤ᴮ RO.⊥ᴮ (sym host) p tt*
  where
    host : RO.⊥ᴮ ≡ RO.⊤ᴮ
    host = sym reads-⊥ ∙ cong reads e ∙ reads-⊤
