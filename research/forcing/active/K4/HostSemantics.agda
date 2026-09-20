{-# OPTIONS --cubical --safe --guardedness #-}

-- K4.9. THE HOST REFERENCE SEMANTICS AND THE CONDITIONAL AGREEMENT.
--
-- SUBORDINATE BY DESIGN. This file defines a second Boolean valuation of the
-- name layer, in the HOST regular open algebra, and relates it to the coded
-- one. The word subordinate is load bearing in three separate ways and each of
-- them is enforced by shape and not by comment.
--
--   1. The host valuation is a REFERENCE, never a definition. K4's Boolean
--      value is the coded one, `Pt B`, because K0's representation ledger fixes
--      the interpreted ultrafilter as a predicate on the B-carrier. Nothing
--      downstream may reach a host value, and nothing downstream may import
--      this module: it is the only K4 file that mentions both carriers.
--   2. The agreement is a THEOREM WITH ITS HYPOTHESES VISIBLE. Every statement
--      that identifies a coded value with a host value carries `reads-sup` and
--      `reads-inf` as explicit arguments. The roadmap's sentence is that
--      agreement with the host evaluator is CONDITIONAL ON BOTH ADMITTING THE
--      RELEVANT FAMILIES (cohen-implementation-roadmap-2026-09.md:193), and
--      those two arguments are exactly that condition, in the one form the
--      induction consumes.
--   3. There is NO internal global truth value function. `interp` is a host
--      function on source formulas, taken here as a parameter, and no code of
--      a formula ever enters a term. Bell, printed page 24 (fulltext:2043-2052),
--      in his own words: "one can prove in ZFC that the collection of all pairs
--      <sigma, [[sigma]]B> is not a definable class. We must therefore think of
--      this map as being defined metalinguistically." That restriction is a
--      THEOREM of ZFC, so it may not be presented as future work, and the host
--      evaluator below does not evade it: `_⊫_` is the book's own
--      `FOL.Semantics`, a host recursion over a host formula, at a second
--      truth algebra. It is a map of the metatheory exactly as the coded one is.
--
-- WHY A REFERENCE SEMANTICS IS CHEAP, which is the architecture's reason for
-- shipping it at all. The host regular open algebra is a TRUTH ALGEBRA
-- (`roAlgebra : TruthAlgebra ℓ (ℓ-suc ℓ)`, HostRegularOpen.agda:446) and names
-- live at the carrier's level (`Name : Type ℓ`, NameKernel.agda:481). So
-- `ZFStructure roAlgebra` with `S := Name` is type correct, and the ten
-- satisfaction clauses of src/FOL/Semantics.lagda.md:107-123 come over with no
-- work at all, including the two unbounded quantifiers, because `Name` fills
-- the `⋀`/`⋁` index slot exactly. That is what this file spends and it is all
-- it spends: the host atomic layer below is built from `⋀ᴿ` and `⋁ᴿ` over
-- `Pt (support n)`, with no value set, no Separation, no Collection and no
-- admission hypothesis anywhere.
--
-- R7, THE ONE CONSTRAINT THAT WILL BE MISTAKEN FOR A LEVEL FAILURE. Equality
-- of two host values is NOT a truth value: `Reg : Type (ℓ-suc ℓ)`
-- (HostRegularOpen.agda:264), while the small entailment `_⊑_ : Sub → Sub →
-- Type ℓ` is (`:96-100`, with the file's own smallness note at `:91-95`). So
-- `Agrees` below is a PAIR OF ENTAILMENTS and never a path, and the wrong
-- instinct on meeting that is to raise a level or reach for resizing. It is a
-- false obstruction: two small entailments are an `Ω`, and `Reg≡`
-- (HostRegularOpen.agda:282) converts them to a path OUTSIDE every `Ω`.
--
-- PARAMETERS, NOT IMPORTS. This file imports no K1, K2 or K3 module and no
-- other K4 module except `K4.Algebra` (for the three algebra records and the
-- point vocabulary) and `K4.Implication` (for one definition and two laws). The
-- host algebra enters as an abstract `TruthAlgebra ℓ (ℓ-suc ℓ)` with its
-- Boolean laws, its host completeness and its small entailment; the name layer,
-- the reading map and the compiler enter flat. `K4/ProbeJ.agda` discharges the
-- host half of that telescope from the real `HostRegularOpen` at exit 0, so the
-- abstraction is checked and not asserted.
--
-- RECORDS ARE GENERATIVE. This file declares NO record. `Lattice`,
-- `Complement` and `CodedComplete` come from `K4.Algebra`; Track C's
-- `AtomicSemantics` and Track F's `InterpLaws` are taken FIELD BY FIELD as flat
-- parameters, which is what Tracks D, E and F each independently chose and for
-- the same measured reason: a flat field list creates no second type and puts
-- no other track's telescope into this one.
--
-- WHAT IS SEALED, and why nothing needs to be. R2 seals description operator
-- terms. There is no description operator in this file: every set is a
-- variable, `⋀ᴿ` and `⋁ᴿ` are projections of a parameter and therefore rigid,
-- and `_≈ᴿ_` is `rawPairRec` applied to a parameter, which cannot unfold
-- either. The seal this file must not break is Track C's, and it does not: the
-- coded atomic values enter as parameters, so `eqᴬ` and `memᴬ` never unfold.
--
-- R3 BY CONSTRUCTION. No signature here contains `supᴮ` or `infᴮ` applied to a
-- constructed set, because no signature here contains `supᴮ` or `infᴮ` at all.
-- The two reading hypotheses are stated as universal properties of an abstract
-- family, so `CodedComplete` is carried only for the uniform telescope and for
-- the two bridge lemmas of section 9 that connect them back to the
-- architecture's own `supᴮ X h` spelling.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
open import FOL.Syntax using
  ( Term; con; var
  ; Formula; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Semantics
open import Algebra using ( module BooleanAlgebra )
import OrdinaryProfile
import K4.Algebra
import K4.Implication

module K4.HostSemantics
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.HLevels using ( isSetΣSndProp )
import Cubical.Data.Empty as Empty

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮

open K4.Algebra 𝒮
  using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans; Lattice; Complement; CodedComplete )

--------------------------------------------------------------------------------
-- 1. The host reference semantics
--------------------------------------------------------------------------------

-- THE LEDGER OF PART ONE, and it is worth reading before the telescope. This
-- module knows nothing about the coded algebra. It takes a truth algebra at the
-- level arithmetic of the regular opens, its Boolean laws, its HOST
-- completeness, the recursion kernel of the name layer, the support, and one
-- host valued weight. From those it builds the two atomic values, a
-- `ZFStructure` over the host algebra, the whole satisfaction relation, and
-- three of Bell's 1.17 clauses. No `reads`, no `Pt B`, no admission, no
-- Separation.
--
-- THE LEVEL POLYMORPHISM IS FORCED AND IT IS A CORRECTION TO TRACK C'S
-- SPELLING. Track C takes the kernel at `(P : S → S → Type ℓ)`
-- (K4/Atomic.agda:169). That instance does not serve this file: the host value
-- is a `Reg`, which is `Type (ℓ-suc ℓ)`, so the recursion that defines `_≈ᴿ_`
-- is at `ℓ-suc ℓ` and the recursion that proves symmetry is a path there. The
-- real kernel is level polymorphic already, `module RawPairRec {ℓp}
-- (P : S → S → Type ℓp)` at NameKernel.agda:411, so nothing in K3 has to
-- change; but a coordinator who instantiates this file from Track C's own
-- parameter list rather than from the kernel will find the levels do not fit.
--
-- `wtᴿ` is a host weight and NOT yet `reads ∘ weightᴮ`. Keeping it abstract
-- here is what makes the claim "the host semantics is subordinate" checkable:
-- part two supplies the connection as a hypothesis, and part one is visibly
-- independent of it.

module Reference
  (𝕋ᴿ : TruthAlgebra ℓ (ℓ-suc ℓ))
  (roLaws : BooleanAlgebra.BooleanLaws 𝕋ᴿ)
  (roComplete : BooleanAlgebra.CompleteHost 𝕋ᴿ)
  (IsName : S → Ω)
  (Child : S → S → Type ℓ)
  (rawRec : {ℓp : Level} (P : S → Type ℓp)
          → ((n : S) → ((x : S) → Child x n → P x) → P n)
          → (n : S) → P n)
  (rawPairRec : {ℓp : Level} (P : S → S → Type ℓp)
              → ((x y : S) → ((u v : S) → Child u x → Child v y → P u v) → P x y)
              → (x y : S) → P x y)
  (rawPairComp : {ℓp : Level} (P : S → S → Type ℓp)
               → (st : (x y : S)
                     → ((u v : S) → Child u x → Child v y → P u v) → P x y)
               → (x y : S)
               → rawPairRec P st x y ≡ st x y (λ u v _ _ → rawPairRec P st u v))
  (support     : S → S)
  (support-out : (n x : S) → ⟨ x ∈ˢ support n ⟩ → Child x n)
  (wtᴿ : (n x : S) → TruthAlgebra.Ω 𝕋ᴿ)
  where

  private
    module RA = BooleanAlgebra 𝕋ᴿ
    module RT = RA.BooleanTheory roLaws

  open RA.CompleteHost roComplete using ( ⋁-sup ; ⋀-inf )

  -- The host vocabulary, aliased rather than opened with `renaming`, for one
  -- mechanical reason: a renamed operator carries no fixity, and this file
  -- writes long nested expressions in which the difference between `infixr 12`
  -- and the default would be a silent reparse. Each alias is a plain definition
  -- and unfolds to the projection, so every law of `roLaws` and every field of
  -- `roComplete` applies to it with no transport.

  infixr 12 _⊓ᴿ_ _⊔ᴿ_
  infixr 10 _⇒ᴿ_
  infix  13 ¬ᴿ_
  infix  4  _≤ᴿ_

  Reg : Type (ℓ-suc ℓ)
  Reg = TruthAlgebra.Ω 𝕋ᴿ

  isSetReg : isSet Reg
  isSetReg = TruthAlgebra.isSetΩ 𝕋ᴿ

  _⊓ᴿ_ _⊔ᴿ_ _⇒ᴿ_ : Reg → Reg → Reg
  _⊓ᴿ_ = TruthAlgebra._⊓_ 𝕋ᴿ
  _⊔ᴿ_ = TruthAlgebra._⊔_ 𝕋ᴿ
  _⇒ᴿ_ = TruthAlgebra._⇒_ 𝕋ᴿ

  ¬ᴿ_ : Reg → Reg
  ¬ᴿ_ = TruthAlgebra.¬_ 𝕋ᴿ

  ⊤ᴿ ⊥ᴿ : Reg
  ⊤ᴿ = TruthAlgebra.⊤ 𝕋ᴿ
  ⊥ᴿ = TruthAlgebra.⊥ 𝕋ᴿ

  ⋀ᴿ ⋁ᴿ : (A : Type ℓ) → (A → Reg) → Reg
  ⋀ᴿ = TruthAlgebra.⋀ 𝕋ᴿ
  ⋁ᴿ = TruthAlgebra.⋁ 𝕋ᴿ

  -- The order is the lattice order of the abstract algebra, spelled out so that
  -- it has a fixity here. It is `Type (ℓ-suc ℓ)`, which is R7 in its positive
  -- form: an order statement between two host values is large, and the small
  -- entailment that part two adds is the device that makes the AGREEMENT small.

  _≤ᴿ_ : Reg → Reg → Type (ℓ-suc ℓ)
  a ≤ᴿ b = (a ⊓ᴿ b) ≡ a

  isProp≤ᴿ : (a b : Reg) → isProp (a ≤ᴿ b)
  isProp≤ᴿ a b = isSetReg (a ⊓ᴿ b) a

  ≤ᴿ-refl : (a : Reg) → a ≤ᴿ a
  ≤ᴿ-refl = RT.≤-refl

  ≤ᴿ-trans : (a b c : Reg) → a ≤ᴿ b → b ≤ᴿ c → a ≤ᴿ c
  ≤ᴿ-trans = RT.≤-trans

  ≤ᴿ-antisym : (a b : Reg) → a ≤ᴿ b → b ≤ᴿ a → a ≡ b
  ≤ᴿ-antisym = RT.≤-antisym

  ⊓ᴿ-lb₁ : (a b : Reg) → (a ⊓ᴿ b) ≤ᴿ a
  ⊓ᴿ-lb₁ = RT.⊓-≤-l

  ⊓ᴿ-lb₂ : (a b : Reg) → (a ⊓ᴿ b) ≤ᴿ b
  ⊓ᴿ-lb₂ = RT.⊓-≤-r

  ⊓ᴿ-glb : (a b c : Reg) → c ≤ᴿ a → c ≤ᴿ b → c ≤ᴿ (a ⊓ᴿ b)
  ⊓ᴿ-glb = RT.⊓-greatest

  ⊓ᴿ-comm : (a b : Reg) → (a ⊓ᴿ b) ≡ (b ⊓ᴿ a)
  ⊓ᴿ-comm = RT.⊓-comm

  ⊓ᴿ-idem : (a : Reg) → (a ⊓ᴿ a) ≡ a
  ⊓ᴿ-idem = RT.⊓-idem

  ⊤ᴿ-unit : (a : Reg) → (a ⊓ᴿ ⊤ᴿ) ≡ a
  ⊤ᴿ-unit = RT.⊤-unit

  ⊤ᴿ-greatest : (a : Reg) → a ≤ᴿ ⊤ᴿ
  ⊤ᴿ-greatest = RT.⊤-greatest

  ⇒ᴿ-curry : (a b c : Reg) → (a ⊓ᴿ b) ≤ᴿ c → a ≤ᴿ (b ⇒ᴿ c)
  ⇒ᴿ-curry = RT.⇒-curry

  ⇒ᴿ-uncurry : (a b c : Reg) → a ≤ᴿ (b ⇒ᴿ c) → (a ⊓ᴿ b) ≤ᴿ c
  ⇒ᴿ-uncurry = RT.⇒-uncurry

  ⇒ᴿ-def : (a b : Reg) → (a ⇒ᴿ b) ≡ ((¬ᴿ a) ⊔ᴿ b)
  ⇒ᴿ-def = RT.⇒-def

  -- Host completeness, as four universal properties. THIS is the whole
  -- economy of the reference semantics and it is exactly what the coded algebra
  -- does not have: `⋁ᴿ` and `⋀ᴿ` are the supremum and infimum of EVERY host
  -- family, with no code, no bound and no admission (Algebra.agda:116-121, and
  -- the file's own warning never to assert it of a coded algebra).

  ⋁ᴿ-ub : (A : Type ℓ) (f : A → Reg) (a : A) → (f a) ≤ᴿ (⋁ᴿ A f)
  ⋁ᴿ-ub A f = fst (⋁-sup A f)

  ⋁ᴿ-lub : (A : Type ℓ) (f : A → Reg) (c : Reg)
         → ((a : A) → (f a) ≤ᴿ c) → (⋁ᴿ A f) ≤ᴿ c
  ⋁ᴿ-lub A f = snd (⋁-sup A f)

  ⋀ᴿ-lb : (A : Type ℓ) (f : A → Reg) (a : A) → (⋀ᴿ A f) ≤ᴿ (f a)
  ⋀ᴿ-lb A f = fst (⋀-inf A f)

  ⋀ᴿ-glb : (A : Type ℓ) (f : A → Reg) (c : Reg)
         → ((a : A) → c ≤ᴿ (f a)) → c ≤ᴿ (⋀ᴿ A f)
  ⋀ᴿ-glb A f = snd (⋀-inf A f)

  -- A meet over a disjoint union splits. It is one antisymmetry and it is free
  -- on the host side for the same reason everything else here is free. Part two
  -- spends it at exactly one place, and that place is the measured finding of
  -- this track: the coded equality value is a greatest lower bound over TWO
  -- supports at once, so its transport is not an instance of the
  -- architecture's `infᴮ X h` shape.

  ⋀ᴿ-⊎ : (I J : Type ℓ) (f : (I ⊎ J) → Reg)
       → (⋀ᴿ (I ⊎ J) f)
       ≡ ((⋀ᴿ I (λ i → f (inl i))) ⊓ᴿ (⋀ᴿ J (λ j → f (inr j))))
  ⋀ᴿ-⊎ I J f = ≤ᴿ-antisym (⋀ᴿ (I ⊎ J) f) (lft ⊓ᴿ rgt) fwd bwd
    where
      lft rgt : Reg
      lft = ⋀ᴿ I (λ i → f (inl i))
      rgt = ⋀ᴿ J (λ j → f (inr j))

      fwd : (⋀ᴿ (I ⊎ J) f) ≤ᴿ (lft ⊓ᴿ rgt)
      fwd = ⊓ᴿ-glb lft rgt (⋀ᴿ (I ⊎ J) f)
              (⋀ᴿ-glb I (λ i → f (inl i)) (⋀ᴿ (I ⊎ J) f)
                (λ i → ⋀ᴿ-lb (I ⊎ J) f (inl i)))
              (⋀ᴿ-glb J (λ j → f (inr j)) (⋀ᴿ (I ⊎ J) f)
                (λ j → ⋀ᴿ-lb (I ⊎ J) f (inr j)))

      branch : (c : I ⊎ J) → (lft ⊓ᴿ rgt) ≤ᴿ (f c)
      branch (inl i) =
        ≤ᴿ-trans (lft ⊓ᴿ rgt) lft (f (inl i))
          (⊓ᴿ-lb₁ lft rgt) (⋀ᴿ-lb I (λ k → f (inl k)) i)
      branch (inr j) =
        ≤ᴿ-trans (lft ⊓ᴿ rgt) rgt (f (inr j))
          (⊓ᴿ-lb₂ lft rgt) (⋀ᴿ-lb J (λ k → f (inr k)) j)

      bwd : (lft ⊓ᴿ rgt) ≤ᴿ (⋀ᴿ (I ⊎ J) f)
      bwd = ⋀ᴿ-glb (I ⊎ J) f (lft ⊓ᴿ rgt) branch

  -- A meet of the constant top is the top, with no inhabitant of the index
  -- required. Bell's 1.17(i) at a name with empty support is exactly this case
  -- and it is the one place where an empty family has to be handled correctly;
  -- Track A measured what happens when an empty family is handled incorrectly
  -- (K4/Infinitary.agda:238-271, the refutation of the architecture's printed
  -- `inf-residual`).

  ⋀ᴿ-const-⊤ : (A : Type ℓ) → (⋀ᴿ A (λ _ → ⊤ᴿ)) ≡ ⊤ᴿ
  ⋀ᴿ-const-⊤ A = ≤ᴿ-antisym (⋀ᴿ A (λ _ → ⊤ᴿ)) ⊤ᴿ
    (⊤ᴿ-greatest (⋀ᴿ A (λ _ → ⊤ᴿ)))
    (⋀ᴿ-glb A (λ _ → ⊤ᴿ) ⊤ᴿ (λ _ → ≤ᴿ-refl ⊤ᴿ))

  -- An implication with a true antecedent to consequent step is the top. The
  -- two directions of the adjunction are the whole proof.

  ⇒ᴿ-≤-⊤ : (a b : Reg) → a ≤ᴿ b → (a ⇒ᴿ b) ≡ ⊤ᴿ
  ⇒ᴿ-≤-⊤ a b h = ≤ᴿ-antisym (a ⇒ᴿ b) ⊤ᴿ (⊤ᴿ-greatest (a ⇒ᴿ b))
    (⇒ᴿ-curry ⊤ᴿ a b (≤ᴿ-trans (⊤ᴿ ⊓ᴿ a) a b (⊓ᴿ-lb₂ ⊤ᴿ a) h))

  ------------------------------------------------------------------------------
  -- 1.1 The index of a family over a support
  ------------------------------------------------------------------------------

  -- The index is a sigma over a MEMBERSHIP PROPOSITION, which is R4's shape and
  -- also, here, the reason the whole construction fits: `Pt (support n)` is
  -- `Type ℓ`, so it fills the index slot of `⋀ᴿ` and `⋁ᴿ` exactly, with zero
  -- margin. Nothing in this file ever indexes a join by a proof or by a record
  -- carrying a path in `Ω`.

  Supᴺ : S → Type ℓ
  Supᴺ n = Pt (support n)

  edge : (n : S) (p : Supᴺ n) → Child (fst p) n
  edge n p = support-out n (fst p) (snd p)

  ------------------------------------------------------------------------------
  -- 1.2 The two atomic values
  ------------------------------------------------------------------------------

  -- The expanded symmetric equation, Track C's `stepᴮ` (K4/Atomic.agda:322-336)
  -- with `meetOf`/`joinOf` replaced by the host `⋀ᴿ`/`⋁ᴿ`. Both conjuncts call
  -- the recursive value at (first coordinate from m, second coordinate from n),
  -- in that order. Writing the second conjunct with the arguments exchanged, as
  -- Bell's printed (1.16) has them, is not a legal recursive call at all:
  -- `RawPairRec`'s step supplies the value only where BOTH coordinates descend
  -- (NameKernel.agda:414-416), while Bell's own relation holds one coordinate
  -- fixed (fulltext:2026). K0 warns against precisely this at
  -- k0-name-pair-weighted-images-2026-09.md:17.

  stepᴿ : (m n : S)
        → ((u v : S) → Child u m → Child v n → Reg) → Reg
  stepᴿ m n r =
    (⋀ᴿ (Supᴺ m)
      (λ p → (wtᴿ m (fst p)) ⇒ᴿ
             (⋁ᴿ (Supᴺ n)
               (λ q → (wtᴿ n (fst q)) ⊓ᴿ
                      (r (fst p) (fst q) (edge m p) (edge n q))))))
    ⊓ᴿ
    (⋀ᴿ (Supᴺ n)
      (λ q → (wtᴿ n (fst q)) ⇒ᴿ
             (⋁ᴿ (Supᴺ m)
               (λ p → (wtᴿ m (fst p)) ⊓ᴿ
                      (r (fst p) (fst q) (edge m p) (edge n q))))))

  infix 20 _≈ᴿ_ _∈ᴿ_ _∈ᴿᵒ_

  _≈ᴿ_ : S → S → Reg
  _≈ᴿ_ = rawPairRec (λ _ _ → Reg) stepᴿ

  -- Membership is DEFINED from equality and is never mutually recursive with
  -- it. This is Bell (1.15) taken as a definition, K0's dependency order
  -- (k0-material-names-value-sets:34), and Track C's; `Valuation.agda:291-295`
  -- is the precedent on the Ω valued side.

  _∈ᴿ_ : S → S → Reg
  m ∈ᴿ n = ⋁ᴿ (Supᴺ n) (λ q → (wtᴿ n (fst q)) ⊓ᴿ (m ≈ᴿ (fst q)))

  -- The MIRRORED membership value, the inner join of the second conjunct. It
  -- differs from `_∈ᴿ_` only in the order of the two arguments of the recursive
  -- call, and it is a separate definition rather than a use of `_∈ᴿ_` because
  -- the two are equal only after symmetry. Identifying them at definition time
  -- would be a well typed false step.

  _∈ᴿᵒ_ : S → S → Reg
  y ∈ᴿᵒ m = ⋁ᴿ (Supᴺ m) (λ p → (wtᴿ m (fst p)) ⊓ᴿ ((fst p) ≈ᴿ y))

  famLᴿ : (m n : S) → Supᴺ m → Reg
  famLᴿ m n p = (wtᴿ m (fst p)) ⇒ᴿ ((fst p) ∈ᴿ n)

  famRᴿ : (m n : S) → Supᴺ n → Reg
  famRᴿ m n q = (wtᴿ n (fst q)) ⇒ᴿ ((fst q) ∈ᴿᵒ m)

  leftᴿ : (m n : S) → Reg
  leftᴿ m n = ⋀ᴿ (Supᴺ m) (famLᴿ m n)

  rightᴿ : (m n : S) → Reg
  rightᴿ m n = ⋀ᴿ (Supᴺ n) (famRᴿ m n)

  -- THE UNFOLDING. The computation law of a well founded recursion is
  -- propositional and never definitional, so this path is the only way into the
  -- value, and every characterization below transports through it exactly once.
  -- After section 1.5 it is never used again.

  ≈ᴿ-step : (m n : S) → (m ≈ᴿ n) ≡ ((leftᴿ m n) ⊓ᴿ (rightᴿ m n))
  ≈ᴿ-step = rawPairComp (λ _ _ → Reg) stepᴿ

  ------------------------------------------------------------------------------
  -- 1.3 The universal properties, free from host completeness
  ------------------------------------------------------------------------------

  ∈ᴿ-ub : (m n x : S) → ⟨ x ∈ˢ support n ⟩
        → ((wtᴿ n x) ⊓ᴿ (m ≈ᴿ x)) ≤ᴿ (m ∈ᴿ n)
  ∈ᴿ-ub m n x h =
    ⋁ᴿ-ub (Supᴺ n) (λ q → (wtᴿ n (fst q)) ⊓ᴿ (m ≈ᴿ (fst q))) (x , h)

  ∈ᴿ-lub : (m n : S) (c : Reg)
         → ((x : S) → ⟨ x ∈ˢ support n ⟩ → ((wtᴿ n x) ⊓ᴿ (m ≈ᴿ x)) ≤ᴿ c)
         → (m ∈ᴿ n) ≤ᴿ c
  ∈ᴿ-lub m n c hyp =
    ⋁ᴿ-lub (Supᴺ n) (λ q → (wtᴿ n (fst q)) ⊓ᴿ (m ≈ᴿ (fst q))) c
      (λ q → hyp (fst q) (snd q))

  ∈ᴿᵒ-ub : (y m x : S) → ⟨ x ∈ˢ support m ⟩
         → ((wtᴿ m x) ⊓ᴿ (x ≈ᴿ y)) ≤ᴿ (y ∈ᴿᵒ m)
  ∈ᴿᵒ-ub y m x h =
    ⋁ᴿ-ub (Supᴺ m) (λ p → (wtᴿ m (fst p)) ⊓ᴿ ((fst p) ≈ᴿ y)) (x , h)

  ∈ᴿᵒ-lub : (y m : S) (c : Reg)
          → ((x : S) → ⟨ x ∈ˢ support m ⟩ → ((wtᴿ m x) ⊓ᴿ (x ≈ᴿ y)) ≤ᴿ c)
          → (y ∈ᴿᵒ m) ≤ᴿ c
  ∈ᴿᵒ-lub y m c hyp =
    ⋁ᴿ-lub (Supᴺ m) (λ p → (wtᴿ m (fst p)) ⊓ᴿ ((fst p) ≈ᴿ y)) c
      (λ p → hyp (fst p) (snd p))

  ≈ᴿ-lbˡ : (m n x : S) → ⟨ x ∈ˢ support m ⟩
         → (m ≈ᴿ n) ≤ᴿ ((wtᴿ m x) ⇒ᴿ (x ∈ᴿ n))
  ≈ᴿ-lbˡ m n x h =
    subst (λ w → w ≤ᴿ ((wtᴿ m x) ⇒ᴿ (x ∈ᴿ n))) (sym (≈ᴿ-step m n))
      (≤ᴿ-trans ((leftᴿ m n) ⊓ᴿ (rightᴿ m n)) (leftᴿ m n)
                ((wtᴿ m x) ⇒ᴿ (x ∈ᴿ n))
        (⊓ᴿ-lb₁ (leftᴿ m n) (rightᴿ m n))
        (⋀ᴿ-lb (Supᴺ m) (famLᴿ m n) (x , h)))

  ≈ᴿ-lbʳ-raw : (m n y : S) → ⟨ y ∈ˢ support n ⟩
             → (m ≈ᴿ n) ≤ᴿ ((wtᴿ n y) ⇒ᴿ (y ∈ᴿᵒ m))
  ≈ᴿ-lbʳ-raw m n y h =
    subst (λ w → w ≤ᴿ ((wtᴿ n y) ⇒ᴿ (y ∈ᴿᵒ m))) (sym (≈ᴿ-step m n))
      (≤ᴿ-trans ((leftᴿ m n) ⊓ᴿ (rightᴿ m n)) (rightᴿ m n)
                ((wtᴿ n y) ⇒ᴿ (y ∈ᴿᵒ m))
        (⊓ᴿ-lb₂ (leftᴿ m n) (rightᴿ m n))
        (⋀ᴿ-lb (Supᴺ n) (famRᴿ m n) (y , h)))

  ≈ᴿ-glb-raw : (m n : S) (c : Reg)
             → ((x : S) → ⟨ x ∈ˢ support m ⟩
                → c ≤ᴿ ((wtᴿ m x) ⇒ᴿ (x ∈ᴿ n)))
             → ((y : S) → ⟨ y ∈ˢ support n ⟩
                → c ≤ᴿ ((wtᴿ n y) ⇒ᴿ (y ∈ᴿᵒ m)))
             → c ≤ᴿ (m ≈ᴿ n)
  ≈ᴿ-glb-raw m n c h₁ h₂ =
    subst (λ w → c ≤ᴿ w) (sym (≈ᴿ-step m n))
      (⊓ᴿ-glb (leftᴿ m n) (rightᴿ m n) c
        (⋀ᴿ-glb (Supᴺ m) (famLᴿ m n) c (λ p → h₁ (fst p) (snd p)))
        (⋀ᴿ-glb (Supᴺ n) (famRᴿ m n) c (λ q → h₂ (fst q) (snd q))))

  ------------------------------------------------------------------------------
  -- 1.4 Symmetry, Bell 1.17(iii), and with it Bell (1.16) in its printed form
  ------------------------------------------------------------------------------

  -- Track C measured that symmetry needs no infinitary law, only commutativity
  -- of the binary meet, because under the expanded symmetric equation the two
  -- halves of the value at (m, n) are the two halves of the value at (n, m) in
  -- the other order, with the recursive calls exchanged. The inductive
  -- hypothesis therefore rewrites each family POINTWISE, and a pointwise
  -- equality under a fixed operation is a `cong` and not a congruence law about
  -- the operation. That argument is a statement about the SHAPE of the equation
  -- and not about the algebra, so it ports here without change and without the
  -- host's distributivity, which this file does have and does not use.

  mirrorᴿ : (m n : S)
          → ((u v : S) → Child u m → Child v n → (u ≈ᴿ v) ≡ (v ≈ᴿ u))
          → (x : S) → Child x m → (x ∈ᴿ n) ≡ (x ∈ᴿᵒ n)
  mirrorᴿ m n ih x e =
    cong (⋁ᴿ (Supᴺ n))
      (funExt (λ q → cong (λ z → (wtᴿ n (fst q)) ⊓ᴿ z)
                          (ih x (fst q) e (edge n q))))

  mirror⁻ᴿ : (m n : S)
           → ((u v : S) → Child u m → Child v n → (u ≈ᴿ v) ≡ (v ≈ᴿ u))
           → (y : S) → Child y n → (y ∈ᴿᵒ m) ≡ (y ∈ᴿ m)
  mirror⁻ᴿ m n ih y e =
    cong (⋁ᴿ (Supᴺ m))
      (funExt (λ p → cong (λ z → (wtᴿ m (fst p)) ⊓ᴿ z)
                          (ih (fst p) y (edge m p) e)))

  symStepᴿ : (m n : S)
           → ((u v : S) → Child u m → Child v n → (u ≈ᴿ v) ≡ (v ≈ᴿ u))
           → (m ≈ᴿ n) ≡ (n ≈ᴿ m)
  symStepᴿ m n ih =
      ≈ᴿ-step m n
    ∙ cong (λ z → z ⊓ᴿ (rightᴿ m n)) eqLeft
    ∙ cong (λ z → (rightᴿ n m) ⊓ᴿ z) eqRight
    ∙ ⊓ᴿ-comm (rightᴿ n m) (leftᴿ n m)
    ∙ sym (≈ᴿ-step n m)
    where
      eqLeft : leftᴿ m n ≡ rightᴿ n m
      eqLeft =
        cong (⋀ᴿ (Supᴺ m))
          (funExt (λ p → cong (λ z → (wtᴿ m (fst p)) ⇒ᴿ z)
                              (mirrorᴿ m n ih (fst p) (edge m p))))

      eqRight : rightᴿ m n ≡ leftᴿ n m
      eqRight =
        cong (⋀ᴿ (Supᴺ n))
          (funExt (λ q → cong (λ z → (wtᴿ n (fst q)) ⇒ᴿ z)
                              (mirror⁻ᴿ m n ih (fst q) (edge n q))))

  ≈ᴿ-sym : (m n : S) → (m ≈ᴿ n) ≡ (n ≈ᴿ m)
  ≈ᴿ-sym = rawPairRec (λ m n → (m ≈ᴿ n) ≡ (n ≈ᴿ m)) symStepᴿ

  ∈ᴿᵒ≡∈ᴿ : (y m : S) → (y ∈ᴿᵒ m) ≡ (y ∈ᴿ m)
  ∈ᴿᵒ≡∈ᴿ y m =
    cong (⋁ᴿ (Supᴺ m))
      (funExt (λ p → cong (λ z → (wtᴿ m (fst p)) ⊓ᴿ z) (≈ᴿ-sym (fst p) y)))

  ------------------------------------------------------------------------------
  -- 1.5 The printed form of Bell (1.16)
  ------------------------------------------------------------------------------

  -- The second conjunct with the mirror collapsed. This is the shape that Track
  -- C's `AtomicSemantics` uses on the coded side (`eqᴬ-lbʳ` speaks of
  -- `memᴬ y m`, not of a mirrored value), so the agreement of part two compares
  -- like with like only after this step.
  --
  -- Note what this equation is and is not. On the host side the atomic value IS
  -- an equation naming a construction, because the host algebra is complete for
  -- every host family and the construction is total. R3 forbids that shape on
  -- the CODED side and the architecture's decision to use universal properties
  -- there stands; here there is no such constraint and the equation is the
  -- honest statement.

  famR′ᴿ : (m n : S) → Supᴺ n → Reg
  famR′ᴿ m n q = (wtᴿ n (fst q)) ⇒ᴿ ((fst q) ∈ᴿ m)

  right′ᴿ : (m n : S) → Reg
  right′ᴿ m n = ⋀ᴿ (Supᴺ n) (famR′ᴿ m n)

  rightᴿ≡right′ᴿ : (m n : S) → rightᴿ m n ≡ right′ᴿ m n
  rightᴿ≡right′ᴿ m n =
    cong (⋀ᴿ (Supᴺ n))
      (funExt (λ q → cong (λ z → (wtᴿ n (fst q)) ⇒ᴿ z) (∈ᴿᵒ≡∈ᴿ (fst q) m)))

  ≈ᴿ-step′ : (m n : S) → (m ≈ᴿ n) ≡ ((leftᴿ m n) ⊓ᴿ (right′ᴿ m n))
  ≈ᴿ-step′ m n =
    ≈ᴿ-step m n ∙ cong (λ z → (leftᴿ m n) ⊓ᴿ z) (rightᴿ≡right′ᴿ m n)

  ≈ᴿ-lbʳ : (m n y : S) → ⟨ y ∈ˢ support n ⟩
         → (m ≈ᴿ n) ≤ᴿ ((wtᴿ n y) ⇒ᴿ (y ∈ᴿ m))
  ≈ᴿ-lbʳ m n y h =
    subst (λ w → (m ≈ᴿ n) ≤ᴿ ((wtᴿ n y) ⇒ᴿ w)) (∈ᴿᵒ≡∈ᴿ y m)
      (≈ᴿ-lbʳ-raw m n y h)

  ≈ᴿ-glb : (m n : S) (c : Reg)
         → ((x : S) → ⟨ x ∈ˢ support m ⟩ → c ≤ᴿ ((wtᴿ m x) ⇒ᴿ (x ∈ᴿ n)))
         → ((y : S) → ⟨ y ∈ˢ support n ⟩ → c ≤ᴿ ((wtᴿ n y) ⇒ᴿ (y ∈ᴿ m)))
         → c ≤ᴿ (m ≈ᴿ n)
  ≈ᴿ-glb m n c h₁ h₂ =
    ≈ᴿ-glb-raw m n c h₁
      (λ y hy → subst (λ w → c ≤ᴿ ((wtᴿ n y) ⇒ᴿ w)) (sym (∈ᴿᵒ≡∈ᴿ y m))
                  (h₂ y hy))

  ------------------------------------------------------------------------------
  -- 1.6 Bell 1.17(i) and (ii) on the host side
  ------------------------------------------------------------------------------

  -- Reflexivity and the weight bound are Bell's (1.17)(i) and (ii) and they are
  -- proved together, by ONE single coordinate induction, exactly as Bell proves
  -- them (fulltext:2100-2103). The step needs no property of the weight at all:
  -- the weight is placed, never read.

  weight-under : (n x : S) (h : ⟨ x ∈ˢ support n ⟩)
           → (x ≈ᴿ x) ≡ ⊤ᴿ → (wtᴿ n x) ≤ᴿ (x ∈ᴿ n)
  weight-under n x h e =
    subst (λ w → w ≤ᴿ (x ∈ᴿ n))
      (cong (λ z → (wtᴿ n x) ⊓ᴿ z) e ∙ ⊤ᴿ-unit (wtᴿ n x))
      (∈ᴿ-ub x n x h)

  weight-underᵒ : (n x : S) (h : ⟨ x ∈ˢ support n ⟩)
            → (x ≈ᴿ x) ≡ ⊤ᴿ → (wtᴿ n x) ≤ᴿ (x ∈ᴿᵒ n)
  weight-underᵒ n x h e =
    subst (λ w → w ≤ᴿ (x ∈ᴿᵒ n))
      (cong (λ z → (wtᴿ n x) ⊓ᴿ z) e ∙ ⊤ᴿ-unit (wtᴿ n x))
      (∈ᴿᵒ-ub x n x h)

  reflStepᴿ : (n : S) → ((x : S) → Child x n → (x ≈ᴿ x) ≡ ⊤ᴿ)
            → (n ≈ᴿ n) ≡ ⊤ᴿ
  reflStepᴿ n ih =
      ≈ᴿ-step n n
    ∙ cong (λ z → z ⊓ᴿ (rightᴿ n n)) eqL
    ∙ cong (λ z → ⊤ᴿ ⊓ᴿ z) eqR
    ∙ ⊓ᴿ-idem ⊤ᴿ
    where
      eqL : leftᴿ n n ≡ ⊤ᴿ
      eqL =
          cong (⋀ᴿ (Supᴺ n))
            (funExt (λ p → ⇒ᴿ-≤-⊤ (wtᴿ n (fst p)) ((fst p) ∈ᴿ n)
                             (weight-under n (fst p) (snd p)
                               (ih (fst p) (edge n p)))))
        ∙ ⋀ᴿ-const-⊤ (Supᴺ n)

      eqR : rightᴿ n n ≡ ⊤ᴿ
      eqR =
          cong (⋀ᴿ (Supᴺ n))
            (funExt (λ q → ⇒ᴿ-≤-⊤ (wtᴿ n (fst q)) ((fst q) ∈ᴿᵒ n)
                             (weight-underᵒ n (fst q) (snd q)
                               (ih (fst q) (edge n q)))))
        ∙ ⋀ᴿ-const-⊤ (Supᴺ n)

  ≈ᴿ-refl : (n : S) → (n ≈ᴿ n) ≡ ⊤ᴿ
  ≈ᴿ-refl = rawRec (λ n → (n ≈ᴿ n) ≡ ⊤ᴿ) reflStepᴿ

  weight-≤ᴿ : (n x : S) → ⟨ x ∈ˢ support n ⟩ → (wtᴿ n x) ≤ᴿ (x ∈ᴿ n)
  weight-≤ᴿ n x h = weight-under n x h (≈ᴿ-refl x)

  ------------------------------------------------------------------------------
  -- 1.7 The structure over the host algebra, and the ten clauses
  ------------------------------------------------------------------------------

  -- THE PAYOFF. `ZFStructure` asks for a carrier at `Type ℓ`, a proof that it
  -- is a set, and two `Ω` valued relations (src/FOL/ZFStructure.lagda.md:60-67).
  -- The host algebra's `Ω` is `Reg : Type (ℓ-suc ℓ)` and `Name : Type ℓ`, so
  -- the record is inhabited with no level arithmetic and the whole of
  -- `FOL.Semantics` follows. Nothing is asserted about this structure: no
  -- axiom, no extensionality, no well foundedness. It is the bare structure,
  -- which is all the satisfaction relation consumes.

  Name : Type ℓ
  Name = Σ[ n ∈ S ] ⟨ IsName n ⟩

  isSetName : isSet Name
  isSetName = isSetΣSndProp isSetS (λ n → snd (IsName n))

  𝒱 : ZFStructure 𝕋ᴿ
  𝒱 = record
    { S      = Name
    ; isSetS = isSetName
    ; _≈ˢ_   = λ τ σ → (fst τ) ≈ᴿ (fst σ)
    ; _∈ˢ_   = λ τ σ → (fst τ) ∈ᴿ (fst σ) }

  module HostSem = FOL.Semantics 𝕋ᴿ 𝒱

  -- The constant domain is the EMPTY type, matching Track F's input syntax
  -- `Src k = Formula (⊥* {ℓ}) k`. That is the book's own convention and its
  -- reason (src/FOL/Syntax.lagda.md:134-160): a syntax whose constants are all
  -- sets is too big to be collected, so formulas used as data are the parameter
  -- free ones and their parameters travel in the environment. Here it means the
  -- two evaluators read the SAME formula, with no translation layer between
  -- them, which is what makes the agreement statable at all.

  module HAt = HostSem.At (⊥* {ℓ}) Empty.rec*

  Src : ℕ → Type ℓ
  Src k = Formula (⊥* {ℓ}) k

  Env : ℕ → Type ℓ
  Env k = Vec Name k

  infix 6 _⊫_

  _⊫_ : ∀ {k} → Env k → Src k → Reg
  _⊫_ = HAt._⊨_

  -- THE READINGS OF THIS TRACK, written before anything is proved about them
  -- and broken once in `K4/ProbeJN.agda`. There are two, they hold by `refl`,
  -- and a reflexivity proof is worthless unless the two sides can be made to
  -- disagree, so both are deliberately falsified there and the exact errors
  -- recorded. The remaining eight clauses of `_⊫_` are equations of
  -- `FOL.Semantics` itself and are not restated.

  ⊫-∈ : ∀ {k} (i j : Fin k) (ν : Env k)
      → (ν ⊫ (var i ∈̇ var j)) ≡ ((fst (lookup i ν)) ∈ᴿ (fst (lookup j ν)))
  ⊫-∈ i j ν = refl

  ⊫-≐ : ∀ {k} (i j : Fin k) (ν : Env k)
      → (ν ⊫ (var i ≐ var j)) ≡ ((fst (lookup i ν)) ≈ᴿ (fst (lookup j ν)))
  ⊫-≐ i j ν = refl

  ⊫-∧ : ∀ {k} (φ ψ : Src k) (ν : Env k)
      → (ν ⊫ (φ ∧̇ ψ)) ≡ ((ν ⊫ φ) ⊓ᴿ (ν ⊫ ψ))
  ⊫-∧ φ ψ ν = refl

  ⊫-∃ : ∀ {k} (φ : Src (suc k)) (ν : Env k)
      → (ν ⊫ (∃̇ φ)) ≡ (⋁ᴿ Name (λ τ → (τ ∷ ν) ⊫ φ))
  ⊫-∃ φ ν = refl

  ⊫-∀ : ∀ {k} (φ : Src (suc k)) (ν : Env k)
      → (ν ⊫ (∀̇ φ)) ≡ (⋀ᴿ Name (λ τ → (τ ∷ ν) ⊫ φ))
  ⊫-∀ φ ν = refl

--------------------------------------------------------------------------------
-- 2. The coded algebra, and the reading map
--------------------------------------------------------------------------------

  -- From here on the file mentions both carriers, and it is the only K4 file
  -- permitted to. The coded algebra enters as Track A's three records in the
  -- uniform telescope; the weight enters as a bare operation with no law, for
  -- the same measured reason Tracks C and D give (nothing reads a weight, it is
  -- only placed).
  --
  -- `CodedComplete` is carried for exactly two lemmas, section 2.5's two
  -- bridges back to the architecture's own `supᴮ X h` spelling. Not one
  -- statement of the agreement names `supᴮ` or `infᴮ`, which is R3 discharged
  -- by construction rather than by care.

  module Coded
    (B  : S)
    (L  : Lattice B)
    (Cm : Complement B L)
    (Kc : CodedComplete B L)
    (weightᴮ : (n x : S) → Pt B)
    where

    open Lattice L
    open Complement Cm
    open CodedComplete Kc
    open K4.Implication 𝒮 ext paths B L Cm using ( _⇒ᴮ_ )

    ----------------------------------------------------------------------------
    -- 2.1 Admission, as a universal property and nothing else
    ----------------------------------------------------------------------------

    -- THE FORM OF THE ADMISSION HYPOTHESIS, and this is where this track parts
    -- company with the architecture's printed `reads-sup`/`reads-inf`.
    --
    -- The architecture prints them as facts about `supᴮ X h` and `infᴮ X h`
    -- (section 1.11, and obstruction O2). Those are facts about a CONSTRUCTION.
    -- Stated that way they are (a) the shape project rule 3 forbids in a
    -- signature and (b) too weak for the induction below, which is a measured
    -- fact and not an aesthetic preference; section 2.5 proves the one
    -- implication that does hold between the two forms.
    --
    -- Stated here as a universal property instead: a family of coded values has
    -- a coded least upper bound, and the hypothesis says the READING of that
    -- bound is the host least upper bound of the read family. That is the
    -- roadmap's own sentence, "agreement with the host evaluator is CONDITIONAL
    -- ON BOTH ADMITTING THE RELEVANT FAMILIES" (roadmap:193), in the one form
    -- the induction consumes: `IsLubᴮ f c` is the coded side admitting the
    -- family, and the conclusion is that the host side agrees with it.

    IsLubᴮ : {I : Type ℓ} → (I → Pt B) → Pt B → Type ℓ
    IsLubᴮ {I} f c = ((i : I) → ⟨ (f i) ≤ᴮ c ⟩)
                   × ((d : Pt B) → ((i : I) → ⟨ (f i) ≤ᴮ d ⟩) → ⟨ c ≤ᴮ d ⟩)

    IsGlbᴮ : {I : Type ℓ} → (I → Pt B) → Pt B → Type ℓ
    IsGlbᴮ {I} f c = ((i : I) → ⟨ c ≤ᴮ (f i) ⟩)
                   × ((d : Pt B) → ((i : I) → ⟨ d ≤ᴮ (f i) ⟩) → ⟨ d ≤ᴮ c ⟩)

    ----------------------------------------------------------------------------
    -- 2.2 The reading map and the agreement predicate
    ----------------------------------------------------------------------------

    -- The reading enters flat, as `reads` with its injectivity and the FIVE
    -- finite preservation lemmas and the two order lemmas, which is exactly
    -- what `CodedCompletion.agda:1226-1269` proves and exactly what it does not.
    --
    -- R6, THE SINGLE MOST LIKELY SILENT FAILURE IN K4.9. `reads` preserves only
    -- the FINITE operations. `grep -c "reads-sup\|reads-inf\|reads-⋁\|reads-⋀"
    -- /tmp/bedrock-k3-probes/CodedCompletion.agda` returns 0, re-run for this
    -- file. There is therefore no infinitary preservation lemma to take flat,
    -- and transporting one silently is the failure mode; the two hypotheses of
    -- section 2.1 are the only route and they are arguments of every theorem
    -- that uses them, never module parameters.
    --
    -- `wt-agrees` is the one line that ties the host weight of part one to the
    -- coded weight. It is a hypothesis rather than a definition so that part
    -- one stays visibly independent of the coded algebra; a caller who sets
    -- `wtᴿ := λ n x → reads (weightᴮ n x)` discharges it by `refl`.

    module Agreement
      (_⊑ᴿ_ : Reg → Reg → Type ℓ)
      (isProp⊑ᴿ : (U V : Reg) → isProp (U ⊑ᴿ V))
      (⊑ᴿ→≤ᴿ : (U V : Reg) → U ⊑ᴿ V → U ≤ᴿ V)
      (≤ᴿ→⊑ᴿ : (U V : Reg) → U ≤ᴿ V → U ⊑ᴿ V)
      (reads : Pt B → Reg)
      (reads-inj : (u v : Pt B) → reads u ≡ reads v → u ≡ v)
      (reads-⊤ : reads ⊤ᴮ ≡ ⊤ᴿ)
      (reads-⊥ : reads ⊥ᴮ ≡ ⊥ᴿ)
      (reads-⊓ : (u v : Pt B) → reads (u ⊓ᴮ v) ≡ ((reads u) ⊓ᴿ (reads v)))
      (reads-¬ : (u : Pt B) → reads (¬ᴮ u) ≡ (¬ᴿ (reads u)))
      (reads-⊔ : (u v : Pt B) → reads (u ⊔ᴮ v) ≡ ((reads u) ⊔ᴿ (reads v)))
      (reads-≤→ : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → (reads u) ⊑ᴿ (reads v))
      (reads-≤← : (u v : Pt B) → (reads u) ⊑ᴿ (reads v) → ⟨ u ≤ᴮ v ⟩)
      (wt-agrees : (n x : S) → reads (weightᴮ n x) ≡ wtᴿ n x)
      (eqᴬ memᴬ : S → S → Pt B)
      (memᴬ-ub  : (m n x : S) → ⟨ x ∈ˢ support n ⟩
                → ⟨ ((weightᴮ n x) ⊓ᴮ (eqᴬ m x)) ≤ᴮ (memᴬ m n) ⟩)
      (memᴬ-lub : (m n : S) (c : Pt B)
                → ((x : S) → ⟨ x ∈ˢ support n ⟩
                   → ⟨ ((weightᴮ n x) ⊓ᴮ (eqᴬ m x)) ≤ᴮ c ⟩)
                → ⟨ (memᴬ m n) ≤ᴮ c ⟩)
      (eqᴬ-lbˡ  : (m n x : S) → ⟨ x ∈ˢ support m ⟩
                → ⟨ (eqᴬ m n) ≤ᴮ ((weightᴮ m x) ⇒ᴮ (memᴬ x n)) ⟩)
      (eqᴬ-lbʳ  : (m n y : S) → ⟨ y ∈ˢ support n ⟩
                → ⟨ (eqᴬ m n) ≤ᴮ ((weightᴮ n y) ⇒ᴮ (memᴬ y m)) ⟩)
      (eqᴬ-glb  : (m n : S) (c : Pt B)
                → ((x : S) → ⟨ x ∈ˢ support m ⟩
                   → ⟨ c ≤ᴮ ((weightᴮ m x) ⇒ᴮ (memᴬ x n)) ⟩)
                → ((y : S) → ⟨ y ∈ˢ support n ⟩
                   → ⟨ c ≤ᴮ ((weightᴮ n y) ⇒ᴮ (memᴬ y m)) ⟩)
                → ⟨ c ≤ᴮ (eqᴬ m n) ⟩)
      (eqᴬ-sym  : (m n : S) → eqᴬ m n ≡ eqᴬ n m)
      where

      ------------------------------------------------------------------------
      -- 2.3 R7, and the agreement predicate it forces
      ------------------------------------------------------------------------

      -- `Agrees u U` says that the coded value `u` and the host value `U` are
      -- the same value. It is NOT the path `reads u ≡ U`, and it cannot be: a
      -- path in `Reg` lives at `Type (ℓ-suc ℓ)` and is not the carrier of any
      -- truth value, while the two entailments live at `Type ℓ` and are
      -- propositions, so their pair IS a truth value. That is the universe
      -- ledger's rule 2 (architecture section 1.0) and it is about this track
      -- specifically.
      --
      -- The two forms are of course logically equivalent, which is what
      -- `agrees→≡` and `≡→agrees` say. The point of the predicate is that the
      -- SMALL form can be quantified over, truncated, and placed inside a join,
      -- and the large one cannot. Nothing here needs to do that today; the
      -- predicate is shipped in the small form so that a later track which does
      -- need to is not forced to relitigate the level.

      Agrees : Pt B → Reg → Ω
      Agrees u U = (((reads u) ⊑ᴿ U) × (U ⊑ᴿ (reads u)))
                 , λ a b i → ( isProp⊑ᴿ (reads u) U (fst a) (fst b) i
                             , isProp⊑ᴿ U (reads u) (snd a) (snd b) i )

      Regᴿ≡ : (U V : Reg) → U ⊑ᴿ V → V ⊑ᴿ U → U ≡ V
      Regᴿ≡ U V h k = ≤ᴿ-antisym U V (⊑ᴿ→≤ᴿ U V h) (⊑ᴿ→≤ᴿ V U k)

      agrees→≡ : (u : Pt B) (U : Reg) → ⟨ Agrees u U ⟩ → reads u ≡ U
      agrees→≡ u U h = Regᴿ≡ (reads u) U (fst h) (snd h)

      ≡→agrees : (u : Pt B) (U : Reg) → reads u ≡ U → ⟨ Agrees u U ⟩
      ≡→agrees u U e =
          ≤ᴿ→⊑ᴿ (reads u) U
            (subst (λ w → (reads u) ≤ᴿ w) e (≤ᴿ-refl (reads u)))
        , ≤ᴿ→⊑ᴿ U (reads u)
            (subst (λ w → w ≤ᴿ (reads u)) e (≤ᴿ-refl (reads u)))

      -- Agreement determines the coded value. This is `reads-inj`'s only use in
      -- the file, and it is what makes the reference semantics a REFERENCE: a
      -- host value that agrees with a coded value pins that coded value, so a
      -- consumer can never obtain two different coded answers from one host
      -- answer. It cannot, however, be turned around: nothing here says that
      -- every host value is read by some coded one, and nothing here needs it.

      agrees-unique : (u v : Pt B) (U : Reg)
                    → ⟨ Agrees u U ⟩ → ⟨ Agrees v U ⟩ → u ≡ v
      agrees-unique u v U hu hv =
        reads-inj u v (agrees→≡ u U hu ∙ sym (agrees→≡ v U hv))

      ------------------------------------------------------------------------
      -- 2.4 What the finite preservation lemmas give
      ------------------------------------------------------------------------

      reads-≤ᴿ : (u v : Pt B) → ⟨ u ≤ᴮ v ⟩ → (reads u) ≤ᴿ (reads v)
      reads-≤ᴿ u v h = ⊑ᴿ→≤ᴿ (reads u) (reads v) (reads-≤→ u v h)

      -- The implication is preserved, and this is a derivation rather than a
      -- sixth hypothesis. Track A defines the coded implication as
      -- `u ⇒ᴮ v = (¬ᴮ u) ⊔ᴮ v` (K4/Implication.agda:309-310), and the host
      -- algebra's own implication is the Heyting one, so the two spellings are
      -- reconciled by `⇒-def` (Algebra.agda:284), which is a theorem of the
      -- Boolean laws and not an assumption about the host. So `reads-¬` and
      -- `reads-⊔` do the whole job and K2 owes nothing further.

      reads-⇒ : (u v : Pt B) → reads (u ⇒ᴮ v) ≡ ((reads u) ⇒ᴿ (reads v))
      reads-⇒ u v =
          reads-⊔ (¬ᴮ u) v
        ∙ cong (λ z → z ⊔ᴿ (reads v)) (reads-¬ u)
        ∙ sym (⇒ᴿ-def (reads u) (reads v))

      ------------------------------------------------------------------------
      -- 2.5 The two conditional hypotheses
      ------------------------------------------------------------------------

      ReadsSup : Type (ℓ-suc ℓ)
      ReadsSup = (I : Type ℓ) (f : I → Pt B) (c : Pt B) → IsLubᴮ f c
               → (reads c) ⊑ᴿ (⋁ᴿ I (λ i → reads (f i)))

      ReadsInf : Type (ℓ-suc ℓ)
      ReadsInf = (I : Type ℓ) (f : I → Pt B) (c : Pt B) → IsGlbᴮ f c
               → (⋀ᴿ I (λ i → reads (f i))) ⊑ᴿ (reads c)

      -- ONE DIRECTION OF EACH IS FREE, and saying which is the point. A coded
      -- upper bound reads to a host upper bound, because `reads` is monotone;
      -- so the host supremum of the read family is already below the reading of
      -- the coded supremum, with no hypothesis at all. What is NOT free, and
      -- what the two hypotheses above supply, is the other half: that the
      -- coded supremum does not read to something strictly larger, which is the
      -- statement that the coded algebra is a COMPLETE subalgebra of the host
      -- one for this family and not merely a subalgebra. Bell's Theorem 1.20
      -- and Corollary 1.21 are about exactly that distinction.

      sup-free : (I : Type ℓ) (f : I → Pt B) (c : Pt B)
               → ((i : I) → ⟨ (f i) ≤ᴮ c ⟩)
               → (⋁ᴿ I (λ i → reads (f i))) ≤ᴿ (reads c)
      sup-free I f c ub =
        ⋁ᴿ-lub I (λ i → reads (f i)) (reads c) (λ i → reads-≤ᴿ (f i) c (ub i))

      inf-free : (I : Type ℓ) (f : I → Pt B) (c : Pt B)
               → ((i : I) → ⟨ c ≤ᴮ (f i) ⟩)
               → (reads c) ≤ᴿ (⋀ᴿ I (λ i → reads (f i)))
      inf-free I f c lb =
        ⋀ᴿ-glb I (λ i → reads (f i)) (reads c) (λ i → reads-≤ᴿ c (f i) (lb i))

      reads-sup-≡ : ReadsSup → (I : Type ℓ) (f : I → Pt B) (c : Pt B)
                  → IsLubᴮ f c → reads c ≡ (⋁ᴿ I (λ i → reads (f i)))
      reads-sup-≡ rs I f c lub =
        ≤ᴿ-antisym (reads c) (⋁ᴿ I (λ i → reads (f i)))
          (⊑ᴿ→≤ᴿ (reads c) (⋁ᴿ I (λ i → reads (f i))) (rs I f c lub))
          (sup-free I f c (fst lub))

      reads-inf-≡ : ReadsInf → (I : Type ℓ) (f : I → Pt B) (c : Pt B)
                  → IsGlbᴮ f c → reads c ≡ (⋀ᴿ I (λ i → reads (f i)))
      reads-inf-≡ ri I f c glb =
        ≤ᴿ-antisym (reads c) (⋀ᴿ I (λ i → reads (f i)))
          (inf-free I f c (fst glb))
          (⊑ᴿ→≤ᴿ (⋀ᴿ I (λ i → reads (f i))) (reads c) (ri I f c glb))

      -- THE BRIDGE BACK TO THE ARCHITECTURE'S SPELLING, in the one direction
      -- that holds. A coded family realized as a ground code `X` inside the
      -- carrier is an `IsLubᴮ` at index `Pt X`, so the hypothesis above IMPLIES
      -- the architecture's `reads-sup`. The converse fails, and that is this
      -- track's measured correction: section 3's induction applies the meet
      -- hypothesis at the index `Supᴺ m ⊎ Supᴺ n`, which is not `Pt X` for any
      -- `X` this file has, and the compiler's quantifier nodes apply both at
      -- the index `Name`, which is not a `Pt X` either. So obstruction O2 as
      -- the architecture states it does NOT gate the agreement: a strictly
      -- stronger statement does, and Probe 1 should be re-scoped accordingly.

      ptIn : (X : S) → ⟨ X ⊆ˢ B ⟩ → Pt X → Pt B
      ptIn X h p = fst p , h (fst p) (snd p)

      supᴮ-lub : (X : S) (h : ⟨ X ⊆ˢ B ⟩) → IsLubᴮ (ptIn X h) (supᴮ X h)
      supᴮ-lub X h = (λ p → sup-ub X h (ptIn X h p) (snd p))
                   , (λ d hd → sup-lub X h d (λ u hu → hd (fst u , hu)))

      infᴮ-glb : (X : S) (h : ⟨ X ⊆ˢ B ⟩) → IsGlbᴮ (ptIn X h) (infᴮ X h)
      infᴮ-glb X h = (λ p → inf-lb X h (ptIn X h p) (snd p))
                   , (λ d hd → inf-glb X h d (λ u hu → hd (fst u , hu)))

      reads-supᴮ : ReadsSup → (X : S) (h : ⟨ X ⊆ˢ B ⟩)
                 → reads (supᴮ X h) ≡ (⋁ᴿ (Pt X) (λ p → reads (ptIn X h p)))
      reads-supᴮ rs X h =
        reads-sup-≡ rs (Pt X) (ptIn X h) (supᴮ X h) (supᴮ-lub X h)

      reads-infᴮ : ReadsInf → (X : S) (h : ⟨ X ⊆ˢ B ⟩)
                 → reads (infᴮ X h) ≡ (⋀ᴿ (Pt X) (λ p → reads (ptIn X h p)))
      reads-infᴮ ri X h =
        reads-inf-≡ ri (Pt X) (ptIn X h) (infᴮ X h) (infᴮ-glb X h)

--------------------------------------------------------------------------------
-- 3. The conditional atomic agreement
--------------------------------------------------------------------------------

      -- The coded membership value is a least upper bound over ONE support, so
      -- its transport is the architecture's own shape at index `Pt (support n)`.

      memLubᴮ : (m n : S)
              → IsLubᴮ {Supᴺ n}
                  (λ q → (weightᴮ n (fst q)) ⊓ᴮ (eqᴬ m (fst q))) (memᴬ m n)
      memLubᴮ m n = (λ q → memᴬ-ub m n (fst q) (snd q))
                  , (λ d hd → memᴬ-lub m n d (λ x hx → hd (x , hx)))

      -- The coded equality value is a greatest lower bound over TWO supports at
      -- once, and there is no intermediate value between them: Track C's
      -- `AtomicSemantics` exposes `eqᴬ` only through `eqᴬ-lbˡ`, `eqᴬ-lbʳ` and
      -- `eqᴬ-glb`, which together say exactly that `eqᴬ m n` is the greatest
      -- lower bound of this ONE family indexed by the disjoint union. The
      -- intermediate meet `leftᴮ ⊓ᴮ rightᴮ` lives inside Track C's opaque block
      -- and is not a field of the record. That is why the meet hypothesis is
      -- needed at a sum index and not at a `Pt X`, and it is a fact about the
      -- interface Track C ships, not about the mathematics.

      eqFamᴮ : (m n : S) → (Supᴺ m ⊎ Supᴺ n) → Pt B
      eqFamᴮ m n (inl p) = (weightᴮ m (fst p)) ⇒ᴮ (memᴬ (fst p) n)
      eqFamᴮ m n (inr q) = (weightᴮ n (fst q)) ⇒ᴮ (memᴬ (fst q) m)

      eqFamᴿ : (m n : S) → (Supᴺ m ⊎ Supᴺ n) → Reg
      eqFamᴿ m n (inl p) = famLᴿ m n p
      eqFamᴿ m n (inr q) = famR′ᴿ m n q

      eqGlbᴮ : (m n : S) → IsGlbᴮ (eqFamᴮ m n) (eqᴬ m n)
      eqGlbᴮ m n = lbs , great
        where
          lbs : (c : Supᴺ m ⊎ Supᴺ n) → ⟨ (eqᴬ m n) ≤ᴮ (eqFamᴮ m n c) ⟩
          lbs (inl p) = eqᴬ-lbˡ m n (fst p) (snd p)
          lbs (inr q) = eqᴬ-lbʳ m n (fst q) (snd q)

          great : (d : Pt B)
                → ((c : Supᴺ m ⊎ Supᴺ n) → ⟨ d ≤ᴮ (eqFamᴮ m n c) ⟩)
                → ⟨ d ≤ᴮ (eqᴬ m n) ⟩
          great d hd = eqᴬ-glb m n d
            (λ x hx → hd (inl (x , hx))) (λ y hy → hd (inr (y , hy)))

      -- THE STEP. One pair recursion over the kernel, with both coordinates
      -- descending. The two membership bridges are where the join hypothesis is
      -- spent, the outer transport is where the meet hypothesis is spent, and
      -- the exchange lemma inside `memL` is where BOTH symmetries are spent:
      -- the coded one, which Track C proved is free, and the host one, which
      -- section 1.4 proves is free for the same structural reason. Without one
      -- of the two the second conjunct cannot be reached, because the inductive
      -- hypothesis descends from `m` on the left and from `n` on the right
      -- while the second conjunct reads the value at the exchanged arguments.

      eqStepᴬ : ReadsSup → ReadsInf → (m n : S)
              → ((u v : S) → Child u m → Child v n
                 → reads (eqᴬ u v) ≡ (u ≈ᴿ v))
              → reads (eqᴬ m n) ≡ (m ≈ᴿ n)
      eqStepᴬ rs ri m n ih =
          reads-inf-≡ ri (Supᴺ m ⊎ Supᴺ n) (eqFamᴮ m n) (eqᴬ m n) (eqGlbᴮ m n)
        ∙ cong (⋀ᴿ (Supᴺ m ⊎ Supᴺ n)) (funExt famAgree)
        ∙ ⋀ᴿ-⊎ (Supᴺ m) (Supᴺ n) (eqFamᴿ m n)
        ∙ sym (≈ᴿ-step′ m n)
        where
          memR : (x : S) → Child x m → reads (memᴬ x n) ≡ (x ∈ᴿ n)
          memR x ex =
              reads-sup-≡ rs (Supᴺ n)
                (λ q → (weightᴮ n (fst q)) ⊓ᴮ (eqᴬ x (fst q))) (memᴬ x n)
                (memLubᴮ x n)
            ∙ cong (⋁ᴿ (Supᴺ n)) (funExt (λ q →
                  reads-⊓ (weightᴮ n (fst q)) (eqᴬ x (fst q))
                ∙ cong (λ z → z ⊓ᴿ (reads (eqᴬ x (fst q))))
                       (wt-agrees n (fst q))
                ∙ cong (λ z → (wtᴿ n (fst q)) ⊓ᴿ z)
                       (ih x (fst q) ex (edge n q))))

          memL : (y : S) → Child y n → reads (memᴬ y m) ≡ (y ∈ᴿ m)
          memL y ey =
              reads-sup-≡ rs (Supᴺ m)
                (λ p → (weightᴮ m (fst p)) ⊓ᴮ (eqᴬ y (fst p))) (memᴬ y m)
                (memLubᴮ y m)
            ∙ cong (⋁ᴿ (Supᴺ m)) (funExt (λ p →
                  reads-⊓ (weightᴮ m (fst p)) (eqᴬ y (fst p))
                ∙ cong (λ z → z ⊓ᴿ (reads (eqᴬ y (fst p))))
                       (wt-agrees m (fst p))
                ∙ cong (λ z → (wtᴿ m (fst p)) ⊓ᴿ z)
                       (exch (fst p) (edge m p))))
            where
              exch : (x : S) → Child x m → reads (eqᴬ y x) ≡ (y ≈ᴿ x)
              exch x ex = cong reads (eqᴬ-sym y x)
                        ∙ ih x y ex ey
                        ∙ ≈ᴿ-sym x y

          famAgree : (c : Supᴺ m ⊎ Supᴺ n)
                   → reads (eqFamᴮ m n c) ≡ eqFamᴿ m n c
          famAgree (inl p) =
              reads-⇒ (weightᴮ m (fst p)) (memᴬ (fst p) n)
            ∙ cong (λ z → z ⇒ᴿ (reads (memᴬ (fst p) n))) (wt-agrees m (fst p))
            ∙ cong (λ z → (wtᴿ m (fst p)) ⇒ᴿ z) (memR (fst p) (edge m p))
          famAgree (inr q) =
              reads-⇒ (weightᴮ n (fst q)) (memᴬ (fst q) m)
            ∙ cong (λ z → z ⇒ᴿ (reads (memᴬ (fst q) m))) (wt-agrees n (fst q))
            ∙ cong (λ z → (wtᴿ n (fst q)) ⇒ᴿ z) (memL (fst q) (edge n q))

      eq-agrees : ReadsSup → ReadsInf → (m n : S) → reads (eqᴬ m n) ≡ (m ≈ᴿ n)
      eq-agrees rs ri =
        rawPairRec (λ m n → reads (eqᴬ m n) ≡ (m ≈ᴿ n)) (eqStepᴬ rs ri)

      mem-agrees : ReadsSup → ReadsInf → (m n : S) → reads (memᴬ m n) ≡ (m ∈ᴿ n)
      mem-agrees rs ri m n =
          reads-sup-≡ rs (Supᴺ n)
            (λ q → (weightᴮ n (fst q)) ⊓ᴮ (eqᴬ m (fst q))) (memᴬ m n)
            (memLubᴮ m n)
        ∙ cong (⋁ᴿ (Supᴺ n)) (funExt (λ q →
              reads-⊓ (weightᴮ n (fst q)) (eqᴬ m (fst q))
            ∙ cong (λ z → z ⊓ᴿ (reads (eqᴬ m (fst q)))) (wt-agrees n (fst q))
            ∙ cong (λ z → (wtᴿ n (fst q)) ⊓ᴿ z) (eq-agrees rs ri m (fst q))))

      -- The two atomic agreements in the form R7 forces. Both carry the two
      -- conditional hypotheses on their face; neither is a module parameter.

      atomic-agrees-≈ : (rs : ReadsSup) (ri : ReadsInf) (m n : S)
                      → ⟨ Agrees (eqᴬ m n) (m ≈ᴿ n) ⟩
      atomic-agrees-≈ rs ri m n =
        ≡→agrees (eqᴬ m n) (m ≈ᴿ n) (eq-agrees rs ri m n)

      atomic-agrees-∈ : (rs : ReadsSup) (ri : ReadsInf) (m n : S)
                      → ⟨ Agrees (memᴬ m n) (m ∈ᴿ n) ⟩
      atomic-agrees-∈ rs ri m n =
        ≡→agrees (memᴬ m n) (m ∈ᴿ n) (mem-agrees rs ri m n)

--------------------------------------------------------------------------------
-- 4. The conditional agreement for every compiled formula
--------------------------------------------------------------------------------

      -- Track F's compiler enters FLAT, as the value function and the fourteen
      -- `InterpLaws` fields, field for field and in its order. Flat rather than
      -- as the record for the reason Tracks D, E and F each measured
      -- independently: a flat field list creates no second type, and taking the
      -- record would put the whole compiler telescope into this file's ledger
      -- for fourteen projections. Nothing here reads `Interp.code` or
      -- `Interp.reading`: the internal formula that describes a value inside
      -- the ground plays no part in the agreement, which is a statement about
      -- the VALUES and not about their internal descriptions.
      --
      -- WHAT MAKES THE STATEMENT POSSIBLE AT ALL, and it is worth naming,
      -- because it is also what keeps Bell's page 24 prohibition intact. The
      -- two evaluators read THE SAME formula. Track F's input is
      -- `Formula (⊥* {ℓ}) k`, parameter free, and section 1.7's `_⊫_` is the
      -- book's own satisfaction at the same syntax with the same empty constant
      -- domain. So there is no translation between the two sides to get wrong,
      -- and `formula-agrees` compares `value φ ν` with `ν ⊫ φ` at the same `φ`.
      -- Both are HOST functions of `φ`; neither is a map of the ground, and no
      -- code of a formula enters any term on either side.

      module Formulas
        (value : ∀ {k} → Src k → Env k → Pt B)
        (law-∈ : ∀ {k} (i j : Fin k) (ν : Env k)
               → value (var i ∈̇ var j) ν
               ≡ memᴬ (fst (lookup i ν)) (fst (lookup j ν)))
        (law-≐ : ∀ {k} (i j : Fin k) (ν : Env k)
               → value (var i ≐ var j) ν
               ≡ eqᴬ (fst (lookup i ν)) (fst (lookup j ν)))
        (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Env k)
               → value (φ ∧̇ ψ) ν ≡ ((value φ ν) ⊓ᴮ (value ψ ν)))
        (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Env k)
               → value (φ ∨̇ ψ) ν ≡ ((value φ ν) ⊔ᴮ (value ψ ν)))
        (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Env k)
               → value (φ ⇒̇ ψ) ν ≡ ((value φ ν) ⇒ᴮ (value ψ ν)))
        (law-⊥ : ∀ {k} (ν : Env k) → value {k} ⊥̇ ν ≡ ⊥ᴮ)
        (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
                    → ⟨ (value φ (σ ∷ ν)) ≤ᴮ (value (∃̇ φ) ν) ⟩)
        (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                    → ((σ : Name) → ⟨ (value φ (σ ∷ ν)) ≤ᴮ c ⟩)
                    → ⟨ (value (∃̇ φ) ν) ≤ᴮ c ⟩)
        (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
                    → ⟨ (value (∀̇ φ) ν) ≤ᴮ (value φ (σ ∷ ν)) ⟩)
        (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                    → ((σ : Name) → ⟨ c ≤ᴮ (value φ (σ ∷ ν)) ⟩)
                    → ⟨ c ≤ᴮ (value (∀̇ φ) ν) ⟩)
        (law-∃∈-ub  : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
                    → ⟨ ((memᴬ (fst σ) (fst (lookup i ν))) ⊓ᴮ (value φ (σ ∷ ν)))
                        ≤ᴮ (value (∃̇∈ (var i) φ) ν) ⟩)
        (law-∃∈-lub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                    → ((σ : Name)
                       → ⟨ ((memᴬ (fst σ) (fst (lookup i ν)))
                             ⊓ᴮ (value φ (σ ∷ ν))) ≤ᴮ c ⟩)
                    → ⟨ (value (∃̇∈ (var i) φ) ν) ≤ᴮ c ⟩)
        (law-∀∈-lb  : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
                    → ⟨ (value (∀̇∈ (var i) φ) ν)
                        ≤ᴮ ((memᴬ (fst σ) (fst (lookup i ν)))
                             ⇒ᴮ (value φ (σ ∷ ν))) ⟩)
        (law-∀∈-glb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                    → ((σ : Name)
                       → ⟨ c ≤ᴮ ((memᴬ (fst σ) (fst (lookup i ν)))
                                  ⇒ᴮ (value φ (σ ∷ ν))) ⟩)
                    → ⟨ c ≤ᴮ (value (∀̇∈ (var i) φ) ν) ⟩)
        where

        -- The four quantifier nodes, repackaged as the admission facts the two
        -- hypotheses consume. Each is at index `Name`, which is a `Type ℓ` and
        -- NOT a `Pt X` for any ground code: the compiler's existential node
        -- joins over ALL names and no bound is constructed (Track F's item 6).
        -- So even the JOIN half of the agreement, whose atomic use does fit the
        -- architecture's `supᴮ X h` shape, does not fit it here.

        ∃-lub : ∀ {k} (φ : Src (suc k)) (ν : Env k)
              → IsLubᴮ {Name} (λ σ → value φ (σ ∷ ν)) (value (∃̇ φ) ν)
        ∃-lub φ ν = (λ σ → law-∃-ub φ ν σ) , (λ d hd → law-∃-lub φ ν d hd)

        ∀-glb : ∀ {k} (φ : Src (suc k)) (ν : Env k)
              → IsGlbᴮ {Name} (λ σ → value φ (σ ∷ ν)) (value (∀̇ φ) ν)
        ∀-glb φ ν = (λ σ → law-∀-lb φ ν σ) , (λ d hd → law-∀-glb φ ν d hd)

        ∃∈-lub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k)
               → IsLubᴮ {Name}
                   (λ σ → (memᴬ (fst σ) (fst (lookup i ν))) ⊓ᴮ (value φ (σ ∷ ν)))
                   (value (∃̇∈ (var i) φ) ν)
        ∃∈-lub i φ ν = (λ σ → law-∃∈-ub i φ ν σ)
                     , (λ d hd → law-∃∈-lub i φ ν d hd)

        ∀∈-glb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k)
               → IsGlbᴮ {Name}
                   (λ σ → (memᴬ (fst σ) (fst (lookup i ν))) ⇒ᴮ (value φ (σ ∷ ν)))
                   (value (∀̇∈ (var i) φ) ν)
        ∀∈-glb i φ ν = (λ σ → law-∀∈-lb i φ ν σ)
                     , (λ d hd → law-∀∈-glb i φ ν d hd)

        -- THE CONDITIONAL AGREEMENT. One structural recursion over the ten
        -- constructors, plus six absurd term cases because the constant domain
        -- is empty. The two hypotheses are module parameters of this anonymous
        -- block only, which makes them the two leading EXPLICIT arguments of
        -- `formula-agrees` from outside, exactly as the architecture prints it.
        --
        -- Where each hypothesis is spent, and it is worth reading as a ledger.
        -- CORRECTED 2026-09-12, after K5's design pass refuted the sentence
        -- that stood here. It read that the six finite cases are
        -- unconditional and that the agreement is therefore unconditional on
        -- the quantifier free fragment. That contradicts its own next clause:
        -- the ten constructors are four quantifier cases and six others, and
        -- THE TWO ATOMIC CASES ARE AMONG THE SIX. They are quantifier free and
        -- they spend both hypotheses, as their own signatures show. The
        -- genuinely unconditional fragment is smaller: the propositional one
        -- generated from falsum by conjunction, disjunction and implication.
        -- The four quantifier cases spend one hypothesis each, at the index
        -- `Name`. What is conditional is every case in which a value is a
        -- supremum or an infimum, on either side, of a family both sides must
        -- admit, and the two atomic values are such suprema.

        module _ (rs : ReadsSup) (ri : ReadsInf) where

          formula-agrees : ∀ {k} (φ : Src k) (ν : Env k)
                         → reads (value φ ν) ≡ (ν ⊫ φ)
          formula-agrees (con () ∈̇ u) ν
          formula-agrees (var i ∈̇ con ()) ν
          formula-agrees (var i ∈̇ var j) ν =
              cong reads (law-∈ i j ν)
            ∙ mem-agrees rs ri (fst (lookup i ν)) (fst (lookup j ν))
          formula-agrees (con () ≐ u) ν
          formula-agrees (var i ≐ con ()) ν
          formula-agrees (var i ≐ var j) ν =
              cong reads (law-≐ i j ν)
            ∙ eq-agrees rs ri (fst (lookup i ν)) (fst (lookup j ν))
          formula-agrees (φ ∧̇ ψ) ν =
              cong reads (law-∧ φ ψ ν)
            ∙ reads-⊓ (value φ ν) (value ψ ν)
            ∙ cong (λ z → z ⊓ᴿ (reads (value ψ ν))) (formula-agrees φ ν)
            ∙ cong (λ z → (ν ⊫ φ) ⊓ᴿ z) (formula-agrees ψ ν)
          formula-agrees (φ ∨̇ ψ) ν =
              cong reads (law-∨ φ ψ ν)
            ∙ reads-⊔ (value φ ν) (value ψ ν)
            ∙ cong (λ z → z ⊔ᴿ (reads (value ψ ν))) (formula-agrees φ ν)
            ∙ cong (λ z → (ν ⊫ φ) ⊔ᴿ z) (formula-agrees ψ ν)
          formula-agrees (φ ⇒̇ ψ) ν =
              cong reads (law-⇒ φ ψ ν)
            ∙ reads-⇒ (value φ ν) (value ψ ν)
            ∙ cong (λ z → z ⇒ᴿ (reads (value ψ ν))) (formula-agrees φ ν)
            ∙ cong (λ z → (ν ⊫ φ) ⇒ᴿ z) (formula-agrees ψ ν)
          formula-agrees ⊥̇ ν = cong reads (law-⊥ ν) ∙ reads-⊥
          formula-agrees (∃̇ φ) ν =
              reads-sup-≡ rs Name (λ σ → value φ (σ ∷ ν))
                (value (∃̇ φ) ν) (∃-lub φ ν)
            ∙ cong (⋁ᴿ Name) (funExt (λ σ → formula-agrees φ (σ ∷ ν)))
          formula-agrees (∀̇ φ) ν =
              reads-inf-≡ ri Name (λ σ → value φ (σ ∷ ν))
                (value (∀̇ φ) ν) (∀-glb φ ν)
            ∙ cong (⋀ᴿ Name) (funExt (λ σ → formula-agrees φ (σ ∷ ν)))
          formula-agrees (∀̇∈ (con ()) φ) ν
          formula-agrees (∀̇∈ (var i) φ) ν =
              reads-inf-≡ ri Name
                (λ σ → (memᴬ (fst σ) (fst (lookup i ν))) ⇒ᴮ (value φ (σ ∷ ν)))
                (value (∀̇∈ (var i) φ) ν) (∀∈-glb i φ ν)
            ∙ cong (⋀ᴿ Name) (funExt (λ σ →
                  reads-⇒ (memᴬ (fst σ) (fst (lookup i ν))) (value φ (σ ∷ ν))
                ∙ cong (λ z → z ⇒ᴿ (reads (value φ (σ ∷ ν))))
                       (mem-agrees rs ri (fst σ) (fst (lookup i ν)))
                ∙ cong (λ z → ((fst σ) ∈ᴿ (fst (lookup i ν))) ⇒ᴿ z)
                       (formula-agrees φ (σ ∷ ν))))
          formula-agrees (∃̇∈ (con ()) φ) ν
          formula-agrees (∃̇∈ (var i) φ) ν =
              reads-sup-≡ rs Name
                (λ σ → (memᴬ (fst σ) (fst (lookup i ν))) ⊓ᴮ (value φ (σ ∷ ν)))
                (value (∃̇∈ (var i) φ) ν) (∃∈-lub i φ ν)
            ∙ cong (⋁ᴿ Name) (funExt (λ σ →
                  reads-⊓ (memᴬ (fst σ) (fst (lookup i ν))) (value φ (σ ∷ ν))
                ∙ cong (λ z → z ⊓ᴿ (reads (value φ (σ ∷ ν))))
                       (mem-agrees rs ri (fst σ) (fst (lookup i ν)))
                ∙ cong (λ z → ((fst σ) ∈ᴿ (fst (lookup i ν))) ⊓ᴿ z)
                       (formula-agrees φ (σ ∷ ν))))

          -- The same statement in the form R7 forces, which is the shape the
          -- architecture prints and the shape a consumer should quote.

          formula-agrees-Ω : ∀ {k} (φ : Src k) (ν : Env k)
                           → ⟨ Agrees (value φ ν) (ν ⊫ φ) ⟩
          formula-agrees-Ω φ ν =
            ≡→agrees (value φ ν) (ν ⊫ φ) (formula-agrees φ ν)

--------------------------------------------------------------------------------
-- 5. What is NOT claimed
--------------------------------------------------------------------------------

-- Collected here beside the signatures they constrain, on the model of the
-- architecture's own section 1.12.
--
-- 1. NO INTERNAL GLOBAL TRUTH VALUE FUNCTION, on either side. `_⊫_` is
--    `FOL.Semantics` applied to a second truth algebra: a host recursion on a
--    host formula, defined metalinguistically exactly as the coded compiler is.
--    There is no `Val : Formula S m`, no code of a formula in any term, and no
--    reading uniform in the formula. Bell's restriction (printed p. 24,
--    fulltext:2043-2052) is a THEOREM of ZFC and this file does not evade it;
--    it also does not weaken, because a reference semantics compares values and
--    never needs the collection of pairs Bell shows is not definable.
--
-- 2. NO UNCONDITIONAL AGREEMENT beyond the quantifier free fragment. Every
--    theorem of sections 3 and 4 that mentions a supremum or an infimum carries
--    `ReadsSup` or `ReadsInf` as an explicit argument. Neither is proved here
--    and neither is proved anywhere in the programme today:
--    `grep -c "reads-sup\|reads-inf\|reads-⋁\|reads-⋀"` over
--    `/tmp/bedrock-k3-probes/CodedCompletion.agda` returns 0, re-run for this
--    file. Obstruction O2 is untouched, and section 2.5 records the one
--    correction this track measures about it: the hypotheses the induction
--    needs are strictly stronger than the `supᴮ X h` and `infᴮ X h` statements
--    the architecture names, because they are applied at index `Name` and at
--    index `Supᴺ m ⊎ Supᴺ n`, neither of which is a `Pt X`.
--
-- 3. NO DISCHARGE OF THE ATOMIC GRAPH and no compiler instance. Obstruction O1
--    is untouched: this file takes Track C's atomic values and Track F's
--    compiler as parameters and discharges neither. The host semantics itself
--    needs no atomic graph at all, which is a real asymmetry between the two
--    sides and the reason the reference semantics is cheap; it is not a route
--    to closing O1, because the coded value is the one K13 must test for
--    membership in the ultrafilter.
--
-- 4. NO CLAIM THAT `reads` IS SURJECTIVE. `agrees-unique` says a host value
--    pins at most one coded value. Nothing says every host value is read by
--    one, and the compiler never needs that: the coded value exists by Track
--    F's construction and the agreement only identifies it.
--
-- 5. NO INFINITE DISTRIBUTIVE LAW IS USED, on either side. The host algebra HAS
--    one, freely, through `Algebra.agda:335-345`'s `CompleteTheory` applied to
--    `roLaws` and `roComplete`; this file never applies that module, and
--    `grep -c "dist\|⋁-dist\|CompleteTheory"` over this file returns 0 outside
--    comment lines. R5 is therefore respected on the coded side by never having
--    a coded infinitary law to respect, and on the host side by choice.
--
-- 6. NO NONDEGENERACY. `roNondegenerate` needs an inhabitant of the condition
--    type (HostRegularOpen.agda:633-634) and nothing here needs the algebra to
--    be nontrivial; the whole file holds, vacuously and correctly, over the
--    one element algebra. Track A's refutation of the architecture's printed
--    `inf-residual` is the cautionary case: a statement that silently forces
--    `⊥ ≡ ⊤` is a statement about the empty family, and section 1's
--    `⋀ᴿ-const-⊤` is the place where an empty support is handled and where the
--    same mistake would have shown up.
--
-- 7. NO BELL 1.17(iv), (v) OR (vi) ON THE HOST SIDE. Reflexivity, the weight
--    bound and symmetry are proved in sections 1.4 and 1.6. Transitivity and
--    the two congruences are not attempted, for a scope reason that is worth
--    stating rather than hiding: no consumer can exist, because no module may
--    import this one, and Track D proves them on the coded side where they are
--    consumed. A later track that wants the host structure to be a
--    Boolean valued MODEL rather than a Boolean valued structure has to add
--    them, and Track D's own measurement applies, that symmetry is load
--    bearing in transitivity and the architecture had the dependency backwards.
--
-- 8. NO SUBALGEBRA OR ABSOLUTENESS CLAIM. Bell's Theorem 1.20 and Corollary
--    1.21 are about the atomic values in two algebras and the coordinator has
--    ruled them K4's, on Track D. This file's `ReadsSup` and `ReadsInf` are the
--    complete subalgebra condition for the families at hand and nothing more:
--    they are hypotheses, they are not derived from a subalgebra inclusion, and
--    no Δ₀ certificate or submodel absoluteness is claimed for any value here.
