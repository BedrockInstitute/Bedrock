{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track J, file 1: the naive disjunction clause and the naive existential
-- clause, transcribed under their own names and refuted.
--
-- THE NOTION. A two element antichain does NOT refute either clause, and a
-- designer proposed it; K5/AntichainControl.agda proves that it does not, so
-- the proposal is refuted there rather than asserted away here. The smallest
-- refuting notion is the three element "V": a top vtop with two incomparable
-- conditions va and vb below it.
--
-- THE ARITHMETIC, checked below rather than quoted:
--
--   i vtop = ⊤ᴮ                         iTop-⊤
--   i va   = { va }                     iA-in, iA-out
--   i vb   = { vb }                     iB-in, iB-out
--   i va ⊔ᴮ i vb = ⊤ᴮ                   join-is-⊤
--
-- so vtop forces the join while forcing neither disjunct. The join is the
-- regularization of the union, and the union { va , vb } has empty
-- pseudocomplement: nothing in this poset is incompatible with both atoms,
-- because every condition refines one of them or is the top, which is refined
-- by both. That is the whole mechanism, and it is invisible if ⊔ᴮ is read as
-- union.
--
-- WHY A COMPETENT READER WRITES THE NAIVE CLAUSES. In a two valued model,
-- and in every textbook presentation of forcing for a COMPLETE sequence of
-- conditions, p ⊩ φ ∨ ψ gives p ⊩ φ or p ⊩ ψ; the Boolean value of a
-- disjunction IS the join, and joins in a powerset algebra are unions. Bell
-- states the clause with a density qualifier (Lemma 2.5) precisely because
-- the join of a Boolean COMPLETION is not the union. A reader who transcribes
-- the two valued clause, or who reads ⊔ᴮ as ∪, writes exactly the statements
-- refuted below.
--
-- The relation used is the module's own entailment of regular subsets, which
-- is the Ω valued form of the Boolean order (⊩ᴴ-to-≤ and ⊩ᴴ-from-≤ prove the
-- two spellings agree, so the refutation cannot be evaded by saying it is
-- about a different relation).
--
-- Every theorem in this file is constructive. LEM appears nowhere.

open import Base.Prelude
open import Base.Truth

module K5.RefutedClauses {ℓ : Level} where

open import Cubical.Data.Bool using ( Bool; true; false; isSetBool )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.HLevels using ( isOfHLevelRetract; isSet× )
import Cubical.Data.Empty as Empty
import Cubical.Functions.Logic as Logic
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

import HostRegularOpen

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 1. The three element V
--------------------------------------------------------------------------------

-- Three conditions. The h-set structure comes from a retraction into
-- Bool × Bool, as K2's four condition instance does; the fourth tag is unused
-- and is sent back to the top.

data V3 : Type ℓ where
  vtop va vb : V3

tag : V3 → Bool × Bool
tag vtop = false , false
tag va   = true  , false
tag vb   = true  , true

untag : Bool × Bool → V3
untag (false , false) = vtop
untag (true  , false) = va
untag (true  , true)  = vb
untag (false , true)  = vtop

tag-retract : (p : V3) → untag (tag p) ≡ p
tag-retract vtop = refl
tag-retract va   = refl
tag-retract vb   = refl

isSetV3 : isSet V3
isSetV3 = isOfHLevelRetract 2 tag untag tag-retract (isSet× isSetBool isSetBool)

-- The order, written by matching on the RIGHT argument only, which is what
-- keeps transitivity at three clauses.

isA : V3 → Ω
isA va = ⊤
isA _  = ⊥

isB : V3 → Ω
isB vb = ⊤
isB _  = ⊥

ord : V3 → V3 → Ω
ord _ vtop = ⊤
ord p va   = isA p
ord p vb   = isB p

ord-refl : (p : V3) → ⟨ ord p p ⟩
ord-refl vtop = tt*
ord-refl va   = tt*
ord-refl vb   = tt*

A-refines : (p q : V3) → ⟨ ord p q ⟩ → ⟨ isA q ⟩ → ⟨ isA p ⟩
A-refines p vtop _ h = Empty.rec* h
A-refines p va   h _ = h
A-refines p vb   _ h = Empty.rec* h

B-refines : (p q : V3) → ⟨ ord p q ⟩ → ⟨ isB q ⟩ → ⟨ isB p ⟩
B-refines p vtop _ h = Empty.rec* h
B-refines p va   _ h = Empty.rec* h
B-refines p vb   h _ = h

ord-trans : {p q r : V3} → ⟨ ord p q ⟩ → ⟨ ord q r ⟩ → ⟨ ord p r ⟩
ord-trans {p} {q} {vtop} _  _  = tt*
ord-trans {p} {q} {va}   h₁ h₂ = A-refines p q h₁ h₂
ord-trans {p} {q} {vb}   h₁ h₂ = B-refines p q h₁ h₂

-- The two atoms are incomparable, and nothing refines both.

atoms-apart : (p : V3) → ⟨ isA p ⟩ → ⟨ isB p ⟩ → ⟨ ⊥ ⟩
atoms-apart vtop h _ = Empty.rec* h
atoms-apart va   _ h = Empty.rec* h
atoms-apart vb   h _ = Empty.rec* h

a-not-below-b : ⟨ ord va vb ⟩ → ⟨ ⊥ ⟩
a-not-below-b h = h

b-not-below-a : ⟨ ord vb va ⟩ → ⟨ ⊥ ⟩
b-not-below-a h = h

--------------------------------------------------------------------------------
-- 2. The regular open algebra of the V, and the forcing relation at it
--------------------------------------------------------------------------------

module R = HostRegularOpen V3 isSetV3 ord ord-refl
             (λ {p} {q} {r} → ord-trans {p} {q} {r})

open R using ( Sub; Reg; _⊑_; ⊑-refl; isProp⊑; Reg≡; _⋆; _∪_; ⋃
             ; ⊤ᴮ; ⊥ᴮ; _⊔ᴮ_; ⋁ᴮ; _≤ᴮ_; ≤ᴮ-from; ≤ᴮ-to; ↓ᶜ_ )

-- The forcing relation of K5 section 1.3, at the host algebra: p forces U
-- when the image of p entails U. Entailment of subsets is SMALL (Type ℓ) and
-- is a proposition, so this is an Ω, which the Boolean order itself is not.

_⊩ᴴ_ : V3 → Reg → Ω
p ⊩ᴴ U = (fst (R.i p) ⊑ fst U) , isProp⊑ (fst (R.i p)) (fst U)

-- and it is the Boolean order, in both directions, so nothing below turns on
-- the choice of spelling.

⊩ᴴ-to-≤ : (p : V3) (U : Reg) → ⟨ p ⊩ᴴ U ⟩ → R.i p ≤ᴮ U
⊩ᴴ-to-≤ p U h = ≤ᴮ-from (R.i p) U h

⊩ᴴ-from-≤ : (p : V3) (U : Reg) → R.i p ≤ᴮ U → ⟨ p ⊩ᴴ U ⟩
⊩ᴴ-from-≤ p U e = ≤ᴮ-to (R.i p) U e

--------------------------------------------------------------------------------
-- 3. The arithmetic of the V, checked
--------------------------------------------------------------------------------

-- The cone of the top is everything, so its pseudocomplement is empty and the
-- image of the top is the top of the algebra.

iTop-⊤ : R.i vtop ≡ ⊤ᴮ
iTop-⊤ = Reg≡ (R.i vtop) ⊤ᴮ
  (λ q _ → tt*)
  (λ q _ r r≼q y → y r (ord-refl r) tt*)

-- vb is incompatible with va, hence lies in the pseudocomplement of va's
-- cone, and symmetrically.

b-avoids-A : ⟨ ((↓ᶜ va) ⋆) vb ⟩
b-avoids-A s s≼vb s≼va = atoms-apart s s≼va s≼vb

a-avoids-B : ⟨ ((↓ᶜ vb) ⋆) va ⟩
a-avoids-B s s≼va s≼vb = atoms-apart s s≼va s≼vb

-- The image of an atom is its own singleton. The inward direction is the
-- cone; the outward direction is where the pseudocomplement is spent.

iA-in : (q : V3) → ⟨ isA q ⟩ → ⟨ fst (R.i va) q ⟩
iA-in = R.i-cone va

iA-out : (q : V3) → ⟨ fst (R.i va) q ⟩ → ⟨ isA q ⟩
iA-out vtop x = x vb tt* b-avoids-A
iA-out va   x = tt*
iA-out vb   x = x vb (ord-refl vb) b-avoids-A

iB-in : (q : V3) → ⟨ isB q ⟩ → ⟨ fst (R.i vb) q ⟩
iB-in = R.i-cone vb

iB-out : (q : V3) → ⟨ fst (R.i vb) q ⟩ → ⟨ isB q ⟩
iB-out vtop x = x va tt* a-avoids-B
iB-out va   x = x va (ord-refl va) a-avoids-B
iB-out vb   x = tt*

-- Nothing is incompatible with both atoms: every condition either refines one
-- of them, or is the top, which both atoms refine. So the union of the two
-- singletons has empty pseudocomplement, and the join regularizes to the top.

AorB : Sub
AorB = (fst (R.i va)) ∪ (fst (R.i vb))

join-dense : (r : V3) → ⟨ (AorB ⋆) r ⟩ → ⟨ ⊥ ⟩
join-dense vtop y = y va tt*            (Logic.inl (R.i-self va))
join-dense va   y = y va (ord-refl va)  (Logic.inl (R.i-self va))
join-dense vb   y = y vb (ord-refl vb)  (Logic.inr (R.i-self vb))

join-is-⊤ : (R.i va ⊔ᴮ R.i vb) ≡ ⊤ᴮ
join-is-⊤ = Reg≡ (R.i va ⊔ᴮ R.i vb) ⊤ᴮ
  (λ q _ → tt*)
  (λ q _ r r≼q y → join-dense r y)

--------------------------------------------------------------------------------
-- 4. The top forces the join and forces neither disjunct
--------------------------------------------------------------------------------

top-forces-join : ⟨ vtop ⊩ᴴ (R.i va ⊔ᴮ R.i vb) ⟩
top-forces-join q _ = λ r r≼q y → join-dense r y

top-not-forces-A : ⟨ vtop ⊩ᴴ R.i va ⟩ → ⟨ ⊥ ⟩
top-not-forces-A h = iA-out vb (h vb (R.i-cone vtop vb tt*))

top-not-forces-B : ⟨ vtop ⊩ᴴ R.i vb ⟩ → ⟨ ⊥ ⟩
top-not-forces-B h = iB-out va (h va (R.i-cone vtop va tt*))

--------------------------------------------------------------------------------
-- 5. THE NAIVE DISJUNCTION CLAUSE, REFUTED
--------------------------------------------------------------------------------

-- The statement, under its own name: a condition forcing a join forces one of
-- the two joinands. The conclusion is the algebra's own ⊔, that is, the
-- propositional truncation of the sum, which is the WEAKEST form of the
-- conclusion and so makes the refutation the strongest.

NaiveDisjunction : Type (ℓ-suc ℓ)
NaiveDisjunction = (p : V3) (U V : Reg)
                 → ⟨ p ⊩ᴴ (U ⊔ᴮ V) ⟩ → ⟨ (p ⊩ᴴ U) ⊔ (p ⊩ᴴ V) ⟩

naive-disjunction-fails : NaiveDisjunction → ⟨ ⊥ ⟩
naive-disjunction-fails nd =
  PT.rec isProp⊥* branch (nd vtop (R.i va) (R.i vb) top-forces-join)
  where
  branch : ⟨ vtop ⊩ᴴ R.i va ⟩ ⊎ ⟨ vtop ⊩ᴴ R.i vb ⟩ → ⟨ ⊥ ⟩
  branch (inl h) = top-not-forces-A h
  branch (inr h) = top-not-forces-B h

-- The same statement spelled with the Boolean order rather than with
-- entailment, so that neither spelling escapes.

NaiveDisjunction≤ : Type (ℓ-suc ℓ)
NaiveDisjunction≤ = (p : V3) (U V : Reg)
                  → R.i p ≤ᴮ (U ⊔ᴮ V) → ∥ (R.i p ≤ᴮ U) ⊎ (R.i p ≤ᴮ V) ∥₁

naive-disjunction≤-fails : NaiveDisjunction≤ → ⟨ ⊥ ⟩
naive-disjunction≤-fails nd = naive-disjunction-fails step
  where
  step : NaiveDisjunction
  step p U V h = PT.map branch (nd p U V (⊩ᴴ-to-≤ p (U ⊔ᴮ V) h))
    where
    branch : (R.i p ≤ᴮ U) ⊎ (R.i p ≤ᴮ V)
           → ⟨ p ⊩ᴴ U ⟩ ⊎ ⟨ p ⊩ᴴ V ⟩
    branch (inl e) = inl (⊩ᴴ-from-≤ p U e)
    branch (inr e) = inr (⊩ᴴ-from-≤ p V e)

--------------------------------------------------------------------------------
-- 6. THE NAIVE EXISTENTIAL CLAUSE, REFUTED
--------------------------------------------------------------------------------

-- The family. The index type of an infinitary join must be a Type ℓ, and the
-- conditions themselves are one, so the V indexes its own family: the top is
-- sent to the bottom of the algebra and each atom to its own image.

fam : V3 → Reg
fam vtop = ⊥ᴮ
fam va   = R.i va
fam vb   = R.i vb

sup-dense : (r : V3) → ⟨ ((⋃ V3 (λ a → fst (fam a))) ⋆) r ⟩ → ⟨ ⊥ ⟩
sup-dense vtop y = y va tt*           ∣ va , R.i-self va ∣₁
sup-dense va   y = y va (ord-refl va) ∣ va , R.i-self va ∣₁
sup-dense vb   y = y vb (ord-refl vb) ∣ vb , R.i-self vb ∣₁

top-forces-sup : ⟨ vtop ⊩ᴴ (⋁ᴮ V3 fam) ⟩
top-forces-sup q _ = λ r r≼q y → sup-dense r y

top-not-forces-fam : (a : V3) → ⟨ vtop ⊩ᴴ fam a ⟩ → ⟨ ⊥ ⟩
top-not-forces-fam vtop h = h vtop (R.i-self vtop)
top-not-forces-fam va   h = top-not-forces-A h
top-not-forces-fam vb   h = top-not-forces-B h

-- The statement, under its own name: a condition forcing an infinitary join
-- forces one member of the family. This is the clause a reader writes for ∃,
-- because the value of an existential IS the join over the names.

NaiveExistential : Type (ℓ-suc ℓ)
NaiveExistential = (p : V3) (A : Type ℓ) (f : A → Reg)
                 → ⟨ p ⊩ᴴ (⋁ᴮ A f) ⟩ → ⟨ ⋁ A (λ a → p ⊩ᴴ f a) ⟩

naive-existential-fails : NaiveExistential → ⟨ ⊥ ⟩
naive-existential-fails ne =
  PT.rec isProp⊥* (λ z → top-not-forces-fam (fst z) (snd z))
    (ne vtop V3 fam top-forces-sup)

--------------------------------------------------------------------------------
-- 7. Positive controls: the clauses K5 actually states DO hold here
--------------------------------------------------------------------------------

-- K5 section 1.3's dense-below operator, at this notion.

DenseBelow : V3 → (V3 → Ω) → Ω
DenseBelow p W = ⋀ V3 (λ q → (ord q p) ⇒ ⋁ V3 (λ r → (ord r q) ⊓ W r))

-- The disjunction clause with the density qualifier holds at the very
-- condition that refutes the naive one, so the refutation is of the missing
-- qualifier and not of the clause layer.

disjunction-dense-below :
  ⟨ DenseBelow vtop (λ r → (r ⊩ᴴ R.i va) ⊔ (r ⊩ᴴ R.i vb)) ⟩
disjunction-dense-below vtop _ =
  ∣ va , tt* , Logic.inl (⊑-refl (fst (R.i va))) ∣₁
disjunction-dense-below va _ =
  ∣ va , tt* , Logic.inl (⊑-refl (fst (R.i va))) ∣₁
disjunction-dense-below vb _ =
  ∣ vb , tt* , Logic.inr (⊑-refl (fst (R.i vb))) ∣₁

existential-dense-below :
  ⟨ DenseBelow vtop (λ r → ⋁ V3 (λ a → r ⊩ᴴ fam a)) ⟩
existential-dense-below vtop _ =
  ∣ va , tt* , ∣ va , ⊑-refl (fst (R.i va)) ∣₁ ∣₁
existential-dense-below va _ =
  ∣ va , tt* , ∣ va , ⊑-refl (fst (R.i va)) ∣₁ ∣₁
existential-dense-below vb _ =
  ∣ vb , tt* , ∣ vb , ⊑-refl (fst (R.i vb)) ∣₁ ∣₁

--------------------------------------------------------------------------------
-- 8. The refuting notion is separative and antisymmetric
--------------------------------------------------------------------------------

-- This is what forecloses the obvious repair. Separativity is Bell's
-- refinement condition, it is the hypothesis that buys back order reflection
-- and injectivity of the embedding (separative→reflect, i-injective), and it
-- is the first thing a reader adds when a clause misbehaves. The V has it,
-- and has antisymmetry as well, and the naive clauses fail there anyway. No
-- hypothesis available at this layer repairs them; only the density qualifier
-- does.

inc-AB : ⟨ R.incompatible va vb ⟩
inc-AB = PT.rec isProp⊥*
  (λ z → atoms-apart (fst z) (fst (snd z)) (snd (snd z)))

inc-BA : ⟨ R.incompatible vb va ⟩
inc-BA = PT.rec isProp⊥*
  (λ z → atoms-apart (fst z) (snd (snd z)) (fst (snd z)))

V3-separative : R.separative
V3-separative vtop q      h = Empty.rec* (h tt*)
V3-separative va   vtop   _ = ∣ vb , tt* , inc-BA ∣₁
V3-separative va   va     h = Empty.rec* (h (ord-refl va))
V3-separative va   vb     _ = ∣ vb , ord-refl vb , inc-BA ∣₁
V3-separative vb   vtop   _ = ∣ va , tt* , inc-AB ∣₁
V3-separative vb   va     _ = ∣ va , ord-refl va , inc-AB ∣₁
V3-separative vb   vb     h = Empty.rec* (h (ord-refl vb))

V3-antisymmetric : R.antisymmetric
V3-antisymmetric vtop vtop _  _  = refl
V3-antisymmetric vtop va   h₁ _  = Empty.rec* h₁
V3-antisymmetric vtop vb   h₁ _  = Empty.rec* h₁
V3-antisymmetric va   vtop _  h₂ = Empty.rec* h₂
V3-antisymmetric va   va   _  _  = refl
V3-antisymmetric va   vb   h₁ _  = Empty.rec* h₁
V3-antisymmetric vb   vtop _  h₂ = Empty.rec* h₂
V3-antisymmetric vb   va   h₁ _  = Empty.rec* h₁
V3-antisymmetric vb   vb   _  _  = refl

--------------------------------------------------------------------------------
-- 9. The two refutations in one statement
--------------------------------------------------------------------------------

-- Both naive clauses fail at a notion that is a SEPARATIVE PARTIAL ORDER and
-- at which the correctly qualified clauses hold. The order facts are recorded
-- so that no reader can attribute the failure to a preorder artefact, to a
-- non-refined presentation, or to a collapsing embedding.

refuted-clauses :
    ((NaiveDisjunction → ⟨ ⊥ ⟩) × (NaiveExistential → ⟨ ⊥ ⟩))
  × ((R.separative × R.antisymmetric)
      × ((⟨ ord va vb ⟩ → ⟨ ⊥ ⟩) × (⟨ ord vb va ⟩ → ⟨ ⊥ ⟩)))
refuted-clauses =
    (naive-disjunction-fails , naive-existential-fails)
  , ((V3-separative , V3-antisymmetric)
  , (a-not-below-b , b-not-below-a))
