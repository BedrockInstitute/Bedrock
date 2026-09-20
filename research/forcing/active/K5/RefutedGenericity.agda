{-# OPTIONS --cubical --safe --guardedness #-}

-- K5 Track J, file 4: the level of host genericity.
--
-- THE STATEMENT. "A generic filter exists." Written host-side it reads: for
-- every forcing notion there is a filter meeting every dense host subset of
-- conditions. A competent reader writes it because the Rasiowa-Sikorski lemma
-- really does produce a filter meeting any COUNTABLE family of dense sets, and
-- because the textbook statement is about an M-generic filter for a countable
-- transitive model M. Drop the countability, equivalently drop the
-- relativization to M, and a true lemma becomes a false one. The level is the
-- tell: hostGeneric quantifies over Sub = Cond → Ω, which is large, so the
-- statement lands in Type (ℓ-suc ℓ), one universe above the coded genericity
-- K5 actually takes as a hypothesis, which quantifies over a code d : S and
-- stays in Type ℓ (K2's isGeneric, CodedCompletion.agda:1070-1074).
--
-- THE WITNESS. K2 proved no-host-generic (ForcingNotion.agda:315-340) under
-- LEM and ATOMLESSNESS, and shipped no atomless notion: K2's three acceptance
-- instances are two-condition, four-condition and one-point, and the
-- one-point one is a positive control for the opposite direction. So the
-- theorem had no instance anywhere in the programme and the existence claim
-- had never been refuted. This file supplies the missing notion, the binary
-- tree of finite 0-1 strings under extension, proves it atomless, and
-- refutes the existence claim at it.
--
-- THE STATEMENT THAT MAY NOT BE MADE, and is not made here: "no filter is
-- host generic", or "the extension properly extends the ground". K2's trivial
-- instance carries a host-generic filter, and section 3 below says exactly
-- what it contains: it is everything, the whole one-point poset, and it is
-- host generic because a dense subset of a one-point poset must contain that
-- one point. Host genericity is notion-dependent, which is the actual content,
-- and section 4 states both halves together.
--
-- LEM ℓ is an explicit argument of exactly the theorems that inherit it from
-- no-host-generic. The atomlessness proof and the whole tree construction are
-- constructive.

open import Base.Prelude
open import Base.Truth

module K5.RefutedGenericity {ℓ : Level} where

open import Base.Classical using ( LEM )
open import Cubical.Data.Bool using ( Bool; true; false; isSetBool )
open import Cubical.Data.Unit using ( tt* )
open import Cubical.Foundations.HLevels using ( isOfHLevelRetract )
import Cubical.Data.Empty as Empty
import Cubical.Data.List as L
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open import ForcingNotion using ( ForcingNotion; module Structure )
import Instances

open TruthAlgebra (hPropAlgebra ℓ)

--------------------------------------------------------------------------------
-- 1. The binary tree of finite strings
--------------------------------------------------------------------------------

-- Conditions are finite 0-1 strings, built with one constructor per digit so
-- that the order below needs no equality of digits. The h-set structure comes
-- from a retraction into List Bool.

data Str : Type ℓ where
  ε     : Str
  s₀ s₁ : Str → Str

toL : Str → L.List Bool
toL ε      = L.[]
toL (s₀ p) = false L.∷ toL p
toL (s₁ p) = true  L.∷ toL p

fromL : L.List Bool → Str
fromL L.[]           = ε
fromL (false L.∷ xs) = s₀ (fromL xs)
fromL (true  L.∷ xs) = s₁ (fromL xs)

toL-retract : (p : Str) → fromL (toL p) ≡ p
toL-retract ε      = refl
toL-retract (s₀ p) = cong s₀ (toL-retract p)
toL-retract (s₁ p) = cong s₁ (toL-retract p)

isSetStr : isSet Str
isSetStr =
  isOfHLevelRetract 2 toL fromL toL-retract (L.isOfHLevelList 0 isSetBool)

-- Pre q p reads "q is an initial segment of p". Written by recursion on both
-- arguments, so it is an Ω by construction and needs no propositionality
-- lemma: every leaf is the algebra's own ⊤ or ⊥.

Pre : Str → Str → Ω
Pre ε      _      = ⊤
Pre (s₀ q) ε      = ⊥
Pre (s₀ q) (s₀ p) = Pre q p
Pre (s₀ q) (s₁ p) = ⊥
Pre (s₁ q) ε      = ⊥
Pre (s₁ q) (s₀ p) = ⊥
Pre (s₁ q) (s₁ p) = Pre q p

Pre-refl : (p : Str) → ⟨ Pre p p ⟩
Pre-refl ε      = tt*
Pre-refl (s₀ p) = Pre-refl p
Pre-refl (s₁ p) = Pre-refl p

Pre-trans : (r q p : Str) → ⟨ Pre r q ⟩ → ⟨ Pre q p ⟩ → ⟨ Pre r p ⟩
Pre-trans ε      q      p      _  _  = tt*
Pre-trans (s₀ r) ε      p      h₁ _  = Empty.rec* h₁
Pre-trans (s₀ r) (s₀ q) ε      _  h₂ = Empty.rec* h₂
Pre-trans (s₀ r) (s₀ q) (s₀ p) h₁ h₂ = Pre-trans r q p h₁ h₂
Pre-trans (s₀ r) (s₀ q) (s₁ p) _  h₂ = Empty.rec* h₂
Pre-trans (s₀ r) (s₁ q) p      h₁ _  = Empty.rec* h₁
Pre-trans (s₁ r) ε      p      h₁ _  = Empty.rec* h₁
Pre-trans (s₁ r) (s₀ q) p      h₁ _  = Empty.rec* h₁
Pre-trans (s₁ r) (s₁ q) ε      _  h₂ = Empty.rec* h₂
Pre-trans (s₁ r) (s₁ q) (s₀ p) _  h₂ = Empty.rec* h₂
Pre-trans (s₁ r) (s₁ q) (s₁ p) h₁ h₂ = Pre-trans r q p h₁ h₂

-- A longer string refines a shorter one: p refines q when q is an initial
-- segment of p. This is Bell's convention, reverse inclusion.

ord : Str → Str → Ω
ord p q = Pre q p

ord-refl : (p : Str) → ⟨ ord p p ⟩
ord-refl = Pre-refl

ord-trans : {p q r : Str} → ⟨ ord p q ⟩ → ⟨ ord q r ⟩ → ⟨ ord p r ⟩
ord-trans {p} {q} {r} h₁ h₂ = Pre-trans r q p h₂ h₁

--------------------------------------------------------------------------------
-- 2. The tree is atomless
--------------------------------------------------------------------------------

-- Concatenation, and the two children of a condition.

app : Str → Str → Str
app ε      t = t
app (s₀ p) t = s₀ (app p t)
app (s₁ p) t = s₁ (app p t)

app-refines : (p t : Str) → ⟨ ord (app p t) p ⟩
app-refines ε      t = tt*
app-refines (s₀ p) t = app-refines p t
app-refines (s₁ p) t = app-refines p t

child₀ child₁ : Str → Str
child₀ p = app p (s₀ ε)
child₁ p = app p (s₁ ε)

-- No string extends both children: the two disagree at the digit in position
-- length p, and the induction walks down to it.

children-apart : (p r : Str)
               → ⟨ ord r (child₀ p) ⟩ → ⟨ ord r (child₁ p) ⟩ → ⟨ ⊥ ⟩
children-apart ε      ε      h₁ _  = Empty.rec* h₁
children-apart ε      (s₀ r) _  h₂ = Empty.rec* h₂
children-apart ε      (s₁ r) h₁ _  = Empty.rec* h₁
children-apart (s₀ p) ε      h₁ _  = Empty.rec* h₁
children-apart (s₀ p) (s₀ r) h₁ h₂ = children-apart p r h₁ h₂
children-apart (s₀ p) (s₁ r) h₁ _  = Empty.rec* h₁
children-apart (s₁ p) ε      h₁ _  = Empty.rec* h₁
children-apart (s₁ p) (s₀ r) h₁ _  = Empty.rec* h₁
children-apart (s₁ p) (s₁ r) h₁ h₂ = children-apart p r h₁ h₂

treeNotion : ForcingNotion {ℓ}
treeNotion = record
  { Cond     = Str
  ; isSetC   = isSetStr
  ; _≼_      = ord
  ; ≼-refl   = ord-refl
  ; ≼-trans  = λ {p} {q} {r} → ord-trans {p} {q} {r}
  ; nonempty = ∣ ε ∣₁ }

module TREE = Structure treeNotion

tree-atomless : TREE.atomless
tree-atomless p =
  ∣ child₀ p
  , ∣ child₁ p , app-refines p (s₀ ε) , app-refines p (s₁ ε) , inc ∣₁ ∣₁
  where
  inc : ⟨ TREE.incompatible (child₀ p) (child₁ p) ⟩
  inc = PT.rec isProp⊥*
          (λ z → children-apart p (fst z) (fst (snd z)) (snd (snd z)))

-- The level tell, as a checked ascription rather than a remark: host
-- genericity lands one universe above the conditions, because it quantifies
-- over host subsets. Nothing at Type ℓ can be substituted for it.

host-generic-level : TREE.Sub → Type (ℓ-suc ℓ)
host-generic-level = TREE.hostGeneric

no-generic-on-the-tree : LEM ℓ → (G : TREE.Sub) → TREE.isFilter G
                       → TREE.hostGeneric G → ⟨ ⊥ ⟩
no-generic-on-the-tree lem = TREE.no-host-generic lem tree-atomless

--------------------------------------------------------------------------------
-- 3. What K2's trivial instance actually carries
--------------------------------------------------------------------------------

-- Checked here rather than quoted. The filter is `everything`, the whole
-- one-point poset; it contains the unique condition; and it is host generic
-- because any dense subset of a one-point poset contains that point. The
-- notion is NOT atomless, which is exactly why it does not contradict
-- no-host-generic.

module TR = Instances.Trivial {ℓ}

trivial-host-generic : Σ[ G ∈ TR.Sub ] (TR.isFilter G × TR.hostGeneric G)
trivial-host-generic = TR.atomless-not-removable

trivial-generic-is-everything : fst trivial-host-generic ≡ TR.everything
trivial-generic-is-everything = refl

trivial-generic-has-the-only-condition : ⟨ TR._∈ᴾ_ tt* (fst trivial-host-generic) ⟩
trivial-generic-has-the-only-condition = tt*

trivial-is-one-point : (p q : TR.Cond) → p ≡ q
trivial-is-one-point = TR.one-point

trivial-not-atomless : TR.atomless → ⟨ ⊥ ⟩
trivial-not-atomless = TR.not-atomless

--------------------------------------------------------------------------------
-- 4. THE EXISTENCE OF A HOST-GENERIC FILTER, REFUTED
--------------------------------------------------------------------------------

HostGenericExists : Type (ℓ-suc ℓ)
HostGenericExists = (𝔓 : ForcingNotion {ℓ})
                  → ∥ Σ[ G ∈ Structure.Sub 𝔓 ]
                        (Structure.isFilter 𝔓 G × Structure.hostGeneric 𝔓 G) ∥₁

host-generic-existence-fails : LEM ℓ → HostGenericExists → ⟨ ⊥ ⟩
host-generic-existence-fails lem ex = PT.rec isProp⊥* step (ex treeNotion)
  where
  step : Σ[ G ∈ TREE.Sub ] (TREE.isFilter G × TREE.hostGeneric G) → ⟨ ⊥ ⟩
  step (G , fil , gen) = no-generic-on-the-tree lem G fil gen

-- Both halves in one statement. The left is K2's trivial instance, so no
-- statement of this package says that host genericity always fails; the right
-- is the tree, so no statement of this package may assume it ever holds.

host-genericity-is-notion-dependent :
    (Σ[ G ∈ TR.Sub ] (TR.isFilter G × TR.hostGeneric G))
  × (LEM ℓ → (G : TREE.Sub) → TREE.isFilter G → TREE.hostGeneric G → ⟨ ⊥ ⟩)
host-genericity-is-notion-dependent =
  trivial-host-generic , no-generic-on-the-tree
