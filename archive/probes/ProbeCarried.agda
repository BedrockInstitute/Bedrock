{-# OPTIONS --cubical --safe --guardedness #-}

-- [L3.32-T53] The carried-sequence gate at the first limit, l = ω.
-- Arm A: ω ∈ Sset (U ω).  Arm B: {Lset n : n < ω} ∈ Sset (γ ω).
-- Arm C: Lset ω ∈ Sset (γ ω).  Untracked probe, no master, no git.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; setIsSet )

module ProbeCarried {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) (A : V ℓ) where

open import FOL.ZFStructure using ( module hPropStructure )
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; extensionalV )
open import V.Model {ℓ} using ( self∈sucV; ∈sucV-elim; ∈sucV-inl )
open import L.Constructible {ℓ}
  using ( IsOrd; isTransV; Lset; Lset-in; Lset-out; Lset-mono; 𝒟ₒ )
open import L.Ordinal {ℓ} using
  ( ∅-ord; suc-ord; mem-ord; #∈ω; numeral-ord; numeral-mem; ω-ord; ω-mem-ord )
open import L.Ordinal.Stages {ℓ} lem using ( ord∈Lset-suc; φ-ord; φ-ord-Δ₀ )
open import FOL.Syntax using ( Formula )
open import FOL.Manipulation.Relabelling using ( mapFo )
open import L.Axioms.Basic {ℓ} using ( Lset-suc )
open import L.Rud.OrdArith {ℓ} lem using ( isLimit; isLimit-ord )
open import L.Rud.OrdBlocks {ℓ} lem using
  ( sucIter; +ω; +ω-in; +ω-out; +ω-mem; +ω-ord; +ω-limit )
open import L.Rud.Step {ℓ} lem A using
  ( Sset; Sset-in; Sset-out; Sset-mono; Sset-mem; Sset-suc; Sset-limit
  ; Sset-trans; Jset; Jset-rud; limit-succ-mem; step; step-∈ )
open import L.Rud.Bridge {ℓ} lem A using
  ( γ; γ-compute; γ-lim; γ-suc; U; U-zero; U-lim; Ul∈γl; γδ⊆U; Sset-⊆-mono
  ; Lset-zero; Sset-union-limit )
open import L.Rud.BaseBlock {ℓ} lem A using
  ( limω; ∅∈Ssetω; baseStage∈J; finiteMember; finSetMem; sTally )
open import L.Rud.SatSets {ℓ} lem A using ( module LimitFullSwitch )
open import L.Definability {ℓ} using ( module DefOf )
open import L.Choice.Finite {ℓ} lem using
  ( Tally; module Search; select; select-in; select-out; marks; marks-lookup
  ; decideOf; decide-true; decide-sound )
open import L.Ordinal.Linear {ℓ} lem using ( ord-tri )
open import L.WellOrder.Base {ℓ-suc ℓ} using ( Tri; lt; eq; gt )
open import V.Coding {ℓ} using ( #-inj′ )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using ( ℕ; zero; suc )
open import Cubical.Data.Nat.Order using ( _<_; <-trans; ¬m<m; _≟_ )
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Fin.Base as FinΣ
open import Cubical.Data.Fin.Properties using ( pigeonhole-special; Fin-fst-≡ )
open import Cubical.Data.FinData.Base using ( toℕ )
open import Cubical.Data.FinData.Properties
  using ( toℕ<n; fromℕ'; inj-toℕ; toFromId' )
open import Cubical.Data.Sigma using ( Σ≡Prop )
open import Cubical.Data.Bool using ( Bool; true; false )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( _∈ₛ_; ∈∈ₛ; ∈ₛ⟪_⟫↪_; ∈-asFiber; ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⋃_; union-ax; ω; module InfinitySet )
open InfinitySet using ( sucV; #_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ

-- Inclusion and extensional equality.
_⊆_ : S → S → Type (ℓ-suc ℓ)
u ⊆ v = (x : S) → ⟨ x ∈ˢ u ⟩ → ⟨ x ∈ˢ v ⟩

ext-⊆ : {u v : S} → u ⊆ v → v ⊆ u → u ≡ v
ext-⊆ sub sup = extensionalV (λ x → ⇔toPath (sub x) (sup x))

-- The iterated successors of zero are exactly the numerals.
sucIter∅≡# : (n : ℕ) → sucIter n ∅ ≡ # n
sucIter∅≡# zero = refl
sucIter∅≡# (suc n) = cong sucV (sucIter∅≡# n)

-- The first ω-block above zero is the first limit: +ω ∅ ≡ ω.
+ω∅≡ω : +ω ∅ ≡ ω
+ω∅≡ω = ext-⊆ sub sup
  where
  sub : +ω ∅ ⊆ ω
  sub x x∈ = PT.rec (snd (x ∈ˢ ω)) go (+ω-out ∅ x x∈)
    where
    go : Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) ∅ ⟩ → ⟨ x ∈ˢ ω ⟩
    go (n , x∈) = numeral-mem (suc n) x
      (subst (λ w → ⟨ x ∈ˢ w ⟩) (sucIter∅≡# (suc n)) x∈)
  sup : ω ⊆ +ω ∅
  sup x x∈ = PT.rec (snd (x ∈ˢ +ω ∅)) go x∈
    where
    go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ x) → ⟨ x ∈ˢ +ω ∅ ⟩
    go (m , q) = subst (λ w → ⟨ w ∈ˢ +ω ∅ ⟩) q
      (+ω-in ∅ nm (lower m) h)
      where
      nm : S
      nm = # (lower m)
      h : ⟨ nm ∈ˢ sucIter (suc (lower m)) ∅ ⟩
      h = subst (λ w → ⟨ nm ∈ˢ w ⟩)
            (sym (sucIter∅≡# (suc (lower m))))
            (self∈sucV nm)

-- The tower at zero is the first limit: γ ∅ = +ω (U ∅) = +ω ∅ = ω.
γ∅≡ω : γ ∅ ≡ ω
γ∅≡ω = subst (λ w → γ ∅ ≡ +ω w) U-zero (γ-compute ∅) ∙ +ω∅≡ω

-- ω ∈ γ 1 = +ω (γ ∅).
ω∈γ1 : ⟨ ω ∈ˢ γ (sucV ∅) ⟩
ω∈γ1 = subst (λ w → ⟨ w ∈ˢ γ (sucV ∅) ⟩) γ∅≡ω
  (subst (λ w → ⟨ γ ∅ ∈ˢ w ⟩) (sym (γ-suc ∅ ∅-ord)) (+ω-mem (γ ∅)))

-- The successor of zero is a member of ω.
1∈ω : ⟨ sucV ∅ ∈ˢ ω ⟩
1∈ω = #∈ω 1

-- ω ∈ U ω via γ 1 ⊆ U ω.
ω∈Uω : ⟨ ω ∈ˢ U ω ⟩
ω∈Uω = γδ⊆U ω (sucV ∅) 1∈ω ω ω∈γ1

-- ω lies in the tower's value at ω (transitivity of the limit ordinal γ ω).
ω∈γω : ⟨ ω ∈ˢ γ ω ⟩
ω∈γω = isLimit-ord (γ ω) (γ-lim ω) .fst {x = U ω} {y = ω} ω∈Uω (Ul∈γl ω)

-- Numerals appear in Lset ω (ord∈Lset-suc) and stages below ω are HF members.
-- The numeral for k, named (the `#` prefix does not parse inside ⟨_⟩).
nk : ℕ → S
nk k = # k

numeral∈Lsetω : (k : ℕ) → ⟨ nk k ∈ˢ Lset ω ⟩
numeral∈Lsetω k = Lset-mono {α = ω} {β = sucV (nk k)} (#∈ω (suc k))
  (ord∈Lset-suc (nk k) (numeral-ord k))

ω⊆Lsetω : ω ⊆ Lset ω
ω⊆Lsetω x x∈ = PT.rec (snd (x ∈ˢ Lset ω)) go x∈
  where
  go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ x) → ⟨ x ∈ˢ Lset ω ⟩
  go (m , q) = subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) q (numeral∈Lsetω (lower m))

numeralStage∈HF : (k : ℕ) → ⟨ Lset (# k) ∈ˢ Sset ω ⟩
numeralStage∈HF zero = subst (λ w → ⟨ w ∈ˢ Sset ω ⟩) (sym Lset-zero) ∅∈Ssetω
numeralStage∈HF (suc k) = baseStage∈J (# k) (#∈ω k) (numeralStage∈HF k)

stage∈HF : (ζ : S) → ⟨ ζ ∈ˢ ω ⟩ → ⟨ Lset ζ ∈ˢ Sset ω ⟩
stage∈HF ζ ζ∈ω = PT.rec (snd (Lset ζ ∈ˢ Sset ω)) go ζ∈ω
  where
  go : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ ζ) → ⟨ Lset ζ ∈ˢ Sset ω ⟩
  go (m , q) = subst (λ w → ⟨ Lset w ∈ˢ Sset ω ⟩) q (numeralStage∈HF (lower m))

-- Lset ω ⊆ Sset ω elementwise (union of successor stages, HF transitive).
Lsetω⊆Ssetω : Lset ω ⊆ Sset ω
Lsetω⊆Ssetω x x∈L = PT.rec (snd (x ∈ˢ Sset ω)) go (Lset-out ω x x∈L)
  where
  go : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ 𝒟ₒ (Lset δ) ⟩) → ⟨ x ∈ˢ Sset ω ⟩
  go (δ , δ∈ω , x∈𝒟) = Sset-trans ω
    (subst (λ w → ⟨ x ∈ˢ w ⟩) (sym (Lset-suc δ)) x∈𝒟)
    (baseStage∈J δ δ∈ω (stage∈HF δ δ∈ω))

-- The easy half: ω ⊆ Sset ω (numerals are hereditarily finite).
ω⊆Ssetω : ω ⊆ Sset ω
ω⊆Ssetω x x∈ = Lsetω⊆Ssetω x (ω⊆Lsetω x x∈)

-- The hard half: ordinals in HF are exactly the numerals.  Chain: a member
-- of a finite S-level is a subset of a tallied level (subset-tallied); a
-- finite ordinal is a numeral (trichotomy vs ω, the other cases refuted by
-- the finite pigeonhole); membership in Sset ω is a finite level.

-- A subset of a tallied set is tallied (marks + select, LEM).
subsetTally : (u : S) → Tally u → (y : S) → y ⊆ u → Tally y
subsetTally u t y sub = record
  { size = sel .fst
  ; item = sel .snd
  ; inside = inside'
  ; onto = onto' }
  where
  open Tally t
  d : S → Bool
  d z = decideOf (z ∈ˢ y) (lem (z ∈ˢ y))
  v : Vec Bool size
  v = marks size item d
  sel : Σ[ k ∈ ℕ ] (Fin k → S)
  sel = select size item v
  inside' : (j : Fin (sel .fst)) → ⟨ sel .snd j ∈ˢ y ⟩
  inside' j = subst (λ w → ⟨ w ∈ˢ y ⟩) (sym (out .snd .snd))
    (decide-sound (item (out .fst) ∈ˢ y) (lem (item (out .fst) ∈ˢ y))
      (sym (marks-lookup size item d (out .fst)) ∙ out .snd .fst))
    where
    out : Σ[ i ∈ Fin size ] ((lookup i v ≡ true) × (sel .snd j ≡ item i))
    out = select-out size item v j
  onto' : (x : S) → ⟨ x ∈ˢ y ⟩ → ∥ Σ[ j ∈ Fin (sel .fst) ] (sel .snd j ≡ x) ∥₁
  onto' x x∈y = PT.map atIndex (onto x (sub x x∈y))
    where
    atIndex : Σ[ i ∈ Fin size ] (item i ≡ x)
            → Σ[ j ∈ Fin (sel .fst) ] (sel .snd j ≡ x)
    atIndex (i , q) = ins .fst , (ins .snd ∙ q)
      where
      ins : Σ[ j ∈ Fin (sel .fst) ] (sel .snd j ≡ item i)
      ins = select-in size item v i
        (marks-lookup size item d i ∙ decide-true (item i ∈ˢ y)
          (lem (item i ∈ˢ y)) (subst (λ w → ⟨ w ∈ˢ y ⟩) (sym q) x∈y))

-- No tally of ω: size+1 distinct numerals among size entries (pigeonhole).
notTallyω : Tally ω → Empty.⊥
notTallyω t = i≢j i≡j
  where
  open Tally t
  Idx : Type (ℓ-suc ℓ)
  Idx = Lift {ℓ-zero} {ℓ-suc ℓ} (Fin size)
  _≺_ : Idx → Idx → Type (ℓ-suc ℓ)
  a ≺ b = Lift {ℓ-zero} {ℓ-suc ℓ} (toℕ (a .lower) < toℕ (b .lower))
  tri : (a b : Idx) → Tri (a ≺ b) (a ≡ b) (b ≺ a)
  tri a b = go (toℕ (a .lower) ≟ toℕ (b .lower))
    where
    go : NatOrder.Trichotomy (toℕ (a .lower)) (toℕ (b .lower))
       → Tri (a ≺ b) (a ≡ b) (b ≺ a)
    go (NatOrder.lt h) = lt (lift {ℓ-zero} {ℓ-suc ℓ} h)
    go (NatOrder.gt h) = gt (lift {ℓ-zero} {ℓ-suc ℓ} h)
    go (NatOrder.eq p) = eq (cong (λ x → lift {ℓ-zero} {ℓ-suc ℓ} x) (inj-toℕ p))
  irr : (a : Idx) → a ≺ a → Empty.⊥
  irr a (lift h) = ¬m<m h
  trans : (a b c : Idx) → a ≺ b → b ≺ c → a ≺ c
  trans a b c (lift h) (lift k) = lift {ℓ-zero} {ℓ-suc ℓ} (<-trans h k)
  module S = Search {A = Idx} _≺_ tri irr trans
  module O = S.Over size (λ i → lift i) (λ a → ∣ a .lower , refl ∣₁)
  eqΩ : {x y : S} → Ω
  eqΩ {x} {y} = (x ≡ y) , setIsSet x y
  pick : (k : ℕ) → Fin size
  pick k = lower (O.least (λ j → eqΩ {item (lower j)} {nk k})
    (PT.map (λ { (i , q) → lift i , q }) (onto (nk k) (#∈ω k))) .fst)
  pick-eq : (k : ℕ) → item (pick k) ≡ nk k
  pick-eq k = O.least (λ j → eqΩ {item (lower j)} {nk k})
    (PT.map (λ { (i , q) → lift i , q }) (onto (nk k) (#∈ω k))) .snd .fst
  conv : {n : ℕ} → Fin n → FinΣ.Fin n
  conv i = toℕ i , toℕ<n i
  conv⁻¹ : {n : ℕ} → FinΣ.Fin n → Fin n
  conv⁻¹ {n} k = fromℕ' n (k .fst) (k .snd)
  f : Fin (suc size) → Fin size
  f i = pick (toℕ i)
  f' : FinΣ.Fin (suc size) → FinΣ.Fin size
  f' k = conv (f (conv⁻¹ k))
  collide : Σ[ i ∈ FinΣ.Fin (suc size) ] Σ[ j ∈ FinΣ.Fin (suc size) ]
              ((i ≡ j) → Empty.⊥) × (f' i ≡ f' j)
  collide = pigeonhole-special f'
  iΣ jΣ : FinΣ.Fin (suc size)
  iΣ = collide .fst
  jΣ = collide .snd .fst
  i j : Fin (suc size)
  i = conv⁻¹ iΣ
  j = conv⁻¹ jΣ
  i≢j : (i ≡ j) → Empty.⊥
  i≢j p = collide .snd .snd .fst
    (Fin-fst-≡ (sym (toFromId' (suc size) (iΣ .fst) (iΣ .snd))
               ∙ cong toℕ p
               ∙ toFromId' (suc size) (jΣ .fst) (jΣ .snd)))
  f≡ : f' iΣ ≡ f' jΣ
  f≡ = collide .snd .snd .snd
  f≡' : f i ≡ f j
  f≡' = inj-toℕ (cong fst f≡)
  num≡ : nk (toℕ i) ≡ nk (toℕ j)
  num≡ = sym (pick-eq (toℕ i)) ∙ cong item f≡' ∙ pick-eq (toℕ j)
  nat≡ : toℕ i ≡ toℕ j
  nat≡ = #-inj′ num≡
  i≡j : i ≡ j
  i≡j = inj-toℕ nat≡

-- A finite ordinal is a numeral (trichotomy vs ω; the other cases refute).
finiteOrd→numeral : (x : S) → IsOrd x → Tally x → ⟨ x ∈ˢ ω ⟩
finiteOrd→numeral x ordx tx = go (ord-tri x ordx ω ω-ord)
  where
  open Tally tx
  go : ⟨ x ∈ˢ ω ⟩ ⊎ ((x ≡ ω) ⊎ ⟨ ω ∈ˢ x ⟩) → ⟨ x ∈ˢ ω ⟩
  go (inl h) = h
  go (inr (inl p)) = Empty.rec (notTallyω (subst Tally p tx))
  go (inr (inr h)) = Empty.rec (notTallyω (subsetTally x tx ω ω⊆x))
    where
    ω⊆x : ω ⊆ x
    ω⊆x w w∈ω = ordx .fst w∈ω h

-- Ordinal in HF is a numeral (transitive finite level, tallied, then above).
ord∈HF→∈ω : (x : S) → IsOrd x → ⟨ x ∈ˢ Sset ω ⟩ → ⟨ x ∈ˢ ω ⟩
ord∈HF→∈ω x ordx x∈S = PT.rec (snd (x ∈ˢ ω)) atLevel
  (Sset-union-limit ω limω x x∈S)
  where
  atLevel : Σ[ δ ∈ S ] (⟨ δ ∈ˢ ω ⟩ × ⟨ x ∈ˢ Sset (sucV δ) ⟩) → ⟨ x ∈ˢ ω ⟩
  atLevel (δ , δ∈ω , x∈level) = PT.rec (snd (x ∈ˢ ω)) atNumeral δ∈ω
    where
    atNumeral : Σ[ m ∈ Lift ℕ ] (# (lower m) ≡ δ) → ⟨ x ∈ˢ ω ⟩
    atNumeral (m , q) = finiteOrd→numeral x ordx xTallied
      where
      level : S
      level = Sset (sucV (nk (lower m)))
      x∈level' : ⟨ x ∈ˢ Sset (sucV (nk (lower m))) ⟩
      x∈level' = subst (λ w → ⟨ x ∈ˢ w ⟩) (cong Sset (cong sucV (sym q))) x∈level
      x⊆level : x ⊆ level
      x⊆level z z∈x = Sset-trans (sucV (nk (lower m))) {x = x} {y = z}
        z∈x x∈level'
      xTallied : Tally x
      xTallied = subsetTally (Sset (sucV (nk (lower m))))
        (sTally (suc (lower m))) x x⊆level

-- Arm A: φ-ord carves the ordinals of the carrier; over HF those are the
-- numerals (hard half above), so it carves ω, and the full switch lands it.
module Carve where
  u : S
  u = Sset ω
  utr : isTransV u
  utr = Sset-trans ω
  module DefA = DefOf u
  module RefA = DefA.Refine utr
  open RefA.Abs using ( _⊨ᵛ_ )
  φ : Formula ⟪ u ⟫ 1
  φ = φ-ord {K = ⟪ u ⟫}
  ⊨ᵛ→ord : (m : ⟪ u ⟫) → ⟨ (⟪ u ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
          → IsOrd (⟪ u ⟫↪ m)
  ⊨ᵛ→ord m sat = transB , memTransB
    where
    B : S
    B = ⟪ u ⟫↪ m
    transB : isTransV B
    transB {x} {y} y∈x x∈B = sat .fst x x∈B y y∈x
    memTransB : (x : S) → ⟨ x ∈ˢ B ⟩ → isTransV x
    memTransB x x∈B {y} {z} z∈y y∈x = sat .snd x x∈B y y∈x z z∈y
  ord→⊨ᵛ : (m : ⟪ u ⟫) → IsOrd (⟪ u ⟫↪ m)
         → ⟨ (⟪ u ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
  ord→⊨ᵛ m ord = c1 , c2
    where
    B : S
    B = ⟪ u ⟫↪ m
    c1 : (x : S) → ⟨ x ∈ˢ B ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩ → ⟨ y ∈ˢ B ⟩
    c1 x x∈B y y∈x = ord .fst y∈x x∈B
    c2 : (x : S) → ⟨ x ∈ˢ B ⟩ → (y : S) → ⟨ y ∈ˢ x ⟩
       → (z : S) → ⟨ z ∈ˢ y ⟩ → ⟨ z ∈ˢ x ⟩
    c2 x x∈B y y∈x z z∈y = ord .snd x x∈B z∈y y∈x
  carve : DefA.defSet φ ≡ ω
  carve = ext-⊆ sub₁ sub₂
    where
    sub₁ : DefA.defSet φ ⊆ ω
    sub₁ y y∈ₛ = ord∈HF→∈ω y ordy y∈u'
      where
      y∈def : ⟨ y ∈ˢ DefA.defSet φ ⟩
      y∈def = y∈ₛ
      y∈u' : ⟨ y ∈ˢ u ⟩
      y∈u' = DefA.defSet⊆A φ y y∈def
      fib : Σ[ m ∈ ⟪ u ⟫ ] (⟪ u ⟫↪ m ≡ y)
      fib = ∈-asFiber {a = y} {b = u} y∈u'
      sat : ⟨ (⟪ u ⟫↪ (fib .fst) ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
      sat = subst ⟨_⟩ (RefA.abs-defSet φ φ-ord-Δ₀ (fib .fst))
        (subst (λ w → ⟨ w ∈ˢ DefA.defSet φ ⟩) (sym (fib .snd)) y∈def)
      ordy : IsOrd y
      ordy = subst IsOrd (fib .snd) (⊨ᵛ→ord (fib .fst) sat)
    sub₂ : ω ⊆ DefA.defSet φ
    sub₂ y y∈ₛ = y∈def y∈ₛ
      where
      y∈def : ⟨ y ∈ˢ ω ⟩ → ⟨ y ∈ˢ DefA.defSet φ ⟩
      y∈def y∈ω = subst (λ w → ⟨ w ∈ˢ DefA.defSet φ ⟩) q
        (subst ⟨_⟩ (sym (RefA.abs-defSet φ φ-ord-Δ₀ m)) sat)
        where
        y∈u' : ⟨ y ∈ˢ u ⟩
        y∈u' = ω⊆Ssetω y y∈ω
        fib : Σ[ m ∈ ⟪ u ⟫ ] (⟪ u ⟫↪ m ≡ y)
        fib = ∈-asFiber {a = y} {b = u} y∈u'
        m : ⟪ u ⟫
        m = fib .fst
        q : ⟪ u ⟫↪ m ≡ y
        q = fib .snd
        sat : ⟨ (⟪ u ⟫↪ m ∷ []) ⊨ᵛ (mapFo DefA.ι φ) ⟩
        sat = ord→⊨ᵛ m (subst IsOrd (sym q) (mem-ord {A = ω} ω-ord y y∈ω))

module FS = LimitFullSwitch (U ω) (U-lim ω limω) ω limω ω∈Uω

target-A : ⟨ ω ∈ˢ Sset (U ω) ⟩
target-A = subst (λ w → ⟨ w ∈ˢ Sset (U ω) ⟩) Carve.carve
  (FS.full-switch-⊇ Carve.φ)
