# The level matrix, with the value polarity

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.Level {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using
  ( Formula; Term; var; con; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ¬̇_; ⊤̇; ⊥̇
  ; ∃̇∈; ∀̇∈; ∃̇_; ∀̇_ )
open import FOL.Manipulation.Relabelling using ( mapFo; mapTm )
open import FOL.LevyHierarchy using
  ( Δ₀; δ-∧; δ-∨; δ-⇒; δ-∀∈; δ-∃∈; δ-∈; δ-≐ )
open import FOL.Manipulation.Parameters using ( countFo )
open import FOL.Manipulation.Relabelling using ( embed )
import FOL.Absoluteness
import FOL.Semantics
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction; extensionalV )
open import V.Coding {ℓ} using ( pr )
open import V.Model {ℓ} using ( self∈sucV; pair-singleton )
open import L.Constructible {ℓ} using
  ( 𝒮ʟ; IsOrd; Lset; isL; isL-trans; 𝒟ₒ; Lset-in; Lset-out; 𝒟ₒ-intro; 𝒟ₒ-inv )
open import L.Absoluteness {ℓ} using ( Δ₀-liftFo )
open import L.Coding.Environment {ℓ} using ( Δ₀-consAt; env; cons )
open import L.Coding.EnvSet {ℓ} lem using ( Ix; envS; envOver; module Recover )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Axioms.Basic {ℓ} using ( LsetS; isL-𝒟ₒ )
open import L.Axioms.Numerals {ℓ} using ( numeralL; numeralL-fst )
open import L.Coding.Model {ℓ} using
  ( sucAtL; sucAtL-adequate; prAtL; prAtL-adequate; appAt; appAt-adequate
  ; prʟ; prʟ-fst; consAtL; consAtL-adequate
  ; envOverAt; envOverAt-transport; envSetAt; extAt-out; extAt-in; extAt-in-both
  ; tmValAt; tmValAt-out; numL; module LCode
  ; subValAt; subValAt-adequate; subValSuccAt; subValSuccAt-adequate
  ; closedAt; domAt
  ; botClauseAt; topClauseAt; negClauseAt; impClauseAt
  ; memClauseAt; eqClauseAt; forallClauseAt; existClauseAt
  ; allInClauseAt; exInClauseAt; binClauseAt; propRel
  ; interAt; unionAt; extAt
  ; arityTagAtL; arityTagPairAtL; arityTagAtL-adequate; arityTagPairAtL-adequate; tagAtL-adequate; tagAtL
  ; body∀; body∃; bodyAll; bodyEx; atomBody )
open import L.Axioms.Numerals {ℓ} using ( pairʟ; pairʟ-fst )
open import L.Coding.Shape {ℓ} using ( shapedAt )
open import L.Hierarchy {ℓ} lem using ( Values; Entries )
open import L.Condensation {ℓ} lem using
  ( Δ₀-prAtL; Δ₀-sucAtL; Δ₀-appAt
  ; tagBS; Δ₀-tagBS; keyArBS; Δ₀-keyArBS
  ; closedBS; Δ₀-closedBS; shapedBS; Δ₀-shapedBS
  ; domB; Δ₀-domB; DefinesBS; Δ₀-DefinesBS; envSetB; Δ₀-envSetB
  ; module Mem; module Eq; module And; module Or; module Imp; module Neg
  ; module Top; module Bot; module Exist; module Forall
  ; module AllIn; module ExIn; module EnvSet; module KFactsNS
  ; module ClosedAgree; module ShapedAgree; module DomainAgree
  ; module DefinesAgree; module BotAgree; module TopAgree; module NegAgree
  ; module ImpAgree
  ; module UnaryShape; module BinaryShape; module GraphEntry; module ChainZ
  ; module TmVal; module SubValB2T; module SubValSuccB2T
  ; extAtB→extAt; extAtB
  ; arTagB; arTagPairB; subValB; subValSuccB; envHypU; envHypB2; envHypB2T
  ; propBodyB; binFullAt; tmValB; atomBodyB
  ; keyU; succU )
open import L.GCH.Hull {ℓ} lem using
  ( module Cnt; erase-Δ₀; isOrd-at-p; Δ₀-isOrd-at-p; _⊨ₚ_ )
open import L.GCH.Frame {ℓ} lem using ( module W3 )
open import L.GCH.Sound {ℓ} lem using
  ( module MatrixP; module Read; read; ord-out; unwrap )
open import L.GCH.LevelRows {ℓ} lem using
  ( module Chain; tmVal-K
  ; module MemAgree′; module EqAgree′; module BndAgree′
  ; module ForallAgree′; module ExistAgree′; module AndAgree′; module OrAgree′ )
open import L.Coding.Unique {ℓ} lem using ( module Good )
open import L.Coding.Sat {ℓ} lem using ( Sat )
open import L.Coding.Table {ℓ} lem using ( keyʟ; keyʟ-shape-in )
open import L.Coding.Powerset {ℓ} lem using
  ( codeAt-out; DefinesAt; DefinesAt-out; DefinesAt-in; isCodeAt; envOne )
open import L.Coding.CodeSet {ℓ} lem using ( keyArityAtL; keyArityAtL-in; keyS; hasWitnessAt )
open import L.Coding.Uniform {ℓ} lem using ( keyBridge )
open import L.Coding.Bridge {ℓ} lem using ( asConst; defSet-Sat )
open import L.Definability {ℓ} using ( module DefOf )
open import V.Coding {ℓ} using ( #mono )
open import Cubical.Data.FinData.Properties using ( toℕ<n )

open import Cubical.Data.Nat using ( _+_ )
open import Cubical.Data.Vec using ( _∷_; []; map; lookup )
open import Cubical.Foundations.Prelude using ( cong₂; transport; subst2 )
open import Cubical.Data.Sigma using ( _×_ )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )
open import Cubical.Data.FinData using ( ¬Fin0; toℕ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties
  using ( ∈∈ₛ; ∈-asFiber; ⟪_⟫; ⟪_⟫↪; ∈ₛ⟪_⟫↪_ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( ∅; ∅-empty; ⁅_,_⁆; ⁅_⁆s; pairing-ax; module InfinitySet )
open InfinitySet {ℓ} using ( #_; sucV )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ)) using ()
open hPropStructure 𝒮ᵥ using (S; _∈ˢ_)

-- The class-carrier reading, as src/L/Condensation.lagda.md:76-77.
module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using (_^_; _⊨ᵐ_)
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The 𝒮ʟ carrier, for the syntax.  Same name as src/L/GCH/Frame.lagda.md.
module CS = hPropStructure 𝒮ʟ using (S)

-- =====================================================================
-- SLOT ARITHMETIC.  Every formula below is written at a variable
-- environment arity with its sets at slots, as src/L/Condensation.lagda.md
-- writes its rows.  The names i0..i8 are the innermost slots at any
-- arity; sh1..sh8 push an outer slot past that many binders.
-- =====================================================================

i0 : ∀ {j} → Fin (suc j)
i0 = zero
i1 : ∀ {j} → Fin (suc (suc j))
i1 = suc zero
i2 : ∀ {j} → Fin (suc (suc (suc j)))
i2 = suc (suc zero)
i3 : ∀ {j} → Fin (suc (suc (suc (suc j))))
i3 = suc (suc (suc zero))
i4 : ∀ {j} → Fin (suc (suc (suc (suc (suc j)))))
i4 = suc (suc (suc (suc zero)))
i5 : ∀ {j} → Fin (suc (suc (suc (suc (suc (suc j))))))
i5 = suc (suc (suc (suc (suc zero))))
i6 : ∀ {j} → Fin (suc (suc (suc (suc (suc (suc (suc j)))))))
i6 = suc (suc (suc (suc (suc (suc zero)))))

sh1 : ∀ {m} → Fin m → Fin (1 + m)
sh1 i = suc i
sh2 : ∀ {m} → Fin m → Fin (2 + m)
sh2 i = suc (suc i)
sh3 : ∀ {m} → Fin m → Fin (3 + m)
sh3 i = suc (suc (suc i))
sh4 : ∀ {m} → Fin m → Fin (4 + m)
sh4 i = suc (suc (suc (suc i)))
sh5 : ∀ {m} → Fin m → Fin (5 + m)
sh5 i = suc (suc (suc (suc (suc i))))
sh6 : ∀ {m} → Fin m → Fin (6 + m)
sh6 i = suc (suc (suc (suc (suc (suc i)))))
sh7 : ∀ {m} → Fin m → Fin (7 + m)
sh7 i = suc (suc (suc (suc (suc (suc (suc i))))))
sh8 : ∀ {m} → Fin m → Fin (8 + m)
sh8 i = suc (suc (suc (suc (suc (suc (suc (suc i)))))))

-- =====================================================================
-- THE PINS ON THE BOUND.  Three facts a Δ₀ sentence can force on the
-- witness set z, beyond the transitivity, pair and successor closure
-- of src/L/GCH/Sound.lagda.md `MatrixP`.
--
-- `numsAt O N0`: O is the set of numerals.  N0 (the empty tag) lies
-- in O, O is closed under successor, and every member is N0 or the
-- successor of a member.  ∈-induction reads it as O = ω.
--
-- `arNumAt C O K`: every member of the code set C has its arity
-- component in O.  This is the one fact the twelve row agreements
-- of src/L/Condensation.lagda.md demand of a code (`codesK`) that
-- no closure supplies.
--
-- `towerAt`: the environment sets of every numeral arity over w lie
-- in K, generated arity by arity.  The rows quantify their
-- environment set bounded by K, so the sets have to be there.
-- =====================================================================

numsAt : ∀ {m} → Fin m → Fin m → Formula CS.S m
numsAt O N0 =
    (var N0 ∈̇ var O)
  ∧̇ ( ∀̇∈ (var O) (∃̇∈ (var (sh1 O)) (sucAtL i1 i0))
    ∧̇ ∀̇∈ (var O) ((var i0 ≐ var (sh1 N0))
                   ∨̇ ∃̇∈ (var (sh1 O)) (sucAtL i0 i1)) )

Δ₀-numsAt : ∀ {m} (O N0 : Fin m) → Δ₀ (numsAt O N0)
Δ₀-numsAt O N0 =
  δ-∧ δ-∈ (δ-∧ (δ-∀∈ (δ-∃∈ (Δ₀-sucAtL i1 i0)))
               (δ-∀∈ (δ-∨ δ-≐ (δ-∃∈ (Δ₀-sucAtL i0 i1)))))

-- At c ∷ γ, then ar ∷ c ∷ γ, then t ∷ ar ∷ c ∷ γ: c = (ar, t) → ar ∈ O.
arNumAt : ∀ {m} → Fin m → Fin m → Fin m → Formula CS.S m
arNumAt C O K =
  ∀̇∈ (var C) (∀̇∈ (var (sh1 K)) (∀̇∈ (var (sh2 K))
    (prAtL i2 i1 i0 ⇒̇ (var i1 ∈̇ var (sh3 O)))))

Δ₀-arNumAt : ∀ {m} (C O K : Fin m) → Δ₀ (arNumAt C O K)
Δ₀-arNumAt C O K = δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-prAtL i2 i1 i0) δ-∈)))

-- THE ENVIRONMENT TOWER.  Ê is a table of pairs (n, Eₙ): at every
-- numeral arity n an entry, and every entry is the environment set of
-- its arity over w as K sees it (src/L/Condensation.lagda.md
-- `envSetB`); and Eₙ₊₁ holds the extension of every member of Eₙ by
-- every member of w.  The last clause is the value polarity: it
-- ASSERTS the extended environment, so ∈-induction on the arity reads
-- "every environment over w lies in its entry", which no closure
-- under pairs can give.  Innermost of the third clause:
-- e' ∷ x ∷ e ∷ E' ∷ E ∷ n' ∷ n ∷ γ.
towerAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Formula CS.S m
towerAt Ê O w K =
    ∀̇∈ (var O) (∃̇∈ (var (sh1 K))
      (appAt (sh2 Ê) i1 i0 ∧̇ envSetB i0 i1 (sh2 w) (sh2 K)))
  ∧̇ ( ∀̇∈ (var K) (∀̇∈ (var (sh1 K))
        (appAt (sh2 Ê) i1 i0 ⇒̇ envSetB i0 i1 (sh2 w) (sh2 K)))
    ∧̇ ∀̇∈ (var K) (∀̇∈ (var (sh1 K)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (sh3 K))
        (( appAt (sh4 Ê) i3 i1 ∧̇ ( appAt (sh4 Ê) i2 i0 ∧̇ sucAtL i3 i2 ))
        ⇒̇ ∀̇∈ (var i1) (∀̇∈ (var (sh5 w))
             (∃̇∈ (var i2) (consAtL i0 i1 i2))))))) )

Δ₀-towerAt : ∀ {m} (Ê O w K : Fin m) → Δ₀ (towerAt Ê O w K)
Δ₀-towerAt Ê O w K =
  δ-∧ (δ-∀∈ (δ-∃∈ (δ-∧ (Δ₀-appAt (sh2 Ê) i1 i0)
                        (Δ₀-envSetB i0 i1 (sh2 w) (sh2 K)))))
  (δ-∧ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (sh2 Ê) i1 i0)
                        (Δ₀-envSetB i0 i1 (sh2 w) (sh2 K)))))
       (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒
         (δ-∧ (Δ₀-appAt (sh4 Ê) i3 i1)
              (δ-∧ (Δ₀-appAt (sh4 Ê) i2 i0) (Δ₀-sucAtL i3 i2)))
         (δ-∀∈ (δ-∀∈ (δ-∃∈ (Δ₀-liftFo _ (Δ₀-consAt i0 i1 i2)))))))))))

-- The tower exists in K.
envTowerAt : ∀ {m} → Fin m → Fin m → Fin m → Formula CS.S m
envTowerAt O w K = ∃̇∈ (var K) (towerAt i0 (sh1 O) (sh1 w) (sh1 K))

Δ₀-envTowerAt : ∀ {m} (O w K : Fin m) → Δ₀ (envTowerAt O w K)
Δ₀-envTowerAt O w K = δ-∃∈ (Δ₀-towerAt i0 (sh1 O) (sh1 w) (sh1 K))

-- =====================================================================
-- THE CODE SET IS CLOSED UNDER THE CODE-FORMING OPERATIONS.  One
-- clause per constructor of the object syntax (src/FOL/Coding.lagda.md
-- `⌜_⌝`), at the key shape (arity, (tag, payload)) of
-- src/L/Coding/Table.lagda.md `keyʟ`.  The arities range over O, the
-- payload components over K, and the code produced is asked for in C.
-- With `closedBS` and `shapedBS` beside it, C is a closed shaped set
-- holding the key of every formula over w: the meta induction below
-- reads exactly these clauses.
-- =====================================================================

-- A term code: (N0, x) for a constant x ∈ w, or (N1, i) for a variable
-- index i ∈ ar.  At the slots t and ar.
tmAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Formula CS.S m
tmAt t ar w K N0 N1 =
    ∃̇∈ (var w)  (tagBS (sh1 t) (sh1 N0) i0 (sh1 K))
  ∨̇ ∃̇∈ (var ar) (tagBS (sh1 t) (sh1 N1) i0 (sh1 K))

Δ₀-tmAt : ∀ {m} (t ar w K N0 N1 : Fin m) → Δ₀ (tmAt t ar w K N0 N1)
Δ₀-tmAt t ar w K N0 N1 =
  δ-∨ (δ-∃∈ (Δ₀-tagBS (sh1 t) (sh1 N0) i0 (sh1 K)))
      (δ-∃∈ (Δ₀-tagBS (sh1 t) (sh1 N1) i0 (sh1 K)))

module Close {m : ℕ} (C O w K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where

  -- Atoms (tags N0, N1): ar ∈ O, terms t u ∈ K over ar; the code
  -- (ar, (N, (t, u))) is in C.  Innermost: s ∷ q ∷ c ∷ u ∷ t ∷ ar ∷ γ.
  atomAt : Fin m → Formula CS.S m
  atomAt N =
    ∀̇∈ (var O) (∀̇∈ (var (sh1 K)) (∀̇∈ (var (sh2 K))
      ((tmAt i1 i2 (sh3 w) (sh3 K) (sh3 N0) (sh3 N1)
        ∧̇ tmAt i0 i2 (sh3 w) (sh3 K) (sh3 N0) (sh3 N1))
      ⇒̇ ∃̇∈ (var (sh3 C)) (∃̇∈ (var (sh4 K)) (∃̇∈ (var (sh5 K))
           ( prAtL i1 i4 i3
           ∧̇ ( prAtL i0 (sh6 N) i1
             ∧̇ prAtL i2 i5 i0 )))))))

  Δ₀-atomAt : (N : Fin m) → Δ₀ (atomAt N)
  Δ₀-atomAt N =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒
      (δ-∧ (Δ₀-tmAt i1 i2 (sh3 w) (sh3 K) (sh3 N0) (sh3 N1))
           (Δ₀-tmAt i0 i2 (sh3 w) (sh3 K) (sh3 N0) (sh3 N1)))
      (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL i1 i4 i3)
                              (δ-∧ (Δ₀-prAtL i0 (sh6 N) i1)
                                   (Δ₀-prAtL i2 i5 i0)))))))))

  -- Binary connectives (tags N2, N3, N4): c₁ = (ar, a), c₂ = (ar, b)
  -- in C give (ar, (N, (a, b))) in C.  Innermost:
  -- s ∷ q ∷ c ∷ b ∷ a ∷ ar ∷ c₂ ∷ c₁ ∷ γ.
  binAt : Fin m → Formula CS.S m
  binAt N =
    ∀̇∈ (var C) (∀̇∈ (var (sh1 C)) (∀̇∈ (var (sh2 O))
      (∀̇∈ (var (sh3 K)) (∀̇∈ (var (sh4 K))
        ((prAtL i4 i2 i1 ∧̇ prAtL i3 i2 i0)
        ⇒̇ ∃̇∈ (var (sh5 C)) (∃̇∈ (var (sh6 K)) (∃̇∈ (var (suc (sh6 K)))
             ( prAtL i1 i4 i3
             ∧̇ ( prAtL i0 (sh8 N) i1
               ∧̇ prAtL i2 i5 i0 )))))))))

  Δ₀-binAt : (N : Fin m) → Δ₀ (binAt N)
  Δ₀-binAt N =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒
      (δ-∧ (Δ₀-prAtL i4 i2 i1) (Δ₀-prAtL i3 i2 i0))
      (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL i1 i4 i3)
                              (δ-∧ (Δ₀-prAtL i0 (sh8 N) i1)
                                   (Δ₀-prAtL i2 i5 i0)))))))))))

  -- Negation (tag N5): c₁ = (ar, a) in C gives (ar, (N5, a)) in C.
  -- Innermost: s ∷ c ∷ a ∷ ar ∷ c₁ ∷ γ.
  unAt : Fin m → Formula CS.S m
  unAt N =
    ∀̇∈ (var C) (∀̇∈ (var (sh1 O)) (∀̇∈ (var (sh2 K))
      (prAtL i2 i1 i0
      ⇒̇ ∃̇∈ (var (sh3 C)) (∃̇∈ (var (sh4 K))
           ( prAtL i0 (sh5 N) i2
           ∧̇ prAtL i1 i3 i0 )))))

  Δ₀-unAt : (N : Fin m) → Δ₀ (unAt N)
  Δ₀-unAt N =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-prAtL i2 i1 i0)
      (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL i0 (sh5 N) i2) (Δ₀-prAtL i1 i3 i0)))))))

  -- Constants (tags N6, N7): at every arity ar ∈ O, (ar, (N, N0)) is
  -- in C.  Innermost: s ∷ c ∷ ar ∷ γ.
  conAt : Fin m → Formula CS.S m
  conAt N =
    ∀̇∈ (var O)
      (∃̇∈ (var (sh1 C)) (∃̇∈ (var (sh2 K))
        ( prAtL i0 (sh3 N) (sh3 N0)
        ∧̇ prAtL i1 i2 i0 )))

  Δ₀-conAt : (N : Fin m) → Δ₀ (conAt N)
  Δ₀-conAt N =
    δ-∀∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL i0 (sh3 N) (sh3 N0)) (Δ₀-prAtL i1 i2 i0))))

  -- Quantifiers (tags N8, N9): c₁ = (ar', a) in C with ar' = suc ar,
  -- ar ∈ O, gives (ar, (N, a)) in C.
  -- Innermost: s ∷ c ∷ a ∷ ar' ∷ ar ∷ c₁ ∷ γ.
  quAt : Fin m → Formula CS.S m
  quAt N =
    ∀̇∈ (var C) (∀̇∈ (var (sh1 O)) (∀̇∈ (var (sh2 K)) (∀̇∈ (var (sh3 K))
      ((prAtL i3 i1 i0 ∧̇ sucAtL i2 i1)
      ⇒̇ ∃̇∈ (var (sh4 C)) (∃̇∈ (var (sh5 K))
           ( prAtL i0 (sh6 N) i2
           ∧̇ prAtL i1 i4 i0 ))))))

  Δ₀-quAt : (N : Fin m) → Δ₀ (quAt N)
  Δ₀-quAt N =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒
      (δ-∧ (Δ₀-prAtL i3 i1 i0) (Δ₀-sucAtL i2 i1))
      (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL i0 (sh6 N) i2) (Δ₀-prAtL i1 i4 i0))))))))

  -- Bounded quantifiers (tags N10, N11): a term t over ar and
  -- c₁ = (ar', a) in C with ar' = suc ar give (ar, (N, (t, a))) in C.
  -- Innermost: s ∷ q ∷ c ∷ a ∷ t ∷ ar' ∷ ar ∷ c₁ ∷ γ.
  bqAt : Fin m → Formula CS.S m
  bqAt N =
    ∀̇∈ (var C) (∀̇∈ (var (sh1 O)) (∀̇∈ (var (sh2 K))
      (∀̇∈ (var (sh3 K)) (∀̇∈ (var (sh4 K))
        (( tmAt i1 i3 (sh5 w) (sh5 K) (sh5 N0) (sh5 N1)
         ∧̇ ( prAtL i4 i2 i0 ∧̇ sucAtL i3 i2 ))
        ⇒̇ ∃̇∈ (var (sh5 C)) (∃̇∈ (var (sh6 K)) (∃̇∈ (var (suc (sh6 K)))
             ( prAtL i1 i4 i3
             ∧̇ ( prAtL i0 (sh8 N) i1
               ∧̇ prAtL i2 i6 i0 )))))))))

  Δ₀-bqAt : (N : Fin m) → Δ₀ (bqAt N)
  Δ₀-bqAt N =
    δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-∀∈ (δ-⇒
      (δ-∧ (Δ₀-tmAt i1 i3 (sh5 w) (sh5 K) (sh5 N0) (sh5 N1))
           (δ-∧ (Δ₀-prAtL i4 i2 i0) (Δ₀-sucAtL i3 i2)))
      (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-prAtL i1 i4 i3)
                              (δ-∧ (Δ₀-prAtL i0 (sh8 N) i1)
                                   (Δ₀-prAtL i2 i6 i0)))))))))))

  closeAt : Formula CS.S m
  closeAt =
    atomAt N0 ∧̇ ( atomAt N1 ∧̇ ( binAt N2 ∧̇ ( binAt N3 ∧̇ ( binAt N4
    ∧̇ ( unAt N5 ∧̇ ( conAt N6 ∧̇ ( conAt N7 ∧̇ ( quAt N8 ∧̇ ( quAt N9
    ∧̇ ( bqAt N10 ∧̇ bqAt N11 ))))))))))

  Δ₀-closeAt : Δ₀ closeAt
  Δ₀-closeAt =
    δ-∧ (Δ₀-atomAt N0) (δ-∧ (Δ₀-atomAt N1) (δ-∧ (Δ₀-binAt N2)
    (δ-∧ (Δ₀-binAt N3) (δ-∧ (Δ₀-binAt N4) (δ-∧ (Δ₀-unAt N5)
    (δ-∧ (Δ₀-conAt N6) (δ-∧ (Δ₀-conAt N7) (δ-∧ (Δ₀-quAt N8)
    (δ-∧ (Δ₀-quAt N9) (δ-∧ (Δ₀-bqAt N10) (Δ₀-bqAt N11)))))))))))

-- =====================================================================
-- THE TWELVE SATISFACTION ROWS, in the order of
-- src/L/Coding/Unique.lagda.md `Good.Clauses`.  Each is the bounded
-- row of src/L/Condensation.lagda.md at the slots C (code set), T
-- (table), B (carrier), its tag slot and K, with the term tags N0 N1.
-- =====================================================================

twelveAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
         → Formula CS.S m
twelveAt C T B K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
    Mem.memBndAt C T B N0 K N0 N1
  ∧̇ ( Eq.eqBndAt C T B N1 K N0 N1
  ∧̇ ( And.andBndAt C T B N2 K
  ∧̇ ( Or.orBndAt C T B N3 K
  ∧̇ ( Imp.impBndAt C T B N4 K
  ∧̇ ( Neg.negBndAt C T B N5 K
  ∧̇ ( Top.topBndAt C T B N6 K
  ∧̇ ( Bot.botBndAt C T B N7 K
  ∧̇ ( Exist.existBndAt C T B N8 K
  ∧̇ ( Forall.forallBndAt C T B N9 K
  ∧̇ ( AllIn.allInBndAt C T B N10 K N0 N1
  ∧̇   ExIn.exInBndAt C T B N11 K N0 N1 ))))))))))

Δ₀-twelveAt : ∀ {m} (C T B K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            → Δ₀ (twelveAt C T B K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11)
Δ₀-twelveAt C T B K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 =
    δ-∧ (Mem.Δ₀-memBndAt C T B N0 K N0 N1)
  ( δ-∧ (Eq.Δ₀-eqBndAt C T B N1 K N0 N1)
  ( δ-∧ (And.Δ₀-andBndAt C T B N2 K)
  ( δ-∧ (Or.Δ₀-orBndAt C T B N3 K)
  ( δ-∧ (Imp.Δ₀-impBndAt C T B N4 K)
  ( δ-∧ (Neg.Δ₀-negBndAt C T B N5 K)
  ( δ-∧ (Top.Δ₀-topBndAt C T B N6 K)
  ( δ-∧ (Bot.Δ₀-botBndAt C T B N7 K)
  ( δ-∧ (Exist.Δ₀-existBndAt C T B N8 K)
  ( δ-∧ (Forall.Δ₀-forallBndAt C T B N9 K)
  ( δ-∧ (AllIn.Δ₀-allInBndAt C T B N10 K N0 N1)
        (ExIn.Δ₀-exInBndAt C T B N11 K N0 N1) ))))))))))

-- =====================================================================
-- THE DEFINABLE-POWERSET ROW, WITH THE VALUE POLARITY.  d = Def(w):
-- there are, in K, a code set C and a table T such that C is closed,
-- shaped over w, of numeral arities and closed under the code-forming
-- operations; T is total on C, the environment sets exist, and the
-- twelve rows hold; and then
--   `memAt`: every x ∈ d is cut from w by the value of T at some
--            arity-one code of C, and
--   `allAt`: every arity-one code of C has its value in K and cuts
--            some x ∈ d from w.
-- The first half is the soundness polarity; the second is the
-- completeness polarity, bounded by the VALUE d and the code set C
-- and never by K alone (dev/literature/devlin-II5.md:240-250).
-- =====================================================================

-- At x ∷ γ, c ∷ x ∷ γ, v ∷ c ∷ x ∷ γ.
memAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
      → Formula CS.S m
memAt d w C T K N0 N1 =
  ∀̇∈ (var d) (∃̇∈ (var (sh1 C)) (∃̇∈ (var (sh2 K))
    ( keyArBS i1 (sh3 N1) (sh3 K)
    ∧̇ ( appAt (sh3 T) i1 i0
      ∧̇ DefinesBS i2 (sh3 w) i0 (sh3 K) (sh3 N0) ))))

Δ₀-memAt : ∀ {m} (d w C T K N0 N1 : Fin m) → Δ₀ (memAt d w C T K N0 N1)
Δ₀-memAt d w C T K N0 N1 =
  δ-∀∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-keyArBS i1 (sh3 N1) (sh3 K))
    (δ-∧ (Δ₀-appAt (sh3 T) i1 i0)
         (Δ₀-DefinesBS i2 (sh3 w) i0 (sh3 K) (sh3 N0))))))

-- At c ∷ γ, v ∷ c ∷ γ, x ∷ v ∷ c ∷ γ.
allAt : ∀ {m} → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → Fin m
      → Formula CS.S m
allAt d w C T K N0 N1 =
  ∀̇∈ (var C)
    (keyArBS i0 (sh1 N1) (sh1 K)
    ⇒̇ ∃̇∈ (var (sh1 K))
        ( appAt (sh2 T) i1 i0
        ∧̇ ∃̇∈ (var (sh2 d)) (DefinesBS i0 (sh3 w) i1 (sh3 K) (sh3 N0)) ))

Δ₀-allAt : ∀ {m} (d w C T K N0 N1 : Fin m) → Δ₀ (allAt d w C T K N0 N1)
Δ₀-allAt d w C T K N0 N1 =
  δ-∀∈ (δ-⇒ (Δ₀-keyArBS i0 (sh1 N1) (sh1 K))
    (δ-∃∈ (δ-∧ (Δ₀-appAt (sh2 T) i1 i0)
               (δ-∃∈ (Δ₀-DefinesBS i0 (sh3 w) i1 (sh3 K) (sh3 N0))))))

module DefV {m : ℕ} (d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where

  -- The body at T ∷ C ∷ γ: C is slot 1, T is slot 0.
  private
    C T : Fin (2 + m)
    C = i1
    T = i0

  body : Formula CS.S (2 + m)
  body =
      closedBS C (sh2 K) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                 (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
    ∧̇ ( shapedBS C (sh2 w) (sh2 K)
          (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
          (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
    ∧̇ ( arNumAt C (sh2 O) (sh2 K)
    ∧̇ ( Close.closeAt {2 + m} C (sh2 O) (sh2 w) (sh2 K)
          (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
          (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
    ∧̇ ( domB T C (sh2 K)
    ∧̇ ( envTowerAt (sh2 O) (sh2 w) (sh2 K)
    ∧̇ ( twelveAt C T (sh2 w) (sh2 K)
          (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
          (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
    ∧̇ ( memAt (sh2 d) (sh2 w) C T (sh2 K) (sh2 N0) (sh2 N1)
    ∧̇   allAt (sh2 d) (sh2 w) C T (sh2 K) (sh2 N0) (sh2 N1) )))))))

  Δ₀-body : Δ₀ body
  Δ₀-body =
      δ-∧ (Δ₀-closedBS C (sh2 K) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                         (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11))
    ( δ-∧ (Δ₀-shapedBS C (sh2 w) (sh2 K)
             (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
             (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11))
    ( δ-∧ (Δ₀-arNumAt C (sh2 O) (sh2 K))
    ( δ-∧ (Close.Δ₀-closeAt {2 + m} C (sh2 O) (sh2 w) (sh2 K)
             (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
             (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11))
    ( δ-∧ (Δ₀-domB T C (sh2 K))
    ( δ-∧ (Δ₀-envTowerAt (sh2 O) (sh2 w) (sh2 K))
    ( δ-∧ (Δ₀-twelveAt C T (sh2 w) (sh2 K)
             (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
             (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11))
    ( δ-∧ (Δ₀-memAt (sh2 d) (sh2 w) C T (sh2 K) (sh2 N0) (sh2 N1))
          (Δ₀-allAt (sh2 d) (sh2 w) C T (sh2 K) (sh2 N0) (sh2 N1)) )))))))

  -- SEALED (P-t).  The row is thousands of nodes and it sits under
  -- three more binders in the step; every conversion that reaches it
  -- through `_⊨_` would normalise it whole.  The two readers are the
  -- official unfolding.
  opaque
    defAt : Formula CS.S m
    defAt = ∃̇∈ (var K) (∃̇∈ (var (sh1 K)) body)

  opaque
    unfolding defAt

    Δ₀-defAt : Δ₀ defAt
    Δ₀-defAt = δ-∃∈ (δ-∃∈ Δ₀-body)

    defAt-out : (γ : CS.S ^ m) → ⟨ γ ⊨ defAt ⟩
              → ⟨ γ ⊨ ∃̇∈ (var K) (∃̇∈ (var (sh1 K)) body) ⟩
    defAt-out γ h = h

    defAt-in : (γ : CS.S ^ m) → ⟨ γ ⊨ ∃̇∈ (var K) (∃̇∈ (var (sh1 K)) body) ⟩
             → ⟨ γ ⊨ defAt ⟩
    defAt-in γ h = h

-- =====================================================================
-- THE STEP, THE APPROXIMATION AND THE GRAPH, WITH THE VALUE POLARITY.
-- The shape of src/L/Coding/Sequence.lagda.md `StepAt`, `ApproxAt`,
-- `LsetGraphAt`, bounded by K, with the step's extension frame split
-- into its two polarities and the definable powerset ASSERTED to
-- exist in K on the completeness side.
-- =====================================================================

module StepV {m : ℕ} (v b f K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where

  -- Soundness half: every x ∈ v lies in some d = Def(w) for a recorded
  -- (c, w) ∈ f with c ∈ b.  Innermost: d ∷ w ∷ c ∷ x ∷ γ.
  intoAt : Formula CS.S m
  intoAt =
    ∀̇∈ (var v) (∃̇∈ (var (sh1 b)) (∃̇∈ (var (sh2 K)) (∃̇∈ (var (sh3 K))
      ( appAt (sh4 f) i2 i1
      ∧̇ ( DefV.defAt {4 + m} i0 i1 (sh4 O) (sh4 K)
            (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
            (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11)
        ∧̇ (var i3 ∈̇ var i0) )))))

  -- Completeness half: every recorded (c, w) ∈ f with c ∈ b has, in K,
  -- a d = Def(w), and d ⊆ v.  Innermost: d ∷ w ∷ c ∷ γ, then x ∷ d ∷ w ∷ c ∷ γ.
  overAt : Formula CS.S m
  overAt =
    ∀̇∈ (var b) (∀̇∈ (var (sh1 K))
      (appAt (sh2 f) i1 i0
      ⇒̇ ∃̇∈ (var (sh2 K))
          ( DefV.defAt {3 + m} i0 i1 (sh3 O) (sh3 K)
              (sh3 N0) (sh3 N1) (sh3 N2) (sh3 N3) (sh3 N4) (sh3 N5)
              (sh3 N6) (sh3 N7) (sh3 N8) (sh3 N9) (sh3 N10) (sh3 N11)
          ∧̇ ∀̇∈ (var i0) (var i0 ∈̇ var (sh4 v)) )))

  stepAt : Formula CS.S m
  stepAt = intoAt ∧̇ overAt

  Δ₀-stepAt : Δ₀ stepAt
  Δ₀-stepAt =
    δ-∧ (δ-∀∈ (δ-∃∈ (δ-∃∈ (δ-∃∈ (δ-∧ (Δ₀-appAt (sh4 f) i2 i1)
          (δ-∧ (DefV.Δ₀-defAt {4 + m} i0 i1 (sh4 O) (sh4 K)
                  (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
                  (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11))
               δ-∈))))))
        (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (sh2 f) i1 i0)
          (δ-∃∈ (δ-∧ (DefV.Δ₀-defAt {3 + m} i0 i1 (sh3 O) (sh3 K)
                        (sh3 N0) (sh3 N1) (sh3 N2) (sh3 N3) (sh3 N4) (sh3 N5)
                        (sh3 N6) (sh3 N7) (sh3 N8) (sh3 N9) (sh3 N10) (sh3 N11))
                     (δ-∀∈ δ-∈))))))

module ApproxV {m : ℕ} (f a K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where

  -- f is defined exactly on a, and every recorded (c, w) ∈ f, with c
  -- and w in K, has w the step at c from f.  Innermost: w ∷ c ∷ γ.
  approxAt : Formula CS.S m
  approxAt =
      domB f a K
    ∧̇ ∀̇∈ (var K) (∀̇∈ (var (sh1 K))
        (appAt (sh2 f) i1 i0
        ⇒̇ StepV.stepAt {2 + m} i0 i1 (sh2 f) (sh2 K) (sh2 O)
             (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
             (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)))

  Δ₀-approxAt : Δ₀ approxAt
  Δ₀-approxAt =
    δ-∧ (Δ₀-domB f a K)
        (δ-∀∈ (δ-∀∈ (δ-⇒ (Δ₀-appAt (sh2 f) i1 i0)
          (StepV.Δ₀-stepAt {2 + m} i0 i1 (sh2 f) (sh2 K) (sh2 O)
             (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
             (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)))))

module GraphV {m : ℕ} (w b K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where

  -- There is, in K, an approximation f on b whose step at b is w.
  graphAt : Formula CS.S m
  graphAt =
    ∃̇∈ (var K)
      ( ApproxV.approxAt {1 + m} i0 (sh1 b) (sh1 K) (sh1 O)
          (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
          (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11)
      ∧̇ StepV.stepAt {1 + m} (sh1 w) (sh1 b) i0 (sh1 K) (sh1 O)
          (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
          (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11) )

  Δ₀-graphAt : Δ₀ graphAt
  Δ₀-graphAt =
    δ-∃∈ (δ-∧ (ApproxV.Δ₀-approxAt {1 + m} i0 (sh1 b) (sh1 K) (sh1 O)
                 (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                 (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11))
              (StepV.Δ₀-stepAt {1 + m} (sh1 w) (sh1 b) i0 (sh1 K) (sh1 O)
                 (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                 (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11)))

-- =====================================================================
-- THE MATRIX.  The pins of src/L/GCH/Sound.lagda.md `MatrixP` (K
-- transitive, closed under pairs and successor, the twelve tags the
-- twelve numerals), the numeral pin on the O slot, and the graph.
-- =====================================================================

module MatrixV {m : ℕ} (w b K O : Fin m)
               (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m) where

  module P = MatrixP {m} w b K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 using (pairK; pins; sucK; transK; Δ₀-pairK; Δ₀-pins; Δ₀-sucK; Δ₀-transK)
  module G = GraphV {m} w b K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 using (graphAt; Δ₀-graphAt)

  -- The value and the parameter lie in the witness.
  matrix : Formula CS.S m
  matrix = P.transK ∧̇ ( P.pairK ∧̇ ( P.sucK ∧̇ ( P.pins
         ∧̇ ( numsAt O N0 ∧̇ ( (var w ∈̇ var K) ∧̇ ( (var b ∈̇ var K)
         ∧̇ G.graphAt ))))))

  Δ₀-matrix : Δ₀ matrix
  Δ₀-matrix =
    δ-∧ P.Δ₀-transK (δ-∧ P.Δ₀-pairK (δ-∧ P.Δ₀-sucK (δ-∧ P.Δ₀-pins
      (δ-∧ (Δ₀-numsAt O N0) (δ-∧ δ-∈ (δ-∧ δ-∈ G.Δ₀-graphAt))))))

-- =====================================================================
-- THE THREE-SLOT FORM.  Sixteen innermost slots: the twelve tags, O,
-- a, p, z.  Thirteen bounded existentials over z, exactly as
-- src/L/GCH/Sound.lagda.md `W3′` spends twelve.
-- =====================================================================

module W3V where

  n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 oo ww bb kk : Fin 16
  n0  = zero
  n1  = suc zero
  n2  = suc (suc zero)
  n3  = suc (suc (suc zero))
  n4  = suc (suc (suc (suc zero)))
  n5  = suc (suc (suc (suc (suc zero))))
  n6  = suc (suc (suc (suc (suc (suc zero)))))
  n7  = suc (suc (suc (suc (suc (suc (suc zero))))))
  n8  = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
  n9  = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
  n10 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  n11 = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
  oo  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
  ww  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
  bb  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
  kk  = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))

  module Mx = MatrixV {16} ww bb kk oo n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 using (matrix; Δ₀-matrix; module P)

  open W3 using ( wrap; δ-wrap )

  -- SEALED, for the reason src/L/GCH/Sound.lagda.md:120-127 seals its
  -- `inner`: the matrix is thousands of nodes and the thirteen wraps
  -- would normalise it thirteen times.
  opaque
    inner : Formula CS.S 16
    inner = Mx.matrix

  opaque
    unfolding inner

    Δ₀-inner : Δ₀ inner
    Δ₀-inner = Mx.Δ₀-matrix

    inner-out : (γ : CS.S ^ 16) → ⟨ γ ⊨ inner ⟩ → ⟨ γ ⊨ Mx.matrix ⟩
    inner-out γ h = h

    inner-in : (γ : CS.S ^ 16) → ⟨ γ ⊨ Mx.matrix ⟩ → ⟨ γ ⊨ inner ⟩
    inner-in γ h = h

  s15 = wrap {14} inner
  s14 = wrap {13} s15
  s13 = wrap {12} s14
  s12 = wrap {11} s13
  s11 = wrap {10} s12
  s10 = wrap {9}  s11
  s9  = wrap {8}  s10
  s8  = wrap {7}  s9
  s7  = wrap {6}  s8
  s6  = wrap {5}  s7
  s5  = wrap {4}  s6
  s4  = wrap {3}  s5
  three : Formula CS.S 3
  three = wrap {2} s4

  Δ₀-three : Δ₀ three
  Δ₀-three =
    δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap
      (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap (δ-wrap Δ₀-inner))))))))))))

  opaque
    unfolding inner DefV.defAt

    count-three : countFo three ≡ 0
    count-three = refl

  erased : Formula (⊥* {ℓ-suc ℓ}) 3
  erased = Cnt.erase three count-three

  Δ₀-erased : Δ₀ erased
  Δ₀-erased = erase-Δ₀ three count-three Δ₀-three

-- THE LEVEL DESCRIPTION, at the consumer's slot order (a, p, z):
-- p is an ordinal, and the pinned graph holds with witness z.
levelFo : Formula (⊥* {ℓ-suc ℓ}) 3
levelFo = isOrd-at-p ∧̇ W3V.erased

Δ₀-levelFo : Δ₀ levelFo
Δ₀-levelFo = δ-∧ Δ₀-isOrd-at-p W3V.Δ₀-erased
```

```agda
-- =====================================================================
-- STEP 2.  THE CLOSURE FACTS.  What the pins say about the bound K
-- and the numeral set O, as one record over the two VALUES, so that
-- every reading at a deeper environment carries the same record.
-- =====================================================================

-- The closure facts, as one product.  perf: as a record this blew the
-- heap at 8 GB in 100 s; the record checker normalises the field types
-- and `prʟ`, `sucV` and `_∈_` unfold without end.  A product is never
-- normalised.
KC : (Kv Ov : V ℓ) → Type (ℓ-suc ℓ)
KC Kv Ov =
    ((x y : V ℓ) → ⟨ x ∈ Kv ⟩ → ⟨ y ∈ x ⟩ → ⟨ y ∈ Kv ⟩)
  × ( ((a b : CS.S) → ⟨ fst a ∈ Kv ⟩ → ⟨ fst b ∈ Kv ⟩ → ⟨ fst (prʟ a b) ∈ Kv ⟩)
  × ( ((a : CS.S) → ⟨ fst a ∈ Kv ⟩ → ⟨ sucV (fst a) ∈ Kv ⟩)
  × ( ((k : ℕ) → ⟨ fst (numeralL k) ∈ Kv ⟩)
  × ( ((k : ℕ) → ⟨ fst (numeralL k) ∈ Ov ⟩)
  × ( ((x : V ℓ) → ⟨ x ∈ Ov ⟩ → ∥ Σ[ k ∈ ℕ ] (x ≡ fst (numeralL k)) ∥₁)
  × ⟨ Ov ∈ Kv ⟩ )))))

module KC (Kv Ov : V ℓ) (kc : KC Kv Ov) where
  transK = kc .fst
  pairK = kc .snd .fst
  sucK = kc .snd .snd .fst
  numK = kc .snd .snd .snd .fst
  numO = kc .snd .snd .snd .snd .fst
  O-num = kc .snd .snd .snd .snd .snd .fst
  OK = kc .snd .snd .snd .snd .snd .snd

-- The twelve tag slots hold the twelve numerals, at an environment.
record Tags {m : ℕ} (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
            (γ : CS.S ^ m) : Type (ℓ-suc ℓ) where
  field
    t0 : fst (lookup N0 γ) ≡ fst (numeralL 0)
    t1 : fst (lookup N1 γ) ≡ fst (numeralL 1)
    t2 : fst (lookup N2 γ) ≡ fst (numeralL 2)
    t3 : fst (lookup N3 γ) ≡ fst (numeralL 3)
    t4 : fst (lookup N4 γ) ≡ fst (numeralL 4)
    t5 : fst (lookup N5 γ) ≡ fst (numeralL 5)
    t6 : fst (lookup N6 γ) ≡ fst (numeralL 6)
    t7 : fst (lookup N7 γ) ≡ fst (numeralL 7)
    t8 : fst (lookup N8 γ) ≡ fst (numeralL 8)
    t9 : fst (lookup N9 γ) ≡ fst (numeralL 9)
    t10 : fst (lookup N10 γ) ≡ fst (numeralL 10)
    t11 : fst (lookup N11 γ) ≡ fst (numeralL 11)
open Tags using (t0; t1; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11)

-- The same record one element deeper: every lookup is definitionally
-- the outer one.
tagsCons : {m : ℕ} (N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
           (γ : CS.S ^ m) (c : CS.S)
         → Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
         → Tags {1 + m} (suc N0) (suc N1) (suc N2) (suc N3) (suc N4) (suc N5)
             (suc N6) (suc N7) (suc N8) (suc N9) (suc N10) (suc N11) (c ∷ γ)
tagsCons N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ c t = record
  { t0 = t .t0 ; t1 = t .t1 ; t2 = t .t2 ; t3 = t .t3
  ; t4 = t .t4 ; t5 = t .t5 ; t6 = t .t6 ; t7 = t .t7
  ; t8 = t .t8 ; t9 = t .t9 ; t10 = t .t10 ; t11 = t .t11 }

-- A member of a class-carrier element, packaged as one.
down : (x : CS.S) (y : V ℓ) → ⟨ y ∈ fst x ⟩ → CS.S
down x y y∈x = y , isL-trans {x = fst x} {y = y} y∈x (snd x)

-- The two atoms, read.
app-out : ∀ {n} (f x y : Fin n) (γ : CS.S ^ n) → ⟨ γ ⊨ appAt f x y ⟩
        → ⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ) ⟩
app-out f x y γ h = subst ⟨_⟩ (appAt-adequate f x y γ) h

app-in : ∀ {n} (f x y : Fin n) (γ : CS.S ^ n)
       → ⟨ pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ) ⟩
       → ⟨ γ ⊨ appAt f x y ⟩
app-in f x y γ h = subst ⟨_⟩ (sym (appAt-adequate f x y γ)) h

pr-out : ∀ {n} (q u v : Fin n) (γ : CS.S ^ n) → ⟨ γ ⊨ prAtL q u v ⟩
       → fst (lookup q γ) ≡ pr (fst (lookup u γ)) (fst (lookup v γ))
pr-out q u v γ h = subst ⟨_⟩ (prAtL-adequate q u v γ) h

suc-out : ∀ {n} (i j : Fin n) (γ : CS.S ^ n) → ⟨ γ ⊨ sucAtL i j ⟩
        → fst (lookup j γ) ≡ sucV (fst (lookup i γ))
suc-out i j γ h = subst ⟨_⟩ (sucAtL-adequate i j γ) h

-- The empty environment is the empty set.
env0≡∅ : (g : Fin 0 → V ℓ) → env g ≡ ∅
env0≡∅ g = extensionalV {a = env g} {b = ∅} (λ x → ⇔toPath (fwd x) (bwd x))
  where
  fwd : (x : V ℓ) → ⟨ x ∈ env g ⟩ → ⟨ x ∈ ∅ ⟩
  fwd x = PT.rec (snd (x ∈ ∅)) (λ { (li , _) → Empty.rec (¬Fin0 (lower li)) })
  bwd : (x : V ℓ) → ⟨ x ∈ ∅ ⟩ → ⟨ x ∈ env g ⟩
  bwd x h = Empty.rec (∅-empty x (∈∈ₛ {a = x} {b = ∅} .fst h))

-- =====================================================================
-- THE TOWER, READ.  Every environment over w of a numeral arity lies
-- in every entry at that arity (an induction on the arity through
-- the cons clause), so the true environment set of that arity IS the
-- entry, and so lies in K; and so does the extension of any such
-- environment by a member of w.  These are the ties `envK`, `envInK`
-- and `consK` of the row agreements, at any environment that holds
-- the arity numeral and the carrier.
-- =====================================================================

module Tower {m : ℕ} (Ê O w K : Fin m) (γ : CS.S ^ m)
             (kc : KC (fst (lookup K γ)) (fst (lookup O γ)))
             (ÊK : ⟨ fst (lookup Ê γ) ∈ fst (lookup K γ) ⟩)
             (h : ⟨ γ ⊨ towerAt Ê O w K ⟩) where

  private
    Kv Ov Êv Wv : V ℓ
    Kv = fst (lookup K γ)
    Ov = fst (lookup O γ)
    Êv = fst (lookup Ê γ)
    Wv = fst (lookup w γ)

    W : CS.S
    W = lookup w γ

    InK : V ℓ → Type (ℓ-suc ℓ)
    InK x = ⟨ x ∈ Kv ⟩

  module C = KC Kv Ov kc using (numK; numO; transK)
  module Z = Chain Kv C.transK using (sndK)

  arityK : (N v : CS.S) → ⟨ fst v ∈ fst N ⟩ → InK (fst N) → InK (fst v)
  arityK N v h' hN = C.transK (fst N) (fst v) hN h'

  nS : ℕ → CS.S
  nS = numeralL

  Entry : ℕ → CS.S → Type (ℓ-suc ℓ)
  Entry n E = ⟨ pr (fst (nS n)) (fst E) ∈ Êv ⟩

  entryK : (n : ℕ) (E : CS.S) → Entry n E → InK (fst E)
  entryK n E p = Z.sndK Êv (fst (nS n)) (fst E) ÊK p

  -- Every entry is the bounded environment set of its arity.
  entry-bnd : (n : ℕ) (E : CS.S) → Entry n E
            → ⟨ (E ∷ nS n ∷ γ) ⊨ envSetB i0 i1 (sh2 w) (sh2 K) ⟩
  entry-bnd n E p =
    h .snd .fst (nS n) (C.numK n) E (entryK n E p)
      (app-in (sh2 Ê) i1 i0 (E ∷ nS n ∷ γ) p)

  some-entry : (n : ℕ) → ∥ Σ[ E ∈ CS.S ] Entry n E ∥₁
  some-entry n =
    PT.map (λ { (E , (_ , (ap , _))) → E , app-out (sh2 Ê) i1 i0 (E ∷ nS n ∷ γ) ap })
      (h .fst (nS n) (C.numO n))

  -- The cons clause, read.
  cons-in : (n : ℕ) (E E' e x : CS.S) → Entry n E → Entry (suc n) E'
          → ⟨ fst e ∈ fst E ⟩ → ⟨ fst x ∈ Wv ⟩
          → ∥ Σ[ e' ∈ CS.S ] (⟨ fst e' ∈ fst E' ⟩
               × ⟨ (e' ∷ x ∷ e ∷ E' ∷ E ∷ nS (suc n) ∷ nS n ∷ γ) ⊨ consAtL i0 i1 i2 ⟩) ∥₁
  cons-in n E E' e x p p' e∈ x∈ =
    h .snd .snd (nS n) (C.numK n) (nS (suc n)) (C.numK (suc n))
      E (entryK n E p) E' (entryK (suc n) E' p')
      ( app-in (sh4 Ê) i3 i1 (E' ∷ E ∷ nS (suc n) ∷ nS n ∷ γ) p
      , ( app-in (sh4 Ê) i2 i0 (E' ∷ E ∷ nS (suc n) ∷ nS n ∷ γ) p'
        , subst ⟨_⟩ (sym (sucAtL-adequate i3 i2 (E' ∷ E ∷ nS (suc n) ∷ nS n ∷ γ)))
            (numeralL-fst (suc n) ∙ cong sucV (sym (numeralL-fst n))) ))
      e e∈ x x∈

  -- The members of w as an index type, and the environments they name.
  ι : ⟪ Wv ⟫ → V ℓ
  ι = ⟪ Wv ⟫↪

  ι∈ : (q : ⟪ Wv ⟫) → ⟨ ι q ∈ Wv ⟩
  ι∈ q = ∈∈ₛ {a = ι q} {b = Wv} .snd (∈ₛ⟪ Wv ⟫↪ q)

  Ev : {n : ℕ} → Ix W n → CS.S
  Ev g = envS W g

  -- EVERY ENVIRONMENT OVER w OF ARITY n LIES IN EVERY ENTRY AT n.
  all-in : (n : ℕ) (g : Ix W n) (En : CS.S) → Entry n En → ⟨ fst (Ev g) ∈ fst En ⟩
  all-in zero g En p = entry-bnd zero En p .snd (Ev g) EgK hb
    where
    e0 : fst (Ev g) ≡ ∅
    e0 = env0≡∅ (λ i → ι (g i))
    EgK : InK (fst (Ev g))
    EgK = subst InK (numeralL-fst 0 ∙ sym e0) (C.numK 0)
    -- Any environment over w at arity zero is empty, hence in K.
    envInK0 : (z : CS.S) → ⟨ (z ∷ En ∷ nS zero ∷ γ) ⊨ envOverAt zero (suc i1) (suc (sh2 w)) ⟩
            → InK (fst z)
    envInK0 z hz = subst InK (numeralL-fst 0 ∙ sym (R.recovers ∙ env0≡∅ _)) (C.numK 0)
      where
      module R = Recover W zero (z ∷ En ∷ nS zero ∷ γ) zero (suc i1) (suc (sh2 w))
                   (numeralL-fst 0) refl hz using (g; recovers)
    module ES = EnvSet {2 + m} i0 i1 (sh2 w) (sh2 K) (En ∷ nS zero ∷ γ)
                  arityK (entryK zero En p) (C.numK 0) envInK0 using (back; bnd→over; over→bnd; φB)
    hov : ⟨ (Ev g ∷ En ∷ nS zero ∷ γ) ⊨ envOverAt zero (suc i1) (suc (sh2 w)) ⟩
    hov = envOverAt-transport (W ∷ (# zero , numL zero) ∷ Ev g ∷ []) (Ev g ∷ En ∷ nS zero ∷ γ)
            (suc (suc zero)) (suc zero) zero zero (suc i1) (suc (sh2 w))
            refl (sym (numeralL-fst 0)) refl (envOver W g)
    hb : ⟨ (Ev g ∷ En ∷ nS zero ∷ γ) ⊨ ES.φB ⟩
    hb = ES.over→bnd (Ev g) EgK hov
  all-in (suc n) g En p =
    PT.rec (snd (fst (Ev g) ∈ fst En)) step (some-entry n)
    where
    tl : Ix W n
    tl i = g (suc i)
    x0 : CS.S
    x0 = down W (ι (g zero)) (ι∈ (g zero))
    step : Σ[ En' ∈ CS.S ] Entry n En' → ⟨ fst (Ev g) ∈ fst En ⟩
    step (En' , p') = PT.rec (snd (fst (Ev g) ∈ fst En)) got
      (cons-in n En' En (Ev tl) x0 p' p (all-in n tl En' p') (ι∈ (g zero)))
      where
      got : Σ[ e' ∈ CS.S ] (⟨ fst e' ∈ fst En ⟩
              × ⟨ (e' ∷ x0 ∷ Ev tl ∷ En ∷ En' ∷ nS (suc n) ∷ nS n ∷ γ) ⊨ consAtL i0 i1 i2 ⟩)
          → ⟨ fst (Ev g) ∈ fst En ⟩
      got (e' , (e'∈ , hc)) = subst (λ u → ⟨ u ∈ fst En ⟩) (sym eq) e'∈
        where
        eq : fst (Ev g) ≡ fst e'
        eq = cong env (funExt (λ { zero → refl ; (suc i) → refl }))
           ∙ sym (subst ⟨_⟩ (consAtL-adequate i0 i1 i2
                    (e' ∷ x0 ∷ Ev tl ∷ En ∷ En' ∷ nS (suc n) ∷ nS n ∷ γ)
                    (λ i → ι (tl i)) refl) hc)

  -- AT ANY ENVIRONMENT holding the arity numeral at `ar` and the
  -- carrier at `Bi`: an environment over w of arity n (at slot zero)
  -- lies in every entry at n, hence in K.
  module At {n' : ℕ} (γ' : CS.S ^ n') (ar Bi : Fin n') (n : ℕ)
            (qd : fst (lookup ar γ') ≡ # n) (qb : fst (lookup Bi γ') ≡ Wv) where

    over-in : (z : CS.S) → ⟨ (z ∷ γ') ⊨ envOverAt zero (suc ar) (suc Bi) ⟩
            → (En : CS.S) → Entry n En → ⟨ fst z ∈ fst En ⟩
    over-in z hz En p =
      subst (λ u → ⟨ u ∈ fst En ⟩) (sym R.recovers) (all-in n R.g En p)
      where
      module R = Recover W n (z ∷ γ') zero (suc ar) (suc Bi) qd qb hz using (g; recovers)

    over-K : (z : CS.S) → ⟨ (z ∷ γ') ⊨ envOverAt zero (suc ar) (suc Bi) ⟩ → InK (fst z)
    over-K z hz = PT.rec (snd (fst z ∈ Kv))
      (λ { (En , p) → C.transK (fst En) (fst z) (entryK n En p) (over-in z hz En p) })
      (some-entry n)

    -- Every entry at n is contained in the true environment set.
    entry-over : (En : CS.S) (p : Entry n En) (z : CS.S) → ⟨ fst z ∈ fst En ⟩
               → ⟨ (z ∷ γ') ⊨ envOverAt zero (suc ar) (suc Bi) ⟩
    entry-over En p z z∈ =
      envOverAt-transport (z ∷ En ∷ nS n ∷ γ) (z ∷ γ')
        zero (suc i1) (suc (sh2 w)) zero (suc ar) (suc Bi)
        refl (numeralL-fst n ∙ sym qd) (sym qb)
        (ES.bnd→over z zK (entry-bnd n En p .fst z z∈))
      where
      zK : InK (fst z)
      zK = C.transK (fst En) (fst z) (entryK n En p) z∈
      envInK' : (u : CS.S)
              → ⟨ (u ∷ En ∷ nS n ∷ γ) ⊨ envOverAt zero (suc i1) (suc (sh2 w)) ⟩
              → InK (fst u)
      envInK' u hu = PT.rec (snd (fst u ∈ Kv))
        (λ { (E₁ , p₁) → C.transK (fst E₁) (fst u) (entryK n E₁ p₁)
               (subst (λ v → ⟨ v ∈ fst E₁ ⟩) (sym R.recovers) (all-in n R.g E₁ p₁)) })
        (some-entry n)
        where
        module R = Recover W n (u ∷ En ∷ nS n ∷ γ) zero (suc i1) (suc (sh2 w))
                     (numeralL-fst n) refl hu using (g; recovers)
      module ES = EnvSet {2 + m} i0 i1 (sh2 w) (sh2 K) (En ∷ nS n ∷ γ)
                    arityK (entryK n En p) (C.numK n) envInK' using (back; bnd→over; over→bnd; φB)

    -- THE TRUE ENVIRONMENT SET IS AN ENTRY, hence lies in K.
    envK : (Ei : Fin n') → ⟨ γ' ⊨ envSetAt Ei ar Bi ⟩ → InK (fst (lookup Ei γ'))
    envK Ei hE = PT.rec (snd (fst (lookup Ei γ') ∈ Kv))
      (λ { (En , p) → subst InK (sym (eqE En p)) (entryK n En p) })
      (some-entry n)
      where
      eqE : (En : CS.S) → Entry n En → fst (lookup Ei γ') ≡ fst En
      eqE En p = extensionalV {a = fst (lookup Ei γ')} {b = fst En}
        (λ x → ⇔toPath (fwd x) (bwd x))
        where
        fwd : (x : V ℓ) → ⟨ x ∈ fst (lookup Ei γ') ⟩ → ⟨ x ∈ fst En ⟩
        fwd x x∈ = over-in xS
          (extAt-out Ei (envOverAt zero (suc ar) (suc Bi)) γ' hE xS x∈) En p
          where
          xS : CS.S
          xS = down (lookup Ei γ') x x∈
        bwd : (x : V ℓ) → ⟨ x ∈ fst En ⟩ → ⟨ x ∈ fst (lookup Ei γ') ⟩
        bwd x x∈ = extAt-in Ei (envOverAt zero (suc ar) (suc Bi)) γ' hE xS
          (entry-over En p xS x∈)
          where
          xS : CS.S
          xS = down En x x∈

    -- THE EXTENSION of an environment over w of arity n by a member of
    -- w lies in K: it is an environment of arity suc n.
    consK : (z x e' : CS.S) → ⟨ (z ∷ γ') ⊨ envOverAt zero (suc ar) (suc Bi) ⟩
          → ⟨ fst x ∈ Wv ⟩
          → ((g : Fin n → V ℓ) → fst z ≡ env g → fst e' ≡ env (cons (fst x) g))
          → InK (fst e')
    consK z x e' hz x∈ rd = PT.rec (snd (fst e' ∈ Kv))
      (λ { (E₁ , p₁) → C.transK (fst E₁) (fst e') (entryK (suc n) E₁ p₁)
             (subst (λ u → ⟨ u ∈ fst E₁ ⟩) eq (all-in (suc n) g' E₁ p₁)) })
      (some-entry (suc n))
      where
      module R = Recover W n (z ∷ γ') zero (suc ar) (suc Bi) qd qb hz using (g; recovers)
      fib : Σ[ q ∈ ⟪ Wv ⟫ ] (ι q ≡ fst x)
      fib = ∈-asFiber {a = fst x} {b = Wv} x∈
      g' : Ix W (suc n)
      g' = cons (fib .fst) R.g
      eq : fst (Ev g') ≡ fst e'
      eq = cong env (funExt (λ { zero → fib .snd ; (suc i) → refl }))
         ∙ sym (rd (λ i → ι (R.g i)) R.recovers)

-- THE NUMERAL PIN, READ.  O holds every numeral, and nothing else:
-- the second is an ∈-induction, since a member is the empty tag or
-- the successor of a member, and the successor holds its predecessor.
module Nums {m : ℕ} (O N0 : Fin m) (γ : CS.S ^ m)
            (h : ⟨ γ ⊨ numsAt O N0 ⟩)
            (t0 : fst (lookup N0 γ) ≡ fst (numeralL 0)) where

  Ov : V ℓ
  Ov = fst (lookup O γ)

  nums : (k : ℕ) → ⟨ fst (numeralL k) ∈ Ov ⟩
  nums zero = subst (λ u → ⟨ u ∈ Ov ⟩) t0 (h .fst)
  nums (suc k) =
    PT.rec (snd (fst (numeralL (suc k)) ∈ Ov)) go
      (h .snd .fst (numeralL k) (nums k))
    where
    go : Σ[ y ∈ CS.S ] (⟨ fst y ∈ Ov ⟩
           × ⟨ (y ∷ numeralL k ∷ γ) ⊨ sucAtL i1 i0 ⟩)
       → ⟨ fst (numeralL (suc k)) ∈ Ov ⟩
    go (y , yO , hy) =
      subst (λ u → ⟨ u ∈ Ov ⟩)
        (suc-out i1 i0 (y ∷ numeralL k ∷ γ) hy
         ∙ cong sucV (numeralL-fst k) ∙ sym (numeralL-fst (suc k)))
        yO

  private
    P : V ℓ → Type (ℓ-suc ℓ)
    P x = ⟨ x ∈ Ov ⟩ → ∥ Σ[ k ∈ ℕ ] (x ≡ fst (numeralL k)) ∥₁

  only-nums : (x : V ℓ) → P x
  only-nums = ∈-induction {P = P} step
    where
    step : (x : V ℓ) → ((y : V ℓ) → ⟨ y ∈ x ⟩ → P y) → P x
    step x IH xO = PT.rec squash₁ go (h .snd .snd (down (lookup O γ) x xO) xO)
      where
      xS : CS.S
      xS = down (lookup O γ) x xO

      go : (x ≡ fst (lookup N0 γ))
         ⊎ ⟨ (xS ∷ γ) ⊨ ∃̇∈ (var (sh1 O)) (sucAtL i0 i1) ⟩
         → ∥ Σ[ k ∈ ℕ ] (x ≡ fst (numeralL k)) ∥₁
      go (inl e) = ∣ 0 , e ∙ t0 ∣₁
      go (inr e) = PT.rec squash₁ viaY e
        where
        viaY : Σ[ y ∈ CS.S ] (⟨ fst y ∈ Ov ⟩
                 × ⟨ (y ∷ xS ∷ γ) ⊨ sucAtL i0 i1 ⟩)
             → ∥ Σ[ k ∈ ℕ ] (x ≡ fst (numeralL k)) ∥₁
        viaY (y , yO , hy) = PT.map named (IH (fst y) y∈x yO)
          where
          xeq : x ≡ sucV (fst y)
          xeq = suc-out i0 i1 (y ∷ xS ∷ γ) hy
          y∈x : ⟨ fst y ∈ x ⟩
          y∈x = subst (λ u → ⟨ fst y ∈ u ⟩) (sym xeq) (self∈sucV (fst y))
          named : Σ[ k ∈ ℕ ] (fst y ≡ fst (numeralL k))
                → Σ[ k ∈ ℕ ] (x ≡ fst (numeralL k))
          named (k , q) = suc k
            , (xeq ∙ cong sucV (q ∙ numeralL-fst k) ∙ sym (numeralL-fst (suc k)))

-- THE CLOSURE FACTS AT THE SIXTEEN-SLOT ENVIRONMENT, from the pins.
module Closure (γ : CS.S ^ 16) (h : ⟨ γ ⊨ W3V.Mx.matrix ⟩)
               (n0K : ⟨ fst (lookup W3V.n0 γ) ∈ fst (lookup W3V.kk γ) ⟩)
               (ooK : ⟨ fst (lookup W3V.oo γ) ∈ fst (lookup W3V.kk γ) ⟩) where
  open W3V using (bb; kk; n0; n1; n10; n11; n2; n3; n4; n5; n6; n7; n8; n9; oo; ww)

  module R = Read {16} ww bb kk n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 γ using (InK; Kv; module Tags; numK-all; pair-out; trans-out)

  ht = h .fst
  hq = h .snd .fst
  hs = h .snd .snd .fst
  hp = h .snd .snd .snd .fst
  hn = h .snd .snd .snd .snd .fst
  wK = h .snd .snd .snd .snd .snd .fst
  bK = h .snd .snd .snd .snd .snd .snd .fst
  hg = h .snd .snd .snd .snd .snd .snd .snd

  module T = R.Tags hp using (t0; t1; t10; t11; t2; t3; t4; t5; t6; t7; t8; t9)

  tags : Tags n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 γ
  tags = record
    { t0 = T.t0 ∙ sym (numeralL-fst 0) ; t1 = T.t1 ∙ sym (numeralL-fst 1)
    ; t2 = T.t2 ∙ sym (numeralL-fst 2) ; t3 = T.t3 ∙ sym (numeralL-fst 3)
    ; t4 = T.t4 ∙ sym (numeralL-fst 4) ; t5 = T.t5 ∙ sym (numeralL-fst 5)
    ; t6 = T.t6 ∙ sym (numeralL-fst 6) ; t7 = T.t7 ∙ sym (numeralL-fst 7)
    ; t8 = T.t8 ∙ sym (numeralL-fst 8) ; t9 = T.t9 ∙ sym (numeralL-fst 9)
    ; t10 = T.t10 ∙ sym (numeralL-fst 10) ; t11 = T.t11 ∙ sym (numeralL-fst 11) }

  module N = Nums {16} oo n0 γ hn (tags .t0) using (nums; only-nums)

  -- Successor closure, from the pin `sucK`.
  sucK-out : (a : CS.S) → R.InK (fst a) → R.InK (sucV (fst a))
  sucK-out a aK = PT.rec (snd (sucV (fst a) ∈ fst R.Kv)) go (hs a aK)
    where
    go : Σ[ y ∈ CS.S ] (R.InK (fst y) × ⟨ (y ∷ a ∷ γ) ⊨ sucAtL i1 i0 ⟩)
       → R.InK (sucV (fst a))
    go (y , yK , hy) = subst R.InK (suc-out i1 i0 (y ∷ a ∷ γ) hy) yK

  kc : KC (fst (lookup kk γ)) (fst (lookup oo γ))
  kc = R.trans-out ht
     , ( (λ a b ha hb → subst R.InK (sym (prʟ-fst a b)) (R.pair-out hq a b ha hb))
     , ( sucK-out
     , ( R.numK-all hs (subst R.InK (tags .t0) n0K)
     , ( N.nums
     , ( N.only-nums
     , ooK )))))



-- =====================================================================
-- STEP 3.  THE DEFINABLE-POWERSET ROW IS SOUND: the statement.  At
-- any environment carrying the closure facts, the tag equalities and
-- the carrier in K, the bounded reading of `DefV.defAt` pins d to the
-- definable powerset of w.  Discharged in step 5 below.
-- =====================================================================

DefSound : Type (ℓ-suc ℓ)
DefSound =
  ∀ {m} (d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
    (γ : CS.S ^ m)
  → KC (fst (lookup K γ)) (fst (lookup O γ))
  → Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ
  → ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩
  → ⟨ γ ⊨ DefV.defAt d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
  → fst (lookup d γ) ≡ 𝒟ₒ (fst (lookup w γ))


-- =====================================================================
-- STEP 5.  THE DEFINABLE-POWERSET ROW, READ.  The body of `DefV.defAt`
-- at T ∷ C ∷ γ, with the tower's table beside it.  The closure facts
-- become the `KFacts` record the row agreements of
-- src/L/Condensation.lagda.md take, the code-set ties come out of the
-- pair chain and the arity pin, and the environment ties out of the
-- tower.
-- =====================================================================

open KFactsNS using (KFacts)

module DefRead {m : ℕ} (d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
               (γ : CS.S ^ m)
               (kc : KC (fst (lookup K γ)) (fst (lookup O γ)))
               (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
               (wK : ⟨ fst (lookup w γ) ∈ fst (lookup K γ) ⟩) where

  module DV = DefV {m} d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 using (body; defAt; defAt-out)

  private
    Kv Ov : V ℓ
    Kv = fst (lookup K γ)
    Ov = fst (lookup O γ)

    -- The carrier, ONE spelling: every `DefOf.defSet (fst W) ψ` and
    -- `𝒟ₒ (fst W)` below is written from W, never from a second name
    -- for its value.  Measured at this site: the two spellings `fst W`
    -- and a private `Wv = fst (lookup w γ)` cost 2.3 s per conversion
    -- under a fully applied `defSet`, whose `sett` the membership
    -- reduces through; `defSet-Sat W ψ` is stated at `fst W`.
    W : CS.S
    W = lookup w γ

    InK : V ℓ → Type (ℓ-suc ℓ)
    InK x = ⟨ x ∈ Kv ⟩

  module C = KC Kv Ov kc using (O-num; numK; numO; pairK; sucK; transK)
  module Z = Chain Kv C.transK using (fstK; prK-fst; prK-snd; sndK)

  arityK : (N v : CS.S) → ⟨ fst v ∈ fst N ⟩ → InK (fst N) → InK (fst v)
  arityK N v h hN = C.transK (fst N) (fst v) hN h

  unK : (k : ℕ) (a : CS.S) → InK (fst a) → InK (fst (prʟ (numeralL k) a))
  unK k a ha = C.pairK (numeralL k) a (C.numK k) ha

  binK : (k : ℕ) (a b : CS.S) → InK (fst a) → InK (fst b)
       → InK (fst (prʟ (numeralL k) (prʟ a b)))
  binK k a b ha hb = C.pairK (numeralL k) (prʟ a b) (C.numK k) (C.pairK a b ha hb)

  module Body (Cs Ts Ês : CS.S)
              (CK : InK (fst Cs)) (TK : InK (fst Ts)) (ÊK : InK (fst Ês))
              (hb : ⟨ (Ts ∷ Cs ∷ γ) ⊨ DV.body ⟩)
              (htow : ⟨ (Ês ∷ Ts ∷ Cs ∷ γ) ⊨ towerAt i0 (sh3 O) (sh3 w) (sh3 K) ⟩) where

    hcl  = hb .fst
    hsh  = hb .snd .fst
    han  = hb .snd .snd .fst
    hclo = hb .snd .snd .snd .fst
    hdom = hb .snd .snd .snd .snd .fst
    h12  = hb .snd .snd .snd .snd .snd .snd .fst
    hmem = hb .snd .snd .snd .snd .snd .snd .snd .fst
    hall = hb .snd .snd .snd .snd .snd .snd .snd .snd

    tags2 : Tags {2 + m} (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
              (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (Ts ∷ Cs ∷ γ)
    tags2 = tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (Cs ∷ γ) Ts
              (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ Cs tags)

    -- THE SITE-FACT BLOCK of src/L/Condensation.lagda.md:6079, at the
    -- carrier w and the bound K.
    facts : KFacts {2 + m} (sh2 w) (sh2 K) (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3)
              (sh2 N4) (sh2 N5) (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
              (Ts ∷ Cs ∷ γ)
    facts = record
      { tagEq0 = tags2 .t0 ; tagEq1 = tags2 .t1 ; tagEq2 = tags2 .t2
      ; tagEq3 = tags2 .t3 ; tagEq4 = tags2 .t4 ; tagEq5 = tags2 .t5
      ; tagEq6 = tags2 .t6 ; tagEq7 = tags2 .t7 ; tagEq8 = tags2 .t8
      ; tagEq9 = tags2 .t9 ; tagEq10 = tags2 .t10 ; tagEq11 = tags2 .t11
      ; numK0 = C.numK 0 ; numK1 = C.numK 1 ; numK2 = C.numK 2 ; numK3 = C.numK 3
      ; numK4 = C.numK 4 ; numK5 = C.numK 5 ; numK6 = C.numK 6 ; numK7 = C.numK 7
      ; numK8 = C.numK 8 ; numK9 = C.numK 9 ; numK10 = C.numK 10 ; numK11 = C.numK 11
      ; innerK = unK
      ; innerPairK = binK
      ; pairK = C.pairK
      ; carrierK = λ v hv → C.transK (fst W) (fst v) wK hv
      ; arityK = arityK }

    module Tw = Tower {3 + m} i0 (sh3 O) (sh3 w) (sh3 K) (Ês ∷ Ts ∷ Cs ∷ γ) kc ÊK htow using (module At; Entry; entryK; some-entry)

    -- THE CODE-SET TIES.  A code's components lie in K by the pair
    -- chain from C ∈ K; its arity is a numeral by the arity pin.
    cK : (c : CS.S) → ⟨ fst c ∈ fst Cs ⟩ → InK (fst c)
    cK c c∈ = C.transK (fst Cs) (fst c) CK c∈

    arNum : (c ar t : CS.S) → ⟨ fst c ∈ fst Cs ⟩ → InK (fst ar) → InK (fst t)
          → fst c ≡ pr (fst ar) (fst t) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    arNum c ar t c∈ arK tK e =
      PT.map (λ { (n , q) → n , q ∙ numeralL-fst n })
        (C.O-num (fst ar)
          (han c c∈ ar arK t tK
            (subst ⟨_⟩ (sym (prAtL-adequate i2 i1 i0 (t ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ))) e)))

    binCodes : (k : ℕ) (c ar a b : CS.S) → ⟨ fst c ∈ fst Cs ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → InK (fst ar) × InK (fst a) × InK (fst b)
               × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    binCodes k c ar a b c∈ e = arK , aK , bK , arNum c ar tS c∈ arK tK e
      where
      ck : InK (pr (fst ar) (pr (# k) (pr (fst a) (fst b))))
      ck = subst InK e (cK c c∈)
      arK : InK (fst ar)
      arK = Z.prK-fst (fst ar) (pr (# k) (pr (fst a) (fst b))) ck
      tK : InK (pr (# k) (pr (fst a) (fst b)))
      tK = Z.prK-snd (fst ar) (pr (# k) (pr (fst a) (fst b))) ck
      abK : InK (pr (fst a) (fst b))
      abK = Z.prK-snd (# k) (pr (fst a) (fst b)) tK
      aK : InK (fst a)
      aK = Z.prK-fst (fst a) (fst b) abK
      bK : InK (fst b)
      bK = Z.prK-snd (fst a) (fst b) abK
      tS : CS.S
      tS = down (lookup K γ) (pr (# k) (pr (fst a) (fst b))) tK

    unCodes : (k : ℕ) (c ar a : CS.S) → ⟨ fst c ∈ fst Cs ⟩
            → fst c ≡ pr (fst ar) (pr (# k) (fst a))
            → InK (fst ar) × InK (fst a) × ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
    unCodes k c ar a c∈ e = arK , aK , arNum c ar tS c∈ arK tK e
      where
      ck : InK (pr (fst ar) (pr (# k) (fst a)))
      ck = subst InK e (cK c c∈)
      arK : InK (fst ar)
      arK = Z.prK-fst (fst ar) (pr (# k) (fst a)) ck
      tK : InK (pr (# k) (fst a))
      tK = Z.prK-snd (fst ar) (pr (# k) (fst a)) ck
      aK : InK (fst a)
      aK = Z.prK-snd (# k) (fst a) tK
      tS : CS.S
      tS = down (lookup K γ) (pr (# k) (fst a)) tK

    entryC : (x y : CS.S) → ⟨ pr (fst x) (fst y) ∈ fst Cs ⟩ → InK (fst x) × InK (fst y)
    entryC x y p = Z.fstK (fst Cs) (fst x) (fst y) CK p , Z.sndK (fst Cs) (fst x) (fst y) CK p

    entryT : (x y : CS.S) → ⟨ pr (fst x) (fst y) ∈ fst Ts ⟩ → InK (fst x) × InK (fst y)
    entryT x y p = Z.fstK (fst Ts) (fst x) (fst y) TK p , Z.sndK (fst Ts) (fst x) (fst y) TK p

    -- A recorded value lies in K.
    valK-un : (c ar a yc : CS.S) → ⟨ fst c ∈ fst Cs ⟩ → fst c ≡ pr (fst ar) (pr (# 0) (fst a))
            → ⟨ pr (fst c) (fst yc) ∈ fst Ts ⟩ → InK (fst yc)
    valK-un c ar a yc _ _ hc = Z.sndK (fst Ts) (fst c) (fst yc) TK hc

    valK-un' : (k : ℕ) (c ar a yc : CS.S) → ⟨ fst c ∈ fst Cs ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (fst a))
             → ⟨ pr (fst c) (fst yc) ∈ fst Ts ⟩ → InK (fst yc)
    valK-un' k c ar a yc _ _ hc = Z.sndK (fst Ts) (fst c) (fst yc) TK hc

    valK-bin : (k : ℕ) (c ar a b yc : CS.S) → ⟨ fst c ∈ fst Cs ⟩
             → fst c ≡ pr (fst ar) (pr (# k) (pr (fst a) (fst b)))
             → ⟨ pr (fst c) (fst yc) ∈ fst Ts ⟩ → InK (fst yc)
    valK-bin k c ar a b yc _ _ hc = Z.sndK (fst Ts) (fst c) (fst yc) TK hc

    -- A subvalue lies in K.
    subK-of : ∀ {n'} (T' ar a y : Fin n') (δ : CS.S ^ n')
            → fst (lookup T' δ) ≡ fst Ts
            → ⟨ δ ⊨ subValAt T' ar a y ⟩ → InK (fst (lookup y δ))
    subK-of T' ar a y δ q h =
      Z.sndK (fst Ts) (pr (fst (lookup ar δ)) (fst (lookup a δ))) (fst (lookup y δ)) TK
        (subst (λ u → ⟨ pr (pr (fst (lookup ar δ)) (fst (lookup a δ))) (fst (lookup y δ)) ∈ u ⟩) q
          (subst ⟨_⟩ (subValAt-adequate T' ar a y δ) h))

    subKS-of : ∀ {n'} (T' ar a y : Fin n') (δ : CS.S ^ n')
             → fst (lookup T' δ) ≡ fst Ts
             → ⟨ δ ⊨ subValSuccAt T' ar a y ⟩ → InK (fst (lookup y δ))
    subKS-of T' ar a y δ q h =
      Z.sndK (fst Ts) (pr (sucV (fst (lookup ar δ))) (fst (lookup a δ))) (fst (lookup y δ)) TK
        (subst (λ u → ⟨ pr (pr (sucV (fst (lookup ar δ))) (fst (lookup a δ))) (fst (lookup y δ)) ∈ u ⟩) q
          (subst ⟨_⟩ (subValSuccAt-adequate T' ar a y δ) h))

    -- The environment ties of a row, from the tower, at the row's own
    -- environment: the arity slot holds a numeral, the carrier slot w.
    envK-of : ∀ {n'} (δ : CS.S ^ n') (ar Bi : Fin n') → fst (lookup Bi δ) ≡ fst W
            → ∥ Σ[ n ∈ ℕ ] (fst (lookup ar δ) ≡ # n) ∥₁
            → (Ei : Fin n') → ⟨ δ ⊨ envSetAt Ei ar Bi ⟩ → InK (fst (lookup Ei δ))
    envK-of δ ar Bi qb arNum Ei hE = PT.rec (snd (fst (lookup Ei δ) ∈ Kv))
      (λ { (n , q) → Tw.At.envK δ ar Bi n q qb Ei hE }) arNum

    envInK-of : ∀ {n'} (δ : CS.S ^ n') (ar Bi : Fin n') → fst (lookup Bi δ) ≡ fst W
              → ∥ Σ[ n ∈ ℕ ] (fst (lookup ar δ) ≡ # n) ∥₁
              → (z : CS.S) → ⟨ (z ∷ δ) ⊨ envOverAt zero (suc ar) (suc Bi) ⟩ → InK (fst z)
    envInK-of δ ar Bi qb arNum z hz = PT.rec (snd (fst z ∈ Kv))
      (λ { (n , q) → Tw.At.over-K δ ar Bi n q qb z hz }) arNum

    -- THE CLOSEDNESS, SHAPEDNESS AND TOTALITY, at the machine's reading.
    module CA = ClosedAgree {2 + m} i1 (sh2 K) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                  (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
                  (sh2 w) (sh2 N0) (sh2 N1) (sh2 N6) (sh2 N7) (Ts ∷ Cs ∷ γ)
                  facts binCodes unCodes entryC using (back)

    closed : ⟨ (Ts ∷ Cs ∷ γ) ⊨ closedAt i1 ⟩
    closed = CA.back hcl

    module SA = ShapedAgree {2 + m} i1 (sh2 w) (sh2 K)
                  (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                  (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (Ts ∷ Cs ∷ γ)
                  facts binCodes unCodes using (back)

    shaped : ⟨ (Ts ∷ Cs ∷ γ) ⊨ shapedAt i1 (sh2 w) ⟩
    shaped = SA.back hsh

    module DA = DomainAgree {2 + m} i0 i1 (sh2 K) (Ts ∷ Cs ∷ γ) entryT cK using (back)

    total : ⟨ (Ts ∷ Cs ∷ γ) ⊨ domAt i0 i1 ⟩
    total = DA.back hdom

    -- THE FOUR ROWS WHOSE TELESCOPES THE TIES ABOVE FILL DIRECTLY.
    module RBot = BotAgree {2 + m} i1 i0 (sh2 w) (sh2 N7) (sh2 K) (Ts ∷ Cs ∷ γ)
                    (tags2 .t7) (C.numK 7) (unK 7) (unCodes 7) (valK-un' 7) using (bot-in)

    rowBot : ⟨ (Ts ∷ Cs ∷ γ) ⊨ botClauseAt i1 i0 ⟩
    rowBot = RBot.bot-in (h12 .snd .snd .snd .snd .snd .snd .snd .fst)

    module RTop = TopAgree {2 + m} i1 i0 (sh2 w) (sh2 N6) (sh2 K) (Ts ∷ Cs ∷ γ)
                    (tags2 .t6) (C.numK 6) (unK 6) arityK (unCodes 6) (valK-un' 6)
                    (λ yc a ar c E arNum hE →
                       envK-of (E ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i3 (sh5 (sh2 w)) refl arNum zero hE)
                    (λ yc a ar c E arK arNum z hz →
                       envInK-of (E ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i3 (sh5 (sh2 w)) refl arNum z hz) using (back)

    rowTop : ⟨ (Ts ∷ Cs ∷ γ) ⊨ topClauseAt i1 i0 (sh2 w) ⟩
    rowTop = RTop.back (h12 .snd .snd .snd .snd .snd .snd .fst)

    module RNeg = NegAgree {2 + m} i1 i0 (sh2 w) (sh2 N5) (sh2 K) (Ts ∷ Cs ∷ γ)
                    (tags2 .t5) (C.numK 5) (unK 5) arityK (unCodes 5) (valK-un' 5)
                    (λ E ya yc a ar c arK aK →
                       subst InK (prʟ-fst ar a) (C.pairK ar a arK aK))
                    (λ ya yc a ar c E hs →
                       subK-of (sh6 i0) i4 i3 i1 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                    (λ ya yc a ar c E arNum hE →
                       envK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum zero hE)
                    (λ ya yc a ar c E arK arNum z hz →
                       envInK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum z hz) using (back)

    rowNeg : ⟨ (Ts ∷ Cs ∷ γ) ⊨ negClauseAt i1 i0 (sh2 w) ⟩
    rowNeg = RNeg.back (h12 .snd .snd .snd .snd .snd .fst)

    module RImp = ImpAgree {2 + m} i1 i0 (sh2 w) (sh2 N4) (sh2 K) (Ts ∷ Cs ∷ γ)
                    (tags2 .t4) (C.numK 4) (binK 4) C.pairK arityK (binCodes 4) (valK-bin 4)
                    C.pairK
                    (λ E yb ya yc b a ar c hs →
                       subK-of (sh8 i0) i6 i5 i2 (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                    (λ E yb ya yc b a ar c hs →
                       subK-of (sh8 i0) i6 i4 i1 (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                    (λ E yb ya yc b a ar c arNum hE →
                       envK-of (E ∷ yb ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i6 (sh8 (sh2 w)) refl arNum zero hE)
                    (λ E ya yc b a ar c arK arNum z hz →
                       envInK-of (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i5 (sh7 (sh2 w)) refl arNum z hz) using (back)

    rowImp : ⟨ (Ts ∷ Cs ∷ γ) ⊨ impClauseAt i1 i0 (sh2 w) ⟩
    rowImp = RImp.back (h12 .snd .snd .snd .snd .fst)

    -- THE ENVIRONMENT SET AT THE BINARY FRAME, for the And and Or rows,
    -- which bind it without a machine-side counterpart: an entry of
    -- the tower, restated as the bounded set at the row's environment.
    someEnv-of : (ya yc b a ar c : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
               → ∥ Σ CS.S (λ E → InK (fst E)
                    × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                        envHypB2 {2 + m} (sh2 w) (sh2 K) ⟩) ∥₁
    someEnv-of ya yc b a ar c = PT.rec squash₁ go
      where
      go : Σ[ n ∈ ℕ ] (fst ar ≡ # n)
         → ∥ Σ CS.S (λ E → InK (fst E)
              × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                  envHypB2 {2 + m} (sh2 w) (sh2 K) ⟩) ∥₁
      go (n , q) = PT.map at (Tw.some-entry n)
        where
        arK : InK (fst ar)
        arK = subst InK (numeralL-fst n ∙ sym q) (C.numK n)
        at : Σ[ En ∈ CS.S ] Tw.Entry n En
           → Σ CS.S (λ E → InK (fst E)
                × ⟨ (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                    envHypB2 {2 + m} (sh2 w) (sh2 K) ⟩)
        at (En , p) = En , (Tw.entryK n En p , ES.back machine)
          where
          module ES = EnvSet {9 + m} zero i5 (sh7 (sh2 w)) (sh7 (sh2 K))
                        (En ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ)
                        arityK (Tw.entryK n En p) arK
                        (λ z hz → Tw.At.over-K (En ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ)
                                    i5 (sh7 (sh2 w)) n q refl z hz) using (back; bnd→over; over→bnd; φB)
          machine : ⟨ (En ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                      envSetAt zero i5 (sh7 (sh2 w)) ⟩
          machine = extAt-in-both zero (envOverAt zero (suc i5) (suc (sh7 (sh2 w))))
                      (En ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ)
                      (λ z z∈ → Tw.At.entry-over (En ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ)
                                  i5 (sh7 (sh2 w)) n q refl En p z z∈)
                      (λ z hz → Tw.At.over-in (En ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ)
                                  i5 (sh7 (sh2 w)) n q refl z hz En p)

    -- THE EXTENDED ENVIRONMENT, at the unary and the binary frames.
    consK-un : (ya yc a ar c E : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
             → (z x e' : CS.S)
             → ⟨ (z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                 envOverAt zero i5 (sh7 (sh2 w)) ⟩
             → ⟨ fst x ∈ fst W ⟩
             → ⟨ (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                 consAtL zero (suc zero) (suc (suc zero)) ⟩
             → InK (fst e')
    consK-un ya yc a ar c E arNum z x e' hz x∈ hc = PT.rec (snd (fst e' ∈ Kv))
      (λ { (n , q) → Tw.At.consK (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) n q refl
             z x e' hz x∈
             (λ g hz' → subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc zero))
                          (e' ∷ x ∷ z ∷ E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) g hz') hc) })
      arNum

    consK-bin : (E ya yc b a ar c : CS.S) → ∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
              → (z w' x e' : CS.S)
              → ⟨ (z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                  envOverAt zero i6 (sh8 (sh2 w)) ⟩
              → ⟨ fst x ∈ fst W ⟩
              → ⟨ (e' ∷ x ∷ w' ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) ⊨
                  consAtL zero (suc zero) (suc (suc (suc zero))) ⟩
              → InK (fst e')
    consK-bin E ya yc b a ar c arNum z w' x e' hz x∈ hc = PT.rec (snd (fst e' ∈ Kv))
      (λ { (n , q) → Tw.At.consK (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i5 (sh7 (sh2 w)) n q refl
             z x e' hz x∈
             (λ g hz' → subst ⟨_⟩ (consAtL-adequate zero (suc zero) (suc (suc (suc zero)))
                          (e' ∷ x ∷ w' ∷ z ∷ E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) g hz') hc) })
      arNum

    t0K : InK (fst (lookup (sh2 N0) (Ts ∷ Cs ∷ γ)))
    t0K = subst InK (sym (tags2 .t0)) (C.numK 0)

    transK' : (x a : CS.S) → ⟨ fst x ∈ fst a ⟩ → InK (fst a) → InK (fst x)
    transK' x a h ha = C.transK (fst a) (fst x) ha h

    -- THE EIGHT RE-TIED ROWS.
    module RMem = MemAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N0) (sh2 K) (sh2 N0) (sh2 N1) (Ts ∷ Cs ∷ γ)
                    (tags2 .t0) (C.numK 0) (binK 0) C.pairK C.transK (binCodes 0) (valK-bin 0)
                    (tags2 .t0) (tags2 .t1) t0K (C.numK 1)
                    (λ yc b a ar c E arNum hE →
                       envK-of (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum zero hE)
                    (λ yc b a ar c E arK arNum z hz →
                       envInK-of (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum z hz) using (back)

    rowMem : ⟨ (Ts ∷ Cs ∷ γ) ⊨ memClauseAt i1 i0 (sh2 w) ⟩
    rowMem = RMem.back (h12 .fst)

    module REq = EqAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N1) (sh2 K) (sh2 N0) (sh2 N1) (Ts ∷ Cs ∷ γ)
                   (tags2 .t1) (C.numK 1) (binK 1) C.pairK C.transK (binCodes 1) (valK-bin 1)
                   (tags2 .t0) (tags2 .t1) t0K (C.numK 1)
                   (λ yc b a ar c E arNum hE →
                      envK-of (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum zero hE)
                   (λ yc b a ar c E arK arNum z hz →
                      envInK-of (E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum z hz) using (back)

    rowEq : ⟨ (Ts ∷ Cs ∷ γ) ⊨ eqClauseAt i1 i0 (sh2 w) ⟩
    rowEq = REq.back (h12 .snd .fst)

    module RAnd = AndAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N2) (sh2 K) (Ts ∷ Cs ∷ γ)
                    (tags2 .t2) (C.numK 2) (binK 2) C.pairK (binCodes 2) (valK-bin 2) transK'
                    (λ x y yc b a ar c hs →
                       subK-of (sh7 i0) i5 i4 i1 (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                    (λ y ya yc b a ar c hs →
                       subK-of (sh7 i0) i5 i3 i0 (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                    (λ ya yc b a ar c _ _ _ arNum → someEnv-of ya yc b a ar c arNum) using (back)

    rowAnd : ⟨ (Ts ∷ Cs ∷ γ) ⊨ binClauseAt i1 i0 2 (propRel i0 (interAt (suc (suc zero)) (suc zero) zero)) ⟩
    rowAnd = RAnd.back (h12 .snd .snd .fst)

    module ROr = OrAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N3) (sh2 K) (Ts ∷ Cs ∷ γ)
                   (tags2 .t3) (C.numK 3) (binK 3) C.pairK (binCodes 3) (valK-bin 3) transK'
                   (λ x y yc b a ar c hs →
                      subK-of (sh7 i0) i5 i4 i1 (x ∷ y ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                   (λ y ya yc b a ar c hs →
                      subK-of (sh7 i0) i5 i3 i0 (y ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                   (λ ya yc b a ar c _ _ _ arNum → someEnv-of ya yc b a ar c arNum) using (back)

    rowOr : ⟨ (Ts ∷ Cs ∷ γ) ⊨ binClauseAt i1 i0 3 (propRel i0 (unionAt (suc (suc zero)) (suc zero) zero)) ⟩
    rowOr = ROr.back (h12 .snd .snd .snd .fst)

    module RExist = ExistAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N8) (sh2 K) (Ts ∷ Cs ∷ γ)
                      (tags2 .t8) (C.numK 8) (unK 8) C.pairK C.transK C.sucK (unCodes 8) (valK-un' 8)
                      (λ ya yc a ar c E hs →
                         subKS-of (sh6 i0) i4 i3 i1 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                      (λ ya yc a ar c E arNum hE →
                         envK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum zero hE)
                      (λ ya yc a ar c E arK arNum z hz →
                         envInK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum z hz) using (back)

    rowExist : ⟨ (Ts ∷ Cs ∷ γ) ⊨ existClauseAt i1 i0 (sh2 w) ⟩
    rowExist = RExist.back (h12 .snd .snd .snd .snd .snd .snd .snd .snd .fst)

    module RForall = ForallAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N9) (sh2 K) (Ts ∷ Cs ∷ γ)
                       (tags2 .t9) (C.numK 9) (unK 9) C.pairK C.transK C.sucK (unCodes 9) (valK-un' 9)
                       (λ ya yc a ar c E hs →
                          subKS-of (sh6 i0) i4 i3 i1 (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                       (λ ya yc a ar c E arNum hE →
                          envK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum zero hE)
                       (λ ya yc a ar c E arK arNum z hz →
                          envInK-of (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i4 (sh6 (sh2 w)) refl arNum z hz)
                       consK-un using (back)

    rowForall : ⟨ (Ts ∷ Cs ∷ γ) ⊨ forallClauseAt i1 i0 (sh2 w) ⟩
    rowForall = RForall.back (h12 .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)

    module RAllIn = BndAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N10) (sh2 K) (sh2 N0) (sh2 N1) (Ts ∷ Cs ∷ γ) 10
                      (tags2 .t10) (C.numK 10) (binK 10) C.pairK C.transK C.sucK (binCodes 10) (valK-bin 10)
                      (λ E ya yc b a ar c hs →
                         subKS-of (sh7 i0) i5 i3 i1 (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                      (λ E ya yc b a ar c arNum hE →
                         envK-of (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i5 (sh7 (sh2 w)) refl arNum zero hE)
                      (λ E ya yc b a ar c arK arNum z hz →
                         envInK-of (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i5 (sh7 (sh2 w)) refl arNum z hz)
                      consK-bin
                      (tags2 .t0) (tags2 .t1) t0K (C.numK 1) using (back-all)

    rowAllIn : ⟨ (Ts ∷ Cs ∷ γ) ⊨ allInClauseAt i1 i0 (sh2 w) ⟩
    rowAllIn = RAllIn.back-all (h12 .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst)

    module RExIn = BndAgree′ {2 + m} i1 i0 (sh2 w) (sh2 N11) (sh2 K) (sh2 N0) (sh2 N1) (Ts ∷ Cs ∷ γ) 11
                     (tags2 .t11) (C.numK 11) (binK 11) C.pairK C.transK C.sucK (binCodes 11) (valK-bin 11)
                     (λ E ya yc b a ar c hs →
                        subKS-of (sh7 i0) i5 i3 i1 (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) refl hs)
                     (λ E ya yc b a ar c arNum hE →
                        envK-of (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i5 (sh7 (sh2 w)) refl arNum zero hE)
                     (λ E ya yc b a ar c arK arNum z hz →
                        envInK-of (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ Ts ∷ Cs ∷ γ) i5 (sh7 (sh2 w)) refl arNum z hz)
                     consK-bin
                     (tags2 .t0) (tags2 .t1) t0K (C.numK 1) using (back-ex)

    rowExIn : ⟨ (Ts ∷ Cs ∷ γ) ⊨ exInClauseAt i1 i0 (sh2 w) ⟩
    rowExIn = RExIn.back-ex (h12 .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd)

    -- THE TABLE IS PINNED: at every key of a formula, the recorded
    -- value is the satisfaction set (src/L/Coding/Unique.lagda.md).
    clauses : Good.Clauses (Ts ∷ Cs ∷ γ) i1 i0 (sh2 w)
    clauses = rowMem , (rowEq , (rowAnd , (rowOr , (rowImp , (rowNeg , (rowTop , (rowBot
            , (rowExist , (rowForall , (rowAllIn , rowExIn))))))))))

    pinned : ∀ {k} (ψ : Formula CS.S k) → Good.Pinned (Ts ∷ Cs ∷ γ) i1 i0 (sh2 w) ψ
    pinned ψ = Good.pinned (Ts ∷ Cs ∷ γ) i1 i0 (sh2 w) closed total clauses ψ

    -- =================================================================
    -- THE KEY OF EVERY FORMULA OVER w LIES IN C.  Induction on the
    -- formula through the twelve closure clauses.  A key is
    -- (arity, (tag, payload)) with `prʟ` (src/L/Coding/Table.lagda.md
    -- `keyʟ`); each clause produces exactly that pair from the
    -- payload's parts, which the induction holds in C or in K.
    -- =================================================================

    private
      toS : ∀ {k} → Formula ⟪ fst W ⟫ k → Formula CS.S k
      toS = mapFo (asConst W)

      toT : ∀ {k} → Term ⟪ fst W ⟫ k → Term CS.S k
      toT = mapTm (asConst W)

      γ′ : CS.S ^ (2 + m)
      γ′ = Ts ∷ Cs ∷ γ

      hAt0 = hclo .fst
      hAt1 = hclo .snd .fst
      hBin2 = hclo .snd .snd .fst
      hBin3 = hclo .snd .snd .snd .fst
      hBin4 = hclo .snd .snd .snd .snd .fst
      hUn5 = hclo .snd .snd .snd .snd .snd .fst
      hCon6 = hclo .snd .snd .snd .snd .snd .snd .fst
      hCon7 = hclo .snd .snd .snd .snd .snd .snd .snd .fst
      hQu8 = hclo .snd .snd .snd .snd .snd .snd .snd .snd .fst
      hQu9 = hclo .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
      hBq10 = hclo .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .fst
      hBq11 = hclo .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd .snd

      pr-in : ∀ {n'} (q u v : Fin n') (δ : CS.S ^ n')
            → fst (lookup q δ) ≡ pr (fst (lookup u δ)) (fst (lookup v δ))
            → ⟨ δ ⊨ prAtL q u v ⟩
      pr-in q u v δ e = subst ⟨_⟩ (sym (prAtL-adequate q u v δ)) e

      suc-in : ∀ {n'} (i j : Fin n') (δ : CS.S ^ n')
             → fst (lookup j δ) ≡ sucV (fst (lookup i δ)) → ⟨ δ ⊨ sucAtL i j ⟩
      suc-in i j δ e = subst ⟨_⟩ (sym (sucAtL-adequate i j δ)) e

      sucNum : (k : ℕ) → fst (numeralL (suc k)) ≡ sucV (fst (numeralL k))
      sucNum k = numeralL-fst (suc k) ∙ cong sucV (sym (numeralL-fst k))

      inC : (c : CS.S) (x : V ℓ) → ⟨ fst c ∈ fst Cs ⟩ → x ≡ fst c → ⟨ x ∈ fst Cs ⟩
      inC c x c∈ e = subst (λ u → ⟨ u ∈ fst Cs ⟩) (sym e) c∈

      -- the code of a key is in K
      codeK : ∀ {k} (χ : Formula CS.S k) → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
            → InK (fst (LCode.⌜ χ ⌝))
      codeK {k} χ c∈ = Z.prK-snd (fst (numeralL k)) (fst (LCode.⌜ χ ⌝))
        (subst InK (prʟ-fst (numeralL k) (LCode.⌜ χ ⌝)) (cK (keyʟ χ) c∈))

      -- the code of a term is in K
      tmK : ∀ {k} (t : Term ⟪ fst W ⟫ k) → InK (fst (LCode.⌜ toT t ⌝ᵗ))
      tmK (con q) = C.pairK (numeralL 0) (asConst W q) (C.numK 0)
                      (C.transK (fst W) (fst (asConst W q)) wK (snd (DefOf.ι (fst W) q)))
      tmK (var i) = C.pairK (numeralL 1) (numeralL (toℕ i)) (C.numK 1) (C.numK (toℕ i))

      -- THE TERM PREDICATE, at any environment holding the term code at
      -- `s`, the arity numeral at `ar`, and the carrier, bound and two
      -- tags at their slots.
      tmAt-in : ∀ {k n'} (t : Term ⟪ fst W ⟫ k) (δ : CS.S ^ n') (s ar wi Ki N0i N1i : Fin n')
              → fst (lookup s δ) ≡ fst (LCode.⌜ toT t ⌝ᵗ)
              → fst (lookup ar δ) ≡ fst (numeralL k)
              → fst (lookup wi δ) ≡ fst W → fst (lookup Ki δ) ≡ Kv
              → fst (lookup N0i δ) ≡ fst (numeralL 0)
              → fst (lookup N1i δ) ≡ fst (numeralL 1)
              → ⟨ δ ⊨ tmAt s ar wi Ki N0i N1i ⟩
      tmAt-in (con q) δ s ar wi Ki N0i N1i qs qar qw qK qN0 qN1 =
        ∣ inl ∣ asConst W q
              , ( subst (λ u → ⟨ fst (asConst W q) ∈ u ⟩) (sym qw) (snd (DefOf.ι (fst W) q))
                , ∣ numeralL 0
                  , ( subst (λ u → ⟨ fst (numeralL 0) ∈ u ⟩) (sym qK) (C.numK 0)
                    , ( sym qN0
                      , pr-in (suc (sh1 s)) zero (suc i0) (numeralL 0 ∷ asConst W q ∷ δ)
                          (qs ∙ prʟ-fst (numeralL 0) (asConst W q)) ) ) ∣₁ ) ∣₁ ∣₁
      tmAt-in {k} (var i) δ s ar wi Ki N0i N1i qs qar qw qK qN0 qN1 =
        ∣ inr ∣ numeralL (toℕ i)
              , ( subst2 (λ a b → ⟨ a ∈ b ⟩) (sym (numeralL-fst (toℕ i)))
                    (sym (qar ∙ numeralL-fst k)) (#mono (toℕ i) k (toℕ<n i))
                , ∣ numeralL 1
                  , ( subst (λ u → ⟨ fst (numeralL 1) ∈ u ⟩) (sym qK) (C.numK 1)
                    , ( sym qN1
                      , pr-in (suc (sh1 s)) zero (suc i0) (numeralL 1 ∷ numeralL (toℕ i) ∷ δ)
                          (qs ∙ prʟ-fst (numeralL 1) (numeralL (toℕ i))) ) ) ∣₁ ) ∣₁ ∣₁

      -- the value of a key from its three pairs
      keyVal2 : ∀ {k} (χ : Formula CS.S k) (k' : ℕ) (x y : CS.S)
              → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') (prʟ x y)
              → fst (keyʟ χ) ≡ pr (fst (numeralL k)) (pr (fst (numeralL k')) (pr (fst x) (fst y)))
      keyVal2 {k} χ k' x y e =
        prʟ-fst (numeralL k) (LCode.⌜ χ ⌝)
        ∙ cong (pr (fst (numeralL k)))
            (cong fst e ∙ prʟ-fst (numeralL k') (prʟ x y)
             ∙ cong (pr (fst (numeralL k'))) (prʟ-fst x y))

      keyVal1 : ∀ {k} (χ : Formula CS.S k) (k' : ℕ) (x : CS.S)
              → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') x
              → fst (keyʟ χ) ≡ pr (fst (numeralL k)) (pr (fst (numeralL k')) (fst x))
      keyVal1 {k} χ k' x e =
        prʟ-fst (numeralL k) (LCode.⌜ χ ⌝)
        ∙ cong (pr (fst (numeralL k))) (cong fst e ∙ prʟ-fst (numeralL k') x)

      -- the value of a produced code from its three pairs
      cVal2 : (c s q : CS.S) (A T P : V ℓ) (k' : ℕ)
            → fst c ≡ pr A (fst s) → fst s ≡ pr T (fst q) → fst q ≡ P
            → T ≡ fst (numeralL k')
            → fst c ≡ pr A (pr (fst (numeralL k')) P)
      cVal2 c s q A T P k' ec es eq et = ec ∙ cong (pr A) (es ∙ cong₂ pr et eq)

      cVal1 : (c s : CS.S) (A T P : V ℓ) (k' : ℕ)
            → fst c ≡ pr A (fst s) → fst s ≡ pr T P
            → T ≡ fst (numeralL k')
            → fst c ≡ pr A (pr (fst (numeralL k')) P)
      cVal1 c s A T P k' ec es et = ec ∙ cong (pr A) (es ∙ cong (λ u → pr u P) et)

    -- THE SIX CLAUSE SHAPES, READ.  Each takes the parts the clause
    -- binds, the tag slot and its numeral, the formula and its code
    -- equation, and returns the key's membership in C.
    private
      atomC : ∀ {k} (t u : Term ⟪ fst W ⟫ k) (Ni : Fin m) (k' : ℕ) (χ : Formula CS.S k)
            → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') (prʟ (LCode.⌜ toT t ⌝ᵗ) (LCode.⌜ toT u ⌝ᵗ))
            → fst (lookup (sh2 Ni) γ′) ≡ fst (numeralL k')
            → ⟨ γ′ ⊨ Close.atomAt {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                  (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                  (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (sh2 Ni) ⟩
            → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
      atomC {k} t u Ni k' χ e te h = PT.rec (snd (_ ∈ fst Cs)) byC
        (h (numeralL k) (C.numO k) (LCode.⌜ toT t ⌝ᵗ) (tmK t) (LCode.⌜ toT u ⌝ᵗ) (tmK u)
           ( tmAt-in t δ₃ i1 i2 (sh3 (sh2 w)) (sh3 (sh2 K)) (sh3 (sh2 N0)) (sh3 (sh2 N1))
               refl refl refl refl (tags2 .t0) (tags2 .t1)
           , tmAt-in u δ₃ i0 i2 (sh3 (sh2 w)) (sh3 (sh2 K)) (sh3 (sh2 N0)) (sh3 (sh2 N1))
               refl refl refl refl (tags2 .t0) (tags2 .t1) ))
        where
        δ₃ : CS.S ^ (3 + (2 + m))
        δ₃ = LCode.⌜ toT u ⌝ᵗ ∷ LCode.⌜ toT t ⌝ᵗ ∷ numeralL k ∷ γ′
        P : V ℓ
        P = pr (fst (LCode.⌜ toT t ⌝ᵗ)) (fst (LCode.⌜ toT u ⌝ᵗ))
        byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst Cs ⟩
                × ⟨ (c ∷ δ₃) ⊨ ∃̇∈ (var (sh4 (sh2 K))) (∃̇∈ (var (sh5 (sh2 K)))
                    ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh6 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 ))) ⟩)
            → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
        byC (c , (c∈ , hq)) = PT.rec (snd (_ ∈ fst Cs)) byQ hq
          where
          byQ : Σ[ q ∈ CS.S ] (InK (fst q)
                  × ⟨ (q ∷ c ∷ δ₃) ⊨ ∃̇∈ (var (sh5 (sh2 K)))
                      ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh6 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 )) ⟩)
              → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
          byQ (q , (_ , hs)) = PT.rec (snd (_ ∈ fst Cs)) byS hs
            where
            byS : Σ[ s' ∈ CS.S ] (InK (fst s')
                    × ⟨ (s' ∷ q ∷ c ∷ δ₃) ⊨
                        ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh6 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 )) ⟩)
                → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
            byS (s' , (_ , (eq , (es , ec)))) = inC c _ c∈
              ( keyVal2 χ k' (LCode.⌜ toT t ⌝ᵗ) (LCode.⌜ toT u ⌝ᵗ) e
              ∙ sym (cVal2 c s' q (fst (numeralL k)) (fst (lookup (sh2 Ni) γ′)) P k'
                       (pr-out i2 i5 i0 (s' ∷ q ∷ c ∷ δ₃) ec)
                       (pr-out i0 (sh6 (sh2 Ni)) i1 (s' ∷ q ∷ c ∷ δ₃) es)
                       (pr-out i1 i4 i3 (s' ∷ q ∷ c ∷ δ₃) eq)
                       te) )

      binC : ∀ {k} (χ₁ χ₂ : Formula CS.S k)
           → ⟨ fst (keyʟ χ₁) ∈ fst Cs ⟩ → ⟨ fst (keyʟ χ₂) ∈ fst Cs ⟩
           → (Ni : Fin m) (k' : ℕ) (χ : Formula CS.S k)
           → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') (prʟ (LCode.⌜ χ₁ ⌝) (LCode.⌜ χ₂ ⌝))
           → fst (lookup (sh2 Ni) γ′) ≡ fst (numeralL k')
           → ⟨ γ′ ⊨ Close.binAt {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                 (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                 (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (sh2 Ni) ⟩
           → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
      binC {k} χ₁ χ₂ c₁∈ c₂∈ Ni k' χ e te h = PT.rec (snd (_ ∈ fst Cs)) byC
        (h (keyʟ χ₁) c₁∈ (keyʟ χ₂) c₂∈ (numeralL k) (C.numO k)
           (LCode.⌜ χ₁ ⌝) (codeK χ₁ c₁∈) (LCode.⌜ χ₂ ⌝) (codeK χ₂ c₂∈)
           ( pr-in i4 i2 i1 δ₅ (prʟ-fst (numeralL k) (LCode.⌜ χ₁ ⌝))
           , pr-in i3 i2 i0 δ₅ (prʟ-fst (numeralL k) (LCode.⌜ χ₂ ⌝)) ))
        where
        δ₅ : CS.S ^ (5 + (2 + m))
        δ₅ = LCode.⌜ χ₂ ⌝ ∷ LCode.⌜ χ₁ ⌝ ∷ numeralL k ∷ keyʟ χ₂ ∷ keyʟ χ₁ ∷ γ′
        P : V ℓ
        P = pr (fst (LCode.⌜ χ₁ ⌝)) (fst (LCode.⌜ χ₂ ⌝))
        byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst Cs ⟩
                × ⟨ (c ∷ δ₅) ⊨ ∃̇∈ (var (sh6 (sh2 K))) (∃̇∈ (var (suc (sh6 (sh2 K))))
                    ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 ))) ⟩)
            → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
        byC (c , (c∈ , hq)) = PT.rec (snd (_ ∈ fst Cs)) byQ hq
          where
          byQ : Σ[ q ∈ CS.S ] (InK (fst q)
                  × ⟨ (q ∷ c ∷ δ₅) ⊨ ∃̇∈ (var (suc (sh6 (sh2 K))))
                      ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 )) ⟩)
              → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
          byQ (q , (_ , hs)) = PT.rec (snd (_ ∈ fst Cs)) byS hs
            where
            byS : Σ[ s' ∈ CS.S ] (InK (fst s')
                    × ⟨ (s' ∷ q ∷ c ∷ δ₅) ⊨
                        ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i5 i0 )) ⟩)
                → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
            byS (s' , (_ , (eq , (es , ec)))) = inC c _ c∈
              ( keyVal2 χ k' (LCode.⌜ χ₁ ⌝) (LCode.⌜ χ₂ ⌝) e
              ∙ sym (cVal2 c s' q (fst (numeralL k)) (fst (lookup (sh2 Ni) γ′)) P k'
                       (pr-out i2 i5 i0 (s' ∷ q ∷ c ∷ δ₅) ec)
                       (pr-out i0 (sh8 (sh2 Ni)) i1 (s' ∷ q ∷ c ∷ δ₅) es)
                       (pr-out i1 i4 i3 (s' ∷ q ∷ c ∷ δ₅) eq)
                       te) )

      unC : ∀ {k} (χ₁ : Formula CS.S k) → ⟨ fst (keyʟ χ₁) ∈ fst Cs ⟩
          → (Ni : Fin m) (k' : ℕ) (χ : Formula CS.S k)
          → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') (LCode.⌜ χ₁ ⌝)
          → fst (lookup (sh2 Ni) γ′) ≡ fst (numeralL k')
          → ⟨ γ′ ⊨ Close.unAt {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (sh2 Ni) ⟩
          → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
      unC {k} χ₁ c₁∈ Ni k' χ e te h = PT.rec (snd (_ ∈ fst Cs)) byC
        (h (keyʟ χ₁) c₁∈ (numeralL k) (C.numO k) (LCode.⌜ χ₁ ⌝) (codeK χ₁ c₁∈)
           (pr-in i2 i1 i0 δ₃ (prʟ-fst (numeralL k) (LCode.⌜ χ₁ ⌝))))
        where
        δ₃ : CS.S ^ (3 + (2 + m))
        δ₃ = LCode.⌜ χ₁ ⌝ ∷ numeralL k ∷ keyʟ χ₁ ∷ γ′
        byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst Cs ⟩
                × ⟨ (c ∷ δ₃) ⊨ ∃̇∈ (var (sh4 (sh2 K)))
                    ( prAtL i0 (sh5 (sh2 Ni)) i2 ∧̇ prAtL i1 i3 i0 ) ⟩)
            → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
        byC (c , (c∈ , hs)) = PT.rec (snd (_ ∈ fst Cs)) byS hs
          where
          byS : Σ[ s' ∈ CS.S ] (InK (fst s')
                  × ⟨ (s' ∷ c ∷ δ₃) ⊨ ( prAtL i0 (sh5 (sh2 Ni)) i2 ∧̇ prAtL i1 i3 i0 ) ⟩)
              → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
          byS (s' , (_ , (es , ec))) = inC c _ c∈
            ( keyVal1 χ k' (LCode.⌜ χ₁ ⌝) e
            ∙ sym (cVal1 c s' (fst (numeralL k)) (fst (lookup (sh2 Ni) γ′)) (fst (LCode.⌜ χ₁ ⌝)) k'
                     (pr-out i1 i3 i0 (s' ∷ c ∷ δ₃) ec)
                     (pr-out i0 (sh5 (sh2 Ni)) i2 (s' ∷ c ∷ δ₃) es)
                     te) )

      conC : ∀ {k} (Ni : Fin m) (k' : ℕ) (χ : Formula CS.S k)
           → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') (numeralL 0)
           → fst (lookup (sh2 Ni) γ′) ≡ fst (numeralL k')
           → ⟨ γ′ ⊨ Close.conAt {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                 (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                 (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (sh2 Ni) ⟩
           → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
      conC {k} Ni k' χ e te h = PT.rec (snd (_ ∈ fst Cs)) byC (h (numeralL k) (C.numO k))
        where
        δ₁ : CS.S ^ (1 + (2 + m))
        δ₁ = numeralL k ∷ γ′
        byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst Cs ⟩
                × ⟨ (c ∷ δ₁) ⊨ ∃̇∈ (var (sh2 (sh2 K)))
                    ( prAtL i0 (sh3 (sh2 Ni)) (sh3 (sh2 N0)) ∧̇ prAtL i1 i2 i0 ) ⟩)
            → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
        byC (c , (c∈ , hs)) = PT.rec (snd (_ ∈ fst Cs)) byS hs
          where
          byS : Σ[ s' ∈ CS.S ] (InK (fst s')
                  × ⟨ (s' ∷ c ∷ δ₁) ⊨ ( prAtL i0 (sh3 (sh2 Ni)) (sh3 (sh2 N0)) ∧̇ prAtL i1 i2 i0 ) ⟩)
              → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
          byS (s' , (_ , (es , ec))) = inC c _ c∈
            ( keyVal1 χ k' (numeralL 0) e
            ∙ sym (cVal1 c s' (fst (numeralL k)) (fst (lookup (sh2 Ni) γ′)) (fst (numeralL 0)) k'
                     (pr-out i1 i2 i0 (s' ∷ c ∷ δ₁) ec)
                     (pr-out i0 (sh3 (sh2 Ni)) (sh3 (sh2 N0)) (s' ∷ c ∷ δ₁) es
                       ∙ cong (pr (fst (lookup (sh2 Ni) γ′))) (tags2 .t0))
                     te) )

      quC : ∀ {k} (χ₁ : Formula CS.S (suc k)) → ⟨ fst (keyʟ χ₁) ∈ fst Cs ⟩
          → (Ni : Fin m) (k' : ℕ) (χ : Formula CS.S k)
          → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') (LCode.⌜ χ₁ ⌝)
          → fst (lookup (sh2 Ni) γ′) ≡ fst (numeralL k')
          → ⟨ γ′ ⊨ Close.quAt {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (sh2 Ni) ⟩
          → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
      quC {k} χ₁ c₁∈ Ni k' χ e te h = PT.rec (snd (_ ∈ fst Cs)) byC
        (h (keyʟ χ₁) c₁∈ (numeralL k) (C.numO k) (numeralL (suc k)) (C.numK (suc k))
           (LCode.⌜ χ₁ ⌝) (codeK χ₁ c₁∈)
           ( pr-in i3 i1 i0 δ₄ (prʟ-fst (numeralL (suc k)) (LCode.⌜ χ₁ ⌝))
           , suc-in i2 i1 δ₄ (sucNum k) ))
        where
        δ₄ : CS.S ^ (4 + (2 + m))
        δ₄ = LCode.⌜ χ₁ ⌝ ∷ numeralL (suc k) ∷ numeralL k ∷ keyʟ χ₁ ∷ γ′
        byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst Cs ⟩
                × ⟨ (c ∷ δ₄) ⊨ ∃̇∈ (var (sh5 (sh2 K)))
                    ( prAtL i0 (sh6 (sh2 Ni)) i2 ∧̇ prAtL i1 i4 i0 ) ⟩)
            → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
        byC (c , (c∈ , hs)) = PT.rec (snd (_ ∈ fst Cs)) byS hs
          where
          byS : Σ[ s' ∈ CS.S ] (InK (fst s')
                  × ⟨ (s' ∷ c ∷ δ₄) ⊨ ( prAtL i0 (sh6 (sh2 Ni)) i2 ∧̇ prAtL i1 i4 i0 ) ⟩)
              → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
          byS (s' , (_ , (es , ec))) = inC c _ c∈
            ( keyVal1 χ k' (LCode.⌜ χ₁ ⌝) e
            ∙ sym (cVal1 c s' (fst (numeralL k)) (fst (lookup (sh2 Ni) γ′)) (fst (LCode.⌜ χ₁ ⌝)) k'
                     (pr-out i1 i4 i0 (s' ∷ c ∷ δ₄) ec)
                     (pr-out i0 (sh6 (sh2 Ni)) i2 (s' ∷ c ∷ δ₄) es)
                     te) )

      bqC : ∀ {k} (t : Term ⟪ fst W ⟫ k) (χ₁ : Formula CS.S (suc k)) → ⟨ fst (keyʟ χ₁) ∈ fst Cs ⟩
          → (Ni : Fin m) (k' : ℕ) (χ : Formula CS.S k)
          → LCode.⌜ χ ⌝ ≡ prʟ (numeralL k') (prʟ (LCode.⌜ toT t ⌝ᵗ) (LCode.⌜ χ₁ ⌝))
          → fst (lookup (sh2 Ni) γ′) ≡ fst (numeralL k')
          → ⟨ γ′ ⊨ Close.bqAt {2 + m} i1 (sh2 O) (sh2 w) (sh2 K)
                (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) (sh2 Ni) ⟩
          → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
      bqC {k} t χ₁ c₁∈ Ni k' χ e te h = PT.rec (snd (_ ∈ fst Cs)) byC
        (h (keyʟ χ₁) c₁∈ (numeralL k) (C.numO k) (numeralL (suc k)) (C.numK (suc k))
           (LCode.⌜ toT t ⌝ᵗ) (tmK t) (LCode.⌜ χ₁ ⌝) (codeK χ₁ c₁∈)
           ( tmAt-in t δ₅ i1 i3 (sh5 (sh2 w)) (sh5 (sh2 K)) (sh5 (sh2 N0)) (sh5 (sh2 N1))
               refl refl refl refl (tags2 .t0) (tags2 .t1)
           , ( pr-in i4 i2 i0 δ₅ (prʟ-fst (numeralL (suc k)) (LCode.⌜ χ₁ ⌝))
             , suc-in i3 i2 δ₅ (sucNum k) ) ))
        where
        δ₅ : CS.S ^ (5 + (2 + m))
        δ₅ = LCode.⌜ χ₁ ⌝ ∷ LCode.⌜ toT t ⌝ᵗ ∷ numeralL (suc k) ∷ numeralL k ∷ keyʟ χ₁ ∷ γ′
        P : V ℓ
        P = pr (fst (LCode.⌜ toT t ⌝ᵗ)) (fst (LCode.⌜ χ₁ ⌝))
        byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst Cs ⟩
                × ⟨ (c ∷ δ₅) ⊨ ∃̇∈ (var (sh6 (sh2 K))) (∃̇∈ (var (suc (sh6 (sh2 K))))
                    ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i6 i0 ))) ⟩)
            → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
        byC (c , (c∈ , hq)) = PT.rec (snd (_ ∈ fst Cs)) byQ hq
          where
          byQ : Σ[ q ∈ CS.S ] (InK (fst q)
                  × ⟨ (q ∷ c ∷ δ₅) ⊨ ∃̇∈ (var (suc (sh6 (sh2 K))))
                      ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i6 i0 )) ⟩)
              → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
          byQ (q , (_ , hs)) = PT.rec (snd (_ ∈ fst Cs)) byS hs
            where
            byS : Σ[ s' ∈ CS.S ] (InK (fst s')
                    × ⟨ (s' ∷ q ∷ c ∷ δ₅) ⊨
                        ( prAtL i1 i4 i3 ∧̇ ( prAtL i0 (sh8 (sh2 Ni)) i1 ∧̇ prAtL i2 i6 i0 )) ⟩)
                → ⟨ fst (keyʟ χ) ∈ fst Cs ⟩
            byS (s' , (_ , (eq , (es , ec)))) = inC c _ c∈
              ( keyVal2 χ k' (LCode.⌜ toT t ⌝ᵗ) (LCode.⌜ χ₁ ⌝) e
              ∙ sym (cVal2 c s' q (fst (numeralL k)) (fst (lookup (sh2 Ni) γ′)) P k'
                       (pr-out i2 i6 i0 (s' ∷ q ∷ c ∷ δ₅) ec)
                       (pr-out i0 (sh8 (sh2 Ni)) i1 (s' ∷ q ∷ c ∷ δ₅) es)
                       (pr-out i1 i4 i3 (s' ∷ q ∷ c ∷ δ₅) eq)
                       te) )

    -- THE INDUCTION.
    key∈C : ∀ {k} (ψ : Formula ⟪ fst W ⟫ k) → ⟨ fst (keyʟ (toS ψ)) ∈ fst Cs ⟩
    key∈C (t ∈̇ u) = atomC t u N0 0 (toS (t ∈̇ u)) refl (tags2 .t0) hAt0
    key∈C (t ≐ u) = atomC t u N1 1 (toS (t ≐ u)) refl (tags2 .t1) hAt1
    key∈C (a ∧̇ b) = binC (toS a) (toS b) (key∈C a) (key∈C b) N2 2 (toS (a ∧̇ b)) refl (tags2 .t2) hBin2
    key∈C (a ∨̇ b) = binC (toS a) (toS b) (key∈C a) (key∈C b) N3 3 (toS (a ∨̇ b)) refl (tags2 .t3) hBin3
    key∈C (a ⇒̇ b) = binC (toS a) (toS b) (key∈C a) (key∈C b) N4 4 (toS (a ⇒̇ b)) refl (tags2 .t4) hBin4
    key∈C (¬̇ a) = unC (toS a) (key∈C a) N5 5 (toS (¬̇ a)) refl (tags2 .t5) hUn5
    key∈C ⊤̇ = conC N6 6 (toS ⊤̇) refl (tags2 .t6) hCon6
    key∈C ⊥̇ = conC N7 7 (toS ⊥̇) refl (tags2 .t7) hCon7
    key∈C (∃̇ a) = quC (toS a) (key∈C a) N8 8 (toS (∃̇ a)) refl (tags2 .t8) hQu8
    key∈C (∀̇ a) = quC (toS a) (key∈C a) N9 9 (toS (∀̇ a)) refl (tags2 .t9) hQu9
    key∈C (∀̇∈ t a) = bqC t (toS a) (key∈C a) N10 10 (toS (∀̇∈ t a)) refl (tags2 .t10) hBq10
    key∈C (∃̇∈ t a) = bqC t (toS a) (key∈C a) N11 11 (toS (∃̇∈ t a)) refl (tags2 .t11) hBq11

    -- =================================================================
    -- THE TWO INCLUSIONS.  A member of d is cut from w by the table's
    -- value at an arity-one code, which is a key (the code set is its
    -- own closed shaped witness), whose value is the satisfaction set;
    -- and every definable subset of w is cut out by the key of its
    -- formula, which lies in C, so the completeness half puts it in d.
    -- =================================================================

    -- THE DEFINABLE SUBSET, READ AT VARIABLES.  The value A and the set
    -- D are abstract, tied by a membership bridge; the proof is sealed,
    -- and the one instantiation below meets `defSet-Sat` at its own
    -- spelling.  Measured at this site: the two readings stated at the
    -- concrete value, where a second name for the carrier met `fst W`
    -- under the fully applied `defSet`, cost 6.1 s and 5.0 s.
    private
      module DefRd {n'} (δ : CS.S ^ n') (xi wi vi : Fin n') (D A : V ℓ)
                   (qw : fst (lookup wi δ) ≡ fst W)
                   (D⊆ : (y : V ℓ) → ⟨ y ∈ D ⟩ → ⟨ y ∈ fst W ⟩)
                   (qv : fst (lookup vi δ) ≡ A)
                   (br : (q : ⟪ fst W ⟫) → (⟪ fst W ⟫↪ q ∈ D) ≡ (envOne (⟪ fst W ⟫↪ q) ∈ A))
                   (hD : ⟨ δ ⊨ DefinesAt xi wi vi ⟩) where
        opaque
          eq : fst (lookup xi δ) ≡ D
          eq = extensionalV {a = fst (lookup xi δ)} {b = D}
            (λ y → ⇔toPath (fwd y) (bwd y))
            where
            fwd : (y : V ℓ) → ⟨ y ∈ fst (lookup xi δ) ⟩ → ⟨ y ∈ D ⟩
            fwd y y∈ = subst (λ u → ⟨ u ∈ D ⟩) (fib .snd)
              (subst ⟨_⟩ (sym (br (fib .fst)))
                (subst (λ u → ⟨ envOne u ∈ A ⟩) (sym (fib .snd))
                  (subst (λ u → ⟨ envOne y ∈ u ⟩) qv (hz .snd))))
              where
              yS : CS.S
              yS = down (lookup xi δ) y y∈
              hz : ⟨ fst yS ∈ fst (lookup wi δ) ⟩ × ⟨ envOne (fst yS) ∈ fst (lookup vi δ) ⟩
              hz = DefinesAt-out xi wi vi δ hD yS y∈
              fib : Σ[ q ∈ ⟪ fst W ⟫ ] (⟪ fst W ⟫↪ q ≡ y)
              fib = ∈-asFiber {a = y} {b = fst W} (subst (λ u → ⟨ y ∈ u ⟩) qw (hz .fst))
            bwd : (y : V ℓ) → ⟨ y ∈ D ⟩ → ⟨ y ∈ fst (lookup xi δ) ⟩
            bwd y y∈ = DefinesAt-in xi wi vi δ hD yS
              ( subst (λ u → ⟨ y ∈ u ⟩) (sym qw) yw
              , subst (λ u → ⟨ envOne u ∈ fst (lookup vi δ) ⟩) (fib .snd)
                  (subst (λ u → ⟨ envOne (⟪ fst W ⟫↪ (fib .fst)) ∈ u ⟩) (sym qv)
                    (subst ⟨_⟩ (br (fib .fst))
                      (subst (λ u → ⟨ u ∈ D ⟩) (sym (fib .snd)) y∈))) )
              where
              yw : ⟨ y ∈ fst W ⟩
              yw = D⊆ y y∈
              yS : CS.S
              yS = y , isL-trans {x = fst W} {y = y} yw (snd W)
              fib : Σ[ q ∈ ⟪ fst W ⟫ ] (⟪ fst W ⟫↪ q ≡ y)
              fib = ∈-asFiber {a = y} {b = fst W} yw

    private
      -- The definable subset of a formula, from the DefinesAt facts at
      -- the satisfaction set: the reading above, instantiated once.
      opaque
        defines-defSet : ∀ {n'} (δ : CS.S ^ n') (xi wi vi : Fin n')
                       → fst (lookup wi δ) ≡ fst W
                       → (ψ : Formula ⟪ fst W ⟫ 1)
                       → fst (lookup vi δ) ≡ fst (Sat W (toS ψ))
                       → ⟨ δ ⊨ DefinesAt xi wi vi ⟩
                       → fst (lookup xi δ) ≡ DefOf.defSet (fst W) ψ
        defines-defSet δ xi wi vi qw ψ qv hD =
          DefRd.eq δ xi wi vi (DefOf.defSet (fst W) ψ) (fst (Sat W (toS ψ))) qw
            (DefOf.defSet⊆A (fst W) ψ) qv (defSet-Sat W ψ) hD

    private
      -- DefinesBS to DefinesAt, at x ∷ γ'' with the value at v and the
      -- carrier at w.
      module Def3 (e0 e1 e2 : CS.S) (xi vi : Fin (3 + (2 + m))) where
        module DfA = DefinesAgree {3 + (2 + m)} xi (sh3 (sh2 w)) vi (sh3 (sh2 K)) (sh3 (sh2 N0))
                      (e0 ∷ e1 ∷ e2 ∷ γ′)
                      (tags2 .t0) (C.numK 0) C.pairK
                      (λ u hu → C.transK (fst W) (fst u) wK hu) arityK
                      (λ z hz → C.transK (fst W) (fst z) wK (hz .fst)) using (back)

    -- SOUNDNESS HALF: every member of d is a definable subset of w.
    into : (x : V ℓ) → ⟨ x ∈ fst (lookup d γ) ⟩ → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
    into x x∈ = PT.rec (snd (x ∈ 𝒟ₒ (fst W))) byC (hmem xS x∈)
      where
      xS : CS.S
      xS = down (lookup d γ) x x∈
      byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ fst Cs ⟩
              × ⟨ (c ∷ xS ∷ γ′) ⊨ ∃̇∈ (var (sh2 (sh2 K)))
                  ( keyArBS i1 (sh3 (sh2 N1)) (sh3 (sh2 K))
                  ∧̇ ( appAt (sh3 i0) i1 i0
                    ∧̇ DefinesBS i2 (sh3 (sh2 w)) i0 (sh3 (sh2 K)) (sh3 (sh2 N0)) )) ⟩)
          → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
      byC (c , (c∈ , hv)) = PT.rec (snd (x ∈ 𝒟ₒ (fst W))) byV hv
        where
        byV : Σ[ v ∈ CS.S ] (InK (fst v)
                × ⟨ (v ∷ c ∷ xS ∷ γ′) ⊨
                    ( keyArBS i1 (sh3 (sh2 N1)) (sh3 (sh2 K))
                    ∧̇ ( appAt (sh3 i0) i1 i0
                      ∧̇ DefinesBS i2 (sh3 (sh2 w)) i0 (sh3 (sh2 K)) (sh3 (sh2 N0)) )) ⟩)
            → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
        byV (v , (_ , (hk , (ha , hdB)))) = PT.rec (snd (x ∈ 𝒟ₒ (fst W))) byT hk
          where
          hcv : ⟨ pr (fst c) (fst v) ∈ fst Ts ⟩
          hcv = app-out (sh3 i0) i1 i0 (v ∷ c ∷ xS ∷ γ′) ha
          hD : ⟨ (v ∷ c ∷ xS ∷ γ′) ⊨ DefinesAt i2 (sh3 (sh2 w)) i0 ⟩
          hD = Def3.DfA.back v c xS i2 i0 hdB
          byT : Σ[ t ∈ CS.S ] (InK (fst t)
                  × ⟨ (t ∷ v ∷ c ∷ xS ∷ γ′) ⊨ ∃̇∈ (var (suc (sh3 (sh2 K))))
                      ((var zero ≐ var (suc (suc (sh3 (sh2 N1)))))
                       ∧̇ prAtL (suc (suc i1)) zero (suc zero)) ⟩)
              → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
          byT (t , (_ , har)) = PT.rec (snd (x ∈ 𝒟ₒ (fst W))) byAr har
            where
            byAr : Σ[ ar ∈ CS.S ] (InK (fst ar)
                     × ⟨ (ar ∷ t ∷ v ∷ c ∷ xS ∷ γ′) ⊨
                         ((var zero ≐ var (suc (suc (sh3 (sh2 N1)))))
                          ∧̇ prAtL (suc (suc i1)) zero (suc zero)) ⟩)
                 → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
            byAr (ar , (_ , (ae , ap))) = PT.rec (snd (x ∈ 𝒟ₒ (fst W))) byψ
              (codeAt-out W zero (sh3 w) (c ∷ γ′) refl (hk1 , hw1))
              where
              ceq : fst c ≡ pr (# 1) (fst t)
              ceq = pr-out (suc (suc i1)) zero (suc zero) (ar ∷ t ∷ v ∷ c ∷ xS ∷ γ′) ap
                  ∙ cong (λ u → pr u (fst t)) (ae ∙ tags2 .t1 ∙ numeralL-fst 1)
              hk1 : ⟨ (c ∷ γ′) ⊨ keyArityAtL zero 1 ⟩
              hk1 = keyArityAtL-in zero 1 (c ∷ γ′) t ceq
              hw1 : ⟨ (c ∷ γ′) ⊨ hasWitnessAt (sh3 w) zero ⟩
              hw1 = ∣ Cs , (c∈ , (closed , shaped)) ∣₁
              byψ : Σ[ ψ ∈ Formula ⟪ fst W ⟫ 1 ] (fst c ≡ fst (keyS W ψ)) → ⟨ x ∈ 𝒟ₒ (fst W) ⟩
              byψ (ψ , qc) = 𝒟ₒ-intro (fst W) x ∣ ψ , sym xeq ∣₁
                where
                qv : fst v ≡ fst (Sat W (toS ψ))
                qv = pinned (toS ψ) c v (qc ∙ keyBridge W ψ) c∈ hcv
                xeq : x ≡ DefOf.defSet (fst W) ψ
                xeq = defines-defSet (v ∷ c ∷ xS ∷ γ′) i2 (sh3 (sh2 w)) i0 refl ψ qv hD

    -- COMPLETENESS HALF: every definable subset of w is a member of d.
    over : (y : V ℓ) → ⟨ y ∈ 𝒟ₒ (fst W) ⟩ → ⟨ y ∈ fst (lookup d γ) ⟩
    over y y∈ = PT.rec (snd (y ∈ fst (lookup d γ))) byψ (𝒟ₒ-inv (fst W) y y∈)
      where
      byψ : Σ[ ψ ∈ Formula ⟪ fst W ⟫ 1 ] (DefOf.defSet (fst W) ψ ≡ y) → ⟨ y ∈ fst (lookup d γ) ⟩
      byψ (ψ , qy) = PT.rec (snd (y ∈ fst (lookup d γ))) byV
        (hall c c∈ ∣ LCode.⌜ toS ψ ⌝ , (codeK (toS ψ) c∈
              , ∣ numeralL 1 , (C.numK 1 , (sym (tags2 .t1)
                , pr-in (suc (suc i0)) zero (suc zero) (numeralL 1 ∷ LCode.⌜ toS ψ ⌝ ∷ c ∷ γ′)
                    (prʟ-fst (numeralL 1) (LCode.⌜ toS ψ ⌝)))) ∣₁) ∣₁)
        where
        c : CS.S
        c = keyʟ (toS ψ)
        c∈ : ⟨ fst c ∈ fst Cs ⟩
        c∈ = key∈C ψ
        byV : Σ[ v ∈ CS.S ] (InK (fst v)
                × ⟨ (v ∷ c ∷ γ′) ⊨ ( appAt (sh2 i0) i1 i0
                    ∧̇ ∃̇∈ (var (sh2 (sh2 d))) (DefinesBS i0 (sh3 (sh2 w)) i1 (sh3 (sh2 K)) (sh3 (sh2 N0))) ) ⟩)
            → ⟨ y ∈ fst (lookup d γ) ⟩
        byV (v , (_ , (ha , hx))) = PT.rec (snd (y ∈ fst (lookup d γ))) byX hx
          where
          hcv : ⟨ pr (fst c) (fst v) ∈ fst Ts ⟩
          hcv = app-out (sh2 i0) i1 i0 (v ∷ c ∷ γ′) ha
          qv : fst v ≡ fst (Sat W (toS ψ))
          qv = pinned (toS ψ) c v refl c∈ hcv
          byX : Σ[ x ∈ CS.S ] (⟨ fst x ∈ fst (lookup d γ) ⟩
                  × ⟨ (x ∷ v ∷ c ∷ γ′) ⊨ DefinesBS i0 (sh3 (sh2 w)) i1 (sh3 (sh2 K)) (sh3 (sh2 N0)) ⟩)
              → ⟨ y ∈ fst (lookup d γ) ⟩
          byX (x , (x∈d , hdB)) = subst (λ u → ⟨ u ∈ fst (lookup d γ) ⟩) (xeq ∙ qy) x∈d
            where
            hD : ⟨ (x ∷ v ∷ c ∷ γ′) ⊨ DefinesAt i0 (sh3 (sh2 w)) i1 ⟩
            hD = Def3.DfA.back x v c i0 i1 hdB
            xeq : fst x ≡ DefOf.defSet (fst W) ψ
            xeq = defines-defSet (x ∷ v ∷ c ∷ γ′) i0 (sh3 (sh2 w)) i1 refl ψ qv hD

    -- THE ROW IS SOUND.
    def-eq : fst (lookup d γ) ≡ 𝒟ₒ (fst W)
    def-eq = extensionalV {a = fst (lookup d γ)} {b = 𝒟ₒ (fst W)}
      (λ x → ⇔toPath (into x) (over x))

  -- THE READING, spending the two existentials of the row and the
  -- tower's.
  def-sound : ⟨ γ ⊨ DV.defAt ⟩ → fst (lookup d γ) ≡ 𝒟ₒ (fst (lookup w γ))
  def-sound h = PT.rec (setIsSet _ _) byC (DV.defAt-out γ h)
    where
    byC : Σ[ Cs ∈ CS.S ] (InK (fst Cs) × ⟨ (Cs ∷ γ) ⊨ ∃̇∈ (var (sh1 K)) DV.body ⟩)
        → fst (lookup d γ) ≡ 𝒟ₒ (fst (lookup w γ))
    byC (Cs , (CK , hT)) = PT.rec (setIsSet _ _) byT hT
      where
      byT : Σ[ Ts ∈ CS.S ] (InK (fst Ts) × ⟨ (Ts ∷ Cs ∷ γ) ⊨ DV.body ⟩)
          → fst (lookup d γ) ≡ 𝒟ₒ (fst (lookup w γ))
      byT (Ts , (TK , hb)) = PT.rec (setIsSet _ _) byÊ (hb .snd .snd .snd .snd .snd .fst)
        where
        byÊ : Σ[ Ês ∈ CS.S ] (InK (fst Ês)
                × ⟨ (Ês ∷ Ts ∷ Cs ∷ γ) ⊨ towerAt i0 (sh3 O) (sh3 w) (sh3 K) ⟩)
            → fst (lookup d γ) ≡ 𝒟ₒ (fst (lookup w γ))
        byÊ (Ês , (ÊK , htow)) = Body.def-eq Cs Ts Ês CK TK ÊK hb htow

-- THE HYPOTHESIS OF STEP 4, DISCHARGED.
defSound : DefSound
defSound d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ kc tags wK h =
  DefRead.def-sound d w O K N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ kc tags wK h

-- =====================================================================
-- STEP 4.  THE STEP, THE APPROXIMATION AND THE GRAPH, READ AGAINST
-- THE TOWER.  src/L/Hierarchy.lagda.md `step-Lset`, `approx-val` and
-- `Lset-only`, at the bounded rows: the only change is that the
-- definable powerset arrives by `DefSound` instead of `DefAt-out`,
-- and each recorded value is put into K by transitivity before the
-- K-bounded quantifiers can reach it.
-- =====================================================================

module Sound4 (ds : DefSound) where

  -- THE STEP.  At v ∷ ... with the slots v b f K O and the tags.
  module Step {m : ℕ} (v b f K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
              (γ : CS.S ^ m)
              (kc : KC (fst (lookup K γ)) (fst (lookup O γ)))
              (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
              (fK : ⟨ fst (lookup f γ) ∈ fst (lookup K γ) ⟩)
              (bK : ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩) where

    module SV = StepV {m} v b f K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 using (intoAt; overAt; stepAt)
    module Z = Chain (fst (lookup K γ)) (KC.transK (fst (lookup K γ)) (fst (lookup O γ)) kc) using (sndK)

    private
      Kv Bv Fv Vv : V ℓ
      Kv = fst (lookup K γ)
      Bv = fst (lookup b γ)
      Fv = fst (lookup f γ)
      Vv = fst (lookup v γ)

      InK : V ℓ → Type (ℓ-suc ℓ)
      InK x = ⟨ x ∈ Kv ⟩

    -- SOUNDNESS HALF: a member of v lies in the definable powerset of
    -- a recorded value, hence, by correctness, in the tower at b.
    into : ⟨ γ ⊨ SV.intoAt ⟩ → Values (lookup f γ) Bv
         → (x : V ℓ) → ⟨ x ∈ Vv ⟩ → ⟨ x ∈ Lset Bv ⟩
    into h vals x x∈ = PT.rec (snd (x ∈ Lset Bv)) byC (h xS x∈)
      where
      xS : CS.S
      xS = down (lookup v γ) x x∈

      byC : Σ[ c ∈ CS.S ] (⟨ fst c ∈ Bv ⟩
              × ⟨ (c ∷ xS ∷ γ) ⊨ ∃̇∈ (var (sh2 K)) (∃̇∈ (var (sh3 K))
                  ( appAt (sh4 f) i2 i1
                  ∧̇ ( DefV.defAt {4 + m} i0 i1 (sh4 O) (sh4 K)
                        (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
                        (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11)
                    ∧̇ (var i3 ∈̇ var i0) ))) ⟩)
          → ⟨ x ∈ Lset Bv ⟩
      byC (c , c∈b , hc) = PT.rec (snd (x ∈ Lset Bv)) byW hc
        where
        byW : Σ[ w ∈ CS.S ] (InK (fst w)
                × ⟨ (w ∷ c ∷ xS ∷ γ) ⊨ ∃̇∈ (var (sh3 K))
                    ( appAt (sh4 f) i2 i1
                    ∧̇ ( DefV.defAt {4 + m} i0 i1 (sh4 O) (sh4 K)
                          (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
                          (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11)
                      ∧̇ (var i3 ∈̇ var i0) )) ⟩)
            → ⟨ x ∈ Lset Bv ⟩
        byW (w , wK , hw) = PT.rec (snd (x ∈ Lset Bv)) byD hw
          where
          byD : Σ[ d ∈ CS.S ] (InK (fst d)
                  × ⟨ (d ∷ w ∷ c ∷ xS ∷ γ) ⊨
                      ( appAt (sh4 f) i2 i1
                      ∧̇ ( DefV.defAt {4 + m} i0 i1 (sh4 O) (sh4 K)
                            (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
                            (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11)
                        ∧̇ (var i3 ∈̇ var i0) )) ⟩)
              → ⟨ x ∈ Lset Bv ⟩
          byD (d , dK , (ha , (hd , x∈d))) =
            Lset-in Bv (fst c) x c∈b
              (subst (λ u → ⟨ x ∈ u ⟩) (dq ∙ cong 𝒟ₒ wq) x∈d)
            where
            rec : ⟨ pr (fst c) (fst w) ∈ Fv ⟩
            rec = app-out (sh4 f) i2 i1 (d ∷ w ∷ c ∷ xS ∷ γ) ha
            wq : fst w ≡ Lset (fst c)
            wq = vals c w c∈b rec
            dq : fst d ≡ 𝒟ₒ (fst w)
            dq = ds {4 + m} i0 i1 (sh4 O) (sh4 K)
                   (sh4 N0) (sh4 N1) (sh4 N2) (sh4 N3) (sh4 N4) (sh4 N5)
                   (sh4 N6) (sh4 N7) (sh4 N8) (sh4 N9) (sh4 N10) (sh4 N11)
                   (d ∷ w ∷ c ∷ xS ∷ γ) kc
                   (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (w ∷ c ∷ xS ∷ γ) d
                     (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (c ∷ xS ∷ γ) w
                       (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (xS ∷ γ) c
                         (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ xS tags))))
                   wK hd

    -- COMPLETENESS HALF: a member of the tower at b lies in the
    -- definable powerset of the tower at some c ∈ b, which the
    -- approximation records; the row then puts the powerset into K
    -- and under v.
    over : ⟨ γ ⊨ SV.overAt ⟩ → IsOrd Bv → Entries (lookup f γ) Bv
         → (x : V ℓ) → ⟨ x ∈ Lset Bv ⟩ → ⟨ x ∈ Vv ⟩
    over h ob ents x x∈ = PT.rec (snd (x ∈ Vv)) put (Lset-out Bv x x∈)
      where
      put : Σ[ δ ∈ V ℓ ] (⟨ δ ∈ Bv ⟩ × ⟨ x ∈ 𝒟ₒ (Lset δ) ⟩) → ⟨ x ∈ Vv ⟩
      put (δ , δ∈b , x∈D) = PT.rec (snd (x ∈ Vv)) byD
        (h c δ∈b Lδ LδK (app-in (sh2 f) i1 i0 (Lδ ∷ c ∷ γ) rec))
        where
        oδ : IsOrd δ
        oδ = mem-ord {A = Bv} ob δ δ∈b
        c : CS.S
        c = down (lookup b γ) δ δ∈b
        Lδ : CS.S
        Lδ = LsetS δ oδ
        rec : ⟨ pr δ (Lset δ) ∈ Fv ⟩
        rec = ents c δ∈b
        LδK : InK (Lset δ)
        LδK = Z.sndK Fv δ (Lset δ) fK rec

        byD : Σ[ d ∈ CS.S ] (InK (fst d)
                × ⟨ (d ∷ Lδ ∷ c ∷ γ) ⊨
                    ( DefV.defAt {3 + m} i0 i1 (sh3 O) (sh3 K)
                        (sh3 N0) (sh3 N1) (sh3 N2) (sh3 N3) (sh3 N4) (sh3 N5)
                        (sh3 N6) (sh3 N7) (sh3 N8) (sh3 N9) (sh3 N10) (sh3 N11)
                    ∧̇ ∀̇∈ (var i0) (var i0 ∈̇ var (sh4 v)) ) ⟩)
            → ⟨ x ∈ Vv ⟩
        byD (d , dK , (hd , sub)) = sub xS x∈d
          where
          dq : fst d ≡ 𝒟ₒ (Lset δ)
          dq = ds {3 + m} i0 i1 (sh3 O) (sh3 K)
                 (sh3 N0) (sh3 N1) (sh3 N2) (sh3 N3) (sh3 N4) (sh3 N5)
                 (sh3 N6) (sh3 N7) (sh3 N8) (sh3 N9) (sh3 N10) (sh3 N11)
                 (d ∷ Lδ ∷ c ∷ γ) kc
                 (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (Lδ ∷ c ∷ γ) d
                   (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (c ∷ γ) Lδ
                     (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ c tags)))
                 LδK hd
          x∈d : ⟨ x ∈ fst d ⟩
          x∈d = subst (λ u → ⟨ x ∈ u ⟩) (sym dq) x∈D
          xS : CS.S
          xS = down d x x∈d

    step-Lset : ⟨ γ ⊨ SV.stepAt ⟩ → IsOrd Bv
              → Values (lookup f γ) Bv → Entries (lookup f γ) Bv
              → Vv ≡ Lset Bv
    step-Lset (hi , ho) ob vals ents =
      extensionalV {a = Vv} {b = Lset Bv}
        (λ x → ⇔toPath (into hi vals x) (over ho ob ents x))

  -- THE APPROXIMATION.  Every recorded value is the tower there, by
  -- ∈-induction on the argument (src/L/Hierarchy.lagda.md `approx-val`).
  module Approx {m : ℕ} (f a K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
                (γ : CS.S ^ m)
                (kc : KC (fst (lookup K γ)) (fst (lookup O γ)))
                (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
                (fK : ⟨ fst (lookup f γ) ∈ fst (lookup K γ) ⟩)
                (aK : ⟨ fst (lookup a γ) ∈ fst (lookup K γ) ⟩)
                (h : ⟨ γ ⊨ ApproxV.approxAt f a K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩)
                (oa : IsOrd (fst (lookup a γ))) where

    module Z = Chain (fst (lookup K γ)) (KC.transK (fst (lookup K γ)) (fst (lookup O γ)) kc) using (fstK; prK-fst; prK-snd; sndK)

    private
      Kv Av Fv : V ℓ
      Kv = fst (lookup K γ)
      Av = fst (lookup a γ)
      Fv = fst (lookup f γ)

      InK : V ℓ → Type (ℓ-suc ℓ)
      InK x = ⟨ x ∈ Kv ⟩

    -- The domain, both ways, from `domB` (the K bounds are supplied
    -- by transitivity).
    dom-out : (c z : CS.S) → ⟨ pr (fst c) (fst z) ∈ Fv ⟩ → ⟨ fst c ∈ Av ⟩
    dom-out c z p = h .fst c cK .fst
      ∣ z , ( Z.sndK Fv (fst c) (fst z) fK p
            , app-in (sh2 f) i1 i0 (z ∷ c ∷ γ) p ) ∣₁
      where
      cK : InK (fst c)
      cK = Z.fstK Fv (fst c) (fst z) fK p

    dom-in : (c : CS.S) → ⟨ fst c ∈ Av ⟩
           → ∥ Σ[ z ∈ CS.S ] ⟨ pr (fst c) (fst z) ∈ Fv ⟩ ∥₁
    dom-in c c∈ = PT.map
      (λ { (z , (_ , ap)) → z , app-out (sh2 f) i1 i0 (z ∷ c ∷ γ) ap })
      (h .fst c (KC.transK (fst (lookup K γ)) (fst (lookup O γ)) kc Av (fst c) aK c∈) .snd c∈)

    private
      Value : V ℓ → Type (ℓ-suc ℓ)
      Value u = ⟨ isL u ⟩ → (z : CS.S) → ⟨ pr u (fst z) ∈ Fv ⟩ → fst z ≡ Lset u

    approx-val : (x z : CS.S) → ⟨ pr (fst x) (fst z) ∈ Fv ⟩ → fst z ≡ Lset (fst x)
    approx-val x = ∈-induction {P = Value} go (fst x) (snd x)
      where
      go : (u : V ℓ) → ((t : V ℓ) → ⟨ t ∈ u ⟩ → Value t) → Value u
      go u IH hu z p =
        St.step-Lset hs ou vals ents
        where
        d : CS.S
        d = u , hu
        uK : InK u
        uK = Z.fstK Fv u (fst z) fK p
        zK : InK (fst z)
        zK = Z.sndK Fv u (fst z) fK p
        u∈a : ⟨ u ∈ Av ⟩
        u∈a = dom-out d z p
        ou : IsOrd u
        ou = mem-ord {A = Av} oa u u∈a
        hs : ⟨ (z ∷ d ∷ γ) ⊨ StepV.stepAt {2 + m} i0 i1 (sh2 f) (sh2 K) (sh2 O)
                (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11) ⟩
        hs = h .snd d uK z zK (app-in (sh2 f) i1 i0 (z ∷ d ∷ γ) p)
        module St = Step {2 + m} i0 i1 (sh2 f) (sh2 K) (sh2 O)
                      (sh2 N0) (sh2 N1) (sh2 N2) (sh2 N3) (sh2 N4) (sh2 N5)
                      (sh2 N6) (sh2 N7) (sh2 N8) (sh2 N9) (sh2 N10) (sh2 N11)
                      (z ∷ d ∷ γ) kc
                      (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ (d ∷ γ) z
                        (tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ d tags))
                      fK uK using (step-Lset)
        vals : Values (lookup f γ) u
        vals c y c∈ q = IH (fst c) c∈ (snd c) y q
        ents : Entries (lookup f γ) u
        ents c c∈ = PT.rec (snd (pr (fst c) (Lset (fst c)) ∈ Fv)) named
          (dom-in c (oa .fst {x = u} {y = fst c} c∈ u∈a))
          where
          named : Σ[ y ∈ CS.S ] ⟨ pr (fst c) (fst y) ∈ Fv ⟩
                → ⟨ pr (fst c) (Lset (fst c)) ∈ Fv ⟩
          named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ Fv ⟩)
            (IH (fst c) c∈ (snd c) y q) q

  -- THE GRAPH: whatever satisfies it at an ordinal is the tower there.
  module Graph {m : ℕ} (w b K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 : Fin m)
               (γ : CS.S ^ m)
               (kc : KC (fst (lookup K γ)) (fst (lookup O γ)))
               (tags : Tags N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 γ)
               (bK : ⟨ fst (lookup b γ) ∈ fst (lookup K γ) ⟩) where

    private
      Kv Bv Wv : V ℓ
      Kv = fst (lookup K γ)
      Bv = fst (lookup b γ)
      Wv = fst (lookup w γ)

    graph-Lset : ⟨ γ ⊨ GraphV.graphAt w b K O N0 N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 ⟩
               → IsOrd Bv → Wv ≡ Lset Bv
    graph-Lset h ob = PT.rec (setIsSet Wv (Lset Bv)) go h
      where
      go : Σ[ f ∈ CS.S ] (⟨ fst f ∈ Kv ⟩
             × ⟨ (f ∷ γ) ⊨
                 ( ApproxV.approxAt {1 + m} i0 (sh1 b) (sh1 K) (sh1 O)
                     (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                     (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11)
                 ∧̇ StepV.stepAt {1 + m} (sh1 w) (sh1 b) i0 (sh1 K) (sh1 O)
                     (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                     (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11) ) ⟩)
         → Wv ≡ Lset Bv
      go (f , fK , (ha , hs)) = St.step-Lset hs ob vals ents
        where
        tags' = tagsCons _ _ _ _ _ _ _ _ _ _ _ _ γ f tags
        module Ap = Approx {1 + m} i0 (sh1 b) (sh1 K) (sh1 O)
                      (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                      (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11)
                      (f ∷ γ) kc tags' fK bK ha ob using (approx-val; dom-in)
        module St = Step {1 + m} (sh1 w) (sh1 b) i0 (sh1 K) (sh1 O)
                      (sh1 N0) (sh1 N1) (sh1 N2) (sh1 N3) (sh1 N4) (sh1 N5)
                      (sh1 N6) (sh1 N7) (sh1 N8) (sh1 N9) (sh1 N10) (sh1 N11)
                      (f ∷ γ) kc tags' fK bK using (step-Lset)
        vals : Values f Bv
        vals c z _ p = Ap.approx-val c z p
        ents : Entries f Bv
        ents c c∈ = PT.rec (snd (pr (fst c) (Lset (fst c)) ∈ fst f)) named
          (Ap.dom-in c c∈)
          where
          named : Σ[ y ∈ CS.S ] ⟨ pr (fst c) (fst y) ∈ fst f ⟩
                → ⟨ pr (fst c) (Lset (fst c)) ∈ fst f ⟩
          named (y , q) = subst (λ t → ⟨ pr (fst c) t ∈ fst f ⟩)
            (Ap.approx-val c y q) q

  -- The last step, at the sixteen-slot environment.
  finish : (γ : CS.S ^ 16) → ⟨ γ ⊨ W3V.Mx.matrix ⟩
         → ⟨ fst (lookup W3V.n0 γ) ∈ fst (lookup W3V.kk γ) ⟩
         → ⟨ fst (lookup W3V.oo γ) ∈ fst (lookup W3V.kk γ) ⟩
         → IsOrd (fst (lookup W3V.bb γ))
         → fst (lookup W3V.ww γ) ≡ Lset (fst (lookup W3V.bb γ))
  finish γ h n0K ooK ob = Gr.graph-Lset Cl.hg ob
    where
    open W3V using (bb; kk; n0; n1; n10; n11; n2; n3; n4; n5; n6; n7; n8; n9; oo; ww)
    module Cl = Closure γ h n0K ooK using (bK; hg; kc; tags)
    module Gr = Graph {16} ww bb kk oo n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11
                  γ Cl.kc Cl.tags Cl.bK using (graph-Lset)

  -- THE THEOREM AT THE CLASS CARRIER.  perf: the environment is spelled
  -- out at every step and never abbreviated (src/L/GCH/Sound.lagda.md:481).
  sound-L : (a p z : CS.S) → ⟨ (a ∷ p ∷ z ∷ []) ⊨ embed levelFo ⟩
          → fst a ≡ Lset (fst p)
  sound-L a p z (ho , hφ) =
    go (subst (λ ψ → ⟨ (a ∷ p ∷ z ∷ []) ⊨ ψ ⟩)
              (Cnt.erase-inv W3V.three W3V.count-three) hφ)
    where
    open W3V using (inner; inner-out; s10; s11; s12; s13; s14; s15; s4; s5; s6; s7; s8; s9; three)

    ordp : IsOrd (fst p)
    ordp = ord-out a p z ho

    G : hProp (ℓ-suc ℓ)
    G = (fst a ≡ Lset (fst p)) , setIsSet (fst a) (Lset (fst p))

    go : ⟨ (a ∷ p ∷ z ∷ []) ⊨ three ⟩ → ⟨ G ⟩
    go =
      unwrap s4 (a ∷ p ∷ z ∷ []) {G} λ x12 m12 →
      unwrap s5 (x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x11 m11 →
      unwrap s6 (x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x10 m10 →
      unwrap s7 (x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x9 m9 →
      unwrap s8 (x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x8 m8 →
      unwrap s9 (x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x7 m7 →
      unwrap s10 (x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x6 m6 →
      unwrap s11 (x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x5 m5 →
      unwrap s12 (x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x4 m4 →
      unwrap s13 (x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x3 m3 →
      unwrap s14 (x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x2 m2 →
      unwrap s15 (x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G} λ x1 m1 →
      unwrap inner (x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) {G}
        λ x0 m0 hm →
          finish (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ [])
            (inner-out (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ x8 ∷ x9 ∷ x10 ∷ x11 ∷ x12 ∷ a ∷ p ∷ z ∷ []) hm)
            m0 m12 ordp

  -- THE THEOREM AT THE AMBIENT READING OF A CLASS-CARRIER TRIPLE.
  levelFo-sound : (a p z : CS.S)
                → ⟨ (fst a ∷ fst p ∷ fst z ∷ []) ⊨ₚ levelFo ⟩
                → fst a ≡ Lset (fst p)
  levelFo-sound a p z h =
    sound-L a p z (subst ⟨_⟩ (sym (read Δ₀-levelFo (a ∷ p ∷ z ∷ []))) h)

  -- THE BRIEF'S TYPE, at three ambient sets known to be constructible.
  level-sound-L : (a p z : S) → ⟨ isL a ⟩ → ⟨ isL p ⟩ → ⟨ isL z ⟩
                → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ levelFo ⟩ → a ≡ Lset p
  level-sound-L a p z la lp lz = levelFo-sound (a , la) (p , lp) (z , lz)

-- =====================================================================
-- THE THEOREM.  Step 4 at the discharged hypothesis.
-- =====================================================================

module Final = Sound4 defSound using (level-sound-L)

level-sound : (a p z : S) → ⟨ isL a ⟩ → ⟨ isL p ⟩ → ⟨ isL z ⟩
            → ⟨ (a ∷ p ∷ z ∷ []) ⊨ₚ levelFo ⟩ → a ≡ Lset p
level-sound = Final.level-sound-L
```
