# Every infinite stage injects into its index, internally

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.GCH.StageCount {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; con; _≐_; _∈̇_; _∧̇_; _⇒̇_; ¬̇_; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; regularityV )
open import V.Presentation {ℓ} using ( member; fiber; ↪-inj )
open import V.Model {ℓ} using ( ∈sucV-inl; self∈sucV )
open import V.Coding {ℓ} using ( pr; pr-inj; #-inj′; #mono )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd; isPropIsOrd; Lset; Lset-mono; Lset→isL )
open import L.Ordinal {ℓ} using ( ∈#-elim; mem-ord; suc-ord; ω-ord; numeral-ord; #∈ω; boundingOrd )
open import L.Ordinal.Linear {ℓ} lem using ( Tri; ord-tri )
open import L.Ordinal.Stages {ℓ} lem using ( suc∈or≡ )
open import L.Axioms.Basic {ℓ} using ( LsetS; ∅ʟ; isL-Lset )
open import L.Axioms.Infinity {ℓ} lem using ( ωʟ )
open import L.Stage {ℓ} lem
  using ( LeastOrd; isPropLeastOrd; leastOrd; stage; stage-ord; stage-mem; stage-earliest )
open import L.Coding.Model {ℓ}
  using ( prAtL; prAtL-adequate; prʟ; prʟ-fst; numL
        ; svAt; svAt-in; svAt-out; domAt; domAt-in; domAt-out; domAt-intro
        ; appAt; appAt-adequate; envOverAt; envOverAt-transport
        ; consAtL; consAtL-adequate )
open import L.Coding.Injection {ℓ} lem
  using ( injAt; injAt-in; injAt-out; module Extract; module Small )
open import L.Coding.Environment {ℓ} using ( env; lookup-spec; cons )
open import L.Coding.EnvSet {ℓ} lem
  using ( Ix; envS; envSet; envSet-in; envSet-out; envOver; module Recover )
open import L.Coding.CodeSet {ℓ} lem using ( AllCodes )
open import L.Coding.Sequence {ℓ} lem using ( LsetGraphAt )
open import L.Hierarchy {ℓ} lem using ( Lset-only; Lset-defines )
open import L.Choice.Internal {ℓ} lem using ( domAt-numeral; domAt-fill; LeastNameAt )
open import L.Choice.Adequate {ℓ} lem using ( module At )
open import L.Choice.Name {ℓ} lem using ( module Naming; code-inj; limitCode )
open import L.Choice.Step {ℓ} lem
  using ( carry; memOf; orderAt; orderAt-step; relOf; IsLeastName; leastNameOf; denotesAt
        ; birth; birth-ord; birth-in; birth-mem; birth-suc; module Family )
  renaming ( Mem to MemOf )
open import L.Choice.Before {ℓ} lem using ( codeOrder; codeOrder-fill; codeOrder-rep )
open import L.Choice.Table {ℓ} lem using ( Related; IsRel; ixRel-rep; ixRel-fill )
open import L.Choice.Order {ℓ} lem using ( relL; relL-spec )
open import L.WellOrder.Base {ℓₚ = ℓ-suc ℓ}
  using ( SWO; leastOf; isPropLeastOf; lt; eq; gt ) renaming ( Tri to TriW )
open import L.Recursion {ℓ} lem using ( Recursion; module Of; mereFunct )
open import L.Cardinal {ℓ} lem using ( InjCode; IsCardinalL )
open import L.GCH {ℓ} lem using ( InjL )
open import L.GCH.Assembly {ℓ} lem
  using ( StageCountedCoded; inclusion-coded; injl-trans )
open import L.GCH.CardOf {ℓ} lem using ( cardOf )
open import L.GCH.Definable {ℓ} lem using ( DefinableMap; module Inj )
open import L.GCH.Least {ℓ} lem using ( module Least )
open import L.GCH.Pairing {ℓ} lem
  using ( prodL; prodL-in; Goal; module Step; prod-inj; no-fin; ω⊆; ordL; isL-ord )
open import L.GCH.Sequences {ℓ} lem using ( seqL; seqL-in; seqL-out; seq-count )
open import L.InjChain {ℓ} lem using ( appC; appC-adequate; ω-limit; finite-excl-ω )
open import L.Choice.Finite {ℓ} lem
  using ( Tally; StageOrder; stageOrder; finiteStage; natOrder )  -- lint-agda: keep (StageOrder used as the projection qualifier)
open import L.GCH.OrderType {ℓ} lem using ( Holds; module Code )

open import Cubical.Data.Nat using ( injSuc )
open import Cubical.Data.Nat.Order using ( _<_; isProp≤ )
open import Cubical.Data.FinData using ( toℕ )
open import Cubical.Data.FinData.Properties using ( toℕ<n; fromℕ'; toFromId'; inj-toℕ )
open import Cubical.Data.Sigma using ( Σ≡Prop; ΣPathP )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Foundations.Prelude using ( subst2; J )
open import Cubical.Foundations.HLevels using ( isProp×; isPropΠ2; isPropΠ3 )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_; setIsSet )
open import Cubical.HITs.CumulativeHierarchy.Properties using ( ⟪_⟫; ⟪_⟫↪ )
open import Cubical.HITs.CumulativeHierarchy.Constructions
  using ( module InfinitySet )
open InfinitySet {ℓ} using ( #_; ω; sucV )
import Cubical.Induction.WellFounded as WF
open import Cubical.Induction.WellFounded using ( Acc; acc; WellFounded )
import Cubical.Data.Empty as Empty
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ᵥ using ( _∈ˢ_ )

-- The V-carrier: the ambient membership lives here.
module SV = hPropStructure 𝒮ᵥ using ()
-- The L-carrier: `InjL` lives here.
module SL = hPropStructure 𝒮ʟ using ( S )
open SL using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans using ( _^_; _⊨ᵐ_ )
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )

-- The numeral k as an element of L.
nn : ℕ → S
nn k = # k , numL k

private
  i0 : ∀ {k} → Fin (suc k)
  i0 = zero
  i1 : ∀ {k} → Fin (suc (suc k))
  i1 = suc i0
  i2 : ∀ {k} → Fin (suc (suc (suc k)))
  i2 = suc i1
  i3 : ∀ {k} → Fin (suc (suc (suc (suc k))))
  i3 = suc i2
  i4 : ∀ {k} → Fin (suc (suc (suc (suc (suc k)))))
  i4 = suc i3
  i5 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc k))))))
  i5 = suc i4
  i6 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc k)))))))
  i6 = suc i5
  i7 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc k))))))))
  i7 = suc i6
  i8 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))
  i8 = suc i7
  i9 : ∀ {k} → Fin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k))))))))))
  i9 = suc i8

-- =====================================================================
-- SECTION 0.  TWO FACTS ABOUT ENVIRONMENTS.
--
--   An environment determines its length (read off `domAt`, through
--   the two readings src/L/Choice/Internal.lagda.md exports), and two
--   environments of one length that are equal agree entrywise.
-- =====================================================================

env-len : (E : S) {n n' : ℕ} (h : Fin n → V ℓ) (h' : Fin n' → V ℓ)
        → ((i : Fin n) → ⟨ isL (h i) ⟩) → ((i : Fin n') → ⟨ isL (h' i) ⟩)
        → fst E ≡ env h → fst E ≡ env h' → n ≡ n'
env-len E {n} {n'} h h' cg cg' q q' =
  #-inj′ (domAt-numeral (suc zero) zero (nn n ∷ E ∷ []) n' h' cg' q'
            (domAt-fill (suc zero) zero (nn n ∷ E ∷ []) n h cg q refl))

env-pt : {n : ℕ} (h h' : Fin n → V ℓ) → env h ≡ env h' → (i : Fin n) → h i ≡ h' i
env-pt h h' q i = subst ⟨_⟩ (lookup-spec h' i (h i))
  (subst (λ w → ⟨ pr (# (toℕ i)) (h i) ∈ w ⟩) q
    (subst ⟨_⟩ (sym (lookup-spec h i (h i))) refl))

-- =====================================================================
-- SECTION 1.  A CODED INJECTION E : A ↪ B LIFTS POINTWISE TO THE FINITE
-- SEQUENCES, seqL A ↪ seqL B.
--
--   Over (y ∷ s ∷ []): "there is n with dom s = n, and y is an
--   environment over B on n whose entry at every i ∈ n is the E-image
--   of the entry of s at i".  Binders, outermost first: n, then b
--   pinned to B, then i ∈ n, then u, v.  Inside all of them: v is 0,
--   u is 1, i is 2, b is 3, n is 4, y is 5, s is 6.
-- =====================================================================

module SeqMap (A B E : S)
              (sv : ⟨ (E ∷ A ∷ []) ⊨ svAt zero ⟩)
              (dm : ⟨ (E ∷ A ∷ []) ⊨ domAt zero (suc zero) ⟩)
              (ij : ⟨ (E ∷ A ∷ []) ⊨ injAt zero ⟩)
              (ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst E ⟩
                   → ⟨ fst y ∈ fst B ⟩) where

  module Sm = Small E A B sv dm ij ran using ( at; fib; small; small-inj; module E )

  -- The map on the presentations, with its graph and its injectivity.
  -- Sealed: measured at this site, an unsealed `f (g j)` met by the
  -- unifier (in `cong (λ h → fst (envS B h)) (funExt pt)`) unfolds the
  -- readback's eliminators and exhausts an 8g heap in under 2 min.
  opaque
    f : ⟪ fst A ⟫ → ⟪ fst B ⟫
    f = Sm.small

    f-graph : (m : ⟪ fst A ⟫)
            → ⟨ pr (⟪ fst A ⟫↪ m) (⟪ fst B ⟫↪ (f m)) ∈ fst E ⟩
    f-graph m = subst (λ w → ⟨ pr (⟪ fst A ⟫↪ m) w ∈ fst E ⟩)
      (sym (Sm.fib m .snd)) (Sm.E.toFun-graph (Sm.at m))

    f-inj : (m n : ⟪ fst A ⟫) → f m ≡ f n → m ≡ n
    f-inj = Sm.small-inj

  vA : {n : ℕ} → Ix A n → Fin n → V ℓ
  vA g i = ⟪ fst A ⟫↪ (g i)

  vB : {n : ℕ} → Ix B n → Fin n → V ℓ
  vB h i = ⟪ fst B ⟫↪ (h i)

  fg : {n : ℕ} → Ix A n → Ix B n
  fg g i = f (g i)

  isLA : {n : ℕ} (g : Ix A n) (i : Fin n) → ⟨ isL (vA g i) ⟩
  isLA g i = isL-trans (member (fst A) (g i)) (snd A)

  isLB : {n : ℕ} (h : Ix B n) (i : Fin n) → ⟨ isL (vB h i) ⟩
  isLB h i = isL-trans (member (fst B) (h i)) (snd B)

  -- -------------------------------------------------------------------
  -- 1.1  The graph, and its host reading.
  -- -------------------------------------------------------------------

  Ent : (y s i : S) → Type (ℓ-suc ℓ)
  Ent y s i = ∥ Σ[ u ∈ S ] Σ[ v ∈ S ]
      ( ⟨ pr (fst i) (fst u) ∈ fst s ⟩
      × ⟨ pr (fst i) (fst v) ∈ fst y ⟩
      × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ ) ∥₁

  Wit : (y s : S) → Type (ℓ-suc ℓ)
  Wit y s = ∥ Σ[ n ∈ S ]
      ( ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
      × ⟨ (B ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
      × ((i : S) → ⟨ fst i ∈ fst n ⟩ → Ent y s i) ) ∥₁

  opaque
    private
      entFo : Formula S 5
      entFo = ∃̇ (∃̇ ( appAt i6 i2 i1 ∧̇ appAt i5 i2 i0 ∧̇ appC E i1 i0 ))

    fo : Formula S 2
    fo = ∃̇ ( domAt i2 i0
           ∧̇ ∃̇ ( (var i0 ≐ con B)
                ∧̇ envOverAt i2 i1 i0
                ∧̇ ∀̇∈ (var i1) entFo ) )

    private
      entOut : (y s n b i : S) → ⟨ (i ∷ b ∷ n ∷ y ∷ s ∷ []) ⊨ entFo ⟩ → Ent y s i
      entOut y s n b i = PT.rec squash₁ (λ { (u , hv) →
        PT.rec squash₁ (λ { (v , (h1 , (h2 , h3))) →
          let γ = v ∷ u ∷ i ∷ b ∷ n ∷ y ∷ s ∷ [] in
          ∣ u , v
          , ( subst ⟨_⟩ (appAt-adequate i6 i2 i1 γ) h1
            , subst ⟨_⟩ (appAt-adequate i5 i2 i0 γ) h2
            , subst ⟨_⟩ (appC-adequate E i1 i0 γ) h3 ) ∣₁ }) hv })

      entIn : (y s n i : S) → Ent y s i → ⟨ (i ∷ B ∷ n ∷ y ∷ s ∷ []) ⊨ entFo ⟩
      entIn y s n i = PT.map (λ { (u , v , (h1 , h2 , h3)) →
        let γ = v ∷ u ∷ i ∷ B ∷ n ∷ y ∷ s ∷ [] in
        u , ∣ v , ( subst ⟨_⟩ (sym (appAt-adequate i6 i2 i1 γ)) h1
                  , subst ⟨_⟩ (sym (appAt-adequate i5 i2 i0 γ)) h2
                  , subst ⟨_⟩ (sym (appC-adequate E i1 i0 γ)) h3 ) ∣₁ })

      bodyOut : (y s n b : S)
              → ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
              → fst b ≡ fst B
              → ⟨ (b ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
              → ⟨ (b ∷ n ∷ y ∷ s ∷ []) ⊨ ∀̇∈ (var i1) entFo ⟩
              → Wit y s
      bodyOut y s n b hd eb he hS =
        ∣ n , ( hd
              , envOverAt-transport (b ∷ n ∷ y ∷ s ∷ []) (B ∷ n ∷ y ∷ s ∷ [])
                  i2 i1 i0 i2 i1 i0 refl refl eb he
              , λ i i∈n → entOut y s n b i (hS i i∈n) ) ∣₁

    fo-out : (y s : S) → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩ → Wit y s
    fo-out y s = PT.rec squash₁ (λ { (n , (hd , hb)) →
      PT.rec squash₁ (λ { (b , (eb , (he , hS))) → bodyOut y s n b hd eb he hS }) hb })

    fo-in : (y s : S) → Wit y s → ⟨ (y ∷ s ∷ []) ⊨ fo ⟩
    fo-in y s = PT.rec (snd ((y ∷ s ∷ []) ⊨ fo))
      (λ { (n , (hd , he , hS)) →
        ∣ n , ( hd , ∣ B , ( refl , he , λ i i∈n → entIn y s n i (hS i i∈n) ) ∣₁ ) ∣₁ })

  -- -------------------------------------------------------------------
  -- 1.2  At a sequence s ≡ envS g of length N: the image sequence
  --      satisfies the graph (`wit`), and nothing else does (`only`).
  -- -------------------------------------------------------------------

  module AtSeq (N : ℕ) (g : Ix A N) (s : S) (e : fst s ≡ fst (envS A g)) where

    y₀ : S
    y₀ = envS B (fg g)

    private
      -- The entry of an environment at a natural index.
      at : {k : ℕ} (h : Fin k → V ℓ) (j : Fin k)
         → ⟨ pr (# (toℕ j)) (h j) ∈ env h ⟩
      at h j = subst ⟨_⟩ (sym (lookup-spec h j (h j))) refl

    wit : Wit y₀ s
    wit = ∣ nn N , ( hd , he , step ) ∣₁
      where
      hd : ⟨ (nn N ∷ y₀ ∷ s ∷ []) ⊨ domAt i2 i0 ⟩
      hd = domAt-fill i2 i0 (nn N ∷ y₀ ∷ s ∷ []) N (vA g) (isLA g) e refl

      he : ⟨ (B ∷ nn N ∷ y₀ ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩
      he = envOverAt-transport (B ∷ nn N ∷ y₀ ∷ []) (B ∷ nn N ∷ y₀ ∷ s ∷ [])
             i2 i1 i0 i2 i1 i0 refl refl refl (envOver B (fg g))

      step : (i : S) → ⟨ fst i ∈ # N ⟩ → Ent y₀ s i
      step i i∈N = PT.map atIndex (∈#-elim N (fst i) i∈N)
        where
        atIndex : Σ[ k ∈ ℕ ] ((k < N) × (fst i ≡ # k))
                → Σ[ u ∈ S ] Σ[ v ∈ S ]
                    ( ⟨ pr (fst i) (fst u) ∈ fst s ⟩
                    × ⟨ pr (fst i) (fst v) ∈ fst y₀ ⟩
                    × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ )
        atIndex (k , p , ei) =
            (vA g j , isLA g j) , (vB (fg g) j , isLB (fg g) j)
          , ( subst2 (λ a w → ⟨ pr a (vA g j) ∈ w ⟩) (sym qi) (sym e) (at (vA g) j)
            , subst (λ a → ⟨ pr a (vB (fg g) j) ∈ fst y₀ ⟩) (sym qi) (at (vB (fg g)) j)
            , f-graph (g j) )
          where
          j : Fin N
          j = fromℕ' N k p
          qi : fst i ≡ # (toℕ j)
          qi = ei ∙ cong #_ (sym (toFromId' N k p))

    only : (y : S) → Wit y s → fst y ≡ fst y₀
    only y = PT.rec (setIsSet (fst y) (fst y₀))
      (λ { (n , (hd , he , hS)) → Only.final n hd he hS })
      where
      module Only (n : S)
                  (hd : ⟨ (n ∷ y ∷ s ∷ []) ⊨ domAt i2 i0 ⟩)
                  (he : ⟨ (B ∷ n ∷ y ∷ s ∷ []) ⊨ envOverAt i2 i1 i0 ⟩)
                  (hS : (i : S) → ⟨ fst i ∈ fst n ⟩ → Ent y s i) where

        qn : fst n ≡ # N
        qn = domAt-numeral i2 i0 (n ∷ y ∷ s ∷ []) N (vA g) (isLA g) e hd

        -- The recovered sequence, sealed: a truncation eliminator, never
        -- to meet the unifier.
        opaque
          gR : Ix B N
          gR = Recover.g B N (B ∷ n ∷ y ∷ s ∷ []) i2 i1 i0 qn refl he

          gR-eq : fst y ≡ fst (envS B gR)
          gR-eq = Recover.recovers B N (B ∷ n ∷ y ∷ s ∷ []) i2 i1 i0 qn refl he

        -- The recovered entry at j is the E-image of the entry of s.
        pt : (j : Fin N) → gR j ≡ fg g j
        pt j = ↪-inj {a = fst B} (PT.rec (setIsSet _ _) read (hS (nn (toℕ j)) j∈n))
          where
          j∈n : ⟨ # (toℕ j) ∈ fst n ⟩
          j∈n = subst (λ w → ⟨ # (toℕ j) ∈ w ⟩) (sym qn) (#mono (toℕ j) N (toℕ<n j))

          read : Σ[ u ∈ S ] Σ[ v ∈ S ]
                   ( ⟨ pr (# (toℕ j)) (fst u) ∈ fst s ⟩
                   × ⟨ pr (# (toℕ j)) (fst v) ∈ fst y ⟩
                   × ⟨ pr (fst u) (fst v) ∈ fst E ⟩ )
               → vB gR j ≡ vB (fg g) j
          read (u , v , (hu , hv , hE)) = sym qv ∙ qv'
            where
            qu : fst u ≡ vA g j
            qu = subst ⟨_⟩ (lookup-spec (vA g) j (fst u))
                   (subst (λ w → ⟨ pr (# (toℕ j)) (fst u) ∈ w ⟩) e hu)
            qv : fst v ≡ vB gR j
            qv = subst ⟨_⟩ (lookup-spec (vB gR) j (fst v))
                   (subst (λ w → ⟨ pr (# (toℕ j)) (fst v) ∈ w ⟩) gR-eq hv)
            qv' : fst v ≡ vB (fg g) j
            qv' = svAt-out zero (E ∷ A ∷ []) sv u v (vB (fg g) j , isLB (fg g) j) hE
                    (subst (λ w → ⟨ pr w (vB (fg g) j) ∈ fst E ⟩) (sym qu) (f-graph (g j)))

        final : fst y ≡ fst y₀
        -- A path lambda, not `cong`: measured at this site, `cong` (or
        -- `congS`) at this function sends the unifier through `envS`
        -- and exhausts an 8g heap; the lambda checks in seconds.
        final = gR-eq ∙ λ i → fst (envS B (funExt pt i))

  -- -------------------------------------------------------------------
  -- 1.3  The recursion, the definable map, and the coded injection.
  -- -------------------------------------------------------------------

  Mem : S → Type (ℓ-suc ℓ)
  Mem s = ⟨ fst s ∈ˢ fst (seqL A) ⟩

  Rep : S → Type (ℓ-suc ℓ)
  Rep s = ∥ Σ[ n ∈ ℕ ] Σ[ g ∈ Ix A n ] (fst s ≡ fst (envS A g)) ∥₁

  rep : (s : S) → Mem s → Rep s
  rep s m = PT.rec squash₁
    (λ { (n , hn) → PT.map (λ { (g , e) → n , g , e }) (envSet-out A n s hn) })
    (seqL-out A s m)

  R : Recursion
  R = record
    { dom   = seqL A
    ; graph = fo
    ; funct = λ s m → mereFunct fo s (PT.map (λ { (n , g , e) →
        AtSeq.y₀ n g s e
        , ( fo-in (AtSeq.y₀ n g s e) s (AtSeq.wit n g s e)
          , λ y' h → Σ≡Prop (λ v → snd (isL v)) (AtSeq.only n g s e y' (fo-out y' s h)) ) })
        (rep s m)) }

  module T = Of R using ( funct; val; val-uniq )

  fn : (s : S) → Mem s → S
  fn = T.val

  fn-code : (s : S) (m : Mem s) (n : ℕ) (g : Ix A n) (e : fst s ≡ fst (envS A g))
          → fn s m ≡ AtSeq.y₀ n g s e
  fn-code s m n g e =
    T.val-uniq s m (AtSeq.y₀ n g s e) (fo-in (AtSeq.y₀ n g s e) s (AtSeq.wit n g s e))

  into : (s : S) (m : Mem s) → ⟨ fst (fn s m) ∈ˢ fst (seqL B) ⟩
  into s m = PT.rec (snd (fst (fn s m) ∈ˢ fst (seqL B)))
    (λ { (n , g , e) → subst (λ w → ⟨ fst w ∈ˢ fst (seqL B) ⟩) (sym (fn-code s m n g e))
           (seqL-in B n (envS B (fg g)) (envSet-in B (fg g))) })
    (rep s m)

  D : DefinableMap
  D = record
    { dom = seqL A ; cod = seqL B ; fn = fn ; into = into ; graph = fo
    ; defines = λ s m → T.funct s m .fst .snd
    ; only    = λ s m y h → sym (T.val-uniq s m y h) }

  -- Injectivity: equal image sequences have one length, and then
  -- agree entrywise through the injectivity of the small map.
  private
    same : (n : ℕ) (g : Ix A n) (n' : ℕ) (g' : Ix A n')
         → fst (envS B (fg g)) ≡ fst (envS B (fg g'))
         → fst (envS A g) ≡ fst (envS A g')
    same n g n' g' q =
      subst P (env-len (envS B (fg g)) (vB (fg g)) (vB (fg g')) (isLB (fg g)) (isLB (fg g')) refl q)
        base g' q
      where
      P : ℕ → Type (ℓ-suc ℓ)
      P k = (h : Ix A k) → fst (envS B (fg g)) ≡ fst (envS B (fg h))
          → fst (envS A g) ≡ fst (envS A h)
      base : P n
      base h q' = λ i → fst (envS A (funExt (λ j →
        f-inj (g j) (h j) (↪-inj {a = fst B} (env-pt (vB (fg g)) (vB (fg h)) q' j))) i))

  inj : (s : S) (m : Mem s) (s' : S) (m' : Mem s')
      → fst (fn s m) ≡ fst (fn s' m') → fst s ≡ fst s'
  inj s m s' m' q = PT.rec2 (setIsSet (fst s) (fst s'))
    (λ { (n , g , e) (n' , g' , e') →
        e
      ∙ same n g n' g'
          (sym (cong fst (fn-code s m n g e)) ∙ q ∙ cong fst (fn-code s' m' n' g' e'))
      ∙ sym e' })
    (rep s m) (rep s' m')

  injL : InjL (seqL A) (seqL B)
  injL = Inj.injL D inj

-- THE LIFT.  A coded injection of A into B lifts to the finite sequences.
seq-map : (A B E : S) → InjCode E A B → InjL (seqL A) (seqL B)
seq-map A B E (sv , dm , ij , ran) = SeqMap.injL A B E sv dm ij ran

-- =====================================================================
-- SECTION 2.  THE SUCCESSOR STEP.  At an infinite ordinal β with a
-- coded injection E : L_β ↪ β, the stage L_{β+1} = 𝒟ₒ(L_β) injects into
-- β+1, internally.
--
--   Every member x of L_{β+1} has a least name (src/L/Choice/Step.lagda.md
--   `leastNameOf`): a parameter-free code s at L_ω, an arity a, and a
--   parameter environment e over L_β.  Since β is infinite the code is
--   itself a member of L_β, so x ↦ s :: e is a map into the finite
--   sequences over L_β.  Its graph is the least-name description
--   `LeastNameAt` of src/L/Choice/Internal.lagda.md, with the code
--   order, the stage order, the tower, its code set and the free code
--   set pinned as constants, followed by the cons.  Then seqL L_β ↪
--   seqL β by section 1 and seqL β ↪ β by src/L/GCH/Sequences.lagda.md.
--
--   Binders, outermost first: R, P, B, C, C₀ pinned, then s, a, e.
--   Inside all of them: e is 0, a is 1, s is 2, C₀ is 3, C is 4, B is
--   5, P is 6, R is 7, y is 8, x is 9.
-- =====================================================================

-- A binder pinned to a constant, with its two readings.
pinAt : ∀ {n} → S → Formula S (suc n) → Formula S n
pinAt c φ = ∃̇ ((var zero ≐ con c) ∧̇ φ)

pin-in : ∀ {n} (c : S) (φ : Formula S (suc n)) (γ : S ^ n)
       → ⟨ (c ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ pinAt c φ ⟩
pin-in c φ γ h = ∣ c , (refl , h) ∣₁

pin-out : ∀ {n} (c : S) (φ : Formula S (suc n)) (γ : S ^ n)
        → ⟨ γ ⊨ pinAt c φ ⟩ → ⟨ (c ∷ γ) ⊨ φ ⟩
pin-out c φ γ = PT.rec (snd ((c ∷ γ) ⊨ φ))
  (λ { (z , (ez , h)) → subst (λ v → ⟨ (v ∷ γ) ⊨ φ ⟩) (Σ≡Prop (λ v → snd (isL v)) ez) h })

-- Five pinned binders and three plain binders, read once for a
-- variable body, and sealed.  Measured at this site: the same readings
-- checked at the concrete body of section 2 cost about 10 s per binder.
opaque
  pin5At : ∀ {n} (c₁ c₂ c₃ c₄ c₅ : S)
         → Formula S (suc (suc (suc (suc (suc n))))) → Formula S n
  pin5At c₁ c₂ c₃ c₄ c₅ φ = pinAt c₁ (pinAt c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ))))

  pin5-out : ∀ {n} (c₁ c₂ c₃ c₄ c₅ : S) (φ : Formula S (suc (suc (suc (suc (suc n))))))
             (γ : S ^ n)
           → ⟨ γ ⊨ pin5At c₁ c₂ c₃ c₄ c₅ φ ⟩ → ⟨ (c₅ ∷ c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ) ⊨ φ ⟩
  pin5-out c₁ c₂ c₃ c₄ c₅ φ γ h =
    pin-out c₅ φ (c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ)
      (pin-out c₄ (pinAt c₅ φ) (c₃ ∷ c₂ ∷ c₁ ∷ γ)
        (pin-out c₃ (pinAt c₄ (pinAt c₅ φ)) (c₂ ∷ c₁ ∷ γ)
          (pin-out c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ))) (c₁ ∷ γ)
            (pin-out c₁ (pinAt c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ)))) γ h))))

  pin5-in : ∀ {n} (c₁ c₂ c₃ c₄ c₅ : S) (φ : Formula S (suc (suc (suc (suc (suc n))))))
            (γ : S ^ n)
          → ⟨ (c₅ ∷ c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ pin5At c₁ c₂ c₃ c₄ c₅ φ ⟩
  pin5-in c₁ c₂ c₃ c₄ c₅ φ γ h =
    pin-in c₁ (pinAt c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ)))) γ
      (pin-in c₂ (pinAt c₃ (pinAt c₄ (pinAt c₅ φ))) (c₁ ∷ γ)
        (pin-in c₃ (pinAt c₄ (pinAt c₅ φ)) (c₂ ∷ c₁ ∷ γ)
          (pin-in c₄ (pinAt c₅ φ) (c₃ ∷ c₂ ∷ c₁ ∷ γ)
            (pin-in c₅ φ (c₄ ∷ c₃ ∷ c₂ ∷ c₁ ∷ γ) h))))

  ∃₃ : ∀ {n} → Formula S (suc (suc (suc n))) → Formula S n
  ∃₃ φ = ∃̇ (∃̇ (∃̇ φ))

  -- Read by named functions with stated types, one per binder: the
  -- nested pattern-lambda form of this reading did not finish in 120 s.
  ∃₃-out : ∀ {n} (φ : Formula S (suc (suc (suc n)))) (γ : S ^ n)
         → ⟨ γ ⊨ ∃₃ φ ⟩
         → ∥ Σ[ s ∈ S ] Σ[ a ∈ S ] Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁
  ∃₃-out {n} φ γ = PT.rec squash₁ at₁
    where
    Out : Type (ℓ-suc ℓ)
    Out = ∥ Σ[ s ∈ S ] Σ[ a ∈ S ] Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁

    at₃ : (s a : S) → Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ → Out
    at₃ s a (e , h) = ∣ s , a , e , h ∣₁

    at₂ : (s : S) → Σ[ a ∈ S ] ∥ Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁ → Out
    at₂ s (a , h) = PT.rec squash₁ (at₃ s a) h

    at₁ : Σ[ s ∈ S ] ∥ Σ[ a ∈ S ] ∥ Σ[ e ∈ S ] ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ ∥₁ ∥₁ → Out
    at₁ (s , h) = PT.rec squash₁ (at₂ s) h

  ∃₃-in : ∀ {n} (φ : Formula S (suc (suc (suc n)))) (γ : S ^ n)
        → (s a e : S) → ⟨ (e ∷ a ∷ s ∷ γ) ⊨ φ ⟩ → ⟨ γ ⊨ ∃₃ φ ⟩
  ∃₃-in φ γ s a e h = ∣ s , ∣ a , ∣ e , h ∣₁ ∣₁ ∣₁

-- A name is determined by its code and its parameters.  Proved once, at
-- variable formulas and vectors, by J: at the reflexive length no
-- transport remains.  Measured at this site: the same assembly written
-- at the concrete names of section 2 did not finish in 150 s.
NameOf : Type ℓ → Type ℓ
NameOf X = Σ[ k ∈ ℕ ] (Formula (⊥* {ℓ}) (suc k) × Vec X k)

name-ext : {X : Type ℓ} {k k' : ℕ} (e : k ≡ k')
           (χ : Formula (⊥* {ℓ}) (suc k)) (χ' : Formula (⊥* {ℓ}) (suc k'))
           (p : Vec X k) (p' : Vec X k')
         → fst (limitCode χ) ≡ fst (limitCode χ')
         → ((i : Fin k) (j : Fin k') → toℕ i ≡ toℕ j → lookup i p ≡ lookup j p')
         → _≡_ {A = NameOf X} (k , χ , p) (k' , χ' , p')
name-ext {X} {k} = J Motive base
  where
  Motive : (k' : ℕ) → k ≡ k' → Type (ℓ-suc ℓ)
  Motive k' e = (χ : Formula (⊥* {ℓ}) (suc k)) (χ' : Formula (⊥* {ℓ}) (suc k'))
                (p : Vec X k) (p' : Vec X k')
              → fst (limitCode χ) ≡ fst (limitCode χ')
              → ((i : Fin k) (j : Fin k') → toℕ i ≡ toℕ j → lookup i p ≡ lookup j p')
              → _≡_ {A = NameOf X} (k , χ , p) (k' , χ' , p')
  ext : {m : ℕ} (p p' : Vec X m) → ((i : Fin m) → lookup i p ≡ lookup i p') → p ≡ p'
  ext []      []       h = refl
  ext (x ∷ p) (y ∷ p') h = cong₂ _∷_ (h zero) (ext p p' (λ i → h (suc i)))
  base : Motive k refl
  base χ χ' p p' q h = λ i → k , code-inj χ χ' q i , ext p p' (λ m → h m m refl) i

module Succ (βL : S) (oβ : IsOrd (fst βL)) (β∉ω : ⟨ fst βL ∈ˢ ω ⟩ → Empty.⊥)
            (E : S) (code : InjCode E (LsetS (fst βL) oβ) βL) where

  private
    β : V ℓ
    β = fst βL

  -- The tower, its code set, and the free code set, sealed where they
  -- are built: each reaches a slot inside a satisfaction.
  opaque
    tw : S
    tw = LsetS β oβ

    tw-eq : tw ≡ LsetS β oβ
    tw-eq = refl

    cs : S
    cs = AllCodes (LsetS β oβ)

    cs-eq : fst cs ≡ fst (AllCodes (LsetS β oβ))
    cs-eq = refl

    c0 : S
    c0 = AllCodes ∅ʟ

    c0-eq : fst c0 ≡ fst (AllCodes ∅ʟ)
    c0-eq = refl

  -- The stage order on L_β, as an element of L, and the naming frame.
  w : SWO ⟪ Lset β ⟫
  w = carry (Lset β) (orderAt β oβ)

  Ps : S
  Ps = relL β (snd βL) oβ

  module NM = Naming (Lset β) w using ( Name; arity; codeOf; denote; formula; nameOrder; params )
  module A6 = At (Lset β) (snd (LsetS β oβ)) w using ( module Least; codeEl; codeEl-fst; envEl; envEl-fst; numAt; numAt-fst )
  module L6 = A6.Least codeOrder Ps codeOrder-rep codeOrder-fill
                (ixRel-rep β oβ Ps (relL-spec β (snd βL) oβ))
                (ixRel-fill β oβ Ps (relL-spec β (snd βL) oβ))
    using ( module Min )

  open NM using ( Name; arity; formula; params; codeOf; denote )

  pfam : (t : Name) → Fin (arity t) → V ℓ
  pfam t i = ⟪ Lset β ⟫↪ (lookup i (params t))

  -- L_ω sits inside L_β, because β is infinite.
  opaque
    Lω⊆Lβ : (z : V ℓ) → ⟨ z ∈ Lset ω ⟩ → ⟨ z ∈ Lset β ⟩
    Lω⊆Lβ z = go (ord-tri ω ω-ord β oβ)
      where
      go : Tri ω β → ⟨ z ∈ Lset ω ⟩ → ⟨ z ∈ Lset β ⟩
      go (inl ω∈β)       = λ h → Lset-mono {α = β} {β = ω} ω∈β h
      go (inr (inl e))   = subst (λ v → ⟨ z ∈ Lset v ⟩) e
      go (inr (inr β∈ω)) = Empty.rec (β∉ω β∈ω)

  -- The code of a name, as a member of the tower.  Sealed: a fiber,
  -- never to meet the unifier (as section 1 measured for `f`).
  opaque
    codeM : (t : Name) → ⟪ Lset β ⟫
    codeM t = fiber (Lset β) (Lω⊆Lβ (fst (codeOf t)) (snd (codeOf t))) .fst

    codeM-eq : (t : Name) → ⟪ Lset β ⟫↪ (codeM t) ≡ fst (codeOf t)
    codeM-eq t = fiber (Lset β) (Lω⊆Lβ (fst (codeOf t)) (snd (codeOf t))) .snd

  -- The value: the code consed onto the parameters, an environment over
  -- L_β of length arity + 1.
  val : Name → V ℓ
  val t = env (cons (fst (codeOf t)) (pfam t))

  valS : Name → S
  valS t = envS (LsetS β oβ) (cons (codeM t) (λ i → lookup i (params t)))

  valS-fst : (t : Name) → fst (valS t) ≡ val t
  valS-fst t = λ i → env (funExt pt i)
    where
    pt : (i : Fin (suc (arity t)))
       → ⟪ Lset β ⟫↪ (cons (codeM t) (λ j → lookup j (params t)) i)
       ≡ cons (fst (codeOf t)) (pfam t) i
    pt zero    = codeM-eq t
    pt (suc i) = refl

  -- -------------------------------------------------------------------
  -- 2.1  The graph, and its host reading.
  -- -------------------------------------------------------------------

  γ₇ : (y x : S) → S ^ 7
  γ₇ y x = c0 ∷ cs ∷ tw ∷ Ps ∷ codeOrder ∷ y ∷ x ∷ []

  Γ : (y x s a e : S) → S ^ 10
  Γ y x s a e = e ∷ a ∷ s ∷ γ₇ y x

  -- The least-name formula at slots, sealed, and its two readings at a
  -- variable environment.  The concrete instance below is only ever
  -- compared under the seal.  Measured at this site: the same two
  -- readings stated at the concrete environment cost 7.5 s each, and
  -- the graph readings through a transparent body 9 s each.
  module LNAt {n : ℕ} (R P B C C₀ s a e d : Fin n) where
    opaque
      Fo : Formula S n
      Fo = LeastNameAt R P B C C₀ s a e d

    module Rd (γ : S ^ n)
              (qR : fst (lookup R γ) ≡ fst codeOrder)
              (qP : fst (lookup P γ) ≡ fst Ps)
              (qB : lookup B γ ≡ LsetS β oβ)
              (qC : fst (lookup C γ) ≡ fst (AllCodes (LsetS β oβ)))
              (q₀ : fst (lookup C₀ γ) ≡ fst (AllCodes ∅ʟ)) where
      open L6.Min R P B C C₀ s a e d γ qR qP qB qC q₀ public

      opaque
        unfolding Fo

        fill : (t : Name) → Least t → ⟨ γ ⊨ Fo ⟩
        fill = LeastAt-fill

        read : ⟨ γ ⊨ Fo ⟩ → ∥ Σ[ t ∈ Name ] Least t ∥₁
        read = LeastAt-read

  module LF = LNAt {10} i7 i6 i5 i4 i3 i2 i1 i0 i9 using ( Fo; module Rd )
  module Min (y x s a e : S) = LF.Rd (Γ y x s a e) refl refl tw-eq cs-eq c0-eq

  LN : (y x s a e : S) → Type (ℓ-suc ℓ)
  LN y x s a e = ⟨ Γ y x s a e ⊨ LF.Fo ⟩

  ln-fill : (y x s a e : S) (t : Name) → Min.Least y x s a e t → LN y x s a e
  ln-fill = Min.fill

  ln-read : (y x s a e : S) → LN y x s a e → ∥ Σ[ t ∈ Name ] Min.Least y x s a e t ∥₁
  ln-read = Min.read

  -- The cons formula, sealed the same way.
  opaque
    cnFo : Formula S 10
    cnFo = consAtL i8 i2 i0

    cn-fill : (y x s a e : S) {k : ℕ} (g : Fin k → V ℓ) → fst e ≡ env g
            → fst y ≡ env (cons (fst s) g) → ⟨ Γ y x s a e ⊨ cnFo ⟩
    cn-fill y x s a e g qe q =
      subst ⟨_⟩ (sym (consAtL-adequate i8 i2 i0 (Γ y x s a e) g qe)) q

    cn-read : (y x s a e : S) {k : ℕ} (g : Fin k → V ℓ) → fst e ≡ env g
            → ⟨ Γ y x s a e ⊨ cnFo ⟩ → fst y ≡ env (cons (fst s) g)
    cn-read y x s a e g qe h =
      subst ⟨_⟩ (consAtL-adequate i8 i2 i0 (Γ y x s a e) g qe) h

  CN : (y x s a e : S) → Type (ℓ-suc ℓ)
  CN y x s a e = ⟨ Γ y x s a e ⊨ cnFo ⟩

  Wit : (y x : S) → Type (ℓ-suc ℓ)
  Wit y x = ∥ Σ[ s ∈ S ] Σ[ a ∈ S ] Σ[ e ∈ S ] (LN y x s a e × CN y x s a e) ∥₁

  opaque
    body : Formula S 10
    body = LF.Fo ∧̇ cnFo

    fo : Formula S 2
    fo = pin5At codeOrder Ps tw cs c0 (∃₃ body)

    fo-out : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩ → Wit y x
    fo-out y x h =
      ∃₃-out body (γ₇ y x) (pin5-out codeOrder Ps tw cs c0 (∃₃ body) (y ∷ x ∷ []) h)

    fo-in : (y x : S) → Wit y x → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩
    fo-in y x = PT.rec (snd ((y ∷ x ∷ []) ⊨ fo))
      (λ { (s , a , e , hb) → pin5-in codeOrder Ps tw cs c0 (∃₃ body) (y ∷ x ∷ [])
             (∃₃-in body (γ₇ y x) s a e hb) })

  -- -------------------------------------------------------------------
  -- 2.2  At a member x of L_{β+1} with least name t: the value satisfies
  --      the graph, and nothing else does.
  -- -------------------------------------------------------------------

  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ Lset (sucV β) ⟩

  -- The least name, sealed: a well-founded selection, never to meet
  -- the unifier.  Being a least name is sealed too, at a variable
  -- name, so that the selected name is only ever compared under the
  -- seal.  Measured at this site: compared under the transparent
  -- predicate, the name order unfolds to its level search, 17 s.
  opaque
    leastP : (x : S) → Mem x → Σ[ t ∈ Name ] IsLeastName β w t (fst x)
    leastP x m = leastNameOf β w (fst x , m)

  opaque
    IsLN : Name → S → Type (ℓ-suc ℓ)
    IsLN t x = IsLeastName β w t (fst x)

    isLN-in : (t : Name) (x : S) → IsLeastName β w t (fst x) → IsLN t x
    isLN-in t x h = h

    isLN-out : (t : Name) (x : S) → IsLN t x → IsLeastName β w t (fst x)
    isLN-out t x h = h

  opaque
    least : (x : S) → Mem x → Name
    least x m = leastP x m .fst

    least-isLN : (x : S) (m : Mem x) → IsLN (least x m) x
    least-isLN x m = isLN-in (leastP x m .fst) x (leastP x m .snd)

  least-is : (x : S) (m : Mem x) → IsLeastName β w (least x m) (fst x)
  least-is x m = isLN-out (least x m) x (least-isLN x m)

  fn : (x : S) → Mem x → S
  fn x m = valS (least x m)

  wit : (x : S) (t : Name) → IsLeastName β w t (fst x) → Wit (valS t) x
  wit x t hl = ∣ A6.codeEl t , A6.numAt (arity t) , A6.envEl t
    , ( ln-fill (valS t) x (A6.codeEl t) (A6.numAt (arity t)) (A6.envEl t) t
          ( (A6.codeEl-fst t , A6.numAt-fst (arity t) , A6.envEl-fst t , sym (hl .fst))
          , λ t' q h' → hl .snd t' (sym q) h' )
      , cn-fill (valS t) x (A6.codeEl t) (A6.numAt (arity t)) (A6.envEl t)
          (pfam t) (A6.envEl-fst t)
          (valS-fst t ∙ cong (λ c → env (cons c (pfam t))) (sym (A6.codeEl-fst t))) ) ∣₁

  only : (x : S) (t : Name) → IsLeastName β w t (fst x)
       → (y : S) → Wit y x → fst y ≡ fst (valS t)
  only x t hl y = PT.rec (setIsSet (fst y) (fst (valS t)))
    (λ { (s , a , e , (hl , hc)) → PT.rec (setIsSet (fst y) (fst (valS t)))
      (λ { (t' , ((qs , qa , qe , qd) , mt)) → Read.final s a e hc t' qs qe qd mt })
      (ln-read y x s a e hl) })
    where
    module Read (s a e : S) (hc : CN y x s a e) (t' : Name)
                (qs : fst s ≡ fst (codeOf t'))
                (qe : fst e ≡ env (pfam t'))
                (qd : fst x ≡ denote t')
                (mt : Min.IsMin y x s a e t') where
      hl' : IsLeastName β w t' (fst x)
      hl' = sym qd , λ t'' q h → mt t'' (sym q) h

      t'≡t : t' ≡ t
      t'≡t = cong fst (isPropLeastOf NM.nameOrder (denotesAt β w (fst x)) (t' , hl') (t , hl))

      final : fst y ≡ fst (valS t)
      final = cn-read y x s a e (pfam t') qe hc
            ∙ (λ i → env (cons (qs i) (pfam t')))
            ∙ (λ i → val (t'≡t i))
            ∙ sym (valS-fst t)

  -- -------------------------------------------------------------------
  -- 2.3  A name is determined by its code and its parameters: equal
  --      values have one arity, one formula and one parameter vector.
  -- -------------------------------------------------------------------

  private
    isLpar : (t : Name) (i : Fin (suc (arity t)))
           → ⟨ isL (cons (fst (codeOf t)) (pfam t) i) ⟩
    isLpar t zero    = isL-trans (snd (codeOf t)) (isL-Lset ω ω-ord)
    isLpar t (suc i) = isL-trans (member (Lset β) (lookup i (params t))) (isL-Lset β oβ)

    -- The entry of an environment at its own index.
    at : {k : ℕ} (h : Fin k → V ℓ) (j : Fin k) → ⟨ pr (# (toℕ j)) (h j) ∈ env h ⟩
    at h j = subst ⟨_⟩ (sym (lookup-spec h j (h j))) refl

  val-inj : (t t' : Name) → val t ≡ val t' → t ≡ t'
  val-inj t t' q = name-ext e (formula t) (formula t') (params t) (params t') qc pt
    where
    e : arity t ≡ arity t'
    e = injSuc (env-len (valS t) (cons (fst (codeOf t)) (pfam t))
                 (cons (fst (codeOf t')) (pfam t')) (isLpar t) (isLpar t')
                 (valS-fst t) (valS-fst t ∙ q))

    qc : fst (codeOf t) ≡ fst (codeOf t')
    qc = subst ⟨_⟩ (lookup-spec (cons (fst (codeOf t')) (pfam t')) zero (fst (codeOf t)))
           (subst (λ v → ⟨ pr (# zero) (fst (codeOf t)) ∈ v ⟩) q
             (at (cons (fst (codeOf t)) (pfam t)) zero))

    -- Entry i of the first parameter vector is entry j of the second
    -- whenever the indices agree, read through the environments.
    pt : (i : Fin (arity t)) (j : Fin (arity t')) → toℕ i ≡ toℕ j
       → lookup i (params t) ≡ lookup j (params t')
    pt i j eij = ↪-inj {a = Lset β}
      (subst ⟨_⟩ (lookup-spec (cons (fst (codeOf t')) (pfam t')) (suc j) (pfam t i))
        (subst2 (λ k v → ⟨ pr (# (suc k)) (pfam t i) ∈ v ⟩) eij q
          (at (cons (fst (codeOf t)) (pfam t)) (suc i))))


  -- 2.4  The definable map, the coded injection, and the step.
  -- -------------------------------------------------------------------

  into : (x : S) (m : Mem x) → ⟨ fst (fn x m) ∈ˢ fst (seqL (LsetS β oβ)) ⟩
  into x m = seqL-in (LsetS β oβ) (suc (arity t)) (valS t)
    (envSet-in (LsetS β oβ) (cons (codeM t) (λ i → lookup i (params t))))
    where
    t : Name
    t = least x m

  D : DefinableMap
  D = record
    { dom = LsetS (sucV β) (suc-ord oβ) ; cod = seqL (LsetS β oβ)
    ; fn = fn ; into = into ; graph = fo
    ; defines = λ x m → fo-in (fn x m) x (wit x (least x m) (least-is x m))
    ; only    = λ x m y h → Σ≡Prop (λ v → snd (isL v))
                  (only x (least x m) (least-is x m) y (fo-out y x h)) }

  inj : (x : S) (m : Mem x) (x' : S) (m' : Mem x')
      → fst (fn x m) ≡ fst (fn x' m') → fst x ≡ fst x'
  inj x m x' m' q =
      sym (least-is x m .fst)
    ∙ (λ i → denote (val-inj (least x m) (least x' m')
        (sym (valS-fst (least x m)) ∙ q ∙ valS-fst (least x' m')) i))
    ∙ least-is x' m' .fst

  names : InjL (LsetS (sucV β) (suc-ord oβ)) (seqL (LsetS β oβ))
  names = Inj.injL D inj

  -- THE STEP.  L_{β+1} ↪ seqL L_β ↪ seqL β ↪ β ⊆ β+1.
  result : InjL (LsetS (sucV β) (suc-ord oβ)) (ordL (sucV β) (suc-ord oβ))
  result = injl-trans (LsetS (sucV β) (suc-ord oβ)) (seqL (LsetS β oβ)) (ordL (sucV β) (suc-ord oβ))
    names
    (injl-trans (seqL (LsetS β oβ)) (seqL βL) (ordL (sucV β) (suc-ord oβ))
      (seq-map (LsetS β oβ) βL E code)
      (injl-trans (seqL βL) βL (ordL (sucV β) (suc-ord oβ))
        (seq-count βL oβ β∉ω)
        (inclusion-coded βL (ordL (sucV β) (suc-ord oβ))
          (λ z z∈β → suc-ord oβ .fst z∈β (self∈sucV β)))))

succ-step : (βL : S) (oβ : IsOrd (fst βL)) → (⟨ fst βL ∈ˢ ω ⟩ → Empty.⊥)
          → InjL (LsetS (fst βL) oβ) βL
          → InjL (LsetS (sucV (fst βL)) (suc-ord oβ)) (ordL (sucV (fst βL)) (suc-ord oβ))
succ-step βL oβ β∉ω = PT.rec squash₁
  (λ { (E , code) → Succ.result βL oβ β∉ω E code })

-- =====================================================================
-- SECTION 3.  THE TABLE OF LEAST INJECTIONS.  At an ordinal δ such that
-- every stage L_β, β ∈ δ, merely injects into δ internally, the family
-- β ↦ e_β of the stage-order-least such injection codes is one set of
-- L: the graph of a definable map on δ.
--
--   A stage γ is chosen that holds one code for every β ∈ δ: the least
--   stage holding one is a function of β (src/L/Stage.lagda.md
--   `leastOrd`), and γ bounds those.  The selection of e_β, its graph
--   and its table are `L.GCH.Least` at γ, δ and the code predicate of
--   `CodeFo`: over (e ∷ b ∷ []), "there is B, the tower at b, with e
--   coding an injection of B into δ".  Inside B: B is 0, e is 1, b is 2.
-- =====================================================================

-- An injection code is a proposition, and it respects the index
-- equations of its graph and its domain.
isPropInjCode : (F a b : S) → isProp (InjCode F a b)
isPropInjCode F a b =
  isProp× (snd ((F ∷ a ∷ []) ⊨ svAt zero))
    (isProp× (snd ((F ∷ a ∷ []) ⊨ domAt zero (suc zero)))
      (isProp× (snd ((F ∷ a ∷ []) ⊨ injAt zero))
        (isPropΠ3 (λ _ y _ → snd (fst y ∈ fst b)))))

injcode-resp : (F F' a a' b : S) → fst F ≡ fst F' → fst a ≡ fst a'
             → InjCode F a b → InjCode F' a' b
injcode-resp F F' a a' b qF qa (sv , dm , ij , ran) =
    svAt-in zero γ' (λ x y y' p q → svAt-out zero γ sv x y y' (mv p) (mv q))
  , domAt-intro zero (suc zero) γ' (λ x →
        (λ h → subst (λ w → ⟨ fst x ∈ w ⟩) qa
                 (PT.rec (snd (fst x ∈ fst a))
                   (λ { (y , p) → domAt-out zero (suc zero) γ dm x y (mv p) }) h))
      , (λ hx → PT.map (λ { (y , p) → y , mv' p })
                 (domAt-in zero (suc zero) γ dm x
                   (subst (λ w → ⟨ fst x ∈ w ⟩) (sym qa) hx))))
  , injAt-in zero γ' (λ y x x' p q → injAt-out zero γ ij y x x' (mv p) (mv q))
  , λ x y p → ran x y (mv p)
  where
  γ γ' : S ^ 2
  γ  = F ∷ a ∷ []
  γ' = F' ∷ a' ∷ []
  mv : {u v : V ℓ} → ⟨ pr u v ∈ fst F' ⟩ → ⟨ pr u v ∈ fst F ⟩
  mv {u} {v} = subst (λ w → ⟨ pr u v ∈ w ⟩) (sym qF)
  mv' : {u v : V ℓ} → ⟨ pr u v ∈ fst F ⟩ → ⟨ pr u v ∈ fst F' ⟩
  mv' {u} {v} = subst (λ w → ⟨ pr u v ∈ w ⟩) qF

-- The injection-code formula at two slots, against the constant b:
-- single-valued, with domain B, injective, with values in b.
injFo : ∀ {n} → S → Fin n → Fin n → Formula S n
injFo b f B = svAt f ∧̇ domAt f B ∧̇ injAt f
            ∧̇ ∀̇ (∀̇ (appAt (suc (suc f)) i1 i0 ⇒̇ (var i0 ∈̇ con b)))

module InjFo {n : ℕ} (b : S) (f B : Fin n) (γ : S ^ n) where
  private
    F A : S
    F = lookup f γ
    A = lookup B γ

  read : ⟨ γ ⊨ injFo b f B ⟩ → InjCode F A b
  read (sv , dm , ij , ran) =
      svAt-in zero (F ∷ A ∷ []) (λ x y y' p q → svAt-out f γ sv x y y' p q)
    , domAt-intro zero (suc zero) (F ∷ A ∷ []) (λ x →
          (λ h → PT.rec (snd (fst x ∈ fst A))
                   (λ { (y , p) → domAt-out f B γ dm x y p }) h)
        , (λ hx → domAt-in f B γ dm x hx))
    , injAt-in zero (F ∷ A ∷ []) (λ y x x' p q → injAt-out f γ ij y x x' p q)
    , λ x y p → ran x y (subst ⟨_⟩ (sym (appAt-adequate (suc (suc f)) i1 i0 (y ∷ x ∷ γ))) p)

  fill : InjCode F A b → ⟨ γ ⊨ injFo b f B ⟩
  fill (sv , dm , ij , ran) =
      svAt-in f γ (λ x y y' p q → svAt-out zero (F ∷ A ∷ []) sv x y y' p q)
    , domAt-intro f B γ (λ x →
          (λ h → PT.rec (snd (fst x ∈ fst A))
                   (λ { (y , p) → domAt-out zero (suc zero) (F ∷ A ∷ []) dm x y p }) h)
        , (λ hx → domAt-in zero (suc zero) (F ∷ A ∷ []) dm x hx))
    , injAt-in f γ (λ y x x' p q → injAt-out zero (F ∷ A ∷ []) ij y x x' p q)
    , λ x y p → ran x y (subst ⟨_⟩ (appAt-adequate (suc (suc f)) i1 i0 (y ∷ x ∷ γ)) p)


-- The code predicate at slots, sealed, with its two readings at a
-- variable environment: "there is B, the tower at b, with e coding an
-- injection of B into δ".  Inside B: B is 0 and the slots shift by one.
-- Measured at this site: the two readings written at the concrete
-- environment cost 7 s each.
module CodeFo {n : ℕ} (δL : S) (e b : Fin n) where
  opaque
    Fo : Formula S n
    Fo = ∃̇ (LsetGraphAt i0 (suc b) ∧̇ injFo δL (suc e) i0)

    read : (γ : S ^ n) (ev bv : S) → lookup e γ ≡ ev → lookup b γ ≡ bv
         → (ob : IsOrd (fst bv)) → ⟨ γ ⊨ Fo ⟩ → InjCode ev (LsetS (fst bv) ob) δL
    read γ ev bv qe qb ob = PT.rec (isPropInjCode ev (LsetS (fst bv) ob) δL) at
      where
      at : Σ[ B ∈ S ] ( ⟨ (B ∷ γ) ⊨ LsetGraphAt i0 (suc b) ⟩
                      × ⟨ (B ∷ γ) ⊨ injFo δL (suc e) i0 ⟩ )
         → InjCode ev (LsetS (fst bv) ob) δL
      at (B , hg , hi) = injcode-resp (lookup e γ) ev B (LsetS (fst bv) ob) δL (cong fst qe)
        ( Lset-only i0 (suc b) (B ∷ γ) hg (subst (λ v → IsOrd (fst v)) (sym qb) ob)
        ∙ cong (λ v → Lset (fst v)) qb )
        (InjFo.read δL (suc e) i0 (B ∷ γ) hi)

    fill : (γ : S ^ n) (ev bv : S) → lookup e γ ≡ ev → lookup b γ ≡ bv
         → (ob : IsOrd (fst bv)) → InjCode ev (LsetS (fst bv) ob) δL → ⟨ γ ⊨ Fo ⟩
    fill γ ev bv qe qb ob code =
      ∣ LsetS (fst bv) ob
      , Lset-defines i0 (suc b) (LsetS (fst bv) ob ∷ γ) (subst (λ v → IsOrd (fst v)) (sym qb) ob)
          (cong (λ v → Lset (fst v)) (sym qb))
      , InjFo.fill δL (suc e) i0 (LsetS (fst bv) ob ∷ γ)
          (injcode-resp ev (lookup e γ) (LsetS (fst bv) ob) (LsetS (fst bv) ob) δL
            (cong fst (sym qe)) refl code) ∣₁

module Table (δL : S) (oδ : IsOrd (fst δL))
             (have : (β : V ℓ) (oβ : IsOrd β) → ⟨ β ∈ fst δL ⟩ → InjL (LsetS β oβ) δL)
             where

  private
    δ : V ℓ
    δ = fst δL

  -- -------------------------------------------------------------------
  -- 3.1  The bounding stage γ.
  -- -------------------------------------------------------------------

  -- Some code at the stage σ.
  HasCode : (β : V ℓ) (oβ : IsOrd β) → V ℓ → hProp (ℓ-suc ℓ)
  HasCode β oβ σ =
    ∥ Σ[ F ∈ S ] (⟨ fst F ∈ Lset σ ⟩ × InjCode F (LsetS β oβ) δL) ∥₁ , squash₁

  -- An index with its ordinal-hood and its membership in δ.
  Ix3 : Type (ℓ-suc ℓ)
  Ix3 = Σ[ b ∈ V ℓ ] (IsOrd b × ⟨ b ∈ δ ⟩)

  -- The least stage holding a code, a function of the index.  Sealed:
  -- a well-founded selection, never to meet the unifier.
  opaque
    ls : (p : Ix3) → LeastOrd (HasCode (fst p) (fst (snd p)))
    ls (β , oβ , β∈δ) = PT.rec (isPropLeastOrd (HasCode β oβ)) from (have β oβ β∈δ)
      where
      from : Σ[ F ∈ S ] InjCode F (LsetS β oβ) δL → LeastOrd (HasCode β oβ)
      from (F , code) = leastOrd (HasCode β oβ)
        ∣ stage (fst F) (snd F) , stage-ord (fst F) (snd F)
        , ∣ F , stage-mem (fst F) (snd F) , code ∣₁ ∣₁

  private
    at : ⟪ δ ⟫ → Ix3
    at m = ⟪ δ ⟫↪ m , mem-ord {A = δ} oδ (⟪ δ ⟫↪ m) (member δ m) , member δ m

  -- The bound, sealed with its three readings.
  opaque
    γ : V ℓ
    γ = boundingOrd ⟪ δ ⟫ (λ m → ls (at m) .fst) (λ m → ls (at m) .snd .fst) .fst

    oγ : IsOrd γ
    oγ = boundingOrd ⟪ δ ⟫ (λ m → ls (at m) .fst) (λ m → ls (at m) .snd .fst) .snd .fst

    bnd-in : (m : ⟪ δ ⟫) → ⟨ ls (at m) .fst ∈ γ ⟩
    bnd-in = boundingOrd ⟪ δ ⟫ (λ m → ls (at m) .fst) (λ m → ls (at m) .snd .fst) .snd .snd

  -- Every β ∈ δ has a code in L_γ: its least stage sits below γ.
  code-at-γ : (β : V ℓ) (oβ : IsOrd β) (β∈δ : ⟨ β ∈ δ ⟩) → ⟨ HasCode β oβ γ ⟩
  code-at-γ β oβ β∈δ = PT.map raise (ls p .snd .snd .fst)
    where
    p : Ix3
    p = β , oβ , β∈δ
    m : ⟪ δ ⟫
    m = fiber δ β∈δ .fst
    -- The two indices are equal, so their least stages are.
    pth : at m ≡ p
    pth = Σ≡Prop (λ b → isProp× (isPropIsOrd b) (snd (b ∈ δ))) (fiber δ β∈δ .snd)
    σ∈γ : ⟨ ls p .fst ∈ γ ⟩
    σ∈γ = subst (λ w → ⟨ w ∈ γ ⟩) (λ i → ls (pth i) .fst) (bnd-in m)
    raise : Σ[ F ∈ S ] (⟨ fst F ∈ Lset (ls p .fst) ⟩ × InjCode F (LsetS β oβ) δL)
          → Σ[ F ∈ S ] (⟨ fst F ∈ Lset γ ⟩ × InjCode F (LsetS β oβ) δL)
    raise (F , h , code) = F , Lset-mono {α = γ} {β = ls p .fst} σ∈γ h , code

  -- -------------------------------------------------------------------
  -- 3.2  The least code at each index, and its table: `L.GCH.Least` at
  -- γ, δ and the code predicate.
  -- -------------------------------------------------------------------

  ordAt : (b : S) → ⟨ fst b ∈ δ ⟩ → IsOrd (fst b)
  ordAt b m = mem-ord {A = δ} oδ (fst b) m

  private
    module CF = CodeFo {2} δL i0 i1 using ( Fo; fill; read )

    have-γ : (b : S) (m : ⟨ fst b ∈ δ ⟩)
           → ∥ Σ[ e ∈ S ] (⟨ fst e ∈ Lset γ ⟩ × ⟨ (e ∷ b ∷ []) ⊨ CF.Fo ⟩) ∥₁
    have-γ b m = PT.map
      (λ { (F , h , code) → F , h , CF.fill (F ∷ b ∷ []) F b refl refl (ordAt b m) code })
      (code-at-γ (fst b) (ordAt b m) m)

    module Ls = Least γ oγ δL CF.Fo have-γ using ( fn; fn-holds; T; T-in; T-out )

  eS : (b : S) → ⟨ fst b ∈ δ ⟩ → S
  eS = Ls.fn

  e-code : (b : S) (m : ⟨ fst b ∈ δ ⟩) → InjCode (eS b m) (LsetS (fst b) (ordAt b m)) δL
  e-code b m = CF.read (eS b m ∷ b ∷ []) (eS b m) b refl refl (ordAt b m) (Ls.fn-holds b m)

  -- THE TABLE: the set of pairs (b, e_b), b ∈ δ.
  T : S
  T = Ls.T

  T-in : (b : S) (m : ⟨ fst b ∈ δ ⟩) → ⟨ pr (fst b) (fst (eS b m)) ∈ fst T ⟩
  T-in = Ls.T-in

  T-out : (b e : S) → ⟨ pr (fst b) (fst e) ∈ fst T ⟩
        → Σ[ m ∈ ⟨ fst b ∈ δ ⟩ ] (fst e ≡ fst (eS b m))
  T-out = Ls.T-out

-- =====================================================================
-- SECTION 4.  THE LIMIT STEP.  At a limit ordinal δ (closed under the
-- successor) such that every stage L_β, β ∈ δ, merely injects into δ
-- internally, L_δ injects into δ.
--
--   x ∈ L_δ is born at some stage: b_x = birth x + 1 is the least
--   ordinal with x ∈ L_{b_x}, and b_x ∈ δ because δ is a limit.  With
--   the table T of section 3, x ↦ (b_x, e_{b_x}(x)) lands in prodL δ,
--   and prodL δ ↪ δ by the pairing at δ.
--
--   The graph, over (y ∷ x ∷ []): "there is b ∈ δ and e with (b, e) ∈ T
--   and some v with (x, v) ∈ e and y = (b, v), and for every b' ∈ b and
--   e' with (b', e') ∈ T no v' has (x, v') ∈ e'".  Binders: b, e, then
--   v; the leastness clause binds b', e', then v'.  Inside b, e: e is
--   0, b is 1, y is 2, x is 3; v adds one; in the leastness clause e'
--   is 0, b' is 1, e is 2, b is 3, y is 4, x is 5, and v' adds one.
-- =====================================================================

module Lim (δL : S) (oδ : IsOrd (fst δL)) (δ∉ω : ⟨ fst δL ∈ˢ ω ⟩ → Empty.⊥)
           (lim : (β : V ℓ) → ⟨ β ∈ fst δL ⟩ → ⟨ sucV β ∈ fst δL ⟩)
           (have : (β : V ℓ) (oβ : IsOrd β) → ⟨ β ∈ fst δL ⟩ → InjL (LsetS β oβ) δL)
           where

  private
    δ : V ℓ
    δ = fst δL

  module Tb = Table δL oδ have using ( T; T-in; T-out; e-code; eS; ordAt )
  open Tb using ( T; T-in; T-out; eS; e-code; ordAt )

  -- -------------------------------------------------------------------
  -- 4.1  The value at x: its birth successor, and the entry there.
  -- -------------------------------------------------------------------

  Mem : S → Type (ℓ-suc ℓ)
  Mem x = ⟨ fst x ∈ Lset δ ⟩

  module AtX (x : S) (m : Mem x) where

    b : V ℓ
    b = sucV (birth (fst x) (snd x))

    ob : IsOrd b
    ob = suc-ord (birth-ord (fst x) (snd x))

    b∈δ : ⟨ b ∈ δ ⟩
    b∈δ = lim (birth (fst x) (snd x)) (birth-in δ oδ (fst x) (snd x) m)

    bS : S
    bS = ordL b ob

    e : S
    e = eS bS b∈δ

    x∈Lb : ⟨ fst x ∈ Lset b ⟩
    x∈Lb = birth-mem (fst x) (snd x)

    code : InjCode e (LsetS b (ordAt bS b∈δ)) δL
    code = e-code bS b∈δ

    -- The entry, sealed with its graph: a readback, never to meet the
    -- unifier.
    opaque
      v : S
      v = Extract.toFun e (LsetS b (ordAt bS b∈δ)) (fst code) (fst (snd code)) (x , x∈Lb)

      v-graph : ⟨ pr (fst x) (fst v) ∈ fst e ⟩
      v-graph = Extract.toFun-graph e (LsetS b (ordAt bS b∈δ)) (fst code) (fst (snd code)) (x , x∈Lb)

    v∈δ : ⟨ fst v ∈ δ ⟩
    v∈δ = snd (snd (snd code)) x v v-graph

    y₀ : S
    y₀ = prʟ bS v

    -- No stage below b holds x.
    not-below : (b' : V ℓ) → IsOrd b' → ⟨ b' ∈ b ⟩ → ⟨ fst x ∈ Lset b' ⟩ → Empty.⊥
    not-below b' ob' b'∈b hx = stage-earliest (fst x) (snd x) b' ob' hx
      (subst (λ w → ⟨ b' ∈ w ⟩) (birth-suc (fst x) (snd x)) b'∈b)

  fn : (x : S) → Mem x → S
  fn x m = AtX.y₀ x m

  -- An entry (x, v') of a table value at b' puts x in L_{b'}.
  entry-stage : (b' e' : S) → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
              → (x v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩
              → Σ[ m' ∈ ⟨ fst b' ∈ δ ⟩ ] ⟨ fst x ∈ Lset (fst b') ⟩
  entry-stage b' e' ht x v' hv = m' , domAt-out zero (suc zero)
      (eS b' m' ∷ LsetS (fst b') (ordAt b' m') ∷ []) (fst (snd (e-code b' m'))) x v'
      (subst (λ w → ⟨ pr (fst x) (fst v') ∈ w ⟩) (T-out b' e' ht .snd) hv)
    where
    m' = T-out b' e' ht .fst

  -- -------------------------------------------------------------------
  -- 4.2  The graph, and its host reading.
  -- -------------------------------------------------------------------

  LWit : (y x : S) → Type (ℓ-suc ℓ)
  LWit y x = ∥ Σ[ b ∈ S ] Σ[ e ∈ S ] Σ[ v ∈ S ]
      ( ⟨ fst b ∈ δ ⟩
      × ⟨ pr (fst b) (fst e) ∈ fst T ⟩
      × ⟨ pr (fst x) (fst v) ∈ fst e ⟩
      × (fst y ≡ pr (fst b) (fst v))
      × ((b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
          → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥) ) ∥₁

  opaque
    private
      leastFo : Formula S 4
      leastFo = ∀̇∈ (var i1) (∀̇ (appC T i1 i0 ⇒̇ ¬̇ (∃̇ (appAt i1 i6 i0))))

      valFo : Formula S 4
      valFo = ∃̇ (appAt i1 i4 i0 ∧̇ prAtL i3 i2 i0)

      body : Formula S 4
      body = appC T i1 i0 ∧̇ valFo ∧̇ leastFo

    fo : Formula S 2
    fo = ∃̇∈ (con δL) (∃̇ body)

    private
      leastOut : (y x b e : S) → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ leastFo ⟩
               → (b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
               → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥
      leastOut y x b e hl b' e' hb ht v' hv =
        hl b' hb e' (subst ⟨_⟩ (sym (appC-adequate T i1 i0 (e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ []))) ht)
          ∣ v' , subst ⟨_⟩ (sym (appAt-adequate i1 i6 i0 (v' ∷ e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ []))) hv ∣₁

      leastIn : (y x b e : S)
              → ((b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
                  → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥)
              → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ leastFo ⟩
      leastIn y x b e mn b' hb e' ht = PT.rec Empty.isProp⊥
        (λ { (v' , hv) → mn b' e' hb
              (subst ⟨_⟩ (appC-adequate T i1 i0 (e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ [])) ht) v'
              (subst ⟨_⟩ (appAt-adequate i1 i6 i0 (v' ∷ e' ∷ b' ∷ e ∷ b ∷ y ∷ x ∷ [])) hv) })

      valOut : (y x b e : S) → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ valFo ⟩
             → ∥ Σ[ v ∈ S ] (⟨ pr (fst x) (fst v) ∈ fst e ⟩ × (fst y ≡ pr (fst b) (fst v))) ∥₁
      valOut y x b e = PT.map (λ { (v , (hv , hy)) →
        v , ( subst ⟨_⟩ (appAt-adequate i1 i4 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ [])) hv
            , subst ⟨_⟩ (prAtL-adequate i3 i2 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ [])) hy ) })

      valIn : (y x b e v : S) → ⟨ pr (fst x) (fst v) ∈ fst e ⟩ → fst y ≡ pr (fst b) (fst v)
            → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ valFo ⟩
      valIn y x b e v hv hy =
        ∣ v , ( subst ⟨_⟩ (sym (appAt-adequate i1 i4 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ []))) hv
              , subst ⟨_⟩ (sym (prAtL-adequate i3 i2 i0 (v ∷ e ∷ b ∷ y ∷ x ∷ []))) hy ) ∣₁

      bodyOut : (y x b e : S) → ⟨ fst b ∈ δ ⟩ → ⟨ (e ∷ b ∷ y ∷ x ∷ []) ⊨ body ⟩ → LWit y x
      bodyOut y x b e hb (ht , hv , hl) = PT.map
        (λ { (v , (hv' , hy)) →
          b , e , v
          , ( hb
            , subst ⟨_⟩ (appC-adequate T i1 i0 (e ∷ b ∷ y ∷ x ∷ [])) ht
            , hv' , hy
            , leastOut y x b e hl ) })
        (valOut y x b e hv)

    fo-out : (y x : S) → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩ → LWit y x
    fo-out y x = PT.rec squash₁ (λ { (b , (hb , h)) →
      PT.rec squash₁ (λ { (e , hbody) → bodyOut y x b e hb hbody }) h })

    fo-in : (y x : S) → LWit y x → ⟨ (y ∷ x ∷ []) ⊨ fo ⟩
    fo-in y x = PT.rec (snd ((y ∷ x ∷ []) ⊨ fo))
      (λ { (b , e , v , (hb , ht , hv , hy , mn)) →
        ∣ b , ( hb
              , ∣ e , ( subst ⟨_⟩ (sym (appC-adequate T i1 i0 (e ∷ b ∷ y ∷ x ∷ []))) ht
                      , valIn y x b e v hv hy
                      , leastIn y x b e mn ) ∣₁ ) ∣₁ })

  -- -------------------------------------------------------------------
  -- 4.3  The value satisfies the graph, and nothing else does.
  -- -------------------------------------------------------------------

  wit : (x : S) (m : Mem x) → LWit (fn x m) x
  wit x m = ∣ X.bS , X.e , X.v
    , ( X.b∈δ , T-in X.bS X.b∈δ , X.v-graph , prʟ-fst X.bS X.v , mn ) ∣₁
    where
    module X = AtX x m using ( b; bS; b∈δ; code; e; not-below; ob; v; v-graph; v∈δ )
    mn : (b' e' : S) → ⟨ fst b' ∈ X.b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
       → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥
    mn b' e' hb ht v' hv = X.not-below (fst b') (ordAt b' (fst es)) hb (snd es)
      where
      es = entry-stage b' e' ht x v' hv

  only : (x : S) (m : Mem x) (y : S) → LWit y x → fst y ≡ fst (fn x m)
  only x m y = PT.rec (setIsSet (fst y) (fst (fn x m)))
    (λ { (b , e , v , (hb , ht , hv , hy , mn)) → Read.final b e v hb ht hv hy mn })
    where
    module X = AtX x m using ( b; bS; b∈δ; code; e; not-below; ob; v; v-graph; v∈δ )
    module Read (b e v : S) (hb : ⟨ fst b ∈ δ ⟩)
                (ht : ⟨ pr (fst b) (fst e) ∈ fst T ⟩)
                (hv : ⟨ pr (fst x) (fst v) ∈ fst e ⟩)
                (hy : fst y ≡ pr (fst b) (fst v))
                (mn : (b' e' : S) → ⟨ fst b' ∈ fst b ⟩ → ⟨ pr (fst b') (fst e') ∈ fst T ⟩
                    → (v' : S) → ⟨ pr (fst x) (fst v') ∈ fst e' ⟩ → Empty.⊥) where

      x∈Lb : ⟨ fst x ∈ Lset (fst b) ⟩
      x∈Lb = snd (entry-stage b e ht x v hv)

      -- b is the birth successor: below it no stage holds x, and above
      -- it the birth successor itself violates the leastness clause.
      qb : fst b ≡ X.b
      qb = go (ord-tri (fst b) (ordAt b hb) X.b X.ob)
        where
        go : Tri (fst b) X.b → fst b ≡ X.b
        go (inl b∈)       = Empty.rec (X.not-below (fst b) (ordAt b hb) b∈ x∈Lb)
        go (inr (inl q))  = q
        go (inr (inr b∋)) = Empty.rec (mn X.bS X.e b∋ (T-in X.bS X.b∈δ) X.v X.v-graph)

      -- The table value at b is the value at the birth successor.
      pth : _≡_ {A = Σ[ c ∈ S ] ⟨ fst c ∈ δ ⟩} (b , T-out b e ht .fst) (X.bS , X.b∈δ)
      pth = Σ≡Prop (λ c → snd (fst c ∈ δ)) (Σ≡Prop (λ w → snd (isL w)) qb)

      qe : fst e ≡ fst X.e
      qe = T-out b e ht .snd ∙ (λ i → fst (eS (fst (pth i)) (snd (pth i))))

      qv : fst v ≡ fst X.v
      qv = svAt-out zero (X.e ∷ LsetS X.b (ordAt X.bS X.b∈δ) ∷ []) (fst X.code) x v X.v
             (subst (λ w → ⟨ pr (fst x) (fst v) ∈ w ⟩) qe hv) X.v-graph

      final : fst y ≡ fst (fn x m)
      final = hy ∙ (λ i → pr (qb i) (qv i)) ∙ sym (prʟ-fst X.bS X.v)

  -- -------------------------------------------------------------------
  -- 4.4  The definable map, injective, hence coded; then the pairing.
  -- -------------------------------------------------------------------

  into : (x : S) (m : Mem x) → ⟨ fst (fn x m) ∈ˢ fst (prodL δL) ⟩
  into x m = subst (λ w → ⟨ w ∈ˢ fst (prodL δL) ⟩) (sym (prʟ-fst X.bS X.v))
    (prodL-in δL X.bS X.v X.b∈δ X.v∈δ)
    where module X = AtX x m

  D : DefinableMap
  D = record
    { dom = LsetS δ oδ ; cod = prodL δL ; fn = fn ; into = into ; graph = fo
    ; defines = λ x m → fo-in (fn x m) x (wit x m)
    ; only    = λ x m y h → Σ≡Prop (λ w → snd (isL w)) (only x m y (fo-out y x h)) }

  inj : (x : S) (m : Mem x) (x' : S) (m' : Mem x')
      → fst (fn x m) ≡ fst (fn x' m') → fst x ≡ fst x'
  inj x m x' m' q =
    injAt-out zero (X.e ∷ LsetS X.b (ordAt X.bS X.b∈δ) ∷ []) (fst (snd (snd X.code)))
      X.v x x' X.v-graph
      (subst2 (λ w u → ⟨ pr (fst x') w ∈ u ⟩) (sym qv) qe X'.v-graph)
    where
    module X  = AtX x m using ( b; bS; b∈δ; code; e; not-below; ob; v; v-graph; v∈δ )
    module X' = AtX x' m'
    pq : (fst X.bS ≡ fst X'.bS) × (fst X.v ≡ fst X'.v)
    pq = pr-inj (sym (prʟ-fst X.bS X.v) ∙ q ∙ prʟ-fst X'.bS X'.v)
    qv : fst X.v ≡ fst X'.v
    qv = snd pq
    -- The table value at the same index is the same value.
    to : Σ[ k ∈ ⟨ fst X.bS ∈ δ ⟩ ] (fst X'.e ≡ fst (eS X.bS k))
    to = T-out X.bS X'.e (subst (λ w → ⟨ pr w (fst X'.e) ∈ fst T ⟩) (sym (fst pq))
                           (T-in X'.bS X'.b∈δ))
    qe : fst X'.e ≡ fst X.e
    qe = to .snd ∙ (λ i → fst (eS X.bS (snd (fst X.bS ∈ δ) (to .fst) X.b∈δ i)))

  injL : InjL (LsetS δ oδ) (prodL δL)
  injL = Inj.injL D inj

  -- The pairing at δ, as src/L/GCH/Sequences.lagda.md builds it.
  pairing : InjL (prodL δL) δL
  pairing = PT.rec squash₁ build (cardOf δL oδ)
    where
    build : Σ[ μ ∈ S ]
              ( IsOrd (fst μ) × IsCardinalL μ
              × ((z : V ℓ) → ⟨ z ∈ˢ fst μ ⟩ → ⟨ z ∈ˢ fst δL ⟩)
              × InjL δL μ × InjL μ δL )
          → InjL (prodL δL) δL
    build (μ , oμ , cardμ , _ , δ↪μ , μ↪δ) =
      injl-trans (prodL δL) (prodL μ) δL (prod-inj δL μ δ↪μ)
        (injl-trans (prodL μ) μ δL
          (WF.WFI.induction regularityV {P = Goal} Step.result (fst μ) (snd μ) oμ cardμ μ∉ω)
          μ↪δ)
      where
      μ∉ω : ⟨ fst μ ∈ˢ ω ⟩ → Empty.⊥
      μ∉ω h = no-fin δL μ oδ δ∉ω oμ h δ↪μ

  result : InjL (LsetS δ oδ) δL
  result = injl-trans (LsetS δ oδ) (prodL δL) δL injL pairing

-- =====================================================================
-- SECTION 5.  THE THEOREM, BY ∈-INDUCTION, FROM THE BASE L_ω ↪ ω.
--
--   At an infinite ordinal δ: if δ = β+1 then β is infinite and the
--   successor step applies to the hypothesis at β; otherwise δ is a
--   limit, every β ∈ δ has L_β ↪ δ (through the hypothesis at an
--   infinite β, through L_ω ↪ ω at a finite one), and the limit step
--   applies.  The base at ω is the one row this chapter takes as its
--   hypothesis: the code set of the names sits in L_ω and in no finite
--   stage, so the successor map of section 2 has no target below ω.
-- =====================================================================

Lω : S
Lω = LsetS ω ω-ord

LimitStageCounted : Type (ℓ-suc ℓ)
LimitStageCounted = InjL Lω ωʟ

-- An internal injection moves along equal carriers, by inclusions.
move : (a a' b b' : S) → fst a ≡ fst a' → fst b ≡ fst b' → InjL a b → InjL a' b'
move a a' b b' qa qb h =
  injl-trans a' a b' (inclusion-coded a' a (λ z hz → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym qa) hz))
    (injl-trans a b b' h (inclusion-coded b b' (λ z hz → subst (λ w → ⟨ z ∈ˢ w ⟩) qb hz)))

module Induction (base : LimitStageCounted) where

  P : V ℓ → Type (ℓ-suc ℓ)
  P δ = (oδ : IsOrd δ) → (⟨ δ ∈ ω ⟩ → Empty.⊥) → InjL (LsetS δ oδ) (ordL δ oδ)

  isPropP : (δ : V ℓ) → isProp (P δ)
  isPropP δ = isPropΠ2 (λ _ _ → squash₁)

  module Ind (δ : V ℓ) (ih : (β : V ℓ) → ⟨ β ∈ δ ⟩ → P β)
              (oδ : IsOrd δ) (δ∉ω : ⟨ δ ∈ ω ⟩ → Empty.⊥) where

    δL : S
    δL = ordL δ oδ

    -- Every stage below δ injects into δ.
    have : (β : V ℓ) (oβ : IsOrd β) → ⟨ β ∈ δ ⟩ → InjL (LsetS β oβ) δL
    have β oβ β∈δ = go (lem (β ∈ ω))
      where
      go : ⟨ β ∈ ω ⟩ ⊎ (⟨ β ∈ ω ⟩ → Empty.⊥) → InjL (LsetS β oβ) δL
      go (inl β∈ω) =
        injl-trans (LsetS β oβ) Lω δL
          (inclusion-coded (LsetS β oβ) Lω (λ z hz → Lset-mono {α = ω} {β = β} β∈ω hz))
          (injl-trans Lω ωʟ δL base
            (inclusion-coded ωʟ δL (λ z hz → ω⊆ δ oδ δ∉ω z hz)))
      go (inr β∉ω) =
        injl-trans (LsetS β oβ) (ordL β oβ) δL (ih β β∈δ oβ β∉ω)
          (inclusion-coded (ordL β oβ) δL (λ z hz → oδ .fst hz β∈δ))

    IsSuc : hProp (ℓ-suc ℓ)
    IsSuc = ∥ Σ[ β ∈ V ℓ ] (IsOrd β × (sucV β ≡ δ)) ∥₁ , squash₁

    atSuc : Σ[ β ∈ V ℓ ] (IsOrd β × (sucV β ≡ δ)) → InjL (LsetS δ oδ) δL
    atSuc (β , oβ , q) =
      move (LsetS (sucV β) (suc-ord oβ)) (LsetS δ oδ) (ordL (sucV β) (suc-ord oβ)) δL
        (cong Lset q) q
        (succ-step (ordL β oβ) oβ β∉ω (ih β β∈δ oβ β∉ω))
      where
      β∈δ : ⟨ β ∈ δ ⟩
      β∈δ = subst (λ w → ⟨ β ∈ w ⟩) q (self∈sucV β)
      β∉ω : ⟨ β ∈ ω ⟩ → Empty.⊥
      β∉ω h = δ∉ω (subst (λ w → ⟨ w ∈ ω ⟩) q (ω-limit β h))

    atLim : (IsSuc .fst → Empty.⊥) → InjL (LsetS δ oδ) δL
    atLim ¬suc = Lim.result δL oδ δ∉ω lim have
      where
      lim : (β : V ℓ) → ⟨ β ∈ δ ⟩ → ⟨ sucV β ∈ δ ⟩
      lim β β∈δ = go (suc∈or≡ β δ oβ oδ β∈δ)
        where
        oβ : IsOrd β
        oβ = mem-ord {A = δ} oδ β β∈δ
        go : ⟨ sucV β ∈ δ ⟩ ⊎ (sucV β ≡ δ) → ⟨ sucV β ∈ δ ⟩
        go (inl h) = h
        go (inr q) = Empty.rec (¬suc ∣ β , oβ , q ∣₁)

    result : InjL (LsetS δ oδ) δL
    result = go (lem IsSuc)
      where
      go : IsSuc .fst ⊎ (IsSuc .fst → Empty.⊥) → InjL (LsetS δ oδ) δL
      go (inl h)  = PT.rec squash₁ atSuc h
      go (inr ¬h) = atLim ¬h

  counted : (δ : V ℓ) → P δ
  counted = WF.WFI.induction regularityV {P = P} Ind.result

-- THE THEOREM, from the base.
stage-counted-from : LimitStageCounted → StageCountedCoded
stage-counted-from base δ Lδ oδ δ∉ω q =
  move (LsetS (fst δ) oδ) Lδ (ordL (fst δ) oδ) δ (sym q) refl
    (Induction.counted base (fst δ) oδ δ∉ω)

-- =====================================================================
-- SECTION 6.  THE BASE OF THE COUNT: THE LIMIT STAGE L_ω IS COUNTABLE,
-- INTERNALLY.  The stage order at ω is a set of L (`relL ω`); its
-- collapse (src/L/GCH/OrderType.lagda.md) is an ordinal every value of
-- which is finite, because the segment below a member sits in one
-- finite stage and omega does not inject into a finite stage.
-- =====================================================================

-- =====================================================================
-- 6.1  A FINITE STAGE HOLDS NO COPY OF omega.
--
--   src/L/Choice/Finite.lagda.md tallies the finite stage L_n: a finite
--   list of members covering it.  At every member the least tally index
--   is a natural number below the tally's size, so an injection of omega
--   into L_n composes to one into the numeral `# size`, which
--   `finite-excl-ω` refutes.  The index is chosen by `leastOf` over the
--   natural order; minimality is never used, any deterministic index
--   would do.
-- =====================================================================

private
  module FinNo (n : ℕ) where
    t : Tally (finiteStage n)
    t = StageOrder.tally (stageOrder n)

    open Tally t using ( size; item; onto )

    -- The tally indices naming x, as natural numbers.
    Named : V ℓ → ℕ → hProp (ℓ-suc ℓ)
    Named x k = ∥ Σ[ i ∈ Fin size ] ((toℕ i ≡ k) × (item i ≡ x)) ∥₁ , squash₁

    least : (x : V ℓ) → ⟨ x ∈ˢ finiteStage n ⟩ → Σ[ k ∈ ℕ ] ⟨ Named x k ⟩
    least x hx = fst l , fst (snd l)
      where
      l = leastOf natOrder lem (Named x)
            (PT.map (λ { (i , q) → toℕ i , ∣ i , refl , q ∣₁ }) (onto x hx))

    noinj : (f : ⟪ ω ⟫ → ⟪ Lset (# n) ⟫)
          → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥
    noinj f finj = finite-excl-ω (# size) (numeral-ord size) (#∈ω size)
      (λ x → q x , q x) (λ x y e → finj x y (qq x y (cong fst e)))
      where
      vl : ⟪ ω ⟫ → V ℓ
      vl x = ⟪ Lset (# n) ⟫↪ (f x)
      mm : (x : ⟪ ω ⟫) → ⟨ vl x ∈ˢ finiteStage n ⟩
      mm x = member (Lset (# n)) (f x)
      k : ⟪ ω ⟫ → ℕ
      k x = least (vl x) (mm x) .fst
      kb : (x : ⟪ ω ⟫) → k x < size
      kb x = PT.rec isProp≤
        (λ { (i , (pi , _)) → subst (λ w → w < size) pi (toℕ<n i) })
        (least (vl x) (mm x) .snd)
      q : ⟪ ω ⟫ → ⟪ # size ⟫
      q x = fiber (# size) (#mono (k x) size (kb x)) .fst
      q-spec : (x : ⟪ ω ⟫) → ⟪ # size ⟫↪ (q x) ≡ # (k x)
      q-spec x = fiber (# size) (#mono (k x) size (kb x)) .snd
      qq : (x y : ⟪ ω ⟫) → q x ≡ q y → f x ≡ f y
      qq x y e = ↪-inj {a = Lset (# n)}
        (PT.rec2 (setIsSet (vl x) (vl y)) go (least (vl x) (mm x) .snd) (least (vl y) (mm y) .snd))
        where
        ek : k x ≡ k y
        ek = #-inj′ (sym (q-spec x) ∙ cong ⟪ # size ⟫↪ e ∙ q-spec y)
        go : Σ[ i ∈ Fin size ] ((toℕ i ≡ k x) × (item i ≡ vl x))
           → Σ[ j ∈ Fin size ] ((toℕ j ≡ k y) × (item j ≡ vl y))
           → vl x ≡ vl y
        go (i , pi , qi) (j , pj , qj) = sym qi ∙ cong item (inj-toℕ (pi ∙ ek ∙ sym pj)) ∙ qj

  NoInto : V ℓ → Type ℓ
  NoInto w = (f : ⟪ ω ⟫ → ⟪ Lset w ⟫)
           → ((x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y) → Empty.⊥

  no-inj-fin : (g : V ℓ) → ⟨ g ∈ˢ ω ⟩ → NoInto g
  no-inj-fin g g∈ω = PT.rec (isPropΠ2 (λ _ _ → Empty.isProp⊥))
    (λ { (k , e) → subst NoInto e (FinNo.noinj (lower k)) }) g∈ω

-- =====================================================================
-- 6.2  L_ω, THE ORDER ON IT AS A SET OF L, AND ITS DOMAIN READING.
--
--   `relL ω` is the stage order at omega, realized as an element of L
--   (src/L/Choice/Order.lagda.md).  `Related` says what its members
--   are: pairs of two members of the stage.  That is the domain
--   hypothesis `OrderType.Code` asks for.
-- =====================================================================

hω : ⟨ isL ω ⟩
hω = isL-ord ω ω-ord

Rω : SL.S
Rω = relL ω hω ω-ord

specω : IsRel ω Rω
specω = relL-spec ω hω ω-ord

Rsub : (y x : SL.S) → Holds Rω y x
     → ⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩
Rsub y x h = PT.rec isP
  (λ { (_ , h₁) → PT.rec isP
    (λ { (a , h₂) → PT.rec isP
      (λ { (b , (q , _)) →
             subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .fst)) (a .snd)
           , subst (λ w → ⟨ w ∈ˢ Lset ω ⟩) (sym (pr-inj q .snd)) (b .snd) })
      h₂ })
    h₁ })
  rel
  where
  isP : isProp (⟨ fst y ∈ˢ Lset ω ⟩ × ⟨ fst x ∈ˢ Lset ω ⟩)
  isP = isProp× (snd (fst y ∈ˢ Lset ω)) (snd (fst x ∈ˢ Lset ω))
  rel : ⟨ Related ω (pr (fst y) (fst x)) ⟩
  rel = subst (λ w → ⟨ Related ω w ⟩) (prʟ-fst y x)
    (specω (prʟ y x) .fst
      (subst (λ w → ⟨ w ∈ˢ fst Rω ⟩) (sym (prʟ-fst y x)) h))

module OT = Code Lω Rω Rsub using ( module Conjuncts; Dom; _≺_; isProp≺; ≺-in; ≺-out )

-- The host order at the same presentation, and the two directions
-- between it and the sealed relation of the collapse.
Wω : SWO ⟪ Lset ω ⟫
Wω = carry (Lset ω) (orderAt ω ω-ord)

open SWO Wω using () renaming ( _<∙_ to _<ω_ )

≺→< : (a b : OT.Dom) → a OT.≺ b → a <ω b
≺→< a b k = ixRel-rep ω ω-ord Rω specω a b (OT.≺-out a b k)

<→≺ : (a b : OT.Dom) → a <ω b → a OT.≺ b
<→≺ a b k = OT.≺-in a b (ixRel-fill ω ω-ord Rω specω a b k)

wfω : WellFounded OT._≺_
wfω m = go (SWO.wf∙ Wω m)
  where
  go : {n : OT.Dom} → Acc _<ω_ n → Acc OT._≺_ n
  go {n} (acc r) = acc (λ n' k → go (r n' (≺→< n' n k)))

transω : {a b c : OT.Dom} → a OT.≺ b → b OT.≺ c → a OT.≺ c
transω {a} {b} {c} k k' =
  <→≺ a c (SWO.trans∙ Wω a b c (≺→< a b k) (≺→< b c k'))

triω : (a b : OT.Dom) → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
triω a b = go (SWO.tri∙ Wω a b)
  where
  go : TriW (a <ω b) (a ≡ b) (b <ω a)
     → (a OT.≺ b) ⊎ ((a ≡ b) ⊎ (b OT.≺ a))
  go (lt h) = inl (<→≺ a b h)
  go (eq e) = inr (inl e)
  go (gt h) = inr (inr (<→≺ b a h))

module C = OT.Conjuncts wfω transω using ( module Inj; col; col-ord; col-out; colTable; otL; otL-out )
module I = C.Inj triω using ( code; col-inj )
-- =====================================================================
-- 6.3  THE SEGMENT BELOW A MEMBER SITS IN ONE FINITE STAGE.
--
--   The stage order compares the BIRTH first (src/L/Choice/Step.lagda.md,
--   `Family._≺_`), so a predecessor of x is born at or below the birth
--   of x, hence belongs to the stage one above that birth.  At omega
--   that stage is finite.
-- =====================================================================

private
  module F = Family ω (λ δ _ → orderAt δ) ω-ord using ( _≺_; bornAt )

  unfoldω : (a b : MemOf (Lset ω))
          → relOf (orderAt ω ω-ord) a b ≡ F._≺_ a b
  unfoldω a b = cong (λ z → relOf (z ω-ord) a b) (orderAt-step ω)

  bAt : MemOf (Lset ω) → V ℓ
  bAt a = F.bornAt a .fst

  bAt∈ω : (a : MemOf (Lset ω)) → ⟨ bAt a ∈ˢ ω ⟩
  bAt∈ω a = F.bornAt a .snd

  bAt-ord : (a : MemOf (Lset ω)) → IsOrd (bAt a)
  bAt-ord a = mem-ord {A = ω} ω-ord (bAt a) (bAt∈ω a)

  self-at : (a : MemOf (Lset ω)) → ⟨ a .fst ∈ˢ Lset (sucV (bAt a)) ⟩
  self-at a = birth-mem (a .fst) (Lset→isL ω ω-ord (a .fst) (a .snd))

  step-bound : (a b : MemOf (Lset ω)) → F._≺_ a b
             → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
  step-bound a b (inl h) =
    raise (suc∈or≡ (bAt a) (bAt b) (bAt-ord a) (bAt-ord b) h)
    where
    raise : ⟨ sucV (bAt a) ∈ˢ bAt b ⟩ ⊎ (sucV (bAt a) ≡ bAt b)
          → ⟨ a .fst ∈ˢ Lset (sucV (bAt b)) ⟩
    raise (inl k) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
      (∈sucV-inl {A = bAt b} {x = sucV (bAt a)} k) (self-at a)
    raise (inr e) = Lset-mono {α = sucV (bAt b)} {β = sucV (bAt a)}
      (subst (λ w → ⟨ sucV (bAt a) ∈ˢ sucV w ⟩) e (self∈sucV (sucV (bAt a))))
      (self-at a)
  step-bound a b (inr (e , u)) =
    subst (λ w → ⟨ a .fst ∈ˢ Lset (sucV w) ⟩) (sym e) (u .fst)

  atIx : OT.Dom → MemOf (Lset ω)
  atIx m = ⟪ Lset ω ⟫↪ m , memOf (Lset ω) m

  gOf : OT.Dom → V ℓ
  gOf p = sucV (bAt (atIx p))

  gOf∈ω : (p : OT.Dom) → ⟨ gOf p ∈ˢ ω ⟩
  gOf∈ω p = ω-limit (bAt (atIx p)) (bAt∈ω (atIx p))

  seg-bound : (p r : OT.Dom) → r OT.≺ p
            → ⟨ ⟪ Lset ω ⟫↪ r ∈ˢ Lset (gOf p) ⟩
  seg-bound p r k =
    step-bound (atIx r) (atIx p) (transport (unfoldω (atIx r) (atIx p)) (≺→< r p k))
-- =====================================================================
-- 6.4  THE ORDER TYPE IS INCLUDED IN omega.
--
--   The collapse value at p is the order type of the segment below p.
--   That segment injects, ambiently, into the finite stage of section 3,
--   so omega does not inject into it; and an ordinal that omega does not
--   reach is a member of omega.  This is the shape of `Step.col-fin`
--   (src/L/GCH/Pairing.lagda.md:979).
-- =====================================================================

private
  Seg : OT.Dom → V ℓ → Type (ℓ-suc ℓ)
  Seg p b = Σ[ r ∈ OT.Dom ] ((r OT.≺ p) × (C.col r ≡ b))

  isPropSeg : (p : OT.Dom) (b : V ℓ) → isProp (Seg p b)
  isPropSeg p b (r , _ , e) (r' , _ , e') =
    Σ≡Prop (λ z → isProp× (OT.isProp≺ z p) (setIsSet _ _))
      (I.col-inj r r' (e ∙ sym e'))

  seg : (p : OT.Dom) (b : V ℓ) → ⟨ b ∈ˢ C.col p ⟩ → Seg p b
  seg p b h = PT.rec (isPropSeg p b) (λ z → z) (C.col-out p b h)

col-fin : (p : OT.Dom) → ⟨ C.col p ∈ˢ ω ⟩
col-fin p = go (ord-tri (C.col p) (C.col-ord p) ω ω-ord)
  where
  refute : ((z : V ℓ) → ⟨ z ∈ˢ ω ⟩ → ⟨ z ∈ˢ C.col p ⟩) → Empty.⊥
  refute sub = no-inj-fin (gOf p) (gOf∈ω p) f f-inj
    where
    s : (x : ⟪ ω ⟫) → Seg p (⟪ ω ⟫↪ x)
    s x = seg p (⟪ ω ⟫↪ x) (sub (⟪ ω ⟫↪ x) (member ω x))
    fb : (x : ⟪ ω ⟫)
       → Σ[ m ∈ ⟪ Lset (gOf p) ⟫ ] (⟪ Lset (gOf p) ⟫↪ m ≡ ⟪ Lset ω ⟫↪ (s x .fst))
    fb x = fiber (Lset (gOf p)) (seg-bound p (s x .fst) (s x .snd .fst))
    f : ⟪ ω ⟫ → ⟪ Lset (gOf p) ⟫
    f x = fb x .fst
    f-inj : (x y : ⟪ ω ⟫) → f x ≡ f y → x ≡ y
    f-inj x y e = ↪-inj {a = ω}
      (sym (s x .snd .snd) ∙ cong C.col rr ∙ s y .snd .snd)
      where
      rr : s x .fst ≡ s y .fst
      rr = ↪-inj {a = Lset ω}
        (sym (fb x .snd) ∙ cong ⟪ Lset (gOf p) ⟫↪ e ∙ fb y .snd)

  go : ⟨ C.col p ∈ˢ ω ⟩ ⊎ ((C.col p ≡ ω) ⊎ ⟨ ω ∈ˢ C.col p ⟩) → ⟨ C.col p ∈ˢ ω ⟩
  go (inl k) = k
  go (inr (inl e)) =
    Empty.rec (refute (λ z z∈ω → subst (λ w → ⟨ z ∈ˢ w ⟩) (sym e) z∈ω))
  go (inr (inr ω∈c)) =
    Empty.rec (refute (λ z z∈ω → C.col-ord p .fst z∈ω ω∈c))

otL⊆ω : (z : V ℓ) → ⟨ z ∈ˢ fst C.otL ⟩ → ⟨ z ∈ˢ ω ⟩
otL⊆ω z h = PT.rec (snd (z ∈ˢ ω))
  (λ { (b , e) → subst (λ w → ⟨ w ∈ˢ ω ⟩) e (col-fin b) })
  (C.otL-out z h)
-- 6.5  THE TWO THEOREMS: the premise of section 5, and the trophy's
-- first line.

limit-stage-counted : LimitStageCounted
limit-stage-counted =
  injl-trans Lω C.otL ωʟ ∣ C.colTable , I.code ∣₁
    (inclusion-coded C.otL ωʟ otL⊆ω)

stage-counted : StageCountedCoded
stage-counted = stage-counted-from limit-stage-counted
```
