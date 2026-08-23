{-# OPTIONS --cubical --safe --guardedness #-}

-- [LJ-1.574] W3.  THE WIDEST UNMEASURED TERM, TYPE ONLY.
--
-- WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
-- task, exactly as the brief orders.  No hole, no postulate.
--
-- The brief names the widest unmeasured term:
--
--     -- [LJ-1.560]'s obligation, re-ascribed at leastOf's predicate,
--     -- TYPE ONLY
--
-- `leastOf`'s predicate is [LJ-1.557]'s `Good`
-- (agents/tasks/LJ-1-557/Probe557.agda:203-204), which is `Code a (up γ)`
-- (Probe557.agda:82-83), which is `L.GCH.InjL` (src/L/GCH.lagda.md:38):
-- a truncated Σ over the WHOLE L-carrier.  [LJ-1.557] measured that
-- this is "a quantifier over the whole L-carrier and not over a stage"
-- (agents/tasks/LJ-1-557/lj-1.557-report.md, ## POINTWISE AGAINST
-- UNIFORM).
--
-- [LJ-1.560]'s reflection step takes a FORMULA and bounds its
-- unbounded existential to a stage.  So the question "does it apply"
-- is one question and not two: IS THAT QUANTIFIER THE ⊨ OF A FORMULA?
--
-- Sections, one line each.
--   0.  `leastOf`'s predicate, re-ascribed.
--   1.  `codeFo`, the formula.  `InjCode`'s fourth conjunct is the only
--       one the tree does not already carry as syntax; `valFo` is it.
--   2.  THE BRIDGE, BOTH DIRECTIONS.  `InjL a c` IS `⊨ ∃̇ codeFo`.
--   3.  [LJ-1.560]'s OBLIGATION, RE-ASCRIBED AT IT.
--
-- CALIBER.  The program set GHCRTS="-A64m -I0 -M8g" on this pane.  I
-- did not set it.  One Agda process at a time.

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module LJ-1-574.runs.W3 {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Formula; var; _∈̇_; _∧̇_; _⇒̇_; ∀̇_; ∃̇_ )
open import FOL.Manipulation.Relativize using ( relativize )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ} using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Axioms.Basic {ℓ} using ( LsetS )
open import L.Cardinal {ℓ} lem using ( InjCode )
open import L.GCH {ℓ} lem using ( InjL )
open import L.Coding.Model {ℓ}
  using ( appAt; appAt-adequate; svAt; svAt-in; svAt-out
        ; domAt; domAt-in; domAt-out; domAt-intro )
open import L.Coding.Injection {ℓ} lem using ( injAt; injAt-in; injAt-out )
open import L.Reflect {ℓ} lem using ( Below; Wit; module Single )
open import L.ReflectFo {ℓ} lem using ( mkReflect )

open import Cubical.Data.FinData using ( Fin; zero; suc )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )
open import Cubical.Functions.Logic using ( ∃[∶]-syntax )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ using ( S )

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL using ( _^_ ) renaming ( _⊨ᵐ_ to _⊨_ )


-- ===================================================================
-- SECTION 0.  `leastOf`'s PREDICATE, RE-ASCRIBED.
-- ===================================================================

-- [LJ-1.557]'s `Good` with the frame's `up γ` abstracted to a bare
-- L-element, because nothing below reads the frame.
Selected : (a : S) → S → hProp (ℓ-suc ℓ)
Selected a c = InjL a c , squash₁


-- ===================================================================
-- SECTION 1.  `codeFo`.
--
--   `InjCode F a c` (src/L/Cardinal.lagda.md:223-228) is FOUR
--   conjuncts.  Three of them are already ⊨ of a named formula, and
--   the formulas are polymorphic in the arity, so they move from the
--   arity-2 environment `(F ∷ a ∷ [])` to the arity-3 one
--   `(F ∷ a ∷ c ∷ [])` with the SAME `Fin` index.
--
--   THE FOURTH IS NOT SYNTAX IN THE TREE.  It is the ambient sentence
--   "every value lies in c".  `L.Coding.Injection` does carry that
--   sentence as a formula, `ranAt` (src/L/Coding/Injection.lagda.md:230),
--   BUT `ranAt` sits under the `private` at
--   src/L/Coding/Injection.lagda.md:156 and is not exported, and it
--   states the range EXACTLY rather than as a subset.  `valFo` below
--   is the one implication `InjCode` asks for, built from the exported
--   `appAt`.
-- ===================================================================

-- Environment (F ∷ a ∷ c ∷ []).  Two ∀̇ push it to
-- (y ∷ x ∷ F ∷ a ∷ c ∷ []): 0 = y, 1 = x, 2 = F, 4 = c.
valFo : Formula S 3
valFo = ∀̇ (∀̇ ( appAt (suc (suc zero)) (suc zero) zero
             ⇒̇ (var zero ∈̇ var (suc (suc (suc (suc zero))))) ))

codeFo : Formula S 3
codeFo = svAt zero ∧̇ (domAt zero (suc zero) ∧̇ (injAt zero ∧̇ valFo))

-- The fourth conjunct's adequacy, and it is `appAt-adequate` twice.
valFo-adequate : (F a c : S)
  → ⟨ (F ∷ a ∷ c ∷ []) ⊨ valFo ⟩
  ≡ ((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst c ⟩)
valFo-adequate F a c i =
  (x y : S)
  → ⟨ appAt-adequate (suc (suc zero)) (suc zero) zero
        (y ∷ x ∷ F ∷ a ∷ c ∷ []) i ⟩
  → ⟨ fst y ∈ fst c ⟩


-- ===================================================================
-- SECTION 2.  THE BRIDGE, BOTH DIRECTIONS.
-- ===================================================================

code→sat : (F a c : S) → InjCode F a c → ⟨ (F ∷ a ∷ c ∷ []) ⊨ codeFo ⟩
code→sat F a c (sv , dm , ij , vl) =
    svAt-in zero (F ∷ a ∷ c ∷ []) (svAt-out zero (F ∷ a ∷ []) sv)
  , ( domAt-intro zero (suc zero) (F ∷ a ∷ c ∷ []) dom
    , ( injAt-in zero (F ∷ a ∷ c ∷ []) (injAt-out zero (F ∷ a ∷ []) ij)
      , transport (sym (valFo-adequate F a c)) vl ) )
  where
  dom : (x : S)
      → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩)
      × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩)
  dom x =
      PT.rec (snd (fst x ∈ fst a))
        (λ { (y , p) → domAt-out zero (suc zero) (F ∷ a ∷ []) dm x y p })
    , domAt-in zero (suc zero) (F ∷ a ∷ []) dm x

sat→code : (F a c : S) → ⟨ (F ∷ a ∷ c ∷ []) ⊨ codeFo ⟩ → InjCode F a c
sat→code F a c (sv , (dm , (ij , vl))) =
    svAt-in zero (F ∷ a ∷ []) (svAt-out zero (F ∷ a ∷ c ∷ []) sv)
  , ( domAt-intro zero (suc zero) (F ∷ a ∷ []) dom
    , ( injAt-in zero (F ∷ a ∷ []) (injAt-out zero (F ∷ a ∷ c ∷ []) ij)
      , transport (valFo-adequate F a c) vl ) )
  where
  dom : (x : S)
      → (⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩ → ⟨ fst x ∈ fst a ⟩)
      × (⟨ fst x ∈ fst a ⟩ → ⟨ ∃[ y ∶ S ] (pr (fst x) (fst y) ∈ fst F) ⟩)
  dom x =
      PT.rec (snd (fst x ∈ fst a))
        (λ { (y , p) → domAt-out zero (suc zero) (F ∷ a ∷ c ∷ []) dm x y p })
    , domAt-in zero (suc zero) (F ∷ a ∷ c ∷ []) dm x

-- AND THE SEARCH ITSELF.  `leastOf`'s predicate IS the object
-- language's own unbounded existential at `codeFo`.
selected→sat : (a c : S) → ⟨ Selected a c ⟩ → ⟨ (a ∷ c ∷ []) ⊨ (∃̇ codeFo) ⟩
selected→sat a c = PT.map (λ { (F , h) → F , code→sat F a c h })

sat→selected : (a c : S) → ⟨ (a ∷ c ∷ []) ⊨ (∃̇ codeFo) ⟩ → ⟨ Selected a c ⟩
sat→selected a c = PT.map (λ { (F , h) → F , sat→code F a c h })


-- ===================================================================
-- SECTION 3.  [LJ-1.560]'s OBLIGATION, RE-ASCRIBED AT IT.
--
--   Both reflection steps the tree carries, instantiated at `codeFo`.
--   Neither term is written here: both are the library's own.
-- ===================================================================

-- 3a.  THE SINGLE-MATRIX LADDER, [LJ-1.560]'s `w3-single`
--      (src/L/Reflect.lagda.md:520).  The matrix is untouched, so the
--      right-hand side is `Wit`: a witness IN `Lset βω`.
--      ITS PRICE IS `Below (Single.βω codeFo) ρ`, and `βω` depends on
--      `codeFo` ALONE.  `codeFo` carries NO constant, so this stage is
--      fixed once and for all and the parameters must fit inside it.
w3-single : (ρ : S ^ 2) → Below (Single.βω codeFo) ρ
          → (ρ ⊨ (∃̇ codeFo)) ≡ Wit codeFo ρ (Single.βω codeFo)
w3-single = Single.reflect codeFo

-- 3b.  THE CALLER-CHOSEN LADDER, [LJ-1.560]'s `w3-full`
--      (src/L/ReflectFo.lagda.md:525).  ANY ordinal the caller names
--      goes INSIDE the stage, so the parameters are no longer a price.
--      The matrix is relativized instead.
w3-full : (μ : V ℓ) (oμ : IsOrd μ)
        → Σ[ β ∈ V ℓ ] Σ[ oβ ∈ IsOrd β ]
            ( ⟨ μ ∈ β ⟩
            × ((γ : S ^ 2) → Below β γ
               → (γ ⊨ (∃̇ codeFo)) ≡ (γ ⊨ relativize (LsetS β oβ) (∃̇ codeFo))) )
w3-full = mkReflect (∃̇ codeFo)
