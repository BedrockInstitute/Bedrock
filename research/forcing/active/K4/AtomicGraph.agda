{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track E: the atomic graph contract, section 1.6 of the K4 architecture.
--
-- THE QUESTION. Track C builds the two atomic values by a host recursion:
-- _≈ᴮ_ is rawPairRec applied to the expanded symmetric step, and _∈ᴮ_ is a
-- coded join over the support. Nothing about that recursion is visible to the
-- ground. A first-order formula cannot run it, and there is no substitution
-- operation anywhere in the tree with which to unroll it. So how does an
-- object-language formula name the value?
--
-- The answer is K3's answer for the name recogniser, one level up. Replace
-- the recursion by a WITNESS. Do not say "the value of m ≈ᴮ n is b"; say
-- "there is a coordinate domain C closed under taking entries, containing m
-- and n, and a table H over C which OBEYS the atomic step, and the entry of H
-- at the key ⟨m,n⟩ is b". The clause "H obeys the step" is flat: it quantifies
-- over the members of C and of H and compares them, which is all a bounded
-- formula can do. The two leading existentials over C and H are unbounded, so
-- the graph is Σ₁ exactly as the recogniser is, and no Δ₀ witness is offered
-- for it here or anywhere.
--
-- WHOSE MATHEMATICS THIS IS. The witness relation, its comparison theorem and
-- the fixed formula are K0's, at
-- k0-good-table-value-relation-2026-09.md (the relation Graph(x,y,b) and its
-- `unique`), k0-fixed-atomic-graph-formula-2026-09.md:7-22 (the formula's
-- exact content, with C, H and the pair code p as OBJECT-LANGUAGE bound
-- variables and no host-computed product inserted as a constant), and
-- k0-closed-domain-independence-2026-09.md (two child-closed domains give the
-- same value at shared coordinates). K0 states in its own words at
-- k0-bounded-table-recursion-2026-09.md:3 that "the actual Boolean atomic
-- step, its internal images, closed-name-domain adapters and general-ground
-- portability remain open", and its one checked instance is stated "For a
-- fixed actual L set X and B = P(X)".
--
-- WHAT THIS FILE THEREFORE IS. A CONTRACT and ONE DISCHARGE ROUTE, and not a
-- general-ground theorem. It builds every piece of syntax that does not depend
-- on the step: the child-closure clause, the internal entry clause, the two
-- graph formulas and their reading theorems. It declares the step clause, the
-- membership-image clause and the recursion's comparison theorem as contract
-- parameters, because each of the three is exactly a thing K0 has built at
-- B = P(X) in L and has NOT built at a general ground. It then proves that the
-- contract composes: `table→graph` turns a supply of value tables into an
-- inhabitant of `AtomicGraph`, which is the one instance discharge the
-- architecture asks for. Proving the step clause at a general ground would be
-- a scope error and is not attempted.
--
-- WHAT IS PROVED HERE AND NOT ASSUMED. The four reading theorems, against
-- explicitly written truth-value readings, so that a wrong de Bruijn shift is
-- a type error and not a silent change of meaning; the functionality of the
-- graph, by eliminating two truncated witnesses into a path in an h-set;
-- domain independence of the table readout; the exactness of the graph at a
-- name, in the form K0 calls `exact`; and that the union of two child-closed
-- domains is child-closed, which is the step K3's per-name `hereditary`
-- (NameSpace.agda:709, truncated) needs before a single domain can hold two
-- names.
--
-- ON WRITING FORMULAS. Every formula below is variable-indexed: its argument
-- slots are `Fin k` and nothing is baked in as a constant. K3's own reason is
-- decisive and applies here unchanged: there is no substitution operation in
-- the tree, so a formula with a parameter frozen into it can never afterwards
-- be nested under a binder. The graph formulas are used under two binders
-- (C and H) the moment they are written, which is why the shifts below are
-- `suc (suc _)` and not `suc _`, and why every reading theorem is stated at an
-- ARBITRARY environment rather than at the three-variable specialization.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import K4.Algebra

module K4.AtomicGraph {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; var; _∈̇_; _∧̇_; ∃̇_; ∀̇∈; ∃̇∈ )
open import FOL.LevyHierarchy using ( Δ₀; checkΔ₀ )
open import FOL.Semantics (hPropAlgebra ℓ) 𝒮 using ( module At; _^_ )
open import CodedVocabulary 𝒮 using ( isKPairΔ; prAtˢ )
open import Cubical.Data.Unit using ( tt )
open import Cubical.Data.Sum using ( _⊎_; inl; inr )
open import Cubical.Functions.Logic using ( ⇔toPath )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )

open TruthAlgebra (hPropAlgebra ℓ) hiding ( ¬_ )
open hPropStructure 𝒮
open At S id using ( _⊨_ )

-- Track A's point type, imported and never re-declared. Records are
-- generative and plain definitions are not, but K4.Algebra is opened here
-- WITHOUT public for the second of Track A's measured reasons: re-exporting a
-- record type name makes its record module reachable by two routes and a
-- consumer that opens both fails with AmbiguousModule (REPORT-A section 4).

open K4.Algebra 𝒮 using ( Pt )

-- The two crossings between the structure's equality and the host path. This
-- file states every value equation as a host path, because K0's own
-- comparison theorem "eliminates the two truncated witnesses only into
-- equality of elements of the h-set S", and converts to ≈ˢ only at the
-- boundary where the architecture's record demands that spelling.

≈→≡ : {x y : S} → ⟨ x ≈ˢ y ⟩ → x ≡ y
≈→≡ {x} {y} = subst ⟨_⟩ (paths x y)

≡→≈ : {x y : S} → x ≡ y → ⟨ x ≈ˢ y ⟩
≡→≈ {x} {y} = subst ⟨_⟩ (sym (paths x y))

-- ---------------------------------------------------------------------
-- The coded layer: the two clauses that do not depend on the step
-- ---------------------------------------------------------------------

-- CHILD CLOSURE. Character for character NameSpace.agda:145-165, with its
-- reading and its Δ₀ witness. It is copied rather than imported: `closedΔ` is
-- a plain definition over CodedVocabulary's `isKPairΔ`, so the copy and K3's
-- original are the same term and a K3 proof of ⟨ closedΔ W C ⟩ fits the slots
-- below definitionally, while importing NameSpace would drag the whole name
-- layer through the elaborator for two definitions and a `refl`.
--
-- The reading is the audit. Under the two bounded universals the outer slots
-- have moved down by two and under the first existential by one more, so the
-- carrier slot is `suc (suc (suc w))`. A wrong shift is invisible to the Δ₀
-- witness, which holds for any slot assignment, and is caught only by the
-- reading theorem.

closedAtˢ : ∀ {k} → Fin k → Fin k → Formula S k
closedAtˢ c w =
  ∀̇∈ (var c)
    (∀̇∈ (var zero)
      (∃̇∈ (var (suc (suc c)))
        (∃̇∈ (var (suc (suc (suc w))))
          (prAtˢ (suc (suc zero)) (suc zero) zero))))

closedΔ : S → S → Ω
closedΔ w C =
  ⋀ S (λ n → (n ∈ˢ C) ⇒
    (⋀ S (λ e → (e ∈ˢ n) ⇒
      (⋁ S (λ x → (x ∈ˢ C) ⊓
        (⋁ S (λ b → (b ∈ˢ w) ⊓ isKPairΔ e x b)))))))

Δ₀-closedAtˢ : ∀ {k} (c w : Fin k) → Δ₀ (closedAtˢ c w)
Δ₀-closedAtˢ c w = checkΔ₀ (closedAtˢ c w) tt

closedAtˢ-reading : ∀ {k} (c w : Fin k) (γ : S ^ k)
                  → (γ ⊨ closedAtˢ c w) ≡ closedΔ (lookup w γ) (lookup c γ)
closedAtˢ-reading c w γ = refl

-- THE UNION OF TWO CLOSED DOMAINS. K3's completeness result `hereditary`
-- (NameSpace.agda:709) gives ONE closed family per name, and it is truncated;
-- the atomic graph needs one domain holding BOTH names, which is K0's
-- ClosedNamePairDomain ("takes actual valid B-names x and y, reuses the
-- previously proved internal closure construction for each name, takes the
-- actual L union C of those closures"). This is the step that makes the two
-- into one, and it is stated through the union's three membership facts
-- rather than through a union operation, so any ground that has one can
-- discharge it and no operation enters this file's ledger. K3 proves the
-- corresponding fact for a SET of closed sets (NameSpace.agda:621, inside
-- Collect) and it is not exported, so this is not a duplicate of a reachable
-- lemma.
--
-- The proof is the only place where the closure clause is unfolded, and it
-- unfolds to a function type because ⋀ and ⇒ are the hProp algebra's.

closed-union : (W C D U : S)
             → ((z : S) → ⟨ z ∈ˢ C ⟩ → ⟨ z ∈ˢ U ⟩)
             → ((z : S) → ⟨ z ∈ˢ D ⟩ → ⟨ z ∈ˢ U ⟩)
             → ((z : S) → ⟨ z ∈ˢ U ⟩ → ∥ (⟨ z ∈ˢ C ⟩ ⊎ ⟨ z ∈ˢ D ⟩) ∥₁)
             → ⟨ closedΔ W C ⟩ → ⟨ closedΔ W D ⟩ → ⟨ closedΔ W U ⟩
closed-union W C D U inC inD out cc dd n hn e he =
  PT.rec PT.squash₁
    (λ { (inl h) → PT.map (λ { (x , hx , rest) → x , inC x hx , rest })
                          (cc n h e he)
       ; (inr h) → PT.map (λ { (x , hx , rest) → x , inD x hx , rest })
                          (dd n h e he) })
    (out n hn)

-- THE INTERNAL ENTRY. "the Kuratowski pair of the Kuratowski pair of x and y
-- with b belongs to H". K0 writes it "there exists p such that p = pair(x,y)
-- and pair(p,b) belongs to H" (k0-fixed-atomic-graph-formula:20-21); K3's
-- vocabulary supplies the pair as a RELATION, prAtˢ (CodedVocabulary.agda:112,
-- reading :127), so both pair codes are bound existentially and the formula
-- has two binders where K0's prose has one.
--
-- Both existentials are unbounded, and no Δ₀ witness is claimed for this
-- formula. There is a bounded presentation, quantifying q over H, then a
-- member s of q, then a member p of s, since p belongs to the singleton of p
-- which belongs to q; it is not built here because nothing below needs
-- absoluteness of the entry clause and the unbounded form is the one K0's
-- discharge produces.

entryAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Formula S k
entryAtˢ h x y b =
  ∃̇ ( prAtˢ zero (suc x) (suc y)
    ∧̇ (∃̇ ( prAtˢ zero (suc zero) (suc (suc b))
          ∧̇ (var zero ∈̇ var (suc (suc h))))))

entryΔ : S → S → S → S → Ω
entryΔ H x y b =
  ⋁ S (λ p → isKPairΔ p x y
    ⊓ (⋁ S (λ q → isKPairΔ q p b ⊓ (q ∈ˢ H))))

entryAtˢ-reading : ∀ {k} (h x y b : Fin k) (γ : S ^ k)
                 → (γ ⊨ entryAtˢ h x y b)
                   ≡ entryΔ (lookup h γ) (lookup x γ) (lookup y γ) (lookup b γ)
entryAtˢ-reading h x y b γ = refl

-- ---------------------------------------------------------------------
-- The contract layer
-- ---------------------------------------------------------------------

-- Everything below is relative to one algebra code B, the two value functions
-- of Track C, the recogniser, and the three things K0 has at B = P(X) in L and
-- nowhere else. Each is taken FLAT rather than as a module application, for
-- the preamble's measured reason: a parameter is a variable that cannot
-- unfold, and a module application is what put K3's composite signature past
-- the 360 second wall.
--
-- W := B throughout, the architecture's section 1.4 decision: the kernel's
-- weight carrier IS the algebra code, so the carrier slot of the closure
-- clause and the value bound of the recursion are the same variable. The
-- named trap is worth restating: this B is the ALGEBRA code and has nothing to
-- do with `nameBound` (NameSpace.agda:557), which bounds names and not values.

module Graph
  (B : S)
  -- Track C's record, flat. K4.Atomic's AtomicSemantics has exactly these two
  -- fields at exactly these types (K4/Atomic.agda:551-553), so the coordinator
  -- passes `AtomicSemantics.eqᴬ as` and `AtomicSemantics.memᴬ as` with no
  -- adaptation. They are taken flat rather than as the record because the
  -- record lives under a fifteen-parameter module application whose other
  -- thirteen parameters no statement in this file mentions: not one universal
  -- property of a value is read below, only the two values themselves.
  (eqᴬ  : S → S → Pt B)
  (memᴬ : S → S → Pt B)
  -- K3's recogniser, as a bare class. No absoluteness and no Δ₀ claim is made
  -- about it here, and none is needed: it occurs only as a hypothesis on the
  -- two totality statements.
  (IsName : S → Ω)
  -- K0's step clause. "H is good for the C-indexed step", as a formula with
  -- three variable slots and its reading. This is the contract boundary: the
  -- clause exists at B = P(X) in L (PowersetGoodFormula.For X.goodAt C H with
  -- its all-environment good-reading) and general-ground portability is open.
  (goodAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Formula S k)
  (goodΔ   : S → S → S → Ω)
  (goodAtˢ-reading : ∀ {k} (c h w : Fin k) (γ : S ^ k)
                   → (γ ⊨ goodAtˢ c h w)
                     ≡ goodΔ (lookup w γ) (lookup c γ) (lookup h γ))
  -- K0's weighted membership image, the same way. The equality value is read
  -- off the table as an entry; the membership value is the relative supremum
  -- over the support of n of the weighted equality values, so it is read off
  -- the SAME table by a different clause. K0 builds that clause at B = P(X)
  -- (WeightedTableImage, and the outer template of
  -- k0-outer-weighted-expression-2026-09.md); it needs an internal indexed
  -- supremum, which K4 has as supᴮ on Pt B and NOT as object syntax, so it is
  -- a contract parameter and not a construction.
  (imgAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Fin k → Formula S k)
  (imgΔ   : S → S → S → S → S → Ω)
  (imgAtˢ-reading : ∀ {k} (h x y b w : Fin k) (γ : S ^ k)
                  → (γ ⊨ imgAtˢ h x y b w)
                    ≡ imgΔ (lookup h γ) (lookup x γ) (lookup y γ)
                           (lookup b γ) (lookup w γ))
  where

  -- -------------------------------------------------------------------
  -- The graph skeleton, written once and instantiated twice
  -- -------------------------------------------------------------------

  -- The two graph formulas differ in one conjunct and agree in the other
  -- five, so the skeleton is factored out with the differing conjunct as a
  -- plain `Formula S (suc (suc k))` argument: first order, so there is no
  -- higher-rank argument to elaborate, and the payload is written at the call
  -- site where its shifts are visible beside the skeleton's.
  --
  -- The conjunct order is K0's, with one deliberate change: the step clause is
  -- LAST rather than fourth. K0's list is closure, x in C, y in C, goodness,
  -- b in B, the entry (k0-fixed-atomic-graph-formula:12-19). Conjunction is
  -- commutative and the reading theorem below states exactly what the order
  -- is, so nothing mathematical turns on it; what turns on it is that the two
  -- conjuncts whose readings are HYPOTHESES rather than refl are then
  -- adjacent and innermost, and the reading proof is a chain of
  -- single-argument congruences with every fixed endpoint written into the
  -- section. That is project rule 1's remedy applied before the rule can bite:
  -- no cong₂ and no bare refl inside a congruence occurs in this file.

  graphBody : ∀ {k} → Formula S (suc (suc k))
            → Fin k → Fin k → Fin k → Fin k → Formula S k
  graphBody pay b m n w =
    ∃̇ (∃̇ ( closedAtˢ (suc zero) (suc (suc w))
          ∧̇ ((var (suc (suc m)) ∈̇ var (suc zero))
          ∧̇ ((var (suc (suc n)) ∈̇ var (suc zero))
          ∧̇ ((var (suc (suc b)) ∈̇ var (suc (suc w)))
          ∧̇ (pay ∧̇ goodAtˢ (suc zero) zero (suc (suc w))))))))

  graphΔ : (S → S → Ω) → S → S → S → S → Ω
  graphΔ P W b m n =
    ⋁ S (λ C → ⋁ S (λ H →
        closedΔ W C
      ⊓ ((m ∈ˢ C)
      ⊓ ((n ∈ˢ C)
      ⊓ ((b ∈ˢ W)
      ⊓ (P C H ⊓ goodΔ W C H))))))

  -- The reading of the skeleton at an arbitrary environment, with the
  -- payload's own reading as its only hypothesis. Read it back against the
  -- intended content before using it: under the two existentials the outer
  -- slots have moved down by two, so `suc (suc m)` is the m of the ambient
  -- environment, `suc zero` is C and `zero` is H, and the carrier slot
  -- `suc (suc w)` is both the closure clause's carrier and the bound that b
  -- must meet. The membership conjuncts say m and n belong to C, not to B.

  graph-reading : ∀ {k} (pay : Formula S (suc (suc k))) (P : S → S → Ω)
                  (b m n w : Fin k) (γ : S ^ k)
                → ((C H : S) → ((H ∷ C ∷ γ) ⊨ pay) ≡ P C H)
                → (γ ⊨ graphBody pay b m n w)
                  ≡ graphΔ P (lookup w γ) (lookup b γ)
                             (lookup m γ) (lookup n γ)
  graph-reading pay P b m n w γ pr =
    cong (⋁ S) (funExt (λ C → cong (⋁ S) (funExt (λ H → inner C H))))
    where
      -- The type is written out rather than left to unification, because it
      -- IS the audit: the left side is what the evaluator makes of the body
      -- under the two binders, the right side is the intended reading, and a
      -- wrong shift makes the two fail to match rather than quietly agreeing
      -- on a different statement.
      inner : (C H : S)
            → ((H ∷ C ∷ γ)
                 ⊨ ( closedAtˢ (suc zero) (suc (suc w))
                   ∧̇ ((var (suc (suc m)) ∈̇ var (suc zero))
                   ∧̇ ((var (suc (suc n)) ∈̇ var (suc zero))
                   ∧̇ ((var (suc (suc b)) ∈̇ var (suc (suc w)))
                   ∧̇ (pay ∧̇ goodAtˢ (suc zero) zero (suc (suc w))))))))
              ≡ ( closedΔ (lookup w γ) C
                ⊓ ((lookup m γ ∈ˢ C)
                ⊓ ((lookup n γ ∈ˢ C)
                ⊓ ((lookup b γ ∈ˢ lookup w γ)
                ⊓ (P C H ⊓ goodΔ (lookup w γ) C H)))))
      inner C H =
        cong (closedΔ (lookup w γ) C ⊓_)
          (cong ((lookup m γ ∈ˢ C) ⊓_)
            (cong ((lookup n γ ∈ˢ C) ⊓_)
              (cong ((lookup b γ ∈ˢ lookup w γ) ⊓_)
                (  cong (_⊓ ((H ∷ C ∷ γ)
                             ⊨ goodAtˢ (suc zero) zero (suc (suc w))))
                        (pr C H)
                ∙ cong (P C H ⊓_)
                       (goodAtˢ-reading (suc zero) zero (suc (suc w))
                                        (H ∷ C ∷ γ))))))

  -- -------------------------------------------------------------------
  -- The two graph formulas
  -- -------------------------------------------------------------------

  eqGraphAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Formula S k
  eqGraphAtˢ b m n w =
    graphBody (entryAtˢ zero (suc (suc m)) (suc (suc n)) (suc (suc b)))
              b m n w

  eqGraphΔ : S → S → S → S → Ω
  eqGraphΔ W b m n = graphΔ (λ _ H → entryΔ H m n b) W b m n

  eqGraph-reading : ∀ {k} (b m n w : Fin k) (γ : S ^ k)
                → (γ ⊨ eqGraphAtˢ b m n w)
                  ≡ eqGraphΔ (lookup w γ) (lookup b γ)
                             (lookup m γ) (lookup n γ)
  eqGraph-reading b m n w γ =
    graph-reading (entryAtˢ zero (suc (suc m)) (suc (suc n)) (suc (suc b)))
                  (λ _ H → entryΔ H (lookup m γ) (lookup n γ) (lookup b γ))
                  b m n w γ (λ C H → refl)

  memGraphAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Formula S k
  memGraphAtˢ b m n w =
    graphBody (imgAtˢ zero (suc (suc m)) (suc (suc n))
                      (suc (suc b)) (suc (suc w)))
              b m n w

  memGraphΔ : S → S → S → S → Ω
  memGraphΔ W b m n = graphΔ (λ _ H → imgΔ H m n b W) W b m n

  memGraph-reading : ∀ {k} (b m n w : Fin k) (γ : S ^ k)
                 → (γ ⊨ memGraphAtˢ b m n w)
                   ≡ memGraphΔ (lookup w γ) (lookup b γ)
                               (lookup m γ) (lookup n γ)
  memGraph-reading b m n w γ =
    graph-reading (imgAtˢ zero (suc (suc m)) (suc (suc n))
                          (suc (suc b)) (suc (suc w)))
                  (λ _ H → imgΔ H (lookup m γ) (lookup n γ)
                                  (lookup b γ) (lookup w γ))
                  b m n w γ
                  (λ C H → imgAtˢ-reading zero (suc (suc m)) (suc (suc n))
                                          (suc (suc b)) (suc (suc w))
                                          (H ∷ C ∷ γ))

  -- -------------------------------------------------------------------
  -- The architecture's contract record
  -- -------------------------------------------------------------------

  -- The record lands at Type (ℓ-suc ℓ) because the two reading fields are
  -- paths in Ω. Section 1.0's rule 1 therefore applies to it: it can never
  -- index ⋀, ⋁, ⋀ᴮ or ⋁ᴮ. Nothing below places one inside a join; it is a
  -- hypothesis of Track F and a result of this file, which is exactly the use
  -- the rule permits.
  --
  -- The Σ₁ complexity is recorded IN the signature block and nowhere
  -- discharged. There is no Δ₀-eqAtˢ and no Δ₀-memAtˢ field, on the model
  -- of K3's recogniser (NameSpace.agda:170-184, which likewise ships no Δ₀
  -- witness), and no absoluteness of the graph or of IsName is claimed,
  -- asserted or used.

  record AtomicGraph : Type (ℓ-suc ℓ) where
    field
      eqAtˢ  : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Formula S k
      memAtˢ : ∀ {k} → Fin k → Fin k → Fin k → Fin k → Formula S k
      eqΔ    : S → S → S → S → Ω
      memΔ   : S → S → S → S → Ω
      eqAtˢ-reading : ∀ {k} (b m n w : Fin k) (γ : S ^ k)
                    → (γ ⊨ eqAtˢ b m n w)
                      ≡ eqΔ (lookup w γ) (lookup b γ)
                            (lookup m γ) (lookup n γ)
      memAtˢ-reading : ∀ {k} (b m n w : Fin k) (γ : S ^ k)
                     → (γ ⊨ memAtˢ b m n w)
                       ≡ memΔ (lookup w γ) (lookup b γ)
                              (lookup m γ) (lookup n γ)
      eq-sound  : (m n b : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
                → ⟨ eqΔ B b m n ⟩ → ⟨ b ≈ˢ fst (eqᴬ m n) ⟩
      eq-total  : (m n : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
                → ⟨ eqΔ B (fst (eqᴬ m n)) m n ⟩
      mem-sound : (m n b : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
                → ⟨ memΔ B b m n ⟩ → ⟨ b ≈ˢ fst (memᴬ m n) ⟩
      mem-total : (m n : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
                → ⟨ memΔ B (fst (memᴬ m n)) m n ⟩

  -- -------------------------------------------------------------------
  -- The value table at a fixed child-closed coordinate domain
  -- -------------------------------------------------------------------

  -- K0's Solve "returns an actual internal table in L, its Good proof and
  -- product bound, a total data-valued readout on D, membership of every value
  -- in B, graph membership and the local step equation"
  -- (k0-bounded-table-recursion:7). The four fields below are that output,
  -- minus the bound and the step equation, which no statement in this file
  -- reads: what is used is the table, its goodness, the readout and the fact
  -- that the readout is the table's entry.
  --
  -- The readout lands in Pt B, so "membership of every value in B" is the
  -- second projection and not a field. The record is at Type ℓ, not
  -- Type (ℓ-suc ℓ) as architecture section 1.6 prints it: every field is a
  -- code, a truth-value inhabitant or a function into Pt B, and Pt B is
  -- Type ℓ. That matters because a Type ℓ record can be truncated and can
  -- index a join, and a Type (ℓ-suc ℓ) one cannot.
  --
  -- NOTHING HERE MENTIONS eqᴬ OR memᴬ. That is deliberate and it is what makes
  -- `table-independent` below a theorem with content rather than a tautology:
  -- a value table is a good table with a readout, and the claim that its
  -- readout is the atomic value is a SEPARATE record.

  record ValueTable (Cd : S) : Type ℓ where
    field
      table     : S
      domain    : ⟨ closedΔ B Cd ⟩
      good      : ⟨ goodΔ B Cd table ⟩
      eqVal     : (x y : S) → ⟨ x ∈ˢ Cd ⟩ → ⟨ y ∈ˢ Cd ⟩ → Pt B
      memVal    : (x y : S) → ⟨ x ∈ˢ Cd ⟩ → ⟨ y ∈ˢ Cd ⟩ → Pt B
      eq-entry  : (x y : S) (hx : ⟨ x ∈ˢ Cd ⟩) (hy : ⟨ y ∈ˢ Cd ⟩)
                → ⟨ entryΔ table x y (fst (eqVal x y hx hy)) ⟩
      mem-entry : (x y : S) (hx : ⟨ x ∈ˢ Cd ⟩) (hy : ⟨ y ∈ˢ Cd ⟩)
                → ⟨ imgΔ table x y (fst (memVal x y hx hy)) B ⟩

  -- K0's comparison theorem, which is the recursion's and not K4's. Its proof
  -- forms E = C ∩ D by internal Separation, restricts both tables to E × E,
  -- transports the step across the change of bound and compares each
  -- restriction with the canonical table over E
  -- (k0-closed-domain-independence-2026-09.md). Every ingredient of that proof
  -- is an operation on internal sets that this file does not have and an
  -- induction along the recursion's well-founded dependency, which this file
  -- cannot state. It is therefore a contract, stated at the strength K0
  -- actually proves it: ARBITRARY good tables, not only the ones a
  -- ValueTable carries, because the graph quantifies over arbitrary H and a
  -- comparison restricted to constructed tables would not reach the witnesses
  -- soundness has to handle.

  record TableComparison : Type ℓ where
    field
      eq-unique  : (C D H K x y b c : S)
                 → ⟨ closedΔ B C ⟩ → ⟨ closedΔ B D ⟩
                 → ⟨ goodΔ B C H ⟩ → ⟨ goodΔ B D K ⟩
                 → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
                 → ⟨ entryΔ H x y b ⟩ → ⟨ entryΔ K x y c ⟩ → b ≡ c
      mem-unique : (C D H K x y b c : S)
                 → ⟨ closedΔ B C ⟩ → ⟨ closedΔ B D ⟩
                 → ⟨ goodΔ B C H ⟩ → ⟨ goodΔ B D K ⟩
                 → ⟨ x ∈ˢ C ⟩ → ⟨ y ∈ˢ C ⟩ → ⟨ x ∈ˢ D ⟩ → ⟨ y ∈ˢ D ⟩
                 → ⟨ imgΔ H x y b B ⟩ → ⟨ imgΔ K x y c B ⟩ → b ≡ c

  -- The bridge from the table's readout to Track C's two values. K0's own
  -- remaining-work list separates this from independence in exactly these
  -- words: "Domain independence alone does not prove reflexivity,
  -- transitivity, substitution or check-name adequacy"
  -- (k0-closed-domain-independence, remaining work 2), and the semantic
  -- computation laws are listed there as still to be derived. So it is a
  -- second record and not a field of ValueTable.

  record Adequate (Cd : S) (t : ValueTable Cd) : Type ℓ where
    field
      eq-value  : (x y : S) (hx : ⟨ x ∈ˢ Cd ⟩) (hy : ⟨ y ∈ˢ Cd ⟩)
                → fst (ValueTable.eqVal t x y hx hy) ≡ fst (eqᴬ x y)
      mem-value : (x y : S) (hx : ⟨ x ∈ˢ Cd ⟩) (hy : ⟨ y ∈ˢ Cd ⟩)
                → fst (ValueTable.memVal t x y hx hy) ≡ fst (memᴬ x y)

  -- -------------------------------------------------------------------
  -- Domain independence
  -- -------------------------------------------------------------------

  -- The architecture's `table-independent`, and K0's statement: "If actual
  -- coordinate sets C and D are closed under the material child relation,
  -- then their constructed recursion tables give equal values at every
  -- ordered pair whose two coordinates belong to both sets. Neither C nor D
  -- must contain the other."
  --
  -- Why it is needed and what it licenses. K3's `hereditary` is TRUNCATED at
  -- both of its sites (NameSpace.agda:709 and :865), so the closed family a
  -- name lives in is never in hand as a datum, only merely. No value may be
  -- read out of such a family until the reading is known not to depend on
  -- which family was chosen, and that is this statement. Once it holds, every
  -- statement below eliminates the truncation into a proposition or into a
  -- path in an h-set, and no representative is ever selected.

  module Independence (tc : TableComparison) where

    open TableComparison tc

    table-independent : (Cd Cd' : S)
                        (t : ValueTable Cd) (t' : ValueTable Cd')
                        (x y : S)
                        (hx : ⟨ x ∈ˢ Cd ⟩) (hy : ⟨ y ∈ˢ Cd ⟩)
                        (hx' : ⟨ x ∈ˢ Cd' ⟩) (hy' : ⟨ y ∈ˢ Cd' ⟩)
                      → fst (ValueTable.eqVal t x y hx hy)
                        ≡ fst (ValueTable.eqVal t' x y hx' hy')
    table-independent Cd Cd' t t' x y hx hy hx' hy' =
      eq-unique Cd Cd' (ValueTable.table t) (ValueTable.table t') x y _ _
                (ValueTable.domain t) (ValueTable.domain t')
                (ValueTable.good t) (ValueTable.good t')
                hx hy hx' hy'
                (ValueTable.eq-entry t x y hx hy)
                (ValueTable.eq-entry t' x y hx' hy')

    table-independent-mem : (Cd Cd' : S)
                            (t : ValueTable Cd) (t' : ValueTable Cd')
                            (x y : S)
                            (hx : ⟨ x ∈ˢ Cd ⟩) (hy : ⟨ y ∈ˢ Cd ⟩)
                            (hx' : ⟨ x ∈ˢ Cd' ⟩) (hy' : ⟨ y ∈ˢ Cd' ⟩)
                          → fst (ValueTable.memVal t x y hx hy)
                            ≡ fst (ValueTable.memVal t' x y hx' hy')
    table-independent-mem Cd Cd' t t' x y hx hy hx' hy' =
      mem-unique Cd Cd' (ValueTable.table t) (ValueTable.table t') x y _ _
                 (ValueTable.domain t) (ValueTable.domain t')
                 (ValueTable.good t) (ValueTable.good t')
                 hx hy hx' hy'
                 (ValueTable.mem-entry t x y hx hy)
                 (ValueTable.mem-entry t' x y hx' hy')

    -- The same fact one level up, about the GRAPH rather than about two
    -- tables: the relation is single valued. This is K0's `unique`, and it is
    -- the statement that makes the graph usable at all, because a relation
    -- that held of two different codes would name no value. Both truncated
    -- witnesses are eliminated into a path in S, which is a proposition
    -- because S is an h-set, so nothing is chosen.

    eqGraphΔ-functional : (m n b c : S)
                   → ⟨ eqGraphΔ B b m n ⟩ → ⟨ eqGraphΔ B c m n ⟩ → b ≡ c
    eqGraphΔ-functional m n b c =
      PT.rec (isPropΠ (λ _ → isSetS b c))
        (λ { (C , wC) → PT.rec (isPropΠ (λ _ → isSetS b c))
          (λ { (H , clC , hmC , hnC , _ , enH , gdH) →
            PT.rec (isSetS b c)
              (λ { (D , wD) → PT.rec (isSetS b c)
                (λ { (K , clD , hmD , hnD , _ , enK , gdK) →
                  eq-unique C D H K m n b c clC clD gdH gdK
                            hmC hnC hmD hnD enH enK })
                wD })
              })
            wC })

    memGraphΔ-functional : (m n b c : S)
                    → ⟨ memGraphΔ B b m n ⟩ → ⟨ memGraphΔ B c m n ⟩ → b ≡ c
    memGraphΔ-functional m n b c =
      PT.rec (isPropΠ (λ _ → isSetS b c))
        (λ { (C , wC) → PT.rec (isPropΠ (λ _ → isSetS b c))
          (λ { (H , clC , hmC , hnC , _ , imH , gdH) →
            PT.rec (isSetS b c)
              (λ { (D , wD) → PT.rec (isSetS b c)
                (λ { (K , clD , hmD , hnD , _ , imK , gdK) →
                  mem-unique C D H K m n b c clC clD gdH gdK
                             hmC hnC hmD hnD imH imK })
                wD })
              })
            wC })

  -- -------------------------------------------------------------------
  -- The discharge route
  -- -------------------------------------------------------------------

  -- What a ground must supply, and the whole of it. For any two names there is
  -- MERELY a child-closed domain containing both, a good table over it, and
  -- the identification of its readout with Track C's two values. This is K0's
  -- ClosedNamePairDomain composed with NamePairRecursion and the semantic
  -- value relation, and it is where the general-ground gap sits: K0 has this
  -- at B = P(X) in L and states that general-ground portability is open.

  AdequateAt : S → S → Type ℓ
  AdequateAt m n =
    Σ[ Cd ∈ S ] Σ[ t ∈ ValueTable Cd ]
      (Adequate Cd t × (⟨ m ∈ˢ Cd ⟩ × ⟨ n ∈ˢ Cd ⟩))

  TableSupply : Type ℓ
  TableSupply = (m n : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩ → ∥ AdequateAt m n ∥₁

  -- The one instance discharge. Given the comparison contract and a supply of
  -- adequate tables, the four soundness and totality obligations hold and the
  -- record is inhabited. Every use of the supply eliminates its truncation
  -- into a proposition: ⟨ eqGraphΔ B b m n ⟩ is an hProp and so is
  -- ⟨ b ≈ˢ c ⟩, so PT.rec applies with nothing to check and no witness is
  -- chosen.

  module Discharge (tc : TableComparison) (sup : TableSupply) where

    open TableComparison tc
    open Independence tc public

    eq-total : (m n : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
             → ⟨ eqGraphΔ B (fst (eqᴬ m n)) m n ⟩
    eq-total m n hm hn =
      PT.rec (snd (eqGraphΔ B (fst (eqᴬ m n)) m n))
        (λ { (Cd , t , ad , hmC , hnC) →
          ∣ Cd , ∣ ValueTable.table t
                 , ValueTable.domain t
                 , hmC , hnC
                 , snd (eqᴬ m n)
                 , subst (λ z → ⟨ entryΔ (ValueTable.table t) m n z ⟩)
                         (Adequate.eq-value ad m n hmC hnC)
                         (ValueTable.eq-entry t m n hmC hnC)
                 , ValueTable.good t ∣₁ ∣₁ })
        (sup m n hm hn)

    mem-total : (m n : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
              → ⟨ memGraphΔ B (fst (memᴬ m n)) m n ⟩
    mem-total m n hm hn =
      PT.rec (snd (memGraphΔ B (fst (memᴬ m n)) m n))
        (λ { (Cd , t , ad , hmC , hnC) →
          ∣ Cd , ∣ ValueTable.table t
                 , ValueTable.domain t
                 , hmC , hnC
                 , snd (memᴬ m n)
                 , subst (λ z → ⟨ imgΔ (ValueTable.table t) m n z B ⟩)
                         (Adequate.mem-value ad m n hmC hnC)
                         (ValueTable.mem-entry t m n hmC hnC)
                 , ValueTable.good t ∣₁ ∣₁ })
        (sup m n hm hn)

    eq-sound : (m n b : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
             → ⟨ eqGraphΔ B b m n ⟩ → ⟨ b ≈ˢ fst (eqᴬ m n) ⟩
    eq-sound m n b hm hn g =
      ≡→≈ (eqGraphΔ-functional m n b (fst (eqᴬ m n)) g (eq-total m n hm hn))

    mem-sound : (m n b : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
              → ⟨ memGraphΔ B b m n ⟩ → ⟨ b ≈ˢ fst (memᴬ m n) ⟩
    mem-sound m n b hm hn g =
      ≡→≈ (memGraphΔ-functional m n b (fst (memᴬ m n)) g (mem-total m n hm hn))

    -- K0's `exact`: at a name the graph does not merely determine the value,
    -- it IS the statement that b is the value. This is the form Track F will
    -- want, because a reading theorem whose right-hand side is a comparison
    -- with a known code composes with the compiler's other clauses, while one
    -- whose right-hand side is an existential does not.

    eq-exact : (m n b : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
             → eqGraphΔ B b m n ≡ (b ≈ˢ fst (eqᴬ m n))
    eq-exact m n b hm hn =
      ⇔toPath {P = eqGraphΔ B b m n} {Q = b ≈ˢ fst (eqᴬ m n)}
        (eq-sound m n b hm hn)
        (λ h → subst (λ z → ⟨ eqGraphΔ B z m n ⟩) (sym (≈→≡ h))
                     (eq-total m n hm hn))

    mem-exact : (m n b : S) → ⟨ IsName m ⟩ → ⟨ IsName n ⟩
              → memGraphΔ B b m n ≡ (b ≈ˢ fst (memᴬ m n))
    mem-exact m n b hm hn =
      ⇔toPath {P = memGraphΔ B b m n} {Q = b ≈ˢ fst (memᴬ m n)}
        (mem-sound m n b hm hn)
        (λ h → subst (λ z → ⟨ memGraphΔ B z m n ⟩) (sym (≈→≡ h))
                     (mem-total m n hm hn))

    atomicGraph : AtomicGraph
    atomicGraph = record
      { eqAtˢ          = eqGraphAtˢ
      ; memAtˢ         = memGraphAtˢ
      ; eqΔ            = eqGraphΔ
      ; memΔ           = memGraphΔ
      ; eqAtˢ-reading  = eqGraph-reading
      ; memAtˢ-reading = memGraph-reading
      ; eq-sound       = eq-sound
      ; eq-total       = eq-total
      ; mem-sound      = mem-sound
      ; mem-total      = mem-total }

  -- The architecture's `table→graph`, as one function rather than a module.
  --
  -- Project rule 3 does NOT bite here, and the negative is measured rather
  -- than assumed. The type of this declaration contains a record of this
  -- layer, `AtomicGraph`, and its body is a projection out of a module
  -- applied to two arguments, which is the shape the rule names. Written
  -- point-free the file costs 1.34 s at 360 MB; written
  -- `table→graph tc sup = Discharge.atomicGraph tc sup` it costs 1.24 s at
  -- 361 MB (chk-E11.log against chk-E12.log). The difference is noise, and
  -- the whole file is 1.3 s. Rule 3's measured kills were composites of one
  -- LAYER applied to a term of another; a module application at two
  -- parameters of the same layer is not one.

  table→graph : TableComparison → TableSupply → AtomicGraph
  table→graph = Discharge.atomicGraph
