{-# OPTIONS --cubical --safe --guardedness #-}

-- K4 Track G: the substitution calculus. Bell 1.17(vii).
--
-- WHAT THIS MODULE PROVES.
--
-- Bell's (vii) reads  ⟦u = v⟧ ∧ ⟦φ(u)⟧ ≤ ⟦φ(v)⟧  for any B-formula φ(x)
-- (fulltext:2096-2097), and his proof of it is one sentence: "Finally, (vii)
-- is proved by a straightforward induction on the complexity of φ, something
-- we leave to the reader" (fulltext:2098). So the induction is written here
-- and not transcribed, and it is the only theorem in K4 that runs over the
-- whole of the object language at once.
--
-- The statement shipped is the simultaneous form at every free variable:
-- given two environments of names, the MEET of the Boolean equalities of
-- corresponding entries, met with the value of φ at the first environment,
-- lies below the value of φ at the second. Bell's one-variable statement is
-- `subst₁` below and is one instance of it. Three remarks on the form.
--
--  * It is an INEQUALITY and it is not an equation. The two directions are
--    genuinely different statements about a fixed pair of environments, and
--    only their conjunction is symmetric. What makes the induction close is
--    that the statement is proved for EVERY pair at once, so the reverse
--    direction is available at the swapped pair whenever a step needs it, and
--    exactly one step does: the implication node.
--  * The meet over the environment is FINITE. It is a fold over a vector of
--    known length, not a join over a class, so no infinitary law of any kind
--    is stated or used here (preamble rule R5).
--  * Every value fact this file consumes is a universal property and not an
--    equation naming a constructed join. That is the architecture's global
--    decision, and Track F found its second justification: a universal
--    property in an internal order is internally expressible while a
--    construction is not (REPORT-F.md section 3). The induction below is
--    stated in the same vocabulary it runs over, which is why the four
--    quantifier nodes cost three lines of order reasoning each and no
--    description operator appears anywhere in this file.
--
-- WHAT IT DOES NOT PROVE, AND THE ONE THING A CONSUMER WILL WANT AND NOT FIND.
--
-- Nothing here is about codes, readings, Δ₀ complexity, the host evaluator,
-- or a second algebra. No atomic value is defined, no atomic law is proved,
-- no value set is formed, no Separation instance is taken, and no completeness
-- field is in the telescope. Obstructions O1 and O2 are untouched.
--
-- The gap a consumer meets: Track D's `Congruent φ` (K4/AtomicLaws.agda:691)
-- is stated for a family `S → Pt B` over ARBITRARY ground codes, while the
-- compiled family runs over NAMES, `Fib IsName`. `subst-head` below is the
-- congruence at names and is exactly as strong as the induction gives.
-- Bridging it to Track D's bounded clauses needs the support of the bound to
-- consist of names, which is closure of a support under the recogniser, and
-- that is not a hypothesis of this track and is not assumed here.
--
-- THE RESIDUATION POINT, WHICH IS WHERE THIS TRACK'S ONLY REAL DIFFICULTY IS.
--
-- Track F measured that the unbounded quantifier nodes share one admission
-- record while the bounded ones do NOT, because their families are the
-- membership value MET with the body in one case and the membership value
-- IMPLYING the body in the other (REPORT-F.md section 5). The consequence for
-- this file is that the bounded universal case is RESIDUATION and not
-- distribution: the goal is a lower bound for a family of implications, so the
-- meet with the environment equality has to be pushed across an implication
-- by Track A's adjunction and never across a join by a distributive law.
-- Track A also refuted the architecture's printed `inf-residual` at an empty
-- family (REPORT-A.md section 3), so no residual law of the architecture's
-- spelling is used here either. The four quantifier cases below use
-- `⇒ᴮ-curry`, `⇒ᴮ-uncurry` and `⇒ᴮ-mp` and nothing else; those three are the
-- adjunction, they are Track A's, and they hold at every family including the
-- empty one because they mention no family at all.
--
-- Measured and recorded in REPORT-G.md: Track A's `sup-residual` and
-- `inf-residual` are not reachable from this file's hypotheses. They are
-- stated about `supᴮ X h` for a ground code X, and the value of a quantified
-- formula enters here only through its universal property, with no set named.
-- The residuation this track performs is the adjunction at that universal
-- property, which is the same argument with the construction removed.
--
-- HYPOTHESES, THE WHOLE LIST.
--
-- The structure, Extensionality and the path realization (these three only so
-- that K4.Implication can be applied for the adjunction); the carrier B, a
-- Lattice and a Complement; the name class; Track C's two atomic values;
-- five of Track D's atomic laws; Track F's value function and the fourteen
-- fields of its InterpLaws. No CodedComplete, no Separation, no Collection,
-- no PowerSet, no LEM, no weight, no support, no recursor, no formula code.
--
-- SCOPE CONTRACT. Records are generative, so this file declares NO record at
-- all. K4.Algebra is opened for the two record types and the point
-- vocabulary; K4.Implication is opened for the Boolean theory. Neither is
-- re-exported. Every consumer opens K4.Algebra itself, per Track A.

open import Base.Prelude
open import Base.Truth
open import FOL.ZFStructure using ( ZFStructure )
import OrdinaryProfile
import K4.Algebra
import K4.Implication

module K4.Substitution
  {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))
  (ext : OrdinaryProfile.Extensionality 𝒮)
  (paths : (x y : ZFStructure.S 𝒮)
         → (ZFStructure._≈ˢ_ 𝒮 x y) ≡ ((x ≡ y) , ZFStructure.isSetS 𝒮 x y))
  where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax
  using ( Term; Formula; con; var
        ; _∈̇_; _≐_; _∧̇_; _∨̇_; _⇒̇_; ⊥̇; ∃̇_; ∀̇_; ∀̇∈; ∃̇∈ )
open import FOL.ZFModel 𝒮 using ( _⊆ˢ_ )

open TruthAlgebra (hPropAlgebra ℓ)
open hPropStructure 𝒮

open K4.Algebra 𝒮
  using ( Pt; _≤ᴮ_; ≤ᴮ-refl; ⊆ˢ-trans; Lattice; Complement )

--------------------------------------------------------------------------------
-- The input language
--------------------------------------------------------------------------------

-- Parameter free formulas, Track F's `Src` character for character. Because
-- the constant domain is the empty type every term of an input formula is a
-- variable, which is why the induction below has six absurd clauses and no
-- clause about a constant. It is also why the bound of a bounded quantifier
-- is always a slot and the environment always hands it a NAME.

Src : ℕ → Type ℓ
Src k = Formula (⊥* {ℓ}) k

module Core
  (B  : S)
  (L  : Lattice B)
  (Cm : Complement B L)
  (IsName : S → Ω)
  where

  open K4.Implication 𝒮 ext paths B L Cm

  -- Track F's `Name` and `Env`, with `Fib IsName` written out. `Fib` is a
  -- plain definition (K4/ValueSets.agda:166), so the two spellings are the
  -- same type and no coercion is needed at the seam; K4/ProbeG.agda checks
  -- that against the real compiler rather than asserting it.

  Name : Type ℓ
  Name = Σ[ x ∈ S ] ⟨ IsName x ⟩

  Env : ℕ → Type ℓ
  Env k = Vec Name k

  ------------------------------------------------------------------------------
  -- A four move order toolkit
  ------------------------------------------------------------------------------

  -- Every proof in this file is a chain of order steps and it makes exactly
  -- these moves. They are named rather than inlined for R1's reason: the
  -- failure shape rule 1 describes is a bare reflexivity standing in for an
  -- unchanged endpoint, and here every endpoint of every step is an explicit
  -- argument, so nothing is left to unification.

  -- Commuting the two factors of a meet under an upper bound.

  ⊓-swap : (a b c : Pt B) → ⟨ (a ⊓ᴮ b) ≤ᴮ c ⟩ → ⟨ (b ⊓ᴮ a) ≤ᴮ c ⟩
  ⊓-swap a b c h = subst (λ z → ⟨ z ≤ᴮ c ⟩) (⊓-comm a b) h

  -- THE WORKHORSE. An element below two things is below anything their meet
  -- is below. Every substitution step in the induction is one `cut`: it is how
  -- a hypothesis of the shape "equality met with a value is below a value"
  -- gets applied to something that happens to be below both factors.

  cut : (x a b c : Pt B)
      → ⟨ x ≤ᴮ a ⟩ → ⟨ x ≤ᴮ b ⟩ → ⟨ (a ⊓ᴮ b) ≤ᴮ c ⟩ → ⟨ x ≤ᴮ c ⟩
  cut x a b c ha hb h = ⊆ˢ-trans (⊓-glb a b x ha hb) h

  -- The two projections, named at their endpoints.

  fstOf : (a b : Pt B) → ⟨ (a ⊓ᴮ b) ≤ᴮ a ⟩
  fstOf = ⊓-lb₁

  sndOf : (a b : Pt B) → ⟨ (a ⊓ᴮ b) ≤ᴮ b ⟩
  sndOf = ⊓-lb₂

  module Laws
    -- Track C's AtomicSemantics, the two value fields, flat. The spellings are
    -- the operator ones because nothing takes them in this module; Track C
    -- calls them eqᴬ and memᴬ only because a record field arrives as a
    -- projection into the enclosing scope.
    (_≈ᴮ_ : S → S → Pt B)
    (_∈ᴮ_ : S → S → Pt B)
    -- Track D's laws. Five of its thirteen, and no other.
    (≈ᴮ-refl  : (n : S) → (n ≈ᴮ n) ≡ ⊤ᴮ)
    (≈ᴮ-sym   : (m n : S) → (m ≈ᴮ n) ≡ (n ≈ᴮ m))
    (∈ᴮ-congˡ : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (m ∈ᴮ p)) ≤ᴮ (n ∈ᴮ p) ⟩)
    (∈ᴮ-congʳ : (m n p : S) → ⟨ ((n ≈ᴮ p) ⊓ᴮ (m ∈ᴮ n)) ≤ᴮ (m ∈ᴮ p) ⟩)
    (≈ᴮ-congˡ : (m n p : S) → ⟨ ((m ≈ᴮ n) ⊓ᴮ (m ≈ᴮ p)) ≤ᴮ (n ≈ᴮ p) ⟩)
    (≈ᴮ-congʳ : (m n p : S) → ⟨ ((n ≈ᴮ p) ⊓ᴮ (m ≈ᴮ n)) ≤ᴮ (m ≈ᴮ p) ⟩)
    -- Track F's compiled value and the fourteen fields of its InterpLaws,
    -- flat, in the record's own field order (K4/Compile.agda:1318-1356).
    (value : ∀ {k} → Src k → Env k → Pt B)
    (law-∈ : ∀ {k} (i j : Fin k) (ν : Env k)
           → value (var i ∈̇ var j) ν
           ≡ (fst (lookup i ν) ∈ᴮ fst (lookup j ν)))
    (law-≐ : ∀ {k} (i j : Fin k) (ν : Env k)
           → value (var i ≐ var j) ν
           ≡ (fst (lookup i ν) ≈ᴮ fst (lookup j ν)))
    (law-∧ : ∀ {k} (φ ψ : Src k) (ν : Env k)
           → value (φ ∧̇ ψ) ν ≡ (value φ ν ⊓ᴮ value ψ ν))
    (law-∨ : ∀ {k} (φ ψ : Src k) (ν : Env k)
           → value (φ ∨̇ ψ) ν ≡ (value φ ν ⊔ᴮ value ψ ν))
    (law-⇒ : ∀ {k} (φ ψ : Src k) (ν : Env k)
           → value (φ ⇒̇ ψ) ν ≡ (value φ ν ⇒ᴮ value ψ ν))
    (law-⊥ : ∀ {k} (ν : Env k) → value {k} ⊥̇ ν ≡ ⊥ᴮ)
    (law-∃-ub   : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
                → ⟨ value φ (σ ∷ ν) ≤ᴮ value (∃̇ φ) ν ⟩)
    (law-∃-lub  : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                → ((σ : Name) → ⟨ value φ (σ ∷ ν) ≤ᴮ c ⟩)
                → ⟨ value (∃̇ φ) ν ≤ᴮ c ⟩)
    (law-∀-lb   : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ : Name)
                → ⟨ value (∀̇ φ) ν ≤ᴮ value φ (σ ∷ ν) ⟩)
    (law-∀-glb  : ∀ {k} (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                → ((σ : Name) → ⟨ c ≤ᴮ value φ (σ ∷ ν) ⟩)
                → ⟨ c ≤ᴮ value (∀̇ φ) ν ⟩)
    (law-∃∈-ub  : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
                → ⟨ ((fst σ ∈ᴮ fst (lookup i ν)) ⊓ᴮ value φ (σ ∷ ν))
                    ≤ᴮ value (∃̇∈ (var i) φ) ν ⟩)
    (law-∃∈-lub : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                → ((σ : Name)
                   → ⟨ ((fst σ ∈ᴮ fst (lookup i ν)) ⊓ᴮ value φ (σ ∷ ν))
                       ≤ᴮ c ⟩)
                → ⟨ value (∃̇∈ (var i) φ) ν ≤ᴮ c ⟩)
    (law-∀∈-lb  : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (σ : Name)
                → ⟨ value (∀̇∈ (var i) φ) ν
                    ≤ᴮ ((fst σ ∈ᴮ fst (lookup i ν)) ⇒ᴮ value φ (σ ∷ ν)) ⟩)
    (law-∀∈-glb : ∀ {k} (i : Fin k) (φ : Src (suc k)) (ν : Env k) (c : Pt B)
                → ((σ : Name) → ⟨ c ≤ᴮ ((fst σ ∈ᴮ fst (lookup i ν))
                                         ⇒ᴮ value φ (σ ∷ ν)) ⟩)
                → ⟨ c ≤ᴮ value (∀̇∈ (var i) φ) ν ⟩)
    where

    ----------------------------------------------------------------------------
    -- Symmetry as an inequality, and what it costs
    ----------------------------------------------------------------------------

    -- Track C proved 1.17(iii) with no infinitary law and Track D restates it
    -- (REPORT-C.md section C1), so it is taken above as a hypothesis rather
    -- than reproved. What this file actually spends is weaker, and it is
    -- recorded here because it is a fact about the hypothesis ledger and not
    -- about the mathematics: the INEQUALITY half follows from 1.17(i) and the
    -- equality congruence alone. A consumer that holds those two and not the
    -- equation can drop `≈ᴮ-sym` and replace `envEq-sym` by `envEq-sym-≤`
    -- below; nothing else in the file changes.

    ≈ᴮ-sym-≤ : (m n : S) → ⟨ (m ≈ᴮ n) ≤ᴮ (n ≈ᴮ m) ⟩
    ≈ᴮ-sym-≤ m n =
      cut (m ≈ᴮ n) (m ≈ᴮ n) (m ≈ᴮ m) (n ≈ᴮ m)
          (≤ᴮ-refl (m ≈ᴮ n)) top (≈ᴮ-congˡ m n m)
      where
        top : ⟨ (m ≈ᴮ n) ≤ᴮ (m ≈ᴮ m) ⟩
        top = subst (λ w → ⟨ (m ≈ᴮ n) ≤ᴮ w ⟩)
                    (sym (≈ᴮ-refl m)) (⊤-greatest (m ≈ᴮ n))

    ----------------------------------------------------------------------------
    -- The environment equality
    ----------------------------------------------------------------------------

    -- The architecture prints this as `meetᴮ (zipWith (λ σ τ → fst σ ≈ᴮ fst τ)
    -- ν μ)`. There is no vector meet and no `zipWith` in play here and neither
    -- is needed: the environments have a known length, so the meet is a fold
    -- and it is written as one. That is the difference between this and every
    -- join in K4, and it is why rule R5 never comes near this file.

    envEq : ∀ {k} → Env k → Env k → Pt B
    envEq []      []      = ⊤ᴮ
    envEq (σ ∷ ν) (τ ∷ μ) = (fst σ ≈ᴮ fst τ) ⊓ᴮ envEq ν μ

    -- Reading one entry back out of the fold. This is the only place the
    -- vector structure is used in the atomic cases.

    envEq-lookup : ∀ {k} (i : Fin k) (ν μ : Env k)
                 → ⟨ envEq ν μ ≤ᴮ (fst (lookup i ν) ≈ᴮ fst (lookup i μ)) ⟩
    envEq-lookup zero    (σ ∷ ν) (τ ∷ μ) = fstOf (fst σ ≈ᴮ fst τ) (envEq ν μ)
    envEq-lookup (suc i) (σ ∷ ν) (τ ∷ μ) =
      ⊆ˢ-trans (sndOf (fst σ ≈ᴮ fst τ) (envEq ν μ)) (envEq-lookup i ν μ)

    -- Symmetry of the fold, entrywise, by two single argument congruences. No
    -- `cong₂`, so no propositionality component is left as a metavariable.

    envEq-sym : ∀ {k} (ν μ : Env k) → envEq ν μ ≡ envEq μ ν
    envEq-sym []      []      = refl
    envEq-sym (σ ∷ ν) (τ ∷ μ) =
        cong (λ w → w ⊓ᴮ envEq ν μ) (≈ᴮ-sym (fst σ) (fst τ))
      ∙ cong (λ w → (fst τ ≈ᴮ fst σ) ⊓ᴮ w) (envEq-sym ν μ)

    -- The same fact without the equation, from `≈ᴮ-sym-≤`. It is what the
    -- induction really needs, and it is shipped so that the ledger claim above
    -- is checkable rather than asserted.

    envEq-sym-≤ : ∀ {k} (ν μ : Env k) → ⟨ envEq ν μ ≤ᴮ envEq μ ν ⟩
    envEq-sym-≤ []      []      = ≤ᴮ-refl ⊤ᴮ
    envEq-sym-≤ (σ ∷ ν) (τ ∷ μ) =
      ⊓-glb (fst τ ≈ᴮ fst σ) (envEq μ ν) ((fst σ ≈ᴮ fst τ) ⊓ᴮ envEq ν μ)
        (⊆ˢ-trans (fstOf (fst σ ≈ᴮ fst τ) (envEq ν μ))
                  (≈ᴮ-sym-≤ (fst σ) (fst τ)))
        (⊆ˢ-trans (sndOf (fst σ ≈ᴮ fst τ) (envEq ν μ)) (envEq-sym-≤ ν μ))

    -- Reflexivity of the fold, from 1.17(i). Used only to strip the trailing
    -- ⊤ᴮ out of `subst-head`.

    envEq-refl : ∀ {k} (ν : Env k) → envEq ν ν ≡ ⊤ᴮ
    envEq-refl []      = refl
    envEq-refl (σ ∷ ν) =
        cong (λ w → w ⊓ᴮ envEq ν ν) (≈ᴮ-refl (fst σ))
      ∙ cong (λ w → ⊤ᴮ ⊓ᴮ w) (envEq-refl ν)
      ∙ ⊓-⊤ ⊤ᴮ

    -- Going under a binder. A name substituted for itself contributes the top
    -- element, by 1.17(i), so the environment equality survives the extension
    -- of both environments by the SAME name. This is the step every quantifier
    -- node takes and the only thing any of them needs about the new slot.

    envEq-cons : ∀ {k} (σ : Name) (ν μ : Env k)
               → ⟨ envEq ν μ ≤ᴮ envEq (σ ∷ ν) (σ ∷ μ) ⟩
    envEq-cons σ ν μ =
      ⊓-glb (fst σ ≈ᴮ fst σ) (envEq ν μ) (envEq ν μ) top (≤ᴮ-refl (envEq ν μ))
      where
        top : ⟨ envEq ν μ ≤ᴮ (fst σ ≈ᴮ fst σ) ⟩
        top = subst (λ w → ⟨ envEq ν μ ≤ᴮ w ⟩)
                    (sym (≈ᴮ-refl (fst σ))) (⊤-greatest (envEq ν μ))

    ----------------------------------------------------------------------------
    -- Bell 1.17(vii)
    ----------------------------------------------------------------------------

    -- The induction. Ten constructor clauses and six absurd term clauses, by
    -- structural recursion on the formula with BOTH environments universally
    -- quantified, which is what makes the implication node close.
    --
    -- The reason the motive carries both environments rather than fixing one:
    -- the implication node needs the inductive hypothesis for the ANTECEDENT
    -- read backwards, from the second environment to the first, because an
    -- implication is antitone in its antecedent. Reading it backwards is
    -- reading it at the swapped pair, and that is available only if the
    -- statement quantifies over pairs. This is the one place in the proof
    -- where the environment equality has to be turned around, and it is where
    -- `envEq-sym` is spent.
    --
    -- Which laws each group of clauses spends, so the ledger is readable off
    -- the proof and not off a comment:
    --
    --   ∈̇  ≐     : law-∈ / law-≐ and the four atomic congruences.
    --   ∧̇        : the lattice alone.
    --   ∨̇        : the adjunction and ⊔-lub. NOT ⊓-⊔-dist; see below.
    --   ⇒̇        : the adjunction, ⇒ᴮ-mp, and envEq-sym.
    --   ⊥̇        : ⊓-lb₂.
    --   ∃̇  ∃̇∈   : the adjunction and the node's lub clause.
    --   ∀̇  ∀̇∈   : the node's glb clause, and for ∀̇∈ the adjunction twice.

    subst-law : ∀ {k} (φ : Src k) (ν μ : Env k)
              → ⟨ (envEq ν μ ⊓ᴮ value φ ν) ≤ᴮ value φ μ ⟩

    -- The two atomic clauses. Bell's (v) and (vi) are exactly (vii) at the two
    -- atomic relations, and Track D proved all four orientations
    -- (K4/AtomicLaws.agda:461, :474, :482, :487), so each clause is two cuts:
    -- substitute the first argument, then the second.

    subst-law (var i ∈̇ var j) ν μ =
      subst (λ w → ⟨ (envEq ν μ ⊓ᴮ w) ≤ᴮ value (var i ∈̇ var j) μ ⟩)
            (sym (law-∈ i j ν))
        (subst (λ w → ⟨ X ≤ᴮ w ⟩) (sym (law-∈ i j μ)) core)
      where
        mi mj ni nj : S
        mi = fst (lookup i ν)
        mj = fst (lookup j ν)
        ni = fst (lookup i μ)
        nj = fst (lookup j μ)

        X : Pt B
        X = envEq ν μ ⊓ᴮ (mi ∈ᴮ mj)

        xe : ⟨ X ≤ᴮ envEq ν μ ⟩
        xe = fstOf (envEq ν μ) (mi ∈ᴮ mj)

        xa : ⟨ X ≤ᴮ (mi ∈ᴮ mj) ⟩
        xa = sndOf (envEq ν μ) (mi ∈ᴮ mj)

        x₁ : ⟨ X ≤ᴮ (ni ∈ᴮ mj) ⟩
        x₁ = cut X (mi ≈ᴮ ni) (mi ∈ᴮ mj) (ni ∈ᴮ mj)
               (⊆ˢ-trans xe (envEq-lookup i ν μ)) xa (∈ᴮ-congˡ mi ni mj)

        core : ⟨ X ≤ᴮ (ni ∈ᴮ nj) ⟩
        core = cut X (mj ≈ᴮ nj) (ni ∈ᴮ mj) (ni ∈ᴮ nj)
                 (⊆ˢ-trans xe (envEq-lookup j ν μ)) x₁ (∈ᴮ-congʳ ni mj nj)

    subst-law (var i ∈̇ con ()) ν μ
    subst-law (con () ∈̇ u) ν μ

    subst-law (var i ≐ var j) ν μ =
      subst (λ w → ⟨ (envEq ν μ ⊓ᴮ w) ≤ᴮ value (var i ≐ var j) μ ⟩)
            (sym (law-≐ i j ν))
        (subst (λ w → ⟨ X ≤ᴮ w ⟩) (sym (law-≐ i j μ)) core)
      where
        mi mj ni nj : S
        mi = fst (lookup i ν)
        mj = fst (lookup j ν)
        ni = fst (lookup i μ)
        nj = fst (lookup j μ)

        X : Pt B
        X = envEq ν μ ⊓ᴮ (mi ≈ᴮ mj)

        xe : ⟨ X ≤ᴮ envEq ν μ ⟩
        xe = fstOf (envEq ν μ) (mi ≈ᴮ mj)

        xa : ⟨ X ≤ᴮ (mi ≈ᴮ mj) ⟩
        xa = sndOf (envEq ν μ) (mi ≈ᴮ mj)

        x₁ : ⟨ X ≤ᴮ (ni ≈ᴮ mj) ⟩
        x₁ = cut X (mi ≈ᴮ ni) (mi ≈ᴮ mj) (ni ≈ᴮ mj)
               (⊆ˢ-trans xe (envEq-lookup i ν μ)) xa (≈ᴮ-congˡ mi ni mj)

        core : ⟨ X ≤ᴮ (ni ≈ᴮ nj) ⟩
        core = cut X (mj ≈ᴮ nj) (ni ≈ᴮ mj) (ni ≈ᴮ nj)
                 (⊆ˢ-trans xe (envEq-lookup j ν μ)) x₁ (≈ᴮ-congʳ ni mj nj)

    subst-law (var i ≐ con ()) ν μ
    subst-law (con () ≐ u) ν μ

    -- Conjunction, Bell (1.8). The lattice alone: the environment equality is
    -- available to both halves because a meet is idempotent as an upper bound,
    -- which is what `cut` says.

    subst-law (φ ∧̇ ψ) ν μ =
      subst (λ w → ⟨ (envEq ν μ ⊓ᴮ w) ≤ᴮ value (φ ∧̇ ψ) μ ⟩)
            (sym (law-∧ φ ψ ν))
        (subst (λ w → ⟨ X ≤ᴮ w ⟩) (sym (law-∧ φ ψ μ)) core)
      where
        a b a' b' : Pt B
        a  = value φ ν
        b  = value ψ ν
        a' = value φ μ
        b' = value ψ μ

        X : Pt B
        X = envEq ν μ ⊓ᴮ (a ⊓ᴮ b)

        xe : ⟨ X ≤ᴮ envEq ν μ ⟩
        xe = fstOf (envEq ν μ) (a ⊓ᴮ b)

        xa : ⟨ X ≤ᴮ a ⟩
        xa = ⊆ˢ-trans (sndOf (envEq ν μ) (a ⊓ᴮ b)) (fstOf a b)

        xb : ⟨ X ≤ᴮ b ⟩
        xb = ⊆ˢ-trans (sndOf (envEq ν μ) (a ⊓ᴮ b)) (sndOf a b)

        core : ⟨ X ≤ᴮ (a' ⊓ᴮ b') ⟩
        core = ⊓-glb a' b' X
                 (cut X (envEq ν μ) a a' xe xa (subst-law φ ν μ))
                 (cut X (envEq ν μ) b b' xe xb (subst-law ψ ν μ))

    -- Disjunction, Bell (1.11). The obvious route is the finite distributive
    -- law `⊓-⊔-dist`, which IS available as a field of Complement. It is not
    -- used. Residuation is shorter and it is the same move the three other
    -- non trivial nodes make: push the environment equality across the join by
    -- currying it away, bound each disjunct separately, and uncurry. Recorded
    -- because a reader who expects distributivity here should be told that the
    -- choice was deliberate and that nothing infinitary is hiding in it.

    subst-law (φ ∨̇ ψ) ν μ =
      subst (λ w → ⟨ (envEq ν μ ⊓ᴮ w) ≤ᴮ value (φ ∨̇ ψ) μ ⟩)
            (sym (law-∨ φ ψ ν))
        (subst (λ w → ⟨ (envEq ν μ ⊓ᴮ (a ⊔ᴮ b)) ≤ᴮ w ⟩)
               (sym (law-∨ φ ψ μ)) core)
      where
        a b a' b' e c : Pt B
        a  = value φ ν
        b  = value ψ ν
        a' = value φ μ
        b' = value ψ μ
        e  = envEq ν μ
        c  = a' ⊔ᴮ b'

        ha : ⟨ a ≤ᴮ (e ⇒ᴮ c) ⟩
        ha = ⇒ᴮ-curry a e c
               (⊓-swap e a c (⊆ˢ-trans (subst-law φ ν μ) (⊔-ub₁ a' b')))

        hb : ⟨ b ≤ᴮ (e ⇒ᴮ c) ⟩
        hb = ⇒ᴮ-curry b e c
               (⊓-swap e b c (⊆ˢ-trans (subst-law ψ ν μ) (⊔-ub₂ a' b')))

        core : ⟨ (e ⊓ᴮ (a ⊔ᴮ b)) ≤ᴮ c ⟩
        core = ⊓-swap (a ⊔ᴮ b) e c
                 (⇒ᴮ-uncurry (a ⊔ᴮ b) e c (⊔-lub a b (e ⇒ᴮ c) ha hb))

    -- Implication, Bell (1.12). THE step that fixes the shape of the whole
    -- induction. An implication is antitone in its antecedent, so the value at
    -- the second environment is reached only by carrying the antecedent BACK
    -- to the first environment, which is the inductive hypothesis for φ read
    -- at the swapped pair. Modus ponens then fires at the first environment
    -- and the consequent travels forward by the inductive hypothesis for ψ.
    -- Bell's own proof says none of this, because he leaves (vii) to the
    -- reader; this is where the reader's work is.

    subst-law (φ ⇒̇ ψ) ν μ =
      subst (λ w → ⟨ (envEq ν μ ⊓ᴮ w) ≤ᴮ value (φ ⇒̇ ψ) μ ⟩)
            (sym (law-⇒ φ ψ ν))
        (subst (λ w → ⟨ (envEq ν μ ⊓ᴮ (a ⇒ᴮ b)) ≤ᴮ w ⟩)
               (sym (law-⇒ φ ψ μ)) core)
      where
        a b a' b' e : Pt B
        a  = value φ ν
        b  = value ψ ν
        a' = value φ μ
        b' = value ψ μ
        e  = envEq ν μ

        X : Pt B
        X = (e ⊓ᴮ (a ⇒ᴮ b)) ⊓ᴮ a'

        xe : ⟨ X ≤ᴮ e ⟩
        xe = ⊆ˢ-trans (fstOf (e ⊓ᴮ (a ⇒ᴮ b)) a') (fstOf e (a ⇒ᴮ b))

        ximp : ⟨ X ≤ᴮ (a ⇒ᴮ b) ⟩
        ximp = ⊆ˢ-trans (fstOf (e ⊓ᴮ (a ⇒ᴮ b)) a') (sndOf e (a ⇒ᴮ b))

        xa' : ⟨ X ≤ᴮ a' ⟩
        xa' = sndOf (e ⊓ᴮ (a ⇒ᴮ b)) a'

        -- The antecedent carried backwards, at the swapped pair.
        xa : ⟨ X ≤ᴮ a ⟩
        xa = cut X (envEq μ ν) a' a
               (subst (λ w → ⟨ X ≤ᴮ w ⟩) (envEq-sym ν μ) xe)
               xa' (subst-law φ μ ν)

        xb : ⟨ X ≤ᴮ b ⟩
        xb = cut X (a ⇒ᴮ b) a b ximp xa (⇒ᴮ-mp a b)

        core : ⟨ (e ⊓ᴮ (a ⇒ᴮ b)) ≤ᴮ (a' ⇒ᴮ b') ⟩
        core = ⇒ᴮ-curry (e ⊓ᴮ (a ⇒ᴮ b)) a' b'
                 (cut X e b b' xe xb (subst-law ψ ν μ))

    -- Falsity, Bell (1.13). Nothing to substitute into.

    subst-law {k} ⊥̇ ν μ =
      subst (λ w → ⟨ (envEq ν μ ⊓ᴮ w) ≤ᴮ value {k} ⊥̇ μ ⟩)
            (sym (law-⊥ ν))
        (subst (λ w → ⟨ (envEq ν μ ⊓ᴮ ⊥ᴮ) ≤ᴮ w ⟩)
               (sym (law-⊥ μ)) (sndOf (envEq ν μ) ⊥ᴮ))

    -- The unbounded existential, Bell (1.9). RESIDUATION and not a
    -- distributive step: the value is a least upper bound and nothing else is
    -- known about it, so the environment equality is curried out of the way,
    -- the lub clause reduces the goal to one name at a time, and the inductive
    -- hypothesis fires under the binder with the SAME name on both sides.

    subst-law (∃̇ φ) ν μ =
      ⊓-swap (value (∃̇ φ) ν) e (value (∃̇ φ) μ)
        (⇒ᴮ-uncurry (value (∃̇ φ) ν) e (value (∃̇ φ) μ) h)
      where
        e : Pt B
        e = envEq ν μ

        h : ⟨ value (∃̇ φ) ν ≤ᴮ (e ⇒ᴮ value (∃̇ φ) μ) ⟩
        h = law-∃-lub φ ν (e ⇒ᴮ value (∃̇ φ) μ) step
          where
            step : (σ : Name)
                 → ⟨ value φ (σ ∷ ν) ≤ᴮ (e ⇒ᴮ value (∃̇ φ) μ) ⟩
            step σ = ⇒ᴮ-curry (value φ (σ ∷ ν)) e (value (∃̇ φ) μ) inner
              where
                Y : Pt B
                Y = value φ (σ ∷ ν) ⊓ᴮ e

                ycons : ⟨ Y ≤ᴮ envEq (σ ∷ ν) (σ ∷ μ) ⟩
                ycons = ⊆ˢ-trans (sndOf (value φ (σ ∷ ν)) e)
                                 (envEq-cons σ ν μ)

                inner : ⟨ Y ≤ᴮ value (∃̇ φ) μ ⟩
                inner = ⊆ˢ-trans
                  (cut Y (envEq (σ ∷ ν) (σ ∷ μ)) (value φ (σ ∷ ν))
                       (value φ (σ ∷ μ)) ycons
                       (fstOf (value φ (σ ∷ ν)) e)
                       (subst-law φ (σ ∷ ν) (σ ∷ μ)))
                  (law-∃-ub φ μ σ)

    -- The unbounded universal, Bell (1.10). The dual, and it needs no
    -- currying: the goal is already a lower bound for the family at the second
    -- environment, so the glb clause applies directly and each instance is the
    -- lb clause at the first environment followed by the inductive hypothesis.

    subst-law (∀̇ φ) ν μ = law-∀-glb φ μ X step
      where
        e : Pt B
        e = envEq ν μ

        X : Pt B
        X = e ⊓ᴮ value (∀̇ φ) ν

        step : (σ : Name) → ⟨ X ≤ᴮ value φ (σ ∷ μ) ⟩
        step σ = cut X (envEq (σ ∷ ν) (σ ∷ μ)) (value φ (σ ∷ ν))
                     (value φ (σ ∷ μ))
                     (⊆ˢ-trans (fstOf e (value (∀̇ φ) ν)) (envEq-cons σ ν μ))
                     (⊆ˢ-trans (sndOf e (value (∀̇ φ) ν)) (law-∀-lb φ ν σ))
                     (subst-law φ (σ ∷ ν) (σ ∷ μ))

    -- The bounded existential, Bell's restricted ∃x ∈ u. Track F measured that
    -- this node and the bounded universal do NOT share an admission record,
    -- because the family here is the membership value MET with the body while
    -- there it is the membership value IMPLYING the body (REPORT-F.md section
    -- 5). The consequence is visible in the two proofs: this one substitutes
    -- into the membership factor in the FORWARD direction, by (vi), and the
    -- universal one substitutes into it BACKWARDS.

    subst-law (∃̇∈ (var i) φ) ν μ =
      ⊓-swap (value (∃̇∈ (var i) φ) ν) e (value (∃̇∈ (var i) φ) μ)
        (⇒ᴮ-uncurry (value (∃̇∈ (var i) φ) ν) e (value (∃̇∈ (var i) φ) μ) h)
      where
        e : Pt B
        e = envEq ν μ

        mi ni : S
        mi = fst (lookup i ν)
        ni = fst (lookup i μ)

        h : ⟨ value (∃̇∈ (var i) φ) ν ≤ᴮ (e ⇒ᴮ value (∃̇∈ (var i) φ) μ) ⟩
        h = law-∃∈-lub i φ ν (e ⇒ᴮ value (∃̇∈ (var i) φ) μ) step
          where
            step : (σ : Name)
                 → ⟨ ((fst σ ∈ᴮ mi) ⊓ᴮ value φ (σ ∷ ν))
                     ≤ᴮ (e ⇒ᴮ value (∃̇∈ (var i) φ) μ) ⟩
            step σ =
              ⇒ᴮ-curry ((fst σ ∈ᴮ mi) ⊓ᴮ value φ (σ ∷ ν)) e
                       (value (∃̇∈ (var i) φ) μ) inner
              where
                Y : Pt B
                Y = ((fst σ ∈ᴮ mi) ⊓ᴮ value φ (σ ∷ ν)) ⊓ᴮ e

                ye : ⟨ Y ≤ᴮ e ⟩
                ye = sndOf ((fst σ ∈ᴮ mi) ⊓ᴮ value φ (σ ∷ ν)) e

                ymem : ⟨ Y ≤ᴮ (fst σ ∈ᴮ mi) ⟩
                ymem = ⊆ˢ-trans
                         (fstOf ((fst σ ∈ᴮ mi) ⊓ᴮ value φ (σ ∷ ν)) e)
                         (fstOf (fst σ ∈ᴮ mi) (value φ (σ ∷ ν)))

                ybody : ⟨ Y ≤ᴮ value φ (σ ∷ ν) ⟩
                ybody = ⊆ˢ-trans
                          (fstOf ((fst σ ∈ᴮ mi) ⊓ᴮ value φ (σ ∷ ν)) e)
                          (sndOf (fst σ ∈ᴮ mi) (value φ (σ ∷ ν)))

                ymem' : ⟨ Y ≤ᴮ (fst σ ∈ᴮ ni) ⟩
                ymem' = cut Y (mi ≈ᴮ ni) (fst σ ∈ᴮ mi) (fst σ ∈ᴮ ni)
                          (⊆ˢ-trans ye (envEq-lookup i ν μ)) ymem
                          (∈ᴮ-congʳ (fst σ) mi ni)

                ybody' : ⟨ Y ≤ᴮ value φ (σ ∷ μ) ⟩
                ybody' = cut Y (envEq (σ ∷ ν) (σ ∷ μ)) (value φ (σ ∷ ν))
                           (value φ (σ ∷ μ))
                           (⊆ˢ-trans ye (envEq-cons σ ν μ)) ybody
                           (subst-law φ (σ ∷ ν) (σ ∷ μ))

                inner : ⟨ Y ≤ᴮ value (∃̇∈ (var i) φ) μ ⟩
                inner = ⊆ˢ-trans
                  (⊓-glb (fst σ ∈ᴮ ni) (value φ (σ ∷ μ)) Y ymem' ybody')
                  (law-∃∈-ub i φ μ σ)

    subst-law (∃̇∈ (con ()) φ) ν μ

    -- The bounded universal. THE RESIDUATION CASE, and the only clause whose
    -- shape is forced rather than chosen. The node's family is a family of
    -- IMPLICATIONS, so the goal after the glb clause is that a meet lies below
    -- an implication, and the only way in is to curry the antecedent into the
    -- hypothesis. Once it is there the membership value must travel BACKWARDS,
    -- from the second environment to the first, before the lb clause at the
    -- first environment can be used at all. That is why this clause reads the
    -- entry of the environment equality in the reversed orientation, which is
    -- the one and only use of `≈ᴮ-sym-≤`, and why no distributive step exists
    -- that would shorten it.

    subst-law (∀̇∈ (var i) φ) ν μ = law-∀∈-glb i φ μ X step
      where
        e : Pt B
        e = envEq ν μ

        W : Pt B
        W = value (∀̇∈ (var i) φ) ν

        X : Pt B
        X = e ⊓ᴮ W

        mi ni : S
        mi = fst (lookup i ν)
        ni = fst (lookup i μ)

        step : (σ : Name) → ⟨ X ≤ᴮ ((fst σ ∈ᴮ ni) ⇒ᴮ value φ (σ ∷ μ)) ⟩
        step σ = ⇒ᴮ-curry X (fst σ ∈ᴮ ni) (value φ (σ ∷ μ)) inner
          where
            Z : Pt B
            Z = X ⊓ᴮ (fst σ ∈ᴮ ni)

            ze : ⟨ Z ≤ᴮ e ⟩
            ze = ⊆ˢ-trans (fstOf X (fst σ ∈ᴮ ni)) (fstOf e W)

            zw : ⟨ Z ≤ᴮ W ⟩
            zw = ⊆ˢ-trans (fstOf X (fst σ ∈ᴮ ni)) (sndOf e W)

            zmem' : ⟨ Z ≤ᴮ (fst σ ∈ᴮ ni) ⟩
            zmem' = sndOf X (fst σ ∈ᴮ ni)

            -- The entry read in the reversed orientation.
            zeq : ⟨ Z ≤ᴮ (ni ≈ᴮ mi) ⟩
            zeq = ⊆ˢ-trans ze
                    (⊆ˢ-trans (envEq-lookup i ν μ) (≈ᴮ-sym-≤ mi ni))

            zmem : ⟨ Z ≤ᴮ (fst σ ∈ᴮ mi) ⟩
            zmem = cut Z (ni ≈ᴮ mi) (fst σ ∈ᴮ ni) (fst σ ∈ᴮ mi)
                     zeq zmem' (∈ᴮ-congʳ (fst σ) ni mi)

            zbody : ⟨ Z ≤ᴮ value φ (σ ∷ ν) ⟩
            zbody = cut Z W (fst σ ∈ᴮ mi) (value φ (σ ∷ ν)) zw zmem
                      (⇒ᴮ-uncurry W (fst σ ∈ᴮ mi) (value φ (σ ∷ ν))
                                  (law-∀∈-lb i φ ν σ))

            inner : ⟨ Z ≤ᴮ value φ (σ ∷ μ) ⟩
            inner = cut Z (envEq (σ ∷ ν) (σ ∷ μ)) (value φ (σ ∷ ν))
                      (value φ (σ ∷ μ))
                      (⊆ˢ-trans ze (envEq-cons σ ν μ)) zbody
                      (subst-law φ (σ ∷ ν) (σ ∷ μ))

    subst-law (∀̇∈ (con ()) φ) ν μ

    ----------------------------------------------------------------------------
    -- The one variable forms
    ----------------------------------------------------------------------------

    -- Substitution at the head slot, with an arbitrary tail. This is the form
    -- a quantifier node consumes: it says the compiled family over names is
    -- congruent for Boolean equality, which is the hypothesis of Bell's
    -- Corollary 1.18 and of Track D's `bounded-∃-ub` and `bounded-∀-lb`
    -- (K4/AtomicLaws.agda:699, :743).
    --
    -- The gap named in the header, restated where it bites: Track D's
    -- `Congruent` quantifies over ARBITRARY ground codes and this quantifies
    -- over names. The two meet only when the support of the bound consists of
    -- names, which is closure of a support under the recogniser. That is not a
    -- hypothesis here and nothing below assumes it.

    subst-head : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ τ : Name)
               → ⟨ ((fst σ ≈ᴮ fst τ) ⊓ᴮ value φ (σ ∷ ν))
                   ≤ᴮ value φ (τ ∷ ν) ⟩
    subst-head φ ν σ τ =
      ⊆ˢ-trans
        (⊓ᴮ-mono (fst σ ≈ᴮ fst τ) (envEq (σ ∷ ν) (τ ∷ ν))
                 (value φ (σ ∷ ν)) (value φ (σ ∷ ν))
                 pad (≤ᴮ-refl (value φ (σ ∷ ν))))
        (subst-law φ (σ ∷ ν) (τ ∷ ν))
      where
        tail : ⟨ (fst σ ≈ᴮ fst τ) ≤ᴮ envEq ν ν ⟩
        tail = subst (λ w → ⟨ (fst σ ≈ᴮ fst τ) ≤ᴮ w ⟩)
                     (sym (envEq-refl ν)) (⊤-greatest (fst σ ≈ᴮ fst τ))

        pad : ⟨ (fst σ ≈ᴮ fst τ) ≤ᴮ envEq (σ ∷ ν) (τ ∷ ν) ⟩
        pad = ⊓-glb (fst σ ≈ᴮ fst τ) (envEq ν ν) (fst σ ≈ᴮ fst τ)
                    (≤ᴮ-refl (fst σ ≈ᴮ fst τ)) tail

    -- Bell 1.17(vii) as the architecture prints it, at one free variable.

    subst₁ : (φ : Src 1) (σ τ : Name)
           → ⟨ ((fst σ ≈ᴮ fst τ) ⊓ᴮ value φ (σ ∷ []))
               ≤ᴮ value φ (τ ∷ []) ⟩
    subst₁ φ σ τ = subst-head φ [] σ τ

    -- The curried reading, for a consumer that has to place a substituted
    -- value under an implication. This is `≈ᴮ-mono-∈`'s shape at a compound
    -- formula (K4/AtomicLaws.agda:495) and it is where the adjunction is spent
    -- once more rather than at every call site.

    subst-mono : ∀ {k} (φ : Src (suc k)) (ν : Env k) (σ τ : Name)
               → ⟨ (fst σ ≈ᴮ fst τ)
                   ≤ᴮ (value φ (σ ∷ ν) ⇒ᴮ value φ (τ ∷ ν)) ⟩
    subst-mono φ ν σ τ =
      ⇒ᴮ-curry (fst σ ≈ᴮ fst τ) (value φ (σ ∷ ν)) (value φ (τ ∷ ν))
               (subst-head φ ν σ τ)
