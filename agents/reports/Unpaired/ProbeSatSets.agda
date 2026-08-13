{-# OPTIONS --cubical --safe --guardedness #-}
-- ProbeSatSets: the [L3.31-R5-G2p] D-1 probe on the full-switch wall
-- candidate.  The classical engine of the full switch builds, for each
-- formula phi with k free variables, the satisfaction SET T_phi (the set of
-- k-tuples from U satisfying phi) as a MEMBER of the rud closure, by
-- induction on phi.  Satisfaction stays external and only certifies.  This
-- probe prices the mini fragment over an abstract P-h interface (nothing
-- concrete unfolds): the membership atom var_i in var_j as an F7-slice of
-- the tuple space, negation as complement within the tuple space via F1,
-- and the UNBOUNDED existential as the domain/projection of T_psi one
-- arity down via F6.  Adequacy is proved in both directions per clause.
--
-- Probe-local, untracked, exempt from make check and from the literate
-- format.  No postulates, no holes, no TERMINATING pragmas.
--
-- Tuple convention (deliberate, see report): k-tuples are LEFT-nested
-- pairs, (x1,...,xk) = pr (pr x1 x2) ... xk, so the tuple space is
-- U^k = F2 (F2 ... (F2 U U) ...) U, the existential on the LAST free
-- variable is F6's native tail projection, and the atom on the FIRST two
-- coordinates is the F7-slice at the head pair.  The delivered F3/F4
-- convention (right-nested) is an assembly-time re-association, priced in
-- the extrapolation.

open import Base.Prelude
open import Base.Truth

module ProbeSatSets {ℓ : Level} where

  open import FOL.ZFStructure using ( module hPropStructure )
  open import V.Hierarchy {ℓ} using ( 𝒮ᵥ )
  open import V.Coding {ℓ} using ( pr; pr-inj )
  import Cubical.HITs.PropositionalTruncation as PT
  open PT using ( ∣_∣₁; ∥_∥₁; squash₁ )
  import Cubical.Data.Empty as Empty
  open import Cubical.HITs.CumulativeHierarchy.Base using ( V )
  open import Cubical.HITs.CumulativeHierarchy.Properties
    using ( _≡ₕ_ )
  open import L.Rud.Ops {ℓ}
    using ( F1; F1-spec; F2; F2-read; F2-write
          ; F6; F6-read; F6-write; F7; F7-read; F7-write )
  open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
  open hPropStructure 𝒮ᵥ

  -- The sixteen-op index, mirroring L.Rud.Step's Op16 (the closure fact
  -- below is the Switch.Closure Jrud shape over this index, taken as an
  -- abstract parameter: the probe never imports the concrete tower).
  data Op16 : Type where
    f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : Op16

  -- The abstract interface, P-h style: a module over U, its transitivity,
  -- and the closure interface.  InJ is abstract; Jrud is the sixteen-op
  -- closure fact; the Fof-f* equations pin the committed operations to
  -- their tags (the assembly obligation is exactly Switch.Closure's
  -- J-F1..J-F7 at Jset-rud).  U itself is in J; members of U are in J via
  -- the transitivity of the closed set, derived below.
  module SatProbe
    (U : V ℓ)
    (Utrans : (x y : V ℓ) → ⟨ x ∈ˢ y ⟩ → ⟨ y ∈ˢ U ⟩ → ⟨ x ∈ˢ U ⟩)
    (InJ : V ℓ → Type (ℓ-suc ℓ))
    (Jtrans : (a b : V ℓ) → InJ b → ⟨ a ∈ˢ b ⟩ → InJ a)
    (Fof : Op16 → V ℓ → V ℓ → V ℓ)
    (Jrud : (i : Op16) (a b : V ℓ) → InJ a → InJ b → InJ (Fof i a b))
    (Fof-f1 : (a b : V ℓ) → Fof f1 a b ≡ F1 a b)
    (Fof-f2 : (a b : V ℓ) → Fof f2 a b ≡ F2 a b)
    (Fof-f6 : (a b : V ℓ) → Fof f6 a b ≡ F6 a b)
    (Fof-f7 : (a b : V ℓ) → Fof f7 a b ≡ F7 a b)
    (JU : InJ U)
    where

    -- The five per-op closure arms, exactly Switch.Closure's shape.
    JF1 : (a b : V ℓ) → InJ a → InJ b → InJ (F1 a b)
    JF1 a b ha hb = subst InJ (Fof-f1 a b) (Jrud f1 a b ha hb)

    JF2 : (a b : V ℓ) → InJ a → InJ b → InJ (F2 a b)
    JF2 a b ha hb = subst InJ (Fof-f2 a b) (Jrud f2 a b ha hb)

    JF6 : (a b : V ℓ) → InJ a → InJ b → InJ (F6 a b)
    JF6 a b ha hb = subst InJ (Fof-f6 a b) (Jrud f6 a b ha hb)

    JF7 : (a b : V ℓ) → InJ a → InJ b → InJ (F7 a b)
    JF7 a b ha hb = subst InJ (Fof-f7 a b) (Jrud f7 a b ha hb)

    -- Members of U lie in the closed set (used by the real G2's parameter
    -- atoms; carried here because the interface pins it).
    UmemInJ : (a : V ℓ) → ⟨ a ∈ˢ U ⟩ → InJ a
    UmemInJ a a∈U = Jtrans a U JU a∈U

    -- The tuple spaces, left-nested: U^2 = F2 U U, U^3 = F2 U^2 U.
    U² : V ℓ
    U² = F2 U U

    U³ : V ℓ
    U³ = F2 U² U

    hU² : InJ U²
    hU² = JF2 U U JU JU

    hU³ : InJ U³
    hU³ = JF2 U² U hU² JU

    -- The membership characterization, stated ONCE (R-36 style, through the
    -- sealed F2's exported read/write lemmas) and consumed by every clause.
    U²-char-in : (m : V ℓ) → ⟨ m ∈ˢ U² ⟩
              → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                   (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
    U²-char-in = F2-read U U

    U²-char-out : (m : V ℓ)
               → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                    (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ m ≡ₕ pr a b ⟩) ∥₁
               → ⟨ m ∈ˢ U² ⟩
    U²-char-out = F2-write U U

    U³-char-in : (m : V ℓ) → ⟨ m ∈ˢ U³ ⟩
              → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
                   (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
                  × ⟨ m ≡ₕ pr (pr a b) c ⟩) ∥₁
    U³-char-in m h = PT.rec squash₁ go (F2-read U² U m h)
      where
      go : Σ[ z ∈ V ℓ ] Σ[ c ∈ V ℓ ]
             (⟨ z ∈ˢ U² ⟩ × ⟨ c ∈ˢ U ⟩ × ⟨ m ≡ₕ pr z c ⟩)
         → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
              (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
             × ⟨ m ≡ₕ pr (pr a b) c ⟩) ∥₁
      go (z , c , z∈ , c∈ , m≡) = PT.rec squash₁ go' (U²-char-in z z∈)
        where
        go' : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ z ≡ₕ pr a b ⟩)
            → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
                 (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
                × ⟨ m ≡ₕ pr (pr a b) c ⟩) ∥₁
        go' (a , b , a∈ , b∈ , z≡) = ∣ a , b , c , (a∈ , b∈ , c∈ , m≡') ∣₁
          where
          m≡' : ⟨ m ≡ₕ pr (pr a b) c ⟩
          m≡' = m≡ ∙ cong (λ t → pr t c) z≡

    U³-char-out : (m : V ℓ)
               → ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
                    (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
                   × ⟨ m ≡ₕ pr (pr a b) c ⟩) ∥₁
               → ⟨ m ∈ˢ U³ ⟩
    U³-char-out m h = F2-write U² U m (PT.rec squash₁ go h)
      where
      go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
             (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
            × ⟨ m ≡ₕ pr (pr a b) c ⟩)
         → ∥ Σ[ z ∈ V ℓ ] Σ[ c ∈ V ℓ ]
              (⟨ z ∈ˢ U² ⟩ × ⟨ c ∈ˢ U ⟩ × ⟨ m ≡ₕ pr z c ⟩) ∥₁
      go (a , b , c , a∈ , b∈ , c∈ , m≡) =
        ∣ pr a b , c
        , (U²-char-out (pr a b) (∣ a , b , (a∈ , b∈ , refl) ∣₁) , c∈ , m≡) ∣₁

    -- The mini fragment: arity-3 formulas (atom x1 in x2, negation) and
    -- arity-2 formulas (unbounded existential over the last free variable,
    -- negation).  The external satisfaction face: Type-valued, only
    -- certifies; the existential quantifies over U itself, which is exactly
    -- the clause the Delta-0 route never had.
    data Fm3 : Type where
      atom : Fm3
      neg : Fm3 → Fm3

    data Fm2 : Type where
      ex : Fm3 → Fm2
      neg₂ : Fm2 → Fm2

    Sat3 : Fm3 → V ℓ → V ℓ → V ℓ → Type (ℓ-suc ℓ)
    Sat3 atom a b c = ⟨ a ∈ˢ b ⟩
    Sat3 (neg φ) a b c = Sat3 φ a b c → Empty.⊥

    Sat2 : Fm2 → V ℓ → V ℓ → Type (ℓ-suc ℓ)
    Sat2 (ex φ) a b = Σ[ c ∈ V ℓ ] (⟨ c ∈ˢ U ⟩ × Sat3 φ a b c)
    Sat2 (neg₂ φ) a b = Sat2 φ a b → Empty.⊥

    -- The satisfaction sets, built from the committed operations only.
    T₃ : Fm3 → V ℓ
    T₃ atom = F2 (F7 U U) U
    T₃ (neg φ) = F1 U³ (T₃ φ)

    T₂ : Fm2 → V ℓ
    T₂ (ex φ) = F6 (T₃ φ) (T₃ φ)
    T₂ (neg₂ φ) = F1 U² (T₂ φ)

    -- THE ENGINE: every satisfaction set is a member of the closure.
    hT₃ : (φ : Fm3) → InJ (T₃ φ)
    hT₃ atom = JF2 (F7 U U) U (JF7 U U JU JU) JU
    hT₃ (neg φ) = JF1 U³ (T₃ φ) hU³ (hT₃ φ)

    hT₂ : (φ : Fm2) → InJ (T₂ φ)
    hT₂ (ex φ) = JF6 (T₃ φ) (T₃ φ) (hT₃ φ) (hT₃ φ)
    hT₂ (neg₂ φ) = JF1 U² (T₂ φ) hU² (hT₂ φ)

    -- Adequacy: m in T_phi iff the external satisfaction holds at the
    -- decoded tuple.  The decode is existential-shaped (the tuple's
    -- coordinates come from the read lemmas); the carrier-level statement
    -- with explicit truncation is lesson I-4's first formulation.
    Dec3 : (φ : Fm3) → V ℓ → Type (ℓ-suc ℓ)
    Dec3 φ m = ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
                 (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
                × Sat3 φ a b c × ⟨ m ≡ₕ pr (pr a b) c ⟩) ∥₁

    Dec2 : (φ : Fm2) → V ℓ → Type (ℓ-suc ℓ)
    Dec2 φ m = ∥ Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                 (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × Sat2 φ a b
                × ⟨ m ≡ₕ pr a b ⟩) ∥₁

    -- Satisfaction respects decode equality (pure Type-level transports,
    -- no induction on the formula; used to identify the two decodes of one
    -- tuple in the negation clause).
    Sat3-cong : (φ : Fm3) (a b c a' b' c' : V ℓ)
              → a ≡ a' → b ≡ b' → c ≡ c'
              → Sat3 φ a' b' c' → Sat3 φ a b c
    Sat3-cong φ a b c a' b' c' a≡ b≡ c≡ sat =
      subst (λ x → Sat3 φ a b x) (sym c≡)
        (subst (λ x → Sat3 φ a x c') (sym b≡)
          (subst (λ x → Sat3 φ x b' c') (sym a≡) sat))

    Sat2-cong : (φ : Fm2) (a b a' b' : V ℓ)
              → a ≡ a' → b ≡ b' → Sat2 φ a' b' → Sat2 φ a b
    Sat2-cong φ a b a' b' a≡ b≡ sat =
      subst (λ x → Sat2 φ a x) (sym b≡)
        (subst (λ x → Sat2 φ x b') (sym a≡) sat)

    mutual
      -- ATOM: T_3(atom) = F2 (F7 U U) U, the F7-slice at the head pair.
      adeq3-in : (φ : Fm3) (m : V ℓ) → ⟨ m ∈ˢ T₃ φ ⟩ → Dec3 φ m
      adeq3-in atom m h = PT.rec squash₁ go (F2-read (F7 U U) U m h)
        where
        go : Σ[ z ∈ V ℓ ] Σ[ c ∈ V ℓ ]
               (⟨ z ∈ˢ F7 U U ⟩ × ⟨ c ∈ˢ U ⟩ × ⟨ m ≡ₕ pr z c ⟩)
           → Dec3 atom m
        go (z , c , z∈ , c∈ , m≡) = PT.rec squash₁ go' (F7-read U U z z∈)
          where
          go' : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                  (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ a ∈ˢ b ⟩ × ⟨ z ≡ₕ pr a b ⟩)
              → Dec3 atom m
          go' (a , b , a∈ , b∈ , a∈b , z≡) =
            ∣ a , b , c , (a∈ , b∈ , c∈ , a∈b , m≡') ∣₁
            where
            m≡' : ⟨ m ≡ₕ pr (pr a b) c ⟩
            m≡' = m≡ ∙ cong (λ t → pr t c) z≡

      -- NEGATION: complement within the tuple space via F1.
      adeq3-in (neg φ) m h = go (F1-spec U³ (T₃ φ) m .fst h)
        where
        go : Σ[ _ ∈ ⟨ m ∈ˢ U³ ⟩ ] (⟨ m ∈ˢ T₃ φ ⟩ → Empty.⊥)
           → Dec3 (neg φ) m
        go (m∈U³ , m∉) = PT.rec squash₁ go' (U³-char-in m m∈U³)
          where
          go' : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
                  (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
                 × ⟨ m ≡ₕ pr (pr a b) c ⟩)
              → Dec3 (neg φ) m
          go' (a , b , c , a∈ , b∈ , c∈ , m≡) =
            ∣ a , b , c , (a∈ , b∈ , c∈ , nsat , m≡) ∣₁
            where
            nsat : Sat3 φ a b c → Empty.⊥
            nsat sat = m∉ (adeq3-out φ m
              (∣ a , b , c , (a∈ , b∈ , c∈ , sat , m≡) ∣₁))

      adeq3-out : (φ : Fm3) (m : V ℓ) → Dec3 φ m → ⟨ m ∈ˢ T₃ φ ⟩
      adeq3-out atom m h = PT.rec (snd (m ∈ˢ T₃ atom)) go h
        where
        go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
               (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
              × Sat3 atom a b c × ⟨ m ≡ₕ pr (pr a b) c ⟩)
           → ⟨ m ∈ˢ T₃ atom ⟩
        go (a , b , c , a∈ , b∈ , c∈ , a∈b , m≡) =
          F2-write (F7 U U) U m (∣ pr a b , c , (z∈ , c∈ , m≡) ∣₁)
          where
          z∈ : ⟨ pr a b ∈ˢ F7 U U ⟩
          z∈ = F7-write U U (pr a b) (∣ a , b , (a∈ , b∈ , a∈b , refl) ∣₁)

      adeq3-out (neg φ) m h = F1-spec U³ (T₃ φ) m .snd (m∈U³ , m∉)
        where
        m∈U³ : ⟨ m ∈ˢ U³ ⟩
        m∈U³ = U³-char-out m (PT.rec squash₁
          (λ { (a , b , c , a∈ , b∈ , c∈ , nsat , m≡) →
               ∣ a , b , c , (a∈ , b∈ , c∈ , m≡) ∣₁ }) h)
        m∉ : ⟨ m ∈ˢ T₃ φ ⟩ → Empty.⊥
        m∉ m∈ = PT.rec Empty.isProp⊥ outer h
          where
          outer : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
                    (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
                   × (Sat3 φ a b c → Empty.⊥) × ⟨ m ≡ₕ pr (pr a b) c ⟩)
                → Empty.⊥
          outer (a , b , c , a∈ , b∈ , c∈ , nsat , m≡) =
            PT.rec Empty.isProp⊥ inner (adeq3-in φ m m∈)
            where
            inner : Σ[ a' ∈ V ℓ ] Σ[ b' ∈ V ℓ ] Σ[ c' ∈ V ℓ ]
                      (⟨ a' ∈ˢ U ⟩ × ⟨ b' ∈ˢ U ⟩ × ⟨ c' ∈ˢ U ⟩
                     × Sat3 φ a' b' c' × ⟨ m ≡ₕ pr (pr a' b') c' ⟩)
                  → Empty.⊥
            inner (a' , b' , c' , _ , _ , _ , sat' , m≡') =
              nsat (Sat3-cong φ a b c a' b' c'
                (pr-inj (pr-inj eq .fst) .fst)
                (pr-inj (pr-inj eq .fst) .snd)
                (pr-inj eq .snd) sat')
              where
              eq : pr (pr a b) c ≡ pr (pr a' b') c'
              eq = sym m≡ ∙ m≡'

      -- UNBOUNDED EXISTENTIAL: T_2(ex phi) = F6 (T_3 phi), the tail
      -- projection one arity down.
      adeq2-in : (φ : Fm2) (m : V ℓ) → ⟨ m ∈ˢ T₂ φ ⟩ → Dec2 φ m
      adeq2-in (ex φ) m h = PT.rec squash₁ go (F6-read (T₃ φ) (T₃ φ) m h)
        where
        go : Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
               (⟨ pr u v ∈ˢ T₃ φ ⟩ × ⟨ m ≡ₕ u ⟩) → Dec2 (ex φ) m
        go (u , v , pruv∈ , m≡u) = PT.rec squash₁ go' (adeq3-in φ (pr u v) pruv∈)
          where
          go' : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ] Σ[ c ∈ V ℓ ]
                  (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ c ∈ˢ U ⟩
                 × Sat3 φ a b c × ⟨ pr u v ≡ₕ pr (pr a b) c ⟩)
              → Dec2 (ex φ) m
          go' (a , b , c , a∈ , b∈ , c∈ , sat , pruv≡) =
            ∣ a , b , (a∈ , b∈ , (c , c∈ , sat) , m≡ab) ∣₁
            where
            m≡ab : ⟨ m ≡ₕ pr a b ⟩
            m≡ab = m≡u ∙ pr-inj pruv≡ .fst

      -- NEGATION at arity 2, the same F1 machinery one level down.
      adeq2-in (neg₂ φ) m h = go (F1-spec U² (T₂ φ) m .fst h)
        where
        go : Σ[ _ ∈ ⟨ m ∈ˢ U² ⟩ ] (⟨ m ∈ˢ T₂ φ ⟩ → Empty.⊥)
           → Dec2 (neg₂ φ) m
        go (m∈U² , m∉) = PT.rec squash₁ go' (U²-char-in m m∈U²)
          where
          go' : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                  (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × ⟨ m ≡ₕ pr a b ⟩)
              → Dec2 (neg₂ φ) m
          go' (a , b , a∈ , b∈ , m≡) =
            ∣ a , b , (a∈ , b∈ , nsat , m≡) ∣₁
            where
            nsat : Sat2 φ a b → Empty.⊥
            nsat sat = m∉ (adeq2-out φ m
              (∣ a , b , (a∈ , b∈ , sat , m≡) ∣₁))

      adeq2-out : (φ : Fm2) (m : V ℓ) → Dec2 φ m → ⟨ m ∈ˢ T₂ φ ⟩
      adeq2-out (ex φ) m h =
        F6-write (T₃ φ) (T₃ φ) m (PT.rec squash₁ go h)
        where
        go : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
               (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩ × Sat2 (ex φ) a b
              × ⟨ m ≡ₕ pr a b ⟩)
           → ∥ Σ[ u ∈ V ℓ ] Σ[ v ∈ V ℓ ]
                (⟨ pr u v ∈ˢ T₃ φ ⟩ × ⟨ m ≡ₕ u ⟩) ∥₁
        go (a , b , a∈ , b∈ , (c , c∈ , sat) , m≡) =
          ∣ pr a b , c , (t₃∈ , m≡) ∣₁
          where
          t₃∈ : ⟨ pr (pr a b) c ∈ˢ T₃ φ ⟩
          t₃∈ = adeq3-out φ (pr (pr a b) c)
                  (∣ a , b , c , (a∈ , b∈ , c∈ , sat , refl) ∣₁)

      adeq2-out (neg₂ φ) m h = F1-spec U² (T₂ φ) m .snd (m∈U² , m∉)
        where
        m∈U² : ⟨ m ∈ˢ U² ⟩
        m∈U² = U²-char-out m (PT.rec squash₁
          (λ { (a , b , a∈ , b∈ , nsat , m≡) →
               ∣ a , b , (a∈ , b∈ , m≡) ∣₁ }) h)
        m∉ : ⟨ m ∈ˢ T₂ φ ⟩ → Empty.⊥
        m∉ m∈ = PT.rec Empty.isProp⊥ outer h
          where
          outer : Σ[ a ∈ V ℓ ] Σ[ b ∈ V ℓ ]
                    (⟨ a ∈ˢ U ⟩ × ⟨ b ∈ˢ U ⟩
                   × (Sat2 φ a b → Empty.⊥) × ⟨ m ≡ₕ pr a b ⟩)
                → Empty.⊥
          outer (a , b , a∈ , b∈ , nsat , m≡) =
            PT.rec Empty.isProp⊥ inner (adeq2-in φ m m∈)
            where
            inner : Σ[ a' ∈ V ℓ ] Σ[ b' ∈ V ℓ ]
                      (⟨ a' ∈ˢ U ⟩ × ⟨ b' ∈ˢ U ⟩
                     × Sat2 φ a' b' × ⟨ m ≡ₕ pr a' b' ⟩)
                  → Empty.⊥
            inner (a' , b' , _ , _ , sat' , m≡') =
              nsat (Sat2-cong φ a b a' b'
                (pr-inj eq .fst) (pr-inj eq .snd) sat')
              where
              eq : pr a b ≡ pr a' b'
              eq = sym m≡ ∙ m≡'
