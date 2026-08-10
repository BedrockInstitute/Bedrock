# The recursion assembly, generic in the value

<!--en-->
One assembly serves the two recursion chapters. The assembly is the
approximation pipeline. It reads a recorded value, proves the values are
unique, reads the graph, and writes the graph from a table. The value
property, the entries predicate, and the step lemmas are parameters. The
sites keep the mathematics that the parameters cannot express.
<!--/-->

```agda
{-# OPTIONS --cubical --safe --guardedness #-}

open import Base.Prelude
open import Base.Truth
open import Base.Classical using ( LEM )

module L.RecAssembly {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where

open import FOL.ZFStructure using ( module hPropStructure )
open import FOL.Syntax using ( Formula; _∧̇_; _⇒̇_; ∃̇_; ∀̇_ )
import FOL.Absoluteness
open import V.Hierarchy {ℓ} using ( 𝒮ᵥ; ∈-induction )
open import V.Coding {ℓ} using ( pr )
open import L.Constructible {ℓ}
  using ( 𝒮ʟ; isL; isL-trans; IsOrd )
open import L.Ordinal {ℓ} using ( mem-ord )
open import L.Coding.Model {ℓ}
  using ( domAt; domAt-in; domAt-out; domAt-intro; appAt; appAt-adequate
        ; prAtL; prAtL-adequate )
import Cubical.HITs.PropositionalTruncation as PT
open PT using ( ∥_∥₁; ∣_∣₁ )
open import Cubical.HITs.CumulativeHierarchy.Base using ( V; _∈_ )

open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))
open hPropStructure 𝒮ʟ

module AbsL = FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans
open AbsL renaming ( _⊨ᵐ_ to _⊨_ )

private
  sh2 : ∀ {n} → Fin n → Fin (suc (suc n))
  sh2 i = suc (suc i)

Values₀ : (P : V ℓ → S → Type (ℓ-suc ℓ)) → S → V ℓ → Type (ℓ-suc ℓ)
Values₀ P h B = (c z : S) → ⟨ fst c ∈ B ⟩
              → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → P (fst c) z

Domain₀ : S → V ℓ → Type (ℓ-suc ℓ)
Domain₀ h B = (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩ → ⟨ fst c ∈ B ⟩

Entries₀ : ((h : S) (B : V ℓ) (c : S) → ⟨ fst c ∈ B ⟩ → Type (ℓ-suc ℓ))
         → S → V ℓ → Type (ℓ-suc ℓ)
Entries₀ entered h B = (c : S) (c∈ : ⟨ fst c ∈ B ⟩) → entered h B c c∈

ApproxAt₀ : (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
          → ∀ {n} → Fin n → Fin n → Formula S n
ApproxAt₀ Step f a = domAt f a
                   ∧̇ ∀̇ (∀̇ ( appAt (sh2 f) (suc zero) zero
                           ⇒̇ Step zero (suc zero) (sh2 f) ))

GraphAt₀ : (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
         → ∀ {n} → Fin n → Fin n → Formula S n
GraphAt₀ Step w b = ∃̇ (ApproxAt₀ Step zero (suc b) ∧̇ Step (suc w) (suc b) zero)

module Assembly
  (P : V ℓ → S → Type (ℓ-suc ℓ))
  (P-prop : (c : V ℓ) (z : S) → isProp (P c z))
  (entered : (h : S) (B : V ℓ) (c : S) → ⟨ fst c ∈ B ⟩ → Type (ℓ-suc ℓ))
  (entered-res : (h : S) (B C : V ℓ) (e : S) (e∈B : ⟨ fst e ∈ B ⟩) (e∈C : ⟨ fst e ∈ C ⟩)
               → entered h B e e∈B → entered h C e e∈C)
  (uniq : (c : V ℓ) (x y : S) → P c x → P c y → x ≡ y)
  (Step : ∀ {n} → Fin n → Fin n → Fin n → Formula S n)
  (step : ∀ {n} (v b f : Fin n) (γ : S ^ n) (ob : IsOrd (fst (lookup b γ)))
        → Values₀ P (lookup f γ) (fst (lookup b γ))
        → Entries₀ entered (lookup f γ) (fst (lookup b γ))
        → ⟨ γ ⊨ Step v b f ⟩ → P (fst (lookup b γ)) (lookup v γ))
  (step-back : ∀ {n} (v b f : Fin n) (γ : S ^ n) (ob : IsOrd (fst (lookup b γ)))
             → Values₀ P (lookup f γ) (fst (lookup b γ))
             → Entries₀ entered (lookup f γ) (fst (lookup b γ))
             → P (fst (lookup b γ)) (lookup v γ) → ⟨ γ ⊨ Step v b f ⟩)
  (to-entered₀ : ∀ {n} (f a : Fin n) (γ : S ^ n)
               → (h : ⟨ γ ⊨ ApproxAt₀ Step f a ⟩) (oa : IsOrd (fst (lookup a γ)))
               → (u : V ℓ) (hu : ⟨ isL u ⟩) (ou : IsOrd u)
               → (u∈a : ⟨ u ∈ fst (lookup a γ) ⟩)
               → ((t : V ℓ) → ⟨ t ∈ u ⟩ → ⟨ isL t ⟩ → IsOrd t
                  → (z : S) → ⟨ pr t (fst z) ∈ fst (lookup f γ) ⟩ → P t z)
               → Entries₀ entered (lookup f γ) u)
  (to-entered₂ : ∀ {n} (w b : Fin n) (γ : S ^ n) (f : S)
               → (ha : ⟨ (f ∷ γ) ⊨ ApproxAt₀ Step zero (suc b) ⟩)
               → (ob : IsOrd (fst (lookup b γ)))
               → Values₀ P f (fst (lookup b γ))
               → Entries₀ entered f (fst (lookup b γ)))
  (to-exists : ∀ {n} (w b : Fin n) (γ : S ^ n) (h : S)
             → (ob : IsOrd (fst (lookup b γ)))
             → Entries₀ entered h (fst (lookup b γ))
             → (c : S) → ⟨ fst c ∈ fst (lookup b γ) ⟩
             → ∥ Σ[ z ∈ S ] ⟨ pr (fst c) (fst z) ∈ fst h ⟩ ∥₁)
  where

  Values : S → V ℓ → Type (ℓ-suc ℓ)
  Values = Values₀ P

  Domain : S → V ℓ → Type (ℓ-suc ℓ)
  Domain = Domain₀

  Entries : S → V ℓ → Type (ℓ-suc ℓ)
  Entries = Entries₀ entered

  ApproxAt : ∀ {n} → Fin n → Fin n → Formula S n
  ApproxAt = ApproxAt₀ Step

  GraphAt : ∀ {n} → Fin n → Fin n → Formula S n
  GraphAt = GraphAt₀ Step

  module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
    ApproxAt-dom : ⟨ γ ⊨ ApproxAt f a ⟩ → Domain (lookup f γ) (fst (lookup a γ))
    ApproxAt-dom h = domAt-out f a γ (h .fst)

    ApproxAt-value : ⟨ γ ⊨ ApproxAt f a ⟩ → (c : S)
                   → ⟨ fst c ∈ fst (lookup a γ) ⟩
                   → ∥ (Σ[ z ∈ S ] ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩) ∥₁
    ApproxAt-value h = domAt-in f a γ (h .fst)

    ApproxAt-step : ⟨ γ ⊨ ApproxAt f a ⟩ → (c z : S)
                  → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                  → ⟨ (z ∷ c ∷ γ) ⊨ Step zero (suc zero) (sh2 f) ⟩
    ApproxAt-step h c z p = h .snd c z
      (subst ⟨_⟩ (sym (appAt-adequate (sh2 f) (suc zero) zero (z ∷ c ∷ γ))) p)

    ApproxAt-in : ⟨ γ ⊨ domAt f a ⟩
                → ((c z : S) → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩
                   → ⟨ (z ∷ c ∷ γ) ⊨ Step zero (suc zero) (sh2 f) ⟩)
                → ⟨ γ ⊨ ApproxAt f a ⟩
    ApproxAt-in hd hs = hd , λ c z p → hs c z
      (subst ⟨_⟩ (appAt-adequate (sh2 f) (suc zero) zero (z ∷ c ∷ γ)) p)

  module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
    GraphOf : Type (ℓ-suc ℓ)
    GraphOf = Σ[ f ∈ S ] ( ⟨ (f ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
                         × ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ )

    Graph-in : (f : S) → ⟨ (f ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
             → ⟨ (f ∷ γ) ⊨ Step (suc w) (suc b) zero ⟩ → ⟨ γ ⊨ GraphAt w b ⟩
    Graph-in f ha hs = ∣ f , (ha , hs) ∣₁

    Graph-out : ⟨ γ ⊨ GraphAt w b ⟩ → ∥ GraphOf ∥₁
    Graph-out h = h

  module _ {n : ℕ} (f a : Fin n) (γ : S ^ n) where
    private
      Value : V ℓ → Type (ℓ-suc ℓ)
      Value u = ⟨ isL u ⟩ → IsOrd u → (z : S)
              → ⟨ pr u (fst z) ∈ fst (lookup f γ) ⟩ → P u z

    approx-val : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
               → (c : S) → IsOrd (fst c) → (z : S)
               → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩ → P (fst c) z
    approx-val h oa c oc = ∈-induction {P = Value} go (fst c) (snd c) oc
      where
      go : (u : V ℓ) → ((t : V ℓ) → ⟨ t ∈ u ⟩ → Value t) → Value u
      go u IH hu ou z p = step zero (suc zero) (sh2 f) (z ∷ d ∷ γ) ou vals ents
        (ApproxAt-step f a γ h d z p)
        where
        d : S
        d = u , hu
        u∈a : ⟨ u ∈ fst (lookup a γ) ⟩
        u∈a = ApproxAt-dom f a γ h d z p
        vals : Values (lookup f γ) u
        vals c y c∈ q = IH (fst c) c∈ (snd c) c-oc y q
          where
          c-oc : IsOrd (fst c)
          c-oc = mem-ord {A = u} ou (fst c) c∈
        ents : Entries (lookup f γ) u
        ents = to-entered₀ f a γ h oa u hu ou u∈a IH

    approx-uniq : ⟨ γ ⊨ ApproxAt f a ⟩ → IsOrd (fst (lookup a γ))
                → (c : S) → IsOrd (fst c) → (x y : S)
                → ⟨ pr (fst c) (fst x) ∈ fst (lookup f γ) ⟩
                → ⟨ pr (fst c) (fst y) ∈ fst (lookup f γ) ⟩ → x ≡ y
    approx-uniq h oa c oc x y p q = uniq (fst c) x y
      (approx-val h oa c oc x p) (approx-val h oa c oc y q)

  module _ {n : ℕ} (w b : Fin n) (γ : S ^ n) where
    graph-only : ⟨ γ ⊨ GraphAt w b ⟩ → IsOrd (fst (lookup b γ))
               → P (fst (lookup b γ)) (lookup w γ)
    graph-only h ob = PT.rec (P-prop (fst (lookup b γ)) (lookup w γ)) read
      (Graph-out w b γ h)
      where
      read : GraphOf w b γ → P (fst (lookup b γ)) (lookup w γ)
      read (f , (ha , hs)) = step (suc w) (suc b) zero (f ∷ γ) ob vals ents hs
        where
        vals : Values f (fst (lookup b γ))
        vals c z c∈ p = approx-val zero (suc b) (f ∷ γ) ha ob c
          (mem-ord {A = fst (lookup b γ)} ob (fst c) c∈) z p
        ents : Entries f (fst (lookup b γ))
        ents = to-entered₂ w b γ f ha ob vals

    graph-table : (h : S) → IsOrd (fst (lookup b γ))
                → Values h (fst (lookup b γ)) → Entries h (fst (lookup b γ))
                → Domain h (fst (lookup b γ))
                → P (fst (lookup b γ)) (lookup w γ) → ⟨ γ ⊨ GraphAt w b ⟩
    graph-table h ob vals ents dom sp = Graph-in w b γ h approx
      (step-back (suc w) (suc b) zero (h ∷ γ) ob vals ents sp)
      where
      onDom : (c : S)
            → (⟨ ⋁ S (λ z → pr (fst c) (fst z) ∈ fst h) ⟩
               → ⟨ fst c ∈ fst (lookup b γ) ⟩)
            × (⟨ fst c ∈ fst (lookup b γ) ⟩
               → ⟨ ⋁ S (λ z → pr (fst c) (fst z) ∈ fst h) ⟩)
      onDom c = (λ hz → PT.rec (snd (fst c ∈ fst (lookup b γ)))
                    (λ { (z , p) → dom c z p }) hz)
              , (λ c∈ → to-exists w b γ h ob ents c c∈)

      onStep : (c z : S) → ⟨ pr (fst c) (fst z) ∈ fst h ⟩
             → ⟨ (z ∷ c ∷ h ∷ γ) ⊨ Step zero (suc zero) (suc (suc zero)) ⟩
      onStep c z p = step-back zero (suc zero) (suc (suc zero)) (z ∷ c ∷ h ∷ γ)
        oc vals' ents' (vals c z c∈ p)
        where
        c∈ : ⟨ fst c ∈ fst (lookup b γ) ⟩
        c∈ = dom c z p
        oc : IsOrd (fst c)
        oc = mem-ord {A = fst (lookup b γ)} ob (fst c) c∈
        vals' : Values h (fst c)
        vals' e t _ q = vals e t (dom e t q) q
        ents' : Entries h (fst c)
        ents' e e∈ = entered-res h (fst (lookup b γ)) (fst c) e
          (ob .fst {x = fst c} {y = fst e} e∈ c∈) e∈
          (ents e (ob .fst {x = fst c} {y = fst e} e∈ c∈))

      approx : ⟨ (h ∷ γ) ⊨ ApproxAt zero (suc b) ⟩
      approx = ApproxAt-in zero (suc b) (h ∷ γ)
        (domAt-intro zero (suc b) (h ∷ γ) onDom) onStep

  PairGraphAt : ∀ {n} → Fin n → Fin n → Formula S n
  PairGraphAt e c = ∃̇ (prAtL (suc e) (suc c) zero ∧̇ GraphAt zero (suc c))

  module _ {n : ℕ} (e c : Fin n) (γ : S ^ n)
           (φ : Formula S n) (qφ : φ ≡ PairGraphAt e c) where
    PairOf : Type (ℓ-suc ℓ)
    PairOf = Σ[ z ∈ S ] ( (fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z))
                        × ⟨ (z ∷ γ) ⊨ GraphAt zero (suc c) ⟩ )

    PairGraph-in : (z : S) → fst (lookup e γ) ≡ pr (fst (lookup c γ)) (fst z)
                 → ⟨ (z ∷ γ) ⊨ GraphAt zero (suc c) ⟩ → ⟨ γ ⊨ φ ⟩
    PairGraph-in z q hg = subst (λ ψ → ⟨ γ ⊨ ψ ⟩) (sym qφ)
      ∣ z , (subst ⟨_⟩
        (sym (prAtL-adequate (suc e) (suc c) zero (z ∷ γ))) q , hg) ∣₁

    PairGraph-out : ⟨ γ ⊨ φ ⟩ → ∥ PairOf ∥₁
    PairGraph-out h = PT.map
      (λ { (z , (hq , hg)) →
        z , (subst ⟨_⟩ (prAtL-adequate (suc e) (suc c) zero (z ∷ γ)) hq , hg) })
      (subst (λ ψ → ⟨ γ ⊨ ψ ⟩) qφ h)
```
