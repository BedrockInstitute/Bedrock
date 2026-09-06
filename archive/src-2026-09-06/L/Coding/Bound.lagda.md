# The limit-closure apparatus of the bound chapter (retired 2026-09-06)

From `src/L/Coding/Bound.lagda.md`.  `module BoundOver` took five facts
about a stage function; only two of them, `T-mono` and `T-ord`, are read
by anything the tree consumes.  The other three (`T-out`, `T-pr`,
`T-trans`), the fiber type `At`, the step-operator module `Iter` with
its unsupplied `powIter` hypothesis, the two L-tower adapters
`Lset-out'` and `Lset-trans'` that existed only to feed `T-out` and
`T-trans`, and `module PowIter` that instantiated `Iter` at the L step,
all went with them.  `module Iter` and `module PowIter` were already
empty of declarations when this was cut: a previous prune had removed
their bodies and left the hypothesis.

THE TREE HAD NO CONSUMER FOR ANY OF IT.  The one importer of
`L.Coding.Bound` is `src/L/GCH/HierDescribe.lagda.md:28`, which takes
`module Bound`, and `HierDescribe.lagda.md:669` instantiates it as
`module B = Bound lam ord succ ∅∈λ using ( num∈λ )`.  `num∈λ` needs
`#∈Tλ`, which needs `#∈λ`, `T-mono` and `T-ord` and nothing else.  The
`module Bound` a name sweep finds in `L/Axioms/Power.lagda.md:128` and
`L/Choice/Order.lagda.md:681` are unrelated definitions with the same
spelling.

The comment on `Iter` recorded, before the cut, that `powIter` "is a
HYPOTHESIS here and it has no supplier; `src/` assumes the same fact
twice, as `DefOK` and as `PowOK`."  That is still true of the tree.

```agda
module BoundOver
  (T : S → S)
  (T-out : (α x : S) → ⟨ x ∈ˢ T α ⟩
         → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ T (sucV δ) ⟩) ∥₁)
  (T-mono : {α β : S} → ⟨ β ∈ˢ α ⟩ → {x : S} → ⟨ x ∈ˢ T β ⟩ → ⟨ x ∈ˢ T α ⟩)
  (T-pr : (σ x y : S) → ⟨ x ∈ˢ T σ ⟩ → ⟨ y ∈ˢ T σ ⟩
        → ⟨ pr x y ∈ˢ T (sucV (sucV σ)) ⟩)
  (T-trans : (α : S) {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ T α ⟩ → ⟨ y ∈ˢ T α ⟩)
  (T-ord : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ T (sucV δ) ⟩)
  (lam : S) (ordλ : IsOrd lam)
  (succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where

  At : S → Type (ℓ-suc ℓ)
  At x = Σ[ δ ∈ S ] (⟨ δ ∈ˢ lam ⟩ × ⟨ x ∈ˢ T (sucV δ) ⟩)

  -- The step operator at a limit, reduced to ONE fact about the step at a
  -- successor: the step of a stage member lands a bounded number of stages
  -- above it.  The fact is a HYPOTHESIS here and it has no supplier; `src/`
  -- assumes the same fact twice, as `DefOK` and as `PowOK`.
  module Iter (D : S → S)
    (powIter : (δ y : S) → ⟨ y ∈ˢ T δ ⟩
             → ∥ Σ[ k ∈ ℕ ] ⟨ D y ∈ˢ T (sucIter k δ) ⟩ ∥₁) where

Lset-out′ : (α x : S) → ⟨ x ∈ˢ Lset α ⟩
          → ∥ Σ[ δ ∈ S ] (⟨ δ ∈ˢ α ⟩ × ⟨ x ∈ˢ Lset (sucV δ) ⟩) ∥₁
Lset-out′ α x hx = PT.map
  (λ { (δ , (δ∈ , h)) → δ , (δ∈ , subst (λ w → ⟨ x ∈ˢ w ⟩)
         (sym (Lset-suc δ)) h) })
  (Lset-out α x hx)

Lset-trans′ : (α : S) {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ Lset α ⟩ → ⟨ y ∈ˢ Lset α ⟩
Lset-trans′ α {x} {y} = layer-trans (Lset-layer α) {x = x} {y = y}

  -- The reduction at the L step operator.  `powIter` stays a hypothesis:
  -- MEASURED, nothing in `src/` proves it, and `L.Coding.Powerset` and
  -- `L.Coding.Sequence` each assume it under another name.
  module PowIter
    (powIter : (δ y : S) → ⟨ y ∈ˢ Lset δ ⟩
             → ∥ Σ[ k ∈ ℕ ] ⟨ 𝒟ₒ y ∈ˢ Lset (sucIter k δ) ⟩ ∥₁) where
    open Iter 𝒟ₒ powIter public
```
