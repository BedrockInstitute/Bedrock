# R2b report: the abstract S-hierarchy engine (`[L3.31-R2b-abs]`)

## 1. Deliverables and status

| item | state |
|---|---|
| `src/L/Rud/Hierarchy.lagda.md` | created; `GHCRTS=-M10g agda src/L/Rud/Hierarchy.lagda.md` checks clean |
| code lines | 236 (stop-line 1,200; 19.7%) |
| prose lint (`lint-prose.py --check`) | clean |
| Agda lint (`lint-agda.py --check`) | clean (no unused imports, OPTIONS header exact) |
| i18n markers (`weave-i18n.py --check`) | clean |
| glossary (`check-glossary.py --check`) | clean |
| `_build/r2b-report.md` | this file |
| walls | none (whole file checks in ~1.3 s cold; no heap event, no 180 s wall, no NO-GO trail) |

Nothing else in the checkout was touched. The concrete sixteen-operation step
is intentionally absent: the module is the abstract engine, and the
instantiation batch discharges the telescope below.

## 2. The final telescope

The module header is

```text
module L.Rud.Hierarchy
  {ℓ : Level}
  (lem : LEM (ℓ-suc ℓ))
  (step : V ℓ → V ℓ)
  (step-⊆  : (u x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ step u ⟩)
  (step-∈  : (u : V ℓ) → ⟨ u ∈ step u ⟩)
  (step-mono : {u v : V ℓ} → u ⊆ v → step u ⊆ step v, stated pointwise)
  (step-trans : (u : V ℓ) → transitive u → transitive (step u), stated pointwise)
```

Seven parameters, no more. No lemma forced any additional property of `step`:
the four pinned core properties are exactly sufficient, which is the point of
the abstract design and was confirmed by writing every proof below against
them and nothing else.

| parameter | why it is needed | where the instantiation discharges it |
|---|---|---|
| `ℓ : Level` | ambient universe of the carrier `V ℓ` | passed by the assembly (R2/R3 chain already carries it) |
| `lem : LEM (ℓ-suc ℓ)` | classical cone, not a step property: the limit equation needs the ordinal trichotomy (`ord-tri` from `L.Ordinal.Linear`, itself LEM-based), and `L.Rud.OrdArith` takes it as its own parameter. Spent at exactly one place: `limit-succ-mem` (see section 4) | the instantiation batch threads the book's established classical face (`LEM (ℓ-suc ℓ)`), same as every downstream classical module |
| `step : V ℓ → V ℓ` | the one-step operator the whole hierarchy is built from | the sixteen-operation operator `S(U) = ⋃ { Fᵢ(a,b) | a,b ∈ U ∪ {U} }` from `L.Rud.Ops` |
| `step-⊆ : u ⊆ step u` | the growth axiom. It is the only property behind cumulativity (`Sset-mono`: `β ∈ α → Sset β ⊆ Sset α`), the `union-of-earlier-levels` direction of the limit equation, and the forward direction of cumulativity-based membership | the sixteen-image operator contains each input in its diagonal images (pair/singleton/union-free images), proven in the instantiation batch from `Ops`'s extension equations |
| `step-∈ : u ∈ step u` | the level-membership reading of cumulativity: `Sset-level-mem` (`sucV β ∈ α → Sset β ∈ Sset α`). This is its only consumer in the module | the self-membership clause of the concrete operator (`u ∈ step u` via the pairing/singleton images) |
| `step-mono : u ⊆ v → step u ⊆ step v` | the successor equation `Sset-suc`: the `⊆` direction splits members of `sucV β` into "below `β`" (cumulativity + `step-mono`) and "equal to `β`" (transport) | monotonicity of each of the sixteen operations in its arguments, again from `Ops` |
| `step-trans : transitive u → transitive (step u)` | transitivity of every level (`level-trans`'s step case, hence `Sset-trans`), the engineered property of the enlarged basis (SZ footnote 5) | transitivity of the concrete sixteen-image operator, the headline property the basis was enlarged for |

One design note on the telescope's spelling: imports placed before the module
header are not in scope inside the header's parameter types (verified by
probe), so `step-trans` could not be stated with the name `isTransV` from
`L.Constructible` (its import is level-parameterized and hence header-invisible).
The parameter is stated with the transitivity predicate written out pointwise;
this is definitionally identical to `isTransV` (an identity bridge
`isTransV' u → isTransV u` typechecks as `t = t`). Downstream readers of the
type see the same function type `∀ {x y} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ u ⟩ → ⟨ y ∈ˢ u ⟩`.

## 3. Per-item inventory: sizes and timings

The whole file checks in **1.3 s user / 1.4 s wall, cold**, under
`GHCRTS=-M10g` (measured twice; the second run 1.3 s). Per-item timings are
not separately measurable: Agda 2.8.0's profile verbosity produced no
per-definition breakdown, and every item is far below the noise floor of the
dependency-chain load that dominates the total. Sizes are code lines inside
` ```agda ` fences.

| item | lines | notes |
|---|---:|---|
| OPTIONS, imports, module header (the telescope) | 38 | includes all opens |
| `_⊆_`, `ext-⊆` | 6 | the only equality engine used |
| `isLevel` (4 constructors), `level-trans` | 12 | mirror of `isLayer`/`layer-trans`; binary-union constructor trimmed |
| tower: `Sset-step`, `opaque Sset`, `Sset-stepFam`, `opaque Sset-compute` | 17 | exact `Lset`-tower mirror, `opaque` at birth (P-c) |
| `Sset-level`, `Sset-trans` | 13 | mirror of `Lset-layer`; transitivity of every level |
| `Sset-in`, `Sset-out` | 33 | membership characterization, both directions |
| `Sset-mono`, `Sset-index-mono` | 8 | cumulativity; monotonicity in the index |
| `Sset-zero`, `Sset-suc` | 29 | derived case equations 1 and 2 |
| `Sset-level-mem` | 4 | level membership reading of cumulativity |
| `limit-succ-mem` | 15 | successor-closure of limits (the one classical step) |
| `Sset-levelFam`, `Sset-limit` | 54 | derived case equation 3 (largest single item) |
| `Jset` + `Jset-trans`/`Jset-mono`/`Jset-limit` | 13 | `J` at limits with its reads |
| **total** | **236** | stop-line 1,200, headroom 81% |

## 4. Proof shapes of the derived equations

The three equations are stated for the code-level family `Sset`; the prose and
this report write the mathematics as `S`.

**`Sset-zero : S ∅ ≡ ∅`.** Both inclusions are trivialities of the empty
index. In: `Sset-out ∅` hands a witness `δ ∈ ∅`, refuted by `∅-empty`. Out:
from `x ∈ ∅`, `∅-empty` refutes, then `Empty.rec`. Uses no step property.

**`Sset-suc : (β : S) → S (sucV β) ≡ step (S β)`.** Two inclusions via
`ext-⊆`.
`⊆`: `Sset-out` hands `γ ∈ sucV β` with `x ∈ step (S γ)`; `∈sucV-elim` splits:
`γ ∈ β` gives `S γ ⊆ S β` by cumulativity (`Sset-mono`, which itself needs
only `step-⊆`) and then `step (S γ) ⊆ step (S β)` by `step-mono`; `γ ≡ β` is
a transport.
`⊇`: `β ∈ sucV β` by `self∈sucV`, then `Sset-in` names the fibre. No ordinal
hypothesis on `β` is needed, so the equation holds for every set, not only
ordinals (stronger than the pinned statement, recorded as a surprise).

**`limit-succ-mem : (α β : S) → isLimit α → β ∈ α → sucV β ∈ α`.** The only
classical step. `ord-tri (sucV β) α` (ordinal trichotomy, LEM) leaves three
cases: membership (done); equality, refuted by `isLimit-not-succ` (a successor
is never a limit); and `α ∈ sucV β`, split by `∈sucV-elim` into `α ∈ β`
(transitivity of `α` closes `α ∈ β ∈ α` into `α ∈ α`, refuted by `∈-irrefl`)
and `α ≡ β` (the premise `β ∈ α` transports to `β ∈ β`, refuted by
`∈-irrefl`). Note the second disjunct uses the *premise* `β ∈ α`, not the
membership `α ∈ sucV β`: `α ∈ sucV β` with `α ≡ β` is only the trivial
disjunct of the successor, so it carries no contradiction by itself. This was
the one proof-shape trap of the chapter.

**`Sset-limit : (α : S) → isLimit α → S α ≡ ⋃ { S β | β ∈ α }`.** Two
inclusions.
`⊆` (union of earlier levels inside `S α`): the fibre of `x ∈ ⋃ { S β | β ∈ α }`
gives `x ∈ S β` with `β ∈ α`; `step-⊆` raises to `x ∈ step (S β)`;
`Sset-in` closes.
`⊇` (`S α` inside the union of earlier levels): `Sset-out` hands
`x ∈ step (S δ)` with `δ ∈ α`; `Sset-suc` rewrites `step (S δ)` to
`S (sucV δ)`; `limit-succ-mem` closes `sucV δ ∈ α`; the union axiom names the
fibre `S (sucV δ)`. This is where `lem`, `Sset-suc`, and `limit-succ-mem`
all pay at once.

The limit equation is the union of *earlier levels*, not of earlier
step-images; the step-images only appear on the way, and the successor
equation converts them. That is exactly why the successor equation must come
first and why the closure of limits under successor is load-bearing.

## 5. LESSONS applied

- **P-h at full strength**: the walk is module-parameterized; `step` and its
  four properties are the entire interface, nothing concrete is in scope, and
  no lemma mentions a `sett` body of a real operator. Measured payoff: the
  whole file checks in 1.3 s, no conversion explosion anywhere (no `-- perf:`
  markers needed).
- **P-c / R-2**: the tower `Sset` is sealed `opaque` at its birth site with
  `Sset-compute` as the official unfolding, mirroring `Lset`.
- **I-2**: every hProp-valued expression in a signature sits inside `⟨_⟩`
  (`⟨ x ∈ˢ u ⟩` throughout); the only bare proposition in a type position is
  the motive of `∈sucV-elim`, which is the level-polymorphic `⊥* {ℓ-suc ℓ}`
  (a `Type`, not an `hProp`).
- **C-11**: parameterized module body indents deeper than the header.
- **R-34 (checked, not needed)**: `InfinitySet`'s `sucV` is used with its
  level anchored by the surrounding set argument (`sucV β` with `β : S`), so
  no implicit-level meta was left open; no module alias was required. The
  B4e-style `#_`-in-a-lemma-type pattern does not occur here.
- **D-7 (not applicable)**: no intersection appears in the abstract engine;
  the realization batch spends LEM where the route memo pins it.
- **T-series (checked, not needed)**: the recursion is the tower's
  `∈-induction` pattern; no accessibility nests arose.
- **C-12 / memory guardrails**: every `agda` run was prefixed
  `GHCRTS=-M10g`, one typecheck at a time; no heap event, no watchdog kill.

## 6. Surprises and lesson candidates

1. **`S` and `J` are taken names.** `S` clashes with the `ZFStructure`
   carrier field re-exported by `open hPropStructure 𝒮ᵥ`; `J` clashes with
   cubical path induction re-exported by `Base.Prelude`. The family is spelled
   `Sset` and the limit subfamily `Jset` in code, with the mathematical `S`/`J`
   kept in prose and this report. Lesson candidate: a family named after a
   single Latin letter cannot coexist with the structure/`hPropStructure`
   scope; compound names (`Lset`, `Sset`) are the house pattern for exactly
   this reason.
2. **Header parameter types cannot see pre-header imports.** A level-specific
   name like `L.Constructible.isTransV` (importable only with `{ℓ}` applied)
   is invisible inside the module header, and even the *handle*
   `L.Constructible` of a plain `import` is not in scope there (probed in
   `/tmp`). `step-trans` is therefore stated with the transitivity predicate
   written out pointwise, definitionally identical to `isTransV`. Lesson
   candidate: telescope types may only use level-generic imported names; any
   level-parameterized predicate must be inlined into the header or the
   module must take its subject parameters in an inner `module _` block.
3. **Agda's mixfix parser rejects `x ∈ˢ ⋃ (...)` and `x ⊆ ⋃ (...)`** (an
   infix operator applied with a prefix `⋃` operand right after it). The
   repo's established workaround is binding the union to a local name (`U`)
   or going through `∈∈ₛ` with the union as the `b` argument; both appear in
   `Sset-limit`. Lesson candidate: never write `∈ˢ ⋃` / `⊆ ⋃` directly;
   always bind the union term.
4. **`Sset-suc` needs no ordinality.** Cumulativity is membership-level
   (`β ∈ α → S β ⊆ S α`) and needs only `step-⊆`, so the successor equation
   holds for every set. The pinned statement (for ordinal `β`) is what the
   literature needs and what the limit equation consumes; the module proves
   the strictly stronger general version at no extra cost.
5. **The trichotomy `α ≡ β` case is a premise trick.** From `α ∈ sucV β` and
   `α ≡ β` there is no contradiction (the membership is the trivial disjunct);
   the contradiction comes from transporting the *premise* `β ∈ α` along the
   equality to `β ∈ β`. Easy to get wrong twice (both subst directions were
   tried before the right one).
6. **`∈sucV-elim`'s motive lives at `Type (ℓ-suc ℓ)`**, so a refutation
   motive must be `⊥* {ℓ-suc ℓ}` (with `isProp⊥* {ℓ-suc ℓ}`), not
   `Empty.⊥`; the consumer is `Empty.rec*`. This is the I-2 boundary showing
   up in motive position rather than signature position.
7. **The `isLevel` predicate trims one constructor.** The constructible
   tower's binary-union closure is omitted (no level here is ever a binary
   union), keeping the predicate's induction minimal; the set-union and
   family-union forms cover every level the tower actually builds.
8. **No walls, no `-- perf:` markers.** The abstract design's promise held:
   the entire engine, including the ordinal side, checks in 1.3 s cold. The
   wall-protocol budget was untouched.

## 7. What the instantiation batch inherits

The exports the rest of the route quotes: `Sset`, `Sset-zero`,
`Sset-suc`, `Sset-limit`, `Sset-mono`, `Sset-index-mono`,
`Sset-level-mem`, `Sset-trans`, `Jset` with `Jset-trans`/`Jset-mono`/
`Jset-limit`, plus `isLevel`/`level-trans` as the closure-principle view.
The batch instantiates the telescope with the sixteen-operation step from
`L.Rud.Ops`, proves the four properties (each mapped to its source in
section 2), and reads the hierarchy off without touching a single proof body
here. `Jset` rud-closure is explicitly NOT a deliverable of this module: it
needs the concrete operations and belongs to the instantiation.
