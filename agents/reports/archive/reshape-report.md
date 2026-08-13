# Reshape report: `step-mono` conditioned on membership (`L.Rud.Hierarchy`)

Follow-on to `_build/polish-r-report.md`, same territory. Trigger: R2c
(`_build/r2c-report.md` §6) refuted the committed telescope's universal
`step-mono` with a two-element counterexample. This batch reshapes the engine's
hypothesis to the form the engine actually uses, and re-derives the one proof
that consumed it. **Only `src/L/Rud/Hierarchy.lagda.md` was edited.**

## 1. The new telescope line, verbatim

```agda
  (step-mono∈ : {u v : V ℓ} → ((x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ v ⟩) → ⟨ u ∈ v ⟩
              → ((x : V ℓ) → ⟨ x ∈ step u ⟩ → ⟨ x ∈ step v ⟩))
```

replacing

```agda
  (step-mono : {u v : V ℓ} → ((x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ v ⟩)
            → ((x : V ℓ) → ⟨ x ∈ step u ⟩ → ⟨ x ∈ step v ⟩))
```

Name `step-mono∈` follows the file's convention (`step-⊆`, `step-∈`,
`step-trans`: the `step-` prefix plus the relation the property is about); the
`∈` marks the added condition, exactly as `step-∈` marks the self-membership
growth property. Hypothesis order keeps the old one first, so the diff at the
call site is an insertion, not a reordering. Continuation `→` is aligned under
the `:`, matching `step-trans`.

The remaining three parameters, the `{ℓ}` and `lem` slots, and the whole
`where` body's export surface are untouched.

## 2. What changed in the proofs

**One code site consumed the old parameter** (verified by grep over `src/`:
`step-mono` occurred exactly once outside prose, at `Sset-suc`). The engine's
other lemmas use `step-⊆` (`Sset-mono`, `Sset-limit`), `step-∈`
(`Sset-level-mem`), `step-trans` (`level-trans`), or no step property at all
(`Sset-index-mono`).

### 2.1 New export `Sset-mem` (the membership half of cumulativity)

```agda
Sset-mem : {α β : S} → ⟨ β ∈ˢ α ⟩ → ⟨ Sset β ∈ˢ Sset α ⟩
Sset-mem {α} {β} β∈α = Sset-in α β (Sset β) β∈α (step-∈ (Sset β))
```

Placed immediately after `Sset-mono` in "Membership and cumulativity", whose
hypothesis it shares verbatim:

| lemma | hypothesis | conclusion | cost |
|---|---|---|---|
| `Sset-mono` | `⟨ β ∈ˢ α ⟩` | `Sset β ⊆ Sset α` | `step-⊆` + `Sset-in` |
| `Sset-mem` (new) | `⟨ β ∈ˢ α ⟩` | `⟨ Sset β ∈ˢ Sset α ⟩` | `step-∈` + `Sset-in` |

That the two halves fall out of the *same* hypothesis, at the same price, with
`step-⊆` and `step-∈` in the same slot, is the reason the reshaped telescope is
dischargeable at all: the levels hand over inclusion and membership together,
which is precisely the pair `step-mono∈` now asks for. It also confirms the
condition is not an ad-hoc patch but the shape the engine was already in.

`Sset-mem` is **incomparable** with the existing `Sset-level-mem`
(`⟨ sucV β ∈ˢ α ⟩ → ⟨ Sset β ∈ˢ Sset α ⟩`), not a generalization of it: the
latter's hypothesis names `sucV β`, so neither implies the other without
transitivity of `α`. `Sset-level-mem` is untouched, statement and proof.

**This is the batch's one addition to the export surface.** Nothing downstream
can break from an addition, and the alternative (a `where`-local or `private`
helper) would hide the fact a future instantiation batch needs. If the owner
would rather it not be exported, demoting it is a one-word edit; flagged here
rather than decided silently.

### 2.2 `Sset-suc`, the only re-derivation

```agda
    uStep (γ , γ∈suc , x∈stepSγ) = ∈sucV-elim (snd (x ∈ˢ step (Sset β))) γ∈suc
      (λ γ∈β → step-mono∈ (Sset-mono {α = β} {β = γ} γ∈β)
                 (Sset-mem {α = β} {β = γ} γ∈β) x x∈stepSγ)
      (λ γ≡β → subst (λ w → ⟨ x ∈ˢ step (Sset w) ⟩) γ≡β x∈stepSγ)
```

The added argument is `Sset-mem` at the same `γ∈β` the old code already passed
to `Sset-mono`. No other line of the proof moved; the `γ ≡ β` branch, the `sup`
direction, and `ext-⊆` are unchanged. Everything else in the chapter needed
nothing.

## 3. Prose corrections (C-3: a prose invariant is load-bearing)

Three places became false or dangling and were corrected in **both** language
blocks (en authored first, zh translated from it; house punctuation rules
applied, `lint-prose.py` clean):

1. **"The derived case equations"** — `step-mono`{.Agda} was a cross-reference
   to a name that no longer exists. Renamed, and a paragraph added recording
   *why* the hypothesis is conditioned: a step that puts its own argument in
   its image cannot be monotone in the subset order (`{u} ∈ step u`, and
   `u ⊆ v` gives no reason for `{u} ∈ step v`, which wants `u ∈ v`); the
   sixteen-image step is of that kind through its pairing operation, so the
   universal form is refutable there. This is R2c's finding, recorded in the
   master where the next reader of the telescope will meet it.
2. **`Sset-level-mem`'s paragraph** claimed *"This is the one place
   `step-∈`{.Agda} is spent."* `Sset-mem` now also spends it, so the sentence
   was false the moment the lemma landed. Rewritten to "the second and last
   place", with `Sset-mem` named.
3. **"Membership and cumulativity"** gained the two sentences introducing
   `Sset-mem` and saying what the pair is for.

Untouched and still true: the header's "four properties the proofs actually
spend" (still four), and the recap's "cumulativity in both readings" (the two
readings are inclusion and membership; `Sset-mem` and `Sset-level-mem` are the
same membership reading at a member index and at a successor index, which is
how the prose now words it).

## 4. Line delta and timings

| | before | after | delta |
|---|---|---|---|
| code lines (`​```agda` fences) | 226 | 230 | **+4** |
| file lines (incl. prose) | 452 | 473 | +21 |

The +4 is `Sset-mem` (2 lines + separator) and the extra line `Sset-suc`'s call
wraps to. The +21 file delta is the prose of §3, mostly the new
why-membership paragraph in two languages.

| check | cap | result | time |
|---|---|---|---|
| `agda src/L/Rud/Hierarchy.lagda.md` | `GHCRTS=-M6g` | **rc=0** | 1 s |
| `agda src/L/Rud/Step.lagda.md` (read-only) | `GHCRTS=-M6g` | **rc=0** | 1 s |
| `agda src/Everything.lagda.md` (read-only) | `GHCRTS=-M6g` | **rc=0** | 4 s |

One check at a time; no heap event, no watchdog kill. `Step.agdai` was deleted
first to force a genuine recheck rather than an interface-hit (the first run
returned instantly with no `Checking` line, which only proves its stored
interface already matched; the forced run prints `Checking L.Rud.Step` and is
the number reported).

Linters on the edited file: `lint-prose.py` 0, `lint-agda.py` 0,
`weave-i18n.py --check` 0.

## 5. Step / Everything: no breakage, and why not

**`src/L/Rud/Step.lagda.md` does not import `L.Rud.Hierarchy`.** Its import
block reaches `L.Rud.Ops` and `L.Rud.Images` only (it could not instantiate the
engine — that is deliverable 3, which R2c reports as blocked by this very
wall). So the telescope change cannot reach it, and the green above is a
control, not a repair.

**`src/Everything.lagda.md` carries a bare `import L.Rud.Hierarchy`** with no
module application, so it consumes the module's existence, not its telescope.
Green.

Consequently **no breakage to report**: neither file needed an edit and neither
was edited. `git status --porcelain` on both is empty.

The instantiation that *will* feel this change does not exist yet: R2c's
deliverable 3 (`ConcreteS`) was blocked precisely because the old telescope was
unsatisfiable. Whoever writes it now owes `step-mono∈` instead, and R2c §6's own
sentence says that obligation is the satisfiable one ("holds only for argument
sets that satisfy `u ∈ v ∪ {v}`; level pairs do").

## 6. Scope and hygiene

- Edited: `src/L/Rud/Hierarchy.lagda.md` only.
- Read-only: `src/L/Rud/Step.lagda.md`, `src/Everything.lagda.md` (typechecked,
  not opened for writing).
- Not touched: `Realize.lagda.md`, `Describe.lagda.md` (other agents'),
  `Ops`/`Images`/`OrdArith` (committed as `77ac3e0`).
- Not folded in: the `sucV-inj-ord` unused-`ordγ` change, per instruction; it
  remains item 5 of `_build/polish-r-report.md` §6, awaiting the owner's ruling.
- Nothing committed.

Declaration diff at indent 0-2 against `HEAD`, the whole of it:

```
< (step-mono : {u v : V ℓ} → ((x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ v ⟩)
> (step-mono∈ : {u v : V ℓ} → ((x : V ℓ) → ⟨ x ∈ u ⟩ → ⟨ x ∈ v ⟩) → ⟨ u ∈ v ⟩
> Sset-mem : {α β : S} → ⟨ β ∈ˢ α ⟩ → ⟨ Sset β ∈ˢ Sset α ⟩
```

One parameter reshaped, one lemma added, nothing else in the interface moved.

## 7. Note for the lesson book (not filed; out of scope)

R2c's §11.1 lesson candidate is now confirmed by construction and is worth a
**D-series** entry rather than a P/R one, since it is a design law about
telescope shape:

> A step operator that contains its own argument cannot be monotone in the
> subset order; state its monotonicity conditioned on membership. The universal
> form looks harmless and is refutable by a two-element counterexample, while
> every classical use of it is at level pairs, where the containing structure
> supplies the membership for free.

The corroborating detail this batch adds: the membership the conditioned form
needs comes from *the same hypothesis and the same construction* as the
inclusion it already had (`Sset-mono`/`Sset-mem` differ only by `step-⊆` versus
`step-∈`), which is the structural sign that the conditioned form, not the
universal one, was the right telescope all along.
