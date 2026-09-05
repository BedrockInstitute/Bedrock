# Review of `amb-limit`: the stated obligation is FALSE

**[LJ-1.392]'s second obligation, `amb-limit`, is refuted.** This file states
the obstruction, names the site, and points at the machine-checked evidence.
A stated NO-GO is a full return.

## The claim

The statement, as the brief writes it
(`agents/tasks/LJ-1-392/LJ-1.392.md:13-18`):

```agda
amb-limit : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
        → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
                     → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥)
        → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ sucV γ ∈ α ⟩
```

is FALSE at `α := sucV ω`, `γ := ω`. The tree therefore holds its negation,
and no term of this type can exist if the ambient theory is consistent.

## The site, in three steps

1. **The no-injection hypothesis is VACUOUS at `α := sucV ω`.** A member of
   `sucV ω` is a member of `ω` or `ω` itself
   (`∈sucV-elim`, `src/V/Model.lagda.md:218-227`). No member of `ω` contains
   `ω` (`ω∉β`, `src/L/InjChain.lagda.md:123-126`), and `ω` does not contain
   itself (`∈-irrefl`, `src/V/Hierarchy.lagda.md:155`). So every `β` meeting
   the clause's premises is excluded, the hypothesis holds outright, and the
   injection it forbids is never examined. This is the SAME vacuity the
   campaign already measured at `ω` itself
   (`agents/tasks/LJ-1-390/lj-1.390-report.md` VERDICT, premise 3 of this
   task's brief), recurring one successor higher.

2. **The conclusion is FALSE at `γ := ω`.** `⟨ ω ∈ sucV ω ⟩` holds
   (`self∈sucV`, `src/V/Model.lagda.md:236-237`), and the conclusion demands
   `⟨ sucV ω ∈ sucV ω ⟩`, which `∈-irrefl` refutes.

3. **The two meet.** `amb-limit` fed the vacuous hypothesis at `sucV ω` and
   applied at `ω` yields `⟨ sucV ω ∈ sucV ω ⟩`, then `⊥`.

## The machine-checked evidence

Both terms are in the probe and both are GREEN (the file's only red is the
deliberate hole in `amb-limit` itself):

- `noinj-vacuous-sucω : (β : V ℓ) → IsOrd β → ⟨ β ∈ sucV ω ⟩ → ⟨ ω ∈ β ⟩
  → (⟪ sucV ω ⟫ ↪ ⟪ β ⟫) → Empty.⊥`
  at `agents/tasks/LJ-1-392/Probe392.agda:229-235`.
- `amb-limit-refuted : ((the amb-limit type) → Empty.⊥`
  at `agents/tasks/LJ-1-392/Probe392.agda:236-244`. It is
  `∈-irrefl (sucV ω) (amb (sucV ω) (suc-ord ω-ord) (self∈sucV ω)
  noinj-vacuous-sucω ω (self∈sucV ω))`.

## What a reviewer should attack

- **The vacuity step.** It uses `∈sucV-elim` at `β ∈ sucV ω`, then `ω∉β` and
  `∈-irrefl`. Both continuations are one line each and cite delivered
  lemmas.
- **The typing.** The hypothesis of `amb-limit-refuted` is the obligation's
  type copied verbatim; Agda accepted the application, so the refuted type
  IS the stated type.
- **Consistency.** If the ambient theory were inconsistent the refutation
  would prove nothing, but the refutation uses no classical parameter at
  its two killing steps (`ω∉β`, `∈-irrefl`), so its cost is exactly the
  tree's regularity and ω-facts.

## The repaired statement, delivered GREEN in the same probe

The obstruction is exactly the member that does not contain `ω`. Restrict
the conclusion to members that DO contain `ω` and the statement closes with
no case split at all, because `suc∈or≡` (`src/L/Ordinal/Stages.lagda.md:137-147`)
delivers both cases and `suc-absorb` kills the successor case through the
ambient clause at `β := γ`:

```agda
amb-limit-ω∈γ : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩
  → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩
               → (⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥)
  → (γ : V ℓ) → ⟨ γ ∈ α ⟩ → ⟨ ω ∈ γ ⟩ → ⟨ sucV γ ∈ α ⟩
```

at `agents/tasks/LJ-1-392/Probe392.agda:255-266`. **`[LJ-1.393]` must take
THIS clause as its hypothesis, not the bare `amb-limit`: its brief says to
take "the clause as a bare hypothesis" on a NO-GO
(`agents/tasks/LJ-1-393/LJ-1.393.md:52-55`), and a refuted hypothesis is
uninstantiable.** The one member the repaired clause misses at any `α` with
`ω ∈ α` is `γ := ω` itself, whose closure `⟨ sucV ω ∈ α ⟩` is exactly what
distinguishes `sucV ω` from the limits above it.
