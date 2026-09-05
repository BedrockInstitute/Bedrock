# Review of `amb-init`: the stated obligation is FALSE

**[LJ-1.393]'s second obligation, `amb-init`, is refuted.** This file states
the obstruction, names the site, and points at the machine-checked evidence.
A stated NO-GO is a full return. The refutation is not new mathematics: it
is `[LJ-1.392]`'s counterexample, delivered between this task's first and
second dispatch, closing this task's own statement through it.

## The claim

The statement, as the brief writes it
(`agents/tasks/LJ-1-393/LJ-1.393.md:21-24`):

```agda
amb-init : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → AmbCard α
         → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
         → Init α
```

is FALSE at `α := sucV ω`. Every hypothesis HOLDS there and the conclusion
is FALSE there, so no term of this type exists if the ambient theory is
consistent. The hole `amb-init = ?` at
`agents/tasks/LJ-1-393/Probe393.agda:185` is the formal remainder, red by
design.

## The site, in four steps

1. **`AmbCard (sucV ω)` holds, vacuously.** `AmbCard` speaks only at
   members `β` of `α` with `⟨ ω ∈ β ⟩`. A member of `sucV ω` is a member
   of `ω` or `ω` itself (`∈sucV-elim`, `src/V/Model.lagda.md:218-227`);
   no member of `ω` contains `ω` (`ω∉β`, `src/L/InjChain.lagda.md:123-126`),
   and `ω` does not contain itself (`∈-irrefl`,
   `src/V/Hierarchy.lagda.md:155`). This is `[LJ-1.392]`'s
   `noinj-vacuous-sucω` (`agents/tasks/LJ-1-392/Probe392.agda:229-235`),
   whose type at `α := sucV ω` IS `AmbCard (sucV ω)`.

2. **The member square-law hypothesis holds, vacuously, for the same
   reason.** It too speaks only at infinite ordinal members of `α`, and
   `sucV ω` has none. `sq β` follows from `Empty.⊥` by `Empty.rec`.

3. **`IsOrd (sucV ω)` and `⟨ ω ∈ sucV ω ⟩` are delivered facts**
   (`suc-ord ω-ord`, `self∈sucV`, `src/V/Model.lagda.md:236-237`).

4. **`Init (sucV ω)` is FALSE, at its THIRD conjunct.** The third conjunct
   (`src/L/Ordinal/SquareLaw.lagda.md:695`) at `γ := ω` demands
   `⟨ sucV ω ∈ sucV ω ⟩` from `⟨ ω ∈ sucV ω ⟩`, and `∈-irrefl` refutes
   it. This is the successor-side recurrence of the boundary correction
   the archive already holds for `ω` itself: `Init ω` is uninhabited
   through the SECOND conjunct
   (`archive/dev/JOURNAL-archived.md:2000-2006`); `Init (sucV ω)` is
   uninhabited through the third.

## The machine-checked evidence

All four terms are in the probe and all are GREEN (the file's only red is
the deliberate hole in `amb-init` itself):

- `no-ω-mem-sucω : (β : V ℓ) → ⟨ β ∈ sucV ω ⟩ → ⟨ ω ∈ β ⟩ → Empty.⊥` at
  `agents/tasks/LJ-1-393/Probe393.agda:152-155`, the `[LJ-1.392]` term
  rebuilt, credited there.
- `AmbCard-sucω : AmbCard (sucV ω)` at
  `agents/tasks/LJ-1-393/Probe393.agda:158-159`.
- `sqβ-sucω : (β : V ℓ) → IsOrd β → ⟨ β ∈ sucV ω ⟩ → ⟨ ω ∈ β ⟩ → sq β`
  at `agents/tasks/LJ-1-393/Probe393.agda:161-162`.
- `amb-init-refuted : ((the amb-init type) → Empty.⊥` at
  `agents/tasks/LJ-1-393/Probe393.agda:164-170`. It is
  `∈-irrefl (sucV ω) ((amb (sucV ω) (suc-ord ω-ord) (self∈sucV ω)
  AmbCard-sucω sqβ-sucω) .snd .snd .fst ω (self∈sucV ω))`.

## What a reviewer should attack

- **The vacuity step.** It is `[LJ-1.392]`'s term verbatim in content; the
  tree holds it green twice now, once in each probe.
- **The typing.** The hypothesis of `amb-init-refuted` is the obligation's
  type copied verbatim; Agda accepted the application and the projection
  chain `.snd .snd .fst`, so the refuted type IS the stated type and the
  third conjunct IS what kills it.
- **Consistency.** The two killing steps are `ω∉β` and `∈-irrefl`, both
  classical-free, so the refutation's cost is the tree's regularity and
  ω-facts and nothing else.
- **The fourth conjunct.** `amb-noinj²` is NOT the obstruction: it is
  green at `agents/tasks/LJ-1-393/Probe393.agda:119-131`, at every `α`,
  from `AmbCard` and the member square law. Only the THIRD conjunct fails,
  and it fails at exactly one member, `γ := ω`.

## The corrected target, delivered GREEN in the same probe

The obstruction is exactly the membership `⟨ sucV ω ∈ α ⟩`: the closure
of `ω` itself. Add it as a hypothesis and the statement closes:

```agda
amb-init' : (α : V ℓ) → IsOrd α → ⟨ ω ∈ α ⟩ → ⟨ sucV ω ∈ α ⟩ → AmbCard α
          → ((β : V ℓ) → IsOrd β → ⟨ β ∈ α ⟩ → ⟨ ω ∈ β ⟩ → sq β)
          → Init α
```

at `agents/tasks/LJ-1-393/Probe393.agda:207-220`. The third conjunct then
closes three ways: a member below `ω` by `ω-limit`
(`src/L/InjChain.lagda.md:109-110`) and the ordinal's transitivity, `ω`
itself by the new hypothesis, and a member containing `ω` by `amb-limit`
in the repaired form `[LJ-1.392]` reports
(`agents/tasks/LJ-1-392/Probe392.agda:255-266`), taken as this probe's
module hypothesis. The corrected form is consistent with the refutation:
`sucV ω` itself satisfies every OTHER hypothesis and fails exactly the new
one. Whether any `α` satisfies ALL of them, with `AmbCard α`, is the
question `[LJ-1.394]` and `[LJ-1.395]` own.
