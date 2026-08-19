# LJ-1.394 review of `not-ambcard-gives`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`no-go-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-394/Probe394.agda:251-256` states
`not-ambcard-gives` exactly as the brief writes it: the negation of
`AmbCard α` must return a `Σ` that carries the ordinal `β`, its three
ordinal properties, and the injection `⟪ α ⟫ ↪ ⟪ β ⟫`, all untruncated.

## THE VERDICT

**NO-GO, and the failure is at ONE step.**

- **STEP 1 is YES.** `lem` reaches the ORDINAL, merely:
  `amb-gives-merely` (`Probe394.agda:144-154`) is green. From
  `(AmbCard α → Empty.⊥)` it produces `ex-amb α`
  (`:136-139`), the truncated existence of a `β` with `IsOrd β`,
  `⟨ β ∈ α ⟩` and `⟨ ω ∈ β ⟩`.
- **STEP 1B is YES.** The tree's own selection device reaches the
  ORDINAL as DATA: `amb-gives-ord-data` (`Probe394.agda:189-206`) is
  green. `leastOf` over `orderAt` at the stage `Lset (sucV α)`
  untruncates the existence, because the payload `Payload α β`
  (`:178-181`) is a proposition.
- **STEP 2 is NO.** NOTHING in this tree reaches the ARROW. The
  injection survives only under a double negation, and the step that
  would remove it is the hole at `Probe394.agda:249`, inside
  `untrunc-amb` (`:247-249`). The file's ONLY error is the unsolved
  meta at that hole (`runs/full-with-hole.out`), exit 42.

## WHICH STEP FAILS, AND WHAT WOULD CLOSE IT

**The failing step.** Convert `(((⟪ α ⟫ ↪ ⟪ β ⟫) → Empty.⊥) →
Empty.⊥)` into `(⟪ α ⟫ ↪ ⟪ β ⟫)`, for the `β` that STEP 1 supplies.
This is a double-negation elimination at a type that is not a
proposition.

**Why `lem` does not close it.** `LEM (ℓ-suc ℓ)` decides propositions
only (`src/Base/Classical.lagda.md:41-42`). `⟪ α ⟫ ↪ ⟪ β ⟫` is a `Σ`
over a function type (`src/L/Cardinal.lagda.md:47-48`); two injections
between the same carriers can differ as functions, so the type is not
a proposition. `lowerLEM` (`src/L/CantorBernstein.lagda.md:7`) moves
the principle between LEVELS, and not between GRADES.

**Why the tree's one untruncation device does not close it.** `leastOf`
demands a payload in `A → hProp`
(`src/L/WellOrder/Base.lagda.md:158-160`), so the payload must be a
proposition. The device worked at `[LJ-1.314]`
(`agents/tasks/LJ-1-314/CodeUntrunc.agda:75-101`) only because
`InjCode` is a proposition. The ordinal order `orderAt` orders the
ORDINALS below `α`; it does not order the INJECTIONS between them.

**What WOULD close it, and the tree holds neither.**

1. A double-negation eliminator at the ambient injection type. This is
   a choice principle that selects a canonical injection from a
   merely-existing family. The literature digest says such a selection
   needs a well-order on the INJECTIONS, and an ambient function type
   does not carry one (`dev/literature/truncation-and-selection.md:335-337`).
2. An ambient-to-coded bridge that turns the injection into an
   `InjCode` proposition. Then STEP 1B's mechanism finishes the job,
   because the payload becomes a proposition. The tree's only bridge
   runs coded to ambient (`src/L/CantorBernstein.lagda.md:33-38`);
   `[LJ-1.299]`'s `amb→code` consumes the ambient face only to REFUTE
   a code, so it is the same readback and not the missing bridge
   (`agents/tasks/LJ-1-299/NoInj2.agda:103-111`).

## THE SWEEP, BECAUSE A REFUTATION MEASURES ONE SITE (C-42)

`grep -rn "∥.*↪" src/` gives 9 lines. Four of them carry THIS task's
shape, a truncation whose payload is an ambient INJECTION:

- `src/L/Cardinal.lagda.md:113`, `:133`, `:141`, `:151`.

All four sit inside the same module, the least-cardinal search
`InternalLeastCard`, and `:133` is `κ-inj`, whose own comment says
"still truncated, still not an hProp". `[LJ-1.314]` already measured
that site and stated the same limit. The other five lines carry
truncations whose payloads are equalities or codes, which are
propositions, so they do not carry this shape.

**So the NO-GO names one debt, and the tree already held it.** The
recursion's case split needs codes at exactly the ARROW, and nowhere
else on the negative side.
