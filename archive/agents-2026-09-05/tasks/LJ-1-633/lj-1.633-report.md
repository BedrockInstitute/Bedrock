# LJ-1.633: report — is ω an L-cardinal

**VERDICT: GO.** `omega-is-L-cardinal : IsCardinalL ωʟ` is inhabited.
The one fact `[LJ-1.629]` left as a hypothesis is discharged, so
`target-false` becomes unconditional and `via-col-square` can serve
the bill's site.

## OBLIGATION

`agents/tasks/LJ-1-633/Probe633.agda::omega-is-L-cardinal`, green with
`--cubical --safe --guardedness`, no hole, no postulate. Verified
through the program's own witness meter:

```
pass      exit=0        1.95s  agents/tasks/LJ-1-633/Probe633.agda::omega-is-L-cardinal
witness: 0 UNRESOLVED of 1, 1.95 s, probe_red=False
```

## THE TERM

`agents/tasks/LJ-1-633/Probe633.agda:67-87`. The clause of `IsCardinalL`
is a function of a TRUNCATED code
(`src/L/Cardinal.lagda.md:230-233`), so the proof never constructs an
injection; it refutes the given one:

1. **Readback.** `readL` (`src/L/CantorBernstein.lagda.md:33-38`, the
   tree's `Small` readback at `src/L/Coding/Injection.lagda.md:123-148`)
   turns the code `InjCode F ωʟ δ` into the ambient injection
   `⟪ ω ⟫ ↪ ⟪ fst δ ⟫`.
2. **Ordinality.** `fst δ` is a member of `ω`, so it is an ordinal:
   `mem-ord {A = ω} ω-ord (fst δ) δ∈ω` (`src/L/Ordinal.lagda.md:221`).
3. **Pigeonhole.** `finite-excl-ω`
   (`src/L/InjChain.lagda.md:153-166`) refutes, for ANY ordinal member
   `β` of `ω`, an injective `⟪ ω ⟫ → ⟪ β ⟫ × ⟪ β ⟫`: `β` is a numeral,
   and the tree's own Fin pigeonhole (the `no-inj` at
   `src/L/Ordinal/SquareLaw.lagda.md:604-610,637-650`, particularized
   at `src/L/InjChain.lagda.md:140-148`) contradicts the injection.
   `PT.rec Empty.isProp⊥` discharges the truncation
   (`src/L/StageCardinal.lagda.md:442-443` uses the same shape).

## WHAT THE STATEMENT COST

- **Term: 15 lines of Agda** (the body of `omega-is-L-cardinal` plus
  its three local rows). The estimate was 60 to 100 lines, basis
  `agents/tasks/LJ-1-629/lj-1.629-report.md:74` and the brief's W3.
  The gap: `[LJ-1.629]` priced the sketch as though the `δ ≡ # n`
  transport and the pigeonhole application had to be written fresh.
  They are already landed in the tree: `finite-excl-ω`
  (`src/L/InjChain.lagda.md:153-166`) does the transport at the
  element level (`pathToEquiv` at `:161-165`) and the pigeonhole in
  one call, and `readL` does the readback. The probe is the
  composition of two landed generic rows.
- **Frame floor** (hole standing in for the term, full import list):
  `runs/floor-1.out`, 2.84 s, 446 MB peak. The frame was never the
  cost.
- **Full probe, green:** `runs/final-3.out` 1.66 s, 415 MB;
  `runs/final-5.out` 2.00 s on the re-run with corrected citations.
  Caliber: the program set `GHCRTS=-A64m -I0 -M2g` (wide); I never
  set it. One Agda process at a time, through the same wrapper as
  `[LJ-1.629]` (`runs/run.sh`). No heap wall, no timeout, so no
  restructuring was needed.
- These are WARM numbers against the cached tree
  (`_build/2.8.0/agda/`), comparable to `[LJ-1.629]`'s 2.81 s under
  the same conditions. A cold whole-tree price was not measured and
  is not claimed; it matters only if the term is later landed in
  `src/` (out of this task's scope).

## WHAT THE SHAPE RESISTED

Two surface issues only, both in the probe's own lines:

- A pattern left-hand side over a dependent pair (`f , finj = readL …`)
  is rejected: `MissingTypeSignature.Function`, then `MissingDefinitions`
  when the second name got its own signature. The landed form is one
  explicit `read : Σ[ f ∈ _ ] _` with `fst`/`snd` projections
  (`agents/tasks/LJ-1-633/Probe633.agda:81-87`).
- `fst ωʟ` reduces to `ω` definitionally
  (`src/L/Axioms/Infinity.lagda.md:69-70`), so `readL ωʟ δ` presents its
  function at `⟪ ω ⟫` with no transport. No deeper resistance: nothing
  in the route had to be weakened.

## WHAT IS NOT CLOSED

Nothing for this obligation. Two boundaries the next brief should
know:

- **The GO is about `IsCardinalL` only, at the coded predicate.** Per
  the pod-math addendum, the ambient `IsCardinal` verdict of
  LJ-1.90-A (`archive/dev/LJ-dispatch-index.md:166`: `| LJ-1.90-A |
  Orchestrator audit: IsCardinal is never inhabited | CONFIRMED | …`)
  was NOT imported. The two predicates DO connect at `ω`, and the
  term that is the connection is `readL` itself: it is the map from
  the coded world to the ambient one. The direction used here is
  `coded code → ambient injection → ambient refutation`; the
  converse direction (ambient non-cardinality of `ω` feeding the
  coded predicate without a code) is not what this proof states, and
  no ambient `IsCardinal ω` term is claimed or needed.
- **`[LJ-1.629]`'s refutation is now unconditional in substance**
  (`target-false` loses its only borrowed hypothesis), but the term
  `target-false` itself still names `IsCardinalL ωʟ` as an argument at
  `agents/tasks/LJ-1-629/Probe629.agda:139-140`. Making it an outright
  `SiteIsInit → Empty.⊥` is a one-line substitution of this term and
  is the mathematician's to queue, not something I did here.

## PREMISES CHECKED

- Premise 1 HOLDS: `target-false` at `agents/tasks/LJ-1-629/Probe629.agda:139-140`.
- Premise 2 HOLDS: the 60-to-100-line price at `agents/tasks/LJ-1-629/lj-1.629-report.md:74`; the brief's `:202-206` is item 3 of the same report's next-brief section, which quotes the same price.
- Premise 3 HOLDS: `no-inj` at `src/L/Ordinal/SquareLaw.lagda.md:604-606`; the brief's `:604-610` spans the whole `NoInj` module head.
- Premise 4 HOLDS but was UNUSED at the probe surface: `numeral-wit` at `src/L/StageCardinal.lagda.md:439-440` is real; the `δ ≡ # n` step my route needs is the same step performed inside `finite-excl-ω` via `ω-mem→numeral` (`src/L/InjChain.lagda.md:158,160`), so the probe never names it.

## W2 AND W4

**W2.** The probe writes no mathematics of its own: it composes two
landed generic rows, `readL` (generic in `a b : S`,
`src/L/CantorBernstein.lagda.md:33-38`) and `finite-excl-ω` (generic
in the ordinal member `β` of `ω`, `src/L/InjChain.lagda.md:153-166`).
Both proofs that later consume this fact share exactly that code.
Nothing landed in `src/`, so no fixed-form chapter was written and no
deadline conflict arose.

**W4.** No module was retired by this return. `dev/ARCHIVE.md` is
untouched.

## RATIO BAR

The write scope carries no `.lagda.md` master; the in-fence line count
is 0, so the 0.0123 s/line bar cannot fire on this return.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` — READ. Used for the addendum's
  near-miss check: `archive/dev/LJ-dispatch-index.md:166` reads
  `| LJ-1.90-A | Orchestrator audit: IsCardinal is never inhabited |
  CONFIRMED | Two hits in src: the definition and the hypothesis.
  The probe's own kappa, sucV omega, is not a cardinal either |`.
  That verdict is about the AMBIENT `IsCardinal` and was not imported;
  see "What is not closed".
- `archive/dev/JOURNAL-archived.md` — declined, not read: a journal,
  and nothing in this task's route needs journal history.
- `archive/dev/JOURNAL.md` — declined, not read: same reason.
- `dev/ARCHIVE.md` — declined, not read: no module retired (W4), so no
  archive row is due.
- `archive/dev/ORCHESTRATION.md` — declined, not read: orchestration
  history, not part of the term's route.

## LITERATURE USED

- `dev/literature/devlin-II5.md` — declined, not read: the obligation
  discharges by composition of landed tree rows; no external set
  theory result is needed.
- `dev/literature/truncation-and-selection.md` — declined, not read:
  the truncation in `IsCardinalL` is the given hypothesis, not a
  selection problem.
- `dev/literature/devlin-errata.md` — declined, not read.
- `dev/literature/digest.md` — declined, not read.
- `dev/literature/geology.md` — declined, not read.
