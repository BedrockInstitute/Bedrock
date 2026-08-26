# review-of-powiter-status: a STATED NO-GO, with the truth of two members

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.668
obligation: agents/tasks/LJ-1-668/Probe668.agda::powiter-status
verdict: **NO-GO on the closed term.** `powiter-status` of type
`(y : S) → ⟨ y ∈ˢ Lset lam ⟩ → ⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩` is not
inhabited. The witness meter reads `1 UNRESOLVED of 1, 1.14 s,
probe_red=False`
(`agents/tasks/LJ-1-668/runs/meter-obligation.out:2`). The probe is
green and carries no hole (`runs/p-final.out`, `EXIT=0`).

**THIS IS NOT A REFUTATION OF `powiter-status`.** I did not build a
term of its negation. The statement is true at every member the frame
admits and that I named. What is measured is that the tree cannot
close the arbitrary-member case today, and that the only route it has
still owes `Describes`.

The critic reads this file. It does not close the task.

---

## 1. WHAT THE SEARCH TRIED

Five green measurements and one designed red slice.

1. **A set is a member of its own definable powerset.** `A∈𝒟ₒ`
   (`Probe668.agda:79-80`) is `𝒟ₒ-intro` at `⊤̇` and
   `DefOf.defSet⊤≡A` (`src/L/Definability.lagda.md:178-179`). Meter:
   `0 UNRESOLVED of 2` including this name
   (`runs/meter-names.out:3`).
2. **A stage is a member of the limit stage.** `At.lset∈limit`
   (`Probe668.agda:132-133`) is `Lset-in` at `A∈𝒟ₒ (Lset δ)`. It
   needs `δ ∈ lam` and nothing else.
3. **`𝒟ₒ` of a STAGE is a member of the limit stage.**
   `At.dee-stage∈limit` (`Probe668.agda:139-143`) rewrites by
   `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`) and reuses
   `lset∈limit` at `sucV δ`. These are the members the tower itself
   applies `𝒟ₒ` to. They do not refute.
4. **The empty set does not refute.** `dee-empty`
   (`Probe668.agda:85-86`) is `𝒟ₒ ∅ ≡ sucV ∅`.
   `At.dee-empty∈limit` (`Probe668.agda:153-158`) puts that ordinal
   in `Lset lam` by `ord∈Lset-suc` and two uses of `succλ`. Meter of
   the five nested names: `0 UNRESOLVED of 5`
   (`runs/meter-consumer.out:6`).
5. **The consumer is already written, generic, and not rewritten.**
   `At.from-iter` (`Probe668.agda:169-173`) is `Bound.Iter.pow∈λ`
   (`src/L/Coding/Bound.lagda.md:109-110`) at `D = 𝒟ₒ`. W2.

The floor of the exact obligation is `runs/FLOOR.agda.txt`: exit 42
at the one designed hole (`runs/floor-1.out:5-7`), 1.35 s, peak
270,811,136 bytes.

## 2. D-10, THE TARGET IS NOT FALSE

I did not find a cardinality or Tarskian obstruction to the
limit-stage closure at an arbitrary member.

Devlin asserts the same closure and proves nothing. `[LJ-1.167]`
quoted the scan (`agents/tasks/LJ-1-167/lj-1.167-report.md:170-172`):
"if lim (α) and α > ω, the set Lα is closed under the function Def".
His extra `α > ω` is a proof-route constraint: formulas live at ω.
It is not a truth constraint. At `y = ∅` the identity `𝒟ₒ ∅ ≡ sucV ∅`
is MEASURED (`Probe668.agda:85-86`), and `sucV ∅` is an ordinal, so
it sits in `Lset ω`.

`[LJ-1.167]` inferred the finite-iterate form with `k = 3`
(`agents/tasks/LJ-1-167/lj-1.167-report.md:204-206`). `[LJ-1.169]`
measured that this tree's codes grow with nesting depth and that
`+ω` absorbs the growth
(`agents/tasks/LJ-1-169/lj-1.169-report.md:247-253`). That is a
proof-route obstruction. It is not a truth obstruction: `𝒟ₒ y` is a
set of subsets of `y`, and its rank is at most one more than the
rank of `y`.

The corrected target beside the original, as D-10 asks, is the same
type. It is true. It is not closed. The consumer `from-iter` is that
type conditional on `PowIter`.

## 3. WHAT A COUNTEREXAMPLE WOULD HAVE TO DECIDE

A pair `(lam, y)` with `IsOrd lam`, successor-closure, `∅ ∈ lam`,
`y ∈ Lset lam`, and `𝒟ₒ y ∉ Lset lam`.

Rank does not give such a pair at a limit: every member of `𝒟ₒ y`
is a subset of `y`, so the rank of `𝒟ₒ y` is at most the rank of
`y` plus one, and that rank sits below `lam`. A counterexample would
have to be a set of small rank that is `𝒟ₒ` of a constructible
member and is not a definable subset of any earlier stage. That is
the negation of `[LJ-1.169]`'s `Describes` at every finite iterate
of the birth stage of `y`
(`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`).

The frame admits `∅` and it admits every stage `Lset δ` with
`δ ∈ lam`. Both are closed. D-26 says a member of a definable power
carries no generation data (`dev/LESSONS.md:1741-1743`), so an
arbitrary `y` does not carry a key that would build `𝒟ₒ y`. A
refutation has to name a specific `y`. I did not find one.

## 4. THE UNPAID ROUTE

The only introduction into `𝒟ₒ` is `𝒟ₒ-intro`
(`src/L/Constructible.lagda.md:301-304`). To place `𝒟ₒ y` in
`Lset (sucV σ)` one must exhibit a formula over `⟪ Lset σ ⟫` whose
inner extension is `𝒟ₒ y`. That is `Describes`
(`agents/tasks/LJ-1-169/ProbeLJ1169A.agda:80-82`). Nothing in `src/`
supplies it. A `Formula Code 1` for `𝒟ₒ` is a second debt. The
brief forbids funding it here. `[LJ-1.664]` measured `DefAt` at 166
constants (`agents/tasks/LJ-1-664/Probe664.agda:62-63`).

Either `Describes` unpaid or `PowIter` unpaid is enough. Both are
unpaid. `from-iter` shows they are the same supplier at the
limit-stage consumer.

---

The next brief should not re-dispatch `powiter-status` as a closed
term until it names a supplier for `Describes` (or for `PowIter`).
The consumer is paid. The stage-member case is paid. The empty set
is paid. The arbitrary member is not.
