# Review of `defat-fill-in-bound`

## HEAD

task: LJ-1.733
reviewed name: agents/tasks/LJ-1-733/Probe733.agda::defat-fill-in-bound
verdict: **NO-GO, STATED.** The obligation's type is FALSE-SCOPED at
the brief's offered hypothesis set: two of its three module hypotheses
are FALSE by their predecessors' NO-GO reports, and the third has no
delivered type from any probe. The coder clause (a module hypothesis
taken from a predecessor is the type that predecessor delivered; if
the report is NO-GO or names the statement FALSE, stop and do not
inhabit) fires, so no inhabitant is written and none is possible at
this scope without absurdity: the premise set is INCONSISTENT,
machine-checked at this task's own restated type by
`envSet-hypothesis-closes-bottom`
(agents/tasks/LJ-1-733/Probe733.agda:308-311), green at EXIT=0
(`agents/tasks/LJ-1-733/runs/p-2.out`). Nothing here re-funds
`stage-read`, the unbounded `fill`, or any corrected scope.

## 1. The clause fires twice

The brief's obligation is the bounded fill, taken under three module
hypotheses, each to be restated from its predecessor's delivery:

1. `keyS-in-carrier-stage`: the predecessor report is
   `agents/tasks/LJ-1-729/review-of-keyS-in-carrier-stage.md`, whose
   HEAD records "**NO-GO, STATED.** The brief's type is FALSE at its
   stated generality." The corrected scope `keyS-in-carrier-lim` under
   `closedω γ` is INHABITED in that probe. The type the 733 brief
   wants restated is the REFUTED one, not the corrected one.
2. `envSet-in-carrier-stage`: the predecessor report is
   `agents/tasks/LJ-1-730/review-of-envSet-in-carrier-stage.md`, whose
   HEAD records "**NO-GO. The target is FALSE as stated.**" with a
   machine-checked refutation at `γ = sucV (sucV ω)`
   (`agents/tasks/LJ-1-730/Probe730.agda:208`).

Two of three. The clause reads: if the report is NO-GO, or names the
statement FALSE, stop and say so with `file:line`; do not inhabit the
brief's type in that case. The reason is not ceremony: with hypothesis
2 in the premise list, the obligation's type is inhabited by absurdity
elimination, so an "inhabitant" would carry no membrane crossing at
all -- it would let a downstream reader import a theorem name that
rests on a refutable hypothesis.

## 2. The third hypothesis has no delivered type

`Sat-in-carrier-stage` ([LJ-1.731]) has no probe, no report and no
review in any worktree: the 731 task directory carries only the brief
(`.pod-state/worktrees/LJ-1-731/agents/tasks/LJ-1-731/LJ-1.731.md`).
The clause says to take the type from the probe that typechecked; no
such probe exists. This probe transcribes the type from the 731
brief's obligation block and labels it as such
(`Probe733.agda:156-160`), because the obligation's own type names it;
but a hypothesis with no delivered type and no verdict is a premise
the tree cannot yet support, and that is its own stop ground.

## 3. The W3 measurement

The brief's W3: whether the three stage-bound hypotheses plus
`relativize-correct` close bounded `fill`. Measured answer: the
question's premise set is inconsistent, so the "closure" it offers is
vacuity. From a hypothesis of type `envSet-in-carrier-stage` ALONE,
`Empty.⊥` closes -- `Probe733.agda:308-311` instantiates the restated
hypothesis at 730's counterexample (`γ = sucV (sucV ω)`,
`A = Lset (sucV ω)`, `n = 1`, all three satisfying the brief's
`ω ∈ˢᵥ γ`) and runs the rank chain, rebuilt at this file from landed
masters only (`:229-301`): four `rank-mono` links climb from
`rank ω` to the rank of the environment set, `rank-Lset` pins the
last inside `γ₂`, two `∈sucV-elim` descents and the ordinal's
transitivity leave `rank ω ∈ˢᵥ ω`, and `rank-fix` with `∈-irrefl`
closes. This is C-42's sweep duty paid at the second site: the false
shape is now measured at keyS (external verdict, 729) and envSet
(machine-checked, twice -- 730 and here). The Sat site is unmeasured;
its probe was never built.

What stays open: whether the ASSEMBLY goes through at the CORRECTED
scopes. That is not decidable here. The corrected shapes are on
record but not settled: keyS has a landed corrected scope
(`keyS-in-carrier-lim`, closedω γ), envSet has three proposed shapes
awaiting the mathematician's ruling (730 review, "The corrected
target, for ruling"), and Sat has nothing. Inventing corrected shapes
to finish the assembly would be inventing a specification.

## 4. What the next brief needs

1. Rule the corrected bound family's scope first (the three 730
   shapes, or a fourth), and state in the brief WHICH delivered probe
   each restated hypothesis comes from.
2. Close or retire [LJ-1.731] before any brief cites its type again.
3. Then re-brief the bounded fill at the ruled scopes; the assembly's
   per-conjunct consumption is on record (the relativized `DefBody`'s
   two existentials want the `Sat` value and the key inside
   `Lset γ`, brief LJ-1.733 premise 2, `src/L/Coding/Powerset.lagda.md:442`).
   Price after the ruling, not before.
4. Do not re-fund `relativize-correct`, unbounded `fill`, the rank
   chain (green at two sites), or `keyS-in-carrier-lim`.
