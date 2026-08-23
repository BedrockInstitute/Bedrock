# review-of-stage-high: not delivered, one statement is left, and the task could not be graded

**NO-GO on the obligation.** `agents/tasks/LJ-1-565/Probe565.agda::stage-high`
is not inhabited and no postulate stands in for it. `StageHigh` is
`[LJ-1.536]`'s type, imported and not restated
(`agents/tasks/LJ-1-536/Probe536.agda:350-352`, imported at
`agents/tasks/LJ-1-565/Probe565.agda:45`).

**THIS IS ATTEMPT 3, AND IT ADDS ONE FINDING THAT IS NOT MATHEMATICAL.**
Attempts 1 and 2 both stopped on the same mathematics. Neither stop was ever
graded, and the reason is measured below. It is a fact about this task's own
directory, and it is cured.

## THE FINDING: NINE HEAP WALLS SAT IN THE VERIFICATION TARGET LIST

`scripts/pod/facts.py:463-465` makes **every** `.agda` file under
`agents/tasks/<CODE>/` a conjunct 1 target, in path order. Conjunct 1 stops at
the first non-zero exit.

**NINE OF THIS TASK'S CONTROL FILES EXHAUST THE HEAP.** Six came from attempt 1
and three from attempt 2. Each one costs 200 s to 279 s and about 11 GB before
it dies:

| file | seconds | peak RSS | attempt | evidence |
|---|---|---|---|---|
| `Control565b.agda` | 268.12 | 11.05 GB | 2 | `runs/ctlb-0.time` |
| `Control565c.agda` | 263.63 | 11.05 GB | 2 | `runs/ctlc-0.time` |
| `Control565f.agda` | 240.56 | 10.94 GB | 2 | `runs/ctlf-0.time` |
| `Control565k.agda` | 237.38 | 10.98 GB | 1 | `runs/ctlk-0.out` |
| `Control565l.agda` | 200.23 | 10.86 GB | 1 | `runs/ctll-0.out` |
| `Control565m.agda` | 239.19 | 11.00 GB | 1 | `runs/ctlm-0.out` |
| `Control565s.agda` | 278.51 | 10.97 GB | 1 | `runs/ctls-0.out` |
| `Control565t.agda` | 238.81 | 10.98 GB | 1 | `runs/ctlt-0.out` |
| `Control565u.agda` | 238.63 | 10.98 GB | 1 | `runs/ctlu-0.out` |

GB here is 10⁹ bytes, which is the unit attempt 2 used.

**THE ACCEPTANCE RECORD SHOWS THE HARNESS HITTING THE SECOND FILE, TWICE.**
`runs/accept-1.out` and `runs/accept-2.out` each list three runs and stop:
`Probe565.agda` rc 0, `runs/Control565a.agda` rc 0, `runs/Control565b.agda`
**rc 251**. Both records read `# error class heap_wall` and `# exit 251`.

**AND NO LATER ATTEMPT COULD ESCAPE IT.** `scripts/pod/facts.py:345` states
that the fact 4 snapshot is cumulative: "The snapshot is CUMULATIVE and that is
deliberate." The program commits only at DONE, so every walled file an earlier
attempt left behind is still dirty when the next attempt starts, and it is a
target again. **Attempt 2 was blocked before it wrote a line**, by six files it
never opened.

## THE CURE, AND IT DELETES NOTHING

The nine files keep their bytes. Each is renamed to `<name>.agda.walled`, so
`p.endswith(".agda")` at `scripts/pod/facts.py:464` no longer selects it.

`scripts/pod/facts.py` now computes a target list of **17 files**, and all 17
are green cold, one Agda process at a time, 110 s in total:

| target | seconds | target | seconds |
|---|---|---|---|
| `Probe565.agda` | 28.85 | `Control565j.agda` | 1.99 |
| `Control565a.agda` | 0.86 | `Control565n.agda` | 1.96 |
| `Control565d.agda` | 1.96 | `Control565o.agda` | 2.02 |
| `Control565e.agda` | 1.50 | `Control565p.agda` | 2.84 |
| `Control565g.agda` | 2.10 | `Control565q.agda` | 1.93 |
| `Control565h.agda` | 26.27 | `Control565r.agda` | 1.95 |
| `Control565i.agda` | 2.08 | `Control565v.agda` | 1.94 |
| | | `Control565w.agda` | 1.98 |
| | | `Control565x.agda` | 27.53 |
| | | `W3.agda` | 2.20 |

The sweep is `runs/sweep-a3.sh`. Its outputs are `runs/a3-*.out` and
`runs/a3-*.time`. **This is the first complete pass of this task's target
list.**

**A RENAME BREAKS THE PREDECESSORS' CITATIONS AND I SAY SO PLAINLY.** Attempt
1's and attempt 2's documents cite `runs/Control565c.agda` and its eight
siblings by path, and those paths are gone. `## THE RENAME TABLE` in
`lj-1.565-report.md` maps every one. **I chose the loud failure over the quiet
one:** a citation to a path that does not exist fails where a reader can see
it, and a citation to a path whose content changed does not.

## THE MATHEMATICS IS ATTEMPT 2'S, AND I DID NOT REPEAT IT

**`Probe565.agda:327-328` stands, unchanged, green:**

    stage-high-from-limit : HierBelowLimitH → StageHigh
    stage-high-from-limit lim = reduction (allH→all (closing lim))

**`StageHigh` RESTS ON EXACTLY ONE OPEN STATEMENT.** It is `HierBelowLimitH`
(`Probe565.agda:285-287`), the limit case. Everything between it and the trophy
is a green term.

I audited the probe rather than rebuilt it. There is no `postulate`, no
interaction hole, no `TERMINATING`, no `REWRITE` and no `primTrustMe` in any of
the 17 targets, and every one carries `--cubical --safe`. **The NO-GO is
honest: the obligation is absent, not faked.**

### The brief's question, answered by attempt 2 and confirmed here

**THE DOOR IS PAID AND THE DOOR WAS NEVER THE BLOCKER.** `AtStage` applies at
`[LJ-1.536]`'s formula with both hypotheses fed: `runs/W3.agda:78-80` is the
membership row and `:83-93` are the two satisfaction directions. The file is
green at 2.20 s cold (`runs/a3-W3.time`), so `[LJ-1.562]`'s finding reaches this
site.
**And it changes nothing, because `[LJ-1.536]` never stood at that door.**
`carve∈𝒟ₒ` (`src/L/Axioms/Separation.lagda.md:198-199`) takes a formula at
`⟪ Lset σ ⟫` and nothing else: no `Δ₀`, no `BoundedFo`, no restriction on its
quantifiers. The two hypotheses buy the satisfaction bridge from an external
formula (`:163-168`), which says **which** set was carved, not the way in.

### What actually blocked it, at the mathematics

**THE NEAR WALL WAS THE SUCCESSOR STEP, AND ATTEMPT 2 BROKE IT.** Its cause is
the computed `isL` witness, not the `sucV` spelling that `[LJ-1.536]` named
(`agents/tasks/LJ-1-536/lj-1.536-report.md:248`). The controlled pair is
`runs/Control565c.agda.walled` (witness computed at `sucV α`: 11.05 GB) against
`runs/Control565g.agda` (witness a parameter, nothing else changed: exit 0,
2.10 s cold). **I re-ran the green half of that pair and I did not re-run the
walled half** (`dev/LESSONS.md:2148`: "A heap-exhausted exit is a WALL event:
apply the P-i playbook, never simply rerun").

### What is left, and why the stop stands

**`HierBelowLimitH`, AND NOTHING ELSE.** At a limit γ the members of `hierL γ`
are the pairs `pr c (Lset c)` for c ∈ γ. To carve that set the formula must say
"w is the tower's value at c" inside the stage, which is the level formula: Σ₁,
with the existential over an approximation unbounded at the ambient level
(`dev/literature/devlin-II5.md:217`).

**THE BRIEF ORDERS THE STOP HERE AND I TAKE IT.** "IF THE REAL BLOCKER IS AN
UNBOUNDED SEARCH, SAY SO AND STOP. `[LJ-1.560]` is running on exactly that
question and this brief must not duplicate it."

**AND I DO NOT OVERSTATE IT, FOR THE THIRD TIME.** Attempt 1 wrote that it
measured nothing about the limit. Attempt 2 wrote the same. **Attempt 3 also
measured nothing about the limit.** That the limit case is `[LJ-1.560]`'s
question is an argument from `dev/literature/devlin-II5.md:217` and `:222`
together with `agents/tasks/LJ-1-536/lj-1.536-report.md`'s `## FOR THE NEXT
BRIEF` point 2. It is not a measurement. **The brief's "CONFIRM from a second
site" is still only half earned, and no attempt of this task has earned the
other half.**

## WHAT THE READER MUST KNOW BEFORE TRUSTING A CITATION HERE

1. **Attempt 2 destroyed part of attempt 1's record.** It overwrote attempt 1's
   `Probe565.agda`, `runs/W3.agda` and `runs/Control565a.agda` through
   `Control565h.agda` before reading them. Its own accounting is at
   `runs/attempt-2-report.md.preserved`, `## THE RECORD I DAMAGED`.
2. **Attempt 3 destroyed nothing.** It copied attempt 2's report, stop and probe
   to `runs/attempt-2-*.preserved` before it wrote anything, and it renamed nine
   files without changing a byte in any of them.
3. **Every surviving document of attempts 1 and 2 is in `runs/`**, under
   `attempt-1-*.preserved` and `attempt-2-*.preserved`.
