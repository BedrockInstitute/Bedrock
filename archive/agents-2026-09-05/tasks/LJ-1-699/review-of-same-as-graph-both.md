# review-of-same-as-graph-both: a STATED NO-GO, the reverse sits in a sibling worktree

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.699
obligation: agents/tasks/LJ-1-699/Probe699.agda::same-as-graph-both
verdict: **NO-GO on the paired term. GO on the frame and on the forward conjunct.**

The obligation asks for the equivalence with both directions written out and the
union of their hypotheses. I wrote the union of the hypotheses as one type, I
supplied the forward conjunct from `[LJ-1.690]` (imported, green), and I named
the reverse conjunct. The reverse term is **not written**: it is delivered in the
sibling worktree `LJ-1-685`, which is not on this worktree's include path, so it
cannot be imported here. The witness meter reads `1 UNRESOLVED of 1, probe_red=False`
(`runs/meter-obligation.out:2`). The probe is green and has no hole; the obligation
is the reverse half, and that half is a path, not a term.

**THIS IS NOT A REFUTATION OF `SameAsGraph`.** The equivalence is not false. Both
directions are delivered, each green in its own worktree: the forward is `[LJ-1.690]`
in this tree, the reverse is `[LJ-1.685]` in the sibling. The NO-GO is on building
the pair in this worktree. The frame is proven compatible at the type level; the
only gap is the reverse's term, and it is a path into another checkout.

The critic reads this file. It does not close the task.

---

## 1. What the obligation asks, and what is here

The obligation is one term, `same-as-graph-both`, of type
`PowIterHyp → IsOrd (fst (lookup b γ)) → Bridge-UP → Bridge-DOWN → SameAsGraph w b γ`
(`runs/FLOOR.agda.txt:69-74`). The two bridges are the two directions' own:
`Bridge-UP` is `[LJ-1.690]`'s `Pin.Bridge` (`graphBndAt → LsetGraphAt`), and
`Bridge-DOWN` is `[LJ-1.685]`'s bridge (`LsetGraphAt → graphBndAt`).

What is in `Probe699.agda` (green, `runs/p-1.out`, EXIT 0):

- `module At` (`Probe699.agda:52`), the union of the two directions' hypotheses,
  written once at a generic `{n} w b γ`. `Mx` is the shared matrix (`:54`), `FPin`
  is the forward's `Pin` (`:55`), `M = 13 + n` (`:58`).
- `same-as-graph-forward` (`:65-74`), the forward conjunct, **supplied from
  `[LJ-1.690]`**: it is the predecessor's own term `FPin.same-as-graph-forward-at`.
  Inhabited. Sigma-1 to graph.
- `Bridge-DOWN` (`:76-79`), the reverse's bridge, restated by hand. The type is
  `[LJ-1.685]`'s own `Bridge` (sibling `Probe685.agda:66-69`).
- `same-as-graph-reverse` (`:85-91`), the reverse conjunct, **named, not inhabited**.
  It is a type. Its value is `[LJ-1.685]`'s `same-as-graph-reverse-at` (sibling
  `Probe685.agda:71-76`), which is green in the sibling but unreachable here.
- the paired term `same-as-graph-both` is **not written** (`:93-103`, commented):
  its second component is a value of `same-as-graph-reverse`.

So the probe holds the forward (a term) and the reverse (a name), and the frame that
ties them. What it does not hold is the pair, because the pair's second half is a
term that lives in another worktree.

## 2. The blocker: the reverse is in a sibling worktree

The reverse was delivered by `[LJ-1.685]`. Its term is real and green:
sibling `runs/p-3.out` records `Checking LJ-1-685.Probe685 ... 71.29 real ... EXIT=0`
(833 MB peak). The `[LJ-1.690]` report names it directly: "reverse | graph to
Sigma-1 | sibling `Probe685.agda:71-76` | GO as a term; report line stale"
(`agents/tasks/LJ-1-690/lj-1.690-report.md:89`). The `[LJ-1.695]` report states the
separation plainly: "`[LJ-1.685]` is not a file in this worktree. The sibling
worktree `LJ-1-685` has `Probe685.agda:71`" (`agents/tasks/LJ-1-695/lj-1.695-report.md:77-78`).

The separation is structural, not incidental:

- The include path is `src agents/tasks` (`bedrock.agda-lib:2`). So
  `import LJ-1-685.Probe685` resolves to `agents/tasks/LJ-1-685/Probe685.agda`,
  which is absent in this worktree.
- `git worktree list` shows `LJ-1-685` at `9e4bb94b` and this worktree
  `LJ-1-699` at `cfd6fa96`. The two checkouts do not share the task's home.
- `git log -- agents/tasks/LJ-1-685/` in this worktree is empty: the task's home
  was never in this tree.

A thin glue that imports the reverse would write `import LJ-1-685.Probe685` and fail
at the include path. Re-landing the reverse here would re-land a completed task
(its machinery already imports `[LJ-1.672]` and `[LJ-1.678]`, both present here),
which is beyond the 80-180 line glue the brief priced. So the paired term is
unbuildable in this worktree.

## 3. What the measurements show

One Agda process at a time, `GHCRTS="-A64m -I0 -M2g"` (wide tier, set by the
program, untouched here):

- **Floor** (`runs/FLOOR.agda.txt`, `runs/floor-1.out`): the full obligation type
  with the body a hole. `55.81 real`, peak `827883520` bytes, 38.6 percent of the
  2g wide cap, EXIT 42 at exactly the one hole (`FLOOR.agda:75`). It elaborated the
  whole forward graph: `LJ-1-520`, `LJ-1-690`, and `LJ-1-690.runs.{DROP,RENAME3,
  UNPACK,UNPACKAT}`. The frame is well-formed.
- **Probe** (`Probe699.agda`, `runs/p-1.out`): green, EXIT 0. Forward warm 2.48 s,
  peak `626900992` bytes, 29.2 percent. The forward conjunct is inhabited; the
  reverse is named.
- **Witness meter** (`runs/meter-obligation.out`): `1 UNRESOLVED of 1, 2.31 s,
  probe_red=False`. The obligation is `NotInScope` because the reverse term is not
  in the probe.

**The partial answer to W3.** The floor shows the two bridges coexist in ONE type at
the SAME matrix `Mx` (arity `13 + n`, slots `sh13 w`, `sh13 b`) with the same
`SameAsGraph` conclusion, with no third bridge in the type. So at the type level the
two telescopes meet without a third bridge. The premise's asymmetry note
(`[LJ-1.695]`: the two spend different site facts, UP and DOWN) shows in the frame
only as two hypothesis arguments; it does not split the matrix. The term-level
meeting is the reverse's value, and that is blocked by the worktree, not by the
matrix.

## 4. D-10: the target is true; state it correctly

I priced the truth of the target before I priced its proof. The target is true:
the forward and the reverse are each delivered, each green in its own worktree.
So the NO-GO is not a refutation. The corrected target is: **the paired `SameAsGraph`
is buildable in a worktree where the homes of `[LJ-1.690]` and `[LJ-1.685]` both
resolve.** Everything needed for that build is in the tree across the two checkouts:
the forward term, the reverse term, the shared matrix, and the frame. The supply of
`SameAsGraph` stays 0 in this worktree and would become 1 where the pair can close.

This is a one-site measurement: it says the pair cannot close in `LJ-1-699`. It says
nothing about the number of worktrees with the same separation; `[LJ-1.695]` already
recorded the same separation, so the pattern is known. The cure is a dispatch policy,
not a per-task term.

## 5. What the next brief should fund

- Fund a worktree where both task homes resolve: co-locate the homes of
  `[LJ-1.690]` and `[LJ-1.685]` (or land the `[LJ-1.685]` probe into the mainline and
  re-dispatch the glue on that commit). Then the obligation is the two-line pair in
  `Probe699.agda:93-103`, with the reverse imported, not restated.
- Do not re-land `[LJ-1.685]`'s machinery into this worktree by hand. Its reverse is
  a delivered, green term; re-landing it re-lands a completed task.
- Do not re-dispatch the forward from `[LJ-1.690]`. It is imported and green here.
- Price the next brief at the frame, which is measured at 55.81 s and 827 MB
  (`runs/floor-1.out`), not at a re-derivation of either direction.

This file is the critic's input and it does not close the task.
