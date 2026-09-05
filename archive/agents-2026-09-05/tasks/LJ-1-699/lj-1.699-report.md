# LJ-1.699 report: the equivalence, both directions, with its real bill

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.699
obligation: agents/tasks/LJ-1-699/Probe699.agda::same-as-graph-both
verdict: **NO-GO on the paired term. GO on the frame and on the forward conjunct.**

Written as a report after the measurement (C-22). No commit, no push. I write only
inside `agents/tasks/LJ-1-699/`. Agda runs under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a time. I did not
set `GHCRTS`. Nothing is postulated. Nothing lands in `src/`. The probe is a raw
`.agda` file, so it carries no fence, counts 0 in-fence lines, and the ratio bar
cannot fire on it.

The obligation is one term, `same-as-graph-both`: the equivalence `SameAsGraph`
with both directions written out and the union of their hypotheses. I wrote the
union of the hypotheses as one type, I supplied the forward conjunct from
`[LJ-1.690]` (imported, green), and I named the reverse conjunct. The paired term is
not written: the reverse is delivered in the sibling worktree `LJ-1-685`, which is
not on this worktree's include path. The witness meter reads `1 UNRESOLVED of 1,
probe_red=False`. The review states the NO-GO.

## What was measured

One Agda process at a time, wide tier, `GHCRTS="-A64m -I0 -M2g"` set by the program:

| Measure | File | Wall | Peak | Exit |
|---|---|---|---|---|
| Floor, the obligation type with a hole | `runs/FLOOR.agda.txt`, `runs/floor-1.out` | 55.81 s | 827883520 B, 38.6% of 2g | 42, one hole at `FLOOR.agda:75` |
| Probe, the forward conjunct (warm) | `Probe699.agda`, `runs/p-1.out` | 2.48 s | 626900992 B, 29.2% | 0, green |
| Witness meter | `runs/meter-obligation.out` | 2.31 s | n/a | 1 UNRESOLVED of 1, `probe_red=False` |

The floor elaborated the whole forward graph: `LJ-1-520`, `LJ-1-690`, and
`LJ-1-690.runs.{DROP,RENAME3,UNPACK,UNPACKAT}`. The frame is well-formed; the single
unsolved meta is the hole standing in for the paired body. The forward conjunct is
inhabited (it is `[LJ-1.690]`'s own term, imported). The reverse conjunct is named,
not inhabited: its value is `[LJ-1.685]`'s `same-as-graph-reverse-at`, green in the
sibling (sibling `runs/p-3.out`, EXIT 0) and unreachable here.

## The blocker, in one paragraph

The reverse is in a sibling worktree. `import LJ-1-685.Probe685` resolves, by the
include path `src agents/tasks` (`bedrock.agda-lib:2`), to `agents/tasks/LJ-1-685/
Probe685.agda`, which is absent in this worktree. `git worktree list` shows `LJ-1-685`
at `9e4bb94b` and this worktree at `cfd6fa96`; `git log -- agents/tasks/LJ-1-685/`
in this tree is empty. `[LJ-1.695]` states it plainly (`agents/tasks/LJ-1-695/
lj-1.695-report.md:77-78`); `[LJ-1.690]` names the reverse as "sibling" and "GO as a
term; report line stale" (`agents/tasks/LJ-1-690/lj-1.690-report.md:89`). So the
pair's second half is a path into another checkout, not a term I can write here.
Re-landing the reverse would re-land a completed task; it is beyond the 80-180 line
glue the brief priced.

## W2: the shared machinery is written once

The two directions are written so the shared machinery is written once and
instantiated by each. `module At` (`Probe699.agda:52`) is the generic carrier
`{n} w b γ`. Inside it, `Mx` is the single shared matrix (`:54`), `M = 13 + n`
(`:58`), and `sh13` lifts the slots once. The forward conjunct (`:65-74`) is the
predecessor's own `FPin.same-as-graph-forward-at`, which instantiates that same
matrix from `[LJ-1.520]`/`[LJ-1.690]`. The reverse conjunct (`:85-91`) is named at
the same carrier and the same matrix. No `fin7` and no cross-arity lift was needed,
because the forward is imported whole and the reverse is named rather than built.

## W3: the partial answer, at the type level

The floor shows the two bridges coexist in ONE type at the SAME matrix `Mx` (arity
`13 + n`, slots `sh13 w`, `sh13 b`) with the same `SameAsGraph` conclusion and no
third bridge in the type. The two directions share the carrier `γ`, the slots `w b`,
the `IsOrd` at slot `b`, and the endpoints `levelFo` and `LsetGraphAt w b`; the only
distinct arguments are the two bridges (UP, DOWN). So at the type level the two
telescopes meet without a third bridge. The premise's asymmetry note (`[LJ-1.695]`:
the two spend different site facts) shows only as two hypothesis arguments and does
not split the matrix. The term-level pair is the reverse's value, blocked by the
worktree, not by the matrix.

## W4: no third structure, no module retired

The pair does not force a third structure. The two bridges coexist at the single
`Mx` matrix (arity `13 + n`), the only known site where both directions share a
matrix. Because I did not build the pair (NO-GO), no module is retired.

## Ratio bar

Nothing lands in `src/`. The probe is a raw `.agda` file with no fence, so it counts
0 in-fence lines and the CJK ratio bar cannot fire.

## Corrected target, for the next brief (D-10)

The target is true: both directions are delivered, each green in its own worktree.
The corrected target is: the paired `SameAsGraph` is buildable in a worktree where the
homes of `[LJ-1.690]` and `[LJ-1.685]` both resolve. The supply of `SameAsGraph` stays
0 in this worktree and would become 1 where the pair can close. Fund the next brief at
the frame, measured at 55.81 s and 827 MB (`runs/floor-1.out`), not at a
re-derivation of either direction. Co-locate the two task homes (or land the
`[LJ-1.685]` probe into the mainline and re-dispatch on that commit). Do not re-land
`[LJ-1.685]`'s machinery and do not re-dispatch the forward.

## ARCHIVE USED

The build surfaced five candidates under `archive/dev/`. I named each and decided.

- `archive/dev/ORCHESTRATION.md` (score 155.110): **declined.** It is the dispatch
  and harness policy (the tier switch, the in-harness refusal rule); it does not cover
  the co-location of task homes across worktrees. The worktree policy I needed is in
  the live `dev/pod/orchestrator.md`, which I read; this archive copy is superseded by
  it and adds nothing to the worktree-separation blocker.
- `archive/dev/DD-archived.md` (score 148.019): **declined.** Archived design doc; the
  live design is `dev/memos/LJ-4-pod-program-design.md`. Nothing in it changes the
  worktree-separation blocker.
- `archive/dev/PLAN-archived.md` (score 132.736): **declined.** Archived plan; the live
  state is `dev/pod/screen.toml` and `dev/pod/queue.toml`, which I read. Superseded.
- `archive/dev/TASKS-archived.md` (score 125.291): **declined.** Archived task ledger;
  the live task home and the sibling worktree are the sources I used. Superseded.
- `archive/dev/STATUS-archived.md` (score 111.818): **declined.** Archived status; the
  live status is `dev/pod/screen.toml`, which I read. Superseded.

## LITERATURE USED

The build surfaced five candidates under `dev/literature/`. This task is a
buildability blocker (a worktree-separation path), not a mathematical question, so I
used none. I named each and declined.

- `dev/literature/primary-sources.md` (score 37.796): **declined.** The Jensen, Devlin
  and Jech manuscript sources for the rud route; the blocker is a checkout path, not a
  source question.
- `dev/literature/level-formula-slot-roles.md` (score 34.791): **declined.** Slot roles
  in the level formula; the two directions share the matrix and the endpoints, and the
  blocker is the reverse's location, not a slot role.
- `dev/literature/devlin-errata.md` (score 32.273): **declined.** Errata on the Devlin
  text; not needed for a worktree-separation NO-GO.
- `dev/literature/glossary-review-2026-08.md` (score 31.331): **declined.** A glossary
  review; I add no term and choose none.
- `dev/literature/BIBLIOGRAPHY.md` (score 23.673): **declined.** The bibliography
  index; no citation is needed for a worktree-separation blocker.

## Return

The obligation is one term, `same-as-graph-both`. I built its frame (the union of the
two directions' hypotheses, one type, well-formed at 55.81 s / 827 MB) and I supplied
the forward conjunct from `[LJ-1.690]` (imported, green). The reverse conjunct is
named, not inhabited: its term is `[LJ-1.685]`, green in the sibling worktree and
unreachable here. The paired term is therefore not written in this worktree. Verdict
is a STATED NO-GO on the pair, a GO on the frame and the forward. This is not a
refutation of the equivalence; both directions are delivered. The next brief should
fund a worktree where both task homes resolve, price the glue at the measured frame,
and neither re-land the reverse nor re-dispatch the forward.
