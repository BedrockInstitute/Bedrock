# LJ-1.709 report: the equivalence, assembled from the two committed halves

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.709
obligation: agents/tasks/LJ-1-709/Probe709.agda::same-as-graph-both
verdict: **GO.** `same-as-graph-both` is written and green:
`Pin.same-as-graph-both` (`Probe709.agda:67`, exported at `Probe709.agda:77`),
one telescope at the union of the two directions' hypotheses, concluding
`P520.SameAsGraph w b γ`. The probe checks clean: `EXIT=0`
(`runs/p-1.out:23`), 2.85 s wall (`runs/p-1.out:5`), peak 554,500,096 B,
25.8 percent of the 2 g wide cap (`runs/p-1.out:6`). The floor carries exactly
ONE unsolved meta, the designed hole at `runs/FLOOR.agda.txt:49`
(`runs/floor-4.out:7`, `EXIT=42` at `runs/floor-4.out:26`). No heap wall was
met anywhere in this task.

**I DID NOT write `review-of-same-as-graph-both.md`.** The obligation is
inhabited. A `review-of-*.md` is how a coder states a NO-GO
(`agents/tasks/LJ-1-703/lj-1.703-report.md:19-20`). This return is GO.

Written as a skeleton before any Agda run and filled as each answer landed
(C-22). No commit, no push. I wrote only inside `agents/tasks/LJ-1-709/`. Agda
ran under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"`,
the WIDE tier, ONE Agda process at a time. I did not set `GHCRTS`. Nothing is
postulated, the probe carries `--safe` and no hole, and nothing lands in
`src/`. The probe is a raw `.agda` file, so it carries no fence, counts 0
in-fence lines, and the ratio bar cannot fire on it.

## What this task changes against LJ-1.699

`[LJ-1.699]` had all three pieces but could not reach one of them: it wrote
the union of the hypotheses as one type and supplied the forward conjunct from
`[LJ-1.690]`, imported green (`agents/tasks/LJ-1-699/lj-1.699-report.md:20`),
but its reverse sat in the sibling worktree `LJ-1-685`, which is not on a
dispatch's include path (`agents/tasks/LJ-1-699/lj-1.699-report.md:22`). That
was an address failure, not a proof failure.

The address now exists in git. `[LJ-1.703]` re-derived the reverse and closed
done; `commit_task()` commits a task's files only on a done close
(`scripts/pod/pod.py:3673`, entry `scripts/pod/pod.py:3263`), so THIS worktree
carries the tracked file `agents/tasks/LJ-1-703/Probe703.agda`, whose last
line exports `same-as-graph-reverse` (`agents/tasks/LJ-1-703/Probe703.agda:90`).
Under the include path `src agents/tasks` (`bedrock.agda-lib:2`) that file
imports as module `LJ-1-703.Probe703`.

The assembly takes each piece from its committed address and rebuilds none:

- the forward conjunct from `[LJ-1.690]`, `FPin.same-as-graph-forward-at`;
- the reverse conjunct from `[LJ-1.703]`,
  `RPin.same-as-graph-reverse-at`, with `[LJ-1.703]`'s own DOWN `Bridge`
  type, not a restatement and not anything from `[LJ-1.685]`;
- the union telescope from `[LJ-1.699]`'s sketch
  (`agents/tasks/LJ-1-699/Probe699.agda:96-98`), unchanged in shape;
- both predecessor pins instantiate `P520.Slots` (`Probe690.agda:55`,
  `Probe703.agda:57`), so the two halves already shared one carrier before
  this task began.

## What was measured

One Agda process per run, sequential through every run below. Floors 1 to 3
carry priced numbers only for their environment record: the Agda process died
by an external signal before any verdict, so none of them prices anything.
Rows 1 to 3 and row 5 come through `runs/run.sh`; row 4 through
`runs/run-diag.sh`, whose only difference is that bash's wait(1) reports the
child exit directly (no `/usr/bin/time` between perl and agda).

| Row | Measure | File | Wall | Peak | Exit |
|---|---|---|---|---|---|
| 1 | Floor attempt 1 | `runs/floor-1.out` | 10.56 s | 659,554,304 B | killed by external signal, no verdict |
| 2 | Floor attempt 2 | `runs/floor-2.out` | 21.08 s | 676,724,736 B | killed by external signal, no verdict |
| 3 | Floor attempt 3 | `runs/floor-3.out` | 21.45 s | 554,139,648 B | killed by external signal, no verdict |
| 4 | Frame, cold full elaboration | `runs/diag-1.out` | about 128 s (06:47:03Z to 06:49:11Z) | not captured | 42, the hole only |
| 5 | Floor, warm | `runs/floor-4.out` | 2.77 s | 598,343,680 B, 27.9 percent | 42, one hole |
| 6 | Probe, the assembled pair | `runs/p-1.out` | 2.85 s | 554,500,096 B, 25.8 percent | 0, green |

The kill signature on rows 1 to 3: time(1) reports
"command terminated abnormally" and "signal: Invalid argument"
(`runs/floor-1.out:9,28`, `runs/floor-2.out:7,26`,
`runs/floor-3.out:8,27`), always under 22 s, always under 700 MB peak
against the 2048 MB cap, never with any Agda diagnostic. That box state sat at
swap 16.9 GB used of 17.4 GB and near-zero free pages at the first two
attempts, and the unified log records host-wide jetsam churn in the same
minutes. The identical frame completed cold on row 4 in the next window. So
rows 1 to 3 are environment facts, and no price here rests on them.

Row 5 re-took the floor through the standard harness once warm
(`runs/floor-4.out:7`: the single error is
`[UnsolvedInteractionMetas] at FLOOR.agda:49.24-28`, the designed `{!!}`).
Every dependency elaborates under the assembled frame: `LJ-1-520.Probe520`,
`LJ-1-690.Probe690` with its runs chain, and `LJ-1-703.Probe703` with its
runs modules, all present because tracked. Row 6 then checked the delivered
probe against cached interfaces. The copies of `FLOOR.agda` used during runs
were removed after each run, so every `.agda` file under this task home at
close is the delivered probe alone.

## W2: the shared machinery is written once

Answer: yes, and the assembly spends nine lines beyond the imports. One
generic carrier `module Pin {n} w b γ` (`Probe709.agda:58`) opens both
predecessor pins at the same slots; `Sl`/`Mx` are instantiated inside
`LJ-1-690.Probe690` and `LJ-1-703.Probe703`, which both instantiate
`LJ-1-520.Probe520`'s `Slots`. My file holds no matrix arithmetic of its own:
no arity constant, no slot lift, no formula. The obligation term body is one
pair clause (`Probe709.agda:73-75`), the forward conjunct dropping the DOWN
bridge, the reverse conjunct dropping the UP bridge. Instantiating by nothing:
the obligation IS the generic statement.

## W3: the widest unmeasured term, answered GO

The brief asked whether the two directions' hypotheses genuinely union, or
whether the reverse needs a frame the forward cannot supply. Measured, not
argued: the union telescope TYPE-CHECKED against both conjuncts on its first
elaboration, before any body existed (row 5: the only complaint is the hole).
So:

1. ONE `PowIterHyp` argument serves BOTH conjuncts: `[LJ-1.690]`'s and
   `[LJ-1.703]`'s spellings unfold to the same type and Agda accepts one
   value for both. No duplicate hypothesis argument exists anywhere.
2. ONE `IsOrd (fst (lookup b γ))` argument serves both.
3. The two bridges coexist as two independent hypothesis arguments
   (`FPin.Bridge` UP, `RPin.Bridge` DOWN) at the SAME matrix `Mx`, arity
   `13 + n`. Neither direction needed a third bridge, a coercion, or a glue
   lemma; the reverse consumed its own bridge type verbatim.
4. The conclusion of both halves met in one pair at
   `P520.SameAsGraph w b γ` (`agents/tasks/LJ-1-520/Probe520.agda:192-195`)
   with no transport.

NO-GO would have earned the frame mismatch as a term. There is no mismatch to
earn: both importable deliveries were made at the same carrier, because both
descend from `[LJ-1.699]`'s own W2 note (`agents/tasks/LJ-1-699/
lj-1.699-report.md:56-58`).

## Consequences for CompletenessFrom

Per the brief: **GO delivers `SameHyp`**, one of `CompletenessFrom`'s two
inputs. The paired statement lives at `agents/tasks/LJ-1-709/Probe709.agda`,
tracked address `LJ-1-709.Probe709.same-as-graph-both`. Supply of
`SameAsGraph` at the union telescope went 0 to 1 in the mainline tree, and
`HierInStage` stays the only other input `CompletenessFrom` still lacks.

## Corrected target (D-10)

The target proved true at the intended generality on the first shot: no
weakening was needed and none was made. For the consumer's brief: take
`SameHyp` as "for generic arity n, slots w b, environment gamma, the union
telescope implies `P520.SameAsGraph w b gamma`", price its invocation at this
frame (row 6 numbers, plus the imported chains), and do not re-derive either
direction.

## Ratio bar

Nothing lands in `src/`. The probe is a raw `.agda` file with no fence, so it
counts 0 in-fence lines and the ratio bar cannot fire. This report names that
fact rather than discovering it late.

## Return

`same-as-graph-both` is built, typed, and green in
`agents/tasks/LJ-1-709/Probe709.agda` at `EXIT=0`, 2.85 s, 554 MB, from three
committed supplies and nine lines of my own. The union is real: one telescope,
both conjuncts, no third structure. Verdict GO on the obligation, which is
also the W3 answer the brief asked me to measure. The working tree carries
only this task home as changed output; nothing is staged, nothing is pushed.

## ARCHIVE USED

The search surfaced five candidates under `archive/dev/`. I name each and
decide each. This task is an assembly at named addresses; its needs are live
paths, recorded measurements, and predecessor probes, all outside the archive.

- `archive/dev/PLAN-archived.md` (score 197.864): **declined, not read.**
  Superseded plan text; the live planning surfaces are `dev/pod/screen.toml`
  and `dev/pod/queue.toml`.
- `archive/dev/ORCHESTRATION.md` (score 191.740): **declined, not read.**
  Archived dispatch policy; the include-path fact I needed is recorded in the
  live `bedrock.agda-lib:2` and in `[LJ-1.699]`'s report, which I cite.
- `archive/dev/DD-archived.md` (score 177.754): **declined, not read.** The
  live design is `dev/memos/LJ-4-pod-program-design.md`; the brief cites its
  own premises directly and none resolves to this archive.
- `archive/dev/STATUS-archived.md` (score 136.238): **declined, not read.**
  The standing status is `dev/pod/screen.toml` alone.
- `archive/dev/TASKS-archived.md` (score 130.974): **declined, not read.**
  The task ledger of record for this campaign is `dev/pod/table.toml`; the
  predecessors' homes I used are live directories, not archive rows.

## LITERATURE USED

The search surfaced five candidates under `dev/literature/`. This task
rebuilds no mathematics: both directions arrived proved, and the assembly
introduced no new definition. I name each and decline each.

- `dev/literature/primary-sources.md` (score 36.586): **declined, not read.**
  Source manuscripts for the rud route; no source question arose in an
  assembly of existing proofs.
- `dev/literature/devlin-errata.md` (score 34.180): **declined, not read.**
  Errata on Devlin; nothing cited here depends on the Devlin text.
- `dev/literature/glossary-review-2026-08.md` (score 29.645): **declined,
  not read.** A glossary review; I add no term and chose no term.
- `dev/literature/BIBLIOGRAPHY.md` (score 26.276): **declined, not read.**
  An index; no citation needed.
- `dev/literature/fine-structure.md` (score 26.195): **declined, not read.**
  Fine-structure notes; the lemma level of this task touched none of it.
