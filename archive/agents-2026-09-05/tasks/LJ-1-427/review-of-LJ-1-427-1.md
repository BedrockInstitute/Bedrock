# LJ-1.427: adversarial review of LJ-1.427#1

## HEAD
head_slot: `mathematician_adversarial`
machine: shared
attacked: `agents/tasks/LJ-1-427/lj-1.427-report.md` and
`agents/tasks/LJ-1-427/review-of-descent-from-internal.md`, the return of
instance LJ-1.427#1
written: one file, this one. No commit, no push, nothing under `src/`.

## THE INSTANCE RECORD, AND ONE GAP IN IT

The brief told me to read the six facts, `model`, `effort` and `heads_sha256`
of instance LJ-1.427#1 in `dev/pod/transitions/`. That source does not hold
this instance. The last row of `dev/pod/transitions/2026-08.jsonl` is task
LJ-1-399 at `2026-08-19T13:31:57Z`. I recovered the record from two other
tracked places, and I name them:

- Six facts: `agents/tasks/LJ-1-427/runs/accept-1.out:24`. Keys read:
  `changed_files` 11 files, `error_class` `unsolved_meta`, `exit_code` 42,
  `heap_wall` false, `lines` 0, `obligations_delta` 0. The same line records
  `obligations_open` 1 and `seconds` 1.84.
- Model and effort: `.pod-state/logs/LJ-1.427-20260820-194713.log:4`, the
  `agent_started` record, `argv` `["grok","--model","grok-4.6","--effort",
  "high","--always-approve"]`. Model `grok-4.6`, effort `high`. The instance
  started `2026-08-20 19:47:13`.
- Heads: `agents/tasks/LJ-1-427/.pod:1`,
  `heads=e70397bea6e45c8fc1ee76cdf86d466c47420028d7549db39333aee0b0831669`
  at `2026-08-20T11:45:33Z`.

The registry row for key `LJ-1.427` (`.pod-state/registry.json`) now names
instance #2, this review, started `20:07:09`. So the registry no longer holds
instance #1. The gap in `dev/pod/transitions/` is a fact for the maintainer,
not a defect in the attacked return.

## QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY?

**The verdict NO-GO is correct on its own numbers. I recomputed them.**

- The W3 hole is real. `agents/tasks/LJ-1-427/Probe427.agda:74-76` states
  `delta-is-ordinal : IsOrd (fst (InternalLeastCard.Selected.δᴸ κ oκ nonempty))`
  with body `{!!}` at `:76`.
- The error class is one class only. `runs/w3-recheck-2.out:2-6` reports
  `UnsolvedInteractionMetas` at `Probe427.agda:76` and `:103` and nothing
  else. The same holds in `runs/w3-1.out`, `runs/w3-recheck-1.out` and
  `runs/w3-recheck-3.out`.
- The medians recompute from the kept `.time` files. Wall seconds
  {2.03, 1.66, 1.67}, median **1.67 s**. Peak RSS {395788288, 395804672,
  395788288} bytes, median **395788288** bytes. Both match the report table.
  First check 1.60 s at `runs/w3-1.time`. No run approached the 8 g cap. No
  heap event.
- The two ordinal uses are correctly named. `ord-tri` takes `IsOrd` on both
  arguments at `src/L/Ordinal/Linear.lagda.md:136`, and `[LJ-1.421]` splits
  with it at `agents/tasks/LJ-1-421/Probe421.agda:185`. `Init` has `IsOrd α`
  as its first conjunct at `src/L/Ordinal/SquareLaw.lagda.md:693`, and
  `[LJ-1-406]` fills it with `κoL a oa` at
  `agents/tasks/LJ-1-406/Probe406.agda:187`.
- The second obstruction is correctly separated. `κ-min-at` at
  `src/L/Cardinal.lagda.md:140-141` forbids an ambient truncated injection
  into a member of `κ` by `∈`. `δ-min` at `src/L/Cardinal.lagda.md:261-263`
  forbids a code into a member of `Lset β` below `δ-card` in `orderAt`. The
  three losses the report names are exactly the three differences between
  those two types. `clause4-at-kappa` spends the first at
  `agents/tasks/LJ-1-406/Probe406.agda:116`.

**One line of the verdict outruns the body. It is the F5 defect class.**

`lj-1.427-report.md:59` reads "**NO-GO.** `descent-from-internal` is not
inhabited". `review-of-descent-from-internal.md:3` and `:126` repeat the same
words. A hole with unsolved metas measures that the tree does NOT DELIVER an
inhabitant. It does not measure that no inhabitant EXISTS. The body states the
correct form at `lj-1.427-report.md:77-79`: "This is not a universal
negative... I measured that this tree does not deliver `IsOrd (fst δᴸ)` from
`internal-nonempty`." So the line and the body disagree in exactly the way the
audit measured twice: `dev/pod/audit-2026-08-20.md:76` (F5, verdict outruns
evidence) and `:83` (F6, words of grade "cannot" outrun the evidence).

Correction for any reuse: write "not delivered from this telescope by this
tree", or keep the D-10 form the report already uses, "the swap as specified
does not go through". The verdict itself does not change.

## QUESTION 2: DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY?

**Resolving and accurate. I opened each of these.**

- `src/L/Cardinal.lagda.md:125-127` (`oκ` by `mem-ord` in `sucV (fst α)`),
  `:133` (truncated `κ-inj`), `:140-141` (`κ-min-at`), `:235` (the
  `InternalLeastCard` module, and my `grep` over `src/` returns exactly this
  one line, so the C-42 count of zero consumers holds), `:239-240` (`Good`
  with no ordinality conjunct), `:243` (`Selected` takes `nonempty` as a
  hypothesis), `:249-254` (`δ-card`, `δᴸ`), `:257` (coded witness `δ-inj`),
  `:261-263` (`δ-min`).
- `src/L/Ordinal/Linear.lagda.md:136`, `src/L/Ordinal/SquareLaw.lagda.md:692-698`,
  `src/L/Constructible.lagda.md:336-337` (`Lset-out`), `src/L/StageCardinal.lagda.md:283`
  (`sq` spent once, in the limit step), `:564` (`stage-card-upper`).
- `agents/tasks/LJ-1-421/Probe421.agda:164-183`, `:182-204`, `:185`, `:189`,
  `:214`, `:225-263` (39 lines, as the report says).
- `agents/tasks/LJ-1-406/Probe406.agda:116`, `:180-190`, `:187`.
- `agents/tasks/LJ-1-403/Probe403.agda:46-52` (`Good⁺`: membership in `κ`,
  infiniteness, the code).
- `agents/tasks/LJ-1-402/Probe402.agda:80` (`δᴸ` as an injection target, not
  as an ordinal).
- All `Probe427.agda` line references: `:22-23`, `:62-76`, `:64-67`, `:70-72`,
  `:74-76`, `:82-83`, `:87-91`, `:92-96`, `:99-103`. All exact. The four
  forbidden strings occur only in comments at `:22-23` and `:82-83`. My `grep`
  confirms this.
- The C-42 probe count holds. Before this task, `δᴸ` occurs in
  `agents/tasks/LJ-1-401/Probe401.agda:63` and `:70` (as an `InjCode` target),
  `agents/tasks/LJ-1-402/Probe402.agda:80`, `agents/tasks/LJ-1-403/Probe403.agda`
  (inside `Good⁺`), and probe-local copies of the module in `LJ-1-236` and
  `LJ-1-278`. None applies `IsOrd`, `ord-tri` or `Init` at `δᴸ`. Count 0, as
  the report says.

**Not resolving, or no longer true. Three findings.**

**Finding A, material: the provisional basis was stale when the return
landed.**

`lj-1.427-report.md:49-53` says "`[LJ-1.424]` and `[LJ-1.425]` have not run",
"The sibling worktrees hold only briefs" and "Neither report is NO-GO". All
three sentences were false before the return was finalized:

- The LJ-1.425 report landed at `19:59:26` (file mtime), verdict
  "**NO-GO on `internal-nonempty`. GO on `κ-in-site-bound`. GO on W3's" at
  `.pod-state/worktrees/LJ-1-425/agents/tasks/LJ-1-425/lj-1.425-report.md:57`.
- The LJ-1.424 report landed in the main tree at `20:00:19` (file mtime),
  verdict "**GO.** The obligation typechecks" at
  `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-424/lj-1.424-report.md:23`,
  committed as `ad62a9c` ("pod: LJ-1.424 done, row task-lj-1-424-go").
- The attacked return was finalized after both: `Probe427.agda` at
  `20:01:40`, `review-of-descent-from-internal.md` at `20:05:22`,
  `lj-1.427-report.md` at `20:06:01` (file mtimes).

The brief's stop-clause was therefore live at finalization time:
"IF EITHER REPORT IS NO-GO, OR NAMES ITS STATEMENT FALSE, DO NOT WRITE THAT
TYPE INTO THIS TELESCOPE. Stop, say which report refused it, and return"
(`agents/tasks/LJ-1-427/LJ-1.427.md:32-33`). The telescope
holds `internal-nonempty` at `Probe427.agda:64-67` and `:92-96`. The return
did not stop, and the OWES rows at `lj-1.427-report.md:258-259` still say
"not run" for both tasks.

Mitigation, and it matters: the breach did not contaminate the measurement.
The type at `Probe427.agda:64-67` is the type the LJ-1.425 brief names, and
the LJ-1.425 report's own TARGET section restates that same type. No refuted
type entered the telescope. The W3 kill does not depend on `coded-to-arrow`,
as the report says. So the verdict stands.

Cause is shared, and this answers my slot's standing question 3. The program
dispatched LJ-1.424, LJ-1.425, LJ-1.426 and LJ-1.427 in one wave: all four
`.pod` stamps read `2026-08-20T11:45:33Z`. The brief assumed two states, report
exists or task not run. The real state was a third: the report landed mid-run.
No clause told the coder to re-poll the named reports before finalizing. This
is a program-level scheduling defect, and the maintainer should see it: either
dispatch a dependency before its consumer, or make the stop-clause a
finalization check.

**Finding B, minor, checkability: one citation has no path in this tree.**

`lj-1.427-report.md:253` cites "sibling `LJ-1-422` report, verdict **NO-GO**
at `lj-1.422-report.md:15`". This worktree has no `agents/tasks/LJ-1-422/`.
The fact is true in the sibling:
`.pod-state/worktrees/LJ-1-422/agents/tasks/LJ-1-422/lj-1.422-report.md:15`
reads "**NO-GO.** The truncated arrow is delivered". A checker inside this
tree cannot open the short path as written. Re-cite with the sibling path, or
land the file.

**Finding C, minor, protocol: the W3 "alone" run has no kept artifact.**

The brief said "Typecheck `IsOrd (fst δᴸ)` ALONE" with "nothing else built"
(`agents/tasks/LJ-1-427/LJ-1.427.md:109`).
Every kept run, including `runs/w3-1.out`, reports metas at `:76` AND `:103`.
So the obligation module was already in the file when every kept run ran. The
reported numbers measure the whole probe, not W3 alone. The kill evidence is
not affected, because the meta at `:76` is reported on its own. But the probe
comment at `Probe427.agda:57-58`, "Nothing / else is built", disagrees with
the artifact the kept runs measured. A successor brief should know this.

## QUESTION 3: IS THE ENUMERATION COMPLETE?

**Within its own frame, yes. Against the tree today, no. Three gaps.**

Gap 1, small: the OWES table omits `lem : LEM (ℓ-suc ℓ)`, a module parameter
at `Probe427.agda:43`. The obligation carries it. The chain's convention
carries it too (`agents/tasks/LJ-1-421/Probe421.agda:34`), and LEM is the
standing classical base, not a debt of this swap. Low materiality. Named here
for completeness.

Gap 2, material: two OWES rows are wrong today, and the campaign bill
understates the debt. Restated:

| hypothesis | the return says | the tree says today |
|---|---|---|
| `coded-to-arrow` | "not run; not in `src/`" (`lj-1.427-report.md:258`) | **delivered green**. LJ-1.424 GO at `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-424/lj-1.424-report.md:23`, commit `ad62a9c` |
| `internal-nonempty` | "not run" (`lj-1.427-report.md:259`) | **refused**. LJ-1.425 NO-GO at the sibling report `:57`. Its own caveat: the natural witness is false and the delivery failed. It is not a refutation at every stage. Its section 5 proposes a corrected statement at a bigger stage |

So the internal face is obstructed at TWO independent sites now:
nonemptiness (LJ-1.425) and ordinality (this task, W3). The ambient face is
obstructed too: `kappa-arrow-data` refused (LJ-1.422, sibling report `:15`)
and `kappa-coded` refused (LJ-1.426,
`.pod-state/worktrees/LJ-1-426/agents/tasks/LJ-1-426/lj-1.426-report.md:51`,
"**NO-GO on `kappa-coded`. GO on HALF B at this pair, with the four"). That
is a stronger input to `[LJ-2.5]` than the attacked return states. The return
could not have known the sibling verdicts: they landed at `19:59:26`,
`20:00:19` and `20:01:41`, mid-run. The bill must still be restated before
anyone queues on it.

Gap 3, the cure landscape: the return names two corrections, `Good` plus an
ordinality conjunct (its section 4) and `Good⁺` from LJ-1.403. It misses the
third, which landed mid-run: LJ-1.425 section 5's bigger-stage correction.
That correction repairs nonemptiness only. It adds no ordinality conjunct, so
the W3 gap stays open at the bigger stage. `Good⁺` would deliver `IsOrd`
through membership in `κ` by `mem-ord` (`src/L/Cardinal.lagda.md:125-127`),
but LJ-1.403's verdict is "GO on the assembly. `ne⁺` is not discharged." at
`agents/tasks/LJ-1-403/lj-1.403-report.md:18`. No correction on the table
delivers BOTH nonemptiness and ordinality. The composite, `Good⁺` at a bigger
stage, is unmeasured. That is the widest unmeasured term for the next
dispatch, and the attacked return does not name it.

## THE VERDICT OF THIS REVIEW

**AGREE, WITH CORRECTIONS. The NO-GO stands.**

A review that agrees is a real result. I attacked the measurement and it held:
the type elaborates, the hole is real, the error class is one class, the
medians recompute from the kept runs, no heap event, and the two obstructions
are correctly separated at `file:line`. The property the ambient face carries
and the internal face lacks is real: `IsOrd` by `mem-ord` at
`src/L/Cardinal.lagda.md:125-127`, against a `Good` that does not ask for it
at `:239-240`.

Corrections required before this return is reused:

1. Replace "is not inhabited" at `lj-1.427-report.md:59` and
   `review-of-descent-from-internal.md:3`, `:126` with the not-delivered form.
   F5 class, one line each.
2. Restate the OWES rows at `lj-1.427-report.md:258-259` against LJ-1.424 GO
   and LJ-1.425 NO-GO, and restate the campaign bill to name both internal
   obstructions and both ambient refusals.
3. Re-cite the LJ-1.422 report at a path that resolves, or land it.
4. Record in any successor brief that the W3 "alone" protocol has no kept
   artifact (Finding C above).

For the maintainer, outside the return: the wave that dispatched LJ-1.424
through LJ-1.427 at one stamp made a stop-clause conditioned on a sibling
report fire mid-run and be missed, and it left `dev/pod/transitions/` without
the instance row this review was told to read. Both are program defects with
evidence above, and neither is the coder's fault.

## WHAT THE NEXT DISPATCH NEEDS

The next mathematical task on this face should measure the composite
correction, `Good⁺` at a stage that also contains the code graph, against
BOTH conjuncts: nonemptiness (LJ-1.425 section 5) and ordinality (this task,
W3). Its D-10 must state that the composite changes which `δ` is least, as
this return correctly said of every correction. The ambient face has no live
rescue on the table: LJ-1.422 and LJ-1.426 both refused. That is the state of
the two-tower candidate as of this review, and it belongs in front of
`[LJ-2.5]`.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: not read, declined. The per-episode journal is
  retired, and this review measures a live return. A live document carries no
  history.
- `archive/dev/ORCHESTRATION.md`: not read, declined. Loop operation is not
  this review's question. The one program-level observation I make
  (Finding A) rests on `.pod` stamps, git log and file mtimes, not on the
  archived operating rules.
- `archive/dev/DD-archived.md`: not read, declined. This review changes no
  DD row. The clauses it applies (W1 through W8) were injected live.
- `archive/dev/PLAN-archived.md`: not read, declined. The live plan is
  `dev/pod/queue.toml` and `dev/pod/screen.toml`, both already in front of
  me. The retired plan is not this measurement.
- `dev/ARCHIVE.md`: not used. No module is retired by this review, W4 does
  not fire, and the attacked return retired nothing.

## LITERATURE USED

- `dev/literature/devlin-II5.md:357`, read: "12. The cardinal arithmetic of
  1.1(vii) and the initial-ordinal facts in". Used for one anchor: in the
  orthodox account the cardinal facts are initial-ORDINAL facts. So the
  internal least cardinal is an ordinal in the mathematics, and the NO-GO of
  this task measures a gap in this tree's `Good`, which asks for no
  ordinality (`src/L/Cardinal.lagda.md:239-240`), not an impossibility. This
  supports the bounded form the return's own body takes at
  `lj-1.427-report.md:77-79` and sharpens Finding 1 under QUESTION 1.
- `dev/literature/BIBLIOGRAPHY.md`: not used, declined. This review adds no
  source.
- `dev/literature/digest.md`: not used, declined. The rud-route digest is not
  this measurement.
- `dev/literature/geology.md`: not used, declined. Geology is not this
  measurement.
- `dev/literature/devlin-errata.md`: not read, declined. This review relies
  on no Devlin proof step, only on the label of the one line quoted above,
  and the errata file holds no entry for it.
