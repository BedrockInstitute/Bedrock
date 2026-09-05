# [LJ-1.702] report: free LJ-1.643's delivered work from its park

## HEAD

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only under `agents/tasks/LJ-1-702/`
and the two [LJ-1.643] repair paths the brief named. Agda ran under the
caliber the program set on this pane, `GHCRTS="-A64m -I0 -M2g"`, the
wide caliber, ONE Agda process at a time. I did not set `GHCRTS`. No
heap event: the largest peak of any run is 751,321,088 bytes against
the 2,147,483,648-byte cap (`runs/floor-1.out`).

TARGET: build ONE term in `agents/tasks/LJ-1-702/Probe702.agda`:

    truncated-producer : NoInjOrd
      → (a : S) → IsOrd a
      → ∥ Σ[ θ ∈ S ] (IsOrd θ × IsCardinal θ × ⟨ a ∈ˢ θ ⟩) ∥₁

That type is [LJ-1.643]'s `Row3`
(`agents/tasks/LJ-1-643/Probe643.agda:118-122`, read from the parked
copy at `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-643/Probe643.agda`;
this worktree does not hold that file). Then rename every `.agda` under
`agents/tasks/LJ-1-643/runs/` to `.agda.txt`, and name the seven survey
paths [LJ-1.643]'s return left unanswered.

Nothing lands in `src/`. I did not write
`agents/tasks/LJ-1-643/Probe643.agda`. I did not change any `.out` file.
I did not write any `review-of-LJ-1-643-*.md`. I did not write
`agents/tasks/LJ-1-702/review-of-truncated-producer.md`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work.
It does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**GO.** `truncated-producer` is inhabited. The two [LJ-1.643] repairs
are on disk.

- **GO on the obligation.** `truncated-producer`
  (`Probe702.agda:43-46`) has type [LJ-1.643]'s `Row3`. The body is
  `ambientCardAbove` (`src/L/CardinalAbove.lagda.md:219-221`). The
  final run is `runs/final-1.out`, `EXIT=0`, 3.37 s, 749,305,856 bytes
  peak, under the 300 s cap. That `.out` postdates the last edit of
  `Probe702.agda` (source mtime 1787799859, `.out` mtime 1787799893).
- **GO on W3.** The term re-derives with no module-parameter
  projection. The import is
  `open import L.CardinalAbove {ℓ} lem using ( NoInjOrd; ambientCardAbove )`
  (`Probe702.agda:32`). There is no `module Sep` and no
  `module T = Sep`.
- **GO on the rename.** Thirteen files under
  `agents/tasks/LJ-1-643/runs/` now end in `.agda.txt`. Content is
  unchanged: `Floor.agda.txt` has MD5 `d5636f6118dca3f93b63fbe52b871a7c`,
  equal to the parked `Floor.agda`. `ls agents/tasks/LJ-1-643/runs/*.agda`
  finds nothing. The pasted output is in FILE REPAIR below.
- **GO on the survey duty.** The seven unnamed paths are now named
  under headings that name [LJ-1.702] as author and the date
  (`agents/tasks/LJ-1-643/lj-1.643-report.md:238-260`).
  `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-643`
  prints `check-survey-quotes: LJ-1-643 clean (0 note(s), 0 defect(s))`.
  The pasted output is in FILE REPAIR below.

The predecessor report is GO, not NO-GO
(`agents/tasks/LJ-1-643/lj-1.643-report.md:5`). The parked probe
typechecked. I took the type from that probe and inhabited it. I did
not write a `review-of-*.md`.

## THE TERM

`truncated-producer` (`Probe702.agda:43-46`) is `ambientCardAbove`.
The type is the type `Row3` already had. The body is the producer the
tree already has. No new construction.

The predecessor needed a projection only for Row1. `θ-card` is a field
of `module Sep` (`src/L/CardinalAbove.lagda.md:160`, and
`Probe643.agda:134-137`). `ambientCardAbove` is a top-level function of
`L.CardinalAbove` (`src/L/CardinalAbove.lagda.md:219-221`). The import
`open import L.CardinalAbove {ℓ} lem` already applies the module
parameters. Nothing remains to project.

I trimmed the imports to the facts the type uses: `NoInjOrd`,
`IsOrd`, `IsCardinal`, `S`, `_∈ˢ_`, `_×_`, `∥_∥₁`, and
`ambientCardAbove`. I did not import `module Sep`, `cardAboveAt`,
`noInjOrd`, `_↪_`, `𝒮ʟ`, or `Empty`.

**What I did not close.** This dispatch does not land
`Probe643.agda` and does not inhabit `amb-card-supply`. Row1 and Row2
stay in that untracked probe. The next brief that wants the whole
census in git still needs that file. After the rename, a retry of
[LJ-1.643] would see only `Probe643.agda` as `.agda` under that home,
so conjunct 1 would no longer typecheck the floor.

**What I did not weaken.** The type is `Row3` as the predecessor
delivered it. No extra hypothesis. No truncated-away conjunct.

## W2

W2: write the mathematics once at a generic carrier and instantiate
it. `ambientCardAbove` is already that generic term
(`src/L/CardinalAbove.lagda.md:219-221`). This probe instantiates it
by import. I did not rewrite `cardAboveAt`, `Sep`, or `noInjOrd`.
There is no deadline that would force a fixed-form copy. No conflict.

## W3

The widest unmeasured term: whether `Row3` re-derives without the
module-parameter projection [LJ-1.643] needed. Estimate 20 to 60
lines, basis `Probe643.agda:126`.

**Measured: GO, 46 lines, no projection.**
`Probe702.agda` is 46 lines (`wc -l`). The obligation is four of them
(`Probe702.agda:43-46`). The file does not import `module Sep`. The
body is a name, not a `where` module.

## FILE REPAIR

**Rename.** I copied the parked `agents/tasks/LJ-1-643/runs/` into
this worktree from the parked tree, then renamed these thirteen files
to the same name with `.agda.txt`: `Floor`, `T1` to `T12`. I did not
change the bytes. I did not change any `.out` file. MD5 of
`accept-1.out` is `72f8555409ac9d4e8b1e43ba7884ea05`, equal to the
parked copy. MD5 of `final-3.out` is
`0db9bea5b8489b197305f5fe4a5fab38`, equal to the parked copy.

I also copied `LJ-1.643.md` into this worktree so the named checker
command could run. I did not edit that brief. I did not copy
`Probe643.agda`. I did not copy any `review-of-LJ-1-643-*.md`.

**Survey.** I appended two headings to
`agents/tasks/LJ-1-643/lj-1.643-report.md`. I changed no other
sentence of that report. The headings name [LJ-1.702] as author and
the date 2026-08-27. [LJ-1.643]'s own agent did not write those
lines. The seven paths are declined, not read. No finding is added.

Output of `.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-643`:

```
check-survey-quotes: LJ-1-643 clean (0 note(s), 0 defect(s))
```

Output of `ls agents/tasks/LJ-1-643/runs/*.agda`:

```
ls: agents/tasks/LJ-1-643/runs/*.agda: No such file or directory
```

## MEASURED GROUND

- caliber on every run: `GHCRTS=[-A64m -I0 -M2g]`, which the program
  set on this pane and every `.out` records. I did not set it and never
  raised it.
- one Agda process at a time. Floor first, then the inhabitant. No
  parallelism.
- floor with a hole, same type, `module Sep` not imported:
  `runs/floor-1.out`, EXIT=42, 5.32 s, 751,321,088 bytes. The only
  failure is the standing interaction hole at `Floor.agda:36.22-26`.
  After that run I renamed `runs/Floor.agda` to `runs/Floor.agda.txt`,
  so conjunct 1 does not typecheck it.
- final: `runs/final-1.out`, EXIT=0, 3.37 s, 749,305,856 bytes. The
  floor paid the cold elaboration of `L.CardinalAbove`
  (`runs/floor-1.out:5-6`). The final reused that interface
  (`runs/final-1.out:4`).
- final 3.37 s is at or below 2 times the floor 5.32 s.
- no postulate, no hole, no `TERMINATING`, no hole-escape in
  `Probe702.agda`. Nothing lands in `src/`. `git status` shows
  `agents/tasks/LJ-1-643/` and `agents/tasks/LJ-1-702/` as new.
- gates run from the tree root while working: `check-probes` clean
  (10728 tracked files, no probe outside `agents/tasks/`, no generated
  file), `check-fences` clean (103 masters), `lint-agda` on
  `Probe702.agda` exit 0.
- ledger ratio bar: the probe is a `.agda` file, not a `.lagda.md`
  master, so the in-fence divisor is 0 and the bar cannot fire on it.

## LAWS

- **C-22.** This report was a skeleton on disk before any Agda ran.
  I filled it as each answer landed.
- **D-10.** The target is the type the predecessor already inhabited.
  The predecessor report is GO (`lj-1.643-report.md:5`). I did not
  price a residue of a wall.
- **P-l.** The type names `S` and `IsOrd`, not a transparent stage
  presentation. Nothing unfolds a `sucV` construction in the
  statement.
- **D-26.** No well-founded key. Not used.
- **C-42.** This dispatch is not a refutation. It re-derives one green
  row and repairs two red conjuncts of a park.

## W4

No module left `src/`. Nothing to archive.

## WHAT THE NEXT BRIEF NEEDS

1. `Row3` re-derives outside its own probe, as a top-level import of
   `ambientCardAbove`, with no `Sep` projection, at 3.37 s and
   749,305,856 bytes under wide caliber.
2. [LJ-1.643]'s two park causes are repaired in this worktree: the
   floor files are `.agda.txt`, and the seven unnamed survey paths are
   named under headings dated 2026-08-27 that say [LJ-1.702] wrote
   them.
3. `Probe643.agda` is still untracked and is still the census
   obligation. This close does not land it. A retry of [LJ-1.643]
   after this salvage would typecheck that probe alone under conjunct
   1, and would pass conjunct 6 on the repaired report.
4. Row1 still needs the `module T = Sep` projection. That fact is
   local to `θ-card`. It does not infect Row3.

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md`: declined, not read. The operating
  rules that bind this slot are `AGENTS.md` and
  `dev/pod/instructions/coder.md`.
- `archive/dev/PLAN-archived.md`: declined, not read. The live status
  is `dev/pod/screen.toml`. This obligation is a re-derive of one
  green row, not a plan item of the archived route.
- `archive/dev/DD-archived.md`: declined, not read. W2 and W4 are live
  clauses of the slot file. The archived DD series is not the source
  for `truncated-producer`.
- `archive/dev/TASKS-archived.md`: declined, not read. The predecessor
  this task reads is the parked live home `agents/tasks/LJ-1-643/`.
- `archive/dev/STATUS-archived.md`: declined, not read. The
  internalization-route goal table is not the source for
  `truncated-producer`.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md`: declined, not read. No
  glossary term is at issue and I added no `dev/glossary.toml` entry.
- `dev/literature/level-formula-slot-roles.md`: declined, not read.
  This obligation does not mention a level formula.
- `dev/literature/primary-sources.md`: declined, not read. The
  inhabitant is an import of a term the tree already has.
- `dev/literature/fine-structure.md`: declined, not read. No
  fine-structure fact is consumed.
- `dev/literature/formalizations-landscape.md`: declined, not read.
  The census of other formalizations is not this re-derive.
