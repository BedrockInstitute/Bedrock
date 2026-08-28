# LJ-1.734 report: `keyS-in-carrier-lim`, the name the meter reads

## HEAD

head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.734
obligation: agents/tasks/LJ-1-734/Probe734.agda::keyS-in-carrier-lim
verdict: **GO.** The 729-inhabited term converts in a fresh file at
its own top-level name. `keyS-in-carrier-lim` is stated and INHABITED
in `Probe734.agda`, exported at the file's top level; the verdict run
p-2 is EXIT=0 on the delivered bytes. No postulate stands anywhere,
the probe carries `--safe`, nothing lands in `src/`, and
`keyS-in-carrier-stage` appears in no code line of the file. The
obligation the live meter reads now has supply.

## 0. THE PREDECESSOR QUESTION

The predecessor is `[LJ-1.729]`. Its report states NO-GO on the
brief's false type and GO on the corrected scope
(agents/tasks/LJ-1-729/lj-1.729-report.md:10), with the corrected
target delivered as the inhabited `keyS-in-carrier-lim`
(agents/tasks/LJ-1-729/lj-1.729-report.md:53). The verdict on the
name this brief buys is GO, so the clause that stops on a NO-GO
predecessor does not fire. The type is taken from the probe bytes
that typechecked, not from the report's prose:
agents/tasks/LJ-1-729/Probe729.agda:202 is the first line of the
inhabited statement, and the signature runs to line 208. The four
brief premises each verified at dispatch:

1. The 729 meter closed on the false name; the brief's type is FALSE
   at `ω ∈ γ` (lj-1.729-report.md:10).
2. The term IS inhabited under `closedω` (lj-1.729-report.md:53).
3. `closedω` is landed (src/L/Ordinal/StageArith.lagda.md:81).
4. The inhabited term stands at the meter-readable name
   (Probe729.agda:202).

## 1. WHAT WAS BUILT

One file, `agents/tasks/LJ-1-734/Probe734.agda`: the full closure of
the 729-inhabited term, transcribed. The diff against the 729 probe
was measured before the first run: every code line is identical, and
the only differences are the header comments, the module line
(`LJ-1-734.Probe734`), and the ABSENT Section 5. Concretely:

- `keyS-in-carrier-lim`, stated and inhabited at the file's top
  level, signature byte-identical to Probe729.agda:202-208.
- Its supports, all real: the finite-iterate shift
  (`sucIter-sucV`, `sucIter-shift`, `iter-up`), the Kuratowski step
  `pr∈iter`, the generic `Climb` module (`pairStep`, `tagStep`,
  `codeTm∈iter`, `code∈iter`), and the absorption body (`close`,
  `step`, `helper`).
- `keyS-in-carrier-stage`, STATED NOWHERE: the false neighbour type
  (counterexample at `γ := sucV (sucV ω)`, recorded in
  agents/tasks/LJ-1-729/review-of-keyS-in-carrier-stage.md) appears
  in this file in comments only. No postulate stands in for it and no
  weaker form is inhabited under its name.

## 2. THE FLOOR AND THE RUNS

No floor run was priced separately, and here is why: the heavy-object
rule prices the frame before a PROOF is attempted, and this task
writes no proof. The term is a verbatim transcription of bytes that
went green at the predecessor's site (729's p-20: 2.14 s, 387 MB,
with the import frame about 1.4 s and 350 MB of it), so the first
real run of this file was already expected to land at the source's
price, and it did. The 1800 s cap was never in play; no heap wall was
met at any point.

| run | wall | peak | note |
|---|---|---|---|
| p-1 | 0.69 s | 245 MB | EXIT=1 with NO Agda message: the runner artifact 729 measured (`time: signal: Invalid argument`, lj-1.729-report.md section 2). No verdict was delivered, so no Agda result was rerun. |
| x-ref-729 | 1.89 s | 387 MB | the runner mechanism re-validated on the known-green 729 probe, EXIT=0, matching its recorded verdict numbers |
| p-2 (verdict) | **1.89 s** | **366,018,560 B** | **EXIT=0, green, delivered bytes** |

## 3. W3 ANSWER

The brief's W3: whether the transcribed alias still converts in a
fresh file, estimated 200 to 280 lines. Answer: **YES, and the
estimate was right.** The file is 248 total lines, 221 non-blank,
raw `.agda` (in-fence count 0, the ratio bar cannot fire). The 729
nesting carried nothing that the fresh file lacks: every name
resolves at the file's own top level, and the only edit the fresh
file demanded was the module line. The false neighbour type needed no
guard here, because the brief forbids inhabiting it and the file
neither states nor inhabits it.

## 4. W2 ANSWER

The climb remains generic: `Climb` quantifies over an arbitrary small
alphabet `K`, an arbitrary value map `f`, and stage facts `hf` and
`hnum`; `keyS-in-carrier-lim` instantiates it at the alphabet
`⟪ fst A ⟫`. The transcription relocated one proof and duplicated
none of its content: there is one statement of the shift lemmas, one
`pr∈iter`, one `Climb`, one obligation body in this file, and the
bound is still proved once at a generic carrier. Nothing landed in
`src/`, so no shared-master question arises. No deadline forced a
fixed form.

## 5. WHAT THE NEXT BRIEF NEEDS

1. The meter's name has supply. Later briefs may cite
   `agents/tasks/LJ-1-734/Probe734.agda::keyS-in-carrier-lim`
   (verdict run p-2, EXIT=0) the way they cite a landed `src/` name,
   with the caveat that it is a task artifact and not a `src/`
   master.
2. The `stage-read` spine re-brief (729 report, section 5 item 2) can
   now name THIS file for its membrane bound. Price the spine after
   the move into `src/`, which stays unfunded; the natural home is
   still `L.Coding.CodeSet`.
3. The move into `src/` retires a real duplication risk: two task
   probes now carry the same roughly 90-line climb. Fund it from the
   p-2/x-ref numbers, not from prose.
4. Fund no new proof. This task discharged a naming obligation, not a
   mathematical one; the only measured content is the conversion,
   already reported in section 3.
5. The runner artifact of p-1 is the same harness glitch the 729
   report measured, and the x-ref validation protocol handles it for
   one 1.9 s run. Expected noise, not a finding.
6. Operational, measured here: `AGENTS.md` names `.venv/bin/python`,
   but in this worktree that relative path does not resolve; the venv
   sits at the main checkout, so the survey check runs as
   `/Users/alsg/Agentic/Bedrock/.venv/bin/python
   scripts/pod/check-survey-quotes.py`. It returned clean, 0 notes,
   0 defects.

## 6. PRICE

| item | value |
|---|---|
| Agda wall, verdict run | 1.89 s (`runs/p-2.out`) |
| peak, verdict run | 366,018,560 B, 17 percent of the 2,147,483,648-byte wide cap |
| runs this dispatch | p-1 (artifact), x-ref-729 (validation), p-2 (verdict) |
| heap wall | none met |
| probe lines | 248 total, 221 non-blank, raw `.agda` (in-fence count 0, the ratio bar cannot fire) |
| brief estimate | 200 to 280 lines (W3); actual 248, inside it |
| caliber | `-A64m -I0 -M2g`, never set here |
| `src/` edits | none |

## ARCHIVE USED

- `archive/dev/ORCHESTRATION.md:1` `# ORCHESTRATION: the orchestrator's operating rules`. Declined: not used. This dispatch transcribes a predecessor's green bytes and runs them; no archived dispatching rule bears on that.
- `archive/dev/DD-archived.md:1` `# THE \`DD\` RULING SERIES, archived in full 2026-08-18`. Declined: not read. The clauses this dispatch answers to live in the slot file and the brief; the closed DD series is history.
- `archive/dev/PLAN-archived.md:1` `# ARCHIVED 2026-08-20`. Declined: not read. The live screen is `dev/pod/screen.toml` and the live direction is `dev/pod/direction.md`; this task follows those.
- `archive/dev/STATUS-archived.md:1` `# STATUS-archived: the goal table of the internalization route`. Declined: not read. The route this task sits on is the live queue's, not the archived table's.
- `archive/dev/TASKS-archived.md:1` `# Archived task index: the \`L3.32-T\` series`. Declined: not read. The `L3.32-T` series predates the POD and shares no obligation with LJ-1.734.

## LITERATURE USED

- `dev/literature/glossary-review-2026-08.md:1` `# Glossary review: the 119 pre-protocol entries`. Declined: not used. A raw `.agda` probe and its records carry no translation surface.
- `dev/literature/devlin-errata.md:1` `# Devlin errata: documented error classes (do-not-repeat checklist)`. Declined: not read. This dispatch cites no Devlin page and transcribes no classical construction.
- `dev/literature/primary-sources.md:1` `# Primary sources, second round: Jensen manuscript, Devlin, Jech`. Declined: not read. The fetch map is the literature team's record; this dispatch fetches nothing.
- `dev/literature/BIBLIOGRAPHY.md:1` `# Bibliography for the rud route`. Declined: not read. No source is cited beyond the predecessor probe and its report.
- `dev/literature/level-formula-slot-roles.md:1` `# The level-hood formula: arity, what it binds, what stays free`. Declined: not read. The slot census belongs to the graph tasks; the climb here counts constructor nodes only.
