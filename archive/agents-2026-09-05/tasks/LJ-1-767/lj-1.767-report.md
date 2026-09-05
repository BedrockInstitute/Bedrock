# LJ-1.767 report: grounded-from-complete at code coordinates, no mkWit ascription

## THE VERDICT

**NO-GO. THE WALL IS REAL, AND IT IS THE MEMBERSHIP SLOT.**
`grounded-from-complete` does not typecheck at `-M4g` in any shape this
dispatch was permitted to write. The ordered full run walled at the 1800 s
cap with peak RSS 4642603008 B, above the 4 GB cap
(runs/probe767-1.out:4,5,22, `EXIT=124`). The brief orders: a NO-GO that is a
heap wall stops this packing at `-M4g`. So this packing stops here.

This is a RESOURCE WALL, not a stated refutation. Per the brief's own rule
("Do not write a `review-of` for a resource wall") no
`review-of-grounded-from-complete.md` is written. `conv-at-Lδ` stays
uninhabited, `amb` stays untried, `mkWit`'s spelled codomain stays unrestored,
`Completeness` stays a hypothesis, and nothing landed in `src/`
(`git status --short src/` is empty; the only tree change is
`agents/tasks/LJ-1-767/`, untracked before this dispatch).

The clause "a heap wall is a signal to restructure in the same dispatch" was
honored: FOUR restructurings were built, run and measured in this dispatch,
and all four wall (section 3). The restructuring clause is exhausted, and the
report gives the specific reason no permitted shape can carry the term
(section 4).

## THE DELIVERABLE

- `Probe767.agda.txt` -- the W3 term at the brief's shape: the two loaded
  interfaces, the obligation's type spelled once, `conv0` un-ascribed
  (codomain a solved meta), the packing inline in the body, no `mkWit`, the
  top-level export. It does not typecheck (the wall), so it rests at
  `.agda.txt`, never `.agda`.
- `runs/Frame767.agda` -- the vendored frame, transcribed. It typechecks:
  GREEN at this site (runs/frame767.out:14,15,32).
- `runs/HullHalf767.agda` -- the vendored hull half, transcribed, import
  retargeted. It typechecks: GREEN at this site
  (runs/hullhalf767.out:4,5,22).
- `runs/Floor767.agda.txt` -- the floor instrument, the probe with the body
  holed (runs/floor767.out:7,8,25).
- `runs/B1Types767.agda.txt`, `runs/B2Conv767.agda.txt` -- the two re-measure
  instruments the brief ordered.
- `runs/D1ConvHoled767.agda.txt`, `runs/D6TupleHoled767.agda.txt`,
  `runs/D7MemHoled767.agda.txt`, `runs/D11MemRef767.agda.txt`,
  `runs/D12MemDecl767.agda.txt`, `runs/D13MemConvHoled767.agda.txt`,
  `runs/D14Shim767.agda.txt`, `runs/D15ShimDecl767.agda.txt`,
  `runs/D17MemOnly767.agda.txt` -- the nine bisect instruments of the
  in-dispatch restructuring (section 3), each with its `.out` record.
- `runs/run.sh` (protocol runner, 1800 s cap) and `runs/diag.sh` (bisect
  runner, 420 s cap). Diagnostic numbers are NEVER quoted as prices; the one
  price this report states for the probe is the 1800 s protocol run.
- One `.agda` file that could not typecheck rested at `.agda` only between
  its run and its deletion (the protocol run's temp copy, deleted at once);
  the tree now carries exactly two `.agda` files, the two GREEN interfaces.

`obligations` stay at 1: `grounded-from-complete` keeps supply 0. The program
should route this return to `heap-wall-park` (park_and_split).

## 0. THE VENDOR DECISION

The brief's premise bases under `agents/tasks/LJ-1-765*/` and
`agents/tasks/LJ-1-728*/` do not exist in this worktree, the same situation
the LJ-1.764 dispatch recorded (agents/tasks/LJ-1-764/lj-1.764-report.md, THE
VENDOR DECISION). The vendor files delivered in this task directory carry the
measured verdicts in their own headers, and no absent directory is needed.

- `VendorFrame.agda.txt` transcribed to `runs/Frame767.agda`: module renamed
  to `LJ-1-767.runs.Frame767`, header rewritten; every line below the module
  line is byte-identical (measured with `diff`, context from the module line
  down, empty diff).
- `VendorHull.agda.txt` transcribed to `runs/HullHalf767.agda`: module
  renamed, the Frame import retargeted to `LJ-1-767.runs.Frame767`, header
  rewritten; `diff` shows exactly one further differing line (the import) and
  the vendor's own duplicated header comment block, kept byte for byte.
- `VendorB1.agda.txt` / `VendorB2.agda.txt` transcribed to the two `.txt`
  instruments: `diff` shows only the two import retargets and comment lines;
  no code row changed.
- Re-measured here per the Boundary rule that a measured cure is re-measured
  at its own site (section 1, rows frame767 and hullhalf767).

## 1. THE PROTOCOL RUNS

ONE Agda process at a time, sequential, `pgrep -x agda` empty between runs.
`GHCRTS` was read from the pane at every run and never set by this task; each
`.out` line 1 shows `-A64m -I0 -M4g`, the heavy caliber. Cap 1800 s on
protocol runs. This worktree's `_build` held no interfaces for the probe
chain, so the first run paid the one-time cold closure. All times are wall
clock, `/usr/bin/time -l`.

| run | file | rc | wall | peak RSS | evidence |
|---|---|---|---|---|---|
| frame (cold chain paid) | `runs/Frame767.agda` | 0 | 226.33 s | 2005188608 B | runs/frame767.out:14,15,32 |
| hull half | `runs/HullHalf767.agda` | 0 | 205.92 s | 1782349824 B | runs/hullhalf767.out:4,5,22 |
| B1 re-measure | `runs/B1Types767.agda.txt` | 42, designed | 8.71 s | 1027391488 B | runs/b1types767.out:7,8,25 |
| B2 re-measure | `runs/B2Conv767.agda.txt` | 42, designed | 110.89 s | 1872560128 B | runs/b2conv767.out:7,8,25 |
| floor (body holed) | `runs/Floor767.agda.txt` | 42, designed | 109.31 s | 1833828352 B | runs/floor767.out:7,8,25 |
| THE RUN (inline packing) | `Probe767.agda.txt` | 124, CAP | 1800.11 s | 4642603008 B | runs/probe767-1.out:4,5,22 |

B1 and B2 exit 42 only on their by-design holes
(runs/b1types767.out, the single `UnsolvedInteractionMetas` block at
`B1Types767.agda:86`; runs/b2conv767.out at `B2Conv767.agda:91`). B2 costs
110.89 s against B1's 8.71 s: `conv0`'s inferred codomain is the 100 s class
cost here, the same shape SSS measured green at 140.69 s (VendorB2 header).
The floor (109.31 s) equals B2 within noise: the top-level export is free,
as in LJ-1.764.

The floor fits the cap with about 2.2 GB to spare, so the probe run went
ahead. It walled: EXIT=124 at the 1800 s cap, peak RSS 4642603008 B
(runs/probe767-1.out:4,5,22). No watchdog kill is logged in the window
(`_build/tools/agda-watchdog.log`, last line is the 2026-08-31 16:21:43
start line).

## 2. THE ENVIRONMENT AT DISPATCH

- `sysctl vm.swapusage`: total 5120.00M, used 3985.31M, free 1134.69M. The
  watchdog's line is 8192 MB (scripts/ops/agda-watchdog.sh). Pressure level
  1 (normal) at dispatch.
- No Agda process at dispatch (`pgrep -x agda` empty).
- Pane caliber `GHCRTS=[-A64m -I0 -M4g]` (heavy), read at dispatch, never
  set or changed.
- `_build/2.8.0/agda/agents` carried no interfaces for Probe652, Probe667,
  Probe673, Probe692, Probe689, Probe686, Probe680 or Probe520, so the cold
  closure was paid once, inside the frame run's 226.33 s.
- This worktree has no `.venv`; the pinned interpreter of the main checkout
  ran the survey gate (section 5).

## 3. THE IN-DISPATCH RESTRUCTURING, AND THE GRID

The coder clause (owner ruling 2026-08-23) makes the wall a signal to
restructure in the same dispatch. Nine bisect instruments were built and run
at a 420 s diagnostic cap (`runs/diag.sh`; the cap line is printed inside
each `.out`). NOTHING in this section is a price; only section 1 states
prices. The instruments differ from the probe ONLY as described.

| instrument | delta from the probe | rc | peak RSS | evidence |
|---|---|---|---|---|
| D1 | last component (`conv0`) holed | 124 | 3978870784 B | runs/d1convholed767.out:5,6,23 |
| D6 | whole tuple holed | 42, designed | 1871757312 B | runs/d6tupleholed767.out:8,9,26 |
| D7 | slot 4 (`a∈H`) holed | 42, designed | 1896218624 B | runs/d7memholed767.out:8,9,26 |
| D11 | slot 4 = `mem a a∈H` (named reference) | 124 | 3956850688 B | runs/d11memref767.out:5,6,23 |
| D12 | `mem` declared, body holed | 42, designed | 1872576512 B | runs/d12memdecl767.out:38,39,56 |
| D13 | slot 4 = `mem a a∈H`, `conv0` holed | 124 | 3947413504 B | runs/d13memconvholed767.out:5,6,23 |
| D14 | supply shim `hullClosedM`, slot 4 = pattern var at the goal's own spelling | 124 | 3926573056 B | runs/d14shim767.out:5,6,23 |
| D15 | shim declared, body holed | 42, designed | 1868578816 B | runs/d15shimdecl767.out:8,9,26 |
| D17 | slot 4 = `a∈H` direct, `conv0` holed | 124 | 3978903552 B | runs/d17memonly767.out:5,6,23 |

D12's one diagnostic beyond its designed hole is an `UnequalTerms` produced
by the instrument itself (a half-commented body), not by `mem`: the run
completed the whole file's elaboration first, at 111.33 s
(runs/d12memdecl767.out:38).

### The law the grid states

GREEN iff the membership slot is a hole. WALL iff a real hull-membership term
stands in the tuple. The four walled forms:

1. the direct pattern binding `a∈H` (D1, D17, and the protocol run);
2. the named reference `mem a a∈H`, whose type is checked in a small
   declaration that is itself GREEN and cheap (D11, against D12);
3. a pattern variable whose type already IS the goal's own spelling, so the
   slot check is syntactic (D14, against D15);
4. any of the above with the reading conv absent (D13, D17).

### What is ruled out

- NOT `conv0`'s comparison. D7 holed slot 4 and kept `conv0` real: GREEN at
  213.09 s (runs/d7memholed767.out:8,9,26). D1 kept both: WALL. The brief's
  W3 suspicion (the un-ascribed convert's comparison) is cleared.
- NOT the truncation plumbing. D6 holed the whole tuple: GREEN at 112.05 s
  (runs/d6tupleholed767.out:8,9,26). The two `PT.rec` binders, both `codeOf`
  applications, `PT.map`, and the `hullClosed` application under the map are
  all inside the floor's price.
- NOT the membership type comparison as such. The conv `HullM a` against
  `⟨ fst a ∈ˢ HS.M ⟩` is GREEN and cheap inside a named declaration: `mem`'s
  declaration costs nothing measurable (D12, 111.33 s, against the 109.31 s
  floor), and the supply shim's own `PT.map` restatement is the same (D15,
  111.63 s, runs/d15shimdecl767.out:8,9,26). `Probe673.agda:100-103`'s
  `bound-from-stage` is the same shape, tree-green.
- NOT the environment alone. D7 greens inside the same two `PT.rec` binders
  that D17 walls in; the only difference is the hole.

### What the wall therefore is

The wall tracks the PRESENCE of a hull-membership proof term inside the
goal-directed 8-component tuple, whatever its form: the raw pattern binding,
a named reference to it, or a variable typed at the goal's own spelling. The
membership proposition is the hull's truncated code search: `Hull = sett Code
(λ c → toSet (val c))` (src/L/Hull.lagda.md:114-115), restated as `M = H.T.Hull`
(src/L/BoundedSubset.lagda.md:910-911). The working hypothesis for the next
probe is that the elaborator, while instantiating the obligation's Sigma
under the two truncation binders, forces that sett-membership structure once
per remaining component and the forcing compounds over the FOL reading's own
membership atoms. The hypothesis is NOT confirmed; what is confirmed is the
grid above, and the grid is the finding.

### Why no permitted shape can carry the term

The obligation's Sigma requires a real membership proof at its fourth
component. Every real form of that proof walls (grid, forms 1 to 4). The
only legal filler of the reading slot is `conv0` itself: a stated-type
wrapper for the reading is the B8 shape the brief bans (premise 3, "the wall
is the comparison"), and `mkWit`'s spelled codomain is banned outright. The
brief's two permitted moves ("pack inline, or leave the convert's codomain
inferred") are both exhausted: the inline packing is the protocol run that
walled, and `conv0` stays inferred in every instrument. A shape that spells
the Sigma's membership component differently, or drops the component, changes
the OBLIGATION'S TYPE, and that is the mathematician's call, not this
dispatch's.

## 4. WHAT THE NEXT BRIEF NEEDS

- The grid of section 3 is the evidence base. Any next attack on this
  obligation should name the grid row it contradicts or the new shape it
  tries.
- A Sigma re-shape is now indicated by measurement: the membership component
  is the wall's site. If the obligation could carry `HullM z` instead of
  `⟨ z ∈ˢ HS.M ⟩` at that component, slot 4 becomes syntactic (D14's class);
  the grid predicts that class still walls (D14), so the re-shape would need
  to go further, and pricing it is a fresh dispatch, not an analogy.
- The supplied pieces stay on the meter at this site: the frame
  (runs/frame767.out:14,15,32), the hull half (runs/hullhalf767.out:4,5,22),
  `conv0` inside B2 (runs/b2conv767.out:7,8,25), the obligation type plus
  export (runs/floor767.out:7,8,25). This worktree's probe chain is now WARM
  (the cold closure was paid in the frame run), so a re-dispatch here starts
  at B1's 8.71 s class, not at 226 s.
- The four walls of the ascribed shape (B2, B8, conv-1, amb-1) stand
  untouched; nothing of that shape was retried. `conv-at-Lδ` was never
  approached.

## 5. SURVEY CHECK

Ran before return, as ordered. This worktree has no `.venv` of its own; the
pinned interpreter of the main checkout ran the gate. First run FAILED with
the ten unanswered names while the report was still its skeleton; the blocks
below were then written and the gate was re-run:

```text
$ /Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/check-survey-quotes.py LJ-1-767
check-survey-quotes: LJ-1-767 clean (0 note(s), 0 defect(s))
```

## 6. W2 ANSWER

Honored by consumption. The dispatch wrote no new mathematics: the frame is
the vendored Frame765 byte for byte below the module line, the hull half is
the vendored HullHalf765 with one import retargeted, `conv0` is the opened
`Spend` term of LJ-1.692, and `grounded-from-complete` is a composition of
those with `codeOf` and the truncation combinators. The generic carrier is
LJ-1.689's `hull-convert`, instantiated by LJ-1.692 at `matrix₃` and
re-exported through the frame; nothing was rewritten at a fixed form. The
rule's home names it: MAXIMUM REUSE is the architecture's objective, and it
is the same rule as WRITE IT GENERIC (archive/dev/DD-archived.md:22). The
tried shim `hullClosedM` was a restatement of `hullClosed`, not a second
mathematics, and it survives only in the bisect instruments, not in the
delivered probe.

## 7. W3 ANSWER

**NO-GO.** Whether `grounded-from-complete` at code coordinates checks at
`-M4g` when packing does not ascribe `conv0`: it does not. The un-ascribed
inline packing walls at the cap with peak RSS 4642603008 B
(runs/probe767-1.out:4,5,22), and four restructurings wall with it (section
3). The brief's estimate, "one B2 file plus inline packing", was correct
about the shape and wrong about the cost: the wall is not the packing's
comparison against the goal (D7 clears `conv0`, D6 clears the plumbing) but
the membership proof's presence in the tuple. The wall stops this packing at
`-M4g`, per the brief.

## 8. RATIO BAR

The write scope of this task carries no ` ```agda ` fence: the probe is a raw
`.agda.txt` (counts 0 by the bar's own rule) and this report is prose. The
divisor of this return is 0 and the bar cannot fire.

## ARCHIVE USED

- archive/dev/DD-archived.md:22 - READ. The line this return's W2 answer
  reports against: "MAXIMUM REUSE is the architecture's objective, and it is
  the same rule as WRITE IT GENERIC."
- archive/dev/ORCHESTRATION.md - declined, not read. Every clause that binds
  this dispatch is in the brief, the slot file and AGENTS.md; no
  loop-operation history was needed.
- archive/dev/PLAN-archived.md - declined, not read. This dispatch plans
  nothing; it runs one probe and reports a wall.
- archive/dev/TASKS-archived.md - declined, not read. The closed task index
  predates LJ-1 and names no obligation of this campaign.
- archive/dev/STATUS-archived.md - declined, not read. Standing status is
  `dev/pod/screen.toml` alone, and no pre-LJ-1 status row bears on this
  probe.

## LITERATURE USED

- dev/literature/glossary-review-2026-08.md - declined, not read. This
  dispatch wrote no mathematical prose and coined no term.
- dev/literature/BIBLIOGRAPHY.md - declined, not read. No source question is
  at stake in a transcription, a run grid and a wall report.
- dev/literature/primary-sources.md - declined, not read. Same reason: no
  literature content was consulted or judged.
- dev/literature/level-formula-slot-roles.md - declined, not read. The probe
  touches no level formula; the wall is an elaboration-resource finding.
- dev/literature/devlin-errata.md - declined, not read. No Devlin text is
  interpreted in this dispatch.
