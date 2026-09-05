# LJ-1.765-SPLIT-SPLIT report: grounded-from-complete at code coordinates

> C-22 skeleton, written before any run. Filled as each fact lands.

## HEAD

task: LJ-1.765-SPLIT-SPLIT
obligation: agents/tasks/LJ-1-765-SPLIT-SPLIT/Probe765SplitSplit.agda::grounded-from-complete
verdict: PENDING

## 0. THE ENVIRONMENT, MEASURED AT DISPATCH

Taken before the first Agda process started (2026-09-02, this worktree):

- Pane caliber, read at dispatch: `GHCRTS=[-A64m -I0 -M4g]`, the HEAVY
  tier (`echo $GHCRTS`).  It was never set or changed by me; the
  runner only echoes it into each `.out` (runs/run.sh:6).
- `sysctl vm.swapusage`: total 5120.00M, used 4009.31M, free
  1110.69M.  Tighter than the SSSSS dispatch's 1017 MB used
  (agents/tasks/LJ-1-728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT/lj-1.728-SPLIT-SPLIT-SPLIT-SPLIT-SPLIT-report.md,
  section 0); re-read before each heavy run and reported in section 3.
- `kern.memorystatus_vm_pressure_level`: 1 (normal).
- No agda process at dispatch (`pgrep -x agda` empty).
- Build state: `_build/2.8.0/agda` carries 708 `.agdai`, and `src/L/Hull.agdai`
  is among them, but NO task-probe interface exists (`find _build
  -name 'Probe652*' -o -name 'Probe692*' -o -name 'Probe673*' -o
  -name 'Probe667*'` is empty).  The warm chain below pays this
  worktree's one-time cold closure of the task-probe cone, one
  process per module.
- This worktree has no `.venv` of its own (`ls -d .venv`: absent);
  the pinned interpreter of the main checkout
  (`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, Python 3.11.16)
  runs the Python gates, as in every predecessor dispatch.

## 1. THE TRANSCRIPTION

Three vendor files were delivered in this task directory.  This
worktree carries neither `agents/tasks/LJ-1-765/` nor
`agents/tasks/LJ-1-765-SPLIT/` (the vendor imports retarget away from
both; `ls agents/tasks` shows no such entry), and the predecessor
reports the brief's premises cite are absent from this worktree, so
every premise is taken from the vendor files' own headers, which
carry the SSS worktree's measured verdicts, plus the in-tree 764
record.  Each file is transcribed under this task's namespace:

- `runs/Frame765.agda` from `VendorFrame.agda.txt`: module
  `LJ-1-765-SPLIT-SPLIT.runs.Frame765`.  Measured with comments and
  blank lines stripped from both sides (runs/vendor-frame.diff):
  exactly ONE non-comment line differs, the module line.
- `runs/HullHalf765.agda` from `VendorHull.agda.txt`: module
  `LJ-1-765-SPLIT-SPLIT.runs.HullHalf765`, the Frame import
  retargeted.  runs/vendor-hullhalf.diff: exactly TWO non-comment
  lines differ, the module line and that import.  The vendor's
  duplicated header block is carried byte-identically.
- `Probe765SplitSplit.agda.txt` from `VendorGFC.agda.txt`: module
  `LJ-1-765-SPLIT-SPLIT.Probe765SplitSplit`, the two interface
  imports retargeted.  runs/vendor-gfc.diff: the brief's TWO deltas
  and nothing else --
  (1) `GroundedFromComplete` re-declared AT CODE COORDINATES, the
  brief's type verbatim: the Sigma packs `ca`, `cp`, `z` and carries
  `fst (val ca) ≡ Lset δ`, `fst (val cp) ≡ δ` and the 3-slot reading
  at `(fst (val ca) ∷ fst (val cp) ∷ z)` as components;
  (2) `amb` DELETED and `mkWit` rewritten as pure packing
  (`ca , cp , fst a , a∈H , Lδ∈M , ca≡Lδ , cp≡δ , conv0 ca cp a sat`),
  so no subst runs along either code equation in this file.
  `conv0` is byte-identical to the vendor's: domain the inline
  spelling, codomain a solved meta `_`, definition unapplied.  No
  Convert hypothesis, no `conv-at-Lδ` inhabitant, Completeness
  consumed as Frame765's HYPOTHESIS.

The predecessor-supplied pieces consumed as delivered (coder clause:
the type a predecessor delivered is the type that predecessor's probe
measured): `codeOf` from Frame765 (frame-2 green, 14.41 s, SSS
worktree, VendorFrame.agda.txt:13), `hullClosed` from HullHalf765
(hull-3 green, 235.43 s, VendorHull.agda.txt:13-14), `conv0`'s
definition from [LJ-1.692]'s constructed `hull-convert-at-matrix`
(GO, agents/tasks/LJ-1-764/lj-1.764-report.md:4, re-verified in this
dispatch's warm chain, runs/warm-p692.out).  The unmeasured part of
this dispatch is exactly the brief's W3: the composition at code
coordinates.

## 2. THE FLOOR

PENDING

## 3. THE RUNS

PENDING

## 4. WHAT THE NEXT BRIEF NEEDS

PENDING

## SURVEY QUOTES CHECK

PENDING

## ARCHIVE USED

PENDING

## LITERATURE USED

PENDING
