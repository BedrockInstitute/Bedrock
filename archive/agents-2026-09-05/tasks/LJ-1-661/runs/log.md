# runs log, LJ-1-661

One Agda process per run. `.out` = agda stdout, `.time` = the
`/usr/bin/time -l -p` report, `.rc` = the exit code of the run.

- floor-0: first probe attempt. Red: `FOL.Count` exports no `module Cnt`
  (the `Cnt` instance had to be built, `runs/floor-0.out`). `.rc` records
  the witness meter's 42 (obligation `[NotInScope]`), the run's own
  tooling line.
- floor-1: probe with the count pin `LsetGraph-fo0 = refl`. Red, the
  measured count wall: `[UnequalTerms]` at `countFo LsetGraph ≡ 0`
  (`runs/floor-1.out`). `.rc` records the meter's 42 as above.
- floor-2: probe, final form. Green, 3.12 s, rc 0 (`runs/floor-2.out`).
  One earlier attempt of the same run exited 71 on a harness bug
  (`--interaction` with an input file); the bad invocation left no
  artifact.
- wall: `Wall661.agda.txt` copied to a temp `Wall661.agda`, run, copy
  removed. Red: exactly the two intended holes, `[UnsolvedInteractionMetas]`,
  rc 42 (`runs/wall.out`). One earlier wall run carried a stray
  `Cubical.Data.Fin` import that warned; the file was fixed and the run
  repeated, the clean one is on record.
