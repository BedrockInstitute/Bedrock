# review-of-LJ-1-662-1: the stop is UPHELD

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.662
attacked_return: agents/tasks/LJ-1-662/lj-1.662-report.md (with agents/tasks/LJ-1-662/review-of-hoodexists.md)
verdict: upheld

**THE VERDICT.** The stop stands. I verified the stop's central fact
independently at its sources, and it holds: the obligation as pinned cannot be
earned for ANY choice of `LevelHood0`'s parameters, because the only `KFacts`
in the tree sits at fourteen environment columns and the pinned shape offers
five committed roles. The task closes on this file (row
`sys-critic-upheld-no-go`).

**ONE SUBSIDIARY MEASUREMENT IS REFUTED**, and the refutation does not touch
the verdict: the report's WALL 1 (the transparent-formula heap wall) is a
watchdog kill misread as a heap exhaustion. Section R below gives the
evidence. The stop does not rest on it.

**THE TRANSITIONS FILE ENDS BEFORE THIS INSTANCE.** This worktree's
`dev/pod/transitions/2026-08.jsonl` carries exactly one `"task": "LJ-1.662"`
line, seq 4314, `to: READY`, ts `2026-08-26T08:25:27Z`. It ends before
attempt #1 was dispatched, so the run's `model` and `effort` are not in this
checkout and I do not infer them. The six facts of the attacked run come from
the accept arm: `runs/accept-1.out:10-23` records all six conjuncts held,
exit 0, error class None, heap_wall false, in-fence lines 0, obligations
delta 0 with 1 open, 68 changed files and all 68 in scope.

## QUESTION 1. The verdict line against its own body: THEY MATCH.

The verdict line says STOP, pinning done and green, blocker one layer earlier
than the brief's named risk (`lj-1.662-report.md:9-13`). The body delivers
exactly that:

- The pinned formula exists and is green: `Probe662.agda:122` (`φ₀`), with
  `count-hood2 = refl` at `:119-120` and `φ₀-inv` at `:127`. The names meter
  confirms all 21 delivered names green (`runs/meter-names.out`,
  `0 UNRESOLVED of 21, 11.05 s, probe_red=False`).
- The obligation is absent, not broken: `runs/meter-obligation.out` reads
  `missing exit=42 ... 1 UNRESOLVED of 1, probe_red=False`. The probe carries
  `hoodexists-at-levelhood0-from-cover` (`Probe662.agda:326`) and
  `-from-sat` (`:331`), never the bare obligation name, which matches.
- The transport the brief called the risk is built and green:
  `hoodExistsP-from-cover` (`Probe662.agda:215-255`).
- The accept facts agree with the stated stop: exit 0, obligation still open
  (`runs/accept-1.out:16,20-23`), and the stop file
  `review-of-hoodexists.md` is in the changed set, which is the
  `stop-stated` branch of the brief (`LJ-1.662.md:81-89`).

No `[LJ-1.373]`-class mismatch is present.

## QUESTION 2. Does every load-bearing `file:line` resolve today? ALL BUT ONE.

I opened every citation that carries the verdict. Each resolves in this
worktree today:

- `src/L/Condensation.lagda.md:6079` is `record KFacts {n} (A K N0 ... N11 : Fin n)`,
  and its fields at `:6082-6093` are twelve `tagEq` equations, each demanding
  a DISTINCT `numeralL k` for k = 0..11. Twelve distinct values need twelve
  distinct columns, plus the carrier `A` and the bound `K`: fourteen.
- The one ground value: `Kenv : S ^ 14` (`:7389`) and
  `facts : KFacts iA iK i0 ... i11 Kenv` (`:7411`), built by `refl`s at
  `:7413-7415`.
- `LevelHood0` takes twenty-eight parameters at `Fin 5` and `Fin 7`
  (`src/L/BoundedSubset.lagda.md:841-842`), instantiates `LevelHood {0}`
  (`:844`), and its matrix is `Formula CS.S 4` (`:848-849`): four free slots
  plus the one bound witness inside the `∃̇∈` (`:108-111`). Five committed
  roles. Twelve distinct numeral columns do not fit in five. The counting
  fact of `review-of-hoodexists.md` section 3 is TRUE.
- `LevelHood` has no consumer: `grep -rn "LevelHood" src/` outside
  `src/L/BoundedSubset.lagda.md` returns 0 lines today. The chapter's own
  words at `src/L/BoundedSubset.lagda.md:901-902`: "the level-hood
  instantiation at the hull is the priced residue".
- `graphBndAt` occurs at exactly six lines in `src/` today
  (`src/L/Condensation.lagda.md:2492,2493,2495,2496`;
  `src/L/BoundedSubset.lagda.md:111,115`), all definitional. No adequacy
  theorem for the bounded graph exists anywhere in `src/`.
- The delivered adequacy is unbounded and at the class carrier: `Lset-only`
  (`src/L/Hierarchy.lagda.md:334`), `Lset-defines` (`:646`), ridden at
  `src/L/Condensation.lagda.md:423-431`.
- `HoodExistsP` at `agents/tasks/LJ-1-653/Probe653.agda:283-287` and
  `levelin-from-hood-pf` at `:289`; `[LJ-1.657]`'s three-hypothesis route at
  `agents/tasks/LJ-1-657/Probe657.agda:435-437`, its `LevelFormulaP` `Σ` at
  `:412-419`, its `Code` inhabitant at `:81`, its stale `PiReflectsOrd`
  comment at `:118-121`; `[LJ-1.654]`'s delivered term at
  `agents/tasks/LJ-1-654/Probe654.agda:295-297`; `[LJ-1.650]`'s
  `cover-in-stage` at `agents/tasks/LJ-1-650/Probe650.agda:333-347`, and it
  is indeed about the covering ORDINAL, so the report's premise-3 distinction
  is real; `elem-down = HEDC.elem-down` at
  `src/L/BoundedSubset.lagda.md:1667-1668` with the code selection at
  `agents/tasks/LJ-1-609/Probe609.agda:345`; P-l at `dev/LESSONS.md:2367`;
  the watchdog's backstop, floor and `kill -9` at
  `scripts/ops/agda-watchdog.sh:17,21,26,32`.
- The run numbers re-verified: floor-1 shows the five predecessor probes
  checked in this worktree (`runs/floor-1.out:5-9`); the ten green forced
  checks are as tabled, median wall 28.56 s and median peak 1,551,212,544
  bytes recomputed from the ten files, highest green peak 1,735,344,128
  (`runs/p-final-13.out`); `runs/join-2.out` 1,472,004,096 exit 0;
  `runs/b7-1.out` 1,293,303,808 exit 0 against the 699,842,560 floor
  (`runs/floor-2.out`), so the projection measurement is sound.

The one citation that does NOT resolve is the report's `runs/p-3.out` claim.
Section R.

Two harmless wobbles, for the record. The report says the probe is 342 lines;
`wc -l` says 343. The stop file's section 3 names the matrix environment
"five slots, `w ∷ u ∷ v ∷ γ ∷ K ∷ []`" while the chapter writes the four
free slots `u ∷ v ∷ γ ∷ K` with the witness `w` bound inside
(`src/L/BoundedSubset.lagda.md:69-72`, `:847`); the count of committed roles
is five under either naming, so the counting argument is unaffected.

## R. THE REFUTATION: WALL 1 is a watchdog kill, not a heap wall.

The report states: "`runs/p-3.out`: exit 251, `Heap exhausted`, at 10.57 s"
(`lj-1.662-report.md:168-169`), and the probe's comment repeats it
(`Probe662.agda:101-108`). The file says otherwise.

1. `runs/p-3.out` records `time: command terminated abnormally` (`:5`),
   NO Agda diagnostic anywhere, `611,270,656` maximum resident (`:7`),
   `972,424,464` peak footprint (`:23`), and `EXIT=1` (`:25`). Both memory
   numbers are far under the 2,147,483,648 cap.
2. Every genuine heap wall in this task's record prints the diagnostic and
   exits 251: `runs/p-4.out`, `runs/p-5.out`, `runs/b2-1.out` all carry
   `agda: Heap exhausted;` and `EXIT=251`. The report itself teaches the
   other signature: "The killed runs record `EXIT=1` with no Agda diagnostic
   at all" (`lj-1.662-report.md:239-240`). `p-3.out` wears exactly that
   signature.
3. The MAIN checkout's watchdog log carries
   `2026-08-26 19:19:38 KILLED agda pid=80356 (free 3% < 8%)`. `p-3` started
   `2026-08-26T11:19:27Z` (`runs/p-3.out:3`), which is 19:19:27 on this
   box's clock, and died 10.57 s later: 19:19:38, the kill stamp to the
   second. The report quoted this same log but only from `19:38:22` onward
   (`lj-1.662-report.md:245-252`), and left the `19:19:38` and `19:20:39`
   lines unattributed. This is the defect class the report itself warns
   about two pages later (the stale worktree log, "nearly recorded the wrong
   cause", `lj-1.662-report.md:273-275`), applied one run too late.

Consequences, and what survives:

- "The cure is P-l ... seal the formula" and "THE SEAL WAS NECESSARY"
  (`lj-1.662-report.md:170-175`) are NOT measured. The transparent shape was
  never shown to exhaust the heap; the watchdog killed it under system
  pressure at 0.97 GB. Only the second half is measured: the SEALED file
  genuinely walled (`runs/p-4.out`, exit 251). A measured cure does not
  transfer by analogy, and here the cure was recorded without its
  measurement. The next worker must not quote WALL 1 as a P-l datum.
- The closing move survives untouched: the projection change is soundly
  measured (`runs/b7-1.out` against `runs/floor-2.out`, `runs/p-7.out`
  against `runs/p-12.out`, `runs/join-2.out` green with 0.6 GB spare), and
  the delivered file is green ten forced times. The seal is harmless and
  stays; only its NECESSITY claim falls.
- If anyone wants the necessity fact, the probe to specify (A21: a coder
  writes and runs it, never this slot): re-run the `p-3` shape, reconstructed
  from `runs/` copies, under the same caliber on a box above the watchdog's
  free floor, and read the exit. I name it and stop there. Nothing in this
  review depends on its answer.

## QUESTION 3. Is the enumeration complete? YES, where the verdict lives.

- The route enumeration is complete. The fork in `review-of-hoodexists.md`
  section 4 plus the report's third option (`lj-1.662-report.md:369-373`) is
  the full space: pay arity 2, pay fourteen pinned columns, or internalize
  the numerals into the formula (named, unpriced). I looked for a fourth
  route through Δ₀ absoluteness and it is not one: the matrix being Δ₀ moves
  satisfaction between carriers, but someone must still prove the bounded
  graph formula TRUE of the pair (`Lset γ`, `γ`) somewhere, and the six-line
  grep shows no adequacy theorem for `graphBndAt` exists to ride.
- One refinement, and it STRENGTHENS the stop: the stop file says the tree
  carries exactly one value of `KFacts` (`review-of-hoodexists.md`
  section 2.4). There is also a second constructor, `KFactsCons`
  (`src/L/Condensation.lagda.md:6122-6130`), which the stop did not name. It
  only rebuilds an existing `KFacts` at a WIDER environment, from `n` to
  `1 + n`, so every `KFacts` still descends from the one ground value at
  fourteen columns and no path shrinks fourteen toward five. The count
  stands. (`src/L/Condensation/TwelveAgree.lagda.md:407` builds an `LFacts`,
  a different record, and is not a counterexample.)
- The kill enumeration is NOT complete, and that is section R: two log lines
  unattributed, one of them `p-3`. It costs the WALL 1 narrative, not the
  verdict.
- The brief's part in the outcome, stated so the next brief can pay it: the
  obligation was pinned to "the chapter's `LevelHood0` shape"
  (`LJ-1.662.md:12-14`), and the counting fact makes that pin unearnable for
  EVERY parameter choice, so the brief foreclosed a GO from the start. Its
  NO-GO clause also pre-named the wrong earn (the transport,
  `LJ-1.662.md:62-64`). The worker answered the brief it was given and then
  correctly relocated the blocker; the stop is the brief's own defect
  surfacing, and the report's section 7 hands the successor the maximal
  green structure (`hoodexists-at-levelhood0-from-sat` needs `SatAtLevel φ₀`
  and `ElemDown` only, `Probe662.agda:331-333`). No cure that closes THIS
  pin was missed.

## ARCHIVE USED

- **`archive/dev/DD-archived.md`: READ.** At `archive/dev/DD-archived.md:35`:
  `| DD25 | **A NEGATIVE RETURN IS ADVERSARIALLY REVIEWED AT MAXIMUM EFFORT, IMMEDIATELY, AND THE TWO ARE THEN READ TOGETHER. THE HEADS COME FROM THE SWITCH.**`
  is where the line begins; it is this review's own mandate and the home of
  the four-question lens I attacked with.
- **`archive/dev/ORCHESTRATION.md`: NOT USED, declined.** The archived
  operating document binds no rule today, and this attack needed no history
  from it.
- **`archive/dev/PLAN-archived.md`: NOT USED, declined.** It carries no
  level-hood or `KFacts` mathematics, which is where this verdict lives.
- **`archive/dev/measurements/README.md`: NOT USED, declined.** Every
  measurement this review judges was re-read from this task's own `runs/`
  and re-run greps; no archived measurement was load-bearing.
- **`archive/dev/README.md`: NOT USED, declined.** An index; nothing in this
  review needed it.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`: READ.** At
  `dev/literature/level-formula-slot-roles.md:40`:
  `### 2.2 ONE bound binds ALL the unbounded quantifiers`
  I also confirmed the row at `:31` reads `**VALUE, ORDINAL**` as the free
  pair, as the report quotes it. Both support the pinning's shape (close the
  bound and the unused slot, keep value and ordinal), which I upheld as
  green; neither rescues the pin from the counting fact, which is about the
  `KFacts` environment and not about the free pair.
- **`dev/literature/devlin-errata.md`: READ.** At
  `dev/literature/devlin-errata.md:98`:
  `- Bounding quantifiers (10.6, p. 60): the proposed bounding class for the`
  The recorded defect in Devlin's own bounding class is a standing warning
  against assuming a bound adequate without proof, and it points the same
  way as this stop: the bounded graph's adequacy is exactly what the tree
  does not carry.
- **`dev/literature/BIBLIOGRAPHY.md`: NOT USED, declined.** This review
  cites no new source.
- **`dev/literature/primary-sources.md`: NOT USED, declined.** Nothing here
  rests on a fetched source.
- **`dev/literature/glossary-review-2026-08.md`: NOT USED, declined.** No
  term is added and no glossary entry is touched.
