# LJ-1.700: adversarial review of LJ-1.700#1

## HEAD
head_slot: coder_adversarial
machine: shared
task: LJ-1.700
predecessor: LJ-1.700#1
verdict: upheld

## METHOD, AND WHAT THIS REVIEW DID NOT RUN

This review is read-only. No Agda process was started. The caliber
the program set on this pane was `-A64m -I0 -M2g` (wide, tier of the
return under attack) and was not touched. The run facts come from
the accept arm written into this checkout,
`agents/tasks/LJ-1-700/runs/accept-1.out`, and from the coder's own
records under `agents/tasks/LJ-1-700/runs/`. A re-run of the same
probe shape would be the forbidden rerun, and a restructured probe
is outside this review's write scope of one file.

`dev/pod/transitions/2026-08.jsonl` holds no line carrying
`LJ-1.700` in this worktree. Its last line is `LJ-1.692`, seq 4617,
`2026-08-26T23:09:13Z`, which is before this task's first dispatch.
So `model`, `effort` and `heads_sha256` for LJ-1.700#1 are not
checkable here. Per the brief, no fact was inferred from that file.
The accept arm carries the six facts instead.

## QUESTION 1. DOES THE PREDECESSOR'S VERDICT LINE MATCH ITS OWN BODY?

No. This is the `[LJ-1.376]` failure class: a live record that
contradicts the live tree.

The verdict line reads: "SKELETON. Written before any Agda beyond
the predecessor read (C-22). Filled as each answer lands."
(`agents/tasks/LJ-1-700/lj-1.700-report.md:9-11`)

The answers landed and the report was never filled. Measured today
with `stat -f '%m %N'`, last-write order is:

```
1787796651  agents/tasks/LJ-1-700/lj-1.700-report.md
1787796760  agents/tasks/LJ-1-700/runs/floor-1.out
1787796821  agents/tasks/LJ-1-700/runs/floor-2.out
1787796861  agents/tasks/LJ-1-700/runs/floor-3.out
1787797044  agents/tasks/LJ-1-700/runs/floor-4.out
1787797201  agents/tasks/LJ-1-700/runs/p-1.out
1787797483  agents/tasks/LJ-1-700/runs/p-2.out
1787797624  agents/tasks/LJ-1-700/runs/p-3.out
1787797684  agents/tasks/LJ-1-700/Probe700.agda
1787797925  agents/tasks/LJ-1-700/runs/p-4.out
1787798013  agents/tasks/LJ-1-700/runs/accept-1.out
```

The report predates every run and the final probe shape. Against
that tree the body makes false claims:

- `:68` "THE FLOOR / Not yet run." The floor ran four times. The
  fourth completed: `136.38 real` and `1348927488 maximum resident
  set size` (`runs/floor-4.out:10-11`), `EXIT=42`
  (`runs/floor-4.out:28`), with the sole error an unsolved meta at
  the intended hole `FLOOR.agda:45.28-32` (`runs/floor-4.out:7`).
- `:93` "RUNS / None yet." Nine run records exist, eight by the
  coder plus the accept arm.
- `:72` W3 "Not yet run." The probe answers W3 in code:
  "SameHyp is not free: AbsL's carrier is not 𝒮ʟ", packed by `toL`
  (`Probe700.agda:54-58`), applied by `same-at-codes`
  (`Probe700.agda:61-66`).
- `:63` "The corrected target ... is recorded after the floor and
  the attempt." Never recorded. D-10's second half is undone.
- `:77`, `:81`, `:87`, `:97`, `:101`, `:105`, `:109`: W2, W4, P-l,
  price, resistance, next brief, gates, all "Not yet".

The return cited C-22 in its own law bundle
(`agents/tasks/LJ-1-700/lj-1.700-report.md:86`) and then left the
file untouched through nine runs. That is the measured failure the
law exists to prevent (`dev/LESSONS.md:2307`).

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A file:line THAT RESOLVES TODAY?

Every citation the report makes resolves today. Checked one by one:

- `Probe679.agda:48-49` `SameHyp`, `:73-78` `Completeness`,
  `:84-88` `HierInStage`, `:94-95` `CompletenessFrom`:
  all present at those lines in `agents/tasks/LJ-1-679/Probe679.agda`.
- `Probe673.agda:83-87` `inBound`, `:93-95` `BoundInStage`: present.
- `Probe520.agda:36-40` the 𝒮ʟ opening, `:192-195` `SameAsGraph`
  both directions: present.
- `Probe667.agda:72-76` `matrix₃` and `Δ₀-matrix₃`: present.
- `Probe692.agda:63-66` `hull-convert-at-matrix`: present.
- `lj-1.692-report.md:335-339`, "FUND Completeness / BoundInStage
  AT matrix₃ STILL ... not this unpack": present.
- `lj-1.679-report.md:8-10`, NO-GO on the closed term, GO on W3:
  present.
- `dev/LESSONS.md:1375` D-10, `:1735` D-26, `:2307` C-22, `:2367`
  P-l, `:3762` C-42: each heading sits at its cited line.
- `src/L/Hull.lagda.md:153` the `AbsL` module over the stage
  membership: present.
- `src/L/Constructible.lagda.md:405-406` `Lset→isL`: present, and
  the probe's `toL` at `Probe700.agda:57-58` uses it as cited.

The defect inverts the rule. The claims that carry the work, the
runs, the wall, the W3 answer and the obstruction argument, have no
citations at all, because the report denies the work happened. The
one load-bearing mathematical claim, that the two hypotheses do not
reach `BoundInStage` (`Probe700.agda:76-79`), lives only in a
comment of a file that no run ever typechecked: `p-2`, `p-3` and
`p-4` all died at the cap. So the NO-GO's outcome is a fact of the
accept arm, and its stated reason is an unverified assertion.

One pointer defect, in the dispatch and not in the predecessor: this
review brief names the three questions at
`dev/memos/LJ-4-pod-program-design.md:2853-2858`. Those lines carry
branch-table prose. The list itself sits at `:2984-2988`. The
questions were answered as written.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE?

No. Section 11, "WHAT THE NEXT BRIEF NEEDS", is "Not yet written"
(`agents/tasks/LJ-1-700/lj-1.700-report.md:105`). Missing items:

1. **The heap wall, unreported.** Three kills of `Probe700.agda`
   under the wide cap: `262.67 real`, `2118500352 maximum resident
   set size` (`runs/p-2.out:5-6`); `26.96 real`, `2305032192`
   (`runs/p-3.out:5-6`); `221.14 real`, `2323808256`
   (`runs/p-4.out:5-6`); all `EXIT=1` (`:24` of each). The run
   durations show shape changes between attempts, so restructures
   were tried, and the wall survived them. None of this is in the
   return. The branch `heap-wall-park` never fired because the arm's
   own run died `rc -9 seconds 4.82` (`runs/accept-1.out:16`) with
   `error class other` (`:22`) and `heap_wall` false, which is an
   anomaly against the coder's own 27 to 262 second runs, not a
   measurement of the file. The wall is a resource fact of the
   probe's presentation, and the record, not the report, is its only
   home.
2. **The wall is already localized, and the return does not say so.**
   `FLOOR.agda.txt` carries the same `Spend` telescope with a hole
   for the term and checks in `136.38` seconds at `1348927488`
   bytes (`runs/floor-4.out:10-11`). `Probe700.agda` adds `toL`,
   `same-at-codes` and `hier-at-code` and dies above `2300000000`
   bytes. The cost sits in the three added definitions. The likeliest
   single cause is the inference-heavy `hier-at-code`, whose target
   type is `_` (`Probe700.agda:70-74`). The untested cure the return
   missed: an explicit codomain there, and the lemmas checked one at
   a time, which is the narrowing the heap-wall ruling asks for.
3. **The unwritten scope file.** The brief's write scope names
   `agents/tasks/LJ-1-700/review-of-completeness-from-hier.md`. It
   was never written. Rows `stop-stated` and `no-go-stated` key on
   it, so the NO-GO never reached its intended route.
4. **W2, W4 and P-l** stand "Not yet answered" (`:77`, `:81`, `:87`).
5. **The floor's positive fact is unspent.** The obligation TYPE
   `A.CompletenessFrom` is expressible at this frame, green against
   a hole (`runs/floor-4.out:7-11`). What is missing is one term.
   That fact prices the next attempt and appears nowhere.

## WHAT THE RETURN DID RIGHT

Scope discipline held: all 12 changed files are the task's own,
none foreign (`runs/accept-1.out:17-18`, `:25`). The `.agda.txt`
naming rule was followed, and no stray `.agda` sits under `runs/`.
The floor came before the attempt. Every citation that was written
resolves. The four-lens finding "is the measurement sound" is yes
for the floor and yes for each run record as a record; the defect is
that the report omits them.

## VERDICT

**Upheld.** The predecessor's NO-GO is correct on its own outcome.
The obligation `completeness-from-hier` is not defined anywhere in
the tree (`Probe700.agda:76-79` says so in code); conjunct 1 FAILED
(`runs/accept-1.out:10`), `obligations delta 0` (`:20`), one
obligation still open. The accept-run kill does not carry the
verdict: the missing definition alone holds conjunct 1 down. No cure
in the record inhabits the term, and the probe's obstruction
argument is coherent and unrefuted. A GO would need a green term;
nothing green exists.

The agreement is with the OUTCOME, not with the record. The return's
defects, the unfilled report, the unreported wall, the unwritten
scope file and the empty enumeration, are findings for the
mathematician who reads this pair. The next dispatch, if any, should
start from item 2 above: the wall is in three definitions, the floor
already paid for the telescope, and an explicit codomain on
`hier-at-code` is the first move nobody has tested.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** `archive/dev/DD-archived.md:35`
  carries, verbatim, the span

  ```
  is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed
  ```

  This is the four-question lens this review attacked with, confirmed
  at its cited home before use.
- **`archive/dev/ORCHESTRATION.md` READ at one line.** The line
  `archive/dev/ORCHESTRATION.md:1` reads, verbatim:

  ```
  # ORCHESTRATION: the orchestrator's operating rules
  ```

  Used only to confirm the predecessor's decline quote. Not
  otherwise used: this review consults no dispatch process document.
- **`archive/dev/PLAN-archived.md` READ at one line.** The line
  `archive/dev/PLAN-archived.md:1` reads, verbatim:

  ```
  # ARCHIVED 2026-08-20
  ```

  Used only to confirm the predecessor's decline quote. The live
  status is `dev/pod/screen.toml`.
- **`archive/dev/TASKS-archived.md` READ at one line.** The line
  `archive/dev/TASKS-archived.md:1` reads, verbatim:

  ```
  # Archived task index: the `L3.32-T` series
  ```

  Used only to confirm the predecessor's decline quote. That series
  is not a predecessor of this composition.
- **`archive/dev/measurements/README.md` READ at one line.** The
  line `archive/dev/measurements/README.md:1` reads, verbatim:

  ```
  # Archived measurement records
  ```

  Declined beyond that line: the memory and wall numbers in this
  review are primary records of THIS task under
  `agents/tasks/LJ-1-700/runs/`, and no archived measurement was
  needed to read them.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.** The line
  `dev/literature/level-formula-slot-roles.md:27` reads, verbatim:

  ```
  | 5 | Devlin 5.2 (b) | `(∀γ<α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z,v,γ)]` | same | `z` | `v`, `γ` | **VALUE, ORDINAL** | `_build/literature/dev2.txt:1193-1198` |
  ```

  The line `dev/literature/level-formula-slot-roles.md:60` reads,
  verbatim:

  ```
  Devlin's `∃w` carries the conjunct `K(w,u)`, "which says `w = K(u)`"
  ```

  Both of the predecessor's quotes resolve at those lines. This file
  is the literature basis of the obligation under review and it was
  used to check the predecessor's reading of the target.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Line 1 reads,
  verbatim:

  ```
  # Bibliography for the rud route
  ```

  Not used: this review adds no citation and misses no source.
- **`dev/literature/devlin-errata.md` DECLINED.** Line 1 reads,
  verbatim:

  ```
  # Devlin errata: documented error classes (do-not-repeat checklist)
  ```

  Not used: no scanned quote is under review.
- **`dev/literature/primary-sources.md` DECLINED.** Line 1 reads,
  verbatim:

  ```
  # Primary sources, second round: Jensen manuscript, Devlin, Jech
  ```

  Not used: the slot arithmetic was already carried by
  `level-formula-slot-roles.md`.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Line 1
  reads, verbatim:

  ```
  # Glossary review: the 119 pre-protocol entries
  ```

  Not used: no naming question arose and no glossary entry is
  proposed.
