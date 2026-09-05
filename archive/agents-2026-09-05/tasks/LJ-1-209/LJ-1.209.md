# LJ-1.209: price the seal `[LJ-1.204]` named, 8.4 s at 420 ms per field

tier: opus (in-harness-subagent-mode), **selected by the CLOCK, not by a
ruling.** `scripts/dispatch_policy.py` reads `VERSION_IN_FORCE = 'auto'` and
Beijing time is inside the 14:00 to 18:00 peak window, so the in-harness Opus
leads. **This task runs Agda and the in-harness path does NOT pass through
`dispatch.py`, so C-12's slot accounting cannot see it: hold ONE process and say
so.**

## GOAL

**`[LJ-1.204]` found the only wing cure with a MEASURED cause, and left it
UNPRICED. Price it.**

**MEASURED by `[LJ-1.204]`:** `Deserialization` at
`src/L/Condensation.lagda.md` is 9,911 ms self today against 1,689 ms at
`[LJ-1.155]`, reproducible over three cold runs and **not transient**.

**The cause is OUR OWN `arNum` field**, the numeral component `[LJ-1.173]` added
to the `codesK` and `envK` telescope hypotheses when it cured 21 false fields.

**And the brief's obvious hypothesis was REFUTED with a measurement:** the full
transitive interface closure grew **0.85 percent** while cold `Deserialization`
grew **8.1 times**. A 0.85 percent size change cannot price a 714 percent time
change.

## THE CURE, in `[LJ-1.204]`'s own words, and it is a HYPOTHESIS

> **The price is pathological, not inherent.** A handful of small type fields
> cost 8.4 s, about **420 ms per field**, for a field that only names 「ar is a
> numeral」.

```agda
opaque
  isNumeral : S → Type (ℓ-suc ℓ)
  isNumeral x = ∥ Σ[ n ∈ ℕ ] (x ≡ # n) ∥₁
```

**Then write `isNumeral (fst ar)` at the type sites and `unfolding isNumeral` at
the proof sites.** If the inferred mechanism is right, the conversion checker
meets a stuck head and the 8.4 s pull stops.

**ITS LINEAGE IS MEASURED AND IT IS THIS PROJECT'S OWN:** `[LJ-1.145]` sealed
`satGraphAt` and took a definition from **2,459 ms to below 1 ms**. **P-t
licenses sealing a built formula wherever its consumers do not look inside.**

## P-l BINDS AND THAT IS WHY THIS IS A TASK

**`[LJ-1.145]`'s cure is a COMPARABLE, not a price.** A measured cure does not
transfer by analogy, and this project has paid for that three times: the seal
that cured Condensation moved `[LJ-1.152]`'s site by nothing, and `[LJ-1.154]`
then measured that its own seals were not load-bearing either.

**So: measure it here, at this site, or you have measured nothing.**

## THE COUNT THAT DECIDES THE PRICE

**`[LJ-1.204]` says「a handful of small type fields」cost 8.4 s at about 420 ms
each.** **Count them yourself before you price anything.** The `arNum`
components live in the three records and in `L/Condensation`'s telescopes;
`[LJ-1.173]` reported 6 record fields, 29 telescope entries, 11 destructuring
sites and 6 projections.

**A price built on「a handful」is not a price.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **CURED.** The seal lands, `Deserialization` falls OUTSIDE the within-series
  spread, and the four masters stay green by explicit exit code. Report the
  before and after with run counts. STOP.
- **THE SEAL DOES NOT REACH.** If the conversion checker still pulls, **say so
  with the profile.** That refutes the mechanism and it is a complete answer:
  P-l would have caught another analogy.
- **IT REACHES AND COSTS MORE THAN IT SAVES.** `unfolding` at every proof site
  is a real cost. **Price both sides and say which wins.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt it, report the elapsed seconds, and bisect. On 2026-08-14 one run
  reached 4 hours 15 minutes because its brief gave a heap cap and no clock cap,
  and the orchestrator's stop message QUEUED behind it and was never read.

## THE INSTRUMENT, and `[LJ-1.201]` corrected this project on it

**The ±12.8 percent in `check-ratio.py` is a ONE-MODULE BETWEEN-SERIES figure,
by that file's own words at `:72-76`. Within-series spread is 0.5 to 4.0
percent.**

**So use a WITHIN-SERIES PAIRED design**, same machine state, before and after
in one series. **A 3 s effect is measurable that way and is not measurable the
other way.** `[LJ-1.185]` applied the between-series band to an aggregate and
wrongly concluded no cure was measurable.

**A SIBLING MAY HOLD AGDA. Report the load beside every absolute figure, discard
a warm-up, and take at least three kept runs for any figure a decision rests
on.**

## WHAT YOU MUST NOT DO

- **Do not undo the 21 cured fields.** They are green, committed, and they are
  the mathematical content the wing needs. **The seal changes HOW the numeral
  property is stated, never WHETHER it holds.**
- **Do not delete a line to improve a ratio.** P-q measured 315 lines removed
  buying 11.8 s.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-209/`**, tracked, never deleted. **A
  master edit lands only after you report the measurement to me.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).** An agent died
  on 2026-08-14 having written nothing and its reasoning had to be salvaged from
  its terminal.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE BAR

**DD24 unchanged and nothing tightens it** (owner, 2026-08-14): the bar was
FIXED when the AC trophy landed, every GCH module uses that one number, and
INTERMEDIATE DEBT IS ALLOWED because only the whole wing at the end is judged.
**The wing's gap is 56 to 67 s, so 8.4 s is a seventh of it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **`[LJ-1.204]`'s mechanism is INFERRED
and you are the measurement.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`isNumeral` is a property of a set, not of a tower. Write it where BOTH towers
can use it**, and say how much re-instantiates for J. `[LJ-1.184]` measured that
six extra lines bought the second tower for a 167-line module.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-204/lj-1.204-report.md`**, read WHOLE with its probes.
  **The cause, the refuted hypothesis, the paired method, and the cure you are
  pricing.**
- **`agents/tasks/LJ-1-145/lj-1.145-report.md`**, read WHOLE. **The seal that
  went 2,459 ms to below 1 ms, and the transplant method that found it.**
- `agents/tasks/LJ-1-173/lj-1.173-report.md`: what `arNum` is, where it went,
  and the four aliases it arrives under.
- `agents/tasks/LJ-1-201/LJ-1.201-report.md`: why the paired design is the right
  instrument and the aggregate band is not.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature governs elaboration cost. Say so in one line.**

## SCOPE (read)

`agents/tasks/LJ-1-204/lj-1.204-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-209/` for probes. **A master edit lands only after you
report.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **P-l.** `[LJ-1.145]`'s cure is a comparable and not a price. **This task is
  P-l's test case by construction.**
- **P-t.** An average hides the term, and it licenses the seal.
- **P-q.** Lines removed do not buy seconds.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-y, P-k, P-m, C-12, C-22, C-36, C-39, C-40. DD0, DD8, DD24, D-1, D-10,
  D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`. Verify a per-module figure
  with `.venv/bin/python scripts/check-ratio.py --module <file> --runs N`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with the seal's measured effect on `Deserialization`, before and after,
and whether it is outside the within-series spread.** Then the count of `arNum`
sites you made yourself. Then the `unfolding` cost at the proof sites. Then the
four masters' exit codes. Then the wing's aggregate re-measured. Then the DD4
re-instantiation figure. **Mark every negative MEASURED or INFERRED.**
