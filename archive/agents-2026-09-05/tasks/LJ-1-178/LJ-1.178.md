# LJ-1.178: build `levelIn` and `cover` on the bypassed wall

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.7]` is blocked on `levelIn` and `cover`, and `theorem` does not
derive.** They are the oldest open names in this phase.

**`[LJ-1.160]` measured that the wall inside them is GONE.** Build them.

## WHY THIS IS NOW A BUILD AND NOT A WALL, and it is measured

**The wall was `π (Lset m') ≡ Lset (π m')`.** `[LJ-1.51]` titled it 「the term I
cannot write」. `[LJ-1.121]` reached it by a second method and stopped. **Four
dispatches went around it and nobody was ever funded to build the chapter.**

**`[LJ-1.160]` MEASURED that it is an artifact of WHERE the argument runs**, at
16 lines, green: **a hull is not transitive, the collapse image is.** So
absoluteness applies directly at the collapse image and nothing needs carrying
across. Both hypotheses come from **one crossing face**.

**`[LJ-1.151]` MEASURED that the instantiation half is separable**, so the two
halves do not have to land together.

## WHAT TO DO

1. **Read `agents/tasks/LJ-1-160/` WHOLE, including its probe.** It is the
   16-line argument and it is your starting point, not a summary of one.
2. **Build `levelIn`.** State it where its consumers use it (P-k), not where
   its proof ends.
3. **Build `cover`.**
4. **Then say whether `theorem` derives**, and if it does not, name exactly what
   is still missing. **That last answer is the deliverable even if the build
   stops short.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH BUILT.** Report the lines, the seconds as measured, and whether
  `theorem` derives. STOP.
- **ONE BUILT.** `[LJ-1.151]` measured the halves separable, so **landing one is
  a real result.** Report it and name what the second needs.
- **A NEW WALL.** Name the term you could not write, at `file:line`, and stop.
  **C-36 says write the term you could not write**, and this project's best
  returns have been refutations.
- **THE 16 LINES DO NOT REACH.** If `[LJ-1.160]`'s argument works in its probe
  and not at the real site, **that is the finding and it is worth more than a
  partial build.** P-l: a measured cure does not transfer by analogy, and this
  task is P-l's test case by construction.

## THE SUPPLY QUESTION, and check it BEFORE you build

**`[LJ-1.163]` measured that `ElemDown` was ALREADY SUPPLIED and in the wrong
place**, after three dispatches priced a term the tree already held. The cause
was a grep that excluded the file holding the answer.

**So before you write a line, grep the WHOLE tree for what you are about to
build, and include the file you think you already know.** Report the search you
ran. **C-38 as extended: a hypothesis is discharged when something SUPPLIES
it.**

## THE BAR, AND IT IS DD24 UNCHANGED

**The owner ruled 2026-08-14 that DD24 is the whole rule and that the readings
layered on it were the orchestrator's own. Read DD24 fundamentally:**

1. **The GCH bar was FIXED when the AC trophy landed. It does not drift.**
2. **EVERY GCH module uses that one number, new or old alike.**
3. **INTERMEDIATE DEBT IS ALLOWED**, because only the WHOLE GCH side, at the
   end, is judged against the bar.

**So report your lines and your seconds, and do NOT judge this build against a
tightened figure.** Record an overage plainly (DD8). **Never delete a line to
improve a ratio**; P-q measured 315 lines removed buying 11.8 s.

## THE INSTRUMENT

**`check-ratio.py` prints `noise band: at least +-12.8%, MEASURED [LJ-1.148]`.**
`[LJ-1.173]` spent most of a leg discovering that its own +6 s was inside it.
**A delta inside the band is not a small measurement, it is no measurement.**
Discard a warm-up and take at least three kept runs for any figure a decision
rests on.

## WHAT YOU MUST NOT DO

- **DO NOT TOUCH `src/L/Condensation.lagda.md` or the three `*Agree` masters.**
  Two siblings are working in them.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change
  there.
- **A probe goes in `agents/tasks/LJ-1-178/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Siblings
  are running. **Report the load beside every absolute figure.**
- **Report a heap exhaustion as a wall.** Never raise the cap.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**Write `levelIn` and `cover` generic in the carrier and in the ordinal, so the
J tower re-instantiates instead of paying again.** `[LJ-1.159]:263` measured
generic at **8.4 times CHEAPER** than fixed at a neighbouring site, and `:50`
states it as DD4 costing nothing there and paying 8.4 times. **The cluster's own
evidence says generic is cheaper here, not dearer.**

**A stop-line is NEVER a reason to write fixed.** Say so and stop for a
re-price.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-160/`**, the report and its probe, read WHOLE. **The
  16-line argument that removed the wall.**
- **`agents/tasks/LJ-1-151/lj-1.151-report.md`**: the separability measurement.
- `agents/tasks/LJ-1-146/lj-1.146-report.md`: the wall named twice by two
  methods, and why four dispatches went around it.
- `agents/tasks/LJ-1-163/lj-1.163-report.md`: the already-supplied term and the
  grep that missed it.
- **`archive/src/2026-08-09-rud-route/` and `archive/dev/TASKS-archived.md`.**
  **The retired route had a condensation chapter and `[LJ-1.160]` found its
  content at `Condensation.lagda.md:160-257` in the archive.** Read it. **Take
  SHAPE from the archive, never a claim**, and say what would not transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/j-hierarchy.md` and `devlin-II5.md`, `devlin-errata.md`.
**Say how Devlin gets the condensation transfer, and whether he needs the
commuting equation at all.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-160/` FIRST, whole, including the probe.

## SCOPE (write)

`agents/tasks/LJ-1-178/` for probes. **A build lands in `src/` only after you
have reported the measurement to me.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and `--for probe`.

- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-k, P-l, P-h, P-m, P-n, R-35, R-38, R-40, C-12, C-22, C-39, C-40.**
- **DD8, DD24, D-1, D-10, D-26, D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with what built and whether `theorem` derives.** Then the lines and the
seconds as measured, judged against nothing tightened. Then the supply search you ran before writing. Then
the DD4 re-instantiation answer. Then what `[LJ-1.7]` still needs. **Mark every
negative MEASURED or INFERRED.**
