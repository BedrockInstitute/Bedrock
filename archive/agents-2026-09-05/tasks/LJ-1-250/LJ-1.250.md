# LJ-1.250: price `StepAgree` and `ApproxAgree`, the last two named lemmas

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.249]` closed the chapter question: there is no chapter.**
`graph-assembly` ports to the `(M, M-trans)` class abstraction, exit 0, 132
non-blank code lines, and its 30-line assembly block is
`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:53-88` VERBATIM with three
renames.

**`[LJ-1.7]`'s whole remaining gap is TWO LEMMAS:**

```agda
StepAgree    -- hypothesis of graph-assembly
ApproxAgree  -- hypothesis of graph-assembly
```

**They enter `agents/tasks/LJ-1-249/ProbeLJ1249.agda` as hypotheses of the
assembly block.** **The source names them in a comment at
`src/L/Condensation.lagda.md:5433-5434` and they exist NOWHERE as code.** **I
grepped `src/` myself: those two names occur only in that comment.**

**Price them. Build them if they build.**

## WHY THIS IS THE LAST STEP AND NOT ANOTHER LINK

**Everything above them is green:** `graph-assembly` derives
`graphBndAt → LsetGraphAt` from exactly these two, and `ProbeLJ152A.agda:58-73`
closes the rest to `fst w ≡ Lset (fst γ)`, which is `go`'s own conclusion at
`agents/tasks/LJ-1-184/ProbeLJ1184B.agda:118-120`.

**Everything below them is green:** the BS templates are re-expressed at the
generic carrier in `ProbeLJ1249.agda`, and `[LJ-1.238]` ported
`L.Coding.Sequence` at per-tower residual ZERO.

**So these two are the join, and nothing else in `[LJ-1.7]`'s residue is
unbuilt.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH BUILD.** Report their written lines and the seconds. **Then `amb` is
  supplied outright, `[LJ-1.7]`'s four hypotheses become three SUPPLIED and one
  BUILT in shape, and phase 1's blocking row moves for the first time since it
  opened.** STOP. **This is the outcome.**
- **ONE BUILDS.** Say which, with its lines, and **name what the other needs**
  (C-36). **A half here is a real result.**
- **NEITHER BUILDS, AND HERE IS THE TERM.** **Name it at `file:line`.** **Then
  `[LJ-1.7]`'s residue is ONE named term and the project can price it exactly.**
- **A LEMMA IS FALSE.** **`[LJ-1.244]` priced a refutable target and
  `[LJ-1.246]` caught it.** **Before you spend a run, check that each lemma's
  statement is constrained: if a parameter is free, the statement may be
  satisfiable by absurdity and unprovable at the same time** (D-10).
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law). **Your control is
  `ProbeLJ1249.agda` at 0.78 user seconds warm.**

## WHAT IS GREEN, so you assemble rather than invent

| file | what it is | state |
|---|---|---|
| `agents/tasks/LJ-1-249/ProbeLJ1249.agda` | the ported assembly, 132 lines, the two lemmas as hypotheses | exit 0 |
| `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda` | the original, unported | exit 0 TODAY, 9.10 s |
| `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:58-73` | the rest of the chain to `go`'s conclusion | read it |
| `agents/tasks/LJ-1-238/GenSequence.agda` | the six readings, residual 0 | exit 0 |

**Start from `ProbeLJ1249.agda` and replace the two hypotheses with proofs.**
**Everything else in that file is measured and must not move.**

## THE LEAF IS WHERE THE WORK IS, and `[LJ-1.249]` measured that

**`[LJ-1.249]` measured that the per-tower content enters the port as
CONSTRAINED parameters: the BS leaf `ψs : Formula S 13` and
`ψa : Formula S 15` (the `DefBodyB` instantiations), and the At leaf trio
`DefAt` / `DefAt-in` / `DefAt-out`.**

**`StepAgree` and `ApproxAgree` are exactly the statements that those two
leaves agree.** **So this is leaf adequacy, and `src/L/Condensation.lagda.md`
already carries leaf adequacy for the OTHER direction.** **Find it and say
whether it transfers.**

## WHAT YOU MUST NOT DO

- **Do not re-port `graph-assembly`.** It is green at 132 lines.
- **Do not touch `[LJ-1.8]`'s blocks.** A sibling may be pricing them.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-250/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## FIVE RULES THIS AREA EARNED THIS WEEK

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.** This whole line of work exists because
a reviewer opened `agents/tasks/archive/LJ-1-52/` after three reports had not.

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**`exit 0` IS NOT A SUPPLY** (C-45). **Audit the instantiation, never the
telescope.**

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.249]` MEASURED that the assembly is paid ONCE for both towers and
that only the leaf is per-tower.** **`StepAgree` and `ApproxAgree` sit exactly
at that leaf.**

**So say plainly: are these two lemmas per-tower, and what is their line
count?** **That number IS phase 1's last per-tower figure**, and
`[LJ-1.248]` measured the rest of the route's per-tower half at 146 lines.

## ARCHIVE (DD18)

- **`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`** and **`ProbeLJ152A.agda`**,
  read WHOLE. **`[LJ-1.52]` is where these two lemmas were named and its
  report may say why they were not built.**
- **`agents/tasks/LJ-1-249/lj-1.249-report.md` and `ProbeLJ1249.agda`**, read
  WHOLE. **Your starting file.**
- `agents/tasks/LJ-1-246/lj-1.246-report.md`: how the gap was found.
- `agents/tasks/LJ-1-238/GenSequence.agda`: the ported readings.
- **`src/L/Condensation.lagda.md:5433-5434` and the leaf adequacy around it:
  read the source.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`[LJ-1.246]` measured that the second coding is load-bearing for a COMPLEXITY
reason: the Sequence coding carries ZERO Δ₀ certificates while `crossOut`
spends `Σ₁ Cr.φP`.** **Say whether these two lemmas touch that gap or leave it
whole.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-249/lj-1.249-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-250/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **D-10.** **Check each lemma's statement is CONSTRAINED before you spend a
  run.** `[LJ-1.244]` priced a refutable target.
- **C-36.** Write the term you could not write.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-44, C-45.** A claim is unchecked until you check it; audit the
  instantiation.
- **P-l, C-42, C-39, C-40. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12,
  C-22. DD0, DD8, DD18, DD24, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `StepAgree` and `ApproxAgree` BUILD, and with their written
lines.** Then whether `amb` is supplied outright with them in place. Then
whether the delivered leaf adequacy transferred. Then the seconds with load and
run count. Then their per-tower line count. **Mark every negative MEASURED or
INFERRED.**
