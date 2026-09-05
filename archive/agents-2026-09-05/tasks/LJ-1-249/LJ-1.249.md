# LJ-1.249: port `graph-assembly` to the class abstraction, and find out whether the chapter exists

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.246]` specified this probe and I pass its specification through
unchanged. It gates whether `[LJ-1.7]` faces a chapter at all.**

**Re-point `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:35,37` from `𝒮ʟ` to
the `(M, M-trans)` abstraction that `agents/tasks/LJ-1-238/GenSequence.agda:14-24`
already uses, and see whether `graph-assembly` still typechecks.**

**About 90 lines. The comparable is 1.95 s, and P-l says that is a comparable
and not your price.**

## WHY THIS GATES A CHAPTER

**`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:70-78` is ALREADY PROVED AND
GREEN.** It derives

```agda
graph-assembly : (step : StepAgree) (approx : ApproxAgree)
               → … → ⟨ … ⊨ graphBndAt ⟩ → ⟨ … ⊨ LsetGraphAt … ⟩
```

**That is exactly the `graphBndAt → LsetGraphAt` direction `q'` needs**, and
`ProbeLJ152A.agda:58-73` closes the rest to `fst w ≡ Lset (fst γ)`, which is
`go`'s conclusion at `agents/tasks/LJ-1-184/ProbeLJ1184B.agda:118-120`.

**I re-derived both of these myself.**

**If it ports, the gap is two named lemmas and not a 1,264-line bridge.**

## WHAT THE GAP ACTUALLY IS, and the source names it in a comment

**`src/L/Condensation.lagda.md:5433-5434` reads:「the consumers of the leaf
adequacy (`[LJ-1.52]` `StepAgree`/`ApproxAgree`/`GraphAgree` …)」.**

**MEASURED, and I checked: `StepAgree` and `ApproxAgree` occur in `src/` ONLY
in that comment. They exist nowhere as code.**

**`[LJ-1.244]` named three other terms as blocking. All three are DELIVERED**
(`TagAgree` at `:6628-6655`, the transfer at `:6802-7054`, `isCodeBS` at
`:1733`). **The gap is one row up from where it looked.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT PORTS.** Report the written lines and the seconds. **Then the chapter
  does NOT exist: `[LJ-1.7]`'s gap is `StepAgree` and `ApproxAgree` plus this
  port, and I price those two next.** STOP. **This is the outcome the whole
  chain has been reaching for.**
- **IT PORTS BUT NEEDS A NEW HYPOTHESIS.** **Name it** (C-36). **A named
  hypothesis is a priceable object; a chapter is not.**
- **IT DOES NOT PORT.** **Name the term that pins `𝒮ʟ`** at `file:line`.
  **Then the 1,264-line upper bound is live and the owner has a chapter
  decision.**
- **THE ARCHIVED PROBE IS NOT GREEN TODAY.** **Run it first, unported, and
  report the exit code before anything else.** **`[LJ-1.235]` did this for
  `[LJ-1.124]` and it turned a 2026-08-13 memory into a live fact.** **If it is
  red, say so and STOP: everything below rests on it.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law). **Your control is step
  zero.**

## WHAT `[LJ-1.244]` GOT WRONG, so you do not inherit it

**Its `module Attempt` left `Graph` (`:45`) and `φ₀` (`:68`) as UNCONSTRAINED
parameters, and `φ₀` occurs in no hypothesis of that telescope except `q'`'s
own statement.** **So the statement was REFUTABLE, not merely unproven:
`⊥̇` for the formulas and `⊤̇` for `φ₀` satisfies all six readings by absurdity
while `q'` fails.** **Exit 42 priced a false target** (D-10).

**Do not repeat that shape. If you introduce a parameter, say what constrains
it.**

## WHAT YOU MUST NOT DO

- **Do not build `StepAgree` or `ApproxAgree`.** **You port the assembly ABOVE
  them.** They are the next dispatch.
- **Do not port the delivered bridge.** All three of `[LJ-1.244]`'s named terms
  are already in `src/`.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-248/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-249/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`.**
- **A probe whose module name predates the one-directory-per-task move needs
  its include path set from the task directory** (`[LJ-1.235]`).
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## FOUR RULES THIS AREA EARNED THIS WEEK

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.** **This task exists because a reviewer
opened `agents/tasks/archive/LJ-1-52/` after three reports had not.**

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**`exit 0` IS NOT A SUPPLY** (C-45). **Audit the instantiation, never the
telescope.**

**C-36: A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY**, and C-44: **if
THIS brief states anything you cannot find, say so and treat it as unproven.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.246]` tested `[LJ-1.244]`'s tower split and found it WRONG AT THE
TOP:** `graph-assembly` names only `graphBndAt`, `LsetGraphAt`, `StepAt` and
`ApproxAt`, all Def-side instantiations of templates whose generic form
exists, **and only the `DefBodyB`/`DefBody` leaf is per-tower.** **So the
assembly is paid ONCE for both towers.** **That is INFERRED and this same run
tests it.** **Say whether it held.**

## ARCHIVE (DD18)

- **`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:35`, `:37`, `:70-88` and
  `ProbeLJ152A.agda:58-73`**, read WHOLE. **These are your starting files and
  they are the reason this task exists.**
- **`agents/tasks/LJ-1-246/lj-1.246-report.md`**, read WHOLE. **It is your
  specification.**
- `agents/tasks/LJ-1-244/lj-1.244-report.md` and `ProbeLJ1244B.agda`: the
  refutable telescope, so you do not repeat it.
- **`agents/tasks/LJ-1-238/GenSequence.agda:14-24`**: the `(M, M-trans)`
  abstraction you re-point to.
- `src/L/Condensation.lagda.md:5433-5434`: the comment that names the gap.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`[LJ-1.246]` measured that the second coding IS load-bearing, for a
COMPLEXITY reason nobody had named: the Sequence coding carries ZERO Δ₀
certificates while `crossOut` spends `Σ₁ Cr.φP`.** **Say whether your port
touches that gap or leaves it whole.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-246/lj-1.246-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-249/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above, step zero first.
- **D-10.** **Price the truth of a target before pricing its proof.
  `[LJ-1.244]` priced a false one.**
- **P-l.** 1.95 s is a comparable and NOT your price.
- **C-36.** Write the term you could not write.
- **C-44.** A brief's claim is unchecked until you check it.
- **C-45.** Audit the instantiation, never the telescope.
- **C-38, C-42, C-39, C-40. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12,
  C-22. DD0, DD8, DD18, DD24, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with step zero's exit code, THEN whether `graph-assembly` ports.** Then
its written lines and the seconds with load and run count. Then any new
hypothesis, named. Then whether the assembly is paid once for both towers.
**Mark every negative MEASURED or INFERRED.**
