# LJ-1.202: is `ω ∈ lam` DERIVABLE at the sole instantiation site?

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda, so it takes pro and holds an Agda slot.

## GOAL

**`[LJ-1.199]` stopped step 6 at ZERO lines on a join, and it found the join by
READING with no Agda run at all. Its finding is verified and its evidence is
exact.**

**The join:** `envSetNumeral∈` takes `⟨ ω ∈ σ ⟩` as a hypothesis
(`src/L/Coding/Key.lagda.md:476`). At the concrete bound the supply needs
`ω ∈ lam`. **`HullStage`'s telescope is `lam, ordλ, succλ, X, X⊆L, ∅∈λ`**
(`src/L/BoundedSubset.lagda.md:903-905`) **and `ω ∈ lam` is not in it.**

**`[LJ-1.199]` also proved successor-closure plus `∅∈λ` does NOT give it**, by
citing that the codebase carries `⟨ ω ∈ˢ α ⟩` and successor-closure as SEPARATE
conjuncts of `Init` (`src/L/Ordinal/SquareLaw.lagda.md:693-697`). **I verified
all three citations myself.**

**THIS TASK ASKS THE ONE QUESTION `[LJ-1.199]` DID NOT: is `ω ∈ lam` derivable
at the site that instantiates `HullStage`?**

## THE LEAD, and it is INFERRED and mine, not a measurement

**`HullStage` has exactly ONE instantiator**, `src/L/BoundedSubset.lagda.md:1405`.
**Read its context at `:1380-1405`.** In scope there are, among others:

- **`α∉ω`**: `α` is not a member of `ω`.
- **`α∈λ`**: `α ∈ lam`.
- **`ordα`** and **`ordλ`**.

**My reasoning, INFERRED and untypechecked:** an ordinal not in `ω` satisfies
`ω ⊆ α`, so `ω ∈ α` or `ω ≡ α`. In the first case `lam` is an ordinal and so
transitive, and `α ∈ lam` carries `ω ∈ lam`. In the second, `α ∈ lam` IS
`ω ∈ lam`.

**Test it. I may be exactly wrong, and `[LJ-1.199]` did not consider it at all.**

## THE OUTCOME THAT COSTS NOTHING, and try for it first

**If `ω ∈ lam` is derivable at the instantiation site, it does not need to be a
`HullStage` PARAMETER at all.** The consumer derives it where it is needed.

**That is the cheapest possible answer**: no new hypothesis, no new debt for any
future instantiator, and the join dissolves.

**Try that shape before you try adding a parameter.**

## THE STANDING PROHIBITION, and why it is suspended for this ONE hypothesis

**I have told four dispatches: no fourth `HullStage` hypothesis.** That
prohibition exists to stop hypothesis creep, because every added hypothesis is a
debt every instantiator must discharge.

**It is suspended here IF AND ONLY IF you measure that the hypothesis is
SUPPLIABLE at the sole instantiation site** (C-38: a hypothesis is discharged
when something SUPPLIES it). **A hypothesis that the only instantiator can
already prove is not creep.**

**If it is NOT suppliable, the prohibition stands and the join is real.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **DERIVABLE, NO PARAMETER.** The consumer derives `ω ∈ lam` in place. Report
  the lines and where it goes. **STOP. This unblocks step 6 and is the best
  outcome.**
- **DERIVABLE, PARAMETER CHEAPER.** If deriving in place is dear but the
  instantiator can supply it in a line or two, say so and price both shapes.
- **NOT DERIVABLE.** `[LJ-1.199]`'s join is real and step 6 is blocked on a
  genuinely missing fact. **Name what would supply it and stop.** That is a
  complete answer and it re-prices the satisfaction layer.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt it, report the elapsed seconds, and bisect. A sibling ran ONE
  typecheck for 3.06 hours on 2026-08-14 because its brief gave a heap cap and
  no clock cap.

## KEEP IT SMALL

**`[LJ-1.199]` answered its question by READING and made no Agda run at all.**
That is the standard here too: **do not build a 684-line probe to answer a
three-line question.** If a miniature grows past what typechecks in minutes,
that growth is itself the finding.

## WHAT YOU MUST NOT DO

- **Do not edit any master** until you have reported. This is a probe first.
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not undo the 21 cured fields.** They are green and committed.
- **A probe goes in `agents/tasks/LJ-1-202/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  holds the other slot. **Report the load beside every absolute figure.**
- **A SIBLING'S FILE MAY BE RED. BUILD GENERIC FIRST.**
- **Create your report file in your FIRST five minutes and fill it as answers
  land (C-22).** A sibling died on 2026-08-14 having written nothing.
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **My lead above is INFERRED and you
are the measurement.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**If `ω ∈ lam` becomes a derivation, write it where BOTH towers can use it**, not
inside a consumer that names the L tower. `[LJ-1.184]` measured that SIX extra
lines bought the second tower for a 167-line module.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-199/lj-1.199-report.md`**, read WHOLE. **The join, its
  three citations, and the nine-lemma table it stopped before.**
- `src/L/BoundedSubset.lagda.md:1380-1405`: **the sole instantiation site, which
  is the whole subject of this task.**
- `src/L/Coding/Key.lagda.md:476`, `src/L/Ordinal/SquareLaw.lagda.md:693-697`.
- `agents/tasks/LJ-1-172/` and `LJ-1-173/`: the refutation that made this layer
  need a numeral bound, and the 21-field cure.
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.** The retired route also bounded stages; say what would NOT transfer.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md`, `devlin-errata.md`. **Say whether Devlin's limit
stages carry `ω` as a member by construction or by hypothesis.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-199/lj-1.199-report.md` FIRST, then the instantiation site.

## SCOPE (write)

`agents/tasks/LJ-1-202/` for probes. **A master edit lands only after you
report.**

## MANDATORY RULES

Run `python3 scripts/rules.py --for probe` and `--for build`.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
  **This task is C-38's test case by construction.**
- **C-36.** Write the term you could not write.
- **C-42.** A refutation measures the site it names, never its extent.
- **P-k, P-l, P-m, C-12, C-22, C-39, C-40. DD0, DD8, DD24, D-1, D-10, D-26,
  D-29, D-30. I-5.**

## CONSTRAINTS

- Count with `python3 scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with DERIVABLE or NOT DERIVABLE, in one word, and with whether step 6 is
unblocked.** Then the derivation or the obstruction, at `file:line`. Then which
shape you took and why. Then the lines and seconds. **Mark every negative
MEASURED or INFERRED, and mark my lead CONFIRMED or REFUTED.**
