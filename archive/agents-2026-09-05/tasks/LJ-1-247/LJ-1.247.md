# LJ-1.247: re-derive A5 after the dissolution, and measure its last inferred row

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.176]` priced A5 at 547 lines with exactly TWO rows INFERRED. One of
them has since DISSOLVED and the other is still unmeasured.**

| row | object | `[LJ-1.176]` | today |
|---|---|---:|---|
| 4 | the column square `pair` | **99, INFERRED** (`lj-1.176-report.md:205`) | **still INFERRED. Yours.** |
| 5 | `pairω` | **160, INFERRED** (`:206`) | **DISSOLVED to 60 MEASURED lines** (`[LJ-1.234]`) |

**Two deliverables:**

1. **Measure row 4, the column square.** It is A5's last inferred row.
2. **Re-derive A5's total** with row 5 at its measured 60 and row 4 at whatever
   you measure.

**This is entirely independent of `[LJ-1.7]`'s `amb` question**, which is
blocked on a chapter and under review at `[LJ-1.246]`. **Do not touch it.**

## WHY ROW 4 MAY ALSO BE LOW, and the warning is `[LJ-1.176]`'s own

**`lj-1.176-report.md:265-269`, in its own words:「Row 4 may be too low as
well. The column square runs over a PRODUCT of small types, `⟪α⟫ × ⟪α⟫`, and
`[LJ-1.152]`'s 99-line second-site figure was measured for a composite of two
graphs between plain sets. The product action `(x , y) ↦ (α↪κ x , α↪κ y)` may
need its own object. INFERRED, not measured, in either direction.」**

**So the 99 was transferred from a DIFFERENT site, and P-l says that is a
comparable and not a price.** **`[LJ-1.226]` measured what happens when such a
transfer is checked: row 5's 160 turned out to be row 1's number moved to
another object** (`lj-1.176-report.md:227-229`).

## ASK THE DISSOLUTION QUESTION FIRST

**`[LJ-1.234]` dissolved row 5 by asking what the CONSUMER actually demands,
and the answer was「an injection」rather than an object-language arithmetic.**
**This project has dissolved FOUR items this month and each beat the
measurement it replaced.**

**So ask it for row 4: does anything actually demand the column square as its
own object, or does the delivered order route give it the way it gave the base
at `ω`?** **`[LJ-1.234]`'s green file is
`agents/tasks/LJ-1-234/ProbeLJ1234A.agda` and `via-col-square` is at
`src/L/Ordinal/SquareLaw.lagda.md:960-961`.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **ROW 4 DISSOLVES.** Say so with the evidence. **Then A5 is 547 minus 99
  minus 160 plus 60, and every row is measured.** STOP. **This is the best
  outcome and it has happened four times this month.**
- **ROW 4 BUILDS.** Report its written lines against the inferred 99, and the
  seconds. **Then A5's total is fully measured for the first time.**
- **ROW 4 IS MATERIALLY OVER 99.** Report both figures. **`[LJ-1.176]`
  predicted this and a confirmed overrun re-prices A5.**
- **THE PRODUCT ACTION NEEDS ITS OWN OBJECT.** **`[LJ-1.176]` named that risk
  exactly. If it is real, NAME the object and price it separately** (C-36).
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law).

## WHAT YOU MUST NOT DO

- **Do not re-price rows 1, 2, 3 or 5.** Row 5 is measured at 60 and the rest
  are `[LJ-1.176]`'s.
- **Do not quote a total for Route A-prime.** Six reports refuse one. **A5's
  own total is what you give.**
- **Do not touch `[LJ-1.7]`'s `amb` question.** Blocked and under review.
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-246/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-247/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one in this very area and it was R-34's unpinned `InfinitySet` level
  meta, cured by `module IS = InfinitySet {ℓ}`.**
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## FOUR RULES THIS AREA EARNED THIS WEEK

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.** Two reports called it surveyed and
not bearing; both were wrong, and the retired route held the object they
needed.

**`exit 0` IS NOT A SUPPLY** (C-45). **Audit the instantiation, never the
telescope.**

**C-44: if THIS brief states anything you cannot find, say so and treat it as
unproven.** **In particular I have not re-derived the 99 myself.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.** **This task exists to convert A5's
LAST inferred number. Do not hand back another.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.243]` measured that `[LJ-1.227]`'s tower table does NOT cover A5, so
A5's tower status is OPEN and not settled.** **Do not assume either way.**

**A column square over `⟪α⟫ × ⟪α⟫` names no tower in its statement.** **If what
you build or dissolve is tower-neutral, say so with evidence, because the J
tower then pays it once.** **`[LJ-1.234]` found the same for the base at `ω`.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-176/lj-1.176-report.md`**, read WHOLE. **Rows 4 and 5,
  the two warnings at `:252` and `:265-269`, and `:227-229` where the 160 is
  recorded as a transferred number.**
- **`agents/tasks/LJ-1-234/lj-1.234-report.md` and `ProbeLJ1234A.agda`**, read
  WHOLE. **The dissolution and how it was found. It is your template.**
- `agents/tasks/LJ-1-152/lj-1.152-report.md`: the 99-line second-site figure
  the 99 was transferred FROM. **Read what it measured.**
- `agents/tasks/LJ-1-156/` and `ProbeLJ1156A.agda:493-494`, `:496-497`: the
  column square as the earlier probes wrote it.
- **`src/L/Ordinal/SquareLaw.lagda.md:960-961` and `:685-687`: the delivered
  order route and the consumer's actual obligation. Read the source.**
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route closed the base at `ω` with ZERO arithmetic in about 79
  lines and `[LJ-1.234]` used its shape. Say whether it also holds a column
  square.** Take SHAPE from the archive, never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/rudimentary-functions.md:68` is the basis `[LJ-1.176]`
inferred A5's objects from.** **Say whether it requires a column square as its
own object or only the injection.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-176/lj-1.176-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-247/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **D-10.** **Price the truth of a recorded residue before pricing its proof.
  Row 4 may not need to exist.**
- **P-l.** **The 99 was measured at ANOTHER site. It is a comparable and NOT
  row 4's price. This task is P-l's test case.**
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

**Lead with whether row 4 DISSOLVES or BUILDS, and with its number against the
inferred 99.** Then A5's re-derived total with every row's class. Then whether
the product action needed its own object. Then the seconds with load and run
count. Then A5's tower status with evidence. **Mark every negative MEASURED or
INFERRED.**
