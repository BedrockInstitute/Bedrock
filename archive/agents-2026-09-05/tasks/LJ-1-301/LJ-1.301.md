# LJ-1.301: build `sq` by descent from `squareω`

tier: pi (pi-subagent-mode), **model `glm-5.3`**. I ran
`scripts/dispatch/dispatch_policy.py` and took the head it gave. **`scripts/`
was reorganised today**: `rules.py` is `scripts/dispatch/rules.py`, the linters
are `scripts/gate/`, `ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**`[LJ-1.8]` is half of LJ-1's terminus and its route was thought circular
until two hours ago. `[LJ-1.300]` measured that WRONG. Build the descent.**

## PREMISES

- **The circle is NOT real, MEASURED by `[LJ-1.300]`.** `Init`'s fourth row at
  `src/L/Ordinal/SquareLaw.lagda.md:696-698` quantifies over `β ∈ˢ α`,
  **strictly below α**. Its probe `StepProbe.agda:45-63` builds `sq α` from the
  square law at MEMBERS only, plus ambient initiality, and **nothing in that
  term mentions `sq α`**. VERIFY.
- **The base exists and bypasses `Init` entirely.** `squareω : sq ω` at
  `src/L/InjChain.lagda.md:184-185`, with `noinj²ω` VACUOUS at `:123-126`.
  VERIFY.
- **`SqShape` now states the real square law.** I fixed a parenthesis defect at
  `src/L/GCH.lagda.md:47` two hours ago, and `[LJ-1.300]` proved by `refl` that
  the fixed body IS `L.Ordinal.SquareLaw.sq`. **Read the CURRENT file, not any
  report written before that fix** (C-32).
- **`κ-limit` is PROVED**, `[LJ-1.294]`, so `Init`'s row 3 is available at the
  use site. Rows 1 and 2 also stand. **Row 4 is what the descent must produce.**

## WHAT TO BUILD

**A recursion that carries `sq` up from `squareω`.** At each step, `Init α`'s
fourth row needs the square law at every infinite `β ∈ˢ α`, which the induction
hypothesis supplies.

**Name the recursion principle you use and say why it is well-founded.** The
tree has `WF.WFI.induction regularityV`, used at
`src/L/Ordinal/Linear.lagda.md:137`. **That may be the right one; check.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE DESCENT BUILDS.** Report the term, its lines, and its cold seconds.
  **Then `[LJ-1.8]`'s route is open for the first time.** STOP.
- **THE INDUCTION HYPOTHESIS IS THE WRONG SHAPE.** `Init` needs the square law
  at infinite members; the induction gives it at ALL smaller ordinals. **Say
  whether the finite ones are a gap or are discharged by `noinj²ω`'s vacuity.**
- **AMBIENT INITIALITY IS NOT AVAILABLE AT THE USE SITE.** `StepProbe` used it.
  **If `GCHStatement`'s hypotheses do not give it, name what is missing** and
  stop. That would re-open the cardinal-face question, which is the OWNER's and
  not yours.
- **IT IS CIRCULAR AFTER ALL.** Then `[LJ-1.300]` is wrong and `[LJ-1.299]` was
  right. **Name the link at `file:line`.** A reversal here is worth more than a
  term.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## CONSTRAINTS

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-301/`.
  **`src/` is forbidden for probes** (I-5).
- **Do not edit any master.** **`src/L/GCH.lagda.md` especially: its statement
  is the trophy and the OWNER rules on it.**
- **A SIBLING IS LIVE** in `agents/tasks/LJ-1-302/`. Do not touch it.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-301/lj-1.301-report.md` in your FIRST five
  minutes** (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `scripts/gate/lint-agda.py --check`. **No em dash in any language.** DD23
  freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**C-32. A cure invalidates every downstream measurement.** **The parenthesis
fix landed two hours ago and it VOIDED `[LJ-1.286]`'s central conclusion.** Read
current source, not reports written before it.

**D-10. Price the truth of a recorded residue before pricing its proof.**
**`[LJ-1.299]` recorded CIRCULAR and `[LJ-1.300]` measured that false.** A
record one dispatch old was wrong; check this brief the same way.

**C-36. A failed substitution is not a proof of impossibility.**

**C-44.** Every claim here is `[LJ-1.300]`'s or mine.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **A descent over ordinals names no tower**, so
say where it belongs under P-k and **NAME YOUR AXIS** (C-46): DD4's own axis is
AC-against-GCH, and `src/L/Ordinal/SquareLaw.lagda.md` is already in the GCH
closure via `src/L/Cardinal.lagda.md:22`.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-300/lj-1.300-report.md` read WHOLE, and its `StepProbe.agda`.
`agents/tasks/LJ-1-299/lj-1.299-report.md`, the CIRCULAR verdict that was
overturned. `agents/tasks/LJ-1-294/` for `κ-limit`. `agents/tasks/LJ-1-279/`
for `squareω` and why row 5 rebuilt the base at ω.
`archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

**`[LJ-1.300]` MEASURED that Devlin II.5 never states a square law at all.**
**So say where the descent's shape comes from, if not the literature**, and
whether that matters. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-300/lj-1.300-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-301/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **OPEN the full entry for any law you act on.**

- **D-1, D-10, C-32, C-36, C-44, C-45.**
- **P-h, P-i, P-k, P-l, P-m, P-t, R-34, R-40, R-41. C-12, C-22, C-38, C-39,
  C-40, C-42, C-49, C-50. I-5. DD0, DD8, DD18, DD24, D-26.**

## RETURN

**Lead with ONE word: BUILDS, BLOCKED or CIRCULAR.** Then the term and the
recursion principle, or the obstruction at `file:line`. Then each premise
VERIFIED or REFUTED. Then whether `Init κ` is constructible at the use site now.
Then the DD4 answer with its axis. **Mark every negative MEASURED or INFERRED.**
