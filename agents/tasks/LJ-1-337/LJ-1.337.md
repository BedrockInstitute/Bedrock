# LJ-1.337: the successor-or-limit dichotomy, and `sq-below`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## WHAT `[LJ-1.335]` MEASURED, and it corrected a premise of mine

**My brief assumed three untruncated bands could be supplied. `[LJ-1.335]`
measured the count differently:**

> **Only TWO of the three are SUPPLIERS. The successor band is a STEP.**
> `sq-suc` reads `sq γ` and returns `sq (sucV γ)`, so a general predecessor `γ`
> is a non-initial limit, whose only supplier is truncated.

**So the tally is: two suppliers, both ALREADY delivered, one step, one
truncation.** **Landing the delivered ones changes nothing.**

**And the consumer needs NOTHING re-plumbed. The diff is EMPTY, MEASURED.** The
narrowing is bought by a NEW lemma outside both chapters:

```agda
sq-below : (α : S) → IsOrd α → LimitBand → SqBelow α
```

**so the caller supplies ONE band and not a family.** **Estimate 120 code
lines**, basis the delivered comparable `Upper` at
`src/L/StageCardinal.lagda.md:498-566`, 59 non-blank non-comment lines measured,
plus the two probes' 25 and 32.

## THE GAP THIS TASK CLOSES

**`[LJ-1.335]` named the one piece `src/` does not have:**

> **A successor-or-limit dichotomy on ordinals. MEASURED ABSENT by three
> literal searches, all hits a different subject.** **`isProp (Init δ)` and
> `sucV` injectivity are absent too.**

**Its lines are NOT in the 120**, because no comparable exists and P-l forbids
the transfer. **So this task prices the thing that has no price.**

## THE TASK

**Build the dichotomy, then `sq-below` on top of it.**

**1. THE DICHOTOMY.** For an ordinal δ: is it a successor, a limit, or zero?
**Search first** (D-10): three of my briefs this week called absent what the
repository held, and `[LJ-1.328]` found a whole uniform family a predecessor had
called missing. **`[LJ-1.335]`'s three searches were literal string searches;
run a semantic one.**

**2. `isProp (Init δ)` AND `sucV` INJECTIVITY**, if the dichotomy needs them.
**Both are named absent. Verify, then build only what you use.**

**3. `sq-below`.** **Only if 1 and 2 land cheaply.** **If the dichotomy alone
costs more than its estimate, STOP and report: a priced dichotomy is the
deliverable and `sq-below` is the next task.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE DICHOTOMY IS DELIVERED SOMEWHERE.** **Say where and this task shrinks to
  `sq-below`.** **That is the cheapest outcome and D-10 says look for it first.**
- **IT BUILDS.** Report its lines and seconds. Then attempt `sq-below`.
- **IT NEEDS CLASSICAL LOGIC.** **LEM is already a module parameter in this
  tree**, so say precisely what it needs and whether the site carries it.
- **IT IS EXPENSIVE.** Price it against a named delivered comparable and STOP.
- **A WALL.** 30 minutes on one invocation is a wall: interrupt, report the
  ELAPSED SECONDS, bisect. **NEVER raise the cap.** **C-56: a truncated proof
  that walls is paying for its ASSEMBLY. Write the untruncated control first.**

## THE HOMES `[LJ-1.335]` ALREADY SETTLED, so you do not re-derive them

**Do not re-open placement.** It measured, with `ledger.py`'s own graph code:

- transports and the limit kit go in `src/L/Ordinal/SquareLaw.lagda.md`,
  **ZERO new imports**;
- `sq-suc` and the assembly need a **NEW master**, because SquareLaw and
  `L.InjChain` both cycle;
- **a band-split PARAMETER touches TWO delivered signatures and costs 22 masters
  and 6,464 lines.** **It is refused in favour of the lemma. Do not propose it
  again.**

**One rewrite it flagged and you must honour:** the probes use `_↪_` from
`L.Cardinal`, and `L.Cardinal` imports SquareLaw, **so state your terms with the
raw Σ shape at `src/L/Ordinal/SquareLaw.lagda.md:686-687`.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-337/`. **`src/` is forbidden** (I-5).
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-330/`, `LJ-1-332/` and `LJ-1-335/`.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every figure.
- **RUN A NEGATIVE CONTROL that MEASURES.** Siblings on this leg have produced
  more than twenty and several put a whole verdict into one error message.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-337/lj-1.337-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Seven of my last nine briefs carried a claim an agent measured FALSE.** **The
one at risk here: 「the dichotomy is absent」.** **It is `[LJ-1.335]`'s
measurement from LITERAL searches only.** **A semantic search is cheap and D-10
demands it.**

## THE RULES

**D-10, P-l, C-44, C-36, C-42, C-45, C-56, P-k, C-40.**
**C-12, C-22, C-32, C-38, C-39, C-49, C-50, C-51.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**A successor-or-limit dichotomy on ordinals is pure ordinal arithmetic and
names no tower.** **So it should be written once and inherited by both ends.**
**Say where it belongs so that is true**, and note `[LJ-1.335]` measured that
`SquareLaw` is in the GCH closure and NOT the AC one, so a home there is
GCH-only today.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-335/lj-1.335-report.md`, read WHOLE.** It funds you, it
  settled the homes, and its section 4.1 is `sq-below`.
- **`agents/tasks/LJ-1-330/lj-1.330-report.md`** and
  **`agents/tasks/LJ-1-332/lj-1.332-report.md`**, the two built bands.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had ordinal arithmetic too.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**A successor-or-limit dichotomy is textbook ordinal arithmetic and every source
uses it without comment.** **The interesting question is CONSTRUCTIVE: say in
one line whether it needs excluded middle in this setting**, and check
`dev/literature/truncation-and-selection.md` for whether the digest bears.
Return a **LITERATURE USED** section.

## SCOPE (read)

`src/L/Ordinal/SquareLaw.lagda.md:686-700` FIRST, the raw Σ shape and `Init`.

## SCOPE (write)

`agents/tasks/LJ-1-337/` only.

## RETURN

**Lead with ONE word: DELIVERED, BUILDS, EXPENSIVE or BLOCKED.** Then whether a
semantic search finds the dichotomy already in the tree. Then the term or the
price with its named comparable. Then `isProp (Init δ)` and `sucV` injectivity,
each VERIFIED absent or found. Then `sq-below` if you reached it. Then your
negative control. **Mark every negative MEASURED or INFERRED.**
