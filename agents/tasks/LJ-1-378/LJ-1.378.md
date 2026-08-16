# LJ-1.378: probe the composite's TERM, the largest unwritten thing in the proof

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **PROBE. Land nothing.**

## WHAT FUNDS THIS

**The owner asked on 2026-08-16 what in the proof itself is still unwritten,
apart from thresholds and wiring.** **`dev/PLAN.md` section 0.0 answers with
three items, and THIS IS ITEM 1, the largest:**

> **The composite's TERM has never been written.** `[LJ-1.302]` proved that a
> HYPOTHETICAL `comp : Composite` makes `amb` come out. **That says it FEEDS
> and not that it EXISTS.** The 470 lines price the ingredients; the composite
> itself is unwritten.

**So `[LJ-1.7]`'s 470-line price is a price for PARTS, and the thing that
assembles them has never been attempted.** **`[LJ-1.8]` sits downstream of
it.**

**`amb-from-composite` typechecks** (`[LJ-1.302]`), which is exactly the shape
`[LJ-1.365]` was later caught by: **a green consumer proves the interface is
usable and says nothing about whether the supplier exists.** **That is C-45's
own lesson and it is the reason this probe is funded.**

## THE QUESTION

**1. WHAT IS `Composite`, as a type?** Read `[LJ-1.302]`'s work and state it.
**Re-derive every citation** (C-44); this chain's line numbers have drifted
before.

**2. WHAT WOULD ITS TERM HAVE TO SUPPLY, part by part?** **The 470 lines name
four parts, each at a BUILT site:** the clean 23 `Agree` modules (~180,
`[LJ-1.298]`), the dirty seven's ambient ties (327, MEASURED, `[LJ-1.338]`),
`StepAgree` with `ApproxAgree` (~190, `[LJ-1.304]`, both BUILT as terms), and
the composite's type (`[LJ-1.302]`). **Say which parts the term consumes and
which it must produce.**

**3. IS THERE A WALL, AND WHERE?** **Build the smallest miniature that either
produces a `Composite` at ONE instance, or fails and names the goal.** **You
do not need the whole thing. You need to know whether the assembly is
mechanical or whether it hides mathematics.**

**That third question is the deliverable. Everything else is context for it.**

## THE ABORT CRITERION (D-1)

- **THE ASSEMBLY IS MECHANICAL.** **Then the 470 stands and the composite is
  a writing job with a price.** Report the miniature and the price. **Best.**
- **IT HIDES MATHEMATICS.** **Name the goal that is not mechanical, at
  `file:line`, with Agda's own type.** **That would mean the 470 is a floor
  and section 0.0 understates the remaining work; the owner should hear it
  today rather than after a 470-line build.**
- **THE PARTS DO NOT FIT.** **If a part the 470 prices does not actually
  compose with the others, say which pair and why.** **`[LJ-1.338]` measured
  that 51 of its 327 lines STATE a residue nothing proves; check whether that
  residue is what the composite needs.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** **C-56: when a truncated
  proof walls, the cost is in the ASSEMBLY, and this task IS an assembly.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-378/`.
- **You may READ and COPY from `LJ-1-298/`, `LJ-1-302/`, `LJ-1-304/` and
  `LJ-1-338/`. Edit none of them.**
- **`[LJ-1.377]` and `[LJ-1.379]` are live.** `[LJ-1.379]` holds one Agda
  slot. **COUNT THE SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** Cap TWO. **If it reads 2, WAIT.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53).
- **RUN A NEGATIVE CONTROL that MEASURES.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-378/lj-1.378-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

- **The composite's term has never been written**, at `dev/PLAN.md:104`.
- **`[LJ-1.302]` proved it FEEDS, not that it EXISTS**, at
  `agents/tasks/LJ-1-302/lj-1.302-report.md:1`.
- **The four parts are each at a BUILT site**, at `dev/PLAN.md:57-63`.
- **51 of `[LJ-1.338]`'s 327 lines state a residue nothing proves**, at
  `dev/PLAN.md:63`.

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last forty briefs carried a claim an agent measured FALSE, and
`[LJ-1.376]` measured today that my costliest failure mode is not reading the
project's own live record.** **The one at risk: 「the four parts are each at a
BUILT site」.** **I took that from section 0.0, which I rewrote hours ago and
which had been stale on two of its four items for a day.** **Check each of the
four yourself before you rely on any of them.**

## THE RULES

**C-45 is this task's law: `exit 0` is not a supply, and a green CONSUMER is
not a supplier.** **C-56: an assembly's cost is in the assembly.** **C-44,
C-57, D-10, C-42, C-53, C-55, C-58, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24, DD25, DD28.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** **NAME YOUR
AXIS** (C-46), fixed at `scripts/measure/ledger.py:50`. **`[LJ-1.113]` split
the per-tower share at about 28 lines, about 7 percent, before this chain
began; say whether your miniature honours that split or breaks it.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route build a
  composite of this shape?** **It ran a different route, so「nothing
  transfers」is a fine answer that must be MEASURED.**
- **`archive/dev/TASKS-archived.md`**: **grep for the retired route's
  assembly dispatches**, taking SHAPE and never a claim.
- **`archive/dev/JOURNAL-archived.md`**: why the retired assembly was shaped
  as it was. **WHY NOT in one line if nothing bears.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on composite structure.
  **WHY NOT in one line if none.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` and `dev/literature/j-hierarchy.md`.** **Say
in ONE line whether the orthodox development assembles anything of this shape,
or whether the composite is an artefact of this formalization.** **That
distinction decides whether the literature can help at all.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-302/` whole, FIRST: it holds `amb-from-composite` and the
composite's type, and it is the only place the object has ever been written
down.

## SCOPE (write)

`agents/tasks/LJ-1-378/` only.

## RETURN

**Lead with ONE word: MECHANICAL, HIDES-MATHEMATICS, or PARTS-DO-NOT-FIT.**
Then `Composite` as a type. Then which parts the term consumes and which it
produces. Then your miniature, with its exit code. Then what the 470 becomes.
Then your negative control. **Mark every negative MEASURED or INFERRED.**
