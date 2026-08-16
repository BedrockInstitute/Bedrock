# LJ-1.381: price the `φ₀` EXTRACTION, the larger of the two UNPRICED rows

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **PROBE. Land nothing.**

## WHY, and it is DD8 in its exact form

**`[LJ-1.378]` returned MECHANICAL today: the composite's assembly hides no
mathematics, and a `Composite` term is BUILT at one instance**
(`ProbeLJ1378A.agda`, exit 0). **So `[LJ-1.7]`'s composite stopped being an
unknown and became a writing job.**

**Its table of what the 470 becomes leaves exactly TWO rows UNPRICED**, and
this is the larger one:

| row | state |
|---|---|
| the extraction | **UNPRICED. Legs delivered or finite, FACTOR UNWRITTEN** |
| the residue's proofs | UNPRICED, and two ties may be false as stated |

**DD8: a build brief names its widest unmeasured term. This IS that term, and
the composite cannot be funded until it has a number.**

## WHAT `[LJ-1.378]` ALREADY MEASURED ABOUT IT

**It called this WALL TWO and it enumerated the legs.** The named hypothesis
`Extraction` (`agents/tasks/LJ-1-378/ProbeLJ1378A.agda`, `Comp` module)
**states the `φ₀`-side obligation exactly**: the fourteen witnesses, the level
row, and the carrier-level slot equations.

**Its legs, with `[LJ-1.378]`'s own status for each:**

| leg | status |
|---|---|
| a fourteen-fold `∃̇` unfold | mechanical |
| a conjunct projection | mechanical |
| the rename-back along `ρ` | **delivered** `⊨-rename`, and it needs the SAME leaf-naturality |
| the un-erase along `Cnt.erase-inv` | **delivered** |
| an `embed`-`renameFo` commutation | **unwritten mechanical induction, about 12 lines** |
| `[LJ-1.241]`'s slot-map towers | finite arithmetic, tedious |

> **Nobody has priced this factor.**

**Re-derive every one of these** (C-44). **`[LJ-1.378]` is two hours old and
its own brief warned that section 0.0, which I had rewritten hours before, had
been stale on two of four items for a day.**

## THE QUESTION

**1. WHAT DOES `Extraction` DEMAND, as a type?** State it. **`[LJ-1.378]`
says it states the obligation EXACTLY, which means the type is the
specification and you do not have to invent one.**

**2. PRICE THE FACTOR.** **Six legs, four of them called mechanical or
delivered and two called tedious or unwritten.** **A price is lines, and「the
legs are mechanical」is not a price.** **Build enough to know: at minimum the
`embed`-`renameFo` commutation, which is the one leg called unwritten and
carries its own about-12 estimate.**

**3. IS ANY LEG NOT WHAT IT IS CALLED?** **The two at risk are the ones with
adjectives instead of terms: 「finite arithmetic, tedious」and 「mechanical
induction」.** **`[LJ-1.378]` itself found that `[LJ-1.302]`'s green consumer
said nothing about its supplier; the same trap is available here, one level
down.**

## THE ABORT CRITERION (D-1)

- **IT PRICES.** **Give the number and its basis, leg by leg.** **Then the
  composite has ONE unpriced row left and `[LJ-1.7]` can be funded against a
  band rather than a floor.** **Best.**
- **A LEG IS NOT MECHANICAL.** **Name it with Agda's own type.** **That is
  more valuable than the price, because it would move work from the writing
  column back to the mathematics column.**
- **THE SLOT-MAP TOWERS ARE THE COST.** **`[LJ-1.241]` is cited as「finite
  arithmetic, tedious」. If the tedium dominates the number, say so: tedious
  and large is a different funding decision from tedious and small.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** **A fourteen-fold unfold is
  exactly the shape C-58 was written from.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-381/`.
- **You may READ and COPY from `LJ-1-241/`, `LJ-1-302/`, `LJ-1-304/` and
  `LJ-1-378/`. Edit none of them.**
- **`[LJ-1.380]` is live, holds one Agda slot, and is TIMING
  `src/L/Condensation.lagda.md` cold at about 150 s per run.** **A timing task
  gets a quiet machine: do NOT start an Agda run while it is timing.** **Count
  the slots before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`.** **Both obvious
  alternatives OVER-COUNT, MEASURED.** **Cap TWO, and if it reads 1 you may
  take the second, but say in your report what it read each time.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53).
- **RUN A NEGATIVE CONTROL that MEASURES.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-381/lj-1.381-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

- **The extraction is UNPRICED and its factor unwritten**, at
  `agents/tasks/LJ-1-378/lj-1.378-report.md:162`.
- **`Extraction` states the obligation exactly**, at
  `agents/tasks/LJ-1-378/ProbeLJ1378A.agda`, `Comp` module.
- **Four of six legs are delivered or mechanical**, at
  `agents/tasks/LJ-1-378/lj-1.378-report.md:28-37`.
- **The composite's assembly is MECHANICAL**, at
  `agents/tasks/LJ-1-378/ProbeLJ1378A.agda`, exit 0.

**Mark each VERIFIED or REFUTED at `file:line`.**

## LIVE RECORD

> **ADDED 2026-08-16 AFTER DISPATCH, AND THE AGENT DID NOT SEE THIS SECTION.**
> `scripts/gate/check-live-record-claims.py` refused this brief, correctly.
> That gate was built HOURS EARLIER, by `[LJ-1.377]`, against the defect
> `[LJ-1.376]` measured as this project's costliest: **the orchestrator's own
> live record unread.** **It caught the orchestrator in the first briefs
> written after it landed, and its duty list named item 7, which the
> orchestrator did not know was there and which turned out to be STALE.** The
> section is added so the record is complete; it does not pretend the agent
> read it.

- **blocked:LJ-1.7** (`dev/PLAN.md:47`): BLOCKED at about 400 lines, `[LJ-1.251]` UPHELD.
- **open work item 0** (`:53`, both halves have a route): BEARS as context. `[LJ-1.7]`'s open parameter is `amb`; `[LJ-1.8]`'s is `sq`.
- **open work item 1** (`:179`, step 6 landed and under the bar): DOES NOT BEAR. `EnvSupply`'s seconds, a different master.
- **open work item 2** (`:244`, the satisfaction layer's supply chain): DOES NOT BEAR on this task's object.
- **open work item 3** (`:265`, A2 landed and under the bar): DOES NOT BEAR.
- **open work item 4** (`:296`, option C's target shrank by 8x): DOES NOT BEAR.
- **open work item 5** (`:311`, the named-slot refactor waiting on a condition): DOES NOT BEAR.
- **open work item 6** (`:347`, DD4's own report ran for the first time): DOES NOT BEAR.
- **open work item 7** (`:410`, `[LJ-1.8]`'s blocker changed): **BEARS, AND IT IS STALE.** It reads 「ONE remains: `sq : SqShape` at `src/L/GCH.lagda.md:80`」. **`[LJ-1.384]` measured `SqShape` in ZERO files under `src/`, and `[LJ-1.323]` deleted that hypothesis from the trophy at commit `ffb0811`.** The blocker survives as a PROOF debt, not a statement hypothesis. **Corrected at `:72` and `:116` on 2026-08-16; `:410` still carries the old letter and is flagged here rather than rewritten, because a dated screen is a record.**
- **screen:47**: `[LJ-1.7]`'s row. BEARS: this task prices one row under its 400.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last forty-two briefs carried a claim an agent measured FALSE.**
**The one at risk: 「four of six legs are delivered or mechanical」.** **Every
word of that table is `[LJ-1.378]`'s, taken two hours ago, and three of its
six cells carry an ADJECTIVE where a term should be.** **An adjective is not a
measurement, and this project measured today that a verdict line can overstate
its own body** (`[LJ-1.375]` on `[LJ-1.373]`). **Check the four before you
lean on any of them.**

## THE RULES

**DD8: this task exists to turn a floor into a price.** **C-45: `exit 0` is
not a supply, and a green consumer is not a supplier, which is the trap
`[LJ-1.378]` escaped one level up.** **C-58, C-44, C-57, D-10, C-42, C-53,
C-55, P-l, P-k.** **C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24, DD25, DD28.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement.

## DD4

**Maximize the code the two proofs share, and write it generic.** **NAME YOUR
AXIS** (C-46), fixed at `scripts/measure/ledger.py:50`. **`[LJ-1.113]` split
the per-tower share at about 28 lines, about 7 percent, before this chain
began.** **Say whether the extraction's legs are class-free, because a leg
that names a tower is a leg the other trophy pays for twice.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route extract
  anything of this shape, and did it price it?** **A retired comparable is the
  only outside number this has.**
- **`archive/dev/TASKS-archived.md`**: **grep for the retired extraction
  dispatches**, taking SHAPE and never a claim.
- **`archive/dev/JOURNAL-archived.md`**: why the retired route shaped its
  extraction as it did. **WHY NOT in one line if nothing bears.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on the extraction's
  placement. **WHY NOT in one line if none.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` and `dev/literature/j-hierarchy.md`.** **Say
in ONE line whether the orthodox development performs an extraction of this
kind at all, or whether it is an artefact of this formalization's coding.**
**That decides whether the literature can price anything here.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-378/lj-1.378-report.md` section 4, WALL TWO, FIRST. It is
the enumeration you are pricing and it is the only place this object has been
written down.

## SCOPE (write)

`agents/tasks/LJ-1-381/` only.

## RETURN

**Lead with ONE line: what does the extraction price at, and what is its
basis.** Then `Extraction` as a type. Then each of the six legs, with a term
or a line count rather than an adjective. Then any leg that is not what it was
called. Then whether the legs are class-free. Then your negative control.
**Mark every negative MEASURED or INFERRED.**
