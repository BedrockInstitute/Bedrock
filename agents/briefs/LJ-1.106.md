# LJ-1.106: build Init at the Hartogs cardinal

tier: codex (default)

## GOAL

**Build the next block of the cardinal side.** `Init κ` is priced at 150
lines with one piece unmeasured. **Build it, and measure that piece.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`5cc68f7`**. HEAD is green. **A sibling agent holds the other Agda slot and
works inside `src/L/Condensation.lagda.md`. Do not touch that file.**

## WHAT IS MEASURED, and I re-ran the decisive checks myself

`[LJ-1.94]` built the ambient Hartogs cardinal: `src/ProbeLJ194A.agda`,
GREEN, 1058 non-blank lines, 27 s cold, **no choice anywhere**.

`[LJ-1.101]` closed the type gap: **`cardκ` typechecks at the MASTER's
`IsCardinal`**, no transport (`src/ProbeLJ1101A.agda:56-57`). Exit 0 when I
re-ran it.

**`Init α` (`src/L/Ordinal/SquareLaw.lagda.md:692-698`) has four
components**, and the tree pays `sq α` for it by the delivered
`via-col-square` (`:960-961`):

| component | status per `[LJ-1.101]` |
|---|---|
| `IsOrd κ` | **DELIVERED**, `src/ProbeLJ194A.agda:919-920` |
| `ω ∈ κ` | **DELIVERED**, `:876-877` |
| the square cardinality clause | **MACHINE-CHECKED from `IsCardinal`** through a countability bridge, `src/ProbeLJ1101A.agda:78-103`, **under one hypothesis: an injective pairing `⟪ ω ⟫ × ⟪ ω ⟫ ↪ ⟪ ω ⟫`** |
| successor closure, `γ ∈ κ → sucV γ ∈ κ` | **NOT DELIVERED.** New content, priced 60 to 150 lines, INFERRED |

**`InitAtSite.initκ : Init SiteAt.κ` already checks under exactly two
hypotheses** (`src/ProbeLJ1101A.agda:105-109`): the pairing and the
successor closure. **So the assembly is done and two pieces are missing.**

## WHAT TO BUILD

**Supply both hypotheses, so `Init SiteAt.κ` holds with nothing assumed.**

1. **The pairing `⟪ ω ⟫ × ⟪ ω ⟫ ↪ ⟪ ω ⟫`**, priced 20 to 50 lines. The
   tree delivers the pairing on `ℕ` with injectivity (`pair`, `pair-inj`,
   `src/FOL/Count.lagda.md:29-30`, `:59-60`) and the injective numerals
   (`#-inj′`, `src/V/Coding.lagda.md:114-115`). **The one unmeasured step
   inside it is the `⟪ ω ⟫` presentation bijection. Measure it.**
2. **The successor closure `γ ∈ κ → sucV γ ∈ κ`**, priced 60 to 150 lines.
   `κ = sett WO ot`, so this asks that a successor of a countable ordinal
   is itself an order type of a well-order on a subset of `ω`. **This is
   the widest unmeasured term of the whole answer.**
3. **Then `Init SiteAt.κ` with no hypothesis left.** Report the term.

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you leave standing must be one something can supply.
Name what would supply it, at `file:line`.** If nothing can, that is the
finding: report the term you could not write.

**Try to refute any hypothesis you introduce.** `src/ProbeLJ197A.agda` is
the shape. **Seven statement-level defects this phase were hypotheses
nothing could satisfy, and four of them were found only after a build was
paid for.**

## THE ABORT CRITERION

- **Both pieces land and `Init SiteAt.κ` holds outright**: report the terms
  and the seconds, and STOP. **Do not go on to `sq` at every infinite
  ordinal; that is 500 lines and a separate dispatch.**
- **One piece lands and the other does not**: report both, with the term you
  could not write. **That is a good return.**
- **A piece turns out to need choice**: STOP and say which and where. **The
  chain has been choice-free so far and that is worth keeping.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. Report both pieces.**

**Work in `src/ProbeLJ1106*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.** `[LJ-1.92]` and `[LJ-1.94]` both
  measured the chain choice-free. **Say at once if a step needs it.**
- **Do not weaken `Init`.** `via-col-square` consumes it as stated.
- **Do not touch `src/L/Condensation.lagda.md`**, where a sibling works.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**
  **Two returns this session called delivered content absent, and both were
  caught by reading the source.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**`[LJ-1.94]` measured its whole chain generic: no tower object in any type
of its mathematics.** Keep it that way, and say whether either piece breaks
it.

## ARCHIVE (DD18)

- **`_build/lj-1.101-report.md`**, read WHOLE, and **`src/ProbeLJ1101A.agda`**,
  read WHOLE. **The assembly, the bridge, and the two hypotheses. This is
  your starting material.**
- **`_build/lj-1.94-report.md`** and **`src/ProbeLJ194A.agda`**, read WHOLE.
  The Hartogs build, `WO`, `ot`, `InitialSegment`, `Count`.
- `_build/lj-1.92-report.md` and `src/ProbeLJ192A.agda`, the order-type
  block.
- **`src/L/Ordinal/SquareLaw.lagda.md:692-698` and `:938-964`**, `Init` and
  `via-col-square`.
- `src/FOL/Count.lagda.md:20-70`, the `ℕ` pairing.
- `src/V/Coding.lagda.md:110-120`, the injective numerals.
- `dev/LESSONS.md` **C-38 as extended, C-39**, C-35, C-36, D-8, D-30, P-l,
  P-m, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Banked. Spend nothing.** `[LJ-1.92]` settled that Devlin assumes order
types. Say so in one line.

## SCOPE (read)

`src/ProbeLJ1101A.agda:60-115` FIRST, then
`src/L/Ordinal/SquareLaw.lagda.md:692-698`, then
`src/ProbeLJ194A.agda`'s `SmallWO` and `Hartogs` blocks.

## SCOPE (write)

`src/ProbeLJ1106*.agda` only. Your report is `_build/lj-1.106-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES
  it.
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-35, C-36, D-8, D-30, D-10.**
- **P-l.** A price from a comparable elsewhere is a hypothesis. **The 150
  line figure is INFERRED. Replace it with a measurement.**
- **P-m.** The instantiation class, which is where `[LJ-1.92]`'s 17 s and
  `[LJ-1.94]`'s 16 s both went.
- **P-h, P-i, P-k, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the bundle gives
  them.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.106-report.md` incrementally, skeleton first.

**Lead with whether `Init SiteAt.κ` holds with no hypothesis left**, in the
words YES or NO, with the term at `file:line` and its seconds. Then each
piece: lines, seconds, and what it rode. Then the successor closure's own
price, MEASURED this time. Then whether anything needs choice. Then the C-39
section. **Mark every negative MEASURED or INFERRED.** Then the DD4 answer.
Confirm no master was touched.
