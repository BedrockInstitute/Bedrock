# LJ-1.107: sq at every infinite ordinal

tier: codex (default)

## GOAL

**Supply `Devlin55`'s first parameter.** `sq` holds at the Hartogs cardinal.
The consumer needs it at EVERY infinite ordinal. **Build the reduction.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`a2e55ab` except `src/L/Condensation.lagda.md`, where **a sibling agent is
working. Do not touch that file.**

## WHAT IS MEASURED, and I verified the decisive term myself

`[LJ-1.106]`: **`Init SiteAt.κ` holds with NO hypothesis left**,
`src/ProbeLJ1106A.agda:573-574`, at the MASTER's statement
(`import L.Ordinal.SquareLaw {ℓ} lem as SQ` at `:43`). **And `sq κ` follows
at once**: `sqκ = SQ.via-col-square SiteAt.κ initκ` (`:578-579`). **I re-ran
the probe: exit 0.** 507 non-blank lines, 31.20 s cold. **No choice and no
LEM in the new content.**

**Three delivered pieces you must reuse and not rebuild:**

- **`PullbackAt` (`src/ProbeLJ1106A.agda:150-373`, 212 lines, 7.6 s), the
  GENERIC half.** For an ordinal `α` with an injection `⟪ α ⟫ ↪ ⟪ ω ⟫`, it
  builds a well-order on a subset of `ω` whose order type is `α`.
- **`NumeralPresentation.ω≃ℕ` (`:124-125`) and `pairω` (`:127-137`)**, the
  presentation bijection and the pairing, choice-free and LEM-free.
- **`SuccClosure`, `SucPresentation`, `SuccCount` (`:385-529`, 130 lines,
  11.5 s)**, the successor's countability.

## THE ROUTE, from `[LJ-1.101]` section 2.2, and it is choice-free

`Devlin55` takes `sq α` for every `α` with `α ∉ ω`
(`src/L/BoundedSubset.lagda.md:1362-1363`). The reduction:

1. **`sq ω`** directly from the ℕ pairing. **Not via `Init`: `Init ω` is
   FALSE**, because `Init` demands `ω ∈ α`.
2. **`|α|`, the least ordinal in bijection with `α`.** For an ordinal `α`,
   separate the `β ∈ sucV α` whose presentation biject with `α`'s; the set
   is inhabited by `α` itself; take the least. **Choice-free: `α` is an
   ordinal, so it is already well-ordered by membership.**
3. **`Init |α|` for infinite `α`**: `IsOrd` and `ω ∈ |α|` from `α`
   infinite; **successor closure because an infinite cardinal is a limit
   ordinal**; the square clause by minimality of `|α|`.
4. **`sq |α|`** by the delivered `via-col-square`
   (`src/L/Ordinal/SquareLaw.lagda.md:960-961`).
5. **`sq α` from `sq |α|`** by composition: `α ↪ |α|` by the bijection and
   `|α| ⊆ α`, so `α² ↪ |α|² ↪ |α| ↪ α`.

**Steps 2 and 3 are the new content. Steps 1, 4 and 5 ride delivered
machinery.**

## WHAT TO BUILD

**Build the chain and end at `(α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq α`,
the exact shape `Devlin55` takes.** Then, if it holds, **apply it: state
`Devlin55`'s `sq` parameter as a value.**

**Report per step: lines, cold seconds, and what it rode.**

## THE RULE ON HYPOTHESES, stated as a test and not as a shape

**Every hypothesis you leave standing must be one something can supply.
Name what would supply it, at `file:line`.** If nothing can, that is the
finding: report the term you could not write.

**Try to refute any hypothesis you introduce.** `src/ProbeLJ197A.agda` is
the shape, and `src/ProbeLJ1104A.agda:118-120` is the one that caught a
defect one dispatch after the rule was written. **Seven statement-level
defects this phase were hypotheses nothing could satisfy.**

## THE ABORT CRITERION

- **The chain closes**: report the term and the per-step table, then STOP.
  **Do not go on to `absorbs-subset`; that is a separate dispatch.**
- **A step does not close**: report it with the term you could not write,
  **and CONTINUE to the next step if it does not depend on the failed one.**
  A partial chain with an honest boundary is a good return.
- **A step needs choice**: STOP and say which and where. **The chain has
  been choice-free through four dispatches and that is worth keeping.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative. Report every step you attempted.**

**Work in `src/ProbeLJ1107*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.** Four dispatches have measured this
  chain choice-free. **Say at once if a step needs it.**
- **Do not weaken `sq`.** `Devlin55` consumes it as stated.
- **Do not rebuild `PullbackAt` or the presentation bijection.** They are
  delivered generic in `src/ProbeLJ1106A.agda`. **Import and reuse.**
- **Do not touch `src/L/Condensation.lagda.md`**, where a sibling works.
- **Do not touch anything under `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers and counts from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**This whole chapter is about ordinals and injections, never about
definability, so it is the most shared content of the wing.** Say whether
any step names a tower object, and whether the J tower gets the chapter
unchanged.

## THE COST QUESTION

The wing is over DD24 and the owner ruled the threshold question is settled
when the phase's content is complete. **So measure, do not gate.** Report
non-blank in-fence lines and cold seconds per step, with the load average.
**`[LJ-1.101]` priced the whole chain at 500 lines, band 350 to 750, and
that figure is INFERRED. Replace it with a measurement.**

## ARCHIVE (DD18)

- **`_build/lj-1.106-report.md`**, read WHOLE, and **`src/ProbeLJ1106A.agda`**,
  read WHOLE. **Your starting material. `PullbackAt` is the generic half
  and it is already built.**
- **`_build/lj-1.101-report.md` section 2.2**, read WHOLE. The route.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, the Hartogs build.
- `_build/lj-1.92-report.md` and `src/ProbeLJ192A.agda`, the order-type
  block.
- **`src/L/Ordinal/SquareLaw.lagda.md:692-698`, `:938-964`, and
  `FiniteBase` around `:539-542`.**
- `src/L/BoundedSubset.lagda.md:1361-1368`, the exact shape you must
  produce.
- `dev/LESSONS.md` **C-38 as extended, C-39**, C-35, C-36, D-8, D-30, P-l,
  P-m, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Devlin uses the square law at 5.5.** Say in two lines whether he proves it
for all infinite ordinals or cites it. Spend little.

## SCOPE (read)

`src/ProbeLJ1106A.agda:150-373` FIRST, then `:100-140`, then
`src/L/Ordinal/SquareLaw.lagda.md:692-698` and `:938-964`.

## SCOPE (write)

`src/ProbeLJ1107*.agda` only. Your report is `_build/lj-1.107-report.md`.
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
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-m.** The instantiation class, where the seconds have gone three times
  running: 17 s, 16 s, 11.5 s.
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

Write `_build/lj-1.107-report.md` incrementally, skeleton first.

**Lead with whether `(α : S) → (α ∉ ω) → SQ.sq α` holds outright**, in the
words YES or NO, with the term at `file:line` and its seconds. Then the
per-step table: lines, cold seconds, what it rode. Then whether anything
needs choice. Then the C-39 section. **Mark every negative MEASURED or
INFERRED.** Then the DD4 answer. Confirm no master was touched.
