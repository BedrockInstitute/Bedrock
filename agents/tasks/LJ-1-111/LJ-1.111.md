# LJ-1.111: can Devlin55 take the TRUNCATED sq?

tier: codex (default)

## GOAL

**Price the way around a measured wall.** `sq` at every infinite ordinal is
blocked by a truncation that cannot eliminate into an injection type. **The
theorem's own conclusion is a proposition, so the truncation may belong at
the top instead.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`. **HEAD is
`3a16f2e`. The two masters under `src/L/Condensation/` are modified by a
sibling agent that is repairing them. Do not touch anything under
`src/L/Condensation/`.**

## WHAT IS MEASURED

`[LJ-1.107]` returned PARTIAL, and its wall is exact.

**The chain closes at `ω` and at every initial ordinal.** It does not close
at `|α| ∈ α`. The term that cannot be written is the injection
`⟪ α ⟫ ↪ ⟪ |α| ⟫`: the least-of search returns `|α|` honestly, but its
witness is the truncation `∥ ⟪ |α| ⟫ ≃ ⟪ α ⟫ ∥₁`
(`src/ProbeLJ1107A.agda:247-248`), and **`⟪ α ⟫ ↪ ⟪ |α| ⟫` is not a
proposition, so `PT.rec` refuses.** The archived route hit the same wall
(`_build/l3.32-t31-report.md` sections 3 and 5).

**`Chain.theorem` (`src/ProbeLJ1107A.agda:663-666`) checks GREEN given that
injection as a module parameter**, and everything short of it closes
outright. 582 non-blank lines, about 117 s cold. **So only that one datum is
missing.**

## THE QUESTION

**Does `Devlin55` need `sq` as DATA, or would `∥ sq α ∥₁` do?**

Three facts I checked in the source, and you must verify all three:

1. **The tree already delivers the truncated form**:
   `via-col-truncated : (α : S) → Init α → ∥ sq α ∥₁`,
   `src/L/Ordinal/SquareLaw.lagda.md:963-964`. **It exists because someone
   met this wall before.**
2. **`sq` is consumed as DATA one level down**:
   `src/L/StageCardinal.lagda.md:281` builds `module B = Bound α oα infα
   (sq α infα)`, and `:286-290` take `cnt` and `cnt-inj` out of it. **So the
   truncation cannot simply be dropped in.**
3. **But the theorem's conclusion is a PROPOSITION, and `Devlin55` already
   eliminates a truncation against it**:
   `src/L/BoundedSubset.lagda.md:1606` reads
   `x∈Lκ = PT.rec (snd (x ∈ˢ Lset κ)) go (cover x x∈M)`.

**So the question is where the truncation can live, not whether it can.**

Answer these, with evidence at `file:line`:

- **How far up does `sq` have to stay data?** Follow it from
  `StageCardinal`'s `Bound` through `stage-card-upper` (`:557-559`) to
  `Devlin55`'s `code-inj` (`src/L/BoundedSubset.lagda.md:1530`) and on to
  the conclusion. **Name the highest point whose type is a proposition.**
- **What does threading `∥ sq α ∥₁` from there down cost?** In non-blank
  in-fence lines and in changed definitions. **One best-effort figure with
  its basis named.** DD8.
- **Is there a cheaper cure?** `[LJ-1.107]` says the least-of search returns
  a truncation. **Could it return the equivalence untruncated for an
  ORDINAL, where the least witness is unique?** A least element of a
  well-order is unique, so the fiber may be a proposition and the
  truncation may eliminate after all. **Check this first: it would be a few
  lines instead of a chapter.**

**This is a pricing task. Do not rewrite `StageCardinal` or `Devlin55`.**
**You may write probes.**

## THE ABORT CRITERION

- **The cheaper cure works**: report it with the machine-checked term and
  STOP. **That is the answer I most want checked rather than assumed.**
- **It does not**: report why, then price the threading, then STOP.
- **Neither route exists**: STOP and say what `Devlin55` would have to
  change. **A clean negative here is a route-level finding.**
- **Anything walls**: STOP, report the wall with its seconds.

**Do not stop at the first negative: the brief asks three questions and the
third is the cheapest.**

**Work in `src/ProbeLJ1111*.agda`. Do not touch any master.**

## C-12, AND THIS IS NOT BOILERPLATE

`[LJ-1.80]` left **SIX agda processes alive at once**, all children of one
wrapper, all on the same probe, none killed. Each carried `-M8g`: 48 GB of
worst case on a 64 GB machine at load 19. **The owner caught it; no tool
did.**

**ONE agda process at a time, and a sibling agent holds the other slot. If a
check does not return, KILL IT before you start another, and report the wall
with its seconds.**

## WHAT YOU MUST NOT DO

- **Do not assume the axiom of choice.** Five dispatches have measured this
  chain choice-free. **Choice would eliminate the truncation trivially and
  that is exactly the move that is forbidden. Say at once if a step needs
  it.**
- **Do not weaken any conclusion.** Only the hypothesis's truncation status
  moves.
- **Do not touch `src/L/Condensation/`**, where a sibling works.
- **Do not touch `src/L/Coding/` or `src/V/`.**
- **Never `src/Everything.lagda.md`.**
- **Do not raise the heap cap.** C-12.
- **Read line numbers from the source, never from a report.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

**A truncation moved to the top is a change to the shared cardinal
chapter.** Say whether the J tower inherits the result unchanged.

## ARCHIVE (DD18)

- **`_build/lj-1.107-report.md`**, read WHOLE, and **`src/ProbeLJ1107A.agda`**.
  **The wall, and the conditional chain that closes given the injection.**
- **`_build/l3.32-t31-report.md` sections 3 and 5**, which `[LJ-1.107]`
  cites for the same wall in the retired route. **Read it: an archived
  measurement of this exact obstacle is worth more than a fresh guess.**
- `_build/lj-1.106-report.md` and `src/ProbeLJ1106A.agda`, `Init` and `sq`
  at the Hartogs cardinal.
- **`src/L/Ordinal/SquareLaw.lagda.md:938-964`**, both `via-col-square` and
  `via-col-truncated`.
- **`src/L/StageCardinal.lagda.md:270-300` and `:550-565`**, where `sq` is
  consumed as data.
- **`src/L/BoundedSubset.lagda.md:1361-1400`, `:1520-1540` and
  `:1595-1615`**, `Devlin55`'s telescope, `code-inj`, and the truncation it
  already eliminates.
- `dev/LESSONS.md` **C-38 as extended, C-39, C-40, P-x**, D-8, D-30, P-l,
  read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Say in two lines whether Devlin's 5.5 uses the square law as data or only
its existence**, from `dev/literature/devlin-II5.md`. Spend little.

## SCOPE (read)

`src/ProbeLJ1107A.agda:240-260` FIRST, then
`src/L/StageCardinal.lagda.md:270-300`, then
`src/L/BoundedSubset.lagda.md:1520-1540`.

## SCOPE (write)

`src/ProbeLJ1111*.agda` only. Your report is `_build/lj-1.111-report.md`.
**No master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-8.** One best-effort figure with its basis named, and the widest
  unmeasured term.
- **C-36.** Write the term you could not write.
- **C-38 as extended, C-35, D-30, D-10.**
- **C-39.** A brief's prohibition binds harder than its goal. **If a line of
  this brief blocks a route you can see, say so in the report and name the
  route. That is a required section, not a courtesy.**
- **C-40.** Verify the CONSUMERS of a changed master, never the master
  alone. **You change no master, but say which masters a real repair would
  touch.**
- **P-l.** A price from a comparable elsewhere is a hypothesis.
- **P-x.** A transparent construction in a record field type is paid by
  every elaboration of the record.
- **P-h, P-i, P-k, P-m, P-n, P-o, P-q, P-t, P-u, P-v, P-w** as the bundle
  gives them.
- **P-c, R-36, R-38, R-35, R-40.**
- **I-5.** The inference trap this tree has paid for.
- **C-12.** ONE agda process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-37.**
- **D-1, D-26, D-29.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The working tree carries a sibling's
  uncommitted repair under `src/L/Condensation/`.**
- Do NOT run `make check`.
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- **Report the load average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.111-report.md` incrementally, skeleton first.

**Lead with the cheapest cure: does the least witness's uniqueness make the
fiber a proposition, so the truncation eliminates?** YES or NO, with the
term or the error. Then the highest point in the chain whose type is a
proposition. Then the threading price with its basis. Then whether anything
needs choice. Then the C-39 section. **Mark every negative MEASURED or
INFERRED.** Then the DD4 answer.
