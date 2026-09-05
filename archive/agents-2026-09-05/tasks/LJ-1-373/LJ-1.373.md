# LJ-1.373: can `BandChoice` be DISCHARGED, or must it be assumed?

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **PROBE. Land nothing.**

## THE OWNER'S RULING THAT FUNDS THIS

> **Do not assume it.**

**Ruled 2026-08-16 on `[LJ-1.369]`.** **So `BandChoice` is admissible ONLY if
it can be PROVED in this tree.** **An undischarged hypothesis stays off the
trophy**, and `[LJ-1.323]` restated the trophy precisely so that it carries
none.

**This task decides whether a cheap door exists at all, or whether
`[LJ-1.332]`'s untruncation is the only door.** **Both answers are useful and
one of them is a stop.**

## THE OBJECT, and it is already spelled

`agents/tasks/LJ-1-368/Probe368.agda:226-227`:

```agda
BandChoice = LimitBandT → ∥ LimitBand ∥₁
```

**MEASURED by `[LJ-1.368]`, two green files, re-run them:**

- **`closes-from-choice`, `:229-236`, exit 0:** `BandChoice` plus one
  `PT.rec` gives the trophy's conclusion, **with NO untruncation anywhere.**
- **`choice-from-untruncation`, `:241-242`, exit 0:** the untruncation
  `[LJ-1.332]` asks for implies `BandChoice` **in one line**.

**So `BandChoice` is no STRONGER than the open debt, MEASURED.** **That it is
strictly WEAKER is INFERRED and its basis is the literature, not a term.**

## THE QUESTION, in three parts

**1. CAN IT BE PROVED OUTRIGHT?** **Try to inhabit `BandChoice` from the
delivered tree.** **The band is the non-initial limit band, and
`[LJ-1.333]` measured that it is the exact complement of the only
canonicalizer.** **If that complement is what blocks a proof too, say so: then
ONE obstruction explains the untruncation's five failures AND this, and that
is a route-level finding worth more than either.**

**2. CAN IT BE PROVED FROM SOMETHING ALREADY DELIVERED AND WEAKER?** **The
tree holds `LEM` as a module parameter at every L chapter.** **Does classical
logic alone give it?** **A selection from a truncated family is exactly where
LEM stops being enough, so I expect NO, but I expect it as a hope rather than
a measurement. Measure it.**

**3. IF IT CANNOT BE PROVED, WHAT IS THE HONEST RESIDUE?** **Name the smallest
thing that would give it, and say whether THAT is provable.** **A chain of
「provable from X, and X is provable from Y」ends somewhere, and where it ends
is the real answer to the owner's question.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT IS PROVABLE.** **Then the owner's refusal costs nothing, the cheap door
  is real and free, and `[LJ-1.332]`'s untruncation is retired.** Report the
  term. **Best possible outcome on this chain.**
- **IT IS NOT PROVABLE, AND THE OBSTRUCTION IS THE CANONICALIZER'S
  COMPLEMENT.** **Then one obstruction explains everything on this chain, and
  the untruncation is the only door. Say so; that closes the question.**
- **IT IS NOT PROVABLE FOR A DIFFERENT REASON.** **Name it. A second, distinct
  obstruction would mean the chain is harder than anyone has said.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** **C-56: when a truncated
  proof walls, the cost is in the ASSEMBLY; bisect the eliminator nesting
  first.** **`[LJ-1.368]` proved C-56's point on this exact chain today.**

## CONSTRAINTS

- **LAND NOTHING. `src/` is forbidden** (I-5). Write only in
  `agents/tasks/LJ-1-373/`.
- **You may READ and COPY from `LJ-1-332/`, `LJ-1-333/`, `LJ-1-337/`,
  `LJ-1-365/` and `LJ-1-368/`. Edit none of them.**
- **`[LJ-1.372]` is live and writes `scripts/gate/` and
  `.claude/skills/codex-dispatch/`.** No collision; it holds no Agda slot.
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.** Cap is TWO.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES.** **If you inhabit `BandChoice`,
  show a variant that does NOT type, so the green is not vacuous.**
  **`[LJ-1.368]` measured that `squash₁` succeeds exactly when the motive
  unfolds to a truncation, so a green there can be a tautology. Do not repeat
  that.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-373/lj-1.373-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** ASD-STE100. Evidence is `file:line`.
  Mark every negative **MEASURED** or **INFERRED**.

## PREMISES

- **`BandChoice` closes the trophy's conclusion with no untruncation**, at
  `agents/tasks/LJ-1-368/Probe368.agda:229-236`, exit 0.
- **The untruncation implies `BandChoice` in one line**, at `:241-242`,
  exit 0.
- **The band is the exact complement of the only canonicalizer**
  (`[LJ-1.333]`), which is why I expect the same obstruction here.
- **The tree holds `LEM` at every L chapter as a module parameter.**

**Mark each VERIFIED or REFUTED at `file:line`.**

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-seven briefs carried a claim an agent measured
FALSE, and today `[LJ-1.368]` refuted the verdict word of a probe I had
accepted within minutes.** **The one at risk: 「the canonicalizer's complement
is what will block this too」.** **That is an analogy from `[LJ-1.333]`'s site
to yours, and P-l says a judgement at one site is a hypothesis at another.**
**If the obstruction here is different, my whole framing of this chain is
wrong and I would rather learn it now.**

## THE RULES

**C-56: the wall is in the ASSEMBLY, proved on this chain today.** **C-54: a
SET-motive stall is a `2-Constant` obligation before it is a principle; read
the FULL entry.** **C-45 and its mirror: `exit 0` is not a supply, and exit 42
is not an impossibility, which is exactly how `[LJ-1.365]` overreached.**
**C-44, C-57, D-10, C-42, C-53, C-58, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD8, DD18, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**`[LJ-1.368]` measured the DD4 stake and it is real: the wrap route edits NO
consumer, while the supplier-change cure touches `L.Ordinal.SquareLaw`, which
BOTH proofs share.** **So a provable `BandChoice` is also the DD4-cheapest
outcome. Say whether your term keeps that property or gives it up.**

## ARCHIVE (DD18)

**`scripts/gate/check-dd18-survey.py` GATES your return: name each of the four
corpora, cited or declined in ONE line, and QUOTE one line per archived file
you read, at its real line number.**

- **`archive/src/2026-08-09-rud-route/`**: **did the retired route ever prove
  a selection from a truncated family, and how?** **Grep for `PT.rec`,
  `∥_∥₁` and any choice-shaped lemma near its square-law work.** **A delivered
  answer settles this in an hour.**
- **`archive/dev/JOURNAL-archived.md:1630`**: **the retired route's reason for
  refusing choice, 「a choice principle implies excluded middle」.** **Quote it
  and say whether it bears on a PROOF as opposed to an assumption, because
  `[LJ-1.368]` said it was spent only as an argument against ASSUMING.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on choice or on
  truncation. **WHY NOT in one line if none bears.**
- **`archive/dev/TASKS-archived.md`**: the retired square-law dispatches,
  taking SHAPE and never a claim.

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md:216-229`.** **`[LJ-1.368]` used
`:225-229` for AC's truncated conclusion and `:216-221` for the untruncation
taboo.** **Read both and say whether the digest names any condition under
which a selection of this shape is PROVABLE rather than assumed.** **That is
the literature asked the owner's question.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-368/Probe368.agda:220-245` FIRST, and RE-RUN it: it holds
`BandChoice` and both implications, and it is two hours old.

## SCOPE (write)

`agents/tasks/LJ-1-373/` only.

## RETURN

**Lead with ONE word: PROVABLE, BLOCKED-BY-THE-COMPLEMENT, or
BLOCKED-OTHERWISE.** Then the term, or the exact goal that refused it with
Agda's own type. Then whether LEM alone suffices. Then the smallest thing that
would give it, and whether THAT is provable. Then your negative control, and
say why it is not a tautology. **Mark every negative MEASURED or INFERRED.**
