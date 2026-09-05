# LJ-1.352: DD25 review of `[LJ-1.347]`'s conjunct refutation

tier: pi (in-harness-subagent-mode), **the switch's ADVERSARIAL row.**
`[LJ-1.347]` was authored in-harness by opus, this mode's DEFAULT row, so the
adversarial row is `herdr` / `pi` / `glm-5.3`. **DD17's invariant holds: the
critic is not the author.**

## WHY

**`[LJ-1.347]` returned FALSE with a machine-checked countermodel.** DD25
requires the review immediately. **I skipped this gate once this session and
`make check` caught it after a repair had landed. This is the third negative in
a row to get its review before anything is built on it.**

**And a 24-site chain rests on this verdict being right.** `[LJ-1.350]` is
probing a repair for that chain right now, **on the assumption that the conjunct
it repairs is genuinely false.**

## THE CLAIM, three separable parts

**1. THE CONJUNCT IS FALSE.** `agents/tasks/LJ-1-347/Residue347.agda`, exit 0 in
3.16 s, refuting `wCodesK` **at the chapter's own delivered `KValue` record**,
with every ambient fact from delivered code (`ChainZ:2837-2844`,
`KTies:6227-6234`).

**2. THE `m = 0` CLAUSE, which walled four times, SETTLES.**
`agents/tasks/LJ-1-347/Zero347.agda`, exit 0 in **1.51 s**, using neither of the
two walled routes: the library exports the refusal as a plain function and
`# zero = ∅` is a defining equation.

**3. THE WALL IS THE PATTERN-MATCH CASE SPLIT**, isolated by five controls two
lines apart: no split 1.73 s, plus a two-line dispatcher **8 GB at 373.93 s**,
the same split via the library eliminator **1.64 s**. **This is law C-58,
written from it today.**

## WHAT TO ATTACK

**1. NON-VACUITY.** **It is this chain's pivot every time**, and `[LJ-1.349]`
strengthened its sibling's by exhibiting a term showing the countermodel lives
INSIDE the chapter's intended premise class. **`[LJ-1.347]` reports three
layers: the other three conclusions hold at the witnesses, every premise is a
closed term, and the refutation runs on the delivered record rather than on
parameters.** **Re-check all three, and ask whether its witness is in the
intended class the way `[LJ-1.349]`'s was.**

**2. THE CONTROL THAT MEASURES THE SITE.** `Control347.agda`, exit 0 in 1.50 s:
the conjunct **HOLDS at a numeral arity and FAILS at the singleton, one argument
apart in one file.** **Verify that; it is the strongest single piece of
evidence and also the easiest to get subtly wrong.**

**3. THE COUNT: 24 producers, 8 second-shape, 20 consumer slots**, from reading
all 106 parameter blocks. **`[LJ-1.344]`'s SIX is MEASURED FALSE by it.**
**Re-derive the count, and especially section 5.4's claim that the sites form a
CHAIN rather than 24 independent statements**, because `[LJ-1.350]`'s whole
pricing rests on it.

**4. C-58 ITSELF.** **A law was written from these five controls today.** **If
the controls do not isolate what they claim, the law is wrong and it will
mislead every future wall.** **Re-run at least the two that differ by two
lines.**

**5. THE CONTRADICTION IT INHERITED.** `[LJ-1.347]` says the missing bound is
shapedness; `[LJ-1.348]` measured that shapedness does not constrain the arity
slot at all, and `[LJ-1.349]` UPHELD that. **Say whether `[LJ-1.347]`'s repair
reading survives.**

## THE ABORT CRITERION (D-1)

- **UPHOLD.** Then four of six construction ties are settled false and
  `[LJ-1.350]`'s repair line is sound.
- **OVERTURN.** **Then `[LJ-1.350]` is repairing something true and must be
  stopped.** **Say so immediately.**
- **SPLIT.** **Likeliest on the wording**: `[LJ-1.349]` ruled that its sibling's
  「MEASURED FALSE」was right but needed the qualifier「no uniform supplier」.
  **Say whether the same qualifier belongs here.**
- **A WALL.** **C-58 is the medicine and it is the thing under review: if you
  wall, replacing a numeral split with the eliminator is the first move.**

## CONSTRAINTS

- **LAND NOTHING, REPAIR NOTHING.** Write only in `agents/tasks/LJ-1-352/`.
  **`src/` is forbidden** (I-5).
- **`agents/tasks/LJ-1-344/Supply344.agda` is RED and that is EXPECTED**: a
  landing removed parameters it still passes. **Do not repair it.**
- **Chapter line numbers have DRIFTED 109 lines.** Re-derive any citation you
  rely on (C-44).
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **Both obvious alternatives OVER-COUNT, MEASURED.** A sibling is live.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended; the target
  measured 0.48 s).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-352/lj-1.352-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check`. **No em dash.**
- Evidence is `file:line`. ASD-STE100. Mark every negative **MEASURED** or
  **INFERRED**, in those words.

## THE VERDICT WORD

**UPHOLD, OVERTURN or SPLIT**, first word of your return. **13 of 32 decided
DD25 reviews here have overturned, 41 percent. An overturn is the valuable
outcome and you are not rewarded for agreeing.**

## THE RULES

**C-45, C-42, C-44, C-57, C-58, C-53, C-36, D-10, P-l, P-i.**
**C-12, C-22, C-32, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`. **Say whether the refutation is class-free, as
its two siblings were, so the falsity holds at both carriers by one file.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-347/lj-1.347-report.md`, read WHOLE.** The target; its
  sections 2 and 5 are the two halves under review.
- **`agents/tasks/LJ-1-349/lj-1.349-report.md`**, the sibling review that set
  this chain's standard for non-vacuity.
- **`agents/tasks/LJ-1-348/lj-1.348-report.md`**, whose shapedness reading may
  contradict the target's repair.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Say in one line whether a 24-site chain of
unbounded conjuncts has any counterpart in his text.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-347/Control347.agda` FIRST: one file holds the conjunct at
one argument and fails it at another, and it is the shortest path to a verdict.

## SCOPE (write)

`agents/tasks/LJ-1-352/` only.

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then non-vacuity, re-checked
against `[LJ-1.349]`'s standard. Then the one-argument-apart control, verified.
Then the count and the chain claim, re-derived. Then C-58's two decisive
controls, re-run. Then whether the shapedness contradiction breaks the repair
reading. **Mark every negative MEASURED or INFERRED.**
