# LJ-1.159: `LeastCardInj` is 48 times the bar and nobody has attacked it

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**A5's real gate, named by `[LJ-1.156]` and never attacked.** Find where 99
seconds sit in 44 lines, and say what would move them.

## WHAT IS MEASURED

`[LJ-1.156]` dissolved `CSB` and, in doing so, measured where A5's seconds
actually are:

| | seconds |
|---|---:|
| the whole dissolution probe, cold, 3 kept runs | **133.00** |
| of which `LeastCardInj` ALONE | **100.64** |
| `[LJ-1.107]`'s bijection `LeastCard`, verbatim | 96.09 |
| `CSB`, the thing everyone worried about | **2.03** |
| the import control | 1.27 |

**0.384 s per line. The bar is 0.010514. That is 48 times.**

**And 99 of those seconds are 44 lines.**

**The swap from bijections to injections did NOT cause it**: 100.64 against
96.09 is inside `[LJ-1.148]`'s measured 12.8 percent band. **The cost was
already there in `[LJ-1.107]` and nobody has attacked it since it was
measured.**

## WHAT TO DO

1. **Profile it.** `agda --profile=definitions` and `--profile=internal` on
   `agents/tasks/LJ-1-156/ProbeLJ1156A.agda`. **Find WHERE inside the 44 lines.**
2. **Transplant the worst definition into its own probe and bisect it**, which
   is the method `[LJ-1.145]` used to find a 2,526 ms conversion inside a
   6,451-line master.
3. **Then price a cure**, in lines and seconds, with its basis (DD8), **and say
   SHARED or WING-LOCAL and what it does to the baseline.** That column decides
   whether the cure helps or hurts the verdict.

## THE THREE CURES ALREADY TRIED AT THIS CLUSTER, so you do not repeat them

**All three were MEASURED and all three are P-l lessons:**

| cure | where it worked | where it did NOT |
|---|---|---|
| `opaque` seal | `Condensation`, 2,459 ms to under 1 | `[LJ-1.152]`'s site, moved nothing; `[LJ-1.154]`'s seals not load-bearing |
| replacement to separation | the identity graph, 254 s to 1.73 | not yet tried here |
| telescope to record | the `*Agree` masters, `DeadCode` by 106x | `Condensation` itself, 4.4 percent only |

**Try the ones that have not been tried HERE, and measure rather than assume.**

## THE STRUCTURAL LEAD, which is INFERRED and yours to refute

**`[LJ-1.156]` found that Devlin has no `CSB` step because II.6.6 defines the
Goedel pairing as the ORDER TYPE of predecessors under the canonical order, so
it is a bijection by construction.** It then recorded that
**`CSB` existed in our chain only because this project PRICED ORDER TYPES OUT**
(`src/L/Ordinal/SquareLaw.lagda.md:1-11`).

**So the question worth asking: is `LeastCardInj` expensive for the same
reason?** A least-cardinal search over a well-order may be doing by search what
an order type does by construction.

**That is INFERRED and it is mine. Refute it if the profile says otherwise.**

## THE ABORT CRITERION

- **You find where the 99 seconds are and price a cure**: report and STOP.
- **The cost is spread across the 44 lines with no dominant term**: **STOP AND
  SAY SO.** Then A5 carries this and the block's price is a DD24 question for
  the owner rather than a craft one, which is a complete answer.
- **The cure is SHARED**: **say so loudly.** A shared cure moves the baseline
  and may make the verdict worse, which is what happened at `[LJ-1.147]`.
- **Anything walls**: STOP, report it. **Never raise the cap.**

## WHAT YOU MUST NOT DO

- **Do not edit any master.** This is a diagnosis.
- **Do not touch the three `*Agree` masters.** `[LJ-1.158]` is collapsing their
  telescopes right now.
- **Do not delete lines to improve a ratio.**
- **A probe goes in `agents/tasks/LJ-1-159/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** A sibling
  is running. **Discard a warm-up, take more than one run for any figure a
  decision rests on, and report the load beside every absolute figure.**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **A least-cardinal search is content BOTH
trophies need. Say whether the cure is template.**

## ARCHIVE (DD18)

**`[LJ-1.157]` measured that 37 of 61 live briefs cite no archive, and that
three tasks priced `levelIn` without an 845-line comparable the route's own
recon had marked ADAPTABLE. This section is real.**

- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`**, **399
  in-fence lines**, the internal predicate layer: equinumerosity, cardinal,
  successor cardinal, each a concretized formula with a certificate, built
  once and generically. **Its own prose records a scope-gate ruling that
  CONTRADICTS what `[LJ-1.156]` just did**: it took equinumerosity as 「there
  exists a bijection」 and REFUSED 「an injection each way」, because the latter
  turns every equality into a per-consumer Cantor-Bernstein obligation. **Read
  that ruling and say whether it bears on the injection swap or is about a
  different layer.**
- **`archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md`** and
  **`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md`**: the
  retired route's own square law and counting.
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-156/lj-1.156-report.md`, read WHOLE, and
  `ProbeLJ1156A.agda`.
- `agents/tasks/archive/LJ-1-107/ProbeLJ1107A.agda`, where the cost first
  appeared.
- **`dev/LESSONS.md` P-y, P-t, P-s, P-l, P-m, C-12**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`dev/literature/devlin-II5.md` and `_build/literature/dev2.txt` around II.6.6.
**Say what Devlin's least cardinal actually is, and whether he searches or
constructs.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-156/ProbeLJ1156A.agda` FIRST, then its report.

## SCOPE (write)

`agents/tasks/LJ-1-159/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for recon`.

- **P-t.** An average hides the term.
- **P-l.** Three cures at this cluster transferred to some sites and not
  others, all measured today.
- **P-y, P-s, P-m, P-x, P-w, C-12, C-22, C-36, C-38 as extended, C-39, C-40.**
- **DD8, D-1, D-10, D-26, D-29, D-30. C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with WHERE the 99 seconds are**, at the finest granularity you reached,
with the load and the run count. Then the cure and its price, and SHARED or
WING-LOCAL. Then whether the order-type lead held. Then what Devlin does. Then
the DD4 answer. **Mark every negative MEASURED or INFERRED.**
