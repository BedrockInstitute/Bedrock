# The decision tree, written BEFORE the returns

**Clause: know your next move for each outcome before the return arrives.** This
file is that, for 729-733. Working note, not a brief.

## THE BOARD

| code | obligation | state at writing |
|---|---|---|
| 724-SPLIT | scoped `table-sat` | RUNNING |
| 726 | `ambient-at-Lω` | RUNNING |
| 725-SPLIT | `stage-read` | DONE meter-GO, report STOP |
| 727-SPLIT | `level-at-pair` | DONE GO |
| 728-SPLIT | `grounded-from-complete` at heavy | PARKED, watchdog swap |
| 715-SPLIT-SPLIT-SPLIT | fourth landing | empty, forbidden |
| 728-SPLIT-SPLIT | same term | empty, watchdog |

## IF 729 IS GO

The key bound is paid. 733's first hypothesis is a report on the next refill, not this one: 733 already takes the TYPE.

**Move A:** if 729 is NO-GO at `ω ≤ γ`, the report names the successor height. Rewrite 733's `keyS` hypothesis to that height. Do not retry unscoped `keyS ∈ Lset γ`.

## IF 730 IS GO

The environment-set bound is paid. Same as 729 for 733's second hypothesis.

**Move A:** if 730 is NO-GO at `ω ≤ γ`, rewrite 733's `envSet` hypothesis to the named height.

## IF 731 IS GO

The Sat-value bound is paid. Same as 729 for 733's third hypothesis.

**Move A:** if 731 is NO-GO because Sat sits one successor above envSet, that is a presentation fact. Rewrite 733 to `Lset (sucV γ)` for the Sat slot only.

## IF 732 IS GO

Completeness holds at the empty instance. 723's `below-closed-via` hyp can sit at those codes. Next generic Completeness is still Bridge 2's production side, not a third packing.

**Move A:** if 732 names the reading FALSE, Completeness is false at those codes. Do not queue a generic Completeness wrap. Re-route.

**Move B:** if 732 STOPS because the hull holds no such codes, that is a hull-alphabet fact. Do not call a vacuous implication GO.

## IF 733 IS GO

The bounded `fill` is paid. `stage-read`'s backward half is then one assembly, priced after 724-SPLIT returns.

**Move A:** if 733 is NO-GO on a hypothesis that 729-731 already refuted, that is expected. Keep the reduction. Do not inhabit `stage-read` from a failed bound.

## STANDING

- 724-SPLIT and 726 are RUNNING. Do not assume either.
- 715-SPLIT-SPLIT stays parked. No fourth landing. Superheavy waits on 43b.
- 728-SPLIT-SPLIT stays empty until swap is below 8192 MB AND a smaller term is named. Not the same composition.
- 719 is the critic's. Do not queue a parallel `soundness-at-SL`.
- Do not fund a sixth ambient-from-coded crossing.
