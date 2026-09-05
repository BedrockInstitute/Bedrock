# The decision tree, written BEFORE the returns

**Clause: know your next move for each outcome before the return arrives.** This
file is that, for the six tasks in flight on 2026-08-26. It is my own working
note, not a brief. Written so a later session acts instead of re-deriving.

## THE BOARD

| code | obligation | state at writing |
|---|---|---|
| 645 | can the chapter take the CODED cardinal | RUNNING |
| 646 | **`lset-code-ord`, the keystone** | RUNNING |
| 647 | step 2 `HullClosedLset`, keystone as hypothesis | READY |
| 648 | clause (iii)'s `Commute`, keystone as hypothesis | READY |
| 649 | `levelIn` assembled from four steps | READY |
| 650 | clause (ii)'s `CodedCover`, keystone as hypothesis | READY |

## IF 646 IS GO

The keystone exists. 647, 648 and 650 become unconditional the moment their own
returns land, and 649 says whether three steps suffice.

**Move A, immediately: the certificate assembled.** One brief taking 647's step 2,
646's step 3 and 648's commute, concluding `Certificate`
(`agents/tasks/LJ-1-578/Probe578.agda:525-534`). `[LJ-1.578]` already proved
`certificate-gives-cohyps` green, so `Certificate` is the last object between the
campaign and `CoHyps`.

**Move B, beside it: `cover` and `levelIn` into `BoundedSubsetAt`.** Both are
parameters at `src/L/BoundedSubset.lagda.md:1671-1672`. HEAVY tier: `[LJ-1.598]`
measured that any frame importing the certificate sits above the wide cap.

**Move C: the at-`ω` half end to end.** With `levelIn` and `cover` supplied and
`sq` free at ambient `ω` (`param-at-ω`), the surviving debts are `cardκ` (645)
and `absorbs`. That is CH in L, the trophy's most important single instance.

## IF 646 IS NO-GO

It found a THIRD obstacle `[LJ-1.462]` did not name. 647, 648 and 650 still
return their reductions, so the map is bought.

**Move A: attack the third obstacle directly**, with 646's own statement of it.
**Move B: re-price the certificate from what 647, 648 and 650 report.** If all
three still reduce to the keystone, the certificate has ONE debt and its size is
646's answer. If any reduces to something else, that something is a fourth clause
and `[LJ-1.578]`'s three-clause decomposition is wrong.

## IF 649 IS NO-GO, WHICHEVER WAY 646 GOES

**That is the most valuable single outcome on the board.** It means `levelIn` needs
a FIFTH step that four hundred dispatches have not named. Everything above changes,
and the first brief after it states that step as a type.

## IF 645 IS GO

The bill feeds its own chapter and the above-`ω` half's blocker dissolves.
Then the above-`ω` half owes conjunct 4 through `c4-from-min`
(`agents/tasks/LJ-1-638/Probe638.agda:212`), whose minimality input `[LJ-1.640]`
tied to ambient cardinality: with 645 that tie is no longer a loop.

## IF 645 IS NO-GO

It names which of the two injections at `src/L/BoundedSubset.lagda.md:1713,1717`
has no code. **Then the ruling is mine and I make it rather than queue around it:**
either the bill's clause is restated to carry ambient cardinality, or the above-`ω`
half is declared blocked and reported to the owner as a stop. I will not queue a
sixth attack on the ambient-from-coded crossing; `[LJ-1.533]` measured it,
`[LJ-1.615]` was shelved on it, and `[LJ-1.644]` refuted the detour.

## STANDING, WHATEVER HAPPENS

- **`absorbs` is genuinely open and has no obvious supplier.** I traced it this
  turn: `src/L/Absorption.lagda.md:635` proves a DIFFERENT object (`sucV γ ↪ γ`),
  and `L.BoundedSubset` does not import `L.Absorption` at all. Recorded so the
  next trace does not repeat it.
- **`lset-code` at a NON-ordinal code stays unbuilt and unasked.** 646 restricts to
  ordinal codes because every consumer has ordinality. If a consumer ever appears
  without it, that is a new object and not a repair of 646.

## A CONVERGENCE I HUNTED AND DID NOT FIND, RECORDED SO IT IS NOT RE-RUN

**The hypothesis.** `[LJ-1.607]` called the untruncation futile because it "is not
a way around the square law but the square law under another type".
`[LJ-1.636]` then delivered `param-at-ω : SqParam ω`. So: is the untruncation
inhabited at ambient `ω`?

**NO, AND THE ARROW IS WHY.** `the-circle : Untruncation → SqParam α₀`
(`agents/tasks/LJ-1-607/Probe607.agda:228-229`) runs untruncation TO square law.
Having `SqParam ω` does not give the untruncation: `A → B` with `B` inhabited
says nothing about `A`. I checked the direction before writing a brief, the same
check that stopped `[LJ-1.640]`'s `readL` from going backwards.

**What IS true, and it is smaller than it looks.** `[LJ-1.607]`'s reason for
calling the route futile was that the untruncation costs you the square law you
were trying to get. At ambient `ω` that cost is now zero. So the FUTILITY
argument does not bite at `ω`, even though the untruncation is still not
inhabited there. The real remaining gap is the one `[LJ-1.607]` named at
`Probe607.agda:231-239`: a BRIDGE from the ambient truncated pairing to the coded
truncated existence, "the piece no instance has". That is ambient-to-coded,
`[LJ-1.533]`'s measured direction, so it stays blocked.

**Do not re-run this trace.** The next thing that would change it is a bridge, not
a square law.
