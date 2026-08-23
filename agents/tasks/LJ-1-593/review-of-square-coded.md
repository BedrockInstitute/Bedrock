# [LJ-1.593] stop: `square-coded` is not inhabited, and it is B9

## THE STOP

**`square-coded` IS NOT INHABITED.** No term of
`agents/tasks/LJ-1-593/Probe593.agda` carries that name. The probe is GREEN and
carries no hole and no postulate, so every reduction in it is a measurement and
not a claim (`agents/tasks/LJ-1-593/runs/final-3.out:22`, `EXIT=0`).

**THIS IS NOT THE SAME STOP AS THE TWO BEFORE IT, AND THE DIFFERENCE IS THE
WHOLE DELIVERABLE.**

- `[LJ-1.556]` stopped because the type was under-hypothesized: it lacked an
  induction hypothesis (`agents/tasks/LJ-1-556/Probe556.agda:340-352`).
- `[LJ-1.581]` stopped because the type was FALSE at κ := 2
  (`agents/tasks/LJ-1-581/Probe581.agda:376`).
- **This task stops because ONE ROW OF THE CAMPAIGN'S OWN BILL IS UNPAID, and
  that row is B9.** Nothing else is missing.

## WHAT IS NO LONGER OPEN

Three things the two earlier stops left open are closed here, each by a term.

**1. THE AMBIENT SQUARE LAW AT THIS SPELLING IS FREE, AND `IsCardinalL` IS NOT
EVEN SPENT.** `ambient-square` (`Probe593.agda:144-147`). The band parameter of
`L.SquareLawClosed` is a MODULE parameter
(`src/L/SquareLawClosed.lagda.md:19-20`), so a caller that wants the law AT κ
instantiates the band AT κ, and `self∈sucV` (`src/V/Model.lagda.md:236-237`)
discharges the band membership with nothing.

**SO `[LJ-1.556]`'s FINDING DOES NOT BIND THIS OBLIGATION.** Its section 4 said
the tree's route needs "THE SQUARE LAW AT EVERY SMALLER INFINITE ORDINAL"
(`agents/tasks/LJ-1-556/Probe556.agda:344-345`). `sq-trunc-closed`
(`src/L/SquareLawClosed.lagda.md:325-328`) is an `∈-induction` and it takes no
induction hypothesis from its caller: `src/` has already paid it.

**2. THE PAIRS INJECT INTO κ, AMBIENTLY, AT EXACTLY THE THREE HYPOTHESES.**
`pairs-inject-ambiently` (`Probe593.agda:279-283`), built from
`[LJ-1.556]`'s two readings (`Probe556.agda:180-184`, `:206-208`). **So nothing
about the SIZE of the domain is open.** What was open was one thing: a CODE.

**3. AND THE CODE IS B9 AT κ.** `square-from-b9`
(`Probe593.agda:532-533`) and `square-from-b9inf` (`:521-530`). Three steps and
no recursion:

| step | what | from |
|---|---|---|
| (a) | κ is successor-closed | `Stage.succ-closed`, `Probe593.agda:443`; uses `shift-coded`, `src/L/CodedShift.lagda.md:37-40` |
| (b) | the pairs lie inside `Lset κ` | `Stage.pairs⊆stage`, `Probe593.agda:483`; uses `Bound.prʟ∈λ`, `src/L/Coding/Bound.lagda.md:142-144` |
| (c) | inclusion, then B9 | `inclusion-coded` and `injl-trans`, `Probe593.agda:417-427`; both from `src/L/InjChain.lagda.md:575-598` and `:314-434` |

## THE PRICE THIS CORRECTS

**`[LJ-1.552]`'s REVIEW PRICED THE CODED SQUARE LAW AS "a chapter and not a
task"** (`agents/tasks/LJ-1-552/review-of-succ-assignment.md:185-192`), and the
brief calls it "THE LARGEST OBJECT LEFT ON THE BILL". **Measured: it is neither.
On top of B9 it is 84 lines of Agda**, and they are written and green in
`Probe593.agda:374-535`, section 8. With comments that section is 162 lines.
The count is `Probe593.agda:374-535`, non-blank lines that are not a comment.

**AND THE REDUCTION DOES NOT EVEN SPEND THE AMBIENT SQUARE LAW.**
`square-from-b9inf` (`Probe593.agda:521`) calls `injl-trans`,
`inclusion-coded` and `Stage.pairs⊆stage`, and none of the three reaches
`ambient-square`. Results 1 and 2 above are measurements of what the
obstruction is NOT; the route uses neither.

**AND IT IS NOT AN INDEPENDENT SITE OF THE CODING WALL.** The probe's section 7
writes the wall as one type, `CodeShape` (`Probe593.agda:301`), and
instantiates it at the four pairs the tree names. Site 3, the square, is site 2,
the stage count. So the wall has **one paid site and two open sites, not
three**.

## WHAT WOULD REOPEN THIS

**ONE THING, AND IT IS ALREADY A ROW OF THE BILL.** B9 at an infinite
L-cardinal: `B9Inf` (`Probe593.agda:511-514`), which is
`StageCountedCoded` (`agents/tasks/LJ-1-564/Probe564.agda:127-130`) narrowed by
`IsCardinalL δ` and the ω clause. `b9-pays-b9inf` (`Probe593.agda:517-518`)
shows the bill's own row pays the narrowed one, so no restatement is needed
anywhere.

**DO NOT FUND THE SQUARE LAW AGAIN.** A fourth dispatch on this object buys
nothing that is not in this file. Fund B9, and the square law is a corollary
already written.

## WHAT I DID NOT CLAIM

**I DID NOT PROVE B9 FROM THE SQUARE LAW, AND I DO NOT CLAIM THE TWO ARE
EQUIVALENT.** The reduction runs one way only, and the probe carries no term in
the other direction.

**I DID NOT ASSERT B9.** It is a hypothesis of `square-from-b9` and
`square-from-b9inf` and of nothing else. `[LJ-1.533]` is B9's NO-GO and its
finding 1 says the type as the bill writes it is FALSE for want of infinitude
(`agents/tasks/LJ-1-533/lj-1.533-report.md:26-28`); that is why the derivation
spends `B9Inf` and not `B9`.

**I DID NOT ATTEMPT ROW 5.** AD12 gives this brief one obligation.
