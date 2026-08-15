# LJ-1.308: DD25 review of `[LJ-1.306]`, the zero-changed port of the clean 23

tier: opus (in-harness-subagent-mode), **and this departs from the table on
purpose.** I ran `scripts/dispatch/dispatch_policy.py` before writing this
line. Today's **adversarial row is `herdr` / `pi` / `glm-5.3`**, and `pi` on
`glm-5.3` WROTE the target. **DD17's invariant is that the critic is never the
same head as the author, and the skill states it is not negotiable.** So the
critic takes the in-harness head, which is today's DEFAULT row. **This is a
consequence of the evening mode flip that nobody priced: every task authored
before the flip was authored by the head that the flip made adversarial.**

## WHY THIS REVIEW EXISTS

**DD25. `[LJ-1.306]`'s return refuted a load-bearing premise of its own brief
and then cured it in the same run.** The brief handed it **23 clean modules**.
The return says **five of the 23 are NOT clean**: `TmAgree`, `BinFormAgree`,
`UnFormAgree`, `ShapesAgree` and `ShapedAgree` name committed `L.Coding.Shape`
deliveries in their types. **A premise refuted and self-healed inside one run
is the case nobody checks, because the row reads like a success.**

**AND THE STAKE IS THE LARGEST OPEN NUMBER IN THE PROJECT.** This port is wave
1 of `q`'s route. `[LJ-1.298]` priced **about 180 new lines placing about 6,900
existing ones**. If the zero-changed rate is real at scale, that is the single
biggest compression on the board. **If it is real only under a measurement that
does not mean what it says, the project funds waves 2 and 3 on a false price.**

## WHAT TO ATTACK, in descending order of what it would cost to be wrong

**1. THE SENTENCE I TRUST LEAST, and attack it first.** The return says:

> One genuine finding: on-the-nose proof-term identity fails (stuck
> `lookup-fst` neutrals under a variable `Fin` index) but no consumer writes
> that equation; satisfaction is squashed.

**A failure dismissed because「no consumer needs it」is exactly the shape C-43
names.** **VERIFY THE DISMISSAL, do not verify the failure.** The failure is
admitted. The question is the second clause:

- **Does any consumer write that equation?** Five files consume
  `L.Condensation` from outside and the return names four that reach ported
  names: `LowerAgree` 13 reaches, `UpperAgree` 14, `TwelveAgree` 2, `EnvSupply`
  2. **Check every one of those 31 reaches**, not a sample.
- **Is「satisfaction is squashed」true at each reach?** A squashed target makes
  proof-term identity irrelevant. **An UNSQUASHED one makes it load-bearing.**
  If even one reach lands in an unsquashed position, the dismissal fails and
  the port has a real defect.
- **`KFacts` is named as「the one nominal-record exception, with zero external
  consumers」.** Zero is a checkable number. **Check it.**

**2. THE ZERO.** `0 of 4,738 copied non-blank lines changed`, MEASURED by a
verbatim-run search over `manifest.json`. **Re-derive it independently and by a
different method than the manifest.** The failure mode to hunt: **a
verbatim-run search can report zero changes because nothing changed, or because
the search's notion of a run does not see the change.** Diff the port against
`src/L/Condensation.lagda.md` directly and count.

**3. THE 45-LINE SCAFFOLD.** The return says one scaffold served all 23 and the
abort branch「each module needs its own」is MEASURED FALSE. **Then ask the
question the brief did not: what does「load-bearing」exclude?** 45 non-blank
load-bearing lines against a 4,738-line port is a ratio worth one minute of
suspicion. **Count the whole file's non-blank lines that are neither copied nor
blank, and say whether 45 is the honest number.**

**4. THE C-42 CLAIM.** The return says the 23 sites「retires the C-42 caveat for
the port itself」. **C-42 says a refutation measures the site it names and never
how far it extends, and the same binds a POSITIVE.** The return marks the dirty
seven INFERRED, which is the honest half. **Check that the retirement claim is
scoped to the 23 and does not silently license wave 2.**

**5. THE 180.** Wave 1's hand-written share is 45; the return says the
remaining about 135 belongs to the dirty seven's gaps. **`[LJ-1.302]` measured
ONE dirty module at 51 lines.** Seven at that rate is 357, not 135. **Either
the dirty seven are much cheaper than the one measured, or the 180 does not
stand. SETTLE IT.** This is the arithmetic most likely to be wrong and it
prices the whole route.

## WHAT YOU MUST NOT DO

- **LAND NOTHING.** Write and run only in `agents/tasks/LJ-1-308/`. **`src/` is
  forbidden for probes** (I-5) and `check-probes.py` enforces it.
- **Do not edit `agents/tasks/LJ-1-306/`**, which is the record under review.
- **Do not edit `src/L/Condensation.lagda.md`.**
- **A SIBLING HOLDS ONE AGDA SLOT** (`[LJ-1.305]`). **You may take the second
  and only the second.** ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, **cap
  NEVER raised.** Report the load beside every absolute figure.
- **Create `agents/tasks/LJ-1-308/lj-1.308-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` on what you write.
  **No em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE VERDICT WORD I WANT

**UPHOLD, OVERTURN or SPLIT**, in that vocabulary, as the first word of your
return. A SPLIT names which claims hold and which fall.

**AN OVERTURN IS THE VALUABLE OUTCOME AND YOU ARE NOT REWARDED FOR AGREEING.**
This project's best results came back as refutations. **13 of 32 decided DD25
reviews have overturned their target, a 41 percent rate**, so an overturn here
is ordinary and not an accusation.

## THE RULES THIS CHAIN EARNED

**C-43. An escape hatch is the shape a wrong choice hides in.** 「No consumer
writes that equation」 is that shape until it is checked.

**C-44. A brief's claim is a measurement until you check it**, and that binds
`[LJ-1.306]`'s claims AND mine in this brief. Re-derive every number.

**C-42. A refutation measures the site it names.** Applied to a positive here.

**C-45. `exit 0` is not a supply.** `GenAgree.agda` exiting 0 proves the port
typechecks. It does not prove the port SERVES what the chapter served.

**C-40. Verify the CONSUMERS of a changed file, never the file alone.** This is
attack 1 in one sentence.

**P-l. A judgement at one site is a hypothesis at another.** `[LJ-1.298]`
measured one site; `[LJ-1.306]` claims 23; the dirty seven are a third
population.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). `[LJ-1.306]` named the **L-against-ambient** axis and
said the AC-against-GCH end gains nothing. **DD4's own axis is AC-against-GCH,
fixed in code at `scripts/measure/ledger.py:50`**, and `src/L/Condensation.lagda.md`
sits in NEITHER trophy closure. **Check that both statements are true**, because
a DD4 answer on the wrong axis is the defect `[LJ-1.272]` found in 12 of 62
figures.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-306/lj-1.306-report.md`, read WHOLE.** It is the target.
- **`agents/tasks/LJ-1-298/lj-1.298-report.md`**, the one-site zero-changed
  measurement this port generalises. **Its scope is the thing under review.**
- **`agents/tasks/LJ-1-307/lj-1.307-report.md`**, which says the port is the
  RIGHT move and is therefore a witness FOR the target. **Read it as evidence,
  not as agreement: it answered a DD13 question and never checked the port.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim. The
  retired route's `Condensation` was 885 lines with no `Agree` family at all.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** `[LJ-1.307]` reports Devlin states ZERO
agreement lemmas, so the thirty are the two-dialect port's price and not the
mathematics. **Say in one line whether that holds**, because if Devlin needs no
such family then the deepest question is not how cheaply we port it. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-306/lj-1.306-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-308/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **C-42, C-43, C-44, C-45, C-40.** Named above with what each attacks.
- **C-36.** A failed substitution is not a proof of impossibility.
- **C-12, C-22, C-32, C-39.** I-5.
- **P-l, P-k, P-y, D-1, D-10, D-26.**
- **DD0, DD4, DD8, DD13, DD18, DD24, DD25.**

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then attack 1, the
「no consumer writes that equation」dismissal, with every reach checked and
counted. Then your independent re-derivation of the zero. Then the scaffold's
honest line count. Then whether the C-42 claim is scoped. Then the 180 against
`[LJ-1.302]`'s 51-line dirty module, settled. **Mark every negative MEASURED or
INFERRED.**
