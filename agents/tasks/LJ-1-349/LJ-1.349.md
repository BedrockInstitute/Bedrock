# LJ-1.349: DD25 review of `[LJ-1.348]`'s `witK` refutation

tier: pi (in-harness-subagent-mode), **the switch's ADVERSARIAL row.**
`[LJ-1.348]` was authored in-harness by opus, this mode's DEFAULT row, so the
adversarial row is `herdr` / `pi` / `glm-5.3`. **DD17's invariant holds: the
critic is not the author.**

## WHY THIS EXISTS

**`[LJ-1.348]` returned `witK` MEASURED FALSE with a machine-checked
countermodel.** **DD25 requires a negative return to be adversarially reviewed
immediately.**

**I skipped this gate once already this session** and `make check` caught it
after a repair had already landed in `src/`. **Not twice.** **Nothing has been
landed on this refutation, so this review runs BEFORE any action rather than
after one.**

## THE CLAIM

**Three parts, and each is separately attackable:**

**1. THE COUNTERMODEL.** `agents/tasks/LJ-1-348/Refute348.agda:247-252`, exit 0
in 2.48 s, derives `⊥` from the tie. `:300-325` states `WitnessAgree`'s type at
`src/L/Condensation.lagda.md:6683-6685` and `LeafAgree`'s at `:7233-7235`
**VERBATIM** and discharges both.

**The mechanism:** `shapes` is a twelve-fold disjunction
(`src/L/Coding/Shape.lagda.md:182-187`); its **tag-6 disjunct** binds the
**ARITY** component existentially and pins only the payload; **`closedAt`
speaks about tags 2, 3, 4, 5, 8, 9, 10 and 11 and NEVER about tag 6**
(`src/L/Coding/Model.lagda.md:2182-2195`). **So the bound goes in the free arity
slot and the tie closes a four-step cycle.**

**2. `shapedAt` DOES NOT BLOCK IT.** **This REFUTES `[LJ-1.344]`, which measured
that it does.** **Two agents read the same conjunct and disagree. Settle it.**

**3. THE CURE IS UNPAYABLE.** `MustFail348.agda`, **EXPECTED RED, exit 42**:
`src/L/Condensation.lagda.md:6717` reads `go (w , (hxw , (hcl , hsh))) =` and
`:6721` reads `wK = witK w (hxw , (hcl , hsh))`, so **`w` comes out of an
UNBOUNDED existential and only the three conjuncts are in scope.**
**`[LJ-1.341]`'s load-bearing check gave the OPPOSITE answer at its own site.**

## THE EVIDENCE THAT IS NOT THE AGENT'S, and check it first

**`src/L/Coding/CodeSet.lagda.md:21-27` is DELIVERED PROSE in the chapter that
owns the notion, and it states the hole in English:**

> nothing in `closedAt` or `shapedAt` constrains the arity slot. Shapedness
> binds the arity existentially and puts no condition on it, **so a set holding
> a pair whose first component is not a numeral at all satisfies both halves**,
> and the decode has nothing to say about that pair. **That debt was recorded
> where it was incurred.**

**I read it and it says what the agent says it says.** **So the tree recorded
this hole two chapters away and nobody connected it.** **If the countermodel is
right, that prose is its independent corroboration; if the countermodel is
wrong, the prose describes a DIFFERENT hole and you must say which.**

## WHAT TO ATTACK

**1. THE TAG-6 READING.** **Does `closedAt` really never speak about tag 6?**
**Read all twelve disjuncts and both conjuncts. Count them and name what you
read** (C-57).

**2. NON-VACUITY.** The agent built the premise in three layers and inhabited
its environment hypothesis. **Re-check: if the premise is empty at the witness,
the countermodel refutes nothing.** **`[LJ-1.341]` and `[LJ-1.345]` both
answered this explicitly, and it is the pivot every time.**

**3. THE LIMIT IT STATED ITSELF, and judge whether it is the right limit.**

> The type cannot be empty at EVERY `γ`: where the read slot is no shape, the
> premise is empty and the tie is vacuous. **I proved the strongest true form:
> no term inhabits it at every `γ`, so no supplier exists.**

**Is「no supplier exists」the claim the project needs, or is「false」stronger
than the evidence?** **The row now says MEASURED FALSE. Say whether that word is
right.**

**4. THE CONTRADICTION WITH `[LJ-1.344]`.** **One of the two readings of
`shapedAt` is wrong.** **Name which, at `file:line`.**

**5. `graphWitK`, which it marked INFERRED false and did NOT refute.** It priced
the remaining work at about 120 lines. **Say whether the inference is sound or
whether it should be measured before the project treats it as false.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **UPHOLD.** Then three of six construction ties are false and the family is a
  route-level finding. **Say what that means for the remaining two, which a
  sibling is settling now.**
- **OVERTURN.** **Then `witK` is true or unrefuted, `[LJ-1.344]` was right, and
  the row must change.** **Nothing has been landed on it, so an overturn costs
  the project nothing except the task.**
- **SPLIT.** **The likeliest outcome given the agent's own stated limit**: the
  refutation holds but「MEASURED FALSE」overstates it. **Say the right word.**
- **A WALL.** 30 minutes on one invocation is a wall: interrupt, report ELAPSED
  SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING and REPAIR NOTHING.** Write and run only in
  `agents/tasks/LJ-1-349/`. **`src/` is forbidden** (I-5).
- **`MustFail348.agda` is EXPECTED RED. Do not repair it.**
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-348/`, `LJ-1-344/`, `LJ-1-341/` and `LJ-1-345/`.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-349/lj-1.349-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE VERDICT WORD I WANT

**UPHOLD, OVERTURN or SPLIT**, as the first word of your return.

**AN OVERTURN IS THE VALUABLE OUTCOME AND YOU ARE NOT REWARDED FOR AGREEING.**
**13 of 32 decided DD25 reviews in this project have overturned their target, a
41 percent rate.** **And the sibling review one step back on this same chain
returned UPHOLD after rebuilding its target's countermodel itself rather than
taking the transcription. Hold that standard.**

## THE RULES

**C-45** is this chain's law: `exit 0` is not a supply, and a hypothesis that
typechecks says nothing about its truth.
**C-42**: a refutation measures the site it names. **C-57**: say how many hits
you read and name what you rejected. **C-44, C-36, D-10, P-l, C-53.**
**C-12, C-22, C-32, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD17, DD18, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**`[LJ-1.348]` claims its countermodel is class-free, so `witK` is false at BOTH
carriers by one file, and that what the task removes is「a FALSE line from the
shared side」.** **VERIFY that**, and note `dev/ledger.toml:204`: the GCH closure
is read from a STATEMENT whose proof is not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-348/lj-1.348-report.md`, read WHOLE.** The target, and
  its section 3.4 prices the strengthening it did not build.
- **`agents/tasks/LJ-1-344/lj-1.344-report.md`**, whose `shapedAt` reading this
  contradicts.
- **`agents/tasks/LJ-1-345/lj-1.345-report.md`**, the review that upheld the
  analogous refutation, for the standard.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Devlin binds every unbounded quantifier by
a set built from the members of its argument, confirmed against the primary
source by `[LJ-1.345]`.** **Say in one line whether a witness drawn from an
unbounded existential has any counterpart in his text.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`src/L/Coding/CodeSet.lagda.md:21-27` FIRST: it is the tree's own prose about
this hole and it is the shortest path to judging the claim.

## SCOPE (write)

`agents/tasks/LJ-1-349/` only.

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then the tag-6 reading, with
the twelve disjuncts counted. Then non-vacuity, re-checked. Then whether
「MEASURED FALSE」is the right word for what was proved. Then which of the two
`shapedAt` readings is wrong. Then whether `graphWitK`'s INFERRED verdict should
be measured before it is believed. **Mark every negative MEASURED or INFERRED.**
