# LJ-1.173: restrict `envSetK` to a numeral arity, and gate it first

tier: opus (version `override`, set 2026-08-13; the head for every case is in
`scripts/dispatch_policy.py`, which is the only place the tables live)

## GOAL

**`[LJ-1.172]` refuted the supply chain's join and named the cure with its
gate. Run the gate, then apply the cure if it is GO.**

**You have the write scope its brief denied it.**

## THE REFUTATION, and I verified every read

**`envSetK` (`src/L/Condensation/TwelveAgree.lagda.md:271-275`) is FALSE at the
bound `HullStage` gives.** It quantifies over ALL `B ar : S` restricted only by
membership in `K`, and then:

- `Generic.envSetGen B ar` is carved from the **FULL L-power** of a bounding
  stage (`src/L/Coding/EnvSet.lagda.md:441-442`).
- `domAt f d` is an **EQUIVALENCE, not an inclusion**
  (`src/L/Coding/Model.lagda.md:278-280`), so its members are functions with
  domain **exactly** `ar`.

**So the field asks a LEVEL to contain a full L-function space.** Structural
half MEASURED; cardinality half INFERRED, with the witness constructible in
this tree's own vocabulary.

**THE ROOT, and it is one substitution nobody had written down.** Devlin builds
`K(u)` with sequences **and POWER**. This tree substituted a LEVEL, which is
transitive, numeral-holding and pair-closed, **and NOT power-closed.**
**`KFacts`'s four classes survive that substitution. The one class `TFacts`
adds is exactly power.**

## THE CURE, in `[LJ-1.172]`'s own words

> **Restrict `envSetK` to a NUMERAL arity.** Every live use is already numeral,
> and `NumeralFromGeneric.derived` (`src/L/Coding/Sound.lagda.md:300`) already
> proves `envSet B n ≡ envSetGen B (nn n)`. **The numeral case is true and
> reachable by `[LJ-1.172]`'s own step 2**: `src/L/Coding/Key.lagda.md:71-81`
> bounds the whole family at a fixed iterate, uniformly in `n`.
>
> **Its gate is ONE declaration in the already-green `Key.lagda.md`.**

## THE OBLIGATION, and its criterion fixed BEFORE the run (D-1)

**FIRST, gate it.** Write ONE declaration in a probe: the numeral-arity
environment set lands in the level, uniformly in `n`.

- **GO at or below 40 lines.** Then apply the cure.
- **NO-GO above it**: report the figure and STOP. **Do not apply a cure whose
  gate failed.**
- **The numeral case is ALSO false**: **STOP AND SAY SO FIRST.** That would
  mean the level substitution fails outright and the supply needs the fourth
  hypothesis, which `[LJ-1.168]` priced as the surviving fallback.

**Do not move the criterion after you see a number.**

## THEN, AND ONLY ON A GO, APPLY IT

**MEASURED by me: `envSetK` has exactly ONE occurrence in `src/`**, its own
declaration. **So the field has no consumer in the tree today**, and narrowing
it breaks nothing that exists. **Verify that yourself before you edit; my grep
is the kind that has been wrong five times this phase.**

**C-40: typecheck `TwelveAgree` and every consumer.** `[LJ-1.158]` collapsed
those telescopes into records and `make check` is green on them; **your change
touches that record.**

## WHAT THE CURE MUST NOT DO

- **Do not weaken the field to something true because it says nothing.** The
  restricted form must still be what step 6 CONSUMES. **Say what step 6 needs
  and show the restricted form gives it, or say it does not.**
- **Do not add the fourth `HullStage` hypothesis.** That is the fallback and it
  is `[LJ-1.168]`'s route, not this one. **If you reach for it, stop and report
  instead: that is a route decision.**

## THE PATTERN THIS TASK EXISTS BECAUSE OF

**`[LJ-1.172]`'s closing line, and it is the lesson of the whole chain:**

> The three figures were each correct at their own site. **What was wrong was
> the SENTENCE JOINING THEM.** That is twice in one task that the error sat
> between the numbers rather than in one.

**So: when you show the restricted form gives step 6 what it needs, show the
JOIN, not the two ends.**

## WHAT YOU MUST NOT DO

- **Do not touch `src/L/Choice/Name.lagda.md`.** Its drop-in is blocked by DD23
  and the owner has not ruled.
- **Do not touch `src/L/Coding/Graph.lagda.md`** or `[LJ-1.164]`'s move.
- **A probe goes in `agents/tasks/LJ-1-173/`**, never in `src/`, tracked.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised. Fix a
  wall-clock criterion in writing before each run.**
- Never `src/Everything.lagda.md`; **tell me any new module and I wire it.**
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Do not run `make check`; I run it.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**`[LJ-1.172]` measured 207 of 257 built lines naming no L token, and found the
generic form made one argument SHORTER.** **Report the tower-token count of
what you write.**

## ARCHIVE (DD18)

**One archive claim I put in a brief was MEASURED FALSE this phase: the lemma I
offered assumed the bound it appeared to prove.**

- **`archive/src/2026-08-09-rud-route/L/Coding/`**: did the retired route's
  environment set quantify over general arities or numeral ones? **That is
  exactly this question, already answered once.**
- **Take SHAPE, never a claim.** `[LJ-1.11]` ruled that route's condensation
  target classically FALSE.
- `agents/tasks/LJ-1-172/lj-1.172-report.md` sections 13-23, read WHOLE.
- **`dev/LESSONS.md` C-38 as extended, C-40, C-36, D-1, P-l**, read WHOLE.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

`_build/literature/dev2.txt:593-640`. **`[LJ-1.172]` MEASURED that Devlin uses
sequences AND POWER. Say whether his arities are numeral, and whether the
restriction is his form or a departure from it.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-172/lj-1.172-report.md` sections 13-23 FIRST, then
`src/L/Coding/Key.lagda.md:60-90`, then `src/L/Coding/Sound.lagda.md:290-310`.

## SCOPE (write)

`agents/tasks/LJ-1-173/` for the probe and report, **and on a GO,
`src/L/Condensation/TwelveAgree.lagda.md` and `src/L/Coding/Key.lagda.md`.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.

- **D-1, C-38 as extended, C-40, C-35, C-36, C-12, C-22, C-39.**
- **DD8, P-l, P-i, P-y. D-10, D-26, D-29, D-30.**
- **C-31, C-32, C-33, C-34, C-37. I-5.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check`, `scripts/lint-agda.py --check` and
  **`scripts/check-unbound-hyp.py`, which stands at 2.**
- DD23 freezes mathematical prose. **Code comments are not prose; write them.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with GO or NO-GO on the gate and the count.** Then, on a GO, whether the
restricted field still gives step 6 what it needs, shown at the JOIN. Then
every consumer's verdict. Then the checker counts. Then the DD4 answer. **Mark
every negative MEASURED or INFERRED.**
