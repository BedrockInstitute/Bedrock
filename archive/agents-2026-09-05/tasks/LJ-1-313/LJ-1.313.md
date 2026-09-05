# LJ-1.313: Fable 5 review of `[LJ-1.312]`'s refutation of the composite's type

tier: fable (in-harness-subagent-mode), run in-harness because `fable` has no
entry in `HARNESS_FOR_AGENT` and `dispatch.py` cannot start it. **DD17's
EMERGENCY BREAKTHROUGH TIER, and its trigger is named here as that rule
requires.**

**THE TRIGGER.** `[LJ-1.312]` returned REFUTED with a machine witness: the
composite's type is wrong, so `[LJ-1.7]`'s only route is built on a formula
that does not say what the route needs. **That is a point where the loop cannot
advance until the verdict is settled**, and DD17's emergency clause is written
for exactly that.

**THE AUTHORIZATION.** The owner authorized Fable 5 for THIS review on
2026-08-15, by name, because the heaviest route deserves the heaviest check.
**DD0: a one-off owner instruction is never a standing head choice, and this
brief does not make one.** The last time this project took an exception's head
without its conditions, four adversarial reviews went to fable on one old
instruction and the checker passed all four, because `fable` is a legal token.

**DD17's INVARIANT HOLDS:** `[LJ-1.312]` was authored in-harness by opus, and
fable is a different head. **The critic is not the author.**

## WHAT IT CLAIMS

**`φ₀`'s two free slots are the graph's ORDINAL and the graph's machinery
BOUND. `q'` needs the VALUE and the ORDINAL. So `[LJ-1.302]`'s `Composite`
carries a wrong type.**

**The machine witness**, `agents/tasks/LJ-1-312/ProbeLJ1312C.agda:39`, exit 42:

```agda
delivered-is-cured : V.levelHoodB ≡ C.levelHoodB
delivered-is-cured = refl
-- error: [UnequalTerms] zero != suc zero of type Fin (suc (suc n))
```

## ATTACK 1: THE REFUSAL PROVES A DIFFERENCE, NOT A DEFECT

**This is the logical hole and it is the first thing to close or open.**

**`V ≢ C` proves the verbatim copy and the cured copy DIFFER. It does not prove
that `V` is WRONG and `C` is RIGHT.** A refusal is symmetric. **The whole
refutation therefore rests on a SEPARATE argument that `C` meets the
specification and `V` does not**, and that argument is:

- **the role measurements** at `ProbeLJ1312A.agda:340-397`, and
- **Devlin's shape** at `dev/literature/devlin-II5.md:95-96`.

**AUDIT THAT BRIDGE, not the refusal.** **If the bridge holds, the refutation
is sound and you say so plainly. If it does not, the project was one step from
editing a correct formula.**

## ATTACK 2: LINK 4 IS A FOUR-HOP READING AND EVERYTHING RESTS ON IT

**`[LJ-1.310]` called the role identification its own WEAKEST JOINT.
`[LJ-1.312]` claims to have settled it inside `src/` by this chain:**

1. `GraphB (w b K)` at `src/L/Condensation.lagda.md:2483-2487` feeds
2. `StepB (v b f K)` at `:2389-2390`, and
3. `stepBndAt = extAtB v K witB` at `:2415`, where
4. `extAtB y K φ = ∀̇∈ (var y) φ ∧̇ ...` at `:100-102` makes `y` the VALUE, and
   `bodyB`'s first conjunct at `:2403` makes `b` the ORDINAL.

**FOUR HOPS, EACH A READING.** **Check every hop at `file:line`.** **If ONE hop
is wrong, the refutation collapses and the delivered formula may be right.**

**And note what makes this hard to trust: `src/L/BoundedSubset.lagda.md:70-72`'s
COMMENT names the slots one position off the syntax, and every reader for
months took the comment.** **`[LJ-1.312]` says the comments at `:847` and `:854`
also disagree with each other.** **So this file's comments are known unreliable
and you must read only syntax.**

## ATTACK 3: THE SWEEP THE TASK DID NOT DO, and this is where I expect a hit

**`[LJ-1.312]` marks this INFERRED in its own words:**

> the shape does not extend past `LevelHood`, `LevelHood0` and `[LJ-1.52]`'s
> archived probe (**I did not audit `StepAtB` or `SatGraphB`**)

**C-42 is the law: a refutation measures the site it names.** **It found THREE
sites and swept none of the tree.**

**THE PRIOR SHOULD BE THAT MORE EXIST.** `[LJ-1.312]` reports that
`[LJ-1.52]`'s `GraphAgree` at
`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:45-53` is **off by one in BOTH
arguments**, and survived because it is a `Type` and never a term, so nothing
ever checked it. **A defect that hid for months in one place hides in others.**

**AUDIT `StepAtB` and `SatGraphB` AT LEAST.** **If the shape extends, the「two
lines」cure is wrong and the price is not 17 seconds.** **That is the finding
that would change what the project does next.**

## ATTACK 4: THE BLAST RADIUS IS A GREP

**`[LJ-1.312]` claims「nothing in `src/` breaks. MEASURED by grep」**, resting
on: `GraphB` has one application in `src/`; `LevelHood` has one; `LevelHood0`
has no consumer; `L.BoundedSubset` has no importer except
`src/Everything.lagda.md:383`.

**C-40: verify the CONSUMERS of a changed file, never the file alone.** **A
grep finds a NAME. It does not find a consumer that reaches the same object
through a re-export, an `open ... public`, a module alias or a record field.**
**Check for those specifically.** **`L.BoundedSubset` having no importer but
`Everything` is a strong claim about a file the route needs; if it is right,
say so with the evidence.**

## ATTACK 5: A WRONG TYPE IS NOT A FALSE STATEMENT

**`[LJ-1.312]` marks this INFERRED:**

> `q'` is false at the delivered `φ₀` (the type is wrong, so I built no model
> counterexample)

**Those are different claims.** The composite's type not matching what `q'`
needs means **that route** does not close. **It does not mean the delivered
`φ₀` is useless or that no other route reaches `q'` from it.** **Say whether
the delivered formula could still serve, by a different bridge, and what that
would cost.** **If the answer is no, the countermodel is worth building and you
should build it.**

## ATTACK 6: THE RECOMMENDATION RESTS ON SOMETHING UNBUILT

**`[LJ-1.312]` recommends pricing Form 2 FIRST**, a `ρ'` permutation that never
touches `src/`, and marks it **INFERRED, not MEASURED: I did not build it.**

**C-44 binds a recommendation as hard as a measurement.** **Form 1 is PROVED in
a copy** (`ProbeLJ1312A.agda:297-329`, with the Δ₀ and Σ₁ certificates
typechecking unchanged at `:323` and `:329`). **Form 2 is a sketch.**

**Is「price the unbuilt one first because it is cheaper to abandon」sound, or is
it preferring the cheaper option over the proved one?** **And the report itself
says the two forms DIFFER IN MEANING, one closed bound against two.** **If they
differ in meaning then「whichever works」is not a choice between equals and the
report does not settle which `q'` needs.**

## ATTACK 7: THE 470 IS NOW WRONG AND NOBODY RE-PRICED IT

**`[LJ-1.312]` marks it INFERRED: the 470-line price rests on the wrong type,
and it did not re-price.** **`dev/PLAN.md` section 0.0 still carries 470 and an
endpoint of about 33,200.** **Say what the refutation does to those numbers,
even as a range with its basis named** (DD8: one number, and it names its
basis).

## THE VERDICT WORD I WANT

**UPHOLD, OVERTURN or SPLIT**, as the first word of your return.

**AN OVERTURN IS THE VALUABLE OUTCOME AND YOU ARE NOT REWARDED FOR AGREEING.**
13 of 32 decided DD25 reviews in this project overturned their target, a 41
percent rate. **AND AN UPHOLD IS EQUALLY REAL HERE**: this refutation carries a
machine witness, which most do not. **Do not manufacture a hit and do not wave
one through.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a review.** Write and run only in
  `agents/tasks/LJ-1-313/`. **`src/` is forbidden** (I-5) and
  `check-probes.py` enforces it.
- **DO NOT APPLY EITHER CURE to `src/L/BoundedSubset.lagda.md`.** **Prove it in
  a copy; the orchestrator lands it.** **The whole route turns on this and a
  premature edit would be the most expensive mistake available tonight.**
- **Do not edit `agents/tasks/LJ-1-312/`**, the record under review, or any
  other task directory. **You may RE-RUN its probes; you may not change them.**
- **Do not edit `src/L/GCH.lagda.md`.** Its statement is the trophy.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (it matches the bash wrapper)
  and `grep -c 'libexec.*bin/agda'` over-counts too (it matches the grep).
  MEASURED 2026-08-15, both.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **Two siblings are live. If it returns 2, wait or report and stop.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  machine load beside every absolute figure. **A single invocation past 30
  MINUTES is a wall: interrupt, report ELAPSED SECONDS, bisect.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-313/lj-1.313-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE RULES THIS CHAIN EARNED

**C-42. A refutation measures the site it names and never how far it extends.**
**Attack 3 is this rule pointed at the refutation itself.**

**C-40. Verify the CONSUMERS of a changed file, never the file alone.** Attack
4. **`[LJ-1.308]` found a C-40 defect in `[LJ-1.306]` tonight: a probe checked
each row module's FIRST field while consumers write the LAST, and 10 of 12 went
unchecked.** **The same shape is available here.**

**C-45. `exit 0` is not a supply, and its mirror binds harder: a successful
typecheck of an ASSUMED object proves nothing about that object.**
**`[LJ-1.302]`'s `Composite` typechecked for weeks with `comp` a module
PARAMETER. That is exactly how a wrong type survives.**

**C-44. A brief's claim is a measurement until you check it**, and that binds
`[LJ-1.312]`'s numbers AND every claim in this brief. **Re-derive them.**

**C-36. A failed substitution is not a proof of impossibility.** Attack 5.

**D-10. Price the TRUTH of a recorded residue before pricing its proof.**

**C-50. Profile before you cure.** The 17-second re-check price is a
COMPARABLE, and `[LJ-1.312]` says so itself under P-l. **Check that honesty
held.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. **`[LJ-1.312]` says the cure touches neither end
today, citing `dev/ledger.toml:2749-2751`, and that `L/BoundedSubset` is
GCH-bound and AC-free.** **VERIFY it.** **And apply the ledger's own
qualification at `dev/ledger.toml:204`: the GCH closure is read from a STATEMENT
whose proof is not wired, so it UNDERSTATES, and `q'` is precisely the route
that would pull `levelHoodB` inside.** **So a file outside both closures TODAY
may be inside one tomorrow, and a DD4 answer that ignores that is on the wrong
timescale.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-312/lj-1.312-report.md`, read WHOLE.** The target.
- **`agents/tasks/LJ-1-310/lj-1.310-report.md` section 7**, the reading that
  raised the candidate, so you can see what was inferred before it was measured.
- **`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:45-53`**, the archived probe
  said to be off by one in BOTH arguments. **Check that claim; it is the
  evidence that the defect hides well.**
- **`agents/tasks/LJ-1-302/ProbeLJ1302A.agda:72-75`**, the `Composite` under
  refutation.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route crossed at the class carrier with `q` as a syntactic identity,
  and `[LJ-1.293]` refuted `q` by machine. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:88-116`, and it is LOAD-BEARING here rather
than decorative.** `[LJ-1.312]` reads Devlin's clause (a) as Φ(z, v, γ) with
`∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`: three slots, (a) closes ONE at position 0,
and the free pair `v` at 1 and `γ` at 2 are VALUE and ORDINAL. **It then claims
Bedrock copies (a) exactly at `src/L/BoundedSubset.lagda.md:142-143`, so
Devlin's shape IS the specification and the delivered formula fails it.**
**VERIFY that reading against the digest, and say whether the digest is faithful
enough to carry this weight or whether the primary text is needed.** Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-312/lj-1.312-report.md` FIRST, whole. Then
`src/L/BoundedSubset.lagda.md:100-115` and `:840-860`, **the syntax and NOT the
comments around it.**

## SCOPE (write)

`agents/tasks/LJ-1-313/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **C-42, C-40, C-45, C-44, C-36, C-50, D-10.** Named above with what each
  attacks.
- **C-12.** Two Agda processes, counted with the command above.
- **C-22, C-32, C-38, C-39, C-49.** I-5. **P-k, P-l, P-m, P-y, D-1, D-26.**
- **DD0, DD4, DD8, DD13, DD17, DD18, DD23, DD24, DD25.**

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then attack 1: whether the
bridge from「V and C differ」to「V is wrong」holds, which is the whole
refutation. Then each of link 4's four hops, VERIFIED or REFUTED at `file:line`.
Then `StepAtB` and `SatGraphB`, audited, and any fourth site. Then the blast
radius re-checked for re-exports and aliases. Then whether a wrong type makes
`q'` false or only makes this route fail. Then Form 1 against Form 2, and which
one `q'` actually needs. Then what the refutation does to PLAN 0.0's 470 and its
33,200. **Mark every negative MEASURED or INFERRED.**
