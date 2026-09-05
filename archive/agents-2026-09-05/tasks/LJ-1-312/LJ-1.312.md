# LJ-1.312: settle `φ₀`'s slot roles by machine

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE CLAIM UNDER TEST, and it is the highest-stakes open question on the board

**`[LJ-1.310]` returned a REFUTATION CANDIDATE for the composite's type, marked
INFERRED, from a reading with no Agda. In its words:**

> `φ₀`'s two free slots are NOT the value and the ordinal. They are the
> **ordinal and the bound**; the value is closed away by `closeN 14`.
>
> So `φ₀(a,b)` says「the level at ordinal `a` exists inside bound `b`」, while
> `q'` asks for「`a` is the level at ordinal `b`」. **Empty set and a limit
> refute it.**

**IF THAT IS TRUE, the composite's type is wrong**, and with it `[LJ-1.302]`'s
`Composite`, the `q'` route, and the 470-line price in `dev/PLAN.md` section
0.0. **`[LJ-1.7]`'s only route runs through this.**

**IF IT IS FALSE, the route is clear and the project stops worrying.** **Either
answer is worth this slot. Do not prefer one.**

## THE DERIVATION TO CHECK, step by step, and every link is a reading

**`[LJ-1.310]` derived it as follows. Re-derive each link at `file:line` and
mark each VERIFIED or REFUTED.**

1. **`∃̇∈` binds at slot 0**, `src/FOL/Semantics.lagda.md:103`.
2. **So `levelHoodB`'s body environment is `x ∷ w ∷ v ∷ γ ∷ K ∷ δ`.**
3. **`GraphB`'s arguments at `src/L/BoundedSubset.lagda.md:105` are slots 0, 2
   and 3**, that is `x`, `v`, `γ`.
4. **`GraphB`'s parameter roles are (value, ordinal, bound)**, MEASURED slot for
   slot against `agents/tasks/LJ-1-238/GenSequence.agda:166-167`. **`[LJ-1.310]`
   calls this its own WEAKEST JOINT and still marks it INFERRED. It is
   therefore the first thing to settle.**
5. **The `≐` at `src/L/BoundedSubset.lagda.md:111` is `w ≐ x`.**
6. **So value is `w` at slot 0, ordinal is `v` at slot 1, bound is `γ` at slot
   2.**
7. **`ρ` sends slots 1 and 2 to 14 and 15**,
   `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-111`.
8. **`closeN 14` closes slots 0 to 13**, so the surviving free pair is (ordinal,
   bound) and never (value, ordinal).

## THE SECOND ANOMALY, and it is independent evidence

**`[LJ-1.310]` reports that `levelHoodB` bounds its WITNESS by slot 3 (`K`) and
its MACHINERY by slot 2 (`γ`).** **Two different bounds in one formula is not a
design.** **Check it.** If it is real it corroborates the off-by-one
independently of the slot census, and `[LJ-1.310]` prices the cure at **two
lines**, at `src/L/BoundedSubset.lagda.md:105` and `:111`.

## WHY NOBODY CAUGHT IT, and this tells you what NOT to trust

**`[LJ-1.310]` gives three reasons, all MEASURED by reading:**

- **`agents/tasks/LJ-1-241/ProbeLJ1241B.agda:120-133` measured the free-variable
  SET and the tag ORDER, never the slot ROLES.** **So the existing probe does
  not settle this and you must not cite it as if it did.**
- **`[LJ-1.52]` dropped the `≐` half and routed through `ride-only` at the outer
  slot**, `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:61-73`.
- **`src/L/BoundedSubset.lagda.md:70-72`'s COMMENT names the slots one position
  off the syntax, and every later reader took the comment.** **DO NOT READ THAT
  COMMENT AS EVIDENCE. Read the syntax.**

## WHAT TO BUILD, and `[LJ-1.310]` named both forms with prices

**FORM A, the cheap census, about 25 lines, INFERRED price.** A slot census in
`ProbeLJ1241B.agda`'s own style: two `refl`s that pin what each slot IS at a
concrete environment.

**FORM B, the better buy, about 60 lines, INFERRED price.** **Copy `LevelHood`
twice into your probe, once VERBATIM and once CURED, and state the slot roles at
a concrete environment.** **If the verbatim copy refuses, the off-by-one is
MEASURED and the cure is priced in the same run.**

**BUY FORM B unless you find a cheaper decisive shape.** **A census that only
confirms a reading is weaker than a copy that refuses to typecheck.** **If you
find something cheaper AND decisive, take it and say why.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE OFF-BY-ONE IS REAL.** **Report it at `file:line`, with the term that
  refuses.** Then price the two-line cure and say what it breaks downstream.
  **This is a route-level refutation and the project must hear it immediately.**
  STOP.
- **THE OFF-BY-ONE IS NOT REAL.** **Say which link of the eight fails and
  why.** Then `[LJ-1.302]`'s `Composite` stands and the route is clear. **That
  is an equally good outcome. Do not manufacture a refutation.**
- **THE ROLES ARE NOT DECIDABLE FROM THE SYNTAX ALONE.** Then say what would
  decide them and what it costs.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report the ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## COUNTING THE AGDA SLOTS, and two obvious commands are both wrong

**C-12 caps this machine at TWO concurrent Agda processes.** **`ps aux | grep -c
'[a]gda '` OVER-COUNTS** (it matches the `/bin/bash -c` wrapper) and **`grep -c
'libexec.*bin/agda'` over-counts too** (it matches the grep itself). **MEASURED
2026-08-15, both.** Use:

```sh
ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
```

**One sibling (`[LJ-1.305]`) holds a slot and another (`[LJ-1.311]`) may take
one. Run the count before every `agda` invocation. If it returns 2, wait or
report and stop.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. THIS IS A PROBE.** Write and run only in
  `agents/tasks/LJ-1-312/`. **`src/` is forbidden** (I-5) and
  `check-probes.py` enforces it.
- **DO NOT APPLY THE TWO-LINE CURE to `src/L/BoundedSubset.lagda.md`**, however
  obvious it looks. **Prove it in a copy; I land it.**
- **Do not edit `src/L/GCH.lagda.md`.** Its statement is the trophy.
- Do not touch another task directory.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  machine load beside every absolute figure.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-312/lj-1.312-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## PREMISES

- **The eight links above are `[LJ-1.310]`'s, from a reading with NO Agda.**
  **Every one is a hypothesis until your machine says otherwise** (C-44).
- **`φ₀ = closeN 14 (pins ∧̇ renamed)`**,
  `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:145-146`, arity two.
- **`[LJ-1.302]`'s `Composite` typechecks with `comp` as a MODULE PARAMETER**,
  `agents/tasks/LJ-1-302/ProbeLJ1302A.agda:72-75`, exit 0. **C-45: a parameter
  is an assumption and never a supply.** **A wrong type can typecheck as a
  parameter forever, which is exactly how this would have survived.**

## THE RULES THIS CHAIN EARNED

**C-36. A failed substitution is not a proof of impossibility**, and its mirror
binds harder here: **a successful typecheck of an ASSUMED object proves
nothing about that object.**

**C-45. `exit 0` is not a supply.** The reason this candidate survived to today.

**D-10. Price the TRUTH of a recorded residue before pricing its proof.** **The
whole 470-line price assumes the composite's type is right. This task prices
that truth, and it should have been priced before the ingredients were.**

**C-44.** Every link above is `[LJ-1.310]`'s reading and you re-derive each one.

**C-42. A refutation measures the site it names.** **If the off-by-one is real
at `levelHoodB`, say whether it extends to any other formula, and do not assume
it does.**

**A STOP IS A DELIVERABLE, and a REFUTATION is this project's best product.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. **`φ₀` and `LevelHood` are FOL and bounded-set
machinery, carrier-free and tower-free**, so a defect there is shared and a cure
there is shared. **Say whether the cure, if there is one, touches the AC end.**
**And note the ledger's own qualification at `dev/ledger.toml:204`: the GCH
closure is read from a STATEMENT whose proof is not wired, so it UNDERSTATES,
and a file outside the closure today can be inside it once `sq` is supplied.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-310/lj-1.310-report.md`, sections 7 and 13, read WHOLE.**
  The derivation under test.
- **`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`**, which dropped the `≐`
  half. **`[LJ-1.310]` says that is why the shape survived; check it.**
- **`agents/tasks/LJ-1-241/ProbeLJ1241B.agda:120-133`**, which measured the
  free-variable set and NOT the roles. **Read it to see exactly what it did
  measure, so you do not repeat it.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route crossed at the class carrier with `q` as a syntactic identity,
  and `[LJ-1.293]` refuted `q` by machine. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:88-116`.** **`[LJ-1.310]` reports Devlin's
clause (a) at `:95-96` closes ONE slot, `z`, and leaves `v` and `γ` free in
exactly the roles the conclusion uses, while Bedrock closes fourteen.** **VERIFY
that reading.** **If Devlin's formula leaves the roles the conclusion needs, his
shape is the specification our `φ₀` should meet**, and that is the strongest
outside check available. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-310/lj-1.310-report.md` section 7 FIRST, whole. Then
`src/L/BoundedSubset.lagda.md:100-115`, the syntax and NOT the comment above it.

## SCOPE (write)

`agents/tasks/LJ-1-312/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The abort criterion is fixed above.
- **D-10, C-45, C-44, C-36, C-42.** Named above with what each governs.
- **C-12.** Two Agda processes, counted with the command above.
- **C-22, C-32, C-38, C-39, C-40, C-49, C-50.** I-5. **P-k, P-l, P-m, D-26.**
- **DD0, DD4, DD8, DD18, DD23, DD24.**

## RETURN

**Lead with ONE word: REFUTED, STANDS or UNDECIDED**, where REFUTED means
`[LJ-1.310]`'s off-by-one is REAL and the composite's type is wrong. Then the
term that refuses, or the link of the eight that fails. Then each of the eight
links VERIFIED or REFUTED at `file:line`. Then the second anomaly, the two
bounds. Then, if the off-by-one is real, the two-line cure proved in a copy and
what it breaks downstream. Then the Devlin reading. **Mark every negative
MEASURED or INFERRED.**
