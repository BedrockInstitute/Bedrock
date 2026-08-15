# LJ-1.293: discharge `q`, and with it `amb`, the phase's last OPEN parameter

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch_policy.py` before writing this line and took the head it
gave**: `pi-subagent-mode` is IN FORCE, PINNED by the owner 2026-08-15, default
case `herdr` / `pi` / `glm-5.3`.

## GOAL, AND IT IS THE PHASE'S TERMINUS

**`[LJ-1.7]` is LJ-1's blocking row. `[LJ-1.267]` re-derived its seven
parameters: three SUPPLIED, three BUILT, and `amb` OPEN.** Step 6 landed today
and discharged what `sl` and `sc` stood on. **`amb` is the one that is left.**

**`amb` is not open for its own sake. It is open because ONE equation is
relayed and never proved.**

`agents/tasks/LJ-1-184/ProbeLJ1184B.agda:112`, inside `module AmbientStep`:

```agda
(q : Graph {2} zero (suc zero) ≡ embed φ₀)
```

`go` spends it at `:122`:

```agda
go γ h = M.graph-only zero (suc zero) γ
  (subst (λ ψ → ⟨ A.ambient γ ψ ⟩) (sym q) h)
```

**`[LJ-1.243]` searched the repository and found the only application,
`ProbeLJ1184C.agda:83`, feeds `q` from its OWN telescope. So the supply relays
`q` and never discharges it.** That is C-45's exact shape: an assumed equation
between two independently quantified terms, which `refl` cannot close.

**Settle `q`. Is it TRUE, and is it PROVABLE here?**

## PREMISES

- **`q` is `Graph {2} zero (suc zero) ≡ embed φ₀`**, at `ProbeLJ1184B.agda:112`.
  I read the line. RE-READ IT (C-44).
- **Nothing instantiates `AmbientStep`**, measured by `[LJ-1.243]` section 2.2
  with a repository-wide search. **VERIFY, because if something does now, the
  answer may already exist.**
- **`amb`'s type is Devlin's clause (a) at the ambient carrier**, at
  `ProbeLJ1178A.agda:190-192`: ambient believes `φP(v,b)` at an ordinal `b`
  implies `v ≡ Lset b`.
- **`sl`, `sc` and `s₁` are BUILT and `el`, `fwd`, `bwd` are SUPPLIED**, per
  `agents/tasks/LJ-1-267/lj-1.267-report.md:13-19`. **So `amb` really is the
  last one**, and that is why this task exists.

## THE THREE OUTCOMES, and D-10 says price the TRUTH before the proof

**1. `q` IS TRUE AND PROVABLE.** Build the term. Then `amb` is SUPPLIED and
`[LJ-1.7]`'s residue is empty.

**2. `q` IS TRUE AND NOT PROVABLE HERE.** Say what it needs and where that
belongs. **A named obligation is worth more than a vague one.**

**3. `q` IS FALSE.** **That is the most valuable outcome and D-10 is the law:
price the truth of a recorded residue before pricing its proof.** A refutation
here re-prices the phase and stops the project proving something that cannot
hold. **Give a countermodel or the exact term that fails.**

**Do NOT assume outcome 1. `[LJ-1.239]`'s target looked provable and was
measured FALSE, and that refutation was worth more than the build would have
been.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`q` IS PROVED.** Report the term and re-run the consumer that needed it.
  STOP.
- **`q` IS FALSE.** Report the countermodel at `file:line`. STOP. **This is a
  GOOD return and DD25 will send it to an adversarial review, which is the
  process working.**
- **`q` NEEDS SOMETHING UNDELIVERED.** Name it at `file:line` and price it.
- **`embed` OR `Graph` IS NOT WHAT ITS NAME SUGGESTS.** `[LJ-1.243]` found a
  supply that relayed rather than discharged by looking at exactly this kind of
  gap. **Look for it again.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. Report a heap exhaustion as a
  wall and **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-293/`.
  **`src/` is forbidden for probes** (I-5) and `scripts/check-probes.py`
  enforces it.
- **Do not edit any master.** **`src/L/Coding/EnvSupply.lagda.md` was cured
  minutes ago and `src/L/Coding/Key.lagda.md` is being profiled by a sibling.**
- **A SIBLING IS LIVE in `agents/tasks/LJ-1-292/`**, profiling
  `Key.lagda.md`. **Another is live in `agents/tasks/LJ-1-291/`**, editing
  `scripts/`. Touch neither.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- **Create `agents/tasks/LJ-1-293/lj-1.293-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on what you write. **No em dash in any
  language.** DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**C-45. An assumed equation in a telescope is an idiom when `refl` closes it
and a HYPOTHESIS when it does not. AUDIT THE INSTANTIATION, never the
telescope.** **`q` is the law's own example**, and this task is the law applied
to the last parameter.

**C-38 as extended. A hypothesis is discharged when something SUPPLIES it, and
BUILT is not SUPPLIED.** A relay is not a supply.

**D-10. Price the truth of a recorded residue before pricing its proof.**

**C-44.** Every claim in this brief is another report's except the two lines I
read, and you must check each one.

**A STOP IS A DELIVERABLE.** If `q` is false, say so and stop. **Refutations
gave this project its best results, and today's biggest win came from a profile
that refuted three diagnoses including mine.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`amb` is the AMBIENT half of a cross that reads the same formula at two
carriers**, so its tower status is not obvious. **Say whether a proof of `q`
would be reusable at the other carrier or would have to be written twice**, and
**NAME YOUR AXIS** (C-46): `[LJ-1.262]` measured that this phase mixes Devlin's
Def-against-J with the port's L-against-ambient, and DD4's OWN axis is
AC-against-GCH, fixed in code at `scripts/ledger.py:50`. **`amb` is the one
parameter where the L-against-ambient axis is the SUBJECT rather than a
label**, so say which axis your answer is on and do not mix them.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-267/lj-1.267-report.md` section 1.6, read WHOLE**: the
  residue statement and the instantiation audit.
- **`agents/tasks/LJ-1-184/ProbeLJ1184B.agda:101-130`, read WHOLE**: the
  telescope, `q`, and `go`. **Read the SOURCE, not a report about it.**
- **`agents/tasks/LJ-1-184/ProbeLJ1184C.agda:83`**: the only application, which
  relays.
- **`agents/tasks/LJ-1-243/lj-1.243-report.md` section 2.2**: how the relay was
  found. **Copy the method.**
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`: `amb`'s type.
- **`archive/dev/TASKS-archived.md`.** **The retired route also had an ambient
  cross. Take SHAPE from the archive, never a claim**, and say what would NOT
  transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows, and `amb` is
clause (a) at the ambient carrier.** **Say which row, and whether Devlin proves
this clause or assumes it.** **If Devlin assumes it, that is evidence about
outcome 2 and I want it.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-184/ProbeLJ1184B.agda` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-293/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **C-45.** Audit the instantiation, never the telescope. **The centre.**
- **C-38 as extended.** A relay is not a supply.
- **D-10.** Price the truth before the proof.
- **C-36.** A failed substitution is not a proof of impossibility. **If you
  cannot prove `q`, write the term you could not write.**
- **P-l, P-i, P-k, P-m, P-t, P-y, R-34, R-35, R-40, R-41. C-12, C-22, C-32,
  C-39, C-40, C-42, C-44, C-49, C-50. I-5. DD0, DD8, DD18, DD24, D-26.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with ONE word on `q`: PROVED, FALSE, or BLOCKED.** Then the term, the
countermodel, or the named obligation, at `file:line`. Then each premise
VERIFIED or REFUTED. Then what `amb`'s status becomes. Then whether
`[LJ-1.7]`'s residue is empty. Then the DD4 answer with its axis named.
**Mark every negative MEASURED or INFERRED.**
