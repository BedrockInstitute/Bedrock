# LJ-1.242: the fifth step, and two returns have already met in the middle

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**`[LJ-1.241]` left ONE term unwritten for `[LJ-1.7]`: the fifth step, the
numeral-closure that discharges `amb`.** **Write it. And start from the fact
that two earlier returns already met in the middle without either noticing.**

## THE CONVERGENCE, which I re-derived at the source

**`amb` is the SOUNDNESS direction**, at
`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:190-192`:

```agda
AmbientRead = (v b : S) → IsOrd b
            → ⟨ (v ∷ b ∷ []) Cr.AbsP.⊨ᵛ Cr.φP ⟩ → v ≡ Lset b
```

**If the AMBIENT carrier believes the formula at `(v, b)`, then `v` IS
`Lset b`.** **That is exactly where `[LJ-1.240]`'s objection bites: an
unconstrained tag lets a WRONG `v` satisfy the formula.**

**`[LJ-1.184]` SUPPLIED `amb` at its verbatim type**
(`agents/tasks/LJ-1-184/ProbeLJ1184B.agda:150`, exit 0), and `theorem` came out
with `amb` gone (`ProbeLJ1184C.agda:95`, exit 0). **But it declared its own
residue first, in its section 0.2**, and the residue is **SIX READINGS at the
ambient carrier**: `StepAt-out`, `StepAt-back`, `ApproxAt-dom`,
`ApproxAt-value`, `ApproxAt-step`, `Graph-out`.

**THOSE ARE THE SAME SIX `[LJ-1.238]` PORTED YESTERDAY.**
`agents/tasks/LJ-1-238/GenSequence.agda`, exit 0, **40 written lines, 145
verbatim, per-tower residual ZERO.**

**So `[LJ-1.184]`'s declared residue is discharged by `[LJ-1.238]`'s port, and
neither report knew about the other.** **Check that claim first: it is mine and
C-44 says it is unchecked until you check it.**

## THE QUESTION, stated exactly

**With `[LJ-1.241]`'s real `φ₀` (which carries `pins`) and `[LJ-1.238]`'s
ported readings, does `amb` hold?**

**`[LJ-1.184]` supplied `amb` at SOME `φ₀`. `[LJ-1.241]` has now built the real
one.** **A supply at one formula is not a supply at another** (P-l applied to a
formula rather than a figure).

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`amb` HOLDS AT THE REAL `φ₀`.** Report the written lines and the seconds.
  **Then `[LJ-1.7]`'s four hypotheses are `amb` SUPPLIED, `s₁` BUILT, and `sl`
  and `sc` reduced to supplying `lh`, and phase 1's blocking row is one
  assembly from moving.** STOP.
- **`amb` NEEDS THE NUMERAL-CLOSURE, AND HERE IT IS.** Write the closure,
  report its lines, and say which pins it needed. **`[LJ-1.241]` built `pins`
  at `ProbeLJ1241A.agda:124-137`; say whether that is the closure or only part
  of it.**
- **`amb` FAILS AT THE REAL `φ₀`.** **NAME the wrong `v` that satisfies the
  formula** (C-36). **That is the most valuable outcome available and it would
  mean `[LJ-1.184]`'s supply does not survive the real formula.** **Say what
  `[LJ-1.184]` supplied it at.**
- **THE SIX READINGS DO NOT DISCHARGE THE RESIDUE.** If `[LJ-1.238]`'s port
  does not fit `[LJ-1.184]`'s hole, **say why at `file:line` on both sides.**
  **My convergence claim is then refuted and I want that plainly.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **Every cut gets the SAME
  bound as its green control, and the control's elapsed time is reported BEFORE
  any cut is interpreted** (`[LJ-1.215]`'s law).

## WHAT IS GREEN, so you assemble rather than invent

| file | what it is | state |
|---|---|---|
| `agents/tasks/LJ-1-241/ProbeLJ1241A.agda` | the real `φ₀` at arity two, with `pins`, 77 lines | exit 0 |
| `agents/tasks/LJ-1-241/ProbeLJ1241B.agda` | the slot-trace verification | exit 0 |
| `agents/tasks/LJ-1-238/GenSequence.agda` | the six readings, class-generic, residual 0 | exit 0 |
| `agents/tasks/LJ-1-184/ProbeLJ1184B.agda` | `amb` supplied at its verbatim type | exit 0 |
| `agents/tasks/LJ-1-184/ProbeLJ1184C.agda` | `theorem` out with `amb` gone | exit 0 |
| `agents/tasks/LJ-1-237/ProbeLJ1237A.agda` | `sl` 14 lines, `sc` 38, over `lh` | exit 0 |

**Six green files. Assemble; do not rewrite any of them.**

## WHAT YOU MUST NOT DO

- **Do not supply `lh`.** That is steps 1 to 4 and a separate dispatch.
  **You do the FIFTH step.**
- **Do not rebuild `φ₀`, the readings, `sl` or `sc`.**
- **Do not edit any master.** This is a probe. **Nothing lands in `src/`, and a
  probe under `src/` is forbidden by I-5.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **A probe goes in `agents/tasks/LJ-1-242/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure**, discard a warm-up, and take at least
  three kept runs for any figure a decision rests on.
- **Report a heap exhaustion as a wall.** Never raise the cap. **`[LJ-1.234]`
  met one and it was R-34's unpinned `InfinitySet` level meta, cured by
  `module IS = InfinitySet {ℓ}`.**
- **A probe whose module name predates the one-directory-per-task move needs
  its include path set from the task directory** (`[LJ-1.235]`).
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## TWO RULES THIS AREA EARNED THIS WEEK

**CARRY A CLAIM'S QUALIFIER OR CARRY NEITHER.** I dropped four words from a
report and the project's status screen then said a type was REFUTED when it was
not. **When you bound a claim, bound it in the sentence a reader will quote.**

**THE ARCHIVE BEARS UNTIL YOU OPEN IT.** Two reports recorded the archive as
surveyed and not bearing; both were wrong, and the retired route held the
arity-two formula everyone was looking for. **Your ARCHIVE USED section must
name, for each archived file you opened, ONE line you read.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.241]` MEASURED the split: `φ₀` is Def-tower content, but the numeral
primitives `isZeroAt`, `sucAt` and `numAt` are pure FOL syntax over `⊥*` and
tower-neutral, so the J tower pays them once.** **`[LJ-1.238]` measured the six
readings at per-tower residual ZERO.**

**So say which side the numeral-closure lands on.** **If the closure is
tower-neutral, phase 1's last per-tower object is smaller than
`dev/literature/devlin-II5.md:387-389`'s two objects suggest, and that is a
real DD4 finding.**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-184/lj-1.184-report.md`**, read WHOLE, **especially
  section 0.2 and section 5**: the supply, the six-reading residue it declared
  itself, and the 167-line carrier-generic read-off it measured.
- **`agents/tasks/LJ-1-238/lj-1.238-report.md` and `GenSequence.agda`**, read
  WHOLE: the port that may fill that hole.
- **`agents/tasks/LJ-1-241/lj-1.241-report.md` and both probes**: the real
  `φ₀`, `pins`, and the verified slot trace.
- `agents/tasks/LJ-1-240/lj-1.240-report.md`: why the closure is owed to `amb`
  and its own failed attack, which is the evidence that it is real.
- `agents/tasks/LJ-1-178/ProbeLJ1178A.agda:188-194`: `AmbientRead` as stated.
- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:167-169`
  (`CrossOut`), `:592-593` (`Cl = ⊤̇`), `:768-769`, `:823-824`.**
  **`[LJ-1.241]` measured that `CrossOut σᴹ` is NEVER APPLIED there, so the
  archive stops exactly where you start.** Take SHAPE, never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md:95-96` states the level-hood as
`∃z Φ(z,v,γ)`.** **Devlin's clause (a) is the soundness direction. Say whether
he proves it or takes it from the construction**, and whether his argument
needs anything like a numeral-closure. Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-184/lj-1.184-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-242/` only. **No master.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and `--for build`.

- **D-1.** The abort criterion is fixed above.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **C-44.** A brief's claim is unchecked until you check it. **The convergence
  claim above is MINE and it is exactly the kind C-44 names.**
- **P-l.** A supply at one formula is not a supply at another.
- **C-36.** Write the term you could not write.
- **C-42, C-39, C-40. I-5, R-34. P-i, P-k, P-m, P-t, P-y, R-40. C-12, C-22.
  DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether `amb` holds at the real `φ₀`, and with the fifth step's
written lines if you wrote it.** Then whether `[LJ-1.238]`'s six readings
discharge `[LJ-1.184]`'s declared residue, at `file:line` on both sides. Then
any wrong `v` you found. Then which side of DD4 the closure lands on. Then the
seconds with load and run count. **Mark every negative MEASURED or INFERRED.**
