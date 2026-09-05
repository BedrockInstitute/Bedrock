# LJ-1.344: supply the repaired ties. `KFacts` lacks a singleton closure

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. I ran
`scripts/dispatch/dispatch_policy.py` before writing this line.

## THE STATE, and this task is unblocked rather than new

**`[LJ-1.341]` proved two delivered ties FALSE. `[LJ-1.343]` landed the repair,
green at 133.96 s. `[LJ-1.345]` reviewed the refutation at the adversarial head
and returned UPHOLD:**

> **The chapter was edited on a TRUE premise. Nothing must be reverted.** The
> instantiation is admissible four ways; both premises are inhabited, so the
> ties were **FALSE and not merely unusable**; and the repaired statement is
> **what the sites need, not merely what typechecks**, because the unbounded
> form was empty at every environment so nothing could ever have supplied it.

**The repair removed VACUITY. It did not supply the ties.** **That is this
task.**

## THE NAMED FIRST LINE

**`[LJ-1.343]` and `[LJ-1.345]` both name the same gap, and `[LJ-1.345]`
re-measured it:**

> **`KFacts` carries no SINGLETON closure, and `envOne v` is a singleton.**
> **It is TWO lines from `BoundOver.pr∈λ` at `src/L/Coding/Bound.lagda.md:69`
> and `trans∈λ` at `:93`**, measured at
> `agents/tasks/LJ-1-341/ProbeTies341.agda:285-286`.

**I read both, verbatim:**

```agda
pr∈λ    : (x y : S) → ⟨ x ∈ˢ T lam ⟩ → ⟨ y ∈ˢ T lam ⟩ → ⟨ pr x y ∈ˢ T lam ⟩
trans∈λ : {x y : S} → ⟨ y ∈ˢ x ⟩ → ⟨ x ∈ˢ T lam ⟩ → ⟨ y ∈ˢ T lam ⟩
```

## THE TASK

**Supply the two repaired ties, `envK` and `defPairK`, at the ambient
carrier.**

**Both repairs are already TERMS** at
`agents/tasks/LJ-1-341/ProbeTies341.agda:248-266` and `:280-294`. **Start from
them, re-run them, and close the singleton gap.**

## WHAT `KValue` KNOWS AND HAS NEVER BEEN ASKED

**`module KValue` at `src/L/Condensation.lagda.md:7264-7318` supplies `pairK`,
`numK0` and `carrierK`, which `[LJ-1.341]` measured are exactly what the
corrected statements need.** **And `[LJ-1.338]` measured it has ZERO consumers
anywhere in `src/`, including its own chapter: the L side built the value and
never wired it.**

**And `[LJ-1.338]` measured that its 50 lines copy to ambient at ZERO changed
lines, plus a 15-code-line adapter.** **So most of this task may be assembly
rather than proof. Check that first.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **BOTH TIES SUPPLIED.** Report the terms, their lines and seconds, and the
  negative control. **Then the third kind of debt is discharged at its own
  site.** STOP.
- **THE SINGLETON CLOSURE IS NOT TWO LINES.** **Say what it costs and why the
  two-line reading was wrong.** `[LJ-1.345]` re-measured the gap as real, but
  neither task built the closure itself.
- **A THIRD TIE IS ALSO UNSUPPLIED.** **`[LJ-1.338]` counted six construction
  ties and `[LJ-1.343]`'s repair touched two.** **The remaining four are
  `witK`, `graphWitK` and two arity-numeral facts.** **If you can supply them
  cheaply, do; if not, price them and stop.**
- **A WALL.** The chapter is about 133 s and **a plain re-check is now a CACHE
  HIT at 2.35 s**, which `[LJ-1.345]` caught: **it forced an honest cold check
  by copying the chapter verbatim with only the module renamed.** **Do the same
  if you need a real figure.** 30 minutes on one invocation is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING in `src/`. This is a probe.** Write and run only in
  `agents/tasks/LJ-1-344/`. **`src/` is forbidden** (I-5). **If a supply belongs
  in the chapter, say where and I land it.**
- **Do not edit another task directory.** You may READ and RE-RUN the probes in
  `agents/tasks/LJ-1-341/`, `LJ-1-343/`, `LJ-1-345/` and `LJ-1-338/`.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **The two obvious alternatives both OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended: a delta
  under the floor is UNMEASURABLE, not small).
- **RUN A NEGATIVE CONTROL that MEASURES**, and **include non-vacuity**:
  `[LJ-1.341]` and `[LJ-1.345]` both did, and this whole episode exists because
  a hypothesis that typechecks says nothing about its truth.
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-344/lj-1.344-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eight of my last seventeen briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the singleton closure is two lines」.** **That figure is
`[LJ-1.341]`'s from a probe line reference, and `[LJ-1.345]` confirmed the gap
is real without building the closure.** **Neither built it. You do.**

**And a correction `[LJ-1.345]` made to the record you should carry:**
`[LJ-1.343]`'s **6,718-line closure figure was taken before its own edit; the
chapter is 6,731 today, still `gch_only`.**

## THE RULES

**C-45** is the law of this whole episode: `exit 0` is not a supply, and a
module that assumes a false thing typechecks forever.
**D-10, C-42, C-44, C-53, C-57, C-36, P-l, C-22, C-32, C-39, C-40.** I-5.
**D-1, D-26. DD0, DD4, DD8, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), which is
AC-against-GCH, fixed at `scripts/measure/ledger.py:50`.

**`[LJ-1.341]` measured that the repair is class-free, so it is written once and
serves both ends.** **Say whether your SUPPLY keeps that property**, and note
`dev/ledger.toml:204`: the GCH closure is read from a STATEMENT whose proof is
not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-345/lj-1.345-report.md`, read WHOLE.** The review that
  unblocked you, and it corrected two figures in the record.
- **`agents/tasks/LJ-1-341/lj-1.341-report.md`**, which holds both repairs as
  terms and the singleton gap.
- **`agents/tasks/LJ-1-338/lj-1.338-report.md`**, the third kind of debt and the
  zero-changed transport of the L-side value module.
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **`[LJ-1.345]` confirmed against the PRIMARY
source that Devlin binds all unbounded quantifiers by a set built from the
members of its argument, and that the repair's carrier hypothesis is the port of
his membership premise.** **Say in one line whether your supply is the port of
something he proves or something he assumes.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-341/ProbeTies341.agda:248-294`, the two repairs as terms,
FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-344/` only.

## RETURN

**Lead with ONE line: are both ties supplied, and at what cost.** Then the
singleton closure, built or refuted at two lines. Then whether `KValue`
transports as measured. Then the four remaining construction ties, supplied or
priced. Then your negative control including non-vacuity. Then where the supply
belongs in the chapter. **Mark every negative MEASURED or INFERRED.**
