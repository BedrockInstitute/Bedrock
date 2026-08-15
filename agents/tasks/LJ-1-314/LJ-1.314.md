# LJ-1.314: DD25 review of `InjData`'s NECESSITY

tier: opus (pi-subagent-mode), **the switch's ADVERSARIAL row.** I ran
`scripts/dispatch/dispatch_policy.py` before writing this line. `[LJ-1.305]` was
dispatched under `pi-subagent-mode` and authored by `pi` on `glm-5.3`, and
**a review takes the mode its TARGET was dispatched under** (owner's ruling,
2026-08-15). That mode's adversarial row is in-harness `opus`. **DD17's
invariant holds: the critic is not the author.**

## WHY THIS REVIEW EXISTS, and it is not routine

**`[LJ-1.305]` returned NEEDS-A-PRINCIPLE.** It asks the project to admit a new
assumption into a trophy:

```agda
Wat α    = Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ α ⟩ × (⟪ α ⟫ ↪ ⟪ δ ⟫))
InjData  = (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩ → ∥ Wat α ∥₁ → Wat α
```

**Under it the untruncated descent is GREEN, 322 lines, 4 s. That half is
MEASURED and this review does not doubt it.**

**The half under review is NECESSITY, and the report marks it plainly:**

> Necessity is **MEASURED at the eliminator level and INFERRED at the theory
> level**; no independence model was built.

**A principle admitted on an INFERRED necessity is an axiom the project did not
have to take.** **The owner is about to be asked to rule on it. Close the gap
first.**

## ATTACK 1: L HAS A DEFINABLE WELL-ORDER, SO WHY IS ANY EXTRACTION NEEDED?

**This is the attack that matters and it should take most of your budget.**

**`InjData` is an extraction principle: from a merely-inhabited `Σ`, produce an
actual one.** **In `L` that is exactly what a definable well-order is FOR.** The
whole reason this project can prove `L ⊨ AC` is that `L`'s elements carry a
canonical order, so a non-empty definable class has a LEAST element and choosing
it needs no choice.

**And the machinery is delivered.** `leastOf` at
`src/L/WellOrder/Base.lagda.md:158-161` extracts the least element of a
predicate under `LEM`. `[LJ-1.305]` USES it, and reports that the successor join
「dissolves for free, because `absorbs` refutes initiality at a predecessor that
`leastOf` extracts with a negational payload」.

**SO ASK THE QUESTION THE REPORT DID NOT: why does the SAME machinery not
dissolve the remaining join?**

- **`Wat α` is a `Σ` over `V ℓ`**, and its first component is an element of a
  well-ordered structure. **Is「the least `δ ∈ α` with `⟪ α ⟫ ↪ ⟪ δ ⟫`」
  expressible as a predicate `leastOf` can take?**
- **If YES, `InjData` is derivable and the principle is not needed.** **That is
  the OVERTURN and it is the most valuable outcome available.**
- **If NO, say exactly which side condition `leastOf` demands that this
  predicate cannot meet**, at `file:line`. **That converts an INFERRED necessity
  into a MEASURED one and the owner can rule on evidence.**

**The report's own words point at the answer either way:** it says the residue
is **「the proof architecture's limitation」**. **An architecture's limitation is
not a theory's necessity.**

## ATTACK 2: THE PRINCIPLE MAY BE A CONSEQUENCE OF A STATEMENT CHOICE

**`[LJ-1.305]` reports a bonus that undercuts its own headline:**

> **Bonus, unconditional.** With no new principle, `sq-initial` delivers the
> untruncated law at every ambient-initial α. Its face is ambient
> `IsCardinal`, against the trophy's `IsCardinalL`.

**So one face of the cardinal fork needs `InjData` and the other may not.**

**That fork is already in the owner's list**, and this return attaches a
measured payoff to it for the first time. **SETTLE WHAT THE PAYOFF ACTUALLY
IS:**

- **Does the ambient face really avoid `InjData` ENTIRELY**, or does it move the
  same debt somewhere else? **Trace it.**
- **Is every ambient-initial α enough for the trophy**, or does `GCHStatement`
  quantify over cardinals that are not ambient-initial? **If the bonus covers
  only a sub-class, it is not an alternative and the report oversells it.**
- **What does the ambient face cost elsewhere?** A statement-level change is
  never free.

**The owner cannot rule on the fork without this.** **It is the second most
valuable thing you can return.**

## ATTACK 3: THE COUNTERMODEL, and check what it actually closes

**`[LJ-1.305]` closes route 1 with a green countermodel:** `sq ω` is NOT an
hProp, `agents/tasks/LJ-1-305/NotProp.agda:203-204`, green.

**Re-run it and read it.** **A countermodel refutes the statement it names and
nothing wider** (C-42). **Does it close「the truncation lifts by
propositionality」in general, or only for the particular `sq` as spelled?** **If
a differently-spelled `sq` were an hProp, route 1 reopens and no principle is
needed.**

## ATTACK 4: IS THIS A CHOICE PRINCIPLE ENTERING AN AC PROOF?

**State plainly what `InjData` is in logical strength terms.** **This project's
first trophy is `L ⊨ AC`, meaning choice is PROVED and never assumed.**

- **Is `InjData` a form of choice, and if so which?** Countable, dependent,
  global, or none of those?
- **Does it appear anywhere in the AC proof's closure**, or only in the GCH
  wing? **`scripts/measure/ledger.py --reuse` answers the second half
  mechanically.**
- **If it is a choice principle and it touches the AC end, say so in the first
  line of your return.** **That would be a much larger finding than a line
  count.**

**I do not assert that it is.** **This is a question I could not answer myself
and it must be answered before the owner rules.**

## ATTACK 5: THE THREE SITES AND ONE RULING

`[LJ-1.305]` says `InjData` is the recorded κ-inj data debt at
`src/L/Cardinal.lagda.md:132-133`, `[LJ-1.299]` and `[LJ-1.156]`
(`dev/PLAN.md:1068`), and that **「one ruling covers all three sites (C-42)」**.

**C-42 says a refutation measures the site it names. Here it is used to EXTEND a
claim across three sites.** **Check the three are really one debt and not three
debts that look alike.** **If they differ, the owner is being asked for one
ruling where three are needed.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **`InjData` IS DERIVABLE from delivered machinery.** **OVERTURN, and the best
  outcome.** Give the term or the exact derivation sketch with each step at
  `file:line`. **No new principle enters the trophy.**
- **IT IS NECESSARY AND YOU MEASURE WHY.** **UPHOLD.** Name the side condition
  `leastOf` cannot meet, at `file:line`. The owner then rules on evidence.
- **THE AMBIENT FACE AVOIDS IT.** **Then the fork decides the principle**, and
  say what the ambient face costs.
- **IT IS A CHOICE PRINCIPLE TOUCHING THE AC END.** **Stop and say so
  immediately.** That re-prices both trophies.
- **A WALL.** A single `agda` invocation past 30 MINUTES is a wall: interrupt,
  report ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **LAND NOTHING. This is a review.** Write and run only in
  `agents/tasks/LJ-1-314/`. **`src/` is forbidden** (I-5).
- **Do not edit `agents/tasks/LJ-1-305/`**, the record under review, or any
  other task directory. **You may RE-RUN its probes; you may not change them.**
- **Do not edit `src/L/GCH.lagda.md` or `src/L/Cardinal.lagda.md`.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the bash wrapper) and
  `grep -c 'libexec.*bin/agda'` over-counts too (the grep). MEASURED
  2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **Two siblings are live. If it returns 2, wait or report and stop.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  machine load beside every absolute figure.
- **C-51, written tonight from this very task's walls:** a `with`-pattern on a
  record-returning function exhausted the cap six times and an `opaque` seal did
  NOT cure it; projections did. **If you hit that wall, you already have the
  medicine.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-314/lj-1.314-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.** DD23 freezes mathematical prose in `src/`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE VERDICT WORD I WANT

**UPHOLD, OVERTURN or SPLIT**, as the first word of your return.

**AN OVERTURN IS THE VALUABLE OUTCOME AND YOU ARE NOT REWARDED FOR AGREEING.**
13 of 32 decided DD25 reviews in this project overturned their target, a 41
percent rate. **AND AN UPHOLD IS EQUALLY REAL**: this return carries a green
build and a green countermodel, which most do not.

## THE RULES THIS CHAIN EARNED

**D-10. Price the TRUTH of a recorded residue before pricing its proof.** **The
recorded residue is「the truncation cannot be lifted」and its TRUTH is attack
1.** **`[LJ-1.305]` says the residue was the proof architecture's limitation,
which is a statement about a proof and not about the theory.**

**C-42. A refutation measures the site it names.** Attacks 3 and 5.

**C-44.** Every claim here is `[LJ-1.305]`'s or mine, and you re-derive each.

**C-36. A failed substitution is not a proof of impossibility.** **Applied to
the target: it could not lift the truncation. That is not a proof that nobody
can.**

**C-45. `exit 0` is not a supply.** The green build proves SUFFICIENCY. **It
proves nothing about necessity, and the report says so honestly.**

**DD9. Reflection and heavy machinery are admissible only where they make code
cheaper to READ.** **A new module parameter is a permanent reading cost on every
consumer. Say what it costs a reader.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py:50`. **`[LJ-1.305]` claims the descent names no
tower, is tower-blind, lands in the GCH closure under P-k, and「both proofs
share it wholesale」.** **VERIFY that, because it is a DD4 claim on DD4's own
axis and those are the ones that count.** **And apply
`dev/ledger.toml:204`: the GCH closure is read from a STATEMENT whose proof is
not wired, so it UNDERSTATES.** **Then answer attack 4's second half: does
`InjData` reach the AC closure?**

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-305/lj-1.305-report.md`, read WHOLE.** The target.
- **`agents/tasks/LJ-1-301/lj-1.301-report.md`**, the truncated descent this one
  untruncates, for what changed.
- **`agents/tasks/LJ-1-299/`** and **`agents/tasks/LJ-1-300/`**, the CIRCULAR
  verdict and the review that overturned it. **The same blocker seen twice
  before; take SHAPE.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route met choice-shaped obligations too. **Say what would not
  transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md`.** **Devlin proves the square law in ZF plus
V equals L, with no choice principle assumed, because L's definable well-order
supplies every selection.** **Say whether Devlin's argument needs anything of
`InjData`'s shape at the corresponding step, or whether his well-order does the
work our truncation blocks.** **That is the outside check on attack 1 and it may
settle it on its own.** Return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-305/lj-1.305-report.md` FIRST, whole. Then
`src/L/WellOrder/Base.lagda.md:150-190`, `leastOf` and what it demands.

## SCOPE (write)

`agents/tasks/LJ-1-314/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for review` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-10, C-42, C-44, C-36, C-45.** Named above with what each attacks.
- **C-12.** Two Agda processes, counted with the command above.
- **C-51**, written tonight from this task's own walls.
- **C-22, C-32, C-38, C-39, C-40, C-49, C-50.** I-5. **P-k, P-l, P-i, P-y,
  R-40, D-1, D-26.**
- **DD0, DD4, DD8, DD9, DD18, DD23, DD24, DD25.**

## RETURN

**Lead with ONE word: UPHOLD, OVERTURN or SPLIT.** Then attack 1: whether
`leastOf` and L's definable well-order derive `InjData`, with the term or the
exact side condition that blocks it at `file:line`. Then the ambient face: does
it avoid the principle entirely, and does it cover every cardinal the trophy
quantifies over. Then the countermodel, re-run and scoped. Then what `InjData`
is in logical strength terms and whether it reaches the AC closure. Then whether
the three sites are one debt. **Mark every negative MEASURED or INFERRED.**
