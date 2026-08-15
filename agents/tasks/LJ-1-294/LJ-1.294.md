# LJ-1.294: is an infinite cardinal a limit ordinal? The one real gap in `Init`

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch_policy.py` before writing this line and took the head it
gave**: `pi-subagent-mode` is IN FORCE, PINNED by the owner 2026-08-15, default
case `herdr` / `pi` / `glm-5.3`. **QUEUED rather than run**, because C-12's two
Agda slots were held; the queue fires when one clears.

## GOAL

**`[LJ-1.8]` is half of LJ-1's terminus. Its statement is landed and ONE
hypothesis blocks the proof: `sq : SqShape` at `src/L/GCH.lagda.md:80`.**

The delivered uniform square law is `via-col-square` at
`src/L/Ordinal/SquareLaw.lagda.md:960`, and it consumes `Init α`, a four-part
conjunction at `:692-699`. **At the USE SITE, where `κ` arrives with
`IsCardinalL κ` and `⟨ fst κ ∈ˢ ω ⟩ → ⊥`, I checked all four:**

| `Init κ` component | status at the use site |
|---|---|
| `IsOrd κ` | **GIVEN** by `GCHStatement` |
| `⟨ ω ∈ˢ κ ⟩` | **DERIVABLE** by `ord-tri`, `src/L/Ordinal/Linear.lagda.md:136` |
| successor-closed, κ a LIMIT | **THE GAP. Nothing in the tree proves it** |
| `noinj²` | the mathematical content `via-col-square` exists to consume |

**Settle the third row. Is an infinite cardinal a limit ordinal, and can this
tree prove it?**

## THE STANDARD ARGUMENT, and it is a SHAPE and not a proof

If `κ = sucV γ` with γ infinite, then `γ ↪ κ` and `κ ↪ γ`, so γ and κ have the
same cardinality, which contradicts `IsCardinalL κ`. **`IsCardinalL` at
`src/L/Cardinal.lagda.md:231-233` says exactly that no smaller ordinal injects
back**, so the contradiction should be reachable. **I have NOT built it. Treat
this paragraph as a hypothesis, not a plan** (C-44).

## PREMISES

- **`Init` is four parts at `src/L/Ordinal/SquareLaw.lagda.md:692-699`**, and
  `:695` is the successor-closure part. I read it. RE-READ IT.
- **`ord-tri` at `src/L/Ordinal/Linear.lagda.md:136` compares any two
  ordinals**, and LEM is already a module parameter there, so using it adds no
  new assumption. **VERIFY that second half**: if it introduces a parameter the
  GCH site does not already carry, the `ω ∈ˢ κ` row is not free after all and
  that changes the answer.
- **`IsCardinalL κ` is `(δ : S) → ⟨ fst δ ∈ fst κ ⟩ → (∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁ → ⊥)`**
  at `src/L/Cardinal.lagda.md:231-233`. **Note it is stated with `InjCode`, an
  internal coded injection, NOT a bare `↪`.** **That may be the whole
  difficulty: the standard argument needs an injection and this gives you a
  coded one.** **Check what it costs to move between them before you assume the
  argument goes through.**
- **`sucV` facts exist**: `self∈sucV` and `∈sucV-inl` are used throughout
  `src/L/Coding/EnvSupply.lagda.md`. Find their home and see what else is there.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT IS PROVABLE AND YOU BUILD IT.** Report the term and its lines. **Then
  `Init κ` is constructible at the use site and `[LJ-1.8]` is unblocked.** STOP.
- **IT IS TRUE BUT NEEDS SOMETHING UNDELIVERED.** **Name it at `file:line` and
  price it.** The `InjCode`-against-`↪` gap is the likeliest such thing.
- **IT IS ALREADY IN THE TREE.** **Then say where and this task closes in an
  hour.** Search before you build (C-44): three times this month a report
  called absent what the repository held.
- **IT IS FALSE OR NOT PROVABLE HERE.** **That is the most valuable outcome**,
  because it means `[LJ-1.8]` needs a different route and the project should
  hear it before funding one. **Give the countermodel or the term that fails**
  (C-36).
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-294/`.
  **`src/` is forbidden for probes** (I-5) and `scripts/check-probes.py`
  enforces it.
- **Do not edit `src/L/GCH.lagda.md`.** **Its statement is the trophy and
  changing it is the owner's, not yours or mine.** If you conclude the fix is a
  re-typing, SAY SO and stop.
- **Do not edit any other master**, and do not touch another task directory.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- **Create `agents/tasks/LJ-1-294/lj-1.294-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on what you write. **No em dash in any
  language.** DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**D-10. Price the TRUTH of a recorded residue before pricing its proof.** **The
orchestrator escalated this to the owner as a two-way fork and was wrong**: the
fork was measured against `SqShape`'s domain instead of the use site, and three
of the four parts changed status once the right object was measured. **Measure
the object the proof will actually face.**

**C-44.** Every claim in this brief is mine from a reading, not from a build.

**C-36. A failed substitution is not a proof of impossibility.** If you cannot
build it, write the term you could not write.

**A STOP IS A DELIVERABLE.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**A cardinal-is-limit lemma is pure ordinal arithmetic and names no tower**, so
it should be written once and inherited by both. **Say where it belongs so that
is true**, and whether `src/L/Ordinal/` or `src/L/Cardinal.lagda.md` is the
right home under P-k, which states a read lemma where its consumers use it.

**NAME YOUR AXIS** (C-46). DD4's own axis is AC-against-GCH, fixed in code at
`scripts/ledger.py:50`. **`src/L/Cardinal.lagda.md` is inside the GCH closure
today and `src/L/Ordinal/Linear.lagda.md` is in BOTH**, so the home you choose
moves the shared figure. Say which way.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-286/lj-1.286-report.md`, the `Init` gap table**, which is
  where this task's question comes from. **Read it whole and notice it measured
  the DOMAIN; your job is the USE SITE.**
- `agents/tasks/LJ-1-279/lj-1.279-report.md`: why row 5 rebuilt the base at ω
  from `InitialCore` rather than calling `via-col-square`. **That is the same
  obstruction seen from the other end.**
- **`archive/dev/TASKS-archived.md`.** **The retired route had cardinal
  arithmetic too, and `[LJ-1.1]` called `CardinalPredicates` PORTABLE at 399
  lines while `[LJ-1.273]` measured its `cardFo` as the BIJECTION form against
  today's INJECTION form.** **Take SHAPE from the archive, never a claim**, and
  say what would not transfer.

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Devlin proves the square law somewhere, and `dev/literature/devlin-II5.md`
splits II.5 into twelve rows.** **Say whether Devlin states cardinal-is-limit as
a lemma, assumes it, or never needs it because his cardinals are limits by
definition.** **That last possibility is real and it would tell us the gap is in
our DEFINITION rather than in our proofs.** Return a **LITERATURE USED**
section.

## SCOPE (read)

`agents/tasks/LJ-1-286/lj-1.286-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-294/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **D-10.** Price the truth before the proof. **The centre.**
- **C-44.** A brief's claim is unchecked until you check it.
- **C-36.** A failed substitution is not a proof of impossibility.
- **C-38 as extended.** A hypothesis is discharged when something SUPPLIES it.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-i, P-m, P-t, R-34, R-35, R-40, R-41. C-12, C-22, C-32, C-39, C-40,
  C-42, C-45, C-49, C-50. I-5. DD0, DD8, DD18, DD24, D-26.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with ONE word: PROVED, BLOCKED, ALREADY-THERE or FALSE.** Then the term
or the obstruction at `file:line`. Then each premise VERIFIED or REFUTED, and
especially whether `ord-tri` is free at the GCH site and what the
`InjCode`-against-`↪` move costs. Then whether `Init κ` is now constructible at
the use site. Then the home you recommend and its DD4 effect with the axis
named. **Mark every negative MEASURED or INFERRED.**
