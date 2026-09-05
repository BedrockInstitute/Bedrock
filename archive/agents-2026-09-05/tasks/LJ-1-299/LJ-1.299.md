# LJ-1.299: build `noinj²`, the last row of `Init`

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the head
it gave.** **NOTE THE PATHS: `[LJ-1.295]` reorganised `scripts/` today.**
`rules.py` is `scripts/dispatch/rules.py`, the linters are `scripts/gate/`,
`ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**`[LJ-1.8]` is half of LJ-1's terminus and it is blocked on ONE row.**

`GCHStatement`'s remaining hypothesis is `sq : SqShape`, and the delivered
uniform law `via-col-square` at `src/L/Ordinal/SquareLaw.lagda.md:960` consumes
`Init α`, four conjuncts at `:692-699`. **Three are now available at the use
site:**

| `Init κ` row | status |
|---|---|
| `IsOrd κ` | GIVEN by `GCHStatement` |
| `⟨ ω ∈ˢ κ ⟩` | derivable, `ord-tri` at `src/L/Ordinal/Linear.lagda.md:136`, and I VERIFIED that `L.GCH` and `L.Ordinal.Linear` take the SAME `LEM (ℓ-suc ℓ)` module parameter, so it costs nothing |
| successor closure | **PROVED** by `[LJ-1.294]`, `κ-limit` |
| **`noinj²`** | **THE GAP** |

**`[LJ-1.294]` measured by grep that NO term of the fourth conjunct exists
anywhere in `src/`**, and that `InitialCore`'s `noinj²` and `finite-excl`
parameters are instantiated only at ω inside `L.InjChain`.

**Build `noinj²` at the use site, or measure that it cannot be built.**

## THE STATEMENT, verbatim from `Init`'s fourth conjunct

```agda
(β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
        → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
        → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥
```

**In words: α's index injects into no infinite member's square.** At the use
site α is κ, and κ carries `IsCardinalL κ`.

## THE SHAPE THAT MAY MAKE IT CHEAP, and it is a HYPOTHESIS not a plan

**`IsCardinalL κ` at `src/L/Cardinal.lagda.md:231-233` says exactly that no
smaller ordinal admits a coded injection back.** `noinj²` asks for no injection
into a SQUARE of a smaller ordinal. **If the square of an infinite β injects
into β, the two are bridgeable and `IsCardinalL` should close it.**

**`[LJ-1.279]` landed `src/L/InjChain.lagda.md` and its row 1 is exactly the
composition of two injections.** **Read it: the composition you need may already
be there.**

**Do NOT assume this goes through** (C-44). `[LJ-1.294]` found that
`IsCardinalL` is stated with `InjCode`, an internal CODED injection, not a bare
`↪`, and flagged the move between them as the likely cost. **Check that first.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT BUILDS.** Report the term and its lines. **Then `Init κ` is constructible
  and `[LJ-1.8]` is unblocked for the first time.** STOP.
- **IT NEEDS THE SQUARE LAW ITSELF.** **Then the dependency is circular:
  `via-col-square` consumes `Init` which needs `noinj²` which needs the square
  law.** **Say so plainly and stop. That is the most valuable outcome**, because
  it would mean the route is wrong and not merely unbuilt.
- **THE `InjCode`-TO-`↪` MOVE IS THE COST.** Price it and say where it belongs.
- **IT IS FALSE AT SOME κ.** Give the countermodel. **`[LJ-1.286]` found two
  `Init` rows FALSE on `SqShape`'s domain by asking exactly this question, so
  ask it here too.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **NEVER raise the cap.**

## CONSTRAINTS

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-299/`.
  **`src/` is forbidden for probes** (I-5).
- **Do not edit any master.** Copy what you need.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- **A SIBLING IS LIVE** in `agents/tasks/LJ-1-298/`. Do not touch it.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-299/lj-1.299-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `scripts/gate/lint-agda.py --check`. **No em dash in any language.** DD23
  freezes mathematical prose.
- Count with `.venv/bin/python scripts/measure/ledger.py`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**D-10. Price the TRUTH of a recorded residue before pricing its proof.** **I
escalated a fork to the owner this afternoon on this exact object and was
wrong**, because I measured `SqShape`'s DOMAIN instead of the USE SITE. **Measure
what the proof will actually face.**

**C-44.** Every claim in this brief is a reading, not a build.

**C-36. A failed substitution is not a proof of impossibility.** If you cannot
build it, write the term you could not write.

**A STOP IS A DELIVERABLE**, and a circular dependency found here is worth more
than a term.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`noinj²` is pure ordinal and cardinal arithmetic and names no tower**, so it
should be written once and inherited by both ends. **Say where it belongs under
P-k, which states a read lemma where its consumers use it**, and **NAME YOUR
AXIS** (C-46): DD4's own axis is AC-against-GCH, fixed in code at
`scripts/measure/ledger.py`, and `src/L/Ordinal/Linear.lagda.md` sits in BOTH
closures while `src/L/Cardinal.lagda.md` sits only in GCH. **The home you choose
moves the shared figure; say which way.**

## ARCHIVE (DD18)

`agents/tasks/LJ-1-294/lj-1.294-report.md` read WHOLE: `κ-limit`, the `Init`
table, and the grep that found no fourth-conjunct term.
`agents/tasks/LJ-1-286/lj-1.286-report.md`: where two `Init` rows were measured
FALSE on a domain. `agents/tasks/LJ-1-279/lj-1.279-report.md` sections 0 to 3:
`InjChain`'s composition and why row 5 rebuilt the base at ω.
`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`, taking SHAPE
and never a claim, and saying what does NOT transfer: `[LJ-1.273]` measured its
`cardFo` as the BIJECTION form against today's INJECTION form. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` splits II.5 into twelve rows.** **Say which row
`noinj²` is, and whether Devlin proves it or takes it as part of the definition
of a cardinal.** **If he takes it definitionally, the gap is in our DEFINITION
and not in our proofs, and that changes everything.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-294/lj-1.294-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-299/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **The tool prints `Full entry: dev/LESSONS.md:<line>` and says THIS
IS AN EXCERPT when it truncated. OPEN the full entry for any law you act on.**

- **D-1.** The abort criterion is fixed above.
- **D-10.** Price the truth before the proof. **The centre.**
- **C-44, C-36, C-38, C-45.**
- **P-k, P-l, P-i, P-m, P-t, R-34, R-40, R-41. C-12, C-22, C-32, C-39, C-40,
  C-42, C-49, C-50. I-5. DD0, DD8, DD18, DD24, D-26.**

## RETURN

**Lead with ONE word: BUILDS, CIRCULAR, BLOCKED or FALSE.** Then the term or the
obstruction at `file:line`. Then whether `Init κ` is constructible at the use
site. Then what the `InjCode`-to-`↪` move cost. Then the home you recommend and
its DD4 effect with the axis named. **Mark every negative MEASURED or
INFERRED.**
