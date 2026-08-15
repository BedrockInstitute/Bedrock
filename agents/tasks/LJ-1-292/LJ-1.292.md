# LJ-1.292: sweep `Key.lagda.md` for the mixed spelling that cost 476 seconds

tier: pi (pi-subagent-mode), **model `glm-5.3`**. **I ran
`scripts/dispatch_policy.py` before writing this line and took the head it
gave**: `pi-subagent-mode` is IN FORCE, PINNED by the owner 2026-08-15, default
case `herdr` / `pi` / `glm-5.3`.

## GOAL

**C-42 is the law: a refutation measures the site it names and never measures
how far that site extends. `[LJ-1.287]` named ONE site. This is the sweep.**

**What `[LJ-1.287]` measured**, and I verified both spellings myself:
`src/L/Coding/EnvSupply.lagda.md` cost **480.25 s** and **438 of those seconds
were one identity conversion**: `sucIter 4 δ` against
`sucV (sucV (sucV (sucV δ)))`, body `p = p`. **Depth is free. The MIXED SPELLING
of the level is what costs.** The in-file control proves it: `envSetK` at
`:143-146` is depth 4 in ONE spelling and costs 11 ms. The cure was three lines
and took the master to **4.10 s**.

**`[LJ-1.287]` then flagged a second site and did not measure it**, which is
what this task is for:

**`src/L/Coding/Key.lagda.md:424-429`.** I read it and both spellings are
present:

```agda
  α = sucIter 3 σ
  σ∈α = ∈sucV-inl {A = sucIter 2 σ} {x = σ}
          (∈sucV-inl {A = sucIter 1 σ} {x = σ} (self∈sucV σ))
```

**`sucIter` at depths 1, 2 and 3, against `∈sucV-inl`'s `sucV` chain.** **That
master has NEVER been profiled.**

## PREMISES

- **`Key.lagda.md:424-429` carries `sucIter` at depths 1 to 3.** I read it; you
  re-read it (C-44).
- **Nobody has profiled `Key.lagda.md`**, per
  `agents/tasks/LJ-1-287/lj-1.287-report.md`. VERIFY, because if someone has,
  the figure exists and this task is cheaper.
- **The cure at the first site was to climb by a module parameter instead of
  `sucIter`.** Whether the same ingredient exists here is NOT known and is
  yours to find.
- **P-l binds hard: 476 seconds at one site says NOTHING about this one.** The
  depths are 1 to 3 here and 4 there, and `[LJ-1.287]` measured that depth is
  free, so **the cost may be small or absent.** A small answer is a real answer.

## WHAT TO BRING BACK

**1. THE PROFILE.** `agda --profile=definitions` on `Key.lagda.md`, cold, with
the load beside it. **Which definition carries the seconds?** C-50: profile
before you cure.

**2. IS IT THE SAME SHAPE?** If the charged definition is a mixed-spelling
conversion, say so at `file:line` and give its ms. **If the seconds are
somewhere else entirely, that is the more valuable answer**, because it means
the shape does not generalise and the project stops looking for it.

**3. A TREATED ARM, ONLY IF THE PROFILE JUSTIFIES ONE.** Control first, at least
three kept cold runs per arm, order reversed between cycles.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE SHAPE IS HERE AND IT COSTS.** Report the profile, the cure and the
  delta. STOP.
- **THE SHAPE IS HERE AND COSTS NEARLY NOTHING.** **Say the number.** Then the
  mixed spelling is not a general defect and `[LJ-1.287]`'s win was about depth
  4, which the project should know before it hunts the shape anywhere else.
- **THE SECONDS ARE SOMEWHERE ELSE.** Name that definition. **A profile of an
  unprofiled master is worth the dispatch whatever it finds.**
- **`Key.lagda.md` IS ALREADY CHEAP.** Say its total. Then there is nothing to
  cure and the sweep closes.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. Report a heap exhaustion as a
  wall and **NEVER raise the cap.**

## WHAT YOU MUST NOT DO

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-292/`.
  **`src/` is forbidden for probes** (I-5) and `scripts/check-probes.py`
  enforces it. Copy what you need.
- **Do not edit `src/L/Coding/Key.lagda.md`.** It is delivered and green.
- **Do not edit `src/L/Coding/EnvSupply.lagda.md`.** **A SIBLING IS LANDING A
  CURE IN IT RIGHT NOW** as `[LJ-1.289]`.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure and discard a warm-up.
- **Check your own timing harness.** `[LJ-1.283]` found `time.monotonic()` is
  process-relative on this machine and its first figure was void.
  **`[LJ-1.287]` used agda's own `--profile` Total.** Say which clock you used.
- **Create `agents/tasks/LJ-1-292/lj-1.292-report.md` in your FIRST five
  minutes** and fill it incrementally (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check` on what you write. **No em dash in any
  language.** DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED, AND TWO WERE WRITTEN THIS WEEK

**C-42. A refutation measures the site it names.** This task IS that law
applied.

**C-50, written 2026-08-15. Profile before you cure, and P-y prices a seal's
COST while saying nothing about its BENEFIT.** `[LJ-1.287]` obeyed it and that
is the only reason the 476 seconds were found. **Three diagnoses were refuted by
the profile, including R-35's and R-40's shallow-index restatement and my own.**

**AND THE SEAL'S BLIND SPOT IS MEASURED.** `[LJ-1.287]` replayed a void seal arm
under the profiler and found 99.25 percent of the bill charged to the read lemma
that made the seal usable. **A seal MOVES a cost; it does not remove one.** Do
not propose one here without a profile behind it.

**P-t. An average hides the term.** **P-l. A cure at one site is a hypothesis at
another.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`Key.lagda.md` is in the GCH closure**, which `scripts/ledger.py --reuse` now
prints for the first time in this project's history at 39.1 percent shared.
**Say whether the definition you charge is tower-neutral**, so its seconds are
paid once, or per-tower and paid twice. **NAME YOUR AXIS** (C-46): DD4's own
axis is AC-against-GCH, fixed in code at `scripts/ledger.py:50`, and it is not
Devlin's Def-against-J.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-287/lj-1.287-report.md` read WHOLE: the six-way bisect, the
mechanism, and the sweep it flagged. `agents/tasks/LJ-1-263/lj-1.263-report.md`:
the task that landed `union∈Lset-suc` into `Key.lagda.md`.
`archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

Nothing in the literature governs elaboration cost. Say so in one line and
return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-287/lj-1.287-report.md` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-292/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **C-42.** The sweep. The centre of this task.
- **C-50.** Profile before you cure.
- **P-t, P-l, P-m, P-q, P-y.** **R-35, R-40**, both REFUTED as cures at the
  first site; do not assume they fail here without measuring.
- **P-h, P-i, P-k, P-n, P-s, R-34, R-38. C-12, C-22, C-32, C-36, C-39, C-40,
  C-44, C-45, C-49. I-5. DD0, DD8, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- **No em dash in any language.** Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with `Key.lagda.md`'s cold total and the definition the profile charges
most, at `file:line`, with its ms and its share.** Then whether it is the mixed
spelling. Then the treated arm, or why there is none. Then which clock you used.
Then the DD4 answer with its axis. **Mark every negative MEASURED or INFERRED.**
