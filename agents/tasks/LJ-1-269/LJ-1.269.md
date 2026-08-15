# LJ-1.269: scout a named-slot layer, and change nothing

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.**

## GOAL

**The owner asked whether the arity arithmetic could be packaged so it is not
written ad hoc each time. The answer I gave, from the source, is that the
ARITHMETIC is already typed and the ad hoc part is the SLOT LAYOUT.**

**Scout it. Land nothing. This is a map for later, not a change.**

**The owner's instruction, in their words: 先摸清楚前面路子的大概样貌,以备
未来之需.** **So the deliverable is a SHAPE and a PRICE, and no edit anywhere.**

## THE EVIDENCE THAT POINTS AT SLOTS RATHER THAN ARITY

**The arity arithmetic is typed and discharges itself.**
`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:140-142`:

```agda
closeN : {n : ℕ} → (k : ℕ) → Formula (⊥*) (k + n) → Formula (⊥*) n
```

**The `k + n` is in the type. Nobody hand-computes it.**

**What IS hand-written is the slot permutation, and its specification lives in
a comment.** `ProbeLJ1241A.agda:106-112`:

```agda
ρ : Fin 16 → Fin 16
ρ zero                      = zero
ρ (suc zero)                = inject+ {15} {1} (fin-suc 14)   -- v → 14
ρ (suc (suc zero))          = fin-suc 15                       -- γ → 15
ρ (suc (suc (suc zero)))    = suc zero                         -- K → 1
ρ (suc (suc (suc (suc i)))) = inject+ {14} {2} (suc (suc i))   -- δᵢ → 2 + i
```

**And the tree has already MEASURED the symptom.** Commit `c8a628b`,
`[LJ-1.173]`'s own words:

> It patched by NAME first and Agda refused four times: the same field arrives
> in the master under FOUR local names, and one module binds its arity under a
> different letter entirely. What worked was patching by SHAPE, taking each
> entry's own binder.

**「The same thing under four names」is the symptom of a missing named-slot
abstraction, and it cost four Agda rounds.**

## THE THREE THINGS TO BRING BACK

**1. THE CENSUS.** **How many hand-written slot permutations and slot pins
exist**, across `src/` and the probes? **Give the count and the sites at
`file:line`.** **A permutation is `Fin n → Fin m` written by clause; a pin is a
conjunct asserting `lookup i γ ≡ something`.** **The census is the number that
says whether this is worth anything.**

**2. THE SKETCH, and it is the smallest thing that answers the question.**
**Build a MINIMAL named-slot layer in your own probe and show whether it
typechecks at all**: a slot layout as data, the `Fin` position derived from it,
and ONE of the census's permutations re-expressed through it. **If it does not
typecheck, name the term** (C-36). **That is the whole point of a scout.**

**3. THE PRICE, from the REWRITE SIDE (DD13).** **Price the ideal form written
fresh today, then compare.**「We already paid for the existing form」decides
nothing in either direction. **Give: the layer's own lines, and the lines it
would DELETE at the census's sites.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE SKETCH TYPECHECKS AND THE CENSUS IS LARGE.** Report both, and the DD13
  comparison. **Then the map says GO and the owner decides when.** STOP.
- **THE SKETCH TYPECHECKS AND THE CENSUS IS SMALL.** **Say the count plainly.**
  **A layer that abstracts three sites is worse than three hand-written
  functions, and saying so is the right answer.**
- **THE SKETCH DOES NOT TYPECHECK.** **Name the term** (C-36). **A named-slot
  layer that Agda will not accept is the most valuable thing you can return,
  because it closes the question for good.**
- **AGDA REFLECTION IS THE RIGHT TOOL AFTER ALL.** **I judged it is not: I
  grepped `src/` and found ZERO precedent, two hits that are the MATHEMATICAL
  reflection principle and the catalog.** **If you disagree, say so with
  evidence.** C-44: my grep is a claim.
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect.

## WHAT YOU MUST NOT DO

- **CHANGE NOTHING OUTSIDE YOUR OWN TASK DIRECTORY.** **No master, no ledger,
  no plan, no other probe.** **The owner said explicitly: no landing changes.**
- **Do not refactor anything.** **You write a SKETCH in your own file. You do
  not touch the sites the census names.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not touch `agents/tasks/LJ-1-266/`.** A sibling is live there.
- **A probe goes in `agents/tasks/LJ-1-269/`**, tracked, never deleted.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the load beside every absolute figure.**
- **Report a heap exhaustion as a wall.** Never raise the cap.
- **Create your report file in your FIRST five minutes (C-22).**
- Never `src/Everything.lagda.md`. Never commit, never push, never
  `git checkout .`, `git stash`, `git reset --hard` or `git clean`.
- Do not run `make check`; the orchestrator runs it.

## DATE YOUR MEASUREMENTS, because this report is for LATER

**C-32: a cure invalidates every measurement downstream of it.** **This map
will be read weeks from now, after landings that will move the census.**

**So write every figure with the date and the commit it was taken at**, and say
in one line what would make each figure stale. **A map with no date is a map
nobody can trust later.**

## THE TIMING IS NOT YOURS TO JUDGE, and I say so plainly

**I already told the owner this refactor should NOT run now**, because step 6's
28 fields just became reachable, two landings just entered `src/`, and
`[LJ-1.266]` is measuring seconds right now. **C-32 would void all of it.**

**So do not recommend a schedule.** **Give the shape and the price. The owner
picks the moment.**

## EIGHT RULES THIS CHAIN EARNED

**DD13: price the ideal form written fresh today, from the REWRITE side.**
「We already paid for it」never decides the question, in either direction.

**DERIVE A FIGURE OR DO NOT WRITE IT** (C-44). **My reflection grep is a claim
and so is my reading of `ρ`.**

**A PROBE'S IMPORTS ARE A CONSUMER GRAPH NOTHING CHECKS.** **Learned today,
the hard way, when a file move blocked two blocks.**

**`exit 0` IS NOT A SUPPLY** (C-45).

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**AN ESCAPE HATCH IS THE SHAPE A WRONG CHOICE HIDES IN** (C-43).

**CHECK THE TREE BEFORE YOU CALL SOMETHING ABSENT.**

**SEARCH THE OPEN-WORK LIST BY CONTENT, NOT BY NAME.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**A slot layout is pure syntax over `Fin n` and it names no tower.** **So a
named-slot layer would be shared by both towers by construction, and that is
an argument FOR it that has nothing to do with seconds.**

**Say whether the census's sites are tower-neutral**, and **NAME YOUR AXIS**:
`[LJ-1.262]` measured that this phase mixes Devlin's Def-against-J with the
port's L-against-ambient, and no figure says which.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-150`**: `ρ`, `pins`, `closeN`
  and `φ₀`. **The specimen.**
- **`src/FOL/Manipulation/`, all five files**: `Renaming.lagda.md` 163 lines,
  `Relabelling.lagda.md` 260, `Bounding.lagda.md` 248, `Parameters.lagda.md`
  484, `Relativize.lagda.md` 177. **I counted those myself. This is the layer a
  slot abstraction would sit beside, not replace.**
- **`src/FOL/Syntax.lagda.md:44`**: `var : Fin n → Term K n`, the de Bruijn
  variable. **There is no freshness anywhere and that is why this is a layout
  problem rather than a binding problem.**
- **`agents/tasks/LJ-1-173/lj-1.173-report.md` and commit `c8a628b`**: the
  four-names episode and the patch-by-shape cure.
- **`archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`.**
  **The retired route wrote formulas too. Did it hand-write slot
  permutations, or did it have something better? Take SHAPE from the archive,
  never a claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether the literature bears on slot layout at all.** It
probably does not, and saying so plainly is the right answer. Return a
**LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-241/ProbeLJ1241A.agda` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-269/` only. **No master, no ledger, no plan, no sibling.**

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for probe` and read every statement.
**The tool prints `Full entry: dev/LESSONS.md:<line>` for every rule and says
THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you act
on.**

- **D-1.** The abort criterion is fixed above.
- **DD13.** **Price from the rewrite side. The centre of this task.**
- **P-h.** Definability walks are module-parameterized, never
  function-parameterized. **A slot layout is exactly the shape P-h is about.**
- **C-36.** Write the term you could not write.
- **C-44.** A brief's claim is unchecked until you check it.
- **C-32.** A cure invalidates every downstream measurement.
- **P-l, P-i, P-k, P-m, P-t, P-y, R-40, R-34, R-35. C-12, C-22, C-38, C-39,
  C-40, C-42, C-43, C-45. I-5. DD0, DD8, DD18, DD24, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with THREE things: the census count, whether the sketch typechecks, and
the DD13 price.** Then the census sites at `file:line`. Then the sketch, or the
term that stopped it. Then what the layer would DELETE. Then the date and
commit of every figure, and what would make each stale. Then the DD4 answer
with its axis. **Mark every negative MEASURED or INFERRED.**
