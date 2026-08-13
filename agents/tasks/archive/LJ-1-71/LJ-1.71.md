# LJ-1.71: consume TwelveAgree, which nothing has ever consumed

tier: codex (default)

## GOAL

**Wire `SatGraphAgree` to instantiate `TwelveAgree`**, discharging its
`twelve-out` and `twelve-back` hypotheses. That is the next wiring step and
it is also the first real audit of a module that was rewritten yesterday.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`c21b417`**. There are no working-tree edits. The leaf adequacy and the
twelve-row discharge are committed.

## WHY THIS ONE FIRST, and it is C-35

`TwelveAgree` (`src/L/Condensation.lagda.md:6412`) was rewritten yesterday:
its twenty-four hypotheses became a forty-seven fact telescope with the
twelve row modules instantiated inside.

**Nothing consumes it. I checked: `TwelveAgree` is instantiated NOWHERE in
the tree**, and `SatGraphAgree` (`:6608`) takes `twelve-out` and
`twelve-back` as parameters instead (`:6618-6623`).

**C-35: a delivered block with no consumer is UNTESTED, and its first
consumer is its first real audit.** Four definitions have been convicted
that way this phase: `oneSameB`, `arTagBS`, `isTmBS` and `satGraphB`. A
fifth was found when the twelve agreements first met their consumer's frame
at all.

**So this dispatch is a build and an audit at once. Report anything it
convicts.**

## THE HISTORY THAT MAKES THIS THE RISKY JOINT

`[LJ-1.54]` found the twelve row agreements **could not be instantiated at
`SatGraphB`'s frame**: the agreements hard-coded slots and the instantiation
needed `suc B = zero`, which has no solution in `Fin`. `[LJ-1.55]`
generalized every row to a full slot tuple to fix it, and proved the
composition in `src/ProbeLJ155B.agda`.

**That fix has never been exercised at the real consumer in a master.**
`ProbeLJ155B` is a probe and probes are never committed.

**So the question this dispatch answers is whether the slot fix holds at the
frame that needed it.** If the instantiation does not go through, say
exactly which index does not match, and STOP; do not reshape a statement to
force it.

## WHAT TO BUILD

Instantiate `TwelveAgree` inside `SatGraphAgree` at the graph frame, and
supply `twelve-out` and `twelve-back` from its `out` and `back`. Those two
parameters then leave `SatGraphAgree`'s telescope.

**`SatGraphAgree`'s statements do not change**, and neither do
`LeafAgree`'s. Only where `twelve-out` and `twelve-back` come from.

**The proofs already exist.** `TwelveAgree.out` and `.back` are proved
(`:6720-6753`). **This is instantiation, not proof.** If you find yourself
proving a row or a composition, stop and say which.

## AND WHILE YOU ARE THERE, ONE MEASUREMENT

`[LJ-1.70]` found that the discharge's mass is the built-tree satisfaction
content, and named **P-w class (c), cheaper types on what is copied**, as
the only untried lever. Its target is the four fact types stating
satisfaction over `envSetAt`, `envOverAt` and `tmValAt`: `envK`, `envInK`,
`valV`, `valW`.

**After you wire the consumption, profile `L.Condensation` once and say
whether those four are still the mass.** Do NOT attempt a class (c) cure;
this dispatch is the wiring plus one observation.

## THE ABORT CRITERION, fixed in advance per D-1

Measure `L.Condensation` cold, three runs each side, same session, gate
caliber, loads reported. **Then run `python3 scripts/check-ratio.py --check`
and quote its aggregate.**

- **The instantiation goes through**: report the cost whatever it is, and
  **STOP**. Do not go on to the post-leaf five, `levelIn` or `cover`.
- **The instantiation does NOT go through**: **STOP immediately** and write
  the term you could not write, with the index that does not match, at
  `file:line`. **That is the most valuable outcome this dispatch can have**,
  because it would mean a fix believed to hold since `[LJ-1.55]` does not.

**Note on the gate's own multiple.** `check-ratio` prints `Nx the AC side`,
which is N times the BASELINE 0.011057, **not** N times the bar 0.012716.
The bar is the baseline times 1.15. **Quote both, or quote the seconds
against the ceiling.** I conflated these for several dispatches and I do not
want it repeated.

## WHAT YOU MUST NOT DO

- **You may not weaken a statement and you may not narrow a direction.**
  Both directions of `TwelveAgree` are needed and that is settled.
- **Do not reshape a statement to make an instantiation go through.** If the
  indices do not match, that is the finding.
- **Do not delete the band or any part of it.** It is the discharge.
- **Do not attempt a class (c) cure.** Observe only.
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`.
- **Count a module's exports by finding its boundary, not by guessing a line
  range**, and say where the module ends if you report a count.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

`[LJ-1.70]` found the frame states its facts at the L tower's slots, so the
J tower needs a second statement rather than a reuse. **Say whether wiring
the consumption changes that**, and mark it MEASURED or INFERRED.

## ARCHIVE (DD18)

- **`_build/lj-1.70-report.md`**, read WHOLE. The frame, the discharge, the
  two heap walls and the class (c) target.
- **`_build/lj-1.55-report.md`** and **`src/ProbeLJ155B.agda:788-979`**, the
  slot fix and the composition this dispatch exercises for the first time in
  a master.
- `_build/lj-1.54-report.md` section 1, the frame mismatch that started this.
- `_build/lj-1.62-report.md` sections 2-3, `SatGraphAgree`'s placement.
- `dev/LESSONS.md` **P-w as amended**, C-35 (`:3173`), P-t (`:2601`),
  P-o (`:2509`), P-m (`:2460`), read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and
spend nothing.

## SCOPE (read)

`src/L/Condensation.lagda.md:6412-6460` (`TwelveAgree`'s telescope) and
`:6608-6660` (`SatGraphAgree`'s) FIRST, then `src/ProbeLJ155B.agda:788-979`,
then `_build/lj-1.70-report.md` section 1.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ171*.agda`. Your report is
`_build/lj-1.71-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **C-35.** A block with no consumer is UNTESTED. **This dispatch is that
  audit.**
- **P-w as amended.** The copy is paid at use; class (c) is the live target.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds**, and this file
  has walled twice at the cap already.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-36, C-37.**
- **D-1, D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree is clean; keep your work
  visible in it.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.71-report.md` incrementally, skeleton first.

**Lead with whether the instantiation went through**, and if it did not, the
index that does not match. Then whether `twelve-out` and `twelve-back` have
left `SatGraphAgree`'s telescope. Then the measured cost, three runs each
side, and the gate's aggregate with BOTH multiples or the seconds against
the ceiling. Then whether the four built-tree fact types are still the mass.
**Mark every negative MEASURED or INFERRED.** Then the DD4 answer and **the
convergence answer.**
