# LJ-1.306: port the clean 23 `Agree` modules generic, wave 1 of `q'`

tier: pi (pi-subagent-mode), **model `glm-5.3`**. I ran
`scripts/dispatch/dispatch_policy.py` and took the head it gave. **`scripts/`
moved today**: `rules.py` is `scripts/dispatch/rules.py`, the linters are
`scripts/gate/`, `ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**`q'` is `[LJ-1.7]`'s only remaining route and its whole cost is now measured.
This is wave 1: the part everything else waits on.**

**The route, all four parts measured at BUILT sites:**

| part | lines | measured by |
|---|---:|---|
| **the clean 23 `Agree` modules, generic** | **~180** | **`[LJ-1.298]`, ZERO changed lines at one site** |
| the dirty seven's ambient ties | ~100 | `[LJ-1.302]` |
| `StepAgree` and `ApproxAgree` | ~190 | `[LJ-1.304]`, both built |
| the composite's type | writable, and it FEEDS | `[LJ-1.302]` |

**Build the first row.**

## PREMISES

- **The port is MECHANICAL at the measured rate. `[LJ-1.298]` re-instantiated
  `TagAgree` with the class as a module parameter and ZERO of its 33 lines
  changed**, verified by `diff` against
  `src/L/Condensation.lagda.md:6666-6669`, `:1484-1487` and `:6670-6697`.
  **RE-DERIVE that at a SECOND module before you trust it for 23** (C-42:
  one site is one observation).
- **23 of the 30 are clean, 3,511 lines**: their text names nothing outside
  `GenModel`'s deliveries, the chapter's own `*BS` syntax and its pre-family
  helpers. **`[LJ-1.298]`'s sweep found them; VERIFY the list before porting.**
- **The scaffold is ~38 lines and ONE serves the whole chapter**, the way
  `GenSequence`'s header serves all of `L.Coding.Sequence`.
- **`[LJ-1.298]`'s `GenTagAgree.agda` exists** and is the pattern. Read it.

## WHAT TO BUILD

**A generic port of the clean 23, in your own task directory, with ONE
scaffold.** Not all 23 if the budget will not carry it: **port as many as you
can and report the COUNT and the changed-line total.** **A partial port with an
honest count is worth more than a claim about 23.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE PORT RUNS AT THE MEASURED RATE.** Report the count ported, the changed
  lines, the scaffold's size, and the cold seconds. STOP.
- **A MODULE IS NOT CLEAN AFTER ALL.** **Name it and what it reaches for.**
  `[LJ-1.298]`'s sweep was textual; **a name can hide behind an alias.** That
  correction is worth more than three more ports.
- **THE RATE IS NOT ZERO.** **Say the real changed-line count.** The 180 rests
  on one site and P-l says that is a hypothesis for the other 22.
- **THE SCAFFOLD DOES NOT SERVE THEM ALL.** If each module needs its own, the
  180 is wrong by a large factor. **Say so with the count.**
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **`Condensation` is 132 s cold
  on its own; prefer copied fragments to the whole chapter.** NEVER raise the
  cap.

## CONSTRAINTS

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-306/`.
  **`src/` is forbidden for probes** (I-5). **The landing is a separate task
  once the count is known.**
- **Do not edit `src/L/Condensation.lagda.md`.** Copy from it.
- **A SIBLING IS LIVE** in `agents/tasks/LJ-1-305/`. Do not touch it.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-306/lj-1.306-report.md` in your FIRST five
  minutes** (C-22).
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `scripts/gate/lint-agda.py --check`. **No em dash in any language.** DD23
  freezes mathematical prose.
- Count with `.venv/bin/python scripts/measure/ledger.py`.
- Evidence is `file:line`. Write ASD-STE100. Mark every negative MEASURED or
  INFERRED, in those words.

## THE RULES THIS CHAIN EARNED

**P-l. A construction delivered at one carrier is a HYPOTHESIS at another.**
**Three times this week the generic port came in cheaper than feared. Do not let
that make you optimistic: measure the second module before you trust the
twenty-third.**

**C-42. A refutation measures the site it names.** **The zero-changed rate is
one site.**

**P-h. Definability walks are module-parameterized, never
function-parameterized.** **That is exactly what a generic class parameter is.**

**R-41, written today.** **Depth is free and MIXED SPELLING costs**, gated at
depth 4. **If a port is slow, look for a type and a body naming one object two
ways before anything else.**

**C-44.** Every figure here is `[LJ-1.298]`'s.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **THIS TASK IS DD4 ITSELF**: it takes a chapter
written at one carrier and makes it serve two. **Say what the port would cost
the J tower to re-instantiate, and NAME YOUR AXIS** (C-46): this is the port's
L-against-ambient axis, and DD4's own axis is AC-against-GCH.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-298/lj-1.298-report.md` read WHOLE, and its
`GenTagAgree.agda`, the pattern. `agents/tasks/LJ-1-302/lj-1.302-report.md` for
what the dirty seven need, so you do not port into their shape by accident.
`agents/tasks/LJ-1-238/` for `GenSequence`, the generic port that paid.
`archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

No literature bears on a mechanical re-instantiation. Say so in one line and
return a **LITERATURE USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-298/GenTagAgree.agda` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-306/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **OPEN the full entry for any law you act on.**

- **D-1, D-10, C-22, C-42, C-44, P-h, P-k, P-l, P-m, P-n, R-35, R-38, R-40,
  R-41, I-5, C-12.**
- **P-i, P-t, P-y, R-34. C-32, C-36, C-38, C-39, C-40, C-45, C-49, C-50. DD0,
  DD8, DD18, DD24, D-26.**

## RETURN

**Lead with the COUNT ported and the changed-line total.** Then the scaffold's
size and whether one served them all. Then any module that was not clean. Then
the cold seconds. Then whether the 180 stands. Then the DD4 answer with its
axis. **Mark every negative MEASURED or INFERRED.**
