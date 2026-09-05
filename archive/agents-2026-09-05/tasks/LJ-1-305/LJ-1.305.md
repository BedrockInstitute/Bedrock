# LJ-1.305: untruncate the descent, and deliver `SqShape`

tier: pi (pi-subagent-mode), **model `glm-5.3`**. I ran
`scripts/dispatch/dispatch_policy.py` and took the head it gave. **`scripts/`
moved today**: `rules.py` is `scripts/dispatch/rules.py`, the linters are
`scripts/gate/`, `ledger.py` is `scripts/measure/ledger.py`.

## GOAL

**This is `[LJ-1.8]`'s WHOLE remaining gap. Close it or measure that it cannot
close.**

`[LJ-1.301]` built the descent, `--safe`, exit 0, 241.9 s, 186 lines:

```agda
sq-descent : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
           → ⟨ isL α ⟩ → ∥ sq α ∥₁
```

**It delivers a PROPOSITION at each ordinal. `SqShape` needs the untruncated
function object**, and after this morning's parenthesis fix `SqShape`'s
conclusion is `(⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫`, a Σ-type carrying an
injection and its proof. **A `∥_∥₁` cannot be stripped to that without a
reason.**

## PREMISES

- **`sq-descent` is green and delivers the truncated form**, at
  `agents/tasks/LJ-1-301/Descent.agda:261-263`. **Read the WHOLE file first**
  and re-run it, so your control is yours (C-44).
- **`[LJ-1.301]`'s section 4 says why it truncated and what the untruncated form
  still owes. READ IT. It is the brief's own starting point** and it may already
  name the obstruction.
- **`SqShape` was FIXED today.** `src/L/GCH.lagda.md:47` now reads
  `(⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫`. **Any report written before 18:00
  measured a different object** (C-32).
- **`_↪_` is a Σ-type**, `src/L/Cardinal.lagda.md:47-50`. **So the target is not
  a proposition and the truncation is not free to drop.** VERIFY.

## THE THREE ROUTES, and I do not know which is right

**1. THE CHOICE IS UNIQUE, so the truncation is removable.** If `sq α`'s
injection is unique up to the equality the type carries, `∥_∥₁` eliminates into
it. **Check whether `sq α` is an hProp**, or can be made one by quotienting.
**This is the clean answer if it holds.**

**2. THE DESCENT CAN CARRY THE UNTRUNCATED OBJECT.** The truncation may be an
artifact of how the step combines its recursive calls, not of the mathematics.
**Read the step. If the truncation enters at ONE join, say where and whether a
choice principle already in the module telescope removes it.** `lem` is a
module parameter throughout this tree.

**3. IT CANNOT BE REMOVED AND `SqShape` MUST BE RESTATED TRUNCATED.** **That
changes the trophy's statement, so it is the OWNER's and not yours.** **If you
conclude this, STOP and report it: do not edit `src/L/GCH.lagda.md`.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE UNTRUNCATED FORM BUILDS.** Report the term, its lines, its cold seconds,
  and which of the three routes you took. **Then `[LJ-1.8]`'s gap is closed.**
  STOP.
- **IT NEEDS A CHOICE PRINCIPLE NOT IN THE TELESCOPE.** **Name it exactly** and
  say what adding it would cost the tree's classical boundary. **DD9 says the
  whole tree is `--safe` with LEM as an explicit parameter; a new principle is a
  real change and the owner rules on it.**
- **`sq α` IS NOT AN hProp AND CANNOT BE MADE ONE.** **Give the term or the
  countermodel** (C-36). Then route 1 is closed and say whether 2 survives.
- **THE TRUNCATION IS UNREMOVABLE.** **That is a real answer and the most
  consequential one.** It sends the trophy's statement to the owner.
- **A WALL.** **A single `agda` invocation past 30 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **The control alone is 242 s;
  budget for it.** NEVER raise the cap.

## CONSTRAINTS

- **THIS IS A PROBE. LAND NOTHING.** Write and run in `agents/tasks/LJ-1-305/`.
  **`src/` is forbidden for probes** (I-5).
- **DO NOT EDIT `src/L/GCH.lagda.md`.** Its statement is the trophy.
- **`agents/tasks/LJ-1-301/` is a FROZEN record.** Read it, copy from it, write
  nothing into it.
- **A SIBLING IS LIVE** in `agents/tasks/LJ-1-306/`. Do not touch it.
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** Report the
  load beside every absolute figure.
- Never `src/Everything.lagda.md`, never `dev/ledger.toml`, never
  `dev/PLAN.md`, never `src/L/Choice/Name.lagda.md` (DD23).
- **Create `agents/tasks/LJ-1-305/lj-1.305-report.md` in your FIRST five
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

**C-32. A cure invalidates every downstream measurement.** **`SqShape` changed
at 18:00 today.** Read current source, never a report written before it.

**D-10. Price the truth of a recorded residue before pricing its proof.**
**`[LJ-1.301]` recorded「truncated」. Whether that is a limitation of the proof
or of the mathematics is exactly this task.**

**C-45. Audit the INSTANTIATION, never the telescope.**

**C-36. A failed substitution is not a proof of impossibility.**

**C-44.** Every claim here is `[LJ-1.301]`'s or mine.

**A STOP IS A DELIVERABLE.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **A descent over ordinals names no tower.** Say
where the untruncated form belongs under P-k, and **NAME YOUR AXIS** (C-46):
DD4's own axis is AC-against-GCH, and `src/L/Ordinal/SquareLaw.lagda.md` is
already in the GCH closure through `src/L/Cardinal.lagda.md:22`.

## ARCHIVE (DD18)

`agents/tasks/LJ-1-301/lj-1.301-report.md` read WHOLE, especially section 4, and
its `Descent.agda`. `agents/tasks/LJ-1-300/lj-1.300-report.md` for what the
parenthesis fix voided. `agents/tasks/LJ-1-294/` for `κ-limit`.
`archive/dev/TASKS-archived.md`, taking SHAPE and never a claim. Return an
**ARCHIVE USED** section naming ONE line read per archived file.

## LITERATURE (DD18)

**`[LJ-1.300]` MEASURED that Devlin II.5 never states a square law at all.**
**So say whether the truncation question has any counterpart in the
literature**, and if not, that it is the port's own. Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-301/Descent.agda` FIRST, whole.

## SCOPE (write)

`agents/tasks/LJ-1-305/` only.

## MANDATORY RULES

Run `.venv/bin/python scripts/dispatch/rules.py --for probe` and read every
statement. **OPEN the full entry for any law you act on.**

- **D-1, D-10, C-22, C-32, C-36, C-44, C-45, C-50.**
- **P-h, P-i, P-k, P-l, P-m, P-n, P-t, P-y, R-34, R-35, R-38, R-40, R-41.
  C-12, C-38, C-39, C-40, C-42, C-49. I-5. DD0, DD8, DD9, DD18, DD24, D-26.**

## RETURN

**Lead with ONE word: BUILDS, NEEDS-A-PRINCIPLE, or UNREMOVABLE.** Then the
term, or the exact principle, or the countermodel. Then which of the three
routes you took and why the others failed. Then whether `sq α` is an hProp.
Then the DD4 answer with its axis. **Mark every negative MEASURED or INFERRED.**
