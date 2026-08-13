# LJ-1.73: does the repaired TwelveAgree instantiate at an ABSTRACT frame?

tier: codex (default)

## GOAL

**One question, cheaply.** `[LJ-1.72]` measured that instantiating the
repaired `TwelveAgree` at a CONCRETE cons-env heap-walls. **Does it
instantiate at an ABSTRACT env?** That answer decides the architecture.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, **clean at
`d0a6658`**. HEAD is green: I reverted `[LJ-1.72]`'s repair because it left
the master non-compiling. **The repair is backed up outside the repository
and you rebuild it from its report, which carries every line reference.**

## WHAT IS MEASURED, so you rebuild rather than rediscover

`[LJ-1.72]` built the statement repair and it is SOUND:

- `TwelveAgree`'s universal `tagEq` and `numK` become twelve per-row fields
  each, the `KFacts` shape. `[LJ-1.71]`'s refutation no longer applies.
  **Checked green in isolation, 133 s.**
- `SatGraphAgree`'s frame gains the forty union facts, 35 to 75.
  **Checked green in isolation, about 130 s.**
- All sixty-nine facts of the repaired telescope have suppliers at the frame.

**And the instantiation walls, MEASURED:**

| configuration | result |
|---|---|
| the telescope with an EMPTY body, same 69 arguments, concrete env | **green, about 105 s** |
| the telescope with its body, concrete env, isolated | **WALL, about 210 s** |
| the same in the full master | **WALL, about 1003 s** |
| `envHypB2` sealed opaque, concrete env | **WALL, about 220 s** |

**The mechanism is measured**: the module application re-elaborates
`TwelveAgree`'s where-block, the twelve row applications, at the graph
frame's concrete cons-env `(f ∷ e ∷ d ∷ γ)`.

**Read `_build/lj-1.72-report.md` WHOLE. Rebuild its repair from sections 1a
and 1b; do not redesign it.**

## THE QUESTION

`lookup` on a concrete cons-chain `(f ∷ e ∷ d ∷ γ)` reduces. `lookup` on an
abstract `γ' : S ^ (11 + n)` does not. **P-h says the walk's parameters stay
ABSTRACT so that nothing unfolds.**

**So: apply the repaired `TwelveAgree` at an abstract `γ' : S ^ (11 + n)`,
with the sixty-nine facts stated at `γ'`, and measure.**

- **If it is green and affordable**, the architecture is settled: the
  discharge happens where the environment is still abstract, and the concrete
  frame is reached by instantiating that module, not by applying
  `TwelveAgree` inside a concrete frame. **Say what the consumer would then
  have to do**, and whether `SatGraphAgree` can be restructured to take the
  discharge that way.
- **If it also walls**, then `TwelveAgree`'s where-block is unaffordable at
  ANY frame, and the twelve-row composition has to be built differently.
  **That is the more valuable answer** and it goes to the owner.

**A probe answers this. You do not need to make the master green.**

## THE ABORT CRITERION, fixed in advance per D-1

- **Abstract application green**: report its seconds, then measure the same
  thing at the concrete env for the contrast, and **STOP**. Do not restructure
  `SatGraphAgree`, do not touch `LeafAgree`, `levelIn` or `cover`.
- **Abstract application walls**: **STOP immediately** and report both walls
  with their seconds.

**Either way this dispatch ends at that one comparison.** It is a probe, so
**you may leave the master untouched entirely**; `src/ProbeLJ173*.agda` is
enough.

**Name probes `src/ProbeLJ173*.agda`, not `.lagda.md`.** `[LJ-1.72]` used
`.lagda.md` and `check-fences` counted five probes as masters. I fixed the
ignore list; use the `.agda` shape anyway.

## WHAT YOU MUST NOT DO

- **Do not raise the heap cap.** C-12: `GHCRTS="-A64m -I0 -M8g"`, one
  process, cap never raised. **A heap exhaustion is a WALL with its seconds,
  and it is a result, not a failure.**
- **Do not leave the master non-compiling.** If you edit it at all, revert
  before you finish, and say the tree is byte-identical to your start.
- **Do not interpose a module that re-exports another.** P-w: measured false
  at four sites.
- **You may not weaken a statement and you may not narrow a direction.**
- **Do not touch anything under `src/L/Coding/`.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

An abstract-frame discharge is the more generic shape and the J tower would
inherit it directly. **Say whether your answer changes what the J tower
pays**, and mark it MEASURED or INFERRED.

## ARCHIVE (DD18)

- **`_build/lj-1.72-report.md`**, read WHOLE. **Sections 1a and 1b are the
  repair to rebuild; section 4 is the wall table.**
- `_build/lj-1.71-report.md` and `src/ProbeLJ171A.agda`, the refutation that
  made the repair necessary and the confirmation that the slot fix holds.
- **`_build/lj-1.25-report.md`** and `_build/lj-1.24-report.md`, the
  abstract-the-source cure that measured 12.8x. **This dispatch is that
  question at a new site**, and P-l says a measured cure does not transfer by
  analogy, so measure it.
- `_build/lj-1.67-report.md`, where an abstract-stack move at the ROW level
  regressed +2.82 s. **Different site: that one interposed a module inside a
  proof body; this one changes what the application's env is.**
- `dev/LESSONS.md` P-h (`:174`), C-38, C-35, P-w as amended, P-o (`:2509`),
  P-t (`:2601`), P-l (`:2305`), read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend
nothing.

## SCOPE (read)

`_build/lj-1.72-report.md` sections 1 and 4 FIRST, then
`src/L/Condensation.lagda.md:6412-6470` (`TwelveAgree` as committed) and
`:6608-6660` (`SatGraphAgree`'s frame), then `src/ProbeLJ171A.agda`.

## SCOPE (write)

`src/ProbeLJ173*.agda` only, and `src/L/Condensation.lagda.md` **only if you
revert it before finishing**. Your report is `_build/lj-1.73-report.md`.
**Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-h.** Module-parameterized, and the parameters STAY ABSTRACT. **This
  brief is P-h applied to the discharge.**
- **C-38.** A hypothesis is discharged when something SUPPLIES it.
- **P-i.** The conversion-explosion playbook: select the cure by its decision
  tree, not by trial.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as above.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35.** State the membership at the SMALL index and climb.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **HEAD is green and the tree is clean;
  leave it that way.**
- Do NOT run `make check`. You need not run `check-ratio`.
- **Run `scripts/check-fences.py --check` before you report anything closed**,
  and confirm it reads 84 masters.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` on
  anything you touch.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.73-report.md` incrementally, skeleton first.

**Lead with whether the repaired `TwelveAgree` applies at an ABSTRACT env,
green or wall, with its seconds**, and the concrete-env contrast at the same
caliber. Then, if green, what a consumer would have to do to use it that way.
**Mark every negative MEASURED or INFERRED.** Then the DD4 answer and **the
convergence answer.** Confirm the tree is byte-identical to your start.
