# LJ-1.67: abstract the stack, one row, measured

tier: codex (default)

## GOAL

`[LJ-1.66]` priced one `EnvSet` application at **1.016 s** and the eighteen
at **18.29 s**. The hoist failed because it kept re-elaborating the body per
site. **Try the other cure: abstract the stack, so nothing unfolds.** One
row, measured, then stop.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `876b7c6`.
**The working tree carries an uncommitted, GREEN placement**:
`src/L/Condensation.lagda.md` at 6,390 in-fence lines against HEAD's 5,562.
`[LJ-1.66]` left it byte-identical to its own start. **Do not discard it.**

## WHAT IS MEASURED, and none of it is to be re-run

| move | measured | |
|---|---:|---|
| **one `EnvSet` application** | **1.016 s** | the target: 18 of them = 18.29 s |
| `KFacts` bundle on the chain | -30 s | worked, banked |
| `Lift12Back` / `Lift12Out` | 4.28x | worked, banked |
| `StageCardinal` dead cluster | -9.85 s | worked, committed |
| birth-site sealing | +1.61 s | REGRESSED |
| hoist to shared frames, **chain**, abstract args | +17.23 s | REGRESSED |
| hoist to three frames, **band**, concrete slots | **+10.88 s** | REGRESSED |
| `TwelveAgree` alias | +3.29 s | REGRESSED |
| band record bundle, one family | -0.06 s | under the line |
| row-level cure of the three hot rows | ~1.3 s ceiling | cannot reach 2.33 |
| deleting the band | rejected | it is the discharge of 24 hypotheses |
| dropping `V.Presentation` | still over by 1.92 s | dead |

**Module-application hoisting is MEASURED FALSE at two sites. Do not try a
third hoist.**

## THE DIAGNOSIS, and it is a law violation

Read `src/L/Condensation.lagda.md:3560-3576`. `NegAgree.out` is:

```agda
out : ⟨ γ ⊨ negClauseAt C T B ⟩ → ⟨ γ ⊨ φB ⟩
out h = λ c c∈ ar arK a aK yc ycK shB hc ya yaK E EK hsub henv →
  let shD = UnaryShape.out {m} N K 5 (yc ∷ a ∷ ar ∷ c ∷ γ) tagEq shB
      module E' = EnvSet {6 + m} zero ...
                     (E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ) entryK ...
```

**The stack variables `c ar a yc ya E` are LAMBDA-BOUND, and the `EnvSet`
application sits inside that lambda, at the concrete cons-stack
`(E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ)`.**

**P-h (`dev/LESSONS.md:174`) says the opposite is required:** the walk's
arguments are **parameters of a module, not of a function**, and they **stay
ABSTRACT through the walk**, so that "memberships and equations flow but
nothing unfolds".

**A concrete cons-stack is exactly what does unfold.** `lookup` on
`E ∷ ya ∷ yc ∷ a ∷ ar ∷ c ∷ γ` reduces; `lookup` on an abstract
`γ' : S ^ (6 + m)` does not. `EnvSet`'s body is three site-fact hypotheses,
two formula definitions, three `appAt-adequate` transport lemmas and two
direction proofs, and every one of them is re-elaborated against that
reducible stack, eighteen times.

**This is `[LJ-1.25]`'s measured cure at a new site.** There, the cost was a
transport across a transparent index, and **abstracting the SOURCE won
12.8x**, landed for 7 lines, 41.21 s to 11.22 s. Nobody has applied it to
the band.

## WHAT TO BUILD, one row only

Take **`NegAgree`** (`:3520`), which holds two of the eighteen sites
(`:3563`, `:3590`).

**Give the row an inner module whose parameters are the stack and its facts,
kept ABSTRACT.** The shape to aim at: a module parameterized by
`(γ' : S ^ (6 + m))` plus the site facts stated at `γ'`, containing what
`out` and `back` currently compute inside their lambdas. The `EnvSet`
application then happens once against `γ'`, where `lookup` cannot reduce,
and the row's `out`/`back` instantiate it at their own stacks.

**This is a re-parameterization, not a weakening.** The logical content of
`out` and `back` must be identical: same hypotheses, same conclusions, both
directions. **`(x : S) → A x → B x` becoming a module parameterized by
`(x : S)` with `out : A x → B x` is permitted and is exactly what P-h
prescribes. Anything that proves less is not.**

**If you cannot keep the content identical, STOP and write the term you
could not write** (C-36).

## THE ABORT CRITERION, fixed in advance per D-1

Measure `L.Condensation` cold, three runs each side, same session, gate
caliber, loads reported.

- **The row's two sites save 1.0 s or more** (a pro-rata share of 18.29 s
  across two of eighteen sites): **GO. Then STOP and report anyway.** I want
  one row's number before the other eight are funded.
- **Saving under 1.0 s, or any regression**: **STOP and report the price.**

**Either way this dispatch ends after ONE row.** Do not convert the other
rows, the chain, `levelIn` or `cover`.

You need not run `check-ratio --check`. **I run the wing gate myself.**

## WHAT YOU MUST NOT DO

- **Do not try another module-application hoist.** Two sites, two
  regressions. This dispatch is about where the parameters are BOUND, not
  about adding a layer.
- **Do not delete the band or any part of it.** `TwelveAgree` takes 24
  hypotheses and the band DISCHARGES them; `[LJ-1.64]` deleted it, the gate
  passed, and I reverted it. That is C-35.
- **Do not delete content to buy the ratio.** P-q, and `[LJ-1.65]` measured
  it here: -46 lines at zero seconds moved the ratio 0.015515 to 0.015618,
  the wrong way.
- **You may not weaken a statement and you may not narrow a direction.**
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or
**INFERRED**, in those words. **A negative that rests on an inference sets no
verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker, so it is stated in every brief and
answered in every return.

An abstract-stack module is MORE generic: the walk states its facts at an
abstract environment and the J tower instantiates it at its own. **Say
whether the row's statements and proofs are unchanged**, and whether the
shape generalizes to the other eight rows or is special to `NegAgree`.

## ARCHIVE (DD18)

- **`_build/lj-1.66-report.md`**, read WHOLE. The unit cost, the hoist's
  regression, and its section 4 finding that the eighteen sites differ in
  their environments and site facts, which is why a concrete hoist cannot
  work and why this dispatch attacks the binding instead.
- **`_build/lj-1.25-report.md`** and `_build/lj-1.24-report.md`, read WHOLE.
  **The abstract-the-source cure, 12.8x. This is the shape you are copying.**
- `_build/lj-1.65-report.md`, the band bundle's NO-GO.
- `_build/diag-dd24-residual.md` section 1, the band attribution.
- `dev/LESSONS.md` **P-h (`:174`)**, P-l (`:2305`), P-m (`:2460`), P-t
  (`:2601`), P-q (`:2633`), read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and
spend nothing.

## SCOPE (read)

`src/L/Condensation.lagda.md:3520-3620` (`NegAgree`, both sites) FIRST, then
`:2761-2860` (`EnvSet`), then `_build/lj-1.25-report.md`, then
`dev/LESSONS.md:174` for P-h.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ167*.agda`. Your report is
`_build/lj-1.67-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every
statement.

- **P-h.** Module-parameterized, never function-parameterized, and the
  parameters STAY ABSTRACT. **This brief is P-h applied to the band.**
- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-i.** The conversion-explosion playbook: select the cure by its
  decision tree, not by trial.
- **P-k, P-l, P-m, P-n, P-o, P-q, P-t, P-u, P-v** as above.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-13, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **The tree carries uncommitted work
  that is not in HEAD.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load
  average beside every absolute figure**, and say if the two sides of a pair
  ran at different loads.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.67-report.md` incrementally, skeleton first.

**Lead with the row's measured before and after**, three runs each side, one
caliber, with the spread and the load, and say whether the statements are
unchanged. Then the arithmetic: this row's saving against 18.29 s across
eighteen sites. Then whether the shape generalizes to the other eight rows.
**Mark every negative MEASURED or INFERRED.** Then the DD4 answer and **the
convergence answer.**
