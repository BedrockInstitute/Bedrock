# LJ-1.65: the band bundle, one family, probe-gated

tier: codex (default)

## GOAL

A max-effort diagnosis says the DD24 residual is **band elaboration mass**, not row cost,
and that the cure is the `KFacts` record-bundle shape applied to the row-agreement band.
**Probe ONE family. Do not roll anything out before the probe measures.**

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, at `21f8f26`.
**The working tree carries an uncommitted, GREEN placement**:
`src/L/Condensation.lagda.md` at 6,390 in-fence lines against HEAD's 5,562. **Do not
discard it.** A backup patch exists outside the repository.

## THE DIAGNOSIS, and I verified its arithmetic and its decisive code claim myself

Read `_build/diag-dd24-residual.md` WHOLE. Its findings, with what I checked:

**The residual is a NET figure.** `L.Condensation` is **+18.19 s** over its own bar share;
the other five wing modules run **15.88 s under**. The net is the 2.33 s. **I recomputed
this from the gate's own rows.** Every second of overage lives in one module.

**The band is the mass.** The row-agreement band (`src/L/Condensation.lagda.md:2720-5101`,
2,196 in-fence lines) costs **44.31 s at 0.0202 s/line**, measured as a same-session
before/after pair. **The residual is 5.26 percent of the band.**

**The band's cost is not in its named proofs.** Only 5.8 s sits in profile-visible
definitions. The rest is elaboration mass.

**The band has the KFacts shape. I checked this myself and it is exact.** `AndAgree`
(`:3336-3368`) restates an eleven-entry core

```text
tagEq numK innerK pairK codesK valK keyK transK subK₁ subK₀ someEnv
```

and then passes **all eleven back to `PropAgree` verbatim** (`:3369-3383`). `OrAgree`
(`:3386-3418`) does the same. Across the band: **591 of 2,196 lines are module headers**,
the `tagEq`/`numK`/`innerK`/`codesK`/`valK` family appears 14 times each, `keyK` 29
times, `arSubK` 31, `envInK` 30.

**The same mechanism measured minus 30 s in this file** when `[LJ-1.62]` bundled the
chain's site facts into `KFacts`.

## WHY NOT ROW-LEVEL TREATMENT

The three named rows hold 5.845 s together. Closing 2.33 s from them needs a **40 percent
cut across all three**, and the only lever with a measured precedent among them
(`BinFormAgree`'s depth-3 `PT.rec` chain, the Lift12 shape) tops out near 1.3 s.

**The "P-n payable floor" label was imprecise.** P-n's signature is hot NAMED definitions
at a concrete carrier. This band's profile is the opposite: cost in `Miscellaneous`, names
under 3 s, environment a module VARIABLE. That is **P-t repeated elaboration**, which is
the cure-able class.

## THE PROBE, and it is the whole dispatch

**Convert ONE family in place: `PropAgree` + `AndAgree` + `OrAgree`.** Their eleven-entry
core is restated three times at `:3090-3145`, `:3336-3368` and `:3386-3418`. Replace that
core with **one bundled parameter**, so each module states it once and each application
passes one value.

**Change the PARAMETER SHAPE ONLY. Add no module application layer.** `[LJ-1.63]`'s
attempt 3 added an application layer with abstract arguments and measured **+17.23 s**.
`KFacts` worked because it changed the parameter shape and nothing else.

**The statements and the proofs do not change.** If a proof body needs editing beyond
projecting fields out of the bundle, stop and say so.

## P-o IS THE NAMED RISK, AND IT NAMES ITS OWN CURE

**`dev/LESSONS.md:2509`, P-o: a `record` whose FIELD has a carrier-indexed type HANGS
Agda 2.8.0's elaborator. The identical content written as a right-nested `Σ` checks
immediately.**

The band's core includes `subK₁`, `subK₀` and `someEnv`, whose types carry `⊨`
satisfaction over built `subValAt` trees. **That is the P-o hazard exactly.**

- **Include at least one `subK`-class field in the probe**, before any roll-out, so the
  hazard is measured rather than discovered later.
- **If the record hangs or walls, use the right-nested `Σ`**, which is P-o's measured
  cure. That is not a fallback, it is the law's prescribed action.
- **A heap exhaustion is a WALL with its seconds. Report it; never raise the cap.**

## THE ABORT CRITERION, fixed in advance per D-1

Measure `L.Condensation` cold, three runs each side, same session, at the gate's caliber.

- **GO**: the one family saves **0.5 s or more**, with no regression elsewhere.
  **Then STOP and report anyway.** Do NOT roll out the remaining families in this
  dispatch. I want the first family's number before the rest is funded.
- **NO-GO**: saving under 0.5 s, any measured regression, or a P-o hang or heap wall.
  **STOP and report the price.**

**Either way this dispatch ends after ONE family.** Do not attempt the env family, the
chain, `levelIn`, or `cover`.

You need not run `check-ratio --check`; a `L.Condensation` before/after pair at the
gate's caliber is what this probe decides. **I run the wing gate myself.**

## WHAT IS ALREADY MEASURED, so you do not re-run it

| move | measured | status |
|---|---:|---|
| `KFacts` bundle on the chain's site facts | **-30 s** | the precedent you are copying |
| `Lift12Back` / `Lift12Out` kits | **4.28x** | the other working shape |
| birth-site sealing (`opaque`) | **+1.61 s** | DO NOT re-run |
| shared instantiation frames | **+17.23 s** | DO NOT re-run |
| `TwelveAgree.twelveB` as an alias | **+3.29 s** | DO NOT re-run |

`[LJ-1.47]`: **sealing buys the repeats, never the once.**

## WHAT YOU MUST NOT DO

- **Do not delete the band or any part of it.** `[LJ-1.64]` did, and I reverted it:
  `TwelveAgree` takes 24 hypotheses (`mem-out` through `exin-back`) and the band is what
  DISCHARGES them. **Nothing consumes the band only because the wiring that would consume
  it is the work that remains.** A gate that passes by deleting the discharge is C-35.
- **Do not delete content to buy the ratio**, anywhere. P-q: a deletion shrinks the
  denominator faster than the numerator and makes the ratio WORSE.
- **You may not weaken a statement, and you may not narrow a direction.** Both directions
  are needed and that is settled.
- **Do not touch anything under `src/L/Coding/`.**
- All masters carry ZERO placement of `absFo` or a placed `Δ₀`.

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

State for every negative whether its deciding claim is **MEASURED** or **INFERRED**, in
those words. **A negative that rests on an inference sets no verdict.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two ends, no
metric and no checker, so it is stated in every brief and answered in every return.

A shared bundle is MORE generic structure, stated once, and the J tower inherits it as it
inherits `KFacts`. **Say whether your bundle keeps that.** The diagnosis notes a second
payoff: the band's consumer is the pending wiring, which will instantiate all thirteen
rows, and today every instantiation restates a 10-to-17 entry telescope. **Say what the
bundle is worth at the instantiation site, or say you cannot tell.**

## ARCHIVE (DD18)

- **`_build/diag-dd24-residual.md`**, read WHOLE. It is the brief's basis; sections 1, 3a
  and 4 are the shape, the risks and the dispatch.
- **`_build/lj-1.62-report.md`** sections 2 and 3, the `KFacts` bundle you are copying and
  its profile arithmetic.
- `_build/lj-1.63-report.md` section 5, the three regressions with their numbers.
- `_build/lj-1.64-report.md` sections 2 and 3, the rejected removal and the band profile.
- `_build/lj-1.58-report.md` section 2, the `Lift12Back` kit.
- `dev/LESSONS.md` **P-o (`:2509`)**, P-t (`:2601`), P-m (`:2460`), P-n (`:2483`),
  P-q (`:2633`), D-30 (`:3255`), read WHOLE.
- `archive/rud-route/` for SHAPE only.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

**Nothing in the literature prices a spelling.** Say so in one line and spend nothing.

## SCOPE (read)

`_build/diag-dd24-residual.md` sections 1 and 4 FIRST, then `src/L/Condensation.lagda.md`
`:3090-3145` (`PropAgree`), `:3336-3418` (`AndAgree`, `OrAgree`), then the placed `KFacts`
at `:5675-5708`, then `dev/LESSONS.md:2509` for P-o.

## SCOPE (write)

`src/L/Condensation.lagda.md` and `src/ProbeLJ165*.agda`. Your report is
`_build/lj-1.65-report.md`. **No other master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and `--for probe`, and read every statement.

- **D-1.** The probe doctrine; the abort criterion is fixed above.
- **P-o.** A record field at a carrier-indexed type hangs the elaborator; use a nested Σ.
- **P-i.** The conversion-explosion playbook: select the cure by its decision tree.
- **P-h.** Module-parameterized, never function-parameterized.
- **P-k, P-l, P-m, P-n, P-q, P-t, P-u, P-v** as above, each with its action.
- **P-c, R-36, R-38.** Seal at the birth site; expose with a read lemma.
- **R-35, R-40.** State the membership SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never raised.
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-8, D-10, D-13, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`, `git reset --hard` or
  `git clean`. **The tree carries uncommitted work that is not in HEAD.**
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **The machine is quiet and both Agda slots are yours. Report the load average beside
  every absolute figure.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.65-report.md` incrementally, skeleton first.

**Lead with the verdict: GO or NO-GO, with the one family's measured before and after**,
three runs each side, one caliber, with the spread and the load. Then whether P-o fired,
and if it did, what the nested Σ measured. Then what the bundle would be worth at the
instantiation site, or that you cannot tell. **Mark every negative MEASURED or INFERRED.**
Then the DD4 answer and **the convergence answer.**
