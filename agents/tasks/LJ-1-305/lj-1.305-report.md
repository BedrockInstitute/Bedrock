# LJ-1.305 report: untruncate the descent, deliver `SqShape`

tier: pi (pi-subagent-mode), model `glm-5.3`. A PROBE: nothing lands,
all work in `agents/tasks/LJ-1-305/`. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words. ASD-STE100 applies.

## 0. LEAD

**NEEDS-A-PRINCIPLE.**

The untruncated descent does not build under the current telescope. It
builds under ONE added principle, named exactly below, and that build is
green. Three results carry the verdict:

1. **Route 1 is closed, MEASURED.** `sq ω` is not an hProp. The
countermodel is `sq-not-prop` at
`agents/tasks/LJ-1-305/NotProp.agda:203-204`, green, exit 0. Section 4.
2. **Route 2 answers, MEASURED at the eliminator level.** The
truncation enters the delivered descent at ONE irreducible join: the
non-initial branch eliminates the classical existence `Wat∥` into data.
The successor join has the same shape but dissolves for free in the
restructure, and `leastOf` extracts its witness with a negational
payload. Section 3.
3. **The principle suffices, MEASURED by a green build.** With
`InjData` as a module parameter, the fully untruncated descent is green
and so is the `SqShape` statement verbatim. Without any new principle,
the descent still delivers `sq α` untruncated at every ambient-initial
α. Both live in `agents/tasks/LJ-1-305/Untruncated.agda`. Section 5.

The trophy statement need not change. D-10's question is answered: the
recorded residue is a limitation of the proof architecture, not of the
mathematics. The owner rules on the principle, not on the statement.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"` on every run, cap
never raised. The machine was NOT quiet: the 1-minute load moved between
4.46 and 8.70 across the session, with sibling tasks active. Siblings
`agents/tasks/LJ-1-306/`, `LJ-1-311/` and `LJ-1-313/` were not touched.

| run | exit | elapsed s | 1-min load |
|---|---:|---:|---:|
| control, module name error, rejected | 42 | 1 | 5.31 |
| control, own `.agdai` deleted, deps warm | **0** | **245** | 5.31→6.19 |
| NotProp, `¬` pattern parse error, rejected | 42 | 2 | 5.77 |
| NotProp, path direction errors, rejected | 42 | 2 to 3 | 5.77 |
| NotProp, with-form of the at-lemmas, wall | 251 | 246 | 5.31 |
| NotProp bisect head-131, same site, wall | 251 | 259 | 5.77 |
| NotProp bisect head-115, same site, wall | 251 | 249 | 5.77 |
| NotProp bisect head-108, meta error, rejected | 42 | 2 | 5.77 |
| NotProp, cured | **0** | **2** | 5.77 |
| Untruncated, `∈ˢ` without `⟨⟩`, rejected | 42 | 4 | 4.92 |
| Untruncated, `leastOf` with-pattern, wall | 251 | 305 | 4.92 |
| Untruncated bisect head-273, same site, wall | 251 | 315 | 4.92 |
| Untruncated bisect head-196, same site, wall | 251 | 311 | 4.49 |
| Untruncated bisect head-148, same site, wall | 251 | 312 | 4.49 |
| Untruncated, seal retry, same site, wall | 251 | 312 | 4.49→5.19 |
| Untruncated, hole and projection bisects | **0** | 3 | 4.46 |
| Untruncated, machinery head-201 green | **0** | 3 | 5.05 |
| Untruncated bisect head-282, same site in `stepI`, wall | 251 | 314 | 6.29 |
| Untruncated, projections everywhere, cured | **0** | 3 | 4.46 |
| Untruncated, subst direction, rejected | 42 | 4 | 4.46 |
| Untruncated, parse of `⟪ α ⟫↪ fst esc`, rejected | 42 | 3 to 4 | 5.07 |
| Untruncated, full file, own `.agdai` deleted | **0** | **4** | 6.29→8.70 |

**A WALL fired nine times as a heap exhaustion, MEASURED, at two sites,
and each site was cured inside the cap.** No invocation passed 30
minutes; the longest was 315 s. Section 5.4 records the cures. **MEASURED
FALSE: an invocation past 30 minutes.** The cap was never raised.

## 2. PREMISES, VERIFIED OR REFUTED

1. **"`sq-descent` is green and delivers the truncated form, at
`agents/tasks/LJ-1-301/Descent.agda:261-263`. Read the WHOLE file first
and re-run it, so your control is yours (C-44)."** **VERIFIED.** The
file was read whole. I copied it to
`agents/tasks/LJ-1-305/Control.agda` with only the module name changed,
and ran the copy. Exit 0, `--safe`, **245 s cold at load 5.31 rising to
6.19** (own `.agdii` deleted, dependencies warm). `[LJ-1.301]` reported
241.9 s at load 4.38 to 6.41. The calibers agree within 1.3 percent.
2. **"`SqShape` was FIXED today. `src/L/GCH.lagda.md:47` now reads
`(⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫`."** **VERIFIED** at
`src/L/GCH.lagda.md:46-49`, read from current source at 20:20. The
statement gates on ordinal, outside ω, and in L, and concludes the
untruncated ambient injection.
3. **"`_↪_` is a Sigma type, `src/L/Cardinal.lagda.md:47-50`. VERIFY."**
**VERIFIED.** `X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y →
x ≡ y)` at `src/L/Cardinal.lagda.md:47-48`. The first component is a
function, so funext separates witnesses. Section 4 measures the failure.
4. **"`[LJ-1.301]`'s section 4 says why it truncated. READ IT."**
**VERIFIED and CONFIRMED at the source.** Section 4
(`agents/tasks/LJ-1-301/lj-1.301-report.md:128`) names two data-consuming
branches, prices the successor one as recoverable by a union-path
decision, and records the non-initial one as the wall. My census
confirms both claims and adds one join the section does not name.

## 3. WHERE THE TRUNCATION ENTERS (route 2, the join census)

I read every elimination of a truncated fact inside `[LJ-1.301]`'s step.
Four joins, at `agents/tasks/LJ-1-301/Descent.agda`:

- **J0, the motive, `:139-140`.** `Sq∥ α` concludes `∥ sq α ∥₁`. The
well-founded recursion itself carries data: `WF.WFI.induction` accepts
any `Type`-valued motive, so J0 is FORCED by J1 and J2, not by the
recursion. MEASURED, by the green untruncated motives of section 5.
- **J1, the irreducible join, `:163-175`.** The classical decision
`lem (Wat∥ , isPropPropTrunc)` returns the positive side only truncated,
because `Wat α`'s payload is an injection, which is data. The outer
`PT.rec` at `:164-166` then eliminates `w : ∥ Wat α ∥₁` under the
propositional motive `∥ sq α ∥₁`, and the inner `PT.rec` at `:166-175`
does the same for the induction hypothesis. Under an untruncated motive
the outer elimination has NO typing: `PT.rec` demands a propositional
motive, and section 4 refutes that for `sq α`. Nothing in the telescope
extracts the payload: `lem` decides propositions and V-paths with data
on the positive side (`setIsSet`), but `Wat α` is not a proposition;
`leastOf` (`src/L/WellOrder/Base.lagda.md:158-160`) returns an INDEX
with a PROPOSITIONAL payload only; the tree's choice delivery is the
coded face, while `Wat`'s payload is an ambient injection, and the
ambient-to-code crossing is the wall `[LJ-1.300]` section 4 recorded as
INDEPENDENT.
- **J2, the successor join, `:206-214`.** The same shape over `Succ∥`.
`[LJ-1.301]` section 4 priced its removal at a union-path decision of
about ten lines. My restructure removes it with no cost at all, MEASURED
by the green build: inside the initial branch the successor case is
REFUTED, because `absorbs` contradicts ambient initiality at the
predecessor (`Untruncated.agda:178-200`), and `esc-wit`
(`Untruncated.agda:125-160`) extracts the predecessor by `leastOf` with
a NEGATIONAL payload, which loses nothing. Outside the initial branch,
successors are subsumed by the non-initial transport. `sq-succ`
(`Descent.agda:94-116`) becomes unnecessary in both descents.
- **J3, the harmless join, `:191-193`.** `noinj` consumes the induction
hypothesis under `PT.rec` into `Empty.⊥`. The output is propositional,
so this join survives every restatement. Under the untruncated motive
it disappears too: the hypothesis is consumed directly.

**Answer to route 2's question.** The truncation enters at ONE join that
cannot be re-typed, J1. A choice principle already in the module
telescope does not remove it, MEASURED by the census above: the
telescope holds `lem` only, and every in-tree extractor is
index-plus-proposition. The principle that removes J1 is `InjData`
below, and it is not in the telescope.

## 4. IS `sq α` AN hProp? (route 1, the countermodel)

**NO, MEASURED.** The countermodel is `sq-not-prop` at
`agents/tasks/LJ-1-305/NotProp.agda:203-204`:

```agda
sq-not-prop : ((g h : sq ω) → g ≡ h) → Empty.⊥
```

Green, exit 0, 2 s with dependencies warm. The construction:

1. `decV` (`NotProp.agda:49-50`) decides paths in V, because `setIsSet`
makes each path type a proposition, so `LEM (ℓ-suc ℓ)` applies. The
positive side carries the path as data.
2. `swap` (`:107-108`) transposes the two numeral points of `⟪ ω ⟫` and
fixes every other point. `swapBy` (`:99-105`) takes its two decisions
as arguments, so every clause reduces on constructors.
3. `swap-inj` (`:147-176`) proves the transposition injective by a
nine-case split on the four decisions.
4. `twisted` (`:169-170`) composes `squareω` with the transposition on
the first coordinate. It inhabits `sq ω`.
5. `twisted≢square` (`:182-183`) refutes any path `twisted ≡ squareω`:
the path applied at `(n₀ , n₀)` gives, by the injectivity of
`squareω`, the equation `n₁ ≡ n₀`, so `# 1 ≡ # 0` by `↪-inj` and
`#-inj′`, against `znots`.

So no `PT.rec` can eliminate `∥ sq α ∥₁` into `sq α`. The same
construction runs at every ordinal that holds both numerals, INFERRED:
it needs only `setIsSet`, `lem` and two numeral points. Every ordinal
the descent visits holds both numerals, because it holds ω. Route 1 is
closed at every site the descent or `SqShape` names.

**C-42 sweep.** The refuted shape is "a truncated classical existence
whose payload is data". The tree's own marker finds it at
`src/L/Cardinal.lagda.md:132` and `:256`, both already recorded as the
`κ-inj` debt. With the descent's site this makes THREE known sites, and
one ruling on `InjData` covers all three. A deeper sweep of every
`PT.rec` consumer was not run and is a separate dispatch.

## 5. THE UNTRUNCATED BUILD

### 5.1 The principle, named exactly

```agda
Wat : (α : V ℓ) → Type (ℓ-suc ℓ)
Wat α = Σ[ δ ∈ V ℓ ] (⟨ δ ∈ˢ α ⟩ × (⟪ α ⟫ ↪ ⟪ δ ⟫))

InjData : Type (ℓ-suc ℓ)
InjData = (α : V ℓ) → IsOrd α → ⟨ ω ∈ˢ α ⟩ → ∥ Wat α ∥₁ → Wat α
```

at `Untruncated.agda:107-115`. Read it as: at an infinite ordinal, a
truncated existence of an absorbing member with its injection yields
the member AND the injection as data. This is the data form of the
least-cardinal injection the tree records as truncated at
`src/L/Cardinal.lagda.md:132-133`, the second owner option of
`[LJ-1.299]` at `agents/tasks/LJ-1-299/lj-1.299-report.md:209-218`, and
the gate `[LJ-1.156]` registered at `dev/PLAN.md:1068`.

### 5.2 The terms

**Descent one, no new principle**, `Untruncated.agda:203-282`. The
motive `SqI α` pairs `(IsCardinal α → sq α)` with `∥ sq α ∥₁`:

```agda
sq-initial : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟨ isL α ⟩
           → IsCardinal α → sq α
```

at `:280-282`. At a non-initial α the untruncated component is
delivered vacuously: ambient initiality contradicts `Wat∥`. At an
initial limit α the law comes from `via-col-square`, whose output is
already untruncated, with row four from the TRUNCATED component of the
hypothesis under a propositional motive. Green, exit 0.

**Descent two, under `InjData`**, `Untruncated.agda:288-352`:

```agda
sq-descentᵘ : (α : V ℓ) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
            → ⟨ isL α ⟩ → sq α

sq-shape : (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
         → (⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫
```

at `:344-348` and `:350-352`. `sq-shape` is `SqShape`
(`src/L/GCH.lagda.md:46-49`) verbatim: the ambient injection form is
`sq` ([LJ-1.300] test 4 proved the bodies equal by `refl`). Green,
exit 0. **Sufficiency of `InjData` is MEASURED by this build.**

**Necessity is MEASURED at the eliminator level and INFERRED at the
theory level.** Measured: J1 has no typing without a payload extractor,
because `PT.rec` demands a propositional motive and section 4 refutes
the motive. Inferred: I built no model showing `lem` alone cannot prove
`InjData`, and no such claim is made.

### 5.3 What `InjData` costs the classical boundary (DD9)

DD9 keeps the tree `--safe` with LEM an explicit parameter and nothing
postulated. `InjData` as a MODULE PARAMETER keeps that discipline: the
debt stays a compile-time fact in the type, visible at every import, as
`Base.Classical`'s own doctrine demands (`src/Base/Classical.lagda.md`
`:52-57`). Three further facts:

1. `InjData` is a selection principle at the AMBIENT face, a form of
choice stronger in shape than LEM. INFERRED consistent with `lem`: no
model was built here.
2. The tree already carries the L-side selection devices: the
`orderAt` well-order family (`src/Everything.lagda.md:991`) and
internal choice `hasChoiceL` (`src/Everything.lagda.md:1000`). They do
not discharge `InjData` today, because `Wat`'s payload is an ambient
injection, and coding its graph into L is the ambient-to-code crossing
recorded as an independent wall. INFERRED: once that crossing is paid,
`InjData` becomes a lemma, and the classical literature agrees in
spirit, since Devlin's proofs pick witnesses by the `<_L`-least
(`dev/literature/devlin-II5.md:259-264`, `:128-129`).
3. One ruling covers all three known sites of the shape (section 4,
C-42).

### 5.4 The walls, and the cures (P-i)

Four repair classes, all cured inside the cap, nine exhaustions total:

1. **NotProp, the with-form of the at-lemmas.** `with decV (⟪ ω ⟫↪ m)
(# zero)` inside a goal that mentions `swap m` normalized V-paths
through the deep monic presentation. Three exhaustions at 246, 259 and
249 s. Cure, MEASURED: pass the decisions as arguments to a helper
whose statement names `swapBy`, never `swap`. Green in 2 s. This is
R-40's small-closures medicine at the decision level.
2. **Untruncated, the unsolved meta in `#-inj′`.** A left metavariable
under `#` made the unifier unfold the numeral structure without limit.
Cure, MEASURED: explicit indices `{zero} {suc zero}`. This is P-i's
repair class [F].
3. **Untruncated, the `leastOf` with-pattern.** `with leastOf ... |
(m , pm , _)` exhausted the cap six times, at 305, 315, 311, 312, 312
and 314 s, the last inside `stepI`'s successor refutation, and the
`opaque` seal of `L.Cardinal`'s medicine alone did NOT cure it,
MEASURED. Cure, MEASURED: take `fst big` and `fst (snd big)` by
projections, at both sites. Green in 3 s. The seal is kept, since it
matches the recorded medicine and costs nothing.
4. **Untruncated, `⟪ α ⟫↪ fst esc`.** Application is left-associative,
so the mixfix took `fst` as its argument. Cure: parentheses.

These are probe-local measurements. The orchestrator assigns any LESSON
ID; I propose the `leastOf` with-pattern as a candidate, since the seal
alone failing is a new fact against an existing medicine.

### 5.5 The route taken

**Route 2, in its restructured reading, plus the countermodel of route
1.** Route 1 fails by the countermodel. Route 3 does not fire: the
mathematics does not force a truncated trophy, and the owner need not
restate `SqShape`. The restructure keeps `[LJ-1.301]`'s architecture,
base, transport, initial core, and replaces only the two payload joins.

## 6. TIMING AND SIZE (DD24, DD8)

`Untruncated.agda`: 352 lines, 322 non-blank, green in **4 s cold**
(own `.agdai` deleted, dependencies warm, load 6.29 rising to 8.70).
`NotProp.agda`: 204 lines, 172 non-blank, green in 2 s warm. The
control cost 245 s for 252 non-blank, so the restructure is about 60
times cheaper than the file it untruncates, MEASURED at this probe's
loads. The successor machinery and its transports carried the cost.

**One best-effort landing price, basis: this probe.** About 300
non-blank lines land both descents, with one import widening beyond
`[LJ-1.301]`'s two: `L.WellOrder.Base` for `leastOf`. The probe's
comment mass is under a third of the file. `ledger.py` does not count
probes by construction, so these figures are mine, counted as non-blank
lines.

## 7. DD4, AND MY AXIS (C-46)

**MY AXIS IS AC-AGAINST-GCH, DD4's OWN.** The untruncated descent names
no tower and no stage presentation. It quantifies over ordinals,
members and injections. Every ingredient, `sq`, `absorbs`,
`via-col-square`, `regularityV`, `leastOf`, `esc-wit`, is tower-blind.
Under P-k it belongs to the GCH closure: `src/L/Ordinal/SquareLaw.lagda.md`
is already in it through `src/L/Cardinal.lagda.md:22`, and the build
adds no AC-side import. The two proofs share this descent wholesale: AC's
counting consumes exactly this pairing, on either side of the axis. The
SHARED row is the one to read, not a share percentage.

Genericity debts for the landing, both small: `ord-mem-emb` still
duplicates `L.BoundedSubset.Devlin55.ord-emb`
(`src/L/BoundedSubset.lagda.md:1370-1378`), and the two step bodies
`stepI` and `stepU` share a branch skeleton that a landing could factor
once, about 20 lines. I audited the instantiations, not the telescope
(C-45).

## 8. THE ABORT CRITERION, FIXED BEFORE THE RUN (D-1)

- **THE UNTRUNCATED FORM BUILDS. FIRES under `InjData`.** Section 5.2,
term, lines, seconds and route. It does not fire without the principle.
- **IT NEEDS A CHOICE PRINCIPLE NOT IN THE TELESCOPE. FIRES.** The
principle is `InjData` at `Untruncated.agda:114-115`. The boundary cost
is section 5.3.
- **`sq α` IS NOT AN hProp. FIRES, with a term.** Section 4. Route 1 is
closed. Route 2 survives in the restructured reading.
- **THE TRUNCATION IS UNREMOVABLE. DOES NOT FIRE** as a statement about
the mathematics. It is unremovable from J1 without a principle,
MEASURED at the eliminator level.
- **A WALL. FIRED four times as heap exhaustions, all cured.** No
invocation reached 30 minutes. Section 5.4.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-301/lj-1.301-report.md`, read WHOLE.** Line read
`:128`, the section 4 heading "WHY TRUNCATED, AND WHAT THE UNTRUNCATED
FORM OWES". TAKEN: the two data-consuming branches, the union-path
price, and the recorded wall my census confirms.
- **`agents/tasks/LJ-1-301/Descent.agda`, read WHOLE, first.** Line read
`:261-263`, the delivered term. TAKEN: the control, and every lemma my
build copies verbatim.
- **`agents/tasks/LJ-1-300/lj-1.300-report.md`, read for what the
parenthesis fix voided.** Line read `:10`, "CLAIM 1, the `SqShape`
mis-parse: HOLDS". TAKEN: every report before 18:00 measured a
different object, so I read current source only.
- **`agents/tasks/LJ-1-294/lj-1.294-report.md`, read for `κ-limit`.**
Line read `:12`, the `κ-limit` statement. TAKEN: row three stays off
the descent's critical path, as `[LJ-1.301]` found.
- **`archive/dev/TASKS-archived.md`, read for SHAPE and never a
claim.** Line read `:140`, the `L3.32-T105` index row with its verdict
in the row. TAKEN, SHAPE ONLY: one row per dispatch, detail in the
report.

## 10. LITERATURE USED (DD18)

- **`dev/literature/devlin-II5.md`.** Line read `:259-264`: Step G's
requirement of "a definable well-order of L_α, used to pick the
`<_L`-least", and `:128-129`: the `<_L`-least construction for
formulas. Line read `:275-284`: Step F consumes `|L_α| = |α|` for
infinite α as an input and never states a square law. TAKEN, three
points. First, the truncation question has NO counterpart in the
literature: classical existence is never truncated, and `∥_∥₁` is the
port's own device, so the question of stripping it is the port's own.
Second, the classical proof of the ordinal square law is choice-free at
initial ordinals, by the canonical max-order collapse, which is exactly
the tree's `InitialCore` `col` machinery
(`src/L/Ordinal/SquareLaw.lagda.md:703`): my finding that the initial
branch untruncates for free matches the literature. Third, at
non-initial ordinals the classical texts pick witnesses by existential
instantiation inside a proof of an existential statement, which is
precisely what the truncation models; making that pick a standing
function is `InjData`, and in L the classical device for it is the
`<_L`-least, INFERRED as the eventual in-tree discharge once the face
crossing is paid.
- **WHY NOT the rest of the digest:** sections 3, 4, 6 and 7 are the
engine list, the crossing map, the errata and the Jech cross-check;
none touches truncation, data versus proposition, or witness
selection.

## 11. WHAT I DID NOT DO

- **No master was touched.** Not `src/L/GCH.lagda.md`, not
`src/Everything.lagda.md`, not any file under `src/`. `git status`
shows my writes confined to `agents/tasks/LJ-1-305/`.
- **No sibling was touched or read**: `LJ-1-306`, and `LJ-1-311` and
`LJ-1-313`, which appeared during the session.
- **`make check` not run**, as the brief orders. Both named linters ran
on my files; section 12.
- **No `dev/` figure was edited**, not `dev/ledger.toml`, not
`dev/PLAN.md`, not `dev/LESSONS.md`. Lesson candidates are proposed in
section 5.4 for the orchestrator to number.
- **No independence model was built** for `InjData` against `lem`. The
necessity claim stops at the eliminator level, and is marked so.
- **No countermodel was built at any ordinal beyond ω.** The
generalization is INFERRED.
- **The union-path successor fix of `[LJ-1.301]` section 4 was
superseded, not built.** The restructure dissolves that branch.
- **`Control.agda` is a calibration copy**, `[LJ-1.301]`'s file with a
new module name. It is not a landing candidate.

## 12. CHECKS RUN

- `.venv/bin/python scripts/gate/lint-prose.py --check`: exit 0.
- `.venv/bin/python scripts/gate/lint-agda.py --check`: exit 0.
- **MEASURED: no em dash in any file I wrote** (grep, zero hits).
- Every agda invocation under `GHCRTS="-A64m -I0 -M8g"`, one process at
a time, cap never raised.

## 13. FOR THE ORCHESTRATOR

1. **The verdict is NEEDS-A-PRINCIPLE, with the sufficiency build
green**: `Untruncated.agda`, 322 non-blank, 4 s cold. The principle is
`InjData` at `:114-115`. The ruling is the one `[LJ-1.299]` framed and
the tree records at `src/L/Cardinal.lagda.md:132-133`: accept the
parameter now, or price the ambient-to-code crossing that would turn it
into a lemma.
2. **The unconditional fragment is delivered regardless**: `sq-initial`
at `Untruncated.agda:280-282` gives the untruncated law at every
ambient-initial ordinal with no new principle. Its face is ambient
`IsCardinal`; the trophy's use site gates on `IsCardinalL`. That face
question is the owner's cardinal-fork ruling already registered in the
newest commit, not a new fork.
3. **One heap-cure fact is new against an existing medicine**: the
`opaque` seal alone did NOT cure the `leastOf` with-pattern wall;
projections did. Propose it for a LESSON ID at your numbering.
4. **`[LJ-1.8]`'s gap is closed conditionally on ruling 1**, and
half-closed unconditionally by 2. If the owner accepts `InjData`, the
landing price is about 300 non-blank lines and one import widening.
