# LJ-1.97: are the satisfier-in-K facts TRUE?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.97-report.md`.

## 0. THE VERDICT

**TEN of the 35 satisfier-in-K facts are REFUTED, MEASURED.** The
refutation typechecks at `src/ProbeLJ197A.agda`, exit 0, one process,
at the C-12 cap, in about 1.9 to 2.5 s total (1.45 to 1.70 s user).
Load average 3.00 to 4.05 (4 users) across the runs. Per the
pre-fixed abort criterion (D-1), STOP after step 1. The route-level
finding: the twelve-row agreement layer's frame is wrong and not
merely unwired. The refuted facts are `succK` and `keyK-un` (no
premise, unconstrained conclusion), `keyK-neg`, `succK-allin`,
`keyK-allin`, `entryK`, and the four `arSubK-*` facts. Step 2's
candidate `entryK` is among them, so its derivability question is
answered MEASURED no. Step 3 was NOT attempted, per the abort
criterion.

## 1. THE REFUTATION COUNT

Ten of the 35 family members are REFUTED. Each refutation assumes
only the fact's type at an arbitrary frame `(n, K, γ')` and derives
`Empty.⊥` from it. The type is empty at every frame. The delivered
lemmas used are `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`),
`self∈sucV` (`src/V/Model.lagda.md:236-237`), `pairing-ax`,
`pair-singleton` (`src/V/Model.lagda.md:172-173`), `pairʟ-fst`
(`src/L/Axioms/Numerals.lagda.md:127`), `prʟ-fst`
(`src/L/Coding/Model.lagda.md:329`), and `∈-induction`
(`src/V/Hierarchy.lagda.md:179-181`). The cycle lemmas
(`no-2-cycle`, `no-3-cycle`, `no-4-cycle`) are written in the probe
from `∈-induction` alone (`src/ProbeLJ197A.agda:55-89`).

Let `X = lookup (suc^6 K) γ'`, the K slot's element, and
`A = fst X`.

| fact | source line | shape | refutation term | probe line |
|---|---|---|---|---|
| `succK` | `TwelveAgree.lagda.md:205-206` | no premise; `sucV (fst ar) ∈ X` for unconstrained `ar` | 2-cycle `A ∈ sucV A ∈ A` | `ProbeLJ197A.agda:136-139` |
| `keyK-un` | `:207-208` | no premise; `pr (sucV (fst ar)) (fst a) ∈ X` | 4-cycle through `pr (sucV A) A` | `:151-155` |
| `keyK-neg` | `:201-204` | no premise; `pr (fst ar) (fst a) ∈ X` | 3-cycle `A ∈ ⁅ A ⁆s ∈ pr A A ∈ A` | `:171-174` |
| `succK-allin` | `:224-228` | no premise; `sucV (fst ar) ∈ X` | 2-cycle, same as `succK` | `:186-189` |
| `keyK-allin` | `:229-235` | no premise; `pr (sucV (fst ar)) (fst b) ∈ X` | 4-cycle, same as `keyK-un` | `:204-208` |
| `entryK` | `:118-120` | premise `pr (fst x) (fst y) ∈ fst z` satisfiable at the singleton of `pr A A` | conclusion `A ∈ A` at `x = y = X` | `:239-240` |
| `arSubK-mem` | `:121-123` | premise `x ∈ ar`; conclusion `x ∈ X` | premise at `ar = pairʟ X X`, `x = X`; conclusion `A ∈ A` | `:251-254` |
| `arSubK-neg` | `:124-126` | premise `x ∈ ar`; conclusion `x ∈ X` | same | `:264-267` |
| `arSubK-top` | `:127-129` | premise `x ∈ ar`; conclusion `x ∈ X` | same | `:277-280` |
| `arSubK-imp` | `:130-132` | premise `x ∈ ar`; conclusion `x ∈ X` | same | `:290-293` |

The two no-premise facts the brief names first, `succK` and `keyK-un`,
are the `succU` and `keyU` relations at
`src/L/Condensation.lagda.md:3635-3644`. Their bodies ignore `C`,
`T`, `B` and `N`; with the frame's lift the conclusion is a
membership in `X` for a completely unconstrained set. That is the
`tmKeyK` shape, and regularity refutes it. The three cycle lengths
come from the pair encoding: `succK` gives a direct 2-cycle,
`keyK-neg` gives a 3-cycle through the singleton `⁅ A ⁆s`, and the
two `keyK-*` forms give a 4-cycle through `⁅ sucV A ⁆s`.

## 2. THE FULL TABLE

One row per fact, read from the source at the cited lines. REFUTED
means a machine-checked `⊥` from the fact's type alone. NOT REFUTED
means no refutation term was found at the abstract frame; it is not a
measurement that the fact is true.

| fact | source | status | reason |
|---|---|---|---|
| `valK` | `:86-88` | NOT REFUTED | conclusion `yc ∈ X` is unconstrained, but the premise needs an element of the code slot, which the frame never supplies |
| `valK-un` | `:89-91` | NOT REFUTED | same |
| `envK-mem` | `:98-101` | NOT REFUTED | conclusion `E ∈ X`; `E` is pinned by the `envSetAt` satisfaction |
| `envK-neg` | `:102-105` | NOT REFUTED | same |
| `envK-top` | `:106-109` | NOT REFUTED | same |
| `envK-imp` | `:110-113` | NOT REFUTED | same |
| `envK-allin` | `:114-117` | NOT REFUTED | same |
| `entryK` | `:118-120` | REFUTED | `:239-240` |
| `arSubK-mem` | `:121-123` | REFUTED | `:251-254` |
| `arSubK-neg` | `:124-126` | REFUTED | `:264-267` |
| `arSubK-top` | `:127-129` | REFUTED | `:277-280` |
| `arSubK-imp` | `:130-132` | REFUTED | `:290-293` |
| `envInK-mem` | `:133-136` | NOT REFUTED | conclusion `z ∈ X`; `z` is the environment set the `envOverAt` satisfaction describes |
| `envInK-neg` | `:137-140` | NOT REFUTED | same |
| `envInK-top` | `:141-144` | NOT REFUTED | same |
| `envInK-imp` | `:145-148` | NOT REFUTED | same |
| `valV` | `:149-154` | NOT REFUTED | conclusion `v ∈ X`; `v` is the value the `tmValAt` satisfaction computes |
| `valW` | `:155-160` | NOT REFUTED | same |
| `wKfact` | `:161-166` | NOT REFUTED | same |
| `subK₁-and` | `:170-175` | NOT REFUTED | conclusion `y ∈ X`; the `subValAt` satisfaction mentions `γ'` slots |
| `subK₀-and` | `:176-181` | NOT REFUTED | same |
| `subK₁-imp` | `:182-187` | NOT REFUTED | same |
| `subK₀-imp` | `:188-193` | NOT REFUTED | same |
| `someEnv` | `:194` | NOT REFUTED | conditional existential; the premises are memberships in `X` with no constructible witness |
| `subK-neg` | `:195-200` | NOT REFUTED | satisfaction premise; not constructible at the abstract frame |
| `keyK-neg` | `:201-204` | REFUTED | `:171-174` |
| `succK` | `:205-206` | REFUTED | `:136-139` |
| `keyK-un` | `:207-208` | REFUTED | `:151-155` |
| `subK-un` | `:209-214` | NOT REFUTED | satisfaction premise; not constructible at the abstract frame |
| `consK-exist` | `:215-219` | NOT REFUTED | satisfaction premise; conclusion lands in the `suc^5 K` slot, a different slot |
| `consK-forall` | `:220-223` | NOT REFUTED | same |
| `succK-allin` | `:224-228` | REFUTED | `:186-189` |
| `keyK-allin` | `:229-235` | REFUTED | `:204-208` |
| `subK-allin` | `:236-241` | NOT REFUTED | satisfaction premise; not constructible at the abstract frame |
| `consK-allin` | `:242-243` | NOT REFUTED | satisfaction premise; conclusion lands in the `suc^5 K` slot |

Count: 10 REFUTED, 25 NOT REFUTED.

## 3. STEP 2: entryK

The step-2 candidate is REFUTED (section 1). `entryK`'s type is empty
at every frame, so no derivation from the machine side exists. The
answer is MEASURED no, by the refutation at
`src/ProbeLJ197A.agda:239-240`. The machine-side supply question
from `[LJ-1.96]` is therefore closed in the negative.

## 4. STEP 3: THE MEM ROW

NOT ATTEMPTED. The abort criterion stops the dispatch after step 1.
The brief allows a partial return on step 1 alone. The Mem-row
restatement would price the rewrite at an extended frame; a frame
that holds ten refuted facts cannot be restated until the facts are
repaired.

## 5. THE DD4 ANSWER

The ten refuted facts are telescope hypotheses of the shared frame.
`AbstractFrame` states them at
`src/L/Condensation/TwelveAgree.lagda.md:118-243`. `LowerAgree`
states the same types at `src/L/Condensation/LowerAgree.lagda.md:112`
and `:182` (`entryK`, `keyK-neg`); `UpperAgree` states them at
`src/L/Condensation/UpperAgree.lagda.md:102` and `:132-135`
(`entryK`, `succK`, `keyK-un`). The twelve row modules state the same
shapes at their own telescopes (`src/L/Condensation.lagda.md:2772`,
`:3490`, `:3658-3671`, `:3934-3947`, `:4165-4167`, `:4712`). The
defect is in the shared layer, and it propagates to every site at
once (D-29, `dev/LESSONS.md:3242-3284`).

The refutation itself is not shared code; it is a probe. The defective
content is the frame's telescope, which the L tower states in three
masters and the rows. A J tower that restates the same frame shape
would inherit the same empty types at every site at once. That J-side
consequence is INFERRED: no J site exists in this tree, and nothing
was machine-checked there. The L-side statements are MEASURED by
reading; the emptiness of the ten types is MEASURED at
`TwelveAgree`'s frame by the probe.

The finding matches C-38 as extended
(`dev/LESSONS.md:3427-3511`): a closure hypothesis about a bounding
set `K` must be conditional. A quantifier over arbitrary sets with no
membership premise is refuted by regularity, always. `succK`,
`keyK-un`, `keyK-neg`, `succK-allin` and `keyK-allin` are exactly
that unconditional shape, now machine-checked at their own site. The
`arSubK-*` facts are the conditional shape with the premise `x ∈ ar`
for a free `ar`, and the singleton of `A` inhabits that premise; the
conditional does not bind `ar` to `K`.

## 6. NEGATIVES AND THEIR STATUS

1. `succK` has an inhabitant: **MEASURED FALSE**. The type is empty
   at every frame (`src/ProbeLJ197A.agda:136-139`).
2. `keyK-un` has an inhabitant: **MEASURED FALSE**
   (`:151-155`).
3. `keyK-neg` has an inhabitant: **MEASURED FALSE** (`:171-174`).
4. `succK-allin` has an inhabitant: **MEASURED FALSE** (`:186-189`).
5. `keyK-allin` has an inhabitant: **MEASURED FALSE** (`:204-208`).
6. `entryK` has an inhabitant or a machine-side derivation:
   **MEASURED FALSE** (`:239-240`). This closes step 2.
7. Each of `arSubK-mem`, `arSubK-neg`, `arSubK-top`, `arSubK-imp`
   has an inhabitant: **MEASURED FALSE** (`:251-254`, `:264-267`,
   `:277-280`, `:290-293`).
8. The other 25 facts have no refutation term at the abstract frame:
   **INFERRED**. No verdict rests on any single one. A failure to
   refute is not a measurement that the fact is true.
9. The same ten types are empty at `LowerAgree`'s and `UpperAgree`'s
   frames: **INFERRED**. The types are identical modulo the
   environment name, and the probe terms transfer by alpha-renaming;
   nothing was machine-checked there.
10. The same shapes are empty at the twelve row telescopes:
    **INFERRED**. The row telescopes differ in module parameters, and
    no row-site probe was built, per the abort criterion.

## 7. ARCHIVE USED

- `_build/lj-1.96-report.md`, read WHOLE. TOOK the classification
  column, the section-1 table, and the `entryK`/`valK` no-home rows.
  This dispatch corrects that report's inference: the family's truth
  was unmeasured, and ten members are now measured false.
- `src/ProbeLJ196A.agda`, read. TOOK the probe shape and the
  `domEntryK` supply result.
- `_build/lj-1.95-report.md`, read WHOLE, and
  `src/ProbeLJ195A.agda`, read. TOOK the `tmKeyK` refutation shape
  and the same-shape scan; the scan's `valK`/`valK-un` caveat (code
  slot) is confirmed here.
- `_build/lj-1.93-report.md`, read WHOLE, and its three probes.
  TOOK the 69-fact frame table and the `entryK` no-home mismatch.
- `_build/lj-1.77-report.md`, read WHOLE. TOOK the singleton
  construction (`pairʟ X X`, `pair-singleton`, `∈∈ₛ`) that the
  `arSubK-*` and `entryK` refutations reuse.
- `_build/lj-1.71-report.md`, read WHOLE. TOOK the C-12 invocation
  line and the MEASURED/INFERRED discipline.
- `src/L/Condensation/TwelveAgree.lagda.md:45-243`, read WHOLE.
  TOOK every fact's exact type and line number quoted here.
- `src/L/Coding/Model.lagda.md`, read the environment machinery:
  `envSetAt` (`:1149-1150`), `envOverAt` (`:483-485`), `extAt`
  (`:662-668`), `subValAt` (`:817-819`), `tmValAt` (`:1701-1702`),
  `subValSuccAt` (`:1405-1407`), `consAtL` (`:1484-1485`). TOOK the
  premise shapes that block refutation of the satisfaction family.
- `src/L/Condensation.lagda.md:3635-3644`, read. TOOK `succU` and
  `keyU`: their bodies ignore `C`, `T`, `B`, `N`, which is the
  over-generalization the refutations exploit.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), each
  read WHOLE. TOOK the conditional-closure standard, the
  no-consumer-no-truth gate, and the shared-layer propagation law.
- `scripts/rules.py --for build` and `--for probe`, read all
  statements.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 8. LITERATURE USED

Banked; nothing spent.

## 9. GATES

- `src/ProbeLJ197A.agda`: GREEN, exit 0, 1.90 s total, 1.70 s user,
  first clean run; the final re-check at 2.54 s total, 1.45 s user.
  One process at the C-12 cap, load average 3.00 to 4.05 (4 users).
  The checks ran after warm dependencies; `L.Condensation` and the
  other masters were cached in `_build`.
- `scripts/lint-agda.py --check src/ProbeLJ197A.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.97-report.md`: exit 0.
- No master was touched. `src/L/Coding/`, `src/V/`,
  `src/Everything.lagda.md` are untouched. The working tree carries
  the probe and this report, both gitignored by design. The tree is
  otherwise clean at `4999160`; the orchestrator committed the
  `[LJ-1.96]` PLAN update while this dispatch ran.
- No `make check`. No commit, no push.
