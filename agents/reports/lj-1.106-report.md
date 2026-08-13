# LJ-1.106: build Init at the Hartogs cardinal

tier: codex (default)

## STATUS

COMPLETE. Both pieces land. `Init SiteAt.κ` holds with no hypothesis
left. The probe is `src/ProbeLJ1106A.agda`, GREEN at the C-12 cap, one
process. No master was touched. No commit, no push.

## 0. THE VERDICT

**YES. `Init SiteAt.κ` holds with no hypothesis left.** The term is
`InitAtSiteFull.initκ : SQ.Init SiteAt.κ` at
`src/ProbeLJ1106A.agda:573-574`. `SQ.Init` is the master's statement at
`src/L/Ordinal/SquareLaw.lagda.md:692-698`. `SiteAt.κ` is the ambient
Hartogs cardinal (`src/ProbeLJ194A.agda:1192-1193`).

The whole probe checks GREEN, exit 0, one process at the C-12 cap:
**31.20 s cold** for the file's own content at load 3.61/4.62/4.75
(four users, machine NOT quiet), and **1.68 s warm** at load
3.59/4.50/4.70. The probe is 507 non-blank lines.

The delivered consumer closes at once. `InitAtSiteFull.sqκ : SQ.sq
SiteAt.κ` (`src/ProbeLJ1106A.agda:578-579`) applies the master's
`via-col-square` (`src/L/Ordinal/SquareLaw.lagda.md:960-961`) to
`initκ`. `sq κ` at the Hartogs cardinal is delivered.

## 1. THE PAIRING `⟪ ω ⟫ × ⟪ ω ⟫ ↪ ⟪ ω ⟫`

`NumeralPresentation.pairω` and `pairω-inj` at
`src/ProbeLJ1106A.agda:127-137`. The piece rides the ℕ pairing
(`pair`, `pair-inj`, `src/FOL/Count.lagda.md:29-30, :59-60`), the
injective numerals (`#-inj′`, `src/V/Coding.lagda.md:114-115`), and the
presentation bijection built in the same module.

The one unmeasured step, the `⟪ ω ⟫` presentation bijection, is
`NumeralPresentation.ω≃ℕ : ⟪ ω ⟫ ≃ ℕ` at `:124-125`. Its forward half
is `to : ⟪ ω ⟫ → ℕ` at `:109-110`: every presented element is a
numeral (`FiniteBase.ω-mem→numeral`,
`src/L/Ordinal/SquareLaw.lagda.md:539-542`), and the numeral fiber is a
proposition because the numerals are injective, so the truncation
eliminates without LEM. The backward half is `numeralω` at `:90-91`.
The roundtrips are at `:112-118`.

The pairing piece is **51 non-blank lines** and checks at **about 0.4 s**
above the warm import base. Prefix 1 (imports plus this module) checks
in 1.84 s at load 6.84/5.20/4.95.

## 2. THE SUCCESSOR CLOSURE `γ ∈ κ → sucV γ ∈ κ`

`SuccClosure.succκ : (γ : S) → ⟨ γ ∈ˢ Hartogs.κ ⟩ → ⟨ sucV γ ∈ˢ
Hartogs.κ ⟩` at `src/ProbeLJ1106A.agda:525-529`. For `wo` with
`ot wo = γ`, the module builds a well-order on a subset of `ω` whose
order type is `sucV γ`, then packs it as a member of `κ`.

The route has three layers.

1. `PullbackAt` (`:150-373`, 212 non-blank lines), the generic half.
   For an ordinal `α`, `IsOrd α`, and an injection `⟪ α ⟫ ↪ ⟪ ω ⟫`,
   the image of the injection is the field of a well-order whose order
   type is `α` (`ot'≡α`, `:372-373`). This is the delivered `Pullback`
   of `[LJ-1.94]` (`src/ProbeLJ194A.agda:937-1107`) with the carrier
   left generic.
2. `SucPresentation` (`:385-421`) and `SuccCount` (`:423-508`), the
   countability of a successor. The presentation of `sucV A` splits
   into the presentation of `A` plus the top (`toSplit`, `:401-405`);
   the split is a proposition because a set never equals one of its own
   members. `succ-inj : ⟪ sucV γ ⟫ ↪ ⟪ ω ⟫` at `:507-508` embeds the
   member part by the delivered countability (`Count.count`,
   `src/ProbeLJ194A.agda:546-553`) shifted past zero, and maps the top
   to the numeral zero.
3. `SuccClosure` (`:510-529`), the instantiation. `succWO` at
   `:514-522` instantiates `PullbackAt` at `δ = sucV (ot wo)`. `succκ`
   at `:525-529` lifts it through the truncation.

The successor closure's own price, **MEASURED**: the instantiation
content (`SucPresentation` plus `SuccCount` plus `SuccClosure`) is
**130 non-blank lines** and checks at **11.5 s** (prefix 3 minus prefix
2, 20.94 s minus 9.46 s, at load 6.11/5.14/4.93). The generic pullback
is **212 non-blank lines** at **7.6 s** (prefix 2 minus prefix 1, at
load 6.62/5.18/4.94). The brief's band, 60 to 150 lines, was INFERRED.
The measured instantiation content sits inside it at 130 lines.

## 3. THE ASSEMBLY

`InitBridge` (`:540-567`) restates the delivered `[LJ-1.101]` bridge
(`src/ProbeLJ1101A.agda:78-103`) and instantiates it with both
hypotheses: `NumeralPresentation.pairω`/`pairω-inj` and
`SuccClosure.succκ`. `InitAtSiteFull.initκ` at `:573-574` is the
four-component tuple at the master's `Init`. The assembly checks at
**9.2 s** (prefix 4 minus prefix 3, 30.09 s minus 20.94 s, at load
5.43/5.06/4.91). The square clause's statement carries `⟪ SiteAt.κ ⟫`
and `⟪ β ⟫`, so the assembly is the P-m instantiation class, the same
class `[LJ-1.101]` measured for the same bridge.

## 4. CHOICE

No axiom of choice is used anywhere. **MEASURED by the probe's imports
and types.** The module parameter `lem : LEM (ℓ-suc ℓ)` is the tree's
standing form, present only to instantiate `ProbeLJ194A` and
`L.Ordinal.SquareLaw`. None of the new definitions uses `lem`. The
presentation bijection eliminates the truncation because the numeral
fiber is a proposition, so the new content needs no LEM and no choice.
The chain stays choice-free.

## 5. C-39 SECTION

One route was blocked by a prohibition, and the door is reported. The
natural assembly would import `ProbeLJ1101A` and instantiate
`InitAtSite` with the two new terms. That import pulls
`L.BoundedSubset` (`src/L/BoundedSubset.lagda.md:29`), which imports
`L.Condensation`, the file the brief forbids touching because a sibling
works inside it. The sibling's file is red in the working tree
(`src/L/Condensation.lagda.md:3650`), so the import route fails today.
The door: `InitBridge` restates the same delivered bridge locally, with
both hypotheses supplied. The restatement is 25 lines of the delivered
shape, not new mathematics.

## 6. NEGATIVES AND THEIR STATUS

1. "`countAt` supplies the successor's countability": **MEASURED
   FALSE**. `countAt` (`src/ProbeLJ194A.agda:555-556`) requires
   `ot wo ≡ δ`, and `ot wo` is not `sucV (ot wo)`. The typechecker
   rejected `refl` at that type. The successor needs its own
   injection, built in section 2.
2. "The pairing is 20 to 50 lines": **MEASURED FALSE at the margin**.
   The module is 51 non-blank lines, one line over the band, because
   the presentation bijection lives inside it.
3. "The successor closure is 60 to 150 lines": **MEASURED TRUE for the
   instantiation content**. 130 non-blank lines, inside the band. The
   band was INFERRED in the brief; this dispatch is the measurement.
4. "`Init SiteAt.κ` holds with nothing assumed": **MEASURED TRUE**.
   `initκ` at `src/ProbeLJ1106A.agda:573-574`, exit 0 at the C-12 cap.
5. "The `ProbeLJ1101A` import route is open": **MEASURED FALSE today**.
   The import fails because `L.BoundedSubset` imports the sibling's red
   `L.Condensation` (`src/L/BoundedSubset.lagda.md:29`; the failure is
   in the sibling's working tree at `src/L/Condensation.lagda.md:3650`).
6. "The successor route needs choice": **MEASURED FALSE**. The
   successor injection is built from the delivered countability, the
   numerals, and the successor-presentation split. No choice axiom
   appears.

## 7. DD4

**The chain stays generic, MEASURED.** The probe's mathematics names
only the ambient universe `S`, the small presentations, injections,
`ω`, `sucV`, `WO`, `ot`, and ordinals. No tower object appears in any
type: no `Def`, no `Rud`, no `Lset`, no `Condensation`. The pullback is
written generic at `PullbackAt` and instantiated once; that is the same
content class as the `[LJ-1.94]` Pullback, one frame instead of a
pinned copy. The J half is **INFERRED** (no J tower exists in this
tree); the ambient half is **MEASURED by the probe's own types**.
Neither piece breaks the generic chain.

## 8. GATES

`src/ProbeLJ1106A.agda`: GREEN at the C-12 cap, one process at a time.
Final cold run: 31.20 s at load 3.61/4.62/4.75. Warm re-run: 1.68 s at
load 3.59/4.50/4.70. Four users, machine NOT quiet.

Prefix bisection, import cache warm, own content cold, one process
each:

| prefix | content | s | load |
|---|---:|---:|---|
| 1 | imports + pairing module | 1.84 | 6.84/5.20/4.95 |
| 2 | + generic pullback | 9.46 | 6.62/5.18/4.94 |
| 3 | + successor instantiation | 20.94 | 6.11/5.14/4.93 |
| 4 | + assembly | 30.09 | 5.43/5.06/4.91 |

`scripts/lint-prose.py --check`: exit 0 on the probe and this report.
`scripts/lint-agda.py --check`: exit 0 on the probe.
`scripts/ledger.py --brief`: standing 28,189 lines over 85 masters,
measured from HEAD.

No process was left alive; every check returned. No `make check`
(forbidden). DD23: no mathematical prose was written. `git status`: the
only tracked change is `src/L/Condensation.lagda.md`, the sibling's
in-progress file, untouched by this dispatch. HEAD moved during the
dispatch from `5cc68f7` to `a2e55ab` (the orchestrator's LJ-1.105 and
LJ-1.106 registration commit). The probe and this report are ignored.
No commit, no push.

## 9. ARCHIVE USED

- `_build/lj-1.101-report.md`, read WHOLE. TOOK the assembly shape, the
  two hypotheses, and the bridge (`src/ProbeLJ1101A.agda:78-103,
  :105-109`), restated at `src/ProbeLJ1106A.agda:540-567`.
- `src/ProbeLJ1101A.agda`, read WHOLE. TOOK `InitClauseBridge` and
  `InitAtSite` (`:78-109`).
- `_build/lj-1.94-report.md`, read WHOLE. TOOK the Hartogs chain, the
  measurement basis, and the choice reading.
- `src/ProbeLJ194A.agda`, read WHOLE. TOOK `WO` (`:184-185`), `ot`
  (`:237-238`), `Count.count` (`:546-553`), `countAt` (`:555-556`),
  `Pullback` (`:937-1107`), `OrdSWO` (`:80-140`), `OrdinalSelf`
  (`:142-366`), `Hartogs` (`:873-920`), `SiteAt` (`:1186-1233`).
- `_build/lj-1.92-report.md` and `src/ProbeLJ192A.agda`, read WHOLE.
  TOOK `OrderType` and `Unique`, used unchanged by `PullbackAt`.
- `src/L/Ordinal/SquareLaw.lagda.md`, read `:692-698` and `:938-964`.
  TOOK `Init` (`:692-698`) and `via-col-square` (`:960-961`). Also read
  `FiniteBase.ω-mem→numeral` (`:539-542`).
- `src/FOL/Count.lagda.md`, read `:20-70`. TOOK `pair`/`pair-inj`
  (`:29-30`, `:59-60`).
- `src/V/Coding.lagda.md`, read `:105-120`. TOOK `#-inj′` (`:114-115`).
- `src/V/Model.lagda.md`, read `:215-240`. TOOK `∈sucV-elim`,
  `∈sucV-inl`, `self∈sucV`.
- `dev/LESSONS.md`, read WHOLE C-38 (`:3427`), C-39 (`:3513`), C-35
  (`:3200`), C-36 (`:3284`), D-8 (`:1377`), D-30 (`:3332`), P-l
  (`:2305`), P-m (`:2460`), and the `--for build` and `--for probe`
  bundles via `scripts/rules.py`.

## 10. LITERATURE USED

Banked. Devlin assumes order types; he does not prove them in II.5
(`dev/literature/devlin-II5.md:145-166`). Spent nothing.

## 11. MASTERS

None touched. The only tracked modification in the tree is the
sibling's `src/L/Condensation.lagda.md`, which this dispatch did not
open for writing.
