# LJ-1.406 report: Init at the ambient least cardinal, from a truncated hypothesis

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-406/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time, no heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-406/Probe406.agda`:
`init-at-kappa`, Init at `fst (κL a oa)` from a truncated IH.

## VERDICT

**GO.** The obligation typechecks (`agents/tasks/LJ-1-406/Probe406.agda:180-190`,
exit 0, median 1.80 s) and PASSes the program's witness meter
(`scripts/pod/witness.py --code LJ-1-406`, exit 0, 1.64 s, 0 UNRESOLVED of 1).
Conjunct 4 closes from a truncated `∥ sq β ∥₁` and a truncated `κ-inj`. Nothing
in this file untruncates anything. `AmbCard` is not used.

## 1. What was built

All in `agents/tasks/LJ-1-406/Probe406.agda`, module
`LJ-1-406.Probe406 {ℓ} (lem)`:

- Sealed helpers: `isL-ord` (`:60-61`), `comp-inj` (`:64-66`),
  `inf-member` (`:69-70`).
- The ambient least cardinal, sealed at this call site: `κL`, `κoL`,
  `κ-injL`, `κ-min-atL` (`:81-95`). Section 5 states why `κ-inj` and
  `κ-min-at` are sealed with the carrier.
- `clause4-at-kappa`, the W3 probe, run first (`:103-122`). NINETEEN
  code lines. Comments and blanks excluded.
- `kappa-limit`, successor-closure of `κ` from `⟨ ω ∈ˢ fst (κL a oa) ⟩`
  (`:139-172`). The `ω ∈ κ` branch of `[LJ-1.404]`'s `kappa-is-limit⁺`
  (`agents/tasks/LJ-1-404/Probe404.agda:229-243`), restated at the sealed
  `κL`. Section 4 states why it is a restatement and not an import.
- `init-at-kappa`, the obligation (`:180-190`). ELEVEN code lines.

## 2. W3: `clause4-at-kappa`, first

**GO.** The widest unmeasured term was conjunct 4 of `Init` at
`fst (κL a oa)`, because that is the one place where a truncation, a
composition and `κ-min-at`'s comparison meet
(`src/L/Cardinal.lagda.md:140-141`). The probe is `clause4-at-kappa`
(`Probe406.agda:103-122`). Inputs: the truncated IH and the truncated
`κ-inj`. Conclusion: `Empty.⊥`. Stated and run alone, before the other
three conjuncts.

Three runs, probe interface deleted, dependencies warm, caliber
`-A64m -I0 -M8g`: 1.96 s, 1.74 s, 1.63 s. Median **1.74 s**, exit 0
every time. `runs/clause4-{1,2,3}.out`. NINETEEN code lines. The
estimate was about 30 code lines, a comparable of shape with
`[LJ-1.398]`'s `kappa-decides` (36 code lines, 1.53 s median). Measured,
conjunct 4 is smaller and in the same second.

Nothing was funded against it.

## 3. The four steps of conjunct 4

They close as the brief wrote them. No step needed the injection as data.

1. `ih β oβ β∈κ (inf-member β ω∈β)` gives `∥ sq β ∥₁`
   (`Probe406.agda:113`). The goal is `Empty.⊥`, a proposition
   (`Empty.isProp⊥`). `PT.rec` eliminates the truncation (`:113`).
2. Inside, `sq β` is `(g , g-inj)`
   (`src/L/Ordinal/SquareLaw.lagda.md:685-687`). Then `λ m → g (f m)`
   is a map `⟪ fst κ ⟫ → ⟪ β ⟫`, injective by `g-inj` then the
   injectivity of `f`. That is `⟪ fst κ ⟫ ↪ ⟪ β ⟫` as DATA, three lines
   (`:118-119`).
3. `κ-inj` is `∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁`
   (`src/L/Cardinal.lagda.md:132-133`). `PT.map` of `comp-inj` over it
   gives `∥ ⟪ fst a ⟫ ↪ ⟪ β ⟫ ∥₁` (`:121-122`). Composition is the same
   three lines `[LJ-1.390]` and `[LJ-1.398]` both wrote
   (`agents/tasks/LJ-1-398/Probe398.agda:101-103`).
4. `κ-min-atL a oa (β , isL-ord β oβ)` takes that truncation and
   returns `Empty.⊥` (`:116`, `src/L/Cardinal.lagda.md:140-141`).

The ordinal certificate of `β` is `oβ`, a hypothesis of conjunct 4, matching
`Init`'s own binder (`src/L/Ordinal/SquareLaw.lagda.md:696`). `mem-ord` is
used only in conjunct 3 (`:147`).

**The truncation is enough.** A cardinal inequality is a truncated existence
of an injection (`dev/literature/truncation-and-selection.md:75-80`). Conjunct
4 is that inequality, spelled as `Empty.⊥`. The literature's free case is the
one that fired: eliminate a truncation into a proposition. The next brief does
not need an untruncation device at this site.

## 4. The other three conjuncts of Init

`Init` has four conjuncts (`src/L/Ordinal/SquareLaw.lagda.md:692-699`).

1. `IsOrd (fst (κL a oa))` is `κoL` (`Probe406.agda:85-86`, `:187`).
2. `⟨ ω ∈ˢ fst (κL a oa) ⟩` is this brief's hypothesis (`:182`, `:188`).
   `[LJ-1.404]` refuted it as a theorem
   (`agents/tasks/LJ-1-404/lj-1.404-report.md:18-24`). It stays a hypothesis.
3. Successor-closure is `kappa-limit` (`:139-172`, placed at `:189`).
4. The no-injection clause is `clause4-at-kappa` applied to `κ-injL`
   (`:190`).

**Why conjunct 3 is a restatement and not a call.** The brief names
`[LJ-1.404]`'s `kappa-is-limit⁺`
(`agents/tasks/LJ-1-404/Probe404.agda:202`) as delivered. Two obstructions
block an import:

- `Probe404.agda:145` is a hole (`kappa-infinite = ?`). The module does not
  typecheck, so nothing in it can be imported.
- `kappa-is-limit⁺` takes `⟨ ω ∈ˢ fst a ⟩`
  (`Probe404.agda:203-204`). This brief's hypothesis is
  `⟨ ω ∈ˢ fst (κL a oa) ⟩`. The two are not the same.

The `ω ∈ κ` branch of `kappa-is-limit⁺` (`Probe404.agda:229-243`) is the
slice that matches the hypothesis. It is restated at the sealed `κL`, using
`suc∈or≡` (`src/L/Ordinal/Stages.lagda.md:137-138`), `ω-limit`
(`src/L/InjChain.lagda.md:109`), and `ShiftAbs.shift↪`
(`src/L/Absorption.lagda.md:189`). The cases `κ ∈ ω` and `κ ≡ ω` are not
needed, because this brief already has `ω ∈ κ`.

The restatement is generic in `a`. It names no site and no numeral. `Shiftω`
is the hotel shift at `ω` itself, the same delivered primitive `[LJ-1.404]`
used (`Probe404.agda:84`).

## 5. The seal

Sealed at this call site: `κL`, `κoL`, `κ-injL`, `κ-min-atL`
(`Probe406.agda:81-95`). Conjunct 4 ran once with the seal and was cheap:
median 1.74 s, exit 0, no heap event. Per the brief I stop there. I did not
spend a heap event to prove the seal was needed. Whether the transparent
`LeastCardInjL.κ` would wall at this site is unmeasured here.

What is new against `[LJ-1.398]`'s seal (`Probe398.agda:126-133`): this site
*calls* `κ-inj` and `κ-min-at`. Their types name `fst κ`. Left transparent,
those types would convert against `fst (κL a oa)` and unfold `leastOf`. The
two extra seals make the consumer types name the atom. `[LJ-1.398]`'s
`kappa-decides` compared `fst κ` against `fst a` and did not call `κ-min-at`,
so it did not need those two wrappers. A measured cure does not transfer by
analogy; the extra wrappers are this site's own seal, and they were cheap.

## 6. W2 and DD4

`init-at-kappa` is generic in `a`. It names no cardinal, no site and no
numeral. The module is generic in `ℓ`. `clause4-at-kappa`, `kappa-limit`,
`κL` and the helpers all quantify over a generic `a : S`. The mathematics
is written once at that carrier. There is no fixed form to report.

W4 does not fire: no module was retired.

## 7. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, every dependency warm, from the repository root.
The probe interface was deleted before each timed run.

- `clause4-at-kappa` alone, three consecutive runs: 1.96 s, 1.74 s, 1.63 s.
  Median **1.74 s**, exit 0 every time. `runs/clause4-{1,2,3}.out`.
- Full file, three consecutive runs: 1.80 s, 1.76 s, 1.81 s. Median
  **1.80 s**, exit 0 every time. `runs/full-{1,2,3}.out`.
- Confirm after dropping an unused `∣_∣₁` open: 1.68 s, exit 0.
  `runs/full-confirm.out`. The term did not change.
- Witness meter, the one obligation: PASS, exit 0, 1.64 s, 0 UNRESOLVED
  of 1, `probe_red=False`.
- `lint-agda.py --check` on the probe: exit 0.
- No heap event.

## 8. What GO earns

**A GO replaces a chain of three hypotheses with one delivered term.**
`[LJ-1.398]`'s positive case runs `amb-card-at-kappa`, then `kappa-is-limit`,
then `amb-init'`, then `via-col-square`
(`agents/tasks/LJ-1-398/lj-1.398-report.md:85-90`). This file reaches
`Init (fst (κL a oa))` from `κ-min-at` and a truncated IH. `AmbCard` is not
in the telescope. The next consumer is `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`), which takes this `Init` to `sq`.
That composition is not built here.

## 9. What this task does NOT settle

- It does not untruncate `κ-inj`. The injection stays truncated
  (`src/L/Cardinal.lagda.md:132-133`).
- It does not pay `band-owes-2`
  (`agents/tasks/LJ-1-398/Probe398.agda:179-184`).
- It does not prove `⟨ ω ∈ˢ fst (κL a oa) ⟩`. That remains a hypothesis,
  because `[LJ-1.404]` refuted it as a theorem.
- It does not discharge the truncated IH. Members of `κ` still owe
  `∥ sq β ∥₁`.
- It does not import `Probe404`. The hole at
  `agents/tasks/LJ-1-404/Probe404.agda:145` makes that module red. A later
  brief that wants `kappa-is-limit⁺` cannot `open` it.

## 10. What the next brief needs

The shape did not resist. Conjunct 4 is the free half it looked like. The
price is 19 code lines and 1.74 s at the W3 term, 11 more for the
obligation wrapper, and the restated `ω ∈ κ` successor-closure. The next
brief can take `init-at-kappa` as a green supplier of `Init` at the sealed
`κ`, conditional on `ω ∈ κ` and on a truncated square law at infinite
members of `κ`.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:926`,
  read: "returns only the truncation `∥ ⟪ α ⟫ ≃ ⟪ κ ⟫ ∥₁`, so the law at the".
  The archived chapter already records that a least-of search yields a
  truncation. This probe's point is the dual: a truncated `sq` is enough
  when the goal is `Empty.⊥`.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`:
  read lines 1-20, not used. This task is the injection-shape `Init` at a
  sealed `κ`, not the reified equinumerosity predicates of the retired
  rud route.
- `archive/dev/JOURNAL-archived.md:1338`, read: "the cardinal step consumes
  is delivered CONDITIONAL on one named bound, the square law (an infinite".
  `Init` is how this probe discharges that bound at the ambient least
  cardinal.
- `archive/dev/TASKS-archived.md`: read lines 1-15, not used. This task is
  `LJ-1.406` on the live route, not an `L3.32-T` dispatch.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**,". Read to resolve the injected
  archived-SquareLaw path.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Conjunct 4 is that inequality, spelled as `Empty.⊥`.
- `dev/literature/truncation-and-selection.md:83`, read: "**So a proof that
  only needs cardinal arithmetic never needs an injection as". The four
  steps never untruncate `κ-inj` or `sq β`.
- `dev/literature/devlin-II5.md`: read lines 120-131, not used. The
  construction eliminates a truncation into a proposition; it does not
  select a least witness.
- `dev/literature/digest.md`: read lines 1-40, not used. This task is the
  internalization square-law `Init` at `κ`, not the rud-route architecture.
- `dev/literature/terms-2026-08.md`: read lines 1-30, not used. No glossary
  work in this task.
