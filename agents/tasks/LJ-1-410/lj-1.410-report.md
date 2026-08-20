# LJ-1.410 report: the descent, with the infinity conjunct OUT of the predicate

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote
only in `agents/tasks/LJ-1-410/`. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M8g"`, one process. I did not set
`GHCRTS`. No heap event.

TARGET: one term `sel-descent-nofin` in
`agents/tasks/LJ-1-410/Probe410.agda`. `Good°` carries two conjuncts.
`isPropInjCode` and `sel-arrow` are module hypotheses. Infinity of the
selected `δ` is recovered from the arrow, not asked of the caller.

Direction file: the current direction is one SRC collection after LJ-1,
not after `[LJ-2.5]`. This task is still LJ-1 work. No conflict with a
Boundary clause.

## VERDICT

**GO.** Gap 3 of `[LJ-1.403]` is retired. The infinity conjunct is not
in the predicate. The selected `δ` is not finite because it receives
an arrow out of an infinite `κ`. The conclusion is spelled as the
consumer spells it: `⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥`.

`sel-descent-nofin` typechecks, exit 0, one process, no heap event.
Every field of the conclusion is data. The membership field is a
projection of `Good°`. The no-finite field is `nofin-at-selected` on
the arrow.

`ne` is not discharged. The campaign item now sits at `Ne°`, which is
a hypothesis about one ordinal, not a missing device. Two gaps remain.
Both are placements. Neither is a truth question.

## 1. W3: `nofin-at-selected`, first

Stated alone in `agents/tasks/LJ-1-410/Probe410.agda` at `:73-85`. Run
before `Good°` and `sel-descent-nofin` were written.

**GO.** Exit 0, real 1.63 s, same caliber, no heap event. Cone warm
(InjChain already loaded). Not a cold price.

**THIRTEEN non-blank code lines** for `nofin-at-selected` (`:73-85`).
The body is the eight-line device of `no-fin-descent`
(`agents/tasks/LJ-1-398/Probe398.agda:213-220`), restated at `S` with
the consumer's `∈ˢ` spelling. Helpers rebuilt beside it, not imported:
`mem-incl` (`:50-63`), `comp-inj` (`:66-68`). The membership
`⟨ fst δ ∈ fst κ ⟩` is a hypothesis because `mem-ord` spends it for
`IsOrd (fst δ)` (`src/L/Ordinal.lagda.md:221`). `Good°` returns that
conjunct as data.

No universe refusal. `⟨ ω ∈ˢ fst κ ⟩` converts with `⟨ ω ∈ fst κ ⟩`
(`src/V/Hierarchy.lagda.md:83`, `_∈ˢ_ = _∈_`). The conclusion is
`⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥`, the consumer's spelling
(`src/L/StageCardinal.lagda.md:17`).

This term does not claim `⟨ ω ∈ fst δ ⟩`. That form can fail at a
finite member (`agents/tasks/LJ-1-403/lj-1.403-report.md:180`).
`[LJ-1.404]` refuted the same spelling at the selected cardinal
(`agents/tasks/LJ-1-404/lj-1.404-report.md:18`). C-42: that refutation
is one site. The honest spelling at this site is
`⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥`.

## 2. THE OBLIGATION

`sel-descent-nofin` at `Probe410.agda:135-175`. **31 non-blank code
lines** (type plus body). Brief estimate: about 30. Not funded against
the `[LJ-1.403]` comparable.

Type (`:135-140`):

    sel-descent-nofin :
        (κ : S) (oκ : IsOrd (fst κ)) → ⟨ ω ∈ˢ fst κ ⟩
      → (ne : Ne° κ oκ)
      → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ fst κ ⟩
                   × (⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥)
                   × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )

No `∥ ∥₁` in the conclusion. The three fields are:

- `⟨ fst δ ∈ fst κ ⟩` from `fst` of `⟨ Good° δ-mem ⟩` (`:155-156`)
- `⟨ fst δ ∈ˢ ω ⟩ → Empty.⊥` from `nofin-at-selected` on the arrow
  (`:174-175`)
- `⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫` from `sel-arrow` on the untruncated code
  (`:171-172`)

Full-file typecheck after the assembly: exit 0, real 1.81 s, cone warm,
same caliber, no heap event.

Assembly, four steps, as the brief stated:

1. `Good°` at `:97-101`. Two conjuncts. The `isProp` packing is one
   `isProp×` (`:101`): membership on the left, `squash₁` on the right.
   `[LJ-1.403]` needed two `isProp×` because it had three conjuncts.
   With one conjunct fewer there is no associativity choice. First
   packing was green.
2. `leastOf (orderAt β oβ) lem Good° ne` (`:146-147`). Returns `δ-mem`
   as data, with membership as a projection. `orderAt` is not used to
   recover membership.
3. `isPropInjCode` packages `GoodCode` (`:161-163`). A second `leastOf`
   (`:165-166`) turns the truncated code into a code as data.
   `sel-arrow` reads that code back (`:171-172`).
4. `nofin-at-selected κ oκ ω∈κ (up δ-mem) mem arrow` (`:174-175`).
   This is the W3 term. It spends `ω∈κ` and `oκ`. In `[LJ-1.403]`,
   `oκ` was unused.

Nothing of `[LJ-1.401]`, `[LJ-1.402]`, `[LJ-1.403]` or `[LJ-1.398]`
was imported. Nothing of those probes was rebuilt except the eight-line
device the brief named, plus the two helpers it spends. The selection
was rebuilt because the predicate changed.

The band membership is not in the type
(`agents/tasks/LJ-1-398/Probe398.agda:206-209`).

## 3. THE MODULE HYPOTHESES

`isPropInjCode` (`Probe410.agda:131`), at the type `[LJ-1.403]` used
(`agents/tasks/LJ-1-403/Probe403.agda:82`):

    (F a b : S) → isProp (InjCode F a b)

`sel-arrow` (`:132`), at the type `[LJ-1.403]` used (`Probe403.agda:83`):

    (F a b : S) → InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

That is the generic readback, not the `Selected`-sited type. A `Good°`
least element is least in a smaller family than `Good`
(`src/L/Cardinal.lagda.md:240`). It need not equal the `Good` least
element. The sited type cannot consume this selection. `[LJ-1.403]`
already recorded that (`agents/tasks/LJ-1-403/lj-1.403-report.md:105-112`).

## 4. WHAT A CALLER MUST PROVE

`Ne°` at `Probe410.agda:108-110` is the hypothesis
`sel-descent-nofin` takes:

    Ne° : (κ : S) (oκ : IsOrd (fst κ)) → Type (ℓ-suc ℓ)
    Ne° κ oκ = ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
                  ⟨ GoodDeg.Good° κ oκ δ ⟩ ∥₁

That is the type the next brief is written from.

The negative case of the band recursion holds `IsCardinalL κ → Empty.⊥`
and `⟨ ω ∈ˢ fst κ ⟩`. Those two together are not `Ne°`. The hoped-for
discharge is `CallerNe°` at `:115-119`:

    CallerNe° κ oκ =
        (IsCardinalL κ → Empty.⊥)
      → ⟨ ω ∈ˢ fst κ ⟩
      → Ne° κ oκ

`CallerNe°` is not inhabited here. Two gaps sit between its hypotheses
and `Ne°`. Each is a type. `[LJ-1.409]` is dispatched against these
two.

**Gap 1. Placement of `δ`.** `IsCardinalL` quantifies over `δ : S`
(`src/L/Cardinal.lagda.md:231-233`). `Good°` quantifies over
`Mem (Lset (SiteBound.β κ))`. A caller must supply

    place-δ :
        (κ : S) (δ : S)
      → ⟨ fst δ ∈ fst κ ⟩
      → Σ[ m ∈ Mem (Lset (SiteBound.β κ)) ]
          (SiteBound.up κ m ≡ δ)

**Gap 2. Placement of `F`.** `IsCardinalL`'s truncated code is
`∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁` (`src/L/Cardinal.lagda.md:233`).
`Good°`'s truncated code is
`∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁`
(`Probe410.agda:100`). A caller must supply

    place-F :
        (κ : S) (F : S)
      → Σ[ m ∈ Mem (Lset (SiteBound.β κ)) ]
          (SiteBound.up κ m ≡ F)

**Gap 3 is retired.** `[LJ-1.403]` asked

    inf-δ :
        (κ : S) (oκ : IsOrd (fst κ)) (δ : S)
      → ⟨ ω ∈ fst κ ⟩
      → ⟨ fst δ ∈ fst κ ⟩
      → ⟨ ω ∈ fst δ ⟩

That conjunct can fail at a finite member of an infinite ordinal
(`agents/tasks/LJ-1-403/lj-1.403-report.md:180-182`). It is not a
caller obligation of `CallerNe°`. The selected `δ` receives an arrow
out of `κ`, and `κ` holds `ω`, so `δ` is not a member of `ω`. That is
`nofin-at-selected`, measured in section 1.

D-10: I did not prove `place-δ` or `place-F` true. They are the
placement `SiteBound` was built for (`src/L/Cardinal.lagda.md:163-172`,
`src/L/Choice/Stage.lagda.md:366-368`). A next brief that inhabits
`CallerNe°` still treats them as placements, not as truth questions.

This task does not discharge `L.StageCardinal`'s module parameter, does
not build the recursion, and does not prove `ne` at any site.

## 5. W2 (DD4)

`Good°` and `sel-descent-nofin` are generic in `κ`. They name no
cardinal. The only named set is `ω`, which is the infinity hypothesis
the brief writes and the consumer's finite-exclusion target. No
numeral. The two hypotheses are generic in `F`, `a` and `b`. No fixed
form was substituted for a generic one.

## 6. WHAT RESISTED, WHAT WAS WEAKENED, WHAT DID NOT CLOSE

**Resisted.** Nothing of the `isProp` packing. One `isProp×` at mixed
levels (`hProp ℓ` membership against `squash₁` at `ℓ-suc ℓ`) was green
on the first assembly run.

**Weakened.** Nothing of the conclusion. `sel-arrow` is taken at the
generic readback type, as `[LJ-1.403]` took it, not at the
`Selected`-sited type. Section 3 states why the sited type cannot be
applied here.

**Did not close.** `Ne°`. `CallerNe°` is the next obligation, with the
two placement types in section 4. `oκ` is spent by step 4. The band
membership is not in this term.

## 7. RUNS

All runs: one Agda process, `GHCRTS="-A64m -I0 -M8g"` as set on the pane,
cap not raised, no heap event.

| step | file | real s | exit |
|---|---|---|---|
| W3 first, `nofin-at-selected` | Probe410.agda | 1.63 | 0 |
| assembly, `sel-descent-nofin` | Probe410.agda | 1.81 | 0 |

The 1.63 s and 1.81 s figures are warm (InjChain and Cardinal cones
already loaded). They are the numbers this pane measured. They are not
a cold price.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`. Read.
  Used as a comparable of *shape* for `isProp` packing of a truncated
  membership existential, not as a comparable of size. Quote at
  `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:331`:
  `isPropPairsClause f = isPropΠ (λ p → isPropΠ (λ _ → squash₁))`
- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`. Read the
  opening. Not used. It is the retired bijection and CSB chapter, not
  the `leastOf` selection this task assembles. Quote at
  `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:4`:
  `The cardinal chapter's definitional layer fixed equinumerosity as the`
- `archive/dev/JOURNAL-archived.md`. Not read. Declined: the live
  selection lives in `src/L/Cardinal.lagda.md` and
  `src/L/WellOrder/Base.lagda.md`.
- `archive/dev/TASKS-archived.md`. Not read. Declined: same reason.
- `dev/ARCHIVE.md`. Read the opening. Not used. It is the index of
  retired modules, not a `Good°` or descent construction. Quote at
  `dev/ARCHIVE.md:1`:
  `# ARCHIVE.md: the archive registry`

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. Read. Used: the
  selection device this assembly runs is a well-order plus an hProp
  guard. Quote at `dev/literature/truncation-and-selection.md:68`:
  `**The selection device is a definable well-order plus a universal guard.** The`
  This task asks for the injection as data, which that file records
  the sources do not supply. The untruncation here is `leastOf` under
  an hProp, not a classical existence. Infinity is recovered after
  selection, so it is not part of the guard.
- `dev/literature/devlin-II5.md`. Read the least-witness paragraph.
  Used as the set-theory shape of putting extra conjuncts into the
  predicate *before* selection, which `[LJ-1.403]` did and which this
  task undoes for the infinity conjunct. Quote at
  `dev/literature/devlin-II5.md:127`:
  `The proof verifies Tarski's criterion by a least-witness argument over the`
- `dev/literature/terms-2026-08.md`. Read the opening. Not used. It is
  a terminology dossier, not a selection or descent fact. Quote at
  `dev/literature/terms-2026-08.md:1`:
  `# The terminology dossier: fourteen renderings for the owner's ruling`
- `dev/literature/digest.md`. Read the opening. Not used. It is the
  rud-route digest, not this selection. Quote at
  `dev/literature/digest.md:1`:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`
