# LJ-1.403 report: the descent, as data, in the shape the band recursion owes

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote
only in `agents/tasks/LJ-1-403/`. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M8g"`, one process. I did not set
`GHCRTS`. No heap event.

TARGET: one term `sel-descent` in `agents/tasks/LJ-1-403/Probe403.agda`,
every field untruncated: a smaller ordinal, infinite, with an injection
into it, all as data. `isPropInjCode` and `sel-arrow` are module
hypotheses. `ne⁺` is a hypothesis.

Direction file: NONE. Work was to the brief. No conflict with a Boundary
clause.

## VERDICT

**GO on the assembly. `ne⁺` is not discharged.**

`sel-descent` typechecks, exit 0, one process, no heap event. Every field
of the conclusion is data. The two side conditions are projections of
`Good⁺`, not recoveries from `orderAt`-leastness.

The campaign item named in the brief now sits at `Ne⁺`, which is a
hypothesis about one ordinal, not a missing device.

## 1. W3: `goodplus-isProp`, first

Stated alone in `agents/tasks/LJ-1-403/Probe403.agda` under
`module GoodPlus` at `:41-55`. Run before `sel-descent` was written.

**TEN code lines** for `Good⁺` plus `goodplus-isProp` (`:45-55`, one blank
omitted). The `isProp` packing itself is three lines (`:50-52`).

The first typecheck **failed** (exit 42, real 1.58 s, no heap event) on
associativity. `A × B × C` is `A × (B × C)`. The packing
`isProp× (isProp× mem1 mem2) squash₁` proves `isProp ((A × B) × C)` and
does not match. The site-fixed order is:

    isProp× (snd (fst (up δ) ∈ fst κ))
            (isProp× (snd (ω ∈ fst (up δ)))
                     squash₁)

That is the W3 measurement: `squash₁` and `isProp×` must be right-associated
at `hProp (ℓ-suc ℓ)`. Membership is `hProp ℓ` (`snd (x ∈ y)`). The truncated
code is `Type (ℓ-suc ℓ)` (`squash₁`). The product lives at `ℓ-suc ℓ`.

Second typecheck **green**, exit 0, real 1.52 s, same caliber, cone already
warm from the failed run.

`⟨ ω ∈ fst (up δ) ⟩` enters the predicate. No universe refusal. Both extra
conjuncts are hProps and `leastOf` accepts the family.

## 2. THE OBLIGATION

`sel-descent` at `Probe403.agda:86-126`. **31 non-blank code lines**
(type plus body). Brief estimate: about 30. Not funded against the
`Good` comparable.

Type (`:86-91`):

    sel-descent :
        (κ : S) (oκ : IsOrd (fst κ))
      → (ne⁺ : Ne⁺ κ oκ)
      → Σ[ δ ∈ S ] ( ⟨ fst δ ∈ fst κ ⟩
                   × ⟨ ω ∈ fst δ ⟩
                   × (⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫) )

No `∥ ∥₁` in the conclusion. The three fields are:

- `⟨ fst δ ∈ fst κ ⟩` from `fst` of `⟨ Good⁺ δ-mem ⟩` (`:106-107`)
- `⟨ ω ∈ fst δ ⟩` from `fst (snd good)` (`:109-110`)
- `⟪ fst κ ⟫ ↪ ⟪ fst δ ⟫` from `sel-arrow` on the untruncated code (`:125-126`)

Full-file typecheck after the assembly: exit 0, real 1.72 s, cone warm,
same caliber, no heap event.

Assembly, three steps, as the brief stated:

1. `leastOf (orderAt β oβ) lem Good⁺ ne⁺` (`:97-98`). Returns `δ-mem` as
   data, with both side conditions as projections. `orderAt` is not used
   to recover membership or infinity.
2. `isPropInjCode` packages `GoodCode` (`:115-117`). A second `leastOf`
   (`:119-120`) turns `δ-inj`-shaped truncation into a code as data.
3. `sel-arrow` reads that code back (`:125-126`).

Nothing of `[LJ-1.401]` or `[LJ-1.402]` was imported. Nothing of either
probe was rebuilt. `Small` was not opened.

## 3. THE MODULE HYPOTHESES

`[LJ-1.401]` and `[LJ-1.402]` reports are not in this worktree. Types
were taken from those briefs.

`isPropInjCode` (`Probe403.agda:82`), at the type `[LJ-1.401]` names:

    (F a b : S) → isProp (InjCode F a b)

`sel-arrow` (`:83`) is **not** at the type `[LJ-1.402]` names. The 402
brief types `sel-arrow` as

    (κ : S) (oκ : IsOrd (fst κ))
  → (nonempty : InternalLeastCard.Selected's own hypothesis)
  → ⟪ fst κ ⟫ ↪ ⟪ fst (InternalLeastCard.Selected.δᴸ κ oκ nonempty) ⟫

That type names `InternalLeastCard.Selected.δᴸ` under unstrengthened
`Good` (`src/L/Cardinal.lagda.md:240`). A `Good⁺` least element is least
in a smaller family. It need not equal the `Good` least element. Feeding
a projected `ne⁺` into 402's type would return an arrow into the **wrong**
`δ`. That is the trap the brief named: `orderAt` is the code order
(`src/L/Cardinal.lagda.md:247`), and leastness under `Good` does not
carry `⟨ fst δ ∈ fst κ ⟩` or `⟨ ω ∈ fst δ ⟩`.

The type this assembly consumes is the generic readback `[LJ-1.402]`
measures (`Small` at `src/L/Coding/Injection.lagda.md:123-128`):

    (F a b : S) → InjCode F a b → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

taken as a bare hypothesis (`Probe403.agda:83`). If 402 later reports a
different type, this hypothesis is still the device 403 applies.

## 4. WHAT A CALLER MUST PROVE

`Ne⁺` at `Probe403.agda:59-61` is the hypothesis `sel-descent` takes:

    Ne⁺ : (κ : S) (oκ : IsOrd (fst κ)) → Type (ℓ-suc ℓ)
    Ne⁺ κ oκ = ∥ Σ[ δ ∈ Mem (Lset (SiteBound.β κ)) ]
                  ⟨ GoodPlus.Good⁺ κ oκ δ ⟩ ∥₁

That is the type the next brief is written from.

The negative case of the band recursion holds `IsCardinalL κ → Empty.⊥`
and `⟨ ω ∈ fst κ ⟩`. Those two together are **not** `Ne⁺`. The hoped-for
discharge is `CallerNe⁺` at `:65-69`:

    CallerNe⁺ κ oκ =
        (IsCardinalL κ → Empty.⊥)
      → ⟨ ω ∈ fst κ ⟩
      → Ne⁺ κ oκ

`CallerNe⁺` is not inhabited here. Three gaps sit between its hypotheses
and `Ne⁺`. Each is a type.

**Gap 1. Placement of `δ`.** `IsCardinalL` quantifies over `δ : S`
(`src/L/Cardinal.lagda.md:231-233`). `Good⁺` quantifies over
`Mem (Lset (SiteBound.β κ))`. A caller must supply

    place-δ :
        (κ : S) (δ : S)
      → ⟨ fst δ ∈ fst κ ⟩
      → Σ[ m ∈ Mem (Lset (SiteBound.β κ)) ]
          (SiteBound.up κ m ≡ δ)

**Gap 2. Placement of `F`.** `IsCardinalL`'s truncated code is
`∥ Σ[ F ∈ S ] InjCode F κ δ ∥₁` (`:233`). `Good⁺`'s truncated code is
`∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) κ (up δ) ∥₁`
(`Probe403.agda:49`). A caller must supply

    place-F :
        (κ : S) (F : S)
      → Σ[ m ∈ Mem (Lset (SiteBound.β κ)) ]
          (SiteBound.up κ m ≡ F)

**Gap 3. Infinity of `δ`, not of `κ`.** The caller has `⟨ ω ∈ fst κ ⟩`.
`Good⁺` asks `⟨ ω ∈ fst (up δ) ⟩` (`:48`). Membership `⟨ fst δ ∈ fst κ ⟩`
and `IsOrd (fst κ)` do not give infinity of a member. A caller must supply

    inf-δ :
        (κ : S) (oκ : IsOrd (fst κ)) (δ : S)
      → ⟨ ω ∈ fst κ ⟩
      → ⟨ fst δ ∈ fst κ ⟩
      → ⟨ ω ∈ fst δ ⟩

or refute it at the sites the recursion visits. The brief already named
this conjunct as the caller's to supply or to refute. Gap 3 is that
conjunct as a type.

D-10: I did not prove these three types true. `place-δ` and `place-F` are
the placement `SiteBound` was built for (`src/L/Cardinal.lagda.md:163-172`,
`src/L/Choice/Stage.lagda.md:366-368`). `inf-δ` can fail at a finite
member of an infinite ordinal. A next brief that inhabits `CallerNe⁺`
must treat Gap 3 as a truth question before a proof.

This task does not discharge `L.StageCardinal`'s module parameter, does
not build the recursion, and does not prove `ne⁺` at any site.

## 5. W2 (DD4)

`Good⁺` and `sel-descent` are generic in `κ`. They name no cardinal.
The only named set is `ω`, which is the infinity conjunct the brief
writes into `Good⁺`. No numeral. The two hypotheses are generic in
`F`, `a` and `b`. No fixed form was substituted for a generic one.

## 6. WHAT RESISTED, WHAT WAS WEAKENED, WHAT DID NOT CLOSE

**Resisted.** The `isProp` packing of `Good⁺` (W3). Right-association of
`isProp×` at mixed levels. One failed run, then green.

**Weakened.** `sel-arrow` was taken at the generic readback type, not at
the `Selected`-sited type the 402 brief writes. Section 3 states why the
sited type cannot be applied here. The conclusion of `sel-descent` is
not weakened: it is the type the brief named.

**Did not close.** `Ne⁺`. `CallerNe⁺` is the next obligation, with the
three gap types in section 4. `oκ` is in the telescope the brief named
and is unused in the term: `SiteBound` and `orderAt` consume `oβ`, not
`oκ`.

## 7. RUNS

All runs: one Agda process, `GHCRTS="-A64m -I0 -M8g"` as set on the pane,
cap not raised, no heap event.

| step | file | real s | exit |
|---|---|---|---|
| W3 first, `isProp×` left-associated | Probe403.agda | 1.58 | 42 |
| W3 second, `isProp×` right-associated | Probe403.agda | 1.52 | 0 |
| assembly, `sel-descent` | Probe403.agda | 1.72 | 0 |

The 1.52 s and 1.72 s figures are warm (Cardinal cone already loaded).
They are the numbers this pane measured. They are not a cold price.

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
  retired modules, not a `Good⁺` or descent construction. Quote at
  `dev/ARCHIVE.md:1`:
  `# ARCHIVE.md: the archive registry`

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. Read. Used: the
  selection device this assembly runs is a well-order plus an hProp
  guard, and a cardinal inequality in the sources is truncated.
  Quote at `dev/literature/truncation-and-selection.md:68`:
  `**The selection device is a definable well-order plus a universal guard.** The`
  This task asks for the injection as data, which that file records
  the sources do not supply. The untruncation here is `leastOf` under
  an hProp, not a classical existence.
- `dev/literature/devlin-II5.md`. Read the least-witness paragraph.
  Used as the set-theory shape of putting extra conjuncts into the
  predicate *before* selection. Quote at
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
