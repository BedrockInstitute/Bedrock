# LJ-1.411 report: a code as DATA, and no placement anywhere

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote
only in `agents/tasks/LJ-1-411/`. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M8g"`. I did not set `GHCRTS`. One
Agda process at a time. No heap event.

TARGET: one term `code-as-data` in
`agents/tasks/LJ-1-411/Probe411.agda`. The term takes no placement
hypothesis, names no `SiteBound.β`, and takes no ordinal. `isPropInjCode`
is a module hypothesis at `[LJ-1.401]`'s type
(`agents/tasks/LJ-1-401/Probe401.agda:48`). Probe401 is not imported
and is not rebuilt.

Direction file: the current direction is one SRC collection after LJ-1,
not after `[LJ-2.5]`. This task is still LJ-1 work. No conflict with a
Boundary clause.

## VERDICT

**GO.** `code-as-data` typechecks. Exit 0. One Agda process. No heap
wall. Every field of the conclusion is data. The term names no
`SiteBound.β`, no ordinal, no cardinal and no numeral.

- `code-has-stage` at `Probe411.agda:51-60` (W3, run first)
- `code-as-data` at `Probe411.agda:82-105`

The two selectors ran in series: `leastOrd (CodeAt a b)`
(`src/L/Stage.lagda.md:149`) then `leastOf (orderAt σ₀ oσ₀)`
(`src/L/WellOrder/Base.lagda.md:158` and
`src/L/Choice/Step.lagda.md:730`). The stage is selected, not supplied.

`IsLeast` is free as `snd picked` (`src/L/WellOrder/Base.lagda.md:130-131`).
It is not spent.

`isPropInjCode` stays a module hypothesis. It is not rebuilt.

## 1. W3: `code-has-stage`, first

Stated alone in `agents/tasks/LJ-1-411/Probe411.agda` at `:51-60`. Run
before `code-as-data` was written. Log: `agents/tasks/LJ-1-411/runs/w3.out`.

**GO.** Exit 0, real 1.75 s, caliber `GHCRTS="-A64m -I0 -M8g"`, one
process, no heap event. Cone warm (Cardinal already loaded). Not a cold
price.

**TEN non-blank code lines** for `code-has-stage` (`:51-60`). Plus
`CodeAt` at `:41-43`, three lines. The body is one `PT.rec` into a
truncation. `σ := stage (fst F) (snd F)`, `stage-ord` for the
certificate, `stage-mem` for the membership
(`src/L/Stage.lagda.md:180-188`). Brief estimate: about 12. These are
comparables of shape, not of size.

No universe refusal. `CodeAt` is an `Ω` because it is a truncation
(`:41-43`). It takes a bare ordinal. It does not mention `IsOrd` and it
does not use a crossing. `leastOrd`'s predicate can hold a Sigma over
the L-carrier: the Sigma sits inside the truncation, and the truncation
is the hProp.

`isPropInjCode` is not used here.

## 2. THE OBLIGATION

`code-as-data` at `Probe411.agda:82-105`. **21 non-blank code lines**
(type plus body). Helpers beside it: `upAt` (`:74-75`, two lines) and
`up-from` (`:77-80`, four lines). Whole file of new code, including
W3: 40 non-blank code lines. Brief estimate: about 45. Not funded
against that number.

Type (`:82-83`):

    code-as-data :
        (a b : S) → ∥ Σ[ F ∈ S ] InjCode F a b ∥₁ → Σ[ F ∈ S ] InjCode F a b

`S` is `L.Cardinal`'s `S` (`src/L/Cardinal.lagda.md:41`). No placement
hypothesis. No `SiteBound.β`. No ordinal in the type.

The body:

1. `leastOrd (CodeAt a b) (code-has-stage a b h)` (`:86`) returns
   `σ₀`, `IsOrd σ₀` and `⟨ CodeAt a b σ₀ ⟩` as data
   (`src/L/Stage.lagda.md:91-92` and `:149`).
2. `upAt` (`:74-75`) is `SiteBound.up` written generic in the ordinal
   (`src/L/Cardinal.lagda.md:171-172`).
3. `up-from` (`:77-80`) is `Σ≡Prop` on `isL`. Two L-elements with the
   same first projection are equal, because `isL` is an hProp
   (`src/L/Constructible.lagda.md:395-396`,
   `src/FOL/ZFStructure.lagda.md:164-166`).
4. The payload of `leastOrd` is still truncated. `PT.rec` crosses it
   into `∥ Σ[ m ∈ Mem (Lset σ₀) ] ⟨ Good m ⟩ ∥₁` (`:95-101`).
5. `leastOf (orderAt σ₀ oσ₀) lem Good` (`:103`) is
   `[LJ-1.401]`'s `sel-code` at the selected stage
   (`agents/tasks/LJ-1-401/Probe401.agda:66-71`). `Good` is `InjCode`
   of the crossed member, packed with `isPropInjCode`.

Full run: `agents/tasks/LJ-1-411/runs/full.out`. Exit 0, real 1.64 s,
same caliber, one process, no heap event. Warm. Not a cold price.

D-10: the target is true. `leastOrd` does what its type says. There is
no cardinality claim. The code exists by hypothesis. Both selections
are searches. No step failed on a level. No step failed on the two
carriers.

## 3. W2 (DD4)

`CodeAt`, `code-has-stage` and `code-as-data` are generic in `a` and
`b`. No cardinal is named. No site is named. No numeral is named. No
stage is named in any statement. The type of `code-as-data` takes no
ordinal. W2 holds. No fixed form was substituted for a generic one.

## 4. TWO CARRIERS

`L.Stage` opens `S` from `hPropStructure 𝒮ᵥ`
(`src/L/Stage.lagda.md:60`). `L.Cardinal` opens `S` from
`hPropStructure 𝒮ʟ` (`src/L/Cardinal.lagda.md:41`). A file that imports
both holds two carriers.

Renamed the V-carrier to `Sᵥ` at import (`Probe411.agda:33`). Kept the
L-carrier as `S` (`:34`). Cost: one `renaming` clause, plus `Sᵥ` in
the types of `CodeAt`, `code-has-stage`, `upAt` and `up-from`. No
adapter. No transport between the two `S` names beyond `fst` of an
L-element and `upAt`.

## 5. C-42 SWEEP

Shape: a term that places an `InjCode` witness inside
`Mem (Lset γ)` for a γ that is supplied or named, typically
`SiteBound.β`. Count first. No opinion about retirement in this
section.

**COUNT: 15 files.** 1 in `src/`, 14 in `agents/tasks/`. Those 14
files sit in 12 task directories.

src/:

| file:line | site |
|---|---|
| `src/L/Cardinal.lagda.md:240` | `InternalLeastCard.Good`: truncated `InjCode` at `SiteBound.β` |
| `src/L/Cardinal.lagda.md:257` | `δ-inj`, same construction |

That is one live master, one construction. Counted as 1 file.

Related, not in the count: `Canonical.chosen` at
`src/L/Cardinal.lagda.md:195` selects a graph at `SiteBound.β`, not
an `InjCode`. `InjL` at `src/L/GCH.lagda.md:38` and `readL` at
`src/L/CantorBernstein.lagda.md:33` quantify over `S` and name no
stage.

agents/tasks/:

| file:line | task |
|---|---|
| `agents/tasks/LJ-1-236/ProbeLJ1236A4.agda:112` | copy of `InternalLeastCard.Good` |
| `agents/tasks/LJ-1-278/BisectA34.agda:132` | same copy |
| `agents/tasks/LJ-1-278/ReRun.agda:77` | `ilcGood` at `SiteBound.β aω` |
| `agents/tasks/LJ-1-386/Probe386.agda:266` | code at `SiteBound.β a` |
| `agents/tasks/LJ-1-390/Probe390.agda:139` | code at `SiteBound.β δ` |
| `agents/tasks/LJ-1-397/Probe397.agda:112` | `CodeP` at `SiteBound.β a` |
| `agents/tasks/LJ-1-397/CodeLands.agda:48` | `code-lands` at `SiteBound.β a` |
| `agents/tasks/LJ-1-399/Probe399.agda:131` | `omega-pair-code` at `SiteBound.β (prodL ωL ωL)` |
| `agents/tasks/LJ-1-400/Probe400.agda:181` | code at `SiteBound.β (prodL κ κ)` |
| `agents/tasks/LJ-1-401/Probe401.agda:61` | `sel-code` at `SiteBound.β κ` |
| `agents/tasks/LJ-1-402/Probe402.agda:71` | readback of `sel-code` at `SiteBound.β κ` |
| `agents/tasks/LJ-1-403/Probe403.agda:49` | truncated code at `SiteBound.β` inside `Good⁺` |
| `agents/tasks/LJ-1-409/Probe409.agda:176` | `place-code` at `SiteBound.β a` |
| `agents/tasks/LJ-1-410/Probe410.agda:100` | truncated code at `SiteBound.β` inside `Good°` |

Related, not in the count: `agents/tasks/LJ-1-314/CodeUntrunc.agda:100`
selects a code at a caller-supplied `β`. That stage is a parameter, not
`SiteBound.β`.

## 6. WHAT THIS TERM PAYS, AND WHAT IT DOES NOT

The term returns some code as data. It does not return the given `F`.
It does not place that `F`, or the selected code, inside
`Lset (SiteBound.β a)`.

`[LJ-1.403]`'s gap 2 and `[LJ-1.410]`'s gap 2 ask

    place-F :
        (κ : S) (F : S)
      → Σ[ m ∈ Mem (Lset (SiteBound.β κ)) ]
          (SiteBound.up κ m ≡ F)

(`agents/tasks/LJ-1-410/lj-1.410-report.md:170-173`). That type is not
`code-as-data`. A next brief that still needs THIS `F` inside
`Lset (SiteBound.β κ)` still has a placement. A next brief that only
needs SOME code as data does not.

`[LJ-1.397]`'s `Placement` (`agents/tasks/LJ-1-397/CodeLands.agda:41`)
and `[LJ-1.409]`'s residue are the same shape: this `F` at
`SiteBound.β a`. This term does not inhabit them.

What `[LJ-1.412]` can take: a truncated `∥ Σ[ F ∈ S ] InjCode F a b ∥₁`
becomes a data `Σ[ F ∈ S ] InjCode F a b`, with `isPropInjCode` as
hypothesis, and with no ordinal in the type. If a consumer's predicate
quantifies over `S` rather than over `Mem (Lset (SiteBound.β _))`, the
placement bill of that consumer is gone.

## 7. WHAT RESISTED, WHAT WAS WEAKENED, WHAT DID NOT CLOSE

**Resisted.** The two carriers. One `renaming` clause closed it. The
crossing `upAt` plus `up-from` closed the inequality of two `isL`
proofs. No universe obstruction.

**Weakened.** Nothing of the type the brief named. `IsLeast` is not in
the conclusion. The brief does not ask for it.

**Did not close.** `isPropInjCode` remains a hypothesis. It is delivered
by `[LJ-1.401]` (`agents/tasks/LJ-1-401/Probe401.agda:48-53`). This
probe does not rebuild it.

## 8. RUNS

All runs: one Agda process, `GHCRTS="-A64m -I0 -M8g"` as set on the pane,
cap not raised, no heap event.

| step | file | real s | exit |
|---|---|---|---|
| W3 first, `code-has-stage` | Probe411.agda | 1.75 | 0 |
| assembly, `code-as-data` | Probe411.agda | 1.64 | 0 |

Both figures are warm. They are the numbers this pane measured. They
are not a cold price.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`
  Read. `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:4`
  quotes: The cardinal chapter's definitional layer fixed equinumerosity as the
  Declined: this is the retired CSB / Cantor chapter. The live `InjCode`
  and `SiteBound.up` are at `src/L/Cardinal.lagda.md:171-228`.
- `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md`
  Read. `archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:34`
  quotes: module L.CardinalPredicates {ℓ : Level} where
  Declined: this is the retired bijection-predicate chapter. It does
  not define `InjCode` and it does not run `leastOrd`.
- `archive/src/2026-08-09-rud-route/L/Choice`
  Not read. Declined: the live `orderAt` is at
  `src/L/Choice/Step.lagda.md:730`. The archived Choice tree is the
  retired route's copy.
- `archive/dev/JOURNAL-archived.md`
  Read. `archive/dev/JOURNAL-archived.md:1`
  quotes: # Archived journal: the retired route
  Declined: not used. This task is `LJ-1.411` on the live coded route.
- `archive/dev/TASKS-archived.md`
  Read. `archive/dev/TASKS-archived.md:1`
  quotes: # Archived task index: the `L3.32-T` series
  Declined: not used. This task is not an `L3.32-T` row.
- `dev/ARCHIVE.md`
  Read. `dev/ARCHIVE.md:1`
  quotes: # ARCHIVE.md: the archive registry
  Declined: not used. No module was retired. W4 does not apply.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`
  Used. `dev/literature/truncation-and-selection.md:146`
  quotes: **The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`
  and `dev/literature/truncation-and-selection.md:148`
  quotes: index is a proposition. **A data payload does not come out.**
  Both selectors on this task obey that constraint. `CodeAt` is an
  hProp, so `leastOrd` returns the ordinal as data. `InjCode` is an
  hProp by the module hypothesis, so `leastOf` returns the code as
  data. The payload of `leastOrd` is still truncated; that is why the
  two selectors run in series.
  `dev/literature/truncation-and-selection.md:68`
  quotes: **The selection device is a definable well-order plus a universal guard.** The
  `orderAt σ₀ oσ₀` is that well-order at the selected stage.
  `dev/literature/truncation-and-selection.md:140`
  quotes: (`src/L/WellOrder/Base.lagda.md:131`). **That is Devlin's `ψ` and Jech's
- `dev/literature/digest.md`
  Read. `dev/literature/digest.md:1`
  quotes: # Digest: the orthodox form of the rud route, pinned from the collected literature
  Declined: the rud-route digest. This probe does not touch rud.
- `dev/literature/terms-2026-08.md`
  Read. `dev/literature/terms-2026-08.md:1`
  quotes: # The terminology dossier: fourteen renderings for the owner's ruling
  Declined: translation terms. This task writes no glossary entry.
- `dev/literature/BIBLIOGRAPHY.md`
  Read. `dev/literature/BIBLIOGRAPHY.md:1`
  quotes: # Bibliography for the rud route
  Declined: the rud-route bibliography. This probe does not cite it.
