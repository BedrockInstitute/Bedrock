# LJ-1.402 report: the selected code, read back as an UNTRUNCATED ambient injection

slot: `coder`. Written early as a skeleton and filled as answers landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-402/`. Agda ran under the
caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time, no heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-402/Probe402.agda`: `sel-arrow`.
UNTRUNCATED. No `∥ ∥₁` in the conclusion.

Direction: none. Work was to the brief.

## VERDICT

**GO.** `sel-arrow` typechecks. Exit 0. The conclusion is `⟪ fst κ ⟫ ↪ ⟪ fst δᴸ ⟫`
with `_↪_` the pair of a function and its injectivity
(`src/L/Cardinal.lagda.md:47-48`). There is no `∥ ∥₁` in the conclusion.

The term is two projections. Open `Small` on the four conjuncts of the
selected `InjCode`. Then `sel-arrow κ oκ nonempty = Sm.small , Sm.small-inj`
(`Probe402.agda:81`).

`[LJ-1.401]` returned GO. `sel-code` is still a module hypothesis. This probe
does not import `Probe401` and does not rebuild the term. The hypothesis type
is the type that report gives (`Probe401.agda:57-63`, read from the
sibling worktree `LJ-1-401`; this tree does not hold that file).

This is ONE arrow, out of `κ` and into `InternalLeastCard.Selected.δᴸ`. It is
not a descent. It does not say `δᴸ` is a member of `κ`. It does not say `δᴸ`
is infinite. Both of those are `[LJ-1.403]`.

## 1. What was built

All in `agents/tasks/LJ-1-402/Probe402.agda`, module
`LJ-1-402.Probe402 {ℓ} (lem)`:

- `up-lands`, the W3 probe, first (`:42-50`). NINE code lines. Run alone
  before `sel-arrow` was written. Exit 0. 1.633 s real.
- `sel-code`, a nested-module parameter (`:66-73`). Type taken from
  `[LJ-1.401]` (`Probe401.agda:57-63`). Not imported. Not rebuilt.
- `sel-arrow` (`:76-89`). FOURTEEN code lines. Green.

The hypothesis sits after `L.Cardinal` is open, because its type names
`Selected` and `InjCode`. Unfolding those names to sit above the header
would copy `InternalLeastCard`. This probe opens that module. It does not
copy it.

## 2. W3: `up-lands`, first

GO. The brief named the lift from `Mem (Lset β)` to `S` across `Small`'s
three set arguments as the widest unmeasured term, and ordered it stated
alone and run before anything else.

`Small` wants `F D C : S` (`src/L/Coding/Injection.lagda.md:123`).

| position | what arrives | already `S`? | what `up-lands` returns |
|---|---|---|---|
| `F` | `Mem (Lset (SiteBound.β κ))` | no | `SiteBound.up κ F` |
| `D` | `κ : S` | yes | `κ` |
| `C` | `InternalLeastCard.Selected.δᴸ` | yes | `δᴸ` |

`δᴸ` is already `SiteBound.up` of the selected member
(`src/L/Cardinal.lagda.md:253-254`). The lift costs one line:
`SiteBound.up κ F` (`Probe402.agda:48`). No transport. `SiteBound.up` lands
at `S` by its own type (`src/L/Cardinal.lagda.md:171-172`).

## 3. The obligation: `sel-arrow`

GREEN at `Probe402.agda:76-89`. FOURTEEN code lines.

The three things that could have added cost, each measured:

1. **The lift.** One line, no transport. Same `SiteBound.up` as `up-lands`.
   `Small` is opened at `SiteBound.up κ (fst Fcode)`, `κ`, and `δᴸ`
   (`Probe402.agda:84-85`). Those are the three sets `up-lands` named.
2. **The destructuring.** `InjCode` is a right-associated 4-tuple
   (`src/L/Cardinal.lagda.md:223-228`). `Small` wants four arguments
   (`src/L/Coding/Injection.lagda.md:123-128`). The associativity did not
   fight. Four projections, no transport (`Probe402.agda:86-89`). Same
   shape as `L.Absorption` feeding `Small` (`src/L/Absorption.lagda.md:504`)
   and as `code-untruncates` (`agents/tasks/LJ-1-386/Probe386.agda:281-283`).
3. **The `_↪_` packing.** `small` has type `⟪ fst D ⟫ → ⟪ fst C ⟫`
   (`src/L/Coding/Injection.lagda.md:144-145`). `small-inj` is that
   function's injectivity (`:147-150`). `_↪_` is that pair
   (`src/L/Cardinal.lagda.md:47-48`). No `fst` juggling. The body is
   `Sm.small , Sm.small-inj` (`Probe402.agda:81`).

IF THE TERM IS TWO PROJECTIONS, THAT IS THE FINDING. It is. The other
thirteen lines of the definition are the type, the `where`, the
`sel-code` application, and the four-projection opening of `Small`.

The brief estimated about 8 code lines against `shiftFun` and
`shiftFun-inj` at `src/L/Absorption.lagda.md:509-530`, a comparable of
SHAPE and not of size. The measured count is 14. Nothing is funded
against the estimate.

## 4. W2 and DD4

The term is sited at `InternalLeastCard` by its type and cannot be written
generically. `Small` (`src/L/Coding/Injection.lagda.md:123-147`) is where
the generic content already lives, and this probe adds none. That is the
one delivered generic module this probe leaned on. Its one delivered
caller is `L.Absorption` at `src/L/Absorption.lagda.md:504`.

## 5. What this does not give

It gives ONE arrow, out of `κ` and into the internal least cardinal `δᴸ`
that `InternalLeastCard.Selected` picked. It does not say `δᴸ` is a member
of `κ`, and it does not say `δᴸ` is infinite. Both are `[LJ-1.403]`.
Without them this arrow is not a descent.

The ambient selection at `src/L/Cardinal.lagda.md:132-134` stays truncated.
This task does not touch it. `[LJ-1.401]` already recorded that site under
`## THE OTHER SITE`.

## 6. Runs

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, from the repository root, 2026-08-20. Exit 0
on every run. No hole. No heap event.

- `up-lands` alone, before `sel-arrow` was written: 1.633 s, exit 0.
- Full file, three consecutive runs: 1.616 s, 1.491 s, 1.482 s. Median
  1.491 s, exit 0 each time.

These runs were WARM: this worktree already held compiled interfaces for
the `L.Cardinal` cone.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Coding`: declined. The directory has
  no `Injection` master and no `Small`. The live readback is
  `src/L/Coding/Injection.lagda.md:123-147`.
- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:1`, read: "# The
  cardinal chapter's theorem side". Not used after that line. That
  archived chapter is the rud-route cardinal arithmetic, not
  `InternalLeastCard` and not `InjCode`.
- `archive/dev/JOURNAL-archived.md`: not used. It is the retired-route
  journal, and no step of this probe consults it.
- `archive/dev/TASKS-archived.md`: not used. The archived task index names
  no task this probe reads.
- `dev/ARCHIVE.md`: not used. This probe retires no module and consults no
  archived module.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:85`, read: "A formalization
  that states its conclusion with the injection as data is asking". That
  is why this task exists. The classical sources conclude a truncated
  cardinal inequality. `Small` is the cubical-side readback that turns a
  selected `InjCode` into that injection as data.
- `dev/literature/devlin-II5.md`: not used. The condensation digest bears
  on the GCH endpoint, not on the Small readback.
- `dev/literature/terms-2026-08.md`: not used. No rendering question
  arises.
- `dev/literature/digest.md`: not used. The rud-route digest is not
  consulted by this probe.

## WHAT I DID NOT DO

- I did not import `Probe401`. `sel-code` is a module hypothesis at the
  type `[LJ-1.401]` reports (`Probe401.agda:57-63`).
- I did not rebuild `sel-code`.
- I did not touch `src/`, did not commit, did not push, and set no
  `GHCRTS` of my own.
- I did not claim this arrow is a descent. It is not.
- I did not write a floor file. SCOPE names two files.
