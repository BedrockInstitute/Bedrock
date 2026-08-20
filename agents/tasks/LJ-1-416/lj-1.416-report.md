# LJ-1.416 report: the rank of a well-order, as DATA, at a generic small carrier

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-416/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `swo-rank-mono` in
`agents/tasks/LJ-1-416/Probe416.agda`, at a generic small `A` with a
generic `SWO A`, order level `ℓ-suc ℓ`. `swo-rank` and `swo-rank-ord` are
part of the obligation.

## VERDICT

**GO.** The obligation typechecks. The witness meter PASSes.

- `swo-rank-mono` is GREEN (`Probe416.agda:111-114` at the top level,
  `Probe416.agda:80-98` at the generic carrier). Forced rechecks after
  the Acc rewrite: 1.43 s, 1.61 s, 1.52 s real
  (`runs/obligation-3.out`, `runs/obligation-4.out`,
  `runs/obligation-5.out`). Median **1.52 s**. Exit 0 every time.
  Caliber `GHCRTS="-A64m -I0 -M8g"`. One Agda process. No heap event.
- Witness: `scripts/pod/witness.py --code LJ-1-416 --brief
  agents/tasks/LJ-1-416/LJ-1.416.md`, exit 0, 0.97 s, 0 UNRESOLVED of 1
  (`runs/witness.out`).
- No `leastOf`. No `PT.rec`. No `Lset`. The family is indexed by `A`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## Levels (the table `[LJ-1.417]` and `[LJ-1.418]` are priced against)

| quantity | level | where |
|---|---|---|
| carrier `A` | `ℓ` | `Probe416.agda:38` |
| order `_<∙_` | `ℓ-suc ℓ` | `L.WellOrder.Base {ℓ-suc ℓ}`, `Probe416.agda:23` |
| `Acc _<∙_ a` | `ℓ-suc ℓ` | `Cubical.Induction.WellFounded`, `ℓ-max ℓ (ℓ-suc ℓ)` |
| `boundingOrd`'s index | `ℓ` | `src/L/Ordinal.lagda.md:154`, applied at `A` |
| `S` | `ℓ-suc ℓ` | `hPropStructure 𝒮ᵥ`, `V ℓ` |

No level was moved. D-10: the target is true at this generality. The
order stays at `ℓ-suc ℓ`. The index stays at `ℓ`.

## 1. W3: `rank-recursion-elaborates`, first

**GO.** Recursion on `wf∙` with motive `A → S` and body `∅` elaborates
at these levels. `Probe416.agda:41-43`. First run `runs/w3-1.out`,
exit 0, **1.00 s** real, same caliber, one Agda process. No
`boundingOrd` in that term.

The motive does not mention `Acc`. The accessibility witness is an
argument of `WFI.induction` and lives at `ℓ-suc ℓ`. The carrier stays
at `ℓ`. The two did meet. The level wall the brief named is not real
at this site.

ESTIMATE was about 12 code lines for the skeleton. MEASURED: 3
non-blank lines for the term (`Probe416.agda:41-43`), plus the
imports and the `Rank` telescope. Comparables of shape, not of size.

## 2. W2

The term is generic in `A` and in `w`. No `Lset`, no stage, no
cardinal, no numeral. `[LJ-1.418]` can instantiate it. W2 holds.

## 3. Literature

`dev/literature/truncation-and-selection.md` section 1 records how
the set-theory literature SELECTS a least witness under a definable
well-order. Section 2 records the type-theory untruncation of that
same selection. This term matches neither device. It selects nothing.
It computes a rank by well-founded recursion. The digest's condition
does not arise. `leastOf` is not used.

## 4. The obligation

All in `agents/tasks/LJ-1-416/Probe416.agda`, inner module
`Rank {A : Type ℓ} (w : SWO A)`, then re-exported at the top level
for the witness meter.

| piece | lines | what |
|---|---|---|
| W3 | `:41-43` | `WFI.induction wf∙`, body `∅` |
| `RankAt` | `:49-50` | `Σ[ ρ ∈ S ] IsOrd ρ` |
| `predAt` / `pred` | `:52-61` | trichotomy split; family indexed by `A` |
| `go` | `:67-72` | Acc recursion into `boundingOrd A` |
| `swo-rank` | `:74-75` | `go a (wf∙ a) .fst` |
| `swo-rank-ord` | `:77-78` | `go a (wf∙ a) .snd` |
| `swo-rank-mono` | `:80-98` | membership law of `boundingOrd` at index `a` |
| top-level names | `:102-114` | witness meter |

The family at `a` is `pred a ih : A → RankAt`. On `lt` it returns the
recursive rank. On `eq` and `gt` it returns `∅`. `boundingOrd` sees
an index of type `A : Type ℓ`. It never sees `Σ[ b ∈ A ] (b <∙ a)`.

`swo-rank-mono` is the membership law of that bound, instantiated at
the smaller index. The `lt` case of `fromTri` identifies the family
value with `swo-rank a` by `isPropAcc`. The `eq` and `gt` cases are
`irr∙` and `trans∙`. That is not one projection. The projection is
`bnd .snd .snd a` (`Probe416.agda:85`). The Acc identification is
the extra cost.

ESTIMATE for the whole obligation was about 45 code lines. MEASURED:
the inner `Rank` module is 61 lines (`:38-98`). The live code from
`RankAt` through `swo-rank-mono` is 39 non-blank non-comment lines.
Comparables of shape: `Fbnd` at `src/L/Reflect.lagda.md:447-449`.

## 5. What the shape resisted

The brief's proof plan used `WFI.induction-compute` with motive
`Σ[ ρ ∈ S ] IsOrd ρ`, so that `pack b` unfolded to the bound and
monotonicity was a projection. That check was killed before it
returned. `runs/obligation-1.out` records `killed-after`. **Not a
heap wall:** `-M8g` did not fire. The compute path is a cubical path
in `IsOrd`. The comment at `Probe416.agda:64` is the note of that
run. The log does not carry a duration.

The live term does not use `induction-compute`. It recurses on `Acc`
and spends `isPropAcc` on `Acc` only. After that rewrite the check
returned in 1.40 s (`runs/obligation-2.out`).

The STATEMENT was not weakened. The proof plan was.

## 6. What `[LJ-1.417]` and `[LJ-1.418]` need

- The level split is GO. Do not shrink the order to `ℓ`.
- Index the predecessor family by `A`, never by the predecessor
  Sigma. `boundingOrd` accepts that shape
  (`src/L/Ordinal.lagda.md:154`).
- Do not put `IsOrd` in a `WFI.induction-compute` motive. Recurse
  on `Acc`. Identify accessibility witnesses with `isPropAcc`.
- Instantiation at the tower does not need a new recursion
  principle. It needs a small `A` and an `SWO A` at order level
  `ℓ-suc ℓ`. This probe already uses that instantiation of
  `L.WellOrder.Base`.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md:1229` "no ordinal arithmetic, no order-type or rank theory"
  Used. That archived journal records the absence this task fills:
  the tree had no rank construction. The live tree still has none
  under `src/` or `archive/src/`. This probe is the first.
- `archive/dev/LJ-dispatch-index.md`: declined. It is a dispatch
  index. It does not bear on a generic rank at a small carrier.
- `dev/ARCHIVE.md:283` "A classical well-order over finite labelled trees by shortlex"
  Used. The retired `L.WellOrder.Tree` is a well-order, not a rank.
  No retired module turns a well-order into an ordinal. This task
  does not retire a module.
- `archive/dev/JOURNAL.md`: declined. Not used. The per-episode
  journal is retired. It does not bear on this rank.
- `archive/dev/DECISIONS-archived.md`: declined. Not used. The
  archived D series does not bear on this rank.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:148` "A data payload does not come out"
  Used. Section 1 records how the set-theory literature selects a
  least witness under a definable well-order. Section 2 records the
  type-theory untruncation of that same selection. This term matches
  neither device. It selects nothing. It computes a rank by
  well-founded recursion. `leastOf` is not used. The digest's
  condition does not arise.
- `dev/literature/devlin-II5.md:259` "a definable well-order of L_α, used to pick the <_L-least"
  Declined as a construction source. Devlin uses the well-order to
  SELECT a least witness. This term does not select.
- `dev/literature/digest.md:334` "the well-order as a purely algebraic"
  Used as confirmation that a well-order may be built by recursion
  with no syntax. It does not supply a rank of a generic `SWO`.
- `dev/literature/terms-2026-08.md:230` "The ordinal a well-order collapses to"
  Used. That is the sense of the object this term computes, at each
  element, as data. The glossary file is a rendering dossier. It is
  not a proof.
- `dev/literature/glossary-review-2026-08.md`: declined. Not used.
  It reviews glossary renderings. It does not bear on this rank.
