# LJ-1.409 report: a code that fits, by trimming it to the pairs it is about

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote only
in `agents/tasks/LJ-1-409/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time, no heap
event.

TARGET: build ONE term `place-code` in `agents/tasks/LJ-1-409/Probe409.agda`.
That term is `[LJ-1.397]`'s `code-lands` with the `Placement` hypothesis
removed. The brief pays the placement bill by replacing the given code with
one that fits, not by placing the given code.

## VERDICT

**NO-GO on `place-code`.** Stated. The obligation is a hole at
`Probe409.agda:190`. Agda reports `UnsolvedInteractionMetas` there
(`runs/place-code-hole.out`). The obstruction is written in
`review-of-place-code.md`.

**GO on the trim.** `trimmed-code` (`Probe409.agda:160-166`) is green.
Given any code `F`, the carved `F′` satisfies `InjCode F′ a c`. The four
conjuncts closed. The W3 probe closed first.

The named construction produces a code that is extensionally a subset of
`PairBound.bnd a c`. It does not produce a witness that this code is a
member of `Lset (SiteBound.β a)`. No finite successor count of that
ordinal does so at this generality. That is the number the brief asked
for: there is no such finite `n`.

## 1. W2

`place-code`, `trimmed-code`, `trim-conj4` and `Trim` are generic in `a`
and `c`. No cardinal, no ordinal and no numeral is named in any
statement. W2 holds.

## 2. W3, THE WIDEST UNMEASURED TERM

The brief named the upward transfer of the conjuncts to `F′`. The probe
is `trim-conj4`. It is GREEN at `Probe409.agda:100-105`, exit 0, 1.66 s
real, caliber `GHCRTS="-A64m -I0 -M8g"`, one Agda process
(`runs/trim-conj4.out`).

MEASURED SIZE of the W3 probe, code lines, before the other three
conjuncts:

- `inFo` (`Probe409.agda:51-52`): 2 lines
- `F′` and `F′-spec` (`:64-69`): 6 lines
- `F′-out` (`:73-81`): 9 lines
- `trim-conj4` (`:100-105`): 6 lines

Total: 23 code lines. The brief's estimate was about 60. Conjunct 4 is
DOWNWARD. Membership in `F′` gives membership in `F` by the separation
spec. The bound is not read. The estimate mixed the downward conjunct
with the upward ones.

The upward direction is `F′-in` (`:85-96`) plus `domAt`'s bwd
(`:145-149`). That is where `PairBound.below` is read
(`src/L/InjChain.lagda.md:299-300`). Those lines were written after this
measurement, as the brief ordered.

## 3. THE FOUR CONJUNCTS

`TrimCode` (`Probe409.agda:113-155`) is green (`runs/four-conjuncts.out`,
exit 0, 1.82 s).

| conjunct | direction | term | cost |
|---|---|---|---|
| 4, range | down | `trim-conj4` / `ranF′` | W3, 6 lines plus `F′-out` |
| `svAt` | down | `svF′` (`:129-131`) | `svAt-out` of `F` along `F′-out` |
| `injAt` | down | `ijF′` (`:133-135`) | `injAt-out` of `F` along `F′-out` |
| `domAt` fwd | down | `fwd` (`:140-143`) | `domAt-out` of `F` along `F′-out` |
| `domAt` bwd | up | `bwd` (`:145-149`) | `domAt-in` of `F`, range into `c`, `F′-in` |

`trimmed-code` packages this as `Σ[ G ∈ S ] InjCode G a c` from the
given code. It is the reusable half. The next brief can import it.

## 4. THE PLACEMENT RESIDUE

`place-code` (`Probe409.agda:173-194`) is `code-lands` with the given
code replaced by `trimmed-code`. The rest is the same `Σ≡Prop` transport
(`:191-194`, `agents/tasks/LJ-1-397/CodeLands.agda:59-62`). The one
unpaid step is

```agda
p : ⟨ fst G ∈ Lset (SiteBound.β a) ⟩
```

at `:189-190`.

`bound-below₂` (`src/L/Choice/Stage.lagda.md:370-373`) does not apply.
It places a member of a member of `a`. The trim is a set of pairs, not
such a member.

The carved set lands in `Lset (sucV σ)` for the reflecting stage `σ` of
`inFo F` (`src/L/Axioms/Full.lagda.md:150-151`,
`src/L/Axioms/Separation.lagda.md:293-294`,
`src/L/Axioms/Basic.lagda.md:196`). `mkBoundedTm (con F)` is the stage
of `F` (`src/L/Axioms/Separation.lagda.md:432`). `σ` is above that
stage (`src/L/ReflectFo.lagda.md:533-535`). `F` is arbitrary. No finite
`n` of successors of `SiteBound.β a` bounds `σ`.

Detail, lemmas, and the C-42 sweep: `review-of-place-code.md`.

## 5. WHAT THE NEXT BRIEF NEEDS

The trim is done. The remaining bill on the coded side is still
placement, now of a subset of `PairBound.bnd a c` whose defining formula
mentions the original `F`. Three options, not priced here:

1. Grow `SiteBound.β` past the stage of `F`. A finite increment of the
   current `β` is not enough. The increment would depend on `F`.
2. Replace the code by a construction whose formula does not mention a
   late `F` as a constant. The brief's trim is not that construction.
3. Keep `Placement` as a hypothesis, as `[LJ-1.397]` did.

I did not touch `src/`. I did not grow `SiteBound.β`.

D-10: I did not treat `place-code` as false. A different replacement
might still close the existential. I measured the named construction.

## 6. PRICE

Green trim, measured: `trimmed-code` plus `Trim` plus `TrimCode` plus
`trim-conj4`, about 90 lines of `Probe409.agda` (`:51-166`), exit 0,
under 2 s on a warm cache at the wide caliber. The brief's 60-line
estimate was for the obligation as a whole and was not a comparable of
size.

Hole: one, `Probe409.agda:190`. No heap event.

## DIRECTION

The standing direction of 2026-08-20 is a W4 pass over `src/` after the
LJ-1 campaign, not after `[LJ-2.5]`. This task is a probe under LJ-1. It
does not collect `src/`. The direction does not conflict with the brief.
The brief does not conflict with a Boundary clause.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Coding`: declined, not used. The
  live coding atoms `svAt`, `domAt`, `injAt` and `pr` are in
  `src/L/Coding/Model.lagda.md` and `src/V/Coding.lagda.md`.
- `archive/src/2026-08-09-rud-route/L/PairAtoms.lagda.md`: declined, not
  used. `archive/src/2026-08-09-rud-route/L/PairAtoms.lagda.md:4`:
  "The tower story, told inside a carrier, is one object-language sentence: some"
  The live pair is `src/V/Coding.lagda.md:175`: "pr : S → S → S".
- `archive/dev/JOURNAL-archived.md`: declined, not used.
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the retired route"
- `archive/dev/TASKS-archived.md`: declined, not used.
  `archive/dev/TASKS-archived.md:1`: "# Archived task index: the `L3.32-T` series"
- `dev/ARCHIVE.md`: declined, not used. `dev/ARCHIVE.md:1`:
  "# ARCHIVE.md: the archive registry"

## LITERATURE USED

- `dev/literature/j-hierarchy.md`: declined, not used.
  `dev/literature/j-hierarchy.md:1`:
  "# The J-hierarchy, S vs J stratification, condensation, well-order, acceptability"
- `dev/literature/digest.md`: declined, not used.
  `dev/literature/digest.md:1`:
  "# Digest: the orthodox form of the rud route, pinned from the collected literature"
- `dev/literature/rudimentary-functions.md`: declined, not used.
  `dev/literature/rudimentary-functions.md:1`:
  "# Rudimentary functions, closure, and the comprehension theorem"
- `dev/literature/terms-2026-08.md`: declined, not used.
  `dev/literature/terms-2026-08.md:1`:
  "# The terminology dossier: fourteen renderings for the owner's ruling"
