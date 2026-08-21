# LJ-1.441 report: the ambient-to-coded crossing, at its one use site

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-441/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: one term `amb-to-coded-at-least` in
`agents/tasks/LJ-1-441/Probe441.agda`. The arrow is not a hypothesis. It
is `κ-injL a oa` from the four-projection seal at
`agents/tasks/LJ-1-433/Probe433.agda:79-90`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

`[LJ-1.420]` VERDICT at `agents/tasks/LJ-1-420/lj-1.420-report.md:53`:

    **GO.** `chain-upper` typechecks

`[LJ-1.414]` VERDICT at `agents/tasks/LJ-1-414/lj-1.414-report.md:51`:

    **NO-GO on `amb-to-coded`. GO on HALF B.**

`[LJ-1.414]` is a NO-GO on the name `amb-to-coded`. This file does not
write `[LJ-1.414]`'s type as an inhabited hypothesis. The type this task
does not inhabit is `agents/tasks/LJ-1-414/Probe414.agda:134-139`.

What the selection gives at `κL a oa` that a generic `d` does not:

1. `κ-min-at` at `src/L/Cardinal.lagda.md:140-141`:

       κ-min-at : (δ : S) → ⟨ fst δ ∈ˢ fst κ ⟩
                → ∥ ⟪ fst α ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥

2. `κ∈sα` at `src/L/Cardinal.lagda.md:129-130`:

       κ∈sα : ⟨ fst κ ∈ˢ sucV (fst α) ⟩
       κ∈sα = member (sucV (fst α)) γ-card

Neither puts a `Formula` anywhere. No third device in the chapter puts
one on the selected arrow. The selection predicate is `InjP'` at
`src/L/Cardinal.lagda.md:82-83`. That is `InjP (up γ)`. `InjP` at
`:66-67` is `∥ Inj γ ∥₁`. The witness is `κ-inj` at `:133-134`, still
truncated, still not a `Formula`. D-10 prices a NO-GO. The task is not
closed here. W3 runs first.

## VERDICT

**NO-GO on `amb-to-coded-at-least`. NO-GO on W3 `half-a-at-least`.**

- `half-a-at-least` is a hole at `Probe441.agda:86`. W3 ran alone, with
  the obligation omitted. Three forced rechecks, exit 42 every time,
  `UnsolvedInteractionMetas` at that one site (`runs/w3-{1,2,3}.out`).
  Median wall **1.46 s**. Median peak RSS **406372352 bytes**. The type
  of `half-a-at-least` checked. `PT.rec` on `κ-injL` checked. The hole
  is `Σ[ G ∈ S ] GraphOf a (κL a oa) f G` after the arrow opens.
- `amb-to-coded-at-least` is a hole at `Probe441.agda:107`. Full file,
  three forced rechecks, exit 42 every time, holes at `:86` and `:107`
  (`runs/full-recheck-{1,2,3}.out`). Median wall **1.45 s**. Median peak
  RSS **385433600 bytes**.
- The witness meter reports 1 UNRESOLVED of 1, `probe_red=True`, 1.66 s
  (`runs/witness-1.out`). The name is in scope. The probe is red by
  the holes.
- The obstruction is `review-of-amb-to-coded-at-least.md`. The one
  declaration that would close HALF A at this site is `selected-graph`
  there. It is `[LJ-1.414]`'s obstruction, not a new one.

A GO here would compose with `[LJ-1.420]`'s `chain-upper`
(`agents/tasks/LJ-1-420/Probe420.agda:97-99`) and put
`stage-card-upper` at every band ordinal under no hypothesis. This
return is not that GO. It does not claim a trophy.
`src/Landmarks.lagda.md` is untouched.

## 1. W2

Everything is written once at a generic carrier. The module is generic
in `ℓ`. `half-a-at-least` and `amb-to-coded-at-least` are generic in
`a`. No band, no numeral and no site is named anywhere in the file
except `ω`, which the obligation telescope names, as the brief
required. There is no fixed form to report.

W4 does not fire: no module was retired.

## 2. W3: `half-a-at-least`, first

**NO-GO.** The widest unmeasured term was HALF A at the selected arrow.
Every earlier measurement of HALF A in this tree took the arrow as a
hypothesis (`agents/tasks/LJ-1-414/Probe414.agda:65-66`). This term
takes the arrow from the seal.

`GraphOf` is copied from `Probe414.agda:56-63`, not imported
(`Probe441.agda:40-47`). The four-projection seal is copied from
`Probe433.agda:79-90` (`Probe441.agda:54-65`). The term is
`half-a-at-least` (`Probe441.agda:73-86`).

Route 1 is legal up to the graph. `PT.rec squash₁ from-down (κ-injL a oa)`
checks, because the goal is a truncation. `from-down` opens the arrow
`f`. The hole is `graph-of-f : Σ[ G ∈ S ] GraphOf a (κL a oa) f G`
(`Probe441.agda:85-86`). That is `[LJ-1.414]`'s `HalfA` at this pair.

Stated and run alone, with the obligation omitted. Probe interface
absent (Agda writes none on a hole). Dependencies warm. Caliber
`-A64m -I0 -M8g`, one Agda process:

| run | wall s | peak RSS (bytes) | log |
|---|---|---|---|
| first | 1.78 | 406355968 | `runs/w3-first.out` |
| 1 | 1.48 | 406372352 | `runs/w3-1.out` |
| 2 | 1.43 | 406372352 | `runs/w3-2.out` |
| 3 | 1.46 | 406372352 | `runs/w3-3.out` |

Median of the three forced rechecks: wall **1.46 s**. Peak RSS
**406372352 bytes**. Exit 42 every time. Each printed `Checking`. The
only error was `UnsolvedInteractionMetas` at `Probe441.agda:86`. No
heap event.

FOURTEEN non-blank code lines for `half-a-at-least` (type plus body).
EIGHT for `GraphOf`. NINE for the seal. The estimate for W3 was about
45 code lines, a comparable of SHAPE with
`agents/tasks/LJ-1-414/Probe414.agda:56-66`. Nothing is funded against
the estimate.

A failure here kills Route 1. The NO-GO is cheap and complete on that
route. The obligation was still attempted, as the brief required.

## 3. The obligation

`amb-to-coded-at-least` (`Probe441.agda:97-107`).

**Route 1, through the graph.** `PT.rec` on `κ-injL a oa` into the
truncated goal (`Probe441.agda:102-107`). That step checks. The hole
is `from-down f` (`:107`). HALF B is green at
`agents/tasks/LJ-1-414/Probe414.agda:115-128` and is not imported: it
consumes the graph the hole does not supply. W3 already measured that
missing graph at this pair.

**Route 2, through minimality.** `κ-min-at`
(`src/L/Cardinal.lagda.md:140-141`) was read as a type. It is a Pi
into `Empty.⊥`. It refutes `∥ ⟪ fst a ⟫ ↪ ⟪ fst δ ⟫ ∥₁` for every
member `δ` of `κ`. A graph `G` is an L-element whose members are
pairs. A negative statement about smaller ordinals does not name those
pairs and does not write a `Formula`. `κ∈sα`
(`src/L/Cardinal.lagda.md:129-130`) is membership of `κ` in
`sucV (fst a)`. It is not a `Formula` for the selected map. The
hypotheses `ω∈a`, `κ∈a` and `κ∉ω` in the obligation telescope were
not spent: none of them is a `Formula` either. I did not add a fifth
projection to the seal. The brief named the four-projection seal of
`[LJ-1.433]`. An unused extra projection would not close HALF A.

Nothing was weakened. No invented hypothesis. The obligation stays a
hole.

ELEVEN non-blank code lines for `amb-to-coded-at-least` (type plus
body). The estimate for the whole Agda was about 130 code lines, a
comparable of SHAPE with `agents/tasks/LJ-1-433/Probe433.agda`. The
file has 63 non-blank non-comment lines, holes included. Nothing is
funded against the estimate.

## 4. Full-file runs

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- First check after the obligation landed: 1.44 s, exit 42, peak RSS
  385417216 bytes. Printed `Checking`. Holes at `:86` and `:107`.
  `runs/full-1.out`.
- Three forced rechecks: 1.47 s, 1.44 s, 1.45 s. Peak RSS 385433600,
  385417216, 385433600 bytes. Median wall **1.45 s**. Median peak RSS
  **385433600 bytes**. Exit 42 every time. Each printed `Checking`.
  `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: 1 UNRESOLVED of 1, `probe_red=True`,
  1.66 s, witness.py exit 1. `runs/witness-1.out`.

No heap event.

## WHAT THIS DOES NOT MEASURE

A GO here would not inhabit `[LJ-1.414]`'s generic type
(`agents/tasks/LJ-1-414/Probe414.agda:134-139`). This return is a
NO-GO, and that NO-GO also does not inhabit that type. C-42 cuts both
ways: `[LJ-1.414]`'s NO-GO at generality did not measure this site,
and this NO-GO does not measure generality.

This NO-GO says nothing about the truncated route. That route's supply
is `[LJ-1.437]` (`agents/tasks/LJ-1-437/lj-1.437-report.md:17`, GO on
`sq-trunc-closed` at `Probe437.agda:345-348`) and its consumer is
`[LJ-1.434]` (`agents/tasks/LJ-1-434/lj-1.434-report.md:52`, GO on
`bounded-from-trunc`).

This measurement is ONE site: HALF A at `d := κL a oa` with the arrow
`κ-injL`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18". Declined. It is a dispatch index. This task measures one hole at a live seal.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route". Declined. The retired-route journal does not bear on HALF A at `κL`.
- `dev/ARCHIVE.md:1`, read: "# ARCHIVE.md: the archive registry". Declined. This task does not retire a module.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined. The per-episode journal is retired. The product of this task lives in this directory.
- `archive/dev/DECISIONS-archived.md:1`, read: "# Archived decisions: the D series". Declined. The live rule for this NO-GO is C-42 at `dev/LESSONS.md:3752`, not an archived D-series row.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:75`, read: "13.20 (`dev/literature/devlin-II5.md:145-166`). **A cardinal inequality is a". Used: the selected witness is truncated existence of an injection, and that is not a graph as data.
- `dev/literature/truncation-and-selection.md:148`, read: "index is a proposition. **A data payload does not come out.**" Used: `leastOf` delivers the least index and a propositional payload. It does not deliver a `Formula` or a graph.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the rud route, pinned from the collected literature". Declined. This task re-measures HALF A at one pair. It does not consult the orthodox digest.
- `dev/literature/devlin-II5.md:1`, read: "# Devlin II.5: the Condensation Lemma and the GCH in L". Declined as a source for a producer. The condensation map is a collapse of a hull, not a coding of `κ-injL`. `[LJ-1.414]` already spent `:72` on that point (`agents/tasks/LJ-1-414/lj-1.414-report.md:233-235`).
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier: fourteen renderings for the owner's ruling". Declined. No glossary work.
- `dev/literature/rudimentary-functions.md:1`, read: "# Rudimentary functions, closure, and the comprehension theorem". Declined. HALF A at this site is not a rudimentary-function identity.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not inhabit `[LJ-1.414]`'s `amb-to-coded`.
- I did not add a module hypothesis whose type is the statement under
  proof, or whose type a predecessor named FALSE.
- I did not import `Probe414`. HALF B stays at its delivered site.
- I did not copy `code-from-graph`. The graph it consumes is the hole.
- I did not unfold `LeastCardInjL.κ`. The seal is the four projections
  `[LJ-1.433]` delivered.

## WHAT THE NEXT BRIEF NEEDS

The ambient route is dead at the pair the chain spends, and the
obstruction is the same one `[LJ-1.414]` met. `[LJ-2.5]` therefore has
that crossing closed as NO-GO at its own site, not only at generality.

The remaining type is `selected-graph` in
`agents/tasks/LJ-1-441/review-of-amb-to-coded-at-least.md`:

    selected-graph :
        (a : S) (oa : IsOrd (fst a))
      → (f : ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫)
      → Σ[ G ∈ S ] GraphOf a (κL a oa) f G

A next brief that wants this hole filled must supply a `Formula` for
that opened `f`, or a producer of `selected-graph`. Minimality does
not supply either. The truncated route (`[LJ-1.437]` into
`[LJ-1.434]`) is a different measurement and this NO-GO does not
price it.
