# LJ-1.426 report: can the tree code the ambient least-cardinal arrow, at one named ordinal

slot: `coder`. Written early as a skeleton and filled as answers landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-426/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`. I did
not set `GHCRTS`. One Agda process at a time. No heap event.

TARGET: build ONE term `kappa-coded` in
`agents/tasks/LJ-1-426/Probe426.agda`, at a generic L-element `a : S` with
its ordinal certificate `oa` as module parameters, with `SiteBound a` and
`LeastCardInjL a oa` in scope:

    kappa-coded : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a κ ∥₁

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work. It
does not start that collection. It does not start phase 3. No Boundary
clause is in conflict. Nothing was written into `src/`.

## D-10, BEFORE ANY AGDA

The ambient arrow at the least cardinal exists as a truncated injection
(`src/L/Cardinal.lagda.md:133`, `κ-inj : ∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁`).
That is the HoTT Book's own reading of a cardinal inequality: mere
existence of an injection
(`dev/literature/truncation-and-selection.md:75-76`). **The truth of the
injection is not in doubt from the ambient side.**

What is in doubt is whether the tree can produce a CONSTRUCTIBLE set that
CODES one. `InjCode` is four satisfaction facts about a SET
(`src/L/Cardinal.lagda.md:223-228`). It names no ambient function. The
conclusion of this task is truncated existence of such a set, so nothing
here untruncates anything.

The literature never codes an arbitrary ambient function. Devlin II.5.2
produces a collapse of a Σ₁ hull (`dev/literature/devlin-II5.md:72-77`).
That map is definable. `leastOf` delivers the least INDEX untruncated; a
data payload does not come out
(`dev/literature/truncation-and-selection.md:146-148`). So the recorded
residue "the ambient arrow at κ, as a code" is not the same statement as
"an injection a → κ exists". The corrected target is HALF A at this one
pair `(a, κ)`: a graph G of that arrow, as an L-element. HALF B is
already paid (`agents/tasks/LJ-1-414/Probe414.agda:115-128`).

W8 does not abort HALF B. It stops the unconditional obligation. A
literature NO-GO on `kappa-coded` built from live chapters is this return,
and it is not a failure of the probe.

## VERDICT

**NO-GO on `kappa-coded`. GO on HALF B at this pair, with the four
readings as module hypotheses.**

- `from-graph` is GREEN (`Probe426.agda:129-130`, `runs/w3-1.out`,
  `runs/w3-2.out`, `runs/w3-3.out`, exit 0 on each of three forced
  rechecks). Median 1.71 s real. Peak RSS 396509184 bytes
  (`runs/w3-1.time:2`). Caliber `GHCRTS="-A64m -I0 -M8g"`, one Agda
  process. No heap event.
- `kappa-coded` is a hole at `Probe426.agda:136`. Agda reports
  `UnsolvedInteractionMetas` (`runs/kappa-coded-hole-1.out:2-4`, exit
  42, median 1.68 s real over three forced rechecks). The obstruction
  is `review-of-kappa-coded.md`.
- HALF A at this pair has no producer in the live chapters. No axiom,
  no postulate, no module parameter that asserts it. HALF A itself was
  not attempted.

This is not a refutation of the type. The `[LJ-1.414]` report returned
NO-GO on the general implication and did not refute it
(`agents/tasks/LJ-1-414/lj-1.414-report.md:39`). Audit finding F6
downgrades the words of grade "cannot" in that report
(`dev/pod/audit-2026-08-20.md:83-91`). This return names HALF A at one
named ordinal as the campaign's remaining link. It does not say the
link is impossible.

## 1. W2

Generic in `a`. The ordinal certificate `oa` is a module parameter
(`Probe426.agda:110`). No band and no numeral is named in any statement
I wrote. `ω` does not appear. W2 holds.

`code-from-graph` is written once at a generic carrier `x d G`
(`Probe426.agda:90-104`) and instantiated at `a` and `κ`
(`Probe426.agda:130`). The copy is from
`agents/tasks/LJ-1-414/Probe414.agda:115-128`. Importing that module
also checks `amb-to-coded = {!!}` (`Probe414.agda:139`), so the
function was copied, not imported.

## 2. FOUR CANDIDATE SUPPLIERS

Each answered. None skipped.

### 2.1 `OrdIncl` (`src/L/InjChain.lagda.md:604-608`)

`OrdIncl C oC D D∈C` opens `InclGraph D C` with the subset witness from
ordinal transitivity (`src/L/InjChain.lagda.md:608`). The inclusion it
carves is the identity on `D` into `C`: domain `D`, codomain `C`
(`src/L/InjChain.lagda.md:575-576`).

The needed arrow is `⟪ fst a ⟫ ↪ ⟪ fst κ ⟫`
(`src/L/Cardinal.lagda.md:63-64`, `:133`): from `a` into `κ`.

The membership the chapter delivers is `κ∈sα : ⟨ fst κ ∈ˢ sucV (fst α) ⟩`
(`src/L/Cardinal.lagda.md:129-130`). Instantiating `OrdIncl` at that
membership gives the inclusion of `κ` into `sucV (fst a)`, which is the
wrong direction.

The direction that would match is `OrdIncl` at `D = a`, `C = κ`, which
needs `⟨ fst a ∈ fst κ ⟩`. That hypothesis is false at this pair:
`idInj` (`src/L/Cardinal.lagda.md:109-110`) is an injection `a ↪ a`,
and `κ-min-at` (`src/L/Cardinal.lagda.md:140-141`) says no `δ ∈ κ`
receives an injection from `a`. Taking `δ = a` would contradict. So
`OrdIncl` does not even instantiate at `(a, κ)` in the needed
direction. This is a measurement of this supplier at this pair. It is
not a refutation of `kappa-coded`.

### 2.2 `Comp` (`src/L/InjChain.lagda.md:314-324`)

`Comp` takes two graphs `F` and `H` that already carry the four
conjuncts each (`svF`, `dmF`, `ijF`, `ranF` and the same four for `H`,
`src/L/InjChain.lagda.md:315-324`). It carves the composite by
separation on `compFo F H` (`src/L/InjChain.lagda.md:336-339`). It
chains coded graphs it is given. It does not manufacture a first
factor. At this pair there is no coded factor to give it.

### 2.3 Separation (`src/L/Absorption.lagda.md:400-401`)

The suspected blocker, written down as a measurement.

`sep` has type

    (b : S) (φ : Formula S 1)
  → isContr (SetOf (λ w → (w ∈ˢ b) ⊓ ((w ∷ []) ⊨ φ)))

Cite: `src/L/Absorption.lagda.md:400-401`. The live field
`hasSeparationL` is the same type (`src/L/Axioms/Full.lagda.md:144-145`).

`Formula` is an inductive datatype of object-language syntax
(`src/FOL/Syntax.lagda.md:94-100`). Its constructors are the atoms
`_∈̇_`, `_≐_`, the connectives, the quantifiers, and the bounded
quantifiers. A term is `con : K → Term K n` or `var : Fin n → Term K n`
(`src/FOL/Syntax.lagda.md:42-44`). The constant of a `Formula S 1` is an
element of `S`, a SET.

`κ-inj` (`src/L/Cardinal.lagda.md:133`) is a truncated ambient FUNCTION:
`∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁`. That type is not `Formula S 1`. There is no
constructor that takes a function. A function cannot be the `φ`
parameter of `sep`. This is the measurement. `[LJ-1.399]` wall 2 named
the same door at a different map
(`agents/tasks/LJ-1-399/lj-1.399-report.md:83-91`); this paragraph is
the measurement at `sep` itself.

### 2.4 `[LJ-1.414]` HALF A (`agents/tasks/LJ-1-414/Probe414.agda:65-66`)

`κ` carries three things a generic `d` does not. Each, separately:

1. **Minimality** (`src/L/Cardinal.lagda.md:140-141`, `κ-min-at`). This
   is a negative statement: no smaller ordinal receives an injection from
   `a`. A negative statement does not give a graph. Combined with
   `idInj` (`src/L/Cardinal.lagda.md:109-110`) it proves the subset
   hypothesis of `OrdIncl` at `(a, κ)` is false (section 2.1). That is
   all it pays.

2. **Membership in `sucV (fst a)`** (`src/L/Cardinal.lagda.md:129-130`).
   This locates `κ`. It instantiates `OrdIncl` in the wrong direction
   (section 2.1). Location is not a graph of `κ-inj`.

3. **The arrow comes from a `leastOf` selection**
   (`src/L/Cardinal.lagda.md:116-117`, `:132-134`). `leastOf` selects the
   least INDEX `γ-card` (`src/L/Cardinal.lagda.md:119-120`). The payload
   `κ-inj` stays truncated (`src/L/Cardinal.lagda.md:133`). The
   literature states the constraint: `leastOf` delivers the least index
   untruncated, and a data payload does not come out
   (`dev/literature/truncation-and-selection.md:146-148`). Selection of
   the ordinal is not a graph of the injection.

None of the three gives a graph.

The `[LJ-1.414]` report returned NO-GO on the general implication and
did not refute it (`agents/tasks/LJ-1-414/lj-1.414-report.md:39`). This
task does not inhabit that general type. It asks the same HALF A at one
named pair.

## 3. W3, `half-a-at-kappa`

THE PROBE instantiates `code-from-graph`
(`agents/tasks/LJ-1-414/Probe414.agda:115-125`) at `x := a` and
`d := κ`, with its four hypotheses left as bare module hypotheses
(`Probe426.agda:117-130`). HALF A is not attempted. Audit finding F6
records that the one attempt to join the halves reached 8.5 GB RSS and
was killed (`dev/pod/audit-2026-08-20.md:88`).

`from-graph` (`Probe426.agda:129-130`) is GREEN given those four as
module hypotheses. The three GREEN rechecks below were of this file with
`from-graph` and without the `kappa-coded` hole. The hole was then added.
The three hole rechecks are section 4. One Agda process, caliber
`GHCRTS="-A64m -I0 -M8g"`:

| run | real s | max RSS bytes | file |
|---|---|---|---|
| 1 | 1.79 | 396509184 | `runs/w3-1.time:1-2` |
| 2 | 1.64 | 396460032 | `runs/w3-2.time:1-2` |
| 3 | 1.71 | 396460032 | `runs/w3-3.time:1-2` |

Median 1.71 s. Peak RSS 396509184 bytes. No heap event.

Which of the four has a producer in the live tree, and which does not.
Each at `file:line`. **None of the four has a producer at the pair
`(a, κ)`.** The live tree produces the same shapes for other maps, and
those sites are named so the claim can be checked.

| hyp | site in this probe | producer at `(a, κ)` | live producer of the shape, not at this pair |
|---|---|---|---|
| `pair-out` | `Probe426.agda:119-120` | none | `InclGraph.pair-out`, `src/L/InjChain.lagda.md:494-495`, for the inclusion of `D` into `C` |
| `pair-in` | `Probe426.agda:121-122` | none | `InclGraph.pair-in`, `src/L/InjChain.lagda.md:509-511`, same graph |
| `uniq` | `Probe426.agda:123-124` | none | argument of `svAt-in` at `src/L/InjChain.lagda.md:519`, derived from that `pair-out` |
| `inj-mem` | `Probe426.agda:125-126` | none | argument of `injAt-in` at `src/L/InjChain.lagda.md:526`, derived from that `pair-out` |

`code-from-graph` (`Probe426.agda:90-104`) consumes the four. It does
not produce any of them. `Comp` (`src/L/InjChain.lagda.md:314-324`)
consumes two already-coded graphs. It does not produce a first factor
at this pair.

Measured size, code lines of the instantiation (the brief's comparable
of SHAPE, `Probe414.agda:115-125`): `FromGraph` plus `from-graph` is
`Probe426.agda:117-130`, fourteen lines. The copy of `CodeFromGraph` is
`Probe426.agda:51-104`, the same telescope `[LJ-1.414]` already paid.
Comparables of shape, not of size. Nothing is funded against them.

## 4. THE OBLIGATION

`kappa-coded` (`Probe426.agda:135-136`) is the brief's type. It is a
hole. HALF A at this pair has no producer, so the truncated existence
has no term. The hole is red by design, as `[LJ-1.414]` left
`amb-to-coded` (`Probe414.agda:139`).

Three forced rechecks of the delivered file, hole in place:

| run | real s | max RSS bytes | file |
|---|---|---|---|
| 1 | 1.66 | 393084928 | `runs/kappa-coded-hole-1.time:1-2` |
| 2 | 1.68 | 393101312 | `runs/kappa-coded-hole-2.time:1-2` |
| 3 | 1.69 | 393101312 | `runs/kappa-coded-hole-3.time:1-2` |

Median 1.68 s. Peak RSS 393101312 bytes. Exit 42,
`UnsolvedInteractionMetas` at `Probe426.agda:136`
(`runs/kappa-coded-hole-1.out:2-4`). No heap event.

No invented hypothesis. The truncated injection does not become a code.

A GO would have named the chapter that supplied the graph and the cost
of a `src/` landing. No chapter supplied the graph. A landing is not
priced, because the graph is the missing link.

## 5. W8, LITERATURE

Read before any Agda. See D-10 and section 2. The sources pick a
definable map (a collapse of a hull, a least witness of a formula). They
do not code an arbitrary ambient injection, and they do not code the
payload of `leastOf`. That is why the unconditional `kappa-coded` is not
an assembly from live chapters.

## 6. C-42

No refutation landed. C-42's sweep of a false shape does not apply. The
named missing link is HALF A at `(a, κ)`, which is smaller than
`[LJ-1.414]`'s general implication.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read. `:1` "# THE `LJ` DISPATCH INDEX,
  archived 2026-08-18". Declined. It is a dispatch index. It does not bear
  on whether the least-cardinal arrow is coded.
- `archive/dev/JOURNAL-archived.md`: read. `:1` "# Archived journal: the
  retired route". Declined. It is the retired-route journal. This task
  measures the live `InjCode`.
- `archive/dev/JOURNAL.md`: read. `:1` "# ARCHIVED 2026-08-20". Declined.
  It is an archived journal. The live record of this task is this
  directory.
- `dev/ARCHIVE.md`: read. `:1` "# ARCHIVE.md: the archive registry".
  Declined. This task does not retire a module.
- `archive/dev/DD-archived.md`: read. `:1` "# THE `DD` RULING SERIES,
  archived in full 2026-08-18". Declined. The rulings archive does not
  bear on HALF A at `κ`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read. `:75` "13.20
  (`dev/literature/devlin-II5.md:145-166`). **A cardinal inequality is a"
  and `:76` "truncated existence of an injection.** That is the HoTT
  Book's own definition,". Used for D-10: the ambient arrow is truncated
  existence. Also `:148` "index is a proposition. **A data payload does
  not come out.**" Used for candidate 4: `leastOf` does not deliver a
  graph.
- `dev/literature/devlin-II5.md`: read. `:72` "> 5.2 Theorem (The
  Condensation Lemma). Let α be a limit ordinal. If". Used for D-10 and
  W8: the literature's embedding is a collapse of a hull, not an
  arbitrary ambient injection.
- `dev/literature/digest.md`: read. `:45` "limit α (SZ pp. 9-10, equation
  I.1). Condensation is at the Sigma-1". Used as the orthodox statement
  of the same hypothesis: a Σ₁ embedding, not an arbitrary function.
- `dev/literature/terms-2026-08.md`: read. `:1` "# The terminology
  dossier: fourteen renderings for the owner's ruling". Declined. It is
  a terminology dossier. It does not bear on coding the least-cardinal
  arrow.
- `dev/literature/geology.md`: read. `:1` "# Geology dossier:
  set-theoretic geology sources and the five questions". Declined. It is
  a geology dossier. It does not bear on this obligation.

## WHAT THE NEXT BRIEF NEEDS

HALF B at `(a, κ)` is paid as a module, given the four membership
readings. None of the four has a producer at this pair. The remaining
type is HALF A at one named ordinal: a graph of `κ-inj`, as an
L-element. That is a smaller object than `[LJ-1.414]`'s general
implication.

A next brief that wants a code at this map must supply a `Formula` for
that map, or some other producer of the four readings at `(a, κ)`. A
next brief that wants to join HALF A to HALF B must not: audit finding
F6 records that the one attempt was killed at 8.5 GB RSS
(`dev/pod/audit-2026-08-20.md:88`). The type is not refuted. Naming HALF
A at `κ` exactly is what `[LJ-2.5]` needs.
