# LJ-1.460 report: a code for the shift, from the carved graph

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-460/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-460/Probe460.agda`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

Nothing lands in `src/`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:38`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict.

## WHY THIS IS NOT THE STATEMENT THAT FAILED THREE TIMES

Written before any Agda.

`amb-to-coded` at `agents/tasks/LJ-1-414/Probe414.agda:134-139`:

    amb-to-coded :
        (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
      → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
      → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁

The arrow is an arbitrary truncated injection. The use site that failed
three times takes that arrow from `leastOf`. `least` at
`src/L/Cardinal.lagda.md:117` is `leastOf w lem InjP' nonempty`. The
witness `κ-inj` at `:133-134` is still truncated. The predicate `InjP'`
at `:82-83` is `InjP (up γ)`, and `InjP` at `:66-67` is
`∥ Inj γ ∥₁`. No `Formula` sits on that selection. `[LJ-1.441]`
recorded the same obstruction
(`agents/tasks/LJ-1-441/lj-1.441-report.md:53`).

`shift-coded` at the type above asks for a code of ONE function: the
shift `sucV γ ↪ γ` at `src/L/Absorption.lagda.md:614-617`. That
function has a defining formula `shiftFo`
(`src/L/Absorption.lagda.md:223-225`). `ShiftGraph` already separated
on it (`:604-605`). C-42: a NO-GO on the `leastOf` graph does not
measure this site.

## D-10, BEFORE ANY AGDA

`[LJ-1.414]` HALF B is `code-from-graph` at
`agents/tasks/LJ-1-414/Probe414.agda:115-125`. Four hypotheses. The
audit at `dev/pod/audit-2026-08-20.md:83-89` measured that 414 never
joined them to HALF A. The four, and the `ShiftGraph` export that
supplies each:

1. **pair-out** (`Probe414.agda:117-118`):
   `(u v : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩ → ⟨ fst u ∈ fst x ⟩ × ⟨ fst v ∈ fst d ⟩`.
   Supplier: `Carve.pair-out` at `src/L/Absorption.lagda.md:428-430`,
   opened publicly by `ShiftGraph` at `:604-605`. That reading is
   truncated and names `val`. Both memberships are hProps, so `PT.rec`
   spends the truncation. The second conjunct is also `ran` at `:494`.
   The first conjunct is the field `m : ⟨ u ∈ˢ D ⟩` after subst along
   `fst x ≡ fst u`.

2. **pair-in** (`Probe414.agda:119-120`):
   `(u : S) → ⟨ fst u ∈ fst x ⟩ → ∥ Σ[ v ∈ S ] ⟨ pr (fst u) (fst v) ∈ fst G ⟩ ∥₁`.
   Supplier: `Carve.pair-in` at `:441-442`. It returns a specific
   `val` untruncated. Truncation plus that term inhabits the 414 type.
   `dm`'s `bwd` at `:490-492` is the same type with `∃` syntax.

3. **uniq** (`Probe414.agda:121-122`):
   `(u v v' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩ → ⟨ pr (fst u) (fst v') ∈ fst G ⟩ → fst v ≡ fst v'`.
   Supplier: the local `go` inside `sv` at `:455-464`. `sv` itself is
   exported at `:452`. The same `go` rebuilds from `pair-out` at `:428`
   and `Fo.val-cong`. `Fo` is the public `ShiftFo` alias at `:403`.

4. **inj-mem** (`Probe414.agda:123-124`):
   `(v u u' : S) → ⟨ pr (fst u) (fst v) ∈ fst G ⟩ → ⟨ pr (fst u') (fst v) ∈ fst G ⟩ → fst u ≡ fst u'`.
   Supplier: the local `go` inside `ij` at `:469-478`. `ij` itself is
   exported at `:466`. The same `go` rebuilds from `pair-out` at `:428`
   and `Fo.val-inj`.

No hypothesis lacks a supplier. I do not stop.

**What the mathematician named as missing is already exported.**
`Carve` builds the four conjuncts at `:448-498` and `ShiftGraph`
opens `Carve` publicly at `:604-605`. So `sv`, `dm`, `ij`, `ran`
are `ShiftGraph` exports. HALF B's output is in `src/`. I do not
rebuild HALF B from 414's four inputs. I do not take HALF B as a
module hypothesis. I pack the four conjuncts. I do not import a
probe. `[LJ-1.294]` already packed the same tuple at
`agents/tasks/LJ-1-294/CardinalLimit.agda:108-109`, then transported
the domain. That probe is not imported.

## GREP, ShiftGraph IN src/

`grep -n ShiftGraph src/` returns two lines, both in
`src/L/Absorption.lagda.md`:

- `:538` the module header
- `:619` the one instantiation inside `absorbs`

No consumer outside that chapter. The graph has no consumer in `src/`.

## VERDICT

**GO.** The obligation typechecks
(`agents/tasks/LJ-1-460/Probe460.agda:73-88`, exit 0, median 1.73 s on
three forced rechecks) and it PASSes the program's witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-460 --brief agents/tasks/LJ-1-460/LJ-1.460.md`, exit 0,
1.56 s, 0 UNRESOLVED of 1, `probe_red=False`). This worktree has no
`.venv`. The witness meter ran under the parent venv. I added no
dependency. I did not write `review-of-shift-coded.md`. The GO branch
forbids that file.

The exact type inhabited, so the next brief can quote it without
opening the probe, is at `Probe460.agda:73-76`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

The four conjuncts come out at `G ∷ D ∷ []` as
`SG.sv , SG.dm , SG.ij , SG.ran` (`Probe460.agda:81-82`). `D` is not
`sucʟ γ` as `S`. `fst D` is `sucV (fst γ)` by construction
(`src/L/Absorption.lagda.md:545`). `sucʟ-fst` at
`src/L/Axioms/Numerals.lagda.md:152` gives
`fst (sucʟ γ) ≡ sucV (fst γ)`. One `Σ≡Prop` along
`sym (sucʟ-fst γ)` (`Probe460.agda:84-85`) moves the tuple, because
`isL` is a proposition (`src/L/Constructible.lagda.md:376-377`). No
hole. No extra hypothesis. No postulate.

This GO is a truncated code for the shift at a generic infinite
L-ordinal that holds every numeral. It is not a code for a
`leastOf` selection. C-42: a measurement of this site does not
measure `amb-to-coded`.

## 1. W2 (DD4)

The mathematics is written once at a generic infinite L-ordinal `γ`
that holds every numeral. `ShiftGraph` is that generic carrier
(`src/L/Absorption.lagda.md:538-540`). This probe instantiates it.
It does not copy the four conjuncts. Both trophies that need a
non-identity code can share that chapter. No deadline asked for a
fixed form.

## 2. W3: `range-clause`

**GO.** Typechecked ALONE, with the obligation omitted. Caliber
`-A64m -I0 -M8g`, set on the pane, untouched. One Agda process. The
probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-460/Probe460.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.99 | 412188672 |
| `runs/w3-2.out` / `w3-2.time` | 1.64 | 412172288 |
| `runs/w3-3.out` / `w3-3.time` | 1.58 | 412172288 |

Median wall **1.64 s**. Median peak RSS **412172288 bytes**. No heap
event.

The truncation spent. `pair-out` at
`src/L/Absorption.lagda.md:428-431` is `PT.map` over `G-out` at the
coded pair. The conclusion `⟨ fst y ∈ fst γ ⟩` is an hProp, so
`PT.rec` at `Probe460.agda:59` spends it. The body is the same
subst-and-member step `ran` uses at
`src/L/Absorption.lagda.md:495-498`. W3 did not call `ran`. It
rebuilt the clause from the reading, as the brief asked.

The conjunct is reachable. The task did not stop at W3.

## 3. The obligation

After W3 was green I added `shift-coded` (`Probe460.agda:73-88`). I
did not import `LJ-1-414.Probe414` or `LJ-1-294.CardinalLimit`. I
did not rebuild HALF B from 414's four inputs. I packed the four
conjuncts `ShiftGraph` already exports.

Three forced rechecks of the full file, probe interface deleted,
dependencies warm, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.72 | 409092096 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.73 | 409108480 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.73 | 409092096 |

Median wall **1.73 s**. Median peak RSS **409092096 bytes**. No heap
event.

Against W3's median 1.64 s the packaging moved the figure by 0.09 s.
The first full check after the term was added was exit 42 on
`ShadowedModule` (`runs/full-1.out`): the W3 block was an anonymous
`module _` and leaked `SG` into the parent. I named that block
`module W3` (`Probe460.agda:51`). The next check was exit 0. That
first red run is not a price. The three rechecks above are the
price.

## WHAT A CODE HERE BUYS

`Residue` at `agents/tasks/LJ-1-447/Probe447.agda:208-210`, restated
at `agents/tasks/LJ-1-456/Probe456.agda:95-99`:

    Residue =
        (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
      → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
      → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

At `y := fst (sucʟ γ)` that type is:

    (oy : IsOrd (fst (sucʟ γ))) → ⟨ ω ∈ˢ fst (sucʟ γ) ⟩
      → ⟨ fst (κL (fst (sucʟ γ) , isL-ord (fst (sucʟ γ)) oy) oy) ∈ˢ fst (sucʟ γ) ⟩
      → ⟨ fst (κC (fst (sucʟ γ) , isL-ord (fst (sucʟ γ)) oy) oy) ∈ˢ fst (sucʟ γ) ⟩

`shift-coded` does not supply that type. It supplies
`∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁`. That is a code of the
shift, not a membership of `κL` or `κC` in the successor.
`[LJ-1.446]` gives the ordering `κC` not strictly below `κL` at one
site (`agents/tasks/LJ-1-446/Probe446.agda:203-206`). One site is
not the band. This report does not claim `Residue` in general.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. What the shape resisted, and what closed

The four conjuncts did not resist. They were already exports. The
domain resisted: `D` and `sucʟ γ` agree on `fst` and differ as `S`.
One `Σ≡Prop` closed that. The range truncation did not resist:
`PT.rec` spent it at W3. Nothing was weakened. Nothing was left a
hole.

The brief's size guess was about 150 lines, of which the obligation
was about 40. The probe is 88 lines. The obligation is 16 lines
(`Probe460.agda:73-88`). The chapter had already paid the
conjuncts. Comparables of shape do not fund a count.

What the next brief needs: this tree now has a truncated
`InjCode` for a non-identity injection, at `sucʟ γ` into `γ`, for
every infinite L-ordinal that holds every numeral. The graph still
has no consumer in `src/`. A user of this code in a chapter would
import `L.Absorption` and pack the same four exports. The
transport along `sucʟ-fst` is the only packaging. `Residue` at
`y := fst (sucʟ γ)` is still open. This term does not close it.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read. `:3` reads
  `Status: ARCHIVED RECORD. It is never rewritten.`. Declined: the
  retired dispatch table. This task's code is not a row I needed.
- `archive/dev/JOURNAL-archived.md`: read. `:1` reads
  `# Archived journal: the retired route`. Declined: a dated record
  of the retired route, not the shift graph.
- `archive/dev/JOURNAL.md`: read. `:1` reads
  `# ARCHIVED 2026-08-20`. Declined: per-episode journal, retired.
  The product of this task sits in `agents/tasks/LJ-1-460/`.
- `dev/ARCHIVE.md`: read. `:1` reads
  `# ARCHIVE.md: the archive registry`. Declined: no module was
  retired, so no row is written.
- `archive/dev/DD-archived.md`: read. `:3` reads
  `Status: ARCHIVED RECORD. Never rewritten, never deleted.`. Declined:
  archived DD series, not the carved shift.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read and used.
  `:143` reads
  `the reason: "a proposition-valued goal absorbs the truncation"`.
  W3's conclusion is an hProp, so `PT.rec` spends `pair-out`.
- `dev/literature/devlin-II5.md`: read. `:1` reads
  `# Devlin II.5: the Condensation Lemma and the GCH in L`.
  Declined: condensation and GCH, not the shift code.
- `dev/literature/terms-2026-08.md`: read. `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined: a glossary dossier, not this code.
- `dev/literature/digest.md`: read. `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined: the rud-route digest, not the shift graph.
- `dev/literature/glossary-review-2026-08.md`: read. `:1` reads
  `# Glossary review: the 119 pre-protocol entries`.
  Declined: glossary review, not this code.
