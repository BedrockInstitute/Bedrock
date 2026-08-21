# LJ-1.465 report: whether 460's code reaches 446's selection

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-465/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-465/Probe465.agda`:

    residue-at-successor-446 :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ⟨ fst (κC (sucʟ γ) (suc-ord oγ)) ∈ˢ fst (sucʟ γ) ⟩

`κC` is `[LJ-1.446]`'s coded selection, not `[LJ-1.464]`'s. Nothing
lands in `src/`.

This is successors that hold every numeral. It is not `Residue`. The
limit case is untouched.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict.

## PREDECESSOR VERDICTS, BEFORE ANY AGDA

- `[LJ-1.464]` `agents/tasks/LJ-1-464/lj-1.464-report.md:91` reads
  `**GO.** The obligation typechecks`. Delivered type
  `agents/tasks/LJ-1-464/Probe464.agda:199-204`:

      residue-at-successor :
          (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
          (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
          (F : S) (code : InjCode F (sucʟ γ) γ)
        → ⟨ fst (W3.κC γ oγ γ∉ω numerals F code) ∈ˢ fst (sucʟ γ) ⟩

  That `κC` is local to `W3` and depends on `F`. The report at
  `lj-1.464-report.md:127-129` says this GO does not say that 446's
  `κC` is a member of `sucʟ γ`.

- `[LJ-1.446]` `agents/tasks/LJ-1-446/lj-1.446-report.md:74` reads
  `**GO.** `kappaC-not-below` typechecks`. Delivered type
  `agents/tasks/LJ-1-446/Probe446.agda:203-206`, under
  `module _ (a : S) (oa : IsOrd (fst a))` (`:117`) and
  `module _ (coded-nonempty : ...)` (`:164-166`):

      kappaC-not-below :
          ⟨ fst κC ∈ˢ fst (κL a oa) ⟩ → Empty.⊥

  `κC` is a local `S` at `Probe446.agda:194-195`, selected at the
  InclGraph bound of `a`.

- `[LJ-1.460]` `agents/tasks/LJ-1-460/lj-1.460-report.md:110` reads
  `**GO.** The obligation typechecks`. Delivered type
  `agents/tasks/LJ-1-460/Probe460.agda:73-76`:

      shift-coded :
          (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
          (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
        → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

No predecessor report is NO-GO. No predecessor names the statement
FALSE. I take those types and those verdicts. I do not stop.

## D-10, BEFORE ANY AGDA

The two selection predicates, written as types.

`[LJ-1.464]` at `agents/tasks/LJ-1-464/Probe464.agda:105-107`, inside
`module W3` with `a = sucʟ γ` (`:64-65`) and `γb = sucV stgF` (`:78-79`):

    CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
    CodedInjP' d =
      ∥ Σ[ G ∈ Mem (Lset γb) ] InjCode (upγ G) a (upα d) ∥₁ , squash₁

`[LJ-1.446]` at `agents/tasks/LJ-1-446/Probe446.agda:158-160`, inside
`module _ (a : S) (oa : IsOrd (fst a))` (`:117`), with `γ` equal to
`bound2 β (sucV stgG) oβ (suc-ord oStg) .fst` (`:132-136`) and
`stgG = stage (fst G) (snd G)` for `G = InclGraph a a` (`:121-127`):

    CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
    CodedInjP' d =
      ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

They differ in more than the bound. Every index, named:

1. **The carrier of the predicate.** Both are
   `⟪ sucV (fst a) ⟫`. MATCH when `a := sucʟ γ`.
2. **`upα`.** Both are the LeastCardInjL crossing at
   `Probe446.agda:153-155` and `Probe464.agda:100-102`. MATCH.
3. **The `InjCode` shape.** Both are
   `InjCode (upγ _) a (upα d)`. MATCH.
4. **The host of the graph.** 464 uses `Mem (Lset γb)` with
   `γb = sucV (stage F)` (`Probe464.agda:72-79`). 446 uses
   `Mem (Lset γ)` with `γ = bound2 β (sucV (stage G))` for
   `G` the inclusion graph of `a` (`Probe446.agda:121-136`).
   DIFFER. 464's host depends on `F`. 446's host depends on `a`
   only.
5. **The graph that names the host.** 464 uses the hypothesized
   shift code `F`. 446 uses `InclGraph a a`. DIFFER.

The one difference that blocks the join is (4): an abstract
`F : S` from 460 has type `S`, not `Mem (Lset γ)` at 446's
`γ`. 464 named this at `lj-1.464-report.md:271-273`. 438's
device (`Probe438.agda:89-93`) places `InclGraph`'s `G` in that
`Lset`. It does not place an abstract `F`.

The target is not false on a Tarskian or cardinality ground. 460
delivers a code. 446 delivers a selection. The question is
whether that code inhabits that predicate. Corrected target:
none. Original target stands. W3 measures whether the two meet.

## VERDICT

**NO-GO.** `fits-446` does not typecheck
(`agents/tasks/LJ-1-465/Probe465.agda:156-158`, exit 42,
`UnequalTerms`, class `other`). The obstruction is
`agents/tasks/LJ-1-465/review-of-residue-at-successor-446.md`.
The obligation is not a term. 446's `κC` is selected only after
a nonempty at that bound (`Probe446.agda:164-195`). Without
`fits-446` there is no `κC (sucʟ γ) (suc-ord oγ)` to inhabit.

This NO-GO says the one delivered code does not reach the
selection the campaign's other results use. It does not say the
membership is false of the carved `ShiftGraph.G`. 460's type
forgets the carve. C-42: a measurement of this site does not
measure Residue, and it does not measure the limit case.

## 1. W2 (DD4)

The mathematics is written once at a generic infinite L-ordinal
`γ` that holds every numeral. `W3` is that generic carrier
(`Probe465.agda:61-64`). Both trophies that need membership of
446's `κC` at a successor can share this code, if a later lemma
places the graph. The carrier is one L-element, not a named
cardinal. No deadline asked for a fixed form.

## 2. W3: `fits-446`

**NO-GO.** Typechecked ALONE, with the obligation omitted.
Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One Agda
process. The probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-465/Probe465.agdai`).

Three forced rechecks, exit 42 every time, each printed
`Checking` then `UnequalTerms` at `Probe465.agda:158`:

```
fst F != fst IG.G of type V ℓ
when checking that the expression stage-mem (fst F) (snd F) has
type ⟨ fst F ∈ˢ Lset stgG ⟩
```

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.19 | 710983680 |
| `runs/w3-2.out` / `w3-2.time` | 1.84 | 711065600 |
| `runs/w3-3.out` / `w3-3.time` | 1.83 | 710983680 |

Median wall **1.84 s**. Median peak RSS **710983680 bytes**. No
heap event. The 8 g caliber was not approached.

The packing that fails, at `d` the index of `γ`
(`Probe465.agda:124-126`):

- `shift-coded` is 460's delivered truncation
  (`Probe465.agda:64`). `CodedInjP' d` is an hProp, so `PT.rec`
  is legal (`Probe465.agda:142`). Truncation is not the killer.
- range by `code-target-swap` along `sym d-eq`
  (`Probe465.agda:163-164`). Rebuilt from `Probe438.agda:108-112`.
  This device is not reached.
- first argument by `Σ≡Prop` on `isL`
  (`Probe465.agda:166-167`). This device is not reached.
- host by 438's `Lset-mono` along `stgG ∈ γB`, then
  `stage-mem` of `F` (`Probe465.agda:156-158`). Agda refuses:
  `stage-mem F` lands in `Lset (stage F)`, and the 438 witness
  lands in `Lset stgG`. `fst F != fst IG.G`.

The two do not meet. That mismatch is the finding. 460 codes
into `γ` as an L-element. 446 lifts with `upα` over
`⟪ sucV (fst a) ⟫`. The index and the range can be packed, as
464 packed them. The host cannot: 446's `Mem (Lset γB)` wants
a member of the InclGraph bound, and 460's `F : S` is not
`IG.G`.

I did not add a hypothesis to cross the bound. I did not
rebuild the carve. I did not change 446's bound to include
`stage F`.

Named packing that is not the failure: `oa` along `sucʟ-fst`
(`Probe465.agda:71-73`), the same one 464 recorded at
`Probe464.agda:67-68`. `suc-ord oγ` has type
`IsOrd (sucV (fst γ))`. SiteBound wants `IsOrd (fst (sucʟ γ))`.

## 3. The obligation

Not written. W3 is the whole probe. The three W3 rechecks are
the full-file numbers. There is no second measurement.

What the shape resisted: the 446 bound. An abstract `F : S`
does not inhabit `Lset` of `bound2 (SiteBound.β a) (sucV (stage G))`
for `G` the inclusion graph of `a`. I copied
`Probe446.agda:117-160`. I applied 438's placement of `G` to
`F`. Agda named the two graphs.

What was weakened: nothing. The telescope of the brief is not
inhabited. The truncation of 460 is not spent, because the pack
dies before `∣ Fg , movedγ ∣₁` typechecks. No postulate.

The brief's size guess was about 170 lines, of which the
obligation was about 30. The probe is 177 lines. The
obligation at the top-level name is 0 lines. Comparables of
shape do not fund a count.

P-l did not fire as a cost: the types name `⟪ sucV (fst a) ⟫`.
D-26 does not fire: no new well-founded key.

## WHAT RESIDUE STILL OWES

`Residue` at `src/L/StageBound.lagda.md:51-59`, restated at
`agents/tasks/LJ-1-447/Probe447.agda:208-210`:

    Residue isL-ord κL κC =
        (y : S) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
      → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
      → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

This task does not cover SUCCESSORS at 446's `κC`. 464 covers
SUCCESSORS of infinite L-ordinals that hold every numeral, for
the coded selection at the stage of a chosen shift code. It
does not cover 446's `κC`. One class is not the band. C-42
rules that in both directions.

What remains, as a type, the LIMIT ordinals `y` with `κL(y) ∈ y`,
at `[LJ-1.464]`'s shape (`lj-1.464-report.md:248-254`):

    Residue-at-limit :
        (y : V ℓ) (oy : IsOrd y)
      → ⟨ ω ∈ˢ y ⟩
      → ((γ : V ℓ) → (y ≡ sucV γ) → Empty.⊥)
      → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
      → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

I did not attempt it. I do not price it from this task's
seconds.

The successor remainder at 446's selection is still open, at
the same type 464 named (`lj-1.464-report.md:264-268`) and this
brief restated. Closing it needs a lemma that a shift code
lives in 446's bound, or a ruling that 464's F-stage selection
is the coded least cardinal Residue may use. This task is
neither.

What the next brief needs: that lemma, or that ruling, or the
limit case by a different code. This return is the mismatch
between 460's type and 446's host.

## 4. C-42, the sweep

The shape is: an abstract `F : S` from 460 against
`Mem (Lset γB)` at 446's InclGraph `bound2`.

`CodedInjP'` occurs in six probes:

| site | host of the graph | places abstract F in 446's bound? |
|---|---|---|
| `Probe430.agda:82` | generic `γ` | no |
| `Probe431.agda:120` | generic `γ` | no |
| `Probe446.agda:158` | InclGraph `bound2` | no; nonempty is 438's `G` |
| `Probe447.agda:128` | generic `γ` | no; nonempty is a hypothesis |
| `Probe464.agda:105` | `sucV (stage F)` | no; different host, GO |
| `Probe465.agda:110` | InclGraph `bound2` | yes; this NO-GO |

COUNT: **1** Agda site of the failing placement (this probe).
**1** named refusal without a term (`lj-1.464-report.md:271-273`).
**0** in `src/`. `Residue` at `src/L/StageBound.lagda.md:51`
names `κC` as a parameter and does not fix the host.

A cure funded against this site is funded against one measured
occurrence. I do not price that cure.

## 5. W4

No module was retired. Nothing moved to `archive/`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read.
  `archive/dev/LJ-dispatch-index.md:1` quotes:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`
  Declined: the retired dispatch table. This task's code is not a
  row I needed.
- `archive/dev/JOURNAL-archived.md`: read.
  `archive/dev/JOURNAL-archived.md:1` quotes:
  `# Archived journal: the retired route`
  Declined: a dated record of the retired route, not the shift
  code and not Residue.
- `archive/dev/JOURNAL.md`: read.
  `archive/dev/JOURNAL.md:1` quotes:
  `# ARCHIVED 2026-08-20`
  Declined: per-episode journal, retired. The product of this task
  sits in `agents/tasks/LJ-1-465/`.
- `dev/ARCHIVE.md`: read.
  `dev/ARCHIVE.md:1` quotes:
  `# ARCHIVE.md: the archive registry`
  Declined: no module was retired, so no row is written.
- `archive/dev/DD-archived.md`: read.
  `archive/dev/DD-archived.md:1` quotes:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`
  Declined: archived DD series, not the coded selection.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read and used.
  `dev/literature/truncation-and-selection.md:146` quotes:
  `**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf``
  `CodedInjP'` is hProp-valued, so `PT.rec` on `shift-coded` is
  legal (`Probe465.agda:142`). Truncation is not the killer.
  The host is.
  Also `dev/literature/truncation-and-selection.md:143` quotes:
  `the reason: "a proposition-valued goal absorbs the truncation"`
  The membership conclusion would also absorb, if the pack
  reached it.
- `dev/literature/devlin-II5.md`: read.
  `dev/literature/devlin-II5.md:1` quotes:
  `# Devlin II.5: the Condensation Lemma and the GCH in L`
  Declined: condensation and GCH, not the shift code at a
  successor.
- `dev/literature/terms-2026-08.md`: read.
  `dev/literature/terms-2026-08.md:1` quotes:
  `# The terminology dossier: fourteen renderings for the owner's ruling`
  Declined: a glossary dossier. This task writes no glossary
  entry.
- `dev/literature/digest.md`: read.
  `dev/literature/digest.md:1` quotes:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`
  Declined: the rud-route digest, not the coded selection.
- `dev/literature/glossary-review-2026-08.md`: read.
  `dev/literature/glossary-review-2026-08.md:1` quotes:
  `# Glossary review: the 119 pre-protocol entries`
  Declined: glossary review, not this code.
