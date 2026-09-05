# LJ-1.464 report: how far the shift code reaches, and what is left of Residue

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-464/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-464/Probe464.agda`:

    residue-at-successor :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ⟨ fst (κC (sucʟ γ) (suc-ord oγ)) ∈ˢ fst (sucʟ γ) ⟩

Nothing lands in `src/`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict.

## PREDECESSOR VERDICTS, BEFORE ANY AGDA

- `[LJ-1.460]` `agents/tasks/LJ-1-460/lj-1.460-report.md:110` reads
  `**GO.** The obligation typechecks`. Delivered type
  `agents/tasks/LJ-1-460/Probe460.agda:73-76`:

      shift-coded :
          (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
          (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
        → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

- `[LJ-1.446]` `agents/tasks/LJ-1-446/lj-1.446-report.md:74` reads
  `**GO.** `kappaC-not-below` typechecks`. Delivered type
  `agents/tasks/LJ-1-446/Probe446.agda:203-206`, under
  `module _ (a : S) (oa : IsOrd (fst a))` (`:117`) and
  `module _ (coded-nonempty : ...)` (`:164-166`):

      kappaC-not-below :
          ⟨ fst κC ∈ˢ fst (κL a oa) ⟩ → Empty.⊥

No predecessor report is NO-GO. No predecessor names the statement
FALSE. I take those types and those verdicts. I do not stop.

## D-10, BEFORE ANY AGDA

The two types, written out.

`[LJ-1.460]` delivers, at `Probe460.agda:73-76`:

    ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

`κC`'s selection predicate, at `agents/tasks/LJ-1-430/Probe430.agda:82-84`:

    CodedInjP' : ⟪ sucV (fst a) ⟫ → hProp (ℓ-suc ℓ)
    CodedInjP' d =
      ∥ Σ[ F ∈ Mem (Lset γ) ] InjCode (upγ F) a (upα d) ∥₁ , squash₁

At `d` the index of `γ` in the successor carrier of `a := sucʟ γ`,
the delivered code is NOT an inhabitant of that predicate on the
nose. Four indices:

1. **F's sort.** 460 gives `F ∈ S`. The predicate wants
   `F ∈ Mem (Lset γ_bound)` and then uses `upγ F`. `S` is not
   `Mem (Lset γ_bound)`.
2. **The graph used.** 460 uses `InjCode F`. The predicate uses
   `InjCode (upγ F)`.
3. **The domain.** 460 uses `sucʟ γ`. The predicate uses `a`. These
   MATCH if `a := sucʟ γ`. Named, not a `subst`.
4. **The range.** 460 uses `γ` as an L-element. The predicate uses
   `upα d` with `d : ⟪ sucV (fst a) ⟫`. These MATCH after the named
   device `fiber` plus 438's `code-target-swap` along
   `⟪ sucV (fst a) ⟫↪ d ≡ fst γ`. They do not match on the nose.

The 446 reconstruction of the bound (`Probe446.agda:117-136`) is a
function of `a` only: `bound2` of `SiteBound.β` and
`sucV (stage (InclGraph a a))`. An abstract `F : S` from 460 has no
lemma that places `fst F` in that `Lset`. A bound that hosts `F` is
`F`'s own stage, which depends on `F`. So a `κC` selected at that
bound depends on `F`. 460 delivers `F` truncated. A truncated `F`
cannot define an F-independent `κC` and cannot inhabit 446's
`CodedInjP'` at a bound that does not know `F`.

Corrected target: the membership at a successor, for the coded
selection whose bound is the stage of a chosen code. Original
target stands as a type. W3 measures whether the two meet.

## VERDICT

**GO.** The obligation typechecks
(`agents/tasks/LJ-1-464/Probe464.agda:199-204`, exit 0, median 3.11 s
on three forced rechecks) and it PASSes the program's witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-464 --brief agents/tasks/LJ-1-464/LJ-1.464.md`, exit 0,
1.77 s, 0 UNRESOLVED of 1, `probe_red=False`). This worktree has no
`.venv`. The witness meter ran under the parent venv. I added no
dependency. I did not write `review-of-residue-at-successor.md`. The
GO branch forbids that file.

The exact type inhabited, so the next brief can quote it without
opening the probe, is at `Probe464.agda:199-204`:

    residue-at-successor :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
        (F : S) (code : InjCode F (sucʟ γ) γ)
      → ⟨ fst (W3.κC γ oγ γ∉ω numerals F code) ∈ˢ fst (sucʟ γ) ⟩

Three packagings, each named, none hidden in a `subst` of the
predicate:

1. **The inner of 460, not the truncation.** 460 delivers
   `∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁`. The bound that hosts `F`
   is `F`'s stage (`Probe464.agda:72-82`). That bound depends on
   `F`. The membership conclusion names one `κC`, so the motive of
   `PT.rec` would depend on `F`. I take the inner pair as two extra
   arguments. I do not spend the truncation.
2. **`oa` along `sucʟ-fst`.** The brief writes `κC (sucʟ γ) (suc-ord oγ)`.
   `suc-ord oγ` has type `IsOrd (sucV (fst γ))`. The selection wants
   `IsOrd (fst (sucʟ γ))`. One `subst IsOrd (sym (sucʟ-fst γ))`
   (`Probe464.agda:67-68`).
3. **`κC` is local in `W3` and depends on `F`.** It is not 446's
   `κC`, which is selected at the InclGraph bound of `a` and does
   not mention `F`.

This GO says: given a chosen shift code, the coded least cardinal
selected at that code's stage is a member of `sucʟ γ`. It does not
say that 446's `κC` is a member of `sucʟ γ`. It does not spend
460's truncation. C-42: a measurement of this site does not
measure Residue, and it does not measure the 446 bound.

## 1. W2 (DD4)

The mathematics is written once at a generic infinite L-ordinal `γ`
that holds every numeral. `W3` is that generic carrier
(`Probe464.agda:59-62`). Both trophies that need membership of a
coded least cardinal at a successor can share this code. The
carrier is one L-element, not a named cardinal. No deadline asked
for a fixed form.

## 2. W3: `fits`

**GO, with named packing.** Typechecked ALONE, with the obligation
omitted. Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One
Agda process. The probe interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-464/Probe464.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 2.66 | 593772544 |
| `runs/w3-2.out` / `w3-2.time` | 3.09 | 593018880 |
| `runs/w3-3.out` / `w3-3.time` | 2.87 | 593674240 |

Median wall **2.87 s**. Median peak RSS **593674240 bytes**. No heap
event.

Without packing, `fits = shift-coded` does not typecheck. The
delivered type is `∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁`. The
predicate at `d` is
`∥ Σ[ G ∈ Mem (Lset γb) ] InjCode (upγ G) a (upα d) ∥₁`. Those
are not the same type.

The named packing that closes W3, at `d` the index of `γ`
(`Probe464.agda:118-122`):

- `F` as `Mem (Lset (sucV (stage F)))` by `stage-mem` and
  `Lset-mono` (`Probe464.agda:87-92`). This is 438's device
  (`Probe438.agda:81-93`) applied to the hypothesis, not to
  InclGraph.
- `d` by `fiber` after transitivity into `sucV (sucV (fst γ))` and
  `sucʟ-fst` (`Probe464.agda:111-119`).
- range by `code-target-swap` along `sym d-eq`
  (`Probe464.agda:126-133`). Rebuilt from `Probe438.agda:108-112`.
- first argument by `Σ≡Prop` on `isL` (`Probe464.agda:136-140`).

The two meet after those four devices. They do not meet at 446's
InclGraph bound. I did not inhabit `fits` there. That mismatch is
the finding the brief named, and it is why `κC` in this file is
not 446's `κC`.

## 3. The obligation

After W3 was green I added the sealed `w`, `w-lt`, `nonempty`,
`selected`, `κC`, and `residue-at-successor` (`Probe464.agda:148-204`).
I did not import `LJ-1-460.Probe460`, `LJ-1-446.Probe446` or
`LJ-1-438.Probe438`. I did not rebuild the carve. Nonempty is
`∣ d , fits ∣₁`. Minimality plus trichotomy of `w` gives
`selected ≤ d`, hence `fst κC ∈ sucʟ γ`.

Three forced rechecks of the full file, probe interface deleted,
dependencies warm, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 3.39 | 742801408 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 3.04 | 742768640 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 3.11 | 742785024 |

Median wall **3.11 s**. Median peak RSS **742785024 bytes**. First
check after the obligation landed: 4.05 s, RSS 742752256
(`runs/full-1.out` / `full-1.time`), exit 0. No heap event.

W3's median was 2.87 s and 593674240 bytes. The obligation added
0.24 s and 149110784 bytes of peak RSS. It did not approach the 8 g
caliber.

P-l did not fire as a cost: `w` is sealed, and the types name
`⟪ sucV (fst a) ⟫`. D-26 does not fire: the well-order is the
delivered `ordSWO` on members of an ordinal successor.

What the shape resisted: the 446 bound. An abstract `F : S` does
not inhabit `Lset` of `bound2 (SiteBound.β a) (sucV (stage G))`
for `G` the inclusion graph of `a`. I did not copy
`Probe446.agda:117-136`. I instantiated 430's generic bound at
`sucV (stage F)`. That is a named change of the bound, not a
change of the predicate shape.

What was weakened: the telescope carries `F` and `code`, the inner
of 460, untruncated. The brief's telescope does not. The
truncation is not spent. Nothing was left a hole. No postulate.

The brief's size guess was about 130 lines, of which the obligation
was about 25. The probe is 204 lines. The obligation at the
top-level name is 6 lines (`Probe464.agda:199-204`). The body in
`W3` is 20 lines (`:175-194`). Comparables of shape do not fund a
count.

## WHAT IS LEFT OF RESIDUE

`Residue` at `agents/tasks/LJ-1-447/Probe447.agda:208-210`,
restated at `agents/tasks/LJ-1-456/Probe456.agda:96-99`:

    Residue =
        (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
      → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
      → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

This term covers SUCCESSORS of infinite L-ordinals that hold every
numeral, for the coded selection at the stage of a chosen shift
code. It does not cover 446's `κC`. It does not claim `Residue`.
One class is not the band. C-42 rules that in both directions.

What remains, as a type, the LIMIT ordinals `y` with `κL(y) ∈ y`:

    Residue-at-limit :
        (y : V ℓ) (oy : IsOrd y)
      → ⟨ ω ∈ˢ y ⟩
      → ((γ : V ℓ) → (y ≡ sucV γ) → Empty.⊥)
      → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
      → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

The shift route does not reach them. `ShiftGraph` is parameterized
by `γ` and codes `sucʟ γ ↪ γ`
(`src/L/Absorption.lagda.md:538-540` and `:614-617`). A limit
ordinal is not a successor. I did not postulate. I did not add a
hypothesis to close the limit case.

A second remainder, at the SUCCESSORS, because this `κC` is not
446's. The truncated 460 code against 446's InclGraph bound:

    residue-at-successor-446 :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
        (shift-coded : ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁)
      → ⟨ fst (κC₄₄₆ (sucʟ γ) oa) ∈ˢ fst (sucʟ γ) ⟩

where `κC₄₄₆` is the selection at `Probe446.agda:117-196` and `oa`
is `subst IsOrd (sym (sucʟ-fst γ)) (suc-ord oγ)`. W3 measured that
the delivered code does not inhabit that predicate without a lemma
that places `F` in that `Lset`. That lemma is not in 460's type.

What the next brief needs: either a lemma that a shift code lives
in 446's bound (so the truncation spends against an F-independent
`κC`), or a ruling that the F-stage selection is the coded least
cardinal Residue may use, or the limit case by a different code.
This term is not that lemma, not that ruling, and not the limit
case.

## 4. W4

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
  sits in `agents/tasks/LJ-1-464/`.
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
  `dev/literature/truncation-and-selection.md:143` quotes:
  `the reason: "a proposition-valued goal absorbs the truncation"`
  `fits` is an hProp, so `∣_∣₁` spends nothing extra. The
  membership conclusion is an hProp, so trichotomy lands in it.
  Also `dev/literature/truncation-and-selection.md:146` quotes:
  `**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf``
  `CodedInjP'` is hProp-valued, so the index `κC` comes out. 460's
  `F` is data, not a proposition, so `PT.rec` cannot spend
  `shift-coded` into an F-dependent `κC`.
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
