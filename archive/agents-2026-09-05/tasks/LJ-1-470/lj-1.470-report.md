# LJ-1.470 report: land the coded shift in a new master

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. Write scope: `src/L/CodedShift.lagda.md`,
`src/Everything.lagda.md`, `dev/ledger.toml`, `agents/tasks/LJ-1-470/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: land ONE term in a NEW master `src/L/CodedShift.lagda.md`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

and register it in `src/Everything.lagda.md` after `import L.Absorption`.
Do not edit `src/L/Absorption.lagda.md`.

## 0. D-10, before any Agda

**Predecessor report verdict**, `agents/tasks/LJ-1-460/lj-1.460-report.md:110`:

> **GO.** The obligation typechecks

The report is GO. It does not name the statement FALSE. I did not stop.

**Delivered type**, `agents/tasks/LJ-1-460/Probe460.agda:73-76`:

```agda
shift-coded :
    (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
    (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
  → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁
```

**The type this task lands is that type, character for character.** I did
not name a difference. I did not stop.

**ShiftGraph's four exported conjuncts**, packed at
`agents/tasks/LJ-1-460/Probe460.agda:81-82` as
`SG.sv , SG.dm , SG.ij , SG.ran`. The suppliers in `src/` are:

- `sv` at `src/L/Absorption.lagda.md:452`
- `dm` at `src/L/Absorption.lagda.md:480`
- `ij` at `src/L/Absorption.lagda.md:466`
- `ran` at `src/L/Absorption.lagda.md:494`

`ShiftGraph` opens `Carve` publicly at
`src/L/Absorption.lagda.md:604-605`. The domain transport is
`Σ≡Prop` along `sym (sucʟ-fst γ)` at `Probe460.agda:84-85`.

**The new master needs only imports from `src/`.** It does not import a
probe. I do not stop.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**GO.** The obligation typechecks at the delivered type
(`src/L/CodedShift.lagda.md:37-40`, exit 0, median 1.78 s on three
forced rechecks) and it PASSes the program's witness meter
(`.venv/bin/python scripts/pod/witness.py --code LJ-1-470 --brief
agents/tasks/LJ-1-470/LJ-1.470.md`, exit 0, 1.96 s, 0 UNRESOLVED of 1,
`probe_red=False`). The master has no inner hypothesis module. I did
not write `review-of-shift-coded.md`. The GO branch forbids that file.

The exact type inhabited, so the next brief can quote it without
opening the probe, is at `src/L/CodedShift.lagda.md:37-40`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

`src/L/Absorption.lagda.md` is unchanged (`git diff` on that path is
empty). The catalog insert is one line at
`src/Everything.lagda.md:377`. Conjunct 4's finding set did not move
(W3 below).

`make check` was green before the catalog import (exit 0, 24.91 s) and
green after (exit 0, 12.42 s). `check-closure: clean (102 masters;
closure, archive)` after the landing. Standing from
`scripts/measure/ledger.py --brief` is 33,467 lines over 99 masters,
measured from HEAD. HEAD does not yet hold this master.

This GO is a truncated code for the shift at a generic infinite
L-ordinal that holds every numeral. It is not a code for a `leastOf`
selection. I did not claim `amb-to-coded`.

## W3: conjunct 4 at the catalog

**GO.** The widest unmeasured term was the finding set of
`scripts/measure/check-unbound-hyp.py --check`, before any `src/` edit
and after the catalog insert. Caliber does not apply: the checker is
not Agda. Two runs, each under 1 s.

**BEFORE**, `runs/unbound-before.out`, exit 1 (findings exist, as they
did on 2026-08-17):

```
src/L/Absorption.lagda.md:398
src/L/Absorption.lagda.md:400
src/L/InjChain.lagda.md:471
src/L/Reflect.lagda.md:365
src/L/StageCardinal.lagda.md:281
```

**AFTER**, `runs/unbound-after.out`, exit 1, the same five strings at
the same lines. Set difference is empty.

`src/Everything.lagda.md` carries no finding. The insert at `:377`
moved `import L.GCH` from `:377` to `:378` and
`import L.SquareLawClosed` from `:387` to `:388`. No finding lived on
those lines. The `[LJ-1.469]` trap (Absorption `:398`/`:400` shifting
to `:399`/`:401`) did not fire here, because Absorption was not
edited.

The new master, scanned by path because it is still untracked,
`runs/unbound-codedshift.out`: `check-unbound-hyp: clean (1 file(s))`,
exit 0. It adds no finding of its own.

`src/Everything.lagda.md` is a master. It is not a master with
findings below the insert point. Conjunct 4 held.

## THE RATIO

Write-scope in-fence non-blank lines of the new master: **39**
(`src/L/CodedShift.lagda.md`, ledger caliber: non-blank lines inside
` ```agda ` fences). `src/Everything.lagda.md` is in `ledger.UNCOUNTED`
and does not enter the divisor. The estimate was about 45.

Median wall of the three forced rechecks: **1.78 s**.

Seconds per in-fence line: **1.78 / 39 = 0.0456**. The live bar is
0.0123. The return is over the bar. I did not pad the master.

`concurrency` = 1. This pane is `machine: exclusive`. `pgrep` found no
Agda compiler before each timed run. I started one Agda process at a
time.

The probe measured a median of 1.73 s
(`agents/tasks/LJ-1-460/lj-1.460-report.md:111`). The master measured
1.78 s. The difference is 0.05 s.

`[LJ-1.469]` measured 5.34 s over 543 in-fence lines inside
`L.Absorption`. This master does not recheck Absorption. Dependencies
were warm. The smaller divisor is what moved the rate over the bar,
not a slower check.

## 1. W2 (DD4)

The mathematics is written once at a generic infinite L-ordinal `γ`
that holds every numeral. `ShiftGraph` is that generic carrier
(`src/L/Absorption.lagda.md:538-540`). This master instantiates it and
packs the four exports. It does not copy the four conjuncts. Both
trophies that need a non-identity code can import `L.CodedShift`. No
deadline asked for a fixed form.

## 2. What was built

New master `src/L/CodedShift.lagda.md`, module
`L.CodedShift {ℓ} (lem)` (`:10`). No inner hypothesis module. No
import under `agents/`. 39 non-blank in-fence lines.

`shift-coded` (`:37-52`) is the body at `Probe460.agda:73-88`, with
the probe's W3 block omitted. The four conjuncts come out as
`SG.sv , SG.dm , SG.ij , SG.ran` (`:46`). One `Σ≡Prop` along
`sym (sucʟ-fst γ)` (`:49`) moves the tuple. No hole. No extra
hypothesis. No postulate.

Registered in `src/Everything.lagda.md:377`, after `import L.Absorption`
(`:376`) and before `import L.SquareLawClosed` (`:388`).

Declared on the GCH wing in `dev/ledger.toml` after
`src/L/Absorption.lagda.md`, so a later commit of this master does not
join the AC baseline by subtraction.

The shape did not resist. The domain `D` and `sucʟ γ` still agree on
`fst` and differ as `S`. The same `Σ≡Prop` closed that. Nothing was
weakened.

## 3. The landed obligation

First check after the master landed: 1.80 s, peak RSS 406847488
bytes, exit 0, printed `Checking`. `runs/full-1.out`.

Full file, three forced rechecks, interface deleted
(`_build/2.8.0/agda/src/L/CodedShift.agdai`), dependencies warm, same
caliber, one Agda process:

| run | wall s | peak RSS bytes | log |
|---|---|---|---|
| 1 | 1.78 | 406863872 | `runs/full-recheck-1.out` / `full-recheck-1.time` |
| 2 | 1.79 | 406814720 | `runs/full-recheck-2.out` / `full-recheck-2.time` |
| 3 | 1.76 | 406798336 | `runs/full-recheck-3.out` / `full-recheck-3.time` |

Median wall **1.78 s**. Median peak RSS **406814720 bytes**. Exit 0
every time. Each printed `Checking`. No heap event.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## 5. What the next brief needs

This tree now has a truncated `InjCode` for a non-identity injection,
at `sucʟ γ` into `γ`, for every infinite L-ordinal that holds every
numeral, in a chapter: `src/L/CodedShift.lagda.md:37-40`. Later briefs
can import `L.CodedShift` and must not rebuild the term from a probe.

The catalog insert did not trip conjunct 4. A landing that does not
edit a master that already carries findings can pass that comparison.
The ratio over 39 in-fence lines is 0.0456, above 0.0123. That is the
price of a small new master whose check is still the warm
`ShiftGraph` cone. Padding the master would move the quotient and
would not change the work.

`Residue` at `y := fst (sucʟ γ)` is still open. This term does not
close it. `[LJ-1.464]` already spends the inner pair of this code and
is GO.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read. `:3` reads
  `Status: ARCHIVED RECORD. It is never rewritten.`. Declined: the
  retired dispatch table. This task's code is not a row I needed.
- `archive/dev/JOURNAL-archived.md`: read. `:1` reads
  `# Archived journal: the retired route`. Declined: a dated record
  of the retired route, not the shift code.
- `archive/dev/JOURNAL.md`: read. `:1` reads
  `# ARCHIVED 2026-08-20`. Declined: per-episode journal, retired.
  The product of this task sits in `agents/tasks/LJ-1-470/`.
- `dev/ARCHIVE.md`: read. `:1` reads
  `# ARCHIVE.md: the archive registry`. Declined: no module was
  retired, so no row is written.
- `archive/dev/DD-archived.md`: read. `:3` reads
  `Status: ARCHIVED RECORD. Never rewritten, never deleted.`. Declined:
  archived DD series, not the coded shift.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read. `:1` reads
  `# Devlin II.5: the Condensation Lemma and the GCH in L`.
  Declined: condensation and GCH, not the shift code.
- `dev/literature/truncation-and-selection.md`: read. `:143` reads
  `the reason: "a proposition-valued goal absorbs the truncation"`.
  Declined: this landing does not spend a truncation in a new proof
  step. The four conjuncts are already exports.
- `dev/literature/terms-2026-08.md`: read. `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined: a glossary dossier, not this code.
- `dev/literature/digest.md`: read. `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined: the rud-route digest, not the shift code.
- `dev/literature/glossary-review-2026-08.md`: read. `:1` reads
  `# Glossary review: the 119 pre-protocol entries`.
  Declined: glossary review, not this code.
