# LJ-1.469 report: land the shift code in L.Absorption

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. Agda ran under the caliber the program
set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a
time. I did not set `GHCRTS`. No heap event.

TARGET: land ONE term in `src/L/Absorption.lagda.md`, after
`ShiftGraph`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

This worktree had no `.venv`. I pointed `.venv` at the parent venv.
I added no dependency.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:37`). This task is still LJ-1 work.
It does not start that collection. It does not start phase 3. No
Boundary clause is in conflict.

## PREDECESSOR VERDICT, BEFORE ANY AGDA

`[LJ-1.460]` `agents/tasks/LJ-1-460/lj-1.460-report.md:110` reads
`**GO.** The obligation typechecks`. Delivered type
`agents/tasks/LJ-1-460/Probe460.agda:73-76`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

The report does not name the statement FALSE. I take that type and
that verdict. I do not stop.

## D-10, BEFORE ANY AGDA

`[LJ-1.460]`'s delivered term in full, `Probe460.agda:73-88`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁
    shift-coded γ oγ γ∉ω numerals = ∣ SG.G , code ∣₁
      where
      module SG = ShiftGraph γ oγ γ∉ω numerals

      codeD : InjCode SG.G SG.D γ
      codeD = SG.sv , SG.dm , SG.ij , SG.ran

      D≡suc : SG.D ≡ sucʟ γ
      D≡suc = Σ≡Prop (λ x → snd (isL x)) (sym (sucʟ-fst γ))

      code : InjCode SG.G (sucʟ γ) γ
      code = subst (λ a → InjCode SG.G a γ) D≡suc codeD

`ShiftGraph`'s four exported conjuncts, opened publicly at
`src/L/Absorption.lagda.md:605-606`
(`open Carve D C γ ωʟ ∅ʟ sh shInj shNum shTop shOther D-in-dec SB.bnd bel`
`hasSeparationL public`):

1. `sv` at `:453`: `sv : ⟨ γ2 ⊨ svAt zero ⟩`
2. `dm` at `:481`: `dm : ⟨ γ2 ⊨ domAt zero (suc zero) ⟩`
3. `ij` at `:467`: `ij : ⟨ γ2 ⊨ injAt zero ⟩`
4. `ran` at `:495`: `ran : (x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst C ⟩`

`C` is `γ` (`:548`). `InjCode` at
`src/L/Cardinal.lagda.md:223-228` is those four conjuncts. `G`, `D`,
`sucʟ`, `sucʟ-fst` and `isL` are already in this chapter. `L.Cardinal`
is already imported (`:37`). `Σ≡Prop` is cubical packing, not a
missing supplier.

The term needs nothing this chapter does not already have. I do not
stop.

## VERDICT

**GO.** The obligation typechecks
(`src/L/Absorption.lagda.md:611-626`, exit 0, median 5.34 s on three
forced rechecks) and it PASSes the program's witness meter
(`.venv/bin/python scripts/pod/witness.py --code LJ-1-469 --brief
agents/tasks/LJ-1-469/LJ-1.469.md`, exit 0, 1.58 s, 0 UNRESOLVED of 1,
`probe_red=False`). I did not write `review-of-shift-coded.md`. The
GO branch forbids that file.

The exact type inhabited, so the next brief can quote it without
opening a probe, is at `src/L/Absorption.lagda.md:611-614`:

    shift-coded :
        (γ : S) (oγ : IsOrd (fst γ)) (γ∉ω : ⟨ fst γ ∈ fst ωʟ ⟩ → Empty.⊥)
        (numerals : (k : ℕ) → ⟨ # k ∈ fst γ ⟩)
      → ∥ Σ[ F ∈ S ] InjCode F (sucʟ γ) γ ∥₁

The four conjuncts come out as `SG.sv , SG.dm , SG.ij , SG.ran`
(`:619-620`). One `Σ≡Prop` along `sym (sucʟ-fst γ)` (`:622-623`)
moves the tuple, because `isL` is a proposition. No hole. No extra
hypothesis. No postulate. The statement is not widened. It is one
code at `sucʟ γ ↪ γ` under the numeral hypothesis. It is not
`amb-to-coded`.

`make check` was green before the landing (exit 0,
`runs/make-check-before.out`) and green after (exit 0,
`runs/make-check-after.out`, `check-closure: clean (101 masters;
closure, archive)`). I wrote no probe. W3 named the chapter itself.

## 1. W2 (DD4)

The mathematics is written once at a generic infinite L-ordinal `γ`
that holds every numeral. `ShiftGraph` is that generic carrier
(`src/L/Absorption.lagda.md:539-541`). This landing instantiates it.
It does not copy the four conjuncts. Both trophies that need a
non-identity code can share this chapter. No deadline asked for a
fixed form.

## 2. W3: the chapter as it stands today

**GO.** Typecheck of `src/L/Absorption.lagda.md` UNCHANGED, three
forced rechecks, interface deleted before every kept run
(`_build/2.8.0/agda/src/L/Absorption.agdai`). Dependencies warm
after `make check`. Caliber `-A64m -I0 -M8g`, set on the pane,
untouched. One Agda process. Each printed `Checking`. Exit 0 every
time. No heap event.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/baseline-1.out` / `baseline-1.time` | 5.32 | 638435328 |
| `runs/baseline-2.out` / `baseline-2.time` | 5.16 | 638451712 |
| `runs/baseline-3.out` / `baseline-3.time` | 5.13 | 638451712 |

Median wall **5.16 s**. Median peak RSS **638451712 bytes**. In-fence
count at HEAD: **526** (`ledger.py count`, `at_head=True`).

This is the parameterized band. It is not the instantiation wall.
The brief refused to guess this number. The measurement is 5.16 s.

## 3. The obligation

After W3 I widened `L.Cardinal` at `:37` to carry `InjCode`. I added
`open import Cubical.Data.Sigma using ( Σ≡Prop )` at `:46`. I put
`shift-coded` after `ShiftGraph` closes (`:605-606`) and before
PART 5. I did not move `ShiftGraph`. I did not touch `Carve`. I did
not import a probe.

The body is the 460 body, character for character at the packing:
`∣ SG.G , code ∣₁` with `SG.sv , SG.dm , SG.ij , SG.ran` and one
`Σ≡Prop` along `sucʟ-fst`.

Three forced rechecks of the chapter with the term, interface
deleted, dependencies warm, exit 0 every time, each printed
`Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 5.34 | 618545152 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 5.34 | 618545152 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 5.61 | 618545152 |

Median wall **5.34 s**. Median peak RSS **618545152 bytes**. No heap
event. The first full check after the term was added was also exit 0
(`runs/full-1.out`, 5.51 s). It is not the price. The three rechecks
are the price.

Against W3's median 5.16 s the landing moved the figure by 0.18 s.
Working-tree in-fence count: **543** (`ledger.py count`,
`at_head=False`). HEAD was 526. Added: **17**. The brief guessed
about 20.

## WHAT THIS UNBLOCKS

`[LJ-1.464]` could not import a master, so it took the inner pair of
460 as extra arguments
(`agents/tasks/LJ-1-464/Probe464.agda:199-204`). GO at
`agents/tasks/LJ-1-464/lj-1.464-report.md:91`.

`[LJ-1.465]` took the same type as a module hypothesis
(`agents/tasks/LJ-1-465/Probe465.agda:63`). The brief named that
task live. The report that sits in the tree is NO-GO at
`agents/tasks/LJ-1-465/lj-1.465-report.md:117`, on the host, not on
the code.

A chapter-level term removes that rebuild. A later brief cites
`L.Absorption.shift-coded` (`src/L/Absorption.lagda.md:611`) instead
of packing `agents/tasks/LJ-1-460/Probe460.agda:73-88`.

It does not settle `Residue`. `[LJ-1.464]` covers successors that
hold every numeral. The limit case is open. `[LJ-1.465]` shows the
code does not reach 446's InclGraph host.

## 4. W4

No module was retired. Nothing moved to `archive/`.

## THE RATIO

Write scope in-fence divisor: `src/L/Absorption.lagda.md`, **543**
non-blank in-fence lines (ledger caliber, working tree). The other
write-scope paths are not `.lagda.md` masters.

Median wall after the landing: **5.34 s**.
Quotient: 5.34 / 543 = **0.009834** s per in-fence line.
Bar: **0.0123**. The quotient is under the bar.
`concurrency`: **1**. Exclusive pane. One Agda process. I did not
pad. I did not trim the chapter.

## 5. What the shape resisted, and what closed

The four conjuncts did not resist. They were already exports. The
domain resisted in 460 and resists the same way here: `D` and
`sucʟ γ` agree on `fst` and differ as `S`. One `Σ≡Prop` closed
that. Nothing was weakened. Nothing was left a hole.

What the next brief needs: this tree now has a truncated `InjCode`
for a non-identity injection, at `sucʟ γ` into `γ`, for every
infinite L-ordinal that holds every numeral, as a chapter term.
Import `L.Absorption` and use `shift-coded`. Do not rebuild the
probe. `Residue` at a limit is still open. 446's host is still the
obstruction recorded by `[LJ-1.465]`.

## Working tree

- `src/L/Absorption.lagda.md` (`shift-coded` at `:611-626`; `InjCode`
  on the `L.Cardinal` import at `:37`; `Σ≡Prop` at `:46`)
- `dev/ledger.toml` (`gch_wing` comment at `:3252`, 526 to 543)
- `agents/tasks/LJ-1-469/lj-1.469-report.md`
- `agents/tasks/LJ-1-469/runs/`

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read. `:3` reads
  `Status: ARCHIVED RECORD. It is never rewritten.`. Declined: the
  retired dispatch table. This task's code is not a row I needed.
- `archive/dev/JOURNAL-archived.md`: read. `:1` reads
  `# Archived journal: the retired route`. Declined: a dated record
  of the retired route, not the shift code.
- `archive/dev/JOURNAL.md`: read. `:1` reads
  `# ARCHIVED 2026-08-20`. Declined: per-episode journal, retired.
  The product of this task sits in `agents/tasks/LJ-1-469/`.
- `dev/ARCHIVE.md`: read. `:1` reads
  `# ARCHIVE.md: the archive registry`. Declined: no module was
  retired, so no row is written.
- `archive/dev/DD-archived.md`: read. `:3` reads
  `Status: ARCHIVED RECORD. Never rewritten, never deleted.`. Declined:
  archived DD series, not the shift code.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read. `:1` reads
  `# Devlin II.5: the Condensation Lemma and the GCH in L`.
  Declined: condensation and GCH, not the shift code.
- `dev/literature/truncation-and-selection.md`: read. `:1` reads
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined: W3 was the chapter's check time. The packing does not
  spend a truncation with `PT.rec`.
- `dev/literature/terms-2026-08.md`: read. `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined: a glossary dossier, not this code.
- `dev/literature/digest.md`: read. `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined: the rud-route digest, not the shift code.
- `dev/literature/glossary-review-2026-08.md`: read. `:1` reads
  `# Glossary review: the 119 pre-protocol entries`.
  Declined: glossary review, not this code.
