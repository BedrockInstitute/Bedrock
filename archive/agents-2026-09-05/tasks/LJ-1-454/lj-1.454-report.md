# LJ-1.454 report: the injection this tree DEFINES, and whether it carries a code

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-454/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term `rank-graph` in
`agents/tasks/LJ-1-454/Probe454.agda`. Land nothing in `src/`.

## THREE PREDECESSORS, READ BEFORE ANY AGDA

The slot clause and the brief both require the REPORT, not the brief, of
each predecessor. All three verdicts are GO. None names the statement
FALSE. I did not stop here.

1. `[LJ-1.416]` verdict, `agents/tasks/LJ-1-416/lj-1.416-report.md:15`:
   "**GO.** The obligation typechecks. The witness meter PASSes."
   Delivered type, `agents/tasks/LJ-1-416/Probe416.agda:105-106`:
   `swo-rank : {A : Type ℓ} (w : SWO A) → A → S`
   with `swo-rank-ord` at `:108` and `swo-rank-mono` at `:111-114`.
   Built by Acc recursion (`Probe416.agda:67-75`). Not hypothesized.

2. `[LJ-1.417]` verdict, `agents/tasks/LJ-1-417/lj-1.417-report.md:19`:
   "**GO.** The obligation typechecks (`agents/tasks/LJ-1-417/Probe417.agda`,"
   Delivered type, `agents/tasks/LJ-1-417/Probe417.agda:80`:
   `swo-into-ord : Σ[ β ∈ S ] (IsOrd β × (A ↪ ⟪ β ⟫))`
   The report says the rank is enough (`lj-1.417-report.md:23`).
   No `∥ ∥₁` in that type.

3. `[LJ-1.418]` verdict, `agents/tasks/LJ-1-418/lj-1.418-report.md:19`:
   "**GO.** The obligation typechecks (`agents/tasks/LJ-1-418/Probe418.agda`,"
   Delivered type, `agents/tasks/LJ-1-418/Probe418.agda:64-66`:
   `stage-into-bound : (α : S) → IsOrd α → Σ[ β ∈ S ] (IsOrd β × (⟪ Lset α ⟫ ↪ ⟪ β ⟫))`
   No pairing, no `Init`, no band, no infiniteness in the telescope.

## WHY THIS IS NOT THE STATEMENT THAT FAILED THREE TIMES

`amb-to-coded` asks for the graph of an ARBITRARY injection. Its type is
`agents/tasks/LJ-1-414/Probe414.agda:134-138`:

```
amb-to-coded :
    (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
  → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
  → ∥ Σ[ F ∈ S ] InjCode F x d ∥₁
```

The injection in that telescope is an element of `_↪_`. `[LJ-1.414]`,
`[LJ-1.426]` and `[LJ-1.441]` each asked for the graph of an injection
that `leastOf` selected. `leastOf` is at `src/L/Cardinal.lagda.md:117`.
Its output carries no defining formula.

This task asks for the graph of ONE named function. The function is
`swo-rank` at `agents/tasks/LJ-1-416/Probe416.agda:105-106`. It is
defined by well-founded recursion (`Probe416.agda:67-75`). C-42
(`dev/LESSONS.md:3752`) says a refutation of the first site says
nothing about the second. The three `amb-to-coded` NO-GOs do not
decide this obligation.

## WHAT `[LJ-1.419]` REFUTED, AND WHY IT IS NOT THIS

`[LJ-1.419]` is NO-GO (`agents/tasks/LJ-1-419/lj-1.419-report.md:15`):
the rank route does not replace the pairing parameter in the
stage-cardinal consumer, and `bound-into-ord` as that brief stated it
is FALSE at that generality. This task makes no claim about the
pairing and does not touch that consumer. It asks only whether the
rank map has a graph.

## VERDICT

**STOP.** W3 typechecks the type `Formula S 2`. Internal delivers the
ORDER and does not deliver the RANK. I omitted `rank-graph`. The
obstruction is `review-of-rank-graph.md`.

`src/L/Choice/Internal.lagda.md` does neither: it does not deliver
`rank-formula`, and it does not derive it.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that
collection. It does not start phase 3. No Boundary clause is in
conflict.

## 1. W3: `rank-formula`, first

**The type is well-formed. Internal does not inhabit it.**

Stated as `rank-formula-type : Type _` equal to `Formula S 2`
(`Probe454.agda:42-43`). Satisfaction at `(z ∷ a ∷ [])` would say `z`
is the pair of a member of `a` and that member's rank. I did not
inhabit `rank-formula : Formula S 2`. I did not postulate it. I did
not invent a body.

The checker loaded every `Formula` constructor Internal exports, as
the 9-tuple `order-formulas` (`Probe454.agda:48-72`):

| name | line | what it describes |
|---|---|---|
| `InLimitAt` | `src/L/Choice/Internal.lagda.md:166` | a code in the limit stage |
| `FreeAt` | `:304` | parameter-free codes |
| `DenoteBody` | `:587` | denotation of a name |
| `NameAt` | `:597-599` | a name at slots |
| `LexAt` | `:731` | first difference of parameters |
| `≺At` | `:741-742` | the ORDER of two names |
| `LeastNameAt` | `:910-911` | least name under that order |
| `StepBody` / `StepAt` | `:967-975` | one step of the family |

None of these is the rank. A search of
`src/L/Choice/Internal.lagda.md` for `rank` returns no match. The
chapter's own English says the order formula runs no recursion of its
own (`src/L/Choice/Internal.lagda.md:22`): "runs **no recursion of
its own**." And at `:709`: "Nothing recurses, nothing is".
`swo-rank` is Acc recursion
(`agents/tasks/LJ-1-416/Probe416.agda:67-75`). A description of the
order is not a description of that recursion.

`graphAt-value` at `src/L/Choice/Internal.lagda.md:514` is
`satGraphAt`, the satisfaction-table graph. It is not the rank graph.

**One line, as the brief asked:** Internal delivers the ORDER
(`≺At` at `:741-742`) and does not deliver the RANK.

The brief says: if it delivers only the order and not the rank, STOP.
I stopped. I did not write `rank-graph`. I did not leave a hole.

ESTIMATE for W3 was about 25 lines and under 10 seconds. MEASURED:
41 non-blank non-comment lines in the probe, of which
`rank-formula-type` is 2 lines and `order-formulas` is the inventory.
The extra lines are the 9-tuple. Comparables of shape, not of size.

Three forced rechecks, one Agda process at a time, probe interface
removed, dependencies warm, from the repository root, caliber
`-A64m -I0 -M8g`:

| run | real (s) | RSS (bytes) | file |
|---|---|---|---|
| w3-2 | 2.89 | 381976576 | `runs/w3-2.out` |
| w3-3 | 2.12 | 368934912 | `runs/w3-3.out` |
| w3-4 | 1.79 | 424902656 | `runs/w3-4.out` |

Median wall **2.12 s**. Peak RSS **424902656** bytes. Exit 0 every
time. No heap event. The first check `runs/w3-1.out` was 1.88 s and
427163648 bytes, also exit 0; it is not one of the three forced
rechecks.

The full file is the W3 file. The obligation is omitted. The same
three runs are the full-file numbers.

## WHAT THE FORMULA COSTS

Internal does not deliver `rank-formula : Formula S 2`. It does not
derive it.

What it does deliver, at `file:line`:

- `≺At : ∀ {n} → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n`
  at `src/L/Choice/Internal.lagda.md:741-742`. Eight slot indices.
  Not `Formula S 2`.
- `LexAt` at `:731`, four indices.
- `LeastNameAt` at `:910-911`, nine indices.
- `StepAt` at `:973-975`, seven indices.

Separation in this tree takes a `Formula`. `hasSeparationL` is
`(a : S) (φ : Formula S 1)` at `src/L/Axioms/Full.lagda.md:144`.
The carve in `src/L/InjChain.lagda.md:468-472` takes
`(φ : Formula S 1)` over a named bound. There is no `φ` here for
the rank.

**The missing formula is worth more than the obligation.** It is a
first-order description of the well-founded rank, as data, of a
well-order that Internal already describes. The next brief's whole
target is that formula. I did not invent its body.

## D-10

The residue "Internal already has the formula the carve consumes" is
FALSE. The inventory above is the measurement. The corrected target,
beside the original, is: first inhabit `rank-formula : Formula S 2`
(or a formula with slots for the order as a set), then carve
`rank-graph` by one separation. I did not price the carve. I did not
claim `rank-graph` is false as a set. I claimed the prescribed
formula is missing.

## 2. W2

The W3 term is generic in the formula arity `n`. It names no stage,
no cardinal, no numeral, and no `Lset`. The stop is at the generic
carrier `S`. I did not write a fixed form. W2 holds for what was
written.

## 3. W4

No module was retired. Nothing moved to `archive/`.

## 4. C-42 sweep, before any cure

This STOP measures ONE site: whether
`src/L/Choice/Internal.lagda.md` delivers `rank-formula : Formula S 2`.

Sweep of the shape "a Formula for the rank of a well-order":

- `src/L/Choice/Internal.lagda.md`: 0 hits for `rank`.
- `src/`: 0 hits for `swo-rank`. The rank as DATA lives only in
  `agents/tasks/LJ-1-416/Probe416.agda` and is consumed as a
  hypothesis by `agents/tasks/LJ-1-417/Probe417.agda`. Neither file
  is a `Formula`.
- `src/`: 0 hits for `rank-formula`.
- Count of Internal's exported `Formula` constructors that describe
  rank: **0**. Count that describe the order: **1** (`≺At`), plus
  the name and step formulas that sit around it.

The three `amb-to-coded` NO-GOs are a different shape (an arbitrary
element of `_↪_`). This sweep does not re-price them.

No cure is priced. The next action is the formula, not the graph.

## 5. What the next brief needs

- Internal describes the ORDER and does not describe the RANK.
  Quote `src/L/Choice/Internal.lagda.md:22` and `:709`. The
  distinction is the finding.
- `swo-rank` is Acc recursion at
  `agents/tasks/LJ-1-416/Probe416.agda:67-75`. It is data in the
  meta-language. Separation needs a `Formula`.
- Do not send `rank-graph` again until a brief names a `Formula`
  that Internal delivers or that a new task writes. The missing
  formula is the whole target.
- Do not reuse `[LJ-1.414]`, `[LJ-1.426]`, or `[LJ-1.441]`. Those
  sites are arbitrary `leastOf` arrows. C-42 forbids the transfer.
- Do not reuse `[LJ-1.419]`. That site is the pairing parameter.
  This task did not touch it.

What the statement cost: 41 non-blank non-comment lines, median
2.12 s, peak RSS 424902656 bytes. What the shape resisted: the
formula does not exist in Internal. What I had to weaken: nothing.
What I could not close: `rank-formula`, and therefore `rank-graph`.

## ARCHIVE USED

- `archive/dev/JOURNAL.md:3`
  "The per-episode journal is retired."
  Declined. Not used. The per-episode journal is retired. The
  history of this campaign is the task directories.
- `archive/dev/JOURNAL-archived.md:1229`
  "no ordinal arithmetic, no order-type or rank theory; the absence was"
  Read. Used. That archived journal records the absence of rank
  theory in the retired route. `[LJ-1.416]` filled the rank as
  DATA in a probe. This task asked for the rank as a `Formula`.
  The object-language half of that absence still holds in
  `src/L/Choice/Internal.lagda.md`.
- `archive/dev/LJ-dispatch-index.md:1`
  "THE `LJ` DISPATCH INDEX, archived 2026-08-18"
  Declined. Not used. It is a dispatch index. It does not bear on
  whether Internal delivers a rank formula.
- `dev/ARCHIVE.md:283`
  "A classical well-order over finite labelled trees by shortlex"
  Read. Used. The retired `L.WellOrder.Tree` is a well-order, not
  a rank formula. No retired module turns a well-order into a
  `Formula S 2` for the rank. This task does not retire a module.
- `archive/dev/DD-archived.md:1`
  "THE `DD` RULING SERIES, archived in full 2026-08-18"
  Declined. Not used. The archived D series does not bear on
  `rank-formula`.

## LITERATURE USED

- `dev/literature/devlin-II5.md:259`
  "a definable well-order of L_α, used to pick the <_L-least"
  Read. Used as contrast. Devlin uses a definable well-order to
  SELECT a least witness. This task does not select. It asks
  whether the rank of a well-order is itself a formula.
- `dev/literature/truncation-and-selection.md:67`
  "The selection device is a definable well-order plus a universal guard."
  Read. Used. The rank is not that device. Internal's order
  formula is the well-order side. The rank is a recursion on that
  order, not a least-witness guard.
- `dev/literature/digest.md:235`
  "The canonical well-order (SZ p. 11): <^A_β is defined recursively; at"
  Read. Used. SZ defines the ORDER recursively. That is the object
  Internal describes without running a recursion of its own
  (`src/L/Choice/Internal.lagda.md:22`). The digest does not
  supply a formula for the rank of that order.
- `dev/literature/terms-2026-08.md:230`
  "The ordinal a well-order collapses to: "the order type of the"
  Read. Used. That is the sense of `swo-rank` as DATA
  (`Probe416.agda:105-106`). The glossary file is a rendering
  dossier. It is not a `Formula S 2`.
- `dev/literature/fine-structure.md:1`
  "Fine structure: projecta, standard codes, the reductions, and their dependencies"
  Declined. Not used. It extracts projecta and codes. It does not
  bear on a rank formula in Internal.

## MACHINE STATE

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, from the repository
root. I did not set `GHCRTS`. No heap event. Before the first run,
another Agda process (`Witness-LJ-1-452`) was live. I waited until
it exited. Then I started one process.

- W3 first check, `runs/w3-1.out`: 1.88 s real, 427163648 bytes
  RSS, printed `Checking`, exit 0.
- Three forced rechecks after `rm` of `Probe454.agdai`:
  2.89 s, 2.12 s, 1.79 s. Median **2.12 s**. Peak RSS
  **424902656** bytes. Exit 0 every time
  (`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`).

Estimate for the Agda was about 160 lines for the whole
obligation. I did not write the obligation. W3 measured 41
non-blank non-comment lines. Nothing is funded against the
estimate.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-454/`:

- `lj-1.454-report.md`, this report
- `review-of-rank-graph.md`, the W3 obstruction
- `Probe454.agda`, W3 only, `rank-graph` omitted
- `runs/`, the Agda transcripts named above
