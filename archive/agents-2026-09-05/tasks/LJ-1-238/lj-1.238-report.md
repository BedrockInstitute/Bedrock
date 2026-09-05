# LJ-1.238 report: `L.Coding.Sequence` ports, residual zero

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. One Agda slot held.
No master edited. No commit, no push. Written incrementally (C-22). Every
negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**IT PORTS.**

The class-generic port of `L.Coding.Sequence` typechecks.
`agents/tasks/LJ-1-238/GenSequence.agda`, exit 0.

**40 written lines against the module's 157.** 145 lines survive verbatim,
12 removed. MEASURED by an indent-insensitive line diff against the fence
extract.

**The three DD4 numbers: shared body 145, plumbing 40, per-tower residual 0.**
Sequence's residual is zero. The six readings are tower-neutral.

**The supplier that leaks is the `DefAt` trio.** `DefAt`, `DefAt-in`,
`DefAt-out` come from `L.Coding.Powerset` (`Sequence.lagda.md:52`). `GenModel`
does not supply them. `GenGraph` does not supply them. MEASURED. At the ambient
class the ambient body supplies them: `LJ-1-224.ProbeGraphSupply.Body` defines
`DefAt` at `:373`, `DefAt-in` at `:531`, `DefAt-out` at `:548`, exit 0.

The load sat at 5.19 / 4.70 / 4.68. Kept runs: 0.886 s, 0.874 s, 0.881 s.

## 1. MACHINE AND PROCESS DISCIPLINE

ONE Agda process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised. Warm-up
discarded. Three kept runs. No run passed 20 minutes. No heap exhaustion.

| run | file | exit | seconds | load |
|---|---|---:|---:|---|
| warm-up | `GenSequence.agda` | 0 | 1.60 | 5.19 / 4.70 / 4.68 |
| kept 1 | `GenSequence.agda` | 0 | **0.886** | 5.19 / 4.70 / 4.68 |
| kept 2 | `GenSequence.agda` | 0 | **0.874** | 5.19 / 4.70 / 4.68 |
| kept 3 | `GenSequence.agda` | 0 | **0.881** | 5.19 / 4.70 / 4.68 |

The machine is not quiet. Five foreign agda processes ran during the checks.
The seconds decide nothing. The exit code and the line counts decide.

## 2. ARTIFACTS

| file | what it is |
|---|---|
| `GenSequence.agda` | the class-generic port of `L.Coding.Sequence`. Exit 0 |
| `_SeqBodyRaw.agda` | the fence extract of the delivered module, 157 non-blank |
| `_SeqBody.agda` | the body with the two substitutions applied, unindented |
| `_SeqBodyIndent.agda` | the same body, indented under `module Body` |
| `_Header.agda` | the port header: telescope, imports, carrier, params |
| `lj-1.238-report.md` | this report |

## 3. THE PORT, COUNTED

The delivered module is 157 non-blank in-fence lines. MEASURED by
`extract.py`. The port is 185 non-blank lines. An indent-insensitive diff
reports:

| figure | non-blank lines |
|---|---:|
| written (added) | **40** |
| removed | 12 |
| verbatim (unchanged) | **145** |

The 40 written lines split in two: 38 header lines and 2 body substitutions.
The header lines are the pre-module imports, the flat class telescope, the
GenModel application, and the `DefAt` parameterization block.

The 2 substitutions are the whole mathematical content of the port. Both are
class-parameter swaps:

- `Sequence.lagda.md:105` `PowOK ... ⟨ isL (𝒟ₒ (fst w)) ⟩` becomes
  `⟨ M (𝒟ₒ (fst w)) ⟩`.
- `Sequence.lagda.md:181-182` `isL-trans {x = 𝒟ₒ (fst w)} {y = x}`
  becomes `M-trans {x = 𝒟ₒ (fst w)} {y = x}`.

The eta-expansion `(λ {x} {y} → M-trans {x} {y})` is used once, at
`GenSequence.agda:45`. It is the plumbing cure `[LJ-1.210]` measured.

One mechanical artifact is real and reported: the body is indented two spaces,
because the `DefAt` trio must sit in a nested `module Body` after the carrier
opens. The delivered module imports them; the port parameterizes them, and a
parameter cannot name `S` before the carrier exists. This re-indent is not a
content change.

## 4. THE SUPPLIER, CHECKED BEFORE PARAMETERIZING

Sequence imports `DefAt`, `DefAt-in`, `DefAt-out` from `L.Coding.Powerset`
at `Sequence.lagda.md:52`.

`GenModel` supplies the Model names and nothing else. It exports `extAt`,
`appAt`, `domAt`, `prAtL`, and their readers (`GenModel.agda:88-105`,
`:165-191`, `:392-408`). It does not define `DefAt`. MEASURED by reading.

`GenGraph` supplies the Graph trio and `GraphWitAt`
(`GenGraph.agda:107-131`). It does not define `DefAt`. MEASURED by reading.

So the `DefAt` trio leaks from Powerset. The class-generic Powerset does not
supply it either: `agents/tasks/LJ-1-213/GenPowerset.agda` exits 42 at `:63`.
MEASURED in `[LJ-1.213]`.

At the AMBIENT class the trio is supplied. The ambient body
`agents/tasks/LJ-1-224/ProbeGraphSupply.agda` defines `DefAt` at `:373-374`,
`DefOK` at `:376-377`, `DefAt-in` at `:531`, `DefAt-out` at `:548`, inside
`module Body`, and the file exits 0 (`[LJ-1.224]`, run 2). The three
signatures match the port's three parameters exactly, read side by side: the
delivered Powerset's `DefAt-in` and `DefAt-out` sit in `module _ (A : S) where`
(`Powerset.lagda.md:473`), so `A` is an explicit first argument, and the port
keeps that shape verbatim.

The six readings therefore exist at the ambient class by one module
application: `GenSequence.Body (AmbientBody.DefAt) (AmbientBody.DefAt-in)
(AmbientBody.DefAt-out)`. No new proof content. INFERRED from the matching
signatures; the application itself was not typechecked because the ambient
body's `Body` is parameterized over 19 supplier names that are the next link,
not this link.

## 5. THE RESIDUAL IS ZERO

The six readings are tower-neutral. `StepAt-out`, `StepAt-back`,
`ApproxAt-dom`, `ApproxAt-value`, `ApproxAt-step`, `Graph-out` name `M`,
`M-trans`, `DefAt`, and the shared operators `appAt`, `domAt`, `extAt`,
`prAtL`. None names `isL`, `isJ`, or a stage. MEASURED by reading the body.

So Sequence's per-tower residual is **zero**, and `[LJ-1.223]`'s zero extends
one module higher. The per-tower content of the coding chain stays where
`[LJ-1.213]` found it: `DefAt-stage`, 8 lines in `Powerset.lagda.md:720-727`,
which spends `LsetS` and `𝒟ₒ→isL`. Sequence has no such block.

`[LJ-1.225]` read the six readings as Devlin's C2 row, the "bounded Def-step
matrix", marked PER-TOWER. That reading is REFUTED on the measured axis. The
six readings are the matrix's "coding analogue" (`devlin-II5.md:375`), and the
port shows that analogue is carrier-generic. The C2 row's PER-TOWER mark
belongs to the "bound inside carrier" half, which is `DefAt-stage`, one module
below Sequence. MEASURED for the residual; the assignment of Devlin's mark is
a reading, stated as such.

One caution, in Devlin's own words. The C2 row's Def column reads
"satisfaction bound K(u) or its coding analogue; J: the sixteen op-graphs,
syntax-free". The two towers in DD4 are L and J, and the class-generic port
measures L against the ambient class `Full`, not against J. A residual of zero
against `Full` does not say the six readings transfer to J unchanged; the J
tower's analogue is op-graphs, not satisfaction coding. That axis is not this
link. INFERRED, and no `src/J/` exists.

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| Sequence will not port | **MEASURED FALSE.** `GenSequence.agda` exit 0 |
| the port is small and mechanical (the brief's inferred phrase) | **MEASURED TRUE.** 40 written, 2 of them mathematical |
| Sequence's residual is nonzero | **MEASURED FALSE.** zero per-tower lines |
| `GenModel` supplies the `DefAt` trio | **MEASURED FALSE.** it exports Model names only |
| `GenGraph` supplies the `DefAt` trio | **MEASURED FALSE.** it exports Graph names only |
| the six readings are Devlin's per-tower content | **MEASURED FALSE on the L-vs-ambient axis.** they are carrier-generic |
| the `DefAt` trio is unsupplied at the ambient class | **MEASURED FALSE.** `ProbeGraphSupply.Body` supplies it, exit 0 |
| the class-generic Powerset supplies the trio | **MEASURED FALSE.** `GenPowerset.agda` exits 42 |

## 7. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-225/lj-1.225-report.md`, read WHOLE, first. TOOK the six
  readings at `:217`, `:221`, `:295`, `:298`, `:303`, `:325`, and the claim
  that the port stops one module short. Section 5 refutes its C2 reading.
- `agents/tasks/LJ-1-210/lj-1.210-report.md`, read WHOLE. TOOK the flat
  telescope shape, the 42/1,272 split, and the eta-expansion cure.
- `agents/tasks/LJ-1-210/GenModel.agda`, read for its export list. TOOK
  `extAt`, `appAt`, `domAt`, `prAtL` and their readers at `:88-105`,
  `:165-191`, `:392-408`.
- `agents/tasks/LJ-1-210/GenGraph.agda`, read WHOLE. TOOK the Graph trio at
  `:107-131` and confirmed it does not supply `DefAt`.
- `agents/tasks/LJ-1-224/lj-1.224-report.md`, read WHOLE. TOOK the SUPPLYABLE
  finding and the 19-parameter width.
- `agents/tasks/LJ-1-224/ProbeGraphSupply.agda`, read WHOLE. TOOK the ambient
  supply of `DefAt` `:373`, `DefAt-in` `:531`, `DefAt-out` `:548`.
- `agents/tasks/LJ-1-213/lj-1.213-report.md`, read WHOLE. TOOK the 7
  substitutions, `DefAt-stage` 8 lines, and the 389/12/8 split.
- `agents/tasks/LJ-1-223/lj-1.223-report.md`, read WHOLE. TOOK the ten
  suppliers and the 2,971 / about 200 / 0 split.
- `src/L/Coding/Sequence.lagda.md`, read WHOLE, never a report about it. This
  is the object.
- `src/L/Coding/Powerset.lagda.md`, read at `:442-446`, `:473`, `:645-688`.
  TOOK the `DefAt-in` and `DefAt-out` signatures and `DefOK`.
- `archive/dev/TASKS-archived.md`, read for shape. TOOK `L3.32-T126`
  (StepStory carrier-generic, instantiated unchanged) and `L3.32-T239`
  (limit clause carrier-generic, +26 at the first site). SHAPE TAKEN, no
  figure. **What would NOT transfer:** every line figure, because the archived
  `L.Rud.*` and `L.Coding.*` modules are the retired tree, and the archived
  `Sequence.lagda.md:41-61` pins `𝒮ʟ` exactly as the delivered one does — the
  archive never ported it either.

## 8. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md:370-383`, read WHOLE. The table has twelve rows:
eight EITHER (A, B, C3, C4, C5, C6, E, F) and four PER-TOWER (C1, C2, D, G).
The word "nine" does not occur in the file. The brief's figure "eight and
four" is correct. MEASURED by reading.

The six readings fall on **C2**, the "bounded Def-step matrix", column Def:
"satisfaction bound K(u) or its coding analogue". The port measures the coding
analogue as carrier-generic, so C2's PER-TOWER mark is not carried by the six
readings. It is carried by the "bound inside carrier" half, which is
`DefAt-stage` in the Agda tree. Section 5.

## 9. RULES ANSWERED

- D-1. The abort criterion was fixed by the brief. The branch that fired is
  IT PORTS. I report the three figures and stop.
- P-l. `[LJ-1.210]`'s 42 lines and `[LJ-1.223]`'s chain rate are comparables,
  not my price. My 40 written is measured at this site.
- C-38 as extended. `DefAt`, `DefAt-in`, `DefAt-out` are checked against
  `GenModel` and `GenGraph` before parameterizing. Neither supplies them. The
  ambient body does.
- C-36. The term I could not write as a green import is the ambient
  instantiation; it sits behind the ambient body's 19 supplier parameters.
  Section 4.
- C-44. The brief's "small and mechanical" was unchecked. I measured it: true.
- C-42. One site measured: `L.Coding.Sequence`. No sweep beyond it.
- C-39, C-40. Every figure traces to a file I opened. The one inference is
  marked INFERRED.
- I-5. No probe under `src/`. The probe sits in `agents/tasks/LJ-1-238/`.
- R-34. No heap wall. The `InfinitySet {ℓ}` cure was not needed.
- C-12, C-22. One process, `-M8g`, report written before the first kept run.
- DD0, DD8. One number per claim, each with its basis.
- DD4. Section 5: 145 shared, 40 plumbing, 0 residual.
- DD23. No mathematical prose written. No master edited.
