# Review of LJ-1.582#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld
attacked: agents/tasks/LJ-1-582/lj-1.582-report.md, with its stated
NO-GO file agents/tasks/LJ-1-582/review-of-defines-level.md
brief: agents/tasks/LJ-1-582/LJ-1.582.md

## THE INVARIANT

The critic is not the author. The author ran as the coder slot. This
critic runs as `mathematician_adversarial`.
`dev/pod/transitions/2026-08.jsonl` in this worktree carries no line
with `"task": "LJ-1.582"`. The file ends at seq 158, task `LJ-1.399`,
stamp 2026-08-19T13:31:57Z. Model, effort and `heads_sha256` are
therefore not on the record here. The six facts come from the newest
accept arm only.

## THE SIX FACTS OF THE INSTANCE

From `agents/tasks/LJ-1-582/runs/accept-3.out`, newest last:

- exit 0 (`accept-3.out:27`), error class None (`:26`)
- obligations delta 0 (`:24`), obligations open 1, probe not red
  (`:29`, `obligations_probe_red: false`)
- heap wall false (`:29`, `heap_wall: false`)
- 2.32 s, in-fence lines 0, tier wide, caliber `-A64m -I0 -M4g`
  (`:5-6`, `:23-25`)
- conjuncts 1 to 6 held (`:10-15`)
- 55 changed files, 13 own (`:21-22`), all under
  `agents/tasks/LJ-1-582/` (`:29`)
- `unbound_vacuous: true` (`:29`): the obligation name is not in
  the probe

The meter agrees. `agents/tasks/LJ-1-582/runs/witness-1.out:1-2`
reads `missing exit=42` on
`agents/tasks/LJ-1-582/Probe582.agda::defines-level` and
`1 UNRESOLVED of 1, 2.96 s, probe_red=False`. Grep of
`Probe582.agda` for `defines-level` returns one comment at `:5`.

## QUESTION 1. DOES THE VERDICT LINE MATCH THE BODY

**Yes. The word is NO-GO, and the body never delivers the term.**

The HEAD says `verdict: NO-GO on defines-level`
(`lj-1.582-report.md:6`). The VERDICT section says the same:
no term of that name exists in the probe (`:18-19`). The stated
NO-GO file says the same (`review-of-defines-level.md:3-4`).
`Cert.DefinesLevel` is the pair at
`agents/tasks/LJ-1-578/Probe578.agda:234-240`: a formula over
hull codes, a truncated witness at the stage, and uniqueness of
that witness as `Lset` of the code value. Nothing in
`Probe582.agda` inhabits that type. The implication that would
inhabit it is `defines-level-from` at
`runs/full-probe.txt:475-480`, and that file is not checked.

This is not the `[LJ-1.373]` defect class. The line and the body
agree on the word.

**The HEAD's reason clause does not match the body's own rank of
the two stops.** The HEAD puts the uniqueness half first as
"written and does not fit the caliber" (`lj-1.582-report.md:6`).
The body then says the widest term is still mathematics, not
caliber (`:79-80`). Uniqueness as written is not a closed term.
`only-witness` at `runs/full-probe.txt:396-398` takes
`StageDecodeAtCode` as a hypothesis. `StageDecodeAtCode` is built
from `P570.GraphAgree` and `LiftMatrix`
(`full-probe.txt:377-379`, `Probe582.agda:287-289`).
`GraphAgree` is a type at
`agents/tasks/LJ-1-570/Probe570.agda:289-294` and has no
inhabitant. Its only consumers take it as a hypothesis
(`Probe570.agda:300`, `:324`). Infinite heap does not inhabit
that type. The HEAD's reason undersells the unpaid types. It
does not flip the word.

**The verdict is correct on its own numbers.** Accept-3 records
delta 0 and one obligation still open. The green probe is green:
`runs/final-5.out` is exit 0 at 55.26 s, peak 1,416,495,104
bytes, under `-A64m -I0 -M4g` (`final-5.out:1`, `:4-5`, `:22`).
The uniqueness assembly is not: `runs/p-19.out` is EXIT=143 at
1140.95 s, peak 9,690,267,648 bytes (`p-19.out:5-6`, `:23`).
Existence is not a line count. `HierInK` is a type at
`agents/tasks/LJ-1-532/Probe532.agda:274-277` with no term.
`[LJ-1.532]` refuted the uncorrected statement `ApproxInK`
(`lj-1.532-report.md:3-9`). `OrdReflect` is a type at
`runs/full-probe.txt:471-473` and has no predecessor: grep of
`agents/tasks` for `OrdReflect` returns this task only.

**The brief did not cause this NO-GO.** It funded one clause
(`LJ-1.582.md:88-90`) and named uniqueness as the widest term
(`:109-117`). Uniqueness states: `runs/W3.agda:52-54`,
`runs/w3-1.out` exit 0 at 2.54 s (`w3-1.out:3-4`). The brief
was wrong about which half is hard. The coder measured that
and said so (`lj-1.582-report.md:131-140`). A GO was not
available behind that wrong guess. `DefinesLevel` needs both
conjuncts (`Probe578.agda:237-240`). Existence still needs
`Witnessed` (`full-probe.txt:440-444`), which the coder reduces
to `HierInK`. The brief's sentence "EVERYTHING ELSE ON ROW 3
IS PAID" (`LJ-1.582.md:37`) is false of `GraphAgree` and of
`HierInK`. That is a brief defect. It made the task attempt a
clause the tree cannot inhabit. It did not hide a GO.

**No missed cure closes the obligation.** Instantiating `GraphB`
at the slot layout the formula wants
(`src/L/Condensation.lagda.md:2486-2488`;
`src/L/BoundedSubset.lagda.md:105`) is a cure for the caliber
wall on `abs₀`, `⊨-map` and `⊨-rename`. The coder named it and
did not do it (`lj-1.582-report.md:424-430`). That instantiation
does not inhabit `GraphAgree`. It does not inhabit `HierInK`.
It does not inhabit `OrdReflect`. Filling the caliber still
leaves the three unpaid types. A dummy formula that never
mentions the matrix would not be Devlin's (b)
(`dev/literature/devlin-II5.md:99`).

## QUESTION 2. IS EVERY LOAD-BEARING CLAIM BACKED BY A FILE:LINE THAT RESOLVES TODAY

**No. The obligation claim resolves. The Probe582 citations do
not. One next-brief grep is false.**

Claims that resolve today:

- `defines-level` is absent. `witness-1.out:1-2`. Accept-3
  `unbound_vacuous: true` (`accept-3.out:29`).
- `DefinesLevel` is the pair at `Probe578.agda:234-240`.
- `GraphAgree` is unpaid. Type at `Probe570.agda:289-294`.
  Consumers at `:300` and `:324` take it as a hypothesis.
  Grep for ` : GraphAgree` under `agents/tasks` finds the type
  and those two uses, plus the archived `[LJ-1.52]` copy.
- `HierInK` is unpaid. Type at `Probe532.agda:274-277`.
  `[LJ-1.532]` is a NO-GO by refutation of `ApproxInK`
  (`lj-1.532-report.md:3-9`). `lj-1.570-report.md:133` still
  reads `HierInK` as "a statement that is open, not a line count".
- `OrdReflect` is new. `runs/full-probe.txt:471-473`.
- Wall (b) of `[LJ-1.230]` is the missing total map
  (`lj-1.230-report.md:65-72`). The erase-and-embed route
  typechecks: `runs/s5-1.out` exit 0 at 11.31 s, 779,829,248
  bytes (`s5-1.out:4-5`, `:22`). `cf = refl` at
  `Probe582.agda:138-139`. `ψ4` at `:142-143`. The three
  embeddings at `:206-213`. `Cnt.erase-inv` at `:221-222`.
- The formula is `levelFo` at `Probe582.agda:241-242`.
  Written out it is Devlin's (b) with the three departures the
  report names. `dev/literature/devlin-II5.md:99` reads
  "> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)]."
  The bound as its own slot is `src/L/BoundedSubset.lagda.md:69-71`.
  `close` is at `:534-536`, with `K : Type (ℓ-suc ℓ)`. Hull
  codes are `Type ℓ` (`src/L/Hull.lagda.md:72`).
- `abs₀` is at `src/FOL/Absoluteness.lagda.md:122`.
  `⊨-map` is at `src/FOL/Manipulation/Relabelling.lagda.md:154`.
  `⊨-rename` is at `src/FOL/Manipulation/Renaming.lagda.md:127`.
  `_⊨_` is the structural recursion at
  `src/FOL/Semantics.lagda.md:91-92`.
- The implicit-formula law is a two-file difference.
  `runs/s6-1.out` is heap exhausted at 182.14 s, 8,980,856,832
  bytes (`s6-1.out:4-8`). `runs/s7-1.out` is exit 0 at 11.20 s,
  810,336,256 bytes (`s7-1.out:3-5`, `:22`). Sixteen times the
  seconds. Eleven times the resident set.
- The `-M4g` re-take matches the files. Green:
  `final-5.out` 55.26 s / 1,416,495,104;
  `s2-2.out` 2.35 s / 688,275,456, EXIT=0 (`:3`, `:21`);
  `s5-2.out` 2.33 s / 705,085,440, EXIT=0 (`:3`, `:21`);
  `s7-2.out` 11.38 s / 810,336,256, EXIT=0 (`:4-5`, `:22`);
  `w3-2.out` 2.30 s / 717,619,200, EXIT=0 (`:3`, `:21`).
  Walls: `s4-2.out` 69.98 s / 4,798,758,912 (`:4-8`);
  `s6-2.out` 92.34 s / 4,803,313,664 (`:4-8`);
  `s8-2.out` 1011.20 s / 5,254,774,784 (`:4-8`);
  accept-1 and accept-2 on `S3.agda` at 63.53 s and 63.89 s,
  exit 251 (`accept-1.out:18`, `:24`; `accept-2.out:18`, `:24`).
- This worktree's `dev/pod/heads.toml` still reads
  `heap = "-A64m -I0 -M8g"` at `[tiers.wide]` (`:291`) and
  `-M12g` at `[tiers.heavy]` (`:295`). The accept arm ran
  `-M4g` (`accept-3.out:5`). The coder did not mix the two
  caps in one comparison (`lj-1.582-report.md:51-54`).
- `levelHoodB` is at `src/L/BoundedSubset.lagda.md:108-111`.
- Clause (ii) does not need uniqueness
  (`Probe578.agda:242-243`).
- Clause (iii) is at the collapse (`Probe578.agda:503-510`).

Claims that do not resolve today:

- **Every `Probe582.agda:N` citation in the report is about ten
  lines early.** The caliber-move comment at
  `Probe582.agda:17-26` was inserted after those citations were
  written. The report still points at the old numbers. Load-bearing
  examples, claimed against what stands at that line today:

  | claimed | what the report says is there | what stands today | actual site |
  |---|---|---|---|
  | `:231-232` | `levelFo` | blank, then `mapUp`'s type | `:241-242` |
  | `:94-96` | `OnlyWitness` | start of `module W3` | `:104-106` |
  | `:132-133` | `ψ4` | the closer of section 2 | `:142-143` |
  | `:140-147` | `ordOf` | `ψ4` and `Δ₀-ψ4` | `:150-154` |
  | `:150-154` | `ρ` | `ordOf` | `:160-164` |
  | `:159-160` | `⊥map` | the comment on slots, then `ρ`'s type | `:169-170` |
  | `:196-203` | the three embeddings | `module At`'s opens | `:206-213` |
  | `:205-209` | the Lévy witness | `matC` and `matSL` | `:215-219` |
  | `:211-212` | `erase-inv` | blank, then `matCS` | `:221-222` |
  | `:262-265` | `LiftMatrix` | the comment on `_⊨_` | `:272-275` |
  | `:277-279` | the stage decode as a term | the comment on wall (b) | `StageDecode` at `:280-283`; `decode-from` at `:287-289` |
  | `:336-338` | `guard-of` | `ordOf-write`'s `hV` and `hM` | `:346-348` |

  The green file is 372 lines, not 362
  (`lj-1.582-report.md:282`). The claims are true at the
  shifted lines. The citations do not resolve today.

- **The grep "no later task cites `[LJ-1.230]`" is false.**
  `lj-1.582-report.md:439-441` says
  `grep -rn "LJ-1.230" agents/tasks/LJ-1-5*/` returns nothing.
  It does not. `[LJ-1.532]` cites it at
  `agents/tasks/LJ-1-532/Probe532.agda:26` and `:270`, and in
  `lj-1.532-report.md:177`. `[LJ-1.536]` cites it at
  `lj-1.536-report.md:75`. `[LJ-1.570]` cites it at
  `review-of-cohyps.md:22`. The next-brief advice that 570
  alone is the wrong predecessor can still be right. The
  measured emptiness is not.

None of these falsifies NO-GO. An unchecked term is still not
a proof (`lj-1.582-report.md:264-266`). That sentence is the
right one, and it does not depend on a drifted line.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

**The blockers of the obligation are complete. The next-brief
ranking is not.**

`defines-level-from-the-five` at `runs/full-probe.txt:484-489`
is the whole bill: `GraphAgree`, `LiftMatrix`, `CodeHop`,
`RenameHop`, `Witnessed`, `OrdReflect`. Six hypotheses, three
kinds.

- Mathematics already open: `GraphAgree` (wall (a) of
  `[LJ-1.230]`, `lj-1.230-report.md:57-63`) and `HierInK`
  inside `Witnessed` (wall (c), `:74-86`; the corrected type
  at `Probe532.agda:274-277`).
- Mathematics new to this task: `OrdReflect`
  (`full-probe.txt:471-473`), forced by
  `DefinesLevel`'s hypothesis `IsOrd (HS.C.π (fst (T.val c)))`
  (`Probe578.agda:236`) against the formula's guard on the
  code value (`Probe582.agda:347-348`).
- Caliber: `LiftMatrix` is `abs₀` (`Probe582.agda:272-275`),
  `CodeHop` is `⊨-map` (`full-probe.txt:353-355`),
  `RenameHop` is `⊨-rename` (`:357-360`). `runs/s8-1.out` is
  the sharp `abs₀` slice: 1115.97 s, 9,379,807,232 bytes,
  stopped (`s8-1.out:4-6`).

No seventh blocker is needed to keep the obligation open.
Any one of `GraphAgree`, `HierInK`, or the assembly wall is
enough. All three stand. Clause (ii) and clause (iii) were
not attempted, as the brief required (`LJ-1.582.md:88-90`).
W3 named uniqueness, specified `runs/W3.agda`, and then
named the replacement: whether the matrix moves off the
class carrier (`lj-1.582-report.md:142-145`). The formula
moves. A satisfaction of it does not. W7 holds: the formula
is over `T.Code` (`Probe582.agda:241`). W8 holds: Devlin's
(b) is not an axiom with no condition this tree meets, and
`dev/literature/devlin-errata.md` has no II.5 (b) row.

**What the enumeration did not finish is the next action.**
The body ranks the unpaid types first (`:79-80`, `:405`).
It then says the next brief is not about mathematics, it is
about the caliber (`:421`). Those two sentences cannot both
steer a successor. A brief that funds only `GraphB` at a new
slot layout still owes `GraphAgree`, `HierInK` and
`OrdReflect`. A brief that funds only those three still
owes a decode that does not apply a satisfaction lemma to
the level-hood matrix. Both are next. Neither is paid.

The false 230-grep belongs here too. Later tasks in the
`LJ-1-5*` band already point at `[LJ-1.230]`. What they did
not do is close wall (b). This task did, for the formula.

W3's type is not the obligation. The brief asked for
uniqueness first and alone. The coder built that type. The
obligation is the pair. The pair is open. The NO-GO stands.

## ARCHIVE USED

- **`archive/dev/JOURNAL.md`.** Read.
  `archive/dev/JOURNAL.md:410` reads
  "level-hood must run through codes and satisfaction, and those leaves are"
  That is the reason clause (i) is a satisfaction, and it is
  why the three hops cost what they cost. The predecessor
  quoted the same line. It resolves.
- **`archive/dev/ORCHESTRATION.md`.** Not used. Declined: it is
  the retired operating document
  (`archive/dev/ORCHESTRATION.md:1`,
  "# ORCHESTRATION: the orchestrator's operating rules").
  The six facts of this instance are in `runs/accept-3.out`.
- **`archive/dev/DD-archived.md`.** Read.
  `archive/dev/DD-archived.md:35` reads
  "The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed."
  Those four are the lens. The three questions above are the
  written answers.
- **`archive/dev/PLAN-archived.md`.** Not used. Declined: it is
  the archived construction registry
  (`archive/dev/PLAN-archived.md:3`,
  "This file is the construction registry as it stood on archival day. Nothing below is current.").
  It does not bear on whether `defines-level` is inhabited.
- **`dev/ARCHIVE.md`.** Not used. Declined: it is the registry
  of retired modules (`dev/ARCHIVE.md:3`,
  "The registry of Bedrock's retired modules."). This task
  retired none.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`.** Read.
  `dev/literature/devlin-II5.md:99` reads
  "> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)]."
  Clause (i) is this inner direction, at the stage, over hull
  codes. The three departures the report names are forced by
  the tree. They do not make a different theorem. They do not
  give a cheaper formula that still meets `DefinesLevel`.
- **`dev/literature/BIBLIOGRAPHY.md`.** Not used. Declined: it
  is the rud-route source list
  (`dev/literature/BIBLIOGRAPHY.md:1`,
  "# Bibliography for the rud route"). The primary clause is
  already in `devlin-II5.md`.
- **`dev/literature/digest.md`.** Not used. Declined: the
  predecessor declined it as the fetch record for Devlin II.5
  (`lj-1.582-report.md:506-510`). This review does not pay
  that reading a second time.
- **`dev/literature/geology.md`.** Not used. Declined: it is
  the set-theoretic geology dossier
  (`dev/literature/geology.md:1`,
  "# Geology dossier: set-theoretic geology sources and the five questions").
  It does not bear on Devlin II.5 (b).
- **`dev/literature/devlin-errata.md`.** Read.
  `dev/literature/devlin-errata.md:100` reads
  "set BIN of finite binary sequences), and (b) the wrong type ("The values of f"
  That (b) is a bounding-class defect in I.9, not II.5 (b).
  Grep of the file for `II.5` and `L_γ` returns nothing.
  Devlin's (b) is not withdrawn. W8 does not abort.
