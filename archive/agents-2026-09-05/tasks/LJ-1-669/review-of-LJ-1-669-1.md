# LJ-1.669: adversarial review of LJ-1.669#1

## HEAD
head_slot: mathematician_adversarial
machine: shared
verdict: upheld
return under attack: agents/tasks/LJ-1-669/lj-1.669-report.md and
agents/tasks/LJ-1-669/review-of-sound-at-arity4.md, coder slot, attempt 0

## THE RECORD THIS REVIEW STANDS ON

`dev/pod/transitions/2026-08.jsonl` carries one line with
`"task": "LJ-1.669"`: attempt 0, `to: "READY"`, `model: null`,
`effort: null`, `heads_sha256: "665f7468"`, at 2026-08-26T13:43:20Z.
The file ends before this review instance. As the brief directs, the
six facts come from the accept arm. From
`agents/tasks/LJ-1-669/runs/accept-1.out`: run of `Probe669.agda`
rc 0 in 2.56 s; `exit_code` 0; `obligations_delta` 0;
`obligations_open` 1; `heap_wall` false; `error_class` null. Changed
files 11, all own. `changed_files_refused` empty. In-fence lines 0.

The branch row that selected this review is `stop-stated`
(agents/tasks/LJ-1-669/LJ-1.669.md): exit 0, `obligations_delta_min`
0, a changed `review-of-*.md`, and no changed `review-of-LJ-*-*.md`.
The accept facts satisfy all four conditions. The escalation is
correct.

The invariant holds. The author of the attacked return is the coder
slot. This review is the mathematician_adversarial slot. The critic is
not the author.

## THE LENS

The four questions this review attacked with are DD25's own, at
`archive/dev/DD-archived.md:35`, which reads, in part:
"The questions are: is the refusal correct on its own numbers; is the
measurement sound; did the BRIEF cause the outcome; and is there a cure
the return missed." The three written below are the review brief's own
list, at `dev/memos/LJ-4-pod-program-design.md:2853-2858`. Nothing in
this section is attributed to any other list.

### Lens 1. Is the verdict correct on its own numbers?

Yes. The NO-GO rests on two walls. Both check against the primary
sources and the runs.

Wall (i), direction. `σ₁-up` has type inner to ambient
(src/FOL/Absoluteness.lagda.md:182-184). The 658 chain's last leg is
ambient to inner (agents/tasks/LJ-1-658/Probe658.agda:269-270:
`inner = subst ⟨_⟩ (sym (AbsL.abs₀ (mapΔ₀ Empty.rec* dφ) γL)) amb-L`).
`runs/wall.out` records `[UnequalTerms]` at `Wall669.agda:57.16-36` and
prints both types: inferred inner to ambient, expected ambient to
inner. Line 57 of `Wall669.agda.txt` is
`wall-reverse = AbsL.σ₁-up Σ₁-matrix`. Same carrier, same formula, only
the arrow differs. The wall is clean. The arrow that does typecheck at
this carrier is `π₁-down`, which is the Π₁ grade
(src/FOL/Absoluteness.lagda.md:187-190), and the probe delivers it
green (`reverse-at-arity4`, Probe669.agda:134-138). So the last leg can
run without `mapΔ₀`, but not at the Σ₁ statement. That is exactly what
the verdict line claims.

Wall (ii), constant domain. `Formula` is indexed by its carrier, and
the chapter's matrix is at `CS.S`
(src/L/BoundedSubset.lagda.md:848-849, its Δ₀ certificate at :851-852).
`runs/wall-ii.out` records the refusal inside the wall-image TYPE, at
`Wall669-ii.agda:48.17-23`: the checker asked that `matrix` have type
`Formula Abs∅.SM 4`. A formula at the class carrier does not type at a
foreign image. The only delivered placement of a class-carrier
certificate at an image is `[LJ-1.161]`'s
`Abs.σ₁-up (mapΣ₁ Empty.rec* (erase-Σ₁ φ p s))`
(agents/tasks/LJ-1-161/ProbeLJ1161A.agda:83-86), and `mapΣₙ` is
`mapΔ₀` at the leaf
(src/FOL/Manipulation/Relabelling.lagda.md:234:
`mapΣₙ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)`).

The class-carrier half is green and real. `transfer-at-arity4`
(Probe669.agda:117-121) is the Σ₁ transfer at arity 4, `K` in the
environment, no `mapΔ₀`. In `Probe669.agda` the token `mapΔ₀` occurs
only in comment lines (lines 5, 22, 105, 115, 131, 157, 174, 175); the
term at line 121 is `transfer-at-arity4 = AbsL.σ₁-up Σ₁-matrix`. The
green runs are `runs/floor-0.out` (3.26 s) and `runs/final-0.out`
(4.00 s), and the accept arm re-ran it green at 2.56 s.

### Lens 2. Is the measurement sound?

Yes, with one precision note that does not change the verdict. Every
`.out` under `runs/` carries `GHCRTS=[-A64m -I0 -M2g]`, a start stamp,
an end stamp and `EXIT=` (runs/log.md). One Agda process per run. The
wall runs used temp copies of the `.agda.txt` files, removed after, and
the accept arm's changed-file list confirms no stray `.agda` landed.
`final-0` ran after a comment edit, not as a rerun of byte-identical
code: the edit sits between the runs (file mtime 22:43 local, between
the 22:41 and 22:44 run stamps in runs/log.md).

Precision note on wall (ii). The diagnostic is `[UnequalLevel]`,
`ℓ-suc ℓ != ℓ-zero`. The dummy image is built from `∅`
(Wall669-ii.agda.txt:44), and `∅` also mismatches at the universe
level, so the printed reason is a level inequality. A same-level dummy
would print `[UnequalTerms]` instead. The refusal itself fires at the
right place, inside the type, where `matrix` is checked against
`Formula Abs∅.SM 4` (runs/wall-ii.out). So the run does witness the
constant-domain refusal, and the claim is forced anyway by the
indexing: a formula at one carrier does not inhabit `Formula` at
another. The wall stands on the run plus the indexing fact together.
The next brief should not reuse `∅` as the dummy image; a same-level
predicate would isolate the domain reason in the diagnostic.

### Lens 3. Did the BRIEF cause the outcome?

The obligation text is a placeholder, and it admits a literal reading
under which a GO was writable: `transfer-at-arity4` satisfies every
clause of the literal text (arity 4, `K` in the environment, the
chapter's `Δ₀-matrix`, transfer at the Σ₁ statement, no `mapΔ₀`). The
predecessor did not use that reading to close the obligation. It took
the lineage reading, "a soundness lemma reshaped to the statement's own
shape" (agents/tasks/LJ-1-661/lj-1.661-report.md:124-129), which names
the 658 chain as the family, and it delivered the literal reading green
in the same probe (report section 6, item 1). Both arms are priced in
one return. So the brief's ambiguity did not produce a hidden failure.
It produced a fork, and the return states both arms with evidence.

What the brief does foreclose, the return reports plainly (report
section 6, item 2): on the hood chain, "at Σ₁" and "not through
`mapΔ₀`" are jointly unsatisfiable in this tree today. That foreclosure
is a measured fact about the tree, priced by the two walls. It is not a
defect of the return. A next brief that wants a GO on that chain must
lift one of the two demands, and the return says so.

### Lens 4. Is there a cure the return missed?

No cure found. The attacks made:

1. The literal reading. Answered above: delivered green.
2. The fixpoint. 658's `embed-fixed`
   (agents/tasks/LJ-1-658/Probe658.agda:252-255) fixes the formula
   under the map because its parameter domain is empty. It moves
   formulas, not certificates. A certificate at the image still needs
   `mapΣₙ`, whose Δ₀ leaf is `mapΔ₀`
   (src/FOL/Manipulation/Relabelling.lagda.md:234).
3. The count pin. The matrix's count is `refl`
   (Probe669.agda:87-88), so `[LJ-1.161]`'s erase route opens at this
   matrix. That route is `mapΣ₁`, which is `mapΔ₀` at the leaf. The
   obligation forbids `mapΔ₀`. The route is named by the return
   (review-of-sound-at-arity4.md, wall ii).
4. A hand-written image certificate would be `mapΔ₀` under another
   name. Not a cure.
5. Avoid the last leg with an ambient reader. That is fork (b) of
   `[LJ-1.662]`, priced at 138.2 s of a 150.2 s chapter profile, 92
   percent (dev/ARCHIVE.md:285). Named by the return
   (review-of-sound-at-arity4.md). Out of this price.
6. The reverse at the class carrier. It is Π₁, not Σ₁
   (Probe669.agda:134-138). The probe delivers it itself, "so the next
   brief does not rediscover it" (Probe669.agda:129-133).

## THE THREE QUESTIONS

### 1. Does the verdict LINE match its own BODY?

Yes. The verdict line says the obligation "cannot be built as a
HoodSound-shaped lemma", and the body establishes exactly that, with
the two walls and their runs. The line's qualifier, "as a
HoodSound-shaped lemma", is the lineage reading, and the body states it
openly and sources it (report section 1; review-of-sound-at-arity4.md,
"What the obligation needs"). The body never claims the literal reading
is unsatisfiable. It says the opposite: the class-carrier term is
delivered green and handed to the next brief (report section 6, item
1). No `[LJ-1.373]`-style split between a line that claims one thing
and a body that establishes another.

### 2. Is every load-bearing claim backed by a `file:line` that resolves today?

Yes. This review opened every citation it could find in the return and
checked each one. All resolve, at the cited lines: the probe facts
(Probe669.agda:78-79, :81-82, :87-88, :92-93, :101-102, :117-121,
:134-138); the wall ascriptions and their recorded error ranges
(Wall669.agda.txt:57, Wall669-ii.agda.txt:48, runs/wall.out,
runs/wall-ii.out); the primary sources
(src/FOL/Absoluteness.lagda.md:182-185, :187-190;
src/L/Constructible.lagda.md:89, :420-421;
src/FOL/Manipulation/Relabelling.lagda.md:234;
src/L/BoundedSubset.lagda.md:848-852, :901-904, :142-146;
src/L/Hierarchy.lagda.md:334-335); the lineage
(agents/tasks/LJ-1-661/lj-1.661-report.md:124-129;
agents/tasks/LJ-1-661/Probe661.agda:98-100, :105-126;
agents/tasks/LJ-1-658/Probe658.agda:226-230, :237-259, :247-270,
:269-270; agents/tasks/LJ-1-653/Probe653.agda:283-288;
agents/tasks/LJ-1-651/Probe651.agda:73-74;
agents/tasks/LJ-1-662/Probe662.agda:102-108;
agents/tasks/LJ-1-662/review-of-hoodexists.md:39-43;
agents/tasks/LJ-1-161/ProbeLJ1161A.agda:83-86); the archive price
(dev/ARCHIVE.md:285); and the run numbers (runs/floor-0.out,
runs/final-0.out, runs/accept-1.out, runs/log.md). The two notes this
review adds, the wall (ii) level diagnostic and the branch row name in
report section 1, are stated in "Precision notes" below. Neither is
load-bearing for the verdict.

### 3. Is the predecessor's enumeration complete?

Yes. The two walls cover the two transfer legs of the 658 chain: leg 1
out of the image (wall ii) and leg 3 back into the class carrier (wall
i). The outs are named, not missed: fork (b), the ambient reader
(dev/ARCHIVE.md:285); the reader residue
(agents/tasks/LJ-1-662/review-of-hoodexists.md:39-43, no theorem in
`src/` relates `graphBndAt` to `LsetGraphAt`); the delivered
class-carrier term (Probe669.agda:117-121); and the delivered reverse
(Probe669.agda:134-138). The C-42 sweep count of 1 is supported: this
review ran the same search. `sound-at-arity4`, `soundP-from-pix` and
`HoodSoundP` return no hit in `src/`; `sound-at-arity4` occurs only
under `agents/tasks/LJ-1-669/`. The sibling shapes differ from the
false one, as the return says: `HoodSoundP` is arity 2 and goes through
`mapΔ₀` (Probe658.agda:237-259); `HoodExistsP` takes no Δ₀ input
(Probe653.agda:283-288).

## PRECISION NOTES

These notes change no part of the verdict. They are recorded so the
next brief does not inherit them silently.

1. Wall (ii) prints `[UnequalLevel]` because the dummy image is built
   from `∅`, which mismatches at the universe level as well as the
   domain. The refusal still fires at the constant-domain position, in
   the type (runs/wall-ii.out). A same-level dummy would isolate the
   domain reason. See Lens 2.
2. Report section 1 says the absent obligation name "is the NO-GO the
   branch table prices". The row the facts select is `stop-stated`
   (exit 0, obligation still open), which escalates to this review, not
   row `no-go-stated` (exit 42). The report's own run table records
   exit 0 for the probe runs, so the body is accurate. The sentence is
   loose wording about the witness meter's `[NotInScope]` reading, not
   a claim the branch table contradicts.

## VERDICT

**Upheld.** The NO-GO is correct on its own numbers, its measurements
are sound, its enumeration is complete, and no cure was missed. The
obligation `sound-at-arity4` stays open as a HoodSound-shaped demand,
and the return states what any successor brief must lift to get a GO:
either the `mapΔ₀` ban on that chain, or the reader's ambient form.
With `verdict: upheld` in HEAD, exit 0 and this file close the task
under row `sys-critic-upheld-no-go`.

## COMPLIANCE

- This review wrote `agents/tasks/LJ-1-669/review-of-LJ-1-669-1.md`
  and nothing else (SCOPE).
- No `.agda` file was written or touched, no probe and no `runs/` file
  (A21, as amended for this slot).
- No table row was written. The program writes the row.

## ARCHIVE USED

- **archive/dev/DD-archived.md READ.**
  `archive/dev/DD-archived.md:35` reads
  "The questions are: is the refusal correct on its own numbers; is the
  measurement sound; did the BRIEF cause the outcome; and is there a
  cure the return missed."
  Used as the lens of this review, as the slot file directs. No other
  row of the file bears on this transfer.
- **archive/dev/ORCHESTRATION.md DECLINED.** Not read, not used. This
  review attacks a mathematical return whose evidence is in Agda
  sources and run records. The archived process document prices no
  transfer.
- **archive/dev/PLAN-archived.md DECLINED.** Not read, not used. The
  NO-GO's evidence is live in this tree: the walls, the probe, the
  runs, and the delivered `src/` terms cited above. The archived plan
  adds nothing a wall run does not already state.
- **archive/dev/measurements/README.md DECLINED.** Not read, not used.
  The numbers this review checks carry their own provenance in the run
  headers and the accept arm (runs/log.md, runs/accept-1.out).
- **archive/dev/README.md DECLINED.** Not read, not used. An index of
  the archive; this review's five candidates were handled directly.

## LITERATURE USED

- **dev/literature/level-formula-slot-roles.md READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  "| 4 | Devlin 5.2 (a) | `Φ(z,v,γ)` with `∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]`
  | 3 in `Φ`, ONE closed | `z` at position 0 | `v` at 1, `γ` at 2 |
  **VALUE, ORDINAL** | `_build/literature/dev2.txt:1186-1191` |", and
  `dev/literature/level-formula-slot-roles.md:28` reads
  "| 6 | Jech 13.14 | "The function `α → L_α` is Δ₁", from a Σ₁ step
  `∃W[...]` | 2 | `W`, the approximating function | value, ordinal |
  **VALUE, ORDINAL** | `_build/literature/jech13.txt:561-572` |".
  Read to check that the predecessor's two literature quotes resolve
  today. They do, at the cited lines. The NO-GO itself is a transfer
  fact, as the predecessor says, and no literature row contradicts it.
- **dev/literature/BIBLIOGRAPHY.md DECLINED.** Not read, not used. The
  shelf list; the two rows that bear on the statement's shape were
  checked in `level-formula-slot-roles.md` above.
- **dev/literature/devlin-errata.md DECLINED.** Not read, not used. The
  verdict rests on direction and carrier facts measured in this tree,
  not on the Devlin extraction.
- **dev/literature/primary-sources.md DECLINED.** Not read, not used.
  Source pointers; the rows used carry their own locators.
- **dev/literature/glossary-review-2026-08.md DECLINED.** Not read, not
  used. A glossary review settles terms, not transfers.
