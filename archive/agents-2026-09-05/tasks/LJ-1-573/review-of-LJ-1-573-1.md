# review-of-LJ-1-573-1: the stop of LJ-1.573#1 is UPHELD

## HEAD
verdict: upheld
head_slot: mathematician_adversarial
machine: shared
return under review: `agents/tasks/LJ-1-573/lj-1.573-report.md` (LJ-1.573#1, slot `coder`)
stop statement under review: `agents/tasks/LJ-1-573/review-of-sq-collect-at.md`
invariant: the critic is not the author. This head did not write the return,
the stop statement, or the probe.

## WHAT THIS REVIEW DECIDES

The predecessor stopped. It built no term `sq-collect-at`, it left the probe
green without that name, and it priced the row at `SetChoice (ℓ-suc ℓ)` while
narrowing the same row to one untruncated least-cardinal injection. I attack
that return on the three questions of this brief. Result: the verdict line and
the body agree, every load-bearing citation for the stop resolves today, and
the route list plus the `κ-injL` sweep are complete for this obligation. One
adjacent prior close of `rec→Set` is unnamed. It does not change the verdict.
The NO-GO is UPHELD.

## INPUTS

- `agents/tasks/LJ-1-573/lj-1.573-report.md`, read in full.
- `agents/tasks/LJ-1-573/LJ-1.573.md`, read in full.
- `agents/tasks/LJ-1-573/review-of-sq-collect-at.md`, read in full.
- `agents/tasks/LJ-1-573/Probe573.agda`, 392 lines, read in full.
- `agents/tasks/LJ-1-573/runs/W3.agda`, 106 lines, read in full.
- `agents/tasks/LJ-1-573/runs/accept-1.out`, read in full. Newest accept arm.
- The transitions record this brief names does not resolve in this worktree.
  `dev/pod/transitions/2026-08.jsonl` ends at line 157, seq 158, task
  `LJ-1.399`, ts `2026-08-19T13:31:57Z`. No line carries `"task": "LJ-1.573"`.
  So `model`, `effort` and `heads_sha256` of LJ-1.573#1 were not readable.
  The six facts of the run under review come from
  `agents/tasks/LJ-1-573/runs/accept-1.out`. No load-bearing claim of the
  return cites the transitions file, so nothing below is blocked by its
  absence.

## QUESTION 1. DOES THE VERDICT LINE MATCH ITS OWN BODY

The line (`agents/tasks/LJ-1-573/lj-1.573-report.md:8`):
"NO-GO, STATED. THE ROW NEEDS A PRINCIPLE AND THE OWNER MUST RULE."

The stop (`agents/tasks/LJ-1-573/review-of-sq-collect-at.md:6-7`):
"NO-GO. NOT INHABITED, AND NOT INHABITABLE ON THIS TREE WITHOUT A
PRINCIPLE THE OWNER MUST RULE ON."

Two readings exist for "NEEDS A PRINCIPLE", and I checked both.

The witness reading. The obligation is the name
`agents/tasks/LJ-1-573/Probe573.agda::sq-collect-at`. The name is not a
binder in the probe. The three hits are `sq-collect-at-from-choice`
(`Probe573.agda:135`), `sq-collect-at-from-bare-inj` (`:294`), and the
comment that the name is not defined (`:375`). The program's meter reports
`1 UNRESOLVED of 1` and `probe_red=False`
(`agents/tasks/LJ-1-573/runs/witness-2.out:5`). The accept arm agrees:
`obligations_open` 1, `obligations_delta` 0, `exit_code` 0,
`obligations_probe_red` false (`agents/tasks/LJ-1-573/runs/accept-1.out:20-23`
and the JSON on `:25`). Under this reading the line is the machine state,
and the body says the same thing in VERDICT (`lj-1.573-report.md:26-28`), in
WHAT THIS DOES TO THE BILL (`:183-186`), and in the stop's own headline.

The type-theoretic reading. Read as "the type `SqCollectAt` has no term from
any route, including routes that change `src/`", the line would claim more
than the body shows. The body never makes that claim. It shows two green
reductions with a hypothesis in front
(`Probe573.agda:135-141`, `:294-295`), it records that `BareLeastInjAt` is
not inhabited (`:385-389`), and it fences the stronger question as a
different row: restating `LeastCardInjL` over `InjL` "costs no principle at
all" if it can be done, and "that is a change to `src/`"
(`lj-1.573-report.md:150-154`). The stop's phrase "ON THIS TREE" is the
correct scope (`review-of-sq-collect-at.md:6`).

I rule the line matches the body. The compression "THE ROW NEEDS A PRINCIPLE"
is the on-this-tree state in the witness's vocabulary. The precise claim sits
in the report's own next-brief sentence. This is not the defect class the
project measured on 2026-08-16, where a line asserted one verdict and the
body measured another. Here the line and the body assert the same NO-GO at
two precisions, and the coarser one is backed by the witness, the accept
record, and the two hypothesised terms together.

The four-question lens, used to reach that ruling and not written as a
fourth section:

1. The refusal is correct on its own numbers. Obligation delta 0, probe
   green, name absent.
2. The measurement is sound. The `SetChoice` reduction is a term. The bare
   recursion is a term. W3's level is a machine error then a green file.
3. The brief did not foreclose a GO that this tree already had. It forbade
   an ambient choice principle (`LJ-1.573.md:81-84`) and forbade landing in
   `src/` (`:91`). Both are the standing rules. The GO the brief describes
   (`:115-116`) was not available without one of those two moves.
4. The cure the return names (restate `LeastCardInjL` over `InjL`) is a
   next row, not a missed inhabitant of this obligation. See QUESTION 3.

## QUESTION 2. DOES EVERY LOAD-BEARING CLAIM RESOLVE TODAY

I opened every citation that carries the stop. All of those resolve. One
non-load-bearing figure does not.

Obligation and meter. `Probe573.agda` has no binder `sq-collect-at`.
`runs/witness-1.out:5` and `runs/witness-2.out:5` both read
`witness: 1 UNRESOLVED of 1` and `probe_red=False`. The report cites those
phrases as `witness-1.out:4-5` (`lj-1.573-report.md:30-31`). The phrases
sit on `runs/witness-1.out:5`, not on line 4. Line 4 is the `missing` row.
The range still contains the quoted words. The accept arm records the same state
(`runs/accept-1.out:25`, `obligations_delta` 0, `obligations_open` 1,
`obligations_probe_red` false, `unbound_vacuous` true). Probe run in the
accept arm: rc 0, 3.01 s, target `Probe573.agda`. W3 run: rc 0, 0.81 s.

`SetChoice` reduction. `src/Base/Choice.lagda.md:55-56` is
`SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)` then
`→ ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁`.
`Probe573.agda:135-141` is `sq-collect-at-from-choice` at that principle
and `ℓ-suc ℓ`. The file is green (`runs/final-4.out:3-5`, exit 0 implied by
no error block, 3.49 s, 730087424 B). The stop's "letter for letter" claim
(`review-of-sq-collect-at.md:17-18`) is the shape after the index `Ix` is
collected (`Probe573.agda:119-120`), not a converse. No term
`SqCollectAt → SetChoice _` is in the file. The body already says the
`SetChoice` price is not tight (`lj-1.573-report.md:188-191` and
`Probe573.agda:145-148`). That is a one-direction measurement, and it is
stated as one.

Level. `runs/w3-1.out:4` reads `Type (ℓ-suc ℓ) != Type ℓ`, exit 42 at
`:34`. `runs/w3-2.out:3-5` is green, 0.80 s, 270041088 B. The report's
"270 MB" is that resident-set figure in decimal megabytes.

Owner's phrase. `agents/tasks/LJ-1-376/LJ-1.376.md:10` reads
`> **「`BandChoice` is an instance of `SetChoice (ℓ-suc ℓ)`」is COMMON`.
The report quotes that fragment at `:10` (`lj-1.573-report.md:56-57`). The
probe comment cites `:11` (`Probe573.agda:107`). Line 11 continues
`> KNOWLEDGE.`. The report's line number for the quoted fragment is the
one that resolves.

Diaconescu and the trophy. `src/Base/Choice.lagda.md:16` reads
`**choice proves the excluded middle**. The observation is due to Diaconescu,`.
`src/V/Model.lagda.md:528` reads
`V⊨ZFC : SetChoice (ℓ-suc ℓ) → isZFCModel`.
`src/Landmarks.lagda.md:54` reads
`V⊨ZFC : ∀ {ℓ : Level} → SetChoice (ℓ-suc ℓ) → isZFCModel (𝒮ᵥ {ℓ})`.
`src/L/Choice/Transversal.lagda.md:382` reads
`hasChoiceL : (zf : isZFModel) → ChoiceStatement zf`.
`src/Base/Choice.lagda.md:12-13` is the parameter rule the D-10 answer
cites. All resolve.

Chapter note and consumer. `src/L/StageBound.lagda.md:42` reads
`-- Collection of truncated squares to a truncated family. Not inhabited.`
`SqCollect` is at `:44-48`. `bounded-modulo-collect` is at `:137-140` and
feeds `SLC.sq-trunc-closed`. The report's reading that the comment names
the real gap at the real site resolves. The correction that "not inhabited"
is a hypothesis rather than a hole is the task's own finding, not a
citation of that line.

Four-case recursion. `src/L/SquareLawClosed.lagda.md:280-323` is `step`.
Case 1 at `:287`. Case 2 `squareω` at `:288`, and
`src/L/InjChain.lagda.md:184` is `squareω : sq ω`. Case 3 `via-col-square`
at `:307-310`, and `src/L/Ordinal/SquareLaw.lagda.md:960-961` is
`via-col-square : (α : S) → Init α → sq α`. Case 4 `PT.map2` over
`κ-injL` at `:314-319`. `κ-injL` itself is at
`src/L/SquareLawClosed.lagda.md:82-84`. `InjP` is at
`src/L/Cardinal.lagda.md:66-67`. The report's `:82-85` and `:67` ranges
contain those binders.

Bare recursion. `Probe573.agda:259-261` is
`bare-sq-closed : BareLeastInj → SqFam α`.
`:283` and `:286` are the identity functions `sqat-is-p550` and
`p550-is-sqat`. `agents/tasks/LJ-1-550/Probe550.agda:309-310` is
`SqAt = (κ : SL.S) → IsOrd (fst κ) → SqLaw (fst κ)`, and `SqLaw` at
`:82-86` is the same Σ as `SqFam`. The accept-arm green run is the
machine's word that the identity functions typecheck.
`:289-290` and `:294-295` are the LEVEL 3 and LEVEL 2 consequences.

Definability non-transfer. `src/L/Axioms/Full.lagda.md:144` is
`hasSeparationL : (a : S) (φ : Formula S 1)`. W3's unfolding
(`Probe573.agda:71-75`, `runs/W3.agda:49-53`) has no `isL`, `Lset`,
`𝒮ʟ`, code, or `⊨` under the arrow. The re-measurement at this site
resolves. It does not claim that no coded neighbour exists. Section 4
names that neighbour.

Coded bridge. `src/L/CantorBernstein.lagda.md:33-35` is `readL`.
`Probe573.agda:354-356` is `inj-from-code = readL`.
`src/L/GCH.lagda.md:37-38` is `InjL a b = ∥ Σ[ F ∈ S ] InjCode F a b ∥₁`.
`src/L/WellOrder/Base.lagda.md:158-160` is `leastOf` on an `hProp`
predicate. `src/L/Cardinal.lagda.md:63-64` is
`Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫`. All resolve.

Archive of the return. `archive/dev/LJ-dispatch-index.md:362` is the
`LJ-1.305` row and contains
`NEEDS-A-PRINCIPLE: InjData, then GREEN`.
`:371` is the `LJ-1.314` row and contains
`Select the CODE, not the function: InjCode is a proposition, so leastOf untruncates it.`
`archive/dev/JOURNAL-archived.md:1630` contains
`evidence: a choice principle implies excluded middle and would cost the tree's postulate-free claim,`.
`archive/dev/DD-archived.md:25` is the DD9 row and contains
`No `postulate` anywhere. LEM, and any classical or choice principle, is an explicit parameter`.
`archive/dev/JOURNAL.md:1353` contains
``dev/literature/truncation-and-selection.md:311-314` but sits at `:307-310`;`.
I opened each of those lines. They match the return's quotes.

Literature of the return.
`dev/literature/truncation-and-selection.md:83` contains
`**So a proof that only needs cardinal arithmetic never needs an injection as`.
`:297` contains
`4. **Does `A` decompose as an index over a well-order plus a`.
`:323` contains
`what is missing is a well-order on the INJECTIONS.`.
`:326` contains
`literature neither proves nor refutes a set-indexed instance.`.
Each quote occurs at the cited line.

C-42 table. I re-ran the live-tree search by reading
`src/L/SquareLawClosed.lagda.md` and grepping `κ-injL` under `src/`.
Seven hits, one file, at lines 82, 84, 143, 158, 176, 207, 318. The
report's commands and counts match. Enclosing names: `:125` `kappa-limit`
for `:143` and `:158`; `:166` `init-at-kappa` for `:176`; `:200`
`kappa-not-fin` for `:207`; `:314` `by-descent` for `:318`. Goals: `:143`
and `:158` spend the truncation into `κ-min-atL`, whose type is
`Empty.⊥`; `:176` feeds `clause4-at-kappa`, which eliminates into
`Empty.⊥` at `:106`; `:207` is `PT.rec Empty.isProp⊥`; `:318` is the
non-proposition `∥ sq x ∥₁`. Four propositional, one not. The sweep
resolves.

Predecessor row. `agents/tasks/LJ-1-571/Probe571.agda:162-163` is
`SqCollectAt`. `:232-234` is the non-discharge. The five-row sentence
the brief attributed to `lj-1.571-report.md:1` sits at
`agents/tasks/LJ-1-571/lj-1.571-report.md:30`, not at line 1. That is a
defect in the work brief's PREMISES list, not in this return. The return
does not cite `:1` for that sentence.

Runs table. `runs/s5-1.out:5-6` is 8.52 s and 1467482112 B (1.47 GB in
decimal). `runs/final-4.out:4-5` is 3.49 s and 730087424 B. The stop cites
`runs/final-2.out` at 3.51 s (`review-of-sq-collect-at.md:31`);
`runs/final-2.out:4` is `3.51 real`. Comment-only later runs do not change
the obligation state.

W3 size figure, not load-bearing. The report says W3 measured 96 lines
(`lj-1.573-report.md:250`). `agents/tasks/LJ-1-573/runs/W3.agda` is 106
lines. The time 0.80 s resolves (`runs/w3-2.out:4`). The qualitative
claim, that the brief's 10-line estimate was low because of imports and
written reasoning, still holds. The number 96 does not. I do not rest the
verdict on it. The probe's own 392 / 132 / 260 split does resolve:
`Probe573.agda` is 392 lines, 132 of them non-blank and not comment.

The measurement that supports the stop is sound. W3 was written first and
typechecked alone, as the brief ordered (`LJ-1.573.md:108-111`). A21 is
met on the coder side: the term `SqFam` is named and the probe is written.
No hole and no postulate are in `Probe573.agda`.

## QUESTION 3. IS THE PREDECESSOR'S ENUMERATION COMPLETE

For this obligation, yes. One adjacent prior close is unnamed. It does not
open a cure this return missed.

Routes the return enumerates, and what I checked against them:

1. Direct inhabitant of `sq-collect-at`. Absent. Meter agrees.
2. `SetChoice (ℓ-suc ℓ)`. Sufficient, as a term. Forbidden by the brief
   as an ambient principle (`LJ-1.573.md:81-84`). Named, not assumed.
3. `[LJ-1.568]`'s `hasSeparationL` carve, re-measured at this site. The
   subject would have to be an ambient function. W3 shows that subject is
   not an object-language formula. Closed.
4. One untruncated least-cardinal injection `BareLeastInjAt`. Sufficient
   for LEVEL 3, hence for the row. Not inhabited. Correctly fenced as a
   re-localization (`Probe573.agda:385-389`).
5. Restate `LeastCardInjL` over `InjL`, then `leastOf` plus `readL`. Named
   as the next brief's question. Not attempted. The brief forbids landing
   in `src/` (`LJ-1.573.md:91`). Assembling the same restatement only in
   the probe would still build a different cardinal predicate than `κL`,
   so it would not plug into `Bare.bare-sq-closed` as written. That is a
   new measurement at `src/L/Cardinal.lagda.md`, which
   `AGENTS.md:45` forbids transferring by analogy. Naming it and stopping
   is the complete move for this slot.

C-42. The shape swept is `κ-injL` in `src/`. Count 7 / 1 file / 5 uses /
1 load-bearing use. I confirmed it. The underlying binder
`LeastCardInjL.κ-inj` at `src/L/Cardinal.lagda.md:133-134` is the
definition, not a second consumer. No other `src/` consumer exists.

What is unnamed, and why it does not overturn.

`[LJ-1.391]` already stopped `sq-collect` at the generic
`L.StageCardinal` parameter and reduced it to a `2-Constant` endomap of
`sq δ` (`agents/tasks/LJ-1-391/review-of-sq-collect.md:40-44`,
`:61-63`). Law C-54 (`dev/LESSONS.md:4448-4456`) orders that check before
a new principle. This task's law bundle does not list C-54
(`LJ-1.573.md:215-230`). The predecessor does not name `[LJ-1.391]`,
`rec→Set`, Kraus, or C-54. That is an enumeration gap.

It is not a missed cure. `[LJ-1.391]` measured that paying the endomap is
paying the residue (`review-of-sq-collect.md:32-34`). The digest this
return does cite already sits downstream of that close: step 6, a
well-order on the injections, then "only then is a new principle in
question" (`dev/literature/truncation-and-selection.md:323-326`). The
predecessor's new term, `Bare.bare-sq-closed`, is tighter than
`[LJ-1.391]`'s pointwise untruncation of every square: `src/`'s own
recursion spends the truncation at one injection, not at the family. That
finding is an independent confirmation of `[LJ-1.571]`'s localisation to
`LeastCardInjL` (`Probe571.agda:236-243`) and it is green on the first
attempt, as claimed.

Work-brief ARCHIVE and LITERATURE candidates. The return names all five
archive paths and all five literature paths from `LJ-1.573.md:236-255`.
Each is quoted or declined.

W2. The brief carries no generic-carrier instruction
(`lj-1.573-report.md:229`). `Bare` is stated once at `(α : SV.S)`
(`Probe573.agda:172`) and instantiated at `fst κ` (`:289-290`). No
conflict, and none is claimed.

W8. The literature does not show that this shape is an axiom with no
condition the tree meets. The digest at `:326` says the literature
neither proves nor refutes a set-indexed instance. A literature NO-GO was
not available, so writing Agda was the right next step.

No missed inhabitant of `sq-collect-at` is in this tree today. The NO-GO
stands.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`. **READ AND USED**, to confirm this worktree
  has no LJ-1.573 transition and to check the return's own citation.
  `archive/dev/JOURNAL.md:1` reads "# ARCHIVED 2026-08-20".
  `archive/dev/JOURNAL.md:1353` reads
  "truncation-and-selection.md:311-314` but sits at `:307-310`;".
  The file is archived and does not carry this task. The line the return
  quoted is present. No other mathematical fact about row 2 is taken from
  it.
- `archive/dev/ORCHESTRATION.md`. **NAMED AND DECLINED.** Not used. The
  three questions this review writes are in the review brief and at
  `dev/memos/LJ-4-pod-program-design.md:2853-2858`. This archived file is
  the old operating text. It does not decide whether `sq-collect-at` is
  inhabited.
- `archive/dev/DD-archived.md`. **READ AND USED.**
  `archive/dev/DD-archived.md:35` reads
  `The questions are: is the refusal correct on its own numbers; is the measurement sound; did the BRIEF cause the outcome; and is there a cure the return missed.`
  That is the four-question lens this slot attacks with. The same file's
  DD9 row at `:25` is the classical-boundary line the return quoted, and
  that quote resolves.
- `archive/dev/PLAN-archived.md`. **NAMED AND DECLINED.** Not used. It is
  the construction registry as archived on 2026-08-20. This review
  attacks a stated NO-GO about one probe name. It takes no fact from
  that registry.
- `dev/ARCHIVE.md`. **NAMED AND DECLINED.** Not used. No module on this
  row is retired, and this task retires nothing. The return already
  declined the same file on that ground.

## LITERATURE USED

- `dev/literature/devlin-II5.md`. **NAMED AND DECLINED.** Not used. It is
  the Condensation Lemma and the GCH in Devlin II.5. This review attacks
  a return that measured which principle an already-stated row is, and
  it raises no source-text question.
- `dev/literature/BIBLIOGRAPHY.md`. **NAMED AND DECLINED.** Not used. It
  is the bibliography of the rud route. Row 2 as `SqCollectAt` is not a
  rud-route fetch question.
- `dev/literature/digest.md`. **NAMED AND DECLINED.** Not used. It pins
  the orthodox form of the rud route. The obligation is an ambient
  collection step already stated in `src/L/StageBound.lagda.md`.
- `dev/literature/geology.md`. **NAMED AND DECLINED.** Not used.
  Set-theoretic geology is not this row's subject and is not this
  review's subject.
- `dev/literature/devlin-errata.md`. **NAMED AND DECLINED.** Not used. It
  is Devlin error classes. This return did not rest on a Devlin lemma
  that those errata could overturn.

The digest `dev/literature/truncation-and-selection.md` is not a candidate
in this review brief. I opened it only to check the return's four quotes
in QUESTION 2. Those quotes resolve at the cited lines.
