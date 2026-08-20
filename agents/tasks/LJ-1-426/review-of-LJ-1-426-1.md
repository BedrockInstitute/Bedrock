# LJ-1.426: adversarial review of the return of LJ-1.426#1

## HEAD
head_slot: `mathematician_adversarial`. machine: shared.
Return attacked: `agents/tasks/LJ-1-426/lj-1.426-report.md` and its stated
NO-GO `agents/tasks/LJ-1-426/review-of-kappa-coded.md`. The branch is
`no-go-stated` (exit 42, `review-of-*.md` changed), so this head is the
critic and not the author.

## VERDICT OF THIS REVIEW

**AGREE. The NO-GO stands.** A review that agrees is a real result. Every
load-bearing claim was re-measured or re-opened, and each held. Three
findings follow. None changes the verdict. One finding is a record gap
outside the return, and it is reported because the brief sent me to that
record.

## QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY?

**YES.**

The verdict line is
`agents/tasks/LJ-1-426/lj-1.426-report.md:51`: "**NO-GO on `kappa-coded`.
GO on HALF B at this pair, with the four readings as module hypotheses."
Three bullets follow it, and the body backs each one.

1. "`from-graph` is GREEN" (`:54-56`). The three `runs/w3-*.out` files
   carry Agda's "Checking" line and no error text. In this setup Agda
   prints errors into the `.out` file, as `runs/kappa-coded-hole-1.out:2`
   shows. So clean `.out` text means exit 0. The claim also survives in
   the delivered file itself: the three hole rechecks checked the whole
   file, and the only error they report is the hole
   (`runs/kappa-coded-hole-1.out:2`). `from-graph` sits in that file with
   no error against it. GREEN is verified twice over.
2. "`kappa-coded` is a hole" (`:59-62`). Verified:
   `agents/tasks/LJ-1-426/Probe426.agda:136` is `kappa-coded = {!!}`, and
   Agda reports `UnsolvedInteractionMetas` at `Probe426.agda:136.17-21`
   (`runs/kappa-coded-hole-1.out:2`).
3. "HALF A at this pair has no producer in the live chapters" (`:63-64`).
   See question 3. My own survey of `src/` agrees.

The numbers on the verdict line were recomputed from the `.time` files.
Green runs: 1.79, 1.64, 1.71 (`runs/w3-1.time:1`, `runs/w3-2.time:1`,
`runs/w3-3.time:1`), so the median 1.71 s is correct
(`lj-1.426-report.md:204`), and the peak 396509184 bytes is the maximum of
the three (`runs/w3-1.time:2`). Hole runs: 1.66, 1.68, 1.69, so the median
1.68 s is correct (`:244`), and the peak 393101312 bytes is the maximum.
The program's own accept record agrees with the exit:
`runs/accept-1.out:16` "# run agents/tasks/LJ-1-426/Probe426.agda rc 42
seconds 1.79" and `runs/accept-1.out:22` "# exit 42".

One wording risk, not a mismatch: the verdict line says "GO on HALF B".
The brief reserves GO for a discharge of the campaign's residue. The body
never claims that discharge; it says the four readings are module
hypotheses (`lj-1.426-report.md:311-312`). The first clause of the line is
"NO-GO on `kappa-coded`", and that is the clause the accept record
measured (`runs/accept-1.out:10` "# conjunct 1 FAILED"). No reader of line
and body together can take this return for a GO.

The return also keeps the F5 and F6 discipline. It writes no universal
negative: "This is not a refutation of the type"
(`review-of-kappa-coded.md:62-64`).

## QUESTION 2: DOES EVERY LOAD-BEARING CLAIM RESOLVE AT `file:line` TODAY?

**YES, with two one-line imprecisions. Both are adjacent-line cites. Both
claims are true at the neighbouring line. Neither is load-bearing at the
wrong site.**

Every cite below was opened this session and resolves:

- `src/L/Cardinal.lagda.md:61` `module LeastCardInjL`, `:63-64` the `Inj`
  type, `:109-110` `idInj`, `:116-117` `least = leastOf`, `:119-120`
  `γ-card`, `:122-123` `κ`, `:129-130` `κ∈sα`, `:133` `κ-inj`
  truncated, `:140-141` `κ-min-at`, `:163` `module SiteBound`, `:171-172`
  `up`, `:223-228` `InjCode`. All resolve.
- `src/L/InjChain.lagda.md:314-324` `module Comp` with eight conjunct
  hypotheses, `:336-339` the composite by `hasSeparationL`, `:494-495`
  `pair-out`, `:509-511` `pair-in`, `:519` the `svAt-in` argument, `:526`
  the `injAt-in` argument, `:575-576` `module InclGraph (D C : S)`,
  `:604-607` `module OrdIncl`. All resolve.
- `src/L/Absorption.lagda.md:400-401` `sep` at `Formula S 1`;
  `src/L/Axioms/Full.lagda.md:144-145` `hasSeparationL` same type;
  `src/FOL/Syntax.lagda.md:42-44` `con` and `var`, `:94-100` the
  `Formula` constructors. All resolve.
- `agents/tasks/LJ-1-414/Probe414.agda:65-66` `HalfA`, `:115-128`
  `code-from-graph`, `:139` `amb-to-coded = {!!}`. All resolve.
- `agents/tasks/LJ-1-414/lj-1.414-report.md:39` "not proved and not
  refuted". Resolves.
- `dev/pod/audit-2026-08-20.md:76` F5, `:83-91` F6, `:88` the 8.5 GB RSS
  kill. Resolve.
- `dev/pod/direction.md:37` the one-collection direction. Resolves.
- `agents/tasks/LJ-1-399/lj-1.399-report.md:83-91` wall 2, the missing
  arithmetic atoms. Resolves.
- Literature: `dev/literature/truncation-and-selection.md:75-76` and
  `:146-148`, `dev/literature/devlin-II5.md:72-77`,
  `dev/literature/digest.md:45`. All resolve and say what the return says.

The two imprecisions:

- F-B1. The return cites the `OrdIncl` open at
  `src/L/InjChain.lagda.md:608` (`lj-1.426-report.md:94-95`).
  Line 608 is the closing fence of the code block. The open
  `open InclGraph D C (λ _ z∈D → oC .fst z∈D D∈C) public` is line 607.
  The claim is true at 607.
- F-B2. The return names the copied telescope as
  `Probe426.agda:51-104` and `code-from-graph` as `:90-104`
  (`lj-1.426-report.md:82`, `:218`, `:225-226`). The module opens at line 50
  and the last code line is 103. The spans cover the object and nothing
  else. The fourteen-line count for `Probe426.agda:117-130` is exact.

**F-A, a record gap outside the return.** The brief told me to read "the
six facts, `model`, `effort` and `heads_sha256` of that instance in
`dev/pod/transitions/`". That record does not exist. The log's last line
is `dev/pod/transitions/2026-08.jsonl:157`, seq 158, task LJ-1.399,
timestamp 2026-08-19T13:31:57Z. No entry for LJ-1.426 and no entry dated
2026-08-20 is in the file. What does exist: the facts block and the
caliber in `runs/accept-1.out`, and the heads hash in
`agents/tasks/LJ-1-426/.pod:1`, whose tail is
"at=2026-08-20T11:45:33Z". `model` and `effort` for this instance are
recorded nowhere I can cite. This is a program-side gap. It is not a
defect in the return, and it does not touch the verdict. It is reported
because the checker of the next dispatch will be sent to the same absent
record.

## QUESTION 3: IS THE PREDECESSOR'S ENUMERATION COMPLETE?

**YES. I re-ran the enumeration independently and found no fifth
supplier.**

The brief prescribed four candidates and the return answered all four
(`lj-1.426-report.md:207-208`): "**None of the four has a producer at the
pair `(a, κ)`.**". A prescribed list can foreclose a cure, so I searched the
live tree for producers the list missed. Method: `grep` over `src/` for
every site that produces an `InjCode`, a graph code, or a crossing from an
ambient function to a code.

- `src/L/CantorBernstein.lagda.md:33-41`, `readL`: consumes
  `Σ[ F ∈ S ] InjCode F a b` and returns an ambient injection. It is a
  consumer of codes, not a producer. Wrong direction for HALF A.
- `src/L/GCH.lagda.md:37-38`, `InjL`: a definition, the truncation of
  `InjCode` existence. `GCHStatement` (`:59-68`) is the trophy and is not
  proved. No producer.
- `src/L/Cardinal.lagda.md:182-210`, `Canonical`: selects a code GIVEN
  `∥ Σ[ A ∈ Mem (Lset β) ] ⟨ Good A ⟩ ∥₁` as a hypothesis (`:192`). It
  consumes a truncated code existence. It does not make one.
- `src/L/Coding/` and `src/L/Choice/`: these code the graphs of definable
  recursions, environments and choice tables. `L.Coding.Graph` codes the
  recursion's own graph (`satGraphOn`). None takes an ambient function as
  input. The return's section 2.3 measurement stands: `sep` takes a
  `Formula S 1` (`src/L/Absorption.lagda.md:400-401`), and `Formula`'s
  constructors are syntax only (`src/FOL/Syntax.lagda.md:94-100`). An
  ambient `↪` has no route into a formula.
- `src/L/Ordinal/`, `src/L/Condensation/`, `src/L/WellOrder/`: ordinal
  arithmetic, agreement lemmas and the SWO frame. No coded injection
  graph.

One candidate the return could not have read: `[LJ-1.424]`. Its files are
absent from this worktree. The commit that carries them, `ad62a9c` at
2026-08-20 20:00:26, landed on main after this worktree was cut at
19:45:33 (`git log`; `agents/tasks/LJ-1-426/.pod:1`). I read it from git.
It is downstream, not a missed cure: `isPropInjCode` and a `leastOf`
selection FROM a truncated code existence
(`git show ad62a9c:agents/tasks/LJ-1-424/Probe424.agda`, lines 64-95 of
that file). It consumes a GO from this task. It supplies nothing toward
HALF A. So the worktree cut foreclosed nothing, and the brief's GO clause
("With `[LJ-1.424]` it gives the ambient arrow at `κ` as DATA") reads
correctly with 424 as the downstream selector.

The direction argument in section 2.1 was also checked on its own steps.
`κ ∈ sucV (fst a)` gives `OrdIncl` at domain `κ`, codomain `sucV (fst a)`,
the wrong way. The needed instantiation wants `⟨ fst a ∈ fst κ ⟩`, and
`κ-min-at` (`src/L/Cardinal.lagda.md:140-141`) with `idInj`
(`:109-110`) refutes that hypothesis at `δ = a`. Sound.

**No cure was missed. The enumeration is complete against the live tree
as of this worktree.**

## FINDINGS

- **F-A (program side, report to the owner).** The LJ-1.426 instance has
  no record in `dev/pod/transitions/2026-08.jsonl`. The log stops at
  `:157`, 2026-08-19. `model` and `effort` for this instance are not
  recoverable from the tracked files.
- **F-B (return, minor).** Two adjacent-line cites:
  `src/L/InjChain.lagda.md:608` for the open at `:607`, and the spans
  `Probe426.agda:51-104` and `:90-104` for the module at `:50-103`. True
  one line over. No action needed for the verdict; a next brief that
  quotes those spans should shift them by one.
- **F-C (worktree, no defect).** `agents/tasks/LJ-1-424/` is absent from
  this worktree. Read from git when needed.

## ARCHIVE USED

- `archive/dev/PLAN-archived.md`: opened, declined. `:1` "# ARCHIVED
  2026-08-20". It is the retired plan. It does not bear on HALF A at
  `(a, κ)`.
- `archive/dev/JOURNAL.md`: opened, declined. `:1` "# ARCHIVED
  2026-08-20". The per-episode journal is retired. Not used.
- `archive/dev/ORCHESTRATION.md`: opened, declined. `:1` "# ORCHESTRATION:
  the orchestrator's operating rules". Dispatch rules, not mathematics.
  Not used.
- `archive/dev/DD-archived.md`: opened, declined. `:1` "# THE `DD` RULING
  SERIES, archived in full 2026-08-18". The rulings archive was already
  in the brief's premises where cited. Not used again.
- `dev/ARCHIVE.md`: opened, declined. `:1` "# ARCHIVE.md: the archive
  registry". No module retires in this review. Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read. `:72` "> 5.2 Theorem (The
  Condensation Lemma). Let α be a limit ordinal. If". Used to check the
  return's W8 claim: the literature's map is a collapse of a hull, and it
  codes no arbitrary ambient injection. The claim holds.
- `dev/literature/digest.md`: read. `:45` "limit α (SZ pp. 9-10, equation
  I.1). Condensation is at the Sigma-1". Used to check the same claim at
  the second source. It holds.
- `dev/literature/BIBLIOGRAPHY.md`: opened, declined. `:1` "# Bibliography
  for the rud route". A source list. This review needed statements, not
  sources. Not used.
- `dev/literature/geology.md`: opened, declined. `:1` "# Geology dossier:
  set-theoretic geology sources and the five questions". Geology, not the
  least-cardinal arrow. Not used.
- `dev/literature/devlin-errata.md`: opened, declined. `:1` "# Devlin
  errata: documented error classes (do-not-repeat checklist)". No Devlin
  text was relied on beyond the two checked statements above. Not used.
