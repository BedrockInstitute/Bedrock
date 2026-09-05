# LJ-1.621 report: Upper's target fixed at the site alpha

Head slot: coder. Machine: shared. Caliber on this pane: GHCRTS
`[-A64m -I0 -M2g]`, set by the program. I did not set it at any
point. One Agda process at a time. Every run ran under a wall-clock
cap I set and report below. This report was a skeleton before any
probe run and was filled as each answer landed (C-22).

## VERDICT

**DELIVERED, GO.** The obligation
`agents/tasks/LJ-1-621/Probe621.agda::upper-at-site` is in the probe
(`agents/tasks/LJ-1-621/Probe621.agda:121-122`) and the probe is
GREEN: `runs/final-4.out` cold at 3.34 s, `runs/final-1.out`,
`runs/final-2.out` and `runs/final-3.out` warm at 1.21 s, 1.70 s and
1.26 s, all exit 0, all postdating the last edit to the probe. The
term takes ONE hypothesis, the pairing the re-run induction needs
(the site fiber at alpha, `Probe621.agda:77-79`), and delivers
`Upper`'s induction re-run with the predicate's target FIXED at the
site alpha, `[LJ-1.617]`'s `Q` verbatim. The induction itself is
IMPORTED from `[LJ-1.617]`'s green probe, not restated, per the
brief's order. The re-run induction does NOT still demand the band:
the only pairing hypothesis the term carries is the one site fiber,
and the orientation row at `Probe621.agda:135-136` shows the band
product pays it. `[LJ-1.617]`'s central measurement stands, now by a
term that states its demand in its own type. The probe carries no
hole and no postulate in its final form. Nothing landed in `src/`.
The scope's `review-of-upper-at-site.md` is NOT written: that name is
the stop path, the obligation is discharged, so no stop is stated.
No commit, no push. `git status` shows only `agents/tasks/LJ-1-621/`
as new.

## D-10, BEFORE ANY AGDA

The brief ordered `[LJ-1.617]`'s section read in full and its `Q`
taken verbatim. The section is
`agents/tasks/LJ-1-617/lj-1.617-report.md:85-104` (`## WHICH GRAIN
THE BILL PAYS IN`), and the sentence the brief quotes from the middle
of is at `agents/tasks/LJ-1-617/lj-1.617-report.md:96`: "replaces
that predicate with `Q γ = ... ↪ ⟪ α ⟫`, the same induction". The
report ELIDES the body of `Q` there, so the verbatim term was taken
from the probe the report names in the same sentence, at
`agents/tasks/LJ-1-617/Probe617.agda:464-465`:

    Q γ = IsOrd γ → ⟨ γ ∈ˢ sucV α ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α ⟫

The target's truth was priced before the proof: the term inhabits a
substitution instance of a probe that is green in this tree, so no
Tarskian or cardinality obstruction could reach it. The only live
risk was interface cost, and the floor run below measured it at
3.07 s. `[LJ-1.617]`'s probe ALREADY builds the re-run induction
(`site-stage-card = ∈-induction step`,
`agents/tasks/LJ-1-617/Probe617.agda:470-471`), so this task
IMPORTED it. `runs/W3.agda` states `Q` alone first, and two refl
rows tie the files together (`agents/tasks/LJ-1-621/runs/W3.agda:47`
against `agents/tasks/LJ-1-621/Probe621.agda:83-85` and
`Probe621.agda:103-104`), so the alone-typechecked predicate and the
delivered one cannot drift.

## W3, THE WIDEST UNMEASURED TERM

`agents/tasks/LJ-1-621/runs/W3.agda`, written FIRST and typechecked
ALONE. It holds `Q` verbatim (`:47-48`), the step type at
`[LJ-1.617]`'s own spelling (`:54-55`), the induction type
(`:57-58`), and one hypothetical acceptance row (`:64-66`): the
tree's own induction former (`src/V/Hierarchy.lagda.md:177-179`),
the one `Upper` runs (`src/L/StageCardinal.lagda.md:566`), accepts a
step at `Q`. TYPE ONLY: no term of that file proves anything about
`Q`. Measured, not guessed: GREEN first run, exit 0, 1.29 s, peak RSS
269,975,552 bytes (257.5 MiB), under the cap this task set at TWO
MINUTES per the brief (`runs/w3-1.out`). The cap was never
approached. The brief estimated about 12 lines; the file is 66 lines
of which about 15 are code, the rest the citation record. The
estimate priced the code and did not price the record.

## THE FLOOR

Measured BEFORE the proof, per the owner's ruling of 2026-08-23: the
probe with the obligation's body holed and everything else present,
`runs/floor-1.out`, 3.07 s cold, peak RSS 452,050,944 bytes
(431.3 MiB), exit 42 with EXACTLY ONE unsolved interaction meta at
`Probe621.agda:122` and no other diagnostic. That run elaborated
`LJ-1-594.runs.W3`, `LJ-1-617.Probe617` and this task's `W3` cold.
The frame is the whole price of this task: the filled body is one
application. Caps, which I set and report: 120 s for W3, 300 s for
every probe run. No run reached a cap. No run hit the heap cap, so
the heap-wall clause never fired and no restructure was needed. No
respelling cost appeared: `Q` is written in ONE spelling everywhere,
and the two refl rows typecheck at zero.

## THE RUN LEDGER

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, cap 120 s | 0 | 1.29 s, 269,975,552 B peak RSS |
| `runs/floor-1.out` | probe, obligation body holed, cap 300 s | 42 | 3.07 s, 452,050,944 B; one meta at `:122`, no other diagnostic |
| `runs/final-1.out` | delivered, warm | 0 | 1.21 s, 313,835,520 B |
| `runs/final-2.out` | delivered, warm | 0 | 1.70 s, 284,311,552 B |
| `runs/final-3.out` | delivered, warm | 0 | 1.26 s, 295,321,600 B |
| `runs/final-4.out` | delivered, COLD: the interface files of `Probe621`, its `W3` and `Probe617` removed first (build outputs only, nothing tracked) | 0 | 3.34 s, 385,646,592 B |

Cold delivered (3.34 s) against the holed floor (3.07 s) prices the
obligation's own body at about 0.3 s. The probe is 136 lines, of
which 41 are non-blank and do not start with a comment dash (awk
count; about 26 of those are rows, the rest imports). The brief
estimated about 180 lines with
about 45 for the obligation; the estimate priced a probe that
RESTATES the induction, and the same brief ordered the import, which
removes those lines. Comparables are of SHAPE only.

## THE PREDICATE, CHANGED

`Q` in full, at `agents/tasks/LJ-1-621/runs/W3.agda:47-48`, verbatim
from `agents/tasks/LJ-1-617/Probe617.agda:464-465`:

    Q : V ℓ → Type (ℓ-suc ℓ)
    Q γ = IsOrd γ → ⟨ γ ∈ˢ sucV α ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α ⟫

Against `Upper`'s own `P` (`src/L/StageCardinal.lagda.md:530-532`),
two things change. First, the TARGET of every leg is `⟪ α ⟫`, the
fixed site, where `P` targets `⟪ γ ⟫`, each step's own ordinal.
Second, `Q` drops `P`'s per-step infinity clause
(`(⟨ α ∈ˢ ω ⟩ → Empty.⊥)`): the step at a finite member ordinal is
the same row as the step at an infinite one, so the ω base
(`L.Choice.Finite`, `FinInj`/`Tally`) is not needed at all.

What the induction then needs at each step, read off the imported
`SiteStep` (`agents/tasks/LJ-1-617/Probe617.agda:313-455`), none of
it a pairing: the composed legs `⟪ Lset δ ⟫ ↪ ⟪ α ⟫` for the member
ordinals `δ ∈ γ`, supplied by the `∈-induction` itself; the
membership embedding `emb : ⟪ γ ⟫ → ⟪ α ⟫`, from `γ ∈ sucV α` by
transitivity; the count of each member stage's formulas into
`⟪ α ⟫`, through `Bound` instantiated ONCE at the site on the site
fiber (`agents/tasks/LJ-1-617/Probe617.agda:255-256`); and the
`leastOf` selection over the ordinal well-order at the site. The
pairing demand per step is ZERO new pairing: every pair operation
happens at `α`, through the ONE fiber the term takes as its
hypothesis (`Probe621.agda:77-79`, `:121`). This is exactly the
contrast with the band spend at `src/L/StageCardinal.lagda.md:283`,
where `P`'s own-ordinal target forces `sq α α∈suc infα` at EVERY
infinite member of the band below the target.

## ITS HOME

`src/L/StageCardinal.lagda.md`, as the brief names it: a module
beside `Upper`, inside the same telescope, whose predicate sits
beside `P` at `:530-532`, and the placement SURVIVES contact. The
decisive reason is that `Bound` (`:64-219`) and `OrdSWO`
(`:228-271`) sit INSIDE that telescope, so a variant module written
beside `Upper` reuses both directly at the site and the 164 lines of
verbatim copies `[LJ-1.617]` paid for them (its sections 2 and 3)
are deleted for free. The import edge it ADDS is NONE: everything
the variant uses is already in the file's import list
(`src/L/StageCardinal.lagda.md:34-60`). The edge it would REMOVE is
`L.Choice.Finite` (`:43-44`), which only the band-valued `Upper`
consumes through `branch` and `fin-inj`; the fixed-target step needs
no finite base, a consequence `[LJ-1.617]` measured and this task's
import re-confirms. The consumer edge does not move:
`BoundedSubsetAt` still instantiates `L.StageCardinal`
(`src/L/BoundedSubset.lagda.md:1397`), but its own `sq` telescope
parameter (`:1388-1391`) narrows to the site fiber, the shape
`Probe621.agda:121` states. Nothing of this was written: the brief
forbade landing in `src/`, and the direction holds the one `src/`
collection pass until LJ-1 closes.

## W2 AND W4

**W2.** The mathematics was written ONCE, by `[LJ-1.617]`, at the
generic telescope `(lem, α, oα, α∉ω, iii)`, and this task adds ZERO
new mathematics: it imports that term
(`agents/tasks/LJ-1-621/Probe621.agda:100`), instantiates it, and
states the demand. Both trophy proofs consume the term unchanged.
No deadline forced a fixed form, so no conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`. The ideal form of this
measurement written fresh today is the probe as it stands: I did not
pay for a worse shape first and then compare. The landed ideal is
the `src/` module named in `## ITS HOME`, and the difference between
the two is exactly the 164 lines of copies, which the landing
deletes.

## PREMISES CHECKED

- Premise 1 HOLDS: `agents/tasks/LJ-1-617/lj-1.617-report.md:9`
  reads "verdict: DELIVERED, GO", and its probe is green in THIS
  tree (re-elaborated cold by `runs/floor-1.out` and
  `runs/final-4.out`).
- Premise 2 HOLDS: `P` at `src/L/StageCardinal.lagda.md:530-532`.
- Premise 3 HOLDS: the spend at `:283`,
  `module B = Bound α oα infα (sq α α∈suc infα)`.
- Premise 4 HOLDS: `src/L/BoundedSubset.lagda.md:1410`,
  `SC.Bound α ordα α∉ω (sq α (self∈sucV α) α∉ω)`.
- Premise 5 HOLDS: the Π-bound at `:1388-1391`.
- Premise 6 HOLDS: `agents/tasks/LJ-1-618/lj-1.618-report.md:9`
  reads "**NO-GO, stated.**", and the residue it names
  (`Inj-extract`, `agents/tasks/LJ-1-618/Probe618.agda:151-154`) is
  untouched here.
- Premise 7 HAS THE KNOWN DEFECT, already recorded by `[LJ-1.617]`
  and `[LJ-1.613]`: `agents/tasks/LJ-1-607/` does not exist in THIS
  worktree. The deliverables sit untracked in the main tree at
  `/Users/alsg/Agentic/Bedrock/agents/tasks/LJ-1-607/`; I read
  `lj-1.607-report.md:173` there, the head "## 6. IS THE CIRCLE
  CLOSED". This task does not rest on that type: it dissolves the
  circle's demand rather than attacking the circle, so the defect is
  recorded and the task proceeds. The next dispatch that DOES rest
  on `[LJ-1.607]` still needs the owner to commit it.
- Premise 8 HOLDS WITH AN OFFSET: section 2.4's head is at
  `dev/literature/truncation-and-selection.md:150`, Theorem 16 at
  `:158`.
- Premise 9 HOLDS WITH AN OFFSET: `agents/tasks/LJ-1-605/
  Probe605.agda:1` is the OPTIONS line; the `splitSup` citation is
  at `:172-173`.
- Premise 10 HOLDS: `agents/tasks/LJ-1-613/Probe613.agda:137-138`.
- **Premise 11 IS THE SAME DEFECT `[LJ-1.613]` REPORTED.** There is
  no R-42 in `dev/LESSONS.md`: the R series ends at R-41, and
  `dev/LESSONS.md:4404` is C-52's Related line, which lists R-41
  among others. The respelling rule is R-41 at `:4762`. The
  premise's figures "1.74 s against 155.02 s" appear in neither
  `dev/LESSONS.md` nor `dev/ledger.toml` (grep, zero hits each), so
  nothing funds them. I worked under R-41's substance: ONE spelling
  of `Q` in every row, and the two tie rows are refl.
- Premise 12 HOLDS: `AGENTS.md:45` is the measured-cure bullet's
  head.
- Premise 13 HOLDS WITH AN OFFSET: the make-check bullet head is at
  `AGENTS.md:75`; `:74` is the tail of the one-off-instruction
  bullet.

## LITERATURE STEP

Read, in full, `dev/literature/truncation-and-selection.md` section
2.4 (`:143-165`), and section 2.3's constraint line (`:146`). **This
route lifts NO truncation.** `upper-at-site` consumes the site fiber
as DATA, an explicit Σ argument, and everything it returns is
untruncated construction; no truncation token appears anywhere in
the probe or its W3 (grep, zero hits), because the imported
induction selects through `leastOf` over an hProp and never holds a
truncated witness. So the Kraus question the brief sets does not
arise FOR THIS TERM. It does arise for the term's HYPOTHESIS, and
the answer in his terms is: if a later task funds `SiteFiber α`
from the tree's truncated supply (`∥ sq δ ∥₁` at every band member,
`src/L/SquareLawClosed.lagda.md:325-328`), the type that needs a
weakly constant endomap is `SiteFiber α` at the SINGLE-SITE grain,
one fixed α, never the band Π. That is the same grain
`[LJ-1.618]`'s residue sits at (`Inj-extract`,
`agents/tasks/LJ-1-618/Probe618.agda:151-154`), and the tree holds
no such endomap there (`agents/tasks/LJ-1-618/
lj-1.618-report.md:9`). This task does not attempt one: the brief
forbids the band pairing, the square law, and B9.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.** `:192`:
  "| LJ-1.116 | At which alpha does Upper need sq? | ONLY AT OMEGA,
  AT THE SITE | Generic demand is every infinite ordinal below
  alpha; the site is omega. Init is false at omega and at
  successors |". This row records Upper's generic demand as the
  band; the term this task delivers is the one that re-runs Upper
  with that recorded demand deleted, which is why the row is the
  right ancestor. Also read and used: `:190` (`[LJ-1.114]`, WALL,
  ROUTE-LEVEL, "Upper's h-inj needs ONE honest injection"), the wall
  this task shrinks from one honest injection per band member to
  ONE, at the site, without lifting it. The index is frozen and
  carries no row for `[LJ-1.617]` or later (grep, zero hits).
- **`archive/dev/JOURNAL.md` DECLINED.** `archive/dev/JOURNAL.md:1`:
  "# ARCHIVED 2026-08-20". A retired journal; the measurements this
  task used are the live probes and reports cited above.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the
  retired route". The retired route's journal does not measure the
  re-run induction or its demand.
- **`archive/dev/DD-archived.md` DECLINED.**
  `archive/dev/DD-archived.md:1`: "# THE `DD` RULING SERIES,
  archived in full 2026-08-18". The rulings that bind this task were
  in the standing instructions; no decision history was needed.
- **`archive/dev/DECISIONS-archived.md` DECLINED.**
  `archive/dev/DECISIONS-archived.md:1`: "# Archived decisions: the
  D series". Same reason as `DD-archived.md`.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md` READ AND USED.**
  `:158`: "- **Theorem 16: \"A type X has a constant endomap if and
  only if it has split". Full statement at `:158-160`, and the
  question line at `:163`: "**So the question \"can this truncation
  be lifted\" is always the question \"does". Used for the
  literature step above; the criterion is answered, not
  re-derived.
- **`dev/literature/devlin-II5.md` READ AND USED.** `:413`:
  "|L_α| = |α| for α ≥ ω (`dev2.txt:117`, `dev2.txt:200-240`) is
  consumed at". The classical theorem states the size equation at
  EVERY infinite level, and the classical proof therefore walks the
  band, the same shape as `Upper`'s induction at `P`. The term this
  task delivers is the single-site reading of that proof: one
  injection read at one α, which is all the bill's consumer takes
  (`src/L/BoundedSubset.lagda.md:1513`).
- **`dev/literature/terms-2026-08.md` DECLINED.**
  `dev/literature/terms-2026-08.md:1`: "# The terminology dossier:
  fourteen renderings for the owner's ruling". This task adds no
  term, and the glossary rule forbids a self-chosen entry.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.**
  `dev/literature/glossary-review-2026-08.md:1`: "# Glossary review:
  the 119 pre-protocol entries". Same reason: no term was added.
- **`dev/literature/digest.md` DECLINED.**
  `dev/literature/digest.md:1`: "# Digest: the orthodox form of the
  rud route, pinned from the collected literature". No rud-route
  question arose; the measurement is inside one chapter's parameter
  grain.

## GATES

`lint-agda.py --check` exit 0; `check-probes.py --check` clean (7898
tracked files); `lint-prose.py --check` exit 0 on this report; grep
for `postulate`, `TERMINATING` and `{!` over the probe and its W3
returns nothing at code level; no em dash in any file of this scope.
`make check` not run: it is the commit gate, nothing here commits,
and no `src/` file changed. The ratio bar cannot fire: the write
scope carries no agda fence, so the in-fence count is 0.

## WHAT THE NEXT BRIEF NEEDS

1. **The demand is now a TERM's OWN TYPE.** `upper-at-site` states
   ingredient (iii)'s remaining demand as `SiteFiber α`
   (`Probe621.agda:121`): one binary function with its injectivity
   at one α. Any brief that funds the last ingredient should fund
   THAT type, at ONE site, and `[LJ-1.618]`'s `Inj-extract` is the
   residue it must clear. With it, `upper-at-site iii` IS the
   `stage-card-upper` reading the bill consumes, and with (i), (ii),
   (iv) and (v) already paid the `class-pred` formula's supplies are
   complete.
2. **What the shape resisted: nothing.** The whole task was one
   import and one application; no wall, no restructure, no
   weakening. The statement was taken whole.
3. **What is not closed:** the site fiber itself. This task does
   not build it, `[LJ-1.618]` measured the direct build NO-GO, and
   the Kraus answer above names the exact grain any funding must
   work at.
4. **For the landing:** the home survives contact with no new
   import edge and one edge removed (`L.Choice.Finite`). The one
   `src/` collection pass the direction orders after LJ-1 should
   carry it, and the same pass lifts `Bound` and `OrdSWO` out of
   the product telescope, deleting `[LJ-1.617]`'s copies and this
   probe's reason to exist beside them.
