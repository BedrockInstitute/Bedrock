# LJ-1.393 report: the ambient cardinal, and the first `Init` above omega

SPLIT VERDICT, second dispatch. The first dispatch built both obligations
green against a bare `amb-limit` module hypothesis; that return failed only
the survey duty (no ARCHIVE USED or LITERATURE USED sections), and before
the re-dispatch `[LJ-1.392]` returned and changed the mathematics: it
REFUTED the bare `amb-limit` the first file rested on. This return
re-answers the obligation in the world as it now stands.

- **GO on `amb-noinj²`**, `Init`'s fourth conjunct. One composition,
  green in the control run, at every ordinal:
  `agents/tasks/LJ-1-393/Probe393.agda:119-131`.
- **NO-GO on `amb-init` as stated, and the NO-GO is a REFUTATION built
  in Agda, not a failure to finish.** The stated term implies
  `Empty.⊥` at `α := sucV ω`: every hypothesis it names HOLDS there and
  `Init (sucV ω)` is FALSE there. The refutation is green at
  `agents/tasks/LJ-1-393/Probe393.agda:152-170`; the obligation itself is
  left as a hole, red by design, at
  `agents/tasks/LJ-1-393/Probe393.agda:185`. The obstruction is stated in
  `agents/tasks/LJ-1-393/review-of-amb-init.md`.
- **The corrected target `amb-init'` is built and green**, with ONE new
  hypothesis against the stated form: `⟨ sucV ω ∈ α ⟩`. `Init α` follows
  from `IsOrd α`, `ω ∈ α`, `sucV ω ∈ α`, `AmbCard α` and the member
  square law: `agents/tasks/LJ-1-393/Probe393.agda:207-221`.

## Verdict

The file as left is red with exactly one unsolved meta (the deliberate
hole), so the branch table routes this return through `no-go-stated`:
exit 42, error class `unsolved_meta`, and a changed
`agents/tasks/LJ-1-393/review-of-amb-init.md`. The witness meter reads
both obligation names PROBE_RED through the hole, exactly as `[LJ-1.392]`
documented for its own split return; the GREEN half is measured by the
control run below, which removes the obligation's declaration and hole
and leaves every other term green.

## What was built

All in `agents/tasks/LJ-1-393/Probe393.agda`, module
`LJ-1-393.Probe393 {ℓ} (lem) (amb-limit)`:

- `AmbCard`, the ambient cardinality notion, a definition:
  `agents/tasks/LJ-1-393/Probe393.agda:102-104`. No ambient injection of
  `⟪ α ⟫` into an infinite ordinal member of `α`. `IsCardinalL` is
  imported from nowhere; `L.Cardinal` is opened for `_↪_` alone
  (`agents/tasks/LJ-1-393/Probe393.agda:97`).
- `amb-noinj²`, `Init`'s fourth conjunct, OBLIGATION 1, GO:
  `agents/tasks/LJ-1-393/Probe393.agda:119-131`. It is the one
  composition the brief predicted: `g = fst (sqβ ...) ∘ f`, injective by
  the member's pairing injectivity, refuted by `AmbCard α`.
- `no-ω-mem-sucω`, `AmbCard-sucω`, `sqβ-sucω`, `amb-init-refuted`: the
  refutation of OBLIGATION 2, at
  `agents/tasks/LJ-1-393/Probe393.agda:152-170`.
- `amb-init`, OBLIGATION 2, as the brief states it, left as a hole:
  `agents/tasks/LJ-1-393/Probe393.agda:182-185`. No term of this type
  exists if the ambient theory is consistent.
- `amb-init'`, the CORRECTED target, green:
  `agents/tasks/LJ-1-393/Probe393.agda:207-221`. Third conjunct by the
  three-way ordinal trichotomy on a member against `ω`. No
  finite-exclusion clause is built anywhere: `Initial` supplies
  `finite-excl` itself from the second conjunct
  (`src/L/Ordinal/SquareLaw.lagda.md:938-941`), read before anything was
  written, so no clause is priced twice.
- `amb-sq'`, one line beyond the brief's three items, the payoff made
  checkable: `agents/tasks/LJ-1-393/Probe393.agda:233-236`. With
  `via-col-square` (`src/L/Ordinal/SquareLaw.lagda.md:960-961`),
  `amb-init'` IS a square law producer GIVEN `AmbCard` and the member
  square law.

Code lines: `AmbCard` 3, `amb-noinj²` 12, the refutation 16, the hole 4,
`amb-init'` 14, `amb-sq'` 4. The brief's three items together (definition,
fourth conjunct, assembly) are 3 + 12 + 14 = 29 code lines against the
brief's estimate of about 45; the estimate's comparable (`Coreω`) prices a
shape whose clauses are vacuous at `ω`, and this return also carries a
refutation and a corrected assembly the estimate never priced. Do not fund
against either number.

## The form taken for `amb-limit`

The module hypothesis is the REPAIRED form `[LJ-1.392]` reports,
`amb-limit-ω∈γ` (`agents/tasks/LJ-1-392/Probe392.agda:255-266`): closure
at every member that CONTAINS `ω`. The stated bare form
(`agents/tasks/LJ-1-392/Probe392.agda:211-215`) is refuted
(`agents/tasks/LJ-1-392/Probe392.agda:236-244`), and `[LJ-1.392]`'s
report warns this task not to take it: a refuted hypothesis is
uninstantiable, and a chapter built on it proves nothing usable. The
first dispatch took the bare form because `[LJ-1.392]` had returned
nothing while it ran; that file is replaced by this one. One spelling
departure, forced by the meter and not by the mathematics: the inner
no-injection clause of the hypothesis is written as an explicit Sigma,
because `_↪_` lives in `L.Cardinal`, whose explicit `lem` parameter
cannot be opened above the module header, and the witness derivation
copies only the lines above that header
(`scripts/pod/witness.py:126-131`). The Sigma is `_↪_` unfolded
(`src/L/Cardinal.lagda.md:47-48`), so `amb-init'` passes `ac : AmbCard α`
into `amb-limit` with no adapter (`agents/tasks/LJ-1-393/Probe393.agda:220`).

## The refutation of the stated `amb-init`

`α := sucV ω` kills it, in four steps, all green in the probe and all
supports delivered in the tree:

1. `AmbCard (sucV ω)` holds VACUOUSLY: `AmbCard` speaks only at members
   containing `ω`, a member of `sucV ω` is a member of `ω` or `ω` itself,
   no member of `ω` contains `ω` (`ω∉β`,
   `src/L/InjChain.lagda.md:123-126`) and `ω` does not contain itself
   (`∈-irrefl`, `src/V/Hierarchy.lagda.md:155`). The core term is
   `[LJ-1.392]`'s `noinj-vacuous-sucω`
   (`agents/tasks/LJ-1-392/Probe392.agda:229-235`), rebuilt here and
   credited in place.
2. The member square-law hypothesis holds vacuously for the same reason:
   it speaks only at infinite ordinal members, and there are none.
3. `IsOrd (sucV ω)` and `⟨ ω ∈ sucV ω ⟩` are delivered (`suc-ord`,
   `ω-ord`, `self∈sucV`).
4. `Init (sucV ω)` is FALSE at its THIRD conjunct
   (`src/L/Ordinal/SquareLaw.lagda.md:695`): at `γ := ω` it demands
   `⟨ sucV ω ∈ sucV ω ⟩`, which `∈-irrefl` refutes.

So `amb-init` applied at `sucV ω` yields a false statement; the term
`amb-init-refuted` builds the whole chain. This is the successor-side
recurrence of the boundary correction the archive holds for `ω` itself:
`Init ω` is uninhabited through the SECOND conjunct
(`archive/dev/JOURNAL-archived.md:2000-2006`), `Init (sucV ω)` through the
third. The corrected target adds exactly the failing membership,
`⟨ sucV ω ∈ α ⟩`, and `sucV ω` itself fails that one hypothesis, so the
corrected form is consistent with the refutation.

## What the statements cost

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, dependencies warm, from the repository
root, 2026-08-19:

- Probe as left (red, the one hole): 1.54 s, 1.53 s, 1.51 s. Median
  **1.53 s**.
- Green control (the obligation's declaration and hole removed, every
  other term present): 1.43 s, 1.52 s, 1.62 s. Median **1.52 s**. The
  hole costs nothing measurable.
- Empty-module floor, tracked at
  `agents/tasks/LJ-1-393/Floor393.agda`: 0.05 s, 0.05 s, 0.06 s. Median
  **0.05 s**. The mathematics above the floor costs about 1.47 s.
- Witness meter, both obligations, grouped run: both names PROBE_RED,
  exit 42 inside the probe (`SolvedButOpenHoles`), 1.60 s and 1.62 s,
  2 UNRESOLVED of 2.

No run came near the heap cap. No `GHCRTS` was set by this return.

## What the shape resisted

Nothing mathematical in the GREEN half: the fourth-conjunct composition
went through as the brief drew it, the predicted level lift was not
needed, and the corrected assembly is a three-case split with one case
per conjunct of the trichotomy. The resistance was in the TARGET, not the
proof: the stated `amb-init` is false, and no proof effort could have
closed it. One real proof defect was found and fixed during the run: the
`γ ≡ ω` case of `amb-init'` needs `subst` along `sym γ≡ω`, not `γ≡ω`,
because the hypothesis is at `ω` and the goal is at `γ`.

## W2 (DD4)

Everything is written once at a generic carrier: `AmbCard`,
`amb-noinj²` and `amb-init'` quantify over a generic `α : V ℓ` and name
no site (`agents/tasks/LJ-1-393/Probe393.agda:102,119,207`), the square
hypothesis is taken at a generic member `β`, and the module hypothesis is
generic in `α` and `γ`. The refutation terms name `sucV ω` because a
refutation measures the site it names (C-42), and that is the whole
content of a refutation. Any site that later produces `AmbCard`, the
member square law and `⟨ sucV ω ∈ α ⟩` instantiates the corrected half
of this file unchanged.

## W3, the widest unmeasured term

The brief names it: whether `AmbCard` is inhabited at any ordinal above
`ω` in this tree. THIS TASK DOES NOT MEASURE IT, and neither does the
refutation: the refutation measures the ONE site it names (`sucV ω`,
C-42) and says only that `AmbCard` holds VACUOUSLY there, which is
inhabitation of the weakest kind. The probe that measures the real term is
`[LJ-1.394]`'s second term, which asks what the negation of `AmbCard`
delivers. This task adds one measured fact beside it: `Init`'s third
conjunct, taken as a demand on `α`, now carries the measured shape
"closure below `ω` free, closure at `ω` a new hypothesis, closure above
`ω` from `AmbCard`" (`agents/tasks/LJ-1-393/Probe393.agda:207-221`).

## What this task does NOT settle

It does not say `AmbCard` has a producer; it moves the demand from `Init`
to `AmbCard` plus one membership, and `[LJ-1.394]` is where the campaign
learns what that costs. It does not produce the member square law;
`[LJ-1.395]` owns that recursion. It does not say any `α` satisfies all
six hypotheses of `amb-init'`. `amb-init'` is not a closing of the square
law: it is a square law producer only under hypotheses no site has yet
discharged above `ω`.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md:2000-2004`, read: the boundary
  correction this task's refutation recurs, "`Init ω` is UNINHABITED...
  and the truth is that it holds strictly ABOVE". The archive's site
  fails through the second conjunct; mine fails one successor higher,
  through the third.
- `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:985-987`,
  read: the archived design decision this task's binding clause exists to
  stop, "no-injection hypothesis in its square form... since the exclusion
  case refutes an... of the index into the square of a member directly".
  This campaign kept `AmbCard` at `⟪ β ⟫` and paid for it with the member
  square law as a hypothesis, as the brief ruled.
- `archive/dev/TASKS-archived.md:82`, read: the register row for the
  archived delivery this task's premises lean on, "Truncated square law
  at initial ordinals | DELIVERED".
- `dev/ARCHIVE.md` DECLINED: nothing in it bears on this task. The
  registry indexes retired `src/` modules; the square-law chapters are
  live, and greps over the registry for `SquareLaw`, `square law`,
  `initial ordinal` and `rud-route` return no row.
- `archive/dev/DECISIONS-archived.md` DECLINED: nothing in it bears on
  this task. The register holds campaign-configuration rulings, and its
  one `ambient`-shaped row (D32, the Condensation crossing) concerns
  satisfaction transfers on a different boundary, retired by D39 before
  this campaign.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:83-86`, read: "a proof
  that only needs cardinal arithmetic never needs... and the
  untruncation question does not arise in the classical texts". This is
  the grade question inside AmbCard, which forbids an injection GIVEN AS
  DATA while the classical inequality is truncated; the tree's own Init
  definition commits to the data grade, and so does this probe. The
  warning is priced, not ignored.
- `dev/literature/terms-2026-08.md:84-88`, read: the term dossier ties
  this chapter's own construction to its name, "An initial segment of the
  L-tower... the collapse read as an initial segment in the square-law
  argument".
- `dev/literature/geology.md` DECLINED: nothing in it bears on this
  task. The survey is set-theoretic geology (grounds, large cardinals);
  no row concerns cardinal arithmetic at initial ordinals.
- `dev/literature/digest.md` DECLINED: nothing in it bears on this task.
  The digest stratifies the J and S hierarchies; its cardinality lines
  concern GCH-in-L bookkeeping, not the initiality clauses.
- `dev/literature/devlin-II5.md` DECLINED: nothing in it bears on THIS
  task's clause. The file prices the campaign's endpoint rows (hull
  sizes, `P(κ) ⊆ L_{κ⁺}`); `[LJ-1.392]` already quoted its
  cardinal-arithmetic row, and the fourth conjunct and `AmbCard` add no
  question the file answers.

## Tree state

Written here, and nothing else touched:
`agents/tasks/LJ-1-393/Probe393.agda` (rewritten in full),
`agents/tasks/LJ-1-393/lj-1.393-report.md` (this file),
`agents/tasks/LJ-1-393/review-of-amb-init.md` (the stated obstruction;
the task's `no-go-stated` branch keys on a changed file matching
`review-of-*.md`, so this third file is required by the task's own branch
table and is not in the brief's two-name SCOPE),
`agents/tasks/LJ-1-393/Floor393.agda` (the floor module, carried from
the first dispatch, its content unchanged). The program wrote
`agents/tasks/LJ-1-393/runs/accept-1.out` for the first dispatch.
Nothing committed, nothing pushed, no `git add` run.

The gates, run from the repository root with `.venv/bin/python`, all
green over the tree: `lint-agda.py --check`, `lint-prose.py --check`,
`check-glossary.py --check`, `check-fences.py --check`,
`check-probes.py --check` (3505 tracked files),
`weave-i18n.py --check`, `check-spec-surface.py --check`,
`check-closure.py --check closure` (99 masters). `check-unbound-hyp.py`
prints the five frozen baseline findings in `src/` this task did not
touch; no master was changed, so the conjunct is vacuous.
`check-survey-quotes.py LJ-1.393` is clean. `make check` was not run as a
whole; the individual checks above were, per the Boundary.
