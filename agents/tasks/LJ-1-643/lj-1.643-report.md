# [LJ-1.643] DO ANY TERMS IN THE TREE PRODUCE AMBIENT CARDINALITY?

## HEAD

GO. The obligation `amb-card-supply`
(agents/tasks/LJ-1-643/Probe643.agda:126) is typechecked with the final
file in place. The census found **three** producers of ambient
`IsCardinal` in the tree, all in `src/L/CardinalAbove.lagda.md`, and the
truncated producer's one external hypothesis is inhabited in the tree
by `noInjOrd`.
This is the return of the coder re-dispatch. The first dispatch built
the probe and this report; three adversarial reviews upheld the census
(`review-of-LJ-1-643-1.md`, `review-of-LJ-1-643-2.md`,
`review-of-LJ-1-643-3.md`); the defects that kept the task open sat in
THIS FILE and in the run set, never in the mathematics. This dispatch
answers every survey path the brief injects (the seven paths
`runs/accept-5.out` names in its lint_detail), moves the deliberately
red measurement inputs out of the Agda run set (THE RUN SET AND THE
ROUTING FACT, below), and re-runs the probe green (`runs/final-4.out`).
The W3 answer: the truncated producer's hypotheses are all dischargeable
at `[LJ-1.640]`'s bill site, so it runs cold there — but what it yields
is a truncated witness at a site the producer chose, not `IsCardinal` at
the bill's named site.

- the final run: agents/tasks/LJ-1-643/runs/final-4.out, `EXIT=0`,
  3.92 s, 763 MB, started 2026-08-27T05:12:45Z, this dispatch's own
  run of the unchanged probe; the first dispatch's finals exited 0 too
  (runs/final-1.out, 2.77 s; runs/final-2.out, 2.70 s; runs/final-3.out,
  3.14 s, 704 MB)
- the floor, measured with a hole before the bodies landed:
  agents/tasks/LJ-1-643/runs/floor-11.out, 3.10 s, 704 MB, the only
  failures the four standing interaction holes
- caliber: `-A64m -I0 -M2g`, which the program set on this pane
  (`GHCRTS`); I did not set it, and never raised it
- one Agda process at a time; no parallelism anywhere in this dispatch
- no postulate, no hole, no hole-escape in the final file; nothing lands
  in `src/`; no commit, no push
- ledger ratio bar: the probe is a `.agda` file, not a `.lagda.md`
  master, so the raw-count ratio bar cannot fire on it
- gates run from the tree root while working, this dispatch, all
  clean: `check-probes` (9739 tracked files, no probe outside
  `agents/tasks/`, no generated file), `check-fences` (103 masters),
  `lint-agda`, `lint-prose`, `check-glossary`, `weave-i18n --check`,
  `check-spec-surface --check`, `check-closure --check closure`, and
  the survey duty `check-survey-quotes.py LJ-1.643` (0 defects, 0 notes)

## THE CENSUS

The grep: `grep -rn IsCardinal` matches **29 lines of 6 files**
(2026-08-23, re-run unchanged by this dispatch on 2026-08-27: 30 name
occurrences, one line carries the name twice); of those, **12 lines in 3 files** carry the bare name
(not the in-L variant `IsCardinalL`):

| file | lines | bare / L-variant |
|---|---|---|
| src/L/CardinalAbove.lagda.md | 13 | 5 / 8 |
| src/L/BoundedSubset.lagda.md | 4 | 4 / 0 |
| src/L/StageBound.lagda.md | 3 | 3 / 0 |
| src/L/Cardinal.lagda.md | 3 | 0 / 3 |
| src/L/GCH.lagda.md | 5 | 0 / 5 |
| src/L/SquareLawClosed.lagda.md | 1 | 0 / 1 |

Of the 12 bare occurrences: one definition (two lines), two imports, **three
producers** (the census), and five consumers (a hypothesis or an
argument, never a conclusion). The in-L variant `IsCardinalL` is a
different predicate (Cardinal.lagda.md:217) and is out of scope.

### THE THREE PRODUCERS

**1. `θ-card`, src/L/CardinalAbove.lagda.md:160.**
Type, measured as `Row1` (agents/tasks/LJ-1-643/Probe643.agda:98):

```
(a β : SV.S) → IsOrd β → ⟨ θ ∈ˢ β ⟩ → IsCardinal θ
```

where `θ` is the separation of `β` at the members that inject into `a`,
built by `module Sep` itself (CardinalAbove.lagda.md:116, 123-124).
What it consumes: a bound ordinal `β` and the one fact that the
separation site `θ` is a member of `β`; the body spends exactly that
witness (CardinalAbove.lagda.md:161-162). What it produces: `IsCardinal` **only at
the site it built itself**. It cannot be pointed at a site handed in
from outside. [LJ-1.640]'s probe comment counted this one alone
(agents/tasks/LJ-1-640/Probe640.agda:161: "PRODUCERS of `IsCardinal`
in src/: ONE. `θ-card`"), and its C-42 sweep then named the rest
(agents/tasks/LJ-1-640/lj-1.640-report.md:238-246); the census below
re-measures the full count at this dispatch's own site: three
producers, the two next rows beside this one.

**2. `cardAboveAt`, src/L/CardinalAbove.lagda.md:207.**
Consumes an ordinal `a` and **one ordinal `γ` that does not inject into
it** — the untruncated Hartogs fact. Produces a Σ: a CHOSEN site `θ`
above `a` with its `IsOrd θ` and its `IsCardinal θ`, untruncated
(measured as `Row2`, Probe643.agda:107).

**3. `ambientCardAbove`, src/L/CardinalAbove.lagda.md:220.**
Consumes `NoInjOrd` — the HARTOGS FACT as a stand-alone supplier,
defined at src/L/CardinalAbove.lagda.md:185 — and the ordinal `a`.
Produces the same witnessed site, truncated (measured as `Row3`,
Probe643.agda:117). The tree inhabits that supplier itself:
`noInjOrd : NoInjOrd` (src/L/CardinalAbove.lagda.md:575), built in the
Hartogs section 6 together with `CardAboveL`
(src/L/CardinalAbove.lagda.md:585). So row 3's ONE external
hypothesis is discharged in the tree.

### THE CONSUMERS

Hypotheses, all of them: the `BoundedSubsetAt` input
(src/L/BoundedSubset.lagda.md:1386, the `cardκ` argument of `[LJ-1.637]`
and `[LJ-1.640]`), the same argument again at the `BSA634` module
(src/L/BoundedSubset.lagda.md:1746), the stage-bound inputs
(src/L/StageBound.lagda.md:65, 94), the local `build` input of the
`NoInjOrd` route (src/L/CardinalAbove.lagda.md:231), and the two
imports (src/L/CardinalAbove.lagda.md:31, src/L/StageBound.lagda.md:16).
The definition itself is two lines
(src/L/BoundedSubset.lagda.md:1046-1047). No other file in the tree
concludes `IsCardinal` at any site.

## THE TERM

`amb-card-supply : CensusEmpty ⊎ ProducerCensus`
(agents/tasks/LJ-1-643/Probe643.agda:126). It takes the CENSUS branch:
the right injection of the product of the three row types, whose bodies
ARE the three producers imported from src/
(Probe643.agda:127-136).

Two measurements reshaped this file, both under the same 2 GB cap, both
recorded as their own runs (2026-08-23 ruling: a heap wall is a signal
to restructure in the same dispatch, and a measured cure does not
transfer by analogy, so each shape was re-measured here):

1. **The module in type position.** This Agda build takes the
   `module Sep` from the `using` import at module-BINDING position
   (`module T = Sep a β oβ`) but refuses the `Sep a β oβ .θ` sugar in
   type position (runs/t1-1.out: `NotInScope: Sep` in a type; runs/t1-2.out
   is green with the same application at module-BINDING position). The
   `sep-site` helper
   (Probe643.agda:88) names the separation site as a value; runs/t3-1.out
   is green at 3.01 s on that shape.
2. **The record in the heap.** A `record` FIELD whose type concludes
   `IsCardinal` exhausts the 2 GB wide-tier heap at 22 s in this build;
   the minimal walling shape is one field `f : (β : SV.S) →
   IsCardinal β` (runs/t10-1.out; the same wall with the `θ-card`
   field at runs/t6-1.out; a plain field type does not wall,
   runs/t7-1.out; a field concluding only in a membership hProp does
   not wall, runs/t11-2.out). The identical type at top level and as a
   product factor does not wall (runs/t3-1.out, runs/t12-1.out: 3.03 s).
   The census is therefore a PRODUCT of the three row types
   (`ProducerCensus = Row1 × Row2 × Row3`, Probe643.agda:123), not a
   record. This is an engine quirk of this Agda build against these
   imports, not a property of the file's meaning; the rows are named
   `Row1`, `Row2`, `Row3` and identified in comments.

Both walls died on restructuring, and the floor of the final shape
measures 3.10 s (runs/floor-11.out), so the wall does not bind this
probe.

**The none branch.** `CensusEmpty` is bare `Unit*`
(Probe643.agda:81). "The tree has no producer" is a fact about the tree
as text, not a mathematical statement: no type can say "no source file
contains a term of this shape" without naming the files, and the
mathematical cousin (`∀ κ → IsCardinal κ → ⊥`) is FALSE, since the tree
does contain producers. The branch records that the census ran and
found nothing; nothing more can be checked inside the language, and the
census in fact found three.

## W3

Bill's site: `κ : SL.S` with `IsOrd (fst κ)`, owed `IsCardinal (fst κ)`
(agents/tasks/LJ-1-640/Probe640.agda:182-184, `least-site⟺amb`: the
`IsCardinal (fst κ) → LeastSite κ` direction consumes it and it is
undischarged at that site).

**Are the truncated producer's own hypotheses dischargeable there?
Yes, all of them.** `ambientCardAbove` needs `NoInjOrd` and an ordinal:
`noInjOrd` comes from the tree (src/L/CardinalAbove.lagda.md:575), and
`a := fst κ` with its ordinality is the bill's own hypothesis. The
application is typechecked in the probe:
`bill-site-truncated-supply` (Probe643.agda:154), green in the final
run. So at the bill's site the tree already supplies, COLD,
`∥ Σ[ θ ] (IsOrd θ × IsCardinal θ × ⟨ fst κ ∈ˢ θ ⟩) ∥₁`.

**What that buys and what it does not.** It yields a truncated
witness at a site `θ` the producer CHOSE, above `fst κ`. The crossing
the bill still wants — from that fresh `θ` to the named site `fst κ`,
untruncated — is not in the tree: row 2 is untruncated but needs the
untruncated Hartogs fact, and row 1's `θ` is the site `Sep` builds from
`β`, which it cannot be pointed at the bill's `κ`. Premise 2 (no site
above the grounds site) is not a hypothesis of row 3 and is untouched.
The gap [LJ-1.640] prices to a single named crossing
(agents/tasks/LJ-1-640/lj-1.640-report.md:46-47) is precisely the
crossing this truncated witness leaves behind: named, untruncated,
at the bill's site. That report's C-42 sweep (lines 238-246) reached
the same producer count in prose; this dispatch types it, imports the
three rows into one obligation, and typechecks the truncated supply at
the bill site as the measured form of the claim.

**Where this leaves the premise.** [LJ-1.640]'s premise 4 leans on the
measurement [LJ-1.533] made in 2026-08-22 (agents/tasks/LJ-1-533/
lj-1.533-report.md:76: "Code buys ambient. Ambient buys nothing.").
That sentence is the COUNT conclusion of this dispatch's question, and
the count is 3, all three of whose value-uses produce at fresh sites.
The premise survives this survey unchanged: the tree's ambient
production is real but at fresh sites, and `[LJ-1.640]`'s own C-42
sweep says so (agents/tasks/LJ-1-640/lj-1.640-report.md:238-246).

## THE RUN SET AND THE ROUTING FACT

The first dispatch left thirteen measurement inputs in `runs/` as
`.agda` files: `Floor.agda`, the four-hole floor (`runs/floor-11.out`
records its rc 42), and `T1` to `T12`, the shape experiments. Five of
those wall at the 2 GB cap by design (`runs/t5-1.out`, `runs/t6-1.out`,
`runs/t8-1.out`, `runs/t9-1.out`, `runs/t10-1.out`); the rest are red
with unsolved metas or a parse error. The acceptance runner's conjunct
1 runs EVERY `.agda` file of the changed set under the task home
(`scripts/pod/facts.py:521-523`, case 2), so the first acceptance ran
`runs/Floor.agda` as a verification target and took its designed rc 42
as the task's exit (`runs/accept-1.out:17`). Those files are evidence,
not obligations: no run of them can be green, because red is what they
measure. This dispatch renames each to `<name>.agda.txt`, content
unchanged, so the one `.agda` file the task owns, the green probe, is
the only verification target. The `.out` records beside them still
name the paths they ran; the sixteen `runs/Floor.agda` cites inside the
three review companions (for example `review-of-LJ-1-643-3.md`)
resolve to `runs/Floor.agda.txt` after this rename.

The routing fact. The obligation resolves today: the witness meter
over this brief reports `0 UNRESOLVED of 1` (`runs/witness-1.out`).
The program measures `obl_before` at dispatch, over the worktree
(`scripts/pod/pod.py:5362`), so THIS dispatch started with the
obligation already discharged, and its acceptance reads
`obligations_delta` 0. Row `go`, the only row whose action is `done`,
keys on `obligations_delta_max = -1` (`LJ-1.643.md:84`); row
`accept-failed` keys on the same bound (`LJ-1.643.md:107`); neither
can match a return from this dispatch. Row `stop-stated` is closed to
every return from this worktree for a second reason: the changed set
is the whole untracked task directory (`git status` reads
`?? agents/tasks/LJ-1-643/`), it carries the three review companions
the critic dispatches wrote, and `stop-stated` demands
`changed_files_none` of `review-of-LJ-*-*.md` (`LJ-1.643.md:97`) while
the row matches on the full changed set (`scripts/pod/table.py:572`).
A green return from this dispatch therefore parks as no-match with all
six conjuncts held. That is the honest end state for the program to
see: the work stands, the record is clean, and the row set cannot close
a task whose obligation an earlier attempt of the same task discharged
before this one started. The owner's cure is a commit of the inherited
companions or a routing amendment, not another coder pass.

## MEASURED GROUND

- floor with holes, final shape: runs/floor-11.out, 3.10 s, 704 MB,
  four unsolved holes only
- floor bisect (record-wall): runs/t6-1.out and runs/t10-1.out, 22.2 s
  and 22.5 s to the 2 GB wall; the top-level and product shapes green at
  3.0 s, 580-590 MB (runs/t3-1.out, runs/t4-1.out, runs/t12-1.out)
- finals: runs/final-1.out, EXIT=0, 2.77 s; runs/final-3.out, EXIT=0,
  3.14 s, 704 MB, after the last comment change to the probe; this
  dispatch: runs/final-4.out, EXIT=0, 3.92 s, 763 MB, probe unchanged
- the witness meter over the brief, this dispatch: runs/witness-1.out,
  `0 UNRESOLVED of 1`, pass at 3.80 s
- probes stay probe-sized: the finals span 2.70 s to 3.92 s against the
  3.10 s floor; the rule, final ≤ 2× floor, holds (3.92 ≤ 6.20)

## ARCHIVE USED

The five candidates the task's ARCHIVE line names, each answered:

- READ, USED. `archive/dev/LJ-dispatch-index.md:165` says "Nothing in
  the tree proves any set is a cardinal", and
  `archive/dev/LJ-dispatch-index.md:166` says "Two hits in src: the
  definition and the hypothesis." That is the earlier survey of exactly
  this question, and its count predates the tree this census reads: the
  re-measure above finds 12 bare-name lines with three producers, and
  `git log -S` puts both `θ-card` and `noInjOrd` into
  `src/L/CardinalAbove.lagda.md` at commit 3c229d2d (2026-08-24 22:52).
  C-42 makes the re-measure the correct action, and the audit's
  operative claim, that no site in the tree CONCLUDES `IsCardinal` at a
  handed-in site, survives it: all three producers conclude at a site
  they choose themselves.
- `archive/dev/JOURNAL-archived.md` - DECLINED, not used.
  `archive/dev/JOURNAL-archived.md:1` reads "# Archived journal: the
  retired route": the retired route's episode record is not where
  `IsCardinal` is produced or demanded, and the census reads the live
  tree only. Not read beyond the header.
- `archive/dev/JOURNAL.md` - DECLINED, not used.
  `archive/dev/JOURNAL.md:1-2` reads "# ARCHIVED 2026-08-20 The
  per-episode journal is retired.": a grep of the file for `IsCardinal`
  returns no hit, so it holds no producer census.
- `dev/ARCHIVE.md` - DECLINED, not used. `dev/ARCHIVE.md:1` reads
  "# ARCHIVE.md: the archive registry": it indexes retired modules, and
  no retired module is on any producer's import path, since the three
  rows import live masters only. Not read beyond the header.
- READ, USED. `archive/dev/DD-archived.md:35` is the DD25 row, the rule
  the three review companions applied to this task's chain, and it
  opens "A NEGATIVE RETURN IS ADVERSARIALLY REVIEWED AT MAXIMUM
  EFFORT". The four questions at the same line are the lens that turned
  the first dispatch's implied NO-GO back into the upheld GO this
  report returns.

## LITERATURE USED

The five candidates the task's LITERATURE line names, each answered;
one read, four declined:

- READ, USED for one sentence. `dev/literature/devlin-II5.md:147`
  quotes Devlin 5.5: "5.5 Lemma. Assume V = L. Let κ be a cardinal. If
  x is a bounded subset of". Cardinality there is a HYPOTHESIS of the
  lemma, the consumer side: the dossier supplies no producer, which
  agrees with this census, whose three producers are the tree's own
  Hartogs terms and not a Devlin counting step.
- `dev/literature/truncation-and-selection.md` - DECLINED, not used. It
  is the dossier of how the two literatures pick a witness from a
  truncated family; this census selects no witness, and rows 2 and 3
  choose their site by Hartogs, so the dossier's question is not this
  task's question.
- `dev/literature/digest.md` - DECLINED, not used. It pins the orthodox
  form of the rud route; nothing in it bears on whether the tree
  concludes `IsCardinal` at a site.
- `dev/literature/terms-2026-08.md` - DECLINED, not used. It is the
  terminology dossier for the owner's translation ruling; the census is
  a grep-and-typecheck fact of the tree and needs no rendering.
- `dev/literature/geology.md` - DECLINED, not used. It pins
  set-theoretic geology sources; geology is not on this route.
