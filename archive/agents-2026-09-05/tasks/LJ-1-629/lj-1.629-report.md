# [LJ-1.629] report: the bill's site is NOT an initial ordinal; conjunct 2 is false at a site the bill admits, and conjunct 4 is a wider demand than row 1

## HEAD

head_slot: coder
machine: shared
task: LJ-1.629
obligation: agents/tasks/LJ-1-629/Probe629.agda::site-is-init
verdict: NO-GO, STOP STATED. No term of the probe carries the
obligation's name or its type, because the target is FALSE at a site
the bill's own hypotheses admit. The stop is
`agents/tasks/LJ-1-629/review-of-site-is-init.md`. The probe is GREEN:
`runs/final-12.out` at 2.76 s, 707 MB peak, exit 0, postdating the
last edit; `runs/final-9.out` through `runs/final-11.out` green before
it. No hole, no
postulate, nothing in `src/`, no commit, no push. `git status` shows
only `agents/tasks/LJ-1-629/` as new.

The brief's hoped-for GO, "ingredient (iii) from a theorem already in
src/", is dead, and NOT because an axiom was needed. `via-col-square`
consumes `Init`; `Init` at the bill's site is not derivable from the
bill, and the shortest reason is one line of set theory the bill
forgot to assume: the trophy clause excludes `κ ∈ ω`, it does not
exclude `κ ≡ ω`, and `Init ω` refutes itself. The brief's second
outcome, a NO-GO merging rows 1 and 2, did not materialize either: the
measurement says conjunct 4 needs MORE than row 1 and row 2 together,
not less. Both brief readings were tested by terms, and both were
wrong in different directions; the four-conjunct table below is what
the next brief needs.

This report was a skeleton before any Agda ran and was filled as each
answer landed (C-22).

## W3: THE FOURTH CONJUNCT AT THE SITE, TYPE ONLY, MEASURED FIRST

`agents/tasks/LJ-1-629/runs/W3.agda`, written first and typechecked
ALONE: `runs/w3-2.out` green at 1.47 s, 406 MB peak, exit 0, under the
two-minute cap the brief set. (After a later name-only restructure,
see the ledger, the same file is green again at `runs/w3-3.out`,
1.86 s.) It carries `Init4` (the fourth conjunct
copied letter for letter from `src/L/Ordinal/SquareLaw.lagda.md:696-698`),
the projection row `init-gives-4` tying the copy to the chapter's own
`Init`, `SiteFrame` (the bill's three hypotheses implying `Init4 (fst κ)`),
and `site-is-init→site4` (the shadow is the obligation's). One false
start: `runs/w3-1.out` at exit 42, my import error (`Cubical.Data.Product`
does not exist in this cubical; `_×_` comes from `Base.Prelude`).

## THE FOUR CONJUNCTS

D-10, priced before any proof. All four rows are green terms in
`agents/tasks/LJ-1-629/Probe629.agda`, and the verdict column is the
deliverable.

| # | conjunct (`src/L/Ordinal/SquareLaw.lagda.md:692-698`) | verdict | evidence |
|---|---|---|---|
| 1 | `IsOrd (fst κ)` | GIVEN, verbatim. The bill's first hypothesis IS the conjunct. | `c1-given`, `Probe629.agda:106-109` |
| 2 | `⟨ ω ∈ˢ fst κ ⟩` | MISSING. The bill's clause `⟨ fst κ ∈ˢ ω ⟩ → ⊥` excludes `κ ∈ ω` only. What it needs: `κ ≢ ω`, equivalently respelling the clause to its strictly-above form `⟨ ω ∈ˢ fst κ ⟩`. And it is not just missing: at `κ := ωʟ` it is FALSE, so the obligation is refutable. | `init-ω-false`, `Probe629.agda:121-122`; `target-false`, `:135-137` |
| 3 | successor closure at the site | PAYABLE from the bill GIVEN conjunct 2. Numerals close through `ω ∈ κ` plus transitivity; an infinite member closes because the only escape, `sucV γ ≡ fst κ`, makes the site a coded successor, and `IsCardinalL` refutes the tree's own shift code. | `c3-payable`, `Probe629.agda:224-230` (with `c3-numeral`, `c3-inf`, `c3-triω`) |
| 4 | `⟪ fst κ ⟫` injects into no infinite member's square | MISSING at the stated grain. It is AMBIENT (the brief's reading, confirmed): `IsCardinalL` refutes CODED injections only (`src/L/Cardinal.lagda.md:238-241`). What it needs: ambient `IsCardinal` AT THE SITE (`src/L/BoundedSubset.lagda.md:1046-1047`) PLUS a pairing at every infinite MEMBER of the site (`BandBelow`, the site-fiber shape at each `β ∈ κ`). | `c4-from`, `Probe629.agda:252-266` |

**The falsification, stated exactly.** At `κ := ωʟ` (`fst ωʟ` is `ω`
by definition, `src/L/Axioms/Infinity.lagda.md:69-70`): `IsOrd (fst ωʟ)`
is `ω-ord` and the trophy clause is `∈-irrefl ω`, both green terms
(`Probe629.agda:124-128`). `Init (fst ωʟ)` forces `⟨ ω ∈ˢ ω ⟩`, which
`∈-irrefl` (`src/V/Hierarchy.lagda.md:155`) refutes. So
`target-false : IsCardinalL ωʟ → SiteIsInit → Empty.⊥` is green. The
one hypothesis of the falsifier I did not build is `IsCardinalL ωʟ`,
and it is TRUE: a code at a member `δ ∈ ω` reads back (`readL`,
`src/L/CantorBernstein.lagda.md:33-38`) to an ambient injection
`⟪ω⟫ ↪ ⟪δ⟫` with `δ ≡ # n` (`ω-mem→numeral`,
`src/L/Ordinal/SquareLaw.lagda.md:539`), and the tree's pigeonhole
`no-inj-finite` (`src/L/Ordinal/SquareLaw.lagda.md:604-660`) is built
to refute that shape. Building it is a self-contained miniature,
priced at about 60 to 100 lines: the extension of an injection
`⟪ω⟫ ↪ ⟪#n⟫` to `⟪sucV ω⟫ ↪ ⟪#n⟫ × ⟪#n⟫` so that `no-inj-finite`
applies at `α := sucV ω`, plus the `n = 0` case through a resident of
`⟪ω⟫` (`fiber ω (#∈ω 0) .fst`, `src/V/Presentation.lagda.md:34`). No
next brief should pay for it unless the stop is contested.

**Prior evidence agrees, and was re-measured, not transferred.**
`archive/dev/LJ-dispatch-index.md:192` (`[LJ-1.116]`): "Init is false
at omega and at successors". The omega half is exactly conjunct 2's
failure, re-measured here AT THE BILL'S SITE as a term (a measured
cure does not transfer by analogy; neither does a measured falsehood,
so it was re-run). The "successors" half is about successor ORDINALS
as sites and does not bite at an infinite-cardinal site: conjunct 3's
row proves closure there.

**Conjunct 4's truth, priced separately from its supply.** Classically
the conjunct holds at every infinite cardinal site (`|β × β| = |β|`
for `β ≥ ω`, the arithmetic `dev/literature/devlin-II5.md:413` pins
from the primary source). The tree's supply, measured by `c4-from`,
needs the ambient cardinal at the site and the pairing at every
infinite member. The second ingredient is the BAND below the site, the
very object `[LJ-1.617]` measured the bill does not otherwise need at
site grain; the first is the internal-to-ambient direction whose only
green row runs the other way (`ambient→internal`,
`agents/tasks/LJ-1-550/Probe550.agda:375-378`).

## IS (iii) ROW 1

NO. Ingredient (iii) and row 1 are both ambient-cardinality demands,
but they are not the same demand, and the campaign does NOT hold one
row where it thought it held two. Row 1
(`agents/tasks/LJ-1-550/Probe550.agda:301-302`) asks ambient
cardinality at the SUCCESSOR `δ` of each internal cardinal, which is
the bridge's own spend (`member-in-stage`, `Probe550.agda:257-259`,
applied at `:355`); conjunct 4 needs ambient cardinality AT THE SITE
`κ` itself, an instance row 1 never covers at `ω` or at any limit
cardinal above it, because nobody's successor cardinal is `ω`, PLUS
the band pairing below the site. The green row `ambient-all→row1`
(`Probe629.agda:282-284`) measures that row 1 is a proper weaken of
ambient cardinality at every internal cardinal, and `route`
(`Probe629.agda:289-294`) measures that the payoff the brief priced,
`sq (fst κ)` from `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`), is real exactly when a
premise the bill does not give holds. Where the Init route could run
at all, it would cost MORE than rows 1 and 2 together.

## THE FLOOR, THE CAPS, THE RUN LEDGER

Caliber on every run: the program's `GHCRTS=[-A64m -I0 -M2g]`, read
from the pane and recorded in every `.out`. I did not set it. One
Agda process at a time. Caps, which I set and report: 120 s for the
alone W3 run, 300 s for every other run. No run reached a cap.

**ONE HEAP WALL, ROUTED AROUND IN THE SAME DISPATCH, per the owner's
ruling of 2026-08-23.** The first shape of conjunct 3's row, one term
with two `with` abstractions inside nested `where` closures, died at
the cap: `runs/final-5.out`, exit 251, 56.29 s, 2436 MB peak. The
restructure was measured, not guessed: the pieces alone were green
(`runs/bisect-1.out`, 2.81 s), so the wall was the shape. Two changes
cured it at the same caliber: trichotomy values became ARGUMENTS of
plain case functions instead of `with` scrutinees, and every
`mem-ord` application passes the implicit `{A}` explicitly, the
tree's own idiom (`src/L/Hierarchy.lagda.md:171`), because leaving it
implicit left `isTransV` metas unsolved (`runs/bisect-5.out` isolated
it; `runs/bisect-7.out` confirmed the cure; `runs/final-9.out` green
whole). The same code was never rerun unchanged.

| run | what | exit | price |
|---|---|---|---|
| `runs/w3-1.out` | my import error (`Cubical.Data.Product` absent) | 42 | 0.93 s |
| `runs/w3-2.out` | W3 ALONE, green | 0 | 1.47 s, 406 MB |
| `runs/floor-1.out` | my scope error (missing `import` before `module W3 =`) | 42 | 3.02 s |
| `runs/floor-2.out` | my projection slip in `init-ω-false` | 42 | 2.74 s |
| `runs/floor-3.out` | my over-application in `ambient-all→row1` | 42 | 2.77 s |
| `runs/floor-4.out` | THE FLOOR: frame plus every section but conjunct 3's row | 0 | 2.73 s, 769 MB |
| `runs/final-5.out` | HEAP WALL: conjunct 3 in the `with`-in-`where` shape | 251 | 56.29 s, 2436 MB |
| `runs/bisect-1.out` | `c3-numeral` + `c3-inf` alone, green | 0 | 2.81 s |
| `runs/final-6.out` | my parse slip (raw `_∈_` not imported; switched to `∈ˢ`) | 42 | 2.67 s |
| `runs/final-7.out` | my `subst` direction slip at `γ ≡ ω` | 42 | 2.71 s |
| `runs/final-8.out` | unsolved metas: `mem-ord`'s implicit | 42 | 2.97 s |
| `runs/bisect-2.out` | forward reference slip of mine | 42 | 2.66 s |
| `runs/bisect-3.out` | my reorder script was a no-op | 42 | 2.80 s |
| `runs/bisect-4.out` | same metas, split file | 42 | 3.04 s |
| `runs/bisect-5.out` | `runs/Bisect.agda` isolates the meta to `mem-ord`/`ord-tri` rows | 42 | 1.43 s |
| `runs/bisect-6.out` | my pattern-binder slip in the bisect file | 42 | 1.47 s |
| `runs/bisect-7.out` | `{A = fst κ}` explicit: all ingredients green | 0 | 1.51 s |
| `runs/final-9.out` | the whole probe, green | 0 | 2.74 s, 707 MB |
| `runs/final-10.out` | green after comment-only edits | 0 | 2.99 s, 707 MB |
| `runs/w3-3.out` | W3 alone again, green, after the name-only rename | 0 | 1.86 s |
| `runs/final-11.out` | green after the name-only rename of the W3 tie row | 0 | 2.83 s, 707 MB |
| `runs/final-12.out` | green, postdating the last edit (the probe header's caliber note corrected) | 0 | 2.76 s, 707 MB |

Sizes: the probe is 292 lines, of which the conjunct rows are 224-230
(conjunct 3, the largest, at about 70 lines with its three case
functions), 106-109, 121-137 and 252-266. W3 is 92 lines. The brief
estimated about 150 probe lines with about 35 for the obligation; the
estimate priced the conjunct rows well and did not price the
falsification and comparison rows, which the stop path needs.
Comparables are of SHAPE only.

Gates run individually: `scripts/gate/lint-agda.py --check` exit 0;
`scripts/gate/check-probes.py --check` clean; `lint-prose.py --check`
exit 0 on this report and on the stop file; `grep` for `postulate`,
`TERMINATING` and `{!` over the probe and W3 returns nothing at code
level; no em dash in any file of this scope. `make check` not run: it
is the commit gate and nothing here commits. The ratio bar cannot
fire: the write scope carries no `.lagda.md` master, so the in-fence
count is 0.

## WHAT THE NEXT BRIEF NEEDS

1. **The falsifying site is one hypothesis wide.** If the bill respells
   its trophy clause from `⟨ fst κ ∈ˢ ω ⟩ → ⊥` to `⟨ ω ∈ˢ fst κ ⟩`
   (strictly above `ω`, which is also what the SquareLaw chapter's own
   prose means by initial: it "contains `ω` strictly"), the
   falsification disappears and conjuncts 1, 2 and 3 all come from the
   bill by green rows. That is a bill edit, and it is the
   mathematician's, not mine. The respelled bill would make the site
   `ω`-strictly-above and the only open row would be conjunct 4.
2. **Conjunct 4 is the whole remaining distance, and it is wider than
   the two rows it was hoped to merge.** To pay the site fiber through
   `Init` the campaign would need ambient cardinality at EVERY
   internal cardinal (row 1 covers only successors: `ω` and every
   limit cardinal are uncovered) plus the band pairing below every
   site (row 2's object at every member, which `[LJ-1.617]` measured
   the bill does not otherwise need). If the owner wants (iii) closed
   by construction rather than through `Init`, the honest comparables
   remain `[LJ-1.618]`'s site-level build and its residue.
3. **`IsCardinalL ωʟ` is priced and unbuilt.** It is the one fact the
   falsification borrows as a hypothesis. If any critic disputes the
   stop's truth (not its proof), the 60-to-100-line miniature named
   above makes `target-false` unconditional. Nobody should build it
   otherwise.
4. **What the shape resisted.** The `with`-in-nested-`where` shape
   walled at 2.4 GB and the case-function shape is green at 707 MB with
   the same mathematics; and `mem-ord`'s implicit `{A}` must be given
   explicitly everywhere (the tree's own idiom, `src/L/Hierarchy.lagda.md:171`).
   Both facts are recorded in the probe's shape note. What I had to
   weaken: nothing; every row is stated at the bill's own grain. What
   is not closed: the obligation itself, deliberately, by the stop.

## PREMISES CHECKED

- Premise 1 HOLDS: `Init` is four conjuncts at
  `src/L/Ordinal/SquareLaw.lagda.md:692-698`.
- Premise 2 HOLDS: `via-col-square : (α : S) → Init α → sq α` at
  `:960-961`.
- Premise 3 HOLDS WITH AN OFFSET: the cited `:85` is the section head
  `## THE SITE GRAIN IS CLOSED`; the initial-ordinals ascription it
  heads is at `agents/tasks/LJ-1-623/review-of-site-fiber.md:86-92`
  with `site-at-init` at `Probe623.agda:200-201`.
- Premise 4 HOLDS WITH A FILENAME OFFSET: the cited
  `agents/tasks/LJ-1-627/LJ-1.627.md` does not exist; the file is
  `agents/tasks/LJ-1-627/lj-1.627-report.md`, read and used.
- Premise 5 HOLDS WITH AN OFFSET: the three hypotheses are at
  `agents/tasks/LJ-1-589/Probe589.agda:245-247`; `:243` is the
  comment line above them.
- Premise 6 HOLDS: `InjCode` at `src/L/Cardinal.lagda.md:230-235`,
  `IsCardinalL` at `:238-241`.
- Premise 7 HOLDS: `AmbientCardAtSucc` at
  `agents/tasks/LJ-1-550/Probe550.agda:301-302`.
- Premise 8 HOLDS: the five-row bill at
  `agents/tasks/LJ-1-564/Probe564.agda:455-464`.
- Premise 9 HOLDS WITH AN OFFSET: the cited `:1388` is inside the
  `BoundedSubsetAt` telescope, which opens at
  `src/L/BoundedSubset.lagda.md:1386`; the `sq` parameter is at
  `:1391-1394`.
- Premise 10 HOLDS: `[LJ-1.617]`'s report, read and used.
- Premise 11 HAS A DEFECT: no `## R-42` heading exists in
  `dev/LESSONS.md` (the last R-numbered entry is R-41 at `:4762`), and
  the cited `dev/LESSONS.md:4404` is the `Related:` line of the
  sweep-filter entry. This task restates no spelling, so nothing here
  rests on it; the next brief that names R-42 should get a corrected
  basis.
- Premise 12 HOLDS: `AGENTS.md:45`.
- Premise 13 HOLDS: `AGENTS.md:74-75`.

## W2 AND W4

**W2.** The conjunct rows are written at generic carriers
(`c3-numeral`, `c3-inf`, `c4-from` are stated for an arbitrary site
`κ` with the bill's own hypotheses, and `BandBelow` at an arbitrary
ambient `α`), so the same rows serve any future site. Nothing landed
in `src/`, so no fixed-form chapter was written and no deadline
conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`. The ideal form of this
measurement written fresh today is the probe as it stands; I did not
pay for a worse shape first and then compare, except in the one place
the comparison is itself the finding (the walled `with` shape versus
the green case-function shape, both on the record under `runs/`).

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:192`: "| LJ-1.116 | At which alpha
  does Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is
  every infinite ordinal below alpha; the site is omega. Init is false
  at omega and at successors |". The omega half of that row is
  conjunct 2's failure; this task re-measured it at the bill's site as
  the term `init-ω-false` instead of transferring it.
- **`archive/dev/JOURNAL.md` DECLINED.** `archive/dev/JOURNAL.md:1`:
  "# ARCHIVED 2026-08-20". A retired journal; the facts this task used
  live in the live task directories and the dispatch index above.
- **`archive/dev/JOURNAL-archived.md` DECLINED.**
  `archive/dev/JOURNAL-archived.md:1`: "# Archived journal: the
  retired route". The retired route's journal measures nothing about
  `Init` at the bill's site.
- **`archive/dev/DD-archived.md` DECLINED.**
  `archive/dev/DD-archived.md:1`: "# THE `DD` RULING SERIES, archived
  in full 2026-08-18". The rulings that bind this task were already in
  the standing instructions; no decision history was needed.
- **`dev/ARCHIVE.md` DECLINED.** `dev/ARCHIVE.md:1`: "# ARCHIVE.md:
  the archive registry". No module was retired by this task, so the
  registry was not used.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ AND USED.**
  `dev/literature/devlin-II5.md:413`: "|L_α| = |α| for α ≥ ω
  (`dev2.txt:117`, `dev2.txt:200-240`) is consumed at". This is the
  classical arithmetic behind conjunct 4's TRUTH (the square of an
  infinite ordinal carries its index): it is why the conjunct is true
  at every infinite cardinal site while its SUPPLY, measured by
  `c4-from`, still costs the ambient cardinal at the site plus the
  band below it.
- **`dev/literature/truncation-and-selection.md` DECLINED.**
  `dev/literature/truncation-and-selection.md:1`: "# Truncation and
  selection: how the two literatures pick a witness". No truncation or
  witness-selection question arises in this task's rows; the code
  consumed is `shift-coded`, an honest untruncated production.
- **`dev/literature/terms-2026-08.md` DECLINED.**
  `dev/literature/terms-2026-08.md:1`: "# The terminology dossier:
  fourteen renderings for the owner's ruling". No terminology question
  arose; this task used the tree's own names.
- **`dev/literature/digest.md` DECLINED.**
  `dev/literature/digest.md:1`: "# Digest: the orthodox form of the
  rud route, pinned from the collected literature". No rud-route
  question arose; the probe prices one `Init` implication.
- **`dev/literature/geology.md` DECLINED.**
  `dev/literature/geology.md:1`: "# Geology dossier: set-theoretic
  geology sources and the five questions". No layering or inner-model
  question arose.
