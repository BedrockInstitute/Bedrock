# LJ-1.531 report: the replacement rank is injective on the members of `a`

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `rank-at′-inj` is built, with no holes.**
`agents/tasks/LJ-1-531/Probe531.agda:185-203`, exit 0, caliber
`-A64m -I0 -M8g` taken from the pane, one Agda process at a time.
`runs/full-1.out` to `runs/full-3.out` and `runs/full-final.out`.

    rank-at′-inj :
        (a : S) (oa : IsOrd (fst a)) (m m' : S)
        (mx : ⟨ fst m ∈ fst a ⟩) (mx' : ⟨ fst m' ∈ fst a ⟩)
      → fst (P521.rank-at′ a oa m mx) ≡ fst (P521.rank-at′ a oa m' mx')
      → fst m ≡ fst m'

**THE TYPE IS PINNED IN A SEPARATE MODULE AND CANNOT HAVE DRIFTED FROM THE
BRIEF.** `runs/Pin.agda:30-38` transcribes the brief's type as `Obligation`,
with one change and no other (`rank-at′` is qualified `P521.`, which is its
name outside `[LJ-1.521]`), and inhabits it by `P531.rank-at′-inj` and by
nothing else. Exit 0, `runs/pin-1.out`. This is `[LJ-1.529]`'s
`range-is-fourth-of-InjCode` device (`Probe529.agda:190-191`) turned on the
brief instead of on `InjCode`.

**THE LEMMA IS TRUE. IT IS NOT A REFUTATION.** The brief prefers a refutation
to a failure and names `[LJ-1.497]` as the respectable precedent. Neither
applies here: the extensionality the argument needs is two fields of the
record the rank already runs on, and section D-10 below gives the `file:line`.

**NOTHING IS POSTULATED. NOTHING LANDED IN `src/`. `injAt` IS NOT BUILT.
`domAt` IS NOT TOUCHED. `Bound′` AND `rank-bound′` ARE NOT REBUILT.**
`swo-rank`, the rank `[LJ-1.497]` refuted, inhabits no term of any file of
this task and is named only in one comment saying so (`Probe531.agda:53-54`).

I did not write a `review-of-*.md`, because this is not a stop.

## D-10, BEFORE ANY AGDA

The brief orders the truth question first: "Say at `file:line` whether the
order `swo-rank′` recurses on is extensional in that sense", and orders a
refutation if it is not.

**IT IS EXTENSIONAL, AND THE ANSWER IS NOT AT THE ORDINAL SITE. IT IS TWO
FIELDS OF THE `SWO` RECORD.**

1. `P521.swo-rank′` recurses on `SWO._<∙_ w` and on no other datum.
   `Rank′.Pred a` is `Σ[ x ∈ A ] (x <∙ a)`
   (`agents/tasks/LJ-1-521/Probe521.agda:234-235`), and `step` and `go`
   (`:237-244`) read the predecessor type and the inductive hypothesis and
   nothing else.
2. The `SWO` bundle CARRIES trichotomy and irreflexivity as fields:
   `tri∙ : (a b : A) → Tri (a <∙ b) (a ≡ b) (b <∙ a)` and
   `irr∙ : (a : A) → ¬ a <∙ a` (`src/L/WellOrder/Base.lagda.md:104-105`).

**SO THE HYPOTHESIS THE BRIEF PUT AT THE SITE, `(a , oa)`, IS NOT NEEDED TO
STATE THE EXTENSIONALITY AND IS NOT NEEDED TO PROVE IT.** Agreeing
predecessor sets force equality by `tri∙` and `irr∙` alone: if `j <∙ k` then
the backward half makes `j <∙ j`, which `irr∙` refuses, and symmetrically.
That is `preds-distinguish` (`Probe531.agda:103-113`), stated at the generic
carrier as clause W2 asks.

**THE ONE PLACE THIS COULD STILL HAVE DIED, AND IT DID NOT.** The literature
carries a measured refutation of a whole family of injectivity claims:
"Every canonical pairing that reads only the reachable set is symmetric,
hence not injective" (`dev/literature/truncation-and-selection.md:312-313`).
A rank that reads only the predecessor set is a reader of that shape, so the
family had to be checked against this site rather than assumed away. **It
does not cover this site, and the reason is exactly the one that entry
names: the symmetry is BROKEN by a datum the family carries.** `SWO` carries
`tri∙`, which is a symmetry-breaking datum on the carrier, and the rank
inherits it. A rank over the predecessors of an order WITHOUT trichotomy
would fall to that refutation.

## W3, THE WIDEST UNMEASURED TERM

**GO, ON THE FIRST ATTEMPT, AT 0.68 s.** `runs/W3.agda`, exit 0,
`runs/w3-1.out` to `runs/w3-3.out` and `runs/w3-final.out`
(0.68 s, 0.65 s, 0.63 s, 0.67 s real). Written first and typechecked ALONE,
as the brief orders. It imports no probe, names neither `swo-rank′` nor
`rank-at′` nor the site, and is generic in the carrier.

It carries two terms:

- `preds-distinguish` (`runs/W3.agda:42-52`), the brief's named shape with
  "their predecessor sets agree" spelled out as the two implications.
- `mono→inj` (`runs/W3.agda:58-69`), the same two record fields used
  directly: over a strict total well-order, ANY strictly monotone map into
  ANY irreflexive relation is injective.

**THE SECOND IS THE ONE THE OBLIGATION SPENDS, AND WRITING BOTH IS THE
FINDING.** The brief's `preds-distinguish` settles the truth question but is
not on the route: the obligation never has two agreeing predecessor sets in
hand. It has an equality of two RANKS. `mono→inj` is what turns that into
equality of members, and it is the same two fields. **So W3's real answer is
that the extensionality and the injectivity are one fact used twice, not two
facts.**

**ONE CHANGE FROM `runs/W3.agda` TO `Probe531.agda:115-128`, AND IT IS A
LEVEL AND NOT A PROOF.** `mono→inj`'s codomain is generalised in its two
levels, because section 3 instantiates `B := V ℓ`, which lives in
`Type (ℓ-suc ℓ)` and not in `Type ℓ`. W3 measured the shape at `Type ℓ`.

**ESTIMATE AGAINST MEASURED for W3:** the brief said about 25 lines and
under 40 seconds. Measured **31 code lines and 0.68 s**. The line figure is
6 over because the file carries two terms rather than one; the time figure
is 0.68 s against a ceiling of 40 s.

## WHAT THE OBLIGATION ACTUALLY COST

**THE OBLIGATION COSTS ABOUT 0.08 s OF USER TIME ABOVE THE BARE IMPORT.
THE IMPORT IS THE PRICE.** This is measured and not reasoned:
`runs/Baseline.agda` imports `[LJ-1.521]` and defines nothing;
`runs/delta.out` alternates the two, deleting only this task's own `.agdai`
before each run and keeping `LJ-1-521.Probe521.agdai`.

| file | real | user |
|---|---|---|
| `Probe531.agda`, three runs | 1.59 s, 1.29 s, 1.24 s | 1.12 s, 1.14 s, 1.10 s |
| `runs/Baseline.agda`, three runs | 1.18 s, 1.17 s, 1.14 s | 1.03 s, 1.03 s, 1.02 s |
| the delta | about 0.19 s | **about 0.08 s** |

**THE COLD FIGURE IS 4.52 s AND IT IS MOSTLY `[LJ-1.521]`.** `runs/full-1.out`
is this file and `Probe521.agda` both from scratch: 4.52 s real, peak
resident set 681,394,176 bytes. No heap wall, at any point, in any run.

**ZERO FAILED ATTEMPTS.** W3 typechecked on its first run and `Probe531.agda`
typechecked on its first run. There was no bisect, no seal, and no retry.
`runs/full-final.out` is a re-run after a comment-only correction to three
`file:line` citations and changes no term.

### the size

| file | total | code | comment | blank |
|---|---|---|---|---|
| `Probe531.agda` | 203 | 81 | 103 | 19 |
| `runs/W3.agda` | 69 | 31 | 31 | 7 |
| `runs/Pin.agda` | 38 | 20 | 10 | 8 |
| `runs/Coexist.agda` | 97 | 52 | 31 | 14 |
| `runs/Baseline.agda` | 12 | 5 | 3 | 4 |

`Probe531.agda`'s 81 code lines are 1 pragma, 20 of imports and the module
line, then 27 for section 1 (W3 restated), 11 for section 2, 5 for section 3
and **17 for the obligation itself** (`:185-203`).

**ESTIMATE AGAINST MEASURED for the probe.** The brief said about 190 lines,
of which the obligation is about 45 and the rest is the rebuilt carve, rank
and bound. Measured 203 total lines, of which the obligation is **17**.

**THE TOTAL IS RIGHT BY ACCIDENT AND THE PARTS ARE BOTH WRONG, WHICH IS THE
MORE USEFUL NUMBER.** The brief funded 145 lines of rebuilt carve, rank and
bound. **This file rebuilds NONE of them and carries 0 lines of them**: the
obligation does not mention the carve, the graph or the bound, so `Bound′`,
`rank-bound′`, `rank-graph` and `Carve` are all absent. What fills the file
instead is 103 lines of comment, which is about 51 percent of it. The obligation
came in at 38 percent of its estimate.

## THE ONE THING THE SHAPE RESISTED

**MONOTONICITY IS NOT A DELIVERED TERM AT THE SEALED RANK, AND THE ARGUMENT
NEEDED IT.** `[LJ-1.515]` states it as `swo-rank′-mem`
(`agents/tasks/LJ-1-515/Probe515.agda:224-226`), and that statement DOES NOT
REACH. It is about `[LJ-1.515]`'s own `swo-rank′`, which is a different term
from `[LJ-1.521]`'s sealed one, and `[LJ-1.521]` did not rebuild it
(`agents/tasks/LJ-1-521/lj-1.521-report.md:350-352`).

**`[LJ-1.529]` PREDICTED THE DERIVATION AND MARKED IT REASONING. THIS TASK
MEASURED IT AND THE PREDICTION WAS RIGHT, INCLUDING THE CONVERSION.**
`rank-mono` (`Probe531.agda:150-158`) is `P521.rank-mem-in`
(`Probe521.agda:399-402`) at `u := swo-rank′ w j`, with `self∈sucV`
(`src/V/Model.lagda.md:236-237`) supplying the successor membership. The
crossing `[LJ-1.529]` named is real and it is one `∈∈ₛ`: `self∈sucV` speaks
`_∈ˢ_` at `𝒮ᵥ` and `rank-mem-in` wants the library's `_∈ₛ_`. A second `∈∈ₛ`
converts back once, in `∈ₛ-irrefl` (`:147-148`), so that `∈-irrefl`
(`src/V/Hierarchy.lagda.md:155-156`) can be the irreflexivity `mono→inj`
asks for.

**COST: 11 CODE LINES FOR THE WHOLE OF IT, AND NO ADAPTER MODULE.**
`[LJ-1.529]` wrote "It is one lemma, and it is one lemma with a conversion
inside it, not a one-liner." That is exactly right, and the conversion cost
two uses of a delivered iso.

## WHY THE IMPORT OF `[LJ-1.521]` IS NECESSARY HERE, AND IT IS SHARPER THAN `[LJ-1.529]`'s

`[LJ-1.529]` declared this import and gave the whole argument
(`agents/tasks/LJ-1-529/Probe529.agda:16-30`): `bedrock.agda-lib:2` lists
`agents/tasks` as an include root, the tree already carries cross-task probe
imports (`agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29`,
`agents/tasks/LJ-1-224/ProbeGraphSupply.agda:24`), and no rule forbids it.
I do not repeat that argument; I record what is NEW about this site.

**`P521.swo-rank′` IS SEALED, AND THE OBLIGATION'S PROOF NEEDS ONE OF THE
FIVE NAMES THE SEAL EXPORTS.** The `opaque` block is `Probe521.agda:380-402`
and its own comment says "The five names below are the whole interface"
(`:377-378`). The proof needs `rank-mem-in`, the fifth. **There is no route
from outside that seal to the recursion**, so a rebuilt `swo-rank′` would be
a different opaque term, `rank-at′-val` (`:438-442`) would not connect it to
`rank-at′`, and this task would be a rebuild of `Probe521`, priced by
`[LJ-1.521]` at 1176 lines (`lj-1.521-report.md:287`).

**SO THE IMPORT IS NOT AN ECONOMY HERE EITHER. IT IS THE DIFFERENCE BETWEEN
81 CODE LINES AND A REBUILD.**

## WHAT `injAt` NEEDS AFTER THIS

**`injAt` IS NOW A COMPOSITION OF DELIVERED TERMS. I DID NOT BUILD IT, AND I
MEASURED THE REACHABILITY RATHER THAN ASSERTING IT.**

`runs/Coexist.agda` imports `[LJ-1.521]`, `[LJ-1.529]` and `[LJ-1.531]` at
ONE `lem` in ONE module and gives each piece a type ascription, so the
elaborator has to agree that the name resolves at this instantiation. Exit 0,
`runs/coexist-2.out`, 2.37 s. **It builds no new term:** every binding is a
name for something a predecessor delivered.

The pieces, each at `file:line`:

| piece | where | what it gives |
|---|---|---|
| `injAt-in` | `src/L/Coding/Injection.lagda.md:72-75` | the hypothesis to the conjunct's satisfaction |
| `Carve.G` | `agents/tasks/LJ-1-529/Probe529.agda:221-222` | the carve, which is the conjunct's `F` |
| `Carve.read` | `agents/tasks/LJ-1-529/Probe529.agda:239-245` | a pair in the carve is `(m , rank at m)` |
| `Carve.val` | `agents/tasks/LJ-1-529/Probe529.agda:248-251` | `fst y ≡ fst (rank-at′ a oa m mx)` |
| `pr-inj` | `src/V/Coding.lagda.md:178-179` | splits a Kuratowski pair equation both ways |
| `rank-at′-inj` | `agents/tasks/LJ-1-531/Probe531.agda:185-203` | THIS TASK |

**TWO DEFINITIONAL FACTS THAT WOULD OTHERWISE BE REASONING ARE NOW
MEASURED**, by `runs/Coexist.agda:76-97`. `injAt-in` lives in a module over
`(f , γ)` (`src/L/Coding/Injection.lagda.md:50`) and the conjunct is at
`f := zero`, `γ := G ∷ a ∷ []` (`src/L/Cardinal.lagda.md:227`). The
ascription `the-injAt-in` names `injAt-in` at exactly that instantiation and
typechecks, so: `lookup zero (G ∷ a ∷ [])` IS the carve, hence the private
`Holds₀` (`src/L/Coding/Injection.lagda.md:52-53`) IS `P529.Carve.Hold`
(`Probe529.agda:230-231`); and what `injAt-in` returns there IS the
conjunct's satisfaction. **The hypothesis is still an open argument and
nothing in the file supplies it.**

**WHAT REMAINS IS ARITHMETIC ON THOSE PARTS, AND I MARK IT AS REASONING AND
NOT AS MEASUREMENT.** Given `h : Hold x y` and `h' : Hold x' y`, take
`read x y h` and `read x' y h'`. `val` at each gives
`fst y ≡ fst (rank-at′ a oa m mx)` and `fst y ≡ fst (rank-at′ a oa m' mx')`;
their composite feeds `rank-at′-inj` and yields `fst m ≡ fst m'`. `pr-inj`'s
FIRST component at each gives `fst x ≡ fst m` and `fst x' ≡ fst m'`. Three
path compositions close `fst x ≡ fst x'`. **Four delivered terms and three
compositions. No new lemma.**

**ONE THING THE NEXT BRIEF SHOULD NOT BE SURPRISED BY, AND IT IS SMALL.**
`Probe529.Carve` exposes `pr-inj`'s SECOND component as `val`
(`Probe529.agda:248-251`) and does NOT name the first. `[LJ-1.524]` named it
`Carve.arg` (`agents/tasks/LJ-1-524/Probe524.agda:221-222`). So the next
task writes one projection, `pr-inj (read x y h .snd .snd) .fst`, and not a
lemma.

**THE LEG AFTER `injAt` HAS ONE NAMED WALL AND IT IS `domAt`'s CONVERSE.**
I did not touch it, as the brief orders. `[LJ-1.524]` measured that
`domAt-in` (`src/L/Coding/Model.lagda.md:294-296`) asks for the CONVERSE of
`rankFo-adequate′` and that nothing in the tree supplies it
(`agents/tasks/LJ-1-524/lj-1.524-report.md:275-286`). This task does not
make it cheaper and does not make it more expensive.

## THE STANDING OF THE FOUR CONJUNCTS, AFTER THIS TASK

| conjunct | what it needs now |
|---|---|
| `svAt` | NOTHING. `[LJ-1.524]`. |
| range clause | NOTHING. `[LJ-1.529]`. |
| `injAt` | one projection and three path compositions, over five delivered terms. Measured reachable in `runs/Coexist.agda`. |
| `domAt` | the CONVERSE of the adequacy: a new theorem. UNCHANGED by this task. |

**I DID NOT VERIFY THE `svAt` AND RANGE ROWS MYSELF.** They are the two
predecessors' own verdicts, and I record them as such.

## THE GATES I RAN

**FOUR INDIVIDUAL CHECKS, ALL EXIT 0**, run while the task was live as the
Boundary asks: `scripts/gate/check-probes.py --check` ("check-probes: clean
(5723 tracked files, no probe outside agents/tasks/ and no generated file)"),
`scripts/gate/lint-agda.py --check`, `scripts/gate/lint-prose.py --check`,
and `scripts/gate/check-fences.py --check` ("check-fences: clean (102
masters, run threshold 3)"). `git status --porcelain` is exactly
`?? agents/tasks/LJ-1-531/` and nothing else. **I did not commit and I did
not push.**

**THIS WORKTREE HAS NO `.venv` AND `[LJ-1.529]` REPORTED THE SAME THING FROM
ITS OWN WORKTREE** (`agents/tasks/LJ-1-529/lj-1.529-report.md:341-350`). I
confirm it here rather than restate it: `.venv/bin/python` does not exist, so
`make check` and every `make` target that calls it fail with "No such file or
directory". I ran the four checkers with
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter of the
main checkout, against THIS worktree's scripts. **I created nothing in the
main checkout and I did not `make venv` here.** Two worktrees in a row is a
pattern and not an accident, and it is the program's call and not mine.

**ONE THING I DID DELETE, AND IT IS A GENERATED FILE.**
`runs/delta.out`'s measurement required removing this task's own Agda
interface files, `_build/2.8.0/agda/agents/tasks/LJ-1-531/Probe531.agdai` and
`.../runs/Baseline.agdai`, before each timed run. They regenerate on the next
run and both exist now. `LJ-1-521.Probe521.agdai` was NOT touched, which is
what makes the delta a delta. Nothing under `src/`, `dev/` or `agents/` was
deleted.

## THE RATIO BAR

**The bar cannot fire on this task, for the reason the brief itself states.**
The divisor is the in-fence line count of this task's write scope, counted
the ledger's way: non-blank lines inside ` ```agda ` fences. My write scope
is `Probe531.agda`, `runs/` and two `.md` files. **A raw `.agda` probe
carries no fence and counts 0**, and nothing in the scope is a `.lagda.md`
master under `src/`. So 0.0123 seconds per in-fence line has no divisor here.

Recorded for the day this lands in a master, and **it is NOT the ratio the
bar measures and may not be compared with it**: 1.12 s of user time over 81
code lines is 0.014 s per code line for the whole file. The honest figure for
the mathematics alone is the delta: **about 0.08 s over 60 code lines, which
is 0.0013 s per code line.** The gap between the two is the import, and it
tells whoever lands this that the cost of this conjunct is not in its own
lines.

## W2, THE GENERIC-CARRIER CLAUSE

**ANSWERED, AND THIS TASK IS AN UNUSUALLY CLEAN CASE OF IT.** Sections 1, 2
and 3 of `Probe531.agda` are ALL at the generic carrier: `preds-distinguish`
and `mono→inj` are in a module over `{A : Type ℓ} (w : SWO {ℓc = ℓ} A)`
(`:100`), and `rank-mono` (`:150-153`) and `swo-rank′-inj` (`:166-168`) both
quantify over `{A} (w)`. **The obligation is the ONLY thing in the file that
names the site**, and it is 17 lines of the 81.

**ONE PLACE W2 IS VISIBLY BUYING SOMETHING.** `mono→inj` is stated over an
arbitrary irreflexive codomain relation and is instantiated once here, at
`_∈ₛ_`. It is the general fact that a strictly monotone map out of a strict
total well-order is injective, and it is now written once in the tree at a
type that any later rank, on any later order, can use without a new proof.
`preds-distinguish` is the second instance of the same two record fields.

**No deadline forced a fixed form and there is no conflict to report.**

## W4, THE RETIREMENT CLAUSE

**Not applicable. This task retires no module and deletes nothing.**
`dev/ARCHIVE.md` takes no row. Nothing under `src/` changed.

**ONE THING FOR THE CAMPAIGN'S W4 PASS, RECORDED AND NOT ACTED ON.**
`[LJ-1.529]` recorded that `agents/tasks/LJ-1-490/Probe490.agda:211-242` is
superseded in substance by `Probe529.agda:101-142`
(`lj-1.529-report.md:392-399`). I add one row of the same kind:
`agents/tasks/LJ-1-515/Probe515.agda:224-226`, `swo-rank′-mem`, is the
monotonicity of a rank that the sealed rank of `[LJ-1.521]` replaced. **It
is not wrong and it is not dead. It is unreachable from the live route**,
and `rank-mono` (`Probe531.agda:150-158`) is what stands in its place there.
**A probe is text and is never deleted** (`agents/README.md`, and
`scripts/gate/check-probes.py:10-12`), so there is nothing to retire; I
record it only so the collection the direction orders after LJ-1 does not
read `Probe515`'s monotonicity as the live one.

**Price the ideal form written fresh today, against the chapter I have.**
There is no chapter here: nothing of this task is in `src/`. Written fresh
today into a master, the ideal form is sections 1 to 3 unchanged, because
they are already generic, plus the obligation. That is the same 81 lines
minus the imports the probe pays twice, and the comment budget would drop
from 51 percent of the file to whatever a master's prose rules allow. **I
have no measured basis for a smaller figure and I do not give one.**

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ.** `:255` reads
  "| LJ-1.179 | DD25 review of LJ-1.169's rank NO-GO | OVERTURNED: A FIXED-SHAPE NO-GO | Right for the coding it measured, wrong for the tree, which already carries the parameter split |".
  I read it because the brief invites a refutation of a rank statement and
  names `[LJ-1.497]` as the precedent. This row is the OTHER precedent: a
  rank NO-GO that was overturned on review because it was measured at a
  fixed shape. It is the reason section D-10 above states the extensionality
  at the generic `SWO` record rather than at the ordinal site. It did not
  change the verdict, which is GO either way.
- `archive/dev/JOURNAL.md`: **not read.** Its one `rank` hit (`:317`) is
  about ranking three cures by history and has nothing to do with a rank
  function.
- `archive/dev/JOURNAL-archived.md`: **not read.** Its `rank` hits are the
  retired flat rank-bounded coding and the `CodePred` route, which
  `dev/ARCHIVE.md` records as dead with the route change under D18. This
  task's rank is `swo-rank′` over a well-order and is not that object.
- `dev/ARCHIVE.md`: **not used.** Its one relevant row (`:266`,
  `L.Rud.CodePred`) is the retired object-language code predicate with its
  own rank descent. This task retires nothing and writes no object-language
  predicate, so the file takes no row from me and gave me none.
- `archive/dev/DECISIONS-archived.md`: **declined.** It is 61 lines and
  carries no `rank` hit at all. The `D<n>` series it resolves is not in
  force.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ, AND IT IS THE ONE
  THAT MATTERED.** `:313` reads
  "pairing that reads only the reachable set is symmetric, hence not injective:".
  This is a measured refutation of a FAMILY of injectivity claims, and a
  rank that reads only the predecessor set is close enough in shape that the
  family had to be checked against this site and not assumed away. Section
  D-10 above records the check and why the family does not cover a rank over
  an order that carries `tri∙`.
- `dev/literature/devlin-II5.md`: **not used.** Its one `rank` hit (`:445`)
  is about the condensation map never raising the `<_L`-rank, which is the
  L-order and not the rank over a member's predecessors.
- `dev/literature/digest.md`: **not used.** Its `rank` hit (`:218`) is the
  finite rank jump per S-step in the J-hierarchy. That is the hierarchy's
  own rank, not `swo-rank′`.
- `dev/literature/terms-2026-08.md`: **not used.** Its `rank` hits (`:111`,
  `:122`) are about the Go rank 初段 in a naming discussion, which is a
  translation matter and not this task's.
- `dev/literature/geology.md`: **not used.** Its `rank` hit (`:64`) is
  rank-into-rank cardinals, a large-cardinal topic this task does not reach.
