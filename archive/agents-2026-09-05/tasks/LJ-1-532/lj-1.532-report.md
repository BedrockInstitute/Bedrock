# LJ-1.532 report: row six's membership is FALSE as stated, and its repair is [LJ-1.494]'s gap

**VERDICT: NO-GO, AND IT IS A REFUTATION AND NOT A GAP REPORT.** The
brief's obligation `approx-in-K` is not delivered, because the statement
is false. The refutation typechecks:
`agents/tasks/LJ-1-532/Probe532.agda:206-209`, exit 0,
`runs/final.out`.

    ApproxInK-is-false : ApproxInK → Empty.⊥

**THE BRIEF PREDICTED THIS CASE AND NAMED THE PRICE OF SAYING IT.** "If
it is not, name what `g` is built from and STOP: an approximation stated
nowhere to be in `K` is the same shape of finding as `[LJ-1.494]`'s, at
a different carrier, and saying so is worth more than a term." **`g` is
built from NOTHING**, and this report says what that means and what to
put in its place. `agents/tasks/LJ-1-532/review-of-approx-in-K.md`
states the stop.

**AND THE BRIEF'S OWN QUESTION HAS AN ANSWER: THE TWO CARRIERS SHARE
ONE OBSTRUCTION, NOT TWO.** Section 4 of the probe writes the corrected
statement, and it is `[LJ-1.494]`'s statement about `hierL`.

**THREE THINGS ARE DELIVERED BESIDE THE REFUTATION**, and each is a term
that typechecks, not a claim:

| what | where |
|---|---|
| an approximation on an ordinal carries EXACTLY the pairs `hierL` carries, both directions | `Probe532.agda:238-244`, `:246-256` |
| the corrected statement, written out and NOT inhabited | `:274-277` |
| the corrected statement is not vacuous: the canonical witness IS an approximation | `:346-349` |

## D-10, BEFORE ANY AGDA

The brief ordered it first: "Say at `file:line` what `K` is at this
frame and what it would take for a set of pairs to be one of its
members."

### What `K` is at this frame

`K` is a value slot of the environment, and the chain's standing
hypothesis is `fst (lookup K γ) ≡ Lset α` with `α` a limit. That
hypothesis is `[LJ-1.522]`'s (`agents/tasks/LJ-1-522/Probe522.agda:359`),
`[LJ-1.525]`'s (`agents/tasks/LJ-1-525/lj-1.525-report.md:112-122`) and
`[LJ-1.530]`'s (`agents/tasks/LJ-1-530/Probe530.agda:135`). **This task
inherits it unchanged and the `K`-is-a-level gap stays open.**

### What it would take for a set of pairs to be one of its members

Two routes exist in the tree and this report checked both, as the brief
required.

**ROUTE ONE, `[LJ-1.522]`: a definable SUBSET of a member of `K`.**
`defPow-closed-noCode` (`agents/tasks/LJ-1-522/Probe522.agda:356-364`)
wants a code `c` and a satisfaction set `v`, both IN `K`, and a
satisfied `DefBody w`. **`g` is reachable from it only through a formula
over an earlier stage that carves the graph of the tower, and the tree
does not have that formula below `α`.** `[LJ-1.530]` measured the same
wall from the other side: "nothing in the tree collects that family at
one stage below `α`"
(`agents/tasks/LJ-1-530/lj-1.530-report.md:102-103`). **Not
reachable.**

**ROUTE TWO, `[LJ-1.530]`: `𝒟ₒ w` for a recorded value `w`.**
`dK` (`agents/tasks/LJ-1-530/Probe530.agda:131-156`) puts a definable
powerset of a STAGE in `K`. `g` is a set of PAIRS, not a definable
powerset of anything, and no chain of `dK` reaches it. **Not
reachable.**

### And then the third answer, which is neither

**THE QUESTION IS NOT WHICH ROUTE REACHES `g`. IT IS THAT NO ROUTE CAN,
BECAUSE `g` IS NOT DETERMINED.** `ApproxAt` speaks only about the
Kuratowski-pair members of `g`; a member that is not a pair is
unconstrained, and there is no bound on it. That is W3, and it is the
refutation.

**THIS IS `K`, NOT A STAGE, AND I DID NOT TRANSFER `[LJ-1.494]`'s
ANSWER.** The brief warned against both readings. The refutation is
proved at `K` on its own terms and cites `[LJ-1.494]` only for the
CORRECTED statement, where the object is the same one `[LJ-1.494]`
measured.

## W3, WRITTEN FIRST AND ALONE

`agents/tasks/LJ-1-532/runs/W3.agda`, 164 lines, 85 non-blank and not a
comment, exit 0, `runs/w3-final.out`, median 3.42 s.

**THE BRIEF NAMED THE TERM AS "g, as a set, at file:line, with whatever
puts it in K or fails to". THE ANSWER IS THAT `g` IS BUILT FROM
NOTHING.** In `LsetGraphAt w b = ∃̇ (ApproxAt zero (suc b) ∧̇ Step (suc w)
(suc b) zero)` (`src/L/Coding/Sequence.lagda.md:291-292`) the
approximation is the witness of an UNBOUNDED existential over the whole
class carrier. It is not constructed anywhere. The only thing said about
it is `ApproxAt zero (suc b)`.

**AND `ApproxAt` IS BLIND.** `ApproxAt f a = domAt f a ∧̇ ∀̇ (∀̇ (appAt …
⇒̇ Step …))` (`src/L/Coding/Sequence.lagda.md:286-289`). `domAt`
(`src/L/Coding/Model.lagda.md:278-280`) constrains `x` only through
`inDomAt`, which is "there merely is `y` with `pr x y ∈ f`"
(`:269-270`); the step conjunct is guarded by `appAt`, the same pair
membership. **Neither conjunct can see a member of `g` that is not a
Kuratowski pair.**

W3's deliverable is the decisive miniature the brief asked for. It is
`blind` (`runs/W3.agda:162-164`, moved unchanged into
`Probe532.agda:191-193`): `⁅ ω ⁆s` satisfies `ApproxAt` at the domain
bound `∅`. **The measurement is a counterexample and not a search**, and
the brief's stop condition fires at its cheapest point, exactly as it
predicted.

**W3 COST 3.42 s AND NOT "UNDER 30 SECONDS", BUT IT IS NOT COMPARABLE TO
THE BRIEF'S GUESS FOR A DIFFERENT REASON:** the brief expected reading
plus a small check, and what W3 needed was a term (`ord-not-pr`, 23
lines) that no predecessor had written.

## THE REFUTATION

`Probe532.agda:206-209`. The instance is the cheapest the frame admits,
and **every frame fact the chain carries is a hypothesis of the
refuted statement**: `K` is a LIMIT level, the bound is an ORDINAL, and
the bound lies IN `K` (`Probe532.agda:108-117`). Nobody can say it won
by dropping one.

| object | value | discharged at |
|---|---|---|
| `α`, `K` | `ω`, `Lset ω` | `ω-IsLimit`, `Probe532.agda:92-97` |
| the bound | `∅` | `∅-ord` (`src/L/Ordinal.lagda.md:77`); `∅ ∈ Lset ω` at `Probe532.agda:195-197` |
| `g` | `⁅ ω ⁆s` | `sglʟ ωʟ` (`src/L/Coding/InL.lagda.md:363-364`, `ω∈L` at `src/L/Axioms/Infinity.lagda.md:66`) |

**THE ONE NEW LEMMA IS `ord-not-pr` (`Probe532.agda:131-153`, 23
lines): AN ORDINAL IS NOT A KURATOWSKI PAIR.** `pr a b = ⁅ ⁅ a ⁆s , ⁅ a
, b ⁆ ⁆` (`src/V/Coding.lagda.md:175-176`), so a transitive `pr a b`
pulls `a` into `pr a b`, hence `a` into `a`, and `∈-irrefl`
(`src/V/Hierarchy.lagda.md:155-156`) closes it. **Transitivity is all of
`IsOrd` that is spent** (`src/L/Constructible.lagda.md:141-142` with
`:83`); the second component is never touched.

**THE ARITHMETIC OF THE REFUTATION, ONE LINE EACH.** `ord-not-pr` at
`ω` says no member of `⁅ ω ⁆s` is a pair, so both halves of `domAt` and
the whole step condition are vacuous, so `⁅ ω ⁆s` is an approximation on
`∅`; `Lset ω` is transitive (`Lset-layer`,
`src/L/Constructible.lagda.md:246`, with `layer-trans`, `:183`), so
`⁅ ω ⁆s ∈ Lset ω` would give `ω ∈ Lset ω`; `ord∈Lset→∈`
(`src/L/Ordinal/Stages.lagda.md:265-268`) would then give `ω ∈ ω`.

**THE INSTANCE IS CHEAP, THE DEFECT IS NOT LOCAL.** `∅` only makes the
completeness half of `domAt` vacuous too. At any ordinal bound the same
junk member can be added to any approximation, because `ApproxAt` never
sees it. Section 3 turns that sentence into a term.

## THE CORRECTED STATEMENT

**SECTION 3 PINS THE DAMAGE: THE ∀-FORM FAILS ONLY ON JUNK.**
`Probe532.agda:227-256` proves both directions against `hierL`, the
tree's own canonical table (`src/L/Hierarchy.lagda.md:621-626`):

| direction | term | built from |
|---|---|---|
| every pair an approximation records, `hierL` records | `pairs-into-hier`, `:238-244` | `approx-val` (`src/L/Hierarchy.lagda.md:274-278`) with `hier-in` (`:527-534`) |
| every pair `hierL` records, the approximation records | `pairs-from-hier`, `:246-256` | `hier-out` (`:511-525`), `ApproxAt-value` (`src/L/Coding/Sequence.lagda.md:298-301`), `approx-val` again |

**NOTHING IN SECTION 3 IS NEW MATHEMATICS.** Every step is a delivered
`src/` term applied once. What is new is the conclusion: two
approximations on one ordinal differ ONLY in members that are not pairs.

**SO ROW SIX'S MEMBERSHIP, CORRECTLY STATED, QUANTIFIES OVER THE
CANONICAL WITNESS** (`Probe532.agda:274-277`):

    HierInK = (α : V ℓ) → IsLimit α
            → (β : V ℓ) (hβ : ⟨ isL β ⟩) (oβ : IsOrd β) → ⟨ β ∈ α ⟩
            → ⟨ fst (hierL β hβ oβ) ∈ Lset α ⟩

**IT IS NOT INHABITED HERE AND NOTHING IN THE TREE INHABITS IT.** It is
`[LJ-1.494]`'s measurement, word for word:
"**Is `hierL δ` a member of `Lset α` when `δ` is?** The tree does not
bound `hierL δ` by `α`" (`agents/tasks/LJ-1-494/lj-1.494-report.md:66-67`),
with `[LJ-1.230]` recorded NO-GO on the same statement before it
(`:116-118`, quoting `agents/tasks/LJ-1-230/lj-1.230-report.md:79`).

**AND IT IS NOT A STATEMENT ABOUT AN EMPTY CLASS.** `hier-is-approx`
(`Probe532.agda:346-349`) proves the canonical witness IS an
approximation at every ordinal bound. **That closes the one hole a
critic could open in the repair**: if `hierL B` failed `ApproxAt`, the
∃-form would have no candidate and the repair would be empty. It does
not fail.

**SECTION 5 IS `graph-table`'s OWN `approx` BLOCK, RE-MEASURED AND NOT
CITED.** `src/` builds it (`src/L/Hierarchy.lagda.md:417-419`, with the two
helpers it consumes at `:390-401` and `:403-415`, inside `graph-table`
at `:382-419`) but keeps it private inside a term that also
builds the OUTER step, and row six needs the approximation alone. A
measured cure does not transfer by analogy (`AGENTS.md:45`); this is the
same code re-elaborated at this site and typechecked here.

## THE ANSWER TO THE BRIEF'S QUESTION

The brief said a NO-GO "would tell the mathematician whether the two
carriers share one obstruction or two". **ONE.** Row six at `K` and
`[LJ-1.494]`'s stage question are the same statement about the same
object, `hierL`, and the only difference is which set is asked to hold
it. The stage form is `[LJ-1.494]`'s; the `K` form is `HierInK` above.

## ROW SEVEN, LOOKED AT ONCE

**ROW SEVEN WRAPS ROW SIX AND ADDS EXACTLY ONE MEMBERSHIP.**
`LevelHood.levelHoodB = ∃̇∈ (var 3) (G.graphBndAt ∧̇ (var 2 ≐ var 0))`
(`src/L/BoundedSubset.lagda.md:108-111`), at the environment
`u ∷ v ∷ γ ∷ K ∷ δ` where slot 3 is `K` and slot 2 is the value `v`
(`:69-71`); so it says "there merely is `w ∈ K` with `graphBndAt` at `w`
and `v = w`", against the unbounded form, which collapses to level-hood
of `v` itself. **Rows one to six bear on it completely and are not
enough on their own:** the bounded direction to the machine forgets the
bound and is free, and the machine direction needs row six at that `w`
PLUS the level value in `K`, that is `⟨ Lset β ∈ Lset α ⟩` for `β ∈ α`.
**That second membership looks cheap and I did not build it and did not
typecheck it:** `[LJ-1.530]` has both pieces, `stage∈𝒟ₒ`
(`agents/tasks/LJ-1-530/Probe530.agda:97-99`) and `Lset-in`
(`src/L/Constructible.lagda.md:319-320`), and nobody has composed them.

## THE PRICE

Three forced rechecks each, the file's own interface removed before
every run, so each number is a real recheck. `GHCRTS="-A64m -I0 -M8g"`,
the wide caliber, set on the pane by the program and untouched. ONE Agda
process per run. All twelve exited 0.

| file | median wall | peak RSS | runs |
|---|---:|---:|---|
| `runs/Control532.agda`, the import list, NO term | **1.58 s** | 406,798,336 B | `runs/ctl-t1.time` to `ctl-t3.time` |
| `runs/W3.agda` alone | **3.42 s** | 408,027,136 B | `runs/w3-t1.time` to `w3-t3.time` |
| `runs/Section12.agda`, through the refutation | **5.16 s** | 446,922,752 B | `runs/s12-t1.time` to `s12-t3.time` |
| `Probe532.agda`, all five sections | **9.05 s** | 610,582,528 B | `runs/full-t1.time` to `full-t3.time` |

**BY SUBTRACTION: THE WHOLE PROBE COSTS 7.47 s ABOVE ITS IMPORTS. THE
REFUTATION IS 3.58 s OF THAT AND THE REPAIR IS 3.89 s.**

**THE REFUTATION IS THE EXPENSIVE HALF PER LINE, AND THE REASON IS THE
ELABORATOR AND NOT THE MATHEMATICS.** Sections 1 and 2 name `⊨` at three
environments (`domAt`, `ApproxAt`, and the step under `Empty.rec`), and
each satisfaction has to be normalised. Sections 3 and 5 are longer and
name `⊨` only where the delivered lemmas already put it. **A brief that
funds a refutation against a membership row's numbers will be wrong by
this factor**, which is `[LJ-1.530]`'s own warning about P-m, in the
opposite direction.

**SIZE.** `Probe532.agda` is 349 lines, of which **181** are non-blank
and not a comment. `runs/W3.agda` is 164 lines, of which **85**.

| term | lines | where |
|---|---:|---|
| `ApproxInK`, the brief's type | 10 | `Probe532.agda:108-117` |
| `ord-not-pr` | 23 | `:131-153` |
| the counterexample objects | 15 | `:170-193` |
| `∅∈Lω`, `ω∉Lω`, `sgl-ω∉Lω` | 9 | `:195-203` |
| **`ApproxInK-is-false`, the refutation** | **4** | `:206-209` |
| `pairs-into-hier` | 7 | `:238-244` |
| `pairs-from-hier` | 11 | `:246-256` |
| `HierInK`, the corrected statement | 4 | `:274-277` |
| `hier-is-approx` with its four tables and two helpers | 46 | `:304-349` |
| `ω-IsLimit`, the non-vacuity witness | 6 | `:92-97` |

**AGAINST THE BRIEF'S ESTIMATE.**

| item | brief | measured |
|---|---|---|
| W3 | about 20 lines, under 30 s | **85 lines, 3.42 s** |
| the probe | about 170 lines | **181 lines** |
| the obligation | about 45 lines | **NOT DELIVERED. The refutation that replaces it is 4 lines on 47 lines of counterexample** |

**THE LINE ESTIMATE FOR THE PROBE WAS CLOSE AND THE ESTIMATE FOR W3 WAS
LOW BY A FACTOR OF FOUR.** The reason is the same in both directions:
the brief priced W3 as reading, and what settled it was a term.

**NOT VACUOUS.** `ω` is a limit level (`Probe532.agda:92-97`, verbatim
from `agents/tasks/LJ-1-530/Probe530.agda:86-91`), so the refuted
statement's antecedent is inhabited and the refutation is not a refutation
of an empty hypothesis.

**NO WALL EVENT.** No heap exhaustion and no rerun after a wall. Peak RSS
is 610,598,912 B against an 8 GB cap, about one thirteenth of it.

**FOUR ERRORS IN ALL, AND EVERY ONE WAS SCOPE OR SIGNATURE AND NOT
MATHEMATICS.** `runs/w3-0.out` `[NotInScope] ∥`; `runs/w3-1.out`
`[UnequalTerms]`, because `⁅ a ⁆s` is a separate `SingletonPackage` and
not `⁅ a , a ⁆`; `runs/full-0.out` `[UnequalTerms]`, because `LsetS`
returns an element of the class and not an `isL` proof
(`src/L/Axioms/Basic.lagda.md:160-161`); `runs/full-2.out`
`[NotInScope] StepAt`, when section 5 was added on top of a green
sections 1 to 4 (`runs/full-1.out`, exit 0). **No unsolved meta and no
universe-level error at any point, and no error of a type or a term.**
All three files were rechecked after the citation fixes:
`runs/final.out`, `runs/w3-final.out` and `runs/s12-final.out`, all exit
0.

**NOTHING WAS POSTULATED.** `grep -c postulate` returns 0 in both Agda
files, and both carry `--safe` (`Probe532.agda:1`, `runs/W3.agda:1`).

**THE CERTIFICATES WERE NOT SPENT.**
`grep -c "Σ₁-levelHood\|σ₁-up\|Σ₁-Σ₂" Probe532.agda` returns 0. The two
`Σ₁` certificates have now been unconsumed since `[LJ-1.228]` through
this task as well.

**GATES.** `check-probes.py` clean (5770 tracked files, no probe outside
`agents/tasks/`), `lint-agda.py` and `lint-prose.py` both silent. Run as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, because this worktree has
no `.venv` of its own.

## SCOPE, AND WHAT I DID NOT DO

Written: `agents/tasks/LJ-1-532/Probe532.agda`,
`agents/tasks/LJ-1-532/review-of-approx-in-K.md`, this report, and
`agents/tasks/LJ-1-532/runs/` (three Agda files and their run evidence).
**Nothing in `src/`.** Nothing committed and nothing pushed.

**I DID NOT REBUILD ROWS ONE TO FIVE.** They are cited from
`[LJ-1.530]`'s table (`agents/tasks/LJ-1-530/lj-1.530-report.md`, the
seven-row table) and never re-derived.

**I DID NOT ATTEMPT ROW SEVEN.** The required section above reads it and
stops there, as AD12 requires.

**I DID NOT WEAKEN THE OBLIGATION TO GET A TERM.** The refuted type is
the brief's, at the site's own environment, with every frame hypothesis
present.

**I WENT BEYOND THE STOP BY THREE TERMS**, in sections 3 to 5
(`pairs-into-hier`, `pairs-from-hier`, `hier-is-approx`). The reason is
the brief: "A NO-GO NAMES WHAT THE APPROXIMATION IS MISSING". **A NO-GO
that says "it is missing a bound" is a claim; a NO-GO that says "here is
the corrected statement, here is the proof that it is exactly the
corrected one, and here is the proof that it is not vacuous" is a
measurement.** The three cost 3.89 s together.

## WHAT THE CHAIN OWES AFTER THIS

| # | what it is | status after this task |
|---|---|---|
| 1 | `StepB.leafB` against `DefAt zero (suc zero)` | BUILT, `[LJ-1.525]`, `leaf-unbounds`, `agents/tasks/LJ-1-525/Probe525.agda:150-165` |
| 2 | `StepB.bodyB` against `StepBody b f` | BUILT, `[LJ-1.527]`, `body-unbounds`, `agents/tasks/LJ-1-527/Probe527.agda:184-200` |
| 3 | `StepB.witB` | WRAPPER BUILT, `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:254-258`; its memberships BUILT in `[LJ-1.530]` |
| 4 | `StepB.stepBndAt` | WRAPPER BUILT with row three; `zK` BUILT in `[LJ-1.530]` |
| 5 | `ApproxB.approxBndAt` | WRAPPER BUILT, `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:313-316`; `entryK` and `domK` BUILT in `[LJ-1.530]` |
| 6 | `GraphB.graphBndAt` against `LsetGraphAt` | **THE BRIEFED FORM IS REFUTED** (`Probe532.agda:206-209`). What is owed is `HierInK` (`:274-277`), which is `[LJ-1.494]`'s open gap. Everything else row six needs is now a term |
| 7 | `LevelHood.levelHoodB` | NOT BUILT. It is row six plus one membership, `⟨ Lset β ∈ Lset α ⟩` for `β ∈ α`, whose two pieces exist and are uncomposed |

**SO THE CHAIN'S REMAINING MATHEMATICAL CONTENT IS ONE FACT AND ONE
RE-MEASUREMENT.** `[LJ-1.527]` said two facts and one re-measurement;
`[LJ-1.530]` paid one of the two facts; **this task shows the other one
was mis-stated and gives its corrected form.** What is left is
`hierL β ∈ Lset α`, and `[LJ-1.304]`'s two wrappers re-measured at `𝒮ʟ`
against `src/L/Coding/Sequence` rather than at the ambient class against
the generic port. That re-measurement is still owed and this task did not
touch it.

**AND THE NEXT BRIEF SHOULD NOT BE ANOTHER ROW.** `[LJ-1.494]` and
`[LJ-1.230]` both stopped on `hierL β ∈ Lset α` and neither priced a
cure. **It is now the single open mathematical fact between the chain
and both `Σ₁` certificates**, and it is worth a brief of its own. What
`[LJ-1.530]` measured about the missing named theorem applies to it
directly: Devlin's bound set `K(w, u)`
(`dev/literature/level-formula-slot-roles.md:23`) is what would carry
the code family and the satisfaction family below `α`, and it is the
same object row six's repair wants.

**THE `K`-IS-A-LEVEL GAP IS STILL OPEN.** `[LJ-1.522]` recorded it,
`[LJ-1.525]`, `[LJ-1.527]` and `[LJ-1.530]` each inherited it, and this
task inherits it in turn: `ApproxInK` takes `fst (lookup K γ) ≡ Lset α`
as given, and the refutation is at `Lset ω` and not at an abstract `K`.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ, AND IT CONFIRMED THAT ROW
  SIX WAS NEVER RUN.** `archive/dev/LJ-dispatch-index.md:361` reads
  "| LJ-1.304 | Price StepAgree and ApproxAgree | BOTH BUILT, ABOUT 190
  LINES. BASIS: THE BUILD | q's four named costs are now ALL measured.
  Neither module exists in src/: they were LJ-1.52's names |". **`[LJ-1.304]`
  built the wrappers for rows three to five and named no wrapper for row
  six**, which agrees with the brief's premise 7 and with `[LJ-1.228]`.
- **`archive/dev/JOURNAL.md`: READ, ONE LINE, AND IT IS ABOUT A
  DIFFERENT SLOT.** `archive/dev/JOURNAL.md:807` reads
  "`u`'s slot is the definable powerset of the recorded value and the
  induction". That is `dK`'s slot, which `[LJ-1.530]` paid. **It does
  not touch row six's witness slot**, and I did not use it as evidence
  about this task.
- **`archive/dev/JOURNAL-archived.md`: NOT USED.** I searched it for
  `ApproxAt`, `LsetGraph` and `hierL` and took nothing from it. The one
  line `[LJ-1.530]` used from it (`:1997`, the `⟪ 𝒟ₒ A ⟫` quotient
  warning) is about the definable powerset and not about the
  approximation. **Declined.**
- **`archive/dev/ORCHESTRATION.md`: NOT READ.** It is the archived
  operating document for the pre-program loop. This task is one
  dispatch under the program and takes no rule from it. **Declined.**
- **`dev/ARCHIVE.md`: READ ITS PURPOSE, NOT USED.** It is the registry
  of retired modules. **This task retires no module and lands nothing in
  `src/`, so no row is owed and none is written.** Declined for content.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`: READ, ONE ROW, AND IT
  NAMES WHAT THE CORRECTED STATEMENT NEEDS.** `:23` reads
  "| 1 | Devlin 2.4 | `D(v,u) = ∃w[K(w,u) ∧ C(w,v,u)]`, and `D(v,u) ↔ v = Def(u)` | 2 | `w`, ONE bound, DETERMINED by `K(w,u)` | `v`, `u` | VALUE, ARGUMENT | `_build/literature/dev2.txt:619-623` |".
  **Devlin's `w` is a BOUND witness determined by `K(w,u)`, and the
  tree's `LsetGraphAt` has no such determination**: its witness is free.
  That is the classical shape of this task's refutation, and it says the
  repair is not a patch but the classical statement.
- **`dev/literature/devlin-II5.md`: READ, AND IT IS WHY I DID NOT CALL
  `HierInK` FALSE.** `dev/literature/devlin-II5.md:339` reads
  "   - Def uniformly Δ₁^α at limit α > ω (2.5, `dev2.txt:663-666`).".
  **The classical result is stated at a limit `α > ω` and the tree's
  `IsLimit` does not carry that side condition.** So the corrected
  statement is probably true and certainly undelivered, which is what
  section 4 says and no more.
- **`dev/literature/truncation-and-selection.md`: READ ITS SUBJECT, NOT
  USED.** The refutation uses `PT.rec` twice and selects nothing; no
  truncation had to be escaped. **Declined.**
- **`dev/literature/digest.md`: NOT USED.** It is the corpus digest and
  I reached the two entries above directly. **Declined.**
- **`dev/literature/terms-2026-08.md`: NOT USED.** This task adds no
  term to `dev/glossary.toml` and proposes no name. **Declined.**
