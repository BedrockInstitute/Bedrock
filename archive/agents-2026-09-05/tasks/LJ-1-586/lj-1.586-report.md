# LJ-1.586 report: `absorbs` is definable

## HEAD
head_slot: coder
machine: shared
verdict: GO
obligation: agents/tasks/LJ-1-586/Probe586.agda::absorbs-definable

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-586/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event: peak footprint 675,578,936 bytes, about 0.63 GiB,
against an 8 GB cap (`runs/final-4.out`). Nothing is postulated, there is no
hole, and no warning is emitted. The probe is a raw `.agda` file, so it carries
no ` ```agda ` fence, counts 0 in-fence lines, and the ratio bar cannot fire on
it.

**GATES RUN.** Every conjunct of `make check` except `typecheck`:
`markers`, `lint`, `lint-agda`, `glossary`, `ledger`, `probes`, `closure`,
`fences`, `reuse`, `ruleids`, `specsurface`. All clean. `check-unbound-hyp` also
clean.

**TWO GATES I DID NOT RUN, AND WHY.** `typecheck` builds the whole tree.
`git status` shows ONE entry, the untracked `agents/tasks/LJ-1-586/`, so no
master changed and a whole-tree typecheck would measure nothing about this task;
it would also be a SECOND Agda process while other panes hold one. `ratio` is
not a conjunct of `make check`, and it refused on its own C-12 guard: two other
slots (LJ-1.582 and LJ-1.587) held live Agda processes at that moment. Neither
refusal is a finding about this task.

The worktree carries no `.venv`, so every gate ran as
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned interpreter of the
main checkout, with the working directory left in this worktree.

## W3, THE WIDEST UNMEASURED TERM

**IT WAS DONE FIRST AND TYPECHECKED ALONE.** The slice is
`agents/tasks/LJ-1-586/runs/W3.agda`, tracked, and it is a real `.agda` and not
a transcript. Runs `runs/w3-2.out` and `runs/w3-3.out`: exit 0, 3.28 s and
3.22 s, peak 611 MB. `runs/w3-1.out` is the first attempt, exit 42, one
`NotInScope` on a missing `PT` import and nothing else. Those three ran while
the file sat at the task root; `runs/w3-4.out` is the same file re-run after it
moved into `runs/` and its module name became `LJ-1-586.runs.W3`, exit 0.
`Probe586.agda` does NOT import it: section 1 of the probe repeats W3's content
so the probe stands alone, and the slice is the record that it was checked
first.

**THE COUNT IS ZERO.** `grep -rn "BoundedSubsetAt" src/` gives THREE lines and
exactly ONE is a module application:

| line | what it is |
|---|---|
| `src/L/BoundedSubset.lagda.md:1385` | the declaration |
| `src/L/StageBound.lagda.md:62` | a comment |
| `src/L/StageBound.lagda.md:74` | **the only application** |

Its twelfth argument is the name `absorbs` (`src/L/StageBound.lagda.md:76`), and
that name is the enclosing module's OWN parameter
(`src/L/StageBound.lagda.md:69`). The outer wrapper repeats the same
pass-through: declared at `:97`, forwarded at `:116`. `L.StageBound` is imported
by ONE file, `src/Everything.lagda.md:396`, which only typechecks it.

**SO NO CONCRETE TERM IS EVER SUPPLIED FOR THE TWELFTH PARAMETER IN `src/`.**
The count of instantiations is 1 module application and 0 terms.

`src/L/Absorption.lagda.md:635` carries the NAME `absorbs` at a DIFFERENT type,
`⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`, and does not fit the slot. C-42: it is a
different statement at a different site and this report never reads one as the
other. `[LJ-1.540]` had already said so
(`agents/tasks/LJ-1-540/Probe540.agda:22-26`), and `[LJ-1.580]` grepped the same
four lines (`agents/tasks/LJ-1-580/review-of-beta-into-alpha-coded.md:29-33`).

## PARAMETER OR TERM

**IT IS A PARAMETER IN `src/`, AND THAT IS THE ANSWER THE BRIEF SAID IT DID NOT
KNOW.** `src/L/BoundedSubset.lagda.md:1392` declares it; nothing in `src/` ever
hands it a term. The count is above, and it is ZERO.

**AND THE CAMPAIGN ALREADY KNEW IT AND WROTE IT DOWN.**
`archive/dev/LJ-dispatch-index.md:338` records `[LJ-1.280]`:

> `sq and absorbs stay Pi-parameters, unsupplied and honestly so.`

That is 306 tasks old and still true at today's tree. This report reaches it by
grep and by the elaborator; the archive row is corroboration and not the source.

**BUT THE BRIEF'S SECOND BRANCH IS THE ONE THAT FIRES.** The brief wrote: "If
`[LJ-1.540]`'s B7 term is what instantiates it, describe THAT. If nothing
instantiates it, the row wants a hypothesis and not a construction." **NEITHER
DISJUNCT IS RIGHT AS WRITTEN**, and saying so is the whole of D-10 here:

- Nothing in `src/` instantiates it, so the first disjunct is false TODAY.
- But `[LJ-1.540]` DELIVERED a term at exactly that type, so the slot is not
  empty and the second disjunct's conclusion does not follow. A hypothesis is
  what you carry when no term exists. **A term exists; it is simply not plugged
  in.**

So the obligation is neither "for any definable `absorbs`" (which would be
`id`, and worth nothing) nor a carried hypothesis. **IT IS A DESCRIPTION OF THE
ONE TERM THE CAMPAIGN HAS BUILT**, and it is stated at that term and not at a
copy: `absorbs-definable`'s type names
`candidate α xe ordα α∉ω xe⊆Lα` (`agents/tasks/LJ-1-586/Probe586.agda:399`),
where `candidate = P540.AbsorbsAt` (`:136`).

`Probe586.agda:196-197` is the `refl` that keeps the two spellings the same object:

    g-is-absorbs : g ≡ fst (candidate α xe ordα α∉ω xe⊆Lα)
    g-is-absorbs = refl

**WHAT FOLLOWS FOR `src/`, AND IT IS THE MATHEMATICIAN'S CALL AND NOT MINE.**
`src/L/StageBound.lagda.md:69` still carries an OPEN `absorbs`, and no term of
this probe reaches it. Two exits, and both are a change to `src/` that this task
was forbidden to make (`Probe586.agda:453-459` states them in the file):

1. `L.StageBound` takes `[LJ-1.540]`'s term as the parameter's value, and the
   parameter disappears. `archive/dev/LJ-dispatch-index.md:195` records that
   `[LJ-1.119]` already did this once for the sibling parameter: "Devlin55 now
   has NO parameter."
2. The parameter stays open and gains a definability hypothesis beside it, at
   the type `absorbs-definable` inhabits.

**Exit 1 is the one this result argues for**, because a hypothesis beside an
open parameter is exactly the arbitrary case, and `[LJ-1.533]` refuted a code
there. I did not take it: it is a `src/` change and AD3 gives the judgement to
the mathematician.

## VERDICT

**GO. `absorbs-definable` IS INHABITED** at
`agents/tasks/LJ-1-586/Probe586.agda:392-400`, top level, with the module's
`Site` telescope discharged. Exit 0 on every final run.

| runs | what the file was | result |
|---|---|---|
| `runs/w3-1.out` | the W3 slice, first attempt | exit 42, ONE `NotInScope` on a missing `PT` import |
| `runs/w3-2.out`, `w3-3.out` | the W3 slice ALONE, at the task root | exit 0, 3.28 s and 3.22 s |
| `runs/w3-4.out` | the SAME slice after the move to `runs/W3.agda` | exit 0 |
| `runs/s2-1.out` | sections 1 to 2, first attempt | exit 42, ONE `NoSuchModule` |
| `runs/s2-2.out` | sections 1 to 2 | exit 0, 3.94 s |
| `runs/s3-1.out` | sections 3 to 5, first attempt | exit 42, ONE `CannotApply` on a stray `{ℓ}` |
| `runs/s3-2.out` | sections 3 to 5 | exit 0, 4.33 s |
| `runs/s5-1.out` | with the top-level obligation and `absorbs-coded` | exit 0 |
| `runs/s6-1.out` | with section 6 | exit 0 |
| `runs/final-1.out` to `final-3.out` | 459 lines, before the comment line-references were corrected | exit 0, 4.80 to 5.33 s |
| `runs/final-4.out` to `final-6.out` | **the file exactly as this report describes it**, 459 lines | exit 0, 3.93 to 4.02 s |

Every `final-*` run and `w3-3` deleted the `.agdai` first, because Agda skips a
file whose content is unchanged and a run that skips measures nothing.

**THE THREE ERRORS ABOVE WERE ALL SCOPE, NOT MATHEMATICS.** The formula and both
adequacy directions typechecked on their first submission. That is a measurement
about the shape and it is the finding of the next section.

### And what it buys, which is more than the brief asked for

`absorbs-coded` (`Probe586.agda:403-410`) is `InjL Dᴸ Cᴸ`: **`absorbs` WITH A
CODE.** It is built from the obligation by two IMPORTED terms and nothing new:
`[LJ-1.568]`'s `def-restricted` (`agents/tasks/LJ-1-568/Probe568.agda:252-253`)
turns `Def` into the graph, and `[LJ-1.561]`'s `Code.code`
(`agents/tasks/LJ-1-561/Probe561.agda:283-284`) reads the four `InjCode`
conjuncts off it. The injectivity it needs is `[LJ-1.540]`'s own `shift-inj`
(`agents/tasks/LJ-1-540/Probe540.agda:292-293`).

## WHAT B7 AND ROW 1 EACH GET

**B7 GETS ITS MISSING PIECE OUTRIGHT**: `[LJ-1.561]` pays B7 from `W`
(`agents/tasks/LJ-1-561/Probe561.agda:388`), `[LJ-1.568]` proved `Def` at a `g`
is what `W` at that `g` amounts to (`Probe568.agda:252`, `:377`), and this task
supplies `Def` at `g := absorbs`, so `absorbs-coded` is B7's conclusion at this
pair without any appeal to `W`. **ROW 1 GETS ONE OF ITS TWO UNCODED THINGS AND
NOT THE ROW**: `count`'s base case applies `code-inj = comp-inj absorbs
(stage-card-upper ...)` (`src/L/BoundedSubset.lagda.md:1512-1513`, and
`[LJ-1.580]`'s `count-applies-absorbs` at `Probe580.agda:148` is the `refl` for
it), so with `[LJ-1.584]`'s stage bound and `Comp`
(`src/L/InjChain.lagda.md:314-433`) the COMPOSITE `code-inj` becomes codable,
but `CSel.leg2` is not `code-inj`: `count` recurses over the hull's term algebra
(`src/L/BoundedSubset.lagda.md:1422-1430`) and `CodeSelect` selects over that
recursion, and neither is paid here.

**ONE DESCRIPTION SERVES BOTH.** There is a single term, `absorbs-definable`,
and both uses read it at the same pair `(Dᴸ , Cᴸ)`; B7 consumes it through
`Code.code` and row 1 would consume it through `Comp`. Nothing about the two
consumers asks for a different formula.

**I BUILT NEITHER ROW.** AD12 gives this brief one obligation, and the brief
named the other one `[LJ-1.584]`'s.

## WHAT THE SHAPE COST

**THE SHAPE DID NOT RESIST, AND THAT IS THE REPORTABLE FACT.** 459 lines against
the brief's estimate of about 180, but the obligation itself is 10 lines
(`Probe586.agda:392-400`) against an estimate of about 45, and the formula plus
both directions is 117 lines (`:250-366`). The overrun is comment and section 6,
not proof. **The estimate was priced against `[LJ-1.568]`, which had to INVENT
`Def` and prove it weakest; this task only had to instantiate it.**

**W2, AND IT IS THE REASON.** `src/L/Absorption.lagda.md` was already written at
a generic carrier: `ShiftFo` (`:229-240`) and `Carve` (`:386-402`) take the
domain, the codomain, the shift and its three readbacks as PARAMETERS.
`archive/dev/DD-archived.md:22` is DD4's archived text, the historical home of
the rule W2 now carries. So the generic writing done there is what made this
task cheap, one campaign later and at a different site. **This report answers
W2 by reporting a dividend, not by claiming one.**

**THREE THINGS DID NOT TRANSFER, AND EACH IS A REAL DIFFERENCE, NOT A RESKIN.**
C-42: a measured cure does not transfer by analogy, and these were re-measured
at this site.

1. **`Carve` DOES NOT FIT.** Its `γ` plays two roles at once: the top element
   that case 2 tests against, and the fallback membership target that case 3
   discriminates on (`src/L/Absorption.lagda.md:215`, `:218`). In `ShiftGraph`
   they coincide because `D = sucV γ` and `C = γ` (`:545-549`). Here the top is
   `xe` and the fallback target is `Lset α`, and they are different sets.
2. **CASE 2 NEEDS `¬̇ (u ∈̇ ω)` AND `shiftCase2` DOES NOT HAVE IT.**
   `ShiftGraph` is handed `γ∉ω` (`:540`) so its top element is never a numeral.
   `[LJ-1.540]` has NO hypothesis on `xe` and measured that it needs none
   (`agents/tasks/LJ-1-540/Probe540.agda:371-376`), so `xe` MAY be a numeral and
   case 1 would take it. Without the conjunct cases 1 and 2 overlap and the
   formula demands two values for one argument.
3. **CASE 3 TESTS `¬̇ (u ≐ xe)` AND NOT `u ∈̇ γ`.** That is what the ambient
   `shift-other` actually consumes (`Probe540.agda:276-279`), and it is why this
   file needs no `D-in-dec` at all (`src/L/Absorption.lagda.md:239-240`): the
   three tests are decided by `lem` alone and are manifestly exclusive.

**AND ONE THING WAS FREE THAT COULD HAVE BLOCKED.** `Def` lives at L-SETS
(`Probe568.agda:159-160`) and `absorbs` is a map between the members of two
AMBIENT sets, so the statement cannot even be FORMED until both are L-elements.
That is `Lset-isL` (`[LJ-1.580]`'s, `Probe580.agda:104`, re-typed at
`Probe586.agda:148-152`) and `dom-isL` (`Probe586.agda:153-156`), and the union half is
two facts already in `src/`: `sglL` and `cupL`
(`src/L/Coding/InL.lagda.md:206`, `:211`). **W3 checked this BEFORE the build,
because it is the one thing that could have made the obligation unstatable.**

**NO LEVY GRADE WAS ASKED FOR.** Both negations in the formula are free because
`hasSeparationL` takes an arbitrary formula (`src/L/Axioms/Full.lagda.md:144`),
which is `[LJ-1.560]`'s gift as `[LJ-1.568]` records it
(`Probe568.agda:185-188`). Had a Δ₀ grade been required, difference 3 above
would have cost real work.

## WHAT I COULD NOT CLOSE

**1. THE ARBITRARY CASE, AND I DID NOT TRY.** The brief forbade it and
`[LJ-1.533]` refuted it (`agents/tasks/LJ-1-533/lj-1.533-report.md:42-43`). The
difference is exactly one Π, and it is written as a TYPE at
`Probe586.agda:442-451` (`Arbitrary`) so it cannot be read out of the obligation
by mistake. **It is NOT inhabited and nothing here bears on whether it could be.**

**2. `src/` IS UNCHANGED, SO THE SITE STILL HAS AN OPEN PARAMETER.** See
`## PARAMETER OR TERM`. This is the one thing that keeps the result from
reaching `src/L/StageBound.lagda.md`, and it is a decision, not a gap in a proof.

**3. ROW 1 IS NOT CLOSED.** See `## WHAT B7 AND ROW 1 EACH GET`. `count`'s
recursion and `CodeSelect`'s selection are untouched.

**4. C-42's SWEEP, AND ITS COUNT IS IN THE PROBE.** The shape is "a bare `_↪_`
handed in as an open parameter and then consumed by a coding step".
`grep -rn "( *[A-Za-z][A-Za-z0-9'-]* *: *⟪.*⟫ *↪ *⟪.*⟫ *)" src/` returns SIX
lines over THREE objects (`Probe586.agda:416-428`):

| site | object | open? |
|---|---|---|
| `src/L/BoundedSubset.lagda.md:1392` | `absorbs` | YES, and this task pays it |
| `src/L/StageBound.lagda.md:69`, `:97` | the SAME object, passed on | YES |
| `src/L/StageCardinal.lagda.md:281`, `:397` | `ih`, the stage-bound induction hypothesis | YES, and it is `[LJ-1.584]`'s |
| `src/L/BoundedSubset.lagda.md:1409` | `CodeCount`'s `g` | NO: applied at `code-inj` (`:1515`) |

**SO THE OPEN ONES ARE TWO, AND THE SWEEP REACHES `[LJ-1.580]`'s PARTITION BY A
DIFFERENT ROUTE.** `[LJ-1.580]` named two uncoded things from the site's own
structure; this grep names two open `_↪_` parameters from the tree's syntax, and
they are the same two. That is the check C-42 asks for, and the answer is that
the cure was NOT funded against an unmeasured number.

**AND ONE NAMED NON-HIT.** `src/L/Absorption.lagda.md:635` carries the NAME
`absorbs` at type `⟪ sucV (fst γ) ⟫ ↪ ⟪ fst γ ⟫`, which does not fit the slot.
`archive/dev/LJ-dispatch-index.md:342` records `[LJ-1.284]` discharging THAT
one. It is a different statement at a different site and no line of this report
reads one as the other.

## ARCHIVE USED

**`archive/dev/LJ-dispatch-index.md` — READ AND USED, four rows.** It is the one
archive file that changed what this report says.

- `archive/dev/LJ-dispatch-index.md:338` reads
  `| LJ-1.280 | LAND A7 as src/L/GCH.lagda.md | LANDED GREEN, 63 LINES | sq and absorbs stay Pi-parameters, unsupplied and honestly so. The 47 code lines cost 0.16x the bar net of the header |`
  This is `## PARAMETER OR TERM`'s corroboration and it is 306 tasks old.
- `archive/dev/LJ-dispatch-index.md:342` reads
  `| LJ-1.284 | LAND A6 and A5 row 3, wave 3 | BOTH LANDED. A-PRIME IS COMPLETE | A6 525 lines at 1.04x the bar, row 3 at 0.69x. The re-site works. A6 DISCHARGES A7's absorbs, proved green |`
  This is the OTHER `absorbs`, and it is the named non-hit above.
- `archive/dev/LJ-dispatch-index.md:195` reads
  `| LJ-1.119 | Restrict absorbs-subset the way sq was restricted | ENTERED, make check PASSES | Devlin55 now has NO parameter. BoundedSubsetAt is entered at the site; the stop is levelIn and cover |`
  This is the precedent for exit 1 of `## PARAMETER OR TERM`: a parameter of this
  module has been closed once before.
- `archive/dev/LJ-dispatch-index.md:177` reads
  `| LJ-1.101 | Close the cardk type gap, then price sq | GAP CLOSED, GREEN | cardk checks at the master's IsCardinal, no transport. And absorbs-subset is REFUTED, so Devlin55 is vacuous |`
  Read as history only. `absorbs-subset` is not `absorbs` and its refutation was
  repaired at `[LJ-1.103]` (`:179`).

**`archive/dev/DD-archived.md` — READ AND USED, one row.**
`archive/dev/DD-archived.md:22` is DD4's archived text, cited in
`## WHAT THE SHAPE COST` as the historical home of the write-it-generic rule
that clause W2 now carries. It is cited as PROVENANCE and not as a rule in
force: the `DD` series is set aside in this form.

**`dev/ARCHIVE.md` — READ, NOT USED.** `grep -n "absorb|shift"` returns two rows,
`:271` and `:282`, both about `L.Godel.Operations` and `L.Godel.Tuples` and both
about a different "shift" (the assignments algebra of a retired
internalization cone). Nothing there bears on this obligation. Declined.

**`archive/dev/JOURNAL-archived.md` — READ, NOT USED.** Its `shift` hits
(`:130-131`) are the Closure chapter's "shift seek machinery", a different
object, and its `absorb` hits (`:528`, `:610`, `:879`, `:1433`) are the English
verb in planning prose. Declined.

**`archive/dev/JOURNAL.md` — READ, NOT USED.** `grep -n "absorb|shift"` returns
NOTHING in its 1,378 lines. Declined.

## LITERATURE USED

**`dev/literature/devlin-II5.md` — READ AND USED.**
`dev/literature/devlin-II5.md:118` reads `### 1.3 5.3: the definable hull`.
That section is the source of the hull this whole site is about, and it is why
"definable" is the right word for what `Def` asks: the object language, with
parameters, describing a member of the stage. It gives the mathematics; it gives
no term and this report takes none from it.

**`dev/literature/glossary-review-2026-08.md` — READ AND USED, for the word.**
`dev/literature/glossary-review-2026-08.md:394` reads `#### definable subset`,
and `:397` confirms the rendering. This report and the obligation's name use
"definable" in that settled sense, so no new term is coined and no
`dev/glossary.toml` entry is proposed.

**`dev/literature/truncation-and-selection.md` — READ, NOT USED.**
`dev/literature/truncation-and-selection.md:14` reads
`## 1. THE SET-THEORY SIDE: the least element under a definable well-order`.
That is about SELECTION under a well-order, which is `CodeSelect`'s problem and
therefore `[LJ-1.580]`'s leg 2, not this obligation. `absorbs` selects nothing:
it is a total function given by a three-way case split on `lem`. Declined, and
the reason is that it belongs to the OTHER half of row 1.

**`dev/literature/terms-2026-08.md` — READ, NOT USED.**
`grep -n "absorb|shift|definab"` returns NOTHING in its 573 lines. Declined.

**`dev/literature/digest.md` — READ, NOT USED.** Its `definab` hits (`:230`,
`:294`, `:332`, `:419`) are all about Σ-definability in J-structures and the
satisfaction-internalization route. This obligation asks for no Levy grade at
all (see `## WHAT THE SHAPE COST`), so the Σ hierarchy does not enter. Declined.
