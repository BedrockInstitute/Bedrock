# LJ-1.544 report: B8 is built on the ladder, and the join goes to three unpaid

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-544/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process of mine at a time. I did not
set `GHCRTS`. Nothing is postulated, the file carries `--safe`, and there is no
hole. The probe is a raw `.agda` file, so it carries no ` ```agda ` fence,
counts 0 in-fence lines, and the ratio bar cannot fire on it.

**NO HEAP EVENT. THE ONE LONG RUN WAS A TIME BLOW-UP AND NOT A WALL.** Peak
footprint on the green file is 234,832,640 bytes, about 224 MiB, against an
8 GB cap (`runs/final-5.out`). TWO runs did not finish, `runs/full-1.out` and
`runs/s2-1.out`, and my own harness stopped both with SIGTERM, at 120 s and at
600 s. Neither reported exit 251 and neither printed a heap message. The cause
is the same for both, it is measured below, and it is an elaboration blow-up
and not memory.

**THE MACHINE IS SHARED AND ANOTHER SLOT WAS ON IT.** During these runs two
other workers held an Agda process: `agents/tasks/LJ-1-536/runs/Control536d.agda`
at 100 percent of one core, and later `agents/tasks/LJ-1-541/runs/BisB.agda`.
Neither is mine. The wall-clock figures below carry that load.

**GATES RUN, ALL EXIT 0.** `lint-prose`, `lint-agda`, `weave-i18n --check`,
`check-glossary`, `ledger --check`, `check-probes`, `check-closure`,
`check-spec-surface`, `check-fences` and `check-rule-ids`. I did NOT run
`make typecheck`, because no master changed. The worktree carries no `.venv`,
so every gate ran as `/Users/alsg/Agentic/Bedrock/.venv/bin/python`, the pinned
interpreter of the main checkout, with the working directory left in this
worktree.

## VERDICT

**GO. `LimitAbove` IS INHABITED** at `[LJ-1.523]`'s type, letter for letter.
The type is `agents/tasks/LJ-1-544/Probe544.agda:216-223` and the term is
`agents/tasks/LJ-1-544/Probe544.agda:225-228`. The obligation witness agrees:
`scripts/pod/witness.py` reports
`pass exit=0 agents/tasks/LJ-1-544/Probe544.agda::LimitAbove`, 0 UNRESOLVED of 1,
`probe_red=False`.

**THE ROUTE IS THE LADDER, AND THE FIT THAT `[LJ-1.543]` DID NOT TYPECHECK NOW
TYPECHECKS.** `Ladder` (`src/L/Reflect.lagda.md:256`) supplies three of the four
conjuncts. The fourth, successor closure, is not in that module, and it is paid
by a fourth term of the same module that `[LJ-1.543]` did not name:
`δ∈top→fin` (`src/L/Reflect.lagda.md:302`), the inversion of the limit's union.

**WHICH CONCLUSION I DELIVERED: THE EXPLICIT ONE, UNDER ONE `PT.map`.** The
brief permits a truncated existence. I did not need it. Section 4 of the probe
(`agents/tasks/LJ-1-544/Probe544.agda:183-203`) is the same construction with
the stage handed over, and it returns a BARE `Σ` with no `∥ … ∥₁` in its type
and none in its term. **So the truncation in B8's conclusion is exactly the
truncation already inside `isL` and the proof creates none.** The obligation is
that construction under one `PT.map`, four lines.

## THE FOUR CONJUNCTS, ONE LINE EACH

Required section. Each conjunct is paid, and the paying term is named at
`file:line`.

1. **`IsOrd lam`. PAID** by `Above.lam-ord`
   (`agents/tasks/LJ-1-544/Probe544.agda:140-141`), which is `Ladder.top-ord`
   (`src/L/Reflect.lagda.md:271`) and nothing else.
2. **`⟨ α ∈ˢ lam ⟩`. PAID** by `Above.into`
   (`agents/tasks/LJ-1-544/Probe544.agda:145-146`): rung zero is a member of the
   limit by `Ladder.G∈top` (`src/L/Reflect.lagda.md:274`), and the limit is
   transitive because it is an ordinal, so anything on rung zero is under the
   limit. `α` is on rung zero by section 2.
3. **`(d : SV.S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩`. PAID** by
   `Above.suc-closed` (`agents/tasks/LJ-1-544/Probe544.agda:151-167`). It uses
   `Ladder.δ∈top→fin` (`src/L/Reflect.lagda.md:302`) to put `d` on a rung, then
   `suc∈or≡` (`src/L/Ordinal/Stages.lagda.md:137`) to put `sucV d` on that rung
   or to identify it with that rung, and either way `sucV d` is a member of the
   next rung.
4. **`⟨ x ∈ˢ Lset lam ⟩`. PAID** by `Lset-mono`
   (`src/L/Constructible.lagda.md:355`) at
   `agents/tasks/LJ-1-544/Probe544.agda:197-198`, applied to `into β`, where `β`
   is the stage of `x` that section 1 returns. `β` is on rung zero by section 2.

**NONE OF THE FOUR IS UNPAID.**

## WHAT THE JOIN NOW STANDS AT

Required section. Counted from `[LJ-1.523]`'s own table
(`agents/tasks/LJ-1-523/lj-1.523-report.md:226-235`), rows B1 to B10, which are
the ten inputs the brief names.

| row | state today | evidence |
|---|---|---|
| B1 | PAID, in `src/` | `src/Landmarks.lagda.md:76-77` |
| B2 | PAID, in `src/` | `src/L/CantorBernstein.lagda.md:51-55` |
| B3 | PAID, in `src/` | `src/L/CantorBernstein.lagda.md:33-38` |
| B4 | PAID, in a probe | `agents/tasks/LJ-1-528/lj-1.528-report.md:339` names `Probe528.agda:696-697` |
| B5 | **UNPAID** | `agents/tasks/LJ-1-523/Probe523.agda:218-220`, STATED NOWHERE |
| B6 | PAID, in a probe | `agents/tasks/LJ-1-543/lj-1.543-report.md:29-30` names `Probe543.agda:125-130` |
| B7 | PAID, in a probe | `agents/tasks/LJ-1-540/lj-1.540-report.md:29-30` names `Probe540.agda:359-365` |
| B8 | **PAID BY THIS TASK, in a probe** | `agents/tasks/LJ-1-544/Probe544.agda:225-228` |
| B9 | **UNPAID** | `agents/tasks/LJ-1-523/Probe523.agda:258-261`, STATED NOWHERE |
| B10 | **UNPAID** | `agents/tasks/LJ-1-523/Probe523.agda:266-268`, STATED NOWHERE |

**SEVEN OF THE TEN ARE PAID AND THREE ARE UNPAID: B5, B9 AND B10.** This is a
count and not an estimate.

**WHAT "PAID" MEANS HERE, AND IT IS NOT THE SAME WORD IN EVERY ROW.** B1, B2 and
B3 are terms in `src/`. B4, B6, B7 and now B8 are terms in a probe under
`--safe`, and **NO ONE OF THE FOUR IS LANDED**. A landing is a separate price
and this task did not measure it.

**THE THREE THAT REMAIN ARE THE THREE THE BRIEF PREDICTED.** B9 and B10 name
`InjL` and want a code, and both routes to a generic code are closed by
measurement (`agents/tasks/LJ-1-533/lj-1.533-report.md`,
`agents/tasks/LJ-1-535/lj-1.535-report.md`). B5 wants the ambient fact out of
the internal one. **So no unpaid row is reachable by the method this task used,
and the ambient rows of the join are exhausted.**

## D-10, BEFORE ANY AGDA

**THE QUESTION THE BRIEF ORDERED: say at `file:line` what chain the ladder gets,
and say it before you build.**

**THE ANSWER: THE ITERATED SUCCESSOR OF ONE ORDINAL ABOVE BOTH `α` AND THE STAGE
OF `x`.** In full, and written before the Agda of sections 2 to 5:

- `Ladder` wants `G : ℕ → V ℓ` with `G-ord` and `G-up`
  (`src/L/Reflect.lagda.md:256-257`). I feed it `G 0 = sucV m`,
  `G (suc n) = sucV (G n)`, where `m` is section 2's merge of `α` and `β`.
  `G-ord` is `suc-ord` (`src/L/Ordinal.lagda.md:96`) by induction on `n`, and
  `G-up` is `self∈sucV` (`src/V/Model.lagda.md:236`) with nothing to prove.
- `m` is needed because `α` and `β` are unrelated. `ord-tri`
  (`src/L/Ordinal/Linear.lagda.md:136`) compares them and `sucV` of the larger
  holds both.

**THE GROUPING THE BRIEF ASKED FOR, AND THE BRIEF'S GUESS WAS RIGHT ON BOTH
GROUPS.**

- Group one, `IsOrd lam` and `⟨ α ∈ˢ lam ⟩`, is `top-ord` and `G∈top` with the
  rungs chosen above `α`. The brief said it had not typechecked this.
  **IT TYPECHECKS.** The only step the brief did not name is that `G∈top` puts
  the RUNG under the limit and not `α`, so the limit's own transitivity is
  needed once (`agents/tasks/LJ-1-544/Probe544.agda:146`).
- Group two, successor closure and `⟨ x ∈ˢ Lset lam ⟩`, is not in `Ladder`, as
  `[LJ-1.543]` said. **BOTH ARE REACHABLE ALL THE SAME.** Successor closure
  needs a term of the same module that `[LJ-1.543]` did not name, `δ∈top→fin`
  (`src/L/Reflect.lagda.md:302`), and `⟨ x ∈ˢ Lset lam ⟩` is one `Lset-mono`
  once `β` is under the limit.

**AND THE CONJUNCT THAT LOOKED HARDEST IS THE ONE WITH A PRECEDENT IN `src/`.**
`kappa-limit` (`src/L/SquareLawClosed.lagda.md:125-129`) is B8's third conjunct
at a different site: it says the cardinal `κL a oa` is closed under `sucV`. C-42
forbids reading one site as the other, and I did not: that term compares against
`ω` by trichotomy, my site inverts a union, and the two proofs share no step.
**The value of the precedent is that the conjunct's SHAPE was known to be
provable in this tree before I started.**

## W3, THE STAGE OF x, AND IT RAN FIRST

**THE QUESTION.** From `⟨ isL x ⟩`, an ordinal `β` with `⟨ x ∈ˢ Lset β ⟩`, or
the reason there is none.

**THE ANSWER: IT IS THE DEFINITION, AND THE TERM IS THE IDENTITY.**
`isL x = ⋁ S (λ α → (IsOrd α , isPropIsOrd α) ⊓ (x ∈ˢ Lset α))`
(`src/L/Constructible.lagda.md:376`). `⋁` is the library's truncated existential
(`src/Base/Truth.lagda.md:107`) and `⊓` is the library's meet
(`src/Base/Truth.lagda.md:100`), so `⟨ isL x ⟩` and
`∥ Σ[ β ∈ SV.S ] (IsOrd β × ⟨ x ∈ˢ Lset β ⟩) ∥₁` are the SAME type.
`stageOf x hx = hx` (`agents/tasks/LJ-1-544/Probe544.agda:67`) typechecks, and
that is the measurement.

**COST OF W3.** The slice was typechecked ALONE before sections 2 to 5 existed.
It is kept at `runs/w3-slice.agda.txt` and its runs are `runs/w3-1.out` to
`runs/w3-3.out`: exit 0 each, 0.80 s, 0.77 s and 0.78 s. **GREEN ON THE FIRST
ATTEMPT.** The brief estimated about 10 lines and under 30 seconds.
**Measured: 5 non-blank non-comment lines and 0.80 s.** The brief also said not
to fund W3 against `[LJ-1.543]`'s numbers, and nothing here is.

**THE CONSEQUENCE FOR THE OBLIGATION, AND IT IS THE WHOLE SHAPE OF THE ANSWER.**
Because `isL` is ALREADY the truncated existence of a stage, the obligation
splits with no residue: an explicit construction from an explicit `β`
(`agents/tasks/LJ-1-544/Probe544.agda:192-203`), and one `PT.map`
(`agents/tasks/LJ-1-544/Probe544.agda:226-228`). No untruncation is attempted
anywhere in the file, and none is needed.

## THE BLOW-UP, AND IT IS A LAW-SHAPED MEASUREMENT

**WRITING THE THREE-CASE MERGE WITH A NESTED `Sum.rec` RAN PAST TEN MINUTES.
WRITING THE SAME MERGE WITH AN EXPLICITLY TYPED `go` TAKES 0.94 SECONDS.** Both
forms prove the same thing and differ only in whether the elaborator has to
infer the branch type.

| run | what the file was | result |
|---|---|---|
| `runs/full-1.out` | sections 1 to 4, the merge as a nested `Sum.rec` | KILLED at 120 s by my harness |
| `runs/imports-1.out` | section 1 only, but every import the full probe wants | exit 0, 0.99 s |
| `runs/s2-1.out` | sections 1 and 2 only, the merge as a nested `Sum.rec` | KILLED at 600 s by my harness |
| `runs/bisectA-1.out` | `ord-tri` applied and nothing else | exit 0, 0.96 s |
| `runs/bisectB-1.out` | the three membership terms, no `Sum.rec` | exit 0, 1.01 s |
| `runs/bisectC-1.out` | the merge with an explicitly typed `go` | exit 0, 0.94 s |
| `runs/bisectD-1.out` | the same plus the ladder instantiation | exit 0, 0.96 s |
| `runs/full-2.out` | sections 1 to 4, the `go` form | exit 0, 1.00 s, GREEN FIRST TRY |
| `runs/full-3.out` | with the two surplus sections added | exit 0, 1.04 s |
| `runs/final-1.out` to `runs/final-3.out` | the SIX-section draft, 253 lines, before the two duplicate proofs were factored | exit 0, 1.03, 1.02 and 1.03 s |
| `runs/full-4.out` | restructured into the five sections of the final file | exit 0, 1.02 s |
| `runs/final-5.out` to `runs/final-7.out` | **the file EXACTLY as this report describes it**, 228 lines | exit 0, 1.04, 1.02 and 1.01 s |
| `runs/final-8.out` | the same file again, after this report was written | exit 0, 1.00 s |
| `runs/skip-5.out`, `runs/skip-6.out` | the same file NOT deleted first, so Agda skips it | exit 0, 0.91 and 0.92 s, and no "Checking" line |

Every run except the `skip-*` runs deleted
`_build/2.8.0/agda/agents/tasks/LJ-1-544/Probe544.agdai` first, because Agda
skips a file whose content is unchanged and a run that skips measures nothing.
`runs/skip-1.out` to `runs/skip-4.out` and `runs/final-1.out` to
`runs/final-3.out` are the EARLIER 253-line file and must not be read against
the final numbers. `runs/imports-only.agda.txt` is the source of
`runs/imports-1.out`, and `runs/w3-slice.agda.txt` is the source of
`runs/w3-1.out` to `runs/w3-3.out`.

**BOTH KILLED RUNS CARRY A COMMENT SAYING SO IN THE FILE ITSELF**
(`runs/full-1.out`, `runs/s2-1.out`). Each shows the "Checking" line and then
nothing, because SIGTERM stopped `/usr/bin/time` before it could print. Neither
is exit 251 and neither printed a heap message.

**THE ISOLATED CAUSE.** `ord-tri` alone is 0.96 s. The three membership terms
alone are 1.01 s. The ladder instantiation is free. **Only the combination is
slow, and only when the branch type is inferred.** The nested form asks Agda to
solve the result type of an inner `Sum.rec` that appears as an argument of an
outer `Sum.rec`, with `V ℓ` terms on both sides.

**WHY THIS IS THE SAME FINDING `[LJ-1.543]` MADE, ONE STEP LARGER.** That task
measured that `IsOrd` is a definition and not a constructor, so Agda cannot
invert `IsOrd _A =?= IsOrd (fst κ)` and the implicit must be given
(`agents/tasks/LJ-1-543/lj-1.543-report.md`, its W3 section). The same cause is
here: **the ordinal predicate and the membership proposition are both
definitions that unfold, so any goal the elaborator must GUESS at this carrier
is a goal it can unfold for a very long time.** The cure at both sites is the
same word: write the type down. **I do not propose it as a rule. It is two
measurements at two sites, and C-42 says the next step is a count and not a
cure.**

## THE NUMBERS

| item | estimate | measured |
|---|---|---|
| probe, total | about 120 lines | 228 lines, 194 non-blank, **106 non-blank non-comment** |
| the obligation `LimitAbove` alone, its term | about 30 lines | **4 non-comment** (`Probe544.agda:225-228`) |
| the obligation's TYPE, `[LJ-1.523]`'s letter for letter | not estimated | 8 non-comment (`Probe544.agda:216-223`) |
| the explicit core `limitAboveΣ` | not estimated | 11 non-comment (`Probe544.agda:192-202`) |
| the merge, section 2 | not estimated | 15 non-comment, of which the type is 4 |
| the ladder work, section 3 | not estimated | 31 non-comment |
| imports and the carrier preamble | not estimated | 24 non-comment |
| W3 | about 10 lines, under 30 s | 5 non-comment; 0.80, 0.77, 0.78 s (`runs/w3-1.out` to `runs/w3-3.out`) |
| typecheck, whole probe | not estimated | 1.04, 1.02, 1.01 and 1.00 s (`runs/final-5.out` to `runs/final-8.out`) |
| interface-load baseline, same file skipped | not estimated | 0.91 and 0.92 s (`runs/skip-5.out`, `runs/skip-6.out`) |
| elaboration of the whole probe | not estimated | **about 0.10 s**, and the paragraph below bounds it |
| peak footprint | not estimated | 234,832,640 bytes, about 224 MiB (`runs/final-5.out`) |
| attempts to green, after the form was fixed | not estimated | **ZERO red.** `runs/full-2.out` is exit 0 on the first run of sections 1 to 4 |
| attempts to green, counting the blow-up | not estimated | TWO runs killed on time, both the same cause |

**THE ELABORATION FIGURE IS DEFENSIBLE THIS TIME, AND THE BASELINE SPREAD SAYS
WHY.** The four skip runs on the final file and its immediate predecessor read
0.91, 0.91, 0.92 and 0.94 s, a spread of 0.03 s. The three green runs read 1.01
to 1.04 s. **So the whole probe elaborates in about 0.10 s, with an uncertainty
of about 0.03 s.** `[LJ-1.543]` could not resolve the same figure because its
baseline pairs differed by 0.09 s. This is a better-behaved measurement and not
a faster row: it is 0.10 s for 106 code lines against that task's upper bound of
0.15 s for 70.

**THE ESTIMATE WAS HIGH ON THE OBLIGATION AND CLOSE ON THE PROBE.** The brief
estimated about 30 lines for the obligation and about 120 for the probe.
**The obligation is 4 lines and the probe is 106 code lines.** The reason the
obligation is so small is section 1: `isL` is already the truncation, so the
obligation is one `PT.map` over a construction that does all of the work
untruncated. **The reason the probe is not smaller is that the four conjuncts
need a merge and a ladder that nothing in `src/` packages together.**

**THESE FIGURES ARE THE PROBE ALONE WITH THE TREE'S INTERFACES WARM ON A SHARED
MACHINE. THEY ARE NOT A CHAPTER PRICE AND MUST NOT BE QUOTED AS ONE.**

## WHAT THE ROW DOES NOT NEED, MEASURED BY THE ELABORATOR

1. **NO CODE AND NO FORMULA.** `InjCode` and `Formula` do not appear in the
   file, and `L.GCH`, `L.BoundedSubset` and `L.Definability` are not in the
   import list (`agents/tasks/LJ-1-544/Probe544.agda:16-32`). **So neither
   closed route of `[LJ-1.533]` and `[LJ-1.535]` is entered.** This confirms
   `[LJ-1.540]`'s split at one more row: B8 is ambient.
2. **NO MODEL AND NO L-CARRIER.** `FOL.ZFModel` is not imported and `𝒮ʟ` does
   not occur. The whole row lives at `𝒮ᵥ`, and `isL` enters only as a
   proposition about a `V ℓ` element.
3. **`lem` IS CONSUMED AT EXACTLY TWO PLACES.** `ord-tri` in section 2
   (`agents/tasks/LJ-1-544/Probe544.agda:92`), and `suc∈or≡` inside section 3
   (`agents/tasks/LJ-1-544/Probe544.agda:166`), which itself calls `ord-tri`
   (`src/L/Ordinal/Stages.lagda.md:139`). **Both are comparisons of two
   ordinals. The ladder needs no classical input at all.**
4. **NO HYPOTHESIS OF THE OBLIGATION IS SURPLUS.** All four binders of
   `LimitAbove` are read: `α` and `IsOrd α` by the merge, `x` by conjunct 4, and
   `⟨ isL x ⟩` by section 1. This is the same finding as `[LJ-1.543]` and the
   opposite of `[LJ-1.540]`'s at B7.

## W2 AND W4, ANSWERED

**W2.** The row is written once at the generic carrier `SV.S`, which is the
ambient `V ℓ`, and it is not instantiated at any second carrier. **There is no
fixed-form copy in this file, so W2 is not in conflict here.** The one place a
second form could appear is a landing in `src/`, and the brief forbids a
landing.

**W4.** No module is retired by this task, so the move-to-archive half has no
subject. The pricing half: **the ideal form written fresh today IS the file, and
I measured the alternative.** The first draft repeated the construction twice,
once truncated and once not, at 253 lines and 124 code lines. Factoring the
explicit core out and defining the obligation as one `PT.map` over it removed
the duplication and gave 228 lines and 106 code lines, with the same three green
runs. **That is 18 code lines saved and no proof changed**
(`runs/full-3.out` is the 124-line form, `runs/full-4.out` the 106-line form,
both exit 0).

## FOR THE MATHEMATICIAN

**THE AMBIENT ROWS OF THIS JOIN ARE NOW EXHAUSTED, AND THAT IS THE RULING THIS
TASK BUYS.** B4, B6, B7 and B8 are the four rows a build could reach without a
code, and all four are paid. **The three that remain each want something this
campaign has already measured as closed or as the direction that does not pay.**

**ONE THING I CAN SAY ABOUT B8 THAT THE JOIN MAY WANT LATER.** The `lam` this
row produces is closed under `sucV` and is above `α`, but **it is not proved to
be a limit in the stronger sense of "not a successor", and nothing in B8's type
asks for that.** If a later consumer wants `lam ∉ ω`, or `ω ∈ˢ lam`, neither is
delivered and neither is free: the chain starts at `sucV m` and says nothing
about `ω`. `kappa-limit` (`src/L/SquareLawClosed.lagda.md:125-129`) is the term
in `src/` that carries an `ω ∈ˢ κ` hypothesis for its own site, and it is the
place to look if that stronger form is ever priced.

**AND ONE COST FOR THE NEXT BRIEF.** This row imports `L.Reflect`, which is a
large chapter. The import costs nothing measurable here (0.99 s for imports
alone against 0.80 s with the small set, `runs/imports-1.out` against
`runs/w3-1.out`), because its interface is already built. **A landing would put
`L.Reflect` into the import closure of whatever module holds B8, and I did NOT
check that closure for a cycle.**

## WHAT I DID NOT DO

- I did not land anything in `src/`. The tree is unchanged outside
  `agents/tasks/LJ-1-544/`.
- I did not build B5, B9 or B10, and I did not build B4, B6 or B7. AD12 gives
  this brief one obligation.
- I did not postulate, and I left no hole.
- I did not set `GHCRTS`, and I ran one Agda process of mine at a time.
- I did not write `review-of-LimitAbove.md`. That file states a NO-GO and this
  is a GO.
- I did not kill the other slots' Agda processes, and I did not wait for them.
- **I did not price the LANDING of this row into `src/`,** and I did not check
  the import closure a landing would create.
- **I did not prove `lam` is not a successor, and I did not prove `ω ∈ˢ lam`.**
  Neither is in B8's type.
- I did not measure whether `Ladder` is the cheapest route. It is the route
  `[LJ-1.543]` named and the one the brief asked me to try.
- I did not run `make typecheck` and I did not run `make check`, because no
  master changed. `git status --porcelain` shows one entry, the untracked
  `agents/tasks/LJ-1-544/`, so a whole-tree typecheck would measure nothing
  about this task.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ AND USED.** `:351` is
  "| LJ-1.294 | Is an infinite cardinal a limit ordinal | PROVED. kappa-limit | Init's rows 1 to 3 are now available at the use site. Row 4, noinj-squared, has NO term anywhere in src/ |".
  That row sent me to `kappa-limit` (`src/L/SquareLawClosed.lagda.md:125-129`),
  which is B8's third conjunct at a different site. It told me the conjunct's
  shape is provable in this tree before I built anything. I did not reuse the
  term: C-42 forbids it and the two proofs share no step.
  I also read `:349`, "| LJ-1.292 | Sweep Key.lagda.md for the mixed spelling | THE SITE IS NOT CHARGED AT ALL. R-41 IS DEPTH-GATED | Key is cheap at 3,974 ms. The ladder: depth 2 is 219 ms, depth 3 is 9,286, depth 4 is 419",
  because it is the only other occurrence of the word "ladder" in the archive.
  **It is a different ladder**, a table of measured depths, and it has nothing
  to do with `L.Reflect`'s `Ladder`. Naming it here stops the next reader paying
  for the same search.
- `archive/dev/JOURNAL.md`: **DECLINED.** `:1` is "# ARCHIVED 2026-08-20". The
  per-episode journal is retired in favour of `agents/tasks/<CODE>/`, and the
  four predecessors this task needed, `[LJ-1.523]`, `[LJ-1.528]`, `[LJ-1.540]`
  and `[LJ-1.543]`, are all in those task directories. Not used.
- `archive/dev/JOURNAL-archived.md`: **DECLINED.** `:1` is
  "# Archived journal: the retired route". B8 is on the live route. Not used.
- `dev/ARCHIVE.md`: **DECLINED.** `:1` is "# ARCHIVE.md: the archive registry".
  It registers retired MODULES. This task retires none and lands nothing, so
  clause W4's move-to-archive half has no subject here. Not used.
- `archive/dev/DECISIONS-archived.md`: **DECLINED.** `:1` is
  "# Archived decisions: the D series". A bare `D<n>` is not a rule in force.
  Not used.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ AND USED, AND IT IS B8 IN ONE CLAUSE OF
  THE SOURCE.** `:152` is
  "The proof (`dev2.txt:1372-1384`): pick α < κ with x ⊆ L_α; take a limit λ"
  and `:153` continues
  "with x ∈ L_λ; by 5.4 take M ≺ L_λ with L_α ∪ {x} ⊆ M and".
  **"Take a limit λ with x ∈ L_λ" is exactly this obligation**, and the source
  spends five words on it inside the proof of 5.5. This task is the price of
  those five words: 106 code lines, of which 4 are the obligation and 46 are the
  merge and the ladder. **The source's silence is the reason the row was carried
  as unmeasured.**
- `dev/literature/truncation-and-selection.md`: **READ AND USED.** `:95` is
  "**This is the only free case.** Everything below is about paying for the rest."
  That sentence closes section 2.1, the free case of unique choice, and it is
  the reason I did NOT attempt an untruncation. The row does not need one:
  section 1 measures that `isL` is already the truncation of the stage, and the
  conclusion is truncated too, so the whole obligation lives inside `PT.map` and
  nothing is ever lifted out of a truncation. **The dossier's criterion at
  `:163-165` about a weakly constant endomap is not reached by this row.**
- `dev/literature/digest.md`: **DECLINED.** `:1` is
  "# Digest: the orthodox form of the rud route, pinned from the collected literature".
  B8 sits on the `Def` tower and no claim here turns on a rud fact. Not used.
- `dev/literature/terms-2026-08.md`: **DECLINED.** `:1` is
  "# The terminology dossier: fourteen renderings for the owner's ruling". This
  report names no new term and adds no glossary entry. Not used.
- `dev/literature/geology.md`: **DECLINED.** `:1` is
  "# Geology dossier: set-theoretic geology sources and the five questions".
  Set-theoretic geology is not on the `[LJ-1]` route and this row touches no
  ground model. Not used.
