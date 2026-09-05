# LJ-1.521 report: the adequacy, discharged on the replacement rank

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. `rankFo-adequate′` is built, with no holes, exactly as `[LJ-1.518]`
restated it.** `agents/tasks/LJ-1-521/Probe521.agda:1006-1023`, exit 0,
caliber `-A64m -I0 -M8g` taken from the pane, one Agda process.
`runs/full-1.out` to `runs/full-3.out`.

    rankFo-adequate′ :
        (Q a : S) (oa : IsOrd (fst a)) (z : S)
      → ord-reads-Q Q a oa
      → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
      → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
          (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))

**THE CONCLUSION IS NOT WEAKENED.** The equality is the one the brief wrote,
character for character. Nothing is postulated. Nothing landed in `src/`.
`swo-rank` is not restored. No `InjCode` conjunct is attempted.

**THE REPLACEMENT RANK FIXES WHAT IT WAS BUILT TO FIX.** W3, the adequacy at a
Q-minimal member, is `Probe521.agda:722-746`. It typechecked at the FIRST
attempt. `[LJ-1.497]` refuted the old adequacy at exactly that member, and the
new rank meets the formula there.

**TWO DEPARTURES FROM THE BRIEF, AND BOTH ARE SEALS, NOT WEAKENINGS.**
Sections 4 and 5 of this report give the measurement that forced each.
`swo-rank′` is `opaque` (`Probe521.agda:380-403`) and `rank-at′` is `opaque`
(`Probe521.agda:424-441`). Both keep their delivered types. `rank-at′` gains
one equation, `rank-at′-val` (`Probe521.agda:438-441`), which is `refl` inside
the block.

I did not write a `review-of-*.md`, because this is not a stop.

## D-10, BEFORE ANY AGDA

**THE BRIEF ORDERED ONE CHECK BEFORE ANY AGDA: is `[LJ-1.518]`'s `ix` the same
`fiber` line as `rank-at′`'s `k`. IT IS THE SAME LINE, and no adapter is
needed.**

`agents/tasks/LJ-1-518/Probe518.agda:95-96`:

    ix : (x : S) → ⟨ fst x ∈ α ⟩ → ⟪ α ⟫
    ix x h = fiber α h .fst

with `α = fst a` (`Probe518.agda:86-87`). `rank-at′` takes
`k = fiber (fst a) mx .fst` (the brief, and
`agents/tasks/LJ-1-497/Probe497.agda:207`). The two are one term: `ix m mx`
reduces to `fiber (fst a) mx .fst`.

**THREE THINGS MAKE THAT AN IDENTITY AND NOT A COINCIDENCE OF SPELLING.**

1. `fiber` is one term, `V.Presentation.fiber` (`src/V/Presentation.lagda.md:34`).
   `[LJ-1.518]` imports it (`Probe518.agda:35`) and `[LJ-1.497]` imports it
   (`Probe497.agda:25`). There is no second `fiber` in either file.
2. `fiber` takes `x` IMPLICITLY (`src/V/Presentation.lagda.md:34`), so the
   membership proof alone fixes the index. `ix m mx` and
   `fiber (fst a) mx .fst` therefore have the same implicit argument, `fst m`.
3. The relation is the same relation. `Site._≺ₛ_` and `SWO._<∙_ (OrdSWO∈ₛ.w …)`
   are equal by `refl` (`Probe521.agda:218-220`, which is `[LJ-1.518]`'s
   `site-is-swo`, `Probe518.agda:402-404`). So the hypothesis is stated at the
   order the rank runs on, and the index it names is the index the rank is
   applied at.

**I did not insert an adapter, and none was needed.**

## 1. W3, THE MINIMAL CASE

**The brief ordered it written FIRST, with the general case omitted, and
typechecked ALONE.** I did that. The slice is
`agents/tasks/LJ-1-521/runs/w3-slice.agda.txt`. It is this probe cut at the
line before section 9, and it is byte for byte the file the three W3 runs used.

The term is `adequate-min` (`Probe521.agda:722-746`):

    adequate-min :
        (z q m r f : S) (mx : ⟨ fst m ∈ α ⟩) → fst q ≡ fst Q
      → ((y : S) → PairOf Q y m → Empty.⊥)
      → Env.Fn z q m r f
      → Env.Sup z q m r f
      → fst r ≡ fst (rank-at′ a oa m mx)

**IT IS THE TWO SIDES OF `[LJ-1.497]`'s DIVERGENCE, NOW EQUAL.** The formula
side is `[LJ-1.497]`'s own two readings, rebuilt: a Q-minimal member gives a
pair-free `f` (`Probe521.agda:670-672`, from `Probe497.agda:299-312`), and a
pair-free `f` pins the rank slot with no member (`Probe521.agda:686-689`, from
`Probe497.agda:329-334`). The rank side is `swo-rank′-∅` at that member. The
bridge between the two notions of minimal is the hypothesis, inlined as
`qmin→min` (`Probe521.agda:714-719`, which is `[LJ-1.518]`'s `q-min→min`,
`Probe518.agda:446-452`).

**ONE STEP IS NEW AND THE BRIEF DID NOT NAME IT.** `sup-no-member` says no
ELEMENT OF THE MODEL is a member of `fst r`, because `extAt` quantifies over
`S` (`src/L/Coding/Model.lagda.md:662-664`). The `∅` law is about `V ℓ`. To
join them I lift: a member of a constructible set is constructible, so every
member of `fst r` is an element of the model. That is `memL`
(`Probe521.agda:445-447`), one line on `isL-trans`
(`src/L/Constructible.lagda.md:379`). The same lift is spent four more times in
section 9. **A statement that quantifies over `S` and a statement that
quantifies over `V ℓ` do not meet without it.**

**W3 TYPECHECKED AT THE FIRST ATTEMPT.** `runs/w3-try1.out`, exit 0, 3.23 s.
That run was on an earlier spelling of the slice; the three reported runs are
on the final bytes.

**W3 median wall 3.29 s. Median peak RSS 492421120 bytes.** Three forced
rechecks, each with the probe's own interface deleted first: 3.27 s, 3.30 s,
3.29 s, at 491372544, 492421120 and 492421120 bytes. `runs/w3-1.out` to
`runs/w3-3.out`, all exit 0. **No heap event.**

## 2. THE OBLIGATION

**THE SHAPE IS ONE WELL-FOUNDED INDUCTION AND ONE EXTENSIONAL IDENTITY, TWICE.**

`assignAt` says that `f`'s value at a member is the union of the successors of
`f`'s values at that member's q-predecessors. `swo-rank′` says that the rank at
an index is the union of the successors of the ranks at that index's
≺-predecessors. **The hypothesis is what makes those two families the same
family.** So the proof is:

- `key` (`Probe521.agda:883-887`), a well-founded induction on `⟪ α ⟫`: below
  the member the formula names, `f`'s value at a member IS the rank at that
  member's index. The step is `keyStep` (`Probe521.agda:807-881`), which takes
  its induction hypothesis EXPLICITLY, so the recursion is one line and the
  termination is on the `Acc` and nothing else.
- `top` (`Probe521.agda:895-946`): the same two directions at the top, where
  `supAt` pins `r` instead of `assignAt` pinning a value.

**THE ONE INPUT THE BRIEF DID NOT LIST, AND IT IS NOT `rank-at′`.** Both
directions need to know WHAT THE MEMBERS OF A RANK ARE. `[LJ-1.515]` proved the
rank is `∅` at a minimal element (`Probe515.agda:218-221`) and that a
predecessor's rank is a MEMBER (`Probe515.agda:224-226`). Neither says which
sets are members. `boundingOrd` exports only the membership of `f x` itself
(`src/L/Ordinal.lagda.md:155`). So this task states and proves the
characterization, in both directions:

- `bnd-out` and `bnd-in` (`Probe521.agda:290-313`), at `boundingOrd`, generic
  in the index type. This is clause W2: the fact is stated at a generic family
  and instantiated once.
- `rank-mem-out` and `rank-mem-in` (`Probe521.agda:393-403`), at the rank.

**`rank-at′` COST WHAT `[LJ-1.518]` SAID, PLUS THREE LINES.** The five lines
are `[LJ-1.518]`'s, unchanged. The three extra lines are type signatures for
the `where` bindings, which an `opaque` block requires: Agda never infers the
type of an opaque definition, `where` bindings included. That cost one run
(`runs/full-try6.out`, exit 42, `[MissingTypeSignatureForOpaque]` and then
`[UnsolvedConstraints]`).

**WHAT RESISTED IN THE MATHEMATICS: NOTHING.** `keyStep`, `key`, `top` and
`concl` were green at the first attempt, and they cost 3.59 s together
(`runs/bisect-top.out`). **What resisted was elaboration cost, and section 4 is
that finding.**

## 3. NON-VACUITY, PROVED IN THIS FILE

The brief asked which witness inhabits the antecedent and where it came from.
**I did not answer that with a citation. I rebuilt the witness here, and applied
the obligation to it.**

`[LJ-1.518]`'s `Witness` (`Probe518.agda:206-342`) is rebuilt at
`Probe521.agda:1046-1160`, against THIS file's `ord-reads-Q`. Then:

    rankFo-adequate′-nonvacuous :
        (a : S) (oa : IsOrd (fst a)) (z : S)
      → ⟨ (z ∷ []) ⊨ rankFo (ord-set-witness a oa .fst) a ⟩
      → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
          (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))

at `Probe521.agda:1169-1176`. It is `rankFo-adequate′` applied at
`ord-set-witness` and nothing else.

**A CITATION WOULD NOT HAVE SETTLED IT, AND THAT IS THE `[LJ-1.507]` LESSON.**
A probe does not import a probe, so `ord-reads-Q` had to be rebuilt here. A
rebuilt statement can differ from the statement that was inhabited, and the
difference would be invisible in a report. The witness in this file removes the
question: the antecedent `rankFo-adequate′` consumes is inhabited at EVERY
ordinal of the model, at the ∈-order, in the same file, and the Agda proves it.

The construction is not invented. It is `L.Choice.Limit`'s `codeOrder`: a
separation out of a `smallDom` bound over the pairs
(`src/L/Choice/Limit.lagda.md:418-419`, `:607-608`), which is what
`[LJ-1.518]` measured.

## 4. THE PRICE, AND THE ONE THING THAT RESISTED

**THE MATHEMATICS COST 3.6 SECONDS. ONE DEFINITION COST MORE THAN 571.** That
is the finding of this task, and it is worth more to the next brief than the
adequacy's own seconds.

**FIRST, THE MACHINE.** This pane is marked `machine: shared`, and the
repository runs a watchdog, `scripts/ops/agda-watchdog.sh`. It kills the
LARGEST `agda` process when SYSTEM free memory falls below 8 percent, whatever
that process is doing (`scripts/ops/agda-watchdog.sh:21-26`).
`_build/tools/agda-watchdog.log` records five kills during this task, at
12:36:56, 12:50:39, 13:09:02, 13:27:24 and 13:41:46, each with the reason
`free N% < 8%`. **My process peaked at 696614912 bytes, and the per-process cap
is 14 GB, so the 14 GB rule never fired.** The kills are the system rule.

**SO NO KILLED RUN IN THIS REPORT IS A PRICE.** Each is a LOWER BOUND on a run
that did not finish. I say which is which every time.

**THE BISECTION.** With the obligation written and the file not finishing, I cut
the file at four points and measured each. One Agda process at a time.

| file cut after | wall | exit | run |
|---|---|---|---|
| `keyStep` | 3.71 s | 0 | `runs/bisect-keystep.out` |
| `key`, `keyAll` | 3.66 s | 0 | `runs/bisect-key.out` |
| `top`, `concl` | 3.59 s | 0 | `runs/bisect-top.out` |
| `Tgt`, `isPropTgt` | did not finish | stopped | `runs/bisect-isprop.out` |

**THE WHOLE MATHEMATICS IS 3.59 SECONDS. `isPropTgt` IS THE COST.** It is not
a mathematical step at all. It is the proof that the conclusion is a
proposition, which is what lets the three existentials of `rankFo` be
eliminated.

**WHY IT COST.** The first spelling was the direct one:

    isPropTgt a oa z (m , (mx , e)) (m' , (mx' , e')) =
      ΣPathP (pm , ΣPathP (pmx , pe))
      where
      pm = ↾-reflects (pr-inj (sym e ∙ e') .fst)

**That puts `pm` inside a type family.** The elaborator then normalizes
`pr-inj … .fst` at a path argument. `pr-inj` (`src/V/Coding.lagda.md:178-179`)
classifies memberships of the Kuratowski pair, so normalizing it unfolds
`_∈ₛ_`, which is `repFiber ⟪ b ⟫↪ a`
(`Cubical/HITs/CumulativeHierarchy/Properties.agda:239-240`), which unfolds the
presentation's eliminator. The family also named `rank-at′`, and `rank-at′`
unfolds to `swo-rank′` at a CONCRETE `SWO` record, whose `wf∙` unfolds to
`regularityV`.

**THREE CURES, MEASURED IN ORDER. ONLY THE THIRD WORKED.**

1. Unsealed: still running at 570.93 s when the watchdog took it. Peak RSS
   663224320. `runs/full-try2.out`.
2. `swo-rank′` sealed `opaque` (`Probe521.agda:380-403`): still running at
   239.41 s when the watchdog took it. Peak RSS 696614912.
   `runs/full-try3.out`. **A 2.4x improvement, and not a cure.**
3. `rank-at′` sealed as well (`Probe521.agda:424-441`): stopped by me after
   about ten minutes. The run's own record carries the started line and no
   completion line, `runs/full-try4.out`. **Not a cure either.**
4. `isPropTgt` rewritten around `J` (`Probe521.agda:964-1000`): **2.53 s**
   (`runs/full-try5.out`, which the watchdog then killed at 18 percent free
   before the exit code was read; `runs/full-try7.out` is the same file, 4.78 s,
   exit 0).

**THE CURE IS ONE LINE OF DESIGN: THE MOTIVE DOES NOT NAME THE PATH.**

    Mot : (m'' : S) → m ≡ m'' → Type (ℓ-suc ℓ)
    Mot m'' _ = …
    atSame : {m'' : S} (q : m ≡ m'') → Mot m'' q
    atSame = J Mot base

Under `J` the path is APPLIED and never normalized. The only family left is at
a FIXED `m`, where `⟨ fst m ∈ fst a ⟩` is stuck on two variables. That is
`Probe521.agda:982-1000`.

**I KEPT BOTH SEALS, AND I SAY WHY RATHER THAN CLAIMING THEY ARE NEEDED.** With
the `J` form in place I did not re-measure the unsealed variants, so **this
report is NOT evidence that either seal is still load bearing.** I kept them
because each was measured to cut an unfinished run by a large factor while it
was the only change, and because `dev/ARCHIVE.md:271` records the opposite
case, where twelve seals bought the worst rate in an archival set. **A seal is
a measurement, not a habit, and re-measuring these two is a cheap thing for the
next task to do.**

## MEASUREMENTS

**Full-file median wall 5.30 s. Median peak RSS 677150720 bytes.** Three forced
rechecks: 5.30 s, 5.37 s, 5.25 s, at 677150720, 677150720 and 677117952 bytes.
`runs/full-1.out` to `runs/full-3.out`, all exit 0. **No heap event.** Caliber
`-A64m -I0 -M8g`, taken from the pane and never set by me. One Agda process at
a time.

The forced recheck deleted
`_build/2.8.0/agda/agents/tasks/LJ-1-521/Probe521.agdai` before each run, so
each number is the probe re-elaborated against warm interfaces for `src/`.
**A cold-tree number is not in this report and nothing may be funded against
these as if it were.**

The file is 1176 lines: 213 comment, 168 blank, 795 code.

## WHAT THE FOUR CONJUNCTS NEED NOW

`[LJ-1.490]` reported that all four conjuncts read the second component of a
pair in the carve and want this adequacy
(`agents/tasks/LJ-1-490/lj-1.490-report.md:275-280`). **With
`rankFo-adequate′` in hand, two of the four have every input, and two do not.
I did not build any of them.**

**ONE CHANGE BINDS ALL FOUR, AND IT IS IN THE TELESCOPE.** `RankCoded`
(`Probe490.agda:289-292`) quantifies over an arbitrary `Q`.
`rankFo-adequate′` consumes `ord-reads-Q Q a oa`. **So no conjunct is provable
at an arbitrary `Q`.** Either the telescope carries `hQ`, or `Q` is
instantiated at `ord-set-witness a oa .fst` (`Probe521.agda:1162-1164`). This
is not a hypothesis added to close a conjunct: it is the hypothesis
`[LJ-1.497]` proved the adequacy cannot do without, and `[LJ-1.518]` supplied.

**A SECOND CHANGE BINDS THREE OF THE FOUR.** `[LJ-1.490]`'s `Bound`, `C` and
`bnd` are built on `swo-rank` (`Probe490.agda:211-232`), the rank `[LJ-1.497]`
refuted. They must be re-based on `swo-rank′`. That is a re-spelling of eleven
lines and not a new proof, but it is not free and nobody has done it.

### `svAt` (`src/L/Coding/Model.lagda.md:210-214`): EVERY INPUT DELIVERED

`svAt-in` (`:238-240`) reduces it to: two values recorded at the same argument
are equal.

- `rank-graph-out` (`Probe490.agda:111-116`) turns each pair in the carve into
  satisfaction of `rankFo Q a`. DELIVERED.
- `rankFo-adequate′` (`Probe521.agda:1006`) turns each satisfaction into
  `fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx))`. DELIVERED.
- `pr-inj` (`src/V/Coding.lagda.md:178-179`) splits that into
  `fst x ≡ fst m` and `fst y ≡ fst (rank-at′ a oa m mx)`. DELIVERED.
- `↾-reflects` (`src/FOL/ZFStructure.lagda.md:164-167`) lifts `fst m ≡ fst m'`
  to `m ≡ m'`. DELIVERED.
- The membership `mx` is a proposition, so `rank-at′ a oa m mx` and
  `rank-at′ a oa m' mx'` agree. `isPropTgt` (`Probe521.agda:964`) is exactly
  this argument, already written. DELIVERED.

**So `svAt` is `isPropTgt` read at two members of the carve.**

### the range clause (`Probe490.agda:276-280`): EVERY INPUT DELIVERED

The clause is `(x y : S) → ⟨ pr (fst x) (fst y) ∈ fst G ⟩ → ⟨ fst y ∈ fst C ⟩`.

- The adequacy gives `fst y ≡ swo-rank′ w (ix m mx)`. DELIVERED.
- `boundingOrd`'s own third component gives
  `⟨ swo-rank′ w k ∈ β ⟩` at every index (`src/L/Ordinal.lagda.md:155`, and
  `Probe490.agda:213` is where the pack is formed). DELIVERED, once the pack
  is re-based on `swo-rank′`.

**So the range clause is the adequacy plus one projection.** This is the
conjunct `[LJ-1.490]` called the fourth and could not close
(`agents/tasks/LJ-1-490/lj-1.490-report.md:264-266`). **It closes now.**

### `injAt` (`src/L/Coding/Injection.lagda.md:44-48`): ONE INPUT MISSING, AND
IT IS ONE LINE

`injAt-in` (`:72-75`) reduces it to: two arguments with the same value are
equal. The adequacy reduces that to: `swo-rank′ w j ≡ swo-rank′ w k` implies
`j ≡ k`.

- **NOT DELIVERED as a named term.** `[LJ-1.515]` has `swo-rank′-mem`
  (`agents/tasks/LJ-1-515/Probe515.agda:224-226`), which is strict
  monotonicity, and this probe does not rebuild it.
- **IT IS ONE LINE FROM WHAT THIS PROBE DOES HAVE.** `rank-mem-in`
  (`Probe521.agda:399-403`) at `u := swo-rank′ w j`, with `self∈sucV`
  (`src/V/Model.lagda.md:236-237`), gives `swo-rank′ w j ∈ swo-rank′ w k`
  whenever `j ≺ k`. Then trichotomy (`SWO.tri∙`,
  `src/L/WellOrder/Base.lagda.md:99-105`) and `∈-irrefl`
  (`src/V/Hierarchy.lagda.md`, imported at `Probe521.agda:44`) give
  injectivity.

**So `injAt` needs one lemma, and the lemma is arithmetic on delivered parts.
It is not a wall.**

### `domAt` (`src/L/Coding/Model.lagda.md:278-280`): ONE HALF DELIVERED, ONE
HALF IS THE NEXT REAL GAP

`domAt` is two implications and they are not the same size.

- **`domAt-out` (`:289-292`), the domain is inside `a`: DELIVERED.** The
  adequacy gives `m` with `fst x ≡ fst m` and `mx : ⟨ fst m ∈ fst a ⟩`.
- **`domAt-in` (`:294-296`), every member of `a` is in the domain: NOT
  DELIVERED, and nothing in the tree supplies it.** It asks for the CONVERSE of
  this task's obligation: given `⟨ fst x ∈ fst a ⟩`, that
  `rankFo Q a` IS SATISFIED at the pair of `x` and its rank, and that this pair
  is a member of the bound.

**THAT CONVERSE IS A SEPARATE THEOREM AND I NAME IT PLAINLY.** This task proved
that a satisfying `z` IS a member-and-rank pair. It did not prove that every
member-and-rank pair satisfies. The two are independent. `[LJ-1.497]` built a
satisfaction witness (`Probe497.agda:380-428`), but for `Q := ∅` and for the
REFUTED rank, and that witness exists to make its refutation unconditional. It
is not this converse and it does not transfer.

**THE CONVERSE MUST EXHIBIT AN APPROXIMATING FUNCTION `f`**, that is, the
graph of `swo-rank′` restricted to the ∈-predecessors of a member, AS A SET OF
THE MODEL, and prove it satisfies `fnAt`, `assignAt` and `supAt`. `[LJ-1.518]`'s
`Witness` is the model for how such a set is carved
(`Probe521.agda:1046-1160` here). **That is the next task, and it is bigger
than this one was.**

The second half also needs `Bound.below` (`Probe490.agda:221-232`) re-based on
`swo-rank′`.

### summary

| conjunct | every input delivered | what is missing |
|---|---|---|
| `svAt` | YES | nothing |
| range clause | YES | nothing, once `Bound` is re-based |
| `injAt` | NO | rank injectivity, one lemma from `rank-mem-in` and `self∈sucV` |
| `domAt` | HALF | the CONVERSE of this adequacy, which is a new theorem |

## 5. ESTIMATE AGAINST MEASURED

**ESTIMATE for the Agda was about 220 lines, of which the obligation about 60
and `rank-at′` about 8. MEASURED 1176 lines.** The file is 535 percent of the
estimate. I name each part, because the estimate was not wrong about the shapes
it priced.

- **`rank-at′`: estimated about 8, measured 8 plus 3.** The five-line body is
  `[LJ-1.518]`'s, exactly. Three lines are the signatures the `opaque` block
  requires. **The estimate was right.**
- **The obligation: estimated about 60, measured 273** (section 9,
  `Probe521.agda:751-1023`). Of that, `keyStep` is 75 lines
  (`:807-881`), `top` is 52 (`:895-946`), `key` and `keyAll` are 7
  (`:883-889`), `concl` is 3 (`:948-950`), `Tgt` and `isPropTgt` are 42
  (`:959-1000`), and the elimination of the three existentials is 18
  (`:1006-1023`). The rest is the comments that carry section 4's
  measurements.
- **What the estimate did not price at all is the REBUILD, and it is 507
  lines.** `Site` and `ord-reads-Q` are 51 (`:113-163`), `OrdSWO∈ₛ` and
  `site-is-swo` are 47 (`:174-220`), the formula is 46 (`:456-501`), the
  environment readers are 178 (`:512-689`), and the witness is 115
  (`:1046-1160`), plus `Rank′` and the `∅` law inside `:228-402`. A probe
  does not import a probe, so every one of these is paid again here.
  **`[LJ-1.518]` said this in its own report and gave the number as roughly
  205 lines; it was low by a factor of about 2.5, because it did not price
  the environment readers.**
- **The rank block, `:228-402`, is 175 lines and it is NOT all rebuild.**
  `bnd-out` and `bnd-in` (`:290-313`) and the two `go-mem-*` laws inside
  `Rank′Laws` are new, and so is the `opaque` interface (`:380-402`).
  `[LJ-1.515]` never stated what the members of a rank are.
- Comments are 213 non-blank lines, which carry the `file:line` of every
  predecessor claim and of every measurement in section 4.

**ESTIMATE for W3 was about 30 lines and under 45 seconds. MEASURED 25 lines
for the term and 3.29 s for the slice.** The TERM matched the estimate. The
SLICE is 748 lines, because it carries the whole rebuild. **These are two
different numbers and the brief priced the first one. Nothing may be funded
against the second.**

**THE BRIEF'S WARNING NOT TO FUND W3 AGAINST `[LJ-1.518]`'s NUMBERS WAS RIGHT,
AND FOR A REASON THE BRIEF DID NOT GIVE.** `[LJ-1.518]` measured 1.82 s for W3
and 1.91 s for its whole file. This task's whole file is 5.30 s, 2.8x that. The
cause is not the adequacy. It is that this file carries `[LJ-1.518]`'s file
almost entirely, plus `[LJ-1.515]`'s, plus `[LJ-1.497]`'s formula, plus the
new work. **The rebuild rule makes each dispatch on this chain cost the sum of
its predecessors. That is now measurable: 500 of 1176 lines and roughly half
the seconds are rebuild.**

## THE RATIO BAR

**THE RATIO BAR HAS NO DIVISOR ON THIS TASK.** The write scope is a raw
`.agda` probe, a report and `runs/`. No ` ```agda ` fence is created, so the
in-fence line count of the scope is 0 and the bar cannot fire. Nothing here is
evidence about what the bar would read if this adequacy moved into `src/`.

**ONE THING IS EVIDENCE FOR WHEN IT DOES.** The bar is 0.0123 seconds per
in-fence line. This probe is 795 code lines at 5.30 s, which is 0.0067 s per
code line, and about half of those lines are rebuild that would not be
duplicated in `src/`. **A master would be smaller and the rate is inside the
bar today.** Both seals of section 4 would move with it, and their measured
basis moves with them.

## GATES RUN

- `scripts/gate/check-probes.py --check`: "check-probes: clean (5444 tracked
  files, no probe outside agents/tasks/ and no generated file)", exit 0.
- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.
- `scripts/gate/check-fences.py --check`: "check-fences: clean (102 masters,
  run threshold 3)", exit 0.
- `scripts/gate/check-rule-ids.py agents/tasks/LJ-1-521/lj-1.521-report.md`:
  see below.
- `make check` was NOT run and nothing is committed, per the Boundary. **The
  working tree holds three of the four scope paths and not the fourth**:
  `agents/tasks/LJ-1-521/Probe521.agda`, this report, and
  `agents/tasks/LJ-1-521/runs/` with its run records and the W3 slice. There is
  no `review-of-*.md`, because this is not a stop. `git status --porcelain`
  returns one line, `?? agents/tasks/LJ-1-521/`.

**ONE NOTE ON THE TOOLING, AND IT IS NOT A DEFECT OF THIS TASK.** This worktree
has no `.venv`. I ran every gate with the main checkout's interpreter,
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, from this worktree's root. I
did not create a venv here and I did not install anything. `[LJ-1.518]`
reported the same condition, so it is now two dispatches old.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ.
  `archive/dev/LJ-dispatch-index.md:411` reads "At the BARE record adequacy is
  FALSE: its equality is not forced to be a path". I searched the index for a
  retired attempt at a rank formula's adequacy, and for any earlier adequacy
  that was refuted for a stated reason. **The index has nine rows that name an
  adequacy and none of them is this one.** The row above is the nearest: it
  records an adequacy that was FALSE at the wrong generality, which is the
  failure mode `[LJ-1.497]` measured here. The live predecessors of this task,
  `[LJ-1.490]`, `[LJ-1.497]`, `[LJ-1.513]`, `[LJ-1.515]` and `[LJ-1.518]`, are
  all outside the archive.
- `dev/ARCHIVE.md`: READ, and it changed what section 4 of this report says.
  `dev/ARCHIVE.md:271` reads "Measured 0.257 s per obligation, 3.48x the 0.074
  benchmark, the worst rate in the set". That row is `L.Godel.Operations`,
  which carried twelve `opaque` blocks and still had the worst rate of its
  archival. **I read it because this task added two seals, and it is the
  standing evidence in this repository that a seal is not automatically a
  win.** Section 4 records both seals as measured-while-alone rather than as
  proved-still-needed because of it.
- `archive/dev/JOURNAL.md`: DECLINED. Measured: `grep -c -E
  'rankFo|swo-rank|rank formula'` returns 0.
- `archive/dev/JOURNAL-archived.md`: DECLINED. Measured: the same `grep -c`
  returns 0.
- `archive/dev/PLAN-archived.md`: DECLINED. Measured: the same `grep -c`
  returns 0.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: READ, and it is the document
  that names this task's real difficulty.
  `dev/literature/truncation-and-selection.md:143` reads
  `the reason: "a proposition-valued goal absorbs the truncation"`. **That
  sentence is the whole of section 9.1.** `rankFo` has three existentials, so
  the adequacy can only be extracted into a proposition, and `isPropTgt` is the
  absorber. The document also records the constraint that made the cost
  possible: the payload a truncation releases must be proposition-valued, so
  the work goes into proving `isProp`, not into the mathematics. **Section 4
  measured exactly that: 3.59 s of mathematics and an unfinished run of
  absorber.**
- `dev/literature/devlin-II5.md`: DECLINED for this task.
  `dev/literature/devlin-II5.md:304` reads "Chapter 13 shows an alternative
  engine, a Π₂ adequacy sentence absolute for". Its subject is the adequacy of a
  LEVEL-HOOD sentence and its complexity class. This task's "adequacy" is the
  agreement of one formula with one recursion at one site, at no complexity
  class at all. **The word is shared and the subject is not.**
- `dev/literature/terms-2026-08.md`: DECLINED. It is a naming dossier;
  `dev/literature/terms-2026-08.md:66` reads
  "  and 接口 (interface, already used for the adequacy interface,". This task
  adds no `dev/glossary.toml` entry and names nothing in Chinese.
- `dev/literature/digest.md`: DECLINED. `dev/literature/digest.md:218` reads
  "  and J_α^A = S_α^A at limit α (I.1); the rank jump per S-step is finite."
  That is the rank of the FINE-STRUCTURAL hierarchy. This task's rank is the
  ordinal a well-founded recursion assigns to an index. Same word, different
  object.
- `dev/literature/geology.md`: DECLINED. `dev/literature/geology.md:64` reads
  "  study of whether very large (rank-into-rank style) cardinals can be".
  Set-theoretic geology is not on this campaign's route.
