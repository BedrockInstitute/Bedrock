# LJ-1.518 report: the hypothesis that links the formula's order to the rank's

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. The hypothesis is STATED, it is INHABITED at the ∈-order, and the whole
file is green.** `agents/tasks/LJ-1-518/Probe518.agda`, exit 0, caliber
`-A64m -I0 -M8g`, one Agda process. `runs/full-1.out` to `runs/full-3.out`.

The obligation is at `Probe518.agda:184-185`:

    ord-reads-Q : (Q a : S) → IsOrd (fst a) → Type (ℓ-suc ℓ)
    ord-reads-Q Q a oa = Site.Reads a oa Q

The witness is at `Probe518.agda:340-342`:

    ord-set-witness : (a : S) (oa : IsOrd (fst a))
                    → Σ[ Q ∈ S ] ord-reads-Q Q a oa

**ONE DEPARTURE FROM THE BRIEF, AND IT IS THE LEVEL.** The brief writes
`Type ℓ`. The type is `Type (ℓ-suc ℓ)` and no statement of this hypothesis can
be smaller. Section 2 gives the reason and the evidence. Nothing else in the
brief was changed: `rankFo` is not touched, `swo-rank′` is not changed, no
term is postulated, nothing landed in `src/`, and `rankFo-adequate′` is not
built.

I did not write a `review-of-*.md`, because this is not a stop.

## D-10, BEFORE ANY AGDA

The brief asks how the tree turns a SET into a RELATION, and whether `appAt`
reading `Q` at `(x, m)` is the same statement as `x ∈ m`. Both were settled
from declarations before any Agda was written.

**1. THE TREE TURNS ONE INTO THE OTHER THROUGH EXACTLY ONE TERM, AND THAT TERM
IS `appAt`.** `src/L/Coding/Model.lagda.md:160-161`:

    appAt : ∀ {n} → Fin n → Fin n → Fin n → Formula S n
    appAt f x y = ∃̇∈ (var f) (prAtL zero (suc x) (suc y))

and its adequacy, `src/L/Coding/Model.lagda.md:163-165`:

    appAt-adequate : ∀ {n} (f x y : Fin n) (γ : S ^ n)
      → (γ ⊨ appAt f x y)
      ≡ (pr (fst (lookup x γ)) (fst (lookup y γ)) ∈ fst (lookup f γ))

**So `appAt Q x m` IS `pr x m ∈ Q` and it is nothing else.** The encoding is
the Kuratowski pair `pr` of `V.Coding`, the one `rankFo` already reads
(`agents/tasks/LJ-1-497/Probe497.agda:228-229`) and the one `pr-inj` already
inverts (used at `Probe518.agda:311`). **I did not choose an encoding and I
did not invent one.** `Probe518.agda:133-140` writes that reading once, as
`PairOf`, and every clause of the file is stated against it. `pairOf-appAt`
(`Probe518.agda:137-140`) is `appAt-adequate` itself, so the identification is
in the file and not only in this paragraph.

**2. `appAt Q x m` IS NOT THE SAME STATEMENT AS `x ∈ m`, AND THAT GAP IS THE
WHOLE TASK.** `pr x m ∈ Q` is a fact about `Q`. `x ∈ m` is a fact about `x`
and `m`. Nothing connects them until something says what `Q` holds. **The
hypothesis is that sentence.** It is stated as two directions,
`Probe518.agda:154-165`:

    ReadsOut Q = (x m : S) → PairOf Q x m
               → Σ[ xa ∈ ⟨ fst x ∈ α ⟩ ] Σ[ ma ∈ ⟨ fst m ∈ α ⟩ ]
                   (ix x xa ≺ₛ ix m ma)

    ReadsIn  Q = (x m : S) (xa : ⟨ fst x ∈ α ⟩) (ma : ⟨ fst m ∈ α ⟩)
               → ix x xa ≺ₛ ix m ma → PairOf Q x m

    Reads Q = ReadsOut Q × ReadsIn Q

**`ReadsOut` SAYS THREE THINGS AND THE FIRST TWO ARE NOT DECORATION.** A pair
in `Q` has BOTH components in `a`. Without those two conjuncts the domain
clause of `fnAt` reads the Q-predecessors of `m` over the whole model
(`agents/tasks/LJ-1-497/Probe497.agda:228`, an unbounded `∀̇`), while the rank
reads them over `⟪ α ⟫` alone. The two sides would still not meet.

**3. THE RELATION IS NAMED AT THE INDICES, THROUGH `ix`.** `ix`
(`Probe518.agda:95-96`) is `fiber α h .fst`, which is the same line
`[LJ-1.497]` uses to feed the rank (`agents/tasks/LJ-1-497/Probe497.agda:207`,
`k = fiber (fst a) mx .fst`). It costs nothing, because `fiber` is the
UNTRUNCATED fiber of the presentation's embedding
(`src/V/Presentation.lagda.md:34`): a membership names an index with no choice
and no truncation to eliminate.

## 1. W3, THE WITNESS

**The brief ordered the witness written FIRST and typechecked ALONE.** I did
that, and the statement and the witness were green before one line of sections
5 or 6 existed. The slice is `agents/tasks/LJ-1-518/runs/w3-slice.agda.txt`:
it is the probe cut after `ord-set-witness`, which is sections 1 to 4 and
nothing else, and it is byte for byte the file the three W3 runs were taken
on.

**THE CONSTRUCTION IS THE ONE THE TREE ALREADY USES FOR AN ORDER AS A SET.**
`L.Choice.Limit` builds `codeOrder` as a separation out of a `smallDom` bound
over the pairs: the bound is `pairsBound`
(`src/L/Choice/Limit.lagda.md:418-419`) and the carve is
`src/L/Choice/Limit.lagda.md:607-608`. Three things change and no more:

- the index of the bound is `⟪ α ⟫ × ⟪ α ⟫` and not the pairs of `Lset ω`
  (`Probe518.agda:213-218`);
- the condition's comparison is `∈` and not the naming order
  (`Probe518.agda:233-241`);
- the condition carries two membership conjuncts that confine both components
  to `a` (`Probe518.agda:236-238`).

**BOTH BOUNDS ARE STAGES AND BOTH CONDITIONS MUST CONFINE, so the third change
is a change of MEANS and not a new duty.** `smallDom` returns `LsetS β oβ`
(`src/L/Recursion.lagda.md:134`), a stage, so each bound holds far more than
the pairs its chapter wants. `L.Choice.Limit` confines its two components
inside its comparison, through `LevelAt` in `LimitOrdAt`
(`src/L/Choice/Limit.lagda.md:463-465`), because a level order already names
where its arguments live. **The ∈-order names nothing**, so the confinement has
to be written beside the comparison, and that is what the two conjuncts are.
Without them the carve would take every pair in the stage whose first component
is a member of its second.

**`smallDom` (`src/L/Recursion.lagda.md:133`) accepts the family**, because
`⟪ α ⟫ × ⟪ α ⟫` is a `Type ℓ`. **`hasSeparationL`
(`src/L/Axioms/Full.lagda.md:144-145`) accepts the condition**, and it wants no
`Δ₀` certificate: it is separation for an ARBITRARY formula, with `lem` and
nothing else. That is why the witness is 128 lines
(`Probe518.agda:206-333`) and not a chapter.

**THE CARVE IS SEALED WHERE IT IS BUILT** (`Probe518.agda:245-251`), which is
the law `L.Choice.Limit` records at its own separation
(`src/L/Choice/Limit.lagda.md:604-605`). I did not measure the unsealed
variant, so nothing here is evidence about what it would cost. I sealed it
because the cure is free and the cited law names this exact site shape.

**ONE MEASUREMENT INSIDE W3, AND IT COST A RUN.** `ix` takes `x` EXPLICITLY.
An implicit `x` never solves, because `fst x` is not a pattern. The evidence is
`runs/w3-implicit-meta.out`, whose line 5 reads "when checking that the
expression x has type ⟨ fst _x_105 ∈ α ⟩": the argument's type never determines
`x`, and the elaborator says so at the first use
(`runs/w3-implicit-meta.out:2`, `Probe518.agda:97.53-54`, `[UnequalTerms]`).
The comment at `Probe518.agda:92-94` carries that citation.

**W3 median wall 1.82 s. Median peak RSS 338083840 bytes.** Three forced
rechecks, each with the probe's own interface deleted first: 1.82 s, 1.74 s,
1.83 s, at 358940672, 338083840 and 286556160 bytes. `runs/w3-1.out` to
`runs/w3-3.out`, all exit 0. **No heap event.** The RSS spread across the three
is 1.25x on a machine marked `shared`, so read the median as the figure and the
spread as the noise floor of this pane.

ESTIMATE for W3 was about 30 lines and under 45 seconds. **MEASURED 342 lines
in the slice and 1.82 s.** The wall time is 24 times inside the estimate. The
line count is not comparable to the brief's number and I say why in section 5:
the brief priced "the witness", and the slice that was checked alone also
carries the statement the witness inhabits, which is the obligation itself.

**THE BRIEF'S WARNING WAS RIGHT AND IT WAS NOT TESTED.** The brief said this
session had already lost three dispatches to a statement nothing satisfied
(`[LJ-1.507]`). **The witness typechecked at the first attempt.** Two runs were
spent before it and neither was spent on the witness: one on an import
(`isPropΣ` is in `Cubical.Foundations.HLevels`, not in `Cubical.Data.Sigma`,
which the Prelude re-exports at `src/Base/Prelude.lagda.md:169-170`) and one on
the implicit `x` above. So this task produced no evidence about how expensive
the `[LJ-1.507]` failure mode is. It produced only the fact that this
hypothesis is not in it.

## 2. THE OBLIGATION, AND THE LEVEL

`ord-reads-Q` is `Probe518.agda:184-185`. Its content is `module Site`,
`Probe518.agda:84-173`.

**THE BRIEF'S `Type ℓ` CANNOT BE MET, AND THE REASON IS STRUCTURAL RATHER THAN
A CHOICE I MADE.**

1. The hypothesis must constrain `Q` at ARBITRARY elements of the model and not
   only at members of `a`. `fnAt`'s domain clause is an unbounded `∀̇`
   (`agents/tasks/LJ-1-497/Probe497.agda:227-229`), so the set it pins is
   `{ x : S | pr x m ∈ Q }` over the whole carrier. A hypothesis that said
   nothing about `x` outside `a` would leave that set larger than the rank's
   predecessor set and the two sides would not meet.
2. `S` is the restricted structure's carrier, `Σ[ x ∈ S ] (x ∈ᶜ M)`
   (`src/FOL/ZFStructure.lagda.md:146`) at `𝒮ᵥ` and `isL`, and
   `V ℓ : Type (ℓ-suc ℓ)`
   (`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/CumulativeHierarchy/Base.agda:30`).
   **A statement that quantifies over `S` is at least `Type (ℓ-suc ℓ)`.**
3. `⟨ pr (fst x) (fst m) ∈ fst Q ⟩` is at `ℓ-suc ℓ` for the same reason:
   `_∈_` is `hProp (ℓ-suc ℓ)`
   (`.../CumulativeHierarchy/Base.agda:31`). `_∈ₛ_` is at `ℓ`
   (`.../CumulativeHierarchy/Properties.agda:239`) and I use it for the
   ORDER, which is why `_≺ₛ_` stays at `Type ℓ` (`Probe518.agda:89-90`). It
   does not rescue the quantifier.

**THE BRIEF'S OWN TWO LINES DISAGREE WITH EACH OTHER.** Its W3 type is

    ord-set-witness : (a : S) (oa : IsOrd (fst a)) → Σ[ Q ∈ S ] ord-reads-Q Q a oa

which names `S` twice, so it is a `Type (ℓ-suc ℓ)` whatever `ord-reads-Q`
returns. I delivered the obligation NAME at the level that can be written and
recorded the departure in the file head (`Probe518.agda:10-17`) as well as
here. **Nothing downstream is weakened by this**: the adequacy's own type is
already at `ℓ-suc ℓ` (`agents/tasks/LJ-1-497/Probe497.agda:275-280`).

**A `Type ℓ` STATEMENT ABOUT THIS SITE DOES EXIST, AND IT IS NOT THIS ONE.** A
statement purely about indices and `_≺ₛ_` stays at `Type ℓ`. It cannot say "z
is the pair of x and m", because that is an equation in `V ℓ`, and it cannot
quantify over the model. So it cannot be read by `appAt`. I did not build it,
because a hypothesis the formula cannot consume is not this task's deliverable.

## 3. THE ORDER IS THE RANK'S OWN ORDER

The brief asks for the hypothesis "at the ∈-order itself". A name that merely
looks like the ∈-order would not answer that, so the probe proves it.

`[LJ-1.515]`'s `OrdSWO∈ₛ` is rebuilt at `Probe518.agda:355-400`, from
`agents/tasks/LJ-1-515/Probe515.agda:244-286`. A probe does not import a probe,
so this is a rebuild and not a reference. Then `Probe518.agda:402-404`:

    site-is-swo : (a : S) (oa : IsOrd (fst a))
                → Site._≺ₛ_ a oa ≡ SWO._<∙_ (OrdSWO∈ₛ.w (fst a) oa)
    site-is-swo a oa = refl

**It is `refl`.** The relation the hypothesis is stated at and the relation
`swo-rank′` reads from its `SWO` argument
(`agents/tasks/LJ-1-515/Probe515.agda:112-113`) are ONE relation, definitionally.

## 4. WHAT THE HYPOTHESIS IS WORTH, MEASURED TWO WAYS

A hypothesis can fail in two directions. Nothing satisfies it, which is what
`[LJ-1.507]` delivered; or everything satisfies it, in which case it says
nothing. Section 6 of the probe answers the second.

**`reads-pins` (`Probe518.agda:465-472`).** Two sets that both satisfy the
hypothesis hold the same pairs. So the hypothesis DESCRIBES one set and is not
a filter many sets pass. `Q := ∅` passes it only where `a` has no member below
another, which is `q-min→min` read at every member.

**`dom-out` and `dom-in` (`Probe518.agda:423-437`).** The Q-predecessors of a
member are exactly its ∈-predecessors inside `a`. This is the reading `fnAt`'s
domain clause spends.

**`q-min→min` and `min→q-min` (`Probe518.agda:446-459`).** Q-minimal and
∈-minimal are ONE notion under the hypothesis. **This is the exact site of
`[LJ-1.497]`'s refutation.** That task took `Q := ∅`, which made every member
of `a` Q-minimal (`agents/tasks/LJ-1-497/Probe497.agda:365-368`), while
`swo-rank` had `∅` as a member at every member of `a`
(`agents/tasks/LJ-1-497/Probe497.agda:213-217`). With the hypothesis in the
telescope, `Q := ∅` is admissible only where the right-hand side of
`swo-rank′-∅` (`agents/tasks/LJ-1-515/Probe515.agda:218-221`) is satisfied,
and there the replacement rank IS `∅`. **The two sides now agree at the very
point where the old ones diverged.**

## WHAT THE ADEQUACY NEEDS NOW

**RESTATED WITH NO HOLES.** With `ord-reads-Q` in hand the statement is:

    rankFo-adequate′ :
        (Q a : S) (oa : IsOrd (fst a)) (z : S)
      → ord-reads-Q Q a oa
      → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
      → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
          (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))

**I DID NOT BUILD IT.** The brief forbids it and AD12 gives this brief one
obligation.

**EVERY INPUT IT NAMES, AND WHERE IT IS.**

| Input | Delivered | Where |
|---|---|---|
| `rankFo` | yes | `agents/tasks/LJ-1-497/Probe497.agda:255-264` |
| `ord-reads-Q` | yes | `agents/tasks/LJ-1-518/Probe518.agda:184-185` |
| a witness for it | yes | `agents/tasks/LJ-1-518/Probe518.agda:340-342` |
| `swo-rank′` | yes | `agents/tasks/LJ-1-515/Probe515.agda:112-113` |
| `swo-rank′-ord` | yes | `agents/tasks/LJ-1-515/Probe515.agda:115-117` |
| the SWO at the site | yes | `agents/tasks/LJ-1-515/Probe515.agda:280-286`, rebuilt at `Probe518.agda:391-397` |
| `swo-rank′-∅` | yes | `agents/tasks/LJ-1-515/Probe515.agda:218-221` |
| `swo-rank′-∅-only` | yes | `agents/tasks/LJ-1-515/Probe515.agda:228-231` |
| the minimal-case bridge | yes | `agents/tasks/LJ-1-518/Probe518.agda:446-459` |
| the domain reading | yes | `agents/tasks/LJ-1-518/Probe518.agda:423-437` |
| the formula's empty rank slot at a Q-minimal member | yes | `agents/tasks/LJ-1-497/Probe497.agda:329-334` |
| **`rank-at′`** | **NO** | see below |

**ONE INPUT IS NOT DELIVERED AND IT IS `rank-at′`.** The statement names the
rank as an element of the model, and nobody has packaged `swo-rank′` as one.
`[LJ-1.497]` has `rank-at` (`agents/tasks/LJ-1-497/Probe497.agda:203-207`), but
it is built on `swo-rank`, the rank `[LJ-1.497]` itself refuted. The
replacement is the same five lines with `swo-rank′` in place of `swo-rank`:

    rank-at′ : (a : S) (oa : IsOrd (fst a)) (m : S) → ⟨ fst m ∈ fst a ⟩ → S
    rank-at′ a oa m mx = r , isL-ord r (swo-rank′-ord w k)
      where
      w = OrdSWO∈ₛ.w (fst a) oa
      k = fiber (fst a) mx .fst
      r = swo-rank′ w k

`isL-ord` is `agents/tasks/LJ-1-497/Probe497.agda:149-150`, itself built from
`Lset→isL`, `suc-ord` and `ord∈Lset-suc`, all in `src/`. **`k` is my `ix`**:
`Probe518.agda:95-96` is that same `fiber` line, so the hypothesis and the
adequacy name the same index with no adapter between them.

**SO THE NEXT TASK IS THE ADEQUACY PLUS ONE FIVE-LINE PACKAGING**, and the
packaging cannot be skipped by importing this probe or `[LJ-1.515]`, because a
probe does not import a probe. **The next task rebuilds `rankFo`, `swo-rank′`
and `OrdSWO∈ₛ` in its own file.** That is roughly 40 lines from
`Probe497.agda:225-264`, 30 lines from `Probe515.agda:81-117`, 45 lines from
`Probe515.agda:244-286` and 90 lines from this file's sections 1 to 4, before
one line of the adequacy is written. **Do not price the adequacy against this
task's seconds**: this file forms a set and that one runs a satisfaction
relation on a five-slot environment.

## MEASUREMENTS

**Full-file median wall 1.91 s. Median peak RSS 372834304 bytes.** Three
forced rechecks: 1.98 s, 1.90 s, 1.91 s, at 294699008, 372834304 and 373866496
bytes. `runs/full-1.out` to `runs/full-3.out`, all exit 0. **No heap event.**
Caliber `-A64m -I0 -M8g`, taken from the pane and never set by me. One Agda
process at a time.

The forced recheck deleted `_build/2.8.0/agda/agents/tasks/LJ-1-518/Probe518.agdai`
before each run, so each number is the probe re-elaborated against warm
interfaces for `src/`. **A cold-tree number is not in this report and nothing
may be funded against these as if it were.**

## 5. ESTIMATE AGAINST MEASURED

ESTIMATE for the Agda was about 160 lines, of which the obligation about 40.
**MEASURED 472 lines, of which the obligation is 90** (`module Site`,
`Probe518.agda:84-173`). The file is 295 percent of the estimate and the
obligation 225 percent of it. The overshoot is four parts and I name each:

- section 3, the witness, `Probe518.agda:187-333`, 147 lines. The brief's W3
  estimate of 30 lines priced a witness that was already stated. This one
  carries the bound, the condition, the seal, and both directions of the carve
  read back through `pr-inj`.
- section 5, `Probe518.agda:344-404`, 61 lines, of which 46 are `[LJ-1.515]`'s
  order rebuilt. The brief asked for the hypothesis at the ∈-order and did not
  price the proof that the two relations are one.
- section 6, `Probe518.agda:406-472`, 67 lines. I wrote it because the required
  report section is answerable without it only by assertion.
- comments, 151 non-blank lines across the file, which carry the `file:line` of
  every predecessor claim. The 472 lines are 151 comment, 78 blank and 243 code.

**THE BRIEF'S ESTIMATE BASIS WAS SOUND AND THE NUMBER WAS STILL LOW.** The
brief said not to fund W3 against `[LJ-1.515]`'s numbers, because that ran a
recursion and this builds a set of pairs. That separation was correct: the
wall times are within a factor of 1.6 (1.16 s there, 1.82 s here) but the LINE
counts are not (77 there, 342 in the slice here). Nothing may be funded
against either.

## THE RATIO BAR

**THE RATIO BAR HAS NO DIVISOR ON THIS TASK.** The write scope is a raw
`.agda` probe, a report and `runs/`. No ` ```agda ` fence is created, so the
in-fence line count of the scope is 0 and the bar cannot fire. Nothing here is
evidence about what the bar would read if this hypothesis moved into `src/`.

## GATES RUN

- `scripts/gate/check-probes.py --check`: "check-probes: clean (5371 tracked
  files, no probe outside agents/tasks/ and no generated file)", exit 0.
- `scripts/gate/lint-agda.py --check`: exit 0, no output.
- `scripts/gate/lint-prose.py --check`: exit 0, no output.
- `scripts/gate/check-fences.py --check`: "check-fences: clean (102 masters,
  run threshold 3)", exit 0.
- `scripts/gate/check-rule-ids.py agents/tasks/LJ-1-518/lj-1.518-report.md`:
  "check-rule-ids: clean (1 files, 165 lessons, 68 decisions)", exit 0. The
  gate takes no `--check` flag.
- `make check` was NOT run and nothing is committed, per the Boundary. **The
  working tree holds three of the four scope paths and not the fourth**:
  `agents/tasks/LJ-1-518/Probe518.agda`, this report, and
  `agents/tasks/LJ-1-518/runs/` with eight files. There is no
  `review-of-*.md`, because this is not a stop. `git status --porcelain`
  returns one line, `?? agents/tasks/LJ-1-518/`.

**ONE NOTE ON THE TOOLING, AND IT IS NOT A DEFECT OF THIS TASK.** This worktree
has no `.venv`. I ran every gate above with the main checkout's interpreter,
`/Users/alsg/Agentic/Bedrock/.venv/bin/python`, from this worktree's root. I
did not create a venv here and I did not install anything.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: READ. `archive/dev/LJ-dispatch-index.md:207`
  reads "The tree already owns the order; V=L buys its DOMAIN." I searched the
  index for a retired attempt at a rank formula's adequacy, or at an order
  carried as a set of pairs. **The
  index is the retired route's dispatches and it has no row for either.** The
  live predecessors are `[LJ-1.475]`, `[LJ-1.490]`, `[LJ-1.497]`, `[LJ-1.513]`
  and `[LJ-1.515]`, all outside the archive.
- `dev/ARCHIVE.md`: READ. `dev/ARCHIVE.md:283` reads "A classical well-order
  over finite labelled trees by shortlex, generic in the alphabet's
  well-order." I checked the retired-module table for an order-as-a-set-of-pairs
  module, because W4 forbids rebuilding something
  retired for a measured reason. **There is none.** The two retired well-order
  modules, `L.WellOrder.Tree` and `L.Godel.Name`, are a shortlex tree order and
  stage names, and neither carries an order as a set of pairs.
- `archive/dev/DECISIONS-archived.md`: READ, and it settled nothing for this
  task. `archive/dev/DECISIONS-archived.md:8` reads "**Nothing here is live.
  Read it for history, and for what a citation means.**" No `D` row is cited by
  this task.
- `archive/dev/JOURNAL.md`: DECLINED. Measured: `grep -c` for
  `codeOrder|pairsBound|set of pairs|rankFo` returns 0.
- `archive/dev/JOURNAL-archived.md`: DECLINED, same measurement, also 0. Both
  are archived journals of the retired route, and the Boundary says a live
  document carries no history; nothing in this task rests on either.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: READ, and it is the file this
  task's proof obeys. `dev/literature/truncation-and-selection.md:143` reads
  `the reason: "a proposition-valued goal absorbs the truncation"`. **That is
  the exact law `rep` spends** (`Probe518.agda:287-330`): the condition of the
  separation is two truncated existentials, and the conclusion is eliminated
  into a `Σ` of propositions, whose `isProp` proof is `isPropReadsOut`
  (`Probe518.agda:167-173`). Without that the carve could not be read back at
  all.
- `dev/literature/devlin-II5.md`: DECLINED. It is the Condensation Lemma and
  the GCH in `L` (`dev/literature/devlin-II5.md:1`). This task is on the coding
  leg of the choice side and touches neither.
- `dev/literature/digest.md`: DECLINED. It pins the orthodox form of the rud
  route, which is the retired route.
- `dev/literature/terms-2026-08.md`: DECLINED. It is a terminology dossier for
  the owner's ruling and this task adds no term. I did not touch
  `dev/glossary.toml`.
- `dev/literature/geology.md`: DECLINED. Set-theoretic geology sources for
  `[L6]`, which is a registered campaign that opens after the trophies land.

## WHAT THE NEXT BRIEF NEEDS

1. **The coding leg has ONE task left and it is the adequacy.** Every input is
   delivered except the five-line `rank-at′` packaging, which the adequacy's
   own file writes.
2. **Price the next task as a REBUILD plus an adequacy.** About 205 lines of
   rebuild land before the first line of the proof, and none of it can be
   imported. That number is counted above and it is a shape, not a funding.
3. **The hypothesis's `ReadsOut` is where the proof will pull.** It hands back
   both memberships and the order fact in one shot, so the adequacy never has
   to invent a membership for a component it read out of a pair.
4. **`swo-rank′-∅-only` (`agents/tasks/LJ-1-515/Probe515.agda:228-231`) is not
   spent by this task and should be spent by the next one.** It is what stops
   the adequacy being satisfiable by a rank that is `∅` everywhere, which is
   the mirror of the defect `[LJ-1.497]` found.
5. **The level departure in section 2 is a fact about the site, not about my
   statement.** If a later brief wants `Type ℓ`, it is asking for a hypothesis
   the object language cannot read, and the answer will be the same.
