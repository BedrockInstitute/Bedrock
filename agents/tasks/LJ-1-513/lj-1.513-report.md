# LJ-1.513 report: re-base the order on membership, so the predecessor set forms

## HEAD
head_slot: coder
machine: shared
verdict: GO

## VERDICT

**GO. The predecessor set forms, and the whole file is green.**
`agents/tasks/LJ-1-513/Probe513.agda`, exit 0, caliber `-A64m -I0 -M8g`, one
Agda process. `runs/full-1.out` to `runs/full-3.out`.

The obligation is delivered at `Probe513.agda:99-100`:

    preds : (a : S) → IsOrd (fst a) → S

It is not a weaker set. `preds-is-a` (`Probe513.agda:103-104`) proves
`fst (preds a oa) ≡ fst a` by extensionality, so the set has exactly the
members of `a` and nothing else.

**The obstruction is REMOVED, not relocated.** I measured both sides at the
same site in one file. The old order refuses:

    Probe513.agda:201.19-68: error: [UnequalSorts]
    Type (ℓ-suc ℓ) != Type ℓ

`runs/contrast-old-order.out`, exit 42. That reproduces
`agents/tasks/LJ-1-497/runs/cure-level.out` at this task's own site. The
re-based order at the same site is accepted: `Probe513.agda:177-178`, inside
the green file.

**AND THE ACCEPTANCE THAT FAILED IS THE ACCEPTANCE THAT NOW PASSES.**
`viaRankFamily` (`Probe513.agda:190-196`) is `Rank.go`'s own `boundingOrd`
line (`agents/tasks/LJ-1-490/Probe490.agda:145`) with the predecessor index in
place of the padded carrier, and with the recursive call taken as a
hypothesis. It typechecks. I did not build `swo-rank′` and I did not attempt
the adequacy.

**BUT READ `## C-42, THE SWEEP` BEFORE YOU PRICE THE CURE.** The re-basing is
green in a probe. In `src/` it is not one edit. All 16 importers of
`L.WellOrder.Base` take `ℓₚ = ℓ-suc ℓ` and none takes `ℓ`.

I did not postulate. I did not raise the carrier. I did not weaken the
predecessor set. Nothing landed in `src/`. I did not write a `review-of-*.md`,
because this is not a stop.

## D-10, BEFORE ANY AGDA

The brief asks where each piece lives, and then whether re-basing lowers the
level or only moves it. The answer came from four declarations and no Agda
was written until it was settled.

1. **The carrier is small.** `⟪_⟫ : (s : V ℓ) → Type ℓ`,
   `Cubical/HITs/CumulativeHierarchy/Properties.agda:220`.
2. **The comparison is large.** `_∈_ : (S T : V ℓ) → hProp (ℓ-suc ℓ)`,
   `Cubical/HITs/CumulativeHierarchy/Base.agda:31`. `_∈ᵗ_` is its underlying
   type and nothing more, `src/FOL/ZFStructure.lagda.md:94-95`.
3. **The order level is a module parameter, and it is the whole problem.**
   `module L.WellOrder.Base {ℓₚ : Level}`, `src/L/WellOrder/Base.lagda.md:54`,
   with `_<∙_ : A → A → Type ℓₚ` at `src/L/WellOrder/Base.lagda.md:103`.
   `[LJ-1.497]` set `ℓₚ = ℓ-suc ℓ` at `agents/tasks/LJ-1-497/Probe497.agda:31`,
   which is why `[LJ-1.490]`'s order reads
   `_≺_ : ⟪ α ⟫ → ⟪ α ⟫ → Type (ℓ-suc ℓ)`
   (`agents/tasks/LJ-1-490/Probe490.agda:167`).
4. **The small membership exists and it is small.**
   `_∈ₛ_ : (a b : V ℓ) → hProp ℓ`,
   `Cubical/HITs/CumulativeHierarchy/Properties.agda:239`, with the comment on
   line 238 of that file: "while ∈ is hProp (ℓ-suc ℓ), ∈ₛ is in ℓ".

**Does re-basing lower the level, or only move it? It lowers it, and the
reason is that the large level occurs only in PROOFS and never in a delivered
TYPE.** `ord-tri` concludes in `Tri A B : Type (ℓ-suc ℓ)`
(`src/L/Ordinal/Linear.lagda.md:133-134`) and `regularityV` is well-foundedness
for `_∈ᵗ_` (`src/V/Hierarchy.lagda.md:139`). Both stay large. But they are
consumed, not stated: `∈∈ₛ`
(`Cubical/HITs/CumulativeHierarchy/Properties.agda:251`) converts each one at
its own step, and every type this task delivers is at `Type ℓ`. A proof that
passes through a large type does not make its statement large.

I wrote the Agda only after that. The measurement below confirms it.

## 1. W3, THE LEVEL, FIRST

**GO, and it is the cheapest possible GO.** The brief asked for the type
alone:

    preds-type : (a : S) → IsOrd (fst a) → Type ℓ
    preds-type a _ = Σ[ x ∈ ⟪ fst a ⟫ ] ⟨ ⟪ fst a ⟫↪ x ∈ₛ fst a ⟩

Typechecked ALONE, with the obligation, the order and the acceptance omitted,
at 34 lines. Exit 0 on the first attempt. It is now `Probe513.agda:51-52` of
the kept file.

Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One Agda process. The
interface `_build/2.8.0/agda/agents/tasks/LJ-1-513/Probe513.agdai` was deleted
before every run.

- `runs/w3-1.out` 1.09 s, 271925248 bytes, exit 0
- `runs/w3-2.out` 1.07 s, 271892480 bytes, exit 0
- `runs/w3-3.out` 1.12 s, 271892480 bytes, exit 0

**W3 median wall 1.09 s. Peak RSS 271925248 bytes.** No heap event.

ESTIMATE for W3 was about 10 lines and under 25 seconds. **MEASURED: 34 lines
and 1.09 s.** The line estimate is off by 3.4x for one reason worth recording:
a type alone still needs the imports that name `S`, `IsOrd`, `⟪_⟫`, `⟪_⟫↪` and
`_∈ₛ_`, and that is 20 of the 34 lines. The Σ itself is 2 lines, as the brief
said.

## 2. THE OBLIGATION

`preds` is `Probe513.agda:99-100`, and its content is `module Preds`,
`Probe513.agda:60-97`, 45 lines including the two subset directions.

The set is `sett P ix` where `P` is the W3 type and `ix` takes the first
component (`Probe513.agda:65-72`). Two directions give extensionality:

- `into` (`Probe513.agda:75-80`): a member of the predecessor set is a member
  of `a`. It reads the second component of the pair, which IS the membership
  proof, so this direction is one `subst`.
- `outo` (`Probe513.agda:82-88`): a member of `a` is a member of the
  predecessor set. It takes the index through `fiber`
  (`src/V/Presentation.lagda.md:34`) and pairs it with `∈ₛ↪`
  (`src/V/Presentation.lagda.md:40-41`).

`is-α` (`Probe513.agda:90-91`) is `extensionality` applied to the pair.
`predsL` (`Probe513.agda:93-94`) transports `a`'s own `isL` backwards along it,
so the predecessor set is an object of L for free. `predsOrd`
(`Probe513.agda:96-97`) does the same for `IsOrd`.

**WHAT THE SHAPE RESISTED, AND THE NEXT BRIEF SHOULD KNOW IT.** Two implicit
arguments do not solve, and both cost a failed typecheck:

1. `mem-ord`'s `{A}` does not unify. `IsOrd A` is a pair of Π types
   (`src/L/Constructible.lagda.md:83-84,141-142`), so `A` is not determined by
   the `IsOrd A` argument, and `⟨ x ∈ˢ A ⟩` unfolds to `fst (x ∈ A)`, which is
   not injective in `A` either. Agda stalls on `fst (x ∈ _A) = fst (x ∈ α)`.
   Write `mem-ord {A = α}`. `[LJ-1.490]` and `[LJ-1.497]` both did
   (`agents/tasks/LJ-1-490/Probe490.agda:171`,
   `agents/tasks/LJ-1-497/Probe497.agda:160`) and neither report says why.
2. `_∈ᵗ_` is already a `Type` and not an `hProp`
   (`src/FOL/ZFStructure.lagda.md:94-95`). `⟨ x ∈ᵗ y ⟩` does not typecheck.
   `_∈ₛ_` and `_∈_` do need the bracket. In one file that mixes all three,
   this is the easy slip.

## 3. THE ORDER, RE-BASED

`module OrdSWO∈ₛ` (`Probe513.agda:113-155`) is `[LJ-1.490]`'s `OrdSWO`
(`agents/tasks/LJ-1-490/Probe490.agda:165-201`) with `_≺_` replaced by

    _≺ₛ_ : ⟪ α ⟫ → ⟪ α ⟫ → Type ℓ
    m ≺ₛ n = ⟨ ⟪ α ⟫↪ m ∈ₛ ⟪ α ⟫↪ n ⟩

at `Probe513.agda:115-116`, and with the import at
`Probe513.agda:32` giving `ℓₚ = ℓ`.

**All four laws survive, and each costs exactly one conversion.** `to∈` and
`fr∈` (`Probe513.agda:118-122`) are the two halves of `∈∈ₛ`. Then:

- `tri₁` (`Probe513.agda:127-135`): `ord-tri` unchanged, `fr∈` on the two
  strict cases, `↪-inj` unchanged on the equal case.
- `irr₁` (`Probe513.agda:137-138`): `to∈` then `∈-irrefl`.
- `trans₁` (`Probe513.agda:140-141`): `to∈` twice, transitivity, `fr∈` once.
- `wf₁` (`Probe513.agda:143-147`): `acc₁` unchanged except for `to∈` at the
  recursive step. `regularityV` still supplies the accessibility.

`w : SWO {ℓc = ℓ} ⟪ α ⟫` at `Probe513.agda:149-155`.

**`[LJ-1.497]` priced this as unmeasured: "the count of steps is not measured
and I will not price it from this task's seconds"
(`agents/tasks/LJ-1-497/lj-1.497-report.md:182-183`). THE COUNT IS FOUR
CONVERSIONS AND 43 LINES**, and no law needed a new proof.

**THE TREE'S PRECEDENT IS ABOUT THE RELATION AND NOT ABOUT THE LEVEL.** The
brief named `src/L/Cardinal.lagda.md:100`, which states
`SWO._<∙_ w m n ≡ ⟨ ⟪ sucV (fst α) ⟫↪ m ∈ˢ ⟪ sucV (fst α) ⟫↪ n ⟩`. That is
`_∈ˢ_`, the LARGE membership at `hProp (ℓ-suc ℓ)`, which is the order this
task replaces. So the precedent shows that an order can BE a membership. It
does not show that it can be the small one, and it did not transfer
(`AGENTS.md:45`). I re-measured at this site.

## 4. THE ACCEPTANCE

`module Accepts` (`Probe513.agda:164-196`) is the decisive part. `boundingOrd`
wants `X : Type ℓ` (`src/L/Ordinal.lagda.md:154`), and that is the acceptance
`runs/cure-level.out` refused. Three forms are accepted here:

- `viaSet` (`Probe513.agda:170-172`): the carrier of the obligation's own set,
  `⟪ predsV ⟫`, which is a `Type ℓ` because `predsV` is a `V ℓ`.
- `viaOrder` (`Probe513.agda:180-183`): `Σ[ x ∈ ⟪ fst a ⟫ ] (x ≺ₛ n)` at an
  arbitrary carrier element `n`. This is the exact Σ of `runs/cure-level.out`
  with the order re-based.
- `viaRankFamily` (`Probe513.agda:190-196`): the same index WITH the rank
  family, taken as a hypothesis `ih` rather than computed. It is
  `agents/tasks/LJ-1-490/Probe490.agda:145` with the padding removed.

The third is the one that matters, because the level could have moved from the
index into the family. It did not.

## WHERE THE LEVEL GOES

**BEFORE the re-basing.**

| piece | universe | evidence |
|---|---|---|
| carrier `⟪ α ⟫` | `Type ℓ` | `Cubical/HITs/CumulativeHierarchy/Properties.agda:220` |
| comparison `_∈_` | `hProp (ℓ-suc ℓ)` | `Cubical/HITs/CumulativeHierarchy/Base.agda:31` |
| `_∈ᵗ_`, its underlying type | `Type (ℓ-suc ℓ)` | `src/FOL/ZFStructure.lagda.md:94-95` |
| order `_<∙_` | `Type ℓₚ` | `src/L/WellOrder/Base.lagda.md:103` |
| `ℓₚ` as `[LJ-1.497]` set it | `ℓ-suc ℓ` | `agents/tasks/LJ-1-497/Probe497.agda:31` |
| `[LJ-1.490]`'s `_≺_` | `Type (ℓ-suc ℓ)` | `agents/tasks/LJ-1-490/Probe490.agda:167` |
| `Σ[ x ∈ ⟪ α ⟫ ] (x <∙ n)` | `Type (ℓ-suc ℓ)` | `agents/tasks/LJ-1-497/runs/cure-level.out` |
| the bundle `SWO {ℓc = ℓ} ⟪ α ⟫` | `Type (ℓ-suc (ℓ-suc ℓ))` | `src/L/WellOrder/Base.lagda.md:101` |
| what `boundingOrd` demands | `Type ℓ` | `src/L/Ordinal.lagda.md:154` |

**AFTER the re-basing.**

| piece | universe | evidence |
|---|---|---|
| carrier `⟪ α ⟫` | `Type ℓ`, unchanged | `Probe513.agda:115` |
| comparison `_∈ₛ_` | `hProp ℓ` | `Cubical/HITs/CumulativeHierarchy/Properties.agda:239` |
| `ℓₚ` | `ℓ` | `Probe513.agda:32` |
| order `_≺ₛ_` | `Type ℓ` | `Probe513.agda:115` |
| `preds-type` | `Type ℓ` | `Probe513.agda:51` |
| `Σ[ x ∈ ⟪ fst a ⟫ ] (x ≺ₛ n)` | `Type ℓ` | `Probe513.agda:177-178` |
| the bundle `SWO {ℓc = ℓ} ⟪ α ⟫` | `Type (ℓ-suc ℓ)` | `Probe513.agda:149` |
| `boundingOrd` on that Σ | accepted | `Probe513.agda:180-196`, `runs/full-1.out` |

**IS THE OBSTRUCTION REMOVED OR RELOCATED? REMOVED, from every type this task
delivers.** The large level survives in three consumed proofs and in no
statement: `ord-tri` (`src/L/Ordinal/Linear.lagda.md:133-134`), `regularityV`
(`src/V/Hierarchy.lagda.md:139`) and `isTransV`
(`src/L/Constructible.lagda.md:83-84`). Each is converted at its own step by
`∈∈ₛ`, at `Probe513.agda:118-122`, and none of them appears in `_≺ₛ_`, in
`preds-type`, in `preds` or in the index `boundingOrd` receives.

The bundle itself also drops one level, from `Type (ℓ-suc (ℓ-suc ℓ))` to
`Type (ℓ-suc ℓ)`. That was not asked for and I did not use it.

**ONE COST DOES MOVE, AND IT IS NOT A LEVEL.** `L.WellOrder.Base` at `ℓₚ = ℓ`
is a different module instance from `L.WellOrder.Base` at `ℓₚ = ℓ-suc ℓ`. Any
statement that must name both orders pays a conversion at each use. Inside
this probe nothing needs both, so the cost is zero here and is NOT measured
for `src/`. The sweep below is why that matters.

## C-42, THE SWEEP

C-42 says a refutation measures one site and never measures how far the shape
extends, so the count comes before the price. `[LJ-1.497]` refuted at one
site. Here is the count.

**Every importer of `L.WellOrder.Base` in `src/` takes `ℓₚ = ℓ-suc ℓ`. The
count is 16, and the count at `ℓₚ = ℓ` is 0.**

    src/L/StageCardinal.lagda.md:35        src/L/Choice/Transversal.lagda.md:65
    src/L/Cardinal.lagda.md:25             src/L/Choice/Table.lagda.md:59
    src/L/BoundedSubset.lagda.md:34        src/L/Choice/Name.lagda.md:55
    src/L/Absorption.lagda.md:25           src/L/Choice/Finite.lagda.md:69
    src/L/Hull.lagda.md:32                 src/L/Choice/Faithful.lagda.md:58
    src/L/Ordinal/SquareLaw.lagda.md:39    src/L/Choice/Order.lagda.md:70
    src/L/Choice/Internal.lagda.md:73      src/L/Choice/Step.lagda.md:58
    src/L/Choice/Limit.lagda.md:62         src/L/Choice/Adequate.lagda.md:60

`agents/tasks/LJ-1-513/Probe513.agda:32` is the FIRST instantiation at
`ℓₚ = ℓ` anywhere in the repository.

**WHAT THAT COUNT DOES AND DOES NOT SAY.** It says the re-based order is new
to the tree and that a route which carries it into `src/` creates a second
live instance of `L.WellOrder.Base`. It does NOT say the 16 break: I changed
no file under `src/` and I did not re-typecheck `src/`, so I have no
measurement of them. The next brief must not read this count as damage. It is
a count.

The counting leg touches at most two of the 16 today,
`src/L/StageCardinal.lagda.md:35` and `src/L/Cardinal.lagda.md:25`, because
those are the two the coded route already reads
(`agents/tasks/LJ-1-490/Probe490.agda:166` rebuilds `StageCardinal`'s
`OrdSWO`). **I did not measure that either. It is a reading of the imports and
not a dependency measurement.**

## WHAT THE REPLACEMENT RANK STILL OWES

Named as types. **None of them is built here.**

1. **The rank, by the recursion on the re-based order.** `Rank.go`'s
   `boundingOrd` line takes the predecessor index in place of the padded
   carrier, and `predAt` and `pred`
   (`agents/tasks/LJ-1-490/Probe490.agda:129-138`) are deleted with the
   padding they exist to supply.

        swo-rank′     : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ
        swo-rank′-ord : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
                      → IsOrd (swo-rank′ w a)

   `viaRankFamily` (`Probe513.agda:190-196`) shows the one line it needs is
   accepted. The recursion itself is not written.

2. **The property the refutation demands.** `[LJ-1.497]` refuted adequacy
   because `swo-rank` is never `∅`
   (`agents/tasks/LJ-1-497/Probe497.agda:435-451`). The replacement must take
   the value `∅` at a minimal element:

        swo-rank′-∅ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
                    → ((x : A) → SWO._<∙_ w x a → Empty.⊥)
                    → swo-rank′ w a ≡ ∅

   This is `[LJ-1.497]`'s `swo-rank′-least`
   (`agents/tasks/LJ-1-497/lj-1.497-report.md:199-201`) with the minimality
   hypothesis written out. I did not attempt it. It is plausible on the shape,
   because `boundingOrd` over an empty index unions an empty family
   (`src/L/Ordinal.lagda.md:156-160`), but plausible is not measured.

3. **The bound, rebuilt at the new rank.** `[LJ-1.490]`'s `Bound`
   (`agents/tasks/LJ-1-490/Probe490.agda:211-230`) reads `swo-rank`. It must
   read `swo-rank′`. `b` stays determined and does not become free
   (`agents/tasks/LJ-1-490/lj-1.490-report.md:271-272`).

4. **The second missing hypothesis, which the rank does not touch.**
   `[LJ-1.497]` measured that the adequacy needs `Q` read as the ∈-order on
   `a`, as a set of pairs
   (`agents/tasks/LJ-1-497/lj-1.497-report.md:211`), and `[LJ-1.475]` said
   it in prose (`agents/tasks/LJ-1-475/lj-1.475-report.md:249`). The
   re-basing does not supply it. **A rank alone will not make the adequacy
   true.**

5. **Then, and only then, the adequacy.** `rankFo-adequate′` as
   `[LJ-1.497]` stated it (`agents/tasks/LJ-1-497/lj-1.497-report.md:209-214`),
   and after it `range-clause` and the three other `InjCode` conjuncts
   (`agents/tasks/LJ-1-490/lj-1.490-report.md:275-279`). **I measured none of
   the four.**

**ONE THING IS EARNED RATHER THAN OWED.** `leastOf` demands
`LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))` (`src/L/WellOrder/Base.lagda.md:158`). At
`ℓₚ = ℓ-suc ℓ` with `ℓc = ℓ` that is `LEM (ℓ-max (ℓ-suc ℓ) ℓ'')`. At `ℓₚ = ℓ`
it is `LEM (ℓ-max ℓ ℓ'')`, one level cheaper. This probe does not use
`leastOf` and does not measure the saving. It is named because a consumer of
the re-based order gets it without asking.

## W2, ANSWERED

**The brief did not state clause W2, and W2 says the brief must**
(`dev/pod/instructions/coder.md`, the W2 paragraph). I answer it anyway.

Nothing here is written at a fixed carrier. `OrdSWO∈ₛ`
(`Probe513.agda:113`) takes a generic `α : V ℓ` with `IsOrd α`. `preds`
(`Probe513.agda:99`) takes a generic `a : S`. `viaRankFamily`
(`Probe513.agda:190`) takes a generic carrier element and a generic family.
The only fixed thing in the file is the order, and making it generic is what
the brief forbids: `SWO`'s `ℓₚ` is already the generic slot, and this task's
whole content is which value it takes.

## PRICES

Full file, 196 lines. Caliber `-A64m -I0 -M8g`, one Agda process, interface
deleted before each run.

- `runs/full-1.out` 1.16 s, 284491776 bytes, exit 0
- `runs/full-2.out` 1.16 s, 284491776 bytes, exit 0
- `runs/full-3.out` 1.15 s, 284557312 bytes, exit 0

**Full-file median wall 1.16 s. Peak RSS 284557312 bytes.** No heap event.

`runs/contrast-old-order.out` 1.14 s, 281133056 bytes, exit 42. It carries one
extra declaration, reverted before `full-1.out`.

ESTIMATE for the Agda was about 150 lines, of which about 30 the obligation.
**MEASURED 196 lines, of which the obligation is 45**
(`Probe513.agda:60-104`). The overshoot is sections 3 and 4, `Probe513.agda:106-196`, 91 lines, which
the brief did not price because it asked only for `preds`. I wrote them
because the title says re-base the order, and because `preds` alone would not
show that `boundingOrd` accepts the result.

Both prices are far under `[LJ-1.497]`'s (W3 1.80 s, full 2.67 s,
`agents/tasks/LJ-1-497/lj-1.497-report.md:56,153`). **Do not read that as
this task being three quarters the size of that one.** That file carried a
formula and a refutation chain; this one carries a set and an order. Sizes of
this shape are not comparable and nothing may be funded against them.

## WHAT I DID NOT DO

- No `swo-rank′`, and no adequacy. AD12 gives this brief one obligation.
- No `postulate`, no hole, no `TERMINATING`, no weakened pragma. The file
  keeps `--cubical --safe --guardedness` (`Probe513.agda:1`).
- No change under `src/`, and no `src/` typecheck.
- No `GHCRTS` change. The caliber on the pane was `-A64m -I0 -M8g` at the
  first command and at the last.
- No commit and no push.
- No `review-of-*.md`. This is a GO and not a stop.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`. **READ.** `archive/dev/JOURNAL.md:1356` reads
  "grep returns `pullOrder` (`src/L/Choice/Step.lagda.md:242`), `natOrder`".
  It records an earlier sweep over the delivered `SWO`s and it is why I ran
  the C-42 count over the importers rather than over the order names. That
  entry counts SWO INSTANCES; my count is of INSTANTIATION LEVELS, and the two
  are different questions.
- `archive/dev/JOURNAL-archived.md`. **READ.**
  `archive/dev/JOURNAL-archived.md:4175` reads
  "universe level.** Verified personally rather than from a report: the module".
  It records that the assembled `L ⊨ ZFC` takes the excluded middle and the
  universe level as its only assumptions. I read it to check that a second
  instance of `L.WellOrder.Base` would add no assumption. It adds none: the
  module has no `LEM` parameter (`src/L/WellOrder/Base.lagda.md:54`).
- `archive/dev/LJ-dispatch-index.md`. **NOT READ, declined.** It is an index of
  dispatches. The three predecessors this task needs were named in the brief
  with their paths, so the index adds nothing.
- `archive/dev/DECISIONS-archived.md`. **NOT READ, declined.** A bare `D<n>`
  resolves only against that archived series and this task cites no `D<n>`.
- `archive/dev/ORCHESTRATION.md`. **NOT READ, declined.** It is the archived
  loop document. This task is one dispatch inside the program and does not
  touch how the loop runs.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`. **READ.**
  `dev/literature/truncation-and-selection.md:134` reads
  "leastOf : {ℓ'' : Level} → LEM (ℓ-max ℓc (ℓ-max ℓₚ ℓ''))".
  That is the one place in the literature that names `ℓₚ` as a cost, and it is
  the source of the `leastOf` remark in
  `## WHAT THE REPLACEMENT RANK STILL OWES`.
- `dev/literature/devlin-II5.md`. **READ, and it did not decide anything.**
  `dev/literature/devlin-II5.md:291` reads
  "π⁻¹ : L_β → L_α (`dev2.txt:1302-1319`). 5.9 needs the predecessor function".
  Devlin's predecessor function is the `<_L`-predecessor on the constructible
  order and is a definability statement. This task's predecessors are
  ∈-predecessors inside one ordinal, and the obstruction is a universe level,
  which Devlin's setting does not have. **It does not transfer.**
- `dev/literature/digest.md`. **NOT READ, declined.** The digest is the
  cross-source summary. The two sources above answered the two questions this
  task had.
- `dev/literature/terms-2026-08.md`. **NOT READ, declined.** It is
  terminology, and this task mints no term and adds no glossary entry.
- `dev/literature/geology.md`. **NOT READ, declined.** Set-theoretic geology
  is not on the counting leg's route.
