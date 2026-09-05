# LJ-1.424 report: untruncate a CODED injection

slot: `coder`. Written early as a skeleton and filled as runs landed
(C-22). No commit, no push. I wrote only in `agents/tasks/LJ-1-424/`.
Agda ran under the caliber the program set on this pane,
`GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-424/Probe424.agda`, at a
GENERIC pair of L-elements `a b : S`, with `L.Cardinal`'s own site bound
in scope (`open SiteBound a`, `src/L/Cardinal.lagda.md:163`):

    coded-to-arrow : ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁
                   → ⟪ fst a ⟫ ↪ ⟪ fst b ⟫

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]` (`dev/pod/direction.md:38`). This task is still LJ-1 work. It
does not start that collection. It does not start phase 3. No Boundary
clause is in conflict. Nothing was written into `src/`.

## VERDICT

**GO.** The obligation typechecks
(`agents/tasks/LJ-1-424/Probe424.agda:90-95`, exit 0, median 1.65 s on
three forced rechecks) and it PASSes the program's witness meter
(`python3 scripts/pod/witness.py --code LJ-1-424 --brief
agents/tasks/LJ-1-424/LJ-1.424.md`, exit 0, 1.64 s, 0 UNRESOLVED of 1,
`probe_red=False`). `.venv/bin/python` is absent in this worktree. The
witness meter ran under `python3`. I added no dependency.

The fourth conjunct fits `leastOf`'s level. The range clause has an
`isProp` witness at that level. `readL`'s result is `_↪_`
definitionally. No ambient injection sits in the telescope, truncated
or otherwise. The telescope is `{ℓ}` and `lem : LEM (ℓ-suc ℓ)` and
then `a b : S`.

This GO is at the CODED site. It does not inhabit
`[LJ-1.422]`'s `kappa-arrow-data`. C-42: a measurement of one site
does not measure the other.

## D-10: WHY THIS SITE IS NOT THE SITE THAT FAILED

Written before any Agda. The two sites share `leastOf`. They do not share
a payload.

**THE AMBIENT SITE, `src/L/Cardinal.lagda.md:117`.** `leastOf w lem InjP'
nonempty` selects an INDEX `γ-card : ⟪ sucV (fst α) ⟫` as DATA. The
predicate `InjP'` at `:82-83` is `InjP (up γ)`, and `InjP` at `:66-67`
is `∥ Inj γ ∥₁ , squash₁` with `Inj γ = ⟪ fst α ⟫ ↪ ⟪ fst γ ⟫` at
`:63-64`. The payload of that predicate is an injection. An injection is
a function type. It is not an hProp. The chapter states the consequence
at `:132`: "-- The witness, an injection, still truncated, still not an hProp."
The returned witness `κ-inj` at `:133-134` is
`∥ ⟪ fst α ⟫ ↪ ⟪ fst κ ⟫ ∥₁`. `leastOf` at
`src/L/WellOrder/Base.lagda.md:158-160` demands `P : A → hProp ℓ''`. The
index comes out as data. The injection stays truncated.

`[LJ-1.422]` measured that site and returned NO-GO. Sibling
`/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-422/agents/tasks/LJ-1-422/lj-1.422-report.md:14-18`
reads:

    **NO-GO.** The truncated arrow is delivered. The data form is a
    choice of one of several injections. No live untruncation device
    covers that carrier. The orthodox size proof does not name this
    arrow as data. The missing device is a well-order on the injections.
    It is absent.

That report's carrier is the injection type itself
(`lj-1.422-report.md:74-75`). No delivered `SWO` has that carrier
(`lj-1.422-report.md:110-111`). This task does not inhabit that type.

**THE CODED SITE, this task.** The carrier is `Mem (Lset β)`, a member of
a stage. `orderAt β oβ` at `src/L/Choice/Step.lagda.md:730` is an `SWO`
on that carrier. The payload IS the index: a member `F` of `Lset β`. The
predicate on that member is `InjCode (up F) a b` at
`src/L/Cardinal.lagda.md:223-228`. That type is four conjuncts:

1. `⟨ (F ∷ a ∷ []) ⊨ svAt zero ⟩`
2. `⟨ (F ∷ a ∷ []) ⊨ domAt zero (suc zero) ⟩`
3. `⟨ (F ∷ a ∷ []) ⊨ injAt zero ⟩`
4. `((x y : S) → ⟨ pr (fst x) (fst y) ∈ fst F ⟩ → ⟨ fst y ∈ fst b ⟩)`

Conjuncts 1 to 3 are carriers of hProps by construction. Conjunct 4 is a
Pi into a membership, and membership is an hProp. The predicate is a
satisfaction fact. It is an hProp by construction. `[LJ-1.401]` already
delivered the witness: `isPropInjCode` at
`agents/tasks/LJ-1-401/Probe401.agda:48-53`, GO at
`agents/tasks/LJ-1-401/lj-1.401-report.md:16-21`. That report is not
NO-GO. It does not name the statement FALSE. This probe reconstructs
that witness at `Probe424.agda:64-69`. It does not assert one.

`leastOf` on this predicate therefore returns the member AND the four
conjuncts as DATA. The payload is a proposition, so it comes out
(`dev/literature/truncation-and-selection.md:146-148`). That is Devlin's
least-witness guard (`dev/literature/devlin-II5.md:129`) in the form
`IsLeast` already has (`src/L/WellOrder/Base.lagda.md:130-131`).

**THE DIFFERENCE, IN ONE LINE.** Ambient: the index is a stage-member and
the payload is a function, so the function stays truncated. Coded: the
index is a stage-member and the payload IS that member's satisfaction,
so the satisfaction comes out as data, and `readL` reads a function from
it.

This is not the site that failed. The missing device at the ambient site
is a well-order on the injections. The device at this site is the
well-order the tree already has on stage members, plus one constructible
graph.

D-26 at `dev/LESSONS.md:1735-1743`: a stage built as the values of
finitely many total operations carries generation data, so a well-founded
key exists. `orderAt` is that key (`src/L/Choice/Step.lagda.md:17-20`,
birth ordinal as primary key). An ambient function type carries no
generation data. That is why 422's carrier has no `SWO` and this carrier
does.

## 1. What was built

All in `agents/tasks/LJ-1-424/Probe424.agda`, module
`LJ-1-424.Probe424 {ℓ} (lem)`, inner `module _ (a b : S)`.

- `clause4` and `clause4-isProp` (`:56-62`). The range clause of
  `src/L/Cardinal.lagda.md:228`, with its `isProp` witness: three
  `isPropΠ` and `snd` of membership. Same construction as
  `agents/tasks/LJ-1-401/Probe401.agda:39-45`, which returned GO.
- `isPropInjCode` (`:64-69`). Three `isProp×` then `clause4-isProp`.
  Generic in `F a b`. Reconstruction of
  `agents/tasks/LJ-1-401/Probe401.agda:48-53`.
- `Good4` (`:80-81`). `Canonical.Good` at
  `src/L/Cardinal.lagda.md:187-190` has three conjuncts at `Ω`. This
  predicate packs the four conjuncts of `InjCode` as
  `hProp (ℓ-suc ℓ)`, the level `src/L/Cardinal.lagda.md:239` already
  uses. The fourth conjunct is the range clause.
- `good-four-selects` (`:83-86`). One `leastOf (orderAt β oβ) lem Good4`.
  Same call the chapter feeds at `src/L/Cardinal.lagda.md:195`. The
  input is the truncated coded existence. The output is the least
  member and `IsLeast`.
- `coded-to-arrow` (`:90-95`). `readL a b` on `up (fst chosen)` and
  the four conjuncts `fst (snd chosen)`. No rebuild of `Small`. No
  rebuild of a coding primitive.

`grep` of `Canonical` in `src/` returns two hits:
`src/L/Cardinal.lagda.md:182` (the definition) and
`src/Base/Classical.lagda.md:119` (a different module). The chapter's
selection still has no consumer in `src/`.

## 2. W3: `good-four-selects`

**GO.** Typechecked ALONE, with the `readL` import and `coded-to-arrow`
omitted, result discarded. Caliber `-A64m -I0 -M8g`, set on the pane,
untouched. One Agda process. The probe interface was deleted before
every kept run (`_build/2.8.0/agda/agents/tasks/LJ-1-424/Probe424.agdai`).

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.60 | 404537344 |
| `runs/w3-2.out` / `w3-2.time` | 1.54 | 404537344 |
| `runs/w3-3.out` / `w3-3.time` | 1.52 | 406634496 |

Median wall **1.54 s**. Median peak RSS **404537344 bytes**. No heap
event.

The fourth conjunct fits `leastOf`'s level: `Good4` is
`hProp (ℓ-suc ℓ)` and `lem : LEM (ℓ-suc ℓ)` is the level
`InternalLeastCard.Good` already uses
(`src/L/Cardinal.lagda.md:239`). The range clause has its `isProp`
witness at that level (`clause4-isProp`, `Probe424.agda:60-62`).
Neither NO-GO condition fired.

## 3. Import cost of `L.CantorBernstein`

Plain wall figure, separate from W3. After W3 was green I added

    open import L.CantorBernstein {ℓ} lem using ( readL )

at `Probe424.agda:37`, plus `coded-to-arrow`. `L.CantorBernstein.agdai`
and `L.GCH.agdai` were already present under `_build/2.8.0/agda/src/L/`.
I did not delete another chapter's interface.

First full check after the import: 1.52 s, RSS 404537344
(`runs/full-1.out` / `full-1.time`), exit 0. Against W3's median 1.54 s
the delta is not a wall. No heap event. Loading the compiled interface
did not move the figure.

## 4. Step two: `readL` and `coded-to-arrow`

**GO.** `readL` at `src/L/CantorBernstein.lagda.md:33-35` returns

    Σ[ f ∈ (⟪ fst a ⟫ → ⟪ fst b ⟫) ]
        ((x y : ⟪ fst a ⟫) → f x ≡ f y → x ≡ y)

`_↪_` at `src/L/Cardinal.lagda.md:47-48` is

    X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)

The two are the same Sigma. `coded-to-arrow` typechecks with no
coercion and no packager (`Probe424.agda:93`). The result is `_↪_`
definitionally. One repackaging is not needed.

I did not rebuild `Small`. The chapter warns that an unsealed `Small`
application exhausts an 8 GB heap
(`src/L/InjChain.lagda.md:550-551`). `readL` already carries that
application (`src/L/CantorBernstein.lagda.md:36-38`). Applying it
cost one call.

Three forced rechecks of the full file, exit 0 every time:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.64 | 404537344 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.67 | 404537344 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.65 | 404553728 |

Median wall **1.65 s**. Median peak RSS **404537344 bytes**. No heap
event.

## 5. W2 (DD4)

The mathematics is written once at a generic carrier. `isPropInjCode`
is generic in `F a b`. `Good4`, `good-four-selects` and
`coded-to-arrow` sit in `module _ (a b : S)` and open `SiteBound a`.
They name no cardinal, no band, no numeral and no ordinal other than
the `β` that `SiteBound a` produces. The term does not know what `b`
is. Both proofs can share this code: the carrier is a pair of
L-elements, not a named cardinal.

## 6. What the input still costs

A GO here untruncates a code that already exists at `SiteBound.β a`.
It does not produce that existence. The input

    ∥ Σ[ F ∈ Mem (Lset β) ] InjCode (up F) a b ∥₁

is a truncated existence of a graph inside `Lset (stageBound (fst a))`.
That is a stronger demand than an unbounded `∥ Σ[ F ∈ S ] InjCode F a b ∥₁`.
The graph has to live at the stage bound of the domain `a`.

`[LJ-1.414]` measured the ambient-to-coded direction and did not
prove it. `agents/tasks/LJ-1-414/lj-1.414-report.md:20` reads:
"**Answer 3. NOT DECIDABLE in this tree.**" and `:39` reads: "So the
statement is not proved and not refuted." HALF A remains the bill
(`lj-1.414-report.md:42-43`).

`[LJ-1.411]` takes an unbounded truncated code and returns a code as
data at the least ordinal that carries one
(`agents/tasks/LJ-1-411/Probe411.agda:82-83`). That stage is not
`SiteBound.β a`. This term starts after the existence is already sited
at `SiteBound.β a`.

The remaining cost is that sited truncated existence. This dispatch
does not price it. A measured cure does not transfer by analogy.

## 7. What this GO says to `[LJ-1.422]`'s sentence, and what it does not

`[LJ-1.422]` named the missing device for the untruncated AMBIENT
arrow as a well-order on the injections, absent from the tree
(`lj-1.422-report.md:17-18`). That sentence stays true of that carrier.
C-42: this GO does not move it.

What GO says: the tree untruncates a CODED injection with the
well-order it does have (`orderAt` on `Mem (Lset β)`). At this site
the missing device is not a well-order on the injections. It is one
constructible graph, selected as the least member of a four-conjunct
predicate, then read by `readL`.

What GO does not buy: an untruncated equivalence, and an untruncated
ambient arrow from a truncated ambient injection. The archived wall
on the equivalence remains
(`archive/dev/JOURNAL-archived.md:1732`).

Shape comparable, never a size comparable:
`src/L/Cardinal.lagda.md:182-211` is `Canonical` in 30 lines. This
probe's obligation body is `Good4` plus `good-four-selects` plus
`coded-to-arrow` (`Probe424.agda:80-95`). Nothing is funded against
the estimate.

Predecessor of the same SHAPE, not this task's comparable of size:
`agents/tasks/LJ-1-386/Probe386.agda:264-283` (`code-untruncates`)
and `agents/tasks/LJ-1-314/CodeUntrunc.agda:122-128` (`codeInj`).
Both used `Small` directly. This task used `readL` and measured W3
first. `[LJ-1.401]` delivered `isPropInjCode` as GO. I reconstructed
it. I did not import that probe.

What resisted: nothing. The types matched. No weakening.

What the next brief needs: a producer of the sited truncated
existence, or a ruling that the trophy may stay truncated. This term
is the read-off. It is not the existence.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`
  Read. `archive/dev/LJ-dispatch-index.md:1`
  quotes: # THE `LJ` DISPATCH INDEX, archived 2026-08-18
  Declined: archived dispatch rows. This task's live producer is
  `dev/pod/queue.toml`. The term does not consult a retired row.
- `archive/dev/JOURNAL-archived.md`
  Used. `archive/dev/JOURNAL-archived.md:1732`
  quotes: "plan rather than the target. The untruncated equivalence remains unavailable (T31's wall) and the"
  A GO on `_↪_` as data does not move that wall. The door is an
  injection. It is not an equivalence.
- `archive/dev/JOURNAL.md`
  Read. `archive/dev/JOURNAL.md:1`
  quotes: # ARCHIVED 2026-08-20
  Declined: retired per-episode journal. The record of this task is
  this directory.
- `dev/ARCHIVE.md`
  Read. `dev/ARCHIVE.md:1`
  quotes: # ARCHIVE.md: the archive registry
  Declined: not used. No module was retired. W4 does not apply.
- `archive/dev/PLAN-archived.md`
  Read. `archive/dev/PLAN-archived.md:1`
  quotes: # ARCHIVED 2026-08-20
  Declined: archived construction registry. The live screen is
  `dev/pod/screen.toml`.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`
  Used. `dev/literature/truncation-and-selection.md:146`
  quotes: "**The constraint the route carries: `P` must be `hProp`-valued.** So `leastOf`"
  and `dev/literature/truncation-and-selection.md:148`
  quotes: "index is a proposition. **A data payload does not come out.**"
  This is why the coded site works and the ambient site does not.
  `InjCode` is an hProp payload, so `leastOf` returns the code as data.
  A truncated existence of an injection is the classical conclusion
  (`dev/literature/truncation-and-selection.md:75`). This task's output
  is stronger than that conclusion: it is the injection as data, from a
  coded existence.
- `dev/literature/devlin-II5.md`
  Used. `dev/literature/devlin-II5.md:129`
  quotes: "ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))"
  That is the classical least-witness guard. `leastOf` is that guard
  (`src/L/WellOrder/Base.lagda.md:158-160`).
- `dev/literature/digest.md`
  Used. `dev/literature/digest.md:58`
  quotes: "- **Q4 (the canonical well-order).** Stage-first, then minimal producer"
  `orderAt` is the live stage-first order on members. It is not an
  order on ambient function types. That is D-26 at this site.
- `dev/literature/terms-2026-08.md`
  Read. `dev/literature/terms-2026-08.md:1`
  quotes: # The terminology dossier: fourteen renderings for the owner's ruling
  Declined: translation terms. This task writes no glossary entry.
- `dev/literature/geology.md`
  Read. `dev/literature/geology.md:1`
  quotes: # Geology dossier: set-theoretic geology sources and the five questions
  Declined: geology sources. This probe does not touch grounds or
  the mantle.
