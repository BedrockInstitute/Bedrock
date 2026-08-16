# LJ-1.373 report: can `BandChoice` be discharged, or must it be assumed?

tier: pi (pi-subagent-mode), model `glm-5.3`. Probe. It lands nothing.
Written incrementally (C-22). No commit, no push. I wrote no file outside
`agents/tasks/LJ-1-373/`. I ran Agda only under `GHCRTS="-A64m -I0 -M8g"`, one
process, and I counted the slots before every run.

## CORRECTION RECEIVED, AND WHAT HAD ALREADY RUN

**Mid-task correction from the orchestrator, quoting the owner: do not spend
time trying to prove things that may simply be unprovable; do the LITERATURE
SURVEY FIRST.** This report was restructured: the literature is the SPINE, and
the Agda half is its appendix. **No Agda attempt to inhabit `BandChoice` was
started before the correction arrived.** What had already run, both premise
checks from the brief's SCOPE (read) section:

- `agents/tasks/LJ-1-368/Floor368.agda`, re-run, exit 0, 0.66 s, slots 0.
- `agents/tasks/LJ-1-368/Probe368.agda`, re-run, exit 0, 14.26 s, slots 0.

## VERDICT

**BLOCKED-OTHERWISE.**

The obstruction that decides the question is NOT the canonicalizer's
complement. It is the SHAPE. `BandChoice` is a selection from a truncated
family, and THIS TREE ALREADY HOLDS THAT SHAPE AS A PRICED INTERFACE,
`SetChoice`, stated levelwise in `src/Base/Choice.lagda.md` and never assumed
and never proved anywhere. My Agda measures that `BandChoice` is an INSTANCE of
`SetChoice (ℓ-suc ℓ)`, exactly and with no residue (section AGDA). The
literature measures that no condition makes this instance provable (section
LITERATURE). The tree's own boundary prose records that excluded middle does
not prove choice (section LEM).

The canonicalizer's complement is a real SECOND obstruction, and it is the one
the brief expected: it explains why the only SUFFICIENT condition the
literature names, the weakly constant endomap, has no supplier on this band.
The one canonicalizer in the tree is refuted on the band by the band's own
definition, MEASURED by `[LJ-1.333]`.

So the brief's framing "one obstruction explains everything" is REFUTED in its
strong form. Two obstructions stack, and the first one is new information for
the chain: the whole band problem bottoms out at the same interface the tree
prices for the V-to-ZFC upgrade.

## LITERATURE, THE SPINE

`dev/literature/truncation-and-selection.md` was read whole, 363 lines. The
three questions, in the correction's order.

### 1. Is a selection of this shape provable in general, or is it an axiom?

**IT IS AN AXIOM.** The digest's standing verdict, `:219-221`: a principle of
this shape "is therefore not refuted by the standard taboo, and it is also not
proved. **It must be ruled on.**" The universal form is refuted (HoTT Book
Theorem 3.2.2 and Corollary 3.2.7, digest `:224-228`), but the refutation runs
on univalence's autoequivalences and "do not reach a family indexed by a set"
(`:217-218`). A set-indexed instance is neither proved nor refuted by the
literature. It must be ruled on per instance, and the ruling here is the
owner's: `[LJ-1.369]`, do not assume it.

**THE TREE ITSELF SAYS THE SAME, MORE SHARPLY.** `src/Base/Choice.lagda.md`
states the shape as the classical boundary's second interface:

```agda
SetChoice : ∀ ℓ → Type (ℓ-suc ℓ)
SetChoice ℓ = (X : Type ℓ) → isSet X → (B : X → Type ℓ)
            → ((x : X) → ∥ B x ∥₁) → ∥ ((x : X) → B x) ∥₁
```

`src/Base/Choice.lagda.md`, the module's `The principle` section. The chapter
proves `choice→lem` from it by Diaconescu's construction, and its own prose
closes the door the other way: "The excluded middle does not return the
favour, so the two interfaces remain distinct." So in this tree the shape is
not an open question of mathematics. It is a PRICED INPUT, and the price list
is public: `V⊨ZFC` spends exactly `SetChoice (ℓ-suc ℓ)`,
`src/Landmarks.lagda.md:54`.

### 2. What condition would make it provable?

The digest names FIVE. Each is quoted, and each is checked against this band.

**A. THE FIBERS ARE PROPOSITIONS: unique choice.** Digest `:95`: "**This is the
only free case.** Everything below is about paying for the rest." The fiber
here is `sq δ`, a function plus an injectivity proof,
`src/L/Ordinal/SquareLaw.lagda.md:685-687`. The function is data. NOT MET,
MEASURED by the definition.

**B. THE FAMILY IS DECIDABLE OVER `ℕ`.** HoTT Book Exercise 3.19, quoted at
digest `:112`: "Suppose P : ℕ → Type is a decidable family of mere
propositions. Prove that ∥ Σ(n:ℕ) P(n) ∥ → Σ(n:ℕ) P(n)." The band's index is
the telescope of non-initial limits with structure, a proper class at
`Type (ℓ-suc ℓ)`, not `ℕ`, and the fibers are data, not propositions. NOT MET,
MEASURED by the telescope's shape (`Probe368.agda:193-196`).

**C. A WELL-ORDER PLUS A UNIVERSAL GUARD: the least witness.** Digest `:68`:
"**The selection device is a definable well-order plus a universal guard.**"
And HoTT Book Theorem 10.4.3's route, digest `:119-120`: "least elements are
unique when they exist, **so merely having one is as good as having one.**"
The tree's own `leastOf`, `src/L/WellOrder/Base.lagda.md:158-160`, is this
device in Agda. Its constraint, digest `:148`: "**A data payload does not come
out.**" The payload here IS the data: an injection, a function. NOT MET, and
the deeper reason is the digest's own section 5.2, `:335`: "A canonical
injection needs a well-order on the INJECTIONS", which an ambient function
type does not have. `[LJ-1.329]` MEASURED 35 `SWO` instances in `src/` with no
function carrier. NOT MET, MEASURED at the carrier and INFERRED at the
generality.

**D. A WEAKLY CONSTANT ENDOMAP: Kraus et al., Theorem 16.** Digest `:158-159`:
"**Theorem 16: 'A type X has a constant endomap if and only if it has split
support in the sense that ∥X∥ → X.'**" Necessary and sufficient, per fiber.
`[LJ-1.368]` already measured the uniform form of this condition as the exact
price of the untruncation: `band-from-endomap`, `Probe368.agda:205-210`, exit
0. The tree's ONLY canonicalizer, `via-col-square`
(`src/L/Ordinal/SquareLaw.lagda.md:960`), is refuted on the band by the band's
definition, MEASURED by `[LJ-1.333]`: the band negates `Init`'s fourth row and
the canonicalizer consumes it. CONDITION IDENTIFIED, SUPPLIER REFUTED ON THE
BAND. Whether a second canonicalizer exists is NOT REFUTED (C-36), and
`[LJ-1.319]`'s ruling records that no in-theory term can ever refute the door.

**E. THE INDEX IS A SET.** HoTT Book Lemma 3.8.5, digest `:234`: "the index
must be a SET". This is the ONE condition the band MEETS. It is the condition
my Agda was permitted to check, and it measures the instance claim of section
AGDA.

**NO OTHER CONDITION EXISTS IN THE DIGEST.** Its checklist, `:295-310`, is the
five above plus its own step 6 (the symmetry a canonical reader must break,
added by `[LJ-1.334]`), which is C's obstruction restated. So the literature's
answer to the owner's question is complete: the shape is an axiom, every
escape condition fails this band except the index's set-hood, and set-hood
alone does not select.

### 3. So what is the answer?

**A literature NO-GO on "provable outright", with one sharpening the
literature could not give and the tree did: the instance is not merely
AN axiom-shaped statement, it is an instance of the tree's OWN priced
interface.** That closes the question the correction asked first, and it
saves the project the attempt.

## AGDA, THE HALF THE LITERATURE PERMITTED

The literature names one condition this band can meet: the index must be a
set. Checking it is one derivation, `agents/tasks/LJ-1-373/Probe373.agda`:

- `BandIndex`, `:78-82`, the band's whole domain telescope as one Σ.
- `band-index-set`, `:87-95`: `isSet BandIndex`, from `isSetS`, the
  propositions' own `isProp` proofs, and `sq`'s set-hood (`[LJ-1.319]`, via
  `sq-set`, `Probe368.agda:199-204`).
- `bandchoice-from-setchoice`, `:136-138`, GREEN, exit 0, 2.46 s, slots 0:

```agda
bandchoice-from-setchoice : SetChoice (ℓ-suc ℓ) → BandChoice
bandchoice-from-setchoice sc t =
  PT.map band-sel (sc BandIndex band-index-set BandFiber (band-inh t))
```

**WHAT THE GREEN MEASURES.** `BandChoice` is an instance of `SetChoice
(ℓ-suc ℓ)`, and the whole distance between the band and the tree's own
interface is ONE `isSet` proof plus two lifts. No other mathematical content
separates them. The spelling is pinned twice: `band-inh` (`:114-117`) must
match `LimitBandT` and `band-sel` (`:120-123`) must match `LimitBand`, so a
wrong telescope refuses to check.

**WHAT IT DOES NOT MEASURE (C-36).** An instance can be weaker than the
interface. Nothing here proves `BandChoice` is AS STRONG as `SetChoice
(ℓ-suc ℓ)`. What is measured is sufficiency in one direction, and, with the
literature, that no weaker provable route is named.

## LEM ALONE: NO

Three independent witnesses, each marked.

1. **MEASURED, at this derivation:** `MustFail373A.agda:80-82` feeds the SAME
   body `LEM (ℓ-suc ℓ)` where `SetChoice (ℓ-suc ℓ)` stands. Exit 42:

   ```
   error: [UnequalTerms]
   (Type (ℓ-suc ℓ)) !=<
   (Σ (Type (ℓ-suc ℓ)) (Cubical.Foundations.HLevels.isOfHLevel 1))
   when checking that the expression BandIndex has type
   hProp (ℓ-suc ℓ)
   ```

   The classical principle cannot even ACCEPT the index. This measures my
   derivation and no other (C-36).

2. **THE TREE'S OWN BOUNDARY PROSE, a recorded position, not a proof:**
   `src/V/Model.lagda.md:426-427`: "The excluded middle does not prove choice,
   so upgrading to ZFC costs a genuinely new assumption". And `choice→lem` in
   `src/Base/Choice.lagda.md` proves the reach runs one way only.

3. **INFERRED, from the literature:** HoTT Book Definition 3.8.1 is an axiom,
   not a theorem (digest `:225-229`), and classical ZF models where choice
   fails satisfy excluded middle. The digest records the axiom-hood; the model
   argument is standard and outside the digest, so the general claim stays
   INFERRED.

## THE HONEST RESIDUE

The chain of "provable from X, and X is provable from Y", followed to its
ends, has exactly two ends, and both are CLOSED:

**END ONE, THE INTERFACE.** `SetChoice (ℓ-suc ℓ)` gives `BandChoice`, MEASURED
green above. Is `SetChoice (ℓ-suc ℓ)` provable? NO: it is the tree's priced
boundary, never proved, strictly stronger than LEM in reach (`choice→lem` is
proved; the converse is the tree's own "does not return the favour"), and
already spent by the tree at exactly this level for `V⊨ZFC`
(`src/Landmarks.lagda.md:54`). Assuming it is the cost class the retired route
refused (ARCHIVE USED, below) and the owner refused again on `[LJ-1.369]`.
Note what `[LJ-1.369]` refused: assuming `BandChoice`. Assuming the interface
that implies it is the same cost under a wider name, and this report does not
recommend it. It records that the door exists, is already built in the tree,
and is priced.

**END TWO, THE UNTRUNCATION.** `(LimitBandT → LimitBand)` gives `BandChoice`
in one line, `Probe368.agda:241-242`, MEASURED. Its own residue is the
canonicalizer family, and the complement refutes the tree's only canonicalizer
exactly on the band, MEASURED by `[LJ-1.333]`. Whether another canonicalizer
exists is open and unrefutable from inside (C-36, `[LJ-1.319]`'s ruling).

**SO THE OWNER'S QUESTION HAS A CLEAN ANSWER: `BandChoice` must be assumed,
unless one of the two closed ends is re-opened by ruling.** The cheap door the
brief hoped for does not exist as a proof. It exists only as a priced
assumption, and the price tag is already printed in the tree.

## NEGATIVE CONTROL, AND WHY IT IS NOT A TAUTOLOGY

The control is `MustFail373A.agda`, described above, exit 42. It is not the
`[LJ-1.368]` tautology for three reasons:

1. My green is not `PT.rec squash₁` at a motive that might unfold to a
   truncation. It is a function between two FIXED types, `SetChoice (ℓ-suc ℓ)`
   and `BandChoice`, and its only eliminator use is `PT.map`, whose type is
   fixed.
2. The green's content is pinned by two terms that must match the delivered
   telescope (`band-inh` against `LimitBandT`, `band-sel` against
   `LimitBand`), in the style of `MustFail368C`. A misspelled index refuses.
3. The control deletes exactly one thing, the selection principle, and Agda's
   refusal names the first argument. The delta between exit 0 and exit 42 is
   the selection structure, nothing else in the body differs.

## PREMISE CHECK

1. **"`BandChoice` closes the trophy's conclusion with no untruncation"**.
   VERIFIED by re-run: `Probe368.agda`, exit 0, 14.26 s. `closes-from-choice`
   at `:229-236`, `BandChoice` at `:226-227`.
2. **"The untruncation implies `BandChoice` in one line"**. VERIFIED by the
   same run: `choice-from-untruncation`, `:241-242`.
3. **"The band is the exact complement of the only canonicalizer"**. VERIFIED
   as `[LJ-1.333]`'s measurement (`agents/tasks/LJ-1-333/lj-1.333-report.md`,
   section 3.2: the band negates `Init`'s fourth row at
   `src/L/Ordinal/SquareLaw.lagda.md:697-699`; the canonicalizer consumes it
   through `InitialCore`'s `noinj²`). I read it and did not re-derive it. The
   word "only" carries `[LJ-1.333]`'s own C-36 mark: no in-theory term can
   refute a second canonicalizer.
4. **"The tree holds `LEM` at every L chapter as a module parameter"**.
   VERIFIED by inspection at this task's own imports: `Probe368.agda`,
   `ProbeLJ1337A.agda`, and the archived `L.Choice.Order` and
   `L.Choice.Transversal` are all `module ... (lem : LEM (ℓ-suc ℓ)) where`.
   The premise holds for the archived route too, which matters to ARCHIVE
   USED.

**THE BRIEF'S AT-RISK PREMISE, ANSWERED.** "The canonicalizer's complement is
what will block this too" was the framing at risk. It is HALF right. The
complement blocks the only SUPPLIER of the literature's necessary-and-
sufficient condition. It does not block the SHAPE, and the shape is what
actually refuses: the band asks for a selection, the tree prices selections at
`SetChoice`, and no condition bridges the two here. The route-level finding
the brief wanted either way: the untruncation remains the only door, AND it
now has a name for its price, which is the same interface the ZFC upgrade
spends.

## DD4

The axis, fixed at `scripts/measure/ledger.py:50`: what the AC and GCH
closures SHARE, in masters and lines. `[LJ-1.368]` measured the stake: the
wrap route edits no consumer, while the supplier-change cure touches
`L.Ordinal.SquareLaw`, which both closures share.

My term is a pure WRAP at the band site. It edits no consumer and touches no
chapter, shared or otherwise. **If the owner ever re-ruled to spend
`SetChoice (ℓ-suc ℓ)`, the DD4-cheapest property measured by `[LJ-1.368]` is
KEPT, at the cost of one new parameter.** The untruncation route is the one
that gives the property up. The DD4-cheapest PROOF does not exist; the
DD4-cheapest ASSUMPTION does, and this report does not choose between them:
that is the owner's, and the two prices are now both printed.

## ARCHIVE USED

- **`archive/src/2026-08-09-rud-route/`** CITED. Answer to the brief's
  question: the retired route never PROVED a selection from a truncated
  family. It built the interface and priced it.
  `archive/src/2026-08-09-rud-route/Everything.lagda.md:67`: "`Base.Choice`{.Agda}:
  the boundary's second interface: set-level choice".
  **QUOTE CORRECTED IN PLACE 2026-08-16 BY THE ORCHESTRATOR, and only the
  quote.** As returned it dropped the `{.Agda}` annotation, so the substring
  did not occur at the cited line and `scripts/gate/check-dd18-survey.py`
  refused this return, correctly: its B2 rule requires the quote to occur AT
  the cited line in the cited file, and a quote that does not is a mis-cited
  line. `[LJ-1.375]` found it. **The line number and the reading are
  unchanged; only the transcription was wrong.** The archived
  `L.Choice.Order` and `L.Choice.Transversal` take only `LEM (ℓ-suc ℓ)` as
  their module parameter (their `module` lines, `:42` and `:50`), so the
  retired L-side choice chapters consumed the well-order device, not a choice
  assumption. `grep` for `SetChoice` across the archived route returns hits
  only in `Everything.lagda.md` and the patch, never in an `L/Choice/`
  chapter.
- **`archive/dev/JOURNAL-archived.md:1630`** CITED, and it bears on ASSUMING,
  not on PROVING: "a choice principle implies excluded middle and would cost
  the tree's postulate-free claim". `[LJ-1.368]`'s reading is confirmed here:
  the sentence is a cost argument against ADDING a choice parameter, and it
  does not claim choice is unprovable. In THIS tree the same cost argument
  has already been paid its honest form: D2 keeps the tree postulate-free
  with LEM and choice as explicit parameters, and the owner's `[LJ-1.369]`
  refusal is the modern descendant of that sentence.
- **`archive/dev/DECISIONS-archived.md`** CITED, one row bears:
  `archive/dev/DECISIONS-archived.md:30`, D2: "LEM (and any classical/choice
  principle) is an explicit parameter". This is the boundary rule any
  `SetChoice` spend must respect: a parameter, never a postulate. No ruling
  on truncation or on the band exists in the archive. WHY NOT the other rows:
  D18, D32, D33 and D38 rule the trophy configuration and the route, and none
  of them touches a selection principle.
- **`archive/dev/TASKS-archived.md`** CITED, shape only:
  `archive/dev/TASKS-archived.md:66`: "| L3.32-T31 | Square law, discharged |
  DELIVERED (transfer blocked) | `_build/l3.32-t31-report.md` |". The retired
  square-law dispatch delivered under a module hypothesis and recorded the
  transfer as blocked. That is the same shape this chain now carries to the
  owner: delivered under a parameter, with the last transfer named and priced.
  The reports themselves are under `_build/` and not in the corpora.

## LITERATURE USED

`dev/literature/truncation-and-selection.md`, read whole (363 lines). USED:
`:95` (unique choice the only free case), `:112` (Exercise 3.19, decidable
families over `ℕ`), `:119-120` (Theorem 10.4.3, least elements unique),
`:148` (`leastOf`'s data-payload limit), `:158-159` (Kraus et al. Theorem 16,
necessary and sufficient), `:164` (the criterion restated as the question),
`:217-221` (the universal taboo does not reach set-indexed families; "It must
be ruled on"), `:225-229` (AC's truncated conclusion; "AC delivers `∥ f ∥₁`
for a selection function `f`, never `f`"), `:234` (Lemma 3.8.5, the index
must be a set), `:295-310` (the checklist, steps 1 through 6), `:335` (a
well-order on the INJECTIONS).

WHY NOT the rest: section 1 (the set-theory side) supplies the least-witness
device, already covered under condition C. Section 3.1 (Paulson's classical
Isabelle/ZF) cannot state the question, as the digest itself records, so it is
not evidence in either direction. Section 3.2 (Matthews and Rathjen) is a
warning about constructive `L` under failing excluded middle, and this project
spends LEM, so its regime does not apply. Section 6 (sources and status)
guided which numbers I may cite by label.

## SLOTS, FLOOR, SECONDS

Floor measured fresh: `Floor368.agda`, exit 0, 0.66 s. Every figure below is
WARM: the whole interface chain under `src/` and the sibling probes were
already built. No cold cost is measured here (P-l).

Slots counted with the brief's exact command before EVERY invocation; the
count was 0 every time. One process per run. Cap never raised. No heap
exhaustion.

| run | file and outcome | exit | real s |
|---|---|---:|---:|
| 1 | `Floor368.agda`, floor, GREEN | 0 | 0.66 |
| 2 | `Probe368.agda`, premises re-run, GREEN | 0 | 14.26 |
| 3 | `Probe373.agda`, scope error, `isProp→isSet` not in cubical `HLevels` | 42 | 2.40 |
| 4 | `Probe373.agda`, same error, `isProp×` namesake | 42 | 2.40 |
| 5 | `Probe373.agda`, parse error in a `Σ` binder | 42 | 2.44 |
| 6 | `Probe373.agda`, **GREEN** | **0** | 2.46 |
| 7 | `MustFail373A.agda`, **REFUSED, the control** | **42** | 2.40 |

The 1-minute load at the last run was 4.65. The machine was not quiet. I
measure no check time as a price, so the load damages no figure here.

Lines, in `agents/tasks/LJ-1-373/`:

| file | total | non-blank |
|---|---:|---:|
| `Probe373.agda` | 157 | 139 |
| `MustFail373A.agda` | 82 | 69 |
| this report | as written | as written |

## WHAT I DID NOT DO

I did not attempt to inhabit `BandChoice` outright, by the correction. I did
not search for a new canonicalizer, by the same correction and by C-36. I did
not touch `src/`, any sibling task's files, `make check`, git history, or the
working tree outside this directory. I ran no `make` target. The two lint
gates the brief names pass on this report and the tree:
`scripts/gate/lint-prose.py --check` exit 0, `scripts/gate/lint-agda.py
--check` exit 0.
