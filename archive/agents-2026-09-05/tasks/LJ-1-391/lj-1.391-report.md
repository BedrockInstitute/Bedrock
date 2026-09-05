# [LJ-1.391] Can `sq` be TRUNCATED? The collection step, measured

[`Probe391.agda`](Probe391.agda), 230 lines, RED at exactly one hole, **1.70
wall seconds**, the median of three consecutive runs (1.68, 1.71, 1.70) at the
wide caliber `-A64m -I0 -M8g` with one Agda process. The empty-module floor on
the same machine on the same day is **1.54 s** (1.61, 1.54, 1.51). Every run
below had the dependencies warm.

This is attempt 2. Attempt 1 (glm-5.3, 2026-08-19) returned NO-GO with a hole
at `PointwiseUntrunc`, then PARKED (`dev/pod/transitions/2026-08.jsonl` seq
116). Its adversarial review (`review-of-LJ-1-391-1.md`) confirmed the verdict
and named four gaps. The owner-authorized audit recorded that none of those
findings were applied (`dev/pod/audit-2026-08-20.md` F8). This return applies
them at the original two obligations. The attempt-1 text of this file is
replaced. The review file is left untouched as the record of that attack.

## VERDICT

**NO-GO on `sq-collect`. The door is load-bearing.** The collection is the
HoTT Book's axiom of choice 3.8.1,
`(∏x ∥Y x∥) → ∥∏x Y x∥`
(`dev/literature/truncation-and-selection.md:223-227`), at the index type of
the band ordinals. It is not a new statement. Equivalently, by C-54 and by
Kraus et al. Theorem 16, it is a `2-Constant` endomap of `sq δ` at each band
member (`EndomapAt`, `Probe391.agda:153-156`). This tree carries no device
that pays either form at the generic parameter `α₀`. **`sq-collect-suffices`
is GREEN** (`Probe391.agda:75-85`). **The digest 2.7 check is GREEN**: if the
collection were paid, the truncated consumer would be served, because
`sq-collect-suffices` concludes in `∥_∥₁` (`ac-composes`,
`Probe391.agda:93-100`; `dev/literature/truncation-and-selection.md:229-232`).

**WHAT `sq-collect` NEEDS, IN ONE LINE.** A `2-Constant` endomap of `sq δ`
over the band (`EndomapAt`, `Probe391.agda:153-156`):

```agda
EndomapAt =
  (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
  → Σ[ k ∈ (sq δ → sq δ) ] 2-Constant k
```

The green terms `const-gives-pointwise` (`Probe391.agda:158-160`) and
`pointwise-gives-const` (`Probe391.agda:162-165`) prove this residue is
EQUIVALENT to `PointwiseUntrunc` (`Probe391.agda:117-119`). The green term
`pointwise-collects` (`Probe391.agda:123-128`) proves that residue SUFFICES
for the collection. The obligation itself is that reduction with the endomap
as the hole (`Probe391.agda:230`). **The run's only error is that hole**:
exit 42, `[UnsolvedInteractionMetas]` at `Probe391.agda:230.58-73`, nothing
else.

**WHY THE RESIDUE IS NOT PAYABLE TODAY, BY THE DIGEST CHECKLIST.**

| Digest step | What it asks | Where the tree falls short |
|---|---|---|
| 1. goal a proposition | `sq-collect`'s conclusion is `∥_∥₁` | Free on the outside. The stall is inside, at each `sq δ`. |
| 2. `A` a proposition | `isProp (sq δ)` | Route A, complete as `prop-gives-pointwise` (`Probe391.agda:172-174`) except for that motive. The motive is false at every banded ordinal that has a pairing: the flipped pairing is a second, and the flip uses no excluded middle (`dev/literature/truncation-and-selection.md:307-310`). The chapter's own `extract` carries the same demand (`src/L/StageCardinal.lagda.md:419-420`). |
| 3. goal a SET plus a `2-Constant` map | `sq δ` is a set | `sq-set` is green at `agents/tasks/LJ-1-319/SqIsSet.agda:37-41`, imported not copied. `rec→Set` applies iff `EndomapAt` is paid (`const-gives-pointwise`). **This is the hole.** Law C-54 (`dev/LESSONS.md:4448-4456`) orders this before a new principle. Paying the endomap IS paying the residue; it is not a cheaper target. |
| 4. well-order plus a propositional payload | `leastOf` over an SWO | `leastOf` needs an `SWO` (`src/L/WellOrder/Base.lagda.md:158-160`), spent as `untruncAt` (`agents/tasks/LJ-1-314/CodeUntrunc.agda:57-66`). No delivered SWO in `src/` has an ambient function type as carrier. The transfer device `pullOrder` (`src/L/Choice/Step.lagda.md:226-242`) does not rescue this: the injection of that function type into a coded carrier IS the door `[LJ-1.386]` measured. Sweep in section 2. |
| 5. weakly constant endomap by any other route | Kraus Theorem 16 | The same obligation as step 3. A *merely* existing endomap is free (`agents/tasks/LJ-1-384/Probe384.agda:65-67`) and does not suffice: if it did, every type would have split support (`Probe384.agda:69-73`), which the digest's section 2.6 records as refuted. |
| 6. a new principle | HoTT Book 3.8.1 | Only now. Stated as a type, never postulated (DD9). |

**THE DIGEST PREDICTED THIS, AND THE MEASUREMENT AGREES WITH IT.**
`dev/literature/truncation-and-selection.md:335-337`: a canonical injection
needs a well-order on the INJECTIONS, which is what `<_L` supplies classically
and an ambient function type does not have. This task did not take the
prediction as an answer. It is now a measurement at this tree's own site, at
the generic parameter `α₀`.

## 1. What was built

| Term | At | Code lines | What it is |
|---|---|---|---|
| `sq-collect-suffices` | `Probe391.agda:75-85` | 10 | **OBLIGATION, GREEN.** `L.StageCardinal` instantiated at the family, `Upper.stage-card-upper` read under one `∣_∣₁` |
| `ac-composes` | `Probe391.agda:93-100` | 8 | GREEN. Digest 2.7: AC's truncated conclusion serves this consumer |
| `PointwiseUntrunc` | `Probe391.agda:117-119` | 3 | split support of `sq` over the band |
| `pointwise-collects` | `Probe391.agda:123-128` | 6 | GREEN. The residue SUFFICES; the rest is bookkeeping |
| `EndomapAt` | `Probe391.agda:153-156` | 4 | the C-54 residue: a `2-Constant` endomap of `sq δ` |
| `const-gives-pointwise` | `Probe391.agda:158-160` | 3 | GREEN. `rec→Set` |
| `pointwise-gives-const` | `Probe391.agda:162-165` | 4 | GREEN. the converse, by `squash₁` |
| `prop-gives-pointwise` | `Probe391.agda:172-174` | 3 | GREEN. Route A complete except for `isProp (sq δ)`, which is false |
| `sq-collect` | `Probe391.agda:226-230` | 5 | **OBLIGATION, RED at the hole.** The reduction with `EndomapAt` unpaid |

**TOTAL: 15 code lines for the two obligations** (10 green, 5 attacked).
The C-54 measurement and the 2.7 check add 31 more. **The file is 230 lines
and 71 code lines**; a code line is a line that is not blank and is not a
comment. The difference is the module header, the imports and the route
records in comments.

**NOTHING WAS RE-PROVED.** `sq-collect-suffices` supplies the module parameter
and reads the delivered conclusion. `LimitStep` was not rebuilt; if it had
needed rebuilding, that would have been a different task and I would have
stopped.

## 2. What the NO-GO proves, and what it does not

**THE TWO EXPENSIVE ROUTES KEEP THEIR PRICE, AT GENERIC `α₀`.** The product
route owes a coded injection out of an internal square at every band ordinal
(`agents/tasks/LJ-1-388/lj-1.388-report.md:236-248`). The descent route owes
`Init` at every internal cardinal, and `Init` has no producer
(`agents/tasks/LJ-1-390/lj-1.390-report.md:20-27`). Both prices buy an
UNTRUNCATED pairing family, and a GO here would have retired both: `∥ sq δ ∥₁`
pointwise is already supplied under `Init` by `via-col-truncated`
(`src/L/Ordinal/SquareLaw.lagda.md:963-964`), and a truncated recursion would
have carried it. **The NO-GO says that saving is not available at this
consumer's module boundary.** The collection cannot turn the truncated supply
into the family the consumer takes as its module parameter
(`src/L/StageCardinal.lagda.md:15-20`), so the family must arrive as data, and
`[LJ-1.386]`'s door, which produces ambient function data from truncated coded
existence, is on the critical path of this consumer and not beside it.

**THE MISSING PRINCIPLE IS THE HoTT BOOK'S 3.8.1, EQUIVALENTLY A `2-Constant`
ENDOMAP OF `sq δ`.** Route B's carrier gap is closed classically by `<_L`,
the definable well-order of the constructible universe, which is the machinery
behind `L ⊨ AC`, the campaign's own first trophy. So the honest reading of the
NO-GO is not "the collection is false" but "paying it costs building the
global well-order at the pairings, which is the whole AC tower, and that is
more than either route's residue".

**THE NO-GO IS OF THIS TREE'S DEVICES, AT GENERIC `α₀`.** Law C-42: a
refutation measures the site it names. One site was measured, the generic
parameter. It is not a claim that `sq-collect` is refuted: under a global
well-order the statement is classically true. It is a measurement that no
device in the tree today selects an ambient pairing at that parameter. One
caliber was run.

**THE [T46] CHECK, ORDERED BY THE BRIEF AND DROPPED BY ATTEMPT 1.**
`L.StageCardinal`'s recursion eliminates its own hypothesis in `branch`
(`src/L/StageCardinal.lagda.md:534-560`). The hypothesis is consumed at
`:550-551`, `comp-inj (IH ω ...)` and at `:556`, `comp-inj (IH δ δ∈α oδ δ∈suc
infδ) (Emb.emb α oα δ δ∈α)`. Both land in the injection type
`⟪ Lset δ ⟫ ↪ ⟪ α ⟫`. The only `Empty.rec` in sight, at `:528`, eliminates
the false membership case, not the hypothesis. **The brief's reading is
right: this chapter is a [T46] site.** The truncated grade fails inside the
chapter as well, so `sq-collect` is not the only thing that fails, and the
T47 dodge of restating the parameter as truncated is not free here. This
strengthens the verdict.

**ADMISSIBILITY, ORDERED BY THE BRIEF, AND NOT DECIDED.** The archived
objection was that a choice principle implies excluded middle and would cost
the tree's postulate-free claim (`archive/dev/JOURNAL-archived.md:1630`). This
tree now carries `lem` as a module parameter (`src/L/StageCardinal.lagda.md:15`).
The standing ruling is D2 (`archive/dev/DECISIONS-archived.md:30`): "LEM (and
any classical/choice principle) is an explicit parameter; the whole tree is
`--safe`." A choice principle packaged the same way as `lem` would be
admissible under that ruling as a packaging. Whether to add one is the
owner's call. This task does not make it.

**THE SWO SWEEP, BECAUSE ATTEMPT 1 CLOSED IT WITH A FALSE GREP.** Attempt 1
wrote that `grep -rn ": SWO\|SWO (" src/` returns no other shape than
`ordSWO`, `orderAt` and `prodSWO`. That sentence is false. The delivered SWOs
in `src/` and their carriers, as of this run:

- `ordSWO : SWO ⟪ α ⟫` (`src/L/Ordinal/SquareLaw.lagda.md:176`; also
  `src/L/StageCardinal.lagda.md:258`)
- `prodSWO : SWO (X × Y)` (`src/L/Ordinal/SquareLaw.lagda.md:127`)
- `lex2 : SWO (⟪ α ⟫ × ⟪ α ⟫)` (`:282`), `lex3` (`:285`)
- `godSWO : SWO Pair` (`:308`), `god : SWO PairA` (`:755`)
- `orderAt : SWO (Mem (Lset γ))` (`src/L/Choice/Step.lagda.md:730`)
- `pullOrder : SWO B` from an injection into a well-ordered `C`
  (`src/L/Choice/Step.lagda.md:226-242`)
- `byName`, `stepAt`, `famOrder` on `New` and `Mem` (`src/L/Choice/Step.lagda.md:373,429,703`)
- `natOrder : SWO ℕ` (`src/L/Choice/Finite.lagda.md:596`)
- `order : SWO (Point n)` (`:884`), `limitOrder : SWO Limit` (`:1114`)
- `nameOrder : SWO (Name)` (`src/L/Choice/Name.lagda.md:804`)
- `stepOrder : SWO (New δ)` (`src/L/Choice/Faithful.lagda.md:400`)
- `ordW : SWO ⟪ Lset δ ⟫` (`src/L/Choice/Order.lagda.md:222`)
- `boundOrder : SWO (Mem (Lset boundOrd))` (`:690`)
- `wL : SWO SL` (`src/L/Hull.lagda.md:158`)
- `W : SWO (Mem (Lset β))` (`src/L/Choice/Transversal.lagda.md:191`)

**None of these has an ambient function type as carrier.** That is the
surviving conclusion of route B. `pullOrder` transfers a well-order along an
injection; with B the pairing type, that injection is the coded door, not a
way around it.

## 3. W2 (DD4), answered

Both obligations are generic: `α₀` and `oα₀` are parameters of the probe
module, `δ` is bound in every statement, and nothing names `ω · 2`, `+ω` or any
other site. The mathematics the payoff uses is written once in the shared
chapter `L.StageCardinal` and reached by instantiation
(`Probe391.agda:81-85`), which is W2's write-once discipline; the J tower can
instantiate the same chapter unchanged. No deadline pressed a fixed form, so no
conflict arose.

## 4. W3: the estimate and what was measured

The widest unmeasured term was `sq-collect` itself, and this task is its probe.
The brief estimated about 35 code lines for the two obligations together, on a
comparable of shape and not of size, and ordered that nothing be funded against
it. **Measured: 15 code lines for the two obligations** (10 green, 5 attacked).
The C-54 endomap and the 2.7 check are the review's named measurement, not a
price against 35. The half that fails costs zero inhabited lines and returns
the whole value of this task, exactly as the brief predicted.

Attempt 1 skipped digest steps 3 and 5. This attempt states them as green
equivalences and leaves the same unpaid residue. The NO-GO does not fall by
the upgrade: paying `EndomapAt` is paying `PointwiseUntrunc`. The upgrade is
that the missing principle now has the library's own name (`2-Constant` /
`rec→Set`) as well as the digest's name (HoTT Book 3.8.1).

## 5. The measurement

Every run is `agda --safe agents/tasks/LJ-1-391/Probe391.agda` from the
repository root, under the caliber the program set on my pane
(`GHCRTS=-A64m -I0 -M8g`), one Agda process at a time, dependencies warm. I
did not set `GHCRTS`.

| Run | Seconds | Exit |
|---|---|---|
| full file, run 1 | 1.68 | 42, `[UnsolvedInteractionMetas]` at `:230.58-73` only |
| full file, run 2 | 1.71 | 42, same |
| full file, run 3 | 1.70 | 42, same |
| floor: the file truncated to its 59 header and import lines | 1.61, 1.54, 1.51; median 1.54 | 0 |

**THE WHOLE MEASUREMENT COSTS 0.16 s OVER ITS FLOOR.** Instantiating the
entire chapter `L.StageCardinal` at a PARAMETER `α₀`, and elaborating
`Upper.stage-card-upper`, is free at this site: `α₀` is an atom to the
elaborator, which is law P-l's moral, and no membership witness at a deep chain
is ever normalized. No conversion explosion appeared, no heap event appeared.
The full-file run reports the one meta at `:230` and nothing else, so Parts 1
to 3 are green inside the surviving file.

The floor replaced the probe in place by its first 59 lines for three runs
and then restored it: `cmp` silent, sha256
`732c148517adfa3fcffe89f846bbe76564f65da935da73c94e5ab4cce7542785` before and
after. A copy sat in `/tmp` during those runs. `/tmp` is outside the tree.

## 6. What this report does NOT claim

- **It does not claim `sq-collect` is false.** Classically, under a global
  well-order, it is true. The NO-GO is that no device in this tree selects an
  ambient pairing today, at the generic parameter `α₀`, and that paying it is
  building `<_L`.
- **It does not refute `EndomapAt`.** A refutation would be an unprovability
  theorem and would upgrade this NO-GO. The endomap is classically true when
  `sq δ` is inhabited. The digest itself leaves that per-site question open
  (`dev/literature/truncation-and-selection.md:330-331`). This task attempted
  the construction, did not find one, and did not find a refutation.
- **It does not formalize the flip argument.** That an inhabited `sq δ` has two
  elements (pairing and its flip) is stated in the probe's comment
  (`Probe391.agda:181-189`) and cited to the digest's own refutation at
  `:307-310`, not proved in Agda: it needs two distinct indices of an infinite
  ordinal, which is real work and not this task's obligation.
- **It does not re-price either route.** Both residues stand at their recorded
  prices; this task changes their STATUS at this consumer, not their cost.
- **It does not claim the truncated grade is useless.** `via-col-truncated`
  still supplies `∥ sq δ ∥₁` under `Init`
  (`src/L/Ordinal/SquareLaw.lagda.md:963-964`), and a future consumer whose
  conclusion is itself truncated may yet collect by other means. What is
  measured is THIS consumer's module boundary.
- **It does not measure a second site.** In particular it does not run `α₀ = ω`.
  The tree already holds `squareω : sq ω` as data (`src/L/InjChain.lagda.md:184-185`),
  so that one concrete band would not need selection. That is a reading of a
  delivered term, not a second run.
- **It does not write the owner's ruling** on whether a trophy statement must
  carry data rather than a truncation
  (`dev/literature/truncation-and-selection.md:338-340`).

## ARCHIVE USED

| Injected path | Read | What it gave |
|---|---|---|
| `archive/dev/JOURNAL-archived.md` | `:1626-1630`, `:1696-1698`, `:1707` | **[T43]** proposed the truncated restatement and priced the choice principle. **[T46]** named the propagation question this task measures. **[T47]** delivered the truncated law under `Init`. |
| `archive/dev/DECISIONS-archived.md` | `:30` | D2: a choice principle is an explicit parameter, never a postulate. The admissibility remark quotes this line. |
| `archive/dev/TASKS-archived.md` | `:82` | T47's row: the truncated square law, DELIVERED |
| `dev/ARCHIVE.md` | `:1` | DECLINED. See below. |
| `archive/src/2026-08-09-rud-route/Everything.lagda.md` | `:1` | DECLINED. See below. |

**`archive/dev/JOURNAL-archived.md:1626-1630`:**

> restate the counting's bounds in TRUNCATED form, since every consumer goal in
> the chain is a proposition and the truncation is therefore free on the
> consumer side
>
> a choice principle implies excluded middle and would cost the tree's
> postulate-free claim

**[T43] ALREADY KNEW THE HONEST EXTRACTION IS A CHOICE PRINCIPLE.** What it did
not have is the live consumer's shape: `L.StageCardinal` takes the family as a
MODULE PARAMETER, so "free on the consumer side" has to survive one more
boundary, and this task measured that it does not. The [T46] check in section 2
says the elimination inside the chapter is not free either.

**`archive/dev/JOURNAL-archived.md:1696-1698`:**

> That goal is NOT proposition-valued: its first component is a function, so a
> truncated equinumerosity cannot supply it as the goal currently stands.

**[T46]'S PROPAGATION QUESTION IS `sq-collect`.** This task answers it at the
live consumer: the propagation dies at the collection, and the principle it
needs is HoTT Book 3.8.1, equivalently `EndomapAt`. [T46]'s own obstruction,
"its first component is a function", is digest step 2's obstruction verbatim.

**`archive/dev/JOURNAL-archived.md:1707`** opens T47's return, the truncated
square law delivered under `Init`. T47 dissolved the collection inside the
chapter by strengthening `noinj²` so the square-law hypothesis vanished from
`InitialCore`'s telescope (`agents/tasks/archive/L3-32-T47/l3.32-t47-report.md:155-158`:
"The honest untruncated transfer stays blocked"). The live consumer still
takes the family as its parameter, so the collection returns there.

**DECLINED, WITH THE REASON.** `dev/ARCHIVE.md:1` is "# ARCHIVE.md: the archive
registry". A registry index; its rows point at the files quoted above and add
nothing. `archive/src/2026-08-09-rud-route/Everything.lagda.md:1` is
"# Bedrock", the archived route's site-reading front matter. Nothing in it
names a truncation.

## LITERATURE USED

| Injected path | Read | What it gave |
|---|---|---|
| `dev/literature/truncation-and-selection.md` | `:174-176`, `:186-190`, `:193-196`, `:223-232`, `:287-302`, `:307-310`, `:330-331`, `:335-340` | the checklist, AC 3.8.1, `rec→Set`, the flip, the open endomap question, the well-order prediction, the owner's ruling this task feeds |
| `dev/literature/devlin-II5.md` | `:1` | DECLINED. See below. |
| `dev/literature/digest.md` | `:1` | DECLINED. See below. |
| `dev/literature/terms-2026-08.md` | `:1` | DECLINED. See below. |
| `dev/literature/geology.md` | `:1` | DECLINED. See below. |

**`dev/literature/truncation-and-selection.md:223-227`:**

> HoTT Book (3.8.1) and Lemma 3.8.2 both have a TRUNCATED conclusion:
>
>     (∏x ∥Y x∥) → ∥∏x Y x∥

**THIS IS THE DIGEST'S NAME FOR `sq-collect`.** The brief ordered that the
principle be named this way and not presented as a new statement.

**`dev/literature/truncation-and-selection.md:229-232`:**

> So AC delivers `∥ f ∥₁` for a selection function `f`, never `f`. **If the goal
> that consumes `f` is not a proposition, AC does not help.**

**THIS IS WHY `ac-composes` WAS BUILT.** `sq-collect-suffices` concludes inside
`∥_∥₁`, which is a proposition, so the pair composes. Measured green at
`Probe391.agda:93-100`.

**`dev/literature/truncation-and-selection.md:307-310`:**

> It is then REFUTED because it is SYMMETRIC, so it is injective only if the
> carrier is a proposition. **The whole refutation is the flip of a pair and it
> uses no excluded middle.**

**THIS IS WHY ROUTE A / STEP 2 IS SHUT AND NOT MERELY UNFINISHED.** Corrected
span, from the review of attempt 1: the quote sits at `:307-310`, not
`:311-314`.

**`dev/literature/truncation-and-selection.md:335-337`:**

> **A canonical injection needs a well-order on the INJECTIONS, which is what
> `<_L` supplies classically and what an ambient function type does not
> have.**

**THE PREDICTION IS NOW A MEASUREMENT AT THIS SITE.** Corrected span, from the
review of attempt 1: `:335-337`, not `:334-336`.

**DECLINED, WITH THE REASON.** `dev/literature/devlin-II5.md:1` is "# Devlin
II.5: the Condensation Lemma and the GCH in L", the condensation spine, not
the collection step. `dev/literature/digest.md:1` is "# Digest: the orthodox
form of the rud route"; the live digest for this question is
`truncation-and-selection.md`. `dev/literature/terms-2026-08.md:1` is "# The
terminology dossier". `dev/literature/geology.md:1` is "# Geology dossier:
set-theoretic geology sources and the five questions". None of the four bears
on this task's step.

## THE TREE AS I LEAVE IT

**I changed three files and all three are mine:**
`agents/tasks/LJ-1-391/Probe391.agda`,
`agents/tasks/LJ-1-391/lj-1.391-report.md`, and
`agents/tasks/LJ-1-391/review-of-sq-collect.md`. The last file states the
NO-GO the brief's `no-go-stated` branch asks for. I did not edit
`LJ-1.391.md`, `review-LJ-1-391-1.md`, or `review-of-LJ-1-391-1.md`. I ran no
`git add`, no commit and no push. A copy of the probe sat in `/tmp` during
the floor run and the file was restored byte-identical, sha256
`732c148517adfa3fcffe89f846bbe76564f65da935da73c94e5ab4cce7542785`.

**THE GATES, run from the repository root with
`/Users/alsg/Agentic/Bedrock/.venv/bin/python` (this worktree has no local
`.venv`):** `lint-agda.py --check`, `check-glossary.py`,
`check-fences.py --check`, `check-probes.py --check`,
`scripts/site/weave-i18n.py --check`,
`scripts/pod/check-closure.py --check closure`,
`scripts/pod/check-spec-surface.py --check` and `lint-prose.py --check` are
all GREEN over the whole tree. `scripts/measure/check-unbound-hyp.py --check`
names five hypotheses, all of them in `src/`
(`src/L/Absorption.lagda.md:398,400`, `src/L/InjChain.lagda.md:471`,
`src/L/Reflect.lagda.md:365`, `src/L/StageCardinal.lagda.md:281`) and none in
this task's files; that gate reports, it does not fail a commit.

**THE PROBE'S OWN STATE, for whoever reads it next:** the file is RED by
design at `:230`, and it stays red. Nothing typechecks this file once this
task closes, so the run table above is the surviving evidence.
