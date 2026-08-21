# LJ-1.458 report: the formula this tree has already written, under another name

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-458/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-458/Probe458.agda`:

    LsetAt : ∀ {n} → Fin n → Fin n → Formula S n

together with

    lsetAt-out : ∀ {n} (x d : Fin n) (γ : S ^ n)
               → ⟨ γ ⊨ LsetAt x d ⟩
               → fst (lookup x γ) ≡ Lset (fst (lookup d γ))

Land nothing in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

READ BEFORE ANY AGDA, as the brief ordered.
`agents/tasks/LJ-1-451/lj-1.451-report.md:66` is the VERDICT heading.
The NO-GO sentence is at `:68`:

> **NO-GO at D-10 step 3.** The W3 type is well-formed and unbuilt

and at `:69-71`:

> `Code` has constructors `base` and `wit` only (`src/L/Hull.lagda.md:72-74`). There is no
> constructor that names `Lset`.

That NO-GO is the hull language. This task is `Formula S n`. The two
sites are not the same. C-42 forbids the transfer.

## D-10, BEFORE ANY AGDA

The four steps, as types. Written here before any term.

1. Grep the names the brief gave.

       grep -rn "LsetAt\|lsetFo\|levelAt\|isLevel" src

   Result: no matches. Also no matches for
   `LsetAt\|lsetFo\|LsetFo\|isLsetAt\|levelAt`.

2. Inventory every formula in `src/L/Coding/` and
   `src/L/Condensation.lagda.md` whose satisfaction mentions a STAGE.
   See `## INVENTORY` below. The inventory is not empty.

3. W3 type:

       stage-mentioning : Formula S 2

   Inhabit it from one delivered formula whose satisfaction speaks
   about `Lset` at a slot.

4. Obligation `LsetAt`, then `lsetAt-out` from delivered pieces.

The residue "NO FORMULA IN THIS TREE NAMES IT" (brief premise 6) is
FALSE at the class carrier. The grep missed `LsetGraphAt`. The
corrected target sits beside the original: inhabit `LsetAt` as
`LsetGraphAt`, and take adequacy from `Lset-only`.

Literature did not stop the task. Devlin II.5 records Φ as a theorem
of LST, not as an axiom this tree fails. See `## LITERATURE USED`.

## VERDICT

**GO.** The named obligation `LsetAt` typechecks. The witness meter
PASSes. W3 is inhabited.

- `LsetAt` is `LsetGraphAt` (`Probe458.agda:55-56`). Same type.
  Delivered at `src/L/Coding/Sequence.lagda.md:349`.
- W3 `stage-mentioning` is `LsetGraph` (`Probe458.agda:47-48`).
  Delivered at `src/L/Coding/Sequence.lagda.md:353-354`.
- Delivered adequacy is `Lset-only` at
  `src/L/Hierarchy.lagda.md:334-335`. Extra `IsOrd`. The probe
  inhabits that type as `lsetAt-out` (`Probe458.agda:62-66`).
- The brief's `lsetAt-out` omits `IsOrd`. That stronger type is
  `LsetAt-out-brief` (`Probe458.agda:69-73`). Stated. Unbuilt.
  I did not postulate. I did not write a well-founded recursion
  inside a formula.
- Witness: 0 UNRESOLVED of 1, 1.36 s, `probe_red=False`
  (`runs/witness.out:1-2`).

This is not `[LJ-1.454]`'s shape. That task found no formula.
This task found the formula under another name.

I did not write `review-of-LsetAt.md`. The verdict is GO. That
file is the critic's input on a NO-GO. It is not this return.

## INVENTORY

Formulas in `src/L/Coding/` and `src/L/Condensation.lagda.md`
whose satisfaction mentions a STAGE, not a pair, a tag or a code.

| name | file:line | what it describes |
|---|---|---|
| `StepAt` | `src/L/Coding/Sequence.lagda.md:119-120` | one step of the stage from an approximation |
| `ApproxAt` | `src/L/Coding/Sequence.lagda.md:286-289` | an approximation to the hierarchy on an argument |
| `GraphAt` | `src/L/Coding/Sequence.lagda.md:291-292` | the value is the stage at the argument |
| `LsetGraphAt` | `src/L/Coding/Sequence.lagda.md:349` | `GraphAt` renamed |
| `LsetGraph` | `src/L/Coding/Sequence.lagda.md:353-354` | `Formula S 2`, the two slots filled |
| `PairGraphAt` | `src/L/Coding/Sequence.lagda.md:328-329` | a pair whose second component satisfies the graph |
| `stepBndAt` | `src/L/Condensation.lagda.md:2417-2418` | bounded restatement of `StepAt` |
| `approxBndAt` | `src/L/Condensation.lagda.md:2471-2477` | bounded restatement of `ApproxAt` |
| `graphBndAt` | `src/L/Condensation.lagda.md:2492-2493` | bounded restatement of `LsetGraphAt` |

`src/L/Coding/Base.lagda.md:248-293` delivers `sglAt`, `pairAt`,
`prAt` and `tagAt`. Those describe a pair, a tag or a singleton.
They are not stages. The brief named them as the class. The stage
formula sits in `Sequence`, not in `Base`.

Adequacy that names `Lset` at a slot:

- `Lset-only` at `src/L/Hierarchy.lagda.md:334-335` (out, needs `IsOrd`).
- `Lset-defines` at `src/L/Hierarchy.lagda.md:646-648` (in, needs `IsOrd`).
- `ride-only` / `ride-defines` at `src/L/Condensation.lagda.md:422-431`
  ride those two theorems. They are not new formulas.

`src/L/Coding/Sequence.lagda.md:413`:

> `LsetGraph`{.Agda} is the object-language sentence "the value is the stage at

Count of formulas named `LsetAt`: **0**. Count of formulas of this
shape under the name `LsetGraphAt`: **1**, plus the closed alias
`LsetGraph`, plus the bounded restatement `graphBndAt`.

The inventory is not empty. That is the measurement this task
exists to make.

## 1. What was built

All in `agents/tasks/LJ-1-458/Probe458.agda`, module
`LJ-1-458.Probe458 {ℓ} (lem)`.

- W3 inhabited: `stage-mentioning = LsetGraph` (`:47-48`).
- Obligation inhabited: `LsetAt = LsetGraphAt` (`:55-56`).
- Delivered adequacy inhabited: `lsetAt-out = Lset-only` (`:62-66`),
  with `IsOrd`.
- Brief adequacy stated: `LsetAt-out-brief` (`:69-73`). Unbuilt.

Measured non-blank non-comment lines: 32. Total lines: 73. The brief
estimate was about 90 lines if the inventory was empty, about 300 if
the pieces exist and the adequacy runs. The pieces exist. The
adequacy is a one-line alias. Nothing is funded against the estimate.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `LsetAt` is generic in the arity `n`. No ordinal is
fixed. No second copy at a concrete stage. The conflict the clause
names (a deadline that forces a fixed form) did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## STEP ONE, W3

**The type is well-formed. The term is inhabited.**
`stage-mentioning` (`Probe458.agda:47-48`) is the brief's
`Formula S 2`. The inhabitant is `LsetGraph`.

W3 was typechecked alone, before the obligation was added. Three
forced rechecks, interface removed before each, dependencies warm,
caliber `-A64m -I0 -M8g`, one Agda process. Exit 0 every time.
Each printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.58 | 386105344 |
| `runs/w3-3.out` / `w3-3.time` | 1.58 | 386138112 |
| `runs/w3-4.out` / `w3-4.time` | 1.54 | 386154496 |

Median wall **1.58 s**. Peak RSS **386154496 bytes**. No heap
event. The first check `runs/w3-1.out` was 1.41 s and 386088960
bytes, also exit 0. It is not one of the three forced rechecks.

The brief estimate for W3 was about 10 lines and under 10 seconds,
or a grep and one sentence if the inventory is empty. The inventory
is not empty. The measured median is under 10 seconds.

## STEP TWO, THE OBLIGATION

Inhabited. `LsetAt = LsetGraphAt`. No new formula. No recursion
written by hand.

The delivered out-direction needs `IsOrd`. I inhabited that type.
I did not inhabit the brief's type without `IsOrd`. That type is
`LsetAt-out-brief`. A well-founded recursion inside a formula was
not required: the description is already the graph of an
approximation (`src/L/Coding/Sequence.lagda.md:291-292`).

The other adequacy direction is also delivered: `Lset-defines` at
`src/L/Hierarchy.lagda.md:646-648`. This task did not re-prove it.
It names it.

## WHAT BOTH FRONTS OWE

`levelIn` at `src/L/BoundedSubset.lagda.md:917`:

    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

This formula does not unblock it. `LsetAt` is `Formula S n`. The
hull's `wit` at `src/L/Hull.lagda.md:74` needs
`Formula (⊥* {ℓ}) (suc k)`. `[LJ-1.451]` measured that gap.

`cover` at `src/L/BoundedSubset.lagda.md:918-919`:

    cover : (y : S) → ⟨ y ∈ˢ M ⟩
          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁

This formula describes the level at the class carrier. `cover`
concludes membership in `Lset γ` inside the model. The formula does
not produce that covering ordinal. I do not claim it unblocks the
condensation lemma.

## THE PRICE

The formula and both adequacy directions are already in the tree.

- Formula: `LsetGraphAt` at `src/L/Coding/Sequence.lagda.md:349`.
- Out: `Lset-only` at `src/L/Hierarchy.lagda.md:334-335`, with `IsOrd`.
- In: `Lset-defines` at `src/L/Hierarchy.lagda.md:646-648`, with `IsOrd`.

If this task had not landed them, the figure for building them
would be **0 new `src/` lines**. They are delivered. This task
landed an alias at the names the brief chose.

What remains unpaid, and is not this task:

1. The hull-language packaging. `[LJ-1.451]` named it
   `MissingFormula` at
   `agents/tasks/LJ-1-451/Probe451.agda:97-100`.
2. The brief's `lsetAt-out` without `IsOrd`. Unbuilt. Unmeasured.
   The tree does not deliver it.

Basis of the 0: the probe inhabits the delivered terms
(`Probe458.agda:48`, `:56`, `:66`). No new constructor. No new
recursion. The comparable `src/L/Coding/Base.lagda.md:248-295` is
47 lines for four formulas at a flat shape. A stage is not flat.
Nothing is funded against that comparable. The measurement that
narrows the brief's 90-to-300 band is this inventory: the stage
formula is already written.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and
untouched here. One Agda process at a time, every dependency warm,
from the repository root. The probe interface was deleted before
every kept run.

- W3, three forced rechecks: see the table above. Median **1.58 s**,
  peak RSS **386154496 bytes**. Exit 0.
- Full file, three forced rechecks. The obligation is in the file.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 1.40 | 379338752 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 1.38 | 379371520 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 1.44 | 379355136 |

Median wall **1.40 s**. Peak RSS **379371520 bytes**. Exit 0 every
time. Each printed `Checking`. No heap event. The first full check
`runs/full-1.out` was 1.58 s and 379355136 bytes, also exit 0. It
is not one of the three forced rechecks.

- Witness meter, one obligation: 0 UNRESOLVED of 1, 1.36 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name `LsetAt`
  is in scope.

## 3. C-42 sweep

This return is not a refutation. Premise 6 named one grep. That
grep measured the identifiers `LsetAt`, `lsetFo`, `LsetFo`,
`isLsetAt` and `levelAt`. It did not measure `LsetGraphAt`.

Sweep of the shape "a `Formula` whose satisfaction speaks about
`Lset` at a slot":

- Named `LsetAt` in `src/`: **0**.
- Named `LsetGraphAt` in `src/`: **1** constructor, plus alias
  `LsetGraph`, plus bounded restatement `graphBndAt`.
- Hull-language formula for `Lset` (`Formula Code` or
  `Formula (⊥* {ℓ})`): **0**. That is `[LJ-1.451]`'s site, not
  this one.

No cure is priced. The class-carrier formula is delivered. The
hull transplant is the remaining front on `levelIn`.

## 4. What the next brief needs

- Do not order `LsetAt : Formula S n` again. It is `LsetGraphAt`.
- The delivered adequacy needs `IsOrd`. The brief's type without
  `IsOrd` is not delivered. A next brief that wants that stronger
  type must order a proof, not an alias.
- Do not send `levelIn` down the hull-language route with this
  formula as the missing piece. `[LJ-1.451]` still holds:
  `Code` has `base` and `wit` only
  (`src/L/Hull.lagda.md:72-74`). `wit` needs
  `Formula (⊥* {ℓ}) (suc k)`. `LsetAt` is `Formula S n`.
- `cover` still needs a producer. A description of the level is
  not a covering ordinal.
- What the statement cost: 32 non-blank non-comment lines, W3
  median 1.58 s, full median 1.40 s, peak RSS 386154496 bytes.
  What the shape resisted: the brief's grep, not the tree. What I
  had to weaken: the out-direction keeps `IsOrd`, which the brief
  omitted. What I could not close: `LsetAt-out-brief`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not
  used. It is the retired dispatch index. This task measures a
  live chapter.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live `Sequence` and
  `Hierarchy` chapters.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote:
  `# ARCHIVED 2026-08-20`. Declined, not used. The per-episode
  journal is retired. The history of this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this
  task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`.
  Declined, not used. The live clauses that bound this slot are
  W2 and W4. W4 did not fire: nothing was retired.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`.
  Used: Φ is a theorem of LST, not an axiom this tree fails. The
  tree's analogue at the class carrier is `LsetGraphAt`. This is
  why W3 is inhabited and why the task is not a literature NO-GO.
- `dev/literature/truncation-and-selection.md`: read at `:1`.
  Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. W3 is a formula-inventory question. It is
  not a truncation question.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Also read at `:40`. Quote:
  `- **Q2 (hierarchy, condensation, acceptability).** The J-hierarchy is indexed`.
  Declined as not used for the term. Q2 documents condensation
  for `J_α`, the retired route. This tree's `Lset` is not that
  hierarchy. The digest does not cover definability of `Lset`.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`.
  Quote:
  `# Glossary review: the 119 pre-protocol entries`.
  Declined, not used. No glossary entry is at issue.

The brief also named `dev/literature/j-hierarchy.md:1`. Quote:
`# The J-hierarchy, S vs J stratification, condensation, well-order, acceptability`.
Read. Used as contrast. It documents `J_α`. This tree's `Lset` is
not that hierarchy. It is not a CANDIDATE in the injected block.
It did not show the shape to be an axiom.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `LsetAt-out-brief`.
- I did not add a `Code` constructor.
- I did not postulate. I did not add an axiom.
- I did not weaken `Lset` to a hypothesis.
- I did not write a well-founded recursion inside a formula.
- I did not claim the formula unblocks the condensation lemma.
- I did not write `review-of-LsetAt.md`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-458/`:

- `lj-1.458-report.md`, this report
- `Probe458.agda`, W3 and the obligation
- `runs/`, the Agda transcripts named above
