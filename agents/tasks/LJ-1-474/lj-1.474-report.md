# LJ-1.474 report: the hull codes for the constants of LsetGraph

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-474/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-474/Probe474.agda`:

    lset-codes : Vec Code (countFo LsetGraph)

Land nothing in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## PREDECESSOR, READ FIRST

`[LJ-1.466]` is a stated NO-GO. The heading `## VERDICT` is at
`agents/tasks/LJ-1-466/lj-1.466-report.md:60`. Quote at `:62-66`:

> **NO-GO.** `how-many` is not zero. It is not a closed integer. Every
> visible constant is `numeralL k` for `k ∈ {0,1,...,11}`. None of those
> sets lies in a general hull carrier `⟪ X ⟫`. Mapping `base` over
> `constantsFo LsetGraph` does not typecheck. I did not inhabit
> `lset-codes`.

I did not inhabit that NO-GO type by `base`. The named type of this brief
is the same name at a different construction: `wit`, not `base`.

`[LJ-1.472]` is GO. The heading `## VERDICT` is at
`agents/tasks/LJ-1-472/lj-1.472-report.md:151`. Quote at `:153-156`:

> **GO.** `zero-in-hull` typechecks. `numerals-in-hull` typechecks. The
> witness meter reads `0 UNRESOLVED of 1`, `probe_red=False`
> (`runs/witness.out:1-2`). I did not add a hypothesis on `X`. I did not
> postulate. I did not inhabit `levelIn` or `lset-codes`.

Neither verdict is missing. I did not stop.

## D-10, BEFORE ANY AGDA

`[LJ-1.472]`'s obligation concludes membership
`⟨ fst (numeralL k) ∈ˢ H.T.Hull ⟩` at `Probe472.agda:217`. A `Code` is
not that. Route 1 names a code before it names the membership.

Quote, `agents/tasks/LJ-1-472/Probe472.agda:108-109`:

    c0 : Code
    c0 = wit 0 φ0 []

Quote, `agents/tasks/LJ-1-472/Probe472.agda:210-211`:

    ck : (k : ℕ) → Code
    ck k = wit 0 (φk k) []

The membership at `:217-223` is `inHull (ck k)` after `val-wit` and
`numeral-unique`. The code is `ck k`. W3 of this task is that code at
`k = 0`, named `zero-code`. The vector maps `ck` along
`constantsFo LsetGraph`.

`constantsFo` returns `Vec CS.S` (`src/FOL/Manipulation/Parameters.lagda.md:105`).
`ck` takes `ℕ`. A map needs `CS.S → ℕ`. `[LJ-1.466]`'s census at
`lj-1.466-report.md:188-189` says every visible `con` is `numeralL k`
for `k ∈ {0,1,...,11}`. The decoder searches those twelve tags by `lem`
on `s ≡ numeralL k`. It does not add a hypothesis on `X`.

## VERDICT

**GO.** `zero-code` typechecks. `lset-codes` typechecks. The witness
meter reads `0 UNRESOLVED of 1`, `probe_red=False`
(`runs/witness.out:1-2`). I did not add a hypothesis on `X`. I did not
postulate. I did not inhabit `levelIn` or `lset-code`.

The term lives inside `HullStage` at `Probe474.agda`, copied from
`src/L/BoundedSubset.lagda.md:903-914`. A top-level alias
`lset-codes = HullStage.lset-codes` is there because the meter reads
`Target.lset-codes` (`scripts/pod/witness.py:278`) and a named
parameterised module does not lift the name.

## W2 (DD4)

The mathematics is written once at a generic carrier. `succFo` and
`numeralFo` are generic in `K` (`Probe474.agda:50-60`). The module is
generic in `ℓ`. `lam`, `X` and the limit hypotheses stay parameters.
Instantiation is at `⊥*` for `wit`. No ordinal is fixed. No second copy
at a concrete stage. The conflict the clause names did not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## 1. What was built

All in `agents/tasks/LJ-1-474/Probe474.agda`, module
`LJ-1-474.Probe474 {ℓ} (lem)`.

- Telescope `HullStage`, copied from
  `src/L/BoundedSubset.lagda.md:903-914`.
- W3: `zero-code` at `k = 0`, `wit` at `∀̇∈ (var zero) ⊥̇`
  (`Probe474.agda:110-111`). Same term as `Probe472.agda:108-109`.
- `succFo` and `numeralFo`, generic in `K`, copied from
  `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:367-373`.
- Packaging `packaged = absFo {ℓz = ℓ} LsetGraph` (`:63-64`), same term
  as `Probe462.agda:66-67`.
- `consts = constantsFo LsetGraph` (`:66-67`). Type `Vec CS.S`.
- `tagOf` (`:82-83`): `CS.S → ℕ` by `lem` on `s ≡ numeralL k` for
  `k = 0,1,...,11`. Bound 12 from `[LJ-1.466]`'s census, not from a
  closed `countFo`. Default 0 if none match.
- `ck k = wit 0 (φk k) []` (`:121-122`). Same term as
  `Probe472.agda:210-211`.
- Obligation: `lset-codes = map (λ s → ck (tagOf s)) consts` (`:124-125`).
- `feed` (`:130-131`): `[LJ-1.462]`'s `feed` with the extra `Vec` filled.
  Not `lset-code`. Not `levelIn`.
- Top-level alias for the witness meter (`:137`).

Measured non-blank non-comment lines: 67. Total lines: 137. The brief
estimate was about 140 lines, of which the obligation is about 25.
Nothing is funded against the estimate.

## STEP ONE, W3

**One code is produced from `[LJ-1.472]`'s route 1.** `zero-code = wit 0 φ0 []`
at `Probe474.agda:110-111`. The obligation was omitted in the W3-only
file. The vector is not out of reach at its cheapest point.

Three forced rechecks of the W3-only file (`zero-code` only, obligation
omitted), `_build` interface removed before each, dependencies warm,
caliber `-A64m -I0 -M8g`, one Agda process. Exit 0 every time. Each
printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.91 | 461864960 |
| `runs/w3-2.out` / `w3-2.time` | 1.89 | 461848576 |
| `runs/w3-3.out` / `w3-3.time` | 1.90 | 461864960 |

Median wall **1.90 s**. Median peak RSS **461864960 bytes**. No heap
event. The first green W3-only check `runs/w3-0.out` was 1.95 s and
461914112 bytes, also exit 0. It is not one of the three forced
rechecks.

## STEP TWO, THE OBLIGATION

Inhabited. Route 1. No extra hypothesis on `X`. `ck k` is the code.
`tagOf` recovers `k` from a class-carrier constant. `map` along
`constantsFo LsetGraph` fills `Vec Code (countFo LsetGraph)`.

The length is still not a closed integer. `satGraphAt` is still opaque
(`src/L/Coding/Graph.lagda.md:203-205`). `constantsFo LsetGraph` does
not reduce to a cons-list. The `map` is typed against that stuck
vector. I report no exact integer.

`tagOf` is a census decoder, not a uniqueness proof. It searches
`numeralL 0` through `numeralL 11` by `lem`. `[LJ-1.466]` printed 105
visible `con`, all in that range (`lj-1.466-report.md:188-189`). The
opaque `satGraphAt` was not unfolded. Its pin is `var ≐ var`
(`src/L/Coding/Graph.lagda.md:205`). A constant outside `{0,...,11}`
would be coded as `ck 0`. I did not print such a constant. I did not
prove `fst (val (ck (tagOf s))) ≡ fst s`.

## WHAT LEVELIN NOW OWES

The extra `Vec Code` that `[LJ-1.462]` named is inhabited. `feed` now
has type `(c : Code) → Code` (`Probe474.agda:130-131`). I do not claim
`levelIn`. The unbuilt types from `[LJ-1.462]`, still unbuilt here:

    lset-code :
      (c : Code) → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

    lset-code-ord :
      (c : Code) → IsOrd (fst (val c))
      → Σ[ d ∈ Code ] (fst (val d) ≡ Lset (fst (val c)))

    HullClosedLset :
      (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

    πCommuteLset :
      (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

    LevelIn :
      (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩

Sites: `agents/tasks/LJ-1-462/Probe462.agda:109-111` (`lset-code`),
`:118-121` (`lset-code-ord`), `:136-142` (step 2), `:147-149`
(`LevelIn`). Step 1 is delivered (`Probe462.agda:133-134`).

The join to `lset-code` is `d = feed c`, then the equality. That
equality still needs three facts this task did not prove:

1. `tagOf` hits the right `k` on every constant of `LsetGraph`, so
   `vals lset-codes` is the constant vector of `LsetGraph` read in the
   hull carrier.
2. `Lset-only` at `src/L/Hierarchy.lagda.md:334-335` reads `wit`'s
   satisfaction of `absFo LsetGraph`. `[LJ-1.462]` measured that this
   meeting is unmeasured (`lj-1.462-report.md:273-277`).
3. `IsOrd` on `fst (val c)`. `lset-code` as stated has none.
   `lset-code-ord` records the correction. The consumer of `levelIn`
   has `IsOrd`.

I did not time that join. A price taken from this file's 4.81 s would
be the packaging plus the vector, not the equality.

Step 2 stays a pair of types. Step 4 is the same type as
`πCommuteLset`. `cover` is untouched.

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before every kept
run.

- W3, three forced rechecks: see the table above. Median **1.90 s**,
  **461864960 bytes**. Exit 0.
- Full file, three forced rechecks. The obligation, the alias, `tagOf`
  and `feed` are in the file.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 4.81 | 1135837184 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 4.82 | 1135804416 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 4.77 | 1135820800 |

Median wall **4.81 s**. Median peak RSS **1135820800 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the obligation, `runs/full-0.out` / `full-0.time`, was
4.76 s and 1135837184 bytes, also exit 0. It is not one of the three
forced rechecks.

- Witness meter, one obligation: 0 UNRESOLVED of 1, 2.05 s,
  `probe_red=False` (`runs/witness.out:1-2`). Exit 0.

## 3. What GO earns, and what is still owed

GO closes the named `Vec Code` step of the hull route. `levelIn` is
now a join of the types in `## WHAT LEVELIN NOW OWES`, not an open
question about the extra vector.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `lset-code` or `lset-code-ord`.
- It does not inhabit `levelIn`.
- It does not refute `levelIn`.
- It does not restrict `X` in the consumer telescope.
- It does not unfold `satGraphAt`.
- It does not produce a closed integer for `countFo LsetGraph`.
- It does not prove `fst (val (ck (tagOf s))) ≡ fst s`.
- It does not edit `src/`.
- It does not pay `cover`.
- It does not land `numeralFo` in `src/`. The formula lives in the probe.

C-42: this is not a refutation. I did not search the tree for a false
shape.

## 4. What the next brief needs

- `lset-codes` is delivered at a general `X`, by `wit` at `numeralFo`
  after `tagOf`. Site: `agents/tasks/LJ-1-474/Probe474.agda:124-125`.
- Do not order a hypothesis `⟨ fst (numeralL k) ∈ˢ X ⟩`. The codes do
  not use `base`.
- `[LJ-1.462]`'s `feed` is now `(c : Code) → Code` at
  `Probe474.agda:130-131`. The next unpaid object on this route is
  `lset-code` / `lset-code-ord`, then step 2, then the join to
  `levelIn`.
- `tagOf` is bounded by 12 from `[LJ-1.466]`'s visible census. A later
  brief that needs the values, not only the codes, must prove the
  decoder, or replace it.
- `countFo LsetGraph` is still not a closed literal. Do not fund a
  later task against an exact length.
- What the statement cost: 67 non-blank non-comment lines, W3 median
  1.90 s, full median 4.81 s, peak RSS 1135837184 bytes on the kept
  rechecks. What the shape resisted: `ck` takes `ℕ` and
  `constantsFo` returns `Vec CS.S`. The decoder is the extra step.
  What I had to weaken: nothing of the obligation. The decoder
  defaults to 0 outside `{0,...,11}`. What I could not close:
  `lset-code`, `levelIn`, the value equation, a closed integer for
  `how-many`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live formula.
- `archive/dev/JOURNAL-archived.md`: read at `:1`. Quote:
  `# Archived journal: the retired route`. Declined, not used.
  Retired-route journal. The consumer is the live `BoundedSubset`
  chapter.
- `archive/dev/JOURNAL.md`: read at `:1`. Quote: `# ARCHIVED 2026-08-20`.
  Declined, not used. The per-episode journal is retired. The history
  of this task is this directory.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this task.
- `archive/dev/DD-archived.md`: read at `:1`. Quote:
  `# THE `DD` RULING SERIES, archived in full 2026-08-18`. Declined,
  not used. The live clauses that bound this slot are W2 and W4. W4
  did not fire: nothing was retired.

The formula I wrote is not in those candidates. It is at
`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:367-373`.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`.
  Used: Φ is the LST analogue of the class-carrier graph. The hull
  codes measured here name the tag numerals of this tree's
  `LsetGraph`, so `wit` can take the packaged graph. Devlin's Φ is a
  formula of LST. The vector is a fact about this tree's coding.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. The codes are `wit` constructors. No truncation
  question is at issue.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. The formula was taken from the archived live
  chapter, not from the rud-route digest.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`.
  Declined, not used. No glossary entry is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `lset-code` or `levelIn`.
- I did not add a `Code` constructor.
- I did not postulate. I did not add a hypothesis placing a numeral
  in `X`.
- I did not unfold `satGraphAt`.
- I did not pay `cover`.
- I did not write `review-of-lset-codes.md`. The term inhabits.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-474/`:

- `lj-1.474-report.md`, this report
- `Probe474.agda`, W3, `numeralFo`, `tagOf`, the telescope and `lset-codes`
- `runs/`, the Agda transcripts named above
