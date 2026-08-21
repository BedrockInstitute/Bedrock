# LJ-1.479 report: step two, uniqueness of the witness

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-479/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-479/Probe479.agda`:

    HullClosedLset : (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

where `M` is the definable hull, copied from
`src/L/BoundedSubset.lagda.md:903-914`. Land nothing in `src/`.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## PREDECESSOR, READ FIRST

`[LJ-1.474]` is GO. The heading `## VERDICT` is at
`agents/tasks/LJ-1-474/lj-1.474-report.md:70`. Quote at `:72-75`:

> **GO.** `zero-code` typechecks. `lset-codes` typechecks. The witness
> meter reads `0 UNRESOLVED of 1`, `probe_red=False`
> (`runs/witness.out:1-2`). I did not add a hypothesis on `X`. I did not
> postulate. I did not inhabit `levelIn` or `lset-code`.

The delivered term is at `agents/tasks/LJ-1-474/Probe474.agda:124-125`.
I do not stop. I do not inhabit a NO-GO as if it were GO.

`[LJ-1.462]` is NO-GO at D-10 step 3
(`agents/tasks/LJ-1-462/lj-1.462-report.md:77`). It states step 2 as a
type at `Probe462.agda:136-138` and leaves it unbuilt. I take that type.
I do not inhabit `[LJ-1.462]`'s failed step 3. I do not build `levelIn`.
I do not touch step 4. `[LJ-1.477]` is a critic-upheld NO-GO on that
route (`agents/tasks/LJ-1-477/lj-1.477-report.md:97`).

## D-10, BEFORE ANY AGDA

`wit k ψ vs` is the witness of a satisfiable formula
(`src/L/Hull.lagda.md:73-74`, `search` at `:79-81`). A witness is a set
that satisfies ψ. It is `Lset y` only if ψ pins that set uniquely.

Delivered uniqueness is `Lset-only` at
`src/L/Hierarchy.lagda.md:334-335`:

    Lset-only : ⟨ γ ⊨ LsetGraphAt w b ⟩ → IsOrd (fst (lookup b γ))
              → fst (lookup w γ) ≡ Lset (fst (lookup b γ))

It gives uniqueness of the value slot. It carries an extra `IsOrd` on
the argument slot. `[LJ-1.458]` recorded that extra hypothesis
(`agents/tasks/LJ-1-458/lj-1.458-report.md:80-84`). The stronger type
without `IsOrd` is `LsetAt-out-brief` at `Probe458.agda:69-73`. Unbuilt.

`inHull` puts `toSet (val c)` in the hull (`src/L/Hull.lagda.md:117-118`).
`feed c = wit (suc (countFo LsetGraph)) packaged (c ∷ lset-codes)` is
delivered at `Probe474.agda:130-131`. `inHull (feed c)` is membership
of `val (feed c)`, not of `Lset y`. The join needs
`fst (val (feed c)) ≡ Lset y`. That equation is `Lset-only` at the
packaged formula. `Lset-only` spends `IsOrd`.

The hull member `y` carries `⟨ y ∈ˢ M ⟩` only. The brief forbids an
ordinality hypothesis on `y`. The live sources of `IsOrd` from
membership are:

- `mem-ord` at `src/L/Ordinal.lagda.md:221`: `IsOrd A → ⟨ x ∈ˢ A ⟩ → IsOrd x`
- `ω-mem-ord` at `src/L/Ordinal.lagda.md:258`: `⟨ y ∈ˢ ω ⟩ → IsOrd y`
- `isOrdAt-out` at `src/L/BoundedSubset.lagda.md:813`: satisfaction of
  `isOrdAt`, not hull membership
- `β-ord` at `src/L/BoundedSubset.lagda.md:939`: `⟨ δ ∈ˢ β ⟩ → IsOrd δ`,
  inside `module Condense`, after `levelIn`

None of these take `⟨ y ∈ˢ M ⟩`. `Hull⊆L` at
`src/L/Hull.lagda.md:330-331` gives `⟨ x ∈ˢ Lset α ⟩`, not `⟨ x ∈ˢ α ⟩`.
`mem-ord` does not apply. The hull carries no ordinality.

Uniqueness therefore fails at the stated type. `wit`'s value need not
be `Lset y`. The join is not written. The task stops at this point.

## VERDICT

**NO-GO at uniqueness.** `pins` typechecks. It is `Lset-only`. The
extra `IsOrd` has no source at a hull member. `pins-no-ord` is
well-formed and unbuilt. `hull-ord` is well-formed and unbuilt. The
obligation term `HullClosedLset` is not written. Witness meter: 1
UNRESOLVED of 1, `probe_red=False` (`runs/witness.out:1-2`).

This is an obstruction of the `wit` then `inHull` join. It is not a
refutation of `HullClosedLset`. I did not build a term of the
negation.

The NO-GO is stated in
`agents/tasks/LJ-1-479/review-of-HullClosedLset.md`. That file is the
critic's input. It does not close the task.

## W2 (DD4)

The mathematics is written once at a generic carrier. The module is
generic in `ℓ`. `pins` is generic in the arity `n`. `lam`, `X` and the
limit hypotheses stay parameters of `HullStage`. No ordinal is fixed.
No second copy at a concrete stage. The conflict the clause names did
not arise.

## W4 (DD13)

Nothing was retired. No module moved to `archive/`.

## 1. What was built

All in `agents/tasks/LJ-1-479/Probe479.agda`, module
`LJ-1-479.Probe479 {ℓ} (lem)`.

- W3 inhabited: `pins = Lset-only` (`:50-54`). Site
  `src/L/Hierarchy.lagda.md:334-335`. Extra `IsOrd` on the argument
  slot.
- Uniqueness without `IsOrd` stated: `pins-no-ord` (`:60-64`).
  Unbuilt. Same type as `LsetAt-out-brief`
  (`agents/tasks/LJ-1-458/Probe458.agda:69-73`).
- Telescope `HullOnV.HullStage` (`:84-96`), copied from
  `src/L/BoundedSubset.lagda.md:903-914`. The outer `S` is the class
  carrier (`open hPropStructure 𝒮ʟ` at `:40`). The hull carrier is
  `VS.S` from `𝒮ᵥ` (`:79`). A second open of `S` failed with
  `[AmbiguousOverloadedProjection]` (`runs/full-ambiguous.out:2-8`).
- The missing source stated: `hull-ord` (`:103-104`). Unbuilt.
- Step 2 as type: `HullClosedLset` (`:109-111`). Unbuilt. Inside
  `HullOnV.HullStage`. No top-level alias. No term named
  `HullClosedLset` at the module root.
- No `feed`. No `inHull`. No `lset-codes`. The join is not written.

Measured non-blank non-comment lines: 49. Total lines: 111. The brief
estimate was about 150 lines, of which the obligation is about 25.
Nothing is funded against the estimate. The file stops at uniqueness.

## STEP ONE, W3

**Uniqueness with `IsOrd` is delivered. Uniqueness without it is
not.** `pins` (`Probe479.agda:50-54`) is the brief's type, taken from
`Lset-only`. Inhabited. The obligation was omitted in the W3-only
file.

`IsOrd` has no source at a hull member. The live lemmas named in
`## D-10, BEFORE ANY AGDA` take membership in an ordinal, membership
in `ω`, satisfaction of `isOrdAt`, or membership in the collapse's
`β` after `levelIn`. None take `⟨ y ∈ˢ M ⟩`.

Three forced rechecks of the W3-only file (`pins` only, obligation
omitted), `_build` interface removed before each, dependencies warm,
caliber `-A64m -I0 -M8g`, one Agda process. Exit 0 every time. Each
printed `Checking`.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-1.out` / `w3-1.time` | 1.86 | 385368064 |
| `runs/w3-2.out` / `w3-2.time` | 1.81 | 385400832 |
| `runs/w3-3.out` / `w3-3.time` | 1.82 | 385384448 |

Median wall **1.82 s**. Median peak RSS **385384448 bytes**. No heap
event. The first W3-only check `runs/w3-0.out` was 2.23 s and
348880896 bytes, also exit 0, also printed `Checking`. It is not
one of the three forced rechecks. The brief estimate for W3 was
about 12 lines and under 15 seconds. The measured median is under
that estimate.

## STEP TWO, THE OBLIGATION

Omitted. Uniqueness without `IsOrd` failed. The obligation is not
inhabited. A truncated conclusion was not written. `IsOrd` was not
added as a hypothesis.

`feed` and `inHull` were not applied. `[LJ-1.474]`'s codes remain
codes. They do not identify `val (feed c)` with `Lset y`.

Step 4 was not reached. `[LJ-1.477]` stands.

## WHAT LEVELIN STILL OWES

The four steps, as types and at `file:line`. I do not claim
`levelIn`.

1. Collapse membership. Built.

       C.πX-member :
           (z : S) → ⟨ z ∈ˢ C.πX ⟩
         → ∥ Σ[ y ∈ S ] (⟨ y ∈ˢ M ⟩ × (C.π y ≡ z)) ∥₁

   Site: `src/V/Collapse.lagda.md:78-79`. Inhabited as `step1` at
   `agents/tasks/LJ-1-462/Probe462.agda:133-134`.

2. Hull closure. This task. NO-GO at uniqueness.

       HullClosedLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ Lset y ∈ˢ M ⟩

   Type at `agents/tasks/LJ-1-462/Probe462.agda:136-138`. Restated
   unbuilt at `Probe479.agda:109-111`. Companion `πCommuteLset` at
   `Probe462.agda:140-142` stays unbuilt.

3. Codes for the constants. Built. The value equation is not.

       lset-codes : Vec Code (countFo LsetGraph)

   Site: `agents/tasks/LJ-1-474/Probe474.agda:124-125`. GO. The
   unbuilt equality remains `lset-code` at
   `Probe462.agda:109-111`. This task measured that the equality
   is `Lset-only`, which needs `IsOrd`, which the hull does not
   supply.

4. Absoluteness. Critic-upheld NO-GO on the computation-law route.

       πCommuteLset :
           (y : S) → ⟨ y ∈ˢ M ⟩ → C.π (Lset y) ≡ Lset (C.π y)

   `[LJ-1.477]` (`agents/tasks/LJ-1-477/lj-1.477-report.md:97`). I
   did not reopen that route.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense` (`src/L/BoundedSubset.lagda.md:917`).

## 2. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root. The probe interface was deleted before every kept
run.

- W3, three forced rechecks: see the table above. Median **1.82 s**,
  **385384448 bytes**. Exit 0.
- Full file, three forced rechecks. The D-10 types are in the file.
  The obligation is omitted.

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/full-recheck-1.out` / `full-recheck-1.time` | 2.50 | 480215040 |
| `runs/full-recheck-2.out` / `full-recheck-2.time` | 2.76 | 440811520 |
| `runs/full-recheck-3.out` / `full-recheck-3.time` | 2.55 | 480165888 |

Median wall **2.55 s**. Median peak RSS **480165888 bytes**. Exit 0
every time. Each printed `Checking`. No heap event. The first full
check after the D-10 types, `runs/full-0.out` / `full-0.time`, was
2.69 s and 480215040 bytes, also exit 0. It is not one of the three
forced rechecks.

- Witness meter, one obligation: 1 UNRESOLVED of 1, 2.13 s,
  `probe_red=False` (`runs/witness.out:1-2`). The name
  `HullClosedLset` is not in scope at the module root. That is the
  intended NO-GO reading.

## 3. What NO-GO earns, and what is still owed

NO-GO says the witness is not the set. `[LJ-1.474]`'s codes buy a
`Code`. They do not buy `fst (val (feed c)) ≡ Lset y`. The hull
route needs uniqueness before the join. Uniqueness is `Lset-only`.
`Lset-only` needs `IsOrd`. `IsOrd` has no source at `⟨ y ∈ˢ M ⟩`.

`cover` is untouched. `levelIn` stays an unpaid hypothesis of
`module Condense`.

What this task does not settle:

- It does not inhabit `HullClosedLset`.
- It does not inhabit `pins-no-ord` or `hull-ord`.
- It does not inhabit `lset-code` or `levelIn`.
- It does not refute `HullClosedLset`.
- It does not add `IsOrd` on `y`.
- It does not apply `feed` or `inHull`.
- It does not measure the meeting of `Lset-only` at the class
  carrier with `wit`'s satisfaction at the stage
  (`agents/tasks/LJ-1-462/lj-1.462-report.md:273-277`).
- It does not edit `src/`.
- It does not pay `cover`.
- It does not touch step 4.

C-42: this is not a refutation. I did not search the tree for a false
shape.

## 4. What the next brief needs

- Do not order `HullClosedLset` by `wit` then `inHull` without a
  source of uniqueness. `pins` is `Lset-only`. It needs `IsOrd`.
- `IsOrd` has no source at a hull member. Do not assume
  `⟨ y ∈ˢ M ⟩ → IsOrd y`. That type is `hull-ord` at
  `Probe479.agda:103-104`. Unbuilt.
- Do not add `IsOrd` on `y` unless a new brief names that type.
  The brief of this task forbade it. The archived companion
  `level-in` at
  `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:240-241`
  carries `IsOrd` as a hypothesis, not as a conclusion from hull
  membership.
- `[LJ-1.474]`'s `lset-codes` and `feed` still stand. They produce
  a code. They do not identify its value with `Lset y`.
- Even with `IsOrd`, `Lset-only` reads the class carrier
  (`src/L/Hierarchy.lagda.md:73` opens `𝒮ʟ`). `wit` searches in
  `TermAlgebra` over the stage (`src/L/Hull.lagda.md:323`). That
  meeting is still unmeasured.
- Step 4 remains a critic-upheld NO-GO on the computation-law
  route. Do not reopen it as if this task had closed step 2.
- What the statement cost: 49 non-blank non-comment lines, W3
  median 1.82 s, full median 2.55 s, peak RSS 480215040 bytes on
  the kept rechecks. What the shape resisted: uniqueness without
  `IsOrd`, and `IsOrd` at a hull member. What I had to weaken:
  nothing of the obligation. The obligation is unbuilt. What I
  could not close: `HullClosedLset`, `pins-no-ord`, `hull-ord`.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: read at `:1`. Quote:
  `# THE `LJ` DISPATCH INDEX, archived 2026-08-18`. Declined, not used.
  It is the retired dispatch index. This task measures a live uniqueness
  lemma.
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

The archived companion that carries `IsOrd` as a hypothesis is not
in those candidates. It is at
`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:240-241`.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: read at `:95`. Quote:
  `> By 2.7 there is a Σ₀ formula Φ(z, v, γ) of LST such that`.
  Also read at `:96`. Quote:
  `> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`.
  Used: Φ pins `v` as `L_γ`. The tree's analogue is `Lset-only`,
  and that analogue adds `IsOrd`. Devlin's biconditional is at an
  ordinal index `γ`. The hull member `y` is not that index.
- `dev/literature/truncation-and-selection.md`: read at `:1`. Quote:
  `# Truncation and selection: how the two literatures pick a witness`.
  Declined, not used. The obstruction is uniqueness, not the
  selection of a least witness.
- `dev/literature/terms-2026-08.md`: read at `:1`. Quote:
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  Declined, not used. No glossary term is at issue.
- `dev/literature/digest.md`: read at `:1`. Quote:
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined, not used. No rud-route step is consulted.
- `dev/literature/glossary-review-2026-08.md`: read at `:1`. Quote:
  `# Glossary review: the 119 pre-protocol entries`.
  Declined, not used. No glossary entry is at issue.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not inhabit `HullClosedLset`, `pins-no-ord` or `hull-ord`.
- I did not add an ordinality hypothesis on `y`.
- I did not postulate.
- I did not apply `feed` or `inHull`.
- I did not inhabit `levelIn`.
- I did not touch step 4.
- I did not pay `cover`.
- I did not hide the extra `IsOrd` in a `subst`.

## WORKING TREE, AS THIS REPORT DESCRIBES IT

Nothing committed, nothing pushed. No master edited. `src/`
untouched.

New files, all in `agents/tasks/LJ-1-479/`:

- `lj-1.479-report.md`, this report
- `Probe479.agda`, W3, `pins-no-ord`, the telescope and the unbuilt types
- `review-of-HullClosedLset.md`, the stated NO-GO
- `runs/`, the Agda transcripts named above
