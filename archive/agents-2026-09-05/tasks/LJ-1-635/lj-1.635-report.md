# [LJ-1.635] report: the bill splits at omega; the split is forced by the order, not by Init

## HEAD

head_slot: coder
machine: shared
task: LJ-1.635
obligation: agents/tasks/LJ-1-635/Probe635.agda::gch-splits-at-ω
verdict: GO. The split term typechecks and is green: `runs/final-3.out`,
exit 0, 1.83 s, 406.7 MB peak, under the 300 s cap, and it postdates the
last edit of the probe (file mtime 1787668281, run mtime 1787668286).
The caliber on every run is the program's `GHCRTS=[-A64m -I0 -M2g]`,
read from the pane and recorded in every `.out`. I did not set it. One
Agda process ran at a time. No hole and no postulate stand in the final
file. Nothing was written under `src/`. No commit, no push. `git status`
shows only `agents/tasks/LJ-1-635/` as new.

This report was a skeleton before any full-probe run, and each section
was filled as its answer landed (C-22).

## W3: THE TRICHOTOMY CROSSING, MEASURED ALONE

`agents/tasks/LJ-1-635/runs/Tri.agda` was written first and typechecked
ALONE: `runs/tri-1.out`, exit 0, 1.42 s, 284 MB peak, under the 120 s
cap. It carries `Triω` (the two live cases of `Tri A ω` once the bill's
clause kills the first case, `runs/Tri.agda:54-55`) and `tri-above`
(the step itself, `runs/Tri.agda:57-63`).

**The crossing the brief flagged does not exist.** The brief's premise 4
worried that "`fst κ` is a `V ℓ` and `ord-tri` wants an `S`". Under
`open hPropStructure 𝒮ᵥ`, `S` IS `V ℓ`, and `IsOrd` and `ord-tri` are
stated at exactly that carrier. So `ord-tri` applies at `fst κ` by one
application, with no coercion of any kind. `[LJ-1.629]` had already
applied it at this grain (`agents/tasks/LJ-1-629/Probe629.agda:224-230`).
The whole step is: run trichotomy against `ω`, then kill the first case
with the bill's own clause. The Agda is 10 lines (`Triω` plus `tri-above`
plus its local case function). The file is 62 lines because the
discipline notes are part of the deliverable. The brief estimated 40 to
80 lines; the estimate priced the file, not the term, and even then the
file came in under the floor of the range.

**GO**, and the price of the widest unmeasured term is 1.42 s alone, and
0 s on top of the probe's frame: the probe's green run (1.83 s) and its
holed floor run (2.36 s) are within cache noise of each other.

## THE TERM

`agents/tasks/LJ-1-635/Probe635.agda` is 123 lines and carries three
sections:

| row | what | evidence |
|---|---|---|
| `Concl` | `GCHStatement`'s conclusion at one site, copied letter for letter from `src/L/GCH.lagda.md:65-68`. The only change is the two added arguments (zf and κ). | `Probe635.agda:73-77` |
| `gch-splits-at-ω` | THE OBLIGATION, stated as the brief names it. Both halves are hypotheses; neither is discharged. | `Probe635.agda:90-104` |
| `above-half-misses-ω` | the forcing row for the addendum's question, see the next section. | `Probe635.agda:122-123` |

The body of the obligation is one dispatch on the W3 step: the equal
case goes through subset eta (`Σ≡Prop`, because the second component of
an `S` is a proposition, so `fst κ ≡ ω` IS `κ ≡ ωʟ`) and `sym`, and the
strictly-above case goes to the `above` hypothesis. The case dispatch is
a plain case function, not a `with` scrutinee, per the shape
`[LJ-1.629]` measured: `with` inside a nested `where` walled at 2.4 GB
(`agents/tasks/LJ-1-629/runs/final-5.out`) and the case-function shape
was green (`agents/tasks/LJ-1-629/runs/final-9.out`).

## THE ADDENDUM QUESTION: WHAT FORCES THE SPLIT

The addendum asked: if the measurement suggests the split is forced by
something other than `Init`'s definition, name the term that forces it.
**It is, and the term is `above-half-misses-ω`, which is `∈-irrefl ω`.**

`fst ωʟ` is `ω` by definition (`src/L/Axioms/Infinity.lagda.md:69-70`),
and no set is a member of itself by regularity (`∈-irrefl`,
`src/V/Hierarchy.lagda.md:155`). So the strictly-above hypothesis
`⟨ ω ∈ˢ fst κ ⟩` is FALSE at the only site `κ := ωʟ`. The `above` half
alone can never pay `GCHStatement zf` at that site, so the at-omega half
is not redundant: the split is forced.

Two facts make this worth more than the split itself:

1. **It is an ORDER fact, not an Init fact.** `Probe635.agda` never
   imports `L.Ordinal.SquareLaw`. `Init` plays no role in the split. The
   addendum's reading, that the ω obstruction is an artifact of how
   `Init` is defined (`src/L/Ordinal/SquareLaw.lagda.md:689-694`), is
   correct in one direction and incomplete in the other: `Init`'s second
   conjunct merely rediscovers `∈-irrefl ω` at `ω`. Delete `Init` from
   the tree and the split stays forced.
2. **The textbook does not split at ω because its hypothesis does not
   mention ω.** Jech 13.20 runs one uniform argument indexed by α
   (`dev/literature/devlin-II5.md:502`). This bill conditions on "not in
   ω" (`src/L/GCH.lagda.md:64`), a clause that admits `κ ≡ ω`. The
   split measures the distance between that clause and the uniform
   hypothesis: exactly one site, ω, and exactly one term,
   `above-half-misses-ω`. A uniform argument that reused `above` at ω
   would need `⟨ ω ∈ˢ ω ⟩`, which `∈-irrefl` forbids. The only other
   exit is a bill edit: respell the clause to exclude `κ ≡ ω`, which is
   the mathematician's call, not mine.

## THE FLOOR, THE CAPS, THE RUN LEDGER

Caliber on every run: `GHCRTS=[-A64m -I0 -M2g]`, set by the program on
this pane. Caps, which I set and report: 120 s for the alone W3 run,
300 s for every other run. No run reached a cap. No heap wall occurred.

The floor was measured before the proof, per the owner's ruling of
2026-08-23: the probe ran first with a hole standing in for the case
body. The floor run also caught a real defect, which is the floor's
job: my first spelling took `S` from `𝒮ᵥ`, but `GCHStatement`'s own `S`
is `𝒮ʟ`'s carrier (`src/L/GCH.lagda.md:23-25` opens `_∈ˢ_` from `𝒮ᵥ`
and `S` from `𝒮ʟ`). The chapter's carrier split is copied now
(`Probe635.agda:64-71`).

| run | what | exit | price |
|---|---|---|---|
| `runs/tri-1.out` | W3 ALONE, green | 0 | 1.42 s, 284 MB |
| `runs/floor-1.out` | floor, holed; caught the carrier slip (UnequalTerms at the δ binder) | 42 | 2.33 s, 406 MB |
| `runs/floor-2.out` | floor, carrier fixed, case body still holed (one unsolved meta, at the hole) | 42 | 2.36 s, 406 MB |
| `runs/final-1.out` | real body; `Σ≡Prop`'s target pair stayed a meta | 42 | 1.81 s |
| `runs/final-2.out` | typed `where` binding pins the endpoint; `subst` ran the wrong way | 42 | 1.98 s |
| `runs/final-3.out` | GREEN, postdating the last probe edit | 0 | 1.83 s, 406.7 MB |

The frame (all imports, `Concl`, the statement, the W3 import) costs
2.36 s. The obligation body costs nothing on top of it. This is not a
heavy object, and the frame, not the term, is what the price measures.

Sizes: the probe is 123 lines, of which the obligation is 15
(`Probe635.agda:90-104`); W3 is 62 lines, of which the term is 10
(`runs/Tri.agda:54-63`). The brief gave no line estimate for the
obligation itself; it estimated 40 to 80 for W3, answered above.

Gates run individually: `scripts/gate/lint-agda.py --check` exit 0;
`scripts/gate/check-probes.py --check` clean (9630 tracked files);
`lint-prose.py --check` exit 0 on this report; `grep` for `postulate`,
`TERMINATING` and `{!` over the probe and W3 returns nothing at code
level; no em dash in any file of this scope. `make check` not run: it is
the commit gate and nothing here commits. The ratio bar cannot fire: the
write scope carries no `.lagda.md` master, so the in-fence count is 0
and the bar's divisor is fact 7 of the write scope.

## WHAT THE NEXT BRIEF NEEDS

1. **The campaign owes exactly two things, and can price each.** The
   split names them: the strictly-above half
   `((κ : S) → IsOrd (fst κ) → IsCardinalL κ → ⟨ ω ∈ˢ fst κ ⟩ → Concl zf κ)`
   and the at-omega half `Concl zf ωʟ`. Nothing else stands between the
   two halves and `GCHStatement zf`.
2. **The at-omega half is one site wide.** It is the continuum
   hypothesis itself, at `ωʟ`, in `L`. The forcing row says why it can
   not be folded into the other half.
3. **The shape to keep.** Plain case functions, not `with` in nested
   `where` (the [LJ-1.629] measurement, re-used here at its own site
   and green at 1.83 s). Typed `where` bindings for every `Σ≡Prop`
   path, so the endpoint never stays a meta. The carrier split of
   `src/L/GCH.lagda.md:23-25` (`S` from `𝒮ʟ`, `_∈ˢ_` from `𝒮ᵥ`) at
   every file that copies the bill's types.
4. **What was weakened: nothing.** The statement is the brief's, letter
   for letter. What is not closed: both halves, deliberately, by the
   decomposition's terms.

## PREMISES CHECKED

- Premise 1 HOLDS: `GCHStatement` is `src/L/GCH.lagda.md:59-69`, its
  clause is `:64`, and its conclusion body is `:65-68`. The clause
  excludes `κ ∈ˢ ω` and admits `κ ≡ ω`.
- Premise 2 HOLDS WITH AN OFFSET: the "initial ordinal has ω as a
  member, so ω is not one" comment is `src/L/Ordinal/SquareLaw.lagda.md:
  689-691`, and `Init` itself is `:692-698`. The brief cited 688-694;
  line 688 is blank.
- Premise 3 HOLDS: `agents/tasks/LJ-1-629/lj-1.629-report.md:183-192`
  is "WHAT THE NEXT BRIEF NEEDS" item 1, the respell proposal this task
  measured as a split instead.
- Premise 4 HOLDS, AND ITS WORRY IS REFUTED AS A WORRY: `ord-tri` is
  `src/L/Ordinal/Linear.lagda.md:136` and `Tri` is `:134`. The flagged
  carrier crossing does not exist; see the W3 section.
- The addendum's citation HOLDS: `dev/literature/devlin-II5.md:502` is
  the Jech 13.20 row, "AGREES".

## W2 AND W4

**W2.** Every row is written at a generic carrier: `Concl` at an
arbitrary `zf` and `κ`, `tri-above` at an arbitrary ambient `A`, the
obligation at an arbitrary model. Both future proofs (the strictly-above
half and the at-omega half) consume the same term unchanged. Nothing
landed in `src/`, so no fixed-form chapter was written and no deadline
conflict arose.

**W4.** No module was retired by this return; `dev/ARCHIVE.md` is
untouched and nothing moved to `archive/`. The ideal form of this
measurement written fresh today is the probe as it stands: 123 lines,
one obligation, one forcing row, one alone-typechecked W3. I did not pay
for a worse shape first, except in the one place the comparison is the
finding (the carrier slip the floor run caught, on the record as
`runs/floor-1.out`).

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md` READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:192`: "| LJ-1.116 | At which alpha
  does Upper need sq? | ONLY AT OMEGA, AT THE SITE | Generic demand is
  every infinite ordinal below alpha; the site is omega. Init is false
  at omega and at successors |". This task's forcing row re-measures
  the omega half of that row as the term `above-half-misses-ω`, and
  sharpens it: the fact behind it is `∈-irrefl ω`, not `Init`.
- **`archive/dev/JOURNAL-archived.md` DECLINED.** Line 1: "# Archived
  journal: the retired route". The retired route's journal measures
  nothing about a split at omega.
- **`archive/dev/JOURNAL.md` DECLINED.** Line 1: "# ARCHIVED
  2026-08-20". A retired journal; the facts this task used live in the
  live task directories and the dispatch index.
- **`dev/ARCHIVE.md` DECLINED.** Line 1: "# ARCHIVE.md: the archive
  registry". No module was retired by this task, so the registry was
  not used.
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Line 1: "# ORCHESTRATION:
  the orchestrator's operating rules". No orchestration question arose;
  the program's standing files already bound this dispatch.

## LITERATURE USED

- **`dev/literature/devlin-II5.md` READ AND USED.**
  `dev/literature/devlin-II5.md:502`: "| 5.5-5.6: P(κ) ⊆ L_{κ⁺}, GCH |
  13.20: P^L(ω_α) ⊂ L_{ω_{α+1}}, |L_{ω_{α+1}}| = ℵ_{α+1}
  (`jech13.txt:762-779`) | AGREES |". This is the addendum's basis: the
  textbook proof is one uniform argument indexed by α and does not split
  at ω. This task's measurement agrees with the addendum's reading and
  adds the term that separates THIS bill from that uniform argument:
  the clause `src/L/GCH.lagda.md:64` plus `∈-irrefl ω`.
- **`dev/literature/truncation-and-selection.md` DECLINED.** Line 1:
  "# Truncation and selection: how the two literatures pick a witness".
  No truncation or witness-selection question arises in this task's
  rows; the decomposition consumes both halves as hypotheses and picks
  no witness.
- **`dev/literature/devlin-errata.md` DECLINED.** Line 1: "# Devlin
  errata: documented error classes (do-not-repeat checklist)". No
  textbook proof was built here, so no error class applies.
- **`dev/literature/digest.md` DECLINED.** Line 1: "# Digest: the
  orthodox form of the rud route, pinned from the collected literature".
  No rud-route question arose; the probe prices one decomposition.
- **`dev/literature/terms-2026-08.md` DECLINED.** Line 1: "# The
  terminology dossier: fourteen renderings for the owner's ruling". No
  terminology question arose; this task used the tree's own names.
