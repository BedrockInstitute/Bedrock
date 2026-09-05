# LJ-1.269 report: scout a named-slot layer, and change nothing

Lead with the three things.

## THE CENSUS COUNT

1 hand-written slot permutation and 133 slot pins exist in the active tree.
The count is LARGE. The abort criterion that says "a layer that abstracts three
sites is worse than three functions" does not fire.

## THE SKETCHES

Both sketches typecheck. Sketch A is pure data. Sketch B is an Agda macro.
Both run under `--cubical --safe --guardedness`, the exact OPTIONS header of
every master. `--safe` permits reflection. MEASURED.

## THE DD13 PRICE

Sketch B costs 54 lines to write fresh. Sketch A costs 78. Both delete the 6
hand-written lines of `ρ`. Sketch B needs no coverage proof. Sketch A needs
one per layout. The reflection route is the cheaper of the two.

---

## 1. The census

### 1.1 Permutations

A permutation is `Fin n → Fin m` written by clause. The active tree has 1.

- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-112`: `ρ : Fin 16 → Fin 16`.
  Five clauses. Its specification lives in a comment (`v → 14`, `γ → 15`,
  `K → 1`, `δᵢ → 2 + i`).

The frozen archive has 1 more.

- `archive/src/2026-08-09-rud-route/L/Rud/StepStory.lagda.md:143`:
  `emb : (n : ℕ) → Fin 3 → Fin (3+n)`, three clauses, used at `:149` through
  `renameFo (emb n) bigOr`.

### 1.2 Pins

A pin is a conjunct or a field that asserts `lookup i γ ≡ numeralL k` with a
hand-written position. The active tree has 133. They split as follows.

`src/` masters, 88 pins:

- `src/L/Condensation/LowerAgree.lagda.md:99-104` and `:135-136`: 8.
  `tagEq0..5` plus `t0eq`, `t1eq`. Record `LFacts`.
- `src/L/Condensation/UpperAgree.lagda.md:96-101` and `:135-136`: 8.
  `tagEq6..11` plus `t0eq`, `t1eq`. Record `UFacts`.
- `src/L/Condensation/TwelveAgree.lagda.md:133-144` and `:181-182`: 14.
  `tagEq0..11` plus `t0eq`, `t1eq`. Record `TFacts`.
- `src/L/Condensation.lagda.md`: 58. The same `tagEq`/`t0eq`/`t1eq` written
  once per constructor row. The pin `fst (lookup (suc×k N) γ) ≡ fst (numeralL j)`
  appears at shift depths 0, 1, 3, 4, 5 and 6. Sites include `:2535`, `:2616`,
  `:2775`, `:3064`, `:3067`, `:3283`, `:3535`, `:3590`, `:3664`, `:3737`,
  `:3850`, `:3962`, `:4144`, `:4212-4213`, `:4410`, `:4428-4429`, `:4800-4801`,
  `:5010`, `:5057-5058`, `:5139`, `:5186-5187`, `:5267`, `:5368`, `:5386-5387`,
  `:5480`, `:5551`, `:5650`, `:5709-5710`, `:5737-5738`, `:5767-5768`, `:5813`,
  `:5825`, `:5915`, `:6079-6090`, `:6290`, `:6340`, `:6671`, `:6700`.

Active probes, 45 pins:

- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:126-137`: 12. The `numAt` conjuncts.
- `agents/tasks/LJ-1-102/ProbeLJ1102A.agda:316`, `:329`, `:330`: 3.
- `agents/tasks/LJ-1-158/ProbeLJ1158T1.agda:55-66` and `:101-102`: 14.
- `agents/tasks/LJ-1-158/ProbeLJ1158L1.agda:56-61` and `:90-91`: 8.
- `agents/tasks/LJ-1-158/ProbeLJ1158L2.agda:57-62` and `:91-92`: 8.

### 1.3 Slot placements, a third shape

The narrow census counts permutations and pins. A third shape exists and it is
the same disease. The 28 LevelHood parameters are placed by hand-written
`inject+ {n} {m} (fin-suc k)` arguments.

- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:86-98`: 28 placements.
- `agents/tasks/LJ-1-241/ProbeLJ1241B.agda:53-69`: 28 placements.

This adds 56 hand-written slot positions. The total of hand-written slot
arithmetic is 1 permutation plus 133 pins plus 56 placements, which is 190
sites.

### 1.4 The four-names symptom, located

Commit `c8a628b` says the same field arrives under four local names. The
census locates it. In `src/L/Condensation.lagda.md` the tag slot is written
with shift depth 0, 1, 3, 4, 5 and 6. The record fields in `*Agree` write depth 6.
The same slot appears under four or more local spellings. This is the symptom.
It is not a metaphor. MEASURED.

### 1.5 What the generic helpers are NOT

The tree has many `Fin n → Fin m` functions. `sh2`, `sh3`, `sh4`, `sh6` in
`src/L/Choice/*` and `src/L/Hierarchy.lagda.md:82` shift every slot by a
constant. `padLeft`, `padRight`, `inject+`, `fin-suc`, `joinFin`, `splitFin`,
`liftρ` are generic plumbing. These are not slot layouts. They name no slot.
They do not count in the census.

---

## 2. Sketch A: the named-slot layer, pure data

The file is `agents/tasks/LJ-1-269/ProbeLJ1269A.agda`. It typechecks. Exit 0.
78 non-blank lines.

The sketch has four parts.

1. Slot names. `w`, `v`, `γ`, `K` and `δ i` are ℕ codes. This is a choice.
   Decidable equality on a multi-constructor `data Slot` is not free in
   cubical. `λ ()` does not refute `w ≡ v`, because `_≡_` is Path. The sketch
   uses ℕ codes, where `discreteℕ` supplies equality for free.
2. The layout as data. `tgt : Vec ℕ 16` lists the slots in target order.
   `src : Vec ℕ 16` lists them in source order.
3. The derived position. `find : (s : ℕ) → Vec ℕ n → Fin (suc n)` scans the
   layout. `strengthen` removes the sentinel. `covers` proves the sentinel is
   never hit. `covers` is 16 refutation clauses. This is the coverage proof.
4. The permutation. `ρ i = strengthen (find (lookup i src) tgt) (covers i)`.
   Correctness checks `check0` through `check4` all close by `refl`.

Sketch A typechecks. The term that would have stopped it is the coverage
proof. It did not stop it, but it is the cost. MEASURED.

---

## 3. Sketch B: the Agda macro

The file is `agents/tasks/LJ-1-269/ProbeLJ1269B.agda`. It typechecks. Exit 0.
54 non-blank lines.

The sketch has three parts.

1. The declarative layout. `layout : List ℕ` lists the 16 target positions in
   source order, one line.
2. The macro. `perm : List ℕ → Term → TC ⊤` builds the term
   `λ i → lookup i table` where `table` is a `Vec (Fin 16) 16` built from the
   layout. It uses `Agda.Builtin.Reflection`.
3. The use. `ρ : Fin 16 → Fin 16` and `ρ = perm layout`. Correctness checks
   `check0` through `check4` and `check15` all close by `refl`.

`--safe` permits reflection. The minimal file
`agents/tasks/LJ-1-269/ProbeLJ1269ReflSafe.agda` proves it. A macro under
`--cubical --safe --guardedness` typechecks and runs. MEASURED.

The macro receives its concrete arguments as values. The file
`agents/tasks/LJ-1-269/ProbeLJ1269MacroArgs.agda` proves it. The macro
pattern-matches the layout value and computes. MEASURED.

Sketch B needs no coverage proof. The macro computes the permutation at
elaboration time. Agda then checks the result. The specification stops living
in a comment. It lives in `layout`.

---

## 4. The DD13 price

Price the ideal form written fresh today. Then compare.

### 4.1 The layer's own lines

- Sketch B, the macro: 54 non-blank lines. The reusable part is the macro and
  its helpers, about 20 lines. The layout is one line. The rest is checks.
- Sketch A, the pure data: 78 non-blank lines. The reusable part is `find`,
  `strengthen` and `covers`, about 40 lines. The coverage proof is 16 of
  those.

### 4.2 What each deletes

The hand-written permutation `ρ : Fin 16 → Fin 16` is 6 lines, one type and
five clauses. Both sketches replace it with one layout line and one use line.

The 133 pins and 56 placements are the bigger mass. Neither sketch generates
pins as written. Both give the position function. A pin site changes from
`fst (lookup (suc (suc (suc (suc (suc (suc N0)))))) γ) ≡ fst (numeralL 0)`
to `fst (lookup (pos (δ 0)) γ) ≡ fst (numeralL 0)`. The hand-written shift
depth moves into the layout data, one place.

### 4.3 The comparison

For the one permutation, the layer costs more than it deletes. 54 lines
against 6. But the census is not one site. It is 190 sites. The layer pays
when the layout is shared. A layout change then edits one place, not four
shift depths.

The decisive fact is Sketch A against Sketch B. Sketch A needs a coverage
proof per layout. The proof is the same work as the hand-written permutation.
Sketch B needs none. The reflection route is strictly cheaper and removes the
comment. DD13 says the reflection route is the ideal form.

---

## 5. Dates, commits and staleness

Every figure was taken at commit `414249b139513b969576ffe48b788c036d12f1d5`,
2026-08-15 08:39:12 +0800. The HEAD when I read the files. The census files
have no diff to the current HEAD `33a9b36`. MEASURED.

- The census count, 1 permutation and 133 pins. Stale when a landing adds or
  removes a hand-written slot site. `[LJ-1.266]` is live and will add sites.
- The sketch results. Stale when the Agda version or the cubical library
  version changes, or when the OPTIONS header changes.
- The line counts. Stale when either sketch file is edited.

The load for every Agda run was `GHCRTS="-A64m -I0 -M8g"`. One process at a
time. No heap exhaustion. MEASURED.

---

## 6. DD4

The slot layout is pure syntax over `Fin` and ℕ. It names no tower. So the
layer is tower-neutral by construction.

The census sites span both sides of the axis. The `*Agree` records and
`Condensation.lagda.md` sit in the internalization wing, the Def-against-J
side. `ProbeLJ1241A` builds `φ₀` from `LevelHood`, the L-against-ambient side.
The frozen archive writes the same shape in its `StepStory`. So the disease is
not tied to one tower.

The axis is `[LJ-1.262]`'s: Devlin's Def-against-J against the port's
L-against-ambient. No figure in this task says which side the phase is on. The
slot layer does not need that answer. It is shared by construction.

The same shape under four names is a DD4 fact. One shared layer removes four
spellings. That is the argument for the layer, and it has nothing to do with
seconds.

---

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Rud/StepStory.lagda.md:143`. Read.
  Took: the retired route hand-wrote `emb : Fin 3 → Fin (3+n)` clause by
  clause and pushed it through `renameFo`. It had nothing better.
- `archive/dev/TASKS-archived.md:69`. Read. Took: the retired route's task
  rows name no slot-abstraction layer. It re-typed `DefInJ` and `SatTable` by
  hand.
- `agents/tasks/LJ-1-173/lj-1.173-report.md:14-17`. Read. Took: the four-names
  episode is in commit `c8a628b`, not the report body. The report records the
  21 false fields. The commit message records the patch-by-shape cure.

## LITERATURE USED

The literature does not bear on slot layout. Slot layout is host-language
syntax over `Fin n`. No digested mathematics names it. One line, honest.

---

## Classification of negatives

- Agda reflection has no precedent in `src/`. MEASURED. The grep for
  `Agda.Builtin.Reflection` returns zero. The word "reflection" in `src/`
  names the mathematical reflection principle, `L.Reflect` and `L.ReflectFo`.
- `--safe` does not block reflection. MEASURED. The minimal probe typechecks.
- Sketch A needs a coverage proof. MEASURED. The 16 clauses of `covers` are in
  the file.
- Sketch B needs no coverage proof. MEASURED. The macro file has none.
- The retired route had no better layer. MEASURED. `StepStory.lagda.md:143`
  hand-writes the same shape.

No negative in this report is INFERRED.
