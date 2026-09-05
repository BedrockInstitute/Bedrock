# LJ-1.84: is witK satisfiable at all, and if so at what stage?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.84-report.md`.

## 0. THE VERDICT

**`witK` IS REFUTABLE. STOP, per the pre-fixed abort criterion (D-1).**
The machine-checked refutation is in `src/ProbeLJ184A.agda`. `refute`
(`:476`) derives `⊥` from the `witK` type at the canonical
`WitnessAgree` frame, and `stage-refute` (`:535`) instantiates it at
the stage `K = LsetS lam ordλ`, for every ordinal `lam`.

The mechanism: **shapedness does not constrain the arity slot of a
member.** The `shapes` predicate (`src/L/Coding/Shape.lagda.md:
182-188`) reads a member as `pr N (pr (# k) payload)` and puts no
condition on the first component `N`. The closedness clauses
(`src/L/Coding/Model.lagda.md:2191-2202`) name tags 2, 3, 4, 5, 8, 9,
10, 11 only. So any closed and shaped code set can be extended by a
junk member whose arity slot is the stage bound `fst K` itself, with
tag 6 and payload the numeral zero: tag 6 fires no closedness clause,
and its shapedness clause (`unForm 6 zeroPay`, `Shape.lagda.md:104-105,
178-179`) demands only that the payload is zero. The extended set is
still closed and shaped, still contains the formula key, and has rank
at least the rank of `fst K`, so it is not a member of `Lset lam`.

The deciding negative is **MEASURED**: `witK`'s type has no inhabitant
at the stage.

## 1. THE REFUTATION

### 1.1 The witness

At the canonical frame: `A₀` is the carrier, `K₀ = LsetS lam ordλ` is
the bound, `X₀` is the formula key at the x slot, and `D` is a
delivered closed and shaped code set over `A₀` that contains `X₀` (at
the stage, the subformula closure). The probe's `Refute` module
(`src/ProbeLJ184A.agda:89`) takes exactly these data as parameters
plus transitivity and irreflexivity of the bound.

The refuting witness is:

```agda
c₀ = prʟ K₀ (prʟ (numeralL 6) (numeralL 0))   -- :106
w  = cupʟ D (sglʟ c₀)                          -- :110
```

`fst c₀ = pr (fst K₀) (pr (# 6) (fst (numeralL 0)))` (`fstC₀`, `:113`):
a tag-6 constant key whose arity slot is the stage bound itself.

### 1.2 The premise holds for w

- `X₀ ∈ w`: `X∈w` (`:120`), by the delivered `X₀ ∈ D` and the union
  inclusion.
- `closedAt zero` at `w`: `wcl` (`:424`). Each of the eight clauses
  case-splits a member of `w` on `D` or the junk member. A member of
  `D` uses the delivered closedness of `D` (the `hcl` parameter),
  decoded to memberships in `D` and injected into `w`. The junk member
  fires no clause: `binRefute`/`unRefute` (`:178-186`) refute the
  clause-tag shape at the junk member by `pr-inj`, `#-inj′` and
  `6 ≢ k`, where `k` is the clause tag.
- `shapedAt zero (suc zero)` over the carrier `A₀`: `wsh` (`:452`). A
  member of `D` is shaped by the delivered shapedness of `D` (the
  satisfaction of `shapes` never reads the set slot, so the proof
  transfers to the `w` env definitionally). The junk member is shaped
  by `cun6` (`:435`): the `unForm 6 zeroPay` disjunct, with arity
  witness `K₀` and payload witness `numeralL 0`.

The assembled premise is `witnessPremise` (`:472`).

### 1.3 The conclusion fails for w

`w∉K` (`:139`): if `fst w ∈ fst K₀`, then `c₀ ∈ fst K₀` by
transitivity, then `⁅ fst K₀ ⁆s ∈ fst K₀` (the singleton lies in the
junk member's pair), then `fst K₀ ∈ fst K₀` by transitivity again,
refuted by `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`). So `w ∉ Lset
lam` for every ordinal `lam`.

`refute` (`:476`) assembles the two halves. `stage-refute` (`:535`)
instantiates at the stage with the formula `⊤̇` over the empty
alphabet; `stage-refute2` (`:583`) repeats it with the compound
formula `⊤̇ ∧̇ ⊤̇`, confirming the module is generic in the formula.
Both check green at the C-12 cap.

### 1.4 What is measured, what is inferred

- **MEASURED**: the `witK` type at the canonical frame (A slot 0, K
  slot 1, key slot 2, env `A₀ ∷ K₀ ∷ X₀ ∷ []`) is uninhabited, and the
  same type is uninhabited at the stage for every ordinal `lam` (the
  `StageRefute` telescope needs only `IsOrd lam` and `IsOrd α`).
- **INFERRED**: the exact chain frame is refuted identically. No
  master instantiates `WitnessAgree` at a concrete env
  (`_build/lj-1.81-report.md:53-59`), so the chain's exact slots and
  env are unpinned. The transfer is sound because the premise and the
  conclusion read only the set slot, the carrier slot, the key slot
  and the bound slot, and the junk construction uses none of them
  except the bound. This inference sets no verdict; the measured
  canonical frame carries the verdict.

A precision on the stage: at the base 14-frame of `[LJ-1.80]`
(`src/ProbeLJ180A.agda:66-70`, env `A ∷ K ∷ numerals`), every slot
holds a non-key, so the premise is empty and `witK` is vacuously true
there. The chain's `witK` obligation is at the deeper `WitnessAgree`
frame where the formula key occupies the x slot; that is the frame the
refutation targets.

## 2. THE CONDITION THAT WOULD MAKE IT TRUE

**No condition on `K` makes the as-written statement true.** The
refutation needs only transitivity of the bound and irreflexivity of
membership, which every stage and every well-founded set has. The
premise is satisfiable at every rank, so a rank bound on `w` cannot
come from `K`; it must come from the premise.

The repair is the C-38 shape: strengthen the premise. The delivered
code-set predicate already carries the missing conjunct: `isCodeAny A
= arityNumAtL zero ∧̇ hasWitness A`
(`src/L/Coding/CodeSet.lagda.md:247-248`). `arityNumAtL`
(`:185`) pins every member's arity to a numeral of `ωʟ`. The witness
premise of `witK` demands only `closedAt ∧̇ shapedAt`, which is the
second conjunct without the arity pin. The junk member's arity slot is
the stage bound, which is not a numeral, so the arity pin excludes it.

With the arity pin, a sufficient condition is that the stage is
closed under the code-set operation: `AllCodes A ∈ Lset lam`, and
every constructible subset of `AllCodes A` appears below `lam`. This
is a cardinality-type condition, and the tree delivers no such lemma:
`smallDom` (`src/L/Recursion.lagda.md:133-134`) returns the
`boundingOrd` of the key family, which is unrelated to `lam`, and no
delivered lemma bounds the constructible subsets of a stage element.
**INFERRED**: the repair's sufficiency is not machine-checked, and the
missing stage condition is a named absence, not a measured one.

## 3. SUPPLIED AT THE LJ-1.80 STAGE?

**No.** At the stage the chain uses, the as-written `witK` is refutable
(section 1). The statement needs repair before any supply work, and
the repair's remaining obligation is the stage closure condition of
section 2, which the tree does not deliver. **INFERRED** for the exact
unpinned chain frame; **MEASURED** at the canonical frame.

## 4. THE DD4 ANSWER

The defect is in the shared layer. `witK` is a parameter of
`WitnessAgree` (`src/L/Condensation.lagda.md:6227-6229`), and the same
refutable shape is carried downstream by `SatGraphAgree` (`:6509`) and
`LeafAgree` (`:6714`). The J tower would inherit the same parameterized
statement from any reuse of these modules, so it would inherit the
defect. No condition on the J stages makes the as-written statement
true, because the refutation is generic in the bound: it uses only
transitivity and irreflexivity, which every stage has. The junk
construction is the shared content; both towers would pay it at once.
**MEASURED** for the L side; **INFERRED** for the J side, which does
not exist in this tree.

## 5. NEGATIVES AND THEIR STATUS

1. "`witK` is refutable": **MEASURED TRUE**. `Refute.refute`
   (`src/ProbeLJ184A.agda:476`) checks green; `stage-refute` (`:535`)
   and `stage-refute2` (`:583`) check green.
2. "The junk member fires no closedness clause and is shaped":
   **MEASURED TRUE**. `wcl` (`:424`) and `wsh` (`:452`) check green.
3. "The refuting witness is not a member of the stage":
   **MEASURED TRUE**. `w∉K` (`:139`) checks green.
4. "Refutable at every stage": **MEASURED TRUE**. The `StageRefute`
   telescope (`:485`) needs only `IsOrd lam` and `IsOrd α`.
5. "No condition on `K` fixes the as-written statement": **MEASURED**.
   The refutation is parameterized by transitivity and irreflexivity
   of the bound, which every stage has.
6. "The arity-pinned premise plus stage closure would make the
   repaired statement true": **INFERRED**. Not machine-checked; the
   tree delivers no constructible-subset bound.
7. "The exact chain frame is refuted identically": **INFERRED**. No
   master pins the chain's env. Sets no verdict; item 1 carries it.

## 6. ARCHIVE USED

- `_build/lj-1.83-report.md`, read WHOLE. TOOK the blocker location
  (`WitnessAgree`'s `witK`, `:103-115`), the stage value `C = K`
  (`:30-36`), and the process discipline (`:256-266`).
- `src/ProbeLJ183A.agda`, read WHOLE. TOOK the generic `CodeFacts`
  module shape and the transitivity route (`:60-146`).
- `_build/lj-1.77-report.md`, read WHOLE. TOOK the refutation shape and
  the MEASURED/INFERRED discipline.
- `src/ProbeLJ177A.agda`, read WHOLE. TOOK the `∈-irrefl` route
  (`:66-78`) and the import set.
- `_build/lj-1.80-report.md` and `src/ProbeLJ180A.agda`, read WHOLE.
  TOOK the stage values (`K = LsetS lam ordλ`, `A = LsetS α ordα`,
  env `A ∷ K ∷ numerals`), the field-by-field supply, and the repaired
  `arityK` with its extra premise.
- `_build/lj-1.52-report.md`, read WHOLE. TOOK the site class: the
  bound is a constructible set inside the stage, never the hull.
- `src/L/Coding/CodeSet.lagda.md`, read WHOLE. TOOK `AllCodes`, the
  `arityNumAtL` conjunct, and the closed/shaped predicates. Read-only.
- `src/L/Coding/Shape.lagda.md`, read the shapes predicate, the
  `unForm` frames and `closureShaped` (`:100-190`, `:646-649`). TOOK
  the arity-freedom reading that the refutation uses.
- `src/L/Coding/Model.lagda.md`, read the `closedAt` conjunction and
  the clause frames (`:2191-2202`), and the adequacy lemmas used to
  decode clause conclusions.
- `src/L/Coding/Closed.lagda.md` and `src/L/Coding/InL.lagda.md`, read
  WHOLE. TOOK `closureClosed`, `clo`, `key`, `key∈closure`, and the
  `cupʟ`/`sglʟ` membership kit.
- `dev/LESSONS.md`, read C-38 as extended (`:3427-3520`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-30 (`:3332-3380`), WHOLE.
  TOOK the discharge standard: a closure hypothesis over arbitrary
  sets is refuted by regularity unless its premise binds the rank.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 7. LITERATURE USED

Devlin's witness for "v = L_γ" is the level sequence (L_δ | δ ≤ γ),
which is an element of L_α for every γ < α by 2.6(ii); what bounds it
is membership inside the carrier L_α. The witness is a set, the level
sequence, not a stage. Contrast: the formal `witK` premise imposes no
such membership bound, which is exactly the hole the junk member
exploits.

## 8. GATES

- `scripts/check-fences.py --check`: clean, **87 masters**.
- `scripts/lint-prose.py --check` on `src/ProbeLJ184A.agda` and this
  report: exit 0.
- `scripts/lint-agda.py --check src/ProbeLJ184A.agda`: exit 0.
- `src/ProbeLJ184A.agda`: GREEN at the C-12 cap, one process at a
  time. Cold run: 4.75 s wall, 3.85 s user; warm reruns: 0.96 to
  1.89 s wall. Load averages during the runs: 4.91 / 27.21 / 47.36
  then 5.51 / 26.59 / 46.91 (1, 5, 15 minutes), four users. The
  machine was NOT quiet, so every absolute figure carries the caveat.
- Process discipline: one `agda` invocation at a time. The probe is
  gitignored (`src/Probe*.agda`), as is this report (`_build/`).
- Masters: all green or untouched. `git status` is clean; HEAD
  `ce66f72` on `two-tower-bridge`, unchanged.
- No `make check`. No commit, no push.
