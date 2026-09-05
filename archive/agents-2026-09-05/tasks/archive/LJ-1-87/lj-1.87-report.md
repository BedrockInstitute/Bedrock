# LJ-1.87: does witK follow from the frame hypothesis plus w ⊆ AllCodes A?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.87-report.md`.

## 0. THE VERDICT

**`witK` does NOT follow from the two premises. The abort criterion's
second branch fires: STOP, and here is the term that could not be
written. This is a fourth statement-level defect, and it outranks
everything else.**

The two premises are

1. `w ⊆ AllCodes A` (`[LJ-1.85]`), and
2. `⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩` (the frame hypothesis,
   `[LJ-1.86]`).

They bound the **members** of `w`, never `w` itself. The conclusion
`fst w ∈ Lset lam` needs `w` to be a **definable** subset of some stage
below `lam`. The premises give `w ⊆ Lset δ` for a `δ ∈ lam`; they do not
give `w ∈ 𝒟ₒ (Lset δ)`. In this hierarchy the gap is real: the stages
are the *definable* power set, and a subset of a stage element need not
appear one level up. The power axiom chapter says it in so many words:
"Condensation is not part of this. It is the sharper statement that a
subset of a stage appears at a stage bounded in terms of that stage
rather than in terms of the subsets themselves, and it is what a
cardinal arithmetic would want. The axiom does not."
(`src/L/Axioms/Power.lagda.md:18-20`), and "the axiom asks for the
constructible subsets to form a set, not for them to appear early"
(`:210-214`).

The measured evidence, in one paragraph:

- The attempted proof, `src/ProbeLJ187B.agda:102-132`, is RED exactly
  at the missing step: the only assembly route is `Lset-in` at the
  `δ ∈ lam` with `w ∈ 𝒟ₒ (Lset δ)`, and the natural term claiming
  `w ≡ defSet (Lset δ) ⊤̇` is rejected with `UnequalTerms`
  (`defSet (Lset δ) ⊤̇ != fst w`), `src/ProbeLJ187B.agda:132.50-54`,
  1.82 s wall.
- The honest content of the two premises is machine-checked GREEN in
  `src/ProbeLJ187A.agda`: the frame hypothesis decomposes to
  `AllCodes A ⊆ Lset δ` with `δ ∈ lam` (`:58-70`), and the two premises
  give `w ⊆ Lset lam` (`:75-82`), member by member. 1.72 s wall.
- A search over `src/` for a "subset of a stage element is a stage
  element" lemma returns zero hits. The only introductions into a stage
  are `Lset-in` (needs `𝒟ₒ`) and its `𝒟ₒ`-based corollaries, so any
  proof of the conclusion must produce a definability witness for `w`
  below `lam`. The premises cannot.

The mathematical reason, **INFERRED** and therefore not a verdict by
itself: at a countable limit `lam`, take a constructible
`T ⊆ ω` whose first appearance is at or above `lam`, and let
`w_T = D ∪ {c_n : n ∈ T}` where `c_n` is the key of `⊤̇` at arity `n`
and `D` is the subformula closure. Then `w_T` is closed, shaped,
contains the formula key, lies in `AllCodes A`, and is not a member of
`Lset lam`. So the repaired universal `witK` is false in general, not
merely unproved. The measured red control carries the verdict.

## 1. THE FRAME HYPOTHESIS AND THE REPAIRED witK

The frame hypothesis is stated at the canonical frame of `[LJ-1.84]`
(carrier `A₀ = LsetS α`, bound `K₀ = LsetS lam`, env
`A₀ ∷ K₀ ∷ X₀ ∷ []`) as the third argument of `witK-repaired`,
`src/ProbeLJ187B.agda:102-107`:

```agda
witK-repaired : (w : Sʟ)
  → ⟨ (w ∷ γ₀) ⊨ ((var (suc (suc (suc zero))) ∈̇ var zero)
       ∧̇ (closedAt zero ∧̇ shapedAt zero (suc zero))) ⟩
  → ((z : V ℓ) → ⟨ z ∈ˢ fst w ⟩ → ⟨ z ∈ˢ fst (AllCodes A₀) ⟩)
  → ⟨ fst (AllCodes A₀) ∈ˢ Lset lam ⟩
  → ⟨ fst w ∈ˢ Lset lam ⟩
```

The term could not be written. The proof body,
`src/ProbeLJ187B.agda:108-132`, runs the two premises to
`AllCodes A₀ ⊆ Lset δ` with `δ ∈ lam` (`Lset-out` plus `𝒟ₒ∋⊆`) and then
to `w ⊆ Lset δ`; the last step needs

```agda
w∈𝒟ₒδ : ((z : V ℓ) → ⟨ z ∈ˢ fst w ⟩ → ⟨ z ∈ˢ Lset δ ⟩)
      → ⟨ fst w ∈ˢ 𝒟ₒ (Lset δ) ⟩
```

at `src/ProbeLJ187B.agda:130`, and its body at `:132` is rejected.
That is the term that could not be written, per C-36: the type error
says the types differ (definability is not subset-membership), and the
missing conjunct is exactly "`w` is definable below `lam`", which no
premise supplies.

## 2. THE SUPPLIER

There is no supplier for the frame hypothesis **as a witK repair**,
because the repaired universal `witK` is false (section 0). The frame
hypothesis bounds the code set; it does not bound the arbitrary closed
shaped subsets of the code set. What would make the conclusion true is
a condensation-type hypothesis, "every constructible subset of
`AllCodes A` appears below `lam`", which the power axiom chapter names
as exactly what is **not** part of the delivered theory
(`src/L/Axioms/Power.lagda.md:18-20`, `:210-214`).

The consumer that would have to supply it does not exist. The frame
that would carry the hypothesis, `BoundedSubsetAt`
(`src/L/BoundedSubset.lagda.md:1396-1401`), has zero instantiations
outside `BoundedSubset.lagda.md`; `UnionKit` (`:1144-1146`) and
`HullStage` (`:902-904`) have zero instantiations as well. The tower's
own hypothesis of the same class, `x∈Lλ`
(`src/L/BoundedSubset.lagda.md:1146`, `:1402`), is likewise supplied by
nobody: the chain is not placed. This matches `[LJ-1.86]`.

The delivered tree could not supply the corrected hypothesis. The
nearest measured comparable is `[LJ-1.86]`'s existence probe,
`AllCodes-stage` (`src/ProbeLJ186A.agda:43-45`), 1.93 s warm at load
4.90 / 5.14 / 6.88. That probe prices the wrong half: it proves that
**some** stage contains `AllCodes A`, not that the frame's fixed `lam`
does. No delivered term compares the code set's stage with the frame's
`lam`; per D-8, an expected figure anchored on a comparable elsewhere
is a hypothesis, not a price. So the one best-effort figure for the
below-lam supply is: **none exists in the delivered tree**, with that
basis. The supplier would have to be the tower's rank machinery at an
instantiation of `BoundedSubsetAt`, and no such instantiation exists.

The repair direction, for the record and not carried further per D-1:
the consumer's actual witness is the subformula closure, which is
finite. A finite set of members of `Lset δ` is a definable subset of
`Lset δ` by the delivered `finSet∈𝒟ₒ`
(`src/L/Axioms/Basic.lagda.md:354`), so the closure lies in
`Lset (sucV δ) ⊆ Lset lam`. The universal form is the defect; the
witness-bound form is the cure. This paragraph is **INFERRED**, not
machine-checked.

## 3. STAGED, NOT DISCHARGED

**With no instantiation, `witK` repaired is staged, not discharged, and
C-35 applies.** In fact the failure is worse than staged: the repaired
universal statement is false, so it is not a true statement awaiting a
consumer but a statement-level defect. C-35's test has its answer:
asking what would be false if the repaired `witK` were wrong, the
answer is "everything downstream that consumes it" and nothing upstream
catches it, because no instantiation exists to catch it.

## 4. NEGATIVES AND THEIR STATUS

1. "The two premises prove the repaired universal `witK`":
   **MEASURED FALSE**. The attempted term is RED at
   `src/ProbeLJ187B.agda:132.50-54` (1.82 s wall); the only structural
   route to `fst w ∈ Lset lam` is a definability witness `w ∈ 𝒟ₒ`
   below `lam`, and a search over `src/` for a subset-to-stage bridge
   returns zero hits. The power axiom chapter disclaims the bridge in
   words (`src/L/Axioms/Power.lagda.md:18-20`, `:210-214`).
2. "The two premises bound the members of `w`":
   **MEASURED TRUE**. `w⊆Lλ` (`src/ProbeLJ187A.agda:75-82`) checks
   GREEN; the frame hypothesis decomposes to `AllCodes A ⊆ Lset δ`
   (`:58-70`), GREEN. 1.72 s wall.
3. "The repaired universal `witK` is mathematically true at every
   admissible frame": **INFERRED FALSE**. The `T ⊆ ω` construction of
   section 0 is argued, not machine-checked. It sets no verdict by
   itself; item 1 carries the verdict.
4. "Some consumer supplies the frame hypothesis at a concrete frame":
   **MEASURED FALSE** by search. `BoundedSubsetAt`, `UnionKit` and
   `HullStage` have zero hits outside `src/L/BoundedSubset.lagda.md`.
5. "The delivered tree prices the below-lam supply":
   **MEASURED FALSE**. The only measured comparable
   (`src/ProbeLJ186A.agda:43-45`, 1.93 s) prices existence of a stage,
   not the below-lam bound; no term compares the code set's stage with
   the frame's `lam`.

## 5. THE DD4 ANSWER

The frame hypothesis is generic in SHAPE and per-tower in CONTENT, and
the failure found here is in the shared shape. The shape "the tower's
code set over the carrier is an element of the frame's stage" is the
same sentence both towers would write at their frames, and the defect
"the code set's stage bounds the members of `w`, never `w` itself" is a
defect of that shared shape: a J tower carrying the same hypothesis
would carry the same false statement (D-29). The per-site content is
the code set (L side: `src/L/Coding/CodeSet.lagda.md:434-441`) and the
stage certificate (L side: `src/L/Axioms/Basic.lagda.md:98`,
`src/L/Axioms/Separation.lagda.md:198-199`, `:293-294`); the J tower
supplies its own. The repair direction is shared in shape too: pin the
boundedness at the witness (the closure), not at all subsets of the
code set. The J side is **INFERRED**: no J tower exists in this tree.

## 6. GATES

- `src/ProbeLJ187A.agda`: GREEN at the C-12 cap, one process. 1.72 s
  wall (warm dependencies). Load average at run: 4.91 / 4.17 / 5.05,
  four users, the machine was NOT quiet.
- `src/ProbeLJ187B.agda`: RED as intended at `:132.50-54`, 1.82 s
  wall, same load window. `UnequalTerms`: `defSet (Lset δ) ⊤̇ != fst w`.
- One `agda` process at a time; both runs returned; none needed
  killing. No process was left alive.
- `scripts/check-fences.py --check`: clean, **87 masters**, run
  threshold 3.
- `scripts/lint-prose.py --check` on both probes and this report:
  exit 0.
- `scripts/lint-agda.py --check` on both probes: exit 0.
- Masters: none touched. `git status` is clean; HEAD `8af8206` on
  `two-tower-bridge`, unchanged. The probes are ignored by
  `.gitignore:22` (`src/Probe*.agda`); this report by `.gitignore:2`
  (`_build/`). No `make check`. No commit, no push.
- DD23: no mathematical prose was written or changed.

## 7. ARCHIVE USED

- `_build/lj-1.86-report.md`, read WHOLE. TOOK the frame walk
  (`lam` a module parameter at `src/L/BoundedSubset.lagda.md:902-904`,
  `:1144-1146`, `:1396-1401`), the existence probe
  (`src/ProbeLJ186A.agda:43-45`, 1.93 s), and the equivalence reading
  "`stage (fst (AllCodes A)) ... ∈ lam`, by `Lset-mono`".
- `src/ProbeLJ186A.agda`, read WHOLE. TOOK the imports and the
  `AllCodes-stage` term.
- `_build/lj-1.85-report.md`, read WHOLE. TOOK the premise
  `w ⊆ AllCodes A`, its supply at the closure
  (`src/ProbeLJ185B.agda:58-68`), and the knife-edge `α+ω`
  counterexample (INFERRED).
- `src/ProbeLJ185B.agda` and `src/ProbeLJ185C.agda`, read WHOLE. TOOK
  the closure-inclusion proof shape and the red-control convention.
- `_build/lj-1.84-report.md` and `src/ProbeLJ184A.agda`, read WHOLE.
  TOOK the canonical frame (`A₀ ∷ K₀ ∷ X₀ ∷ []`), the closedness
  clause reading (eight clauses, tags 2, 3, 4, 5, 8, 9, 10, 11), and
  the `StageRefute` telescope.
- `src/L/BoundedSubset.lagda.md`, read the mandated frames
  (`:900-960`, `:1140-1160`, `:1390-1410`). TOOK the universal-parameter
  reading of `lam` and the `x∈Lλ` hypothesis class (`:1146`, `:1402`).
- `src/L/Condensation.lagda.md`, read the `WitnessAgree` frame
  (`:6224-6249`). TOOK `witK` as a parameter and the transfer `go`.
- `src/L/Axioms/Power.lagda.md`, read the opening and the closing prose
  (`:1-27`, `:205-216`). TOOK the condensation disclaimer, the decisive
  negative for this dispatch.
- `src/L/Constructible.lagda.md`, read `Lset-in/out/mono`, `𝒟ₒ∋⊆`
  and `𝒮ʟ = 𝒮ᵥ ↾ isL` (`:300-411`). TOOK the only-introduction reading
  of stage membership.
- `src/L/Ordinal/Stages.lagda.md`, read the rank opening and the
  ordinal-stage lemmas (`:10-30`, `:120-180`, `:430-465`). TOOK the
  definable-subset reading of a stage member.
- `src/L/Coding/Model.lagda.md` and `src/L/Coding/Shape.lagda.md`,
  read the clause and shape frames (`:2160-2210`, `:95-200`). TOOK the
  downward-closed reading of `closedAt`.
- `src/L/Choice/Step.lagda.md`, read `theCarve` (`:95-130`). TOOK the
  "a set enters the tower only by being carved" reading.
- `src/L/Choice/Internal.lagda.md` and `src/L/Choice/Adequate.lagda.md`,
  read the `AllCodes` usage (`:185-220`, `:300-405`). TOOK the finding
  that the choice chain pins `AllCodes` at slots but never supplies a
  stage bound.
- `src/L/Axioms/Basic.lagda.md`, read `finSet∈𝒟ₒ` (`:354`) and the
  separation certificate lines. TOOK the finite-set definability fact
  for the repair direction.
- `src/L/Stage.lagda.md`, read `stage`, `stage-ord`, `stage-mem`
  (`:175-190`). TOOK the earliest-stage function.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3241`), C-36 (`:3284-3331`), D-8 (`:1377-1418`), D-30
  (`:3332-3380`), read WHOLE. TOOK the discharge standard, the
  untested-block test, and the write-the-unwritable-term discipline.
- `archive/rud-route/`, SHAPE only. Read the README and the file list;
  took nothing.

## 8. LITERATURE USED

- Banked per DD18: `[LJ-1.86]` answered how Devlin gets his bound
  (he chooses a limit `λ` with `x ∈ L_λ` after `x` is known). This
  dispatch spent nothing on it.
