# LJ-1.88: is the witness step circular, or does the theorem's own
# hypothesis supply it?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.88-report.md`.

## 0. THE VERDICT

**The witness step is NOT circular. `w`'s appearance follows from `x`'s,
by the finite-family route, and the route is NOT condensation. The first
abort branch fires: the route exists, the decisive step is machine-checked,
and the remaining work is wiring, not a redesign.**

The witness `w` that `hasWitnessAt` produces is the subformula closure
`clo ι ιL φ` (`src/L/Coding/CodeSet.lagda.md:369`), a finite union of
singletons of keys (`src/L/Coding/InL.lagda.md:258-270`). Its appearance in
`Lset lam` follows from a stage-fact for the code set, in three measured
steps:

1. `w ⊆ AllCodes A`, machine-checked (`clo⊆All`,
   `src/ProbeLJ185B.agda:58-68`, GREEN, 1.09 s wall).
2. `AllCodes A` has a stage: `AllCodes A ∈ Lset δ₀`
   (`src/ProbeLJ186A.agda:43-45`, GREEN, 1.61 s wall).
3. The decisive step, machine-checked in this dispatch: a finite family of
   members of a stage is a definable subset of that stage
   (`finSet∈𝒟ₒ`, `src/L/Axioms/Basic.lagda.md:352-354`), and the successor
   stage is exactly the definable power set
   (`Lset-suc`, `src/L/Axioms/Basic.lagda.md:196`). Hence the family appears
   one level up: `finSet-stage` (`src/ProbeLJ188A.agda:56-61`), GREEN,
   1.72 s wall at load 2.89 / 4.24 / 4.80.

Steps 1 and 2 decompose to `w ⊆ Lset δ₁` for `δ₁ ∈ δ₀` (`Lset-out`,
`src/L/Constructible.lagda.md:336-337`; `𝒟ₒ∋⊆`, `:313`). Step 3 then gives
`w ∈ Lset (sucV δ₁)`. With `lam` a limit (`succλ`,
`src/L/BoundedSubset.lagda.md:1401`) and `δ₁ ∈ lam`, `Lset-mono`
(`src/L/Constructible.lagda.md:355-356`) gives `w ∈ Lset lam`.

What the route needs as input is the stage-fact `AllCodes A ∈ Lset lam`,
the stage condition `[LJ-1.86]` and `[LJ-1.87]` named as missing. It is the
same hypothesis class as the frame's own `x∈Lλ`
(`src/L/BoundedSubset.lagda.md:1402`). It is NOT condensation: the power
axiom chapter's disclaimer (`src/L/Axioms/Power.lagda.md:209-214`) says the
axiom asks for the constructible subsets to form a set, not to appear
early. The closure is FINITE, so it is definable over the stage of its own
members, and the climb is a fixed finite number of successor steps inside
the limit. Nothing in the route uses the theorem's conclusion
`x ∈ Lset κ` (`src/L/BoundedSubset.lagda.md:1621`), so nothing is circular.

The honest caveat, in one sentence: the theorem's own hypothesis gives a
stage-fact for the theorem's `x` (`x∈Lλ`), and the closure route's input is
a stage-fact for the code set (or for the formula keys); these are the same
CLASS of hypothesis, and the concrete stage-facts are wiring obligations of
the instantiation, which does not exist in the tree.

## 1. THE FRAME (question 1)

The frame carries BOTH `x ⊆ Lset α` and a stage for `x`. At
`BoundedSubsetAt` (`src/L/BoundedSubset.lagda.md:1396-1402`):

- `(x⊆Lα : (z : S) → ⟨ z ∈ˢ x ⟩ → ⟨ z ∈ˢ Lset α ⟩)`, `:1399`: `x` is a
  subset of the stage `Lset α`.
- `(x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)`, `:1402`: `x` appears at the stage
  `Lset lam`.

`lam` is a limit ordinal: `ordλ` at `:1400`, `α∈λ` at `:1400`, and
`succλ : (d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩` at `:1401`. `UnionKit`
carries the same two hypotheses (`:1144-1146`), and `HullStage` carries the
limit admissibility (`:902-904`). The theorem is `⟨ x ∈ˢ Lset κ ⟩`
(`:1621-1622`). This is **MEASURED by reading**.

## 2. THE ROUTE (question 2)

Yes, the route reaches `w`. The mechanism is finiteness, and the route is
at `file:line` as follows.

The witness. `witnessAt-in` produces `clo ι ιL φ` as the witness of
`hasWitnessAt A x`, where `x` is the key of `φ`
(`src/L/Coding/CodeSet.lagda.md:365-373`, witness at `:369`). The closure
is built by recursion: a finite union of singletons of keys
(`src/L/Coding/InL.lagda.md:258-270`).

Step A, members in the code set. Every member of the closure is a key of a
formula over the carrier (`closure-inv`,
`src/L/Coding/InL.lagda.md:445-457`), and every such key lies in
`AllCodes A` (`key∈AllCodes`, `src/L/Coding/CodeSet.lagda.md:443-444`). The
composition `clo⊆All` is machine-checked
(`src/ProbeLJ185B.agda:58-68`), GREEN.

Step B, the code set has a stage. `AllCodes A` is built by separation, so
its carrier element carries an `isL` certificate, and `stage` names the
containing ordinal: `AllCodes A ∈ Lset δ₀`
(`src/ProbeLJ186A.agda:43-45`), GREEN. `Lset-out` decomposes this to
`AllCodes A ∈ 𝒟ₒ (Lset δ₁)` with `δ₁ ∈ δ₀`
(`src/L/Constructible.lagda.md:336-337`), and `𝒟ₒ∋⊆` gives
`AllCodes A ⊆ Lset δ₁` (`:313`). With `w ⊆ AllCodes A`, every member of `w`
is a member of `Lset δ₁`.

Step C, the decisive step. `w` is a finite family of members of `Lset δ₁`.
`finSet∈𝒟ₒ` says a finite family drawn from a stage spans a definable
subset of that stage (`src/L/Axioms/Basic.lagda.md:352-354`), and `Lset-suc`
says the successor stage is exactly the definable power set (`:196`). The
composition is `finSet-stage` (`src/ProbeLJ188A.agda:56-61`), machine-
checked GREEN. Hence `w ∈ Lset (sucV δ₁)`.

Step D, the climb. With `δ₁ ∈ lam` and `succλ`, `sucV δ₁ ∈ lam`, and
`Lset-mono` (`src/L/Constructible.lagda.md:355-356`) gives
`w ∈ Lset lam`.

One correction to the brief's framing, **MEASURED by reading**: the closure
is NOT built by separation over `AllCodes A`. It is built by recursion
(singletons and unions, `src/L/Coding/InL.lagda.md:258-270`) and then shown
to be a subset of `AllCodes A`. The route does not need separation over
`AllCodes A`: finiteness supplies definability over the stage, and
`finSet∈𝒟ₒ` is the mechanism.

The alternative route from the key directly is also available, but it is
**INFERRED** at one point. From `x = key φ ∈ Lset δ`, the subformula codes
lie in `Lset δ` by transitivity of the stage and the nested-pair structure
of the code; the subformula keys climb with `pr∈Lset-suc`
(`src/L/Axioms/Basic.lagda.md:598-599`); the closure is a finite family of
those keys. The code-member facts are not a named delivered lemma, so this
half is argued, not machine-checked. The `AllCodes` route above avoids the
unchecked half and is the measured one.

## 3. WHAT REPLACES witK (question 3)

The universal `witK` (`src/L/Condensation.lagda.md:6227-6229`) is false in
general: the repaired universal form has no inhabitant at the knife-edge
stage, measured by the red control (`src/ProbeLJ187B.agda:132.50-54`). It
is replaced by a per-witness construction at the witness's birth site:

```agda
closure-stage : (σ : V ℓ) (oσ : IsOrd σ) (A : Sʟ)
              → ⟨ fst (AllCodes A) ∈ˢ Lset σ ⟩
              → {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
              → ⟨ fst (clo ι ιL φ) ∈ˢ Lset (sucV σ) ⟩
```

The body is the composition of section 2: `clo⊆All` for `w ⊆ AllCodes A`,
`Lset-out` plus `𝒟ₒ∋⊆` for `AllCodes A ⊆ Lset δ` with `δ ∈ σ`, the
closure-as-finite-enumeration identity (by recursion on `φ`), and
`finSet-stage`. Two pieces of the body are wiring, not mathematics: the
identity `closure φ ≡ finSet (number of subformulas) (keys of subformulas)`,
and the fiber enumeration `g : Fin m → ⟪ Lset δ ⟫`. Both are mechanical
recursions over the formula shape; neither is delivered in the tree.

At the transfer, `WitnessAgree.out`'s `witK` argument
(`src/L/Condensation.lagda.md:6247-6249`) is supplied for the produced
witness instead of being a universal hypothesis. The frame's obligation is
the stage-fact `AllCodes A ∈ Lset lam`, which `[LJ-1.86]` and `[LJ-1.87]`
already identified as the missing premise of the same class as `x∈Lλ`.

## 4. WHAT IS MISSING (question 4)

Since the route exists, this section states the caveat precisely. What `w`
needs that the frame does not yet carry is one stage-fact: the code set
below the frame's stage, `AllCodes A ∈ Lset lam` (equivalently
`stage (fst (AllCodes A)) ((AllCodes A) .snd) ∈ lam`, by `Lset-mono`).
It is NOT condensation. It is a hypothesis of the same class as the frame's
own `x∈Lλ` (`src/L/BoundedSubset.lagda.md:1402`), and no delivered term
relates Devlin's `x` to `AllCodes A`'s stage: the frame's `x∈Lλ` is about
`x`, not about the code set, **MEASURED by reading**. The universal form's
failure is irrelevant to the produced witness: the closure route works from
the code set's stage-fact, and the closure needs no condensation because it
is finite.

## 5. HOW DEVLIN BOUNDS HIS WITNESS

Three lines. Devlin's witness for "v = L_γ" is the level sequence
`(L_δ | δ ≤ γ)`. By 2.6(ii), the sequence is an element of `L_α` for every
`γ < α`: the witness lands INSIDE the carrier stage
(`_build/literature/dev2.txt:1191-1194`). The Σ₀ matrix's bound `K(u)`,
the finite-sequence set over the formula set, also lies inside the carrier
(`dev2.txt:593-630`). No condensation enters at that step.

Is that route available here? Yes, with a different mechanism. Devlin's
sequence is infinite and lives in the carrier by the level-recursion
theorem; the tree's witness is the subformula closure, which is FINITE, and
the finite-family principle (`finSet∈𝒟ₒ` plus `Lset-suc`) lands it one
level up from the stage of its members, measured by `finSet-stage`
(`src/ProbeLJ188A.agda:56-61`). Both avoid condensation. The tree's route
is simpler: finiteness instead of the level-sequence recursion.

## 6. THE DD4 ANSWER

The route is generic in SHAPE and per-tower in CONTENT. The shared shape is
the whole section 2 template: "the witness is a finite set of code-set
members; a finite family drawn from a stage is a definable subset of that
stage; the successor stage is the definable power set; hence the witness
appears one level up, and a limit stage with room absorbs the climb". A J
tower's witness is also a finite closure over its own code set, so its
witness appears the same way. The per-site content is the L-side code set
(`AllCodes`, `src/L/Coding/CodeSet.lagda.md:440-441`), the L-side closure
(`src/L/Coding/InL.lagda.md:258-270`), and the L-side code-set stage
certificate (`src/ProbeLJ186A.agda:43-45`). None of the L terms transfers
literally; the J tower supplies its own. The J side is **INFERRED**: no J
tower exists in this tree.

## 7. NEGATIVES AND THEIR STATUS

1. "`w`'s appearance follows from the key's appearance, in the
   `hasWitnessAt A x` reading": **MEASURED TRUE** by the route of section
   2: `w ⊆ AllCodes A` (`src/ProbeLJ185B.agda:58-68`, 1.09 s), the code
   set's stage (`src/ProbeLJ186A.agda:43-45`, 1.61 s), and the decisive
   finite-family step (`src/ProbeLJ188A.agda:56-61`, 1.72 s), with the
   limit-stage climb at `src/L/BoundedSubset.lagda.md:1401` and
   `src/L/Constructible.lagda.md:355-356`.
2. "The witness step is circular, i.e. it needs the theorem's conclusion
   `x ∈ Lset κ`": **MEASURED FALSE**. The route's input is the code set's
   stage-fact, a hypothesis of the same class as `x∈Lλ`
   (`src/L/BoundedSubset.lagda.md:1402`); the conclusion
   (`:1621`) never enters.
3. "The universal `witK` is true for every closed shaped witness":
   **MEASURED FALSE**, `[LJ-1.87]`, red control at
   `src/ProbeLJ187B.agda:132.50-54`. The universal form is dropped and
   replaced by the per-witness construction.
4. "The closure is built by separation over `AllCodes A`":
   **MEASURED FALSE** by reading. It is built by recursion
   (`src/L/Coding/InL.lagda.md:258-270`); `AllCodes A` itself is built by
   separation (`src/L/Coding/CodeSet.lagda.md:440-441`). The route does not
   need the closure to be built by separation.
5. "The frame carries a stage for `x`": **MEASURED TRUE**, `x∈Lλ` at
   `src/L/BoundedSubset.lagda.md:1402`, also `:1146`.
6. "The frame supplies `AllCodes A ∈ Lset lam`": **MEASURED FALSE** by
   reading and search. No frame hypothesis names the code set's stage, and
   no instantiation exists (`[LJ-1.86]`). Same class as `x∈Lλ`; a wiring
   gap, not condensation.
7. "The key-route code-member facts are delivered": **INFERRED**. The
   subformula codes lying in the transitive closure of the key is argued,
   not a named lemma. The `AllCodes` route avoids this half.

## 8. GATES

- `src/ProbeLJ188A.agda`: GREEN at the C-12 cap, one process.
  `GHCRTS="-A64m -I0 -M8g" agda src/ProbeLJ188A.agda`, 1.72 s wall (warm
  dependencies). Load average at run: 2.89 / 4.24 / 4.80, four users, the
  machine was NOT quiet.
- `src/ProbeLJ185B.agda`: GREEN, 1.09 s wall, same load window.
- `src/ProbeLJ186A.agda`: GREEN, 1.61 s wall, load 3.22 / 4.29 / 4.82.
- One `agda` process at a time; all runs returned; none needed killing.
  No process was left alive.
- `scripts/check-fences.py --check`: clean, **87 masters**, run threshold 3.
- `scripts/lint-prose.py --check` on the probe and this report: exit 0.
- `scripts/lint-agda.py --check` on the probe: exit 0.
- Masters: none touched. `git status` is clean; HEAD `8a7c40b` on
  `two-tower-bridge`, unchanged. The probe is ignored by `.gitignore:22`
  (`src/Probe*.agda`); this report by `.gitignore:2` (`_build/`). No
  `make check`. No commit, no push.
- DD23: no mathematical prose was written or changed.

## 9. ARCHIVE USED

- `_build/lj-1.87-report.md`, read WHOLE. TOOK the red control
  (`src/ProbeLJ187B.agda:132.50-54`), the two-premises decomposition, and
  the INFERRED repair direction (section 2: "the consumer's actual witness
  is the subformula closure, which is finite"), which this dispatch
  machine-checked.
- `src/ProbeLJ187B.agda`, read WHOLE. TOOK the `witK-repaired` frame and
  the `w∈𝒟ₒδ` red step.
- `_build/lj-1.86-report.md`, read WHOLE. TOOK the frame walk (`lam` a
  module parameter at `src/L/BoundedSubset.lagda.md:902-904`,
  `:1144-1146`, `:1396-1401`) and the missing stage condition
  `AllCodes A ∈ Lset lam`.
- `src/ProbeLJ186A.agda`, read WHOLE and RE-RUN. TOOK `AllCodes-stage`
  (`:43-45`), GREEN 1.61 s.
- `_build/lj-1.85-report.md`, read WHOLE. TOOK the premise
  `w ⊆ AllCodes A` and its supply at the closure.
- `src/ProbeLJ185B.agda`, read WHOLE and RE-RUN. TOOK `clo⊆All`
  (`:58-68`), GREEN 1.09 s.
- `src/L/Axioms/Power.lagda.md`, read the opening (`:1-27`) and the recap
  (`:206-216`). TOOK the condensation disclaimer (`:18-20`, `:210-214`) as
  the statement that finiteness, not condensation, is the route.
- `src/L/BoundedSubset.lagda.md`, read the frames
  (`:900-904`, `:1144-1146`, `:1396-1402`) and the theorem (`:1621`). TOOK
  the exact `x⊆Lα` / `x∈Lλ` hypotheses and `succλ`.
- `src/L/Coding/CodeSet.lagda.md`, read the witness block
  (`:360-373`) and `AllCodes` (`:434-444`). TOOK `witnessAt-in`'s witness
  `clo ι ιL φ` at `:369` and `AllCodes`' construction.
- `src/L/Coding/InL.lagda.md`, read the key/closure definitions
  (`:248-284`) and `closure-inv` (`:445-457`). TOOK the recursive finite
  closure shape.
- `src/L/Axioms/Basic.lagda.md`, read `Lset-suc` (`:196`), `FinOf`
  (`:296-359`), `finSet∈𝒟ₒ` (`:352-354`), the union body (`:660-717`), and
  `pair∈Lset-suc` / `sgl∈Lset-suc` / `pr∈Lset-suc` (`:587-599`). TOOK the
  finite-family and successor-stage facts, the decisive step of this
  dispatch.
- `src/L/Constructible.lagda.md`, read `𝒟ₒ-intro/inv`, `𝒟ₒ∋⊆`
  (`:300-314`), `Lset-in/out` (`:316-338`), `Lset-mono` (`:355-356`).
  TOOK the out-and-subset decomposition and the monotone climb.
- `src/L/Stage.lagda.md`, read WHOLE. TOOK `stage` / `stage-ord` /
  `stage-mem` and the seal discipline.
- `src/L/Axioms/Separation.lagda.md`, read the separation certificate
  lines (`:198-199`, `:293-294`). TOOK the provenance of the code set's
  `isL` certificate.
- `src/L/Condensation.lagda.md`, read the `WitnessAgree` frame
  (`:6224-6249`). TOOK `witK` as a universal hypothesis and the transfer
  shape that consumes it.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3241`), C-36 (`:3284-3331`), D-30 (`:3332-3380`), read WHOLE.
  TOOK the discharge standard, the untested-block test, and the
  write-the-unwritable-term discipline.
- `archive/rud-route/`, SHAPE only. Read the README and the file list;
  took nothing. The route's `BelowLim` closes `Sset γ ∈ Lset (γ+1)` at a
  general limit, which is the same content class as the missing stage
  condition, but nothing here re-uses it.

## 10. LITERATURE USED

- `dev/literature/devlin-II5.md`, read Step C (section 2.3) and the 5.5
  chain (sections 1.4-1.5). TOOK the level-sequence witness reading and
  the 2.6(ii) carrier bound.
- `_build/literature/dev2.txt:1372-1385`, read the 5.5 proof. TOOK the
  witness-bound of section 5: the witness lands inside the carrier by
  2.6(ii), and the matrix bound `K(u)` lies inside the carrier
  (`:1191-1194`, `:593-630` via the digest).

## 6. THE DD4 ANSWER

## 7. NEGATIVES AND THEIR STATUS

## 8. GATES

## 9. ARCHIVE USED

## 10. LITERATURE USED
