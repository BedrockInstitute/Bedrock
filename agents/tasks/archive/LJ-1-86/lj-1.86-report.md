# LJ-1.86: is there a stage that contains AllCodes A?

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.86-report.md`.

## 0. THE VERDICT

**A stage containing `AllCodes A` exists (MEASURED TRUE), and the
condensation proof cannot choose it (MEASURED FALSE, by reading). STOP
per D-1: the second half fails, so the gap does not close.**

Half 1: `AllCodes A` is an element of `L` by the delivered construction
itself. The separation machinery builds it as a definable subset of a
stage, so its carrier element carries an `isL` certificate, and the
earliest-stage function names the ordinal that contains it:

```agda
AllCodes-stage : (A : Sʟ) → Σ[ lam ∈ V ℓ ] (IsOrd lam × ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩)
AllCodes-stage A = stage (fst (AllCodes A)) ((AllCodes A) .snd)
                 , stage-ord (fst (AllCodes A)) ((AllCodes A) .snd)
                 , stage-mem (fst (AllCodes A)) ((AllCodes A) .snd)
```

Machine-checked GREEN at the C-12 cap, `src/ProbeLJ186A.agda:43-45`,
1.93 s wall (warm dependencies; load average 4.90 / 5.14 / 6.88 at run,
four users, the machine was NOT quiet). The stage is
`stage (fst (AllCodes A)) ((AllCodes A) .snd)`, and its ordinality and
membership come from `L.Stage` (`src/L/Stage.lagda.md:180`, `:185-186`,
`:188-189`). This is not a rank inference: the certificate is built by
the construction, at `file:line` in section 1.

Half 2: the stage in `witK`'s frame is fixed upstream. Every frame that
reaches `witK` takes `lam` and its admissibility as module parameters
(`src/L/BoundedSubset.lagda.md:902-904`, `:1144-1146`, `:1396-1401`),
and the `[LJ-1.81]` existential freedom covers only the level bound
`K'`, never the stage (`src/ProbeLJ152A.agda:78-81`). So the proof can
pick the bound `K'` but cannot pick `lam`. Section 2 gives the frame
walk at `file:line`.

Because half 2 fails, the repaired `witK` cannot be assembled from the
delivered tree: the stage condition `AllCodes A ∈ Lset lam` at the
frame's fixed `lam` is not provable in general (INFERRED; the
knife-edge `α+ω` counterexample of the LJ-1.85 report). The obligation
moves to the frame as a hypothesis, in the same class as the tower's
own `x∈Lλ` (`src/L/BoundedSubset.lagda.md:1145-1146`).

## 1. HALF 1: IS `AllCodes A` CONSTRUCTIBLE?

The delivered construction, at `file:line`:

1. `AllCodes A = sepAny .fst .fst`
   (`src/L/Coding/CodeSet.lagda.md:440-441`), where
   `sepAny = hasSeparationL (smallAny .fst) (isCodeAny A)`
   (`:308-310`). The superset `smallAny .fst` is a stage delivered by
   `smallDom` (`src/L/Recursion.lagda.md:133-134`).
2. `hasSeparationL a φ` is a transport of
   `separateΔ₀ a (relativize c φ) (Δ₀-relativize c φ)` along the
   pointwise predicate equality (`src/L/Axioms/Full.lagda.md:144-147`).
3. `separateΔ₀` runs `AtStage.separateAt`
   (`src/L/Axioms/Separation.lagda.md:481`), whose centre is
   `sepElt = carve ψ , 𝒟ₒ→isL σ oσ (carve ψ) (carve∈𝒟ₒ ψ)`
   (`:293-294`), with `carve∈𝒟ₒ ψ : ⟨ carve ψ ∈ 𝒟ₒ (Lset σ) ⟩`
   (`:198-199`).
4. `𝒟ₒ→isL σ oσ x : ⟨ x ∈ 𝒟ₒ (Lset σ) ⟩ → ⟨ isL x ⟩`
   (`src/L/Axioms/Basic.lagda.md:98`). Its proof places `x` inside
   `Lset (sucV σ)` through `Lset-compute` and the union branch at
   `sucV σ`, with `suc-ord oσ` supplying the ordinality.
5. The transport does not move the underlying set: the first component
   of `SetOf` is constant in the predicate, so `fst (AllCodes A)` is
   `carve ψ` and `(AllCodes A) .snd` is the certificate
   `⟨ isL (fst (AllCodes A)) ⟩`.

So the tree already proves constructibility, and the probe names the
stage: `stage (fst (AllCodes A)) ((AllCodes A) .snd)` is an ordinal by
`stage-ord` and contains `fst (AllCodes A)` by `stage-mem`. The probe
imports only delivered modules: `L.Coding.CodeSet`, `L.Constructible`,
`L.Stage` (`src/ProbeLJ186A.agda:13-19`).

The answer to the brief's question 1 is YES, at
`src/ProbeLJ186A.agda:43-45`, resting on
`src/L/Axioms/Separation.lagda.md:293-294` and `:198-199` and
`src/L/Axioms/Basic.lagda.md:98`.

## 2. HALF 2: CAN THE CONDENSATION PROOF CHOOSE `lam`?

No. The walk, at `file:line`:

1. `witK` is a parameter of `WitnessAgree`
   (`src/L/Condensation.lagda.md:6224-6229`): its conclusion is
   `⟨ fst w ∈ fst (lookup K γ) ⟩`, membership in the env's K-slot
   value. The module is generic over `n`, the slots, `γ`, `f` and
   `witK` itself.
2. The frames that would instantiate the env and discharge `witK` all
   take `lam` as a module parameter:
   - `UnionKit (α lam x : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
     (α∈λ : ⟨ α ∈ˢ lam ⟩) (x⊆Lα : ...) (x∈Lλ : ⟨ x ∈ˢ Lset lam ⟩)
     (α∉ω : ...)` (`src/L/BoundedSubset.lagda.md:1144-1146`);
   - `HullStage (lam : S) (ordλ : IsOrd lam) (succλ : ...) (X : S)
     (X⊆L : ...) (∅∈λ : ...)` (`:902-904`);
   - `Devlin55.BoundedSubsetAt` adds `κ`, `α`, `x` and `lam` with their
     hypotheses (`:1396-1401`), and its theorem is
     `⟨ x ∈ˢ Lset κ ⟩` (`:1621`), universal over the parameters.
3. The existential freedom named by `[LJ-1.81]` is in `Adeq m`:
   `∥ Σ[ K' ∈ S ] Σ[ v' ∈ S ] Σ[ w' ∈ S ] (⟨ w' ∈ˢ K' ⟩ × ...) ∥₁`
   (`src/ProbeLJ152A.agda:78-81`). The three witnesses are the bound
   `K'` and its two partners; `lam` is not among them. The bound is a
   constructible set inside the stage, by the elementarity-down chain
   (`_build/lj-1.81-report.md` section 1).
4. No delivered term instantiates these frames: a search for
   `Devlin55`, `BoundedSubsetAt` and `HullStage` over `src/` returns
   zero hits outside `src/L/BoundedSubset.lagda.md`. This matches the
   LJ-1.81 finding that the chain is not placed. The eventual theorem
   statement quantifies `lam` universally; the proof does not choose
   it.

Consequence: a chosen `K'` that contains `AllCodes A` would still have
to satisfy `K' ∈ Lset lam` (hull membership), so the condition
`rank (AllCodes A) < lam` cannot be manufactured by the proof. The
freedom reaches the bound, not the stage.

The answer to the brief's question 2 is NO, at
`src/L/BoundedSubset.lagda.md:1396-1401` and
`src/ProbeLJ152A.agda:78-81`.

## 3. THE TERM THAT COULD NOT BE WRITTEN

The repaired `witK`'s stage obligation is the type

```agda
(A : Sʟ) (lam : V ℓ) (ordλ : IsOrd lam) → ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩
```

It has no inhabitant in general at the frame's fixed `lam`. The
knife-edge case: at `lam = α+ω` with carrier `A = LsetS α`, the frame
is admissible (the LJ-1.80 parameters hold), the set `AllCodes A`
itself satisfies the full repaired premise (closed, shaped, contains
the formula key, trivially `⊆` itself), and `AllCodes A ∉ Lset (α+ω)`
because the members' ranks are cofinal below `α+ω`. This is
**INFERRED**: it is the mathematical argument of `_build/lj-1.85
-report.md` section 4, not machine-checked, and per the brief's
classification rule it sets no verdict by itself. The MEASURED verdict
is the frame reading of section 2: `lam` is a parameter, so the proof
cannot dodge the case.

Where the obligation moves: the frame must carry the stage condition as
a hypothesis, `⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩` (equivalently
`stage (fst (AllCodes A)) ((AllCodes A) .snd) ∈ lam`, by `Lset-mono`).
That is the same class as the tower's own `x∈Lλ`
(`src/L/BoundedSubset.lagda.md:1145-1146`), and no consumer supplies it
today. The consumer that must supply it is whoever instantiates
`BoundedSubsetAt` and the repaired `WitnessAgree` at a concrete env:
the tower's rank machinery, exactly as the LJ-1.85 report concluded.

## 4. NEGATIVES AND THEIR STATUS

1. "`AllCodes A` is constructible; some ordinal stage contains it":
   **MEASURED TRUE**. `AllCodes-stage`
   (`src/ProbeLJ186A.agda:43-45`) checks GREEN at the C-12 cap, 1.93 s
   wall at load 4.90 / 5.14 / 6.88. The certificate's provenance:
   `src/L/Axioms/Separation.lagda.md:293-294` and `:198-199`,
   `src/L/Axioms/Basic.lagda.md:98`.
2. "The condensation proof can choose that `lam`": **MEASURED FALSE**
   by reading. `lam` is a module parameter at
   `src/L/BoundedSubset.lagda.md:902-904`, `:1144-1146`, `:1396-1401`;
   no instantiation exists (search returns zero hits outside
   `BoundedSubset.lagda.md`); the `Adeq` existential covers only
   `K' v' w'` (`src/ProbeLJ152A.agda:78-81`).
3. "`AllCodes A ∈ Lset lam` holds at the frame's fixed `lam` in
   general": **INFERRED FALSE**. The `α+ω` counterexample
   (`_build/lj-1.85-report.md` section 4) is argued, not machine-
   checked. Sets no verdict by itself; verdict 2 carries the finding.
4. "Some consumer supplies the stage condition": **MEASURED FALSE**.
   No delivered term states or proves `AllCodes A ∈ Lset lam`; the
   frames' hypotheses are `x∈Lλ` and the admissibility of `lam`
   (`src/L/BoundedSubset.lagda.md:1144-1146`, `:1396-1401`), not a
   code-set stage condition.

## 5. DEVLIN'S BOUND

Devlin gets a stage large enough by choosing it. In lemma 5.5 he "lets
λ be a limit ordinal such that λ ≤ κ and x ∈ L_λ"
(`_build/literature/dev2.txt:1377-1378`): since `x ⊆ L_α` gives
`x ∈ L_{α+1}` and κ is a cardinal above α, a limit λ above the
witness's stage and below κ exists, and λ is picked inside the proof
after x is known (`dev/literature/devlin-II5.md` section 2.3 Step C).

The tree's analogue is missing at the same point. The tree's `lam` is
not a local choice: it is a fixed module parameter of the frames that
reach `witK` (`src/L/BoundedSubset.lagda.md:1396-1401`), so the
"choose a stage that outranks the code set" step cannot be performed.
The content Devlin gets by choosing must enter the tree as a
hypothesis, exactly as `x∈Lλ` already does
(`src/L/BoundedSubset.lagda.md:1145-1146`).

## 6. THE DD4 ANSWER

The stage argument is generic in SHAPE and per-tower in CONTENT. The
shape "the code set is built by separation; separation produces a
definable subset of a stage with an `isL` certificate; the earliest-
stage function names the containing stage" is a template both towers
can follow, and the frame obligation "the frame's stage outranks the
code set's stage" has the same shape on both sides. The content is
per-site: the L code set is satisfaction-based
(`src/L/Coding/CodeSet.lagda.md:434-441`), the certificate comes from
L's `𝒟ₒ→isL` (`src/L/Axioms/Basic.lagda.md:98`) and `carve∈𝒟ₒ`
(`src/L/Axioms/Separation.lagda.md:198-199`), and the rank bound
(`α+ω`) is L-side ordinal arithmetic. None of the L terms transfers
literally; the J tower supplies its own code set, its own hierarchy
certificate and its own bound. The J side is **INFERRED**: no J tower
exists in this tree. This matches the LJ-1.85 split: the code-set data
is per-site content, and the frame shape is shared.

## 7. GATES

- `src/ProbeLJ186A.agda`: GREEN at the C-12 cap, one process.
  `GHCRTS="-A64m -I0 -M8g" agda src/ProbeLJ186A.agda`, 1.93 s wall
  (warm dependencies). Load average at run: 4.90 / 5.14 / 6.88, four
  users, the machine was NOT quiet. No other agda process was started;
  none needed killing.
- `scripts/check-fences.py --check`: clean, 87 masters, run threshold 3.
- `scripts/lint-prose.py --check`: exit 0.
- `scripts/lint-agda.py --check`: exit 0.
- Masters: none touched. `git status`: working tree clean; the probe is
  ignored by `.gitignore:22` (`src/Probe*.agda`) and the report by
  `.gitignore:2` (`_build/`). `make check` was not run.
- DD23: no mathematical prose was written or changed.

## 8. ARCHIVE USED

- `_build/lj-1.85-report.md`, read WHOLE. TOOK the repaired premise
  (`w ⊆ AllCodes A`), the missing stage condition as the named absence
  (sections 0 and 4), and the knife-edge `α+ω` counterexample
  (section 4, INFERRED).
- `src/ProbeLJ185A.agda` and `src/ProbeLJ185C.agda`, read WHOLE. TOOK
  the `Sʟ` conventions, the stage parameters (`lam`, `ordλ`, `α`,
  `ordα`, `α∈λ`, `α∉ω`), and the imports for the stage lemmas.
- `src/ProbeLJ185B.agda`, read WHOLE. TOOK the supply point
  (`clo⊆All`, `:58-68`): the consumer's witness lies in `AllCodes A`
  member by member.
- `_build/lj-1.84-report.md` and `src/ProbeLJ184A.agda`, read WHOLE.
  TOOK the junk-member refutation mechanism and the recorded missing
  stage condition.
- `_build/lj-1.81-report.md`, read WHOLE. TOOK the `Adeq` existential
  (`K' v' w'`), the bound-in-the-stage reading, and the finding that
  the chain is not placed.
- `src/L/Constructible.lagda.md`, read WHOLE. Read-only. TOOK `Lset`,
  `Lset-compute`, `Lset-in/out`, `Lset-mono`, `𝒟ₒ`, `𝒟ₒ-intro`,
  `isLayer` and `layer-trans`.
- `src/L/Ordinal/Stages.lagda.md`, read WHOLE. Read-only. TOOK
  `ord∈Lset-suc`, `Lset-cumul`, `suc∈or≡` and the `𝒟ₒ→Lset-suc` shape.
- `src/L/Coding/CodeSet.lagda.md`, read WHOLE. Read-only. TOOK
  `AllCodes` (`:440-441`), `sepAny` (`:308-310`), `smallAny`
  (`:304-306`), and the `AllCodes-in/out` pair.
- `src/L/Axioms/Full.lagda.md`, read WHOLE. Read-only. TOOK
  `hasSeparationL` (`:144-147`).
- `src/L/Axioms/Separation.lagda.md`, read WHOLE. Read-only. TOOK
  `sepElt` (`:293-294`), `carve∈𝒟ₒ` (`:198-199`), `separateAt`
  (`:281-284`) and `separateΔ₀` (`:481`).
- `src/L/Axioms/Basic.lagda.md`, read the opening and `𝒟ₒ→isL`
  (`:98-121`). TOOK the certificate: a member of `𝒟ₒ (Lset σ)` lands in
  `Lset (sucV σ)`.
- `src/L/Stage.lagda.md`, read WHOLE. TOOK `stage`, `stage-ord`,
  `stage-mem` and their seal discipline.
- `src/L/Recursion.lagda.md`, read `smallDom` (`:133-134`) and its
  prose. TOOK the stage-valued superset.
- `src/L/Condensation.lagda.md`, read the `WitnessAgree` frame
  (`:6224-6229`) and the agreement band around it. TOOK `witK` as a
  parameter and the env-K conclusion.
- `src/L/BoundedSubset.lagda.md`, read the mandated frames:
  `HullStage` (`:902-904`), `UnionKit` (`:1144-1146`),
  `BoundedSubsetAt` (`:1396-1401`), and the theorem (`:1621`). TOOK
  the universal-parameter reading of `lam`.
- `src/ProbeLJ152A.agda`, read the `Adeq` statement (`:78-81`). TOOK
  the existential's exact variable list.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3511`), C-35
  (`:3200-3241`), C-36 (`:3284-3331`), D-30 (`:3332-3380`), read
  WHOLE. TOOK the discharge standard (a hypothesis is discharged when
  something supplies it) and the restatement-vs-instantiation audit.
- `archive/rud-route/`, SHAPE only. Read the README and the file list;
  took nothing.

## 9. LITERATURE USED

- `dev/literature/devlin-II5.md`, read Step C (section 2.3) and the
  5.5 context. TOOK the two-line bound of section 5: Devlin chooses a
  limit λ with `x ∈ L_λ` after x is known.
- `_build/literature/dev2.txt:1372-1385`, read the 5.5 proof. TOOK the
  "let λ be a limit ordinal such that λ ≤ κ and x ∈ L_λ" step at
  `:1377-1378` as the tree's missing choice.
