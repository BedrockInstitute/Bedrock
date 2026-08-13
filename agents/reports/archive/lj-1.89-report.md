# LJ-1.89: prove witK by the finite-family route

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.89-report.md`.

## 0. THE VERDICT

**The repaired `witK` is PROVED.** The assembled term is `Frame.witK`
at `src/ProbeLJ189A.agda:266-306`, GREEN at the C-12 cap, one agda
process. 1.77 s wall (warm), 0.91 s user, 0.18 s sys. Load at run:
6.83 / 6.30 / 5.55, four users, the machine was NOT quiet. The abort
criterion's first branch fires: the assembly typechecks, so STOP.
`levelIn` and `cover` are untouched.

The route assembles end to end from the three inputs of the brief:

1. The frame hypothesis `AllCodes A ∈ Lset lam`, the only open premise
   (`witK`, `src/ProbeLJ189A.agda:267`).
2. The premise `w ⊆ AllCodes A`, supplied at the witness's birth site
   by `clo⊆All` (`src/ProbeLJ189A.agda:241-251`), restated from
   `src/ProbeLJ185B.agda:58-68`.
3. The delivered finiteness of the subformula closure. `closureFin`
   (`src/ProbeLJ189A.agda:203-216`) reads the delivered closure shape
   (`src/L/Coding/InL.lagda.md:258-270`) and returns the finite
   enumeration, through the singleton lemma `sglFin` (:88-101) and the
   union lemma `unionFin` (:104-161).

The body of `witK` composes the measured steps. `Lset-out` peels
`AllCodes A ∈ Lset lam` to `δ ∈ lam` with `AllCodes A ∈ 𝒟ₒ (Lset δ)`
(:270-271). `𝒟ₒ∋⊆` plus `clo⊆All` give `w ⊆ Lset δ` (:279-281). The
fiber enumeration `gδ` (:288-292) and the identity `eqδ` (:300-302)
put the finite family in the exact shape `finSet-stage` consumes.
`finSet-stage` (:254-259), restated from `src/ProbeLJ188A.agda:56-61`,
lands the family in `Lset (sucV δ)` (:304-306). `succλ` and `Lset-mono`
climb it into `Lset lam` (:275-277).

## 1. STAGED OR DISCHARGED

**STAGED, NOT DISCHARGED (C-38).** A hypothesis is discharged when
something SUPPLIES it. `BoundedSubsetAt` has no instantiation anywhere,
so even a proved `witK` is staged until a consumer supplies the frame
hypothesis. The eventual instantiation of `BoundedSubsetAt`'s module
telescope (`src/L/BoundedSubset.lagda.md:1396-1402`) would supply it:
the consumer that names `lam` and produces `x ∈ Lset lam` must also
produce the code set's stage `AllCodes A ∈ Lset lam`. No such
instantiation exists in the tree.

**A block with no consumer is UNTESTED (C-35).** This assembly has no
consumer in the tree. Its first consumer is its first real audit.

## 2. THE TERM

The statement, at `src/ProbeLJ189A.agda:266-268`:

```agda
  witK : {n : ℕ} (φ : Formula ⟪ fst A ⟫ n)
       → ⟨ fst (AllCodes A) ∈ˢ Lset lam ⟩
       → ⟨ fst (clo ι₀ ιL₀ φ) ∈ˢ Lset lam ⟩
```

`Frame` is module-parameterized (P-h): the carrier `A`, the limit stage
`lam`, its ordinality `ordλ`, and its successor closure `succλ`
(`src/ProbeLJ189A.agda:225-226`), the frame shape of
`BoundedSubsetAt`. The witness is the produced witness, the subformula
closure `clo ι₀ ιL₀ φ`, at its birth site. The conclusion is
`fst w ∈ Lset lam`, unchanged.

## 3. THE DD4 ANSWER

The assembly is generic in the stage, MEASURED by construction. `Frame`
takes the carrier and the stage as module parameters (P-h). The
finiteness machinery `ClosureFin` is parameterized by the carrier map
`f` and its `isL` certificate, and never names a concrete stage.
`finSet-stage` is stated at an arbitrary ordinal `σ`, and the climb is
one successor step inside the limit. The J tower's witness would appear
the same way: a finite closure over its own code set, definable one
level above the stage of its members. The J side is INFERRED: no J
tower exists in this tree, and no L term transfers literally. The J
tower supplies its own code set, its own closure, and its own code-set
stage certificate.

## 4. NEGATIVES AND THEIR STATUS

1. "The universal `witK` follows from the two premises": **MEASURED
   FALSE**. The red control at `src/ProbeLJ187B.agda:132.50-54` rejects
   the only assembly route. The universal form is replaced by the
   per-witness form.
2. "The repaired per-witness `witK` cannot be assembled": **MEASURED
   FALSE**. The assembly typechecks at `src/ProbeLJ189A.agda:266-306`.
3. "The closure-as-finite-enumeration identity is delivered in the
   tree": **MEASURED FALSE by reading**. It is built here as
   `closureFin` (`src/ProbeLJ189A.agda:203-216`) with `sglFin` and
   `unionFin`. It is wiring, not mathematics.
4. "A consumer supplies the frame hypothesis": **MEASURED FALSE**.
   `BoundedSubsetAt` appears once in the tree, at its declaration
   (`src/L/BoundedSubset.lagda.md:1396`). No instantiation exists.
5. "The assembly is generic in the stage": **MEASURED TRUE by
   construction**. Module parameters and an arbitrary-`σ` finiteness
   step carry it, per section 3.
6. "The J tower's witness appears the same way": **INFERRED**. No J
   tower exists in this tree.

## 5. GATES

- `src/ProbeLJ189A.agda`: GREEN at the C-12 cap, one process.
  `GHCRTS="-A64m -I0 -M8g" agda src/ProbeLJ189A.agda`, 1.77 s wall
  (warm), 0.91 s user, 0.18 s sys. Load average at run:
  6.83 / 6.30 / 5.55, four users, the machine was NOT quiet. The first
  successful check was 2.01 s wall.
- One `agda` process at a time. Every run returned; none hung; none
  needed killing. No process was left alive.
- `scripts/check-fences.py --check`: clean, **87 masters**, run
  threshold 3.
- `scripts/lint-prose.py --check` on the probe and this report:
  exit 0.
- `scripts/lint-agda.py --check` on the probe: exit 0.
- Masters: none touched. `git status` is clean; HEAD `6a3e4ee` on
  `two-tower-bridge`, unchanged. The probe is ignored by
  `.gitignore:22` (`src/Probe*.agda`); this report by `.gitignore:2`
  (`_build/`). No `make check`. No commit, no push.
- DD23: no mathematical prose was written or changed.

## 6. ARCHIVE USED

- `_build/lj-1.88-report.md`, read WHOLE. TOOK the three-step route,
  the `closure-stage` repair shape (section 3), and the honest caveat
  that the route's input is the code set's stage-fact.
- `src/ProbeLJ188A.agda`, read WHOLE and RE-RUN. TOOK `finSet-stage`
  (:56-61), restated at `src/ProbeLJ189A.agda:254-259`.
- `_build/lj-1.87-report.md`, read the verdict and the red assembly.
  TOOK the red control (`src/ProbeLJ187B.agda:132.50-54`) and the
  statement that the premises bound members, never `w` itself.
- `src/ProbeLJ187B.agda`, read WHOLE. TOOK the frame walk (`Lset-out`,
  `𝒟ₒ∋⊆`, `Lset-in` shape) that this dispatch completed with the
  finite-family step.
- `_build/lj-1.86-report.md`, read the verdict and section 1. TOOK the
  `AllCodes A` stage certificate provenance and the frame walk.
- `src/ProbeLJ186A.agda`, read WHOLE. TOOK `AllCodes-stage` (:43-45).
- `_build/lj-1.85-report.md`, read the verdict and section 1. TOOK the
  premise `w ⊆ AllCodes A` and its supply at the closure.
- `src/ProbeLJ185B.agda`, read WHOLE. TOOK `clo⊆All` (:58-68),
  restated at `src/ProbeLJ189A.agda:241-251`.
- `src/L/Axioms/Basic.lagda.md`, read `Lset-suc` (:190-205) and
  `FinOf` (:340-360). TOOK `finSet`, `finSet-in`, `finSet-out`, and
  `finSet∈𝒟ₒ` as the decisive machinery.
- `src/L/Constructible.lagda.md`, read `𝒟ₒ∋⊆` (:313), `Lset-in/out`
  (:316-338), `Lset-mono` (:355-356). TOOK the out-and-subset
  decomposition and the monotone climb.
- `src/L/Ordinal.lagda.md`, read `mem-ord` (:221-222). TOOK the
  ordinality of `δ` below `lam`.
- `src/L/Coding/InL.lagda.md`, read the closure (:258-270),
  `closure-inv` (:445-457), `key∈closure` (:492-504), and the
  singleton/union memberships (:338-360). TOOK the delivered finite
  closure shape, read by `closureFin`.
- `src/L/Coding/Closed.lagda.md`, read `clo` (:78-81). TOOK
  `fst (clo f h φ) ≡ closure f h φ`, definitional.
- `src/L/Coding/CodeSet.lagda.md`, read `key∈AllCodes` (:443-444) via
  the report of `[LJ-1.85]`. TOOK the premise's supply.
- `src/L/Condensation.lagda.md`, read the `WitnessAgree` frame
  (:6224-6249). TOOK the `witK` hypothesis shape that the per-witness
  form replaces.
- `src/L/BoundedSubset.lagda.md`, read the frame (:1396-1402) and
  searched for instantiations. TOOK the exact `lam`/`succλ`/`x∈Lλ`
  parameters; TOOK the absence of any `BoundedSubsetAt` instantiation
  as the C-38 basis.
- `dev/LESSONS.md`, read WHOLE the sections C-35 (:3200-3241), C-36
  (:3284-3331), D-30 (:3332-3380), C-38 as extended (:3427-3511).
  TOOK the discharge standard, the untested-block test, and the
  write-the-unwritable-term discipline.
- `archive/rud-route/`, SHAPE only. Read the README and the file list.
  TOOK nothing; the archived `BelowLim` closes a general-limit stage
  fact, which is the same content class as the frame hypothesis, but
  nothing here re-uses it.

## 7. LITERATURE USED

Banked: `[LJ-1.88]` answered how Devlin bounds his witness. Nothing
spent in this dispatch.
