# LJ-1.235 report: strengthen `hasReplacementL`'s conclusion

tier: pi (deepseek-subagent-mode). One Agda process, cap `GHCRTS="-A64m -I0 -M8g"`,
never raised. No master, brief or report edited. No commit, no push. No
`make check`. Written incrementally (C-22).

## 0. LEAD: STEP ZERO, THEN THE WALL (c) VERDICT

**Step zero: exit code 0.** The bounded decode probe typechecks. **Elapsed,
first run: 6.1 user seconds, 7.2 real seconds.** A re-run later in the session:
1.5 user seconds, 2.5 real seconds, load 3.84 (two users, 16 CPUs). Both runs
were WARM: `_build/2.8.0/agda/agents/tasks/LJ-1-124/ProbeLJ1124A.agdai`
already exists. The report's cold figure is 37.43 user seconds
(`agents/tasks/LJ-1-124/lj-1.124-report.md:44-52`). The probe is green today.
I ran it from its task directory with the include path set, because the module
name predates the one-directory-per-task move
(`agents/tasks/LJ-1-233/lj-1.233-report.md:146-149`).

**Wall (c) verdict: THE BOUND COMES OUT.** The strengthened conclusion
typechecks. The bound is `βimg`, the stage `hasReplacementL` already computes
inside `module Images` and then discards. It is stated in terms of the input.

## 1. THE LEMMA I WROTE

The probe is `agents/tasks/LJ-1-235/ProbeLJ1235A.agda`. It writes one sibling
lemma beside `hasReplacementL`, leaving `hasReplacementL` unchanged.

The statement:

```agda
hasReplacementL-bound : (a : S) (φ : Formula S 2)
  → (fc : (x : S) → ⟨ x ∈ˢ a ⟩
       → isContr (Σ[ y ∈ S ] ⟨ (y ∷ x ∷ []) ⊨ φ ⟩))
  → Σ[ β ∈ V ℓ ] (IsOrd β
       × isContr (SetOf (replQ a φ))
       × ((y : S) → ⟨ replQ a φ y ⟩ → ⟨ fst y ∈ Lset β ⟩))
```

The proof:

```agda
hasReplacementL-bound a φ fc =
  βimg , (βimg-ord , (hasReplacementL a φ fc , img-mem))
  where
  open Images a φ fc

  img-mem : (y : S) → ⟨ replQ a φ y ⟩ → ⟨ fst y ∈ Lset βimg ⟩
  img-mem y = PT.rec (snd (fst y ∈ Lset βimg))
    (λ { (x , (x∈a , h)) →
        subst (λ w → ⟨ fst w ∈ Lset βimg ⟩)
          (img-uniq (x , x∈a) y h)
          (img∈βimg (x , x∈a)) })
```

It returns `βimg` and `βimg-ord` (both public fields of `Images`), the existing
`hasReplacementL a φ fc` as the contractible replacement set, and `img-mem`,
which lifts `img∈βimg` from the indexed images to every member of the
replacement set.

**Written lines:** 18 non-blank, non-comment code lines (`replQ` onward). The
whole probe file has 40 non-blank, non-comment lines, 60 physical lines.

## 2. WHETHER THE BOUND IS IN TERMS OF `b`

**YES.** `βimg` is defined inside `Images a φ fc` as

```agda
βimg = boundingOrd ⟪ fst a ⟫
         (λ m → stage (fst (img (memS m))) (img (memS m) .snd))
         (λ m → stage-ord (fst (img (memS m))) (img (memS m) .snd))
         .fst
```

(`src/L/Axioms/Full.lagda.md:222-229`). It is the bound on the stages of the
images, computed by `boundingOrd` over the fibers `⟪ fst a ⟫` of the input.
For the `hierL` consumer, `a = (b, hb)`, so `fst a = b` and the bound is a
function of `b` and `φ` alone.

## 3. CONSUMERS (C-40)

I wrote a sibling lemma. `hasReplacementL` is unchanged. No consumer breaks.

The five call sites are, MEASURED by `grep`:

1. `src/L/Hierarchy.lagda.md:595` — `r = hasReplacementL A φ fc`
2. `src/L/Model.lagda.md:91` — `hasReplacement = hasReplacementL` (field use)
3. `src/L/Choice/Table.lagda.md:751` — `rep = hasReplacementL A φ fc`
4. `src/L/Choice/Before.lagda.md:1214` — `r = hasReplacementL ωʟ φ fc`
5. `src/L/Recursion.lagda.md:177` — `r = hasReplacementL dom graph funct .fst`

None of them sees the new lemma. This is the cheaper branch the brief named.

## 4. SECONDS, LOAD, RUN COUNT

One Agda process, cap `GHCRTS="-A64m -I0 -M8g"`. Warm caches. The warm-up run
(discarded): 1.77 s real. Three kept runs: **1.69 s, 0.91 s, 0.85 s** real.
Load at the close: **3.99** (two users, 16 CPUs). The figure the decision
rests on is the exit code, not a wall time: the probe is 40 code lines and the
bulk of every run is loading cached interfaces for `L.Axioms.Full`.

## 5. NEGATIVES, CLASSIFIED

| negative | class |
|---|---|
| the bound comes out | **MEASURED TRUE.** `ProbeLJ1235A.agda` typechecks, exit 0 |
| the bound is in terms of `b` | **MEASURED TRUE.** `βimg = boundingOrd ⟪ fst a ⟫ …`, `src/L/Axioms/Full.lagda.md:222-229` |
| strengthening breaks a consumer | **MEASURED FALSE.** `hasReplacementL` unchanged; five call sites untouched |
| the bound is `sucV (sucV b)` literally | **MEASURED FALSE.** It is `boundingOrd` over the image stages, not that literal term |
| `βimg` is not a function of the input | **MEASURED FALSE.** It depends on `a`, `φ`, `fc` only |
| the bound places the SET itself in a stage | **NOT DELIVERED.** `img-mem` places each member; the set-level climb is the consumer's assembly, per the brief's "supply the ingredient" |

## 6. DD4

The SHAPE is tower-neutral; the instantiation is per-tower.

`boundingOrd` is ambient-V machinery (`src/L/Ordinal.lagda.md:154-183`) and is
shared by both towers. The per-tower content in `βimg` is exactly `stage`
(`src/L/Stage.lagda.md:180`) and `Lset`, both L-specific. So the shape — bound
the image stages by `boundingOrd` over the input's fibers, and expose that
bound — could be stated once over a structure parameter carrying the tower's
`stage` and level operation, and instantiated twice. `hasReplacementL` itself
is L's axiom instance, so the concrete `Images` module is per-tower by its
name. The J tower needs its own `Images` with its own `stage`; the bound shape
carries over.

## 7. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:88-106` and `:362-394`.**

Devlin does NOT need a separate rank bound on a replacement image at this
point. His level sequence is the Σ₁ witness `z` of the formula
`v = L_γ ↔ ∃z Φ(z, v, γ)` (`:96`), and its members are levels `L_δ` for
`δ < γ`, which land in `L_γ` by the cumulative construction of the tower. He
gets the bound from the construction, not from a rank lemma on a replacement
image. **MEASURED** by reading `:96-100`.

Our tree builds `hierL b` by the replacement axiom (`src/L/Hierarchy.lagda.md:594-595`),
so the bound is not visible in the construction; it must be exported. That is
exactly the strengthening this probe writes. **INFERRED**, from the two
presentations.

## 8. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-233/lj-1.233-report.md`, read WHOLE.** TOOK the wall (c)
  refinement (`:49-56`), the `βimg`/`img∈βimg` location (`:227-231`), the
  step-zero include-path note (`:146-149`), and the C-42 negatives table
  (`:260-265`).
- **`agents/tasks/LJ-1-230/lj-1.230-report.md`, read WHOLE.** TOOK the two
  candidate shapes (`:81-86`) and the five call sites (`:60-64`).
- **`agents/tasks/LJ-1-124/lj-1.124-report.md`, read WHOLE.** TOOK the GO and
  the cold seconds (`:44-52`), and the term list (`:23-30`).
- **`agents/tasks/LJ-1-124/ProbeLJ1124A.agda`, read WHOLE.** TOOK the module
  header and the `graph-out`/`graph-in` terms (`:199-209`).
- **`src/L/Axioms/Full.lagda.md`, read `:180-340`.** TOOK `module Images`
  (`:195-241`), `βimg` (`:222-229`), `img∈βimg` (`:231`), and `hasReplacementL`
  (`:277-280`). **NOT edited.**
- **`src/L/Hierarchy.lagda.md`, read `:500-660`.** TOOK `hierAt` (`:537`),
  the `hasReplacementL` build (`:594-595`), `hierL` (`:621-622`), and the
  `Lset-defines` consumer (`:646-659`).
- **`src/L/Ordinal.lagda.md`, read `:150-196`.** TOOK `boundingOrd` and `bound2`.
- **`src/L/Stage.lagda.md`, read `:176-193`.** TOOK `stage`, `stage-ord`,
  `stage-mem`.
- **`src/L/Constructible.lagda.md`, read `:215-227`, `:355-356`, `:376-411`.**
  TOOK `Lset`, `Lset-mono`, `isL`, `𝒮ʟ`.
- **`src/L/Axioms/Basic.lagda.md`, read `:154-157`, `:196`.** TOOK `isL-Lset`,
  `LsetS`, `Lset-suc`.
- **`src/L/BoundedSubset.lagda.md`, read `:904`, `:1394`.** TOOK `succλ`.
- **`src/L/Model.lagda.md:91`**, **`src/L/Recursion.lagda.md:177`**, read for the
  consumer audit.
- `archive/dev/TASKS-archived.md` and `archive/src/2026-08-09-rud-route/`:
  **NOT read.** The retired route's shape question is answered by the live
  `Full.lagda.md` source; I state that plainly.

## 9. PROHIBITIONS, ANSWERED

No master, brief or report edited. `src/Everything.lagda.md` not opened.
`agents/tasks/LJ-1-236/` not touched. `src/L/Choice/Name.lagda.md` not opened.
No commit, no push, no `git checkout`/`stash`/`reset`/`clean`. No `make check`.
One Agda process at a time, cap never raised.

**My files:** `agents/tasks/LJ-1-235/ProbeLJ1235A.agda` and
`agents/tasks/LJ-1-235/lj-1.235-report.md`.

## 10. GATES

- `scripts/lint-agda.py --check agents/tasks/LJ-1-235/ProbeLJ1235A.agda`: clean.
- `scripts/lint-prose.py --check agents/tasks/LJ-1-235/ProbeLJ1235A.agda`: clean.
- `scripts/check-probes.py --check`: clean.
- `make check` not run.
