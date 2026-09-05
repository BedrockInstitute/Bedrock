# LJ-1.78: make the closure facts conditional, on ONE row, and see if the proof survives

Status: COMPLETE, written incrementally per C-22. No commit, no push.
ASD-STE100. This report is `_build/lj-1.78-report.md`.

## 0. THE VERDICT

**`MemAgree` SURVIVES conditional closure facts. The repair is
mechanical, and the probe is green.** STOP per the pre-fixed abort
criterion (D-1): one row decides, and this row went through.

The row proof's only use of the two facts was the single
`BinaryShape.in'` call in `back`
(`src/L/Condensation.lagda.md:4190-4191`). With the facts guarded,
that call takes the two membership witnesses, and the row already
has them bound two lines earlier: `(arK , (aK , bK)) = codesK c ar a b
c∈ shEq` (`:4189`). The forward direction `out` never mentions the two
facts at all; its text is byte-identical in the probe.

Machine-checked at `src/ProbeLJ178A.agda:107-315`: the guarded
`BinaryShape'.in'` (`:174-215`) and the full guarded `MemAgree'`
module with both `out` (`:278-292`) and `back` (`:294-315`) check
GREEN under the C-12 cap, one process:

```text
GHCRTS="-A64m -I0 -M8g" agda -i . -i _build/2.8.0/agda/src src/ProbeLJ178A.agda
exit 0, first successful check 6.08 s wall (4.98 s user),
re-check 2.76 s wall (1.55 s user), warm dependencies
```

Load average was 28.08 to 49.03 (4 users) across the runs: the
machine was NOT quiet, and every absolute figure carries that caveat.
The deciding positive is MEASURED.

## 1. THE CONDITIONAL FORMS

The row's two closure facts, both stated at the row's own `K` slot
(`K-slot = fst (lookup K γ)` at the `MemAgree` frame), become:

```agda
innerK : (a b : S) → ⟨ fst a ∈ K-slot ⟩ → ⟨ fst b ∈ K-slot ⟩
       → ⟨ fst (prʟ (numeralL 0) (prʟ a b)) ∈ K-slot ⟩
pairK  : (a b : S) → ⟨ fst a ∈ K-slot ⟩ → ⟨ fst b ∈ K-slot ⟩
       → ⟨ fst (prʟ a b) ∈ K-slot ⟩
```

Each new premise is `⟨ component ∈ K-slot ⟩` for the component the
conclusion mentions. A real consumer supplies it in `back`, from the
row's own `codesK` fact: `codesK c ar a b c∈ shEq` concludes
`ar ∈ K × a ∈ K × b ∈ K` (`src/L/Condensation.lagda.md:4189`), and
`aK bK` are passed straight into `BinaryShape.in'`
(`src/ProbeLJ178A.agda:301-303`). No new hypothesis is added: `codesK`
is already a site-fact parameter of the row, so the supply point
exists in the telescope as it stands.

At the frame, `BinaryShape'.in'` states the two witnesses as explicit
parameters at the frame's own positions: `a₀ = lookup (suc (suc zero))
γ`, `b₀ = lookup (suc zero) γ` at the 5-deep frame, which are
definitionally the row's `a` and `b` (`src/ProbeLJ178A.agda:166-167`).
The two applications change from `ik a₀ b₀` to `ik a₀ b₀ a₀K b₀K`
(`:190`) and from `pk a₀ b₀` to `pk a₀ b₀ a₀K b₀K` (`:210`).

The choice is justified by the mathematics the brief names: Devlin's
Skolem hull is closed under ordered pairs for arguments already IN the
hull (`_build/literature/dev2.txt:1907-1914`, Claim 1), and the KFacts
`innerK`/`innerPairK`/`pairK` are exactly the L-side readings of that
closure. The conclusion of each guarded fact is unchanged; only the
hypotheses are bounded, so the row's conclusion is not weakened.

## 2. THE ROW PROOF, RE-CHECKED

The probe `src/ProbeLJ178A.agda` contains the guarded binary shape
frame (`BinaryShape'`, `:107-216`) and the guarded row (`MemAgree'`,
`:223-315`), copied from the master at
`src/L/Condensation.lagda.md:2608-2680` and `:4117-4210`. The diff
shape is three edits and nothing else:

1. The two fact types gain the two membership premises.
2. `BinaryShape'.in'` gains the two witnesses as parameters.
3. `back`'s call passes `aK bK` from `codesK`.

`BinaryShape'.out` and `MemAgree'.out` are byte-identical to the
master's text. The probe checks GREEN:

```text
first successful check: 6.08 s wall, 4.98 s user, exit 0
re-check:               2.76 s wall, 1.55 s user, exit 0
load average:           28.08 to 49.03 (4 users), not quiet
```

One Agda process per run, sequential, at the C-12 cap
`GHCRTS="-A64m -I0 -M8g"`. No master was edited, so no master
re-check was needed and none was run.

## 3. THE DD4 ANSWER UNDER D-29

**The conditional form is still generic in the slots.** Both guarded
facts quantify over `S` and state every membership at the row's own
`K`-slot (`lookup K γ`); `BinaryShape'.in'` states its two witnesses
at the frame's own `a₀`/`b₀` environment positions and the frame's
`K`-slot. No concrete carrier, set body, or stage presentation enters
either type. The KFacts fields can take the same guarded shape
(`carrierK` already does), so the J tower inherits the repair rather
than the defect.

Under D-29 the fix propagates at the same rate the defect did: the
closure facts live in the shared frame (`BinaryShape`), the defect
reached every binary row through the one frame, and the guarded
`BinaryShape'.in'` signature is the one place that changes to repair
every binary row that calls it. The premises flow from each row's own
site facts, which are already in the row telescope. This dispatch
machine-checked the Mem row only, per the brief; the other rows are
untouched.

## 4. NEGATIVES AND THEIR STATUS

1. "The row proof does not survive conditional facts": **MEASURED
   FALSE**. The guarded `MemAgree'` checks green at
   `src/ProbeLJ178A.agda:223-315`. This negative would have set the
   verdict; it did not.
2. "The new premises cannot be supplied at the point of use":
   **MEASURED FALSE**. `aK bK` are bound from `codesK` at
   `src/L/Condensation.lagda.md:4189` and typecheck at the guarded
   call (`src/ProbeLJ178A.agda:301-303`).
3. "The forward direction depends on the closure facts": **MEASURED
   FALSE**. `out` never mentions `innerK` or `pairK`; its text is
   byte-identical in the probe.
4. "The guarded forms are themselves uninhabitable": **NOT CLAIMED**.
   A guarded closure fact is satisfiable at a hull-shaped site
   (INFERRED from the literature reading); constructing such a site is
   the project's own business, not this dispatch's. No verdict rests
   on it.

## 5. ARCHIVE USED

- `_build/lj-1.77-report.md`, read WHOLE. TOOK the machine-checked
  refutation, the `carrierK`-as-model note, and the blast-radius list.
- `src/ProbeLJ177A.agda`, read WHOLE. TOOK the probe import pattern
  (the `AbsL` open that supplies `_^_` and `_⊨_`) and the C-12
  invocation.
- `_build/diag-twelve-row-math.md` section 4, read WHOLE (`:252-370`).
  TOOK the conditional-form recipe (section 3, `:237-241`): the facts
  must be hull-relativized, and the row proofs re-threaded with the
  guards. Confirmed here on the Mem row.
- `_build/lj-1.62-report.md` sections 2 and 3. TOOK the KFacts
  content-class history (the record bundle at
  `src/L/Condensation.lagda.md:5675`).
- `src/V/Hierarchy.lagda.md:130-160`. TOOK `regularityV` (`:139`) and
  `∈-irrefl` (`:155`), the refuting tools the guard avoids.
- `dev/LESSONS.md`: C-38 as extended today (`:3427-3465`), C-35
  (`:3200-3242`), D-29 (`:3242-3284`), D-30, read WHOLE. TOOK the
  discharge standard, the shared-layer propagation law, and the
  price-what-the-consumer-needs rule.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 6. LITERATURE USED

Yes: Devlin's hull is closed under ordered pairs for arguments already
in the hull (`_build/literature/dev2.txt:1907-1914`, Claim 1), which
is exactly the conditional shape this probe checks.

## 7. GATES

- `scripts/check-fences.py --check`: clean, 87 masters (run threshold
  3).
- `scripts/lint-agda.py --check src/ProbeLJ178A.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.78-report.md
  src/ProbeLJ178A.agda`: exit 0.
- No master was edited. The tree is byte-identical to the start
  (`b540478`, clean): `git status --short` is empty, and the only
  additions are this report and the probe, both gitignored by design
  (`_build/` at `.gitignore:2`, `src/Probe*.agda` at `.gitignore:22`).
- No `make check`. No commit, no push.
