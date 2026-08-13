# LJ-1.107: sq at every infinite ordinal

tier: codex (default)

## STATUS

PARTIAL. The chain closes at `ω` and at the initial ordinals; it does
not close at the non-initial ordinals, because the honest injection
`α ↪ |α|` that the brief's step 5 takes "by the bijection" is not
constructible from the delivered least-of data. The probe is
`src/ProbeLJ1107A.agda`, GREEN at the C-12 cap, one process, 582
non-blank lines. No master was touched. No commit, no push.

## 0. THE VERDICT

**NO. `(α : S) → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → SQ.sq α` does not close from
the delivered machinery as the brief routes it.** The chain closes at
`ω` and at every ordinal with `|α| = α` (the initial case); it does not
close at ordinals with `|α| ∈ α` (the non-initial case). The term that
cannot be written is the honest injection

`(α : S) (oα : IsOrd α) (ω∈α : ⟨ ω ∈ˢ α ⟩) (LC : LeastCard α oα)
 → ⟨ LC.κ ∈ˢ α ⟩ → ⟪ α ⟫ ↪ ⟪ LC.κ ⟫`

That is the brief's step 5 datum "`α ↪ |α|` by the bijection". The least-of
search returns `|α|` honestly but its bijection witness is the
truncation `∥ ⟪ |α| ⟫ ≃ ⟪ α ⟫ ∥₁` (`LeastCard.κ-eqα`,
`src/ProbeLJ1107A.agda:247-248`), and the truncation cannot eliminate into
the injection type: `⟪ α ⟫ ↪ ⟪ |α| ⟫` is not a proposition, so
`PT.rec` refuses (the machine-checked attempt fails with
`Type ℓ !=< x ≡ y`; the same wall is recorded in the archived route at
`_build/l3.32-t31-report.md` section 3 and section 5). The chain is
assembled conditionally: `Chain.theorem`
(`src/ProbeLJ1107A.agda:663-666`) checks GREEN given the injection as a
module parameter, and everything short of the injection closes
outright.

Whole-file cold check: **about 117 s** at load 3.57 / 4.33 / 4.65
(four users, machine NOT quiet), one process, C-12 cap. Warm re-check:
2.25 s.

## 1. THE PER-STEP TABLE

The probe is `src/ProbeLJ1107A.agda`; the marginal seconds are prefix
bisection (import cache warm, own content cold, one process each,
`GHCRTS="-A64m -I0 -M8g"`), the same basis as the [LJ-1.106] table.
Line counts are non-blank in-fence.

| step | content | lines | cold s | load (1/5/15) | rode |
|---|---|---:|---:|---|---|
| 1 | `CSB`, Cantor-Bernstein for h-sets | 97 (+81 header/imports) | 2.03 | 3.90/4.65/4.90 | LEM (standing parameter); the cubical Embedding fiber facts |
| 2 | `LeastCard`, least-of `|α|` with leastness | 38 | 91.98 | 3.75/4.61/4.88 | delivered `OrdSWO`, `leastOf`, `suc-ord`, `mem-ord`; the [LJ-1.117] `Card` shape |
| 3 | `ShiftAbs` + `Shiftω`, successor absorption | 103 | 2.83 | 4.47/4.39/4.73 | the archived [LJ-1.117] `Shift` shape; `natOrder`, `FiniteBase.ω-mem→numeral` |
| 4 | `FiniteAtω`, `Incl` | 42 | 0 to 1 (within noise; p4 measured 0.30 s under p3) | 5.04/4.77/4.84 | `FiniteBase` counting (`toFin`/`fromFin`/`factor`), the `AbstractChase` pigeonhole |
| 5 | `InitialCase` + `NonInitial` | 142 | 1.63 | 3.78/4.54/4.75 | `via-col-square`, `CSB`, `ShiftAbs`, the leastness, `ord-tri` |
| 6 | `Chain`, the `∈`-induction | 33 | 18.62 | 3.57/4.33/4.65 | delivered `∈-induction`; the step instantiates `LeastCard`, `InitialCase`, `NonInitial` at the abstract ordinal |
| whole | the probe | 582 | about 117 | 3.57/4.33/4.65 | above |

The dominant term is step 2: the least-of over the well-order on the
successor's presentation (`⟪ sucV α ⟫` normalizes the union structure,
the P-m instantiation class). Steps 3 to 5 are cheap; step 6 (the
`∈`-induction step's instantiation of the `Init` type at the abstract
ordinal) is the second term at 18.6 s.

## 2. WHAT CLOSES, AND WHAT DOES NOT

**Closes outright (each checks GREEN):**

- `sq ω`: `Chain.sqω` (`src/ProbeLJ1107A.agda:636-637`), the delivered
  `NumeralPresentation.pairω`/`pairω-inj` (`src/ProbeLJ1106A.agda:127-137`).
- The least cardinal `|α|`: `LeastCard` (`:217-266`), `|α|`, `oκ`,
  the truncated witness `κ-eqα`, and the leastness `κ-min-at`
  (`:259-266`).
- The initial case `|α| = α`: `InitialCase` (`:464-537`). `Init α`
  closes: `IsOrd` and `ω ∈ α` are the hypotheses; the successor closure
  (`succ-closure`, `:493-533`) refutes `sucV γ = α` by the shift
  absorption (`ShiftAbs`/`Shiftω` + the inclusion + CSB give
  `γ ≃ sucV γ`) and the leastness; the square clause (`noinj²`,
  `:469-491`) composes the injection `α ↪ β×β` with the induction
  hypothesis `sq β`, then CSB and the leastness refute `β < |α|`.
  `sq α = SQ.via-col-square α initα` (`:536-537`).
- The `∈`-induction frame: `Chain` (`:630-666`), with the case split
  `ω = α` (the pairing), `α ∈ ω` (refuted), and the least cardinal's
  split `|α| = α` (initial case) versus `|α| ∈ α` (non-initial case).
- The non-initial case **conditional on the honest injection**:
  `NonInitial` (`:549-618`), including `|α| ∉ ω` from the truncated
  witness plus the finite exclusion at `ω` (`:556-591`), and `sq α` by
  composition through `sq |α|` (`pair`/`pair-inj`, `:601-616`).

**Does not close:** the honest injection `α ↪ |α|` for the non-initial
branch. `Chain.theorem` is stated with the injection as a parameter;
without it, the `split (inl κ∈α)` branch has no term. The brief's step
5 says "`α ↪ |α|` by the bijection", but the bijection's only witness
is the truncation `κ-eqα`; the extraction attempt

```agda
attempt : (α κ : S) → ∥ ⟪ α ⟫ ≃ ⟪ κ ⟫ ∥₁ → ⟪ α ⟫ ↪ ⟪ κ ⟫
attempt α κ = PT.rec (λ x y → x ≡ y) (λ e → equivFun e , inj e)
```

is rejected (`Type ℓ !=< x ≡ y`: the isProp requirement of `PT.rec`
cannot be met, because the injection type is not a proposition), and
CSB needs the honest injection as its second input, exactly the
missing object. This is the wall the old route recorded at
`_build/l3.32-t31-report.md` section 3 ("its equinumerosity witness is
the truncation ... no canonical bijection exists to reconstruct an
honest `α ≅ κ` from it") and section 5 ("CSB requires a second honest
injection `α ↪ κ`, which is exactly the missing object").

## 3. THE STEP THE BRIEF DID NOT ANTICIPATE

The square clause of `Init |α|` needs Cantor-Bernstein. From
`f : |α| ↪ β×β` and `sq β` (the induction hypothesis) one gets
`h : |α| ↪ β`; with the inclusion `β ↪ |α|` (from `β ∈ |α|`), the
leastness refutes `β < |α|` only through an equivalence `|α| ≃ β`,
which is exactly the Cantor-Bernstein step. `CSB` (`:99-207`) is
written generically for h-sets with LEM (the standing module
parameter), about 97 lines; it is LEM-priced, not choice. The same
composition is named in the old route's records
(`_build/l3.32-t31-report.md` section 5, "the Cantor-Bernstein
composition T31 recorded as standard-but-blocked").

## 4. CHOICE

No axiom of choice is used anywhere. **MEASURED by the probe's
imports and types**: the new content uses LEM (the standing module
parameter) in `leastOf`, in `CSB`'s case splits, in `ShiftAbs`'s
membership/equality decisions, and in the ordinal trichotomy; no
choice principle appears. The chain stays choice-free.

## 5. THE C-39 SECTION

Two routes are blocked, and both doors are reported.

1. **The brief's step 5 itself is the blocked route.** The route
   "`α ↪ |α|` by the bijection" cannot be written: the bijection's
   least-of witness is truncated, and no canonical bijection exists to
   recover (the old route measured the same). This is a block in the
   brief's mathematics, not a prohibition; the door is the honest
   injection, which needs either a data-carrying least (not available:
   `leastOf`'s predicate must be a proposition) or a canonical
   bijection (does not exist, e.g. `ω ≃ ω + 1` admits many). The
   archive records the same door at `_build/l3.32-t31-report.md`
   section 3.
2. **The natural import of `L.BoundedSubset` (for `Devlin55`'s exact
   telescope) is blocked by the sibling's working tree**, exactly as in
   [LJ-1.106]: `L.BoundedSubset` imports `L.Condensation`
   (`src/L/BoundedSubset.lagda.md:29`), which a sibling is editing.
   The door: the probe states the consumer's shape
   `(α : S) → α ∉ ω → SQ.sq α` locally (`Chain.theorem`), and the
   master's shape is reproduced in the report rather than imported.

## 6. THE NEGATIVES AND THEIR STATUS

1. "`sq ω` comes from the delivered pairing": **MEASURED TRUE**.
   `Chain.sqω` checks.
2. "The least ordinal in bijection with `α` is delivered by
   `leastOf` over `⟪ sucV α ⟫`": **MEASURED TRUE**. `LeastCard`
   checks; the witness is the truncation, and the leastness is data.
3. "`Init |α|` closes for the initial case": **MEASURED TRUE**.
   `InitialCase.initα` checks, with CSB and the shift absorption as
   the new content.
4. "The square clause follows by minimality of `|α|` plus `sq β'`":
   **MEASURED TRUE given CSB**. The composition `|α| ↪ β`, the
   inclusion, CSB, and `κ-min-at` check (`noinj²`,
   `src/ProbeLJ1107A.agda:469-491`).
5. "`α ↪ |α|` by the bijection" (brief step 5): **MEASURED FALSE as
   stated**. The bijection's least-of witness is the truncation; the
   extraction attempt is rejected, and CSB needs the honest injection
   as its second input. The same wall was measured in the old route
   (`_build/l3.32-t31-report.md` section 3). This is the deciding
   negative, and it is MEASURED at the level of the machine-checked
   refusal and the archive's recorded measurement.
6. "The whole chain closes at every infinite ordinal":
   **MEASURED FALSE for the non-initial branch**; the initial branch
   and the `ω` branch close. The theorem is stated conditional on the
   injection (`Chain.theorem`), and every other branch checks.
7. "The route is choice-free": **MEASURED TRUE** for the content that
   closes (no choice axiom in the imports); the un-writable injection
   is the blocker, not a choice principle.
8. "`Init ω` is false, so `sq ω` must come from the pairing":
   **MEASURED TRUE** by reading (`Init` demands `ω ∈ ω`); the pairing
   branch checks.

## 7. DD4

**The chain stays generic, MEASURED.** The probe's mathematics names
only the ambient universe `S`, the presentations, injections, the
`SWO` record, `leastOf`, `ω`, `sucV`, `#_`, `IsOrd`, and CSB for
generic h-sets. No tower object appears in any type: no `Def`, no
`Rud`, no `Lset`, no `Condensation`. `CSB`, `ShiftAbs`, `LeastCard`
and `InitialCase` are written generic over their carriers and
instantiated once. The J half is **INFERRED** (no J tower exists in
this tree); the ambient half is **MEASURED by the probe's own types**.
Neither piece names a tower object.

## 8. THE COST QUESTION

The brief priced the whole chain at 500 lines (band 350 to 750),
INFERRED by [LJ-1.101]. The measured replacement: the probe is 582
non-blank lines and checks cold at about 117 s at load 3.57 / 4.33 /
4.65. The widest term is `LeastCard` (about 92 s of the 117 s), the
least-of over the successor's presentation; the second is the chain's
instantiation (18.6 s). The 500-line figure is replaced by this
measurement; the chain itself does not close, so the price is for the
partial chain, not for the theorem.

## 9. ARCHIVE USED

- `_build/lj-1.106-report.md`, read WHOLE. TOOK the delivered pieces
  (`NumeralPresentation`, `PullbackAt`, `SuccClosure`), the prefix
  bisection basis, and the C-39 door at `L.BoundedSubset`.
- `src/ProbeLJ1106A.agda`, read WHOLE. TOOK `NumeralPresentation`
  (`:90-137`), imported unchanged.
- `_build/lj-1.101-report.md`, read WHOLE (section 2.2 in detail).
  TOOK the route, whose step 5 is the wall reported here.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, read WHOLE.
  TOOK `OrdSWO` (`:80-140`), `isSet⟪⟫`, `member`/`fiber`/`↪-inj`
  usage, the Hartogs self-membership proof (the contrast: `cardκ`
  needs no CSB; the general initial ordinal does).
- `_build/lj-1.92-report.md` and `src/ProbeLJ192A.agda`, read WHOLE.
  TOOK the order-type block's shape and its measured rate.
- `src/L/Ordinal/SquareLaw.lagda.md`, read `:539-542`, `:685-701`,
  `:703-964`. TOOK `Init`, `sq`, `via-col-square`, `FiniteBase`,
  `AbstractChase.NoInj`, and the header's statement that the
  least-of transfer is not built.
- `src/L/BoundedSubset.lagda.md`, read `:1361-1368`. TOOK the exact
  consumer shape.
- `dev/LESSONS.md`, read WHOLE C-38 (`:3427`), C-39 (`:3513`), C-35
  (`:3200`), C-36 (`:3284`), D-8 (`:1377`), D-30 (`:3332`), P-l
  (`:2305`), P-m (`:2460`), and the `--for build` and `--for probe`
  bundles via `scripts/rules.py`.
- `_build/l3.32-t21-report.md`, `_build/l3.32-t31-report.md`,
  `_build/l3.32-t43-report.md`, `_build/l3.32-t47-report.md`,
  `_build/l3.32-t81-report.md`, read WHOLE. TOOK the documented
  extraction wall (T31 section 3 and section 5), the CSB survey
  (T81, "keep ours", 145 lines at the retired `L.Cardinal`), and the
  truncated-transfer analysis (T43 section 2, proposition-valued
  consumers). These are the records that the current route's step 5
  re-encounters.
- `src/ProbeLJ117SquareLaw.agda`, read WHOLE. TOOK the `Card` least
  shape (`:511-542`) and the `Shift` injection (`:543-640`), restated
  generically (`LeastCard`, `ShiftAbs`).

## 10. LITERATURE USED

Devlin's II.5 consumes 1.1(vii), "|L_α| = |α| for infinite α"
(`_build/literature/dev2.txt:200-222`; the digest at
`dev/literature/devlin-II5.md:155, 160-165`). He proves the square-law
fact in his Chapter 1 as standard cardinal arithmetic (the limit case
`Σ_{β<λ} |β| = |λ|` is the square law; `dev2.txt:203-205`) and cites
it in II.5; he does not prove it there. Two lines: **Devlin cites
1.1(vii); the square law is proved in his Chapter 1 as standard
cardinal arithmetic, not inside II.5.** The old route's records name
the same classical source (`_build/l3.32-t43-report.md` section 1,
Jech 3.5).

## 11. MASTERS

None touched. `git status` shows only the sibling's in-progress
`src/L/Condensation/` files; the probe is untracked and ignored. HEAD
moved during the dispatch (`4930b72` to `3a16f2e`, the orchestrator's
commits), one of which landed a `.gitignore` change that ignores all
`src/**/*.agda` (added by another actor mid-dispatch, citing my
scratch file). No commit, no push.
One agda process at a time; no process left alive. `make check` not
run. DD23: no mathematical prose written. Linters: `lint-prose.py
--check` exit 0, `lint-agda.py --check` exit 0 on the probe and this
report; zero hits for `postulate`, `TERMINATING`, holes. Ledger:
standing 28,373 lines over 85 masters, measured from HEAD.
