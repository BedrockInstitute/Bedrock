# LJ-1.114: thread the truncation from StageCardinal to Devlin55

tier: codex (default)

## STATUS

ABORTED AT THE WALL. The threading does NOT land. `L.StageCardinal.Upper.
LimitStep` cannot carry the truncation: with the per-step induction
hypothesis truncated, the honest injection `⟪ Lset α ⟫ ↪ ⟪ α ⟫` cannot be
constructed, because the count of a formula's constants through the
branch injection is not injective across two independently chosen honest
injections. The deciding refusal is measured at line 412 of the threaded
edit of `src/L/StageCardinal.lagda.md` (`g₂' != g₁`, 2.49 s, load 4.98 /
4.31 / 4.40; the master was then reverted to HEAD), and the mathematical
fact behind it is measured by
`src/ProbeLJ1114A.agda`, GREEN: the tuple code `tuple-g g k cs` is
injective per injection but not across injections (`collision : refl` at
`:89-90`, `tuples-differ` at `:92-94`). All master changes were reverted;
no master is touched. `Devlin55` cannot be entered. This is a
route-level finding.

## 0. THE VERDICT

**NO, the threading does not land, measured.** The plan of `[LJ-1.111]`
section 4 restates `LimitStep` "in full; the per-step IH becomes
truncated and must be eliminated at every use". The restatement was
attempted in the master. It compiles as far as the counting machinery
(`cnt-g`, `cnt-g-inj`, `cnt-g-stable`, `class-pred` with the honest
injection carried in the witness, `nonempty`, `h`) and refuses at the
injectivity step of `h-inj`: the equality of two codes does not imply the
equality of the two formulas, because each class witness carries an
honest injection extracted from its OWN truncation elimination, and the
count is injective per injection only. Agda rejects the term with
`g₂' != g₁` at line 412 of the threaded edit (before the revert).

The probe `src/ProbeLJ1114A.agda` isolates the mathematical fact. With
`K = Fin 2`, `α = ω`, and two honest injections `g₁`, `g₂` of `K` into
`⟪ ω ⟫` that swap the two elements, the `Bound`-style tuple code satisfies

```agda
collision : tuple-g inj₁ 2 (a ∷ a ∷ []) ≡ tuple-g inj₂ 2 (b ∷ b ∷ [])
collision = refl                                -- src/ProbeLJ1114A.agda:89-90
```

while the tuples differ (`tuples-differ : (a ∷ a ∷ []) ≡ (b ∷ b ∷ [])
→ Empty.⊥`, `:92-94`). The code value therefore does not determine the
formula across independently chosen honest injections, and the
injectivity step of `LimitStep.h-inj` cannot be written. The per-member
honest injection itself is also not extractable from the per-member
truncation: that is the measured wall of `[LJ-1.111]` probe B
(`src/ProbeLJ1111B.agda:46`, `Type _ℓ_8 !=< x ≡ y`), reproduced here at
the count-injectivity step.

**The theorem would have to state the honest injection instead.** The
honest `stage-card-upper : (α : S) → IsOrd α → (α ∉ ω) → ⟪ Lset α ⟫ ↪
⟪ α ⟫` at every infinite α requires the honest per-member injections in
the ∈-induction, which requires the honest `sq δ` at every member, the
exact object `[LJ-1.107]` measured unconstructible at non-initial
ordinals. A truncated `∥ stage-card-upper ∥₁` cannot be built from the
truncated data. The final theorem's statement does not change in this
dispatch, because nothing lands; but a working threading would have
required `Upper`'s output to be `∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁` while its
construction needs honest per-member injections, and the two cannot both
hold. That is the route-level finding.

## 1. THE THREADING: what was tried, where it refused

The brief's route, followed literally:

1. `L.StageCardinal`'s parameter changed from the honest `sq` to the
   truncated `sqT : (α : S) → (α ∉ ω) → ∥ pairing-type α ∥₁`
   (`src/L/StageCardinal.lagda.md:15-17`), with `∥_∥₁` imported before
   the module header.
2. `Bound` kept honest (`:62-65`): its consumer `LimitStep` instantiates
   it with the honest `sqα` from a single elimination of `sqT` at the
   top of `limit-stepT` (the output target `∥ inj ∥₁` is a proposition).
3. `LimitStep` restated in full: `sqα` as a module parameter, `ih`
   truncated per member, the count stated on the honest injection
   (`cnt-g m g φ`), `class-pred`/`nonempty`/`h`/`h-inj` with the honest
   per-witness data carried inside the truncated witness, and the
   truncations eliminated only at the proposition points.
4. `Upper.P` truncated (`... → ∥ Σ[ f ] inj ∥₁`), `branch` per member
   truncated, `limit-stepT` truncated, `stage-card-upper` truncated.

The wall is step 3's `h-inj`, at line 412 of the threaded edit. The
proof of injectivity of the least-code function compares two witnesses
of the code class. Each witness carries its own honest branch injection,
extracted from its own elimination of `ih m` (or `ih m'`). The
pairing-injectivity splits the code equality into `m₁ ≡ m₂` and an
equality of two count values computed under DIFFERENT honest injections.
Count injectivity (`cnt-g-inj m₁ g₁`) requires the same injection on both
sides; transporting one witness's injection to the other member gives
`g₂' != g₁` and Agda refuses. There is no term connecting them: the
probe measures that two distinct tuples can collide across two honest
injections.

The refusing fragment, exactly as edited:

```agda
          ecount' : cnt-g m₁ g₁ φ₁
                  ≡ cnt-g m₁ (subst (λ w → ⟪ Lset (⟪ α ⟫↪ w) ⟫ ↪ ⟪ α ⟫)
                               (sym qm) g₂) (subst F (sym qm) φ₂)
          ecount' = ecount ∙ sym (cnt-g-stable m₁ m₂ (sym qm) g₂ φ₂)
          eφ : φ₁ ≡ subst F (sym qm) φ₂
          eφ = cnt-g-inj m₁ g₁ φ₁ (subst F (sym qm) φ₂) ecount'
```

Agda's refusal, verbatim: "when checking that the expression ecount'
has type cnt-g m₁ g₁ φ₁ ≡ cnt-g m₁ g₁ (subst F (λ i → qm (~ i)) φ₂)",
with the transported `g₂` normalizing to a term that is not `g₁`.

Every alternative placement of the elimination was considered and is
closed:

- Eliminating `sqT` inside `Upper.step` with `P α` honest fails: `P α` is
  data, so there is no proposition point at the step.
- Keeping `P α` honest and eliminating `sqT` nowhere fails: `LimitStep`
  needs the honest pairing at every α, including non-initial ones, where
  the honest `sq α` is unconstructible (`[LJ-1.107]`, measured).
- Restating `branch` to produce one honest family per step fails: the
  family is data, and the infinite-member branches consume the truncated
  `IH δ`; an honest injection is not extractable from the truncation
  (`[LJ-1.111B]`, measured).
- Making the per-member data honest by any `leastOf` extraction fails:
  extracting an honest injection from `∥ K ↪ ⟪ α ⟫ ∥₁` is the same
  refusal (`Type !=< x ≡ y`), and a per-point extraction has the same
  cross-injection collision that probe A measures.

So the truncation cannot pass through the ∈-induction of `Upper`. The
Devlin55 side of the plan is not the blocker: if `Upper` delivered
`∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁`, the assembly could eliminate it at the two
proposition points `β∈κ` and `x∈Lκ` (`src/L/BoundedSubset.lagda.md:1594`,
`:1605`), with `CodeCount`, `CodeSelect`, `CanonCode`, `πX↪α`, `β↪α`
built inside the branches from the single honest `sqα` and the single
honest `stage-card-upper`, one elimination, consistent data, exactly the
`[LJ-1.111]` `NonInitialT` pattern. That half is analyzed, **INFERRED**
(nothing machine-checked it, because the prerequisite master change does
not compile).

## 2. THE DIFF, THE SECONDS, THE SPREAD

No master diff survives. `src/L/StageCardinal.lagda.md` was edited and
reverted to HEAD exactly (`git diff` empty, verified); `src/L/
BoundedSubset.lagda.md` was never edited. The probe `src/ProbeLJ1114A.
agda` is new, untracked and ignored (`git check-ignore` confirms).

Timing, ONE agda process at a time, `GHCRTS="-A64m -I0 -M8g"`, import
cache warm (the "own content cold" convention of `[LJ-1.106]` section 8),
machine not quiet, 4 users:

| target | state | real s | user s | load 1/5/15 |
|---|---|---:|---:|---|
| `StageCardinal` | HEAD before | 1.65, 1.71, 1.76 | 0.83-0.87 | 3.03/3.85/4.33 to 3.57/3.92/4.35 |
| `StageCardinal` | threaded, at the wall | refused at 2.31, 2.49 | 1.49-1.65 | 4.98/4.31/4.40 |
| `StageCardinal` | reverted after | 1.71 | 0.84 | ~3.5 |
| `BoundedSubset` | HEAD before | 2.20, 3.28 | 2.08-2.23 | 3.57/3.92/4.35 |
| `ProbeLJ1114A` | new, GREEN | 2.35, 2.43, 2.46 | 1.41-1.54 | 3.72/4.27/4.34 to 5.43/4.61/4.45 |

Run-to-run spread on this machine and cache state is about 0.1 s on
`StageCardinal` (1.65 to 1.76) and about 1.1 s on `BoundedSubset` (2.20
to 3.28), so any delta below about 1 s on `BoundedSubset` and 0.2 s on
`StageCardinal` would be noise. No delta is claimed: the threaded
`StageCardinal` never completed. The earlier record of "about 15 s" for
`BoundedSubset` (`[LJ-1.111]` gates) was measured under a colder cache;
this dispatch's numbers are the warm-cache convention and are reported
with that basis.

The wall's seconds: the threaded `StageCardinal` refused at 2.49 s real
(user 1.65 s) at load 4.98/4.31/4.40. That is the wall's seconds, not a
completion.

## 3. THE C-40 SECTION: THE CONSUMERS

`git grep -l "StageCardinal\|BoundedSubset" src/` names three files:
`src/Everything.lagda.md`, `src/L/BoundedSubset.lagda.md`,
`src/L/StageCardinal.lagda.md`.

- `src/L/StageCardinal.lagda.md` (the changed master): checked GREEN at
  HEAD before the edit (1.65-1.76 s), RED at the wall during the edit
  (`:412`), GREEN after the revert (1.71 s).
- `src/L/BoundedSubset.lagda.md` (imports and instantiates
  `L.StageCardinal` at `:881`, `:1368`): checked GREEN at HEAD (2.20 and
  3.28 s). It was never re-checked against the threaded master, because
  the threaded master never compiled; C-40's check is therefore not run
  against a broken intermediate, and the reverted tree is the green base.
- `src/Everything.lagda.md` (imports both at `:369`, `:374`): not
  typechecked; no master change survives, so `make check`'s result on the
  base applies. The brief's rule against `make check` was obeyed.

Result: no consumer is broken, because no master change survives. The
consumers were named and the base was verified.

## 4. THEOREM STATEMENTS

No theorem's final statement changed. `Devlin55.theorem` is untouched
(`src/L/BoundedSubset.lagda.md:1621`). The only candidate conclusion that
would have to change is inside `Upper`: its per-α output would have to
remain the honest injection (data) or be built from honest per-member
injections, either of which requires the honest `sq` that the goal
removes. State the negative as the brief demands: **a working threading
would force `stage-card-upper`'s output to stay data or force the honest
per-member injections to be supplied, and neither is available; the
final theorem's statement itself does not change because nothing lands.**

## 5. THE C-39 SECTION

No brief prohibition blocked a route. `src/L/Condensation*` was never
touched and never needed: the abort is a mathematical wall, not a
prohibition. The route the abort closes is the brief's own GOAL route
(truncate `sq` at both parameters and thread down); the door behind the
wall is the honest `sq` or the honest per-member injections, i.e. the
`[LJ-1.107]` wall at every member stage. A threading that kept
`LimitStep`'s `ih` honest would still need the honest `sq δ` at every
infinite member, which is exactly the object measured unconstructible.

## 6. THE NEGATIVES AND THEIR STATUS

1. "The threading lands; `∥ sq α ∥₁` reaches Devlin55's proposition
   points": **MEASURED FALSE** at the wall. The restatement of
   `LimitStep` refuses at line 412 of the threaded edit (`g₂' != g₁`),
   2.49 s.
2. "The count of a formula's constants is injective across two honest
   injections of the same carrier": **MEASURED FALSE**.
   `src/ProbeLJ1114A.agda:89-90` (`collision = refl`) and `:92-94`
   (`tuples-differ`), GREEN.
3. "An honest injection is extractable from a per-member truncation":
   **MEASURED FALSE** by the archive's `[LJ-1.111B]` refusal
   (`src/ProbeLJ1111B.agda:46`), which this dispatch re-encounters at
   the count-injectivity step.
4. "Some other construction of `∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁` from the
   truncated data exists": **INFERRED** (a machine cannot certify
   nonexistence). The structural argument: every honest injection from
   the least-code machinery needs per-member consistent honest data; the
   truncations cannot supply it (2 and 3); no alternative route in the
   tree supplies it either (`[LJ-1.107]` section 5, the archive's
   measured route analysis).
5. "The Devlin55-side assembly could eliminate at `β∈κ`/`x∈Lκ` if
   `Upper` delivered the truncation": **INFERRED** (analyzed, not
   machine-checked; the prerequisite master change does not compile).
6. "The 350-line figure": the module extents were **MEASURED**; the
   lift pattern (5 to 8 lines per module) was **INFERRED**, and the
   load-bearing `LimitStep` row (111 lines, "restated in full") is now
   known to be un-restatable, so the figure is not a price.

## 7. DD4

The square law remains ordinal-and-injection mathematics, never
definability: the attempted threading stays inside `StageCardinal` and
`BoundedSubset`, both tower-generic. The truncated parameter does not
change that classification. The J half is **INFERRED** (no J tower in
this tree): it would inherit the changed signatures unchanged, but it
would also inherit the wall: a J consumer of the threaded `Upper` would
face the same per-member truncation problem. Nothing in this dispatch
adds shared code: the probe is throwaway evidence, and the master is
reverted.

## 8. THE COST QUESTION

No delta is claimed (section 2). The wall costs: the threaded
`StageCardinal` refused at 2.49 s at load 4.98/4.31/4.40; the probe
checks GREEN at 2.35-2.46 s at load 3.72-5.43. The widest term of the
planned threading, `LimitStep`'s restatement, is where the wall sits; it
is not a seconds term but an impossibility. The run-to-run spread is
reported in section 2.

## 9. ARCHIVE USED

- `_build/lj-1.111-report.md`, read WHOLE. TOOK the two elimination
  points (`β∈κ`, `x∈Lκ`), the per-module extent table, the `LimitStep`
  "restated in full" row, and the `NonInitialT` single-elimination
  pattern.
- `src/ProbeLJ1111A.agda`, read WHOLE. TOOK `NonInitialT`'s pattern:
  two truncations eliminated once each at the top of a proposition, then
  honest data used consistently.
- `src/ProbeLJ1111B.agda`, read WHOLE. TOOK the measured extraction
  refusal (`Type _ℓ_8 !=< x ≡ y`, `:46`), the per-member version of the
  wall.
- `_build/lj-1.107-report.md`, read WHOLE. TOOK the honest-injection
  wall and its route analysis.
- `_build/lj-1.106-report.md` and `src/ProbeLJ1106A.agda`, read WHOLE.
  TOOK `NumeralPresentation.pairω`/`pairω-inj` and `numeralω`,
  `numeralω-inj`, reused by probe A.
- `src/L/StageCardinal.lagda.md`, read WHOLE. TOOK the `sq` parameter
  (`:15`), `Bound` (`:62-180`), `LimitStep` (`:275-414`), `Upper`
  (`:546-559`); the threaded edit and its refusal at `:412`.
- `src/L/BoundedSubset.lagda.md`, read `:1361-1626` (Devlin55 whole).
  TOOK `β∈κ` (`:1594-1603`), `x∈Lκ` (`:1605-1611`), `theorem`
  (`:1621`), and the assembly's data chain.
- `src/L/Ordinal/SquareLaw.lagda.md`, read `:938-964`. TOOK
  `via-col-square`/`via-col-truncated`.
- `dev/LESSONS.md`, read WHOLE C-40 (`:3602`), C-39 (`:3521`), C-38
  (`:3427`), P-x (`:3564`), C-35 (`:3200`), C-36 (`:3284`), D-8
  (`:1377`), D-30 (`:3332`), P-l (`:2305`), and the `--for build` and
  `--for rewrite` bundles via `scripts/rules.py`.

## 10. LITERATURE USED

Banked. `[LJ-1.111]` settled how Devlin uses the square law
(`_build/lj-1.111-report.md` section 12); nothing new spent.

## 11. GATES

`src/ProbeLJ1114A.agda`: GREEN at the C-12 cap, one process at a time,
2.35-2.46 s at load 3.72-5.43. `scripts/check-fences.py --check`: clean,
92 masters. `scripts/lint-prose.py --check`: exit 0 on the probe and
this report. `scripts/lint-agda.py --check`: exit 0 on the probe.
`scripts/check-unbound-hyp.py src/ProbeLJ1114A.agda`: clean, 1 file,
exit 0. Zero hits for `postulate`, `TERMINATING`, holes in the probe.
`scripts/ledger.py --brief`: standing 28,425 lines over 85 masters,
measured from HEAD. `make check` not run (forbidden). No master touched:
`git diff` empty, `git status` shows only the ignored probe. No process
left alive; every check returned. No commit, no push.
