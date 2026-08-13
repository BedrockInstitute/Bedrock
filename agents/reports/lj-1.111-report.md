# LJ-1.111: can Devlin55 take the TRUNCATED sq?

tier: codex (default)

## STATUS

COMPLETE. All three questions answered with machine checks. The
cheapest cure is NO, measured. The truncation-at-top route closes: the
truncated chain `(α : S) → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) →
∥ SQ.sq α ∥₁` checks GREEN without the honest injection. Feeding
Devlin55 needs the threading, priced at about 350 lines. No master was
touched. No commit, no push.

## 0. THE VERDICT

**NO, the least witness's uniqueness does not make the fiber a
proposition.** The extraction of the honest injection
`⟪ α ⟫ ↪ ⟪ κ ⟫` from the truncated `κ-eqα` is refused by the machine
with the exact wall `[LJ-1.107]` recorded
(`src/ProbeLJ1111B.agda:46`, error `Type _ℓ_8 !=< x ≡ y`), with the
leastness `κ-min-at` in scope. The leastness constrains the ordinal,
never the bijection type.

**But the truncation-at-top route closes.** The truncated theorem

```agda
TruncatedChain.theorem : (α : S) → IsOrd α
  → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ∥ SQ.sq α ∥₁
```

checks GREEN (`src/ProbeLJ1111A.agda:271-272`), without the honest
injection `α ↪ |α|`. The non-initial branch eliminates the delivered
truncated equivalence `κ-eqα` and the truncated induction hypothesis
into the proposition `∥ sq α ∥₁`, and transports the honest pairing of
`κ` through the honest equivalence. The initial branch uses the
delivered `via-col-truncated` at an `Init α` built with a truncated
induction hypothesis, whose square clause concludes `Empty.⊥` and so
absorbs the truncation.

**Devlin55 can take `∥ sq α ∥₁` only through the threading.** Every
type between `Bound`'s pairing and the conclusion is data. The
truncation can eliminate only at the proposition points `β∈κ` and
`x∈Lκ`. The threading is priced at about 350 non-blank in-fence lines.

Probe A (`src/ProbeLJ1111A.agda`, 250 non-blank lines): GREEN, one
process, C-12 cap. Full check about 20.9 s at load 3.09 / 4.03 / 4.24
(four users, machine NOT quiet); warm re-check 2.41 s at the same
load. Probe B (`src/ProbeLJ1111B.agda`, 40 non-blank lines): RED by
design, the refusal at 1.84 s at load 3.60 / 4.06 / 4.24.

## 1. THE CHEAPEST CURE (question 3): NO, measured

The brief asks whether the least-of search can return the equivalence
untruncated for an ordinal, because a least element of a well-order is
unique. The claim fails at the type level: uniqueness of the least
ORDINAL does not make the bijection type a proposition. The type
`⟪ κ ⟫ ≃ ⟪ α ⟫` at the least `κ` has many witnesses whenever `α` has
more than one element, which every infinite ordinal has. The archive
recorded the same example: `⟪ ω ⟫ ≃ ⟪ ω + 1 ⟫` admits the shift and
many others (`_build/l3.32-t31-report.md` section 3).

The machine-checked refusal is the deciding evidence. With the full
`LeastCard` data in scope, including `κ-min-at`, the extraction

```agda
attempt : ⟪ α ⟫ ↪ ⟪ κ ⟫
attempt = PT.rec (λ x y → x ≡ y)
  (λ e → (invEq e , λ x y p → sym (secEq e x) ∙ cong (equivFun e) p ∙ secEq e y))
  κ-eqα
```

is rejected at `src/ProbeLJ1111B.agda:46` with `Type _ℓ_8 !=< x ≡ y`.
`PT.rec` requires `isProp (⟪ α ⟫ ↪ ⟪ κ ⟫)`, and nothing in the
leastness supplies it, because `κ-min-at` (`src/ProbeLJ1107A.agda:
259-266`) refutes only STRICTLY SMALLER equinumerous ordinals and never
constrains two witnesses at `κ` itself. This reproduces `[LJ-1.107]`'s
measured refusal (`_build/lj-1.107-report.md` section 2) with the
leastness added, and the same wall in the retired route
(`_build/l3.32-t31-report.md` section 3 and section 5).

Status: **MEASURED FALSE** for the extraction. The general claim "the
equivalence type is not a proposition at the least cardinal" is
**INFERRED** (the archive's `ω ≃ ω + 1` example is classical, not
machine-checked here), but the deciding negative is the refusal, which
is measured.

## 2. THE TRUNCATION AT THE TOP: the route that closes, measured

The brief's GOAL says the truncation may belong at the top, because
the theorem's conclusion is a proposition. The machine confirms it,
with one correction: the tree delivers the truncated form only at
`Init α` (`via-col-truncated`, `src/L/Ordinal/SquareLaw.lagda.md:
963-964`), which is the initial case. The non-initial case is new
content, and it closes without the honest injection.

The truncated chain mirrors `[LJ-1.107]`'s `Chain`
(`src/ProbeLJ1107A.agda:630-666`) with the conclusion truncated:

1. `sqωT` at `ω`: `NumeralPresentation.pairω` and `pairω-inj`
   (`src/ProbeLJ1111A.agda:239-240`).
2. `InitialCaseT` (`:121-201`): `Init α` built from the same
   mathematics as `[LJ-1.107]`'s `InitialCase`
   (`src/ProbeLJ1107A.agda:464-537`), with the induction hypothesis
   truncated. The only consumer of the honest IH is the square clause
   `noinj²`, whose conclusion is `Empty.⊥`; the truncation eliminates
   there (`src/ProbeLJ1111A.agda:129-131`). The result is
   `SQ.via-col-truncated α initα` (`:195-196`).
3. `NonInitialT` (`:202-233`): the genuinely new piece. It eliminates
   `κ-eqα : ∥ ⟪ κ ⟫ ≃ ⟪ α ⟫ ∥₁` and the truncated IH
   `sqκT : ∥ SQ.sq κ ∥₁`, both into the proposition `∥ sq α ∥₁`. In
   the branch, the honest equivalence `e : ⟪ κ ⟫ ≃ ⟪ α ⟫` transports
   the honest pairing of `κ` to `α` (`pair`, `pair-inj`, `:208-227`).
   No injection `α ↪ κ` appears anywhere.
4. `TruncatedChain` (`:234-272`): the `∈`-induction
   (`src/ProbeLJ1111A.agda:271-272`), with the same case split as
   `[LJ-1.107]`'s `Chain` and the truncated cases above.

`κ∉ω` is copied from `[LJ-1.107]`'s `NonInitial.κ∉ω`
(`src/ProbeLJ1107A.agda:552-590`) as `NonInitKappaNotOmega`
(`src/ProbeLJ1111A.agda:78-120`); it uses only `κ-eqα` and the finite
exclusion, never the injection.

The truncated chain is **180 non-blank lines** in the probe
(`NonInitKappaNotOmega` 41, `InitialCaseT` 76, `NonInitialT` 28,
`TruncatedChain` 35). Of these, the genuinely new mathematics is the
double elimination in `NonInitialT` and the truncated square clause:
about 40 lines. The rest is the delivered `[LJ-1.107]` scaffolding
restated with the truncated types.

**The wall does not move to the truncated form.** Every route the tree
offers for the honest `sq α` at a non-initial `α` passes through the
honest injection (`_build/lj-1.107-report.md` sections 2 and 5): the
initial case is false, and the non-initial case needs `α ↪ |α|`. But
the truncated form does not need the injection, and this is the whole
point. The negative "no route to `∥ sq α ∥₁` without the injection
exists" is **INFERRED**: a machine cannot certify nonexistence, and
the tree's delivered routes are measured to pass through the injection.

## 3. HOW FAR UP `sq` MUST STAY DATA (question 1)

All the way. The trace, in the source:

1. `L.StageCardinal` takes `sq` as a module parameter, a Σ of a
   pairing and its injectivity (`src/L/StageCardinal.lagda.md:15-17`).
2. `Bound` takes `pairing` as data (`:62-65`) and consumes `fst
   pairing` and `snd pairing` in `pair` (`:67-73`), `tuple-g`
   (`:88-96`), and `formula-bound` (`:175-177`), whose output is again
   a Σ of a function and injectivity.
3. `LimitStep` instantiates `module B = Bound α oα infα (sq α infα)`
   (`:281`) and takes `cnt` and `cnt-inj` out of `B.formula-bound`
   (`:286-289`). `limit-step` (`:394-397`) and `stage-card-upper`
   (`:557-559`) output the injection `⟪ Lset α ⟫ ↪ ⟪ α ⟫`, data.
4. `Devlin55` instantiates `module SC = L.StageCardinal {ℓ} lem sq`
   (`src/L/BoundedSubset.lagda.md:1368`), takes `stage-card-upper`
   (`:1372-1374`), and builds `code-inj : ⟪ UK.X ⟫ ↪ ⟪ α ⟫`
   (`:1529-1530`), data.
5. `CodeCount` (`:1426`), `CodeSelect` (`:1098-1144`), `CanonCode`
   (`:463-505`) consume the counting and the canonical codes as data:
   `count`/`count-inj`, `h`/`h-inj`, `canonical`/`canonical-spec`.
6. `hedF` (`:1549-1551`) and `hedF-spec` (`:1552-1554`) feed
   `HullElemDown.WithCode` (`:681-766`). `elem-down` (`:1568-1569`,
   type at `DownReflect.ElemDown` `:410-413`) is proposition-valued,
   but it is built through the data chain.
7. `πX↪α` (`:1574-1576`) and `β↪α` (`:1578-1582`) are injections,
   data.

The first proposition-typed values are `β∈κ : ⟨ β ∈ˢ κ ⟩`
(`:1594-1603`) and `x∈Lκ : ⟨ x ∈ˢ Lset κ ⟩` (`:1605-1611`), which
already eliminates the cover truncation (`:1606`). The highest point
whose type is a proposition is the conclusion

```agda
theorem : ⟨ x ∈ˢ Lset κ ⟩          -- src/L/BoundedSubset.lagda.md:1621
```

Between `sq`'s entry at `Bound` and that conclusion, every type is an
injection, a Σ, or a function into one. `PT.rec` cannot eliminate
`∥ sq α ∥₁` at any of them. The truncation can live only at the
proposition points `β∈κ`, `x∈Lκ`, and the conclusion, and the data
chain must be restated to carry it there.

## 4. THE THREADING PRICE (question 2)

One best-effort figure: **about 350 non-blank in-fence lines**, band
300 to 400, to thread `∥ sq α ∥₁` from the top down to `sq`'s entry
and to supply it. Basis: measured module extents, below, plus the
measured supply chain of section 2.

The supply side is the truncated chain: **180 lines, measured** (the
probe content of section 2).

The consumer side, by measured module extent:

| module | measured extent | change |
|---|---:|---|
| `StageCardinal` parameter (`src/L/StageCardinal.lagda.md:15-17`) | 3 | `sq` becomes `sqT` |
| `LimitStep` + `limit-step` (`:275-397`) | 111 | restated in full; the per-step IH becomes truncated and must be eliminated at every use |
| `Upper.step` + `stage-card-upper` (`:555-559`) | 8 | output becomes `∥ injection ∥₁` |
| `Bound` (`:62-180`) | 107 measured | reusable; a ~6-line `formula-boundT` lift instantiates it in the branch |
| `CodeCount` (`src/L/BoundedSubset.lagda.md:1426-1531`) | 99 measured | reusable; a ~5-line lift |
| `CodeSelect` (`:1098-1144`) | 41 measured | reusable; a ~5-line lift |
| `CanonCode` (`:463-505`) | 34 measured | reusable; a ~5-line lift |
| `HullElemDown.WithCode` (`:681-766`) | 78 measured | reusable; a ~6-line lift, since `ElemDown` is a proposition |
| `BoundedSubsetAt` assembly (`:1532-1611`) | 67 measured | `code-inj`, `πX↪α`, `β↪α` lifted; `β∈κ` and `x∈Lκ` eliminate |
| `Devlin55` parameter (`:1361-1366`) | 5 | `sq` becomes `sqT` |

The genuinely restated module is `LimitStep` (111 lines): its counting
machinery consumes the induction hypothesis as data
(`src/L/StageCardinal.lagda.md:286-289, :331-349`), so the truncated
IH forces a real restatement, not a wrapper. The other modules are
self-contained: a `PT.rec squash₁ (λ honest → ∣ reuse honest ∣₁)` lift
of about 5 to 8 lines each, because each target `∥ · ∥₁` is a
proposition. Sum: about 170 consumer lines, of which about 120
restate and about 50 are lifts. With the 180-line supply, the total is
about 350. The lift-count is **INFERRED** (5 to 8 lines per module);
the module extents are **MEASURED**.

The widest unmeasured term is SECONDS: the lifted pipeline re-elaborates
the honest machinery inside each `PT.rec` branch, so the check time is
the honest pipeline's time plus the elimination overhead. The P-m and
P-l classes put that overhead at a fraction of the pipeline's own cost,
but nothing here measures it. A real build must re-measure at the site
(P-l).

**The threading does not cure the wall; it relocates it.** The honest
`sq α` at non-initial `α` remains unconstructible (`[LJ-1.107]`,
measured). What the threading buys is that no consumer needs it: the
truncated chain supplies `∥ sq α ∥₁` everywhere, the pipeline carries
the truncation down, and the conclusion eliminates it.

## 5. CHOICE

No axiom of choice is used. The probe imports no choice principle. The
standing `lem : LEM (ℓ-suc ℓ)` parameter exists only to instantiate
`ProbeLJ1107A`; the new content calls no `lem` of its own
(`src/ProbeLJ1111A.agda`). The truncated chain stays choice-free,
**MEASURED** by the probe's imports and types. This matches
`[LJ-1.107]`'s reading of the same chain
(`_build/lj-1.107-report.md` section 4).

## 6. THE C-39 SECTION

One brief prohibition blocks a route, and the door is reported.

**"Do not touch `src/L/Condensation/`"** blocks the natural probe
import of `L.BoundedSubset`, because `L.BoundedSubset` imports
`L.Condensation` (`src/L/BoundedSubset.lagda.md:29`), where a sibling
works. The door: the probe imports `ProbeLJ1107A` and restates the
consumer shapes locally, exactly as `[LJ-1.107]` did
(`_build/lj-1.107-report.md` section 5). This is the same door as
`[LJ-1.106]` (`_build/lj-1.106-report.md` section 5).

The brief's question 3 itself blocks nothing: the untruncated-equivalence
route is closed by the mathematics, not by a prohibition. The route
behind the wall is the truncation-at-top threading of sections 2 and 4,
which the GOAL names and this dispatch measures. Nothing in the brief
forbids it; the probes state it without touching any master.

## 7. C-40 SECTION: THE CONSUMERS OF A REAL REPAIR

The probes change no master, so C-40's test is not run. A real repair
would change `L.StageCardinal` (the `sq` parameter, `LimitStep`, the
`Upper` step) and `L.BoundedSubset` (the `Devlin55` parameter and the
assembly). Their consumers, verified by reading:

- `L.BoundedSubset` imports `L.StageCardinal`
  (`src/L/BoundedSubset.lagda.md:881`) and instantiates it
  (`:1368`).
- `src/Everything.lagda.md:369` and `:374` import the two masters.
- `Devlin55` has no instantiation anywhere in the tree
  (`rg Devlin55` hits only `src/L/BoundedSubset.lagda.md`), so it is
  currently consumer-free; a signature change to `Devlin55` would not
  break anything that exists.

The J tower inherits the change by the shared signature: no J tower
exists in this tree (**INFERRED**, same as `[LJ-1.107]` section 7), so
the question is what a future J consumer would see. Both the honest
`sq` parameter and the threaded `sqT` parameter are tower-generic; the
threaded form would let a J consumer run on the truncated chain, and
the honest-injection wall would bind neither.

## 8. THE NEGATIVES AND THEIR STATUS

1. "The least witness's uniqueness makes the fiber a proposition, so
   the truncation eliminates": **MEASURED FALSE**. The extraction is
   refused at `src/ProbeLJ1111B.agda:46` with `Type _ℓ_8 !=< x ≡ y`,
   with `κ-min-at` in scope.
2. "`∥ sq α ∥₁` at every infinite ordinal closes without the honest
   injection": **MEASURED TRUE**. `TruncatedChain.theorem`
   (`src/ProbeLJ1111A.agda:271-272`) checks GREEN.
3. "The truncated form was already delivered": **MEASURED FALSE as a
   full statement**. `via-col-truncated` is conditional on `Init α`
   (`src/L/Ordinal/SquareLaw.lagda.md:963-964`), the initial case
   only. The non-initial truncated case is new content, section 2.
4. "`sq` is consumed as data one level down": **MEASURED TRUE**.
   `src/L/StageCardinal.lagda.md:281` and `:286-289`.
5. "The theorem's conclusion is a proposition": **MEASURED TRUE**.
   `src/L/BoundedSubset.lagda.md:1621`.
6. "Every intermediate type between `Bound` and the conclusion is
   data": **MEASURED TRUE** by reading, section 3.
7. "The threading costs about 350 lines": module extents **MEASURED**;
   the lift pattern **INFERRED** at 5 to 8 lines per module.
8. "No route to `∥ sq α ∥₁` without the injection exists":
   **INFERRED**. The delivered routes are measured to pass through the
   injection (`_build/lj-1.107-report.md` sections 2 and 5); a machine
   cannot certify nonexistence.
9. "The route is choice-free": **MEASURED TRUE** for the probe
   content, section 5.

## 9. DD4

The truncated chain is written generic. Its types name only the
ambient universe `S`, the presentations `⟪ · ⟫`, the well-order
machinery, `ω`, `sucV`, `IsOrd`, `SQ.sq`, and truncations; no tower
object appears (`src/ProbeLJ1111A.agda`). It reuses the `[LJ-1.107]`
modules (`LeastCard`, `CSB`, `ShiftAbs`, `Shiftω`, `Incl`,
`FiniteAtω`) unchanged, so the code the two proofs share is maximized:
the truncated chain is the honest chain with the conclusion truncated
and two case modules adapted. The J half is **INFERRED** (no J tower
exists); it would inherit the same generic statement.

**A truncation moved to the top is a change to the shared cardinal
chapter.** The J tower does NOT inherit the result unchanged: it would
inherit the changed signatures of `L.StageCardinal` and
`L.BoundedSubset` (section 7), and it would inherit the wall's
disappearance, because the truncated chain is tower-generic. The
honest-injection wall binds the data version only, and the threading
removes the data requirement.

## 10. THE COST QUESTION

`[LJ-1.107]` priced the partial honest chain at 582 lines and about
117 s. This dispatch replaces the wall with a measured route:

- The truncated chain: 180 non-blank lines, checks inside the
  250-line probe at about 20.9 s cold (load 3.09 / 4.03 / 4.24) and
  2.41 s warm.
- The threading to Devlin55: about 350 lines total, band 300 to 400,
  basis in section 4.
- The honest chain at non-initial `α` stays unconstructible; the wall
  is unchanged for the data version.

The widest unmeasured term is the threading's check time, **INFERRED**
to sit near the honest pipeline's own seconds plus elimination
overhead.

## 11. ARCHIVE USED

- `_build/lj-1.107-report.md`, read WHOLE. TOOK the wall and its
  error (`Type ℓ !=< x ≡ y`, section 2), the conditional chain
  (`Chain.theorem`, `src/ProbeLJ1107A.agda:663-666`), and the C-39
  door at `L.BoundedSubset`.
- `src/ProbeLJ1107A.agda`, read WHOLE. TOOK `LeastCard` (`:217-266`,
  `κ-eqα` `:247-248`, `κ-min-at` `:259-266`), `InitialCase`
  (`:464-537`), `NonInitial` (`:549-618`), `Chain` (`:630-666`),
  reused unchanged by the truncated chain.
- `_build/l3.32-t31-report.md`, read WHOLE. TOOK sections 3 and 5:
  the same extraction wall and the `ω ≃ ω + 1` many-bijections
  example.
- `_build/lj-1.106-report.md`, read WHOLE, and
  `src/ProbeLJ1106A.agda` (`:540-579`). TOOK `InitBridge` and
  `InitAtSiteFull.initκ`, the pairing at `ω`, and the C-39 door.
- `src/L/Ordinal/SquareLaw.lagda.md`, read `:938-964`. TOOK `Init`
  (`:692-698`), `via-col-square` (`:960-961`), `via-col-truncated`
  (`:963-964`).
- `src/L/StageCardinal.lagda.md`, read `:1-110`, `:255-397`,
  `:510-560`. TOOK the `sq` parameter (`:15-17`), `Bound` (`:62-180`),
  the `LimitStep` consumption (`:281`, `:286-289`), `limit-step`
  (`:394-397`), `step` and `stage-card-upper` (`:555-559`).
- `src/L/BoundedSubset.lagda.md`, read `:356-463`, `:463-505`,
  `:667-766`, `:1098-1144`, `:1358-1626`. TOOK `Devlin55` (`:1361`),
  the `sq` parameter (`:1362-1364`), `code-inj` (`:1529-1530`),
  `CodeCount` (`:1426`), `CodeSelect` (`:1098`), `CanonCode`
  (`:463`), `HullElemDown.WithCode` (`:681`), `ElemDown` (`:410`),
  `πX↪α` (`:1574`), `β↪α` (`:1578`), `β∈κ` (`:1594`), `x∈Lκ`
  (`:1605-1611`), `theorem` (`:1621`).
- `dev/LESSONS.md`, read WHOLE C-38 (`:3427`), C-39 (`:3521`),
  C-40 (`:3602`), P-x (`:3564`), D-8 (`:1377`), D-30 (`:3332`),
  P-l (`:2305`), P-m (`:2460`), and the `--for build` and `--for
  probe` bundles via `scripts/rules.py`.
- `dev/literature/devlin-II5.md`, read the 5.5 and 5.6 spine
  (`:150-170`) and the square-law rows (`:382`, `:411-415`).

## 12. LITERATURE USED

Devlin's 5.5 consumes 1.1(vii), `|L_α| = |α|`, as a cardinal EQUALITY,
never as a data-carrying pairing (`dev/literature/devlin-II5.md:
154-156`). The square-law fact is proved in his Chapter 1 as standard
cardinal arithmetic and cited in 5.5; the honest injection that the
tree needs internally is a formalization choice, not a Devlin datum.

## 13. GATES

`src/ProbeLJ1111A.agda`: GREEN at the C-12 cap, one process at a time.
About 20.9 s first full check, 2.41 s warm, at load 3.09 / 4.03 /
4.24, four users, machine NOT quiet. `src/ProbeLJ1111B.agda`: RED by
design, the refusal, 1.84 s at load 3.60 / 4.06 / 4.24. Both linters
clean: `lint-prose.py --check` exit 0, `lint-agda.py --check` exit 0.
Zero hits for `postulate`, `TERMINATING`, holes in both probes.
`scripts/ledger.py --brief`: standing 28,425 lines over 85 masters,
measured from HEAD. `make check` not run (forbidden). DD23: no
mathematical prose written to a master. No process left alive; every
check returned. HEAD moved during the dispatch, from `0332614` to
`126773f`: the sibling's `src/L/Condensation/` repair and two
registrations (`[LJ-1.112]`, `[LJ-1.113]`) were committed by the
orchestrator mid-dispatch. The probes were re-checked GREEN at the
final HEAD (2.24 s warm at load 4.31 / 5.01 / 4.67); the probe imports
never reach `L.Condensation`. The working tree is clean except the
ignored probes and report; no master touched. No commit, no push.
