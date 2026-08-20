# LJ-1.408 report: may the pairing live inside the consumer's truncation?

slot: `coder`. Written early as a skeleton and filled as answers landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-408/`. Agda ran under the
caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time, no heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-408/Probe408.agda`: `pair-cross`.

## VERDICT

NO-GO. The NO-GO is a refutation: the statement is FALSE as stated, and the
refutation is green in Agda. The obstruction is `review-of-pair-cross.md`,
written for the branch `no-go-stated`.

1. `pair-cross` is REFUTED. The site is `α := ω`. Given any pairing `s : sq ω`,
   `s₂ := swap-sq ω s` makes `fst s (m0 , m1) ≡ fst s₂ (m1 , m0)` hold by
   `refl`, and the stated conclusion is `m0 ≡ m1`. The numerals `# 0` and
   `# 1` are distinct members of `ω`. `∈-irrefl` kills the equality
   (`src/V/Hierarchy.lagda.md:155-156`). The refutation
   `pair-cross-refuted` is green (`Probe408.agda:95-104`). The obligation is
   left as a hole (`:64`), red by design, exactly as `[LJ-1.396]` left
   `kappa-is-limit` (`agents/tasks/LJ-1-396/Probe396.agda:110`) and
   `[LJ-1.404]` left `kappa-infinite` (`agents/tasks/LJ-1-404/Probe404.agda:145`).
2. The consumer needs the pairing as DATA at
   `src/L/StageCardinal.lagda.md:283` (the one spend of the module parameter)
   and `:382` (`h-inj` reads `B.pair-inj` at that one pairing). If the pairing
   moved inside `class-pred`'s truncation (`:319-322`), `h-inj` would need
   `pair-cross`, which is false.

THE TYPE THAT WOULD HAVE TO BE CANONICAL for `h-inj` to survive a truncated
pairing: `isProp (sq α)`. That type is false. `sq α` is a Sigma
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`). The swap is a second inhabitant
whenever one exists. The weaker surviving type is the current one: the pairing
is data beside the truncation, so both packages share `B.pair`.

## 1. What was built

All in `agents/tasks/LJ-1-408/Probe408.agda`, module
`LJ-1-408.Probe408 {ℓ}`:

- `sq`, the pairing-and-injectivity Sigma (`:33-35`). THREE code lines. It
  matches `src/L/Ordinal/SquareLaw.lagda.md:685-687`. Written here so the
  probe does not load that chapter for a type alias.
- `swap-sq`, the W3 probe, first (`:43-52`). TEN code lines.
- `pair-cross`, the obligation as the brief states it, a hole (`:58-64`).
- The refutation: `m0` (`:76-77`), `m1` (`:79-80`), `m0≢m1` (`:82-93`),
  `pair-cross-refuted` (`:95-104`).

The pairing at `ω` is a hypothesis of `pair-cross-refuted`. `pair-cross` is a
Π over pairings, so a counterexample must instantiate one. The consumer has
that pairing as a module parameter (`src/L/StageCardinal.lagda.md:17`). The
tree also has `squareω : sq ω` (`src/L/InjChain.lagda.md:184-185`). This
probe does not import `InjChain`.

## 2. W3: `swap-sq`, first

GO. The brief named the swapped pairing as the widest unmeasured term, and
ordered it stated alone and run before anything else. It is `swap-sq`
(`Probe408.agda:43-52`). TEN code lines. Signature 1, body 9. If
`s = (f , f-inj)`, the swap sends `(x , y)` to `f (y , x)`. Injectivity is
`ΣPathP` over `f-inj` of the swapped pair: `cong snd p` recovers the first
component, `cong fst p` recovers the second. No associativity and no
transport.

First run of this term alone: 0.78 s, exit 0, caliber `-A64m -I0 -M8g`.

## THE OTHER SITE

`grep` of `src/L/StageCardinal.lagda.md` for the identifier `sq` (not
`squash₁`, not the comment "square law"):

| line | what |
|---|---|
| 17 | module-parameter declaration |
| 283 | the spend: `module B = Bound α oα infα (sq α α∈suc infα)` |

COUNT of spend sites: 1.

The parameter could be an argument of `LimitStep` / `limit-step`
(`src/L/StageCardinal.lagda.md:277` and `:396-403`) instead of a module
parameter. That is a telescope change. `Upper.step` (`:561-562`) calls
`limit-step` and would thread the pairing at `α`. `Upper.stage-card-upper`
(`:564-566`) is `∈-induction step`, so a family of pairings remains in
scope either as the module parameter or as an extra argument of `step`.
Proof bodies do not change. The module parameter already IS that family
(`:17-19`). One spend site does not make the pairing a proposition.

## THE FAMILY

`LimitStep` takes the stage embeddings as a family
`ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫`
(`src/L/StageCardinal.lagda.md:281`). `Upper.branch` builds that family from
the recursion (`:534-559`).

The family cannot be pointwise truncated. The term that breaks is `cnt`
(`:288`):

    cnt m = fst (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m))

`formula-bound` (`:177-179`) wants the injection as a Sigma, data, not a
truncation. `cnt-inj` (`:291`) is the same spend. I did not build a truncated
family. I named `cnt`.

## W2 (DD4)

`pair-cross` is generic in `α` and in both pairings. It names no ordinal and
no numeral. `swap-sq` is generic in `α`. The refutation names ONE site,
`α := ω`, which is what a refutation must do (C-42). The two members are the
numerals `# 0` and `# 1` of that site.

## 3. Runs, caliber, slots

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, from the repository root, 2026-08-20. The only
error in every full-file run is the hole at `Probe408.agda:64`.

- W3 alone, first: 0.78 s, exit 0.
- Full file, three consecutive runs: 0.87 s, 0.86 s, 0.86 s. Median 0.86 s,
  exit 42 each time.

The refutation is in the file that Agda checked; it is green because the only
unsolved meta is the stated hole. No heap event.

The brief's estimate for the obligation was about 25 code lines including the
refutation. `swap-sq` is 10. The refutation block (`m0`, `m1`, `m0≢m1`,
`pair-cross-refuted`) is 28. Nothing is funded against that estimate. The extra
is the numeral-membership plumbing at `ω`.

## C-42 sweep

The refutation measures ONE site: `α := ω`, with the swapped pairing. COUNT of
sites in live `src/` that compare two counts under two different pairings: 0.

Every live `pair-inj` is at one pairing:

- `src/L/StageCardinal.lagda.md:71-72`, `:382`
- `src/L/BoundedSubset.lagda.md:1439` and the seven call sites after it
- `src/L/Ordinal/SquareLaw.lagda.md:947-948`
- `src/FOL/Count.lagda.md:59-60`

No cure is priced. The measured warrant is: the consumer needs the pairing as
DATA at `:283` and `:382`.

## 4. What GO and NO-GO each earn

NO-GO earns the campaign's bill, stated once: the consumer needs the pairing
as DATA, at `src/L/StageCardinal.lagda.md:283` and `:382`, because `h-inj`
compares two packages with `B.pair-inj` at one pairing, and the cross-pairing
step `pair-cross` is false. `[LJ-1.407]`'s truncated square law does not
reach this consumer as stated. Codes, `Ne⁺`, and the ambient arrow are not
withdrawn by this return; they are not this measurement.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md`: read at `:28`.
  Quote: `module L.CardinalCount {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where`.
  Surveyed. It is the archived counting chapter. It is not a two-pairing site.
- `archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md`: read at `:609`.
  Quote: `pair-inj : {a b c d : ⟪ α ⟫} → pair a b ≡ pair c d → (a ≡ c) × (b ≡ d)`.
  Archived `pair-inj` is at ONE pairing, the same shape as the live
  `B.pair-inj`. Used for the C-42 sweep of the archive.
- `archive/dev/JOURNAL-archived.md`: declined, not used. It is the retired-route
  journal and does not name `pair-cross` or a swapped pairing.
- `archive/dev/TASKS-archived.md`: declined, not used. It is the retired
  `L3.32-T` index.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No pairing module is retired by this task.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read at `:70`. Quote:
  `selection a function rather than a choice.` Used: `h` is `leastOf` over an
  hProp (`src/L/StageCardinal.lagda.md:350-351`,
  `src/L/WellOrder/Base.lagda.md:158`), so `h` stays data if the pairing moves
  inside `class-pred`. The step that then fails is `h-inj`, not `h`. Also
  read at `:76`. Quote:
  `truncated existence of an injection.** That is the HoTT Book's own definition,`
  The square law as a cardinal equation would be truncated; the consumer asks
  for the pairing as data.
- `dev/literature/devlin-II5.md`: declined, not used. Condensation digest.
  This probe measures a pairing-cross, not II.5.
- `dev/literature/digest.md`: declined, not used. Orthodox rud-route digest.
- `dev/literature/terms-2026-08.md`: declined, not used. Terminology dossier.
