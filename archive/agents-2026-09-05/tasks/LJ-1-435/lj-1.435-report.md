# LJ-1.435 report: the limit step from a POINTWISE truncated branch family

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-435/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`. I did
not set `GHCRTS`. One Agda process at a time. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-435/Probe435.agda`:

    limit-step-trunc :
        (α : S) → ⟨ α ∈ˢ sucV α₀ ⟩ → IsOrd α → (⟨ α ∈ˢ ω ⟩ → Empty.⊥)
      → ((m : ⟪ α ⟫) → ∥ ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫ ∥₁)
      → ∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁

The pairing stays data: `sq α α∈suc infα`
(`src/L/StageCardinal.lagda.md:283`). This task does not truncate it.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that collection.
It does not start phase 3. No Boundary clause is in conflict. Nothing was
written into `src/`.

## VERDICT

NO-GO. The NO-GO is a refutation of the cross-count that injectivity needs.
The obstruction is `review-of-limit-step-trunc.md`, written for the branch
`no-go-stated`.

1. W3, the value half, is GO. `h-trunc` typechecks
   (`Probe435.agda:132-141`). `class-pred'` carries the branch injection
   inside the truncation that is already there. `leastOf` still runs.
   The pairing stays data at `SC.Bound` (`Probe435.agda:72`), matching
   `src/L/StageCardinal.lagda.md:283`.
2. The obligation `limit-step-trunc` is not inhabited. It is a hole
   (`Probe435.agda:153`), red by design, exactly as `[LJ-1.408]` left
   `pair-cross` (`agents/tasks/LJ-1-408/Probe408.agda:64`).
3. What `h'-inj` needs, as a type, is `CntCross` (`Probe435.agda:166-175`).
   The chapter's step that assumes one injection is
   `src/L/StageCardinal.lagda.md:390`: `cnt-inj m₁ φ₁ (subst F (sym qm) φ₂)
   ecount'`. The tree does not deliver the cross form. `CntCross` is
   FALSE. The refutation `cnt-cross-refuted` is green
   (`Probe435.agda:347-353`).

This task closes the STEP along the chapter's counting, and it closes it
as a NO-GO. It does not close the INDUCTION. It does not say
`limit-step-trunc` is false as a type. It says the chapter's counting
cannot inhabit it, because that counting needs `CntCross`.

## D-10, BEFORE ANY AGDA

Every use of the `ih` parameter inside `module LimitStep`
(`src/L/StageCardinal.lagda.md:277-393`). The identifier `ih` occurs at the
telescope (`:281`) and at two spends. The two spends are `cnt` and
`cnt-inj`. I continued.

| site | what | under `class-pred`'s truncation? |
|---|---|---|
| `:281` | telescope: `ih : (m : ⟪ α ⟫) → ⟪ Lset (⟪ α ⟫↪ m) ⟫ ↪ ⟪ α ⟫` | declaration, not a spend |
| `:289` | `cnt m = fst (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m))` | no. Module-level definition. |
| `:292` | `cnt-inj m = snd (B.formula-bound {K = ⟪ Lset (⟪ α ⟫↪ m) ⟫} (ih m))` | no. Module-level definition. |

`grep` of `src/L/StageCardinal.lagda.md` for the identifier `ih` inside
`module LimitStep` (lines 277-393): three hits, `:281`, `:289`, `:292`.
No fourth spend.

`cnt` is later read inside the truncated predicate (`:322`, `:343`) and
inside `h-inj` after the predicate is opened (`:368-388`). `cnt-inj` is
read only in `h-inj` (`:390`), after both witnesses are opened. Those
are uses of `cnt` and `cnt-inj`, not further uses of `ih`.

## 1. What was built

All in `agents/tasks/LJ-1-435/Probe435.agda`, module
`LJ-1-435.Probe435 {ℓ} (lem) (α₀) (oα₀) (sq)`:

- `LimitStepTrunc`, with `class-pred'` carrying `g` in the witness
  (`:64-130`, predicate at `:91-97`). `cnt-of g = fst (B.formula-bound g)`
  (`:77-78`). Pairing is data (`:72`).
- W3: `h-trunc` (`:132-141`).
- `limit-step-trunc`, the obligation as the brief states it, a hole
  (`:149-153`).
- `fb` and `CntCross`, the type `h'-inj` needs (`:159-175`).
- The refutation: `m0`, `m1`, `m0≢m1` (`:189-206`), `g₁`/`g₂` and their
  injectivity (`:208-229`), `φ₀`/`ψ₀` (`:237-242`), `counts-eq-prf`
  (`:293-345`), `cnt-cross-refuted` (`:347-353`).

## 2. W3: `h-trunc`, first

**GO.** The brief named the value half as the widest unmeasured term. The
probe is `h-trunc` (`Probe435.agda:132-141`). Nonemptiness recs over
`Lset-out`, then `inv`, then `ih m`, because the goal is truncated
(`:99-117`). `h` is `leastOf` over `class-pred'` (`:129-130`).

Caliber `-A64m -I0 -M8g`, one Agda process, three forced rechecks of the
value-only file (obligation omitted):

| run | wall s | peak RSS bytes |
|---|---|---|
| recheck 1 | 1.26 | 350175232 |
| recheck 2 | 1.26 | 350158848 |
| recheck 3 | 1.27 | 350158848 |

Median wall 1.26 s. Median peak RSS 350158848 bytes. Exit 0 every time.
No heap event. `runs/w3-recheck-{1,2,3}.out`. The first green check of
this term was 1.35 s (`runs/w3-2.out`).

The elaborator printed `Checking LJ-1-435.Probe435` and stopped. No
error. Quote from `runs/w3-recheck-1.out:1`:

    Checking LJ-1-435.Probe435 (/Users/alsg/Agentic/Bedrock/.pod-state/worktrees/LJ-1-435/agents/tasks/LJ-1-435/Probe435.agda).

## WHERE TWO WITNESSES MEET

After `B.pair-inj` (`src/L/StageCardinal.lagda.md:382`) identifies `m₁`
and `m₂`, the two opened witnesses of `class-pred'` carry `g₁` and `g₂`.
The equation that remains is

    fb α oα infα pairing g₁ φ₁ ≡ fb α oα infα pairing g₂' φ₂'

with `g₂'` and `φ₂'` transported along `m₁ ≡ m₂`. The conclusion the
chapter needs is `φ₁ ≡ φ₂'`. That type is `CntCross`
(`Probe435.agda:166-175`).

The chapter's step that assumes one injection is
`src/L/StageCardinal.lagda.md:390`:

    eφ = cnt-inj m₁ φ₁ (subst F (sym qm) φ₂) ecount'

The tree delivers `cnt-inj` at one `g` (`:292`). It does not deliver
`CntCross`. I do not assert `CntCross` is false by analogy with
`[LJ-1.408]`. I refute it in Agda: `cnt-cross-refuted`
(`Probe435.agda:347-353`), same shape as
`agents/tasks/LJ-1-408/Probe408.agda:95-104`.

The site is `β := ω`, with any pairing as a hypothesis. `K` is
`Lift {ℓ-zero} {ℓ} Bool`. The two injections swap `m0` and `m1`. The
two formulas are `var 0 ≐ con (lift false)` and `var 0 ≐ con (lift true)`.
`k`, shape and `n` of `composed-count` match by `refl`
(`Probe435.agda:311-316`). `encTm` of `con _` ignores the constant
(`src/FOL/Count.lagda.md:284-285`). `tuple-g` of the duplicated
constants collides because `g₁ (lift false) ≡ m0 ≡ g₂ (lift true)`.
`CntCross` would force the formulas equal, hence `lift false ≡ lift true`.

## W2 (DD4)

`limit-step-trunc` and `h-trunc` are generic in `α`. The telescope matches
`limit-step` (`src/L/StageCardinal.lagda.md:396-398`). It does not fix a
band ordinal. It does not add an infiniteness hypothesis the chapter does
not have. `infα : ⟨ α ∈ˢ ω ⟩ → Empty.⊥` is the chapter's own hypothesis.
`CntCross` is generic in `β`. The refutation names ONE site, `β := ω`,
which is what a refutation must do (C-42).

## 3. Runs, caliber, slots

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, from the repository root, 2026-08-20. The only
error in every full-file run is the hole at `Probe435.agda:153`.

Full file, three forced rechecks:

| run | wall s | peak RSS bytes |
|---|---|---|
| recheck 1 | 6.28 | 588972032 |
| recheck 2 | 6.26 | 588972032 |
| recheck 3 | 6.23 | 588955648 |

Median wall 6.26 s. Median peak RSS 588972032 bytes. Exit 42 each time.
The elaborator names one unsolved meta, at `Probe435.agda:153.20-21`:

    error: [UnsolvedInteractionMetas]
    Unsolved interaction metas at the following locations:
      .../Probe435.agda:153.20-21

Quote from `runs/full-recheck-1.out:2`. The refutation is in the file that
Agda checked. It is green because the only unsolved meta is the stated
hole. No heap event.

The brief's estimate for the Agda was about 110 code lines. The probe is
354 lines, of which the refutation block from `m0` to `cnt-cross-refuted`
is the extra. Nothing is funded against that estimate. Comparables of
shape, never of size.

## C-42 sweep

The refutation measures ONE site: `β := ω`, with two injections of
`Lift Bool`. COUNT of sites in live `src/` that compare `formula-bound`
at two different injections: 0.

Every live spend of `formula-bound` is at one injection:

- `src/L/StageCardinal.lagda.md:289` and `:292`, one `ih m` per index.
- `src/L/StageCardinal.lagda.md:177-185`, the definition.

`[LJ-1.408]` measured the pairing (`pair-cross` false). This measures the
branch injection (`CntCross` false). Two sites, two measurements. C-42
forbade transferring 408 here. The transfer would have been wrong in
direction: 408 does not imply this, and this does not re-open 408. Both
objects now fail to move into the same truncation, for two different
reasons: the pairing because `pair-inj` is at one pairing, the branch
witness because `cnt-inj` is at one injection.

No cure is priced. The consumer needs the branch family as DATA at
`:289` and `:390`.

## 4. What GO and NO-GO each earn

NO-GO earns the campaign's bill for this site, stated once: the limit
step's counting cannot absorb a pointwise truncated branch family,
because `h-inj` needs `CntCross` and `CntCross` is false. The value half
can. The branch witness is as unmovable as the pairing, by a different
measurement. `[LJ-1.407]`'s family of truncations does not reach this
consumer as stated. This closes the truncated route at its one candidate
site for the chapter's counting. It hands `[LJ-2.5]` that measured
reason. It does not close the induction above the step.

What the next brief needs:

- The value construction `h-trunc` is reusable. It cost 1.26 s median
  at the wide caliber.
- The shape that resisted is injectivity of `formula-bound` across two
  injections, not selection of the least packed value.
- Nothing was weakened. The conclusion was not dropped below
  `∥ ⟪ Lset α ⟫ ↪ ⟪ α ⟫ ∥₁`. The obligation was not inhabited.
- What did not close is `h'-inj` along `cnt-inj`. A different inhabitant
  of `limit-step-trunc`, if one exists, cannot use this counting.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: declined, not used. It is the
  archived dispatch index. This task measures a live counting step.
- `archive/dev/JOURNAL-archived.md`: read at `:1433`. Quote:
  `least-witness machinery, which absorbs a truncated union membership into a proposition-valued goal),`
  The cure absorbed a MEMBERSHIP (truncated union membership, already an
  hProp), not a FUNCTION. The object this task must absorb is an
  injection, which is not an hProp. That difference is the whole risk.
  Also read at `:1442`. Quote:
  `truncation wall on the naive descent, cured by the least-witness pattern the re-home probe`
  The value half (`h-trunc`) is that same least-witness pattern, and it
  GO. The injectivity half is not a membership into a proposition-valued
  goal. A measured cure does not transfer by analogy. Re-measured here:
  the membership-shaped half GO, the function-shaped half NO-GO.
- `dev/ARCHIVE.md`: read at `:29`. Quote:
  `- **Module.** The module's name as it was known in the live tree, e.g.`
  Declined as not used for the term. No module is retired by this task.
- `archive/dev/JOURNAL.md`: declined, not used. It is the retired
  per-episode journal.
- `archive/dev/DD-archived.md`: declined, not used. It is the archived
  DD series. W2 is live in the slot file.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read at `:70`. Quote:
  `selection a function rather than a choice.`
  Used: `h` is `leastOf` over an hProp
  (`src/L/StageCardinal.lagda.md:350-351`,
  `src/L/WellOrder/Base.lagda.md:158`), so `h-trunc` stays data when the
  branch witness moves inside `class-pred'`. The step that then fails is
  `h-inj`, not `h`. Also read at `:76`. Quote:
  `truncated existence of an injection.** That is the HoTT Book's own definition,`
  The obligation's conclusion is truncated. That does not make
  `CntCross` a proposition. `CntCross` concludes `φ ≡ ψ` as data.
- `dev/literature/devlin-II5.md`: declined, not used. Condensation
  digest. This probe measures a cross-count, not II.5.
- `dev/literature/digest.md`: declined, not used. Orthodox rud-route
  digest.
- `dev/literature/terms-2026-08.md`: declined, not used. Terminology
  dossier.
- `dev/literature/glossary-review-2026-08.md`: declined, not used.
  Glossary review.
