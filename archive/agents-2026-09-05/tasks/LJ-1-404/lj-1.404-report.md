# LJ-1.404 report: the selected cardinal is infinite, so it IS closed under successor

slot: `coder`. Written early as a skeleton and filled as answers landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-404/`. Agda ran under the
caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time, no heap event.

TARGET: build TWO terms in `agents/tasks/LJ-1-404/Probe404.agda`, at a GENERIC
ordinal: `kappa-infinite` and `kappa-is-limit⁺`.

## VERDICT

SPLIT. NO-GO on `kappa-infinite`. GO on `kappa-is-limit⁺`. The NO-GO is a
refutation: the statement is FALSE as stated, and the refutation is green in
Agda. The obstruction is `review-of-kappa-infinite.md`, written for the branch
`no-go-stated`.

1. `kappa-infinite` is REFUTED. The site is `a := sucV ω`. At that site
   `fst κ ≡ ω` (`Probe404.agda:175-180`), and the conclusion is `⟨ ω ∈ ω ⟩`,
   which `∈-irrefl` kills. The refutation `kappa-infinite-refuted` is green
   (`:182-188`). The obligation is left as a hole (`:141-145`), red by design,
   exactly as `[LJ-1.396]` left its refuted `kappa-is-limit`
   (`agents/tasks/LJ-1-396/Probe396.agda:110`).
2. `kappa-is-limit⁺` is GREEN (`Probe404.agda:202-243`). Successor-closure of
   the selected `κ` holds from `⟨ ω ∈ fst a ⟩`. The case `κ ≡ ω` is `ω-limit`.
   The case `ω ∈ κ` closes `γ ≡ ω` by `suc∈or≡` plus `Shiftω.shift↪` plus
   `κ-min-at`. The brief named `⟨ sucV ω ∈ fst κ ⟩` as a possible extra
   hypothesis. It is a conclusion, not a hypothesis.
3. The honest infiniteness is `kappa-not-finite` (`Probe404.agda:124-133`),
   also green: `ω ∈ a` implies `κ ∉ ω`. With `infinite-or-omega` that is
   `(κ ≡ ω) ⊎ ⟨ ω ∈ κ ⟩`.

## MEMBERSHIP SPELLING

Every membership in the two obligations is `∈ˢ`, matching `κ-min-at` at
`src/L/Cardinal.lagda.md:140-142`:

```
κ-min-at : (δ : S) → ⟨ fst δ ∈ˢ fst κ ⟩
         → ∥ ⟪ fst α ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥
```

The brief's displayed types use the bare `∈`. The two convert, as
`[LJ-1.396]` already used. W3's `infinite-or-omega` keeps the brief's bare
`∈`, because that is the consumer-bridge type as stated.

## 1. What was built

All in `agents/tasks/LJ-1-404/Probe404.agda`, module
`LJ-1-404.Probe404 {ℓ} (lem)`:

- `infinite-or-omega`, the W3 probe, first (`:52-59`). EIGHT code lines.
- `pair-const` and `pair-const-inj` (`:66-72`). SIX code lines. This is the
  adaptation of a plain injection to `finite-excl`'s square.
- `comp-inj` (`:74-76`), `beta-lifts` (`:78-79`).
- `Shiftω` (`:84`), `ShiftAbs` at `ω`. The injection `⟪ sucV ω ⟫ ↪ ⟪ ω ⟫`.
- `shift-at` (`:87-91`), `ShiftAbs` at a generic infinite ordinal.
- `plain-excl` (`:96-116`). TWENTY-ONE code lines. The pairing is not free:
  the dummy member exists at a positive numeral, and the zero numeral is
  killed as an empty target.
- `kappa-not-finite` (`:124-133`). TEN code lines.
- `kappa-infinite`, TERM 1 as the brief states it, a hole (`:141-145`).
- The refutation: `aω` (`:155-158`), `κ-not-sucω` (`:168-173`), `κ≡ω`
  (`:175-180`), `kappa-infinite-refuted` (`:182-188`).
- `kappa-is-limit⁺`, TERM 2, green (`:202-243`). FORTY-TWO code lines.

`LeastCardInjL` is opened and not restated (`Probe404.agda:133`, `:209`), as
the brief orders (`src/L/Cardinal.lagda.md:60`).

## 2. W3: `infinite-or-omega`, first

GO. The brief named the consumer bridge as the widest unmeasured term, and
ordered it stated alone and run before anything else. It is
`infinite-or-omega` (`Probe404.agda:52-59`). EIGHT code lines. Signature 2,
body 6. Proved by `ord-tri` (`src/L/Ordinal/Linear.lagda.md:136`). The finite
case is the hypothesis's negation. The two remaining cases are the two
summands.

First run of this term alone: 0.89 s, exit 0, caliber `-A64m -I0 -M8g`.

The consumer `L.StageCardinal` quantifies `sq` over `δ` with
`(⟨ δ ∈ ω ⟩ → Empty.⊥)` (`src/L/StageCardinal.lagda.md:16-19`), which allows
`δ ≡ ω`. This term splits that hypothesis. The `δ ≡ ω` branch is `squareω`
(`src/L/InjChain.lagda.md:184-185`). The `ω ∈ δ` branch is the hypothesis of
both obligations here.

## 3. TERM 1: the refutation, and the finite-excl adaptation

The brief's reasoning for `kappa-infinite` is: if `κ` were finite, `κ-inj`
would inject `⟪ fst a ⟫` into a finite ordinal, and `finite-excl` would
refute that. That argument is TRUE and is `kappa-not-finite`. It does not
give `ω ∈ κ`. Trichotomy still has the case `κ ≡ ω`.

`finite-excl` (`src/L/Ordinal/SquareLaw.lagda.md:664-668`) takes
`f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫`, a map into the SQUARE, not a plain injection.
The adaptation is `pair-const` (`Probe404.agda:66-72`): pair the plain
injection with a fixed member of `⟪ β ⟫`. SIX code lines, and they are not
free. Finding the member is a real step:

- If `β ≡ # 0`, the target is empty. `ω ∈ α` gives an inhabitant of `⟪ α ⟫`,
  and there is no injection into `⟪ ∅ ⟫` (`plain-excl`, zero clause,
  `:105-109`).
- If `β ≡ # (suc n)`, the dummy is `fiber (# (suc n)) (self∈sucV (# n)) .fst`,
  rewritten along the path (`:114-116`).

I used `finite-excl`, not `finite-excl-ω`. The source is a generic
`ω`-holding ordinal, not `ω` itself. The truncation of `κ-inj` is free
because the conclusion is `Empty.⊥`
(`dev/literature/truncation-and-selection.md:75-80`).

The missing case `κ ≡ ω` is actual at `a := sucV ω`. `ShiftAbs`
(`src/L/Absorption.lagda.md:73-75`, `:189-190`) instantiates at `ω`: `ω` is
not a numeral (`∈-irrefl ω`) and holds every numeral (`#∈ω`). That is
`⟪ sucV ω ⟫ ↪ ⟪ ω ⟫`, which `suc-absorb` cannot give, because `suc-absorb`
wants `ω ∈ γ`. Minimality then forbids `κ ≡ sucV ω`. Combined with
`kappa-not-finite`, `fst κ ≡ ω`. Then `ω ∈ κ` is `ω ∈ ω`.

## 4. TERM 2: successor-closure, green as stated

`kappa-is-limit⁺` splits `κ` against `ω` first, then `γ` against `ω`.

- `κ ∈ ω`: `kappa-not-finite`.
- `κ ≡ ω`: `γ ∈ ω`, and `ω-limit` (`src/L/InjChain.lagda.md:109`) keeps the
  successor inside `ω`.
- `ω ∈ κ`, and `γ ∈ ω`: `ω-limit`, then transitivity through `ω ∈ κ`.
- `ω ∈ κ`, and `γ ≡ ω`: `suc∈or≡` (`src/L/Ordinal/Stages.lagda.md:137`) at
  `ω`. The membership case is the goal. The equality `κ ≡ sucV ω` dies on
  `Shiftω.shift↪` composed under `κ-inj` and `κ-min-at` (`:213-221`).
- `ω ∈ κ`, and `ω ∈ γ`: `suc∈or≡` at `γ`. The equality dies on `shift-at`
  (`:87-91`) the same way. This is `[LJ-1.396]`'s `kappa-is-limit-ω∈γ`
  (`agents/tasks/LJ-1-396/Probe396.agda:172-184`) with `ShiftAbs` in place
  of the module hypothesis `suc-absorb`.

The `γ ≡ ω` case, which the brief flagged as the likely NO-GO, closes. It
does not follow from `ω ∈ κ` alone. It follows from `ω ∈ κ` plus
minimality plus the hotel shift at `ω`.

## 5. W2 and DD4

Both statements are written once at a generic `a : S`, with
`oa : IsOrd (fst a)`. The statements name no ordinal, no site and no
numeral. TERM 1's refutation names `a := sucV ω`, which is what a
refutation must do (C-42). `kappa-not-finite` and `kappa-is-limit⁺` are
generic in `a` and in `γ`. `ShiftAbs` is written once at a generic carrier
in `src/` and instantiated twice: at `ω`, and at a generic infinite
ordinal.

## 6. Runs, caliber, slots

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, from the repository root, 2026-08-20. The only
error in every full-file run is the hole at `Probe404.agda:145`.

- W3 alone, first: 0.89 s, exit 0.
- Full file, three consecutive runs: 1.92 s, 1.91 s, 1.91 s. Median 1.91 s,
  exit 42 each time.

The repaired infiniteness, the successor-closure, and the refutation are all
in the file that Agda checked; they are green because the only unsolved meta
is the stated hole. No heap event.

The brief's estimate for the two obligations together was about 35 code
lines. TERM 2 alone is 42. Nothing is funded against that estimate. The
extra is the split of `κ` against `ω` (the brief split only `γ`) and the
`ShiftAbs` wiring of the two equality cases.

## 7. C-42 sweep

The refutation measures ONE site: `a := sucV ω`. COUNT of the named shape
(`ω ∈` the selected `κ`, from `ω ∈ a`) in live `src/`: 0. COUNT of that
shape as a stated obligation: 1, this task.

Cousins, not this shape and not funded against it:

- `kappa-is-limit` (`agents/tasks/LJ-1-396/Probe396.agda:106-110`),
  successor-closure of `κ` with no infiniteness hypothesis, refuted at
  `a := sucV ∅`.
- `amb-limit` (`agents/tasks/LJ-1-392/Probe392.agda:211-215`),
  successor-closure of a generic `α` given `AmbCard`, with `⟨ ω ∈ α ⟩` and
  without `⟨ ω ∈ γ ⟩`.
- `amb-init` (`agents/tasks/LJ-1-393/Probe393.agda:182-185`), `Init` from
  `AmbCard` without `⟨ sucV ω ∈ α ⟩`.

## 8. What GO and NO-GO each earn

NO-GO on TERM 1 earns the falsehood of `ω ∈ κ` from `ω ∈ a`. The selected
cardinal of a countable ordinal that holds `ω` is `ω`. The honest
infiniteness is `kappa-not-finite`.

GO on TERM 2 earns successor-closure of the selected `κ` from `ω ∈ a`. When
`κ ≡ ω`, that closure is `ω-limit`, and the square law is `squareω`
(`src/L/InjChain.lagda.md:184-185`), not `Init`. When `ω ∈ κ`, TERM 2
supplies the third conjunct of `Init` at `κ`, including `sucV ω ∈ κ`.
`[LJ-1.396]` already supplies `AmbCard` at `κ`. This probe does not prove
`AmbCard (fst a)`, it does not touch the arrow's truncation, and it does
not discharge any module parameter.

The consumer bridge is green. A caller that has `(⟨ δ ∈ ω ⟩ → Empty.⊥)`
uses `infinite-or-omega` to split: `δ ≡ ω` is `squareω`, and `ω ∈ δ` is
the hypothesis of TERM 2.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md`: read at `:29`,
  `module L.Cardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ)) where`. Declined for
  use. It is the rud-route CSB and Cantor chapter. It does not contain
  `LeastCardInjL`. The live site is `src/L/Cardinal.lagda.md:60`.
- `archive/src/2026-08-09-rud-route/L/Ordinal`: not surveyed. It is a
  directory of the archived rud-route ordinal development. The live
  trichotomy, `finite-excl`, and `ω-ord` sit in `src/`.
- `archive/dev/JOURNAL-archived.md`: not read. It is the retired-route
  journal, and no step of this probe consults it.
- `archive/dev/TASKS-archived.md`: not read. The archived task index names
  no task this probe reads.
- `dev/ARCHIVE.md`: read at `:3`, `The registry of Bedrock's retired modules. One entry per module, written at`.
  Not used. This probe retires no module.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: read at `:76`,
  `truncated existence of an injection.** That is the HoTT Book's own definition,`.
  Used: the truncation of `κ-inj` is free in `kappa-not-finite` and in both
  `κ-min-at` appeals, because each conclusion is `Empty.⊥`.
- `dev/literature/terms-2026-08.md`: read at `:8`,
  `Written incrementally: skeleton first, each term filled as its findings`.
  Not used. This probe writes no glossary entry and no translation.
- `dev/literature/devlin-II5.md`: read at `:127`,
  `The proof verifies Tarski's criterion by a least-witness argument over the`.
  Not used. The selection this probe consumes is the live `LeastCardInjL`,
  already delivered.
- `dev/literature/digest.md`: read at `:1`,
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  Declined. This probe does not consult the rud architecture.
