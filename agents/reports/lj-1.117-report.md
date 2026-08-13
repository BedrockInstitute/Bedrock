# LJ-1.117: restrict sq to the ordinals the consumer reaches

tier: codex (default)

## STATUS

COMPLETE. The restriction lands and every consumer is green. `sq` is now
stated only at the ordinals the site reaches, and the site `α = ω`
supplies it from the honest ℕ pairing, machine-checked. No theorem
conclusion changed. No master was touched except the two in scope; all
three consumers check GREEN. No commit, no push.

## 0. THE VERDICT

**The restriction lands: `sq` is stated only at `δ ≤ α₀`, where `α₀` is
the site ordinal, now a module parameter of `L.StageCardinal`.** The
parameter, quoted from `src/L/StageCardinal.lagda.md:15-19`:

```agda
module L.StageCardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
  (α₀ : V ℓ) (oα₀ : IsOrd α₀)
  (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
      → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
          ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where
```

The demand set is the site's `α₀` and every infinite ordinal below it
(`[LJ-1.116]` section 1); the bound `⟨ δ ∈ sucV α₀ ⟩` is exactly "δ ≤
α₀" for ordinals, so the hypothesis is stated precisely where the
consumers reach it. The unconstructible case at non-initial ordinals
above the site never arises: those ordinals are outside the hypothesis's
domain, and the site's own demand (`sq ω`) is honest.

Every consumer is green: `src/L/StageCardinal.lagda.md`,
`src/L/BoundedSubset.lagda.md` and `src/Everything.lagda.md` all
typecheck (section 4). The site supply is machine-checked in
`src/ProbeLJ1117A.agda`, GREEN at the C-12 cap (section 3).

## 1. THE RESTRICTION

**The step has its own target `α` and the bound `α ∈ sucV α₀` in hand;
the restriction is stated from that pair.** The demand trace, at
`file:line`:

1. `sq` appears in `L.StageCardinal` at exactly two lines: the parameter
   (`src/L/StageCardinal.lagda.md:15`) and `LimitStep`'s
   `module B = Bound α oα infα (sq α α∈suc infα)` (`:283`).
2. `LimitStep` (`:277`) takes the step's own `α`, `oα`, `infα`, and the
   threaded bound `α∈suc : ⟨ α ∈ˢ sucV α₀ ⟩`. That bound is what the
   step has in hand; the site `α₀` is the module parameter.
3. `Upper.P` (`:531`) carries the bound: `P α = IsOrd α → ⟨ α ∈ˢ sucV
   α₀ ⟩ → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ...`, so the `∈-induction` descends
   with it.
4. `branch` derives the bound for each member: `δ∈suc = suc-ord oα₀ .fst
   {x = α} {y = δ} δ∈α α∈suc` (`:546`), transitivity of the successor
   ordinal. The IH at `δ` is then applied with `δ ∈ sucV α₀` in the
   `δ ≡ ω` and `ω ∈ δ` branches (`:549-556`).
5. At a finite member `δ ∈ ω`, the branch uses `fin-inj` and never
   invokes the IH (`:548`), so `sq δ` is never demanded there, exactly as
   `[LJ-1.116]` traced.

The bound is the narrowest the bodies support. The top step demands
`sq α₀` itself, so the bound cannot be "δ < α₀" only. Every infinite
member of the descent satisfies `δ ∈ sucV α₀`, and the finite members
never demand anything. A bound stated at the step's own target alone
(`α ∈ sucV α`) is always true, which would be no restriction. So the
site-relative bound `δ ∈ sucV α₀` is the one the bodies support. This
last sentence is **INFERRED** (a machine cannot certify "narrowest");
the demand trace itself is **MEASURED** by reading at `file:line`.

The `[LJ-1.114]` truncation threading was not attempted; the restriction
makes the truncation unnecessary at the site (section 3).

## 2. WHERE IT LANDS

**`sq` moves out of `Devlin55`'s telescope into `BoundedSubsetAt`, which
names the site `α`.** `Devlin55` (`src/L/BoundedSubset.lagda.md:1362`)
has no `α` parameter, so the restricted `sq` cannot stay there. The new
parameter sits next to `α` in `BoundedSubsetAt` (`:1391-1393`):

```agda
(sq : (δ : S) → ⟨ δ ∈ˢ sucV α ⟩ → (⟨ δ ∈ˢ ω ⟩ → Empty.⊥)
    → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
        ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y))
```

The `L.StageCardinal` instantiation moves with it: `module SC =
L.StageCardinal {ℓ} lem α ordα sq` (`:1399`), and the local
`stage-card-upper` is the restricted one (`:1402-1404`). `Devlin55`
keeps only `absorbs-subset` (`:1363-1365`), which already quantifies its
own `α` and is site-agnostic. The two sq-consumers in the body use the
restricted supply at the site: `CodeCount`'s `Bound`
(`module B = SC.Bound α ordα α∉ω (sq α (self∈sucV α) α∉ω)`, `:1429`)
and `code-inj` (`:1532`), both with the bound supplied by
`self∈sucV α`.

`Upper.stage-card-upper` keeps its three public uses' conclusion; its
statement now takes the bound it needs:

```agda
stage-card-upper : (α : S) → IsOrd α → ⟨ α ∈ˢ sucV α₀ ⟩
                 → (⟨ α ∈ˢ ω ⟩ → Empty.⊥) → ⟪ Lset α ⟫ ↪ ⟪ α ⟫
```

(`src/L/StageCardinal.lagda.md:564-565`.) The consumer calls it at the
site with `self∈sucV α` as the bound (`src/L/BoundedSubset.lagda.md:
1532`), and `stage-card-upper = ∈-induction step` (`:566`) closes with
the threaded `P`.

## 3. THE SITE SUPPLY

**At `α₀ = ω` the demand is only `sq ω`, and the honest ℕ pairing
supplies it; the site instance is machine-checked.** The supply is built,
not assumed (C-38):

```agda
sqω : (δ : S) → ⟨ δ ∈ sucV ω ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → pairing δ
sqω δ δ∈suc inf = go (ord-tri δ oδ ω ω-ord)
```

(`src/ProbeLJ1117A.agda:57-58`.) The only live case is `δ = ω`: a
finite `δ` closes by `inf δ∈ω`, and `ω ∈ δ` is refuted through the
bound `δ ∈ sucV ω` (`:59-68`). The pairing at `ω` is the delivered
`NumeralPresentation.pairω`/`pairω-inj`
(`src/ProbeLJ1106A.agda:127-137`).

The machine-checked instance, GREEN at the C-12 cap, one process:

| check | statement | where |
|---|---|---|
| the restricted supply | `sqω` from `pairω`/`pairω-inj` | `src/ProbeLJ1117A.agda:57` |
| the restricted module at the site | `SC = L.StageCardinal {ℓ} lem ω ω-ord sqω` | `:74` |
| the site's stage-card-upper | `up-ω = Up.stage-card-upper ω ω-ord (self∈sucV ω) (∈-irrefl ω)` | `:77-78` |
| the CodeCount-side count | `count-ω`, `Bound`'s `formula-bound` over `⟪ Lset ω ⟫` | `:80-85` |

The two checked terms are exactly the two sq-consumers of the master's
body: `code-inj`'s `stage-card-upper α ...` (`src/L/BoundedSubset.lagda.md:
1532`) and `CodeCount`'s `Bound` (`:1429`).

The full `BoundedSubsetAt` instance still does not close, and not because
of `sq`: `absorbs-subset`, `levelIn` and `cover` remain hypotheses
(`src/L/BoundedSubset.lagda.md:1363-1365`, `:1410-1413`), the same
boundary as `[LJ-1.94]` and `[LJ-1.116]` recorded. The sq-dependent part
is what this dispatch measures, and it closes.

## 4. THE C-40 SECTION

`git grep -l "StageCardinal\|BoundedSubset" src/` names three files.
All three were checked, one agda process at a time, and all three are
GREEN:

| consumer | where it uses the masters | result |
|---|---|---|
| `src/L/StageCardinal.lagda.md` | the changed master itself | GREEN after, 0.85-0.89 s, 3-4 runs |
| `src/L/BoundedSubset.lagda.md` | instantiates `L.StageCardinal` at `:1399` | GREEN after, 2.12-2.19 s, 3 runs |
| `src/Everything.lagda.md` | imports both at `:369`, `:374` | GREEN, whole import closure, 2.43-2.80 s, two runs |

`Devlin55` has no instantiation anywhere in the tree (`rg Devlin55` hits
only `src/L/BoundedSubset.lagda.md`), so no site consumer exists outside
the probe; the probe is the acceptance test (section 3). `Everything`
imports both masters and no other file does, so the C-40 list is
complete.

## 5. CONCLUSIONS

No theorem's conclusion changed. `Devlin55.theorem : ⟨ x ∈ˢ Lset κ ⟩`
(`src/L/BoundedSubset.lagda.md:1623`) is byte-identical. The only
changes are hypothesis-domain moves: `sq` is bounded by `sucV α₀`, and
`Upper.stage-card-upper` carries the bound premise its descent needs.
`absorbs-subset`, `levelIn` and `cover` are unchanged hypotheses.

## 6. THE C-39 SECTION

No brief prohibition blocked a route; the goal route itself landed.
Prohibitions audited:

- **Do not touch `src/L/Condensation*`**: no edit. `L.BoundedSubset`
  imports `L.Condensation` (`src/L/BoundedSubset.lagda.md:29`) and
  typechecks it, read-only. The probe imports `L.StageCardinal`
  directly, whose closure is Condensation-free, the same door as
  `[LJ-1.106]`, `[LJ-1.107]` and `[LJ-1.116]`.
- **Do not touch `src/L/Coding/` or `src/V/`**: no edits. `BoundedSubset`
  gained one import line (`open import V.Model {ℓ} using ( self∈sucV )`,
  `:877`); `V.Model` is not edited.
- **Do not weaken any theorem's conclusion**: respected, section 5.
- **Do not re-attempt the truncation threading**: not attempted; the
  restriction makes the truncation unnecessary at the site.
- **Never `src/Everything.lagda.md`**: typechecked only (the C-40
  consumer check); not edited.
- **Never `make check`**: not run; the individual gates of section 11
  were run instead.

## 7. THE NEGATIVES AND THEIR STATUS

1. "The unconstructible case never arises at the site": **MEASURED
   TRUE**. The demand set at `α₀ = ω` is `{ω}` (`[LJ-1.116]` section 1),
   and `sqω` supplies it from the honest pairing
   (`src/ProbeLJ1117A.agda:57-68`, GREEN).
2. "The induction never demands `sq` at a finite ordinal": **MEASURED
   TRUE** by reading. The branch's finite case uses `fin-inj` and never
   invokes the IH (`src/L/StageCardinal.lagda.md:548`); the restricted
   supply's finite case closes by `inf δ∈ω`
   (`src/ProbeLJ1117A.agda:69`).
3. "The bound `δ ∈ sucV α₀` is the narrowest the bodies support":
   **INFERRED** (no machine can certify narrowest). The demand trace is
   measured at `file:line` (section 1); the top step's demand is at
   `α₀` itself, and the descent reaches every infinite member below it.
4. "The J tower inherits the restricted modules unchanged":
   **INFERRED** (no J tower exists in this tree, same as `[LJ-1.107]`).
   The module is site-parameterized and tower-generic; a J consumer
   would instantiate it at its own site with its own `sq` supply.
5. "The whole `BoundedSubsetAt` instance closes": **INFERRED FALSE**
   today as a module instantiation: `absorbs-subset`, `levelIn` and
   `cover` are still hypotheses (`src/L/BoundedSubset.lagda.md:1363-
   1365`, `:1410-1413`). The sq part is not the blocker; this dispatch
   measured that part only.
6. The `check-unbound-hyp.py` flag on `LimitStep`'s `ih`
   (`src/L/StageCardinal.lagda.md:281`, rule 3, "m are free") is
   **PRE-EXISTING**: the `ih` parameter line is byte-identical at HEAD
   (`git diff` shows no change to it). The checker is advisory
   (`dev/LESSONS.md` C-38); `ih` is supplied by `branch`, never by an
   instantiation of the module.

## 8. DD4

The restricted module stays generic: the site `α₀` is a module
parameter, and the supply content is the same tower-generic pairing
mathematics. The two proofs share the same signatures, now with `sq`'s
domain bounded by the site. **A restricted hypothesis is a weaker
demand on both towers**, and the J half is **INFERRED** (no J tower in
this tree): a J consumer inherits the site-parameterized `StageCardinal`
unchanged and instantiates it at its own site. Nothing in the change
forks the shared chapter; the restriction is a domain bound, not a
second statement.

## 9. THE COST QUESTION

Measured under the archive's convention (import cache warm, own content
cold), one agda process at a time, load 3.5-5.0 / 3.6-4.4 / 4.3-4.6, four
users:

| master | before (archive `[LJ-1.114]` section 2, same convention) | after, 3-4 runs | run-to-run spread |
|---|---:|---:|---:|
| `StageCardinal` | 1.65-1.76 s | 0.85-0.89 s | 0.04 s after; 0.11 s before |
| `BoundedSubset` | 2.20-3.28 s | 2.12-2.19 s | 0.07 s after; 1.08 s before |

The before figures come from a different session at load 3.0-5.4, so a
delta claim across sessions is a hypothesis, not a controlled pair
(P-l). The `StageCardinal` drop of about 0.8 s is larger than either
session's own spread; the `BoundedSubset` change is inside the archive's
spread, so no solid delta is claimed for it. A first run after a pause
can land higher (1.74 s and 2.32 s were observed once each and are not
repeated by the spread runs); the table reports the repeated figures.
`ProbeLJ1117A` checks at 1.42-1.48 s, 3 runs, same load. `Everything`
(whole closure) at 2.43-2.80 s, two runs. The wall protocol was
respected: every check returned, none was killed.

## 10. ARCHIVE USED

- `_build/lj-1.116-report.md`, read WHOLE. TOOK the demand trace
  (section 1), the two `Init` refutations, the omega-site check shape,
  and the boundary at `BoundedSubsetAt`.
- `src/ProbeLJ1116A.agda`, read WHOLE. TOOK the probe shape for the
  site checks (`sqω`, `up-ω`, `count-ω`), restated against the
  restricted module.
- `_build/lj-1.114-report.md`, read WHOLE. TOOK the wall and its cause;
  did not repeat the threading.
- `_build/lj-1.111-report.md`, read WHOLE. TOOK the truncation
  elimination points and the C-40 reading of `Devlin55`.
- `_build/lj-1.94-report.md` and `src/ProbeLJ194A.agda`, read WHOLE.
  TOOK the site shape (`α = ω`) and the boundary hypotheses.
- `src/L/StageCardinal.lagda.md`, read WHOLE. TOOK the `sq` parameter
  (`:15`), `LimitStep` (`:277-283`), `Upper` (`:496-566`), `Bound`.
- `src/L/BoundedSubset.lagda.md`, read `:1361-1626` (Devlin55 whole).
  TOOK `code-inj` (`:1532`), `CodeCount` (`:1429`), the site telescope
  (`:1388-1413`), `theorem` (`:1623`).
- `src/L/Ordinal.lagda.md`, read `:83-104` and `:221-222`. TOOK
  `suc-ord`, `mem-ord`, `ω-ord`.
- `src/V/Model.lagda.md`, read `:218-237`. TOOK `∈sucV-elim`,
  `∈sucV-inl`, `self∈sucV`.
- `src/L/Constructible.lagda.md`, read `:83-145`. TOOK `IsOrd`,
  `isTransV`, `isPropIsOrd`.
- `dev/LESSONS.md`, read WHOLE D-30 (`:3332`), C-38 (`:3427`), C-39
  (`:3521`), C-40 (`:3602`), C-36 (`:3284`), D-1 (`:1038`), D-8
  (`:1377`), D-10 (`:1316`), P-l (`:2305`), C-35 (`:3200`), D-29
  (`:3242`), D-26 (`:1676`), and the `--for build` and `--for rewrite`
  bundles via `scripts/rules.py`.

## 11. LITERATURE USED

Banked. `[LJ-1.116]` settled what Devlin assumes; nothing spent.

## 12. GATES

- `src/L/StageCardinal.lagda.md`: GREEN, 0.85-0.89 s, 3-4 runs.
- `src/L/BoundedSubset.lagda.md`: GREEN, 2.12-2.19 s, 3 runs.
- `src/Everything.lagda.md`: GREEN, whole import closure,
  2.43-2.80 s, two runs.
- `src/ProbeLJ1117A.agda`: GREEN, 1.42-1.48 s, 3 runs, at the C-12 cap,
  one process at a time. 72 non-blank lines. Zero hits for `postulate`,
  `TERMINATING`; no holes.
- `scripts/check-fences.py --check`: clean, 92 masters.
- `scripts/lint-prose.py --check`: exit 0 on both masters, the probe and
  this report.
- `scripts/lint-agda.py --check`: exit 0 on both masters and the probe.
- `scripts/check-unbound-hyp.py`: clean on the probe; flags the
  pre-existing `LimitStep.ih` shape in `StageCardinal` (section 7, item
  6).
- `scripts/ledger.py --brief`: standing 28,425 lines over 85 masters,
  measured from HEAD.
- `make check` not run (forbidden). DD23: no mathematical prose changed;
  the diffs are code only.
- Working tree: `git status` shows only the two in-scope masters
  modified, plus the ignored probe and this report. No commit, no push.
  Every agda invocation returned; none was left alive.
