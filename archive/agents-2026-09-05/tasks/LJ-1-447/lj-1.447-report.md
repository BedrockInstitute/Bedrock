# LJ-1.447 report: the descent split at both least cardinals

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-447/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-447/Probe447.agda`:

    descent-both :
        (residue : (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
                 → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
                 → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩)
      → (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

W2 (from DD4): write the mathematics once at a generic carrier and
instantiate it. Answered in section 5.

## FOUR PREDECESSOR VERDICTS, BEFORE ANY AGDA

Quoted from the reports the brief names. Each is GO. None names the
statement FALSE. I take the type from the probe that typechecked.

`agents/tasks/LJ-1-421/lj-1.421-report.md:53`:

    **GO.** `d := κ` serves. `descent-from-data` typechecks

Delivered type, `agents/tasks/LJ-1-421/Probe421.agda:111-118`:

    descent-data : (x d : S) (ox : IsOrd (fst x))
                 → ⟨ fst d ∈ˢ fst x ⟩
                 → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫
                 → sq (fst d)
                 → sq (fst x)

Case 3 of that file, `agents/tasks/LJ-1-421/Probe421.agda:246-250`:

    by-init : fst κ ≡ x → sq x
    by-init κ≡x =
      subst sq κ≡x
        (via-col-square (fst κ)
          (init-at-kappa a ox (ω∈κ κ≡x) (members κ≡x)))

`agents/tasks/LJ-1-432/lj-1.432-report.md:63`:

    **GO.** `descent-case4-coded` typechecks

Delivered type, `agents/tasks/LJ-1-432/Probe432.agda:155-159`:

    descent-case4-coded :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

`agents/tasks/LJ-1-433/lj-1.433-report.md:51`:

    **GO.** `init-fails-below` typechecks

Delivered type, `agents/tasks/LJ-1-433/Probe433.agda:146-149` as named
in that report at `:8-14`:

    init-fails-below :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ x ⟩
      → Init x → Empty.⊥

`agents/tasks/LJ-1-406/lj-1.406-report.md:13`:

    **GO.** The obligation typechecks (`agents/tasks/LJ-1-406/Probe406.agda:180-190`,

Delivered type, `agents/tasks/LJ-1-406/Probe406.agda:180-185`:

    init-at-kappa :
        (a : S) (oa : IsOrd (fst a))
      → ⟨ ω ∈ˢ fst (κL a oa) ⟩
      → (ih : (β : V ℓ) → IsOrd β → ⟨ β ∈ˢ fst (κL a oa) ⟩
            → (⟨ β ∈ˢ ω ⟩ → Empty.⊥) → ∥ sq β ∥₁)
      → Init (fst (κL a oa))

No predecessor is NO-GO. I did not stop. I did not inhabit a FALSE type.

## D-10, BEFORE ANY AGDA

The four-case account, worked on paper. Split first on the coded
cardinal, then on the ambient one inside the equality branch. Each
cardinal lies in `sucV x` (premise 7, `Probe437.agda:98`, and the
selected-index line `Probe430.agda:96-98`). The successor split has two
branches and no third. There is no fourth case.

1. `fst (κC a ox) ∈ x`. PAID. It is `[LJ-1.432]`'s
   `descent-case4-coded` at this `x`
   (`Probe432.agda:155-168`). The induction hypothesis that type
   wants is DATA, and this telescope supplies it
   (`Probe432.agda:158-160`). Membership is the inr branch of the
   coded split. The ambient split is not consulted.

2. `fst (κC a ox) ≡ x` and `fst (κL a ox) ≡ x`. PAID. It is
   `[LJ-1.421]`'s `by-init`: `via-col-square` applied to
   `init-at-kappa`, then `subst sq` (`Probe421.agda:246-250`).
   Truncate the induction hypothesis with `∣_∣₁` at the call, exactly
   as `members` does (`Probe421.agda:241-243`). `[LJ-1.406]` is GO on
   `init-at-kappa` from a truncated IH. Conjunct 4 is not re-measured.

3. `fst (κC a ox) ≡ x` and `fst (κL a ox) ∈ x`. VACUOUS UNDER
   `residue`. The hypothesis at this `x` gives
   `fst (κC a ox) ∈ˢ x`. The coded equality rewrites the left side
   and yields `⟨ x ∈ˢ x ⟩`. `∈-irrefl` (`src/V/Hierarchy.lagda.md:155`)
   closes it. Nothing inhabits `residue`. Nothing weakens it to a
   truncation.

4. There is no fourth case. Each cardinal is a member of `sucV x`.
   Trichotomy against `x` then has `∈`, `≡`, or the reverse `∈`. The
   reverse is refuted by the cycle-or-self argument in
   `kappa-decides` (`Probe421.agda:194-204`), written once at a
   generic member of `sucV x` (W2) and instantiated at both
   cardinals.

The account is the brief's account. I did not add a hypothesis to make
a case close. `residue` is an argument of the obligation, not a new
principle I claim.

Corrected target: none. Original target stands. The four-case account
was not false on paper. W3 measured that the two splits share a
carrier. The term inhabits the account.

## VERDICT

**GO.** `descent-both` typechecks
(`agents/tasks/LJ-1-447/Probe447.agda:207-257`, exit 0, median 1.81 s
on three forced rechecks) and PASSes the program's witness meter
(`python3 scripts/pod/witness.py --code LJ-1-447 --brief
agents/tasks/LJ-1-447/LJ-1.447.md`, exit 0, 1.65 s, 0 UNRESOLVED of 1,
`probe_red=False`). `.venv/bin/python` is absent in this worktree. The
witness meter ran under `python3`. I added no dependency.

I did not write `review-of-descent-both.md`. The verdict is GO.

A GO says the descent runs on DATA under one named hypothesis. It does
not run the band induction. It does not touch `src/Landmarks.lagda.md`.
It does not close the campaign. It does not claim a trophy.

## 1. What was built

All in `agents/tasks/LJ-1-447/Probe447.agda`, module
`LJ-1-447.Probe447 {ℓ} (lem)`.

- `isL-ord`, sealed (`:59-61`). Same one line as `Probe437.agda:67-69`.
- `in-suc-decides` (`:65-81`). W2: the successor split, once, at a
  generic member of `sucV x`. Shape of `Probe421.agda:185-204`.
- The ambient least cardinal, five projections, sealed
  (`:89-106`). Same seal as `Probe437.agda:90-107`. This site does
  not re-measure the wall. `κ-injL` and `κ-min-atL` are sealed and
  not spent.
- The coded selection, rebuilt from `Probe431.agda:108-131`
  (`:114-160`). Generic in the bound `γ`. `nonempty-coded` is a
  module hypothesis. `κC` and `κC∈suc` are sealed at the export so
  `fst κC` is an atom. I did not import a probe. I did not rebuild
  `coded-to-arrow-at` (`Probe431.agda:100-106`, `:133-134`): neither
  W3 nor the obligation spends the DATA arrow, and
  `descent-case4-coded` is a hypothesis that already carries it.
- W3: `both-in-suc` (`:167-174`).
- `κC-ord` (`:178-180`), restated from `Probe430.agda:96-98` at the
  sealed `κC`.
- Three module hypotheses (`:187-204`) at the types the GO probes
  delivered: `init-at-kappa`, `descent-case4-coded`, `descent-data`.
- The obligation: `descent-both` (`:207-257`). `residue` is its first
  argument. I did not inhabit it.

## 2. W3: `both-in-suc`, first

**GO.** The two splits sit over the same `sucV x`.

Left half is `κ∈sucL` (`Probe437.agda:98-100`, rebuilt `:96-97`).
Right half is `κC∈suc`, one line from the selected index, in the
shape `Probe430.agda:96-98` uses for ordinality: `member (sucV (fst a))
(fst selected)` at `:151-152`, sealed with `κC` at `:158-160`.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`, set
on the pane, untouched. One Agda process. Dependencies warm. The probe
interface was deleted before every kept recheck
(`_build/2.8.0/agda/agents/tasks/LJ-1-447/Probe447.agdai`).

First landing, obligation omitted: 1.66 s, peak RSS 395640832 bytes,
exit 0, printed `Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.67 | 395689984 |
| `runs/w3-3.out` / `w3-3.time` | 1.65 | 395657216 |
| `runs/w3-4.out` / `w3-4.time` | 1.64 | 395657216 |

Median wall **1.65 s**. Median peak RSS **395657216 bytes**. No heap
event.

EIGHT non-blank code lines for `both-in-suc` (type plus body). The
estimate was about 10 lines and under 3 seconds. Measured, it is
smaller and in the same second. Nothing is funded against the
estimate. The two halves sit over the same `sucV x`. The four-case
account has its first step.

P-l did not fire: the types name the sealed atoms `κL` and `κC`, not a
transparent `sucV`-chain. `sucV x` is in the statement the brief
wrote.

## 3. The obligation

`descent-both` (`:207-257`) splits first on the coded cardinal, then
on the ambient one inside the equality branch.

| case | supplier | file:line |
|---|---|---|
| `fst κC ∈ x` | `descent-case4-coded` at this `x`, IH as DATA | `:252` |
| `fst κC ≡ x` and `fst κL ≡ x` | `via-col-square` of `init-at-kappa`, `subst sq`; IH truncated with `∣_∣₁` | `:237-241`, `:231-235` |
| `fst κC ≡ x` and `fst κL ∈ x` | `residue` rewrites to `⟨ x ∈ˢ x ⟩`, `∈-irrefl` | `:243-249`, spent at `:257` |

The coded split is `in-suc-decides` at `κC` (`:215`). The ambient
split is `in-suc-decides` at `κL` (`:253`). Same term, two
instantiations.

**46 non-blank code lines** for `descent-both` (type plus body). The
brief's estimate was about 30, a comparable of SHAPE from one case of
`[LJ-1.432]` plus `[LJ-1.421]`'s three-line `splitOwn`. The extra is
the plumbing of two sealed cardinals and the vacuous case. Nothing is
funded against the estimate.

Nothing was weakened. Nothing failed to close. `residue` stays an
argument.

## 4. Extra hypotheses

| hypothesis | delivered type | spent? |
|---|---|---|
| `nonempty-coded` (`:133-136`) | `[LJ-1.431]`'s module hypothesis, lifted to a function of `a` | yes, at `Sel.selected` `:146` |
| `init-at-kappa` (`:188-193`) | `Probe406.agda:180-185` | yes, case 2 at `:241` |
| `descent-case4-coded` (`:194-198`) | `Probe432.agda:155-159` | yes, case 1 at `:252` |
| `descent-data` (`:199-204`) | `Probe421.agda:111-118` | no. Taken because the brief named it. Case 1 spends the 432 wrapper, not this name. |
| `residue` (`:208-210`) | argument of the obligation, not a predecessor delivery | yes, case 3 at `:247`. Not inhabited. |

Rebuilt, not hypothesized:

| term | copied from |
|---|---|
| `κL`, `κoL`, `κ∈sucL`, `κ-injL`, `κ-min-atL` | `Probe437.agda:90-107` |
| `κC`, `κC∈suc` | `Probe431.agda:108-131`, sealed at the export |
| `κC-ord` | `Probe430.agda:96-98` |
| `in-suc-decides` | `Probe421.agda:185-204`, generic in `d` |

I did not rebuild `init-at-kappa`. I did not re-measure conjunct 4 of
`Init`. I did not import a probe.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ`. The bound `γ` is generic. `κL` and `κC` are generic in `a`.
`in-suc-decides` is generic in the member `d` of `sucV x` and is
instantiated at both cardinals (`:215`, `:253`). `descent-both` is
generic in `x`. No cardinal, no band and no numeral is named anywhere
in the file except `ω`, which is where the obligation's own statement
puts it. There is no fixed form to report.

W4 does not fire: no module was retired.

## 6. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 first, obligation omitted: median **1.65 s**, median peak RSS
  **395657216 bytes**, exit 0. Section 2.
- Full file, first check after the obligation landed: 1.84 s, exit 0,
  peak RSS 421806080 bytes, printed `Checking`. `runs/full-1.out` /
  `full-1.time`.
- Full file, three forced rechecks (probe interface deleted before
  each run, dependencies warm): 1.81 s, 1.81 s, 1.81 s. Peak RSS
  421822464, 421773312, 421806080 bytes. Median wall **1.81 s**.
  Median peak RSS **421806080 bytes**. Exit 0 every time. Each printed
  `Checking`. `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 1.65 s, 0 UNRESOLVED
  of 1, `probe_red=False`. `runs/witness-1.out`.
- `lint-agda.py --check` on the probe: exit 0.
- No heap event. The two opaque seals did not fire the unfolding
  style `[LJ-1.398]` met (`dev/pod/audit-2026-08-20.md:128-133`).

## WHAT IS LEFT

`residue` as a type, at `agents/tasks/LJ-1-447/Probe447.agda:208-210`:

    (y : V ℓ) (oy : IsOrd y) → ⟨ ω ∈ˢ y ⟩
  → ⟨ fst (κL (y , isL-ord y oy) oy) ∈ˢ y ⟩
  → ⟨ fst (κC (y , isL-ord y oy) oy) ∈ˢ y ⟩

In words: when the ambient least cardinal of an infinite ordinal lies
strictly below it, so does the coded one.

`[LJ-1.441]`'s obligation, at
`agents/tasks/LJ-1-441/Probe441.agda:97-101`:

    amb-to-coded-at-least :
        (a : S) (oa : IsOrd (fst a)) → ⟨ ω ∈ˢ fst a ⟩
      → ⟨ fst (κL a oa) ∈ˢ fst a ⟩
      → (⟨ fst (κL a oa) ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ Σ[ F ∈ S ] InjCode F a (κL a oa) ∥₁

That conclusion names `InjCode` at `κL a oa`. It asks for a code AT
the ambient least cardinal. `residue`'s conclusion is membership of
`κC` in `y`. It asks for a code at SOME member, the coded selection,
and not at `κL`. **`residue` is the weaker statement.** Evidence: the
two conclusions at `Probe447.agda:210` and `Probe441.agda:101`. 441
returns `InjCode F a (κL a oa)`. 447 returns `⟨ fst (κC ...) ∈ˢ y ⟩`.

`[LJ-1.441]` is NO-GO on the stronger statement
(`agents/tasks/LJ-1-441/lj-1.441-report.md:53`). C-42: that refutation
measures that site. It does not measure `residue`. Nothing in this
tree proves `residue` and nothing in this tree refutes it. DD9: a new
principle is stated as a type. This file states it and spends it.

After this GO, the counting leg reduces to that one statement about
two ordinals. The band induction is not run. `[LJ-2.5]` is not this
task.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18".
  Declined. The live producer is `dev/pod/queue.toml`. This probe does
  not consult the archived dispatch index.
- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route".
  Declined. This task measures a descent split on the live route. It
  does not consult the retired-route journal.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**". Read to resolve the injected archive
  paths. This task does not retire a module.
- `archive/dev/DD-archived.md:1`, read: "# THE `DD` RULING SERIES, archived
  in full 2026-08-18". Declined. This task does not change a DD row.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Used to keep case 2's induction hypothesis truncated: a cardinal
  inequality is a truncated injection, and `init-at-kappa` takes
  `∥ sq β ∥₁`. The DATA IH is truncated with `∣_∣₁` at `:235`, exactly
  as `Probe421.agda:241-243` does.
- `dev/literature/truncation-and-selection.md:148`, read: "delivers the
  least INDEX untruncated, and any payload it delivers with the". Used
  with `:149` "index is a proposition. **A data payload does not come
  out.**" W3 does not ask `leastOf` for a payload: both halves are
  membership of a selected index. The DATA arrow stays inside the
  432 hypothesis.
- `dev/literature/devlin-II5.md:72`, read: "> 5.2 Theorem (The
  Condensation Lemma). Let α be a limit ordinal. If". Declined.
  Condensation codes a collapse of a hull. This task splits two
  selections already in the tree. It does not ask for a condensation.
- `dev/literature/terms-2026-08.md:1`, read: "# The terminology dossier:
  fourteen renderings for the owner's ruling". Not used. No glossary
  work in this task.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the
  rud route, pinned from the collected literature". Not used. This
  probe is the L-tower band step, not the rud-route architecture.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic
  geology sources and the five questions". Not used. Geology is not
  this measurement.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import a probe.
- I did not inhabit `residue`. I did not postulate it. I did not
  weaken it to a truncation.
- I did not rebuild `init-at-kappa`. I did not re-measure conjunct 4
  of `Init`.
- I did not write `coded-to-arrow-at`. The obligation does not spend
  that arrow.
- I did not write `review-of-descent-both.md`. The verdict is GO.
- I did not claim the campaign closes. I did not claim a trophy.
- I did not touch `src/Landmarks.lagda.md`.
