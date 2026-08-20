# LJ-1.407 report: the truncated square law at every band ordinal, no residue

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-407/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-407/Probe407.agda`, at a GENERIC
band, with `init-at-kappa` taken as a module hypothesis at the type
`[LJ-1.406]` names:

    sq-trunc :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥)
      → ∥ sq δ ∥₁

## VERDICT

**GO.** The obligation typechecks (`agents/tasks/LJ-1-407/Probe407.agda`,
exit 0, median 1.77 s on three forced rechecks) and it PASSes the program's
witness meter (`scripts/pod/witness.py --code LJ-1-407 --brief
agents/tasks/LJ-1-407/LJ-1.407.md`, exit 0, 1.64 s, 0 UNRESOLVED of 1).
Every case closed. There is no residue.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that collection.
It does not start phase 3. No Boundary clause is in conflict.

## 1. What was built

All in `agents/tasks/LJ-1-407/Probe407.agda`, module
`LJ-1-407.Probe407 {ℓ} (lem) (α₀) (oα₀)`.

- `isL-ord`, sealed (`:66-68`), `mem-incl` (`:72-85`), `comp-inj` (`:88-90`).
- The ambient least cardinal, sealed at the call site: `κL`, `κoL`,
  `κ∈sucL`, `κ-injL` (`:99-111`). `κ-injL` is in the same opaque block, so
  its target is the sealed `κ`.
- W3: `kappa-not-fin` (`:117-133`).
- `kappa-decides` (`:140-162`), the split copied from
  `agents/tasks/LJ-1-398/Probe398.agda:141`.
- `descent-core` (`:169-189`), rebuilt from
  `agents/tasks/LJ-1-390/Probe390.agda:110`. Not imported. Not a hypothesis.
- `band-ord` (`:193-196`).
- `init-at-kappa`, the one module hypothesis, at the type `[LJ-1.406]`
  names (`:203-209`). `[LJ-1.406]` is not in this worktree. I did not import
  `Probe406` and I did not rebuild it.
- `Goal`, `step`, `sq-trunc` (`:214-215`, `:217-260`, `:262-265`).
- `ConsumerShape` and `plugs-in` (`:273-280`).

## 2. W3: `kappa-not-fin`, first

**GO.** The brief named the infiniteness of the descent target as the widest
unmeasured term, because `[LJ-1.404]` refuted `⟨ ω ∈ fst κ ⟩`
(`agents/tasks/LJ-1-404/lj-1.404-report.md:18-24`). The probe is
`kappa-not-fin` (`Probe407.agda:117-133`).

```agda
kappa-not-fin : (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
              → (⟨ fst (κL (x , isL-ord x ox) ox) ∈ˢ ω ⟩ → Empty.⊥)
```

Membership is `∈ˢ`, matching the brief's display and `κ-min-at` at
`src/L/Cardinal.lagda.md:140`. The two convert. The body spends `κ-injL`
under `PT.rec` into `Empty.⊥`, composes `mem-incl` at `ω` with the arrow,
and applies `finite-excl-ω` (`src/L/InjChain.lagda.md:153`). **SEVENTEEN
code lines.** Stated and run alone, before the recursion: first check
**1.75 s**, then 1.73 s and 1.75 s, exit 0 every time.
`runs/w3-{1,2,3}.out`. The first run printed `Checking`. That is the
alone-run price.

## 3. The four cases, and each one closes

At an infinite site `x`, `step` splits by `ord-tri` against `ω`, then by
`kappa-decides`. It does **not** split on `IsCardinalL`. No `InjCode`, no
`InternalLeastCard`, and no `Ne⁺` appears in the file.

| case | supplier, and how it closes |
|---|---|
| `x ∈ ω` | refuted by the infinitude hypothesis; `:224` |
| `x ≡ ω` | `squareω`, transported, then `∣ ∣₁`; `:225` |
| `ω ∈ x` and `fst κ ≡ x` | `init-at-kappa` gives `Init (fst κ)`, `via-col-square` gives `sq (fst κ)` as data, transported along the equality, then wrapped; `by-init`, `:243-247` |
| `ω ∈ x` and `fst κ ∈ x` | `kappa-not-fin` shows the target is not finite; `IH (fst κ)` gives `∥ sq (fst κ) ∥₁`; `mem-incl` is the inclusion; `PT.map2` over `κ-injL` and the IH, with `descent-core` inside, gives `∥ sq x ∥₁`; `by-descent`, `:251-256` |

The `ih` that `init-at-kappa` needs is the recursion's own `IH`, with
membership transported along `fst κ ≡ x` (`members`, `:236-240`). The
`⟨ ω ∈ fst κ ⟩` that it needs is `ω ∈ x` transported along the same
equality (`ω∈κ`, `:233-234`).

**There is no fifth case and no residue.** `[LJ-1.398]` split on
`IsCardinalL` and that split produced its residue
(`agents/tasks/LJ-1-398/lj-1.398-report.md:55-70`). This assembly does not
take that split. Case 4 spends the truncated `κ-inj` directly, because the
conclusion is a proposition.

## 4. The consumer match, checked

The consumer takes `sq` as a module parameter with no ordinal certificate
(`src/L/StageCardinal.lagda.md:17-19`). `ConsumerShape` (`:273-277`)
repeats that type with `∥ ∥₁` around the Sigma and nothing else changed.
`plugs-in` (`:279-280`) discharges it. `sq δ` is the Sigma the chapter
writes (`src/L/Ordinal/SquareLaw.lagda.md:685-687`), judgmentally, so no
transport sits inside `plugs-in`. `band-ord` (`:193-196`) produces the
certificate the chapter does not ask for. The band argument is ignored at
the plug, exactly as `plugs-in` in `[LJ-1.398]` ignored it
(`agents/tasks/LJ-1-398/Probe398.agda:298-299`).

**Membership spelling.** `sq-trunc` and `ConsumerShape` use Cubical `_∈_`,
matching `L.StageCardinal` after `sucV` and `ω` are opened. The brief's
display uses `∈ˢ`. The two convert, as `[LJ-1.398]` already used. W3 and
the `init-at-kappa` telescope keep `∈ˢ`, matching `[LJ-1.406]` and
`κ-min-at`.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic in
`ℓ`. `α₀` and `oα₀` are the consumer's own parameters. Every term
quantifies over a generic `x : V ℓ`. `init-at-kappa` and `descent-core`
are generic in their site. No site, no ordinal and no numeral is named
anywhere in the file except `ω`, which is the base.

`descent-core` is rebuilt here (`:169-189`, 18 code lines) from the
delivered `[LJ-1.390]` term. It is not a second hypothesis. The only
module hypothesis is `init-at-kappa`.

## 6. The seal, and whether this site needed it

`[LJ-1.398]` measured an 8 GB heap wall at a transparent
`LeastCardInjL.κ` (`agents/tasks/LJ-1-398/lj-1.398-report.md:140-153`).
The brief ordered the same seal here. I sealed from the start: `κL`,
`κoL`, `κ∈sucL`, `κ-injL` (`:99-111`). The assembly was cheap (median
1.77 s). There was no heap event. **This site did not independently
measure a wall.** A measured cure does not transfer by analogy. I did not
spend a heap event to prove the seal was needed.

## 7. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root.

- W3 alone, three runs: 1.75 s, 1.73 s, 1.75 s. First run printed
  `Checking`. Median of the three **1.75 s**, exit 0. `runs/w3-{1,2,3}.out`.
- Full file, first check after the recursion landed: 1.82 s, exit 0,
  printed `Checking`. `runs/full-1.out`.
- Full file, three forced rechecks (the probe interface removed before
  each run, dependencies warm): 1.81 s, 1.76 s, 1.77 s. Median **1.77 s**,
  exit 0 every time. Each printed `Checking`.
  `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 1.64 s, 0 UNRESOLVED of 1,
  `probe_red=False`.

Estimate for the obligation: about 70 code lines, a comparable of SHAPE
from `[LJ-1.398]`'s 74 (`agents/tasks/LJ-1-398/lj-1.398-report.md:161-169`).
Measured, `Goal` plus `step` plus `sq-trunc` are **41 code lines**
(comments and blanks excluded). W3 adds 17. Nothing is funded against the
estimate.

## 8. What GO earns, and what is still owed

GO is the truncated square law at every band ordinal, conditional only on
`init-at-kappa`. The pairing is proved up to `∥ ∥₁`. Everything the
campaign has owed since `[LJ-1.384]` (`Ne⁺`, `AmbCard`, `InjCode`, the
placement, the coded square law) is then owed for exactly one reason: the
consumer wants the pairing as DATA and this proves it only up to a
truncation.

**What this task does not settle.**

- It does not pay `init-at-kappa`. `[LJ-1.406]` is not in this worktree.
  The type is taken as a bare hypothesis, as the brief ordered.
- It does not test whether `L.StageCardinal` accepts a truncated parameter.
  That is `[LJ-1.408]`.
- It does not produce an untruncated arrow at any ordinal.

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:955`,
  read: "the truncated square law `∥ sq α ∥₁` as its projection. It does
  not give the". The archived chapter already names the truncated shape
  this probe proves at every band ordinal.
- `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md`, declined:
  opened at the head only. The assembly does not consult the archived
  counting chapter.
- `archive/dev/JOURNAL-archived.md:1338`, read: "the cardinal step consumes
  is delivered CONDITIONAL on one named bound, the square law (an infinite".
  The bound that chapter named is the law this probe now supplies in
  truncated form.
- `archive/dev/TASKS-archived.md:82`, read: "| L3.32-T47 | Truncated square
  law at initial ordinals | DELIVERED | `_build/l3.32-t47-report.md` |".
  That row is the truncated law at *initial* ordinals. This probe is the
  same shape at every band ordinal.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**". Read to resolve the injected archived
  SquareLaw path.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`". A
  cardinal inequality is a truncated injection. That is why `κ-inj` is
  free once the conclusion is `∥ sq x ∥₁`.
- `dev/literature/devlin-II5.md`, not used: the condensation digest for
  the GCH endpoint. This probe assembles a recursion at a generic band,
  and no step consults a condensation argument. Opened at the head only.
- `dev/literature/digest.md:241`, read: "surjection g : α -> J_α^A when α
  is closed under Gödel pairing (SZ 1.17)." Not used: this assembly is
  the L-band truncated law, and the digest's pairing sentence was not
  spent.
- `dev/literature/j-hierarchy.md`, not used: notes on the J-hierarchy.
  This probe is the L-tower band recursion. Opened at the head only.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process.
- I did not write in `src/`.
- I did not import `Probe406`. I did not rebuild `init-at-kappa`.
- I did not split on `IsCardinalL`.
- I did not leave a residue.
