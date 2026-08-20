# LJ-1.413 report: the square law as DATA at every band ordinal, one residue

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-413/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-413/Probe413.agda`, at a GENERIC
band, with three module hypotheses, conclusion `sq δ` and no `∥ ∥₁`:

    sq-data :
        (δ : V ℓ) → ⟨ δ ∈ sucV α₀ ⟩ → (⟨ δ ∈ ω ⟩ → Empty.⊥) → sq δ

## VERDICT

**GO.** The obligation typechecks (`agents/tasks/LJ-1-413/Probe413.agda`,
exit 0, median 2.07 s on three forced rechecks) and it PASSes the program's
witness meter (`scripts/pod/witness.py --code LJ-1-413 --brief
agents/tasks/LJ-1-413/LJ-1.413.md`, exit 0, 1.56 s, 0 UNRESOLVED of 1).
The consumer parameter is DATA. There is no `∥ ∥₁` in the conclusion.
Case two and case three close as data. They do not hide a truncation.
The only residue is `amb-to-coded`.

The standing direction says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is still LJ-1 work. It does not start that collection.
It does not start phase 3. No Boundary clause is in conflict.

## 1. What was built

All in `agents/tasks/LJ-1-413/Probe413.agda`, module
`LJ-1-413.Probe413 {ℓ} (lem) (α₀) (oα₀)`.

- `isL-ord`, sealed (`:67-68`), `mem-incl` (`:72-85`), `comp-inj` (`:88-90`).
- W3: `descent-core` (`:101-121`) and `descent-data` (`:123-129`).
- The ambient least cardinal, sealed at the call site: `κL`, `κoL`,
  `κ∈sucL`, `κ-injL` (`:136-146`).
- `kappa-not-fin` (`:150-166`), rebuilt from `[LJ-1.407]`. The residue
  spends it.
- `kappa-decides` (`:173-195`).
- `band-ord` (`:199-202`). `band-down` (`:206-210`), rebuilt from
  `κ-min-at` (`src/L/Cardinal.lagda.md:145`). The motive does not carry
  the band, so `step` does not spend `band-down`. The helper is not
  carried into `coded-descent`.
- Three module hypotheses (`:219-236`): `init-at-kappa` at `[LJ-1.406]`'s
  type, `coded-descent` at `[LJ-1.412]`'s type, `amb-to-coded` as the
  brief names it. I did not import `Probe406`, `Probe407` or `Probe412`.
  I did not rebuild those three terms.
- `Goal`, `step`, `sq-data` (`:242-243`, `:245-307`, `:309-312`).
- `ConsumerShape` and `plugs-in` (`:319-326`).

## 2. W3: `descent-data`, first

**GO.** The brief named case four at data level as the widest unmeasured
term, because every delivered form of it ran under a truncation. The
probe is `descent-data` (`Probe413.agda:123-129`).

```agda
descent-data : (x d : S) (ox : IsOrd (fst x))
             → ⟨ fst d ∈ˢ fst x ⟩
             → ⟪ fst x ⟫ ↪ ⟪ fst d ⟫
             → sq (fst d)
             → sq (fst x)
```

Three payload hypotheses: membership, the descending arrow, `sq` at the
target. `ox : IsOrd (fst x)` is the recursion's own certificate.
`mem-incl` spends it. It is not a fourth payload. The body is one line:
`descent-core` on `mem-incl`. **SEVEN non-blank code lines** for
`descent-data`. `descent-core` beside it is **18 non-blank code lines**,
rebuilt from `agents/tasks/LJ-1-390/Probe390.agda:110`. Stated and run
alone, before the recursion: first check **1.58 s**, then 1.67 s and
1.67 s, exit 0 every time. `runs/w3-{1,2,3}.out`. The first run printed
`Checking`. That is the alone-run price. Median of the three **1.67 s**.

## 3. The four cases, and each one closes at data level

At an infinite site `x`, `step` splits by `ord-tri` against `ω`, then by
`kappa-decides`. It does **not** split on `IsCardinalL`. The residue
converts the ambient truncated arrow into `IsCardinalL a → Empty.⊥` and
hands that to `coded-descent`.

| case | supplier, and how it closes |
|---|---|
| `x ∈ ω` | refuted by the infinitude hypothesis; `:252` |
| `x ≡ ω` | `squareω`, transported. DATA. No wrap. `:253` |
| `ω ∈ x` and `fst κ ≡ x` | `init-at-kappa` gives `Init (fst κ)`, `via-col-square` gives `sq (fst κ)` as data, transported along the equality. DATA. No wrap. `by-init`, `:269-273` |
| `ω ∈ x` and `fst κ ∈ x` | `amb-to-coded` on `κ-injL` gives `IsCardinalL a → Empty.⊥`; `coded-descent` gives `d`, membership, infiniteness and the arrow as data; `IH` at `d` gives `sq (fst d)`; `descent-data` gives `sq x`. DATA. `by-descent`, `:278-303` |

The `ih` that `init-at-kappa` needs is the recursion's own `IH`, wrapped
into `∥ sq β ∥₁` (`members`, `:262-266`). That wrap is data into a
truncation. It is always possible. The result of case three is not
wrapped. The `⟨ ω ∈ fst κ ⟩` that `init-at-kappa` needs is `ω ∈ x`
transported along `fst κ ≡ x` (`ω∈κ`, `:259-260`).

**Case two and case three do not need a truncation that `[LJ-1.407]`
hid.** Both close as data. That is the measurement this task was
asked to make.

The infiniteness at the coded descent target comes from
`coded-descent`, in the consumer's spelling `⟨ fst d ∈ˢ ω ⟩ → Empty.⊥`
(`:294-295`). `[LJ-1.404]` refuted the other spelling.

## 4. The consumer match, checked

The consumer takes the pairing as a module parameter with no ordinal
certificate (`src/L/StageCardinal.lagda.md:17-19`). `ConsumerShape`
(`:320-323`) repeats that type with NO `∥ ∥₁`. `plugs-in` (`:325-326`)
discharges it with `sq-data`. `sq δ` is the Sigma the chapter writes
(`src/L/Ordinal/SquareLaw.lagda.md:685-687`), judgmentally, so no
transport sits inside `plugs-in`. `band-ord` (`:199-202`) produces the
certificate the chapter does not ask for.

**Membership spelling.** `sq-data` and `ConsumerShape` use Cubical `_∈_`,
matching `L.StageCardinal` after `sucV` and `ω` are opened. The brief's
display uses `∈ˢ`. The two convert. W3, the residue, and
`coded-descent` keep `∈ˢ`.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic in
`ℓ`. `α₀` and `oα₀` are the consumer's own parameters. Every term
quantifies over a generic `x : V ℓ`. The three hypotheses and
`descent-data` are generic in their site. No site, no ordinal and no
numeral is named anywhere in the file except `ω`, which is the base.

`descent-core` and `descent-data` are rebuilt here. They are not extra
hypotheses.

## 6. The residue, stated and not discharged (D-10)

Exact type used (`Probe413.agda:232-236`):

```agda
amb-to-coded :
    (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
  → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
  → (IsCardinalL x → Empty.⊥)
```

I did not try to prove it. I did not weaken it. `[LJ-1.414]` measures
its truth.

## 7. The motive, and whether the data form cost anything

`[LJ-1.407]`'s motive was `∥ sq x ∥₁`, a proposition. This motive is
`sq x`, a Sigma (`:243`). `∈-induction` accepted it. There was no heap
event. No conversion explosion. P-l and R-40 did not fire: the motive
does not name a transparent `sucV`-chain, and the band is not in the
type.

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, every dependency warm, from the
repository root.

- W3 alone, three runs: 1.58 s, 1.67 s, 1.67 s. First run printed
  `Checking`. Median of the three **1.67 s**, exit 0. `runs/w3-{1,2,3}.out`.
- Full file, first check after the recursion landed: 1.84 s, exit 0,
  printed `Checking`. `runs/full-1.out`.
- Full file, three forced rechecks (the probe interface removed before
  each run, dependencies warm): 1.79 s, 2.22 s, 2.07 s. Median **2.07 s**,
  exit 0 every time. Each printed `Checking`.
  `runs/full-recheck-{1,2,3}.out`.
- After deleting one unused `oκ` binding: 1.86 s, exit 0, printed
  `Checking`. `runs/full-2.out`.
- Witness meter, one obligation: PASS, exit 0, 1.56 s, 0 UNRESOLVED of 1,
  `probe_red=False`.

Against `[LJ-1.407]`'s median of 1.77 s
(`agents/tasks/LJ-1-407/lj-1.407-report.md:19`): this median is 2.07 s.
The spread is 1.79 s to 2.22 s. The data motive did not produce a wall
and did not change the order of magnitude. I do not claim a structural
cost from the Sigma. The extra third of a second sits inside run noise
at this site.

Estimate for the obligation: about 75 code lines, a comparable of SHAPE
from `[LJ-1.407]`'s `step` and `sq-trunc`. Measured, `Goal` plus `step`
plus `sq-data` are **55 code lines** (comments and blanks excluded).
W3 `descent-data` adds 7. Nothing is funded against the estimate.

The seal on `κL` is the same seal `[LJ-1.407]` used. This site did not
independently measure a wall. A measured cure does not transfer by
analogy.

## 8. What GO earns, and what is left

GO is the square law as DATA at every band ordinal, conditional on the
three hypotheses. The consumer's module parameter is delivered, up to
`amb-to-coded`.

**What is left, as a type:**

    amb-to-coded :
        (x : S) (ox : IsOrd (fst x)) → ⟨ ω ∈ˢ fst x ⟩
      → (d : S) → ⟨ fst d ∈ˢ fst x ⟩ → (⟨ fst d ∈ˢ ω ⟩ → Empty.⊥)
      → ∥ ⟪ fst x ⟫ ↪ ⟪ fst d ⟫ ∥₁
      → (IsCardinalL x → Empty.⊥)

## ARCHIVE USED

- `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:955`,
  read: "the truncated square law `∥ sq α ∥₁` as its projection. It does
  not give the". The archived chapter names the truncated shape
  `[LJ-1.407]` proved. This probe is the data shape the projection does
  not give.
- `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md`, declined:
  opened at the head only. The assembly does not consult the archived
  counting chapter.
- `archive/dev/JOURNAL-archived.md:1338`, read: "the cardinal step consumes
  is delivered CONDITIONAL on one named bound, the square law (an infinite".
  The bound that chapter named is the law this probe now supplies as data,
  up to the residue.
- `archive/dev/TASKS-archived.md:82`, read: "| L3.32-T47 | Truncated square
  law at initial ordinals | DELIVERED | `_build/l3.32-t47-report.md` |".
  That row is the truncated law at *initial* ordinals. This probe is the
  data law at every band ordinal.
- `archive/dev/LJ-dispatch-index.md`, declined: opened at the head only.
  The live producer is `dev/pod/queue.toml`. This probe does not consult
  the archived dispatch index.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**". Read to resolve the injected archived
  SquareLaw path.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`". A
  cardinal inequality is a truncated injection. That is why `κ-inj` is
  truncated at its definition site, and why a data motive cannot spend
  it with `PT.map2`. The residue is that gap.
- `dev/literature/digest.md:241`, read: "surjection g : α -> J_α^A when α
  is closed under Gödel pairing (SZ 1.17)." Not used: this assembly is
  the L-band data law, and the digest's pairing sentence was not spent.
- `dev/literature/j-hierarchy.md`, declined: notes on the J-hierarchy.
  This probe is the L-tower band recursion. Opened at the head only.
- `dev/literature/BIBLIOGRAPHY.md`, declined: opened at the head only.
  No citation from that list is spent.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not import `Probe406`, `Probe407` or `Probe412`.
- I did not try to prove `amb-to-coded`. I did not weaken it.
- I did not split on `IsCardinalL` as the recursion's own split.
