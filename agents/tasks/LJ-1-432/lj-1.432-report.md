# LJ-1.432 report: which case of the descent a coded arrow closes, and which it does not

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-432/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. I did not set `GHCRTS`. No heap event.

TARGET: build ONE term in `agents/tasks/LJ-1-432/Probe432.agda`, at a
GENERIC ordinal:

    descent-case4-coded :
        (x : V ℓ) (ox : IsOrd x) → ⟨ ω ∈ˢ x ⟩
      → ⟨ fst (κC (x , isL-ord x ox) ox) ∈ˢ x ⟩
      → ((y : V ℓ) → ⟨ y ∈ˢ x ⟩ → IsOrd y → (⟨ y ∈ˢ ω ⟩ → Empty.⊥) → sq y)
      → sq x

`κC` is a sealed module hypothesis with three properties, in the shape
`[LJ-1.421]` seals `κL` at `agents/tasks/LJ-1-421/Probe421.agda:125-135`.
The arrow arrives as data, not truncated.

The standing direction (`dev/pod/direction.md:37`) says one SRC collection
after LJ-1, not after `[LJ-2.5]`. This task is still LJ-1 work. It does not
start that collection. It does not start phase 3. No Boundary clause is in
conflict.

## D-10, BEFORE ANY AGDA

Read `agents/tasks/LJ-1-421/Probe421.agda:225-263`. Case 4 is
`by-descent` at `:252-259`. It supplies `descent-data`'s arguments
(`:111-118`) as follows.

| argument of `descent-data` | supplier in case 4 | file:line |
|---|---|---|
| `x : S` | packed `a = x , isL-ord x ox` | `Probe421.agda:231-232` |
| `d : S` | `κ = κL a ox` | `Probe421.agda:233-234` |
| `ox : IsOrd (fst x)` | the ordinal certificate of `x` | `Probe421.agda:226` |
| `⟨ fst d ∈ˢ fst x ⟩` | the inr branch of `kappa-decides` | `Probe421.agda:252-254` |
| `⟪ fst x ⟫ ↪ ⟪ fst d ⟫` | `kappa-arrow-data a ox` | `Probe421.agda:255-257` |
| `sq (fst d)` | IH at `κ`, with `κoL` and `kappa-not-fin` | `Probe421.agda:258-259` |

The one argument `[LJ-1.421]` could not pay from the tree is the DATA
arrow, at type `⟪ fst x ⟫ ↪ ⟪ fst (κL x ox) ⟫`
(`agents/tasks/LJ-1-421/lj-1.421-report.md:89-90`,
`agents/tasks/LJ-1-421/Probe421.agda:255-257`). The tree delivers only
`∥ ⟪ fst a ⟫ ↪ ⟪ fst (κL a oa) ⟫ ∥₁`
(`src/L/Cardinal.lagda.md:133`). This telescope pays that argument
because `κC-arrow` is data by construction, at the same type with `κC`
in place of `κL`. Membership is a hypothesis of the obligation, not a
search. Infinitude is W3, restated at `κC` from that data arrow.

Corrected target: none. Original target stands. The statement is not
false. It is the 421 case-4 application with `d := κC` and the arrow
already data.

`[LJ-1.421]` returned GO (`agents/tasks/LJ-1-421/lj-1.421-report.md:53`).
I opened that report and the probe that typechecked. `descent-data` is
taken from `agents/tasks/LJ-1-421/Probe421.agda:111-118`, rebuilt, not
imported. I took no module hypothesis from `[LJ-1.429]`, `[LJ-1.430]`,
or `[LJ-1.431]`: those reports are not in this tree.

## VERDICT

**GO.** `descent-case4-coded` typechecks
(`agents/tasks/LJ-1-432/Probe432.agda:155-168`, exit 0, median 1.70 s
on three forced rechecks) and PASSes the program's witness meter
(`/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py
--code LJ-1-432 --brief agents/tasks/LJ-1-432/LJ-1.432.md`, exit 0,
1.63 s, 0 UNRESOLVED of 1, `probe_red=False`).

The untruncated arrow the descent needs does not have to sit at the
ambient least cardinal. Case 4 closes at a generic `d` whose arrow is
data by construction. **Case 3 is not closed.** That case is named
below. It is this task's deliverable to `[LJ-2.5]`.

## 1. What was built

All in `agents/tasks/LJ-1-432/Probe432.agda`, module
`LJ-1-432.Probe432 {ℓ} (lem)`.

- `isL-ord`, sealed (`:54-56`), `mem-incl` (`:58-71`), `comp-inj`
  (`:73-75`). Rebuilt from `[LJ-1.421]` `Probe421.agda:62-82`.
- `descent-core` (`:82-102`) and `descent-data` (`:104-110`). Rebuilt
  from `Probe421.agda:89-118`. Generic in `d`. Nothing in the type
  names a least cardinal.
- Four module hypotheses (`:118-123`), sealed in the shape of
  `Probe421.agda:125-135`: `κC`, `κC-ord`, `κC∈suc`, `κC-arrow`. The
  arrow is data, not truncated. None is inhabited. `κC∈suc` is in the
  seal and is not spent: case 4 hypothesizes membership directly.
- W3: `kappaC-not-fin` (`:132-147`).
- The obligation: `descent-case4-coded` (`:155-168`).

No `LeastCardInjL`. No `κL`. No `init-at-kappa`. No `via-col-square`.
No `ord-tri`. No case 3. No full descent.

## 2. W3: `kappaC-not-fin`, first

**GO.** Infinitude of `κC` closes from the DATA arrow. The induction
hypothesis reaches `κC`.

`[LJ-1.421]` proves the same fact at `κL` from the truncated arrow, by
`PT.rec` on `κ-injL` (`Probe421.agda:164-180`). This restatement skips
the truncation: `κC-arrow` is already data, so `comp-inj` of
`mem-incl x ω ox ω∈x` with `κC-arrow a ox` is `⟪ ω ⟫ ↪ ⟪ fst κC ⟫`,
and `finite-excl-ω` (`src/L/InjChain.lagda.md:153-155`) refutes
membership in `ω`.

Typechecked ALONE, obligation omitted, caliber `-A64m -I0 -M8g`, set
on the pane, untouched. One Agda process. Dependencies warm. The probe
interface was deleted before every kept run
(`_build/2.8.0/agda/agents/tasks/LJ-1-432/Probe432.agdai`).

First landing, obligation omitted: 1.80 s, peak RSS 406011904 bytes,
exit 0, printed `Checking`. `runs/w3-1.out` / `w3-1.time`.

Three forced rechecks, exit 0 every time, each printed `Checking`:

| run | wall s | peak RSS bytes |
|---|---|---|
| `runs/w3-2.out` / `w3-2.time` | 1.62 | 405995520 |
| `runs/w3-3.out` / `w3-3.time` | 1.64 | 406011904 |
| `runs/w3-4.out` / `w3-4.time` | 1.63 | 406044672 |

Median wall **1.63 s**. Median peak RSS **406011904 bytes**. No heap
event.

## 3. The obligation

`descent-case4-coded` (`:155-168`) applies `descent-data` with
`d := κC`.

| argument | supplier here | file:line |
|---|---|---|
| `x : S` | packed `a = x , isL-ord x ox` | `Probe432.agda:163-164` |
| `d : S` | `κ = κC a ox` | `Probe432.agda:165-166` |
| `ox` | the ordinal certificate of `x` | `Probe432.agda:155` |
| membership | hypothesis of the obligation | `Probe432.agda:157` |
| DATA arrow | `κC-arrow a ox` | `Probe432.agda:122`, spent at `:161` |
| `sq (fst κ)` | IH at `κC-ord` and `kappaC-not-fin` | `Probe432.agda:167-168` |

The one argument `[LJ-1.421]` could not pay is paid here: the arrow is
data by construction. Membership is hypothesized, so this term is
exactly case 4 of the 421 split (`Probe421.agda:252-259`) and not the
split itself.

**14 non-blank lines** for `descent-case4-coded` (type plus body).
The brief's estimate was about 55 code lines, a comparable of SHAPE
from `Probe421.agda:62-118` plus the seal change and one application.
Nothing is funded against the estimate.

## 4. Extra hypotheses

The four names in the seal (`:118-123`) are module parameters. I
inhabited none of them. I imported none of 429, 430, 431. I copied no
type out of any of their briefs.

Rebuilt, not hypothesized, copied from the 421 probe that typechecked:

| term | copied from |
|---|---|
| `isL-ord`, `mem-incl`, `comp-inj` | `agents/tasks/LJ-1-421/Probe421.agda:62-82` |
| `descent-core`, `descent-data` | `agents/tasks/LJ-1-421/Probe421.agda:89-118` |
| `kappaC-not-fin` | `agents/tasks/LJ-1-421/Probe421.agda:164-180`, with `PT.rec` dropped |

## WHO OWES WHAT

The brief names three tasks and four seal names. A report I cannot
open is a report I may not cite. I assert none of 429, 430, 431 as a
fact.

| hypothesis | task the brief names | report in this tree today |
|---|---|---|
| `κC` (the nonemptiness that makes it exist) | `[LJ-1.429]` | no. `agents/tasks/LJ-1-429/` is absent. |
| `κC-ord` | `[LJ-1.430]` | no. `agents/tasks/LJ-1-430/` is absent. |
| `κC-arrow` | `[LJ-1.431]` | no. `agents/tasks/LJ-1-431/` is absent. |
| `κC∈suc` | the brief names this seal property and names no task that owes it | no report to open |

Membership `⟨ fst (κC ...) ∈ˢ x ⟩` is a hypothesis of this obligation.
It is case 4 of the split. It is not owed by those three tasks.

## THE CASE THAT DOES NOT CLOSE

**Case 3 is not closed.** The other case of the 421 split is
`fst κ ≡ x` (`agents/tasks/LJ-1-421/Probe421.agda:246-250`). Replacing
`κL` by `κC`, that case is `fst (κC a oa) ≡ x`. This task does not
build it.

`[LJ-1.421]` closes that case through `init-at-kappa`
(`agents/tasks/LJ-1-406/Probe406.agda:180-185`) and `via-col-square`.
Conjunct 4 of `Init` is `src/L/Ordinal/SquareLaw.lagda.md:696`:

    ((β : S) → IsOrd β → ⟨ β ∈ˢ α ⟩ → ⟨ ω ∈ˢ β ⟩
     → (f : ⟪ α ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
     → ((m n : ⟪ α ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥)

`[LJ-1.406]` pays that conjunct at `κL` as `clause4-at-kappa`
(`agents/tasks/LJ-1-406/Probe406.agda:103-122`). The spend is
`κ-min-atL` at `:116`, whose type is `κ-min-at` at
`src/L/Cardinal.lagda.md:140-141`:

    κ-min-at : (δ : S) → ⟨ fst δ ∈ˢ fst κ ⟩
             → ∥ ⟪ fst α ⟫ ↪ ⟪ fst δ ⟫ ∥₁ → Empty.⊥

That input is an ambient truncated injection. The composition that
produces it is `Probe406.agda:118-122`: square pairing of `κ` into
`β`, then `PT.map` along the truncated ambient arrow `κ-inj`.

**That conjunct does not still close when the selection's minimality
forbids a code rather than an ambient injection.** The composition
yields `∥ ⟪ fst a ⟫ ↪ ⟪ β ⟫ ∥₁`. It does not yield a code. Ambient
minimality at `src/L/Cardinal.lagda.md:140` fires on that object. A
minimality that fires only on a code does not see it. With a data
arrow the same composition is available without `PT.map`, and the
output is still an ambient injection, still not a code.

I did not inhabit case 3. I did not refute `Init` at `κC`. I did not
add a minimality hypothesis. Adding one would be the shape audit
findings F1 and F3 measured (`dev/pod/audit-2026-08-20.md:34`).

The one statement that would close case 3, as a type, at
`src/L/Ordinal/SquareLaw.lagda.md:696`, instantiated at
`fst (κC a oa)`:

    (β : S) → IsOrd β → ⟨ β ∈ˢ fst (κC a oa) ⟩ → ⟨ ω ∈ˢ β ⟩
      → (f : ⟪ fst (κC a oa) ⟫ → ⟪ β ⟫ × ⟪ β ⟫)
      → ((m n : ⟪ fst (κC a oa) ⟫) → f m ≡ f n → m ≡ n) → Empty.⊥

That is conjunct 4 of `Init (fst (κC a oa))`. If it lands, case 3
transports along `fst (κC a oa) ≡ x` as `Probe421.agda:247-250` does
at `κL`. It is smaller than the campaign residue `[LJ-1.421]` named
(`agents/tasks/LJ-1-421/lj-1.421-report.md:60`): it is not an
untruncated ambient arrow at the least cardinal.

## 5. W2 and DD4

Everything is written once at a generic carrier. The module is generic
in `ℓ`. `κC` is generic in `a`. `descent-case4-coded` is generic in
`x`. No cardinal, no band and no numeral is named anywhere in the
file. `ω` appears only where `[LJ-1.421]`'s own statement puts it: in
`⟨ ω ∈ˢ x ⟩`, in `⟨ _ ∈ˢ ω ⟩ → Empty.⊥`, and in `kappaC-not-fin`.
`descent-data` is written once and instantiated at `d := κC`. There is
no fixed form to report.

W4 does not fire: no module was retired.

## 6. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched
here. One Agda process at a time, from the repository root.

- W3 first, obligation omitted: median **1.63 s**, median peak RSS
  **406011904 bytes**, exit 0. Section 2.
- Full file, first check after the obligation landed: 1.76 s, exit 0,
  peak RSS 408338432 bytes, printed `Checking`. `runs/full-1.out` /
  `full-1.time`.
- Full file, three forced rechecks (probe interface deleted before
  each run, dependencies warm): 1.73 s, 1.69 s, 1.70 s. Peak RSS
  408322048, 408322048, 408354816 bytes. Median wall **1.70 s**.
  Median peak RSS **408322048 bytes**. Exit 0 every time. Each printed
  `Checking`. `runs/full-recheck-{1,2,3}.out`.
- Witness meter, one obligation: PASS, exit 0, 1.63 s, 0 UNRESOLVED
  of 1, `probe_red=False`.
- No heap event.

P-l did not fire: the types name the parameter atom `κC`, not a
transparent `sucV`-chain. `κC∈suc` mentions `sucV (fst a)` in the same
shape as `κ∈sucL` at `Probe421.agda:131`.

## 7. What GO earns, and what the next brief needs

A GO shrinks the campaign's residue and does not discharge it. Case 4
of the descent does not need the ambient least cardinal. It needs an
ordinal `d ∈ x` whose arrow `⟪ x ⟫ ↪ ⟪ d ⟫` is data, plus infinitude
of `d`, plus `sq d` from the IH. `κC` is such an ordinal as a
hypothesis.

**Case 3 is not closed.** The statement that would close it is conjunct
4 of `Init` at `fst (κC a oa)`, typed at
`src/L/Ordinal/SquareLaw.lagda.md:696`. The 406 payment of that
conjunct spends ambient truncated-injection minimality
(`src/L/Cardinal.lagda.md:140`) and does not spend a code. If `κC`'s
minimality forbids a code, that payment does not transfer.

The four hypotheses remain owed. Their reports are not in this tree.
I did not inhabit them.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md:1`, read: "# Archived journal: the retired route".
  Declined. This task does not consult the archived journal.
- `archive/dev/LJ-dispatch-index.md:1`, read: "# THE `LJ` DISPATCH INDEX, archived 2026-08-18".
  Declined. The live producer is `dev/pod/queue.toml`. This probe does
  not consult the archived dispatch index.
- `archive/dev/JOURNAL.md:1`, read: "# ARCHIVED 2026-08-20". Declined.
  The per-episode journal is retired. This task's record is its own
  directory.
- `dev/ARCHIVE.md:33`, read: "`archive/`. **`archive/src/` carries one extra
  level, the ARCHIVAL EVENT**". Read to resolve the injected archive
  paths. This task does not retire a module.
- `archive/dev/ORCHESTRATION.md:1`, read: "# ORCHESTRATION: the orchestrator's operating rules".
  Declined. How the loop is operated is not this task.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:79`, read: "`card(A) ≤
  card(B) :≡ ∥ inj(A,B) ∥` ... "In other words, `card(A) ≤ card(B)`".
  Used for D-10 and for case 3: a cardinal inequality is a truncated
  injection, and that is the input of `κ-min-at` at
  `src/L/Cardinal.lagda.md:140`.
- `dev/literature/truncation-and-selection.md:147`, read: "delivers the
  least INDEX untruncated, and any payload it delivers with the". Used
  with `:148` "index is a proposition. **A data payload does not come
  out.**" `[LJ-1.421]` could not pay the data arrow from `leastOf`.
  This telescope does not ask `leastOf` for a payload: `κC-arrow` is
  data by hypothesis.
- `dev/literature/devlin-II5.md:72`, read: "> 5.2 Theorem (The
  Condensation Lemma). Let α be a limit ordinal. If". Declined. Condensation
  codes a collapse of a hull. This task measures case 4 of the descent
  at a data arrow, not a condensation.
- `dev/literature/digest.md:1`, read: "# Digest: the orthodox form of the
  rud route, pinned from the collected literature". Not used. This
  probe is the L-tower band step, not the rud-route architecture.
- `dev/literature/geology.md:1`, read: "# Geology dossier: set-theoretic
  geology sources and the five questions". Not used. Geology is not
  this measurement.
- `dev/literature/fine-structure.md:1`, read: "# Fine structure: projecta, standard codes, the reductions, and their dependencies".
  Declined. Case 3 names a code only as the object coded minimality
  would forbid. This file is the rud-route fine structure, not that
  measurement.

## WHAT I DID NOT DO

- I did not commit. I did not push.
- I did not set `GHCRTS`.
- I did not start a second Agda process from this slot.
- I did not write in `src/`.
- I did not write case 3. I did not write the full descent.
- I did not import `Probe406`, `Probe421`, or any 429, 430, 431 probe.
- I did not inhabit `κC`, `κC-ord`, `κC∈suc`, or `κC-arrow`.
- I did not copy a type out of a 429, 430, or 431 brief.
- I did not assert any statement of those three tasks as a fact.
