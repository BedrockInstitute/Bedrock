# LJ-1.398 report: the band recursion on the two selections, and the one residue

slot: `coder`. Written early as a skeleton and filled as runs landed (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-398/`. Agda ran under
the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda
process at a time. One heap exhaustion was hit and cured; it is recorded and
section 7 states it.

TARGET: build TWO terms in `agents/tasks/LJ-1-398/Probe398.agda`, at a GENERIC
band, with every case fed by a named supplier taken as a module hypothesis:

1. `band-owes-2`, the residue, at the ONE class the four cases leave unpaid.
2. `sq-band-2`, the recursion, by `∈-induction`, split by `lem` on
   `IsCardinalL`, matching `L.StageCardinal`'s module parameter exactly.

## VERDICT

**GO.** Both obligations typecheck (`agents/tasks/LJ-1-398/Probe398.agda`,
exit 0, median 1.64 s) and both PASS the program's witness meter
(`scripts/pod/witness.py --code LJ-1-398`, grouped run, exit 0, 1.75 s,
0 UNRESOLVED of 2). The recursion assembled with all four cases fed, and the
residue is ONE datum: the untruncated ambient arrow at an L-cardinal that is
not its own ambient least cardinal. That datum is the campaign's next bill.

## 1. What was built

All in `agents/tasks/LJ-1-398/Probe398.agda`, module
`LJ-1-398.Probe398 {ℓ} (lem) (α₀) (oα₀)`.

- The five supplier statements, taken as hypotheses of a nested
  `module _ (...)` and nothing imported or copied:
  `coded-arrow` is [LJ-1.397]'s statement (`agents/tasks/LJ-1-397/LJ-1.397.md`,
  obligation section) at `Probe398.agda:192-193`; `amb-card-at-kappa` and
  `kappa-is-limit` are [LJ-1.396]'s two statements
  (`agents/tasks/LJ-1-396/LJ-1.396.md`, obligation section) at `:195-199`;
  `amb-init'` is [LJ-1.393]'s (`agents/tasks/LJ-1-393/Probe393.agda:207-221`)
  at `:200-202`; `descent-core` is [LJ-1.390]'s
  (`agents/tasks/LJ-1-390/Probe390.agda:110-131`) at `:203-204`.
- The ambient least cardinal is SEALED at the call site: `κL`, `κoL`,
  `κ∈sucL` (`:126-133`), an opaque wrapper over `LeastCardInjL.κ`. Section 7
  states why. `band-owes-2` and the two `κ`-named supplier statements are
  spelled over `κL`, not over the bare `LeastCardInjL.κ`.
- `kappa-decides`, the W3 probe: `:141-176`.
- `band-owes-2`, the residue: `:179-184`.
- `Goal`, the motive, `no-fin-descent`, and `step`: `:208-209`, `:213-220`,
  `:223-276`.
- `sq-band-2`, the obligation: `:278-281`.
- `ConsumerShape` and `plugs-in`, the consumer match: `:292-299`.

## 2. `band-owes-2`: the residue, and what each conjunct is for

```agda
band-owes-2 =
  (a : V ℓ) (oa : IsOrd a) → ⟨ ω ∈ a ⟩
  → IsCardinalL (a , isL-ord a oa)
  → ⟨ fst (κL (a , isL-ord a oa) oa) ∈ a ⟩
  → (⟪ a ⟫ ↪ ⟪ fst (κL (a , isL-ord a oa) oa) ⟫)
```

- **`oa : IsOrd a`.** Spent to form the L-element `(a , isL-ord a oa)` and to
  run `κL`.
- **`⟨ ω ∈ a ⟩`.** The case is an infinite ordinal; the recursion holds it and
  `by-residue` uses it (through `no-fin-descent`) to show the target is
  infinite, so the induction hypothesis applies.
- **`IsCardinalL (a , isL-ord a oa)`.** The case is an L-cardinal.
- **`⟨ fst κ ∈ a ⟩`.** The case is NOT its own ambient least cardinal; this is
  the `inr` of `kappa-decides`.
- **The conclusion `⟪ a ⟫ ↪ ⟪ fst κ ⟫`.** The ONE datum owed: the untruncated
  ambient arrow into the ambient least cardinal. The target's ordinality is
  `κoL`, its membership is the hypothesis, and its infinitude follows from the
  arrow by `finite-excl-ω` (`by-residue`, `:268-276`). So nothing else is owed.

The band membership does not appear, exactly as [LJ-1.395]'s `band-owes`
omitted it (`agents/tasks/LJ-1-395/Probe395.agda:124-127`): the band is the
recursion's context, not the residue's. The residue quantifies over exactly
the class the brief names, no more.

## 3. The four cases, and the supplier of each

At an infinite site `x` (after `ord-tri` closes `x ≡ ω` by `squareω` and
refutes `x ∈ ω` by the infinitude), `step` splits by `lem` on
`IsCardinalL (x , isL-ord x ox)`, a proposition (`isPropCardL`, `:111-112`),
then by `kappa-decides` on the positive side.

| case | supplier, and how it closes |
|---|---|
| `x ≡ ω` | `squareω`, delivered (`src/L/InjChain.lagda.md:184-185`), `:230` |
| `IsCardinalL` fails | `coded-arrow` (hypothesis) hands the arrow over as data, then `descent-core` with the IH; `by-coded`, `:249-252` |
| `IsCardinalL` holds, `x` its own least cardinal | `amb-card-at-kappa` then `kappa-is-limit` then `amb-init'` then `via-col-square`, transported along `fst κ ≡ x`; `splitOwn` `inl`, `:240-245` |
| `IsCardinalL` holds, `x` not its own least cardinal | `band-owes-2` (the residue), then `descent-core`; `by-residue`, `:268-276` |

**One interface note, for the next brief.** The case table names
`amb-card-at-kappa` for the positive case. `amb-init'` needs
`⟨ sucV ω ∈ fst κ ⟩` (`agents/tasks/LJ-1-393/Probe393.agda:207-221`), and that
hypothesis is fed by [LJ-1.396]'s SECOND term `kappa-is-limit`, not by
`amb-card-at-kappa`. I took `kappa-is-limit` as a fifth hypothesis
(`:198-199`). Without it the positive case does not close: nothing in the tree
produces `⟨ sucV ω ∈ x ⟩` from `IsCardinalL x` alone (the only escape is
`x ≡ sucV ω`, which is not refutable because the injection
`⟪ sucV ω ⟫ ↪ ⟪ ω ⟫` is a counting fact the tree does not deliver).

**The descent step is not rebuilt.** `descent-core` is a hypothesis. The
inclusion arrow at each descent target is `mem-incl` (`:85-99`), rebuilt from
`member`, `fiber`, `↪-inj` (`src/V/Presentation.lagda.md:31-38`), the same 12
lines [LJ-1.390] and [LJ-1.394] wrote.

## 4. The two descent targets are infinite, and it is delivered

`coded-arrow` returns a target `b` with no infinitude hypothesis. The descent
needs `sq (fst b)` from the IH, which needs `⟨ fst b ∈ ω ⟩ → Empty.⊥`.
`no-fin-descent` (`:213-220`) closes it: `ω ∈ x` gives `⟪ ω ⟫ ↪ ⟪ x ⟫`
(`mem-incl`), the arrow composes to `⟪ ω ⟫ ↪ ⟪ fst b ⟫` (`comp-inj`), and
`finite-excl-ω` (`src/L/InjChain.lagda.md:153-167`) refutes a finite target.
The same helper serves the residue target `fst κ`. This is what makes the
brief's "the negative side is free" true: the arrow is data, and the target's
infinitude is a delivered fact, not a wall.

## 5. The consumer match, checked

The consumer takes `sq` as a module parameter with no ordinal certificate
(`src/L/StageCardinal.lagda.md:17-19`). `plugs-in` (`:298-299`) discharges that
parameter at `ConsumerShape` (`:292-296`), which repeats the chapter's stated
type with the same terms: `sucV` opened instead of qualified
`InfinitySet.sucV`, and alpha-equivalent binders. `sq δ` is the Sigma the
chapter writes (`src/L/Ordinal/SquareLaw.lagda.md:685-687`), judgmentally, so
no transport sits inside `plugs-in`. `band-ord` (`:286-289`, the port of
`agents/tasks/LJ-1-395/Probe395.agda:209-212`) produces the certificate the
chapter does not ask for. Once `band-owes-2` is paid, `plugs-in` closes
`L.StageCardinal`'s module parameter at exactly the stated type. I checked it;
`plugs-in` is the check.

## 6. W2 and DD4

Everything is written once at a generic carrier. The module is generic in `ℓ`;
`α₀` and `oα₀` are the consumer's own parameters; every term quantifies over a
generic `x : V ℓ`. `coded-arrow`, `amb-card-at-kappa`, `kappa-is-limit`,
`amb-init'` and `descent-core` are all generic in their site. No site, no
ordinal and no numeral is named anywhere in the file.

## 7. The heap wall, and the cure

The first assembly spelled `band-owes-2` and the positive case over the bare
`LeastCardInjL.κ`. It exhausted the 8 GB heap: `runs/wall-transparent-kappa.out`
records `Heap exhausted; Current maximum heap size is 8589934592 bytes`. I did
not rerun it; I diagnosed it.

The cause is P-i/R-36. `fst (LeastCardInjL.κ a oa)` reduces through
`leastOf`'s body to a large stuck term, because only `w` is sealed inside
`L.Cardinal` and `leastOf`'s own body is transparent. Every conversion check
between two spellings of `fst κ` (the residue's `⟪ x ⟫ ↪ ⟪ fst κ ⟫` against the
arrow the hypothesis already carries) re-ran that reduction and exploded.

The cure is the opaque seal `κL`/`κoL`/`κ∈sucL` (`:126-133`): `fst (κL a oa)`
is a small atom, and the comparison is instant. After the seal the full file
checks in 1.64 s median, and `kappa-decides` alone in 1.53 s median. This is
the measured cure at its own site (Boundary: a measured cure does not transfer
by analogy; the chapter already carries its own seal at `src/L/Cardinal.lagda.md:85-89`).

## 8. W3: the probe, run first

**GO.** The widest unmeasured term was the second positive split: whether the
site is its own ambient least cardinal. The probe is `kappa-decides`
(`:141-176`): `ord-tri` on `fst (κL a oa)` against `fst a`, with the third
trichotomy branch `fst a ∈ fst κ` refuted against `κ∈sucL` by `∈sucV-elim`,
`∈-irrefl` and the transitivity of `IsOrd`. Stated and run alone, before the
assembly: median **1.53 s**, three runs, 36 code lines, exit 0. The estimate
was about 90 code lines for the two obligations; measured, the obligations
with their motive and step are 74 code lines (`band-owes-2` `:179-184`,
`Goal` `:208-209`, `no-fin-descent` `:213-220`, `step` `:223-276`,
`sq-band-2` `:278-281`, comments and blanks excluded), and `kappa-decides`
adds 36.

## 9. Runs, floor, witness

Caliber `-A64m -I0 -M8g`, set on the pane by the program and untouched here.
One Agda process at a time, every dependency warm, from the repository root.

- Full file, three consecutive runs: 1.63 s, 1.64 s, 1.64 s. Median
  **1.64 s**, exit 0 every time. `runs/full-{1,2,3}.out`.
- Preamble floor (`Floor398.agda`, imports and an empty body), three runs:
  0.82 s, 0.82 s, 0.83 s. Median **0.82 s**.
- `kappa-decides` alone (`KappaOnly`, run during the task and removed), three
  runs: 1.53 s, 1.54 s, 1.53 s. Median **1.53 s**.
- Witness meter, both obligations, grouped: PASS, exit 0, 1.75 s,
  0 UNRESOLVED of 2, `probe_red=False`.
- The wall run: `runs/wall-transparent-kappa.out` (heap exhausted), and the
  cure is section 7.

## 10. What GO earns, and the campaign's next bill

GO earns the square law at every band ordinal, conditional on `band-owes-2`,
and it earns the exact size of `band-owes-2`: ONE arrow. If `band-owes-2` is
paid, `plugs-in` closes `L.StageCardinal`'s module parameter, and with it the
whole GCH module parameter reduces to one named case.

**The next bill is the untruncated ambient arrow at an L-cardinal that is not
its own ambient least cardinal.** `κ-inj` gives it truncated
(`src/L/Cardinal.lagda.md:132-134`), and the chapter says the witness stays
truncated. [LJ-1.394] measured that `lem` and `leastOf` do not untruncate an
ambient injection (`agents/tasks/LJ-1-394/review-of-not-ambcard-gives.md`,
STEP 2), because the injection type is not a proposition and the tree's one
untruncation device needs a proposition payload. `band-owes-2` states that
debt as a type, at the recursion's own site, and at no other site.

## 11. What this task does NOT settle

- It does not pay `band-owes-2`. No square law at any ordinal is
  unconditional here.
- It does not produce `AmbCard` or `IsCardinalL` at any ordinal.
- It does not rebuild `descent-core`, `coded-arrow`, `amb-card-at-kappa`,
  `kappa-is-limit` or `amb-init'`; each is a hypothesis.

## 12. ARCHIVE USED

- `archive/dev/JOURNAL-archived.md:1338`, read: "the cardinal step consumes
  is delivered CONDITIONAL on one named bound, the square law (an infinite".
  The supplier of that bound is what this probe assembles at the band.
- `dev/ARCHIVE.md:33`, read: "**`archive/src/` carries one extra level, the
  ARCHIVAL EVENT**". Read to resolve the injected archived-SquareLaw path.
- `archive/dev/DECISIONS-archived.md:50`, read: the D30 row's
  "they state at abstract carriers and variable indices so nothing
  re-normalizes". This probe states every term at a generic band and a
  generic site.
- `archive/dev/TASKS-archived.md:82`, read: "| L3.32-T47 | Truncated square
  law at initial ordinals | DELIVERED | `_build/l3.32-t47-report.md` |". The
  row of the route whose residue this task names.
- `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:926`, read:
  "returns only the truncation `∥ ⟪ α ⟫ ≃ ⟪ κ ⟫ ∥₁`, so the law at the". The
  archived least-of search left the law named at non-initial ordinals; that
  named gap is this recursion's residue case.

## 13. LITERATURE USED

- `dev/literature/truncation-and-selection.md:335`, read: "`ω`. **A canonical
  injection needs a well-order on the INJECTIONS, which is". This is why
  `band-owes-2` asks for the arrow as data and why `lem` cannot produce it.
- `dev/literature/digest.md:241`, read: "surjection g : α -> J_α^A when α is
  closed under Gödel pairing (SZ 1.17)." The J-tower form of the closure this
  tree calls the square law; the digest offers no untruncated arrow.
- `dev/literature/terms-2026-08.md:42`, read: "| 13 | square pairing | 平方配对
  | in use; no literature for the scheme；配对函数 is the established generic |
  yes |". The square pairing term; no rendering question arises in a probe.
- `dev/literature/devlin-II5.md`, not used: the condensation digest for the
  GCH endpoint. This probe assembles a recursion at a generic band, and no
  step consults a condensation argument. Opened at the head only.
- `dev/literature/geology.md`, not used: sources for a later milestone, and
  nothing in it bears on this probe. Opened at the head only.

## WHAT I DID NOT DO

- I did not import an earlier probe and did not copy a proof from one. The
  five statements are parameters; the rebuilt `mem-incl`, `comp-inj` and
  `isL-ord` are from `src/` primitives, and their provenance is stated at
  their sites.
- I did not touch `src/`, did not commit, did not push, and set no `GHCRTS`
  of my own.
- I did not run `make check`: it is the gate before a commit, and this slot
  never commits.
