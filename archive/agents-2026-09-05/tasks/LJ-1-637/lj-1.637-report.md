# LJ-1.637 report: the class-pred consumer, assembled, with (iii) as the only remaining hypothesis

**VERDICT: GO.** The assembly composes. The four landed ingredients assemble into
the one term the brief names, at the type the brief asks for. Ingredient (iii) is
taken as a hypothesis and its exact type is written out in section 2. The assembly
consumes (iii) EXACTLY ONCE, at the site, and it does not need more than (iii).
Nothing lands in `src/`.

## 1. THE ONE TERM

`agents/tasks/LJ-1-637/Probe637.agda` carries one deliverable:

```agda
class-pred-debt : SiteFiber α₀ → (γ : V ℓ) → Q γ
class-pred-debt iii = ∈-induction (step iii)
```

The probe module is `LJ-1-637.Probe637 {ℓ} (lem) (α₀) (oα₀) (α∉ω₀) (band)`.
`band` is the ABSTRACT band parameter the tree's chapter carries
(`src/L/StageCardinal.lagda.md:17-20`); no row instantiates it, prices it, or
reaches into the circle. The probe carries no postulate and no hole in its final
form (final run below). Its companion row `site-leg-α` is the consumer read at
`γ = α₀`, the grain `src/L/BoundedSubset.lagda.md:1513` consumes.

## 2. THE EXACT TYPE OF (iii)

(iii) is the site fiber: ONE binary function on the site's index with its
injectivity, at ONE ordinal:

```agda
SiteFiber : V ℓ → Type ℓ
SiteFiber β = Σ[ f ∈ (⟪ β ⟫ × ⟪ β ⟫ → ⟪ β ⟫) ]
  ((u v : ⟪ β ⟫ × ⟪ β ⟫) → f u ≡ f v → u ≡ v)
```

This is the value half of the band parameter applied at the site
(`src/L/BoundedSubset.lagda.md:1410`) and the fiber half of the law chapter's own
`sq` (`src/L/Ordinal/SquareLaw.lagda.md:685-688`); `[LJ-1.604]` measured it the
same object. The obligation fixes the injection's TARGET at the site:

```agda
Q : V ℓ → Type (ℓ-suc ℓ)
Q γ = IsOrd γ → ⟨ γ ∈ˢ sucV α₀ ⟩ → ⟪ Lset γ ⟫ ↪ ⟪ α₀ ⟫
```

with `X ↪ Y = Σ[ f ∈ (X → Y) ] ((x y : X) → f x ≡ f y → x ≡ y)`, the tree's own
shape (`src/L/StageCardinal.lagda.md:243-246`). `[LJ-1.621]` delivered this same
obligation from this same fiber
(`agents/tasks/LJ-1-621/Probe621.agda:128-129`).

## 3. THE RUNS, IN ORDER

The program set GHCRTS on this pane (`[-A64m -I0 -M2g]`). One Agda process at a
time. Caps per run in `runs/run.sh`.

1. **W3 first** (`runs/W3.agda`, `runs/w3-2.out`): the widest unmeasured term,
   type only, capped at two minutes. GREEN. Wall 0.75 s, peak 210 MB.
2. **The floor** (`runs/floor-1.out`): the probe with the obligation row and the
   site row holed, everything else in place, cap 900 s. RED, as a floor is: the
   ONLY errors are the two hole positions themselves
   (`UnsolvedInteractionMetas` at `Probe637.agda:397.23-27` and
   `:402.18-22`, nothing else). Wall 9.83 s, peak 1.56 GB.
3. **The final** (`runs/final-7.out`): the filled probe, cap 1800 s, run after
   deleting the probe's own interface so the check is fresh. GREEN. Wall
   12.14 s, peak 1.79 GB, resident 1.85 GB under the 2 GB wall.
   `runs/final-6.out` is the same file's first green (12.34 s) before the floor
   swap.

## 4. WHAT THE ASSEMBLY READS, ROW BY ROW

Section 3 of the probe (`DebtStep`, the limit step at the fixed site) reads:

- **(i)** — the landed row, `src/L/Constructible.lagda.md:314-317`, consumed as
  its two projections: `D = D-i` and `inv = inv-i` (the probe's section 2.1).
  It is opaque; no row restates its body.
- **(ii)** — the landed row `least-at-site`,
  `src/L/StageCardinal.lagda.md:265-272`, consumed as the selection (the probe's
  section 2.2, `selection-at`): `h x = fst (selection-at α₀ oα₀ (class-pred x)
  (nonempty x))`, definitionally the tree's own inline call at
  `src/L/StageCardinal.lagda.md:361`.
- **(iii)** — the hypothesis, spent ONCE, at the site, through the LANDED
  `Bound`: `module B = SC.Bound α₀ oα₀ α∉ω₀ iii`
  (`src/L/StageCardinal.lagda.md:64-70`). The count of each member formula type
  into `⟪ α₀ ⟫` is `B.formula-bound` on the branch; the packing of the stage
  index and the count is `B.pair`.
- **(iv)** — NOT consumed by the ambient step. It is a certificate of the branch
  the induction hypothesis graphs: `class-pred-iv` at
  `src/L/BoundedSubset.lagda.md:1753` is the object-language twin of the
  step's `ihm` (the probe's section 5 names the tie; it is a certificate, not a
  step ingredient).
- **(v)** — NAMED, NOT CONSUMED: `row-v = F637.class-pred-v` (the probe's
  section 6). The tree's own consumer carries the formula itself in its witness
  (`src/L/StageCardinal.lagda.md:329-334`); `[LJ-1.617]`'s green step has no key
  row. (v) lives on the constructible carrier `Sʟ`, a different carrier from
  the step's `S = V ℓ`; it cannot be a step ingredient at this site.

**The answer to the brief's question:** the assembly needs LESS than a full
fresh pairing law. It needs (iii) at one ordinal — the fiber half of `sq` —
spent once, at the site. The debt is the fiber, and the fiber is the type in
section 2.

## 5. MEASUREMENTS FROM THE TASK, FOR THE NEXT BRIEF

1. **Import form for the parameterized `L.StageCardinal` chapter.** The green
   probe uses the single in-module instantiation
   `import L.StageCardinal {ℓ} lem α₀ oα₀ band as SC` (probe line 101). The
   two-line form `import L.StageCardinal` followed by `module SC = L.StageCardinal
   {ℓ} ...` left `SC.Bound` and the step lines out of scope in this worktree
   (measured: `runs/final-5.out` and the diagnostic runs removed from `runs/`).
   The `open` form additionally leaks the chapter's own `_↪_` into the probe's
   scope and clashes with the probe's local injection type (measured:
   `runs/final-4.out`).
2. **Module application in the step line must be the projection form.** The
   green line is `step iii γ IH oγ γ∈suc = DebtStep.leg iii γ oγ γ∈suc IH`,
   the exact shape of `[LJ-1.617]`'s step
   (`agents/tasks/LJ-1-617/Probe617.agda:468`). The application form
   `DebtStep iii γ oγ γ∈suc IH .leg` does not elaborate.
3. **`𝒮ʟ` must come from the in-module `{ℓ}` instantiation.** The top-level
   `open import L.Constructible using ( 𝒮ʟ )` leaves a level meta that blocks
   (`UnsolvedConstraints ℓ = _ℓ_18`); moving `𝒮ʟ` into the in-module
   `open import L.Constructible {ℓ} using ( ...; 𝒮ʟ )` closes it.
4. **The base repo's `_build` carries probe interfaces that skip re-checks.**
   `agda agents/tasks/LJ-1-613/Probe613.agda` in this worktree returned in
   1.69 s with NO "Checking" line: the copied interface was trusted and the
   file never re-verified. A probe run is a fresh measurement only after
   deleting the probe's own `.agdai` (done before `final-7.out`).
5. **The `Bound` instance wants the FIBER, not the band.**
   `src/L/StageCardinal.lagda.md:64-68` asks for the pairing at the instance
   ordinal; the chapter's own spend is `(sq α α∈suc infα)`
   (`src/L/StageCardinal.lagda.md:293`). Passing the band function fails with
   `UnequalTerms` (measured in a diagnostic run).

## 6. THE RATIO

The probe is a raw `.agda` file; it carries no ` ```agda ` fence and counts 0
in-fence lines. No `.lagda.md` master was written. The 0.0123 s/line bar does
not fire on this return.

## 7. THE GATES

- `src/` untouched: the git diff in this worktree shows no `src/` path.
- The probe has no postulate and no hole in its final form: `grep -n
  "FILL IN\|postulate" agents/tasks/LJ-1-637/Probe637.agda` matches only the
  file's own header comment.
- The floor and the final are recorded above with caps and peaks.
- No commit and no push; the tree is left exactly as this report describes.

## 8. WHAT THE NEXT BRIEF NEEDS

1. The landed home for (iii): the fiber type of section 2 at the site, with the
   spend shape `Bound α₀ oα₀ α∉ω₀ (sq α₀ (self∈sucV α₀) α∉ω₀)` from
   `src/L/BoundedSubset.lagda.md:1410` / `:1526`.
2. The import form of section 5.1 for any probe or chapter touching
   `L.StageCardinal`.
3. The interface-freshness rule of section 5.4 for any `runs/` evidence.
4. The split between step ingredients ((i), (ii), (iii)) and certificates
   ((iv), (v)) of section 4: the landing plan must not budget (iv) or (v) as
   consumer spend.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md` — declined, not read.
- `archive/dev/JOURNAL-archived.md` — declined, not read.
- `archive/dev/JOURNAL.md` — declined, not read.
- `dev/ARCHIVE.md` — declined, not read.
- `archive/dev/ORCHESTRATION.md` — declined, not read.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md` — declined, not read.
- `dev/literature/devlin-II5.md` — declined, not read.
- `dev/literature/digest.md` — declined, not read.
- `dev/literature/terms-2026-08.md` — declined, not read.
- `dev/literature/geology.md` — declined, not read.
