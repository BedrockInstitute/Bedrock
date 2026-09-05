# Review of the `CardAboveL` landing: the proposed chapter is impossible

**VERDICT: NO-GO ON `src/L/StageCardinal.lagda.md`. GO ON
`src/L/CardinalAbove.lagda.md`, and the term is in the tree there.**

The brief's obligation name is `src/L/StageCardinal.lagda.md::CardAboveL`. That
name cannot be inhabited. This file states why, because the brief said so:
"If landing there creates an import cycle, say so and name the chapter that does
not." The term itself is delivered, green, at the corrected path. The report is
`agents/tasks/LJ-1-555/lj-1.555-report.md`.

## 1. THE IMPORT CYCLE, AT `file:line`

`L.BoundedSubset` already imports `L.StageCardinal` and instantiates it:

- `src/L/BoundedSubset.lagda.md:882` `import L.StageCardinal`
- `src/L/BoundedSubset.lagda.md:1397` `    module SC = L.StageCardinal {ℓ} lem α ordα sq`

So `L.StageCardinal` is BELOW `L.BoundedSubset` in the tree.

`CardAboveL` needs three names that live only in `L.BoundedSubset`:

- `src/L/BoundedSubset.lagda.md:1043` `_↪_ : Type ℓ → Type ℓ → Type ℓ`
- `src/L/BoundedSubset.lagda.md:1046` `IsCardinal : S → Type (ℓ-suc ℓ)`
- `src/L/BoundedSubset.lagda.md:1362` `module Devlin55`, which supplies
  `comp-inj` (`:1365`) and `ord-emb` (`:1370`)

The probe takes all three from that module:
`agents/tasks/LJ-1-528/Probe528.agda:29-30`, and opens `Devlin55` at `:34`.

Landing `CardAboveL` in `L.StageCardinal` therefore needs
`L.StageCardinal → L.BoundedSubset → L.StageCardinal`. **That is a cycle and
Agda refuses it.** No arrangement inside the chapter removes it, because the
cycle is a property of the two chapters and not of the term.

## 2. A SECOND, INDEPENDENT REASON, AND IT IS THE BRIEF'S OWN BAR

`src/L/StageCardinal.lagda.md:15-19` is the module header:

    module L.StageCardinal {ℓ : Level} (lem : LEM (ℓ-suc ℓ))
      (α₀ : V ℓ) (oα₀ : IsOrd α₀)
      (sq : (δ : V ℓ) → ⟨ δ ∈ InfinitySet.sucV α₀ ⟩ → (⟨ δ ∈ InfinitySet.ω {ℓ} ⟩ → Empty.⊥)
          → Σ[ f ∈ (⟪ δ ⟫ × ⟪ δ ⟫ → ⟪ δ ⟫) ]
              ((x y : ⟪ δ ⟫ × ⟪ δ ⟫) → f x ≡ f y → x ≡ y)) where

`CardAboveL` consumes NONE of `α₀`, `oα₀` and `sq`. A term placed in that
chapter is reachable only by a consumer that supplies an ordinal `α₀` and the
square law at it. The square law is the campaign's own open question
(`dev/pod/queue.toml:169`). **So the proposed chapter would gate a
hypothesis-free theorem behind the campaign's most expensive open hypothesis.**
The brief forbids exactly this: "DO NOT WEAKEN THE STATEMENT TO MAKE IT LAND."

Reason 1 alone is decisive. Reason 2 says that even if the cycle were removed,
the chapter would still be the wrong home.

## 3. THE CHAPTER THAT DOES NOT

**No existing master can host the term without a new import edge, and only one
existing file already sits above every dependency: `src/Everything.lagda.md`,
which is the aggregator and defines nothing.**

Measured over the 102 masters of the tree, by the import graph read from the
`import` lines of every `.lagda.md` under `src/`. The term's dependencies are
`L.Cardinal`, `L.BoundedSubset`, `L.CantorBernstein`, `L.InjChain`,
`L.Ordinal.Stages`, `L.Ordinal.Linear`, `L.Constructible`, `L.Ordinal`,
`V.Model`, `V.Presentation` and `V.Hierarchy`. The union of their import
closures is 87 masters. A host must sit outside that union. Fourteen masters
do, and every one of them is topically unrelated to cardinal existence:
`L.Absorption`, `L.CodedShift`, `L.SquareLawClosed`, `L.StageBound`,
`L.Model`, `Landmarks`, `FOL.Bernstein`, `L.Choice.Transversal`,
`L.Coding.EnvSupply`, `L.Coding.Key`, `L.Coding.KeyRead`,
`L.Condensation.LowerAgree`, `L.Condensation.TwelveAgree` and
`L.Condensation.UpperAgree`.

**So the landing needs a NEW master, and it is `src/L/CardinalAbove.lagda.md`.**
It is a leaf: nothing imports it, so it adds no edge to any existing chapter.
Its telescope is `{ℓ : Level} (lem : LEM (ℓ-suc ℓ))` and nothing else
(`src/L/CardinalAbove.lagda.md:10`), which is the probe's telescope
(`agents/tasks/LJ-1-528/Probe528.agda:15`).

## 4. WHAT THE MATHEMATICIAN MUST DO WITH THIS

**The obligation NAME in the brief is wrong, and the term is right.** The next
brief that cites this input must name
`src/L/CardinalAbove.lagda.md::CardAboveL`.

**AND THE SCOPE WAS TOO NARROW TO COMMIT THE RESULT.** The task's write scope
names `src/L/StageCardinal.lagda.md` and nothing else under `src/`. The landing
touched two paths that the scope does not name:

- `src/L/CardinalAbove.lagda.md` (new, 587 lines)
- `src/Everything.lagda.md` (one line added, `import L.CardinalAbove`)

Rule R8 makes the program commit by explicit path from the task's scope, so
**neither file is committable under this task as written.** This is a program
input and not a mathematical one: the scope needs the two paths, or the work is
green in the worktree and absent from the branch.

## 5. WHAT IS TRUE AFTER THIS FILE

`make check` is GREEN on the final tree: exit 0, 11.208 s, 103 masters,
`agents/tasks/LJ-1-555/runs/make-check-final.log`. The term is
typechecked by the build for the first time in the campaign.
