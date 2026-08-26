# review-of-lset-formula-to-level: the hypothesis names no fact

**THIS IS A STOP, AND IT IS THE DELIVERABLE.** The brief orders one term,
`lset-formula-to-level`, from `[LJ-1.651]`'s delivered `lset-formula` to
`[LJ-1.650]`'s `LevelFormula`. **That term is not in `Probe659.agda` and this
file says why.** The probe is green and carries no hole
(`runs/p-final.out`, exit 0 in 4.39 s at 787,546,112 bytes); the obligation
reads `missing` (`runs/meter-obligation.out`, `1 UNRESOLVED of 1`,
`probe_red=False`); the other 27 names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 27`).

**THE STOP IS NOT "I COULD NOT FIND THE PROOF". IT IS A PROOF THAT THE ARROW
BUYS NOTHING**, and section 1 is that proof, machine-checked.

## 1. THE HYPOTHESIS IS DEGENERATE, AND THIS IS PROVED

`[LJ-1.651]` delivered `lset-formula` at this type, read at the line it was
built on:

```
lset-formula : Formula Code 2          agents/tasks/LJ-1-651/Probe651.agda:141-142
```

**That is a type of SYNTAX. It carries no law about `_⊨c_`, so it says
nothing about `Lset`.** The clause "A MODULE HYPOTHESIS TAKEN FROM A
PREDECESSOR IS THE TYPE THAT PREDECESSOR DELIVERED" fixes the hypothesis to
that type, and at that type the brief's arrow is

```
LsetFormulaToLevel = Formula Code 2 → LevelFormula     Probe659.agda:109-110
```

The tree inhabits `Formula Code 2` without leaving the syntax chapter, so the
arrow is interderivable with its own target. Three terms, all green:

| name | line | what it says |
|---|---|---|
| `trivial` | `Probe659.agda:121-122` | `⊤̇ : Formula Code 2`. The domain is inhabited by a formula with NO connection to `Lset`. |
| `level-from-obligation` | `:127-128` | the obligation gives `LevelFormula`, at `[LJ-1.651]`'s own term. |
| `level-from-nothing` | `:130-131` | it gives `LevelFormula` at `⊤̇` as well, so the predecessor is not what pays. |
| `obligation-from-level` | `:134-135` | and `LevelFormula` gives the obligation back, by `const`. |
| `obligation-is-the-target` | `:141-143` | the two directions as one pair. |

**So proving the brief's obligation IS proving `LevelFormula`.** The brief
itself records `LevelFormula` as "a type nothing inhabits" (`LJ-1.659.md`,
WHAT IS DELIVERED ALREADY). A dispatch that funds the arrow funds the target
under another name, at no discount.

## 2. AGDA SAYS THE SAME THING IN ITS OWN WORDS

`runs/NO-LAWS.agda.txt`, `runs/nolaws-1.out`, exit 42 in 3.18 s. The
obligation attempted the only way a bare formula allows: hand the delivered
syntax through and read the soundness law off satisfaction itself.

```
NoLaws659.agda:60.16-17: error: [UnequalTerms]
fst ((v ∷ γ ∷ []) T.AtCode.⊨ lf) !=< fst v ≡ Lset (fst γ)
when checking that the expression h has type fst v ≡ Lset (fst γ)
```

**Satisfaction of the syntax is not the equality the syntax is supposed to
certify, and nothing in the tree connects them.** `levelHoodB`
(`src/L/BoundedSubset.lagda.md:108-111`) carries a `Δ₀` certificate
(`:113-139`) and a `Σ₁` certificate (`:145-146`) and NO adequacy theorem;
`graphBndAt` (`src/L/Condensation.lagda.md:2492-2497`) carries `Δ₀` and no
adequacy either. `grep -rn "levelHood\|graphBndAt" src/` returns no consumer
outside `src/L/BoundedSubset.lagda.md` and `src/L/Condensation.lagda.md`.

## 3. I DID NOT PROVE THE OBLIGATION'S TYPE FALSE

I proved that the hypothesis is free and therefore that the arrow is the
target. A refutation of `LevelFormula` is a different task and this one does
not attempt it. `[LJ-1.650]` drew the same line about its own stop
(`agents/tasks/LJ-1-650/lj-1.650-report.md`, section 3).

## 4. THE CORRECTED OBLIGATION, AND IT IS BUILT

The brief says: "If it does not follow, the deliverable is the term naming
what the two-variable form has that the one-variable form does not." **It is
two SEMANTIC laws and nothing else**, stated at `[LJ-1.651]`'s own slot order
(ordinal 0, value 1):

```
Sound    lf = (γ v : SL) → ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩ → fst v ≡ Lset (fst γ)
Complete lf = (γ : SL) → IsOrd (fst γ)
            → ∥ Σ[ v ∈ SL ] ((fst v ≡ Lset (fst γ)) × ⟨ (γ ∷ v ∷ []) ⊨c lf ⟩) ∥₁
```

`Probe659.agda:155-162`. `LsetFormulaWithLaws` (`:164-165`) is the delivered
formula PLUS those two, and `delivered-is-the-first-component` (`:169-171`)
shows the correction ADDS to `[LJ-1.651]` and discards nothing.

**AND FROM THAT HYPOTHESIS THE ARROW COSTS ONE RENAMING.**
`level-from-laws : LsetFormulaWithLaws → LevelFormula`
(`Probe659.agda:199-214`) is green. It is `renameFo swap` on the syntax and
`⊨-rename` on the meaning (`src/FOL/Manipulation/Renaming.lagda.md:127-129`),
and it spends nothing else. **The whole difference between `[LJ-1.651]` and
`[LJ-1.650]` on the syntax side is the slot order**, and 25 non-blank
non-comment lines settle it.

## 5. WHAT THIS STOP ASKS THE MATHEMATICIAN FOR

**Restate the obligation with the two laws in it.** The brief's own
suspicion (premise 3, "the arrow runs the OTHER way") is HALF right: the
arrow at the delivered type is degenerate, but the arrow from the delivered
type PLUS its adequacy runs in the direction the brief wanted, for one
renaming. So `[LJ-1.651]` is not beside the path. **It delivered the first
of three components and the brief priced it as though it were all three.**

The residue is exactly `Sound delivered × Complete delivered`, which is
`[LJ-1.651]`'s own open residue stated as a type. Its report says so at
`agents/tasks/LJ-1-651/lj-1.651-report.md:180`:

> 2. **The adequacy derivation at the hull** stays the open residue:

It is the object to fund, and no dispatch has funded it yet.
