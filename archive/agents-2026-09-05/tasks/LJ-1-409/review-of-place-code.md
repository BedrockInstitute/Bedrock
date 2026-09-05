# LJ-1.409 review of `place-code`: the stated NO-GO

slot: `coder`. This file states the NO-GO that the brief's branch
`no-go-stated` asks for. Evidence is `file:line` throughout.

## THE OBLIGATION

`agents/tasks/LJ-1-409/Probe409.agda:173-177` states `place-code` exactly
as the brief writes it:

```agda
place-code :
    (a c : S)
  → ∥ Σ[ F ∈ S ] InjCode F a c ∥₁
  → ∥ Σ[ F ∈ Mem (Lset (SiteBound.β a)) ]
          InjCode (SiteBound.up a F) a c ∥₁
```

The term follows `[LJ-1.397]`'s `code-lands` shape
(`agents/tasks/LJ-1-397/CodeLands.agda:46-62`). The given code is replaced
by the trim. The membership

```agda
p : ⟨ fst G ∈ Lset (SiteBound.β a) ⟩
```

at `Probe409.agda:189-190` is a hole. Agda reports
`UnsolvedInteractionMetas` at `Probe409.agda:190.9-13`
(`agents/tasks/LJ-1-409/runs/place-code-hole.out`).

## THE VERDICT

NO-GO on the named construction. This is an obstruction, not a refutation
of the type. I did not build a term of the negation. I did not prove the
type false.

What closed: the trim is a code. `trimmed-code`
(`Probe409.agda:160-166`) is green. The four conjuncts of `InjCode` hold
for `F′` (`TrimCode.trimmed`, `Probe409.agda:154-155`). The W3 probe
`trim-conj4` is green (`Probe409.agda:100-105`,
`runs/trim-conj4.out`, exit 0, 1.66 s).

What did not close: membership of that trim in `Lset (SiteBound.β a)`.
No delivered lemma pays it. No finite successor count `n` of
`SiteBound.β a` pays it at the stated generality.

## THE TRIM, WHICH DID CLOSE

`F′` is carved from `PairBound.bnd a c` by `hasSeparationL` at the formula
`inFo F = var zero ∈̇ con F` (`Probe409.agda:51-52, 64-68`), the same
carve Comp uses at `src/L/InjChain.lagda.md:339`.

- Downward, free: `F′-out` (`Probe409.agda:73-81`). A pair in `F′` is a
  pair in `F` by `F′-spec`. Conjunct 4, `svAt` and `injAt` transfer along
  this reading. The bound is not read.
- Upward, the bound is read: `F′-in` (`Probe409.agda:85-96`). A pair over
  `a` and `c` that `F` holds is in `PairBound.bnd a c` by `PairBound.below`
  (`src/L/InjChain.lagda.md:299-300`) and back in `F′` by the separation
  spec. `domAt`'s "pair is in the code" conclusion uses this.

W2: every statement above is generic in `a` and `c`. No cardinal, no
ordinal and no numeral is named.

## WHY THE PLACEMENT DOES NOT CLOSE

The brief named `bound-below₂` (`src/L/Choice/Stage.lagda.md:370-373`)
and `stageBound` (`:366-368`) as the placement tools.

`bound-below₂` places `y` given `y ∈ x ∈ a`. The trim `G` is a set of
pairs over `a` and `c`. It is not a member of a member of `a`. The lemma
does not apply.

`stageBound a` is `bound2 ω (stage a)` (`:368`). `SiteBound.β a` is that
ordinal (`src/L/Cardinal.lagda.md:165-166`). It sits above `ω` and above
the stage of `a`. It does not sit above the stage of an arbitrary code
`F`, and it does not sit above the pair-bound of `a` and `c`.

The construction of `F′` mentions `F` as a constant. That is why the
stage of the carved set follows `F`.

1. `inFo F` is `var zero ∈̇ con F` (`Probe409.agda:51-52`).
2. `hasSeparationL` reflects the formula at a stage above the bound's
   own stage (`src/L/Axioms/Full.lagda.md:150-151`):
   `R = mkReflect φ sa (stage-ord (fst a) (a .snd))`.
3. `mkBoundedTm (con c)` is `stage (fst c) (c .snd)`
   (`src/L/Axioms/Separation.lagda.md:432`). For `con F` that is the
   stage of `F`.
4. `mkReflect` takes `bound2` of that bounding ordinal and the bound's
   stage (`src/L/ReflectFo.lagda.md:533-535`). The reflecting stage `σ`
   is above the stage of `F`.
5. The carved set is `carve ψ` with `carve ψ ∈ 𝒟ₒ (Lset σ)`
   (`src/L/Axioms/Separation.lagda.md:293-294`).
6. `Lset (sucV σ) ≡ 𝒟ₒ (Lset σ)` (`src/L/Axioms/Basic.lagda.md:196`).
   So the carved set lands in `Lset (sucV σ)`, one successor above a
   stage that is already above `F`.

`F` is an arbitrary element of `S`. Its stage is not bounded by any
fixed finite iterate of `sucV` on `SiteBound.β a`.

## THE NUMBER THE BRIEF ASKED FOR

The brief asked for the smallest `n` such that

```
⟨ fst F′ ∈ˢ Lset (<n successors of SiteBound.β a>) ⟩
```

is provable, with the lemma for each step.

No such finite `n` exists at the stated generality. A number relative to
`SiteBound.β a` would have to bound the stage of `F`. `F` is free. A
guess is not a return; this is the measurement.

A number relative to the reflecting stage of the trim formula does exist
and is `1`: `Lset-suc` (`src/L/Axioms/Basic.lagda.md:196`) places the
carve in the successor of that stage. That stage is not `SiteBound.β a`,
and it still depends on `F`. It does not answer the brief's question.

The chapter's `SiteBound.β` would have to grow past the stage of `F` to
place this trim. Changing the chapter is a later task. This task does
not touch `src/`.

## THIS IS NOT A REFUTATION OF THE TYPE

`place-code` is existential on both sides. A different replacement than
this trim might still land in `Lset (SiteBound.β a)`. I did not search
for one beyond the construction the brief named. I did not refute the
type. D-10: I recorded the obstruction of the named construction beside
the original target. I did not treat the original target as false.

## THE SWEEP (C-42)

This return is not a refutation, so C-42's count is of the named shape,
not of a false statement.

Shape: the implication from `∥ Σ[ F ∈ S ] InjCode F a c ∥₁` to a code in
`Mem (Lset (SiteBound.β a))`.

COUNT of that implication in live `src/`: 0. `IsCardinalL` keeps the `S`
quantifier (`src/L/Cardinal.lagda.md:231-233`). `InternalLeastCard.Good`
already uses the `Mem` form (`:240`). Nothing in `src/` proves the
implication.

COUNT of that implication as a stated obligation: 2.

- `[LJ-1.397]` `code-lands`, conditional on `Placement`
  (`agents/tasks/LJ-1-397/CodeLands.agda:40-41, 46-49`).
- this task, with `Placement` removed.

Cousins, not this shape: `[LJ-1.403]` gaps 1 and 2
(`agents/tasks/LJ-1-403/lj-1.403-report.md:144-163`) name the same
placement as a caller-supplied type, not as a term.
