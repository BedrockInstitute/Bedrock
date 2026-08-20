# Review of `limit-above`

The obligation is a hole. This file is the obstruction, for the branch
`no-go-stated`.

## THE STATEMENT

```
limit-above :
    (u : S) → IsOrd u
  → Σ[ lam ∈ S ] ( IsOrd lam
                 × ⟨ u ∈ˢ lam ⟩
                 × ((d : S) → ⟨ d ∈ˢ lam ⟩ → ⟨ sucV d ∈ˢ lam ⟩) )
```

It is `Probe439.agda:176-181`, witness `+ω u`. Generic in `u`. No
stage, no cardinal, no band. Agda reports `UnsolvedInteractionMetas`
at `Probe439.agda:90` (`runs/w3-alone-1.out`, exit 42, median 1.08 s,
caliber `GHCRTS="-A64m -I0 -M8g"`). The hole is the third conjunct
`plus-omega-suc`. The first two conjuncts are green: `+ω-ord u ou`
and `+ω-mem u`.

## D-10

Not FALSE. The ω-block is an ordinal, it contains its base, and
successor closure holds once a member can be eliminated into a
finite iterate. `module WithOut` inhabits both
`plus-omega-suc-from-out` and `limit-above-from-out` from that one
elimination (`Probe439.agda:133-170`, median 0.82 s, exit 0).

The live seal exports no elimination. Inventory of
`src/L/Ordinal/StageArith.lagda.md:44-78`: `+ω-in` (`:48`),
`+ω-mem` (`:62`), `+ω-sup` (`:65`), `+ω-iter` (`:68`) are
introductions; `sucIter-ord` (`:72`) and `+ω-ord` (`:76`) are
ordinality facts. Zero eliminations.

## WHERE ROUTE 1 STOPS

`Probe439.agda:90.16-20`, under `eq-above`. After trichotomy on
`d` and `u`, and after trichotomy on `sucV d` and `+ω u`, the open
case is:

```
⟨ u ∈ˢ d ⟩
⟨ d ∈ˢ +ω u ⟩
sucV d ≡ +ω u
⟨ sucV u ∈ˢ d ⟩
goal: ⟨ sucV d ∈ˢ +ω u ⟩
```

The branch `sucV u ≡ d` contradicts by `+ω-iter 3`
(`Probe439.agda:95-102`). The branch `sucV u ∈ d` has no next
named iterate. The elaborator:

```
UnsolvedInteractionMetas
  agents/tasks/LJ-1-439/Probe439.agda:90.16-20
```

Cite: `runs/w3-alone-1.out`.

## THE ONE DECLARATION

Export this TYPE from the `opaque unfolding +ω` block in
`src/L/Ordinal/StageArith.lagda.md`, after `+ω-in` (after
`:59`, before the `+ω-mem` group at `:61`):

```
+ω-out : (u x : S) → ⟨ x ∈ˢ +ω u ⟩
       → ∥ Σ[ n ∈ ℕ ] ⟨ x ∈ˢ sucIter (suc n) u ⟩ ∥₁
```

Last green:
`archive/src/2026-08-09-rud-route/L/Rud/OrdBlocks.lagda.md:107-108`.
It uses `union-ax` on the sealed union, so it belongs inside
`unfolding +ω`. It is not a second ω-block.

`WithOut` (`Probe439.agda:128-130`) is that type as a module
parameter. With it, `limit-above-from-out` is
`+ω u , (+ω-ord u ou , +ω-mem u , plus-omega-suc-from-out u ou)`
(`Probe439.agda:169-170`).

## WHAT WAS NOT DONE

`src/` was not edited. `+ω` was not unfolded from the probe.
No postulate. No second ω-block. The unconditioned
`plus-omega-suc` stays a hole.

## C-42

This is a measurement of the live `+ω` seal at
`src/L/Ordinal/StageArith.lagda.md:44-78`. It does not count other
sites that ask for successor closure of a limit stage. A later
sweep, not this review, reports that count.
