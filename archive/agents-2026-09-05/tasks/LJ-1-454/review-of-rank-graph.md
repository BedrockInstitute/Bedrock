# Review of `rank-graph`

The obligation `rank-graph` is omitted. This file is the obstruction,
for the branch `stop-stated`. W3 failed as an inhabitant: Internal
delivers the ORDER and does not deliver the RANK.

## THE STATEMENT THE BRIEF NAMES

```
rank-graph :
    (a : S) (w : SWO ⟪ fst a ⟫)
  → Σ[ G ∈ S ]
      ((z : S) → ⟨ z ∈ˢ G ⟩
        ≡ ∥ Σ[ m ∈ ⟪ fst a ⟫ ]
              (fst z ≡ pr (⟪ fst a ⟫↪ m) (swo-rank w m)) ∥₁)
```

It is `agents/tasks/LJ-1-454/LJ-1.454.md:11-16`. I did not inhabit
it. I did not weaken it. I did not postulate it. I did not add a
hypothesis. The name does not appear in
`agents/tasks/LJ-1-454/Probe454.agda`. A hole would have been exit
42. The brief says STOP. The probe typechecks (exit 0).

## W3. THE FORMULA INTERNAL WOULD HAVE TO DELIVER

```
rank-formula : Formula S 2
```

Satisfaction at `(z ∷ a ∷ [])` would say `z` is the pair of a
member of `a` and that member's rank. The type is well-formed:
`rank-formula-type` at `Probe454.agda:42-43`. I did not inhabit it.

**Internal does neither: it does not deliver `rank-formula`, and it
does not derive it.**

What it delivers is the ORDER. `≺At` at
`src/L/Choice/Internal.lagda.md:741-742` is

```
≺At : ∀ {n} → Fin n → Fin n → Fin n → Fin n
    → Fin n → Fin n → Fin n → Fin n → Formula S n
```

Eight slot indices. Not `Formula S 2`. The chapter says the order
formula runs no recursion of its own
(`src/L/Choice/Internal.lagda.md:22`): "runs **no recursion of
its own**." And at `:709`: "Nothing recurses, nothing is".

`swo-rank` is Acc recursion
(`agents/tasks/LJ-1-416/Probe416.agda:67-75`). A description of the
order is not a description of that recursion. That distinction is
the finding.

The probe loaded Internal's exported `Formula` constructors as
`order-formulas` (`Probe454.agda:48-72`): `InLimitAt`, `FreeAt`,
`DenoteBody`, `NameAt`, `LexAt`, `≺At`, `LeastNameAt`, `StepBody`,
`StepAt`. A search of `src/L/Choice/Internal.lagda.md` for `rank`
returns no match. `graphAt-value` at `:514` is `satGraphAt`. It is
not the rank graph.

Three forced rechecks of this file, caliber `-A64m -I0 -M8g`, one
Agda process at a time: 2.89 s, 2.12 s, 1.79 s, all exit 0
(`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`). Median
2.12 s. Peak RSS 424902656 bytes. No heap event.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts
`rank-graph` or `rank-formula`. The obligation stays omitted. W3
states the type and the inventory. It does not invent a body.

## D-10

The residue "Internal already has the formula the carve consumes"
is FALSE at this site. The corrected target is the missing
`rank-formula` itself. I did not claim `rank-graph` is false as a
set. I claimed the prescribed formula is missing, so the carve
cannot start.

## C-42

This STOP measures ONE site: whether
`src/L/Choice/Internal.lagda.md` delivers a `Formula S 2` for the
rank of `swo-rank`. It does not inhabit `amb-to-coded`. It does not
inhabit `[LJ-1.419]`'s `bound-into-ord`. Sweep count for a rank
formula in `src/`: 0.
