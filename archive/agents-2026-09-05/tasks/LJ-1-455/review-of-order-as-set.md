# Review of `order-as-set`

The obligation `order-as-set` is omitted. This file is the obstruction,
for the branch `stop-stated`. W3 failed as an inhabitant: Internal
delivers `≺At` at eight `Fin n` indices, and those eight cannot be
brought to `Formula S 1` from a set `a` alone.

## THE STATEMENT THE BRIEF NAMES

```
order-as-set :
    (a : S) (w : SWO ⟪ fst a ⟫) (bnd : S)
  → ((x y : S) → ⟨ x ∈ˢ fst a ⟩ → ⟨ y ∈ˢ fst a ⟩
               → ⟨ pr (fst x) (fst y) ∈ fst bnd ⟩)
  → Σ[ R ∈ S ] ((z : S) → ⟨ z ∈ˢ R ⟩
      ≡ ((z ∈ˢ bnd) ⊓ ((z ∷ []) ⊨ orderFo a)))
```

It is `agents/tasks/LJ-1-455/LJ-1.455.md:11-16`. I did not inhabit
it. I did not weaken it. I did not postulate it. I did not add a
hypothesis. The name does not appear in
`agents/tasks/LJ-1-455/Probe455.agda` as a definition. A hole would
have been exit 42. The brief says STOP. The probe typechecks
(exit 0).

## W3. THE FORMULA THE CARVE WOULD HAVE TO CONSUME

```
orderFo : (a : S) → Formula S 1
```

Satisfaction at `(z ∷ [])` would say `z` is a pair in the order of
`a`. The type is well-formed: `orderFo-type` at
`Probe455.agda:45-46`. I did not inhabit it.

**Internal delivers `≺At`, and `≺At` is not that formula.**
`src/L/Choice/Internal.lagda.md:741-742`:

```
≺At : ∀ {n} → Fin n → Fin n
    → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Formula S n
```

Eight slot indices. Not `Formula S 1` with seven slots fixed at
`a`. The slots are `R P s₁ a₁ e₁ s₂ a₂ e₂`. Each is `Fin n`
(`src/FOL/Syntax.lagda.md:43-44`). `inclFo` fixes its extra slot
by `con D` in a Term position
(`src/L/InjChain.lagda.md:445-446`). `≺At` has no Term position.
The reduction is not a specialisation.

The only `Formula S 1` `≺At` forms without a restatement is
`≺At-at-one` (`Probe455.agda:50-51`): every index is `zero`. The
argument `a` does not appear.

What the formula still needs, from `a` alone, is named in
`lj-1.455-report.md` under D-10: the code-order `R`, the
parameter-order `P`, and either two names' data or (for `StepAt`)
the carrier and the two code sets, plus a pairing atom for `z`.

Three forced rechecks of this file, caliber `-A64m -I0 -M8g`, one
Agda process at a time: 1.50 s, 1.54 s, 1.56 s, all exit 0
(`runs/w3-2.out`, `runs/w3-3.out`, `runs/w3-4.out`). Median
1.54 s. Peak RSS 440729600 bytes. No heap event.

## WHAT WAS NOT DONE

No axiom. No postulate. No module parameter that asserts
`order-as-set` or `orderFo`. The obligation stays omitted. W3
states the type and the slot measurements. It does not invent a
body.

## D-10

The residue "fix seven slots of `≺At` at `a` and separate once"
is FALSE at this site. The corrected target is a formula whose
extra parameters the brief is allowed to name. I did not claim
the order-as-a-set is false as a set. I claimed the prescribed
slot reduction does not exist, so the carve cannot start.

## C-42

This STOP measures ONE site: whether
`src/L/Choice/Internal.lagda.md` delivers a `Formula S 1` for the
order of a set `a` by fixing seven of `≺At`'s slots at `a`. It
does not inhabit `rank-graph`. It does not inhabit `rank-formula`.
Sweep count for `≺At` used as `Formula S 1` in `src/`: 0.
