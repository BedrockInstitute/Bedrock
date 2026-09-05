# review-of-dee-in-hull: a STATED NO-GO, with the search's map

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.664
obligation: agents/tasks/LJ-1-664/Probe664.agda::DeeInHull
verdict: **NO-GO on the closed term.** `DeeInHull` of type
`(y : S) → ⟨ y ∈ˢ M ⟩ → ⟨ 𝒟ₒ y ∈ˢ M ⟩` is not inhabited. The
witness meter reads `1 UNRESOLVED of 1, 2.70 s, probe_red=False`
(`agents/tasks/LJ-1-664/runs/meter-obligation.out:2`). The probe is
green and carries no hole (`runs/p-final.out`, `EXIT=0`).

**THIS IS NOT A REFUTATION OF `DeeInHull`.** I did not build a term of
its negation. The statement is true of an elementary hull of a limit
stage. What is measured is that the tree cannot close it today, and
what two suppliers it still owes.

The critic reads this file. It does not close the task.

---

## 1. WHAT THE SEARCH TRIED

Four green measurements and one designed red slice.

1. **The consumer is ten lines, generic, and already written.**
   `At.dee-from-code` (`Probe664.agda:115-118`) is
   `[LJ-1.647]`'s `hull-closed-op∥` at `F = 𝒟ₒ` and `P = Unit*`.
   Meter: `0 UNRESOLVED of 4` including this name
   (`runs/meter-consumer.out:5`). Nothing of that proof is rewritten
   (W2).
2. **The only delivered `𝒟ₒ`-formula is not the Lset shape.**
   `countFo (DefAt u w) ≡ 166` (`Probe664.agda:62-63`, `refl`).
   `[LJ-1.651]`'s `lset-formula` has `countFo ≡ 0`
   (`agents/tasks/LJ-1-651/Probe651.agda:115-116`). The cheap Σ₀
   route does not transfer.
3. **Those 166 constants all lie in some stage.** `defAt-bound`
   (`Probe664.agda:69-71`) is `mkBoundedFo (DefAt u w)`, total at
   `src/L/Axioms/Separation.lagda.md:449`. That is `[LJ-1.514]`'s
   instrument, re-measured at `DefAt`. It transports `DefAt` to a
   STAGE alphabet. It does not produce a `Formula Code`.
4. **`CloseSyntax.close` cannot be applied at `Code`.** The dummy
   `Type ℓ` fails with `[UnequalSorts] Type ℓ != Type (ℓ-suc ℓ)`
   (`runs/close-1.out:5-7`). That is `[LJ-1.652]`'s universe
   mismatch, now printed by Agda, not argued.

The floor of the exact obligation is `runs/FLOOR.agda.txt`: exit 42
at the one designed hole (`runs/floor-1.out:5-7`), 2.40 s, peak
445,038,592 bytes.

## 2. WHAT THE CODE MAP NEEDS

Two different maps were conflated. They are not the same object.

**Map A, `f : A.SM → Code`.** This is what `HullElemDown.WithCode`
takes (`src/L/BoundedSubset.lagda.md:681-682`). **It is already in
the tree:** `hedF` at `src/L/BoundedSubset.lagda.md:1648-1652`,
instantiated as `HEDC = HED.WithCode hedF hedF-spec` (`:1660`). The
brief's premise 2 priced this map as missing. It is not missing. It
lives inside `Devlin55` and is not a HullStage-only object.

**Map B, the operation map `DeeCode∥`.** This is what the consumer
spends (`Probe664.agda:108-110`):

```
(c : Code) → ∥ Σ[ d ∈ Code ] (fst (val d) ≡ 𝒟ₒ (fst (val c))) ∥₁
```

It is not built. Building it is a `wit` at a formula that holds of
`𝒟ₒ (val c)`, or a `hull-closed` search at a `Formula Code 1` that
says the same thing. Both routes need the two suppliers in section 3.

A `Formula Code 1` is not Map A and is not Map B. `[LJ-1.651]`'s
`inF` is that shape for `Lset`. `DefAt` is the only delivered
analogue for `𝒟ₒ`, and it is a `Formula S 2` with 166 constants.

## 3. TWO UNPAID SUPPLIERS, AND EITHER ONE STOPS THE CLOSED TERM

**Supplier 1. `PowIter`.** Verbatim
`src/L/Coding/Bound.lagda.md:151-152`, named at
`Probe664.agda:134-136`, not inhabited. The tree says so itself:
"`powIter` stays a hypothesis: MEASURED, nothing in `src/` proves it"
(`src/L/Coding/Bound.lagda.md:147-149`). Every `𝒟ₒ` lemma in
`src/L/Axioms/Basic.lagda.md` takes `Lset β` as its argument, not a
general hull member. `hull-closed` (`src/L/Hull.lagda.md:415`)
requires the STAGE to satisfy the existential, so
`⟨ 𝒟ₒ y ∈ˢ Lset lam ⟩` is necessary. `Hull⊆L`
(`src/L/Hull.lagda.md:330`) makes it necessary for the conclusion
too: a hull member is a stage member.

**Supplier 2. A `Formula Code 1` that holds of `𝒟ₒ y`.** `DefAt` is
not that formula. Relabel takes it to a stage alphabet
(`defAt-bound`). CloseSyntax cannot then close a parameter at
`Code` (`runs/close-1.out:5-7`). `[LJ-1.651]` closed the Lset
parameter by `con c` because its matrix had no constants. `DefAt`
has 166.

Either supplier unpaid is enough. Both are unpaid.

## 4. D-10, THE TARGET IS NOT FALSE

I did not find a cardinality or Tarskian obstruction to `DeeInHull`.
An elementary hull of `L_λ` at a limit is closed under a definable
operation, and `𝒟ₒ` is such an operation once it is named in the
stage's language and the stage holds its value. Kunen never writes
that name as a formula
(`dev/literature/level-formula-slot-roles.md:79-82`). Devlin writes
a Σ₀ matrix for `L_γ`, not for `𝒟(A)`
(`dev/literature/devlin-II5.md:95-96`, STANDING). The corrected
target beside the original is the same type, conditional on
`DeeCode∥` (or on `PowIter` plus a `Formula Code 1`). The consumer
`dee-from-code` is that corrected target at the first of those
hypotheses.

## 5. THE GRADE, AGAINST Lset

| | Lset (`[LJ-1.651]`) | `𝒟ₒ` (this task) |
|---|---|---|
| delivered formula | `lset-formula` | `DefAt` |
| `countFo` | 0 | 166 |
| cheap matrix | `levelHoodB`, Σ₁, 2 unbounded ∃̇ | none delivered |
| consumer from a code map | 10 lines (`[LJ-1.647]`) | the same 10 lines, at `𝒟ₒ` |

The grade wall of `LsetGraph` (664 constants, 2,287 unbounded ∃̇)
does not recur as a number I counted on `DefAt`'s quantifiers. The
constant count is enough to refuse the zero-constant slide
`[LJ-1.651]` used. I did not build `wit` at `absFo DefAt`. That
route is the one `[LJ-1.646]` refused for `LsetGraph`, and `DefAt`
is a component of that graph (`[LJ-1.498]`'s census: 166 of 664).

---

The next brief should not re-dispatch `DeeInHull` as a closed term
until it names a supplier for `PowIter` or for `DeeCode∥`. The
consumer is paid. Map A is paid. Map B is not.
