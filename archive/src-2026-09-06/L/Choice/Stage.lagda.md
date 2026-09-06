# The least stage meeting a set (retired 2026-09-06)

The `μ` chapter of `src/L/Choice/Stage.lagda.md`: "some member of `u`
has appeared by stage `σ`" as an ordinal property (`meets`), the
truncated witness that some ordinal qualifies (`meetsSome`, from
`isL-trans` at a member of an `Inhabited` cell), the instance of the
least-ordinal operator (`theEarliestMeet`), and the sealed operator `μ`
with its ordinal-hood projection `μ-ord`.

THE TREE HAD NO CONSUMER FOR ANY OF IT, nor did the rest of the file.
The importers of `L.Choice.Stage` take `bound-below₂`
(`Transversal.lagda.md:61`), `stageBound` (`Order.lagda.md:53`,
`SuccIntoPower.lagda.md:25`), `IsPredOf`, `predOf`, `carveAt`
(`Step.lagda.md:55`), `ord-suc-inj` (`Faithful.lagda.md:53`,
`Pairing.lagda.md:31`) and `stage-below` (`SuccIntoPower.lagda.md:25`),
and every one of those stays in the live file.  The `μ-ord` a name
sweep finds in `src/L/CardinalAbove.lagda.md` is Hartogs' own `μ`,
an unrelated definition with the same spelling.

Retired with it: the empty husks a previous prune left behind, an
`opaque` block and an `opaque / unfolding defStage` block with no
declarations in them, two empty code fences, and the prose of the
`carveMeets`, `defStage` and `Lset-μ` sections whose code was already
gone.  `defStage`, `carveMeets` and `Lset-μ` are named in the retired
prose and exist nowhere in the tree.

```agda
meets : S → S → Ω
meets u σ = ⋁ S (λ z → (z ∈ˢ u) ⊓ (z ∈ˢ Lset σ))

Inhabited : S → Type (ℓ-suc ℓ)
Inhabited u = ∥ Σ[ z ∈ S ] ⟨ z ∈ˢ u ⟩ ∥₁

meetsSome : (u : S) → ⟨ isL u ⟩ → Inhabited u
          → ∥ Σ[ σ ∈ S ] (IsOrd σ × ⟨ meets u σ ⟩) ∥₁
meetsSome u pu = PT.rec squash₁ atMember
  where
  atMember : Σ[ z ∈ S ] ⟨ z ∈ˢ u ⟩
           → ∥ Σ[ σ ∈ S ] (IsOrd σ × ⟨ meets u σ ⟩) ∥₁
  atMember (z , z∈u) = PT.map
    (λ { (α , (ordα , z∈Lα)) → α , (ordα , ∣ z , (z∈u , z∈Lα) ∣₁) })
    (isL-trans {x = u} {y = z} z∈u pu)

theEarliestMeet : (u : S) → ⟨ isL u ⟩ → Inhabited u → LeastOrd (meets u)
theEarliestMeet u pu h = leastOrd (meets u) (meetsSome u pu h)

opaque
  μ : (u : S) → ⟨ isL u ⟩ → Inhabited u → S
  μ u pu h = theEarliestMeet u pu h .fst

opaque
  unfolding μ
  μ-ord : (u : S) (pu : ⟨ isL u ⟩) (h : Inhabited u) → IsOrd (μ u pu h)
  μ-ord u pu h = theEarliestMeet u pu h .snd .fst
```
