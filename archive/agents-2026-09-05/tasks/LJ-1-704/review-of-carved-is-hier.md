# Review of `carved-is-hier` — NO-GO (in-tree)

**Missing fact, in three lines or fewer:**
recording-satisfaction — that the A-bounded reading of the recording holds
of the table entry `⟨x, Lset x⟩`, established inductively from the entries
below x (693's `HierInK` chain, gated by 698's `ThroughDoor` / 532's FALSE
stop; 536's `HierBelow`). The obligation is **true in the model** and
**not constructible in-tree**.

## Verdict

`carved ≡ fst (hierL γ hγ oγ)` is **not inhabited in the tree**. The
metatheoretic picture, pinned by this probe, is that the obligation **holds
in the model**: at the frame's stage the A-bounded reading and the L-tower
table are exactly the same set. The NO-GO is a construction stop, not a
truth counterexample.

## Why the reading is exact at the frame's stage

The 698 frame (`LJ-1-698.Probe698.Carved`, `Probe698.agda:107-120`) sets
`φᵣ = relativize (LsetS γ oγ) (recordedFo (γ , hγ))` (`:108-109`) and
`σ = bound-of γ oγ hγ .fst` (`:111-112`), with
`bound-of = mkBoundedFo (relativize …)` (`:97-101`). `mkBoundedFo` bounds a
constant `con c` at `stage (fst c)` (`L/Axioms/Separation.lagda.md:431-432`),
and `stage x = theEarliest x` — the **least** ordinal with
`x ∈ Lset σ` (`L/Stage.lagda.md:176-181`). The constants of `φᵣ` are
`con γ` and `con (Lset γ)` (relativization bounds every raw quantifier at
the constant `Lset γ`, `FOL/Manipulation/Relativize.lagda.md:57,60`; the
recording is `∃̇∈ (con γ) …`, `Probe698.agda:84-85`); both first appear at
stage γ + 1 (`ord∈Lset-suc`, `L/Ordinal/Stages.lagda.md:434`; and not
earlier, the harder half of the stage-ordinal theorem, `:179+`). So the
frame sits on **σ = γ + 1**, and `Lset σ = 𝒟ₒ (Lset γ)`
(`L/Axioms/Basic.lagda.md:196` `Lset-suc`).

At that height there is no junk. Every element of `Lset (γ + 1)` is a
definable subset of `Lset γ`: `defSet ⊤̇ ≡ A` and every member of `Def A` is
a subset of `A` (`L/Definability.lagda.md:164-166`, `:178`). So every
`w ∈ Lset σ` satisfies `w ⊆ Lset γ = A`, and the A-bounded reading of
`φᵣ` at `⟨x, w⟩` sees the full content of `w`: the StepAt content is
"w is the table below x", which forces `w ≡ Lset x`; and the stage holds
exactly the ordinals below it (`Stages.lagda.md:179+`), so the `x` bound at
`con γ` with the recording content is exactly `x ∈ γ`. Hence in the model

```
carved = { ⟨ x , Lset x ⟩ | x ∈ γ } = fst (hierL γ hγ oγ).
```

The junk argument I started with — `w' = Lset x ∪ { Lset γ }`, with
`w' ∩ Lset γ = Lset x` — only works at a **higher** stage: `w'` has rank
γ + 3, so it fits in `Lset σ` only for σ ≥ γ + 3. Had the frame taken a
higher bound, the reading would over-count and the obligation would be
false. The equality is a property of the earliest stage, and the frame
sits on it. This is a fragility worth recording: **any future task that
re-bounds `φᵣ` to a larger stage loses the equality.**

## The in-tree blocker

Both inclusions of the obligation wait on the same unlanded chain:

- `hierL ⊆ carved`: the A-bounded content of `⟨x, Lset x⟩` is
  established only through the entries `⟨u, Lset u⟩` below x. That
  induction is 693's `HierInK` (`LJ-1-693.Probe693.HierInK`,
  `Probe693.agda:59-62`), which 698 showed to be gated by `ThroughDoor` —
  itself blocked because `ApproxInK` is FALSE (`Probe532.agda:206-209`;
  698 review: the `𝒟ₒ-intro` route dies there).
- `carved ⊆ hierL`: needs the model-exactness of the previous section as a
  tree-internal content lemma, i.e. the same satisfaction induction run
  backward — 536's `HierBelow`, also unlanded (536 subgoal of the door
  chain).

The missing fact, stated (Probe704 section 3,
`agents/tasks/LJ-1-704/Probe704.agda:97-100`):

```
table-sat : (x : V ℓ) → ⟨ x ∈ˢ γ ⟩
            → (the A-bounded reading of φᵣ at ⟨ x , Lset x ⟩
               holds in the stage model)
```

by induction on the ordinal, the step consuming the entries below x.

## In-tree facts this probe established

`agents/tasks/LJ-1-704/Probe704.agda` compiles (GREEN, `runs/p-4.out`):

- `gamma-below-sigma : ⟨ γ ∈ˢ Lset σ ⟩` (`Probe704.agda:51-52`): the bound
  the 698 frame proved (`hφ : BoundedFo (Below′ σ) φᵣ`, `Probe698.agda:114-115`)
  is a stage fact of the ordinal itself.
- `ord-in-Lset : (c : V ℓ) → ⟨ c ∈ˢ γ ⟩ → ⟨ c ∈ˢ Lset γ ⟩`
  (`Probe704.agda:56-59`): one line on `Lset-cumul` + `ord∈Lset-suc`
  (`L/Ordinal/Stages.lagda.md:164-168`, `:434`); the in-tree leg of the
  "member of the ordinal sits in its stage" fact used throughout the
  review.

The witness meter on the obligation is 1 UNRESOLVED of 1,
`probe_red=False` (`runs/meter-obligation.out`, `missing exit=42 2.25 s`,
`[NotInScope]` at the generated witness for `carved-is-hier`).

## Disposition

NO-GO. Nothing is landed in `src/`. The model says the obligation is true;
the tree cannot build it without the 693/698/536 satisfaction chain, which
this task neither found nor can find in one probe. If the program re-queues
this target, it should queue the chain, not the equality.
