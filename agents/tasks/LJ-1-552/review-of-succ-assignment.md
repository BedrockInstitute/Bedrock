# Review of `succ-assignment`

**THE OBLIGATION IS NOT INHABITED. THIS FILE IS THE OBSTRUCTION.** The brief
ordered a NO-GO that names the missing well-order, and this is that stop. It
names TWO well-orders that ARE in the tree, and one term that is not.

`agents/tasks/LJ-1-552/Probe552.agda` is GREEN, exit 0, three cold runs
(`runs/final-1.out` to `runs/final-3.out`). It carries no hole and no
postulate: a hole makes every reduction a claim, and green makes each one a
measurement. Nothing lands in `src/`. The witness meter agrees both ways:
`missing exit=42 agents/tasks/LJ-1-552/Probe552.agda::succ-assignment`,
`1 UNRESOLVED of 1`, `probe_red=False` (`runs/witness-1.out`), and the ten
terms the file does deliver all resolve, `0 UNRESOLVED of 10`
(`runs/witness-2.out`).

## THE STATEMENT

    succ-assignment :
        (δ κ : S) → SuccCardL δ κ
      → ∥ Σ[ s ∈ (⟪ fst δ ⟫ → S) ]
             ( ((k : ⟪ fst δ ⟫) → ⟨ s k ⊆ˢ κ ⟩)
             × ((k k' : ⟪ fst δ ⟫) → fst (s k) ≡ fst (s k') → k ≡ k') ) ∥₁

It is the type `Assignment` (`Probe552.agda:109-113`). **IT CANNOT HAVE
DRIFTED FROM `[LJ-1.549]`'s RESIDUE.** `residue-first-three`
(`Probe552.agda:120-121`) takes `P549.Residue δ κ`
(`agents/tasks/LJ-1-549/Probe549.agda:668-677`) apart and rebuilds nothing:
its three arguments `(s , (sub , (inj , _)))` ARE the brief's three
components, and if the transcription differed in any detail the term would
not typecheck.

## FINDING 1. W3 IS A GO ON BOTH HALVES, AND THE LEASTNESS CLAUSE PAYS

The brief names the widest unmeasured term as "the well-order that picks a
coding for each member of δ", and asks for "the term in this tree that gives,
for a member of δ, a bijection to a subset of κ, or the sentence that there is
none".

**THAT IS TWO TERMS, AND BOTH EXIST.**

**HALF 1, THE COMPARISON.** `member-into-kappa` (`Probe552.agda:158-194`):

    member-into-kappa :
        (δ κ : S) → SuccCardL δ κ
      → (a : S) → ⟨ fst a ∈ˢ fst δ ⟩
      → ∥ ⟪ fst a ⟫ ↪ ⟪ fst κ ⟫ ∥₁

Every member of δ injects into κ, AMBIENTLY. The route is three delivered
terms and one line of trichotomy: `LeastCardInjL`
(`src/L/Cardinal.lagda.md:61`) produces the least ordinal the member's index
injects into; `card-of` (`Probe552.agda:134-138`) shows that ordinal is an
ambient cardinal, because a smaller target would beat the selection;
`ambient→internal` (`Probe552.agda:144-146`, `[LJ-1.528]`'s three lines
re-typed) makes it an L-cardinal; and then `SuccCardL`'s fourth component
refutes the only bad case, because `δ ⊆ c` and `c ⊆ a ∈ δ` give `a ∈ a`.

**THIS IS NOT THE FIRST SPEND OF THE FOURTH COMPONENT AND I DO NOT REPORT IT
AS ONE.** `[LJ-1.550]`'s `site-forced`
(`agents/tasks/LJ-1-550/Probe550.agda:385-390`) already applies it, at a
HYPOTHESISED ambient cardinal μ, concluding `δ ⊆ μ`. The difference is that
here the cardinal is PRODUCED, from the member itself, so the conclusion is an
injection rather than an inclusion. `[LJ-1.549]` reported the clause unused in
its own file and said the whole difficulty sits on the other side of it
(`agents/tasks/LJ-1-549/lj-1.549-report.md`, `## THE LEASTNESS CLAUSE`). This
is that other side, and the clause does pay for it.

**HALF 2, THE PICKING WELL-ORDER.** `memSWO` (`Probe552.agda:221-225`):

    memSWO : (b : S) → SWO ⟪ fst b ⟫

A strict well-order on the members of ANY set of L, not only at a stage. Three
delivered terms: `stageBound` (`src/L/Choice/Stage.lagda.md:366`) puts every
member of a set of L inside one stage, `stageOrder`
(`src/L/Choice/Step.lagda.md:279`) orders that stage, and `pullOrder`
(`src/L/Choice/Step.lagda.md:242`) pulls it back. With `leastOf`
(`src/L/WellOrder/Base.lagda.md:158`) that is a CHOICE-FREE selection out of
any non-empty family over the members of a set of L.

## FINDING 2. THE CHOOSING IS FREE. THE POINTWISE EXISTENCE IS THE WHOLE COST

`Codes δ κ` (`Probe552.agda:295-300`) is a family of small predicates on the
members of `powL κ`, one per member of δ, that is (i) inhabited at every
member of δ and (ii) separating.

- `codes-suffice` (`Probe552.agda:302-326`): `Codes δ κ → Assignment δ κ`.
  Half 2 plus `leastOf`, and NOTHING ELSE. No choice, no extra hypothesis.
- `codes-are-the-obligation` (`Probe552.agda:331-361`):
  `Assignment δ κ → ∥ Codes δ κ ∥₁`.

**SO THE RESIDUE IS EXACTLY THE OBLIGATION AND NOT A WEAKENING OF IT**, and
the reduction buys one real thing: the obligation's truncation and its ambient
FUNCTION are not the obstruction. What is left is pointwise: at ONE member `a`
of δ, an L-SET subset of κ that determines `a`.

## FINDING 3. WHICH TERM I CANNOT SUPPLY

**AN L-SET SUBSET OF κ THAT DETERMINES A MEMBER `a` OF δ WITH `κ ∈ a`.**

Three facts fix that, and each is a term or a `file:line`.

**(a) BELOW κ IT IS FREE, AND ONLY BELOW κ.** `free-below-kappa`
(`Probe552.agda:257-271`) is the assignment on `sucʟ κ`, and it is the
IDENTITY: every member of κ⁺¹ is already a subset of κ
(`[LJ-1.549]`'s `succ-kappa-subsets`,
`agents/tasks/LJ-1-549/Probe549.agda:503-510`). And `sucʟ κ` is a MEMBER of δ
(`free-part-is-a-member`, `Probe552.agda:273-278`, which is `[LJ-1.549]`'s
`succ-kappa-in`, `Probe549.agda:514-536`), so the free part never reaches δ.
**The obstruction is not the first member. It is every member past κ.**

**(b) THE AMBIENT INJECTION IS NOT A SET OF L, AND NOTHING IN THE TREE TURNS
IT INTO ONE.** Half 1 gives `⟪ fst a ⟫ ↪ ⟪ fst κ ⟫`. That is an ambient
function, and the image of the ordering under it is an ambient subset of κ. An
ambient subset of κ is not a member of `powL κ`. **There are exactly TWO
generators of a set of L in the tree and BOTH take a `Formula`:**
`hasSeparationL` (`src/L/Axioms/Full.lagda.md:144-146`, `Formula S 1`) and
`hasReplacementL` (`src/L/Axioms/Full.lagda.md:277-280`, `Formula S 2`).
`hasPowerL` (`src/L/Axioms/Power.lagda.md:187-190`) is the first of the two at
`subFo`, so it is no third shape; and finding 2 shows the only other route,
picking out of a set that already exists, needs the existence first. This is
`[LJ-1.533]`'s wall, at its FOURTH site.

**(c) THE CLASSICAL CODING NEEDS A PAIRING ON κ INSIDE L, AND THE TREE'S
PAIRING IS AMBIENT.** The classical argument codes an ordinal `a` with
`|a| ≤ κ` by a well-ordering of a subset of κ of order type `a`, which is a
subset of κ × κ, carried down to a subset of κ by a pairing. The tree's square
law is `sq` (`src/L/Ordinal/SquareLaw.lagda.md:685-687`), delivered by
`via-col-square` (`:960-961`) and closed by `sq-trunc-closed`
(`src/L/SquareLawClosed.lagda.md:325-327`). Every one of them is an AMBIENT
function `⟪ α ⟫ × ⟪ α ⟫ → ⟪ α ⟫`. An ambient pairing carries an L-set to an
ambient subset of κ, which is (b) again.

## WHY NO COUNTING ARGUMENT CAN REPLACE THE CONSTRUCTION

**THIS IS A READING OF THE TYPES AND NOT A MEASUREMENT, AND I MARK IT AS
ONE.** Finding 1 half 2 puts a well-order on `⟪ fst (powL κ) ⟫`, and `⟪ fst δ ⟫`
is well-ordered as an ordinal, so a comparison of the two is the obvious next
idea. It cannot close the obligation, because the losing branch needs an
ambient Cantor: from an ambient injection `⟪ fst (powL κ) ⟫ ↪ ⟪ fst κ ⟫` the
diagonal subset of κ is AMBIENT, so it is not a member of `powL κ` and no
contradiction follows. Both δ and `powL κ` are sets of L, and nothing in the
hypotheses fixes their AMBIENT sizes. `[LJ-1.535]` closed the counting-site
route by measurement (`agents/tasks/LJ-1-535/lj-1.535-report.md:1`); this is
the same wall seen from the other leg. **No term of this file refutes the
counting route, and I do not claim one.**

## THE SWEEP (C-42)

My refutation is "no delivered term produces an L-subset of κ from an ambient
injection". C-42 asks for the COUNT of sites carrying that shape.

**THE COUNT IS FOUR, and three were already recorded.**

| site | task | what it wanted from an ambient object |
|---|---|---|
| B9, `StageCountedCoded` | `[LJ-1.533]` | a code for `⟪ Lset δ ⟫ ↪ ⟪ δ ⟫` |
| B7, the counting site | `[LJ-1.535]` | a code out of a bare Σ |
| `Link`, the residue's fourth component | `[LJ-1.549]` | a formula describing an ambient assignment |
| **this obligation** | `[LJ-1.552]` | **an L-SET out of an ambient injection** |

**AND THE FOURTH IS NOT THE SAME AS THE THIRD, WHICH IS THE FINDING THE NEXT
BRIEF NEEDS.** `[LJ-1.549]` recorded its residue as two independent missing
inputs, the assignment and its link, and priced the first as "a mathematics
task and not a coding task"
(`agents/tasks/LJ-1-549/lj-1.549-report.md`, item 3 of
`## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE`). **They are not independent.**
Building `s` at a member past κ needs a `Formula` of its own, for the same
reason `Link` does: a set enters L only through a generator, and both
generators take a `Formula`. A brief that funds the assignment as pure
mathematics and the link as pure coding has mis-split the work.

## WHAT WOULD REOPEN THIS

`Codes δ κ` (`Probe552.agda:295-300`), and nothing weaker was found. Its
existence half decomposes, and the decomposition is the priced route:

1. **An INTERNAL injection code `a ↪ κ` for each member `a` of δ.** Half 1
   gives the ambient one. `InternalLeastCard` (`src/L/Cardinal.lagda.md:235`)
   is the shape that would produce the internal one, with `L.InjChain.InclGraph`
   (`src/L/InjChain.lagda.md:575`) for its non-emptiness and
   `L.InjChain.Comp` (`src/L/InjChain.lagda.md:314`) to compose down to κ.
   **I DID NOT BUILD THIS AND I DO NOT CLAIM IT WORKS.** Two things have to be
   checked first: that the carved code lands in the stage
   `InternalLeastCard` selects over, and that the leastness of `δ` refutes the
   bad branch internally the way `member-into-kappa` refutes it ambiently.
2. **The square law INSIDE L**: an L-set injection of κ × κ into κ. The tree
   has only the ambient one, cited in finding 3(c).
3. **The formula that carves the coded subset out of κ**, given 1 and 2, by
   `hasSeparationL`.

Step 2 is a chapter and not a task. **A brief that funds this obligation
without funding step 2 is funding half a task**, and that is the same shape of
error `[LJ-1.549]` recorded about its own residue.

## WHAT WAS NOT DONE

No postulate, no hole, no module parameter that asserts the assignment. `src/`
is untouched. `Link` was not built. B9 and B5 were not touched. No term named
`succ-assignment` exists in any file of this task. I did not commit and did
not push.
