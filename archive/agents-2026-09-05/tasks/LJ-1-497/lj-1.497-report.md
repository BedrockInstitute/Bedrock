# LJ-1.497 report: the bridge from `rankFo` to `swo-rank`

## HEAD
head_slot: coder
machine: shared
verdict: NO-GO

## VERDICT

**NO-GO, and the statement is FALSE, not merely unbuilt.** I did not fail to
inhabit `rankFo-adequate`. I REFUTED it, and the refutation typechecks:

    no-adequacy :
        (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
      → RankFoAdequate → Empty.⊥

`Probe497.agda:435-451`. Exit 0, caliber `-A64m -I0 -M8g`, one Agda process.
The whole file is green: `runs/full-1.out` through `runs/full-4.out`.

**THE SLOT THAT DIVERGES is the THIRD existential of `rankFo`**, the `r` slot
(`Probe497.agda:258`, the inner `∃̇ (` of that line opens it; the slot is read
by `prAtL (s3 zero) (suc zero) zero` at `Probe497.agda:259` and pinned by
`supAt zero (suc zero)` at `Probe497.agda:263`). It is the second component of
the coded pair. **It is the very slot `range-clause` reads**
(`agents/tasks/LJ-1-490/Probe490.agda:280`, `⟨ fst y ∈ fst B.C ⟩`).

**THE DIVERGENCE IS IN THE RANK, NOT IN THE FORMULA.** The brief predicted a
NO-GO "would retire `[LJ-1.475]`'s formula rather than extend it". **It does
not.** `[LJ-1.475]`'s formula computes the standard rank, `ρ(m) = sup{ρ(y)+1 :
y < m}`, which is `∅` at a minimal member. `swo-rank` computes something else:
**it never takes the value `∅` at all.** The formula is sound; the rank is the
term that must change.

I did not postulate. I did not weaken the rank to a bound. I did not claim
`InjCode`, a limit, or `Residue`. I did not attempt `range-clause`. I wrote
`review-of-rankFo-adequate.md`. Nothing landed in `src/`.

## 1. W3, THE RANK AT A MEMBER, FIRST

**GO on the question the brief asked, and the answer is the finding.**

The brief asked: "If the recursion will not reduce at a slot the formula can
name, the bridge cannot be stated and the task stops at its cheapest point."

**The recursion DOES reduce at that slot.** `rank-at` typechecks
(`Probe497.agda:203-208`). Typechecked ALONE, with the formula and the
obligation omitted, at 194 lines. Exit 0 on the first attempt.

Caliber `-A64m -I0 -M8g`, set on the pane, untouched. One Agda process. The
probe interface was deleted before every kept recheck.

- `runs/w3-1.out` 1.80 s, 295141376 bytes, exit 0
- `runs/w3-2.out` 1.72 s, 295108608 bytes, exit 0
- `runs/w3-3.out` 1.85 s, 295141376 bytes, exit 0

**W3 median wall 1.80 s. Peak RSS 295141376 bytes.** No heap event.

ESTIMATE for W3 was about 30 lines and under 45 seconds. **MEASURED: 194
lines and 1.80 s.** The line estimate is off by 6x and the reason is worth
recording: `swo-rank` cannot be named without an `SWO`, the only delivered
route to an `SWO` at `a` is `OrdSWO` (`Probe490.agda:165-201`), and `OrdSWO`
drags in `ord-tri`, `regularityV`, `∈-irrefl`, `member` and `↪-inj`. The rank
alone is 40 lines; its well-order is 40 more.

**What the reduction reduced TO is the whole finding.** `rank-at-has-∅`
(`Probe497.agda:213-216`):

    rank-at-has-∅ :
        (a : S) (oa : IsOrd (fst a)) (m : S) (mx : ⟨ fst m ∈ fst a ⟩)
      → ⟨ ∅ ∈ fst (rank-at a oa m mx) ⟩

**`∅` is a member of the rank of EVERY member of `a`.** So `swo-rank` never
takes the value `∅`. A rank function on a well-order takes the value `∅` at
its minimum. `swo-rank` is therefore not a rank function.

## 2. THE D-10 READING, BEFORE THE AGDA

`[LJ-1.475]` is GO on `rank-formula` and left the adequacy
(`agents/tasks/LJ-1-475/lj-1.475-report.md:107`, "**GO.** W3 typechecks
`fn-clause : Formula S 3`"). Slot by slot, in the env `rankFo`'s innermost
body uses, `(f ∷ r ∷ m ∷ q ∷ z ∷ [])`:

| clause | `file:line` | what it asserts |
|---|---|---|
| `var zero ≐ con Q` | `Probe497.agda:257` | `q` is the parameter set `Q` |
| `prAtL (s3 zero) (suc zero) zero` | `Probe497.agda:259` | `z` is the pair `⟨m , r⟩` |
| `var (suc zero) ∈̇ con a` | `Probe497.agda:260` | `m` is a member of `a` |
| `fnAt f q m` | `Probe497.agda:225-229` | `f` is single-valued, and `dom f` is exactly `{x : ⟨x , m⟩ ∈ q}` |
| `assignAt f q` | `Probe497.agda:231-239` | each `f x` is `⋃{sucV (f y) : ⟨y , x⟩ ∈ q}` |
| `supAt f r` | `Probe497.agda:252-253` | `r` is exactly `⋃{sucV (f x) : x ∈ dom f}` |

`supAt` is built on `extAt`, and **`extAt` is a BICONDITIONAL**
(`src/L/Coding/Model.lagda.md:662-664`, two implications conjoined). So the
formula does not merely BOUND the `r` slot. **It PINS it.** At an `m` with no
`q`-predecessor, `dom f` is empty, and `r` is pinned to a set with no member.

What `swo-rank` computes (`Probe497.agda:74-135`, rebuilt at `[LJ-1.490]`'s
delivered type, `Probe490.agda:123-157`): `go a (acc rs)` is
`boundingOrd A (λ x → pred a ih x .fst) …`, and **the index type is `A`, the
WHOLE carrier, not the predecessors of `a`** (`Probe490.agda:145`). Every
non-predecessor is padded with `∅` (`Probe490.agda:134-135`,
`predAt a b (eq _) _ = ∅ , ∅-ord` and the `gt` line). `boundingOrd` is
`⋃ (sett X (sucV ∘ f))` (`src/L/Ordinal.lagda.md:156-167`), so **each padded
point contributes `sucV ∅ = {∅}` to the union, and `∅` lands inside every
value.**

**The two do not correspond, and they diverge at the `r` slot.** The formula
says `∅` at a minimal member; the rank says a set containing `∅`.

## 3. THE MEASUREMENT

Three typechecked terms, in order of strength.

**(a) The formula side, `Fml.sup-no-member`** (`Probe497.agda:329-334`,
resting on `body-absurd` at `Probe497.agda:315-326`). At a
pair-free `f`, the `supAt` clause pins `r` to a set with NO member. This is
the reading of `extAt` made into a term, not a claim about it.

**(b) The link to `Q`, `Fml.fn-no-pairs`** (`Probe497.agda:299-312`). If `m`
has no `q`-predecessor, then `f` is pair-free. This turns the hypothesis from
one about the existential witness `f` into one about the parameter `Q`.

**(c) The Q-INDEPENDENT divergence, `divergence`** (`Probe497.agda:351-362`).
For ANY `Q`, at a `Q`-minimal member of `a`, the `fnAt` and `supAt` clauses
together contradict the adequacy conclusion. **This is the finding that does
not depend on my choice of `Q`.**

**(d) The unconditional refutation, `no-adequacy`** (`Probe497.agda:435-451`).
`Q := ∅` makes every member `Q`-minimal (`empty-is-minimal`,
`Probe497.agda:365-368`), and the empty approximating function satisfies all
three clauses, so `rankFo ∅ a` IS satisfied, at the pair `prʟ m ∅ˢ`
(`Sat.sat`, `Probe497.agda:425-428`). Feeding that to `RankFoAdequate` and
using `pr-inj` (`src/V/Coding.lagda.md:178`) forces `∅ ≡ swo-rank …`, which
`rank-at-has-∅` refutes.

**A CRITIC SHOULD PRESS HERE, so I state the limit myself.** `no-adequacy`
realizes the `Q`-minimal hypothesis with `Q := ∅`, which is a degenerate `Q`.
That alone would only prove the brief's telescope too loose, because it leaves
`Q` free with no hypothesis at all. **The `Q`-independent content is (c), and
(a) plus `rank-at-has-∅` carry it**: for every `Q`, the formula pins the `r`
slot empty wherever `m` is `Q`-minimal, and `swo-rank` is never empty. A
well-order `Q` HAS a minimal member of `a`. I did not build that last step,
because proving it needs `Q` read as an `SWO`, which is the reading the
formula does not perform.

Full-file rechecks, same caliber, interface deleted before each:

- `runs/full-1.out` 2.72 s, 358219776 bytes, exit 0
- `runs/full-2.out` 2.67 s, 358203392 bytes, exit 0
- `runs/full-3.out` 2.66 s, 358219776 bytes, exit 0
- `runs/full-4.out` 2.67 s, 358219776 bytes, exit 0 (after the cure probes were reverted)

**Full-file median wall 2.67 s. Peak RSS 358219776 bytes.** 451 lines. No heap
event. ESTIMATE for the Agda was about 170 lines, of which about 45 the
obligation. MEASURED 451 lines, of which the refutation chain (a)-(d) is 143.

## 4. THE CURE, PRICED, NOT BUILT

Two measurements, both preserved, both reverted before the final green check.

**The obvious cure does NOT typecheck.** Index `boundingOrd` over the
predecessors `Σ[ x ∈ A ] (x <∙ a)` instead of the whole carrier:

    Type (ℓ-suc ℓ) != Type ℓ
    when checking that the expression Σ-syntax A λ x → x <∙ a has type Type ℓ

`runs/cure-level.out`, exit 42. **This is why the padding is there.**
`boundingOrd` wants a small index (`src/L/Ordinal.lagda.md:154`,
`(X : Type ℓ)`), and `OrdSWO`'s order is `_∈ᵗ_`-valued, hence `Type (ℓ-suc ℓ)`
(`Probe490.agda:167-168`). `[LJ-1.416]` had no small predecessor type, so it
padded over `A`. The padding is a universe artefact, not a mathematical
choice.

**The small membership IS small enough.** `⟨ x ∈ₛ y ⟩ : Type ℓ` typechecks,
`runs/cure-small.out`, exit 0. So the route exists: re-base `OrdSWO`'s order
on `_∈ₛ_` rather than `_∈ᵗ_`, which puts `SWO` at `ℓₚ = ℓ`, which makes
`Σ[ x ∈ A ] (x <∙ a) : Type ℓ`, which `boundingOrd` accepts.

**I DID NOT BUILD THAT.** It needs `tri₁`, `irr₁`, `trans₁` and `wf₁` restated
at the small membership, and `regularityV` and `ord-tri` deliver the large
one. `∈∈ₛ` converts (`src/L/Constructible.lagda.md:46`), so the conversion is
available at every step, but the count of steps is not measured and I will not
price it from this task's seconds.

## WHAT THE RANGE CLAUSE NEEDS NEXT

**`b` IS DETERMINED, NOT FREE.** `[LJ-1.490]` measured it
(`agents/tasks/LJ-1-490/lj-1.490-report.md:271-272`) and this task does not
disturb it: the codomain is `C`, the bounding ordinal
`Bound.C` (`Probe490.agda:216-217`), not a free parameter.

**WHAT REMAINS BETWEEN THIS TASK AND `range-clause` IS NOT A BRIDGE. IT IS A
REPLACEMENT RANK.** The type that must be delivered before the adequacy can
even be stated truthfully:

    -- the rank whose bounding ordinal is taken over the PREDECESSORS only
    swo-rank′ : {A : Type ℓ} (w : SWO {ℓc = ℓ} A) → A → V ℓ

    swo-rank′-least :
        {A : Type ℓ} (w : SWO {ℓc = ℓ} A) (a : A)
      → (SWO.wf∙ w a is at a minimal a) → swo-rank′ w a ≡ ∅

and it is blocked today by `runs/cure-level.out`. The order must be re-based
on `_∈ₛ_` first. **That re-basing is the next brief, and it is a coder task,
not a bridge.**

Only then does the adequacy become statable:

    rankFo-adequate′ :
        (Q a : S) (oa : IsOrd (fst a)) (z : S)
      → (Q reads as the ∈-order on a)          -- MISSING, see below
      → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩
      → Σ[ m ∈ S ] Σ[ mx ∈ ⟨ fst m ∈ fst a ⟩ ]
          (fst z ≡ pr (fst m) (fst (rank-at′ a oa m mx)))

**AND A SECOND HYPOTHESIS IS MISSING FROM THE BRIEF'S TELESCOPE, INDEPENDENT
OF THE RANK.** `rankFo Q a` reads its order from the SET `Q`, through
`appAt q x m` (`Probe497.agda:228-229`). `swo-rank` reads its order from
`oa : IsOrd (fst a)`, through `OrdSWO` (`Probe490.agda:212`). **Nothing in the
brief's type links them.** Any adequacy statement needs the hypothesis that
`Q` is the ∈-order on `a`, as a set of pairs. `[LJ-1.475]` said this in
prose (`agents/tasks/LJ-1-475/lj-1.475-report.md:249`,
"a well-order from the set `Q`, which this formula does not read"). **This
task turns that prose into a refutation.**

**THE THREE OTHER CONJUNCTS.** `[LJ-1.490]` reported that `svAt`, `domAt` and
`injAt` also read the second component of a pair in the carve and want the
same adequacy (`agents/tasks/LJ-1-490/lj-1.490-report.md:275-279`). This task
did not measure them. **But the brief's promise that "A GO UNBLOCKS ALL FOUR
CONJUNCTS AT ONCE" now cuts the other way: a NO-GO on the adequacy blocks all
four**, and the cure is one term, `swo-rank′`, not four.

**Do not attempt `range-clause`.** I did not.

**Do not fund the next task against this task's seconds for the re-basing.**
The cure is measured only as an error message, not as a build.

## 5. THE BRIEF'S TELESCOPE COULD NOT BE STATED

`Probe497.agda:275-280`. The brief writes
`(Q a z : S) → ⟨ (z ∷ []) ⊨ rankFo Q a ⟩ → …`. `swo-rank` needs an `SWO`, and
the only delivered route to one at `a` is `OrdSWO.w (fst a) oa`
(`Probe490.agda:212-213`), which needs `oa : IsOrd (fst a)`. **I added `oa`,
and it is the predecessor's delivered hypothesis, not one I chose to close a
conjunct** (the coder clause: a module hypothesis taken from a predecessor is
the type that predecessor delivered). I did not invent any other hypothesis.

## 6. W2, W4, C-42

**W2.** Every term is generic in the carrier. `Rank`, `RankAt`, `pred`,
`step`, `go` and `swo-rank` are written once at an abstract `A : Type ℓ` and
an abstract `SWO`. `rankFo` and its clauses are written at slots and
instantiated by one pin each. No stage, no cardinal, no numeral, no `Lset` is
named. No deadline asked for a fixed form. No conflict.

**W4.** No module was retired. Nothing moved to `archive/`. **A candidate is
now on the table and I am NOT taking it:** `swo-rank`'s padding is a defect,
but `swo-rank` lives in a probe, not in a module of `src/`, so W4 does not
reach it. The rule is module-granular and this is not a module.

**C-42, the sweep.** A refutation measures ONE site. The site is
`swo-rank`'s use of `boundingOrd` over the whole carrier. **The shape is
"a bounding ordinal used where an exact one is meant".** Counts, before any
opinion:

- `grep -rn boundingOrd src` gives **26 occurrences in 11 files**. Of those,
  **9 are call sites**, one in each of `L/Reflect.lagda.md:447`,
  `L/InjChain.lagda.md:82`, `L/Recursion.lagda.md:136`,
  `L/Axioms/Full.lagda.md:222`, `L/Axioms/Basic.lagda.md:403`,
  `L/Axioms/Separation.lagda.md:537`, `L/Axioms/Power.lagda.md:147`,
  `L/Choice/Before.lagda.md:1015` and `L/Coding/EnvSet.lagda.md:95`. The rest
  are 9 import lines, 5 in the defining chapter `L/Ordinal.lagda.md`, 2 in the
  generated `Everything.lagda.md`, and 1 prose line at
  `L/InjChain.lagda.md:69`.
- **All 9 call sites consume the `∈ β` conclusion and none reads the value.**
  Seven pass a `stage`-valued family on the call line
  (`InjChain:82`, `Recursion:136`, `Full:222`, `Separation:537`, `Power:147`,
  `Before:1015`, `EnvSet:95`); `Basic:403` is the two-element merge inside
  `bound2`; `Reflect:444-449` states its own conclusion as
  `⟨ pickStage ψ (…) ∈ β ⟩` for every index. **So the shape measured here
  does NOT propagate: the count is 9 and the exposure is 0.**
- `src/`: 0 hits for `swo-rank`. 0 hits for `rankFo`. The defect has not
  reached the tree.
- The archive already knew the shape: `boundingOrd` "supplies a *common
  stage*" (`archive/dev/JOURNAL-archived.md:3635`). **Common, not least.**
  Every one of the 9 sites is safe wherever a COMMON bound is what is
  wanted, and unsafe only where an EXACT value is wanted. This task is the
  first site in the campaign where an exact value was wanted.

**I read the 9 call lines and each one's stated conclusion; I did not read
the 9 bodies.** The count is the deliverable C-42 asks for before the cure is
priced. A body audit is a separate task and I do not price it here.

**D-26** (`dev/LESSONS.md:1735`): a definable power carries no generation
data and needs syntax. `rankFo` is that syntax. This task does not weaken
D-26; it says the META-level rank the syntax is measured against is the wrong
term.

**P-l** (`dev/LESSONS.md:2357`): no type here names a transparent stage
presentation. `a` and `Q` are abstract elements of `S`.

**D-10** (`dev/LESSONS.md:1375`): this is the whole of section 2. The target
was false and the five minutes found it. The corrected target is in
`## WHAT THE RANGE CLAUSE NEEDS NEXT`, beside the original.

**C-22** (`dev/LESSONS.md:2297`): this report was written as a skeleton before
section 3's Agda was attempted, and filled as each measurement landed.

## 7. WHAT THE STATEMENT COST, AND WHAT RESISTED

**What it cost.** 451 lines, 2.67 s median, 295141376 to 358219776 bytes peak
RSS. Two rebuilds that were pure re-typing (`OrdSWO`, `rankFo`'s clauses) cost
about 120 lines and no thought. The refutation chain cost about 143.

**What resisted.** Nothing resisted. That is the surprise and it is worth
recording: I expected the fight to be in the satisfaction plumbing, and it was
not. `extAt`, `appAt-adequate`, `inDomAt-adequate` and `svAt-in` are exactly
the readers this needed, and each one was one `subst`. **The four nested
existentials of `rankFo` were four `PT.∣_∣₁`.** The formula layer of
`L.Coding.Model` is in good shape and the next task should expect to use it,
not to fight it.

**What I had to weaken.** Nothing. I inhabited no weakened type. I added one
hypothesis, `oa`, and it is the predecessor's.

**What I could not close.** `rankFo-adequate`, because it is false. And the
`Q`-independent form of the refutation, which needs a minimal member of `a`
under `Q`, which needs `Q` read as a well-order.

**Two definitional refactors, both declared.** `go`'s body is factored into
`step` (`Probe497.agda:93-96`), with `step-mem` (`Probe497.agda:98-101`) so `boundingOrd`'s own membership is nameable;
`supAt`'s body is split into `supB2`/`supB1`/`supBody`
(`Probe497.agda:241-250`) so `extAt-out` can be applied at a named `φ`.
Neither changes a type and neither changes a value.

## 8. THE DIRECTION AND THE BOUNDARY

`dev/pod/direction.md` says one SRC collection after LJ-1, not after
`[LJ-2.5]`. This task is LJ-1 work. It does not start that collection and it
does not start phase 3. No Boundary clause is in conflict. Nothing was
committed and nothing was pushed. The working tree carries only
`agents/tasks/LJ-1-497/`.

## ARCHIVE USED

- `archive/dev/JOURNAL-archived.md:3635`
  "  (`L.OrdinalLinear.ord-tri`); Bedrock's `boundingOrd` supplies a *common"
  **Read, and USED.** This is the load-bearing archive hit. It records that
  `boundingOrd` was adopted to supply a COMMON stage. That is exactly the
  property that makes it wrong as the rank: common is not least, and the
  padding over the whole carrier is what a common bound permits and an exact
  rank forbids. It is cited in section 6's C-42 sweep.
- `archive/dev/LJ-dispatch-index.md:1`
  "# THE `LJ` DISPATCH INDEX, archived 2026-08-18"
  Head read, then **declined**. Not used. It is an index of dispatch rows. The
  predecessors this task rests on are named in the brief and their reports are
  live under `agents/tasks/`, so the index adds nothing to the divergence.
- `archive/dev/JOURNAL.md:1`
  "# ARCHIVED 2026-08-20"
  Head read, then **declined**. Not used. The per-episode journal is retired
  and its own head says the task directories carry the record.
- `dev/ARCHIVE.md:1`
  "# ARCHIVE.md: the archive registry"
  Read, then **declined as a write target**. No module was retired by this
  task, so no row is owed and none was written. It is cited in section 6 only
  to record that W4 was considered and does not reach a probe.
- `archive/dev/DECISIONS-archived.md:1`
  "# Archived decisions: the D series"
  Head read, then **declined**. Not used. A bare `D<n>` resolves only against
  this archived series and no `D` row bears on whether a rank function takes
  the value `∅`. The clauses that bind this task are `W2` and `W4` from the
  slot file, and the laws are the `D-`/`C-`/`P-` entries of `dev/LESSONS.md`,
  which are live.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md:28`
  "`_build/literature/dev2.txt:1340-1350`. The least witness is the UNIQUE witness"
  **Read, and USED as a cross-check.** The classical sources select the LEAST
  witness under a definable well-order, and leastness is what makes the
  selection definable at all. That is the same discipline the rank needs: a
  rank that is merely A bounding ordinal is not the rank, for the same reason
  a witness that is merely SOME witness is not definable. It supports section
  4's claim that the cure is an exact rank, not a tighter bound.
- `dev/literature/devlin-II5.md:1`
  "# Devlin II.5: the Condensation Lemma and the GCH in L"
  Head read, then **declined**. Not used. II.5 is the Condensation Lemma and
  the GCH derivation. This task is about the value of a rank recursion, which
  II.5 does not reach.
- `dev/literature/digest.md:1`
  "# Digest: the orthodox form of the rud route, pinned from the collected literature"
  Head read, then **declined**. Not used. The rud route is a tower question.
  The divergence measured here is in `boundingOrd`'s index type and is
  route-neutral.
- `dev/literature/terms-2026-08.md:1`
  "# The terminology dossier: fourteen renderings for the owner's ruling"
  **Declined, not read past the head.** It is a translation dossier. No term
  was named or renamed by this task, and clause W5's naming protocol is not
  engaged.
- `dev/literature/geology.md:1`
  "# Geology dossier: set-theoretic geology sources and the five questions"
  **Declined, not read past the head.** Set-theoretic geology is grounds and
  mantles. It does not bear on the value of a well-founded recursion.
