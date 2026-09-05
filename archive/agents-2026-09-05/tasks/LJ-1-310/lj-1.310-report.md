# LJ-1.310 report: every step of the composite's TERM, from `φ₀` to `Graph*`

tier: opus (in-harness-subagent-mode), the switch's DEFAULT row. Recon,
lands nothing. Written incrementally (C-22).

**I RAN NO AGDA.** Every mark below comes from reading source text. Each
negative carries **MEASURED** or **INFERRED**, in those words. Each
positive that no typecheck confirms carries **INFERRED** too.

## 0. LEAD

**THE CHAIN HAS 23 STEPS. TEN ARE UNBUILT.**

Five steps are SUPPLIED by a delivered `src/` name. Eight are
BUILT-AT-A-PROBE. Ten are UNBUILT.

**The ten UNBUILT steps cost about 175 hand-written lines that
`dev/PLAN.md` section 0.0's 470 does not contain, plus about 120 copied
lines, plus ONE step that I cannot price.**

**THE ONE STEP I CANNOT PRICE IS A REFUTATION CANDIDATE, and it is the
most valuable thing in this report.** Step 11 moves the graph from
`levelHoodB`'s existential witness to `q'`'s free value slot. My reading
of the slot arithmetic says that `φ₀`'s two free slots are NOT the value
and the ordinal. They are the ordinal and the bound, and the value is
closed away by `closeN 14`. **If that reading holds, `q'` at the intended
`φ₀` is FALSE, and `[LJ-1.302]`'s `Composite` type is writable but
uninhabitable.** Section 7 gives the derivation at `file:line`, a second
and independent anomaly in the same formula, and a candidate cure of TWO
LINES at `src/L/BoundedSubset.lagda.md:105` and `:111`. **It is INFERRED,
never MEASURED: no Agda ran, and I edited nothing.** Section 9 names the
one probe that settles it.

**The recorded residue is still true (D-10).** `dev/PLAN.md` section 0.0
records "the composite's TERM, which has never been written". I searched
`src/` and `agents/tasks/` for each of the 23 steps. No file holds the
composite, and no file holds ten of its steps. MEASURED, by the greps in
sections 2 and 8.

**The abort criterion fired on its SECOND branch, and it touched the
FOURTH.** Some steps are UNBUILT: that is the expected outcome, and
sections 2 to 5 deliver it. The fourth branch, "the type is wrong", is
raised as a candidate and not as a finding, because settling it needs one
typecheck that this task may not run.

## 1. THE TWO ENDPOINTS, READ

**The right endpoint.** `S.Graph* {2} zero (suc zero)` is
`Seq.LsetGraphAt`, which is `RecShape.GraphAt` opened at `StepAt`
(`agents/tasks/LJ-1-238/GenSequence.agda:92-93` through
`agents/tasks/LJ-1-297/ProbeLJ1297D.agda:92-93`). It unfolds to

```text
GraphAt w b   = ∃̇ (ApproxAt zero (suc b) ∧̇ StepAt (suc w) (suc b) zero)
ApproxAt f a  = domAt f a ∧̇ ∀̇ (∀̇ (appAt (sh2 f) 1 0 ⇒̇ StepAt 0 1 (sh2 f)))
StepAt v b f  = extAt v (∃̇ (∃̇ (∃̇ (StepBody b f))))
StepBody b f  = (var 2 ∈̇ var (sh4 b)) ∧̇ (appAt (sh4 f) 2 1
              ∧̇ (DefAt 0 1 ∧̇ (var 3 ∈̇ var 0)))
```

at `agents/tasks/LJ-1-238/GenSequence.agda:166-167`, `:161-164`, `:72-73`
and `:66-70`. **In `GraphAt w b`, `w` is the value and `b` is the
ordinal.** MEASURED, from `StepAt (suc w) (suc b) zero`: `StepAt`'s first
argument is the extension slot and its second is the domain bound.

**The left endpoint.** `φ₀ = closeN 14 (pins ∧̇ renamed)` at
`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:145-146`, with
`renamed = renameFo ρ base` at `:113-114` and
`base = Cnt.erase LH.levelHoodB refl` at `:102-103`. `LH` is
`L.BoundedSubset`'s `LevelHood {12}` at `:85-99`.

`levelHoodB` is at `src/L/BoundedSubset.lagda.md:108-111`:

```agda
levelHoodB = ∃̇∈ (var (suc (suc (suc zero))))
               (G.graphBndAt ∧̇ (var (suc zero) ≐ var zero))
```

with `G = GraphB {m} ψs ψa zero (suc (suc zero)) (suc (suc (suc zero)))`
at `:81-105`, and `GraphB`'s three slot parameters are `(w b K)`, the
value, the ordinal and the bound
(`src/L/Condensation.lagda.md:2483-2490`).

**So the two endpoints are two codings of one notion, and the composite
is one transport between them.** That is `[LJ-1.302]`'s finding and I
confirm it.

## 2. THE CHAIN TABLE

The steps run in the order a term would run them, from the hypothesis to
the conclusion.

| # | step | supplier | mark |
|---:|---|---|---|
| 1 | read `embed φ₀` free of the constant domain | `src/FOL/Manipulation/Relabelling.lagda.md:188-190`, `embed-⊨`; spent at `agents/tasks/LJ-1-184/ProbeLJ1184A.agda:339-348`, `free` | **SUPPLIED** |
| 2 | open the fourteen existentials of `closeN 14` | none | **UNBUILT** |
| 3 | split `pins ∧̇ renamed` | `src/FOL/Semantics.lagda.md:94`, `γ ⊨ (φ ∧̇ ψ) = (γ ⊨ φ) ⊓ (γ ⊨ ψ)` | **SUPPLIED** |
| 4 | decode `pins` to twelve numeral identities | none | **UNBUILT** |
| 5 | transport across the renaming | `src/FOL/Manipulation/Renaming.lagda.md:127-129`, `⊨-rename` | **SUPPLIED** |
| 6 | the `Agrees ρ` witness at `[LJ-1.241]`'s `ρ` | none; `ρ` at `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-111`, `Agrees` at `src/FOL/Manipulation/Renaming.lagda.md:101-102` | **UNBUILT** |
| 7 | re-enter the constant domain after `erase` | `src/FOL/Count.lagda.md:617-618`, `erase-inv`; `embed` at `src/FOL/Manipulation/Relabelling.lagda.md:117-118` | **SUPPLIED** |
| 8 | `DefBodyB`, `GraphB` and `LevelHood` generic in the class | none | **UNBUILT** |
| 9 | `erase` of the generic matrix equals `[LJ-1.241]`'s `base` | none | **UNBUILT** |
| 10 | open `levelHoodB`'s bounded existential | `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:61-73`, `matrix-decode`'s `go`, class carrier, frozen | **BUILT-AT-A-PROBE** |
| 11 | move the graph to `q'`'s free value slot across the `≐` conjunct | none | **UNBUILT** |
| 12 | `graphBndAt` to `LsetGraphAt`, the assembly | `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:70-88`, `graph-assembly`, class carrier, frozen | **BUILT-AT-A-PROBE** |
| 13 | `approxBndAt` to `ApproxAt` | `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:273-315`, `ApproxAgree.approx-agree` | **BUILT-AT-A-PROBE** |
| 14 | `stepBndAt` to `StepAt` | `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:168-262`, `StepAgree.step-agree` | **BUILT-AT-A-PROBE** |
| 15 | the bounded extension frame to the machine frame | `src/L/Condensation.lagda.md:2511-2529`, `extAtB→extAt` and `extAt→extAtB` | **SUPPLIED** |
| 16 | the ambient leaf-frame wrapper, `leafFwd` and `leafBwd` | none; the hypotheses are at `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:177-183` | **UNBUILT** |
| 17 | the clean 23 `Agree` modules, generic | `agents/tasks/LJ-1-306/GenAgree.agda`, exit 0, 155.1 s | **BUILT-AT-A-PROBE** |
| 18 | `DomainAgree`, generic | `agents/tasks/LJ-1-302/GenDomainAgree.agda:97`, `DomainAgree.back` | **BUILT-AT-A-PROBE** |
| 19 | the other six dirty modules, `LeafAgree` included, generic | none | **UNBUILT** |
| 20 | the ambient tie supply for those six | none; one site built at `agents/tasks/LJ-1-302/ProbeLJ1302B.agda`, 51 lines | **UNBUILT** |
| 21 | `dK`, the definable powerset of a recorded value lands in `K` | none | **UNBUILT** |
| 22 | the reading transport between `⊨ᵐ` and the ambient reading | `agents/tasks/LJ-1-297/ProbeLJ1297C.agda`, `absFull`, 20 lines, exit 0 | **BUILT-AT-A-PROBE** |
| 23 | `Graph*` itself and `LsetGraph-in` | `agents/tasks/LJ-1-238/GenSequence.agda:196-201` and `:224-226` | **BUILT-AT-A-PROBE** |

**Counts: 5 SUPPLIED, 8 BUILT-AT-A-PROBE, 10 UNBUILT.**

**The evidence for each "none" in the supplier column is a search, and
each search is named in section 8.**

## 3. LINE ESTIMATES FOR THE UNBUILT ROWS (DD8)

Each row gets ONE number and names its basis.

| # | step | lines | basis |
|---:|---|---:|---|
| 2 | `closeN-out` | **about 35** | **SURVEY.** An induction on `k` with truncation plumbing. The nearest delivered comparable is `agents/tasks/LJ-1-238/GenSequence.agda:104-135`, `unfold` and `fill`, 32 non-blank lines for THREE nested existentials with truncation. The lemma is generic in `k`, so the cost is the induction and not fourteen copies |
| 4 | the `numAt` decode | **about 55** | **SURVEY.** Two atoms need a decode: `isZeroAt` gives the empty set by extensionality, and `sucAt` gives `k = a ∪ {a}` by extensionality. Then one induction on `k`. No delivered comparable exists, and `src/L/Coding/Bound.lagda.md:139-144` does NOT transfer: it is a membership fact, not a decode (P-l) |
| 6 | the `Agrees ρ` witness | **about 20** | **SURVEY.** A `Fin 16` case split against `ρ` at `ProbeLJ1241A.agda:106-111`, with the `inject+` and `fin-suc` reductions |
| 8 | the generic matrices above the step | **about 10 hand-written, about 120 copied** | **DELIVERED COMPARABLE.** The spans are `src/L/Condensation.lagda.md:2335-2367` (`DefBodyB`, 33), `:2483-2494` (`GraphB`, 12) and `src/L/BoundedSubset.lagda.md:74-146` (`LevelHood`, 73). `[LJ-1.306]` measured the copy rate at 0 changed lines over 4,738, with ONE 45-line scaffold serving 146 blocks. The `Δ₀` certificates drop, as `ProbeLJ1304A.agda:121-122` states for the same direction |
| 9 | the `erase` equation | **about 15** | **SURVEY.** It may fall to ZERO under the cure in section 6.1 |
| 11 | the slot move across `≐` | **UNPRICED** | **NO BASIS EXISTS.** If my section 7 reading holds, this row is not a lemma. It is a re-statement of `φ₀`, and the route re-prices |
| 16 | the ambient leaf-frame wrapper | **about 25** | **PROBE.** `[LJ-1.304]` section 3, INFERRED there from a shape it measured twice at another arity. Already carried in `dev/PLAN.md` section 0.0's 40 |
| 19 | the six dirty modules, generic | **about 135** | **PROBE.** `[LJ-1.298]`'s 180 minus `[LJ-1.306]`'s MEASURED 45 of scaffold. Already carried in the 470 |
| 20 | the six remaining tie supplies | **about 100** | **PROBE.** `[LJ-1.302]` section 4, one site measured at 51 lines. Already carried in the 470 |
| 21 | `dK` | **about 15** | **PROBE.** `[LJ-1.304]` section 4, INFERRED there. Already carried in the 40 |

**WHAT IS NEW, and this is the number `dev/PLAN.md` section 0.0 cannot
state.** Rows 19, 20 and 21 and 16 are already inside the 470 and the 40
that section 0.0 records. Rows 2, 4, 6, 8 and 9 are NOT, and neither is
the re-landing of rows 10 and 12.

| new item | lines |
|---|---:|
| row 2, `closeN-out` | 35 |
| row 4, the `numAt` decode | 55 |
| row 6, the `Agrees ρ` witness | 20 |
| row 8, the generic matrices, hand-written | 10 |
| row 9, the `erase` equation | 15 |
| rows 10 and 12, re-landing `[LJ-1.52]`'s two archived terms | 40 |
| **TOTAL, hand-written, outside the record** | **about 175** |
| plus, copied at a measured zero-change rate | about 120 |
| plus row 11 | UNPRICED |

**The 40 for rows 10 and 12 is `[LJ-1.304]` section 10's own figure**,
which that task flagged as "the last unpriced term on `q'`'s route" and
which the 470 does not carry. I take it and I do not re-derive it.

## 4. WHICH STEP BLOCKS THE MOST

**FIRST, row 11.** It blocks every other row, because it decides whether
the target is true. Rows 2, 4, 6, 8 and 9 all exist to carry a hypothesis
from `φ₀` down to `graphBndAt`. If `φ₀`'s free slots are not the value
and the ordinal, then every one of those rows is work against a false
target. **Cost to settle: ONE small typecheck. Section 9 writes it.**

**SECOND, row 8.** Rows 9, 10, 11 and 12 all state themselves at the
generic matrices, and the matrices do not exist. `[LJ-1.304]` ported
`extAtB`, `leafB`, `bodyB`, `witB`, `stepBndAt` and `approxBndAt` and
stopped below `GraphB`
(`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:123-160`). MEASURED, by reading
the module outline. So the port has a hole exactly where the composite
needs it.

**THIRD, row 4.** The `numAt` decode is what discharges the site facts
that every `Agree` module's telescope demands. `UnaryShape.tagEq` at
`src/L/Condensation.lagda.md:2534-2535` is one of them, and
`ProbeLJ152B.agda:47` bundles the whole family as `SF`. **Nothing else in
the tree can supply those facts at a constant-free `φ₀`**, because the
tags are pinned inside the formula and not by a constant. So row 4 is the
price of `[LJ-1.240]`'s constant-free design, and it was never counted.

**FOURTH, row 2.** It is small, it is generic, and it blocks rows 4 to
12 mechanically.

## 5. THE DD4 READING, PER UNBUILT STEP

**NAME THE AXIS (C-46).** The composite lives on the L-against-ambient
axis, which is the Def tower's internal axis. **That is NOT DD4's own
axis.** DD4's axis is AC against GCH, fixed in code at
`scripts/measure/ledger.py:50`, where `--reuse` reports what the AC and
GCH closures share. **So for each UNBUILT step I say whether writing it
generic serves the AC end at all.**

| # | serves the AC end? | why |
|---:|---|---|
| 2 | **YES.** | `closeN-out` names no tower, no carrier and no class. It is pure FOL syntax over `src/FOL/Semantics.lagda.md:100`. Any proof that closes a formula's head slots spends it, and `src/L/Choice/Name.lagda.md` already does formula surgery of that kind. **Write it first.** INFERRED, that the AC side would use it: I did not find a call site |
| 4 | **YES.** | The numeral decode is tower-free and carrier-generic. `src/L/Choice/Adequate.lagda.md:302-306` carries the AC side's own numeral machinery at the SET level, and a formula-level decode sits directly beside it. **Write it second.** INFERRED, for the same reason |
| 6 | **NO.** | It is the `Agrees` witness for `[LJ-1.241]`'s one concrete `ρ`. GCH-only, and it is 20 lines |
| 8 | **NO.** | `levelHoodB` is the GCH trophy's certificate. The port serves the L-against-ambient axis and the J tower's re-instantiation, which is DD4's FIRST end. It gains nothing on the AC-against-GCH end, and I say so rather than stretch the axis |
| 9 | **NO.** | Same reason as row 8 |
| 11 | **NO.** | It is a correctness question about one formula, not a sharing question |
| 16 | **NO.** | `[LJ-1.304]` section 6 said the same for the stems, and this wrapper is theirs |
| 19 | **NO.** | `[LJ-1.306]` section 5 said the same for the family |
| 20 | **NO.** | `[LJ-1.302]` section 6 said the same for the ties |
| 21 | **UNMEASURED.** | `dK` is a tower closure fact over `𝒟ₒ`. The AC side may need `𝒟ₒ` inside a stage too. I did not search for an AC consumer, so this cell is INFERRED and open |

**THE DD4 READING OF THIS CHAIN.** Two of the ten UNBUILT steps are
tower-free and carrier-free, and both sit at the TOP of the chain, on the
`φ₀` side. **Rows 2 and 4 are the only two the AC end could ever spend,
and together they are 90 of the 175 new lines.** Everything below row 8
is GCH-only by construction, because it is about one tower's certificate
against one tower's graph. **So the DD4 order and the blocking order
disagree**, and the brief's rule says a step that serves both is worth
more. Rows 2 and 4 should be written first on DD4 grounds, and row 11
should be SETTLED first on truth grounds. Those are different actions, so
both can happen.

## 6. TWO OBSERVATIONS THE CHAIN FORCED

### 6.1 The `erase` round trip does not cross carriers, and row 9 exists because of that

`erase-inv` at `src/FOL/Count.lagda.md:617-618` states
`mapFo Empty.rec* (erase φ p) ≡ φ`. **It returns the formula to the
constant domain it left.** `[LJ-1.241]` erased from `CS.S`, the L
carrier's element type (`src/L/BoundedSubset.lagda.md:58`,
`src/L/Condensation.lagda.md` opens the same). The composite needs the
statement at `A.R.SC`, the ambient carrier's. So `erase-inv` alone does
not close the gap, and row 9 is the residue.

**THE CURE, and it is DD4-shaped.** Write the bounded matrices ONCE over
`⊥*`, and `embed` them into each carrier. Then `φ₀` is not an erasure of
an L-carrier formula. It IS the master, and `embed φ₀` at any carrier is
the same object by `embed-⊨`. Row 9 falls to zero and row 8 becomes a
re-siting rather than a port. **INFERRED.** I did not check that every
sub-formula of `levelHoodB` is constant-free at the point of definition,
and `[LJ-1.242]` measured only the WHOLE `base` at `countFo ≡ 0`
(`agents/tasks/LJ-1-242/lj-1.242-report.md:110-115`). That measurement
makes the cure plausible and does not prove it.

### 6.2 `[LJ-1.52]`'s `GraphAgree` was never a term, and its slot reading disagrees with the syntax

`ProbeLJ152A.agda:48-53` states `GraphAgree` as a `Type`, with the
comment "the bounded graph implies the machine graph at the value slot w
(slot 1) and the index slot γ (slot 3)". The `graphBndAt` occurrence
inside `levelHoodB` sits at value slot 0, ordinal slot 2 and bound slot 3
of the same extended environment, by the arithmetic in section 7. **So
the archived hypothesis relates two DIFFERENT slot triples.** It
typechecks, because a `Type` always does. Nobody has inhabited it.
MEASURED, by reading both files whole. This is C-45 exactly: `exit 0` is
not a supply, and a hypothesis is not a term.

## 7. THE REFUTATION CANDIDATE, DERIVED

**CLAIM (INFERRED, never MEASURED): `φ₀`'s two free slots are the graph's
ORDINAL and BOUND. The graph's VALUE is closed away.**

The derivation, step by step, each step at `file:line`.

1. **`∃̇∈ t φ` binds at slot 0 and shifts the environment up by one.**
   `γ ⊨ (∃̇∈ t φ) = ⋁ S (λ x → (x ∈ˢ ⟦ t ⟧ γ) ⊓ ((x ∷ γ) ⊨ φ))`, at
   `src/FOL/Semantics.lagda.md:103`. MEASURED, by reading.
2. **`levelHoodB`'s outer environment is `w ∷ v ∷ γ ∷ K ∷ δ`.**
   `src/L/BoundedSubset.lagda.md:70-73`, the author's own comment.
3. **Its body's environment is therefore `x ∷ w ∷ v ∷ γ ∷ K ∷ δ`**, with
   `x` the bounded witness. From steps 1 and 2.
4. **`G.graphBndAt`'s three slots are 0, 2 and 3 of the body's
   environment.** `src/L/BoundedSubset.lagda.md:105`,
   `zero (suc (suc zero)) (suc (suc (suc zero)))`. So they are `x`, `v`
   and `γ`.
5. **`GraphB`'s parameters are `(w b K)`, the value, the ordinal and the
   bound.** `src/L/Condensation.lagda.md:2483-2490`. The identification
   is MEASURED against `GenSequence.agda:166-167`: `GraphB`'s inner
   applications `ApproxB ... zero (suc b) (suc K)` and
   `StepB ... (suc w) (suc b) zero (suc K)` match `GraphAt`'s
   `ApproxAt zero (suc b)` and `Step (suc w) (suc b) zero` slot for slot.
6. **So `levelHoodB` reads: exists `x` in `K`, the graph holds at value
   `x`, ordinal `v` and bound `γ`, and `w ≐ x`.** The `≐` conjunct is
   `var (suc zero) ≐ var zero` at `src/L/BoundedSubset.lagda.md:111`,
   which is `w ≐ x` in the body's environment. **So the VALUE is `w`,
   slot 0, and the ORDINAL is `v`, slot 1, and the BOUND is `γ`, slot
   2.**
7. **`ρ` maps `base`'s slot 0 to 0, slot 1 to 14, slot 2 to 15 and slot 3
   to 1.** `agents/tasks/LJ-1-241/ProbeLJ1241A.agda:106-111`. `renameFo`
   places `base`'s slot `i` at slot `ρ i`, by `Agrees` at
   `src/FOL/Manipulation/Renaming.lagda.md:101-102`.
8. **`closeN 14` closes the head fourteen slots of `renamed`**, which are
   slots 0 to 13. `ProbeLJ1241A.agda:140-142` and `:145-146`. Those slots
   hold `base`'s `w` at 0, `base`'s `K` at 1 and the twelve tags at 2 to
   13.
9. **So `φ₀`'s free slot 0 is `base`'s slot 1 and `φ₀`'s free slot 1 is
   `base`'s slot 2.** From steps 7 and 8. By step 6 those are the
   ORDINAL and the BOUND.
10. **`q'` needs `Graph* {2} zero (suc zero)`, which is the graph at
    value slot 0 and ordinal slot 1.** `ProbeLJ1302A.agda:75` and
    `GenSequence.agda:228-229`. `AmbientStep.go` confirms the reading:
    it concludes `fst (lookup zero γ) ≡ Lset (fst (lookup (suc zero) γ))`
    at `agents/tasks/LJ-1-244/ProbeLJ1244A.agda:111-114`.

**The consequence, if the reading holds.** `φ₀(a, b)` says "the level at
ordinal `a` exists inside bound `b`". `q'` asks it to give "`a` is the
level at ordinal `b`". Take `a` the empty set and `b` a limit above it:
the hypothesis holds and the conclusion fails. **So `q'` is FALSE at the
intended `φ₀`, and `Composite` is uninhabitable.**

**WHY NOBODY CAUGHT IT.** Three reasons, each MEASURED.

- **`[LJ-1.241]`'s verification measured the free-variable SET, not the
  slot ROLES.** `agents/tasks/LJ-1-241/ProbeLJ1241B.agda:120-133` holds
  `freeCheck` and `freeCheck'`, both `refl`. They record which slots
  occur and the tag order. They say nothing about which slot is the
  value. `[LJ-1.241]`'s report calls this "verified the pinning", and the
  pinning it verified is the TAG pinning.
- **`[LJ-1.52]` routed around the `≐` conjunct.** `matrix-decode` at
  `ProbeLJ152A.agda:61-73` takes `fst hx`, the `graphBndAt` half, and
  drops the `≐` half. It then applies `ride-only` at the OUTER slot. So
  the slot mismatch never had to close.
- **`src/L/BoundedSubset.lagda.md:70-72`'s own comment names the slots
  one position away from the syntax.** It says "v is the value, γ the
  ordinal index, K the bound". The syntax makes `w` the value, `v` the
  ordinal and `γ` the bound. **A comment is not a checker**, and every
  later reader took the comment.

**A SECOND ANOMALY, INDEPENDENT OF THE FIRST, AND IT POINTS AT ONE
OFF-BY-ONE.** `levelHoodB` uses TWO different bounds. Its own existential
ranges over slot 3, the intended `K`
(`src/L/BoundedSubset.lagda.md:110`). The graph machinery inside it is
bounded by slot 2, which is `γ`, because `GraphB`'s third argument at
`:105` is `suc (suc (suc zero))` and the body's environment carries the
extra binder. **A bounded matrix that bounds its witness by `K` and its
machinery by the ordinal index is not a design. It is an off-by-one.**
Under the author's comment at `:70-73` every structural argument should
sit ONE slot higher: the value at slot 2, the ordinal at slot 3 and the
bound at slot 4.

**So the candidate cure is TWO LINES in a delivered file.** At
`src/L/BoundedSubset.lagda.md:105`, read `zero (suc (suc (suc zero)))
(suc (suc (suc (suc zero))))` in place of `zero (suc (suc zero))
(suc (suc (suc zero)))`. At `:111`, read `var (suc (suc zero)) ≐ var
zero` in place of `var (suc zero) ≐ var zero`. **I did NOT make that
edit**: the file is outside my write scope, DD23 governs it, and no
typecheck stands behind the reading. **INFERRED, both the anomaly's
reading and the cure.**

**MY CONFIDENCE, stated honestly.** The derivation has one weak joint,
and it is step 5. If `GraphB`'s parameters are not `(value, ordinal,
bound)`, the whole thing collapses. I checked step 5 against
`GenSequence.agda:166-167` slot for slot and it matches. **I still call
the claim INFERRED and not MEASURED, because no Agda ran.** C-36 applies:
a failed reading is not a proof of impossibility, and the honest action
is the probe in section 9.

## 8. THE SEARCHES BEHIND EACH "none"

Every UNBUILT mark rests on a search. Each search is named with its
filter, so a reader can re-run it (`load-bearing-claim`).

| # | search | result |
|---:|---|---|
| 2 | `grep -rn "closeN" src/ agents/` | Occurs ONLY in `agents/tasks/`, in `[LJ-1.241]`'s probe and in seven reports. Never in `src/`. No `closeN-out` and no `closeN-in` anywhere. **MEASURED** |
| 4 | `grep -rn "isZeroAt\|sucAt" src/` and `grep -rn "numAt" src/` | `sucAtL` at `src/L/Absorption.lagda.md:33` is a DIFFERENT delivery, the successor reading over the L coding. `numAt` at `src/L/Choice/Adequate.lagda.md:302-306` is a DIFFERENT object, a function `ℕ → S`. `[LJ-1.241]`'s three formulas have no adequacy lemma at their own probe: the file ends at `:150`. **MEASURED** |
| 6 | reading `ProbeLJ1241A.agda` whole | The file defines `ρ` and never states `Agrees ρ`. **MEASURED** |
| 8 | `grep -rn "graphBndAt" agents/` and `grep -rn "levelHoodB" agents/` | The only hits outside reports are two whole-chapter CLASS-CARRIER control copies, `agents/tasks/LJ-1-275/CondControlToday.lagda.md:2489-2490` and `agents/tasks/archive/tmp-cond-dd3aa13.lagda.md:2486-2487`, and the archived class-carrier skeletons `agents/tasks/archive/LJ-1-7/ProbeLJ17Skel.agda:99-105` and `ProbeLJ17.agda:119-120`. **No generic form exists.** **MEASURED** |
| 9 | `grep -rn "erase-inv" src/ agents/` | Only its own definition at `src/FOL/Count.lagda.md:617-628`. **Zero consumers.** **MEASURED** |
| 11 | reading `ProbeLJ152A.agda` and `ProbeLJ152B.agda` whole | Neither closes the `≐` conjunct. **MEASURED** |
| 16 | reading `ProbeLJ1304A.agda:168-192` | `leafFwd` and `leafBwd` are module PARAMETERS. C-45: a parameter is an assumption. **MEASURED** |
| 19 | `[LJ-1.306]` section 1 and its own report | The port covers the clean 23 and 123 helpers. "The dirty seven's spans, `DomainAgree` through `LeafAgree`, were never touched", `lj-1.306-report.md:89-90`. `[LJ-1.302]` ported `DomainAgree` alone. **MEASURED**, by reading two reports |
| 20 | `[LJ-1.302]` section 4 | One site built, six inferred. **MEASURED** |
| 21 | `[LJ-1.304]` section 4 | That task searched `src/L/Hierarchy.lagda.md` and `src/L/Constructible.lagda.md` and found nothing. I did not re-run the search. **TAKEN from the record** |

## 9. THE STEPS THAT NEED A TYPECHECK TO SETTLE

**I name three, in the order the orchestrator should fund them.**

**FIRST, and it is small: step 11, the slot question of section 7.** One
file, no new mathematics, and it settles whether `q'` is worth funding at
all.

The cheapest decisive form is a slot census in `[LJ-1.241]`'s own style.
`ProbeLJ1241B.agda` already computes `freeFo` over `base`. Extend it to
compute the free-variable list of `G.graphBndAt` ALONE at the same
instantiation, and compare the three slots it uses against 0, 2 and 3 of
the body environment. Two `refl`s settle it. **INFERRED at about 25
lines and under 10 seconds**, on `ProbeLJ1241B.agda`'s measured shape.

A second form is stronger and costs more: state
`Composite` at a CONCRETE environment where the ordinal and the value
differ, and try to inhabit it. **A failure there is C-36 evidence and not
a refutation**, so the census is the better first buy.

**A THIRD form settles the anomaly and the cure at once, and it is the
one I would buy.** Copy `LevelHood` into a probe file twice, once
verbatim and once with section 7's two-line cure. Then state, at a
concrete environment, that the cured form's graph slots are the value and
the ordinal. **If the verbatim copy refuses the same statement, the
off-by-one is MEASURED and the cure is priced at two lines.** INFERRED at
about 60 lines and under 30 seconds, on `ProbeLJ1302B.agda`'s measured
shape.

**SECOND: step 8 and step 9 together.** Whether the generic `GraphB` and
`LevelHood` port at `[LJ-1.306]`'s zero-change rate is a copy question,
and `[LJ-1.306]` measured that rate at 146 blocks. **But `LevelHood`
lives in `src/L/BoundedSubset.lagda.md`, which `[LJ-1.306]` did NOT
port**, and that chapter's `LevelHood` reaches `CS.S` directly at
`:108`. So the port may need a class parameter where the chapter has a
carrier. INFERRED, that it is a copy; only a typecheck settles it.

**THIRD: step 2 and step 4.** Both are ordinary Agda work and neither
has a hidden wall that I can see. They do not need a probe. They need a
build.

**WHAT I DID NOT NEED AGDA FOR.** Every other row in section 2 rests on
reading one file, and the file is named.

## 10. PREMISES, VERIFIED OR REFUTED (C-44)

| the brief's premise | verdict |
|---|---|
| `[LJ-1.302]`'s `Fed.amb-from-composite = AS.amb` typechecks, and a composite term is sufficient for `amb` | **VERIFIED, as a reading.** `agents/tasks/LJ-1-302/ProbeLJ1302A.agda:81-92` applies `AmbientStep` at probe D's six readings and at `comp : Composite`. The Def-step trio stays a module parameter (`:59-68`), so the sufficiency is modulo that trio. **A composite term is the only thing missing FROM `AmbientStep`. It is not the only thing missing from the ROUTE**: `Composite` itself needs the 23 steps above. INFERRED, that the probe still exits 0 today; I did not re-run it |
| `[LJ-1.304]` BUILT `StepAgree` and `ApproxAgree`, and neither module exists in `src/` | **VERIFIED.** The terms are at `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:254-262` and `:313-315`. Neither name occurs in `src/` outside one comment; `[LJ-1.304]` section 0 cites that comment at `src/L/Condensation.lagda.md:5476`. **They are BUILT-AT-A-PROBE, and they are built MODULO PARAMETERS**: five for `StepAgree` at `:177-192`, seven for `ApproxAgree` at `:275-297`. C-45 binds here |
| `[LJ-1.306]` ported the clean 23 at zero changed lines, and it is UNSETTLED under `[LJ-1.308]` | **TAKEN, and marked INFERRED throughout.** Rows 17 and 19 rest on it. If `[LJ-1.308]` refutes the zero rate, row 19's 135 moves and row 17's mark moves with it |
| `[LJ-1.298]` measured the port's rate at ONE site (P-l) | **VERIFIED and superseded.** `[LJ-1.306]` re-measured at 23 sites plus 123 helpers. The one-site caveat is retired for the CLEAN modules and stands for the dirty seven, where the sites are `DomainAgree` alone |
| the recorded residue "the composite is unwritten" is still true (D-10) | **VERIFIED.** MEASURED, by the ten searches in section 8 |

## 11. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the composite's chain has a supplier at every step | **MEASURED FALSE.** Ten steps have none, section 8 |
| `closeN` has an unpacking lemma anywhere | **MEASURED FALSE.** Section 8, row 2 |
| `[LJ-1.241]`'s `numAt` has an adequacy lemma anywhere | **MEASURED FALSE.** Section 8, row 4 |
| a generic `GraphB` or `LevelHood` exists | **MEASURED FALSE.** Section 8, row 8 |
| `erase-inv` has any consumer | **MEASURED FALSE.** Section 8, row 9 |
| `[LJ-1.52]`'s `GraphAgree` is a term | **MEASURED FALSE.** It is a `Type` at `ProbeLJ152A.agda:48-53` |
| `[LJ-1.52]`'s `StepAgree` and `ApproxAgree` are terms | **MEASURED FALSE.** Hypotheses at `ProbeLJ152B.agda:53-58` and `:64-68`. `[LJ-1.304]` built the two at ambient, and that is a DIFFERENT statement at a different carrier |
| `φ₀`'s free slots are the value and the ordinal | **INFERRED FALSE.** Section 7. **No Agda ran.** This is the report's chief claim and its weakest joint is step 5 |
| `q'` is TRUE | **INFERRED FALSE**, by the same reading. Neither `[LJ-1.297]`, `[LJ-1.298]`, `[LJ-1.302]`, `[LJ-1.304]` nor `[LJ-1.306]` settled it, and neither do I |
| `[LJ-1.241]`'s `ProbeLJ1241B` verified the slot roles | **MEASURED FALSE.** It verified the free-variable set and the tag order, `:120-133` |
| the archived `[LJ-1.52]` files still typecheck today | **UNKNOWN.** Frozen, not re-run, as `[LJ-1.302]` and `[LJ-1.304]` left it |
| `[LJ-1.306]`'s zero rate holds | **INFERRED.** Under adversarial review as `[LJ-1.308]` |
| rows 2 and 4 have an AC-side consumer today | **INFERRED.** I named a plausible site and did not grep for a call |
| the cure in section 6.1 works | **INFERRED.** `[LJ-1.242]` measured `countFo base ≡ 0`, not the sub-formulas |
| the new 175 is complete | **INFERRED.** It is the sum of nine rows, and row 11 is unpriced. A refutation at row 11 moves all of it |
| `levelHoodB` bounds its witness and its machinery by the same slot | **INFERRED FALSE.** Two bounds, section 7. This is independent evidence for the off-by-one, and no Agda ran |
| the two-line cure in section 7 is correct | **INFERRED.** Nothing checked it, and I did not edit the file |

## 12. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-116`.

**Does Devlin need a composite of this shape? NO, and the reason is
sharper than "he writes one coding".** His 2.7 gives one Σ₀ formula
`Φ(z, v, γ)` with clause (a) `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`, at
`dev/literature/devlin-II5.md:95-96`. **His existential closes ONE slot,
`z`, and it leaves `v` and `γ` free in exactly the roles the conclusion
uses.** Bedrock's `closeN 14` closes fourteen, and section 7 says the
value is among them. **So the divergence from Devlin is not the second
coding alone. It is the SHAPE OF THE CLOSURE**, and that is the port's
choice and not the mathematics.

**What this changes about the word "unbuilt".** `[LJ-1.302]` and
`[LJ-1.304]` both concluded that the composite is the PORT's price and
not Devlin's mathematics, and both are right about rows 12 to 21. **Rows
2, 4, 6, 8, 9 and 11 are a different animal: they are the price of
`[LJ-1.240]`'s constant-free `φ₀`**, which exists so that `embed` can
carry the formula between carriers. Devlin pays none of it, because he
never moves a formula between constant domains. So the top of the chain
is a cost the CHOICE OF `φ₀` created, and section 6.1's cure attacks
exactly that cost.

**WHY NOT the other rows.** C1 is the level-hood formula, which is `q'`'s
subject matter and not a method for it. C3 is Σ₀ absoluteness, delivered,
and spent by `absFull` at row 22. C2's coding analogue is the `Agree`
family. C4, the elementarity transfer, is downstream of `amb`. C5, C6, D
and G are bookkeeping, unions and the well-order. A, B, E and F are
extensionality, collapse, counting and cardinals. **None prices a slot
alignment between two codings**, which is what section 7 is about.

## 13. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-302/lj-1.302-report.md`, read WHOLE, FIRST, as the
  brief orders. **Line read:** `:9`, "The composite's TYPE is `q'`
  itself, it is WRITABLE, and it FEEDS." TOOK the task, the
  decomposition at `:35`, and the leaf-stem citation. **CORRECTED
  nothing in it**, and EXTENDED its section 5 route with the six rows
  above `graphBndAt` that it did not name.
- `agents/tasks/LJ-1-302/ProbeLJ1302A.agda`, read WHOLE, FIRST, per
  SCOPE. **Line read:** `:72-75`, the `Composite` type. TOOK both
  endpoints, which sections 1 and 7 unfold.
- `agents/tasks/LJ-1-304/lj-1.304-report.md`, read WHOLE. **Line read:**
  section 10, "The archived assembly's re-landing ... about 40 lines,
  INFERRED. It is the last unpriced term on `q'`'s route." TOOK the 40
  for rows 10 and 12, and the five obligations of `StepAgree`.
- `agents/tasks/LJ-1-297/lj-1.297-report.md`, read `:1-60`. **Line
  read:** section 0, "`ProbeLJ1297C.agda`, exit 0, 1.56 s ... 20 lines."
  TOOK the nearest comparable for an ambient supply, which row 22 uses.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`, read WHOLE. **Line
  read:** `:48-53`, `GraphAgree` as a `Type`. TOOK the archived slot
  reading, which section 6.2 measures against the syntax.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`, read WHOLE. **Line
  read:** `:70-88`, `graph-assembly`, proved from two hypotheses. TOOK
  row 12's supplier.
- `agents/tasks/archive/LJ-1-7/ProbeLJ17Skel.agda`, grepped. **Line
  read:** `:99-100`, `levelHoodB` at the CLASS carrier. TOOK the
  confirmation that every archived `levelHoodB` is class-carrier, so row
  8 stands.
- `archive/dev/TASKS-archived.md`, read `:58-75` and grepped. **Line
  read:** the `L3.32-T33` row, "Condensation crossing | DELIVERED".
  **TOOK SHAPE ONLY.** The retired route delivered a crossing over the
  stems. **WHAT WOULD NOT TRANSFER:** that route's composite ran at the
  CLASS carrier with `q` as a syntactic identity, and `[LJ-1.293]`
  refuted `q` by machine (`agents/tasks/LJ-1-293/lj-1.293-report.md:9`).
  So the retired crossing's TERM cannot be re-used, and no figure of its
  transfers. Only the fact that a crossing was once assembled transfers,
  and that fact prices nothing.

## 14. WHAT I DID NOT SETTLE

- **Step 11, and it is the report's whole weight.** Section 9 names the
  probe. Until it runs, `q'`'s truth is INFERRED FALSE by ONE reading and
  nothing more.
- **Whether the section 6.1 cure removes rows 8 and 9.** INFERRED.
- **Whether rows 2 and 4 have a real AC-side consumer.** I named a site
  and did not grep for a call.
- **Whether `dK` serves the AC end.** Not searched.
- **Whether any archived `[LJ-1.52]` file typechecks today.** Frozen, not
  re-run.
- **The seconds of any UNBUILT row.** No Agda ran, so I give no seconds
  and I quote nobody else's as mine.

## 15. PROHIBITIONS, ANSWERED

**I ran NO Agda.** No `agda` process started from this task, so C-12's
two slots stayed with `[LJ-1.305]` and `[LJ-1.308]`.

I wrote only inside `agents/tasks/LJ-1-310/`: this report. `src/` holds
no probe of mine. `src/L/Condensation.lagda.md`,
`src/L/BoundedSubset.lagda.md`, `src/FOL/`, `dev/PLAN.md` and
`dev/literature/devlin-II5.md` were read, never opened for writing.
`agents/tasks/LJ-1-305/`, `agents/tasks/LJ-1-308/` and every other task
directory were not touched. `dev/`, `AGENTS.md` and
`src/Everything.lagda.md` were not touched. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py --check` was run on this
report. No em dash in any language. `_build/` gained nothing.
