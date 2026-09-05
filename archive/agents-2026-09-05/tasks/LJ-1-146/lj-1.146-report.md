# LJ-1.146: `levelIn` and `cover`, the root of the unconsumed chain

tier: opus (version `override`). **RECON AND PRICE. No master was changed. No
probe was written. No Agda ran. No commit, no push.** Every negative is marked
**MEASURED** or **INFERRED**.

## 0. LEAD: THE TROPHY NEEDS THEM, AND THE UNCONSUMED CHAIN IS NOT EVIDENCE AGAINST THEM

**Answer to the funding question: YES. `L ⊨ GCH` needs `levelIn` and `cover`.
The brief's alternative does not fire.**

The two hypotheses gate `theorem : ⟨ x ∈ˢ Lset κ ⟩`
(`src/L/BoundedSubset.lagda.md:1621-1622`). That term is Devlin 5.5, the
bounded subset lemma. Devlin proves GCH from 5.5 in three lines and one
application (`dev/literature/devlin-II5.md:159-166`). **Nothing else in the
tree proves 5.5. MEASURED** by grep over `src/`: only
`src/Everything.lagda.md:374` names `L.BoundedSubset`.

**The brief's hypothesis was that the chain above them buys nothing. It is
false, and the reason is the direction of the chain.** `[LJ-1.144]` measured
that `LeafAgree` and `LevelHood` have no consumer. Those two are on the
**SUPPLY** side of `levelIn`, not on the consumer side. **A supply chain with
no consumer is the signature of an unbuilt assembly, not of dead code.** The
assembly that would consume them is the level hood transfer, and nobody has
written it.

**And the unconsumed region is larger than `[LJ-1.144]` reported. MEASURED
TODAY.** `theorem` itself has no consumer either. `Devlin55` and
`BoundedSubsetAt` appear in no master, only in probes
(`agents/tasks/LJ-1-119/ProbeLJ1119A.agda:45-47`). **So C-35 fires over the
whole wing, from `TwelveAgree` at the top down to `theorem` at the bottom, and
the cause is one thing: the trophy at the bottom is not written.** `[LJ-1.8]`
is still `planned` (`dev/PLAN.md:630`). **Retiring any link of that chain
would retire the wing, not prune it.**

**The price, one best-effort figure each (DD8).**

| term | figure | basis |
|---|---|---|
| in-fence lines to supply both | **about 1.0 thousand**, band 0.6k to 1.5k | `[LJ-1.123]`'s 0.6k certificate remainder, **plus** the instantiation the 0.6k does not contain. Section 3 |
| cold seconds added | **about 30 s**, band 15 to 60 | the projected lines against the two measured rates at `dev/ledger.toml:2681`. **INFERRED. I measured no seconds.** Section 3.4 |
| widest unmeasured term | **the 28 closure facts at a real `K`** (`[LJ-1.113]`) | section 4. It is the C-38 instantiation term, and no line figure exists for it |

**The C-38 warning the brief asked for, applied to my own price.** The 0.6k
figure of `[LJ-1.123]` prices the certificate INTERFACE and its transfer. It
does not price the INSTANTIATION. `[LJ-1.129]` said so first
(`agents/tasks/LJ-1-129/lj-1.129-report.md:264-274`). **I did not reuse the
0.6k as a total. I added the instantiation as a separate term and I say
plainly that its band is the softest number in this report.**

**Wall or deferral: a WALL, and the record names it TWICE at the same term.**
`[LJ-1.51]` and `[LJ-1.121]` both aimed at the supply, by different methods,
and both stopped at the collapse-of-the-level. Four other dispatches deferred
around it. **The wall has since fallen a long way, and section 2.4 measures
how far.**

**DD4, in one line: they serve BOTH towers in SHAPE and ONE tower in
INSTANCE, and the per-tower half is the LARGER half of the bill.** The
transfer that produces them is either-tower. The certificate they transfer is
per-tower. So a supply buys about one third of itself twice. Section 6.

**MY RECOMMENDATION, and it is a recommendation rather than a verdict.**
**Fund the supply, and gate it on the instantiation probe of section 4 rather
than on the certificate side.** The certificate side has a measured band and a
green probe inside it. The instantiation side has neither, it is the larger
soft term, and two dispatches have now named it without running it. **Do not
retire any link of this chain: section 0 shows that retiring one retires the
wing.**

## 1. WHAT THEY ARE

### 1.1 The two statements, and where they bind

They bind at two sites. `HullStage.Condense`'s telescope
(`src/L/BoundedSubset.lagda.md:916-919`):

```agda
  module Condense
    (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩)
    (cover : (y : S) → ⟨ y ∈ˢ M ⟩
           → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁)
```

`Devlin55.BoundedSubsetAt.Co` restates them at `:1408-1411` and passes them to
`Condense` at `:1414`.

`M` is the hull carrier. `C.π` is its Mostowski collapse. `C.πX` is the
collapse image.

- **`levelIn` says the collapse image is closed under the level
  construction.** For an ordinal `δ` in `πX`, the level `Lset δ` is again in
  `πX`.
- **`cover` says every collapsed hull member lands in a level of the
  collapse.** For a hull member `y`, some ordinal `γ` in `πX` has
  `π y ∈ Lset γ`.

### 1.2 What a supplier must produce, and it is three terms

`[LJ-1.121]` reduced the supply to three named terms and machine checked the
reduction (`agents/tasks/LJ-1-121/lj-1.121-report.md:112-145`,
`agents/tasks/LJ-1-121/ProbeLJ1121A.agda:102-110` and `:116-118`, GREEN):

| term | type | state |
|---|---|---|
| `hullLevel` | `(δ : S) → IsOrd δ → ⟨ δ ∈ˢ πX ⟩ → ⟨ Lset δ ∈ˢ M ⟩` | not delivered |
| `piFixesLevel` | `(δ : S) → IsOrd δ → ⟨ δ ∈ˢ πX ⟩ → π (Lset δ) ≡ Lset δ` | not delivered |
| `CoverTransfer` | `cover`'s own type | not delivered |

`levelIn` follows from the first two by one `subst`
(`agents/tasks/LJ-1-121/ProbeLJ1121A.agda:108-110`). **The three are one
content: the level hood statement moves between the hull and the collapse, and
the collapse fixes the level.**

### 1.3 The four consumer sites, re-measured today. MEASURED

| use | line | which |
|---|---|---|
| `Condense.β-succ` | `:967` | `cover` |
| `Condense.πX⊆Lβ` | `:1002` | `cover` |
| `Condense.Lβ⊆πX` | `:1020` | `levelIn` |
| `Co.x∈Lκ` | `:1606` | `cover` |

**One observation nobody has recorded, and I mark it MEASURED and small.**
`levelIn` has exactly ONE use site, `:1020`, and that site always applies it
at a SUCCESSOR ordinal, `sucV δ`. So the consumer needs the closure at
successors only. **I do NOT recommend narrowing the statement to successors.**
The certificate proves the level hood uniformly in `δ`, so a successor only
statement would cost the same to supply and would buy nothing. This is
**INFERRED**, from the uniform shape of the certificate at
`src/L/BoundedSubset.lagda.md:74-146`. I record the fact because D-30 asks for
it and because a later reader may find a use for it.

### 1.4 What hangs on them. MEASURED

**294 in-fence lines of delivered proof are conditional on the two.** Counted
with `awk` over the ` ```agda ` fences: `Condense` (`:916-1035`) is 106 lines,
and `Co` (`:1408-1622`) is 188 lines. The master holds 1,409 in-fence lines in
total, which agrees with `dev/ledger.toml:3039`.

## 2. WHY THEY WERE NEVER SUPPLIED: A WALL, NAMED TWICE, AT THE SAME TERM

**The brief asks for the class, because a wall and a deferral have different
cures. The record holds both, and the wall is the load-bearing half.**

### 2.1 The entry was a deferral, and so were the passers-by

`levelIn` and `cover` entered as hypotheses at `[LJ-1.7]`
(`dev/PLAN.md:499`): "888 lines at 0.0111, under the bar. But levelIn and
cover are HYPOTHESES: the semantic transfer is assumed."

Four later dispatches had other targets, cleared them, and recorded the two as
still open: `[LJ-1.57]`, `[LJ-1.59]`, `[LJ-1.60]`, `[LJ-1.61]`
(`dev/PLAN.md:512`, `:516`, `:518`, `:521`, and the reports at
`agents/tasks/archive/LJ-1-57/lj-1.57-report.md:130-151` and
`agents/tasks/archive/LJ-1-61/lj-1.61-report.md:153`). **Those four were
DEFERRALS.** `agents/tasks/archive/LJ-1-61/LJ-1.61.md:73` records that the two
had "survived nine dispatches" by that date.

### 2.2 But TWO dispatches took them as targets, and BOTH returned a wall

**This is the correction I make to the brief's framing, and it changes the
class.** `[LJ-1.121]` was not the first dispatch to aim at the supply.

**`[LJ-1.51]` aimed at them and returned a wall.** Its section title is
literal: "`levelIn`: the wall, and the term I cannot write"
(`agents/tasks/archive/LJ-1-51/lj-1.51-report.md:135`). It wrote the term it
could not write as a comment, and it named the deepest step:
`π (Lset m') ≡ Lset (π m')`, the collapse commuting with the level
construction (`:151-152`). Its verdict at `:166-168`: **"the
collapse-of-the-level is the wall, with no measured price"**, and a contingent
structural total of **200 to 400 lines for `levelIn` alone** (`:167`).

**`[LJ-1.121]` aimed at them again, later, and returned the SAME term.** Its
machine-checked reduction stops at `hullLevel` and `piFixesLevel`
(`agents/tasks/LJ-1-121/lj-1.121-report.md:112-137`,
`agents/tasks/LJ-1-121/ProbeLJ1121A.agda:102-110`, GREEN). **`piFixesLevel` IS
`[LJ-1.51]`'s collapse-of-the-level.** Its verdict at `:7-18`: "Neither is
refutable. Neither is supplied."

**Two independent dispatches, different agents, different methods, one term.**
`[LJ-1.51]` reached it by writing the proof structure in prose. `[LJ-1.121]`
reached it by writing a reduction that a typechecker accepted. **MEASURED
agreement, and it is the strongest evidence in this report that the wall is
real and correctly located.**

### 2.3 So the class, and what the class implies

**WALL, not deferral.** The named cause is not a local missing lemma. It is one
missing chapter, the level hood certificate, which `[LJ-1.12]` priced at 2.8k
to 3.3k lines and nobody built
(`agents/tasks/LJ-1-121/lj-1.121-report.md:147-151`).

**A local defect needs a lemma. A missing chapter needs funding.** That is why
seven dispatches passed the two by and none supplied them: **no dispatch was
ever funded to build the chapter.**

### 2.4 And the wall has already fallen a long way

**`[LJ-1.123]` re-priced the chapter from 2.8k to 3.3k down to 0.6k**
(`agents/tasks/LJ-1-123/lj-1.123-report.md:26-45`). The reason is not a
cleverer plan. **The reason is that the LJ-1 series built the substrate under
the price while the price stood still.** `src/L/Condensation.lagda.md` and
`src/L/BoundedSubset.lagda.md` did not exist at the `[LJ-1.12]` commit
(`agents/tasks/LJ-1-123/lj-1.123-report.md:83-88`, MEASURED there by
`git diff --stat`).

**Then `[LJ-1.124]` measured the widest band of that 0.6k and returned GO**
(`agents/tasks/LJ-1-124/lj-1.124-report.md:1-56`): the bounded level graph
decode closes both ways in **147 in-fence lines** at **37.4 cold seconds**.

**So the wall of `[LJ-1.121]` is not the wall of today.** Today the certificate
side is one measured decode plus three unbuilt assemblies over delivered
parts.

### 2.5 The honest counterweight: what fell was not the whole price

`[LJ-1.129]` reviewed the 0.6k and marked its centre optimistic, for a stated
reason (`agents/tasks/LJ-1-129/lj-1.129-report.md:255-274`): **the 0.6k does
not carry the 28 closure facts that a real instantiation needs.** Section 3.3
carries that term separately, which is what `[LJ-1.129]` asked for and what no
figure since has done.

## 3. THE PRICE, AND EACH TERM NAMES ITS BASIS (DD8)

**I ran no Agda. Every second below is another task's measurement, cited at
`file:line`. I say so once here and I do not repeat it per row.** The reason
is section 8.

### 3.1 The certificate side: about 0.6k lines

`[LJ-1.123]`'s four bands (`agents/tasks/LJ-1-123/lj-1.123-report.md:35-43`):

| piece | band | class today |
|---|---:|---|
| the bounded level graph decode, both ways | 0.10-0.25k | **MEASURED at 0.147k** by `[LJ-1.124]` |
| the certificate truth at the hull ordinals | 0.10-0.25k | INFERRED |
| the three transfer lemmas at the hull | 0.10-0.25k | INFERRED |
| the assembly into `Co` | 0.03-0.08k | INFERRED |

**Centre about 0.6k. Basis: a delivered component map read at `file:line`, with
one band now measured by probe.** One of four bands moved from INFERRED to
MEASURED since the figure was set, and it landed inside its band.

**One independent corroboration, and it agrees.** `[LJ-1.51]` priced `levelIn`
ALONE at **200 to 400 lines, contingent on the collapse-of-the-level**
(`agents/tasks/archive/LJ-1-51/lj-1.51-report.md:166-168`). That figure is
older and it was set by a different agent on a different tree. **It sits inside
my certificate-side band and it was reached without `[LJ-1.123]`'s component
map.** Two independent projections that agree are not a measurement, but they
are better than one projection alone.

### 3.2 The `TwelveAgree` bridge: 38 lines

**MEASURED** by `[LJ-1.144]`
(`agents/tasks/LJ-1-144/lj-1.144-report.md:16-22`): about 38 in-fence lines
and about 3.5 s, at the consumer's exact types, with no new master. **This is
not part of `[LJ-1.123]`'s 0.6k.** It is a separate term and it is the
cheapest link in the whole chain.

### 3.3 The instantiation: about 0.35k lines, and this is the soft term

**C-38 as extended, applied to my own price.** The certificate side supplies an
INTERFACE. `LeafAgree` (`src/L/Condensation.lagda.md:6911`) still takes
`twelve-out` and `twelve-back` as hypotheses. Supplying those needs
`TwelveAgree.AbstractFrame` instantiated at a real `K`. `[LJ-1.112]` measured
that instantiation at zero unsolved metas. `[LJ-1.113]` then classed its 29
consumer side facts as **PROVABLE 1, NEW CONTENT 28**
(`agents/tasks/LJ-1-113/lj-1.113-report.md:6-18`).

**The 28 are still open today. MEASURED against the record.** `someEnv` closed
at `[LJ-1.120]` and `[LJ-1.122]`, and `envSetK` replaced it as the open term
with a home but no supply (`dev/PLAN.md:600`, `:604`). The count did not fall.

**My figure: about 0.35k in-fence lines, band 0.2k to 0.6k. INFERRED.** The
basis, stated in full because the number is soft:

1. The 28 split into three shapes: **25 satisfier-in-K closures of one
   pattern**, 2 slot equalities, 1 environment set closure
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:61-66`).
2. The ONE delivered comparable at this site: `[LJ-1.122]` closed one member
   of the family and **added 179 lines** (`dev/PLAN.md:601`).
3. The 25 share one pattern, so the shared closure lemma is paid once and the
   applications are thin.

**P-l binds here and I obey it.** The 179 lines paid for a CONSTRUCTION, the
generic environment set. The 25 are CONDITIONAL closures of a different shape.
**So the 179 is a comparable at the same site, not a measured cure that
transfers.** I use it as the only real anchor available and I mark the
projection INFERRED.

### 3.4 The seconds: about 30 s, band 15 to 60. INFERRED

**Two measured rates in the tree bracket this work, and they differ by a factor
of eight** (`dev/ledger.toml:2681-2683`, MEASURED 2026-08-13):

| master | s per in-fence line |
|---|---:|
| `src/L/BoundedSubset.lagda.md` | 0.0121 |
| `src/L/Condensation/UpperAgree.lagda.md` | 0.0478 |
| `src/L/Condensation/LowerAgree.lagda.md` | 0.0899 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 0.0993 |

The certificate assembly lands at or near `BoundedSubset`'s rate. The
instantiation lands at or near the `*Agree` family's rate, because it is
twelve row frame work. **0.6k at 0.0121 is about 7 s. 0.35k at 0.0478 to
0.0993 is about 17 s to 35 s.** Add `[LJ-1.144]`'s measured 3.5 s for the
bridge. **Centre about 30 s.**

**One warning, C-40. This figure is about to move, and I name the mover.**
`[LJ-1.145]` measured a cure worth about 21 s on the `Condensation` family
(`dev/PLAN.md:625`), and `[LJ-1.147]` is landing it as I write. **If that lands,
the `*Agree` rates fall and my seconds figure needs re-basing before anyone
quotes it.** Nobody should carry the 30 s past `[LJ-1.147]`'s return.

### 3.5 The total, one number

**About 1.0 thousand in-fence lines and about 30 cold seconds. Band 0.6k to
1.5k lines.** The band is wide because one of its three terms, the
instantiation, has never been probed.

## 4. THE WIDEST UNMEASURED TERM, AND ITS PROBE

**The widest unmeasured term is the 28 closure facts at a real `K`.**

It is wider than the certificate side, for a measured reason. The certificate
side has one probe inside it already (`[LJ-1.124]`, 147 lines, GO). The
instantiation side has none. `[LJ-1.144]` named the same term as its own
widest, independently (`agents/tasks/LJ-1-144/lj-1.144-report.md:281-294`).
**Two dispatches now agree on one term, and nobody has run it.**

**THE PROBE, with its abort criterion fixed in advance (D-1).**

**The obligation, stated as an obligation and not as an entry point (C-33):**
supply ONE member of the 25-fact satisfier-in-K family at a concrete `K`, and
report the line count for that ONE fact.

Write the probe in `agents/tasks/<TASK>/`. `valK`
(`agents/tasks/LJ-1-113/lj-1.113-report.md` row 4) is the candidate I would
pick, because its missing piece is already named: the graph membership
`pr c yc ∈ T`, which `binClause-out` binds
(`src/L/Coding/Model.lagda.md:911-917`) and `domEntryK` then closes. **The
agent should take any member of the family it finds cheaper.** The site facts
are the `KFacts` record (`src/L/Condensation.lagda.md:5939-5975`), at the stage
`[LJ-1.144]` names (`agents/tasks/LJ-1-144/lj-1.144-report.md:291-294`). Cold
check at the C-12 cap, on a quiet machine.

- **GO** if the one closure closes at or below 60 probe lines. Then the shared
  pattern is real and the 0.35k band tightens onto the 25.
- **NO-GO** if the site facts do not reach it. Then the 25 are 25 separate
  proofs, the band re-opens at the full frame rate, and the whole
  instantiation needs its own chapter price.

**The probe must report the line count for the ONE fact, not for the file.**
`[LJ-1.124]` was marked MEASURED FALSE on exactly that distinction
(`agents/tasks/LJ-1-124/lj-1.124-report.md:129-134`).

## 5. DOES THE GCH TROPHY NEED THEM? YES, AND HERE IS THE EVIDENCE

### 5.1 `theorem` is Devlin 5.5, and 5.6 is one application of it

`theorem : ⟨ x ∈ˢ Lset κ ⟩` (`src/L/BoundedSubset.lagda.md:1621-1622`) is the
bounded subset lemma. The digest states 5.6 in full
(`dev/literature/devlin-II5.md:159-166`): "By 5.5, 𝒫(κ) ⊆ L_{κ⁺} for all
infinite cardinals κ ... The result follows at once." **The GCH theorem is one
application of `theorem` at `κ⁺` with `α = κ`, plus the counting lemma
1.1(vii). MEASURED from the digest.**

### 5.2 `theorem` is conditional on exactly these two, and on nothing after them

**MEASURED by `[LJ-1.121]` section 4**
(`agents/tasks/LJ-1-121/lj-1.121-report.md:161-165`): `Co`'s telescope holds
only `levelIn` and `cover`. Every later name in `:1408-1622` is a definition.
**So the two are the last gate before the lemma, and there is no second gate
behind them.**

### 5.3 Nothing else in the tree proves 5.5. MEASURED

`grep -rn "BoundedSubset" src/` returns one line outside the master itself:
`src/Everything.lagda.md:374`. No master re-proves the bounded subset lemma by
another route.

**And there is no other route in the literature.** Devlin's 5.5 proof runs
"collapse M to L_γ by condensation" (`dev/literature/devlin-II5.md:152-156`).
Condensation part (i) IS the pair `levelIn` and `cover`
(`agents/tasks/LJ-1-121/lj-1.121-report.md:322-330`, and
`dev/literature/devlin-II5.md:102-110`). **A GCH proof that skips condensation
is not in the digested literature. I did not find one and I do not claim one
cannot exist: C-36 binds.**

### 5.4 Both routes keep them, so no route change removes the need

`[LJ-1.131]` excluded them from both route prices and left them owed in full
(`agents/tasks/LJ-1-131/lj-1.131-report.md:402-406`): "Both routes owe it in
full and it does not separate them."

**Its master by master table (`:451`) is more precise than that, and I give the
precise reading rather than the convenient one.**

- **Under Route A**, `BoundedSubset`'s body `:1408-1622` "is generic in `x` and
  does not branch, so it survives verbatim". `levelIn` and `cover` are
  untouched.
- **Under Route A-prime**, the same row adds that the header opens `𝒮ʟ` where
  it opens `𝒮ᵥ` today (`:56`), and `IsCardinal` restates over L-injections.
  **So the two hypotheses would restate at the internal carrier.** Their SHAPE
  does not change, and the obligation does not fall. **INFERRED**, because
  `[LJ-1.131]` read the types and did not run the change, and it says so.

**Route A-prime's seven priced blocks A1 to A7 are all on the CARDINAL side**
(`agents/tasks/LJ-1-136/lj-1.136-report.md:82-90`). **No block removes the
condensation obligation, and no block supplies it.** So the route change moves
the carrier, not the need.

### 5.5 The one real threat to the wing, and it is NOT this chain

**I report it because it decides funding and no other section carries it.**
`[LJ-1.129]` Q4 measured that `IsCardinal`
(`src/L/BoundedSubset.lagda.md:1046-1047`) is AMBIENT by type, because the
master opens the V-structure at `:56`
(`agents/tasks/LJ-1-129/lj-1.129-report.md:202-231`). The ruled endpoint is
`L ⊨ GCH` **stated in L** (DD2). **So `theorem` today is a true claim about V
that mentions L, and nothing connects it to the ruled statement.**

**That gap is real and it is priced.** It is Route A-prime, blocks A1 to A7,
and `[LJ-1.134]` and `[LJ-1.136]` returned GO on its two gates
(`dev/PLAN.md:614`, `:616`). **It is a gap in the CARDINAL side. It leaves the
condensation side exactly where it is.** So it does not weaken this section's
answer. It means the wing needs BOTH the condensation supply and the
internalization, and neither substitutes for the other.

### 5.6 The reframe the brief asked me to test, and my verdict on it

**The brief's third abort case was "nothing above them is on the trophy's
route". It does NOT fire, and the measurement that suggested it points the
other way.**

The chain `[LJ-1.144]` found unconsumed runs `TwelveAgree` to `LeafAgree` to
`LevelHood` to `levelIn`. **That is the supply direction.** Each link is
unconsumed because the link BELOW it is unbuilt, not because the trophy has
moved away from it. **And the same measurement extends past `levelIn` to
`theorem` itself, which no master consumes either.**

**So C-35 is firing on a wing whose bottom end is unwritten, and the cure is to
write the bottom end, not to prune the top.** The one honest qualification: I
measured the import graph, and I did not audit every module inside
`src/L/Condensation.lagda.md` for a second consumer. **INFERRED that the whole
region is one chain**, on the same basis `[LJ-1.144]` marked INFERRED
(`agents/tasks/LJ-1-144/lj-1.144-report.md:40-42`).

## 6. DD4: THE SHAPE IS SHARED, THE INSTANCE IS PER-TOWER, AND THE SUPPLY IS THE EXPENSIVE HALF

**Maximize the code the two proofs share, and write it generic.**

**The statements name only shared objects.** `levelIn` and `cover` mention the
hull carrier `M`, the collapse `π`, and the collapse image `πX`. The collapse
(`src/V/Collapse.lagda.md`) and the hull (`src/L/Hull.lagda.md`) name no tower.
**MEASURED** by reading the two types at
`src/L/BoundedSubset.lagda.md:917-919`.

**They mention `Lset`, so the literal instances are Def tower content.** A J
tower states the same shape about its own level construction.

**The literature settles the split and it is not a guess.**
`dev/literature/devlin-II5.md:374-382`, the per-step DD4 table:

| step | verdict |
|---|---|
| C1, the level hood formula | **PER-TOWER content, same shape.** Def: syntax. J: generation data |
| C4, transfer along Σ₁-elementarity and the collapse | **EITHER tower** |
| F, 5.5 itself | **EITHER tower** |

**So `levelIn` and `cover` are C4's conclusions applied to C1's certificate.
The transfer that produces them is shared. The certificate they transfer is
per-tower.**

**The uncomfortable half, and it decides what a supply is worth.** Of my 1.0k
price, the shared part is the transfer assembly and the three lemmas, roughly
0.3k to 0.4k. **The per-tower part is the certificate and its instantiation,
roughly 0.6k to 0.7k, and it is the larger half.** The J tower re-pays that
half with sixteen operation graphs and no syntax
(`dev/literature/devlin-II5.md:375`). **So a supply here buys about one third
of itself twice and two thirds of itself once.** This is **INFERRED**: no J
tower exists in this tree to measure against.

**No stop-line pushed me toward writing fixed. I priced nothing fixed.**

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `levelIn` or `cover` is refutable | **MEASURED FALSE as a search result** (`agents/tasks/LJ-1-121/lj-1.121-report.md:71-102`). "Not refutable at all" stays **INFERRED**: no search proves absence |
| either is delivered by some master | **MEASURED FALSE.** The three reduced terms are named nowhere in `src/` |
| either is stated more generally than used | **MEASURED FALSE.** Both are at the hull's own objects (`:917-919`) |
| there is a hypothesis after them | **MEASURED FALSE.** `Co`'s body closes to `theorem` (`:1408-1622`) |
| something else in the tree proves the bounded subset lemma | **MEASURED FALSE.** Only `src/Everything.lagda.md:374` names the master |
| something in a master consumes `theorem` | **MEASURED FALSE.** `Devlin55` and `BoundedSubsetAt` appear only in probes |
| the chain above them is off the trophy's route | **MEASURED FALSE.** It is the supply side of a lemma the trophy needs. Section 5 |
| the 0.6k figure is a total | **MEASURED FALSE.** It excludes the instantiation, and `[LJ-1.129]:264-274` said so |
| the 28 closure facts have fallen since `[LJ-1.113]` | **MEASURED FALSE.** `someEnv` closed and `envSetK` replaced it (`dev/PLAN.md:600`, `:604`) |
| `[LJ-1.121]`'s 2.8k to 3.3k wall still stands | **MEASURED FALSE, and superseded.** `[LJ-1.123]` re-priced it to 0.6k on a delivered component map, and `[LJ-1.124]` measured one band inside it |
| Devlin's own proof avoids them | **MEASURED FALSE.** They are his chain (c) to (i) and (j) to (q) conclusions. Section 9 |
| they are an artifact of our encoding | **MEASURED FALSE.** Unlike the twelve rows, which `[LJ-1.144]` measured as ours. Section 9 |
| narrowing `levelIn` to successors would cut the price | **INFERRED FALSE.** The certificate is uniform in `δ`. Section 1.3 |
| the 0.35k instantiation band is measured | **INFERRED, not measured.** One delivered comparable at the site, 179 lines, of a different shape. P-l marked |
| the 30 s figure survives `[LJ-1.147]` | **INFERRED FALSE.** `[LJ-1.145]` measured a 21 s cure on the family. Section 3.4 |
| the whole unconsumed region is one chain | **INFERRED.** I measured the import graph, not every module inside `Condensation.lagda.md` |
| no derivation could supply the 28 | **NOT CLAIMED.** `[LJ-1.113]` found none refutable. C-36 binds |
| the ambient cardinal gap is fatal to this chain | **MEASURED FALSE.** It is the cardinal side, blocks A1 to A7. Section 5.5 |

## 8. WHY I RAN NO AGDA, AND WHY I WROTE NO PROBE

**MEASURED, at the time of the decision.** `ps aux` returned one live
typechecker owned by a sibling:

```
alsg 80054 100.0 10.1 ... agda src/L/Condensation.lagda.md
```

It ran inside `[LJ-1.147]`'s `check-ratio.py` timing run, which writes
`agents/tasks/LJ-1-147/runs/before-1.txt`. Load averages 4.18 / 4.57 / 4.54,
four users, 2026-08-13 19:12.

**The brief told me `[LJ-1.145]` is MEASURING SECONDS and told me to keep my
runs small. The correct small run here is no run.** Any probe of mine that
reaches `levelIn` must import `L.Condensation`. `[LJ-1.144]` measured that
import at about 30 s warm and about 150 s when the master re-elaborates
(`agents/tasks/LJ-1-144/lj-1.144-report.md:172-178`). **The sibling is
typechecking that master inside a BEFORE measurement, and `[LJ-1.147]` will
edit it next.** A run of mine would have loaded the machine during that
measurement, and the coming edit would have forced my own re-elaboration.
**That corrupts a sibling's deliverable to buy a figure my abort criterion does
not require.**

**D-1 rule 5 decided the rest**: "run it yourself while your task is live: that
is the only check it will ever get" (`dev/LESSONS.md:1075-1077`). **A probe I
cannot run is not evidence. So I wrote none rather than commit an unchecked
file.** The probe is named in full in section 4, with its abort criterion fixed
in advance, for the dispatch that gets a quiet machine.

**My brief's first abort case fired**: a price with a basis, and an answer on
whether the trophy needs them. **I report and STOP.**

## 9. LITERATURE: DEVLIN'S CONTENT, NOT OUR ENCODING'S

**The brief's question, answered directly: `levelIn` and `cover` are Devlin's
content.**

The digest's chain (c) to (q) (`dev/literature/devlin-II5.md:95-110`) is
Devlin's proof of condensation part (i). Its two halves are:

- **Forward.** For each ordinal γ of the collapse, transfer the Σ₁ statement
  "∃v∃z φ(z, v, γ)" from L_α to X and along the collapse to M, giving
  `L_γ ∈ M` for every γ < β, hence ⋃_{γ<β} L_γ ⊆ M (`dev2.txt:1200-1240`).
  **This is `levelIn`.**
- **Reverse.** The same transfer on "∃γ∃v∃z(φ(z,v,γ) ∧ x ∈ v)" gives
  M ⊆ ⋃_{γ<β} L_γ (`dev2.txt:1245-1290`). **This is `cover`.**

**So at this point Devlin's own proof needs exactly these two statements, and
he needs them for the same reason our `Condense` does: they are the two
inclusions that make the collapse a level.**

**The contrast with the twelve rows is the sharp part, and it changes the
verdict on the chain.** `[LJ-1.144]` measured that Devlin does NOT need a
twelve row agreement, and that the twelve rows are an artifact of our
`Formula` having twelve bounded clause rows
(`agents/tasks/LJ-1-144/lj-1.144-report.md:488-497`, citing
`dev/literature/devlin-II5.md:253-256`). **`levelIn` and `cover` are the
opposite case. Devlin states them. We did not invent them.**

**What IS our encoding's is the DIFFICULTY of supplying them.** Devlin gets
them from 2.7's Σ₁ level formula in one page. We must first build a bounded
description of the Def step with its bound inside the carrier, which is
`dev/literature/devlin-II5.md:245-256`, and on our coding that is the twelve
row substrate. **The statements are his. The bill is ours.**

## 10. THE RULES, ANSWERED

- **C-35.** This task is C-35 firing at the root. Section 5.6 finds the defect
  runs PAST the root, down to `theorem`. **The cure is to write the trophy, not
  to prune the chain.**
- **C-38 as extended.** Sections 0 and 3.3. I did not report the certificate
  interface as a supply, and I priced the instantiation as a separate term at a
  named site.
- **D-30.** Section 1.3. I checked for a narrowing, found one, and reported
  that it buys nothing rather than banking it as a saving.
- **DD8.** Sections 3 and 4. One best-effort figure per term, each with its
  basis. The widest unmeasured term is named with its probe.
- **D-1.** Section 8. The probe is specified with its abort criterion fixed in
  advance. It was not run, and the reason is stated rather than hidden.
- **P-l.** Section 3.3. The 179-line comparable is marked as a comparable at
  the same site, of a different shape, and the projection is INFERRED.
- **P-x.** `envSetK` is a telescope fact, not a record field, which is P-x
  applied correctly at `[LJ-1.125]`. It is still unsupplied.
- **C-12.** No Agda ran, so no cap was set or raised. One sibling process was
  live and I stayed off the machine. Load reported beside the only figure I
  took, section 8.
- **C-22.** This file was a skeleton before any reading. It was filled as
  answers landed.
- **C-36.** No refusal is reported as an impossibility. Section 5.3 says
  plainly that I did not find another GCH route and does not claim none
  exists.
- **C-39.** Section 8. The one prohibition that bit was the heap and machine
  discipline, and I name the door it closed rather than working around it.
- **C-40.** Section 3.4. My seconds rest on a rate that a live sibling is about
  to change, and I say so beside the figure.
- **C-32.** The same section, and this is the law that governs it. `[LJ-1.147]`
  is landing a cure inside the `Condensation` cone. **Every seconds figure in
  this report, including mine, goes stale when it lands.** The gate to re-run
  is `check-ratio.py` on the wing, and my 30 s must be re-derived from the new
  rates rather than carried forward.
- **C-34.** Section 4 names the next cure and section 8 reports the wall that
  stopped me from pricing it: the machine was not mine to load. **I did not
  leave a cure named and unpriced without saying which of the two applied.**
- **C-33.** Section 4 states the OBLIGATION, one member of the 25-fact family,
  and offers `valK` as a candidate rather than a mandate.
- **C-31, C-37, D-10, D-26, D-29, I-5, R-40.** Read through
  `scripts/rules.py --for recon` and `--for probe`. **D-10 bit**: the recorded
  residue here is `[LJ-1.121]`'s 2.8k to 3.3k wall, and section 2.4 prices its
  TRUTH before its proof. It is superseded by two later measurements.
- **DD23.** No mathematical prose was written.
- **DD4.** Section 6.

## 11. GATES

- **No Agda ran.** Section 8 gives the reason and the evidence.
- `.venv/bin/python scripts/ledger.py --brief`: standing **28,617 lines over 85
  masters**, measured from HEAD.
- `.venv/bin/python scripts/lint-prose.py --check` on this report: run at the
  end.
- `scripts/lint-agda.py --check`: nothing to check. No probe was written.
- **No `make check`.** The orchestrator runs it.
- **No master was edited. No commit, no push. No probe was written.**
- **The working tree at the close, and NONE of it is mine except my report.**
  `git status --short` shows `dev/PLAN.md` and `scripts/check-ratio.py`
  modified, plus the untracked `agents/tasks/LJ-1-147/`,
  `agents/tasks/LJ-1-148/` and `scripts/tests/test_ratio_noise.py`. **Those are
  the siblings' work.** My only new file is
  `agents/tasks/LJ-1-146/lj-1.146-report.md`.
- Load at the close: 4.36 / 4.39 / 4.44, four users, 19:22. **No typechecker
  was running at the close.** `ps aux | grep "[a]gda"` returned only
  `_build/tools/agda-watchdog.sh` and two shell wrappers, none of them mine.
  **I started no Agda process and I left none running.** Section 8.

## ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-144/lj-1.144-report.md`, read WHOLE.** TOOK the
  unconsumed chain table (`:78-84`), the bridge price (`:16-22`), the
  route-neutral exclusion (`:217-225`), the DD4 per-tower verdict (`:231-243`),
  the widest-term finding (`:281-294`), and the import cost figures
  (`:172-178`). **Section 5.6 extends its finding rather than contradicting
  it.**
- **`agents/tasks/LJ-1-131/lj-1.131-report.md`, read `:380-470`.** TOOK the
  exclusion from both routes (`:402-406`) and the master by master table row
  for `BoundedSubset` (`:451`), which section 5.4 uses.
- **`agents/tasks/LJ-1-121/lj-1.121-report.md`, read WHOLE.** TOOK the two
  statements (`:36-42`), the four consumer sites (`:58-60`), the three-term
  reduction (`:112-151`), the "no hypothesis after them" measurement
  (`:161-165`), the generality check (`:171-181`), and the literature note
  (`:322-330`). **This is the dispatch that met them head on.**
- **`agents/tasks/LJ-1-121/ProbeLJ1121A.agda`**, read at `:83-118`. TOOK the
  `Supply` reduction (`:102-110`) and `CoverTransfer` (`:116-118`). NOT
  re-run: section 8.
- **`agents/tasks/LJ-1-123/lj-1.123-report.md`, read WHOLE.** TOOK the four
  bands (`:35-43`), the delivered component map (`:63-124`), the three facts
  (`:136-223`), and the DD4 verdict (`:353-374`).
- **`agents/tasks/LJ-1-124/lj-1.124-report.md`, read `:1-133`.** TOOK the GO
  verdict, the 147-line decode measurement (`:38-42`), the 37.4 s runs
  (`:44-52`), and the line-counting distinction (`:129-134`).
- **`agents/tasks/LJ-1-129/lj-1.129-report.md`, read `:150-320`.** TOOK Q4's
  ambient cardinal finding (`:202-231`), Q5's verdict on the hypotheses
  (`:233-274`), and the clean-half audit of `Devlin55.Co`
  (`:278-300`). **This is the report that priced the 0.6k as optimistic.**
- **`agents/tasks/LJ-1-113/lj-1.113-report.md`, read `:1-70`.** TOOK the three
  counts (`:6-18`), the 29-row table (`:29-59`), and the three-shape split
  (`:61-66`).
- `agents/tasks/LJ-1-119/ProbeLJ1119A.agda`, read `:1-47`. TOOK the site entry
  and the fact that `Devlin55` is entered only in a probe.
- **`agents/tasks/archive/LJ-1-51/lj-1.51-report.md`, read `:1-30` and
  `:130-175`.** TOOK the survivor table (`:19-20`), **the wall section title
  and the term the agent could not write (`:135-153`)**, the
  collapse-of-the-level (`:151-152`, `:161-162`), and **the 200 to 400 line
  contingent price for `levelIn` alone (`:166-168`)**. **This is the report
  that named the wall FIRST, and section 2.2 uses it to raise the confidence in
  `[LJ-1.121]`'s independent reduction.**
- `agents/tasks/archive/LJ-1-57/lj-1.57-report.md`, read `:1-20`, `:97`,
  `:130-151`. TOOK the ledger rows and the deferral language of section 2.1.
- `agents/tasks/archive/LJ-1-61/lj-1.61-report.md`, read `:22-31`, `:153`,
  `:215`, `:240`. TOOK the "nine dispatches" count and the deferral pattern.
- `agents/tasks/archive/LJ-1-59/lj-1.59-report.md` and
  `agents/tasks/archive/LJ-1-60/lj-1.60-report.md`, read at the `levelIn`
  sections. TOOK the same deferral pattern. Nothing new.
- `agents/tasks/archive/LJ-1-112/` and `LJ-1-113/`: `[LJ-1.112]`'s zero-meta
  result taken through `[LJ-1.144]:52-53` and `[LJ-1.129]:164-170` rather than
  re-read.
- **`src/L/BoundedSubset.lagda.md`, read `:880-1035`, `:1355-1626`, `:50-60`,
  `:1043-1050`.** TOOK the two telescopes, the four uses, `theorem`,
  `IsCardinal`, and the ambient `open hPropStructure 𝒮ᵥ` at `:56`.
- `src/L/Condensation.lagda.md`, read at `:2489-2493` and `:6903-6911` only,
  and NOT edited. `[LJ-1.145]` owns it. **Its working copy matched HEAD when I
  read it** (`git diff` empty), so my line numbers are HEAD's.
- `src/Everything.lagda.md`, read `:368-380`. NOT edited.
- **`dev/PLAN.md`**: `:499-512` (the deferral rows), `:585-603` (`[LJ-1.105]`
  to `[LJ-1.115]`), `:599-628` (the recent rows and `[LJ-1.8]`).
- **`dev/ledger.toml`**: `:2665-2713` (the two measured rates and the caliber
  note), `:3039` (the master's 1,409 in-fence lines).
- **`dev/LESSONS.md`**: **D-1 read WHOLE at `:1038-1094`, including the
  2026-08-13 probe-location ruling**, which section 8 works to. C-12, C-22,
  C-35, C-36, C-38, C-39, C-40, D-10, D-26, D-29, D-30, P-l, P-x, R-40, P-i
  loaded through `scripts/rules.py --for recon` and `--for probe` and read.
- **`AGENTS.md`, read fresh** for the probe rule, as the brief ordered.
- `archive/dev/`: **NOT read.** The `D` series is superseded by `DD`, and no
  archived record bears on whether a live hypothesis is supplied.

## LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read at `:95-110`, `:143-175`, `:240-262`,
`:360-396`.**

- `:95-110` is the chain (c) to (q). **It is where `levelIn` and `cover` are
  Devlin's own two inclusions.** Section 9.
- `:143-166` is 5.5 and 5.6. **It is where the trophy turns out to be one
  application of `theorem`.** Section 5.1.
- `:152-156` is 5.5's proof, which reads "collapse M to L_γ by condensation".
  **That is the step nothing else can supply.** Section 5.3.
- `:374-382` is the per-step DD4 table. **Rows C1, C4 and F give section 6 its
  split**: the transfer is either-tower, the certificate is per-tower, and 5.5
  itself is either-tower.
- `:253-256` is the freedom clause, which `[LJ-1.144]` used to show the twelve
  rows are ours. **Section 9 uses it for the contrast: the freedom is about the
  SHAPE of the bounded description, not about whether the two inclusions are
  needed.**

`_build/literature/dev2.txt`: **NOT opened directly.** Every `dev2.txt`
citation above is quoted through the digest.

`dev/literature/devlin-errata.md`: **NOT read.** `[LJ-1.136]` measured that the
errata touch no part of II.5
(`agents/tasks/LJ-1-144/lj-1.144-report.md:503-508`). **I took that finding
rather than re-measuring it, and I record that I took it.**
