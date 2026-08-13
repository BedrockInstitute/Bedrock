# LJ-1.151 report: the satisfier-in-K instantiation, measured

tier: opus (version `override`). **No master was changed. Two probes were
written and both ran GREEN. No commit, no push.** Every negative is marked
**MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. LEAD

### 0.1 The verdict against the criterion, which I did not move

**GO. The one fact closes in 21 probe lines. The criterion was 60.**

The fact is `valK`, the brief's candidate
(`src/L/Condensation/TwelveAgree.lagda.md:155-157`). It closes at a concrete
`K`, the constructibility level `Lset α` as an element of L. The probe is
`agents/tasks/LJ-1-151/ProbeLJ1151A.agda`, exit 0.

**The 21 lines are the fact. What I excluded is in section 1.2, and the file
total is there too.**

### 0.2 The finding that outranks the number

**The frame's `valK`, AS STATED, is REFUTABLE. MEASURED, exit 0, at
`agents/tasks/LJ-1-151/ProbeLJ1151B.agda:48-58`.**

`valK` concludes `fst yc ∈ K` and `yc` occurs in NO premise. Take `yc` to be
the K slot itself. Then `valK` gives `K ∈ K`, and `∈-irrefl`
(`src/V/Hierarchy.lagda.md:155`) closes it. The refutation needs one clause
code of binary shape in the clause set and nothing else about `K`.

`scripts/check-unbound-hyp.py` already flagged it. **MEASURED today:**

```
src/L/Condensation/TwelveAgree.lagda.md:155: valK: rule 1, conclusion subject unconstrained: yc
src/L/Condensation/TwelveAgree.lagda.md:158: valK-un: rule 1, conclusion subject unconstrained: yc
```

**So the 21-line figure prices the CORRECTED fact, which carries the graph
membership `hc : pr c yc ∈ T` that the row's `back` already binds**
(`binClause-out`, `src/L/Coding/Model.lagda.md:904-910`). I say this at the
top because a 21-line price for a false statement would be worthless.

`[LJ-1.113]` measured that the frame's `valK` is not derivable
(`agents/tasks/LJ-1-113/lj-1.113-report.md:34`, probe A, exit 42). **It did
not measure that the statement is false. That is new, and it makes the frame
line a defect and not a debt.**

### 0.3 The DD4 answer, which the brief asked for at the top

**The one fact is TEMPLATE content, and that moves `[LJ-1.146]`'s split.**

Of the 21 lines, **19 name no tower and 2 name `Lset`**. The closure lemma
`prK` takes transitivity as its ONLY premise, so a J level instantiates it
unchanged. The per-tower part is `levelK` and the module application, and it
is two lines.

**`[LJ-1.146]` section 6 put the instantiation on the PER-TOWER side and
called that side the larger half.** For this fact that is wrong by
measurement. Section 6 gives the correction and its limits.

### 0.4 The wall did not come into it

**MEASURED. Neither probe names `π`, the collapse, the hull or `πX`.**
`grep` over both files returns nothing for those terms. The deepest object
either probe touches is `Lset α` under `opaque`
(`src/L/Constructible.lagda.md:222`), and no probe unfolds it.

**So the two halves ARE separable at this term.** The instantiation side can
be priced without `π (Lset m') ≡ Lset (π m')`. That is a positive finding for
the phase and it was the brief's most valuable possible negative.

### 0.5 The band: it tightens on 9 of the 25 and stays open on 16

**This is a report on what the GO licenses, not a change to the criterion.**

The criterion was one fact at or below 60 lines. That fact closed at 21. The
brief's stated inference was that "the shared pattern is real and the 0.35k
band tightens onto the 25". **The pattern is real for 9 of the 25. For the
other 16 it is not the same pattern at all.** Section 4 splits the family by
shape and gives the evidence for each side.

## 1. THE ONE FACT AND ITS LINE COUNT

### 1.1 What the fact is

The obligation, stated as an obligation and not as an entry point (C-33):

> Supply `valK` at a concrete `K`. `valK` says that the value recorded for a
> binary clause code lands in `K`.

The probe supplies it in three parts
(`agents/tasks/LJ-1-151/ProbeLJ1151A.agda`):

| part | lines | what it is |
|---|---:|---|
| the `Fact` module header | 1 | it binds `K` and its transitivity |
| `Fact.prK` | 8 | a transitive set absorbs both components of a Kuratowski pair it contains |
| `Fact.valK` | 8 | the obligation, 6 of them the type and 2 the proof |
| `levelK`, `AtLevel` | 4 | the concrete instance: `K` is `Lset α` as an element of L |
| **total, THE FACT** | **21** | |

`Ktr`, the transitivity of `K`, is **not** a hypothesis of the probe. It is
discharged at `:89` by `layer-trans (Lset-layer α)`, both delivered
(`src/L/Constructible.lagda.md:183`, `:246`).

### 1.2 What I excluded, and the file totals

**Excluded from the 21: the OPTIONS header, 19 import and open lines, the
module header, the `AbsL` module application, every comment and every blank
line.** None of that is the fact's price. `[LJ-1.124]` was
marked MEASURED FALSE on exactly this distinction
(`agents/tasks/LJ-1-124/lj-1.124-report.md:129-134`).

| figure | value |
|---|---:|
| **THE FACT** | **21** |
| the slot match block, section 1.3 | 14 |
| fact plus slot match | 35 |
| probe A file, non-blank non-comment | 59 |
| probe A file, non-blank | 96 |
| probe A file, all lines | 112 |
| probe B refutation, the fact only | 9 |
| probe B file, non-blank non-comment | 24 |
| probe B file, non-blank | 49 |
| probe B file, all lines | 58 |

**Both the 21 and the 35 are inside the 60-line criterion.**

### 1.3 The slot match is machine-checked, not read

The frame writes its facts at slots of an environment. So the probe restates
`valK` in the frame's own notation, at `lookup Cs γ'`, `lookup T γ'` and
`lookup K γ'`, and discharges it from the block above
(`ProbeLJ1151A.agda:98-112`, module `Slots`). **The match is therefore a
typecheck and not a reading.**

The type uses the same names in the same senses as the master: `pr` from
`V.Coding`, `#_` from `InfinitySet`, `_∈_` from the library, and `S` from
`hPropStructure 𝒮ʟ`. **MEASURED** by reading `TwelveAgree.lagda.md:20-42`
against `ProbeLJ1151A.agda:27-46`.

### 1.4 The three changes to the frame's type, named

1. The `K` slot is a concrete set, which is the point of the probe.
2. The `C` slot is the set it denotes.
3. **The graph membership `hc` is a premise.** Section 0.2.

**There is no fourth change.** The `k`, the shape equation and the
clause-set membership stand exactly as the frame writes them.

### 1.5 One fact about the proof that sharpens the obligation

**The proof uses `hc` alone. `C`, `c∈` and `shape` are dead weight.
MEASURED**, by reading `ProbeLJ1151A.agda:80-81`: the body is
`prK (fst c) (fst yc) (Ktr hc TK) .snd`.

So the honest obligation is not `valK` at all. It is the graph entry closure,
which the stage already names as `domEntryK`
(`src/L/Condensation.lagda.md:6710-6712`). **`valK` is `domEntryK`'s second
projection with three unused premises, and its own type lost the one premise
that matters.**

## 2. WHICH FAMILY MEMBER, AND WHY

**I took `valK`, the brief's candidate. I did not look for a cheaper one, and
here is why that was right rather than lazy.**

1. `valK` is the only member whose missing piece the record already names
   (`agents/tasks/LJ-1-113/lj-1.113-report.md:34`). A probe that measures a
   named gap measures something.
2. It is the archetype of the largest single sub-shape. Section 4 shows that
   9 members conclude "a component of a pair recorded in the graph is in K",
   which is what `prK` closes.
3. It carries a defect. Section 0.2. **A cheaper member would have hidden
   that, and the defect is worth more than the number.**

**What I did NOT take, and the honest reason.** I did not take a member of
the environment or the cons family. Those conclude that a SET the machine
BUILDS is in `K`. Section 4 explains why that is a different obligation and
why my figure does not price it.

## 3. THE RESIDUE I DID NOT DISCHARGE, STATED PLAINLY

**`TK : T ∈ K` stays a hypothesis of my probe.** `T` is the graph slot.

This is a genuine site fact of the stage, not a hole I hid. `witK` supplies
exactly this shape at `src/L/Condensation.lagda.md:6715-6724`, and `domK` at
`:6713-6714`. **But it is unsupplied there too**: `SatGraphAgree` takes all
four as telescope hypotheses, and `LeafAgree` passes them up
(`:6918`, `:6999`).

**So the buck passes to the first module that puts a real set in the `K`
slot, and MEASURED, no module in `src/` does.** `grep -rn "KFacts" src/`
returns only the record, its `Cons` lift and four telescope parameters. **Not
one instantiation.** C-38 as extended: the interface has no instance.

**The residue is SMALL and FIXED, and that is the load-bearing point.** It is
"the ambient objects are in K", which is a handful of facts about the graph,
the clause set and the carrier. It is not 25 facts. **INFERRED**, from the
shape of the four stage hypotheses at `:6698-6724`.

## 4. THE 0.35k BAND: IT TIGHTENS ON 9 AND STAYS OPEN ON 16

**The family does not have one shape. It has two plus a hybrid, and my probe
prices one of them.**

### 4.1 Shape one: extract a component. `prK` closes it

The conclusion is a component of a pair that some ambient set records. The
adequacy theorem pins the pair, the ambient set is in `K`, and `prK` finishes
in two transitivity steps.

| member | why it is this shape | class |
|---|---|---|
| `valK`, `valK-un` | the graph records `pr c yc`, and the graph is the ambient set | **MEASURED** for `valK`, this probe |
| `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`, `subK-neg`, `subK-un`, `subK-allin` | `subValAt-adequate` pins `pr (pr ar a) y ∈ T`, and `T` is the same ambient set (`agents/tasks/LJ-1-113/lj-1.113-report.md:48`) | INFERRED |

**Nine members, and their ambient set is ONE object, the graph.** For these
the pattern is real and one lemma serves them all.

**Three more members are HYBRID and I do not count them here.** `valV`,
`valW` and `wKfact` extract a component, but their ambient object is the
ENVIRONMENT, not the graph. `[LJ-1.113]` says so plainly: `tmValAt-out`
"pins v via the environment, which only gives v ∈ K after the env closure"
(`agents/tasks/LJ-1-113/lj-1.113-report.md:45`). **So their price is shape
one's price PLUS shape two's, and shape two is unmeasured.**

### 4.2 Shape two: build a set. `prK` does NOT close it

The conclusion is a set the machine constructs. `K` must be closed under that
construction. **A component closure cannot give this**, because the members
being in `K` does not put the set in `K`.

| member | what it needs | class |
|---|---|---|
| `envK-mem`, `envK-neg`, `envK-top`, `envK-imp`, `envK-allin` | `K` closed under the environment set | INFERRED |
| `envInK-mem`, `envInK-neg`, `envInK-top`, `envInK-imp` | `K` closed under an environment, a set of pairs | INFERRED |
| `consK-exist`, `consK-forall`, `consK-allin` | `K` closed under environment extension | INFERRED |
| `sucK` | `K` closed under the model successor, a union | **MEASURED FALSE from the closure fields** (`[LJ-1.113]` probe D, `agents/tasks/LJ-1-113/lj-1.113-report.md:102-107`) |

**Thirteen members, counting `sucK`.** `sucK` is the one already measured,
and it went the wrong way.

**The three shapes account for all 25**: 9 plus 13 plus 3.

### 4.3 So the band

**It tightens on shape one and it re-opens on shape two.**

- **Shape one, 9 members: MEASURED at 21 lines for the first, and the shared
  lemma is paid once.** The remaining 8 are applications of `prK` at the same
  ambient set. **INFERRED** at a few lines each.
- **Shape two, 13 members counting `sucK`: NOT MEASURED, and my probe says
  nothing about it.** The one member of it that anyone has probed came back
  negative.
- **Hybrid, 3 members: they inherit shape two's risk.** Their price is not
  bounded by mine.

**So my GO covers 9 of the 25: one by measurement and 8 by inference from
it. It does not cover 16.**

**I give no new total.** `[LJ-1.146]`'s 0.35k centre rests on a comparable of
a different shape and it says so (`agents/tasks/LJ-1-146/lj-1.146-report.md:274-289`).
My probe moves 9 of the 25 and leaves 16 where they were. **P-l binds: a
measured cure does not transfer by analogy, and shape two is not my site.**

**The next probe, named with its abort criterion (DD8).** Take `envInK-mem`,
the cheapest member of shape two, at `K = Lset α`. **GO if it closes at or
below 60 lines from the level's own closure properties. NO-GO if it needs a
closure the level does not have**, in which case shape two needs the level
hood certificate and not a closure lemma.

## 5. THE WALL

**It did not come into it. MEASURED, section 0.4.**

I record the mechanism, because it says WHY the two halves separate here.
`Lset` is `opaque` (`src/L/Constructible.lagda.md:222`), and `Lset-layer`
and `layer-trans` are delivered above the seal. **So a probe can name the
concrete level, use its transitivity, and never unfold it.** P-l is the law
and this is a clean instance of it: naming a concrete stage costs nothing
when the stage is an atom to the elaborator.

**`π (Lset m') ≡ Lset (π m')` is a different term and my probe never
approaches it.** It sits on the certificate side, not the instantiation
side.

## 6. DD4

**Maximize the code the two proofs share, and write it generic.**

**Of the 21 lines, 19 name no tower.**

| block | lines | tower |
|---|---:|---|
| `Fact.prK` | 8 | **SHARED.** Its only premise is transitivity |
| `Fact.valK` | 9 | **SHARED.** It names `pr`, `#_` and the carrier, none of them a tower |
| `levelK`, `AtLevel` | 4, of which 2 name `Lset` | **PER-TOWER** |
| `Slots` (outside the 21) | 14 | **SHARED.** Slot bookkeeping names no tower |

A J level is transitive. So `prK` instantiates unchanged, and the J tower
re-pays two lines, not twenty one.

**The correction to `[LJ-1.146]` section 6.** It put the instantiation on the
per-tower side and called that side the larger half
(`agents/tasks/LJ-1-146/lj-1.146-report.md:475-482`). **For this fact the
per-tower share is about one tenth.** The report marked that split INFERRED
and said no J tower exists to measure against, so this is a correction to an
inference and not a contradiction of a measurement.

**The limit of my correction, stated so nobody over-reads it.** I measured one
fact of shape one. **Shape two may go the other way**, because a closure of
`K` under the machine's environment construction names the machine, and the
machine is per-tower content (`dev/literature/devlin-II5.md:375`, row C2).
**INFERRED.**

**No stop-line pushed me toward writing fixed.** The generic form was also the
short form here.

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the one fact closes at or below 60 lines | **MEASURED TRUE.** 21 lines, exit 0 |
| the frame's `valK` as stated is supplyable | **MEASURED FALSE.** Probe B refutes it, exit 0 |
| `valK-un` has the same defect | **INFERRED.** `check-unbound-hyp.py` flags it by the same rule. I did not write its refutation |
| the refutation needs a property of `K` | **MEASURED FALSE.** Probe B's `K` is an arbitrary `S` |
| the refutation needs a new object | **MEASURED FALSE.** It applies `valK` at the K slot itself |
| the clause set holds a binary code at the real site | **INFERRED TRUE**, from the twelve rows. I did not measure it, and the refutation is stated as conditional on it |
| the transitivity of the level is delivered | **MEASURED TRUE.** `layer-trans (Lset-layer α)`, exit 0 |
| `T ∈ K` is discharged by my probe | **MEASURED FALSE.** It is a hypothesis. Section 3 |
| some module in `src/` puts a real set in the K slot | **MEASURED FALSE.** `grep -rn "KFacts" src/` finds no instantiation |
| the proof uses the clause-set premise or the shape premise | **MEASURED FALSE.** The body uses `hc` alone |
| the probe drifted into the wall | **MEASURED FALSE.** No probe names `π`, the collapse or the hull |
| the whole 25-fact family shares one pattern | **MEASURED FALSE for the family as a whole.** Section 4 splits it into 9, 12 and 3 by shape |
| the other 8 members of shape one close as cheaply | **INFERRED.** I measured one |
| shape two closes from the level's own properties | **NOT MEASURED.** Section 4.3 names the probe |
| `sucK` follows from the closure fields | **MEASURED FALSE**, by `[LJ-1.113]` probe D, not by me |
| the instantiation is per-tower content | **MEASURED FALSE for this fact.** 19 of 21 lines name no tower |
| the 0.35k band tightens onto all 25 | **INFERRED FALSE.** It tightens on 9 |
| no supply for shape two exists | **NOT CLAIMED.** C-36 binds. I did not search for one |

## 8. GATES AND MEASUREMENTS

**The machine was BUSY throughout. `[LJ-1.150]` holds the other slot.** Load
averages ran between 4.27 and 7.58, four users, from 20:32 to 20:37 on
2026-08-13. **My figure is LINES, so a busy machine cost me time and nothing
else. I say so rather than waiting, as the brief instructed. Every second
below is therefore indicative and no ratio should be taken from it.**

| run | file | result | real s | load at start |
|---|---|---|---:|---:|
| A, first form | `ProbeLJ1151A.agda` | exit 0 | 1.73 | 6.04 |
| A, at the frame type | `ProbeLJ1151A.agda` | exit 0 | 1.82 | 6.34 |
| A, with the slot match | `ProbeLJ1151A.agda` | exit 0 | 1.77 | 4.47 |
| B, the refutation | `ProbeLJ1151B.agda` | exit 0 | 0.80 | 6.34 |

`GHCRTS="-A64m -I0 -M8g"` on every run. **One agda process at a time. The cap
was never raised. No heap exhaustion, no kill, no wall.** The `.agdai` of
each probe was deleted before its timed run, so each figure is a full
re-elaboration of the probe against a warm dependency cone.

**The cone is light and that is itself a finding.** Neither probe imports
`L.Condensation`, `L.Coding.Model` or `L.Condensation.TwelveAgree`. **So the
K-closure content sits far below the twelve-row substrate, and it does not
pay the substrate's check cost.** `[LJ-1.144]` measured the heavy import at
about 30 s (`agents/tasks/LJ-1-144/lj-1.144-report.md:172-178`). My fact
needs none of it.

**Checkers.**

- `scripts/lint-agda.py --check` on both probes: **exit 0**.
- `scripts/check-unbound-hyp.py` on both probes: **clean (2 files)**.
- `scripts/check-probes.py --check`: **clean**, 1641 tracked files.
- `scripts/check-unbound-hyp.py src/L/Condensation/TwelveAgree.lagda.md`:
  **2 hypotheses flagged**, quoted at section 0.2. **I did not edit that
  file.** `[LJ-1.150]` holds it and the run was read only.
- `scripts/lint-prose.py --check` on this report: run at the close.
- `scripts/ledger.py --brief`: standing **28,723 lines over 85 masters**,
  measured from HEAD. Thresholds SUSPENDED per the ledger header.
- **No `make check`.** The orchestrator runs it.

**Prohibitions.** No master edited. `src/Everything.lagda.md` not opened.
`src/L/Coding/Graph.lagda.md` not opened. `src/L/Condensation/TwelveAgree.lagda.md`
read only, never written. `src/ProbeLJ1134A.agda` and `src/ProbeLJ1136*.agda`
untouched. No commit, no push, no `git checkout`, `stash`, `reset` or `clean`.

**The working tree at the close.** `src/L/Condensation/TwelveAgree.lagda.md`
modified and `agents/tasks/LJ-1-150/` untracked: **those are `[LJ-1.150]`'s,
not mine.** My files are `agents/tasks/LJ-1-151/lj-1.151-report.md`,
`ProbeLJ1151A.agda` and `ProbeLJ1151B.agda`. **The probes are tracked, in
`agents/tasks/`, and never deleted.**

## 9. THE RULES, ANSWERED

- **D-1.** The abort criterion was written into the brief before the run and
  I did not move it. Section 0.1 reports against it as written, and section
  0.5 reports what it licenses separately.
- **C-33.** Section 1.1 states the obligation as an obligation.
- **C-38 as extended.** This probe instantiates an interface that nothing
  instantiates. Section 3 records that `KFacts` still has no instance in
  `src/`, and section 1.5 records that the fact reduces to a projection.
- **D-10.** **This law bit hardest.** I priced the TRUTH of the recorded
  residue before its proof, and the residue is false. Section 0.2.
- **P-l.** Section 4.3. I did not carry my shape-one measurement onto shape
  two.
- **P-x.** `TK` is a telescope fact, not a record field, and I left it as
  one. Section 3.
- **C-12.** One agda process, `-M8g`, cap never raised. Load reported beside
  every figure. Section 8.
- **C-22.** This file was a skeleton before I read the archive.
- **C-31, C-32.** Section 8 says the seconds are indicative on a busy
  machine, so nobody quotes them.
- **C-34.** Section 4.3 names the next probe and its abort criterion, so no
  cure is left named and unpriced.
- **C-36.** Section 7's last row. I do not claim no supply exists for shape
  two. I claim I did not measure one.
- **C-39.** Section 10.
- **C-40.** Section 6 names the limit of my own correction, and section 4.3
  names the limit of my own band.
- **D-26.** Section 6 uses the digest's per-step carrier column.
- **D-29, D-30.** Section 1.5 reports the narrowing I found, that the fact
  needs one premise of three, and does not bank it as a saving.
- **I-5.** The probe leaves no unsolved meta. Exit 0 with no
  `UnsolvedMetaVariables`.
- **R-40.** No deep successor chain appears. `Lset α` stays opaque.
- **DD8.** One best-effort figure per term, each with its basis.
- **DD23.** No mathematical prose was written. The probes carry comments
  only.
- **DD4.** Section 6.

## 10. C-39: WHAT A PROHIBITION CLOSED

**One brief line closed a door I can see, and it was right.**

"Do not touch `src/L/Condensation/TwelveAgree.lagda.md`" blocks the route
where the frame's `valK` gets its missing premise. **That is a one-line fix
to the master and section 0.2 measures that it is needed.** The prohibition
is correct for this dispatch, because `[LJ-1.150]` is editing that file now.
**The fix belongs in a dispatch that owns the file.**

I record the exact change so the next agent does not re-derive it: add
`→ ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ') ⟩` before the conclusion of
`valK` at `:157` and of `valK-un` at `:160`. **The rows already bind that
premise, so no consumer breaks. INFERRED**, from `binClause-out`'s type at
`src/L/Coding/Model.lagda.md:904-910`. **I did not run the consumers.**

**No other brief line blocked a route.** The write scope cost nothing: the
probe fits in `agents/tasks/LJ-1-151/`.

## 11. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-146/lj-1.146-report.md`, read WHOLE.** TOOK section 4
  (`:321-355`), which specifies this probe and its criterion; the 0.35k
  instantiation term and its basis (`:260-289`); the DD4 split I correct in
  section 6 (`:449-484`); and the wall's location (`:160-184`).
- **`agents/tasks/LJ-1-113/lj-1.113-report.md`, read WHOLE.** TOOK the 29-row
  table (`:29-59`), row 4 for `valK` (`:34`), the three-shape split
  (`:61-66`), the `sucK` measurement (`:102-109`), the price and its basis
  (`:133-146`), and the DD4 reading (`:217-239`). **Section 4 of my report
  re-splits its 25 by a different axis and says why.**
- **`agents/tasks/LJ-1-124/lj-1.124-report.md`, read `:110-169`.** TOOK the
  one-fact against whole-file distinction (`:129-134`), which section 1.2
  obeys.
- **`agents/tasks/LJ-1-144/lj-1.144-report.md`, read `:270-300`.** TOOK the
  widest-term finding (`:281-294`) and the heavy import cost (`:172-178`).
- `agents/tasks/LJ-1-96/ProbeLJ196A.agda`, read WHOLE. TOOK the `valK` from
  `domEntryK` shape (`:44-54`). **It states `domEntryK` as a hypothesis, so
  it is a pass-through and not an instantiation. My probe discharges the
  transitivity instead.**
- `agents/tasks/LJ-1-150/lj-1.150-report.md`, read `:1-30`. TOOK only the
  fact that the sibling holds `TwelveAgree` right now.
- `agents/tasks/archive/LJ-1-51/lj-1.51-report.md`: **NOT read.** The wall it
  names never entered my probe, and `[LJ-1.146]:160-184` carries its content
  at `file:line`. Section 0.4 measures that I stayed clear of it.
- **`src/L/Condensation/TwelveAgree.lagda.md`, read `:18-50` and `:114-340`.
  NOT edited.** TOOK the `AbstractFrame` telescope, `valK` at `:155-157`,
  `valK-un` at `:158-160`, `transK` at `:220-222`, and the preamble the probe
  mirrors. **Its working copy is `[LJ-1.150]`'s, so my line numbers are the
  working copy's and not HEAD's.**
- **`src/L/Condensation.lagda.md`, read `:5900-6000` and `:6674-6760`. NOT
  edited.** TOOK the `KFacts` record (`:5940-5976`), `KFactsCons`
  (`:5983-5990`), and the `SatGraphAgree` telescope with `codesK`,
  `closedEntryK`, `domEntryK`, `domK` and `witK` (`:6698-6724`).
- **`src/L/Coding/Model.lagda.md`, read `:400-520` and `:880-940`.** TOOK
  `binClause-out` (`:904-917`, its type at `:904-910`), `envOverAt` and its four projections
  (`:483-495`), and `valuesInAt-out` (`:446-451`).
- **`src/L/Constructible.lagda.md`, read `:75-130` and `:175-260`.** TOOK
  `isTransV` (`:83-84`), `layer-trans` (`:183`), `Lset` and its `opaque` seal
  (`:222`), and `Lset-layer` (`:246`). **These four are the probe's whole
  mathematical content.**
- `src/V/Coding.lagda.md`, read `:28-90` and `:120-180`. TOOK `pr`
  (`:175-176`) and the import list the probe copies (`:38-55`).
- `src/V/Hierarchy.lagda.md`, read `:20-50`, `:70-95`, `:155`. TOOK `𝒮ᵥ`'s
  membership field (`:78-84`) and `∈-irrefl` (`:155`), which is probe B's
  whole content.
- `src/L/BoundedSubset.lagda.md`, read `:60-160`. TOOK `LevelHood`
  (`:74-146`) and the comment that names `K` as the bound of the bounded
  existential (`:69-73`).
- `src/FOL/ZFStructure.lagda.md`, read `:37-100` and `:149`. TOOK that
  `𝒮ʟ`'s membership is `λ a b → fst a ∈ˢ fst b` (`:149`), which is why my
  V-level statement IS the frame's statement.
- **`dev/LESSONS.md`**: D-1, P-l, P-i, C-12, D-10, C-22, R-40 loaded through
  `scripts/rules.py --for probe` and read. C-33, C-38, C-36, C-39, C-40 read
  through `[LJ-1.146]` and `[LJ-1.113]`'s citations at `file:line`.
- **`AGENTS.md`, read WHOLE and fresh**, as the brief ordered. **It changed
  today**: probes now live beside the report and are tracked, and `_build/`
  needs a declaration. My probes obey the first and touch nothing in
  `_build/` but the compiler's own `.agdai`.
- `archive/dev/`: **NOT read.** No archived record bears on whether a live
  closure fact closes at a concrete level.

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:240-262` and `:368-396`.**

**The brief's question, answered directly: the 25 closure facts are OURS, not
Devlin's. `levelIn` and `cover` are the opposite case.**

- `:245-256` is the requirement. Devlin binds every unbounded quantifier of
  the Def step by the concrete set `K(u)`, the finite sequences over the
  formula set, the variables and the members of `u`. The digest then says the
  argument "does not require them to have any particular shape, only that
  some bounded description with a bound inside the carrier exists".
  **So Devlin needs A bound. He does not need OUR 25 facts.**
- `:375`, row C2, classes the bounded Def-step matrix as **PER-TOWER
  content**, and names our side as "satisfaction bound K(u) or its coding
  analogue".
- **So the 25 are the coding analogue.** They exist because our machine
  describes the step with twelve clause rows, and each row's witness must be
  shown to stay inside the bound. **Devlin gets that from one sentence about
  `K(u)`'s construction. We get it fact by fact.**

**The contrast with `[LJ-1.146]`'s answer, which the brief asked me to draw.**
`[LJ-1.146]` found `levelIn` and `cover` are Devlin's own two inclusions
(`agents/tasks/LJ-1-146/lj-1.146-report.md:542-573`). **The 25 are not. They
are ours, like the twelve rows `[LJ-1.144]` measured.** The statements at the
top of the chain are his; the bill at the bottom is ours.

**One qualification, and it matters for the price.** The MATHEMATICS of my
one fact is Devlin's and it is trivial for him: a level is transitive, so a
component of a pair inside it is inside it. **My 21 lines are the cost of
saying that on our encoding, not the cost of the mathematics.** That is why
the number is small, and it is the strongest reason to expect shape one to
stay cheap.

`_build/literature/dev2.txt`: **NOT opened.** Every citation above is through
the digest.

`dev/literature/devlin-errata.md`: **NOT read.** `[LJ-1.136]` measured that
the errata touch no part of II.5, taken through
`agents/tasks/LJ-1-146/lj-1.146-report.md:735-738`.
