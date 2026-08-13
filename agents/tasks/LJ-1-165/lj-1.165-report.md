# LJ-1.165 report: BUILD the crossing face, close `levelIn` and `cover`

tier: opus (version `override`). **The master is byte-identical to HEAD. Two
probes were written and both run GREEN. No commit, no push.** Every negative is
marked **MEASURED** or **INFERRED**. Written incrementally (C-22).

## 0. THE CRITERIA, FIXED BEFORE ANY RUN (D-1, DD8)

### 0.1 The wall-clock criterion, written before the first `agda` invocation

**20 minutes of wall time per `agda` invocation**, under `GHCRTS="-A64m -I0 -M8g"`,
**ONE** agda process. Past 20 minutes I record a **WALL** with its wall clock and
its resident set, I revert the walling term, and I keep the rest of the tree
green. **I never raise the cap.** I never move a line criterion after I see a
clock.

`[LJ-1.161]` measured a wall at this exact cluster at 20 minutes and 9.03 GB.
`[LJ-1.163]` measured a second at 20:42.15 and 2074 MB. `AGENTS.md` records a
cold whole-tree typecheck at about twelve minutes, so a single declaration that
outruns the whole tree has already answered.

### 0.2 The line criteria, which are the brief's and which I do not move

| piece | gated | abort at (+50 percent) |
|---|---:|---:|
| `levelIn` and `cover` from the face | 16 | 24 |
| `CrossOut` leg 1, the transfer | 20 | 30 |
| leg 2, the moved formula means the delivered one | 18 | 27 |
| leg 3, the identification | 125 | 188 |
| **`CrossOut` total** | **163** | **245** |

### 0.3 The named stop, which the brief fixed in advance

`[LJ-1.162]` MEASURED that leg 3's backward direction needs the definable power
of the recorded value to be IN `K`, that `𝒟ₒ` occurs ZERO times across
`Condensation` and the three `*Agree` masters, and that `KFacts` has no such
field. **If I reach it and cannot pay it, I stop and say so.**

## 1. VERDICT

### 1.1 The two answers the brief asked me to lead with

**`levelIn` and `cover` are NOT DISCHARGED. `theorem` does not derive
unconditionally. I STOP.**

**The stop is the brief's own third criterion, and it is WIDER than the brief
expected.** `[LJ-1.162]` named ONE unsupplied obligation, the definable power of
the recorded value in `K`. **MEASURED: it is not one obligation. It is the whole
K-adequacy layer, and the same absence blocks `HasLevels` and `Covered` as
well.** Section 3.

### 1.2 What DID land, and it is not nothing

1. **The assembly LANDS at the master.** `module Crossing` derives BOTH
   hypotheses from one crossing face, **17 in-fence lines against the gated 16**,
   master exit 0 in 15.79 s, RSS 1.89 GB. Section 2.1.
2. **`[LJ-1.161]`'s block-3 WALL is CURED and its diagnosis is refuted.**
   171 s of heap exhaustion becomes **4 s** under P-i repair **[F]**, one line.
   Section 1A.
3. **A SECOND wall, at a different term, is measured and NOT cured.** Section 5.

### 1.3 The one sentence a reader must carry

**Six dispatches gated the DERIVATIONS of `CrossOut`, `HasLevels` and `Covered`.
None gated their SUPPLIES.** Every leg is a function from site facts to a
conclusion; **MEASURED: nothing in `src/` supplies a single one of those site
facts, and nothing in `src/` proves that any set at all satisfies the bounded
graph.** The brief's "every piece has been gated and every gate is green" is
true of the legs and **MEASURED FALSE of the supply**.

## 1A. THE `[LJ-1.161]` WALL: BISECTED, DIAGNOSED, CURED

`[LJ-1.161]` recorded 20 min 0 s and 9.03 GB with NO heap exhaustion, and
marked its cause **INFERRED**: `refl : countFo LH.levelHoodΣ₁ ≡ 0`. **P-l says
re-measure, and re-measuring refutes the inference.**

`agents/tasks/LJ-1-165/ProbeLJ1165B.agda`, one declaration added per run, one agda
process, `GHCRTS="-A64m -I0 -M8g"`, cap never raised:

| step | term | result |
|---|---|---|
| a | `refl : countFo LH.levelHoodΣ₁ ≡ 0` | **exit 0, 4 s** |
| b | `eF = Cnt.erase LH.levelHoodΣ₁ cnt` | exit 0, 4 s |
| c | `eS = erase-Σ₁ LH.levelHoodΣ₁ cnt LH.Σ₁-levelHood` | exit 0, 6 s |
| d1 | `at = embed eF`, at an arbitrary transitive carrier | exit 0, 6 s |
| **d2** | **`atS = mapΣ₁ Empty.rec* eS`** | **HEAP EXHAUSTED, 171 s, 8 GB** |
| **d3** | **the same with `{φ = eF}` given** | **exit 0, 4 s** |

**MEASURED: step a costs 4 seconds.** `[LJ-1.161]`'s INFERRED cause is
**MEASURED FALSE**. One copy of the twelve-row table also costs 4 s:
`agents/tasks/LJ-1-165/ProbeLJ1165A.agda`, `cnt-DefBodyB`.

**The cause is P-i class [F], verbatim.** `mapΣ₁` (`[LJ-1.161]`'s own four-line
lemma) carries `{φ : Formula K n}` implicitly, and it is applied at a concrete
huge formula. P-i: "a lemma with an implicit formula or code index applied at a
concrete huge argument must get the index explicitly; a left metavariable makes
the unifier normalize the huge instance under a type-level FUNCTION head, which
is not invertible." **I selected the cure from the decision tree and ran no
trial before it.**

**Consequence for the price, stated exactly.** `[LJ-1.161]` reported the whole
transfer at the LEVEL-HOOD certificate unreachable in one process. **MEASURED:
three of its four steps are reachable, and the fourth still walls.** Section 5.2.
**Nobody should carry "the level-hood transfer walls" without carrying which
step, because one of the two walls costs one line and the other does not.**

## 2. EACH PIECE AGAINST ITS GATED FIGURE

### 2.1 The assembly: GO, 17 against 16

`src/L/BoundedSubset.lagda.md`, `module Crossing` inside `HullStage`, placed
between `module C = Collapse M` and `module Condense`.

| part | in-fence lines |
|---|---:|
| the face, three hypotheses plus the module header | 11 |
| `levelIn` | 6 |
| `cover` | 11 |
| **the two derivations** | **17** |
| gated by `[LJ-1.160]` | 16 |

**+6 percent, far inside the +50 percent abort.** The one extra line is `cover`'s
`go` type: at the master the collapse map is `C.π`, not the probe's `pi`, so the
payload type needs three lines where the probe used two. **P-l: I re-measured at
the master rather than carrying the probe's 16.**

**Master verdict: exit 0, 15.79 s wall, RSS 1.89 GB, no heap exhaustion.**
`check-unbound-hyp.py` stayed at **2**, so the face's three hypotheses did not
add to that count.

### 2.2 `CrossOut` leg 1, the transfer, AT THE REAL CERTIFICATE

`[LJ-1.161]` gated leg 1 at **20 lines** for `Σ₁-cert`, and reported that the
certificate `CrossOut` actually consumes, `LevelHood.Σ₁-levelHood`, **could not
be fed to it in one process**.

**MEASURED, and I split the claim carefully because leg 1 is NOT complete.**

| leg 1, step by step, at the LEVEL-HOOD certificate | state |
|---|---|
| the Levy witness reaches the parameter-free axis (`erase-Σ₁`) | **GREEN, 6 s** |
| the formula reaches the image's carrier (`embed`) | **GREEN, 6 s** |
| the Levy witness reaches the image's carrier (`mapΣ₁`) | **GREEN, 4 s, after the cure.** Was heap exhaustion at 171 s |
| **the transfer itself (`σ₁-up`)** | **WALL. 20 min 1 s, 9.40 GB, SIGTERM** |

**So leg 1 is three quarters green and its last step walls.** `[LJ-1.161]`
reported the whole of it unreachable in one process; **MEASURED: only the last
step is, and the cure for the step before it is one line.**

**Line count for the GREEN part: 26 in-fence lines**
(`agents/tasks/LJ-1-165/ProbeLJ1165B.agda`, 29 less the 3-line site module),
against `[LJ-1.161]`'s 20 for the same machine at `Σ₁-cert`. **+30 percent,
inside the +50 percent abort.** The extra lines are the explicit `{n}` and `{φ}`
indices that the cure requires and the named `eF`, `eS`, `at`, `atS` that P-i
[F] needs in order to have an index to give. **I give the walling step no line
figure.**

### 2.3 Legs 2 and 3: NOT REACHED, and I say why rather than guess

**I did not write leg 2 or leg 3 at the master.** Leg 3's site facts have no
supplier (section 3), so writing it would have added a module of hypotheses that
nothing discharges. **C-38 as extended forbids exactly that, and the brief names
it as this wing's measured failure mode.** I give leg 2 and leg 3 no new figure;
`[LJ-1.161]`'s 18 and `[LJ-1.162]`'s 125 stand, both measured at probe sites.

## 3. THE STOP: THE K-ADEQUACY LAYER HAS NO SUPPLIER

### 3.1 The obligation the brief named, re-MEASURED at this task's date

`𝒟ₒ` occurrences, by `grep -c`:

| file | count |
|---|---:|
| `src/L/Condensation.lagda.md` | **0** |
| `src/L/Condensation/LowerAgree.lagda.md` | **0** |
| `src/L/Condensation/UpperAgree.lagda.md` | **0** |
| `src/L/Condensation/TwelveAgree.lagda.md` | **0** |

`KFacts` (`src/L/Condensation.lagda.md:5996-6033`) has twelve tag equations,
twelve numeral memberships, and five closure fields: `innerK`, `innerPairK`,
`pairK`, `carrierK`, `arityK`. **None bounds a definable power.** `[LJ-1.162]`'s
measurement holds unchanged.

### 3.2 The finding that WIDENS the brief's stop, and it is the return

**`powK` is not one missing fact. It is one of seven, and they are one thing.**
`agents/tasks/LJ-1-162/ProbeLJ1162A.agda` states leg 3's telescope; every
K-membership hypothesis in it is an ADEQUACY condition on the bound `K`:

| hypothesis | `ProbeLJ1162A.agda` | what it asserts | supplier |
|---|---|---|---|
| `envK` | `:91-92` | the leaf's environment lies in `K` | **NONE** |
| `codeK` | `:93-94` | the leaf's code lies in `K` | **NONE** |
| `memK` | `:95-96` | the leaf's satisfier lies in `K` | **NONE** |
| `valK` | `:138-139` | the recorded value lies in `K` | **NONE** |
| **`powK`** | `:140-141` | **the definable power of the recorded value lies in `K`** | **NONE** |
| `stepK` | `:142-143` | the step's satisfier lies in `K` | **NONE** |
| `entryK` | `:197-198` | the approximation's entry pair lies in `K` | **NONE** |

**MEASURED, and this is the sharper statement: `KFacts` is never CONSTRUCTED
anywhere in `src/`.** `grep -rn "KFacts" src/` returns the record declaration
(`:5996`), `open KFacts` (`:6034`), one lifting lemma (`:6041-6042`), five module
hypotheses (`:6080`, `:6363`, `:6462`, `:6488`, `:6755`, `:7015`), one `lift3`
(`:6809`) and two comments. **No `record { ... }` and no field-wise value. The
whole site-fact layer is hypothetical.**

**MEASURED: `LeafAgree` and `DomainAgree` have no consumer outside their own
master.** `grep -rn "LeafAgree\|DomainAgree" src/` outside
`src/L/Condensation.lagda.md` returns nothing. `[LJ-1.162]` consumed their two
directions through hypotheses of the same SHAPE; nothing consumes the delivered
objects.

### 3.3 The same absence blocks `HasLevels` and `Covered`, which nobody gated

**This is the part no gate looked at, and it is the largest.**

`HasLevels` and `Covered` produce a BELIEF. `[LJ-1.161]` section 3.2 measured
that their transport machine is delivered (`IsoInv.iso-inv`,
`src/L/BoundedSubset.lagda.md:195-196` and `:250-251`) and section 3.3 named the
remaining term as `ElemDown`. **MEASURED: that reading is incomplete.**
`ElemDown` reflects a satisfaction DOWN from the stage `Lset λ` into the hull.
**Something must first prove that `Lset λ` satisfies the level-hood statement,
and nothing does.**

**MEASURED, by `grep -rn "graphBndAt" src/`: `GraphB.graphBndAt` has exactly ONE
consumer in the whole tree, `LevelHood.levelHoodB`
(`src/L/BoundedSubset.lagda.md:111`), and that consumer only STATES it.** No
declaration anywhere in `src/` concludes `⟨ γ ⊨ GraphB.graphBndAt ... ⟩` for any
`γ`. The same holds for `approxBndAt` and `stepBndAt`.

**And the master says so itself.** `src/L/BoundedSubset.lagda.md:899-902`: "the
level-hood instantiation at the hull is the priced residue". **That residue is
still unbuilt, and `HasLevels` and `Covered` cannot be supplied without it.**

**MEASURED (C-35): `LevelHood0` at `src/L/BoundedSubset.lagda.md:840-869` has NO
consumer.** Its `matrix` (`:849`), `Σ₂` (`:856`), `Σ₁-Σ₂` (`:859`) and `reverse`
(`:865`) are named nowhere else in `src/`. **`Σ₂` is exactly the statement
`HasLevels` needs, and it is the fifth delivered definition in this wing with no
consumer.** `[LJ-1.151]` found the first, `[LJ-1.161]` three more, `[LJ-1.163]` a
fourth. **I did not add a sixth, and section 6 says what I removed to keep that
true.**

### 3.4 Why the two absences are ONE thing, marked INFERRED

**MEASURED:** the delivered `levelHoodB` (`src/L/BoundedSubset.lagda.md:108-111`)
leaves `K` a free variable and states no closure property of it. Its bounded
step, `StepB.witB` (`src/L/Condensation.lagda.md:2407-2412`), bounds the recorded
value and its definable power by `K`; its bounded extension frame,
`extAtB` (`:100-102`), says "every satisfier lies in `K`" rather than "every
satisfier lies in `v`".

**INFERRED, and I mark it because I did not build the counterexample:** with a
`K` too small, `levelHoodB(w, v, γ, K)` can hold with `v` a proper subset of
`Lset γ`, because the frame's second half quantifies only over `K`. **So the
seven site facts are not incidental plumbing. They are the adequacy of `K`, they
are what makes the sentence say what it means, and the same construction that
supplies them is the construction `HasLevels` needs.** Devlin's `K(u)`
(`dev/literature/devlin-II5.md:249-256`) is that construction.

**C-36 binds and I obey it. I do not claim `CrossOut` is false, and I do not
claim no supplier exists. I claim I found none, at the `file:line` above.**

## 4. CONSUMER VERDICTS (C-40)

**The consumer set is MEASURED, not assumed.** `grep -rn "L.BoundedSubset" src/`
outside the master returns one line, `src/Everything.lagda.md:374`.

**Every consumer typechecked, before and after the revert.**

| what | exit | wall | RSS |
|---|---|---|---|
| `src/L/BoundedSubset.lagda.md` WITH `Crossing` | **0** | 15.79 s | 1.89 GB |
| `src/L/BoundedSubset.lagda.md` after the revert | **0** | 16 s | |
| `src/Everything.lagda.md`, the ONLY importer | **0** | 4 s | |
| `agents/tasks/LJ-1-165/ProbeLJ1165A.agda` | **0** | 4 s | |
| `agents/tasks/LJ-1-165/ProbeLJ1165B.agda` | **0** | 6 s | |

**No heap exhaustion in any standing run.** The two heap and wall figures that
are NOT clean belong to the walling terms of section 5 and to nothing that
stands in the tree.

## 5. WALLS

**TWO walls, both measured under the criterion of section 0.1, one CURED and one
NOT.** One agda process throughout, `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised.**

### 5.1 WALL 1, CURED: `mapΣ₁` at the level-hood certificate

| figure | value |
|---|---|
| before the cure | **HEAP EXHAUSTED at 171 s**, 8 GB cap |
| after P-i **[F]**, `{φ = eF}` given | **exit 0, 4 s** |

**This is the wall `[LJ-1.161]` reported as 20 min and 9.03 GB with no heap
exhaustion. Its INFERRED cause, `countFo`, is MEASURED FALSE at 4 s.**

### 5.2 WALL 2, NOT CURED: `σ₁-up` at the level-hood certificate

| figure | value |
|---|---|
| wall time | **20 min 1 s**, then SIGTERM |
| resident set | **9.14 GB** |
| heap cap | `-M8g`. **NO heap exhaustion. Cap held, never raised** |

**MEASURED: 9.14 GB against `[LJ-1.161]`'s 9.03 GB, and the same 20-minute
SIGTERM with no heap exhaustion. It is the same wall, and its site is
`Abs.σ₁-up`, not `countFo`.**

**What it is, and I mark the split.** **MEASURED:** the wall is at `σ₁-up`
applied to the level-hood Levy witness. **INFERRED:** `σ₁-up (σ-Δ₀ d) δ =
subst ⟨_⟩ (abs₀ d δ)` (`src/FOL/Absoluteness.lagda.md:182-184`), and `abs₀`
builds a PATH by `cong₂` and `⇔toPath` at every node of the Δ₀ witness. The
level-hood matrix nests the twelve-row table through two `extAtB` frames, and
`extAtB y K φ` carries `φ` TWICE (`src/L/Condensation.lagda.md:100-102`,
measured generically at `ProbeLJ1165A.agda:cnt-extAtB`). **That is a path term
over an eight-fold copy of the table, and it is the cost the three `*Agree`
masters exist to split** (`src/L/Condensation/README.md:1-3`).

**P-i binds and I obeyed its first clause: no trial, no surgery.** I applied
repair **[F]** at `σ₁-up` too, because its `{φ}` is implicit as well. **It did
NOT cure this one: 20 min 1 s, 9.40 GB, SIGTERM.** Two runs, one with the index
and one without, and the criterion fired on both. **I did not raise the cap and I
did not re-approach the term.**

**What this wall does NOT say.** It does not say the level-hood certificate
cannot be transferred. **C-36 binds.** It says `σ₁-up` at that formula does not
finish in one process in 20 minutes, and that the delivered cure for exactly this
cost is the `*Agree` split. **I did not price that cure.**

## 6. WHAT I LEFT IN THE TREE, AND WHY THE MASTER IS UNCHANGED

**`src/L/BoundedSubset.lagda.md` is byte-identical to HEAD.** `git diff src/` is
empty. I wrote `module Crossing` into it, typechecked it green, measured it, and
then **removed it**.

**The reason is the brief's own rule and this wing's own history.** The face's
three hypotheses have no supplier (section 3). Leaving them in the master would
have added a **sixth** delivered statement with no consumer, after `[LJ-1.151]`'s
one, `[LJ-1.161]`'s three and `[LJ-1.163]`'s fourth, and after section 3.3 found
the fifth. **C-38 as extended says a hypothesis is discharged when something
SUPPLIES it. Nothing does.**

**Nothing is lost, because the code is here and it is measured.** Paste it
between `module C = Collapse M` (`src/L/BoundedSubset.lagda.md:914`) and
`module Condense` (`:916`):

```agda
  module Crossing
    (Bel : S → S → Type (ℓ-suc ℓ))
    (crossOut : (v b : S) → ⟨ v ∈ˢ C.πX ⟩ → ⟨ b ∈ˢ C.πX ⟩ → IsOrd b
              → Bel v b → v ≡ Lset b)
    (hasLevels : (b : S) → ⟨ b ∈ˢ C.πX ⟩ → IsOrd b
               → ∥ Σ[ v ∈ S ] (⟨ v ∈ˢ C.πX ⟩ × Bel v b) ∥₁)
    (covered : (x : S) → ⟨ x ∈ˢ C.πX ⟩
             → ∥ Σ[ b ∈ S ] Σ[ v ∈ S ]
                 (⟨ b ∈ˢ C.πX ⟩ × ⟨ v ∈ˢ C.πX ⟩ × IsOrd b × Bel v b
                  × ⟨ x ∈ˢ v ⟩) ∥₁)
    where

    levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ C.πX ⟩ → ⟨ Lset δ ∈ˢ C.πX ⟩
    levelIn δ oδ δ∈ = PT.rec (snd (Lset δ ∈ˢ C.πX)) go (hasLevels δ δ∈ oδ)
      where
      go : Σ[ v ∈ S ] (⟨ v ∈ˢ C.πX ⟩ × Bel v δ) → ⟨ Lset δ ∈ˢ C.πX ⟩
      go (v , (v∈ , bel)) =
        subst (λ w → ⟨ w ∈ˢ C.πX ⟩) (crossOut v δ v∈ δ∈ oδ bel) v∈

    cover : (y : S) → ⟨ y ∈ˢ M ⟩
          → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁
    cover y y∈M = PT.rec squash₁ go (covered (C.π y) (C.πX-intro y y∈M))
      where
      go : Σ[ b ∈ S ] Σ[ v ∈ S ]
             (⟨ b ∈ˢ C.πX ⟩ × ⟨ v ∈ˢ C.πX ⟩ × IsOrd b × Bel v b
              × ⟨ C.π y ∈ˢ v ⟩)
         → ∥ Σ[ γ ∈ S ] (IsOrd γ × ⟨ γ ∈ˢ C.πX ⟩ × ⟨ C.π y ∈ˢ Lset γ ⟩) ∥₁
      go (b , (v , (b∈ , (v∈ , (ob , (bel , y∈v)))))) =
        ∣ b , (ob , (b∈ ,
          subst (λ w → ⟨ C.π y ∈ˢ w ⟩) (crossOut v b v∈ b∈ ob bel) y∈v)) ∣₁
```

**It needs no new import and no new name.** `PT.rec`, `squash₁`, `∣_∣₁`, `subst`,
`C.πX-intro` and `Lset` are all already in scope at that point. **Master exit 0,
15.79 s, RSS 1.89 GB, `check-unbound-hyp.py` unchanged at 2.**

**My files are only:** `agents/tasks/LJ-1-165/lj-1.165-report.md`,
`agents/tasks/LJ-1-165/ProbeLJ1165A.agda`,
`agents/tasks/LJ-1-165/ProbeLJ1165B.agda`. Both probes are tracked-in-place,
beside the report, and they ran while my task was live.

## 7. DD4

**Maximize the code the two proofs share, and write it generic.**

### 7.1 The answer in one line

**26 of the 28 in-fence lines of the assembly are TEMPLATE. TWO name a tower.**

| part | lines | class | why |
|---|---:|---|---|
| the face's three hypotheses and the module header | 11 | **TEMPLATE** | `Bel : S → S → Type` is a parameter and nothing inspects it. The only tower token is `Lset` in `crossOut`'s conclusion |
| `levelIn` | 6 | **TEMPLATE but for one token** | one `PT.rec`, one `subst`. `Lset` appears in the type only |
| `cover` | 11 | **TEMPLATE but for one token** | one `PT.rec`, one `subst`, `C.πX-intro`. `Lset` appears in the type only |

**MEASURED by reading the block: `Lset` appears in 3 lines of 28, `Def` in 0,
`𝒟ₒ` in 0, and no rud name anywhere.** Counting DECLARATIONS rather than
occurrences, two of the five carry a tower name.

**Where the fork point sits, and it did not move.** `[LJ-1.163]` measured it at
ONE line, `src/L/BoundedSubset.lagda.md:670`. The assembly sits at `:914`, far
below, and I changed nothing above `:914`. **A J tower supplies its own `Bel`,
its own `crossOut`, `hasLevels` and `covered`, and takes `levelIn` and `cover`
out unchanged.**

**This is the fourth site this phase where the generic form was the SHORT form.**
`[LJ-1.151]` 19 of 21, `[LJ-1.160]` 73 percent, `[LJ-1.161]` 16 of 20,
`[LJ-1.162]` 103 of 134. **No stop-line pushed me toward writing fixed.**

### 7.2 The limit, so nobody over-reads it

**The SUPPLY is per-tower content and this measurement does not touch it.** The
face is generic; the level-hood certificate that would fill it is row C1 of the
literature's own table, PER-TOWER (`dev/literature/devlin-II5.md:375`). **What
DD4 buys here is that the assembly is written once. It buys nothing on the term
that is actually missing.**

### 7.3 One DD4 finding on the wall, and it is reusable

**P-i repair [F] is tower-blind.** `mapΣ₁`, `σ₁-up` and `mapΔ₀` are all in
`FOL/`, they carry an implicit formula index, and they will be applied at a huge
formula by BOTH towers. **The cure is one line at each call site and it belongs
in the shared half.** Section 8 marks the second wall's cure as unpriced.

## 8. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| `levelIn` and `cover` are discharged | **MEASURED FALSE.** The face's three hypotheses have no supplier |
| `theorem` derives unconditionally | **MEASURED FALSE.** It still needs `Co` applied to the undischarged pair |
| the assembly closes both hypotheses from one face | **MEASURED TRUE.** Master exit 0, 17 in-fence lines against the gated 16 |
| the assembly exceeds its gated figure by 50 percent | **MEASURED FALSE.** 17 against 16, +6 percent |
| `refl : countFo LH.levelHoodΣ₁ ≡ 0` walls | **MEASURED FALSE. 4 seconds.** `[LJ-1.161]` marked this INFERRED and it is wrong |
| one copy of the twelve-row table walls `countFo` | **MEASURED FALSE. 4 seconds.** `ProbeLJ1165A.agda` |
| `mapΣ₁` at the level-hood certificate is reachable | **MEASURED TRUE, after the cure.** Heap exhaustion at 171 s becomes exit 0 at 4 s with `{φ}` given |
| P-i repair [F] cures the `mapΣ₁` wall | **MEASURED TRUE.** One line |
| P-i repair [F] cures the `σ₁-up` wall | **MEASURED FALSE.** 20 min 1 s and 9.40 GB with the index, 9.14 GB without |
| the `σ₁-up` wall is a new kind of obstruction | **MEASURED FALSE.** Same shape as `[LJ-1.161]`'s: 20 minutes, about 9 GB, SIGTERM, no heap exhaustion |
| the level-hood certificate cannot be transferred at all | **NOT CLAIMED. C-36.** One process in 20 minutes does not finish it |
| the tree supplies `𝒟ₒ w ∈ K` | **MEASURED FALSE.** `𝒟ₒ` occurs 0 times in `Condensation` and all three `*Agree` masters |
| `powK` is the ONLY unsupplied site fact | **MEASURED FALSE.** Seven of them, all K-adequacy, none supplied. Section 3.2 |
| `KFacts` is constructed anywhere in `src/` | **MEASURED FALSE.** Declaration, `open`, one lift, six module hypotheses, two comments. No value |
| `LeafAgree` or `DomainAgree` has a consumer outside its master | **MEASURED FALSE** |
| anything in `src/` proves a satisfaction of the bounded graph | **MEASURED FALSE.** `graphBndAt` has ONE consumer, `LevelHood.levelHoodB`, and it only states it |
| `HasLevels` and `Covered` need only `ElemDown` and `iso-inv` | **MEASURED FALSE.** They also need the stage to SATISFY level-hood, which nothing proves. This corrects `[LJ-1.161]` section 3.3 |
| `LevelHood0` has a consumer | **MEASURED FALSE.** `matrix`, `Σ₂`, `Σ₁-Σ₂` and `reverse` are named nowhere else. C-35, and it is the fifth in this wing |
| `CrossOut` is false as stated for the delivered `levelHoodB` | **INFERRED, NOT CLAIMED.** Section 3.4 gives the mechanism and says I built no counterexample. C-36 |
| the seven site facts are incidental plumbing | **INFERRED FALSE.** They are the adequacy of `K`. Section 3.4 |
| a cheaper route to the belief exists | **NOT CLAIMED. C-36.** I measured one route |
| the six gates are wrong | **NOT CLAIMED.** Every gated figure held or moved by less than 50 percent. What the gates did not cover is the SUPPLY, and section 1.3 says so |

## 9. CHECKERS AND GATES

| checker | result |
|---|---|
| `scripts/lint-agda.py --check` | **exit 0**, tree and both probes |
| `scripts/lint-prose.py --check` on this report | **exit 0** |
| `scripts/check-probes.py --check` | **clean, 1,775 tracked files** |
| `scripts/check-unbound-hyp.py` | **2**, both the known false positives at `src/L/Reflect.lagda.md:365` and `src/L/StageCardinal.lagda.md:281`. **Unchanged, and it stayed at 2 while `Crossing` was in the master** |
| `scripts/ledger.py --brief` | standing **28,940 lines over 85 masters**, from HEAD; thresholds SUSPENDED per the ledger header; endpoint REFUSED |
| `make check` | **NOT RUN.** The orchestrator runs it |

**Prohibitions, answered.** `src/Everything.lagda.md` never edited.
`src/L/Coding/Graph.lagda.md` never opened. The three `*Agree` masters read at
their `README.md` and by `grep` only, never edited. `[LJ-1.164]`'s move NOT
undone: `elem-down` is still at `src/L/BoundedSubset.lagda.md:1551`. **No
commit, no push, no `git checkout .`, no `stash`, no `reset`, no `clean`.** No
probe under `src/`. **No `postulate`, no hole, no unsolved meta in either
probe**, and `--safe` is on in both.

**C-12.** ONE agda process throughout, `GHCRTS="-A64m -I0 -M8g"`, **cap NEVER
raised**. The machine carried one user; load averages 6.0 to 7.4 at the start.
**My line figures are lines, so a busy machine costs me time only. My two wall
figures are seconds, and I report the load beside them: both walls hit the same
20-minute criterion and the same 9 GB resident set that `[LJ-1.161]` measured on
a quieter machine, so the load does not explain them.**

## 10. WHAT THE NEXT BRIEF SHOULD FUND, WITH ITS GATE

**Offered, not assumed.** The phase's block is ONE object, not three:

> **Devlin's `K(u)`: construct the bound inside `Lset λ` and prove the bounded
> level-hood statement at it.** `dev/literature/devlin-II5.md:249-256` is the
> construction. It supplies the seven site facts of section 3.2 AND the belief
> that `HasLevels` and `Covered` need, because both are the same adequacy.

**Its gate, stated as an obligation with the criterion in advance:** construct
`K` and supply **`powK`** alone, at `LevelHood`'s own slots. **GO if `powK`
lands; NO-GO if the construction needs a closure of `K` under `𝒟ₒ` that the
stage does not give.** That single fact is the narrowest decisive term, because
`[LJ-1.162]` measured it as the one with no supplier and section 3.2 measures
that the other six are the same kind.

**And the second gate, independent of the first:** `σ₁-up` at the level-hood
certificate, split the way `src/L/Condensation/README.md:1-3` splits the twelve
rows. **GO if the split brings it under 20 minutes in one process.** Nobody has
priced this and I do not price it.

## 11. ARCHIVE USED (DD18)

- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:160-257`**, the
  crossing face and `module Assembly`. **TOOK the SHAPE of `CrossOut`
  (`:168-170`), `HasLevels` (`:173-175`) and `Covered` (`:177-180`), and the
  shape of `level-in` (`:240-247`) and `M⊆L` (`:249-257`).** Section 6's code is
  that shape restated at the current route's own two types. **I took no claim:
  `[LJ-1.11]` ruled that route's condensation target classically FALSE, and
  `[LJ-1.162]` measured that the archive STATES `CrossOut` at nine places and
  proves it nowhere. This task confirms the second half from the other side: the
  current tree cannot prove it either, for a reason the archive never met.**
- **`archive/src/2026-08-09-rud-route/L/Hull.lagda.md:248-249`, `:396-398`**,
  the BUILT Tarski-Vaught theorem and `hull-closed`. **READ, and NOT used.**
  `[LJ-1.164]` measured that the archive's elementarity carries no condensation
  parameter and that the live tree agrees at `src/L/Hull.lagda.md:163` and
  `:313`. **My block is below both, so the archive's placement bears on nothing
  I wrote. I say so rather than list a row I did not spend.**
- `agents/tasks/LJ-1-160/lj-1.160-report.md`, **READ WHOLE.** TOOK the 16-line
  re-route (`:196-201`), the three open facts (`:266-279`), the mechanism
  (`:246-252`) and the DD4 split (`:383-390`).
- `agents/tasks/LJ-1-160/ProbeLJ1160A.agda`, **READ WHOLE.** Section 6's code is
  its `Reroute` at the master's own names.
- `agents/tasks/LJ-1-161/lj-1.161-report.md`, **READ WHOLE.** TOOK the 20-line
  gate (`:28-36`), the counterweight (`:76-87`), the three legs (`:180-186`),
  **the block-3 wall and its INFERRED cause (`:378-410`), which section 1A
  refutes**, and section 3.3's reading of `HasLevels` and `Covered`
  (`:276-283`), **which section 3.3 of this report corrects.**
- `agents/tasks/LJ-1-161/ProbeLJ1161A.agda`, **READ WHOLE.** TOOK `mapΣ₁` and
  `erase-Σ₁` (`:62-72`) verbatim, and its commented block 3 (`:174-185`), which
  is the term probe B bisects.
- `agents/tasks/LJ-1-162/lj-1.162-report.md`, **READ WHOLE.** TOOK the 125-line
  leg (`:59-66`), the four frames (`:131-138`), **the unsupplied obligation
  (`:140-172`), which section 3 re-measures and widens**, and the DD4 split
  (`:208-225`).
- `agents/tasks/LJ-1-162/ProbeLJ1162A.agda`, **READ WHOLE.** Section 3.2's table
  is its telescope, hypothesis by hypothesis, at `file:line`.
- `agents/tasks/LJ-1-164/lj-1.164-report.md`, **READ WHOLE.** TOOK the purity
  measurement (`:7-17`), the new location of `elem-down` (`:58`), and the
  reachability in both directions (`:154-194`). **`[LJ-1.164]`'s move is intact
  and I did not undo it.**
- `agents/tasks/LJ-1-164/ProbeLJ1164A.agda`, **READ WHOLE.** Its `Site` module
  is what tells me `theorem` needs only the discharged pair.
- `agents/tasks/LJ-1-163/lj-1.163-report.md`: **NOT read whole.** Taken through
  `[LJ-1.164]`'s report at `:228-242` (the fork point) and `:310-313` (its
  wall). **I mark this so nobody credits me with a reading I did not do.**
- `archive/dev/`: **NOT read.** No `D`-series ruling bears on a line count or on
  a heap figure.
- `dev/LESSONS.md`: **P-i read WHOLE**, and it is the law that produced this
  task's one cure. C-35, C-36, C-38, C-39, C-40, C-12, C-22, P-l read whole;
  D-10, D-26, D-29, D-30, C-31 to C-34, C-37, P-h, P-k, P-m, P-n, R-35, R-38,
  R-40, I-5 loaded through `scripts/rules.py --for build`.

## 12. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:88-125` and `:240-262`.**

- **`:95-96`, Devlin's step (a).** `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]`, with `Φ`
  a Σ₀ formula. **`[LJ-1.162]` MEASURED that this is stated at the BOUNDED
  matrix with only the outer existential unbounded, and that the delivered
  `Lset-only` is NOT his (a). I follow that reading and I did not re-open it.**
- **`:249-256` is the passage this task's finding rests on**, and it is the one
  the six gates did not spend:

  > 2.2 to 2.4 write the Def step as Σ₁, then bind every unbounded quantifier by
  > the concrete set K(u) ... The Σ₀ matrix C(w, v, u) with w = K(u) is the
  > bounded satisfaction substrate of Devlin's engine.

  **"the concrete set K(u)" is the term.** Devlin's matrix is bounded by a set he
  CONSTRUCTS, and the equivalence in (a) holds **because** `K(u)` is that set.
  **The delivered `levelHoodB` (`src/L/BoundedSubset.lagda.md:108-111`) leaves
  `K` a free variable and constructs nothing.** So the seven site facts of
  section 3.2 are not our encoding's overhead: **they are the content of
  "w = K(u)", and the literature says so in its own words.**
- `:374-382`, the per-step DD4 table. TOOK row C1 (level-hood formula,
  PER-TOWER) for section 7.2.

`_build/literature/dev2.txt`: **NOT opened.** Every citation is through the
digest. `dev/literature/devlin-errata.md`: **NOT read**, on `[LJ-1.136]`'s
measurement that the errata touch no part of II.5, taken through
`agents/tasks/LJ-1-160/lj-1.160-report.md:664-666`.

## 13. C-39: WHAT A PROHIBITION CLOSED, AND WHAT IT DID NOT

- **"Do not undo `[LJ-1.164]`'s move."** Correct, and it cost nothing.
  `elem-down` is still at `:1551`.
- **"Do not touch the three `*Agree` masters."** Correct, and it cost nothing.
  Reading their `README.md` is what named the split cure for wall 2, and
  `grep` over them is what measured `𝒟ₒ` at zero.
- **"Never raise the cap."** Correct, and it is what produced the finding.
  A raised cap would have let wall 1 finish slowly and I would have reported a
  slow build instead of a one-line cure.
- **"A stop is a deliverable."** This changed how I worked. **I looked for the
  supply before I wrote the legs**, and that is why section 3 exists instead of
  a partially-built leg 3 resting on seven hypotheses.

**The one line I would add to the next brief, offered and not assumed.**

**The brief says "Six dispatches have gated every piece and every gate is
green." MEASURED: the six gates priced the DERIVATIONS. None of them priced a
SUPPLY, and each said so in its own return** — `[LJ-1.160]` at `:216-218`
("It does not buy a supply"), `[LJ-1.161]` at `:334` ("It supplies one leg of
three"), `[LJ-1.162]` at `:318` ("52 lines stated, NOT discharged").
**A brief that reads six green gates as a fundable build should say which gate
priced the supply. If none did, the build is not gated, and that is what this
return found.**


