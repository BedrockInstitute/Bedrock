# LJ-1.246 report: DD25 review of `[LJ-1.244]`

tier: opus (deepseek-subagent-mode), the switch's ADVERSARIAL row. The target
was written by pi, so the critic is not the author. No Agda ran: a sibling held
the slot. No master, brief or report was edited. No commit, no push. No
`make check`. Written incrementally (C-22). Every negative is MEASURED or
INFERRED, in those words.

## VERDICT

**UPHELD BUT MISATTRIBUTED.**

`[LJ-1.244]` is right that `q'` is unbuilt and that the phase faces real work.
It is wrong about three things: the probe that produced the negative measures a
statement that is false for a reason unrelated to the bridge; the blocking terms
it names are delivered in `src/` and are one level below the gap; and the gap
itself is already decomposed and half proved in a green archived probe that the
target did not open.

**For the owner, one sentence.** `[LJ-1.7]` costs two named lemmas,
`StepAgree` and `ApproxAgree`, plus a carrier port, and not the 970 to 1,264
line class-carrier bridge that the record now says; the choice is to fund a
one-file port probe (about 90 lines, a comparable at 1.95 s) before any chapter
is priced, or to fund the chapter blind.

## Q1. IS THE STUCK GOAL REALLY STUCK?

**NO, in the sense that matters. The stuck goal carries no information about the
bridge. MEASURED, from the probe's own telescope.**

### 1.1 The probe left both sides abstract

`agents/tasks/LJ-1-244/ProbeLJ1244B.agda:42-69` opens `module Attempt`. In that
telescope `Graph` is a parameter at `:45` and `φ₀` is a parameter at `:68`.

**`φ₀` occurs in no hypothesis of that telescope.** It occurs only inside the
statement of `q'` itself, at `:73`. MEASURED, by reading `:42` to `:75` whole.
Nothing relates `φ₀` to `Graph`, to `Step`, or to `Approx`.

So the goal at `ProbeLJ1244B.agda:75` is the goal of a universally quantified
statement over two unrelated formula families. C-36 is exact here: the elaborator
reports that it cannot connect two abstract families, and that is all it reports.

### 1.2 The statement in the probe is not merely unproven. It is refutable

Take `Step`, `Approx` and `Graph` all equal to `⊥̇`, and `φ₀` equal to `⊤̇`.

Each of the six readings has `⟨ A.ambient γ (Step ...) ⟩`,
`⟨ A.ambient γ (Approx ...) ⟩` or `⟨ A.ambient γ (Graph ...) ⟩` in its premise
(`ProbeLJ1244B.agda:46-67`). `ambient γ φ = (map fst γ) R.Abs.⊨ᵛ φ`
(`agents/tasks/LJ-1-184/ProbeLJ1184A.agda:326-327`), so each premise is empty
and each reading holds by absurdity.

`embed ⊤̇` is `⊤̇`, because `embed = mapFo Empty.rec*` and `mapFo f ⊤̇ = ⊤̇`
(`src/FOL/Manipulation/Relabelling.lagda.md:117-118`, `:62`). So `q'` would give
an inhabitant of an empty type from an inhabited one.

**MEASURED** that the telescope permits this instantiation, by reading it.
**INFERRED** that Agda accepts it, because I did not run Agda.

**Consequence.** Exit 42 at `ProbeLJ1244B.agda:75` prices a false target. D-10
is the rule: price the truth of a target before pricing its proof. The target's
own section 2 applies C-45 to `q`, and the target's probe B then repeats C-45's
failure at one level up. It audited a telescope, not an instantiation.

### 1.3 A term exists, and it is green

**`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:70-88` defines
`graph-assembly`, and `[LJ-1.52]` records the probe as green** at 1.95 s mean
over three runs (`agents/tasks/archive/LJ-1-52/lj-1.52-report.md:94`).

Its type at `ProbeLJ152B.agda:70-74`: from `StepAgree` and `ApproxAgree`, at a
five slot environment, `graphBndAt` implies `LsetGraphAt`. Its body at `:75-88`
is proved, not assumed. It closes with `LsetGraph-in`.

`graphBndAt` is the bounded graph of the BS coding
(`src/L/Condensation.lagda.md:2489-2490`), and it is the body of `levelHoodB`
(`src/L/BoundedSubset.lagda.md:108-111`), which is the content of `φ₀`
(`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:102-103`, `:145-146`).

**So the direction `q'` needs, BS to At, is already assembled. MEASURED.**

The companion probe closes the rest of the chain.
`agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda:58-73` defines `matrix-decode`:
from the level hood matrix and `GraphAgree`, it gives `fst w ≡ Lset (fst γ)`.
**That is the conclusion of `go`** at `agents/tasks/LJ-1-184/ProbeLJ1184B.agda:118-120`.

**What is left is exactly two named hypotheses**, `StepAgree`
(`ProbeLJ152B.agda:53-58`) and `ApproxAgree` (`ProbeLJ152B.agda:60-64`).

### 1.4 What survives of the target's negative

`q'` is still unbuilt. **MEASURED**, because `StepAgree` and `ApproxAgree` are
hypotheses in the only file that states them, and no module supplies them.

The chain is at the CLASS carrier. `ProbeLJ152B.agda:35` reads
`open hPropStructure 𝒮ʟ` and `:37` reads
`FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans`. **So the target's sentence "none of
it is ported to the ambient carrier" is TRUE. MEASURED.**

## Q2. IS THE BLOCKING TERM CORRECTLY NAMED?

**NO. The three named terms are delivered, and they are one level below the gap.
MEASURED, at the source.**

### 2.1 The three citations, re-derived

The target writes them at `agents/tasks/LJ-1-244/lj-1.244-report.md:77-81`.

| target's citation | what is there |
|---|---|
| `TagAgree` at `:6617-6654` | `:6617-6623` is a comment banner. The module is `src/L/Condensation.lagda.md:6628-6655`. The cited range stops one line short of `back`'s last line |
| `SatGraphB` against `satGraphAt` at `:6795-7045` | `SatGraphB` is the FORMULA module at `src/L/Condensation.lagda.md:2230`. The TRANSFER is `SatGraphAgree` at `:6802-7054`. The cited range truncates `back` (`:7045-7054`) |
| `isCodeBS` against `isCodeAt` at `:7170-7179` | **No complete declaration lies in that range.** `ic-out` is `:7169-7177` and `ic-back` is `:7179-7187`, both inside `module LeafAgree` (`:7065-7200`). `isCodeBS` is defined at `:1733` and `isCodeAt` at `src/L/Coding/Powerset.lagda.md:297` |

**All three are delivered and both directional. MEASURED.** `TagAgree.out` is at
`:6632` and `TagAgree.back` at `:6643`.

### 2.2 The gap is one level up, and the source names it

`src/L/Condensation.lagda.md:5433-5434` reads: "the consumers of the leaf
adequacy (`[LJ-1.52]` StepAgree/ApproxAgree/GraphAgree and the Adeq decode)".

**No module of those three names exists.** `grep` over `src/`, `agents/tasks/`
and `archive/` returns that comment line, one archived copy of the same file,
and the two hypothesis statements in `ProbeLJ152B.agda`. **MEASURED.**

**So the delivered `Agree` family covers the LEAF row.** `TagAgree`, `KeyAgree`,
`EnvOneAgree`, `DefinesAgree`, `SatGraphAgree`, `ClosedAgree`, `DomainAgree`,
`ShapedAgree`, `WitnessAgree` and `LeafAgree` sit at
`src/L/Condensation.lagda.md:6404` to `:7200`. **The missing row is
`StepAt`/`ApproxAt`/`LsetGraphAt` against
`stepBndAt`/`approxBndAt`/`graphBndAt`.**

### 2.3 The port check the brief asked for

`[LJ-1.238]` ported `L.Coding.Sequence`, not any part of the bridge.
`agents/tasks/LJ-1-238/GenSequence.agda:14-24` abstracts the module over
`(M : V ℓ → hProp (ℓ-suc ℓ))` and `(M-trans : Transitive (𝒮ᵥ {ℓ}) M)`.

**A qualifier the target does not carry.** `agents/tasks/LJ-1-238/lj-1.238-report.md:113-118`
records that the ambient instantiation was never typechecked, and marks the
ambient half INFERRED. So `[LJ-1.238]` delivers a class-generic port, not an
ambient one.

**Nothing of the `Agree` family is ported. MEASURED**, by the two opens at
`ProbeLJ152B.agda:35,37` and by `src/L/Condensation.lagda.md:71`, which reads
`open hPropStructure 𝒮ʟ` for the whole file.

## Q3. HOW BIG IS THE CHAPTER?

**A band, with its basis, and one probe named. The target gave no figure.**

### 3.1 The delivered comparable, counted

Caliber: non-blank lines inside ` ```agda ` fences. The region
`src/L/Condensation.lagda.md:6617-7179` lies wholly inside one fence
(`:5424` opens, `:7202` closes), so non-blank equals in-fence non-blank there.

| block | non-blank lines |
|---|---:|
| the three cited ranges | 288 |
| the contiguous region `:6617-7179` | 527 |
| plus first order supports in the same file | 970 |
| plus second order supports | 1,264 |

The first order supports are `keyArBS` (`:1474`), `tagBS` (`:1484`), `closedBS`
(`:1586`), `hasWitnessBS` (`:1712`), `isCodeBS` (`:1733`), `domB` (`:1746`),
`module SatGraphB` (`:2230`), `KFactsNS` (`:6033`), `KFactsCons` (`:6077`),
`ClosedAgree` (`:6404`), `DomainAgree` (`:6468`), `WitnessAgree` (`:6534`) and
`KeyAgree` (`:6657`).

### 3.2 It is NOT the 1,105 lines, and `[LJ-1.233]` repeats here

`agents/tasks/LJ-1-218/lj-1.218-report.md:192` prices "the whole `*Agree`
architecture" at 1,105, and its own parenthetical splits that into
`TwelveAgree` 494, `UpperAgree` 305 and `LowerAgree` 306. **Those are three
separate files under `src/L/Condensation/`.** The same report counts
`src/L/Condensation.lagda.md` separately at 6,676 (`:21`).

**So this bridge is NOT those 1,105 lines. MEASURED.** The pattern
`[LJ-1.233]` found at wall (a) holds again.

**But the 1,105 is the supplier, so a port drags it.**
`agents/tasks/LJ-1-218/lj-1.218-report.md:192` records that `TwelveAgree`'s
`twelve-out` and `twelve-back` are the types `SatGraphAgree` takes as
hypotheses, at `src/L/Condensation.lagda.md:6812-6815` and `:7097-7100`.

### 3.3 The band

**Upper bound, MEASURED: 1,264 lines**, if the whole class-carrier block must be
rewritten at the ambient carrier.

**Lower bound: NOT PRICED.** The one comparable is `[LJ-1.238]`, which wrote 40
lines to port 157 and left 145 verbatim, with 0 per-tower residual
(`agents/tasks/LJ-1-238/lj-1.238-report.md:61-67`). **I refuse that ratio as a
price.** P-l: a measured cure does not transfer by analogy. `L.Coding.Sequence`
builds formulas and reads off projections. The `Agree` family transfers
satisfaction and spends numeral facts such as `numeralL-fst`
(`src/L/Condensation.lagda.md:6638`). The two are not comparable work.

**The correct answer under DD8 is that pricing needs a probe, and here it is.**

**THE PROBE.** Take `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`, 87 lines,
green at 1.95 s. Replace `open hPropStructure 𝒮ʟ` (`:35`) and
`FOL.Absoluteness.Single 𝒮ᵥ isL isL-trans` (`:37`) with the `(M, M-trans)`
abstraction that `agents/tasks/LJ-1-238/GenSequence.agda:14-24` already uses.
Then ask whether `graph-assembly` still typechecks.

That probe measures the widest unmeasured term: **is the assembly
carrier-generic, or does it spend `isL`?** If it is generic, the residue is
`StepAgree` and `ApproxAgree` alone, and the chapter is bounded below the block
above. If it is not, the 1,264 line upper bound stands.

The probe is one file and its comparable runs in about two seconds. **It is
cheaper than one paragraph of the chapter it would price.**

## Q4. IS THERE A FOURTH ROUTE?

**The premise is TRUE and the route it suggests does NOT exist. But the record
names the wrong reason for the second coding, and that correction matters more.**

### 4.1 The premise, checked

`[LJ-1.243]` says Devlin needs no two-coding bridge. **Confirmed.**
`dev/literature/devlin-II5.md:95-100` quotes Devlin's 2.7: one Σ₀ formula `Φ`
and its ℒ-analogue `φ`, related by translation, not by an equation.

**What 1.9.15 actually requires.** `dev/literature/devlin-II5.md:224-227` states
two hypotheses: the matrix is Σ₀, and the carrier is transitive. A third
requirement is prior and belongs to 1.9.11, the translation
(`dev/literature/devlin-II5.md:326-328`).

### 4.2 Why Bedrock has two codings. The source says it

`src/L/Condensation.lagda.md:438-439`: "The tag numerals are slots, so every row
formula carries `countFo = 0` and instantiates the `EraseTransfer` template."

`erase` demands `countFo φ ≡ 0` (`src/FOL/Count.lagda.md:598`). It does not
replace a constant by a variable. `eraseTm (con a) p = Empty.rec (snotz p)`
(`:595`). **So a formula reaches `Formula ⊥* n` only if it is already constant
free.** `tagAtL` holds `con (numeralL k)`
(`src/L/Coding/Model.lagda.md:585-586`), and `tagBS` holds a variable bounded in
`K` (`src/L/Condensation.lagda.md:1484-1485`). That single trade is the whole
difference the `Agree` family repairs.

### 4.3 The second coding IS load-bearing, and for a reason nobody named

| property the crossing needs | Sequence coding (At) | BS coding |
|---|---|---|
| Δ₀ or Σ₁ certificate | **absent.** `grep -c Δ₀ src/L/Coding/Sequence.lagda.md` is 0 | present, `src/L/BoundedSubset.lagda.md:113`, `:145-146` |
| constant free | no, `src/L/Coding/Model.lagda.md:586` | yes, `src/L/Condensation.lagda.md:438-439` |
| tower read-off | yes, `Lset-only`, `src/L/Hierarchy.lagda.md:334` | none in the tree |

**Neither coding serves both ends. MEASURED.** So a route that deletes one
coding does not exist.

**The correction.** `[LJ-1.242]`, `[LJ-1.243]` and `[LJ-1.244]` all name the
CONSTANT gap. `agents/tasks/LJ-1-242/lj-1.242-report.md:295-301` calls the
numeral closure "OUR price, an artifact of the slot design".
`agents/tasks/LJ-1-243/lj-1.243-report.md:130-139` calls the wall an interface
type.

**Both stop one step short. There is a second, independent gap: complexity.**
`crossOut` spends `Σ₁ Cr.φP` (`agents/tasks/LJ-1-178/ProbeLJ1178A.agda:194-196`),
and the Sequence coding carries no complexity certificate at all. **So a
constant-free `LsetGraphAt` would still not serve the crossing. MEASURED**, from
the zero Δ₀ count against the `Σ₁` demand.

That is the answer to the question the project had not asked. The second coding
is not an artifact of slot design. **It is the only coding that carries the Σ₁
certificate Devlin's 1.9.15 requires.**

### 4.4 A fourth-route candidate, marked as a candidate

`extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)`
(`src/L/Coding/Model.lagda.md:662-663`) is a guarded `∀̇`, not the bounded
`∀̇∈` that `Δ₀` admits through `δ-∀∈`. The tree already carries
`extAtB→extAt` (`src/L/Condensation.lagda.md:2511`).

**So a normalization from the guarded form to the bounded form could give the At
coding its own Δ₀ certificate and remove the need for a second coding.**
**INFERRED**, from the two shapes plus the existing pair. I did not price it and
I did not check whether the rest of the At chain is bounded. **It is a candidate,
not a route.**

## C-42 BOTH DIRECTIONS

### Further: does this negative reach past `[LJ-1.7]`?

**NO, through `src/`. MEASURED.** `L.BoundedSubset` is imported by exactly one
file in `src/`, the index at `src/Everything.lagda.md:377`. `levelHoodB` occurs
ten times, all inside `src/L/BoundedSubset.lagda.md`. `graphBndAt` occurs six
times, four of them its own definition. **So the level hood block has no
consumer other than the `φ₀` build.**

**YES, inside `[LJ-1.7]`. MEASURED.**
`agents/tasks/archive/LJ-1-52/lj-1.52-report.md:17-18` records that `levelIn`
AND `cover` both need the same adequacy. So the negative holds both halves of
`[LJ-1.7]`, not one. The target treats it as one.

### Less far: does the DIRECTION finding survive?

**YES, and it is now corroborated twice. MEASURED.**

Probe A is green and `amb` comes out (`agents/tasks/LJ-1-244/ProbeLJ1244A.agda:114-117`).
The direction it spends is `embed φ₀` to `Graph`, which is BS to At.

`agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda:70-74` runs the same direction,
BS to At, in an older green probe. **So the direction finding is real, reusable,
and independent of everything this review overturns.** It is the target's best
result and it stands.

## DD4 SPLIT, TESTED

`[LJ-1.244]` section 5 says `q'` sits at the SHARED layer while the graph-witness
construction is PER-TOWER, and marks the second half INFERRED.

**The split is wrong at the top and right at the bottom.**

`agents/tasks/archive/LJ-1-52/lj-1.52-report.md:122-143` is an earlier dispatch's
own DD4 section. It records that `graph-assembly` is template-shaped and that the
J tower reuses it with its own bounded graph, and that `StepAgree` and
`ApproxAgree` are template content once the leaf adequacy exists. It records that
only the `DefBodyB` leaf is per-tower.

**I can check the load-bearing half myself.** `graph-assembly`'s type at
`ProbeLJ152B.agda:70-74` names `graphBndAt`, `LsetGraphAt`, `StepAt` and
`ApproxAt` and no Def-tower syntax beyond those four. Those four are Def-side
instantiations of templates whose generic form already exists
(`agents/tasks/LJ-1-238/GenSequence.agda:14-24`).

**So the chapter's assembly is paid once for both towers, and only its leaf is
per-tower. INFERRED**, because nothing measures the J tower's instantiation and
`[LJ-1.52]`'s DD4 section is a claim, not a measurement.

**Why this matters to the owner.** If the split holds, the price halves in the
only sense DD4 means. **The port probe of section 3.3 tests it in the same run**,
because a carrier-generic `graph-assembly` is the same fact as a tower-neutral
one.

## EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the stuck goal at `ProbeLJ1244B.agda:75` proves `q'` is hard | **MEASURED FALSE.** `Graph` and `φ₀` are unconstrained parameters, `:45`, `:68` |
| the statement in probe B is true at that generality | **MEASURED FALSE** from the telescope, **INFERRED** for the instantiation, section 1.2 |
| `TagAgree`, `SatGraphB`, `isCodeBS` are the blocking terms | **MEASURED FALSE.** All delivered, `src/L/Condensation.lagda.md:6628`, `:6802`, `:1733` |
| the cited line ranges name complete declarations | **MEASURED FALSE.** `:7170-7179` holds none, section 2.1 |
| nothing in the tree produces `LsetGraphAt` from `graphBndAt` | **MEASURED FALSE.** `ProbeLJ152B.agda:70-88`, proved |
| the bridge is unported to the ambient carrier | **MEASURED TRUE.** `ProbeLJ152B.agda:35,37`, `src/L/Condensation.lagda.md:71` |
| `q'` is built | **MEASURED FALSE.** `StepAgree` and `ApproxAgree` are hypotheses, `ProbeLJ152B.agda:53-64` |
| the bridge is the 1,105 `*Agree` lines | **MEASURED FALSE.** Those are three other files, `agents/tasks/LJ-1-218/lj-1.218-report.md:192` |
| the second coding is a slot-design artifact | **MEASURED FALSE.** It is the only coding with a Σ₁ certificate, section 4.3 |
| Devlin needs a two-coding bridge | **MEASURED FALSE.** `dev/literature/devlin-II5.md:95-100` |
| the level hood block has other consumers | **MEASURED FALSE.** One import, `src/Everything.lagda.md:377` |
| the negative holds only one half of `[LJ-1.7]` | **MEASURED FALSE.** Both halves, `agents/tasks/archive/LJ-1-52/lj-1.52-report.md:17-18` |

## ARCHIVE USED (DD18)

One line read named per file.

- `agents/tasks/LJ-1-244/lj-1.244-report.md`, read WHOLE. **Line read `:80-81`**,
  "None of it is ported to the ambient carrier". True, and not the block.
- `agents/tasks/LJ-1-244/ProbeLJ1244A.agda`, read WHOLE. **Line read `:114`**,
  `go γ h = M.graph-only zero (suc zero) γ (q' γ h)`.
- `agents/tasks/LJ-1-244/ProbeLJ1244B.agda`, read WHOLE. **Line read `:68`**,
  `(φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)`, the unconstrained parameter that voids the
  measurement.
- `agents/tasks/LJ-1-243/lj-1.243-report.md`, read `:37-135`, `:640-720`.
  **Line read `:136`**, "That type forbids a constant by construction". Correct,
  and one gap short.
- `agents/tasks/LJ-1-242/lj-1.242-report.md`, read `:20-110`, `:225-240`.
  **Line read `:295-301`**, the slot-design attribution, which section 4.3
  corrects.
- `agents/tasks/LJ-1-238/lj-1.238-report.md` and `GenSequence.agda`.
  **Line read `:113-118`**, the ambient half marked INFERRED, which the target
  did not carry.
- `agents/tasks/LJ-1-218/lj-1.218-report.md`. **Line read `:192`**, the 1,105
  row with its three-file parenthetical.
- `agents/tasks/LJ-1-241/ProbeLJ1241A.agda`. **Line read `:103`**,
  `base = Cnt.erase LH.levelHoodB refl`, which fixes what `φ₀` is.
- `agents/tasks/LJ-1-184/ProbeLJ1184A.agda`. **Line read `:327`**,
  `ambient γ φ = (map fst γ) R.Abs.⊨ᵛ φ`, which section 1.2 spends.
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read WHOLE. **Line read `:118-120`**,
  `go`'s type, which `matrix-decode` already concludes.
- `agents/tasks/archive/LJ-1-52/lj-1.52-report.md`, read `:1-175`. **Line read
  `:63-64`**, "the unbuilt content is `StepAgree` ... and `ApproxAgree`". This is
  the review's centre.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152B.agda`, read WHOLE. **Line read
  `:70`**, `graph-assembly`, proved and green.
- `agents/tasks/archive/LJ-1-52/ProbeLJ152A.agda`, read `:40-104`. **Line read
  `:58`**, `matrix-decode`.
- `agents/tasks/archive/LJ-1-61/ProbeLJ161A.agda`, `LJ-1-57/ProbeLJ157A.agda`,
  `LJ-1-56/ProbeLJ156A.agda`, headers read. **Line read
  `ProbeLJ161A.agda:5-9`**, the leaf chain's contents. All at `𝒮ʟ`; none bears
  on the missing row.
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read `:200-215`,
  `:800-815`. **Line read `:808`**, "the class-carrier equivalence, stated in the
  crossing section below and left standing with the ambient obligations". The
  retired route parameterized the crossing as `CrossOut φ` (`:208`) and never
  discharged it. **It shows no route Bedrock has not tried.** The live route's
  `[LJ-1.52]` decomposition is strictly further along.

## LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:88-115`, `:205-415`.

- **`:95-100`**, Devlin's 2.7: one Σ₀ formula `Φ` and its ℒ-analogue `φ`.
- **`:224-227`**, what 1.9.15 requires: the matrix is Σ₀, and the carrier is
  transitive. Both directions.
- **`:321-324`**, 1.9.15 as the bridge between satisfaction inside a transitive
  carrier and ambient truth.
- **`:326-328`**, 1.9.11, the translation, which is prior to 1.9.15 and is not
  1.9.15.
- **`:376`**, row C3, which assigns Σ₀ absoluteness to neither tower.

**WHY NOT.** I did not use `:415-620`. That range covers the J tower's op-graph
route and the Σ₀ naming caveat. Neither bears on which coding carries the Σ₁
certificate in the Def tower.

**The premise holds.** Devlin needs no two-coding bridge, because he has one
formula and a translation. **Bedrock needs one, because its two codings split the
three properties the crossing needs, and no single coding carries all three.**

## PROHIBITIONS, ANSWERED

No Agda ran. No master, brief or report was edited. `agents/tasks/LJ-1-245/` and
`agents/tasks/LJ-1-247/` were not opened. `q` was not re-litigated: both its
refutations were read and accepted at
`agents/tasks/LJ-1-243/lj-1.243-report.md:56-81` and `:105-128`. No commit, no
push, no `git checkout`, `stash`, `reset` or `clean`. No `make check`.

**My file:** `agents/tasks/LJ-1-246/lj-1.246-report.md`, and nothing else.
