# LJ-1.251 report: DD25 review of `[LJ-1.250]`

tier: opus, the ADVERSARIAL row. The target was written by pi, so the critic is
not the author. NO AGDA RAN. No master edited. No commit, no push. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## VERDICT

**UPHELD.**

`[LJ-1.250]` is right. `ψs` and `ψa` enter the port with no constraint at all,
so `StepAgree` and `ApproxAgree` are interfaces and not theorems.
`[LJ-1.249]` is the report that is wrong.

**The residue is not unmeasured. It is measured, four times, and it already
sits in the status screen under another name.**

## ONE SENTENCE FOR THE OWNER

**`[LJ-1.7]` costs step 6 of the satisfaction supply chain, which is
`[LJ-1.113]`'s 28 fields at about 255 in-fence lines, plus the placement of the
leaf transfer above it at a delivered comparable of 147 lines, plus an unpriced
tail of site facts.**

That sentence will not change next dispatch, because step 6 is the same object
under every name the chain has used, and `dev/PLAN.md:56` already carries its
figure.

## Q1. IS THE REFUTABILITY CLAIM RIGHT?

**YES. `[LJ-1.250]` is right and `[LJ-1.249]` is wrong.** I read the telescope
myself, as the brief ordered.

**The telescope.** `Body` at `agents/tasks/LJ-1-249/ProbeLJ1249.agda:140-152`
takes five parameters.

| parameter | line | does a hypothesis constrain it? |
|---|---|---|
| `DefAt` | `:141` | not by itself |
| `DefAt-in` | `:142-145` | YES. It pins `DefAt` to `𝒟ₒ` |
| `DefAt-out` | `:146-149` | YES. The other direction |
| `ψs : Formula S 13` | `:150` | **NO. Bare** |
| `ψa : Formula S 15` | `:151` | **NO. Bare** |

**MEASURED: `ψs` and `ψa` enter with no accompanying hypothesis.** The
telescope closes at `:152` with `where`. No equation, no adequacy pair and no
relation follows the two formulas. `DefAt` shows the contrast inside the same
telescope, because two adequacy hypotheses follow it at `:142-149`.

**The two sides of the implication touch disjoint parameters.**

- `StepAgree` (`ProbeLJ1249.agda:164-168`) has the premise `GB.S.stepBndAt` and
  the conclusion `StepAt`.
- `GB.S.stepBndAt` goes through `GraphB` (`:124-131`) to `StepB` (`:88-110`).
  Its only content parameter is `ψs`, applied at `:128` and used in `leafB` at
  `:91-94`.
- `StepAt` is `GenSequence`'s (`agents/tasks/LJ-1-238/GenSequence.agda:72-73`).
  It is built from `StepBody` (`:66-70`), whose only content parameter is
  `DefAt` at `:69`.

**MEASURED: no parameter, equation or hypothesis relates `ψs` to `DefAt`.** The
premise is a formula in `ψs`. The conclusion is a formula in `DefAt`. The
telescope that introduces both introduces no bridge between them.

**So the implication is refutable at that generality. INFERRED**, because no
Agda ran. The refutation needs only the freedom in `ψs`. Choose `ψs` to make
`stepBndAt` hold at the environment. The conclusion still asks for a `𝒟ₒ` fact
that `DefAt-out` does not give. `[LJ-1.246]` classified its `φ₀` refutation the
same way.

**WHY `[LJ-1.249]` IS WRONG, exactly.**
`agents/tasks/LJ-1-249/lj-1.249-report.md:84-86` says「Both are constrained,
not free: `ψs` and `ψa` determine `GB.S.stepBndAt` ...; `DefAt` occurs in the
At formulas」. **To determine a formula is not to be constrained by one.**
`agents/tasks/LJ-1-250/lj-1.250-report.md:56-57` names the error correctly:
occurrence is not constraint. `[LJ-1.249]:164` then answers C-45 with「I
audited the instantiation: `ψs`/`ψa`/`DefAt` are constrained」. That is the
audit C-45 asks for, reported with the wrong result.

**A second, smaller error in `[LJ-1.249]` supports this reading.** Its section 4
cites the leaf parameters at `ProbeLJ1249.agda:148-149` and the `DefAt` trio at
`:141-147`. **MEASURED FALSE.** `ψs` is at `:150` and `ψa` is at `:151`. The
trio spans `:141-149`. The citation is wrong by two lines in a nine-line
telescope. That is consistent with a claim written from the file's shape and
not from its text.

**ONE REFINEMENT `[LJ-1.250]` MUST CARRY. It does not weaken the verdict.**
`lj-1.250-report.md:10-12` calls the interfaces「UNCONSTRAINED」and puts
`DefAt` among the unrelated parameters. **`DefAt` IS constrained**, by
`DefAt-in` and `DefAt-out` at `ProbeLJ1249.agda:142-149`, which pin it to `𝒟ₒ`
in both directions. **The unconstrained parameters are `ψs` and `ψa` alone.**
The verdict holds, because the refutation needs only those two. A reader who
carries「the leaves are unconstrained」forward will overstate the damage on the
At side, where the adequacy pair is real and delivered.

## Q2. HOW MUCH OF `[LJ-1.249]` SURVIVES?

**The port is not worth zero. It is worth much less than its headline.**

**WHAT SURVIVES, and it is real.** `graph-assembly` at
`ProbeLJ1249.agda:176-194` is a PROVED term with a body. It is an honest
implication: given `StepAgree`, given `ApproxAgree` and given the site facts,
it assembles `LsetGraphAt`. **Its truth does not depend on its hypotheses being
dischargeable**, so the refutability finding does not touch it. It is proved at
the `(M, M-trans)` carrier, so both towers pay for it once. That is a real DD4
result, and Q3's per-tower section confirms it from a second source.

**WHAT IT BUYS, measured.** The assembly block is 30 non-blank code lines
(`lj-1.249-report.md:57`). It is `ProbeLJ152B.agda:53-88` verbatim with three
renames (`lj-1.249-report.md:60-63`). **So the port re-sited 30 known-good lines
and wrote no new mathematics.** The other 101 lines of the 132 are plumbing (54)
and re-expressed BS templates (47). Both restate material already in
`src/L/Condensation.lagda.md` (`lj-1.249-report.md:55-56`, `:66-68`).

**WHAT IT DOES NOT BUY. MEASURED.** No line of the port moves the supply. The
two hypotheses stay hypotheses. The objects that would discharge them are
untouched by the file.

**So the port is a placement and not a discharge. `exit 0` is not a supply
(C-45).** The sentence that did the damage is
`lj-1.249-report.md:16-17`:「So the chapter does NOT exist. `[LJ-1.7]`'s gap is
`StepAgree` and `ApproxAgree` plus this port.」**MEASURED FALSE**, and Q3 says
by how much.

**A third interface that neither report flags.** `ProbeLJ1249.agda:162` opens
`module _ (SF : (h x w v γ K : S) → Type (ℓ-suc ℓ))`. `SF` is an arbitrary type
family. `graph-assembly` then takes `sf : (h' : S) → SF h' x w v γ K` at
`:177`. **So the port has THREE unsupplied interfaces and not two. MEASURED**,
by reading the module header. This does not make `graph-assembly` false, for
the reason above. It does mean that any count of the gap which names two
objects is short by one.

## Q3. WHAT IS THE RESIDUE, EXACTLY?

**THE 28 PIECES, PLUS SOMETHING. The 28 are the core, and the project has
priced them four times.**

**FIRST, THE IDENTIFICATION, which is the answer to「it keeps changing」.**
The chain has used four names for one object. They are the same object.

| name used | where | the object |
|---|---|---|
|「a chapter」| `[LJ-1.244]` | the same |
|「two named lemmas」| `[LJ-1.246]`, `[LJ-1.249]` | the same |
|「a leaf supply」| `[LJ-1.250]` | the same |
|「step 6, the satisfaction layer」| `[LJ-1.168]` to `[LJ-1.199]` | the same |

**The identification is MEASURED, not read off a summary.**
`agents/tasks/LJ-1-173/lj-1.173-report.md:857` says「building step 6 first would
have been worse than useless. **Its 28 fields** include these nine」. The 28
originate at `agents/tasks/LJ-1-113/lj-1.113-report.md:8`:「PROVABLE: 1. NEEDS
NEW CONTENT: 28.」They are enumerated one per row at `:29-59`. The source
comment the brief quotes, `src/L/Condensation/TwelveAgree.lagda.md:519-522`,
points at that same set.

**SECOND, THE PRICE. It exists and the status screen already carries it.**

| figure | source | basis, in the source's own words |
|---|---:|---|
| about 250 | `lj-1.113-report.md:135-137` | **hypothesis**, and `:143-146` says so |
| about 270 or 271 | `lj-1.168-report.md:316-318` | **survey** on delivered comparables, `:364-367` |
| 405 | `LJ-1.172.md:22` | an **abort ceiling**, 270 plus 50 percent |
| **about 255** | `lj-1.173-report.md:1946` | **re-cost** of the 1.168 allocation, `:1939-1965` |

`dev/PLAN.md:56` carries the 255 today:「Step 6 re-prices at about 255 and is
UNBUILT. Its seconds are NOT MEASURED」. **I checked that number to its source
and it traces correctly.** `[LJ-1.199]` was dispatched to build it and wrote
**ZERO lines** (`agents/tasks/LJ-1-199/lj-1.199-report.md:10`), stopping at the
join and not at the budget (`:116`).

**No probe has ever measured any of the 28. MEASURED**, and every author says
so in his own report: `lj-1.113-report.md:143-146`, `lj-1.168-report.md:364-367`
and `lj-1.173-report.md:1060`.

**THIRD, WHAT THE 255 DOES NOT COVER. Each item is MEASURED as unpriced.**

1. **`LeafAgree`'s 14 site facts.** Its telescope at
   `src/L/Condensation.lagda.md:7074-7147` has 16 slots: one `KFacts` record,
   `twelve-out` and `twelve-back`, and 14 site-fact functions. The 255 prices
   the `TFacts` fields behind `twelve-out` and `twelve-back`. **It prices none
   of the 14.** No search of mine found a figure for them.
2. **The `SF` bundle** at `ProbeLJ1249.agda:162`, unpriced anywhere.
3. **The `ω ∈ σ` discharge.** `agents/tasks/LJ-1-199/lj-1.199-report.md:166-167`
   says「The re-price stays about 255; the discharge of `ω ∈ σ` is NEW content
   the 255 did not count」, and `:175` marks「the 255-line price covers the
   whole supply」as **MEASURED FALSE in one term**.

**FOURTH, THE PLACEMENT, and it has a delivered comparable that this chain
never cited.** `agents/tasks/LJ-1-124/ProbeLJ1124A.agda` proves all six
directions: `step-out` `:112`, `step-in` `:116`, `approx-out` `:167`,
`approx-in` `:171`, `graph-out` `:199`, `graph-in` `:204`. It is green at
**147 non-comment lines and 37.43 user seconds**
(`agents/tasks/LJ-1-124/lj-1.124-report.md:8-9`, `:44-52`).

**So `StepAgree` and `ApproxAgree` were built once already, in a probe.**
`[LJ-1.250]`'s「Written proof lines: 0」(`lj-1.250-report.md:13`) is true for
`src/` and true for the port. **It is MEASURED FALSE against the probe
corpus.** The 1.124 bridges stand over their own hypotheses
(`ProbeLJ1124A.agda:44-56`, `:127-141`, `:182-194`), so they are a placement
and not a supply. They are still the right comparable for what the placement
costs.

**THE BAND, with its basis.**

**ONE figure: about 400 in-fence lines.** It is 255 plus 147.

- **255** for step 6's 28 fields. Basis: **survey**. Spread across the four
  historical estimates is **250 to 271**.
- **147** for the placement. Basis: **one delivered comparable**, green.
- **Excluded and unpriced:** the 14 site facts, the `SF` bundle, the `ω ∈ σ`
  term.

**Seconds are NOT MEASURED for step 6** (`lj-1.173-report.md:1962`,
`dev/PLAN.md:56`). **One waller is known and it is inside the 28.**
`agents/tasks/LJ-1-158/LJ-1.158.md:37` records that `sucV`, inside `sucK`,
**exhausts 8 GB in 108 s** as a record field, and
`agents/tasks/LJ-1-158/lj-1.158-report.md:355` calls `sucK`「the only known
waller in this family」. `sucK` is item 23 of `[LJ-1.113]`'s 28
(`lj-1.113-report.md:54`). **So the 400 is a line figure with a live heap risk
attached, not a schedule.**

**THE STATE OF THE 28 TODAY, so the next dispatch does not re-derive it.**

- **0 of 28 are supplied.** MEASURED. `grep -rn TFacts src` returns hits only
  inside `src/L/Condensation/TwelveAgree.lagda.md`. No `TFacts` value exists.
- **`AbstractFrame` has ZERO applications in `src/`.** MEASURED. `grep -rn
  AbstractFrame src` gives two hits: a comment at
  `src/L/Condensation/TwelveAgree.lagda.md:70` and the header at `:333`.
- **10 of the 28 were refuted as written and then cured by a restriction
  ruling.** They are still unsupplied. `lj-1.173-report.md:851-852`, `:901-902`;
  `dev/PLAN.md:723`.
- **1 of the 28, `someEnv`, was reduced to `envSetK` and not closed.**
  `dev/PLAN.md:670`.

## Q4. DID THE BRIEF CAUSE IT?

**The framing did NOT cost the verdict. The ARCHIVE list cost the price.**

**The framing did not bind the agent.** `agents/tasks/LJ-1-250/LJ-1.250.md:30`
says「Everything above them is green」and `:39` says「So these two are the
join」. `[LJ-1.250]` refuted that framing in its own section 2, and it put the
D-10 check first. **So the assertion did not stop the refutation.** That is the
brief working as intended.

**The ARCHIVE section did bind the agent, and it cost the price.** The brief's
ARCHIVE list (`LJ-1.250.md`, ARCHIVE section) names six sources: `LJ-1-52`
twice, `LJ-1-249`, `LJ-1-246`, `LJ-1-238` and one source site. **Every one is
in the `StepAgree`/`ApproxAgree` lineage.** Not one is in the
`TFacts`/step-6 lineage, which is `LJ-1-113`, `LJ-1-166`, `LJ-1-168`,
`LJ-1-172`, `LJ-1-173` and `LJ-1-199`.

**The measured consequence.** `lj-1.250-report.md:137` says「Term 1 is the
widest unmeasured term」. **MEASURED FALSE.** Term 1 had been priced four times
and a build dispatch had already been sent at it. The agent searched hard and
searched along the lineage it was given: its own ARCHIVE USED section
(`lj-1.250-report.md:168-198`) adds `LJ-1-57`, `LJ-1-61` and `LJ-1-34`, all in
the same lineage.

**So the brief cost `[LJ-1.250]` the price and not the verdict.** The cure is
not a better framing. **The cure is that an ARCHIVE section which names one
lineage will get one lineage back.**

## THE CORRECTION I ALMOST WROTE, and I report it because it nearly shipped

**`agents/tasks/LJ-1-233/lj-1.233-report.md:247` says「That comment is now
STALE, and the tree delivers the real `K`」about the same
`TwelveAgree.lagda.md:519-522` that the brief and the status screen quote.** I
found that first and I began to write that three dispatches had missed it.

**I checked it, and `[LJ-1.233]` is the report that is wrong.**

- `[LJ-1.233]`'s evidence is `module KValue`
  (`src/L/Condensation.lagda.md:7222-7276`), which supplies a **`KFacts`**
  value, 29 closure fields, at `Lset lam`. That is real and it is delivered.
- **`AbstractFrame` does not consume `KFacts`. It consumes `TFacts`**
  (`src/L/Condensation/TwelveAgree.lagda.md:338`), a different record with 59
  fields (`lj-1.168-report.md:17-18`).
- **The 28 satisfaction fields are exactly the ones `KFacts` does not carry.**
  `KValue.facts` at `:7254-7267` has no field of that class.

**So the comment is TRUE at HEAD.** What `[LJ-1.233]` established is that the K
VALUE now exists. The comment never denied that. It says the 28 FACTS about K
are unbuilt, and they are. **MEASURED.**

**`[LJ-1.250]` and `dev/PLAN.md:47` are right to cite the comment as live.**
`[LJ-1.233]:247` is the error in the record, and it is the kind of error this
review exists to catch. **`[LJ-1.239]` carries a second record error in the
same area:** it attributes the 28-piece measurement to `[LJ-1.233]`, and the
measurement is `[LJ-1.113]`'s.

## C-42 IN BOTH DIRECTIONS

### It reaches FURTHER than the brief hoped

**`[LJ-1.237]`'s `sl` and `sc` are NOT safe, and `[LJ-1.240]` is not the
protection the brief takes it for.**

- **`sl` and `sc` are proved terms**, with bodies at
  `agents/tasks/LJ-1-237/ProbeLJ1237A.agda:191-201` and `:205-246`.
- **They stand over a BARE parameter.** `module StageLH` at `:127-129` takes
  `(φ₀ : Formula (⊥* {ℓ-suc ℓ}) 2)` with no hypothesis about it. `module Build`
  at `:178-181` then takes `lh` over that `φ₀`. **MEASURED**, by reading both
  telescopes. This is the `[LJ-1.250]` shape.
- **`[LJ-1.240]`'s inhabitability finding is INFERRED and not MEASURED.**
  `agents/tasks/LJ-1-240/lj-1.240-report.md:104-113` marks the three source
  clauses MEASURED and the composite reduction **INFERRED**. That report names
  the missing probe itself at `:354-356`. **The probe never ran.**
- **`[LJ-1.241]` claims to have closed it and did not.**
  `agents/tasks/LJ-1-241/lj-1.241-report.md:14-15` says the inhabitability
  turns from INFERRED to MEASURED. Its own probes contain no `lh`, no `Build`
  and no `StageLH`. `[LJ-1.241]:123` admits「Not the supply of `lh`」. **So the
  record says MEASURED where the artifacts give INFERRED.**
- **The witness is the vacuity.** The only `φ₀` at which `lh` is known
  inhabited is `⊤̇`, at which `sl` and `sc` say nothing.

**ONE DIFFERENCE, and I will not overstate the damage.** `lh` is in scope
inside `module Build`, and `sl`'s body applies it at `:191`. So `sl` and `sc`
are genuine conditional theorems. They are not refutable, unlike `StepAgree`.
**The accurate negative is: `sl` and `sc` are green over a hypothesis whose
only demonstrated inhabitant is the vacuous one.** That is one step milder than
`[LJ-1.250]`'s finding, and it is still a defect the status screen does not
carry.

### It reaches LESS far in one place

**`[LJ-1.248]`'s 146 lines are NOT reached by this failure.** Its four addends
trace to green probes with ordinary constrained telescopes: A1 54
(`agents/tasks/LJ-1-232/lj-1.232-report.md:144-146`), A3 26 (`:58`), A4 22
(`agents/tasks/LJ-1-236/lj-1.236-report.md:144`), A6 44
(`agents/tasks/LJ-1-217/lj-1.217-report.md:115`).

**It has a different and milder defect.** `[LJ-1.248]` ran nothing
(`lj-1.248-report.md:3-4`), so its per-tower PARTITION is a survey while its
addends are measurements. `:271` marks the composite MEASURED. **The composite
also excludes A5, the largest block at 348 lines, which `:163` marks OPEN.**
`lj-1.248-report.md:188-189` gives A5's share as about 21 to 50. **So the
per-tower half is about 146 to 196 and the screen carries 146.**

### The narrow check the brief asked for

**`[LJ-1.249]`'s three separable facts survive.** Step zero ran and the
archived probe was green (`lj-1.249-report.md:26`). The port typechecked
(`:27-30`). The DD4 measurement holds, and the next section confirms it from an
older and independent source. **Only the「constrained」claim falls.**

## PER-TOWER FRACTION (DD4)

**The brief asks whether `[LJ-1.249]`'s DD4 measurement is「true and nearly
empty」if the leaf holds all the work. ANSWER: NO. The leaf is 25 parts shared
machinery to 3 parts tower.**

**`[LJ-1.113]` split the same 29 facts by DD4, and it did so before this chain
began.** `agents/tasks/LJ-1-113/lj-1.113-report.md:219-220` reads「**25 of the
29 are about the CODING machinery; 4 are about the TOWER.**」The coding half is
listed at `:222-231`. The tower half at `:232-236` is `t0eq`, `t1eq`, `t0K` and
`someEnv`. `t0K` is the one provable fact, so **the tower share of the 28 is
three: `t0eq`, `t1eq` and `someEnv`.** `:238-239` states the answer:「the J
tower repeats at most the 4 tower facts; the 25 coding facts are paid once」.

**The fraction, by count and by lines.**

| measure | per-tower | shared | source |
|---|---:|---:|---|
| pieces, of the 28 | **3** | 25 | `lj-1.113-report.md:219-236` |
| lines, of the 255 | **about 28** | about 227 | `someEnv` at 25 in `lj-1.173-report.md:1960`, plus two field entries at about 1.5 each |
| lines, of the 400 | **about 28**, so about 7 percent | about 372 | the 147 placement is carrier-generic |

**So `[LJ-1.7]`'s per-tower share is about 28 lines. INFERRED**, because it
composes a MEASURED DD4 split with a SURVEYED line allocation. **Against
`[LJ-1.248]`'s 146 for A-prime, `[LJ-1.7]` adds a small per-tower charge and a
large shared one.**

**That is the honest DD4 reading, and it AGREES with `[LJ-1.249]` on this one
point.** Its section 4 claim that the assembly is paid once for both towers is
correct, and a second and older measurement now supports it. **The DD4 result
is not nearly empty. The constraint claim beside it is still wrong.**

## EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `ψs` and `ψa` carry a constraint | **MEASURED FALSE.** `ProbeLJ1249.agda:150-152`, bare to the `where` |
| `DefAt` carries no constraint | **MEASURED FALSE.** `DefAt-in`/`DefAt-out`, `:142-149`. `[LJ-1.250]`'s wording overstates here |
| a refutation instance typechecks | **INFERRED.** No Agda ran, as the brief ordered |
| `[LJ-1.249]`'s section 4 cites the right lines | **MEASURED FALSE.** Off by two; `ψs` is `:150`, not `:148` |
| the port has two unsupplied interfaces | **MEASURED FALSE. Three.** `SF` at `:162` |
| the green port is worth zero | **MEASURED FALSE.** `graph-assembly` is a proved implication, 30 re-sited lines |
| the residue is unmeasured | **MEASURED FALSE.** Priced four times; 255 stands in `dev/PLAN.md:56` |
| the residue is only the 28 pieces | **MEASURED FALSE.** Add the placement, 14 site facts, `SF`, and `ω ∈ σ` |
| `StepAgree`/`ApproxAgree` have zero written proof lines | **MEASURED FALSE against the probe corpus.** `ProbeLJ1124A.agda`, six directions, 147 lines, green |
| any of the 28 is supplied in `src/` | **MEASURED FALSE. Zero.** No `TFacts` value exists |
| `AbstractFrame` is applied in `src/` | **MEASURED FALSE.** Two hits, a comment and the header |
| the `:519-522` comment is stale | **MEASURED FALSE.** `[LJ-1.233]:247` is wrong; `KValue` supplies `KFacts`, and `AbstractFrame` consumes `TFacts` |
| `sl` and `sc` are safe because `lh` is inhabitable | **MEASURED FALSE.** `φ₀` is bare at `ProbeLJ1237A.agda:128`, and the inhabitant is INFERRED |
| `[LJ-1.241]` measured `lh` inhabitable | **MEASURED FALSE.** Its probes name no `lh`; `[LJ-1.241]:123` says so |
| `[LJ-1.248]`'s 146 is reached by this failure | **MEASURED FALSE.** Its addends rest on constrained probes |
| `[LJ-1.248]`'s 146 is a complete per-tower half | **MEASURED FALSE.** A5 is OPEN; the band is about 146 to 196 |
| the DD4 measurement is nearly empty | **MEASURED FALSE.** 25 of 28 pieces are shared machinery |
| the brief's framing cost the verdict | **MEASURED FALSE.** `[LJ-1.250]` refuted the framing |
| the brief's ARCHIVE list cost the price | **MEASURED TRUE.** Six sources, one lineage, and the price sits in another |

## C-44: THE BRIEF'S OWN CLAIMS, CHECKED

- 「`LeafAgree` is at `src/L/Condensation.lagda.md:7065` ... a grep returns only
  two comments and the declaration」. **CONFIRMED.** Three hits: `:7057`,
  `:7065`, `:7077`.
- 「`TwelveAgree.lagda.md:519-522` says ... 28 pieces. MEASURED」. **The quote is
  accurate. The word MEASURED applies to the comment's TEXT and not to the
  tree's state.** I measured the state separately, and it agrees with the
  comment. See the correction section above.
- 「`[LJ-1.248]` measured the rest of A-prime's per-tower half at 146 lines」.
  **PARTLY UNPROVEN.** The addends are measured; the partition is a survey; A5
  is excluded and OPEN.

## ARCHIVE USED (DD18)

One line named per file.

- `agents/tasks/LJ-1-250/lj-1.250-report.md`, read WHOLE. **Line read `:55`**,
  「No parameter, hypothesis or equation relates `ψs` to `DefAt`」, the claim I
  upheld.
- `agents/tasks/LJ-1-250/ProbeLJ1250.agda` and `LJ-1.250.md`, read. **Line read
  `LJ-1.250.md:39`**,「So these two are the join」, the framing in Q4.
- `agents/tasks/LJ-1-249/ProbeLJ1249.agda`, read WHOLE. **Line read `:150`**,
  `(ψs : Formula S 13)`, the bare parameter that settles Q1.
- `agents/tasks/LJ-1-249/lj-1.249-report.md`, read WHOLE. **Line read `:84`**,
  「Both are constrained, not free」, the sentence that is wrong.
- `agents/tasks/LJ-1-246/lj-1.246-report.md`, consulted through `[LJ-1.250]`'s
  citation. **Line read `:68`**, the `φ₀` refutation shape.
- `agents/tasks/archive/LJ-1-52/lj-1.52-report.md`. **Line read `:105-110`**,
  the wall named as the `DefBodyB`/`DefBody` leaf adequacy, which answers why
  the two lemmas were never built.
- `agents/tasks/LJ-1-113/lj-1.113-report.md`. **Line read `:219`**,「25 of the
  29 are about the CODING machinery」, the DD4 split.
- `agents/tasks/LJ-1-168/lj-1.168-report.md`. **Line read `:316-318`**, the 270
  and the 360.
- `agents/tasks/LJ-1-173/lj-1.173-report.md`. **Line read `:1946`**,「THE
  NUMBER: about 255 in-fence lines」.
- `agents/tasks/LJ-1-199/lj-1.199-report.md`. **Line read `:166-167`**, the
  `ω ∈ σ` term the 255 did not count.
- `agents/tasks/LJ-1-233/lj-1.233-report.md`. **Line read `:247`**,「That
  comment is now STALE」, which I refute.
- `agents/tasks/LJ-1-124/lj-1.124-report.md` and `ProbeLJ1124A.agda`. **Line
  read `lj-1.124-report.md:8`**, the 147 lines in two directions.
- `agents/tasks/LJ-1-237/ProbeLJ1237A.agda`. **Line read `:128`**, the bare
  `φ₀`.
- `agents/tasks/LJ-1-240/lj-1.240-report.md`. **Line read `:112`**, the
  composite reduction marked INFERRED.
- `agents/tasks/LJ-1-241/lj-1.241-report.md`. **Line read `:123`**,「Not the
  supply of `lh`」.
- `agents/tasks/LJ-1-248/lj-1.248-report.md`. **Line read `:167`**, the 146.
- `agents/tasks/LJ-1-158/LJ-1.158.md`. **Line read `:37`**, `sucK` exhausts
  8 GB in 108 s.
- `src/L/Condensation.lagda.md`, read `:7050-7277`. **Line read `:7097`**,
  `twelve-out`, the slot the 28 pieces feed.
- `src/L/Condensation/TwelveAgree.lagda.md`, read `:129-135`, `:325-400`,
  `:490-534`. **Line read `:338`**, `(tf : TFacts ...)`, which is not `KFacts`.
- `agents/tasks/LJ-1-238/GenSequence.agda`. **Line read `:69`**, `DefAt zero
  (suc zero)` inside `StepBody`.
- `dev/PLAN.md`, read `:36-80`. **Line read `:56`**,「Step 6 re-prices at about
  255 and is UNBUILT」.

## LITERATURE USED (DD18)

**In one line: the literature does NOT bound leaf adequacy, because leaf
adequacy is a coding-to-coding transfer and Devlin has only one coding.**

- `dev/literature/devlin-II5.md:224-227` gives Σ₀ absoluteness of the matrix
  for transitive carriers. That relates ONE coding to the ambient. **Leaf
  adequacy relates TWO of this project's codings, `DefBodyB` and `DefBody`, at
  a common environment.** No item in that digest states such a transfer, so the
  literature gives no bound and no proof shape for it. **MEASURED**, by reading
  the four numbered items at `:218-232`.
- **`[LJ-1.246]`'s complexity finding bears on it only negatively.** The
  Sequence coding carries zero Δ₀ certificates
  (`agents/tasks/LJ-1-249/lj-1.249-report.md:141-142`, re-checked there). **So
  the leaf adequacy cannot borrow a certificate it needs, because none is
  there.** It does not make the leaf adequacy harder. It removes one route.
- **WHY NOT the rest.** I did not use `fine-structure.md`, `j-hierarchy.md` or
  `rudimentary-functions.md`. The residue is a supply of membership facts about
  a bound in THIS formalization. It is not a mathematical step in Devlin, so no
  source prices it.

## RULES ANSWERED

- **C-45.** I audited the instantiation. The telescope at
  `ProbeLJ1249.agda:140-152` and the applications at `:128` and `:157` are the
  evidence, and not the module names.
- **D-10.** I priced the target's truth first. Q1 is that check.
- **C-36.** A failed substitution is not a proof of impossibility. I name the
  terms not written in Q3 and I do not claim they are impossible.
- **C-38.** A hypothesis is discharged when something supplies it. Zero of the
  28 have a supplier.
- **C-44.** I checked the brief's three claims. One is confirmed, one needs a
  qualifier, one is partly unproven.
- **P-l.** I re-measured at this site. I did not carry a comparable as a price.
  The 147 is named a comparable and never a measurement of this residue.
- **C-42.** Both directions, in their own section.
- **C-22.** The skeleton was written first, and the file was filled in four
  passes.
- **C-12.** NO AGDA RAN. No slot was taken.
- **DD4.** The per-tower fraction is a section, with its own source.
- **DD8.** ONE figure, about 400, with its basis and its exclusions named.
- **DD18.** ARCHIVE USED and LITERATURE USED above.
- **DD25.** I state where I agree with the target, and I report the correction
  I almost made against it.
