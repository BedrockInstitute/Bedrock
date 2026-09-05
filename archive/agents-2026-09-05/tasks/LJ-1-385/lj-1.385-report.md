# LJ-1.385 report: DD25 review of `[LJ-1.383]`'s「all six residues are FALSE」

tier: pi (pi-subagent-mode), the switch's ADVERSARIAL row, in-harness
opus. `[LJ-1.383]` was written by `pi` / `glm-5.3`, so the critic is not
the author (DD17). Adversarial review. Lands nothing, repairs nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED, in
those words.

## 0. VERDICT

**SPLIT.**

**UPHELD.** The sixth refutation is real. I re-ran `Probe383.agda`
myself: **exit 0 in 1.77 s user**. The count of six residue-labeled
parameters in `ProbeLeaf338.agda` is correct, and `[LJ-1.383]`'s
correction of `[LJ-1.378]`'s wrong line citation is correct. The four
prior refutations exist and are terms.

**OVERTURNED, half one, and I measured it.** **Not one of the six
refutations is a term about a residue parameter's own type.** The six
residue parameters live at the ambient structure `𝒮ᵥ ↾ Full`
(`agents/tasks/LJ-1-338/ProbeLeaf338.agda:62`). All five prior
refutations and `[LJ-1.383]`'s new term live at `𝒮ʟ`
(`ProbeTies341.agda:79`, `Residue347.agda:71`, `Refute348.agda:80`,
`Refute351.agda:106`, `Probe383.agda:80`). `𝒮ʟ = 𝒮ᵥ ↾ isL`
(`src/L/Constructible.lagda.md:411`) and `Full _ = Unit*`
(`agents/tasks/LJ-1-297/ProbeLJ1297A.agda:59-60`), so the two `S` types
are different types. My `Cross385.agda` measures it: **exit 42** at the
ONE line that separates it from my green `Ident385.agda`. `[LJ-1.383]`
DISCLOSES this in its section 8 and its section 10. Its LEAD does not,
and the brief copied the lead.

**OVERTURNED, half two, and this one is new.** **Two of the six are not
residue parameters of the LIVE leaf-stem.** `[LJ-1.338]` instantiates
`GD.LeafAgree`, which is `agents/tasks/LJ-1-336/GenDirty.agda:907`, a
frozen probe copy. That copy still carries `envK` (`:983-984`) and
`defPairK` (`:985-986`). The live chapter's `LeafAgree`
(`src/L/Condensation.lagda.md:7224-7305`) does NOT carry them, and the
chapter says why at `:7300-7302`:「THE TWO ENVIRONMENT TIES ARE GONE
FROM THIS TELESCOPE ([LJ-1.346])」. **The live residue is FOUR ties, not
six.** MEASURED.

**WHAT SURVIVES FOR THE ROUTE.** The ambient leaf-stem still rests on
false parameters, so `[LJ-1.378]`'s row is still not a price. But the
number is FOUR, the falsity of all four at the ambient structure is
INFERRED and not MEASURED, and two of the six died from a repair that
landed nine tasks ago rather than from mathematics. **`[LJ-1.378]`'s row
must be re-stated against the live chapter before it is re-priced.**

## 1. NON-VACUITY ON THE SIXTH

`[LJ-1.383]` refutes residue 2, the unary arity conjunct, at
`Probe383.agda:186-190`. I re-ran the file: **exit 0, 1.77 s user**.
MEASURED.

**THE ABSENCE CLAIM IS CORRECT.** No term refuted the unary arity
residue before this task. I searched every `.agda` file under
`agents/tasks/` for `wUnArNum`, `unCodesK` and `arity-cure-un`, then
filtered for absurdity. The hits are chapter copies (`GenDirty.agda`,
`GenAgree.agda`), the cure (`Cure350.agda:89`), deletion probes
(`LJ-1-204/ProbeMinusArNum.agda`, `LJ-1-214/ProbeMinusArNum.agda`,
which are chapter variants and not refutations) and `[LJ-1.383]`'s own
files. MEASURED.

**THE THREE LAYERS ARE PRESENT.** Layer one, the tie's other
conclusions hold at the same witnesses (`un-other-conjuncts`,
`Probe383.agda:219-220`). Layer two, every premise is a closed term
(`wU∈K` `:152-153`, `cU∈wU` `:155-156`, `codeEqU` `:158-161`). Layer
three, the run is at the delivered `KValue` record through `module Wire`
(`:245-280`). The discriminating control is one argument apart in the
same file: `numeral-arity-holds` at `ar := numeralL 1` (`:228-229`)
against the refutation at `ar := sglS (numeralL 1)` (`:129`). This is
`[LJ-1.347]`'s standard and `[LJ-1.350]`'s standard, and the sixth
meets both. MEASURED.

**THE STANDARD THE BRIEF NAMES IS NOT MET.** `[LJ-1.349]` set a fourth
layer and named it the last escape:「false only where the chapter never
looks」. It closed that escape with a term, `Live349.intended :
⟨ env ⊨ hasWitnessAt (suc zero) zero ⟩`
(`agents/tasks/LJ-1-349/Refute349.agda:244-245`), because
`WitnessAgree.out` consumes exactly `hasWitnessAt`. **`Probe383.agda`
holds ZERO occurrences of `hasWitness`, `shaped`, `intended` or `Live`.**
MEASURED, by grep over the whole file. So the sixth does not show that
its container `wU` is a witness set the consumer ever presents.

**HOW LARGE IS THAT GAP?** Smaller than it looks, and still open. The
countermodel's container is `wU = sglS cU`, the singleton of a code
whose arity slot is `sglS (numeralL 1)`, which is not a numeral. So the
container is a singleton of a fake code. `[LJ-1.352]` built the
matching fact for the BINARY container at tag 3, where the relation
`noneB` is `⊤̇` (`agents/tasks/LJ-1-352/lj-1.352-report.md:22-27`), and
`[LJ-1.350]` reached it at a second site. The unary container has no
such term. **P-l says a measured cure does not transfer by analogy.**
The same law binds a measured shapedness fact. **So the sixth's
intended-class membership is INFERRED from two binary comparables, not
MEASURED.**

**VERDICT ON ATTACK 1.** The sixth is genuinely refuted AT ITS STATED
TYPE, at `𝒮ʟ`. Its non-vacuity is adequate at `[LJ-1.347]`'s standard
and short of `[LJ-1.349]`'s. **UPHELD, with the fourth layer named as
open.**

## 2. THE COUNT, RE-DERIVED

**THE RESIDUE-LABELED PARAMETERS OF `ProbeLeaf338.agda` ARE EXACTLY
SIX.** I read the file whole. Each carries a `RESIDUE n` comment
directly above it.

| n | name | lines | block |
|---|---|---|---|
| 1 | `wArNum` | `:119-122` | `module Supply` |
| 2 | `wUnArNum` | `:124-127` | `module Supply` |
| 3 | `witK` | `:319-321` | `module Leaf` |
| 4 | `graphWitK` | `:333-342` | `module Leaf` |
| 5 | `envK` | `:346-347` | `module Leaf` |
| 6 | `defPairK` | `:349-350` | `module Leaf` |

**Two more parameters sit in `module Leaf` and are NOT ties**:
`twelve-out` (`:324-326`) and `twelve-back` (`:327-329`), under the
comment `NOT A TIE` at `:322-323`. **So the two residue blocks carry
eight parameters, of which two are not ties.** `[LJ-1.383]`'s count is
VERIFIED, MEASURED.

**THE BRIEF'S CITATION IS WRONG AND `[LJ-1.383]` CORRECTED IT
CORRECTLY.** `ProbeLeaf338.agda:353-356` is
`module LA = GD.LeafAgree ...`, the instantiation, not the residue.
VERIFIED at those lines. `[LJ-1.378]:61` carries the wrong citation
with the right count.

**ONE SMALL SLIP IN THE TARGET.** `[LJ-1.383]` places the two twelve
readings at `:324-332`. They end at `:329`; `:330-332` is RESIDUE 4's
comment. Three lines, no consequence.

**BUT SIX IS THE COUNT AGAINST A FROZEN COPY, AND THE LIVE COUNT IS
FOUR.** This is the finding neither the target nor the brief has.

- `ProbeLeaf338.agda:56-57` sets `module PKV = LJ-1-338.ProbeKValue338`
  and `module GD = PKV.GD`. `ProbeKValue338.agda:44` sets
  `module GD = LJ-1-336.GenDirty {ℓ} P1297A.Full`. So `GD.LeafAgree` is
  `agents/tasks/LJ-1-336/GenDirty.agda:907`, a probe copy generic in
  the class (`GenDirty.agda:56-60`).
- GenDirty's `LeafAgree` carries `envK` at `:983-984` and `defPairK` at
  `:985-986`, and passes them to `DefinesAgree` at `:1007-1009`.
- The LIVE chapter's `LeafAgree` telescope runs
  `src/L/Condensation.lagda.md:7224-7305`. It carries fourteen
  parameters after `f`, and `envK` and `defPairK` are not among them.
  The chapter states the removal at `:7300-7302`. Its `DA` at
  `:7323-7325` takes `(f .pairK) (f .carrierK) (f .arityK)` where
  GenDirty took `envK defPairK`.
- Those three are `KFacts` RECORD FIELDS. `ProbeLeaf338.agda:150-167`
  already builds the record `fL`. **So the live chapter asks
  `[LJ-1.338]` for nothing new in their place.** MEASURED.
- **THE ARITHMETIC, and it is the shortest statement of the finding.**
  The live telescope takes **FOURTEEN** parameters after `f`
  (`:7233`, `:7239`, `:7246`, `:7252`, `:7256`, `:7259`, `:7262`,
  `:7270`, `:7277`, `:7281`, `:7285`, `:7288`, `:7298`, `:7303`).
  `ProbeLeaf338.agda:353-356` passes **SIXTEEN** after `fL`. **The two
  extra are `envK` and `defPairK`.** MEASURED.
- The live chapter now derives both inside `SatGraphAgree`, at
  `src/L/Condensation.lagda.md:6905`:
  `open KTies {m} w K γ numK pairK carrierK arityK using ( envK; defPairK )`.
  MEASURED.
- The landing commit is `b834c2e`,「[LJ-1.346] Both ties land green
  first try, and the private block stays private」, found by
  `git log -S "THE TWO ENVIRONMENT TIES ARE GONE"`.

**THE LIVE RESIDUE OF THE AMBIENT LEAF-STEM IS FOUR TIES:** `wArNum`,
`wUnArNum`, `witK`, `graphWitK`, plus the two twelve readings, which
are not ties. MEASURED, by reading the live telescope against
`ProbeLeaf338`'s ten supplied ties (`:184`, `:195`, `:215`, `:235`,
`:245`, `:254`, `:260`, `:270`, `:280`, `:301`).

**`ProbeLeaf338.agda` IS GREEN TODAY, and that is not a contradiction.**
I ran it: **exit 0, 47.80 s user cold and 2.98 s warm**. It is green
because it typechecks against the frozen copy, not against the chapter.
MEASURED.

## 3. THE IDENTIFICATION, CHECKED

This is the attack the brief called load-bearing. **The failure the
brief feared did not happen. A different one did.**

### 3.1 The names and the type TEXTS match, MEASURED

| residue | its text at `[LJ-1.338]` | the refuted text | verdict |
|---|---|---|---|
| `defPairK` | `ProbeLeaf338.agda:349-350` | `ProbeTies341.agda:172-174` (`DefPairK`) | same text, `Ki := suc (suc (suc K))` |
| `envK` | `:346-347` | `ProbeTies341.agda:201-203` (`EnvK`) | same text |
| `witK` | `:319-321` | live chapter `:7233-7235` | same text |
| `graphWitK` | `:333-342` | live chapter `:7288-7297` | same text |
| `wArNum` | `:119-122` | `Probe383.agda:193-195` (`WArNum`) | same text |
| `wUnArNum` | `:124-127` | `Probe383.agda:182-184` (`WUnArNum`) | same text |

**`[LJ-1.341]`'s refutation is generic in the environment**, at
`module Refute {n : ℕ} (Ki : Fin n) (γ : S ^ n)`
(`ProbeTies341.agda:151`), so it does not depend on one chosen
environment. **`[LJ-1.351]`'s and `[LJ-1.348]`'s are terms deriving
`Empty.⊥`** at `Refute351.agda:408-412` and `Refute348.agda:247-252`.
So「merely NAMED like a refuted tie」is **MEASURED FALSE**.

**AND I PROVED HALF OF IT BY THE ELABORATOR, NOT BY READING.**
`agents/tasks/LJ-1-385/Ident385.agda` restates residues 1 and 2 at
`:49-60` and feeds them to `PL.Supply` at `:73`. **Exit 0, 12.14 s
user.** The application typechecks only if my two restatements ARE the
two residue slots. MEASURED.

### 3.2 The identification FAILS at the STRUCTURE, MEASURED

**The residue and every refutation live at different structures.**

- `[LJ-1.338]`'s residue: `open hPropStructure (𝒮ᵥ ↾ P1297A.Full)`
  (`ProbeLeaf338.agda:62`), and `Full _ = Unit* , isPropUnit*`
  (`agents/tasks/LJ-1-297/ProbeLJ1297A.agda:59-60`).
- Every refutation: `open hPropStructure 𝒮ʟ` (`ProbeTies341.agda:79`,
  `Residue347.agda:71`, `Refute348.agda:80`, `Refute351.agda:106`,
  `Probe383.agda:80`), and `𝒮ʟ = 𝒮ᵥ ↾ isL`
  (`src/L/Constructible.lagda.md:411`).

**THE MEASUREMENT.** `Cross385.agda` is `Ident385.agda` plus ONE module
application, `[LJ-1.341]`'s `Refute` at `[LJ-1.338]`'s own environment
and K slot. **Exit 42 at `Cross385.agda:76.58-63`:**

```
(Lift Agda.Builtin.Unit.⊤) !=< ∥ Σ PT341.HV.S (λ x → ... isL ...) ∥₁
when checking that the expression Sup.γ has type
P1297A.P1241.CS.S PT341.GM.AbsL.^ 17
```

The green file and the red file differ by that one line. **So no prior
refutation can even be APPLIED at the residue's environment.** MEASURED.

### 3.3 Does the transfer hold anyway?

**INFERRED YES, and the direction is favorable.** `S` at `Full` is
`Σ[ v ∈ V ] (Lift ⊤)`, so it carries a copy of every L set and the
ambient statement quantifies over strictly more objects. A countermodel
of the weaker L statement therefore lifts, if the ambient satisfaction
of the Δ₀ premise agrees, which `[LJ-1.297]`'s `absFull` supplies
(`ProbeLeaf338.agda:74-80`).

**BUT NOBODY HAS WRITTEN IT.** The countermodel needs GenDirty's own
ambient `prʟ`, `numeralL` and `tagAtL-adequate`, which are GenDirty
PARAMETERS (`GenDirty.agda:58-60`), not the L side lemmas the five
refutations use. **INFERRED, NOT MEASURED.** `[LJ-1.383]` says this
plainly at its section 8 (「Class-free: MINE IS NOT」) and its section
10 (「The ambient countermodels」). **Its lead does not, and the brief
copied the lead.** This is the same shape `[LJ-1.375]` measured today:
a verdict line that overstates its own body.

### 3.4 Verdict on attack 3

**SPLIT.** The identification holds by NAME and by TYPE TEXT, MEASURED.
It fails by TYPE, MEASURED. The gap is one unwritten port, not a
mistake in the mathematics. **The honest row word for all six is
INFERRED FALSE AT THE AMBIENT FRAME, MEASURED FALSE AT `𝒮ʟ`.**

## 4. DOES「ALL SIX FALSE」FOLLOW?

**NO, and it does not need to.** Six separate refutations are six
theorems, not one. `[LJ-1.383]` never claims one theorem; it lists them
one at a time in its section 1. The claim that fails is the narrower
one in its lead: that the row reads「terms modulo something FALSE」for
**ALL SIX today**.

**COULD A DIFFERENT SET OF PARAMETERS SUPPLY THE LEAF-STEM? FOR TWO OF
THE SIX, YES, AND IT ALREADY DOES.** `[LJ-1.346]` landed the
replacement. `KTies` derives both ties from `KFacts` fields at
`src/L/Condensation.lagda.md:6239-6259`, under the note at `:6192`:
「`DefinesAgree` and `LeafAgree` took `envK` and `defPairK` as ...」.
The live `LeafAgree` dropped both. **For `envK` and `defPairK` the
finding is exactly「a defect in `[LJ-1.338]`'s packaging」, and the
repair for `ProbeLeaf338.agda` is to delete two arguments from its
`:353-356` application.** MEASURED.

**FOR THE OTHER FOUR THE FINDING IS MATHEMATICAL.** `witK`,
`graphWitK`, `wArNum` and `wUnArNum` are still parameters of the live
telescope, at `:7233-7235`, `:7288-7297`, and inside `wCodesK`
`:7239-7245` and `wUnCodesK` `:7246-7251`. Their repair is the
`hasWitnessAt+` restatement family. `[LJ-1.383]` prices that family at
about 113 insertions from `[LJ-1.360]` and `[LJ-1.379]`. **I did not
re-derive that number and I do not endorse it**; `[LJ-1.383]` says
itself that nobody has carved the residue's share out of it
(`lj-1.383-report.md:155-164`).

**SO THE ROUTE-LEVEL CONSEQUENCE.** `[LJ-1.378]`'s row「leaf-stem,
ambient: TERMS modulo residue」is still not a price, for four names
rather than six. **And the row's citation is worse than wrong in its
line numbers: it points at an instantiation of a frozen chapter copy
that is one landed repair behind the chapter.** The ambient leaf-stem
needs re-statement against the live telescope FIRST, and re-pricing
after that.

## 5. PREMISES CHECK

| premise | status |
|---|---|
| six residue parameters at `ProbeLeaf338.agda:353-356` | **SPLIT.** Six residue-labeled parameters: VERIFIED at `:119-122`, `:124-127`, `:319-321`, `:333-342`, `:346-347`, `:349-350`. The citation `:353-356`: **REFUTED**, it is the `LA` instantiation. The LIVE count: **FOUR**, MEASURED against `src/L/Condensation.lagda.md:7224-7305` |
| five were refuted before this task | **SPLIT.** Five terms exist and derive `Empty.⊥`: VERIFIED at `ProbeTies341.agda:185-190` and `:231-238`, `Refute348.agda:247-252`, `Refute351.agda:408-412`, `Residue347.agda`. **REFUTED as stated about the residue parameters**: every one is at `𝒮ʟ`, the residue is at `𝒮ᵥ ↾ Full`, MEASURED by `Cross385.agda` exit 42 |
| the sixth is refuted by a new term, exit 0 | **VERIFIED**, `Probe383.agda`, re-run by me, exit 0 in 1.77 s user |
| `[LJ-1.378]` called the leaf-stem「TERMS modulo residue」at `lj-1.378-report.md:61` | **VERIFIED**, read today. The row also names「six residues parameters」and cites `:353-356` |
| `[LJ-1.383]`'s 113-insertion family price | not re-measured here; it is `[LJ-1.379]`'s, and `[LJ-1.383]` marks it uncarved |

## 6. ARCHIVE USED (DD18)

The four corpora, one line each, with one quoted line per file I read.

- **`archive/src/2026-08-09-rud-route/`**: **the retired route DID name
  residues with exact types, but they were PROOF OBLIGATIONS and not
  telescope parameters, so nothing transfers.** MEASURED by reading
  `L/OrderFormula.lagda.md:416-418`. **Line read, `:418`:**
  「Three residues remain, each stated with its exact type. **The
  image-image」. A residue there is a direction of a proof left
  unproved. A residue here is a HYPOTHESIS the module takes and cannot
  discharge, which can be FALSE. The two words name different objects,
  and that difference is why D-10 exists.
- **`archive/dev/TASKS-archived.md`**: read `:217`. **Line read:**
  「L3.32-T194 | D22 gate: the Q-lim residue at a general limit | RED:
  the frame re-instantiates at 62, but the family equality rests on a
  FALSE bridge; 612-1,062」. TOOK SHAPE only: the retired route also met
  a residue whose frame re-instantiated cheaply while the content under
  it was false. That is this task's shape exactly, and it carries no
  figure here.
- **`archive/dev/JOURNAL-archived.md`**: read `:1586-1588`. **Line
  read, `:1588`:**「lines, and reduces the third to one named residue
  **which is exactly the object the incumbent's own」. TOOK the WHY: the
  retired route also reduced a batch to ONE named residue and then found
  that the named object was the incumbent's own unpaid work. The lesson
  transferred is to name the OBJECT, not the count.
- **`archive/dev/DECISIONS-archived.md`**: read whole, 61 lines;
  grepped `residue`, `parameter`, `telescope`, `structure`. **WHY NOT:
  no archived ruling governs residue parameters. The one hit, `:25`, is
  about retired DECISION codes and uses「residue」for leftover rule
  text. The binding rules are the live D-10 and C-45.**

## 7. LITERATURE USED (DD18)

**The one line the brief asks for: a leaf-level ambient residue has NO
counterpart in Devlin, because his argument needs no per-notion tie
between two codings at all.**

- `dev/literature/devlin-II5.md`, read `:171-193` and `:214-222`.
  **Line read, `:181-185`:**「The short answer: Devlin's argument needs
  level-hood at Σ₁ strength with a Σ₀ matrix, uniformly Δ₁ at limit
  levels, and it needs the Σ₀ matrix to contain a BOUNDED object-level
  description of the Def step. It does not need a Δ₀ witness for the
  unbounded satisfaction existentials of the project's `LsetGraphAt`」.
  Devlin bounds the Def step INSIDE one Σ₀ matrix. Bounding it that way
  is what removes every「this object is inside the bound」obligation of
  the kind the six residues state. So the residues are an artefact of
  this formalization's two-coding split, and the orthodox text has no
  statement of their shape to be true or false. **This is a reason to
  doubt the SHAPE of the leaf-stem, not only its price.**
- `dev/literature/j-hierarchy.md`: **WHY NOT. It is the retired rud
  route's fine-structure note on ONE coding's stratification. A single
  coding has no second coding whose leaf ties could be false, so it
  bears on nothing here.** Same reason `[LJ-1.378]` and `[LJ-1.383]`
  declined it.

## 8. DD4, WITH THE AXIS NAMED (C-46)

**My axis is the L-against-ambient axis. DD4's own axis is
AC-against-GCH, fixed in code at `scripts/measure/ledger.py:50`, read
today.** Nothing in this review moves either trophy's closure. My two
files land nothing.

**MY FINDING IS A DD4 FINDING, and that is its most useful reading.**
The whole defect measured in section 3.2 is a SHARING failure on my
axis. `[LJ-1.336]` wrote `GenDirty` generic in the class
(`GenDirty.agda:56-60`), which is DD4 done right: one text, two
carriers. **But every refutation in this chain was written FIXED to
`𝒮ʟ`.** So the refutations cannot be re-instantiated at the ambient
carrier, and six negative results now need a port that generic writing
would have made free. **That is D29's attitude clause and P-h's law,
paid in the negative direction: a countermodel is content too, and a
countermodel written fixed re-instantiates at full price.** MEASURED,
by `Cross385.agda`'s exit 42.

**DOES THE RESIDUE INHERIT `[LJ-1.338]`'s CONTAINMENT?** `[LJ-1.383]`
answers NO for the supply and YES for the repair, and I agree with
both. **I sharpen the second half.** After `[LJ-1.346]`, the repair
containment is not two families for six names. It is ONE restatement
family for the FOUR live names, because the other two are landed and
gone from the telescope. **So one repair does serve all of the live
residue, and the finding is cheaper than `[LJ-1.383]` makes it look.**
MEASURED, by the live telescope at `src/L/Condensation.lagda.md:7233`
and `:7288` against `:7300-7302`.

**C-55 and P-l are respected in my files.** Every type I state sits in
a module telescope, never a record field, and no statement names a
concrete frame's presentation.

## 9. SECONDS, LOAD, RUNS

One Agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. No heap exhaustion. No invocation near 30 minutes. I counted the
slots before EVERY invocation with the brief's exact command,
`ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`: it read 0 once
and 1 for every later run, so one slot stayed free under the cap of two.
Load average between 4.14 and 4.30 throughout, with a sibling live.

| file | exit | user s | note |
|---|---:|---:|---|
| `LJ-1-385/Floor385.agda` | **0** | **11.88** | **my empty-body floor (C-53)**, same imports as my two files |
| `LJ-1-338/ProbeLeaf338.agda` | **0** | 47.80 cold | the residue's source, GREEN today against the FROZEN copy |
| `LJ-1-338/ProbeLeaf338.agda` | **0** | 2.98 warm | same file, interfaces cached |
| `LJ-1-385/Ident385.agda` | **0** | 12.14 | my restatements ARE residue slots 1 and 2 |
| `LJ-1-385/Cross385.agda` | **42** | 4.96 | **EXPECTED RED**, refused at `:76.58-63`, the ONE added line |
| `LJ-1-383/Probe383.agda` | **0** | 1.77 | the sixth refutation, re-run green today |

**On the floor.** My floor is 11.88 s against `Ident385.agda`'s 12.14 s,
so my own file costs about 0.26 s over its imports. `Cross385.agda`
reads BELOW the floor because it stops at the first error and because
interface caching order differs between runs. `[LJ-1.383]`'s own floor
for `Probe383.agda` is `Floor383.agda`, 1.60 s, which is the number the
1.77 s stands against.

## 10. WHAT I DID NOT SETTLE

- **The ambient countermodels.** I measured that the L-side refutations
  cannot be applied at the ambient environment. I did NOT build the
  ambient terms, and I did not price them. **INFERRED small**: the
  ingredients are GenDirty parameters and the construction is
  `[LJ-1.341]`'s, rotated. NOT MEASURED.
- **The fourth non-vacuity layer for the unary conjunct.** No term
  shows the countermodel's container inside the consumer's premise
  class. `[LJ-1.352]` has the binary counterpart; the unary one is
  unwritten.
- **The 113-insertion family price.** Not re-derived, not endorsed.
- **Whether `ProbeLeaf338.agda` would still typecheck against the LIVE
  chapter.** It does not import the chapter, so the question is about a
  file nobody has written. INFERRED that dropping two arguments from
  `:353-356` is the whole edit; NOT MEASURED.
- **`[LJ-1.378]`'s 650-line composite floor.** Out of scope.

## 11. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-385/`: this report,
`Ident385.agda`, `Cross385.agda`, `Floor385.agda`. `src/` holds no probe
of mine and I did not edit it. `LJ-1-336/`, `LJ-1-338/`, `LJ-1-341/`,
`LJ-1-347/`, `LJ-1-348/`, `LJ-1-349/`, `LJ-1-350/`, `LJ-1-351/`,
`LJ-1-352/`, `LJ-1-378/` and `LJ-1-383/` were read and imported, never
edited. I re-ran `ProbeLeaf338.agda` and `Probe383.agda` and changed
neither. The EXPECTED RED files elsewhere were not touched and not
re-run. `src/Everything.lagda.md`, `dev/PLAN.md` and `dev/ledger.toml`
were not opened for writing. No commit, no push, no `git checkout`,
`stash`, `reset` or `clean`. No `make check`. `_build/` holds only
Agda's own interface files for my three modules. No em dash in any
language.
