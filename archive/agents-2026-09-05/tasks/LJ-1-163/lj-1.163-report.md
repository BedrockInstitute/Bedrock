# LJ-1.163 report: `ElemDown` is already supplied, and the brief's premise is false

## 0. THE CRITERION, FIXED BEFORE THE RUN (D-1)

Written before any `agda` process started.

- **Line criterion, taken from the brief and NOT moved:** GO at or below
  **120 in-fence lines** for the supply of `ElemDown` at one real arity.
- **Wall-clock criterion, fixed here:** **20 minutes of wall time per `agda`
  invocation**, under `GHCRTS="-A64m -I0 -M8g"`, ONE process, cap never raised.
  Past 20 minutes I record a **WALL** with its clock and its resident set, I
  comment the walling block out, and I keep the other blocks green. I do not
  move the line criterion on a wall.

## 1. LEAD: GO, AND THE SUPPLY COSTS 0 NEW LINES

**GO against 120 lines.**

**`ElemDown` IS ALREADY SUPPLIED IN `src/`. The brief's premise is FALSE.**

`src/L/BoundedSubset.lagda.md:1568-1569`:

```agda
      elem-down : DR54.ElemDown
      elem-down = HEDC.elem-down
```

**MEASURED.** The master holds ONE agda fence, from `:3` to `:1626`
(`grep -n '^\`\`\`' src/L/BoundedSubset.lagda.md` returns exactly those two
lines), so `:1568` is live code, not a comment. `src/Everything.lagda.md:374`
imports the master.

**The supply typechecks today, and I confirmed it three ways rather than
trusting the build directory.**

1. `_build/2.8.0/agda/src/L/BoundedSubset.agdai` carries a later timestamp than
   the source, so Agda accepted the interface without rechecking.
2. **My own probe imports the master and exits 0.** Agda rechecks a master
   whose source no longer matches its interface, so a green probe import is a
   green master.
3. **My run 4 elaborated the site's `elem-down` itself.** It failed on a
   conversion, `levelIn₁ != levelIn₂`, which Agda can only reach AFTER
   elaborating both `Co₁.elem-down` and `Co₂.elem-down` and their types. A
   term that elaborates is a term that typechecks.

**The brief says: "MEASURED: nothing in `src/` supplies it. `ElemDown` appears
only in `BoundedSubset` itself, and `module _ (ed : ElemDown)` at `:414` takes
it as a hypothesis."** The first clause is FALSE. The second is TRUE and is
what makes the first look true: `ElemDown` does appear only in this master,
because its supplier is in the same master, 58 lines from its end.

**Two numbers, and I keep them apart:**

| | lines |
|---|---|
| NEW lines needed to supply `ElemDown` | **0. It is delivered.** |
| the reusable supply, written fresh outside `Co`, GIVEN the code count | **18**, `agents/tasks/LJ-1-163/ProbeLJ1163A.agda:77-102` |

**18 against a criterion of 120.** The 18 counts non-blank non-comment lines,
**telescope included**, by `[LJ-1.161]`'s and `[LJ-1.162]`'s rule.

### What the 18 are, and what I excluded

| part | lines | what it is |
|---|---|---|
| telescope, `:77-80` | 4 | the stage, the hull's generator, the ordinal's well-order |
| the two module aliases, `:82-83` | 2 | `HullElemDown` and `DownReflect` at the same stage |
| `WithCount`, `:85-102` | 12 | the count hypothesis, `CanonCode`, the canonical-code function `f`, its spec, and `ElemDown` |
| **the gated supply** | **18** | |

| excluded block | lines | why |
|---|---|---|
| BLOCK 2, `Arity`, `:115-160` | 30 | the C-38 obligation. It CONSUMES the supply; counting it would price the consumer inside the supplier. `[LJ-1.161]` excluded its block 2 for the same reason |
| BLOCK 3, `Site`, `:179-227` | 26 | the site instantiation. Not a supply |
| the probe's imports and header | 26 | fixed cost of any probe |

**Whole probe: 227 lines, 100 non-blank non-comment.** I give both so nobody
carries the 18 without the file it came from.

## 2. THE ONE REAL FINDING: THE SUPPLY IS IN THE WRONG PLACE

The delivered `elem-down` sits **inside `module Co`**
(`src/L/BoundedSubset.lagda.md:1408-1412`), and `Co` takes the phase's two
open hypotheses:

```agda
    module Co
      (levelIn : (δ : S) → IsOrd δ → ⟨ δ ∈ˢ HS.C.πX ⟩ → ⟨ Lset δ ∈ˢ HS.C.πX ⟩)
      (cover : (y : S) → ⟨ y ∈ˢ HS.M ⟩ → ∥ ... ∥₁)
```

**So as delivered, the supply is unreachable by anybody who is trying to PROVE
`levelIn` or `cover`.** That is the whole of the phase blocker, and it is a
placement, not mathematics.

**MEASURED, lexically:** lines `1426-1570`, which hold the whole chain
`CodeCount` → `code-inj` → `CC` → `CCn` → `hedF` → `HED` → `HEDC` →
`elem-down`, name **none** of `levelIn`, `cover`, `Cn.`, `β`.

```
awk 'NR>=1426 && NR<=1570' src/L/BoundedSubset.lagda.md \
  | grep -E "levelIn|cover|(^|[^C])Cn\.|β"     # exit 1, no match
```

**MEASURED, by construction:** `agents/tasks/LJ-1-163/ProbeLJ1163A.agda:77-102`
rebuilds the same supply in a module where `levelIn` and `cover` are **not in
scope at all**, from TOP-LEVEL modules of the master only, and it typechecks.
That is a stronger independence witness than any equality test, because the
hypotheses cannot be named.

**CONSEQUENCE, and this is what `[LJ-1.7]` needs.** Moving `elem-down` and the
five definitions above it out of `Co` and up into `BoundedSubsetAt` is a **pure
move**: no proof changes, no line is written. After the move the three open
facts `CrossOut`, `HasLevels` and `Covered` may each consume `ElemDown` while
proving `levelIn` and `cover`, which today they cannot.

**I did not make the move. The brief forbids editing any master, and it is the
orchestrator's call.**

## 3. WHAT THE COMMENT'S ROUTE ALREADY DELIVERS

The comment at `:455-461` names five things. **All five are delivered**, and
four of them are TOP-LEVEL modules of the master. Line counts are non-blank
non-comment.

| the comment's words | delivered at | lines |
|---|---|---|
| "the canonical code of each hull member (the `CodeSelect` least-of pattern)" | `CanonCode`, `:463-498` | **28** |
| "the generic close operation that replaces the top parameters by their codes as constants" | `CloseSyntax`, `:500-588` | **72** |
| "its satisfaction adequacy" | `CloseSem`, `:590-661` | **58** |
| "the `TarskiVaught` instance at every arity assembled from `hull-closed` through the two halves" | `HullElemDown.WithCode.tv`, `:698-757` | **58** |
| "`AtM.TV-thm` turns the instance into `Elementary`, hence `ElemDown`" | `WithCode.elem` `:759-760`, `WithCode.elem-down` `:762-765` | **6** |
| the whole `HullElemDown` module | `:667-765` | **84** |
| the code count, the one thing the top level lacks | `CodeCount`, `:1426-1531` | **98** |
| the site's wiring from the count to `elem-down` | `:1545-1569` | **17** |

**So the route is not partly built. It is built end to end.** `[LJ-1.161]`'s
"the residue of all three is `ElemDown`" was right about the dependency and
wrong about the debt: the residue was already paid.

**One correction to the brief's own reading.** The brief says "`down-reflect`
at `:446` already runs through `hull-closed`, and `CanonCode` at `:463` is the
module that comment names", offering these as the delivered *pieces*. They are
the two SMALLEST delivered pieces. The brief did not look past `:463`, and
`CloseSyntax`, `CloseSem` and `HullElemDown`, 214 of the 242 lines, sit
between `:500` and `:765`, inside the scope the brief itself set
(`:353-470` then `:660-700`). **The scope's second window stops at `:700`, and
`tv` ends at `:757`.**

## 4. THE PROBE

`agents/tasks/LJ-1-163/ProbeLJ1163A.agda`, 227 lines, 100 non-blank
non-comment. It is tracked, it lives in the task directory, and it was run
there. **No `postulate`, no hole, no unsolved meta**; `--safe` is on in the
OPTIONS header and every run below exited 0 unless the table says otherwise.

### BLOCK 1, `:77-102`. THE LIFT. 18 lines. GO.

`ElemDown` from top-level modules only, with the code count as its single
hypothesis:

```agda
module Lifted (α lam : S) (ordα : IsOrd α) (ordλ : IsOrd lam)
  (w : SWO {ℓ} ⟪ α ⟫)
  (X : S) (X⊆L : (x : S) → ⟨ x ∈ˢ X ⟩ → ⟨ x ∈ˢ Lset lam ⟩)
  (∅∈λ : ⟨ ∅ ∈ˢ lam ⟩) where
  ...
    ed : DR.ElemDown
    ed = W.elem-down
```

**Green in 2.9 s.**

### BLOCK 2, `:115-160`. C-38 AT ONE REAL ARITY. 30 lines.

The brief's C-38 guard is the reason this block exists, and it is earned:
**MEASURED, `grep -rn "elem-down" src/` finds the delivered supply's
DEFINITION at `:1568-1569` and NO USE ANYWHERE.** By C-35 it is a delivered
block with no consumer, and it is the fourth of that class this phase after
`[LJ-1.161]`'s three.

So the probe applies it at concrete arities, not just at the interface:

- `at0`, arity **0**, at `∃̇ (var zero ≐ var zero)`.
- `at1`, arity **1**, at `var zero ∈̇ var zero`, with a real hull member in the
  environment.
- `at2`, arity **1 with a constant**, at `con p ∈̇ var zero`, so the
  relabelling `mapFo inL` is not the identity on the constants.
- `reflect`, the master's OWN consumer `DownReflect.down-reflect` (`:443-451`),
  fed the supply. This is the consumer the master wrote for `ElemDown` and
  never connected.

**Green in 4.1 s with BLOCK 1.**

### BLOCK 3, `:179-227`. THE SITE.

`Devlin55.BoundedSubsetAt` instantiated at its fifteen parameters, then `Co`,
then `same : Co₁.elem-down ≡ LW₁.ed` by `refl`. This puts the site's delivered
supply against BLOCK 1's lift at the site's own count, to show the lift is not
a look-alike.

**Result: see section 5. This block met a wall.**

### THE TEST I TRIED AND WITHDREW, and why

I first wrote `indep : Co₁.elem-down ≡ Co₂.elem-down` by `refl`, over two
different `(levelIn, cover)` pairs. **It failed in 6.5 s** with

```
levelIn₁ δ x₁ x₂ != levelIn₂ δ x₁ x₂
```

**INFERRED, not measured:** this is Agda comparing two applications of the same
module-generated constant argument-wise. A module application binds every
parameter of the telescope whether the body reads it or not, so
`Co₁.elem-down` is `Co.elem-down levelIn₁ cover₁`, and the comparison reaches
the parameters before it reaches the body. **I do not read this failure as
evidence of dependence**, and I say so plainly rather than quoting it as a
negative. The independence is settled by BLOCK 1, which does not name the
hypotheses, and by the lexical measurement in section 2.

## 5. THE WALL

**BLOCK 3 met the wall-clock criterion I fixed in section 0.**

| | |
|---|---|
| what walled | `same : Co₁.elem-down ≡ LW₁.ed`, by `refl`, at the full `Devlin55.BoundedSubsetAt` instantiation |
| **wall clock** | **20:42.15 total, 1236.01 s user, 99 % CPU** |
| **resident set** | **2074 MB**, flat from 2005 MB at 11:42; it was not climbing |
| heap | `GHCRTS="-A64m -I0 -M8g"`, ONE process, **cap never raised** |
| heap exhaustion | **NO.** 2.07 GB against an 8 GB cap. The cap was never approached |
| how it ended | **SIGTERM** at the criterion, by my own guard |
| surgery | **NONE.** P-i: no surgery on a walling term. It is commented, not rewritten, at `ProbeLJ1163A.agda:213-227` |
| the rest of the probe after commenting | **GREEN, exit 0, 16.7 s** |

**Diagnosis, INFERRED:** `refl` at this type forces the conversion checker
through the whole `WithCode.tv` term at every arity, and `tv` runs through
`CloseSem.⊨-close`, a fourteen-clause induction over the syntax, at both the
stage semantics and the hull semantics. `[LJ-1.161]` measured a comparable wall
at 20 minutes and 9.03 GB on a `refl` forcing a count over a nested table.
**This is the same class and I did not re-measure it as a new one (P-l).**

**The wall costs the report nothing, and I say exactly what it does cost.**
`same` would have shown the lift and the site's supply are the same TERM. What
survives the wall is everything the verdict rests on: BLOCK 1 is a supply,
green in 2.9 s; BLOCK 2 applies it at three concrete arities and feeds the
master's own consumer; and after commenting `same`, **`Co₁` and `LW₁` still
elaborate**, so the site instantiates and BLOCK 1's lift accepts the site's own
count `CC.count`. **Only the judgmental identification of the two terms is
unmeasured, and I claim nothing about it.**

### Run table

| run | probe state | result | wall clock |
|---|---|---|---|
| 1 | BLOCK 1, module named `Lift` | scope error, `Lift` shadows `Cubical.Foundations.Prelude` | 3.1 s |
| 2 | BLOCK 1, renamed `Lifted` | **exit 0** | **2.9 s** |
| 3 | BLOCKS 1 and 2 | **exit 0** | **4.1 s** |
| 4 | + BLOCK 3 with `indep` | error, `levelIn₁ != levelIn₂` | 6.5 s |
| 5 | + BLOCK 3 with `same` only | **WALL, SIGTERM, RSS 2074 MB, no heap exhaustion** | **20:42.15** |
| 6 | BLOCK 3 with `same` commented out | **exit 0** | **16.7 s** |

## 6. DD4: MAXIMIZE WHAT THE TWO PROOFS SHARE

**MEASURED. 158 of the 242 delivered lines name NO tower at all, and the other
84 name it on 5 lines.**

| block | lines | tower names | class |
|---|---|---|---|
| `CloseSyntax` `:500-588` | 72 | **0** | TEMPLATE. Generic in the constant type `K`; pure syntax |
| `CloseSem` `:590-661` | 58 | **0** | TEMPLATE. Generic in the ZF structure `𝒮` and in `K` |
| `CanonCode` `:463-498` | 28 | **0** | TEMPLATE. Ordinal, code type and count only; no `Lset`, no `Def` |
| `HullElemDown` `:667-765` | 84 | **5** | `:668` telescope, `:670` `module ASt = AtStage α ordα`, `:679` `CseL` at the stage, `:687` and `:737` the two `Σ≡Prop` at `Lset α` |
| **total** | **242** | **5** | |

`grep -c "Lset\|Def\|𝒟ₒ"` over each of the first three blocks returns **0**.

**The fork point is `AtStage`, `:670`.** `L.Hull:148-159` fixes it to `Lset α`,
so a J tower needs its own `AtStage`, and everything downstream of `ASt.*`
follows for free. The other 4 lines are `Lset α` written out where the stage
module would have served, so they are a rewrite, not a second fork. **I did not
rewrite them and I claim no saving from doing so.** `L.Hull:55-60` already says the term algebra under it was written generic
"so the J tower instantiates the same core (DD4)", and this measurement
confirms the same shape one level up: **elementarity is not tower content, and
the delivered code already treats it that way.**

**My own 18 lines: 1 names the tower.** `Lset lam`, in the telescope's `X⊆L`.

**I did not write a fixed version and I did not write a J-tower variant, so I
give NO generic-versus-fixed delta.** `[LJ-1.162]` reported the first site this
phase where the generic form was not within two lines of the fixed one. **I
cannot extend or contradict that measurement, because at this site I never had
to choose:** `CanonCode`, `CloseSyntax` and `CloseSem` were already generic when
I arrived, and my 18 lines only apply them. **The number I do give is the fork
point: ONE line, `:670`, `module ASt = AtStage α ordα`.**

## 7. WHAT THE THREE OPEN FACTS COST NOW

**`[LJ-1.7]`'s gate is complete, and `ElemDown` is not what is left.**

| fact | its residue after this task |
|---|---|
| `CrossOut` | 163 lines, `[LJ-1.161]` and `[LJ-1.162]`. **Unchanged.** |
| `HasLevels` | its transport machine is delivered, `:195-196` and `:250-251`. **Unchanged.** |
| `Covered` | delivered likewise. **Unchanged.** |
| `ElemDown`, the claimed common residue | **0 lines. Delivered at `:1568`. It needs a MOVE out of `Co`, not a proof.** |

**One more C-35 reading, MEASURED, offered without an opinion:**
`grep -rn "Devlin55\|BoundedSubsetAt" src/` outside the master returns nothing.
The whole assembly, `theorem : ⟨ x ∈ˢ Lset κ ⟩` at `:1621` included, has no
consumer either. That is the known STRUCTURE-ONLY state of `[LJ-1.7]` and I
report it only so the `elem-down` finding is not read as unique.

**MEASURED negative, and it is the one worth carrying:** the phase spent
`[LJ-1.161]`, `[LJ-1.162]` and this dispatch pricing a term the tree already
held. The cost was not the mathematics. It was that a delivered supply 58 lines
from the end of a 1626-line master, inside a module whose two hypotheses are
the phase's open facts, reads exactly like an unmet obligation from any `grep`.

## 8. ARCHIVE USED (DD18)

**The archive holds elementarity and the Tarski-Vaught instance, and the live
tree's copy is a direct descendant. SHAPE only, per the brief.**

- **`archive/src/2026-08-09-rud-route/L/Hull.lagda.md:130-135`** states
  `Elementary` and `TarskiVaught` in the same two shapes the live
  `src/L/Hull.lagda.md:174-181` uses today.
- **`:169-176`** holds `elem→TV` and `TV→elem`; **`:248-249`** holds `TV-thm`
  as the same pair. The live `src/L/Hull.lagda.md:306-307` is the same line.
- **`:396-398`** holds `hull-closed` at the archive's own hull, the same
  least-witness Tarski instance the live `HullElemDown.tv` consumes.
- **`:420-429`** is the archive's own account of what its route left open: the
  full elementary reading and minimality, both reduced to "the adequate
  witness". **Taken as shape: the archive already knew the criterion was the
  machine and the least witness was the content.**
- **`:14-17`** records that the archive settled the elementarity flag **by
  building**, not by hypothesis.

**So the answer to the brief's archive question is: the archive fares BETTER
than `CrossOut` did.** `[LJ-1.162]` found `CrossOut` there only as a
hypothesis; `ElemDown`'s analogue is there as a **built** `TV-thm` plus a built
`hull-closed`, and the live tree inherited both.

- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:5-8`: Devlin's
  statement is for an elementary substructure of a level, and that chapter
  treated the elementary-substructure half as a separate, carrier-neutral
  probe. **Consistent with section 6's DD4 measurement.**
- `archive/src/2026-08-09-rud-route/L/Definability.lagda.md`: read, nothing
  bearing on `ElemDown`. I say so rather than pad the section.
- `agents/tasks/LJ-1-161/` and `agents/tasks/LJ-1-162/`, read whole.
  `agents/tasks/LJ-1-161/lj-1.161-report.md:279` is the sentence this brief was
  built on: "That is `ElemDown`, the elementarity residue". **It named the term
  correctly and did not check whether the term was supplied.**

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read whole for 5.1 to 5.5.

**What elementarity does Devlin assume in 5.5, at what level, and does he prove
it or cite it?**

- **He ASSUMES full elementarity, `M ≺ L_λ`, and he PROVES it.** 5.5's proof
  (`devlin-II5.md:147-158`, from `dev2.txt:1372-1384`) takes `M ≺ L_λ` from
  **5.4**, which is a corollary of **5.3**.
- **5.3** (`:118-133`, `dev2.txt:1329-1335`) states `M ≺ L_α` for the definable
  hull and proves it **by verifying Tarski's criterion** through a least-witness
  argument over `<_L`: for `φ(v₀)`, form
  `ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))`. **Proved, not cited.**
- **5.1** (`:42-66`, `dev2.txt:1071-1078`) is the equivalence that licenses
  that move: `N ≺ₙ M` iff every non-empty `Σ₁`-definable subset of `M` with
  parameters from `N` meets `N`. **Devlin proves 5.1 in the chapter**, by
  induction on formula length, both directions. He does not cite it.
- **The level actually USED downstream is weaker than what 5.3 delivers.** The
  condensation chain (`:102-115`, `:189-193`) needs only `Σ₁`-elementarity, and
  at one point only "`Σ₁`-elementarity at quantifier-free matrices", which the
  memo marks "strictly weaker than full `Σ₁`-elementarity".

**How the tree matches him, and where it is stronger.** `AtM.TV-thm`
(`src/L/Hull.lagda.md:306-307`) is 5.1: the criterion-to-elementarity
equivalence, proved by induction over the full syntax, both directions.
`H.hull-closed` is 5.3's least-witness instance. `HullElemDown.tv` is the
Tarski-Vaught instance at every arity, and `WithCode.elem` is `TV-thm .snd tv`.
**The tree proves the FULL equivalence where Devlin's own chain only needs the
`Σ₁` half**, and `ElemDown` is the downward direction of it.

## 10. CLASSIFICATION OF EVERY NEGATIVE

| claim | verdict |
|---|---|
| nothing in `src/` supplies `ElemDown` | **MEASURED FALSE.** `src/L/BoundedSubset.lagda.md:1568-1569`, live, one fence, imported by `Everything` |
| `ElemDown` is FALSE at the hull, or needs a hypothesis the hull cannot pay | **MEASURED FALSE.** It is proved at the hull today, from `hull-closed` through `AtM.TV-thm` |
| the supply exceeds 120 lines | **MEASURED FALSE.** 0 new; 18 for the reusable lift, exit 0 in 2.9 s |
| the delivered supply has a consumer | **MEASURED FALSE.** `grep -rn "elem-down" src/` finds the definition and no use. C-35 |
| the supply depends on `levelIn` or `cover` | **MEASURED FALSE**, two ways: the lexical sweep of `:1426-1570` matches nothing, and BLOCK 1 rebuilds it with the hypotheses out of scope |
| `Co₁.elem-down ≡ Co₂.elem-down` fails, therefore the supply depends on the hypotheses | **INFERRED FALSE.** The failure is Agda's argument-wise comparison of a module application. Not offered as evidence |
| the comment's route is partly built | **MEASURED FALSE.** All five named pieces are delivered, 242 lines |
| the archive holds only a hypothesis, as it did for `CrossOut` | **MEASURED FALSE.** `archive/.../L/Hull.lagda.md:248-249` and `:396-398` hold built `TV-thm` and built `hull-closed` |
| `same` fits the wall-clock criterion | **MEASURED FALSE.** It walled. Section 5 |
| BLOCK 3's wall moves the gate | **MEASURED FALSE.** BLOCK 1 is 18 lines and exits 0 without BLOCK 3 |

## 11. WHAT I DID NOT DO, AND THE STOP LINES I KEPT

- **No master edited.** The move out of `Co` is named, priced at zero lines, and
  left to the orchestrator.
- **No `src/` probe.** The probe is `agents/tasks/LJ-1-163/ProbeLJ1163A.agda`.
- **No `postulate`, no hole, no unsolved meta**, and `--safe` on.
- **No commit, no push, no `git checkout .`, no `stash`, no `reset`, no
  `clean`.**
- **`make check` not run.** The orchestrator runs it.
- **ONE agda process throughout, `GHCRTS="-A64m -I0 -M8g"`, cap never raised.**
- **No surgery on the walling term (P-i).**

## 12. STANDING FIGURES

`.venv/bin/python scripts/ledger.py --brief`: standing **28,940 lines over 85
masters**, from HEAD; thresholds SUSPENDED per the ledger header; endpoint
REFUSED; DD5 benchmarks NOT MEASURED. **I quote no size figure from any
paragraph.**

## 13. MANDATORY RULES, ANSWERED

- **D-1.** Criterion fixed before the run, wall-clock included. Section 0.
- **C-38 as extended.** Instantiated at arity 0, arity 1, and arity 1 with a
  constant, then fed to the master's own consumer. Section 4 BLOCK 2.
- **C-35.** The delivered supply has NO consumer. Reported as the finding it is.
- **P-i.** No surgery on the walling term.
- **P-l.** The wall is assigned to `[LJ-1.161]`'s measured class by inference
  and labelled INFERRED. I did not re-price it from that comparable.
- **C-12.** One agda process, `-M8g`, cap never raised, load beside the seconds.
- **C-22.** This file was created as a skeleton before the first agda run and
  filled as each answer landed.
- **C-39, C-40.** The brief's central assumption is contradicted in section 1,
  first line. The site hypotheses in BLOCK 3 are telescope, **not discharged**,
  and I claim nothing about them.
- **DD8.** The widest unmeasured term was "how much of the comment's route is
  built". Section 3 measures it at `file:line`.
- **DD4.** Section 6, measured, with the fork point named.
- **DD23.** No mathematical prose touched.
