# LJ-1.178 report: `levelIn` and `cover` built, and the term that stays

tier: opus (version `override`). **Two probes were written. Both ran GREEN. No
master was changed. No commit, no push.** Every negative is marked **MEASURED**
or **INFERRED**. Written incrementally (C-22).

## 0. LEAD

### 0.1 What built

**`levelIn` and `cover` are BUILT at the real site, as functions of FOUR named
hypotheses.** `agents/tasks/LJ-1-178/ProbeLJ1178B.agda`, exit 0, 10.25 s.

The probe enters `Devlin55.BoundedSubsetAt` with the site's own telescope, gives
`levelIn` and `cover` at their **verbatim** site types, applies `BA.Co`, and
reads `theorem` out. The type of `theorem` in the probe is `⟨ x ∈ˢ Lset κ ⟩`,
which is the type at `src/L/BoundedSubset.lagda.md:1621`.

### 0.2 Does `theorem` derive?

**NO, and I mark that MEASURED.** Four hypotheses stay open. **One of them is a
NEW WALL and three of them are content nobody has written yet.**

**But `theorem` now derives from a chain that TYPECHECKS end to end.** Before
this task the phase held two hypotheses with no derivation at all. After it, the
gap is four named statements, and each one is about ONE formula.

### 0.3 The four, and what each one is

| hypothesis | what it says | state |
|---|---|---|
| `amb` | Devlin's (a) at the **AMBIENT** carrier: an ambient reading of the level-hood formula pins the value | **NEW WALL.** Section 3 |
| `sl` | the stage believes every ordinal has a level | **OPEN.** The priced residue, and it is at the STAGE |
| `sc` | the stage believes every set lies in a level | **OPEN.** Same class |
| `s₁` | the level-hood formula is Σ₁ | **DELIVERED in shape**, and section 2.5 measures the missing piece at 2 lines |

### 0.4 What the build DISCHARGED, and it is the result

**`[LJ-1.160]` left THREE facts open at the collapse image: `CrossOut`,
`HasLevels` and `Covered`. TWO OF THE THREE ARE NOW DISCHARGED.**

`HasLevels` and `Covered` are **derived** from two stage facts, by two transports
that the tree already delivers:

1. **the hull's elementarity**, `src/L/Hull.lagda.md:174-176`, supplied at the
   site by `HEDC.elem` (`src/L/BoundedSubset.lagda.md:759-760`, wired `:1544`);
2. **the collapse's satisfaction iso-invariance**,
   `src/L/BoundedSubset.lagda.md:195-196` and `:250-251`, at `CollapseIso`
   (`:321`).

**Both fit probe A's types with no adapter. MEASURED**, probe B lines 78 to 85.

**So the open facts moved off the collapse image and onto the STAGE.** A stage
fact names no hull and no collapse. `src/L/BoundedSubset.lagda.md:901-902`
already calls that content "the priced residue".

### 0.5 The term I could not write, in one line (C-36)

```agda
AmbientRead = (v b : S) → IsOrd b
            → ⟨ (v ∷ b ∷ []) AbsP.⊨ᵛ embed φ₀ ⟩ → v ≡ Lset b
```

**The tree delivers this read-off at the CLASS carrier `L` and nowhere else**
(`Lset-only`, `src/L/Hierarchy.lagda.md:334-335`). **The bypass lands in the
AMBIENT universe, because `σ₁-up` at a transitive set carries an inner belief to
`𝒮ᵥ`** (`src/FOL/Absoluteness.lagda.md:182-184`). Section 3 is the evidence.

## 1. THE SUPPLY SEARCH, RUN BEFORE ANY LINE WAS WRITTEN

`[LJ-1.163]` measured that a grep which excluded one file cost three dispatches.
**I report every search I ran, with its result.**

| # | search | scope | result |
|---|---|---|---|
| S1 | `git grep -n "levelIn\|level-in"` | **whole tree**, tracked | Only `agents/` reports and briefs, plus the two declaration sites `src/L/BoundedSubset.lagda.md:917-919` and `:1555-1558`. **Nothing supplies either. MEASURED** |
| S2 | `git grep -n "CrossOut\|HasLevels\|Covered\|crossOut\|hasLevels\|covered"` | `src/`, `archive/` | In `src/` the only hits are prose and an unrelated `covered` at `src/L/Coding/Environment.lagda.md:543`. The face exists only in `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`. **MEASURED** |
| S3 | `git grep -n "levelHood\|LevelHood"` | `src/` | `LevelHood` (`:74`), `levelHoodB` (`:108`), `Δ₀-levelHoodB` (`:113`), `levelHoodΣ₁` (`:142`), `Σ₁-levelHood` (`:145`), `LevelHood0` (`:840`), all in `src/L/BoundedSubset.lagda.md`. **The formula and its Σ₁ witness ARE delivered.** Their instantiation is not |
| S4 | `git grep -n "≡ Lset"` | `src/`, all masters | 35 hits. The tower read-off is `Lset-only` at `src/L/Hierarchy.lagda.md:334`, and `ride-only` at `src/L/Condensation.lagda.md:419-422`. **This is the file I thought I already knew, and it held the answer** |
| S5 | `git grep -n "⊨ᵛ"` | `src/`, all masters | **Five files only**: `FOL/Absoluteness`, `L/Axioms/Separation`, `L/Condensation`, `L/Definability`, `L/Ordinal/Stages`. **`L/Hierarchy` is NOT among them.** So no ambient read-off of the tower graph exists. **MEASURED, and it is the wall's evidence** |
| S6 | `git grep -n "Lset-only\|Lset-defines\|ride-only\|ride-defines"` | `src/` | 8 consumers, in `L/Choice/Before`, `Faithful`, `Internal`, `Limit`, `Order`, and `L/Condensation`. **Every one reads at the class carrier. MEASURED** |
| S7 | `git grep -n "πX"` | `src/` outside `V/Collapse` | Only `L/BoundedSubset`. **No fact of the form `πX ⊆ L` exists. MEASURED** |
| S8 | `git grep -n "mapΣ₁\|mapΠ₁"` and `"erase-Σ₁\|erase-Δ₀"` | `src/` | `mapΔ₀` is delivered (`src/FOL/Manipulation/Relabelling.lagda.md:209`). **`mapΣ₁` does NOT exist. `erase-Σ₁` does NOT exist**; `erase-Δ₀` does (`src/L/BoundedSubset.lagda.md:825`). **MEASURED**, and section 2.5 prices it |

**The one search that changed the task is S5.** It turned a suspicion into a
measurement, and it decided the report's lead.

## 2. THE BUILD

`agents/tasks/LJ-1-178/ProbeLJ1178A.agda`, exit 0, 2.88 s, 301 non-blank
non-comment lines. `agents/tasks/LJ-1-178/ProbeLJ1178B.agda`, exit 0, 10.25 s,
65 lines.

### 2.1 Section 1, the face and the assembly

The face is stated at **one parameter-free formula `φ₀`**, so the SAME statement
reads at the stage, at the hull and at the collapse image. `embed-stable` is the
one line that makes this work: a parameter-free formula survives every
relabelling.

`levelIn` and `cover` come out at their verbatim site types. **This re-measures
`[LJ-1.160]`'s 16 lines at a face that is now generic in the formula, not only
in the carrier.**

### 2.2 Section 2, `CrossOut` in ONE line

```agda
crossOut s amb v b ob bel =
  amb (fst v) (fst b) ob (Cr.AbsP.σ₁-up s (v ∷ b ∷ []) bel)
```

**MEASURED: `CrossOut` costs ONE line, given `AmbientRead` and the Σ₁
certificate.** The whole first open row of `[LJ-1.160]` section 3.3 is that line
plus the ambient statement.

### 2.3 Section 3, the two transports

Four legs, one line each: `fromStage`, `toStage`, `toImage`, `fromImage`. Each
one moves a parameter-free formula between two carriers. `fromStage` and
`toStage` ride the hull's elementarity. `toImage` and `fromImage` ride the
collapse's iso-invariance.

**Neither leg mentions `Lset`. The wall `π (Lset m') ≡ Lset (π m')` appears
nowhere in either probe. MEASURED**, by grep over both files.

### 2.4 Sections 4 and 5, `HasLevels` and `Covered` DISCHARGED

`hasLevels` takes the ordinal premise at the image, moves it to the hull, moves
it to the stage, applies the stage fact, and brings the value back. `covered`
does the same for the three-variable cover sentence.

**`Covered` needed two pieces the tree does not deliver, and both are cheap.**

1. **The ordinal atom at a SLOT.** The delivered `isOrdAt`
   (`src/L/BoundedSubset.lagda.md:795`) sits at slot zero of arity one only, and
   its two readings sit at one interpretation
   (`:813-821`). The probe restates both **generic in the slot and in the
   interpretation**, at 12 lines. **DD4: the J tower reuses them unchanged.**
2. **Relabelling and renaming commute.** `mapFo-ren`, 14 lines, the same shape
   as `mapFo-ext` at `src/L/BoundedSubset.lagda.md:387-400`. **MEASURED
   MISSING** from `src/FOL/Manipulation/Relabelling.lagda.md`.

### 2.5 The Σ₁ certificate, priced

**`mapΣ₁` does not exist in the tree (S8). Two clauses close it**, and the probe
carries them:

```agda
mapΣ₁ f (σ-Δ₀ d) = σ-Δ₀ (mapΔ₀ f d)
mapΣ₁ f (σ-∃ s)  = σ-∃ (mapΣ₁ f s)
```

**So `s₁` is not a wall.** `Σ₁-levelHood` is delivered
(`src/L/BoundedSubset.lagda.md:145-146`) at arity 3, with `v`, `γ` and the bound
`K` free. One more `σ-∃` binds `K` and leaves the two-variable form.
`erase-Σ₁` is the mirror of the delivered `erase-Δ₀` (`:825`), also two extra
clauses. **INFERRED at 4 to 8 lines**, because I did not write the erase half.

### 2.6 Section 6 and probe B, the site

Probe B enters `BoundedSubsetAt` with its own telescope and checks the four
delivered inputs against probe A's types:

- `elem = BA.HEDC.elem` against `Sx.A.Elementary`. **GREEN.**
- `isoFwd`, `isoBwd` from `CIso.I.iso-inv` and `iso-inv-bwd`. **GREEN.**
- `BA.HS.C.πX-trans`, `C.πX-intro`, `C.πX-member`, `C.π`. **GREEN.**

Then `module Co = BA.Co levelIn cover` and `theorem = Co.theorem`. **GREEN.**

**This is the measurement that turns a shape match into a build.** `[LJ-1.51]`
recorded the hull's elementarity as "an unbuilt TV/ElemDown instance"
(`agents/tasks/archive/LJ-1-51/lj-1.51-report.md:141-143`). **It is built now,
and probe B is its first consumer at this site.**

## 3. THE NEW WALL, NAMED AND PLACED

### 3.1 The statement

**Devlin's (a), at the ambient carrier.** `dev/literature/devlin-II5.md:93-96`
quotes it:

> (a) ∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]

**This is a statement of the real universe.** The digest's chain confirms it at
`:102-106`: "1.9.15 converts M's satisfaction of the Σ₀ matrix into **ambient**
Φ; (a) turns Φ into `v = L_γ`".

### 3.2 Why the tree cannot supply it today

**The whole coding and adequacy stack is instantiated at the CLASS carrier `L`.**

- `src/L/Coding/Sequence.lagda.md:59` opens `hPropStructure 𝒮ʟ` and `:61-62`
  renames `AbsL._⊨ᵐ_` to `_⊨_`. So `StepAt`, `ApproxAt` and `LsetGraphAt` are
  read at `L`.
- `src/L/Hierarchy.lagda.md:73` and `:78-79` do the same. So `Lset-only`
  (`:334-335`) and `Lset-defines` (`:646-648`) read at `L`.
- `src/L/Condensation.lagda.md:419-428` rides both at `L`, and names them
  "delivered theorems, ridden here at the class carrier" (`:415-417`).

**The bypass lands somewhere else.** `σ₁-up` at a transitive set `P` gives the
`𝒮ᵥ` reading, not the `L` reading (`src/FOL/Absoluteness.lagda.md:182-184`
against `:66-71`). **MEASURED: `⊨ᵛ` occurs in five masters and `L/Hierarchy` is
not one of them** (S5).

### 3.3 The second road, and it is circular

**`abs₀` is a PATH, so it runs both ways** (`src/FOL/Absoluteness.lagda.md:122`).
So the ambient reading comes back down to `L` **if every environment member is
constructible**. That needs `πX ⊆ L`.

**`πX ⊆ L` is not supplied (S7). And `cover` PROVES it**: `πX⊆Lβ`
(`src/L/BoundedSubset.lagda.md:997-1008`) uses `cover` alone and concludes
`πX ⊆ Lset β`. **So supplying `πX ⊆ L` to get `cover` is circular. INFERRED**,
from reading `:997-1008`, and I did not try to break the circle.

### 3.4 What the wall is NOT

**It is not `[LJ-1.51]`'s wall.** `π (Lset m') ≡ Lset (π m')` appears in neither
probe. **MEASURED by grep.** `[LJ-1.160]`'s finding stands: the collapse never
has to commute with the level construction.

**It is not a refutation.** The statement is Devlin's own lemma and it is true.
**What is missing is an instance at a second carrier of machinery the tree has
at one carrier.** C-36 binds and I obey it: I do not claim no supply exists.

### 3.5 The price I will NOT give

**I give `AmbientRead` no line figure, and I say why.** Its supply is one of two
things, and the two are different chapters:

1. the read-off stack (`StepAt`, `ApproxAt`, `LsetGraphAt`, `approx-val`,
   `step-Lset`, `Lset-only`) re-stated generic in a transitive carrier; or
2. `πX ⊆ L` by some non-circular route.

**C-40 binds: I name the term my own figures do not cover.** P-l binds too. **A
comparable from the class-carrier instance is a hypothesis about the ambient
instance, not a price**, so I do not transfer one.

## 4. MEASUREMENTS

**The machine was NOT quiet. Load averages 3.25 to 5.96, one user, 2026-08-14
08:35 to 08:51. Two siblings were building.** I report the load beside every
figure, as the brief instructed.

| run | file | result | seconds |
|---|---|---|---|
| probe A | `agents/tasks/LJ-1-178/ProbeLJ1178A.agda` | **exit 0** | warm-up 3.87, kept **2.96, 2.78, 2.91**, mean **2.88** |
| probe A, no-op | same | exit 0 | **1.77** (interface load only) |
| probe B | `agents/tasks/LJ-1-178/ProbeLJ1178B.agda` | **exit 0** | warm-up 10.96, kept **10.00, 10.33, 10.42**, mean **10.25** |
| probe B, no-op | same | exit 0 | **2.69** |

`GHCRTS="-A64m -I0 -M8g"`. **One agda process. The cap was never raised. No heap
exhaustion.**

| figure | probe A | probe B |
|---|---:|---:|
| all lines | 505 | 108 |
| non-blank | 419 | 87 |
| non-blank non-comment | **301** | **65** |

**The honest reading of the seconds.** Probe A's own elaboration is
`2.88 - 1.77 = 1.11 s` over 301 lines. Probe B's is `10.25 - 2.69 = 7.56 s` over
65 lines, and **almost all of that is entering `BoundedSubsetAt`, not my code**:
the site's telescope alone forces the whole `Co` body to elaborate.

**Against DD24's figure I report the numbers and do not judge.** A probe has no
` ```agda ` fences, so the ledger's counting rule does not apply to it, and
neither probe is a master. **Nothing in this report is a size claim on the GCH
side.** `scripts/ledger.py --brief`: standing **29,700 lines over 88 masters**,
from HEAD, thresholds SUSPENDED.

**Checkers.**

- `scripts/lint-agda.py --check` on both probes: **exit 0**.
- `scripts/check-unbound-hyp.py` on both probes: **clean (2 files)**.
- `scripts/check-probes.py --check`: **clean**, 1,821 tracked files.
- **No `make check`.** The orchestrator runs it.

## 5. DD4

**Maximize the code the two proofs share, and write it generic.**

### 5.1 The measurement

**Probe A names `Lset` ELEVEN times in 301 code lines, and every one is in a
TYPE.** No body mentions the tower. The eleven are: the import, `CrossOut`'s
right-hand side, `levelIn`'s three, `cover`'s two, `AmbientRead`'s one, the
stage inclusion in `Site`'s telescope, and `Whole`'s two re-statements.

**Everything else is generic in five things at once**: the carrier `P`, its
transitivity, the hull `M`, the map `pi`, the stage `α`, and **the level-hood
formula `φ₀`**.

### 5.2 What the J tower re-instantiates

**The J tower supplies its own `φ₀` and its own two stage facts. Nothing else
changes.** `dev/literature/devlin-II5.md:374-382` classes the level-hood formula
row C1 as PER-TOWER, and rows C3 and C4, the absoluteness and the transfer, as
**EITHER TOWER**. **Probe A is rows C3 and C4, and it is 301 lines that both
towers pay once.**

The four helpers the probe had to write are all tower-free: `embed-stable`,
`mapΣ₁`, `isOrdSlot` with its slot-generic reader, and `mapFo-ren`. **Not one of
them names a tower. They belong in `FOL/`, not in `L/`.**

### 5.3 Generic was the SHORT form again

**No stop-line pushed me toward writing fixed.** Writing the face at one
parameter-free formula is what let ONE `toImage` serve the ordinal atom, the
level-hood formula and the membership atom. A carrier-fixed version would have
needed three copies of each transport.

**This agrees with `[LJ-1.159]:263` and `[LJ-1.151]`, and it is a third
independent site.**

## 6. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `theorem` derives today | **MEASURED FALSE.** Four hypotheses stay open. Probe B `module Open` |
| `levelIn` and `cover` are supplied outright | **MEASURED FALSE.** They are functions of the four |
| the tree already supplies `levelIn` or `cover` | **MEASURED FALSE.** S1 |
| the tree already supplies `CrossOut`, `HasLevels` or `Covered` | **MEASURED FALSE.** S2 |
| `HasLevels` and `Covered` need new crossing content | **MEASURED FALSE.** Both derive from two stage facts and two delivered transports. Probe A sections 4 and 5 |
| the hull's elementarity is unbuilt | **MEASURED FALSE.** `BA.HEDC.elem` fits probe A's `Elementary`. Probe B line 78 |
| the collapse iso needs an adapter at this site | **MEASURED FALSE.** `CIso.I.iso-inv` fits with no adapter. Probe B lines 81-85 |
| `[LJ-1.160]`'s 16 lines do not reach the real site | **MEASURED FALSE.** Probe B reaches `theorem` through them |
| the wall `π (Lset m') ≡ Lset (π m')` is needed | **MEASURED FALSE.** It appears in neither probe |
| the tree supplies the ambient read-off | **MEASURED FALSE.** S5 and S6. `⊨ᵛ` occurs in five masters and `L/Hierarchy` is not one |
| the tree supplies `πX ⊆ L` | **MEASURED FALSE.** S7 |
| `πX ⊆ L` is a way around the wall | **INFERRED FALSE.** `cover` proves it (`:997-1008`), so the road is circular |
| `mapΣ₁` is delivered | **MEASURED FALSE.** S8. Two clauses close it, and the probe carries them |
| `erase-Σ₁` is delivered | **MEASURED FALSE.** S8. Only `erase-Δ₀` exists (`:825`) |
| `mapFo-ren` is delivered | **MEASURED FALSE.** 14 lines, and the probe carries them |
| the slot-generic ordinal atom is delivered | **MEASURED FALSE.** `isOrdAt` sits at one slot and one interpretation (`:795`, `:813-821`) |
| `AmbientRead` is false | **NOT CLAIMED.** It is Devlin's own lemma (a). C-36 binds |
| the ambient read-off is cheap | **NOT CLAIMED, and I refuse a figure.** Section 3.5 |
| the two stage facts are cheap | **NOT CLAIMED.** They are the level-hood instantiation, and P-m classes instantiation as the expensive content class |
| probe A's seconds price a master | **MEASURED FALSE.** A probe has no fences and is not a master. Section 4 |

## 7. WHAT `[LJ-1.7]` STILL NEEDS

**Exactly four statements, and they sit in two classes.**

**Class 1, per-formula instantiation at the STAGE.** `sl` and `sc`. Each says
that `Lset lam` believes something about its own levels. **Neither mentions the
hull. Neither mentions the collapse.** That is the change this task made: before
it, the same debt sat at the collapse image, where the hull and the collapse were
both in the statement.

**Class 2, the ambient read-off.** `amb`. Section 3.

**And `s₁`, which I do not count as a wall.** Section 2.5 prices its missing
half at 2 lines written and 4 to 8 lines inferred.

**The next probe, with its abort criterion fixed in advance (D-1, C-34).**

> **The obligation**: state `Lset-only` at a GENERIC transitive carrier rather
> than at `𝒮ʟ`. Take the smallest step: restate `ApproxAt-value` and
> `approx-val` (`src/L/Hierarchy.lagda.md`) with the carrier a module parameter,
> and report the in-fence line count for that ONE lemma pair.
>
> - **GO** if the pair restates with the carrier abstract and no new hypothesis
>   beyond transitivity. Then the read-off stack is carrier-generic and
>   `AmbientRead` is a port, not a chapter.
> - **NO-GO** if either lemma needs `isL` in an essential position, for example
>   through `PowOK` (`src/L/Coding/Sequence.lagda.md:124-125`) or through
>   `hasReplacementL`. Then the ambient read-off needs the definable-powerset
>   operation proved absolute, and that IS a chapter.

**P-l binds on that probe by construction, and I say so: the class-carrier
instance is NOT a price for the ambient instance.**

## 8. TWO PROCESS FACTS THE ORCHESTRATOR ASKED FOR

### 8.1 The bar changed under me, and it cost nothing

**The correction arrived before I wrote a line of Agda.** No decision of mine
turned on the tightened figure. **I judge nothing against 0.009143 at 1.00x**,
and section 4 reports the seconds and the lines as measured, with no ratio
verdict.

### 8.2 A sibling held the import path red, and I worked around it

**MEASURED**: at 08:35 the first probe run failed inside
`src/L/Condensation.lagda.md:5832`, an `UnequalTerms` error in a sibling's
in-progress edit. `git status` showed `src/L/Condensation.lagda.md` and the three
`*Agree` masters modified, with mtime 08:34.

**I did not touch any of them.** I built probe A without the import path, and
named every delivered object as a hypothesis with its `file:line`. **At 08:47 the
sibling was green again**, and probe B wired the site for real in 146 s of cold
rebuild.

**The lesson, offered and not assumed.** A brief that forbids touching a file
should say whether the agent may WAIT for it. **I chose to build around it and
re-enter later, and that cost one restructure and about 15 minutes.** A brief
line saying "the sibling's file may be red; build generic first" would have cost
nothing.

## 9. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-160/lj-1.160-report.md`, READ WHOLE.** TOOK the lead
  (`:11-31`), the three open rows (`:266-279`), the two routes side by side
  (`:224-244`), the mechanism (`:246-262`), the next-probe obligation
  (`:293-306`), and the DD4 section (`:377-425`). **Its section 3.3 table is the
  spine of this report: two of its three rows are now discharged.**
- **`agents/tasks/LJ-1-160/ProbeLJ1160A.agda`, READ WHOLE.** TOOK the `Reroute`
  telescope (`:63-80`), `levelIn` (`:83-88`) and `cover` (`:91-100`). **Probe A
  section 1 is that derivation, restated at one parameter-free formula so the
  same statement reads at three carriers.**
- **`agents/tasks/LJ-1-151/lj-1.151-report.md`**: read `:11-19` and `:61-70`.
  TOOK the separability finding. **It held: `HasLevels` and `Covered` landed
  without `CrossOut`.**
- `agents/tasks/LJ-1-163/lj-1.163-report.md`: taken through the brief's summary.
  **Its lesson drove section 1, and search S4 found the answer in the file I
  thought I knew.**
- **`agents/tasks/archive/LJ-1-51/lj-1.51-report.md`**, read `:135-153`. TOOK the
  wall term and the unbuilt elementarity instance (`:141-143`). **Section 2.6
  measures that instance built.**
- **`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`**, read
  `:780-880`. **TOOK the class-carrier mirror `σL` with `levelΠ₁L` and
  `level-transfer-down` by `π₁-down` (`:846-880`).** **This is the archive's
  answer to the same question, and it is why section 3.3 asks whether the
  ambient reading comes back down.** The archive could come down because its
  story was Δ₀ at `L`; **the current route's environment members are at the
  collapse image, and their constructibility is exactly what is missing.**
  **SHAPE TAKEN, CLAIM REFUSED**, as `[LJ-1.160]` section 0.4 requires.
- `archive/dev/`: **NOT read.** The `D` series is superseded and no archived
  ruling bears on this task.
- **`src/L/BoundedSubset.lagda.md`**, read `:1-460`, `:660-1035`, `:1355-1626`.
  **TOOK `LevelHood` (`:74-146`), `IsoInv` (`:152-318`), `CollapseIso`
  (`:321-350`), `DownReflect` (`:356-451`), `HullElemDown.WithCode.elem`
  (`:681-765`), `isOrdAt` and `Amb` (`:795-821`), `erase-Δ₀` (`:825`),
  `LevelHood0` (`:840-859`), `HullStage.Condense` (`:903-1034`), the site
  telescope (`:1385-1394`), `HEDC` (`:1544`), `Co` (`:1554-1622`).** **NOT
  edited.**
- **`src/L/Hull.lagda.md`**, read `:148-250` and `:313-360`. TOOK `AtStage`,
  `AtM.Elementary` (`:174-176`), `TV-thm` (`:306-307`) and `Hull` (`:313-355`).
- **`src/L/Hierarchy.lagda.md`**, read `:1-90`, `:320-350`, `:640-660`. **TOOK
  `Lset-only` (`:334-335`) and `Lset-defines` (`:646-648`), and the module header
  (`:73`, `:78-79`) that fixes them at the class carrier. This is the wall's
  evidence.**
- **`src/L/Coding/Sequence.lagda.md`**, read `:41-175` and `:281-355`. TOOK
  `StepAt` (`:110`), `PowOK` (`:124-125`), `RecShape` and `LsetGraphAt`
  (`:281-352`), and the header (`:59-62`).
- **`src/L/Condensation.lagda.md`**, read `:80-120`, `:240-300`, `:405-445`,
  `:2230-2500`, `:6960-7060`. TOOK `Σ₁-cert` (`:269-270`), `CertTransfer`
  (`:409-411`), **`ride-only` and `ride-defines` (`:415-428`)**, `SatGraphB`
  (`:2230`), `GraphB` (`:2483-2494`), `DefBodyB` (`:2497`). **NOT edited.**
- **`src/V/Collapse.lagda.md`**, read `:1-120`. TOOK `isTrans` (`:25-26`), `πX`
  (`:75`), `πX-member` (`:78`), `πX-intro` (`:86`), `πX-trans` (`:89`).
- **`src/FOL/Absoluteness.lagda.md`**, read `:40-200`. **TOOK `Single`'s two
  semantics (`:66-71`), `abs₀` (`:122`), `σ₁-up` (`:182-184`) and `π₁-down`
  (`:186-188`).**
- `src/FOL/Manipulation/Relabelling.lagda.md`, read `:49-190` and `:209`. TOOK
  `mapFo`, `mapFo-comp` (`:87-89`), `embed` (`:117-118`), `⊨-map` (`:154-155`),
  `embed-⊨` (`:184-186`), `mapΔ₀` (`:209`).
- `src/FOL/Manipulation/Renaming.lagda.md`, read `:41-150`. TOOK `liftρ`
  (`:50-52`), `renameFo` (`:58`), `Agrees` (`:101-102`), `agrees∷` (`:116-118`),
  **`⊨-rename` (`:127-129`)**.
- **`dev/LESSONS.md`**: C-12, C-22, C-36, C-38, C-40, C-42, D-1, D-10, I-5, P-h,
  P-k, P-l, P-m, P-n, R-35, R-38, R-40 loaded through
  `scripts/rules.py --for build` and `--for probe`.
- `dev/PLAN.md`: DD8, DD23, DD24, DD27 through the brief.

## 10. LITERATURE USED (DD18)

**`dev/literature/devlin-II5.md`, read `:88-120`, `:236-262`, `:368-396`.**

**The brief's question, answered directly.**

> **Say how Devlin gets the condensation transfer, and whether he needs the
> commuting equation at all.**

**Devlin gets it by (a), and (a) is an AMBIENT statement.** `:93-96` quotes the
lemma: `∀v∀γ [v = L_γ ↔ ∃z Φ(z, v, γ)]` with `Φ` a Σ₀ formula. **The universe
that quantifier ranges over is the real one, not `L`.**

**The chain at `:102-106` spends it exactly once, at the collapsed `M`:**
"1.9.15 converts M's satisfaction of the Σ₀ matrix into ambient Φ; (a) turns Φ
into `v = L_γ`".

**He does NOT need the commuting equation. MEASURED, by reading `:100-112`
whole.** No step of the chain moves a level construction across the collapse.
**This confirms `[LJ-1.160]` from the literature side, and it is why the build in
this task never writes `π (Lset m')`.**

**And it names what our tree lacks.** Devlin's (b) at `:95-96` is the LOCALIZED
form, `v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ`. **Our `Lset-only` is (b) at the class
carrier. Our chain needs (a).**

`:243-256` re-confirms the strength: "a Δ₀ witness for the satisfaction leaves is
NOT what Devlin's argument needs. Level-hood is used at Σ₁ strength". **So `s₁`
is the right certificate and section 2.5's two lines are the right cure.**

`:374-382` is the per-step DD4 table. **TOOK row C1 (level-hood formula,
PER-TOWER), row C3 (Σ₀ absoluteness at transitive carriers, EITHER TOWER) and
row C4 (transfer, EITHER TOWER).** **Section 5.2 stands on C3 and C4.**

`dev/literature/devlin-errata.md`: **NOT read.** `[LJ-1.136]` measured that the
errata touch no part of II.5.

`dev/literature/j-hierarchy.md`: **NOT read.** No J-tower content entered this
task; the build is generic in the formula, so the J tower's own level-hood
formula plugs in without reading its digest.

`_build/literature/dev2.txt`: **NOT opened.** Every citation runs through the
digest.

## 11. THE RULES, ANSWERED

- **C-36.** Section 0.5 writes the term I could not write, and section 3 places
  it. **I do not claim no supply exists.**
- **C-38 as extended.** Sections 0.4 and 2.4. **`HasLevels` and `Covered` are
  DISCHARGED, because two delivered objects SUPPLY them.** `CrossOut` is
  RESTATED, not discharged, and I say so.
- **C-42.** Section 3 measures ONE site: the ambient read-off for THIS formula.
  **I did not sweep the tree for other statements with the same carrier-fixed
  shape, and section 7's next probe is that sweep's first step.**
- **P-k.** `levelIn` and `cover` are stated where their consumers use them: at
  the verbatim types of `src/L/BoundedSubset.lagda.md:917-919`, checked by probe
  B against `BA.Co`.
- **P-l.** Sections 3.5 and 7. **I give the ambient read-off no figure anchored
  on the class-carrier instance.**
- **P-h.** The definability walk stays module-parameterized: `φ₀` is a module
  parameter of `Crossing`, `Site` and `AtSite`, and no body names a concrete
  formula.
- **P-m, P-n.** Section 7 classes the two stage facts as instantiation content
  and does NOT price them.
- **C-39.** Section 8.2.
- **C-40.** Section 3.5.
- **C-12.** One agda process, `-M8g`, cap never raised. Load beside every figure.
- **C-22.** This file existed as a skeleton before the first probe ran.
- **D-1.** Both probes are in `agents/tasks/LJ-1-178/`, both ran while the task
  was live, both are tracked. The abort criterion was the brief's, fixed in
  advance.
- **D-10.** The recorded residue was `levelIn` and `cover`. I priced their truth
  before their proof: both are Devlin's content, and both are true.
- **D-26.** Section 5.2 uses the digest's per-step carrier column.
- **D-29, D-30.** Section 0.4 reports the reduction and does not bank it as a
  saving. Probe B prices what the CONSUMER needs.
- **DD8.** One best-effort figure per term, each with its basis. Section 2.5.
  **Section 3.5 refuses a figure and says why.**
- **DD23.** No mathematical prose was written. Both probes carry comments only.
- **DD24.** Section 4 reports the seconds and the lines, and judges nothing.
- **DD4.** Section 5.

## 12. PROHIBITIONS, ANSWERED

**No master edited.** `src/Everything.lagda.md` not opened.
`src/L/Condensation.lagda.md`, the three `*Agree` masters and
`src/L/Choice/Name.lagda.md` were READ ONLY, never written. No commit, no push,
no `git checkout`, `stash`, `reset` or `clean`. No `make check`.

**My only files are** `agents/tasks/LJ-1-178/lj-1.178-report.md`,
`agents/tasks/LJ-1-178/ProbeLJ1178A.agda` and
`agents/tasks/LJ-1-178/ProbeLJ1178B.agda`. **Both probes are tracked, they sit
beside the report, and they are never deleted.**
