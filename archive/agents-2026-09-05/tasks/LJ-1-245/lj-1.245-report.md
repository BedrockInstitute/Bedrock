# LJ-1.245 report: C-45 applied to the whole record

tier: pi (deepseek-subagent-mode), model `deepseek-v4-pro`. No Agda ran. No
master, brief or report was edited. No commit, no push. Written incrementally
(C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. LEAD

**Two numbers: 7 undischarged sites, 0 `dev/PLAN.md` rows now rest on one.**

The count is 7, but the set the record names is wrong. `[LJ-1.243]` counted
seven sites and named one of them `ProbeT193.agda:63,94,97`. It treated that
file as one site and counted `ProbeLJ1120A.agda:189` as undischarged. Both
moves are wrong. My own boundary test finds **8** equation-parameter sites of
the hypothesis form, across 7 probe modules. **7 of the 8 are undischarged.
The 8th is discharged by `refl` and `[LJ-1.243]` missed the call site.**

**The one row C-45 cost is `[LJ-1.184]`, and it is already corrected**
(`dev/PLAN.md:731`, and `dev/PLAN.md:47`). No other row, live or archived,
records a result that rests on an undischarged parameter without saying so.
The record is otherwise clean.

## 1. THE COUNT, AND MY OWN BOUNDARY TEST

`[LJ-1.243]` section 6.1 listed seven recurrence rows. I re-derived each with
the boundary the brief fixed: an idiom has one independent side and `refl`
closes it at the call site. A hypothesis has independent terms on BOTH sides,
so `refl` is impossible. I read every parameter and searched the whole tree
for every application of every module.

| # | site | parameter | module | discharge |
|---|---|---|---|---|
| 1 | `agents/tasks/LJ-1-184/ProbeLJ1184B.agda:112` | `q : Graph {2} zero (suc zero) ≡ embed φ₀` | `AmbientStep` | none; relayed at `ProbeLJ1184C.agda:83` |
| 2 | `agents/tasks/LJ-1-184/ProbeLJ1184C.agda:80` | `q : AG {2} zero (suc zero) ≡ embed φ₀` | `Step184` | none; applied nowhere |
| 3 | `agents/tasks/archive/L3-32-T193/ProbeT193.agda:63` | `carve : DefOf.defSet (Lset γ) ψ ≡ Sset γ` | `CarveLanding` | none; fed at `:97` |
| 4 | `agents/tasks/archive/L3-32-T193/ProbeT193.agda:94` | `carve₀ : DefOf.defSet (Lset a₀) ψ₀ ≡ Sset a₀` | `FirstLimit` | none; applied nowhere |
| 5 | `agents/tasks/archive/Unpaired/ProbeW3Seq.agda:347` | `x≡ : x ≡ Fof i a b` | `OpDecode` | none; applied nowhere |
| 6 | `agents/tasks/LJ-1-151/ProbeLJ1151A.agda:100` | `Kis : lookup K γ' ≡ levelK α o` | `Slots` | none; applied nowhere |
| 7 | `agents/tasks/archive/L3-32-T194/ProbeT194.agda:73` | `F≡ : F ≡ DefOf.defSet (Sset (U l)) σ` | `GeneralQlim` | none; applied nowhere |
| 8 | `agents/tasks/LJ-1-120/ProbeLJ1120A.agda:189` | `qE : fst (lookup Ei γ) ≡ fst envSetGen` | `Holds` | **DISCHARGED** by `refl` at `ProbeLJ1120B.agda:61` |

**The boundary test result.** Sites 1 to 7 are hypotheses. Each has
independent terms on both sides. Site 8 is the idiom. MEASURED, section 2.

**The count error, stated.** `[LJ-1.243]` said "seven sub-shape B sites" and
its section 6.1 table listed seven recurrences. Two of its moves are false:

1. It counted `ProbeT193.agda:63` and `:94` as separate rows but called the
   file one site in the brief's reading. The file holds TWO parameters. So the
   brief's "one of them: `ProbeT193.agda:63,94,97`" under-counts the file by
   one. MEASURED, by reading the file.
2. It recorded `ProbeLJ1120A.agda:189` (`Holds`) as "applied nowhere". The
   module is applied once, at `ProbeLJ1120B.agda:61`, with `refl` for `qE`.
   So the site is DISCHARGED, not undischarged. MEASURED, section 2.

The two errors cancel. The true count of undischarged sites is 7. But the
membership differs: `ProbeLJ1120A.agda:189` leaves the list, and
`ProbeT193.agda:63` and `:94` are two sites, not one. The brief's "find the
other six" therefore names the wrong set.

## 2. ONE SECTION PER SITE

### 2.1 `ProbeLJ1184B.agda:112`, `q`

**Shape:** hypothesis. `Graph` is a parameter at `:104`, `φ₀` at `:111`. Both
sides are applications. `refl` cannot close it. MEASURED.

**Discharged?** No. `AmbientStep` is applied once, at
`ProbeLJ1184C.agda:83`, and the `q` argument there is the caller's own
parameter. It relays; it discharges nothing. MEASURED.

**Row:** `LJ-1.184`. It is corrected at `dev/PLAN.md:731` to "SUPPLIED UNDER
AN ASSUMED q. See LJ-1.243". `dev/PLAN.md:47` (`[LJ-1.7]`) is corrected too.
Both rows say so. This is the one row C-45 cost, already paid.

### 2.2 `ProbeLJ1184C.agda:80`, `q`

**Shape:** hypothesis. Same form as 2.1, at the relay site. MEASURED.

**Discharged?** No. `Step184` is applied nowhere. MEASURED, by search.

**Row:** `LJ-1.184`, the same row, already corrected. No separate row exists
for `[LJ-1.184]` probe C.

### 2.3 `ProbeT193.agda:63`, `carve`

**Shape:** hypothesis. `DefOf.defSet (Lset γ) ψ` depends on `γ` and `ψ`. `Sset γ`
depends on `γ`. Neither side is a fresh slot, and `DefOf.defSet` does not
reduce to `Sset`. `refl` cannot close it. MEASURED.

**Discharged?** No. `CarveLanding` is applied once, at `ProbeT193.agda:97`,
from `FirstLimit`'s own `carve₀`. It relays. MEASURED.

**Row:** the task is `L3-32-T193`, a retired-route gate. Its rows live in
`archive/dev/`, not in `dev/PLAN.md` section 11. MEASURED, by search of the
live index. The archived row records the landing as GREEN and names the carve
clause as a parameter. It does not claim the carve is discharged. Section 5.

### 2.4 `ProbeT193.agda:94`, `carve₀`

**Shape:** hypothesis. Same form as 2.3, at the first limit. MEASURED.

**Discharged?** No. `FirstLimit` is applied nowhere. MEASURED, by search.

**Row:** same as 2.3. Archived, and the record names the carve as a
parameter. Section 5.

### 2.5 `ProbeW3Seq.agda:347`, `x≡`

**Shape:** hypothesis. `x`, `i`, `a` and `b` are all parameters. The body
spends `x≡` through `sym` at `:362` (`repVal`). It is a real premise, not a
refl-closable pin. MEASURED.

**Discharged?** No. `OpDecode` is applied nowhere. MEASURED, by search.

**Row:** the task is `L3-32-T50`, a retired-route gate. Archived. The archived
record says `OpDecode.keyImg` is GREEN "now checked", and it names the
hypotheses in the claim itself ("x = Fof i a b and no smaller op"). It does
not claim `x≡` is discharged. Section 5.

### 2.6 `ProbeLJ1151A.agda:100`, `Kis`

**Shape:** hypothesis. `lookup K γ'` depends on `K` and `γ'`. `levelK α o`
depends on `α` and `o`. All four are parameters. `refl` cannot close it.
MEASURED.

**Discharged?** No. `Slots` is applied nowhere. MEASURED, by search.

**Row:** `LJ-1.151` lives in `dev/PLAN.md:701` and reads "GO AT 21 LINES, AND
valK IS FALSE". The GO is the `Fact` module, which has no equation parameter
and is not `Slots`. The report's own section 1.3 puts `Slots` "outside the
21". So the row does not rest on `Kis`. INFERRED, from reading the row against
the report.

**One note the orchestrator should see.** The REPORT
`agents/tasks/LJ-1-151/lj-1.151-report.md` section 1.3 records "the match is
machine-checked, not read". That claim rests on `frame-valK`, which rests on
`Kis`. So the report carries a C-45-shaped claim: a green fact that rests on
an undischarged parameter. It is a report, never rewritten, and it is not the
PLAN row. I name it and leave it. The delivered fact (`valK`, 21 lines) is not
conditional on `Kis`.

### 2.7 `ProbeT194.agda:73`, `F≡`

**Shape:** hypothesis. `F` and `σ` are parameters, and `DefOf.defSet` does not
reduce. The probe's own comment names `F`, `σ`, `carve-⊆`, `carve-⊇` as "the
content the transfer would have to build, stated here as module parameters".
MEASURED.

**Discharged?** No. `GeneralQlim` is applied nowhere. MEASURED, by search.

**Row:** the task is `L3-32-T194`, a retired-route gate. Archived. Its outcome
is RED, not a delivered result, and it states the family equality as a
parameter. It does not claim `F≡` is discharged. Section 5.

### 2.8 `ProbeLJ1120A.agda:189`, `qE` (the misclassified site)

**Shape:** idiom, and DISCHARGED. MEASURED, by reading the call site.

`Holds` is applied at `ProbeLJ1120B.agda:61`:

```agda
let module H = G.Holds
      (E ∷ ya ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ)
      zero (suc (suc (suc (suc (suc zero)))))
      (suc (suc (suc (suc (suc (suc (suc zero)))))))
      refl refl refl
```

The three `refl` close `qE`, `qd` and `qb`. For `qE`, the slot `Ei` is `zero`,
the environment is `(E ∷ ...)`, so `lookup zero (E ∷ ...)` is `E`. And
`ProbeLJ1120B.agda:58-59` defines `E = G.envSetGen`. So both sides of `qE`
are `fst G.envSetGen`, and `refl` closes it. MEASURED.

`[LJ-1.243]` said `Holds` is "applied nowhere". That is MEASURED FALSE.

**Row:** `LJ-1.120` lives at `dev/PLAN.md:670` and reads "BUILDS, someEnv
CLOSES". The result does rest on `Holds.holds` (which the report cites at
`ProbeLJ1120A.agda:207`). But `qE` is discharged by `refl`, so nothing rests
on an UNDISCHARGED parameter here. No defect.

## 3. IS `src/` REALLY CLEAN

**Yes, of the hypothesis form. MEASURED, by reading the three named sites and
spot-checking the rest.**

`[LJ-1.243]` named three `src/` modules that carry an undischarged bare
equation only because no consumer exists. I read all three.

| site | parameter | form |
|---|---|---|
| `src/L/Coding/KeyRead.lagda.md:130` | `q : fst (lookup A γ) ≡ ∅` | idiom: one side is the constant `∅` |
| `src/L/Choice/Adequate.lagda.md:802` | `qR qP qB qC q₀`, all `lookup _ ≡ _` pins to constants `Rs Ps Aʟ AllCodes` | idiom: one side is determined |
| `src/L/Condensation.lagda.md:1806` | `p : countFo φ ≡ 0` | idiom: one side is the constant `0` |

Each has one determined side. Each would close by `refl` if a consumer
existed. None is the hypothesis form. MEASURED, by reading each.

I also spot-checked `src/L/Choice/Order.lagda.md:298-304`, whose `Slots`
module carries `qtw : fst tw ≡ Lset δ` and three more slot pins. Its body
spends them through `refl` and `Σ≡Prop` at `:316-317`. That is the slot-match
idiom, and its prose names the pins as such. Not the hypothesis form.

**No delivered master carries the hypothesis form.** I did not re-run the full
4,165-telescope sweep. The named sites are idiom, and the spot-check found no
counter-example. INFERRED for the parts I did not read; MEASURED for the
named sites.

## 4. THE ARCHIVE'S INSTANCES

**The archive carries ONE instance, the crossing, and it is a function
hypothesis, not a bare equation. MEASURED.**

`archive/src/2026-08-09-rud-route/L/Condensation.lagda.md:168-170` defines
`CrossOut φ = (v b : Sᴹ) → IsOrd (fst b) → Believes φ v b → fst v ≡ Lset (fst b)`.
`:208` reads `module Assembly (φ : Formula Sᴹ 2) (co : CrossOut φ) where`.
Nothing in the archive instantiates `Assembly`. MEASURED, by search.

`:806-809` names the owed equivalence in prose: "the agreement itself is the
class-carrier equivalence ... left standing with the ambient obligations". So
the retired route recorded the crossing as OWED, not built. MEASURED, by
reading the block.

**Does it carry more?** No. A search for bare equation parameters in the
archive's module telescopes found none beyond the crossing. The crossing is
one instance, and it is a function hypothesis, not the three-token
`_≡_` parameter shape. MEASURED, by search.

**Do the archived rows claim on it?** No row records `CrossOut σᴹ` or `co` as
supplied. The prose records it as standing with the ambient obligations.
MEASURED, by search of `archive/dev/`.

**Do the archived rows claim on the probe sites (T193, T194, T50)?** Each
names its equation as a parameter or a premise, never as a discharged fact.

- `L3-32-T50` (`archive/dev/TASKS-archived.md:85`): the JOURNAL entry records
  `OpDecode.keyImg` as GREEN "now checked" and names the premises in the
  claim. Not an unconditional claim. MEASURED.
- `L3-32-T193` (`archive/dev/JOURNAL-archived.md:3187`): "the landing is 4
  code lines ... GREEN ... the carve clause is a delivered parameter". It
  names the carve as a parameter. MEASURED.
- `L3-32-T194` (`archive/dev/JOURNAL-archived.md:3202`): outcome RED, and it
  states the family equality as a parameter to build. MEASURED.

## 5. DD4

**One of the seven sits in shared machinery, and its shared half is a shape.**

`ProbeLJ1151A.agda:100` (`Kis`) sits in the `Slots` block. The report's
section 6 classes that block "SHARED. Slot bookkeeping names no tower". But
`Kis` is undischarged and `Slots` is applied nowhere. So the shared content is
a shape waiting for a proof, not a delivered shared result. Any DD4 figure
that counts the slot bookkeeping as shared reads one site too high. INFERRED,
from the report's classification plus the undischarged parameter.

The other six sit in single-tower machinery:

- Sites 1 and 2 (`q`) are the Def-tower crossing. Per-tower, not shared.
  MEASURED, from `[LJ-1.242]` section 5.
- Sites 3, 4, 5 and 7 (`carve`, `carve₀`, `x≡`, `F≡`) are retired Sset-rud
  machinery. That is one tower's content, archived. Not shared. MEASURED, by
  the files' imports.

Site 8 (`qE`) is tower-free coding machinery, but it is discharged, so it
carries no DD4 defect.

## 6. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-243/lj-1.243-report.md`, read WHOLE. **Line read:** `:496`,
  the table row for `ProbeT193.agda:94`. TOOK the seven-site claim and its
  boundary test.
- `agents/tasks/LJ-1-242/lj-1.242-report.md`, read WHOLE. **Line read:** `:11`,
  "is not six readings. It is six readings PLUS one equation".
- `agents/tasks/LJ-1-184/ProbeLJ1184B.agda`, read `:101-118`. **Line read:**
  `:112`, `q : Graph {2} zero (suc zero) ≡ embed φ₀`.
- `agents/tasks/LJ-1-184/ProbeLJ1184C.agda`, read WHOLE. **Line read:** `:80`,
  `q : AG {2} zero (suc zero) ≡ embed φ₀`.
- `agents/tasks/archive/L3-32-T193/ProbeT193.agda`, read WHOLE. **Line read:**
  `:97`, `open CarveLanding a₀ a₀-ord firstLimit seg∈L₀ ψ₀ carve₀ public`.
- `agents/tasks/archive/L3-32-T194/ProbeT194.agda`, read `:69-137`. **Line
  read:** `:73`, `F≡ : F ≡ DefOf.defSet (Sset (U l)) σ`.
- `agents/tasks/archive/Unpaired/ProbeW3Seq.agda`, read `:341-360`. **Line
  read:** `:347`, `x≡ : x ≡ Fof i a b`.
- `agents/tasks/LJ-1-151/ProbeLJ1151A.agda`, read WHOLE. **Line read:** `:100`,
  `Kis : lookup K γ' ≡ levelK α o`.
- `agents/tasks/LJ-1-151/lj-1.151-report.md`, read WHOLE. **Line read:** `:117`,
  "the slot match block, section 1.3 | 14". TOOK that the GO excludes `Slots`.
- `agents/tasks/LJ-1-120/ProbeLJ1120A.agda`, read `:1-100,188-207`. **Line
  read:** `:189`, `qE : fst (lookup Ei γ) ≡ fst envSetGen`.
- `agents/tasks/LJ-1-120/ProbeLJ1120B.agda`, read WHOLE. **Line read:** `:61`,
  `let module H = G.Holds ... refl refl refl`. TOOK the discharge of `qE`.
- `agents/tasks/LJ-1-120/lj-1.120-report.md`, read WHOLE. **Line read:** `:8`,
  "The generic environment-set builds."
- `archive/dev/TASKS-archived.md`, read `:85`. **Line read:** `:85`, the
  `L3-32-T50` row.
- `archive/dev/JOURNAL-archived.md`, read `:1815-1829,3187-3215`. **Line
  read:** `:1822`, "`Decode.OpDecode.keyImg` decodes x = Fof i a b".
- `archive/src/2026-08-09-rud-route/L/Condensation.lagda.md`, read
  `:166-170,206-210,806-809`. **Line read:** `:208`,
  `module Assembly (φ : Formula Sᴹ 2) (co : CrossOut φ) where`.
- `dev/PLAN.md`, read `:1-60,387-823`. **Line read:** `:731`, the corrected
  `LJ-1.184` row.
- `dev/LESSONS.md`, read C-45. **Line read:** `:3915`, the C-45 heading.
- `src/L/Coding/KeyRead.lagda.md`, read `:120-135`. **Line read:** `:130`.
- `src/L/Choice/Adequate.lagda.md`, read `:795-810`. **Line read:** `:802`.
- `src/L/Condensation.lagda.md`, read `:1798-1812`. **Line read:** `:1806`.
- `src/L/Choice/Order.lagda.md`, read `:285-320`. **Line read:** `:298`,
  `module Slots (tw pw rl cs ro c0 : S)`.

## 7. LITERATURE USED (DD18)

Nothing in the literature governs Agda telescopes.

**Separately:** one delivered row cited the literature to support a result
that rested on an undischarged parameter, and it is corrected. `LJ-1.184`'s
row recorded `amb` (Devlin's clause (a) at the ambient carrier) as SUPPLIED,
and `amb` rested on `q`. The row now reads "SUPPLIED UNDER AN ASSUMED q".
No archived or delivered row that is still live cites the literature to
support a result resting on an undischarged parameter. MEASURED, by search of
the rows.

## 8. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| the undischarged count is seven | **MEASURED TRUE**, but the membership is wrong, section 1 |
| `ProbeT193.agda` is one site | **MEASURED FALSE.** Two parameters, `:63` and `:94` |
| `Holds` is applied nowhere | **MEASURED FALSE.** Applied at `ProbeLJ1120B.agda:61` |
| `qE` is an undischarged hypothesis | **MEASURED FALSE.** Closed by `refl` |
| a PLAN row rests on `Kis` | **INFERRED FALSE.** The `LJ-1.151` row's GO is the `Fact` module |
| the `LJ-1.151` report's match claim is unconditional | **MEASURED FALSE.** It rests on `Kis`, section 2.6 |
| a live row rests on an undischarged parameter | **MEASURED FALSE.** Only `LJ-1.184`, already corrected |
| `src/` carries the hypothesis form | **MEASURED FALSE** at the named sites; INFERRED for the rest |
| the archive carries more than one instance | **MEASURED FALSE.** One crossing, no bare equation |
| the archive records the crossing as supplied | **MEASURED FALSE.** It records it as owed, `:806-809` |
| an archived row claims an unconditional result on an undischarged parameter | **MEASURED FALSE.** T50, T193, T194 each name the premise |
| a literature citation still supports an undischarged-parameter result | **MEASURED FALSE.** The one case is corrected |

## 9. PROHIBITIONS, ANSWERED

No Agda ran. No master, brief or report was edited. `src/Everything.lagda.md`
was not opened. No commit, no push, no `git checkout`, `stash`, `reset` or
`clean`. `make check` did not run. My file is
`agents/tasks/LJ-1-245/lj-1.245-report.md` and it is the only file I wrote.
