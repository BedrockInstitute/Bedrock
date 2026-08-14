# LJ-1.209 report: price the seal `[LJ-1.204]` named

**STATUS: COMPLETE.** I edited no master. I committed nothing and pushed
nothing. I ran no `make check`. Every probe lives under
`agents/tasks/LJ-1-209/`, tracked, never deleted.

**Head: the in-harness Opus 5, selected by the clock**
(`scripts/dispatch_policy.py`, `VERSION_IN_FORCE = 'auto'`, Beijing time inside
the 14:00 to 18:00 peak window). **The in-harness path passes through no tool,
so C-12's slot accounting cannot see me. I held ONE Agda process at all times,
at `GHCRTS="-A64m -I0 -M8g"`, and I never raised the cap.** No heap
exhaustion. **The longest single invocation was 142.94 s**, far inside the 30
minute wall.

**MACHINE STATE.** A sibling held the other Agda slot for the whole session:
`LJ-1.198`, `agents/tasks/LJ-1-198/ProbeLJ1198C.agda` then a successor, at
about 100 percent of one core. **Load averages are recorded beside every run in
the tables below and in each `runs/*.txt` header.** Load moved between 3.46 and
26.04 during the session, and section 3.1 says what that did.

## 0. LEAD

**THE SEAL DOES NOT REACH. MEASURED.**

**AND THE TERM MOVES: the numeral property's CONTENT costs nothing at all.
MEASURED.** `[LJ-1.204]`'s 8.4 s is not the numeral property. No restatement of
that property, sealed or open, can reach it.

### 0.1 `Deserialization` before and after the seal

One paired within-series run, the two arms alternating, three kept runs each,
one discarded warm-up. Raw files in `agents/tasks/LJ-1-209/runs/`.

| arm | run 1 | run 2 | run 3 | mean | own spread |
|---|---:|---:|---:|---:|---:|
| **before** the seal (`ProbePlain`) | 10,020 | 9,774 | 9,289 | **9,694 ms** | 7.5 percent |
| **after** the seal (`ProbeSeal`) | 9,782 | 9,401 | 9,650 | **9,611 ms** | 4.0 percent |

**The seal buys 83 ms, 0.86 percent. It is NOT outside the within-series
spread.** The unsealed arm's own spread is 731 ms, 7.5 percent, so the effect
is nine times smaller than the noise around it. `scripts/check-ratio.py:72-76`
fixes the within-series band at 0.5 to 4.0 percent on a QUIET machine; today's
machine was not quiet, and gave 7.5 percent.

**And the sign flips.** In the last pair the sealed arm reads HIGHER: 9,289
unsealed against 9,650 sealed. **An effect with no consistent sign across three
pairs is not an effect.**

**The scale settles it without statistics.** The term to buy is about 8,200 ms
(section 3.4). **The seal buys 83 ms of it, one percent.**

### 0.2 The `unfolding` cost is ZERO, and that is the refutation

**`agents/tasks/LJ-1-209/ProbeSeal.agda` typechecks at exit 0 with NO
`unfolding` line anywhere.** The seal needed no proof-site work at all.

**That is not good news for the cure. It is the reason the cure fails.** In
this whole wing the numeral property is ONLY EVER A HYPOTHESIS: nothing builds
it and nothing eliminates it. **So the elaborator never unfolded it, and
`opaque` removes a capability that was never used.** Section 2 gives the
evidence.

### 0.3 The classification the brief asks for

**`[LJ-1.204]`'s mechanism was INFERRED. This report is the measurement, and it
REFUTES it.** The report itself marks the attribution INFERRED at its own
`agents/tasks/LJ-1-204/LJ-1.204-report.md:80` and `:89`, and it was right to.

## 1. THE COUNT OF `arNum` SITES, made by me

**The brief and `[LJ-1.204]:119-121` say「a handful」. It is 63 written type
occurrences.**

**THE SEARCH, and its filter, stated so the negative can be checked (rule 1).**
I swept by SHAPE, not by one spelling, and in three widening passes:

1. `grep -rn "Σ\[ n ∈ ℕ \]" src/` gives 78 hits.
2. `grep -rn "Σ\[ *[a-zA-Z] *∈ *ℕ *\]" src/` widens the binder letter and the
   spacing: 133 hits, and no new hit of the property.
3. `grep -rn "≡ # n\b" src/` gives 79 hits. Subtracting my 63 leaves 14, and I
   read all 14: they are numeral adequacy and injectivity lemmas
   (`src/V/Model.lagda.md:189`, `src/V/Coding.lagda.md:106,114`,
   `src/L/Axioms/Numerals.lagda.md:179`), an unrelated numeral property in
   `src/L/Ordinal/SquareLaw.lagda.md:539,543,671,858`, and UNTRUNCATED `fst d ≡
   # n` hypotheses in `src/L/Coding/Shape.lagda.md:422,434,467`,
   `src/L/Coding/Key.lagda.md:276,411` and
   `src/L/Coding/EnvSet.lagda.md:316`. **None is an `arNum` site.**

**No filter removed a candidate file. The sweep is over all of `src/`.**

### 1.1 The property has TWO spellings

| spelling | occurrences |
|---|---:|
| `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` | 57 |
| `∥ Σ[ n ∈ ℕ ] (fst N ≡ # n) ∥₁` | 6 |
| **total** | **63** |

### 1.2 Per file

| file | occurrences |
|---|---:|
| `src/L/Condensation.lagda.md` | 46 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 7 |
| `src/L/Condensation/UpperAgree.lagda.md` | 5 |
| `src/L/Condensation/LowerAgree.lagda.md` | 5 |

### 1.3 By family, because two dispatch stages put them there

| family | occurrences | where |
|---|---:|---|
| `codesK` / `codesK-un` / `compK` / `unCompK` | **42** | 36 in `Condensation`, 6 in the three `*Agree` records |
| `envK` / `envK-mem` / `envK-neg` / `envK-imp` | **21** | 10 in `Condensation`, 11 in the three `*Agree` records |

### 1.4 The name against the type

**The literal name `arNum` appears 20 times**, all in
`src/L/Condensation.lagda.md`, at `:2803`, `:3506`, `:3714`, `:3718`, `:3800`,
`:3805`, `:3919`, `:3924`, `:4094`, `:4099`, `:4466`, `:4470`, `:5082`,
`:5087`, `:5206`, `:5211`, `:5308`, `:5314`, `:5404`, `:5408`.

**The name is 20; the TYPE is 63.** `[LJ-1.204]`'s「about 420 ms per field」
divides 8.4 s by「a handful」. **Against 63 the rate is 133 ms, against 20 it is
420 ms. Neither rate means anything, because section 3.3 measures that the
field's content costs nothing.**

### 1.5 Against `[LJ-1.173]`

**The brief's premise is SOUND and I name its row (rule 5):**
`agents/tasks/LJ-1-173/lj-1.173-report.md:1784-1790` gives 6 record field
declarations, 29 telescope entries by SHAPE, 6 projection sites and 11
destructuring sites.

**That table is stage TWO only, the `codesK` sweep.** It gives 6 + 29 = 35 type
sites against my 42 in that family. **INFERRED, and I did not verify it:** the
gap is the `fst N` spelling and the local type ascriptions, which a
`codesK`-name sweep does not reach. **Stage THREE added the 21-site `envK`
family separately and the report does not count it in one table.**

**The commit that placed the field is `c8a628b`**,
「[LJ-1.173] All 21 false fields are cured」, whose body states the same 29
telescope entries. **The report file and the commit are the same task under
two stages.**

## 2. THE `unfolding` COST: ZERO, and why

**MEASURED: exit 0, no `unfolding` line.** The evidence for the reason:

- All 63 type occurrences sit in a module telescope, a record field, or a local
  type ascription of a hypothesis's own result. The ascription shape is at
  `src/L/Condensation.lagda.md:6289-6292`.
- All 20 uses of the name are a destructured `let` binding or a direct argument
  pass. The pair at `src/L/Condensation.lagda.md:3714` and `:3718` is the
  shape: bind `arNum` out of `codesK`, hand the same token to `envK`.
- **No `PT.rec` and no `PT.map` touches it.** The `PT.rec` elimination
  `[LJ-1.173]` first priced at `agents/tasks/LJ-1-173/lj-1.173-report.md:1288`
  was withdrawn; commit `c8a628b`'s body records the withdrawal.

**The proof is the compile itself. If ANY site looked inside the property,
Agda would have refused `ProbeSeal.agda`.** It did not.

### 2.1 The seal was REAL, and I certified it

**A green compile alone does not prove the seal bit. It is equally consistent
with `opaque` not sealing at all within one module.** So I built the control.

**`agents/tasks/LJ-1-209/ProbeOpaqueReal.agda`**, five seconds, both halves
run:

| half | result |
|---|---|
| `unfolded→open`, inside `opaque unfolding isNum` | **GREEN, exit 0** |
| `sealed→open`, the same coercion outside the `unfolding` | **REFUSED:** `isNum n !=< n ≡ n` `[UnequalTerms]` at `:31.19-20` |

**MEASURED: `opaque` does seal against LATER CODE IN ITS OWN MODULE.** So
`ProbeSeal`'s `isNumeral` was genuinely opaque, and it still moved nothing. The
file is left in its green state with the red half commented out and the
refusal recorded here.

### 2.2 The forward cost, for the record

The truncation elimination lands once, in the eventual supplier of `codesK`,
which is not written. Commit `c8a628b`'s body states that design:
「The elimination moves into the eventual supplier, where it happens once
instead of eleven times」. **So the future `unfolding` price is ONE block, not
63.**

## 3. THE MEASUREMENT, in full

### 3.1 The instrument

`--profile=internal`, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process of mine at a
time. **A probe under `agents/tasks/` has no interface in the tree, so every
run is cold by construction**; `agents/tasks/LJ-1-209/run_one.sh` deletes the
probe's own `.agdai` first to keep that true after run one.

**Design: WITHIN-SERIES PAIRED, per `[LJ-1.201]` section 2.2.** The between-series
band that `check-ratio.py` carries is a ONE-MODULE figure of plus or minus 12.8
percent, by that file's own words at `:72-76`, and it cannot resolve a 3 s
effect. `[LJ-1.185]` applied that band to an aggregate and wrongly concluded no
cure was measurable.

### 3.2 SERIES 1, the seal

| run | arm | `Deserialization` self | cumulative | total | wall | load before | exit |
|---|---|---:|---:|---:|---:|---|---:|
| validate (**discarded warm-up**) | seal | 9,797 | 10,351 | 134,511 | 135.47 | 6.44 / 5.21 / 4.93 | 0 |
| p1 | plain | 10,020 | 10,575 | 140,959 | 142.94 | 5.16 / 5.05 / 4.90 | 0 |
| s1 | seal | 9,782 | 10,352 | 136,750 | 137.78 | **26.04** / 18.02 / 10.42 | 0 |
| p2 | plain | 9,774 | 10,335 | 137,246 | 138.29 | 6.96 / 13.28 / 9.62 | 0 |
| s2 | seal | 9,401 | 9,973 | 132,921 | 133.84 | 5.11 / 10.23 / 8.94 | 0 |
| p3 | plain | 9,289 | 9,827 | 131,837 | 132.74 | 4.38 / 8.20 / 8.32 | 0 |
| s3 | seal | 9,650 | 10,186 | 131,505 | 132.42 | 4.52 / 6.77 / 7.71 | 0 |

**The load spike is real and I report it rather than hide it.** A sibling
started an Agda run inside my p1 window and the one-minute average reached
26.04. The series then decays back to 4.4 to 6.5. **That decay is why the plain
arm reads 10,020, then 9,774, then 9,289: it is the machine, not the code.**

**ONE DESIGN FLAW, stated plainly.** Series 1 ran plain-then-seal in every
pair, so the decay always favoured the seal. **Series 2 reverses the order for
exactly that reason, and its result is the same.**

### 3.3 SERIES 2, THE DISCRIMINATOR, and it moves the term

**The seal answers「does opacity stop the pull?」. The sharper question is:
does the 8.4 s follow the numeral CONTENT, or the extra telescope COMPONENT,
whatever that component holds?**

`agents/tasks/LJ-1-209/ProbeTrivial.agda` answers it. **It keeps all 46
components in `Condensation` exactly where they are and empties the content:**

```agda
isNumeral : V ℓ → Type (ℓ-suc ℓ)
isNumeral x = x ≡ x
```

**No ℕ, no `#`, no Σ, no truncation. Same level, same component count.** It is
not mathematics; it isolates one term. The new arm goes FIRST in every pair.

| run | arm | `Deserialization` self | cumulative | total | wall | exit |
|---|---|---:|---:|---:|---:|---:|
| t1 | trivial | 9,812 | 10,383 | 140,003 | 141.48 | 0 |
| q1 | plain | 9,488 | 10,040 | 135,454 | 136.40 | 0 |
| t2 | trivial | 9,498 | 10,034 | 134,194 | 135.07 | 0 |
| q2 | plain | 9,645 | 10,194 | 135,823 | 136.76 | 0 |
| t3 | trivial | 9,035 | 9,579 | 129,874 | 130.76 | 0 |
| q3 | plain | 9,069 | 9,595 | 126,948 | 127.79 | 0 |

| arm | mean `Deserialization` self |
|---|---:|
| trivial (`x ≡ x`) | **9,448 ms** |
| plain (the real numeral property) | **9,401 ms** |

**MEASURED: the numeral CONTENT costs 47 ms, and the sign is the wrong way
round.** Deleting ℕ, `#`, the Σ and the truncation makes the check 0.5 percent
SLOWER. **That is zero.**

### 3.4 THE LADDER, all four rungs in ONE DAY

I re-ran `[LJ-1.204]`'s own bottom rung today, unchanged, to put every rung in
one machine state. **P-l says a measured cure does not transfer by analogy, so
RE-MEASURE it at its own site: that applies to a cross-day baseline too.**

| rung | probe | `Deserialization` self | what it is |
|---|---|---:|---|
| 1 | `agents/tasks/LJ-1-204/ProbeMinusArNum.agda` | **1,165 ms** | commit `c8a628b` reverted |
| 2 | `ProbeTrivial` | 9,448 ms | component present, content emptied |
| 3 | `ProbePlain` | 9,401 ms | today's master |
| 4 | `ProbeSeal` | 9,611 ms | content sealed `opaque` |

Rung 1 read 1,238 ms on `[LJ-1.204]`'s day
(`agents/tasks/LJ-1-204/LJ-1.204-report.md:58`) and **1,165 ms today**, load
3.46 before and 5.00 after, exit 0, wall 124.57 s. **The term reproduces:
9,401 minus 1,165 is 8,236 ms.**

**Rungs 2, 3 and 4 sit within 2 percent of each other, and rung 1 is eight
times below all three.** **So the 8.2 s is carried by commit `c8a628b`, and it
is carried by neither the numeral property's content nor its transparency.**

### 3.5 The verdict against the abort criterion (D-1, fixed before the run)

| criterion | verdict |
|---|---|
| **CURED** | **NO.** 83 ms of an 8,236 ms term, inside a 731 ms noise band, sign flipping |
| **THE SEAL DOES NOT REACH** | **YES. This is the answer.** Sections 3.2 and 3.3 hold the profile |
| **IT REACHES AND COSTS MORE THAN IT SAVES** | Not applicable. It reaches nothing and it costs nothing to write |
| **A WALL** | **NO.** Longest single invocation 142.94 s. No heap exhaustion. Cap never raised |

## 4. THE FOUR MASTERS

**I edited no master. MEASURED:** `git status --porcelain
src/L/Condensation.lagda.md src/L/Condensation/` prints nothing, so all four
are byte-identical to HEAD.

**The brief makes the four-master exit code a condition of the CURED branch
only, and the branch is not CURED, so there is nothing to land and nothing to
re-check.** I did not spend four cold runs proving that untouched files still
typecheck.

**What the runs DO certify:** `ProbePlain`, `ProbeSeal` and `ProbeTrivial` each
carry the whole `agda` content of `src/L/Condensation.lagda.md`, differing only
in the module name and the property's spelling. **All 13 runs of them exit 0**,
and the 14th run file is `[LJ-1.204]`'s bottom rung, also exit 0.

## 5. THE WING AGGREGATE

**NOT RE-MEASURED, and I state why rather than spend the hour.** The aggregate
answers「what did the cure buy?」. **The cure bought 83 ms inside a 731 ms
band.** A twelve-master `check-ratio.py` pass costs minutes per module and
carries a 12.8 percent between-series band, which is more than an order of
magnitude wider than the effect. **It could not resolve this cure, and
`[LJ-1.185]` is the standing example of that exact error**, which
`[LJ-1.201]` section 2.2 overturned.

**The standing figures, from the only admissible source**
(`.venv/bin/python scripts/ledger.py --brief`): **29,777 lines over 88 masters,
measured from HEAD.** DD24's cold AC-only baseline is **133.19 s**
(`dev/ledger.toml:341`). **DD5's seconds benchmark DOES NOT EXIST**, by that
same line, so no wing aggregate binds anything today.

**On the bar (DD24 unchanged, owner 2026-08-14):** the brief prices the wing's
gap at 56 to 67 s and calls 8.4 s a seventh of it. **That seventh is not
available through this cure.** Intermediate debt is allowed, so nothing is
overdue; the term simply stays open.

## 6. DD4

**Maximize the code the two proofs share, and write it generic. One rule, two
ends, no metric and no checker.**

**`isNumeral` is a property of `V ℓ` and it mentions no tower.** I wrote it
that way in the probe:

```agda
opaque
  isNumeral : V ℓ → Type (ℓ-suc ℓ)
  isNumeral x = ∥ Σ[ n ∈ ℕ ] (x ≡ # n) ∥₁
```

`#_` comes from Cubical's `InfinitySet` on `V`
(`src/L/Condensation.lagda.md:66`), and `V ℓ : Type (ℓ-suc ℓ)`
(`src/V/Hierarchy.lagda.md:78-85`). **So the definition sits BELOW both towers.
The J-tower re-instantiation figure is ZERO extra lines**, because the
definition never names `L`, `Lset`, `isL` or `𝒮ʟ`. Compare `[LJ-1.184]`, where
six extra lines bought the second tower for a 167-line module.

**But DD4 does not save this cure. Three shared lines that buy 83 ms are three
lines that buy 83 ms.** A shared line is still a line.

### 6.1 A free DD4 finding, and I did not price it

**The property already exists in the tree TWICE, in TWO ORIENTATIONS, and
neither is shared with the wing:**

- `src/L/StageCardinal.lagda.md:422`: `ω-mem→numeral : (δ : S) → ⟨ δ ∈ˢ ω ⟩ → ∥
  Σ[ n ∈ ℕ ] (# n ≡ δ) ∥₁`, with `isPropNumeralWit` at `:425` and
  `numeral-wit` at `:429`.
- `src/L/Ordinal/SquareLaw.lagda.md:539`: the same lemma name, the OPPOSITE
  orientation `β ≡ # n`, which is the wing's orientation.

**So a shared `isNumeral` has a natural home and two existing consumers, and
the tree currently pays a `sym` at whichever orientation it does not pick. I
did NOT measure what that `sym` costs, and I do not claim it is worth anything.**

## 7. WHAT I DID NOT SETTLE, and the probe that would

### 7.1 The named next gate

**OPEN: is the 8.2 s the extra telescope COMPONENT, or another part of commit
`c8a628b`?** Rung 1 reverts the WHOLE commit, which was 77 lines net and also
restructured the `envK` family. **My probes cannot separate those two.
INFERRED, not measured.**

**The decisive probe, priced.** Build a fourth arm from `ProbeTrivial` that
DELETES the component instead of emptying it. Its edits are bounded and I
counted them:

| edit class | sites | shape |
|---|---:|---|
| type sites, drop the conjunct and move a closing paren up | 46 | `× isNumeral (fst ar))` and 5 variants |
| destructuring sites | 11 | `(arK , (aK , arNum))` becomes `(arK , aK)` |
| argument sites | 9 | `envK ... arNum hE` becomes `envK ... hE` |
| projection sites | 5 lines in 4 regions | `ks .snd .snd .fst` becomes `ks .snd .snd` |

**71 edits, one generator, one validation run and three paired runs: about 12
minutes of Agda.** The five projection lines are
`ProbeTrivial.agda:5809`, `:5810`, `:5885`, `:6277` and `:6322`.
**The trap is the OTHER projections:
`ProbeTrivial.agda:6920-6921` and `:7019-7021` bind a DIFFERENT `ks`, from
`graphWitK`, which has no numeral component and must not be touched.** A blind
rewrite breaks them.

**I did not build it, because my brief's abort criterion names「THE SEAL DOES
NOT REACH」a complete answer, and because a half-built arm is worse than a
named one.**

### 7.2 What I did not observe

**I did not identify WHICH imported definitions are pulled.** Agda offers no
per-import deserialization account, and `[LJ-1.204]` established the same at
its `:105-109`. I did not re-test that.

## 8. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| the `opaque` seal cures the term | **REFUTED. MEASURED.** 83 ms of 8,236 ms, inside a 731 ms band, sign flipping |
| the seal costs `unfolding` at the proof sites | **REFUTED. MEASURED.** Zero `unfolding` lines, exit 0 |
| `opaque` seals against later code in its own module | **CONFIRMED. MEASURED.** `ProbeOpaqueReal`, `[UnequalTerms]` at `:31.19-20` |
| the conversion checker was unfolding the property | **REFUTED. MEASURED.** Nothing in the wing looks inside it, so nothing unfolded it |
| the 8.4 s is the numeral property's CONTENT | **REFUTED. MEASURED.** Emptying the content moves it 47 ms the WRONG way |
| the 8.2 s term is real and reproduces today | **CONFIRMED. MEASURED.** 9,401 against 1,165 in one day, one machine state |
| the 8.2 s is the extra telescope COMPONENT | **UNRESOLVED. INFERRED.** Rung 1 reverts a 77-line commit, not one component |
| 「a handful of small type fields」 | **REFUTED. MEASURED.** 63 type occurrences, 20 name uses |
| 「about 420 ms per field」 | **VOID. MEASURED.** The rate divides a term the field does not carry |
| the cure re-instantiates free for J | **TRUE but MOOT. INFERRED.** Zero extra lines, and it buys 83 ms |
| a single invocation passed 30 minutes | **MEASURED FALSE.** Longest 142.94 s |
| I ran more than one Agda process, or raised the cap | **MEASURED FALSE.** One at a time, `-A64m -I0 -M8g` throughout |
| I edited a master, committed, pushed, or ran `make check` | **MEASURED FALSE.** None of these. `git status` on the four masters is empty |
| I touched `src/Everything.lagda.md` or `src/L/Choice/Name.lagda.md` | **MEASURED FALSE.** Neither appears in `git status` |
| I deleted a line to improve a ratio (P-q) | **MEASURED FALSE.** No master changed |

## 9. PROBES

All under `agents/tasks/LJ-1-209/`, tracked, run while the task was open.

| file | question | verdict |
|---|---|---|
| `gen_probes.py` | build the three arms from the master's fences | generator |
| `ProbePlain.agda` | today's master, renamed | baseline, 3 kept runs plus 3 more |
| `ProbeSeal.agda` | does the `opaque` seal cure the term? | **NO: 9,611 against 9,694** |
| `ProbeTrivial.agda` | does the numeral CONTENT carry the term? | **NO: 9,448 against 9,401** |
| `ProbeOpaqueReal.agda` | does `opaque` seal within its own module? | **YES, and Agda's refusal is quoted** |
| `run_one.sh`, `run_series.sh`, `run_series2.sh` | the cold harness | instrument |
| `runs/` | 14 raw profiles, each with its load header | evidence |

**MEASURED: `.venv/bin/python scripts/check-probes.py` is CLEAN**, 1,969
tracked files, no probe outside `agents/tasks/` and no generated file.

**`lint-agda.py` and `lint-prose.py`: NOT RUN, and I say so rather than claim a
green I did not take.** No master edit landed, so neither had new master text
to check.

## 10. ARCHIVE USED (DD18)

- **`agents/tasks/LJ-1-204/LJ-1.204-report.md`, read WHOLE with its probes.**
  **TOOK:** the cause and the 9,911 ms figure at `:16-18`; the refuted
  interface-size hypothesis at `:20-24`; the cure hypothesis at `:130-138`; the
  1,238 ms bottom rung at `:58`; the INFERRED marking of the mechanism at
  `:80` and `:89`; the「no per-import account」finding at `:105-109`; and the
  probe design it named at `:148-151`, **which I ran and which returned NO**.
  I also read and re-ran its `ProbeMinusArNum.agda` unchanged, and read
  `gen_probes.py` and `runs/run_cold.sh` for the cold protocol.
- **`agents/tasks/LJ-1-145/lj-1.145-report.md`, read sections 0, 1, 4, 9.**
  **TOOK:** the seal that went 2,459 ms to below 1 ms at `:308-312`; the P-t
  licence sentence at `:295-297`; and the load-beside-every-figure table shape
  at `:22-30`. **TOOK AS SHAPE ONLY, never as a price (P-l).** Its seal cured a
  `Typing.CheckRHS` conversion; mine had to face a `Deserialization` term, and
  it did not.
- **`agents/tasks/LJ-1-201/LJ-1.201-report.md`, read sections 0, 1, 2.**
  **TOOK:** the within-series paired design and the reason the aggregate band
  is the wrong instrument, at `:25` and `:252-253`; and the 0.5-to-4.0 percent
  within-series band, which I quote against my own 7.5 percent.
- **`agents/tasks/LJ-1-173/lj-1.173-report.md`.** **TOOK:** the site table at
  `:1784-1790`; the withdrawn `PT.rec` price at `:1288`; the four-alias
  finding at `:1443-1448`. **NOTE for the record:** this file is the STAGE ONE
  gate report and returns NO-GO on a different question. **The `arNum` field
  was placed by commit `c8a628b`**, found with `git log -S`.
- **`scripts/check-ratio.py:65-85`**, read directly rather than through a
  report. **TOOK:** the constant's own words that 12.8 percent is a
  BETWEEN-SERIES one-module figure.
- **`dev/ledger.toml:341`** and `scripts/ledger.py --brief`. **TOOK:** the
  133.19 s DD24 baseline and the standing 29,777 lines.
- **`archive/dev/TASKS-archived.md`: SURVEYED, NOT USED.** The retired route
  predates the arNum field and holds no interface-deserialization account.
  **Taken as shape only:** nothing there bears.
- **`dev/LESSONS.md` at each entry named in the brief:** P-l (a measured cure
  does not transfer by analogy, so RE-MEASURE it at its own site: I re-measured
  rung 1 today for that reason), P-t (the seal licence, whose precondition
  「consumers do not look inside」 is met here and still did not pay), P-q (no
  line deletion to buy a ratio: no master changed), C-42 (the refutation names
  ONE site, so section 1 counts the shape before pricing anything), C-12 (one
  process, cap never raised), C-22 (this file existed before the first run),
  D-1 (abort criteria fixed in the brief before the first run), DD8 (one
  best-effort number with its basis, in section 7.1).

## 11. LITERATURE (DD18)

**Nothing in the literature governs elaboration cost.**
