# LJ-1.507 report: someEnv at the frame, and what arNumC can and cannot pay

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).
No commit, no push. I wrote only in `agents/tasks/LJ-1-507/`. Agda ran
under the caliber the program set on this pane, `GHCRTS="-A64m -I0 -M8g"`,
ONE Agda process at a time. I did not set `GHCRTS`. No heap event in any
run.

TARGET: one term `someEnv-at-frame` in
`agents/tasks/LJ-1-507/Probe507.agda`, by discharging `[LJ-1.504]`'s
`someEnvDef-gap` from the frame hypothesis `arNumC` and then applying
`gap-suffices`. Nothing lands in `src/`. I did not build a `TFacts`
value. I did not edit `someEnvDef` and I did not weaken it. I did not
use `[LJ-1.506]`'s equation and I did not name `AllCodes`. I did not
postulate `arNumC`.

The standing direction (`dev/pod/direction.md:37`) says one SRC
collection after LJ-1, not after `[LJ-2.5]`. This task is LJ-1 work. It
does not start that collection and it does not start phase 3. No
Boundary clause is in conflict.

## VERDICT

**NO-GO, STATED. THE GAP IS NOT UNPAID. IT IS FALSE.**

The brief's route asked `arNumC` to discharge `someEnvDef-gap`. It
cannot, and the reason is stronger than a weak hypothesis:
`someEnvDef-gap` has **no** inhabitant at `[LJ-1.504]`'s own frame. The
refutation is machine-checked under `--safe`,
`agents/tasks/LJ-1-507/Probe507.agda:257-268`, exit 0, `runs/final.out`.
So `gap-suffices` (`agents/tasks/LJ-1-504/Probe504.agda:133-138`) is a
true implication out of an empty antecedent and it inhabits nothing.

The probe is GREEN and the obligation name `someEnv-at-frame` is
DELIBERATELY ABSENT from it. The witness meter agrees and reads the
intended state:
`/opt/homebrew/bin/python3.11 scripts/pod/witness.py --code LJ-1-507
--brief agents/tasks/LJ-1-507/LJ-1.507.md`, exit 1, 3.06 s,
**1 UNRESOLVED of 1, `probe_red=False`** (`runs/witness-1.out`).
`.venv/bin/python` is absent in this worktree, as `[LJ-1.499]` and
`[LJ-1.504]` also found; I added no dependency.

The stop is written at
`agents/tasks/LJ-1-507/review-of-someEnv-at-frame.md`.

**THE MATHEMATICIAN'S RULING ON `arNumC` IS NOT OVERTURNED. IT IS
VINDICATED AND RELOCATED.** `arNumC` is sufficient for the numeral the
supplier needs, measured at `Probe507.agda:213-224`. What the refutation
moves is WHERE the hypothesis has to sit: not in a gap between the record
and its supplier, but inside `someEnvDef`'s own type.

## D-10, BEFORE ANY AGDA

The brief asked, at `file:line`, whether `[LJ-1.500]`'s frame and
`[LJ-1.504]`'s frame agree slot for slot, and said a difference is a
STOP.

**THEY AGREE, AT ALL TWENTY SLOTS, AND THE AGREEMENT IS DEFINITIONAL.**

| | `[LJ-1.500]` | `[LJ-1.504]` |
|---|---|---|
| the vector | `c6 ∷ c5 ∷ c4 ∷ c3 ∷ c2 ∷ c1 ∷ Kenv` (`agents/tasks/LJ-1-500/Probe500.agda:357`) | `SE.B₀ ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ KV.Kenv` (`agents/tasks/LJ-1-504/Probe504.agda:60`) |
| its type | `S ^ 20` (`Probe500.agda:356`) | `Vec S 20` (`Probe504.agda:59`) |
| `Kenv` | `KValue`'s own, 14 slots (`src/L/Condensation.lagda.md:7389-7393`) | the same |
| the code slot | `suc (suc zero)` (`Probe500.agda:359`, `:350`) | `suc (suc zero)`, which `someEnvDef`'s consumer reads at `src/L/Condensation/LowerAgree.lagda.md:116` |
| the K slot | `suc⁶ iK` (`Probe500.agda:360`) | `suc⁶ KV.iK` (`Probe504.agda:92`) |

**BUT D-10 IS NOT A SLOT COUNT, AND THAT IS WHY THE TASK STOPPED
ANYWAY.** D-10 says to price the TRUTH of a recorded residue before
pricing its proof. `someEnvDef-gap` is that residue
(`Probe504.agda:120-126`), and `[LJ-1.504]`'s own review already read it
back in plain words: **"at `KValue`'s bound, a member of `K` is a
numeral"** (`agents/tasks/LJ-1-504/review-of-someEnv-reaches.md:31-32`).
Stated that way it is visibly a claim about EVERY member of `Lset lam`,
and `KValue` itself puts non-numerals there. The five minutes D-10 asks
for is what turned this task from a build into a refutation.

**PREDICTION, MADE BEFORE THE AGDA: the frames agree and the gap is
false.** Both held.

## W3, MEASURED FIRST AND ALONE

**GO, ON THE FIRST TYPECHECK.** `runs/w3-0.out` and `runs/w3-1.out`,
exit 0.

The brief's W3 was a TYPE, `arNumC-at-504-frame`. A type that merely
FORMS proves nothing, so the term measured is one step stronger:
`frames-agree` (`Probe507.agda:177-184`) states `arNumC` at
`[LJ-1.504]`'s vector and FEEDS it into `[LJ-1.500]`'s rebuilt `Num`
(`Probe507.agda:75-88`, `[LJ-1.500]`'s `Probe500.agda:225-239`), then
returns `[LJ-1.500]`'s delivered conclusion. If the two frames disagreed
at any of the twenty slots, that application would not elaborate.

**NEGATIVE CONTROL, BECAUSE AN ACCEPTED APPLICATION PROVES NOTHING ON
ITS OWN.** I moved the `Num` instantiation from the code slot `iC` to
the K slot `K6` and reran. Exit **42**, `error: [UnequalTerms]`,
`fst g2 != L.Constructible.Lset lam of type V ℓ`
(`runs/w3-control.out:3`). The conversion checker does resolve the
twenty slots and does compare the values, so the green run is a real
measurement and not a vacuity. **It also delivers a fact the report
needs below: `lookup iC (gam' …)` is the FREE variable `g2`, and
`lookup K6 (gam' …)` is `Lset lam`.**

The brief estimated about 15 lines and under 30 seconds for W3.
Measured: the W3 stage is **144 lines** in the file of which 66 are
non-blank and non-comment, and **3.25 s**. The stage is bigger than the
estimate because W3 could not be stated without rebuilding both frames
first, which the brief itself priced separately at about 160 of its 200
lines. I did not fund it against `[LJ-1.500]`'s 3.16 s.

The W3-only file is kept at
`agents/tasks/LJ-1-507/runs/Probe507.w3-only.agda.txt`. It is the file
the `w3-*` runs measured, saved with a `.txt` tail so it is not a second
module in the include path.

## THE JOIN

Three findings, in the order they were measured.

### 1. `arNumC` does not reach the gap, and Agda names the missing input

`runs/attempt-0.out`, exit 42. The attempt is

```agda
gap-from-arNumC arNumC g1 g2 g3 g4 g5 ya yc b a ar c yaK ycK arK =
  frames-agree g1 g2 g3 g4 g5 (arNumC g1 g2 g3 g4 g5) 0 c ar a b arK refl
```

and Agda's answer is

```
(fst ar) != (fst c) of type (V ℓ)
when checking that the expression arK has type
⟨ fst c ∈ fst (lookup iC (gam' g1 g2 g3 g4 g5)) ⟩
```

The gap hands a member of **K** where `arNumC`'s only consumer wants a
member of the **CODE SET**. Those are different slots: `iC` is `g2`, a
free variable, and `K6` is `Lset lam` (`runs/w3-control.out:3`).

### 2. What `arNumC` is missing is exactly three arguments

`gap-with-code` (`Probe507.agda:213-224`) is GREEN. It is the gap's
telescope plus a tag `k`, the code membership at `iC`, and the shape
equation `fst c ≡ pr (fst ar) (pr (# k) (pr (fst a') (fst b')))`. With
those three, `arNumC` pays in one line. **Those three are precisely what
`TFacts.codesK` carries (`src/L/Condensation/TwelveAgree.lagda.md
:162-167`) and precisely what `someEnvDef` omits
(`src/L/Condensation/LowerAgree.lagda.md:52-58`).**

### 3. The gap is FALSE

`gap-is-false : someEnvDef-gap → Empty.⊥` (`Probe507.agda:257-268`),
exit 0, `runs/final.out`, under `--safe`, with no postulate and no
hypothesis beyond `[LJ-1.504]`'s own frame telescope.

`KValue` DELIVERS a `KFacts` VALUE at this frame
(`src/L/Condensation.lagda.md:7411-7425`), and two of its fields are the
whole refutation: `numK0` puts `numeralL 0` in K (`:7416`) and `pairK`
closes K under the L-pair (`:7423`). So
`prʟ (numeralL 0) (numeralL 0)` is a member of K
(`Probe507.agda:251-255`) and the gap would call it a numeral.

It is not one. `pr a a` is `⁅ ⁅ a ⁆s , ⁅ a , a ⁆ ⁆`
(`src/V/Coding.lagda.md:175-176`), whose two members each hold `a`; an
ordinal is transitive (`src/L/Constructible.lagda.md:141-142`), so `a`
would belong to `pr a a` and hence to itself, which `∈-irrefl` forbids
(`src/V/Hierarchy.lagda.md:155`); and every numeral IS an ordinal
(`src/L/Ordinal.lagda.md:244`). That is `pr-self-not-numeral`
(`Probe507.agda:124-126`), and it needs no excluded middle: `lem` is a
module parameter and this term does not use it.

**NEGATIVE CONTROL.** With a genuine numeral at the `ar` slot instead of
the pair, the same term is exit 42 (`runs/refute-control.out:3-9`). The
refutation depends on its witness and is not a type error in disguise.

**`runs/refute-0.out` IS A CODER'S SLIP AND NOT A FINDING**, kept because
the runs are kept. I passed the same variable at all eleven telescope
positions, so `badAr` never reached the `ar` slot. Its error text is
therefore identical to the negative control's, and neither is evidence
about the gap. `runs/refute-1.out` is the first green run of the
refutation.

**WHAT I DO NOT CLAIM.** I do **NOT** claim `someEnvDef {9} KV.iK
(gam' …)` is false. I refuted ONE route to it, the route this brief
named. `[LJ-1.172]`'s refutation of the unrestricted `envSetK` still
sits one step away and I did not measure whether it reaches `someEnvDef`
(`AGENTS.md:45`).

## THE SWEEP (C-42)

C-42 says a refutation measures the site it names and never how far the
shape extends, so the count comes before any price.

**THE REFUTED SHAPE IS: an obligation that CONCLUDES the numeral
truncation while its telescope carries only K-memberships of the
subject, with no code membership and no decomposition equation.**

The numeral truncation `∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁` across `src/`,
counted at the cited files:

| file | as a CONCLUSION | as a HYPOTHESIS |
|---|---|---|
| `src/L/Condensation.lagda.md` | 30 | 20 |
| `src/L/Condensation/TwelveAgree.lagda.md` | 2 | 9 |
| `src/L/Condensation/LowerAgree.lagda.md` | 2 | 6 |
| `src/L/Condensation/UpperAgree.lagda.md` | 2 | 6 |
| `src/L/Coding/EnvSupply.lagda.md` | 0 | 10 |
| **total** | **36** | **51** |

**OF THE 36 CONCLUSION SITES, 34 CARRY THE CODE MEMBERSHIP AND THE SHAPE
EQUATION IN THEIR OWN TELESCOPE.** The two that do not are local type
annotations, `ks` at `src/L/Condensation.lagda.md:6435-6437` and `:6482
-6483`, and both sit inside a `go` whose telescope does carry `c∈` and
`shapeM` (`:6424-6425` and `:6471-6472`) and both are filled by
`codesK`/`unCodesK` applied to them. So neither is an independent
obligation.

**THE COUNT IS ONE, AND IT IS `someEnvDef`.** To be exact:
`someEnvDef` does not conclude the truncation, it never mentions it. It
is the one field type in `src/` whose SUPPLIER demands the truncation
(`src/L/Coding/EnvSupply.lagda.md:418`) while the field's own telescope
carries nothing about `ar` but a K-membership
(`src/L/Condensation/LowerAgree.lagda.md:52-58`). **Any bridge between
the two is therefore forced into exactly the shape refuted above**, and
that is what `[LJ-1.504]` found and what this task refuted.
`someEnvDef` is declared once
(`src/L/Condensation/LowerAgree.lagda.md:52`) and consumed by two record
fields, `LFacts.someEnv` (`:218`) and `TFacts.someEnv`
(`src/L/Condensation/TwelveAgree.lagda.md:289`). `UpperAgree` has no
`someEnv` field: `grep -c someEnv src/L/Condensation/UpperAgree.lagda.md`
returns **0**.

**SO THE CURE DOES NOT SPREAD.** The 51 hypothesis sites already ASK for
the truncation and prove nothing, and the 34 sound conclusion sites
already have what they need. **The thread `[LJ-1.504]` named is still the
whole fix, and this sweep says no second site was hiding behind it.**

**I DO NOT PRICE THE THREAD.** `[LJ-1.504]` counted 12 sites of type
change (`agents/tasks/LJ-1-504/lj-1.504-report.md:164-165`) and I have
measured none of them.

## THE PRICE

Three forced rechecks each, one Agda process, wide caliber, same pane.
The interface `_build/2.8.0/agda/agents/tasks/LJ-1-507/Probe507.agdai`
was deleted before every run.

W3 alone (`runs/w3-1.time`, `w3-2.time`, `w3-3.time`):

| run | wall s | peak RSS bytes |
|---|---|---|
| `w3-1` | 3.29 | 592723968 |
| `w3-2` | 3.25 | 592740352 |
| `w3-3` | 3.25 | 592740352 |

Median wall **3.25 s**, median peak RSS **592,740,352 B**.

Full file (`runs/full-1.time`, `full-2.time`, `full-3.time`), measured on
the file as delivered:

| run | wall s | peak RSS bytes |
|---|---|---|
| `full-1` | 3.42 | 732430336 |
| `full-2` | 3.44 | 732413952 |
| `full-3` | 3.42 | 732430336 |

Median wall **3.42 s**, median peak RSS **732,430,336 B**. No heap event
in any run.

**THE JOIN AND THE REFUTATION COST 0.17 s AND 140 MB OVER W3 ALONE.**
The two batches ran minutes apart on the same pane, not interleaved.
0.17 s is outside the spread of either batch (0.04 s and 0.02 s), so I
report it; 140 MB is the elaboration of the pairing lemmas and the
`KValue` record projection.

The brief estimated about 200 lines in the probe, of which the obligation
is about 40. Measured: the file is **279 lines**, **144** of them
non-blank and non-comment. The obligation is not there at all, and what
took its place is 12 lines of refutation
(`Probe507.agda:257-268`). **The estimate is not funded against and
nothing here was sized by it.**

The ratio bar does not fire: the write scope carries no ` ```agda `
fence, so the divisor is 0 in-fence lines and the bar binds nothing on
this task.

## WHAT someEnv COST IN THE END

Every predecessor whose DELIVERED term this task used, at `file:line`:

| predecessor | term used | where |
|---|---|---|
| `[LJ-1.499]` | the frame telescope and `gam'` | via `[LJ-1.504]`'s copy, `agents/tasks/LJ-1-504/Probe504.agda:47-60` |
| `[LJ-1.500]` | `ar-is-numeral`, rebuilt | `agents/tasks/LJ-1-500/Probe500.agda:78-84` |
| `[LJ-1.500]` | `module Num` and the type of `arNumC`, rebuilt | `agents/tasks/LJ-1-500/Probe500.agda:225-239` |
| `[LJ-1.503]` | the gate `ω∈σ`, taken from the frame and never reopened | `agents/tasks/LJ-1-504/Probe504.agda:52` |
| `[LJ-1.504]` | `K6`, `someEnvDef-gap` and `gap-suffices`, rebuilt | `agents/tasks/LJ-1-504/Probe504.agda:91-92`, `:120-126`, `:133-138` |
| `[LJ-1.506]` | its FINDING only, that the truncation needs a hypothesis about the code set | `agents/tasks/LJ-1-506/Probe506.agda:143-150` |
| the tree | `KValue.facts`, `numK0`, `pairK` | `src/L/Condensation.lagda.md:7411`, `:7416`, `:7423` |
| the tree | `arityNumAtL`, `arityNumAtL-out` | `src/L/Coding/CodeSet.lagda.md:185`, `:189` |

I imported no probe. `[LJ-1.506]`'s equation is not used and `AllCodes`
is not named anywhere in `Probe507.agda`.

**WHAT REMAINS BETWEEN THIS AND A `TFacts` VALUE, IN ONE SENTENCE.**
`someEnvDef` has to carry the numeral truncation in its own type before
`someEnv` can be filled at all, and only then do the remaining twenty of
the fifty-nine positions become an arithmetic question rather than a
mathematical one.

I did not build that value. Fifty-nine positions are out of scope and
AD12 gives this brief one obligation.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`: READ AND USED.**
  `archive/dev/LJ-dispatch-index.md:249` reads
  `| LJ-1.173 | Restrict envSetK to a numeral arity | ALL 21 CURED, 77 LINES | My ruling's scope was one record; its sweep measured three. Patch by SHAPE, not name: one field has four aliases |`.
  **This is the archive's own price for the same SHAPE of change the
  thread now needs**, and it is the reason my sweep counted by shape
  rather than by name. It is an OLD price at an OLD tree and I do not
  carry it as this task's number. `:248` reads
  `| LJ-1.172 | BUILD the supply | 1 TO 5 BUILT; 6 REFUTED AT THE JOIN. DD25 review [LJ-1.180] UPHELD | envSetK asks a level to hold a function space. Six names, one fact, no supplier |`,
  which pins the neighbouring refutation this report names but does not
  transfer.
- **`archive/dev/JOURNAL-archived.md`: DECLINED.** `grep -c someEnv`
  returns **0** and `grep -c envSetK` returns **0**. Its subject is the
  retired route (`:1` reads `# Archived journal: the retired route`).
  Nothing in it bears on this field.
- **`archive/dev/JOURNAL.md`: DECLINED.** `grep -c someEnv` returns
  **0**. `:1` reads `# ARCHIVED 2026-08-20`. Same reason.
- **`archive/dev/DECISIONS-archived.md`: DECLINED.** `grep -c someEnv`
  returns **0** and `grep -c numeral` returns **0**. `:1` reads
  `# Archived decisions: the D series`; the `D<n>` series resolves
  against it and this task cites no `D<n>` code.
- **`dev/ARCHIVE.md`: DECLINED.** `grep -c someEnv` returns **0**. `:1`
  reads `# ARCHIVE.md: the archive registry`. This task retires no
  module, so it writes no row there. W4 is answered below.

## LITERATURE USED

- **`dev/literature/truncation-and-selection.md`: READ, AND IT SENT ME TO
  THE RIGHT QUESTION.** `dev/literature/truncation-and-selection.md:195`
  reads

  > principle. **It is a `2-Constant` proof.** Discharge it or refute it before

  The rule it states is that a stalled truncation obligation is usually
  not a new principle, and that the two live options are to discharge it
  or to REFUTE it. Reading that is what made me price the gap's truth
  before its proof rather than hunting for a selection principle.
  `[LJ-1.504]` read the same file and reported that no selection
  principle supplies the statement
  (`agents/tasks/LJ-1-504/lj-1.504-report.md:272-280`); this task
  measured why, and the reason is that the statement is false.
- **`dev/literature/devlin-II5.md`: DECLINED.** `:1` reads
  `# Devlin II.5: the Condensation Lemma and the GCH in L`. This task
  compares two Agda frames and refutes one type; it reaches no
  mathematical content Devlin covers.
- **`dev/literature/digest.md`: DECLINED.** `:1` reads
  `# Digest: the orthodox form of the rud route, pinned from the collected literature`.
  This task touches no tower choice.
- **`dev/literature/geology.md`: DECLINED.** `:1` reads
  `# Geology dossier: set-theoretic geology sources and the five questions`.
  No bearing on a record field type.
- **`dev/literature/terms-2026-08.md`: DECLINED.** `:1` reads
  `# The terminology dossier: fourteen renderings for the owner's ruling`.
  This task names no new term and adds no `dev/glossary.toml` entry.

## W2 AND W4, ANSWERED

**W2 (DD4).** The mathematics is written once at a generic carrier and
instantiated. `ar-is-numeral` (`Probe507.agda:61-67`) and `module Num`
(`:75-88`) are generic in `m`, `C` and `γ`, exactly as `[LJ-1.500]`
delivered them, and the frame instantiates them at `m = 20`. The
refutation's four pairing lemmas (`:97-112`) are generic in `V ℓ` and
know nothing about this frame. No fixed form was written and there is no
conflict to report.

**W4 (DD13).** This task retires no module and deletes nothing, so
`dev/ARCHIVE.md` takes no row. Priced against the ideal form written
fresh today: the ideal `Probe507.agda` would still rebuild both frames,
because a probe may not import a probe, so the 144 non-blank
non-comment lines are close to irreducible. The one thing an ideal form
would drop is `gap-with-code`, which exists only to make the second
finding constructive rather than an error message.

## WHAT I DID NOT DO

- I did not build a term named `someEnv-at-frame`, so the obligation
  reads UNRESOLVED by design.
- I did not edit or weaken `someEnvDef`.
- I did not use `[LJ-1.506]`'s equation and I did not name `AllCodes`.
- I did not postulate `arNumC`.
- I did not import a probe. Both predecessors' terms are rebuilt.
- I did not build a `TFacts` value and I did not price the remaining
  twenty fields.
- I did not price the 12-site thread.
- I did not measure whether `[LJ-1.172]`'s refutation reaches
  `someEnvDef`, and I do not claim it does.
- I did not set `GHCRTS` and I ran one Agda process at a time.
- Nothing landed in `src/`. No commit. No push.
