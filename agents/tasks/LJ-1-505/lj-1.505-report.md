# `[LJ-1.505]` report: the environment vector at `KValue`'s frame

slot: `coder`. Written early as a skeleton and filled as runs land (C-22).

## 1. THE VERDICT

**GO.** `agents/tasks/LJ-1-505/Probe505.agda` typechecks at exit 0, median
**3.08 s** and peak RSS **653,164,544** bytes over three forced rechecks of the
full file. The obligation
`agents/tasks/LJ-1-505/Probe505.agda::gammaPrime` is at `:113-114`.

**W3 IS GREEN AND THE ARITHMETIC HOLDS.** `11 + 9` and `6 + 14` agree
definitionally at this frame. `lengthCheck` (`:64-65`) is that check alone:
median **2.29 s**, peak RSS **611,041,280** bytes over three forced rechecks.
The brief estimated under 25 s; the measured cost is 2.29 s. Nothing landed in
`src/`. **No `TFacts` value was built.**

**THE FRAME DECISION IS NOT MADE HERE.** `[LJ-1.499]` handed the free slots to
the mathematician and this task supplies the evidence for that choice. Section 2
is that evidence. **Three of the twenty slots are UNCONSTRAINED and this report
does not fill them with a reason.**

## 2. THE TWENTY SLOTS

One row per slot: its index, its occupant in `gammaPrime`, and the `file:line`
of what requires that occupant, or the word UNCONSTRAINED.

`TA` abbreviates `src/L/Condensation/TwelveAgree.lagda.md` and `CO`
abbreviates `src/L/Condensation.lagda.md`.

| # | Occupant | Required by | Refs |
|---:|---|---|---:|
| 0 | `SE.B₀`, the carrier | **PINNED.** `witK`'s pin clause `CO:7010`; and the `B` slot of `TA:186`, `:192`, `:198`, `:204`, `:210`, `:216`, `:223`, `:230`, `:237` | 9 |
| 1 | `junk` | **ROLE ONLY.** The satisfaction graph `T`: `TA:173`, `:177` (lookups) and `TA:265`, `:271`, `:277`, `:283`, `:290`, `:311`, `:326` (`subVal*` arguments). **No named graph object exists in the tree.** | 9 |
| 2 | `junk` | **ROLE ONLY.** The code set `C`: `TA:162`, `:168`, `:173`, `:177`. **One named candidate exists and this task does not choose it**, see 2.3 | 4 |
| 3 | `junk` | **UNCONSTRAINED** | 0 |
| 4 | `junk` | **UNCONSTRAINED** | 0 |
| 5 | `junk` | **UNCONSTRAINED** | 0 |
| 6 | `LsetS gam ordγ` | `Kenv` slot `iA`, `CO:7390`; and the pin's right side, `CO:7010` | - |
| 7 | `LsetS lam ordλ` | `Kenv` slot `iK`, `CO:7390`; the `K` of every K-field, e.g. `TA:145-156` | - |
| 8 | `numeralL 0` | `Kenv`, `CO:7391`; `tagEq0` at `TA:133`; and `t0eq` at `TA:181` under `[LJ-1.502]` | - |
| 9 | `numeralL 1` | `Kenv`, `CO:7391`; `tagEq1` at `TA:134`; and `t1eq` at `TA:182` under `[LJ-1.502]` | - |
| 10 | `numeralL 2` | `Kenv`, `CO:7391`; `tagEq2` at `TA:135` | - |
| 11 | `numeralL 3` | `Kenv`, `CO:7391`; `tagEq3` at `TA:136` | - |
| 12 | `numeralL 4` | `Kenv`, `CO:7392`; `tagEq4` at `TA:137` | - |
| 13 | `numeralL 5` | `Kenv`, `CO:7392`; `tagEq5` at `TA:138` | - |
| 14 | `numeralL 6` | `Kenv`, `CO:7392`; `tagEq6` at `TA:139` | - |
| 15 | `numeralL 7` | `Kenv`, `CO:7392`; `tagEq7` at `TA:140` | - |
| 16 | `numeralL 8` | `Kenv`, `CO:7393`; `tagEq8` at `TA:141` | - |
| 17 | `numeralL 9` | `Kenv`, `CO:7393`; `tagEq9` at `TA:142` | - |
| 18 | `numeralL 10` | `Kenv`, `CO:7393`; `tagEq10` at `TA:143` | - |
| 19 | `numeralL 11` | `Kenv`, `CO:7393`; `tagEq11` at `TA:144` | - |

### 2.1 The census, and where it CORRECTS the brief

The brief measured slot 1 at **two** references and slots 0 and 2 at nine and
four. **Slot 1 carries NINE, not two.** The brief's regex found the two bare
`lookup (suc zero) γ'` occurrences and could not see the other seven, which
reach slot 1 as an ARGUMENT of a formula under a prefix: `subValAt` and
`subValSuccAt` take the graph slot first, and at a prefix of depth `d` that
argument is written `suc^(d+1) zero`. The seven are `TA:265`, `:271`, `:277`,
`:283`, `:290`, `:311`, `:326`.

The census is mechanical and it is a syntactic result, not a proof. It parses
all **59** fields of `record TFacts` (`TA:129-332`), reads every environment
prefix `(x ∷ ... ∷ γ')` in each field, and decodes every `suc^k zero` against
every prefix depth `d` that field uses, reporting `k - d` when it is not
negative. The script is `agents/tasks/LJ-1-505/runs/census.py` and its output
is `runs/census.out`; the second pass is `runs/census-slots345.py` and
`runs/census-slots345.out`. Both are tracked and both re-run in under a second
with no Agda. The counts they produced are the `Refs` column above, and each is
backed by the `file:line` list beside it, which can be checked by hand.

**SLOTS 3, 4 AND 5 CARRY ZERO REFERENCES UNDER ANY PREFIX DEPTH.** That is the
second pass of the census, run precisely because taking one depth per field
could hide a hit: a smaller depth gives a LARGER `k - d`, so a hit at 3, 4 or 5
could exist under a depth the first pass did not take. It does not. All three
counts are zero across all 59 fields and all depths.

### 2.2 What slots 3, 4 and 5 ARE, which is not the same as what constrains them

**UNCONSTRAINED does not mean unused, and the mathematician should not read it
that way.** `TFacts`'s consumer states `γ'` as `f ∷ e ∷ d ∷ γ` with
`γ : S ^ (8 + n)` (`CO:6971`). So the six front slots split three and three:
slots 0, 1, 2 are the three existential witnesses of `satGraphOn`
(`src/L/Coding/Graph.lagda.md:104-111`), and **slots 3, 4, 5 are the outer
environment's own front three**, which `TFacts` never reads but `LeafAgree`
does:

- **slot 3** is `appAt`'s value position at `CO:7013-7014`, and
  `DefinesAgree`'s `v` at `CO:7323-7324`.
- **slot 4** is `appAt`'s argument position at `CO:7013-7014`,
  `WitnessAgree`'s `x` at `CO:7307`, and `KeyAgree`'s `c` at `CO:7316`.
- **slot 5** is `DefinesAgree`'s `x` at `CO:7323`.

`appAt f x y = ∃̇∈ (var f) (prAtL zero (suc x) (suc y))`
(`src/L/Coding/Model.lagda.md:160-161`), so the pair is `(x, y)` and slot 4 is
the argument, slot 3 the value.

**SO THE REAL FINDING IS NOT "THREE SLOTS ARE SPARE". IT IS THAT `TFacts` IS
STATED OVER THREE MORE SLOTS THAN IT READS, AND THOSE THREE BELONG TO
`LeafAgree`.** They cannot be dropped from the record's length, because the
length is fixed by the consumer's environment. They can be filled with anything
by a `TFacts` value, because no field of the record reads them.

### 2.3 Slots 1 and 2 are ROLE-NAMED and OBJECT-FREE, and they are not symmetric

Thirteen fields name slots 1 and 2, and every one of them names a role rather
than an identity. `codesK` (`TA:162`) says: anything in slot 2 with code shape
has its components in `K`. At slot 2 empty that is vacuously true. **The record
does not force slot 2 to be THE code set, and this task will not invent that
requirement.**

The two slots differ in what the tree can offer:

- **Slot 2 has one named candidate.** `AllCodes : S` (`src/L/Coding/CodeSet.lagda.md:440`)
  is a named set over a carrier `A`, and at this frame `A` would be `SE.B₀`.
  **It is a CANDIDATE and not a requirement, and there is a real question
  attached to it**: `AllCodes` holds KEYS, by `IsKeyOverAny`
  (`src/L/Coding/CodeSet.lagda.md:434-437`) and `key∈AllCodes` (`:443`),
  whereas `codesK` reads its members as CODES. Whether the key set is the `C`
  the frame means is a mathematical judgement and AD3 gives it to the
  mathematician. I did not instantiate it and I did not price it.
- **Slot 1 has none.** I surveyed every `S`-valued named definition in
  `src/L/Coding/` and the nearest thing is `Sat : ∀ {n} → Formula S n → S`
  (`src/L/Coding/Sat.lagda.md:142`), which is the satisfaction set of ONE
  formula and not a graph pairing codes with values. **No named satisfaction
  graph exists in the tree today.**

That asymmetry is the part of this report most likely to matter next: the graph
is produced existentially by `satGraphOn` and is never named as a closed
object, so a `TFacts` value that wants a named occupant for slot 1 must either
build one or stay universally quantified in `e`, exactly as `twelve-out` and
`twelve-back` already are (`CO:6971-6976`).

### 2.4 The junk value, and why this one

`junk = numeralL 0` (`Probe505.agda:92-93`), in slots 1 to 5.

`numeralL 0` and no other, for three reasons. It is a closed named object, so
the vector is closed and the obligation's type is met. **This frame already
holds it**, at `Kenv` slot 2 (`CO:7391`), so it adds no import, no new
elaboration and no new price. And it is inert: no field reads slots 3, 4, 5 at
all, and the fields that read slots 1 and 2 read them only as containers.

**A slot carrying `junk` below is carrying it because the census found nothing
that names it, or nothing that names an object for it. It is not a claim about
the slot.** The name is in the file so that a later reader cannot mistake a
placeholder for a decision.

## 3. WHAT WAS BUILT, AND HOW EACH TERM IS DECISIVE

`Probe505.agda` is 176 lines. It carries no `TFacts` value, no `src/` change
and no formula of its own.

- **`lengthCheck` (`:64-65`), W3.** Six junk slots consed onto `KV.Kenv` at the
  declared type `S ^ (11 + 9)`. It is decisive because it is stated at the
  record's OWN length and takes `Kenv` whole: if `11 + 9` did not reduce to
  `6 + 14` the term would not elaborate. It sits in its own module `W3`, which
  takes `KValue`'s telescope only, so the length is measured with no ω gate and
  no `SupplyEnv` in scope.
- **`gammaPrime` (`:113-114`), THE OBLIGATION.** `SE.B₀ ∷ junk ∷ junk ∷ junk ∷ junk ∷ junk ∷ KV.Kenv`.
- **`slot0-is-carrier` (`:123-124`).** `refl`. The vector's slot 0 is literally
  the object `SupplyEnv` delivers, not a copy of its definition.
- **`pin-holds` (`:135-136`).** `refl`, and **this is the strongest new result
  in the file.** See 4.1.
- **`slotK-is-bound` (`:139-141`).** `refl` at the index `suc^6 iK`, which is
  where every K-field of the record reads. This is what makes the six-fold
  shift concrete: the record's `K` parameter at `iK` lands on the bound.
- **`tag0` to `tag11` (`:144-167`).** Twelve `refl`s at `suc^6 i0` through
  `suc^6 i11`. Each is stated at the `S` level and the corresponding `tagEq`
  field asks only for the `fst` equation, so each `refl` is strictly stronger
  than the field it answers.
- **`t0-serves-both`, `t1-serves-both` (`:173-176`).** `[LJ-1.502]` is GO and
  its identification is taken, not re-opened: at `t0 := N0` and `t1 := N1` the
  `t0eq` and `t1eq` fields ask of slots 8 and 9 exactly what `tagEq0` and
  `tagEq1` ask, so `tag0` and `tag1` stand unchanged in both field positions.

**WHAT I DID NOT BUILD.** No `TFacts` value (the brief forbids it and twenty of
the fifty nine fields are still unaccounted). No `envK-*` or `envInK-*` term.
No instantiation of `AllCodes`. I did not re-open `[LJ-1.502]`'s identification
or `[LJ-1.503]`'s gate.

## 4. WHAT THE NEXT BRIEF NEEDS

### 4.1 Slot 0 is PINNED, which is stronger than `[LJ-1.499]` recorded

`[LJ-1.499]` fixed slot 0 to `SE.B₀` and called it "the ONE constraint the
frame carries" (`agents/tasks/LJ-1-499/lj-1.499-report.md:209-219`), justified
by the nine `envK-*` and `envInK-*` fields. **That justification is sound and
it is not the whole reason.**

`witK`'s first clause is `var zero ≐ var (suc (suc (suc (suc (suc (suc w))))))`
(`CO:7010`). At `KValue`'s frame `w` is the carrier index `iA`: `KFacts`'s
first parameter is the carrier (`CO:6680-6682`) and `[LJ-1.495]` instantiated
it at `iA` (`agents/tasks/LJ-1-495/Probe495.agda:169`). **So the pin SAYS slot
0 is slot 6.** `pin-holds` shows this vector satisfies it definitionally, by
`refl`.

The consequence for the next brief: **the carrier occupies two slots of `γ'` by
design, 0 and 6, and slot 0 was never free.** A frame decision that moved slot 0
would have to answer the pin, not just the nine fields.

### 4.2 The three questions this report hands back, in the order they bite

1. **Slot 1 has no named object anywhere in the tree, and slot 2 has one
   candidate whose members are keys rather than codes.** Both are in 2.3. This
   is the frame decision `[LJ-1.499]` asked for, now with the search done.
2. **Whether a `TFacts` value should be stated at concrete slots 1 and 2 at
   all.** The consumer quantifies over them (`CO:6971-6976`), so a value that
   fixes them proves less than one that does not. This report does not settle
   which the campaign wants.
3. **Slots 3, 4, 5 are `LeafAgree`'s, not `TFacts`'s** (2.2). If the
   mathematician was considering whether the record should have had `11 + n`
   slots, the answer this measurement gives is that the length is not the
   record's to choose: it is fixed by `f ∷ e ∷ d ∷ γ` at `CO:6971`.

### 4.3 Prices, for funding the next brief

| What | Median wall | Peak RSS | Runs |
|---|---:|---:|---:|
| W3, `lengthCheck` alone | 2.29 s | 611,041,280 B | 3 forced |
| The full file | 3.08 s | 653,164,544 B | 3 forced |

Raw output and `/usr/bin/time -l` records are in `agents/tasks/LJ-1-505/runs/`:
`w3-0` to `w3-2` and `final-0` to `final-2`.

**HOW "FORCED" IS MEANT HERE, BECAUSE MY FIRST ATTEMPT WAS NOT.** I first timed
by touching the source between runs. **That does not force a recheck**: Agda
reuses the interface and prints nothing, and runs 2 and 3 measured interface
LOADING only, which on this file is within about 0.1 s of a real recheck and so
does not announce itself in the wall time. The empty `.out` file is the tell.
Every number above comes from runs that delete
`_build/2.8.0/agda/agents/tasks/LJ-1-505/Probe505.agdai` first, and each of the
six `.out` files is non-empty as a result. **A successor timing one of these
probes should delete the interface, not touch the file.**

W3 is timed in its own file, `agents/tasks/LJ-1-505/runs/ProbeW3.agda`, which
carries the `W3` module and nothing else, so the 2.29 s is the length alone and
not the length inside the full file.

**THE `SupplyEnv` APPLICATION IS CHEAP AT THIS FRAME.** The whole delta from W3
to the full file is 0.79 s, and that covers the `SupplyEnv` module application,
the vector and all seventeen `refl`s. `[LJ-1.499]` paid for the same
application. **Do not fund a successor against this 3.08 s if it builds a
`TFacts` value**: this file states seventeen equations and inhabits no field,
and the unaccounted twenty fields are where the price is.

No heap wall. One Agda process per run, at the wide caliber
`-A64m -I0 -M8g` set on the pane by the program. I did not set `GHCRTS`.

## 5. THE CLAUSES

**W2 (from DD4).** The vector is written once, at `Frame`'s telescope, and it
is generic in `lam` and `gam`. It names no fixed ordinal and no fixed stage. It
takes `KV.Kenv` whole rather than restating its fourteen entries, so the tail is
`KValue`'s one copy and not a second one. There is no conflict with W2 and no
deadline pressure to report.

**W3.** The widest unmeasured term was the length and the brief named it. I
wrote it first, at junk in every front slot, and typechecked it alone before
anything else in the file existed. **GO at 2.29 s.** I report the number I
measured and not the number the brief guessed; the brief's estimate was under
25 s and it was not funded against `[LJ-1.495]`'s 2.44 s.

**W4.** Does not fire. No module was retired and nothing moved to `archive/`.

**The Boundary.** Nothing was committed and nothing was pushed. The working
tree carries exactly the paths in this task's write scope. Every number above
comes from a file in `runs/`. No em dash anywhere in the probe or this
report.

## 6. STOPS

None. The brief named a file and a statement the tree supports, and the
statement is discharged.

## ARCHIVE USED

- **`archive/dev/LJ-dispatch-index.md`. NOT USED.** I searched it for this
  frame and it returned nothing: `grep -n "γ'\|front slot\|environment vector\|Kenv"`
  gives no hit. Declined on evidence rather than unread.
- **`archive/dev/JOURNAL.md`. Not read.** Declined. The Boundary says a live
  document carries no history, and this task needed the current frame, which
  `TwelveAgree.lagda.md` and `Condensation.lagda.md` carry directly.
- **`archive/dev/JOURNAL-archived.md`. Not read.** Declined, same reason.
- **`archive/dev/DECISIONS-archived.md`. Not read.** Declined. The `D<n>` series
  it holds is not a rule in force, and nothing in this task turned on one.
- **`dev/ARCHIVE.md`. Not read.** Declined. W4 does not fire here: no module was
  retired, so there is no row to write and no row to consult.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md`. READ, AND IT CORROBORATES 2.2.**
  `:55` reads:
  `**No source uses two independent bounds.** A formula with two independent bound`
  This is the outside view beside 4.1: this vector holds the carrier at slots 0
  and 6 and the bound at slot 7, which is one bound and one carrier, not two
  bounds. `:37` reads:
  `Rows 3, 4, 5, 6, 8 and 9 agree. **A level-hood formula leaves exactly the two`
  and the pair those rows leave free is the VALUE and the ARGUMENT. **Slots 3
  and 4 of this vector are exactly that pair**, by `appAt` at `CO:7013-7014`.
  So the three slots `TFacts` does not read are not an accident of this port:
  they are where the literature puts the free pair.
- **`dev/literature/devlin-II5.md`. Not read.** Declined. It carries Devlin's
  level-hood chain and its complexity requirements, and `level-formula-slot-roles.md:7-9`
  records that it does NOT carry the slot arithmetic, which is what this task
  needed.
- **`dev/literature/digest.md`. Not read.** Declined. It pins the orthodox rud
  route, and this task settled a slot census inside an existing port.
- **`dev/literature/terms-2026-08.md`. Not read.** Declined. It is a
  terminology dossier for an owner's ruling, and this task minted no term and
  proposed no glossary entry.
- **`dev/literature/truncation-and-selection.md`. Not read.** Declined. It is
  about how a witness is picked, and this task picked no witness: it reports
  slots 1 and 2 as object-free rather than choosing occupants for them.
