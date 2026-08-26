# review-of-levelin-from-level-formula: the level formula reaches the collapse's BELIEF and never its SOUNDNESS

**THIS IS A STOP, AND IT IS THE DELIVERABLE.** The brief orders one term,
`levelin-from-level-formula`, from `[LJ-1.650]`'s `LevelFormula` to
`[LJ-1.653]`'s `HoodExistsP` and `HoodSoundP` "at the formula it carries".
**That term is not in `Probe657.agda` and this file says why.** The probe is
green and carries no hole (`runs/final-1.out`, exit 0 in 6.89 s); the
obligation reads `missing` (`runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`); the twenty-two names the probe does
deliver are all green (`runs/meter-names.out`, `0 UNRESOLVED of 22`).

**The brief asked for the right measurement and premise 4 named the right
risk.** The answer is that the alphabet gap is real, that it is CURABLE, and
that curing it does not open the road, because a second gap sits behind it
and that second gap is step 4.

## 1. THE OBLIGATION AS WRITTEN CANNOT BE TYPED, AND AGDA SAYS SO

Read the two formula slots side by side, at the lines each was taken from.

```
LevelFormula   (agents/tasks/LJ-1-650/Probe650.agda:322-324)
    Σ[ lv ∈ Formula Code 2 ] ( <sound at the STAGE> × <complete at the STAGE> )

HoodExistsP    (agents/tasks/LJ-1-653/Probe653.agda:283-284)
    Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)

HoodSoundP     (agents/tasks/LJ-1-653/Probe653.agda:235-236)
    Formula (⊥* {ℓ-suc ℓ}) 2 → Type (ℓ-suc ℓ)
```

`Code : Type ℓ` (`src/L/Hull.lagda.md:72`), so `Formula Code 2 : Type ℓ`.
`⊥* {ℓ-suc ℓ} : Type (ℓ-suc ℓ)`, so `Formula (⊥* {ℓ-suc ℓ}) 2` is one
universe higher. **The two formula types are not in the same universe, so the
brief's conclusion cannot be stated at the brief's hypothesis.**

I did not argue this. I wrote the obligation the only way it can be written
and let Agda name the fault.

**FIRST SLICE, THE OBLIGATION ITSELF** (`runs/NoPinned.agda.txt`,
`runs/nopinned-1.out`, exit 42 in 3.78 s):

```
NoPinned.agda:52.23-29: error: [UnequalLevel]
ℓ-zero != ℓ-suc ℓ
when checking that the expression fst lf has type
FOL.Syntax.Formula ⊥* 2
```

**SECOND SLICE, THE FORMULA SLOT ALONE** (`runs/NoAlphabet.agda.txt`,
`runs/noalpha-1.out`, exit 42 in 3.13 s), with the level written out so the
message cannot be blamed on a metavariable:

```
NoAlphabet.agda:55.27-33: error: [UnequalLevel]
ℓ-zero != ℓ-suc ℓ
when checking that the expression fst lf has type Formula ⊥* 2
```

Both files are RED BY CONSTRUCTION and both are kept as `.agda.txt`, so
acceptance conjunct 1 does not run them.

## 2. AND THE RELABELLING THAT WOULD CROSS THE ALPHABET IS REFUTABLE

Relabelling carries `⊥*` INTO any alphabet and never out of one. `embed` is
that direction (`src/FOL/Manipulation/Relabelling.lagda.md:117-118`), and the
direction the brief needs is `mapFo f` for some `f : Code → ⊥*`.

**No such `f` exists, and the refutation takes no hypothesis at all**
(`Probe657.agda:83-84`, green):

```
no-relabelling-out-of-Code : (T.Code → ⊥* {ℓ-suc ℓ}) → Empty.⊥
no-relabelling-out-of-Code f = Empty.rec* (f code-inhabited)
```

`code-inhabited` is `T.wit 0 ⊤̇ []` (`Probe657.agda:81`). `wit` is a
CONSTRUCTOR of `Code` (`src/L/Hull.lagda.md:72-74`) and it asks only for a
parameter-free formula and a vector of codes. So `Code` is inhabited with no
fact about `lam`, `X` or the hull, and the alphabet crossing dies at every
instance and not just at a hard one.

The same two lines run alone as the W3 miniature: `runs/W3.agda`,
`runs/w3-final.out`, exit 0 in 2.43 s.

## 3. THE UN-PINNED READING CAN BE WRITTEN, AND THREE OF ITS FOUR FACTS ARE FREE

`[LJ-1.653]` also states the pair UN-pinned, at `Formula CIso.I.SM 2`
(`HoodExists`, Probe653.agda:263-267; `HoodSound`, Probe653.agda:191-195),
and the tree already carries `Code → SM`: `DownReflect.codeValM`
(`src/L/BoundedSubset.lagda.md:377-378`). So the crossing that DOES exist is
one line (`levelFo`, `Probe657.agda:96-97`).

Under that reading the level formula pays, with no step 4 anywhere in the
terms:

| fact | term | what it spends |
|---|---|---|
| `HoodComplete` | `hoodComplete-from-level`, `Probe657.agda:198-200` | `ElemDown` only |
| `HoodExists` | `hoodExists-from-level`, `Probe657.agda:146-149` | `ElemDown`, `PiReflectsOrd` |

`ElemDown` is the tree's OWN named residue
(`src/L/BoundedSubset.lagda.md:410-412`), already taken as a hypothesis by
`AtHullInstance.reflect` (`src/L/BoundedSubset.lagda.md:782`), so it is not
new debt. `PiReflectsOrd` is `[LJ-1.649]`'s fifth fact, verbatim
(`agents/tasks/LJ-1-649/Probe649.agda:222-223`), named there as unbuilt.

**So the collapse's BELIEF is bought.** Both halves of what the hull and the
collapse THINK about level-hood come out of the stage formula.

## 4. THE FOURTH FACT IS STEP 4 ITSELF, AND THE CIRCLE IS A TERM

`HoodSound` is not a belief. It says the value the collapse believes is the
level really IS the level, in the AMBIENT hierarchy. `LevelFormula`'s
soundness says the same thing at the STAGE. Carrying one to the other means
carrying `π` past `Lset`, and that is `[LJ-1.462]`'s step 4 at ordinals.

`hoodSound-from-level` (`Probe657.agda:253-256`) is green and it spends
`Hd.PiCommuteLsetOrd` at exactly one line (`Probe657.agda:274`). Nothing else
in the file spends it.

**And the price is not a side condition. It is the same fact under a second
name** (`hoodsound-is-step4`, `Probe657.agda:344-351`, green):

```
(PiCommuteLsetOrd → HoodSound (levelFo lf))
×
(HoodSound (levelFo lf) → PiCommuteLsetOrd)
```

The second component is `[LJ-1.653]`'s own `step4-at-ord`
(`agents/tasks/LJ-1-653/Probe653.agda:200-203`), whose completeness half
section 3 supplies for free. So the two implications close, and step 4 is not
a hypothesis this route can shed.

## 5. THE PRICED ROUTE IS DOMINATED BY A TERM THAT IS ALREADY GREEN

If step 4 has to be paid anyway, the level formula buys nothing on this road.
`[LJ-1.649]`'s `levelin-from-647-ord-commute`
(`agents/tasks/LJ-1-649/Probe649.agda:241-245`, GO by
`agents/tasks/LJ-1-649/lj-1.649-report.md:147`) reaches the SAME conclusion
from a SUBSET of the hypotheses: no level formula and no elementarity.

That predecessor's own term inhabits the type with no adapter
(`lj649-route`, `Probe657.agda:365-366`), and the domination is the body of
`levelin-priced-is-dominated` (`Probe657.agda:368-371`), which ignores both
`lf` and `Elem`:

```
levelin-priced-is-dominated lf e pro hcl s4 = lj649-route pro hcl s4
```

## 6. WHAT WOULD REPAIR THE ALPHABET, AND WHY IT IS NOT ENOUGH

**The literature states the level-hood formula PARAMETER-FREE.**
`dev/literature/level-formula-slot-roles.md:37` reads "Rows 3, 4, 5, 6, 8 and
9 agree. **A level-hood formula leaves exactly the two", and row 9
(`:31`) quotes Schindler-Zeman 1.10(2): the formula "does not depend on `α`".
So `Lv.LevelFormula` typed at `Formula Code 2` is WEAKER than the object the
sources describe, and the alphabet gap is a defect of the Bedrock statement
and not of `[LJ-1.653]`.

Stated parameter-free, the pinned pair becomes reachable, and this is
MEASURED and not argued. `LevelFormulaP` (`Probe657.agda:412-419`) is the
same statement over `Formula (⊥* {ℓ-suc ℓ}) 2`; `levelP→level`
(`Probe657.agda:423-424`) lands in `[LJ-1.650]`'s own type with no adapter,
so it is a strengthening and nothing else; and then

- `hoodExistsP-from-levelP` (`Probe657.agda:435-437`) is GREEN and spends
  `ElemDown` and `PiReflectsOrd` only.
- `hoodSoundP-from-levelP` (`Probe657.agda:458-460`) is GREEN and spends
  step 4, UNCHANGED.

**So the alphabet repair moves the existential half and leaves the soundness
half exactly where it was.** The second gap is about the two CARRIERS and not
about the alphabet, and no restatement of the formula can move it.

## 7. WHAT THIS FILE DOES NOT CLAIM

1. **It does not refute `HoodSound`.** `[LJ-1.653]` section 5 already forked
   its remaining leg into (a) `C.πX ⊆ L` and (b) an ambient `Lset-only`
   (`agents/tasks/LJ-1-653/lj-1.653-report.md`). Nothing here prices either.
2. **It does not claim `LevelFormula` is worthless.** It closes
   `[LJ-1.650]`'s `CodedCover` (`coded-cover-from-level`,
   `agents/tasks/LJ-1-650/Probe650.agda:385-386`) and it pays two of the
   three Hood facts here. It does not pay the third.
3. **It does not measure whether `PiReflectsOrd` is cheap.** It enters as a
   hypothesis at the type `[LJ-1.649]` named.
4. **It changed nothing in `src/`.**
