# LJ-1.308 report: adversarial DD25 review of `[LJ-1.306]`

tier: opus (in-harness-subagent-mode). Review, lands nothing.
Written incrementally (C-22). Every negative is MEASURED or INFERRED,
in those words.

## 0. VERDICT

**SPLIT.**

**THE NUMBERS HOLD. THE EVIDENCE BEHIND ONE OF THEM DID NOT.**

**What holds, and I re-derived each one:**

1. **The zero.** `0 of 4,738 copied non-blank lines changed` is TRUE. I
   re-derived it by a whole-sequence diff, which is stronger than the
   target's verbatim-run search. Section 2.
2. **The dismissal「no consumer writes that equation」.** TRUE at all 31
   external reaches. Section 1.
3. **`KFacts` has zero external consumers.** TRUE. Section 1.4.
4. **The 45-line scaffold.** TRUE for hand-written code, and exact.
   Section 3.
5. **The C-42 retirement is scoped.** It does not license wave 2.
   Section 4.
6. **The 180.** It stands on the caliber `[LJ-1.298]` wrote it in.
   Section 5.
7. **「The AC-against-GCH end gains nothing」.** TRUE, and I MEASURED it.
   Section 6.

**What falls, all MEASURED:**

1. **The serving evidence tested names the consumers do NOT write.**
   `ProbeCompat.agda` checked the FIRST field of each row module. The
   consumers write the LAST field. **Ten of twelve row fields went
   unchecked.** It checked `EnvSet.φB` and `EnvSet.φ`; the consumer
   writes `EnvSet.back`. It checked 2 of the 12 clause names the two
   `sixAt` formulas write. This is C-40 exactly. Section 1.
2. **「39 checks」is 37.** `ProbeCompat.agda` holds 37 top-level
   declarations. Section 1.5.
3. **「Two `EnvSet` refls, for `L.Coding.EnvSupply`'s two names」is
   FALSE.** `EnvSupply` names `envSetB` and `EnvSet.back`. Section 1.3.
4. **The scaffold's context.** 247 non-blank lines are neither blank nor
   copied from the chapter, not 45 plus 19. Section 3.
5. **The DD4 axis is not DD4's own axis** (C-46). Section 6.

**AND THE BRIEF'S OWN ARITHMETIC IS WRONG (C-44).** 「Seven at that rate
is 357」multiplies an AMBIENT TIE SUPPLY figure into a GENERIC PORT
budget. The two are different buckets, and `[LJ-1.302]` says so at
`agents/tasks/LJ-1-302/lj-1.302-report.md:205-209`. Section 5.

**THE PORT IS SAFE TO FUND.** Its conclusions survive. Its serving
evidence needed the 26 checks I ran, and they are green.

## 1. ATTACK 1: THE 「NO CONSUMER WRITES THAT EQUATION」 DISMISSAL

**THE DISMISSAL HOLDS, and I MEASURED it where `[LJ-1.306]` inferred
it.** My probe is `agents/tasks/LJ-1-308/ProbeReach.agda`, exit 0, 9 s,
load 4.36 to 4.31, 3 users, one agda process, `GHCRTS="-A64m -I0 -M8g"`,
cap never raised.

### 1.1 EVERY REACH, COUNTED AND CLASSIFIED

`[LJ-1.306]` counts 31 reaches over four external files. I confirm the
count. **I do not confirm that its probe tested them.**

| consumer | reach | site | target kind |
|---|---|---|---|
| `LowerAgree` | `envHypB2` | `:58` | `Formula` |
| `LowerAgree` | `Mem.memBndAt` | `:295` | `Formula` |
| `LowerAgree` | `Eq.eqBndAt` | `:300` | `Formula` |
| `LowerAgree` | `And.andBndAt` | `:305` | `Formula` |
| `LowerAgree` | `Or.orBndAt` | `:308` | `Formula` |
| `LowerAgree` | `Imp.impBndAt` | `:311` | `Formula` |
| `LowerAgree` | `Neg.negBndAt` | `:314` | `Formula` |
| `LowerAgree` | `MemAgree` `.out` `.back` | `:255`, `:331`, `:340` | `⟨ _ ⊨ _ ⟩` |
| `LowerAgree` | `EqAgree` `.out` `.back` | `:262`, `:332`, `:341` | `⟨ _ ⊨ _ ⟩` |
| `LowerAgree` | `AndAgree` `.out` `.back` | `:269`, `:333`, `:342` | `⟨ _ ⊨ _ ⟩` |
| `LowerAgree` | `OrAgree` `.out` `.back` | `:275`, `:334`, `:343` | `⟨ _ ⊨ _ ⟩` |
| `LowerAgree` | `ImpAgree` `.out` `.back` | `:281`, `:335`, `:344` | `⟨ _ ⊨ _ ⟩` |
| `LowerAgree` | `NegAgree` `.out` `.back` | `:287`, `:336`, `:345` | `⟨ _ ⊨ _ ⟩` |
| `UpperAgree` | `succU` | `:229` | `Type`, body `⟨ _ ∈ _ ⟩` |
| `UpperAgree` | `keyU` | `:236` | `Type`, body `⟨ _ ∈ _ ⟩` |
| `UpperAgree` | `Top.topBndAt` | `:296` | `Formula` |
| `UpperAgree` | `Bot.botBndAt` | `:299` | `Formula` |
| `UpperAgree` | `Exist.existBndAt` | `:302` | `Formula` |
| `UpperAgree` | `Forall.forallBndAt` | `:305` | `Formula` |
| `UpperAgree` | `AllIn.allInBndAt` | `:308` | `Formula` |
| `UpperAgree` | `ExIn.exInBndAt` | `:313` | `Formula` |
| `UpperAgree` | `TopAgree` `.out` `.back` | `:253`, `:332`, `:341` | `⟨ _ ⊨ _ ⟩` |
| `UpperAgree` | `BotAgree` `.bot-out` `.bot-in` | `:259`, `:333`, `:342` | `⟨ _ ⊨ _ ⟩` |
| `UpperAgree` | `ExistAgree` `.out` `.back` | `:264`, `:334`, `:343` | `⟨ _ ⊨ _ ⟩` |
| `UpperAgree` | `ForallAgree` `.out` `.back` | `:272`, `:335`, `:344` | `⟨ _ ⊨ _ ⟩` |
| `UpperAgree` | `AllInAgree` `.out` `.back` | `:280`, `:336`, `:345` | `⟨ _ ⊨ _ ⟩` |
| `UpperAgree` | `ExInAgree` `.out` `.back` | `:287`, `:337`, `:346` | `⟨ _ ⊨ _ ⟩` |
| `TwelveAgree` | `succU` | `:371` | `Type`, body `⟨ _ ∈ _ ⟩` |
| `TwelveAgree` | `keyU` | `:378` | `Type`, body `⟨ _ ∈ _ ⟩` |
| `EnvSupply` | `envSetB` | `:424`, `:443` | `Formula` |
| `EnvSupply` | `EnvSet.back` | `:444` | `⟨ _ ⊨ _ ⟩` |

**IS THE TARGET SQUASHED AT EVERY REACH? YES. MEASURED.**

- **Every `*Agree` field the consumers write has type
  `⟨ γ ⊨ X ⟩ → ⟨ γ ⊨ Y ⟩`.** `⟨ _ ⟩` is the carrier of an `hProp` under
  `open TruthAlgebra (hPropAlgebra (ℓ-suc ℓ))`. Both ends are
  propositions. MEASURED, by reading all 24 `out` and `back` signatures.
  Example: `src/L/Condensation.lagda.md:4463` and `:4483`.
- **`succU` and `keyU` declare `Type (ℓ-suc ℓ)`**, at
  `src/L/Condensation.lagda.md:3837` and `:3843`. **This is the one place
  where「satisfaction is squashed」is the wrong word.** Their bodies are
  `⟨ _ ∈ _ ⟩` at `:3838-3841` and `:3844-3846`. They are membership
  propositions, not satisfaction, and they ARE prop-valued. MEASURED. The
  substance holds; the word does not.
- **Every other reach is `Formula`-valued.** A formula is data. Proof-term
  identity cannot apply.

**No consumer writes an equation between two proof terms.** MEASURED, by
this search: `grep -n '≡'` over the four consumer files, filtered to the
lines that also name a reached name (`Agree`, `*BndAt`, `succU`, `keyU`,
`envSetB`, `EnvSet`, `envHypB2`, or one of the twelve module aliases `M.`
to `EI.` and `ES.`). **The filtered result is EMPTY in all four files.**
The consumers APPLY the fields. `LowerAgree:331-336` and `:340-345`, and
`UpperAgree:332-337` and `:341-346`, are the only application sites. All
four build tuples.

**So the dismissal is correct. The failure at
`agents/tasks/LJ-1-306/ProbeCompat.agda`'s first form does not bind.**

### 1.2 BUT THE EVIDENCE THE TARGET CITED TESTED THE WRONG NAMES

**This is C-40, and it is the review's main finding.**

**The row modules.** The twelve modules `Bot`, `Top`, `Neg`, `Forall`,
`And`, `Or`, `Imp`, `Mem`, `Eq`, `AllIn`, `ExIn` and `Exist` sit at
`src/L/Condensation.lagda.md:1127` to `:1416`. They carry 28 fields in
all. `ProbeCompat.agda:92-140` checks **the first field of each**:
`botBndAt`, `topBndAt`, `subN`, `subF`, `subA`, `subO`, `subI`, `subE`,
`bodyM`, `bodyE`, `subA`, `subE`.

**The consumers write the LAST field of each: the `*BndAt` one.** Two of
the twelve coincide, because `Bot` and `Top` hold one field only.
**Ten of the twelve fields the external consumers name were NOT
checked.** MEASURED, by the table in 1.1 against `ProbeCompat.agda:92`.

**The clause names.** `LowerAgree:319-327` and `UpperAgree:320-328` build
`sixAt` from twelve COMMITTED `L.Coding.Model` clause names. The ported
`*Agree` modules produce the GENERIC twins. `ProbeCompat.agda:72-86`
checks four names, of which two are clause names: `botClauseAt` and
`topClauseAt`. **Ten of the twelve clause identities went unchecked.**
MEASURED.

**I ran the missing checks. ALL 26 ARE GREEN.**
`agents/tasks/LJ-1-308/ProbeReach.agda`, exit 0, 9 s:

| section | checks | result |
|---|---:|---|
| A. all twelve clause names, generic-at-class against committed | 12 | green |
| B. all twelve `*BndAt` row fields, original against generic | 12 | green |
| C. `envSetAt`, generic-at-class against committed | 1 | green |
| D. `EnvSet.back` in `EnvSupply`'s own serving shape | 1 | green |

**The eleven unmeasured `*Agree` serving reaches now follow by
conversion, not by analogy.** `φB` is DEFINED as the row field:
`src/L/Condensation.lagda.md:4458` reads
`φB = Mem.memBndAt C T B N K t0 t1`, and `:3693` reads
`φB = Top.topBndAt C T B N K`. So each `out` has type
`⟨ γ ⊨ memClauseAt … ⟩ → ⟨ γ ⊨ Mem.memBndAt … ⟩`. Section A measured the
left type identical, section B measured the right type identical, and
`GenAgree.agda` exit 0 proves the term inhabits the generic type. Two
definitionally equal types accept the same term. **MEASURED, not
INFERRED.**

### 1.3 THE `EnvSet` CLAIM IS FALSE AS WRITTEN

`agents/tasks/LJ-1-306/lj-1.306-report.md:182` says「Two `EnvSet` refls,
for `L.Coding.EnvSupply`'s two names」.

**`L.Coding.EnvSupply` names `envSetB` and `module EnvSet` at
`src/L/Coding/EnvSupply.lagda.md:47`. Inside `EnvSet` it writes ONE
field, `back`, at `:444`.** MEASURED, by grep over the file.

`ProbeCompat.agda:273-293` checks `EnvSet.φB` and `EnvSet.φ`. Those are
the formula fields at `src/L/Condensation.lagda.md:2949` and `:2952`.
**`EnvSupply` writes neither.** MEASURED.

`EnvSet.back` has type
`⟨ γ ⊨ envSetAt E ar B ⟩ → ⟨ γ ⊨ envSetB E ar B K ⟩` at
`src/L/Condensation.lagda.md:3042`. Its SOURCE type carries `envSetAt`,
a cross-boundary name that `ProbeCompat` did not check. My section D
checks `back` in the consumer's exact shape, and my section C checks
`envSetAt`. Both green.

**The report's claim that both fields are formula-valued is TRUE.** The
defect is that they are not the fields the consumer reaches.

### 1.4 `KFacts`: ZERO IS THE RIGHT NUMBER

**MEASURED TRUE.** `grep -rn 'KFacts' src/` returns 25 hits. Twenty-four
sit in `src/L/Condensation.lagda.md`, from `:6075` to `:7317`. The one
hit outside is a COMMENT at `src/L/Condensation/UpperAgree.lagda.md:52`,
which reads「never a KFacts record field (P-x)」. **A comment is not a
reach.** So `KFacts` has zero external code consumers, and the nominal
record exception does not bind any file outside the chapter.

### 1.5 「39 CHECKS」IS 37

`agents/tasks/LJ-1-306/lj-1.306-report.md:167` says「39 checks green」.

**`ProbeCompat.agda` holds 37 top-level declarations.** MEASURED, by
`grep -c -E '^(chk|served)[^ ]* *:'`. The report's own itemization at
`:171-183` also sums to 37: 4 formula refls, 27 term-identity refls, 4
serving checks and 2 `EnvSet` refls. **The lead figure and the
itemization disagree by 2, and the itemization is right.**

## 2. ATTACK 2: THE ZERO, RE-DERIVED INDEPENDENTLY

**THE ZERO HOLDS, and my method is stronger than the target's.**

`[LJ-1.306]` used a verbatim-run search over `manifest.json`. A run
search can report zero because nothing changed, or because it does not
see the change. I used a whole-sequence diff instead. My script is
`agents/tasks/LJ-1-308/verify_zero.py`.

**Method.** I concatenated the 146 chapter spans in manifest order into
an expected text. Then I aligned that text against the whole port with
`difflib.SequenceMatcher`, `autojunk=False`. A whole-sequence alignment
reports `delete` and `replace` operations. A per-block run search cannot
report them.

**Result.**

| quantity | value | source |
|---|---:|---|
| manifest blocks | 146 | `manifest.json` |
| chapter span lines | 5,131 | my sum over the spans |
| chapter span non-blank lines | 4,711 | my count |
| blocks NOT found as exact runs | **0** | my own run search |
| diff `delete` lines | **0** | `SequenceMatcher` |
| diff `replace` hunks | **0** | `SequenceMatcher` |
| diff `insert` lines | 413 (247 non-blank) | `SequenceMatcher` |

**Zero deletions and zero replacements mean the expected text is an
exact ordered sub-sequence of the port.** Nothing was reordered. Nothing
was edited. The 4,711 figure and the 5,131 figure both re-derive exactly.
MEASURED, by `agents/tasks/LJ-1-308/verify_zero.py`.

**The Shape half also re-derives.** Port lines `:76-109` hold 27
non-blank code lines. `[LJ-1.306]` says 27. MEASURED. Section 3 gives the
count.

**4,711 + 27 = 4,738.** The claim `0 of 4,738 copied non-blank lines
changed` is TRUE. **This attack UPHOLDS the target.**

**One record defect, not a number defect.** The port's header comment at
`agents/tasks/LJ-1-306/GenAgree.agda:14-15` cites Shape at `:99-104` and
`:170-191`. The report at `agents/tasks/LJ-1-306/lj-1.306-report.md:76-77`
cites `:99-105` and `:169-190`. The two records disagree by one line at
three of six endpoints. MEASURED. The copied text is identical either
way, so no figure moves.

## 3. ATTACK 3: THE 45-LINE SCAFFOLD

**45 IS THE HONEST COUNT OF HAND-WRITTEN CODE. It is NOT the count of
non-copied content, and the report's「plus a 19-line header comment」
understates that content by 156 non-blank lines.**

**The whole file, classified.** MEASURED, by `verify_zero.py` and by
`agents/tasks/LJ-1-308/uncovered.txt`:

| class | non-blank lines |
|---|---:|
| copied from `src/L/Condensation.lagda.md` | 4,711 |
| copied from `src/L/Coding/Shape.lagda.md` (`:76-109`) | 27 |
| hand-written CODE (`:1`, `:21-69`) | **45** |
| comment (`:3-19`, `:71-74`, `:111-115`, `:5395-5543`) | **175** |
| port total non-blank | 4,958 |

4,711 + 27 + 45 + 175 = 4,958. The arithmetic closes exactly.

**The 45 is exact.** Line `:1` is the OPTIONS pragma. Lines `:21-69` hold
44 non-blank lines: the imports, the eight-parameter telescope, the `GM`
application and the three opens. 1 + 44 = 45. MEASURED.

**「Load-bearing」excludes comments, and that is where the report loses
scale.** The report names one 19-line header comment. The true comment
volume is 175 non-blank lines: 17 in the header at `:3-19`, 4 at
`:71-74`, 5 at `:111-115`, and **149 in the trailing manifest at
`:5395-5543`**. The header is 17 lines and not 19. MEASURED.

**Why this matters for a price.** `AGENTS.md` fixes the caliber, and
`dev/ledger.toml:12-13` states it: a size figure counts non-blank lines
inside ` ``agda ` fences. A comment inside a fence is a non-blank line
inside a fence. **On the project's own caliber the port adds 220
non-blank lines the chapter did not have**, not 45: 45 code plus 175
comment. The 149-line manifest is a probe artefact and would not land.
The other 26 comment lines would.

**Verdict on attack 3: SPLIT.** The 45 is honest for hand-written code.
The report's summary understates the non-copied content, MEASURED.

## 4. ATTACK 4: THE C-42 CLAIM

**THE RETIREMENT IS SCOPED. It does not license wave 2. UPHELD.**

`agents/tasks/LJ-1-306/lj-1.306-report.md:106` reads:「The C-42 caveat on
the clean modules is now retired **for the port itself**.」

**Three tests, all passed. MEASURED, by reading the report whole.**

1. **The claim names its object.** 「For the port itself」 restricts the
   retirement to the zero-changed COPY rate at the 23 sites. It does not
   claim the modules SERVE, and it does not claim anything about the
   dirty seven.
2. **The dirty seven stay INFERRED.** Section 6 row at `:270` reads
   「the dirty seven typecheck verbatim against the landed chapter |
   **INFERRED.** Their port is wave 2, not checked today」. Section 9 at
   `:315-317` repeats it.
3. **The serving half stays INFERRED too.** Section 6 row at `:271`
   reads「the other 18 clean modules serve, untested one by one |
   **INFERRED** … C-42」. **The report separates the COPY claim from the
   SERVING claim, and marks each correctly.**

**One overstatement remains, and it is section 6, not section 2.** The
row at `:267` reads「the generic family fails to serve an external
consumer | **MEASURED FALSE** at 39 checks」. Section 1.2 shows the 39
checks did not test the consumers' own names. **That row should have read
INFERRED on the evidence the report held.** It reads MEASURED. My
`ProbeReach.agda` now makes it MEASURED in fact, so the row is true
today, but it was not true when it was written. MEASURED.

**C-42's own sweep instruction was followed.** `[LJ-1.298]`'s clean-list
claim was refuted, and `[LJ-1.306]` swept the whole 23 rather than the
one module that failed. It found five, not one. That is the sweep C-42
asks for, and `dev/LESSONS.md:3713-3715` is the rule.

## 5. ATTACK 5: THE 180, SETTLED AGAINST `[LJ-1.302]`'s 51

**THE BRIEF'S ARITHMETIC IS WRONG. The 51 and the 180 are different
buckets, and multiplying one into the other is a category error.
MEASURED.**

### 5.1 WHAT THE 51 IS

`agents/tasks/LJ-1-302/lj-1.302-report.md:44-45` reads: the
「telescope ties SUPPLY at the ambient carrier as terms, from delivered
lemmas, at a concrete environment: 51 non-blank supply lines」.

**The 51 is AMBIENT INSTANTIATION cost. It is not generic port cost.**
The same report at `:283` records the dirty module's GENERIC PORT at
「0 of 41 lines changed, `GenDomainAgree.agda`」. **A dirty module costs
ZERO hand-written lines to port.** MEASURED, by `[LJ-1.302]`.

### 5.2 SEVEN AT THAT RATE IS NOT 357

`[LJ-1.302]` already priced the seven, and the figure is not 7 times 51.
At `:191` it reads「**The ties are ONE debt, not sixteen.**」At `:205-209`
it gives the DD8 number: **about 100 lines** for the whole dirty seven,
made of about 20 shared closure lines plus about 10 per module.

**So the brief's「357, not 135」rests on a rate the source report
explicitly refuses.** MEASURED FALSE, at
`agents/tasks/LJ-1-302/lj-1.302-report.md:191` and `:205-209`.

**And the 100 does not compete with the 180 either.**
`agents/tasks/LJ-1-298/lj-1.298-report.md:300-303` excludes the ambient
supply from the 180 in writing:「The dirty seven's hypothesis telescopes
at the ambient carrier. Unmeasured.」and「Its price is not my 180-line
figure.」

### 5.3 DOES THE 180 STAND

**On `[LJ-1.298]`'s own caliber: YES, with about 30 lines of margin.**

`agents/tasks/LJ-1-298/lj-1.298-report.md:140-142` sets the 180 as
「38 of scaffolding, about 145 of formula re-statements and gap syntax」.
Its own gap itemization at `:120-133` is: `keyArityAtL` 1, `hasWitnessAt`
3, `twelveAt` 11, `satGraphAt` about 16, the
`DefBody`/`envOneAt`/`DefinesAt`/`isCodeAt` group about 12, the
`L.Coding.Shape` `shapes` syntax about 40, and an unquantified part of
`L.Coding.Model`'s 374-line clause region.

**Wave 1 discharged the Shape term by COPYING.** 27 copied lines replace
the 40-line hand-written estimate. So the residual named gaps are about
43 plus the clause-region term, which the 180 implies at about 62. That
is about 105.

Measured scaffold 45, plus about 105 residual, is about 150 against 180.
**The 180 stands.** Basis: `[LJ-1.298]`'s itemization for the gaps, my
count for the scaffold.

**On the PROJECT's caliber: it is TIGHT, and it may fail.**

The project counts every non-blank line inside an ` ``agda ` fence,
whatever its provenance. On that caliber wave 1 costs **72 code lines**
(45 scaffold plus 27 Shape), or **98** with the 26 landing comment lines
of section 3. Against the same about-105 residual:

| caliber | wave 1 | remaining of 180 | residual gaps | margin |
|---|---:|---:|---:|---:|
| `[LJ-1.298]`, hand-written code only | 45 | 135 | about 105 | about 30 |
| project, code copied or written | 72 | 108 | about 105 | about 3 |
| project, plus landing comments | 98 | 82 | about 105 | **about -23** |

**So the 180 survives on the caliber it was written in and has no
margin on the caliber the ledger uses.** MEASURED for wave 1, INFERRED
for the residual, whose basis is `[LJ-1.298]`'s survey and not a probe.

**The scaffold also grew.** `[LJ-1.298]` projected 38. The measurement is
45. That is +7 against its own line, and the report at `:39-42` does not
say so.

### 5.4 WHAT WOULD SETTLE IT

**Nothing here settles the dirty seven's GAPS, and no probe has.** They
are the widest unmeasured term in the route (DD8). `[LJ-1.302]` measured
their TIES at about 100 lines and their PORT at zero changed lines.
Neither figure is the gap figure. **A wave 2 build brief that cannot name
that term and its probe is not ready to send.**

## 6. DD4, WITH THE AXIS NAMED (C-46)

**NAME MY AXIS: I report on DD4's OWN axis, AC-against-GCH, and I ran
the rule's own report.**

**Statement 1 of the brief: DD4's axis is AC-against-GCH, fixed in code
at `scripts/measure/ledger.py:50`. TRUE.** That line reads
「`ledger.py --reuse`   DD4's report: what the AC and GCH closures share,
in」. MEASURED.

**Statement 2 of the brief: `src/L/Condensation.lagda.md` sits in NEITHER
trophy closure. TRUE, MEASURED.**

My script is `agents/tasks/LJ-1-308/closure_check.py`. It walks the
transitive import graph from each declared root over git-tracked masters
under `src/`. Roots: `ac_root = "src/L/Model.lagda.md"`,
`gch_root = "src/L/GCH.lagda.md"` at `dev/ledger.toml:170` and `:203`.

| closure | masters | `L.Condensation` inside |
|---|---:|---|
| AC | 73 | **no** |
| GCH | 51 | **no** |
| shared | 44 | n/a |

My 73, 51 and 44 reproduce `ledger.py --reuse` exactly, so the walk is
the same instrument. **`L.Condensation` and all four of its external
consumers sit outside both closures.** MEASURED.

**Therefore `[LJ-1.306]`'s second DD4 statement is TRUE, and now it has
evidence.** The report says at `:252`「The second end, AC against GCH,
gains nothing from this port」. A module outside both closures moves no
cell of the reuse report. Zero AC lines, zero GCH lines and zero shared
lines change. **The report asserted this; I measured it.**

**But `[LJ-1.306]`'s named axis is NOT DD4's own axis.** It names
「the port's L-against-ambient axis」at `:235`. C-46 at
`dev/LESSONS.md:4008-4010` fixes DD4's axis as AC-against-GCH in code.
**The L-against-ambient axis is a real axis and a useful one. It is not
the rule's.** The report is honest, because it names both ends and says
which is which. It is on a proxy axis for the first end, and C-46 asks
for that qualifier. It is missing.

**ONE CORRECTION TO A LESSON, for the orchestrator.**
`dev/LESSONS.md:4014-4016` states that `--reuse` prints no GCH endpoint
and that「DD4's own report has never been able to run」. **That is STALE
today.** `dev/ledger.toml:203-204` records `gch_root =
"src/L/GCH.lagda.md"`, landed 2026-08-15 by `[LJ-1.280]`, and the report
runs and prints all four figures. MEASURED, by running it. I did not edit
`dev/LESSONS.md`; the correction is the orchestrator's.

**DD4 in one sentence for this port.** The port maximizes shared code on
the L-against-ambient axis, at chapter scale, by making 4,738 lines serve
two carriers at the cost of 45. **On DD4's own axis it is neutral by
structure, because the chapter is in neither trophy closure.**

## 7. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| a copied non-blank line changed | **MEASURED FALSE.** Whole-sequence diff, 0 delete and 0 replace, `verify_zero.py` |
| a copied block was reordered | **MEASURED FALSE.** The expected text is an ordered sub-sequence |
| a consumer writes a proof-term equation on an `Agree` field | **MEASURED FALSE.** All 31 reaches read, section 1.1 |
| a reach lands in an unsquashed position | **MEASURED FALSE.** All 24 `out`/`back` types are `⟨ _ ⟩`; `succU` and `keyU` bodies are `⟨ _ ∈ _ ⟩` |
| `KFacts` has an external code consumer | **MEASURED FALSE.** One comment hit, no code hit |
| a clause name differs between the class instance and the committed module | **MEASURED FALSE** at all 12, `ProbeReach.agda` exit 0 |
| a `*BndAt` row field differs | **MEASURED FALSE** at all 12, `ProbeReach.agda` exit 0 |
| `envSetAt` differs, or `EnvSet.back` fails to serve | **MEASURED FALSE.** `ProbeReach.agda` sections C and D |
| `ProbeCompat.agda` tested the row fields the consumers write | **MEASURED FALSE.** It tested the first field; 10 of 12 differ |
| `ProbeCompat.agda` tested `EnvSupply`'s field | **MEASURED FALSE.** It tested `φB` and `φ`; the consumer writes `back` |
| `ProbeCompat.agda` holds 39 checks | **MEASURED FALSE.** 37 declarations |
| the scaffold is 45 hand-written code lines | **MEASURED TRUE**, exactly |
| the non-copied content is 45 plus 19 | **MEASURED FALSE.** 247 non-blank, of which 175 comment |
| the C-42 retirement licenses wave 2 | **MEASURED FALSE.** Scoped「for the port itself」, section 4 |
| seven dirty modules cost 7 times 51 | **MEASURED FALSE.** `[LJ-1.302]:191` and `:205-209` price the seven at about 100 |
| the 180 fails on `[LJ-1.298]`'s caliber | **MEASURED FALSE** for wave 1; **INFERRED** for the residual |
| the 180 holds on the project's caliber with landing comments | **INFERRED FALSE.** About -23 lines, on a survey residual |
| `L.Condensation` is in a trophy closure | **MEASURED FALSE.** AC 73 and GCH 51, neither contains it |
| the eleven unchecked `*Agree` modules fail to serve | **MEASURED FALSE** by conversion: `φB` is the row field, and both sides are measured identical |
| the dirty seven typecheck against the landed chapter | **INFERRED.** Wave 2, untouched here |
| the clean 23's ambient ties cost the dirty seven's rate | **INFERRED.** No site measured, P-l binds |
| a probe under `src/` was written | **MEASURED FALSE.** All my files sit in `agents/tasks/LJ-1-308/` |
| `agents/tasks/LJ-1-306/` was edited | **MEASURED FALSE.** `git status` shows my directory only |

## 8. ARCHIVE USED (DD18)

One line read per archived file.

- `agents/tasks/LJ-1-306/lj-1.306-report.md`, read WHOLE, FIRST, as SCOPE
  orders. **Line read:** `:167`,「YES, MEASURED, 39 checks green,
  `ProbeCompat.agda` exit 0, 7.9 s」. TOOK the serving claim as the
  review's first target; CORRECTED the count to 37 and the coverage at
  section 1.2.
- `agents/tasks/LJ-1-298/lj-1.298-report.md`, read `:104-215` and
  `:290-310`. **Line read:** `:140-142`,「about **180 lines of new
  hand-written code**: 38 of scaffolding, about 145 of formula
  re-statements and gap syntax」. TOOK the 180's decomposition, which is
  what settles attack 5.
- `agents/tasks/LJ-1-302/lj-1.302-report.md`, read by targeted grep over
  the tie and price passages. **Line read:** `:191`,「**The ties are ONE
  debt, not sixteen.**」TOOK the refutation of the brief's 7-times-51
  arithmetic.
- `agents/tasks/LJ-1-307/lj-1.307-report.md`, read `:1-45` and
  `:355-370`. **Line read:** `:358`,「**How many agreement lemmas does
  Devlin state? None.**」READ AS EVIDENCE, not as agreement: it answered
  a DD13 question and never checked the port, so it carries no weight for
  or against the zero.
- `agents/tasks/LJ-1-210/ProbeLJ1210Inst.agda`, read `:82-130`. **Line
  read:** `:86-91`, the comment「The ONE name of the nine whose PROOF TERM
  does not match on the nose … the two proofs inhabit the same type, so
  either serves any consumer」. TOOK the finding that `[LJ-1.306]`'s
  「one genuine finding」was already measured at `[LJ-1.210]`, with the
  same cause and the same dismissal. **It is a re-observation, not a new
  finding.**
- `archive/dev/TASKS-archived.md`, read `:68`. **Line read:** the
  `L3.32-T33` row,「Condensation crossing | DELIVERED」. TOOK SHAPE only:
  a crossing was delivered under the retired route, and no figure and no
  content transfers to this port.

## 9. LITERATURE USED (DD18)

`dev/literature/devlin-II5.md`, read `:40-90` and `:312-365`.

**The one line the brief asks for: `[LJ-1.307]`'s reading HOLDS for II.5,
and it is narrower than it sounds.** The digest's engine list at `:312`
to `:365` names twelve items II.5 leans on, and **not one is an agreement
between two codings**. MEASURED, by reading all twelve.

**But the agreement is not absent from the mathematics. It is paid ONCE,
in Chapter I.** Item 3 at `:325-327` is「The ℒ-analogue translation 1.9.11:
each LST formula has an ℒ-formula with the same meaning over transitive
sets」, and item 2 at `:321-324` is Σ₀ absoluteness 1.9.15,「the bridge
between satisfaction inside a transitive carrier and ambient truth」.
**Devlin pays the two-language bridge once at the syntax level, not once
per connective.**

**So the deepest question is the one the brief points at.** Bedrock's
thirty modules exist because the bridge is proved per NOTION rather than
once per LANGUAGE. `[LJ-1.306]` prices the port of that choice. It does
not price the choice. **That is outside this review's scope and I do not
claim it is wrong**, only that the port's zero says nothing about it.
C-45 is the rule: `exit 0` proves the port typechecks, never that the
shape was right.

**WHY NOT the rest of the digest.** Sections 2 and 4 partition the steps
by tower and by Def-against-J. That axis is Devlin's, not DD4's, and
C-46 at `dev/LESSONS.md:4010` says so. Using it here would repeat the
defect `[LJ-1.272]` measured in 12 of 62 figures. Section 7's errata
territory does not reach II.5.

## 10. SECONDS, LOAD, RUNS

One agda process at a time, always `GHCRTS="-A64m -I0 -M8g"`, cap NEVER
raised. No heap exhaustion. No run near 30 minutes. **I checked the slot
before I started: `ps` showed zero agda processes at 21:19, so the
sibling `[LJ-1.305]` had released its own.** I held one slot.

| file | exit | seconds | load at start / end | note |
|---|---:|---:|---|---|
| `agents/tasks/LJ-1-308/ProbeReach.agda` | **0** | **9** | 4.36 / 4.31, 3 users | 26 checks, all green |

Python runs cost under 2 s each and take no Agda slot:
`verify_zero.py`, `closure_check.py`, and `scripts/measure/ledger.py
--reuse`.

## 11. PROHIBITIONS, ANSWERED

I wrote only inside `agents/tasks/LJ-1-308/`: this report,
`ProbeReach.agda`, `verify_zero.py`, `closure_check.py` and
`uncovered.txt`. `src/` holds no probe of mine.
`src/L/Condensation.lagda.md` was read only.
`agents/tasks/LJ-1-306/` was read only, never edited. I did not open
`src/Everything.lagda.md`, `dev/PLAN.md`, `dev/LESSONS.md`,
`dev/ledger.toml` or `AGENTS.md` for writing. No commit, no push, no
`git checkout`, `stash`, `reset` or `clean`. No `make check`.
`.venv/bin/python scripts/gate/lint-prose.py --check` passes on my
files. No em dash in any language. `_build/` holds only Agda's own
interface files for my module.
