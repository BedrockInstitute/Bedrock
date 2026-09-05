# LJ-1.272 report: label every DD4 figure in this phase with its axis

tier: pi (deepseek-subagent-mode), model `deepseek-v4-flash`. No Agda ran. No
slot held. No master, brief or report edited except this one. Written
incrementally (C-22). Every negative is MEASURED or INFERRED, in those words.

## 0. THE COUNT

**Twelve DD4 figures carry no axis in their own words. MEASURED, by reading
each figure's report.**

The twelve are in the port chain, where both axes were live:

| report | figure |
|---|---|
| LJ-1-210 | 19 lines buy the second tower |
| LJ-1-213 | shared 389, plumbing 12, residual 8 |
| LJ-1-219 | shared 389, plumbing 21, residual 8 |
| LJ-1-220 | 9 modules, 22 names |
| LJ-1-223 | shared 2,971, plumbing about 200, residual 0 |
| LJ-1-224 | shared 338, plumbing 53, residual 8 modules 19 names |
| LJ-1-225 | the carried 2,971 / 200 / 0, and the tower-neutral lift |
| LJ-1-246 | assembly paid once, leaf per-tower |
| LJ-1-253 | the band 146 to 196 |
| LJ-1-257 | the move tower-neutral, about 30 lines |
| LJ-1-258 | none of the fifteen is per-tower |
| LJ-1-260 | the three records stay tower-neutral |

The claim table's seven are not the corpus. Six of the seven name their axis
in their own words. One of the seven, LJ-1-258, does not. The sweep found
eleven more.

The abort criterion's second branch does not fire. Twelve is not an isolated
defect. It is a pattern inside the port chain, and every one of the twelve
changes meaning once labelled (section 2).

Most reports do name their axis. In the port chain, 50 figure-bearing
reports name it, and 12 do not. I say that plainly. The phase's accounting
is in better shape than the premise "no figure says which" suggests, and it
is still not usable until the twelve carry their axis.

## 1. THE TABLE

One row per DD4 figure. The axis cell says what the figure is on. The
`states` cell says whether the report names the axis in its own words.
The deciding line is the file:line that fixes the axis.

### 1.1 The port chain, 200 to 269

| report | figure | axis | decides | states |
|---|---|---|---|---|
| 200 | class surface 17 lines; carried "six extra lines buy the second tower" | L-VS-AMBIENT for its own figure | LJ-1.200-report.md:193-201 | YES |
| 201 | the series re-instantiates for the J side | DEF-VS-J | LJ-1.201-report.md:471-489 | YES |
| 209 | the J-tower re-instantiation figure is ZERO | DEF-VS-J | lj-1.209-report.md:327-348 | YES |
| 210 | 19 lines buy the second tower | UNLABELLED | lj-1.210-report.md:358-377 | NO |
| 213 | shared 389, plumbing 12, residual 8 | UNLABELLED | lj-1.213-report.md:110-123 | NO |
| 214 | zero extra lines for the J tower | DEF-VS-J | lj-1.214-report.md:154-176 | YES |
| 216 | three numbers at the ambient class | L-VS-AMBIENT | lj-1.216-report.md:107-118 | YES |
| 217 | 85 percent generic | DEF-VS-J | lj-1.217-report.md:181-206 | YES |
| 219 | shared 389, plumbing 21, residual 8 | UNLABELLED | lj-1.219-report.md:121-134 | NO |
| 220 | 9 modules, 22 names | UNLABELLED | lj-1.220-report.md:174-175 | NO |
| 221 | the thin-thick supplier split; the Hull module | BOTH, both named | lj-1.221-report.md:411-416 | YES |
| 222 | 23 template lines, 500 per-tower | DEF-VS-J | lj-1.222-report.md:423-455 | YES |
| 223 | shared 2,971, plumbing about 200, residual 0 | UNLABELLED | lj-1.223-report.md:102-116 | NO |
| 224 | shared 338, plumbing 53, residual 8 modules 19 names | UNLABELLED | lj-1.224-report.md:337-362 | NO |
| 225 | carried 2,971 / 200 / 0; the tower-neutral lift | UNLABELLED | lj-1.225-report.md:91-99, :106 | NO |
| 226 | pairω is tower-neutral | DEF-VS-J | lj-1.226-report.md:148-161 | YES |
| 227 | A2 and A7 neutral; A1, A3, A4 per-tower | DEF-VS-J | lj-1.227-report.md:235-251 | YES |
| 228 | sl and sc are one object | DEF-VS-J | lj-1.228-report.md:162-186 | YES |
| 229 | range set and ranAt tower-neutral; A2 is 186 | DEF-VS-J | lj-1.229-report.md:128-143 | YES |
| 230 | the structure parameter the J tower needs | DEF-VS-J | lj-1.230-report.md:97-112 | YES |
| 231 | pairω tower-neutral | DEF-VS-J | lj-1.231-report.md:451-475 | YES |
| 232 | A1 and A3 per-tower | DEF-VS-J | lj-1.232-report.md:157-161 | YES |
| 233 | C1 and C2 per-tower; the 147-line joining layer is tower-free | DEF-VS-J | lj-1.233-report.md:329-345 | YES |
| 234 | the content is tower-neutral | DEF-VS-J | lj-1.234-report.md:151-164 | YES |
| 235 | shape neutral, instantiation per-tower | DEF-VS-J | lj-1.235-report.md:112-124 | YES |
| 236 | A7 neutral, A4 per-tower | DEF-VS-J | lj-1.236-report.md:196-214 | YES |
| 237 | structure-parameter cost is zero | DEF-VS-J | lj-1.237-report.md:110-117 | YES |
| 238 | residual 0 | L-VS-AMBIENT | lj-1.238-report.md:140-146 | YES |
| 239 | steps 2 and 4 neutral; the closure is PER-TOWER | DEF-VS-J | lj-1.239-report.md:99-108 | YES |
| 240 | lh per-tower; the numeral tags Def-tower | DEF-VS-J | lj-1.240-report.md:408-427 | YES |
| 241 | φ₀ is Def-tower | DEF-VS-J | lj-1.241-report.md:92-108 | YES |
| 242 | the closure is per-tower | DEF-VS-J | lj-1.242-report.md:187-202 | YES |
| 243 | the bridge is Def-tower | DEF-VS-J | lj-1.243-report.md:620-644 | YES |
| 244 | q' is per-tower | DEF-VS-J | lj-1.244-report.md:149-179 | YES |
| 245 | q is the Def-tower crossing | DEF-VS-J | lj-1.245-report.md:245-258 | YES |
| 246 | assembly paid once, leaf per-tower | UNLABELLED | lj-1.246-report.md:314-339 | NO |
| 247 | the dissolution is tower-neutral | DEF-VS-J | lj-1.247-report.md:132-142 | YES |
| 248 | the per-tower half is 146; the band is 146 to 196 | DEF-VS-J | lj-1.248-report.md:151-167 | YES |
| 249 | the assembly is carrier-generic | BOTH | lj-1.249-report.md:70-97 | YES |
| 250 | the two lemmas are not per-tower; the leaf is 135 | DEF-VS-J | lj-1.250-report.md:140-158 | YES |
| 251 | the per-tower fraction is about 28 lines | DEF-VS-J | lj-1.251-report.md:346-370 | YES |
| 252 | tower-neutral, paid once | DEF-VS-J | lj-1.252-report.md:107-112 | YES |
| 253 | the band 146 to 196, unchanged | UNLABELLED | lj-1.253-report.md:111-124 | NO |
| 254 | the 3 per-tower fields; zero extra lines | DEF-VS-J | lj-1.254-report.md:79-98 | YES |
| 255 | the eleven fields | DEF-VS-J | lj-1.255-report.md:135-152 | YES |
| 256 | the J tower's re-payment is about 25 lines | DEF-VS-J | lj-1.256-report.md:302-321 | YES |
| 257 | the move tower-neutral, about 30 lines | UNLABELLED | lj-1.257-report.md:151-171 | NO |
| 258 | none of the fifteen is per-tower | UNLABELLED | lj-1.258-report.md:154-161 | NO |
| 259 | the closure tower-neutral, not (K, Ktr)-neutral | BOTH | lj-1.259-report.md:141-151 | YES |
| 260 | the three records stay tower-neutral | UNLABELLED | lj-1.260-report.md:104-113 | NO |
| 261 | the merge stayed tower-neutral | DEF-VS-J | lj-1.261-report.md:98-115 | YES |
| 263 | the axis is named | BOTH | lj-1.263-report.md:78-82 | YES |
| 264 | the axis is named | BOTH | lj-1.264-report.md:129-144 | YES |
| 265 | DD24's bar axis | BOTH | lj-1.265-report.md:153-160 | YES |
| 267 | seven parameters, each with an axis | BOTH | lj-1.267-report.md:169-193 | YES |
| 268 | per-block landing order, with an axis | DEF-VS-J, both named | lj-1.268-report.md:207-232 | YES |
| 269 | the slot layout, tower-neutral by construction | BOTH, both named | lj-1.269-report.md:209-218 | YES |
| 196 | the NO-GO re-instantiates for the J tower | DEF-VS-J | lj-1.196-report.md:140-150 | YES |
| 198 | the formula and reading re-instantiate for the J tower | DEF-VS-J | lj-1.198-report.md:157-170 | YES |
| 199 | the statement layer re-instantiates; the coding cone per-tower | DEF-VS-J | lj-1.199-report.md:140-151 | YES |
| 202 | the derivation names no tower | DEF-VS-J | lj-1.202-report.md:65-70 | YES |
| 215 | isNumeral is the generic shape | DEF-VS-J | lj-1.215-report.md:699-725 | YES |

### 1.2 The earlier chain, 90 to 199

These reports name the J tower or both axes in their own words, except the
four frame counts below. MEASURED, by reading each DD4 section.

| report | axis | states |
|---|---|---|
| 90, 91, 92, 93, 95, 96, 97, 101, 103, 105, 111, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 144, 146, 149, 150, 151, 152, 153, 154, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 176, 177, 178, 185 | DEF-VS-J | YES |
| 94, 106, 107, 159, 175, 184 | BOTH | YES |
| 131, 134, 136, 145, 147, 156 | third axis, the two proofs, named | YES |
| 100, 108, 110, 112 | third axis, the two proofs, unnamed | NO |

The deciding lines are `lj-1.100-report.md:155-159` (count 11),
`lj-1.108-report.md:141-158` (35-line saving), `lj-1.110-report.md:208-216`
(frame counts 43 to 37, 43 to 36, 69 to 59) and `lj-1.112-report.md:184-188`
(count 0). Each is a count of what the two proofs share in a frame. None
names Def-vs-J or L-vs-ambient.

The count in section 0 counts only the port chain. The four earlier frame
counts are a separate finding, reported in section 3.

## 2. FIGURES THAT CHANGE MEANING ONCE LABELLED

Every one of the twelve unlabelled figures changes meaning once labelled.
MEASURED, by testing each on both axes.

1. **LJ-1-210.** "19 lines buy the second tower". The heading says "FOR J"
   (`lj-1.210-report.md:358`). The table row it describes is the `Full`
   instance (`:377`). The heading invites a Def-vs-J reading. That
   reading is false: no J instance was built. The measured instance is the
   ambient class, so the true reading is L-vs-ambient.
2. **LJ-1-213.** "shared class-generic body 389... per-tower residual 8"
   (`lj-1.213-report.md:111-113`). Read on L-vs-ambient, the 389 is the
   carrier-generic body and the 8 is the L-specific residue. Read on
   Def-vs-J, the 389 is what the J tower shares. The J-transfer is
   INFERRED, stated at `:117-119`. The two readings give different claims.
3. **LJ-1-219.** The same three numbers, carried from LJ-1-213
   (`lj-1.219-report.md:121-134`). Same ambiguity.
4. **LJ-1-220.** "9 modules must go generic before the shared body serves
   both towers" (`lj-1.220-report.md:174-175`). "Serves both towers" is
   Def-vs-J vocabulary. The instrument measured the ambient class
   (`:165`). Read on Def-vs-J, it claims a J result that was not measured.
5. **LJ-1-223.** "2,971 shared, about 200 plumbing, 0 per-tower residual"
   (`lj-1.223-report.md:111-116`). The suppliers are "tower-neutral...
   None of them names isL or isJ" (`:104`). The evidence is carrier
   genericity: "speak only of the carrier S... GenModel takes all of those
   as parameters" (`:105-106`). The residual is "INFERRED: no second tower
   was built" (`:116`). This is the figure LJ-1-225 carried into the
   misattribution. Read on Def-vs-J, the zero says the J tower re-instantiates
   the chain with no residue. Per `lj-1.238-report.md:140-146`, that does
   not follow from a zero against `Full`.
6. **LJ-1-224.** "the same 338 lines at the ambient class as at 𝒮ʟ... one
   body serves both towers... per-tower residual 8 modules 19 names"
   (`lj-1.224-report.md:337-362`). "At the ambient class" is L-vs-ambient.
   "Per-tower residual" is Def-vs-J vocabulary. The residual is the port's
   module width, not the J tower's.
7. **LJ-1-225.** The known case. "0 per-tower residual in the chain"
   (`lj-1.225-report.md:94`) is an L-vs-ambient figure, read under a
   Def-vs-J doubt (`:97-99`). The `:106` row applies `devlin-II5.md:375`,
   a Def-vs-J mark, to the L-vs-ambient lift.
8. **LJ-1-246.** "a carrier-generic graph-assembly is the same fact as a
   tower-neutral one" (`lj-1.246-report.md:338-339`). This asserts that the
   two axes coincide. `[LJ-1.262]` section 7 says they do not
   (`lj-1.262-report.md:309-310`). The figure "paid once for both towers"
   (`:332-334`) is INFERRED on Def-vs-J and measured on L-vs-ambient.
9. **LJ-1-253.** "The band stays 146 to 196" (`lj-1.253-report.md:122`).
   Read on L-vs-ambient, it says the ambient residual is 146 to 196 lines.
   That is false. The band is the A-prime per-tower half, the Def-vs-J
   figure LJ-1-248 stated at `lj-1.248-report.md:153`.
10. **LJ-1-257.** "The MOVE is tower-neutral... about 30 lines once, not per
    tower" (`lj-1.257-report.md:158`, `:170-173`). The report also says the
    shells are "NOT yet tower-neutral" (`:161`) and that the general form
    makes them "generic over the carrier slot" (`:167`). The Def-vs-J
    reading overclaims what the report itself measured.
11. **LJ-1-258.** "None of the fifteen is per-tower... All fifteen are
    stated over (K, Ktr) from their first line, so the J tower re-instantiates
    Fact unchanged" (`lj-1.258-report.md:154-161`). This is the LJ-1-225
    shape one dispatch later. The evidence, "(K, Ktr)", is the L-vs-ambient
    axis. The conclusion, "the J tower re-instantiates", is the Def-vs-J
    axis. The carrier evidence does not license the J conclusion.
12. **LJ-1-260.** "The three records stay tower-neutral... all stated over
    (K, Ktr)... the two halves a J tower would re-instantiate"
    (`lj-1.260-report.md:104-113`). Same shape as LJ-1-258.

**One carried mislabel, in LJ-1-240.** The report says `[LJ-1.238]`
"measured L.Coding.Sequence's per-tower residual at ZERO"
(`lj-1.240-report.md:425-427`). LJ-1.238's zero is L-vs-ambient, stated at
`lj-1.238-report.md:140-146`. LJ-1-240 re-labels it "per-tower residual",
Def-vs-J vocabulary. The carried figure changes meaning at the new site.

**No figure is false on both axes. MEASURED.** Each of the twelve is true
or measured on one axis and false or INFERRED on the other. None is false
on both. The "something better" branch of the abort criterion does not fire.

## 3. A THIRD AXIS EXISTS

The abort criterion's third branch fires. Some figures are on neither axis
the phase used.

The two proofs in DD4's own text are the two trophies, `L ⊨ AC` and
`L ⊨ GCH`, both stated in L. `dev/PLAN.md:282` (DD2) names them.
`dev/ORCHESTRATION.md:352` names them in the standing brief clause.
`scripts/ledger.py:404-407` says the reuse report computes "what the two
proofs actually share", and it computes the AC and GCH closures
(`scripts/ledger.py:50`). The archive ruling D39 says "Prove L ⊨ AC and
L ⊨ GCH on that bridge... MAXIMIZE THE CODE THE TWO PROOFS SHARE"
(`archive/dev/DECISIONS-archived.md:58`).

So the third axis is the two-proof axis, AC against GCH. It is DD4's own
words. The phase measured it once, in the ledger split
(`lj-1.131-report.md:509-525`: shared 17,948, GCH alone 8,624, AC alone
225) and in the frame chain (`lj-1.100-report.md:155-159`: count 11;
`lj-1.112-report.md:184-188`: count 0). The four frame counts
(LJ-1-100, 108, 110, 112) carry no axis in their own words.

`[LJ-1.262]` measured two axes and did not claim there are only two. The
sweep adds the third.

## 4. WHICH AXIS DD4'S OWN TEXT NAMES

**DD4's own text names the two trophy proofs, not the two towers and not the
ambient class. MEASURED.**

The DD4 row says "maximize the code the two proofs share"
(`dev/PLAN.md:283`). The record fixes "the two proofs" as the two trophies:
DD2 (`dev/PLAN.md:282`), D39 (`archive/dev/DECISIONS-archived.md:58`), the
ORCHESTRATION clause (`dev/ORCHESTRATION.md:352`), and the ledger reuse
report (`scripts/ledger.py:50`, `:404-407`).

The mechanism the row prescribes is D29's, absorbed into it: "written once
at a generic carrier and instantiated" (`dev/PLAN.md:283`; D29 at
`archive/dev/DECISIONS-archived.md:48`). That mechanism is the port's axis,
L against the ambient class. The row does not name the towers at all.

So DD4 itself means the two-trophy sharing, realized by generic-carrier
writing. It does not mean Def-against-J. That axis is Devlin's, imported
through `dev/literature/devlin-II5.md:375` and `:387-389`.

The consequence the brief asked me to state: the plan should hear that the
phase's DEF-VS-J figures answer Devlin's question, not DD4's own words. The
per-tower half of 146 to 196 lines, and the A1, A3, A4 per-tower marks, are
Devlin's axis. The L-VS-AMBIENT figures, the residual zeros and the carrier
genericity, answer DD4's own mechanism.

The two-tower route makes per-tower content a real DD4 cost, because it is
the boundary of what the two proofs can share across the bridge. That keeps
the Def-vs-J figures relevant. It does not make them DD4's own words.

## 5. DOES THE LABELLED ACCOUNTING SUPPORT THE PLAN

Yes, on the measured axis of each figure. The plan rows that quote the
figures survive once the axis is added.

- `dev/PLAN.md:829` (LJ-1.238): "RESIDUAL 0. The six readings are
  tower-neutral". The report states the axis: L-vs-ambient, measured.
  The row survives on that axis.
- `dev/PLAN.md:837` (LJ-1.249): "DD4 split HELD". LJ-1-249 states the
  L-vs-ambient axis as MEASURED and the L-vs-J axis as INFERRED
  (`lj-1.249-report.md:91-94`). The row survives on the measured axis.
- `dev/PLAN.md:814` (LJ-1.223): "2,971 SHARED... per-tower residual 0".
  The report does not name the axis. The row inherits the defect.
- `dev/PLAN.md:820` and `:862` (LJ-1.227, LJ-1.248): Def-vs-J, stated at
  the source. The rows survive.
- `dev/PLAN.md:816` (LJ-1.225): corrected by `[LJ-1.262]`.

The plan's own rows carry the unlabelled wording, "tower-neutral" and
"per-tower residual 0". The plan should carry the axis in the row, not only
in the report.

One claim the plan makes from the accounting is not supported: the
Def-vs-J reading of an L-vs-ambient zero. `dev/PLAN.md:814`'s "per-tower
residual 0" is that reading, and it is exactly what LJ-1.225 did wrong.

## 6. ARCHIVE USED (DD18)

One line read named per archived file.

- `agents/tasks/LJ-1-262/lj-1.262-report.md`, read WHOLE. **Line read
  `:298`**, "Devlin's axis is Def tower against J tower."
- `agents/tasks/LJ-1-238/lj-1.238-report.md`, read WHOLE. **Line read
  `:140-146`**, the caveat: "the class-generic port measures L against the
  ambient class Full, not against J."
- `agents/tasks/LJ-1-225/lj-1.225-report.md`, read. **Line read `:97-99`**,
  "the C2 row marks the coding per-tower, which bears on the word 'shared'."
- `agents/tasks/LJ-1-248/lj-1.248-report.md`, read. **Line read `:153`**,
  "the part the J tower pays again."
- `agents/tasks/LJ-1-227/lj-1.227-report.md`, read. **Line read `:243`**,
  "On the J tower it is `⟨ isJ x ⟩`."
- `agents/tasks/LJ-1-258/lj-1.258-report.md`, read. **Line read `:160`**,
  "so the J tower re-instantiates `Fact` unchanged."
- `agents/tasks/LJ-1-267/lj-1.267-report.md`, read. **Line read `:169`**,
  "Two axes, per `[LJ-1.262]`."
- `agents/tasks/LJ-1-268/lj-1.268-report.md`, read. **Line read `:207`**,
  "The axis is Def against J."
- `agents/tasks/LJ-1-269/lj-1.269-report.md`, read. **Line read `:215`**,
  "The axis is `[LJ-1.262]`'s."
- `agents/tasks/archive/LJ-1-52/lj-1.52-report.md`, read. **Line read
  `:128`**, "the J tower's analogue reuses the assembly with its own
  bounded graph."
- `agents/tasks/archive/LJ-1-16/lj-1.16-report.md`, read. **Line read
  `:113-115`**, "Shape 3 is per-tower... The L-side order at `Lset α` is
  not the J-side order."
- `agents/tasks/archive/LJ-1-23/lj-1.23-report.md`, read. **Line read
  `:179-188`**, "The J tower supplies five things... The one per-tower
  leaf is the junk membership lemma."
- `archive/dev/TASKS-archived.md`, read. **Line read `:217`**,
  `L3.32-T194`: "RED: the frame re-instantiates at 62, but the family
  equality rests on a FALSE bridge." **SHAPE TAKEN, no figure.**

**The retired route named its axis.** Its reports say "the J tower" and
"the J side is INFERRED" in their own words. The defect is not older than
this phase. The archive had one axis in play and named it.

## 7. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:370-394`, read WHOLE. **Line read `:375`**,
  the C2 row: "PER-TOWER content | Def: satisfaction bound K(u) or its
  coding analogue; J: the sixteen op-graphs, syntax-free."
- `dev/literature/devlin-II5.md:387-389`, read. The verdict: "The per-tower
  content is exactly two objects: the level-hood certificate (Step C) and
  the definable well-order (Steps D, G)."

**Do Devlin's twelve rows admit the L-vs-ambient axis? No. MEASURED.**
Every row is marked EITHER or PER-TOWER against the Def and J towers. The
carrier column names Def syntax and J generation data. No row and no
column names the ambient class, the class parameter M, or genericity in a
carrier. The L-vs-ambient axis is purely the port's. It does not exist in
Devlin's table.

**WHY NOT.** I did not use `dev/literature/devlin-II5.md:301-303`. It is
about the level-hood formula's presentation, not the axis question.

## 8. RULES ANSWERED

- **C-42.** The count is the deliverable. Twelve figures carry no axis in
  their own words, at one site per figure. I priced no cure.
- **C-44.** The brief's seven-row claim is a claim. The sweep found eleven
  figures the claim did not list.
- **C-43.** `UNLABELLABLE` is not used. Every figure admits an axis once
  read. The twelve are unlabelled, not unlabellable.
- **D-10.** The recorded figures were priced for truth by reading, not by
  proof. Section 2 tests each on both axes.
- **P-l.** No figure's value was re-derived. Axis labels came from each
  report's own words.
- **D-26.** D-26 is a Def-vs-J statement. `devlin-II5.md:375` carries it in
  the C2 row. That row cannot measure L against the ambient class.
- **C-22.** This report existed as a skeleton before the sweep began.
- **C-36.** No failed reading became an impossibility claim. Section 3
  names the third axis instead.
- **C-32, C-38, C-39, C-40, C-45, I-5, DD0, DD2, DD5, DD8, DD18, DD24.**
  Read and respected. DD2 and DD18 have sections. The rest had no site in
  this task.
- **DD4.** Section 4 and section 5. The phase's accounting, once labelled,
  supports the plan on the measured axis of each figure, and the plan's
  rows should carry the axis.

## 9. WORKING TREE, AS MY REPORT DESCRIBES IT

One file written: `agents/tasks/LJ-1-272/lj-1.272-report.md`, this file.
No master edited. No brief or report edited. No probe written. No Agda
process ran. No commit, no push, no `git checkout .`, stash, reset or
clean.

`scripts/lint-prose.py --check` runs on this report and exits 0.
