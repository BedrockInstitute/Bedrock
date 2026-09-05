# LJ-1.657 report: levelIn from the level formula

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.657
obligation: agents/tasks/LJ-1-657/Probe657.agda::levelin-from-level-formula
verdict: **STOP ON THE OBLIGATION, AND THE STOP IS
`review-of-levelin-from-level-formula.md`. Premise 4 is REFUTED as stated,
the alphabet gap is real AND curable, and curing it does not open the road,
because a SECOND gap sits behind it and that second gap is step 4.**

The obligation reads `missing` (`runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`: the probe is green and the name is
absent, not broken). Twenty-two other names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 22`).

**READ THESE FIVE SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **THE LEVEL FORMULA BUYS THE COLLAPSE'S BELIEF AND NEVER ITS
   SOUNDNESS.** `HoodComplete` costs `ElemDown` alone
   (`hoodComplete-from-level`, `Probe657.agda:198-200`) and `HoodExists`
   costs `ElemDown` and `PiReflectsOrd` (`hoodExists-from-level`,
   `Probe657.agda:146-149`). Neither term mentions step 4.
2. **SO `levelIn` NOW OWES `HoodSound` ALONE**
   (`levelin-owes-soundness-alone`, `Probe657.agda:388-390`), and so does
   step 4 (`step4-owes-soundness-alone`, `Probe657.agda:379-381`). That is
   the one thing this task moves, and it moves it with no step 4 in either
   term.
3. **AND `HoodSound` IS STEP 4 UNDER A SECOND NAME.** `hoodsound-is-step4`
   (`Probe657.agda:344-347`) is green in BOTH directions. So the level
   formula cannot shed step 4 on this road: it is the same fact.
4. **THE PRICED ROUTE IS DOMINATED BY A TERM THAT IS ALREADY GREEN.**
   `[LJ-1.649]`'s own `levelin-from-647-ord-commute` inhabits the same
   conclusion from a SUBSET of the hypotheses, with no formula and no
   elementarity (`lj649-route`, `Probe657.agda:365-366`;
   `levelin-priced-is-dominated`, `Probe657.agda:368-371`).
5. **THE ALPHABET GAP IS A DEFECT OF `LevelFormula`, NOT OF `[LJ-1.653]`,
   AND THE LITERATURE SAYS WHICH SIDE IS RIGHT.**
   `dev/literature/level-formula-slot-roles.md:31` quotes Schindler-Zeman
   1.10(2) for a formula that "does not depend on `α`". Stated
   parameter-free, the PINNED pair becomes reachable for the existential
   half and stays unreachable for soundness (`Probe657.agda:412-482`, all
   green).

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-657/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a time. I
did not set `GHCRTS`. Nothing is postulated, every delivered file carries
`--safe`, the delivered probe carries no hole, and nothing lands in `src/`.
The probe is a raw `.agda` file, so it carries no ` ```agda ` fence, counts
0 in-fence lines, and the ratio bar cannot fire on it.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task, 716 at the
end). No number here is a cold-cache number, and this report does not bound
one.

## 1. THE FLOOR, AND THE IMPORT ROUTE IS ALIVE HERE

Coder clause, owner 2026-08-23: price the frame before the term. The honest
way to take a predecessor's type is to IMPORT it, and `[LJ-1.650]` measured
that route DEAD for `[LJ-1.595]` (`agents/tasks/LJ-1-650/Probe650.agda:6-14`:
2 GB exhausted on the frame alone). **The same route is ALIVE for
`[LJ-1.650]`, `[LJ-1.653]` and `[LJ-1.649]`, which import only `src/`.**

`runs/Floor657.agda` imports all three and states nothing else.

| run | frame | wall s | peak RSS bytes | exit |
|---|---|---|---|---|
| `runs/floor-0.out` | 650 and 653, both predecessors COLD | 5.57 | 964,280,320 | 0 |
| `runs/floor-1.out` | 650, 653 and 649, warm | 3.57 | 654,409,728 | 0 |
| `runs/floor-final.out` | the same, interface deleted first | 3.11 | 654,393,344 | 0 |

`runs/floor-0.out:4-6` shows the two predecessors checked inside that run, so
both `[LJ-1.650]` and `[LJ-1.653]` are green in THIS worktree and not only in
their own.

**The obligation adds about 3.8 s to a 3.1 s floor** (median final 6.89 s,
section 9). No heap event at any point, and no restructuring was needed.
I trimmed the imports to the names the rows actually use.

## 2. WHAT THE BRIEF ASKED, AND WHY IT CANNOT BE TYPED

The brief orders `HoodExistsP` and `HoodSoundP` "at the formula
`LevelFormula` carries". That formula is `fst lf : Formula Code 2`
(`agents/tasks/LJ-1-650/Probe650.agda:324`). The two pinned predicates take
`Formula (⊥* {ℓ-suc ℓ}) 2` (`agents/tasks/LJ-1-653/Probe653.agda:283`,
`:235`).

`Code : Type ℓ` (`src/L/Hull.lagda.md:72`), so the two formula types are not
even in the same universe. **Agda names it, twice, and I did not argue it**:
`runs/nopinned-1.out` (exit 42 in 3.78 s) and `runs/noalpha-1.out` (exit 42
in 3.13 s), both `[UnequalLevel] ℓ-zero != ℓ-suc ℓ`. The two sources are
`runs/NoPinned.agda.txt` and `runs/NoAlphabet.agda.txt`, RED BY CONSTRUCTION
and kept as `.agda.txt` so conjunct 1 does not run them.

**And the relabelling that would cross the alphabet is refutable with no
hypothesis at all**: `no-relabelling-out-of-Code` (`Probe657.agda:83-84`).
`Code` is inhabited by the constructor `wit` alone
(`code-inhabited`, `Probe657.agda:81`; `src/L/Hull.lagda.md:72-74`), so the
crossing dies at EVERY instance and not at a hard one.

The full stop is `review-of-levelin-from-level-formula.md`.

## 3. THE READING THAT CAN BE WRITTEN, AND WHAT IT COSTS

`[LJ-1.653]` states the pair UN-pinned as well, at `Formula CIso.I.SM 2`
(`Probe653.agda:263`, `:191`), and the tree already carries `Code → SM`:
`DownReflect.codeValM` (`src/L/BoundedSubset.lagda.md:377-378`). So the
crossing that DOES exist is ONE line, `levelFo` (`Probe657.agda:96-97`).

**Two crossings stand between the two sides, and only the second one costs.**

| crossing | what carries it | price |
|---|---|---|
| alphabet, `Code` to `SM` | `codeValM`, delivered | ONE line |
| carrier, STAGE to HULL | `ElemDown`, the tree's own residue (`src/L/BoundedSubset.lagda.md:410-412`) | already on the books |
| carrier, HULL to COLLAPSE | `CIso.I.iso-inv` / `iso-inv-bwd`, delivered | free |
| ordinality, COLLAPSE back to HULL | `PiReflectsOrd` (`agents/tasks/LJ-1-649/Probe649.agda:222-223`) | unbuilt |
| ambient soundness at the COLLAPSE | step 4 | THE STOP |

`ElemDown` is not new debt: `AtHullInstance.reflect`
(`src/L/BoundedSubset.lagda.md:782`) already takes it, and
`HullElemDown.elem` (`src/L/BoundedSubset.lagda.md:759`) discharges it from a
code selection. My restatement of the full `Elementary` is certified against
the tree's own type by `elem-restates-the-tree` (`Probe657.agda:247-248`),
whose body is `λ e → e`, and `elem-down` (`Probe657.agda:250-251`) shows
`ElemDown` is its one half.

## 4. THE THREE FACTS THE LEVEL FORMULA PAYS

| fact | term | hypotheses spent |
|---|---|---|
| `HoodComplete` | `hoodComplete-from-level`, `Probe657.agda:198-200` | `ElemDown` |
| `HoodExists` | `hoodExists-from-level`, `Probe657.agda:146-149` | `ElemDown`, `PiReflectsOrd` |
| `HoodExistsP` (pinned) | `hoodExistsP-from-levelP`, `Probe657.agda:435-437` | `ElemDown`, `PiReflectsOrd`, a parameter-free `LevelFormula` |

**None of the three mentions step 4.** `hoodComplete-from-level` does not
even spend `PiReflectsOrd`, because the consumer hands `IsOrd y` on the hull
side already.

The consequence is the one thing this task moves:

- `levelin-owes-soundness-alone` (`Probe657.agda:388-390`): the consumer's
  own goal, `LevelIn`, from the level formula, `ElemDown`, `PiReflectsOrd`
  and `HoodSound`. No step 2 in that chain and no step 4.
- `step4-owes-soundness-alone` (`Probe657.agda:379-381`): step 4 itself, from
  the level formula, `ElemDown`, `[LJ-1.647]`'s step 2 and `HoodSound`.

**`[LJ-1.653]` left the pair owing two facts. It now owes one.**

## 5. THE FACT IT DOES NOT PAY, AND WHY IT CANNOT

`HoodSound` (`Probe653.agda:191-195`) is an AMBIENT claim: the value the
collapse believes is the level really IS the level. `LevelFormula`'s
soundness is an ambient claim at the STAGE. Carrying one to the other means
carrying `π` past `Lset`.

`hoodSound-from-level` (`Probe657.agda:253-256`) is green and spends
`PiCommuteLsetOrd` at exactly ONE line, `Probe657.agda:274`. Nothing else in
the file spends it.

**AND THE PRICE IS THE SAME FACT, NOT A SIDE CONDITION.**
`hoodsound-is-step4` (`Probe657.agda:344-351`) is green in both directions:
step 4 gives `HoodSound`, and `HoodSound` gives step 4 through
`[LJ-1.653]`'s own `step4-at-ord` (`Probe653.agda:200-203`), whose
completeness half section 4 supplies for free.

**SO THE PRICED ROUTE IS DOMINATED.** `[LJ-1.649]`'s
`levelin-from-647-ord-commute` (`Probe649.agda:241-245`, GO by
`agents/tasks/LJ-1-649/lj-1.649-report.md:147`) reaches `LevelIn` from
`PiReflectsOrd`, step 2 and step 4, with no level formula and no
elementarity. Its own term inhabits my restatement with no adapter
(`lj649-route`, `Probe657.agda:365-366`), and `levelin-priced-is-dominated`
(`Probe657.agda:368-371`) is the domination written out: the body ignores
both `lf` and `Elem`.

## 6. THE ALPHABET GAP IS CURABLE, AND THE CURE IS THE LITERATURE'S OWN SHAPE

`dev/literature/level-formula-slot-roles.md:37` records that rows 3, 4, 5, 6,
8 and 9 all leave exactly the value and the ordinal free, and row 9 (`:31`)
quotes Schindler-Zeman 1.10(2) for a formula that "does not depend on `α`".
**So the sources' level-hood formula is PARAMETER-FREE, and
`Lv.LevelFormula` typed at `Formula Code 2`
(`agents/tasks/LJ-1-650/Probe650.agda:322-324`) is weaker than the object
they describe.**

Part 8 of the probe measures the repair.

- `LevelFormulaP` (`Probe657.agda:412-419`) is the same statement over
  `Formula (⊥* {ℓ-suc ℓ}) 2`.
- `levelP→level` (`Probe657.agda:423-424`) lands in `[LJ-1.650]`'s own type
  with NO adapter, so it is a strengthening and nothing else.
- `hoodExistsP-from-levelP` (`Probe657.agda:435-437`) is GREEN: the pinned
  existential half costs `ElemDown` and `PiReflectsOrd` only.
- `hoodSoundP-from-levelP` (`Probe657.agda:458-460`) is GREEN and spends step
  4, UNCHANGED.

**The alphabet repair moves the existential half and leaves the soundness
half exactly where it was**, because the second gap is about the two CARRIERS
and not about the alphabet. No restatement of the formula can move it.

## 7. W3, THE WIDEST UNMEASURED TERM

The brief named it: "The alphabet embedding of premise 4", estimated at 80 to
170 lines.

**MEASURED: the decisive miniature is TWO lines, and it is a REFUTATION and
not an embedding.** `runs/W3.agda` carries `code-inhabited` and
`no-relabelling-out-of-Code` and nothing else; it typechecked ALONE at
`runs/w3-1.out` (exit 0 in 3.18 s) and again at `runs/w3-final.out` (exit 0
in 2.43 s, interface deleted first).

**The estimate was high by about two orders of magnitude AT THE ALPHABET,
because the alphabet was never where the cost was.** The crossing that exists
is `mapFo codeValM`, one line, and the delivered probe's 262 non-blank
non-comment lines are almost all CARRIER work: the stage-to-hull elementarity
plumbing and the hull-to-collapse iso, sections 4 to 6.

## 8. W2, THE GENERIC CARRIER

Answered, and the clause is met.

The whole probe sits in ONE telescope, `module Bridge`
(`Probe657.agda:45-49`), which is the same cut `Probe653.agda:74-77`,
`Probe650.agda:59-63` and `Probe462.agda:78-90` took. Nothing is written
twice for a fixed `lam` or a fixed `X`, and no fact of any predecessor is
restated: all three enter by IMPORT (`Probe657.agda:34-40`), so `Code`,
`SM`, `SL`, `M` and `C.π` are one object each and not five.

Every delivered term is generic in the FORMULA as well: `hoodExists-from-level`,
`hoodComplete-from-level` and `hoodSound-from-level` take `lf` and never a
fixed `lv`, so they hold at whatever level-hood formula `[LJ-1.656]` finally
delivers.

I did not meet a conflict between W2 and a deadline.

## 9. RUNS

Caliber `-A64m -I0 -M2g`, the wide caliber, set on the pane by the program
and untouched here. One Agda process at a time. All runs from the repository
root. The mechanism is `runs/run.sh`, copied verbatim from
`agents/tasks/LJ-1-650/runs/run.sh`.

Three forced rechecks of the delivered file, the probe interface deleted
before each:

| run | wall s | peak RSS bytes | exit |
|---|---|---|---|
| `runs/final-1.out` | 6.89 | 1,042,055,168 | 0 |
| `runs/final-2.out` | 7.45 | 774,242,304 | 0 |
| `runs/final-3.out` | 6.86 | 1,051,082,752 | 0 |

A fourth run after the last edit to the report's own line citations, with
every interface under this task home deleted first: `runs/final-confirm.out`,
6.31 s, 1,051,066,368 bytes, exit 0. The two companions were rechecked in the
same pass: `runs/w3-final.out` (2.43 s) and `runs/floor-final.out` (3.11 s),
both exit 0.

Median wall **6.89 s**. Median peak RSS **1,042,055,168 bytes**. Each printed
`Checking`. **No heap event at any point in this task, and no restructuring
was needed.**

The build order, kept:

| run | wall s | exit | what it added, or what it caught |
|---|---|---|---|
| `runs/p-0.out` | 3.45 | 42 | `[NotInScope] Lv.Code`. A SCOPE slip and not a mathematical one: `[LJ-1.650]`'s `Coded` opens the term algebra WITHOUT `public`, so `Code` is not re-exported. The fix names the tree's own copy, `module T = DR.H.T` |
| `runs/p-1.out` | 4.16 | 0 | parts 1 and 2: the alphabet refutation and `levelFo` |
| `runs/p-2.out` | 5.76 | 0 | parts 3 and 4: the hypotheses and the existential half |
| `runs/p-3.out` | 3.38 | 42 | `[NotInScope] Σ≡Prop`, a missing import and nothing else |
| `runs/p-4.out` | 7.10 | 0 | parts 5 and 6: completeness and soundness |
| `runs/p-5.out` | 6.18 | 0 | part 7: the obligation's type and the priced terms |
| `runs/p-6.out` | 7.04 | 0 | the `[LJ-1.649]` import, so the domination is a term |
| `runs/p-7.out` | 6.09 | 0 | 7.6 and 7.7, the two "owes soundness alone" terms |
| `runs/p-8.out` | 6.76 | 0 | part 8, the parameter-free repair |

Meters: `runs/meter-obligation.out` (`missing`, `1 UNRESOLVED of 1`,
`probe_red=False`, 3.11 s) and `runs/meter-names.out`
(`0 UNRESOLVED of 22`, 4.65 s). This worktree has no `.venv`; the meter ran
as `/Users/alsg/Agentic/Bedrock/.venv/bin/python scripts/pod/witness.py`. I
did not add a dependency and I did not create a local `.venv`.

## 10. WHAT THE NEXT BRIEF NEEDS

1. **DO NOT FUND `levelIn` FROM THE LEVEL FORMULA.** Section 5 is the
   measurement: whatever that route delivers, `[LJ-1.649]`'s green term
   delivers from fewer hypotheses.
2. **FUND `HoodSound` AND NOTHING ELSE.** It is now the single open fact
   under `levelIn`, under step 4 and under the pinned pair alike (sections 4,
   5 and 6). `[LJ-1.653]`'s section 5 already forked it into (a)
   `C.πX ⊆ L` and (b) an ambient `Lset-only`, and called (a) almost certainly
   the cheap one. Nothing here prices either, and this task adds no third
   fork.
3. **`[LJ-1.656]` SHOULD DELIVER ITS FORMULA PARAMETER-FREE.** Section 6 is
   the reason and `dev/literature/level-formula-slot-roles.md:31` is the
   authority. The strengthening lands in `[LJ-1.650]`'s own type with no
   adapter (`Probe657.agda:423-424`), so it costs the producer nothing to
   state, and it is the difference between the pinned pair being reachable
   and not.
4. **`PiReflectsOrd` IS NOW SPENT ON A SECOND ROUTE.** `[LJ-1.649]` named it
   the price of the ordinal keystone. It is also the price of the existential
   half here (`Probe657.agda:146-149`). It is still unbuilt, and it is now
   worth more than one route's worth.
5. **`ElemDown` IS ON THE BOOKS AND IS NOT A NEW STOP.** Every term here that
   crosses from the stage to the hull spends it, and
   `src/L/BoundedSubset.lagda.md:759` discharges it from a code selection.
6. This task changed nothing in `src/`.

## 11. GATES

Run individually while the work was live, as the Boundary requires:

- `scripts/gate/lint-agda.py --check`: clean, no output, exit 0.
- `scripts/gate/check-probes.py --check`: `check-probes: clean (10031
  tracked files, no probe outside agents/tasks/ and no generated file)`.
- `scripts/gate/lint-prose.py --check`: clean, no output, exit 0.

I did not run `make check`. I did not commit and I did not push. The working
tree carries exactly one untracked path, `agents/tasks/LJ-1-657/`.

## ARCHIVE USED

- **`archive/dev/DECISIONS-archived.md` READ.**
  `archive/dev/DECISIONS-archived.md:51` carries D31, and inside it: "The
  rud side delivers per-step content at a STAGE carrier while the crossing
  needs a two-slot value-and-index formula at the CLASS carrier". **That is
  the same STAGE-against-outer-carrier gap this task measured**, one route
  over, and it is why section 5's obstruction is structural and not an
  accident of `[LJ-1.650]`'s statement.
- **`archive/dev/LJ-dispatch-index.md` READ.**
  `archive/dev/LJ-dispatch-index.md:198`: "| LJ-1.121 | Supply levelIn and
  cover at the site | NEITHER REFUTABLE, NEITHER SUPPLIED | The wall is the
  LJ-1.12 crossing, the level-hood certificate, priced 2.8k to 3.3k lines and
  not built |". It confirms `levelIn` has never been supplied and that the
  level-hood certificate is the standing wall, which is what section 4
  narrows to one fact.
- **`archive/dev/JOURNAL-archived.md` READ.**
  `archive/dev/JOURNAL-archived.md:634`: "134-reading cone monomorphic in
  𝒮ʟ; the formula is not even parameter-free". **The parameter-freeness of a
  level formula has been a live defect before**, which is section 6's point
  restated from an older stop.
- **`dev/ARCHIVE.md` READ.** `dev/ARCHIVE.md:285` carries the
  `L.Condensation` Crossing row: "The Crossing section stated the
  ambient-reading form of `Lset-only` at the class carrier." That is fork (b)
  of `HoodSound`'s remaining leg, and section 10 item 2 points at it without
  pricing it.
- **`archive/dev/JOURNAL.md` READ, ONE LINE.** `archive/dev/JOURNAL.md:410`:
  "level-hood must run through codes and satisfaction, and those leaves are".
  It is the earlier record that the certificate runs through CODES, which is
  the alphabet section 2 refutes at the pinned slot. Nothing else in that file
  bears on this task: it has no other hit for "level-hood", "parameter-free"
  or "levelIn".

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ, AND IT DECIDED
  SECTION 6.** `dev/literature/level-formula-slot-roles.md:37`: "Rows 3, 4,
  5, 6, 8 and 9 agree. **A level-hood formula leaves exactly the two", and
  `:31` carries row 9, Schindler-Zeman 1.10(2), "`x = S_γ^A` is Σ₁ over
  `J_α^A` as witnessed by a formula which does not depend on `α`". Together
  they say the sources' level formula is PARAMETER-FREE, so the pinned slot
  of `[LJ-1.653]` is the faithful one and `[LJ-1.650]`'s `Formula Code 2` is
  the loose one.
- **`dev/literature/devlin-II5.md` READ.**
  `dev/literature/devlin-II5.md:104`: "downward) and along the collapse to M;
  1.9.15 converts M's satisfaction of", and `:224`: "3. Σ₀ absoluteness for
  the matrix: 1.9.15 moves L_α's (or M's) satisfaction". **The source makes
  `HoodSound` a Σ₀-absoluteness step at a TRANSITIVE carrier and not a
  consequence of the stage formula**, which is exactly section 5's
  measurement, and it confirms the route without confirming any price.
- **`dev/literature/digest.md` DECLINED.** Not read beyond its head. It is
  the orthodox form of the RUD route (`digest.md:1`); no step of this task is
  on that route.
- **`dev/literature/truncation-and-selection.md` DECLINED.** Not used. This
  task takes no truncated choice and selects no witness: every truncated
  existence here stays under `PT.map` or `PT.rec` into a proposition. The one
  selection in the thread is `[LJ-1.650]`'s `skolemCode`, which this task
  does not touch.
- **`dev/literature/terms-2026-08.md` DECLINED.** Not used. It is a
  terminology dossier for the owner's naming ruling and this task names
  nothing new in Chinese or Japanese.
