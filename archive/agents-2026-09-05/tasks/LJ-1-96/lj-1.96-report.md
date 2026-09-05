# LJ-1.96: price the ideal form of the three split masters

Status: ABORTED at the pre-fixed criterion (D-1). No commit, no push.
ASD-STE100. This report is `_build/lj-1.96-report.md`.

## 0. THE VERDICT

**RETIRE the three delivered masters.** The ideal form at the
consumer's frame cannot be stated: the consumer's frame (the 29-field
`KFacts` and the six site facts) is short of the satisfier-in-K facts
and the `t0`/`t1` facts the twelve rows need. The repair in place
un-empties three of the 69 hypotheses but does not bridge the
consumer's frame. The deciding negative is MEASURED: the consumer's
telescope has no fact about the `t0`/`t1` slots, no general `entryK`,
and no satisfier-in-K family; the `t0eq` and `entryK` mismatches are
machine-checked (`src/ProbeLJ193C.agda:66-75`); the 39-unsupplied
instantiation failure is machine-checked (`src/ProbeLJ193B.agda`,
exit 42).

## 1. THE IDEAL FORM: NO HOME AT THE CONSUMER'S FRAME

The pinned ideal frame is `KFacts` (`src/L/Condensation.lagda.md:5734-5770`)
plus the six site facts `codesK` `:6492-6496`, `unCodesK` `:6497-6500`,
`closedEntryK` `:6501-6503`, `domEntryK` `:6504-6506`, `domK`
`:6507-6508`, `witK` `:6509-6513`. The twelve-row agreement at that
frame needs content that the frame does not state. Item by item:

| content | where the rows need it | home at the consumer's frame |
|---|---|---|
| `t0eq`, `t1eq`, `t0K` | `TmVal` (`Condensation.lagda.md:2885-2890`), the atom rows and the bounded-quantifier rows read the numerals at the `t0`/`t1` slots | NONE. `KFacts` constrains `N0`/`N1` (`tagEq0` `:5737`, `tagEq1` `:5738`), never `t0`/`t1`. The consumer takes `t0 t1` bare (`:6477`). MEASURED: `t0eq` from `kf .tagEq0` fails at `ProbeLJ193C.agda:66-67` (`N0 != t0`) |
| general `entryK` | every `EnvSet` instantiation in the rows (`:2861-2866` and the row backs) | NONE. The consumer holds only the C-slot instance (`closedEntryK` `:6501-6503`) and the T-slot instance (`domEntryK` `:6504-6506`). MEASURED: `entryK` from `closedEntryK` fails at `ProbeLJ193C.agda:69-75` |
| `envK-mem/neg/top/imp/allin`, `envInK-mem/neg/top/imp` | the rows' machine-to-story `back` (`:2863`, `:3326`, `:3609`) | NONE. No consumer parameter concludes `E ∈ K` from an `envSetAt`/`envOverAt` satisfaction. MEASURED by listing (`:6476-6513` holds no such type); INFERRED that no derivation exists |
| `valV`, `valW`, `wKfact` | the atom rows' `AtomLeaf`/`BndLeaf` instantiations (`:4206`, `:4227`, `:4772`) | NONE. MEASURED by listing; INFERRED no derivation |
| `subK₁-and`, `subK₀-and`, `subK₁-imp`, `subK₀-imp`, `subK-neg`, `subK-un` | the propositional and unary rows' `back` (`:3325`, `:3611`) | NONE. MEASURED by listing; INFERRED no derivation |
| `succK`, `keyK-neg`, `keyK-un`, `subK-un`, `consK-exist`, `consK-forall`, `succK-allin`, `keyK-allin`, `subK-allin`, `consK-allin` | the AllIn/ExIn rows (`UpperAgree.lagda.md:207`, `:214`) | NONE. MEASURED by listing; INFERRED no derivation |
| `someEnv` | the And/Or rows (`Condensation.lagda.md:3330`) | NONE. The consumer holds no env-existence fact. MEASURED by listing; INFERRED no derivation |
| `tmKeyK`'s honest replacement, the `keyValK` shape (`(t : S) → ⟨ (t ∷ γ) ⊨ tagAtL ... ⟩ → t ∈ K`) | `TmVal.in'` `:2948` (`kk k`) | NONE. `SatGraphAgree`'s frame does not hold it; `LeafAgree` holds it as a hypothesis (`:6764-6765`), not as a fact of the shared record. MEASURED by listing; INFERRED no derivation from the six site facts |

The abort criterion fires: the ideal form cannot be stated at the
consumer's frame. The finding is about the consumer, not about the
split: the consumer's own frame is short of the satisfier-in-K family
and the `t0`/`t1` facts.

## 2. THE REPAIR IN PLACE: THE PER-USE TABLE

The three hypotheses have no value-use inside the three masters' own
proof bodies. The composer (`TwelveAgree.lagda.md`) only threads them
into the partials (`:252-253`, `:263-264`, `:278-279`, `:287-288`,
`:299-300`, `:308-309`). The partials only pass them into the twelve
row modules. The value-uses live in the shared rows inside
`src/L/Condensation.lagda.md`.

| hypothesis | every value-use | what the use needs | premises at the site | served by `carrierK` (`:5767-5768`)? | served by `arityK` (`:5769-5770`)? | served by a conditional fact the consumer holds? |
|---|---|---|---|---|---|---|
| `valK` (binary, rows 0-4, 10, 11) | one per row `back`: `ycK = valK c ar a b yc c∈ shEq` (`Condensation.lagda.md:3323`, `:4216`, `:4792`, `:4914`, `:5014`, `:5109`; Or delegates to And at `:3439`) | `yc ∈ K` for the graph-value witness `yc`, from `c∈ : c ∈ C-slot` and `shEq : c ≡ pr ar (pr k (pr a b))` | the graph membership `hc : ⟨ pr (fst c) (fst yc) ∈ fst (lookup T γ) ⟩`, a binder of every row's `back` (`binClause-out`, `src/L/Coding/Model.lagda.md:911-917`) | NO. Needs `yc ∈ A-slot`, absent | NO. Needs `yc ∈ N` with `N ∈ K`; the site has `pr c yc ∈ T`, never `yc ∈ N` for an `N ∈ K` | YES, machine-checked. `domEntryK`'s second projection at `(c, yc)` with `hc` is exactly `yc ∈ K` (`src/ProbeLJ196A.agda:50-52`, green). The row/frame type must gain the `hc` premise |
| `valK-un` (unary, rows 5-9) | one per row `back`: `ycK = valK c ar a yc c∈ shEq` (`:2757`, `:3524`, `:3607`, `:3721`, `:3891`) | same, minus `b` | same `hc` | NO | NO | YES, same fact and same probe |
| `tmKeyK` (all three masters) | one value-use: `kk k` in `TmVal.in'` (`Condensation.lagda.md:2948`), reached through `AtomLeaf` `:3984` and `BndLeaf` `:4530` from the four leaf rows (`:4159`, `:4745`, `:4867`, `:5052`) | `k ∈ K` for the machine's unbounded term-code witness `k` | the tag satisfaction `ht : ⟨ (k ∷ γ) ⊨ tagAtL (suc t) 1 zero ⟩` and the app satisfaction `hm` (`TmVal.in'` `:2939-2948`) | NO. Needs `k ∈ A-slot`, absent | NO. Needs `k ∈ N` with `N ∈ K`; the site's facts about `k` are structural (tag/app), and no enclosing `N ∈ K` is available | NO. The honest conditional is the `keyValK` shape (tagged implies in K), which `KeyAgree` `:6334-6335` and `LeafAgree` `:6764-6765` state as a hypothesis, not a fact; the consumer's six site facts do not include it |

The repair price: change the three hypothesis types and their use
sites. `valK`/`valK-un` need the added `hc` premise at the 12 row
telescopes (`Condensation.lagda.md:2737`, `:3361`, `:3414`, `:3483`,
`:3549`, `:3655`, `:3758`, `:4153`, `:4709`, `:4831`, `:4952`,
`:5046`), the 11 use lines, and the 3 master telescopes
(`LowerAgree.lagda.md:88-98`, `UpperAgree.lagda.md:78-88`,
`TwelveAgree.lagda.md:86-96`). `tmKeyK` needs the `keyValK` shape at
`TmVal.in'` `:2892`, `:2948`, the two leaves, the four leaf rows, and
the 3 master telescopes. The changed lines total roughly 80 to 120
across four files. The change does not make the masters consumable at
the consumer's frame: the other 36 unsupplied hypotheses remain
(MEASURED, section 1), and the `keyValK` replacement has no home
there. C-35 still applies: a repaired master with no consumer is
untested.

## 3. WHICH IS CHEAPER, AND WHY

The ideal form has no line price: it cannot be stated at the pinned
frame (section 1). The repair has a line price of roughly 80 to 120
changed lines (section 2), but it does not reach the consumer's frame,
so it produces a frame that still has no instantiation. Neither form
delivers a consumable twelve-row agreement. The recommendation is to
retire the three delivered masters: the delivered frame is measured
empty at every frame (section 6), and the repair keeps an unconsumed
artifact alive at a frame nobody holds.

The line arithmetic of the ideal form, as evidence only: the delivered
telescopes run from `LowerAgree.lagda.md:59-185` (about 127 lines),
`UpperAgree.lagda.md:49-172` (about 124 lines) and
`TwelveAgree.lagda.md:45-243` (about 199 lines); a telescope of
`KFacts` plus the six site facts is about 35 facts, or roughly 40
lines. The saving is real but not reachable: the missing facts must
first have a home.

The risk comparison: the repair touches 12 row telescopes and one
shared transfer inside `src/L/Condensation.lagda.md`, whose cold check
is about 102 to 108 s (MEASURED, `_build/lj-1.76-report.md` and
`_build/lj-1.79-report.md`), plus the three masters at 20.64, 11.23
and 21.33 s (MEASURED, `_build/lj-1.76-report.md:38-40`). The
`TmVal.in'` signature change ripples through four rows and two leaves.
The retirement risk is near zero: nothing outside the split imports
the three masters (MEASURED, `rg` over `src/`; the only importers are
`src/Everything.lagda.md:371-373`), and the association bridge
survives (`src/ProbeLJ193A.agda:57-97`, green).

## 4. THE WIDEST UNMEASURED TERM AND ITS PROBE

The recommended path is retirement, and the next real step is a
rewrite at a frame the consumer can hold. The widest unmeasured term
in that path is the per-row line and seconds cost of the twelve-row
agreement at `KFacts` plus the six site facts plus the satisfier-in-K
family: it prices the whole rewrite, and it settles how many of the
satisfier-in-K facts must stay hypotheses. Its probe is one row, the
Mem row, restated at that extended frame in a probe file, cold-checked
at the C-12 cap, with the unsolved metas naming exactly which facts
still have no home. That probe is NOT built here: the abort criterion
stopped the dispatch at the unstatable ideal form.

The probe that WAS built prices the repair's consumer-side supply:
`src/ProbeLJ196A.agda:50-52` shows `domEntryK`'s second projection
serves the row `valK` use, green at the cap, 0.79 s user, 1.01 s
total, load average 3.26 to 3.28 (4 users).

## 5. THE DD4 ANSWER

The delivered split maximizes sharing at the 69-fact frame
(`_build/lj-1.76-report.md:158-165`). The consumer holds the 29-field
`KFacts` frame plus six site facts. The two frames do not meet, and
the split as delivered is a DD4-negative at the frame level: sharing is
only free when the shared frame is the frame the consumer actually
holds (`_build/lj-1.93-report.md` section 6), and this frame is not
it. The ideal form should be generic in the consumer's frame, but that
frame is short of the satisfier-in-K family, so the ideal form's
generic frame is the consumer's frame extended by those facts. The
consumer's own frame is the finding, not the split.

The association bridge is generic in the twelve conjuncts and survives
whatever is ruled (`src/ProbeLJ193A.agda:57-97`); that work is
untouched by this verdict.

## 6. NEGATIVES AND THEIR STATUS

1. The ideal form at the consumer's frame has a line price:
   **MEASURED FALSE**. The content with no home is itemized in
   section 1; the `t0eq` and `entryK` no-homes are machine-checked
   (`src/ProbeLJ193C.agda:66-75`). This negative sets the verdict.
2. The satisfier-in-K family is derivable at the consumer's frame:
   **INFERRED FALSE, NOT CLAIMED AS MEASURED**. The types are absent
   from the telescope (MEASURED by listing); no derivation is
   delivered or visible. No verdict rests on the inference alone.
3. `tmKeyK`'s use is served by `carrierK` or `arityK`:
   **MEASURED FALSE by shape**. Both need a membership premise the
   site does not hold (`k ∈ A-slot`, or `k ∈ N` with `N ∈ K`); the
   site's facts about `k` are the tag and app satisfactions only.
4. `valK`/`valK-un`'s uses are served by `carrierK` or `arityK`:
   **MEASURED FALSE by shape**. Same reason: the needed premises are
   absent; the graph membership `hc` is the premise that closes the
   use, and it is not the premise either field takes.
5. `valK`/`valK-un`'s uses can be served by a conditional closure
   fact the consumer holds: **MEASURED TRUE**. `domEntryK`'s second
   projection closes the use at the site
   (`src/ProbeLJ196A.agda:50-52`, green).
6. The repaired masters become consumable at the consumer's frame:
   **MEASURED FALSE**. The other 36 unsupplied hypotheses remain, and
   the `keyValK` replacement has no home (section 1).
7. The three masters have an instantiation as delivered:
   **MEASURED FALSE**. `tmKeyK` is refuted at every frame
   (`src/ProbeLJ195A.agda:45-48`, green; `_build/lj-1.95-report.md`
   section 0).

## 7. ARCHIVE USED

- `_build/lj-1.76-report.md`, read WHOLE. TOOK the 69-fact frame, the
  per-master seconds (20.64 / 11.23 / 21.33 s, `:38-40`), the
  delivered-and-unconsumed verdict (`:57-58`), and the generic-frame
  DD4 claim (`:158-165`).
- `_build/lj-1.95-report.md`, read WHOLE, and `src/ProbeLJ195A.agda`,
  read. TOOK the `tmKeyK` refutation (`:45-48`) and the blast radius:
  all three masters state the empty type.
- `_build/lj-1.93-report.md`, read WHOLE, and
  `src/ProbeLJ193A.agda`, `src/ProbeLJ193B.agda`,
  `src/ProbeLJ193C.agda`, read. TOOK the 39-unsupplied table, the
  machine-checked `t0eq`/`entryK` mismatches (`ProbeLJ193C.agda:66-75`),
  and the green association bridge (`ProbeLJ193A.agda:57-97`).
- `_build/lj-1.79-report.md` and `_build/lj-1.77-report.md`, read
  WHOLE. TOOK the guarded `KFacts` forms and the `arityK` refutation
  recipe; the current `carrierK`/`arityK` at
  `src/L/Condensation.lagda.md:5767-5770` are the repaired shapes.
- `src/L/Condensation.lagda.md:5734-5770` and `:6476-6696`, read.
  TOOK the 29-field `KFacts`, the `SatGraphAgree` telescope, and the
  six site facts at `:6492-6513`.
- `dev/LESSONS.md`, C-38 as extended (`:3427-3520`), C-35
  (`:3200-3242`), C-36 (`:3284-3332`), D-29 (`:3242-3284`), D-30
  (`:3332-3380`), D-1 (`:1038-1195`), D-8 (`:1377-1397`), read WHOLE.
  TOOK the conditional-closure standard, the no-consumer-no-delivered
  gate, and the price-what-the-consumer-needs rule.
- `dev/PLAN.md` DD13 (`:174`), read. TOOK the rewrite-side rule: price
  the ideal form first; a consumer does not prove a chapter must stay.
- `dev/ARCHIVE.md`, read. TOOK the archival record's required columns
  (why, last green, measured size, what it did right, revival
  condition), in case the owner rules retirement.
- `archive/rud-route/`, SHAPE only. Took nothing.

## 8. LITERATURE USED

Nothing in the literature prices a frame in our own tree. Banked;
nothing spent.

## 9. GATES

- `src/ProbeLJ196A.agda`: GREEN, exit 0, 0.79 s user, 1.01 s total,
  one process at the C-12 cap, load average 3.26 to 3.28 (4 users).
- `scripts/lint-agda.py --check src/ProbeLJ196A.agda`: exit 0.
- `scripts/lint-prose.py --check _build/lj-1.96-report.md`: exit 0.
- No master was touched. `src/L/Condensation/`, `src/L/Coding/`,
  `src/V/` and `src/Everything.lagda.md` are untouched.
- No `make check`. No commit, no push. The tree is clean at
  `3ce65f4`; the probe and this report are gitignored by design.
