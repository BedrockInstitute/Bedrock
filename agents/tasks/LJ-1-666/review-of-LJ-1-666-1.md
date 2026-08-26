# review-of-LJ-1-666-1: the stop is correct, three stated reasons are not

## HEAD
head_slot: mathematician_adversarial
machine: shared
task: LJ-1.666
attacked return: LJ-1.666#1, `agents/tasks/LJ-1-666/lj-1.666-report.md`, with its stated NO-GO `agents/tasks/LJ-1-666/review-of-sat-at-level.md`
verdict: **upheld**

I attacked the return, not the task. I wrote this one file and nothing
else. I wrote and touched no `.agda` file, so A21 holds for this return
the same way it binds the one under attack. No commit, no push.

## 0. WHAT THIS REVIEW READ

The report, the work brief `LJ-1.666.md`, `Probe666.agda`, the four files
under `runs/`, the predecessor probes and reports that the report cites,
and the cited lines of `src/L/Condensation.lagda.md`,
`src/L/BoundedSubset.lagda.md`, `src/L/Hierarchy.lagda.md` and
`src/L/Hull.lagda.md`.

`dev/pod/transitions/2026-08.jsonl` in this checkout holds no line with
`"task": "LJ-1.666"`. Its last line is `LJ-1.665` at `seq 4317`. So the
model, the effort and the `heads_sha256` of the attacked return are not
in this checkout, and this review does not infer them. The six facts of
the run came from the acceptance arm: exit 0, one green run at 0.82 s,
six changed files all own, zero in-fence lines, one obligation open with
delta 0, no error class (`runs/accept-1.out:25`).

## 1. QUESTION 1: DOES THE VERDICT LINE MATCH ITS OWN BODY?

No. Three mismatches. The stop itself still stands; section 4 says why.

### 1.1 The line claims a universal the body never establishes

The line: "The obligation is not inhabited for any arity-2,
parameter-free `φ₀` built from the chapter's bounded matrix"
(`lj-1.666-report.md:24`, `review-of-sat-at-level.md:9`).

The body says of the direct route: "A direct proof of the bounded graph's
stage satisfaction, bypassing the bridge, is not
delivered in the tree" (`review-of-sat-at-level.md:87-88`). It says the
same of the third and fourth routes, that they are "not delivered in the
tree" (`review-of-sat-at-level.md:168`, `lj-1.666-report.md:195`). Not
delivered is a fact about the tree. The line turns it into a fact about
inhabitation. A body that hands four unpriced constructions to the next
brief cannot carry a line that says no construction exists.

### 1.2 The class in the line has cheap inhabitants

This is an argument, and this review labels it as one; it was not run.
The chapter's own import list exports the truth constant (`⊤̇`,
`src/L/BoundedSubset.lagda.md:12`). If `φ₀` is in the class of the line,
then `φ₀ ∨̇ ⊤̇` is also in that class. It keeps arity 2. It stays free of
constants, because `hood2` already is (`count-hood2 = refl`,
`agents/tasks/LJ-1-662/Probe662.agda:118-119`) and `⊤̇` adds none. Its
satisfaction at the canonical environment holds through the second
disjunct at every stage. So the line, read as written, is false.

What keeps such a formula out of the campaign is the soundness half: the
formula must pin the value to `Lset γ` so `HoodSoundP` can read it. The
return states this constraint itself, but only inside option 4 of its own
next-brief list (`review-of-sat-at-level.md`, section 6). The constraint
is real. It lives outside the satisfaction obligation, and the body never
argues it into the verdict line.

The brief did not cause this. The brief forbids one module ("DO NOT PIN
AT `LevelHood0`", `LJ-1.666.md`, THE OBLIGATION). The widening from that
one module to "any `φ₀` built from the chapter's bounded matrix" is the
return's own act.

### 1.3 The line quotes a number no run file carries

"0.98 s" stands in the verdict of both files (`lj-1.666-report.md:26`,
`review-of-sat-at-level.md:11`) and again in both run tables
(`lj-1.666-report.md:145`, `:152`, `review-of-sat-at-level.md:147`). The
meter file reads "witness: 1 UNRESOLVED of 1, 0.58 s, probe_red=False"
(`runs/meter-obligation.out:2`). The acceptance arm reads
`"witness_seconds": 0.57` (`runs/accept-1.out:25`). No file under `runs/`
contains the string `0.98`; it occurs only in the two authored files.

Three more numbers of the same kind stand in the report's run table
(`lj-1.666-report.md:144-147`). The table gives `probe-2` a wall of 1.2 s
and a peak RSS of "not measured"; the file prints "1.88 real" and
"289062912 maximum resident set size" (`runs/probe-2.out`). The table
says the probe is 155 lines with 38 code lines; the file has 177 lines,
of which 25 are neither blank nor comment.

The file times show the cause. `review-of-sat-at-level.md` was last
written at 22:44:42. `Probe666.agda` was edited at 22:47:43. The meter
ran at 22:48:02. The stated NO-GO was not refreshed after the last runs.
C-22 (`dev/LESSONS.md:2307`) asks for incremental writing; here the
writing stopped before the last answers landed, and the verdict kept a
stale number.

## 2. QUESTION 2: IS EVERY LOAD-BEARING CLAIM BACKED BY A `file:line` THAT RESOLVES TODAY?

Mostly yes. The slot-count spine of the NO-GO resolves and is read
correctly: `LevelHood0`'s N-parameters `Fin 5` (`src/L/BoundedSubset.lagda.md:841`)
and M-parameters `Fin 7` (`:842`), matrix arity 4 (`:849`), the `KFacts`
fields (`src/L/Condensation.lagda.md:6079` onward), `Kenv : S ^ 14`
(`:7389`), the sole value `facts` (`:7411`), `DefBodyB`'s sixteen indices
over `Fin (5 + n)` (`:2338-2346`), the six `graphBndAt` sites,
`Lset-only` (`src/L/Hierarchy.lagda.md:334-335`), `Lset-defines`
(`:646`), `LeafAgree` (`src/L/Condensation.lagda.md:7224`), the named
residue (`src/L/BoundedSubset.lagda.md:901-902`), `SatAtLevel`
(`agents/tasks/LJ-1-662/Probe662.agda:284-286`), `hood2` (`:110-111`),
the consumer (`:331`), `HoodExistsP` at arity 2
(`agents/tasks/LJ-1-653/Probe653.agda:283`).

Four claims do not hold.

### 2.1 `runs/probe-1.out` does not resolve

Both files cite it as the first red run (`lj-1.666-report.md:143`,
`review-of-sat-at-level.md:145`). `runs/` holds `accept-1.out`,
`meter-obligation.out`, `probe-2.out` and `probe-recheck-1.out`. The
cited file is absent. The record points at evidence that is not there.

### 2.2 `extAtB→extAt` takes no `KFacts`

The report: "the `fwd`/`bwd` arguments are `KFacts`-indexed"
(`lj-1.666-report.md:92`). The review: "it takes a `KFacts`-indexed leaf
agreement" (`review-of-sat-at-level.md:81`). The signature
(`src/L/Condensation.lagda.md:2514-2518`) takes two plain satisfaction
implications and one membership fact:

    → ((z : S) → ⟨ (z ∷ γ) ⊨ φB ⟩ → ⟨ (z ∷ γ) ⊨ φ ⟩)
    → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ (z ∷ γ) ⊨ φB ⟩)
    → ((z : S) → ⟨ (z ∷ γ) ⊨ φ ⟩ → ⟨ fst z ∈ fst (lookup K γ) ⟩)

No `KFacts` appears in it. The `KFacts` enters at `LeafAgree`, the priced
instance of those implications for the `DefBodyB`/`DefBody` leaf. The
lift is generic; the price is leaf-local.

### 2.3 "The only bridge in the tree is `LeafAgree`" is false as an enumeration

`review-of-sat-at-level.md:77`. The lift itself is a bridge, and the tree
uses it at twelve more sites with leaf agreements that come from no
`KFacts`. At `src/L/Condensation.lagda.md:2727` both directions are
`(λ z x → x)`. The same lift serves at `:3268`, `:3733`, `:3831`,
`:3955`, `:4135`, `:4505`, `:5135`, `:5264`, `:5463`, `:6880`, `:6949`.
The true statement is narrower: the only delivered leaf agreement for the
`DefBodyB` leaf is `LeafAgree`, and `LeafAgree` carries a `KFacts` among
its hypotheses.

### 2.4 The `KFacts` record does not require fourteen environment slots

The report: "The `KFacts` requires fourteen environment slots"
(`lj-1.666-report.md:114`). The review: "requires a `KFacts` record at
fourteen environment slots" (`review-of-sat-at-level.md:77-79`). The
record is generic: `record KFacts {n : ℕ} (A K N0 ... N11 : Fin n)`
(`src/L/Condensation.lagda.md:6079`). Fourteen is the environment arity
of the sole value, `Kenv : S ^ 14` (`:7389`). Two facts follow, and the
return uses neither. First, `LeafAgree` runs its `KFacts` at
`S ^ (8 + n)`, not at fourteen (`src/L/Condensation.lagda.md:7225-7226`).
Second, the sole value extends to every larger arity by `KFactsCons`
(`:6122`), and the tree's own consumer accepts the extension (`consed`,
`:7429`). Fourteen is the floor of the delivered value. It is not a
commitment of the record, and it is not a wall the arity-2 side must
meet.

## 3. QUESTION 3: IS THE ENUMERATION COMPLETE?

No. Four gaps.

### 3.1 The `LevelHood {n}` route is mispriced, and the body contradicts itself

The report says "This is true of ANY instantiation of the bounded graph,
at ANY arity" (`lj-1.666-report.md:114-115`) and, two lines later,
"`LevelHood {n}` for `n ≥ 14` has room for the columns" (`:117`). Both
cannot hold. The thresholds are also not read off the machinery. The
twelve numeral columns of `DefBodyB` must occupy twelve distinct slots
among the `5 + n` its indices address (`src/L/Condensation.lagda.md:2338-2346`),
so the columns fit from `n ≥ 7`, and from `n ≥ 9` once the `w` and `K`
slots must also be distinct. `LeafAgree`'s `KFacts` environment `8 + n`
reaches fourteen at `n ≥ 6` (`:7225-7226`). At `n = 9` the matrix arity
is 13, not "`4 + n ≥ 18`" (`review-of-sat-at-level.md:121-122`). The
number fourteen was carried from the delivered value (`:7389`) into a
threshold it does not set.

### 3.2 "Closing the surplus by `∃̇` loses the tag equations" is an argument, not a measurement

`review-of-sat-at-level.md:122-123`, `lj-1.666-report.md:119`. The tag
equations are `refl` when the environment is built with the numerals in
place (`KValue.facts`, `src/L/Condensation.lagda.md:7413`). An
existentially closed witness chosen as the numeral makes its own tag
equation true by construction. What the closing really costs is a
different fact: the formula stops forcing the numerals, which matters to
the soundness half, and the stage semantics must supply them, which
matters to the satisfaction half. Neither cost was measured. W1 binds
this point for both returns: an argument changes no architecture; the
measurement does, and the architecture decision stands at `[LJ-2.5]`.

### 3.3 The stage question is not asked

`⊨c` is the code-indexed semantics of the hull (`_⊨c_ = AtCode._⊨_`,
`src/L/Hull.lagda.md:94-95`), and the numerals enter it as base codes
(`val (base m) = emb m`, `:89`). The delivered `KFacts` value is a fact
about a bound level: `numK0 = B.num∈λ 0` and its siblings
(`src/L/Condensation.lagda.md:7416`). Whether the twelve tag equations of
`embed hood2` close at the canonical environment in the `⊨c` semantics
is the widest unmeasured term in the whole return, and the return never
names it as a term. Section 5 names the probe.

### 3.4 `LeafAgree`'s other hypotheses are unpriced

`LeafAgree` takes six site facts beside the `KFacts`: `witK`, `wCodesK`,
`wUnCodesK`, `wEntryK`, `twelve-out`, `twelve-back`
(`src/L/Condensation.lagda.md:7231-7262`). The return prices only the
`KFacts`. A cure that supplies the `KFacts` still owes the six.

## 4. WHY THE STOP STANDS ANYWAY

The lens is DD25's four, at `archive/dev/DD-archived.md:35`; this review
cites section 6.6 only for the three questions it answers above.

1. On its own numbers, at the site that matters, the verdict is correct.
   `LevelHood0`'s N-parameters address at most five slots and its
   M-parameters at most seven (`src/L/BoundedSubset.lagda.md:841-842`).
   The `DefBodyB` leaf reads twelve numeral columns from those slots
   (`src/L/Condensation.lagda.md:2338-2346`). Five does not reach twelve;
   seven does not reach twelve. No choice of the twenty-eight parameters
   changes this. The brief forbade the module for this reason, and the
   prohibition is sound.
2. The measurement is honest where it counts. The obligation name is
   absent from the probe, the meter reads one unresolved obligation with
   the probe green (`runs/meter-obligation.out:1-2`), and the return says
   plainly that the `[NotInScope]` reading is the branch table's priced
   reading (`review-of-sat-at-level.md`, section 1). No stage-satisfaction
   lemma for the bounded graph exists in `src/`; the six `graphBndAt`
   sites are the definition and its certificate.
3. The brief did not cause the outcome. The brief priced the NO-GO
   itself, and the earned content, which arity and which slot commitment
   cannot be met at once, is delivered: arity 2 against twelve numeral
   columns. The defects of sections 1 to 3 are the return's own: the
   stale numbers, the widened class, the misread bridge, the invented
   thresholds.
4. No cure was missed that lands at this task's price. Every route in
   section 3, corrected for its true price, is still new work. The
   direct `⊨c` satisfaction is the chapter's named residue
   (`src/L/BoundedSubset.lagda.md:901-902`). The `LevelHood {n}` route
   opens at `n ≥ 9`, with a matrix at arity 13 still to close to 2. None
   of that fits inside this task's scope and price.

The NO-GO is upheld. The corrections in sections 1 to 3 are for the next
brief, and the next brief must not build on the return's "only bridge"
count, its fourteen-slot record claim, or its `n ≥ 14` threshold.

## 5. W3, ANSWERED (A21)

The widest unmeasured term: the direct `⊨c` price of `embed hood2` at the
canonical environment, that is, the twelve tag equations of the embedded
matrix in the code-indexed hull semantics (`src/L/Hull.lagda.md:89`,
`:94-95`). Estimate: 100 lines, one best-effort number. Basis: a
delivered comparable, `agents/tasks/LJ-1-666/Probe666.agda`, 177 lines,
green at 0.82 s (`runs/accept-1.out:25`).

The probe, named for the coder to write; this review writes no `.agda`
file. A probe under the next task home that states the twelve tag
equations of `embed hood2` at the canonical environment as obligations in
the `⊨c` semantics, with the numerals as base codes, and runs the witness
meter on them. Green says the direct route is cheap and the bridge story
was the wrong wall. Red, with those obligations named, says the stage
itself resists, and the next brief prices a stage-closure lemma.

## ARCHIVE USED

- **`archive/dev/DD-archived.md` READ.** `archive/dev/DD-archived.md:35`
  carries the four questions of the lens: "is the refusal correct on its
  own numbers; is the measurement sound; did the BRIEF cause the outcome;
  and is there a cure the return missed".
- **`archive/dev/ORCHESTRATION.md` DECLINED.** Not read. The dispatch
  process is not in question; the program's preamble stands in this
  dispatch.
- **`archive/dev/PLAN-archived.md` DECLINED.** Not read. A history; the
  live status is `dev/pod/screen.toml`.
- **`archive/dev/measurements/README.md` DECLINED.** Not read. No
  measurement method was in question; the meter output was read
  directly.
- **`archive/dev/README.md` DECLINED.** Not read. No placement question
  arose; this review writes one file into an existing task home.

## LITERATURE USED

- **`dev/literature/level-formula-slot-roles.md` READ.**
  `dev/literature/level-formula-slot-roles.md:26` reads
  `| 4 | Devlin 5.2 (a) | \`Φ(z,v,γ)\` with \`∀v∀γ [v = L_γ ↔ ∃z Φ(z,v,γ)]\` | 3 in \`Φ\`, ONE closed | \`z\` at position 0 | \`v\` at 1, \`γ\` at 2 | **VALUE, ORDINAL** | \`_build/literature/dev2.txt:1186-1191\` |`.
  This confirms the arity-2 free pair that the brief (premise 4) and the
  return both used.
- **`dev/literature/BIBLIOGRAPHY.md` DECLINED.** Not read. No citation
  was added or questioned.
- **`dev/literature/devlin-errata.md` DECLINED.** Not read. This review
  certifies no leaf as bounded.
- **`dev/literature/primary-sources.md` DECLINED.** Not read. No source
  was missing; the slot-roles table answered the arity question.
- **`dev/literature/glossary-review-2026-08.md` DECLINED.** Not read. No
  naming question arose.
