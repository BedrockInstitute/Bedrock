# LJ-1.318 ruling: the level-hood cure lands, in Form 1, as SIX lines

Authorization: the owner's delegation, dated 2026-08-15, scoped to this one
set of rulings. The orchestrator executes. Nothing here edits `AGENTS.md`,
nothing here pushes, and nothing here changes what a trophy states.

## 0. DECISION

**LAND the cure, in Form 1, as SIX in-place line replacements in
`src/L/BoundedSubset.lagda.md`: lines 82, 90, 105, 111, 116 and 124, zero
net lines.** The four-line count is short by two: the Δ₀ certificate inlines
the two leaf literals again, and this ruling MEASURED both directions
(section 6). Form 2 is REFUSED and is not priced. Three subsidiary rulings:

1. The digest LANDS as `dev/literature/level-formula-slot-roles.md`
   (section 5).
2. `dev/literature/devlin-II5.md` section 6 gets the clause (a)
   restoration entry, and `BIBLIOGRAPHY.md` entry 17 records the Kunen
   fetch (section 5).
3. The determinacy question is a SEPARATE question. It gets its own gate,
   and the gate runs before anybody funds the `q'` build (section 4). It
   does not delay this landing.

## 1. REASONS

**R1. The defect is real, and all three legs agree.** The probe measured
it: the delivered formula refuses the cured one at
`agents/tasks/LJ-1-312/ProbeLJ1312C.agda:39`, exit 42, and the role census
at `ProbeLJ1312A.agda:177-282` pins the delivered free pair to (ORDINAL,
machinery bound). The review re-ran that witness and verified every hop of
the role chain (`agents/tasks/LJ-1-313/lj-1.313-report.md` sections 1 and
2). The literature fixes the specification: the free pair is (VALUE,
ORDINAL) in Devlin 2.7 and 5.2, Jech 13.14, Kunen VI 3.2 and
Schindler-Zeman 1.10(2) (`agents/tasks/LJ-1-315/lj-1.315-report.md`
section 1). `q'` needs (VALUE, ORDINAL)
(`agents/tasks/LJ-1-244/ProbeLJ1244A.agda:111-114`, per the review).

**R2. Form 1 is the only coherent form.** The review REFUTED Form 2's
premise by machine: the delivered matrix mis-bounds its own leaves on a
BOUND variable (`ProbeLJ1313A.agda:88-109`, control
`ProbeLJ1313B.agda:44`, exit 42), and a permutation of FREE slots cannot
reach a bound variable (`lj-1.313-report.md` section 6). The literature
gives Form 2's two-independent-bounds shape no precedent in any of the
four authors, and Devlin states the single-bound rule in words: all
unbounded quantifiers are bound by ONE set
(`_build/literature/dev2.txt:591` and `:600-601`, re-read for this
ruling). The probe's own recommendation to price Form 2 first does not
survive this evidence, and I set it aside (section 7).

**R3. The landing diff is six lines, not four. MEASURED here, both
directions.** The Δ₀ certificate inlines the two leaf literals at
`src/L/BoundedSubset.lagda.md:116` and `:124`, mirroring `:82` and `:90`.
My `ProbeLJ1318A.agda` holds the delivered structure with exactly the six
replacements: exit 0 in 21.22 s. My `ProbeLJ1318B.agda` holds the
four-line form with the two mirrors left stale: exit 42 at `:79`,
`[UnequalTerms]`, in 2.68 s. The six-line result is refl-equal to the
`[LJ-1.313]` cured copy (`ProbeLJ1318A.agda`, module `Tie`), so the
review's census (frame and content coincide, certificates unchanged in
shape) holds of this exact landing diff.

**R4. The landing breaks nothing in `src/`. RE-MEASURED here.**
`L.BoundedSubset` has exactly one importer, the bare
`import L.BoundedSubset` at `src/Everything.lagda.md:383`, with no `open`
and no `public`. The only other `src/` mention is a comment pointer at
`src/L/Coding/Key.lagda.md:73`. `LevelHood`, `levelHood` and `graphBndAt`
appear in no `src/` file outside `L/BoundedSubset.lagda.md` except
`graphBndAt`'s definition at `src/L/Condensation.lagda.md:2489-2493`. The
file's own tail also survives: `LevelHood0`'s members are formulas and
Levy certificates, never semantic terms
(`src/L/BoundedSubset.lagda.md:840-869`), and `ProbeLJ1318A.agda` section
3 restates all five members over the cured module verbatim, exit 0.

**R5. The certificates and the sizes do not move.** The Δ₀ and Σ₁
certificates typecheck with unchanged structure
(`ProbeLJ1313C.agda:134-141`, re-run here at exit 0, 2.57 s; and
`ProbeLJ1318A.agda:108-144`). The six replacements are one-for-one, so
standing does not move. The re-check comparable is about 17 s for the
file (`dev/ledger.toml:3126` and `:2749-2751`, a comparable and not a
measurement of this edit, P-l).

**R6. The comments must move with the code, minimally.** A wrong comment
in this file survived two years and seeded the defect chain
(`lj-1.312-report.md` section 8). After the cure the header comment at
`:70-73` stays wrong about slot zero only, and the comment at `:141`
misnames the closed slot as the witness. Section 2 gives one-for-one
replacement text. The comment at `:107` becomes TRUE under the cure and
stays.

## 2. WHAT THE ORCHESTRATOR MUST DO

Steps 1 to 5 are one landing commit. Steps 6 to 8 are one records commit.
Steps 9 to 12 are dispatches and bookkeeping.

1. **Apply the six line replacements** to `src/L/BoundedSubset.lagda.md`.
   The cured module is `ProbeLJ1318A.agda:67-139`, and the six cured
   lines there are `:75`, `:83`, `:98`, `:104`, `:109` and `:117`.
   - `:82` second argument of `DefBodyB`: `(suc (suc (suc (suc zero))))`
     becomes the nine-deep `(suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))`.
   - `:90` second argument of `DefBodyB`: the same literal becomes the
     eleven-deep `(suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))`.
   - `:105`: `zero (suc (suc zero)) (suc (suc (suc zero)))` becomes
     `zero (suc (suc (suc zero))) (suc (suc (suc (suc zero))))`.
   - `:111`: `var (suc zero) ≐ var zero` becomes
     `var (suc (suc zero)) ≐ var zero`.
   - `:116` (certificate mirror of `:82`): the same nine-deep literal.
   - `:124` (certificate mirror of `:90`): the same eleven-deep literal.
2. **Replace the comment lines `:70-73`**, four lines for four lines:
   ```
   -- u ∷ v ∷ γ ∷ K ∷ δ (4 + n).  Slot zero is unused; v is the value,
   -- γ the ordinal index, K the one bound.  The bounded existential
   -- binds the witness w, ranges over K (variable three), and the
   -- machinery shares that bound ([LJ-1.312], [LJ-1.313], [LJ-1.318]).
   ```
   **Replace the comment line `:141`**, one line for one line:
   ```
     -- The Sigma-1 form: closes the unused slot over the bounded matrix.
   ```
   Do NOT touch the comments at `:847`, `:854` and `:861-863`. They
   belong to step 11's task, together with the code they describe.
3. **Re-check the file**: count the Agda slots with the C-12 command
   first, then run `GHCRTS="-A64m -I0 -M8g" agda src/L/BoundedSubset.lagda.md`.
   Expect about 17 s warm (the ledger comparable, R5).
4. **Run `lint-agda.py` and the wired checkers** on the touched file.
5. **Commit the landing**, citing `[LJ-1.312]`, `[LJ-1.313]` and
   `[LJ-1.318]` as the evidence chain. Do not push without the owner.
6. **Land the digest**: copy
   `agents/tasks/LJ-1-315/proposed-devlin-slot-roles.md` to
   `dev/literature/level-formula-slot-roles.md`. Strip the proposal
   banner, lines 1 to 9. Amend its one forward-looking sentence, "entry
   17 lists Kunen as cite-only, and this fetch changes that", to "entry
   17 records the fetch", after step 8.
7. **Correct `dev/literature/devlin-II5.md` section 6**: add a resolved
   item that clause (a) at `:95-100` is a RESTORATION, because the scan
   loses the (a) display (`_build/literature/dev2.txt:1187-1191`), with
   the three legible confirmations: the slot order at `dev2.txt:1186`,
   clause (b) at `:1193-1198`, and 2.7's `H(x,α)` at `:679-680`. Credit
   `[LJ-1.315]`.
8. **Update `dev/literature/BIBLIOGRAPHY.md` entry 17** (Kunen): fetched
   2026-08-15 from the TU Delft URL the digest names, open access, read
   for the level formula, not retained in the tree; the slot-roles digest
   reads it.
9. **Register `[LJ-1.318]`** in `dev/PLAN.md` section 11 and
   `dev/JOURNAL.md` per section 6.0's rules.
10. **Dispatch the φ₀ re-derivation** (small): re-run
    `ProbeLJ1241A.agda`'s construction over the cured matrix. The review
    expects `ρ` and `pins` to survive by construction, INFERRED
    (`lj-1.313-report.md` section 8). Only after that, re-price the
    block `dev/PLAN.md` section 0.0 carries, because its 470 rests on a
    type this landing just changed.
11. **Dispatch the `LevelHood0` re-shape** (small, low priority): re-derive
    `Σ₂` and `reverse` and their comments against the cured roles, prove
    the result in a copy, then land. `LevelHood0` has no consumer
    (`lj-1.312-report.md` section 9, re-verified in R4), so this blocks
    nothing.
12. **Arm the determinacy gate** before any brief that funds the
    `q'`/`Composite` build (section 4). The gate is that brief's DD8
    widest-unmeasured-term, and `check-dd4-stated.py` does not cover it:
    write it into the brief by hand.

Do not re-run or repair the older probes that pin the pre-cure formula.
After the landing, any probe that states the delivered slots by `refl`
flips to exit 42. That flip is the expected consequence of a landed cure
and not a regression. The certain flips are `ProbeLJ1312A.agda`
(`probe-is-delivered`), `ProbeLJ1313A.agda` (the delivered leaf census),
and the delivered-shape pins in `ProbeLJ1241A.agda`, `ProbeLJ1241B.agda`
and `ProbeLJ1239A.agda`. INFERRED for the exact per-file outcomes of
`ProbeLJ1161A.agda`, `ProbeLJ1165B.agda` and `ProbeLJ1230A.agda`, which I
did not open.

## 3. WHAT WOULD REVERSE THIS RULING

Each condition is observable, and any one reopens the matching part.

1. **The landed file fails its re-check** (step 3 exits non-zero). My
   probes cover the `LevelHood` module and the whole of `LevelHood0`;
   the rest of the file names neither, MEASURED by the R4 sweep. A
   failure elsewhere would mean the sweep missed a path, and the landing
   reverts while that path is measured.
2. **A `src/` consumer of the changed names surfaces** that the name
   sweep missed, observable as a red module outside `L/BoundedSubset` in
   a full `src/Everything.lagda.md` check naming `LevelHood` or
   `graphBndAt`.
3. **The determinacy gate refutes the slot ORDER rather than the bare
   bound**: if its countermodel shows the cure put the wrong pair free,
   the Form 1 reading falls. I judge this near-impossible: three legs
   and four authors agree on the pair. But the gate could observe it.
4. **A legible print of Devlin 5.2's (a) display contradicts the
   restoration**, observable in a better scan. Three legible anchors
   make this near-impossible (`dev2.txt:1186`, `:1193-1198`,
   `:679-680`, re-read here).
5. **The owner rules the corpus holds one Devlin digest only**: then
   fold the slot-roles table into `devlin-II5.md` instead of landing a
   new file. The content of the ruling does not change.

## 4. THE DETERMINACY QUESTION, RULED

**It is a SEPARATE question, and it does not delay this landing.** The
survey is right that the difference is real: Devlin's witness carries the
determining conjunct `K(w,u)`, "which says w = K(u)"
(`_build/literature/dev2.txt:611`, re-read here), so his bound is unique.
Bedrock closes its bound with a bare existential
(`agents/tasks/LJ-1-241/ProbeLJ1241A.agda:140-146`, per the survey).
"SOME bound works" and "THE canonical bound works" are different
statements.

**Why it does not block the landing.** The cure repairs the slot ROLES,
and the roles are right under every answer to the determinacy question.
If a determining conjunct proves necessary, it is ADDED to the cured
matrix; it does not reorder the cured slots. Deferring the landing would
keep a MEASURED-false formula in the tree while a separate question
pends, and would keep the `dev/PLAN.md` section 0.0 price resting on a
wrong type.

**The trigger, named.** The gate runs BEFORE any brief that funds the
`q'`/`Composite` build. That brief must name, as its DD8 widest
unmeasured term: **whether the cured matrix at an ARBITRARY bound admits
satisfaction at a wrong value.** The risk shape is concrete:
`extAtB y K φ` is two universals
(`src/L/Condensation.lagda.md:100-102`, re-read here), so a degenerate
`K` makes both vacuous, and `extAtB` holds at an empty `y` for ANY `φ`.
Whether the full matrix admits such degenerate satisfaction is exactly
the soundness half of `q'`. INFERRED, no model ran. The gate probe
states the degenerate-bound satisfaction question in a miniature and
returns GO or NO-GO with a price. GO means the bare existential is
sound and the build proceeds. NO-GO means `levelHoodB` gains a
determining conjunct, Devlin's `K(w,u)` analogue
(`dev2.txt:611-623`), proved in a copy first. Either way the trophy
STATEMENTS do not move: `levelHoodB` is proof machinery, and
`L/BoundedSubset` sits in neither trophy closure today, MEASURED
(`dev/ledger.toml:2749-2751`, and the R4 grep).

## 5. THE DIGEST, RULED

**LAND it, under the survey's name: `dev/literature/level-formula-slot-roles.md`.**

- The corpus needs it: `devlin-II5.md` carries the level-hood chain and
  its complexity requirements, not the slot arithmetic, and the slot
  arithmetic is what this defect chain was about.
- Its load-bearing claims verify. I re-read the primary scan for this
  ruling: the (a) display is lost (`dev2.txt:1187-1191` print stray
  glyphs), the slot order is legible (`:1186`), clause (b) is legible
  (`:1193-1198`), the single-bound sentences are legible (`:591`,
  `:600-601`), the determining conjunct is legible (`:611`), and 2.7's
  `H(x,α)` is legible (`:679-680`). Every check agrees with the digest.
- The name fits the directory's convention of lowercase hyphenated
  topics, and it does not collide (`dev/literature/` listing, checked).
- Nothing is canonical twice: the new file carries the slot table and
  the OCR verdict; `devlin-II5.md` keeps the chain and gains only the
  section 6 correction entry, which cross-references it.
- The correction to `devlin-II5.md` is owed, MEASURED: its section 6
  items 6.1 to 6.6 do not mention clause (a), and `:95-100` presents the
  restored clause as a quotation.
- `BIBLIOGRAPHY.md` entry 17 is Kunen, at `:165`, and the fetch record
  belongs there (step 8).

## 6. VERIFICATION RUN FOR THIS RULING (C-44)

All Agda under `GHCRTS="-A64m -I0 -M8g"`, one process, cap never raised.
The C-12 count `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`
ran before every invocation and returned 0 every time. Machine load
(1-minute average) beside each wall figure. No run approached the
30-minute wall.

| run | exit | wall | load | what it establishes |
|---|---:|---:|---:|---|
| `ProbeLJ1313C.agda` re-run | **0** | 2.57 s | 7.07 | the review's cured copy stands on this machine today |
| `ProbeLJ1318A.agda` (new) | **0** | 21.22 s | 7.01 | the SIX-line diff in the delivered structure, tied to `LevelHoodC2` by `refl`, plus `LevelHood0` verbatim over the cure |
| `ProbeLJ1318B.agda` (new) | 42, EXPECTED | 2.68 s | 7.01 | the FOUR-line diff refuses at the certificate, `:79`, `[UnequalTerms]` |

Non-Agda verification: the R4 greps (importer, re-export, aliases); the
`LevelHood0` read at `src/L/BoundedSubset.lagda.md:840-869`; the
`extAtB` read at `src/L/Condensation.lagda.md:100-102`; the OCR
spot-checks in section 5; the `devlin-II5.md` section 6 read; the
`BIBLIOGRAPHY.md` entry check; the `dev/literature/` listing. The
delivered lines `:82-146` were read whole before the probes were
written.

## 7. WHERE THE LEGS DISAGREE, AND HOW I RULED

| disagreement | ruling |
|---|---|
| The probe recommends pricing Form 2 first; the review refutes Form 2's premise; the survey finds Form 2's shape unprecedented and formally weaker | **Against the probe.** Its recommendation predates the leaf measurement and cannot survive it. Form 2 is refused, not priced |
| The review counts the cure at FOUR lines; my measurement lands it at SIX | **Against the review's count, with its own content.** The review's copy proved the right term; its count missed the two certificate mirrors, MEASURED by `ProbeLJ1318B.agda:79` |
| The probe marks the `q'` falsity INFERRED; the review re-classifies it as a fork | No ruling needed. Both agree the delivered type is wrong, and the landing does not depend on the fork |

## 8. DD4, AND MY AXIS

DD4: maximize the code the two proofs share, and write it generic. My
axis is AC-against-GCH, DD4's own. The cure edits carrier-generic FOL
and bounded-set machinery; it names no tower stage and no trophy
carrier, so the repair is shared by construction. It moves no code
across the axis and changes no import; net lines are zero. The file is
GCH-bound and AC-free on the ledger's own qualification
(`dev/ledger.toml:204-205`), and that is unchanged by this ruling.

## 9. EVERY NEGATIVE, CLASSIFIED

| statement | class |
|---|---|
| The four-line landing does not typecheck | **MEASURED**, `ProbeLJ1318B.agda:79`, exit 42 |
| The six-line landing breaks nothing in the delivered file's own tail | **MEASURED** for `LevelHood0` (`ProbeLJ1318A.agda` section 3); **INFERRED** for the rest of the file, from the R4 name sweep |
| `L.BoundedSubset` has no importer beyond `src/Everything.lagda.md:383`, and no re-export path | **MEASURED**, R4 greps re-run for this ruling |
| `LevelHood`, `levelHood`, `graphBndAt` have no `src/` consumer outside the two files | **MEASURED**, R4 grep |
| Form 2 cannot repair the leaf defect | **INFERRED** by the review from the MEASURED bound-variable location; I take it |
| The determinacy question does not affect the cured slot order | **INFERRED**: a conjunct adds, it does not reorder. The gate can observe the contrary (section 3, condition 3) |
| The degenerate bound makes `extAtB` vacuously satisfiable | **INFERRED** from the syntax at `src/L/Condensation.lagda.md:100-102`; no model ran |
| The older probes' post-landing flips are not regressions | **INFERRED** from what each pins; the named certain flips are read, the three unread files are marked |
| Standing does not move | **MEASURED** for the diff shape (six one-for-one replacements, and comment steps 2 are line-for-line); the re-check cost is a comparable, P-l |
| No formalization faces this slot question | **INFERRED**, the survey's own classification, bounded by its 2026-08-02 index sweep; I did not re-search |

## 10. WHAT STAYS THE OWNER'S

- No edit to `AGENTS.md` is made or needed.
- No push. The landing waits for the owner's push in the normal cycle.
- No trophy statement changes. The cure and both follow-ups are proof
  machinery. If the determinacy gate ever demands a change to what
  either trophy STATES, that half escalates to the owner; nothing in
  this ruling predicts it.

## 11. PROHIBITIONS, ANSWERED

- I wrote only inside `agents/tasks/LJ-1-318/`: this ruling,
  `ProbeLJ1318A.agda`, `ProbeLJ1318B.agda`. `src/`, `dev/`,
  `AGENTS.md` and the other task directories are untouched.
- Sibling task directories were read and re-run, never edited.
- No commit, no push, no `git checkout .`, no `git stash`, no
  `git reset --hard`, no `git clean`, no `make check`.
- One Agda process at a time under the C-12 cap, counted with the
  brief's command before every invocation.
- `lint-prose.py --check` exits 0 on this ruling. `lint-agda.py --check`
  exits 0 on both probes.
