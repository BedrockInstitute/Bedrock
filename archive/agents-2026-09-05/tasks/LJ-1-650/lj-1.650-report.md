# LJ-1.650 report: cover's coded covering ordinal, from the keystone

## HEAD
head_slot: coder
machine: shared
agda_tier: wide
task: LJ-1.650
obligation: agents/tasks/LJ-1-650/Probe650.agda::coded-cover-from-keystone
verdict: **STOP ON THE OBLIGATION. The keystone points the WRONG WAY, and
the stop is `review-of-coded-cover.md`. W3 is a GO and it delivered the
term the whole residue was waiting for.**

The obligation reads `missing` (`runs/meter-obligation.out`,
`1 UNRESOLVED of 1`, `probe_red=False`: the probe is green and the name is
absent, not broken). Eighteen other names are green
(`runs/meter-names.out`, `0 UNRESOLVED of 18`).

**READ THESE FOUR SENTENCES BEFORE YOU QUEUE ANYTHING.**

1. **`[LJ-1.646]` IS NOT CLAUSE (ii)'s KEYSTONE.** `lset-code-ord` maps an
   ORDINAL code to a LEVEL code. `CodedCover` maps ANY code to an ORDINAL
   code that covers it. Agda names the mismatch in its own words twice
   (`runs/nokey-1.out`, `runs/nokey-2.out`), and the second run names the
   fact the ordinality slot really demands: `IsOrd (Lset α)`.
2. **THE TREE WAS MISSING ONE TERM, AND IT IS NOW BUILT.** `skolemCode`
   (`Probe650.agda:118-149`) returns the Skolem witness AS A CODE and NOT
   under a truncation. `L.Hull`'s `closed` (`src/L/Hull.lagda.md:120-142`)
   proves the same fact and discards the code, and `CodedCover` is
   untruncated, so `closed` could never serve it.
3. **`CodedCover` AT AN ORDINAL VALUE IS NOW FREE**
   (`coded-cover-at-ordinal`, `Probe650.agda:235-260`): unconditional, no
   keystone, no level formula. The whole residue of clause (ii) is at
   NON-ordinal values.
4. **AND THE RESIDUE CLOSES FROM ONE FORMULA**
   (`coded-cover-from-level`, `Probe650.agda:385-386`). That formula is
   NEARER to `CodedCover` than to `[LJ-1.646]`, so the queue plans the
   expensive one first. Section 5 below is that correction.

Written as a skeleton before any Agda beyond the floor and filled as each
answer landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-650/`. Agda ran under the caliber the program set on
this pane, `GHCRTS="-A64m -I0 -M2g"`, the WIDE tier, ONE Agda process at a
time. I did not set `GHCRTS`. Nothing is postulated, every delivered file
carries `--safe`, the delivered probe carries no hole, and nothing lands
in `src/`. The probe is a raw `.agda` file, so it carries no ` ```agda `
fence, counts 0 in-fence lines, and the ratio bar cannot fire on it.

**EVERY NUMBER BELOW IS MEASURED WITH A WARM `src/` INTERFACE CACHE**
(708 `.agdai` files under `_build/` at the start of the task, 722 at the
end). No number here is a cold-cache number, and this report does not
bound one.

## 1. THE FLOOR, AND THE WALL IT FOUND

**A HEAP WALL WAS MET, AND IT WAS ROUTED AROUND IN THE SAME DISPATCH**
(coder clause, owner 2026-08-23). It is reported here as a FRAME
measurement, not as a finding about any term: no delivered term walls.

The honest way to take a predecessor's type is to IMPORT it, so the first
floor did. `import LJ-1-595.Probe595` pulls the 544/550/558/564/570/578
chain, and it **EXHAUSTS the wide caliber's heap on the frame ALONE**,
with no term of this task's own in the file:

- `runs/FLOOR-IMPORT595.agda.txt`, `runs/floor-1.out`: `EXIT=251`,
  `agda: Heap exhausted; Current maximum heap size is 2147483648 bytes`,
  after 63.18 s at 1,911,226,368 bytes. It died in
  `Checking LJ-1-570.Probe570`.

**Restructured: `src/` only, and the two predecessor types RESTATED
VERBATIM, each cited at the line it was read.** The new frame is
`runs/Floor650.agda`, `runs/floor-2.out`, exit 0 in 3.67 s at 740,179,968
bytes. **63.18 s and a wall became 3.67 s and a green file, and the
restructuring is the whole difference.**

**THIS IS A DATUM ABOUT CROSS-TASK IMPORTS, NOT ABOUT `[LJ-1.595]`.**
`[LJ-1.595]` itself imported `LJ-1-578.Probe578` and closed green
(`agents/tasks/LJ-1-595/runs/p-final.out`, 8.68 s at 1,002,045,440 bytes),
but that was BEFORE the 2026-08-23 caliber ruling took the wide tier from
`-M8g` to `-M2g`; its own first run peaked at 2,527,182,848 bytes
(`agents/tasks/LJ-1-595/runs/p-1.out`), which is 118 % of today's cap.
**Any task that plans to import a probe two or more links down the
LJ chain should price the frame first.**

## 2. W3: GO, AND THE ESTIMATE WAS HIGH

The brief asked "whether the covering ordinal's code needs `Lset` named at
the STAGE rather than at a hull code", priced 70 to 150 lines, and named
the decisive miniature's home. **The answer is that the question had a
prior: the tree had no way to name ANY code from a formula without
truncating, so neither reading could be tested.**

`runs/W3.agda` is that miniature, typechecked ALONE first
(`runs/w3-1.out`, exit 0 in 3.83 s at 711,327,744 bytes; `runs/w3-final.out`
2.85 s). **It is 63 non-blank non-comment lines with its imports, and the
term itself is 32** (`Probe650.agda:118-149`), against the brief's 70 to
150. The estimate was high because the proof is `closed`'s own, with the
Skolem constant `wit k ψ cs` KEPT instead of discarded; `val-wit`
(`src/L/Hull.lagda.md:105-107`) is what makes the keeping legal.

**AND THE ANSWER TO THE QUESTION AS ASKED IS: THE STAGE.** `skolemCode`
consumes a `Formula Code 1` READ AT THE STAGE'S INNER WORLD, because that
is what `wit` consumes (`src/L/Hull.lagda.md:72-74`: `base` and `wit` are
the only two code constructors, and `wit` takes a formula). A hull-code
reading, which is what `lset-code-ord` is, supplies no formula and
therefore no code.

**IT IS NOT PLUMBING, AND THE CHEAPEST PROOF OF THAT IS `ordinal-code`**
(`Probe650.agda:214-218`): the hull NAMES an ordinal, unconditionally and
untruncated, because `ordFo` is satisfiable at the empty set. No
hypothesis of any kind enters.

## 3. THE OBLIGATION: NOT INHABITED, AND MEASURED TWICE

`review-of-coded-cover.md` is the stop and carries both Agda errors in
full. In one line each:

- **The direct application** (`runs/NO-KEYSTONE-DIRECT.agda.txt`,
  `runs/nokey-1.out`, exit 42): `[UnequalTerms]`, the keystone's
  `IsOrd (val c) → Σ[d] (val d ≡ Lset (val c))` against `CodedCover`'s
  `Σ[d] (IsOrd (val d) × val c ∈ Lset (val d))`.
- **Where the keystone DOES apply** (`runs/NO-KEYSTONE-ORD.agda.txt`,
  `runs/nokey-2.out`, exit 42): restricted to an ordinal-valued code, so
  the keystone's own hypothesis is paid, the ordinality slot demands
  `IsOrd (Lset (fst (Q.T.val c)))`. **That is the fact, named by Agda.**

`keystone-row-at-ordinal` (`Probe650.agda:417-427`) is the whole keystone
route to one row of `CodedCover` with that fact and the matching covering
fact ADDED as hypotheses. It is green, and it is the price of the route.
`coded-cover-at-ordinal` pays the same row with NEITHER.

**I DID NOT PROVE THE OBLIGATION'S TYPE FALSE.** I proved that no term
composes it out of the keystone and the tree, and I measured the two facts
any such term must add. A refutation of the type is a different task.

## 4. WHAT IS DELIVERED, AND WHAT EACH THING COSTS

Every name below is metered green in `runs/meter-names.out`.

| name | line | what it is | hypothesis |
|---|---|---|---|
| `skolemCode` | 118 | coded Skolem witness, untruncated | none |
| `ordinal-code` | 214 | the hull names an ordinal | none |
| `coded-cover-at-ordinal` | 235 | `CodedCover` at an ordinal value | none |
| `cover-in-stage` | 333 | the covering ordinal is free at the stage | none |
| `coded-cover-from-internal` | 289 | `CodedCover` | `InternalCover` |
| `internal-from-level` | 352 | `InternalCover` | `LevelFormula` |
| `coded-cover-from-level` | 385 | `CodedCover` | `LevelFormula` |
| `keystone-output-is-a-level` | 398 | what the keystone IS, as a map | keystone |
| `keystone-applied` | 405 | the keystone is not vacuous | keystone |
| `keystone-row-at-ordinal` | 417 | the keystone route, fully priced | keystone + 2 |

`ord-out`, `ord-in` and `cover-in-stage` are `[LJ-1.595]`'s section 4 and
section 5 re-read at this file. **W2 forbids a second proof of the same
fact without a reason, and the reason is the measured wall in section 1
and nothing else.** Where the import is affordable it should be preferred
and this file says so in its own header.

The probe is 427 lines, 249 non-blank non-comment.
`runs/p-final.out`: exit 0 in 4.60 s at 695,812,096 bytes.

## 5. WHAT THE NEXT BRIEF NEEDS

**5.1 THE QUEUE HAS THE DEPENDENCY BACKWARDS.** `LevelFormula`
(`Probe650.agda:322-328`) is one formula in two variables, sound and
complete for "v is the level indexed by γ" at the stage's inner world. It
is Devlin's own object (`dev/literature/devlin-II5.md:214-217`).

- It reaches **`CodedCover`** with `∃̇` and nothing else
  (`internal-from-level`, `Probe650.agda:352-382`). The consumer binds the
  LEVEL and leaves the INDEX free.
- It reaches **`lset-code-ord`** only through a constant substituted for
  the index, which `[LJ-1.595]` recorded as a renaming it did not price
  (`agents/tasks/LJ-1-595/lj-1.595-report.md:167-169`).

**So `[LJ-1.650]` is CHEAPER from the true keystone than `[LJ-1.646]` is,
and `[LJ-1.646]` does not produce `[LJ-1.650]` at any price.** If one of
the two is to be dispatched first, it is the level formula itself, stated
as `LevelFormula` and not as `lset-code-ord`.

**5.2 THE BINDER DIFFERENCE RECURS ONE LEVEL DOWN.** `[LJ-1.595]` measured
that clause (i) and clause (ii) differ by a BINDER and not by a shape
(`agents/tasks/LJ-1-595/lj-1.595-report.md:154-156`). `lset-code-ord` is
the index-FREE reading and `CodedCover` is the index-BOUND one. **That is
the same difference at the code level, and it is why the trace from
`[LJ-1.595]` to `[LJ-1.646]` misses.** The destination `[LJ-1.595]` named,
"the level formula read at the stage"
(`agents/tasks/LJ-1-595/lj-1.595-report.md:171-179`), is right. The
address is wrong: `lset-code-ord` is a SEMANTIC consequence of that
formula, and `CodedCover` needs the SYNTAX.

**5.3 C-42, AND IT IS NOT THIS TASK'S SCOPE.** A refutation measures the
site it names. This one names ONE site. **It says nothing about how many
other queued tasks take `[LJ-1.646]` as their keystone, and the sweep is
the next action.** Two are already visible without searching:
`[LJ-1.647]`'s `hull-closed-lset` takes it
(`agents/tasks/LJ-1-647/Probe647.agda:165-167`) and `[LJ-1.649]` measured
that the ordinal condition costs a FIFTH fact downstream
(`agents/tasks/LJ-1-649/lj-1.649-report.md:190-197`). Those two are about
whether the keystone is EXPENSIVE. This task is about whether it is the
RIGHT object. **A sweep should ask the second question at every site, not
only the first.**

**5.4 `skolemCode` IS REUSABLE AND SHOULD BE TAKEN, NOT REPROVED.** It is
generic in the formula and spends no fact about `Lset`, no ordinality and
no collapse. Every residue of the form "the hull CONTAINS a code for ..."
now reduces to "there is a formula that selects it", and that is the only
thing left to buy. `[LJ-1.649]` gave the same advice about `pix-closed-op`
(`agents/tasks/LJ-1-649/lj-1.649-report.md:341-346`); this is the second
such tool in three tasks.

**5.5 WHERE `skolemCode` BELONGS IF IT SURVIVES REVIEW.** It is a fact
about `TermAlgebra` and nothing else. Its natural home is beside `closed`,
`src/L/Hull.lagda.md:120`, as the untruncated form `closed` should have
had. **This task does not land it there and makes no claim about the
in-fence price of doing so.**

## 6. HEAP AND TIME, IN FULL

| run | file | exit | wall | peak bytes |
|---|---|---|---|---|
| `floor-1` | `FLOOR-IMPORT595.agda.txt` | 251 (WALL) | 63.18 s | 1,911,226,368 |
| `floor-2` | `runs/Floor650.agda` | 0 | 3.67 s | 740,179,968 |
| `w3-1` | `runs/W3.agda` | 0 | 3.83 s | 711,327,744 |
| `p-1` | `Probe650.agda` (sections 1-7) | 0 | 4.20 s | 658,030,592 |
| `p-2` | `Probe650.agda` (with section 6.5) | 0 | 4.21 s | 695,795,712 |
| `nokey-1` | `NO-KEYSTONE-DIRECT.agda.txt` | 42 | 3.40 s | 610,615,296 |
| `nokey-2` | `NO-KEYSTONE-ORD.agda.txt` | 42 | 3.41 s | 737,591,296 |
| `floor-final` | `runs/Floor650.agda` | 0 | 2.84 s | 709,246,976 |
| `w3-final` | `runs/W3.agda` | 0 | 2.85 s | 703,004,672 |
| `p-final` | `Probe650.agda` | 0 | 4.60 s | 695,812,096 |

**The highest peak of any GREEN run is 740,179,968 bytes, 34 % of the
2,147,483,648-byte wide cap.** The only run that walled is the imported
frame, and it is kept as `.agda.txt` because it cannot typecheck. The caps
I set are wall-clock caps of 900 s enforced by a perl alarm
(`runs/run.sh`), because this macOS has no `timeout` (`[LJ-1.602]`,
`[LJ-1.610]`). No run came near one. **Every `.agda` file under this task
home typechecks**; the three that cannot are named `.agda.txt`, which is
what the brief ordered and what `[LJ-1.636]` and `[LJ-1.643]` each lost a
return to.

**W4.** Nothing was retired and nothing was deleted. No `dev/ARCHIVE.md`
row is owed by this task.

## ARCHIVE USED

- `archive/dev/JOURNAL.md`: **READ.** `archive/dev/JOURNAL.md:328` reads
  "**DD27 landed.** `[LJ-1.23]` re-indexed the hull by `Code`, 372 to 431
  lines at". It is why `Code` is the hull's index type at all, and
  therefore why `CodedCover` is stated over codes rather than over hull
  members. It also records that `hull-closed` "gives the criterion at HULL
  parameters" (`:329`), which is the fact `skolemCode` sharpens: the
  criterion was already at code parameters, only truncated.
- `archive/dev/LJ-dispatch-index.md`: **READ.**
  `archive/dev/LJ-dispatch-index.md:74` reads
  "| LJ-1.16-R | DD25 review of LJ-1.16 | OVERTURN the operative clause | The obstruction is the hull's INDEX TYPE, a LJ-1.3 design choice, not the mathematics. Owner's fork; LJ-1.18 prices it |".
  The same lesson lands again here: this task's obstruction is also a type
  question and not a mathematics question.
- `archive/dev/JOURNAL-archived.md`: **NOT USED.** Its hull material is the
  pre-port survey; `archive/dev/JOURNAL-archived.md:722` reads
  "Levy-class packaging was "optional, 150-400 lines"; the hull is greenfield".
  That is history about a tree that no longer exists. A live document
  carries no history and I did not need one.
- `dev/ARCHIVE.md`: **DECLINED.** It is the register of retired modules.
  This task retires nothing (section 6), so it owes no row and reads none.
- `archive/dev/ORCHESTRATION.md`: **DECLINED.** It is the archived
  operating document, superseded by
  `dev/memos/LJ-4-pod-program-design.md`. Nothing in this task turns on
  how the loop is operated.

## LITERATURE USED

- `dev/literature/truncation-and-selection.md`: **READ, AND IT IS W3's OWN
  DIGEST.** At `dev/literature/truncation-and-selection.md:163` the line is

  > **So the question "can this truncation be lifted" is always the question "does

  and it completes at `:164`, `this type have a weakly constant endomap".`
  The route is named at `:165`:

  > to build one: normalize any witness to the least one.

  **`skolemCode` is exactly that route, and the normalizer is already in the
  tree**: `wit k ψ cs` names the LEAST satisfier under the stage's
  well-order (`src/L/Hull.lagda.md:79-81`), so the endomap is constant by
  construction and the truncation lifts. The digest records Devlin making
  the same move; at `:25` it writes his formula:

  > ψ(v₀) = φ(v₀) ∧ ∀v₁(v₁ <_L v₀ → ¬φ(v₁))

- `dev/literature/devlin-II5.md`: **READ.** At
  `dev/literature/devlin-II5.md:214` the line is

  > 1. Level-hood as Σ₁ with a Σ₀ matrix: there is a Σ₀ formula Φ(z, v, γ) of

  That is `LevelFormula`'s shape, and it is why section 6.5 states it in TWO
  variables rather than three: Devlin's `z` bundles the level sequence, and
  none of this task's consumers reads it. `:219` gives the STAGE reading the
  brief's W3 asked about:

  > v = L_γ iff v ∈ L_α and L_α ⊨ ∃z φ(z, v, γ)

- `dev/literature/digest.md`: **NOT READ.** It is the corpus-wide digest.
  The two files above are its II.5 chapter and its selection chapter at full
  detail, and this task needed only those two.
- `dev/literature/geology.md`: **DECLINED.** Set-theoretic geology bears on
  ground models and the mantle, not on a Skolem hull's codes.
- `dev/literature/terms-2026-08.md`: **DECLINED.** It is a terminology
  file. This task adds no `dev/glossary.toml` entry and proposes none.
