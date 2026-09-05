# LJ-1.260: land the numeral premise in `TFacts`, `LFacts` and `UFacts`

tier: pi (deepseek-subagent-mode), **model `deepseek-v4-pro`**: this task runs
Agda and holds a slot. **The clock selected the mode.** **THIS TASK EDITS
MASTERS. It is a BUILD, not a probe.**

## GOAL

**`[LJ-1.257]` built all four `envInK-*` and `someEnv`, exit 0, WITH a premise
the delivered records do not carry.** **Add it.**

```agda
∥ Σ[ n ∈ ℕ ] (fst ar ≡ # n) ∥₁
```

**Three records carry the four fields, so all three change:**

| record | at | fields |
|---|---|---|
| `TFacts` | `src/L/Condensation/TwelveAgree.lagda.md:216-244` | all four |
| `LFacts` | `src/L/Condensation/LowerAgree.lagda.md:158-170` | `envInK-mem`, `envInK-neg`, `envInK-imp` |
| `UFacts` | `src/L/Condensation/UpperAgree.lagda.md:158-170` | `envInK-neg`, `envInK-top`, `envInK-imp` |

## WHY IT COSTS THE CONSUMERS NOTHING, and the MASTER says so itself

**`src/L/Condensation/TwelveAgree.lagda.md:298-301`, in the tree's own words:**

> The restriction costs the consumers nothing, because the arity at every
> consuming site IS a numeral: `codesK` gives the code's shape, `arityNumAtL`
> (`L.Coding.CodeSet`) says its arity component is a numeral, and `pr-inj`
> closes both into `fst ar ≡ # n`.

**I re-derived that comment and `codesK` is at `TwelveAgree.lagda.md:162`.**
**But a comment is a CLAIM. C-44: it is unchecked until you check it.** **If a
site cannot discharge the premise, that site is the finding and you stop
there.**

## THE CONSUMERS, all named by `[LJ-1.257]` and all in `src/`

- **`AbstractFrame`** (`TwelveAgree.lagda.md:337-338`), the only `tf : TFacts`
  consumer: pass-through, re-typecheck only.
- **`LowerAgree`** (`LowerAgree.lagda.md:226`) forwards three fields.
  **`UpperAgree`** (`UpperAgree.lagda.md:213`) forwards three.
- **Eleven row modules in `src/L/Condensation.lagda.md`**: `MemAgree` (`:4420`),
  `EqAgree` (`:5358`), `ImpAgree` (`:5270`), `NegAgree` (`:3763`), `TopAgree`
  (`:3684`), `ExistAgree` (`:3980`), `ForallAgree` (`:3872`), `AllInAgree`
  (`:5029`), `ExInAgree` (`:5153`), `ClauseAgree` (`:4158`).

**Every one already takes `codesK`.**

**Price, INFERRED by `[LJ-1.257]`: about 40 to 60 lines of mechanical edits and
NO new proof.** **`envInK-gen` is 12 lines and MEASURED.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT LANDS AND EVERY MASTER IS GREEN.** Report the lines changed per file and
  the seconds. **Then step 6's four `envInK-*` are supplied in the delivered
  tree.** STOP.
- **A SITE CANNOT DISCHARGE THE PREMISE.** **Name it at `file:line` and STOP.**
  **Do not invent a hypothesis to get past it.** **That site refutes the
  master's own comment and it is worth more than the landing.**
- **MATERIALLY OVER 60 LINES.** Report the figure. **`[LJ-1.257]` INFERRED the
  40 to 60 and never ran the change.**
- **A MASTER GOES RED AND STAYS RED.** **Revert your own edits to that file,
  report the term, and leave the tree GREEN.** **A red master is worse than an
  unlanded change.**
- **A WALL.** **A single `agda` invocation past 20 MINUTES is a wall**:
  interrupt, report the ELAPSED SECONDS, bisect. **`src/L/Condensation.lagda.md`
  is a large master; expect a long check and report it.**

## WHAT YOU MAY AND MAY NOT TOUCH

**YOU MAY EDIT:** `src/L/Condensation/TwelveAgree.lagda.md`,
`src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md`, and
`src/L/Condensation.lagda.md`.

**YOU MAY NOT:**

- **Never `src/Everything.lagda.md`.** **The orchestrator wires it.**
- **Do not touch `src/L/Choice/Name.lagda.md`.** DD23 blocks a pending change.
- **Do not change any mathematical prose** (DD23). **The `<!--en--> <!--zh-->
  <!--ja-->` marker grammar binds every master you touch: if a change makes a
  prose sentence false, STOP and report it rather than rewriting it.**
- **Do not touch `agents/tasks/LJ-1-259/`.** A sibling is live there.
- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Leave the working tree as your report
  describes it.**
- **Do not run `make check`**; the orchestrator runs it. **Typecheck the
  individual masters you touch.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.**
- **Create your report file in your FIRST five minutes (C-22).**

## SEVEN RULES THIS CHAIN EARNED

**C-40 IS THIS TASK'S CENTRE: verify the CONSUMERS of a changed record, never
the record alone.** **You are changing three delivered records with fourteen
named consumers.**

**CHECK THE TREE BEFORE YOU CALL SOMETHING ABSENT.** **Three times this
week.**

**A PROHIBITION IN A BRIEF CAN BE THE WHOLE BLOCKER** (C-39). **Mine blocked
these five fields for a whole dispatch.**

**FIVE COPIES OF ONE PROOF ARE ONE OBSERVATION.**

**A FAILED SUBSTITUTION IS NOT A PROOF OF IMPOSSIBILITY** (C-36).

**`exit 0` IS NOT A SUPPLY** (C-45).

**C-44: the master's comment at `:298-301` is a CLAIM. Check it.**

## THE CLASSIFICATION I WANT ON EVERY NEGATIVE

**MEASURED or INFERRED, in those words.**

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker.

**`[LJ-1.258]` MEASURED that none of its fifteen fields is per-tower and that
all are stated over `(K, Ktr)`.** **The numeral premise names no tower
either.** **Say whether the three records stay tower-neutral after the
change**, because `LFacts` and `UFacts` are the two halves the J tower would
re-instantiate.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-257/lj-1.257-report.md`**, read WHOLE. **Its section 4
  is your specification, consumer by consumer.**
- `agents/tasks/LJ-1-255/` and `LJ-1-258/`: the fields already green, so you
  know what the premise buys.
- `agents/tasks/LJ-1-173/` around `:843-846`: the cure table's row 1 defect
  that put `ar ∈ K` where the numeral belonged.
- **`src/L/Condensation/TwelveAgree.lagda.md:162`, `:216-244`, `:298-301`,
  `:337-338`: read the source, never a report about it.**
- **`archive/dev/TASKS-archived.md`.** **Take SHAPE from the archive, never a
  claim.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**Say in one line whether the numeral restriction has any counterpart in the
literature or is purely an artifact of the coding.** Return a **LITERATURE
USED** section.

## SCOPE (read)

`agents/tasks/LJ-1-257/lj-1.257-report.md` FIRST, whole.

## SCOPE (write)

`src/L/Condensation/TwelveAgree.lagda.md`,
`src/L/Condensation/LowerAgree.lagda.md`,
`src/L/Condensation/UpperAgree.lagda.md`, `src/L/Condensation.lagda.md`, and
`agents/tasks/LJ-1-260/` for your report.

## MANDATORY RULES

Run `.venv/bin/python scripts/rules.py --for build` and read every statement.
**The tool now prints `Full entry: dev/LESSONS.md:<line>` for every rule and
says THIS IS AN EXCERPT when it truncated. OPEN the full entry for any law you
act on.**

**The `build` bundle, which the dispatch gate refused this brief for missing
once. Read every statement.**

- **P-h.** Definability walks are module-parameterized, never
  function-parameterized. **You are adding a premise to three RECORDS; keep the
  parameterization where the master already has it.**
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l.** A statement may be ABOUT a concrete stage without dragging that
  stage's PRESENTATION into its type.
- **P-m.** The check-cost rate is a content-class certificate, and
  instantiation is the expensive class. **Eleven row modules re-instantiate
  after your change; report their seconds.**
- **P-n.** Satisfaction content at a concrete carrier is a payable floor, not a
  defect.
- **R-35.** Union representations are meta-poisoned; state memberships at small
  indices.
- **R-38.** A consumer's alias of a transparent imported operation is a birth
  site. **Fourteen consumers touch this change; watch for an alias.**
- **R-40.** A deep successor-chain membership witness normalizes
  super-linearly; climb by small closures.
- **I-5.** Inner-world truncation branches carry written types. **The premise
  IS a truncation, so its branches carry written types.**
- **C-12.** One agda process, the cap never raised.
- **D-10.** Price the truth of a recorded residue before pricing its proof.
- **C-22.** Write your deliverable incrementally.

**And the ones this chain earned:**

- **C-40.** **Verify the CONSUMERS, never the record alone. The centre.**
- **C-44.** A claim is unchecked until you check it.
- **C-45.** Audit the instantiation, never the telescope.
- **D-1.** The abort criterion is fixed above.
- **C-36, C-38, C-39, C-42. R-34. P-t, P-y. DD0, DD8, DD18, DD23, DD24, D-26,
  D-29, D-30.**

## CONSTRAINTS

- Count with `.venv/bin/python scripts/ledger.py`.
- Run `scripts/lint-prose.py --check` and `scripts/lint-agda.py --check` on
  every file you touch.
- DD23 freezes mathematical prose.
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

**Lead with whether every touched master is GREEN and with the lines changed
per file.** Then each of the fourteen consumers and how it discharged the
premise. Then any site that could not. Then the seconds per master with load.
Then whether the three records stayed tower-neutral. **Mark every negative
MEASURED or INFERRED.**
