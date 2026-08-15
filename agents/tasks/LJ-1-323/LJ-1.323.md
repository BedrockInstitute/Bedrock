# LJ-1.323: the most natural statement of BOTH trophies, ruled

tier: fable (in-harness-subagent-mode), run through a workflow so the effort
tier is actually set to `max`. `fable` has no entry in `HARNESS_FOR_AGENT` and
`dispatch.py` cannot start it, so in-harness is the only path.

## THE AUTHORIZATION, and read its scope exactly

**The repository owner delegated THIS RULING to you on 2026-08-15, in these
words:**

> **I delegate the judgement to you in full. Whatever is the most natural and
> most elegant primitive statement mathematically. THIS ONCE, you need not be
> bound by the project's current rules. I authorize the orchestrator to change
> the trophy statement according to your ruling. State it so that it is natural
> from BOTH the classical-mathematics angle AND the cubical angle.**

**WHAT THAT LIFTS.** You are NOT bound by: the current text of either trophy;
DD23's freeze on mathematical prose; the route already built; the 470-line
price; what has already been proved; or any project convention about how a
statement is written. **If the natural statement throws away work, say so and
rule for the natural statement.** **The owner asked for the RIGHT statement, not
the cheap one.**

**WHAT IT DOES NOT LIFT, and these are machine safety and record-keeping rather
than mathematical judgement:** C-12's two-Agda-process cap and the 8 GB heap
cap, which protect the machine; never commit and never push; and write only in
your own directory, because the orchestrator lands. **Say if you think any of
these blocked you.**

## THE QUESTION

**Write the statement of `L ⊨ AC` and the statement of `L ⊨ GCH` as they SHOULD
be written, in this development, in cubical Agda.**

**Then rule: is the delivered statement of each one right, and if not, what
exactly replaces it?**

## THE TEST YOUR STATEMENT MUST PASS, and it is a DOUBLE test

**The owner emphasised this above everything else, so it is the acceptance
criterion:**

1. **A set theorist who has never read a line of type theory reads your
   statement and says: yes, that is AC in L, and that is GCH in L.**
2. **A cubical type theorist who has never seen this project reads it and says:
   yes, that is how you say it here.**

**If EITHER reader has to ask「why is it written like that?」, the statement
fails.** **Show your statement to both, in your report, in their own
vocabularies.** **A statement that is natural in one lens and awkward in the
other is the failure mode this task exists to prevent.**

## THE FIVE TENSIONS TO RESOLVE, and they are the substance

**You may find more. These are the ones already measured.**

### 1. TRUNCATED OR DATA, and the delivered statement is inconsistent with itself

`src/L/GCH.lagda.md`, one file, two lines apart in spirit:

```agda
SqShape =                                       -- :44-47, the HYPOTHESIS
  (α : S) → IsOrd (fst α) → (⟨ fst α ∈ˢ ω ⟩ → Empty.⊥)
          → (⟪ fst α ⟫ × ⟪ fst α ⟫) ↪ ⟪ fst α ⟫          -- bare ↪, DATA

GCHStatement zf =                               -- :77-87, the CONCLUSION
  (sq : SqShape) → (κ : S) → IsCardinalL κ
  → (⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)
  → ∥ Σ[ δ ∈ S ] ( SuccCardL δ κ
       × (⟪ fst (𝒫 κ) ⟫ ↪ ⟪ fst δ ⟫) ) ∥₁               -- ∥ ∥₁, TRUNCATED
```

**The hypothesis demands data and the conclusion delivers a proposition.**

**`[LJ-1.316]` measured why this matters, from the sources:** the classical
conclusion at the square-law step is a cardinal EQUATION, and **a cardinal
inequality IS a truncated existence of an injection by the HoTT Book's own
Definition 10.2.7.** **So no classical source ever faces an untruncation
problem here. The data demand is this project's own choice**, and it is what
produced a proposed new axiom that a later probe had to talk the project out
of.

**RULE ON IT. And say what the right general policy is**, not just the local
fix: **when does a statement in this development say `∥ A ↪ B ∥₁` and when does
it say `A ↪ B`?**

### 2. IS `sq` A HYPOTHESIS AT ALL?

**A theorem with an undischarged hypothesis is a CONDITIONAL theorem.** Devlin
proves the square law as a LEMMA on the way to the GCH; it is not a caveat on
his theorem.

**So: does `SqShape` belong in the statement of the trophy, or does it belong
in the proof?** **If it belongs in the proof, the trophy currently claims less
than it should, and the honest statement has no `sq` in it.** **Rule.**

### 3. WHICH CARDINAL FACE AT κ, and this half is genuinely undecidable inside

`IsCardinalL` at `src/L/Cardinal.lagda.md:230-233` refutes **CODED** injections:
`InjCode`'s `F` ranges over the L-carrier `S`. **The ambient `IsCardinal` is
about ambient functions.** The only crossing device is `Small` at
`src/L/Coding/Injection.lagda.md:123` and **it runs code to ambient; the reverse
has no term.** `amb→code` proves `IsCardinal (fst κ) → IsCardinalL κ` and
nothing proves the converse.

**AND THE MISSING DIRECTION IS INDEPENDENT** (`[LJ-1.300]`): `AmbientToCode` is
TRUE when the ambient universe satisfies V=L and FALSE under a Levy collapse.
**No proof and no countermodel can settle it inside this development.**

**So this is not a gap to fill. It is a choice the STATEMENT makes.** **Which
face does「L models GCH」mean?** **Answer it from the mathematics: which face
makes the sentence say what a set theorist means by it.** **Do not answer it
from which face is cheaper to prove.**

**And note the measurement that removed the temptation:** `[LJ-1.314]` measured
that the ambient face buys nothing toward `SqShape`, because two delivered
consumers need the law at every δ below the site and most are not cardinals.
**So no face is the cheap one now. Rule on meaning alone.**

### 4. A BOUND OR AN EQUALITY?

**GCH classically is `2^κ = κ⁺`, an EQUALITY.** The delivered statement gives
one direction, `⟪ 𝒫 κ ⟫ ↪ ⟪ δ ⟫`, a bound.

**Is the other direction free here?** Classically `κ⁺ ≤ 2^κ` follows from
Cantor and the definition of the successor cardinal. **Check whether it is free
in this development.** **If it is, say whether the natural statement names the
equality anyway, because a set theorist reading「GCH」expects `2^κ = κ⁺` and
not a one-sided bound.**

### 5. BOTH TROPHIES, ONE HAND

**`L ⊨ AC` is delivered as `L⊨ZFC` at `src/L/Model.lagda.md:99`, a RECORD
inhabitant**: `record { zf = L⊨ZF ; hasChoice = hasChoiceL L⊨ZF }`. **`L ⊨ GCH`
is a Π-type with hypotheses.** **Those are two different literary forms for two
halves of one result.**

**Rule on whether they should match, and if so, in which direction.** **DD4's
spirit is that the two proofs share; this task asks whether the two STATEMENTS
should read as siblings.** **A reader meeting both should not think they came
from two projects.**

## WHAT YOU MUST DELIVER

1. **THE STATEMENTS, as exact Agda text**, ready to paste. Both trophies.
2. **THE TWO READINGS.** Each statement rendered in a set theorist's prose and
   in a cubical type theorist's prose, so the double test is checkable rather
   than asserted.
3. **THE DIFF.** What changes against the delivered text, line by line.
4. **THE DAMAGE.** What proofs break, what has to be re-proved, and roughly what
   it costs. **Name it honestly and rule for the right statement anyway if that
   is your judgement.** **Say plainly if you are proposing to discard delivered
   work.**
5. **THE POLICY.** The general rule this development should follow for
   truncation in statements, so the next statement does not need a ruling.
6. **WHAT WOULD REVERSE THE RULING**, as an observable condition.

**TYPECHECK YOUR PROPOSED STATEMENTS if you can.** A statement that does not
typecheck is a sketch. **Count the Agda slots first** (see below) and write the
candidates in your own directory.

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE DELIVERED STATEMENTS ARE ALREADY RIGHT.** **A real outcome and you must
  be willing to reach it.** Then say why each tension above is a non-issue, and
  the project stops re-opening them. STOP.
- **ONE CHANGES, THE OTHER DOES NOT.** Rule on each separately and say why the
  asymmetry is right.
- **BOTH CHANGE.** Then give both, and the damage.
- **THE TWO LENSES GENUINELY CONFLICT.** **If no single statement is natural to
  both readers, say so, give the best compromise, and name exactly what is
  sacrificed to which reader.** **That is a real answer and it is the one thing
  the owner asked you to avoid papering over.**

## OPERATIONAL CONSTRAINTS

- **Write ONLY in `agents/tasks/LJ-1-323/`.** **Do not edit `src/`.** **The
  orchestrator lands the statement change; the owner authorized that
  explicitly.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. **`ps aux | grep -c '[a]gda '` OVER-COUNTS (the
  bash wrapper) and `grep -c 'libexec.*bin/agda'` over-counts too (the grep).
  MEASURED 2026-08-15.** Use:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
- **`GHCRTS="-A64m -I0 -M8g"`, ONE process, cap NEVER raised.** Report load
  beside every absolute figure. A single invocation past 30 minutes is a wall.
- **Create `agents/tasks/LJ-1-323/lj-1.323-ruling.md` in your FIRST five
  minutes** and fill it incrementally.
- Evidence is `file:line` or a citation locator. **No em dash in any language.**
  Mark every negative **MEASURED** or **INFERRED**.
- **Write your ruling in ASD-STE100**, because its reader is the orchestrator.
  **The two READINGS in deliverable 2 are exempt: there, write the natural prose
  of each field, because their whole purpose is to sound native to a
  mathematician and to a type theorist.**

## THE EVIDENCE, all of it, and read what bears

- **`src/L/GCH.lagda.md`**, the GCH statement, WHOLE. **`src/L/Model.lagda.md:92-100`**,
  the AC statement.
- **`src/L/Cardinal.lagda.md:230-233`**, `IsCardinalL`, and
  `src/L/Coding/Injection.lagda.md:123`, `Small`.
- **`dev/PLAN.md:410-431`**, the cardinal-face fork as the project registered it.
- **`dev/literature/truncation-and-selection.md`**, landed tonight: how each
  literature picks a witness, the HoTT Book on cardinal inequality as a
  truncated existence, and Kraus et al Theorem 16.
- **`dev/literature/level-formula-slot-roles.md`**, landed tonight: four
  authors on how the level formula binds and frees.
- **`dev/literature/devlin-II5.md`**, the II.5 digest, for how Devlin states
  the GCH in L.
- **`agents/tasks/LJ-1-316/lj-1.316-report.md`**, the survey that found the data
  demand is self-inflicted. **`agents/tasks/LJ-1-314/lj-1.314-report.md`**, the
  ambient-face measurement. **`agents/tasks/LJ-1-319/lj-1.319-ruling.md`
  section 4**, which escalated both halves to the owner.
- **`archive/dev/DECISIONS-archived.md` and `archive/dev/TASKS-archived.md`**,
  taking SHAPE and never a claim: the retired route stated these theorems too.
  **Say what would not transfer.**

**Return an ARCHIVE USED section and a LITERATURE USED section, each naming one
line read per file, with WHY NOT for anything you chose not to read.**

## THE ONE RULE THAT STILL BINDS YOUR JUDGEMENT

**A claim is a measurement until you check it.** Every number and every reading
in this brief is some other agent's or mine. **Re-derive what you rely on.**
**That rule is not a project convention; it is what makes a ruling worth
having.**

## RETURN

**Lead with ONE sentence per trophy: does its statement change, and to what.**
Then the exact Agda text of both. Then the two readings, one per lens, in their
own prose. Then the diff, the damage and the cost. Then the truncation policy.
Then what would reverse it. **Mark every negative MEASURED or INFERRED.**
