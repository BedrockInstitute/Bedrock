# LJ-1.353: recon. How hard is `L ⊨ Cantor-Bernstein`?

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the head
it gave.** **The owner switched the mode to `pi-subagent-mode` on 2026-08-16,
from this task on and until they say otherwise.**

## THE OWNER'S QUESTION, in their own words

> **We have proved `L ⊨ ZFC`. Is proving `L ⊨ Cantor-Bernstein` hard? Send a
> recon first.**

**This is a RECON. Price it; do not build it.**

## WHY IT IS ASKED NOW

**The restated GCH trophy concludes with TWO coded injections rather than one
equality:**

```agda
  → ∥ Σ[ δ ∈ S ] ( SuccCardL δ κ × InjL (𝒫 κ) δ × InjL δ (𝒫 κ) ) ∥₁
```

`src/L/GCH.lagda.md`. **The owner asked why it is not stated as
`|𝒫(κ)| = κ⁺` in `L`, and the honest answer was that the tree cannot SAY that
today.** **MEASURED by me before writing this brief:**

| what | result |
|---|---|
| `Cantor`, `Bernstein`, `Schroeder` anywhere in `src/` | **ZERO hits** |
| a coded BIJECTION predicate | **does not exist** |
| the coded predicates that DO exist | **`domAt` 82, `svAt` 39, `injAt` 12** |
| ambient antisymmetry on injections | **ZERO hits** |

**So there is no surjectivity predicate. The sentence「some `F` in `L` is a
bijection」has no vocabulary.**

**And the trophy says `L ⊨ …`, so an AMBIENT Cantor-Bernstein would not serve.
It must be a theorem OF `L`.**

## THE QUESTION TO PRICE, in three parts

**1. WHAT DOES `L ⊨ ZFC` ALREADY BUY?** `L⊨ZFC : isZFCModel` at
`src/L/Model.lagda.md:99`, over the record at `src/FOL/ZFModel.lagda.md:419`.
**Cantor-Bernstein is a theorem of ZF, so in principle the model's own axioms
give it.** **The question is what that costs HERE, where every step must be a
satisfaction fact rather than an ambient argument.** **Read the record's fields
and say which the standard proof needs.**

**2. WHAT VOCABULARY IS MISSING?** **A coded surjection or bijection at
minimum.** **Price it against the delivered `InjCode`**, which is a four-part
product of satisfaction facts at `src/L/Cardinal.lagda.md:223-228`. **Say
whether a bijection predicate is `InjCode` plus one conjunct or something
larger.**

**3. WHICH PROOF OF CANTOR-BERNSTEIN.** **The classical proofs differ sharply in
what they need.** **Name the one you would port and why**, and say what it needs
from the ambient side: excluded middle is already a module parameter in this
tree, so using it costs nothing new. **Say whether any of them needs choice,
because this project's first trophy exists to PROVE choice rather than assume
it.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **IT IS CHEAP.** **Say so with a line estimate and its basis** (DD8: one
  number naming a probe, a delivered comparable, or a survey). **Then the owner
  can decide whether to state the trophy as an equality.**
- **IT IS EXPENSIVE.** **Price it and name the widest unmeasured term and the
  smallest decisive miniature that measures it.** **That is DD8's own
  requirement for a build brief.**
- **IT IS BLOCKED.** **If the model record cannot express something the proof
  needs, name it at `file:line`.** **That would be the most valuable answer,
  because it would mean the two-injection form is not a choice but a
  necessity.**
- **SOMETHING ALREADY EXISTS.** **D-10: search before you price.** **Three
  tasks this week found delivered answers that earlier reports called absent,
  and twice the answer was written in English in a sibling chapter.** **My four
  greps above are LITERAL; run a semantic search.**

## WHAT YOU MUST NOT DO

- **DO NOT BUILD IT. This is a recon.** Write only in
  `agents/tasks/LJ-1-353/`. **`src/` is forbidden** (I-5).
- **A MINIATURE IS ALLOWED and encouraged if it settles a price**, but keep it
  small and say what it decides.
- **Do not edit another task directory.**
- **COUNT THE AGDA SLOTS BEFORE EVERY INVOCATION.** C-12 caps this machine at
  TWO and a sibling is live. Use exactly:
  ```sh
  ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l
  ```
  **Both obvious alternatives OVER-COUNT, MEASURED 2026-08-15.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **C-58**: a numeral pattern-match split can exhaust 8 GB where the library
  eliminator is free. **Use the eliminator from the start.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-353/lj-1.353-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `.venv/bin/python scripts/gate/lint-agda.py --check` on what you write. **No
  em dash in any language.**
- Evidence is `file:line`. Write ASD-STE100. Mark every negative **MEASURED**
  or **INFERRED**, in those words.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Ten of my last twenty-four briefs carried a claim an agent measured FALSE.**
**The one at risk: 「the tree has no Cantor-Bernstein」.** **My four greps are
literal string searches, and C-57 was written this week precisely because a
literal search returned the answer at hit 55 of 59 and the reading discarded
it.** **Re-run it semantically. If it is there, say where and this task closes
in an hour.**

## THE RULES

**D-10** is the first move: price the truth of the residue「it is absent」before
pricing its proof. **DD8**: one number, naming its basis, and a build brief
names its widest unmeasured term. **C-57, C-44, C-45, C-42, C-53, C-58, P-l.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**Cantor-Bernstein inside `L` would be pure model-level mathematics naming no
tower**, so it should be written once and inherited by both trophies. **Say
where it belongs so that is true**, and note `dev/ledger.toml:204`: the GCH
closure is read from a STATEMENT whose proof is not wired, so it UNDERSTATES.

## ARCHIVE (DD18)

- **`agents/tasks/LJ-1-323/lj-1.323-ruling.md`, sections 1 and 2.** It wrote the
  current statement and its set-theorist reading ends「so |𝒫(κ)| = κ⁺ in L by
  Cantor-Bernstein」, **which means the READER supplies the step, not the
  statement.**
- **`agents/tasks/LJ-1-325/lj-1.325-report.md`**, which priced the reverse bound
  at about 600 lines **precisely because the tree has no Cantor lemma.**
- **`archive/dev/TASKS-archived.md`**, taking SHAPE and never a claim: the
  retired route had cardinal arithmetic too. **Say what would not transfer.**

**Return an ARCHIVE USED section naming ONE line read per archived file.**

## LITERATURE (DD18)

**`dev/literature/truncation-and-selection.md`**, which carries the HoTT Book's
definition that a cardinal inequality IS a truncated injection, and
**`dev/literature/devlin-II5.md`**. **Say in one line whether Devlin ever needs
Cantor-Bernstein relativized to `L`, or whether he works with the two bounds as
this trophy does.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/FOL/ZFModel.lagda.md:419-445`, the model record whose fields any internal
proof must use, FIRST.

## SCOPE (write)

`agents/tasks/LJ-1-353/` only.

## RETURN

**Lead with ONE word: CHEAP, EXPENSIVE or BLOCKED, and ONE number with its
basis.** Then whether a semantic search finds anything already delivered. Then
which fields of the model record the standard proof needs. Then the missing
vocabulary, priced against `InjCode`. Then which proof you would port and what
it assumes. Then the widest unmeasured term and its miniature. **Mark every
negative MEASURED or INFERRED.**
