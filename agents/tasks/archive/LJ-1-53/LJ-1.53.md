# LJ-1.53: the three walls of the hull adequacy

tier: codex (default)

## GOAL

`[LJ-1.52]` assembled the chain and located exactly three unbuilt pieces. Build
them, or return the term you could not write for each.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`, clean at
`f7314af`.

## WHAT IS ALREADY ASSEMBLED AND MACHINE-CHECKED

`[LJ-1.52]`'s two probes are green and I have not re-run them; **re-verify them
first** (D-10). The chain
`matrix → graphBndAt → LsetGraphAt → ride-only → w = Lset γ` is fully assembled
at the class carrier. `graph-assembly` (`src/ProbeLJ152B.agda:71-87`) is PROVED
from `StepAgree`, `ApproxAgree` and the site facts.

**So the obligation is no longer "the adequacy". It is three named leaves.**

## THE THREE WALLS

### 1. The `DefBodyB`/`DefBody` leaf adequacy, inside `StepAgree`

The two-way satisfaction transfer between the bounded code-set description and
the machine's `DefBody` at a common environment, under the leg-D site facts.
`[LJ-1.7-R]` recorded that nothing proves it; `[LJ-1.52]` located it as
`StepAgree`'s leaf.

**Try `EraseTransfer` on it.** `src/ProbeDD25H2.agda` instantiates the delivered
`EraseTransfer` at a leaf in 1.56 s, and **it never calls `erase-Δ₀` at all**:
`abs₀` recurses on the Δ₀ WITNESS, not the formula, so the certificate never
crosses `erase`. That route is delivered and green.

### 2. The parameter-to-code relabelling, inside TV/ElemDown

A function `SM → Code` picking a canonical code for each hull member, plus the
satisfaction transfer between the parameter-in-env and the parameter-as-constant
spellings.

**`[LJ-1.52]` names both halves as solved shapes**: the `CodeSelect` least-of
pattern is DELIVERED in `Co`, and the transfer is **P-v's second-spelling
family**, which this file has beaten repeatedly.

### 3. Piece 1, and I am challenging its framing rather than accepting it

`[LJ-1.52]` says piece 1 needs `Lset m ⊆ M` for ordinal `m ∈ M`, which is the
adequacy itself, **and `m ⊆ M`, "hull transitivity, absent because the Skolem
hull is not transitive in general"**.

**That last clause may be answering the wrong question, and I want it tested
rather than assumed.** In Devlin's proof (`_build/literature/dev2.txt:1372-1385`)
the hull is taken **of `L_α ∪ {x}`**, so `L_α ⊆ M` holds BY CONSTRUCTION, and
non-transitivity elsewhere is exactly what the **Mostowski collapse** is applied
to fix. `src/V/Collapse.lagda.md` is delivered with its transitive-fixing clause.

**So ask: does piece 1 need transitivity of `M`, or transitivity of `π M`?**
If the statement can be made after the collapse rather than before it, the wall
may not exist. **If it genuinely needs `M` transitive, say so and show why the
collapse cannot serve.**

**This is a question, not an instruction.** I have been wrong about the
mathematics in this file before, and `dev/LESSONS.md` C-33 and C-37 exist
because my briefs foreclosed answers.

## THE SPELLING RULE THAT DECIDES YOUR SECONDS

**P-v: GIVE A PROOF A NAME AND PASS THE NAME.** Writing the same proof inline as
`refl` in both a type and a body makes the elaborator decide a conversion
between two elaborations of it, and deciding that unfolds the built tree.

| spelling | ms |
|---|---:|
| `refl` inline in the type AND the body | **150,133** |
| the proof NAMED and passed | **220** |
| named in the type, `refl` in the body | 151,402 |

**One named side is not enough.** **If any measurement of yours lands in the
hundred-second range, look here before anywhere else.**

## THE LAWS, each with the ACTION it prescribes (C-37)

- **P-u. CERTIFY BEFORE YOU PLACE**, and the action is to compose the
  absoluteness through the UNPLACED form, which IS `EraseTransfer`. Do NOT build
  the certificate at variable slots: measured SLOWER, 327 ms against 220.
- **P-t.** The class follows the FORMULA, not the carrier.
- **D-30. Price what the CONSUMER needs.** 5.5 uses each piece at ONE shape.
- **C-34. Build the cure or report the wall that stopped you.** "It is a design
  decision" is not a third option. **Broken three times this phase, and a
  review built the deferred cure every time: 0.334 to 0.0108, 0.436 to 0.0072,
  and 150 s to 1.56 s.**
- **C-36.** A failed substitution is not a proof of impossibility. **Write the
  term you could not write**, as `[LJ-1.51]` and `[LJ-1.52]` both did. You may
  strengthen a statement; you may not weaken one.

## ORDER OF ATTACK

**Wall 2 first**: both halves are named as delivered or as a family this file
has beaten. **Wall 1 second**: try `EraseTransfer` before anything else.
**Wall 3 last**, and start by answering the collapse question above rather than
by building.

**A partial with an honest ledger is a full deliverable**, and `[LJ-1.51]`'s and
`[LJ-1.52]`'s ledgers are the model. **This is the fourth dispatch on this one
obligation, so say plainly whether it is converging**: if each dispatch only
renames the wall, that is a finding the owner needs and it outranks any partial
progress.

## WHAT IS SETTLED

- `fin-inj` and `Mext` are DISCHARGED. `sq` has a master; its parameter
  survives on a consumer reshaping that is NOT your task.
- The twelve-row table, block 1, and the row agreements are CLOSED.
- **Δ₀ IS the target.** Delivered `Σ₁`'s only base is `σ-Δ₀`.
- All masters carry ZERO placement. **If you need `absFo` or a placed `Δ₀`,
  STOP and report it.**

## THE THRESHOLD

DD24's live bar is **0.012716**; the GCH aggregate is 0.0118, within. **Do not
use 0.013193.** Report the marginal rate, the whole-file rate and the cone
separately, each from three cold runs in ONE caliber with the spread.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule, two
ends, no metric and no checker, so it is stated in every brief and answered in
every return.

`[LJ-1.52]` found the matrix semantics and the graph agreement are Def-side.
**Say which side each of the three walls falls on**, and whether the collapse
piece is template, since it is about a collapse and a tower rather than about
definability.

## ARCHIVE (DD18)

- **`_build/lj-1.52-report.md`** and its probes `src/ProbeLJ152A.agda`,
  `ProbeLJ152B.agda`, read WHOLE.
- **`_build/lj-1.50-review.md`** with `src/ProbeDD25H2.agda`, the
  `EraseTransfer` route.
- `_build/lj-1.51-report.md` for the hypothesis ledger, and
  `_build/lj-1.7-review.md` for what it recorded about the leaf.
- `archive/rud-route/` for SHAPE only; `[LJ-1.11]` showed its condensation
  target is classically FALSE.
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## LITERATURE (DD18)

- **`_build/literature/dev2.txt:1372-1385`, 5.5's proof.** Read it for wall 3:
  what the hull is taken OF, and what the collapse is applied to.
- `dev/literature/devlin-II5.md` Step C.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## SCOPE (read)

`_build/lj-1.52-report.md` sections 2 and 4 FIRST, then its two probes, then
`src/ProbeDD25H2.agda`, then `src/V/Collapse.lagda.md` for wall 3.

## SCOPE (write)

`src/L/BoundedSubset.lagda.md`, `src/L/Condensation.lagda.md`, and
`src/ProbeLJ153*.agda`. Your report is `_build/lj-1.53-report.md`. **No other
master. Never `src/Everything.lagda.md`.**

## MANDATORY RULES FOR A BUILD

Run `python3 scripts/rules.py --for build` and read every statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-l, P-m, P-n, P-t, P-u, P-v** as above, each with its action.
- **R-35.** State the membership at the SMALL index and climb.
- **R-38.** Seal at the birth site, and do NOT unseal.
- **R-40.** State a membership witness SHALLOW and climb.
- **I-5.** The inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process, cap never
  raised. **A heap exhaustion is a WALL with its seconds; an interruption is
  NOT.**
- **C-22.** Write the deliverable incrementally.
- **C-31, C-32, C-33, C-34, C-35, C-36, C-37.**
- **D-10, D-26, D-29, D-30.**

## CONSTRAINTS

- Never commit, never push, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`.
- Typecheck what you touch and every consumer. Do NOT run `make check`.
- **Run `scripts/check-fences.py --check` before you report anything closed.**
- Count with `scripts/ledger.py`. Run `scripts/lint-prose.py --check` and
  `scripts/lint-agda.py --check`.
- DD23 freezes mathematical prose. Code and its own comments only.
- **Two read-only audits may be running. Check for an Agda process before you
  measure and say what you found.**
- Evidence is `file:line`. Write ASD-STE100.

## RETURN

Write `_build/lj-1.53-report.md` incrementally, skeleton first.

Lead with the ledger: which of the three walls fell, and whether `levelIn` and
`cover` are discharged. **Then answer the convergence question plainly.** Then
wall 3's collapse question. Then the rates with spreads in one caliber, the DD4
split, and what you are not sure of.
