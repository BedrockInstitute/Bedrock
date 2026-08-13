# LJ-1.5: the condensation lemma, block 1, on the erase route

tier: codex (default)

## GOAL

Build condensation's first block as a MASTER, on the erase route. **The gate is
GO and this is funded.** Land it or refuse with a measurement.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## THE GATE IS OPEN, and here is exactly how open

`[LJ-1.31]` made `consAtL` constant-free (committed, `5aa4bd6`). That cure
opened two routes. **I measured both cold myself, one process, quiet machine:**

| probe | cold user s | code lines | rate | against |
|---|---:|---:|---:|---|
| `src/ProbeLJ127.agda`, the placement route | 19.86 | 283 | **0.0702** | 0.100 NO-GO line: GO |
| `src/ProbeDD25E.agda`, **the erase route** | 2.87 | 251 | **0.0114** | DD24's 0.013193 bar: GO |

**BUILD THE ERASE ROUTE.** It is 6.2x cheaper and it is the only one under
DD24's bar. The placement route passes the gate but would spend the GCH side's
whole seconds budget.

## YOUR STARTING POINT IS A GREEN PROBE, and this is unusual

**`src/ProbeDD25E.agda` is GREEN and it already carries the block.**
`[LJ-1.27-R]` wrote it, `[LJ-1.31]`'s cure fixed its one failing line, and
`[LJ-1.32-R]` verified declaration by declaration that it carries the same
eleven obligations as the gate probe: the whole `Clause` module, both decodes,
`σL-transfer`, `σL-up`, `cert-transfer` and both rides. **Nothing is dropped.**

**Re-derive it into a master. Do NOT copy a probe into a master** (D-1). A
probe is a residue; verify each obligation as you lift it (D-10).

## THE MECHANISM, so you do not re-derive it

The clause reaches the parameter-free axis through the DELIVERED `erase`, with
**no placement anywhere**:

- `erase : (φ : Formula K n) → countFo φ ≡ 0 → Formula (⊥* {ℓ}) n`
  (`src/FOL/Count.lagda.md:598-611`)
- `erase-inv : mapFo Empty.rec* (erase φ p) ≡ φ` (`:617-637`)

Then `σL = embed (erase φ refl)`, and `erase-inv` gives `σL ≡ φ` as syntax. The
transfer is two syntactic `cong`s plus one `abs₀` at the original clause.

**P-u is the law this obeys, and it is why placement is banned here:** a Levy
witness travels along a relabelling for free and does not travel along a
placement at all. **Certify BEFORE you place.** `[LJ-1.32]` measured the
placement wall flat at 8 GB across constant counts 0, 1, 2 and 5, so the cost
tracks the formula TREE and no constant-count trick escapes it.

**If you find yourself needing `absFo` or a placed `Δ₀`, STOP and report it.**
That is the walling shape and it is not a matter of trying harder.

## SCOPE, and keep it to ONE block

`[LJ-1.26]` prices route A at about 3.3k lines over eight components
(`_build/lj-1.12-report.md:20-49`). **You are building the FIRST block only:**
the clause, its two-way decode at the class carrier, its certificate, and the
transfer. That is what `ProbeDD25E` carries.

**Do not attempt the twelve-clause table, the step and graph stack, the
iso-invariance or the limit case.** Say in the return what the next block needs
and what it would cost.

**Report the rate for what you land.** DD24 gates at 0.013193, module caliber.
`ProbeDD25E` measures 0.0114 at probe scale; a master pays a module-load floor,
so expect movement and say which way.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

`[LJ-1.26]` split condensation into ONE template frame plus TWO per-tower
certificates. `[LJ-1.27-R]` found the Def certificate keys on the defining
SYNTAX while the J tower's stage carries generation data, so the J certificate
is structural and avoids the syntax entirely (D-26).

**So say which side each thing you write falls on**, and **parameterize the
MODULE** (P-h) so the template half is instantiable. **The erase route itself
is template**: it is a fact about constant-free formulas, not about `L`.

## THE THRESHOLD

DD24 gates at **0.013193 s per line**, module caliber. The GCH side's whole
seconds budget is **99.6 to 147.7 s** over a PROJECTED 7,553 to 11,197 lines
(`dev/ledger.toml`).

**C-31: a budget from a projected size is divided by the PROJECTED size, never
by today's.** The per-module flag is ADVICE; the aggregate is the judgment. So
report your rate and do NOT declare a failure from one module's number.

## LITERATURE (DD18)

- **`dev/literature/devlin-II5.md`, sections 2.1 to 2.8, Step C.** Level-hood
  at Σ₁ strength with a Σ₀ matrix, the witness inside the carrier, and the
  bounded Def-step description.
- `_build/literature/dev2.txt:1369-1388` for 5.5 and 5.6 themselves.
- The errata do NOT cover Chapter II section 5. `[LJ-1.14]` verified it. **Do
  not re-check it.**

Return a **LITERATURE USED** section, with WHY NOT for anything skipped.

## ARCHIVE (DD18)

**Read these documents WHOLE. C-32 was admitted today because a brief of mine
named a SECTION and the decisive probe was in another one.**

- **`src/ProbeDD25E.agda`**, green, your starting point.
- **`_build/lj-1.32-review.md`**, which found the gate open and verified the
  block's obligations.
- **`_build/lj-1.27-review.md`**, which wrote the block and closed the
  placement route.
- `_build/lj-1.27-report.md`, `_build/lj-1.29-report.md`,
  `_build/lj-1.31-report.md`, `_build/lj-1.32-report.md`.
- `_build/lj-1.28-report.md`, which found the equivalence legs RIDE the
  delivered graph theorems, with each at `file:line`.
- `archive/rud-route/src/L/Condensation.lagda.md`, 514 lines. **Its target is
  classically FALSE (`[LJ-1.11]`), so read it for SHAPE and never for a
  price.**
- `dev/LESSONS.md` is NOT archived and still binds.

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-l.** No stage presentation in a type that does not need one.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **P-u.** Certify BEFORE you place. **This block exists because of it.**
- **R-35, R-38**: sealing and opacity. **Do not unseal.**
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process.
- **C-22.** Write the deliverable incrementally.
- **C-31.** A budget from a projected size is divided by the projected size.
- **C-32.** A cure invalidates downstream measurements. **The cure landed
  today, so re-verify any figure you take from a report written before it.**
- **D-10.** Every figure in this brief is a residue. Re-verify.

## SCOPE (read)

`src/ProbeDD25E.agda` FIRST, then `_build/lj-1.32-review.md`, then
`src/FOL/Count.lagda.md` at the named lines, then `src/L/Hierarchy.lagda.md`.

## SCOPE (write)

**At most ONE new master under `src/L/`**, and `_build/lj-1.5-report.md`. Probe
files `src/ProbeLJ15*.agda` if you need them. **Never
`src/Everything.lagda.md`**: I wire the catalog after auditing, and the gate
has refused a commit for exactly that.

## CONSTRAINTS

- **Never commit and never push.**
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** Revert by exact path only.
- **Typecheck your master AND every consumer.** Do NOT run `make check`.
- **Interfaces live in `_build/2.8.0/agda/src/`, NOT beside the source.**
  Deleting a `.agdai` next to a `.agda` removes nothing and silently turns a
  cold measurement into a warm read. I made that mistake and C-32 records it.
- **Count with `python3 scripts/ledger.py`'s caliber.** DD26 excludes the two
  catalogs.
- **Report cold seconds and the RATE per file**, noise rule: under 0.5 s or 5
  percent, whichever is larger, is flat.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS.**
- **The machine is quiet and both Agda slots are yours.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.5-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: delivered with lines and rate, or refused with
   a measurement.
2. **DID YOU NEED A PLACEMENT ANYWHERE?** Answer first after the verdict.
3. **THE ELEVEN OBLIGATIONS**: which landed, and any that did not.
4. **THE NUMBER**: in-fence lines, ledger caliber.
5. **SECONDS AND RATE**, against 0.013193 and with C-31's aggregate framing.
6. **WHAT THE NEXT BLOCK NEEDS**, and what it would cost.
7. **DD4**: template or per-tower, per piece, and what the J tower gets.
8. **LITERATURE USED.** 9. **ARCHIVE USED.** 10. **WHAT I AM NOT SURE OF.**
