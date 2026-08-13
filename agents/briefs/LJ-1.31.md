# LJ-1.31: build the constant-free reader in the coding layer

tier: codex (default)

## GOAL

`[LJ-1.30]` priced this and I reproduced its two decisive numbers myself.
**Land it.** Make `consAtL` constant-free, so a clause reaches the
parameter-free axis through the delivered `erase` with no placement anywhere.

## CWD

`/Users/alsg/Agentic/Bedrock`, on branch `two-tower-bridge`.

## WHY THIS IS FUNDED, and the number is verified rather than reported

`[LJ-1.27]`'s gate went RED at 0.1135 s per line against a 0.10 NO-GO line.
`[LJ-1.27-R]`, a maximum-effort adversarial review, UPHELD that and closed
three of the four ways out by measurement. `[LJ-1.29]` closed the fourth
architecture escape: the crossing CANNOT drop the shared formula.

**This is the only surviving route, and it measures GO.** I re-measured both
probes cold myself, on a quiet machine, one process at a time:

| probe | cold user seconds | code lines | rate |
|---|---:|---:|---:|
| `src/ProbeLJ127.agda`, uncured | **32.12** | 283 | **0.1135** |
| `src/ProbeLJ130A.agda`, cured | **2.95** | 289 | **0.0102** |

DD24's bar is 0.013193 and the gate's GO line is 0.013. **10.9x, and the cured
form is under both.**

## THE FINDING THAT MAKES IT CHEAP, and it killed the risk I had named

I briefed `[LJ-1.30]` that the 16 constants would have to move into environment
slots, widening every consumer's arity, and that four of five transplants in
this tree have failed. **That risk does not bind, and the reason is exact.**

The 16 constants are ALL `con (# 0)`, and **`# 0` IS the empty set
definitionally**: `# zero = ∅` in the ACTIVE cubical library at
`/opt/homebrew/Cellar/agda/2.8.0-r3/share/agda/cubical/Cubical/HITs/CumulativeHierarchy/Constructions.agda`.
I checked the active library myself, not an archived copy.

So "the first component is `# 0`" is "the first component is EMPTY", and
emptiness is Δ₀ with bounded quantifiers only:

```agda
sgl0At k = (∃̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
        ∧̇ (∀̇∈ (var k) (∀̇∈ (var zero) ⊥̇))
```

**The reader becomes constant-free IN PLACE. No arity changes anywhere.**
`consAt0` keeps arity `n`, exactly as `consAt` had.

## THE PRICE `[LJ-1.30]` MEASURED, about 110 lines over TWO masters

| file | change | lines |
|---|---|---:|
| `src/L/Coding/Environment.lagda.md` | three readers and their Δ₀ witnesses | ~15 |
| `src/L/Coding/Environment.lagda.md` | meta machinery: `∅-uniq`, shapes, `prChar∅` | ~75 |
| `src/L/Coding/Environment.lagda.md` | `tag0At-adequate` | ~6 |
| `src/L/Coding/Environment.lagda.md` | `consAt` and `Δ₀-consAt` | ~4 changed |
| `src/L/Coding/Environment.lagda.md` | `consAt-adequate` proof | 3 changed |
| `src/L/Coding/Model.lagda.md` | `bddCons`, `consAtL` | ~8 changed |
| **the six consumer masters** | **NONE** | **0** |

**`src/ProbeLJ130B.agda` holds the whole new adequacy proof at 130 lines and it
typechecks. I ran it myself: exit 0.** Re-derive from it. **Do not copy a probe
into a master** (D-1).

## THE INVARIANT THAT MAKES THE CONSUMERS FREE, and you must protect it

**`consAt-adequate`'s STATEMENT does not change**, because `pr ∅ W` and
`pr (# 0) W` are the same type by `refl`. Its proof swaps three lemma calls.
The six consumers keep their text unchanged.

**If any consumer needs an edit, STOP and report it.** That would mean the
statement moved, and the whole price rests on it not moving. Zero consumer
edits is the deliverable's defining property, not a nice-to-have.

The six consumers, with `[LJ-1.30]`'s use-site counts, all verified by grep of
masters:

`L.Coding.Sat` 11, `L.Coding.Bridge` 17, `L.Coding.Sound` 9,
`L.Coding.Unique` 9, `L.Choice.Internal` 7, `L.Choice.Adequate` 5, plus the
home master `L.Coding.Model` at 20.

**Typecheck every one of them.** The coding layer is delivered and green; this
edit must leave it green.

## ONE CORRECTION `[LJ-1.30]` MADE, so you do not inherit the error

`[LJ-1.27-R]` attributed the 16 constants to "`tagAt` and `shiftPairAt`.
**That attribution is wrong.** All 16 are in `tagAt`: `consAt` calls
`tagAt zero 0 (suc m)` twice and each names `con (# 0)` eight times.
`shiftPairAt` contributes ZERO; it is built from `prAt` and `sucAt` only.
The COUNT was right and the attribution was not.

## DD4, WHICH GOES IN EVERY BRIEF

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends. It has NO metric and no checker by the owner's ruling, so it is
stated in every brief and answered in every return; the repetition is its only
enforcement.

**The coding layer is TEMPLATE content, so both towers get this.** A
constant-free reader is strictly more reusable than one naming coded objects,
because a constant is a commitment to one carrier's encoding.

**Say what the J tower gets.** `[LJ-1.27-R]` found the J certificate is
structural and avoids the syntax entirely (D-26), so it may not use `consAtL`
at all. **If so, say that plainly rather than claiming a shared win that is not
there.**

## LITERATURE (DD18)

**None bears.** This is a representation choice inside this tree's own coding
layer. **Say so in one line naming `dev/literature/` and spend nothing.**

## ARCHIVE (DD18)

- **`_build/lj-1.30-report.md` in full**, and `src/ProbeLJ130A.agda` and
  `src/ProbeLJ130B.agda`. **`130B` is the adequacy proof; it is your model.**
- `_build/lj-1.27-review.md` sections 4 to 6, why the placement route walls.
- `_build/lj-1.29-report.md` section 1, why the shared formula stays.
- `src/FOL/Count.lagda.md:598-611` and `:617-637`, `erase` and `erase-inv`.
- `dev/LESSONS.md` is NOT archived and still binds. **P-u, admitted TODAY, is
  the law this build serves:** a Levy witness travels along a relabelling for
  free and does not travel along a placement at all. Also **P-h, P-l, P-m,
  D-10 and D-26.**

Return an **ARCHIVE USED** section at `file:line`.

## MANDATORY RULES FOR A BUILD

From `python3 scripts/rules.py --for build`. Run it and read each statement.

- **P-h.** Module-parameterized, never function-parameterized.
- **P-l.** No stage presentation in a type that does not need one.
- **P-k.** A read lemma is stated where its consumers use it.
- **P-m.** The check-cost rate is a content-class certificate.
- **P-n.** Satisfaction content at a concrete carrier is a payable floor.
- **P-u.** Certify BEFORE you place.
- **R-35, R-38**: sealing and opacity. **Do not unseal.**
- **R-40**: state a membership witness SHALLOW and climb.
- **I-5**: the inference trap this tree has paid for.
- **C-12.** `GHCRTS="-A64m -I0 -M8g" agda <file>`, ONE process.
- **C-22.** Write the deliverable incrementally.
- **D-10.** The 110-line price is a residue one hour old. Re-verify before you
  build on it.

## SCOPE (read)

`src/ProbeLJ130B.agda` FIRST, then `_build/lj-1.30-report.md`, then
`src/L/Coding/Environment.lagda.md` in full, then `src/L/Coding/Model.lagda.md`
at the named lines.

## SCOPE (write)

`src/L/Coding/Environment.lagda.md` and `src/L/Coding/Model.lagda.md` ONLY,
plus `src/ProbeLJ131*.agda` if you need one. Your report is
`_build/lj-1.31-report.md`. **No other master. Never
`src/Everything.lagda.md`.**

## CONSTRAINTS

- **Never commit and never push.**
- **Never run `git checkout .`, `git stash`, `git reset --hard` or `git
  clean`.** `dev/` has uncommitted changes.
- **Typecheck the two masters AND all six consumers**, one process at a time.
  Do NOT run `make check`.
- **Do not weaken or delete a theorem that stands.** `consAt-adequate`'s
  statement above all.
- **The machine is quiet and both Agda slots are yours.** Say if that changes.
- **Count with `python3 scripts/ledger.py`'s caliber.** DD26 excludes the two
  catalogs.
- **Report cold seconds and the RATE per file**, noise rule: under 0.5 s or 5
  percent, whichever is larger, is flat. **Interfaces live in
  `_build/2.8.0/agda/src/`, NOT beside the source**; deleting a `.agdai` next
  to a `.agda` removes nothing and turns a cold measurement into a warm read.
  I made exactly that mistake today.
- **Run `python3 scripts/lint-prose.py --check` and `python3
  scripts/lint-agda.py --check`.**
- **DD23 freezes mathematical prose.** Code and its own comments only.
- **Evidence is `file:line`.**
- **A refusal with a measurement is a SUCCESS.**
- Write ASD-STE100 in the report.

## RETURN

Write `_build/lj-1.31-report.md` INCREMENTALLY, skeleton first.

1. **THE VERDICT**, first line: delivered with lines and rates, or refused with
   a measurement.
2. **DID ANY CONSUMER NEED AN EDIT?** Answer first after the verdict.
3. **IS `consAt-adequate`'s STATEMENT UNCHANGED?**
4. **THE NUMBER**: in-fence lines per file, before and after.
5. **SECONDS AND RATE per file**, including all six consumers, against the
   delivered figures.
6. **DID THE CLAUSE'S COUNT REACH 0** in the real masters, not just the probe?
7. **DD4**: what the J tower gets, and whether it uses `consAtL` at all.
8. **ARCHIVE USED.** 9. **WHAT I AM NOT SURE OF.**
