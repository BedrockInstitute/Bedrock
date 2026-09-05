# LJ-1.362: build STAGE 1 of Cantor-Bernstein over an ARBITRARY model of ZF

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** Agda. **BUILD, staged.**

## THE OWNER'S RULING, in their own words

> **Dispatch one now to do「every model of ZF satisfies CSB」. This does not
> disturb the current GCH route. If it turns out we do not need it, we can
> archive it later.**

**So the risk of「we may not need this」is RULED and is not yours to re-open.**
**Build it well; archiving is cheap and this project never deletes.**

## WHAT `[LJ-1.361]` MEASURED, and you start from it

**VERDICT: OPEN-BUT-NOT-CHEAPER, about 700 lines.** **The route is open: the
proof needs only record FIELDS.**

**THE CRUX IS SETTLED BY A GREEN FILE.** `agents/tasks/LJ-1-361/MiniSep.agda`,
**exit 0 in 1.34 s, floor 0.62 s**, at an ABSTRACT
`𝒮 : ZFStructure (hPropAlgebra ℓ)` and an abstract `isZFModel`:

- **the separation the fixed point needs IS the field `hasSeparation`**,
  `src/FOL/ZFModel.lagda.md:194`, and it takes ANY first-order formula;
- **bounded quantifiers `∀̇∈` and `∃̇∈` are PRIMITIVE constructors**,
  `src/FOL/Syntax.lagda.md:100`;
- **the power object is the field `hasPower`**, `:199`, derived `𝒫` at `:287`;
- the carve comes through `separate` at `:281` with `separate-spec`;
- **and it proved by `refl` that satisfaction of the bounded quantifier
  computes to the truth algebra's sup**, so **no translation layer stands
  between the formula and the host logic at an abstract carrier.**

**THE THREE CLOSURE FACTS ARE GENERIC**, `[LJ-1.361]` part 3: inferences about
satisfaction in whatever model holds the record. **The full field list the
proof consumes is `separate`, `𝒫`, `pair`, `⋃`, `extensional`, plus excluded
middle at the model's level. All are fields or one-line consequences.**

**READ `MiniSep.agda` FIRST AND RE-RUN IT.** It is your foundation and it is
40 minutes old.

## WHY THIS IS STAGED, and what stage 1 is

**DD8: a build brief names its widest unmeasured term.** **`[LJ-1.361]` named
what its miniature did NOT decide:**

> the closure condition's content, **the pair-reader adequacy against the
> derived pair**, and the graph carve.

**And it flagged the adequacy as NEW WORK: 150 lines L-sited becomes about 200
generic, because the adequacy must now run against the record's DERIVED pair
rather than against a delivered L-side reader.** **That is the widest
unmeasured term in the whole 700, and it is stage 1's target.**

**STAGE 1 IS: the generic module, the statement, the Tarski formula, and the
pair-reader adequacy against the derived pair.** **NOT the three closure facts
and NOT the graph carve.** **You stop when adequacy is green or when it walls,
and you report a GO or NO-GO with a price for the remaining 250 to 300.**

**A partial landing is the expected outcome and it is not a failure.** **Land
what is green; leave the rest as a named hole with its price.**

## THE STATEMENT, from `[LJ-1.361]` part 1, which needs NO new vocabulary

```agda
module FOL.Bernstein {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) where
  module ZF = FOL.ZFModel 𝒮
  CSB : ZF.isZFModel → Type (ℓ-suc ℓ)
```

**Re-derive it; do not paste it.** `[LJ-1.361]`'s sketch writes the formula
families `svAt`, `domAt`, `injAt`, `inRanAt` at
`Formula (ZFStructure.S 𝒮) n`. **MEASURED by `[LJ-1.361]` part 4: those three
are parameter-free, variable-only syntax and carry no constant, so the same
trees typecheck at any carrier.** Their L-sited homes are
`src/L/Coding/Model.lagda.md:210-214` and `:278-279`,
`src/L/Coding/Injection.lagda.md:44-48`, with `prAt` at
`src/L/Coding/Base.lagda.md:285-287`.

**DO NOT MOVE THEM OUT OF THE L CHAPTERS IN THIS TASK.** `[LJ-1.361]` priced
that migration at about 125 lines with 10 consumers rewiring imports. **It is
a separate ruling and it is not yours.** **Write what you need at the generic
site, and say plainly which definitions you had to duplicate and how many
lines the duplication cost.** **That number is what a future migration ruling
will be priced against, so measure it honestly rather than minimising it.**

## THE ABORT CRITERION (D-1)

- **ADEQUACY LANDS GREEN.** **Then the widest unmeasured term is measured and
  the remaining 250 to 300 can be funded.** Report the price. **Best.**
- **ADEQUACY WALLS.** **Name what fails, at `file:line`, with the type Agda
  refused.** **A NO-GO here is worth more than a half-built 700, because it
  says the generic route costs more than `[LJ-1.361]` inferred.**
- **THE STATEMENT WILL NOT EVEN TYPE.** **Then `[LJ-1.361]` part 1 is wrong
  and the owner's route closes. Say so immediately with the term.**
- **A WALL.** **C-58: replace a numeral pattern-match split with the library
  eliminator before bisecting the mathematics.** **C-55: a hypothesis stating
  an equation against a coded term is FREE as a module parameter and an 8 GB
  wall as a record field.**

## CONSTRAINTS

- **You MAY create ONE new master, `src/FOL/Bernstein.lagda.md`, and edit
  nothing else in `src/`.** **NEVER touch `src/Everything.lagda.md`; I wire it
  after auditing your work.** If a consumer forces another edit, say so BEFORE
  making it.
- **`src/` is bilingual, `en` + `zh`, MEASURED** (`Makefile:29`,
  `LANGS := en,zh`). **Write both. No Japanese.** **If you need a term
  rendering `dev/glossary.toml` lacks, STOP and name it: DD19's pipeline is
  two agents and it is not yours.**
- **`[LJ-1.363]` is live and writes only in `agents/tasks/LJ-1-363/` and
  `scripts/gate/`.** No collision; it holds no Agda slot.
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **RUN A NEGATIVE CONTROL that MEASURES.** **`[LJ-1.355]`'s standard: swap
  two components of one tuple and show Agda refuses with exit 42 naming the
  expected type.** **A green run on a new file proves nothing until you have
  seen the file go red.**
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. **Do not run `make check`; I run it.**
- **Create `agents/tasks/LJ-1-362/lj-1.362-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check`,
  `lint-agda.py --check` and `scripts/site/weave-i18n.py --check`. **No em
  dash.** Evidence is `file:line`. **Your REPORT is ASD-STE100; the MASTER's
  prose is not.** Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty-one briefs carried a claim an agent measured
FALSE.** **The one at risk: 「the adequacy is about 200 lines」.** **That is
`[LJ-1.361]`'s INFERRED figure, marked INFERRED by it, anchored on
`src/L/Coding/Base.lagda.md` at 185 measured code lines at a DIFFERENT site.**
**P-l: a measured cure does not transfer by analogy, and a figure anchored on
a comparable elsewhere is a hypothesis rather than a price.** **Re-measure it
at its own site and report the real number without apology.**

## THE PERFORMANCE LAWS THAT BEAR DIRECTLY ON A GENERIC MODULE

**Three of these are about exactly what you are building, so read the full
entries rather than the headlines.**

- **P-h: definability walks are MODULE-parameterized, never
  FUNCTION-parameterized.** **Your whole master is one module over `𝒮` and an
  `isZFModel`. Take the parameters at the module, not on each definition.**
  **Getting this wrong is the difference between a cheap generic theorem and
  an unusable one.**
- **P-m: the check-cost rate is a content-class certificate, and
  INSTANTIATION is the expensive class.** **A generic theorem exists to be
  instantiated, so this law prices the thing your master is FOR.** **Say what
  you expect an instantiation at `𝒮ʟ` to cost, and mark it INFERRED if you do
  not run one.**
- **P-n: satisfaction content at a CONCRETE carrier is a payable floor, not a
  defect.** **You are writing at an ABSTRACT carrier, so the floor may move.
  Report what you observe rather than assuming P-n transfers** (P-l).
- **R-38: a consumer's alias of a transparent imported operation is a birth
  site.** **You will alias the record's derived operations (`𝒫`, `pair`,
  `⋃`). Watch this.**
- **R-35** (union representations are meta-poisoned; state memberships at
  small indices) and **R-40** (a deep successor-chain membership witness
  normalizes super-linearly). **Both bear if the Tarski carve walks a chain.**

## THE RULES

**DD8: name the widest unmeasured term; it is the adequacy and you are
measuring it.** **P-h, P-m, P-n, R-35, R-38, R-40, as above.** **C-44: re-derive every line I quoted; two of my recent briefs
quoted stale ones and `[LJ-1.359]` caught both.** **C-45: `exit 0` is not a
supply.** **C-57, D-10, C-42, C-53, C-55, C-58, P-l, P-k.**
**C-12, C-22, C-32, C-36, C-39, C-40.** I-5. **D-1, D-26.**
**DD0, DD4, DD5, DD9, DD13, DD19, DD23, DD24, DD25.**

Run `.venv/bin/python scripts/dispatch/rules.py --for build` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**THIS TASK IS DD4 IN ITS PUREST FORM AND THAT IS WHY THE OWNER FUNDED IT.**
**A theorem proved over an arbitrary `𝒮` is inherited by EVERY model, not just
by both trophies.** **Two delivered models wait today: `L` at
`src/L/Model.lagda.md:98` and `V` at `src/V/Model.lagda.md:415`.** **And DD5
benchmarks the double trophy against the internalization route, which would
inherit it too.**

**So report the closure for both ends, and ALSO say which delivered models
could instantiate your master the day it lands.** **Note
`dev/ledger.toml:200-206`: the GCH closure is read from a STATEMENT whose
proof is not wired, so it UNDERSTATES by about 1,027 lines.**

**One thing you must NOT claim.** **`[LJ-1.361]` measured that nothing landed
today is retired by this route:** `V.CantorBernstein` and `L.CantorBernstein`
serve the AMBIENT reading, and a generic internal theorem produces a CODED
bijection, **a different object.** **Both readings stand beside each other.
Do not write that yours replaces them.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation, MEASURED
2026-08-16** (`scripts/gate/check-archive-cited.py:26-27`). **Cite archived
CODE, not only records.** **Name each of the four corpora, cited or declined
in one line: DD18's amended row now asks for that.**

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`**, the
  retired CSB. **`[LJ-1.361]` was asked whether it was stated generically or
  at a fixed carrier. Read its module line and parameters yourself: it is the
  closest delivered comparable to what you are writing, and its packaging
  choice is direct evidence.**
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`**, the
  retired ruling that equinumerosity is a BIJECTION, chosen precisely to avoid
  a per-consumer CSB obligation. **Your theorem is what would have made that
  choice unnecessary. Say so in one line if it is true.**
- **`archive/dev/DECISIONS-archived.md`**: any ruling on where a model-level
  theorem belongs. **WHY NOT in one line if none bears.**
- **`archive/dev/JOURNAL-archived.md`**: the reasoning behind the retired
  carrier choice. **WHY NOT in one line if nothing bears.**

**Return an ARCHIVE USED section naming every path above, TOOK or DECLINED,
and quoting ONE line read per archived file.** **That quote duty is DD18's
amended return clause, ruled by the owner today.**

## LITERATURE (DD18)

**`dev/literature/digest.md` and `dev/literature/devlin-II5.md`.** **The
owner's question asked of the mathematics: does a set theorist prove CSB once
in ZF and relativize it, or re-prove it inside each model?** **`[LJ-1.361]`
was asked this; verify its answer rather than repeat it.** Return a
**LITERATURE USED** section with WHY NOT.

## SCOPE (read)

`agents/tasks/LJ-1-361/MiniSep.agda` FIRST, WHOLE, and RE-RUN IT. Then
`src/FOL/ZFModel.lagda.md:187-200` and `:281-290`, the fields and the derived
operations your proof consumes.

## SCOPE (write)

`src/FOL/Bernstein.lagda.md`, and `agents/tasks/LJ-1-362/`.

## RETURN

**Lead with ONE line: does the pair-reader adequacy land green at the generic
site, and at how many lines against the INFERRED 200.** Then the statement, as
it actually typed. Then what you had to duplicate from the L chapters and its
line cost. Then GO or NO-GO for the remaining 250 to 300, with a price. Then
your negative control with the exit code and the type Agda named. Then which
delivered models could instantiate it today. **Mark every negative MEASURED or
INFERRED.**
