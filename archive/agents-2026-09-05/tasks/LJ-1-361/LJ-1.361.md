# LJ-1.361: recon. Prove Cantor-Bernstein for ANY model of ZF, then instantiate at L

tier: pi (pi-subagent-mode), model `glm-5.3`. **I ran
`scripts/dispatch/dispatch_policy.py` before writing this line and took the
head it gave.** **This is a RECON. Price it; do not build it.** Agda allowed
for a miniature.

## THE OWNER'S QUESTION, in their own words

> **I do not understand why proving CSB has to involve anything specific to
> `L`. Could we prove a more general theorem: every model of ZF satisfies CSB,
> and then, because `L` models ZF, `L` satisfies CSB too? Would that be
> simpler?**

## WHY THIS TASK EXISTS, and the fault is mine

**`[LJ-1.353]` priced internal `L ⊨ CSB` at about 650 lines. IT WAS NEVER
ASKED THIS QUESTION.** **My brief framed it L-side and closed the door in one
sentence:「And the trophy says `L ⊨ …`, so an AMBIENT Cantor-Bernstein would
not serve. It must be a theorem OF `L`.」** **That sentence is true and it is
not the whole space: between「ambient」and「of L」sits「of an ARBITRARY model」,
and I never named it.** **MEASURED: `grep -i` over
`agents/tasks/LJ-1-353/lj-1.353-report.md` returns ONE hit for `ZFModel`, and
it only says where the record sits. So its 650 prices the L-sited form and
says nothing about the generic one.**

## WHAT I MEASURED BEFORE WRITING THIS, and you must re-derive all of it (C-44)

| what | reading |
|---|---|
| `src/FOL/ZFModel.lagda.md:24` | **`module FOL.ZFModel {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ))`. The chapter is ALREADY generic over an arbitrary ZF structure.** |
| the model record's fields | **they ARE the axioms**, and two of them take a `Formula S 1` (`:159`) |
| `hasPower` | `:199`, `isContr (SetOf (λ x → x ⊆ˢ a))` |
| `hasPair` | `:192` |
| `L⊨ZFC` | `src/L/Model.lagda.md:99`, an `isZFCModel` |
| `InjCode` | `src/L/Cardinal.lagda.md:223-228`: **four SATISFACTION facts**, `⊨ svAt`, `⊨ domAt`, `⊨ injAt`, plus a value clause. **Nothing in the STATEMENT is specific to `L`** |
| why it is L-sited | `L.Cardinal` imports `L.Constructible`, `L.Ordinal`, `V.Model`. **Sited in L, not obviously OF L** |

## THE QUESTION TO PRICE, in four parts

**1. CAN THE STATEMENT BE MADE GENERIC AT ALL?** **Write, as a type, what
「every model of ZF satisfies CSB」would be over `FOL.ZFModel`'s own `𝒮`
parameter and its `isZFModel` record.** **If it cannot even be STATED there,
say exactly which vocabulary is missing and the question closes.**

**2. WHICH FIELDS DOES THE PROOF NEED, and does the record carry them?**
**`[LJ-1.353]` chose Tarski's fixed-point form over the chain form, because
the fixed point needs ONE separation over a `𝒫 a`-bounded quantifier.** **THE
CRUX: is that separation a FIELD of the generic record, or does it need
something a particular model supplies?** **`:159` says two fields take a
`Formula S 1`. Read them and decide.** **This single question decides the
whole task.**

**3. WHAT DOES THE 650 BECOME?** **`[LJ-1.353]` named its widest unmeasured
term as「the three closure facts as satisfaction inferences」.** **Are those
three facts L-specific, or are they facts about ANY model's satisfaction?**
**If generic, the 650 does not shrink but it is paid ONCE for every model
forever, which is a different and better deal.** **If they are L-specific, say
why, at `file:line`.**

**4. HOW MUCH OF WHAT IS ALREADY DELIVERED WOULD MOVE?** **`InjCode` is the
test case.** **Say whether `InjCode` could be stated over a generic `𝒮` and
`isZFModel`, and what would have to move with it.** **Do NOT propose the
move; price it.** **A big answer here is a route-level finding and may deserve
its own ruling.**

## THE MINIATURE THAT WOULD SETTLE IT

**Build the smallest thing that decides part 2**: take `FOL.ZFModel` at an
ABSTRACT `𝒮`, take an `isZFModel`, and try to obtain the one separation the
fixed-point argument needs, **using only the record's fields**. **You do not
need CSB. You need to know whether the tool is in the box.** **If it types,
the owner's route is open and you can price the rest. If it does not, name the
missing field.**

## THE ABORT CRITERION, fixed BEFORE the run (D-1)

- **THE OWNER'S ROUTE IS OPEN AND CHEAPER.** **Say so with a line estimate and
  its basis** (DD8). **Best possible outcome, and it would make the just-landed
  L-side work partly redundant. SAY THAT PLAINLY IF SO; I would rather retire
  34 lines than defend them.**
- **THE ROUTE IS OPEN AND NOT CHEAPER.** **Then say what it BUYS instead: one
  proof serving `L`, the internalization route and every future model.**
  **That is a DD4 answer and it may still be the right call. Price both.**
- **THE ROUTE IS BLOCKED.** **Name the field or the vocabulary that is
  missing, at `file:line`.** **That is the most valuable outcome, because it
  turns the L-sited form from a choice into a necessity, and the owner asked
  precisely for this.**
- **IT IS ALREADY THERE.** **D-10: search before you price.** **Three tasks
  this month found delivered answers that earlier reports called absent, and
  twice the answer was written in English in a sibling chapter (C-57). Run a
  SEMANTIC search, not only a literal one.**

## WHAT YOU MUST NOT DO

- **DO NOT BUILD IT. This is a recon.** Write only in
  `agents/tasks/LJ-1-361/`. **`src/` is forbidden** (I-5).
- **DO NOT re-litigate `[LJ-1.323]`'s statement ruling.** The trophy's shape
  is settled. **You are pricing where a PROOF lives, not what the trophy
  says.**
- **`src/L/CantorBernstein.lagda.md` and `src/V/CantorBernstein.lagda.md`
  landed TODAY and are green.** **Read both. They are the AMBIENT corollary
  and its substrate, NOT the internal theorem.** **Do not confuse the two;
  `[LJ-1.353]` kept them separate and so must you.**
- **`[LJ-1.360]` is LIVE and holds ONE Agda slot**, writing only in
  `agents/tasks/LJ-1-360/`. **You may take the second slot and no more.**
- **COUNT THE AGDA SLOTS** before every invocation, exactly:
  `ps aux | awk '/libexec.*bin\/agda/ && !/awk/' | wc -l`. **Both obvious
  alternatives OVER-COUNT, MEASURED.**
- **ONE agda process, `GHCRTS="-A64m -I0 -M8g"`, cap NEVER raised.** **Report
  the empty-file floor beside any seconds figure** (C-53 as extended).
- **Never commit, never push**, never `git checkout .`, `git stash`,
  `git reset --hard` or `git clean`. Do not run `make check`.
- **Create `agents/tasks/LJ-1-361/lj-1.361-report.md` in your FIRST five
  minutes** (C-22).
- Run `.venv/bin/python scripts/gate/lint-prose.py --check` and
  `lint-agda.py --check`. **No em dash.** Evidence is `file:line`. ASD-STE100.
  Mark every negative **MEASURED** or **INFERRED**.

## THE PREMISE OF MINE MOST LIKELY TO BE WRONG

**Eleven of my last thirty briefs carried a claim an agent measured FALSE, and
`[LJ-1.359]` found two stale citations in a brief I wrote an hour before it.**
**The one at risk:「`InjCode`'s statement contains nothing specific to `L`」.**
**I read four conjuncts and saw satisfaction facts. I did NOT check what `S`,
`⊨`, `pr` and `svAt` resolve to in that module, and any one of them may drag
`L` in by its definition rather than by its name.** **Check that first. If
`InjCode` is L-specific in substance, part 4 collapses and part 1 may too.**

## THE RULES

**D-10 is the first move: price the truth of the residue before pricing its
proof.** **DD8: one number naming its basis.** **C-57, C-44, C-45, C-42,
C-53, C-58, P-l, P-k.** **C-12, C-22, C-32, C-36, C-39, C-40.** I-5.
**D-1, D-26.** **DD0, DD4, DD5, DD18, DD23, DD24.**

Run `.venv/bin/python scripts/dispatch/rules.py --for recon` and read every
statement, opening the full entry for any law you act on.

## DD4

**Maximize the code the two proofs share, and write it generic.** One rule,
two ends, no metric and no checker. **NAME YOUR AXIS** (C-46), fixed at
`scripts/measure/ledger.py:50`.

**THIS TASK IS DD4 ITSELF, STATED AS A QUESTION ABOUT ONE THEOREM.** **The
owner's route is the DD4-ideal form: prove it once over an arbitrary model and
let `L` inherit by instantiation.** **So do not treat DD4 as a section to
fill. It is the thing being priced.** **Say what the generic form would do to
the AC closure, the GCH closure and their shared core**, and note
`dev/ledger.toml:200-206`: the GCH closure is read from a STATEMENT whose
proof is not wired, so it UNDERSTATES by about 1,027 lines.

**And note DD5: the double-trophy endpoint is benchmarked against the
internalization route. A theorem proved over an arbitrary ZF model is
inherited by that route too.** **Say in one line whether that matters here.**

## ARCHIVE (DD18)

**A live `agents/tasks/` path is NOT an archive citation, MEASURED
2026-08-16** (`scripts/gate/check-archive-cited.py:26-27`). **Cite archived
CODE, not only records.**

- **`archive/src/2026-08-09-rud-route/L/Cardinal.lagda.md:89-190`**, the
  retired route's CSB. **THE KEY QUESTION FOR YOU: was it stated generically
  or at a fixed carrier?** **Read its module line and its parameters.** **The
  retired route made the opposite packaging choice, so its answer here is
  direct evidence.**
- **`archive/src/2026-08-09-rud-route/L/CardinalPredicates.lagda.md:10`**, the
  retired ruling that equinumerosity is a bijection, chosen to avoid a
  per-consumer CSB obligation.
- **`archive/dev/DECISIONS-archived.md`**: **grep for any ruling on where a
  model-level theorem belongs.** WHY NOT if none bears.
- **`archive/dev/JOURNAL-archived.md`**: the reasoning behind the retired
  carrier choice. WHY NOT if nothing bears.

**Return an ARCHIVE USED section naming ONE line read per archived file, with
WHY NOT for anything you decline.**

## LITERATURE (DD18)

**`dev/literature/devlin-II5.md` and `dev/literature/digest.md`.** **Say in
one line how the literature treats this: does a set theorist prove CSB once in
ZF and relativize it, or re-prove it inside each model?** **That is the
owner's question asked of the mathematics rather than of the tree, and the
answer is evidence.** Return a **LITERATURE USED** section.

## SCOPE (read)

`src/FOL/ZFModel.lagda.md:154-200` FIRST: the record whose fields decide
part 2, and the two fields that take a `Formula S 1`.

## SCOPE (write)

`agents/tasks/LJ-1-361/` only.

## RETURN

**Lead with ONE word: OPEN, OPEN-BUT-NOT-CHEAPER, or BLOCKED, and ONE number
with its basis.** Then the generic statement as a type, or the vocabulary that
prevents it. Then the crux: is the bounded separation a field of the record.
Then what the 650 becomes. Then whether `InjCode` is L-specific in SUBSTANCE.
Then your miniature. Then what would move, priced and not proposed. **Mark
every negative MEASURED or INFERRED.**
