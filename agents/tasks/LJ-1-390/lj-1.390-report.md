# [LJ-1.390] The descent route to `sq`, priced against `Leg1`'s second conjunct

[`Probe390.agda`](Probe390.agda), 279 lines, GREEN, **1.44 wall seconds**, the
median of three consecutive runs (1.42, 1.44, 1.45) at the wide caliber
`-A64m -I0 -M8g` with one Agda process.

## VERDICT

**GO on the machinery. Both terms are built at generic `δ` and `κ`, and neither
uses an internal product.** `descent-gives-sq` is at
`Probe390.agda:135-142`. `descent-closes` is at `Probe390.agda:213-219`.

**THE DESCENT ROUTE DOES NOT AVOID THE RISK THE BRIEF NAMED. IT MOVES IT TO THE
INTERNAL CARDINALS AND NOWHERE ELSE.** `descent-owes` (`Probe390.agda:155-163`)
is a three-way disjunction. At an ordinal that is an internal cardinal, the
third disjunct is refuted, and `owes-third-refuted` (`Probe390.agda:170-176`)
proves that refutation in Agda. So the residue at a cardinal is `Init`, which is
the ambient-to-coded converse the brief warned about.

**`Init` HAS NO PRODUCER IN THE TREE. RE-MEASURED 2026-08-19.** `grep -rnw Init
src/` gives seven lines: the definition at
`src/L/Ordinal/SquareLaw.lagda.md:692-700`, the module `Initial` at `:938`, the
two suppliers at `:960` and `:963`, one chapter comment at `:13`, and one
comment at `src/L/InjChain.lagda.md:104`. **None of the seven builds an `Init`.**
`[LJ-1.286]` measured the same absence
(`agents/tasks/LJ-1-286/lj-1.286-report.md:180-181`).

**THE ROUTE IS NOT NEW GROUND, AND THE REPORT MUST NOT SELL IT AS SUCH.** Two
prior records already hold it. The archived rud route stated the descent AND
its residue in prose
(`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:957-962`,
quoted in full under ARCHIVE USED). And `[LJ-1.337]` already built the same
recursion with a different residue:
`sq-core` at `agents/tasks/LJ-1-337/ProbeLJ1337B.agda:203-204`, over
`LimitBand` at `:124-125`, by the same `∈-induction`. Its open branch is "δ
closed and not `Init δ`" (`agents/tasks/LJ-1-337/lj-1.337-report.md:262-263`).
**`descent-gives-sq` is a supplier for exactly that branch**, and it is one that
`[LJ-1.337]` did not have. The descent route is therefore a way to CLOSE
`[LJ-1.337]`'s open branch, not a second route beside it.

**WHAT THIS TASK ADDS, IN ONE LINE.** The archive gave the plan and `[LJ-1.337]`
gave the recursion. This task gives the terms at generic `δ` and `κ`, the
`sq`-free residue, the mechanical proof that the residue is not vacuous, the fit
to the consumer's own type, and the price.

## 1. What was built

| Term | At | Code lines | What it is |
|---|---|---|---|
| `mem-incl` | `Probe390.agda:76-89` | 12 | `κ ∈ δ` with `δ` an ordinal gives `⟪κ⟫ ↪ ⟪δ⟫` |
| `descent-core` | `Probe390.agda:110-131` | 18 | the composite, with the descending arrow a variable |
| `descent-gives-sq` | `Probe390.agda:135-142` | 8 | the obligation. `descent-core` with the door applied |
| `descent-owes` | `Probe390.agda:155-163` | 9 | the residue |
| `owes-third-refuted` | `Probe390.agda:170-176` | 7 | the residue is not satisfiable by descent alone |
| `Goal`, `descent-step` | `Probe390.agda:180-204` | 22 | the recursion motive and its step |
| `band-ord` | `Probe390.agda:208-211` | 4 | the band hypothesis gives the ordinal certificate |
| `descent-closes` | `Probe390.agda:213-219` | 7 | the obligation. `∈-induction` over the step |
| `ConsumerShape`, `plugs-in` | `Probe390.agda:232-240` | 8 | the consumer's own type, and the fit to it |

**TOTAL: 95 code lines.** A code line is a line that is not blank and is not a
comment. The file is 279 lines and 128 code lines. The difference is the module
header and the imports.

**THE FOUR ARROWS, AND NO PRODUCT ANYWHERE.** `descent-core` maps a pair in
`⟪δ⟫ × ⟪δ⟫` down by the descending arrow, applies `sq (fst κ)`, and lifts by
`mem-incl`. The type of `descent-gives-sq` names no product of two L-sets, and
the body forms none. `[LJ-1.386]` measured that `src/` holds no such product
(`agents/tasks/LJ-1-386/lj-1.386-report.md:130-136`), and this route never needs
one.

**PART 4 IS AN ANSWER THE BRIEF DID NOT ASK FOR AND THE CAMPAIGN NEEDS.** The
consumer takes `δ` as a bare `V ℓ` (`src/L/StageCardinal.lagda.md:17-20`), and
`descent-closes` takes an L-element. `plugs-in` (`Probe390.agda:238-240`) closes
that gap: a member of `sucV α₀` is an ordinal by `band-ord`, and every ordinal is
an L-element by `isL-ord` (`agents/tasks/LJ-1-386/Probe386.agda:82-83`). **So
the discharge is not near the consumer's shape. It IS the consumer's shape.**

## 2. `descent-owes`, and why it is not the conclusion in disguise

```agda
descent-owes =
  (a : S) → IsOrd (fst a) → (⟨ fst a ∈ ω ⟩ → Empty.⊥)
  → (fst a ≡ ω)
  ⊎ (Init (fst a)
  ⊎ (Σ[ κ ∈ S ] (⟨ fst κ ∈ fst a ⟩
               × (⟨ fst κ ∈ ω ⟩ → Empty.⊥)
               × ∥ Σ[ A ∈ Mem (Lset (SiteBound.β a)) ]
                     InjCode (SiteBound.up a A) a κ ∥₁)))
```

**CLAUSE 1, CLOSED. It holds in the strongest form.** `descent-owes` is a
`Type`, not a family. It takes no parameter at all, so it takes none of
`descent-closes`'s telescope.

**CLAUSE 2, NO `sq` AT A BOUND VARIABLE. It holds in the strongest form.** The
type does not contain the token `sq`.

**CLAUSE 3, THE ONE LINE.** `descent-owes` never mentions `sq`, it is refuted at
any internal cardinal by `owes-third-refuted` unless its `Init` disjunct holds
there, and each of its three disjuncts already has a delivered supplier at some
site: `refl` at ω, `via-col-square` under `Init`
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`), and
`InternalLeastCard.Selected.δ-inj` for the coded descent
(`src/L/Cardinal.lagda.md:257-258`).

**WHAT THE RESIDUE ASKS FOR, BY CASE.** This is the honest reading and it is
what the campaign should fund against.

| The ordinal `a` | What `descent-owes` demands |
|---|---|
| `a ≡ ω` | nothing. `squareω` serves it (`src/L/InjChain.lagda.md:184-185`) |
| `a` is an internal cardinal | `Init a`. The third disjunct is refuted at `Probe390.agda:170-176` |
| `a` is not an internal cardinal | ONE coded injection out of `a` into a smaller infinite ordinal |

**THE THIRD ROW IS THE ROUTE'S ONE GAIN OVER THE PRODUCT ROUTE.** The product
route asks for a coded injection out of the internal SQUARE of `a`
(`agents/tasks/LJ-1-386/Probe386.agda:287-290`). The descent route asks for one
out of `a` itself. `[LJ-1.386]` named the square version as the only place
cardinal arithmetic enters the route
(`agents/tasks/LJ-1-386/lj-1.386-report.md:138-139`). The descent version does
not form a square.

**THE THIRD ROW IS ALSO WHERE THE ROUTE IS WEAKEST, AND IT IS UNMEASURED.**
Nothing measured says the coded injection out of `a` exists at a non-cardinal
`a`. `InternalLeastCard.Selected.δ-inj` carries an object of that shape, but only
under its `nonempty` hypothesis (`src/L/Cardinal.lagda.md:243-258`), and this
probe did not discharge that hypothesis at any `a`.

## 3. The price, side by side

**NEITHER ROUTE IS PRICED END TO END. THE TWO NUMBERS BELOW ARE THE BUILT
HALVES, AND THEY ARE NOT THE ROUTES.**

| | Product route | Descent route |
|---|---|---|
| Built and green | the internal product and its bridge: **125 code lines, 1.39 s** (`agents/tasks/LJ-1-388/lj-1.388-report.md:23-24`) | the whole descent machine: **95 code lines, 1.44 s** (this file) |
| Sets it must build first | one, the internal product | **none** |
| Payoff term | `leg1-gives-sq`, 9 lines (`agents/tasks/LJ-1-386/Probe386.agda:294-302`) | `descent-core` and `descent-gives-sq`, 26 code lines |
| Still owed | the coded injection out of the internal square, at every band ordinal | `descent-owes`: `Init` at the internal cardinals, one coded injection elsewhere |
| Price of what is owed | UNPRICED. `[LJ-1.388]` gives about 130 code lines as a best-effort figure and says not to quote it as a price (`agents/tasks/LJ-1-388/lj-1.388-report.md:244-248`) | UNPRICED. Section 4 gives the figure and its basis |

**THE COMPARISON THAT THE CAMPAIGN CAN ACT ON IS NOT THE LINE COUNT.** It is the
shape of the two demands. The product route owes one object at EVERY band
ordinal. The descent route owes `Init` only at the internal cardinals in the
band, and a weaker object everywhere else. **That narrowing is the descent
route's whole value, and this probe measured it.**

## 4. W3: the widest unmeasured term, and its probe

**THE WIDEST UNMEASURED TERM IS `Init a` AT AN INTERNAL CARDINAL `a`.** Nothing
in the tree builds an `Init` (section VERDICT, re-measured today), so this term
has no delivered comparable of its own kind.

**THE PROBE THAT MEASURES IT.** Build `IsCardinalL a → Init a` at generic `a`,
in its own task directory. Its hard conjunct is the fourth
(`src/L/Ordinal/SquareLaw.lagda.md:696-698`): no ambient injection of `⟪a⟫` into
the square of an infinite member. `IsCardinalL` forbids only a CODED injection
(`src/L/Cardinal.lagda.md:230-233`), so the probe must turn an ambient function
into a code. **The probe should be built to REFUTE.** A NO-GO there ends the
descent route on evidence and leaves the product route the only one.

**THE ESTIMATE: about 60 code lines. THE BASIS IS A SURVEY, AND IT IS WEAK.**
The survey is section VERDICT's grep plus `[LJ-1.337]`'s pricing of the three
easy conjuncts, which it built as `isProp (Init δ)` in 11 lines over four rows
that were each already delivered
(`agents/tasks/LJ-1-337/lj-1.337-report.md:216-225`). **That basis prices the
three easy conjuncts and not the fourth**, and the fourth is the whole risk.
**Do not fund against 60.**

## 5. The measurement that cost the most, and its cure

**THE SAME MATHEMATICS COST 175.42 s IN ONE TERM AND 1.54 s IN TWO.** The six
control runs are recorded in the probe at `Probe390.agda:243-279`, with their
caliber and their conditions.

**THE CURE.** Take the descending arrow as a parameter (`descent-core`,
`Probe390.agda:110-131`) and apply `code-untruncates` once outside it
(`descent-gives-sq`, `Probe390.agda:135-142`).

**TWO CONTROLS SAY IT IS NOT THE DOOR.** Applying the door and spending its
forward half alone costs 1.54 s. Spending its injectivity half alone, at generic
`a` and generic `b`, costs 1.57 s. The cost needs both halves inside one term.

**THIS PROBE DID NOT ISOLATE THE TRIGGER, AND ONE CONTROL RULES OUT THE OBVIOUS
STATEMENT OF IT.** A seventh run repeated `leg1-gives-sq` of the product route
verbatim, with its `δ` made generic so that both of its sites are variables. It
cost 1.56 s. **So the product route's payoff does not show the cost**, and no
claim of the form "the door costs at generic sites" is supported here.

**THE CURE DOES NOT TRANSFER BY ANALOGY.** The Boundary forbids that, and the
seventh run is why the rule is right. `[LJ-1.388]`'s consumer must re-measure at
its own site.

## 6. What this report does NOT claim

- **It does not claim the square law at any ordinal.** Every term here is
  conditional. `descent-closes` takes `descent-owes`, and nothing inhabits
  `descent-owes` today.
- **It does not claim a bijection or an equivalence anywhere.** Every arrow built
  here is an injection in the sense of `_↪_` (`src/L/Cardinal.lagda.md:47-48`).
  The archived route reached the ordinal pairing well-order and stalled on the
  equinumerosity (`archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:4-16`),
  and this probe does not touch it.
- **It does not claim the descent route is cheaper than the product route.**
  Both residues are unpriced. Section 3 gives the built halves only.
- **It does not claim the recursion is new.** `[LJ-1.337]` built it first
  (`agents/tasks/LJ-1-337/ProbeLJ1337B.agda:203-204`). What is new is the
  `sq`-free residue and the supplier for its open branch.
- **It does not price `[LJ-1.388]`'s route.** It quotes that report's own
  figures, at their line numbers, and nothing else.
- **It does not measure the `nonempty` hypothesis of `InternalLeastCard`.** That
  hypothesis is what the third disjunct needs at a non-cardinal, and no run here
  touched it.

## ARCHIVE USED

**THE ARCHIVE ALREADY NAMED THIS ROUTE AND ALREADY NAMED THIS RESIDUE. THIS IS
THE MOST IMPORTANT ROW IN THE TABLE BELOW.**

| Injected path | Read | What it gave |
|---|---|---|
| `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md` | `:957-962` | **The descent and its residue, both stated.** |
| `archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md` | `:12-15` | the archived wall, quoted in section 6 |
| `archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md` | `:14` | the consumer that needs the law |
| `archive/dev/JOURNAL-archived.md` | `:1338` | the law was a named conditional bound |
| `archive/src/2026-08-09-rud-route/Everything.lagda.md` | `:1` | DECLINED. See below. |

**`archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md:957-962`:**

> It does not give the law at the non-initial ordinals such as
> `ω + ω`: the reduction of such a site to its cardinal is the least-of
> transfer, which is the counting's own plumbing (its input, the truncated
> equinumerosity witness of `Card.least`, is delivered here), and at the
> cardinals themselves the counting must still verify the three initiality
> clauses, or take them as its cardinal notion.

**READ THIS AGAINST `descent-owes`.** "The reduction of such a site to its
cardinal" is the third disjunct. "At the cardinals themselves the counting must
still verify the three initiality clauses" is the second disjunct. **The
archived route stated both, in prose, before the cutover.** So the descent idea
is NOT this task's find, and the report must not present it as one.

**WHAT THIS TASK ADDS OVER THAT PARAGRAPH.** The Agda terms at generic `δ` and
`κ`, the recursion that spends them, the mechanical proof that the residue is
not satisfiable by descent alone (`Probe390.agda:170-176`), the fit to the
consumer's own type (`Probe390.agda:238-240`), and the price. **The archive gave
the plan. This task gives the machine and the number.**

**`archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md:12-15`:**

> the classical theorem that this order type is
> equinumerous to the ordinal itself, the square law of infinite ordinals, is
> named as the one remaining theorem, with the arithmetic it needs priced in the
> report rather than faked here.

**`archive/src/2026-08-09-rud-route/L/CardinalCount.lagda.md:14`:**

> after that is an injection into an ordinal, and the one fact the bound

The sentence continues into `:15` and names the square law. This is the
consumer's archived form, and it agrees with the live consumer at
`src/L/StageCardinal.lagda.md:17-20`.

**`archive/dev/JOURNAL-archived.md:1338`:**

> the cardinal step consumes is delivered CONDITIONAL on one named bound, the
> square law (an infinite

**DECLINED, WITH THE REASON.**
`archive/src/2026-08-09-rud-route/Everything.lagda.md:1` is `# Bedrock`, the
site reading page of the archived route. It is a module catalog and a book
front matter. It holds no statement about the square law, so it bears on
nothing in this task.

## LITERATURE USED

| Injected path | Read | What it gave |
|---|---|---|
| `dev/literature/truncation-and-selection.md` | `:334-336` | why the door works at all |
| `dev/literature/devlin-II5.md` | `:280-282` | the classical route does not descend by codes |
| `dev/literature/terms-2026-08.md` | `:37` | the fact is about CARDINALS |
| `dev/literature/rudimentary-functions.md` | `:1` | DECLINED. See below. |
| `dev/literature/devlin-errata.md` | `:1` | DECLINED. See below. |

**W8: THE LITERATURE DOES NOT SHOW THIS SHAPE IS AN AXIOM.** It shows the
opposite. The square law of infinite ordinals is a theorem of ZF, and the
classical proof is the Godel pairing. So there is no literature NO-GO here, and
the task proceeds.

**`dev/literature/truncation-and-selection.md:334-336`:**

> each element to the least unused target fails at order type `ω · 2` into
> `ω`. **A canonical injection needs a well-order on the INJECTIONS, which is
> what `<_L` supplies classically and what an ambient function type does not

**THIS IS WHY `code-untruncates` WORKS AND WHY ITS CONVERSE IS HARD.** The door
well-orders the CODES, by `orderAt` over the members of `Lset β`
(`agents/tasks/LJ-1-386/Probe386.agda:270-284`), which is a well-order on the
injections. The digest says an ambient function type gives no such well-order.
**So the digest predicts, in advance and independently, that the ambient-to-coded
direction is the hard one.** That is the direction `Init` needs, and section 4
names it as the widest unmeasured term.

**`dev/literature/devlin-II5.md:280-282`:**

> (ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact
> |γ| = |α| < κ with κ a cardinal implies γ < κ (`dev2.txt:1372-1384`).
> Strength: parts (i) and (ii) of condensation only, plus the level-size

**THE CLASSICAL ROUTE SPENDS CARDINAL ARITHMETIC, NOT A CODED DESCENT.** Devlin
uses the level-size equation and initial-ordinal arithmetic. Neither is a coded
injection. So the literature gives this route no comparable and no price, and
section 4's estimate does not rest on it.

**`dev/literature/terms-2026-08.md:37`:**

> | 8 | square law | 平方律 | no literature under that name; the fact is 无穷基数的平方等于自身；no source uses 平方定理 for it | yes |

**THE FACT IS STATED AT CARDINALS.** The dossier records the fact as the square
of an infinite CARDINAL. The consumer at `src/L/StageCardinal.lagda.md:17-20`
asks for it at every ordinal of the band. **The descent is what bridges those
two statements**, and that is the whole reason this route exists.

**DECLINED, WITH THE REASON.** `dev/literature/rudimentary-functions.md` holds
the rud-route source notes; `grep -n -i "square law"` over it returns nothing,
and the rud route is archived. `dev/literature/devlin-errata.md` is a
do-not-repeat checklist for Devlin's errors; its only cardinality line is
`:136`, about a Π1 and Σ1 pair, which bears on no term here.

## THE TREE AS I LEAVE IT

**I changed two files and both are mine:** `agents/tasks/LJ-1-390/Probe390.agda`
and `agents/tasks/LJ-1-390/lj-1.390-report.md`. The task directory also holds
`LJ-1.390.md` and `.pod`, and the program wrote both. `git status --porcelain
agents/tasks/LJ-1-390/` shows that one untracked directory and nothing else, so
no file outside it moved. I ran no `git add`, no commit and no push.

**ONE GATE IS RED AND IT IS NOT MINE. REPORTED, NOT FIXED.**
`scripts/gate/lint-prose.py --check` exits 1 on
`dev/pod/instructions/coder.md:17`, "line break renders as a space between
Chinese characters; join with the next line". That file is another slot's, it is
modified in the working tree by another worker, and it is outside this task's
SCOPE. **Conjunct 6 will go red for that reason and not for this task's files.**
`[LJ-1.388]`'s acceptance record already shows `error class lint` with conjunct
6 FAILED (`agents/tasks/LJ-1-388/runs/accept-1.out`), so the defect is not new
today.

**EVERY OTHER GATE IS GREEN over the whole tree**, run from the repository root
with `.venv/bin/python`: `lint-agda.py`, `check-glossary.py`, `check-fences.py`,
`check-probes.py`, `weave-i18n.py`, `check-spec-surface.py`,
`check-closure.py --check closure`, and
`check-survey-quotes.py LJ-1.390`. `check-unbound-hyp.py --check` names five
hypotheses, all of them in `src/` and none in this task's files.
