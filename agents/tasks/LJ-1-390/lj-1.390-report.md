# [LJ-1.390] The descent route to `sq`, priced against `Leg1`'s second conjunct

slot: `coder`. Written incrementally (C-22). No commit, no push. I wrote only
in `agents/tasks/LJ-1-390/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, one process, no heap event.

[`Probe390.agda`](Probe390.agda), 291 lines, GREEN, **1.89 wall seconds**,
one run at the wide caliber `-A64m -I0 -M8g` with one Agda process. Exit 0.
No heap event.

## VERDICT

**GO on the machinery. Both named terms are built at generic `δ` and `κ`, and
neither uses an internal product.** `descent-gives-sq` is at
`Probe390.agda:135-142`. `descent-closes` is at `Probe390.agda:225-231`.

**THE DESCENT ROUTE DOES NOT AVOID THE RISK THE BRIEF NAMED. IT MOVES IT TO
THE INTERNAL CARDINALS AND NOWHERE ELSE.** `descent-owes` (`Probe390.agda:161-170`)
is a four-way disjunction. At an ordinal that is an internal cardinal, the
fourth disjunct is refuted, and `owes-third-refuted` (`Probe390.agda:177-183`)
proves that refutation in Agda. So the residue at a non-Init cardinal is `sq`
at that cardinal.

**`Init` HAS NO PRODUCER IN THE TREE. RE-MEASURED 2026-08-20.** `grep` for
`Init` under `src/` gives seven lines: the definition at
`src/L/Ordinal/SquareLaw.lagda.md:692-693`, the module `Initial` at `:938`,
the two suppliers at `:960` and `:963`, one chapter comment at `:13`, and one
comment at `src/L/InjChain.lagda.md:104`. **None of the seven builds an
`Init`.**

**CLAUSE 3, THE ONE LINE.** `descent-owes` asks for `sq` only at an internal
cardinal that it quantifies itself, and at every other infinite ordinal it
asks for a coded injection, not for `sq`.

**Predecessor types, taken from the probe that typechecked.** `[LJ-1.386]`
report is GO on the door (`agents/tasks/LJ-1-386/lj-1.386-report.md:20-21`).
`code-untruncates` is taken from `agents/tasks/LJ-1-386/Probe386.agda:264-268`,
imported, not copied. That report does not name the door FALSE. `isL-ord` is
taken from the same probe at `:82-83`.

## 1. What was built

| Term | At | Code lines | What it is |
|---|---|---|---|
| `mem-incl` | `Probe390.agda:76-89` | 12 | `κ ∈ δ` with `δ` an ordinal gives `⟪κ⟫ ↪ ⟪δ⟫` |
| `descent-core` | `Probe390.agda:110-131` | 18 | the composite, with the descending arrow a variable |
| `descent-gives-sq` | `Probe390.agda:135-142` | 8 | the obligation. `descent-core` with the door applied |
| `descent-owes` | `Probe390.agda:161-170` | 10 | the residue, four disjuncts |
| `owes-third-refuted` | `Probe390.agda:177-183` | 7 | the residue is not satisfiable by descent alone |
| `Goal`, `descent-step` | `Probe390.agda:187-216` | 26 | the recursion motive and its step |
| `band-ord` | `Probe390.agda:220-223` | 4 | the band hypothesis gives the ordinal certificate |
| `descent-closes` | `Probe390.agda:225-231` | 7 | the obligation. `∈-induction` over the step |
| `ConsumerShape`, `plugs-in` | `Probe390.agda:244-252` | 8 | the consumer's own type, and the fit to it |

**TOTAL: 100 code lines** for those terms. A code line is a line that is not
blank and is not a comment. The file is 291 lines and 133 code lines. The
difference is the module header and the imports.

**THE FOUR ARROWS, AND NO PRODUCT ANYWHERE.** `descent-core` maps a pair in
`⟪δ⟫ × ⟪δ⟫` down by the descending arrow, applies `sq (fst κ)`, and lifts by
`mem-incl`. The type of `descent-gives-sq` names no product of two L-sets, and
the body forms none. `[LJ-1.386]` measured that `src/` holds no such product
(`agents/tasks/LJ-1-386/lj-1.386-report.md:130-136`), and this route never
needs one.

**PART 4 FITS THE CONSUMER'S OWN TYPE.** The consumer takes `δ` as a bare
`V ℓ` (`src/L/StageCardinal.lagda.md:17-20`), and `descent-closes` takes an
L-element. `plugs-in` (`Probe390.agda:250-252`) closes that gap: a member of
`sucV α₀` is an ordinal by `band-ord`, and every ordinal is an L-element by
`isL-ord` (`agents/tasks/LJ-1-386/Probe386.agda:82-83`).

## 2. `descent-owes`, and why it is not the conclusion in disguise

```agda
descent-owes =
  (a : S) → IsOrd (fst a) → (⟨ fst a ∈ ω ⟩ → Empty.⊥)
  → (fst a ≡ ω)
  ⊎ (Init (fst a)
  ⊎ ((IsCardinalL a × sq (fst a))
  ⊎ (Σ[ κ ∈ S ] (⟨ fst κ ∈ fst a ⟩
               × (⟨ fst κ ∈ ω ⟩ → Empty.⊥)
               × ∥ Σ[ A ∈ Mem (Lset (SiteBound.β a)) ]
                     InjCode (SiteBound.up a A) a κ ∥₁))))
```

**CLAUSE 1, CLOSED.** `descent-owes` is a `Type`, not a family. It takes no
parameter of `descent-closes`'s telescope.

**CLAUSE 2, NO `sq` AT A BOUND VARIABLE.** The only `sq` in the type is
`sq (fst a)` under `IsCardinalL a`. That `a` is quantified by `descent-owes`
itself. It is not a variable that `descent-closes` binds.

**CLAUSE 3, THE ONE LINE.** See VERDICT.

**WHY THIS IS THE WEAKEST THAT CLOSES.** The brief said not to assume the
residue is `IsCardinalL → Init`. The recursion needs `sq` at the cardinal.
`Init` stays as a disjunct because it is a delivered supplier
(`via-col-square` at `src/L/Ordinal/SquareLaw.lagda.md:960-961`). Dropping it
would force an Init non-cardinal to inhabit the coded-descent disjunct, and
`¬ IsCardinalL` does not deliver that witness as data. Adding
`IsCardinalL a × sq (fst a)` is the extra disjunct the brief asked for: a
non-Init cardinal is served by `sq` itself.

**WHAT THE RESIDUE ASKS FOR, BY CASE.**

| The ordinal `a` | What `descent-owes` demands |
|---|---|
| `a ≡ ω` | nothing. `squareω` serves it (`src/L/InjChain.lagda.md:184-185`) |
| `Init a` | nothing further. `via-col-square` serves it |
| `a` is an internal cardinal, not Init | `sq (fst a)`. The fourth disjunct is refuted by `owes-third-refuted` |
| `a` is not an internal cardinal | ONE coded injection out of `a` into a smaller infinite ordinal |

**THE CODED-DESCENT ROW IS THE ROUTE'S ONE GAIN OVER THE PRODUCT ROUTE.** The
product route asks for a coded injection out of the internal square of `a`
(`agents/tasks/LJ-1-386/Probe386.agda:287-290`). The descent route asks for
one out of `a` itself.

**THAT ROW IS ALSO UNMEASURED.** `InternalLeastCard.Selected.δ-inj` carries an
object of that shape, but only under its `nonempty` hypothesis
(`src/L/Cardinal.lagda.md:243-258`). This probe did not discharge that
hypothesis at any `a`.

## 3. The price, side by side

**NEITHER ROUTE IS PRICED END TO END. THE TWO NUMBERS BELOW ARE THE BUILT
HALVES, AND THEY ARE NOT THE ROUTES.**

| | Product route | Descent route |
|---|---|---|
| Built and green | the internal product and its bridge: 125 code lines, 1.39 s (`agents/tasks/LJ-1-388/lj-1.388-report.md:23-24`) | the whole descent machine: **100 code lines, 1.89 s** (this file) |
| Sets it must build first | one, the internal product | **none** |
| Payoff term | `leg1-gives-sq`, 9 lines (`agents/tasks/LJ-1-386/Probe386.agda:294-302`) | `descent-core` and `descent-gives-sq`, 26 code lines |
| Still owed | the coded injection out of the internal square, at every band ordinal | `descent-owes`: `sq` at non-Init internal cardinals, one coded injection elsewhere |

**THE COMPARISON THE CAMPAIGN CAN ACT ON IS THE SHAPE OF THE TWO DEMANDS.**
The product route owes one object at every band ordinal. The descent route
owes `sq` only at the internal cardinals in the band, and a weaker object
everywhere else.

## 4. W3: the widest unmeasured term, and its probe

**THE WIDEST UNMEASURED TERM IS `sq (fst a)` AT AN INFINITE INTERNAL CARDINAL
`a`.** That is the third disjunct of `descent-owes`. The tree supplies `sq`
at ω (`src/L/InjChain.lagda.md:184-185`) and under `Init`
(`src/L/Ordinal/SquareLaw.lagda.md:960-961`). Nothing in the tree supplies
`sq` at a non-Init cardinal other than ω.

**THE PROBE THAT MEASURES IT.** Build `IsCardinalL a → (⟨ fst a ∈ ω ⟩ → Empty.⊥)
→ sq (fst a)` at generic `a`, in its own task directory. **The probe should
be built to REFUTE.** A NO-GO there ends the descent route on evidence and
leaves the product route the only one.

**NO LINE FIGURE.** `[LJ-1.337]` priced the three easy conjuncts of `Init`
(`agents/tasks/LJ-1-337/lj-1.337-report.md:216-225`), which is a comparable
of shape and not of this `sq`. The Boundary forbids the transfer.

## 5. W2 AND DD4

Both terms are at generic `δ` and `κ`. `descent-gives-sq` takes `(δ κ : S)`.
`descent-closes` takes an arbitrary `δ : S` in the band. No fixed site, and
in particular no `+ω ω`. `[LJ-1.386]` measured that nothing in the tree
certifies `+ω ω` as a band ordinal
(`agents/tasks/LJ-1-386/lj-1.386-report.md:213-217`).

## 6. The measurement that cost the most, and its cure

**THE SAME MATHEMATICS COST 175.42 s IN ONE TERM AND 1.54 s IN TWO**, measured
2026-08-19 under `-A64m -I0 -M8g`, recorded at `Probe390.agda:255-291`. I did
not re-run those six controls. I re-measured the full file today at 1.89 s.
The cure is: take the descending arrow as a parameter (`descent-core`,
`Probe390.agda:110-131`) and apply `code-untruncates` once outside it
(`descent-gives-sq`, `Probe390.agda:135-142`).

**THE CURE DOES NOT TRANSFER BY ANALOGY.**

## 7. What this report does NOT claim

- **It does not claim the square law at any ordinal.** Every term here is
  conditional. `descent-closes` takes `descent-owes`, and nothing inhabits
  `descent-owes` today.
- **It does not claim a bijection or an equivalence anywhere.** Every arrow
  built here is an injection in the sense of `_↪_`
  (`src/L/Cardinal.lagda.md:47-48`).
- **It does not claim the descent route is cheaper than the product route.**
  Both residues are unpriced. Section 3 gives the built halves only.
- **It does not claim the recursion is new.** `[LJ-1.337]` built it first
  (`agents/tasks/LJ-1-337/ProbeLJ1337B.agda:203-204`). What this task adds is
  the supplier `descent-gives-sq` for that probe's open branch
  (`agents/tasks/LJ-1-337/lj-1.337-report.md:262-263`) and a residue that
  names `sq` at the cardinal rather than only `Init`.
- **It does not measure the `nonempty` hypothesis of `InternalLeastCard`.**

## ARCHIVE USED

**THE ARCHIVE ALREADY NAMED THIS ROUTE AND ALREADY NAMED THIS RESIDUE.**

| Injected path | Read | What it gave |
|---|---|---|
| `archive/src/2026-08-09-rud-route/L/Ordinal/SquareLaw.lagda.md` | `:957-962` | **The descent and its residue, both stated.** |
| `archive/src/2026-08-09-rud-route/L/Ordinal/Pairing.lagda.md` | `:12-15` | the archived wall, quoted in section 7 |
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
cardinal" is the fourth disjunct. "At the cardinals themselves the counting
must still verify the three initiality clauses" is the second disjunct, and
the third disjunct is the weaker `sq` the brief asked for.

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

**THE LITERATURE DOES NOT SHOW THIS SHAPE IS AN AXIOM.** It shows the
opposite. The square law of infinite ordinals is a theorem of ZF, and the
classical proof is the Godel pairing. So there is no literature NO-GO here,
and the task proceeds.

**`dev/literature/truncation-and-selection.md:334-336`:**

> each element to the least unused target fails at order type `ω · 2` into
> `ω`. **A canonical injection needs a well-order on the INJECTIONS, which is
> what `<_L` supplies classically and what an ambient function type does not

**THIS IS WHY `code-untruncates` WORKS AND WHY ITS CONVERSE IS HARD.** The
door well-orders the CODES, by `orderAt` over the members of `Lset β`
(`agents/tasks/LJ-1-386/Probe386.agda:270-284`). The digest says an ambient
function type gives no such well-order. So the digest predicts that the
ambient-to-coded direction is the hard one. Section 4 names `sq` at an
internal cardinal as the widest unmeasured term, which does not need that
converse.

**`dev/literature/devlin-II5.md:280-282`:**

> (ii), |L_α| = |α| for infinite α (1.1(vii)), and the cardinal fact
> |γ| = |α| < κ with κ a cardinal implies γ < κ (`dev2.txt:1372-1384`).
> Strength: parts (i) and (ii) of condensation only, plus the level-size

**THE CLASSICAL ROUTE SPENDS CARDINAL ARITHMETIC, NOT A CODED DESCENT.**
Devlin uses the level-size equation and initial-ordinal arithmetic. Neither
is a coded injection. So the literature gives this route no comparable and
no price.

**`dev/literature/terms-2026-08.md:37`:**

> | 8 | square law | 平方律 | no literature under that name; the fact is 无穷基数的平方等于自身；no source uses 平方定理 for it | yes |

**THE FACT IS STATED AT CARDINALS.** The consumer at
`src/L/StageCardinal.lagda.md:17-20` asks for it at every ordinal of the
band. The descent is what bridges those two statements.

**DECLINED, WITH THE REASON.** `dev/literature/rudimentary-functions.md` holds
the rud-route source notes; `grep -n -i "square law"` over it returns nothing,
and the rud route is archived. `dev/literature/devlin-errata.md` is a
do-not-repeat checklist for Devlin's errors; its only cardinality line is
`:136`, about a Π1 and Σ1 pair, which bears on no term here.

## THE TREE AS I LEAVE IT

**I changed two files and both are mine:** `agents/tasks/LJ-1-390/Probe390.agda`
and `agents/tasks/LJ-1-390/lj-1.390-report.md`. The brief `LJ-1.390.md` is
modified in the working tree by the program (`head_slot: coder`). I ran no
`git add`, no commit and no push.

**GATES, run from the repository root with
`/Users/alsg/Agentic/Bedrock/.venv/bin/python` (this worktree has no `.venv`).**

- `scripts/gate/lint-agda.py --check` on `Probe390.agda`: exit 0
- `scripts/gate/check-probes.py --check`: exit 0, 3703 tracked files
- `scripts/pod/check-survey-quotes.py LJ-1.390`: exit 0, clean
- `scripts/gate/check-fences.py --check`: exit 0
- `scripts/gate/check-glossary.py --check`: exit 0
- `scripts/site/weave-i18n.py --check`: exit 0
- `scripts/pod/check-spec-surface.py --check`: exit 0
- `scripts/pod/check-closure.py --check closure`: exit 0
- `scripts/gate/lint-prose.py --check`: exit 0
- `scripts/measure/check-unbound-hyp.py --check`: exit 1, five hypotheses, all
  in `src/`, none in this task's files
- No em dash (U+2014) in either file I wrote

**I did not run `make check`.** A cold typecheck of the tree takes about twelve
minutes. I ran the probe and the individual checks.

**I wrote nothing under `agents/tasks/LJ-1-388/`.** I did not touch `src/`.
