# LJ-1.581 review: the brief's type is `[LJ-1.556]`'s type, and it is FALSE

## HEAD
head_slot: coder
machine: shared
verdict: STOP

**THIS IS A STOP AND NOT A HEAP EVENT, NOT A BUDGET EVENT AND NOT A RED PROBE.**
`agents/tasks/LJ-1-581/Probe581.agda` is green, exit 0 in 2.03 s
(`agents/tasks/LJ-1-581/runs/final-1.out:4`), and carries no hole and no
postulate. The program's own witness agrees: `missing exit=42`,
`probe_red=False` (`agents/tasks/LJ-1-581/runs/witness-2.out:3-4`).

**IT IS ALSO NOT A "THE TREE CANNOT REACH IT" STOP.** The obligation is not
merely unreachable. It is refuted, by a term that typechecks:
`obligation-false : Obligation → Empty.⊥` at
`agents/tasks/LJ-1-581/Probe581.agda:376`.

## 1. THE BRIEF SAYS IT DOES NOT RE-DISPATCH `[LJ-1.556]`'S TYPE. IT DOES.

The brief states, in `## THE OBLIGATION`: "**This brief does not re-dispatch
that type.** It asks for the CODE at one cardinal, which is what row 5 actually
consumes."

`[LJ-1.556]`'s type is written out at `agents/tasks/LJ-1-556/Probe556.agda:325`:

    BriefTarget = (κ : S) → IsOrd (fst κ) → IsCardinalL κ → InternalSquare κ

with `InternalSquare κ = ∥ Σ[ F ∈ S ] InjCode F (Square.sqL κ) κ ∥₁` at `:321-322`.

The brief's obligation is `(κ : S) → IsOrd (fst κ) → IsCardinalL κ` followed by
"an L-set injection CODE from the pairs of κ into κ". Section 1 of the probe
measures that "the pairs of κ" IS `Square.sqL κ` (`Probe581.agda:94`). So the
two types are one type, and two identity functions say so rather than a
sentence:

- `obligation-is-556-brieftarget x = x` (`Probe581.agda:133-134`)
- `brieftarget-556-is-obligation x = x` (`Probe581.agda:136-137`)

Both are `λ x → x`. The elaborator accepts them, so there is no difference to
argue about. **`[LJ-1.556]`'s own instruction to the next brief is
`agents/tasks/LJ-1-556/lj-1.556-report.md:300`: "DO NOT RE-DISPATCH THE BRIEF'S
TYPE."** My standing clause says the same: a module hypothesis taken from a
predecessor is the type that predecessor delivered, and if the report is NO-GO,
stop and say so.

## 2. AND THE TYPE IS NOT "UNDER-HYPOTHESIZED". IT IS FALSE.

`[LJ-1.556]` called the type under-hypothesized "against every route the tree
has" (`agents/tasks/LJ-1-556/Probe556.agda:351-352`). That is a statement about
routes. **This task measured the statement itself, which D-10 asks for before
any proof is priced, and the statement is false.**

The counterexample is κ := 2, the L-element `numeralL 2`
(`Probe581.agda:242-245`). Three facts, each a typechecked term:

1. **2 is an L-ordinal.** `κ₂-ord` (`Probe581.agda:262`), from
   `numeral-ord` (`src/L/Ordinal.lagda.md:244`).
2. **2 is an L-cardinal.** `κ₂-card` (`Probe581.agda:322`). Nothing is assumed:
   a code for an injection of 2 into a member of 2 is read down by `readL`
   (`src/L/CantorBernstein.lagda.md:33`), and a member of 2 holds at most one
   thing (`thin`, `Probe581.agda:226`), so the two distinct members of 2 have
   one image (`m₀≢m₁`, `Probe581.agda:284`).
3. **The pairs of 2 do not inject into 2.** `no-square-at-two`
   (`Probe581.agda:356`). Three of the four pairs are enough: 2 has exactly two
   members (`κ₂-two`, `Probe581.agda:288`), and three distinct things do not fit
   in two places (`pigeon`, `Probe581.agda:337`).

`IsCardinalL` (`src/L/Cardinal.lagda.md:230`) is the initial-ordinal condition
and every finite ordinal satisfies it. `IsOrd`
(`src/L/Constructible.lagda.md:141`) is hereditary transitivity and every finite
ordinal satisfies it. **Neither hypothesis excludes a finite κ, and the square
law is false at every finite κ above 1.**

## 3. `SquareStep`, THE CORRECTION `[LJ-1.556]` TOLD THE NEXT BRIEF TO FUND, IS FALSE TOO

This is the part that matters most, because it is where the next brief was
going. `agents/tasks/LJ-1-556/lj-1.556-report.md:300-301` says: "Fund
`SquareStep` (probe section 4) or fund nothing."

`SquareStep` (`agents/tasks/LJ-1-556/Probe556.agda:357-362`) adds the induction
hypothesis `(β : S) → IsOrd (fst β) → ⟨ fst β ∈ fst κ ⟩ → InternalSquare β`.
**The prose of section 4 says "THE SQUARE LAW AT EVERY SMALLER INFINITE ORDINAL"
(`Probe556.agda:340-341`). The Agda says every smaller ordinal, and the conclusion
is at an unrestricted κ.** So the same κ := 2 refutes it:

    squarestep-false : P556.SquareStep → Empty.⊥      Probe581.agda:387

**AND IT COSTS NO CONSTRUCTION.** No code is built anywhere in this file. The
induction hypothesis at 2 is supplied by `SquareStep` itself, used at 0 and then
at 1 first: at 0 the hypothesis is vacuous, and at 1 it is the value at 0,
because `fst β ≡ fst κ₀` gives `β ≡ κ₀` (`isL` is a proposition,
`src/L/Absorption.lagda.md:623`). The chain is `Probe581.agda:392-419`.

## 4. THE CORRECTED TARGET, AND IT IS ONE CLAUSE

`SquareStepInf` (`Probe581.agda:427`) is `SquareStep` with the clause the
tree's OWN square law already carries:

    ⟨ ω ∈ fst κ ⟩

That is the second conjunct of `Init` at
`src/L/Ordinal/SquareLaw.lagda.md:694`, which is the hypothesis of the ambient
chain this obligation was to internalize. The coded side of the tree carries the
same restriction in a different spelling: `shift-coded`
(`src/L/CodedShift.lagda.md:37-39`) takes `γ∉ω` and `numerals`, two infinity
hypotheses, for a strictly easier conclusion than the square law.

**AND THE COUNTEREXAMPLE DOES NOT REACH THE CORRECTED TARGET.**
`two-not-infinite` (`Probe581.agda:435`) shows κ := 2 does not satisfy the new
clause. `SquareStepInf` is NOT inhabited here, and naming it is the deliverable,
in exactly the way `[LJ-1.556]` named `SquareStep`.

## 5. THE SWEEP (C-42), BECAUSE A REFUTATION MEASURES ONE SITE

A refutation says nothing about how far the shape extends, so I counted before
proposing any cure. The shape is: **a conclusion that asserts a coded injection
or a square law at κ, under hypotheses that do not make κ infinite.** I read
every site that two greps returned: the sites that hypothesise `IsCardinalL`,
and the sites that conclude a coded injection.

**THE COUNT IS TWO, AND BOTH ARE IN `[LJ-1.556]`'s PROBE**
(`Probe556.agda:325` and `:357`). Both are refuted above.

Every other site carries an infinity clause already:

| site | the clause |
|---|---|
| `src/L/GCH.lagda.md:64` | `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)`, in the trophy statement |
| `src/L/Ordinal/SquareLaw.lagda.md:694` | `⟨ ω ∈ˢ α ⟩`, in `Init` |
| `src/L/Absorption.lagda.md:611-613` | `γ∉ω` and `numerals` |
| `src/L/CodedShift.lagda.md:37-39` | `γ∉ω` and `numerals` |
| `agents/tasks/LJ-1-368/Probe368.agda:79-80` | `κ∉ω` |
| `agents/tasks/LJ-1-390/Probe390.agda:163` | `(⟨ fst a ∈ ω ⟩ → Empty.⊥)` |
| `agents/tasks/LJ-1-398/Probe398.agda:181` | `⟨ ω ∈ a ⟩` |
| `agents/tasks/LJ-1-236/ProbeLJ1236A7.agda:153` | `(⟨ fst κ ∈ˢ ω ⟩ → Empty.⊥)` |

**SO THE CURE IS NOT A SWEEP. IT IS ONE CLAUSE IN ONE NEW TYPE**, and `src/` is
untouched by this finding.

**ONE THING THE SWEEP FOUND THAT THE NEXT BRIEF MUST NOT LOSE.** The consumer of
this obligation is row 5, and `[LJ-1.574]`'s `Obligation`
(`agents/tasks/LJ-1-574/Probe574.agda:766`) and `[LJ-1.549]`'s `Residue`
(`agents/tasks/LJ-1-549/Probe549.agda:668`) carry `SuccCardL δ κ` and NO
infinity clause. `GCHStatement` has the clause at `src/L/GCH.lagda.md:64`, so it
exists upstream. **It has to be threaded down to the square law, and today
nothing threads it.** I did not test whether those two types are true without
it; I measured only that a CODED SQUARE LAW cannot be stated without it.

## 6. WHAT THE STOP IS NOT

It is not W3. **W3 came out GO on the first run** (`runs/w3-1.out:23`, `EXIT=0`). The
pairs of κ are an L-set with two projections, and it is `[LJ-1.556]`'s section 1
object; the only thing to check was the bridge `prʟ-fst`
(`src/L/Coding/Model.lagda.md:329`).

It is not the readback. `square-from-code` (`Probe581.agda:193`) turns a code
into the ambient square injection, and it cost nothing. The direction the brief
wanted is the OTHER one.

It is not a price. **The price of this chapter fell by a factor of 90 during
this task**, and `## THE MEASURED CURE` of the report has every number of it.

## 7. WHAT WOULD REOPEN THIS

1. **FUND `SquareStepInf`** (`Probe581.agda:427`), or the same type with the
   `γ∉ω`-plus-`numerals` spelling that `src/L/CodedShift.lagda.md:37-39` uses.
   Nothing in this file inhabits it and nothing refutes it.
2. **THREAD THE INFINITY CLAUSE THROUGH ROW 5 FIRST**, because the consumer does
   not carry it today (section 5 above). That is a smaller task than the square
   law, and it decides the shape of the square-law brief rather than following
   it.
