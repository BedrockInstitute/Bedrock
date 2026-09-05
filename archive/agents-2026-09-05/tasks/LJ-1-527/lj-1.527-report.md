# LJ-1.527 report: row two, which costs almost nothing, and the census that does not

**VERDICT: GO.** The obligation is written and it typechecks.
`agents/tasks/LJ-1-527/Probe527.agda:184-200`, exit 0,
`runs/full-t-t2.out`.

    body-unbounds :
        (α : V ℓ) → IsLimit α
      → ∀ {m} (ψ : Formula S (suc (suc (suc (4 + m))))) (sv b f K : Fin m)
      → (γ : S ^ (4 + m))
      → fst (lookup (suc (suc (suc (suc K)))) γ) ≡ Lset α
      → ⟨ fst (lookup (suc zero) γ)
          ∈ fst (lookup (suc (suc (suc (suc K)))) γ) ⟩
      → ((x c val : S) → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ ψ ⟩
                       → ⟨ (val ∷ c ∷ x ∷ γ) ⊨ DefBody (suc zero) ⟩)
      → ((x : S) → ⟨ (x ∷ γ) ⊨ leafFo (suc zero) ⟩
                 → ⟨ (x ∷ γ) ⊨ leafBFo (suc (suc (suc (suc K)))) ψ ⟩)
      → ⟨ γ ⊨ StepB.bodyB {m} ψ sv b f K ⟩
      → ⟨ γ ⊨ StepBody b f ⟩

**W3 IS GO, ON THE FIRST RUN.** `sh4` is `suc⁴` at both slots.
`agents/tasks/LJ-1-527/runs/W3.agda:67-81`, exit 0, `runs/w3-0.out`.

**THE BRIEF SAID TO SAY SO IF ROW TWO COSTS ALMOST NOTHING. IT DOES:
four lines of term and 1.62 s.** The brief also said the census is the
real deliverable, and the census returned one thing the brief did not
predict, which is section `## THE MEMBERSHIPS ROWS THREE TO SIX WANT`
below: **rows three, four and five are already BUILT as terms, in
`agents/tasks/LJ-1-304/ProbeLJ1304A.agda`, at the AMBIENT carrier.**
`[LJ-1.525]`'s row-4 note cites `[LJ-1.250]`'s refutation and does not
cite `[LJ-1.304]`'s build, which came 54 dispatches later and overturned
it. A brief for rows three to five that starts from `[LJ-1.525]`'s table
alone will re-buy work that exists.

## THE ONE SENTENCE FOR THE NEXT BRIEF

**The three memberships rows three and four want are named, as types, at
`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:176-182`, and they are `wK`,
`dK` and `zK`.** Two of the three reduce: `zK` is `dK` plus the
transitivity of a level, which `src/` delivers as `layer-trans
(Lset-layer α)` (`src/L/Constructible.lagda.md:183`, `:246`). **So the
whole of rows three and four rests on TWO facts about `K`, not five**,
and one of the two, `wK`, is already a field of a delivered `src/`
module (`src/L/Condensation.lagda.md:6615-6616`).

## D-10, BEFORE ANY AGDA

The brief ordered it first: "`suc⁴ b` and `sh4 b` must be the same
index. **Check it at `file:line`.**"

### The check cannot be written as a function equality, and that is not the gap

`sh4` is PRIVATE (`src/L/Coding/Sequence.lagda.md:110-111`, inside the
`private` block that opens at `:109`). It cannot be named from a probe,
so no equality between the two FUNCTIONS `suc⁴` and `sh4` is writable.

**WHAT IS WRITABLE DECIDES THE SAME QUESTION.**
`runs/W3.agda:59-64` writes the step frame with its two index slots
OPEN, as arguments `B F : Fin (4 + m)`; it fixes no relation between
them and `b`, `f`. Then:

- `runs/W3.agda:67-72` supplies `suc⁴ b` and `suc⁴ f` and matches
  `StepB.bodyB` (`src/L/Condensation.lagda.md:2404-2408`), which is
  written with those numerals literally. `refl`.
- `runs/W3.agda:76-81` supplies **the same two indices** and matches
  `StepBody` (`src/L/Coding/Sequence.lagda.md:113-117`), which is
  written with `sh4`. `refl`.

The second holds only if `sh4 i` computes to `suc (suc (suc (suc i)))`,
at both slots. **IT DOES.** Exit 0 on the first run, `runs/w3-0.out`.

### So the two formulas differ in the leaf slot ONLY

`StepB.bodyB` and `StepBody b f` are one and the same frame, at the same
two indices, with `StepB.leafB` in one leaf slot and `DefAt zero (suc
zero)` in the other. **The brief's reading is confirmed and row two is
one congruence.** This restates `[LJ-1.525]`'s section 6
(`agents/tasks/LJ-1-525/Probe525.agda:250-259`), which used a frame with
the indices CLOSED; the open-index form above is what actually pins the
indices, because a closed frame would match both sides even if `sh4`
were some other shift applied consistently.

**I DID NOT STOP.** The brief's stop condition was "if they are not
[the same index], the two formulas differ in more than one slot and the
congruence is not one step". They are the same index.

## WHAT ROW TWO COST

**FOUR LINES OF TERM AND 1.62 SECONDS.**

| item | count |
|---|---:|
| section 3 in full, the obligation | **17** non-blank non-comment lines, `Probe527.agda:184-200` |
| of which the TYPE, carrying row one's five hypotheses | 13, `:184-196` |
| of which the TERM | **4**, `:197-200` |
| the congruence it calls, `frame-cong`, generic | 5 type + 5 term, `:163-174` |

Seconds, by subtraction over three forced rechecks each, same machine,
same caliber:

| what | median wall | difference |
|---|---:|---:|
| `runs/Control527.agda`, the import list, NO term | 2.60 s | the chapter load |
| `runs/Sections12.agda`, row one rebuilt plus `frame-cong` | 5.36 s | **+2.76 s** |
| `Probe527.agda`, all three sections | 6.98 s | **+1.62 s, and that is row two** |

**1.62 s FOR FOUR LINES IS NOT NEAR ZERO, AND THE REASON IS NOT THE
MATHEMATICS.** `frame-cong` alone costs nothing measurable: it is inside
the 2.76 s that also holds the whole of row one. What costs is
INSTANTIATING it, at `StepB.leafB ψ sv b f K` and `DefAt zero (suc
zero)` and at `StepB.bodyB`'s unfolding to the frame. That is the tree's
own instantiation class, P-m, and `[LJ-1.525]` measured the same effect
one row down at 20.37 s for a pure instantiation
(`agents/tasks/LJ-1-525/lj-1.525-report.md:161`). **A brief that funds a
congruence row against the four lines of its term will be wrong by
whatever the instantiation costs at that row's arity.**

## WHAT THE STATEMENT COSTS, AND WHAT IT DOES NOT

**ROW ONE'S FIVE HYPOTHESES RIDE INTO THE CONCLUSION UNCHANGED. NONE IS
DISCHARGED AND NONE IS HIDDEN.** They are `α` with `IsLimit α`;
`fst (lookup (suc⁴ K) γ) ≡ Lset α`; the carrier at slot one lies in `K`;
the ψ-level leaf agreement; and `bwd`, the machine-to-story leaf
direction. `[LJ-1.525]`'s own table of the five
(`agents/tasks/LJ-1-525/lj-1.525-report.md:112-122`) applies here word
for word, because this task added nothing to it and took nothing from
it.

**ROW TWO ADDS NO SIXTH HYPOTHESIS.** `frame-cong`
(`Probe527.agda:163-174`) takes one argument beyond the frame: the map
on the leaf slot. Row one is that map. The other three conjuncts are
carried by `h .fst`, `h .snd .fst` and `h .snd .snd .snd`, untouched.

**THE `K`-IS-A-LEVEL GAP IS STILL OPEN AND THIS TASK DID NOT TOUCH IT.**
`[LJ-1.522]` recorded it and `[LJ-1.525]` inherited it
(`agents/tasks/LJ-1-525/lj-1.525-report.md:130-137`). Row two inherits
it in turn.

**THE CERTIFICATE WAS NOT SPENT.** `Σ₁-levelHood`
(`src/L/BoundedSubset.lagda.md:145`) is not named anywhere in
`Probe527.agda`, and `σ₁-up` (`src/FOL/Absoluteness.lagda.md:182`) is
not named either. `grep -c "Σ₁-levelHood\|σ₁-up" agents/tasks/LJ-1-527/Probe527.agda`
returns 0.

**NOTHING WAS POSTULATED.** `grep -c postulate agents/tasks/LJ-1-527/Probe527.agda`
returns 0, and the file carries `--safe`.

## THE MEMBERSHIPS ROWS THREE TO SIX WANT

**THE FINDING FIRST.** `[LJ-1.525]`'s table names rows three to six as
undelivered and cites, for row four, `[LJ-1.250]`'s refutation
(`archive/dev/LJ-dispatch-index.md:319`). **Fifty-four dispatches later
`[LJ-1.304]` BUILT the same two stems**
(`archive/dev/LJ-dispatch-index.md:361`), and the build names every
membership rows three, four and five want, as a type, in one telescope:
`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:176-182` and `:283-293`.

**THE QUALIFICATION THAT DECIDES HOW MUCH OF IT TRANSFERS, AND IT IS
LARGE.** `[LJ-1.304]` runs at the AMBIENT class, `P1297A.Full`
(`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:74`), not at `𝒮ʟ`, and against
the GENERIC port `LJ-1-238.GenSequence` (`:74-79`), not against
`src/L/Coding/Sequence`'s `StepAt`. At the ambient class the step's two
side conditions are inhabited by `tt*`
(`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:185-189`); at `𝒮ʟ` they are
`PowOK` (`src/L/Coding/Sequence.lagda.md:130-131`) and are not trivial.
**AGENTS.md:45 governs: a measured cure does not transfer by analogy.**
What transfers without re-measurement is the LIST OF MEMBERSHIPS, which
is what the brief asked for. What does not is the wrapper's price.

### Row three: `witB` against the three unbounded existentials

`StepB.witB`, `src/L/Condensation.lagda.md:2410-2415`, against
`∃̇ (∃̇ (∃̇ (StepBody b f)))` inside `StepAt`,
`src/L/Coding/Sequence.lagda.md:119-120`. Direction bounded to machine
is free: drop three bounds. Direction machine to bounded is the one that
buys memberships, and `extAtB→extAt` needs BOTH, so both are owed.

| membership | as a type | status |
|---|---|---|
| the argument `c` lies in the domain bound `b` | `⟨ fst c ∈ fst (lookup b γ) ⟩` | **FREE, and this is a finding.** It is the machine's OWN first conjunct, `var (suc (suc zero)) ∈̇ var (sh4 b)` at `src/L/Coding/Sequence.lagda.md:114`. The bounded side's outer `∃̇∈ (var (suc b))` asks for exactly it. No membership is bought. |
| the recorded value `w` lies in `K` | `(c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩ → ⟨ fst w ∈ fst (lookup K γ) ⟩` | **delivered in `src/` AS A HYPOTHESIS, never inhabited.** It is the second component of `DomainAgree`'s `entryK`, `src/L/Condensation.lagda.md:6615-6616`. **delivered in a probe as the same hypothesis**, `wK` at `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:176-177`. Nothing in the tree PROVES it. |
| the definable powerset `d` lies in `K` | `(c w : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩ → ⟨ 𝒟ₒ (fst w) ∈ fst (lookup K γ) ⟩` | **delivered in a probe as a hypothesis**, `dK` at `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:178-179`, which that task's own header calls out as staying a hypothesis (`:26-28`). **Stated nowhere in `src/`.** The nearest `src/` statement is `PowOK` (`src/L/Coding/Sequence.lagda.md:130-131`), which concludes `⟨ isL (𝒟ₒ (fst w)) ⟩`, CONSTRUCTIBLE and not IN `K`. It is strictly weaker and it is not this. |

### Row four: `stepBndAt` against `StepAt`

`StepB.stepBndAt`, `src/L/Condensation.lagda.md:2417-2418`, against
`StepAt v b f`, `src/L/Coding/Sequence.lagda.md:119-120`. It is a second
`extAtB→extAt` (`src/L/Condensation.lagda.md:2514-2521`), so it wants
row three in both directions plus one `inK`.

| membership | as a type | status |
|---|---|---|
| the STEP's value lies in `K` | `(c w x : S) → ⟨ pr (fst c) (fst w) ∈ fst (lookup f γ) ⟩ → ⟨ fst x ∈ 𝒟ₒ (fst w) ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩` | **delivered in a probe as a hypothesis**, `zK` at `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:180-182`, and spent at `:258` through the local `zK-step` at `:260-262`. **Stated nowhere in `src/`.** |

**AND IT REDUCES, WHICH IS THE SECOND FINDING.** `zK` is `dK` followed
by the transitivity of `K`. `src/` delivers that transitivity for a
level: `layer-trans` (`src/L/Constructible.lagda.md:183`) applied to
`Lset-layer` (`:246-247`), which is the same pair `src/` already uses at
`:382`. **So rows three and four together rest on TWO facts about `K`
and not three**, given the frame hypothesis `fst (lookup K γ) ≡ Lset α`
that row one already carries. `[LJ-1.525]` said row four "asks the same
question this task answered, one level out and about a bigger object"
(`agents/tasks/LJ-1-525/lj-1.525-report.md:205-207`). **Measured here:
it does not. Row one's answer went through `defPow-closed-noCode`, which
is about a MEMBER of the definable powerset; row four's goes through
`dK`, which is about the definable powerset ITSELF. They are different
statements and the second is the one nothing proves.**

### Row five: `approxBndAt` against `ApproxAt`

`ApproxB.approxBndAt`, `src/L/Condensation.lagda.md:2471-2477`, against
`ApproxAt f a`, `src/L/Coding/Sequence.lagda.md:286-289`. Two bounded
universals against two unbounded ones, plus `domB` against `domAt`.

| membership | as a type | status |
|---|---|---|
| the argument AND the recorded value of every entry lie in `K` | `(c z : S) → ⟨ pr (fst c) (fst z) ∈ fst (lookup f γ) ⟩ → ⟨ fst c ∈ fst (lookup K γ) ⟩ × ⟨ fst z ∈ fst (lookup K γ) ⟩` | **delivered in `src/` AS A HYPOTHESIS**: `DomainAgree`'s `entryK`, `src/L/Condensation.lagda.md:6615-6616`. **delivered in a probe as the same hypothesis**, `entryK` at `agents/tasks/LJ-1-304/ProbeLJ1304A.agda:291-293`. Nothing PROVES it. This one hypothesis serves both universals. |
| every member of the domain bound `a` lies in `K` | `(x : S) → ⟨ fst x ∈ fst (lookup a γ) ⟩ → ⟨ fst x ∈ fst (lookup K γ) ⟩` | **delivered in `src/` AS A HYPOTHESIS**: `DomainAgree`'s `domK`, `src/L/Condensation.lagda.md:6617`. It is what `DomainAgree.back` (`:6633`) spends. |
| row four, at the shifted environment | the row above, at `(z ∷ c ∷ γ)` | the same three, restated two slots deeper. `[LJ-1.304]` states them at the base slots and reports they "carry no binder dependence" (`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:269-272`). |

**`domB` AGAINST `domAt` IS THE ONE ROW OF THE SIX THAT IS DELIVERED IN
`src/` AS A TERM.** `DomainAgree.out` (`src/L/Condensation.lagda.md:6624`)
and `.back` (`:6633`) are both built, under `entryK` and `domK`. No new
membership is bought there.

### Row six: `graphBndAt` against `LsetGraphAt`

`GraphB.graphBndAt`, `src/L/Condensation.lagda.md:2492-2493`, against
`LsetGraphAt w b`, which is `RecShape.GraphAt` at `Step := StepAt`
(`src/L/Coding/Sequence.lagda.md:291-292`, renamed at `:349`).

| membership | as a type | status |
|---|---|---|
| the APPROXIMATION FUNCTION itself lies in `K` | `(g : S) → ⟨ γ ⊨ ApproxAt-at-g ⟩ → ⟨ fst g ∈ fst (lookup K γ) ⟩`, i.e. the witness of the machine's outer `∃̇` lies in `K` | **STATED NOWHERE.** Not in `src/`, not in any probe I found. `grep -rn "graphBndAt\|GraphAgree" agents/tasks/` returns no build; the only hits are prices and reviews. |

Direction bounded to machine is free: `∃̇∈ (var K)` forgets its bound and
becomes `∃̇`. **The whole of row six's cost is the other direction, and
its whole content is that one membership.** `[LJ-1.228]` priced the
two-way decode at "150 to 250 probe lines" and recorded that "Nobody ran
it" (`agents/tasks/LJ-1-228/lj-1.228-report.md:128-130`). That is still
true today.

### The three-way split, collected

| bucket | which |
|---|---|
| **delivered in `src/`** as a TERM | `domB` against `domAt`, both directions (`src/L/Condensation.lagda.md:6624`, `:6633`); `K`'s transitivity from `K ≡ Lset α` (`src/L/Constructible.lagda.md:183` with `:246-247`) |
| **delivered in `src/`** as a HYPOTHESIS nothing inhabits | `entryK` (`src/L/Condensation.lagda.md:6615-6616`), which covers row three's `w ∈ K` and both of row five's; `domK` (`:6617`) |
| **delivered in a probe**, at the AMBIENT carrier and the generic port | the row three plus four wrapper, `StepAgree.step-agree` (`agents/tasks/LJ-1-304/ProbeLJ1304A.agda:254-258`); the row five wrapper, `ApproxAgree.approx-agree` (`:313-316`). Both under `wK`, `dK`, `zK`, and the second also under `domAgree` and `entryK`. |
| **stated nowhere** | `dK`, the definable powerset of a recorded value lies in `K`, stated only as a probe hypothesis and PROVED by nothing; row six's approximation-function membership, stated by nothing at all |

**SO THE CHAIN'S REMAINING MATHEMATICAL CONTENT IS TWO FACTS AND ONE
RE-MEASUREMENT**, not four rows: prove `dK`, prove row six's
membership, and re-measure `[LJ-1.304]`'s two wrappers at `𝒮ʟ` against
`src/L/Coding/Sequence` rather than at the ambient class against the
generic port.

## THE PRICE

Three forced rechecks each, five for the full file. The file's own
interface was removed before every run, so each number is a real
recheck. `GHCRTS="-A64m -I0 -M8g"`, the wide caliber, set on the pane by
the program and untouched. ONE Agda process per run.

| file | median wall | peak RSS | runs |
|---|---:|---:|---|
| `runs/W3.agda` alone | **3.03 s** | 599,638,016 B | `runs/w3-t-t1.time` to `w3-t-t3.time` |
| `runs/Control527.agda` | **2.60 s** | 605,290,496 B | `runs/ctl-t1.time` to `ctl-t3.time` |
| `runs/Sections12.agda` | **5.36 s** | 656,588,800 B | `runs/s12-t1.time` to `s12-t3.time` |
| `Probe527.agda`, full | **6.98 s** | 696,549,376 B | `runs/full-t-t1.time` to `full-t-t5.time` |

All fourteen timed runs exited 0.

**SIZE.** `Probe527.agda` is 200 lines, of which **123** are non-blank
and not a comment. `runs/W3.agda` is 81 lines, of which **33** are
non-blank and not a comment.

**AGAINST THE BRIEF'S ESTIMATE.**

| item | brief | measured |
|---|---|---|
| W3 | about 10 lines, under 25 s | **33 lines, 3.03 s** |
| the probe | about 140 lines | **123 lines** |
| the obligation | about 20 lines | **17 lines, of which 4 are term** |

**THE TIME ESTIMATE WAS HIGH AND THE LINE ESTIMATE FOR W3 WAS LOW.** W3
came in at 3.03 s against 25 s, and 2.60 s of that is the chapter load
that no term of mine pays for: W3's own two `refl`s cost **0.43 s**. It
took 33 lines rather than 10 because `sh4` is private, so the comparison
had to be routed through an open-index frame instead of written as one
equality between two `Fin`s. **The brief's shape was right and only its
form was unavailable.**

**NO WALL EVENT.** No heap exhaustion and no rerun after a wall. Peak
RSS is 696,549,376 B against an 8 GB cap, about one twelfth of it.

**ONE FIRST-RUN ERROR, AND IT WAS SCOPE AND NOT MATHEMATICS.** An
implicit `{m}` was written in a clause body that did not bind it
(`runs/full-0.out`, exit 42, `[NotInScope]`). Deleting the implicit
fixed it. No unsolved meta and no universe-level error at any point.

## THE CLAUSES ANSWERED

**W2, the generic carrier.** ANSWERED AND OBEYED. The congruence is
written once at `frame-cong` (`Probe527.agda:163-174`), which fixes no
arity, no index and no leaf: it is a fact about a four-place conjunction
with a hole. The obligation (`:184-200`) is one instantiation of it and
adds no content. **It would carry any other frame of the same shape at
the same price**, so the two towers share it if the second tower's step
is a conjunction with a leaf slot. Nothing here is written at a fixed
form and there is no conflict to report.

**W3, the widest unmeasured term.** WRITTEN FIRST AND ALONE, typechecked
before `Probe527.agda` existed. GO. See `## D-10, BEFORE ANY AGDA`.

**W4, the retirement rule.** NOTHING WAS RETIRED. This task lands
nothing in `src/`, moves no module and writes no `dev/ARCHIVE.md` row.
The ideal form of row two written fresh today IS the four lines at
`Probe527.agda:197-200`, because the congruence has no other shape; so
the comparison W4 asks for is empty here.

**THE RATIO BAR.** `Probe527.agda` and `runs/W3.agda` are raw `.agda`
files and carry no ` ```agda ` fence, so the divisor is 0 in-fence lines
and the bar cannot fire. Nothing was landed under `src/`.

**NEVER COMMIT AND NEVER PUSH.** Nothing was committed and nothing was
pushed. `git status --porcelain` returns the single line
`?? agents/tasks/LJ-1-527/`, which holds three of the four scope paths:
`Probe527.agda`, `lj-1.527-report.md` and `runs/`. The fourth,
`review-of-body-unbounds.md`, is NOT written, because this is a GO and
that file is how a NO-GO is stated.

## ARCHIVE USED

Every CANDIDATE the brief listed is named below.

- **`archive/dev/LJ-dispatch-index.md`: READ, AND IT CARRIES THE
  FINDING OF THIS TASK.** Two rows decided the census.
  `archive/dev/LJ-dispatch-index.md:319` reads
  "| LJ-1.250 | Price StepAgree and ApproxAgree | NEITHER BUILDS: UNCONSTRAINED INTERFACES. DD25 [LJ-1.251] | Refutable at that generality. The residue is the leaf-adequacy supply, not one term |",
  which is the refutation `[LJ-1.525]` cites for row four.
  `archive/dev/LJ-dispatch-index.md:361` reads
  "| LJ-1.304 | Price StepAgree and ApproxAgree | BOTH BUILT, ABOUT 190 LINES. BASIS: THE BUILD | q's four named costs are now ALL measured. Neither module exists in src/: they were LJ-1.52's names |",
  which overturns it and pointed me at
  `agents/tasks/LJ-1-304/ProbeLJ1304A.agda`.
- **`archive/dev/JOURNAL.md`: READ, NOT USED.**
  `archive/dev/JOURNAL.md:809` reads
  "missing `Δ₀` cure**, because the tree already carries `Δ₀-extAtB`,".
  It is the only hit in that file for the bounded-frame vocabulary and
  it is about the `Δ₀` witnesses, not about any of the six rows. It
  bears on nothing here.
- **`archive/dev/JOURNAL-archived.md`: NOT USED, DECLINED.**
  `grep -n "StepB\|bodyB\|StepBody\|graphBndAt\|extAtB"` over it returns
  nothing, so it holds no record of this chain.
- **`dev/ARCHIVE.md`: NOT USED, DECLINED.** It records retired modules
  and this task retires none (see W4 above). The same grep returns
  nothing.
- **`archive/dev/DECISIONS-archived.md`: NOT USED, DECLINED.** It
  resolves the bare `D<n>` series. No `D<n>` code arose in this task,
  and the same grep returns nothing.

## LITERATURE USED

Every CANDIDATE the brief listed is named below.

- **`dev/literature/devlin-II5.md`: READ, AND IT NAMES WHAT THE CHAIN
  IS FOR.** `dev/literature/devlin-II5.md:99` reads
  "> (b) (∀γ < α)(∀v)[v = L_γ ↔ v ∈ L_α ∧ L_α ⊨ ∃z φ(z, v, γ)].",
  which is the Σ₁ level-hood statement the chain exists to serve:
  `levelHoodΣ₁` (`src/L/BoundedSubset.lagda.md:142-143`) is that `∃z φ`,
  and `Σ₁-levelHood` (`:145`) is its certificate. It confirmed for me
  that the six rows are the MEANING side of that biconditional and not
  a syntactic detour, and so that no row may be skipped. It gave no
  index and no membership, so it did not change any line of Agda.
- **`dev/literature/truncation-and-selection.md`: NOT USED, DECLINED.**
  Row two performs no selection: `frame-cong` never opens a `∥ ∥₁`. The
  truncations in this file are all inside row one's rebuilt term, where
  `[LJ-1.525]` already settled them.
- **`dev/literature/digest.md`: NOT USED, DECLINED.** It pins the rud
  route. This chain is the definable-powerset route, and the direction
  file rules no rud work in `[LJ-1]`.
- **`dev/literature/geology.md`: NOT USED, DECLINED.** Set-theoretic
  geology, for `[L6]`. Nothing to do with a formula congruence.
- **`dev/literature/terms-2026-08.md`: NOT USED, DECLINED.** A
  terminology dossier. This task names no new term and adds no
  `dev/glossary.toml` entry.

## WHAT I DID NOT DO

- **ROWS THREE TO SIX WERE NOT ATTEMPTED.** AD12 gives this brief one
  obligation and the brief forbade them. What is above is a census of
  their memberships, not a build.
- **THE CERTIFICATE WAS NOT SPENT.** The chain is incomplete.
- **`[LJ-1.304]`'S WRAPPERS WERE NOT RE-MEASURED AT `𝒮ʟ`.** I read them
  and I report what they state. Running them against
  `src/L/Coding/Sequence` is a task of its own and `AGENTS.md:45`
  forbids me to price it from theirs.
- **NOTHING WAS LANDED IN `src/`, NOTHING WAS COMMITTED, NOTHING WAS
  PUSHED.**
