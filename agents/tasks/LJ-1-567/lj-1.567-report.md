# LJ-1.567 report: the Step formula for `col`

## HEAD
head_slot: coder
machine: shared
verdict: GO

The report was written as a skeleton before any Agda and filled as each answer
landed (C-22). No commit, no push. I wrote only inside
`agents/tasks/LJ-1-567/`. Agda ran under the caliber the program set on this
pane, `GHCRTS="-A64m -I0 -M8g"`, ONE Agda process at a time. I did not set
`GHCRTS`. No heap event: the largest resident set was 486 MB against the 8 GB
cap (`agents/tasks/LJ-1-567/runs/final-1.out:5`). Nothing is postulated and no
hole is left, so every reduction in the probe is a measurement and not a claim.
Both files are raw `.agda`, so they carry no ` ```agda ` fence, count 0 in-fence
lines, and the ratio bar cannot fire on them.

## VERDICT

**GO. The obligation is inhabited.** `col-step` is at
`agents/tasks/LJ-1-567/Probe567.agda:259`. The program's own witness resolves
it: `pass exit=0 1.95s`, `probe_red=False`
(`agents/tasks/LJ-1-567/runs/witness-1.out:3`).

**W3 IS GO.** `RecShape` instantiates at `dom = Square.sqL κ` with nothing to
pay. The slice is `agents/tasks/LJ-1-567/runs/W3.agda`, 64 lines, green on the
first run.

**THE ORDER NEVER BECAME A SET.** The brief set that test: "If you find
yourself building an order-as-a-set, stop and say so". I did not build one at
any point, in any section. So `[LJ-1.556]`'s finding holds at this frame.

Three findings follow.

1. **`sucV` NEVER HAS TO BE AN ELEMENT OF THE MODEL.** The brief's step is
   `z = ⋃ { sucV (f r) : r ≺ c }`. The obvious route names the successor with
   `sucAtL` (`src/L/Coding/Model.lagda.md:1395`) and binds it. That costs a
   THIRD bound variable, and an object-language existential ranges over `L`, so
   the step would carry a closure side condition of the same shape as `PowOK`
   (`src/L/Coding/Sequence.lagda.md:130`), which the previous recursion pays at
   every call site. Written instead as the disjunction `x ∈̇ w ∨̇ x ≐ w`
   (`agents/tasks/LJ-1-567/Probe567.agda:141-142`) the successor is INSIDE the
   formula, the side condition disappears, and the two readings need only
   `∈sucV-elim` and `∈sucV-inl` (`src/V/Model.lagda.md:218`, `:230`). **This is
   the one measurement of this task that a chapter should copy.**

2. **THE STEP COSTS TWO BOUND VARIABLES AND NO MORE.** `ColBody`
   (`Probe567.agda:138`) binds the predecessor `r` and the recorded value `w`.
   The previous recursion's `StepBody` (`src/L/Coding/Sequence.lagda.md:113`)
   binds three, and the third is the definable powerset. The collapse's step is
   cheaper than the tower's step at the same shape.

3. **THE ADEQUACY OF AN ORDER DOES NOT FIT AT `Type (ℓ-suc ℓ)`.** `Order`
   (`Probe567.agda:94`) holds the order formula, the relation on `L`, and the
   reading that ties them. The reading is an equation of `Ω`, and `Ω` is itself
   at `Type (ℓ-suc (ℓ-suc ℓ))`. My first run was RED for exactly this:
   `ConstructorDoesNotFitInData` (`agents/tasks/LJ-1-567/runs/s1-1.out:4`). The
   record sits one universe higher. **A chapter that lands this record in
   `src/` pays one universe level, and it should know that before it writes the
   file, not after.**

## W3, THE WIDEST UNMEASURED TERM

The brief names it: "`RecShape` at this `dom`", TYPE ONLY, `Step` abstract, and
attaches one question, "If `RecShape` will not instantiate there, the formula
has nowhere to go."

**IT WAS WRITTEN FIRST AND TYPECHECKED ALONE, before any other Agda of this
task.** The slice is `agents/tasks/LJ-1-567/runs/W3.agda`, 64 lines, `Step` a
module parameter, three types written and NONE inhabited: `ColDomain`,
`ColApprox` and `ColGraph` (`runs/W3.agda:57`, `:60`, `:63`).

**GREEN ON THE FIRST RUN, exit 0.** `runs/w3-1.out` (198.06 s, everything
cold), `runs/w3-2.out` (2.04 s, own interface deleted, the imported probe
warm), `runs/w3-3.out` (2.03 s, after a comment-only citation fix). There is no
red predecessor.

**THE BRIEF ESTIMATED "about 15 lines, under 2 minutes". The measured numbers
are 64 lines and 2.03 s warm, or 198.06 s cold.** The cold number is NOT this
slice's price. `LJ-1-556.Probe556` is imported rather than transcribed, and
that probe alone costs 176.57 s on a cold interface
(`agents/tasks/LJ-1-556/runs/full-5.out:4`). So the import is paid once and the
slice itself is about 2 s. **I report the number I measured and not the number
the brief guessed.**

**THE ANSWER, AND IT IS WORTH ONE SENTENCE MORE THAN "YES".** `RecShape` holds
the domain in ONE environment slot of type `S` (`src/L/Coding/Sequence.lagda.md:286`,
`:291`). Nothing in the module inspects what is in that slot. So the
instantiation at `Square.sqL κ` is the same instantiation it would be at any
element of `L`, and it cannot fail for a type reason. **The risk the brief
priced is not there.**

## THE THREE `Fin n` ARGUMENTS OF `Step`, AT THIS INSTANTIATION

The brief asks for this before the formula. The answer is read off `ApproxAt`
(`src/L/Coding/Sequence.lagda.md:286`) and `ApproxAt-step`
(`src/L/Coding/Sequence.lagda.md:303`), which pin the three places:

| place | what it is | at `col` |
|---|---|---|
| first | THE VALUE `z` | the ordinal the collapse assigns to the argument |
| second | THE ARGUMENT `c` | a member of `Square.sqL κ`, so a coded pair |
| third | THE APPROXIMATION `f` | the partial collapse, readable ONLY through `appAt` |

The second place is where this instantiation differs from the tower's. In
`RecShape`'s `GraphAt` (`src/L/Coding/Sequence.lagda.md:291`) ONE variable `b`
serves both as the approximation's domain and as the step's argument, which is
correct for an ordinal, because an ordinal IS the set of its predecessors. **A
coded pair is not.** So at `col` the two roles separate: the approximation's
domain is `Square.sqL κ`, and the argument is one member of it. `ApproxAt`
already separates them (`f` and `a` are two variables), so nothing had to
change. **`GraphAt` does not separate them, and a consumer that wants the graph
at `col` will meet this.** It is not a defect of `RecShape`; it is a fact the
next brief needs.

## THE OBLIGATION

```
col-step : (O : Order) (κ f : S) → Approx O κ f → (c z : S)
         → ⟨ pr (fst c) (fst z) ∈ fst f ⟩
         → ( ((x : S) → ⟨ fst x ∈ fst z ⟩ → ∥ ColOf O f c x ∥₁)
           × ((x : S) → ColOf O f c x → ⟨ fst x ∈ fst z ⟩) )
```

`Probe567.agda:259`. In words: **take an approximation whose domain is
`Square.sqL κ`, and any pair the approximation records; then the recorded value
is exactly `⋃ { sucV (f r) : r ≺ c }`.**

`Approx O κ f` (`Probe567.agda:254`) is `RecShape`'s own `ApproxAt` at the
environment `(f ∷ Square.sqL κ ∷ [])`, so the domain the brief names is in the
obligation's type and not only in its prose. `ColOf O f c x`
(`Probe567.agda:150`) is one member of the union: a predecessor `r`, the value
`w` recorded there, and `x ∈ sucV w`.

**BOTH DIRECTIONS ARE DELIVERED, AND THAT IS NOT PADDING.**
`z = ⋃ { sucV (f r) : r ≺ c }` is a set identity. Read one way only it is an
inclusion, and an inclusion is not the step. The two halves are `StepFo-out`
(`Probe567.agda:207`) and `StepFo-in` (`Probe567.agda:213`), both stated at any
arity, so a consumer at another environment reuses them.

**THE ORDER IS A PARAMETER AND IT CARRIES NO SET.** `Order`
(`Probe567.agda:94`) has three fields: the formula with two free places, the
relation on `L` it is about, and the reading. It has no field of type `S`.
That is `[LJ-1.556]`'s finding, written as a type.

## WHAT I COPIED

**I copied by IMPORT and not by transcription, which is the strongest form of
"copy what is green".** `Probe567.agda:58` and `runs/W3.agda:42` both read
`import LJ-1-556.Probe556 {ℓ} lem as P556`. Zero lines of `[LJ-1.556]` were
re-derived, so zero lines could drift. Cross-probe import is established
practice in this tree: `agents/tasks/LJ-1-184/ProbeLJ1184C.agda:29` imports
`LJ-1-178.ProbeLJ1178A` the same way.

| taken | from | what I changed |
|---|---|---|
| `Square.sqL κ`, the domain | `agents/tasks/LJ-1-556/Probe556.agda:148` | nothing. Used as an atom. |
| the nesting idiom for reading stacked existentials | `agents/tasks/LJ-1-556/Probe556.agda:110-143` | widened from TWO binders to FOUR, in `FstFo-adequate` (`Probe567.agda:322`) |
| "env spelled out at both ends" | `src/L/Coding/Sequence.lagda.md:175` | nothing. Obeyed at `Probe567.agda:161` and `:329`. No environment abbreviation anywhere. |

**WHAT I COULD NOT COPY, AND WHY.** `ltFo`
(`agents/tasks/LJ-1-556/Probe556.agda:219`) and `ltL`
(`agents/tasks/LJ-1-556/Probe556.agda:269`) are the obvious candidates and
neither fits. Both are UNARY: one free place, a condition on ONE pair code. An
order is BINARY: two pair codes, four components, and a condition across them.
`AGENTS.md:45` refuses the transfer by analogy, so section 4 builds the binary
shape and reads it at its own site.

**`Square.sqL κ` IS `opaque` (`agents/tasks/LJ-1-556/Probe556.agda:147`), AND
THAT IS WHY THE PRICE IS FLAT (P-l).** The obligation's type names a concrete
domain, but that domain is an ATOM to the elaborator, so nothing unfolds when
the type is checked. The whole probe is 372 lines at 1.67 s warm, which is
0.0045 s per raw line. **This number is a SHAPE and not a price for any master:
raw lines are not in-fence lines, and a `.lagda.md` master carries prose the
ledger does not count and Agda does not check.**

## WHAT SQUARESTEP STILL WANTS

Given `col-step`, `SquareStep` (`agents/tasks/LJ-1-556/Probe556.agda:357`)
still wants three things, and I did not build any of them.

First it wants an order that is a WELL-order on `Square.sqL κ`, delivered as a
formula with a reading, because `col-step` accepts ANY binary relation and a
collapse needs well-foundedness and totality, which section 4's witness has
neither of. Second it wants the recursion itself, that is, an `f` that
satisfies `Approx O κ f` over the whole of `Square.sqL κ`, because `RecShape`
states the approximation and the graph but no chapter builds either at this
domain today. Third it wants `[LJ-1.556]`'s induction hypothesis, `InternalSquare β`
at every smaller infinite ordinal (`agents/tasks/LJ-1-556/Probe556.agda:361`),
together with the proof that the collapse's range stays inside `κ`, which is
where the cardinal arithmetic enters and which `col-step` does not touch.

## THE ORDER SLOT IS FILLABLE, MEASURED

Section 4 (`Probe567.agda:275-372`) fills the slot and reads it both ways:
`FstFo` (`:310`), `FstRel` (`:319`), `FstFo-adequate` (`:322`), `FstOrder`
(`:364`). `col-step-at-Fst` (`Probe567.agda:368`) is the obligation at that
concrete order, so the parameter is not vacuous.

**IT IS NOT THE GOEDEL ORDER AND I DO NOT CLAIM IT IS.** The witness is
membership on FIRST components: `r ≺ c` when `r = pr a b`, `c = pr d e` and
`a ∈ d`. It is not total on `Square.sqL κ` and it is not well-founded there, so
no collapse runs on it. What it measures is the SHAPE: four bound components,
two `prAtL` reads, one condition across them, and a two-way reading, **with no
set anywhere**. The max-then-lexicographic order adds a `max` and a case split
over the same four components. That is more conjuncts at the same shape, and
`AGENTS.md:45` still says the next agent must re-measure it at its own site.

## W2

**The rule is answered and it was not weakened.** The mathematics is written
ONCE at a generic carrier. `ColBody`, `StepFo`, `ColOf`, `StepFo-out` and
`StepFo-in` (`Probe567.agda:138`, `:146`, `:150`, `:207`, `:213`) all take the
order as the parameter `O : Order` and are stated at an arbitrary arity `n` and
an arbitrary environment `γ`. `FstOrder` (`Probe567.agda:364`) is one
instantiation and `col-step-at-Fst` (`:368`) is the instantiated obligation.
Nothing is written twice, and no deadline forced a fixed form.

## D-10, THE RE-READ OF `Probe556.agda`

I read its four sections before I wrote any Agda, as the brief orders.

- **Section 1 (`Probe556.agda:71-202`) IS GREEN AND I USE IT.** `sqL`
  (`:148`), `sqL-in` (`:156`) and `sqL-out` (`:186`), the last untruncated.
  This is the domain of my instantiation.
- **Section 2 (`Probe556.agda:204-301`) IS GREEN AND I DO NOT USE IT.** `ltFo`
  (`:219`) and `ltL` (`:269`). It measures a unary condition, and my slot is
  binary. See `## WHAT I COPIED`.
- **Section 3 (`Probe556.agda:309-326`) IS A TYPE AND IS NOT INHABITED.**
  `InternalSquare` (`:321`) and `BriefTarget` (`:325`).
- **Section 4 (`Probe556.agda:329-362`) IS WHAT `SquareStep` ASKS FOR.**
  `SquareStep` (`:357`) adds one hypothesis to `BriefTarget`: the square law at
  every smaller infinite ordinal (`:361`). It is not inhabited there and it is
  not inhabited here. My task does not touch it.

**I DID NOT RE-DISPATCH `[LJ-1.556]`'S TYPE and I did not build the square
law.** No term of this task is named `square-inside-L`, and `BriefTarget` and
`SquareStep` appear nowhere in `Probe567.agda`.

## PRICES, EVERY ONE MEASURED ON THIS PANE

| run | what | seconds | exit |
|---|---|---|---|
| `runs/w3-1.out` | W3 alone, everything cold | 198.06 | 0 |
| `runs/w3-2.out` | W3 alone, own interface deleted, import warm | 2.04 | 0 |
| `runs/w3-3.out` | W3 after a comment-only fix | 2.03 | 0 |
| `runs/s1-1.out` | section 1 only | red | 42 |
| `runs/s2-1.out` | sections 1 and 2 | 2.01 | 0 |
| `runs/s3-1.out` | sections 1 to 3, the obligation added | 2.05 | 0 |
| `runs/s4-1.out` | the whole probe, 4 sections | 2.17 | 0 |
| `runs/final-1.out` | whole probe, own interface deleted | 2.25 | 0 |
| `runs/final-2.out` | whole probe after a comment-only fix | 1.67 | 0 |
| `runs/witness-1.out` | the program's obligation witness | 1.95 | 0 |
| `runs/confirm.out` | both files back to back, final state | 1.78 and 1.85 | 0 and 0 |
| `runs/witness-2.out` | the obligation witness on the final file | 1.81 | 0 |

`agents/tasks/LJ-1-567/Probe567.agda` is 372 lines and
`agents/tasks/LJ-1-567/runs/W3.agda` is 64 lines. **The brief estimated about
160 lines with about 40 for the obligation. The obligation and its two readings
are 103 lines with their comments (`Probe567.agda:138-217` and `:250-272`), and
the whole file is 372.** The overrun is section 4, which the brief did not ask for and which
`AGENTS.md:45` made necessary once I saw that `[LJ-1.556]`'s order device is
unary. **Nothing here was funded against the 775-line figure at
`archive/dev/LJ-dispatch-index.md:100`**, and the standing size figure comes
only from `scripts/measure/ledger.py --brief`: `standing 33,523 lines over 100
masters, measured from HEAD`.

## GATES

I ran the individual checks that this task's files can move. I did not run
`make check`, because I committed nothing and because `make check` runs a full
`typecheck` of `src/`, which this task does not touch.

| gate | exit |
|---|---|
| `scripts/gate/check-probes.py --check` | 0, "clean (6711 tracked files, no probe outside agents/tasks/ and no generated file)" |
| `scripts/gate/lint-agda.py --check` | 0 |
| `scripts/gate/lint-prose.py --check` | 0 |
| `scripts/site/weave-i18n.py --check` | 0 |
| `scripts/gate/check-glossary.py --check` | 0 |
| `scripts/measure/ledger.py --check` | 0 |

## ONE DEFECT IN THE BRIEF, REPORTED AND NOT A STOP

**The brief's `## LAWS` block declares kind `recon`, and describes it as
"read-only ... It writes a report and nothing else."** The brief's
`## THE OBLIGATION` and `## SCOPE (write)` require a probe, an obligation
inside it, and a `runs/` directory. The two cannot both be right. I built the
probe, because the obligation and the write scope are explicit and AD12 gives
this brief one obligation. **The mismatch is a fact about the brief and not
about the mathematics**, so it is reported here rather than made into a stop.
It also selected the law bundle: `C-42`'s sweep is a recon action and no
refutation landed in this task, so there is nothing to sweep for.

## ARCHIVE USED

- `archive/dev/LJ-dispatch-index.md`: **READ.** `:100` says
  "| LJ-1.51 | Discharge the five hypotheses | 2 of 5, plus the sq master |".
  This is the row the brief's premise 9 names and the source of the 775-line
  figure. **I read it in order to refuse it as funding**, which the brief and
  `AGENTS.md:17-18` both require.
- `archive/dev/JOURNAL.md`: **READ.** `:939` says
  "`src/L/Ordinal/SquareLaw.lagda.md:685-687` and". The paragraph around it
  records that both consumers of the square law demand an injective
  `⟪δ⟫ × ⟪δ⟫ → ⟪δ⟫` and nothing more. That is what makes `col` the right
  target: a collapse produces the injection, and no object-language arithmetic
  is owed.
- `archive/dev/DD-archived.md`: **READ.** `:1` says
  "# THE `DD` RULING SERIES, archived in full 2026-08-18". I opened it to check
  that clause W2's parent ruling DD4 is a moved record and not a live rule I
  should quote from. It is: `:11` says "**The rulings are not repealed. They
  moved.**" So my `## W2` section answers the clause in
  `dev/pod/instructions/coder.md` and quotes no `DD` number.
- `archive/dev/JOURNAL-archived.md`: **NOT USED, declined.** Not read beyond a
  relevance grep. Its square-law rows price the retired rud route, and this
  task builds on the two-tower route's `RecShape`. A price from that route is
  not comparable to anything here.
- `dev/ARCHIVE.md`: **NOT USED, declined.** Not read. Clause W4 applies when a
  MODULE retires. This task retires nothing, moves nothing to `archive/`, and
  deletes nothing, so there is no row to write.

## LITERATURE USED

- `dev/literature/devlin-II5.md`: **READ.** `:262` says
  "(`dev2.txt:1328-1329`). The order must be definable by a formula of low".
  This is the source's own statement that the order the argument consumes must
  be DEFINABLE BY A FORMULA. It is independent confirmation of the shape
  `[LJ-1.556]` measured and this task built: the order enters as a formula, and
  `Order` (`Probe567.agda:94`) carries no set.
- `dev/literature/truncation-and-selection.md`: **READ.** `:83` says
  "**So a proof that only needs cardinal arithmetic never needs an injection as".
  This is why `ColOf` (`Probe567.agda:150`) is used under a truncation in
  `StepFo-out` and untruncated in `StepFo-in`: the outward reading needs only
  the EXISTENCE of a predecessor and its value, so truncating costs nothing,
  while the inward reading is supplied a chosen pair and must not truncate it.
- `dev/literature/terms-2026-08.md`: **NOT USED, declined.** Not read. It is
  the terminology dossier for the owner's naming ruling. This task names
  nothing new for the user-facing vocabulary and adds no `dev/glossary.toml`
  entry, which the Boundary forbids me to do in any case.
- `dev/literature/digest.md`: **NOT USED, declined.** Not read. It pins the
  orthodox form of the RUD route. This task is on the collapse route inside the
  two-tower architecture.
- `dev/literature/geology.md`: **NOT USED, declined.** Not read. It is the
  set-theoretic geology dossier. Nothing in this task concerns grounds or
  mantles.

## WHAT THE NEXT BRIEF NEEDS FROM THIS ONE

1. **THE STEP IS BANKED AND IT IS GENERIC.** `StepFo` (`Probe567.agda:146`)
   and its two readings hold at any arity, any environment and any order that
   fills `Order`. A chapter copies them and pays only the order.
2. **THE NEXT PAYABLE PIECE IS THE WELL-ORDER, AS A FORMULA.** Section 4 shows
   the binary shape works and costs four binders. The max-then-lexicographic
   order is more conjuncts at that shape. **Do not fund it against section 4's
   line count**: `FstFo-adequate` is 41 lines (`Probe567.agda:322-362`) for
   ONE condition, and `max` adds a case split whose price nobody has measured.
3. **`GraphAt` FUSES THE DOMAIN WITH THE ARGUMENT AND `col` DOES NOT.** See
   `## THE THREE Fin n ARGUMENTS`. Whoever wants the graph of `col` from
   `RecShape` will meet this first, before any mathematics.
4. **THE RECORD COSTS A UNIVERSE LEVEL.** `Order` sits at
   `Type (ℓ-suc (ℓ-suc ℓ))` and it cannot sit lower while its reading is an
   equation of `Ω` (`runs/s1-1.out:4`). Decide this before a master is written,
   not after.

## WHAT WAS NOT DONE

No postulate, no hole, no module parameter that asserts anything about the
collapse. `src/` is untouched. I did not build the square law, and no term of
this task is named `square-inside-L`. I did not re-dispatch `[LJ-1.556]`'s
type. I did not build the Goedel max-then-lexicographic order and I do not
claim section 4's witness is it. I did not build an order as a set at any
point. I did not prove that any `f` satisfies `Approx`, and I do not claim the
collapse exists. I did not touch `[LJ-1.557]`'s pointwise internal code. I did
not set `GHCRTS`. I did not commit and did not push.
