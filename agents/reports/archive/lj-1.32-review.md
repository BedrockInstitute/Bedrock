# LJ-1.32-R review: DD25 attack on the LJ-1.32 negative

Status: COMPLETE. Written incrementally per C-22. Untracked probes, no commit,
no push. ASD-STE100.

All runs used `GHCRTS="-A64m -I0 -M8g"`, one Agda process at a time, cold, on
a quiet machine. I never raised the cap. I never deleted an interface beside a
source file; interfaces live in `_build/2.8.0/agda/src/`.

## 1. THE VERDICT

**OVERTURN. The measurement stands. The conclusion does not.**

I say this as plainly as I would say an upheld verdict. The return's ladder is
right. The wall does not scale with the constant count. I reproduced the
count-0 wall myself in two formulations. Section 3 gives the figures.

The conclusion built on the ladder is wrong in two separate ways. Each one
alone re-opens the phase.

**FIRST. The gate that stopped the phase is stale. It is GREEN today.**

`src/ProbeLJ127.agda` is the `[LJ-1.27]` gate probe. Nobody has changed that
file: its 283 lines still reproduce, and its `Clause` module is byte-identical
to `src/ProbeDD25D.agda`'s. `[LJ-1.27]` measured it at 32.07 seconds cold and
called the rate 0.1133 seconds per line against a 0.100 NO-GO line.
`[LJ-1.31]` then made `consAtL` constant-free. **Nobody re-ran the gate
probe.** I ran it.

| run | seconds, cold | lines | seconds per line |
|---|---:|---:|---:|
| `[LJ-1.27]`, before the cure | 32.07 | 283 | **0.1133, NO-GO** |
| mine, run 1, after the cure | 18.95 | 283 | **0.0670, GO** |
| mine, run 2, after the cure | 19.17 | 283 | **0.0677, GO** |

Net of the 1.17 second warm interface read the rate is 0.0627 to 0.0636. The
gate passes on both bases, with a third of the budget spare. **`[LJ-1.31]` cut
the gate probe by 41 percent and nobody measured it.**

**SECOND. The whole crossing block, on the erase route, checks in 2.6
seconds.**

`[LJ-1.27-R]` wrote `src/ProbeDD25E.agda`. It is the complete block on the
erase route. At `[LJ-1.27-R]` it failed at ONE line: the `refl` that asserts
the constant count is zero (`_build/lj-1.27-review.md:234-235`). `[LJ-1.31]`
removed the constants that made that line fail. **Nobody ran the probe
again.** I ran it.

```
GHCRTS="-A64m -I0 -M8g" agda src/ProbeDD25E.agda
  run 1: 2.62s user, 4.15s wall, EXIT=0
  run 2: 2.84s user, 3.99s wall, EXIT=0
  run 3: 2.61s user, 2.77s wall, EXIT=0
```

251 lines at 2.69 seconds is **0.0107 seconds per line gross and 0.0059 net**.
That is a factor of 10 below the NO-GO line and a factor of 6 below the gate
probe's own placement route.

**It is the same obligation, and I checked declaration by declaration.** Both
probes carry the same eleven obligations, in the same order, with the same
types: the whole `Clause` module with all ten Delta-0 witnesses, `existCertAt`,
`Σ₁-cert`, `existBnd-out`, `existBnd-in`, `σL`, `σL-eq`, `σL-out`, `σL-in`,
`σL-transfer`, `σL-up`, `cert-transfer`, `ride-only` and `ride-defines`.
Nothing is dropped. The only difference is the apparatus: `src/ProbeLJ127.agda`
carries `nφ`, `cs`, `δ` and `map-++` for the constant vector
(`src/ProbeLJ127.agda:266-336`); `src/ProbeDD25E.agda` carries `Cnt`, `σL₀`
and `σL≡` for the erase (`src/ProbeDD25E.agda:270-281`). The erase route is
four declarations shorter, not four obligations shorter.

The interface confirms the work: `ProbeDD25E.agdai` is 300,575 bytes, against
319,678 for the gate probe and 338,848 for `ProbeDD25C`.

**THE RETURN ALSO CONTRADICTS ITSELF, and the contradiction is where the
negative comes from.** Its section 4 proves the delivered clause forms are not
Delta-0, so the certificate is for the crossing's own bounded MATRIX. Its
section 7 admits "the crossing's exact matrix is not in the delivered
masters". Then its section 1 rules route A out because **the DELIVERED clause
forms** keep counts of 1 and 5. Those counts do not bind a certificate that is
not about those formulas. The crossing author writes the matrix, and can write
the tag as a slot. `src/ProbeDD25E.agda` does exactly that.

## 2. IS THE REMAINING OBLIGATION REALLY ONE CONSTANT?

**YES, and it is already paid. `src/ProbeDD25E.agda` pays it and is green.**

The chain, each link re-verified.

**The matrix carries one constant, and it is the arity tag.** The matrix names
`con (numeralL 8)` once, in `shapeBnd` (`src/ProbeDD25D.agda:150`). `shapeBnd`
is the bounded restatement of `arityTagAtL`
(`src/L/Coding/Model.lagda.md:763-765`), whose constant enters through
`tagAtL`. I re-verified the delivered counts by re-running
`src/ProbeLJ132Counts.agda`: green, so `arityTagAtL` is 1 and `exInClauseAt`
is 5.

**Removing it means writing the numeral as a slot, not as a constant.**
`src/ProbeDD25E.agda:63` gives the clause a fourth parameter `N`, and `:125`
writes `var (suc (suc (suc (suc (suc (suc (suc N)))))))` where
`src/ProbeDD25D.agda:150` writes `con (numeralL 8)`. That is the whole edit.
It is one line.

**At count 0 the placement is not needed at all.** `erase` takes a formula
with a zero count straight to the parameter-free axis, at the SAME arity
(`src/FOL/Count.lagda.md:598-611`), and `erase-inv` says the embedding gives
the formula back (`:617-637`). `src/ProbeDD25E.agda:271-281` rides both.

**The count is zero at a VARIABLE arity, not only at a sample.**
`src/ProbeDD25E.agda:273` is `Cnt.erase (Clause.existBndAt {n} C T B N) refl`
inside a module with `{n : ℕ}` free. That `refl` machine-checks
`countFo φ ≡ 0` for every `n`. It is stronger than the return's own count
assertions, which are all at `n = 1`.

**What the slot costs, honestly.** The placement route puts the numeral into
the environment mechanically: `absFo` raises the arity and `δ = γ ++ cs`
carries `numeralL 8` (`src/ProbeLJ127.agda:266-279`). The slot route asks the
author to put the same value in the same place by hand. **Same value, same
position, and only one of the two costs 8 GB.** The crossing must then show
the slot holds `numeralL 8`, which is one environment lookup.

**One gap, and it is not new.** Neither `src/ProbeLJ127.agda` nor
`src/ProbeDD25E.agda` proves that the bounded matrix says what the delivered
`existClauseAt` says. That link was missing before this task and it is missing
now. The erase route neither adds it nor makes it harder.

**The `# 0 = ∅` trick is indeed unavailable, and it is not needed.** The tag
is `# 8`. The slot replaces it without any arithmetic identity.

## 3. IS THE COUNT-0 WALL REAL?

**YES. I reproduce it, and I show it is not an artefact of how the lemma is
written.**

| probe | formula | arity | placements | result | seconds |
|---|---|---|---|---|---:|
| `src/ProbeLJ132C0.agda` | matrix, count 0 | variable `n` | implicit | **WALL** | 61.37 user, 63.53 wall |
| `src/ProbeDD25B3.agda` | matrix, count 0 | variable `n` | **explicit** | **WALL** | 61.71 user, 62.71 wall |

`src/ProbeDD25B3.agda` is mine. It is `src/ProbeLJ132C0.agda` with the
explicit `placeΔ₀` of `src/ProbeDD25H.agda`, so no metavariable is left for
the elaborator to chase. It walls at the same cost. **The count-0 wall is a
real placement cost, not a meta search.** The return is right, and the point
needed checking: at count 0 the generic `placeΔ₀` leaves its `θ` arguments
unconstrained, so the naive reading of `src/ProbeLJ132C0.agda` was open to
that objection.

**The count assertion is sound.** `src/ProbeLJ132Ctrl0.agda` holds the same
`Clause` module and the same `refl` without the placement. I re-ran it: GREEN,
2.32 seconds. `src/ProbeDD25E.agda` proves the same count at a variable arity,
which is the stronger statement.

**One flaw in the ladder, which does not change the verdict.** The four ladder
points do NOT differ only in the constant count. `src/ProbeLJ132C2.agda` adds
a whole conjunct `(var (suc zero) ≐ con (numeralL 11))` to `shapeBnd`, so its
TREE is larger as well as its count. `src/ProbeLJ132C5.agda` adds more. Count
and size move together up the ladder. The confound cannot rescue the scaling
hypothesis, because the smallest point, count 0, already walls. I report the
flaw for the record, not as a refutation.

## 4. THE SIZE LAW

The return states a size hypothesis and does not isolate it. Its control pair
is confounded: `src/ProbeLJ132Small0.agda` is a SMALL formula at a CONCRETE
arity 1, and `src/ProbeLJ132C0.agda` is a BIG formula at a VARIABLE arity `n`.
The two differ on two axes at once. I measured each axis on its own.

**First, the x axis.** `src/ProbeDD25B5.agda` is red by design and its error
message is the measurement. It reports `small + 1000 * big = 651244`, so the
delivered `consAtL` is **244 nodes** and the walling matrix is **651 nodes**.
The "small" control is not small. The two formulas are only 2.7x apart.

**The arity axis, size held fixed.**

| probe | formula | arity | result | seconds |
|---|---|---|---|---:|
| `src/ProbeLJ132Small0.agda` | `consAtL`, 244 nodes | concrete 1 | GREEN | 3.09 |
| `src/ProbeDD25B1.agda` | `consAtL`, 244 nodes | **variable `n`** | GREEN | 4.18 |
| `src/ProbeDD25B4.agda` | matrix, 651 nodes | concrete 1 | **GREEN** | **30.82** |
| `src/ProbeLJ132C0.agda` | matrix, 651 nodes | variable `n` | **WALL** | 61.37 |

**The arity is a real second axis.** The same 651-node matrix that exhausts
8 GB at a variable arity finishes in 30.82 seconds at a concrete arity. At
`n + 0` with a variable `n`, and with `padRight`/`padLeft` applied to variable
indices, every leaf carries an index term that cannot reduce.

**The tree axis, arity held at the setting that walls.** Right-nested
conjunctions of `consAtL`, count 0, placed, at a variable arity.

| probe | copies | nodes | result | seconds |
|---|---:|---:|---|---:|
| `src/ProbeDD25B1.agda` | 1 | 244 | GREEN | 4.18 |
| `src/ProbeDD25B10.agda` | 2 | 489 | GREEN | 9.95 |
| `src/ProbeDD25B11.agda` | 4 | 979 | GREEN | 46.06 |
| `src/ProbeDD25B12.agda` | 8 | 1959 | **WALL** | 58.11 |
| `src/ProbeDD25B13.agda` | 16 | 3919 | **WALL** | 65.27 |
| `src/ProbeDD25B14.agda` | 32 | 7839 | **WALL** | 94.74 |

**The turnover is between 979 and 1959 nodes**, and the cost is superlinear
below it: doubling 244 to 489 costs 2.4x, and doubling 489 to 979 costs 4.6x.

**Binder depth is FREE, and that kills the obvious explanation.** One atom
under `d` nested bounded quantifiers, count 0, placed, at a variable arity:

| probe | depth | nodes | result | seconds |
|---|---:|---:|---|---:|
| `src/ProbeDD25Bd04.agda` | 4 | 5 | GREEN | 0.67 |
| `src/ProbeDD25Bd08.agda` | 8 | 9 | GREEN | 0.72 |
| `src/ProbeDD25Bd12.agda` | 12 | 13 | GREEN | 0.75 |
| `src/ProbeDD25Bd16.agda` | 16 | 17 | GREEN | 0.76 |
| `src/ProbeDD25Bd20.agda` | 20 | 21 | GREEN | 0.79 |

Sixteen extra binders cost 0.12 seconds. These five probes import much less
than the others, so their 0.67 second floor is not comparable to the 4.18
second floor above; the DELTA across the ladder is the measurement, and it is
flat.

**What I can and cannot conclude.** The 651-node matrix walls while a
979-node flat conjunction is green. So the node count alone does NOT predict
the turnover, and neither does the binder depth. The matrix costs more per
node than a flat conjunction, and I did not isolate why.

**The law, with its measurement, for the orchestrator to number or reject.**
This corrects the return's proposed clause for P-u rather than replacing it.

> **Certify a formula before you place it, or do not place it at all.** A Levy
> witness travels along a constant relabelling for free (`mapΔ₀`) and along
> `erase` for free (`erase-inv`). It does not travel along a placement. The
> placement cost is superlinear in the formula tree; it is INDEPENDENT of the
> constant count and of the binder depth; and it is far worse at a variable
> arity than at a concrete one. Measured on this tree: flat conjunctions of
> `consAtL` at a variable arity place green at 244, 489 and 979 nodes in 4.18,
> 9.95 and 46.06 seconds, and wall at 1959 nodes in 58.11 seconds; the
> 651-node condensation matrix walls at counts 0, 1, 2 and 5 in 61 to 65
> seconds, and the same matrix at a concrete arity is green in 30.82 seconds;
> binder depth 4 to 20 costs 0.12 seconds. **The cure is `erase` at count 0:
> the same block goes from a wall to 2.62 seconds.**

## 5. DID THE BRIEF CAUSE IT?

**YES. This one is on the brief, and the evidence is exact.**

The brief drew the archive scope at one section, and the decisive artefact sat
in the next one.

- Brief `_build/briefs/LJ-1.32.md:101`: "**`_build/lj-1.27-review.md` section
  4**, the wall and its two formulations. **`src/ProbeDD25D.agda` is the
  walling probe. Start from it.**"
- Brief `:131-133`, SCOPE (read): "`src/ProbeDD25D.agda` and
  `src/ProbeLJ131.agda` FIRST, then `_build/lj-1.27-review.md` **section 4**".
- Return `_build/lj-1.32-report.md:116-117`, ARCHIVE USED:
  "`_build/lj-1.27-review.md:114-166`. Section 4 locates the wall".

Lines 114 to 166 ARE section 4, and nothing else. The return read exactly what
the brief told it to read, and it read nothing else of that file.

**Section 6 of the same review is lines 204 to 256.** Its title is "WHAT THE
GATE SHOULD SAY NOW, AND WHETHER ROUTE A FUNDS". It names the erase route, it
cites `erase` and `erase-inv` at `file:line`, and at `:234` it says: "I wrote
this variant as `src/ProbeDD25E.agda`. It fails at one line only, the `refl`
that asserts the count is zero."

**`[LJ-1.31]` is the task that fixed that one line.** The finished probe sat
in the tree, one command away, for the whole of `[LJ-1.32]`.

Two smaller brief effects, both real.

**The ladder framing chose the wrong question.** "Suggested ladder: 0, 1, 2,
5, then upward" (`:47`) makes "does the wall scale with the count" the only
question. The question that decides route A is "does the crossing still need a
placement at all". The brief never asks it. The return answered the asked
question correctly.

**"Use the DELIVERED clause forms" (`:50`) pointed at formulas that cannot
carry the certificate.** The return discovered this itself and reported it
well. But the instruction then leaked into the verdict: the return rules route
A out on the delivered forms' counts, and the certificate does not depend on
them.

**What the brief did right, and it matters.** It demanded the counts be
re-verified (D-10), it demanded controls in the same session, and it warned
about the interface location. The return obeyed all three, and every
measurement in it that I checked reproduced.

## 6. A THIRD ROUTE?

**There are two live routes, not one, and neither needs new machinery.**

**Route 1: change nothing.** The gate probe is green at 0.067 seconds per line
(section 1). The composed placement transfer that `[LJ-1.27]` already wrote
funds on the cured tree. This route costs zero further work.

**Route 2: the erase route.** Slot the arity tag in the crossing's matrix and
take `erase`. 0.0107 seconds per line, a factor of 6 better, and it deletes
`absFo`, the constant vector, the appended environment and two generic
theorems from the block. `src/ProbeDD25E.agda` is the finished template, and
it is 32 lines shorter than the placement version.

I recommend route 2, and I record that route 1 alone already re-opens the
phase. Route 2's advantage is not only seconds: at count 0 the environment
does not grow, so `σL-eq` and `σL-transfer` stay at `γ` instead of `γ ++ cs`,
and every downstream consumer keeps the arity it had.

**Splitting the matrix does NOT work, and I checked before proposing it.**
`placeFo` raises the arity of the WHOLE formula, `n` to `n + k`
(`src/FOL/Manipulation/Parameters.lagda.md:226-246`). A subformula cannot be
placed on its own without moving every other index. The slot route reaches the
same end for free, so splitting has no purpose.

**A cure the return named but did not test, and it is unnecessary.** The
return says the fix is to make the DELIVERED readers erase-eligible, and calls
that unpriced. The delivered readers are not Delta-0 and never enter the
certificate, so their counts do not need to move.

**DD4.** The erase route is the better shared answer. It removes the
Def-tower-specific placement apparatus from the crossing and rides three
delivered generic lemmas that are constant-domain polymorphic: `erase` and
`erase-inv` (`src/FOL/Count.lagda.md:598-637`) and `mapΔ₀`
(`src/FOL/Manipulation/Relabelling.lagda.md:209-220`). `[LJ-1.27-R]` found the
J tower's certificate is structural and avoids the syntax (D-26), so the J
tower inherits the law rather than the code. The law in section 4 is the
transferable part.

## 7. WHAT I AM NOT SURE OF

**`src/ProbeDD25E.agda` is a probe, not the crossing.** It restates the
hardest clause as a bounded matrix. The crossing is about 3,300 lines. The
figures above are RATES against DD24's bar, not a total. A rate measured on
the hardest clause is the right thing to gate on, and it is not a delivery.

**The matrix-to-clause link is unproven, in both routes.** Nothing shows the
bounded matrix says what the delivered `existClauseAt` says. That gap is older
than this task and it is equal on both routes, but it is real and somebody
must price it.

**The slot's environment obligation is unmeasured.** Route 2 needs the
crossing's environment to hold `numeralL 8` at the slot. I did not build that
lookup. It is one line in the placement route, so I expect one line here, and
P-l forbids me from calling that a price.

**A wall is a wall, not a price.** I did not raise the cap, so I do not know
whether any walling probe finishes at 16 GB.

**I did not explain why the 651-node matrix walls while a 979-node flat
conjunction is green.** I ruled out the constant count, the binder depth and
the metavariables. I did not find the positive cause. The law in section 4
states only what I measured.

**The depth ladder's floor is not comparable to the width ladder's.** Those
five probes import much less. I read only the delta across them.

**I did not test whether the crossing needs `σL` at all.** That is
`[LJ-1.27-R]`'s open question and it is still open. If each carrier can keep
its own formula, the whole apparatus goes away.

## 8. ARCHIVE USED

- `_build/lj-1.27-review.md` in full, and **section 6 at `:204-256`** is the
  section that decided this review. `:234-235` names `src/ProbeDD25E.agda` and
  the one line that failed.
- `src/ProbeDD25E.agda` in full, and RUN. Green, 2.62 s.
- `src/ProbeDD25D.agda` and `src/ProbeDD25H.agda` in full: the walling probe
  and the explicit-placement formulation I ported to count 0.
- `src/ProbeLJ127.agda` in full, and RUN twice. The gate probe, now green.
- `src/ProbeLJ132C0.agda`, `Ctrl0`, `Small0`, `NotD0`, `Counts`, `C2`, `C5`:
  read, and C0, Ctrl0, Small0 and Counts re-run.
- `src/FOL/Count.lagda.md:594-637`: `erase`, `eraseTm`, `erase-inv`.
- `src/FOL/Manipulation/Parameters.lagda.md:74-117`, `:154-156`, `:226-261`,
  `:421-423`: `countFo`, `constantsFo`, `padLeft`, `placeFo`, `absFo`,
  `⊨-abs`.
- `src/FOL/Manipulation/Relabelling.lagda.md:117-118`, `:209-220`: `embed`
  and `mapΔ₀`.
- `src/FOL/LevyHierarchy.lagda.md:47-58`: no `∀̇` or `∃̇` constructor.
- `src/L/Coding/Model.lagda.md:730-732`, `:763-765`, `:890-902`, `:985-997`:
  `arityTagPairAtL`, `arityTagAtL`, `binClauseAt`, `unClauseAt`. I confirm the
  return's finding that the delivered frames use the unbounded quantifiers.
- `dev/LESSONS.md`: P-u at `:2908`, and P-l, P-m, P-t, D-1, D-10, C-12, C-22
  through `scripts/rules.py --for probe`.
- `dev/literature/`: nothing bears. This is an elaborator cost measurement on
  this tree's own formulas.

## 9. THE PROBES

All are untracked, all match `src/Probe*.agda`, and none is committed.
`.gitignore:22` covers them.

| file | what it measures | result |
|---|---|---|
| `src/ProbeDD25B1.agda` | small `consAtL` placed at a VARIABLE arity | GREEN 4.18 s |
| `src/ProbeDD25B2.agda` | matrix placed at a CONCRETE arity, implicit placements | 30.24 s, one unsolved meta |
| `src/ProbeDD25B3.agda` | matrix placed at a VARIABLE arity, EXPLICIT placements | **WALL** 61.71 s |
| `src/ProbeDD25B4.agda` | matrix placed at a CONCRETE arity, EXPLICIT placements | GREEN 30.82 s |
| `src/ProbeDD25B5.agda` | node counts of `consAtL` and of the matrix | RED by design: 244 and 651 |
| `src/ProbeDD25B10/11/12/13/14.agda` | width ladder, 2/4/8/16/32 copies | GREEN, GREEN, WALL, WALL, WALL |
| `src/ProbeDD25Bd04/08/12/16/20.agda` | depth ladder, 4/8/12/16/20 binders | all GREEN, 0.67 to 0.79 s |
