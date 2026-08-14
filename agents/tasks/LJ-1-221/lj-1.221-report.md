# LJ-1.221 report: DD25 review of `[LJ-1.216]`, `[LJ-1.219]`, and the one-link-per-task method

tier: opus (deepseek-subagent-mode), ADVERSARIAL row. Written incrementally
(C-22). No master edited. No brief edited. No other report edited. No commit,
no push. **NO AGDA RAN.** Every negative is MEASURED or INFERRED, in those
words.

## 0. THE THREE VERDICTS

| target | verdict |
|---|---|
| `[LJ-1.216]` | **UPHELD** |
| `[LJ-1.219]` | **UPHELD BUT MISATTRIBUTED** |
| the method, one link per task | **WASTEFUL** |

Both stops are correct measurements. I reproduced every line figure in both
reports and every one matched exactly. `[LJ-1.219]`'s verdict is right and its
CAUSE is wrong: **the second brick is not a brick.** Section 4 gives the
evidence.

## 1. WHAT I RE-DERIVED, AND IT ALL MATCHED

I re-ran `agents/tasks/LJ-1-213/linediff.py` on the probe files myself.

| claim | source | my measurement | result |
|---|---|---|---|
| join is 21 added, 6 deleted, 386 unchanged | `lj-1.219-report.md:21-22` | `added=21 deleted=6 unchanged=386` | **EXACT** |
| the 21 splits 13 + 2 + 2 + 1 + 2 + 1 | `lj-1.219-report.md:129-131` | the diff gives exactly those six groups | **EXACT** |
| body port is 19 added, 21 deleted, 370 verbatim | `lj-1.213-report.md:55-57` | `added=19 deleted=21 unchanged=370` | **EXACT** |
| ambient file is 392 non-blank, net +3 | `lj-1.216-report.md:55-57` | 392 non-blank, net +3 | **EXACT on the total** |
| generic candidate is 389 non-blank | `lj-1.213-report.md:60` | 389 non-blank | **EXACT** |

One sub-figure does not match and it moves nothing. `[LJ-1.216]` says the
delta is "one import line added, two header parameter lines removed, four
`M`/`M-trans` lines added" (`lj-1.216-report.md:56-57`), which sums to 5 added
and 2 deleted. The measured delta is 7 added and 4 deleted, because the
module-name line is a rename and the header is 3 lines, not 2
(`agents/tasks/LJ-1-213/GenPowerset.agda:14-16`). Net +3 and the total 392 are
right. **MEASURED, and immaterial.**

**The reporting discipline in both files is good.** Neither rests a verdict on
seconds. Both quote the compiler. Both refuse to price what they did not
reach. I say this because the defects below are narrow and I do not want them
read as a pattern of sloppiness.

## 2. `[LJ-1.216]`: UPHELD. The four questions.

### 2.1 Is the stop correct on its own numbers? YES.

`GenPowersetAtAmbient.agda:68` is `envOneAt e y = extAt e (tagAtL zero 0 (suc y))`,
exactly as quoted (`lj-1.216-report.md:88`). `envOneAt`'s return type is
`Formula S n` at `:67`; `S` comes from `open hPropStructure (𝒮ᵥ {ℓ} ↾ M)` at
`:60` with `M` the ambient class at `:53-54`; `extAt` and `tagAtL` come from
`open import L.Coding.Model` at `:24-26`. The two carriers cannot meet.

`:62` is the eta-expanded `module AbsL = FOL.Absoluteness.Single (𝒮ᵥ {ℓ}) M (λ {x} {y} → M-trans {x} {y})`.
The pre-cure form survives in `agents/tasks/LJ-1-213/GenPowerset.agda:60` as
`... M M-trans`, so the report's account of both failures is checkable against
both files. **MEASURED.**

### 2.2 Is the measurement sound? Does the exit code mean what the report says?

**YES, and I ran the brief's inverse test.** An error at `:68` does not by
itself prove `L.Coding.Model` is the cause. Here it does, for a reason the
report does not state.

The quoted message names `Formula (FOL.ZFStructure.ZFStructure.S L.Constructible.𝒮ʟ) _n_21`
as the inferred type (`lj-1.216-report.md:80`). `𝒮ʟ` can reach `:68` only
through `extAt` or `tagAtL`. The other names on that line are `envOneAt`
(declared at `:67` over the ambient `S`), `e`, `y` and `zero`, and none of them
can introduce `𝒮ʟ`. The attribution is forced by the message. **MEASURED.**

### 2.3 Did the BRIEF cause the outcome? It named the branch, and the finding
still stands.

`LJ-1.216.md:67-68` names the branch. `LJ-1.216.md:84-85` forbids the
alternative: "Do not port a supplier."

**The agent had no alternative, and that is the correct call here.** The
branch is conditional on a fact the agent could not choose: the file either
typechecks at the ambient class or it does not. A branch that fires on a fact
the agent cannot influence is a finding, even when the brief made it easy to
take. **The defect is in what the next brief did with the result, not in this
one.**

### 2.4 Is there a cure `[LJ-1.216]` missed? YES, one, and it cost a dispatch.

`lj-1.216-report.md:99` says "The next module to port is `L.Coding.Model`."

**`L.Coding.Model` was already ported when that sentence was written, and the
port was named in `[LJ-1.216]`'s own brief** at `LJ-1.216.md:41`:
"`agents/tasks/LJ-1-210/GenModel.agda`: the class-generic `Model`."

The correct sentence was "the generic replacement already exists at
`agents/tasks/LJ-1-210/GenModel.agda`, so the join is available now." The
report instead described delivered work as future work. **MEASURED.** It does
not touch the verdict, and I do not overturn for it.

I also record what the report got RIGHT and could have got wrong. Its supplier
list at `lj-1.216-report.md:101-104` names ten modules and excludes
`L.Coding.Environment`, which the body also imports
(`GenPowersetAtAmbient.agda:27`). That exclusion is correct: the only name
taken from it is `env`, used at `:65` with type `V ℓ → V ℓ`, which never
mentions a structure. **The report read the types, not just the import list.
MEASURED.**

## 3. `[LJ-1.219]`: the measurement, which is excellent

### 3.1 Is the stop correct on its own numbers? YES, and the five-name claim
holds exactly.

The brief asked me to check the file. `JoinAtAmbient.agda:142` is
`hasKey : ⟨ fst (keyOf 0 (lookup y γ)) ∈ fst E ⟩`, as quoted
(`lj-1.219-report.md:87`).

**The five Model names, each at its own line. MEASURED by reading the file.**

| name | first use before `:142` |
|---|---|
| `extAt` | `JoinAtAmbient.agda:91` |
| `tagAtL` | `JoinAtAmbient.agda:91` |
| `extAt-in-both` | `JoinAtAmbient.agda:109` |
| `tagAtL-adequate` | `JoinAtAmbient.agda:112` |
| `extAt-out` | `JoinAtAmbient.agda:126` |

**Both INFERRED claims are correct. MEASURED by grep.** `extAt-in` first
appears as a USE at `:143`, one line past the error; `:109` is
`extAt-in-both`, a different name, and `:79` is the `open` list. The `domAt`
trio appears at `:246`, `:247` and `:269`. All past `:142`. The refusal to
price them is correct C-42 discipline.

### 3.2 Is the measurement sound? YES, and the column range settles it.

**This is the strongest single piece of evidence in either report, and the
report does not use it.**

The reported range is `JoinAtAmbient.agda:142.32-42` (`lj-1.219-report.md:11`).
I counted the columns of `:142`. Columns 32 to 41 are exactly `lookup y γ`,
the second argument of `keyOf`. The message reads "when checking that the
expression lookup y γ has type FOL.ZFStructure.ZFStructure.S L.Constructible.𝒮ʟ"
(`lj-1.219-report.md:83-84`).

So Agda states in its own words that the expected type of `keyOf`'s argument
is the carrier of `𝒮ʟ`. **The attribution is not an inference from a line
number. It is the compiler naming the demanded type at the exact column of
that supplier's argument. MEASURED.** The brief's inverse test passes.

## 4. WHY `[LJ-1.219]` IS MISATTRIBUTED: brick two is not a brick

The verdict is right. The cause is wrong. `lj-1.219-report.md:113-116` says:

> `Recover` is itself a consumer of the delivered Model ... So it is the next
> brick in `[LJ-1.213]`'s bottom-up order. **I do not port it. One link per
> task.**

**`L.Coding.Recover` does not need porting for this consumer. Its two leaking
names are one-line definitions whose generic form is already built and already
green.** Every fact below is MEASURED at a named line.

### 4.1 The whole of brick two is two names

`src/L/Coding/Powerset.lagda.md:57` imports from `Recover` exactly and only
`keyOf` and `keyOf-fst`. It is the only import of that module in the master,
and the probe copies it at `JoinAtAmbient.agda:26`. **No other name from
`Recover` appears anywhere in the body. MEASURED by grep.**

### 4.2 The delivered definitions are one line each

`src/L/Coding/Recover.lagda.md:112-116`:

```
keyOf : ℕ → S → S
keyOf n x = prʟ (numeralL n) x

keyOf-fst : (n : ℕ) (x : S) → fst (keyOf n x) ≡ pr (# n) (fst x)
keyOf-fst n x = prʟ-fst (numeralL n) x ∙ cong₂ pr (numeralL-fst n) refl
```

`keyOf` is not a theorem. It is an application of `prʟ` to a numeral. Its four
ingredients are `prʟ`, `prʟ-fst`, `numeralL` and `numeralL-fst`, and `Recover`
imports the first two from `L.Coding.Model` at
`src/L/Coding/Recover.lagda.md:69`.

### 4.3 All four ingredients already exist, generic and green

In `agents/tasks/LJ-1-210/GenModel.agda`, which exits 0 (`LJ-1.219.md:38`):

| ingredient | generic form | line |
|---|---|---|
| `prʟ` | `prʟ a b = pairʟ (pairʟ a a) (pairʟ a b)` | `GenModel.agda:193-194` |
| `prʟ-fst` | proved from `pairʟ-fst` and `pair-singleton` | `GenModel.agda:196-199` |
| `numeralL` | a MODULE PARAMETER | `GenModel.agda:16` |
| `numeralL-fst` | a MODULE PARAMETER | `GenModel.agda:17` |

None of the four sits in a `private` block. All four are at column 0 or are
parameters.

**And `keyOf-fst`'s body already exists, verbatim.** `GenModel.agda:214-215`:

```
tagBridge : (k : ℕ) (x : S) → fst (LCode.mkTag k x) ≡ VCode.mkTag k (fst x)
tagBridge k x = prʟ-fst (numeralL k) x ∙ cong₂ pr (numeralL-fst k) refl
```

Compare `Recover.lagda.md:116`:

```
keyOf-fst n x = prʟ-fst (numeralL n) x ∙ cong₂ pr (numeralL-fst n) refl
```

**The two right-hand sides are character-for-character identical up to the
bound variable name. MEASURED.**

### 4.4 And the probe already applied the module that holds them

`JoinAtAmbient.agda:76-77` applies `GenModel` at the ambient class. The two
ambient numerals it needs are supplied twelve lines earlier, at
`JoinAtAmbient.agda:57-61`, as `numeralF` and `numeralF-fst`, and the pairing
at `:63-68` as `pairF` and `pairF-fst`.

`JoinAtAmbient.agda:79-80` then opens NINE names from `AtFull` and stops:

```
open AtFull using ( extAt; extAt-out; extAt-in; extAt-in-both; tagAtL
                  ; tagAtL-adequate; domAt; domAt-intro; domAt-out )
```

**`prʟ`, `prʟ-fst` and `tagBridge` were inside the applied module, at the
ambient class, sixty-five lines above the failure, and the `using` list did
not name them.** MEASURED.

### 4.5 The classification of this finding

**INFERRED, and every ingredient is MEASURED.** I did not run Agda and P-l
binds: a cure that works at the numeral site is a hypothesis at the `keyOf`
site until it is measured there. I do not give a line price and I do not
predict an exit code.

**The test that would settle it, at one Agda run:** add `prʟ` and `prʟ-fst` to
the `using` list at `JoinAtAmbient.agda:79-80`, copy the two bodies from
`src/L/Coding/Recover.lagda.md:113` and `:116` into the probe, delete the
import at `JoinAtAmbient.agda:26`, and re-run. The types line up on
inspection: `prʟ (numeralL n) x` has type `S` for the ambient `S`
(`GenModel.agda:193`), and `keyOf-fst`'s statement needs exactly the
`numeralL-fst` step that `numeralF-fst` supplies at
`JoinAtAmbient.agda:60-61`.

### 4.6 Did the BRIEF cause it? YES.

`LJ-1.219.md:62-64` writes the branch as: "A SECOND SUPPLIER LEAKS. Name it at
`file:line` and stop. That is the next brick ... **Do not port it: one link
per task.**"

**The brief offered only two readings of a leak: it is a brick, or it is a
refutation of the order.** It offered no branch for "the leaking name is thin
and its generic form is already on disk". The agent obeyed the brief exactly
and could not report what the brief had no slot for.

This is `[LJ-1.211]` category 2, "the brief fixed a method that could not
answer the question", the largest single cause at four of ten
(`lj-1.211-report.md:16`).

## 5. THE THIRD TARGET: the method is WASTEFUL

### 5.1 The load-bearing sentence was never measured

**`[LJ-1.213]` does not contain the claim the later briefs attribute to it.**
MEASURED by reading the file whole.

`lj-1.213-report.md:73-75` says:

> The fixed supplier modules import `𝒮ʟ`. They block the generic body until
> each supplier is ported. This is the chain gate.

**The words ORDER, "bottom-up" and "port first" do not appear anywhere in
`lj-1.213-report.md`.** What appears is a clause of purpose inside a sentence
whose measured content is an exit code at `GenPowerset.agda:63`.

`LJ-1.216.md:49-50` then wrote: "`[LJ-1.213]` calls that the chain gate and it
is an ORDER problem: the suppliers must port first."

`LJ-1.219.md:23-26` then wrote: "**`[LJ-1.213]` MEASURED that the chain gate is
an ORDER, not a wall** ... **It said port bottom-up.**"

**Over two hops the word MEASURED was attached to a repair proposal.**
`[LJ-1.213]` measured that the generic body does not typecheck while its
suppliers are fixed. It never measured that porting each supplier is the only
repair, the first-best repair, or that the repairs are ordered at all. **No
probe in the chain has ever tested an alternative.** Section 4 is the
counterexample the chain never looked for.

### 5.2 The agent inherited the frame, exactly as `[LJ-1.211]` predicts

`lj-1.219-report.md:115` writes "the next brick in `[LJ-1.213]`'s bottom-up
order", citing a phrase that is not in `[LJ-1.213]`. It came from its own
brief.

`lj-1.219-report.md:162` is the weakest row in either report:

> | the order is wrong | **MEASURED FALSE so far.** The Model link confirms
> `[LJ-1.213]`'s bottom-up reading for the first step |

**This row is a category error.** What was measured is that ONE method works
for ONE step. That a sufficient method succeeds is not evidence that it is
necessary, and "the order is wrong" is a claim about necessity. The probe
tests no alternative, so the correct class is INFERRED, not MEASURED FALSE.
**MEASURED: the row's own evidence column describes a confirmation of one
method, not a refutation of others.**

### 5.3 What each dispatch actually bought

| dispatch | new fact no static reading could give | already on disk before it ran |
|---|---|---|
| `[LJ-1.213]` | the body is green at `isL` with 7 substitutions; `DefAt-stage` is 8 lines | nothing |
| `[LJ-1.216]` | the ambient class reaches `:68`; the eta cure transfers to this site | the supplier list; `GenModel.agda` |
| `[LJ-1.219]` | **`GenModel` composes with the body at the ambient class, five names** | the supplier list; that `Recover` was in it; that `keyOf` is one line |

**`[LJ-1.219]`'s composition result is real and it was worth a dispatch.** It
discharges the hypothesis that the two generic bricks fit at all, which is
C-38 as extended: something SUPPLIES it. No census gives that.

**Its second half was not.** "The next blocker is `L.Coding.Recover`" was
derivable with no Agda from files already committed:

- `agents/tasks/LJ-1-216/lj-1.216-report.md:101-104` lists all ten remaining
  fixed suppliers by name.
- `agents/tasks/LJ-1-219/JoinAtAmbient.agda:26-39` lists the exact names taken
  from each.
- `src/L/Coding/Recover.lagda.md:112-116` shows those two names are one-liners.

**Which supplier Agda names next is decided by textual position in the
CONSUMER, not by the mathematics.** `keyOf` won the title because `:142` is
where the body first uses a leaking name. Had `sub₂` been written before
`sub₁`, another supplier would hold it. Each further dispatch buys one entry
of a committed list, in an order that carries no mathematical content.
**INFERRED from the file layout; MEASURED that the list and the names are
already written at the three citations above.**

### 5.4 The count, corrected

The method has spent three dispatches to walk two links, and section 4 shows
the second link did not need walking.

**The remaining width is smaller than this task's brief states. MEASURED.**
The brief speaks of "a seventeen-module chain" and "fifteen more dispatches"
(`LJ-1.221.md:24`, `:31-32`). The probe imports twelve `L.Coding` modules
(`JoinAtAmbient.agda:24-39`). One of those, `L.Coding.Environment`, supplies
only `env`, whose type never mentions a structure. `L.Coding.Model` is done.
**So at most ten suppliers remain, not fifteen.** Separately, 23 modules exist
under `src/L/Coding/` and all 23 fix the structure at import time, so the
seventeen is not that count either.

After three dispatches the project still has no figure for the chain's total
price, and every brief forbids producing one (`LJ-1.216.md:84-85`,
`LJ-1.219.md:77`).

**Verdict: WASTEFUL.** Precisely: sound for exactly one dispatch,
`[LJ-1.219]`, whose composition result had to be built; wasteful from the
second link on, because the remaining output is a re-ordering of a committed
list, and because the second link was not a link.

### 5.5 The one-sentence repair

**The order `[LJ-1.213]` observed is a TYPECHECK order. The briefs converted it
into a DISPATCH order. That conversion is the unmeasured step.**

Nothing forces one dispatch per link. The ten remaining suppliers can be read
in one pass and split into thin and thick, and the thin ones need no dispatch
at all.

## 6. THE ATTACK ON「PORT BOTTOM-UP」

**It is not a fact about Agda's module system. It is a property of how the 23
modules under `src/L/Coding/` were written, and the delivered tree already
contains three counterexamples.**

### 6.1 Module parameters: the delivered tree already does this

`src/FOL/Absoluteness.lagda.md:57-59` declares
`module Single {ℓ} (𝒮 : ZFStructure (hPropAlgebra ℓ)) (M : ZFStructure.S 𝒮 → hProp ℓ) (trans : Transitive 𝒮 M)`.
Structure, class and transitivity proof, all three as parameters.

It is applied at 43 sites in `src/`, at **at least three different classes**:

- the delivered `isL`, for example `src/L/Coding/Recover.lagda.md:86`;
- a class PARAMETER, `src/L/Definability.lagda.md:278`, whose enclosing
  `module Refine (Atrans : Transitive 𝒮ᵥ M)` is at `src/L/Definability.lagda.md:215`;
- a stage class, `src/L/Hull.lagda.md:153`, `(λ x → x ∈ˢ Lset α)`;
- and the ambient class in the probes, `JoinAtAmbient.agda:85` and
  `GenPowersetAtAmbient.agda:62`.

**A delivered module supplies names at four distinct classes and was never
ported. MEASURED.**

### 6.2 A record of operations: the delivered tree already does this too

`src/FOL/ZFStructure.lagda.md:43` declares `record ZFStructure`, the bundle of
carrier and relations. `src/FOL/Coding.lagda.md:47-52` takes that record plus
**four operations** as parameters: `pr`, `pr-inj`, `encℕ`, `encℕ-inj`.

That one generic module is instantiated at two different structures already:

- `src/V/Coding.lagda.md:231`, at `𝒮ᵥ`;
- `agents/tasks/LJ-1-210/GenModel.agda:212`, at `𝒮ᵥ ↾ M`, the ambient class.

**A delivered module instantiated at two classes, no port. MEASURED.**

`src/L/WellOrder/Base.lagda.md:101` declares `record SWO`, a bundle of an
order and its four laws, consumed as ONE argument at `src/L/Hull.lagda.md:60`.

### 6.3 The delivered tree already carries a DD4-motivated generic module

`src/L/Hull.lagda.md:58-62` declares `module TermAlgebra` generic in the
carrier, the order and the junk element. Its own comment at
`src/L/Hull.lagda.md:56-57` says it is written that way "so the J tower
instantiates the same core (DD4)".

**So DD4 by parameterization is already delivered practice in this tree, with
DD4 named in the code. MEASURED.** No brief in this chain cites it.

### 6.4 What the order actually binds

**It binds the typecheck, and it binds THICK suppliers. It does not bind THIN
ones, and it never bound the dispatch.**

- A **THIN** supplier gives a definition plus a computational lemma. `keyOf`
  and `keyOf-fst` are the measured case (`src/L/Coding/Recover.lagda.md:112-116`),
  and so are the six numerals at `JoinAtAmbient.agda:57-74`, whose every
  obligation is `tt*` or `refl`. For a thin supplier, parameterizing or
  re-deriving DISSOLVES the order.
- A **THICK** supplier gives a theorem. `soundness` from `L.Coding.Sound`
  (`JoinAtAmbient.agda:35`) and `Good.pinned` from `L.Coding.Unique`
  (`:36`, used at `:267`) are theorems with real proofs. Parameterizing there
  MOVES the obligation to the instantiation site and shares nothing, which is
  the opposite of DD4. For a thick supplier, making the module generic IS the
  sharing, and the order among generic modules is a typecheck order.

**C-38 as extended is the guard against over-reading this.** Parameterization
never discharges an obligation; it relocates it. Something must still SUPPLY
an ambient `soundness`. **The order is dissolved for thin suppliers only, and
the work is never dissolved. MEASURED for the thin case at
`src/L/Coding/Recover.lagda.md:112-116` and `JoinAtAmbient.agda:57-74`;
INFERRED for the thick case, because no ambient instance of any theorem
supplier has ever been built.**

### 6.5 What this says about `[LJ-1.220]`, which I did not read

I was told not to treat the opposite bet as settled, and I do not. My answer
is independent and it matches neither bet.

**Parameterizing every leak cannot be right as a blanket rule.** The body takes
about twenty-seven names from eleven suppliers (`JoinAtAmbient.agda:26-39`);
a telescope that wide must be supplied at every instantiation, and theorem
obligations do not become cheaper by being moved.

**Porting bottom-up as a DISPATCH rule cannot be right either.** The next name
is on disk, and section 4 shows the next name did not need a port.

The live question is the thin-thick split of the ten remaining suppliers.
**That is one static reading, and it needs no Agda slot.**

### 6.6 The archive's warning, which is the strongest caution against my own
finding

The retired route BUILT a second class and never instantiated a body at it.
`archive/src/2026-08-09-rud-route/L/Rud/ClassJ.lagda.md:57` defines `isJ`,
`:95` defines `isJ-trans`, and `:118-119` defines `𝒮ⱼ = 𝒮ᵥ ↾ isJ`, with prose
at `:134` saying it "stands beside `𝒮ʟ` at the same cost". **No consumer ever
took it. MEASURED:** the only importer is
`archive/src/2026-08-09-rud-route/L/Rud/Bridge.lagda.md:58`, which takes
`isJ` and `Jset→isJ` and not `𝒮ⱼ` or `isJ-trans`.

**Declaring the second class is cheap and instantiating a body at it is the
thing that has never happened on this project, in either route.** That is the
real content of DD4's remaining risk, and it is why `[LJ-1.219]`'s composition
result matters more than its stop.

The archive's positive shape is carrier-generic, not class-generic:
`archive/src/2026-08-09-rud-route/L/Rud/StepStory.lagda.md:35-36` is generic in
the carrier and a transitivity proof, with a second layer taking operations as
parameters at `:91-100`. `archive/dev/TASKS-archived.md:161` records it as
"instantiated unchanged, no growth". **SHAPE TAKEN, figure NOT taken:** that
axis is the carrier, not the class, and P-l forbids carrying the figure across.

## 7. C-42 IN BOTH DIRECTIONS, PER TARGET

### 7.1 `[LJ-1.216]`

**Further than it claims?** One place. Its section 5 says the shared body at
the ambient class is "the SAME 389 lines as text" (`lj-1.216-report.md:114`).
The file it built has 392 non-blank lines; 389 is the count of a different
file, `agents/tasks/LJ-1-213/GenPowerset.agda`. The claim is true of the body
TEXT and the table column invites reading it as the file's figure.
**MEASURED, immaterial.**

**Less far than it claims?** No. It claims one leaking supplier at one line
and proves exactly that. Its refusal to price the other ten
(`lj-1.216-report.md:104-105`) is correct.

### 7.2 `[LJ-1.219]`

**Further than it claims?** Two places.

1. **`:138` is labelled MEASURED and was never reached.**
   `lj-1.219-report.md:106-107` writes "MEASURED at `JoinAtAmbient.agda:142`
   (`keyOf`) and `:138` (`keyOf-fst`)". Agda reported one error, at `:142`, and
   it checks a `where` block before the clause body that uses it, so the
   signature of `hasKey` at `:142` is checked before the expression at `:138`.
   **`:138` was never reached and its class is INFERRED, not MEASURED.** The
   inference is almost certainly right, since `keyOf-fst` takes the same
   argument. It is still the wrong label. MEASURED that only one error site is
   quoted (`lj-1.219-report.md:78-85`).
2. **"The Model link composes" is measured up to deferred constraints.** Agda
   defers constraints and reports `UnsolvedConstraints` at the end of a module;
   a file that dies at `:142` never reaches that point. So the five names
   elaborated without a REPORTED error, which is not the same as green in a
   completed module. **This is not hypothetical here:** `[LJ-1.216]`'s FIRST
   failure was exactly a deferred `UnsolvedConstraints` in this same file
   family (`lj-1.216-report.md:59-65`). **MEASURED, and it narrows the claim
   without breaking it.**

**Less far than it claims?** Yes, and this is section 4 seen from the other
side. The report treats `L.Coding.Recover` as the next brick
(`lj-1.219-report.md:115-116`). The measured fact is narrower and better: TWO
NAMES leak. **MEASURED: `JoinAtAmbient.agda:26` imports exactly `keyOf` and
`keyOf-fst`, and no other name from that module appears in the file.** The
refutation names two names and the report lets it extend to a module, which is
C-42's failure in the direction the law's authors did not stress.

## 8. DD4: is there anything on record that supports a threshold?

**No. Nothing on record supports a width threshold, and I decline to invent
one. INFERRED, from the absence of any second-tower cost figure.**

What the record holds:

- `[LJ-1.213]`'s 389 shared, 12 plumbing, 8 residual
  (`lj-1.213-report.md:112-114`), all measured at `isL`, with its own DD4 line
  saying the second-tower figure is **INFERRED** (`lj-1.213-report.md:121-125`).
- `[LJ-1.216]` could give no second-tower figure (`lj-1.216-report.md:109-116`).
- `[LJ-1.219]` gives 21 plumbing for the join and correctly refuses to divide
  it by `[LJ-1.210]`'s 19 (`lj-1.219-report.md:133-137`). **That P-l discipline
  is right and I uphold it.**

**A threshold needs a per-module second-tower cost and the record has zero of
them.**

**What the record DOES support, and no brief has used.** The literature answers
the width question from the mathematics side.
`dev/literature/devlin-II5.md:387-389` states: "The per-tower content is
exactly two objects: the level-hood certificate (Step C) and the definable
well-order (Steps D, G)."

**If the mathematics has two per-tower objects and the Agda tree has eleven
tower-fixed suppliers, the gap is an artifact of module authoring, not of the
theorem.** That is an argument FOR the port and it is stronger than any line
count. Section 4 is the first measured instance of the gap being an artifact:
one of the eleven dissolves into two one-line definitions.

## 9. LITERATURE: does `[LJ-1.219]`'s reading hold? YES. And a figure is wrong.

**The reading holds, and it is the most useful sentence in either report.**
`lj-1.219-report.md:193-196` says the table splits mathematics and not modules,
and that `keyOf` is "tower-neutral as an idea and tower-fixed as an Agda term".
`JoinAtAmbient.agda:142` proves the second half at the column level and
`devlin-II5.md:302-303` proves the first: "The proof does not pin the
presentation: any formula with these properties works." **UPHELD.**

Section 4 sharpens it: `keyOf` is tower-fixed as an Agda term **only because
of where it was written**, and its own body is already generic elsewhere.

**The figure quoted by three briefs and both reports is FALSE. MEASURED.**

Three briefs say the table "splits II.5 into nine tower-neutral steps and three
per-tower ones" (`LJ-1.216.md:130`, `LJ-1.219.md:126-127`, and this task's own
brief `LJ-1.221.md:154-155`). Both reports repeat it
(`lj-1.216-report.md:168-169`, `lj-1.219-report.md:186-187`).

I counted the table at `dev/literature/devlin-II5.md:370-383`. It has **12
rows, 8 EITHER and 4 PER-TOWER**:

- EITHER at `:372`, `:373`, `:376`, `:377`, `:378`, `:379`, `:381`, `:382`. Eight.
- PER-TOWER at `:374`, `:375`, `:380`, `:383`. Four.

**The word "nine" does not appear in `dev/literature/devlin-II5.md` at all.
MEASURED by grep.**

**The origin is the citation range.** Every brief cites `:370-382`, which stops
one line before row G at `:383`. Row G is PER-TOWER. The truncated range gives
8 and 3, so the "three" is an artifact of a cut citation and the "nine" is
wrong under either reading.

The false count is not load-bearing, because both reports used the SPLIT and
not the count. It is still a figure that reached five documents unchecked,
which is C-39 and C-40's exact shape.

## 10. WHAT EACH TARGET UNBLOCKS OR CONFIRMS

**`[LJ-1.216]` confirms** that the Powerset body is generic in its own text and
blocked in its imports, and names the first blocker correctly. It unblocks
`[LJ-1.219]`. It is correct and it is spent.

**`[LJ-1.219]` confirms the one thing that had to be built:** two generic
bricks compose at the ambient class, for five names, at `JoinAtAmbient.agda:91`,
`:109`, `:112` and `:126`. **That discharges the composition hypothesis and it
is the whole value of the chain so far.** Every later step now rests on a
demonstrated mechanism rather than a hope.

**`[LJ-1.219]` also unblocks more than it says.** If section 4's test passes,
the join advances past `:142` without any port, and the next measurement is
free.

**Neither unblocks the DD4 question**, and neither could, because both briefs
forbade the work that would.

## 11. EVERY NEGATIVE, CLASSIFIED

| negative | class |
|---|---|
| `[LJ-1.216]`'s stop is wrong | **MEASURED FALSE.** `:68` is as quoted and `𝒮ʟ` reaches it only through Model |
| `[LJ-1.219]`'s stop is wrong | **MEASURED FALSE.** Columns 32 to 41 of `:142` are `lookup y γ`, `keyOf`'s argument |
| the reported line figures are wrong | **MEASURED FALSE.** All five re-derived exactly |
| `[LJ-1.216]`'s 5-added breakdown is exact | **MEASURED FALSE.** The measured delta is 7 added, 4 deleted. Net +3 is right |
| `[LJ-1.216]` was right that Model still needed porting | **MEASURED FALSE.** `GenModel.agda` existed and its own brief named it at `LJ-1.216.md:41` |
| `L.Coding.Recover` is the next brick to port | **MEASURED FALSE as stated.** Only two names are imported, both one-line definitions, all four ingredients generic and green at `GenModel.agda:16-17,193-199,215` |
| the repair at `:142` needs a module port | **INFERRED FALSE.** Named test in section 4.5. P-l: not a price, not an exit code |
| `[LJ-1.219]`'s `:138` site is MEASURED | **MEASURED FALSE.** Agda checks the `where` signature at `:142` first, and one error is quoted |
| "the order is wrong: MEASURED FALSE" is sound | **MEASURED FALSE.** Its evidence confirms one method and tests no alternative. Correct class is INFERRED |
| `[LJ-1.213]` said ORDER, or said port bottom-up | **MEASURED FALSE.** Neither phrase is in `lj-1.213-report.md` |
| the delivered tree cannot supply a name without a port | **MEASURED FALSE.** `FOL.Absoluteness.Single` at four classes; `FOL.Coding` at two |
| parameterization removes the proof work | **MEASURED FALSE for thin suppliers, INFERRED for thick ones.** C-38: it relocates the obligation |
| the literature table is 9 and 3 | **MEASURED FALSE.** It is 8 and 4 over 12 rows, `devlin-II5.md:370-383` |
| fifteen suppliers remain | **MEASURED FALSE.** At most ten, `JoinAtAmbient.agda:24-39` |
| the other suppliers leak | **INFERRED.** No probe reached them. I hold `[LJ-1.219]`'s refusal |
| an ambient instance of a THEOREM supplier is cheap | **INFERRED.** None has ever been built, in either route |
| the retired route instantiated a body at a second class | **MEASURED FALSE.** `𝒮ⱼ` exists and no consumer takes it |

## 12. ARCHIVE USED (DD18)

- `agents/tasks/LJ-1-219/lj-1.219-report.md`, read WHOLE, FIRST, per
  `LJ-1.221.md:161`. TOOK the verdict, the five-name claim at `:92-96`, the
  error text at `:78-85`, the DD4 table at `:123-131`, the negatives table at
  `:155-162`.
- `agents/tasks/LJ-1-219/JoinAtAmbient.agda`, read WHOLE, 407 non-blank lines.
  TOOK the leak site `:142`, the column count, the import list `:24-39`, the
  numerals `:57-74`, the module application `:76-77`, the `using` list `:79-80`.
- `agents/tasks/LJ-1-216/lj-1.216-report.md`, read WHOLE. TOOK the `:68` wall,
  the supplier list `:101-104`, the DD4 table `:112-116`, the "next module to
  port" sentence `:99`.
- `agents/tasks/LJ-1-216/GenPowersetAtAmbient.agda`, read at `:1-100`. TOOK the
  imports `:24-28`, the class `:53-57`, the eta-expanded application `:62`, the
  leak line `:68`.
- `agents/tasks/LJ-1-216/LJ-1.216.md`, read WHOLE. TOOK the abort branches
  `:59-72`, the prohibition `:84-85`, and the naming of `GenModel.agda` at `:41`.
- `agents/tasks/LJ-1-219/LJ-1.219.md`, read WHOLE. TOOK the ORDER sentence
  `:23-26`, the abort branches `:55-71`, the prohibition `:77`.
- `agents/tasks/LJ-1-213/lj-1.213-report.md`, read WHOLE. TOOK the chain-gate
  sentence `:73-75`, which is the sentence this review attacks, and the DD4
  figures `:112-125`.
- `agents/tasks/LJ-1-213/linediff.py`, read and RUN three times. TOOK the three
  diffs in section 1.
- `agents/tasks/LJ-1-213/GenPowerset.agda`, read at `:14-16` and `:60`, and
  diffed. TOOK the pre-cure application and the header telescope.
- `agents/tasks/LJ-1-210/GenModel.agda`, read at `:1-60` and `:188-223`. TOOK
  the parameter list `:13-23`, `prʟ` `:193-194`, `prʟ-fst` `:196-199`,
  `LCode` `:212`, `tagBridge` `:214-215`. **This is the finding of section 4.**
- `agents/tasks/LJ-1-211/lj-1.211-report.md`, read WHOLE. TOOK the cause split
  `:15-21`, category 2 at `:63-103`, and the premise-gate proposal `:282-305`.
- `src/L/Coding/Recover.lagda.md`, read at `:57`, `:66`, `:69`, `:84`, `:86`,
  `:105-120`. TOOK the header, the fixing line, the Model imports, and the two
  definitions.
- `src/L/Coding/Powerset.lagda.md:57`. TOOK the sole `Recover` import.
- `src/FOL/Absoluteness.lagda.md:57-59`, `src/FOL/Coding.lagda.md:47-52`,
  `src/FOL/ZFStructure.lagda.md:43`, `src/L/Hull.lagda.md:56-62`, `:153`,
  `src/L/Definability.lagda.md:215`, `:278`, `src/L/WellOrder/Base.lagda.md:101`,
  `src/V/Coding.lagda.md:231`. TOOK the three delivered mechanisms of section 6.
- The 23 modules under `src/L/Coding/`, surveyed at their structure-fixing
  lines. TOOK the count and the fact that none takes a class parameter.
- `archive/src/2026-08-09-rud-route/L/Rud/ClassJ.lagda.md:57`, `:95`,
  `:118-119`, `:134`, and `L/Rud/Bridge.lagda.md:58`. **TOOK the warning of
  section 6.6:** the second class was built and never instantiated.
- `archive/src/2026-08-09-rud-route/L/Rud/StepStory.lagda.md:35-36`, `:91-100`.
  **SHAPE TAKEN:** a generic master plus an operations layer.
- `archive/dev/TASKS-archived.md:161`, `:163`, `:225`, `:226`, `:243`, `:244`.
  Read for shape. **FIGURE NOT TAKEN:** those rows price a carrier-generic
  axis on the retired route, and P-l forbids carrying the number to a
  class-generic axis here.
- `dev/PLAN.md` and `dev/JOURNAL.md`: NOT read. Nothing in this review rests
  on a status cell. Every claim is at a file the claim is about.

## 13. LITERATURE USED (DD18)

- `dev/literature/devlin-II5.md:302-303`. **USED.** "The proof does not pin the
  presentation: any formula with these properties works." This is the
  load-bearing sentence for section 6: if the mathematics does not pin the
  presentation, a tower-fixed Agda type is an authoring choice.
- `dev/literature/devlin-II5.md:370-383`, the whole table, counted row by row.
  **USED** to check the 9-and-3 figure, which is false; the true split is 8 and 4.
- `dev/literature/devlin-II5.md:387-389`. **USED, and no brief has used it.**
  "The per-tower content is exactly two objects." This is the strongest
  argument for the port on the record and it is a mathematical statement, not
  a line count.
- `dev/literature/devlin-II5.md:299-310`, the summary of strengths, and Jech's
  alternative engine at `:304-307`. **WHY NOT USED for a verdict:** it
  concerns the choice of level formula, and no target in this review touches
  the level formula. It supports `:302-303` and nothing further.
- `dev/literature/devlin-II5.md:312-362`, the engine list. **WHY NOT USED:**
  it names what II.5 assumes and proves nothing about Agda module structure,
  which is the whole subject of both targets.
- No other literature file read. The two targets are module-structure
  measurements, and the DD18 requirement is met by the file the briefs cite.
