# LJ-1.38 review: the DD25 adversarial review of a negative return

Status: COMPLETE. Written incrementally per C-22. No commit, no push.
The review uses ASD-STE100.

Probes: `src/ProbeDD25E1.agda` (green), `src/ProbeDD25E2.agda` (green),
`src/ProbeDD25E3.agda` (the control, red by design). All three are
untracked and thrown away per D-1.

## 1. THE VERDICT

**UPHOLD.** The refusal is correct.

**Committed content is defective and must be reworked.** The defect is
in `src/L/Condensation.lagda.md`. It covers block 2, which
`[LJ-1.37]` committed at `92e8b8b`, and block 1, which `[LJ-1.5]`
committed earlier. About 968 of the master's 2,141 in-fence lines carry
it.

Three things qualify that sentence, and each one matters.

1. **No false theorem stands in the tree.** Every delivered theorem in
   the master is a Δ₀ witness, a two-way decode, an erase transfer or a
   Σ₁ certificate. Each one is true of the formula it names. The
   formulas are wrong; the theorems about them are not. I grepped the
   master for a committed story-to-machine agreement and found none:
   the only `adequate` uses are the delivered `appAt-adequate` inside
   the decodes (`src/L/Condensation.lagda.md:269,289,748,767,790,809,
   827,858,895`). So nothing must be retracted. Definitions must be
   corrected.
2. **The defect is worse than the return says, on two counts.** The
   atom rows are not weak. They are FALSE of the true satisfaction
   table. And block 1 carries the same defect, which the return
   recorded only as an uncertainty.
3. **The cure is cheaper than the return says, on one count.** The
   correct frame is already delivered and eleven of the twelve rows
   already use it. The description block keeps its type and does not
   need a re-lay.

The return's positive measurement is sound. I re-measured the master
cold, one process, at `GHCRTS="-A64m -I0 -M8g"`, with its own interface
moved aside and the dependencies warm: **9.47 seconds of user time,
10.70 wall**, green. The return reported 9.60 to 9.65 user. My run is
inside the noise band. The rate is 9.47 / 2,141 = **0.00442 seconds per
line**, against the return's 0.00449 and DD24's bar of 0.013193. I
count 2,141 in-fence non-blank lines in the master, which matches the
return exactly.

## 2. THE VACUITY CLAIM

**The claim is TRUE. I machine-checked it.** The probe is
`src/ProbeDD25E1.agda`. It checks green in 2.59 seconds wall, 1.54
user, one process, at `GHCRTS="-A64m -I0 -M8g"`.

### 2.1 The two endings are not equivalent

`extAt y φ` is BOTH directions
(`src/L/Coding/Model.lagda.md:662-664`):

```
extAt y φ = ∀̇ ((var zero ∈̇ var (suc y)) ⇒̇ φ)
         ∧̇ ∀̇ (φ ⇒̇ (var zero ∈̇ var (suc y)))
```

The story's frames end in `∀̇∈ (var yc) body`, which is the first
direction only, and bounded by the value itself
(`src/L/Condensation.lagda.md:638,657,695,716`). The probe states both
endings against the delivered semantics:

- `story-vacuous`: at an empty value the story's ending is discharged
  by `Empty.rec`. It asserts nothing.
- `machine-binds`: at an empty value the machine's ending forbids every
  satisfier, through the delivered `extAt-in`.
- `no-transfer`: the story's ending does NOT imply the machine's. The
  countermodel is concrete, not hypothetical: `numeralL 0` at the value
  slot, which is the empty set of L, and `⊤̇` as the body.

The frames really do end that way, and the evidence is delivered code
rather than my reading. `BinEnvDecode.binEnv-in`
(`src/L/Condensation.lagda.md:900-913`) has this innermost hypothesis:
`(e : S) → ⟨ fst e ∈ fst yc ⟩ → ⟨ (e ∷ E ∷ yc ∷ b ∷ a ∷ ar ∷ c ∷ γ) ⊨
body ⟩`. Block 1 spells its binder list in its own comment
(`:132-133`): `e (∀∈yc)`.

### 2.2 The return stopped one step early, and the next step is worse

At a NONEMPTY value the delivered atom row is not weak. **It is false
of the true satisfaction table.**

The probe's `story-forces-all` proves it. Take the delivered
`Mem.bodyM` at the environment the delivered decode hands over. Take
ONE member `e` of the value `yc`. Then EVERY member of `E` that lies in
`K` is a member of `yc`:

```agda
  story-forces-all : (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ δ e ⊨ Mem.bodyM C T B N K t0 t1 ⟩
    → (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩ → ⟨ fst z ∈ fst E ⟩
    → ⟨ fst z ∈ fst yc ⟩
  story-forces-all e e∈ h z z∈K z∈E = h .snd z z∈K (z∈E , h .fst e e∈ .snd)
```

The reason is one de Bruijn index. The story's atom body reads both
term values at the FRAME's member `e`, not at the extension candidate
`z` (`src/L/Condensation.lagda.md:946,952` against
`src/L/Coding/Model.lagda.md:1749,1756-1757`). So the defining
condition never mentions the element it defines. The inner `extAtB`
then equates `yc` with all of `E ∩ K`.

The two rows are therefore incompatible. The probe's `clash` proves it:

```agda
  clash : (e : S) → ⟨ fst e ∈ fst yc ⟩
    → ⟨ δ e ⊨ Mem.bodyM C T B N K t0 t1 ⟩
    → ⟨ μ ⊨ extAt (suc zero) (atomBody memRel) ⟩
    → (z : S) → ⟨ fst z ∈ fst (lookup K γ) ⟩ → ⟨ fst z ∈ fst E ⟩
    → (⟨ (z ∷ μ) ⊨ atomBody memRel ⟩ → Empty.⊥)
    → Empty.⊥
```

Read that plainly. The story's Mem row and the machine's Mem row cannot
both hold at a value that is nonempty and misses one member of `E` in
`K`. That is the normal case for an atom. So the story's row is not a
weaker description of the true table. It EXCLUDES the true table.

### 2.3 The control, which makes the probe evidence

A proof that goes through is only evidence if it fails against correct
content. `src/ProbeDD25E3.agda` repeats `story-forces-all` word for
word against a body that differs from the delivered `atomBodyB` in ONE
index: the environment argument of the two term readers moves from
`suc (suc (suc zero))`, the frame's member, to `suc (suc zero)`, the
extension candidate. Agda rejects it:

```
src/ProbeDD25E3.agda:82.50-66: error: [UnequalTerms]
fst e != fst z of type Cubical.HITs.CumulativeHierarchy.Base.V ℓ
when checking that the expression h .fst e e∈ .snd has type ...
```

So the collapse is the delivered index, and not an artefact of my
proof. The control also names the target of the cure.

## 3. DOES THE VACUOUS CASE ARISE AT THE REAL SITE?

**The cheapest cure does not work. The same probe refutes it.** I
checked it because the brief asked, and the answer is NO.

The hoped-for cure was an extra hypothesis: the value is nonempty
wherever the row is used. Split the twelve rows by whether the body
uses the frame's bound member. I checked every index in every body.

- **Six rows never use it**: Top, Neg, Forall, And, Or, Imp. There
  `∀e∈yc φ` is exactly `yc nonempty → φ`. The hypothesis WOULD save
  those six.
- **Five rows use it**: Mem, Eq, AllIn, ExIn, Exist. There the
  hypothesis makes the row worse, not better. `clash` NEEDS the value
  to be nonempty. Nonemptiness is what turns the row from silent into
  false.
- **One row has no such binder**: Bot, which uses `unBareAt`.

The hypothesis also fails on its own terms for the six rows, because it
is false at the site.

- The story's own Bot row asserts the value IS empty
  (`src/L/Condensation.lagda.md:1080`, `emptyB`). So the description
  itself contemplates empty values.
- Any code whose matrix is unsatisfiable has an empty value. `⊥̇` is
  such a code and the table must carry it.
- A description that assumes its own answer is circular. To discharge
  "this value is nonempty" you must already know the value.

So no delivered bound fact rescues the rows, and `[LJ-1.35]`'s bound
facts are the wrong kind of fact for this. They are membership facts.
The gap is about which element a condition speaks of, and about a
missing second direction. **A site fact DOES help, but not here.** See
section 6.3.

## 4. IS THE MACHINE CORRECT?

**The return is right and my brief is wrong.** There is no machine
defect. Settled at `file:line`:

| what | where | what it says |
|---|---|---|
| the slot layout comment | `Model.lagda.md:1745` | `w = 0, v = 1, e = 2, E = 3, yc = 4, b = 5, a = 6` |
| the slot definitions | `Model.lagda.md:1746-1751` | `b9″ = suc (suc (suc (suc (suc zero))))`, which is slot 5, the TERM slot `b` |
| the atom body | `Model.lagda.md:1753-1759` | `tmValAt a9″ e9″ v9″` and `tmValAt b9″ e9″ w9″` |
| the brief's cited range | `Model.lagda.md:1765-1770` | `AtomWit` (`:1764-1767`) and the head of `atomBody-in` (`:1769-1771`). It contains NO slot definition |

The machine reads the two term slots, both at the `extAt` candidate.
That is the correct reading. The value slot `yc` is slot 4 and the
machine's atom body never reads a term from it.

Two consequences for the orchestrator.

1. **No delivered master needs an edit.** Neither option my brief told
   the agent to price was necessary. `src/L/Coding/Model.lagda.md` and
   its consumers stay closed.
2. **The machine is the specification.** The story must move to the
   machine, in every row. The return says this and it is right.

## 5. DID THE BRIEF CAUSE IT?

**Partly, and the quote is mine.** `_build/briefs/LJ-1.38.md:62-68`:

> `[LJ-1.37]` found a machine quirk no probe had surfaced:
> The delivered `atomBody` reads the second term's value from the VALUE
> slot `yc` rather than the TERM slot `b`
> (`src/L/Coding/Model.lagda.md:1765-1770`).

The claim is false. It is not mine originally: it comes from the
`[LJ-1.37]` return (`_build/lj-1.37-report.md:133-137` and `:230-233`).
My brief carried it forward as a found fact. The same brief lists D-10
in its mandatory rules (`LJ-1.38.md:175`): "Every figure here is a
residue. Re-verify before building on it." I broke my own rule in the
same document that states it. C-33 was admitted for this failure and it
happened again.

**What it cost.** The agent spent its whole atom-row section refuting
the premise and then priced two cures that were never needed. Its
option table (report section 2) gives two lines to non-existent tasks
and one line to the real one. The brief also gave it a stop-line
("if either exceeds the block's whole 4-second survey, STOP"), which
invited a stop at a wall that does not exist. The brief did NOT hide
the real defect, and the agent found it anyway. So the harm is wasted
work and a mis-shaped price, not a wrong verdict.

**The deeper cause is not this brief.** It is the `[LJ-1.37]` and
`[LJ-1.5]` briefs. Both asked for a bounded RESTATEMENT of delivered
formulas. Both gated it on syntax: a Δ₀ witness, `countFo = 0`, no
placement, and check time. **No gate asked whether one row MEANS what
the machine's row means.** Every mechanical check passed and eleven
rows are wrong. `[LJ-1.36]` even recorded the reason the comparison
never happened: eight rows have no public whole-row reader, so the
machine's rows are private and an outside reader never unfolds them.
That finding was reported as a cost, and it was also a warning.

**Candidate law, with its measurement.** A bounded restatement of a
delivered formula must carry a satisfaction-level agreement for at
least ONE row, in the same dispatch that builds the rows. Measurement:
the omission carried 968 in-fence lines of wrong meaning through two
dispatches and four green gates, and cost three dispatches to find. The
agreement that would have caught it is small: my `ProbeDD25E1` and
`ProbeDD25E2` are 176 lines together and each checks in under 3
seconds. The orchestrator assigns the ID.

## 6. THE TRUE SCOPE OF ANY REWORK

The return says "a re-lay of the five frames, the twelve bodies, the
certificates and the frame decodes". That is accurate for what it
names. It understates the scope in one place and overstates it in
another. Here is the measured breakdown, by the ledger's caliber.

### 6.1 What is re-opened: about 968 in-fence lines of 2,141

| region | lines | why |
|---|---:|---|
| block 1: `Clause`, `ClauseDecode`, the certificate (`:54-366`) | 269 | `existBndAt` (`:133-141`) has the same `∀e∈yc` binder, and `bodyBnd` (`:100-106`) has NO `extAtB` at all. Both defects |
| the five frames and their Δ₀ witnesses (`:629-732`) | 94 | four of five carry the extra binder |
| the frame decodes (`:733-916`) | 174 | four of five lose one argument. `UnBareDecode` survives |
| the eleven row bodies and rows (`:917-1400`) | 431 | every body re-indexes |

**The return listed block 1 only as an uncertainty (its item 4). It is
not an uncertainty.** Block 1 is defective on both counts, and it
carries the `EraseTransfer` instantiation and the Σ₁ certificate.

### 6.2 What survives, which the return missed

| region | lines |
|---|---:|
| the bounded atoms (`:368-628`) | 223 |
| the description region (`:1401-2251`) | 798 |
| block 3, this task's own work (`:2252-end`) | 111 |

The reason is a type. A frame's OUTER type is `Formula S m` and the
repair does not change it. Only the body argument's arity changes. So
`twelveB`, `satGraphB`, `DefBodyB` and `Δ₀-DefBodyB` need RE-CHECKING,
not re-laying. The 227-line bounded code-set description stands. This
is worth about 1,021 lines against the return's framing, and it is why
the rework is a re-index rather than a rebuild.

### 6.3 The shape of the work, which is mechanical

**The correct frame is already delivered.** `extAtB`
(`src/L/Condensation.lagda.md:394-396`) is the bounded two-way
extension frame, and it is right. Eleven of the twelve rows already use
an `extAtB`-based operation inside (`emptyB`, `sameB`, `diffB`,
`interB`, `unionB`, `implB` at `:519-556`, and `extAtB` directly in
Forall, Mem, Eq, AllIn, ExIn). Only `Exist` and block 1's `Clause` have
none.

The repair per row is: delete the frame's final binder, then lower
every body index that points above the removed slot. For Mem, Eq, AllIn
and ExIn that single decrement lands the term reader on the extension
candidate, which is the machine's point. `ProbeDD25E3` proves the
corrected index is the right target, because the collapse proof fails
against it.

**Two rows need more than a decrement.**

- `Exist` (`:1375-1381`) must be wrapped in `extAtB`. It has one
  direction and no extension frame at all. Block 1's `bodyBnd` is the
  same case.
- `Forall` (`:1142`) has a genuinely wrong slot. Its extended
  environment lands on `E`; the machine's lands on the subvalue `ya`
  (`src/L/Coding/Model.lagda.md:1573`). A decrement does not fix it.
  `ProbeDD25E1` pins both slots by `refl`.

**And the transfer closes.** `src/ProbeDD25E2.agda` proves
`extAtB y K φB → extAt y φ` under two hypotheses: the leaves agree, and
every satisfier lies in `K`. The second is the site fact, and the row's
own leaf supplies it, because the leaf says the candidate lies in `E`
and `E` lies in `K`. The converse direction needs no site fact at all.
So the corrected frame reaches the machine's frame with NO new
machinery. **That is where the site facts help. It is not where my
brief looked.**

### 6.4 What I do not price

I do not price the dispatch in seconds. I measured the shape, not the
cost. Two facts bound it. The work adds no new construct. The master
checks whole in 9.47 seconds today, and a re-index does not change its
class.

## 7. WHAT I AM NOT SURE OF

1. **I proved incompatibility for the Mem row only.** `clash` is about
   `Mem.bodyM` against the machine's `atomBody memRel`. I checked
   AllIn, ExIn, Forall and Exist by index arithmetic and by two `refl`
   lemmas, not at the satisfaction level. I expect the same result and
   I did not machine-check it.
2. **I did not prove the corrected rows CLOSE leg D.** `ProbeDD25E2`
   proves the frame transfer under a leaf-agreement hypothesis. The
   leaf agreement itself, `tmValB` against `tmValAt` and bounded
   against unbounded, is the real work of the next dispatch. I did not
   price it.
3. **The description's class.** I argue the weak rows do not pin the
   graph, and that the atom rows exclude the true graph. I did not
   build the countermodel table, so the first half is an argument and
   the second half is machine-checked.
4. **The return's row 3 is half wrong, and it does not change the
   verdict.** For AllIn and ExIn the return says "story extends the
   environment in `E`, machine in the subvalue". Both sides use the
   subvalue (`Condensation:1009,1027` land on `ya`;
   `Model:1873` lands on `yb`). The other half of that row, the bound
   term read at the frame's member, is TRUE.
5. **A bound asymmetry I did not settle.** `bndBodyAll` bounds its
   inner quantifier by `B` (`:998`) and `bndBodyEx` bounds its by `K`
   (`:1016`). The machine uses an unbounded quantifier in both
   (`Model:1881,1887`). I do not know whether the asymmetry is
   deliberate.
6. **Block 3's size.** The return reports 110 in-fence lines and I
   count 111. It is a one-line boundary difference and it is not
   material.
7. **My seconds are one run.** I measured the master once, cold for its
   own interface and warm for its dependencies, while a sibling held
   the other Agda slot. The figure agrees with the return's flat pair,
   so I did not spend a second run.
