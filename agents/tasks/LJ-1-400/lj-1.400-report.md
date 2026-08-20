# [LJ-1.400] The coded square law at a generic L-cardinal

Date: 2026-08-20. Slot: `coder`. Probe:
[`Probe400.agda`](Probe400.agda), 195 lines, GREEN.
Written incrementally (C-22). No commit, no push. One Agda process.
Caliber on this pane: `GHCRTS="-A64m -I0 -M8g"`. This slot did not set it.

TARGET: one term `card-pair-code` at a generic L-cardinal, and a residue
type `card-owes`. The brief also names the W3 probe `collapse-states`.

## VERDICT

**NO-GO on the coded route. GO on the W3 statement.**

Both named obligations typecheck:

- `card-owes` at `Probe400.agda:164-170`
- `card-pair-code` at `Probe400.agda:178-195`

`card-owes` is not the unit type. The construction stops before it
builds a graph. The door packages a graph that the code does not
supply. The coded route of `[LJ-1.386]` therefore stays open.

`collapse-states` is written, with no proof, at
`Probe400.agda:148-153`. `src/` does not hold this formula. Grep over
`src/` for `godAt` and for `collapse-states` returns no hit.

The statement cost 52 code lines, against the brief's estimate of about
300. Nothing may be funded against 300. The 52 is the measured size of
the statement. It is not a price for a proof.

## 0. LITERATURE (W8), BEFORE ANY AGDA

The literature does not stop the task.

The square law is a theorem. An infinite cardinal squared is itself.
No source in this corpus uses the short name "square law" for that
fact (`dev/literature/terms-2026-08.md:37`). The fact is not an axiom.

The Gödel pairing appears here as a HYPOTHESIS of SZ 1.17. That lemma
gives a surjection `g : α → J_α^A` when `α` is closed under the pairing
function (`dev/literature/j-hierarchy.md:111`;
`dev/literature/digest.md:241`). That hypothesis is a condition on
`|J_α| = |α|`. It is not a condition on `κ × κ ↪ κ` at an L-cardinal.

Devlin's GCH chain uses 1.1(vii) as a size fact
(`dev/literature/devlin-II5.md:160`). It does not add a side condition
that this tree fails.

So W8 does not abort. The rest of this return is the coding question.

## 1. WHAT WAS ASKED, AND WHAT IS DELIVERED

The brief asked for two terms at a generic L-cardinal. Both exist.

| Term | Line | What it is |
|---|---|---|
| `collapse-states` | `Probe400.agda:148` | the object-language statement of the collapse, no proof |
| `godAt` | `Probe400.agda:93` | the Gödel order as a formula, no proof |
| `maxAt` | `Probe400.agda:83` | the max atom, copied from `[LJ-1.327]` |
| `card-owes` | `Probe400.agda:164` | the residue: a graph that satisfies the statement, that is an `InjCode`, and that sits at the product's stage bound |
| `card-pair-code` | `Probe400.agda:178` | the door's input, from that residue |

`[LJ-1.399]` is not in the tree. This probe prices against `IdGraph`
(`agents/tasks/LJ-1-386/Probe386.agda:94-193`), as the brief ordered.

## 2. WHICH ROUTE, AND WHY

**Route A: code the ambient collapse.** Route B is not cheaper.

The ambient pairing is `col`, by well-founded recursion
(`src/L/Ordinal/SquareLaw.lagda.md:383-387`). `via-col-square` is the
ambient theorem (`:960-961`). Route B still needs the graph of that
map. The formula that names the graph is the shared cost. Route A
reuses the delivered `col`. Route B would rebuild the same values
under another name.

`[LJ-1.327]` already found the template: `hierAt` turns an ambient
well-founded recursion into an L-set by `hasReplacementL`
(`src/L/Hierarchy.lagda.md:536-595`;
`agents/tasks/LJ-1-327/lj-1.327-report.md:163-178`). The collapse runs
over `≺` rather than `∈`. The shape is the same. This probe did not
run that replacement. It wrote the formula that the replacement would
consume.

## 3. W3, `collapse-states`

The object-language statement, with no proof:

    for every p ∈ P, there is γ such that F(p) = γ and
    γ = ⋃ { suc(F(r)) | r ∈ P and r ≺ p }.

That is `col-compute` (`src/L/Ordinal/SquareLaw.lagda.md:387`) as a
formula. The file composes it from:

- `maxAt` (`Probe400.agda:83-85`), the atom `[LJ-1.327]` already
  measured (`agents/tasks/LJ-1-327/ProbeLJ1327A.agda:132-134`)
- `godAt` (`Probe400.agda:93-120`), the Gödel order on two coded pairs
- `appAtCon` (`Probe400.agda:124-125`), application against a constant
  graph, because `appAt` takes a variable
  (`src/L/Coding/Model.lagda.md:160-161`)
- `extAt′` (`Probe400.agda:129-131`), the two implications of `extAt`
  (`src/L/Coding/Model.lagda.md:662-664`)
- `sucAtL` (`src/L/Coding/Model.lagda.md:1395`)
- `prAtL` (`src/L/Coding/Model.lagda.md:122`)

**Does `src/` hold a formula for the collapse? No.** Grep over `src/`
for `godAt` and for `collapse-states` returns no hit. The tree holds
the atoms. It does not hold the composed statement.

**Measured size of the statement: 52 code lines** in
`Probe400.agda:83-153`. First green check 5.93 s. Warm recheck 1.64 s.
Both at `-A64m -I0 -M8g`, one process, exit 0. Load before the green
runs was 1 or 2 other Agda processes on the machine.

The brief's estimate was about 300. The statement is smaller. The
estimate was for a formula that might have needed new vocabulary. The
vocabulary is already there. The cost that remains is adequacy, and
the replacement that builds the graph.

## 4. THE TWO OBLIGATIONS

`card-pair-code` is the packaging `[LJ-1.386]` measured for the
identity (`Probe386.agda:203-214`). It transports `InjCode` along
`SiteBound.up`. The `isL` proof is the only change
(`Probe400.agda:194-195`).

It does not build a graph. It consumes `card-owes`.

`card-owes` names three conjuncts, at a generic `κ`:

1. `F` satisfies `collapse-states` on `prodL κ κ`
2. `InjCode F (prodL κ κ) κ`
3. `fst F` is a member of `Lset` at the product's own stage bound

None of the three is discharged. The first needs adequacy of
`collapse-states` against ambient `col`, then `hasReplacementL` with a
functionality proof. The second needs the four conjuncts of `InjCode`
(`src/L/Cardinal.lagda.md:223-228`). The third is not the free
placement of `IdGraph`. See section 5.

## 5. WHAT THE RESIDUE STILL IS

`IdGraph` builds `{ ⟨x,x⟩ : x ∈ D }` by replacement on
`y = ⟨x,x⟩` (`Probe386.agda:97-117`). The value is a closed term of
the argument. `col p` is not a closed term of `p` in the object
language. The identity pattern does not transfer. `[LJ-1.327]`
measured that fact at `lj-1.327-report.md:42-56`. This probe did not
re-measure it. It used that report.

The remaining work, named, not priced at this site:

| Piece | What it is | Comparable, not a price here |
|---|---|---|
| adequacy of `godAt` | both directions against `_≺_` | `[LJ-1.327]` wrote `maxAt` both ways in 60 code lines (`ProbeLJ1327A.agda:132-206`) and estimated the full order at about 150 |
| adequacy of `collapse-states` | the formula means `F(p) = col p` | unmeasured |
| the replacement | `hasReplacementL` along `≺`, values from ambient `col` | `hierAt` at `src/L/Hierarchy.lagda.md:536-595` |
| `InjCode` at source `prodL κ κ` and target `κ` | four conjuncts | `IdGraph.idCode` at `Probe386.agda:186-187` |
| range in `κ` | `Init`'s fourth conjunct, from `IsCardinalL` | spent ambiently at `src/L/Ordinal/SquareLaw.lagda.md:876` |
| placement at `SiteBound.β (prodL κ κ)` | the DOMAIN's bound, not the graph's | `IdGraph.G∈` places the graph at the graph's own bound (`Probe386.agda:190-192`) |

**The placement conjunct may be false.** `Leg1` searches in
`Lset (SiteBound.β P)` (`Probe386.agda:288-290`). `IdGraph` searched
in `Lset (SiteBound.β G)` with `G` the graph. A set of pairs
`⟨p, col p⟩` appears after `P`. D-10 applies: a residue can name a
false target. This probe did not prove the conjunct false. It also did
not prove it true. The next brief should check it before it funds a
discharge.

`[LJ-1.327]` estimated about 820 lines for a coded square law at a
generic ordinal (`lj-1.327-report.md:184`). That number is not a price
here. P-l forbids the transfer. Two pieces of that estimate are now
delivered at other sites: `prodL` (`Probe388.agda:296`) and the max
atom (`ProbeLJ1327A.agda:132-206`). A fourth `Carve` is not needed.
`[LJ-1.386]` discharges `InjCode` without `Carve`.

**Nothing in this return funds a construction against 300, or against
820.**

## 6. W2

The construction is generic in `κ`. No line names a site, a band, or
`ω` as a carrier. `⟨ ω ∈ fst κ ⟩` is a hypothesis of `card-owes` and
of `card-pair-code`, as the brief required. `collapse-states` is
generic in the product `P` and the graph `F`.

## 7. TWO STATEMENTS ABOUT THE LAST OBLIGATION

The brief asked which of two claims this return checked.

**Checked.** With this conjunct paid, `Leg1` is complete at a
cardinal, and `leg1-gives-sq` returns the ambient square law as data
(`agents/tasks/LJ-1-386/Probe386.agda:294-295`). The term is in the
tree. This return read it.

**Taken on report.** `[LJ-1.398]`'s recursion carries that fact to
every band ordinal. `[LJ-1.398]` is not in the tree. This return did
not read a file for it.

## 8. W1 AND `[LJ-2.5]`

The brief asked: if coding one definable ambient map needs the
rudimentary tower, then the J tower is on the critical path for GCH.

**The evidence does not support that reading.**

The formula of the collapse is first-order over atoms the Def tower
already has (`prAtL`, `sucAtL`, `extAt`, bounded quantifiers).
`hierAt` already turns an ambient well-founded recursion into an
L-set, by `hasReplacementL`, on the Def tower
(`src/L/Hierarchy.lagda.md:536-595`). The obstruction is an unbuilt
formula and an unbuilt replacement along `≺`. Both are Def-tower
work. This probe wrote the formula. It did not write the replacement.

A rud Gödel operation would be a different construction of the same
graph. It is an alternative. It is not a necessity measured here.

D18 kept the trophy on the Def tower
(`archive/dev/DECISIONS-archived.md:40`). This return does not reopen
that ruling. `[LJ-2.5]` is where the architecture is ruled. This
measurement does not move it.

## 9. THE PRICE OF WHAT RAN

Caliber `-A64m -I0 -M8g`. One Agda process. No heap wall.

| run | what | exit | real seconds | load before |
|---|---|---:|---:|---:|
| check-1 | parse error in `godAt` | 42 | 0.07 | 2 |
| check-2 | parse error, `godAt` rewritten | 42 | 1.64 | 1 |
| check-3 | `_+_` not in scope | 42 | 1.70 | 2 |
| check-4 | first green | **0** | 5.93 | 1 |
| check-5 | warm recheck | **0** | 1.64 | 1 |

The empty-module floor was not remeasured. The 388 floor of 0.06 s is
not a number this probe may quote as its own.

File: 195 lines, 111 code lines (non-blank, not comment-only). The
W3 block is 52 of those 111.

## ARCHIVE USED

- **`archive/dev/JOURNAL-archived.md`.** Read.
  `archive/dev/JOURNAL-archived.md:1732`: "The untruncated equivalence
  remains unavailable (T31's wall) and the". The door of
  `[LJ-1.386]` returns an injection as data. It does not return a
  bijection. This line is that wall.
- **`archive/dev/DECISIONS-archived.md`.** Read.
  `archive/dev/DECISIONS-archived.md:40`: "The trophy stays on the Def
  tower; there is no re-founding onto the rud/J tower." Used in
  section 8. A NO-GO that needed rud would speak to `[LJ-2.5]`. This
  NO-GO does not need rud.
- **`dev/ARCHIVE.md`.** Read.
  `dev/ARCHIVE.md:1`: "# ARCHIVE.md: the archive registry". Searched
  for SquareLaw and for pairing. No module row. The registry did not
  supply a retired coded pairing to revive.
- **`archive/dev/TASKS-archived.md`.** Read.
  `archive/dev/TASKS-archived.md:82`: "| L3.32-T47 | Truncated square
  law at initial ordinals | DELIVERED |
  `_build/l3.32-t47-report.md` |". That is the ambient theorem this
  task was to code.
- **`archive/src/2026-08-09-rud-route/Everything.lagda.md`.** Read.
  `archive/src/2026-08-09-rud-route/Everything.lagda.md:307`: "the
  least-of search returns its witness only up to".
  `:308`: "truncation, and no canonical bijection exists to make it
  honest." Confirms the door's limit: injection, not bijection.

## LITERATURE USED

- **`dev/literature/devlin-II5.md`.** Read.
  `dev/literature/devlin-II5.md:160`: "> Proof. By 5.5, 𝒫(κ) ⊆ L_{κ⁺}
  for all infinite cardinals κ. So by 1.1(vii),". GCH uses the square
  law as a size fact. No extra condition.
- **`dev/literature/truncation-and-selection.md`.** Read.
  `dev/literature/truncation-and-selection.md:79`:
  "`card(A) ≤ card(B) :≡ ∥ inj(A,B) ∥`". The door's truncated existence
  is the classical conclusion. Used to read `card-pair-code`'s `∥ _ ∥₁`.
- **`dev/literature/digest.md`.** Read.
  `dev/literature/digest.md:241`: "surjection g : α -> J_α^A when α is
  closed under Gödel pairing (SZ 1.17).". W8: pairing-closure is not
  a condition on the square law at a cardinal.
- **`dev/literature/geology.md`.** Declined. The file is about
  grounds, the mantle, and Hamkins. It does not treat the square law
  or the Gödel pairing.
- **`dev/literature/terms-2026-08.md`.** Read.
  `dev/literature/terms-2026-08.md:37`: "| 8 | square law | 平方律 |
  no literature under that name; the fact is 无穷基数的平方等于自身；no
  source uses 平方定理 for it | yes |". W8: the fact, not the name.

Also read, not in the injected candidate list, because the brief named
them:

- `dev/literature/j-hierarchy.md:111`: "if α is closed under the Gödel
  pairing function then there is a surjection"
