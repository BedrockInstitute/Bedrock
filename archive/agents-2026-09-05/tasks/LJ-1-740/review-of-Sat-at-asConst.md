# Review of `Sat-at-asConst`: park review, for the critic and the next dispatch

- task: LJ-1.740
- writer: coder
- probe: `agents/tasks/LJ-1-740/Probe740.agda` (555 lines, TYPECHECKS,
  EXIT=0, `runs/p-104.out`, 1.82 s, 417,611,776 B peak, wide caliber,
  no postulate, no hole, nothing in `src/`)
- this file is a PARK REVIEW, not a NO-GO.  The obligation's type is
  priced TRUE (D-10 below).  The dispatch did not close it;  what is
  green, what is parked, and the exact continuation are recorded here.

## 1. The target is true

`Sat-at-asConst` states the bound at the carrier-bounded alphabet:  the
constants of `mapFo (asConst A) ψ` are `asConst A m`, whose underlying
sets sit in the carrier, and the carrier sits below γ by hypothesis.
The 736 defect (an unplaced constant above γ) cannot fire:  every
`cond`-witness -- the atom escorts, the numeral witness of tmIs, the
quantifier extenders -- is bounded, by the stage set `Lset σ₀` or by
`envSet A (suc n)`, both placed below γ by the room.  The D-10 atom
pricing the brief asked for (`var 0 ∈̇ asConst m` first) is done:  the
atom clause's witnesses reach the stage set through z's membership
chain (`slot-bounded`/`asConst-bounded` in the probe) and are
machine-checked to the extent the delivered bytes typecheck.

## 2. What is machine-checked green in the delivered bytes

Runs p-103/p-104, EXIT=0:

1. The scaffold (`WithStage`):  σ₀ = +ω (+ω m), the stage set `Om`,
   the room (A, envSet A k at every arity, numerals, asConst values),
   the monotone lifts, `mem-trans`, `snd∈L`.
2. The placement core (`SatPlace.place`):  the AtStage carve of the
   bound-conjunction, identified with `Sat A χ` by extensionality,
   placed at `Lset (sucV β)`.  This is the engine the climb calls.
3. The arithmetic (`plus-zero/plus-suc/plus-assoc`, the bare order
   `≤ⁿ`, `m≤ⁿ+`, `sub≤bin`, `un≤'`) and the Δ₀ lift helpers
   (`Δ₀-prAtL`/`Δ₀-appAt`/`Δ₀-consAtL`, the Condensation pattern).

## 3. What is parked, and the continuation

`runs/unfinished-4c-5-6.agda.txt` holds the written-but-unverified
parts (a snapshot;  it does not typecheck and is not claimed to):

1. `envSet-graph` + `consAt-route`:  every environment-set member is
   the graph of a carrier vector (via `envSet-out`), and a consAtL
   fact pins the extender's graph into `envSet A (suc n)` (via the
   Bridge's `consAtL-out`/`graph-envSet`).
2. `Bd` and `bdΔ₀`:  the bounded description per constructor.  The six
   propositional clauses ARE `cond` itself (their adequacy is the
   identity and their Δ₀ certificates are one δ-combinator each);  the
   atom and quantifier clauses bound the unbounded witnesses.
3. The adequacy per constructor, both directions, on the landed
   readers (`cond∈/≐/∃/∀/∃∈/∀∈-in/out`) plus the cons-graph route.
4. The climb `R` (one clause per constructor, stage
   `sucIter (nsuc (d + sizeψ ψ)) σ₀`, room lifted by `≤ⁿ`) and the
   merge + assembly (Section 6 of the design):  Lset-out + ord-tri +
   the 735 close produce the stage facts `WithStage` consumes;
   closedω absorbs the whole iterate into γ in two `Lset-mono` links.

Continuation plan, in order:  (a) move the `NeedsAt`/`bddBd` block
after `Bd`/`bdΔ₀` (definition order);  (b) re-verify the four
quantifier adequacies against the reader shapes (the ∃̇∈ satisfaction
is a truncated Σ with an Ω-pair -- measured, not guessed);  (c) write
the merge (Lset-out → ord-tri → the three cases → `WithStage.final`)
and `Sat-at-asConst`;  (d) the known defect classes are all recorded in
this dispatch's runs (`p-1` to `p-104`).

## 4. What would close it

One more coder dispatch on the same brief:  the design is complete, the
parked text is the continuation, and the remaining work is assembly
(estimated 150-250 lines of glue plus defect rounds).  Do not re-brief
the design;  do not re-fund the placement core.

## 5. What this dispatch measured that the next brief should know

1. The W3 estimate (250-450 lines) undersold the route:  the green
   prefix alone is 555 lines and the full climb lands near 1,100-1,300.
   The overage is `cond`'s own unbounded witnesses forcing a bounded
   description plus twelve clauses of certificate plumbing.
2. `bddCons` is private in `L.Coding.Model`;  the exported workaround
   for the cons-condition's Δ₀ certificate is the conversion trick
   (`Δ₀-liftFo _ (Δ₀-consAt …)`), exactly as `src/L/Condensation.lagda.md`
   does it.
3. The ∃̇∈-satisfaction shape (truncated Σ, Ω-pair body) and the
   where-scope rule (Agda 2.8.0 where-declarations are sequential, not
   mutual) are the two traps that cost the most rounds this dispatch.
