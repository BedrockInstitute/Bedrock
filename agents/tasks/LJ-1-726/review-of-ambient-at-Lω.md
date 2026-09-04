# review-of-ambient-at-Lω (LJ-1.726)

## The verdict line

NO-GO. The parked target `ambient-at-Lω : (δ : CS.S) (oδ : IsOrd (fst δ)) →
⟨ (Lset (fst δ) ∷ fst δ ∷ Lset ω ∷ []) P652.⊨ₚ P667.matrix₃ ⟩` is FALSE at
`δ := ω`. The graph half of `matrix₃` bounds the approximation table by the
witness slot; its domB conjunct forces the table to answer exactly the members
of the parameter that lie in the witness; at `(Lset ω, ω, Lset ω)` the numerals
lie in both, so the table would carry an entry with first component `# k` for
every `k`; but the table sits in `Lset ω`, so its rank sits in `ω`, so its rank
is a numeral `# j`, and the entry at `# j` puts `# j` inside `# j`. One
counterexample kills the Π. This is a D-10 catch against the brief's premise 3:
716's corrected target was recorded as "a witness slot that carries the
numerals", but carrying the numerals is not enough; the witness must also
carry the table, and no fixed stage does for general δ.

## What is machine-checked green

1. `#∈Lω` (runs/TablePerp.agda:67-70): every numeral sits in `Lset ω`, by
   `ord∈Lset-suc` (src/L/Ordinal/Stages.lagda.md:434), `#∈ω`
   (src/L/Ordinal.lagda.md:248) and `Lset-mono`.
2. `table-⊥` (runs/TablePerp.agda:72-97): a table `c` in `Lset ω` answering every
   numeral is impossible. The chain: `rank-Lset` (src/L/Ordinal/
   Stages.lagda.md:190) puts `rank c` in `ω`; the ω-members decode (the
   truncated-numeral pattern behind `ω-mem-ord`, src/L/Ordinal.lagda.md:258)
   gives `rank c = # j`; the entry at `# j` gives `pr (# j) y ∈ˢ c`; then
   `rank-mono` (src/L/Rank.lagda.md:117) twice with the pair components
   (`self∈singl`/`inl∈pair`, the library packages at
   Cubical.HITs.CumulativeHierarchy.Constructions:135-148, since the tree's
   own spellings are private in src/V/Coding.lagda.md:137-150), transitivity
   of `rank (pr (# j) y)` (`rank-ord`), and `rank-fix`
   (src/L/Rank.lagda.md:191) put `# j` inside `rank c = # j`; `∈-irrefl`
   closes. Green, ~0 wasted structure: the whole kill is delivered lemmas.
3. `ambient-at-Lω-refutes` (Probe726.agda:151-155): the refutation composed
   against the obligation at `δ := (ω , its constructibility)`.

## What is parked, and why

`matrix₃-table` (Probe726.agda:129-140, the hole): the extraction of the table
and its entry function from the matrix satisfaction. The route was written and
driven to within one application: the erased reading transfers to the
`SemV.At CS.S fst` landing reading (three-sat, via `Count.erase-inv`,
src/FOL/Count.lagda.md:617, and `embed-⊨`,
src/FOL/Manipulation/Relabelling.lagda.md:188), the twelve bounded existentials
peel one step at a time (peel3 to peel14, each green; exp3 measured the shape
in runs/exp-12.out), and the domB conjunct at the c-level environment yields
the entry type. The last application left the satisfaction coercion unreduced
at the application check (runs/p-45.out), and every restructuring of the deep
peel then crashed Agda 2.8.0 itself: the crash runs p-50 to p-53, p-58,
p-60 to p-61, p-63 to p-67, p-70, p-74 to p-76, p-80, p-83 all abort with
`time: command terminated abnormally`, no Agda message. The working
configuration required taking the assembly back out of the deep mutual block
and parking it. The heap-wall clause was honored: every restructuring was
tested under the same cap before the step was parked, and every test died.

## What the next brief needs

1. The corrected target, recorded beside the original (D-10): at a FIXED
   witness stage the obligation dies for every parameter whose numeral
   content outranks that stage. The readings that survive keep the witness
   growing with the parameter (z := Lset (suc^k δ) for small fixed k, the
   table's rank being δ + finite), or drop the table bound entirely. Which of
   these feeds `LsetGrounded` is the mathematician's call.
2. The extraction's last step should go through the delivered reading-lemmas
   (Sequence's `ApproxAt-value`, src/L/Coding/Sequence.lagda.md:298, and
   `StepAt-back`, src/L/Coding/Sequence.lagda.md:221, at variable slots)
   instead of raw satisfaction peeling, or price a satisfactions-level
   `domAt-out` analogue. The raw route is measured: it walls one application
   short and crashes the compiler on restructure.
3. The C-42 sweep count for the shape "graph table bounded by a fixed-stage
   witness": exactly ONE site, this obligation. The neighbours do not carry
   it: Probe520's `levelFo` binds its thirteen existentials unbounded
   (agents/tasks/LJ-1-520/Probe520.agda:171-185), and the delivered
   `GraphB` consumers bind by a hull-relative K where the table exists by
   construction (src/L/Condensation.lagda.md:2486-2506).

## Question 1: does the verdict LINE match its own BODY?

YES. The LINE says NO-GO, target false at δ := ω. The BODY claims the
refutation chain green up to the final extraction application, and says
plainly that the extraction's last step is parked with the compiler-crash
evidence. Nothing in the LINE claims the obligation is unrefuted; the hole at
`ambient-at-Lω` (Probe726.agda:157-163) is designed and documented.

## Question 2: is every load-bearing claim backed by a file:line that resolves today?

The load-bearing chain: `domB`'s reading (src/L/Condensation.lagda.md:1749-1761,
with `appAt` at src/L/Coding/Model.lagda.md:160-162 and the adequacy at :164),
the rank chain (src/L/Rank.lagda.md:117, :191; src/L/Ordinal/Stages.lagda.md:190),
the ω-members decode (src/L/Ordinal.lagda.md:258-263), the pair components
(src/V/Coding.lagda.md:175-179 defines `pr`; the membership lemmas are the
library's SingletonPackage/pairing-ax, Cubical.HITs.CumulativeHierarchy/
Constructions.agda:133-160), and `ω-ord`/`#∈ω` (src/L/Ordinal.lagda.md:248-263).
The parked step is parked with its exact failing check quoted in the file's
hole note and in runs/p-45.out.

## Prices measured

The full-file check at the wide caliber (-A64m -I0 -M2g) ran 128-1018 s
depending on pane contention, peak resident 1.55-1.63 GB, under the cap. The
final checks with the extraction parked and the kill green:
runs/p-final3-tableperp.out (green, 0.95 s, peak 282 MB) and
runs/p-final3-probe.out (rc 42, 2.94 s, peak 622 MB, the two designed
metas only). The compiler crashes on the deep-peel
restructures reproduce deterministically on this pane (the crash-run list
above).
