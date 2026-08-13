# [L3.32-T44] W3 chapter B: the order formula and its adequacy
tier: codex (default)

GOAL: `[T42]` delivered W3's chapter A (the family and its table) and booked
the per-level order-as-an-element residue to chapter B, in the exact shape the
coding chapters recorded. `[T40]`'s hull then found BOTH of its own residues
gated on the same object: the adequate internal order formula at the carrier.
Build chapter B, and unblock both.

CWD: /Users/alsg/Agentic/Bedrock
SCOPE (write): ONE new master under `src/L/` plus `_build/l3.32-t44-report.md`.
Never `src/Everything.lagda.md`. **Do not touch `src/L/Rud/Bridge.lagda.md`,
`src/L/Rud/SatTable.lagda.md`, `src/L/Ordinal/`, or `src/L/OrderFamily.lagda.md`
(siblings own those or they are settled).**
SCOPE (read, in order): `_build/l3.32-t42-report.md` (**chapter A and the
residue it booked here, with its exact shape**); `src/L/OrderFamily.lagda.md`
(the interface you must satisfy: `OrderAtAt` and what it demands);
`_build/l3.32-t22-report.md` (**the sealing prescription, binding**, and note
T42's finding that a good interface absorbs the least-witness contact);
`_build/l3.32-t40-report.md` section 3 (the hull's two residues and their exact
types, since your chapter is what discharges them); `_build/l3.32-t14-report.md`
(the chapter split); `src/L/Rud/Order.lagda.md`, `src/L/PairAtoms.lagda.md`,
`src/L/LevelFormula.lagda.md` (the decode discipline), `src/L/Definability.lagda.md`;
`dev/LESSONS.md` (binding; R-35's storage-position rule and R-38's appended
rule both fired in chapter A).

CONTENT: the order formula, its two-way adequacy, and the carve placing the
order element in the level, so `OrderAtAt` is instantiated rather than assumed.
D-10 first: T19 found the recorded targets not establishable as stated at the
concrete level, so state each target, check its truth at the intended
generality, and record any correction beside the original.

CONSTRAINTS: `GHCRTS=-M8g agda <file>`, ONE Agda process at a time (three
siblings run). STOP-LINE 400 non-blank in-fence lines; if the carve cannot
close inside it, STOP and report what is proved and what remains. No postulate,
no hole, no TERMINATING. Trilingual prose (en and zh), no em dash. Both linters
clean. **New terms NAMED in the report, never added to the glossary yourself.**
Do NOT run `make check`. No git. Never touch `.claude/`.

RETURN (`_build/l3.32-t44-report.md`; final message = the summary): the exports
and types; the measured size; **whether the hull's two residues are now
dischargeable, which is the question this batch answers for W7**; the D-10
record; walls by LESSONS class; new terms; and the wiring note.
