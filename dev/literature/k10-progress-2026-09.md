# K10 continuation checkpoint

K10 remains incomplete. The new continuation builds on the checked
[K7 local repair](k7-local-preservation-repair-2026-09.md).

Checkpoint:
`/Users/alsg/Agentic/bedrock-proofs-archive/k10-progress-2026-09-13`.
See `PROGRESS-report.md` for the exact hypotheses and
`sh verify-k10-progress.sh` for the serial regression.

On 2026-09-13 the gate exited 0: all 120 positive modules passed, and the
missing-function negative control was rejected with the expected exit 42
and type error. Scoped prose and glossary gates passed as well.

New checked work:

- Positive-pair versus function-pair conversion, value uniqueness and the
  actual surjection-to-possible-value implication, including the exact name
  formula seam.
- Actual Cohen forcing of equality between translated checks implies ground
  equality, with the reflection input supplied by K9.
- A general larger-bound covering argument with an explicit square premise,
  and a separate concrete `𝒮ʟ` supplier applying `square-law-L` to discharge
  that premise. The L-specific result retains ordinary Foundation/Choice
  and explicit cardinal/ordinal and smaller-ordinal bounds. It does not use
  `MemberImage`, and is not a general-ground cardinal multiplication proof.
- Top-value proofs for the exact singleton and unordered-pair formulas,
  under the K4 evaluator laws. The concrete atomic-graph/compiler supplier
  and ordered-pair/graph formula proofs remain separate obligations.
- Actual K9 generic-extension injection, checked omega and checked injection
  are assembled into successor identification and shared non-CH/negated
  GCH omega-instance satisfaction. The two preserved cardinals and extension
  profile capabilities remain explicit inputs, not claimed suppliers.

The all-condition forcing consequence needed by the antichain construction
is still open. Truth in the supplied generic only handles conditions in that
generic and does not fill this gap. General omega-two covering, actual
preservation assembly and Boolean non-CH top values remain open as well.

The checkpoint includes an unchanged production-source snapshot for checking
the specific L dependencies without writing to original production caches.
It changes no production proof or landmark, and performs no commit or push.
