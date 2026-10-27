# FIG-22 minimum-cost extension plan

Scope: extend the completed binary TRUE-generation classification at source commit
`67053880df1ab44833d55e4cf685b8d8ead1d84c`; preserve all predecessor evidence.
The user explicitly requests execution, tests, proofs, and an issue extension.

## Contract

Two-valued, ordered binary operations; variable leaves only; repeated variables
allowed. Binary constant-valued operations cost one gate, never zero.
Formula cost counts gate occurrences; DAG cost counts reachable gate nodes;
depth counts longest gate path from inputs at depth zero. Wires, fanout and
tied pins are free. No algebraic simplification is silently charged as reuse.
Source identifiers and revisions remain explicit; unary identification is a
mathematical reduction, not permission to merge distinct runtime inputs.

## Tasks and checks

1. Independently derive six singleton minima and cost-preserving unary reduction.
   Prove lower bounds, with NOR FALSE-generation as a separate lemma.
2. Add `code/circuit_costs.py` and `tests/test_circuit_costs.py`: deterministic
   synthesis, exact tree/depth closure, DAG state search, immutable source-aware
   plans, exhaustive truth-vector witness evaluation. Tests precede implementation.
3. Add independent raw syntactic enumeration without importing production cost
   algorithms: all ordered unary trees up to five gates, and all topologically
   ordered straight-line programs up to three gates; all 136 singleton/pair bases.
   Record exact domains, counts, source hashes, commands, and actual results.
4. Add `CIRCUIT_COSTS.md`: definitions, proofs, explicit witnesses, pair results,
   validated local architecture interface and remaining questions. Update README
   and evidence index additively, preserving generation/recognition/completeness.
5. Fresh-context review; run full module tests and predecessor self-test; preserve
   exact outputs/provenance; open a reviewable GitHub PR and append FIG-22 checkpoint.

Budget: finite populations above; no random sampling, external experiments,
runtime deployment, merge, history rewrite, or unrelated research. On disagreement,
preserve both outputs and resolve it before any stronger status. Stop after verified
finite results and clearly defined generalization questions. Recovery is the unchanged
source commit plus additive files and a separate branch.
