# Theorem 2 full Lean extension

Input: existing hand statement in CIRCUIT_COSTS.md and Lean basis/circuit models
at remote checkpoint154d5cb53ad36d8598f6d8239356d2e9d6356a94.

Obligation: classify every subset of the16 total binary Boolean operations,
including empty and full bases, by exact formula gate occurrences, distinct
reachable DAG gates, formula depth and DAG depth for TRUE generation. Ordered
first-match rules and their supporting facts must be kernel proved. Arbitrary
nonempty symbolic variable collections and every finite circuit size are covered.

1. Prove binary-function/truth-table encoding bijection, diagonal partition,
   0-preserving/self-dual characterizations, and raw operator representation
   adapters preserving semantics, formula/DAG costs and depth.
2. Formalize all seven ordered cases for arbitrary bases; kernel-check small
   maximal-basis potential/closure certificates for universal lower bounds;
   transfer attained witnesses by basis monotonicity for upper bounds.
3. Prove the exact classification and supporting corollaries: impossible cases,
   no formula optimum four, shared optimum equals depth, finite upper bounds,
   and invariance under reordered or repeated basis entries.
4. Independently crosscheck all65536 distinct bases with exact semantic algorithms;
   the executable check is corroboration, never a trusted Lean premise.
5. Add all modules to the fresh-build/axiom-audit verifier, reject deliberately
   wrong Theorem2 branch claims, review quantified statements and raw adapters,
   preserve hashes/logs/previous revisions, and update PR6/FIG-22 after success.

No proof holes, custom axioms, unsafe declarations, or native_decide. Standard
Lean foundational axioms remain explicit. Stop after all claimed factors above
are checked or an exact unresolved gap is honestly recorded; do not promote a
hand-only claim to kernel status. Existing physical/runtime hypotheses are not
silently introduced into the pure Boolean theorem.
