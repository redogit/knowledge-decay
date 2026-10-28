# Full Theorem 2 independent review — 2026-10-28

Primary verdict: **proved as written within the explicit Boolean circuit model**.
No incorrect condition, missing preceding failure, weakened quantifier or invalid
cost transfer was found. No mathematical gap remains in the reviewed scope.

The reviewer was a fresh, read-only same-model subagent, separate from the proof
authors. This is distinct from external human corroboration. The review treated
kernel acceptance and correctness of the formal statement as separate obligations.

## Quantified claim

For any chosen source x:α and every list or predicate-defined subset of total
binary Boolean functions, exactly the first applicable one of seven ordered
cases yields exact formula occurrence size, distinct reachable DAG size, formula
depth and DAG depth, or impossibility for every permitted finite object.
There is no size, depth, allocation or basis-cardinality cutoff.

## Dependency obligations

| Obligation | Result and mechanism |
| --- | --- |
| Four-state unary semantics | Passed: local inequalities and closed sets lift by induction |
| Ordered first-match premises | Passed: classify_iff, branch_complete, all preceding failures included |
| Operator exhaustiveness | Passed: all sixteen truth tables and inverse bijection with all binary functions |
| Lower bounds | Passed: maximal allowed bases, restricted certificates, diagonal formula lifting |
| DAG size | Passed: unfolding preserves depth; depth≤distinct output ancestors, including dead allocations |
| Upper bounds | Passed: checked singleton/pair witnesses transferred solely by operation membership |
| Empty/full and reordered/repeated bases | Passed: branch examples and extensional membership congruence |
| Mathematical subsets | Passed: normalization membership equivalence; no supplied decision procedure |
| Raw formulas/DAGs | Passed: inverse encodings preserve all four costs, semantics, admissibility and source topology |
| Direct raw predicate theorem | Passed: conclusion quantifies about raw predicate-admissible objects |
| Corollaries | Passed: uniqueness, all profiles, no minimum four, G=D and sharp bounds |

The finite local certificates and maximal-basis restrictions were reviewed for
all seven cases. The two blocked cases close {FALSE,x} and {x,NOT x}. The
five reachable cases have the exact profiles (1,1,1), (2,2,2), (3,2,2),
(3,3,3), (5,3,3), including separate attaining witnesses and universal bounds.

## Execution and independence

The reviewer separately compiled all seven new source modules and checked
axiom dependencies of the main, ordered, subset, raw, predicate and consequence
theorems. Additional empty/full and reordered/repeated examples passed.
Those review runs used existing dependency objects; the parent then supplied
the independent freshness check: all twelve modules built in a fresh temporary
directory, all 926 public theorem axiom audits passed, and all four deliberately
false controls were rejected specifically as false propositions.

Only standard Lean propext, Quot.sound and Classical.choice occur. No sorry,
admit, project-added axioms, unsafe declarations or native_decide were found.
The independent Python all-basis enumeration is corroboration and is not used
as a premise of the universal proof.

## Exact reviewed revisions

Predecessor remote checkpoint: 154d5cb53ad36d8598f6d8239356d2e9d6356a94.

| File | SHA-256 |
| --- | --- |
| `formal/BooleanSupport.lean` | `0de170dce6f26f32143bf1da1d7e16c403a4e1a38ceb3397385cce94bd358533` |
| `formal/BooleanDagSupport.lean` | `e34129eaf3068e963597c15f3b416c5bd6e4d4ae9dbbeddc3ea8330c41fec8cb` |
| `formal/TheoremTwoUpper.lean` | `cc8617056f2362e369caea68009bac9f27ced15570ff5272c687c369416042ad` |
| `formal/TheoremTwoLower.lean` | `46f09301b90ed655d6960d8d75e6ade369d3136af9bdee705a152dd26ccd7f5b` |
| `formal/TheoremTwo.lean` | `b363ddca2e20895aeb08118a424f9a319d886bc66138b3a433afad8c412c01a2` |
| `formal/TheoremTwoConsequences.lean` | `8aebfbb417b68e0b77f125534a31f1d2d8ecf9cea8fada004d011354cb4742f7` |
| `formal/TheoremTwoRaw.lean` | `2de64f7dbd347abd5dc4fd7c028b018ff2c59859640556b6fa6171c692fc7856` |

The fresh-build manifest additionally records every executed input and output
hash. This review supersedes the earlier hand-only Theorem 2 remainder; the
older five-module review remains preserved as a historical checkpoint.
