# Minimum-cost review checkpoint

Date: 2026-10-27. Primary verdict: **proved as written** for Theorems 1 and 2
under the stated binary, unit-gate, variable-leaf model. No actionable findings.

The mathematical derivation was first delegated to an isolated agent given
the operations and model without the preliminary counts or implementation.
It independently obtained the singleton minima and ordered binary-basis rules.
A separate fresh-context reviewer then audited the final proof and code.
These are distinct same-model sessions, not external mathematical corroboration.
No Lean or other proof-kernel verification is claimed.

| Obligation | Result |
| --- | --- |
| Cost-preserving unary reduction and source-vertex caveat | Passed |
| NOR FALSE cost, TRUE tree lower bound, shared/depth lower bounds | Passed |
| NAND and four one-gate singleton bounds | Passed |
| Theorem 2 ordered cases for arbitrary binary bases | Passed by hand review |
| Complete raw-tree and ordered-program populations | Passed |
| Separate scalar replay of stored witnesses | Passed |
| Source/revision retention, serialization, topology and reachable accounting | Passed |
| External runtime interoperability | Out of scope; FIG-23 remains open |
| Proof-kernel verification and general recognition complexity | Not claimed |

Observed verification: 24/24 module tests passed; predecessor self-test passed,
including 136 bases, 93 generating, 43 blocked, and five mutation rejections.
The current computation manifest's input and output hashes matched the files.
Unchanged source artifacts matched their pinned upstream Git blob identities.

## Exact principal revisions audited

| File | SHA-256 |
| --- | --- |
| `CIRCUIT_COSTS.md` | `0d88fc8e37331918b389c78b8874f3c79af3be76e52a41aa86c933d81709be33` |
| `code/circuit_costs.py` | `baceb6161e34441813836fdc5f92f135adccd0289dbe5754bb65e008c66aab51` |
| `code/raw_circuit_enumerator.py` | `348e76b938f2bf1b47eca14e186a05a1c735c6e750f16242cdc0c982d14bcaba` |
| `code/verify_circuit_costs.py` | `74e76c9e67c516b472812123aee6de6ba1a2b65c823b11cd8276cf4dc7efa707` |

The reviewer also made an unpreserved, read-only all-binary-bases sanity check.
It is excluded from project executable evidence. The durable computational
claim remains the 136 singleton/pair population and its saved raw results.

Remaining obligations are grouped in CIRCUIT_COSTS.md: multiple outputs,
weighted physical costs, higher arity, nonconstant target dependence, and
versioned external architecture admission.
