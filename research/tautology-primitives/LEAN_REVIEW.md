# Lean formalization review — 2026-10-28

Historical review of the five-module checkpoint. The subsequent full
Theorem2 review is preserved separately in THEOREM_TWO_REVIEW.md.

Primary verdict: **proved as written** for the scoped six-singleton and
136-singleton/pair minimum-cost claims. No mathematical model or engineering
defect remained after review.

The fresh isolated reviewer checked gate occurrences versus immutable indexed
gates; ordered/tied pins; strictly backward references; actual distinct output
ancestors; arbitrary-variable lifting; zero-gate cases; charged binary constants;
and source identity. All136 population members, local certificate inequalities,
formula/depth witnesses, and all93 indexed DAG witnesses passed a separate
scalar check.

The reviewer requested an explicit API for depth directly over DAGs.
Interface.lean now provides ExactDagDepthOver, dag_depth_exact_of_formula_depth,
and every_generating_row_dag_depth. The reviewer inspected the bridge and
confirmed fidelity: the formula-depth lower bound applies to unfolding, while
the reachable witness and depth≤reachable give an attaining DAG.

Observed verification: official Lean4.35.0 accepted all five modules; all794
public theorem axiom audits passed; both deliberately false controls were
rejected. The dependency union is standard Lean propext, Quot.sound, and
Classical.choice. No added axioms, proof holes, unsafe declarations or
native_decide were used. An ordinary lake build also completed all7 jobs.

The runtime compatibility source was reviewed separately: only the exact
caller-own executable-path readlink is redirected to /proc/self/exe. The
official compiler/kernel is unchanged, and the release archive SHA matched
its published digest. The run manifest hashes the compiler and kernel library.

## Exact proof revisions

| File | SHA-256 |
| --- | --- |
| `formal/TreeProofs.lean` | `fec21ca03c8808b9b4afd860af4672d2c980c01ce115afef89b4d1bc6cd57649` |
| `formal/DagProofs.lean` | `676b33de5336aefc650f39e244825a37765ee5baf305eca707f7ae2a5c78917b` |
| `formal/BasisCertificates.lean` | `2ede79f0a0ef5305f1898c34b773bb4ecb1da311bb103e47b8017e2362ed6fc6` |
| `formal/BasisDag.lean` | `977f520b962a861d14485a52e9bd5fe31ff1d2b64f4ed90e6fb8a0844747e028` |
| `formal/Interface.lean` | `9aaee5bb36613d5c27d504c2bc2f87190a601ae0a14ce3c57663800ea2f3a0cd` |
| `formal/runtime/proc_self_path.c` | `f1cbab588c0e295ed4ed3618c6d286940c4ad490b03997b187e28bcfde306207` |
| `code/verify_lean_proofs.py` | `7107ce6114df379a8615370d0153dcebecc14679d176e4dfa7d9b908987d7bf4` |

Review provenance: a fresh same-model subagent, separate from the proof authors;
not external human corroboration. Kernel acceptance and statement/model fidelity
were checked separately. The review covered prior checkpoint
874992c61f38ecc5ba03d021ab1b8a650c3a98a3 plus the additive formal files.

At this historical five-module checkpoint, arbitrary-subset Theorem2 was
hand-proved and outside the checked136-base population. The subsequent full
Theorem2 proof and supporting-factor review are in THEOREM_TWO_REVIEW.md.
Hardware weights, higher arity, multi-output optimization and external runtime
admission are separate mathematical targets.
