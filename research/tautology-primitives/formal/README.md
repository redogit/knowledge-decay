# Lean kernel proofs for FIG-22

Status: **kernel checked with Lean 4.35.0** on 2026-10-28. This is a new
verification checkpoint for the October 27 hand proofs and Python evidence.

## What is proved

| Result | Lean statement / module | Scope |
| --- | --- | --- |
| Six exact formula sizes and depths | `Tree.singleton_minima`, `Checked.singleton_exact` | Every nonempty finite input dimension; arbitrary finite trees |
| Six exact shared-gate minima | `DAG.singleton_minimum` | Arbitrary acyclic circuits, arbitrary outputs and dead allocated gates |
| Complete 136-base population | `Basis.population_complete` | All 16 singletons and 120 distinct unordered pairs of binary operations |
| Formula, reachable-DAG and formula-depth minima for every generating basis | `Basis.every_generating_row_all_costs` | Every nonempty variable type; no size or depth search cutoff |
| Depth minima directly over DAGs | `Checked.every_generating_row_dag_depth` | Every generating row, arbitrary finite DAGs |
| Non-generation for all 43 blocked bases | `Basis.every_blocked_row_over`, `Basis.every_blocked_row_dag` | Every finite allowed formula or DAG |
| Histogram and sharing savings | `Basis.population_111` through `population_533`, `population_sharing_gain` | 58/24/3/4/4 generating bases; 7 have tree/shared savings |
| Representation agreement | `Checked.tree_dag_semantics`, `Checked.tree_basis_semantics` | Ordered truth tables and the singleton/full-basis interfaces |
| Unary substitution and identity | `Tree.identify_*`, `DAG.Circuit.diagonal_preserves_*` | Gate occurrences, ordered references, reachability and tautology preserved |

Names above are within namespace `FIG22`. Gate costs are unit weights;
variable leaves, wires, fanout and tied pins are free. Binary constants remain
charged applications. Formula size counts occurrences; shared size counts
**distinct output-ancestor gates**. Depth is the longest gate path. Inputs are
symbolic identities, not values that may silently be merged.

The exact singleton results remain NOR (5,3,3), NAND (2,2,2), and XNOR,
either implication and binary TRUE (1,1,1), in formula/shared/depth order.

## Why these proofs exceed bounded testing

The generic formula lower bound follows by structural induction from a finite
potential inequality at each gate. The depth proof uses the analogous max
inequality. A finite closure certificate excludes every finite term for a
blocked basis. These arguments quantify over arbitrary tree sizes.

For DAGs, ordered references point strictly backward. Unfolding preserves
semantics and depth. The formal theorem `Dag.depth_le_reachable` bounds that
depth by the number of distinct output ancestors, excluding unused allocations.
For each of the 93 generating bases, a concrete indexed DAG attains the bound.
A separate bridge proves the exact depth optimum directly over DAGs.

Python proposes the certificate data and witnesses. It is not a trusted proof
oracle: Lean checks each certificate and witness, the generic implications,
and the equality between the recorded population and all singleton/pair bases.
All finite decisions use proof-producing `decide`, with kernel reduction.

## Reproduce

Install the official pinned toolchain in `lean-toolchain`. Only the bundled
Lean/Std libraries are required; no Mathlib or other package download is needed.
From the parent `research/tautology-primitives` folder:

```bash
python code/verify_lean_proofs.py --lean /path/to/lean
python -m unittest discover -s tests -v
```

The verifier builds all five modules into a fresh temporary directory, imports
only those fresh proof objects, prints the axiom dependencies of every public
project theorem, checks input hashes before and after, and saves the actual log
and manifest. It also requires Lean to reject two deliberately false controls:
NOR formula cost four, and the claim that NOR(x,x) is a tautology.

`lake build` from this directory is an ordinary project build. The Python
verifier additionally performs the complete axiom audit and negative controls.
The generator can reproduce the two certificate modules:

```bash
python formal/generate_basis_certificates.py
```

Run that command from the parent module folder. Generation is not proof
verification; rerun the Lean verifier after any change.

## Axioms and runtime provenance

No `sorry`, `admit`, project-added `axiom`, `unsafe`, or `native_decide` is
permitted in the proof sources. The audited theorem dependency union is Lean's
standard **propext, Quot.sound, Classical.choice**. This is not an axiom-free
claim; no extra mathematical assumption is introduced by this project.

The official Linux release archive was checked against its published SHA-256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The Lean release commit is `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The run manifest also hashes the actual compiler executable and kernel shared
library.

On the execution host, getpid() and /proc/self use different PID views. Lean's
own-executable lookup consequently initially failed. The bundled
`runtime/proc_self_path.c` maps only the caller's `/proc/<getpid()>/exe` readlink
to `/proc/self/exe`; it changes no proof, kernel, evaluator, or other filesystem
operation. The verifier detects this exact mismatch, builds the adapter only
when necessary, and records its source and shared-library hashes. Ordinary
hosts need no adapter. The official Lean compiler/kernel remains unchanged.

## Evidence and boundary

- `../evidence/lean_proofs.log`: actual compilation, axiom-audit and negative-control output.
- `../evidence/lean_verification.json`: toolchain, hashes, commands and exact proof scope.
- `../evidence/lean_axiom_audit.lean`: generated, replayable audit source.
- `../LEAN_REVIEW.md`: independent statement/model review and exact reviewed files.

The separate analytical Theorem 2 for arbitrary subsets of the sixteen
operations is **not** claimed Lean-formalized by this checkpoint. Its hand
proof remains distinct from the complete singleton/pair kernel proof. Weighted
hardware costs, higher-arity bases, multi-output optimization, and external
architecture/runtime admission remain separate obligations.
