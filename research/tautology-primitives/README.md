# Tautology Primitives and Verified State Cycles

## Purpose

This research module keeps three questions distinct:

1. **Tautology generation** — can a Boolean basis express constant TRUE?
2. **Tautology recognition** — is an arbitrary formula true under every valuation?
3. **Functional completeness** — can a basis express every Boolean function?

Cook's 1971 theorem-proving paper concerns recognition and polynomial reducibility. Post's functional-completeness theorem is stronger than the constant-TRUE generation question studied here.

## Current exact results

Truth vectors use ordered inputs `00, 01, 10, 11`. Exactly six of the sixteen binary Boolean operators generate a tautology using variables as leaves and no primitive nullary constants:

| Operator | Truth vector |
| --- | --- |
| NOR | `1000` |
| XNOR | `1001` |
| `y -> x` | `1011` |
| `x -> y` | `1101` |
| NAND | `1110` |
| binary constant TRUE | `1111` |

If a one-connective formula `T(x1,...,xn)` is a tautology, identifying all variables yields the unary tautology `T(x,...,x)`. The existence question therefore reduces to the unary Boolean closure `{0, 1, x, NOT x}`.

For arbitrary sets of **binary** Boolean operators, exact enumeration of all singleton and pair bases gives:

```text
constant TRUE is generable
iff
not(all selected operators preserve 0)
and
not(all selected operators are self-dual)
```

All `16 + C(16,2) = 136` singleton/pair bases were checked: 93 generate TRUE and 43 do not. Every larger binary basis escaping both obstructions contains an escaping singleton or pair.

This is not functional completeness. NAND and NOR are the two binary singleton bases that generate all sixteen two-variable Boolean functions.

## Minimum circuit costs (2026-10-27 extension)

The completed classification now has a separate [minimum-cost proof and model](CIRCUIT_COSTS.md).
With unit-cost binary gates, no primitive constants, and free wires/fanout:

| Basis | Formula gate occurrences | Shared DAG gates | Minimum depth |
| --- | ---: | ---: | ---: |
| NOR | 5 | 3 | 3 |
| NAND | 2 | 2 | 2 |
| XNOR, either implication, binary TRUE | 1 | 1 | 1 |

The NOR witness computes NOT x, then FALSE, then NOR(FALSE,FALSE), reusing
the same FALSE node. All 136 singleton/pair bases have exact cost witnesses
or an obstruction. An independent raw enumerator checks 195,320 trees and
37,512 straight-line programs; a separate evaluator replays all 279 TRUE
witnesses. NOR combined with FALSE or either difference operation has
formula size 3 versus shared size 2. The proof also derives ordered minimum-cost
rules for arbitrary sets of binary operations; its executable crosscheck is
explicitly limited to the 136 singleton/pair bases.

`code/circuit_costs.py` provides immutable source-aware local plans, preserves
input identities and revisions, and measures each cost separately. This is a
validated Python interface, with external runtime admission still tracked by
FIG-23. It establishes no P-versus-NP or neural-learning replacement claim.

Reproduce the complete module and new evidence from this folder:

```bash
python -m unittest discover -s tests -v
python code/verify_circuit_costs.py
```

New evidence: `evidence/minimum_costs.json`, `evidence/raw_minimum_costs.json`,
`evidence/circuit_cost_run.json`, and `evidence/circuit_cost_sources.json`.

## Lean kernel verification (2026-10-28)

The [formal Lean project](formal/README.md) proves the six singleton minima and
all 136 singleton/pair formula, shared-DAG and depth results. Universal lower
bounds cover arbitrary finite circuit sizes; source renaming preserves costs;
actual reachable-node counting excludes dead allocations. The 43 blocked bases
are excluded at every finite size.

Official Lean 4.35.0 compiled all five modules. All 794 public theorem axiom
audits passed, using only the standard `propext`, `Quot.sound` and
`Classical.choice` axioms. No proof holes, project-added axioms or
`native_decide` are used. Two deliberately false claims were rejected.
The broader arbitrary-subset Theorem 2 remains outside this Lean scope.

```bash
python code/verify_lean_proofs.py --lean /path/to/lean
```

The exact commands, source/toolchain hashes, compatibility adapter, axiom
dependencies and negative-control results are in `evidence/lean_verification.json`
and `evidence/lean_proofs.log`. [LEAN_REVIEW.md](LEAN_REVIEW.md) records the
independent statement/model review.

## Verified state-cycle implementation

`code/cook_cycle_factories.py` is the factory/builder refactor of the fixed DPLL cycle. The seven-bit word follows

```text
w -> w + 64 -> w + 65 -> w + 64 -> 2w + 1 (mod 128)
```

while all non-word coordinate bits are preserved. The CNF verifier constrains every lifecycle edge:

```text
S0 -> S1       word +64 mod 128
S1 -> S2       word +1 mod 128
S2 -> S1Return word -1 mod 128
S1Return + S2  -> S3 word mod 128
S0 non-word bits == S3 non-word bits
```

Reference anchor:

```text
State 3 Int53 : 8800120086943
Final word    : 31
SAT           : True
```

Deliberate mutation of `S1`, `S2`, the return state, the `S3` word, or an `S3` upper bit is rejected.

## Factory / builder architecture

- `FactoryRegistry` — assembly root.
- `CookCycleFactory` — fluent `explore`, `transport`, `return_by`, `origin`, `limits`, `build`, `run`.
- `TautologyFactory` — fluent Boolean-basis analyzer.
- `BooleanOperatorFactory` — immutable named truth-table factory.
- `BooleanRelationFactory` — exact relation-to-CNF construction.
- `TransitionClauseFactory` — lifecycle transition clauses.
- `LifecycleClauseFactory` — full pinned-state CNF.
- `DpllSatSolver` — solver behind a narrow interface.
- `DefaultCycleEvaluator` — execution separated from description construction.

`build()` returns an immutable detached `CyclePlan`; `run()` delegates to the evaluator. The architecture follows the verified Episteme factory pattern without claiming direct runtime interoperability.

## Evidence

- `evidence/cycle_self_test.json`
- `evidence/tautology_singletons.json`
- `evidence/binary_basis_classification.json`
- `tests/test_cook_cycle_factories.py`

Run from this folder:

```bash
python code/cook_cycle_factories.py
python -m unittest tests/test_cook_cycle_factories.py -v
```

## Claim boundaries

```text
TAUTOLOGY_GENERATION != TAUTOLOGY_RECOGNITION
GENERATES_TRUE != FUNCTIONALLY_COMPLETE
SOFTWARE_VERIFICATION != MATHEMATICAL_PROOF
FINITE_ENUMERATION != P_VS_NP_RESULT
COOK_REDUCTION != THIS_LOCAL_CYCLE_VERIFIER
EPISTEME_ARCHITECTURE_TRANSFER != EPISTEME_RUNTIME_INTEGRATION
```
