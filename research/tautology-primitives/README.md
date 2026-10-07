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
