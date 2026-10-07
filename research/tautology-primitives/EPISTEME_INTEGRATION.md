# Episteme integration assessment

## Decision

Integrate the **factory contract and execution architecture** now; defer direct JavaScript runtime coupling until the exact Episteme source package and serialized factory schema are available at the integration boundary. This avoids inventing an interoperability contract from reports alone.

## Verified Episteme pattern used here

Preserved Episteme evidence describes fluent numeric, text, bindings, and pattern factories with:
- caller-declared origin/provenance;
- a thin fluent construction adapter;
- `build()` producing a detached immutable description;
- `run()` delegating to a shared evaluator/kernel;
- versioned operation definitions;
- explicit finite resource limits;
- typed results with traces and derivations;
- explicit failure/incomplete termination;
- construction kept separate from execution and interface code.

Recorded implementation boundaries include `src/core/81-factory-kernel.js`, family evaluators, thin construction adapters in `src/core/90-builders.js`, and assembly in `src/core/95-assembly.js`.

## Mapping

| Episteme concept | Python implementation |
| --- | --- |
| `E.build.<family>(...)` | `Factories.cook_cycle(...)`, `Factories.tautology()` |
| fluent operations | `explore`, `transport`, `return_by`, `operator`, `operators`, `origin`, `limits` |
| detached build description | frozen `CyclePlan` and immutable operator tuples |
| shared evaluator | `DefaultCycleEvaluator` |
| versioned definitions | `OperationDefinition` |
| finite budget | `ExecutionLimits` |
| inspectable trace | `CycleResult.trace` |
| explicit incomplete result | `CycleResult.complete` + `error` |

## SOLID boundary

- **SRP:** representation, state derivation, CNF construction, SAT solving, tautology analysis are separated.
- **OCP:** alternate codecs and SAT solvers satisfy narrow protocols.
- **LSP:** evaluator consumes `SatSolver`, not a concrete DPLL type.
- **ISP:** `CoordinateCodec`, `SatSolver`, `CycleEvaluator` expose only required operations.
- **DIP:** `CookCycleFactory` delegates execution through an injected evaluator.

## Boundary

The Python `CyclePlan` is Episteme-inspired, not an authenticated Episteme serialized plan. Direct runtime integration requires the authoritative Episteme revision, the admitted factory-description schema, versioned Boolean/cycle families, and cross-language replay fixtures.

```text
ARCHITECTURE_INTEGRATED = true
DIRECT_EPISTEME_RUNTIME_BRIDGE = false
```

Linear issue FIG-23 tracks this runtime bridge obligation.
