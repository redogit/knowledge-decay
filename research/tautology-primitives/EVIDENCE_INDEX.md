# Evidence index

This index separates mathematical derivation, finite computation, implementation tests, literature, project-management provenance, and architecture-transfer evidence.

## Internal mathematical derivation

1. **Single-connective reduction.** If a `g`-only formula `T(x1,...,xn)` is a tautology, variable identification gives the unary tautology `T(x,...,x)`. The unary term closure lies in `{0,1,x,NOT x}`.
2. **Six singleton bases.** Exact case analysis yields NOR, XNOR, reverse implication, implication, NAND, and binary constant TRUE.
3. **Binary-basis obstruction theorem.** A binary basis cannot generate TRUE when every member is 0-preserving or when every member is self-dual. Exhaustive singleton/pair closure establishes sufficiency for the complete 16-operation binary universe; every larger escaping basis contains an escaping singleton or pair.

See [CLAIM_BOUNDARIES.md](CLAIM_BOUNDARIES.md).

## Exact finite computation

- [tautology_singletons.json](evidence/tautology_singletons.json): all 16 binary Boolean operators.
- [binary_basis_classification.json](evidence/binary_basis_classification.json): all 136 singleton/pair bases; 93 TRUE-generating, 43 non-generating; every two-obstruction prediction matches.
- [cycle_self_test.json](evidence/cycle_self_test.json): 55 carrier round trips, 46 non-word bit positions, 128 word inputs, five deliberate lifecycle corruptions, and anchor SAT trace.

These finite records support only the enumerated domains.

## Independent computational cross-checks

Wolfram was used as an independent exact-computation surface. Recorded outcomes:
- all 16 two-input Boolean truth functions were represented;
- the six singleton TRUE-generators matched the internal enumeration;
- NAND and NOR alone generated all 16 two-variable Boolean functions;
- the complete singleton/pair sweep had 136 bases, 93 generating TRUE and 43 not.

The repository evidence is regenerated independently in Python and does not depend on Wolfram execution.

## Literature checks

- Cook 1971: tautology recognition and polynomial reducibility.
- Post/Pelletier-Martin: functional completeness and the five-class obstruction criterion.
- Open Logic Project: valuation, satisfaction, satisfiability, tautology and entailment.
- Boolean-completeness and normal-form references listed in [SOURCES.md](SOURCES.md).
- Implication-only Boolean-tree literature explicitly treats tautologies as formulas computing constant TRUE.

Source URLs are retained in [SOURCES.md](SOURCES.md); copyrighted papers are referenced rather than republished.

## Episteme architecture evidence

Architecture transfer was based on preserved Episteme reports and verification records identifying:
- `81-factory-kernel.js`
- numeric/text/bindings family evaluators;
- thin fluent adapters in `90-builders.js`;
- assembly in `95-assembly.js`;
- detached `build()` descriptions, evaluator-delegated `run()`, versioned definitions, explicit budgets, traces, origins, and incomplete/failure semantics.

The underlying private/library evidence is not copied into this public repository. [EPISTEME_INTEGRATION.md](EPISTEME_INTEGRATION.md) records the transferable contract and the unresolved direct-runtime bridge. Linear FIG-23 tracks the bridge.

## Linear and Figma provenance

Service snapshots are under `provenance/integrations/`:
- three Linear research projects;
- 23 Linear issues with accessible comments;
- zero Linear documents at export;
- one concretely recovered FigJam board with XML, image snapshot and source metadata;
- public-safe Figma account/plan metadata, 35 connector-enumerable first-party shaders and zero user generative plugins.

The Figma connector does not provide an account-wide design-file listing. The exported Figma set is therefore explicitly incomplete at the account level.

## Verification run

The self-contained regression suite was run after repository packaging-path repair:

```text
python -m unittest tests/test_cook_cycle_factories.py -v
3 tests passed
0 failures
runtime: 0.132 s
```

The full factory self-test produced the stored cycle evidence. The refactored implementation SHA-256 is:

```text
7492473b20d5b78eb5c195f4f2441fc0685159e4bc8d815e0f911a2fa04992d9
```

A remote branch read was compared against the exact generated attachment and matched exactly across all 793 lines.

## Claim ceilings

```text
SOURCE_REFERENCE != SOURCE_REPUBLICATION
SERVICE_PROVENANCE != MATHEMATICAL_EVIDENCE
INDEPENDENT_COMPUTATION != PROOF
SOFTWARE_VERIFICATION != MATHEMATICAL_PROOF
ARCHITECTURE_TRANSFER != RUNTIME_INTEGRATION
FINITE_BOOLEAN_CLASSIFICATION != P_VS_NP_RESULT
```
