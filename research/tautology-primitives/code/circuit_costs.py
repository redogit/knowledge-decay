"""Exact unary Boolean synthesis and a validated local circuit description.

The cost model has variable leaves only, ordered binary pins, free wires/fanout,
and one gate for every binary operation (including constant-valued operations).
Formula size counts occurrences after unfolding both pins; DAG size counts only
reachable gate nodes; depth counts gates on the longest input-to-output path.

This module reuses the predecessor's 00, 01, 10, 11 operator convention. Unary
semantic identification is confined to the synthesis algorithms. CircuitPlan
never merges declared source identities or revisions, even when their present
values, representations, or output functions coincide. Plans describe local
finite Boolean computations, not external runtime bindings or authority.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import product
from types import MappingProxyType
from typing import Any, Iterable, Mapping

from cook_cycle_factories import BinaryBooleanOperator, BooleanOperatorFactory

UnaryTruth = tuple[int, int]
UNARY_FUNCTIONS: tuple[UnaryTruth, ...] = ((0, 0), (0, 1), (1, 0), (1, 1))
PROJECTION: UnaryTruth = (0, 1)
MAX_SOURCES = 10


def _operator(value: BinaryBooleanOperator | str) -> BinaryBooleanOperator:
    """Detach even a predecessor operator constructed with a mutable truth list."""
    if isinstance(value, str):
        value = BooleanOperatorFactory.named(value)
    if not isinstance(value, BinaryBooleanOperator):
        raise ValueError("operator must be a BinaryBooleanOperator or a factory name")
    if not isinstance(value.name, str) or not value.name.strip():
        raise ValueError("operator name must be a nonempty string")
    truth = tuple(value.truth)
    if len(truth) != 4 or any(type(bit) is not int or bit not in (0, 1) for bit in truth):
        raise ValueError("binary truth vector must contain four integer 0/1 values")
    return BinaryBooleanOperator(value.name, truth)


def _reference(value: int) -> None:
    if type(value) is not int or value < 0:
        raise ValueError("references must be nonnegative integers (not booleans)")


def _fields(value: Any, expected: set[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or set(value) != expected:
        raise ValueError("serialized record has missing or unexpected fields")
    return value


@dataclass(frozen=True)
class InputSource:
    """One declared input identity at one explicit revision; both are strings."""

    identifier: str
    revision: str

    def __post_init__(self) -> None:
        if any(not isinstance(v, str) or not v.strip()
               for v in (self.identifier, self.revision)):
            raise ValueError("source identifier and revision must be nonempty strings")


@dataclass(frozen=True)
class CircuitGate:
    """A binary gate with ordered left/right refs into sources and earlier gates."""

    operator: BinaryBooleanOperator | str
    left: int
    right: int

    def __post_init__(self) -> None:
        object.__setattr__(self, "operator", _operator(self.operator))
        _reference(self.left)
        _reference(self.right)


@dataclass(frozen=True)
class CircuitPlan:
    """Immutable, detached, topologically ordered circuit with explicit output.

    If there are n sources, source refs are 0..n-1 and gate i has ref n+i.
    Every gate pin must refer to a strictly earlier node. This rejects forward
    references, self-loops, and cycles structurally. The output may select any
    declared node; unused sources and gates are retained. There must be 1..10
    declared sources, with distinct (identifier, revision) pairs. Revisions of
    the same identifier remain distinct inputs.
    """

    sources: tuple[InputSource, ...]
    gates: tuple[CircuitGate, ...]
    output: int

    def __post_init__(self) -> None:
        try:
            sources, gates = tuple(self.sources), tuple(self.gates)
        except TypeError as exc:
            raise ValueError("sources and gates must be finite sequences") from exc
        if not 1 <= len(sources) <= MAX_SOURCES:
            raise ValueError(f"a plan must declare 1..{MAX_SOURCES} sources")
        if any(not isinstance(source, InputSource) for source in sources):
            raise ValueError("every source must be an InputSource")
        if len(set(sources)) != len(sources):
            raise ValueError("duplicate source identity and revision")
        if any(not isinstance(gate, CircuitGate) for gate in gates):
            raise ValueError("every gate must be a CircuitGate")
        for index, gate in enumerate(gates, start=len(sources)):
            if gate.left >= index or gate.right >= index:
                raise ValueError("gate pins must reference sources or strictly earlier gates")
        _reference(self.output)
        if self.output >= len(sources) + len(gates):
            raise ValueError("output must reference a declared source or gate")
        object.__setattr__(self, "sources", sources)
        object.__setattr__(self, "gates", gates)

    def to_dict(self) -> dict[str, Any]:
        """JSON-compatible description retaining every source, gate and ordered pin."""
        return {
            "sources": [{"identifier": s.identifier, "revision": s.revision}
                        for s in self.sources],
            "gates": [
                {"operator": {"name": g.operator.name, "truth": list(g.operator.truth)},
                 "left": g.left, "right": g.right}
                for g in self.gates
            ],
            "output": self.output,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> CircuitPlan:
        """Parse the exact to_dict schema and revalidate the complete plan."""
        record = _fields(value, {"sources", "gates", "output"})
        if not isinstance(record["sources"], (list, tuple)) or not isinstance(
                record["gates"], (list, tuple)):
            raise ValueError("serialized sources and gates must be arrays")
        sources = []
        for value in record["sources"]:
            source = _fields(value, {"identifier", "revision"})
            sources.append(InputSource(source["identifier"], source["revision"]))
        gates = []
        for value in record["gates"]:
            gate = _fields(value, {"operator", "left", "right"})
            op = _fields(gate["operator"], {"name", "truth"})
            if not isinstance(op["truth"], (list, tuple)):
                raise ValueError("serialized operator truth vector must be an array")
            operator = _operator(BinaryBooleanOperator(op["name"], tuple(op["truth"])))
            gates.append(CircuitGate(operator, gate["left"], gate["right"]))
        return cls(tuple(sources), tuple(gates), record["output"])


@dataclass(frozen=True)
class GateTrace:
    """One declared gate's full truth vector and syntactic source dependencies."""

    ref: int
    operator: BinaryBooleanOperator
    left: int
    right: int
    truth_vector: tuple[int, ...]
    source_support: tuple[InputSource, ...]


@dataclass(frozen=True)
class CircuitEvaluation:
    """Exhaustive evaluation in lexicographic source order (00..0 through 11..1).

    gate_traces includes unused gates so the whole description is inspectable.
    Costs and source_support apply only to the selected output. Support means
    syntactic provenance, not essential-variable support: a binary constant gate
    still retains the sources supplied to its pins. No semantic simplification
    changes the represented computation or the cost being measured.
    """

    sources: tuple[InputSource, ...]
    source_truth_vectors: tuple[tuple[int, ...], ...]
    gate_traces: tuple[GateTrace, ...]
    output_truth_vector: tuple[int, ...]
    source_support: tuple[InputSource, ...]
    reachable_gate_refs: tuple[int, ...]
    dag_gate_count: int
    formula_size: int
    depth: int


def evaluate_plan(plan: CircuitPlan) -> CircuitEvaluation:
    """Evaluate all 2**n declared input assignments and measure the chosen output.

    Equal source values in any row never merge sources. Repeated gate pins are
    counted twice by formula_size and once by reachable-node DAG size.
    """
    if not isinstance(plan, CircuitPlan):
        raise ValueError("evaluation requires a validated CircuitPlan")
    n = len(plan.sources)
    source_vectors = tuple(
        tuple((row >> (n - index - 1)) & 1 for row in range(1 << n))
        for index in range(n)
    )
    vectors = list(source_vectors)
    supports = [frozenset((index,)) for index in range(n)]
    formula_sizes = [0] * n
    depths = [0] * n
    traces = []

    def identities(indices: frozenset[int]) -> tuple[InputSource, ...]:
        return tuple(source for index, source in enumerate(plan.sources) if index in indices)

    for ref, gate in enumerate(plan.gates, start=n):
        truth = tuple(gate.operator.apply(left, right)
                      for left, right in zip(vectors[gate.left], vectors[gate.right]))
        support = supports[gate.left] | supports[gate.right]
        vectors.append(truth)
        supports.append(support)
        formula_sizes.append(1 + formula_sizes[gate.left] + formula_sizes[gate.right])
        depths.append(1 + max(depths[gate.left], depths[gate.right]))
        traces.append(GateTrace(ref, gate.operator, gate.left, gate.right, truth,
                                identities(support)))
    reachable: set[int] = set()
    pending = [plan.output]
    while pending:
        ref = pending.pop()
        if ref < n or ref in reachable:
            continue
        reachable.add(ref)
        gate = plan.gates[ref - n]
        pending.extend((gate.left, gate.right))
    return CircuitEvaluation(
        plan.sources, source_vectors, tuple(traces), vectors[plan.output],
        identities(supports[plan.output]), tuple(sorted(reachable)), len(reachable),
        formula_sizes[plan.output], depths[plan.output],
    )


@dataclass(frozen=True)
class CostWitness:
    """An exact nonnegative cost with a concrete source-aware circuit witness."""

    cost: int
    plan: CircuitPlan


@dataclass(frozen=True)
class MinimumCosts:
    """Independent optima; an unreachable target has None for all three metrics."""

    target: UnaryTruth
    formula: CostWitness | None
    dag: CostWitness | None
    depth: CostWitness | None


@dataclass(frozen=True)
class _Expression:
    cost: int
    operator: BinaryBooleanOperator | None = None
    left: _Expression | None = None
    right: _Expression | None = None


def _basis(values: Iterable[BinaryBooleanOperator | str]) -> tuple[BinaryBooleanOperator, ...]:
    # Equal operations need not be considered repeatedly during synthesis.
    # A canonical name among aliases makes witnesses independent of input order.
    canonical: dict[tuple[int, int, int, int], BinaryBooleanOperator] = {}
    for value in values:
        op = _operator(value)
        previous = canonical.get(op.truth)
        if previous is None or op.name < previous.name:
            canonical[op.truth] = op
    return tuple(sorted(canonical.values(), key=lambda op: (op.truth, op.name)))


def _apply(op: BinaryBooleanOperator, left: UnaryTruth, right: UnaryTruth) -> UnaryTruth:
    return op.apply(left[0], right[0]), op.apply(left[1], right[1])


def _tree_minima(basis: tuple[BinaryBooleanOperator, ...], depth: bool) -> dict[UnaryTruth, _Expression]:
    """Solve the four-state Bellman recurrences by strict integer relaxation.

    Start with x of cost zero and relax every ordered pair under every operator:
    formula = 1 + left + right; depth = 1 + max(left, right). Every installed
    candidate is witnessed by a finite expression. At the fixed point, induction
    on any competing expression gives the computed value <= its cost. Thus the
    witnessed values are exact. Only four semantic functions exist; each first
    obtains a finite integer and thereafter strictly decreases, so termination
    is finite. Operators/pairs have fixed order; equal-cost ties retain the first
    witness. Semantic states here identify a single synthesis variable only.
    """
    best = {PROJECTION: _Expression(0)}
    changed = True
    while changed:
        changed = False
        current = tuple(sorted(best.items()))
        for op in basis:
            for (left_truth, left), (right_truth, right) in product(current, repeat=2):
                truth = _apply(op, left_truth, right_truth)
                candidate = 1 + (max(left.cost, right.cost) if depth else left.cost + right.cost)
                if truth not in best or candidate < best[truth].cost:
                    best[truth] = _Expression(candidate, op, left, right)
                    changed = True
    return best


def _tree_plan(expression: _Expression, source: InputSource) -> CircuitPlan:
    gates: list[CircuitGate] = []

    def emit(node: _Expression) -> int:
        if node.operator is None:
            return 0
        left, right = emit(node.left), emit(node.right)
        gates.append(CircuitGate(node.operator, left, right))
        return len(gates)

    output = emit(expression)
    return CircuitPlan((source,), tuple(gates), output)


@dataclass(frozen=True)
class _Step:
    operator: BinaryBooleanOperator
    left: UnaryTruth
    right: UnaryTruth
    output: UnaryTruth


def _dag_minima(basis: tuple[BinaryBooleanOperator, ...], source: InputSource) -> dict[UnaryTruth, CostWitness]:
    """BFS over sets of available unary functions gives exact shared-gate minima.

    A state is a subset of the four unary functions containing x. One transition
    adds one previously unavailable output, using any ordered available pair.
    Unit-weight BFS therefore finds the fewest gates reaching each target.

    Completeness: take an arbitrary unary straight-line circuit. If a gate's
    function already occurred at an input or earlier gate, redirect all its uses
    and the output to that earlier node and delete the duplicate. This preserves
    unary semantics, acyclicity, and does not increase gate count. Delete unused
    gates. The remaining program adds a new function at every step, so its path
    occurs in this search. State histories with the same available set have the
    same possible next semantic operations; only their shortest history matters.
    There are at most eight such subsets and three additions. This reduction is
    for unary synthesis alone: runtime/source-aware plans retain distinct input
    identities, separate revisions, and separate syntactic gates.
    """
    initial = frozenset((PROJECTION,))
    queue = deque((initial,))
    histories: dict[frozenset[UnaryTruth], tuple[_Step, ...]] = {initial: ()}
    witnesses: dict[UnaryTruth, CostWitness] = {}
    while queue:
        state = queue.popleft()
        history = histories[state]
        for target in sorted(state):
            if target in witnesses:
                continue
            refs = {PROJECTION: 0}
            gates = []
            for step in history:
                gates.append(CircuitGate(step.operator, refs[step.left], refs[step.right]))
                refs[step.output] = len(gates)
            plan = CircuitPlan((source,), tuple(gates), refs[target])
            witnesses[target] = CostWitness(len(history), plan)
        for op in basis:
            for left, right in product(sorted(state), repeat=2):
                output = _apply(op, left, right)
                if output in state:
                    continue
                successor = state | {output}
                if successor in histories:
                    continue
                histories[successor] = history + (_Step(op, left, right, output),)
                queue.append(successor)
    return witnesses


def all_unary_minima(
    basis: Iterable[BinaryBooleanOperator | str],
    source: InputSource = InputSource("x", "v1"),
) -> Mapping[UnaryTruth, MinimumCosts]:
    """Return an immutable mapping of all four unary targets to exact optima.

    An empty basis is allowed: only projection x is then reachable at zero cost.
    Witnesses have one declared source, preserve its identity/revision, and use
    only the supplied operators. The three witnesses may differ because each
    metric is optimized independently. Names are factory names or detached
    BinaryBooleanOperator values. Equal truth tables use their smallest name
    lexicographically; this normalization never applies to evaluated plans.
    """
    if not isinstance(source, InputSource):
        raise ValueError("synthesis source must be an InputSource")
    operators = _basis(basis)
    formula = _tree_minima(operators, depth=False)
    depth = _tree_minima(operators, depth=True)
    dag = _dag_minima(operators, source)
    result = {}
    for target in UNARY_FUNCTIONS:
        formula_witness = (CostWitness(formula[target].cost, _tree_plan(formula[target], source))
                           if target in formula else None)
        depth_witness = (CostWitness(depth[target].cost, _tree_plan(depth[target], source))
                         if target in depth else None)
        result[target] = MinimumCosts(target, formula_witness, dag.get(target), depth_witness)
    return MappingProxyType(result)


def minimum_costs(
    basis: Iterable[BinaryBooleanOperator | str],
    target: UnaryTruth = (1, 1),
    source: InputSource = InputSource("x", "v1"),
) -> MinimumCosts:
    """Return exact formula/DAG/depth costs and plans, defaulting to unary TRUE."""
    if (not isinstance(target, (tuple, list)) or len(target) != 2
            or any(type(bit) is not int or bit not in (0, 1) for bit in target)):
        raise ValueError("unary target must contain exactly two integer 0/1 values")
    return all_unary_minima(basis, source)[tuple(target)]
