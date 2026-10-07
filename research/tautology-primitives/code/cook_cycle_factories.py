from __future__ import annotations

import struct
from dataclasses import dataclass, field, asdict
from itertools import combinations, product
from types import MappingProxyType
from typing import Any, Dict, Iterable, List, Mapping, MutableMapping, Optional, Protocol, Sequence, Set, Tuple

# =============================================================================
# Constants
# =============================================================================
SHIFT_WORD = 0
MASK_WORD = 0x7F
WORD_BITS = 7
STATE_BITS = 53
INT53_MASK = (1 << STATE_BITS) - 1


# =============================================================================
# Immutable records / Episteme-style descriptions
# =============================================================================
@dataclass(frozen=True)
class Origin:
    source: str = "local"
    revision: str = "unversioned"
    note: str = ""


@dataclass(frozen=True)
class ExecutionLimits:
    max_dpll_calls: int = 100_000
    max_clauses: int = 50_000
    max_variables: int = 10_000


@dataclass(frozen=True)
class OperationDefinition:
    id: str
    version: str
    meaning: str


@dataclass(frozen=True)
class CyclePlan:
    family: str
    version: str
    initial_coordinate: int
    explore_delta: int
    transport_delta: int
    return_delta: int
    origin: Origin
    limits: ExecutionLimits
    definitions: Tuple[OperationDefinition, ...]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "family": self.family,
            "version": self.version,
            "initial_coordinate": self.initial_coordinate,
            "explore_delta": self.explore_delta,
            "transport_delta": self.transport_delta,
            "return_delta": self.return_delta,
            "origin": asdict(self.origin),
            "limits": asdict(self.limits),
            "definitions": [asdict(d) for d in self.definitions],
        }


@dataclass(frozen=True)
class CycleStates:
    s0: int
    s1: int
    s2: int
    s1_returned: int
    s3: int

    @property
    def final_word(self) -> int:
        return self.s3 & MASK_WORD


@dataclass(frozen=True)
class VerificationRecord:
    satisfiable: bool
    assignment: Mapping[int, bool]
    dpll_calls: int
    branch_calls: int
    unit_propagations: int
    clauses: int
    variables: int


@dataclass(frozen=True)
class CycleResult:
    ok: bool
    complete: bool
    plan: CyclePlan
    states: CycleStates
    float_carrier: float
    verification: VerificationRecord
    trace: Tuple[str, ...]
    error: Optional[str] = None


@dataclass(frozen=True)
class TautologyAnalysis:
    operator_names: Tuple[str, ...]
    generates_true: bool
    generates_false: bool
    unary_closure: Tuple[Tuple[int, int], ...]
    reason: str


# =============================================================================
# Narrow interfaces (SOLID: ISP / DIP)
# =============================================================================
class CoordinateCodec(Protocol):
    def normalize(self, value: int) -> int: ...
    def read_word(self, value: int) -> int: ...
    def write_word(self, value: int, word: int) -> int: ...
    def to_float_carrier(self, value: int) -> float: ...
    def from_float_carrier(self, value: float) -> int: ...


class SatSolver(Protocol):
    def solve(self, clauses: Sequence[Set[int]], limits: ExecutionLimits) -> VerificationRecord: ...


class CycleEvaluator(Protocol):
    def run(self, plan: CyclePlan) -> CycleResult: ...


# =============================================================================
# Concrete coordinate codec (SRP)
# =============================================================================
class Int53WordCodec:
    def normalize(self, value: int) -> int:
        return value & INT53_MASK

    def read_word(self, value: int) -> int:
        return (value >> SHIFT_WORD) & MASK_WORD

    def write_word(self, value: int, word: int) -> int:
        return (value & ~(MASK_WORD << SHIFT_WORD)) | ((word & MASK_WORD) << SHIFT_WORD)

    def to_float_carrier(self, value: int) -> float:
        return struct.unpack("<d", struct.pack("<Q", value & INT53_MASK))[0]

    def from_float_carrier(self, value: float) -> int:
        return struct.unpack("<Q", struct.pack("<d", value))[0] & INT53_MASK


# =============================================================================
# Boolean primitives / tautology research
# =============================================================================
@dataclass(frozen=True)
class BinaryBooleanOperator:
    name: str
    # Ordered 00, 01, 10, 11.
    truth: Tuple[int, int, int, int]

    def __post_init__(self) -> None:
        if len(self.truth) != 4 or any(v not in (0, 1) for v in self.truth):
            raise ValueError("binary truth vector must contain four 0/1 values")

    def apply(self, a: int | bool, b: int | bool) -> int:
        ai, bi = int(bool(a)), int(bool(b))
        return self.truth[(ai << 1) | bi]

    @property
    def preserves_zero(self) -> bool:
        return self.truth[0] == 0

    @property
    def self_dual(self) -> bool:
        # f(x,y) = NOT f(NOT x, NOT y)
        return (
            self.truth[0] == 1 - self.truth[3]
            and self.truth[1] == 1 - self.truth[2]
        )


class BooleanOperatorFactory:
    """Creates named immutable Boolean operators; no evaluation state lives here."""

    _OPS: Mapping[str, Tuple[int, int, int, int]] = MappingProxyType({
        "FALSE": (0, 0, 0, 0),
        "AND": (0, 0, 0, 1),
        "X_AND_NOT_Y": (0, 0, 1, 0),
        "X": (0, 0, 1, 1),
        "NOT_X_AND_Y": (0, 1, 0, 0),
        "Y": (0, 1, 0, 1),
        "XOR": (0, 1, 1, 0),
        "OR": (0, 1, 1, 1),
        "NOR": (1, 0, 0, 0),
        "XNOR": (1, 0, 0, 1),
        "NOT_Y": (1, 0, 1, 0),
        "Y_IMPLIES_X": (1, 0, 1, 1),
        "NOT_X": (1, 1, 0, 0),
        "X_IMPLIES_Y": (1, 1, 0, 1),
        "NAND": (1, 1, 1, 0),
        "TRUE": (1, 1, 1, 1),
    })

    @classmethod
    def named(cls, name: str) -> BinaryBooleanOperator:
        key = name.upper()
        if key not in cls._OPS:
            raise KeyError(f"unknown Boolean operator: {name}")
        return BinaryBooleanOperator(key, cls._OPS[key])

    @classmethod
    def all(cls) -> Tuple[BinaryBooleanOperator, ...]:
        return tuple(BinaryBooleanOperator(name, truth) for name, truth in cls._OPS.items())


class TautologyFactory:
    """
    Fluent, bounded analyzer for the constant-TRUE question.

    This deliberately answers a weaker question than functional completeness:
    can compositions of the selected binary operators and projection variables
    express the unary constant TRUE function?
    """

    def __init__(self) -> None:
        self._operators: List[BinaryBooleanOperator] = []
        self._origin = Origin(source="tautology-research", revision="v1")

    def operator(self, operator: BinaryBooleanOperator | str) -> "TautologyFactory":
        op = BooleanOperatorFactory.named(operator) if isinstance(operator, str) else operator
        self._operators.append(op)
        return self

    def operators(self, operators: Iterable[BinaryBooleanOperator | str]) -> "TautologyFactory":
        for operator in operators:
            self.operator(operator)
        return self

    def origin(self, source: str, revision: str = "unversioned", note: str = "") -> "TautologyFactory":
        self._origin = Origin(source, revision, note)
        return self

    @staticmethod
    def _apply_unary(op: BinaryBooleanOperator, left: Tuple[int, int], right: Tuple[int, int]) -> Tuple[int, int]:
        return (
            op.apply(left[0], right[0]),
            op.apply(left[1], right[1]),
        )

    def build(self) -> Tuple[BinaryBooleanOperator, ...]:
        if not self._operators:
            raise ValueError("at least one Boolean operator is required")
        # Detached immutable snapshot, mirroring Episteme's build() contract.
        return tuple(self._operators)

    def run(self) -> TautologyAnalysis:
        operators = self.build()
        closure: Set[Tuple[int, int]] = {(0, 1)}  # unary projection x
        changed = True
        while changed:
            changed = False
            current = tuple(closure)
            for op in operators:
                for left in current:
                    for right in current:
                        out = self._apply_unary(op, left, right)
                        if out not in closure:
                            closure.add(out)
                            changed = True

        generates_true = (1, 1) in closure
        generates_false = (0, 0) in closure

        all_zero_preserving = all(op.preserves_zero for op in operators)
        all_self_dual = all(op.self_dual for op in operators)
        if generates_true:
            reason = "constant TRUE is present in the unary composition closure"
        elif all_zero_preserving:
            reason = "blocked: every selected operator is 0-preserving"
        elif all_self_dual:
            reason = "blocked: every selected operator is self-dual"
        else:
            reason = "not generated in exact unary closure"

        return TautologyAnalysis(
            operator_names=tuple(op.name for op in operators),
            generates_true=generates_true,
            generates_false=generates_false,
            unary_closure=tuple(sorted(closure)),
            reason=reason,
        )


# =============================================================================
# CNF clause factories
# =============================================================================
class VariableFactory:
    def __init__(self, state_layers: int) -> None:
        self._state_layers = state_layers
        self._next = state_layers * STATE_BITS + 1

    @staticmethod
    def state(state_idx: int, bit: int) -> int:
        return state_idx * STATE_BITS + bit + 1

    def auxiliary(self) -> int:
        value = self._next
        self._next += 1
        return value

    @property
    def max_variable(self) -> int:
        return self._next - 1


class BooleanRelationFactory:
    """Creates CNF clauses for exact finite Boolean relations."""

    @staticmethod
    def forbid_assignment(variables: Sequence[int], values: Sequence[bool]) -> Set[int]:
        return {
            (-var if value else var)
            for var, value in zip(variables, values)
        }

    @classmethod
    def function(cls, inputs: Sequence[int], output: int, fn) -> List[Set[int]]:
        variables = list(inputs) + [output]
        clauses: List[Set[int]] = []
        for row in product((False, True), repeat=len(variables)):
            in_values = row[:-1]
            out_value = row[-1]
            if out_value != bool(fn(*in_values)):
                clauses.append(cls.forbid_assignment(variables, row))
        return clauses

    @staticmethod
    def equivalent(a: int, b: int) -> List[Set[int]]:
        return [{-a, b}, {a, -b}]

    @staticmethod
    def opposite(a: int, b: int) -> List[Set[int]]:
        return [{-a, -b}, {a, b}]


class TransitionClauseFactory:
    """Single responsibility: encode the lifecycle relations as CNF."""

    def __init__(self, vars_: VariableFactory) -> None:
        self.v = vars_
        self.rel = BooleanRelationFactory()

    def preserve_nonword(self, src: int, dst: int) -> List[Set[int]]:
        clauses: List[Set[int]] = []
        for bit in range(WORD_BITS, STATE_BITS):
            clauses.extend(self.rel.equivalent(self.v.state(src, bit), self.v.state(dst, bit)))
        return clauses

    def plus_64(self, src: int, dst: int) -> List[Set[int]]:
        clauses: List[Set[int]] = []
        for bit in range(STATE_BITS):
            a = self.v.state(src, bit)
            b = self.v.state(dst, bit)
            clauses.extend(self.rel.opposite(a, b) if bit == 6 else self.rel.equivalent(a, b))
        return clauses

    def plus_one(self, src: int, dst: int) -> List[Set[int]]:
        clauses = self.preserve_nonword(src, dst)
        carry = self.v.auxiliary()
        clauses.append({carry})
        for bit in range(WORD_BITS):
            a, out = self.v.state(src, bit), self.v.state(dst, bit)
            clauses.extend(self.rel.function([a, carry], out, lambda x, c: x ^ c))
            if bit < WORD_BITS - 1:
                nxt = self.v.auxiliary()
                clauses.extend(self.rel.function([a, carry], nxt, lambda x, c: x and c))
                carry = nxt
        return clauses

    def minus_one(self, src: int, dst: int) -> List[Set[int]]:
        clauses = self.preserve_nonword(src, dst)
        borrow = self.v.auxiliary()
        clauses.append({borrow})
        for bit in range(WORD_BITS):
            a, out = self.v.state(src, bit), self.v.state(dst, bit)
            clauses.extend(self.rel.function([a, borrow], out, lambda x, b: x ^ b))
            if bit < WORD_BITS - 1:
                nxt = self.v.auxiliary()
                clauses.extend(self.rel.function([a, borrow], nxt, lambda x, b: (not x) and b))
                borrow = nxt
        return clauses

    def word_sum(self, left: int, right: int, dst: int) -> List[Set[int]]:
        clauses: List[Set[int]] = []
        carry = self.v.auxiliary()
        clauses.append({-carry})
        for bit in range(WORD_BITS):
            a = self.v.state(left, bit)
            b = self.v.state(right, bit)
            out = self.v.state(dst, bit)
            clauses.extend(self.rel.function([a, b, carry], out, lambda x, y, c: x ^ y ^ c))
            if bit < WORD_BITS - 1:
                nxt = self.v.auxiliary()
                clauses.extend(
                    self.rel.function(
                        [a, b, carry],
                        nxt,
                        lambda x, y, c: (x and y) or (x and c) or (y and c),
                    )
                )
                carry = nxt
        return clauses


class LifecycleClauseFactory:
    """Creates the full lifecycle clause set from immutable state snapshots."""

    STATE_LAYERS = 5

    def build(self, states: CycleStates, limits: ExecutionLimits) -> Tuple[List[Set[int]], int]:
        values = (states.s0, states.s1, states.s2, states.s1_returned, states.s3)
        vars_ = VariableFactory(self.STATE_LAYERS)
        transitions = TransitionClauseFactory(vars_)
        clauses: List[Set[int]] = []

        # Pin all supplied state bits.
        for state_idx, value in enumerate(values):
            value &= INT53_MASK
            for bit in range(STATE_BITS):
                literal = vars_.state(state_idx, bit)
                clauses.append({literal} if ((value >> bit) & 1) else {-literal})

        # Full lifecycle relations.
        clauses.extend(transitions.plus_64(0, 1))
        clauses.extend(transitions.plus_one(1, 2))
        clauses.extend(transitions.minus_one(2, 3))
        clauses.extend(transitions.preserve_nonword(0, 4))
        clauses.extend(transitions.word_sum(3, 2, 4))

        if len(clauses) > limits.max_clauses:
            raise RuntimeError("clause limit exceeded")
        if vars_.max_variable > limits.max_variables:
            raise RuntimeError("variable limit exceeded")
        return clauses, vars_.max_variable


# =============================================================================
# DPLL implementation
# =============================================================================
class DpllSatSolver:
    def solve(self, clauses: Sequence[Set[int]], limits: ExecutionLimits) -> VerificationRecord:
        counters = {"calls": 0, "branches": 0, "unit": 0}

        def recurse(assignment: Dict[int, bool]) -> Tuple[bool, Dict[int, bool]]:
            counters["calls"] += 1
            if counters["calls"] > limits.max_dpll_calls:
                raise RuntimeError("DPLL call limit exceeded")

            simplified: List[Set[int]] = []
            for clause in clauses:
                satisfied = False
                remainder: Set[int] = set()
                for literal in clause:
                    var = abs(literal)
                    sign = literal > 0
                    if var in assignment:
                        if assignment[var] == sign:
                            satisfied = True
                            break
                    else:
                        remainder.add(literal)
                if not satisfied:
                    simplified.append(remainder)

            if not simplified:
                return True, assignment
            if any(len(c) == 0 for c in simplified):
                return False, {}

            for clause in simplified:
                if len(clause) == 1:
                    counters["unit"] += 1
                    literal = next(iter(clause))
                    extended = assignment.copy()
                    extended[abs(literal)] = literal > 0
                    return recurse(extended)

            candidates = sorted({abs(l) for c in simplified for l in c if abs(l) not in assignment})
            if not candidates:
                return False, {}
            chosen = candidates[0]
            counters["branches"] += 1
            for value in (True, False):
                extended = assignment.copy()
                extended[chosen] = value
                sat, model = recurse(extended)
                if sat:
                    return True, model
            return False, {}

        sat, model = recurse({})
        variables = max((abs(l) for c in clauses for l in c), default=0)
        return VerificationRecord(
            satisfiable=sat,
            assignment=MappingProxyType(dict(model)),
            dpll_calls=counters["calls"],
            branch_calls=counters["branches"],
            unit_propagations=counters["unit"],
            clauses=len(clauses),
            variables=variables,
        )


# =============================================================================
# Cycle evaluator
# =============================================================================
class DefaultCycleEvaluator:
    def __init__(self, codec: CoordinateCodec, solver: SatSolver) -> None:
        self.codec = codec
        self.solver = solver
        self.clause_factory = LifecycleClauseFactory()

    def derive_states(self, plan: CyclePlan) -> CycleStates:
        s0 = self.codec.normalize(plan.initial_coordinate)
        s1 = self.codec.write_word(s0, self.codec.read_word(s0) + plan.explore_delta)
        s2 = self.codec.write_word(s1, self.codec.read_word(s1) + plan.transport_delta)
        s1_returned = self.codec.write_word(s2, self.codec.read_word(s2) - plan.return_delta)
        s3 = self.codec.write_word(
            s0,
            self.codec.read_word(s1_returned) + self.codec.read_word(s2),
        )
        return CycleStates(s0, s1, s2, s1_returned, s3)

    def run(self, plan: CyclePlan) -> CycleResult:
        trace: List[str] = []
        try:
            states = self.derive_states(plan)
            trace.append("cycle.states.derived@2")
            clauses, _ = self.clause_factory.build(states, plan.limits)
            trace.append("cycle.cnf.full-lifecycle@2")
            verification = self.solver.solve(clauses, plan.limits)
            trace.append("cycle.dpll.verify@1")
            return CycleResult(
                ok=verification.satisfiable,
                complete=True,
                plan=plan,
                states=states,
                float_carrier=self.codec.to_float_carrier(states.s3),
                verification=verification,
                trace=tuple(trace),
            )
        except Exception as exc:
            empty = CycleStates(0, 0, 0, 0, 0)
            verification = VerificationRecord(False, MappingProxyType({}), 0, 0, 0, 0, 0)
            return CycleResult(
                ok=False,
                complete=False,
                plan=plan,
                states=empty,
                float_carrier=0.0,
                verification=verification,
                trace=tuple(trace),
                error=str(exc),
            )


# =============================================================================
# Fluent builder / factory surface
# =============================================================================
class CookCycleFactory:
    """
    Fluent construction adapter.

    The mutable builder is deliberately thin. build() emits an immutable plan;
    run() delegates to the injected evaluator. This follows the Episteme factory
    pattern without claiming direct runtime compatibility with Episteme JS.
    """

    DEFINITIONS = (
        OperationDefinition("cycle.explore", "2", "replace the 7-bit word by word + delta modulo 128"),
        OperationDefinition("cycle.transport", "2", "replace the 7-bit word by word + delta modulo 128"),
        OperationDefinition("cycle.return", "2", "replace the 7-bit word by word - delta modulo 128"),
        OperationDefinition("cycle.combine", "2", "preserve State-0 non-word bits; sum returned and transported words modulo 128"),
        OperationDefinition("cycle.verify", "2", "pin all states and encode every lifecycle edge as CNF"),
    )

    def __init__(self, initial_coordinate: int, evaluator: CycleEvaluator) -> None:
        self._initial_coordinate = initial_coordinate
        self._explore_delta = 64
        self._transport_delta = 1
        self._return_delta = 1
        self._origin = Origin(source="cook-cycle", revision="factory-v2")
        self._limits = ExecutionLimits()
        self._evaluator = evaluator

    def explore(self, delta: int = 64) -> "CookCycleFactory":
        self._explore_delta = delta & MASK_WORD
        return self

    def transport(self, delta: int = 1) -> "CookCycleFactory":
        self._transport_delta = delta & MASK_WORD
        return self

    def return_by(self, delta: int = 1) -> "CookCycleFactory":
        self._return_delta = delta & MASK_WORD
        return self

    def origin(self, source: str, revision: str = "unversioned", note: str = "") -> "CookCycleFactory":
        self._origin = Origin(source, revision, note)
        return self

    def limits(
        self,
        *,
        max_dpll_calls: Optional[int] = None,
        max_clauses: Optional[int] = None,
        max_variables: Optional[int] = None,
    ) -> "CookCycleFactory":
        current = self._limits
        self._limits = ExecutionLimits(
            max_dpll_calls=max_dpll_calls if max_dpll_calls is not None else current.max_dpll_calls,
            max_clauses=max_clauses if max_clauses is not None else current.max_clauses,
            max_variables=max_variables if max_variables is not None else current.max_variables,
        )
        return self

    def build(self) -> CyclePlan:
        return CyclePlan(
            family="cook-cycle",
            version="2.0.0",
            initial_coordinate=self._initial_coordinate & INT53_MASK,
            explore_delta=self._explore_delta,
            transport_delta=self._transport_delta,
            return_delta=self._return_delta,
            origin=self._origin,
            limits=self._limits,
            definitions=self.DEFINITIONS,
        )

    def run(self) -> CycleResult:
        return self._evaluator.run(self.build())


class FactoryRegistry:
    """Small assembly root; callers depend on interfaces, not constructors."""

    def __init__(self, codec: Optional[CoordinateCodec] = None, solver: Optional[SatSolver] = None) -> None:
        self.codec = codec or Int53WordCodec()
        self.solver = solver or DpllSatSolver()
        self.evaluator = DefaultCycleEvaluator(self.codec, self.solver)

    def cook_cycle(self, initial_coordinate: int) -> CookCycleFactory:
        return CookCycleFactory(initial_coordinate, self.evaluator)

    def tautology(self) -> TautologyFactory:
        return TautologyFactory()


# Public Episteme-like entry point.
Factories = FactoryRegistry()


# =============================================================================
# Compatibility helpers for the earlier procedural API
# =============================================================================
def run_dpll_verified_cook_cycle(initial_coordinate: int) -> Tuple[float, int, bool]:
    result = Factories.cook_cycle(initial_coordinate).run()
    return result.float_carrier, result.states.s3, result.ok


def build_cycle_states(initial_coordinate: int) -> CycleStates:
    plan = Factories.cook_cycle(initial_coordinate).build()
    return Factories.evaluator.derive_states(plan)  # type: ignore[attr-defined]


def verify_cycle_states(states: CycleStates) -> bool:
    clauses, _ = LifecycleClauseFactory().build(states, ExecutionLimits())
    return DpllSatSolver().solve(clauses, ExecutionLimits()).satisfiable


# =============================================================================
# Self-tests / evidence checks
# =============================================================================
def _anchor() -> int:
    return (4 << 41) | (120 << 25) | (8 << 16) | (2 << 12) | (3 << 7) | 15


def self_test() -> Dict[str, Any]:
    codec = Int53WordCodec()
    anchor = _anchor()
    result = (
        Factories.cook_cycle(anchor)
        .explore(64)
        .transport(1)
        .return_by(1)
        .origin("conversation-fixed-code", "factory-v2")
        .run()
    )
    assert result.ok and result.complete
    assert result.states.s3 == 8800120086943
    assert result.states.final_word == 31
    assert isinstance(result.float_carrier, float)

    # Carrier coverage including bit 52.
    carrier_cases = [0, INT53_MASK] + [1 << bit for bit in range(53)]
    for value in carrier_cases:
        assert codec.from_float_carrier(codec.to_float_carrier(value)) == value

    # Preserve all 46 non-word bits.
    for bit in range(7, 53):
        value = (1 << bit) | 15
        out = Factories.cook_cycle(value).run()
        assert out.ok
        assert (out.states.s3 & ~MASK_WORD) == (value & ~MASK_WORD & INT53_MASK)

    # Exhaustive 7-bit word recurrence.
    upper = anchor & ~MASK_WORD
    for word in range(128):
        out = Factories.cook_cycle(upper | word).run()
        assert out.ok
        assert out.states.final_word == ((2 * word + 1) & MASK_WORD)

    # Mutation rejection of every lifecycle edge.
    valid = build_cycle_states(0)
    assert verify_cycle_states(valid)
    mutations = (
        CycleStates(valid.s0, valid.s1 ^ 1, valid.s2, valid.s1_returned, valid.s3),
        CycleStates(valid.s0, valid.s1, valid.s2 ^ 1, valid.s1_returned, valid.s3),
        CycleStates(valid.s0, valid.s1, valid.s2, valid.s1_returned ^ 1, valid.s3),
        CycleStates(valid.s0, valid.s1, valid.s2, valid.s1_returned, valid.s3 ^ 1),
        CycleStates(valid.s0, valid.s1, valid.s2, valid.s1_returned, valid.s3 ^ (1 << 20)),
    )
    assert all(not verify_cycle_states(m) for m in mutations)

    # Single-operator tautology classification.
    generated = []
    for op in BooleanOperatorFactory.all():
        analysis = Factories.tautology().operator(op).run()
        if analysis.generates_true:
            generated.append(op.name)
    expected = ["NOR", "XNOR", "Y_IMPLIES_X", "X_IMPLIES_Y", "NAND", "TRUE"]
    assert generated == expected

    # All singleton/pair bases: exact theorem check for binary operators.
    ops = BooleanOperatorFactory.all()
    checked_bases = 0
    true_bases = 0
    for size in (1, 2):
        for basis in combinations(ops, size):
            analysis = Factories.tautology().operators(basis).run()
            theorem_predicts = (
                not all(op.preserves_zero for op in basis)
                and not all(op.self_dual for op in basis)
            )
            assert analysis.generates_true == theorem_predicts
            checked_bases += 1
            true_bases += int(analysis.generates_true)
    assert checked_bases == 136
    assert true_bases == 93

    # build() must be detached from later fluent mutations.
    builder = Factories.cook_cycle(anchor).transport(1)
    first_plan = builder.build()
    builder.transport(3)
    second_plan = builder.build()
    assert first_plan.transport_delta == 1
    assert second_plan.transport_delta == 3

    return {
        "anchor_s3": result.states.s3,
        "anchor_word": result.states.final_word,
        "anchor_sat": result.ok,
        "carrier_cases": len(carrier_cases),
        "nonword_bits": 46,
        "word_cases": 128,
        "mutation_rejections": len(mutations),
        "tautology_singletons": expected,
        "basis_cases": checked_bases,
        "basis_true": true_bases,
        "basis_false": checked_bases - true_bases,
        "trace": result.trace,
        "dpll_calls": result.verification.dpll_calls,
        "branches": result.verification.branch_calls,
        "unit_propagations": result.verification.unit_propagations,
    }


if __name__ == "__main__":
    summary = self_test()
    print("Factory architecture self-test passed")
    for key, value in summary.items():
        print(f"{key}: {value}")