"""Behavioral checks for exact synthesis and source-aware local circuit plans."""

import importlib.util
import json
from dataclasses import FrozenInstanceError
from itertools import combinations
from pathlib import Path
import sys
import unittest

PROJECT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT_ROOT / "code"))

import cook_cycle_factories as predecessor

if importlib.util.find_spec("circuit_costs") is not None:
    import circuit_costs as costs
else:
    costs = None


class CircuitCostsTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(costs, "the new circuit_costs module is not implemented")

    def assert_witness(self, witness, target, metric):
        result = costs.evaluate_plan(witness.plan)
        self.assertEqual(result.output_truth_vector, target)
        self.assertEqual(getattr(result, metric), witness.cost)

    def test_six_singleton_true_minima(self):
        # Lower bounds and witnesses are derived separately in CIRCUIT_COSTS.md.
        expected = {
            "NOR": (5, 3, 3),
            "NAND": (2, 2, 2),
            "XNOR": (1, 1, 1),
            "Y_IMPLIES_X": (1, 1, 1),
            "X_IMPLIES_Y": (1, 1, 1),
            "TRUE": (1, 1, 1),
        }
        for name, want in expected.items():
            with self.subTest(operator=name):
                result = costs.minimum_costs([name])
                self.assertEqual(
                    (result.formula.cost, result.dag.cost, result.depth.cost), want
                )
                self.assert_witness(result.formula, (1, 1), "formula_size")
                self.assert_witness(result.dag, (1, 1), "dag_gate_count")
                self.assert_witness(result.depth, (1, 1), "depth")

    def test_every_singleton_and_pair_matches_predecessor_existence(self):
        ops = predecessor.BooleanOperatorFactory.all()
        checked = yes = no = 0
        for size in (1, 2):
            for basis in combinations(ops, size):
                expected = predecessor.TautologyFactory().operators(basis).run()
                all_targets = costs.all_unary_minima(basis)
                for target, target_result in all_targets.items():
                    target_reachable = target in expected.unary_closure
                    for witness, metric in ((target_result.formula, "formula_size"),
                                            (target_result.dag, "dag_gate_count"),
                                            (target_result.depth, "depth")):
                        self.assertEqual(witness is not None, target_reachable, (basis, target))
                        if witness is not None:
                            self.assert_witness(witness, target, metric)
                result = all_targets[(1, 1)]
                reachable = result.formula is not None
                self.assertEqual(reachable, expected.generates_true, basis)
                self.assertEqual(result.dag is not None, reachable, basis)
                self.assertEqual(result.depth is not None, reachable, basis)
                if reachable:
                    yes += 1
                    self.assert_witness(result.formula, (1, 1), "formula_size")
                    self.assert_witness(result.dag, (1, 1), "dag_gate_count")
                    self.assert_witness(result.depth, (1, 1), "depth")
                else:
                    no += 1
                checked += 1
        self.assertEqual((checked, yes, no), (136, 93, 43))

    def test_all_four_unary_targets_have_exact_nor_minima(self):
        results = costs.all_unary_minima(["NOR"])
        expected = {
            (0, 0): (2, 2, 2),
            (0, 1): (0, 0, 0),
            (1, 0): (1, 1, 1),
            (1, 1): (5, 3, 3),
        }
        self.assertEqual(set(results), set(expected))
        for target, want in expected.items():
            result = results[target]
            self.assertEqual((result.formula.cost, result.dag.cost, result.depth.cost), want)
            for witness, metric in ((result.formula, "formula_size"),
                                    (result.dag, "dag_gate_count"),
                                    (result.depth, "depth")):
                self.assert_witness(witness, target, metric)
        with self.assertRaises(TypeError):
            results[(0, 1)] = None

    def test_nor_dag_reuses_false_but_tree_cost_unfolds_both_pins(self):
        result = costs.minimum_costs(["NOR"])
        plan = result.dag.plan
        gate = plan.gates[plan.output - len(plan.sources)]
        self.assertEqual(gate.left, gate.right)
        evaluated = costs.evaluate_plan(plan)
        false_trace = next(t for t in evaluated.gate_traces if t.ref == gate.left)
        self.assertEqual(false_trace.truth_vector, (0, 0))
        self.assertEqual((evaluated.dag_gate_count, evaluated.formula_size, evaluated.depth),
                         (3, 5, 3))

    def test_mixed_basis_can_reach_true_when_neither_singleton_can(self):
        self.assertIsNone(costs.minimum_costs(["NOT_X"]).formula)
        self.assertIsNone(costs.minimum_costs(["OR"]).formula)
        result = costs.minimum_costs(["NOT_X", "OR"])
        self.assertEqual((result.formula.cost, result.dag.cost, result.depth.cost), (2, 2, 2))
        self.assertEqual(costs.minimum_costs(["NOR", "TRUE"]).formula.cost, 1)
        self.assertEqual(costs.minimum_costs(["NOR", "NAND"]).formula.cost, 2)

    def test_empty_basis_has_only_free_projection(self):
        results = costs.all_unary_minima([])
        for target, result in results.items():
            if target == (0, 1):
                self.assertEqual((result.formula.cost, result.dag.cost, result.depth.cost),
                                 (0, 0, 0))
                self.assertEqual(result.formula.plan.gates, ())
            else:
                self.assertIsNone(result.formula)
                self.assertIsNone(result.dag)
                self.assertIsNone(result.depth)

    def test_basis_order_duplicates_and_aliases_do_not_change_witnesses(self):
        alias = predecessor.BinaryBooleanOperator("alternative NOR", (1, 0, 0, 0))
        a = costs.minimum_costs(["OR", "NOR", alias, "OR"])
        b = costs.minimum_costs([alias, "NOR", "OR"])
        self.assertEqual(a, b)

    def test_all_sixteen_binary_truth_vectors_keep_ordered_pins(self):
        x, y = costs.InputSource("x", "r1"), costs.InputSource("y", "r1")
        for op in predecessor.BooleanOperatorFactory.all():
            plan = costs.CircuitPlan((x, y), (costs.CircuitGate(op, 0, 1),), 2)
            actual = costs.evaluate_plan(plan)
            self.assertEqual(actual.output_truth_vector, op.truth, op.name)
            self.assertEqual(actual.source_truth_vectors, ((0, 0, 1, 1), (0, 1, 0, 1)))
            swapped = costs.CircuitPlan((x, y), (costs.CircuitGate(op, 1, 0),), 2)
            self.assertEqual(costs.evaluate_plan(swapped).output_truth_vector,
                             (op.truth[0], op.truth[2], op.truth[1], op.truth[3]))

    def test_distinct_input_identity_and_revision_survive_equal_values(self):
        sources = (costs.InputSource("x", "r1"), costs.InputSource("y", "r1"),
                   costs.InputSource("x", "r2"))
        plan = costs.CircuitPlan(sources, (costs.CircuitGate("X_IMPLIES_Y", 0, 1),), 3)
        result = costs.evaluate_plan(plan)
        self.assertEqual(result.output_truth_vector, (1, 1, 1, 1, 0, 0, 1, 1))
        self.assertEqual(result.source_support, sources[:2])
        self.assertEqual(plan.sources, sources)
        # Equal values at rows 000 and 110 are still two retained input identities.
        self.assertEqual(result.output_truth_vector[0], result.output_truth_vector[6])
        tied = costs.CircuitPlan(sources, (costs.CircuitGate("X_IMPLIES_Y", 0, 0),), 3)
        self.assertEqual(costs.evaluate_plan(tied).output_truth_vector, (1,) * 8)
        self.assertNotEqual(result.output_truth_vector, costs.evaluate_plan(tied).output_truth_vector)

    def test_only_reachable_gates_contribute_to_all_costs(self):
        x, unused = costs.InputSource("x", "1"), costs.InputSource("unused", "1")
        plan = costs.CircuitPlan((x, unused), (
            costs.CircuitGate("NOR", 0, 0),
            costs.CircuitGate("NOR", 2, 2),
            costs.CircuitGate("XNOR", 0, 0),
        ), 4)
        result = costs.evaluate_plan(plan)
        self.assertEqual((result.dag_gate_count, result.formula_size, result.depth), (1, 1, 1))
        self.assertEqual(result.reachable_gate_refs, (4,))
        self.assertEqual(result.source_support, (x,))
        self.assertEqual(len(result.gate_traces), 3)
        output_source = costs.CircuitPlan(plan.sources, plan.gates, 1)
        evaluated = costs.evaluate_plan(output_source)
        self.assertEqual((evaluated.dag_gate_count, evaluated.formula_size, evaluated.depth), (0, 0, 0))
        self.assertEqual(evaluated.source_support, (unused,))

    def test_equal_runtime_gate_functions_remain_distinct_nodes(self):
        source = costs.InputSource("x", "1")
        plan = costs.CircuitPlan((source,), (
            costs.CircuitGate("NOR", 0, 0),
            costs.CircuitGate("NOR", 0, 0),
            costs.CircuitGate("OR", 1, 2),
        ), 3)
        evaluated = costs.evaluate_plan(plan)
        self.assertEqual((evaluated.dag_gate_count, evaluated.formula_size, evaluated.depth),
                         (3, 3, 2))
        self.assertEqual(evaluated.reachable_gate_refs, (1, 2, 3))
        self.assertEqual(evaluated.gate_traces[0].truth_vector, (1, 0))
        self.assertEqual(evaluated.gate_traces[1].truth_vector, (1, 0))
        self.assertNotEqual(evaluated.gate_traces[0].ref, evaluated.gate_traces[1].ref)

    def test_constant_gate_preserves_both_syntactic_source_dependencies(self):
        sources = (costs.InputSource("x", "1"), costs.InputSource("y", "1"))
        plan = costs.CircuitPlan(sources, (costs.CircuitGate("TRUE", 0, 1),), 2)
        evaluated = costs.evaluate_plan(plan)
        self.assertEqual(evaluated.output_truth_vector, (1, 1, 1, 1))
        self.assertEqual(evaluated.source_support, sources)
        self.assertEqual(evaluated.gate_traces[0].source_support, sources)
        self.assertEqual((evaluated.dag_gate_count, evaluated.formula_size, evaluated.depth),
                         (1, 1, 1))

    def test_source_limit_and_source_identity_validation(self):
        x = costs.InputSource("x", "1")
        with self.assertRaises(ValueError):
            costs.CircuitPlan((x, x), (), 0)
        for identifier, revision in (("", "1"), ("x", ""), (1, "1"), ("x", None)):
            with self.subTest(identity=(identifier, revision)), self.assertRaises(ValueError):
                costs.InputSource(identifier, revision)
        with self.assertRaises(ValueError):
            costs.CircuitPlan((), (), 0)
        sources = tuple(costs.InputSource(str(i), "1") for i in range(11))
        with self.assertRaises(ValueError):
            costs.CircuitPlan(sources, (), 0)
        plan = costs.CircuitPlan(sources[:10], (), 0)
        self.assertEqual(len(costs.evaluate_plan(plan).output_truth_vector), 1024)

    def test_negative_noninteger_forward_and_cyclic_refs_are_rejected(self):
        x = costs.InputSource("x", "1")
        for bad in (-1, 0.0, True, "0", None):
            with self.subTest(ref=bad), self.assertRaises(ValueError):
                costs.CircuitGate("NOR", bad, 0)
        for output in (-1, 1, True, 0.0):
            with self.subTest(output=output), self.assertRaises(ValueError):
                costs.CircuitPlan((x,), (), output)
        for gates in (
            (costs.CircuitGate("NOR", 0, 1),),
            (costs.CircuitGate("NOR", 0, 2), costs.CircuitGate("NOR", 0, 1)),
        ):
            with self.subTest(gates=gates), self.assertRaises(ValueError):
                costs.CircuitPlan((x,), gates, 1)

    def test_detached_immutable_plans_and_truth_vectors(self):
        truth = [1, 0, 0, 0]
        op = predecessor.BinaryBooleanOperator("custom NOR", truth)
        sources = [costs.InputSource("x", "1")]
        gates = [costs.CircuitGate(op, 0, 0)]
        plan = costs.CircuitPlan(sources, gates, 1)
        sources.clear()
        gates.clear()
        truth[0] = 0
        self.assertEqual(costs.evaluate_plan(plan).output_truth_vector, (1, 0))
        with self.assertRaises(FrozenInstanceError):
            plan.output = 0
        with self.assertRaises(FrozenInstanceError):
            plan.sources[0].revision = "2"
        with self.assertRaises(FrozenInstanceError):
            plan.gates[0].left = 1
        with self.assertRaises(TypeError):
            plan.gates[0].operator.truth[0] = 0

    def test_json_round_trip_preserves_unused_and_versioned_sources(self):
        sources = (costs.InputSource("x", "1"), costs.InputSource("x", "2"),
                   costs.InputSource("unused", "1"))
        op = predecessor.BinaryBooleanOperator("custom implication", (1, 1, 0, 1))
        plan = costs.CircuitPlan(sources, (costs.CircuitGate(op, 0, 1),), 3)
        serialized = json.loads(json.dumps(plan.to_dict()))
        restored = costs.CircuitPlan.from_dict(serialized)
        self.assertEqual(restored, plan)
        self.assertEqual(restored.sources, sources)
        self.assertEqual(costs.evaluate_plan(restored), costs.evaluate_plan(plan))
        serialized["gates"][0]["left"] = 3
        with self.assertRaises(ValueError):
            costs.CircuitPlan.from_dict(serialized)

    def test_invalid_operators_targets_and_record_shapes_are_rejected(self):
        for bad in (42, None, object()):
            with self.subTest(operator=bad), self.assertRaises((ValueError, TypeError)):
                costs.minimum_costs([bad])
        for target in ((1,), (1, 0, 0), (1, 2), (True, False), "11"):
            with self.subTest(target=target), self.assertRaises(ValueError):
                costs.minimum_costs(["NOR"], target=target)
        for data in ({}, {"sources": [], "gates": [], "output": 0},
                     {"sources": [{"identifier": "x", "revision": "1"}],
                      "gates": [{"operator": {"name": "bad", "truth": [0, 0, 0, 2]},
                                 "left": 0, "right": 0}], "output": 1}):
            with self.subTest(data=data), self.assertRaises(ValueError):
                costs.CircuitPlan.from_dict(data)

    def test_requested_source_identity_is_retained_in_every_witness(self):
        source = costs.InputSource("temperature-sensor", "revision-17")
        result = costs.minimum_costs(["NOR"], source=source)
        for witness in (result.formula, result.dag, result.depth):
            self.assertEqual(witness.plan.sources, (source,))
            self.assertEqual(costs.evaluate_plan(witness.plan).source_support, (source,))


if __name__ == "__main__":
    unittest.main()
