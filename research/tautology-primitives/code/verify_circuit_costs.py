"""Regenerate and cross-check the fixed FIG-22 cost domain and its provenance.

Run from research/tautology-primitives: python code/verify_circuit_costs.py
The comparison uses optimized semantic synthesis and separate raw syntactic
enumeration. Every saved plan is replayed by a second scalar/ancestry evaluator
below, without calling the production evaluator. The manifest hashes inputs
before and after the run; a successful run requires both hashes to agree.
"""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import time

from cook_cycle_factories import BooleanOperatorFactory, Factories
from circuit_costs import InputSource, minimum_costs
from raw_circuit_enumerator import enumerate_all

ROOT = Path(__file__).resolve().parents[1]
SOURCE_COMMIT = '67053880df1ab44833d55e4cf685b8d8ead1d84c'


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def replay_witness(description: dict) -> dict:
    """Second evaluator of stored unary plans: direct scalar lookup, set ancestry.

    This deliberately avoids the production evaluator's vector implementation.
    Scope is the one-source witnesses produced by this bounded synthesis run.
    """
    require(len(description['sources']) == 1, 'witness must have one symbolic source')
    gates = description['gates']
    depth = [0]
    size = [0]
    ancestors = [set()]
    for ref, gate in enumerate(gates, 1):
        left, right = gate['left'], gate['right']
        require(type(left) is int and type(right) is int and
                0 <= left < ref and 0 <= right < ref, 'invalid topological witness')
        depth.append(1 + max(depth[left], depth[right]))
        size.append(1 + size[left] + size[right])
        ancestors.append(ancestors[left] | ancestors[right] | {ref})
    output = description['output']
    truth = []
    for x in (0, 1):
        values = [x]
        for gate in gates:
            a, b = values[gate['left']], values[gate['right']]
            values.append(gate['operator']['truth'][2*a + b])
        truth.append(values[output])
    require(truth == [1, 1], 'saved witness is not TRUE')
    return {'formula_gates': size[output], 'dag_gates': len(ancestors[output]),
            'depth': depth[output], 'output_truth_vector': truth}


def build_evidence() -> tuple[dict, dict]:
    raw = enumerate_all()
    all_ops = BooleanOperatorFactory.all()
    rows = []
    witnesses_checked = 0
    for raw_row in raw['rows']:
        ids = raw_row['basis_ids']
        basis = tuple(all_ops[i] for i in ids)
        for i, op in zip(ids, basis):
            require(list(op.truth) == [int(c) for c in f'{i:04b}'], 'source orientation mismatch')
        answer = minimum_costs(basis, source=InputSource('fig22:x', 'symbolic-v1'))
        metrics = (('formula_gates', answer.formula), ('dag_gates', answer.dag),
                   ('depth', answer.depth))
        costs = {key: witness.cost if witness is not None else None for key, witness in metrics}
        require(costs == raw_row['minimum'], f'optimized/raw disagreement for basis {ids}')
        predecessor = Factories.tautology().operators(basis).run()
        require(predecessor.generates_true == (answer.formula is not None),
                f'predecessor closure disagreement for basis {ids}')
        saved = {}
        for key, witness in metrics:
            if witness is None:
                saved[key] = None
                continue
            plan = witness.plan.to_dict()
            allowed = {tuple(op.truth) for op in basis}
            require(all(tuple(g['operator']['truth']) in allowed for g in plan['gates']),
                    'witness uses an operation outside its basis')
            replay = replay_witness(plan)
            require(replay[key] == witness.cost, f'witness cost disagreement for {ids}/{key}')
            saved[key] = {'cost': witness.cost, 'plan': plan, 'independent_replay': replay}
            witnesses_checked += 1
        rows.append({'basis_ids': ids, 'operator_names': [op.name for op in basis],
                     'truth_vectors': raw_row['truth_vectors'], 'minimum': costs,
                     'witnesses': saved})
    generating = sum(row['minimum']['formula_gates'] is not None for row in rows)
    result = {
        'schema': 'fig22-minimum-costs-v1', 'source_commit': SOURCE_COMMIT,
        'truth_table_order': ['00', '01', '10', '11'],
        'assertion_tested': raw['assertion_tested'],
        'cost_model': {'gate_weight': 1, 'wires_fanout_and_tied_pins': 'free',
                       'inputs': 'variable sources only', 'input_depth': 0,
                       'formula': 'gate occurrences after unfolding',
                       'dag': 'reachable gate nodes', 'depth': 'longest gate path'},
        'bases_checked': len(rows), 'generates_true': generating,
        'does_not_generate_true': len(rows) - generating,
        'witnesses_checked': witnesses_checked,
        'raw_trees_checked': sum(x['trees'] for r in raw['rows'] for x in r['formula_layers']),
        'raw_programs_checked': sum(x['programs'] for r in raw['rows'] for x in r['dag_layers']),
        'histogram_formula_dag_depth': raw['histogram_formula_dag_depth'],
        'rows': rows,
    }
    require((len(rows), generating, witnesses_checked) == (136, 93, 279), 'population mismatch')
    return result, raw


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    started = datetime.now(timezone.utc).isoformat()
    clock = time.perf_counter()
    paths = sorted([*ROOT.glob('code/*.py'), *ROOT.glob('tests/*.py'),
                    ROOT / 'CIRCUIT_COSTS.md', ROOT / 'COST_PLAN.md',
                    ROOT / 'evidence/circuit_cost_sources.json'])
    for path in paths:
        require(path.is_file(), f'missing verification input: {path.name}')
    before = {path: sha256(path) for path in paths}
    optimized, raw = build_evidence()
    outputs = []
    for name, value in (('minimum_costs.json', optimized), ('raw_minimum_costs.json', raw)):
        path = ROOT / 'evidence' / name
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n', encoding='utf-8')
        outputs.append({'path': str(path.relative_to(ROOT)), 'sha256': sha256(path), 'kind': 'result'})
    artifacts = [{'path': str(p.relative_to(ROOT)), 'sha256': before[p],
                  'sha256_after': sha256(p)} for p in paths]
    require(all(x['sha256'] == x['sha256_after'] for x in artifacts), 'inputs changed during run')
    manifest = {
        'schema_version': 2, 'claim_id': 'FIG-22-minimum-TRUE-costs',
        'repository': {'commit': SOURCE_COMMIT, 'dirty': True,
                       'snapshot': 'Pinned source module plus additive extension; hashes identify the executed working files.'},
        'command': [sys.executable, *sys.argv],
        'environment': {'software': [{'name': 'Python', 'version': platform.python_version()}],
                        'hardware': f'{platform.system()} {platform.machine()}; logical_cpus={os.cpu_count()}'},
        'mathematics': {'assertion_tested': raw['assertion_tested'], 'coefficient_domain': 'two-valued Boolean algebra',
                        'conventions': '00,01,10,11; unary x=0,1; ordered pins; unit gates; free fanout; no primitive constants',
                        'inputs': ['All singleton and unordered distinct pair subsets of truth-table ids 0..15'],
                        'bounds': {'bases': 136, 'raw_formula_gates': 5, 'raw_dag_gates': 3,
                                   'raw_trees': optimized['raw_trees_checked'], 'raw_programs': optimized['raw_programs_checked'],
                                   'witnesses': optimized['witnesses_checked']},
                        'non_claims': ['No P-versus-NP result', 'No external runtime bridge',
                                       'No neural learning replacement', 'No proof-kernel verification',
                                       'Raw absence alone does not prove unbounded nonexistence']},
        'randomness': {'used': False, 'generator': '', 'seed': None},
        'run': {'started_at': started, 'runtime_seconds': time.perf_counter() - clock,
                'exit_status': 0, 'status': 'completed',
                'resource_limits': {'memory_bytes': None, 'cpu_seconds': None, 'max_cores': None, 'max_threads': None}},
        'outputs': outputs,
        'checks': ['All 136 optimized costs equal independent raw syntax minima',
                   'All 279 stored witnesses replayed by separate scalar/ancestry evaluator',
                   'Every gate truth function belongs to its stated basis',
                   'All 136 existence results agree with unchanged predecessor unary closure',
                   'Ordered truth-table orientation checked for every selected operator',
                   'Input SHA256 values unchanged before/after'],
        'result': {'outcome': 'implementation and finite assertion verified in the stated range',
                   'bases_checked': 136, 'generates_true': 93, 'does_not_generate_true': 43,
                   'histogram_formula_dag_depth': optimized['histogram_formula_dag_depth']},
        'residual_risks': ['Independent implementations and fresh agent use the same model family',
                           'Mathematical arguments are hand-reviewed, not proof-kernel checked',
                           'Hardware costs differ if fanout, wires or storage are charged'],
        'input_artifacts': artifacts, 'declared_results': [x['path'] for x in outputs],
    }
    path = ROOT / 'evidence/circuit_cost_run.json'
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(f"Verified {optimized['bases_checked']} bases, {optimized['witnesses_checked']} witnesses, "
          f"{optimized['raw_trees_checked']} trees, {optimized['raw_programs_checked']} programs.")
    print(json.dumps(optimized['histogram_formula_dag_depth'], sort_keys=True))


if __name__ == '__main__':
    main()
