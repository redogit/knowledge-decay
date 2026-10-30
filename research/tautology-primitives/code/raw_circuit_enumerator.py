"""Independent exhaustive *syntactic* countercheck for FIG-22.

No production synthesizer/evaluator is imported. Operator id is its displayed
four-bit truth vector, MSB first in 00,01,10,11 order. A unary value is a
two-tuple of scalar outputs on x=0 and x=1. Duplicate semantic values and
duplicate computations are deliberately retained, including dead DAG gates.

Coverage: every ordered full binary unary-leaf tree with 0..5 internal nodes;
every unary-input, ordered-pin, topological straight-line program of 0..3
gates, output at its last gate. For positive size k the population is
Catalan(k)*len(basis)**k trees and (k!)**2*len(basis)**k programs.
Any gate-minimal single-output DAG has no dead gates and a topological order
ending at its output, so these programs include all possible cheaper DAGs.
Depth <3 implies at most 3 gates after unfolding, so the tree population also
excludes all shallower alternatives to the depth-3 witnesses in this domain.
Nonexistence beyond these bounds is NEVER inferred from this program alone.
"""
from __future__ import annotations

import argparse
from itertools import combinations
import json
from math import comb, factorial
from pathlib import Path


def scalar(operator: int, left: int, right: int) -> int:
    return (operator >> (3 - (2 * left + right))) & 1


def enumerate_basis(basis: tuple[int, ...]) -> dict:
    """Enumerate the fixed finite domain above; no semantic deduplication."""
    if not basis or any(type(op) is not int or not 0 <= op < 16 for op in basis):
        raise ValueError('basis must contain integer truth tables 0..15')
    if len(set(basis)) != len(basis):
        raise ValueError('basis contains duplicate operators')
    basis = tuple(sorted(basis))
    # Each list entry denotes one concrete syntax, even when its value repeats.
    # (truth on x=0, truth on x=1, depth)
    trees = [[(0, 1, 0)]]
    layers = [{'gates': 0, 'trees': 1, 'true_trees': 0}]
    formula_min = None
    depth_min = None
    for count in range(1, 6):
        current = []
        true_count = 0
        for left_size in range(count):
            for left in trees[left_size]:
                for right in trees[count - 1 - left_size]:
                    for op in basis:
                        value = (scalar(op, left[0], right[0]),
                                 scalar(op, left[1], right[1]),
                                 1 + max(left[2], right[2]))
                        current.append(value)
                        if value[:2] == (1, 1):
                            true_count += 1
                            formula_min = count if formula_min is None else formula_min
                            depth_min = value[2] if depth_min is None else min(depth_min, value[2])
        expected = comb(2*count, count) // (count + 1) * len(basis)**count
        assert len(current) == expected
        trees.append(current)
        layers.append({'gates': count, 'trees': len(current), 'true_trees': true_count})

    # A prefix entry is the complete vector of computed gate values. Retaining
    # duplicates counts different operator/pin choices as different programs.
    programs = [((0, 1),)]
    dag_layers = [{'gates': 0, 'programs': 1, 'true_outputs': 0}]
    dag_min = None
    for count in range(1, 4):
        following = []
        true_count = 0
        for values in programs:
            for op in basis:
                for left in values:
                    for right in values:
                        value = (scalar(op, left[0], right[0]), scalar(op, left[1], right[1]))
                        following.append(values + (value,))
                        if value == (1, 1):
                            true_count += 1
        assert len(following) == factorial(count)**2 * len(basis)**count
        if true_count and dag_min is None:
            dag_min = count
        dag_layers.append({'gates': count, 'programs': len(following), 'true_outputs': true_count})
        programs = following
    return {'basis_ids': list(basis), 'truth_vectors': [f'{op:04b}' for op in basis],
            'minimum': {'formula_gates': formula_min, 'dag_gates': dag_min, 'depth': depth_min},
            'formula_layers': layers, 'dag_layers': dag_layers}


def enumerate_all() -> dict:
    rows = [enumerate_basis(tuple(b)) for size in (1, 2) for b in combinations(range(16), size)]
    histogram = {}
    for row in rows:
        key = ','.join(str(row['minimum'][k]) for k in ('formula_gates', 'dag_gates', 'depth'))
        histogram[key] = histogram.get(key, 0) + 1
    return {
        'schema': 'fig22-raw-syntax-v1',
        'assertion_tested': 'All ordered unary formula trees through 5 gates and ordered topological programs through 3 gates for all 16 singleton and 120 pair binary bases.',
        'truth_table_order': ['00', '01', '10', '11'],
        'formula_bound': 5, 'dag_bound': 3, 'bases_checked': len(rows),
        'no_semantic_deduplication': True,
        'nonexistence_ceiling': 'Missing TRUE is only absence in the stated bounds; consult mathematical obstruction proof for global nonexistence.',
        'histogram_formula_dag_depth': dict(sorted(histogram.items())),
        'rows': rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(enumerate_all(), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(result, encoding='utf-8')
    else:
        print(result, end='')


if __name__ == '__main__':
    main()
