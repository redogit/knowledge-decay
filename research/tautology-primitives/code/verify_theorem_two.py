"""Independent exact semantic crosscheck of all 65,536 binary-operation bases.

This is executable corroboration, not a premise of the Lean theorem. Operators
are truth-table integers with MSB-first 00,01,10,11 order. Unary functions are
00=FALSE,01=x,10=NOT x,11=TRUE. Formula/depth minima use exact integer fixed
points; shared minima use complete BFS over the eight available-function sets
containing x. No production synthesizer or hard-coded classifier shortcut is
used to obtain minima. The ordered theorem classifier is compared afterwards.
"""
from __future__ import annotations
from collections import Counter, deque
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import time

ROOT=Path(__file__).resolve().parents[1]


def scalar(op: int,a: int,b: int)->int:
    return (op >> (3-(2*a+b))) & 1


def unary(op: int,a: int,b: int)->int:
    return (scalar(op,a>>1,b>>1)<<1) | scalar(op,a&1,b&1)


# For each ordered unary pair and output, the bitmask of generating operators.
PAIR_OPS=tuple(tuple(tuple(sum(1<<op for op in range(16) if unary(op,a,b)==out)
                         for out in range(4)) for b in range(4)) for a in range(4))


def valid_mask(mask:int)->None:
    if type(mask) is not int or not 0<=mask<65536:
        raise ValueError('basis mask must be an integer 0..65535')


def tree_min(mask:int,depth:bool)->int|None:
    best=[None,0,None,None]
    changed=True
    while changed:
        changed=False
        for a in range(4):
            if best[a] is None:
                continue
            for b in range(4):
                if best[b] is None:
                    continue
                candidate=1+(max(best[a],best[b]) if depth else best[a]+best[b])
                for out,ops in enumerate(PAIR_OPS[a][b]):
                    if mask&ops and (best[out] is None or candidate<best[out]):
                        best[out]=candidate
                        changed=True
    return best[3]


def dag_min(mask:int)->int|None:
    queue=deque([(2,0)])
    visited={2}
    while queue:
        available,cost=queue.popleft()
        if available&8:
            return cost
        inputs=[i for i in range(4) if available&(1<<i)]
        outputs=0
        for a in inputs:
            for b in inputs:
                for out,ops in enumerate(PAIR_OPS[a][b]):
                    if mask&ops:
                        outputs|=1<<out
        for out in range(4):
            if outputs&(1<<out) and not available&(1<<out):
                following=available|(1<<out)
                if following not in visited:
                    visited.add(following)
                    queue.append((following,cost+1))
    return None


def minimum_costs(mask:int)->tuple[int|None,int|None,int|None]:
    valid_mask(mask)
    return tree_min(mask,False),dag_min(mask),tree_min(mask,True)


def classify(mask:int)->str:
    valid_mask(mask)
    def has(i):return bool(mask&(1<<i))
    c=any(has(i) for i in (9,11,13,15))
    n=any(has(i) for i in (8,10,12,14))
    z=any(has(i) for i in (0,2,4,6))
    l=any(has(i) for i in (10,12))
    if c:return 'row1_diagonal_true'
    if not n:return 'row2_zero_preserving'
    if has(14) or has(6) or has(7) or (l and z):return 'row3_two_gates'
    if has(8) and z:return 'row4_shared_false'
    if l and (has(8) or has(1)):return 'row5_three_gates'
    if has(8):return 'row6_nor_tree'
    return 'row7_self_dual'


def expected_costs(branch:str)->tuple[int|None,int|None,int|None]:
    return {'row1_diagonal_true':(1,1,1),'row2_zero_preserving':(None,None,None),
            'row3_two_gates':(2,2,2),'row4_shared_false':(3,2,2),
            'row5_three_gates':(3,3,3),'row6_nor_tree':(5,3,3),
            'row7_self_dual':(None,None,None)}[branch]


def main()->None:
    start=datetime.now(timezone.utc).isoformat()
    tick=time.perf_counter()
    source=Path(__file__).resolve()
    before=hashlib.sha256(source.read_bytes()).hexdigest()
    branches=Counter()
    profiles=Counter()
    stream=hashlib.sha256()
    for mask in range(65536):
        actual=minimum_costs(mask)
        branch=classify(mask)
        expected=expected_costs(branch)
        if actual!=expected:
            raise RuntimeError(f'Theorem2 disagreement for mask {mask}: {actual} != {expected}')
        branches[branch]+=1
        profiles[str(actual)]+=1
        stream.update(mask.to_bytes(2,'big')+bytes(255 if x is None else x for x in actual))
    after=hashlib.sha256(source.read_bytes()).hexdigest()
    if before!=after:
        raise RuntimeError('Crosscheck source changed during run')
    result={'schema':'fig22-theorem2-all-bases-crosscheck-v1','started_at':start,
            'runtime_seconds':time.perf_counter()-tick,'status':'verified','exit_status':0,
            'basis_masks':{'first':0,'last':65535,'population':65536,'bits':'bit i selects ordered truth table i'},
            'ordered_truth_inputs':['00','01','10','11'],'unary_encoding':['FALSE','x','NOT x','TRUE'],
            'methods':['exact integer formula fixed point','exact integer depth fixed point',
                       'complete available-unary-function BFS for shared gates'],
            'classifier':'First matching row of Theorem2; compared after independent minima',
            'branch_counts':dict(sorted(branches.items())),'cost_profiles':dict(sorted(profiles.items())),
            'disagreements':0,'profile_stream_sha256':stream.hexdigest(),
            'stream_encoding':'For ascending mask: 2-byte big-endian mask then F,G,D each one byte; unreachable=255',
            'source':str(source.relative_to(ROOT)),'source_sha256_before':before,'source_sha256_after':after,
            'claim_ceiling':'Independent executable corroboration; not a premise of the Lean kernel proof.'}
    path=ROOT/'evidence/theorem_two_crosscheck.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('All 65536 bases agree with Theorem2. No disagreements.')
    print(json.dumps(result['cost_profiles'],sort_keys=True))


if __name__=='__main__':
    main()
