# Theorem 2 — all binary Boolean bases, kernel checked

Status: **Lean 4.35.0 kernel proved**, 2026-10-28. This completes the earlier
hand-only arbitrary-basis classification and its supporting Boolean factors.

## Statement to remember

Choose any basis B from the sixteen total binary Boolean operations, including
the empty basis. Use variable leaves, no primitive nullary constants, unit-cost
binary gate applications, free wires/fanout, and ordered or tied gate pins.
Binary TRUE/FALSE operations still cost one application. The variable collection
is nonempty. Circuits are finite and acyclic.

F(B) is minimum formula-tree gate occurrence count for constant TRUE.
G(B) is minimum distinct reachable DAG gate count. D(B) is minimum depth;
the theorem establishes the same optimum for formula depth and DAG depth.
These quantities are minimized separately.

Define:

- C = {XNOR, x⇒y, y⇒x, binary TRUE}.
- N = {NOR, NAND, NOT_X, NOT_Y}.
- Z = {binary FALSE, x AND NOT y, NOT x AND y, XOR}.
- L = {NOT_X, NOT_Y}.

NOT_X and NOT_Y are binary functions ignoring one pin. Every truth table keeps
ordered inputs 00,01,10,11. Apply the rows **in order**; each row includes the
failure of every preceding row.

| First matching condition | Exact (F,G,D) |
| --- | --- |
| B meets C | (1,1,1) |
| B does not meet N | Impossible |
| B contains NAND, XOR or OR; or meets both L and Z | (2,2,2) |
| B contains NOR and meets Z | (3,2,2) |
| B meets L and contains NOR or AND | (3,3,3) |
| B contains NOR | (5,3,3) |
| Otherwise | Impossible |

“Impossible” excludes every allowed finite formula and DAG, without a search
cutoff. “Exact” includes both an attaining witness and a lower bound for every
allowed finite object.

Consequences now also proved in Lean:

1. Every reachable basis has exactly one of the five displayed optimum profiles.
2. Minimum formula size four never occurs: `no_formula_four`.
3. Minimum shared size equals minimum formula depth and minimum DAG depth.
4. Whenever TRUE is generable, F≤5 and G,D≤3.
5. Minimum values are unique. The selected branch depends on operation membership,
   preserving its meaning under basis reordering or repeated entries.
6. Arbitrary predicate-defined subsets and arbitrary raw binary Boolean functions
   are covered; a supplied numeric list or membership algorithm is not required.

## Exact formal entry points

All names below have prefix `FIG22.Basis.TheoremTwo` unless otherwise specified.

| Obligation | Lean theorem |
| --- | --- |
| Full arbitrary operation-list classification | `theorem_two` |
| Classifier equivalent to all ordered row premises | `classify_iff`, `branch_complete`, `ordered_row` |
| Every mathematical subset of numeric operations | `theorem_two_subset`, `mem_basisOf` |
| Every list of raw functions Bool→Bool→Bool | `theorem_two_raw` |
| Every predicate-defined subset of raw functions | `theorem_two_raw_subset` |
| All five reachable profiles or impossibility | `complete`, `complete_raw` |
| No minimum formula size four | `no_formula_four`, `no_formula_four_raw` |
| Sharp finite upper bounds and attaining minima | `every_reachable_cost`, `every_reachable_cost_raw` |
| Shared optimum equals either depth optimum | `shared_equals_depth`, `shared_equals_dag_depth` and raw variants |
| All binary functions represented, both inverses | `FIG22.Basis.binaryFunction_bijection` |

The raw predicate theorem states its conclusion directly about admissible
function-labelled formulas and DAGs. Its hypothesis is only a chosen variable
x:α and a mathematical predicate on binary functions. Classical subset
normalization is a mathematical representation, not a runtime oracle for an
arbitrary undecidable predicate.

## Supporting proof factors

| Factor | Kernel-checked mechanism |
| --- | --- |
| Complete operator representation | Inverse maps between Fin16 and every total Bool→Bool→Bool function |
| Ordered truth-table convention | Four input positions and encoding weights 8,4,2,1; both off-diagonal positions retained |
| Four diagonal classes | Diagonal FALSE/x/NOT x/TRUE partition and exact operation memberships |
| Obstructions | Zero-preserving and self-dual characterizations; closed unary state sets |
| Unbounded tree lower bounds | Local potential certificates, restricted from maximal allowed bases, then structural induction |
| Unbounded DAG lower bounds | Unfolding preserves depth; depth≤distinct reachable ancestors |
| Upper bounds | Existing checked singleton/pair witnesses transfer by operation membership |
| All branch conditions | Preceding failures formally imply the required maximal-basis restrictions |
| Source and gate identities | Labels change under representation adapters; source names, indices, ordered references and output ancestry are retained |
| Raw representation transport | Both directions preserve admissibility, semantics, tautology, occurrence size, depth and reachable gate count |
| Mathematical subsets | Predicate-to-list normalization with membership equivalence; no supplied-list restriction |
| Consequences | Classification plus uniqueness of each independently minimized quantity |

The local lower-bound certificates use weights in unary order
(FALSE,x,NOT x,TRUE):

| Selected finite outcome | Maximal numeric basis | Formula weight | Depth weight |
| --- | --- | --- | --- |
| (1,1,1) | All sixteen | (0,0,0,1) | (0,0,0,1) |
| (2,2,2) | All except 9,11,13,15 | (1,0,1,2) | (1,0,1,2) |
| (3,2,2) | 0,1,2,3,4,5,8 | (1,0,1,3) | (1,0,1,2) |
| (3,3,3) | 1,3,5,8,10,12 | (2,0,1,3) | (2,0,1,3) |
| (5,3,3) | 1,3,5,8 | (2,0,1,5) | (2,0,1,3) |

The blocked cases use maximal bases 0..7 with closed states {FALSE,x}, and
{3,5,10,12} with closed states {x,NOT x}. Every local certificate and its
application to the actual ordered branch is proved in Lean. No appeal to the
Python all-basis crosscheck is needed for the universal theorem.

## Verification and reproduction

The complete project compiles twelve modules from fresh output directories.
All 926 public theorem axiom audits passed. No sorry/admit, project-added axioms,
unsafe declarations or native_decide are permitted. The dependency union is
only standard Lean propext, Quot.sound and Classical.choice.

Four deliberately false controls must be rejected **because decide proves the
proposition false**. Import failures or unrelated compilation errors cannot count
as a successful negative control. The added controls challenge the empty-basis
branch and the NOR+FALSE sharing branch.

From research/tautology-primitives:

```bash
python code/verify_lean_proofs.py --lean /path/to/lean
python -m unittest discover -s tests -v
python code/verify_theorem_two.py
```

The last command independently crosschecks every membership mask0..65535 using
exact formula/depth fixed points and available-function DAG BFS. Its result is
corroboration, with a deterministic digest of all computed profiles; Lean is
the proof authority. No random sampling is used.

Actual artifacts:

- `evidence/lean_verification.json`: proof scope, all theorem identities, commands,
  compiler/kernel hashes, runtime compatibility source and input/output hashes.
- `evidence/lean_proofs.log` and `evidence/lean_axiom_audit.lean`: compile, axiom
  and false-control output plus replayable audit source.
- `evidence/theorem_two_crosscheck.json`: all 65,536 executable comparisons.
- `THEOREM_TWO_REVIEW.md`: independent statement/model review and exact source hashes.

The theorem concerns constant-TRUE generation in the explicitly defined binary
Boolean model. Recognition of arbitrary tautologies, functional completeness,
weighted physical hardware, higher-arity gates and multi-output objectives are
different mathematical obligations and are not assumptions in its proof.
