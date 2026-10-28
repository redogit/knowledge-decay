# Minimum TRUE-generation costs — FIG-22

Date: 2026-10-27. Scope: pure, finite Boolean circuits over binary operations,
variable inputs, no primitive nullary constants. This extends the completed
classification; it does not reopen it. Source baseline:
`redogit/knowledge-decay@67053880df1ab44833d55e4cf685b8d8ead1d84c`.

## 1. Models and exact statement

Fix a basis B of binary truth functions. Truth vectors always list outputs on
ordered inputs **00, 01, 10, 11**. Both pins of a gate may use the same source.
Inputs are variables, not charged gates. Gates have unit cost even when their
binary truth function ignores a pin or is constant valued. In particular,
the binary operation TRUE costs one gate; there is no free TRUE source.

| Quantity | Definition | Free structure / restriction |
| --- | --- | --- |
| Formula size F(B) | Minimum number of gate **occurrences** in a rooted binary tree computing TRUE | Variable leaves may repeat; internal subtrees are copied at each use |
| Shared size G(B) | Minimum number of reachable gate **nodes** in an acyclic, single-output circuit computing TRUE | Wires, fanout and tied pins are free; reachable gates are charged once |
| Depth D(B) | Minimum maximum number of gates on an input-to-output path | Inputs have depth 0; gate depth is 1 + max of its input depths |
| Reuse | Two or more pin incidences referencing one immutable node | Reuse does not mean equal strings, equal current values, or an unverified semantic equivalence |
| Source identity | Declared (identifier, revision) of a symbolic input; a gate has an occurrence position and ordered source references | Distinct source keys remain independent variables unless an explicit mathematical substitution is made |

These are separately minimized quantities, not a claim that arbitrary
area/depth tradeoffs disappear. The witnesses below happen to achieve all
three singleton minima. Dead gates do not count in a single-output cost.
Total allocated gates and reachable gates can differ. We count gate depth,
not physical delay, energy, source storage, wire length or fanout buffers.

**Theorem 1 (singleton minimum costs).** Over any finite nonempty collection
of variable symbols, with repeated symbols permitted, the exact minima are:

| Basis | Ordered truth vector | Formula gates F | Shared gates G | Minimum depth D | Leaves in a minimum formula |
| --- | --- | ---: | ---: | ---: | ---: |
| NOR | 1000 | 5 | 3 | 3 | 6 |
| NAND | 1110 | 2 | 2 | 2 | 3 |
| XNOR | 1001 | 1 | 1 | 1 | 2 |
| Y_IMPLIES_X | 1011 | 1 | 1 | 1 | 2 |
| X_IMPLIES_Y | 1101 | 1 | 1 | 1 | 2 |
| binary TRUE | 1111 | 1 | 1 | 1 | 2 |

Leaves = F+1 because these formulas are full binary trees, including gates
whose semantics ignore a pin. Counting leaves or all tree vertices would
therefore be a different numerical size convention.

## 2. Cost-preserving unary reduction

Let C(x1,...,xn) compute TRUE for every Boolean valuation. Substitute the
same symbolic variable x for every input symbol, without simplifying or
merging gate occurrences. Then C(x,...,x) is TRUE on x=0 and x=1.

The substitution preserves every internal gate, its label, ordered pins,
gate-to-gate references, formula occurrence count and path depth. In a DAG,
one may retain distinct input occurrences interpreted by the same x. If an
implementation instead merges input vertices, source-vertex topology changes;
the internal gate count and gate depth still do not. No claim of preserving
distinct runtime source identities is needed or made by this substitution.

Thus every multivariable witness gives a unary witness of the same costs.
Every unary witness is also allowed in the original model. The three
minimum costs are therefore equal to their unary minima. For depth this
also holds between trees and DAGs: unfolding shared nodes preserves depth,
though it can increase size. This argument applies to every binary basis.

It does **not** apply to obligations requiring all input symbols to occur
distinctly, read-once formulas, prescribed dependence on every input, unsafe
physical signal identification, or independent random rather than symbolic
inputs. A tautology need not depend semantically on any of its inputs.

## 3. Witnesses and hand proofs of minimality

Write N(a,b)=NOT(a OR b) and A(a,b)=NOT(a AND b).

### NOR

The shared witness is the straight-line program

```text
n := N(x,x)       # NOT x, depth 1
z := N(x,n)       # FALSE, depth 2
t := N(z,z)       # TRUE, depth 3; both pins reference the SAME z
```

Exactly three gates are reachable. Its tree unfolding is

```text
N( N(x,N(x,x)), N(x,N(x,x)) )
```

with 1+2+2=5 gate occurrences. The two appearances of the FALSE subtree
are distinct occurrences in the tree, with the same derivation.

**Lemma (FALSE cost).** A zero-gate unary formula is x. The only one-gate
NOR formula is N(x,x)=NOT x. Neither is FALSE. The term N(x,N(x,x)) is
FALSE, so its minimum tree size, shared size and depth are all 2. Depth 1
cannot generate FALSE, since every gate then has only variable pins and
identification reduces it to N(x,x).

If N(U,V) is identically TRUE, both U and V are identically FALSE:
at each valuation, NOR returns 1 only on the ordered input pair 00.
In a tree each child therefore costs at least two gates independently,
giving F >= 1+2+2=5. A circuit producing TRUE must first have computed
FALSE at a gate earlier than its TRUE output; FALSE needs at least two
gates, so G >= 3. Each FALSE child has depth at least 2, hence D >= 3.
The displayed witnesses attain every bound. This is a lower-bound proof,
independent of the enumeration below.

### NAND

The witness A(x,A(x,x)) has two gate occurrences, two shared gates and
depth 2. Its inner gate is NOT x; the outer is NOT(x AND NOT x)=TRUE.
The zero-gate term x is not TRUE. Every one-gate unary NAND term is
A(x,x)=NOT x, also not TRUE. By the reduction, no multivariable
zero/one-gate circuit or depth-1 circuit can improve the bound. Thus
F=G=D=2.

### XNOR, the two implications, and binary TRUE

For each of these four operations h, h(0,0)=h(1,1)=1, so h(x,x) is TRUE
with one gate and depth 1. A variable leaf is not a tautology, excluding
zero gates and depth 0. Thus F=G=D=1. For binary TRUE the pin values are
irrelevant, but its application still costs one gate.

## 4. Composed bases: exact small-domain results

We checked **all 16 singleton and 120 distinct unordered pair bases**,
including bases that contain non-generating singleton operators. The
completed existence classification remains 93 generating and 43 blocked.
The cost refinement is:

| (F,G,D) | Number of singleton/pair bases | Evidence |
| --- | ---: | --- |
| (1,1,1) | 58 | Explicit witnesses; exact recurrences and raw syntax agree |
| (2,2,2) | 24 | Same |
| (3,2,2) | 3 | Same; composed-basis sharing gain |
| (3,3,3) | 4 | Same |
| (5,3,3) | 4 | Same; NOR sharing gain retained |
| unreachable | 43 | Prior obstruction proof plus complete unary closure; raw bounds alone do not prove nonexistence |

There is no formula optimum 4 **in this singleton/pair population**.
No empirical claim about larger bases or other arities follows merely
from this finite count. The analytical extension below has its own proof.

The three additional pairs with a sharing gain are exactly

| Basis with NOR | One-gate FALSE term Z(x) | Minimum formula | Shared witness | (F,G,D) |
| --- | --- | --- | --- | --- |
| binary FALSE (0000) | FALSE(x,x) | N(Z(x),Z(x)) | z:=Z(x); t:=N(z,z) | (3,2,2) |
| X_AND_NOT_Y (0010) | x AND NOT x | N(Z(x),Z(x)) | Same | (3,2,2) |
| NOT_X_AND_Y (0100) | NOT x AND x | N(Z(x),Z(x)) | Same | (3,2,2) |

**Hand lower bound for these pairs.** One gate gives either NOT x (NOR)
or FALSE (the other operation), never TRUE. A two-gate formula has a
root and exactly one gate child; its other child is x. NOR cannot give
TRUE with the nonconstant child x, regardless of pin order. The other
operation, on the possible pairs (x,FALSE), (FALSE,x), (x,NOT x),
(NOT x,x), gives respectively (x,FALSE,x,NOT x) for a AND NOT b,
(FALSE,x,NOT x,x) for NOT a AND b, or four FALSEs for binary FALSE.
These are all possible root cases because a one-gate child is FALSE
or NOT x. None is constant TRUE.
Hence F>=3. The same one-gate exclusion gives G,D>=2; witnesses attain
the bounds. This checks the ordered mixed cases, not a lossy XOR class.

NOR with AND, first projection X, or second projection Y retains (5,3,3).
For AND+NOR, no tree with fewer than two gates is FALSE. A minimum TRUE
tree cannot end in AND: both children would themselves be smaller TRUE
trees. It must end in NOR, requiring two FALSE children of size at least
2, so F>=5. Projections cannot improve a minimum term because removing
a projection root and retaining its selected child reduces size and does
not increase depth. The NOR witnesses therefore give the matching bounds.

Composing gates can also improve generation without producing any
tree/DAG gap. For example OR(x,NOR(x,x)) is TRUE in two gates/depth 2;
OR alone does not generate TRUE. The full per-basis records preserve such
distinctions rather than treating all improvements as reuse.

### Analytical extension to arbitrary sets of binary operations

**Theorem 2.** Let B be any subset of the sixteen total binary Boolean
operations, including the empty set. The following ordered rules give
all three minimum costs. Each row assumes all preceding rows failed.
The full ordered classification and its supporting factors are now Lean 4.35.0
kernel proved; see [Theorem 2 and its proof map](THEOREM_TWO.md). The earlier
136-base evidence remains preserved, with a separate all 65,536-basis crosscheck.

Define C={XNOR, X_IMPLIES_Y, Y_IMPLIES_X, TRUE},
N={NOR, NOT_X, NOT_Y, NAND}, L={NOT_X, NOT_Y}, and
Z={FALSE, X_AND_NOT_Y, NOT_X_AND_Y, XOR}. Here NOT_X and NOT_Y
are still binary operations that ignore one pin.

| First matching condition | (F,G,D) |
| --- | --- |
| B meets C | (1,1,1) |
| B does not meet N | unreachable |
| B contains NAND, XOR or OR; or B meets both L and Z | (2,2,2) |
| B contains NOR and meets Z | (3,2,2) |
| B meets L and contains NOR or AND | (3,3,3) |
| B contains NOR | (5,3,3) |
| Otherwise | unreachable |

**Proof.** The sixteen truth tables split by their diagonal into C
(constant TRUE), N (NOT x), Z (constant FALSE), and
{AND,X,Y,OR} (x). Thus the first row follows from one gate.
After excluding C, absence of N means every operation is 0-preserving,
so no composition can be TRUE.

Suppose N is present and C absent. A first gate can produce only x,
FALSE or NOT x. A two-gate formula has one gate child and one leaf x.
If the first gate is x, the root reduces to a diagonal already considered.
If the child is FALSE, a root applied to (x,FALSE) or (FALSE,x) can
give TRUE only if it is NAND or the appropriate negated projection.
If the child is NOT x, a root applied to (x,NOT x) or its reverse can
give TRUE only for NAND, XOR or OR. These statements follow directly
from the four ordered root entries and exhaust the sixteen operations.
The third-row conditions are therefore necessary and sufficient for
two-gate formulas. They also yield depth 2 and a two-gate DAG.

If that row fails, a two-gate DAG has just one additional possibility:
both root pins reuse the first gate. Its value can be x, FALSE or NOT x.
A diagonal TRUE root is absent. A diagonal x root cannot create TRUE;
a diagonal NOT x root can do so only by negating a first-gate FALSE.
That requires N and Z. The third row already excludes NAND and L+Z,
so the only remaining case is NOR+Z, row four. It has shared witness
z:=Z(x,x); t:=NOR(z,z), and formula witness duplicating z. Hence
the costs are exactly (3,2,2).

After these rows fail, no Z-gate is present (N is either NOR or a
negated projection), and NAND, OR and C are absent. Available one-gate
values are therefore x and NOT x. No operation remaining can give TRUE
from any two of these values: AND and NOR give FALSE on the complementary
pair, while projections and negated projections stay nonconstant.
Consequently depth 2 is impossible, even with arbitrarily many parallel
gates, and a two-gate DAG is impossible. If L is present together with
AND or NOR, negate the FALSE expression AND(x,NOT x) or NOR(x,NOT x).
This gives a three-gate formula and DAG of depth 3, proving row five.
The ignored pin of the negated projection is supplied by the free leaf x.

In the remaining NOR case, B is a subset of {NOR,AND,X,Y}; the TRUE-root
argument already given forces two FALSE subtrees of at least two gates
each. The NOR witness proves (5,3,3). If NOR is also absent, only
projections and negated projections remain; their unary closure stays
within {x,NOT x}. This proves the final unreachable case. All operations
have now been accounted for. In particular formula optimum 4 never
occurs for **any binary basis in this model**, by this proof rather than
by extrapolating the 136-case table.

## 5. Why the exhaustive algorithms cover the claimed domain

### Optimized exact algorithms

The unary domain consists of precisely x, NOT x, FALSE and TRUE. For a
basis operation h and unary values u,v, compute h(u,v) coordinatewise
on x=0 and x=1, retaining ordered arguments.

For formula size, initialize cost(x)=0 and other costs to infinity, and
relax cost(h(u,v)) by 1+cost(u)+cost(v) to a fixed point. Every finite
cost has a concrete term witness. Structural induction shows every term
is represented; a minimal term's children may be replaced by minima
without increasing size. For depth use 1+max(depth(u),depth(v)).

For DAG size, breadth-first search starts with available functions {x}.
A transition applies one basis gate to any ordered available pair and
adds its result. It costs one. A minimum unary DAG never needs to
compute a unary function already available: rewire its consumers to
the earlier equal function and remove the redundant gate. This is
valid for pure extensional Boolean semantics. It does not merge
runtime identities or provenance records. The earliest occurrence is
earlier than every rewired consumer, so no cycle is introduced.
There are four unary functions; a useful program adds at most three
new functions. BFS therefore gives an exact unbounded unary gate minimum,
not a heuristic stopped after an arbitrary search budget.

The finite-state projection is used for **synthesis**, while concrete
witness plans retain each node's source references and occurrence.

### Independent raw syntax countercheck

`code/raw_circuit_enumerator.py` imports no production synthesizer,
operator factory, or evaluator. It implements scalar truth functions
by bit indexing, and retains every semantic duplicate in its lists.

For each basis of size b it visits every ordered binary tree of k gates
for k=0,...,5: Catalan(k)*b^k trees. It separately visits every ordered-pin
straight-line program of k gates for k=0,...,3: (k!)^2*b^k programs,
with one input x and the last gate as output. Any minimum single-output
DAG has no dead gates and admits a topological order ending at its
output; thus these programs include all cheaper alternatives to the
at-most-three-gate witnesses. Extra dead gates are retained in the
enumerator, not silently pruned.

Totals across all 136 bases: **195,320 trees and 37,512 programs**, including
the zero-gate case for each basis. For NOR alone the tree populations are
1,1,2,5,14,42, and the program populations are 1,1,4,36. No NOR tree
through 4 gates or program through 2 gates produces TRUE. Any circuit
of depth at most 2 unfolds to a tree with at most 3 gates, also covered;
this excludes all depth improvements to the depth-3 witnesses.

The mathematical reduction, coverage proof, lower bounds, and exact
enumerations jointly establish the stated costs. Passing software tests
alone is not substituted for those arguments. The October 27 checkpoint
provided hand proofs with executable verification. On October 28, the six
singleton and all 136 singleton/pair cost results additionally passed Lean 4.35.0
kernel verification; see [the formal proof scope and reproduction](formal/README.md).
A subsequent twelve-module checkpoint also kernel-proves Theorem 2 for every
binary basis and all supporting representation factors; see THEOREM_TWO.md.

## 6. Validated local interface and architecture boundary

The local interface is an immutable source-aware `CircuitPlan`: declared
`InputSource(identifier, revision)` records, a topological list of
`CircuitGate(operator, left, right)` records and an output reference.
Sources precede gates in the integer reference space; pins are ordered.
The evaluator checks the complete ordered valuation space of the declared
sources, records gate traces, and reports reachable gate count, unfolded
formula size, depth and syntactic source support. Support here means
structural ancestry, not semantic influence: TRUE can have structural
inputs while depending on none of their values.

Tests check source/revision retention, immutable detached plans, serialization
round trips, malformed references, tied pins, full truth-vector orientation,
unreachable/dead gates, and the explicit source-count evaluation bound.
The counterprobe x IMPLIES y has vector 1101 on two independent sources;
x IMPLIES x is constant TRUE. Equal observed source values therefore
never justify identifying their symbolic identities.

This supplies one tested local structural reasoning primitive: construct
a concrete plan, retain its dependency references, evaluate its stated
Boolean semantics, and compare tree-versus-reuse costs. The source-aware
plan is a local schema, not an authenticated Horizon/SCDL or Episteme
schema. [FIG-23](https://linear.app/fighting-decay-of-knowlege/issue/FIG-23)
still requires the authoritative target revision and schema, versioned
operation identities, budgets/failure semantics and cross-language replay.
No cross-runtime binding is claimed by this extension.

```text
TAUTOLOGY_GENERATION != TAUTOLOGY_RECOGNITION
GENERATES_TRUE != FUNCTIONAL_COMPLETENESS
EXTENSIONAL_EQUALITY != SOURCE_IDENTITY
VALIDATED_LOCAL_PLAN != EXTERNAL_RUNTIME_INTEGRATION
FINITE_CIRCUIT_COST_RESULT != P_VS_NP_RESULT
BOOLEAN_CIRCUIT_SYNTHESIS != GENERAL_REASONING_OR_LEARNING_SYSTEM
```

An operation's specified truth table is a premise, not an empirically
learned fact. These circuits implement known Boolean functions. The
results establish neither a replacement for neural-network learning nor
an algorithm for recognizing arbitrary tautologies in polynomial time.

## 7. Remaining generalization bucket: cost under stronger obligations

The finite singleton/pair, unit-cost, single-output TRUE question above
is settled. The next bucket changes an explicitly named obligation:

* **Multiple required outputs.** Objects: one source-aware DAG and a list
  of target truth vectors. Relation: shared intermediate dependencies.
  Question: minimum joint gate count versus separately optimized outputs.
  Independent unary lower bounds need not add, because outputs can share.
* **Gate weights and physical fanout.** Objects: weighted gate and wire
  model. Assumptions must specify buffers, storage, pin and source costs.
  Question: when does the NOR FALSE-reuse witness still reduce total cost?
  Failure mode: the free-fanout theorem is applied to charged hardware.
* **Higher arity.** The proof of unary reduction still applies to ordinary
  Boolean terms, but the explicit rules of Theorem 2 use binary truth
  tables. Minimum-cost classifications for higher-arity bases need a new
  statement and proof. No binary histogram becomes an all-arity classification.
* **Specified nonconstant functions.** Objects: n-input target functions
  and circuits that retain their distinct sources. Identifying all inputs
  now loses required information. Complexity can no longer be inferred
  from the four unary states. Generation and recognition remain distinct.
* **Architecture admission.** Required evidence: a versioned external
  contract and positive, negative, stale-revision, mutation, zero-budget
  and exhausted-budget replay. Until then only the local Python interface
  is validated. Semantic reuse must never erase source lineage.

These are open obligations for future work, not conjectures asserted as
facts. No unproved conjecture is needed for Theorem 1 or the 136-base table.
Preserve this checkpoint before choosing a stronger target.

## 8. Reproduction and source custody

From `research/tautology-primitives/`:

```bash
python -m unittest discover -s tests -v
python code/cook_cycle_factories.py
python code/raw_circuit_enumerator.py --output evidence/raw_minimum_costs.json
python code/verify_circuit_costs.py
```

`evidence/minimum_costs.json` stores optimized witnesses and comparison;
`evidence/raw_minimum_costs.json` stores complete finite-layer counts;
`evidence/circuit_cost_run.json` records the actual verification command,
runtime, environment, bounds, status and input/output hashes. The verification
command regenerates both result files and checks all 136 bases against the
independent enumerator. `evidence/circuit_cost_sources.json` pins the original
repository revision, original file blob hashes, and FIG-22 checkpoint identities.
No private conversational source text is included in this public extension.
