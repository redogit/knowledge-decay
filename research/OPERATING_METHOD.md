# Operating method

Status: **research method / editorial synthesis — not a proof of general human benefit or an implemented autonomous system**.

This document makes explicit a working method already implied by the project charter, requirement map, and proof qualifications. It is intended to keep reconstruction, experimentation, revision, and reuse aligned without strengthening the evidence status of any underlying claim.

## 1. Core loop

For a bounded task, use the following cycle:

[
\text{Thought}
\rightarrow \text{Explicit structure}
\rightarrow \text{Action}
\rightarrow \text{Observation}
\rightarrow \text{Residual}
\rightarrow \text{Smallest repair}
\rightarrow \text{Counterprobe}
\rightarrow \text{Preservation}
\rightarrow \text{Use}
]

The steps have distinct obligations:

1. **Explicit structure** — state the object, request or question, scope, assumptions, expected observable, claim ceiling, stop condition, and recovery route.
2. **Action** — distinguish chosen interventions from imposed changes in data, environment, definitions, or constraints.
3. **Observation** — record what actually occurred without rewriting it to fit the expectation.
4. **Residual** — compare expectation with observation using a type-compatible comparison. A residual need not be numeric.
5. **Smallest repair** — change the smallest structure sufficient to explain the residual. Preserve the predecessor.
6. **Counterprobe** — ask for the cheapest independent test capable of falsifying the proposed repair.
7. **Preservation** — retain lineage, evidence status, uncertainty, privacy classification, failures, and a usable way back.
8. **Use** — identify who can use the result, for what task, what it improves, what it costs or risks, and how it can be reversed or rechecked.

A successful local test raises only the claim justified by that test.

## 2. Side-to-side review

Before escalating a result vertically into a broader claim, compare it horizontally with sibling records, probes, representations, or implementations.

For siblings (A) and (B), record at minimum:

- shared invariants;
- consequential differences;
- compatible interfaces;
- contradictions or incompatible assumptions;
- unresolved remainder.

Shared structure may travel between domains. Evidence does not travel merely because two structures resemble one another.

[
\boxed{\text{RELATION} \neq \text{EVIDENCE TRANSFER}}
]

Repeated presentation of one source, dataset, or result is not independent confirmation.

## 3. Global obligations are not pairwise obligations

Pairwise compatibility does not establish whole-group compatibility.

For surviving candidate sets (G_i),

[
\forall i<j,\;G_i\cap G_j\neq\varnothing
]

does not imply

[
\bigcap_i G_i\neq\varnothing.
]

Likewise,

[
\boxed{\forall i\;\exists\theta_i\;\;\not\Rightarrow\;\;\exists\theta\;\forall i}
]

A different parameter choice for every test is not one shared solution. When a task requires one object, model, configuration, or parameter set to satisfy all obligations, the shared object must remain frozen across those obligations unless a change is explicitly recorded as a successor model.

Unknown membership remains **UNKNOWN**, not exclusion.

## 4. Preserve, verify, admit, and satisfy the question separately

Four questions must remain separate:

1. **Preservation:** did the record arrive unchanged?
2. **Verification:** does the reported result follow from the declared inputs and procedure?
3. **Obligation:** does the verified calculation answer the question that was actually required?
4. **Admission:** does the resulting evidence justify the proposed claim?

Therefore:

[
\boxed{\text{PRESERVE} \neq \text{VERIFY} \neq \text{OBLIGATION MATCH} \neq \text{ADMIT}}
]

A correctly transported mistake is still a mistake. A correctly recomputed result may still answer a weakened or substituted question. A correct calculation does not establish the truth of its scientific premises.

This extends the existing project boundary:

[
\text{GENERATE} \neq \text{VERIFY} \neq \text{ADMIT}.
]

## 5. Representation changes must preserve consequential distinctions

Let (f:U\rightarrow V) be a common representation change over candidate objects. If (f) is injective over the distinctions that matter to the task, then for a nonempty finite family of candidate sets,

[
f\!\left(\bigcap_i G_i\right)=\bigcap_i f(G_i).
]

If the representation is lossy, distinct candidates can collapse to the same representation and create apparent agreement that did not exist before transport.

The operational rule is therefore:

> Preserve every distinction required by the obligation, or make the loss explicit and refuse conclusions that depend on the lost distinction.

This requirement concerns the carrier or representation. It does **not** require every physical or empirical observation to be injective; complementary ambiguous observations may still be informative when their limitations are explicit.

Byte equality, hash equality, or carrier agreement establish only the corresponding integrity property.

[
\boxed{\text{CARRIER AGREEMENT} \neq \text{INDEPENDENT VERIFICATION}}
]

## 6. One object, many projections

A useful general pattern is to keep one candidate object fixed and expose it to multiple independent projections:

[
P_i(G,\nu_i)\rightarrow O_i,
]

where (G) contains shared object or model parameters and (
u_i) contains projection-local nuisance terms.

The method is:

1. define (G) explicitly;
2. freeze shared parameters;
3. document each projection and nuisance treatment;
4. compare each prediction with its native observation;
5. preserve projection-specific residuals;
6. intersect surviving candidates only after adapter compatibility is established;
7. flag any changed shared parameter as a retuned successor rather than silently treating it as the original (G).

A nonempty intersection of null tests means **not excluded under those tests**, not detected.

This pattern is useful in scientific model comparison, software/configuration testing, scheduling, simulation, and other domains. The evidence supporting one application remains native to that application.

## 7. Models and referents remain distinct

A record, interpretation, model, category, or simulation of an object is not the object itself.

[
\boxed{\text{MODEL} \neq \text{REFERENT}}
]

Consequently, an inference about a representation should be carried back to its referent only through an explicit, justified adapter. Similarity, naming, shared identifiers, or convenient grouping are insufficient.

For simulations and constructed worlds, a surface may be treated as a projection of a larger explicit model,

[
W=P_{\text{surface}}(U),
]

provided real evidence, research hypotheses, and deliberately fictional rules remain separately typed. A fictional modification does not become evidence about physical reality.

## 8. Minimal repair and adversarial continuation

When a residual appears:

[
F^*=\arg\min_F\{\text{structure size}\mid F\text{ is sufficient to explain the residual}\}.
]

The expression is an operating target, not a guarantee that the true cause is uniquely identifiable.

Prefer a one-degree repair when practical: change one independently testable component, preserve the predecessor, and specify in advance what observation would count against the repair.

After a repair passes, challenge it again. A green test is evidence about the tested boundary, not a reason to stop preserving counterexamples or unresolved remainder.

## 9. Reusable record

A bounded result should be reconstructible from a record containing, where applicable:

```text
stable_id
parent_or_predecessor
native_domain
source_and_version
input_or_dataset_ids
scope
assumptions
expected_observable
observed_result
uncertainty
residual
chosen_actions
imposed_changes
smallest_suspected_failure
proposed_repair
counterprobe
competing_explanations
claim_ceiling
privacy_class
lineage
recovery_route
remainder
usefulness_witness
```

Fields that are unavailable remain explicit rather than being converted to false or null evidence.

## 10. Relationship to the requirement map

This method does not replace the eight existing requirements.

- **R-IDENTITY:** preserve object, occurrence, revision, representation, and interpretation distinctions.
- **R-UPDATE:** preserve predecessors and validate successors.
- **R-REFLECT:** expectation, observation, residual, and remainder are explicit.
- **R-PATH:** actions have conditional successors, stop conditions, and recovery.
- **R-MAP:** side-to-side relations are typed and do not transfer authority.
- **R-CLARITY:** assumptions, scope, uncertainty, and claim ceilings remain visible.
- **R-GROUP:** whole-group obligations are checked globally rather than inferred from pairwise compatibility.
- **R-LANGUAGE:** carriers and translations preserve required distinctions or declare loss.

## Claim ceiling

This document is an operating discipline assembled from current project requirements and bounded methodological work. It does not establish universal correctness, independent scientific confirmation, improved human learning, or implementation of every described check.
