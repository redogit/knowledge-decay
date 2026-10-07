# Application seams

Status: **public research application notes — evidence remains native to each source domain**.

This document preserves several high-value applications of the Knowledge Decay operating method without importing their evidence into the core project. The purpose is to record reusable seams: places where a broader problem reduces to a smaller explicit structure that can be tested, repaired, or falsified.

Current source check: **2026-10-07**.

## 1. Extra spatial dimensions as a Decision Field case study

A higher-dimensional candidate can be represented as

$$
G=
\{
n,\;
\text{compactification scales},\;
\text{curvature},\;
\text{topology},\;
\text{warping},\;
\text{brane/bulk assignments},\;
\text{couplings},\;
\text{cutoffs},\ldots
\}.
$$

Each experiment or observation supplies its own projection,

$$
P_i(G,\nu_i)\rightarrow O_i,
$$

with probe-local nuisance structure $\nu_i$.

The important methodological rule is not to merge models because they share one coordinate such as a radius. A Dirac bulk-neutrino model, a Majorana bulk-neutrino model, a phantom-brane cosmology, and a KK-graviton dark-matter model are different candidate objects unless a complete typed adapter establishes otherwise.

### Source-verified examples

- **IceCube large-extra-dimension neutrino search** — the IceCube Collaboration uses 10.7 years of upward-going muon-neutrino data and reports, within its model, a largest compactification-radius constraint of approximately \(R\lesssim0.17\,\mu\mathrm m\) at 90% confidence for both neutrino mass orderings. This is a direct experimental analysis of an accessible realization, not a general exclusion of extra dimensions.  
  Source: https://arxiv.org/abs/2608.29746

- **Majorana Dark-Dimension neutrinos** — a distinct model with bulk Majorana fermions is confronted with Daya Bay, KATRIN, and KamLAND-Zen data. In the stated Dark-Dimension window, beta decay supplies the strongest reported constraint and drives allowed Yukawa couplings to order \(10^{-3}\). This result must remain separate from the IceCube Dirac-bulk realization.  
  Source: https://arxiv.org/abs/2609.10668

- **Metastable dark energy on the phantom brane** — a five-dimensional induced-gravity braneworld is fit to CMB, DESI DR2 BAO, and DES-Dovekie supernova data. Its M2 branch, in which dark energy decays to dark matter, reports \(\Omega_m=0.441\pm0.038\) and \(S_8=0.733^{+0.016}_{-0.020}\) at 68% confidence and explicitly motivates a future full-shape clustering test.  
  Source: https://arxiv.org/abs/2609.39039

- **KK-graviton cascade correction** — a theoretical recalculation finds a \(q^5\)-dependent near-threshold decay rate and argues that the rapid cascade used by some earlier Dark-Dimension dark-matter models is strongly suppressed. This is a meaningful theoretical contradiction for those realizations, not an observational detection.  
  Source: https://arxiv.org/abs/2609.36234  
  Related source: https://arxiv.org/abs/2610.01825

- **Vector dark matter from \(d\ge2\) extra dimensions** — a newer construction derives KK-vector dark-matter candidates for models with at least two extra dimensions and studies their cosmological parameter space. This opens a distinct branch of the Decision Field; it does not inherit evidence from one-dimensional models.  
  Source: https://arxiv.org/abs/2610.05851

These examples illustrate the rule

$$
\boxed{\text{same vocabulary} \neq \text{same model} \neq \text{shared evidence}}.
$$

## 2. Full-shape galaxy clustering: a concrete next seam

The phantom-brane M2 branch is valuable because the source itself identifies full-shape galaxy clustering as a discriminating next test. The reported high matter density and low clustering amplitude make the growth sector informative.

A predecessor analysis of metastable dark energy **without** the braneworld already uses DESI DR1 full-shape measurements and finds that full-shape information helps distinguish the dark-energy-to-dark-matter interaction from the other decay channels.

Source: https://arxiv.org/abs/2608.01844

The bounded program is therefore:

$$
\text{freeze }G_*
\rightarrow
\text{background geometry}
\rightarrow
\text{perturbation/growth reconstruction}
\rightarrow
\text{full-shape clustering}
\rightarrow
\text{held-out geometry}.
$$

### Frozen candidate

Use one declared phantom-brane M2 candidate \(G_*\). Shared physics parameters remain fixed across the probes. A changed shared parameter creates a successor candidate and is recorded as **RETUNED**, not silently treated as the original model.

### Background projection

First compute only the background observables needed for geometry:

$$
H(z),\qquad D_M(z),\qquad D_H(z),\qquad F_{\rm AP}(z).
$$

A failure here should be localized before adding galaxy-bias or nonlinear-clustering machinery.

### Perturbation seam

The phantom-brane paper states that its numerical implementation extends the metastable-dark-energy perturbation treatment to include the braneworld. The remaining reusable research obligation is therefore **not to invent a missing interaction equation**, but to expose and independently reconstruct enough of the combined perturbation operator and implementation assumptions to support a frozen-parameter full-shape test.

The structure to recover is schematically

$$
\mathcal L_{\rm M2+brane}
[
\delta_{\rm DM},
\delta_b,
\Phi,
\Psi,
\delta\rho_x,
Q^\mu,
\text{bulk/Weyl terms},
\text{boundary assumptions}
]=0.
$$

The smallest current seam is:

> Can the combined M2 + phantom-brane perturbation dynamics be reconstructed sufficiently from the declared equations/implementation to make independent full-shape predictions without silently changing shared physics parameters?

That question is narrower and safer than assuming the operator is absent or already independently verified.

### Full-shape projection

Once the linear dynamics are independently reconstructible, compare the same frozen candidate against clustering observables such as

$$
P_0(k),\qquad P_2(k),\qquad P_4(k),
$$

while keeping residuals separated:

$$
R=
\{
R_{\rm AP},
R_{\rm growth},
R_{\rm RSD},
R_{\rm broadband},
R_{\rm scale}
\}.
$$

A global likelihood change is useful, but a typed residual is more informative for locating the smallest failing structure.

### Held-out high-redshift geometry

DESI DR2 Ly-\(\alpha\) full-shape work supplies a useful complementary geometry projection at \(z_{\rm eff}=2.33\), reporting an Alcock-Paczyński constraint at approximately 1% precision.

Source: https://arxiv.org/abs/2607.27410

Its validation paper is a reminder that observables from one analysis need separate admission checks.

Source: https://arxiv.org/abs/2607.27411

The general pattern is

$$
\boxed{
\text{one candidate universe}
\rightarrow
\text{many observer surfaces}
\rightarrow
\text{many independent residuals}
\rightarrow
\text{one unchanged shared parameter set}
}.
$$

## 3. Pairwise survival versus global survival

The extra-dimensions case study exposes a general error mode:

$$
\forall i\,\exists G_i
\not\Rightarrow
\exists G\,\forall i.
$$

It is easy to produce a separately tuned model for every probe. That is not cross-probe closure.

A stronger claim requires one declared \(G_*\), fixed before examining the held-out projection, together with explicit nuisance handling and adapters. Even then, survival of null tests means only **NOT_EXCLUDED under those tests**.

## 4. Representation agreement cannot create physical agreement

A carrier or translation may preserve a scientific record exactly while the scientific model remains wrong. Conversely, a lossy carrier can collapse two distinct candidate models into one apparent representation.

Therefore the application keeps three layers separate:

1. **carrier integrity** — did the representation preserve the declared record?
2. **calculation verification** — does the reported prediction follow from the declared model and inputs?
3. **physical admission** — does independent evidence justify the physical claim?

The first cannot substitute for the second or third.

## 5. Constructed-world and simulation application

The same structure is useful outside physical inference.

Let \(U\) be a larger explicit world model and let a game, simulation, visualization, or observer experience be a projection

$$
W=P_{\rm surface}(U).
$$

Different observers may receive different lawful projections of the same underlying state. The useful design rule is to keep the following separately typed:

- invariants of the constructed universe;
- replaceable machinery;
- research hypotheses borrowed for exploration;
- deliberately fictional laws;
- observer-specific information limits;
- immutable or reconstructible history;
- residuals produced when a projection fails its stated rules.

This permits a constructed world to reuse the **method** of scientific model comparison without borrowing scientific evidence. A fictional rule can be explicit and internally consistent without becoming a statement about physical reality.

## 6. Language and interpretation application

A representation of a person, object, event, or system is not its referent.

$$
\boxed{\text{MODEL} \neq \text{REFERENT}}
$$

For knowledge records, this means observations, interpretations, assumptions, and decisions should remain distinguishable. A useful minimal decomposition is:

- **observed** — what was actually available;
- **inferred** — what was concluded from it;
- **assumed** — what was supplied by the model rather than the observation;
- **acted on** — what decision depended on those layers.

This is an epistemic hygiene rule, not a psychological or moral claim.

## 7. Usefulness witness

These application notes are valuable only if they reduce future ambiguity.

A future researcher should be able to:

1. identify whether two apparently similar higher-dimensional claims refer to the same geometry;
2. detect parameter retuning before calling several probe results a common solution;
3. recover the full-shape phantom-brane seam without assuming either success or failure;
4. distinguish carrier integrity from calculation verification and physical admission;
5. reuse the one-object/many-projections pattern in simulations without transferring scientific evidence.

## Claim ceiling

This document records application seams and current source-verified examples. It does not establish a new experimental result, prove extra spatial dimensions, certify the phantom-brane model, validate a game universe as physics, or transfer authority from any cited source into Knowledge Decay.
