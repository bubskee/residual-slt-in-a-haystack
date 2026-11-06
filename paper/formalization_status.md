# Formal verification coverage

Proof source: [dfd9f7ee8c4338256a7cb7426ceaae7a038fbf00](https://github.com/bubskee/residual-slt-in-a-haystack/tree/dfd9f7ee8c4338256a7cb7426ceaae7a038fbf00).
Lean `v4.35.0`; mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The release preserves the audited Lean source byte for byte. No Lean theorem was added or changed by the manuscript polish. Integrability thresholds and boundary divergence for the identity target are formalized; the manuscript's multiplicities, Laplace asymptotics, arrangements, coercivity, and global selection have paper proofs only.

## Exact formal assumptions

The relevant namespace is `ResidualSLT`. `networkPopulationLoss μ r w` is the actual integral of the squared identity-target error of the raw-weight residual recursion, not a postulated comparison model. `network_raw_step` identifies the recursion; `network_squaredError_integrable` proves input integrability before `network_loss_eq_gram` identifies its coefficient quadratic form.

- Degree `r : ℕ`, with `2 ≤ r` and `Even r` for the even theorem, or `3 ≤ r` and `Odd r` for the odd theorem.
- Depth `L : ℕ`, `0 < L`. Depth one is included.
- Input `μ : Measure ℝ`. No probability normalization is required by Lean.
- `FinitePositiveFeatureGram μ (networkFeatures r L)`: every pairwise product of the features is integrable, and their integral Gram matrix is positive definite.
- **The formal features are the contiguous basis** `x^r, x^(r+1), …, x^(r^L)`, indexed by `Fin (r^L + 1 - r)`. The paper assumes only the sparse basis `x^(1+j(r-1))`. For `r>2` this is a genuine hypothesis difference, not an equality of statements. The paper's sufficient condition (probability law with infinite support and finite absolute moment of order `2r^L`) implies both assumptions by an ordinary argument; this sufficient-condition implication is not being claimed as a new Lean certificate.
- Radius `ε : ℝ`, `0 < ε`, `ε ≤ 1`.
- Raw parameter domain `Metric.ball (0 : Fin L → ℝ) ε` with the standard maximum norm. `parameter_ball_eq_cube` proves that this is exactly `(-ε,ε)^L`.
- Prior `p : (Fin L → ℝ) → NNReal`, globally measurable and finite-valued, with finite upper and strictly positive lower bounds almost everywhere on the ball. This is `BoundedPositivePriorOn p (ball 0 ε) volume`. Outside the ball there are no density bounds. Smoothness, normalization, and a product density are not assumed.
- Parameter measure is `volume.withDensity (fun w => (p w : ENNReal))`. The prior is outside the negative loss power.

For every real `s`, the principal odd theorem concludes

```text
IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s))
  (ball 0 ε) (volume.withDensity (fun w => (p w : ENNReal)))
  ↔ s < if L < r then L/(2*r)
        else if L = r then 1/2
        else (L+r)/(4*r).
```

The even theorem has right side `s < L/(2*r)`. The corresponding non-integrability declarations include equality and every larger `s`.

`HasIntegrabilityThresholdOn` separately includes almost-everywhere strict positivity of the loss and the iff criterion for every nonnegative real exponent. This excludes an artifact from Lean's totalized real powers at zero. The iff declarations above cover all real exponents and are stronger on that point.

## Correspondence

| Manuscript assertion | Existing declarations | Scope |
|---|---|---|
| Theorem 1: actual squared-error reduction | `signed_network_certificate`, `signed_network_loss_comparison`; `network_squaredError_integrable`, `network_loss_eq_gram` | Kernel-checked under the contiguous Gram assumption; comparison on the radius-one max-norm ball |
| Theorem 1: even identity threshold | `even_network_prior_integrableOn_iff`, `even_network_certificate` | Kernel-checked for all positive depths and even `r ≥ 2` |
| Theorem 1: odd identity threshold | `odd_network_prior_phase_transition`, `odd_network_prior_integrableOn_iff`, `odd_network_certificate` | Kernel-checked for all positive depths and odd `r ≥ 3` |
| Identity boundary divergence | `even_network_prior_not_integrable`, `odd_network_prior_not_integrable` | Kernel-checked, including all exponents above the boundary |
| Prior-weighted Lebesgue form | `even_network_prior_weighted_integrableOn_iff`, `odd_network_prior_weighted_integrableOn_iff` | Kernel-checked, density outside the loss power |
| Whole-neighborhood odd assembly | `cancellationModel_integrable_of_angular`, `cancellationModel_angular_of_integrable`, `odd_cancellationModel_all_depths_integrableOn_iff` | Kernel-checked; signed pivot cones, finite union, origin, and low depths handled |
| Actual chart-image containments and unused coordinates | `TransverseChart.image_subset_cylinder`, `TransverseChart.exists_inner_cylinder`, `angularCylinder_integrable_iff` | Kernel-checked in `AngularIntegration.lean`; no global sphere chart or rectangle equality is assumed |
| Actual-loss divergence witness | `signed_network_prior_necessary_of_interior_zero`, using `signed_network_prior_transverse_cone_iff` | Kernel-checked; for depths at least three an interior angular zero is constructed. Depths one and two use a radial necessity argument |
| Theorem 1: multiplicity, Laplace rate, coercivity/global integral | No end-to-end certificate of these claims | Paper proof only |
| Theorem 2: arbitrary-active-count local arrangement | No certificate | Paper proof only; `active_factor_relation`, `active_family_independent`, and `two_direction_degree_gaps` cover limited algebraic ingredients, not the full theorem |
| Table 1 and Theorem 3: nonidentity local/global pairs | No certificate of the stated analytic results | Paper proof and exact arithmetic checks only |

The partial algebraic declarations do not certify the full family of active/group directions, its differential identification, the uniform remainder bound, the nonidentity loss comparison, or its integration. The `active_family_independent` declaration is an extension lemma, not a certificate of the manuscript's complete inductively indexed family.

## Build and focused audit

From the repository root:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false ../paper/checks/IdentityAudit.lean
```

The release verification reran the build from an isolated copy of the pinned proof source, using the pinned mathlib checkout and existing dependency build cache. The build completed successfully (3583 jobs); the strict focused audit passed. See `checks/lean-build.txt` and `checks/IdentityAudit.txt`.

`checks/IdentityAudit.lean` prints the types and axiom dependencies of exactly nine declarations: the five principal declarations and four supporting declarations enumerated in Appendix E. Each axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`. This is a focused nine-declaration audit, not a fresh audit of every declaration in the library.
