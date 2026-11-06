# Formal verification coverage

Reproducibility snapshot (proof source and audit): [2865e70a9ca7f559dabfce6aa32e13cf4fc88259](https://github.com/bubskee/residual-slt-in-a-haystack/tree/2865e70a9ca7f559dabfce6aa32e13cf4fc88259).
The Lean source is unchanged from proof-source commit `3aa873960d83313e44d966ebc124655e87aa0982`.
Lean `v4.35.0`; mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Formal verification and extensions are ongoing. A growing subset of the results has been formalized in Lean 4; the repository documents the currently certified statements and their assumptions.

The current certificate covers complete raw fibers, exact cardinalities, local arrangement pairs, and global learning pairs for every degree `r ≥ 2`, positive depth, and active count. It supersedes the identity-only coverage of earlier manuscript releases. This release imports the completed Lean results without changing their proofs.

## Shared hypotheses

`ResidualSLT.unified_residual_network_certificate` constructs `UnifiedNetworkCertificate μ r L k t ρ` from:

- Natural degree `r ≥ 2` and positive depth `L`.
- An input measure `μ : Measure ℝ` with `FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)`: every retained feature product is integrable and the Gram is positive definite. The features are `x^(r+j*(r-1))`, for `0 ≤ j < (r^L-1)/(r-1)`, exactly the paper's sparse basis after reindexing. Probability normalization is unnecessary.
- A raw target vector `t : Fin L → ℝ` with `k` nonzero entries. The theorem derives `k ≤ L`; it includes the identity and all-active cases, repetitions, and every realizable sign pattern.
- A measurable density `ρ : (Fin L → ℝ) → NNReal` with finite total mass, continuous and strictly positive at every point where `networkTargetLoss μ r t` is zero. No global density bound, product structure, normalization, or tail moment is assumed.

The loss is the actual squared-error population integral of the raw-weight network. The parameter measure is `volume.withDensity ρ`; the prior lies outside the negative loss power. Fiber classification and local analytic certificates are conclusions, not hypotheses.

## Correspondence with the paper

| Paper result | Principal declaration or unified field | Certified content |
|---|---|---|
| Theorem 1: identity pair | `sparse_identity_network_rlct_laplace_certificate` | All degree/depth regimes, inverse-power iff and two-sided power/logarithmic Laplace bounds |
| Theorem 2: local arrangement | `arrangement_raw_network_rlct_laplace_certificate_of_depth_pos`; `local_certificates`, `local_at_arrangement` | Actual raw arrangements at every fiber point, exact local pair, inverse-power iff, endpoint divergence and Laplace order |
| Theorem 3: complete fibers | `network_full_raw_fiber`; `ordered_fiber`, `odd_fiber`, `even_fiber` | Equality of retained ordered effective words; raw words for odd degree, absolute-value words for even degree |
| Theorem 3: exact count | `raw_network_fiber_cardinality`; `fiber_cardinality` | `(if Even r then 2^k else 1) * L.choose k` |
| Theorem 3: global pair | `global_dominance`, `global_attained`, `global_integrability`, `global_boundary`, `global_laplace` | Full-space selection, an actual attaining realization, integrability iff for positive exponents, endpoint divergence and Laplace order |
| Depth-five cubic figure | `CheckUnifiedNetworkCertificate.lean` | The three displayed local pairs for the same target and prior |

The algebraic fiber/count results also allow different source and target depths, including zero depth, and require no Gram or prior. Lean stores active words in reverse chronological order; equality is the same ordered-chain condition used in the paper.

## Analytic scope

`HasLaplaceOrder λ m Z` states `m > 0` and positive constants `c,C,N₀`, with `N₀ > 1`, such that

```text
c * N^(-λ) * (log N)^(m-1) ≤ Z(N) ≤ C * N^(-λ) * (log N)^(m-1)
```

for every real `N ≥ N₀`. The logarithmic power is proved independently of the inverse-power threshold. No leading constant, full asymptotic expansion, or complex meromorphic continuation is certified. The paper's zeta-pole interpretation under smooth local densities uses the cited resolution theory.

`LocalNetworkCertificate` gives the inverse-power iff for every real exponent, endpoint divergence, and Laplace order on every sufficiently small ball around the realization. Standalone identity/arrangement certificates require only `BoundedPositivePriorOn`: measurability and almost-everywhere positive lower and finite upper density bounds on the ball. Balls use the finite-product maximum norm. Inner and outer neighborhoods transfer their order to the paper's smooth local cutoffs.

The global inverse-power iff is stated for `s > 0`. At `s = 0`, finite prior mass suffices; negative exponents would require additional positive loss moments. The global Laplace integral is over all raw parameter space.

## Reproduce

From the repository root:

```sh
git checkout 2865e70a9ca7f559dabfce6aa32e13cf4fc88259
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false ../paper/checks/NetworkAudit.lean
lake env lean -DwarningAsError=true -DautoImplicit=false CheckUnifiedNetworkCertificate.lean
```

To rerun all library audit/check files:

```sh
for f in Audit*.lean Check*.lean; do
  lake env lean -DwarningAsError=true -DautoImplicit=false "$f" || exit 1
done
```

The release build, focused audit, and all 48 library audit/check files pass. The five focused declarations listed in Appendix E each depend on exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The focused audit also prints the definitions of `HasLaplaceOrder`, `LocalNetworkCertificate`, and `UnifiedNetworkCertificate`.

Evidence: `checks/lean-build.txt`, `checks/NetworkAudit.txt`, `checks/library-audits/`, and `checks/proof-source-sha256.json`. The release source is byte-identical to the completed research checkpoint `91b60f5850947f26ba4687d4f458f1ff2c3af6a1` under `lean/`; the public hash differs because the release repository has its own history. Dependencies were reused at their pinned revisions for this build.
