module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open MeasureTheory Metric

/-- Both RLCT and Laplace multiplicity specialize through the unified certificate. -/
theorem unified_quadratic_equal (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 2 2))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 2 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ 2 w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < 1/2) ∧
    HasLaplaceOrder (1/2) 1 (fun N => ∫ w : Fin 2 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 2 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := identity_network_rlct_laplace_certificate μ 2 2 (by norm_num)
    (by omega) h ε hε hε1 ρ hρ
  norm_num [identityLearningPair] at hh ⊢
  exact hh

/-- Both RLCT and Laplace multiplicity specialize through the unified certificate. -/
theorem unified_quadratic_deep (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 2 5))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 5 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ 2 w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < 5/4) ∧
    HasLaplaceOrder (5/4) 1 (fun N => ∫ w : Fin 5 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 2 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := identity_network_rlct_laplace_certificate μ 2 5 (by norm_num)
    (by omega) h ε hε hε1 ρ hρ
  norm_num [identityLearningPair] at hh ⊢
  exact hh

/-- Both RLCT and Laplace multiplicity specialize through the unified certificate. -/
theorem unified_quintic_depth_one (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 5 1))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 1 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ 5 w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < 1/10) ∧
    HasLaplaceOrder (1/10) 1 (fun N => ∫ w : Fin 1 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 5 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := identity_network_rlct_laplace_certificate μ 5 1 (by norm_num)
    (by omega) h ε hε hε1 ρ hρ
  norm_num [identityLearningPair] at hh ⊢
  exact hh

/-- Both RLCT and Laplace multiplicity specialize through the unified certificate. -/
theorem unified_cubic_shallow (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 2))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 2 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ 3 w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < 1/3) ∧
    HasLaplaceOrder (1/3) 1 (fun N => ∫ w : Fin 2 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 3 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := identity_network_rlct_laplace_certificate μ 3 2 (by norm_num)
    (by omega) h ε hε hε1 ρ hρ
  norm_num [identityLearningPair] at hh ⊢
  exact hh

/-- Both RLCT and Laplace multiplicity specialize through the unified certificate. -/
theorem unified_cubic_critical (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 3 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ 3 w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < 1/2) ∧
    HasLaplaceOrder (1/2) 2 (fun N => ∫ w : Fin 3 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 3 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := identity_network_rlct_laplace_certificate μ 3 3 (by norm_num)
    (by omega) h ε hε hε1 ρ hρ
  norm_num [identityLearningPair] at hh ⊢
  exact hh

/-- Both RLCT and Laplace multiplicity specialize through the unified certificate. -/
theorem unified_cubic_deep (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 5))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 5 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ 3 w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < 2/3) ∧
    HasLaplaceOrder (2/3) 1 (fun N => ∫ w : Fin 5 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 3 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := identity_network_rlct_laplace_certificate μ 3 5 (by norm_num)
    (by omega) h ε hε hε1 ρ hρ
  norm_num [identityLearningPair] at hh ⊢
  exact hh

/-- The unified divergence corollary applies exactly at its computed threshold. -/
theorem unified_identity_boundary (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 (1/2)) volume) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ r w^(-(identityLearningPair r L).1))
      (ball 0 (1/2)) (volume.withDensity (fun w => (ρ w : ENNReal))) :=
  identity_network_prior_not_integrable μ r L hr hL h (1/2) (by norm_num) (by norm_num)
    ρ hρ _ le_rfl

end ResidualSLT.Examples

#print axioms ResidualSLT.Examples.unified_quadratic_equal
#print axioms ResidualSLT.Examples.unified_quadratic_deep
#print axioms ResidualSLT.Examples.unified_quintic_depth_one
#print axioms ResidualSLT.Examples.unified_cubic_shallow
#print axioms ResidualSLT.Examples.unified_cubic_critical
#print axioms ResidualSLT.Examples.unified_cubic_deep
#print axioms ResidualSLT.Examples.unified_identity_boundary
