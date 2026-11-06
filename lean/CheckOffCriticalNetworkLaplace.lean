module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open MeasureTheory Metric

/-- Actual population loss: degree 3, depth 1, bounded positive prior. -/
theorem cubic_depth_one_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 1))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 1 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (1/6) (fun N => ∫ w : Fin 1 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 3 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := odd_offcritical_network_laplace_order μ 3 1 (by norm_num) (by decide)
    (by omega) (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- Actual population loss: degree 3, depth 2, bounded positive prior. -/
theorem cubic_depth_two_network_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 2))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 2 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (1/3) (fun N => ∫ w : Fin 2 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 3 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := odd_offcritical_network_laplace_order μ 3 2 (by norm_num) (by decide)
    (by omega) (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- Actual population loss: degree 3, depth 4, bounded positive prior. -/
theorem cubic_depth_four_network_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 4))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 4 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (7/12) (fun N => ∫ w : Fin 4 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 3 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := odd_offcritical_network_laplace_order μ 3 4 (by norm_num) (by decide)
    (by omega) (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- Actual population loss: degree 5, depth 6, bounded positive prior. -/
theorem quintic_depth_six_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 5 6))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 6 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (11/20) (fun N => ∫ w : Fin 6 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 5 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := odd_offcritical_network_laplace_order μ 5 6 (by norm_num) (by decide)
    (by omega) (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- The combined certificate includes boundary divergence for the actual loss. -/
theorem cubic_depth_two_network_boundary (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 2))
    (ρ : (Fin 2 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 (1/2)) volume) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-(1/3:ℝ))) (ball 0 (1/2))
      (volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := (odd_offcritical_network_certificate μ 3 2 (by omega) (by decide)
    (by omega) (by omega) h (1/2) (by norm_num) (by norm_num) ρ hρ).2 (1/3)
  norm_num at hh
  exact hh

end ResidualSLT.Examples

#print axioms ResidualSLT.Examples.cubic_depth_one_laplace
#print axioms ResidualSLT.Examples.cubic_depth_two_network_laplace
#print axioms ResidualSLT.Examples.cubic_depth_four_network_laplace
#print axioms ResidualSLT.Examples.quintic_depth_six_laplace
#print axioms ResidualSLT.Examples.cubic_depth_two_network_boundary
