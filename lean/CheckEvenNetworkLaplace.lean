module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open MeasureTheory Metric

/-- Actual even network: degree 2, depth 1, arbitrary bounded positive prior. -/
theorem quadratic_depth_one_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 2 1))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 1 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (1/4) (fun N => ∫ w : Fin 1 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 2 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := even_network_laplace_order μ 2 1 (by norm_num) (by decide)
    (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- Actual even network: degree 2, depth 2, arbitrary bounded positive prior. -/
theorem quadratic_depth_two_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 2 2))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 2 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (1/2) (fun N => ∫ w : Fin 2 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 2 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := even_network_laplace_order μ 2 2 (by norm_num) (by decide)
    (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- Actual even network: degree 2, depth 5, arbitrary bounded positive prior. -/
theorem quadratic_depth_five_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 2 5))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 5 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (5/4) (fun N => ∫ w : Fin 5 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 2 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := even_network_laplace_order μ 2 5 (by norm_num) (by decide)
    (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- Actual even network: degree 4, depth 4, arbitrary bounded positive prior. -/
theorem quartic_depth_four_laplace (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 4 4))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 4 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (1/2) (fun N => ∫ w : Fin 4 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 4 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := even_network_laplace_order μ 4 4 (by norm_num) (by decide)
    (by omega) h ε hε hε1 ρ hρ
  norm_num at hh ⊢
  exact hh

/-- Boundary divergence remains valid with a non-unit neighborhood. -/
theorem quadratic_depth_five_laplace_boundary (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 2 5))
    (ρ : (Fin 5 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 (1/2)) volume) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ 2 w^(-(5/4:ℝ))) (ball 0 (1/2))
      (volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hh := (even_network_laplace_certificate μ 2 5 (by omega) (by decide)
    (by omega) h (1/2) (by norm_num) (by norm_num) ρ hρ).2 (5/4)
  norm_num at hh
  exact hh

/-- The independent radial density theorem also permits cutoffs larger than one. -/
theorem radial_density_five_quartic_laplace :
    HasPowerLaplaceOrder (5/4) (fun N => ∫ x : ℝ in Set.Ioo 0 2,
      x^4*Real.exp (-N*x^4)) := by
  have h := weighted_radial_interval_laplace_order 5 2 (by omega) (by omega) 2 (by norm_num)
  norm_num at h ⊢
  exact h

end ResidualSLT.Examples

#print axioms ResidualSLT.Examples.quadratic_depth_one_laplace
#print axioms ResidualSLT.Examples.quadratic_depth_two_laplace
#print axioms ResidualSLT.Examples.quadratic_depth_five_laplace
#print axioms ResidualSLT.Examples.quartic_depth_four_laplace
#print axioms ResidualSLT.Examples.quadratic_depth_five_laplace_boundary
#print axioms ResidualSLT.Examples.radial_density_five_quartic_laplace
