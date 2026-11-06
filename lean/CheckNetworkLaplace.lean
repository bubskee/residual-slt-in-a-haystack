module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open MeasureTheory Metric

/-- Cubic, depth-three actual population loss, with arbitrary bounded positive prior. -/
theorem cubic_identity_laplace_order (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin 3 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasCriticalLaplaceOrder (fun N => ∫ w : Fin 3 → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ 3 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) :=
  odd_critical_network_laplace_order μ 3 (by norm_num) (by decide) h ε hε hε1 ρ hρ

/-- Quintic, depth-five actual population loss: the statement is not specific to cubic degree. -/
theorem quintic_identity_laplace_order (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 5 5))
    (ρ : (Fin 5 → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 1) volume) :
    HasCriticalLaplaceOrder (fun N => ∫ w : Fin 5 → ℝ in ball 0 1,
      Real.exp (-N*networkPopulationLoss μ 5 w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) :=
  odd_critical_network_laplace_order μ 5 (by norm_num) (by decide) h 1 zero_lt_one le_rfl ρ hρ

/-- A non-unit weighted product region also has the logarithmic factor. -/
theorem cubic_weighted_small_rectangle :
    HasCriticalLaplaceOrder (weightedLaplaceSymmetric 3 (1/2) (1/3)) :=
  weightedLaplaceSymmetric_has_order 3 (by norm_num) (1/2) (1/3) (by norm_num) (by norm_num)

end ResidualSLT.Examples
#print axioms ResidualSLT.Examples.cubic_identity_laplace_order
#print axioms ResidualSLT.Examples.quintic_identity_laplace_order
#print axioms ResidualSLT.Examples.cubic_weighted_small_rectangle
