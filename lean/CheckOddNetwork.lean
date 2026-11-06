module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open Set MeasureTheory Metric

/-- Actual cubic depth-one network, not the weighted comparison model. -/
theorem cubic_depth_one_threshold (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 1))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 1 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔ s < 1 / 6 := by
  convert odd_network_prior_phase_transition μ 3 (by decide) (by decide) 1 (by decide) h
    ε hε hε1 p hp s using 1
  norm_num

/-- Depth two checks the boundary angular case; no interior cancellation point is assumed. -/
theorem cubic_depth_two_threshold (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 2))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 2 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔ s < 1 / 3 := by
  convert odd_network_prior_phase_transition μ 3 (by decide) (by decide) 2 (by decide) h
    ε hε hε1 p hp s using 1
  norm_num

/-- Critical depth: the exact integrability threshold is one half. -/
theorem cubic_depth_three_threshold (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 3 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔ s < 1 / 2 := by
  simpa using odd_network_prior_phase_transition μ 3 (by decide) (by decide) 3 (by decide) h
    ε hε hε1 p hp s

/-- Above the transition, the actual-network threshold is (L+r)/(4r). -/
theorem cubic_depth_four_threshold (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 4))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 4 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔ s < 7 / 12 := by
  convert odd_network_prior_phase_transition μ 3 (by decide) (by decide) 4 (by decide) h
    ε hε hε1 p hp s using 1
  norm_num

theorem quintic_depth_six_threshold (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 5 6))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 6 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 5 w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) ↔ s < 11 / 20 := by
  convert odd_network_prior_phase_transition μ 5 (by decide) (by decide) 6 (by decide) h
    ε hε hε1 p hp s using 1
  norm_num

/-- Endpoint divergence of the actual cubic loss, including the bounded positive prior. -/
theorem cubic_critical_endpoint_diverges (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 3 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-(1 / 2 : ℝ))) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) := by
  rw [cubic_depth_three_threshold μ h ε hε hε1 p hp]
  exact lt_irrefl _

/-- The half exponent is genuinely integrable above the transition. -/
theorem cubic_depth_four_half_integrable (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 4))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 4 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-(1 / 2 : ℝ))) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) := by
  rw [cubic_depth_four_threshold μ h ε hε hε1 p hp]
  norm_num

/-- Input finiteness and a.e. positivity belong to the network certificate itself. -/
theorem cubic_depth_three_certificate (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (p : (Fin 3 → ℝ) → NNReal)
    (hp : BoundedPositivePriorOn p (ball 0 ε) volume) :
    (∀ w : Fin 3 → ℝ, Integrable (networkSquaredError 3 w) μ) ∧
    HasIntegrabilityThresholdOn (@networkPopulationLoss μ 3 3) (ball 0 ε)
      (volume.withDensity (fun w => (p w : ENNReal))) (1 / 2) := by
  obtain ⟨hfin, _, hth⟩ := odd_network_certificate μ 3 (by decide) (by decide) 3 (by decide) h
    ε hε hε1 p hp
  refine ⟨hfin, ?_⟩
  convert hth using 1
  norm_num

/-- Nonvacuous instance: the input Gram hypothesis is discharged by the existing
explicit atomic measure, rather than retained as an assumption. -/
theorem cubic_atomic_threshold (s : ℝ) :
    IntegrableOn (fun w : Fin 3 → ℝ => networkPopulationLoss
      (atomicInput (fun i : Fin (networkFeatureCount 3 3) => (i.val : ℝ) + 1)) 3 w ^ (-s))
      (ball 0 1) volume ↔ s < 1 / 2 := by
  convert odd_network_integrableOn_iff _ 3 (by decide) (by decide) 3 (by decide)
    (network_atomic_gram 3 3) 1 zero_lt_one le_rfl s using 1
  norm_num

#print axioms cubic_depth_one_threshold
#print axioms cubic_depth_two_threshold
#print axioms cubic_depth_three_threshold
#print axioms cubic_depth_four_threshold
#print axioms quintic_depth_six_threshold
#print axioms cubic_critical_endpoint_diverges
#print axioms cubic_depth_four_half_integrable
#print axioms cubic_depth_three_certificate
#print axioms cubic_atomic_threshold
end ResidualSLT.Examples
