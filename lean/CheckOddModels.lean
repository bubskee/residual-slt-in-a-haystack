module
import ResidualSLT

noncomputable section
namespace ResidualSLT.Examples
open MeasureTheory Set

/-- Below transition: L=2,r=3; this is the weighted model, not the network. -/
theorem cubic_two_model (s : ℝ) :
    IntegrableOn (weightedCancellation 2 3 3 s) (Ioo 0 1 ×ˢ Ioo (-1) 1) volume ↔
      s < 1 / 3 := by
  convert weightedNetworkModel_phase_transition 2 3 (by decide) (by decide) s using 2; norm_num

/-- At transition, on unequal small radial/transverse intervals. -/
theorem cubic_three_local_model (s : ℝ) :
    IntegrableOn (weightedCancellation 3 3 3 s)
      (Ioo 0 (1 / 10) ×ˢ Ioo (-(1 / 7)) (1 / 7)) volume ↔ s < 1 / 2 := by
  simpa using weightedNetworkModel_local_phase_transition 3 3 (by decide) (by decide)
    (1 / 10) (1 / 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) s

/-- Above transition: L=4,r=3. -/
theorem cubic_four_model (s : ℝ) :
    IntegrableOn (weightedCancellation 4 3 3 s) (Ioo 0 1 ×ˢ Ioo (-1) 1) volume ↔
      s < 7 / 12 := by
  convert weightedNetworkModel_phase_transition 4 3 (by decide) (by decide) s using 2; norm_num

theorem cubic_transition_endpoint :
    ¬ IntegrableOn (weightedCancellation 3 3 3 (1 / 2))
      (Ioo 0 (1 / 10) ×ˢ Ioo (-(1 / 7)) (1 / 7)) volume := by
  rw [cubic_three_local_model]
  exact lt_irrefl _

/-- General k=5,r=3,L=5 model, with d=k-r=2. -/
theorem unequal_radial_order_model (s : ℝ) :
    IntegrableOn (weightedCancellation 5 3 2 s) (Ioo 0 1 ×ˢ Ioo (-1) 1) volume ↔
      s < 7 / 10 := by
  convert weightedCancellation_symmetric_integrableOn_iff 5 (by norm_num) 3 2
    (by decide) (by decide) s using 2; norm_num

/-- Critical transverse exponent is integrable above the transition. -/
theorem cubic_four_half_integrable :
    IntegrableOn (weightedCancellation 4 3 3 (1 / 2)) (Ioo 0 1 ×ˢ Ioo (-1) 1) volume := by
  rw [cubic_four_model]
  norm_num

/-- The cancellation set is nonempty and transverse for every odd degree, L≥2. -/
theorem odd_sphere_regular_witness (r L : ℕ) (hr : Odd r) (hL : 2 ≤ L) :
    ∃ w v : Fin L → ℝ, weightPowerSum r w = 0 ∧ weightPowerSum 2 w = 1 ∧
      fermatDifferential 2 w v = 0 ∧ fermatDifferential r w v ≠ 0 := by
  obtain ⟨w, hS, hSphere⟩ := odd_fermat_sphere_nonempty r L hr hL
  obtain ⟨v, hv, hv'⟩ := fermat_sphere_transverse r L hr.pos w hS hSphere
  exact ⟨w, v, hS, hSphere, hv, hv'⟩

/-- Actual cubic depth-three prior transfer stops at the radial Fermat model. -/
theorem cubic_network_radial_reduction (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ (networkFeatures 3 3))
    (ρ : (Fin 3 → ℝ) → NNReal)
    (hρ : BoundedPositivePriorOn ρ (Metric.ball 0 1) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ 3 w ^ (-s)) (Metric.ball 0 1)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
      IntegrableOn (fun w : Fin 3 → ℝ =>
        (weightPowerSum 3 w ^ 2 + ‖w‖ ^ 12) ^ (-s)) (Metric.ball 0 1) volume := by
  exact signed_network_prior_integrableOn_iff_radial μ 3 (by decide) 3 (by decide)
    h 1 le_rfl ρ hρ s

#print axioms cubic_two_model
#print axioms cubic_three_local_model
#print axioms cubic_four_model
#print axioms cubic_transition_endpoint
#print axioms unequal_radial_order_model
#print axioms cubic_four_half_integrable
#print axioms odd_sphere_regular_witness
#print axioms cubic_network_radial_reduction
end ResidualSLT.Examples
