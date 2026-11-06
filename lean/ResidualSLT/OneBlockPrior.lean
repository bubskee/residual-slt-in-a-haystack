module
public import ResidualSLT.OneBlock
public import ResidualSLT.PriorMeasure

/-! The actual one-block loss with a locally bounded positive parameter prior.
Input law μ and parameter density ρ are separate. This is an integrability threshold,
not a pole multiplicity or Laplace-asymptotic certificate. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set
open scoped NNReal ENNReal

/-- All real exponents, with no assumptions on the density outside the neighborhood. -/
theorem oneBlock_prior_integrableOn_iff (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε)
    (ρ : ℝ → ℝ≥0) (hρ : BoundedPositivePriorOn ρ (Ioo (-ε) ε) volume) (s : ℝ) :
    IntegrableOn (fun w => oneBlockLoss μ r w ^ (-s)) (Ioo (-ε) ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) ↔ s < 1 / (2 * (r : ℝ)) := by
  rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_Ioo hρ]
  exact oneBlock_integrableOn_iff μ r hr h ε hε s

/-- Equivalent statement for the usual density-weighted Lebesgue integrand. -/
theorem oneBlock_prior_weighted_integrableOn_iff (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε)
    (ρ : ℝ → ℝ≥0) (hρ : BoundedPositivePriorOn ρ (Ioo (-ε) ε) volume) (s : ℝ) :
    IntegrableOn (fun w => (ρ w : ℝ) * oneBlockLoss μ r w ^ (-s))
      (Ioo (-ε) ε) volume ↔ s < 1 / (2 * (r : ℝ)) := by
  rw [← integrableOn_withDensity_iff_weighted measurableSet_Ioo hρ.measurable]
  exact oneBlock_prior_integrableOn_iff μ r hr h ε hε ρ hρ s

/-- The one-block threshold under a measurable, locally bounded positive prior. -/
theorem oneBlock_prior_threshold (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε)
    (ρ : ℝ → ℝ≥0) (hρ : BoundedPositivePriorOn ρ (Ioo (-ε) ε) volume) :
    HasIntegrabilityThresholdOn (oneBlockLoss μ r) (Ioo (-ε) ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) (1 / (2 * (r : ℝ))) := by
  exact (oneBlock_threshold μ r hr h ε hε).withDensity measurableSet_Ioo hρ

/-- End-to-end: input integrability, actual population loss formula, prior threshold. -/
theorem oneBlock_prior_certificate (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε)
    (ρ : ℝ → ℝ≥0) (hρ : BoundedPositivePriorOn ρ (Ioo (-ε) ε) volume) :
    (∀ w, Integrable (oneBlockSquaredError r w) μ) ∧
    (∀ w, oneBlockLoss μ r w = evenMoment μ r * w ^ (2 * r)) ∧
    HasIntegrabilityThresholdOn (oneBlockLoss μ r) (Ioo (-ε) ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) (1 / (2 * (r : ℝ))) := by
  exact ⟨oneBlock_squaredError_integrable μ r h.integrable, oneBlock_loss_eq μ r,
    oneBlock_prior_threshold μ r hr h ε hε ρ hρ⟩

/-- Divergence at the critical exponent also survives the change of parameter measure. -/
theorem oneBlock_prior_not_integrable_at_threshold (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε)
    (ρ : ℝ → ℝ≥0) (hρ : BoundedPositivePriorOn ρ (Ioo (-ε) ε) volume) :
    ¬ IntegrableOn (fun w => oneBlockLoss μ r w ^ (-(1 / (2 * (r : ℝ)))))
      (Ioo (-ε) ε) (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) := by
  rw [oneBlock_prior_integrableOn_iff μ r hr h ε hε ρ hρ]
  exact lt_irrefl _
end ResidualSLT
