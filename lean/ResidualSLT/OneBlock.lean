module
public import ResidualSLT.PolynomialNetworks
public import ResidualSLT.LossComparison
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! An end-to-end integrability certificate for the actual one-block population loss.
Input measure `μ` and parameter Lebesgue measure are distinct. The result needs a finite,
strictly positive input moment; probability measures are included but normalization is unnecessary.
No pole multiplicity, Laplace asymptotic, or multi-block threshold is asserted. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial MeasureTheory Set

/-- The squared residual of the existing polynomial network at depth one. -/
@[expose] def oneBlockSquaredError (r : ℕ) (w x : ℝ) : ℝ :=
  ((network r (fun _ => w ^ r) 1).eval x - x) ^ 2

/-- Population squared-error loss against the identity target, with raw weight w. -/
@[expose] def oneBlockLoss (μ : Measure ℝ) (r : ℕ) (w : ℝ) : ℝ :=
  ∫ x, oneBlockSquaredError r w x ∂μ

/-- Input even moment. As with all Bochner integrals, use an integrability hypothesis
before interpreting this totalized expression as an ordinary finite moment. -/
@[expose] def evenMoment (μ : Measure ℝ) (r : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ (2 * r) ∂μ

/-- Explicit finiteness and nondegeneracy assumptions on the input distribution. -/
structure FinitePositiveEvenMoment (μ : Measure ℝ) (r : ℕ) : Prop where
  integrable : Integrable (fun x : ℝ => x ^ (2 * r)) μ
  positive : 0 < evenMoment μ r

/-- Exact algebra of the actual depth-one network, before taking any integral. -/
theorem oneBlock_squaredError_eq (r : ℕ) (w x : ℝ) :
    oneBlockSquaredError r w x = w ^ (2 * r) * x ^ (2 * r) := by
  simp only [oneBlockSquaredError, network, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    add_sub_cancel_left, mul_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm r 2]

/-- A finite input moment guarantees integrability of every actual squared-error integrand. -/
theorem oneBlock_squaredError_integrable (μ : Measure ℝ) (r : ℕ)
    (h : Integrable (fun x : ℝ => x ^ (2 * r)) μ) (w : ℝ) :
    Integrable (oneBlockSquaredError r w) μ := by
  change Integrable (fun x => oneBlockSquaredError r w x) μ
  simpa only [oneBlock_squaredError_eq] using h.const_mul (w ^ (2 * r))

/-- Exact evaluation of the population loss. This identity also holds for totalized
Bochner integrals; the certificate below separately proves actual integrability. -/
theorem oneBlock_loss_eq (μ : Measure ℝ) (r : ℕ) (w : ℝ) :
    oneBlockLoss μ r w = evenMoment μ r * w ^ (2 * r) := by
  simp only [oneBlockLoss, oneBlock_squaredError_eq, integral_const_mul, evenMoment]
  ring

/-- A useful distribution-level sufficient condition: finite moment and positive mass
away from zero. No infinite-support or positive-density assumption is required at depth one. -/
theorem finitePositiveEvenMoment_of_mass_ne_zero (μ : Measure ℝ) (r : ℕ) (hr : 0 < r)
    (hfin : Integrable (fun x : ℝ => x ^ (2 * r)) μ)
    (hmass : 0 < μ {x : ℝ | x ≠ 0}) : FinitePositiveEvenMoment μ r := by
  refine ⟨hfin, ?_⟩
  rw [evenMoment, integral_pos_iff_support_of_nonneg (fun x => ?_) hfin]
  · simpa [Function.support, pow_eq_zero_iff (by omega : 2 * r ≠ 0)] using hmass
  · rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) r

/-- Exact power-integrability criterion for the actual population loss on every full
symmetric parameter neighborhood. The exponent s may be any real number. -/
theorem oneBlock_integrableOn_iff (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun w => oneBlockLoss μ r w ^ (-s)) (Ioo (-ε) ε) volume ↔
      s < 1 / (2 * (r : ℝ)) := by
  simp only [oneBlock_loss_eq]
  rw [integrableOn_rpow_const_mul_iff h.positive (Filter.Eventually.of_forall (fun w => ?_))]
  · exact monomial_integrableOn_symmetric_iff r (by omega) ε hε s
  · rw [pow_mul]
    exact pow_nonneg (sq_nonneg w) r

/-- The raw one-block population-loss threshold, with finite positive input moment. -/
theorem oneBlock_threshold (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn (oneBlockLoss μ r) (Ioo (-ε) ε) volume
      (1 / (2 * (r : ℝ))) := by
  have heq : oneBlockLoss μ r = fun w => evenMoment μ r * w ^ (2 * r) :=
    funext (oneBlock_loss_eq μ r)
  rw [heq]
  exact (monomial_thresholdOn_symmetric r (by omega) ε hε).const_mul h.positive

/-- A single end-to-end certificate: every input loss integrand is integrable, its integral
has the exact moment formula, and its parameter integrability threshold is 1/(2r). -/
theorem oneBlock_certificate (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε) :
    (∀ w, Integrable (oneBlockSquaredError r w) μ) ∧
    (∀ w, oneBlockLoss μ r w = evenMoment μ r * w ^ (2 * r)) ∧
    HasIntegrabilityThresholdOn (oneBlockLoss μ r) (Ioo (-ε) ε) volume
      (1 / (2 * (r : ℝ))) := by
  exact ⟨oneBlock_squaredError_integrable μ r h.integrable,
    oneBlock_loss_eq μ r, oneBlock_threshold μ r hr h ε hε⟩

/-- Boundary divergence is part of the certificate, not merely a supremum computation. -/
theorem oneBlock_not_integrable_at_threshold (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h : FinitePositiveEvenMoment μ r) (ε : ℝ) (hε : 0 < ε) :
    ¬ IntegrableOn (fun w => oneBlockLoss μ r w ^ (-(1 / (2 * (r : ℝ)))))
      (Ioo (-ε) ε) volume := by
  rw [oneBlock_integrableOn_iff μ r hr h ε hε]
  exact lt_irrefl _
end ResidualSLT
