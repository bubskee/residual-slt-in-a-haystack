module
import ResidualSLT

/-! Assumption and integration checks: a nonvacuous probability input, a degenerate input,
a nonconstant bounded positive loss factor, and a discontinuous compact prior density. These are kernel-checked examples, not numerical tests. -/
open ResidualSLT MeasureTheory Set

/-- A finite-support input law already suffices at depth one. -/
theorem dirac_one_moment (r : ℕ) : FinitePositiveEvenMoment (Measure.dirac (1 : ℝ)) r := by
  constructor
  · exact integrable_dirac (by finiteness)
  · simp [evenMoment]

theorem quadratic_oneBlock_dirac_one : HasIntegrabilityThresholdOn (oneBlockLoss (Measure.dirac (1 : ℝ)) 2)
    (Ioo (-1) 1) volume (1 / 4) := by
  convert oneBlock_threshold (Measure.dirac (1 : ℝ)) 2 (by omega)
    (dirac_one_moment 2) 1 (by norm_num) using 1; norm_num

/-- The positivity assumption excludes a point mass at the zero input. -/
theorem zero_input_excluded (r : ℕ) (hr : 0 < r) : ¬ FinitePositiveEvenMoment (Measure.dirac (0 : ℝ)) r := by
  intro h
  have hp := h.positive
  simp [evenMoment, show 2 * r ≠ 0 by omega] at hp

theorem quadratic_positiveFactor_example : HasIntegrabilityThresholdOn
    (fun w : ℝ => (2 + w ^ 2) * oneBlockLoss (Measure.dirac (1 : ℝ)) 2 w)
    (Ioo (-1) 1) volume (1 / 4) := by
  have h : HasIntegrabilityThresholdOn (oneBlockLoss (Measure.dirac (1 : ℝ)) 2)
      (Ioo (-1) 1) volume (1 / 4) := by
    convert oneBlock_threshold (Measure.dirac (1 : ℝ)) 2 (by omega)
      (dirac_one_moment 2) 1 (by norm_num) using 1; norm_num
  refine h.mul_bounded (c := 2) (C := 3) ?_ ?_ (by norm_num) (by norm_num) ?_
  · have heq : oneBlockLoss (Measure.dirac (1 : ℝ)) 2 = fun w : ℝ => w ^ 4 := by
      funext w
      simp [oneBlock_loss_eq, evenMoment]
    rw [heq]
    exact (measurable_id.pow_const 4).aemeasurable
  · exact (measurable_const.add (measurable_id.pow_const 2)).aemeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    constructor
    · nlinarith [sq_nonneg w]
    · nlinarith [mul_pos (sub_pos.mpr hw.2) (by linarith [hw.1] : 0 < 1 + w)]

#print axioms dirac_one_moment

#print axioms quadratic_oneBlock_dirac_one
#print axioms zero_input_excluded
#print axioms quadratic_positiveFactor_example

open scoped NNReal ENNReal

/-- A discontinuous, compactly supported density. It vanishes outside (-2,2). -/
noncomputable def compactStepPrior (w : ℝ) : ℝ≥0 :=
  if w ∈ Ioo (-2 : ℝ) 2 then (if w < 0 then 1 else 2) else 0

theorem compactStepPrior_bounded :
    BoundedPositivePriorOn compactStepPrior (Ioo (-1) 1) volume := by
  constructor
  · exact (measurable_const.ite measurableSet_Iio measurable_const).ite
      measurableSet_Ioo measurable_const
  · refine ⟨1, 2, by norm_num, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    have hi : w ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hw.1], by linarith [hw.2]⟩
    simp only [compactStepPrior, ite_eq_left hi]
    split_ifs <;> norm_num

/-- The prior changes the measure, while the actual population loss is unchanged. -/
theorem quadratic_compactPrior_iff (s : ℝ) :
    IntegrableOn (fun w => oneBlockLoss (Measure.dirac (1 : ℝ)) 2 w ^ (-s))
      (Ioo (-1) 1) (volume.withDensity (fun w => (compactStepPrior w : ℝ≥0∞))) ↔
        s < 1 / 4 := by
  convert oneBlock_prior_integrableOn_iff (Measure.dirac (1 : ℝ)) 2 (by omega)
    (dirac_one_moment 2) 1 (by norm_num) compactStepPrior compactStepPrior_bounded s
    using 1; norm_num

/-- The endpoint diverges for the conventional prior-weighted Lebesgue integrand too. -/
theorem quadratic_compactPrior_weighted_boundary :
    ¬ IntegrableOn (fun w => (compactStepPrior w : ℝ) *
      oneBlockLoss (Measure.dirac (1 : ℝ)) 2 w ^ (-(1 / 4 : ℝ)))
      (Ioo (-1) 1) volume := by
  rw [← integrableOn_withDensity_iff_weighted measurableSet_Ioo
    compactStepPrior_bounded.measurable, quadratic_compactPrior_iff]
  exact lt_irrefl _

#print axioms compactStepPrior_bounded
#print axioms quadratic_compactPrior_iff
#print axioms quadratic_compactPrior_weighted_boundary
