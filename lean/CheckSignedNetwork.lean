module
import ResidualSLT

/-! Cubic signed-cancellation examples with a proved nondegenerate atomic input. -/
open ResidualSLT MeasureTheory Metric Polynomial
open scoped NNReal ENNReal Classical

noncomputable def cubicInput : Measure ℝ :=
  atomicInput (fun i : Fin (networkFeatureCount 3 3) => (i.val : ℝ) + 1)

theorem cubic_three_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ ball (0 : Fin 3 → ℝ) 1,
      c * cancellationModel 3 w ≤ networkPopulationLoss cubicInput 3 w ∧
      networkPopulationLoss cubicInput 3 w ≤ C * cancellationModel 3 w :=
  signed_network_loss_comparison cubicInput 3 (by norm_num) 3 (by norm_num) (network_atomic_gram 3 3)

theorem cubic_model_on_cancellation (t : ℝ) :
    weightPowerSum 3 (![t, -t, 0] : Fin 3 → ℝ) = 0 ∧
    cancellationModel 3 (![t, -t, 0] : Fin 3 → ℝ) = 4 * t ^ 12 := by
  constructor
  · simp [weightPowerSum, Fin.sum_univ_succ]
    ring
  · simp [cancellationModel, weightPowerSum, weightSquareSum, Fin.sum_univ_succ]
    ring

theorem cubic_second_on_cancellation (t : ℝ) :
    (network 3 (fun i => zeroExtend (![t, -t, 0] : Fin 3 → ℝ) i ^ 3) 3 - X).coeff 5 =
      -3 * t ^ 6 := by
  have h := residual_second_SQ 3 (by norm_num) 3 (![t, -t, 0] : Fin 3 → ℝ)
  norm_num [weightPowerSum, weightSquareSum, Fin.sum_univ_succ] at h
  rw [coeff_sub]
  norm_num [coeff_X] at h ⊢
  nlinarith

/-- Along this nontrivial cancellation path the actual loss has order twelve. -/
theorem cubic_loss_on_cancellation :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, |t| < 1 →
      c * t ^ 12 ≤ networkPopulationLoss cubicInput 3 (![t, -t, 0] : Fin 3 → ℝ) ∧
      networkPopulationLoss cubicInput 3 (![t, -t, 0] : Fin 3 → ℝ) ≤ C * t ^ 12 := by
  obtain ⟨c, C, hc, hC, hb⟩ := cubic_three_comparison
  refine ⟨4 * c, 4 * C, by positivity, by positivity, ?_⟩
  intro t ht
  have hw : (![t, -t, 0] : Fin 3 → ℝ) ∈ ball 0 1 := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs, ht]
  have h := hb _ hw
  rw [(cubic_model_on_cancellation t).2] at h
  constructor <;> nlinarith [h.1, h.2]

theorem cubic_loss_positive_on_cancellation (t : ℝ) (ht : |t| < 1) (hne : t ≠ 0) :
    0 < networkPopulationLoss cubicInput 3 (![t, -t, 0] : Fin 3 → ℝ) := by
  obtain ⟨c, C, hc, _, hb⟩ := cubic_loss_on_cancellation
  exact lt_of_lt_of_le (mul_pos hc (pow_pos (sq_pos_of_ne_zero hne) 6)) (by
    simpa only [← pow_mul] using (hb t ht).1)

noncomputable def cubicCompactPrior (w : Fin 3 → ℝ) : ℝ≥0 :=
  if w ∈ ball 0 2 then (if w 0 < 0 then 1 else 2) else 0

theorem cubicCompactPrior_bounded :
    BoundedPositivePriorOn cubicCompactPrior (ball 0 1) volume := by
  constructor
  · exact (measurable_const.ite (measurableSet_lt (measurable_pi_apply 0) measurable_const)
      measurable_const).ite measurableSet_ball measurable_const
  · refine ⟨1, 2, by norm_num, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hw2 : w ∈ ball (0 : Fin 3 → ℝ) 2 := ball_subset_ball (by norm_num) hw
    simp only [cubicCompactPrior, ite_eq_left hw2]
    split_ifs <;> norm_num

theorem cubic_prior_reduction (s : ℝ) :
    IntegrableOn (fun w => (cubicCompactPrior w : ℝ) * networkPopulationLoss cubicInput 3 w ^ (-s))
      (ball 0 1) volume ↔
    IntegrableOn (fun w : Fin 3 → ℝ => cancellationModel 3 w ^ (-s)) (ball 0 1) volume :=
  signed_network_prior_weighted_integrableOn_iff_model cubicInput 3 (by norm_num)
    3 (by norm_num) (network_atomic_gram 3 3) 1 (le_refl 1) cubicCompactPrior cubicCompactPrior_bounded s

/-- At depth one the second coefficient lies beyond the feature basis and vanishes. -/
theorem cubic_single_block_second_zero (t : ℝ) :
    (network 3 (fun i => zeroExtend (![t] : Fin 1 → ℝ) i ^ 3) 1 - X).coeff 5 = 0 := by
  have h : network 3 (fun i => zeroExtend (![t] : Fin 1 → ℝ) i ^ 3) 1 - X =
      C (t ^ 3) * X ^ 3 := by simp [network, zeroExtend]
  rw [h, coeff_C_mul]
  norm_num

#print axioms cubic_three_comparison
#print axioms cubic_model_on_cancellation
#print axioms cubic_second_on_cancellation
#print axioms cubic_loss_on_cancellation
#print axioms cubic_loss_positive_on_cancellation
#print axioms cubicCompactPrior_bounded
#print axioms cubic_prior_reduction
#print axioms cubic_single_block_second_zero
