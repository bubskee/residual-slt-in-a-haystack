module
import ResidualSLT

/-! Actual-network examples beyond two quadratic blocks, with proved input hypotheses. -/
open ResidualSLT MeasureTheory Metric
open scoped NNReal ENNReal Classical

noncomputable def depthInput (r L : ℕ) : Measure ℝ :=
  atomicInput (fun i : Fin (networkFeatureCount r L) => (i.val : ℝ) + 1)

theorem quadratic_depth_three_threshold :
    HasIntegrabilityThresholdOn (@networkPopulationLoss (depthInput 2 3) 2 3)
      (ball 0 1) volume (3 / 4) := by
  convert even_network_threshold (depthInput 2 3) 2 (by norm_num) (by decide)
    3 (by norm_num) (network_atomic_gram 2 3) 1 (by norm_num) (le_refl 1) using 1; norm_num

theorem quartic_depth_two_threshold :
    HasIntegrabilityThresholdOn (@networkPopulationLoss (depthInput 4 2) 4 2)
      (ball 0 1) volume (1 / 4) := by
  convert even_network_threshold (depthInput 4 2) 4 (by norm_num) (by decide)
    2 (by norm_num) (network_atomic_gram 4 2) 1 (by norm_num) (le_refl 1) using 1; norm_num

/-- A discontinuous density with compact support in three raw parameters. -/
noncomputable def compactThreePrior (w : Fin 3 → ℝ) : ℝ≥0 :=
  if w ∈ ball 0 2 then (if w 0 < 0 then 1 else 2) else 0

theorem compactThreePrior_bounded :
    BoundedPositivePriorOn compactThreePrior (ball 0 1) volume := by
  constructor
  · exact (measurable_const.ite (measurableSet_lt (measurable_pi_apply 0) measurable_const)
      measurable_const).ite measurableSet_ball measurable_const
  · refine ⟨1, 2, by norm_num, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hw2 : w ∈ ball (0 : Fin 3 → ℝ) 2 := ball_subset_ball (by norm_num) hw
    simp only [compactThreePrior, ite_eq_left hw2]
    split_ifs <;> norm_num

theorem quadratic_depth_three_prior_iff (s : ℝ) :
    IntegrableOn (fun w => (compactThreePrior w : ℝ) *
      networkPopulationLoss (depthInput 2 3) 2 w ^ (-s)) (ball 0 1) volume ↔ s < 3 / 4 := by
  convert even_network_prior_weighted_integrableOn_iff (depthInput 2 3) 2 (by norm_num)
    (by decide) 3 (by norm_num) (network_atomic_gram 2 3) 1 (by norm_num) (le_refl 1)
    compactThreePrior compactThreePrior_bounded s using 1; norm_num

theorem quadratic_depth_three_prior_boundary :
    ¬ IntegrableOn (fun w => (compactThreePrior w : ℝ) *
      networkPopulationLoss (depthInput 2 3) 2 w ^ (-(3 / 4 : ℝ))) (ball 0 1) volume := by
  rw [quadratic_depth_three_prior_iff]
  exact lt_irrefl _

/-- The general actual loss specializes to the previously certified quadratic loss. -/
theorem general_loss_agrees_quadratic (μ : Measure ℝ) (a b : ℝ) :
    networkPopulationLoss μ 2 (![a, b] : Fin 2 → ℝ) = quadraticLoss μ (a, b) := by
  simp [networkPopulationLoss, networkSquaredError, quadraticLoss, quadraticSquaredError,
    network, zeroExtend]

/-- Odd-degree power sums can vanish away from the origin, so the even argument does not apply. -/
theorem cubic_model_cancellation :
    (![1, -1] : Fin 2 → ℝ) ≠ 0 ∧ evenNetworkModel 3 (![1, -1] : Fin 2 → ℝ) = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · norm_num [evenNetworkModel, weightPowerSum, Fin.sum_univ_succ]

#print axioms quadratic_depth_three_threshold
#print axioms quartic_depth_two_threshold
#print axioms compactThreePrior_bounded
#print axioms quadratic_depth_three_prior_iff
#print axioms quadratic_depth_three_prior_boundary
#print axioms general_loss_agrees_quadratic
#print axioms cubic_model_cancellation
