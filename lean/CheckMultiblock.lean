module
import ResidualSLT

/-! Nonvacuity check for the two-block Gram hypotheses, using three input atoms. -/
open ResidualSLT MeasureTheory Matrix
open scoped NNReal ENNReal Classical
noncomputable def threePointInput : Measure ℝ :=
  Measure.dirac (-1) + Measure.dirac 1 + Measure.dirac 2

theorem threePoint_integrable (f : ℝ → ℝ) : Integrable f threePointInput := by
  exact ((integrable_dirac (by finiteness)).add_measure
    (integrable_dirac (by finiteness))).add_measure (integrable_dirac (by finiteness))

theorem threePoint_gram_matrix : featureGram threePointInput quadraticFeatures =
    !![18, 32, 66; 32, 66, 128; 66, 128, 258] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [featureGram, quadraticFeatures, threePointInput, integral_add_measure,
      integrable_dirac]

theorem threePoint_positive_gram : FinitePositiveFeatureGram threePointInput quadraticFeatures := by
  refine ⟨fun i j => threePoint_integrable _, ?_⟩
  rw [threePoint_gram_matrix, Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  · intro c hc
    have heq : star c ⬝ᵥ (!![18, 32, 66; 32, 66, 128; 66, 128, 258] *ᵥ c) =
        (c 0 - c 1 + c 2) ^ 2 + (c 0 + c 1 + c 2) ^ 2 +
          (4 * c 0 + 8 * c 1 + 16 * c 2) ^ 2 := by
      simp [dotProduct, mulVec, Fin.sum_univ_succ]
      ring
    rw [heq]
    by_contra hn
    have h0 : c 0 - c 1 + c 2 = 0 := by
      nlinarith [sq_nonneg (c 0 - c 1 + c 2), sq_nonneg (c 0 + c 1 + c 2),
        sq_nonneg (4 * c 0 + 8 * c 1 + 16 * c 2)]
    have h1 : c 0 + c 1 + c 2 = 0 := by
      nlinarith [sq_nonneg (c 0 - c 1 + c 2), sq_nonneg (c 0 + c 1 + c 2),
        sq_nonneg (4 * c 0 + 8 * c 1 + 16 * c 2)]
    have h2 : 4 * c 0 + 8 * c 1 + 16 * c 2 = 0 := by
      nlinarith [sq_nonneg (c 0 - c 1 + c 2), sq_nonneg (c 0 + c 1 + c 2),
        sq_nonneg (4 * c 0 + 8 * c 1 + 16 * c 2)]
    apply hc
    funext i
    fin_cases i
    · change c 0 = 0; linarith
    · change c 1 = 0; linarith
    · change c 2 = 0; linarith

theorem threePoint_twoBlock_threshold :
    HasIntegrabilityThresholdOn (quadraticLoss threePointInput)
      (Metric.ball (0 : ℝ × ℝ) 1) volume (1 / 2) :=
  quadratic_threshold threePointInput threePoint_positive_gram 1 (by norm_num) (le_refl 1)

#print axioms threePoint_integrable
#print axioms threePoint_gram_matrix
#print axioms threePoint_positive_gram
#print axioms threePoint_twoBlock_threshold

/-- A compactly supported discontinuous parameter density, positive only locally. -/
noncomputable def compactPlanePrior (w : ℝ × ℝ) : ℝ≥0 :=
  if w ∈ Metric.ball 0 2 then (if w.1 < 0 then 1 else 2) else 0

theorem compactPlanePrior_bounded :
    BoundedPositivePriorOn compactPlanePrior (Metric.ball (0 : ℝ × ℝ) 1) volume := by
  constructor
  · exact (measurable_const.ite (measurableSet_lt measurable_fst measurable_const)
      measurable_const).ite measurableSet_ball measurable_const
  · refine ⟨1, 2, by norm_num, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hw2 : w ∈ Metric.ball (0 : ℝ × ℝ) 2 := Metric.ball_subset_ball (by norm_num) hw
    simp only [compactPlanePrior, ite_eq_left hw2]
    split_ifs <;> norm_num

theorem threePoint_twoBlock_prior_iff (s : ℝ) :
    IntegrableOn (fun w => (compactPlanePrior w : ℝ) * quadraticLoss threePointInput w ^ (-s))
      (Metric.ball (0 : ℝ × ℝ) 1) volume ↔ s < 1 / 2 := by
  exact quadratic_prior_weighted_integrableOn_iff threePointInput threePoint_positive_gram
    1 (by norm_num) (le_refl 1) compactPlanePrior compactPlanePrior_bounded s

theorem threePoint_twoBlock_prior_boundary :
    ¬ IntegrableOn (fun w => (compactPlanePrior w : ℝ) * quadraticLoss threePointInput w ^ (-(1 / 2 : ℝ)))
      (Metric.ball (0 : ℝ × ℝ) 1) volume := by
  rw [threePoint_twoBlock_prior_iff]
  exact lt_irrefl _

/-- The one-block witness δ₁ is insufficient for a positive three-feature Gram. -/
theorem dirac_one_gram_excluded :
    ¬ FinitePositiveFeatureGram (Measure.dirac (1 : ℝ)) quadraticFeatures := by
  intro h
  have hc : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro he
    have he0 := congrFun he 0
    norm_num at he0
  have hp := h.positive.dotProduct_mulVec_pos hc
  norm_num [featureGram, quadraticFeatures, dotProduct, mulVec, Fin.sum_univ_succ] at hp

#print axioms compactPlanePrior_bounded
#print axioms threePoint_twoBlock_prior_iff
#print axioms threePoint_twoBlock_prior_boundary
#print axioms dirac_one_gram_excluded
