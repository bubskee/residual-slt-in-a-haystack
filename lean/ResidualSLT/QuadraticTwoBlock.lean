module
public import ResidualSLT.FeatureGram
public import ResidualSLT.PolynomialNetworks
public import ResidualSLT.PriorMeasure

/-! The actual quadratic two-block identity-target population loss.
Parameters use the standard product norm: its balls are open squares. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Set Metric Polynomial
open scoped NNReal ENNReal

@[expose] def quadraticFeatures (i : Fin 3) (x : ℝ) : ℝ := x ^ (i.val + 2)
@[expose] def quadraticCoefficients (w : ℝ × ℝ) : Fin 3 → ℝ :=
  ![w.1 ^ 2 + w.2 ^ 2, 2 * w.1 ^ 2 * w.2 ^ 2, w.1 ^ 4 * w.2 ^ 2]
@[expose] def quadraticSquaredError (w : ℝ × ℝ) (x : ℝ) : ℝ :=
  ((network 2 (fun i => if i = 0 then w.1 ^ 2 else w.2 ^ 2) 2).eval x - x) ^ 2
@[expose] def quadraticLoss (μ : Measure ℝ) (w : ℝ × ℝ) : ℝ :=
  ∫ x, quadraticSquaredError w x ∂μ
@[expose] def quadraticModel (w : ℝ × ℝ) : ℝ := (w.1 ^ 2 + w.2 ^ 2) ^ 2

/-- Exact polynomial identity, before evaluation or integration. -/
theorem quadratic_network_polynomial (a b : ℝ) :
    network 2 (fun i => if i = 0 then a ^ 2 else b ^ 2) 2 - X =
      C (a ^ 2 + b ^ 2) * X ^ 2 + C (2 * a ^ 2 * b ^ 2) * X ^ 3 +
        C (a ^ 4 * b ^ 2) * X ^ 4 := by
  simp [network, map_add, map_mul, map_pow, map_ofNat]
  ring

theorem quadratic_squaredError_eq (w : ℝ × ℝ) (x : ℝ) :
    quadraticSquaredError w x = (∑ i, quadraticCoefficients w i * quadraticFeatures i x) ^ 2 := by
  simp [quadraticSquaredError, network, quadraticCoefficients, quadraticFeatures,
    Fin.sum_univ_succ]
  ring

theorem quadratic_squaredError_integrable (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures) (w : ℝ × ℝ) :
    Integrable (quadraticSquaredError w) μ := by
  change Integrable (fun x => quadraticSquaredError w x) μ
  simp_rw [quadratic_squaredError_eq]
  exact feature_square_integrable μ quadraticFeatures h.integrable (quadraticCoefficients w)

theorem quadratic_loss_eq_gram (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures) (w : ℝ × ℝ) :
    quadraticLoss μ w = gramValue (featureGram μ quadraticFeatures) (quadraticCoefficients w) := by
  simp only [quadraticLoss, quadratic_squaredError_eq]
  exact feature_integral_eq_gram μ quadraticFeatures h.integrable (quadraticCoefficients w)

theorem quadraticLoss_continuous (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures) : Continuous (quadraticLoss μ) := by
  have heq := funext (quadratic_loss_eq_gram μ h)
  rw [heq]
  apply (gramValue_continuous _).comp
  unfold quadraticCoefficients
  fun_prop

/-- The coefficient vector has size comparable to a²+b² on the unit square. -/
theorem quadratic_coefficients_bounds (w : ℝ × ℝ) (hw : w ∈ ball 0 1) :
    w.1 ^ 2 + w.2 ^ 2 ≤ ‖quadraticCoefficients w‖ ∧
      ‖quadraticCoefficients w‖ ≤ 2 * (w.1 ^ 2 + w.2 ^ 2) := by
  have ha : |w.1| < 1 := lt_of_le_of_lt (norm_fst_le w) (mem_ball_zero_iff.mp hw)
  have hb : |w.2| < 1 := lt_of_le_of_lt (norm_snd_le w) (mem_ball_zero_iff.mp hw)
  have ha2 : w.1 ^ 2 ≤ 1 := by nlinarith [abs_lt.mp ha |>.1, abs_lt.mp ha |>.2]
  have hb2 : w.2 ^ 2 ≤ 1 := by nlinarith [abs_lt.mp hb |>.1, abs_lt.mp hb |>.2]
  have hab : w.1 ^ 2 * w.2 ^ 2 ≤ w.1 ^ 2 := by nlinarith [sq_nonneg w.1]
  have ha4 : w.1 ^ 4 ≤ w.1 ^ 2 := by nlinarith [sq_nonneg w.1]
  have ha4b : w.1 ^ 4 * w.2 ^ 2 ≤ w.1 ^ 2 :=
    (mul_le_mul_of_nonneg_left hb2 (by positivity)).trans (by simpa using ha4)
  constructor
  · simpa [quadraticCoefficients, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ w.1 ^ 2 + w.2 ^ 2)]
      using norm_le_pi_norm (quadraticCoefficients w) 0
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i <;> norm_num [quadraticCoefficients, Real.norm_eq_abs]
    · rw [abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg w.1, sq_nonneg w.2]
    · nlinarith [sq_nonneg w.2]
    · rw [← abs_pow, abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg w.1, sq_nonneg w.2]

/-- Derived local loss comparison: no comparison constants are assumed. -/
theorem quadratic_loss_comparison (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ ball (0 : ℝ × ℝ) 1,
      c * quadraticModel w ≤ quadraticLoss μ w ∧ quadraticLoss μ w ≤ C * quadraticModel w := by
  obtain ⟨c, C, hc, hC, hg⟩ := gramValue_bounds _ h.positive
  refine ⟨c, 4 * C, hc, by positivity, ?_⟩
  intro w hw
  obtain ⟨hl, hu⟩ := quadratic_coefficients_bounds w hw
  rw [quadratic_loss_eq_gram μ h]
  constructor
  · exact (mul_le_mul_of_nonneg_left (by dsimp [quadraticModel]; nlinarith [norm_nonneg (quadraticCoefficients w), sq_nonneg w.1, sq_nonneg w.2]) hc.le).trans (hg _).1
  · have hh := (hg (quadraticCoefficients w)).2
    have hn := norm_nonneg (quadraticCoefficients w)
    have hp : ‖quadraticCoefficients w‖ ^ 2 ≤ 4 * quadraticModel w := by
      dsimp [quadraticModel]
      nlinarith [sq_nonneg w.1, sq_nonneg w.2]
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hC.le])
/-- The standard product-norm ball is exactly the displayed raw-weight square. -/
theorem parameter_ball_eq_square (ε : ℝ) :
    ball (0 : ℝ × ℝ) ε = (Ioo (-ε) ε) ×ˢ (Ioo (-ε) ε) := by
  ext w
  simp [Prod.norm_def, Real.norm_eq_abs, abs_lt]

theorem quadraticModel_pos (w : ℝ × ℝ) (hw : w ≠ 0) : 0 < quadraticModel w := by
  have hs : 0 < w.1 ^ 2 + w.2 ^ 2 := by
    by_contra hn
    have ha : w.1 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2]
    have hb : w.2 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2]
    exact hw (Prod.ext ha hb)
  exact pow_pos hs 2

theorem quadraticModel_smul (a : ℝ) (w : ℝ × ℝ) :
    quadraticModel (a • w) = a ^ 4 * quadraticModel w := by
  simp only [quadraticModel, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Exact two-dimensional comparison-loss criterion for every real exponent. -/
theorem quadraticModel_integrableOn_iff (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun w => quadraticModel w ^ (-s)) (ball (0 : ℝ × ℝ) ε) volume ↔ s < 1 / 2 := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  convert positive_homogeneous_integrableOn_iff (μ := (volume : Measure (ℝ × ℝ)))
    (Q := quadraticModel) 4 (by omega) (by unfold quadraticModel; fun_prop)
    quadraticModel_pos (fun a _ w => quadraticModel_smul a w) ε hε s using 1; norm_num

/-- Exact two-dimensional comparison-loss threshold on every positive-radius square. -/
theorem quadraticModel_threshold (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn quadraticModel (ball (0 : ℝ × ℝ) ε) volume (1 / 2) := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  convert positive_homogeneous_threshold (μ := (volume : Measure (ℝ × ℝ)))
    (Q := quadraticModel) 4 (by omega) (by unfold quadraticModel; fun_prop)
    quadraticModel_pos (fun a _ w => quadraticModel_smul a w) ε hε using 1; norm_num

/-- Actual two-block population-loss threshold on every square of radius at most one. -/
theorem quadratic_threshold (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasIntegrabilityThresholdOn (quadraticLoss μ) (ball (0 : ℝ × ℝ) ε) volume (1 / 2) := by
  obtain ⟨c, C, hc, hC, hb⟩ := quadratic_loss_comparison μ h
  have hmodel : Continuous quadraticModel := by unfold quadraticModel; fun_prop
  apply (quadraticModel_threshold ε hε).of_comparable hmodel.measurable.aemeasurable
    (quadraticLoss_continuous μ h).measurable.aemeasurable hc hC
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).1
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).2

/-- Positive-prior threshold for the actual two-block network, with explicit local bounds. -/
theorem quadratic_prior_threshold (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (ℝ × ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball (0 : ℝ × ℝ) ε) volume) :
    HasIntegrabilityThresholdOn (quadraticLoss μ) (ball (0 : ℝ × ℝ) ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) (1 / 2) := by
  exact (quadratic_threshold μ h ε hε hε1).withDensity measurableSet_ball hρ

/-- End-to-end certificate: actual input integrability, exact Gram integral, and prior threshold. -/
theorem quadratic_twoBlock_certificate (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (ℝ × ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball (0 : ℝ × ℝ) ε) volume) :
    (∀ w, Integrable (quadraticSquaredError w) μ) ∧
    (∀ w, quadraticLoss μ w = gramValue (featureGram μ quadraticFeatures) (quadraticCoefficients w)) ∧
    HasIntegrabilityThresholdOn (quadraticLoss μ) (ball (0 : ℝ × ℝ) ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) (1 / 2) := by
  exact ⟨quadratic_squaredError_integrable μ h, quadratic_loss_eq_gram μ h,
    quadratic_prior_threshold μ h ε hε hε1 ρ hρ⟩

/-- Divergence at every exponent at or above one half, under the prior measure. -/
theorem quadratic_prior_not_integrable (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (ℝ × ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball (0 : ℝ × ℝ) ε) volume)
    (s : ℝ) (hs : 1 / 2 ≤ s) :
    ¬ IntegrableOn (fun w => quadraticLoss μ w ^ (-s)) (ball (0 : ℝ × ℝ) ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) := by
  rw [(quadratic_prior_threshold μ h ε hε hε1 ρ hρ).2 s (by linarith)]
  exact not_lt.mpr hs
/-- The actual-loss criterion includes every real exponent, not only s≥0. -/
theorem quadratic_integrableOn_iff (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w => quadraticLoss μ w ^ (-s)) (ball (0 : ℝ × ℝ) ε) volume ↔ s < 1 / 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := quadratic_loss_comparison μ h
  have hmodel : Continuous quadraticModel := by unfold quadraticModel; fun_prop
  have hl : ∀ᵐ w ∂volume.restrict (ball (0 : ℝ × ℝ) ε), c * quadraticModel w ≤ quadraticLoss μ w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).1
  have hu : ∀ᵐ w ∂volume.restrict (ball (0 : ℝ × ℝ) ε), quadraticLoss μ w ≤ C * quadraticModel w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).2
  rw [integrableOn_rpow_iff_of_comparable_all hmodel.measurable.aemeasurable
    (quadraticLoss_continuous μ h).measurable.aemeasurable (quadraticModel_threshold ε hε).1
    hc hC hl hu s]
  exact quadraticModel_integrableOn_iff ε hε s

/-- All-real-exponent integrability criterion under the actual parameter-prior measure. -/
theorem quadratic_prior_integrableOn_iff (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (ℝ × ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball (0 : ℝ × ℝ) ε) volume) (s : ℝ) :
    IntegrableOn (fun w => quadraticLoss μ w ^ (-s)) (ball (0 : ℝ × ℝ) ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) ↔ s < 1 / 2 := by
  rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
  exact quadratic_integrableOn_iff μ h ε hε hε1 s

/-- Conventional density-weighted Lebesgue formulation, for every real s. -/
theorem quadratic_prior_weighted_integrableOn_iff (μ : Measure ℝ)
    (h : FinitePositiveFeatureGram μ quadraticFeatures)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (ℝ × ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball (0 : ℝ × ℝ) ε) volume) (s : ℝ) :
    IntegrableOn (fun w => (ρ w : ℝ) * quadraticLoss μ w ^ (-s))
      (ball (0 : ℝ × ℝ) ε) volume ↔ s < 1 / 2 := by
  rw [← integrableOn_withDensity_iff_weighted measurableSet_ball hρ.measurable]
  exact quadratic_prior_integrableOn_iff μ h ε hε hε1 ρ hρ s
end ResidualSLT
