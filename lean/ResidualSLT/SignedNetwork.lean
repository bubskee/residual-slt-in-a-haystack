module
public import ResidualSLT.SignedCoefficientBounds
public import ResidualSLT.EvenNetwork

/-! Actual-network comparison with S²+Q², valid with signed effective weights.
The result includes odd-degree cancellation; it does not assign a numerical odd RLCT. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory Metric
open scoped NNReal ENNReal

@[expose] def weightSquareSum (r : ℕ) {L : ℕ} (w : Fin L → ℝ) : ℝ :=
  ∑ i, (w i ^ r) ^ 2
@[expose] def cancellationModel (r : ℕ) {L : ℕ} (w : Fin L → ℝ) : ℝ :=
  weightPowerSum r w ^ 2 + weightSquareSum r w ^ 2

/-- Q is the raw 2r-power sum, without changing the raw-weight parameter measure. -/
theorem weightSquareSum_eq (r L : ℕ) (w : Fin L → ℝ) :
    weightSquareSum r w = ∑ i, w i ^ (2 * r) := by
  simp only [weightSquareSum, ← pow_mul, Nat.mul_comm r 2]

theorem weightSquareSum_nonneg (r L : ℕ) (w : Fin L → ℝ) :
    0 ≤ weightSquareSum r w := Finset.sum_nonneg (fun _i _ => sq_nonneg _)

theorem signed_effective_weights_bounds (r L : ℕ) (w : Fin L → ℝ)
    (hw : w ∈ ball 0 1) : ∀ i < L, |zeroExtend w i ^ r| ≤ 1 := by
  intro i hi
  simp only [zeroExtend, dite_eq_left hi, abs_pow]
  exact pow_le_one₀ (abs_nonneg _)
    ((norm_le_pi_norm w ⟨i, hi⟩).trans (mem_ball_zero_iff.mp hw).le)

/-- Uniform O(Q) control of every higher actual-network coefficient, with no parity assumption. -/
theorem signed_raw_higher_coeff_bound (r L : ℕ) (w : Fin L → ℝ)
    (hw : w ∈ ball 0 1) (k : ℕ) (hk : k ≠ r) :
    |(network r (fun i => zeroExtend w i ^ r) L - X).coeff k| ≤
      (signedRemainderEnvelope r L * L) * weightSquareSum r w := by
  simpa [← Fin.sum_univ_eq_sum_range, zeroExtend, weightSquareSum] using
    signed_higher_coeff_bound r L (fun i => zeroExtend w i ^ r)
      (signed_effective_weights_bounds r L w hw) k hk

/-- Any residual coefficient is controlled by the finite coefficient-vector norm,
including degrees outside the chosen basis (where it vanishes). -/
theorem residual_coeff_le_norm (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (w : Fin L → ℝ) (k : ℕ) :
    |(network r (fun i => zeroExtend w i ^ r) L - X).coeff k| ≤ ‖networkCoefficients r w‖ := by
  let p := network r (fun i => zeroExtend w i ^ r) L - X
  change |p.coeff k| ≤ _
  by_cases hk : k < r
  · have hz := X_pow_dvd_iff.mp (network_residual_X_pow_dvd r (by omega)
      (fun i => zeroExtend w i ^ r) L) k hk
    change p.coeff k = 0 at hz
    rw [hz, abs_zero]
    exact norm_nonneg _
  by_cases hd : k ≤ r ^ L
  · let j : Fin (networkFeatureCount r L) := ⟨k - r, by unfold networkFeatureCount; omega⟩
    have hj : r + j.val = k := by dsimp [j]; omega
    simpa only [networkCoefficients, hj, Real.norm_eq_abs] using
      norm_le_pi_norm (networkCoefficients r w) j
  · have hb := natDegree_sub_le (network r (fun i => zeroExtend w i ^ r) L) X
    have hn := network_natDegree_le r hr (fun i => zeroExtend w i ^ r) L
    have hp := Nat.le_pow (a := r) hL
    simp only [natDegree_X] at hb
    have hdeg : p.natDegree < k := by dsimp [p]; omega
    rw [coeff_eq_zero_of_natDegree_lt hdeg, abs_zero]
    exact norm_nonneg _

/-- Exact second coefficient relation, for the residual and finite raw-weight vector. -/
theorem residual_second_SQ (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (w : Fin L → ℝ) :
    2 * (network r (fun i => zeroExtend w i ^ r) L - X).coeff (2 * r - 1) =
      (r : ℝ) * (weightPowerSum r w ^ 2 - weightSquareSum r w) := by
  have h := network_coeff_two_mul_sub_one r hr (fun i => zeroExtend w i ^ r) L
  simpa [coeff_sub, coeff_X, show 1 ≠ 2 * r - 1 by omega,
    ← Fin.sum_univ_eq_sum_range, zeroExtend, weightPowerSum, weightSquareSum] using h

/-- The raw unit cube bounds |S| by the depth. -/
theorem weightPowerSum_abs_le_depth (r L : ℕ) (w : Fin L → ℝ) (hw : w ∈ ball 0 1) :
    |weightPowerSum r w| ≤ L := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i : Fin L, |w i ^ r|) ≤ ∑ _i : Fin L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [zeroExtend] using signed_effective_weights_bounds r L w hw i.val i.isLt
    _ = _ := by simp

/-- A signed coefficient-vector upper bound; higher terms are controlled by Q, not |S|. -/
theorem signed_network_coefficients_upper (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (w : Fin L → ℝ) (hw : w ∈ ball 0 1) :
    ‖networkCoefficients r w‖ ≤ |weightPowerSum r w| +
      (signedRemainderEnvelope r L * L) * weightSquareSum r w := by
  have hD : 0 ≤ signedRemainderEnvelope r L * L :=
    mul_nonneg (signedRemainderEnvelope_nonneg r L) (Nat.cast_nonneg _)
  have hQ := weightSquareSum_nonneg r L w
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  by_cases hj : r + j.val = r
  · have hj0 : j = ⟨0, networkFeatureCount_pos r L hL⟩ := Fin.ext (by change j.val = 0; omega)
    rw [hj0, networkCoefficients_first r hr L hL w, Real.norm_eq_abs]
    linarith [mul_nonneg hD hQ]
  · have hb := signed_raw_higher_coeff_bound r L w hw (r + j.val) hj
    change |(network r (fun i => zeroExtend w i ^ r) L - X).coeff (r + j.val)| ≤ _
    exact hb.trans (le_add_of_nonneg_left (abs_nonneg _))

/-- The two exact leading coefficients control Q even on S=0. -/
theorem signed_network_coefficients_lower (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (w : Fin L → ℝ) (hw : w ∈ ball 0 1) :
    |weightPowerSum r w| ≤ ‖networkCoefficients r w‖ ∧
      weightSquareSum r w ≤ (L + 1 : ℝ) * ‖networkCoefficients r w‖ := by
  have hS : |weightPowerSum r w| ≤ ‖networkCoefficients r w‖ := by
    simpa only [networkCoefficients_first r hr L hL w, Real.norm_eq_abs] using
      norm_le_pi_norm (networkCoefficients r w) ⟨0, networkFeatureCount_pos r L hL⟩
  refine ⟨hS, ?_⟩
  have hsecond := residual_second_SQ r hr L w
  have hb := residual_coeff_le_norm r hr L hL w (2 * r - 1)
  have hb' := neg_abs_le ((network r (fun i => zeroExtend w i ^ r) L - X).coeff (2 * r - 1))
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hnorm := norm_nonneg (networkCoefficients r w)
  have hQ : weightSquareSum r w ≤ weightPowerSum r w ^ 2 + ‖networkCoefficients r w‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr') hnorm]
  have hSL := weightPowerSum_abs_le_depth r L w hw
  have hmul := mul_le_mul hSL hS (abs_nonneg _) (Nat.cast_nonneg L)
  rw [← sq, sq_abs] at hmul
  nlinarith

/-- Explicit two-sided squared coefficient bounds for the cancellation model. -/
theorem signed_network_coefficients_bounds (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (w : Fin L → ℝ) (hw : w ∈ ball 0 1) :
    cancellationModel r w ≤ (1 + (L + 1 : ℝ) ^ 2) * ‖networkCoefficients r w‖ ^ 2 ∧
      ‖networkCoefficients r w‖ ^ 2 ≤
        (2 * (1 + (signedRemainderEnvelope r L * L) ^ 2)) * cancellationModel r w := by
  obtain ⟨hS, hQ⟩ := signed_network_coefficients_lower r hr L hL w hw
  have hQ0 := weightSquareSum_nonneg r L w
  have hD : 0 ≤ signedRemainderEnvelope r L * L :=
    mul_nonneg (signedRemainderEnvelope_nonneg r L) (Nat.cast_nonneg _)
  constructor
  · have hs := pow_le_pow_left₀ (abs_nonneg _) hS 2
    rw [sq_abs] at hs
    have hq := pow_le_pow_left₀ hQ0 hQ 2
    simp only [mul_pow] at hq
    unfold cancellationModel
    nlinarith
  · have hu := pow_le_pow_left₀ (norm_nonneg _) (signed_network_coefficients_upper r hr L hL w hw) 2
    have hc := sq_nonneg (|weightPowerSum r w| -
      (signedRemainderEnvelope r L * L) * weightSquareSum r w)
    have hd := mul_nonneg (sq_nonneg (signedRemainderEnvelope r L * L)) (sq_nonneg (weightPowerSum r w))
    have hs := sq_abs (weightPowerSum r w)
    unfold cancellationModel
    nlinarith [sq_nonneg (weightSquareSum r w)]

/-- Derived actual-loss comparison K ≍ S²+Q², uniformly including the cancellation set S=0.
It holds for every r≥2, with no parity restriction and no assumed comparison constants. -/
theorem signed_network_loss_comparison (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ ball (0 : Fin L → ℝ) 1,
      c * cancellationModel r w ≤ networkPopulationLoss μ r w ∧
      networkPopulationLoss μ r w ≤ C * cancellationModel r w := by
  let : Nonempty (Fin (networkFeatureCount r L)) := ⟨⟨0, networkFeatureCount_pos r L hL⟩⟩
  obtain ⟨c, C, hc, hC, hg⟩ := gramValue_bounds _ h.positive
  let A : ℝ := 1 + (L + 1 : ℝ) ^ 2
  let B : ℝ := 2 * (1 + (signedRemainderEnvelope r L * L) ^ 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨c / A, C * B, div_pos hc hA, mul_pos hC hB, ?_⟩
  intro w hw
  obtain ⟨hl, hu⟩ := signed_network_coefficients_bounds r hr L hL w hw
  rw [network_loss_eq_gram μ r hr L hL h]
  constructor
  · calc
      _ ≤ (c / A) * (A * ‖networkCoefficients r w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hl (div_pos hc hA).le
      _ = c * ‖networkCoefficients r w‖ ^ 2 := by field_simp
      _ ≤ _ := (hg _).1
  · calc
      _ ≤ C * ‖networkCoefficients r w‖ ^ 2 := (hg _).2
      _ ≤ C * (B * cancellationModel r w) := mul_le_mul_of_nonneg_left hu hC.le
      _ = _ := by ring

/-- Actual input finiteness, exact Gram representation, and signed local comparison together. -/
theorem signed_network_certificate (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L)) :
    (∀ w : Fin L → ℝ, Integrable (networkSquaredError r w) μ) ∧
    (∀ w : Fin L → ℝ, networkPopulationLoss μ r w =
      gramValue (featureGram μ (networkFeatures r L)) (networkCoefficients r w)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ ball (0 : Fin L → ℝ) 1,
      c * cancellationModel r w ≤ networkPopulationLoss μ r w ∧
      networkPopulationLoss μ r w ≤ C * cancellationModel r w) :=
  ⟨network_squaredError_integrable μ r hr L hL h, network_loss_eq_gram μ r hr L hL h,
    signed_network_loss_comparison μ r hr L hL h⟩

/-- On exact cancellation directions, the actual loss is uniformly comparable to Q². -/
theorem signed_network_cancellation_comparison (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ ball (0 : Fin L → ℝ) 1,
      weightPowerSum r w = 0 →
      c * weightSquareSum r w ^ 2 ≤ networkPopulationLoss μ r w ∧
      networkPopulationLoss μ r w ≤ C * weightSquareSum r w ^ 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := signed_network_loss_comparison μ r hr L hL h
  refine ⟨c, C, hc, hC, ?_⟩
  intro w hw hs
  simpa only [cancellationModel, hs, zero_pow (by decide : 2 ≠ 0), zero_add] using hb w hw

theorem cancellationModel_continuous (r L : ℕ) : Continuous (@cancellationModel r L) := by
  unfold cancellationModel weightPowerSum weightSquareSum
  fun_prop

theorem cancellationModel_pos (r L : ℕ) (w : Fin L → ℝ) (hw : w ≠ 0) :
    0 < cancellationModel r w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hn
    exact hw (funext hn)
  have hq : 0 < weightSquareSum r w := Finset.sum_pos'
    (fun j _ => sq_nonneg (w j ^ r))
    ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero (pow_ne_zero r hi)⟩
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hq 2)

/-- Exact reduction of every real power-integrability question to S²+Q².
The model's numerical odd-degree threshold remains a separate integration problem. -/
theorem signed_network_integrableOn_iff_model (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε) volume ↔
      IntegrableOn (fun w : Fin L → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  obtain ⟨c, C, hc, hC, hb⟩ := signed_network_loss_comparison μ r hr L hL h
  apply integrableOn_rpow_iff_of_comparable_all
    (cancellationModel_continuous r L).measurable.aemeasurable
    (networkPopulationLoss_continuous μ r hr L hL h).measurable.aemeasurable _ hc hC _ _ s
  · filter_upwards [ae_restrict_of_ae ((volume : Measure (Fin L → ℝ)).ae_ne 0)] with w hw
    exact cancellationModel_pos r L w hw
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).1
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).2

/-- A bounded positive prior does not change the reduced integrability question. -/
theorem signed_network_prior_integrableOn_iff_model (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε1 : ε ≤ 1) (ρ : (Fin L → ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) ↔
      IntegrableOn (fun w : Fin L → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume := by
  rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
  exact signed_network_integrableOn_iff_model μ r hr L hL h ε hε1 s

/-- Conventional weighted-integrand version of the same reduction. -/
theorem signed_network_prior_weighted_integrableOn_iff_model (μ : Measure ℝ)
    (r : ℕ) (hr : 2 ≤ r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε1 : ε ≤ 1) (ρ : (Fin L → ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => (ρ w : ℝ) * networkPopulationLoss μ r w ^ (-s)) (ball 0 ε) volume ↔
      IntegrableOn (fun w : Fin L → ℝ => cancellationModel r w ^ (-s)) (ball 0 ε) volume := by
  rw [← integrableOn_withDensity_iff_weighted measurableSet_ball hρ.measurable]
  exact signed_network_prior_integrableOn_iff_model μ r hr L hL h ε hε1 ρ hρ s
end ResidualSLT
