module
public import ResidualSLT.NetworkLoss
public import ResidualSLT.CoefficientBounds
public import ResidualSLT.PriorMeasure
public import Mathlib.MeasureTheory.Constructions.Pi

/-! Arbitrary positive-depth even-degree actual network thresholds.
The coefficient and Gram comparison constants are derived. Input feature moments,
positive definiteness, local domains and parameter priors are explicit. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Polynomial Finset Metric
open scoped NNReal ENNReal

@[expose] def evenNetworkModel (r : ℕ) {L : ℕ} (w : Fin L → ℝ) : ℝ :=
  weightPowerSum r w ^ 2

theorem weightPowerSum_nonneg (r L : ℕ) (heven : Even r) (w : Fin L → ℝ) :
    0 ≤ weightPowerSum r w :=
  Finset.sum_nonneg (fun i _ => heven.pow_nonneg (w i))

theorem evenNetworkModel_pos (r L : ℕ) (heven : Even r) (w : Fin L → ℝ) (hw : w ≠ 0) :
    0 < evenNetworkModel r w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hn
    exact hw (funext hn)
  have hs : 0 < weightPowerSum r w :=
    Finset.sum_pos' (fun j _ => heven.pow_nonneg (w j))
      ⟨i, Finset.mem_univ _, heven.pow_pos hi⟩
  exact pow_pos hs 2

theorem evenNetworkModel_continuous (r L : ℕ) : Continuous (@evenNetworkModel r L) := by
  unfold evenNetworkModel weightPowerSum
  fun_prop

theorem weightPowerSum_smul (r L : ℕ) (a : ℝ) (w : Fin L → ℝ) :
    weightPowerSum r (a • w) = a ^ r * weightPowerSum r w := by
  simp [weightPowerSum, mul_pow, Finset.mul_sum]

theorem evenNetworkModel_smul (r L : ℕ) (a : ℝ) (w : Fin L → ℝ) :
    evenNetworkModel r (a • w) = a ^ (2 * r) * evenNetworkModel r w := by
  simp only [evenNetworkModel, weightPowerSum_smul, mul_pow, ← pow_mul, Nat.mul_comm r 2]

/-- Exact homogeneous comparison-model criterion at every positive radius. -/
theorem evenNetworkModel_integrableOn_iff (r : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => evenNetworkModel r w ^ (-s)) (ball 0 ε) volume ↔
      s < (L : ℝ) / (2 * r) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  simpa using positive_homogeneous_integrableOn_iff (volume : Measure (Fin L → ℝ))
    (2 * r) (by omega) (evenNetworkModel_continuous r L) (evenNetworkModel_pos r L heven)
    (fun a _ w => evenNetworkModel_smul r L a w) ε hε s

theorem evenNetworkModel_threshold (r : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    HasIntegrabilityThresholdOn (@evenNetworkModel r L) (ball 0 ε) volume
      ((L : ℝ) / (2 * r)) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  simpa using positive_homogeneous_threshold (volume : Measure (Fin L → ℝ))
    (2 * r) (by omega) (evenNetworkModel_continuous r L) (evenNetworkModel_pos r L heven)
    (fun a _ w => evenNetworkModel_smul r L a w) ε hε

/-- Even powers of raw weights in the unit cube lie in [0,1]. -/
theorem even_effective_weights_bounds (r L : ℕ) (heven : Even r) (w : Fin L → ℝ)
    (hw : w ∈ ball 0 1) : ∀ i < L, 0 ≤ zeroExtend w i ^ r ∧ zeroExtend w i ^ r ≤ 1 := by
  intro i hi
  simp only [zeroExtend, dite_eq_left hi]
  constructor
  · exact heven.pow_nonneg _
  · have habs : |w ⟨i, hi⟩| ≤ 1 :=
      (norm_le_pi_norm w ⟨i, hi⟩).trans (mem_ball_zero_iff.mp hw).le
    calc
      w ⟨i, hi⟩ ^ r ≤ |w ⟨i, hi⟩ ^ r| := le_abs_self _
      _ = |w ⟨i, hi⟩| ^ r := abs_pow _ _
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) habs

/-- Every actual residual coefficient is controlled uniformly by Σwᵢ^r. -/
theorem even_residual_coeff_bound (r L : ℕ) (heven : Even r) (w : Fin L → ℝ)
    (hw : w ∈ ball 0 1) (k : ℕ) :
    0 ≤ (network r (fun i => zeroExtend w i ^ r) L - X).coeff k ∧
      (network r (fun i => zeroExtend w i ^ r) L - X).coeff k ≤
        networkEnvelope r L * weightPowerSum r w := by
  have h := residual_coeff_uniform_bound r L (fun i => zeroExtend w i ^ r)
    (even_effective_weights_bounds r L heven w hw) k
  simpa [← Fin.sum_univ_eq_sum_range, zeroExtend, weightPowerSum] using h

/-- Coefficient vector comparison, with an explicit upper constant depending only on r,L. -/
theorem even_network_coefficients_bounds (r : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (L : ℕ) (hL : 0 < L) (w : Fin L → ℝ) (hw : w ∈ ball 0 1) :
    weightPowerSum r w ≤ ‖networkCoefficients r w‖ ∧
      ‖networkCoefficients r w‖ ≤ networkEnvelope r L * weightPowerSum r w := by
  have hs := weightPowerSum_nonneg r L heven w
  have hb : 0 ≤ networkEnvelope r L := le_trans zero_le_one (networkEnvelope_one_le r L)
  constructor
  · have hn := norm_le_pi_norm (networkCoefficients r w) ⟨0, networkFeatureCount_pos r L hL⟩
    simpa only [networkCoefficients_first r hr L hL w, Real.norm_eq_abs, abs_of_nonneg hs] using hn
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb hs)).mpr
    intro j
    obtain ⟨hpos, hle⟩ := even_residual_coeff_bound r L heven w hw (r + j.val)
    simpa only [networkCoefficients, Real.norm_eq_abs, abs_of_nonneg hpos] using hle

/-- Derived comparison of the actual arbitrary-depth even-degree loss to (Σwᵢ^r)². -/
theorem even_network_loss_comparison (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ ball (0 : Fin L → ℝ) 1,
      c * evenNetworkModel r w ≤ networkPopulationLoss μ r w ∧
      networkPopulationLoss μ r w ≤ C * evenNetworkModel r w := by
  let : Nonempty (Fin (networkFeatureCount r L)) := ⟨⟨0, networkFeatureCount_pos r L hL⟩⟩
  obtain ⟨c, C, hc, hC, hg⟩ := gramValue_bounds _ h.positive
  have hb : 0 < networkEnvelope r L := lt_of_lt_of_le zero_lt_one (networkEnvelope_one_le r L)
  refine ⟨c, C * networkEnvelope r L ^ 2, hc, by positivity, ?_⟩
  intro w hw
  obtain ⟨hl, hu⟩ := even_network_coefficients_bounds r hr heven L hL w hw
  have hs := weightPowerSum_nonneg r L heven w
  rw [network_loss_eq_gram μ r hr L hL h]
  constructor
  · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hl 2) hc.le).trans (hg _).1
  · calc
      _ ≤ C * ‖networkCoefficients r w‖ ^ 2 := (hg _).2
      _ ≤ C * (networkEnvelope r L * weightPowerSum r w) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 2) hC.le
      _ = _ := by unfold evenNetworkModel; ring
/-- The standard finite-product norm ball is exactly the open raw-weight cube. -/
theorem parameter_ball_eq_cube (L : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ball (0 : Fin L → ℝ) ε = Set.pi Set.univ (fun _ => Set.Ioo (-ε) ε) := by
  ext w
  simp [pi_norm_lt_iff hε, Real.norm_eq_abs, abs_lt]

/-- Exact criterion for the actual population loss, for every real exponent. -/
theorem even_network_integrableOn_iff (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    IntegrableOn (fun w : Fin L → ℝ => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε) volume ↔
      s < (L : ℝ) / (2 * r) := by
  obtain ⟨c, C, hc, hC, hb⟩ := even_network_loss_comparison μ r hr heven L hL h
  have hl : ∀ᵐ w ∂volume.restrict (ball (0 : Fin L → ℝ) ε),
      c * evenNetworkModel r w ≤ networkPopulationLoss μ r w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).1
  have hu : ∀ᵐ w ∂volume.restrict (ball (0 : Fin L → ℝ) ε),
      networkPopulationLoss μ r w ≤ C * evenNetworkModel r w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).2
  rw [integrableOn_rpow_iff_of_comparable_all
    (evenNetworkModel_continuous r L).measurable.aemeasurable
    (networkPopulationLoss_continuous μ r hr L hL h).measurable.aemeasurable
    (evenNetworkModel_threshold r hr heven L hL ε hε).1 hc hC hl hu s]
  exact evenNetworkModel_integrableOn_iff r hr heven L hL ε hε s

/-- The arbitrary-depth even-degree actual-loss threshold is L/(2r). -/
theorem even_network_threshold (μ : Measure ℝ) (r : ℕ) (hr : 2 ≤ r) (heven : Even r)
    (L : ℕ) (hL : 0 < L) (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasIntegrabilityThresholdOn (@networkPopulationLoss μ r L) (ball 0 ε) volume
      ((L : ℝ) / (2 * r)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := even_network_loss_comparison μ r hr heven L hL h
  apply (evenNetworkModel_threshold r hr heven L hL ε hε).of_comparable
    (evenNetworkModel_continuous r L).measurable.aemeasurable
    (networkPopulationLoss_continuous μ r hr L hL h).measurable.aemeasurable hc hC
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).1
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact (hb w (ball_subset_ball hε1 hw)).2

/-- All-real-exponent criterion under a locally bounded positive parameter density. -/
theorem even_network_prior_integrableOn_iff (μ : Measure ℝ)
    (r : ℕ) (hr : 2 ≤ r) (heven : Even r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (Fin L → ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) ↔ s < (L : ℝ) / (2 * r) := by
  rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
  exact even_network_integrableOn_iff μ r hr heven L hL h ε hε hε1 s

/-- Conventional density-weighted Lebesgue formulation, with the prior outside the power. -/
theorem even_network_prior_weighted_integrableOn_iff (μ : Measure ℝ)
    (r : ℕ) (hr : 2 ≤ r) (heven : Even r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (Fin L → ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) (s : ℝ) :
    IntegrableOn (fun w => (ρ w : ℝ) * networkPopulationLoss μ r w ^ (-s))
      (ball 0 ε) volume ↔ s < (L : ℝ) / (2 * r) := by
  rw [← integrableOn_withDensity_iff_weighted measurableSet_ball hρ.measurable]
  exact even_network_prior_integrableOn_iff μ r hr heven L hL h ε hε hε1 ρ hρ s

/-- End-to-end certificate: actual input integrability, coefficient-Gram integral, prior threshold. -/
theorem even_network_certificate (μ : Measure ℝ)
    (r : ℕ) (hr : 2 ≤ r) (heven : Even r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (Fin L → ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    (∀ w : Fin L → ℝ, Integrable (networkSquaredError r w) μ) ∧
    (∀ w : Fin L → ℝ, networkPopulationLoss μ r w =
      gramValue (featureGram μ (networkFeatures r L)) (networkCoefficients r w)) ∧
    HasIntegrabilityThresholdOn (@networkPopulationLoss μ r L) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) ((L : ℝ) / (2 * r)) := by
  exact ⟨network_squaredError_integrable μ r hr L hL h, network_loss_eq_gram μ r hr L hL h,
    (even_network_threshold μ r hr heven L hL h ε hε hε1).withDensity measurableSet_ball hρ⟩

/-- The critical exponent and all larger exponents are non-integrable under the prior. -/
theorem even_network_prior_not_integrable (μ : Measure ℝ)
    (r : ℕ) (hr : 2 ≤ r) (heven : Even r) (L : ℕ) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ρ : (Fin L → ℝ) → ℝ≥0)
    (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) (s : ℝ) (hs : (L : ℝ) / (2 * r) ≤ s) :
    ¬ IntegrableOn (fun w => networkPopulationLoss μ r w ^ (-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ℝ≥0∞))) := by
  rw [even_network_prior_integrableOn_iff μ r hr heven L hL h ε hε hε1 ρ hρ s]
  exact not_lt.mpr hs
end ResidualSLT
