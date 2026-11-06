module
public import ResidualSLT.OneActiveLossComparison

/-! Sparse-Gram control for a fixed target realized by any raw network of the same depth. -/
public section
noncomputable section
namespace ResidualSLT
open Polynomial Finset MeasureTheory

@[expose] def networkTargetLoss (μ : Measure ℝ) (r : ℕ) {L : ℕ} (t w : Fin L → ℝ) : ℝ :=
  ∫ x, ((network r (fun i => zeroExtend w i^r) L).eval x-
    (network r (fun i => zeroExtend t i^r) L).eval x)^2 ∂μ

@[expose] def networkTargetCoefficients (r : ℕ) {L : ℕ} (t w : Fin L → ℝ) :
    Fin (sparseNetworkFeatureCount r L) → ℝ := sparseNetworkCoefficients r w-sparseNetworkCoefficients r t

theorem networkTarget_feature_expansion (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (t w : Fin L → ℝ) (x : ℝ) :
    (network r (fun i => zeroExtend w i^r) L).eval x-(network r (fun i => zeroExtend t i^r) L).eval x =
      ∑ j, networkTargetCoefficients r t w j*sparseNetworkFeatures r L j x := by
  simp only [networkTargetCoefficients,Pi.sub_apply,sub_mul,sum_sub_distrib]
  rw [← sparse_network_feature_expansion r L hr hL,← sparse_network_feature_expansion r L hr hL]
  ring

theorem networkTargetLoss_eq_gram (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t w : Fin L → ℝ) :
    networkTargetLoss μ r t w =
      gramValue (featureGram μ (sparseNetworkFeatures r L)) (networkTargetCoefficients r t w) := by
  simp only [networkTargetLoss,networkTarget_feature_expansion r L hr hL]
  exact feature_integral_eq_gram μ _ hμ.integrable _

theorem networkTargetLoss_continuous (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (t : Fin L → ℝ) :
    Continuous (networkTargetLoss μ r t) := by
  change Continuous (fun w => networkTargetLoss μ r t w)
  simp_rw [networkTargetLoss_eq_gram μ r L hr hL hμ]
  exact (gramValue_continuous _).comp ((sparseNetworkCoefficients_continuous r L hr).sub continuous_const)

theorem networkTargetLoss_coefficient_bounds (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ t w : Fin L → ℝ,
      a*‖networkTargetCoefficients r t w‖^2 ≤ networkTargetLoss μ r t w ∧
      networkTargetLoss μ r t w ≤ A*‖networkTargetCoefficients r t w‖^2 := by
  let : Nonempty (Fin (sparseNetworkFeatureCount r L)) := ⟨⟨0,sparseNetworkFeatureCount_pos r L hr hL⟩⟩
  obtain ⟨a,A,ha,hA,hb⟩ := gramValue_bounds _ hμ.positive
  exact ⟨a,A,ha,hA,fun t w => by rw [networkTargetLoss_eq_gram μ r L hr hL hμ]; exact hb _⟩

/-- Uniform in both raw target and raw candidate: only sparse features enter. -/
theorem networkTargetLoss_comparable (μ ν : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L))
    (hν : FinitePositiveFeatureGram ν (sparseNetworkFeatures r L)) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ t w : Fin L → ℝ,
      a*networkTargetLoss ν r t w ≤ networkTargetLoss μ r t w ∧
      networkTargetLoss μ r t w ≤ A*networkTargetLoss ν r t w := by
  obtain ⟨a,A,ha,hA,hμb⟩ := networkTargetLoss_coefficient_bounds μ r L hr hL hμ
  obtain ⟨b,B,hb,hB,hνb⟩ := networkTargetLoss_coefficient_bounds ν r L hr hL hν
  refine ⟨a/B,A/b,div_pos ha hB,div_pos hA hb,?_⟩
  intro t w
  constructor
  · calc
      _ ≤ (a/B)*(B*‖networkTargetCoefficients r t w‖^2) :=
        mul_le_mul_of_nonneg_left (hνb t w).2 (div_pos ha hB).le
      _ = a*‖networkTargetCoefficients r t w‖^2 := by field_simp
      _ ≤ _ := (hμb t w).1
  · calc
      _ ≤ A*‖networkTargetCoefficients r t w‖^2 := (hμb t w).2
      _ = (A/b)*(b*‖networkTargetCoefficients r t w‖^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hνb t w).1 (div_pos hA hb).le

end ResidualSLT
