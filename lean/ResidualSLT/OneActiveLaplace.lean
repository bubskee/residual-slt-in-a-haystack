module
public import ResidualSLT.OneActiveModelComparison
public import ResidualSLT.LaplacePairPrior

/-! Transfer to the actual one-active network in raw local product coordinates. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Filter Metric Set

theorem oneActivePopulationLoss_continuous (μ : Measure ℝ) (r L : ℕ) (hr : 2 ≤ r)
    (hL : 0 < L) (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r L)) (c : ℝ) :
    Continuous (oneActivePopulationLoss μ r c : (Fin L → ℝ) → ℝ) := by
  change Continuous (fun w : Fin L → ℝ => oneActivePopulationLoss μ r c w)
  simp_rw [oneActive_loss_eq_gram μ r L hr hL hμ]
  apply (gramValue_continuous _).comp
  exact (sparseNetworkCoefficients_continuous r L hr).sub continuous_const

theorem oneActiveAssemble_continuous (p q : ℕ) (τ : ℝ) :
    Continuous (oneActiveAssemble p q τ) := by
  apply continuous_pi_iff.mpr
  intro i
  unfold oneActiveAssemble
  split_ifs <;> fun_prop

theorem identityReferenceLoss_continuous (r n : ℕ) (hr : 2 ≤ r) :
    Continuous (identityReferenceLoss r n) := by
  by_cases hn : n = 0
  · subst n
    change Continuous (fun w : Fin 0 → ℝ => identityReferenceLoss r 0 w)
    simpa [identityReferenceLoss,networkPopulationLoss,networkSquaredError,network] using
      (continuous_const : Continuous (fun _ : Fin 0 → ℝ => (0:ℝ)))
  · exact networkPopulationLoss_continuous _ r hr n (by omega) (network_atomic_gram r n)

theorem oneActiveComparisonLoss_continuous (r p q : ℕ) (hr : 2 ≤ r) :
    Continuous (oneActiveComparisonLoss r p q) := by
  have hp := identityReferenceLoss_continuous r p hr
  have hq := identityReferenceLoss_continuous r q hr
  unfold oneActiveComparisonLoss
  fun_prop

/-- A local loss comparison with the certified product model suffices, on every smaller
full product ball and with every bounded positive prior. -/
theorem oneActive_laplace_of_local_comparison (r p q : ℕ) (hr : 2 ≤ r)
    (K : OneActiveAux p q → ℝ) (hK : Continuous K)
    (hcomp : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ w in nhds 0,
      c*oneActiveComparisonLoss r p q w ≤ K w ∧ K w ≤ C*oneActiveComparisonLoss r p q w) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : OneActiveAux p q → NNReal, BoundedPositivePriorOn ρ (ball 0 ε) volume →
      HasLaplaceOrder (oneActiveLearningPair r p q).1 (oneActiveLearningPair r p q).2
        (fun N => ∫ w in ball 0 ε, Real.exp (-N*K w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨c,C,hc,hC,hb⟩ := hcomp
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff_ball.mp hb
  refine ⟨min δ 1,lt_min hδ zero_lt_one,min_le_right _ _,?_⟩
  intro ε hε hεδ ρ hρ
  have hJ := oneActiveComparisonLoss_continuous r p q hr
  have hiK (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hiJ (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*oneActiveComparisonLoss r p q w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*oneActiveComparisonLoss r p q w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hbound : ∀ᵐ w ∂(volume : Measure (OneActiveAux p q)).restrict (ball 0 ε),
      c*oneActiveComparisonLoss r p q w ≤ K w ∧ K w ≤ C*oneActiveComparisonLoss r p q w := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact hb w (ball_subset_ball (hεδ.trans (min_le_left _ _)) hw)
  have horder := laplace_pair_order_of_comparable volume (ball 0 ε)
    (oneActiveComparisonLoss r p q) K hiJ hiK c C hc hC hbound
    (oneActiveComparisonLoss_laplace_order r p q hr ε hε (hεδ.trans (min_le_right _ _)))
  exact laplace_pair_order_withDensity volume measurableSet_ball K hiK ρ hρ horder

/-- Every r≥3 one-active realization has its arrangement-dependent Laplace pair.
The active raw weight is τ≠0; p and q are arbitrary, possibly zero. -/
theorem oneActive_network_laplace_order_of_three_le (μ : Measure ℝ) (r p q : ℕ) (hr : 3 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q))) (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : OneActiveAux p q → NNReal, BoundedPositivePriorOn ρ (ball 0 ε) volume →
      HasLaplaceOrder (oneActiveLearningPair r p q).1 (oneActiveLearningPair r p q).2
        (fun N => ∫ w in ball 0 ε,
          Real.exp (-N*oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w))
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  apply oneActive_laplace_of_local_comparison r p q (by omega)
    (fun w => oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w))
    ((oneActivePopulationLoss_continuous μ r (p+1+q) (by omega) (by omega) hμ (τ^r)).comp
      (oneActiveAssemble_continuous p q τ))
  obtain ⟨a,A,ha,hA,hactual⟩ := oneActive_loss_retained_comparison μ r p q hr hμ τ hτ
  obtain ⟨b,B,hb,hB,hmodel⟩ := oneActive_model_retained_comparison r p q (by omega)
  refine ⟨a/B,A/b,div_pos ha hB,div_pos hA hb,?_⟩
  filter_upwards [hactual,hmodel] with w hw hv
  constructor
  · calc
      _ ≤ (a/B)*(B*‖oneActiveRetained r p q w‖^2) :=
        mul_le_mul_of_nonneg_left hv.2 (div_pos ha hB).le
      _ = a*‖oneActiveRetained r p q w‖^2 := by field_simp
      _ ≤ _ := hw.1
  · calc
      _ ≤ A*‖oneActiveRetained r p q w‖^2 := hw.2
      _ = (A/b)*(b*‖oneActiveRetained r p q w‖^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (div_pos hA hb).le

end ResidualSLT
