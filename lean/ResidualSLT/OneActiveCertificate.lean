module
public import ResidualSLT.OneActiveEvenComparison

/-! Unified one-active-target local comparison and arrangement-dependent Laplace certificate.
All neighborhoods and priors use raw active displacement and raw inactive weights. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Filter Metric

/-- The actual one-active loss comparison, for every degree r≥2 and both arbitrary group sizes. -/
theorem oneActive_network_retained_comparison (μ : Measure ℝ) (r p q : ℕ) (hr : 2 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q)))
    (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ w : OneActiveAux p q in nhds 0,
      a*‖oneActiveRetained r p q w‖^2 ≤
        oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ∧
      oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ≤
        A*‖oneActiveRetained r p q w‖^2 := by
  by_cases h3 : 3 ≤ r
  · exact oneActive_loss_retained_comparison μ r p q h3 hμ τ hτ
  · have heven : Even r := by
      have he : r = 2 := by omega
      rw [he]
      decide
    obtain ⟨a,A,ha,hA,hb⟩ := oneActive_even_loss_retained_comparison μ r p q hr heven hμ τ hτ
    refine ⟨a,A,ha,hA,?_⟩
    filter_upwards [hb,oneActiveEvenRetained_norm_eq r p q hr heven] with w hw he
    simpa only [he] using hw

/-- Explicit local comparison with a regular squared displacement plus two actual identity losses.
No nonlinear inactive coordinates or unproved domain inclusions enter the measure transfer. -/
theorem oneActive_network_local_comparison (μ : Measure ℝ) (r p q : ℕ) (hr : 2 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q)))
    (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ w : OneActiveAux p q in nhds 0,
      c*oneActiveComparisonLoss r p q w ≤
        oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ∧
      oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w) ≤
        C*oneActiveComparisonLoss r p q w := by
  obtain ⟨a,A,ha,hA,hactual⟩ := oneActive_network_retained_comparison μ r p q hr hμ τ hτ
  obtain ⟨b,B,hb,hB,hmodel⟩ := oneActive_model_retained_comparison r p q hr
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

/-- End-to-end one-active arrangement pair, including quadratic degree, empty/singleton groups,
and one or two critical odd groups. Multiplicity is certified by two-sided Laplace bounds. -/
theorem oneActive_network_laplace_order (μ : Measure ℝ) (r p q : ℕ) (hr : 2 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q))) (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : OneActiveAux p q → NNReal, BoundedPositivePriorOn ρ (ball 0 ε) volume →
      HasLaplaceOrder (oneActiveLearningPair r p q).1 (oneActiveLearningPair r p q).2
        (fun N => ∫ w in ball 0 ε,
          Real.exp (-N*oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w))
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  exact oneActive_laplace_of_local_comparison r p q hr _
    ((oneActivePopulationLoss_continuous μ r (p+1+q) hr (by omega) hμ (τ^r)).comp
      (oneActiveAssemble_continuous p q τ))
    (oneActive_network_local_comparison μ r p q hr hμ τ hτ)

theorem oneActiveLearningPair_even (r p q : ℕ) (heven : Even r) :
    oneActiveLearningPair r p q = (1/2+((p:ℝ)+q)/(2*r),1) := by
  simp [oneActiveLearningPair,identityLearningPair_even r p heven,identityLearningPair_even r q heven]
  ring

end ResidualSLT
