module
public import ResidualSLT.OneActiveCoordinates

/-! The one-active arrangement certificate on the original chronological raw-weight space. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Filter Metric Set

/-- Exact local RLCT and Laplace multiplicity on the original raw network parameter space.
The center has its unique nonzero weight τ at position p, with q subsequent blocks.
The parameter ball uses the usual maximum norm on Fin (p+1+q) → ℝ. -/
theorem oneActive_raw_network_rlct_laplace_certificate (μ : Measure ℝ) (r p q : ℕ) (hr : 2 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q))) (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : (Fin (p+1+q) → ℝ) → NNReal,
        BoundedPositivePriorOn ρ (ball (oneActiveAssemble p q τ 0) ε) volume →
      (∀ s : ℝ, IntegrableOn (fun w : Fin (p+1+q) → ℝ => (oneActivePopulationLoss μ r (τ^r) w)^(-s))
        (ball (oneActiveAssemble p q τ 0) ε) (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
          s < (oneActiveLearningPair r p q).1) ∧
      HasLaplaceOrder (oneActiveLearningPair r p q).1 (oneActiveLearningPair r p q).2
        (fun N => ∫ w : Fin (p+1+q) → ℝ in ball (oneActiveAssemble p q τ 0) ε,
          Real.exp (-N*oneActivePopulationLoss μ r (τ^r) w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨ε₀,hε₀,hε₀1,hcert⟩ := oneActive_network_rlct_laplace_certificate μ r p q hr hμ τ hτ
  refine ⟨ε₀,hε₀,hε₀1,?_⟩
  intro ε hε hεsmall ρ hρ
  have hρone : BoundedPositivePriorOn (fun _ : OneActiveAux p q => (1:NNReal)) (ball 0 ε) volume :=
    ⟨measurable_const,1,1,by norm_num,Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)⟩
  obtain ⟨hthreshold,horder⟩ := hcert ε hε hεsmall _ hρone
  have hvol : (volume : Measure (OneActiveAux p q)).withDensity (fun _ => (1:ENNReal)) = volume := withDensity_one
  simp only [ENNReal.coe_one,hvol] at hthreshold horder
  let e := oneActiveCoordinateEquiv p q τ
  have hmp : MeasurePreserving e
      ((volume : Measure (OneActiveAux p q)).restrict (ball 0 ε))
      ((volume : Measure (Fin (p+1+q) → ℝ)).restrict (ball (oneActiveAssemble p q τ 0) ε)) := by
    have hh := (oneActiveCoordinateEquiv_measurePreserving p q τ).restrict_preimage
      (measurableSet_ball (x := oneActiveAssemble p q τ 0) (ε := ε))
    simpa only [oneActiveCoordinateEquiv_preimage_ball] using hh
  have hK := oneActivePopulationLoss_continuous μ r (p+1+q) hr (by omega) hμ (τ^r)
  constructor
  · intro s
    rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
    have he := hmp.integrable_comp ((hK.measurable.pow_const (-s)).aestronglyMeasurable)
    have he' : IntegrableOn
        (fun w : OneActiveAux p q => (oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w))^(-s))
          (ball 0 ε) volume ↔
        IntegrableOn (fun w : Fin (p+1+q) → ℝ => (oneActivePopulationLoss μ r (τ^r) w)^(-s))
          (ball (oneActiveAssemble p q τ 0) ε) volume := by
      simpa only [IntegrableOn,Function.comp_def,e,oneActiveCoordinateEquiv_apply] using he
    exact he'.symm.trans (hthreshold s)
  · have he (N : ℝ) :
        (∫ w : OneActiveAux p q in ball 0 ε,
          Real.exp (-N*oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w))) =
        ∫ w : Fin (p+1+q) → ℝ in ball (oneActiveAssemble p q τ 0) ε,
          Real.exp (-N*oneActivePopulationLoss μ r (τ^r) w) := by
      simpa only [e,oneActiveCoordinateEquiv_apply] using
        hmp.integral_comp e.measurableEmbedding (fun w => Real.exp (-N*oneActivePopulationLoss μ r (τ^r) w))
    simp_rw [he] at horder
    apply laplace_pair_order_withDensity volume measurableSet_ball _ _ ρ hρ horder
    intro N
    exact ((by fun_prop : Continuous (fun w : Fin (p+1+q) → ℝ => Real.exp (-N*oneActivePopulationLoss μ r (τ^r) w))).continuousOn.integrableOn_compact
      (isCompact_closedBall (oneActiveAssemble p q τ 0) ε)).mono_set ball_subset_closedBall

/-- The endpoint is divergent for the same original raw-weight loss and local priors. -/
theorem oneActive_raw_network_boundary_divergence (μ : Measure ℝ) (r p q : ℕ) (hr : 2 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q))) (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : (Fin (p+1+q) → ℝ) → NNReal,
        BoundedPositivePriorOn ρ (ball (oneActiveAssemble p q τ 0) ε) volume →
      ¬ IntegrableOn (fun w : Fin (p+1+q) → ℝ =>
          (oneActivePopulationLoss μ r (τ^r) w)^(-(oneActiveLearningPair r p q).1))
        (ball (oneActiveAssemble p q τ 0) ε) (volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨ε₀,hε₀,hε₀1,hcert⟩ := oneActive_raw_network_rlct_laplace_certificate μ r p q hr hμ τ hτ
  refine ⟨ε₀,hε₀,hε₀1,?_⟩
  intro ε hε hεsmall ρ hρ
  rw [(hcert ε hε hεsmall ρ hρ).1]
  exact lt_irrefl _

end ResidualSLT
