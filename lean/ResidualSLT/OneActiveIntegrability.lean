module
public import ResidualSLT.OneActiveCertificate
public import ResidualSLT.LaplaceThreshold

/-! Exact one-active inverse-power threshold and Laplace multiplicity in one certificate. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Filter Metric Set

theorem oneActiveLearningPair_pos (r p q : ℕ) : 0 < (oneActiveLearningPair r p q).1 := by
  have hn (n : ℕ) : 0 ≤ (identityLearningPair r n).1 := by
    unfold identityLearningPair
    split_ifs <;> dsimp <;> positivity
  dsimp [oneActiveLearningPair]
  linarith [hn p,hn q]

/-- Raw active displacement is nonzero a.e. in the full product parameter space. -/
theorem oneActive_active_ne_zero_ae (p q : ℕ) :
    ∀ᵐ w : OneActiveAux p q ∂volume, w.1 ≠ 0 := by
  have hh : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  have hp := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ((Fin p → ℝ) × (Fin q → ℝ))))).ae hh
  simpa only [← Measure.volume_eq_prod] using hp

/-- Exact arrangement-dependent integrability threshold, endpoint divergence and Laplace
multiplicity for the actual one-active-target loss, for all r≥2 and arbitrary p,q≥0. -/
theorem oneActive_network_rlct_laplace_certificate (μ : Measure ℝ) (r p q : ℕ) (hr : 2 ≤ r)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (p+1+q))) (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : OneActiveAux p q → NNReal, BoundedPositivePriorOn ρ (ball 0 ε) volume →
      (∀ s : ℝ, IntegrableOn
        (fun w => (oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w))^(-s))
        (ball 0 ε) (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
          s < (oneActiveLearningPair r p q).1) ∧
      HasLaplaceOrder (oneActiveLearningPair r p q).1 (oneActiveLearningPair r p q).2
        (fun N => ∫ w in ball 0 ε,
          Real.exp (-N*oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w))
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨η,hη,hη1,horder⟩ := oneActive_network_laplace_order μ r p q hr hμ τ hτ
  obtain ⟨a,A,ha,_,hcomp⟩ := oneActive_network_retained_comparison μ r p q hr hμ τ hτ
  obtain ⟨δ,hδ,hcomp⟩ := Metric.eventually_nhds_iff_ball.mp hcomp
  refine ⟨min η δ,lt_min hη hδ,(min_le_left _ _).trans hη1,?_⟩
  intro ε hε hε₀ ρ hρ
  have hεη : ε ≤ η := hε₀.trans (min_le_left _ _)
  have hεδ : ε ≤ δ := hε₀.trans (min_le_right _ _)
  refine ⟨?_,horder ε hε hεη ρ hρ⟩
  let K : OneActiveAux p q → ℝ := fun w =>
    oneActivePopulationLoss μ r (τ^r) (oneActiveAssemble p q τ w)
  have hK : Continuous K :=
    (oneActivePopulationLoss_continuous μ r (p+1+q) hr (by omega) hμ (τ^r)).comp
      (oneActiveAssemble_continuous p q τ)
  have hpos : ∀ᵐ w ∂(volume : Measure (OneActiveAux p q)).restrict (ball 0 ε), 0 < K w := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (oneActive_active_ne_zero_ae p q)] with w hw hn
    have hbound := (hcomp w (ball_subset_ball hεδ hw)).1
    have hz : 0 < ‖oneActiveRetained r p q w‖ := by
      have hh := norm_le_pi_norm (oneActiveRetained r p q w) 0
      exact (norm_pos_iff.mpr hn).trans_le hh
    exact (mul_pos ha (sq_pos_of_pos hz)).trans_le hbound
  have hi (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hρone : BoundedPositivePriorOn (fun _ : OneActiveAux p q => (1:NNReal)) (ball 0 ε) volume :=
    ⟨measurable_const,1,1,by norm_num,Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)⟩
  have hvol : (volume : Measure (OneActiveAux p q)).withDensity (fun _ => (1:ENNReal)) = volume := withDensity_one
  have hZ : HasLaplaceOrder (oneActiveLearningPair r p q).1 (oneActiveLearningPair r p q).2
      (fun N => ∫ w in ball 0 ε, Real.exp (-N*K w)) := by
    simpa only [ENNReal.coe_one,hvol] using horder ε hε hεη _ hρone
  let : IsFiniteMeasure ((volume : Measure (OneActiveAux p q)).restrict (ball 0 ε)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  intro s
  rw [integrableOn_withDensity_iff_of_boundedPositive measurableSet_ball hρ]
  by_cases hs : 0 < s
  · exact inversePower_integrable_iff_of_laplace_order (volume.restrict (ball 0 ε)) K hK.measurable hpos hi
      _ _ hZ s hs
  · have hnonpos : s ≤ 0 := le_of_not_gt hs
    have hint : IntegrableOn (fun w => (K w)^(-s)) (ball 0 ε) volume :=
      (((Real.continuous_rpow_const (neg_nonneg.mpr hnonpos)).comp hK).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
    exact iff_of_true hint (hnonpos.trans_lt (oneActiveLearningPair_pos r p q))

end ResidualSLT
