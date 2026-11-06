module
public import ResidualSLT.ArrangementLaplace
public import ResidualSLT.LaplaceThreshold

/-! Exact inverse-power threshold, endpoint divergence and Laplace multiplicity. -/
public section
noncomputable section
namespace ResidualSLT
open MeasureTheory Filter Metric Set

theorem arrangementLearningPair_pos (r k : ℕ) (n : Fin (k+1) → ℕ) (hk : 0 < k) :
    0 < (arrangementLearningPair r k n).1 := by
  have hn (g : Fin (k+1)) : 0 ≤ (identityLearningPair r (n g)).1 := by
    unfold identityLearningPair
    split_ifs <;> dsimp <;> positivity
  have hh := Finset.sum_nonneg (fun g (_ : g ∈ Finset.univ) => hn g)
  dsimp [arrangementLearningPair]
  exact add_pos_of_pos_of_nonneg (by positivity) hh

theorem arrangement_active_ne_zero_ae (k : ℕ) (n : Fin (k+1) → ℕ) (j : Fin k) :
    ∀ᵐ w : ArrangementAux k n ∂volume, w.1 j ≠ 0 := by
  have hh : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  have hi := (Measure.quasiMeasurePreserving_eval (fun _ : Fin k => (volume : Measure ℝ)) j).ae hh
  have hi' : ∀ᵐ w : Fin k → ℝ ∂volume, w j ≠ 0 := by simpa only [← volume_pi] using hi
  have hp := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Fin k → ℝ)))
    (ν := (volume : Measure (∀ g : Fin (k+1), Fin (n g) → ℝ)))).ae hi'
  simpa only [← Measure.volume_eq_prod] using hp

/-- Exact arrangement-dependent integrability threshold, endpoint divergence and Laplace
multiplicity for the actual one-active-target loss, for all r≥2 and arbitrary p,q≥0. -/
theorem arrangement_network_rlct_laplace_certificate (μ : Measure ℝ) (r k : ℕ) (hr : 2 ≤ r) (hk : 0 < k)
    (n : Fin (k+1) → ℕ)
    (hμ : FinitePositiveFeatureGram μ (sparseNetworkFeatures r (arrangementDepth k n k le_rfl)))
    (τ : Fin k → ℝ) (hτ : ∀ j,τ j ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ρ : ArrangementAux k n → NNReal, BoundedPositivePriorOn ρ (ball 0 ε) volume →
      (∀ s : ℝ, IntegrableOn
        (fun w => (arrangementPopulationLoss μ r k n τ w)^(-s))
        (ball 0 ε) (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
          s < (arrangementLearningPair r k n).1) ∧
      HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
        (fun N => ∫ w in ball 0 ε,
          Real.exp (-N*arrangementPopulationLoss μ r k n τ w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  obtain ⟨η,hη,hη1,horder⟩ := arrangement_network_laplace_order μ r k hr n (hk.trans_le (arrangementDepth_ge k n k le_rfl)) hμ τ hτ
  obtain ⟨a,A,ha,_,hcomp⟩ := arrangement_loss_retained_comparison μ r k hr n (hk.trans_le (arrangementDepth_ge k n k le_rfl)) hμ τ hτ
  obtain ⟨δ,hδ,hcomp⟩ := Metric.eventually_nhds_iff_ball.mp hcomp
  refine ⟨min η δ,lt_min hη hδ,(min_le_left _ _).trans hη1,?_⟩
  intro ε hε hε₀ ρ hρ
  have hεη : ε ≤ η := hε₀.trans (min_le_left _ _)
  have hεδ : ε ≤ δ := hε₀.trans (min_le_right _ _)
  refine ⟨?_,horder ε hε hεη ρ hρ⟩
  let K : ArrangementAux k n → ℝ := fun w =>
    arrangementPopulationLoss μ r k n τ w
  have hK : Continuous K :=
    arrangementPopulationLoss_continuous μ r k hr n (hk.trans_le (arrangementDepth_ge k n k le_rfl)) hμ τ
  have hpos : ∀ᵐ w ∂(volume : Measure (ArrangementAux k n)).restrict (ball 0 ε), 0 < K w := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (arrangement_active_ne_zero_ae k n ⟨0,hk⟩)] with w hw hn
    have hbound := (hcomp w (ball_subset_ball hεδ hw)).1
    have hz : 0 < ‖arrangementSignedRetained r k n w‖ := by
      have hh := (norm_le_pi_norm w.1 (⟨0,hk⟩ : Fin k)).trans (norm_fst_le (arrangementSignedRetained r k n w))
      exact (norm_pos_iff.mpr hn).trans_le hh
    exact (mul_pos ha (sq_pos_of_pos hz)).trans_le hbound
  have hi (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hρone : BoundedPositivePriorOn (fun _ : ArrangementAux k n => (1:NNReal)) (ball 0 ε) volume :=
    ⟨measurable_const,1,1,by norm_num,Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)⟩
  have hvol : (volume : Measure (ArrangementAux k n)).withDensity (fun _ => (1:ENNReal)) = volume := withDensity_one
  have hZ : HasLaplaceOrder (arrangementLearningPair r k n).1 (arrangementLearningPair r k n).2
      (fun N => ∫ w in ball 0 ε, Real.exp (-N*K w)) := by
    simpa only [ENNReal.coe_one,hvol] using horder ε hε hεη _ hρone
  let : IsFiniteMeasure ((volume : Measure (ArrangementAux k n)).restrict (ball 0 ε)) :=
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
    exact iff_of_true hint (hnonpos.trans_lt (arrangementLearningPair_pos r k n hk))


end ResidualSLT
