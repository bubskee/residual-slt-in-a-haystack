module
public import ResidualSLT.PositiveHomogeneousLaplace
public import ResidualSLT.EvenNetwork

/-! Even-degree identity-target population loss: Laplace pair (L/(2r),1)
at every positive depth, under the existing feature-Gram and prior hypotheses. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- The even comparison model is positive homogeneous, with no cancellation set. -/
theorem evenNetworkModel_laplace_order (r L : ℕ) (hr : 0 < r) (heven : Even r)
    (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    HasPowerLaplaceOrder ((L:ℝ)/(2*r)) (fun N => ∫ w : Fin L → ℝ in ball 0 ε,
      Real.exp (-N*evenNetworkModel r w)) := by
  let : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  simpa using positive_homogeneous_laplace_order (volume : Measure (Fin L → ℝ)) r hr
    (evenNetworkModel_continuous r L) (evenNetworkModel_pos r L heven)
    (fun a _ w => evenNetworkModel_smul r L a w) ε hε

/-- Derived loss comparisons transfer the model's Laplace power to the actual
squared-error population loss for every even degree r≥2 and positive depth. -/
theorem even_network_volume_laplace_order (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (heven : Even r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder ((L:ℝ)/(2*r)) (fun N => ∫ w : Fin L → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ r w)) := by
  have hcK := evenNetworkModel_continuous r L
  have hcJ := networkPopulationLoss_continuous μ r hr L hL h
  obtain ⟨c,C,hc,hC,hb⟩ := even_network_loss_comparison μ r hr heven L hL h
  apply power_laplace_order_of_comparable volume (ball 0 ε) (evenNetworkModel r) (networkPopulationLoss μ r)
    (fun N => ((by fun_prop : Continuous (fun w : Fin L → ℝ => Real.exp (-N*evenNetworkModel r w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall)
    (fun N => ((by fun_prop : Continuous (fun w : Fin L → ℝ => Real.exp (-N*networkPopulationLoss μ r w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall)
    c C hc hC _ (evenNetworkModel_laplace_order r L (by omega) heven hL ε hε)
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact hb w (ball_subset_ball hε1 hw)

/-- A bounded positive measurable prior preserves the even network's pure power. -/
theorem even_network_laplace_order (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (heven : Even r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder ((L:ℝ)/(2*r)) (fun N => ∫ w : Fin L → ℝ in ball 0 ε,
      Real.exp (-N*networkPopulationLoss μ r w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hc := networkPopulationLoss_continuous μ r hr L hL h
  apply power_laplace_order_withDensity volume measurableSet_ball (networkPopulationLoss μ r) _ ρ hρ
    (even_network_volume_laplace_order μ r L hr heven hL h ε hε hε1)
  intro N
  exact ((by fun_prop : Continuous (fun w : Fin L → ℝ => Real.exp (-N*networkPopulationLoss μ r w))).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall

/-- Explicit two-sided bounds certify the pair (λ,m)=(L/(2r),1).
The bounds hold for all sufficiently large real sample sizes. -/
theorem even_network_laplace_bounds (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (heven : Even r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      c*N^(-((L:ℝ)/(2*r))) ≤
        (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ∧
      (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ≤ C*N^(-((L:ℝ)/(2*r))) :=
  (even_network_laplace_order μ r L hr heven hL h ε hε hε1 ρ hρ).bounds

/-- Direct Laplace bounds and the preserved exact power-integrability criterion,
including boundary divergence, for the same actual loss and parameter prior. -/
theorem even_network_laplace_certificate (μ : Measure ℝ)
    (r L : ℕ) (hr : 2 ≤ r) (heven : Even r) (hL : 0 < L)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder ((L:ℝ)/(2*r))
      (fun N => ∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
        ∂volume.withDensity (fun w => (ρ w : ENNReal))) ∧
    ∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔ s < (L:ℝ)/(2*r) :=
  ⟨even_network_laplace_order μ r L hr heven hL h ε hε hε1 ρ hρ,
    even_network_prior_integrableOn_iff μ r hr heven L hL h ε hε hε1 ρ hρ⟩

end ResidualSLT
