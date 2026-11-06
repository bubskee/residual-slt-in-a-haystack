module
public import ResidualSLT.OneDimensionalLaplace
public import ResidualSLT.HomogeneousFermat

/-! Noncritical odd identity-target network: two-sided pure-power Laplace bounds. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- Fermat specialization of the general noncritical theorem; the nonempty
cancellation cone exists at every depth L≥2. -/
theorem odd_offcritical_fermat_laplace_order (r L : ℕ) (hr : 0 < r) (hodd : Odd r)
    (hL : 2 ≤ L) (hne : L ≠ r) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r)))
      (fun N => ∫ w : Fin L → ℝ in ball 0 ε,
        Real.exp (-N*homogeneousConeLoss (weightPowerSum r) (r+r) w)) := by
  have hf : ContDiff ℝ 1 (@weightPowerSum r L) := by unfold weightPowerSum; fun_prop
  have hreg : ∀ w : Fin L → ℝ, w ≠ 0 → weightPowerSum r w = 0 →
      fderiv ℝ (weightPowerSum r) w ≠ 0 := by
    intro w hw _
    rw [(weightPowerSum_hasFDerivAt r L w).fderiv]
    exact fermatDifferential_ne_zero r L hr w hw
  obtain ⟨w,hw,hnorm⟩ := odd_fermat_sphere_nonempty r L hodd hL
  have hz : ∃ w : Fin L → ℝ, w ≠ 0 ∧ weightPowerSum r w = 0 := by
    refine ⟨w,?_,hw⟩
    intro he
    simp [he,weightPowerSum] at hnorm
  obtain ⟨n,rfl⟩ : ∃ n, L = n+2 := ⟨L-2,by omega⟩
  have h := homogeneous_offcritical_laplace_order n r r hr hr hne
    (weightPowerSum r) hf (weightPowerSum_smul r (n+2)) hreg hz ε hε hε1
  simpa only [coneLaplaceExponent,show 2*((r:ℝ)+r)=4*r by ring] using h

/-- All positive depths, with the empty cancellation cone at L=1 handled by
an independent one-dimensional radial estimate. -/
theorem odd_offcritical_fermat_all_depths_laplace_order (r L : ℕ) (hr : 0 < r) (hodd : Odd r)
    (hL : 0 < L) (hne : L ≠ r) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r)))
      (fun N => ∫ w : Fin L → ℝ in ball 0 ε,
        Real.exp (-N*homogeneousConeLoss (weightPowerSum r) (r+r) w)) := by
  by_cases hL2 : 2 ≤ L
  · exact odd_offcritical_fermat_laplace_order r L hr hodd hL2 hne ε hε hε1
  · have he : L = 1 := by omega
    subst L
    have hm := coneLaplaceExponent_of_le 1 r r hr (by omega)
    simp only [coneLaplaceExponent,show 2*((r:ℝ)+r)=4*r by ring,Nat.cast_one] at hm
    rw [Nat.cast_one,hm]
    exact one_fermat_laplace_order r hr ε hε hε1

/-- The actual identity-target population loss at odd degree and L≠r has pure-power
Laplace order on every raw parameter ball of radius 0<ε≤1. -/
theorem odd_offcritical_network_volume_laplace_order (μ : Measure ℝ)
    (r L : ℕ) (hr : 3 ≤ r) (hodd : Odd r) (hL : 0 < L) (hne : L ≠ r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasPowerLaplaceOrder (min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r))) (fun N => ∫ w : Fin L → ℝ in ball 0 ε,
      Real.exp (-N * networkPopulationLoss μ r w)) := by
  let K := homogeneousConeLoss (@weightPowerSum r L) (r+r)
  have hcK : Continuous K := by unfold K homogeneousConeLoss weightPowerSum; fun_prop
  have hcJ := networkPopulationLoss_continuous μ r (by omega) L (by omega) h
  have hiK (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hiJ (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*networkPopulationLoss μ r w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w : Fin L → ℝ => Real.exp (-N*networkPopulationLoss μ r w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  obtain ⟨a,A,ha,hA,hnet⟩ := signed_network_loss_comparison μ r (by omega) L (by omega) h
  obtain ⟨b,B,hb,hB,hmodel⟩ := cancellationModel_radial_comparison r L (by omega) (by omega)
  apply power_laplace_order_of_comparable volume (ball 0 ε) K (networkPopulationLoss μ r)
    hiK hiJ (a*b) (A*B) (mul_pos ha hb) (mul_pos hA hB) _
    (odd_offcritical_fermat_all_depths_laplace_order r L (by omega) hodd hL hne ε hε hε1)
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  have hn := hnet w ((ball_subset_ball hε1) hw)
  have hm := hmodel w
  have he : weightPowerSum r w ^ 2 + ‖w‖ ^ (4*r) = K w := by
    unfold K homogeneousConeLoss
    congr 2; omega
  rw [he] at hm
  constructor
  · calc
      (a*b)*K w = a*(b*K w) := mul_assoc _ _ _
      _ ≤ a*cancellationModel r w := mul_le_mul_of_nonneg_left hm.1 ha.le
      _ ≤ _ := hn.1
  · calc
      _ ≤ A*cancellationModel r w := hn.2
      _ ≤ A*(B*K w) := mul_le_mul_of_nonneg_left hm.2 hA.le
      _ = (A*B)*K w := (mul_assoc _ _ _).symm

/-- A bounded positive measurable prior preserves the noncritical network power.
All hypotheses are input moments/Gram positivity, parity, radius, and prior bounds;
no chart, comparison constant, or asymptotic conclusion is assumed. -/
theorem odd_offcritical_network_laplace_order (μ : Measure ℝ)
    (r L : ℕ) (hr : 3 ≤ r) (hodd : Odd r) (hL : 0 < L) (hne : L ≠ r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r))) (fun N => ∫ w : Fin L → ℝ in ball 0 ε,
      Real.exp (-N * networkPopulationLoss μ r w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hc := networkPopulationLoss_continuous μ r (by omega) L (by omega) h
  apply power_laplace_order_withDensity volume measurableSet_ball (networkPopulationLoss μ r) _ ρ hρ
    (odd_offcritical_network_volume_laplace_order μ r L hr hodd hL hne h ε hε hε1)
  intro N
  exact ((by fun_prop : Continuous (fun w : Fin L → ℝ => Real.exp (-N*networkPopulationLoss μ r w))).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall

/-- Expanded numerical certificate for the noncritical pair (λ,m)=(min(L/(2r),(L+r)/(4r)),1).
The sample-size variable is real; in particular the bounds hold for all sufficiently
large natural sample sizes. -/
theorem odd_offcritical_network_laplace_bounds (μ : Measure ℝ)
    (r L : ℕ) (hr : 3 ≤ r) (hodd : Odd r) (hL : 0 < L) (hne : L ≠ r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      c * (N ^ (-min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r)))) ≤
        (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ∧
      (∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ≤
        C * (N ^ (-min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r)))) :=
  (odd_offcritical_network_laplace_order μ r L hr hodd hL hne h ε hε hε1 ρ hρ).bounds

/-- The actual loss has both multiplicity-one Laplace order and the exact local
power-integrability threshold, including divergence at the boundary. -/
theorem odd_offcritical_network_certificate (μ : Measure ℝ)
    (r L : ℕ) (hr : 3 ≤ r) (hodd : Odd r) (hL : 0 < L) (hne : L ≠ r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r L))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin L → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasPowerLaplaceOrder (min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r)))
      (fun N => ∫ w : Fin L → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
        ∂volume.withDensity (fun w => (ρ w : ENNReal))) ∧
    ∀ s : ℝ, IntegrableOn (fun w => networkPopulationLoss μ r w^(-s)) (ball 0 ε)
      (volume.withDensity (fun w => (ρ w : ENNReal))) ↔
      s < min ((L:ℝ)/(2*r)) (((L:ℝ)+r)/(4*r)) :=
  ⟨odd_offcritical_network_laplace_order μ r L hr hodd hL hne h ε hε hε1 ρ hρ,
    odd_network_prior_all_depths_via_homogeneous μ r L hr hodd hL h ε hε hε1 ρ hρ⟩

end ResidualSLT
