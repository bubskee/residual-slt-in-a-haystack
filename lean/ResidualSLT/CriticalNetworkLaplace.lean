module
public import ResidualSLT.ConeLaplace
public import ResidualSLT.LaplaceTransfer

/-! Critical odd identity-target network: two-sided N^(-1/2) log N bounds.
This certifies (λ,m)=(1/2,2) in the Laplace-order sense, without claiming a
leading asymptotic constant or complex meromorphic continuation. -/
public section
noncomputable section
namespace ResidualSLT
open Set MeasureTheory Metric

/-- The actual identity-target population loss at odd depth=degree has critical
Laplace order on every raw parameter ball of radius 0<ε≤1. -/
theorem odd_critical_network_volume_laplace_order (μ : Measure ℝ)
    (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r r))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasCriticalLaplaceOrder (fun N => ∫ w : Fin r → ℝ in ball 0 ε,
      Real.exp (-N * networkPopulationLoss μ r w)) := by
  let K := homogeneousConeLoss (@weightPowerSum r r) (r+r)
  have hcK : Continuous K := by unfold K homogeneousConeLoss weightPowerSum; fun_prop
  have hcJ := networkPopulationLoss_continuous μ r (by omega) r (by omega) h
  have hiK (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*K w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w => Real.exp (-N*K w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  have hiJ (N : ℝ) : IntegrableOn (fun w => Real.exp (-N*networkPopulationLoss μ r w)) (ball 0 ε) volume :=
    ((by fun_prop : Continuous (fun w : Fin r → ℝ => Real.exp (-N*networkPopulationLoss μ r w))).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall
  obtain ⟨a,A,ha,hA,hnet⟩ := signed_network_loss_comparison μ r (by omega) r (by omega) h
  obtain ⟨b,B,hb,hB,hmodel⟩ := cancellationModel_radial_comparison r r (by omega) (by omega)
  apply laplace_order_of_comparable volume (ball 0 ε) K (networkPopulationLoss μ r)
    hiK hiJ (a*b) (A*B) (mul_pos ha hb) (mul_pos hA hB) _
    (criticalFermat_laplace_order r hr hodd ε hε hε1)
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

/-- A bounded positive measurable prior preserves the critical network logarithm.
All hypotheses are input moments/Gram positivity, parity, radius, and prior bounds;
no chart, comparison constant, or asymptotic conclusion is assumed. -/
theorem odd_critical_network_laplace_order (μ : Measure ℝ)
    (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r r))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin r → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    HasCriticalLaplaceOrder (fun N => ∫ w : Fin r → ℝ in ball 0 ε,
      Real.exp (-N * networkPopulationLoss μ r w)
      ∂volume.withDensity (fun w => (ρ w : ENNReal))) := by
  have hc := networkPopulationLoss_continuous μ r (by omega) r (by omega) h
  apply laplace_order_withDensity volume measurableSet_ball (networkPopulationLoss μ r) _ ρ hρ
    (odd_critical_network_volume_laplace_order μ r hr hodd h ε hε hε1)
  intro N
  exact ((by fun_prop : Continuous (fun w : Fin r → ℝ => Real.exp (-N*networkPopulationLoss μ r w))).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 ε)).mono_set ball_subset_closedBall

/-- Expanded numerical certificate for the critical pair (λ,m)=(1/2,2).
The sample-size variable is real; in particular the bounds hold for all sufficiently
large natural sample sizes. -/
theorem odd_critical_network_laplace_bounds (μ : Measure ℝ)
    (r : ℕ) (hr : 3 ≤ r) (hodd : Odd r)
    (h : FinitePositiveFeatureGram μ (networkFeatures r r))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ρ : (Fin r → ℝ) → NNReal) (hρ : BoundedPositivePriorOn ρ (ball 0 ε) volume) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      c * (N ^ (-(1/2:ℝ)) * Real.log N) ≤
        (∫ w : Fin r → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ∧
      (∫ w : Fin r → ℝ in ball 0 ε, Real.exp (-N*networkPopulationLoss μ r w)
          ∂volume.withDensity (fun w => (ρ w : ENNReal))) ≤
        C * (N ^ (-(1/2:ℝ)) * Real.log N) :=
  (odd_critical_network_laplace_order μ r hr hodd h ε hε hε1 ρ hρ).bounds

end ResidualSLT
